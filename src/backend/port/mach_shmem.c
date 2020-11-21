/*-------------------------------------------------------------------------
 *
 * mach_shmem.c
 *	  Implement shared memory using mach facilities
 *
 * These routines used to be a fairly thin layer on top of mach shared
 * memory functionality.  With the addition of anonymous-shmem logic,
 * they're a bit fatter now.  We still require a mach shmem block to
 * exist, though, because mmap'd shmem provides no way to find out how
 * many processes are attached, which we need for interlocking purposes.
 *
 * Portions Copyright (c) 1996-2020, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/port/mach_shmem.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <unistd.h>
#include <sys/mman.h>
#include <sys/stat.h>
#ifdef HAVE_SYS_IPC_H
#include <sys/ipc.h>
#endif

#include "miscadmin.h"
#include "portability/mem.h"
#include "storage/dsm.h"
#include "storage/ipc.h"
#include "storage/pg_shmem.h"
#include "utils/pidfile.h"

#include <mach/port.h>
#include <mach/mach.h>
#include <mach/mach_vm.h>


/*
 * As of PostgreSQL 9.3, we normally allocate only a very small amount of
 * System V shared memory, and only for the purposes of providing an
 * interlock to protect the data directory.  The real shared memory block
 * is allocated using mmap().  This works around the problem that many
 * systems have very low limits on the amount of System V shared memory
 * that can be allocated.  Even a limit of a few megabytes will be enough
 * to run many copies of PostgreSQL without needing to adjust system settings.
 *
 * We assume that no one will attempt to run PostgreSQL 9.3 or later on
 * systems that are ancient enough that anonymous shared memory is not
 * supported, such as pre-2.4 versions of Linux.  If that turns out to be
 * false, we might need to add compile and/or run-time tests here and do this
 * only if the running kernel supports it.
 *
 * However, we must always disable this logic in the EXEC_BACKEND case, and
 * fall back to the old method of allocating the entire segment using System V
 * shared memory, because there's no way to attach an anonymous mmap'd segment
 * to a process after exec().  Since EXEC_BACKEND is intended only for
 * developer use, this shouldn't be a big problem.  Because of this, we do
 * not worry about supporting anonymous shmem in the EXEC_BACKEND cases below.
 *
 * As of PostgreSQL 12, we regained the ability to use a large System V shared
 * memory region even in non-EXEC_BACKEND builds, if shared_memory_type is set
 * to sysv (though this is not the default).
 */


typedef key_t IpcMemoryKey;		/* shared memory key passed to shmget(2) */
typedef int IpcMemoryId;		/* shared memory ID returned by shmget(2) */

/*
 * How does a given IpcMemoryId relate to this PostgreSQL process?
 *
 * One could recycle unattached segments of different data directories if we
 * distinguished that case from other SHMSTATE_FOREIGN cases.  Doing so would
 * cause us to visit less of the key space, making us less likely to detect a
 * SHMSTATE_ATTACHED key.  It would also complicate the concurrency analysis,
 * in that postmasters of different data directories could simultaneously
 * attempt to recycle a given key.  We'll waste keys longer in some cases, but
 * avoiding the problems of the alternative justifies that loss.
 */
typedef enum
{
	SHMSTATE_ANALYSIS_FAILURE,	/* unexpected failure to analyze the ID */
	SHMSTATE_ATTACHED,			/* pertinent to DataDir, has attached PIDs */
	SHMSTATE_ENOENT,			/* no segment of that ID */
	SHMSTATE_FOREIGN,			/* exists, but not pertinent to DataDir */
	SHMSTATE_UNATTACHED			/* pertinent to DataDir, no attached PIDs */
} IpcMemoryState;


unsigned long UsedShmemSegID = 0;
void	   *UsedShmemSegAddr = NULL;

static Size AnonymousShmemSize;
static void *AnonymousShmem = NULL;
memory_object_size_t mo_size = 0;

static void *InternalIpcMemoryCreate(IpcMemoryKey memKey, Size size);
static void IpcMemoryDetach(int status, Datum shmaddr);
static void IpcMemoryDelete(int status, Datum shmId);
static IpcMemoryState PGSharedMemoryAttach(IpcMemoryId shmId,
										   void *attachAt,
										   PGShmemHeader **addr);


/*
 *	InternalIpcMemoryCreate(memKey, size)
 *
 * Attempt to create a new shared memory segment with the specified key.
 * Will fail (return NULL) if such a segment already exists.  If successful,
 * attach the segment to the current process and return its attached address.
 * On success, callbacks are registered with on_shmem_exit to detach and
 * delete the segment when on_shmem_exit is called.
 *
 * If we fail with a failure code other than collision-with-existing-segment,
 * print out an error and abort.  Other types of errors are not recoverable.
 */
static void *
InternalIpcMemoryCreate(IpcMemoryKey memKey, Size size)
{
	mem_entry_name_port_t MachPort = MACH_PORT_NULL;
	kern_return_t kr;
	mach_vm_address_t requestedAddress;
	void	   *memAddress;
	mo_size = round_page(size);

	/*
	 * Normally we just pass requestedAddress = NULL to shmat(), allowing the
	 * system to choose where the segment gets mapped.  But in an EXEC_BACKEND
	 * build, it's possible for whatever is chosen in the postmaster to not
	 * work for backends, due to variations in address space layout.  As a
	 * rather klugy workaround, allow the user to specify the address to use
	 * via setting the environment variable PG_SHMEM_ADDR.  (If this were of
	 * interest for anything except debugging, we'd probably create a cleaner
	 * and better-documented way to set it, such as a GUC.)
	 */
#ifdef EXEC_BACKEND
	{
		char	   *pg_shmem_addr = getenv("PG_SHMEM_ADDR");

		if (pg_shmem_addr)
			requestedAddress = (void *) strtoul(pg_shmem_addr, NULL, 0);
	}
#endif

	/* OK, should be able to attach to the segment */
	kr = mach_make_memory_entry_64(mach_task_self(),
								   &mo_size,
								   memKey,
								   MAP_MEM_NAMED_CREATE | VM_PROT_DEFAULT,
								   &MachPort,
								   MACH_PORT_NULL);

	/* Register on-exit routine to delete the new segment */
	on_shmem_exit(IpcMemoryDelete, Int32GetDatum(MachPort));

	if (kr != KERN_SUCCESS)
		elog(FATAL,
			 "mach_make_memory_entry_64("
			 "target_task=%d, "
			 "size=%llu, "
			 "offset=%d, "
			 "permission=0x%x, "
			 "object_handle=%d, "
			 "parent_entry=%d) failed: "
			 "%d",
			 mach_task_self(),
			 mo_size,
			 memKey,
			 MAP_MEM_NAMED_CREATE | VM_PROT_DEFAULT,
			 MachPort,
			 MACH_PORT_NULL,
			 kr);

	kr = mach_vm_map(mach_task_self(),
					 &requestedAddress,
					 mo_size,
					 0,
					 VM_FLAGS_ANYWHERE,
					 MachPort,
					 0,
					 FALSE,
					 VM_PROT_DEFAULT,
					 VM_PROT_DEFAULT,
					 VM_INHERIT_NONE);

	if (kr != KERN_SUCCESS)
		elog(FATAL,
			 "mach_vm_map("
			 "target_task=%d, "
			 "address=%p, "
			 "size=%llu, "
			 "mask=%d, "
			 "flags=0x%x, "
			 "object=%d, "
			 "offset=%d, "
			 "copy=%d, "
			 "cur_protection=0x%x, "
			 "max_protection=0x%x, "
			 "inheritance=0x%x) failed: "
			 "%d",
			 mach_task_self(),
			 &requestedAddress,
			 mo_size,
			 0,
			 VM_FLAGS_ANYWHERE,
			 MachPort,
			 0,
			 FALSE,
			 VM_PROT_DEFAULT,
			 VM_PROT_DEFAULT,
			 VM_INHERIT_NONE,
			 kr);
	memAddress = (void *)requestedAddress;

	/* Register on-exit routine to detach new segment before deleting */
	on_shmem_exit(IpcMemoryDetach, AddressGetDatum(requestedAddress));

	/*
	 * Store shmem key and ID in data directory lockfile.  Format to try to
	 * keep it the same length always (trailing junk in the lockfile won't
	 * hurt, but might confuse humans).
	 */
	{
		char		line[64];

		sprintf(line, "%9lu %9lu",
				(unsigned long) memKey, (unsigned long) MachPort);
		AddToDataDirLockFile(LOCK_FILE_LINE_SHMEM_KEY, line);
	}

	return memAddress;
}

/****************************************************************************/
/*	IpcMemoryDetach(status, shmaddr)	removes a shared memory segment		*/
/*										from process' address space			*/
/*	(called as an on_shmem_exit callback, hence funny argument list)		*/
/****************************************************************************/
static void
IpcMemoryDetach(int status, Datum shmaddr)
{
	/* Detach System V shared memory block. */
	kern_return_t kr = mach_vm_deallocate(mach_task_self(), *DatumGetAddress(shmaddr), mo_size);
	if (kr != KERN_SUCCESS)
		elog(LOG, "mach_vm_deallocate(target=%d, address=%p, size=%llu) failed: %d",
			 mach_task_self(), DatumGetAddress(shmaddr), mo_size, kr);
}

/****************************************************************************/
/*	IpcMemoryDelete(status, shmId)		deletes a shared memory segment		*/
/*	(called as an on_shmem_exit callback, hence funny argument list)		*/
/****************************************************************************/
static void
IpcMemoryDelete(int status, Datum shmId)
{
	kern_return_t kr = mach_port_deallocate(mach_task_self(), DatumGetInt32(shmId));
	if (kr != KERN_SUCCESS)
		elog(FATAL, "mach_port_deallocate(task=%d, name=%d) failed: %d",
			 mach_task_self(), DatumGetInt32(shmId), kr);
}

/*
 * PGSharedMemoryIsInUse
 *
 * Is a previously-existing shmem segment still existing and in use?
 *
 * The point of this exercise is to detect the case where a prior postmaster
 * crashed, but it left child backends that are still running.  Therefore
 * we only care about shmem segments that are associated with the intended
 * DataDir.  This is an important consideration since accidental matches of
 * shmem segment IDs are reasonably common.
 */
bool
PGSharedMemoryIsInUse(unsigned long id1, unsigned long id2)
{
	kern_return_t kr;
	mach_msg_type_number_t pCount = VM_PAGE_INFO_BASIC_COUNT;
	vm_page_info_basic_data_t pInfo;

	kr = mach_vm_page_info(mach_task_self(), id2, VM_PAGE_INFO_BASIC, (vm_page_info_t)&pInfo, &pCount);
	if (kr != KERN_SUCCESS)
		elog(LOG, "mach_vm_map(target_task=%d, address=%lu, flavor=0x%x, info=%p, infoCnt=%d) failed: %d",
			 mach_task_self(), id2, VM_PAGE_INFO_BASIC, &pInfo, pCount, kr);

	if (pInfo.disposition & (VM_PAGE_QUERY_PAGE_PRESENT | VM_PAGE_QUERY_PAGE_REF | VM_PAGE_QUERY_PAGE_DIRTY))
		return true;
	return false;
}

/*
 * Test for a segment with id shmId; see comment at IpcMemoryState.
 *
 * If the segment exists, we'll attempt to attach to it, using attachAt
 * if that's not NULL (but it's best to pass NULL if possible).
 *
 * *addr is set to the segment memory address if we attached to it, else NULL.
 */
static IpcMemoryState
PGSharedMemoryAttach(IpcMemoryId shmId,
					 void *attachAt,
					 PGShmemHeader **addr)
{
	mem_entry_name_port_t MachPort;
	kern_return_t kr;
	struct stat statbuf;
	PGShmemHeader *hdr;

	*addr = NULL;

	/*
	 * First, try to stat the shm segment ID, to see if it exists at all.
	 */
	mach_msg_type_number_t pCount = VM_PAGE_INFO_BASIC_COUNT;
	vm_page_info_basic_data_t pInfo;
	kr = mach_vm_page_info(mach_task_self(), shmId, VM_PAGE_INFO_BASIC, (vm_page_info_t)&pInfo, &pCount);
	if (kr != KERN_SUCCESS)
		elog(LOG, "mach_vm_page_info(target_task=%d, address=%d, flavor=0x%x, info=%p, infoCnt=%d) failed: %d",
			 mach_task_self(), shmId, VM_PAGE_INFO_BASIC, &pInfo, pCount, kr);

	if (pInfo.disposition & (VM_PAGE_QUERY_PAGE_PRESENT | VM_PAGE_QUERY_PAGE_REF | VM_PAGE_QUERY_PAGE_DIRTY))
		return SHMSTATE_ATTACHED;

	if (kr != KERN_SUCCESS)
	{
		/*
		 * EINVAL actually has multiple possible causes documented in the
		 * shmctl man page, but we assume it must mean the segment no longer
		 * exists.
		 */
		if (kr == KERN_INVALID_ADDRESS)
			return SHMSTATE_ENOENT;

		/*
		 * EACCES implies we have no read permission, which means it is not a
		 * Postgres shmem segment (or at least, not one that is relevant to
		 * our data directory).
		 */
		if (kr == KERN_PROTECTION_FAILURE)
			return SHMSTATE_FOREIGN;

		/*
		 * Some Linux kernel versions (in fact, all of them as of July 2007)
		 * sometimes return EIDRM when EINVAL is correct.  The Linux kernel
		 * actually does not have any internal state that would justify
		 * returning EIDRM, so we can get away with assuming that EIDRM is
		 * equivalent to EINVAL on that platform.
		 */

		/*
		 * Otherwise, we had better assume that the segment is in use.  The
		 * only likely case is (non-Linux, assumed spec-compliant) EIDRM,
		 * which implies that the segment has been IPC_RMID'd but there are
		 * still processes attached to it.
		 */
		return SHMSTATE_ANALYSIS_FAILURE;
	}

	/*
	 * Try to attach to the segment and see if it matches our data directory.
	 * This avoids any risk of duplicate-shmem-key conflicts on machines that
	 * are running several postmasters under the same userid.
	 *
	 * (When we're called from PGSharedMemoryCreate, this stat call is
	 * duplicative; but since this isn't a high-traffic case it's not worth
	 * trying to optimize.)
	 */
	if (stat(DataDir, &statbuf) < 0)
		return SHMSTATE_ANALYSIS_FAILURE;	/* can't stat; be conservative */

	MachPort = DatumGetInt32(shmId);
	kr = mach_vm_map(mach_task_self(),
					 attachAt,
					 mo_size,
					 0,
					 VM_FLAGS_ANYWHERE,
					 MachPort,
					 0,
					 FALSE,
					 VM_PROT_DEFAULT,
					 VM_PROT_DEFAULT,
					 VM_INHERIT_NONE);

	if (kr != KERN_SUCCESS)
	{
		/*
		 * Attachment failed.  The cases we're interested in are the same as
		 * for the shmctl() call above.  In particular, note that the owning
		 * postmaster could have terminated and removed the segment between
		 * shmctl() and shmat().
		 *
		 * If attachAt isn't NULL, it's possible that EINVAL reflects a
		 * problem with that address not a vanished segment, so it's best to
		 * pass NULL when probing for conflicting segments.
		 */
		elog(LOG,
			 "mach_vm_map("
			 "target_task=%d, "
			 "address=%p, "
			 "size=%llu, "
			 "mask=%d, "
			 "flags=0x%x, "
			 "object=%d, "
			 "offset=%d, "
			 "copy=%d, "
			 "cur_protection=0x%x, "
			 "max_protection=0x%x, "
			 "inheritance=0x%x) failed: "
			 "%d",
			 mach_task_self(),
			 attachAt,
			 (mach_vm_size_t)sizeof(PGShmemHeader),
			 0,
			 VM_FLAGS_ANYWHERE,
			 MachPort,
			 0,
			 FALSE,
			 VM_PROT_DEFAULT,
			 VM_PROT_DEFAULT,
			 VM_INHERIT_NONE,
			 kr);

		if (kr == KERN_INVALID_ADDRESS)
			return SHMSTATE_ENOENT; /* segment disappeared */
		if (errno == KERN_PROTECTION_FAILURE)
			return SHMSTATE_FOREIGN;	/* must be non-Postgres */
		/* Otherwise, be conservative. */
		return SHMSTATE_ANALYSIS_FAILURE;
	}
	hdr = (void *)attachAt;
	*addr = hdr;

	if (hdr->magic != PGShmemMagic ||
		hdr->device != statbuf.st_dev ||
		hdr->inode != statbuf.st_ino)
	{
		/*
		 * It's either not a Postgres segment, or not one for my data
		 * directory.
		 */
		return SHMSTATE_FOREIGN;
	}

	/*
	 * It does match our data directory, so now test whether any processes are
	 * still attached to it.  (We are, now, but the shm_nattch result is from
	 * before we attached to it.)
	 */
	return pInfo.ref_count == 0 ? SHMSTATE_UNATTACHED : SHMSTATE_ATTACHED;
}

/*
 * Creates an anonymous mmap()ed shared memory segment.
 *
 * Pass the requested size in *size.  This function will modify *size to the
 * actual size of the allocation, if it ends up allocating a segment that is
 * larger than requested.
 */
static void *
CreateAnonymousSegment(Size *size)
{
	Size		allocsize = *size;
	void	   *ptr = MAP_FAILED;
	int			mmap_errno = 0;

	if (ptr == MAP_FAILED && huge_pages != HUGE_PAGES_ON)
	{
		/*
		 * Use the original size, not the rounded-up value, when falling back
		 * to non-huge pages.
		 */
		allocsize = *size;
		ptr = mmap(NULL, allocsize, PROT_READ | PROT_WRITE,
				   PG_MMAP_FLAGS, -1, 0);
		mmap_errno = errno;
	}

	if (ptr == MAP_FAILED)
	{
		errno = mmap_errno;
		ereport(FATAL,
				(errmsg("could not map anonymous shared memory: %m"),
				 (mmap_errno == ENOMEM) ?
				 errhint("This error usually means that PostgreSQL's request "
						 "for a shared memory segment exceeded available memory, "
						 "swap space, or huge pages. To reduce the request size "
						 "(currently %zu bytes), reduce PostgreSQL's shared "
						 "memory usage, perhaps by reducing shared_buffers or "
						 "max_connections.",
						 allocsize) : 0));
	}

	*size = allocsize;
	return ptr;
}

/*
 * AnonymousShmemDetach --- detach from an anonymous mmap'd block
 * (called as an on_shmem_exit callback, hence funny argument list)
 */
static void
AnonymousShmemDetach(int status, Datum arg)
{
	/* Release anonymous shared memory block, if any. */
	if (AnonymousShmem != NULL)
	{
		if (munmap(AnonymousShmem, AnonymousShmemSize) < 0)
			elog(LOG, "munmap(%p, %zu) failed: %m",
				 AnonymousShmem, AnonymousShmemSize);
		AnonymousShmem = NULL;
	}
}

/*
 * PGSharedMemoryCreate
 *
 * Create a shared memory segment of the given size and initialize its
 * standard header.  Also, register an on_shmem_exit callback to release
 * the storage.
 *
 * Dead Postgres segments pertinent to this DataDir are recycled if found, but
 * we do not fail upon collision with foreign shmem segments.  The idea here
 * is to detect and re-use keys that may have been assigned by a crashed
 * postmaster or backend.
 */
PGShmemHeader *
PGSharedMemoryCreate(Size size,
					 PGShmemHeader **shim)
{
	kern_return_t kr;
	IpcMemoryKey NextShmemSegID;
	mach_vm_address_t *memAddress;
	PGShmemHeader *hdr;
	struct stat statbuf;
	Size		sysvsize;

	/*
	 * We use the data directory's ID info (inode and device numbers) to
	 * positively identify shmem segments associated with this data dir, and
	 * also as seeds for searching for a free shmem key.
	 */
	if (stat(DataDir, &statbuf) < 0)
		ereport(FATAL,
				(errcode_for_file_access(),
				 errmsg("could not stat data directory \"%s\": %m",
						DataDir)));

	/* Room for a header? */
	Assert(size > MAXALIGN(sizeof(PGShmemHeader)));

	if (shared_memory_type == SHMEM_TYPE_MMAP)
	{
		AnonymousShmem = CreateAnonymousSegment(&size);
		AnonymousShmemSize = size;

		/* Register on-exit routine to unmap the anonymous segment */
		on_shmem_exit(AnonymousShmemDetach, (Datum) 0);

		/* Now we need only allocate a minimal-sized SysV shmem block. */
		sysvsize = sizeof(PGShmemHeader);
	}
	else
		sysvsize = size;

	/*
	 * Loop till we find a free IPC key.  Trust CreateDataDirLockFile() to
	 * ensure no more than one postmaster per data directory can enter this
	 * loop simultaneously.  (CreateDataDirLockFile() does not entirely ensure
	 * that, but prefer fixing it over coping here.)
	 */
	NextShmemSegID = statbuf.st_ino;

	for (;;)
	{
		PGShmemHeader *oldhdr;
		IpcMemoryState state;

		/* Try to create new segment */
		memAddress = InternalIpcMemoryCreate(NextShmemSegID, sysvsize);
		if (memAddress)
			break;				/* successful create and attach */

		/* Check shared memory and possibly remove and recreate */

		/*
		 * shmget() failure is typically EACCES, hence SHMSTATE_FOREIGN.
		 * ENOENT, a narrow possibility, implies SHMSTATE_ENOENT, but one can
		 * safely treat SHMSTATE_ENOENT like SHMSTATE_FOREIGN.
		 */
		mach_msg_type_number_t pCount = VM_PAGE_INFO_BASIC_COUNT;
		vm_page_info_basic_data_t pInfo;
		kr = mach_vm_page_info(mach_task_self(), *memAddress, VM_PAGE_INFO_BASIC, (vm_page_info_t)&pInfo, &pCount);
		if (kr != KERN_SUCCESS)
			elog(LOG, "mach_vm_page_info(target_task=%d, address=%d, flavor=0x%x, info=%p, infoCnt=%d) failed: %d",
				 mach_task_self(), NextShmemSegID, VM_PAGE_INFO_BASIC, &pInfo, pCount, kr);

		if (kr != KERN_SUCCESS)
		{
			oldhdr = NULL;
			state = SHMSTATE_FOREIGN;
		}
		else
			state = PGSharedMemoryAttach(pInfo.object_id, NULL, &oldhdr);

		switch (state)
		{
			case SHMSTATE_ANALYSIS_FAILURE:
			case SHMSTATE_ATTACHED:
				ereport(FATAL,
						(errcode(ERRCODE_LOCK_FILE_EXISTS),
						 errmsg("pre-existing shared memory block (key %lu, ID %lu) is still in use",
								(unsigned long) NextShmemSegID,
								(unsigned long) pInfo.object_id),
						 errhint("Terminate any old server processes associated with data directory \"%s\".",
								 DataDir)));
				break;
			case SHMSTATE_ENOENT:

				/*
				 * To our surprise, some other process deleted since our last
				 * InternalIpcMemoryCreate().  Moments earlier, we would have
				 * seen SHMSTATE_FOREIGN.  Try that same ID again.
				 */
				elog(LOG,
					 "shared memory block (key %lu, ID %lu) deleted during startup",
					 (unsigned long) NextShmemSegID,
					 (unsigned long) pInfo.object_id);
				break;
			case SHMSTATE_FOREIGN:
				NextShmemSegID++;
				break;
			case SHMSTATE_UNATTACHED:

				/*
				 * The segment pertains to DataDir, and every process that had
				 * used it has died or detached.  Zap it, if possible, and any
				 * associated dynamic shared memory segments, as well.  This
				 * shouldn't fail, but if it does, assume the segment belongs
				 * to someone else after all, and try the next candidate.
				 * Otherwise, try again to create the segment.  That may fail
				 * if some other process creates the same shmem key before we
				 * do, in which case we'll try the next key.
				 */
				if (oldhdr->dsm_control != 0)
					dsm_cleanup_using_control_segment(oldhdr->dsm_control);
				if (mach_port_deallocate(mach_task_self(), pInfo.object_id) != KERN_SUCCESS)
					NextShmemSegID++;
				break;
		}

		if (oldhdr) {
			kr = mach_vm_deallocate(mach_task_self(), (mach_vm_address_t)oldhdr, mo_size);
			if (kr != KERN_SUCCESS)
				elog(LOG, "mach_vm_deallocate(target=%d, address=%p, size=%llu) failed: %d",
					 mach_task_self(), oldhdr, mo_size, kr);
		}
	}

	/* Initialize new segment. */
	hdr = (PGShmemHeader *) memAddress;
	hdr->creatorPID = getpid();
	hdr->magic = PGShmemMagic;
	hdr->dsm_control = 0;

	/* Fill in the data directory ID info, too */
	hdr->device = statbuf.st_dev;
	hdr->inode = statbuf.st_ino;

	/*
	 * Initialize space allocation status for segment.
	 */
	hdr->totalsize = size;
	hdr->freeoffset = MAXALIGN(sizeof(PGShmemHeader));
	*shim = hdr;

	/* Save info for possible future use */
	UsedShmemSegAddr = memAddress;
	UsedShmemSegID = (unsigned long) NextShmemSegID;

	/*
	 * If AnonymousShmem is NULL here, then we're not using anonymous shared
	 * memory, and should return a pointer to the System V shared memory
	 * block. Otherwise, the System V shared memory block is only a shim, and
	 * we must return a pointer to the real block.
	 */
	if (AnonymousShmem == NULL)
		return hdr;
	memcpy(AnonymousShmem, hdr, sizeof(PGShmemHeader));
	return (PGShmemHeader *) AnonymousShmem;
}

#ifdef EXEC_BACKEND

/*
 * PGSharedMemoryReAttach
 *
 * This is called during startup of a postmaster child process to re-attach to
 * an already existing shared memory segment.  This is needed only in the
 * EXEC_BACKEND case; otherwise postmaster children inherit the shared memory
 * segment attachment via fork().
 *
 * UsedShmemSegID and UsedShmemSegAddr are implicit parameters to this
 * routine.  The caller must have already restored them to the postmaster's
 * values.
 */
void
PGSharedMemoryReAttach(void)
{
	IpcMemoryId shmid;
	PGShmemHeader *hdr;
	IpcMemoryState state;
	void	   *origUsedShmemSegAddr = UsedShmemSegAddr;

	Assert(UsedShmemSegAddr != NULL);
	Assert(IsUnderPostmaster);

	elog(DEBUG3, "attaching to %p", UsedShmemSegAddr);
	shmid = shmget(UsedShmemSegID, sizeof(PGShmemHeader), 0);
	if (shmid < 0)
		state = SHMSTATE_FOREIGN;
	else
		state = PGSharedMemoryAttach(shmid, UsedShmemSegAddr, &hdr);
	if (state != SHMSTATE_ATTACHED)
		elog(FATAL, "could not reattach to shared memory (key=%d, addr=%p): %m",
			 (int) UsedShmemSegID, UsedShmemSegAddr);
	if (hdr != origUsedShmemSegAddr)
		elog(FATAL, "reattaching to shared memory returned unexpected address (got %p, expected %p)",
			 hdr, origUsedShmemSegAddr);
	dsm_set_control_handle(hdr->dsm_control);

	UsedShmemSegAddr = hdr;		/* probably redundant */
}

/*
 * PGSharedMemoryNoReAttach
 *
 * This is called during startup of a postmaster child process when we choose
 * *not* to re-attach to the existing shared memory segment.  We must clean up
 * to leave things in the appropriate state.  This is not used in the non
 * EXEC_BACKEND case, either.
 *
 * The child process startup logic might or might not call PGSharedMemoryDetach
 * after this; make sure that it will be a no-op if called.
 *
 * UsedShmemSegID and UsedShmemSegAddr are implicit parameters to this
 * routine.  The caller must have already restored them to the postmaster's
 * values.
 */
void
PGSharedMemoryNoReAttach(void)
{
	Assert(UsedShmemSegAddr != NULL);
	Assert(IsUnderPostmaster);

	/* For cleanliness, reset UsedShmemSegAddr to show we're not attached. */
	UsedShmemSegAddr = NULL;
	/* And the same for UsedShmemSegID. */
	UsedShmemSegID = 0;
}

#endif							/* EXEC_BACKEND */

/*
 * PGSharedMemoryDetach
 *
 * Detach from the shared memory segment, if still attached.  This is not
 * intended to be called explicitly by the process that originally created the
 * segment (it will have on_shmem_exit callback(s) registered to do that).
 * Rather, this is for subprocesses that have inherited an attachment and want
 * to get rid of it.
 *
 * UsedShmemSegID and UsedShmemSegAddr are implicit parameters to this
 * routine, also AnonymousShmem and AnonymousShmemSize.
 */
void
PGSharedMemoryDetach(void)
{
	kern_return_t kr;
	if (UsedShmemSegAddr != NULL)
	{
		kr = mach_vm_deallocate(mach_task_self(), (mach_vm_address_t)UsedShmemSegAddr, mo_size);
		if (kr != KERN_SUCCESS)
			elog(LOG, "mach_vm_deallocate(target=%d, address=%p, size=%llu) failed: %d",
				 mach_task_self(), UsedShmemSegAddr, mo_size, kr);
		UsedShmemSegAddr = NULL;
	}

	if (AnonymousShmem != NULL)
	{
		if (munmap(AnonymousShmem, AnonymousShmemSize) < 0)
			elog(LOG, "munmap(%p, %zu) failed: %m",
				 AnonymousShmem, AnonymousShmemSize);
		AnonymousShmem = NULL;
	}
}
