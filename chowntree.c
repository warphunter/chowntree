/*
   chowntree - fast parallel file tree chown

   Copyright (C) 2020 - 2024 by Jorn I. Viken <jornv@1337.no>

   Portions of this code are derived from software created by
   - Dmitry Yu Okunev <dyokunev@ut.mephi.ru>, https://github.com/xaionaro/libpftw (pthreads framework)

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#define VERSION "1.16"
#define CHOWNTREE

#define _GNU_SOURCE

#include <errno.h>
#include <semaphore.h>
#if defined(__APPLE__)
#   include <dispatch/dispatch.h>
#endif
#include <signal.h>
#if defined(_AIX)
#    define _SIGSET_T	// needed at least on GCC 4.8.5 to avoid these msgs: "error: conflicting types for 'sigset_t'"
#endif
#include <pthread.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <regex.h>
#include <stdlib.h>
#include <search.h>
#include <dirent.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <assert.h>
#include <limits.h>
#include <time.h>
#include <sys/time.h>
#include <pwd.h>
#include <grp.h>

#if defined(__hpux)
#   include <sys/pstat.h>
#endif

#if defined (__sun__)
#    include <sys/statvfs.h>
#elif defined(__hpux)
#    include <sys/vfs.h>
#elif defined(__FreeBSD__) || defined(__OpenBSD__) || defined(__APPLE__)
#    include <sys/param.h>
#    include <sys/mount.h>
#endif

#undef FALSE
#undef TRUE
typedef enum {FALSE, TRUE} boolean;

#if defined (__linux__) || defined(__FreeBSD__) || defined(__OpenBSD__)
#    include <fcntl.h>
#    include <sys/syscall.h>
#    define DEFAULT_DIRENT_COUNT 100000		// - for option -X, may be overridden using env var DIRENTS
    static boolean extreme_readdir = FALSE; 	// - set to TRUE if option -X is given
    static unsigned buf_size;			// - set if option -X is given
    static unsigned getdents_calls;		// - incremented for every syscall(SYS_getdents, ... (if option -X is given)
#endif

// Borrowed from /usr/include/nspr4/pratom.h on RH6.4:
#if ((__GNUC__ > 4) || (__GNUC__ == 4 && __GNUC_MINOR__ >= 1)) && ! defined(__hppa__)
#    define PR_ATOMIC_ADD(ptr, val) __sync_add_and_fetch(ptr, val)
#else
     static pthread_mutex_t accum_filecnt_lock = PTHREAD_MUTEX_INITIALIZER; // for protecting "accum_filecnt"
#endif

#define INLINE_PROCESSING_THRESHOLD	2

#define MAX_THREADS        	512	// - max number of threads that may be created

#define DIRTY_CONSTANT		~0 	// - for handling non-POSIX compliant file systems
			   		// (link count should reflect the number of subdirectories, and should be 2 for empty directories)

#define S_IRWXA (S_IRWXU|S_IRWXG|S_IRWXO)

static char *progname;
static boolean xdev = FALSE;		// - set to TRUE if option -x is given

static boolean master_finished = FALSE;

static unsigned statcount = 0; // - counter for lstat calls
#if ! defined(PR_ATOMIC_ADD)
	static pthread_mutex_t statcount_lock = PTHREAD_MUTEX_INITIALIZER;
#endif

#if defined(__linux__) || defined(__FreeBSD__) || defined(__OpenBSD__) || defined(__APPLE__)
	unsigned statcount_unexp = 0;
#	if ! defined(PR_ATOMIC_ADD)
		static pthread_mutex_t statcount_unexp_lock = PTHREAD_MUTEX_INITIALIZER;
#	endif
#endif

static unsigned queued_dirs = 0;	// - the total number of dirs handled by a separate thread
#if ! defined(PR_ATOMIC_ADD)
	static pthread_mutex_t queued_dirs_lock = PTHREAD_MUTEX_INITIALIZER;
#endif

static boolean simulate_posix_compliance = FALSE; // - POSIX requires the directory link count to be at least 2

static unsigned char inline_processing_threshold = INLINE_PROCESSING_THRESHOLD;

static boolean lifo_queue = TRUE;       // - default queue of directories to be processed is of type LIFO
static boolean fifo_queue = FALSE;      // - select a standard FIFO queue with option -q
static boolean ino_queue = FALSE;       // - select a sorted queue of dirents with option -Q
static unsigned long inolist_bypasscount;// - total number of list elements bypassed; only used by inodirlist_bintreeinsert() 

static boolean debug = FALSE;		// - set if env var DEBUG is set

enum filetype {
	FILETYPE_REGFILE=1,
	FILETYPE_DIR=2,
	FILETYPE_SYMLINK=4,
	FILETYPE_BLOCKDEV=8,
	FILETYPE_CHARDEV=16,
	FILETYPE_PIPE=32,
	FILETYPE_SOCKET=64
};
static unsigned filetypemask = 0;	  // - set if option -f, -d is specified

static unsigned accum_filecnt = 0;	  // - count the number of files seen
static unsigned verbose_count = 0;	  // - set if option -v is specified
static unsigned last_accum_filecnt = 0;   // - used by -v
static pthread_mutex_t last_accum_filecnt_lock = PTHREAD_MUTEX_INITIALIZER; // for protecting "accum_filecnt"
static time_t last_t = 0;                 // - previous timestamp in seconds since EPOCH, used in pthread_routine()

static boolean just_count = FALSE;        // - set if -w, -z, -D, -R is specified

static char **excludelist;		  // - set if -e/-E is specified
static unsigned excludelist_count = 0;	  // - set if -e/-E is specified
static regex_t **excluderecomp;		  // - set if -e/-E is specified

boolean dryrun = FALSE; 		  // - set to TRUE if -n is specified; don't delete anything; just print files/dirs to be deleted

static unsigned entries_chowned = 0;	  // - total number of files/dirs chown()'ed.
#if ! defined(PR_ATOMIC_ADD)
	static pthread_mutex_t entries_chowned_lock = PTHREAD_MUTEX_INITIALIZER;
#endif

static unsigned file_no_access = 0;       // - counter for unsuccessful chown() calls, type EEXIST
static unsigned file_not_found = 0;       // - counter for unsuccessful chown() calls, type ENOENT
static unsigned file_any_other_error = 0; // - counter for unsuccessful chown() calls, type "any other reason"
static uid_t new_uid = 0;
static gid_t new_gid = 0;

static pthread_mutex_t perror_lock = PTHREAD_MUTEX_INITIALIZER; // The perror() function should be allowed to finish printing.

typedef struct dirlist dirlist_t;

struct dirlist {
	char		*dirpath;
	unsigned	 depth;		    // - Current directory depth.
	unsigned	 inlined;  	    // - How many subdirs are processed inline so far.
	unsigned	 filecnt;    	    // - Number of files in this dir.
	dirlist_t	*next;	    	    // - A pointer to next directory in queue.
	dirlist_t       *prev;              // - pointer to previous directory in queue
 	unsigned	 st_nlink;	    // - Link count for current directory = number of subdirs incl "." and "..".
	unsigned long	 st_dev;	    // - File system id for current directory.
	uid_t		 st_uid;	    // - User ID of the directory's owner
	gid_t		 st_gid;	    // - Group ID of the directory's group
        ino_t            st_ino;            // - Directory inode number
};

// This is the global list of directories to be processed, malloc'ed later:
dirlist_t	*dirlist_head;	    // - first directory in queue
dirlist_t	*dirlist_tail;	    // - last directory in queue - only for FIFO queue (option -q)
unsigned	 queuesize = 0;	    // - current number of queued directories waiting to be processed by a thread
unsigned	 maxdepth = 0;	    // - max directory depth, if option -m is specified
pthread_mutex_t	 dirlist_lock = PTHREAD_MUTEX_INITIALIZER; // - for protecting dirlist_head, dirlist_tail, queuesize

static pthread_t	*thread_arr	 	= NULL;
static unsigned		 thread_cnt	 	= 0; // - set by main(), used by traverse_trees(), thread_prepare(), thread_cleanup()
static unsigned		 sleeping_thread_cnt	= 0;
#if ! defined(PR_ATOMIC_ADD)
	static pthread_mutex_t   sleeping_thread_cnt_lock = PTHREAD_MUTEX_INITIALIZER; // - for protecting "sleeping_thread_cnt"
#endif

#if ! defined(__APPLE__)
	static sem_t	 master_sem;
	static sem_t	 threads_sem;
	static sem_t	 finished_threads_sem;
#else
	static dispatch_semaphore_t
			 master_sem;
	static dispatch_semaphore_t
			 threads_sem;
	static dispatch_semaphore_t
			 finished_threads_sem;
#endif
static unsigned		 sem_val_max_exceeded_cnt = 0;	// - _POSIX_SEM_VALUE_MAX == 32767, so this variable counts all above this value
static pthread_mutex_t	 sem_val_max_exceeded_cnt_lock = PTHREAD_MUTEX_INITIALIZER; // - for protecting "sem_val_max_exceeded_cnt"

/////////////////////////////////////////////////////////////////////////////

static inline __attribute__((always_inline)) void do_chown(
	const char *path,
	const uid_t new_owner,
	const gid_t new_group)
{
	int rc;

        rc = lchown(path, new_owner, new_group);
        if (rc < 0) {
                switch (errno) {
                	case EACCES:
                        	file_no_access++;
                                break;
                        case ENOENT:
                                file_not_found++;
                                break;
                        default:
                                file_any_other_error++;
                }
		pthread_mutex_lock(&perror_lock);
                perror("chown()");
		pthread_mutex_unlock(&perror_lock);
	} else {
#             if defined(PR_ATOMIC_ADD)
                PR_ATOMIC_ADD(&entries_chowned, 1);
#             else
                pthread_mutex_lock(&entries_chowned_lock);
		entries_chowned++;
                pthread_mutex_unlock(&entries_chowned_lock);
#             endif
	}
}

/////////////////////////////////////////////////////////////////////////////

#include "commonlib.h"

/////////////////////////////////////////////////////////////////////////////

// Used by walk_dir:
static inline void handle_dirent(dirlist_t *, struct dirent *);

/////////////////////////////////////////////////////////////////////////////

static void walk_dir(
	dirlist_t *curdir)
{
	DIR *dir = NULL;
#if defined(__linux__) || defined(__FreeBSD__) || defined(__OpenBSD__)
	unsigned fd = 0;    		// - only used on Linux/*BSD if option -X is given
	char *buf = NULL;   		// - same
	unsigned bpos = 0, nread = 0;	// - same
#endif
	struct dirent *dent = NULL;

#     if defined(DEBUG2)
	if (getenv("DEBUG2") && curdir->depth <= 2)
		fprintf(stderr, "- opendir(%s)\n", curdir->dirpath);
#     endif
	//assert(curdir->dirpath);

#    if defined(__linux__) || defined(__FreeBSD__) || defined(__OpenBSD__)
	if (extreme_readdir) {
		if ((fd = open(curdir->dirpath, O_RDONLY | O_DIRECTORY)) < 0) {
			pthread_mutex_lock(&perror_lock);
			perror(curdir->dirpath);
			pthread_mutex_unlock(&perror_lock);
			return;
		}
		dent = malloc(sizeof(struct dirent));
		assert(dent);
		buf = malloc(buf_size);
		assert(buf);
	} else
#    endif
	if (! (dir = opendir(curdir->dirpath))) {
			pthread_mutex_lock(&perror_lock);
			perror(curdir->dirpath);
			pthread_mutex_unlock(&perror_lock);
			return;
	}

	if (curdir->st_nlink < 2 && ! simulate_posix_compliance) {
		if (debug)	
			fprintf(stderr, "POSIX non-compliance detected on %s - setting simulate_posix_compliance = TRUE\n", curdir->dirpath);
		simulate_posix_compliance = TRUE;
		curdir->st_nlink = DIRTY_CONSTANT;
	}

	while (TRUE) {
		//assert(dir); // - something is seriously wrong if dir == 0 here...
#	      if defined(__linux__) || defined(__FreeBSD__) || defined(__OpenBSD__)
		if (extreme_readdir) {
			readdir_extreme(fd, buf, buf_size, curdir->dirpath, &bpos, dent, &nread);
			if (! nread) {
				close(fd);
				free(buf);
				free(dent);
				dent = NULL;
			}
		} else
#	      endif
		dent = readdir(dir);

		if (dent == NULL)
			break;

#	     if defined(DEBUG2)
		if (getenv("DEBUG2") && curdir->depth <= 2)
			fprintf(stderr, "- readdir(%s) done, dent=<%s>\n", curdir->dirpath, dent->d_name);
#	     endif

		if (dent->d_name[0] == '.' && 
			(dent->d_name[1] == 0 ||
			(dent->d_name[1] == '.' && dent->d_name[2] == 0)))
				continue;       // Skip "." and ".."

		handle_dirent(curdir, dent);
	}

#     if defined(__linux__) || defined(__FreeBSD__) || defined(__OpenBSD__)
	if (! extreme_readdir)
#     endif
		closedir(dir);

	if (! dryrun) {
		if (! filetypemask || (filetypemask&FILETYPE_DIR)) {
			if ((new_uid >= 0 && new_uid != curdir->st_uid) || (new_gid >= 0 && new_gid != curdir->st_gid))
				do_chown(curdir->dirpath, new_uid, new_gid);
		}
	}

	if (curdir->dirpath)
		free(curdir->dirpath);

	return;
}

/////////////////////////////////////////////////////////////////////////////

static inline __attribute__((always_inline)) void handle_dirent(
	dirlist_t *curdir,
	struct dirent *dent)
{
	boolean dive_into_subdir = FALSE;
	int rc, i;
	struct stat st;
	st.st_dev = 0;
	st.st_uid = -1;
	st.st_gid = -1;

	// Getting path
	size_t path_len = strlen(curdir->dirpath) + 1 + strlen(dent->d_name);
	char *path = malloc(path_len+1);
	assert(path);
	strcpy(path, curdir->dirpath);
	if (! (path[0] == '/' && path[1] == 0)) strcat(path, "/"); // - only add / if path != /
	strcat(path, dent->d_name);

#     if defined(DEBUG2)
	if (getenv("DEBUG2") && curdir->depth <= 2)
		fprintf(stderr, "-> handle_dirent(): d_name=\"%s\" of dirpath=\"%s\" path=\"%s\", d_type=%i, n_link=%u\n",
			dent->d_name, curdir->dirpath, path, dent->d_type, curdir->st_nlink);
#     endif

	// Getting stat if there might be subdirs below
#if defined(__linux__) || defined(__FreeBSD__) || defined(__OpenBSD__) || defined(__APPLE__)
	if (dent->d_type == DT_DIR
	   || dent->d_type == DT_UNKNOWN) {
		// We might get d_type == DT_UNKNOWN (0):
		// - on directories we don't own ourselves.
		// - on NFS shares.
		if (debug)
			fprintf(stderr, "handle_dirent(): lstat(%s) [nlink=%i]\n", path, curdir->st_nlink);
		rc = lstat(path, &st);
		if (rc && errno == EACCES) {
			pthread_mutex_lock(&perror_lock);
			perror(path);
			pthread_mutex_unlock(&perror_lock);
		}

		if (dent->d_type == DT_UNKNOWN) {
#                     if defined(PR_ATOMIC_ADD)
                        PR_ATOMIC_ADD(&statcount_unexp, 1);
#                     else
                        pthread_mutex_lock(&statcount_unexp_lock);
			statcount_unexp++;
                        pthread_mutex_unlock(&statcount_unexp_lock);
#                     endif

			switch (st.st_mode & S_IFMT) {
				case S_IFREG:
					dent->d_type = DT_REG;
					break;
				case S_IFDIR:
					dent->d_type = DT_DIR;
					break;
				case S_IFBLK:
					dent->d_type = DT_BLK;
					break;
				case S_IFCHR:
					dent->d_type = DT_CHR;
					break;
				case S_IFIFO:
					dent->d_type = DT_FIFO;
					break;
				case S_IFLNK:
					dent->d_type = DT_LNK;
					break;
				case S_IFSOCK:
					dent->d_type = DT_SOCK;
					break;
			}
		} else {
#     		      if defined(PR_ATOMIC_ADD)
        		PR_ATOMIC_ADD(&statcount, 1);
#     		      else
        		pthread_mutex_lock(&statcount_lock);
			statcount++;
        		pthread_mutex_unlock(&statcount_lock);
#     		      endif
		}
	}

	if (dent->d_type == DT_DIR) {
		dive_into_subdir = TRUE;

		if (xdev && curdir->st_dev != st.st_dev)
			dive_into_subdir = FALSE;
	}
#else // - non-Linux/BSD goes here: // - non-Linux/BSD goes here:
        if (curdir->st_nlink > 2) {
#             if defined(PR_ATOMIC_ADD)
                PR_ATOMIC_ADD(&statcount, 1);
#             else
                pthread_mutex_lock(&statcount_lock);
                statcount++;
                pthread_mutex_unlock(&statcount_lock);
#             endif

		rc = lstat(path, &st);
		if (rc && errno == EACCES) {
			pthread_mutex_lock(&perror_lock);
			perror(path);
			pthread_mutex_unlock(&perror_lock);
		}

		if (S_ISDIR(st.st_mode)) {
			dive_into_subdir = TRUE;

			if (xdev && curdir->st_dev != st.st_dev)
				dive_into_subdir = FALSE;
		}
	}
#endif

	if (dive_into_subdir) {
		if (maxdepth) {
			if (curdir->depth >= maxdepth) {
				free(path);
				return;
			}
		}
		if (excludelist_count > 0) {
                	for (i = 0; i < excludelist_count; i++)
                        	if (excluderecomp) {
                                	if (regexec(excluderecomp[i], dent->d_name, 0, NULL, 0) == 0) {
                                        	if (debug) fprintf(stderr, "==> Skipping dir %s (%s)\n", path, excludelist[i]);
                                        	return;         // - skip directories specified through -e
                                	}
                        	} else {
                                	if (strcmp(excludelist[i], dent->d_name) == 0) {
                                        	if (debug) fprintf(stderr, "==> Skipping dir %s (%s)\n", path, excludelist[i]);
                                        	return;         // - skip directories specified through -E
                                	}
                        	}
        	}

		if (dryrun
		    && (! filetypemask || (filetypemask & FILETYPE_DIR)))
			puts(path);

               if (inline_processing_threshold &&
                    (curdir->st_nlink < inline_processing_threshold + 2 ||                              // - posix compliant
                    (simulate_posix_compliance && curdir->inlined < inline_processing_threshold))) {    // - non-compliant (btrfs)
                        // Process up to n subdirs inline, n = inline_processing_threshold.
			curdir->inlined++;

			dirlist_t subdirentry;

			subdirentry.dirpath = strdup(path);
			assert(subdirentry.dirpath);
			subdirentry.depth = curdir->depth+1;
			subdirentry.inlined = 0;
			subdirentry.st_nlink = simulate_posix_compliance ? DIRTY_CONSTANT : st.st_nlink;
			subdirentry.st_dev = st.st_dev;
			subdirentry.st_uid = st.st_uid;
			subdirentry.st_gid = st.st_gid;
			subdirentry.filecnt = 0;

			walk_dir(&subdirentry);
		} else {
                        // - The first n subdirs, n <= inline_processing_threshold, will be enqueued and processed when a thread is available.
                        dirlist_add_dir(path, curdir->depth+1, &st);
		}
	} else if (! filetypemask || (filetypemask&FILETYPE_REGFILE)) {
                if (dryrun) {
                        puts(path);
                } else {
			// - If we don't have an lstat() filled st struct so far, just set the new user/group instead of the more time consuming procedure of running lstat() and check old values.
			if ((st.st_uid >= 0 && st.st_uid != new_uid) || (st.st_gid >= 0 && st.st_gid != new_gid))
				do_chown(path, new_uid, new_gid);
		}
	}

	free(path);

	return;
}

/////////////////////////////////////////////////////////////////////////////

static int usage(
	char *argv[])
{
	char *progname = strrchr(argv[0], '/');
	if (progname) progname++; // - move pointer past the found '/'
	else progname = argv[0];

        printf("Usage: %s [-t <count>] [-I <count>] [-e <dir> ... | -E <dir> ... | -Z] [-x] [-m <maxdepth>]\n", progname);
	printf("\t\t [-f] [-d] [-n] [-I <count>] [-q | -Q] [-X] [-T] [-S] [-V] [user][:group] arg1 [arg2 ...]\n");
        printf("-t <count>\t Run up to <count> threads in parallel.\n");
        printf("\t\t * Must be a non-negative integer between 1 and %i.\n", MAX_THREADS);
        printf("\t\t * Defaults to (virtual) CPU count on host, up to 8.\n");
        printf("\t\t * Note that <count> threads will be created in addition to the main thread,\n");
        printf("\t\t   so the total thread count will be <count+1>, but the main, controlling thread will be mostly idle.\n\n");

        printf("-e <dir>\t Exclude directory matching <dir> from traversal.\n");
        printf("\t\t * Extended regular expressions are supported.\n");
        printf("\t\t * Any number of -e options are supported, up to command line limit.\n\n");

	printf("-E <dir>\t Exclude directory <dir> from traversal.\n");
        printf("\t\t * For simplicity, only exact matches are excluded.\n");
        printf("\t\t * Any number of -E options are supported, up to command line limit.\n");
        printf("\t\t * Hint: Excluding .snapshot is usually desired on (the root of) NFS shares from NAS.\n\n");

        printf("-Z\t\t Equivalent to -E.snapshot.\n");
        printf("\t\t * Just to save some typing since it is commonly needed on a NAS NFS share.\n\n");

        printf("-x\t\t Only traverse the file system(s) containing the directory/directories specified.\n");
        printf("\t\t * This equals the -xdev option to find(1).\n\n");

        printf("-m <maxdepth>\t Descend at most <maxdepth> (a positive integer) levels below the start point(s).\n");
        printf("\t\t * This equals the -maxdepth option to GNU find(1).\n\n");

	printf("-f\t\t Just chown() all types of files without affecting directories.\n");
        printf("\t\t * May be combined with -d.\n\n");
	printf("-d\t\t Just chown() directories without affecting any other file type.\n");
        printf("\t\t * May be combined with -f.\n\n");

	printf("-n\t\t Can be used to dry-run before actually chown()'ing anything.\n");
	printf("\t\t * Files and directories will just be listed on stdout, and WILL NOT be chown()'ed.\n\n");

        printf("-I <count>\t Use <count> as number of subdirectories in a directory, that should\n");
        printf("\t\t be processed in-line instead of processing them in separate threads.\n");
        printf("\t\t * Default is to process the first two subdirectories in a directory in-line.\n");
        printf("\t\t * This is a performance option to possibly squeeze out even faster run-times.\n");
        printf("\t\t * Use 0 for no in-line processing.\n");
        printf("\t\t * Only meaningful for POSIX compliant file systems, where directory link count is 2 plus number of subdirs.\n\n");

	printf("-q\t\t Organize the queue of directories as a FIFO which may be faster in some cases (default is LIFO).\n");
        printf("\t\t * The speed difference between a LIFO and a FIFO queue is usually small.\n");
        printf("\t\t * Note that this option will make '%s' use more memory.\n\n", progname);

        printf("-Q\t\t Organize the queue of directories as a list sorted on inode number.\n");
        printf("\t\t * Using this option with a file system on a single (or mirrored) spinning disk is recommended.\n");
        printf("\t\t * Using it on a storage array or on SSD or FLASH disk is probably pointless.\n\n");

#if defined(__linux__) || defined(__FreeBSD__) || defined(__OpenBSD__)
        printf("-X\t\t May be used to speed up %s'ing eXtremely big directories containing millions of files.\n", progname);
        printf("\t\t * Default maximum number of dirents read in one go is 100000.\n");
        printf("\t\t * Environment variable DIRENTS may be set to override the default.\n\n");
#endif

        printf("-S\t\t Print some stats to stderr when finished.\n");
        printf("-T\t\t Print the elapsed real time between invocation and termination of the program on stderr, like time(1).\n");
        printf("-V\t\t Print out version and exit.\n");
        printf("-h\t\t Print this help text.\n");

        printf("\n* If no argument is specified, this help text will be printed to stdout.\n");
        printf("* User and/or group must always be specified.\n");
        printf("  Numeric uid/gid is supported in addition to user/group name.\n");
        printf("* All arguments (arg1 arg2 ...) should be directories or symlinks to directories.\n");
        printf("  If some of them are not, they will just be excluded and an error message will be printed for each.\n");
        printf("  All files and directories below the start point(s) will by default be chown()'ed in parallel\n");
	printf("  (in addition to the start point(s)).\n");
        printf("  To dry-run before actually chown()'ing anything, please use the -n option, e.g.:\n");
        printf("  `%s -n johndoe arg1 arg2 ...`\n", progname);
        printf("* The program has been tested with start point(s) on these file systems:\n");
        printf("  - Linux: ext2, ext3, ext4, xfs, jfs, btrfs, nilfs2, f2fs, zfs, tmpfs\n");
	printf("           reiserfs, hfs plus, minix, bfs, ntfs (fuseblk), vxfs, gpfs\n");
        printf("  - FreeBSD: ufs, zfs, devfs, ms-dos/fat\n");
        printf("  - OpenBSD: ffs\n");
        printf("  - MacOS: apfs\n");
        printf("  - AIX: jfs, jfs2, ahafs\n");
        printf("  - HP-UX: vxfs, hfs\n");
        printf("  - Solaris: zfs, ufs, udfs\n");
        printf("  - All: nfs\n");

	printf("* The program contains code inspired by https://github.com/xaionaro/libpftw\n");
	printf("* Warning: This program may impose a very high load on your storage systems when utilizing many CPU cores.\n");
	printf("* The \"%s\" program comes with ABSOLUTELY NO WARRANTY.  This is free software, and you are welcome\n", progname);
	printf("  to redistribute it under certain conditions.  See the GNU General Public Licence for details.\n");

	printf("\nCopyright (C) 2020 - 2024 by Jorn I. Viken, jornv@1337.no.\n");
	return -1;
}

////////////////////////////////////////////////////////////////////////////

int main(
	int argc,
	char *argv[])
{
	char **startdirs;
	unsigned startdircount;
	int ch;
	boolean stats = FALSE;
	boolean e_option = FALSE, E_option = FALSE;
	struct timeval starttime;
	boolean timer = FALSE;
	unsigned threads = 1;
#    if defined(__hpux)
	struct pst_dynamic psd;

	if (pstat_getdynamic(&psd, sizeof(psd), (size_t)1, 0))
		threads = (unsigned) psd.psd_proc_cnt;
#    elif defined(__MINGW32__)
	SYSTEM_INFO sysinfo;
	GetSystemInfo(&sysinfo);
	threads = sysinfo.dwNumberOfProcessors;
#    else
	threads = (unsigned) sysconf(_SC_NPROCESSORS_ONLN);
#    endif
	if (threads > 8)
		threads = 8; // - using 8 as default max number of threads

        progname = strrchr(argv[0], '/');
        if (progname)
                progname++; // - move pointer past the found '/'
        else
                progname = argv[0];

	debug = getenv("DEBUG") != NULL;

	tzset(); // - core dumps on Ubuntu 16.04.6 LTS with kernel 4.4.0-174-generic when executed through localtime() at the end of main()

	while ((ch = getopt(argc, argv, "ht:I:e:E:Zfdm:nvxqQSTVX")) != -1)
		switch (ch) {
			case 't':
				threads = atoi(optarg);
				if (threads < 1 || threads > MAX_THREADS)
					return usage(argv);
				break;
			case 'I':
				inline_processing_threshold = atoi(optarg);
				break;
			case 'e':
				if (E_option) {
					fprintf(stderr, "Option -e can not be combined with -E.\n");
					exit(1);
				}
				excludelist = realloc(excludelist, (excludelist_count + 1) * sizeof(excludelist));
				assert(excludelist);
				excludelist[excludelist_count] = optarg;
				excluderecomp = realloc(excluderecomp, (excludelist_count + 1) * sizeof(excluderecomp));
				assert(excluderecomp);
				if (! regex_init(&excluderecomp[excludelist_count], optarg, REG_EXTENDED|REG_NOSUB))
					return usage(argv);
				excludelist_count++;
				e_option = TRUE;
				break;
			case 'E':
                        case 'Z':
				if (e_option) {
					fprintf(stderr, "Option -E  / -Z can not be combined with -e.\n");
					exit(1);
				}
				excludelist = realloc(excludelist, (excludelist_count + 1) * sizeof(excludelist));
				assert(excludelist);
                                if (ch == 'E')
                                        excludelist[excludelist_count++] = optarg;
                                else
                                        excludelist[excludelist_count++] = ".snapshot";
				E_option = TRUE;
				break;
       		        case 'f':
	                        filetypemask |= FILETYPE_REGFILE;
               		        break;
                	case 'd':
                        	filetypemask |= FILETYPE_DIR;
                        	break;
			case 'm':
				if (atoi(optarg) < 1)
					return usage(argv);
				maxdepth = atoi(optarg);
				break;
			case 'n':
				dryrun = TRUE;
				break;
			case 'v':
				if (atoi(optarg) < 1)
					return usage(argv);
				verbose_count = atoi(optarg);
				break;
			case 'x':
				xdev = TRUE;
				break;
			case 'q':
				fifo_queue = TRUE;
                        	lifo_queue = FALSE;
                        	ino_queue = FALSE;
				break;
			case 'Q':
                        	ino_queue = TRUE;
                        	lifo_queue = FALSE;
                        	fifo_queue = FALSE;
				break;
			case 'S':
				stats = TRUE;
				break;
			case 'T':
				timer = TRUE;
				(void) gettimeofday(&starttime, NULL);
				break;
			case 'V':
				printf("%s\n", VERSION);
				exit(0);
				break;
			case 'X':
#			      if defined(__linux__) || defined(__FreeBSD__) || defined(__OpenBSD__)
				extreme_readdir = TRUE;
				if (getenv("DIRENTS"))
					buf_size = atoi(getenv("DIRENTS")) * sizeof(struct dirent);
				else
					buf_size = DEFAULT_DIRENT_COUNT * sizeof(struct dirent);
#			      else
				fprintf(stderr, "Option -X is not implemented for this OS.\n");
				exit(1);
#			      endif
				break;
			case 'h':
			case '?':
			default:
				return usage(argv);
		}

	argc -= optind;
	argv += optind;

	if (argc < 1) {
		fprintf(stderr, "Too few arguments - bailing out...\n");
		return usage(argv-optind);
	} else {
		char *ugptr = *argv;
		if (isdigit((int)*ugptr)) {
			// uid given, and maybe group name or gid
			char *separator = strchr(ugptr, ':');
			if (separator) {
				*separator = '\0';
				new_uid = strtoul(ugptr, NULL, 10);
				ugptr = separator + 1;
				new_gid = isdigit((int)*ugptr) ? strtoul(ugptr, NULL, 10)
						: groupname_to_gid_or_exit(ugptr);
			} else {
				// just uid given
				new_uid = strtoul(ugptr, NULL, 10);
				new_gid = -1;
			}
		} else {
			if (*ugptr == ':') {
				// - just group name or gid given
				new_uid = -1;
				ugptr++;
				if (isdigit((int)*ugptr)) {
					// - numeric gid given
					new_gid = strtoul(ugptr, NULL, 10);
				} else {
					// - group name given
					new_gid = groupname_to_gid_or_exit(ugptr);
				}
			} else {
				// - user name given, and maybe group name or gid
				char *separator = strchr(ugptr, ':');
				if (separator) {
					*separator = '\0';
					new_uid = username_to_uid_or_exit(ugptr);
					ugptr = separator + 1;
					new_gid = isdigit((int)*ugptr) ? strtoul(ugptr, NULL, 10)
						: groupname_to_gid_or_exit(ugptr);
				} else {
					// - just user name or uid given
					new_uid = isdigit((int)*ugptr) ? strtoul(ugptr, NULL, 10)
							: username_to_uid_or_exit(ugptr);
					new_gid = -1;
				}
			}
		}

		if (debug)
			fprintf(stderr, "uid = %i, gid = %i\n", new_uid, new_gid);

		startdirs = ++argv;
		startdircount = argc-1;
	}

	if (debug && filetypemask)
		fprintf(stderr, "Filetypemask=%i\n", filetypemask);

	if (threads == 1)
                inline_processing_threshold = DIRTY_CONSTANT; // - process everything inline if we have just 1 CPU...

	thread_cnt = threads;
	thread_prepare();

	traverse_trees(startdirs, startdircount);

	thread_cleanup();

	if (timer) {
		struct timeval endtime;
		(void) gettimeofday(&endtime, NULL);
		fflush(stdout);
		fprintf(stderr, "Real: %.2f seconds\n",
			(double)(((endtime.tv_sec-starttime.tv_sec)*1000 + (endtime.tv_usec-starttime.tv_usec) / 1000)) / 1000);
	}

	if (stats) {
		fprintf(stderr, "+------------------------------+\n");
		fprintf(stderr, "| Some final tidbits from \"-S\" |\n");
		fprintf(stderr, "+------------------------------+\n");
		fprintf(stderr, "- Version: %s\n", VERSION);
		fprintf(stderr, "- Number of active threads used: %i\n", threads);
		fprintf(stderr, "- Number of subdirectories processed in-line per directory (and not in a separate thread): %i\n", inline_processing_threshold);
#if 	      defined(__linux__) || defined(__FreeBSD__) || defined(__OpenBSD__)
		if (extreme_readdir) {
			fprintf(stderr, "- Number of SYS_getdents system calls = %u\n", getdents_calls);
			fprintf(stderr, "- Used DIRENTS = %lu\n", (unsigned long)buf_size / sizeof(struct dirent));
		}
#	      endif
		fprintf(stderr, "- Mandatory lstat calls (at least 1 per directory): %i\n", statcount);
#	      if defined(__linux__) || defined(__FreeBSD__) || defined(__OpenBSD__) || defined(__APPLE__)
		fprintf(stderr, "- Unexpected lstat calls (when returned d_type is DT_UNKNOWN): %i\n", statcount_unexp);
#	      endif
		fprintf(stderr, "- Number of queued directories: %i\n", queued_dirs);
		fprintf(stderr, "- Number of files/directories chown()'ed: %i\n", entries_chowned);
                fprintf(stderr, "- Unsuccessful chown() calls, type EACCES: %i\n", file_no_access);
                fprintf(stderr, "- Unsuccessful chown() calls, type ENOENT: %i\n", file_not_found);
                fprintf(stderr, "- Unsuccessful chown() calls, type \"any other reason\": %i\n", file_any_other_error);

#             if defined(PR_ATOMIC_ADD)
		fprintf(stderr, "- Program compiled with support for __sync_add_and_fetch\n");
#             endif
#             if defined(CC_USED)
                fprintf(stderr, "- Compiled using: %s\n", CC_USED);
#             endif
	}
	return 0;
}
