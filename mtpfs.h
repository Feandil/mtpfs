#ifndef _MTPFS_H_
#define _MTPFS_H_

#ifdef HAVE_CONFIG_H
# include "config.h"
#endif

#if DEBUG
# define G_DEBUG_LOCKS
#endif

#ifdef linux
/* For pread()/pwrite() */
# define _XOPEN_SOURCE 500
#endif

#define FUSE_USE_VERSION 26

#define MAX_STORAGE_AREA 4

#endif /* _MTPFS_H_ */
