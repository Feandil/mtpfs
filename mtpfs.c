/*
    FUSE: Filesystem in Userspace
    Copyright (C) 2001-2005  Miklos Szeredi <miklos@szeredi.hu>

    This program can be distributed under the terms of the GNU GPL.
    See the file COPYING.
*/

/* Headers */
#include "mtpfs.h"

#include <assert.h>
#include <dirent.h>
#include <errno.h>
#include <fuse.h>
#include <fcntl.h>
#include <getopt.h>
#include <glib.h>
#include <glib/gprintf.h>
#include <libmtp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <sys/mman.h>
#include <sys/statfs.h>
#include <unistd.h>


/* Debugging macro */

#if DEBUG
# define STRINGIFY(x) #x
# define TOSTRING(x) STRINGIFY(x)
# define DBG(a...) {g_printf( "[" __FILE__ ":" TOSTRING(__LINE__) "] " a );g_printf("\n");}
# ifdef DEBUG_FUNC
#  define DBG_F(a...) DBG(a)
# else
#  define DBG_F(a...)
# endif
static void dump_mtp_error(LIBMTP_mtpdevice_t *device)
{
    LIBMTP_Dump_Errorstack(device);
    LIBMTP_Clear_Errorstack(device);
}
#else
# define DBG(a...)
# define DBG_F(a...)
# define dump_mtp_error(a)
#endif

/* Private struct */

typedef struct
{
    LIBMTP_devicestorage_t *storage;
    LIBMTP_folder_t *folders;
    gboolean folders_changed;
} StorageArea;

/* Static variables */
static LIBMTP_mtpdevice_t *device;
static StorageArea storageArea[MAX_STORAGE_AREA];
static LIBMTP_file_t *files = NULL;
static gboolean files_changed = TRUE;
static GSList *lostfiles = NULL;
static GHashTable *myfiles = NULL;

G_LOCK_DEFINE_STATIC(device_lock);
#define return_unlock(a)       do { G_UNLOCK(device_lock); return a; } while(0)

/* Freeing tree representation */
static void
free_files(LIBMTP_file_t *filelist)
{
    DBG_F("Free_files(%p)", filelist);

    LIBMTP_file_t *file = filelist, *tmp;
    while (file) {
        tmp = file;
        file = file->next;
        LIBMTP_destroy_file_t(tmp);
    }
}

/* Checking tree representation */
static void
check_files ()
{
    DBG_F("check_files()");

    if (files_changed) {
        DBG("Refreshing Filelist");
        if (files) free_files(files);
        files = LIBMTP_Get_Filelisting_With_Callback(device, NULL, NULL);
        files_changed = FALSE;
        //check_lost_files ();
        DBG("Refreshing Filelist exiting");
    }
}

static void
check_lost_files ()
{
    uint32_t last_parent_id = 0xFFFFFFFF;
    gboolean last_parent_found = FALSE;
    LIBMTP_file_t *item;

    DBG_F("check_lost_files()");

    if (lostfiles != NULL)
        g_slist_free (lostfiles);

    lostfiles = NULL;
    for (item = files; item != NULL; item = item->next) {
        gboolean parent_found;

        if (last_parent_id == 0xFFFFFFFF || last_parent_id != item->parent_id) {
            if (item->parent_id == 0) {
                parent_found = TRUE;
            } else {
                int i;
                for (i = 0; i < MAX_STORAGE_AREA; ++i) {
                    if (storageArea[i].folders!=NULL) {
                        if (LIBMTP_Find_Folder (storageArea[i].folders, item->parent_id) != NULL) {
                            parent_found = FALSE;
                        }
                    }
                }
            }
            last_parent_id = item->parent_id;
            last_parent_found = parent_found;
        } else {
            parent_found = last_parent_found;
        }
        DBG("MTPFS checking for lost files %s, parent %d - %s", item->filename, last_parent_id, ( parent_found ? "FALSE" : "TRUE" ) );
        if (parent_found == FALSE) {
            lostfiles = g_slist_append (lostfiles, item);
        }
    }
    DBG("MTPFS checking for lost files exit found %d lost tracks", g_slist_length (lostfiles) );
}

static void
check_folders ()
{
    int i;

    DBG_F("check_folders()");

    for (i = 0; i < MAX_STORAGE_AREA; ++i) {
        if (storageArea[i].folders_changed) {
            DBG("Refreshing Folderlist %d-%s", i,storageArea[i].storage->StorageDescription);
            if (storageArea[i].folders) {
                LIBMTP_destroy_folder_t(storageArea[i].folders);
            }
            storageArea[i].folders = LIBMTP_Get_Folder_List_For_Storage(device, storageArea[i].storage->id);
            storageArea[i].folders_changed= FALSE;
        }
    }
}

/* Finding elements in representation */

static int
find_storage(const gchar * path)
{
    int i;
    gsize storage_len;
    gchar * second_slash;

    DBG_F("find_storage(%s)", path);

    // Skip initial '/'
    if (*path != '/') {
       DBG("find_storage: internal error: unexpected root");
       return -1;
    }
    ++path;

    // find storage len
    second_slash = strstr(path, "/");
    if (second_slash == NULL) {
        storage_len = strlen(path);
    } else {
        assert(second_slash > path);
        storage_len = (gsize)(second_slash - path);
    }

    for (i = 0; i < MAX_STORAGE_AREA; ++i) {
        if (storageArea[i].storage != NULL) {
            if ((storage_len == strlen(storageArea[i].storage->StorageDescription)) &&
                (strncmp(storageArea[i].storage->StorageDescription, path, storage_len) == 0)) {
                DBG("find_storage:%s found as %d", storageArea[i].storage->StorageDescription, i);
                return i;
            }
        }
    }
    DBG("find_storage: %s not found", path - 1);
    return -1;
}

static uint32_t
lookup_folder_id (LIBMTP_folder_t * folder, const gchar * path)
{
    gchar ** fields;
    gsize pos;
    uint32_t ret = 0xFFFFFFFF;

    DBG_F("lookup_folder_id(%p, %s)", folder, path);

    if (folder == NULL) {
        DBG_F("lookup_folder_id: Empty list");
        return 0xFFFFFFFF;
    }
    if (path[0] != '/') {
        DBG("lookup_folder_id: Internal error: unexpected root")
        return 0xFFFFFFFF;
    }

    check_folders();

    fields = g_strsplit(path + 1, "/", -1);

    if (fields[1] == NULL) {
        DBG("lookup_folder_id: Storage dir");
        return 0;
    }

    //DBG("lookup_folder_id: Strip storage area name");
    pos = 1;

    while (fields[pos] != NULL && folder != NULL) {
        if (*fields[pos] == '\0') {
            //DBG("lookup_folder_id: Skipping empty part in path");
            ++pos;
            continue;
        }
        //DBG("lookup_folder_id: Compare %s(%i) and %s", fields[pos], pos, folder->name);
        if (g_ascii_strncasecmp(fields[pos], folder->name, strlen(folder->name)) == 0) {
            //DBG("lookup_folder_id: match, going deeper");
            ret = folder->folder_id;
            ++pos;
            folder = folder->child;
        } else {
            //DBG("lookup_folder_id: no match, try sibling");
            folder = folder->sibling;
        }
    }

    if (fields[pos] == NULL) {
        DBG("lookup_folder_id %s: found %i", path, ret);
        return ret;
    }
    g_strfreev(fields);
    DBG("lookup_folder_id %s: not found", path);
    return 0xFFFFFFFF;
}

static uint32_t
parse_path (const gchar * path)
{
    uint32_t res;
    uint32_t item_id = 0xFFFFFFFF;
    int i;

    DBG_F("parse_path(%s)", path);

    // Check lost+found
    if (strncmp("/lost+found", path, 11) == 0) {
        GSList *item;
        gchar *filename  = g_path_get_basename (path);

        res = 0xFFFFFFFF;
        for (item = lostfiles; item != NULL; item = g_slist_next (item) ) {
            LIBMTP_file_t *file = (LIBMTP_file_t *) item->data;

            if (strcmp( file->filename, filename) == 0) {
                res = file->item_id;
                break;
            }
        }
        g_free (filename);
        return res;
    }

    // Check device
    LIBMTP_folder_t *folder;
    gchar **fields;
    gchar *directory;
    size_t path_len = strlen (path) + 1;
    directory = (gchar *) g_malloc(path_len);
    if (directory == NULL) {
        DBG("Memory error")
        res = 0xFFFFFFFF;
        goto end;
    }
    *directory = '\0';
    fields = g_strsplit (path, "/", -1);
    res = 0xFFFFFFFF;
    int storageid;
    storageid = find_storage(path);
    for (i = 0; fields[i] != NULL; i++) {
        if (strlen (fields[i]) > 0) {
            if (fields[i + 1] != NULL) {
                if (path_len < (strlen(fields[i]) + 2)) {
                    DBG("INTERNAL ERROR, please report");
                    res = 0xFFFFFFFF;
                    goto freeall;
                }
                directory = strncat (directory, "/", path_len);
                --path_len;
                directory = strncat (directory, fields[i], path_len);
                path_len -= strlen(fields[i]);
            } else {
                check_folders();
                folder = storageArea[storageid].folders;
                uint32_t folder_id = 0;
                if (strcmp (directory, "") != 0) {
                    folder_id = lookup_folder_id (folder, directory);
                }
                DBG("parent id:%d:%s", folder_id, directory);
                LIBMTP_file_t *file;
                check_files();
                file = files;
                while (file != NULL) {
                    if (file->parent_id == folder_id) {
                        if (folder_id == 0 && (file->storage_id != storageArea[storageid].storage->id)) {
                            goto next;
                        }
                        if (file->filename == NULL) DBG("MTPFS filename NULL");
                        if (file->filename != NULL && g_ascii_strcasecmp (file->filename, fields[i]) == 0) {
                            DBG("found:%d:%s", file->item_id, file->filename);

                            item_id = file->item_id;
                            break; // found!
                        }
                    }
next:
                    file = file->next;
                }
                if (item_id == 0xFFFFFFFF) {
                    if (path_len < (strlen(fields[i]) + 2)) {
                        DBG("INTERNAL ERROR, please report");
                        res = 0xFFFFFFFF;
                        goto freeall;
                    }
                    directory = strncat (directory, "/", path_len);
                    --path_len;
                    directory = strncat (directory, fields[i], path_len);
                    path_len -= strlen(fields[i]);
                    item_id = lookup_folder_id (folder, directory);
                    res = item_id;
                    break;
                } else {
                    res = item_id;
                    break;
                }
            }
        }
    }
freeall:
    g_strfreev (fields);
    g_free (directory);
end:
    DBG("parse_path exiting:%s - %d",path,res);
    return res;
}

/* Find the file type based on extension */
static LIBMTP_filetype_t
find_filetype (const gchar * filename)
{
    DBG("find_filetype");
    gchar **fields;
    fields = g_strsplit (filename, ".", -1);
    gchar *ptype;
    ptype = g_strdup (fields[g_strv_length (fields) - 1]);
    g_strfreev (fields);
    LIBMTP_filetype_t filetype;

    // This need to be kept constantly updated as new file types arrive.
    if (!g_ascii_strncasecmp (ptype, "wav",3)) {
        filetype = LIBMTP_FILETYPE_WAV;
    } else if (!g_ascii_strncasecmp (ptype, "mp3",3)) {
        filetype = LIBMTP_FILETYPE_MP3;
    } else if (!g_ascii_strncasecmp (ptype, "wma",3)) {
        filetype = LIBMTP_FILETYPE_WMA;
    } else if (!g_ascii_strncasecmp (ptype, "ogg",3)) {
        filetype = LIBMTP_FILETYPE_OGG;
    } else if (!g_ascii_strncasecmp (ptype, "aa",2)) {
        filetype = LIBMTP_FILETYPE_AUDIBLE;
    } else if (!g_ascii_strncasecmp (ptype, "mp4",3)) {
        filetype = LIBMTP_FILETYPE_MP4;
    } else if (!g_ascii_strncasecmp (ptype, "wmv",3)) {
        filetype = LIBMTP_FILETYPE_WMV;
    } else if (!g_ascii_strncasecmp (ptype, "avi",3)) {
        filetype = LIBMTP_FILETYPE_AVI;
    } else if (!g_ascii_strncasecmp (ptype, "mpeg",4) || !g_ascii_strncasecmp (ptype, "mpg",3)) {
        filetype = LIBMTP_FILETYPE_MPEG;
    } else if (!g_ascii_strncasecmp (ptype, "asf",3)) {
        filetype = LIBMTP_FILETYPE_ASF;
    } else if (!g_ascii_strncasecmp (ptype, "qt",2) || !g_ascii_strncasecmp (ptype, "mov",3)) {
        filetype = LIBMTP_FILETYPE_QT;
    } else if (!g_ascii_strncasecmp (ptype, "wma",3)) {
        filetype = LIBMTP_FILETYPE_WMA;
    } else if (!g_ascii_strncasecmp (ptype, "jpg",3) || !g_ascii_strncasecmp (ptype, "jpeg",4)) {
        filetype = LIBMTP_FILETYPE_JPEG;
    } else if (!g_ascii_strncasecmp (ptype, "jfif",4)) {
        filetype = LIBMTP_FILETYPE_JFIF;
    } else if (!g_ascii_strncasecmp (ptype, "tif",3) || !g_ascii_strncasecmp (ptype, "tiff",4)) {
        filetype = LIBMTP_FILETYPE_TIFF;
    } else if (!g_ascii_strncasecmp (ptype, "bmp",3)) {
        filetype = LIBMTP_FILETYPE_BMP;
    } else if (!g_ascii_strncasecmp (ptype, "gif",3)) {
        filetype = LIBMTP_FILETYPE_GIF;
    } else if (!g_ascii_strncasecmp (ptype, "pic",3) || !g_ascii_strncasecmp (ptype, "pict",4)) {
        filetype = LIBMTP_FILETYPE_PICT;
    } else if (!g_ascii_strncasecmp (ptype, "png",3)) {
        filetype = LIBMTP_FILETYPE_PNG;
    } else if (!g_ascii_strncasecmp (ptype, "wmf",3)) {
        filetype = LIBMTP_FILETYPE_WINDOWSIMAGEFORMAT;
    } else if (!g_ascii_strncasecmp (ptype, "ics",3)) {
        filetype = LIBMTP_FILETYPE_VCALENDAR2;
    } else if (!g_ascii_strncasecmp (ptype, "exe",3) || !g_ascii_strncasecmp (ptype, "com",3) ||
               !g_ascii_strncasecmp (ptype, "bat",3) || !g_ascii_strncasecmp (ptype, "dll",3) ||
               !g_ascii_strncasecmp (ptype, "sys",3)) {
        filetype = LIBMTP_FILETYPE_WINEXEC;
    } else if (!g_ascii_strncasecmp (ptype, "txt",3)) {
        filetype = LIBMTP_FILETYPE_TEXT;
    } else if (!g_ascii_strncasecmp (ptype, "htm",3) || !g_ascii_strncasecmp (ptype, "html",4) ) {
        filetype = LIBMTP_FILETYPE_HTML;
    } else if (!g_ascii_strncasecmp (ptype, "bin",3)) {
        filetype = LIBMTP_FILETYPE_FIRMWARE;
    } else if (!g_ascii_strncasecmp (ptype, "aac",3)) {
        filetype = LIBMTP_FILETYPE_AAC;
    } else if (!g_ascii_strncasecmp (ptype, "flac",4) || !g_ascii_strncasecmp (ptype, "fla",3)) {
        filetype = LIBMTP_FILETYPE_FLAC;
    } else if (!g_ascii_strncasecmp (ptype, "mp2",3)) {
        filetype = LIBMTP_FILETYPE_MP2;
    } else if (!g_ascii_strncasecmp (ptype, "m4a",3)) {
        filetype = LIBMTP_FILETYPE_M4A;
    } else if (!g_ascii_strncasecmp (ptype, "doc",3)) {
        filetype = LIBMTP_FILETYPE_DOC;
    } else if (!g_ascii_strncasecmp (ptype, "xml",3)) {
        filetype = LIBMTP_FILETYPE_XML;
    } else if (!g_ascii_strncasecmp (ptype, "xls",3)) {
        filetype = LIBMTP_FILETYPE_XLS;
    } else if (!g_ascii_strncasecmp (ptype, "ppt",3)) {
        filetype = LIBMTP_FILETYPE_PPT;
    } else if (!g_ascii_strncasecmp (ptype, "mht",3)) {
        filetype = LIBMTP_FILETYPE_MHT;
    } else if (!g_ascii_strncasecmp (ptype, "jp2",3)) {
        filetype = LIBMTP_FILETYPE_JP2;
    } else if (!g_ascii_strncasecmp (ptype, "jpx",3)) {
        filetype = LIBMTP_FILETYPE_JPX;
    } else {
        DBG("Sorry, file type \"%s\" is not yet supported", ptype);
        DBG("Tagging as unknown file type.");
        filetype = LIBMTP_FILETYPE_UNKNOWN;
    }
    g_free (ptype);
    return filetype;
}

static int
mtpfs_release (const char *path, struct fuse_file_info *fi)
{
    DBG("mtpfs_release(%s, %p)", path, fi);
    G_LOCK(device_lock);

    assert(fi->fh <= INT_MAX);

    int ret = 0;
    if (g_hash_table_contains(myfiles, path)) {
        //find parent id
        gchar *filename = g_strdup("");
        gchar **fields;
        gchar *directory;
        directory = (gchar *) g_malloc (strlen (path));
        directory = strcpy (directory, "/");
        fields = g_strsplit (path, "/", -1);
        int i;
        uint32_t parent_id = 0;
        int storageid;
        storageid = find_storage(path);
        for (i = 0; fields[i] != NULL; i++) {
            if (strlen (fields[i]) > 0) {
                if (fields[i + 1] == NULL) {
                    gchar *tmp = g_strndup (directory, strlen (directory) - 1);
                    parent_id = lookup_folder_id (storageArea[storageid].folders, tmp);
                    g_free (tmp);
                    if (parent_id == 0xFFFFFFF)
                        parent_id = 0;
                    g_free (filename);
                    filename = g_strdup (fields[i]);
                } else {
                    directory = strcat (directory, fields[i]);
                    directory = strcat (directory, "/");
                }
            }
        }
        DBG("%s:%s:%d", filename, directory, parent_id);

        struct stat st;
        uint64_t filesize;
        fstat((int)fi->fh, &st);
        assert(st.st_size >= 0);
        filesize = (uint64_t) st.st_size;

        // Setup file
        LIBMTP_filetype_t filetype;
        filetype = find_filetype (filename);
        LIBMTP_file_t *genfile;
        genfile = LIBMTP_new_file_t ();
        genfile->filesize = filesize;
        genfile->filetype = filetype;
        genfile->filename = g_strdup (filename);
        genfile->parent_id = (uint32_t) parent_id;
        genfile->storage_id = storageArea[storageid].storage->id;

        ret = LIBMTP_Send_File_From_File_Descriptor (device, (int)fi->fh,
                                                     genfile, NULL, NULL);
        LIBMTP_destroy_file_t (genfile);
        if (ret == 0) {
            DBG("Sent %s",path);
        } else {
            DBG("Problem sending %s - %d",path,ret);
        }
        // Cleanup
        g_strfreev (fields);
        g_free (filename);
        g_free (directory);
        // Refresh filelist
        files_changed = TRUE;
        g_hash_table_remove(myfiles, path);
    }
    close((int)fi->fh);
    G_UNLOCK(device_lock);
    return ret;
}

static void
mtpfs_destroy ()
{
    DBG("mtpfs_destroy()");
    G_LOCK(device_lock);

    if (files) free_files(files);
    int i;
    for (i = 0; i < MAX_STORAGE_AREA; ++i) {
        if (storageArea[i].folders) LIBMTP_destroy_folder_t(storageArea[i].folders);
    }
    if (device) LIBMTP_Release_Device (device);
    return_unlock();
}

static int
mtpfs_readdir (const gchar * path, void *buf, fuse_fill_dir_t filler,
               off_t offset, struct fuse_file_info *fi)
{
    LIBMTP_folder_t *folder;

    DBG("mtpfs_readdir(%s, %p, %p, %lli, %p)", path, buf, filler, offset, fi);
    G_LOCK(device_lock);

    // Add common entries
    filler (buf, ".", NULL, 0);
    filler (buf, "..", NULL, 0);

    // If in root directory
    if (strcmp(path,"/") == 0) {
        if (lostfiles != NULL) {
            filler (buf, "lost+found", NULL, 0);
        }
        LIBMTP_devicestorage_t *storage;
        for (storage = device->storage; storage != 0; storage = storage->next) {
            struct stat st;
            memset (&st, 0, sizeof (st));
            st.st_nlink = 2;
            st.st_ino = storage->id;
            st.st_mode = S_IFREG | 0555;
            filler (buf, storage->StorageDescription, &st, 0);
        }
        return_unlock(0);
    }

    // Are we looking at lost+found dir?
    if (strncmp (path, "/lost+found",11) == 0) {
        check_files ();
        GSList *item;

        for (item = lostfiles; item != NULL; item = g_slist_next (item) ) {
            LIBMTP_file_t *file = (LIBMTP_file_t *) item->data;

            struct stat st;
            memset (&st, 0, sizeof (st));
            st.st_ino = file->item_id;
            st.st_mode = S_IFREG | 0444;
            if (filler (buf, (file->filename == NULL ? "<mtpfs null>" : file->filename), &st, 0))
                break;
        }
        return_unlock(0);
    }

    // Get storage area
    int storageid = -1;
    storageid=find_storage(path);
    // Get folder listing.
    uint32_t folder_id = 0;
    if (strcmp (path, "/") != 0) {
        check_folders();
        folder_id = lookup_folder_id (storageArea[storageid].folders, path);
    }

    DBG("Checking folders for %d on %d", folder_id, storageid);
    check_folders();
    if (folder_id == 0) {
        DBG("Root of storage area");
        folder=storageArea[storageid].folders;
    } else {
        folder = LIBMTP_Find_Folder (storageArea[storageid].folders, folder_id);
        if (folder == NULL) return_unlock(0);
        folder = folder->child;
    }

    while (folder != NULL) {
        if (folder->parent_id == folder_id) {
            if (folder_id == 0 && (folder->storage_id != storageArea[storageid].storage->id)) {
                goto next_1;
            }
            DBG("found folder: %s, id %d", folder->name, folder->folder_id);
            struct stat st;
            memset (&st, 0, sizeof (st));
            st.st_ino = folder->folder_id;
            st.st_mode = S_IFDIR | 0777;
            if (filler (buf, folder->name, &st, 0))
                break;
        }
next_1:
        folder = folder->sibling;
    }
    DBG("Checking folders end");
    LIBMTP_destroy_folder_t (folder);
    DBG("Checking files");
    // Find files
    LIBMTP_file_t *file;
    check_files();
    file = files;
    while (file != NULL) {
        if (file->parent_id == folder_id) {
            if (folder_id == 0 && (file->storage_id != storageArea[storageid].storage->id)) {
                goto next_2;
            }
            struct stat st;
            memset (&st, 0, sizeof (st));
            st.st_ino = file->item_id;
            st.st_mode = S_IFREG | 0444;
            if (filler (buf, (file->filename == NULL ? "<mtpfs null>" : file->filename), &st, 0))
                break;
        }
next_2:
        file = file->next;
    }
    DBG("readdir exit");
    return_unlock(0);
}

static int
mtpfs_getattr_real (const gchar * path, struct stat *stbuf)
{
    int ret = 0;

    DBG_F("mtpfs_getattr_real(%s, %p)", path, stbuf);

    if (path == NULL) return_unlock(-ENOENT);
    memset (stbuf, 0, sizeof (struct stat));

    // Set uid/gid of file
    struct fuse_context *fc;
    fc = fuse_get_context();
    stbuf->st_uid = fc->uid;
    stbuf->st_gid = fc->gid;
    if (strcmp (path, "/") == 0) {
        stbuf->st_mode = S_IFDIR | 0777;
        stbuf->st_nlink = 2;
        return_unlock(0);
    }

    // Check cached files first (stuff that hasn't been written to dev yet)
    if (g_hash_table_contains(myfiles, path)) {
        stbuf->st_mode = S_IFREG | 0777;
        stbuf->st_size = 0;
        stbuf->st_blocks = 2;
        stbuf->st_mtime = time(NULL);
        return_unlock(0);
    }

    // Special case directory 'Playlists', 'lost+found'
    // Special case root directory items
    if (g_strrstr(path+1,"/") == NULL) {
        stbuf->st_mode = S_IFDIR | 0777;
        stbuf->st_nlink = 2;
        return_unlock(0);
    }

    int storageid;
    storageid=find_storage(path);

    if (strncasecmp (path, "/lost+found",11) == 0) {
        GSList *item;
        uint32_t item_id = parse_path (path);
        if (item_id == 0xFFFFFFFF) {
            DBG("mtpfs_getattr_real: not found (%s)", path);
            return_unlock(-ENOENT);
        }
        for (item = lostfiles; item != NULL; item = g_slist_next (item)) {
            LIBMTP_file_t *file = (LIBMTP_file_t *) item->data;

            if (item_id == file->item_id) {
                stbuf->st_ino = item_id;
                assert(file->filesize <= INT64_MAX);
                stbuf->st_size = (int64_t) file->filesize;
                stbuf->st_blocks = (file->filesize / 512) +
                    (file->filesize % 512 > 0 ? 1 : 0);
                stbuf->st_nlink = 1;
                stbuf->st_mode = S_IFREG | 0777;
                stbuf->st_mtime = file->modificationdate;
                return_unlock(0);
            }
        }

        return_unlock(-ENOENT);
    }

    uint32_t item_id = 0xFFFFFFF;
    check_folders();
    item_id = lookup_folder_id (storageArea[storageid].folders, path);
    if (item_id != 0xFFFFFFFF) {
        // Must be a folder
        stbuf->st_ino = item_id;
        stbuf->st_mode = S_IFDIR | 0777;
        stbuf->st_nlink = 2;
    } else {
        // Must be a file
        item_id = parse_path (path);
        DBG("id:path=%d:%s", item_id, path);
        if (item_id == 0xFFFFFFFF) {
            DBG("mtpfs_getattr_real: not found (%s)", path);
            return_unlock(-ENOENT);
        }
        check_files();
        LIBMTP_file_t *file;
        file = files;
        gboolean found = FALSE;
        while (file != NULL) {
            if (file->item_id == item_id) {
                stbuf->st_ino = item_id;
                assert(file->filesize <= INT64_MAX);
                stbuf->st_size = (int64_t) file->filesize;
                stbuf->st_blocks = (file->filesize / 512) +
                    (file->filesize % 512 > 0 ? 1 : 0);
                stbuf->st_nlink = 1;
                stbuf->st_mode = S_IFREG | 0777;
                DBG("time:%s",ctime(&(file->modificationdate)));
                stbuf->st_mtime = file->modificationdate;
                stbuf->st_ctime = file->modificationdate;
                stbuf->st_atime = file->modificationdate;
                found = TRUE;
            }
            file = file->next;
        }
        if (!found) {
            ret = -ENOENT;
        }
    }

    return ret;
}

static int
mtpfs_getattr (const gchar * path, struct stat *stbuf)
{
    DBG("mtpfs_getattr(%s, %p)", path, stbuf);
    G_LOCK(device_lock);

    int ret = mtpfs_getattr_real (path, stbuf);

    DBG("getattr exit");
    return_unlock(ret);
}

static int
mtpfs_mknod (const gchar * path, mode_t mode, dev_t dev)
{
    DBG("mtpfs_mknod(%s, %u, %llu)", path, mode, dev);
    G_LOCK(device_lock);

    if (g_hash_table_contains(myfiles, path))
        return_unlock(-EEXIST);
    uint32_t item_id = parse_path (path);
    if (item_id != 0xFFFFFFFF)
        return_unlock(-EEXIST);
    g_hash_table_insert(myfiles, g_strdup(path), NULL);
    DBG("NEW FILE");
    return_unlock(0);
}

static int
mtpfs_open (const gchar * path, struct fuse_file_info *fi)
{
    uint32_t item_id;

    DBG("mtpfs_open(%s, %p)", path, fi);
    G_LOCK(device_lock);

    item_id = parse_path (path);
    if ((item_id == 0xFFFFFFFF) && (!(g_hash_table_contains(myfiles, path)))) {
        return_unlock(-ENOENT);
    }
    if (item_id == 0) {
        DBG("Trying to open root");
        return_unlock(-EPERM);
    }
    if (g_hash_table_lookup(myfiles, path) != NULL) {
        return_unlock(-EBUSY);
    }

    if (fi->flags == O_RDONLY) {
        DBG("read");
    } else if (fi->flags == O_WRONLY) {
        DBG("write");
    } else if (fi->flags == O_RDWR) {
        DBG("rdwrite");
    }

    FILE *filetmp = tmpfile ();
    int tmpfile_fd = fileno (filetmp);
    if (tmpfile_fd != -1) {
        if (item_id == 0xFFFFFFFF) {
            g_hash_table_replace(myfiles, g_strdup(path), (void*)1);
            fi->fh = (unsigned long long) tmpfile_fd;
        } else {
            int ret = LIBMTP_Get_File_To_File_Descriptor (device, item_id, tmpfile_fd, NULL, NULL);
            if (ret == 0) {
                fi->fh = (unsigned long long)tmpfile_fd;
            } else {
                return_unlock(-ENOENT);
            }
        }
    } else {
        return_unlock(-ENOENT);
    }

    return_unlock(0);
}

static int
mtpfs_read (const gchar * path, gchar * buf, size_t size, off_t offset,
            struct fuse_file_info *fi)
{
    int ret;

    DBG("mtpfs_read(%s, %p, %zu, %llu, %p)", path, buf, size, offset, fi);
    G_LOCK(device_lock);

    assert(fi->fh <= INT_MAX);
    if ((int)fi->fh != -1) {
        ret = pread ((int)fi->fh, buf, size, offset);
        if (ret == -1)
            ret = -errno;
    } else {
        ret = -ENOENT;
    }

    return_unlock(ret);
}

static int
mtpfs_write (const gchar * path, const gchar * buf, size_t size, off_t offset,
             struct fuse_file_info *fi)
{
    int ret;

    DBG("mtpfs_write(%s, %p, %zu, %llu, %p)", path, buf, size, offset, fi);
    G_LOCK(device_lock);

    assert(fi->fh <= INT_MAX);
    if (fi->fh != (uint64_t) -1) {
        ret = pwrite ((int)fi->fh, buf, size, offset);
    } else {
        ret = -ENOENT;
    }

    return_unlock(ret);
}


static int
mtpfs_unlink (const gchar * path)
{
    int ret;

    DBG("mtpfs_unlink(%s)", path);
    G_LOCK(device_lock);

    uint32_t item_id = parse_path (path);
    if (item_id == 0 || item_id == 0xFFFFFFFF)
        return_unlock(-ENOENT);
    ret = LIBMTP_Delete_Object (device, item_id);
    if (ret != 0) {
        LIBMTP_Dump_Errorstack (device);
    } else {
        files_changed = TRUE;
    }

    return_unlock(ret);
}

static int
mtpfs_mkdir_real (const char *path, mode_t mode)
{
    DBG_F("mtpfs_mkdir_real(%s, %u)", path, mode);

    if (g_str_has_prefix (path, "/.Trash") == TRUE)
      return_unlock(-EPERM);

    int ret = 0;
    uint32_t item_id = parse_path (path);
    int storageid = find_storage(path);
    if ((item_id == 0xFFFFFFFF) && !g_hash_table_contains(myfiles, path)) {
        // Split path and find parent_id
        gchar *filename = g_strdup("");
        gchar **fields;
        gchar *directory;

        directory = (gchar *) g_malloc (strlen (path));
        directory = strcpy (directory, "/");
        fields = g_strsplit (path, "/", -1);
        int i;
        uint32_t parent_id = 0;
        for (i = 0; fields[i] != NULL; i++) {
            if (strlen (fields[i]) > 0) {
                if (fields[i + 1] == NULL) {
                    gchar *tmp = g_strndup (directory, strlen (directory) - 1);
                    parent_id = lookup_folder_id (storageArea[storageid].folders, tmp);
                    g_free (tmp);
                    if (parent_id == 0xFFFFFFFF) {
                        DBG("parent not found");
                        ret = -ENOENT;
                        goto clean;
                    }
                    g_free (filename);
                    filename = g_strdup (fields[i]);
                } else {
                    directory = strcat (directory, fields[i]);
                    directory = strcat (directory, "/");
                }
            }
        }
        DBG("%s:%s:%d", filename, directory, parent_id);
        item_id = LIBMTP_Create_Folder (device, filename, parent_id, storageArea[storageid].storage->id);
        if (item_id == 0) {
            ret = -EEXIST;
        } else {
            storageArea[storageid].folders_changed=TRUE;
            ret = 0;
        }
clean:
        g_strfreev (fields);
        g_free (directory);
        g_free (filename);
    } else {
        ret = -EEXIST;
    }
    return ret;
}

static int
mtpfs_mkdir (const char *path, mode_t mode)
{
    DBG("mtpfs_mkdir(%s, %u)", path, mode);
    G_LOCK(device_lock);

    int ret = mtpfs_mkdir_real (path, mode);

    return_unlock(ret);
}

static int
mtpfs_rmdir (const char *path)
{
    DBG("mtpfs_rmdir(%s)", path);
    G_LOCK(device_lock);

    int ret = 0;
    uint32_t folder_id = 0xFFFFFFFF;
    if (strcmp (path, "/") == 0) {
        return_unlock(0);
    }
    int storageid=find_storage(path);
    folder_id = lookup_folder_id (storageArea[storageid].folders, path);
    if (folder_id == 0 || folder_id == 0xFFFFFFFF)
        return_unlock(-ENOENT);

    LIBMTP_Delete_Object(device, folder_id);

    storageArea[storageid].folders_changed=TRUE;
    return_unlock(ret);
}

/* Not working. need some way in libmtp to rename objects
int
mtpfs_rename (const char *oldname, const char *newname)
{
    uint32_t old_id = parse_path(oldname);
    LIBMTP_track_t *track;
    track = LIBMTP_Get_Trackmetadata(device,old_id);
    gchar *filename;
    gchar **fields;
    gchar *directory;
    directory = (gchar *) g_malloc (strlen (newname));
    directory = strcpy (directory, "/");
    fields = g_strsplit (newname, "/", -1);
    int i;
    uint32_t parent_id = 0;
    for (i = 0; fields[i] != NULL; i++) {
        if (strlen (fields[i]) > 0) {
            if (fields[i + 1] == NULL) {
                directory = g_strndup (directory, strlen (directory) - 1);
                parent_id = lookup_folder_id (folders, directory);
                if (parent_id < 0)
                    parent_id = 0;
                filename = g_strdup (fields[i]);
            } else {
                directory = strcat (directory, fields[i]);
                directory = strcat (directory, "/");

            }
        }
    }
    DBG("%s:%s:%d", filename, directory, parent_id);

    track->parent_id = parent_id;
    track->title = g_strdup(filename);
    int ret = LIBMTP_Update_Track_Metadata(device, track);
    return ret;
}
*/

/* Allow renaming of empty folders only */
static int
mtpfs_rename (const char *oldname, const char *newname)
{
    DBG("mtpfs_unlink(%s, %s)", oldname, newname);
    G_LOCK(device_lock);

    uint32_t folder_id = 0xFFFFFFFF;
    int folder_empty = 1;
    int ret = -ENOTEMPTY;
    LIBMTP_folder_t *folder;
    LIBMTP_file_t *file;

    int storageid_old=find_storage(oldname);
    int storageid_new=find_storage(newname);
    if (strcmp (oldname, "/") != 0) {
        folder_id = lookup_folder_id (storageArea[storageid_old].folders, oldname);
    }
    if (folder_id == 0 || folder_id == 0xFFFFFFFF)
        return_unlock(-ENOENT);

    check_folders();
    folder = LIBMTP_Find_Folder (storageArea[storageid_old].folders, folder_id);

    /* MTP Folder object not found? */
    if (folder == NULL)
        return_unlock(-ENOENT);

    folder = folder->child;

    /* Check if empty folder */
    DBG("Checking empty folder start for: subfolders");

    while (folder != NULL) {
        if (folder->parent_id == folder_id) {
            folder_empty = 0;
            break;
        }
        folder = folder->sibling;
    }

    DBG("Checking empty folder end for: subfolders. Result: %s", (folder_empty == 1 ? "empty" : "not empty"));

    if (folder_empty == 1) {
        /* Find files */
        check_files();
        DBG("Checking empty folder start for: files");
        file = files;
        while (file != NULL) {
            if (file->parent_id == folder_id) {
                folder_empty = 0;
                break;
            }
            file = file->next;
        }
        DBG("Checking empty folder end for: files. Result: %s", (folder_empty == 1 ? "empty" : "not empty"));


        /* Rename folder. First remove old folder, then create the new one */
        if (folder_empty == 1) {
            struct stat stbuf;
            if ( (ret = mtpfs_getattr_real (oldname, &stbuf)) == 0) {
                DBG("removing folder %s, id %d", oldname, folder_id);

                ret = mtpfs_mkdir_real (newname, stbuf.st_mode);
                LIBMTP_Delete_Object(device, folder_id);
                storageArea[storageid_old].folders_changed=TRUE;
                storageArea[storageid_new].folders_changed=TRUE;
            }
        }
    }
    return_unlock(ret);
}

static int
mtpfs_statvfs (const char *path, struct statvfs *stbuf)
{
    int storage_id = -1;

    DBG("mtpfs_statvfs(%s, %p)", path, stbuf);

    stbuf->f_bsize = 1024;

    storage_id = find_storage(path);
    if (storage_id == -1) {
        stbuf->f_blocks = 0;
        stbuf->f_bfree = 0;
        stbuf->f_ffree = 0;
        for (storage_id = 0; storage_id < MAX_STORAGE_AREA; ++storage_id) {
            if (storageArea[storage_id].storage != NULL) {
                stbuf->f_blocks += storageArea[storage_id].storage->MaxCapacity / 1024;
                stbuf->f_bfree  += storageArea[storage_id].storage->FreeSpaceInBytes /1024;
                stbuf->f_ffree  += storageArea[storage_id].storage->FreeSpaceInObjects;
            }
        }
    } else {
        stbuf->f_blocks = storageArea[storage_id].storage->MaxCapacity / 1024;
        stbuf->f_bfree  = storageArea[storage_id].storage->FreeSpaceInBytes / 1024;
        stbuf->f_ffree  = storageArea[storage_id].storage->FreeSpaceInObjects;
    }
    stbuf->f_bavail = stbuf->f_bfree;
    return 0;
}

static void *
mtpfs_init ()
{
    DBG("mtpfs_init");
    files_changed=TRUE;
    DBG("Ready");
    return 0;
}

static int
mtpfs_blank()
{
    // Do nothing
    return 0;
}

static struct fuse_operations mtpfs_oper = {
    .chmod   = mtpfs_blank,
    .release = mtpfs_release,
    .readdir = mtpfs_readdir,
    .getattr = mtpfs_getattr,
    .open    = mtpfs_open,
    .mknod   = mtpfs_mknod,
    .read    = mtpfs_read,
    .write   = mtpfs_write,
    .unlink  = mtpfs_unlink,
    .destroy = mtpfs_destroy,
    .mkdir   = mtpfs_mkdir,
    .rmdir   = mtpfs_rmdir,
    .rename  = mtpfs_rename,
    .statfs  = mtpfs_statvfs,
    .init    = mtpfs_init,
};

static const struct option long_options[] = {
  {"device",       required_argument, 0,  'z' },
  {NULL,                           0, 0,  0 }
};

int
main (int argc, char *argv[])
{
    LIBMTP_raw_device_t * rawdevices;
    int numrawdevices;
    LIBMTP_error_number_t err;
    int raw_device;
    int opt_seen;
    int opt;
    int i;
    char *friendlyname;

    /* Silently accept unknown opt */
    opterr = 0;
    raw_device = 0;
    opt_seen = 0;
    while ((opt = getopt_long(argc, argv, "z:", long_options, NULL)) != -1 ) {
        switch (opt) {
        case 'z':
            raw_device = atoi(optarg);
            opt_seen += 2;
            break;
        default:
            break;
        }
    }

    argc -= opt_seen;
    argv += opt_seen;

    LIBMTP_Init ();

    fprintf(stdout, "Listing raw device(s)\n");
    err = LIBMTP_Detect_Raw_Devices(&rawdevices, &numrawdevices);
    switch(err) {
    case LIBMTP_ERROR_NO_DEVICE_ATTACHED:
        fprintf(stdout, "   No raw devices found.\n");
        return 0;
    case LIBMTP_ERROR_CONNECTING:
        fprintf(stderr, "Detect: There has been an error connecting. Exiting\n");
        return 1;
    case LIBMTP_ERROR_MEMORY_ALLOCATION:
        fprintf(stderr, "Detect: Encountered a Memory Allocation Error. Exiting\n");
        return 1;
    case LIBMTP_ERROR_NONE:
        {
            fprintf(stdout, "   Found %d device(s):\n", numrawdevices);
            for (i = 0; i < numrawdevices; i++) {
                if (rawdevices[i].device_entry.vendor != NULL ||
                    rawdevices[i].device_entry.product != NULL) {
                    fprintf(stdout, "   %s: %s (%04x:%04x) @ bus %d, dev %d\n",
                      rawdevices[i].device_entry.vendor,
                      rawdevices[i].device_entry.product,
                      rawdevices[i].device_entry.vendor_id,
                      rawdevices[i].device_entry.product_id,
                      rawdevices[i].bus_location,
                      rawdevices[i].devnum);
                } else {
                    fprintf(stdout, "   %04x:%04x @ bus %d, dev %d\n",
                      rawdevices[i].device_entry.vendor_id,
                      rawdevices[i].device_entry.product_id,
                      rawdevices[i].bus_location,
                      rawdevices[i].devnum);
                }
            }
        }
        break;
    case LIBMTP_ERROR_GENERAL:
    default:
        fprintf(stderr, "Unknown connection error.\n");
        return 1;
    }

    fprintf(stdout, "Attempting to connect device %d\n", raw_device);
    if (raw_device >= numrawdevices) {
        fprintf(stderr, "Device %d does not exist\n", raw_device);
        return 1;
    }
    device = LIBMTP_Open_Raw_Device(&rawdevices[raw_device]);
    if (device == NULL) {
        fprintf(stderr, "Unable to open raw device %d\n", raw_device);
        return 1;
    }

    /* Echo the friendly name so we know which device we are working with */
    friendlyname = LIBMTP_Get_Friendlyname(device);
    if (friendlyname == NULL) {
        printf("Listing File Information on Device with name: (NULL)\n");
    } else {
        printf("Listing File Information on Device with name: %s\n", friendlyname);
        g_free(friendlyname);
    }

    /* Get all storages for this device */
    int ret = LIBMTP_Get_Storage(device, LIBMTP_STORAGE_SORTBY_NOTSORTED);
    if (ret != 0) {
        if (ret == 1) {
            fprintf(stdout, "LIBMTP_Get_Storage() failed: unable to get storage properties\n");
        } else {
            fprintf(stdout,"LIBMTP_Get_Storage() failed:%d\n", ret);
        }
        dump_mtp_error(device);
        return 1;
    }

    /* Check if multiple storage areas */
    LIBMTP_devicestorage_t *storage;
    i = 0;
    for (storage = device->storage; storage != 0 && i < MAX_STORAGE_AREA; storage = storage->next)  {
        storageArea[i].storage = storage;
        storageArea[i].folders = NULL;
        storageArea[i].folders_changed = TRUE;
        DBG("Storage%d: %d - %s\n",i, storage->id, storage->StorageDescription);
        i++;
    }

    myfiles = g_hash_table_new_full(g_str_hash, g_str_equal, g_free, NULL);

    DBG("Start fuse");
    return fuse_main(argc, argv, &mtpfs_oper, NULL); //TODO: use privdata instead of static vars
}
