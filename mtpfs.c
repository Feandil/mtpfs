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
static GSList *myfiles = NULL;

G_LOCK_DEFINE_STATIC(device_lock);
#define enter_lock(a...)       do { G_LOCK(device_lock); } while(0)
#define return_unlock(a)       do { G_UNLOCK(device_lock); return a; } while(0)


/* Freeing tree representation */
static void
free_files(LIBMTP_file_t *filelist)
{
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
    int last_parent_id = -1;
    gboolean last_parent_found = FALSE;
    LIBMTP_file_t *item;

    if (lostfiles != NULL)
        g_slist_free (lostfiles);

    lostfiles = NULL;
    for (item = files; item != NULL; item = item->next) {
        gboolean parent_found;

        if (last_parent_id == -1 || last_parent_id != item->parent_id) {
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

void
check_folders ()
{
    int i;
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
    //DBG("find_storage:%s", path);

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
        storage_len = second_slash - path;
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

static int
lookup_folder_id (LIBMTP_folder_t * folder, const gchar * path)
{
    gchar ** fields;
    gsize pos;
    int ret;
    //DBG("lookup_folder_id %s", path);

    if (folder == NULL) {
        DBG("lookup_folder_id: Empty list");
        return -1;
    }
    if (path[0] != '/') {
        DBG("lookup_folder_id: Internal error: unexpected root")
        return -1;
    }

    check_folders();

    fields = g_strsplit(path + 1, "/", -1);

    if (fields[1] == NULL) {
        DBG("lookup_folder_id: Storage dir");
        return -2;
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

    g_strfreev(fields);

    if (fields[pos] == NULL) {
        DBG("lookup_folder_id %s: found %i", path, ret);
        return ret;
    }
    DBG("lookup_folder_id %s: not found", path);
    return -1;
}

static int
parse_path (const gchar * path)
{
    DBG("parse_path:%s",path);
    int res;
    int item_id = -1;
    int i;
    // Check cached files first
    if (g_slist_find_custom (myfiles, path, (GCompareFunc) strcmp) != NULL)
        return 0;

    // Check lost+found
    if (strncmp("/lost+found", path, 11) == 0) {
        GSList *item;
        gchar *filename  = g_path_get_basename (path);

        res = -ENOENT;
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
    directory = (gchar *) g_malloc (strlen (path));
    directory = strcpy (directory, "");
    fields = g_strsplit (path, "/", -1);
    res = -ENOENT;
    int storageid;
    storageid = find_storage(path);
    for (i = 0; fields[i] != NULL; i++) {
        if (strlen (fields[i]) > 0) {
            if (fields[i + 1] != NULL) {
                directory = strcat (directory, "/");
                directory = strcat (directory, fields[i]);
            } else {
                check_folders();
                folder = storageArea[storageid].folders;
                int folder_id = 0;
                if (strcmp (directory, "") != 0) {
                    folder_id = lookup_folder_id (folder, directory);
                }
                DBG("parent id:%d:%s", folder_id, directory);
                LIBMTP_file_t *file;
                check_files();
                file = files;
                while (file != NULL) {
                    if ((file->parent_id == folder_id) ||
                       (folder_id==-2 && (file->parent_id == 0) && (file->storage_id == storageArea[storageid].storage->id))) {
                        if (file->filename == NULL) DBG("MTPFS filename NULL");
                        if (file->filename != NULL && g_ascii_strcasecmp (file->filename, fields[i]) == 0) {
                            DBG("found:%d:%s", file->item_id, file->filename);

                            item_id = file->item_id;
                            break; // found!
                        }
                    }
                    file = file->next;
                }
                if (item_id < 0) {
                    directory = strcat (directory, "/");
                    directory = strcat (directory, fields[i]);
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
    g_free (directory);
    g_strfreev (fields);
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
    enter_lock("release: %s", path);
    // Check cached files first
    GSList *item;
    int ret = 0;

    item = g_slist_find_custom (myfiles, path, (GCompareFunc) strcmp);
    if (item != NULL) {
        //find parent id
        gchar *filename = g_strdup("");
        gchar **fields;
        gchar *directory;
        directory = (gchar *) g_malloc (strlen (path));
        directory = strcpy (directory, "/");
        fields = g_strsplit (path, "/", -1);
        int i;
        int parent_id = 0;
        int storageid;
        storageid = find_storage(path);
        for (i = 0; fields[i] != NULL; i++) {
            if (strlen (fields[i]) > 0) {
                if (fields[i + 1] == NULL) {
                    gchar *tmp = g_strndup (directory, strlen (directory) - 1);
                    parent_id = lookup_folder_id (storageArea[storageid].folders, tmp);
                    g_free (tmp);
                    if (parent_id < 0)
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
        fstat (fi->fh, &st);
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

        ret =
            LIBMTP_Send_File_From_File_Descriptor (device, fi->fh,
                genfile, NULL, NULL);
        LIBMTP_destroy_file_t (genfile);
        DBG("Sent FILE %s",path);
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
        if (item->data) {
            g_free (item->data);
        }
        myfiles = g_slist_remove (myfiles, item->data);
    }
    close (fi->fh);
    G_UNLOCK(device_lock);
    return ret;
}

void
mtpfs_destroy ()
{
    enter_lock("destroy");
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
    enter_lock("readdir %s", path);
    LIBMTP_folder_t *folder;

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
    int folder_id = 0;
    if (strcmp (path, "/") != 0) {
        check_folders();
        folder_id = lookup_folder_id (storageArea[storageid].folders, path);
    }

    DBG("Checking folders for %d",storageid);
    check_folders();
    if (folder_id==-2) {
        DBG("Root of storage area");
        folder=storageArea[storageid].folders;
    } else {
        folder = LIBMTP_Find_Folder (storageArea[storageid].folders, folder_id);
        if (folder == NULL) return_unlock(0);
        folder = folder->child;
    }

    while (folder != NULL) {
        if ((folder->parent_id == folder_id) ||
           (folder_id==-2 && (folder->storage_id == storageArea[storageid].storage->id))) {
            DBG("found folder: %s, id %d", folder->name, folder->folder_id);
            struct stat st;
            memset (&st, 0, sizeof (st));
            st.st_ino = folder->folder_id;
            st.st_mode = S_IFDIR | 0777;
            if (filler (buf, folder->name, &st, 0))
                break;
        }
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
        if ((file->parent_id == folder_id) ||
           (folder_id==-2 && (file->parent_id == 0) && (file->storage_id == storageArea[storageid].storage->id))) {
            struct stat st;
            memset (&st, 0, sizeof (st));
            st.st_ino = file->item_id;
            st.st_mode = S_IFREG | 0444;
            if (filler (buf, (file->filename == NULL ? "<mtpfs null>" : file->filename), &st, 0))
                break;
        }
        file = file->next;
    }
    DBG("readdir exit");
    return_unlock(0);
}

static int
mtpfs_getattr_real (const gchar * path, struct stat *stbuf)
{
    int ret = 0;
    if (path==NULL) return_unlock(-ENOENT);
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
    if (myfiles != NULL) {
        if (g_slist_find_custom (myfiles, path, (GCompareFunc) strcmp) != NULL) {
            stbuf->st_mode = S_IFREG | 0777;
            stbuf->st_size = 0;
            stbuf->st_blocks = 2;
            stbuf->st_mtime = time(NULL);
            return_unlock(0);
        }
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
        int item_id = parse_path (path);
        for (item = lostfiles; item != NULL; item = g_slist_next (item)) {
            LIBMTP_file_t *file = (LIBMTP_file_t *) item->data;

            if (item_id == file->item_id) {
                stbuf->st_ino = item_id;
                stbuf->st_size = file->filesize;
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

    int item_id = -1;
    check_folders();
    item_id = lookup_folder_id (storageArea[storageid].folders, path);
    if (item_id >= 0) {
        // Must be a folder
        stbuf->st_ino = item_id;
        stbuf->st_mode = S_IFDIR | 0777;
        stbuf->st_nlink = 2;
    } else {
        // Must be a file
        item_id = parse_path (path);
        LIBMTP_file_t *file;
        DBG("id:path=%d:%s", item_id, path);
        check_files();
        file = files;
        gboolean found = FALSE;
        while (file != NULL) {
            if (file->item_id == item_id) {
                stbuf->st_ino = item_id;
                stbuf->st_size = file->filesize;
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
    enter_lock("getattr %s", path);

    int ret = mtpfs_getattr_real (path, stbuf);

    DBG("getattr exit");
    return_unlock(ret);
}

static int
mtpfs_mknod (const gchar * path, mode_t mode, dev_t dev)
{
    enter_lock("mknod %s", path);
    int item_id = parse_path (path);
    if (item_id > 0)
        return_unlock(-EEXIST);
    myfiles = g_slist_append (myfiles, (gpointer) (g_strdup (path)));
    DBG("NEW FILE");
    return_unlock(0);
}

static int
mtpfs_open (const gchar * path, struct fuse_file_info *fi)
{
    enter_lock("open");
    int item_id = -1;
    item_id = parse_path (path);
    if (item_id < 0)
        return_unlock(-ENOENT);

    if (fi->flags == O_RDONLY) {
        DBG("read");
    } else if (fi->flags == O_WRONLY) {
        DBG("write");
    } else if (fi->flags == O_RDWR) {
        DBG("rdwrite");
    }

    int storageid;
    storageid=find_storage(path);
    FILE *filetmp = tmpfile ();
    int tmpfile = fileno (filetmp);
    if (tmpfile != -1) {
        if (item_id == 0) {
            fi->fh = tmpfile;
        } else {
            int ret =
                LIBMTP_Get_File_To_File_Descriptor (device, item_id, tmpfile,
                                                    NULL, NULL);
            if (ret == 0) {
                fi->fh = tmpfile;
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
    enter_lock("read");
    int ret;

    int item_id = -1;
    item_id = parse_path (path);
    if (item_id < 0)
        return_unlock(-ENOENT);

    ret = pread (fi->fh, buf, size, offset);
    if (ret == -1)
        ret = -errno;

    return_unlock(ret);
}

static int
mtpfs_write (const gchar * path, const gchar * buf, size_t size, off_t offset,
             struct fuse_file_info *fi)
{
    enter_lock("write");
    int ret;
    if (fi->fh != -1) {
        ret = pwrite (fi->fh, buf, size, offset);
    } else {
        ret = -ENOENT;
    }

    return_unlock(ret);
}


static int
mtpfs_unlink (const gchar * path)
{
    enter_lock("unlink");
    int ret = 0;
    int item_id = -1;
    item_id = parse_path (path);
    if (item_id < 0)
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
    if (g_str_has_prefix (path, "/.Trash") == TRUE)
      return_unlock(-EPERM);

    int ret = 0;
    GSList *item;
    item = g_slist_find_custom (myfiles, path, (GCompareFunc) strcmp);
    int item_id = parse_path (path);
    int storageid = find_storage(path);
    if ((item == NULL) && (item_id < 0)) {
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
                    check_folders();
                    parent_id = lookup_folder_id (storageArea[storageid].folders, tmp);
                    g_free (tmp);
                    if (parent_id < 0)
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
        ret = LIBMTP_Create_Folder (device, filename, parent_id, storageArea[storageid].storage->id);
        g_strfreev (fields);
        g_free (directory);
        g_free (filename);
        if (ret == 0) {
            ret = -EEXIST;
        } else {
            storageArea[storageid].folders_changed=TRUE;
            ret = 0;
        }
    } else {
        ret = -EEXIST;
    }
    return ret;
}


static int
mtpfs_mkdir (const char *path, mode_t mode)
{
    enter_lock("mkdir: %s", path);
    int ret = mtpfs_mkdir_real (path, mode);

    return_unlock(ret);
}

static int
mtpfs_rmdir (const char *path)
{
    enter_lock("rmdir %s", path);
    int ret = 0;
    int folder_id = -1;
    if (strcmp (path, "/") == 0) {
        return_unlock(0);
    }
    int storageid=find_storage(path);
    folder_id = lookup_folder_id (storageArea[storageid].folders, path);
    if (folder_id < 0)
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
     enter_lock("rename '%s' to '%s'", oldname, newname);

    int folder_id = -1;
    int folder_empty = 1;
    int ret = -ENOTEMPTY;
    LIBMTP_folder_t *folder;
    LIBMTP_file_t *file;

    int storageid_old=find_storage(oldname);
    int storageid_new=find_storage(newname);
    if (strcmp (oldname, "/") != 0) {
        folder_id = lookup_folder_id (storageArea[storageid_old].folders, oldname);
    }
    if (folder_id < 0)
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

    DBG("mtpfs_statvfs(%s)", path);


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
    .statfs  = mtpfs_statfs,
    .init    = mtpfs_init,
};

int
main (int argc, char *argv[])
{
    umask (0);
    LIBMTP_raw_device_t * rawdevices;
    int numrawdevices;
    LIBMTP_error_number_t err;
    int i;

    int opt;
    extern int optind;
    extern char *optarg;

    //while ((opt = getopt(argc, argv, "d")) != -1 ) {
        //switch (opt) {
        //case 'd':
            ////LIBMTP_Set_Debug(9);
            //break;
        //}
    //}

    //argc -= optind;
    //argv += optind;

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
            int i;

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

    fprintf(stdout, "Attempting to connect device\n");
    device = LIBMTP_Open_Raw_Device(&rawdevices[i]);
    if (device == NULL) {
        fprintf(stderr, "Unable to open raw device %d\n", i);
        return 1;
    }

    LIBMTP_Dump_Errorstack(device);
    LIBMTP_Clear_Errorstack(device);

    char *friendlyname;
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

    DBG("Start fuse");
    return fuse_main(argc, argv, &mtpfs_oper, NULL); //TODO: use privdata instead of static vars
}
