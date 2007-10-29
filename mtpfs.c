/*
    FUSE: Filesystem in Userspace
    Copyright (C) 2001-2005  Miklos Szeredi <miklos@szeredi.hu>

    This program can be distributed under the terms of the GNU GPL.
    See the file COPYING.
*/

#include <mtpfs.h>


void
free_files(LIBMTP_file_t *filelist)
{
    LIBMTP_file_t *file = filelist, *tmp;
    while (file) {
        tmp = file;
        file = file->next;
        LIBMTP_destroy_file_t(tmp);
    }
}

void
free_playlists(LIBMTP_playlist_t *pl)
{
    LIBMTP_playlist_t *playlist = pl, *tmp;
    while (playlist) {
        tmp = playlist;
        playlist = playlist->next;
        LIBMTP_destroy_playlist_t(tmp);
    }
}

void
check_files ()
{
    if (files_changed) {
        if (DEBUG) g_debug("Refreshing Filelist");
        LIBMTP_file_t *newfiles = NULL;
        g_mutex_lock(device_lock);
        if (files) free_files(files);
        newfiles = LIBMTP_Get_Filelisting_With_Callback(device, NULL, NULL);
        files = newfiles;
        newfiles = NULL;
        files_changed = FALSE;
        g_mutex_unlock(device_lock);
    }
}

void
check_folders ()
{
    if (folders_changed) {
        if (DEBUG) g_debug("Refreshing Folderlist");
        LIBMTP_folder_t *newfolders = NULL;
        g_mutex_lock(device_lock);
        if (folders) {
            LIBMTP_destroy_folder_t(folders);
        }
        newfolders = LIBMTP_Get_Folder_List(device);
        folders = newfolders;
        newfolders = NULL;
        folders_changed= FALSE;
        g_mutex_unlock(device_lock);
    }
}

void
check_playlists ()
{
    if (playlists_changed) {
        if (DEBUG) g_debug("Refreshing Playlists");
        LIBMTP_playlist_t *newplaylists;
        g_mutex_lock(device_lock);
        if (playlists) free_playlists(playlists);
        newplaylists = LIBMTP_Get_Playlist_List(device);
        playlists = newplaylists;
        playlists_changed = FALSE;
        g_mutex_unlock(device_lock);
    }
}

int
save_playlist (const char *path, struct fuse_file_info *fi)
{
    if (DEBUG) g_debug("save_playlist");
    int ret=0;

    LIBMTP_playlist_t *playlist;
    FILE *file = NULL;
    char item_path[1024];
    uint32_t item_id=0;
    uint32_t *tracks;
    gchar **fields;
    GSList *tmplist=NULL;

    fields = g_strsplit(path,"/",-1);
    gchar *playlist_name;
    playlist_name = g_strndup(fields[2],strlen(fields[2])-4);
    if (DEBUG) g_debug("Adding:%s",playlist_name);
    g_strfreev(fields);

    playlist=LIBMTP_new_playlist_t();
    playlist->name=g_strdup(playlist_name);

    file = fdopen(fi->fh,"r");
    while (fgets(item_path,sizeof(item_path)-1,file) != NULL){
        g_strchomp(item_path);
        item_id = parse_path(item_path);
        if (item_id != -1) {
            tmplist = g_slist_append(tmplist,GUINT_TO_POINTER(item_id));
            g_debug("Adding to tmplist:%d",item_id);
        }
    }
    playlist->no_tracks = g_slist_length(tmplist);
    tracks = g_malloc(playlist->no_tracks * sizeof(uint32_t));
    int i;
    for (i = 0; i < playlist->no_tracks; i++) {
            tracks[i]=(uint32_t)GPOINTER_TO_UINT(g_slist_nth_data(tmplist,i));
            g_debug("Adding:%d-%d",i,tracks[i]);
    }
    playlist->tracks = tracks;
    g_debug("Total:%d",playlist->no_tracks);
    
    int playlist_id = 0;
    LIBMTP_playlist_t *tmp_playlist;
    check_playlists();
    tmp_playlist=playlists;
    while (tmp_playlist != NULL){
        if (strcasecmp(tmp_playlist->name,playlist_name) == 0){
            playlist_id=playlist->playlist_id;
        }
        tmp_playlist=tmp_playlist->next;
    }

    if (playlist_id > 0) {
        if(DEBUG) g_debug("Update playlist %d",playlist_id);
        playlist->playlist_id=playlist_id;
        ret = LIBMTP_Update_Playlist(device,playlist);
    } else {
        if(DEBUG) g_debug("New playlist");
        ret = LIBMTP_Create_New_Playlist(device,playlist,0);
    }
    playlists_changed=TRUE;
    return ret;
}

/* Find the file type based on extension */
static LIBMTP_filetype_t
find_filetype (const gchar * filename)
{
    if (DEBUG) g_debug ("find_filetype");
    gchar **fields;
    fields = g_strsplit (filename, ".", -1);
    gchar *ptype;
    ptype = g_strdup (fields[g_strv_length (fields) - 1]);
    g_strfreev (fields);
    LIBMTP_filetype_t filetype;
    // This need to be kept constantly updated as new file types arrive.
    if (!strcasecmp (ptype, "wav")) {
        filetype = LIBMTP_FILETYPE_WAV;
    } else if (!strcasecmp (ptype, "mp3")) {
        filetype = LIBMTP_FILETYPE_MP3;
    } else if (!strcasecmp (ptype, "wma")) {
        filetype = LIBMTP_FILETYPE_WMA;
    } else if (!strcasecmp (ptype, "ogg")) {
        filetype = LIBMTP_FILETYPE_OGG;
    } else if (!strcasecmp (ptype, "mp4")) {
        filetype = LIBMTP_FILETYPE_MP4;
    } else if (!strcasecmp (ptype, "wmv")) {
        filetype = LIBMTP_FILETYPE_WMV;
    } else if (!strcasecmp (ptype, "avi")) {
        filetype = LIBMTP_FILETYPE_AVI;
    } else if (!strcasecmp (ptype, "mpeg") || !strcasecmp (ptype, "mpg")) {
        filetype = LIBMTP_FILETYPE_MPEG;
    } else if (!strcasecmp (ptype, "asf")) {
        filetype = LIBMTP_FILETYPE_ASF;
    } else if (!strcasecmp (ptype, "qt") || !strcasecmp (ptype, "mov")) {
        filetype = LIBMTP_FILETYPE_QT;
    } else if (!strcasecmp (ptype, "wma")) {
        filetype = LIBMTP_FILETYPE_WMA;
    } else if (!strcasecmp (ptype, "jpg") || !strcasecmp (ptype, "jpeg")) {
        filetype = LIBMTP_FILETYPE_JPEG;
    } else if (!strcasecmp (ptype, "jfif")) {
        filetype = LIBMTP_FILETYPE_JFIF;
    } else if (!strcasecmp (ptype, "tif") || !strcasecmp (ptype, "tiff")) {
        filetype = LIBMTP_FILETYPE_TIFF;
    } else if (!strcasecmp (ptype, "bmp")) {
        filetype = LIBMTP_FILETYPE_BMP;
    } else if (!strcasecmp (ptype, "gif")) {
        filetype = LIBMTP_FILETYPE_GIF;
    } else if (!strcasecmp (ptype, "pic") || !strcasecmp (ptype, "pict")) {
        filetype = LIBMTP_FILETYPE_PICT;
    } else if (!strcasecmp (ptype, "png")) {
        filetype = LIBMTP_FILETYPE_PNG;
    } else if (!strcasecmp (ptype, "wmf")) {
        filetype = LIBMTP_FILETYPE_WINDOWSIMAGEFORMAT;
    } else if (!strcasecmp (ptype, "ics")) {
        filetype = LIBMTP_FILETYPE_VCALENDAR2;
    } else if (!strcasecmp (ptype, "exe") || !strcasecmp (ptype, "com") ||
               !strcasecmp (ptype, "bat") || !strcasecmp (ptype, "dll") ||
               !strcasecmp (ptype, "sys")) {
        filetype = LIBMTP_FILETYPE_WINEXEC;
    } else {
        printf ("Sorry, file type \"%s\" is not yet supported\n", ptype);
        printf ("Tagging as unknown file type.\n");
        filetype = LIBMTP_FILETYPE_UNKNOWN;
    }
    return filetype;
}

static int
lookup_folder_id (LIBMTP_folder_t * folderlist, gchar * path, gchar * parent)
{
    //if (DEBUG) g_debug("lookup_folder_id");
    int ret = -1;
    if (folderlist == NULL) {
        return -1;
    }
    check_folders();
    gchar *current;
    current = g_strconcat(parent, "/", folderlist->name,NULL);
    if (strcasecmp (path, current) == 0) {
        return folderlist->folder_id;
    }
    if (strncasecmp (path, current, strlen (current)) == 0) {
        ret = lookup_folder_id (folderlist->child, path, current);
    }
    g_free(current);
    if (ret >= 0) {
        return ret;
    }
    ret = lookup_folder_id (folderlist->sibling, path, parent);
    return ret;
}

static int
parse_path (const gchar * path)
{
    if (DEBUG) g_debug ("parse_path:%s",path);
    int item_id = -1;
    int i;
    // Check cached files first
    GSList *item;
    item = g_slist_find_custom (myfiles, path, (GCompareFunc) strcmp);
    if (item != NULL)
        return 0;

    // Check Playlists
    if (strncmp("/Playlists",path,10) == 0) {
        LIBMTP_playlist_t *playlist;
        check_playlists();
        playlist=playlists;
        while (playlist != NULL) {
            gchar *tmppath;
            tmppath = g_strconcat("/Playlists/",playlist->name,".m3u",NULL);
            if (g_strcasecmp(path,tmppath) == 0)
                return playlist->playlist_id;
            playlist = playlist->next;
        }
        return -ENOENT;

    }
    // Check device
    LIBMTP_folder_t *folder;
    gchar **fields;
    gchar *directory;
    directory = (gchar *) g_malloc (strlen (path));
    directory = strcpy (directory, "");
    fields = g_strsplit (path, "/", -1);
    for (i = 0; fields[i] != NULL; i++) {
        if (strlen (fields[i]) > 0) {
            if (fields[i + 1] != NULL) {
                directory = strcat (directory, "/");
                directory = strcat (directory, fields[i]);
            } else {
                check_folders();
                folder = folders;
                int folder_id = 0;
                if (strcmp (directory, "") != 0) {
                    folder_id = lookup_folder_id (folder, directory, "");
                }
                if (DEBUG) g_debug ("parent id:%d:%s", folder_id, directory);
                LIBMTP_file_t *file;
                check_files();
                file = files;
                while (file != NULL) {
                    if (file->parent_id == folder_id) {
                        if (strcasecmp (file->filename, fields[i]) == 0) {
                            if (DEBUG) g_debug ("found:%d:%s", file->item_id,
                                     file->filename);
                            item_id = file->item_id;
                            return item_id;
                        }
                    }
                    file = file->next;
                }
                if (item_id < 0) {
                    directory = strcat (directory, fields[i]);
                    item_id = lookup_folder_id (folder, directory, "");
                    return item_id;
                }
            }
        }
    }
    return -ENOENT;
}

static int
mtpfs_release (const char *path, struct fuse_file_info *fi)
{
    if (DEBUG) g_debug ("release");
    // Check cached files first
    GSList *item;
    item = g_slist_find_custom (myfiles, path, (GCompareFunc) strcmp);

    if (item != NULL) {
        if (strncmp("/Playlists/",path,11) == 0) {
            g_mutex_lock(device_lock);
            save_playlist(path,fi);
            close (fi->fh);
            g_mutex_unlock(device_lock);
            return 0;
        } else {
            //find parent id
            gchar *filename = "";
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
                        directory = g_strndup (directory, strlen (directory) - 1);
                        parent_id = lookup_folder_id (folders, directory, "");
                        if (parent_id < 0)
                            parent_id = 0;
                        filename = g_strdup (fields[i]);
                    } else {
                        directory = strcat (directory, fields[i]);
                        directory = strcat (directory, "/");
                    }
                }
            }
            if (DEBUG) g_debug ("%s:%s:%d", filename, directory, parent_id);
    
            struct stat st;
            uint64_t filesize;
            fstat (fi->fh, &st);
            filesize = (uint64_t) st.st_size;
    
            // Setup file
            LIBMTP_filetype_t filetype;
            filetype = find_filetype (filename);
            int ret;
            if (filetype == LIBMTP_FILETYPE_MP3) {
                LIBMTP_track_t *genfile;
                genfile = LIBMTP_new_track_t ();
                gint songlen;
                struct id3_file *id3_fh;
                struct id3_tag *tag;
                gchar *tracknum;


                id3_fh = id3_file_fdopen (fi->fh, ID3_FILE_MODE_READONLY);
                tag = id3_file_tag (id3_fh);

                genfile->artist = getArtist (tag);
                genfile->title = getTitle (tag);
                genfile->album = getAlbum (tag);
                genfile->genre = getGenre (tag);
                genfile->date = getYear (tag);
                genfile->usecount = 0;

                /* If there is a songlength tag it will take
                 * precedence over any length calculated from
                 * the bitrate and filesize */
                songlen = getSonglen (tag);
                if (songlen > 0) {
                    genfile->duration = songlen * 1000;
                } else {
                    genfile->duration = (uint16_t)calc_length(fi->fh) * 1000;
                    //genfile->duration = 293000;
                }

                tracknum = getTracknum (tag);
                if (tracknum != NULL) {
                    genfile->tracknumber = strtoul(tracknum,NULL,10);
                } else {
                    genfile->tracknumber = 0;
                }
                g_free (tracknum);

                // Compensate for missing tag information
                if (!genfile->artist)
                    genfile->artist = g_strdup("<Unknown>");
                if (!genfile->title)
                    genfile->title = g_strdup("<Unknown>");
                if (!genfile->album)
                    genfile->album = g_strdup("<Unknown>");
                if (!genfile->genre)
                    genfile->genre = g_strdup("<Unknown>");

                genfile->filesize = filesize;
                genfile->filetype = filetype;
                genfile->filename = g_strdup (filename);
                //title,artist,genre,album,date,tracknumber,duration,samplerate,nochannels,wavecodec,bitrate,bitratetype,rating,usecount
                //g_debug("%d:%d:%d",fi->fh,genfile->duration,genfile->filesize);
                g_mutex_lock(device_lock);
                ret =
                    LIBMTP_Send_Track_From_File_Descriptor (device, fi->fh,
                                                            genfile, NULL, NULL,
                                                            parent_id);
                g_mutex_unlock(device_lock);
                id3_file_close (id3_fh);
                LIBMTP_destroy_track_t (genfile);
            } else {
                LIBMTP_file_t *genfile;
                genfile = LIBMTP_new_file_t ();
                genfile->filesize = filesize;
                genfile->filetype = filetype;
                genfile->filename = g_strdup (filename);
                genfile->parent_id = parent_id;
    
                g_mutex_lock(device_lock);
                ret =
                    LIBMTP_Send_File_From_File_Descriptor (device, fi->fh,
                                                        genfile, NULL, NULL,
                                                        parent_id);
                g_mutex_unlock(device_lock);
                LIBMTP_destroy_file_t (genfile);
            }
            if (ret == 0)
                if (DEBUG) g_debug ("Sent %s",path);
            // Cleanup
            myfiles = g_slist_remove (myfiles, item->data);
            g_strfreev (fields);
            close (fi->fh);
            // Refresh filelist
            files_changed = TRUE;
            //files = LIBMTP_Get_Filelisting(device);
            return ret;
        }
    }
    close (fi->fh);
    return 0;
}

void
mtpfs_destroy ()
{
    if (DEBUG) g_debug ("destroy");
    if (files) free_files(files);
    if (folders) LIBMTP_destroy_folder_t(folders);
    if (playlists) free_playlists(playlists);
    LIBMTP_Release_Device (device);
}

static int
mtpfs_readdir (const gchar * path, void *buf, fuse_fill_dir_t filler,
               off_t offset, struct fuse_file_info *fi)
{
    if (DEBUG) g_debug ("readdir");
    LIBMTP_folder_t *folder;

    // Add common entries
    filler (buf, ".", NULL, 0);
    filler (buf, "..", NULL, 0);

    // Are we looking at the playlists?
    if (strncmp (path, "/Playlists",10) == 0) {
        if (DEBUG) g_debug("Checking Playlists");
        LIBMTP_playlist_t *playlist;
        check_playlists();
        playlist=playlists;
        while (playlist!= NULL) {
            struct stat st;
            memset (&st, 0, sizeof (st));
            st.st_ino = playlist->playlist_id;
            st.st_mode = S_IFREG | 0666;
            gchar *name;
            name = g_strconcat(playlist->name,".m3u",NULL);
            if (DEBUG) g_debug("Playlist:%s",name);
            if (filler (buf, name, &st, 0))
                break;
            playlist=playlist->next;
        }
        return 0;
    }
    // Get folder listing.
    int folder_id = 0;
    if (strcmp (path, "/") != 0) {
        check_folders();
        folder = folders;
        folder_id = lookup_folder_id (folder, (gchar *) path, "");
    }

    if (folder_id == 0) {
        filler (buf, "Playlists", NULL, 0);
        check_folders();
        folder = folders;
    } else {
        g_mutex_lock(device_lock);
        check_folders();
        folder = LIBMTP_Find_Folder (folders, folder_id);
        g_mutex_unlock(device_lock);
        folder = folder->child;
    }

    while (folder != NULL) {
        if (folder->parent_id == folder_id) {
            struct stat st;
            memset (&st, 0, sizeof (st));
            st.st_ino = folder->folder_id;
            st.st_mode = S_IFDIR | 0777;
            if (filler (buf, folder->name, &st, 0))
                break;
        }
        folder = folder->sibling;
    }
    LIBMTP_destroy_folder_t (folder);

    // Find files
    LIBMTP_file_t *file, *tmp;
    check_files();
    file = files;
    while (file != NULL) {
        if (file->parent_id == folder_id) {
            struct stat st;
            memset (&st, 0, sizeof (st));
            st.st_ino = file->item_id;
            st.st_mode = S_IFREG | 0444;
            if (filler (buf, file->filename, &st, 0))
                break;
        }
        tmp = file;
        file = file->next;
    }

    return 0;
}

static int
mtpfs_getattr (const gchar * path, struct stat *stbuf)
{
    if (DEBUG) g_debug ("getattr");

    int ret = 0;
    memset (stbuf, 0, sizeof (struct stat));

    // Set uid/gid of file
    struct fuse_context *fc;
    fc = fuse_get_context();
    stbuf->st_uid = fc->uid;
    stbuf->st_gid = fc->gid;

    // Check cached files first
    GSList *item;
    if (myfiles != NULL) {
        item = g_slist_find_custom (myfiles, path, (GCompareFunc) strcmp);
        if (item != NULL) {
            stbuf->st_mode = S_IFREG | 0777;
            stbuf->st_size = 0;
            stbuf->st_blocks = 2;
            return 0;
        }
    }

    // Special case directory 'Playlists'
    if (strcasecmp (path, "/Playlists") == 0) {
        stbuf->st_mode = S_IFDIR | 0777;
        stbuf->st_nlink = 2;
        return 0;
    }
    if (strncasecmp (path, "/Playlists",10) == 0) {
        LIBMTP_playlist_t *playlist;
        check_playlists();
        playlist=playlists;
        while (playlist != NULL) {
            gchar *tmppath;
            tmppath = g_strconcat("/Playlists/",playlist->name,".m3u",NULL);
            if (g_strcasecmp(path,tmppath) == 0) {
                int filesize = 0;
                int i;
                for (i=0; i <playlist->no_tracks; i++){
                    LIBMTP_file_t *file;
                    LIBMTP_folder_t *folder;
                    file = LIBMTP_Get_Filemetadata(device,playlist->tracks[i]);
                    if (file != NULL) {
                        int parent_id = file->parent_id;
                        filesize = filesize + strlen(file->filename) + 2;
                        while (parent_id != 0) {
                            check_folders();
                            folder = LIBMTP_Find_Folder(folders,parent_id);
                            parent_id = folder->parent_id;
                            filesize = filesize + strlen(folder->name) + 1;
                        }
                    }
                }
                stbuf->st_mode = S_IFREG | 0777;
                stbuf->st_size = filesize;
                stbuf->st_blocks = 2;
                return 0;
            }
            playlist = playlist->next;   
        }
        return -ENOENT;
    }

    if (strcmp (path, "/") == 0) {
        stbuf->st_mode = S_IFDIR | 0777;
        stbuf->st_nlink = 2;
    } else {
        int item_id = -1;
        LIBMTP_folder_t *folder;
        check_folders();
        folder = folders;
        item_id = lookup_folder_id (folder, (gchar *) path, "");
        if (item_id >= 0) {
            stbuf->st_ino = item_id;
            stbuf->st_mode = S_IFDIR | 0777;
            stbuf->st_nlink = 2;
        } else {
            item_id = parse_path (path);
            LIBMTP_file_t *file;
            if (DEBUG) g_debug ("%d:%s", item_id, path);
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
                    found = TRUE;
                }
                file = file->next;
            }
            if (!found) {
                ret = -ENOENT;
            }
        }
    }

    return ret;
}

static int
mtpfs_mknod (const gchar * path, mode_t mode, dev_t dev)
{
    if (DEBUG) g_debug ("mknod");
    int item_id = parse_path (path);
    if (item_id > 0)
        return -EEXIST;

    myfiles = g_slist_append (myfiles, (gpointer) (g_strdup (path)));
    if (DEBUG) g_debug ("NEW FILE");
    return 0;
}

static int
mtpfs_open (const gchar * path, struct fuse_file_info *fi)
{
    if (DEBUG) g_debug ("open");
    int item_id = -1;
    item_id = parse_path (path);
    if (item_id < 0)
        return -ENOENT;

    if (fi->flags == O_RDONLY) {
        if (DEBUG) g_debug("read");
    } else if (fi->flags == O_WRONLY) {
        if (DEBUG) g_debug("write");
    } else if (fi->flags == O_RDWR) {
        if (DEBUG) g_debug("rdwrite");
    }

    FILE *filetmp = tmpfile ();
    int tmpfile = fileno (filetmp);
    if (tmpfile != -1) {
        if (item_id == 0) {
            fi->fh = tmpfile;
        } else if (strncmp("/Playlists/",path,11) == 0) {
            // Is a playlist
            gchar **fields;
            fields = g_strsplit(path,"/",-1);
            gchar *name;
            name = g_strndup(fields[2],strlen(fields[2])-4);
            g_strfreev(fields);
            fi->fh = tmpfile;
            LIBMTP_playlist_t *playlist;
            check_playlists();
            playlist = playlists;
            while (playlist != NULL) {
                if (strcasecmp(playlist->name,name) == 0 ) {
                    //int playlist_id=playlist->playlist_id;
                    int i;
                    for (i=0; i <playlist->no_tracks; i++){
                        LIBMTP_file_t *file;
                        LIBMTP_folder_t *folder;
                        g_mutex_lock(device_lock);
                        file = LIBMTP_Get_Filemetadata(device,playlist->tracks[i]);
                        g_mutex_unlock(device_lock);
                        if (file != NULL) {
                            gchar *path;
                            path = (gchar *) g_malloc (1024);
                            path = strcpy(path,"/");
                            int parent_id = file->parent_id;
                            while (parent_id != 0) {
                                check_folders();
                                g_mutex_lock(device_lock);
                                folder = LIBMTP_Find_Folder(folders,parent_id);
                                path = strcat(path,folder->name);
                                path = strcat(path,"/");
                                parent_id = folder->parent_id;
                                g_mutex_unlock(device_lock);
                            }
                            path = strcat (path,file->filename);
                            fprintf (filetmp,"%s\n",path);
                            if (DEBUG) g_debug("%s\n",path);
                        }
                    }
                    //LIBMTP_destroy_file_t(file);
                    fflush(filetmp);
                    break;
                }
                playlist=playlist->next;
            }
        } else {
            g_mutex_lock(device_lock);
            int ret =
                LIBMTP_Get_File_To_File_Descriptor (device, item_id, tmpfile,
                                                    NULL, NULL);
            g_mutex_unlock(device_lock);
            if (ret == 0) {
                fi->fh = tmpfile;
            } else {
                return -ENOENT;
            }
        }
    } else {
        return -ENOENT;
    }

    return 0;
}

static int
mtpfs_read (const gchar * path, gchar * buf, size_t size, off_t offset,
            struct fuse_file_info *fi)
{
    if (DEBUG) g_debug ("read");
    int ret;

    int item_id = -1;
    item_id = parse_path (path);
    if (item_id < 0)
        return -ENOENT;

    ret = pread (fi->fh, buf, size, offset);
    if (ret == -1)
        ret = -errno;

    return ret;
}

static int
mtpfs_write (const gchar * path, const gchar * buf, size_t size, off_t offset,
             struct fuse_file_info *fi)
{
    //if (DEBUG) g_debug ("write");
    int ret;
    if (fi->fh != -1) {
        ret = pwrite (fi->fh, buf, size, offset);
    } else {
        ret = -ENOENT;
    }

    return ret;
}


static int
mtpfs_unlink (const gchar * path)
{
    if (DEBUG) g_debug ("unlink");
    int ret = 0;
    int item_id = -1;
    item_id = parse_path (path);
    if (item_id < 0)
        return -ENOENT;
    g_mutex_lock(device_lock);
    ret = LIBMTP_Delete_Object (device, item_id);
    if (strncmp (path, "/Playlists",10) == 0) {
        playlists_changed = TRUE;
    } else {
        files_changed = TRUE;
    }
    g_mutex_unlock(device_lock);

    return ret;
}

static int
mtpfs_mkdir (const char *path, mode_t mode)
{
    if (DEBUG) g_debug ("mkdir");
    int ret = 0;
    GSList *item;
    item = g_slist_find_custom (myfiles, path, (GCompareFunc) strcmp);
    int item_id = parse_path (path);
    if ((item == NULL) && (item_id < 0)) {
        // Split path and find parent_id
        gchar *filename="";
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
                    directory = g_strndup (directory, strlen (directory) - 1);
                    check_folders();
                    parent_id = lookup_folder_id (folders, directory, "");
                    if (parent_id < 0)
                        parent_id = 0;
                    filename = g_strdup (fields[i]);
                } else {
                    directory = strcat (directory, fields[i]);
                    directory = strcat (directory, "/");
                }
            }
        }
        if (DEBUG) g_debug ("%s:%s:%d", filename, directory, parent_id);
        g_mutex_lock(device_lock);
        ret = LIBMTP_Create_Folder (device, filename, parent_id);
        g_mutex_unlock(device_lock);
        g_strfreev (fields);
        if (ret == 0) {
            ret = -EEXIST;
        } else {
            folders_changed=TRUE;
            ret = 0;
        }
    } else {
        ret = -EEXIST;
    }
    return ret;
}

static int
mtpfs_rmdir (const char *path)
{
    if (DEBUG) g_debug ("rmdir");
    int ret = 0;
    int folder_id = -1;
    if (strcmp (path, "/") != 0) {
        folder_id = lookup_folder_id (folders, (gchar *) path, "");
    }
    if (folder_id < 0)
        return -ENOENT;
    
    g_mutex_lock(device_lock);
    LIBMTP_Delete_Object(device, folder_id);
    g_mutex_unlock(device_lock);

    folders_changed=TRUE;
    return ret;
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
                parent_id = lookup_folder_id (folders, directory, "");
                if (parent_id < 0)
                    parent_id = 0;
                filename = g_strdup (fields[i]);
            } else {
                directory = strcat (directory, fields[i]);
                directory = strcat (directory, "/");

            }
        }
    }
    if (DEBUG) g_debug ("%s:%s:%d", filename, directory, parent_id);

    track->parent_id = parent_id;
    track->title = g_strdup(filename);
    int ret = LIBMTP_Update_Track_Metadata(device, track);
    return ret;
}
*/

static int
mtpfs_statfs (const char *path, struct statfs *stbuf)
{
    if (DEBUG) g_debug ("mtpfs_statfs");
    stbuf->f_bsize=1024;
    stbuf->f_blocks=device->storage->MaxCapacity/1024;
    stbuf->f_bfree=device->storage->FreeSpaceInBytes/1024;
    stbuf->f_ffree=device->storage->FreeSpaceInObjects/1024;
    stbuf->f_bavail=stbuf->f_bfree;
    return 0;
}

void *
mtpfs_init ()
{
    if (DEBUG) g_debug ("mtpfs_init");
    LIBMTP_Init ();
    device = LIBMTP_Get_First_Device ();
    if (device == NULL) {
        if (DEBUG) g_debug ("No devices.");
        exit (1);
    }
    if (!g_thread_supported ()) g_thread_init(NULL);
    device_lock = g_mutex_new ();
    files_changed=TRUE;
    folders_changed=TRUE;
    playlists_changed=TRUE;
    //if (DEBUG) g_debug ("Get Folder List");
    //folders = LIBMTP_Get_Folder_List (device);
    //if (DEBUG) g_debug ("Get File List");
    //files = LIBMTP_Get_Filelisting (device);
    //if (DEBUG) g_debug ("Get Playlists");
    //playlists = LIBMTP_Get_Playlist_List(device);
    if (DEBUG) g_debug ("Ready");
    return 0;
}

static struct fuse_operations mtpfs_oper = {
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
/*    .rename  = mtpfs_rename,*/
    .statfs  = mtpfs_statfs,
    .init    = mtpfs_init,
};

int
main (int argc, char *argv[])
{
    umask (0);
    return fuse_main (argc, argv, &mtpfs_oper);
}

/* Private buffer for passing around with libmad */
typedef struct
{
    /* The buffer of raw mpeg data for libmad to decode */
    void * buf;

    /* Cached data: pointers to the dividing points of frames
       in buf, and the playing time at each of those frames */
    void **frames;
    mad_timer_t *times;

    /* fd is the file descriptor if over the network, or -1 if
       using mmap()ed files */
    int fd;

    /* length of the current stream, corrected for id3 tags */
    ssize_t length;

    /* have we finished fetching this file? (only in non-mmap()'ed case */
    int done;

    /* total number of frames */
    unsigned long num_frames;

    /* number of frames to play */
    unsigned long max_frames;

    /* total duration of the file */
    mad_timer_t duration;

    /* filename as mpg321 has opened it */
    char filename[PATH_MAX];
} buffer;

/* XING parsing is from the MAD winamp input plugin */

struct xing {
      int flags;
      unsigned long frames;
      unsigned long bytes;
      unsigned char toc[100];
      long scale;
};

enum {
      XING_FRAMES = 0x0001,
      XING_BYTES  = 0x0002,
      XING_TOC    = 0x0004,
      XING_SCALE  = 0x0008
};

# define XING_MAGIC     (('X' << 24) | ('i' << 16) | ('n' << 8) | 'g')



/* Following two function are adapted from mad_timer, from the
   libmad distribution */
static
int parse_xing(struct xing *xing, struct mad_bitptr ptr, unsigned int bitlen)
{
  if (bitlen < 64 || mad_bit_read(&ptr, 32) != XING_MAGIC)
    goto fail;

  xing->flags = mad_bit_read(&ptr, 32);
  bitlen -= 64;

  if (xing->flags & XING_FRAMES) {
    if (bitlen < 32)
      goto fail;

    xing->frames = mad_bit_read(&ptr, 32);
    bitlen -= 32;
  }

  if (xing->flags & XING_BYTES) {
    if (bitlen < 32)
      goto fail;

    xing->bytes = mad_bit_read(&ptr, 32);
    bitlen -= 32;
  }

  if (xing->flags & XING_TOC) {
    int i;

    if (bitlen < 800)
      goto fail;

    for (i = 0; i < 100; ++i)
      xing->toc[i] = mad_bit_read(&ptr, 8);

    bitlen -= 800;
  }

  if (xing->flags & XING_SCALE) {
    if (bitlen < 32)
      goto fail;

    xing->scale = mad_bit_read(&ptr, 32);
    bitlen -= 32;
  }

  return 1;
 fail:
  xing->flags = 0;
  return 0;
}


int scan(void const *ptr, ssize_t len)
{
    struct mad_stream stream;
    struct mad_header header;
    struct xing xing;
    xing.frames=0;
    g_debug("scan: %d",len);


    unsigned long bitrate = 0;
    int has_xing = 0;
    int is_vbr = 0;
    int duration = 0;
    mad_stream_init(&stream);
    mad_header_init(&header);

    mad_stream_buffer(&stream, ptr, len);

    int num_frames = 0;

    /* There are three ways of calculating the length of an mp3:
      1) Constant bitrate: One frame can provide the information
         needed: # of frames and duration. Just see how long it
         is and do the division.
      2) Variable bitrate: Xing tag. It provides the number of
         frames. Each frame has the same number of samples, so
         just use that.
      3) All: Count up the frames and duration of each frames
         by decoding each one. We do this if we've no other
         choice, i.e. if it's a VBR file with no Xing tag.
    */

    while (1)
    {
        if (mad_header_decode(&header, &stream) == -1)
        {
            if (MAD_RECOVERABLE(stream.error))
                continue;
            else
                break;
        }

        /* Limit xing testing to the first frame header */
        if (!num_frames++)
        {
            if(parse_xing(&xing, stream.anc_ptr, stream.anc_bitlen))
            {
                is_vbr = 1;

                if (xing.flags & XING_FRAMES)
                {
                    /* We use the Xing tag only for frames. If it doesn't have that
                       information, it's useless to us and we have to treat it as a
                       normal VBR file */
                    has_xing = 1;
                    num_frames = xing.frames;
                    break;
                }
            }
        }

        /* Test the first n frames to see if this is a VBR file */
        if (!is_vbr && !(num_frames > 20))
        {
            if (bitrate && header.bitrate != bitrate)
            {
                is_vbr = 1;
            }

            else
            {
                bitrate = header.bitrate;
            }
        }

        /* We have to assume it's not a VBR file if it hasn't already been
           marked as one and we've checked n frames for different bitrates */
        else if (!is_vbr)
        {
            break;
        }

        duration = header.duration.seconds;
    }

    if (!is_vbr)
    {
        double time = (len * 8.0) / (header.bitrate); /* time in seconds */
        //double timefrac = (double)time - ((long)(time));
        long nsamples = 32 * MAD_NSBSAMPLES(&header); /* samples per frame */

        /* samplerate is a constant */
        num_frames = (long) (time * header.samplerate / nsamples);

        duration = (int)time;
        g_debug("d:%d",duration);
    }

    else if (has_xing)
    {
        /* modify header.duration since we don't need it anymore */
        mad_timer_multiply(&header.duration, num_frames);
        duration = header.duration.seconds;
    }

    else
    {
        /* the durations have been added up, and the number of frames
           counted. We do nothing here. */
    }

    mad_header_finish(&header);
    mad_stream_finish(&stream);
    return duration;
}


int calc_length(int f)
{
    struct stat filestat;
    void *fdm;
    char buffer[3];

    fstat(f, &filestat);

    /* TAG checking is adapted from XMMS */
    int length = filestat.st_size;

    if (lseek(f, -128, SEEK_END) < 0)
    {
        /* File must be very short or empty. Forget it. */
        return -1;
    }

    if (read(f, buffer, 3) != 3)
    {
        return -1;
    }

    if (!strncmp(buffer, "TAG", 3))
    {
        length -= 128; /* Correct for id3 tags */
    }

    fdm = mmap(0, length, PROT_READ, MAP_SHARED, f, 0);
    if (fdm == MAP_FAILED)
    {
        g_error("Map failed");
        return -1;
    }

    /* Scan the file for a XING header, or calculate the length,
       or just scan the whole file and add everything up. */
    int duration = scan(fdm, length);

    if (munmap(fdm, length) == -1)
    {
        g_error("Unmap failed");
        return -1;
    }

    lseek(f, 0, SEEK_SET);
    return duration;
}

