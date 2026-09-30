/* fs_shim.c -- the two questions about a directory Fortran cannot ask:
 * is this path a directory, and what does it hold. readdir's struct is
 * laid out differently on each system, so it is read here, in C. POSIX;
 * Windows (FindFirstFile) waits for v1.0. */
#include <dirent.h>
#include <string.h>
#include <sys/stat.h>

/* 1 a directory, 0 anything else, -1 no such path */
int clotran_fs_kind(const char *path) {
  struct stat st;
  if (stat(path, &st) != 0) return -1;
  return S_ISDIR(st.st_mode) ? 1 : 0;
}

/* The names in a directory, without . and .., each ended by a newline,
 * into buf. The length written; -1 if it cannot be opened; -(needed) if
 * buf is too small, so the caller can ask again with room. */
long clotran_fs_list(const char *path, char *buf, long cap) {
  DIR *d = opendir(path);
  struct dirent *e;
  long n = 0;
  int short_of_room = 0;
  if (!d) return -1;
  while ((e = readdir(d)) != NULL) {
    size_t k = strlen(e->d_name);
    if (strcmp(e->d_name, ".") == 0 || strcmp(e->d_name, "..") == 0) continue;
    if (!short_of_room && n + (long)k + 1 <= cap) {
      memcpy(buf + n, e->d_name, k);
      buf[n + k] = '\n';
    } else {
      short_of_room = 1;
    }
    n += (long)k + 1;
  }
  closedir(d);
  return short_of_room ? -n : n;
}
