// SPDX-FileCopyrightText: 2009-2020 ret2libc <sirmy15@gmail.com>
// SPDX-License-Identifier: LGPL-3.0-only

#include <rz_types.h>
#include <rz_util.h>

struct buf_file_user {
	const char *file;
	int perm;
	int mode;
};

#ifdef __EMSCRIPTEN__
// Keeps its own position and reads from a cache of aligned blocks, because each read() is a call
// into the file system of JavaScript and Rizin makes millions of small reads.
#define RZ_BUF_FILE_BLOCK_SIZE (64 * 1024)
#define RZ_BUF_FILE_BLOCKS     256
#endif

struct buf_file_priv {
	int fd;
	ut8 tmp[8];
#ifdef __EMSCRIPTEN__
	ut64 position;
	ut64 block_offset[RZ_BUF_FILE_BLOCKS];
	st64 block_length[RZ_BUF_FILE_BLOCKS];
	ut8 *block[RZ_BUF_FILE_BLOCKS];
#endif
};

static inline struct buf_file_priv *get_priv_file(RzBuffer *b) {
	struct buf_file_priv *priv = (struct buf_file_priv *)b->priv;
	rz_warn_if_fail(priv);
	return priv;
}

static bool buf_file_init(RzBuffer *b, const void *user) {
	const struct buf_file_user *u = (const struct buf_file_user *)user;
	struct buf_file_priv *priv = RZ_NEW0(struct buf_file_priv);
	if (!priv) {
		return false;
	}
	int fd = rz_sys_open(u->file, u->perm, u->mode);
	if (fd == -1) {
		free(priv);
		return false;
	}
	priv->fd = fd;
	b->priv = priv;
	b->fd = priv->fd;
	return true;
}

static bool buf_file_fini(RzBuffer *b) {
	struct buf_file_priv *priv = get_priv_file(b);
	close(priv->fd);
#ifdef __EMSCRIPTEN__
	for (int i = 0; i < RZ_BUF_FILE_BLOCKS; i++) {
		free(priv->block[i]);
	}
#endif
	RZ_FREE(b->priv);
	return true;
}

static ut64 buf_file_get_size(RzBuffer *b) {
	struct buf_file_priv *priv = get_priv_file(b);
	off_t pos = lseek(priv->fd, 0, SEEK_CUR);
	off_t res = lseek(priv->fd, 0, SEEK_END);
	if (pos >= 0) {
		lseek(priv->fd, (off_t)pos, SEEK_SET);
	}
	return (ut64)res;
}

static st64 buf_file_read(RZ_BORROW RzBuffer *b, RZ_OUT ut8 *buf, ut64 len) {
	struct buf_file_priv *priv = get_priv_file(b);
#ifdef __EMSCRIPTEN__
	ut64 done = 0;
	while (done < len) {
		ut64 at = priv->position + done;
		ut64 number = at / RZ_BUF_FILE_BLOCK_SIZE;
		int i = (int)(number % RZ_BUF_FILE_BLOCKS);
		if (!priv->block[i] || priv->block_length[i] <= 0 || priv->block_offset[i] != number * RZ_BUF_FILE_BLOCK_SIZE) {
			if (!priv->block[i] && !(priv->block[i] = malloc(RZ_BUF_FILE_BLOCK_SIZE))) {
				return -1;
			}
			priv->block_offset[i] = number * RZ_BUF_FILE_BLOCK_SIZE;
			priv->block_length[i] = pread(priv->fd, priv->block[i], RZ_BUF_FILE_BLOCK_SIZE, (off_t)priv->block_offset[i]);
		}
		if (priv->block_length[i] <= 0 || at >= priv->block_offset[i] + (ut64)priv->block_length[i]) {
			priv->block_length[i] = 0;
			break;
		}
		ut64 offset = at - priv->block_offset[i];
		ut64 size = RZ_MIN(len - done, (ut64)priv->block_length[i] - offset);
		memcpy(buf + done, priv->block[i] + offset, size);
		done += size;
	}
	priv->position += done;
	return (st64)done;
#else
	ssize_t result = read(priv->fd, buf, len);
	return result;
#endif
}

static st64 buf_file_write(RzBuffer *b, const ut8 *buf, ut64 len) {
	struct buf_file_priv *priv = get_priv_file(b);
#ifdef __EMSCRIPTEN__
	memset(priv->block_length, 0, sizeof(priv->block_length));
	ssize_t written = pwrite(priv->fd, buf, len, (off_t)priv->position);
	if (written > 0) {
		priv->position += written;
	}
	return written;
#else
	return write(priv->fd, buf, len);
#endif
}

static st64 buf_file_seek(RzBuffer *b, st64 addr, int whence) {
	struct buf_file_priv *priv = get_priv_file(b);
	switch (whence) {
	case RZ_BUF_CUR: whence = SEEK_CUR; break;
	case RZ_BUF_SET: whence = SEEK_SET; break;
	case RZ_BUF_END: whence = SEEK_END; break;
	}
#ifdef __EMSCRIPTEN__
	st64 position;
	if (whence == SEEK_SET) {
		position = addr;
	} else if (whence == SEEK_CUR) {
		position = (st64)priv->position + addr;
	} else {
		position = (st64)buf_file_get_size(b) + addr;
	}
	if (position < 0) {
		return -1;
	}
	priv->position = (ut64)position;
	return position;
#else
	return lseek(priv->fd, (off_t)addr, whence);
#endif
}

static bool buf_file_resize(RzBuffer *b, ut64 newsize) {
	struct buf_file_priv *priv = get_priv_file(b);
#ifdef __EMSCRIPTEN__
	memset(priv->block_length, 0, sizeof(priv->block_length));
#endif
	return rz_sys_truncate_fd(priv->fd, newsize) >= 0;
}

static const RzBufferMethods buffer_file_methods = {
	.init = buf_file_init,
	.fini = buf_file_fini,
	.read = buf_file_read,
	.write = buf_file_write,
	.get_size = buf_file_get_size,
	.resize = buf_file_resize,
	.seek = buf_file_seek,
};
