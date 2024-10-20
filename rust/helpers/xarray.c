// SPDX-License-Identifier: GPL-2.0

#include <linux/xarray.h>

void *rust_helper_xa_zero_entry(void)
{
	return XA_ZERO_ENTRY;
}

int rust_helper_xa_err(void *entry)
{
	return xa_err(entry);
}

void *rust_helper_xa_load(struct xarray *xa, unsigned long index)
{
	return xa_load(xa, index);
}

void *rust_helper_xa_find(struct xarray *xa, unsigned long *index,
			  unsigned long max, xa_mark_t mark)
{
	return xa_find(xa, index, max, mark);
}

void *rust_helper_xa_find_after(struct xarray *xa, unsigned long *index,
				unsigned long max, xa_mark_t mark)
{
	return xa_find_after(xa, index, max, mark);
}

void rust_helper_xa_destroy(struct xarray *xa)
{
	return xa_destroy(xa);
}

void rust_helper_xa_init_flags(struct xarray *xa, gfp_t flags)
{
	return xa_init_flags(xa, flags);
}

int rust_helper_xa_trylock(struct xarray *xa)
{
	return xa_trylock(xa);
}

void rust_helper_xa_lock(struct xarray *xa)
{
	return xa_lock(xa);
}

void rust_helper_xa_unlock(struct xarray *xa)
{
	return xa_unlock(xa);
}

void *rust_helper___xa_erase(struct xarray *xa, unsigned long index)
{
	return __xa_erase(xa, index);
}

void *rust_helper___xa_store(struct xarray *xa, unsigned long index,
			     void *entry, gfp_t gfp)
{
	return __xa_store(xa, index, entry, gfp);
}

int rust_helper___xa_insert(struct xarray *xa, unsigned long index,
			    void *entry, gfp_t gfp)
{
	return __xa_insert(xa, index, entry, gfp);
}

void *rust_helper___xa_cmpxchg(struct xarray *xa, unsigned long index,
			       void *old, void *entry, gfp_t gfp)
{
	return __xa_cmpxchg(xa, index, old, entry, gfp);
}

int rust_helper___xa_alloc(struct xarray *xa, u32 *id, void *entry,
			   struct xa_limit limit, gfp_t gfp)
{
	return __xa_alloc(xa, id, entry, limit, gfp);
}

int rust_helper___xa_alloc_cyclic(struct xarray *xa, u32 *id, void *entry,
				  struct xa_limit limit, u32 *next, gfp_t gfp)
{
	return __xa_alloc_cyclic(xa, id, entry, limit, next, gfp);
}
