#ifndef __HASHTBLI_H
#define __HASHTBLI_H

#include "recalloc.h"
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>

// Hashtable indexing items by pairs of integer hashes.
// Stored items must be non are non-null.

struct hashtbli2_elem {
  uint64_t hash1, hash2;
  void* data;
};

struct hashtbli3_elem {
  uint64_t hash1, hash2, hash3;
  void* data;
};

struct hashtbli2 {
  struct hashtbli2_elem *d;
  uint32_t num;     // Bindings
  uint32_t maxelem; // Space
  uint32_t *used;   // Used indices for resizing
};

struct hashtbli3 {
  struct hashtbli3_elem *d;
  uint32_t num;     // Bindings
  uint32_t maxelem; // Space
  uint32_t *used;   // Used indices for resizing
};

static uint32_t hashtbli2_find_index(struct hashtbli2 *h, uint64_t hsh1, uint64_t hsh2) {
  uint32_t pos = (hsh1 ^ hsh2) & h->maxelem;
  while (h->d[pos].data && (h->d[pos].hash1 != hsh1 || h->d[pos].hash2 != hsh2))
    pos = (pos + 1) & h->maxelem;
  return pos;
}

static uint32_t hashtbli3_find_index(struct hashtbli3 *h, uint64_t hsh1, uint64_t hsh2, uint64_t hsh3) {
  uint32_t pos = (hsh1 ^ hsh2 ^ hsh3) & h->maxelem;
  while (h->d[pos].data && (h->d[pos].hash1 != hsh1 || h->d[pos].hash2 != hsh2 || h->d[pos].hash3 != hsh3))
    pos = (pos + 1) & h->maxelem;
  return pos;
}

static void* hashtbli2_find(struct hashtbli2 *h, uint64_t hsh1, uint64_t hsh2) {
  uint32_t pos = (hsh1 ^ hsh2) & h->maxelem;
  while (h->d[pos].data && (h->d[pos].hash1 != hsh1 || h->d[pos].hash2 != hsh2))
    pos = (pos + 1) & h->maxelem;
  return (h->d[pos].data);
}

static void hashtbli2_clear(struct hashtbli2 *h) {
  for (uint32_t i=0; i<h->num; ++i)
    h->d[h->used[i]].data=NULL;
  h->num=0;
}

static void hashtbli3_clear(struct hashtbli3 *h) {
  for (uint32_t i=0; i<h->num; ++i)
    h->d[h->used[i]].data=NULL;
  h->num=0;
}

// Returns: did the rehashing change
static bool hashtbli2_rehash(struct hashtbli2 *h) {
  bool changed = false; void* tmp; int32_t pos;
  for (int k = 0; k < h->num; ++k) {
    int32_t i = h->used[k]; int64_t hsh1 = h->d[i].hash1, hsh2 = h->d[i].hash2;
    tmp=h->d[i].data; h->d[i].data=NULL; pos=hashtbli2_find_index(h, hsh1, hsh2);
    if (pos == i) {
      h->d[i].data = tmp;
    } else {
      h->d[pos].data = tmp;
      h->d[pos].hash1 = hsh1;
      h->d[pos].hash2 = hsh2;
      h->used[k]=pos;
      changed = true;
    }
  }
  return changed;
}

static bool hashtbli3_rehash(struct hashtbli3 *h) {
  bool changed = false; void* tmp; int32_t pos;
  for (int k = 0; k < h->num; ++k) {
    int32_t i = h->used[k]; int64_t hsh1 = h->d[i].hash1, hsh2 = h->d[i].hash2, hsh3 = h->d[i].hash3;
    tmp=h->d[i].data; h->d[i].data=NULL; pos=hashtbli3_find_index(h, hsh1, hsh2, hsh3);
    if (pos == i) {
      h->d[i].data = tmp;
    } else {
      h->d[pos].data = tmp;
      h->d[pos].hash1 = hsh1;
      h->d[pos].hash2 = hsh2;
      h->d[pos].hash3 = hsh3;
      h->used[k]=pos;
      changed = true;
    }
  }
  return changed;
}

static void hashtbli2_double(struct hashtbli2 *h) {
  h->d = recalloc(h->d, h->maxelem+1, (h->maxelem+1)<<1, sizeof(struct hashtbli2_elem));
  h->used = recalloc(h->used, (h->maxelem+1)>>1, h->maxelem+1, sizeof(uint32_t));
  if (!h->d || !h->used) { printf("hashtbli2_double: Out of memory!\n"); fflush(stdout); }
  h->maxelem = (h->maxelem<<1) + 1;
  while (hashtbli2_rehash(h));
}

static void hashtbli3_double(struct hashtbli3 *h) {
  h->d = recalloc(h->d, h->maxelem+1, (h->maxelem+1)<<1, sizeof(struct hashtbli3_elem));
  h->used = recalloc(h->used, (h->maxelem+1)>>1, h->maxelem+1, sizeof(uint32_t));
  if (!h->d || !h->used) { printf("hashtbli3_double: Out of memory!\n"); fflush(stdout); }
  h->maxelem = (h->maxelem<<1) + 1;
  while (hashtbli3_rehash(h));
}

// Returns the pointer to the added item
static void* hashtbli2_add_atpos(struct hashtbli2 *h, uint32_t pos, uint64_t hsh1, uint64_t hsh2, void* t) {
  h->d[pos].data=t;
  h->d[pos].hash1=hsh1;
  h->d[pos].hash2=hsh2;
  h->used[h->num]=pos;
  h->num++;
  if (h->num >= (h->maxelem >> 1))
    hashtbli2_double(h);
  return t;
}

static void* hashtbli3_add_atpos(struct hashtbli3 *h, uint32_t pos, uint64_t hsh1, uint64_t hsh2, uint64_t hsh3, void* t) {
  h->d[pos].data=t;
  h->d[pos].hash1=hsh1;
  h->d[pos].hash2=hsh2;
  h->d[pos].hash3=hsh3;
  h->used[h->num]=pos;
  h->num++;
  if (h->num >= (h->maxelem >> 1))
    hashtbli3_double(h);
  return t;
}

static void* hashtbli2_add(struct hashtbli2 *h, uint64_t hsh1, uint64_t hsh2, void* t) {
  uint32_t pos = hashtbli2_find_index(h, hsh1, hsh2);
  if (h->d[pos].data) printf ("Warning: Hashtbli2_add overwrite!\n");
  return hashtbli2_add_atpos(h, pos, hsh1, hsh2, t);
}

static void hashtbli2_make(struct hashtbli2 *h, uint32_t len) {
  h->d = calloc(len, sizeof(struct hashtbli2_elem));
  h->maxelem = len-1;
  h->num = 0;
  h->used = calloc(len >> 1, sizeof(uint32_t));
}

static void hashtbli3_make(struct hashtbli3 *h, uint32_t len) {
  h->d = calloc(len, sizeof(struct hashtbli3_elem));
  h->maxelem = len-1;
  h->num = 0;
  h->used = calloc(len >> 1, sizeof(uint32_t));
}

#endif /* __HASHTBLI_H */
