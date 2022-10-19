#ifndef __VECTOR_H
#define __VECTOR_H

#include "recalloc.h"

struct vector {
  void** data;
  int32_t len;
};

static void vector_make(struct vector *v, int32_t len) {
  v->data = calloc(1 << 12, sizeof(void*));
  v->len = len;
}

static void vector_resize(struct vector *v, int32_t len) {
  v->data = recalloc(v->data, v->len, len, sizeof(void*));
  v->len = len;
}

static void vector_clear(struct vector *v) {
  for (int i = 0; i < v->len; ++i)
    v->data[i] = NULL;
}


#endif /* __VECTOR_H */
