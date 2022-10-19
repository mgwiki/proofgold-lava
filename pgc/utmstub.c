#include "hashtbli.h"
#include "vector.h"

enum l_kind { NONE=0, DB, TMH, PRIM, AP, LAM, IMP, ALL, EX, EQ };

struct tm_struct {
  int16_t tag; uint16_t x; uint16_t y;
  int32_t no;
  struct tm_struct *l;
  struct tm_struct *r;
  uint64_t id;
};
typedef struct tm_struct* trm_p;

#define BLOCK_SIZE (1 << 16)

static struct tm_struct **tm;
static uint32_t x; // position of next tm (or length in current block)
static uint32_t y; // current block number
static uint32_t y_len; // allocated blocks
static uint32_t start_x; // Used by pre-hashed terms not cleared (DBs)

static uint8_t *id; // Hash of all used hashes
static uint32_t idmaxelem;

static struct hashtbli2 imps, aps, lams, alls, exs, arrs;
static struct hashtbli3 eqs;

static trm_p dbs[256];
static struct vector tmhs, prims, bases;

static void double_id() {
  uint32_t newmaxelem = (idmaxelem << 1) + 1;
  id=recalloc(id, idmaxelem + 1, newmaxelem + 1, sizeof(uint8_t));
  for (int i = 0; i <= y; ++i) {
    for (int j = 0; j < ((i == y) ? x : BLOCK_SIZE); ++j) {
      id[tm[i][j].id & idmaxelem]=0;
      id[tm[i][j].id & newmaxelem]=1;
    }
  }
  idmaxelem = newmaxelem;
}

static uint64_t new_id() {
  uint64_t r = rand();
  // make sure hashes are non-zero to allow having them as options
  while (id[r & idmaxelem] || r == 0)
    r = rand();
  id[r & idmaxelem] = 1;
  return r;
}

static void tm_id_clear() {
  for (int i = 0; i <= y; ++i) {
    for (int j = ((i == 0) ? start_x : 0); j < ((i == y) ? x : BLOCK_SIZE); ++j) {
      id[tm[i][j].id & idmaxelem]=0;
    }
  }
  y=0; x=start_x;
}

// Finds next position in blocks and returns a cell with x and y set.
static trm_p incr_xy() {
  if (x >= BLOCK_SIZE) {
    x = 0; y++;
    if (y >= y_len) {
      tm[y] = calloc(BLOCK_SIZE, sizeof(struct tm_struct));
      if (!tm[y]) { printf("incr_xy: Out of memory!\n"); fflush(stdout); }
      y_len++;
    }
    if ((y + 1) * BLOCK_SIZE > (idmaxelem >> 1)) // space for x to grow
      double_id();
  }
  tm[y][x].x=x; tm[y][x].y=y;
  return &tm[y][x++];
}

static trm_p add_tm_no(int16_t tag, int32_t no, trm_p r) {
  trm_p ret = incr_xy();
  ret->tag = tag; ret->no = no; ret->r = r; ret->id = new_id();
  return ret;
}

static trm_p add_tm_l(int16_t tag, trm_p l, trm_p r) {
  trm_p ret = incr_xy();
  ret->tag = tag; ret->l = l; ret->r = r; ret->id = new_id();
  return ret;
}

static trm_p add_tm_nol(int16_t tag, int32_t no, trm_p l, trm_p r) {
  trm_p ret = incr_xy();
  ret->tag = tag; ret->no = no; ret->l = l; ret->r = r; ret->id = new_id();
  return ret;
}


static void init_unique_terms() {
  tm = calloc(BLOCK_SIZE, sizeof(struct tm_struct *));
  x = 0; y = 0; y_len = 8;
  for (int i = 0; i < y_len; ++i)
    tm[i] = calloc(BLOCK_SIZE, sizeof(struct tm_struct));
  id = calloc(1 << 20, sizeof(uint8_t));
  idmaxelem = (1 << 20) - 1;
  hashtbli2_make(&imps,  1 << 16);
  hashtbli2_make(&aps,   1 << 16);
  hashtbli2_make(&lams,  1 << 16);
  hashtbli2_make(&alls,  1 << 16);
  hashtbli2_make(&exs,  1 << 16);
  hashtbli3_make(&eqs,  1 << 16);
  hashtbli2_make(&arrs,  1 << 16);
  for (int i = 0; i < 256; ++i)
    dbs[i] = add_tm_no(DB, i, NULL);
  vector_make(&tmhs, 1 << 12);
  vector_make(&prims, 1 << 12);
  vector_make(&bases, 1 << 12);
  start_x = x;
}

static trm_p mk_imp(trm_p l, trm_p r) {
  uint32_t pos = hashtbli2_find_index(&imps, l->id, r->id);
  if (imps.d[pos].data) return imps.d[pos].data;
  return(hashtbli2_add_atpos(&imps, pos, l->id, r->id, add_tm_l(IMP, l, r)));
}

static trm_p mk_ap(trm_p l, trm_p r) {
  uint32_t pos = hashtbli2_find_index(&aps, l->id, r->id);
  if (aps.d[pos].data) return aps.d[pos].data;
  return(hashtbli2_add_atpos(&aps, pos, l->id, r->id, add_tm_l(AP, l, r)));
}

static trm_p mk_lam(uint32_t tyno, trm_p t) {
  uint32_t pos = hashtbli2_find_index(&lams, ((uint64_t)tyno)<<10, t->id);
  if (lams.d[pos].data) return lams.d[pos].data;
  return(hashtbli2_add_atpos(&lams, pos, ((uint64_t)tyno)<<10, t->id, add_tm_no(LAM, tyno, t)));
}

static trm_p mk_all(uint32_t tyno, trm_p t) {
  uint32_t pos = hashtbli2_find_index(&alls, ((uint64_t)tyno)<<10, t->id);
  if (alls.d[pos].data) return alls.d[pos].data;
  return(hashtbli2_add_atpos(&alls, pos, ((uint64_t)tyno)<<10, t->id, add_tm_no(ALL, tyno, t)));
}

static trm_p mk_ex(uint32_t tyno, trm_p t) {
  uint32_t pos = hashtbli2_find_index(&exs, ((uint64_t)tyno)<<10, t->id);
  if (exs.d[pos].data) return exs.d[pos].data;
  return(hashtbli2_add_atpos(&exs, pos, ((uint64_t)tyno)<<10, t->id, add_tm_no(EX, tyno, t)));
}

static trm_p mk_eq(uint32_t tyno, trm_p t1, trm_p t2) {
  uint32_t pos = hashtbli3_find_index(&eqs, ((uint64_t)tyno)<<10, t1->id, t2->id);
  if (eqs.d[pos].data) return eqs.d[pos].data;
  return(hashtbli3_add_atpos(&eqs, pos, ((uint64_t)tyno)<<10, t1->id, t2->id, add_tm_nol(EQ, tyno, t1, t2)));
}

static uint64_t mk_tparr(uint64_t l, uint64_t r) {
  uint32_t pos = hashtbli2_find_index(&arrs, l, r);
  if (arrs.d[pos].data) return (uint64_t)(arrs.d[pos].data);
  uint64_t id = new_id();
  return (uint64_t)(hashtbli2_add_atpos(&arrs, pos, l, r, (void*)id));
}

static uint64_t mk_tpbase(uint32_t no) {
  while (bases.len <= no)
    vector_resize(&bases, bases.len << 1);
  if (bases.data[no]) return (int64_t)(bases.data[no]);
  bases.data[no] = (void *)(new_id ());
  return (int64_t)(bases.data[no]);
}

static trm_p mk_db(uint32_t vno) {
  if (vno > 255 || vno < 0) {
    printf("mk_db called with %i!!!\nproceeding with incorrect DB number!!\n", vno);
    vno = 0;
    fflush(stdout);
  }
  return dbs[vno];
}

static trm_p mk_prim(uint32_t no) {
  while (prims.len <= no)
    vector_resize(&prims, prims.len << 1);
  if (prims.data[no]) return prims.data[no];
  prims.data[no] = add_tm_no(PRIM, no, NULL);
  return prims.data[no];
}

static trm_p mk_tmh(uint32_t no) {
  while (tmhs.len <= no)
    vector_resize(&tmhs, prims.len << 1);
  if (tmhs.data[no]) return tmhs.data[no];
  tmhs.data[no] = add_tm_no(TMH, no, NULL);
  return tmhs.data[no];
}

#include <caml/alloc.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/custom.h>

#define Tm_val(i)     (&tm[Int_val(i) >> 16][Int_val(i) & 0xFFFF])
static value Val_tm(trm_p p) {return Val_int((p->y << 16) | p->x);}

void c_utm_init(value unit) {
  CAMLparam1(unit);
  init_unique_terms();
  CAMLreturn0;
}

value c_utm_mk_tpbase(value n) {
  CAMLparam1(n);
  CAMLreturn(Val_int(mk_tpbase(Int_val(n))));
}

value c_utm_mk_tparr(value l, value r) {
  CAMLparam2(l,r);
  CAMLreturn(Val_int(mk_tparr(Int_val(l), Int_val(r))));
}


value c_utm_mk_db(value n) {
  CAMLparam1(n);
  CAMLreturn(Val_tm(mk_db(Int_val(n))));
}

value c_utm_mk_tmh(value n) {
  CAMLparam1(n);
  CAMLreturn(Val_tm(mk_tmh(Int_val(n))));
}

value c_utm_mk_prim(value n) {
  CAMLparam1(n);
  CAMLreturn(Val_tm(mk_prim(Int_val(n))));
}

value c_utm_mk_ap(value l, value r) {
  CAMLparam2(l,r);
  CAMLreturn(Val_tm(mk_ap(Tm_val(l), Tm_val(r))));
}

value c_utm_mk_imp(value l, value r) {
  CAMLparam2(l,r);
  CAMLreturn(Val_tm(mk_imp(Tm_val(l), Tm_val(r))));
}

value c_utm_mk_lam(value n, value r) {
  CAMLparam2(n,r);
  CAMLreturn(Val_tm(mk_lam(Int_val(n), Tm_val(r))));
}

value c_utm_mk_all(value n, value r) {
  CAMLparam2(n,r);
  CAMLreturn(Val_tm(mk_all(Int_val(n), Tm_val(r))));
}

value c_utm_mk_ex(value n, value r) {
  CAMLparam2(n,r);
  CAMLreturn(Val_tm(mk_ex(Int_val(n), Tm_val(r))));
}

value c_utm_mk_eq(value n, value l, value r) {
  CAMLparam3(n,l,r);
  CAMLreturn(Val_tm(mk_eq(Int_val(n), Tm_val(l), Tm_val(r))));
}

void c_utm_hash_clear(value unit) {
  CAMLparam1(unit);
  vector_clear(&prims);
  vector_clear(&tmhs);
  vector_clear(&bases);
  hashtbli2_clear(&imps);
  hashtbli2_clear(&aps);
  hashtbli2_clear(&lams);
  hashtbli2_clear(&alls);
  hashtbli2_clear(&exs);
  hashtbli3_clear(&eqs);
  hashtbli2_clear(&arrs);
  tm_id_clear();
  CAMLreturn0;
}
