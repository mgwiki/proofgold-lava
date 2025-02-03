#include <stdio.h>
#include <ctype.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <caml/callback.h>
#include <caml/alloc.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/custom.h>
#include <caml/fail.h>


typedef struct { uint64_t d[4]; } int64p4;
typedef struct { uint32_t d[8]; } int32p8;

static struct custom_operations s2n_ops = {
  (char*)"s2n",
  custom_finalize_default,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default,
  custom_compare_ext_default
};

#define S2n_val8(v) ((int32p8 *)Data_custom_val(v))
#define S2n_valp(v) ((uint64_t *)Data_custom_val(v))
static value alloc_s2n() {
  return (caml_alloc_custom(&s2n_ops, sizeof(int64p4), 0, 1));
}

value c_s2n_to_le_string(value x){
  CAMLparam1(x);
  CAMLlocal1(r);
  r = caml_alloc_string(32);
  memcpy(Bytes_val(r), S2n_valp(x), 32);
  CAMLreturn(r);
}

// Needs to work with shorter strings
value c_s2n_of_le_string(value x){
  CAMLparam1(x);
  CAMLlocal1(r);
  r = alloc_s2n();
  memset(S2n_valp(r), 0, 32);
  memcpy(S2n_valp(r), Bytes_val(x), caml_string_length(x));
  CAMLreturn(r);
}

value c_s2n_to_int32p8(value s){
  CAMLparam1(s);
  CAMLlocal4(a,b,c,d);
  a = caml_copy_int32(S2n_val8(s)->d[7]);
  b = caml_copy_int32(S2n_val8(s)->d[6]);
  c = caml_copy_int32(S2n_val8(s)->d[5]);
  d = caml_copy_int32(S2n_val8(s)->d[4]);
  CAMLlocal4(e,f,g,h);
  e = caml_copy_int32(S2n_val8(s)->d[3]);
  f = caml_copy_int32(S2n_val8(s)->d[2]);
  g = caml_copy_int32(S2n_val8(s)->d[1]);
  h = caml_copy_int32(S2n_val8(s)->d[0]);
  CAMLlocal1 (r);
  r = caml_alloc_tuple(8);
  Field(r, 0) = a;
  Field(r, 1) = b;
  Field(r, 2) = c;
  Field(r, 3) = d;
  Field(r, 4) = e;
  Field(r, 5) = f;
  Field(r, 6) = g;
  Field(r, 7) = h;
  CAMLreturn (r);

}

value c_s2n_of_int32p8(value ox){
  CAMLparam1(ox);
  CAMLlocal1(o);
  o = alloc_s2n();
  S2n_val8(o)->d[0] = Int32_val(Field(ox, 7));
  S2n_val8(o)->d[1] = Int32_val(Field(ox, 6));
  S2n_val8(o)->d[2] = Int32_val(Field(ox, 5));
  S2n_val8(o)->d[3] = Int32_val(Field(ox, 4));
  S2n_val8(o)->d[4] = Int32_val(Field(ox, 3));
  S2n_val8(o)->d[5] = Int32_val(Field(ox, 2));
  S2n_val8(o)->d[6] = Int32_val(Field(ox, 1));
  S2n_val8(o)->d[7] = Int32_val(Field(ox, 0));
  CAMLreturn(o);
}

value c_s2n_of_int(value ox){
  CAMLparam1(ox);
  CAMLlocal1(o);
  o = alloc_s2n();
  *S2n_valp(o) = Long_val(ox);
  CAMLreturn(o);
}

extern uint64_t bignum_iszero (uint64_t k, uint64_t *x);
value c_s2n_iszero(value ox) {
  CAMLparam1 (ox);
  CAMLreturn (Val_bool(bignum_iszero(4, S2n_valp(ox))));
}

extern uint64_t bignum_even (uint64_t k, uint64_t *x);
value c_s2n_iseven(value ox) {
  CAMLparam1 (ox);
  CAMLreturn (Val_bool(bignum_even(4, S2n_valp(ox))));
}

extern uint64_t bignum_eq(uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);
value c_s2n_eq(value x, value y) {
  CAMLparam2 (x, y);
  CAMLreturn (Val_bool(bignum_eq(4, S2n_valp(x), 4, S2n_valp(y))));
}

extern uint64_t bignum_gt(uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);
value c_s2n_gt(value x, value y) {
  CAMLparam2 (x, y);
  CAMLreturn (Val_bool(bignum_gt(4, S2n_valp(x), 4, S2n_valp(y))));
}

extern void bignum_modinv (uint64_t k, uint64_t *z, uint64_t *a, uint64_t *b, uint64_t *t);

static uint64_t _n[] = {0xBFD25E8CD0364141, 0xBAAEDCE6AF48A03B, 0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF};
static uint64_t _p[] = {0xFFFFFFFEFFFFFC2F, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF};

value c_s2n_modinv_n(value ox) {
  CAMLparam1 (ox);
  uint64_t t[12];
  CAMLlocal1(oz);
  oz = alloc_s2n();
  bignum_modinv(4, S2n_valp(oz), S2n_valp(ox), _n, t);
  CAMLreturn (oz);
}

value c_s2n_modinv_p(value ox) {
  CAMLparam1 (ox);
  uint64_t t[12];
  CAMLlocal1(oz);
  oz = alloc_s2n();
  bignum_modinv(4, S2n_valp(oz), S2n_valp(ox), _p, t);
  CAMLreturn (oz);
}
