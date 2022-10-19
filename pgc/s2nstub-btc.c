#include <stdio.h>
#include <ctype.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <caml/alloc.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/custom.h>
#include <caml/fail.h>
#include <arpa/inet.h>

#include <time.h> // Only needed to avoid warning
#include "secp256k1.h"
#include "scalar_impl.h"
#include "hash_impl.h"
#include "field_impl.h"
#include "scratch_impl.h"

static struct custom_operations s2n_ops = {
  (char*)"s2n",
  custom_finalize_default,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default,
  custom_compare_ext_default
};

#define S2n_val(v) ((secp256k1_fe *)Data_custom_val(v))
static value alloc_s2n() {
  return (alloc_custom(&s2n_ops, sizeof(secp256k1_fe), 0, 1));
}

value c_s2n_iseven(value x) {
  CAMLparam1 (x);
  CAMLreturn(Val_bool(!(secp256k1_fe_is_odd(S2n_val(x)))));
}

value c_s2n_iszero(value x) {
  CAMLparam1 (x);
  CAMLreturn(Val_bool(secp256k1_fe_normalizes_to_zero(S2n_val(x))));
}

value c_s2n_eq(value x,value y) {
  CAMLparam2 (x,y);
  CAMLreturn(Val_bool(secp256k1_fe_equal(S2n_val(x),S2n_val(y))));
}

value c_s2n_gt(value x,value y) {
  CAMLparam2 (x,y);
  CAMLreturn(Val_bool(secp256k1_fe_cmp_var(S2n_val(x),S2n_val(y))==1));
}

value c_s2n_of_int(value i){
  CAMLparam1(i);
  CAMLlocal1(o);
  o = alloc_s2n();
  secp256k1_fe_set_int(S2n_val(o), Long_val(i));
  CAMLreturn(o);
}

value c_s2n_to_int32p8(value s){
  CAMLparam1(s);
  unsigned char xxx[32];
  secp256k1_fe_get_b32(xxx, S2n_val(s));
  secp256k1_scalar xx;
  secp256k1_scalar_set_b32(&xx, xxx, NULL);
  CAMLlocal4(a,b,c,d);
  a = caml_copy_int32(((int32_t*)xx.d)[7]);
  b = caml_copy_int32(((int32_t*)xx.d)[6]);
  c = caml_copy_int32(((int32_t*)xx.d)[5]);
  d = caml_copy_int32(((int32_t*)xx.d)[4]);
  CAMLlocal4(e,f,g,h);
  e = caml_copy_int32(((int32_t*)xx.d)[3]);
  f = caml_copy_int32(((int32_t*)xx.d)[2]);
  g = caml_copy_int32(((int32_t*)xx.d)[1]);
  h = caml_copy_int32(((int32_t*)xx.d)[0]);
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
  secp256k1_scalar xx;
  ((uint32_t*)(xx.d))[0] = Int32_val(Field(ox, 7));
  ((uint32_t*)(xx.d))[1] = Int32_val(Field(ox, 6));
  ((uint32_t*)(xx.d))[2] = Int32_val(Field(ox, 5));
  ((uint32_t*)(xx.d))[3] = Int32_val(Field(ox, 4));
  ((uint32_t*)(xx.d))[4] = Int32_val(Field(ox, 3));
  ((uint32_t*)(xx.d))[5] = Int32_val(Field(ox, 2));
  ((uint32_t*)(xx.d))[6] = Int32_val(Field(ox, 1));
  ((uint32_t*)(xx.d))[7] = Int32_val(Field(ox, 0));
  unsigned char xxx[32];
  secp256k1_scalar_get_b32(xxx, &xx);
  CAMLlocal1(o);
  o = alloc_s2n();
  secp256k1_fe_set_b32(S2n_val(o), xxx);
  CAMLreturn(o);
}

value c_s2n_to_le_string(value x){
  CAMLparam1(x);
  CAMLlocal1(r);
  r = caml_alloc_string(32);
  unsigned char tmp;
  secp256k1_fe_get_b32((unsigned char*)(Bytes_val(r)), S2n_val(x));
  for (int i = 0; i < 16; ++i) {
    tmp=Byte_u(r, i); Byte_u(r, i) = Byte_u(r, 31 - i); Byte_u(r, 31 - i) = tmp;
  }
  CAMLreturn(r);
}

value c_s2n_of_le_string(value x){
  CAMLparam1(x);
  CAMLlocal1(r);
  r = alloc_s2n();
  unsigned char xxx[32];
  memset(xxx, 0, 32);
  memcpy(xxx, Bytes_val(x), caml_string_length(x));
  unsigned char tmp;
  for (int i = 0; i < 16; ++i) {
    tmp=xxx[i]; xxx[i]=xxx[31 - i]; xxx[31 - i]=tmp;
  }
  secp256k1_fe_set_b32(S2n_val(r), xxx);
  CAMLreturn(r);
}

value c_s2n_modinv_n(value x) {
  CAMLparam1 (x);
  unsigned char xxx[32];
  secp256k1_fe_get_b32(xxx, S2n_val(x));
  secp256k1_scalar xx1, xx2;
  secp256k1_scalar_set_b32(&xx1, xxx, NULL);
  secp256k1_scalar_inverse(&xx2, &xx1);
  secp256k1_scalar_get_b32(xxx, &xx2);
  CAMLlocal1(r);
  r = alloc_s2n();
  secp256k1_fe_set_b32(S2n_val(r), xxx);
  CAMLreturn(r);
}

value c_s2n_modinv_p(value x) {
  CAMLparam1 (x);
  CAMLlocal1(r);
  r = alloc_s2n();
  secp256k1_fe_inv(S2n_val(r), S2n_val(x));
  secp256k1_fe_normalize(S2n_val(r));
  CAMLreturn(r);
}
