#include <stdio.h>
#include <string.h>
#include <stdbool.h>
#include <caml/alloc.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/custom.h>
#include <caml/fail.h>
#include <caml/intext.h>
#include <arpa/inet.h>

#define visible __attribute__((visibility("default")))

visible value c_int32_bebits(value x){
  CAMLparam1(x);
  CAMLlocal1(r);
  r = caml_alloc_string(4);
  *((uint32_t*)(Bytes_val(r))) = htonl((uint32_t)(Int32_val(x)));
  CAMLreturn(r);
}

visible value c_int32pow5_bebits(value x){
  CAMLparam1(x);
  CAMLlocal1(r);
  r = caml_alloc_string(20);
  ((uint32_t*)(Bytes_val(r)))[0] = htonl((uint32_t)(Int32_val(Field(x, 0))));
  ((uint32_t*)(Bytes_val(r)))[1] = htonl((uint32_t)(Int32_val(Field(x, 1))));
  ((uint32_t*)(Bytes_val(r)))[2] = htonl((uint32_t)(Int32_val(Field(x, 2))));
  ((uint32_t*)(Bytes_val(r)))[3] = htonl((uint32_t)(Int32_val(Field(x, 3))));
  ((uint32_t*)(Bytes_val(r)))[4] = htonl((uint32_t)(Int32_val(Field(x, 4))));
  CAMLreturn(r);
}

visible value c_int32pow8_bebits(value x){
  CAMLparam1(x);
  CAMLlocal1(r);
  r = caml_alloc_string(32);
  ((uint32_t*)(Bytes_val(r)))[0] = htonl((uint32_t)(Int32_val(Field(x, 0))));
  ((uint32_t*)(Bytes_val(r)))[1] = htonl((uint32_t)(Int32_val(Field(x, 1))));
  ((uint32_t*)(Bytes_val(r)))[2] = htonl((uint32_t)(Int32_val(Field(x, 2))));
  ((uint32_t*)(Bytes_val(r)))[3] = htonl((uint32_t)(Int32_val(Field(x, 3))));
  ((uint32_t*)(Bytes_val(r)))[4] = htonl((uint32_t)(Int32_val(Field(x, 4))));
  ((uint32_t*)(Bytes_val(r)))[5] = htonl((uint32_t)(Int32_val(Field(x, 5))));
  ((uint32_t*)(Bytes_val(r)))[6] = htonl((uint32_t)(Int32_val(Field(x, 6))));
  ((uint32_t*)(Bytes_val(r)))[7] = htonl((uint32_t)(Int32_val(Field(x, 7))));
  CAMLreturn(r);
}

visible value c_bebits_int32(value x){
  CAMLparam1(x);
  if (caml_string_length(x) != 4)
    caml_invalid_argument("c_bebits_int32: not a 4 byte string!");
  CAMLlocal1(r);
  r = caml_copy_int32((int32_t)(ntohl(*((uint32_t*)(Bytes_val(x))))));
  CAMLreturn(r);
}

visible value c_bebits_int32pow5(value x){
  CAMLparam1(x);
  if (caml_string_length(x) != 20)
    caml_invalid_argument("c_bebits_int32pow8: not a 32 byte string!");
  CAMLlocal5(a,b,c,d,e);
  a=caml_copy_int32((int32_t)(ntohl(((uint32_t*)(Bytes_val(x)))[0])));
  b=caml_copy_int32((int32_t)(ntohl(((uint32_t*)(Bytes_val(x)))[1])));
  c=caml_copy_int32((int32_t)(ntohl(((uint32_t*)(Bytes_val(x)))[2])));
  d=caml_copy_int32((int32_t)(ntohl(((uint32_t*)(Bytes_val(x)))[3])));
  e=caml_copy_int32((int32_t)(ntohl(((uint32_t*)(Bytes_val(x)))[4])));
  CAMLlocal1(r);
  r = caml_alloc_tuple(5);
  Field(r, 0) = a;
  Field(r, 1) = b;
  Field(r, 2) = c;
  Field(r, 3) = d;
  Field(r, 4) = e;
  CAMLreturn(r);
}

visible value c_bebits_int32pow8(value x){
  CAMLparam1(x);
  if (caml_string_length(x) != 32)
    caml_invalid_argument("c_bebits_int32pow8: not a 32 byte string!");
  CAMLlocal4(a,b,c,d);
  a=caml_copy_int32((int32_t)(ntohl(((uint32_t*)(Bytes_val(x)))[0])));
  b=caml_copy_int32((int32_t)(ntohl(((uint32_t*)(Bytes_val(x)))[1])));
  c=caml_copy_int32((int32_t)(ntohl(((uint32_t*)(Bytes_val(x)))[2])));
  d=caml_copy_int32((int32_t)(ntohl(((uint32_t*)(Bytes_val(x)))[3])));
  CAMLlocal4(e,f,g,h);
  e=caml_copy_int32((int32_t)(ntohl(((uint32_t*)(Bytes_val(x)))[4])));
  f=caml_copy_int32((int32_t)(ntohl(((uint32_t*)(Bytes_val(x)))[5])));
  g=caml_copy_int32((int32_t)(ntohl(((uint32_t*)(Bytes_val(x)))[6])));
  h=caml_copy_int32((int32_t)(ntohl(((uint32_t*)(Bytes_val(x)))[7])));
  CAMLlocal1(r);
  r = caml_alloc_tuple(8);
  Field(r, 0) = a;
  Field(r, 1) = b;
  Field(r, 2) = c;
  Field(r, 3) = d;
  Field(r, 4) = e;
  Field(r, 5) = f;
  Field(r, 6) = g;
  Field(r, 7) = h;
  CAMLreturn(r);
}


static inline char i_to_ascii(uint8_t i) {
  return (((i < 10) ? '0' : 'W') + i); // W is the ascii code of 'a' minus 10
}

visible value c_bebits_hexstring(value x){
  CAMLparam1(x);
  const mlsize_t len = caml_string_length(x);
  CAMLlocal1(r);
  r = caml_alloc_string(2 * len);
  for (uint32_t i = 0; i < len; ++i) {
    const uint8_t xi = Byte_u(x, i);
    const uint8_t c2 = xi        & 0x0F;
    const uint8_t c1 = (xi >> 4) & 0x0F;
    Byte(r, 2 * i  ) = i_to_ascii(c1);
    Byte(r, 2 * i+1) = i_to_ascii(c2);
  }
  CAMLreturn(r);
}

static const char hextable[] = {
  -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
  -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
  -1,-1, 0,1,2,3,4,5,6,7,8,9,-1,-1,-1,-1,-1,-1,-1,10,11,12,13,14,15,-1,
  -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
  -1,-1,10,11,12,13,14,15,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
  -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
  -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
  -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
  -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
  -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
  -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1
};

/* This conversion seems less efficient in practice
   if(a[i] < 48) exit(0); else
   if(a[i] < 58) val += (a[i]-48)*(1<<(4*(len-1-i))); else
   if(a[i] < 65) exit(0); else
   if(a[i] < 71) val += (a[i]-55)*(1<<(4*(len-1-i))); else
   if(a[i] < 97) exit(0); else
   if(a[i] < 103) val += (a[i]-87)*(1<<(4*(len-1-i))); else
   exit(0); */

// Could also provide a 'hexsubstring_bebits'
// Ignores last character is length is odd.
visible value c_hexstring_bebits(value x){
  CAMLparam1(x);
  const mlsize_t len = caml_string_length(x);
  const mlsize_t nlen = len >> 1;
  CAMLlocal1(r);
  r = caml_alloc_string(nlen);
  for (uint32_t i = 0; i < nlen; ++i) {
    const int8_t b1 = hextable[Byte_u(x, 2 * i)];
    const int8_t b2 = hextable[Byte_u(x, 2 * i + 1)];
    if (b1 < 0 || b2 < 0)
      caml_invalid_argument("c_hexstring_bebits: not a hex string!");
    Byte_u(r, i) = b1 << 4 | b2;
  }
  CAMLreturn(r);
}

visible value c_bebits_rev(value x){
  CAMLparam1(x);
  const mlsize_t len = caml_string_length(x);
  CAMLlocal1(r);
  r = caml_alloc_string(len);
  for (uint32_t i = 0; i < len; ++i)
    Byte_u(r, i) = Byte_u(x, len - i - 1);
  CAMLreturn(r);
}


#define fst(a) Field(a, 0)
#define snd(a) Field(a, 1)

#define set_nth_bit(c,p) (c[(p) >> 3] |= (1 << (7 - (p) % 8)))
#define clear_nth_bit(c,p) (c[(p) >> 3] &= ~ (1 << (7 - (p) % 8)))
#define get_nth_bit(c,p) ((bool)(c[(p) >> 3] & (1 << (7 - (p) % 8))))

visible value c_bebits_get_bit(value s, value i){
  CAMLparam2(s, i);
  CAMLreturn(Val_bool(get_nth_bit(Bytes_val(s), Int_val(i))));
}

visible void c_bebits_set_bit(value s, value i, value v){
  CAMLparam3(s, i, v);
  if (Bool_val(v))
    set_nth_bit(Bytes_val(s), Int_val(i));
  else
    clear_nth_bit(Bytes_val(s), Int_val(i));
  CAMLreturn0;
}

visible void c_bools_blit_bebits(value l, value r, value st, value incr){
  CAMLparam4(l,r,st,incr);
  for (int32_t pos = Int_val(st); l != Val_emptylist; pos += Int_val(incr), l = Field(l, 1))
    if (Bool_val(Field(l, 0)))
      set_nth_bit(Bytes_val(r), pos);
    else
      clear_nth_bit(Bytes_val(r), pos);
  CAMLreturn0;
}

// en is the first invalid position
visible value c_bebits_to_bools(value b, value st, value en, value step){
  CAMLparam4(b,st,en,step);
  CAMLlocal2(r,t);
  r = Val_emptylist;
  for (int32_t pos = Int_val(st); pos != Int_val(en); pos += Int_val(step)) {
    t = caml_alloc_small(2, Tag_cons);
    fst(t) = Val_bool(get_nth_bit(Bytes_val(b), pos));
    snd(t) = r;
    r = t;
  }
  CAMLreturn(r);
}

visible void c_bebits_zero_bits(value s, value st, value len){
  CAMLparam3(s,st,len);
  for (int32_t pos = Int_val(st); pos < Int_val(st) + Int_val(len); ++pos)
    clear_nth_bit(Bytes_val(s), pos);
  CAMLreturn0;
}

visible value c_bebits_bit_eq(value s1, value st1, value s2, value st2, value len) {
  CAMLparam5(s1,st1,s2,st2,len);
  for (int i = 0; i < len; ++i) {
    const int b1 = get_nth_bit(Bytes_val(s1),i+Int_val(st1));
    const int b2 = get_nth_bit(Bytes_val(s2),i+Int_val(st2));
    if (!b1 != !b2)
      return Val_false;
  }
  return Val_true;
}

// Assumes the string is longer than an int
visible value c_bebits_hash(value s) {
  CAMLparam1(s);
  CAMLreturn(Val_long(*((unsigned long*)(Bytes_val(s)))));
}

visible value c_bebits_get_byte(value x, value i){
  CAMLparam2(x,i);
  const uint8_t t = Bytes_val(x)[Int_val(i)];
  CAMLreturn(Val_int(t));
}

visible void c_bebits_set_byte(value x, value i, value v){
  CAMLparam3(x,i,v);
  const uint8_t t = Int_val(v);
  Bytes_val(x)[Int_val(i)] = t;
  CAMLreturn0;
}
