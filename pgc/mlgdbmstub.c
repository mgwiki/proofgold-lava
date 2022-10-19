#include <string.h>
#include <caml/alloc.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/custom.h>
#include <caml/fail.h>
#include <caml/intext.h>
#include <gdbm.h>

#define Gdbm_val(v) (*((GDBM_FILE *)Data_custom_val(v)))

void gdbm_finalize(value db) {
  gdbm_close(Gdbm_val(db));
}

static struct custom_operations gdbm_ops = {
  (char*)"gdbm",
  gdbm_finalize,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default,
  custom_compare_ext_default
};

static value alloc_gdbm() {
  return (alloc_custom(&gdbm_ops, sizeof(GDBM_FILE), 0, 1));
}

value c_gdbm_open(value fname) {
  CAMLparam1(fname);
  GDBM_FILE db = gdbm_open(Bytes_val(fname),0,GDBM_WRCREAT,0666,NULL);
  if (!db)
    caml_invalid_argument("c_gdbm_open: cannot open/create db file!");
  CAMLlocal1(r);
  r=alloc_gdbm();
  Gdbm_val(r) = db;
  CAMLreturn(r);
}

value c_gdbm_exists(value db, value k) {
  CAMLparam2(db,k);
  CAMLlocal1(r);
  datum kk = {.dptr=Bytes_val(k), .dsize=caml_string_length(k) };
  CAMLreturn (Val_bool(gdbm_exists(Gdbm_val(db), kk)));
}

value c_gdbm_delete(value db, value k) {
  CAMLparam2(db,k);
  datum kk = {.dptr=Bytes_val(k), .dsize=caml_string_length(k) };
  gdbm_delete(Gdbm_val(db), kk);
  CAMLreturn(Val_unit);
}

value c_gdbm_replace(value db, value k, value v) {
  CAMLparam3(db,k,v);
  datum kk = {.dptr=Bytes_val(k), .dsize=caml_string_length(k) };
  datum vv = {.dptr=Bytes_val(v), .dsize=caml_string_length(v) };
  if (gdbm_store(Gdbm_val(db), kk, vv, GDBM_REPLACE))
    caml_invalid_argument("c_gdbm_replace: store failed");
  CAMLreturn(Val_unit);
}

value c_gdbm_fetch(value db, value k) {
  CAMLparam2(db,k);
  datum rr, kk = {.dptr=Bytes_val(k), .dsize=caml_string_length(k) };
  rr = gdbm_fetch(Gdbm_val(db), kk);
  if (!rr.dptr)
    caml_raise_not_found();
  CAMLlocal1(r);
  r = caml_alloc_string(rr.dsize);
  memcpy (Bytes_val(r), rr.dptr, rr.dsize);
  free(rr.dptr);
  CAMLreturn(r);
}

value c_gdbm_fetch_opt(value db, value k) {
  CAMLparam2(db,k);
  datum rr, kk = {.dptr=Bytes_val(k), .dsize=caml_string_length(k) };
  rr = gdbm_fetch(Gdbm_val(db), kk);
  if (!rr.dptr) CAMLreturn(Val_unit);
  CAMLlocal2(r,v);
  v=caml_alloc_string(rr.dsize);
  memcpy (Bytes_val(v), rr.dptr, rr.dsize);
  free(rr.dptr);
  r=caml_alloc(1, 0);
  Field(r, 0) = v;
  CAMLreturn(r);
}

value c_gdbm_fetch_unmarshal(value db, value k) {
  CAMLparam2(db,k);
  datum rr, kk = {.dptr=Bytes_val(k), .dsize=caml_string_length(k) };
  rr = gdbm_fetch(Gdbm_val(db), kk);
  if (!rr.dptr)
    caml_raise_not_found();
  CAMLlocal1(r);
  r=caml_input_value_from_block(rr.dptr,rr.dsize);
  free(rr.dptr);
  CAMLreturn(r);
}

value c_gdbm_fetch_unmarshal_opt(value db, value k) {
  CAMLparam2(db,k);
  datum rr, kk = {.dptr=Bytes_val(k), .dsize=caml_string_length(k) };
  rr = gdbm_fetch(Gdbm_val(db), kk);
  if (!rr.dptr) CAMLreturn(Val_unit);
  CAMLlocal2(r,v);
  v=caml_input_value_from_block(rr.dptr,rr.dsize);
  free(rr.dptr);
  r=caml_alloc(1, 0);
  Field(r, 0) = v;
  CAMLreturn(r);
}

value c_gdbm_sync(value db) {
  CAMLparam1(db);
  gdbm_sync(Gdbm_val(db));
  CAMLreturn(Val_unit);
}

value c_gdbm_reorganize(value db) {
  CAMLparam1(db);
  gdbm_reorganize(Gdbm_val(db));
  CAMLreturn(Val_unit);
}

value c_gdbm_firstkey(value db) {
  CAMLparam1(db);
  datum kk = gdbm_firstkey(Gdbm_val(db));
  if (!kk.dptr)
    caml_raise_not_found();
  CAMLlocal1(r);
  r = caml_alloc_string(kk.dsize);
  memcpy (Bytes_val(r), kk.dptr, kk.dsize);
  free(kk.dptr);
  CAMLreturn(r);
}

value c_gdbm_nextkey(value db, value k) {
  CAMLparam2(db, k);
  datum kk1 = {.dptr=Bytes_val(k), .dsize=caml_string_length(k) };
  datum kk2 = gdbm_nextkey(Gdbm_val(db), kk1);
  if (!kk2.dptr)
    caml_raise_not_found();
  CAMLlocal1(r);
  r = caml_alloc_string(kk2.dsize);
  memcpy (Bytes_val(r), kk2.dptr, kk2.dsize);
  free(kk2.dptr);
  CAMLreturn(r);
}
