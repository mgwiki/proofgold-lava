CFLAGS=-O3 -fPIC # -pg -g -Wcast-align=strict
#MKLIBFLAGS=-custom -ocamloptflags -p
OFLAGS=-O3 # -p
# CFLAGS+= -DHAVE_S2N
# CFLAGS+= -DHAVE_S2N_ALT
OCAMLOPT=ocamlopt
OCAMLC=ocamlc

OINCL=-I bin # -I +zarith
CINCL=-I secp256k1 -I bitcoin -I s2n
CDEFS=-DHAVE_CONFIG_H # -DVALGRIND -DVERIFY
CWARN=-pedantic -Wno-long-long -Wno-overlength-strings -Wno-unused-function
CFLAGS+=$(CINCL) $(CDEFS) $(CWARN)
CHIDE=-fvisibility=hidden

all: bin/pgc.cmxa

S2N=$(wildcard s2n/*.S)
S2NB=$(patsubst s2n/%,bin/%,$(S2N))
S2NO=$(patsubst %.S,%.o,$(S2NB))
BINOBJ=$(addprefix bin/,bebitsstub.o mlgdbmstub.o hashbtcstub.o s2nstub.o secp256k1btcstub.o utmstub.o bebits.cmo bebits.cmx be160.cmi be160.cmo be160.cmx be256.cmi be256.cmo be256.cmx mlgdbm.cmo mlgdbm.cmx hashbtc.cmo hashbtc.cmx s2n.cmo s2n.cmx secp256k1btc.cmo secp256k1btc.cmx bitlist.cmi bitlist.cmo bitlist.cmx utm.cmo utm.cmx)

bin/pgc.cmxa: Makefile bin $(S2NO) $(BINOBJ)
	ocamlmklib $(MKLIBFLAGS) $(OINCL) -o bin/pgc -cclib -L/usr/lib/x86_64-linux-gnu/ -Lbin -L. -lgdbm $(filter-out %.cmi bin Makefile,$^)

test_gdbm: bin/pgc.cmxa bin/test_gdbm.cmx
	$(OCAMLOPT) $(OFLAGS) -I bin $^ -o bin/$@
	@ln -sf bin/$@

test_sha256: bin/pgc.cmxa bin/test_sha256.cmx
	$(OCAMLOPT) $(OFLAGS) -I bin $^ -o bin/$@
	@ln -sf bin/$@

test_bitlist: bin/pgc.cmxa bin/test_bitlist.cmx
	$(OCAMLOPT) $(OFLAGS) -I bin $^ -o bin/$@
	@ln -sf bin/$@

clean:
	rm -f bin/* *.o *.cmx *.cmi *.cma *.cmo *.cmxa *.a *.so *~ *annot gmon.out ocamlprof.dump test test_gdbm test_sha256 test_bitlist

# GENERAL

bin/%.cmx: %.ml Makefile
	$(OCAMLOPT) $(OFLAGS) $(OINCL) -c $< -o $@

bin/%.cmo: %.ml Makefile
	$(OCAMLC) $(OINCL) -c $< -o $@

bin/%.cmi: %.mli Makefile
	$(OCAMLC) $(OINCL) -c $< -o $@

bin/%.o: %.c Makefile
	$(OCAMLC) -ccopt "$(CFLAGS) $(CHIDE)" -c $<
	@mv *.o bin

bin/%.o: s2n/%.S Makefile
	cpp $(CFLAGS) $< | as -o $@ -

bin:
	@mkdir -p bin
