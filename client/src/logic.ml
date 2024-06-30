(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2016 The Qeditas developers *)
(* Copyright (c) 2017-2018 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

(* This code defines several data types used in a formal proof system. *)

open Hash (* This line opens the Hash module, which provides functions for working with hash values. *)

(* Type definition for "stp", which represents a type in the proof system. *)
type stp =
  | Base of int (* Base type constructor, which takes an integer as an argument. *)
  | TpArr of stp * stp (* Type arrow constructor, which takes two types as arguments. *)
  | Prop (* Proposition type constructor, which represents a logical proposition. *)

(* Type definition for "trm", which represents a term in the proof system. *)
type trm =
  | DB of int (* Database constant constructor, which takes an integer as an argument. *)
  | TmH of hashval (* Hash value constructor, which takes a hash value as an argument. *)
  | Prim of int (* Primitive constant constructor, which takes an integer as an argument. *)
  | Ap of trm * trm (* Application constructor, which takes two terms as arguments. *)
  | Lam of stp * trm (* Lambda abstraction constructor, which takes a type and a term as arguments. *)
  | Imp of trm * trm (* Implication constructor, which takes two terms as arguments. *)
  | All of stp * trm (* Universal quantification constructor, which takes a type and a term as arguments. *)
  | Ex of stp * trm (* Existential quantification constructor, which takes a type and a term as arguments. *)
  | Eq of stp * trm * trm (* Equality constructor, which takes a type and two terms as arguments. *)

(* Type definition for "pf", which represents a proof in the proof system. *)
type pf =
  | Known of hashval (* Known proof constructor, which takes a hash value as an argument. *)
  | Hyp of int (* Hypothesis proof constructor, which takes an integer as an argument. *)
  | PrAp of pf * pf (* Proof application constructor, which takes two proofs as arguments. *)
  | TmAp of pf * trm (* Term application constructor, which takes a proof and a term as arguments. *)
  | PrLa of trm * pf (* Proof lambda abstraction constructor, which takes a term and a proof as arguments. *)
  | TmLa of stp * pf (* Term lambda abstraction constructor, which takes a type and a proof as arguments. *)
  | Ext of stp * stp (* Proof extension constructor, which takes two types as arguments. *)

(* Type definition for "gsign", which represents a global signature in the proof system. *)
type gsign = ((hashval * stp) * trm option) list * (hashval * trm) list

(* Type definition for "theoryitem", which represents an item in a theory specification. *)
type theoryitem =
  | Thyprim of stp (* Theory primitive constructor, which takes a type as an argument. *)
  | Thyaxiom of trm (* Theory axiom constructor, which takes a term as an argument. *)
  | Thydef of stp * trm (* Theory definition constructor, which takes a type and a term as arguments. *)

(* Type definition for "theoryspec", which represents a theory specification. *)
type theoryspec = theoryitem list

(* Type definition for "theory", which represents a theory. *)
type theory = stp list * hashval list

(* Type definition for "signaitem", which represents an item in a signature specification. *)
type signaitem =
  | Signasigna of hashval (* Signature signature constructor, which takes a hash value as an argument. *)
  | Signaparam of hashval * stp (* Signature parameter constructor, which takes a hash value and a type as arguments. *) 
  | Signadef of stp * trm (* Signature definition constructor, which takes a type and a term as arguments. *)
  | Signaknown of trm (* Signature known constructor, which takes a term as an argument. *)

(* Type definition for "signaspec", which represents a signature specification. *)
type signaspec = signaitem list

(* Type definition for "signa", which represents a signature. *)
type signa = hashval list * gsign

(* Type definition for "docitem", which represents an item in a documentation specification. *)
type docitem =
  | Docsigna of hashval (* Documentation signature constructor, which takes a hash value as an argument. *)
  | Docparam of hashval * stp (* Documentation parameter constructor, which takes a hash value and a type as arguments. *)
  | Docdef of stp * trm (* Documentation definition constructor, which takes a type and a term as arguments. *)
  | Docknown of trm (* Documentation known constructor, which takes a term as an argument. *)
  | Docpfof of trm * pf (* Documentation proof constructor, which takes a term and a proof as arguments. *)
  | Docconj of trm (* Documentation conjunction constructor, which takes a term as an argument. *)

(* Type definition for "doc", which represents a documentation specification. *)
type doc = docitem list
