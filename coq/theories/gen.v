From mathcomp Require Import all_ssreflect.
Require Import String.
Require Import Ascii.

Require Import htmlescape.listutils.
Require Import htmlescape.assoc.
Require Import htmlescape.ssrstr.
Require Import htmlescape.spec.
Require Import htmlescape.imp.

Require Import Monomorph.monomorph.

Terminate Monomorphization html_escape_byte_table.
Terminate Monomorphization cmpestri_ubyte_eqany_ppol_lsig.
Terminate Monomorphization chars_to_escape.
Terminate Monomorphization m128_of_bptr.
Terminate Monomorphization bptradd.
Terminate Monomorphization bptrget.
Terminate Monomorphization bufaddmem.
Terminate Monomorphization addn.
Terminate Monomorphization subn.
Terminate Monomorphization leq.

Monomorphization trec_html_escape.
Monomorphization sse_html_escape.
GenCFile "gen/esc.c" _trec_html_escape _sse_html_escape.
