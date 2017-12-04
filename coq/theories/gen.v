From mathcomp Require Import all_ssreflect.
Require Import String.
Require Import Ascii.

Require Import htmlescape.listutils.
Require Import htmlescape.assoc.
Require Import htmlescape.ssrstr.
Require Import htmlescape.spec.
Require Import htmlescape.imp.

Require Import codegen.codegen.

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

Terminate Monomorphization cmpestrc_ubyte_eqany_ppol_lsig_bitmask.
Terminate Monomorphization cmpestrm_ubyte_eqany_ppol_lsig_bitmask.
Terminate Monomorphization lo64_of_m128.

Monomorphization trec_html_escape.
Monomorphization sse_html_escape.
Monomorphization sse_html_escape2.

GenCFile "gen/esc.c"
  _trec_html_escape _sse_html_escape
  _sse_html_escape2_dense
  _sse_html_escape2_aligned
  _sse_html_escape2.
