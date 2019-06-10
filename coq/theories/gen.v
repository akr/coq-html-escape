From mathcomp Require Import all_ssreflect.
Require Import String.
Require Import Ascii.

Require Import htmlescape.listutils.
Require Import htmlescape.assoc.
Require Import htmlescape.ssrstr.
Require Import htmlescape.spec.
Require Import htmlescape.imp.

Require Import codegen.codegen.

CodeGen Terminate Monomorphization html_escape_byte_table.
CodeGen Terminate Monomorphization cmpestri_ubyte_eqany_ppol_lsig.
CodeGen Terminate Monomorphization chars_to_escape.
CodeGen Terminate Monomorphization m128_of_bptr.
CodeGen Terminate Monomorphization bptradd.
CodeGen Terminate Monomorphization bptrget.
CodeGen Terminate Monomorphization bufaddmem.
CodeGen Terminate Monomorphization addn.
CodeGen Terminate Monomorphization subn.
CodeGen Terminate Monomorphization leq.

CodeGen Terminate Monomorphization cmpestrc_ubyte_eqany_ppol_lsig_bitmask.
CodeGen Terminate Monomorphization cmpestrm_ubyte_eqany_ppol_lsig_bitmask.
CodeGen Terminate Monomorphization lo64_of_m128.

CodeGen Monomorphization trec_html_escape.
CodeGen Monomorphization sse_html_escape.
CodeGen Monomorphization sse_html_escape2.

CodeGen GenCFile "gen/esc.c"
  _trec_html_escape _sse_html_escape
  _sse_html_escape2_dense
  _sse_html_escape2_aligned
  _sse_html_escape2.
