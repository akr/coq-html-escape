From mathcomp Require Import all_ssreflect.
Require Import String.
Require Import Ascii.

Require Import htmlescape.natutils.
Require Import htmlescape.listutils.
Require Import htmlescape.assoc.
Require Import htmlescape.ssrstr.
Require Import htmlescape.imp.
Require Import htmlescape.htmlescape.

Require Import monadification.monadification.

Definition ret {A} (x : A) := Some x.
Definition bind {A} {B} (x' : option A) (f : A -> option B) :=
  match x' with
  | None => None
  | Some x => f x
  end.

Monadify Type option.
Monadify Return @ret.
Monadify Bind @bind.

Notation "'return' t" := (ret t) (at level 100).
Notation "x >>= y" := (bind x y)
  (at level 65, left associativity).

Definition W := 64.
Definition check x :=
  if log2 x < W then Some x else None.
Definition SM a := check a.+1.
Definition addM a b := check (a + b).
Definition mulM a b := check (a * b).

(* addn, muln and S may overflow *)
Monadify Action addn => addM.
Monadify Action muln => mulM.
Monadify Action S => SM.

Definition bptraddM ptr n :=
  let i := i_of_bptr ptr in
  let s := s_of_bptr ptr in
  if i + n <= size s then
    Some (bptradd ptr n)
  else
    None.

Definition bptrgetM ptr :=
  let i := i_of_bptr ptr in
  let s := s_of_bptr ptr in
  if i < size s then
    Some (bptrget ptr)
  else
    None.

Monadify Action bptradd => bptraddM.
Monadify Action bptrget => bptrgetM.

Definition bufaddmemM buf ptr n :=
  let i := i_of_bptr ptr in
  let s := s_of_bptr ptr in
  if i + n <= size s then
    Some (bufaddmem buf ptr n)
  else
    None.

Monadify Action bufaddmem => bufaddmemM.

Monadify Pure html_escape_byte_table.

Monadification trec_html_escape.
(*Print trec_html_escapeM.*)

Lemma i_of_html_escape_byte_ptr c : i_of_bptr (html_escape_byte_ptr c) = 0.
Proof.
  rewrite /html_escape_byte_ptr.
  by case: (assoc c html_escape_alist).
Qed.

Lemma size_s_of_html_escape_byte_ptr c :
  size (s_of_bptr (html_escape_byte_ptr c)) = html_escape_byte_len c.
Proof.
  rewrite /html_escape_byte_ptr /html_escape_byte_len.
  by case: (assoc c html_escape_alist) => [p /=|]; first rewrite size_cat /= addn1.
Qed.

Lemma trec_html_escape_success i s n buf ptr :
  ptr = bptr i s ->
  i + n <= size s -> log2 (size s) < W ->
  trec_html_escapeM buf ptr n = Some (trec_html_escape buf ptr n).
Proof.
  move=> ->.
  clear ptr.
  elim: n i buf.
    by [].
  move=> n IH i buf Hin Hs /=.
  rewrite /bind /ret.
  rewrite /bptrgetM /=.
  rewrite (_ : i < size s); last first.
    apply: (leq_trans _ Hin).
    by rewrite addnS ltnS leq_addr.
  rewrite html_escape_byte_split.
  rewrite /bufaddmemM.
  rewrite i_of_html_escape_byte_ptr add0n.
  rewrite size_s_of_html_escape_byte_ptr leqnn.
  rewrite /bptraddM /=.
  rewrite (_ : i + 1 <= size s); last first.
    apply: (leq_trans _ Hin).
    by rewrite addn1 addnS ltnS leq_addr.
  rewrite IH.
      by [].
    by rewrite /= addn1 addSnnS.
  by [].
Qed.

Monadify Pure nat_eqMixin.

(* subn must be pure because it is used for decreasing argument *)
Monadify Pure subn.

(* This monadic action makes Coq hang
Definition subM a b := if a >= b then Some (a - b) else None.
Monadify Action subn => subM.
*)

Monadify Pure leq.

Definition cmpestri_ubyte_eqany_ppol_lsigM a la b lb :=
  if (la <= 16) && (lb <= 16) then
    Some (cmpestri_ubyte_eqany_ppol_lsig a la b lb)
  else
    None.
Monadify Action cmpestri_ubyte_eqany_ppol_lsig => cmpestri_ubyte_eqany_ppol_lsigM.

Monadify Pure chars_to_escape num_chars_to_escape.

Definition m128_of_bptrM ptr :=
  let i := i_of_bptr ptr in
  let s := s_of_bptr ptr in
  if i + 16 <= size s then
    Some (m128_of_bptr ptr)
  else
    None.
Monadify Action m128_of_bptr => m128_of_bptrM.

Monadification sse_html_escape. (* coqc hang *)
(*Print sse_html_escapeM.*)

Lemma cmpestri_ubyte_eqany_ppol_lsig_bound a la b lb :
  cmpestri_ubyte_eqany_ppol_lsig a la b lb <= 16.
Proof.
  rewrite /cmpestri_ubyte_eqany_ppol_lsig.
  case: ifP => [_|]; last by [].
  apply: (@leq_trans (size (take lb (seq_of_m128 b)))).
    by apply find_size.
  rewrite size_take size_seq_of_m128.
  by case: ltnP; first move/ltnW.
Qed.

Lemma sse_html_escape_success i s m n buf ptr :
  ptr = bptr i s ->
  i + m + n <= size s -> log2 (size s) < W ->
  sse_html_escapeM buf ptr m n = Some (sse_html_escape buf ptr m n).
Proof.
  move=> ->.
  clear ptr.
  elim/ltn_wf_ind: n i m buf.
  case => /=.
    move=> IH i m buf.
    rewrite addn0 => Him Hs.
    by rewrite /bufaddmemM /= Him.
  move=> n IH i m buf Himn Hs.
  rewrite /bptraddM /bptrgetM /bufaddmemM /m128_of_bptrM /=.
  have Him : i + m <= size s.
    apply: (leq_trans _ Himn).
    by apply leq_addr.
  have Him' : i + m < size s.
    apply: (leq_trans _ Himn).
    rewrite addnS.
    by apply leq_addr.
  rewrite Him /=.
  case: ltnP.
    move=> Hn.
    rewrite Him' /=.
    rewrite html_escape_byte_split.
    rewrite i_of_html_escape_byte_ptr add0n.
    rewrite size_s_of_html_escape_byte_ptr leqnn /=.
    rewrite addn1 Him' /=.
    apply (trec_html_escape_success (i + m + 1) s).
        by rewrite /bptradd.
      by rewrite addn1 addSnnS.
    by [].
  move=> Hn.
  rewrite (_ : i + m + 16 <= size s) /=; last first.
    apply: (leq_trans _ Himn).
    by rewrite leq_add2l ltnS.
  rewrite {1}/addM /check.
  rewrite (_ : log2 (m + 16) < W) /=; last first.
    apply: (leq_ltn_trans _ Hs).
    apply log2_le_mono.
    apply: (leq_trans _ Himn).
    apply leq_add.
      by apply leq_addl.
    by rewrite ltnS.
  case: ltnP => Hcmp.
    rewrite IH.
          by [].
        by rewrite ltnS leq_subr.
      apply: (leq_trans _ Himn).
      rewrite -2![i + _ + _]addnA.
      rewrite leq_add2l.
      rewrite -[m + _ + _]addnA.
      rewrite leq_add2l.
      rewrite addSn ltnS.
      by rewrite subnKC; first apply leqnn.
    by [].
  rewrite /addM /check.
  rewrite (_ : log2 _ < W) /=; last first.
    apply: (leq_ltn_trans _ Hs).
    apply log2_le_mono.
    apply: (leq_trans _ Himn).
    apply leq_add.
      by apply leq_addl.
    apply: (@leq_trans 16).
      by apply cmpestri_ubyte_eqany_ppol_lsig_bound.
    by rewrite ltnS.
  rewrite (_ : i + (m + _) <= size s) /=; last first.
    apply: (leq_trans _ Himn).
    rewrite addnA.
    apply leq_add.
      by apply leqnn.
    apply: (@leq_trans 16).
      by apply cmpestri_ubyte_eqany_ppol_lsig_bound.
    by rewrite ltnS.
  rewrite addn1.
  rewrite (_ : i + (m + _) < size s) /=; last first.
    apply: (leq_trans _ Himn).
    rewrite addnA.
    rewrite -addnS.
    apply leq_add.
      by apply leqnn.
    rewrite ltnS.
    by apply: (@leq_trans 15); first apply Hcmp.
  rewrite html_escape_byte_split.
  rewrite i_of_html_escape_byte_ptr add0n.
  rewrite size_s_of_html_escape_byte_ptr leqnn /=.
  apply IH.
      by rewrite ltnS leq_subr.
    rewrite /= addn0.
    apply: (leq_trans _ Himn).
    rewrite addn1 addSn addnS ltnS.
    rewrite -2![i + _ + _]addnA.
    rewrite leq_add2l.
    rewrite -[m + _ + _]addnA.
    rewrite leq_add2l.
    rewrite subnKC; first by apply leqnn.
    by apply: (@leq_trans 15).
  by [].
Qed.
