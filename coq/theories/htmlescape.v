From mathcomp Require Import all_ssreflect.
Require Import String.
Require Import Ascii.

Require Import htmlescape.listutils.
Require Import htmlescape.assoc.
Require Import htmlescape.ssrstr.
Require Import htmlescape.spec.
Require Import htmlescape.imp.

Lemma html_escape_cat s1 s2 : html_escape (s1 ++ s2) = html_escape s1 ++ html_escape s2.
Proof. by rewrite /html_escape -flatten_cat map_cat. Qed.

Lemma html_escape_cons c s : html_escape (c :: s) = html_escape_byte c ++ html_escape s.
Proof. by rewrite /html_escape /flatten. Qed.

Lemma html_unescape_escape s : html_unescape (html_escape s) = s.
Proof.
  rewrite /html_escape /=.
  elim: s => [|c str IH /=]; first by [].
  rewrite /html_escape_byte /assoc /=.
  case: eqP => [<- /=|/eqP not_amp]; first by rewrite drop0 IH.
  do 4 (case: eqP => [<- /=|/eqP _]; first by rewrite drop0 IH).
  rewrite [_ ++ _]/=.
  case: c not_amp.
  (* "&" is 0b00100110 *)
  case; first by rewrite /= IH. (* LSB of "&" *)
  case; last by rewrite /= IH.
  case; last by rewrite /= IH.
  case; first by rewrite /= IH.
  case; first by rewrite /= IH.
  case; last by rewrite /= IH.
  case; first by rewrite /= IH.
  case; first by rewrite /= IH. (* MSB of "&" *)
  by [].
Qed.

Lemma html_unescape_correct raw escaped :
  text_spec raw escaped -> html_unescape escaped = raw.
Proof.
  elim/text_spec_ind.
    by [].
  clear raw escaped.
  move=> c s raw escaped.
  move=> Hcs Hts IH.
  case: Hcs; clear c.
        case.
        case; first by rewrite /= IH.
        case; last by rewrite /= IH.
        case; last by rewrite /= IH.
        case; first by rewrite /= IH.
        case; first by rewrite /= IH.
        case; last by rewrite /= IH.
        case; first by rewrite /= IH.
        case; first by rewrite /= IH.
        by [].
      move=> c entity.
      rewrite /html_char_entities 5!in_cons in_nil.
      by do 5 (case/orP => [/eqP [] -> -> /=|]; first by rewrite /= drop0 IH).
    move=> m digs Hnnil Hdigs /=.
    rewrite (_ : match (digs ++ _) ++ escaped with | [::] => None | sch :: _ => _ end = None); last first.
      have: all isdigit digs.
        by rewrite -decode_dec_all_isdigit Hdigs.
      case digs.
        by [].
      move=> c s' /= /andP [] Hisdigit _.
      move: Hisdigit.
      rewrite /isdigit /assoc /assoc_if /digit_chars /=.
      do 10 (case: eqP => [<- _ /=|_]; first by []).
      by [].
    rewrite drop0 -catA map_prefix_cat; last by [].
    rewrite size_map_prefix_digs; last first.
      by rewrite -decode_dec_all_isdigit Hdigs.
    rewrite size_eq0 -[digs == [::]]negbK Hnnil /= drop_size_cat; last by [].
    rewrite /= drop0 IH.
    congr (ascii_of_nat _ :: raw).
    have Hsz: size (map_prefix nat_of_digit digs) == size digs.
      by rewrite -decode_dec_eqsize Hdigs.
    move: Hdigs.
    by rewrite /decode_decimal /decode_decimal_prefix Hsz => [] [].
  move=> x m xdigs /eqP Hx Hnonnil Hxdigs.
  rewrite /= -Hx eq_refl drop0 -catA map_prefix_cat; last by [].
  rewrite size_map_prefix_xdigs; last first.
    by rewrite -decode_hex_all_isxdigit Hxdigs.
  rewrite size_eq0 -[xdigs == [::]]negbK Hnonnil /= drop_size_cat; last by [].
  rewrite eq_refl /= drop0 IH.
  congr (ascii_of_nat _ :: raw).
  have Hsz: size (map_prefix nat_of_xdigit xdigs) == size xdigs.
    by rewrite -decode_hex_eqsize Hxdigs.
  move: Hxdigs.
  by rewrite /decode_hex /decode_hex_prefix Hsz => [] [].
Qed.

Lemma html_escape_correct raw escaped :
  html_escape raw = escaped -> text_spec raw escaped.
Proof.
  elim: raw escaped.
    move=> escaped /= <-.
    constructor.
  move=> c s IH escaped /=.
  rewrite html_escape_cons /html_escape_byte /assoc /=.
  case: eqP => [<- <-|/eqP not_amp].
    by constructor; [constructor|apply IH].
  case: eqP => [<- <-|not_lt].
    by constructor; [constructor|apply IH].
  case: eqP => [<- <-|not_gt].
    by constructor; [constructor|apply IH].
  case: eqP => [<- <-|not_quot].
    by constructor; [constructor|apply IH].
  case: eqP => [<- <-|not_apos].
    rewrite (_ : "'"%char = ascii_of_nat 39); last by [].
    by constructor; [apply char_dec|apply IH].
  move=> <-.
  constructor.
    apply char_normal.
    by rewrite eq_sym.
  by apply IH.
Qed.

Definition html_escape_byte_ptr c :=
  if assoc c html_escape_alist is Some p then
    bptr 0 ("&" ++ p.2 ++ ";")
  else
    bptr 0 [:: c].

Definition html_escape_byte_len c :=
  if assoc c html_escape_alist is Some p then
    (size p.2).+2
  else
    1.

Lemma html_escape_byte_split c : html_escape_byte_table c =
  (html_escape_byte_ptr c, html_escape_byte_len c).
Proof.
  rewrite /html_escape_byte_ptr /html_escape_byte_len /assoc /=.
  case: eqP => [<-|/eqP /negbTE not_amp]; first by [].
  case: eqP => [<-|/eqP /negbTE not_lt]; first by [].
  case: eqP => [<-|/eqP /negbTE not_gt]; first by [].
  case: eqP => [<-|/eqP /negbTE not_quot]; first by [].
  case: eqP => [<-|/eqP /negbTE not_apos]; first by [].
  rewrite /html_escape_byte_table /assoc /=.
  by rewrite not_amp not_lt not_gt not_quot not_apos.
Qed.

Lemma i_of_html_escape_byte_ptr c : i_of_bptr (html_escape_byte_ptr c) = 0.
Proof.
  rewrite /html_escape_byte_ptr.
  by case: (assoc c html_escape_alist).
Qed.

Lemma take_html_escape_byte_len_ptr c :
    take (html_escape_byte_len c) (s_of_bptr (html_escape_byte_ptr c)) =
    s_of_bptr (html_escape_byte_ptr c).
Proof.
  rewrite /html_escape_byte_len /html_escape_byte_ptr.
  case: (assoc c html_escape_alist) => [p|] /=; last by [].
  rewrite (_ : (size p.2).+1 = size (p.2 ++ [:: ";"%char])).
    by rewrite take_size.
  by rewrite size_cat addn1.
Qed.

Lemma s_of_html_escape_byteptr c : s_of_bptr (html_escape_byte_ptr c) = html_escape [:: c].
Proof.
  rewrite /html_escape_byte_ptr html_escape_cons /html_escape_byte.
  case: (assoc c html_escape_alist) => [p|] /=; last by [].
  by rewrite cats0.
Qed.

Lemma trec_html_escape_correct1 s buf i j :
  i + j = size s ->
  s_of_buf (trec_html_escape (bufctr buf) (bptr i s) j) =
  buf ++ html_escape (drop i s).
Proof.
  elim: j i buf.
    move=> i buf /=.
    rewrite addn0 => ->.
    by rewrite drop_size cats0.
  move=> j IH i buf Hij /=.
  move Hc: (bptrget (bptr i s)) => c.
  rewrite /bptrget /= in Hc.
  have Hs : take i s ++ c :: drop i.+1 s = s.
    clear IH.
    rewrite -{3}[s](cat_take_drop i).
    congr (take i s ++ _).
    rewrite [drop i s](drop_nth "000"%char).
      by rewrite -Hc.
    by rewrite -Hij addnS ltnS leq_addr.
  rewrite html_escape_byte_split /=.
  rewrite -{2}[s]Hs drop_size_cat; last first.
    rewrite size_takel; first by [].
    by rewrite -Hij leq_addr.
  rewrite html_escape_cons /= catA.
  rewrite /bptradd /= addn1.
  rewrite /bufaddmem /= i_of_html_escape_byte_ptr drop0.
  rewrite /html_escape_byte_ptr.
  rewrite /html_escape_byte_len.
  rewrite /html_escape_byte.
  case: (assoc c html_escape_alist) => [p|] /=.
    rewrite IH; last by rewrite addSnnS.
    congr ((buf ++ "&"%char :: _) ++ html_escape (drop i.+1 s)).
    rewrite (_ : (size p.2).+1 = (size (p.2 ++ [:: ";"%char]))).
      by rewrite take_size.
    by rewrite size_cat /= addn1.
  by rewrite IH; last by rewrite addSnnS.
Qed.

Lemma trec_html_escape_correct s : trec_html_escape_stub s = html_escape s.
Proof.
  rewrite /trec_html_escape_stub.
  by rewrite trec_html_escape_correct1; first rewrite drop0.
Qed.

Lemma m128_of_seq_of_m128 m : m128_of_seq (seq_of_m128 m) = m.
Proof.
  by case: m.
Qed.

Lemma seq_of_m128_of_seq n s :
  n = size s ->
  take n (seq_of_m128 (m128_of_seq s)) = take (minn n 16) s.
Proof.
  move=> ->.
  case: s => [|b0 s]; first by [].
  case: s => [|b1 s]; first by [].
  case: s => [|b2 s]; first by [].
  case: s => [|b3 s]; first by [].
  case: s => [|b4 s]; first by [].
  case: s => [|b5 s]; first by [].
  case: s => [|b6 s]; first by [].
  case: s => [|b7 s]; first by [].
  case: s => [|b8 s]; first by [].
  case: s => [|b9 s]; first by [].
  case: s => [|ba s]; first by [].
  case: s => [|bb s]; first by [].
  case: s => [|bc s]; first by [].
  case: s => [|bd s]; first by [].
  case: s => [|be s]; first by [].
  case: s => [|bf s]; first by [].
  by rewrite /= take0.
Qed.

Lemma size_seq_of_m128 m : size (seq_of_m128 m) = 16.
Proof.
  by case: m.
Qed.

Lemma seq_of_m128_of_seq_long s :
  16 <= size s -> seq_of_m128 (m128_of_seq s) = take 16 s.
Proof.
  move=> Hs.
  rewrite (_ : 16 = (minn (size s) 16)); last first.
    by rewrite /minn ltnNge Hs.
  rewrite -seq_of_m128_of_seq; last by [].
  rewrite take_oversize; first by [].
  by rewrite size_seq_of_m128.
Qed.

Lemma m128_of_seq_take n s : 16 <= n -> m128_of_seq (take n s) = m128_of_seq s.
Proof.
  do 16 (case: n => [|n]; first by []).
  move=> _.
  case: s => [|c0 s]; first by [].
  case: s => [|c1 s]; first by [].
  case: s => [|c2 s]; first by [].
  case: s => [|c3 s]; first by [].
  case: s => [|c4 s]; first by [].
  case: s => [|c5 s]; first by [].
  case: s => [|c6 s]; first by [].
  case: s => [|c7 s]; first by [].
  case: s => [|c8 s]; first by [].
  case: s => [|c9 s]; first by [].
  case: s => [|ca s]; first by [].
  case: s => [|cb s]; first by [].
  case: s => [|cc s]; first by [].
  case: s => [|cd s]; first by [].
  case: s => [|ce s]; first by [].
  case: s => [|cf s]; first by [].
  by [].
Qed.

Lemma take_seq_of_m128 n m : 16 <= n -> take n (seq_of_m128 m) = seq_of_m128 m.
Proof.
  do 16 (case: n => [|n]; first by []).
  by case: m.
Qed.

Lemma cmpestri_minn16la a la b lb : cmpestri_ubyte_eqany_ppol_lsig a la b lb =
  cmpestri_ubyte_eqany_ppol_lsig a (minn 16 la) b lb.
Proof.
  rewrite /cmpestri_ubyte_eqany_ppol_lsig.
  by rewrite minnC take_minn [take 16 _]take_seq_of_m128.
Qed.

Lemma cmpestri_minn16lb a la b lb : cmpestri_ubyte_eqany_ppol_lsig a la b lb =
  cmpestri_ubyte_eqany_ppol_lsig a la b (minn 16 lb).
Proof.
  rewrite /cmpestri_ubyte_eqany_ppol_lsig.
  by rewrite minnC take_minn [take 16 _]take_seq_of_m128.
Qed.

Lemma cmpestri_none a b :
  size a <= 16 -> size b <= 16 ->
  16 <= cmpestri_ubyte_eqany_ppol_lsig (m128_of_seq a) (size a) (m128_of_seq b) (size b) ->
  let p x := x \notin a in all p b.
Proof.
  move=> Ha Hb.
  rewrite /cmpestri_ubyte_eqany_ppol_lsig.
  rewrite seq_of_m128_of_seq; last by [].
  rewrite seq_of_m128_of_seq; last by [].
  rewrite 2![minn _ 16]minnC /minn 2![16 < _]ltnNge.
  rewrite Ha Hb 2![if ~~ true then _ else _]/= 2!take_size.
  case: ifP.
    rewrite has_find.
    move=> H1 H2.
    have: 16 < size b.
      by apply: (leq_ltn_trans H2).
    clear H1 H2 Ha.
    by rewrite ltnNge Hb. 
  move/hasP.
  move=> Hex _.
  apply/allP => x Hxb.
  apply (@introN (is_true (in_mem x (mem a)))).
    by case: (in_mem x (mem a)); constructor.
  move=> Hxa.
  apply Hex.
  by exists x.
Qed.

Lemma negb_has_take_find {T : eqType} p (s : seq T) : ~~ has p (take (find p s) s).
Proof.
  elim: s.
    by [].
  move=> v s IH /=.
  move Hpv : (p v) => pv.
  case: pv Hpv.
    by [].
  move=> /= ->.
  by rewrite IH.
Qed.

Lemma cmpestri_found a b i :
  size a <= 16 -> size b <= 16 ->
  i = cmpestri_ubyte_eqany_ppol_lsig
    (m128_of_seq a) (size a) (m128_of_seq b) (size b) ->
  i < 16 ->
  let p x := x \notin a in all p (take i b) /\
  nth "000"%char b i \in a.
Proof.
  move=> Ha Hb.
  rewrite /cmpestri_ubyte_eqany_ppol_lsig.
  rewrite seq_of_m128_of_seq; last by [].
  rewrite seq_of_m128_of_seq; last by [].
  rewrite 2![minn _ 16]minnC /minn 2![16 < _]ltnNge.
  rewrite Ha Hb 2![if ~~ true then _ else _]/= 2!take_size.
  rewrite /in_mem.
  move=> Hif Hi.
  have Hhas : has (mem a) b.
    move: Hif Hi.
    by case: (has (mem a) b) => [|->].
  rewrite Hhas in Hif.
  split.
    rewrite all_predC.
    rewrite Hif.
    by apply negb_has_take_find.
  rewrite Hif.
  by apply nth_find.
Qed.

Require Import Wf_nat.

Lemma ltn_wf_ind (n : nat) (P : nat -> Prop) :
  (forall n0 : nat, (forall m : nat, m < n0 -> P m) -> P n0) -> P n.
Proof.
  move=> Hssr.
  apply lt_wf_ind => n0 Hcoq.
  apply Hssr => m Hltn.
  apply Hcoq.
  apply/ltP.
  by apply Hltn.
Qed.

Lemma html_escape_rawchar c s :
  c \notin chars_to_escape_list  ->
  html_escape (c :: s) = c :: html_escape s.
Proof.
  rewrite html_escape_cons /html_escape_byte.
  rewrite /in_mem /= 5!negb_or /assoc /= => /andP [].
  do 4 (rewrite eq_sym => /negbTE -> /andP []).
  by rewrite eq_sym => /negbTE -> _.
Qed.

Lemma html_escape_rawonly s :
  (let p x := x \notin chars_to_escape_list  in
  all p s) ->
  html_escape s = s.
Proof.
  elim: s.
    by [].
  move=> c s IH H.
  rewrite html_escape_rawchar; last first.
    by move: H => /= /andP [] ->.
  congr (c :: _).
  rewrite IH; first by [].
  by move: H => /= /andP [] _ ->.
Qed.

Lemma sse_html_escape_correct1 s buf i m n : i + m + n = size s ->
  s_of_buf (sse_html_escape (bufctr buf) (bptr i s) m n) =
  buf ++ take m (drop i s) ++ html_escape (drop (i + m) s).
Proof.
  elim/ltn_wf_ind: n i m buf.
  case => [_|n IH] i m buf /=.
    rewrite addn0 => ->.
    by rewrite drop_size cats0.
  move=> Himn.
  rewrite (_ : (let '(escptr, escn) := _ in _) =
      trec_html_escape
        (bufaddmem (bufctr buf) (bptr i s) m)
        (bptradd (bptr i s) m) n.+1); last by [].
  case: ltnP.
    by rewrite trec_html_escape_correct1 /=; first rewrite catA.
  move=> Hn.
  case: leqP; last first.
    rewrite /bufaddmem /bptradd /=.
    rewrite IH; last first.
        rewrite -Himn.
        rewrite addnA addnBA; last by rewrite -ltnS.
        by rewrite addnC addnA -add1n addnA addnK addn1 addnS addnC.
      by rewrite ltnS leq_subr.
    rewrite /m128_of_bptr /=.
    rewrite addnC -drop_drop.
    rewrite /chars_to_escape.
    rewrite drop_drop [m + i]addnC => Hcmpestri.
    congr (buf ++ _).
    rewrite -[take (m + 16) (drop i s)](cat_take_drop m).
    rewrite take_take; last by rewrite leq_addr.
    rewrite -catA.
    congr (take m (drop i s) ++ _).
    rewrite drop_take_inv drop_drop.
    rewrite [m + i]addnC addnA.
    rewrite -{2}[drop (i + m) s](cat_take_drop 16).
    rewrite html_escape_cat.
    rewrite drop_drop [16 + _]addnC.
    congr (_ ++ html_escape (drop (i + m + 16) s)).
    have Hds : n.+1 = size (drop (i + m) s).
      by rewrite size_drop -Himn addKn.
    have Hnotin : let p x :=
        x \notin chars_to_escape_list in
        all p (take 16 (drop (i + m) s)).
      apply cmpestri_none.
          by [].
        by rewrite size_takel; last rewrite -Hds.
      rewrite m128_of_seq_take; last by [].
      rewrite (_ : (size (take 16 (drop (i + m) s))) = 16); last first.
        by rewrite size_takel; last rewrite -Hds.
      by apply Hcmpestri.
    by rewrite html_escape_rawonly; last apply Hnotin.
  rewrite /chars_to_escape /m128_of_bptr /=.
  rewrite -[m128_of_seq (drop (i + m) s)](m128_of_seq_take 16); last by [].
  move Hcmpestri: (cmpestri_ubyte_eqany_ppol_lsig _ _ _ _) => k.
  rewrite {2}(_ : 16 = size (take 16 (drop (i + m) s))) in Hcmpestri; last first.
    by rewrite size_takel; last rewrite size_drop -Himn addKn.
  move=> Hk.
  have : k < 16; first by [].
  rewrite -{1}Hcmpestri.
  move=> Hk'.
  apply (cmpestri_found
    chars_to_escape_list
    (take 16 (drop (i + m) s))) in Hk'; last first.
        by [].
      by rewrite size_takel; last rewrite size_drop -Himn addKn.
    by [].
  rewrite Hcmpestri in Hk'.
  case: Hk' => Hbefore.
  rewrite nth_take; last by [].
  rewrite nth_drop => Hfound.
  rewrite html_escape_byte_split.
  rewrite /bufaddmem /bptradd /bptrget /=.
  rewrite i_of_html_escape_byte_ptr drop0.
  rewrite take_html_escape_byte_len_ptr.
  rewrite IH; last first.
      rewrite addn0.
      rewrite addnAC -Himn addn1 addnS.
      congr (_.+1).
      rewrite -2![i + _ + _]addnA.
      congr (i + _).
      rewrite -[m + _ + _]addnA.
      congr (m + _).
      rewrite subnKC.
        by [].
      apply: (leq_trans _ Hn).
      by rewrite -ltnS.
    by rewrite ltnS leq_subr.
  rewrite -2!catA.
  congr (buf ++ _).
  rewrite take0 cat0s addn0 addnA.
  rewrite -{1}[take (m + k) (drop i s)](cat_take_drop m) -catA.
  rewrite take_take; last by rewrite leq_addr.
  rewrite drop_take_inv drop_drop [m + i]addnC.
  congr (take m (drop i s) ++ _).
  rewrite -{2}[drop (i + m) s](cat_take_drop k).
  rewrite drop_drop [k + (i + m)]addnC.
  rewrite -[drop (i + m + k) s](cat_take_drop 1).
  rewrite drop_drop [1 + (i + m + k)]addnC.
  rewrite 2!html_escape_cat.
  congr (_ ++ _ ++ _).
    rewrite html_escape_rawonly; first by [].
    rewrite take_take in Hbefore.
      by apply Hbefore.
    by apply ltnW.
  rewrite s_of_html_escape_byteptr.
  congr (html_escape _).
  clear Hcmpestri Hbefore Hfound.
  rewrite (drop_nth "000"%char); last first.
    rewrite -Himn ltn_add2l.
    apply: (leq_trans _ Hn).
    by rewrite -ltnS.
  by rewrite /= take0.
Qed.

Lemma sse_html_escape_correct s : sse_html_escape_stub s = html_escape s.
Proof.
  rewrite /sse_html_escape_stub.
  by rewrite sse_html_escape_correct1; first rewrite take0 drop0.
Qed.
