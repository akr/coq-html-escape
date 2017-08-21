From mathcomp Require Import all_ssreflect.
Require Import String.
Require Import Ascii.

Require Import htmlescape.listutils.
Require Import htmlescape.assoc.
Require Import htmlescape.ssrstr.

Local Open Scope string_scope. (* enable "string-literal" and str ++ str *)
Local Open Scope seq_scope. (* prefer seq ++ seq over str ++ str *)

Definition assoc {A : eqType} {B : Type} (a : A) (al : seq (A * B)) :=
  nosimpl (@assoc.assoc A B a al).

Definition rassoc {A : Type} {B : eqType} (b : B) (al : seq (A * B)) :=
  nosimpl (@assoc.rassoc A B b al).

Definition html_escape_al := [::
  ("&"%char, "amp");
  ("<"%char, "lt");
  (">"%char, "gt");
  (""""%char, "quot");
  ("'"%char, "#39")
].

Fixpoint html_escape s :=
  match s with
  | nil => nil
  | c :: s' =>
      (if assoc c html_escape_al is Some p then
        "&" ++ p.2 ++ ";"
      else
        [:: c]) ++
      html_escape s'
  end.

Goal html_escape "abc&def<>""'" = "abc&amp;def&lt;&gt;&quot;&#39;". by []. Qed.

Lemma html_escape_cat s1 s2 : html_escape (s1 ++ s2) = html_escape s1 ++ html_escape s2.
Proof.
  elim: s1.
    by [].
  move=> c s1 /= ->.
  by rewrite catA.
Qed.

Definition html_unescape_al := map (fun p => (p.1, seq_of_str p.2)) [::
  ("&"%char, "amp");
  ("<"%char, "lt");
  (">"%char, "gt");
  (""""%char, "quot");
  ("'"%char, "apos")
].

Fixpoint html_unescape s :=
  match s with
  | nil => nil
  | "&"%char :: s1 =>
      if ci_start_with "#x" s1 is Some n1 then
        let s2 := drop n1 s1 in
        let (v, n2) := decode_hex_prefix s2 in
        if n2 == 0 then "&"%char :: html_unescape s1 else
        let s3 := drop n2 s2 in
        if start_with ";" s3 is Some n3 then
          (ascii_of_nat v) :: html_unescape (drop n3 s3)
        else
          "&"%char :: html_unescape s1
      else if start_with "#" s1 is Some n1 then
        let s2 := drop n1 s1 in
        let (v, n2) := decode_decimal_prefix s2 in
        if n2 == 0 then "&"%char :: html_unescape s1 else
        let s3 := drop n2 s2 in
        if start_with ";" s3 is Some n3 then
          (ascii_of_nat v) :: html_unescape (drop n3 s3)
        else
          "&"%char :: html_unescape s1
      else if sindex ";"%char s1 is Some n1 then
        let name := take n1 s1 in
        let s2 := drop n1 s1 in
        if start_with ";" s2 is Some n2 then
          let s3 := drop n2 s2 in
          if rassoc name html_unescape_al is Some (c, _) then
            c :: html_unescape s3
          else
            "&"%char :: html_unescape s1
        else
          "&"%char :: html_unescape s1
      else
        "&"%char :: html_unescape s1
  | c :: s1 => c :: html_unescape s1
  end.

Lemma html_unescape_escape (s : seq ascii) : html_unescape (html_escape s) = s.
Proof.
  elim: s => [|c str IH /=]; first by [].
  rewrite /assoc /=.
  case: eqP => [<- /=|/eqP not_amp]; first by rewrite drop0 IH.
  case: eqP => [<- /=|/eqP not_lt]; first by rewrite drop0 IH.
  case: eqP => [<- /=|/eqP not_gt]; first by rewrite drop0 IH.
  case: eqP => [<- /=|/eqP not_quot]; first by rewrite drop0 IH.
  case: eqP => [<- /=|/eqP not_apos]; first by rewrite drop0 IH.
  rewrite [_ ++ _]/=.
  move: not_amp not_lt not_gt not_quot not_apos.
  case: c => b1 b2 b3 b4 b5 b6 b7 b8.
  case: b1; case: b2; case: b3; case: b4;
  case: b5; case: b6; case: b7; case: b8; by rewrite /= IH.
Qed.

Inductive esc_spec : seq ascii -> seq ascii -> Prop :=
  | esc_empty : esc_spec nil nil
  | esc_normal : forall c raw escaped, c != "&"%char ->
      esc_spec raw escaped -> esc_spec (c :: raw) (c :: escaped)
  | esc_entity : forall c entity raw escaped, (c, entity) \in html_unescape_al ->
      esc_spec raw escaped -> esc_spec (c :: raw) ("&" ++ entity ++ ";" ++ escaped)
  | esc_hex : forall x m xdigs raw escaped,
      downcase_ascii x == "x"%char -> xdigs != nil -> decode_hex xdigs = Some m ->
      esc_spec raw escaped ->
      esc_spec (ascii_of_nat m :: raw) ("&#" ++ x :: xdigs ++ ";" ++ escaped)
  | esc_dec : forall m digs raw escaped, digs != nil -> decode_decimal digs = Some m ->
      esc_spec raw escaped ->
      esc_spec (ascii_of_nat m :: raw) ("&#" ++ digs ++ ";" ++ escaped).

Lemma html_unescape_ok raw escaped :
  esc_spec raw escaped -> html_unescape escaped = raw.
Proof.
  elim/esc_spec_ind.
          by [].
        clear raw escaped => c raw escaped.
        rewrite {1}/eq_op [Equality.op _ _ _]/= /eqascii.
        case: c => b1 b2 b3 b4 b5 b6 b7 b8.
        rewrite 7!negb_and 3!eqb_id 5!eqbF_neg 5!negbK.
        move=> Hbs _ /= ->.
        move: Hbs.
        case: b1 => [|/=]; first by [].
        case: b2 => [/=|]; last by [].
        case: b3 => [/=|]; last by [].
        case: b4 => [|/=]; first by [].
        case: b5 => [|/=]; first by [].
        case: b6 => [/=|]; last by [].
        case: b7 => [|/=]; first by [].
        case: b8 => [|/=]; first by [].
        by [].
      clear raw escaped => c entity raw escaped al spec unesc.
      move: al.
      rewrite /html_unescape_al 5!in_cons in_nil.
      do 5 (case/orP => [/eqP [] -> -> /=|]; first by rewrite drop0 unesc).
      by [].
    clear raw escaped.
    move=> x m xdigs raw escaped /eqP Hx Hnonnil Hxdigs IH.
    move Hrest: (x :: xdigs ++ ";" ++ escaped) => rest /=.
    rewrite -Hx -{}Hrest eq_refl [drop 1 _]drop0 map_prefix_cat; last by [].
    rewrite size_map_prefix_xdigs; last first.
      by rewrite -decode_hex_all_isxdigit Hxdigs.
    rewrite size_eq0 -[xdigs == [::]]negbK Hnonnil /= drop_size_cat; last by [].
    rewrite eq_refl /= drop0 => ->.
    congr (ascii_of_nat _ :: raw).
    have Hsz: size (map_prefix nat_of_xdigit xdigs) == size xdigs.
      by rewrite -decode_hex_eqsize Hxdigs.
    move: Hxdigs.
    by rewrite /decode_hex /decode_hex_prefix Hsz => [] [].
  clear raw escaped.
  move=> m digs raw escaped Hnonnil Hdigs IH.
  simpl.
  rewrite (_ : match digs ++ _ with | [::] => None | sch :: _ => _ end = None); last first.
    have: all isdigit digs.
      by rewrite -decode_dec_all_isdigit Hdigs.
    case digs.
      by [].
    move=> c s' /= /andP [] Hisdigit _.
    move: Hisdigit.
    rewrite /isdigit /assoc /assoc_if /digit_chars /=.
    do 10 (case: eqP => [<- _ /=|_]; first by []).
    by [].
  rewrite drop0 map_prefix_cat; last by [].
  rewrite size_map_prefix_digs; last first.
    by rewrite -decode_dec_all_isdigit Hdigs.
  rewrite size_eq0 -[digs == [::]]negbK Hnonnil /= drop_size_cat; last by [].
  rewrite eq_refl /= drop0 => ->.
  congr (ascii_of_nat _ :: raw).
  have Hsz: size (map_prefix nat_of_digit digs) == size digs.
    by rewrite -decode_dec_eqsize Hdigs.
  move: Hdigs.
  by rewrite /decode_decimal /decode_decimal_prefix Hsz => [] [].
Qed.

Lemma html_escape_ok raw escaped :
  html_escape raw = escaped -> esc_spec raw escaped.
Proof.
  elim: raw escaped.
    move=> escaped /= <-.
    constructor.
  move=> c s IH escaped /=.
  have Hcat str : (("&"%char :: str ++ [:: ";"%char]) ++ html_escape s) =
                   ("&" ++ str ++ [:: ";"%char] ++ html_escape s).
    by rewrite 2!catA.
  rewrite /assoc /=.
  case: eqP => [<- <-|/eqP not_amp].
    by rewrite Hcat; apply esc_entity; last apply IH.
  case: eqP => [<- <-|not_lt].
    by rewrite Hcat; apply esc_entity; last apply IH.
  case: eqP => [<- <-|not_gt].
    by rewrite Hcat; apply esc_entity; last apply IH.
  case: eqP => [<- <-|not_quot].
    by rewrite Hcat; apply esc_entity; last apply IH.
  case: eqP => [<- <-|not_apos].
    rewrite (_ : "'"%char = ascii_of_nat 39); last by [].
    rewrite (_ : (("&"%char :: "#39" ++ [:: ";"%char]) ++ html_escape s) =
      ("&#" ++ "39" ++ ";" ++ html_escape s)); last by [].
    apply esc_dec.
        by [].
      by [].
    by apply IH.
  move=> /= <-.
  apply esc_normal.
    by rewrite eq_sym.
  by apply IH.
Qed.

(* pointer to byte (unsigned char).
  "cptr i lst" represents a pointer to i'th char in lst.
  restriction: 0 <= i <= size lst.
  Although a pointer with i = size lst is valid, its dereference is invalid.
*)
Inductive byteptr := bptr : nat -> seq ascii -> byteptr.

(* accessors for Coq proof *)
Definition i_of_bptr ptr := let: bptr i s := ptr in i.
Definition s_of_bptr ptr := let: bptr i s := ptr in s.

(* precondition: i + n <= size s
  C: p + n *)
Definition bptradd ptr n :=
  let i := i_of_bptr ptr in
  let s := s_of_bptr ptr in
  bptr (i + n) s.

(* precondition: n <= i
  C: p - n *)
Definition bptrsub ptr n :=
  let i := i_of_bptr ptr in
  let s := s_of_bptr ptr in
  bptr (i - n) s.

(* precondition: i < size s
  C: *p *)
Definition bptrget ptr :=
  let i := i_of_bptr ptr in
  let s := s_of_bptr ptr in
  nth "000"%char s i.

(* buffer implemented using Ruby String.
  Encoding is not considiered.
  The C type is struct rbuf { size_t len; VALUE str }.
  "len" is used to detect the non-linear use of the string.
  If the string is used linearly, len == RSTRING_LEN(str) is hold.
  We assume this condition in following explanation.
 *)
Inductive buffer := bufctr of seq ascii.

(* accessor for Coq proof *)
Definition s_of_buf buf := let: bufctr s := buf in s.

(* (struct rbuf){ len + 1, rb_str_buf_cat(str, &b, 1) } *)
Definition bufaddbyte buf b :=
  let s := s_of_buf buf in
  bufctr (rcons s b).

(* precondition: i + n <= size s'
  (struct rbuf){ len + n, rb_str_buf_cat(str, ptr, n) }
 *)
Definition bufaddmem buf ptr n :=
  let s := s_of_buf buf in
  let i := i_of_bptr ptr in
  let s' := s_of_bptr ptr in
  bufctr (s ++ take n (drop i s')).

(* This function will be implemented as a table in C *)
Definition html_escape_byte c :=
  if assoc c html_escape_al is Some p then
    let s := "&" ++ p.2 ++ ";" in
    (bptr 0 s, size s)
  else
    (bptr 0 [:: c], 1).

Fixpoint trec_html_escape buf ptr n :=
  match n with
  | 0 => buf
  | n'.+1 =>
      let: (escptr, escn) := html_escape_byte (bptrget ptr) in
      trec_html_escape
        (bufaddmem buf escptr escn)
        (bptradd ptr 1)
        n'
  end.

Definition trec_html_escape_stub s :=
  s_of_buf (trec_html_escape (bufctr [::]) (bptr 0 s) (size s)).

Lemma html_escape_byte_split c : html_escape_byte c =
  ((if assoc c html_escape_al is Some p then
    bptr 0 ("&" ++ p.2 ++ ";")
  else
    bptr 0 [:: c]),
  (if assoc c html_escape_al is Some p then
    (size p.2).+2
  else
    1)).
Proof.
  rewrite /assoc /=.
  case: eqP => [<-|/eqP /negbTE not_amp]; first by [].
  case: eqP => [<-|/eqP /negbTE not_lt]; first by [].
  case: eqP => [<-|/eqP /negbTE not_gt]; first by [].
  case: eqP => [<-|/eqP /negbTE not_quot]; first by [].
  case: eqP => [<-|/eqP /negbTE not_apos]; first by [].
  rewrite /html_escape_byte /assoc /=.
  by rewrite not_amp not_lt not_gt not_quot not_apos.
Qed.

Lemma trec_html_escape_ok1 s buf i j :
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
  rewrite /= catA.
  rewrite /bptradd /= addn1.
  case: (assoc c html_escape_al).
    move=> p.
    rewrite /bufaddmem /=.
    rewrite IH; last by rewrite addSnnS.
    congr ((buf ++ "&"%char :: _) ++ html_escape (drop i.+1 s)).
    rewrite (_ : (size p.2).+1 = (size (p.2 ++ [:: ";"%char]))).
      by rewrite take_size.
    by rewrite size_cat /= addn1.
  rewrite /bufaddmem /=.
  by rewrite IH; last by rewrite addSnnS.
Qed.

Lemma trec_html_escape_ok s : trec_html_escape_stub s = html_escape s.
Proof.
  rewrite /trec_html_escape_stub.
  by rewrite trec_html_escape_ok1; first rewrite drop0.
Qed.

Inductive m128 := c128 :
  ascii -> ascii -> ascii -> ascii ->
  ascii -> ascii -> ascii -> ascii ->
  ascii -> ascii -> ascii -> ascii ->
  ascii -> ascii -> ascii -> ascii -> m128.

Definition seq_of_m128 m :=
  let: c128 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 ba bb bc bd be bf := m in
  [:: b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; ba; bb; bc; bd; be; bf].

Definition m128_of_seq s := c128
  (nth "000"%char s 0) (nth "000"%char s 1) (nth "000"%char s 2) (nth "000"%char s 3)
  (nth "000"%char s 4) (nth "000"%char s 5) (nth "000"%char s 6) (nth "000"%char s 7)
  (nth "000"%char s 8) (nth "000"%char s 9) (nth "000"%char s 10) (nth "000"%char s 11)
  (nth "000"%char s 12) (nth "000"%char s 13) (nth "000"%char s 14) (nth "000"%char s 15).

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

Definition m128_of_bptr ptr := m128_of_seq (drop (i_of_bptr ptr) (s_of_bptr ptr)).

(* _mm_cmpestri(a, la, b, lb,
     _SIDD_UBYTE_OPS|_SIDD_CMP_EQUAL_ANY|
     _SIDD_POSITIVE_POLARITY|_SIDD_LEAST_SIGNIFICANT) *)
Definition cmpestri_ubyte_eqany_ppol_lsig (a : m128) (la : nat) (b : m128) (lb : nat) :=
  let sa := take la (seq_of_m128 a) in
  let sb := take lb (seq_of_m128 b) in
  let p x := x \in sa in
  if has p sb then find p sb else 16.

Definition need_to_escape := m128_of_seq [:: "&"%char; "<"%char; ">"%char; """"%char; "'"%char].

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
  have Hhas : has [eta mem a] b.
    move: Hif Hi.
    by case: (has [eta mem a] b) => [|->].
  rewrite Hhas in Hif.
  split.
    apply/allP => x.
    
  
About before_find.
Qed.

Fixpoint sse_html_escape buf ptr n :=
  match n with
  | 0 => buf
  | n'.+1 =>
      if n < 16 then
        trec_html_escape buf ptr n
      else
        let i := cmpestri_ubyte_eqany_ppol_lsig
            need_to_escape 5 (m128_of_bptr ptr) 16 in
        if i < 16 then
          let buf2 := bufaddmem buf ptr i in
          let ptr2 := bptradd ptr i in
          let c := bptrget ptr2 in
          let ptr3 := bptradd ptr2 1 in
          let: (escptr, escn) := html_escape_byte c in
          let buf3 := bufaddmem buf2 escptr escn in
          sse_html_escape buf3 ptr3 (n' - i)
        else
          sse_html_escape (bufaddmem buf ptr 16) (bptradd ptr 16) (n' - 15)
  end.

Definition sse_html_escape_stub s :=
  s_of_buf (sse_html_escape (bufctr [::]) (bptr 0 s) (size s)).

Require Import Wf_nat.
About lt_wf_ind.

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
  c \notin [:: "&"%char; "<"%char; ">"%char; """"%char; "'"%char] ->
  html_escape (c :: s) = c :: html_escape s.
Proof.
  rewrite /in_mem /= 5!negb_or /assoc /= => /andP [].
  do 4 (rewrite eq_sym => /negbTE -> /andP []).
  by rewrite eq_sym => /negbTE -> _.
Qed.

Lemma html_escape_rawonly s :
  (let p x := x \notin [:: "&"%char; "<"%char; ">"%char; """"%char; "'"%char] in
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

Lemma sse_html_escape_ok s : sse_html_escape_stub s = html_escape s.
Proof.
  rewrite /sse_html_escape_stub.
  rewrite -[html_escape s]cat0s.
  move: [::] => buf.
  rewrite -{3}[s]drop0.
  move: (Logic.eq_refl (size s)).
  rewrite -{1}[size s]add0n.
  move: 0 => i.
  move: {1 3}(size s) => j.
  elim/ltn_wf_ind: j i buf.
  case => [|j] IH i buf /=.
    rewrite addn0 => ->.
    by rewrite drop_size cats0.
  move=> Hij.
  rewrite (_ : (let '(escptr, escn) := _ in _) =
      trec_html_escape (bufctr buf) (bptr i s) j.+1); last by [].
  case: ltnP.
    by rewrite trec_html_escape_ok1.
  move=> Hj.
  case: leqP.
    rewrite /bufaddmem /bptradd /=.
    rewrite IH; last first.
        rewrite -Hij.
        rewrite addnBA; last by rewrite -ltnS.
        by rewrite addnC addnA -add1n addnA addnK addn1 addnS addnC.
      by rewrite ltnS leq_subr.
    rewrite /m128_of_bptr /=.
    rewrite addnC -drop_drop.
    rewrite /need_to_escape.
    move=> Hcmpestri.
    rewrite -catA.
    congr (buf ++ _).
    rewrite -{3}[drop i s](cat_take_drop 16).
    rewrite html_escape_cat.
    congr (_ ++ html_escape (drop 16 (drop i s))).
    have Hds : j.+1 = size (drop i s).
      by rewrite size_drop -Hij addKn.
    have Hnotin : let p x :=
        x \notin [:: "&"%char; "<"%char; ">"%char; """"%char; "'"%char] in
        all p (take 16 (drop i s)).
      apply cmpestri_none.
          by [].
        by rewrite size_takel; last rewrite -Hds.
      rewrite m128_of_seq_take; last by [].
      rewrite (_ : (size (take 16 (drop i s))) = 16); last first.
        by rewrite size_takel; last rewrite -Hds.
      by apply Hcmpestri.
    by rewrite html_escape_rawonly; last apply Hnotin.
  
  
    
  
        rewrite take_size.
          rewrite -Hds.
        rewrite -Hds.
    apply (cmpestri_none _ _) in Hcmpestri.
    move: Hds Hj Hcmpestri.


    case: (drop i s) => [|c0 s1]; first by [].
    case: s1 => [/= ->|c1 s1]; first by [].
    case: s1 => [/= ->|c2 s1]; first by [].
    case: s1 => [/= ->|c3 s1]; first by [].
    case: s1 => [/= ->|c4 s1]; first by [].
    case: s1 => [/= ->|c5 s1]; first by [].
    case: s1 => [/= ->|c6 s1]; first by [].
    case: s1 => [/= ->|c7 s1]; first by [].
    case: s1 => [/= ->|c8 s1]; first by [].
    case: s1 => [/= ->|c9 s1]; first by [].
    case: s1 => [/= ->|ca s1]; first by [].
    case: s1 => [/= ->|cb s1]; first by [].
    case: s1 => [/= ->|cc s1]; first by [].
    case: s1 => [/= ->|cd s1]; first by [].
    case: s1 => [/= ->|ce s1]; first by [].
    case: s1 => [/= ->|cf s1]; first by [].
    simpl.
    rewrite cmpestri_none.


    case: s1.
      simpl.
      by move=> ->.
      
  

  rewrite ltnS.
    
    rewrite html_escape_byte_split.
    rewrite trec_html_escape_ok1; last first.
      by rewrite -Hij addn1 addSnnS.
    rewrite (_ : (i_of_bptr _) = 0); last first.
      by case: (assoc _ _).

    
  
Qed.

Require Import Monomorph.monomorph.

Terminate Monomorphization html_escape_byte.

Terminate Monomorphization cmpestri_ubyte_eqany_ppol_lsig.
Terminate Monomorphization need_to_escape.
Terminate Monomorphization m128_of_bptr.
Terminate Monomorphization bptradd.
Terminate Monomorphization bufaddmem.
Terminate Monomorphization bptrget.
Terminate Monomorphization subn.
Terminate Monomorphization eqn.
Terminate Monomorphization leq.
Monomorphization trec_html_escape.
Monomorphization sse_html_escape.
GenCFile "gen/esc.c" _trec_html_escape _sse_html_escape.

