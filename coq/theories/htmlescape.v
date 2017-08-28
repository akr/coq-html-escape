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

Definition html_escape_alist :=
  map (fun p => (p.1, seq_of_str p.2)) [::
  ("&"%char, "amp");
  ("<"%char, "lt");
  (">"%char, "gt");
  (""""%char, "quot");
  ("'"%char, "#39")
].

Definition html_escape_byte c :=
  if assoc c html_escape_alist is Some p then
    "&" ++ p.2 ++ ";"
  else
    [:: c].

Definition html_escape s := flatten (map html_escape_byte s).

Goal html_escape "abc&def<>""'" = "abc&amp;def&lt;&gt;&quot;&#39;". by []. Qed.

Lemma html_escape_cat s1 s2 : html_escape (s1 ++ s2) = html_escape s1 ++ html_escape s2.
Proof. by rewrite /html_escape -flatten_cat map_cat. Qed.

Lemma html_escape_cons c s : html_escape (c :: s) = html_escape_byte c ++ html_escape s.
Proof. by rewrite /html_escape /flatten. Qed.

Definition html_char_entities :=
  map (fun p => (p.1, seq_of_str p.2)) [::
  ("&"%char, "amp");
  ("<"%char, "lt");
  (">"%char, "gt");
  (""""%char, "quot");
  ("'"%char, "apos")
  (* ... more character entities here ... *)
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
          if rassoc name html_char_entities is Some (c, _) then
            c :: html_unescape s3
          else
            "&"%char :: html_unescape s1
        else
          "&"%char :: html_unescape s1
      else
        "&"%char :: html_unescape s1
  | c :: s1 => c :: html_unescape s1
  end.

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

(* HTML character and text specification.
 * https://html.spec.whatwg.org/multipage/syntax.html#text-2
 * Note: Unicode is not considered.
 *)
Inductive char_spec : ascii -> seq ascii -> Prop :=
  | char_normal : forall c, c != "&"%char -> char_spec c [:: c]
  | char_named : forall c entity, (c, entity) \in html_char_entities ->
      char_spec c ("&" ++ entity ++ ";")
  | char_dec : forall m digs, digs != nil -> decode_decimal digs = Some m ->
      char_spec (ascii_of_nat m) ("&#" ++ digs ++ ";")
  | char_hex : forall x m xdigs,
      downcase_ascii x == "x"%char -> xdigs != nil -> decode_hex xdigs = Some m ->
      char_spec (ascii_of_nat m) ("&#" ++ x :: xdigs ++ ";").

Inductive text_spec : seq ascii -> seq ascii -> Prop :=
  | text_empty : text_spec [::] [::]
  | text_cons : forall c s raw escaped,
      char_spec c s -> text_spec raw escaped -> text_spec (c :: raw) (s ++ escaped).

Lemma html_unescape_ok raw escaped :
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

Lemma html_escape_ok raw escaped :
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
Definition html_escape_byte_table c :=
  if assoc c html_escape_alist is Some p then
    let s := "&" ++ p.2 ++ ";" in
    (bptr 0 s, size s)
  else
    (bptr 0 [:: c], 1).

Fixpoint trec_html_escape buf ptr n :=
  match n with
  | 0 => buf
  | n'.+1 =>
      let: (escptr, escn) := html_escape_byte_table (bptrget ptr) in
      trec_html_escape
        (bufaddmem buf escptr escn)
        (bptradd ptr 1)
        n'
  end.

Definition trec_html_escape_stub s :=
  s_of_buf (trec_html_escape (bufctr [::]) (bptr 0 s) (size s)).

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

Lemma take_seq_of_m128 n m : 16 <= n -> take n (seq_of_m128 m) = seq_of_m128 m.
Proof.
  do 16 (case: n => [|n]; first by []).
  by case: m.
Qed.

Definition m128_of_bptr ptr := m128_of_seq (drop (i_of_bptr ptr) (s_of_bptr ptr)).

(* _mm_cmpestri(a, la, b, lb,
     _SIDD_UBYTE_OPS|_SIDD_CMP_EQUAL_ANY|
     _SIDD_POSITIVE_POLARITY|_SIDD_LEAST_SIGNIFICANT) *)
Definition cmpestri_ubyte_eqany_ppol_lsig (a : m128) (la : nat) (b : m128) (lb : nat) :=
  let sa := take la (seq_of_m128 a) in
  let sb := take lb (seq_of_m128 b) in
  let p := mem sa in
  if has p sb then find p sb else 16.

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

Definition chars_to_escape_list := [:: "&"%char; "<"%char; ">"%char; """"%char; "'"%char].
Definition chars_to_escape := m128_of_seq chars_to_escape_list.
Definition num_chars_to_escape := size chars_to_escape_list.

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

Fixpoint sse_html_escape buf ptr m n :=
  match n with
  | 0 => bufaddmem buf ptr m
  | n'.+1 =>
      let p1 := bptradd ptr m in
      if n <= 15 then
        trec_html_escape (bufaddmem buf ptr m) p1 n
      else
        let i := cmpestri_ubyte_eqany_ppol_lsig
            chars_to_escape num_chars_to_escape
            (m128_of_bptr p1) 16 in
        if 16 <= i then
          sse_html_escape buf ptr (m + 16) (n' - 15)
        else
          let buf2 := bufaddmem buf ptr (m + i) in
          let p2 := bptradd ptr (m + i) in
          let c := bptrget p2 in
          let p3 := bptradd p2 1 in
          let: (escptr, escn) := html_escape_byte_table c in
          let buf3 := bufaddmem buf2 escptr escn in
          sse_html_escape buf3 p3 0 (n' - i)
  end.

Definition sse_html_escape_stub s :=
  s_of_buf (sse_html_escape (bufctr [::]) (bptr 0 s) 0 (size s)).

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

Lemma sse_html_escape_ok1 s buf i m n : i + m + n = size s ->
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
    by rewrite trec_html_escape_ok1 /=; first rewrite catA.
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

Lemma sse_html_escape_ok s : sse_html_escape_stub s = html_escape s.
Proof.
  rewrite /sse_html_escape_stub.
  by rewrite sse_html_escape_ok1; first rewrite take0 drop0.
Qed.

Require Import Monomorph.monomorph.

Terminate Monomorphization html_escape_byte_table.

Terminate Monomorphization cmpestri_ubyte_eqany_ppol_lsig.
Terminate Monomorphization chars_to_escape.
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

