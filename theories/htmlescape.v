From mathcomp Require Import all_ssreflect.
Require Import String.
Require Import Ascii.

Require Import htmlescape.listutils.

Local Open Scope string_scope. (* enable "string-literal" and str ++ str *)
Local Open Scope seq_scope. (* prefer seq ++ seq over str ++ str *)

Definition eqascii a b :=
  let: Ascii a1 a2 a3 a4 a5 a6 a7 a8 := a in
  let: Ascii b1 b2 b3 b4 b5 b6 b7 b8 := b in
  (a1 == b1) && (a2 == b2) && (a3 == b3) && (a4 == b4) &&
  (a5 == b5) && (a6 == b6) && (a7 == b7) && (a8 == b8).

Lemma eqasciiP : Equality.axiom eqascii.
Proof.
  move=> a b.
  apply: (iffP idP).
    case: a => a1 a2 a3 a4 a5 a6 a7 a8.
    case: b => b1 b2 b3 b4 b5 b6 b7 b8.
    rewrite /eqascii.
    do 7 rewrite andbC => /andP [] /eqP ->.
    by move=> /eqP ->.
  move=> ->.
  case: b => b1 b2 b3 b4 b5 b6 b7 b8 /=.
  by do 8 rewrite eq_refl.
Qed.

Canonical ascii_eqMixin := EqMixin eqasciiP.
Canonical ascii_eqType := Eval hnf in EqType ascii ascii_eqMixin.

Definition downcase_ascii (ch : ascii) :=
  match ch with
  | "A"%char => "a"%char
  | "B"%char => "b"%char
  | "C"%char => "c"%char
  | "D"%char => "d"%char
  | "E"%char => "e"%char
  | "F"%char => "f"%char
  | "G"%char => "g"%char
  | "H"%char => "h"%char
  | "I"%char => "i"%char
  | "J"%char => "j"%char
  | "K"%char => "k"%char
  | "L"%char => "l"%char
  | "M"%char => "m"%char
  | "N"%char => "n"%char
  | "O"%char => "o"%char
  | "P"%char => "p"%char
  | "Q"%char => "q"%char
  | "R"%char => "r"%char
  | "S"%char => "s"%char
  | "T"%char => "t"%char
  | "U"%char => "u"%char
  | "V"%char => "v"%char
  | "W"%char => "w"%char
  | "X"%char => "x"%char
  | "Y"%char => "y"%char
  | "Z"%char => "z"%char
  | _ => ch
  end.

Fixpoint seq_of_str str :=
  match str with
  | "" => nil
  | String c str' => c :: (seq_of_str str')
  end.

Fixpoint str_of_seq s :=
  match s with
  | nil => ""
  | c :: s' => String c (str_of_seq s')
  end.

Lemma str_of_seq_of_str str : str_of_seq (seq_of_str str) = str.
Proof. by elim: str => [|c str /= ->]. Qed.

Lemma seq_of_str_of_seq s : seq_of_str (str_of_seq s) = s.
Proof. by elim: s => [|c s /= ->]. Qed.

Coercion seq_of_str : string >-> seq.

Definition eqstr a b := seq_of_str a == seq_of_str b.

Lemma eqstr_eq a b : (eqstr (str_of_seq a) (str_of_seq b)) = (a == b).
Proof. by rewrite /eqstr 2!seq_of_str_of_seq. Qed.

Lemma eqstrP : Equality.axiom eqstr.
Proof.
  move=> a' b'.
  rewrite -(str_of_seq_of_str a') -(str_of_seq_of_str b').
  move: (seq_of_str a') (seq_of_str b') => a b.
  clear a' b'.
  rewrite eqstr_eq.
  apply: (iffP idP).
    by move=> /eqP ->.
  rewrite -{2}(seq_of_str_of_seq a) => ->.
  by rewrite seq_of_str_of_seq.
Qed.

Canonical string_eqMixin := EqMixin eqstrP.
Canonical string_eqType := Eval hnf in EqType string string_eqMixin.

Definition sindex c (s : seq ascii) :=
  let i := seq.index c s in
  if i < size s then
    Some i
  else
    None.

Definition str_of_char c := String c EmptyString.

Definition str_of_asciicode n := str_of_char (ascii_of_nat n).

Lemma isSome_exists {T : Type} (x : option T) : isSome x -> exists v, x = Some v.
Proof.
  case: x.
    move=> v' _.
    by exists v'.
  by [].
Qed.

Definition assoc_if {A B : Type} (p : A -> bool) (al : seq (A * B)) : option (A * B) :=
  List.find (p \o fst) al.

Definition rassoc_if {A B : Type} (p : B -> bool) (al : seq (A * B)) : option (A * B) :=
  List.find (p \o snd) al.

Definition assoc {A : eqType} {B : Type} (a : A) (al : seq (A * B)) : option (A * B) :=
  assoc_if (pred1 a) al.

Definition rassoc {A : Type} {B : eqType} (b : B) (al : seq (A * B)) : option (A * B) :=
  rassoc_if (pred1 b) al.

Definition assoc_default {A : eqType} {B : Type} (d : B) (a : A) (al : seq (A * B)) :=
  if assoc a al is Some (k,v) then v else d.

Definition rassoc_default {A : Type} {B : eqType} (d : A) (b : B) (al : seq (A * B)) :=
  if rassoc b al is Some (k,v) then k else d.

Lemma associf_filter A B (p : A -> bool) (al : seq (A * B)) :
  assoc_if p al = if filter (p \o fst) al is x :: _ then Some x else None.
Proof.
  elim: al => [|y al IH /=]; first by [].
  case: ifP; first by [].
  by rewrite -IH.
Qed.

Lemma rassocif_filter A B (p : B -> bool) (al : seq (A * B)) :
  rassoc_if p al = if filter (p \o snd) al is x :: _ then Some x else None.
Proof.
  elim: al => [|y al IH /=]; first by [].
  case: ifP; first by [].
  by rewrite -IH.
Qed.

Fixpoint map_prefix {T1 T2 : Type} (f : T1 -> option T2) (s : seq T1) : seq T2 :=
  match s with
  | nil => nil
  | e :: s' =>
      if f e is Some v then
        v :: map_prefix f s'
      else
        nil
  end.

Lemma map_prefix_cat {T1 T2 : Type} (f : T1 -> option T2) e s1 s2 :
  f e = None -> map_prefix f (s1 ++ e :: s2) = map_prefix f s1.
Proof.
  move=> H.
  elim: s1.
    simpl.
    by rewrite H.
  move=> a s IH /=.
  by rewrite IH.
Qed.

Lemma size_map_prefix_full {T1 T2 : Type} (f : T1 -> option T2) s :
  (size (map_prefix f s) == size s) = (all (isSome \o f) s).
Proof.
  elim: s.
    by [].
  move=> e s IH /=.
  case: (f e) => [_ /=|]; last by [].
  by rewrite eqSS.
Qed.

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

Fixpoint start_with (prefix s : seq ascii) :=
  match prefix with
  | nil => Some 0
  | pch :: prefix' =>
      match s with
      | nil => None
      | sch :: s' =>
          if pch == sch then
            if start_with prefix' s' is Some n then Some n.+1 else None
          else None
      end
  end.

(* case insensitive version of start_with *)
Fixpoint ci_start_with (prefix s : seq ascii) :=
  match prefix with
  | nil => Some 0
  | pch :: prefix' =>
      match s with
      | nil => None
      | sch :: s' =>
          if downcase_ascii pch == downcase_ascii sch then
            if ci_start_with prefix' s' is Some n then Some n.+1 else None
          else None
      end
  end.

Definition digit_chars := [::
  ("0"%char, 0);
  ("1"%char, 1);
  ("2"%char, 2);
  ("3"%char, 3);
  ("4"%char, 4);
  ("5"%char, 5);
  ("6"%char, 6);
  ("7"%char, 7);
  ("8"%char, 8);
  ("9"%char, 9)
].

Definition nat_of_digit (ch : ascii) :=
  if assoc ch digit_chars is Some (_, d) then Some d else None.

Definition isdigit ch := isSome (assoc ch digit_chars).

Lemma isdigit_natof c : isdigit c = isSome (nat_of_digit c).
Proof.
  rewrite /isdigit /nat_of_digit.
  by case: (assoc c digit_chars) => [[]|].
Qed.

Definition decode_decimal_prefix s :=
  let ds := map_prefix nat_of_digit s in
  let v := foldl (fun u d => u * 10 + d) 0 ds in
  (v, size ds).

Definition decode_decimal s :=
  let (v, n) := decode_decimal_prefix s in
  if n == size s then
    Some v
  else
    None.

Lemma decode_dec_eqsize digs : isSome (decode_decimal digs) =
  (size (map_prefix nat_of_digit digs) == size digs).
Proof.
  rewrite /decode_decimal /decode_decimal_prefix /=.
  by case: ifP.
Qed.

Lemma decode_dec_all_isdigit digs : isSome (decode_decimal digs) = all isdigit digs.
Proof.
  rewrite decode_dec_eqsize size_map_prefix_full.
  elim: digs; first by [].
  move=> c s IH /=.
  by rewrite isdigit_natof IH.
Qed.

Definition xdigit_chars := [::
  ("0"%char, 0);
  ("1"%char, 1);
  ("2"%char, 2);
  ("3"%char, 3);
  ("4"%char, 4);
  ("5"%char, 5);
  ("6"%char, 6);
  ("7"%char, 7);
  ("8"%char, 8);
  ("9"%char, 9);
  ("a"%char, 10);
  ("b"%char, 11);
  ("c"%char, 12);
  ("d"%char, 13);
  ("e"%char, 14);
  ("f"%char, 15);
  ("A"%char, 10);
  ("B"%char, 11);
  ("C"%char, 12);
  ("D"%char, 13);
  ("E"%char, 14);
  ("F"%char, 15)
].

Definition nat_of_xdigit (ch : ascii) :=
  if assoc ch xdigit_chars is Some (_, d) then Some d else None.

Definition isxdigit ch :=
  if assoc ch xdigit_chars is Some _ then true else false.

Lemma isxdigit_natof c : isxdigit c = isSome (nat_of_xdigit c).
Proof.
  rewrite /isxdigit /nat_of_xdigit.
  by case: (assoc c xdigit_chars) => [[]|].
Qed.

Definition decode_hex_prefix s :=
  let ds := map_prefix nat_of_xdigit s in
  let v := foldl (fun u d => u * 16 + d) 0 ds in
  (v, size ds).

Definition decode_hex s :=
  let (v, n) := decode_hex_prefix s in
  if n == size s then
    Some v
  else
    None.

Lemma decode_hex_eqsize xdigs : isSome (decode_hex xdigs) =
  (size (map_prefix nat_of_xdigit xdigs) == size xdigs).
Proof.
  rewrite /decode_hex /decode_hex_prefix /=.
  by case: ifP.
Qed.

Lemma decode_hex_all_isxdigit xdigs : isSome (decode_hex xdigs) = all isxdigit xdigs.
Proof.
  rewrite decode_hex_eqsize size_map_prefix_full.
  elim: xdigs; first by [].
  move=> c s IH /=.
  by rewrite isxdigit_natof IH.
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

Lemma size_map_prefix_xdigs xdigs :
  all isxdigit xdigs -> size (map_prefix nat_of_xdigit xdigs) = size xdigs.
Proof.
  elim: xdigs; first by [].
  move=> c s IH /= /andP [].
  rewrite isxdigit_natof => /isSome_exists [] d -> /= H.
  by rewrite IH.
Qed.

Lemma size_map_prefix_digs digs :
  all isdigit digs -> size (map_prefix nat_of_digit digs) = size digs.
Proof.
  elim: digs; first by [].
  move=> c s IH /= /andP [].
  rewrite isdigit_natof=> /isSome_exists [] d -> /= H.
  by rewrite IH.
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
  simpl.
  case: eqP => [<-|/eqP /negbTE not_amp]; first by [].
  case: eqP => [<-|/eqP /negbTE not_lt]; first by [].
  case: eqP => [<-|/eqP /negbTE not_gt]; first by [].
  case: eqP => [<-|/eqP /negbTE not_quot]; first by [].
  case: eqP => [<-|/eqP /negbTE not_apos]; first by [].
  rewrite /html_escape_byte /=.
  by rewrite not_amp not_lt not_gt not_quot not_apos.
Qed.

Lemma trec_html_escape_ok s : trec_html_escape_stub s = html_escape s.
Proof.
  rewrite /trec_html_escape_stub.
  rewrite -[html_escape s]cat0s.
  move: [::] => buf.
  rewrite -{3}[s]drop0.
  move: (Logic.eq_refl (size s)).
  rewrite -{1}[size s]add0n.
  move: 0 => i.
  move: {1 3}(size s) => j.
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
  move Ha: (if "&"%char == c then _ else _) => a.
  rewrite -{2}[s]Hs drop_size_cat; last first.
    rewrite size_takel; first by [].
    by rewrite -Hij leq_addr.
  rewrite /= {}Ha catA.
  rewrite /bptradd /= addn1.
  case: a.
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

Lemma seq_of_m128_of_seq s :
  take (size s) (seq_of_m128 (m128_of_seq s)) = take (minn (size s) 16) s.
Proof.
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

Definition m128_of_bptr ptr := m128_of_seq (s_of_bptr ptr).

(* _mm_cmpestri(a, la, b, lb,
     _SIDD_UBYTE_OPS|_SIDD_CMP_EQUAL_ANY|
     _SIDD_POSITIVE_POLARITY|_SIDD_LEAST_SIGNIFICANT) *)
Definition cmpestri_ubyte_eqany_ppol_lsig (a : m128) (la : nat) (b : m128) (lb : nat) :=
  let sa := take la (seq_of_m128 a) in
  let sb := take lb (seq_of_m128 b) in
  let p x := x \in sa in
  let i := find p sb in
  if i == size sb then 16 else i.

Definition need_to_escape := m128_of_seq [:: "&"%char; "<"%char; ">"%char; """"%char; "'"%char].

Fixpoint sse_html_escape buf ptr n :=
  match n with
  | 0 => buf
  | n'.+1 =>
      if n < 16 then
        trec_html_escape buf ptr n
      else
        let i := cmpestri_ubyte_eqany_ppol_lsig
            need_to_escape 5 (m128_of_bptr ptr) 16 in
        if i == 16 then
          sse_html_escape (bufaddmem buf ptr 16) (bptradd ptr 16) (n' - 15)
        else
          let buf2 := bufaddmem buf ptr i in
          let ptr2 := bptradd ptr i in
          let c := bptrget ptr2 in
          let ptr3 := bptradd ptr2 1 in
          let: (escptr, escn) := html_escape_byte c in
          let buf3 := bufaddmem buf2 escptr escn in
          sse_html_escape buf3 ptr3 (n' - i)
  end.

Definition sse_html_escape_stub s :=
  s_of_buf (sse_html_escape (bufctr [::]) (bptr 0 s) (size s)).

