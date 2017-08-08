From mathcomp Require Import all_ssreflect.
Require Import String.
Require Import Ascii.

Local Open Scope string_scope. (* enable "string-literal" and str ++ str *)
Local Open Scope seq_scope. (* prefer seq ++ seq over str ++ str *)

Local Notation "c & str" := (String c str) (at level 60, right associativity).

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
  | c & str' => c :: (seq_of_str str')
  end.

Fixpoint str_of_seq s :=
  match s with
  | nil => ""
  | c :: s' => c & (str_of_seq s')
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

Lemma cons_str_of_seq c s : c & str_of_seq s = str_of_seq (c :: s).
Proof. by []. Qed.

Lemma append_cat (s1 s2 : seq ascii) :
  append (str_of_seq s1) (str_of_seq s2) = str_of_seq (s1 ++ s2).
Proof. by elim: s1 => [|c s /= ->]. Qed.

Lemma length_size (s : seq ascii) : length (str_of_seq s) = size s.
Proof. by elim: s => [|c s /= ->]. Qed.

Lemma substring_take_drop m n s :
  substring m n (str_of_seq s) = str_of_seq (take n (drop m s)).
Proof.
  elim: s m n => [m n|c s IH m n /=].
    by case: m; case: n.
  case: m => [|m].
    by case: n => [|n]; last rewrite IH drop0.
  by case: n => [|n]; rewrite IH.
Qed.

Definition stake n (str : string) := str_of_seq (take n str).

(* usable for decreasing argument *)
Fixpoint sdrop n str {struct str} :=
  match n with
  | 0 => str
  | n'.+1 =>
      match str with
      | "" => str
      | ch & str' => sdrop n' str'
      end
  end.

Lemma sdrop_drop n s : sdrop n (str_of_seq s) = str_of_seq (drop n s).
Proof.
  elim: s n.
    by move=> [|n].
  move=> c s IH n.
  case: n; first by [].
  move=> n /=.
  by rewrite IH.
Qed.

(*
Lemma sdrop_substring n str : sdrop n str = substring n (length str - n) str.
Proof.
  rewrite -(str_of_seq_of_str str).
  move: (seq_of_str str) => s.
  clear str.
  rewrite sdrop_drop.
  rewrite substring_take_drop.
  congr (str_of_seq _).
  rewrite length_size.
  rewrite [take (size _ - _) _]take_oversize.
    by [].
  by rewrite size_drop.
Qed.
*)

Lemma sdrop0 str : sdrop 0 str = str.
Proof.
  rewrite -(str_of_seq_of_str str).
  move: (seq_of_str str) => s.
  clear str.
  by rewrite sdrop_drop drop0.
Qed.

Lemma stake_sdrop n str : append (stake n str) (sdrop n str) = str.
Proof.
  rewrite -(str_of_seq_of_str str).
  move: (seq_of_str str) => s.
  by rewrite /stake sdrop_drop seq_of_str_of_seq append_cat cat_take_drop.
Qed.

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
      (if assoc c html_escape_al is Some (_, e) then
        "&" ++ e ++ ";"
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

Lemma isdigit_natofdigit_some c : isdigit c = isSome (nat_of_digit c).
Proof.
  rewrite /isdigit /nat_of_digit.
  by case: (assoc c digit_chars) => [[]|].
Qed.

Lemma nat_of_digit_isdigit c : (nat_of_digit c != None) = isdigit c.
Proof.
  rewrite /nat_of_digit /isdigit.
  case: (assoc c digit_chars).
    by case.
  by [].
Qed.

(*
Lemma isdigit_nat_of_digit_some c : isdigit c -> exists d, nat_of_digit c = Some d.
Proof.
  rewrite /isdigit.
  case: (nat_of_digit c).
    move=> n _.
    by exists n.
  by [].
Qed.

Lemma nat_of_digit_some_isdigit c : (exists d, nat_of_digit c = Some d) -> isdigit c.
Proof.
  case => d.
  by rewrite /isdigit => ->.
Qed.

Lemma isdigit_nat_of_digit_none c : ~~ isdigit c -> nat_of_digit c = None.
Proof.
  rewrite /isdigit.
  by case: (nat_of_digit c).
Qed.

Require Import Sumbool.

Lemma nat_of_digit_dec c :
  { (exists d, nat_of_digit c = Some d) } + { nat_of_digit c = None }.
Proof.
  move Hb: (isdigit c) => b.
  case: b Hb.
    move=> Hb.
    left.
    by apply isdigit_nat_of_digit_some.
  move/negbT => Hb.
  right.
  by apply isdigit_nat_of_digit_none.
Qed.
*)

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
  by rewrite isdigit_natofdigit_some IH.
Qed.

Definition dec_entref s :=
  if start_with "#" s is Some n1 then
    let s2 := drop n1 s in
    if s2 is nil then
      None
    else
      oapp (Some \o ascii_of_nat) None (decode_decimal s2)
  else
    None.

Lemma decode_decimal_prefix_all_digit s v n :
  decode_decimal_prefix s = (v, n) -> all isdigit (take n s).
Proof.
  rewrite /decode_decimal_prefix => [] [] _.
  elim: s n => [|c s IH n /=]; first by [].
  case: n => [|n /=]; first by [].
  rewrite {1}/nat_of_digit {1}/isdigit.
  case: (assoc c digit_chars); last by [].
  case=> _ d /= /eqP.
  rewrite eqSS => /eqP.
  by apply IH.
Qed.

Lemma decode_decimal_all_digit s m :
  decode_decimal s = Some m -> all isdigit s.
Proof.
  rewrite /decode_decimal /decode_decimal_prefix.
  case: eqP => [H _|]; last by [].
  clear m.
  elim: s H => [|c s IH /=]; first by [].
  rewrite {1}/nat_of_digit {1}/isdigit.
  case: (assoc c digit_chars); last by [].
  move=> [] _ /= _ /eqP.
  by rewrite eqSS => /eqP.
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

Lemma xdigit_max c p : assoc c xdigit_chars = Some p -> p.2 < 16.
Proof.
  simpl.
  do 22 (case: eqP => [_ [] <-|_]; first by []).
  by [].
Qed.

Definition nat_of_xdigit (ch : ascii) :=
  if assoc ch xdigit_chars is Some (_, d) then Some d else None.

Definition isxdigit ch :=
  if assoc ch xdigit_chars is Some _ then true else false.

Lemma isxdigit_natofxdigit_some c : isxdigit c = isSome (nat_of_xdigit c).
Proof.
  rewrite /isxdigit /nat_of_xdigit.
  by case: (assoc c xdigit_chars) => [[]|].
Qed.

(*
Lemma isxdigit_natof c : isxdigit c -> exists d, d < 16 /\ nat_of_xdigit c = Some d.
Proof.
  rewrite /isxdigit /nat_of_xdigit.
  case Ha: (assoc c xdigit_chars) => [p|]; last by [].
  move=> _.
  exists p.2.
  split.
    by apply (xdigit_max c).
  clear Ha.
  by case: p.
Qed.
*)

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
  by rewrite isxdigit_natofxdigit_some IH.
Qed.

Definition hex_entref s :=
  if ci_start_with "#x" s is Some n1 then
    let s2 := drop n1 s in
    if s2 is nil then
      None
    else
      oapp (Some \o ascii_of_nat) None (decode_hex s2)
  else
    None.

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
  rewrite isxdigit_natofxdigit_some => /isSome_exists [] d -> /= H.
  by rewrite IH.
Qed.

Lemma size_map_prefix_digs digs :
  all isdigit digs -> size (map_prefix nat_of_digit digs) = size digs.
Proof.
  elim: digs; first by [].
  move=> c s IH /= /andP [].
  rewrite isdigit_natofdigit_some=> /isSome_exists [] d -> /= H.
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
        clear raw escaped => c raw escaped not_amp spec unesc.
        case: c not_amp => b1 b2 b3 b4 b5 b6 b7 b8.
        case: b1; case: b2; case: b3; case: b4;
        case: b5; case: b6; case: b7; case: b8; by rewrite /= unesc.
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

