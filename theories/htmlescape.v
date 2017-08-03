From mathcomp Require Import all_ssreflect.
Require Import String.
Require Import Ascii.

Local Open Scope string_scope.

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

Definition downcase_char (ch : ascii) :=
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
  | EmptyString => nil
  | String c str' => c :: seq_of_str str'
  end.

Fixpoint str_of_seq s :=
  match s with
  | nil => EmptyString
  | c :: s' => String c (str_of_seq s')
  end.

Lemma str_of_seq_of_str str : str_of_seq (seq_of_str str) = str.
Proof. by elim: str => [|c str /= ->]. Qed.

Lemma seq_of_str_of_seq s : seq_of_str (str_of_seq s) = s.
Proof. by elim: s => [|c s /= ->]. Qed.

Fixpoint eqstr a b :=
  match a, b with
  | EmptyString, EmptyString => true
  | String ca a', String cb b' => (ca == cb) && eqstr a' b'
  | _, _ => false
  end.

Lemma eqstr_eq a b : (eqstr (str_of_seq a) (str_of_seq b)) = (a == b).
Proof.
  elim: b a; first by case.
  move=> c s' IH [] /=.
    by [].
  move=> c' s.
  by rewrite IH.
Qed.

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

Lemma append_cat (s1 s2 : seq ascii) :
  (str_of_seq s1) ++ (str_of_seq s2) = str_of_seq (s1 ++ s2).
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

Definition str_of_char c := String c EmptyString.

Definition str_of_asciicode n := str_of_char (ascii_of_nat n).

Local Notation "c :: str" := (String c str) (at level 60, right associativity).

Fixpoint html_escape str :=
  match str with
  | "" => ""
  | c :: str' =>
      (if c == "&"%char then "&amp;"
      else if c == "<"%char then "&lt;"
      else if c == ">"%char then "&gt;"
      else if c == """"%char then "&quot;"
      else if c == "'"%char then "&#39;"
      else str_of_char c) ++
      html_escape str'
  end.

Goal html_escape "abc&def<>""'" = "abc&amp;def&lt;&gt;&quot;&#39;". by []. Qed.

Definition firstn n str := substring 0 n str.

Fixpoint aftern n str {struct str} :=
  match n with
  | 0 => str
  | n'.+1 =>
      match str with
      | "" => str
      | ch :: str' => aftern n' str'
      end
  end.

Lemma aftern_drop n s : aftern n (str_of_seq s) = str_of_seq (drop n s).
Proof.
  elim: s n.
    by move=> [|n].
  move=> c s IH n.
  case: n; first by [].
  move=> n /=.
  by rewrite IH.
Qed.

Lemma aftern_substring n str : aftern n str = substring n (length str - n) str.
Proof.
  rewrite -(str_of_seq_of_str str).
  move: (seq_of_str str) => s.
  clear str.
  rewrite aftern_drop.
  rewrite substring_take_drop.
  congr (str_of_seq _).
  rewrite length_size.
  rewrite [take (size _ - _) _]take_oversize.
    by [].
  by rewrite size_drop.
Qed.

Lemma after0 str : aftern 0 str = str.
Proof.
  rewrite -(str_of_seq_of_str str).
  move: (seq_of_str str) => s.
  clear str.
  by rewrite aftern_drop drop0.
Qed.

Lemma firstn_aftern n str : firstn n str ++ aftern n str = str.
Proof.
  rewrite /firstn aftern_substring -(str_of_seq_of_str str).
  move: (seq_of_str str) => s.
  clear str.
  rewrite 2!substring_take_drop append_cat.
  congr (str_of_seq _).
  rewrite drop0 length_size [take (size _ - _) _]take_oversize.
    by rewrite cat_take_drop.
  by rewrite size_drop.
Qed.

Fixpoint start_with prefix str :=
  match prefix with
  | "" => Some 0
  | pch :: prefix' =>
      match str with
      | "" => None
      | sch :: str' =>
          if pch == sch then
            if start_with prefix' str' is Some n then Some n.+1 else None
          else None
      end
  end.

(* case insensitive version of start_with *)
Fixpoint start_with_ci prefix str :=
  match prefix with
  | "" => Some 0
  | pch :: prefix' =>
      match str with
      | "" => None
      | sch :: str' =>
          if downcase_char pch == downcase_char sch then
            if start_with_ci prefix' str' is Some n then Some n.+1 else None
          else None
      end
  end.

Definition nat_of_digit (ch : ascii) :=
  match ch with
  | "0"%char => Some 0
  | "1"%char => Some 1
  | "2"%char => Some 2
  | "3"%char => Some 3
  | "4"%char => Some 4
  | "5"%char => Some 5
  | "6"%char => Some 6
  | "7"%char => Some 7
  | "8"%char => Some 8
  | "9"%char => Some 9
  | _ => None
  end.

Fixpoint decode_decimal_prefix str :=
  match str with
  | ch :: str' => 
      if nat_of_digit ch is Some d then
        let (n, len) := decode_decimal_prefix str' in
        (d * 10 ^ len + n, len.+1)
      else
        (0, 0)
  | "" => (0, 0)
  end.

Definition nat_of_hexdig (ch : ascii) :=
  match ch with
  | "0"%char => Some 0
  | "1"%char => Some 1
  | "2"%char => Some 2
  | "3"%char => Some 3
  | "4"%char => Some 4
  | "5"%char => Some 5
  | "6"%char => Some 6
  | "7"%char => Some 7
  | "8"%char => Some 8
  | "9"%char => Some 9
  | "a"%char => Some 10
  | "b"%char => Some 11
  | "c"%char => Some 12
  | "d"%char => Some 13
  | "e"%char => Some 14
  | "f"%char => Some 15
  | "A"%char => Some 10
  | "B"%char => Some 11
  | "C"%char => Some 12
  | "D"%char => Some 13
  | "E"%char => Some 14
  | "F"%char => Some 15
  | _ => None
  end.

Fixpoint decode_hex_prefix str :=
  match str with
  | ch :: str' => 
      if nat_of_hexdig ch is Some d then
        let (n, len) := decode_hex_prefix str' in
        (d * 16 ^ len + n, len.+1)
      else
        (0, 0)
  | "" => (0, 0)
  end.

Fixpoint html_unescape str :=
  match str with
  | "" => ""
  | "&" :: str1 =>
      if start_with "amp;" str1 is Some n then "&" ++ html_unescape (aftern n str1)
      else if start_with "lt;" str1 is Some n then "<" ++ html_unescape (aftern n str1)
      else if start_with "gt;" str1 is Some n then ">" ++ html_unescape (aftern n str1)
      else if start_with "quot;" str1 is Some n then """" ++ html_unescape (aftern n str1)
      else if start_with_ci "#x" str1 is Some n1 then
        let str2 := aftern n1 str1 in
        let: (m, n2) := decode_hex_prefix str2 in
        if 0 < n2 then
          let str3 := aftern n2 str2 in
          if start_with ";" str3 is Some n3 then
            str_of_asciicode m ++ html_unescape (aftern n3 str3)
          else
            "&" :: html_unescape str1
        else
          "&" :: html_unescape str1
      else if start_with "#" str1 is Some n1 then
        let str2 := aftern n1 str1 in
        let: (m, n2) := decode_decimal_prefix str2 in
        if 0 < n2 then
          let str3 := aftern n2 str2 in
          if start_with ";" str3 is Some n3 then
            str_of_asciicode m ++ html_unescape (aftern n3 str3)
          else
            "&" :: html_unescape str1
        else
          "&" :: html_unescape str1
      else "&" :: html_unescape str1
  | ch :: str1 => str_of_char ch ++ html_unescape str1
  end.

Lemma html_unescape_escape str : html_unescape (html_escape str) = str.
Proof.
  elim: str => [|c str IH /=]; first by [].
  case: eqP => [-> /=|/eqP not_amp]; first by rewrite after0 IH.
  case: eqP => [-> /=|/eqP not_lt]; first by rewrite after0 IH.
  case: eqP => [-> /=|/eqP not_gt]; first by rewrite after0 IH.
  case: eqP => [-> /=|/eqP not_quot]; first by rewrite after0 IH.
  case: eqP => [-> /=|/eqP not_apos]; first by rewrite after0 IH.
  rewrite [_ ++ _]/=.
  move: not_amp not_lt not_gt not_quot not_apos.
  case: c => b1 b2 b3 b4 b5 b6 b7 b8.
  case: b1; case: b2; case: b3; case: b4;
  case: b5; case: b6; case: b7; case: b8; by rewrite /= IH.
Qed.



