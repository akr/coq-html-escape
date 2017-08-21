From mathcomp Require Import all_ssreflect.
Require Import String.
Require Import Ascii.

Require Import htmlescape.listutils.
Require Import htmlescape.assoc.

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

Lemma isSome_exists {T : Type} (x : option T) : isSome x -> exists v, x = Some v.
Proof.
  case: x.
    move=> v' _.
    by exists v'.
  by [].
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

