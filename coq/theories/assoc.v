From mathcomp Require Import all_ssreflect.

Require Import htmlescape.listutils.

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
