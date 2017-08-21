From mathcomp Require Import all_ssreflect.

Section ListUtils.

Variable T : Type.
Implicit Type s : seq T.

Lemma drop_drop s a b : drop a (drop b s) = drop (a + b) s.
Proof.
elim: s a b => // ? ? H ? [|?]; by [rewrite drop0 addn0 | rewrite H addnS].
Qed.

Lemma take_take s b a : a <= b -> take a (take b s) = take a s.
Proof.
elim: s a b => // h t H [ [] | a] // [ | b] //=.
rewrite ltnS => ?; by rewrite H.
Qed.

Lemma catr_take n (s1 s2 : seq T) : s1 ++ take n s2 = take (size s1 + n) (s1 ++ s2).
Proof. by rewrite take_cat -ltn_subRL subnn ltn0 addnC addnK. Qed.

Lemma drop_take_inv m n s : drop m (take (m + n) s) = take n (drop m s).
Proof.
  elim: s m n => [|a l IH m n]; first by [].
  by case: m => [|m /=]; [rewrite 2!drop0 add0n|rewrite -IH].
Qed.

End ListUtils.


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

