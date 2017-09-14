From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From mathcomp Require Import div prime.

Require Coq.Numbers.Natural.Peano.NPeano.

Section NatUtils.

(* lt *)

Lemma ltneqWbr (b:bool) (m n:nat) : (m < n) || (m == n) && b -> m <= n.
Proof.
  case: b; first by rewrite andbT orbC -leq_eqVlt.
  rewrite andbF orbF.
  by apply ltnW.
Qed.

(* add *)

Lemma plus_id_l : forall n m, (n + m == m) = (n == 0).
Proof.
  move=> n m.
  by rewrite -[n == 0](eqn_add2r m) add0n.
Qed.

(* sub *)

Lemma eqn_sub2l p m n : m <= p -> n <= p -> (p - m == p - n) = (m == n).
Proof.
  move=> Hm Hn.
  symmetry.
  case: eqP => [->|Hmn].
    by rewrite eq_refl.
  apply/sym_eq/eqP => Hpmn.
  apply Hmn.
  by rewrite -(subKn Hm) Hpmn (subKn Hn).
Qed.

(* mul *)

(* div, mod *)

Lemma x_mod_yz_div_z : forall x y z,
  0 < y -> 0 < z ->
  x %% (y * z) %/ z = (x %/ z) %% y.
Proof.
  move=> x y z Hy Hz.
  have Hyz: 0 < y * z.
    rewrite lt0n muln_eq0.
    apply/norP.
    rewrite -2!lt0n.
    by split.
  rewrite {2}(divn_eq x (y * z)) mulnA divnMDl; last by [].
  rewrite modnMDl.
  rewrite [((x %% (y * z)) %/ z) %% y]modn_small; first by [].
  rewrite ltn_divLR; last by [].
  by apply ltn_pmod.
Qed.

Lemma divnS_mod m d : (m %% d.+1) %/ d.+1 = 0.
Proof.
  by rewrite divn_small; last apply ltn_pmod.
Qed.

Lemma divn_mod m d : 0 < d -> (m %% d) %/ d = 0.
Proof.
  case: d => [|d Hd]; first by [].
  by rewrite divnS_mod.
Qed.

Lemma modnBmr m n d : n <= m -> m - n %% d = m - n %[mod d].
Proof.
  move=> Hnm.
  rewrite {2}(divn_eq n d) addnC subnDA.
  rewrite -[(m - n %% d - n %/ d * d) %% d](modnMDl (n %/ d)).
  rewrite subnKC; first by [].
  rewrite -(leq_add2r (n %% d)) -divn_eq subnK; first by [].
  apply leq_trans with (n:=n); last by [].
  apply leq_mod.
Qed.

Lemma modnBmr_small m d : (d - m %% d.+1) %% d.+1 = d - m %% d.+1.
Proof.
  by rewrite modn_small; last rewrite ltnS leq_subr.
Qed.

Lemma eqn_modB p m n d : m <= p -> n <= p -> ((p - m) == (p - n) %[mod d]) = (m == n %[mod d]).
Proof.
  wlog: m n / m <= n => [H|Hmn Hm Hn].
    case: (leqP m n); first by apply H.
    rewrite [RHS]eq_sym [LHS]eq_sym => Hnm Hm Hn.
    apply: H Hn Hm.
    by apply ltnW.
  rewrite eqn_mod_dvd; last by apply leq_sub2l.
  rewrite eq_sym eqn_mod_dvd; last by [].
  by rewrite subnAC subKn.
Qed.

Lemma ndvdn_modSn m d : ~~(d %| m.+1) -> m.+1 %% d = (m %% d).+1.
Proof.
  case: d => [|d H]; first by [].
  rewrite -addn1 -modnDml addn1 modn_small; first by [].
  rewrite /dvdn -[0](@modn_small 0 d.+1) in H; last by [].
  rewrite -(eqn_modDr d) addSnnS add0n modnDr [d %% d.+1]modn_small in H;last by [].
  by rewrite ltnS ltn_neqAle H andTb -ltnS ltn_pmod.
Qed.

Lemma dvdn_modSn m d : d %| m.+1 -> m.+1 %% d = 0.
Proof. by rewrite /dvdn => /eqP. Qed.

Lemma ndvdn_divSn m d : ~~(d %| m.+1) -> m.+1 %/ d = m %/ d.
Proof.
  case: d => [|d H]; first by [].
  rewrite /dvdn in H.
  rewrite {1}(divn_eq m d.+1) -addnS divnMDl; last by [].
  rewrite [X in _ + X](_ : _ = 0); first by [].
  apply divn_small.
  rewrite /dvdn -[0](@modn_small 0 d.+1) in H; last by [].
  rewrite -(eqn_modDr d) addSnnS add0n modnDr [d %% d.+1]modn_small in H;last by [].
  by rewrite ltnS ltn_neqAle H andTb -ltnS ltn_pmod.
Qed.

Lemma dvdn_divSn m d : d %| m.+1 -> m.+1 %/ d = (m %/ d).+1.
Proof.
  case: d => [|d]; first by [].
  rewrite /dvdn -[0](@modn_small 0 d.+1); last by [].
  rewrite -(eqn_modDr d) addSnnS add0n modnDr [d %% d.+1]modn_small; last by [].
  move/eqP.
  rewrite {2}(divn_eq m d.+1) -addnS => ->.
  by rewrite -mulSnr mulnK.
Qed.

Lemma dvdn_modn m d : d %| m -> m %% d = 0.
Proof. by rewrite /dvdn => /eqP. Qed.

Lemma dvdn_ndvdnS m d : 1 < d -> d %| m -> ~~(d %| m.+1).
Proof.
  move=> Hd Hdvdn.
  rewrite /dvdn -addn1 -modnDml [m %% d]dvdn_modn; last by [].
  by rewrite add0n modn_small.
Qed.

Lemma divn_eq0 m d : 0 < d -> (m %/ d == 0) = (m < d).
Proof.
  move=> Hd.
  by rewrite -(negbK (m %/ d == 0)) ltnNge -lt0n divn_gt0.
Qed.

Lemma dvdn_dvdn_eq1 m d : d %| m -> d %| m.+1 -> d = 1.
Proof.
  move=> H0 H1.
  apply/eqP.
  by rewrite -dvdn1 -(@dvdn_add_eq d m); last rewrite addn1.
Qed.

Lemma ndvdn_modDdp m d : 0 < d -> ~~ (d %| m) -> (m + d.-1) %% d = (m %% d).-1.
Proof.
  case: d => [|dp _ Hndvdn]; first by [].
  rewrite succnK.
  case: m Hndvdn => [|mp Hndvdn]; first by rewrite /dvdn mod0n.
  by rewrite addSnnS modnDr ndvdn_modSn; first rewrite succnK.
Qed.

Lemma ndvdn_divDdp m d : 0 < d -> ~~ (d %| m) -> (m + d.-1) %/ d = (m %/ d).+1.
Proof.
  case: d => [|dp _ Hndvdn]; first by [].
  rewrite succnK.
  case: m Hndvdn => [|mp Hndvdn]; first by rewrite /dvdn mod0n.
  by rewrite addSnnS divnDr; first rewrite divnn /= addn1 ndvdn_divSn.
Qed.

(* even, odd *)

(* expn *)

Lemma ltnDexp m n p q : 1 < m -> q <= n -> q + p < m ^ q -> n + p < m ^ n.
Proof.
  move=> Hm Hqn Hqp.
  rewrite -(subnKC Hqn).
  elim: (n - q) => [|i IH]; first by rewrite addn0.
  rewrite addnS addSn -addn1 expnS.
  rewrite -{1}(@prednK m); last by apply ltnW.
  rewrite -[m.-1.+1]add1n mulnDl mul1n.
  apply leq_add; first by [].
  clear IH Hqp.
  rewrite muln_gt0.
  apply/andP.
  split; first by case: m Hm.
  rewrite expn_gt0.
  apply/orP.
  left.
  by apply ltnW.
Qed.

Lemma leq_MDexp k1 k0 n0 m n : 1 < m -> 0 < n0 -> n0 <= n -> k1 * n0 + k0 <= m ^ n0 -> k1 * n + k0 <= m ^ n.
Proof.
  move=> Hm Hn0 Hn H0.
  rewrite -(subnKC Hn).
  elim: (n - n0) => [|i IH]; first by rewrite addn0.
  rewrite addnS mulnSr -[(n0 + i).+1]addn1 expnD expn1.
  rewrite {2}(_: m=(1 + m.-1)); last first.
    by rewrite add1n prednK; last apply ltnW.
  rewrite [m ^ _ * _]mulnDr muln1 -addnA [k1 + k0]addnC addnA.
  apply leq_add; first by [].
  rewrite expnD -mulnA.
  apply leq_trans with (n:=m ^ n0); last first.
    apply leq_pmulr.
    rewrite muln_gt0 expn_gt0.
    apply/andP.
    split.
      apply/orP.
      left.
      by apply ltnW.
    move: Hm.
    clear H0 IH.
    case: m => [|m]; first by [].
    by rewrite ltnS succnK.
  apply: (leq_trans _ H0).
  apply: (@leq_trans (k1 * n0)).
    by apply leq_pmulr.
  by apply leq_addr.
Qed.

(* pow *)

Lemma pow_expn m n : Nat.pow m n = m ^ n.
Proof.
  by elim: n => [|n IH /=]; last rewrite multE expnS IH.
Qed.

(* log2 *)

Definition log2 n := trunc_log 2 n.

Lemma log2_trunc_log n : Nat.log2 n = log2 n.
Proof.
  case: n => [|n]; first by [].
  have /andP [Hcoq1 Hcoq2] : 2 ^ (Nat.log2 n.+1) <= n.+1 < 2 ^ (Nat.log2 n.+1).+1.
    case: (NPeano.log2_spec n.+1); first by apply/ltP.
    by rewrite !pow_expn => /leP -> /ltP ->.
  have /andP [Hssr1 Hssr2] : 2 ^ (log2 n.+1) <= n.+1 < 2 ^ (log2 n.+1).+1.
    by apply trunc_log_bounds.
  apply/eqP.
  rewrite eqn_leq.
  apply/andP.
  split; by rewrite -ltnS -(@ltn_exp2l 2); first apply: (@leq_ltn_trans n.+1).
Qed.

Lemma log2_pow2 a : log2 (2 ^ a) = a.
Proof.
  rewrite -log2_trunc_log -pow_expn.
  by rewrite NPeano.Nat.log2_pow2; last apply/leP.
Qed.

Lemma log2_pred_pow2 a : log2 (2 ^ a).-1 = a.-1.
Proof.
  case: a => [|a]; first by [].
  rewrite -log2_trunc_log -pow_expn.
  by rewrite NPeano.Nat.log2_pred_pow2; last apply/ltP.
Qed.

Lemma log2_1 : log2 1 = 0.
Proof. by []. Qed.

Lemma log2_2 : log2 2 = 1.
Proof. by []. Qed.

Lemma log2_pos a : 1 < a -> 0 < log2 a.
Proof.
  rewrite -log2_trunc_log => H.
  by apply/ltP/NPeano.Nat.log2_pos/ltP.
Qed.

Lemma iff_eq (a b : bool) : (a <-> b) -> a = b.
Proof.
  rewrite /iff => - [/implyP H] /implyP.
  by case: a b H; case.
Qed.

Lemma log2_null a : (log2 a == 0) = (a <= 1).
Proof.
  apply iff_eq.
  case: (NPeano.Nat.log2_null a).
  rewrite log2_trunc_log => Hcoq1 Hcoq2.
  split => H.
    by apply/leP/Hcoq1/eqP.
  by apply/eqP/Hcoq2/leP.
Qed.

Lemma log2_le_mono a b : a <= b -> log2 a <= log2 b.
Proof.
  move=> H.
  rewrite -2!log2_trunc_log.
  by apply/leP/NPeano.Nat.log2_le_mono/leP.
Qed.

Lemma log2_lt_cancel a b : log2 a < log2 b -> a < b.
Proof.
  move=> H.
  apply/ltP/NPeano.Nat.log2_lt_cancel/ltP.
  by rewrite 2!log2_trunc_log.
Qed.

Lemma log2_le_pow2 a b : 0 < a -> (2 ^ b <= a) = (b <= log2 a).
Proof.
  move=> Ha.
  case: (NPeano.Nat.log2_le_pow2 a b); first by apply/ltP.
  rewrite pow_expn log2_trunc_log => Hcoq1 Hcoq2.
  apply iff_eq.
  split => H.
    by apply/leP/Hcoq1/leP.
  by apply/leP/Hcoq2/leP.
Qed.

Lemma leq_pow2_log2 a b : (2 ^ b <= a) -> (b <= log2 a).
Proof.
  case: a => [|a H].
    by rewrite leqNgt expn_gt0.
  by rewrite -log2_le_pow2.
Qed.

Lemma leq_log2_pow2 a b : 0 < a -> (b <= log2 a) -> (2 ^ b <= a).
Proof.
  move=> H.
  by rewrite -log2_le_pow2.
Qed.

Lemma log2_lt_pow2 a b : 0 < a -> (a < 2 ^ b) = (log2 a < b).
Proof.
  move=> Ha.
  case: (NPeano.Nat.log2_lt_pow2 a b); first by apply/ltP.
  rewrite pow_expn log2_trunc_log => Hcoq1 Hcoq2.
  apply iff_eq.
  split => H.
    by apply/ltP/Hcoq1/ltP.
  by apply/ltP/Hcoq2/ltP.
Qed.

Lemma ltn_pow2_log2 a b : 0 < a -> (a < 2 ^ b) -> (log2 a < b).
Proof.
  move=> H.
  by rewrite log2_lt_pow2.
Qed.

Lemma ltn_pow2_log2' a b : 0 < b -> (a < 2 ^ b) -> (log2 a < b).
Proof.
  case: a => [|a Hb]; first by [].
  by rewrite log2_lt_pow2.
Qed.

Lemma ltn_log2_pow2 a b : (log2 a < b) -> (a < 2 ^ b).
Proof.
  case: a => [_|a Hb]; first by apply expn_gt0.
  by rewrite log2_lt_pow2.
Qed.

Lemma log2_lt_lin a : 0 < a -> log2 a < a.
Proof.
  move=> H.
  rewrite -log2_trunc_log.
  by apply/ltP/NPeano.Nat.log2_lt_lin/ltP.
Qed.

Lemma log2_le_lin a : 0 <= a -> log2 a <= a.
Proof.
  move=> H.
  rewrite -log2_trunc_log.
  by apply/leP/NPeano.Nat.log2_le_lin/leP.
Qed.

Lemma log2_mul_below a b : 0 < a -> 0 < b -> log2 a + log2 b <= log2 (a * b).
Proof.
  move=> Ha Hb.
  rewrite -3!log2_trunc_log addnE mulnE.
  by apply/leP/NPeano.Nat.log2_mul_below; apply /ltP.
Qed.

Lemma log2_mul_above a b : 0 <= a -> 0 <= b -> log2 (a * b) <= (log2 a + log2 b).+1.
Proof.
  move=> Ha Hb.
  rewrite -3!log2_trunc_log -addn1 addnE mulnE.
  by apply/leP/NPeano.Nat.log2_mul_above; apply/leP.
Qed.

Lemma log2_mul_pow2 a b : 0 < a -> 0 <= b -> log2 (a * 2 ^ b) = b + log2 a.
Proof.
  move=> Ha Hb.
  rewrite -2!log2_trunc_log -pow_expn addnE mulnE.
  by apply NPeano.Nat.log2_mul_pow2; [apply/ltP|apply/leP].
Qed.

Lemma log2_double a : 0 < a -> log2 (a.*2) = (log2 a).+1.
Proof.
  move=> Ha.
  rewrite -2!log2_trunc_log -mul2n.
  by apply/NPeano.Nat.log2_double/ltP.
Qed.

Lemma log2_same a b : 0 < a -> 0 < b -> log2 a = log2 b -> a < b.*2.
Proof.
  move=> Ha Hb.
  rewrite -2!log2_trunc_log -mul2n => H.
  by apply/ltP/NPeano.Nat.log2_same => //; apply/ltP.
Qed.

Lemma log2_succ_le a : log2 a.+1 <= (log2 a).+1.
Proof.
  rewrite -2!log2_trunc_log.
  by apply/leP/NPeano.Nat.log2_succ_le.
Qed.

Lemma log2_succ_or a : (log2 a.+1 == (log2 a).+1) || (log2 a.+1 == log2 a).
Proof.
  rewrite -2!log2_trunc_log.
  apply/orP.
  by case (NPeano.Nat.log2_succ_or a) => ->; [left|right].
Qed.

Lemma log2_eq_succ_is_pow2 a : log2 a.+1 = (log2 a).+1 -> exists b, S a = 2 ^ b.
Proof.
  rewrite -2!log2_trunc_log => H.
  case (NPeano.Nat.log2_eq_succ_is_pow2 a H) => b' H'.
  exists b'.
  by rewrite H' pow_expn.
Qed.

Lemma log2_eq_succ_iff_pow2 a : 0 < a ->
  (log2 a.+1 = (log2 a).+1 <-> exists b, S a = 2 ^ b).
Proof.
  move/ltP => Ha.
  rewrite -2!log2_trunc_log.
  case (NPeano.Nat.log2_eq_succ_iff_pow2 a Ha) => H1 H2.
  split => [H|[b' H]].
    case (H1 H) => b' H'.
    exists b'.
    by rewrite H' pow_expn.
  apply H2.
  exists b'.
  by rewrite pow_expn.
Qed.

Lemma log2_succ_double a : 0 < a -> log2 (a.*2.+1) = (log2 a).+1.
Proof.
  move=> Ha.
  rewrite -2!log2_trunc_log -mul2n -addn1.
  by apply/NPeano.Nat.log2_succ_double/ltP.
Qed.

Lemma log2_add_le a b : a != 1 -> b != 1 -> log2 (a+b) <= log2 a + log2 b.
Proof.
  move=> Ha Hb.
  rewrite -3!log2_trunc_log.
  by apply/leP/NPeano.Nat.log2_add_le; apply/eqP.
Qed.

Lemma add_log2_lt a b : 0 < a -> 0 < b -> log2 a + log2 b < 2 * log2 (a+b).
Proof.
  move=> Ha Hb.
  rewrite -3!log2_trunc_log.
  by apply/ltP/NPeano.Nat.add_log2_lt; apply/ltP.
Qed.

(* bitlen *)

Definition bitlen n := if n is 0 then 0 else (log2 n).+1.

Lemma bitlen_bound n : n < 2 ^ (bitlen n).
Proof. by case: n => [|n]; last rewrite /bitlen trunc_log_ltn. Qed.

Lemma bitlen_small n : bitlen n <= n.
Proof.
  case: n => [|n]; first by [].
  rewrite /bitlen -(@leq_exp2l 2); last by [].
  rewrite 2!expnS leq_pmul2l; last by [].
  apply (@leq_trans n.+1).
    by apply trunc_logP.
  by apply ltn_expl.
Qed.

Lemma bitlen_eq0 n : (bitlen n == 0) = (n == 0).
Proof. by case: n. Qed.

Lemma leq_bitlen_l n j : (bitlen n <= j) = (n < 2 ^ j).
Proof.
  case: n j => [|n] j /=; first by rewrite leq0n expn_gt0.
  set k := log2 n.+1.
  have Hlo : 2 ^ k <= n.+1. by apply trunc_logP.
  have Hhi : n.+1 < 2 ^ k.+1. by apply trunc_log_ltn.
  case: (ltnP n.+1 (2 ^ j)) => [Hlt|Hle].
    change (k < j).
    by rewrite -(@ltn_exp2l 2); first apply (leq_ltn_trans Hlo).
  apply negbTE.
  by rewrite -leqNgt -ltnS -(@ltn_exp2l 2); first apply (leq_ltn_trans Hle).
Qed.

Lemma ltn_bitlen_r j n : (j < bitlen n) = (2 ^ j <= n).
Proof.
  case: n => [|n] /=.
    rewrite ltn0.
    apply/eqP.
    by rewrite eq_sym eqbF_neg -ltnNge expn_gt0.
  set k := log2 n.+1.
  have Hlo : 2 ^ k <= n.+1. by apply trunc_logP.
  have Hhi : n.+1 < 2 ^ k.+1. by apply trunc_log_ltn.
  case: (leqP (2 ^ j) n.+1) => [Hlt|Hle].
    change (j < k.+1).
    by rewrite -(@ltn_exp2l 2); first apply (leq_ltn_trans Hlt).
  apply negbTE.
  by rewrite -leqNgt -(@ltn_exp2l 2); first apply (leq_ltn_trans Hlo).
Qed.

End NatUtils.
