Require Import Relation_Definitions Morphisms.
From mathcomp Require Export all_ssreflect ssralg ssrnum.
From mathcomp Require Export mathcomp_extra exp reals signed.
From mathcomp Require Export boolp Rstruct.

From mathcomp.algebra_tactics Require Export ring lra.

Export Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

Section HelperLemmas.
  Context {R : realType}.

  Fact abs_eq : forall (a b : R), a = b -> `|a| = `|b|.
  Proof. move => a b H1; by rewrite H1. Qed.

  Definition NonZeroSameSign (a b : R) : Prop :=
    (a > 0 /\ b > 0) \/ (a < 0 /\ b < 0).

  Instance trans_NonZeroSameSign : Transitive NonZeroSameSign.
  Proof.
    rewrite /NonZeroSameSign /Transitive => x y z H1 H2.
    case: H1 H2 => H3 H4; destruct H3; destruct H4; lra. Qed.

  Instance sym_NonZeroSameSign : Symmetric NonZeroSameSign.
  Proof.
    rewrite /NonZeroSameSign /Symmetric => x y H1.
    case: H1 => H2. lra. lra. Qed.

  (* NB: x is not reflexive (needs to be non-zero). *)
  Lemma nonzero_refl_NonZeroSameSign : forall x, x != 0 -> NonZeroSameSign x x.
  Proof.
    move=> x H1. rewrite /NonZeroSameSign.
    case: (@real_ltP _ x 0 _ _) => //= x_ltP.
    auto. lra. Qed.

  Lemma lt0_NonZeroSameSign : forall x y, x < 0 -> NonZeroSameSign x y -> y < 0.
  Proof. rewrite /NonZeroSameSign. move=> x y H1 H2.
         case: H2 => H3; lra. Qed.

  Lemma gt0_NonZeroSameSign : forall x y, 0 < x -> NonZeroSameSign x y -> 0 < y.
  Proof. rewrite /NonZeroSameSign. move=> x y H1 H2.
         case: H2 => H3; lra. Qed.

  Lemma NonZeroSameSignMulGen : forall (a a' b b' : R),
    (NonZeroSameSign a a') -> (NonZeroSameSign b b') ->(NonZeroSameSign (a * b) (a' * b')).
  Proof. rewrite /NonZeroSameSign. move=> a a' b b' H1 H2.
         case: H1 => H3; case: H2 => H4.
         left.
         split; destruct H3; destruct H4; apply mulr_gt0 => //.
         right.
         split; destruct H3; destruct H4.
         replace (a * b) with (b * a) by lra.

         remember (- b) as n.
         replace b with (- n) by lra.
         assert (0 < n) by lra.
         suff opp: 0 < (n * a) by lra.
         apply mulr_gt0 => //.

         remember (- b') as n.
         replace b' with (- n) by lra.
         assert (0 < n) by lra.
         suff opp: (0 < n * a') by lra.
         apply mulr_gt0 => //.

         destruct H3. destruct H4.
         right.
         remember (- a) as n. remember (- a') as n'.
         replace a with (- n) by lra. replace a' with (- n') by lra.
         assert (0 < n) by lra. assert (0 < n') by lra.
         split.
         suff opp: (0 < n * b) by lra. apply mulr_gt0 => //.
         suff opp: (0 < n' * b') by lra. apply mulr_gt0 => //.

         destruct H3. destruct H4.
         left. split.
         suff opp: (0 < (- a) * (- b)) by lra.
         apply mulr_gt0 => //; lra.
         suff opp: (0 < (- a') * (- b')) by lra.
         apply mulr_gt0 => //; lra. Qed.

  Lemma NonZeroSameSignMul : forall (a b : R),
    forall k, k != 0 ->
              (NonZeroSameSign a b) -> (NonZeroSameSign (k * a) (k * b)).
  Proof. move=> a b k H1 H2.
         apply NonZeroSameSignMulGen.
         apply nonzero_refl_NonZeroSameSign => //.
         apply H2. Qed.

  Lemma real_eqP : forall (r : R), r != 0 \/ r = 0.
  Proof. move=> r. case: (@real_ltP _ r 0 _ _) => //= a_ltP; lra.
          Qed.

  Lemma NonZeroSameSignMulInv : forall (a b : R),
    forall k, k != 0 ->
              NonZeroSameSign (k * a) (k * b) -> NonZeroSameSign a b.
  Proof. move=> a b k H1 H2.
         have simp_more: (1 / k * k = 1 * (k / k)) by lra.
         replace a with (1 / k * (k * a)).
         replace b with (1 / k * (k * b)).
         apply (@NonZeroSameSignMul (k * a) (k * b) (1 / k)) => //.
         case: (@real_ltP _ k 0 _ _) => //= a_ltP.
         {
          suff lt_0: 1 / k < 0 by lra.
          suff gt_0: 1 / - k > 0 by lra.
          apply divr_gt0; lra.
         }
         {
           have kgt_0: 0 < k by lra.
           suff gt_0: 1 / k > 0 by lra.
           apply divr_gt0; lra.
         }
         have b_rewrite: (1 / k * (k * b) = (1 / k * k) * b) by lra.
         rewrite b_rewrite. rewrite simp_more. rewrite mulfV.
         rewrite !mul1r. auto. auto.
         have a_rewrite: (1 / k * (k * a) = (1 / k * k) * a) by lra.
         rewrite a_rewrite. rewrite simp_more. rewrite mulfV.
         rewrite !mul1r. auto. auto. Qed.

  Lemma NonZeroSameSignExp : forall (a b : R),
    forall k, (NonZeroSameSign a b) -> (NonZeroSameSign (a `^ k) (b `^ k)).
  Proof. Admitted.

  Lemma NonZeroSameSignExpInv : forall (a b : R),
    forall k, (NonZeroSameSign (a `^ k) (b `^ k) -> NonZeroSameSign a b).
  Proof. Admitted.

  Lemma NonZeroSameSignDivPos : forall (a a' : R),
    NonZeroSameSign (a) (a') -> 0 < a / a'.
  Proof. Admitted.

  Lemma le_mul_pos : forall (k a b : R), a <= b -> (`|k| * a <= `|k| * b). Admitted.
  Lemma norm_mul_split : forall (a b : R), `| a * b | = `| a | * `| b |. Admitted.
  Lemma factor_exp : forall (a a' k : R), (a `^ k / a' `^ k = (a / a') `^ k). Admitted.
End HelperLemmas.
