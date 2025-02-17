Require Import Relation_Definitions Morphisms.
From mathcomp Require Export all_ssreflect ssralg ssrnum.
From mathcomp Require Export mathcomp_extra exp reals signed.
From mathcomp Require Export boolp Rstruct.

From mathcomp.algebra_tactics Require Export ring lra.

Export Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

Section HelperLemmas.
  Context {R : realType}.

  Definition e := @sequences.expR R 1.

  Lemma ln_e : ln e = 1.
  Proof.
    unfold e.
    rewrite expRK => //.
  Qed.

  Lemma e_gt0: 0 < e.
  Proof.
    unfold e.
    rewrite expR_gt0 => //.
  Qed.

  Lemma ln_pow_id : forall u, ln (R:=R) (e `^ u) = u.
  Proof. move=> u. unfold powR.
         rewrite expR_eq0. rewrite (@expRK R) ln_e mulr1 => //.
  Qed.

  Lemma pow_ln_id : forall u, 0 < u -> (e `^ (ln u)) = u.
  Proof. move=> u H1.
         unfold powR.
         rewrite expR_eq0.
         rewrite expRM (@lnK R). rewrite ln_e. rewrite powRr1 => //.
         lra.
         have gt0: (0 < u) by lra.
         apply gt0.
         Qed.


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

  Lemma NonZeroSameSignDivPos: forall (a b : R),
      NonZeroSameSign a b -> 0 < a / b.
  Proof. rewrite /NonZeroSameSign. move=> a b H1.
         case H1 => H2; destruct H2.
         apply divr_gt0 => //.
         remember (- a) as n. have a_rewrite: (a = - n) by lra. rewrite a_rewrite.
         remember (- b) as m. have b_rewrite: (b = - m) by lra. rewrite b_rewrite.
         assert (0 < n) by lra. assert (0 < m) by lra.
         suff: (0 < n / m) by lra.
         apply divr_gt0 => //. Qed.

  Lemma DivPosNonZeroSameSign: forall (a b : R),
      0 < a / b -> NonZeroSameSign a b.
  Proof. Admitted.

  Lemma NonZeroSameSignDivAbs: forall (a b : R),
      NonZeroSameSign a b -> `|a| / `|b| = a / b.
  Proof. rewrite /NonZeroSameSign. move=> a b H1.
         case: (@real_ltP _ a 0 _ _) => //= a_ltP.
         {
           have b_lt_0: b < 0 by lra.
           rewrite !ltr0_norm.
           rewrite divrNN => //.
           auto. auto.
         }
         have a_gt_0: 0 < a by lra.
         have b_gt_0: 0 < b by lra.
         rewrite !ger0_norm => //.
         lra. Qed.

  Lemma NonZeroSameSignAbs : forall (a b : R), a != 0 -> b != 0 -> NonZeroSameSign `|a| `|b|.
  Proof. rewrite /NonZeroSameSign. move=> a b H1 H2.
         left. split; rewrite normr_gt0 => //. Qed.

  Lemma NonZeroSameSignExp : forall (a b : R),
    forall k, (NonZeroSameSign a b) -> (NonZeroSameSign (`|a| `^ k) (`|b| `^ k)).
  Proof. rewrite /NonZeroSameSign. move=> a b k H1.
         (* Setup some basic facts to share *)
         have a_nonzero: a != 0 by lra.
         have b_nonzero: b != 0 by lra.
         have a_abs_nonzer0: `|a| != 0. rewrite normr_eq0 => //.
         have b_abs_nonzer0: `|b| != 0. rewrite normr_eq0 => //.
         have a_abs_gt0: 0 < `|a|. rewrite normr_gt0 => //.
         have b_abs_gt0: 0 < `|b|. rewrite normr_gt0 => //.

         (* step 1: |b| = |a| * (|b| / |a|); rewrite. *)
         have b_rewrite1: `|b| = 1 * `|b| by lra.
         have b_rewrite2: 1 = `|a| / `|a|. rewrite divff => //.
         rewrite b_rewrite2 in b_rewrite1.
         have b_rewrite: `|b| = `|a| * (`|b| / `|a|) by lra.
         clear b_rewrite1 b_rewrite2.
         pose proof H1 as H2.
         rewrite b_rewrite.

         (* step 2: 0 < (|b| / |a|). *)
         assert (0 < `|b| / `|a|).
         apply divr_gt0 => //.

         (* step 3: 0 < (b / a) so 0 < (b / a) ^ k *)
         assert (0 < (`|b| / `|a|) `^ k).
         apply powR_gt0 => //.

         (* step 4: b ^ k = a ^ k * (b / a) ^ k, so b ^ k must have the same sign as a ^k. *)
         have split_exp: ((`|a| * (`|b| / `|a|)) `^ k = `|a| `^ k * (`|b| / `|a|) `^ k).
         apply powRM; lra.

         (* step 5: use NonZeroSameSignMulGen with previous facts. *)
         rewrite split_exp.
         fold (NonZeroSameSign (`|a| `^ k) (`|a| `^ k * (`|b| / `|a|) `^ k)).
         replace (`|a| `^ k) with (`|a| `^ k * 1) by lra.
         apply NonZeroSameSignMulGen.
         have a_k_ne0: (`|a| `^ k != 0).
         rewrite lt0r_neq0 => //.
         apply powR_gt0 => //.
         have a_id: (`|a| `^ k * 1 = `|a| `^ k) by lra.
         rewrite a_id.
         apply nonzero_refl_NonZeroSameSign => //.
         left. lra.
  Qed.

  Lemma norm_mul_split : forall (a b : R), `| a * b | = `| a | * `| b |.
  Proof. move=> a b.
         case: (@real_ltP _ a 0 _ _) => //= a_ltP.
         {
          case: (@real_ltP _ b 0 _ _) => //= b_ltP.
          {
            have a_b_gt0: (0 < a * b).
            rewrite nmulr_rgt0 => //.
            rewrite gtr0_norm => //.
            rewrite !ltr0_norm => //.
            lra.
          }
          {
            case: (real_eqP b) => //= b_eq0.
            {
              have a_b_le0: (a * b <= 0).
              rewrite mulr_le0_ge0 => //. lra.
              rewrite ltr0_norm => //.
              rewrite ltr0_norm => //.
              rewrite gtr0_norm => //.
              lra.
              lra.
              assert (a != 0) by lra.
              assert (a * b != 0).
              apply mulf_neq0 => //.
              lra.
            }
            {
              rewrite !b_eq0.
              assert (a * 0 = 0) by lra.
              rewrite H.
              rewrite !normr0.
              lra.
            }
          }
         }
         {
          case: (real_eqP a) => //= a_eq0.
          {
            case: (@real_ltP _ b 0 _ _) => //= b_ltP.
            {
              assert (0 < a) by lra.
              assert (a * b < 0).
              rewrite nmulr_llt0 => //.
              rewrite ltr0_norm => //.
              rewrite gtr0_norm => //.
              rewrite ltr0_norm => //.
              lra.
            }
            {
              rewrite !ger0_norm => //.
              rewrite mulr_ge0 => //.
            }
          }
          {
            rewrite !a_eq0.
            assert (0 * b = 0) by lra.
            rewrite H.
            rewrite !normr0.
            lra.
          }
         }
  Qed.

  Lemma factor_exp : forall (a a' k : R), 0 < a -> 0 < a' -> (a `^ k / a' `^ k = (a / a') `^ k).
    move=> a a' k a_gt0 a'_gt0.
    have a_ne0: (a == 0 = false). lra.
    have a'_ne0: (a' == 0 = false). lra.
    have aa'_ge0: (0 < a / a'). apply divr_gt0 => //.
    have aa'_ne0: (a / a' == 0 = false). lra.
    unfold powR.
    rewrite a_ne0 a'_ne0 aa'_ne0.
    rewrite -expRN.
    rewrite -exp.expRD.
    rewrite -GRing.mulrBr.
    rewrite ln_div => //.
  Qed.

  Lemma e_exp_ge: forall (a b : R), a <= b  -> (e `^ a) <= (e `^ b).
  Proof.
  move => a b H1.
  rewrite -ler_ln; [rewrite !ln_powR ln_e; nra | | ].
  all : rewrite posrE; apply powR_gt0, expR_gt0.
  Qed.

  Lemma e_exp_ge1 : forall (p : R), 0 <= p -> 1 <= e `^ p.

  Proof. move=> p H1. rewrite -ler_ln;[rewrite ln1 ln_powR ln_e; nra | |].
  all: rewrite posrE; try nra; apply powR_gt0, expR_gt0. Qed.

  Lemma e_exp_bigger: forall (x y: R), 0 <= x -> 0 <= y -> x <= x * e `^ y.
  Proof. move=> x y H1 H2.
         apply ler_peMr => //.
         apply e_exp_ge1 => //.
  Qed.

  Lemma div_mul_id: (forall (x y : R), x != 0 -> ( y / x ) * x = y).
  Proof. move=>x y H1. rewrite -mulrA. field. auto. Qed.
  Lemma div_mul: (forall (x : R), x != 0 -> ( 1 / x ) * x = x / x).
  Proof. move=> x H1. rewrite div_mul_id => //. rewrite mulfV => //. Qed.
  Lemma div_mul_y: (forall (x y : R), x != 0 -> ( x * (y / x) ) = y).
  Proof. move=> x y H1. rewrite mulrC. rewrite div_mul_id => //.
         Qed.

  Lemma e_ne0: (e == 0) = false.
  Proof. rewrite expR_eq0. reflexivity. Qed.

  Lemma ln_norm_sym : (forall (a b : R), NonZeroSameSign a b -> (`|ln (R:=R) (a / b)| = `|ln (R:=R) (b / a)|)).
  Proof. move=> a b H1.
         rewrite -invf_div.
         rewrite -(@powR_inv1 _ (b / a)).
         rewrite ln_powR.
         rewrite mulN1r.
         rewrite normrN.
         reflexivity.
         assert (0 < b / a).
         apply NonZeroSameSignDivPos.
         apply sym_NonZeroSameSign => //.
         lra.
  Qed.

  Lemma e_del_ge2: forall del, 2%R <= @GRing.add R (e `^ del) (e `^ (-del)).
  Proof.
    move=> del.
    pose proof (leif_AGM2_scaled (e `^ del) (e `^ - del)).
    destruct H.
    clear e0.
    rewrite -powRD in i.
    assert (del - del = 0) by lra.
    rewrite H in i. clear H.
    rewrite powRr0 in i.
    rewrite -ler_ln in i.

    assert (4 = @GRing.exp R 2 2) by lra.
    rewrite H in i. clear H.
    rewrite -!powR_mulrn in i.
    rewrite (ln_powR 2 2) in i.
    rewrite (ln_powR ((e `^ del + e `^ (- del))) 2) in i.

    assert (0 <= 1 / 2) as H0 by lra.
    assert (0 <= 2 * @ln R 2) as H1. apply mulr_ge0. lra. apply ln_ge0. lra.
    assert (1/2 <= 1/2) as H2 by lra.
    pose proof (@ler_pM R (1 / 2) (1 / 2) (2 * ln 2) (2 * ln (e `^ del + e `^ (- del))) H0 H1 H2 i) as main_thm.
    assert (forall (x : R), (1 / 2 * (2 * x)) = x) as H3. move=> y. lra.
    rewrite !H3 in main_thm.

    pose proof (e_exp_ge _ _ main_thm) as main_thm'.
    rewrite !pow_ln_id in main_thm'.
    apply main_thm'.
    all:
      repeat progress
      (try apply addr_gt0;
      try apply addr_ge0;
      try apply mulr_gt0;
      try apply e_ge0;
      try apply powR_gt0;
      try apply powR_ge0;
      try apply e_gt0;
      try lra).

    pose proof e_gt0.
    assert (e != 0) by lra.
    rewrite H0.
    apply implybT.
    Qed.

End HelperLemmas.

Ltac simp :=
  let H1 := fresh in
  let H2 := fresh in
  match goal with
    | [ |- context[?X \is Num.pos] ] => suff H1: (0 < X); apply H1
    | [ |- context[e `^ ?X != 0] ] => assert (0 < @e _ `^ X) as H1 by (apply powR_gt0; apply e_gt0); lra; clear H1
    | [ |- context[@e _ == 0] ] => rewrite e_ne0
    | [ |- context[sequences.expR (ln (R:=_) _ )] ] => rewrite lnK
    | [ |- context[(ln (R:=_) (sequences.expR _) )] ] => rewrite expRK
    (* | [ |- context[?X^-1] ] => rewrite -(@div1r _ X) *)
  end.

Ltac destroy' :=
  let H1 := fresh in
  let H2 := fresh in
  match goal with
    | [ |- context[0 < ?X * ?Y] ] => suff H1: (0 < X); suff H2: (0 < Y); lra
    | [ |- context[?B <= ?B * (e `^ ?Y)]] => rewrite e_exp_bigger; try lra
    (* | [ |- context[- ?X <= - ?Y]] => have H1: 0 - Y = - Y by lra; have H2: 0 - X = - X by lra; rewrite H1 H2; apply lerB; try auto *)
  end.

Ltac destroy := try repeat progress simp; try repeat destroy'; try repeat apply addr_gt0 => //; try repeat apply mulr_gt0 => //; try apply powR_gt0; try apply e_gt0; try lra.
