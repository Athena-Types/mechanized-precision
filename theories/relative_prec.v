Require Import ErrorMetrics.lemmas.

Local Open Scope ring_scope.

(** * Section 3.1. Relative precision. *)
Section RelPrec.

  Context {R : realType}.

  Definition e := @sequences.expR R 1.

  Lemma ln_e : ln e = 1.
  Proof.
    unfold e.
    rewrite expRK => //.
  Qed.

  Definition RelPrec (a a' α : R) : Prop :=
    α >= 0 /\ NonZeroSameSign a a' /\
    `|ln(a / a')| <= α.

  Definition RelPrecAlt (a a' α : R) : Prop :=
    α >= 0 /\ exists u, a/a' = e `^ u /\ `|u| <= α.

  Theorem RelPrecAltEquiv (a a' α : R) : RelPrec a a' α <-> RelPrecAlt a a' α.
  Proof. rewrite /RelPrec /RelPrecAlt. split. move=> [H1 [H2 H3]].
         split; try split; auto.
         {
           exists (ln (R:=R) (a / a')).
           split; auto.
           unfold powR.
           rewrite expR_eq0.
           rewrite ln_e.
           rewrite mulr1.
           rewrite lnK => //.
           apply NonZeroSameSignDivPos => //.
         }
         {
           move=> [H1 [u [H2 H3]]].
           split; try split; auto.
           assert (0 < e `^ u).
           case: (real_eqP (e `^ u)) => //= exp_eq0.
           {
             have pow_ge0: 0 <= e `^ u.
             apply powR_ge0.
             lra.
           }
           {
             apply powR_eq0_eq0 in exp_eq0.
             assert (e == 0 = true) by lra.
             assert (e == 0 = false).
             apply expR_eq0.
             rewrite H in H0.
             discriminate.
           }
           rewrite -H2 in H.
           apply DivPosNonZeroSameSign => //.
           assert (ln (R:=R) (a / a') = ln (R:=R) (e `^ u)). congruence.
           assert (ln (R:=R) (e `^ u) = u).
           rewrite ln_powR. rewrite ln_e. lra.
           congruence.
         }
         Qed.
End RelPrec.

Notation "a ~ a' ; rp( α )" := (RelPrec a a' α) (at level 99).

(** ** Section 3.2. Elemetary properties. *)
Section RPElementaryProperties.

  Context {R : realType}.
  Variables (a a' α : R).
  Hypothesis Halpha : 0 <= α.

  (** *** Property 1. *)

  Theorem RPProp1 : (a ~ a' ; rp(α)) -> (a' ~ a ; rp(α)).
  Proof. rewrite /RelPrec /NonZeroSameSign.
         move=> [H1 [H2 H3]].
         repeat split; auto.
         destruct H2. left. destruct H; split; auto.
         destruct H. right. destruct H3; split; auto.
         suff sym : ((`|ln (R:=R) (a' / a)|) = `|ln (R:=R) (a / a')|).
         rewrite sym => //.
         suff inv_neg : (ln (R:=R) (a' / a) =  - 1 * ln (R:=R) (a / a')).
         rewrite inv_neg.
         suff neg_1_swap : ( - 1 * ln (R:=R) (a / a') = - ln (R:=R) (a / a')).
         rewrite neg_1_swap.
         apply: normrN.
         apply: mulN1r.
         rewrite - (GRing.invf_div a a').
         rewrite - ln_powR.
         rewrite powRN.
         rewrite powRr1.
         reflexivity.
         case: H2.
         move=> Ha.
         apply: divr_ge0.
         by [lra].
         by [lra].
         move=> [Ha' Ha].
         suff temp: 0 <= (- a) / (- a') by lra.
         suff neg_a: 0 <= - a'.
         suff neg_a': 0 <= - a.
         apply: divr_ge0; lra.
         by [lra].
         by [lra].
         Qed.

  (** *** Property 2. *)

  Theorem RPProp2 : forall (δ : R), (a ~ a' ; rp(α)) -> 0 <= α -> α <= δ -> (a ~ a' ; rp(δ)).
  Proof. rewrite /RelPrec.
         move=> del [H2 [H3 H4]] H5 H6. repeat split; auto.
         rewrite (@le_trans _ _ α) => //.
         rewrite (@le_trans _ _ α) => //.
         Qed.

  (** *** Property 3. *)

  Theorem RPProp3 : forall (k : R), (a ~ a'; rp(α)) -> k != 0 -> (k * a ~ k * a' ; rp(α)).
  Proof. rewrite /RelPrec; move => k [H1 [H2 H3]] H4. repeat split; auto.
         apply (NonZeroSameSignMul _ _ k) => //.
         rewrite -mulf_div. rewrite divff => //. rewrite mul1r => //. Qed.

  (** *** Property 4.
      In Olver (1978), property 4 is stated as follows. If [k] is any real
      number, then [a ^ k ≃ a'^k ; rp (|k|α)]. However, this does not make
      sense for negative [a] and [a']. Accordingly, we adjust the property
      statement to take absolute values first: [|a| ^ k ≃ |a'|^k ; rp (|k|α)].
      The adjusted property is stated and proved below.
   *)

  Theorem RPProp4 : forall (k : R),
      (a ~ a' ; rp(α)) -> 0 <= α -> `|a| `^ k ~ `|a'| `^ k ; rp(`|k|*α).
  Proof. rewrite /RelPrec. move => k [H1 [H2 H3]] H4. repeat split; auto.
         rewrite mulr_ge0 => //.
         apply (NonZeroSameSignExp a a' k) => //.
         rewrite (factor_exp `|a| `|a'| k). rewrite ln_powR.
         rewrite norm_mul_split.
         suff key_rel : `|ln (R:=R) (a / a')| <= α.
         apply ler_pM => //.
         rewrite NonZeroSameSignDivAbs => //.
         apply H3 => //.
         unfold NonZeroSameSign in H2.
         rewrite normr_gt0 => //. lra.
         unfold NonZeroSameSign in H2.
         rewrite normr_gt0 => //. lra.
  Qed.

  (** *** Property 5. *)

  Theorem RPProp5 : forall (b b' β : R),
      a ~ a' ; rp(α) ->  b ~ b' ; rp(β) -> 0 <= β -> a * b ~ a' * b' ; rp(α + β).
  Proof. rewrite /RelPrec. move=> b b' β [H1 [H2 H3]] [H4 [H5 H6]] H7. repeat split; auto.
         rewrite addr_ge0 => //.
         apply NonZeroSameSignMulGen => //.
         suff sep_frac : (a * b / (a' * b') = (a / a') * (b / b')).
         rewrite sep_frac lnM.
         rewrite (@le_trans _ _ _ _ _ (ler_normD _ _)) => //.
         suff add_le : forall (a b c d : R), a <= b -> c <= d -> a + c <= b + d.
         rewrite add_le => //.
         move=> w x y z P1 P2. lra.
         apply NonZeroSameSignDivPos => //. apply NonZeroSameSignDivPos => //. lra. Qed.

  Lemma ln_dist_triangle :
    forall (x y z c d : R),
      0 < x -> 0 < y -> 0 < z -> 0 <= c -> 0 <= d ->
      `|ln (R:=R) (x / y)| <= c -> `|ln (R:=R) (y / z)| <= d ->
      `|ln (R:=R) (x / z)| <= c + d.
  Proof. move=> x y z c d xgt0 ygt0 zgt0 cge0 dge0 H1 H2.
         rewrite ln_div; auto. rewrite ln_div in H1; auto. rewrite ln_div in H2; auto.
         have Hceq: `|c| = c. apply ger0_norm => //. rewrite -Hceq. rewrite -Hceq in H1.
         have Hdeq: `|d| = d. apply ger0_norm => //. rewrite -Hdeq. rewrite -Hdeq in H2.
         have Hnormleq: `|(ln (R:=R) x - ln (R:=R) y) + (ln (R:=R) y - ln (R:=R) z)| <= `|ln (R:=R) x - ln (R:=R) y| + `|ln (R:=R) y - ln (R:=R) z|.
         apply ler_normD => //.
         have Haddleq: `|ln (R:=R) x - ln (R:=R) y| + `|ln (R:=R) y - ln (R:=R) z| <= `|c| + `|d|.
         apply lerD => //.
         have norm_simpl: `|ln (R:=R) x - ln (R:=R) z| =  `|(ln (R:=R) x - ln (R:=R) y) + (ln (R:=R) y - ln (R:=R) z)|.
         rewrite subrKA => //.
         rewrite -norm_simpl in Hnormleq.
         apply (@le_trans _ _ _ _ _ Hnormleq Haddleq). Qed.

  (** *** Property 6. *)

  Theorem RPProp6 : forall (a'' δ : R ),
      a ~ a' ; rp(α) -> a' ~ a'' ; rp(δ) -> 0 <= δ -> a ~ a'' ; rp(α + δ).
  Proof. rewrite /RelPrec. move=> a'' δ [H1 [H2 H3]] [H4 [H5 H6]] H7. repeat split; auto.
         rewrite addr_ge0 => //.
         apply (@trans_NonZeroSameSign _ _ _ _ H2 H5).
         case: (@real_ltP _ a 0 _ _) => //= a_ltP.
         {
           have a'lt0: (a' < 0) by apply (lt0_NonZeroSameSign a).
           have a''lt0: (a'' < 0) by apply (lt0_NonZeroSameSign a').
           remember (- a) as b.
           remember (- a') as b'.
           remember (- a'') as b''.
           move: H3 H6.
           replace a with (- b) by lra.
           replace a' with (- b') by lra.
           replace a'' with (- b'') by lra.
           have blt0: (0 < b) by lra.
           have b'lt0: (0 < b') by lra.
           have b''lt0: (0 < b'') by lra.
           rewrite !divrNN.
           move=> H3 H6.
           apply (ln_dist_triangle b b' b'') => //.
         }
         rewrite /NonZeroSameSign in H2.
         have a_gt0: 0 < a by lra.
         have a'gt0: (0 < a') by apply (gt0_NonZeroSameSign a).
         have a''gt0: (0 < a'') by apply (gt0_NonZeroSameSign a').
         apply (ln_dist_triangle a a' a'') => //.
  Qed.

End RPElementaryProperties.

(** ** Section 3.3. Addition and subtraction. *)
Section RPAddSub.
  Context {R : realType}.
  Variables (α β : R).

  Hypothesis Halpha : 0 <= α.
  Hypothesis Hbeta : 0 <= β.

  (* helper lemmas *)
  Lemma e_exp_ge: forall (a b : R), a <= b  -> (e `^ a) <= (e `^ b).
  Proof.
  move => a b H1.
  rewrite -ler_ln; [rewrite !ln_powR ln_e; nra | | ].
  all : rewrite posrE; apply powR_gt0, expR_gt0.
  Qed.

  Lemma e_exp_ge1 : forall (p : R), 0 <= p -> 1 <= e `^ p.

  Proof. move=> p H1. Admitted.

  Lemma e_exp_bigger: forall (x y: R), 0 <= x -> 0 <= y -> x <= x * e `^ y.
  Proof. move=> x y H1 H2.
         apply ler_peMr => //.
         apply e_exp_ge1 => //.
  Qed.


  Lemma div_mul_id: (forall (x y : R), x != 0 -> ( y / x ) * x = y).
  Proof. move=>x y H1. rewrite -mulrA. field. auto. Qed.
  Lemma div_mul: (forall (x : R), x != 0 -> ( 1 / x ) * x = x / x).
  Proof. move=> x H1. rewrite div_mul_id => //. rewrite mulfV => //. Qed.

  (** *** Theorem 3.1 (helper theorem; no reasoning by symmetry applied yet) *)
  Theorem RPAddCore (a a' b b' : R) : a ~ a' ; rp(α) -> b ~ b' ; rp(β) ->
                                          0 < a -> 0 < b -> (a' + b' <= a + b) ->
                  a + b ~ a' + b'; rp(ln((a' * (e `^ α) +  b * (e `^ β)) / (a' + b') )).
  Proof. move=> A1 A2 a_gt0 b_gt0 a_b_gt_a'_b'.
         have B1: (RelPrecAlt a a' α). apply RelPrecAltEquiv => //.
         have B2: (RelPrecAlt b b' β). apply RelPrecAltEquiv => //.
         rewrite RelPrecAltEquiv. unfold RelPrecAlt in *. unfold RelPrec in *. unfold NonZeroSameSign in *.
         case B1 => P1 [u1 [P2 P2']]. case B2 => P3 [u2 [P4 P4']].

         suff a_eq: a = e `^ u1 * a'.
         suff b_eq: b = e `^ u2 * b'.
         have a_b_ge0: 0 < a + b. lra.
         have a'_b'_ge0: 0 < a' + b'. lra.
         have a_p_b_ne0: a + b != 0. lra.
         have a'_p_b'_ne0: a' + b' != 0. lra.
         suff b_exp_ge_b: b <= b * e `^ β.
         split.
         {
           apply ln_ge0.
           rewrite -(@ler_pMl R ((a' * e `^ α + b * e `^ β) / (a' + b')) (a' + b') a'_b'_ge0). (* multiply both sides of the <= ineq *)
           rewrite -div1r.
           assert ((a' * e `^ α + b * e `^ β) * (1 / (a' + b')) * (a' + b') = (a' * e `^ α + b * e `^ β) * ((1 / (a' + b')) * (a' + b'))) by lra.
           rewrite H. clear H.
           rewrite div_mul_id; try lra. rewrite mulr1.
           apply lerD.
           apply e_exp_bigger => //. lra.
           rewrite b_eq.
           rewrite mulrC. rewrite mulrA.
           rewrite -powRD.
           rewrite mulrC.

           apply e_exp_bigger => //. lra.
           suff u2_lhs: -u2 <= β.

           lra.
           assert (- u2 <= `|u2|).
           rewrite -normrN.
           rewrite ler_norm => //.
           lra.
           assert (@e R != 0 = true).
           assert (0 <@e R). apply expR_gt0.
           lra.
           rewrite H.
           apply implybT.
         }
         {
           exists (ln (R := R) ((a + b) / (a' + b'))).

           split.
           unfold powR.
           rewrite ln_e.
           assert ((@e R == 0) = false). apply expR_eq0. rewrite H.
           rewrite mulr1.
           rewrite lnK => //.
           apply divr_gt0 => //.

           rewrite ger0_norm.
           rewrite !ln_div.
           rewrite a_eq.
           rewrite b_eq.
           apply lerB.

           suff lhs0_rewrite: (0 <= ln (R:=R) (a' * e `^ α + e `^ u2 * b' * e `^ β) - ln (R:=R) (e `^ u1 * a' + e `^ u2 * b')).
           have lhs1_rewrite: (0 + ln (R:=R) (e `^ u1 * a' + e `^ u2 * b') = ln (R:=R) (e `^ u1 * a' + e `^ u2 * b')) by lra.
           rewrite -lhs1_rewrite.

           rewrite (lerBrDr 0 (ln (R:=R) (a' * e `^ α + e `^ u2 * b' * e `^ β)) (ln (R:=R) (e `^ u1 * a' + e `^ u2 * b'))) in lhs0_rewrite.
           apply lhs0_rewrite.
           rewrite -ln_div.
           rewrite -a_eq -b_eq.

           apply ln_ge0.
           (* suff bounds_good: a + b <= (a' * e `^ α + b * e `^ β). *)
           rewrite -(@ler_pMl R ((a' * e `^ α + b * e `^ β) / (a + b)) (a + b) a_b_ge0). (* multiply both sides of the <= ineq *)
           rewrite -div1r.
           assert ((1 / (a + b)) * (a + b) = ((a + b) / (a + b))) by lra.
           rewrite -mulrA.
           rewrite div_mul_id.
           rewrite mulr1.
           rewrite a_eq b_eq.
           apply lerD.
           {
             rewrite -P2.
             rewrite -div1r. rewrite -mulrA.
             assert (( 1 / a' ) * a' = a' / a') by lra.
             rewrite H0.
             rewrite mulfV => //; try lra. rewrite mulr1.
             rewrite -(@ler_pdivrMl _  a' (e `^ α) a); try lra.
             have a_inv: (a'^-1 * a = a / a') by lra.
             rewrite a_inv P2.
             apply e_exp_ge.
             apply ler_normlW => //.  auto.
           }
           {
             rewrite -P4.
             rewrite -div1r. rewrite -mulrA.
             rewrite div_mul_id; try rewrite mulr1; try lra.
           }
           lra.
           {
            suff gt0: (0 < a' * e `^ α + e `^ u2 * b' * e `^ β).
            apply gt0.
            rewrite -(addr0 0).
            apply ltrD; rewrite pmulr_lgt0 => //; try apply powR_gt0; try apply expR_gt0; try lra.
           }
           {
            suff gt0: (0 < e `^ u1 * a' + e `^ u2 * b').
            apply gt0.
            rewrite -(addr0 0).
            apply ltrD; rewrite pmulr_lgt0 => //; try apply powR_gt0; try apply expR_gt0; try lra.
           }
           lra.
           {
            suff gt0: (0 < a' * e `^ α + b * e `^ β).
            apply gt0.
            rewrite -(addr0 0).
            apply ltrD; rewrite pmulr_lgt0 => //; try apply powR_gt0; try apply expR_gt0; try lra.
           }
           auto.
           auto.
           auto.
           apply ln_ge0.
           rewrite -(@ler_pMl R ((a + b) / (a' + b')) (a' + b')). (* multiply both sides of the <= ineq *)
           rewrite div_mul_id.
           lra.
           lra.
           lra.
         }
         apply e_exp_bigger => //.
         lra.
         rewrite -P4.
         rewrite div_mul_id => //.
         lra.
         rewrite -P2.
         rewrite div_mul_id => //.
         lra.
    Qed.

  (** *** Theorem 3.1 (full theorem with reasoning by symmetry) *)
  Theorem RPAdd (a a' b b' : R) : a ~ a' ; rp(α) -> b ~ b' ; rp(β) ->
                  a + b ~ a' + b'; rp(ln((a' * (e `^ α) +  b * (e `^ β)) / (a' + b') )).
  Proof. move=> A1 B1.
         case: (@real_ltP _ 0 a _ _) => //= a_ltP.
         {
          case: (@real_ltP _ 0 b _ _) => //= b_ltP.
          {
            case: (@real_leP _ (a' + b') (a + b)) => //= ab_ltP.
            {
              apply RPAddCore => //.
            }
            {
              apply RPProp1.
              apply RPProp1 in A1. apply RPProp1 in B1.
              Check RPAddCore.
              have ab_leP: (a + b <= a' + b') by lra.
              unfold RelPrec in A1.
              unfold RelPrec in B1.
              unfold NonZeroSameSign in *.
              have a'_lt0: (0 < a') by lra.
              have b'_lt0: (0 < b') by lra.
              pose proof (@RPAddCore a' a b' b A1 B1 a'_lt0 b'_lt0 ab_leP) as rp_sym.
              give_up.
            }
          }
          {
            give_up.
          }
         }
         {
           give_up.
         }
  Admitted.

  (** *** Theorem 3.2 *)
  Theorem RPSub : a ~ a' ; rp(α) -> b ~ b' ; rp(β) -> `|a'| * (e `^ -α) > `|b'| * (e `^ β) ->
                  a + b ~ a' + b'; rp(ln(a' * (e `^ α) -  b * (e `^ -β) / (a' - b') )).
    Admitted.

End RPAddSub.
