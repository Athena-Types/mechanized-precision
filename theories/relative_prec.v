From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import mathcomp_extra exp reals signed.
From mathcomp Require Import boolp Rstruct.

From mathcomp.algebra_tactics Require Import ring lra.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Require Import ErrorMetrics.lemmas.
Require Import ErrorMetrics.absolute_prec.

Local Open Scope ring_scope.

(** * Section 3.1. Relative precision. *)
Section RelPrec.

  Context {R : realType}.

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
             assert (@e R == 0 = true) by lra.
             assert (@e R == 0 = false).
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

  (** **** Equation 3.3
      In Olver (1978), equation 3.3 is ill-defined for negative a. Accordingly,
      we adjust the property statement to take absolute values first. Also, note
      that the original paper claims that Equation 3.2 (a ~ a' ; rp(α)) is
      equivalent to Equation 3.3 ((ln `|a|) ~ (ln `|a'|) ; ap(α)). This is not
      quite correct as Equation 3.2 has the additional assumption that a and a'
      are non-zero and have the same sign, whereas Equation 3.1 is unrestricted.
      Therefore, we only state and prove the forwards direction of the
      biconditional below.
   *)

  Theorem RelAbsConvert : a ~ a' ; rp(α) -> ((ln `|a|) ~ (ln `|a'|) ; ap(α)).
  Proof. rewrite /RelPrec /AbsPrec.
         move=> [H1 [H2 H3]].
         split; try split; auto.
         case: H2 => NSSS; move: NSSS => [NSSS1 NSSS2].
         {
           rewrite (@gtr0_norm R a) => //.
           rewrite (@gtr0_norm R a') => //.
           rewrite ln_div in H3 => //.
         }
         {
           rewrite (@ltr0_norm R a') => //.
           rewrite (@ltr0_norm R a) => //.
           rewrite -ln_div.
           rewrite divrNN.
           auto.
           assert (0 < -a) by lra. auto.
           assert (0 < -a') by lra. auto.
         }
  Qed.

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

  Theorem RPProp2 : forall (δ : R), (a ~ a' ; rp(α)) -> α <= δ -> (a ~ a' ; rp(δ)).
  Proof. rewrite /RelPrec.
         move=> del [H2 [H3 H4]] H6. repeat split; auto.
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

  (** *** Theorem 3.1 (core helper theorem) *)
  Theorem RPAddCore (a a' b b' : R) : a ~ a' ; rp(α) -> b ~ b' ; rp(β) ->
                                          0 < a -> 0 < b ->
                  a + b ~ a' + b'; rp(ln((a' * (e `^ α) +  b' * (e `^ β)) / (a' + b') )).
  Proof. move=> A1 A2 a_gt0 b_gt0.
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
           rewrite -(@ler_pMl R ((a' * e `^ α + b' * e `^ β) / (a' + b')) (a' + b') a'_b'_ge0). (* multiply both sides of the <= ineq *)
           rewrite -div1r.
           rewrite mulrA.
           rewrite div_mul_id.
           rewrite mulr1.
           apply lerD; destroy.
           destroy.
         }
         {
           exists (ln (R := R) ((a + b) / (a' + b'))).
           split.
           unfold powR.
           rewrite ln_e. rewrite mulr1.
           destroy.
           rewrite invr_gt0.
           lra.

           case: (@real_leP _ (a' + b') (a + b) _ _) => //= ab_leP.
           {
             rewrite ger0_norm.
             rewrite !ln_div.
             apply lerB.
             rewrite ler_ln.
             apply lerD.
             all: try destroy.

             rewrite a_eq. rewrite mulrC.
             rewrite -subr_ge0.
             rewrite -GRing.mulrBr.
             rewrite mulr_ge0; try lra.
             rewrite subr_ge0.
             rewrite e_exp_ge => //.
             apply ler_normlW => //.

             rewrite b_eq. rewrite mulrC.
             rewrite -subr_ge0.
             rewrite -GRing.mulrBr.
             rewrite mulr_ge0; try lra.
             rewrite subr_ge0.
             rewrite e_exp_ge => //.
             apply ler_normlW => //.

             rewrite ln_div.
             rewrite subr_ge0.
             rewrite ler_ln.
             all: destroy.
          }
          {
             rewrite ler_norml in P4'.
             rewrite ler_norml in P2'.

             rewrite ln_norm_sym.
             rewrite ger0_norm.
             rewrite a_eq b_eq.
             rewrite ler_ln.
             rewrite lter_pdivlMr.
             rewrite mulrC.
             rewrite mulrA.
             rewrite lter_pdivrMr.
             rewrite !mulrDr !mulrDl.
             rewrite !mulrA !addrA.

             assert (a' * e `^ α * e `^ u1 * a' + b' * e `^ β * e `^ u1 * a' + a' * e `^ α * e `^ u2 * b' + b' * e `^ β * e `^ u2 * b'
                     =
                     a' * e `^ α * e `^ u1 * a' + a' * b' * (e `^ α * e `^ u2 + e `^ β * e `^ u1) + b' * e `^ β * e `^ u2 * b')
               by lra.
             rewrite H. clear H.

             assert (a' * a' + b' * a' + a' * b' + b' * b' = a' * a' + a' * b' * 2 + b' * b') by lra.
             rewrite H. clear H.

             repeat apply lerD.
             apply ler_pM => //; try lra.
             rewrite -mulrA.
             apply ler_peMr => //; try lra.
             rewrite -powRD.
             apply e_exp_ge1.
             lra.
             destroy.

             apply ler_pM => //; try lra.
             apply mulr_ge0; try lra.
             remember (β - α) as del.
             assert (β = α + del) by lra.
             rewrite H. clear H.
             assert ((e `^ (-del)) + (e `^ (del)) <= e `^ (α + u2) + e `^ (α + del + u1)).
             apply lerD; apply e_exp_ge; lra.
             have tmp: (2 <= (e `^ (-del)) + (e `^ (del))).
             rewrite addrC. apply e_del_ge2.
             rewrite -!powRD.
             all: try destroy.

             repeat apply lerD.
             apply ler_pM => //; try lra.
             rewrite -mulrA.
             apply ler_peMr => //; try lra.
             rewrite -powRD.
             apply e_exp_ge1.
             lra.
             destroy.

             rewrite invr_gt0.
             lra.
             apply addr_gt0;
             rewrite pmulr_rgt0;
             try apply powR_gt0;
             try apply e_gt0; try lra.

             rewrite invr_gt0.
             lra.

             apply ln_ge0.
             rewrite ler_pdivlMr.
             rewrite mul1r.
             lra.
             lra.
             unfold NonZeroSameSign.
             lra.
          }
         }
         apply e_exp_bigger; lra.
         rewrite -P4 div_mul_id; lra.
         rewrite -P2 div_mul_id; lra.
    Qed.

  (** *** Theorem 3.1 *)
  Theorem RPAdd (a a' b b' : R) :
    NonZeroSameSign a b -> a ~ a' ; rp(α) -> b ~ b' ; rp(β) ->
                  a + b ~ a' + b'; rp(ln((a' * (e `^ α) +  b' * (e `^ β)) / (a' + b') )).
  Proof. move=> NSSS A1 A2.
         case: NSSS => H1; destruct H1.
         {
           apply RPAddCore => //.
         }
         {
           apply (RPProp3 _ _ _ (-1)) in A2; try lra.
           apply (RPProp3 _ _ _ (-1)) in A1; try lra.
           have inverted_thm: (-1 * a + -1 * b ~ -1 * a' + -1 * b'; rp( ln (R:=R) ((-1 * a' * e `^ α + -1 * b' * e `^ β) / (-1 * a' + -1 * b')))).
           apply RPAddCore => //; try lra.
           rewrite -!mulrDr in inverted_thm.
           apply (RPProp3 _ _ _ (-1)) in inverted_thm; try lra.
           rewrite !mulrA in inverted_thm.
           assert (-1 * -1 * (a + b) = a + b) by lra.
           assert (-1 * -1 * (a' + b') = a' + b') by lra.
           assert ((-1 * a' * e `^ α + -1 * b' * e `^ β) / (-1 * (a' + b')) = (a' * e `^ α + b' * e `^ β) / ((a' + b'))) by lra.
           rewrite H1 H2 H3 in inverted_thm.
           apply inverted_thm.
         }
         Qed.

  (** **** Corollary 1 for Theorem 3.1. *)
  Corollary RPAdd1 (a a' b b' : R) :
    NonZeroSameSign a b -> a ~ a' ; rp(α) -> b ~ b' ; rp(β) ->
                  a + b ~ a' + b'; rp(Num.max α β).
  Proof. move=> NSSS A1 A2.
         have rp_thm: a + b ~ a' + b'; rp(ln((a' * (e `^ α) +  b' * (e `^ β)) / (a' + b') )).
         apply (RPAdd a a' b b' NSSS A1 A2).
         unfold RelPrec in *.
         move: rp_thm => [ltP [NSSSp ubP]].
         move: A1 => [lt_alpha [NSSS1 H1]]; move: A2 => [lt_beta [NSSS2 H2]].
         unfold NonZeroSameSign in *.
         split; try split.
         {
           unfold maxr.
           destruct (α < β ); auto.
         }
         {
           auto.
         }
         {
           suff ub: ln (R:=R) ((a' * e `^ α + b' * e `^ β) / (a' + b')) <= maxr α β.
           apply (le_trans ubP ub).
           unfold maxr.
           case: (@real_ltP _ α β  _ _) => //= alpha_ltP.
           {
             suff ub_beta: ln (R:=R) ((a' * e `^ α + b' * e `^ β) / (a' + b')) <= ln (R:=R) ((a' * e `^ β  + b' * e `^ β) / (a' + b')).
             suff ub_beta': ln (R:=R) ((a' * e `^ β  + b' * e `^ β) / (a' + b')) <= β.
             apply (le_trans ub_beta ub_beta').
             rewrite -mulrDl.
             rewrite mulrC mulrA.
             rewrite mulVf.
             rewrite mul1r.
             rewrite ln_pow_id.
             auto.
             lra.

             case: NSSSp => NSSSp'.
             {
              rewrite ler_ln => //.
              rewrite ler_pM => //.
              apply addr_ge0; apply mulr_ge0; try lra; try apply powR_ge0.
              rewrite invr_ge0; lra.

              apply lerD; apply ler_pM; try lra; try apply powR_ge0.
              apply e_exp_ge; lra.

              destroy.
              apply addr_gt0; apply mulr_gt0; try lra; try apply powR_gt0; try apply e_gt0.
              rewrite invr_gt0; lra.

              destroy.
              apply addr_gt0; apply mulr_gt0; try lra; try apply powR_gt0; try apply e_gt0.
              rewrite invr_gt0; lra.
             }
             {
               remember (-1 * a') as n'.
               remember (-1 * b') as m'.
               assert (a' = -1 * n') by lra.
               assert (b' = -1 * m') by lra.
               assert (0 < n' + m') by lra.
               rewrite !H !H0.
               rewrite -!mulrA.
               rewrite -!mulrDr.
               rewrite !mulN1r.
               rewrite !divrNN.

               rewrite ler_ln => //.
               rewrite ler_pM => //.
               apply addr_ge0; apply mulr_ge0; try lra; try apply powR_ge0.
               rewrite invr_ge0; lra.

               apply lerD; apply ler_pM; try lra; try apply powR_ge0.
               apply e_exp_ge; lra.

               destroy.
               apply addr_gt0; apply mulr_gt0; try lra; try apply powR_gt0; try apply e_gt0.
               rewrite invr_gt0; lra.

               destroy.
               apply addr_gt0; apply mulr_gt0; try lra; try apply powR_gt0; try apply e_gt0.
               rewrite invr_gt0; lra.
             }
           }
           {
             suff ub_alpha: ln (R:=R) ((a' * e `^ α + b' * e `^ β) / (a' + b')) <= ln (R:=R) ((a' * e `^ α + b' * e `^ α) / (a' + b')).
             suff ub_alpha': ln (R:=R) ((a' * e `^ α + b' * e `^ α) / (a' + b')) <= α.

             apply (le_trans ub_alpha ub_alpha').
             rewrite -mulrDl.
             rewrite mulrC mulrA.
             rewrite mulVf.
             rewrite mul1r.
             rewrite ln_pow_id.
             auto.
             lra.

             case: NSSSp => NSSSp'.
             {
              rewrite ler_ln => //.
              rewrite ler_pM => //.
              apply addr_ge0; apply mulr_ge0; try lra; try apply powR_ge0.
              rewrite invr_ge0; lra.

              apply lerD; apply ler_pM; try lra; try apply powR_ge0.
              apply e_exp_ge; lra.

              destroy.
              apply addr_gt0; apply mulr_gt0; try lra; try apply powR_gt0; try apply e_gt0.
              rewrite invr_gt0; lra.

              destroy.
              apply addr_gt0; apply mulr_gt0; try lra; try apply powR_gt0; try apply e_gt0.
              rewrite invr_gt0; lra.
             }
             {
               remember (-1 * a') as n'.
               remember (-1 * b') as m'.
               assert (a' = -1 * n') by lra.
               assert (b' = -1 * m') by lra.
               assert (0 < n' + m') by lra.
               rewrite !H !H0.
               rewrite -!mulrA.
               rewrite -!mulrDr.
               rewrite !mulN1r.
               rewrite !divrNN.

               rewrite ler_ln => //.
               rewrite ler_pM => //.
               apply addr_ge0; apply mulr_ge0; try lra; try apply powR_ge0.
               rewrite invr_ge0; lra.

               apply lerD; apply ler_pM; try lra; try apply powR_ge0.
               apply e_exp_ge; lra.

               destroy.
               apply addr_gt0; apply mulr_gt0; try lra; try apply powR_gt0; try apply e_gt0.
               rewrite invr_gt0; lra.

               destroy.
               apply addr_gt0; apply mulr_gt0; try lra; try apply powR_gt0; try apply e_gt0.
               rewrite invr_gt0; lra.
             }
           }
         }
    Qed.

  (** *** Theorem 3.2 *)
  Theorem RPSub (a a' b b' : R) : a ~ a' ; rp(α) -> b ~ b' ; rp(β) -> `|a'| * (e `^ -α) > `|b'| * (e `^ β) ->
                  a + b ~ a' + b'; rp(ln(a' * (e `^ α) -  b' * (e `^ -β) / (a' - b') )).
    Admitted.
End RPAddSub.
