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
           Search sequences.expR.
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
             Check powR_eq0_eq0.
             apply powR_eq0_eq0 in exp_eq0.
             Search (sequences.expR).
             assert (e == 0 = true) by lra.
             assert (e == 0 = false).
             apply expR_eq0.
             rewrite H in H0.
             discriminate.
           }
           rewrite -H2 in H.
           apply DivPosNonZeroSameSign => //.
           assert (ln (R:=R) (a / a') = ln (R:=R) (e `^ u)). congruence.
           Search (ln).
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
  Variables (a a' b b' α β : R).

  Hypothesis Halpha : 0 <= α.

  (** *** Theorem 3.1 *)
  Theorem RPAdd : a ~ a' ; rp(α) -> b ~ b' ; rp(β) ->
                  a + b ~ a' + b'; rp(ln((a' * (e `^ α) +  b * (e `^ β)) / (a' + b') )).
  Proof. rewrite /RelPrec. move=> [H1 [H2 H3]] [H4 [H5 H6]].
         suff a'_le_a: a' <= a.
         suff b'_le_b: a' <= a.
         suff sym_arg: 1 <= (a + b) / (a' + b').
         suff sign_ass: 0 < a /\ 0 < b /\ 0 < a' /\ 0 < b'.
         split; try split.
         {
           give_up.
         }
         {
           rewrite /NonZeroSameSign. lra.
         }
         {
           rewrite ger0_norm => // .
           (* Search sequences.expR. *)
           (* Search (_`^_ <=  _). *)
           (* rewrite expRK. *)


           rewrite !ln_div. rewrite ln_div in H3. rewrite ln_div in H6.
           have a_ineq: a <= a' * e `^ α.
           rewrite lnM.
           Search ln.
           rewrite -ln_powR.
           apply lerB.

           lra.
           rewrite ln_ge0 => //.
         }
         give_up.

         give_up.
    rewrite RPProp3.
    Admitted.

  (** *** Theorem 3.2 *)
  Theorem RPSub : a ~ a' ; rp(α) -> b ~ b' ; rp(β) -> `|a'| * (e `^ -α) > `|b'| * (e `^ β) ->
                  a + b ~ a' + b'; rp(ln(a' * (e `^ α) -  b * (e `^ -β) / (a' - b') )).
    Admitted.

End RPAddSub.
