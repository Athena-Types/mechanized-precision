From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import mathcomp_extra exp reals signed.
From mathcomp Require Import boolp Rstruct.

From mathcomp.algebra_tactics Require Import ring lra.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Require Import ErrorMetrics.lemmas.

Local Open Scope ring_scope.

Section AbsPrec.

  Context {R : realType}.

  Definition AbsPrec (a a' α : R) : Prop := α >= 0 /\ `| (a - a') | <= α.

End AbsPrec.

Notation "a ~ a' ; ap( α )" := (AbsPrec a a' α) (at level 99).

(* Properties from Olver Section 2.2 *)
Section APElementaryProperties.
  Context {R : realType}.

  Variables (a a' α : R). 
  Hypothesis Halpha : 0 <= α.  
  
  Theorem Prop1 : (a ~ a' ; ap(α)) -> (a' ~ a ; ap(α)).
  Proof. rewrite /AbsPrec. move => [H1 H2].
         rewrite Num.Theory.distrC H1 => //=. Qed.

  Theorem Prop2 : forall (δ : R), (a ~ a' ; ap(α)) -> 0 <= α -> α <= δ -> (a ~ a' ; ap(δ)).
  Proof. rewrite /AbsPrec; move => δ [H1 H2] H3 H4.
         split; rewrite (@le_trans _ _ α) => //. Qed.

  Theorem Prop3 : forall (k : R), (a ~ a'; ap(α)) -> (a+k ~ a'+k ; ap(α)).
  Proof. rewrite /AbsPrec; move => k [H1 H2]. split. auto.
         rewrite (abs_eq _ (a-a')) => //. ring. Qed.

  Fact abs_mul_eq : forall (k : R), `|k * a| = `|k| * `|a|. 
  Proof. move => k; by rewrite normrM. Qed.

  Theorem Prop4 : forall (k : R), (a ~ a' ; ap(α)) -> 0 <= α -> a*k ~ a'*k ; ap(`|k|*α).
  Proof. rewrite /AbsPrec; move => k [H1 H2] H3. split.
         rewrite mulr_ge0 => //=.
         rewrite (abs_eq _ (k * (a-a'))) => //.
         rewrite normrM ler_pM => //=. ring.
         Qed.

  Lemma Prop4_1 :  a ~ a' ; ap(α) -> -a ~ -a' ; ap(α).
  Proof. rewrite /AbsPrec; move => [H1 H2]. split. auto. rewrite -(abs_eq (a' - a)) => //.
         rewrite distrC => //.
         ring. Qed.

  Theorem Prop5 : forall (b b' β : R), 
      a ~ a' ; ap(α) ->  b ~ b' ; ap(β) -> 0 <= β -> a + b ~ a' + b' ; ap(α + β).
  Proof. rewrite /AbsPrec; move => b b' β [H1 H2] [H3 H4] H5.
         split. lra.
         rewrite (@le_trans _ _ (normr (a-a') + normr (b -b'))) => //.
         rewrite -(abs_eq ((a-a')+(b-b'))) => //; 
          [rewrite ler_normD => // | ring ]. rewrite lerD => //. Qed.

  Theorem Prop6 : forall (a'' δ : R ), 
      a ~ a' ; ap(α) -> a' ~ a'' ; ap(δ) -> 0 <= δ -> a ~ a'' ; ap(α + δ).
  Proof. rewrite /AbsPrec. move => a'' δ [H1 H2] [H3 H4] H5.
         split. lra.
         rewrite -(abs_eq ((a-a') + (a' -a''))) => //; [|ring].
         rewrite (@le_trans _ _ (normr (a-a') + normr (a'-a''))) => //. 
         rewrite ler_normD => //. rewrite lerD => //. Qed.

End APElementaryProperties.

Fact normr_inv : forall {R : realType} (x : R), `|1/x| = 1/`|x|.
Proof. move => H x; have Hx : (0 <= x) \/ (x < 0) by nra. destruct Hx;
         [rewrite !ger0_norm => //|]. rewrite divr_ge0 => //.
       rewrite !ltr0_norm => //; [nra|]. rewrite ltr_ndivrMr; nra. Qed.

Fact divr_le : forall {R : realType} (x y : R), 0< y -> y <= x  -> 1/x <= 1/y.
Proof. move => H x y H1 H2. rewrite ler_pdivrMr => //; [|nra].
rewrite div1r ler_pdivlMl => //; nra. Qed.

(* Theorems from Section 2.3 *)
Section APMultDiv.

  Context {R : realType}.
  Variables (a a' b b' α β : R). 

  Hypothesis Halpha : 0 <= α.
  Hypothesis Hbeta  : 0 <= β. 

  (* Theorem 2.1 *)
  Theorem APMul : 
    a ~ a' ; ap(α) -> b ~ b' ; ap(β) -> a * b ~ a' * b' ; ap(`|a'| * β + `|b'| * α + α * β).
    Proof. rewrite /AbsPrec. move => [H1 H2] [H3 H4].
           split. rewrite addr_ge0 => //. rewrite addr_ge0 => //.
           apply mulr_ge0; try apply normr_ge0; try lra.
           apply mulr_ge0; try apply normr_ge0; try lra.
           apply mulr_ge0; try apply normr_ge0; try lra.
           set (u := a - a'); set (v := b - b').
           rewrite -(abs_eq (a'*v + (b'*u + u * v))) => //.
           rewrite (@le_trans _ _ (`|a' * v| + `|b' * u + u * v|)) => //.
           rewrite ler_normD => //. rewrite -addrA lerD => //. 
           rewrite normrM /v ler_pM => //.
           rewrite (@le_trans _ _ (`|b' * u| + `|u * v|)) => //.
           rewrite ler_normD => //. rewrite lerD => //. rewrite normrM /u ler_pM => //.
           rewrite normrM /u /v ler_pM => //; rewrite H1 => //.
           rewrite /u /v. ring. Qed.


   (* Theorem 2.2 *)
   Theorem APDiv :
     a ~ a' ; ap(α) -> b ~ b' ; ap(β) -> `|b'| > β ->
     a/b ~ a'/b' ;  ap((`|a'|*β + `|b'|*α)/(`|b'|*(`|b'| - β))).
     Proof. rewrite /AbsPrec. move => [H1 H2] [H3 H4] H5.
            set (u := a - a'); set (v:= b - b').
            split. apply divr_ge0. Search (0 <= _ + _).
            apply addr_ge0; apply mulr_ge0 => //.
            apply mulr_ge0 => //. lra.
            rewrite -(abs_eq ((b'*u - a'*v) *  (1/ (b' * (b' + v))))) => //;
                                            [ |rewrite /u /v; field]. 
            rewrite normrM. rewrite ler_pM => //. rewrite distrC. 
            rewrite (@le_trans _ _ (`|a'*v | + `|b'*u|)) => //; 
                                            [rewrite ler_normB => //|].
            repeat rewrite normrM; rewrite lerD => //; rewrite ler_pM => //;
            rewrite /u /v; try rewrite H1 => //; try rewrite H2 => //.
            rewrite normr_inv normrM -(div1r (normr b' * _)) divr_le => //.
            rewrite mulr_gt0 => //; try nra.
            rewrite ler_pM => //; try nra. rewrite /v lerBlDl.
            rewrite (abs_eq (b' + _) b) => //; [|ring]. rewrite -lerBlDr.
            rewrite (@le_trans _ _ `|b' - b|) => //. rewrite lerB_dist => //.
            rewrite distrC => //.
            apply /andP. split. rewrite -normr_gt0 (@le_lt_trans _ _ β) => //.

            case: (real_eqP b) => //= b_eq0.
            {
              subst.
              rewrite sub0r in H4.
              rewrite normrN in H4.
              move: (lt_le_asym β `|b'|) => H.

              assert (β  < `|b'| <= β ).
              apply /andP.
              split; auto.
              rewrite H0 in H.
              inversion H.
            }
     Qed.

End APMultDiv.

Section MultDiv2.

Context {R: realType}.
Variable (a a' α b b' β : R).
Hypothesis Halpha : 0 <= α.
Hypothesis Hbeta  : 0 <= β.

     Corollary APMul2 :
       a ~ a'; ap(α) -> b ~ b' ; ap(β) -> a * b ~ a' * b' ; ap(`|a| * β + `|b| * α + α * β).
       Proof. move => H1 H2. apply: Prop1; apply: APMul => //; apply Prop1 => //. Qed.

     Corollary APDiv2 : 
     a ~ a' ; ap(α) -> b ~ b' ; ap(β) -> `|b'| > β -> `|b| > β ->
     a/b ~ a'/b' ;  ap((`|a|*β + `|b|*α)/(`|b|*(`|b| - β))).
       Proof. move => H1 H2 H3 H4. apply: Prop1; apply APDiv => //; apply Prop1 => //. Qed.

End MultDiv2.


