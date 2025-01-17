From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import mathcomp_extra exp reals signed.
From mathcomp Require Import boolp Rstruct.

From mathcomp.algebra_tactics Require Import ring lra. 

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

Section AbsPrec.

  Context {R : realType}.

  Definition AbsPrec (a a' α : R) : Prop := α >= 0 -> `| (a - a') | <= α.    

End AbsPrec.

Notation "a ~ a' ; ap( α )" := (AbsPrec a a' α) (at level 99).

Fact abs_eq : forall {R : realType} (a b : R), a = b -> `|a| = `|b|. 
Proof. move => HR a b H1; by rewrite H1. Qed.

(* Properties from Olver Section 2.2 *)
Section APElementaryProperties.

  Context {R : realType}.
  Variables (a a' α : R). 
  Hypothesis Halpha : 0 <= α.  
  
  Theorem Prop1 : (a ~ a' ; ap(α)) -> (a' ~ a ; ap(α)).
  Proof. rewrite /AbsPrec. move => H1 H2. 
         rewrite Num.Theory.distrC H1 => //=. Qed.

  Theorem Prop2 : forall (δ : R), (a ~ a' ; ap(α)) -> 0 <= α -> α <= δ -> (a ~ a' ; ap(δ)).
  Proof. rewrite /AbsPrec; move => δ H1 H2 H3 H4.
         rewrite (@le_trans _ _ α) => //. rewrite H1 => //=. Qed.

  Theorem Prop3 : forall (k : R), (a ~ a'; ap(α)) -> (a+k ~ a'+k ; ap(α)).
  Proof. rewrite /AbsPrec; move => k H1 H2. rewrite (abs_eq _ (a-a')) => //;
         [rewrite H1 => //| ring]. Qed.

  Fact abs_mul_eq : forall (k : R), `|k * a| = `|k| * `|a|. 
  Proof. move => k; by rewrite normrM. Qed.

  Theorem Prop4 : forall (k : R), (a ~ a' ; ap(α)) -> 0 <= α -> a*k ~ a'*k ; ap(`|k|*α).
  Proof. rewrite /AbsPrec; move => k H1 H2 H3. rewrite (abs_eq _ (k * (a-a'))) => //;
         [rewrite normrM ler_pM => //=; rewrite H1 => //= | ring]. Qed.

  Lemma Prop4_1 :  a ~ a' ; ap(α) -> -a ~ -a' ; ap(α).
  Proof. rewrite /AbsPrec; move => H1 H2. rewrite -(abs_eq (a' - a)) => //;
         [rewrite Prop1 => //| ring]. Qed.
                                                              
  Theorem Prop5 : forall (b b' β : R), 
      a ~ a' ; ap(α) ->  b ~ b' ; ap(β) -> 0 <= β -> a + b ~ a' + b' ; ap(α + β).
  Proof. rewrite /AbsPrec; move => b b' β H1 H2 H3 H4.
         rewrite (@le_trans _ _ (normr (a-a') + normr (b -b'))) => //.
         rewrite -(abs_eq ((a-a')+(b-b'))) => //; 
          [rewrite ler_normD => // | ring ]. rewrite lerD => //; 
          [rewrite H1 => //| rewrite H2 => //]. Qed.

  Theorem Prop6 : forall (a'' δ : R ), 
      a ~ a' ; ap(α) -> a' ~ a'' ; ap(δ) -> 0 <= δ -> a ~ a'' ; ap(α + δ).
  Proof. rewrite /AbsPrec. move => a'' δ H1 H2 H3 H4.
         rewrite -(abs_eq ((a-a') + (a' -a''))) => //; [|ring].
         rewrite (@le_trans _ _ (normr (a-a') + normr (a'-a''))) => //. 
         rewrite ler_normD => //. rewrite lerD => //; [rewrite H1|rewrite H2] => //=. Qed.

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
    Proof. rewrite /AbsPrec. move => H1 H2 H3. 
           set (u := a - a'); set (v := b - b').
           rewrite -(abs_eq (a'*v + (b'*u + u * v))) => //.
           rewrite (@le_trans _ _ (`|a' * v| + `|b' * u + u * v|)) => //.
           rewrite ler_normD => //. rewrite -addrA lerD => //. 
           rewrite normrM /v ler_pM => //. rewrite H2 => //. 
           rewrite (@le_trans _ _ (`|b' * u| + `|u * v|)) => //.
           rewrite ler_normD => //. rewrite lerD => //. rewrite normrM /u ler_pM => //.
           rewrite H1 => //. rewrite normrM /u /v ler_pM => //; 
           [rewrite H1 => // | rewrite H2 => //]. rewrite /u /v; ring. Qed.


   (* Theorem 2.2 *)
   (* Can we prove this without |b| > β? The hypothesis isn't used in the paper. *)
   Theorem APDiv : 
     a ~ a' ; ap(α) -> b ~ b' ; ap(β) -> `|b'| > β -> `|b| > β ->
     a/b ~ a'/b' ;  ap((`|a'|*β + `|b'|*α)/(`|b'|*(`|b'| - β))).
     Proof. rewrite /AbsPrec. move => H1 H2 H3 H4 H5.
            set (u := a - a'); set (v:= b - b').
            rewrite -(abs_eq ((b'*u - a'*v) *  (1/ (b' * (b' + v))))) => //; 
                                            [ |rewrite /u /v; field]. 
            rewrite normrM. rewrite ler_pM => //. rewrite distrC. 
            rewrite (@le_trans _ _ (`|a'*v | + `|b'*u|)) => //; 
                                            [rewrite ler_normB => //|].
            repeat rewrite normrM; rewrite lerD => //; rewrite ler_pM => //;
            rewrite /u /v; try rewrite H1 => //; try rewrite H2 => //.
            rewrite normr_inv normrM -(div1r (normr b' * _)) divr_le => //.
            rewrite mulr_gt0 => //; try nra. rewrite (@le_lt_trans _ _ β) => //.
            rewrite ler_pM => //; try nra. rewrite /v lerBlDl. 
            rewrite (abs_eq (b' + _) b) => //; [|ring]. rewrite -lerBlDr. 
            rewrite (@le_trans _ _ `|b' - b|) => //. rewrite lerB_dist => //. 
            rewrite Prop1 => //. apply /andP; split; rewrite -normr_gt0 (@le_lt_trans _ _ β) => //. Qed.

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


Section RelPrec.

  Context {R : realType}.

  Definition RelPrec (a a' α : R) : Prop :=
    α >= 0 ->
    (a > 0 /\ a' > 0) \/ (a < 0 /\ a' < 0) ->
    `|ln(a / a')| <= α.

End RelPrec.

Notation "a ~ a' ; rp( α )" := (RelPrec a a' α) (at level 99).

Section RPElementaryProperties.

  Context {R : realType}.
  Variables (a a' α : R).
  Hypothesis Halpha : 0 <= α.

  Theorem RPProp1 : (a ~ a' ; rp(α)) -> (a' ~ a ; rp(α)).
  Proof. rewrite /RelPrec.
         move => H1 H2 H3.
         apply H1 in H2.
         suff sym : ((`|ln (R:=R) (a' / a)|) = `|ln (R:=R) (a / a')|).
         rewrite sym.
         apply: H2.
         suff inv_neg : (ln (R:=R) (a' / a) =  - 1 * ln (R:=R) (a / a')).
         rewrite inv_neg.
         suff neg_1_swap : ( - 1 * ln (R:=R) (a / a') = - ln (R:=R) (a / a')).
         rewrite neg_1_swap.
         apply normrN.
         apply mulN1r.
         rewrite - (GRing.invf_div a a').
         rewrite - ln_powR.
         rewrite powRN.
         rewrite powRr1.
         reflexivity.
         destruct H3.
         + destruct H.
           apply divr_ge0; lra.
         + destruct H.
           suff temp: 0 <= (- a) / (- a') by lra.
           suff neg_a: 0 <= - a'.
           suff neg_a': 0 <= - a.
           apply divr_ge0; lra.
           lra.
           lra.
         + destruct H3; auto; destruct H; try split; auto.
         Qed.

  Theorem RPProp2 : forall (δ : R), (a ~ a' ; rp(α)) -> 0 <= α -> α <= δ -> (a ~ a' ; rp(δ)).
  Proof. Admitted.

  Theorem RPProp3 : forall (k : R), (a ~ a'; rp(α)) -> (a+k ~ a'+k ; rp(α)).
  Proof. Admitted.

  Fact RPabs_mul_eq : forall (k : R), `|k * a| = `|k| * `|a|.
  Proof. Admitted.

  Theorem RPProp4 : forall (k : R), (a ~ a' ; rp(α)) -> 0 <= α -> a*k ~ a'*k ; rp(`|k|*α).
  Proof. Admitted.

  Lemma RPProp4_1 :  a ~ a' ; rp(α) -> -a ~ -a' ; rp(α).
  Proof. Admitted.

  Theorem RPProp5 : forall (b b' β : R),
      a ~ a' ; rp(α) ->  b ~ b' ; rp(β) -> 0 <= β -> a + b ~ a' + b' ; rp(α + β).
  Proof. Admitted.

  Theorem RPProp6 : forall (a'' δ : R ),
      a ~ a' ; rp(α) -> a' ~ a'' ; rp(δ) -> 0 <= δ -> a ~ a'' ; rp(α + δ).
  Proof. Admitted.

End RPElementaryProperties.
