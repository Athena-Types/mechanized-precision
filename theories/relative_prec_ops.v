From ErrorMetrics Require Import error_model relative_prec.
From Flocq Require Import Core.
From Coq Require Import Reals Psatz List.

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import Rstruct sequences exp.

Local Open Scope R_scope.

Section Lemmas.

Lemma NZSS_mul_exp : 
forall x eps : R, x <> 0 -> lemmas.NonZeroSameSign (x * expR eps) x.
Proof.
move => x eps Hx0.
have He : 0 < expR eps.
{ apply /RltP. apply expR_gt0. } 
case: (Rdichotomy x 0) => // H0; rewrite /lemmas.NonZeroSameSign;
[right | left]; split; rewrite /ssralg.GRing.zero => //=; apply /RltP => //. 
apply Rmult_neg_pos => //. 
apply Rmult_lt_0_compat => //. 
Qed.

End Lemmas.

Section ExtendedRP.

Definition RelPrecEx (x y a : R) : Prop := 
   (x == 0) /\ (y == 0) /\ (a == 0) \/ (x ~ y ; rp(a)).

Notation "a ~ a' ; rpe( c )" := (RelPrecEx a a' c) (at level 99).

Section RPOps.

Variable beta : radix.
Variable prec : Z.
Variable rnd : R -> Z.

Hypothesis Hprec : Prec_gt_0 prec.
Hypothesis Hprec2: (1 < prec)%Z.
Hypothesis Hrnd  : Valid_rnd rnd.

Notation fexp := (FLX_exp prec).
Notation format := (generic_format beta fexp).
Notation u := (bpow beta (-prec + 1)).

Theorem relative_prec_plus:  
  forall x y : R, format x -> format y -> x + y <> 0 ->  
  ((round beta fexp rnd (x + y)) ~ (x + y); rp(u/(1-u))).
Proof.
move => x y Hx Hy H0.
destruct (exp_error_model beta _ Hprec rnd Hrnd Hprec2 (x + y)) as (eps, (H1, H2)) => //.
rewrite H2 /RelPrec; repeat split.
apply /RleP. apply Rle_trans with (Rabs eps) => //. apply Rabs_pos.
apply NZSS_mul_exp => //.
rewrite -!RmultE -!RinvE Rmult_inv_r_id_m => //.
rewrite exp.expRK => //=. apply /RleP => //.
Qed.

Definition sumF  := fun x y => round beta fexp rnd (x + y).
Definition multF := fun x y => round beta fexp rnd (x * y).

Definition dot_prod (sum mult: R -> R -> R) (x y: list R) : R:= 
  fold_right (fun x s => sum (mult (fst x) (snd x)) s) 0 (combine x y). 

Definition dot_prodF := dot_prod sumF multF.
Definition dot_prodR := dot_prod Rplus Rmult.

Lemma dotprodR_plus : 
 forall a x, 
 fold_right (fun x s => Rplus (Rmult (fst x) (snd x)) s) 0 (a :: x)
 = fst a * snd a + fold_right (fun x s => Rplus (Rmult (fst x) (snd x)) s) 0 x.
Proof. trivial. Qed.

Lemma dotprodF_plus : 
 forall a x, fold_right (fun x s => sumF (multF (fst x) (snd x)) s) 0 (a :: x) = 
 sumF (multF (fst a) (snd a)) 
   (fold_right (fun x s => sumF (multF (fst x) (snd x)) s) 0 x).
Proof. trivial. Qed.

Theorem dot_product: 
  forall x y : list R, 
    let n:= length (combine x y) in 
    (dot_prodF x y ~ dot_prodR x y ; rpe(INR n * (u/(1-u)) )).
Proof.
move => x y.
rewrite /dot_prodF /dot_prodR /dot_prod.
induction (combine x y); [left|right].
{ simpl. rewrite Rmult_0_l /RelPrecEx; repeat split; try apply /eqP; try nra.  }
rewrite dotprodR_plus dotprodF_plus. 
replace (INR (length ( _ :: _))) with (1 + INR (length l)).
rewrite Rmult_plus_distr_r Rmult_1_l.
set dpF := fold_right _.
set A := sumF (multF a.1 a.2) _.
set C := a.1 * _ + _.
set B := Rplus (multF a.1 a.2) (dpF 0 l).
pose proof (RPProp6 A B (u / (1-u)) C (INR (length l) * (u / (1-u)))).
apply H; clear H.
rewrite /A /sumF /B.
apply relative_prec_plus. admit. admit. admit.
Admitted.

End RPOps.
