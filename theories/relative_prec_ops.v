From ErrorMetrics Require Import error_model relative_prec lemmas.
From Flocq Require Import Core.
From Coq Require Import Reals Psatz List.

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import Rstruct sequences exp.

From Coq Require Import FunctionalExtensionality.

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
  forall x y : R, x + y <> 0 ->  
  ((round beta fexp rnd (x + y)) ~ (x + y); rp(u/(1-u))).
Proof.
move => x y H0.
destruct (exp_error_model beta _ Hprec rnd Hrnd Hprec2 (x + y)) as (eps, (H1, H2)) => //.
rewrite H2 /RelPrec; repeat split.
apply /RleP. apply Rle_trans with (Rabs eps) => //. apply Rabs_pos.
apply NZSS_mul_exp => //.
rewrite -!RmultE -!RinvE Rmult_inv_r_id_m => //.
rewrite exp.expRK => //=. apply /RleP => //.
Qed.

Theorem relative_prec_mul:  
  forall x y : R, x * y <> 0 ->  
  ((round beta fexp rnd (x * y)) ~ (x * y); rp(u/(1-u))).
Proof.
move => x y H0.
destruct (exp_error_model beta _ Hprec rnd Hrnd Hprec2 (x * y)) as (eps, (H1, H2)).
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

Lemma generic_format_dpF : 
 forall x, 
   generic_format beta fexp (fold_right (fun x s => sumF (multF (fst x) (snd x)) s) 0 x).
Proof. 
move => x. induction x => //=. apply generic_format_0. 
rewrite /sumF. apply generic_format_round => //. apply FLX_exp_valid => //.
Qed.

Lemma round_round_dpF : 
 forall x, 
   round beta fexp rnd (fold_right (fun x s => sumF (multF (fst x) (snd x)) s) 0 x) = 
   fold_right (fun x s => sumF (multF (fst x) (snd x)) s) 0 x.
Proof.
move => x.
induction x => //=; [by rewrite round_0|].
rewrite /sumF. rewrite round_generic => //. apply generic_format_round => //.
apply FLX_exp_valid => //.
Qed.

Theorem sum_pos_neq_0 : 
 forall x y x0 y0,
   (forall a, In a (combine (x0 :: x)  (y0 :: y)) -> fst a * snd a > 0) -> 
   dot_prodR (x0 :: x)  (y0 :: y) > 0.
Proof.
move => x y x0 y0. rewrite /dot_prodR /dot_prod => //=.
induction (combine x y) => //= H. rewrite Rplus_0_r. 
apply (H (x0,y0)) => //=; by left.
rewrite Rplus_comm Rplus_assoc.
apply Rplus_lt_0_compat.
apply (H a) => //=. by right; left.
rewrite Rplus_comm. apply IHl.
move => a0 [Ha0| Ha0]. apply H; left => //.
apply H ; by right; right.
Qed.

Lemma sum_pos_gt_0 : 
 forall l,
   (forall a, In a l -> fst a * snd a > 0) -> 
   l <> nil -> 
   fold_right (fun x => Rplus (Rmult x.1 x.2)) 0 l > 0.
Proof.
move =>  l H1 H2=> //=.
induction l => //=.
destruct l => //=.
rewrite Rplus_0_r. 
apply (H1 a) => //=. by left.
apply Rplus_lt_0_compat.
apply (H1 a) => //=. by left.
apply IHl => //=. 
move => a0 [H0|H0]. 
apply H1 => //=. by right; left.
apply (H1 a0) => //=. by right; right.
Qed.

Lemma Fsum_pos_gt_0 : 
 forall l,
   (forall a, In a l -> fst a * snd a > 0) -> 
   l <> nil -> 
   fold_right (fun x => sumF (multF x.1 x.2)) 0 l > 0.
Proof.
move =>  l H1 H2=> //=.
induction l => //=.
destruct l => //=.
rewrite /sumF /multF Rplus_0_r.
rewrite round_generic.
apply round_preserves_sign_pos => //. 
apply (H1 a) => //=. by left.
apply generic_format_round => //.
apply FLX_exp_valid => //.
apply round_preserves_sign_pos => //. 
apply Rplus_lt_0_compat.
apply round_preserves_sign_pos => //. 
apply (H1 a) => //=. by left.
apply IHl => //=. 
move => a0 [H0|H0]. 
apply H1 => //=. by right; left.
apply (H1 a0) => //=. by right; right.
Qed.

Fact ub_ge_0 : 0 <= u / (1-u).
Proof.
apply Rdiv_pos_pos_le.
apply Rlt_0_minus. 
change 1 with (bpow beta 0); apply bpow_lt.
rewrite Z.add_comm. 
rewrite Z.add_opp_r. 
apply Z.lt_sub_0 => //.
apply Rle_ge, bpow_ge_0.
Qed.

Lemma length_cons : 
  forall A (l : list A) a, 1 + INR (length l) = INR (length(a::l)).
Proof.
move => A l a. induction l => //=; nra.
Qed.

Theorem dot_product: 
  forall x y : list R, 
    (forall xy, In xy (combine x y) -> (fst xy * snd xy) > 0) -> 
    combine x y <> nil -> 
    let n:= length (combine x y) in 
    (dot_prodF x y ~ dot_prodR x y ; rp(INR n * (u/(1-u)) )).
Proof.
move => x y H H1.
rewrite /dot_prodF /dot_prodR /dot_prod.
induction (combine x y); [ simpl => // |]. 
replace (INR (length ( _ :: _))) with (1 + INR (length l)).
set b := (_/ _). 
have: l = [::] \/ l <> [::]. 
{ destruct l. by left. right. move : H1 => //=. } 
rewrite Rmult_plus_distr_r Rmult_1_l => //=.
move => [] Hl; [rewrite Hl => //=| ].
{ rewrite /sumF /multF  !Rplus_0_r round_generic.
eapply RPProp2. apply relative_prec_mul. 
apply Rgt_not_eq. apply (H a) => //=. by left.
apply /RleP. suff : 1 * b <= 2 * b ; rewrite /b;  try nra.
apply Rmult_le_compat; try nra. apply ub_ge_0.
apply generic_format_round => //. apply FLX_exp_valid => //. }
have Ha : 0 < a.1 * a.2.
{ apply (H a) => //=. by left. }  
set dpF := fold_right _.
have HdpF : dpF 0 l > 0.
{ rewrite /dpF. apply Fsum_pos_gt_0 => //.
move => a0 Ha0. apply H => //=; by right. } 
have HRp : fold_right (fun x => [eta Rplus (x.1 * x.2)]) 0 l > 0.
{ apply sum_pos_gt_0 => //. 
move => a0 Ha0 => //. apply H=> //=; by right. } 
set A := sumF (multF a.1 a.2) _.
set C := a.1 * _ + _.
set B := Rplus (multF a.1 a.2) (dpF 0 l).
set n := INR _. 
apply (RPProp6 A B b C (n * b)).
{ apply relative_prec_plus; 
apply Rgt_not_eq; apply Rplus_pos_pos => //.
rewrite /multF.
apply round_preserves_sign_pos => //. } 
apply RPProp1; eapply RPProp2. 
apply (RPAdd b (n*b)). 
rewrite /lemmas.NonZeroSameSign; left; split; apply /RltP => //=.
rewrite /multF; apply RPProp1, relative_prec_mul, Rgt_not_eq =>//. 
apply RPProp1, IHl => //.
move => xy Hxy. apply H => //=; by right.
{ rewrite -!RmultE -!RplusE -RinvE.
apply /RleP.
have H01 : 0 < a.1 * a.2 + dpF 0 l.
{ apply Rplus_lt_0_compat => //. } 
set D1 := multF a.1 a.2 * _ + _ .
set D2 := multF a.1 a.2 + _.
have Hmult : 0 < multF a.1 a.2.
{ apply round_preserves_sign_pos => //. } 
have HD1 : 0 < D1.
{ rewrite /D1. apply Rplus_lt_0_compat => //.
apply Rmult_lt_0_compat => //.
apply /RltP. rewrite powR_gt0 => //.
apply expR_gt0.
apply Rmult_lt_0_compat => //.
apply /RltP. rewrite powR_gt0 => //.
apply expR_gt0. } 
have HD2 : 0 < D2.
{ rewrite /D2. apply Rplus_lt_0_compat => //. } 
apply Rle_trans with 
  (ln (D2 * powR e (n * b) * / D2)). 
apply ln_le_increasing; 
repeat try apply Rmult_lt_0_compat => //;
try apply Rinv_0_lt_compat => //.
apply /RltP. rewrite powR_gt0 => //.
apply expR_gt0.  
apply Rmult_le_compat; try nra.
apply Rlt_le, Rinv_0_lt_compat => //.
rewrite /D2 /D1.
rewrite Rmult_plus_distr_r.
apply Rplus_le_compat; try nra.
apply Rmult_le_compat; try nra.
apply Rlt_le; apply /RltP. rewrite powR_gt0 => //.
apply expR_gt0. 
apply /RleP. rewrite e_exp_ge => //. rewrite /n.
apply /RleP; replace b with (INR 1 * b) at 1; [|simpl; nra].
apply Rmult_le_compat; [apply pos_INR | apply ub_ge_0 | | ]; try nra.
apply le_INR; destruct l => //=; lia. 
rewrite Rmult_inv_r_id_m => //.
rewrite ln_powR ln_e -RmultE. rewrite Rmult_1_r; nra.
apply nesym, Rlt_not_eq => //. } 
apply /RleP. apply Rmult_le_pos; [| apply ub_ge_0].
apply pos_INR. apply length_cons.
Qed.

End RPOps.
