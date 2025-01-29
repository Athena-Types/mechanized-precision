From ErrorMetrics Require Import error_model relative_prec.
From Flocq Require Import Core.
From Coq Require Import Reals Psatz.

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
  exists eps, 
  Rabs eps <= u / (1-u) /\ ((round beta fexp rnd (x + y)) ~ (x + y); rp(eps)).
Proof.
move => x y Hx Hy H0.
destruct (exp_error_model beta _ Hprec rnd Hrnd Hprec2 (x + y)) as (eps, (H1, H2)) => //.
exists (Rabs eps); split. 
rewrite Rabs_Rabsolu => //. rewrite H2 /RelPrec; repeat split.
apply /RleP; apply Rabs_pos. apply NZSS_mul_exp => //.
rewrite -!RmultE -!RinvE Rmult_inv_r_id_m => //.
rewrite exp.expRK => //=.
Qed.

End RPOps.

