From Flocq Require Import Core Round Relative.
From Coq Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect boolp ssrnum.
From mathcomp Require Import sequences exp Rstruct.

Local Open Scope R_scope.

Section RArithFacts.

Notation ln := exp.ln.

Lemma ln_div : 
  forall x y, 0 < x -> 0 < y -> ln (x/y) = ln x - ln y.
Proof.
move => x y Hx Hy. rewrite Rdiv_def RmultE RinvE RminusE ln_div => //;
rewrite ssrnum.Num.Theory.posrE; by apply /RltP.
Qed.

Lemma ln_x_lt_x :
  forall x, x > 0 ->ln x < x.
Proof.
move => x Hx.
apply /RltP. apply ln_sublinear. by apply /RltP.
Qed.

Lemma Rabs_ln_sym : 
  forall x y, 0 < x -> 0 < y -> Rabs(ln(x/y)) = Rabs(ln(y/x)).
Proof.
move => x y Hx Hy. 
rewrite !ln_div => //.
apply Rabs_minus_sym.
Qed.

Lemma ln_1_plus_le : 
  forall x, x <> 0 -> - 1 < x -> ln (1 + x) <= x.
Proof.
move => x Hx H1.
rewrite -{2}(expRK  x).
apply Rlt_le. apply /RltP. rewrite ltr_ln. 
rewrite expR_gt1Dx => //. 
apply /eqP => //. 
rewrite ssrnum.Num.Theory.posrE; apply /RltP.
rewrite /ssralg.GRing.zero => //=. nra.
rewrite ssrnum.Num.Theory.posrE;
apply expR_gt0.
Qed.

Lemma ln_le_div : 
  forall x, 0 < x -> x < 1 ->  -ln(1-x) <= x / (1-x).
Proof.
move => x H0 Hx.
rewrite -(expRK (x/(1-x))).
apply Rlt_le. apply /RltP. 
rewrite -ltr_expR.
rewrite expRN -RinvE !expRK lnK. 
apply /RltP; 
apply Rle_lt_trans with (1 + (x/(1-x))); [field_simplify ;nra | ].
apply /RltP. rewrite expR_gt1Dx => //.
rewrite /ssralg.GRing.zero => //=. apply /eqP. 
have Hx0 : x / (1-x) > 0; [|nra]. 
apply Rdiv_pos_pos => //; nra.
rewrite ssrnum.Num.Theory.posrE /ssralg.GRing.zero => //=. 
apply /RltP; nra.
Qed.

Lemma ln_le_div_rev : 
  forall x, 0< x < 1 -> -(x/(1-x)) <= ln(1-x).
Proof.
move => x H0.
rewrite -(Ropp_involutive (ln(1-x))).
apply Ropp_le_contravar, ln_le_div; nra.
Qed.

Lemma ln_le_increasing : 
forall x y, 0 < x -> 0 < y -> x <= y -> ln x <= ln y.
Proof.
move => x y Hx Hy Hxy.
destruct Hxy. apply Rlt_le. apply /RltP. 
rewrite ltr_ln; [ apply /RltP => // | |];   
rewrite ssrnum.Num.Theory.posrE /ssralg.GRing.zero => //=;
                                                        apply /RltP => //.
rewrite H. by apply Req_le.
Qed.

Lemma div_neg_pos :
  forall x y, x < 0 -> y < 0 -> 0 < x/y.
Proof.
move => x y Hx Hy. 
have Hx1 : 0 < -x by apply Ropp_neg => //.
have Hx2 : 0 < -y by apply Ropp_neg => //.
have H : x/y = - x / - y by rewrite Rdiv_opp_r Rdiv_opp_l; nra.
rewrite H; apply Rdiv_lt_0_compat => //.
Qed.

Lemma Rdiv_pos_pos_le : 
  forall x y, x > 0 -> y >= 0 -> 0<=y/x.
Proof.
move => x y Hx Hy. destruct Hy. 
apply Rlt_le, Rdiv_pos_pos => //.
rewrite H; nra.
Qed.

Lemma Rmult_le_lt_compat : 
  forall r1 r2 r3 r4,
    0 <= r1 -> 0 <= r2 -> 0 < r4 -> 
    r1 < r3 -> r2 <= r4 -> r1 * r2 < r3 * r4.
Proof.
move => r1 r2 r3 r4 H1 H2 H3 H4 H5.
destruct H5; [apply Rmult_lt_compat => //|
                                        rewrite H; apply Rmult_lt_compat_r => //].
Qed.

End RArithFacts.

Section ErrorTheorems.

Variable beta : radix.
Variable prec :  Z.

Hypothesis Hprec : (Prec_gt_0 prec).
Notation fexp := (FLX_exp prec).

Notation ln  := (exp.ln).
Notation exp := expR.

Fact round_preserves_sign_neg :
  forall rnd : R -> Z, Valid_rnd rnd -> 
  forall x, x < 0 -> round beta fexp rnd x < 0.
Proof.
move => rnd Hrnd x Hx.
have Hrx : round beta fexp rnd x <> 0%R.
{ apply: round_neq_0_negligible_exp => //; [ |nra]. 
apply negligible_exp_FLX, Hprec. }
case: (@round_le beta fexp _ _ _ x 0); [ nra |
                   rewrite (round_0 beta fexp _) =>//  | rewrite round_0 => //=].
Qed.

Fact round_preserves_sign_pos : 
forall rnd : R -> Z, Valid_rnd rnd -> 
  forall x, 0 < x -> 0 < round beta fexp rnd x.
move => rnd Hrnd x Hx.
have Hrx : round beta fexp rnd x <> 0%R.
{ apply: round_neq_0_negligible_exp => //; [ | nra].
apply negligible_exp_FLX, Hprec. } 
case: (@round_le beta fexp _ _ _ 0 x); [ nra |
                   rewrite (round_0 beta fexp _) =>//  | rewrite round_0 => //=].
move => H0. rewrite H0 in Hrx => //=.
Qed.

Lemma exp_error_model_conversion_aux : 
forall rnd : R -> Z, Valid_rnd rnd -> 
 forall (x b : R), 
  (0 < b) -> 
  (x <> 0 -> Rabs (ln (round beta fexp rnd x /x)) <= b) ->
  ( 0 < round beta fexp rnd x / x) -> 
  exists (eps : R), (Rabs eps <= b) /\ (round beta fexp rnd x = x * (exp eps)).
Proof.
move => rnd Hrnd x b Hb.
set (rx := round beta fexp rnd x).
case (Req_dec x 0) => Hx0.
{ exists 0%R; rewrite /rx Hx0 Rabs_R0 round_0; split => //; nra. }
move => Hx H1.
have Hxx : Rabs (ln (rx /x )) <= b by nra.
exists (ln (rx/x)); split => //; rewrite lnK => //. 
                             field_simplify => //.
rewrite ssrnum.Num.Theory.posrE /ssralg.GRing.zero => //=.
by apply /RltP. 
Qed. 

Lemma exp_error_model_le_conversion : 
forall rnd : R -> Z, Valid_rnd rnd ->  
forall (x b : R), 
  (0 < b) -> let RND := round beta fexp rnd in 
  (x <> 0 -> Rabs (ln (x/ RND x)) <= b) ->
  exists (eps : R), (Rabs eps <= b) /\ (RND x = x * (exp eps)).
Proof.
move => rnd Hrnd x b Hb.
case (Req_dec x 0) => Hx0.
{ exists 0%R; rewrite  Hx0 Rabs_R0 round_0; split => //; nra. }
simpl; move => H. apply exp_error_model_conversion_aux => //. 
case: (Rdichotomy x 0) => Hx1 => //.
rewrite -(Ropp_involutive (_ / _)) -Rdiv_opp_l -Rdiv_opp_r.
rewrite Rabs_ln_sym => //; try nra. rewrite Rdiv_opp_l Rdiv_opp_r Ropp_involutive => //.  
apply Ropp_0_gt_lt_contravar, round_preserves_sign_neg => //.
rewrite Rabs_ln_sym => //.
apply round_preserves_sign_pos => //.
apply Rdichotomy in Hx0. destruct Hx0;
[ apply div_neg_pos => //; apply round_preserves_sign_neg => // | 
  apply Rdiv_lt_0_compat => //; apply round_preserves_sign_pos => //].
Qed.

Lemma rnd_DN_lt_rel_prec: 
forall x, 
~ generic_format beta fexp x ->
0 < x -> ln (round beta fexp Zfloor x / x) < 0.
Proof.
move => x Hg Hx. rewrite ln_div => //.
apply Rlt_minus; apply /RltP; rewrite ltr_ln; apply /RltP.
destruct (round_DN_UP_lt beta fexp x) => //.
apply round_preserves_sign_pos => //.
apply valid_rnd_DN.
rewrite /ssralg.GRing.zero => //.
apply round_preserves_sign_pos => //.
by apply valid_rnd_DN.
Qed.

Lemma relative_prec_le_conversion : 
  forall x y b, 0 < x -> 0 < y -> 0 < b < 1 -> 
                Rabs ((x -y)/ x) <= b -> Rabs (ln(x/y)) <= b / (1-b).
Proof.
move => x y b Hx Hy Hb Hxy.
rewrite Rabs_ln_sym => //.
apply Rabs_le.
have H1 : -b <= y/x - 1 <= b.
{ apply Rabs_le_inv. apply Rle_trans with (Rabs((x-y)/x)) => //.
  apply Req_le. rewrite Rabs_minus_sym. 
  rewrite (Rdiv_def (x-y) x) Rmult_minus_distr_r -!Rdiv_def Rdiv_diag ; [|nra] => //. } 
have H01 : 1 -b <= y/x by nra.
have H11 : y/x <= 1 + b by nra.
split. 
{ apply ln_le_increasing in H01; try nra.
eapply Rle_trans with (ln (1 - b)) => //.
apply ln_le_div_rev => //. } 
apply ln_le_increasing in H11; try nra.
apply Rle_trans with (ln(1+b)) => //.
apply Rle_trans with b. apply ln_1_plus_le; nra.
have : b * 1 <= b * (1/(1-b)); try nra.
apply Rmult_le_compat_l; try nra.  
apply Rmult_le_reg_r with (1-b); [nra | ].
rewrite -Rmult_div_swap Rmult_1_l Rdiv_diag; [|nra].
apply Rplus_le_reg_r with b. field_simplify; nra.
Qed.
 
Theorem relative_prec_error :
  forall rnd : R -> Z, Valid_rnd rnd ->
  (1 < prec)%Z -> 
  forall x, x <> 0 -> 
            let b:= bpow beta (-prec + 1)%Z in 
            Rabs (ln (x/round beta fexp rnd x)) <= b / (1- b).
Proof.
move => rnd Hrnd Hprec1 x Hx0.
have Hp: bpow beta (-prec + 1) < bpow beta 0 => //.
{ apply bpow_lt; lia. } 
case: (Rdichotomy x 0) => // Hx. 
(* x < 0 *)
{ rewrite -(Ropp_involutive (_/_)) -Rdiv_opp_l -Rdiv_opp_r.
apply relative_prec_le_conversion; try nra.
apply Ropp_0_gt_lt_contravar, round_preserves_sign_neg => //.
split; [apply bpow_gt_0 | ] => //.
rewrite Rdiv_opp_r -Ropp_minus_distr Rdiv_opp_l Ropp_involutive.
rewrite Rdiv_def Rabs_mult Rabs_inv. 
apply Rmult_le_reg_r with (Rabs x); [apply Rabs_pos_lt => //|].
field_simplify;[|apply Rabs_no_R0 => //]. rewrite -Rabs_Ropp Rmult_comm.
replace (-(- _ -- _)) with (round beta fexp rnd x - x) by nra.
apply Rlt_le, relative_error_FLX => //; try lia. }
(* 0 < x *)
apply relative_prec_le_conversion; try nra.
apply round_preserves_sign_pos => //.
split; [apply bpow_gt_0 | ] => //.
rewrite Rdiv_def Rabs_mult Rabs_minus_sym Rabs_inv.
apply Rmult_le_reg_r with (Rabs x); [apply Rabs_pos_lt => //|].
field_simplify;[| apply Rabs_no_R0 => //].
apply Rlt_le. rewrite Rmult_comm.
apply relative_error_FLX => //; try lia.
Qed.

Theorem exp_error_model: 
  forall rnd : R -> Z, Valid_rnd rnd ->
  ( 1 < prec)%Z -> 
  forall (x : R), 
  let b:= bpow beta (-prec + 1)%Z in 
  exists (eps : R), (Rabs eps <= b/(1-b)) /\ (round beta fexp rnd x = x * (exp eps)).
Proof.
move => rnd Hrnd Hprec1 x.
have Hp: bpow beta (-prec + 1) < 1.
{ suff : bpow beta (-prec + 1) < bpow beta 0 => //.
 apply bpow_lt. lia. } 
case : (Req_dec x 0) => // H0.
{ exists 0; split; try nra. rewrite Rabs_R0. apply Rlt_le, Rdiv_lt_0_compat; 
    [apply bpow_gt_0| nra]. rewrite H0 round_0; nra. } 
apply exp_error_model_le_conversion => //.
apply Rdiv_lt_0_compat; [apply bpow_gt_0 | nra].
move => _.
apply relative_prec_error => //.
Qed.

End ErrorTheorems.
