Require Import Relation_Definitions Morphisms.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import mathcomp_extra exp reals signed.
From mathcomp Require Import boolp Rstruct.

From mathcomp.algebra_tactics Require Import ring lra.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Require Import ErrorMetrics.lemmas.
Require Import ErrorMetrics.relative_prec.

Local Open Scope ring_scope.

Section RelError.
  Context {R : realType}.

  Definition RelError (a a' α : R) : Prop := `| (a - a') / a | <= α.

  Notation "a ~ a' ; re( α )" := (RelError a a' α) (at level 99).

  Theorem RelPrecRelErrorConvert (a a' α : R): (a ~ a' ; rp(α)) -> (a ~ a' ; re(e `^ α - 1)).
  Proof. rewrite /RelError.
         move=> H1.
         apply RPProp1 in H1.
         pose proof (@RelPrecAltEquiv R a' a α).
         destruct H.
         pose proof (H H1).
         unfold RelPrecAlt in H2.
         destruct H2.
         destruct H3.
         destruct H3.

         suff lb1: `|(a - a') / a| <= e `^ `|x| - 1.
         suff lb2: e `^ `|x| - 1 <= e `^ α - 1.
         apply (le_trans lb1 lb2).

         apply lerB => //.
         apply e_exp_ge => //.
         rewrite mulrBl.
         rewrite mulfV.
         rewrite H3.
         rewrite distrC.

         case: (lerP 0 x) => ler0.
         {
           rewrite !ger0_norm.
           lra.
           lra.
           pose proof (e_exp_ge1 x ler0).
           lra.
         }
         {
           rewrite distrC.
           rewrite ger0_norm.
           suff lb3: 2 <= e `^ x + e `^ `|x|.
           lra.
           rewrite ler0_norm.
           apply e_del_ge2.
           lra.

           unfold e.
           rewrite -expRM.
           rewrite mul1r.
           suff lb4: sequences.expR x < 1. lra.
           rewrite expR_lt1 => //.
         }
         unfold RelPrec in H1.
         unfold NonZeroSameSign in H1.
         lra. Qed.
End RelError.
