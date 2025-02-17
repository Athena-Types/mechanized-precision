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

  (* Theorem RelPrecRelErrorConvert : *)

End RelError.
