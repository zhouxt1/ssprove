(** The "independent rule": combine two UNARY facts about [c1]/[c2],
  established completely separately (no shared state, no coupling
  argument at all), into a relational judgement [⊨⦃P⦄c1≈c2⦃Q⦄].

  This is the state-level building block for the bad-true branch of
  the up-to-bad adversary-linking induction: once a shared [bad] flag
  is already true, the two sides no longer need to be related by
  shared-code induction -- each side just needs to keep [bad] true
  *on its own* -- and [indp] (the product/independent coupling, see
  UpToBad.v) combines the two resulting unary facts into one relational
  postcondition for free, PROVIDED both sides are lossless (see
  UpToBad.v's [IndependentCoupling] section for why).

  Mirrors [reflexivity_rule]'s proof shape exactly (RulesStateProb.v),
  swapping the diagonal self-coupling [coupling_self_SDistr] for the
  product coupling [indp]. *)

From Stdlib Require Import Utf8.
Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".
Unset SsrOldRewriteGoalsOrder.

From SSProve.Relational Require Import OrderEnrichedCategory.
From SSProve.Crypt Require Import Axioms ChoiceAsOrd RulesStateProb.
From SSProve.Crypt.rhl_semantics.only_prob Require Import UpToBad.

Import Num.Theory.
Import RSemanticNotation.
#[local] Open Scope rsemantic_scope.
#[local] Open Scope ring_scope.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Lemma independent_rule
  { A1 A2 : ord_choiceType } { S1 S2 : choiceType }
  (c1 : FrStP S1 A1) (c2 : FrStP S2 A2)
  (P : (S1 * S2) → Prop) (Q : (A1 * S1) → (A2 * S2) → Prop)
  (Hlossless1 : ∀ s1 s2, P (s1, s2) → psum (θ_dens (θ0 c1 s1)) = 1)
  (Hlossless2 : ∀ s1 s2, P (s1, s2) → psum (θ_dens (θ0 c2 s2)) = 1)
  (HQ : ∀ s1 s2, P (s1, s2) →
    ∀ a1 s1' a2 s2',
      (0 < θ_dens (θ0 c1 s1) (a1, s1'))%R →
      (0 < θ_dens (θ0 c2 s2) (a2, s2'))%R →
      Q (a1, s1') (a2, s2'))
  : ⊨ ⦃ P ⦄ c1 ≈ c2 ⦃ Q ⦄.
Proof.
  move => [s1 s2] /=.
  move => π [Hpre Himp] /=.
  exists (indp (θ_dens (θ0 c1 s1)) (θ_dens (θ0 c2 s2))).
  split.
  - split.
    + exact: (indp_lmg _ _ (Hlossless2 s1 s2 Hpre)).
    + exact: (indp_rmg _ _ (Hlossless1 s1 s2 Hpre)).
  - move=> [a1 s1'] [a2 s2'] Hgt.
    apply: Himp.
    move: Hgt.
    rewrite (indp_ext (θ_dens (θ0 c1 s1)) (θ_dens (θ0 c2 s2)) (a1, s1') (a2, s2')) => Hgt.
    apply: (HQ s1 s2 Hpre a1 s1' a2 s2').
    { rewrite lt0r; apply/andP; split;
        [apply/eqP=>Hz; move: Hgt; by rewrite Hz GRing.mul0r Order.POrderTheory.ltxx
        | exact: ge0_mu]. }
    { rewrite lt0r; apply/andP; split;
        [apply/eqP=>Hz; move: Hgt; by rewrite Hz GRing.mulr0 Order.POrderTheory.ltxx
        | exact: ge0_mu]. }
Qed.
