(** The "Fundamental Lemma of Game-Playing", lifted through packages.

  [eq_up_to_inv]/[eq_up_to_inv_adversary_link] (pkg_rhl.v) prove two
  packages equivalent oracle-by-oracle, but require an EXACT match
  (b₀ = b₁) at every single call -- too strong once the two sides can
  genuinely diverge. This file relaxes that to "match until [bad_loc]
  fires", using [independent_rule] (UpToBadState.v) for the branch
  where [bad_loc] is already true entering an oracle call (no relation
  between the two sides survives at that point -- each side just needs
  to keep [bad_loc] true on its own, from there on).
*)

From Stdlib Require Import Utf8.
From SSProve.Relational Require Import OrderEnrichedCategory
  OrderEnrichedRelativeMonadExamples.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice order reals distr seq all_algebra fintype realsum.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap.
From SSProve.Mon Require Import SPropBase.
(* NOTE: this import list/order intentionally mirrors pkg_rhl.v's own
  verbatim (up to appending pkg_lossless/UpToBadState at the end) --
  reordering it (e.g. moving RulesStateProb after pkg_rhl instead of
  before pkg_core_definition) was empirically confirmed to break the
  [r⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄] notation's elaboration: [pre : precond]
  stops unifying against [fromPrePost]'s implicit [choiceType] argument
  ("The term ... has type precond while it is expected to have type
  choice.Choice.sort ?S1 * ... -> Prop"), apparently because canonical
  structure resolution for [heap] is import-order-sensitive. *)
From SSProve.Crypt Require Import Prelude Axioms ChoiceAsOrd SubDistr Couplings
  RulesStateProb UniformStateProb UniformDistrLemmas StateTransfThetaDens
  StateTransformingLaxMorph choice_type pkg_core_definition pkg_notation
  pkg_tactics pkg_composition pkg_heap pkg_semantics pkg_advantage
  pkg_invariants pkg_distr Casts fmap_extra pkg_rhl pkg_lossless.
From SSProve.Crypt.rules Require Import UpToBadState.

Import Num.Theory.
Import SPropNotations.
Import PackageNotation.
Import RSemanticNotation.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

(** The shared, monotone "bad" flag: a boolean location, identified by
  its underlying [nat] key [bad_id] (so [get_heap h (bad_loc bad_id)]
  is concretely [bool]-typed, matching e.g. HKDF.v's own
  [bad_loc := mkloc 4 (false : bool)]). *)
Definition bad_loc (bad_id : nat) : Location := mkloc bad_id (false : bool).

(** The relaxed per-oracle guarantee: same as [eq_up_to_inv], except
  the outputs are only required to match while [bad_loc] is false. *)
Definition eq_up_to_bad (E : Interface) (I : precond) (bad_id : nat)
  (p₀ p₁ : raw_package) :=
  ∀ (id : ident) (S T : choice_type) (x : S),
    fhas E (id, (S, T)) →
    ⊢ ⦃ λ '(s₀, s₁), I (s₀, s₁) ⦄
      resolve p₀ (id, (S, T)) x ≈ resolve p₁ (id, (S, T)) x
      ⦃ λ '(b₀, s₀) '(b₁, s₁),
          I (s₀, s₁) ∧ (get_heap s₀ (bad_loc bad_id) = false → b₀ = b₁) ⦄.

(** The extra, UNARY fact needed for the bad-true branch: once
  [bad_loc] is true entering a given oracle call on package [p], (a) it
  stays true, and (b) the call is lossless (needed for
  [independent_rule]'s product coupling to be a valid coupling at
  all). *)
Definition bad_preserved (E : Interface) (bad_id : nat)
  (p : raw_package) :=
  ∀ (id : ident) (S T : choice_type) (x : S) (h : heap),
    fhas E (id, (S, T)) →
    get_heap h (bad_loc bad_id) = true →
    psum (θ_dens (θ0 (repr (resolve p (id, (S, T)) x)) h)) = 1 ∧
    (∀ a h', (0 < θ_dens (θ0 (repr (resolve p (id, (S, T)) x)) h) (a, h'))%R →
       get_heap h' (bad_loc bad_id) = true).

Lemma eq_up_to_bad_adversary_link :
  ∀ {L₀ L₁ LA E} (p₀ p₁ : raw_package) (I : precond) (bad_id : nat)
    {B} (A : raw_code B)
    `{ValidPackage L₀ Game_import E p₀}
    `{ValidPackage L₁ Game_import E p₁}
    `{@ValidCode LA E B A},
    INV LA I →
    eq_up_to_bad E I bad_id p₀ p₁ →
    bad_preserved E bad_id p₀ →
    bad_preserved E bad_id p₁ →
    r⊨ ⦃ I ⦄ code_link A p₀ ≈ code_link A p₁
      ⦃ λ '(b₀, s₀) '(b₁, s₁),
          I (s₀, s₁) ∧ (get_heap s₀ (bad_loc bad_id) = false → b₀ = b₁) ⦄.
Proof.
Admitted.
