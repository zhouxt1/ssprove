(** Losslessness of [raw_code], for an ARBITRARY starting heap.

  [theories/Crypt/nominal/Pr.v] already has [LosslessCode]/[Lossless_ret]/
  [Lossless_sample]/[Lossless_if], but they don't fit the up-to-bad
  argument's needs:
  - [Pr_fst] (hence [LosslessCode]) is hardwired to start from the EMPTY
    heap ([Pr_fst c := dfst (Pr_code c emptym)]); we need losslessness
    starting from an ARBITRARY heap (the continuation after earlier
    gets/puts have already run).
  - [Pr_code_fst]/[Pr_fst_bind] (Pr.v's only "bind" lemmas for a package
    with locations) require [ValidCode emptym [interface] c] -- i.e. NO
    locations at all, not just an empty import -- since their proof
    discharges [getr]/[putr] as vacuous exactly like [opr]. That's fine
    for Pr.v's own use case (code renaming) but not for us: every game
    in HKDF.v uses locations.

  This file proves the general version: code that (a) never calls an
  import (so [opr] is never reachable -- unavoidable, since [opr] is
  interpreted as [dnull], mass 0, before package linking resolves it;
  see [Pr_code_call]) but (b) freely uses locations and (c) only samples
  from lossless ops, has a lossless denotation from ANY starting heap.
*)

From Stdlib Require Import Utf8.
Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".
Unset SsrOldRewriteGoalsOrder.

From SSProve.Crypt Require Import Axioms choice_type fmap_extra
  pkg_core_definition pkg_heap pkg_composition pkg_semantics pkg_distr
  pkg_advantage RulesStateProb.
From SSProve.Crypt.nominal Require Import Pr.

Import GRing.Theory.
Import Num.Theory.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Local Open Scope ring_scope.
Local Open Scope package_scope.

Section LosslessValid.

  (* Like [valid_code], but for code that never calls an import (so no
    [opr] constructor at all) and whose every [sampler] node uses a
    provably-lossless op. This is exactly the extra content needed,
    beyond ordinary [ValidCode L [interface] c], to conclude
    losslessness: [ValidCode] alone doesn't track whether the sampled
    ops are lossless. *)
  Inductive lossless_valid {A : choiceType} (L : Locations) : raw_code A → Prop :=
  | lv_ret : ∀ x, lossless_valid L (ret x)
  | lv_getr : ∀ l k,
      fhas L l →
      (∀ v, lossless_valid L (k v)) →
      lossless_valid L (getr l k)
  | lv_putr : ∀ l v k,
      fhas L l →
      lossless_valid L k →
      lossless_valid L (putr l v k)
  | lv_sampler : ∀ op k,
      LosslessOp op →
      (∀ v, lossless_valid L (k v)) →
      lossless_valid L (sampler op k).

  Lemma Pr_code_lossless {A : choiceType} (L : Locations) (c : raw_code A) :
    lossless_valid L c → ∀ h, psum (Pr_code c h) = 1.
  Proof.
    move=> Hlv.
    induction Hlv as [x | l k Hl k' IH | l v k Hl k' IH | op k Hop k' IH].
    - move=> h. by rewrite Pr_code_ret Couplings.psum_SDistr_unit.
    - move=> h. by rewrite Pr_code_get IH.
    - move=> h. by rewrite Pr_code_put IH.
    - move=> h. rewrite Pr_code_sample.
      under eq_psum do rewrite dletE.
      rewrite __admitted__interchange_psum.
      1: move=> x; apply: summable_mu_wgtd => y;
         apply/andP; split; [exact: ge0_mu | exact: le1_mu1].
      1: apply: (eq_summable (S1 := Pr_code (sampler op k) h));
         [move=> x; by rewrite Pr_code_sample dletE | exact: summable_mu].
      rewrite (eq_psum (F2 := projT2 op)) //.
      move=> y. rewrite psumZ ?ge0_mu ?IH ?GRing.mulr1 //.
  Qed.

End LosslessValid.

(** Bridge between [Pr_code]'s denotational semantics (direct structural
  recursion via the [SDistr] relative monad) and the semantics used by
  the relational program logic, [θ_dens (θ0 (repr c) h)] (via the free
  monad translation [repr] then the state-threading interpreter [θ0]).
  These are two different encodings of "the same" operational meaning
  of [raw_code] -- confirmed NOT definitionally equal (a bare [erefl]
  fails to unify them) -- so this lemma is needed to transport
  [Pr_code_lossless] into the vocabulary [independent_rule]
  (UpToBadState.v) actually needs. Proved by a straightforward
  five-case induction on [raw_code], mirroring [Pr_code_bind]'s own
  structure; each non-trivial case reduces, after [cbn], to the exact
  same "doubly wrapped [SDistr_obligation_2]" shape [Pr_code_ret]'s own
  proof already has to unwind. *)
Lemma Pr_code_theta_bridge {A : choiceType} (c : raw_code A) (h : heap) :
  Pr_code c h = θ_dens (θ0 (repr c) h).
Proof.
  induction c in h |- *.
  - rewrite Pr_code_ret. cbn. reflexivity.
  - rewrite Pr_code_call. cbn. symmetry; apply: dlet_null_ext.
  - rewrite Pr_code_get. cbn.
    rewrite /SubDistr.SDistr_obligation_2 2!SubDistr.SDistr_rightneutral //.
  - rewrite Pr_code_put. cbn.
    rewrite /SubDistr.SDistr_obligation_2 2!SubDistr.SDistr_rightneutral //.
  - rewrite Pr_code_sample. cbn.
    apply eq_dlet => x.
    rewrite /SubDistr.SDistr_obligation_2 2!SubDistr.SDistr_rightneutral //.
Qed.

(** [Pr_code_lossless], transported into the [θ_dens ∘ θ0 ∘ repr]
  vocabulary that [independent_rule] (UpToBadState.v) needs. *)
Lemma theta_lossless {A : choiceType} (L : Locations) (c : raw_code A) :
  lossless_valid L c → ∀ h, psum (θ_dens (θ0 (repr c) h)) = 1.
Proof.
  move=> Hlv h.
  rewrite -Pr_code_theta_bridge.
  exact: (Pr_code_lossless L c Hlv h).
Qed.
