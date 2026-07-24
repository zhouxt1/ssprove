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
  pkg_invariants pkg_distr Casts fmap_extra pkg_rhl pkg_lossless FreeProbProg.
From SSProve.Crypt.nominal Require Import Pr.
From SSProve.Crypt.rules Require Import UpToBadState.

Arguments retrFree {_ _ _} _.
Arguments bindrFree {_ _ _ _} _ _.
Arguments ropr {_ _ _} _ _.

Import Num.Theory.
Import SPropNotations.
Import PackageNotation.
Import RSemanticNotation.
#[local] Open Scope rsemantic_scope.
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

(** A single unary fact bundling losslessness with "[bad_loc] stays
  true", stated in [Pr_code]'s vocabulary (matching pkg_lossless.v --
  the bridge to the [θ_dens ∘ θ0 ∘ repr] vocabulary [independent_rule]
  needs is applied only once, at the point [independent_rule] actually
  gets invoked, via [Pr_code_theta_bridge]). *)
Definition bad_lossless (bad_id : nat) {A : choiceType} (c : raw_code A)
  (h : heap) : Prop :=
  psum (Pr_code c h) = 1 ∧
  (∀ a h', (0 < Pr_code c h (a, h'))%R → get_heap h' (bad_loc bad_id) = true).

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
    bad_lossless bad_id (resolve p (id, (S, T)) x) h.

(** Like [lossless_valid] (pkg_lossless.v), but for ADVERSARY code:
  unlike a package's own code, adversary code genuinely calls oracles
  ([opr] nodes reachable, unlike [lossless_valid] which forbids them
  entirely) -- those calls just aren't required to be lossless HERE,
  since [bad_preserved_link] below discharges that separately via
  [bad_preserved]. *)
Inductive lossless_valid_adv {A : choiceType} (L : Locations) (E : Interface)
  : raw_code A → Prop :=
| lva_ret : ∀ x, lossless_valid_adv L E (ret x)
| lva_opr : ∀ o x k,
    fhas E o →
    (∀ v, lossless_valid_adv L E (k v)) →
    lossless_valid_adv L E (opr o x k)
| lva_getr : ∀ l k,
    fhas L l →
    (∀ v, lossless_valid_adv L E (k v)) →
    lossless_valid_adv L E (getr l k)
| lva_putr : ∀ l v k,
    fhas L l →
    lossless_valid_adv L E k →
    lossless_valid_adv L E (putr l v k)
| lva_sampler : ∀ op k,
    LosslessOp op →
    (∀ v, lossless_valid_adv L E (k v)) →
    lossless_valid_adv L E (sampler op k).

(** Bind-composition of [bad_lossless]: if [c]'s denotation from [h] is
  lossless and keeps [bad_loc] true, and every reachable continuation
  is too, so is the whole bind. Mirrors [Pr_code_bind]'s structure via
  [dletC]/[Pr_fstC]-style dlet-of-lossless reasoning. *)
Lemma bad_lossless_bind (bad_id : nat) {A B : choiceType}
  (c : raw_code A) (f : A → raw_code B) (h : heap) :
  bad_lossless bad_id c h →
  (∀ a h', (0 < Pr_code c h (a, h'))%R → bad_lossless bad_id (f a) h') →
  bad_lossless bad_id (bind c f) h.
Proof.
  move=> [Hc1 Hc2] Hf.
  rewrite /bad_lossless Pr_code_bind. split.
  - under eq_psum do rewrite dletE.
    rewrite __admitted__interchange_psum.
    + rewrite (eq_psum (F2 := Pr_code c h)) //.
      move=> [a h']. case: (eqVneq (Pr_code c h (a, h')) 0) => Ha.
      * rewrite Ha; under eq_psum do rewrite GRing.mul0r; exact: psum0.
      * have Hpos : (0 < Pr_code c h (a, h'))%R.
        { rewrite lt0r. apply/andP; split; [exact: Ha | exact: ge0_mu]. }
        rewrite (psumZ _ (ge0_mu _ _)) (Hf a h' Hpos).1 GRing.mulr1 //.
    + move=> x. apply: summable_mu_wgtd => y.
      apply/andP; split; [exact: ge0_mu | exact: le1_mu1].
    + apply: (eq_summable (S1 := Pr_code (bind c f) h));
        [move=> x; by rewrite Pr_code_bind dletE | exact: summable_mu].
  - move=> b h'' Hgt.
    move: Hgt; rewrite dletE => Hgt.
    have Hne : psum (fun y : A * heap => Pr_code c h y * Pr_code (f y.1) y.2 (b, h'')) <> 0.
    { move=> Habs. move: Hgt. rewrite Habs. by rewrite Order.POrderTheory.ltxx. }
    have [[a h'] Hne2] := neq0_psum Hne.
    have Ha0 : Pr_code c h (a, h') != 0.
    { apply/eqP => Hz. apply: Hne2. by rewrite /= Hz GRing.mul0r. }
    have HaPos : (0 < Pr_code c h (a, h'))%R.
    { rewrite lt0r. apply/andP; split; [exact: Ha0 | exact: ge0_mu]. }
    have Hb0 : Pr_code (f a) h' (b, h'') != 0.
    { apply/eqP => Hz. apply: Hne2. by rewrite /= Hz GRing.mulr0. }
    have HbPos : (0 < Pr_code (f a) h' (b, h''))%R.
    { rewrite lt0r. apply/andP; split; [exact: Hb0 | exact: ge0_mu]. }
    exact: (Hf a h' HaPos).2 b h'' HbPos.
Qed.

(** [bad_lossless], transported into the [θ_dens ∘ θ0 ∘ repr] vocabulary
  [independent_rule] (UpToBadState.v) needs, via [Pr_code_theta_bridge]. *)
Lemma theta_bad_lossless (bad_id : nat) {A : choiceType} (c : raw_code A)
  (h : heap) :
  bad_lossless bad_id c h →
  psum (θ_dens (θ0 (repr c) h)) = 1 ∧
  (∀ a h', (0 < θ_dens (θ0 (repr c) h) (a, h'))%R →
     get_heap h' (bad_loc bad_id) = true).
Proof.
  rewrite /bad_lossless -Pr_code_theta_bridge. done.
Qed.

(** [bad_preserved] (a fact about ONE oracle call) transported through
  [code_link]'s WHOLE structural recursion over the adversary's code:
  once [bad_loc] is true entering [code_link A p], it stays true
  throughout, and the whole thing is lossless. Requires the adversary's
  own locations to avoid [bad_loc] (so its own gets/puts can't disturb
  it) and its own samples to be lossless ([lossless_valid_adv]). *)
Lemma bad_preserved_link {L LA E} (p : raw_package) (bad_id : nat)
  {B} (A : raw_code B)
  `{ValidPackage L Game_import E p} `{@ValidCode LA E B A} :
  lossless_valid_adv LA E A →
  bad_id \notin domm LA →
  bad_preserved E bad_id p →
  ∀ h, get_heap h (bad_loc bad_id) = true → bad_lossless bad_id (code_link A p) h.
Proof.
  move=> Hlva Hfresh Hbp.
  induction Hlva as [x | o x k Ho k' IH | l k Hl k' IH | l v k Hl IH | op k Hop k' IH].
  - move=> h Hh. rewrite /bad_lossless Pr_code_ret. split.
    + exact: Couplings.psum_SDistr_unit.
    + move=> a h' Hgt. move: Hgt; rewrite dunit1E.
      case: eqP => [[_ <-] _|_//].
      * exact: Hh.
      * rewrite ltr0n; done.
  - move=> h Hh.
    apply inversion_valid_opr in H0 as [Hin vk].
    destruct o as [id [S T]].
    rewrite /=. apply: bad_lossless_bind.
    + exact: (Hbp id S T x h Hin Hh).
    + move=> a h' Hgt. apply: (IH a (vk a) h').
      exact: (Hbp id S T x h Hin Hh).2 a h' Hgt.
  - move=> h Hh.
    apply inversion_valid_getr in H0 as [Hin vk]. rewrite /= /bad_lossless Pr_code_get.
    apply: (IH (get_heap h l) (vk (get_heap h l)) h Hh).
  - move=> h Hh.
    apply inversion_valid_putr in H0 as [Hin vk]. rewrite /= /bad_lossless Pr_code_put.
    apply: (IHIH vk (set_heap h l v)).
    rewrite get_set_heap_neq //.
    apply/eqP => Heq.
    have Hindomm := fhas_in LA l Hin.
    have Heq' : bad_id = l.1 := Heq.
    move/dommPn: Hfresh => Hfresh.
    move: Hfresh; rewrite Heq'; move/dommP: Hindomm => [v0 ->]; discriminate.
  - move=> h Hh. rewrite /bad_lossless Pr_code_sample.
    under eq_psum do rewrite dletE.
    rewrite __admitted__interchange_psum.
    + have vk := inversion_valid_sampler LA E H0.
      split.
      * rewrite (eq_psum (F2 := op.π2)) //.
        move=> y. rewrite psumZ ?ge0_mu //.
        rewrite (IH y (vk y) h Hh).1 GRing.mulr1 //.
      * move=> a h' Hgt.
        move: Hgt; rewrite dletE => Hgt.
        have Hne : psum (fun y : Arit op => op.π2 y * Pr_code (code_link (k y) p) h (a, h')) <> 0.
        { move=> Habs. move: Hgt. rewrite Habs. by rewrite Order.POrderTheory.ltxx. }
        have [y Hney] := neq0_psum Hne.
        have Hyb : op.π2 y != 0.
        { apply/eqP => Hz. apply: Hney. by rewrite Hz GRing.mul0r. }
        have HyPos : (0 < op.π2 y)%R.
        { rewrite lt0r. apply/andP; split; [exact: Hyb | exact: ge0_mu]. }
        have Hab : Pr_code (code_link (k y) p) h (a,h') != 0.
        { apply/eqP => Hz. apply: Hney. by rewrite Hz GRing.mulr0. }
        have HabPos : (0 < Pr_code (code_link (k y) p) h (a,h'))%R.
        { rewrite lt0r. apply/andP; split; [exact: Hab | exact: ge0_mu]. }
        exact: (IH y (vk y) h Hh).2 a h' HabPos.
    + move=> x. apply: summable_mu_wgtd => y.
      apply/andP; split; [exact: ge0_mu | exact: le1_mu1].
    + apply: (eq_summable (S1 := Pr_code (sampler op (fun y => code_link (k y) p)) h));
        [move=> x; by rewrite Pr_code_sample dletE | exact: summable_mu].
Qed.

Lemma eq_up_to_bad_adversary_link :
  ∀ {L₀ L₁ LA E} (p₀ p₁ : raw_package) (I : precond) (bad_id : nat)
    {B} (A : raw_code B)
    `{ValidPackage L₀ Game_import E p₀}
    `{ValidPackage L₁ Game_import E p₁}
    `{@ValidCode LA E B A},
    INV LA I →
    lossless_valid_adv LA E A →
    bad_id \notin domm LA →
    (∀ s₀ s₁, I (s₀, s₁) →
       get_heap s₀ (bad_loc bad_id) = get_heap s₁ (bad_loc bad_id)) →
    (∀ s₀ s₁, get_heap s₀ (bad_loc bad_id) = true →
       get_heap s₁ (bad_loc bad_id) = true → I (s₀, s₁)) →
    eq_up_to_bad E I bad_id p₀ p₁ →
    bad_preserved E bad_id p₀ →
    bad_preserved E bad_id p₁ →
    r⊨ ⦃ I ⦄ code_link A p₀ ≈ code_link A p₁
      ⦃ λ '(b₀, s₀) '(b₁, s₁),
          I (s₀, s₁) ∧ (get_heap s₀ (bad_loc bad_id) = false → b₀ = b₁) ⦄.
Proof.
  intros L₀ L₁ LA E p₀ p₁ I bad_id B A vp₀ vp₁ vA hLA Hlva Hfresh Hsync HbadI hp hbp0 hbp1.
  induction Hlva as [x | o x k Ho k' IH | l k Hl k' IH | l v k Hl IH | op k Hop k' IH] in vA |- *.
  - cbn - [semantic_judgement].
    eapply weaken_rule. 1: apply ret_rule.
    intros [h₀ h₁] post.
    cbn. unfold SPropMonadicStructures.SProp_op_order.
    unfold Basics.flip, SPropMonadicStructures.SProp_order.
    intros [HI Hp].
    apply Hp. split; [exact: HI | done].
  - cbn - [semantic_judgement].
    apply inversion_valid_opr in vA as hA. destruct hA as [hi vk].
    have vp₀' := vp₀. have vp₁' := vp₁.
    destruct vp₀ as [vp0e vp0i].
    specialize (vp0e o) as [vp0e _].
    specialize (vp0e hi) as [f₀ e₀].
    destruct vp₁ as [vp1e vp1i].
    specialize (vp1e o) as [vp1e _].
    specialize (vp1e hi) as [f₁ e₁].
    destruct o as [id [T S]].
    specialize (hp id T S x hi).
    rewrite /resolve e₀ e₁ 2!coerce_kleisliE in hp |- *.
    rewrite 2!repr_bind.
    eapply bind_rule_pp. 1:{ eapply to_sem_jdg in hp. exact hp. }
    cbn - [semantic_judgement].
    intros a₀ a₁.
    apply pre_hypothesis_rule.
    intros s₀ s₁ [HI Hcond].
    case: (boolP (get_heap s₀ (bad_loc bad_id))) => Hbad.
    + have Hbad1 : get_heap s₁ (bad_loc bad_id) = true.
      { move: Hbad => /= Hbad. rewrite -(Hsync s₀ s₁ HI). exact: Hbad. }
      apply: independent_rule.
      * move=> s1 s2 [Heq1 Heq2] /=. cbn in Heq1. rewrite Heq1.
        exact: (theta_bad_lossless bad_id (code_link (k a₀) p₀) s₀
                 (bad_preserved_link p₀ bad_id (k a₀) (k' a₀) Hfresh hbp0 s₀ Hbad)).1.
      * move=> s1 s2 [Heq1 Heq2] /=. cbn in Heq2. rewrite Heq2.
        exact: (theta_bad_lossless bad_id (code_link (k a₁) p₁) s₁
                 (bad_preserved_link p₁ bad_id (k a₁) (k' a₁) Hfresh hbp1 s₁ Hbad1)).1.
      * move=> s1 s2 [Heq1 Heq2] a1 s1' a2 s2' Hgt1 Hgt2.
        cbn in Heq1, Heq2. subst s1 s2.
        have Hm1 := (theta_bad_lossless bad_id (code_link (k a₀) p₀) s₀
                      (bad_preserved_link (L:=L₀) p₀ bad_id (k a₀) (k' a₀) Hfresh hbp0 s₀ Hbad)).2 a1 s1' Hgt1.
        have Hm2 := (theta_bad_lossless bad_id (code_link (k a₁) p₁) s₁
                      (bad_preserved_link (L:=L₁) p₁ bad_id (k a₁) (k' a₁) Hfresh hbp1 s₁ Hbad1)).2 a2 s2' Hgt2.
        move: (Hm1 vp₀' (vk a₀)) (Hm2 vp₁' (vk a₁)) => {}Hm1 {}Hm2.
        split.
        { exact: (HbadI s1' s2' Hm1 Hm2). }
        { rewrite Hm1. discriminate. }
    + move: Hbad => /negbTE Hbad.
      move: (Hcond Hbad) => Heq. subst a₁.
      eapply pre_weaken_rule. 1: eapply IH.
      * eapply vk.
      * cbn. intros s₀' s₁' [? ?]. subst. auto.
  - cbn - [semantic_judgement bindrFree].
    apply inversion_valid_getr in vA as hA. destruct hA as [hi vk].
    match goal with
    | |- ⊨ ⦃ ?pre_ ⦄ bindrFree ?m_ ?f1_ ≈ bindrFree _ ?f2_ ⦃ ?post_ ⦄ =>
      eapply (bind_rule_pp (f1 := f1_) (f2 := f2_) m_ m_ pre_ _ post_)
    end.
    + eapply (get_case LA). all: auto.
    + intros a₀ a₁. cbn - [semantic_judgement].
      eapply pre_hypothesis_rule.
      intros s₀ s₁ [? ?]. subst a₁.
      eapply pre_weaken_rule. 1: eapply IH.
      * eapply vk.
      * cbn. intros s₀' s₁' [? ?]. subst. auto.
  - cbn - [semantic_judgement bindrFree].
    apply inversion_valid_putr in vA as hA. destruct hA as [hi vk].
    match goal with
    | |- ⊨ ⦃ ?pre_ ⦄ bindrFree ?m_ ?f1_ ≈ bindrFree _ ?f2_ ⦃ ?post_ ⦄ =>
      eapply (bind_rule_pp (f1 := f1_) (f2 := f2_) m_ m_ pre_ _ post_)
    end.
    + eapply (@put_case LA). all: auto.
    + intros a₀ a₁. cbn - [semantic_judgement].
      eapply pre_hypothesis_rule.
      intros s₀ s₁ [? ?]. subst a₁.
      eapply pre_weaken_rule. 1: eapply IHIH.
      * eapply vk.
      * cbn. intros s₀' s₁' [? ?]. subst. auto.
  - cbn - [semantic_judgement bindrFree].
    eapply bind_rule_pp.
    + eapply (@sampler_case LA). auto.
    + intros a₀ a₁. cbn - [semantic_judgement].
      eapply pre_hypothesis_rule.
      intros s₀ s₁ [? ?]. subst a₁.
      eapply pre_weaken_rule. 1: eapply IH.
      * eapply inversion_valid_sampler. eauto.
      * cbn. intros s₀' s₁' [? ?]. subst. auto.
Qed.
