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
From SSProve.Crypt.rhl_semantics.only_prob Require Import UpToBad.
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
    eq_up_to_bad E I bad_id p₀ p₁ →
    bad_preserved E bad_id p₀ →
    bad_preserved E bad_id p₁ →
    r⊨ ⦃ I ⦄ code_link A p₀ ≈ code_link A p₁
      ⦃ λ '(b₀, s₀) '(b₁, s₁),
          get_heap s₀ (bad_loc bad_id) = false → I (s₀, s₁) ∧ b₀ = b₁ ⦄.
Proof.
  intros L₀ L₁ LA E p₀ p₁ I bad_id B A vp₀ vp₁ vA hLA Hlva Hfresh Hsync hp hbp0 hbp1.
  induction Hlva as [x | o x k Ho k' IH | l k Hl k' IH | l v k Hl IH | op k Hop k' IH] in vA |- *.
  - cbn - [semantic_judgement].
    eapply weaken_rule. 1: apply ret_rule.
    intros [h₀ h₁] post.
    cbn. unfold SPropMonadicStructures.SProp_op_order.
    unfold Basics.flip, SPropMonadicStructures.SProp_order.
    intros [HI Hp].
    apply Hp. move=> Hb. split; [exact: HI | done].
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
        move: (Hm1 vp₀' (vk a₀)) => {}Hm1.
        rewrite Hm1. discriminate.
    + move: Hbad => /negbTE Hbad.
      move: (Hcond Hbad) => Heq. subst a₁.
      eapply pre_weaken_rule. 1: eapply IH.
      * eapply vk.
      * cbn. intros s₀' s₁' Hpost. case: Hpost => -> ->. exact: HI.
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

(** Turns a relational judgement into the actual probability bound,
  via [pr_up_to_bad] (UpToBad.v) -- mirrors [Pr_eq] (RulesStateProb.v),
  which does the analogous thing for EXACT equality (using
  [Hagree]-only, no sync fact: [pr_up_to_bad] doesn't need [bad] to be
  literally synced across the coupling's support, only that [event]
  agrees wherever [bad] is false on the LEFT side). *)
Lemma Pr_bound {X : ord_choiceType} {S : choiceType}
  {event bad : pred (X * S)}
  (Psi : S * S → Prop) (phi : (X * S) → (X * S) → Prop)
  (c1 c2 : RulesStateProb.FrStP S X)
  (H : ⊨ ⦃ Psi ⦄ c1 ≈ c2 ⦃ phi ⦄)
  {s1 s2 : S} (HPsi : Psi (s1, s2))
  (Hagree : ∀ x y, phi x y → bad x = false → event x = event y) :
  `| \P_[θ_dens (θ0 c1 s1)] event - \P_[θ_dens (θ0 c2 s2)] event |
  <= \P_[θ_dens (θ0 c1 s1)] bad.
Proof.
  specialize (H (s1, s2) (fun '(a, b) => phi a b)). simpl in H.
  have Hd := H (conj HPsi (fun a b h => h)).
  destruct Hd as [d [[Hd0 Hd1] Hsupp]].
  apply: (pr_up_to_bad _ _ d Hd0 Hd1 event bad).
  move=> x y Hgt Hb. exact: (Hagree x y (Hsupp x y Hgt) Hb).
Qed.

(** [Pr], but reading [bad_loc]'s final value instead of the run's own
  boolean output -- the RHS of the top-level Fundamental Lemma bound,
  [eq_upto_bad_perf_ind] below. *)
Definition Pr_bad (p : raw_package) (bad_id : nat) : SDistr (bool : choiceType) :=
  SDistr_bind (fun '(_, s) => SDistr_unit _ (get_heap s (bad_loc bad_id)))
    (Pr_op p RUN tt empty_heap).

(** The Fundamental Lemma of Game-Playing, in [AdvantageE]'s own
  vocabulary: mirrors [eq_upto_inv_perf_ind] (pkg_rhl.v, which gives
  [AdvantageE p₀ p₁ A = 0] from an EXACT-match [eq_up_to_inv]), using
  [eq_up_to_bad_adversary_link] + [Pr_bound] in place of
  [eq_up_to_inv_adversary_link] + [Pr_eq_empty]. *)
Lemma eq_upto_bad_perf_ind :
  ∀ {L₀ L₁ LA E} (p₀ p₁ : raw_package) (I : precond) (bad_id : nat) (A : raw_package)
    `{ValidPackage L₀ Game_import E p₀}
    `{ValidPackage L₁ Game_import E p₁}
    `{ValidPackage LA E A_export A},
    INV LA I →
    I (empty_heap, empty_heap) →
    fseparate LA L₀ →
    fseparate LA L₁ →
    lossless_valid_adv LA E (resolve A RUN tt) →
    bad_id \notin domm LA →
    (∀ s₀ s₁, I (s₀, s₁) → get_heap s₀ (bad_loc bad_id) = get_heap s₁ (bad_loc bad_id)) →
    eq_up_to_bad E I bad_id p₀ p₁ →
    bad_preserved E bad_id p₀ →
    bad_preserved E bad_id p₁ →
    AdvantageE p₀ p₁ A <= Pr_bad (A ∘ p₀) bad_id true.
Proof.
  intros L₀ L₁ LA E p₀ p₁ I bad_id A vp₀ vp₁ vA hI hIe hd₀ hd₁ Hlva Hfresh Hsync hp hbp0 hbp1.
  unfold AdvantageE, Pr, Pr_bad.
  pose r := resolve A RUN tt.
  unshelve epose proof (eq_up_to_bad_adversary_link p₀ p₁ I bad_id r hI Hlva Hfresh Hsync hp hbp0 hbp1) as h.
  1:{
    eapply valid_resolve.
    - eauto.
    - apply RUN_in_A_export.
  }
  unfold Pr_op.
  unshelve epose (rhs := thetaFstd _ (repr (code_link r p₀)) empty_heap).
  simpl in rhs.
  epose (lhs := Pr_op (A ∘ p₀) RUN tt empty_heap).
  assert (lhs = rhs) as he.
  { subst lhs rhs.
    unfold Pr_op. unfold Pr_code.
    unfold thetaFstd. simpl. apply f_equal2. 2: reflexivity.
    apply f_equal. apply f_equal.
    by rewrite resolve_link.
  }
  unfold lhs in he. unfold Pr_op in he.
  rewrite he.
  unshelve epose (rhs' := thetaFstd _ (repr (code_link r p₁)) empty_heap).
  simpl in rhs'.
  epose (lhs' := Pr_op (A ∘ p₁) RUN tt empty_heap).
  assert (lhs' = rhs') as e'.
  { subst lhs' rhs'.
    unfold Pr_op. unfold Pr_code.
    unfold thetaFstd. simpl. apply f_equal2. 2: reflexivity.
    apply f_equal. apply f_equal.
    by rewrite resolve_link.
  }
  unfold lhs' in e'. unfold Pr_op in e'.
  rewrite e'.
  unfold rhs', rhs.
  unfold SDistr_bind. unfold SDistr_unit.
  rewrite !dletE.
  assert (
    ∀ y,
      (λ x : prod_choiceType (tgt RUN) heap, (y x) * (let '(b, _) := x in dunit (R:=R) (T:=tgt RUN) b) true) =
      (λ x : prod_choiceType (tgt RUN) heap, (x.1 == true)%:R * (y x))
  ) as Hrew.
  { intros y. extensionality x.
    destruct x as [x1 x2].
    rewrite dunit1E.
    simpl. rewrite GRing.mulrC. reflexivity.
  }
  rewrite !Hrew.
  assert (
    ∀ y : prod_choiceType (tgt RUN) heap -> R,
      (λ x : prod_choiceType (tgt RUN) heap, (y x) * (let '(_, s) := x in dunit (R:=R) (T:=bad_loc bad_id) (get_heap s (bad_loc bad_id))) true) =
      (λ x : prod_choiceType (tgt RUN) heap, (get_heap x.2 (bad_loc bad_id) == true)%:R * (y x))
  ) as Hrew2.
  { intros y. extensionality x.
    destruct x as [x1 x2].
    rewrite dunit1E.
    simpl. rewrite GRing.mulrC. reflexivity.
  }
  rewrite Hrew2.
  pose (event := fun x : prod_choiceType (tgt RUN) heap => x.1 == true).
  pose (bad := fun x : prod_choiceType (tgt RUN) heap => get_heap x.2 (bad_loc bad_id) == true).
  pose proof (@Pr_bound (tgt RUN) heap event bad I
                (fun '(b₀,s₀) '(b₁,s₁) => get_heap s₀ (bad_loc bad_id) = false → I (s₀,s₁) ∧ b₀ = b₁)
                (repr (code_link r p₀)) (repr (code_link r p₁)) h empty_heap empty_heap hIe) as Hb.
  have Hag : (∀ x y : tgt RUN * heap,
     (λ '(b₀, s₀) '(b₁, s₁),
        get_heap s₀ (bad_loc bad_id) = false → I (s₀, s₁) ∧ b₀ = b₁)
       x y
     → bad x = false → event x = event y).
  { move=> [b0 s0] [b1 s1] Himp /= /eqP Hbadx.
    have Hb0 : get_heap s0 (bad_loc bad_id) = false.
    { case: (get_heap s0 (bad_loc bad_id)) Hbadx => //. }
    have [_ Heq] := Himp Hb0.
    rewrite /event /=. congr (_ == true). exact: Heq. }
  specialize (Hb Hag).
  unfold TransformingLaxMorph.rlmm_from_lmla_obligation_1. simpl.
  unfold SubDistr.SDistr_obligation_2. simpl.
  unfold OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1.
  rewrite !SDistr_rightneutral. simpl.
  rewrite /StateTransfThetaDens.unaryStateBeta'_obligation_1.
  exact: Hb.
Qed.

(** [bad_preserved]'s concrete witness: a syntactic guarantee that a
  piece of code only ever writes [true] to [bad_loc bad_id] (never
  [false], and any other location is untouched by this constraint) --
  a purely structural, LOSSLESSNESS-FREE property (unlike
  [lossless_valid], no [LosslessOp] side condition is needed: even a
  divergent sampler can't make [bad_loc] go back to [false]). Meant to
  be combined with [lossless_valid] (pkg_lossless.v) via
  [Pr_code_lossless_bad] below to discharge a concrete package's
  [bad_preserved] obligation. *)
Inductive bad_loc_monotone (bad_id : nat) {A : choiceType} : raw_code A → Prop :=
| blm_ret : ∀ x, bad_loc_monotone bad_id (ret x)
| blm_call : ∀ o x k, (∀ v, bad_loc_monotone bad_id (k v)) → bad_loc_monotone bad_id (opr o x k)
| blm_getr : ∀ l k, (∀ v, bad_loc_monotone bad_id (k v)) → bad_loc_monotone bad_id (getr l k)
| blm_putr_bad : ∀ k,
    bad_loc_monotone bad_id k →
    bad_loc_monotone bad_id (putr (bad_loc bad_id) true k)
| blm_putr_other : ∀ l v k,
    l.1 ≠ bad_id →
    bad_loc_monotone bad_id k →
    bad_loc_monotone bad_id (putr l v k)
| blm_sampler : ∀ op k, (∀ v, bad_loc_monotone bad_id (k v)) → bad_loc_monotone bad_id (sampler op k).

Lemma Pr_code_bad_monotone {bad_id : nat} {A : choiceType} (c : raw_code A) :
  bad_loc_monotone bad_id c →
  ∀ h, get_heap h (bad_loc bad_id) = true →
    ∀ a h', (0 < Pr_code c h (a, h'))%R → get_heap h' (bad_loc bad_id) = true.
Proof.
  move=> Hm.
  induction Hm as [x | o x k IH | l k IH | k' IH | l v k Hne k' IH | op k IH];
    move=> h Hb a h' Hgt.
  - rewrite Pr_code_ret dunit1E in Hgt.
    have Heq := ge0_eq Hgt. inversion Heq. subst. exact: Hb.
  - move: Hgt. rewrite Pr_code_call dnullE => Hgt.
    by rewrite Order.POrderTheory.ltxx in Hgt.
  - move: Hgt. rewrite Pr_code_get => Hgt.
    exact: (H _ h Hb a h' Hgt).
  - move: Hgt. rewrite Pr_code_put => Hgt.
    apply: (IHIH (set_heap h (bad_loc bad_id) true)).
    + exact: get_set_heap_eq.
    + exact: Hgt.
  - move: Hgt. rewrite Pr_code_put => Hgt.
    have Hkey : (bad_loc bad_id).1 != l.1.
    { apply/eqP => Heq. exact: (Hne (esym Heq)). }
    have Hb2 : get_heap (set_heap h l v) (bad_loc bad_id) = true.
    { rewrite (get_set_heap_neq h l v (bad_loc bad_id) Hkey). exact: Hb. }
    exact: (IH (set_heap h l v) Hb2 a h' Hgt).
Unshelve.
all: exact: Hkey.
  - move: Hgt. rewrite Pr_code_sample => Hgt.
    have Hin : (a, h') \in dinsupp (\dlet_(x <- op.π2) Pr_code (k x) h).
    { apply/dinsuppP.
      move=> Hz. rewrite Hz in Hgt. by rewrite Order.POrderTheory.ltxx in Hgt. }
    have [x Hx1 Hx2] := dinsupp_dlet Hin.
    have Hx2' : (0 < Pr_code (k x) h (a, h'))%R.
    { move: Hx2 => /eqP Hne0.
      rewrite lt0r. apply/andP; split.
      - apply/negP => /eqP Heq. exact: (Hne0 Heq).
      - exact: ge0_mu. }
    exact: (H x h Hb a h' Hx2').
Qed.

(** [bad_preserved]'s ONLY nontrivial half, [bad_lossless], from a
  [lossless_valid] fact (ordinary losslessness, pkg_lossless.v) plus
  a [bad_loc_monotone] fact (this file). *)
Lemma Pr_code_lossless_bad {bad_id : nat} {A : choiceType} (L : Locations) (c : raw_code A) :
  lossless_valid L c → bad_loc_monotone bad_id c →
  ∀ h, get_heap h (bad_loc bad_id) = true → bad_lossless bad_id c h.
Proof.
  move=> Hlv Hm h Hb. split.
  - exact: (Pr_code_lossless L c Hlv h).
  - move=> a h' Hgt. exact: (Pr_code_bad_monotone c Hm h Hb a h' Hgt).
Qed.
