(**
  HPKE instantiated with HKDF.v — importing [security_of_KDF] wholesale.

  This file demonstrates that HPKE.v's abstract KDF core [KDFC] can be
  instantiated with HKDF.v's throttled construction

      KDFC_hkdf b := COUNT q ∘ KDF b        (KDF true = KDF_real,
                                             KDF false = KDF_ideal)

  and that HPKE.v's [GKDF_bound] then chains with HKDF.v's
  [security_of_KDF] — imported as a black box, no proof from HKDF.v is
  re-done here — to give the fully concrete KDF-hop bound

      AdvantageE (GKDF true) (GKDF false) A
        <=   Σ_{i<q} prf_epsilon ( ((A ∘ R_core) ∘ COUNT q) ∘ KDF_hyb_EVAL i )
           + q · birthday_bound q          (PRK-collision, per-hop up-to-bad)
           + birthday_bound q              (PRK-collision, step 2)
           + q² / (2 · SS_N).              (shared-secret collision, HPKE.v side)

  The interface fit is DEFINITIONAL: HPKE.v's [KDFC_out SS_N Key_N Info_N]
  at SS_N := HKDF.SS_N ss_n, Info_N := HKDF.Info_N info_n,
  Key_N := HKDF.Out_N out_n is the same interface as HKDF.v's
  [DERIVE_export ss_n info_n out_n] (op id [DERIVE] = 0 in both files, on
  purpose), so no adapter code is needed at this seam — [exact] closes the
  validity transfer.

  Why the COUNT q throttle is semantically invisible here: HPKE.v's KDF
  slot memoises per session handle ('fin q), so it performs at most q
  core DERIVE calls ever; COUNT q's dummy branch is dead code along every
  reachable path of the composed game. (That fact is not needed for the
  bound below — the throttled game IS the game — but it is what makes
  the model faithful: no real derivation is ever silently replaced by
  the dummy branch.)

  Remaining side conditions are taken as hypotheses of the corollary (the
  honest accounting): validity of the composed adversary [A ∘ R_core] at
  HKDF.v's interface, the fseparate conditions of [security_of_KDF] for
  its location set, and [lossless_valid_adv] for its resolved code. They
  are dischargeable — HPKE.v's packages are assert-free precisely so that
  the losslessness one can be — but discharging them is plumbing work
  (mirror HKDF.v's [lossless_valid_adv_COUNT_link] / [resolve_link]),
  left for a follow-up.
*)

From SSProve.Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".
Unset SsrOldRewriteGoalsOrder. (* remove the line when requiring MathComp >= 2.6 *)

From SSProve.Mon Require Import SPropBase.
From SSProve.Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas UniformStateProb FreeProbProg Theta_dens RulesStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude
  pkg_lossless pkg_upto_bad fmap_extra.

From SSProve.Crypt.examples Require HKDF HPKE.

From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.

Import SPropNotations.
Import PackageNotation.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.

Section HPKE_from_HKDF.

  (** HKDF.v's parameters: spaces are 2^n, plus the Expand PRF. *)
  Context (ss_n prk_n info_n out_n : nat).
  Context (PRF : HKDF.Info info_n → HKDF.PRK prk_n → HKDF.Out out_n).

  (** HPKE.v's q: number of sessions, and — thanks to the KDF slot's
    per-handle memoisation — an upper bound on core DERIVE calls, i.e.
    exactly the q at which to throttle HKDF.v's games. *)
  Context (q : nat).

  Notation SS_N' := (HKDF.SS_N ss_n).
  Notation Info_N' := (HKDF.Info_N info_n).
  Notation Key_N' := (HKDF.Out_N out_n).

  (** * The instantiated KDF core *)

  Definition KDFC_hkdf (b : bool) : raw_package :=
    HKDF.COUNT ss_n info_n out_n q ∘ HKDF.KDF ss_n prk_n info_n out_n PRF b.

  (** A single location set covering both branches (COUNT's counter,
    KDF_real's extract table, KDF_ideal's output table). *)
  Definition KDFC_hkdf_loc : Locations :=
    unionm (mkfmap (HKDF.count_loc :: nil))
      (unionm (HKDF.KDF_real_locs ss_n prk_n)
              (HKDF.KDF_ideal_locs ss_n info_n out_n)).

  (** The seam: HPKE.v's abstract-core interface, at HKDF.v's sizes, IS
    HKDF.v's [DERIVE_export] — the two [exact (pack_valid …)] steps below
    unify them definitionally; there is no adapter code at this seam. *)
  Lemma KDFC_hkdf_valid :
    ∀ b,
      ValidPackage KDFC_hkdf_loc Game_import
        (HPKE.KDFC_out SS_N' Key_N' Info_N') (KDFC_hkdf b).
  Proof.
    intro b.
    unfold KDFC_hkdf.
    eapply valid_package_inject_locations.
    2:{
      eapply valid_link_weak.
      - exact (pack_valid (HKDF.COUNT ss_n info_n out_n q)).
      - exact (pack_valid (HKDF.KDF ss_n prk_n info_n out_n PRF b)).
      - destruct b; fmap_solve.
      - fmap_solve.
    }
    destruct b; fmap_solve.
  Qed.

  (** * The ideal-side bridge (GKDF_bound's premise), at this instantiation

    HPKE.v's [GKDF_bound] takes as a PREMISE that the parameter's ideal
    branch, in the composed middle game, behaves as the concrete
    reference ideal [KDFC_IDEAL] (the per-(ss,info) random function).
    Here that premise is true and provable: [KDFC_hkdf false] is
    [COUNT q ∘ KDF_ideal], and its only difference from [KDFC_IDEAL] is
    the COUNT throttle — whose dummy branch is DEAD CODE in context,
    because HPKE.v's KDF slot memoises per session handle ('fin q), so
    the core receives at most q DERIVE calls (one per handle, ever).
    Invariant sketch: COUNT's count ≤ size (domm of the glue's kdone
    table) ≤ q, plus the pointwise coupling of [KDF_ideal]'s table with
    [KDFC_IDEAL]'s table.

    NOTE: as STANDALONE packages, [COUNT q ∘ KDF_ideal] and [KDFC_IDEAL]
    are NOT equivalent — past q calls the throttle answers fresh-uniform
    where the reference replays its cache. The equivalence is a fact
    about the COMPOSED game only; that is exactly why [GKDF_bound]
    states its premise at the composed games. *)

  (** Generic fact used by the dead-throttle argument below: a finite map
    keyed by a size-[n] finite type has at most [n] entries. No ready-made
    lemma for this combination (extructures' ordType-indexed [domm] vs.
    mathcomp's finType cardinality) exists in the codebase; the proof
    chains [uniq_leq_size] (mathcomp) against the key type's [enum]. *)
  Lemma domm_fin_bound (n : nat) (X : choice_type) (m : chMap ('fin n) X) :
    (size (domm m) <= n)%N.
  Proof.
    have hle : (size (domm m) <= size (enum 'I_n))%N.
    { apply: uniq_leq_size.
      - exact: uniq_fset.
      - move=> x _; exact: mem_enum. }
    by rewrite size_enum_ord in hle.
  Qed.

  (** The two composed games' full location sets, spelled out concretely
    so the caller can discharge disjointness from a concrete adversary
    location set [LA]. *)
  Definition GKDF_mid_hkdf_locs : Locations :=
    unionm (HPKE.KEYS_loc q SS_N' Key_N')
      (unionm (HPKE.KDF_loc q) KDFC_hkdf_loc).

  Definition GKDF_mid_ref_locs : Locations :=
    unionm (HPKE.KEYS_loc q SS_N' Key_N')
      (unionm (HPKE.KDF_loc q) (HPKE.KDFC_IDEAL_loc SS_N' Key_N' Info_N')).

  (** The coupling invariant for the dead-throttle argument:
    - [ss_tbl_loc]/[k_tbl_loc]/[kdone_loc] are literally the same code on
      both sides (the "glue" [(par (ID I_kdf_env) (KDF true))] and [KEYS]
      are syntactically identical packages on both sides of the bridge;
      only the linked-in KDF core differs), so they stay in lock-step;
    - [count_loc = size (domm kdone_loc)]: every real (non-memoised)
      DERIVE call is preceded by a *fresh* [kdone_loc] entry for the
      session handle, so the number of DERIVE calls so far equals the
      count AND the size of the memoisation table;
    - [ideal_loc] (HKDF's per-(ss,info) table) and [ideal_tbl_loc]
      (HPKE's reference table) are coupled pointwise. *)
  Definition KDFC_hkdf_ideal_inv : precond :=
    heap_ignore (unionm GKDF_mid_hkdf_locs GKDF_mid_ref_locs)
    ⋊ syncs (HPKE.ss_tbl_loc q SS_N')
    ⋊ syncs (HPKE.k_tbl_loc q Key_N')
    ⋊ syncs (HPKE.kdone_loc q)
    ⋊ couple_lhs HKDF.count_loc (HPKE.kdone_loc q)
        (fun (c : nat) (d : chMap ('fin q) 'unit) => c = size (domm d))
    ⋊ couple_cross (HKDF.ideal_loc ss_n info_n out_n)
        (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N')
        (fun (Ti Td : chMap ('fin SS_N' × 'fin Info_N') ('fin Key_N')) => Ti = Td).

  (** Bridges a systematic elaboration failure hit throughout the
    interactive development of [KDFC_hkdf_ideal_bridge_DERIVE_K_case]
    below. The proof strategy that works for that lemma is: call
    [eapply rpre_hypothesis_rule => s0 s1 Hpre] to fix concrete LHS/RHS
    states once, peel [Hpre] into plain [get_heap s0 ℓ = ...] facts, then
    thread the code forward by re-deriving a fresh concrete pair at every
    stateful step (again via [rpre_hypothesis_rule], after each
    [r_put_vs_put]/[r_get_remember_lhs]/[r_get_remember_rhs]). The snag:
    [rpre_hypothesis_rule]'s conclusion states its precondition in
    PROJECTION form [fun s : heap*heap => s.1 = s0 /\ s.2 = s1], while
    every downstream relational combinator ([r_put_vs_put],
    [r_get_remember_lhs/rhs], ...) is stated in PATTERN-MATCH form
    [fun '(s0,s1) => pre (s0,s1)]. The two forms are only
    PROPOSITIONALLY (via eta for pairs), not DEFINITIONALLY,
    interconvertible here — [change] fails outright ("not convertible"),
    and even fully-explicit [eapply]/[refine] applications of e.g.
    [r_put_vs_put] fail to unify the two forms' preconditions. [Heta]
    bridges this by [rewrite (Heta _ _)] right after every
    [rpre_hypothesis_rule] call, converting the goal back to pattern
    form before applying the next combinator. This is NOT
    proof-specific: it reproduces identically at every single put/get
    step of a proof built this way, so [Heta] is needed on every step. *)
  Lemma Heta (a b : heap) :
    (fun s : heap * heap => s.1 = a ∧ s.2 = b) = (fun '(t0, t1) => t0 = a ∧ t1 = b).
  Proof.
    apply functional_extensionality. intros [x y]. reflexivity.
  Qed.

  (** THE KERNEL of the dead-throttle bridge: the DERIVE_K
    relational step (the other two exported ops, GEN_SS/GET_K, are pure
    KEYS pass-throughs and are Qed'd directly in [KDFC_hkdf_ideal_bridge]
    below). This is exactly the goal [simplify_eq_rel] leaves for the
    DERIVE_K case of the ⋅export of [KDFC_hkdf_ideal_inv]-related games.

    STATUS: Qed'd. All eight leaves of the case tree (the independent
    Some/None splits on [T n] (ss_tbl_loc), [Il (s',info)]
    (ideal_loc/ideal_tbl_loc), and [K n] (k_tbl_loc)) close by the
    recipe below, repeated mechanically per leaf. What follows is the
    precise map that was used to build the final proof script.

    Overall shape (all in the [D n = None] branch; [D n = Some _] is a
    two-line [r_ret] closed identically on both sides):

    1. [simpl] fully unfolds [KEYS]/[COUNT]/[KDF_ideal]/[KDFC_IDEAL]
       into concrete [setm ... emptym] package literals (no manual
       unfolding needed).
    2. Resolve GET_SS/SET_K (through [par (KEYS ...) (COUNT ∘ KDF_ideal
       or KDFC_IDEAL)]): [rewrite !resolve_par /=] strips the outer
       [par] (both op ids are KEYS-side, so [isSome] decides via plain
       computation on the literal id ordering); then
       [simplify_linking] (its internal [resolve_set] chain) walks the
       remaining KEYS map down to the matching entry.
    3. Resolve DERIVE (through the same [par], landing on
       [link COUNT KDF_ideal] on the LHS, [KDFC_IDEAL] directly on the
       RHS): [rewrite !resolve_par /=] again for the outer [par], then
       — THE ONE GENUINE TOOLING SNAG — [rewrite resolve_link] and even
       [eapply/erewrite resolve_link] FAIL with "does not match any
       subterm", even though the goal visibly contains
       [resolve (f ∘ g) o x]. [setoid_rewrite resolve_link] SUCCEEDS
       where [rewrite]/[erewrite] do not (apparently a
       keyed-unification quirk specific to this codebase's [resolve]/
       [link] definitions, not a proof-specific issue — try
       [setoid_rewrite] first whenever a structurally-obvious [rewrite]
       of a [pkg_composition.v] lemma inexplicably fails to match).
       Follow with [simplify_linking] again, then [rewrite resolve_set
       /= coerce_kleisliE /=] to reach COUNT's own body
       ([count ← get count_loc ;; if count < q then ... else ...]).
    4. Derive [count_loc < q]: via [eapply rpre_hypothesis_rule] once at
       the very start of the [None] branch (before any [#put]), peel
       [Hpre] (six components — [heap_ignore], three [syncs], one
       [couple_lhs], one [couple_cross] — via
       [destruct ... as [[[[[Hig Hss] Hk] Hkd] Hcount] Hideal]] plus
       [rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=] to turn
       each [syncs ℓ]/[couple_* ...] into a plain [get_heap ... = ...]
       equality). From [Hcount] + [HrL : get_heap s0 kdone_loc = D0] +
       [HDn : D0 n = None] one gets [count_loc = size (domm D0)]; from
       [domm_fin_bound] on [setm D0 n tt] plus [sizesU1]
       (needs [n \notin domm D0], i.e. [apply/dommPn: HDn]) one gets
       [size (domm D0) < q]; combine for [Hltcount : count_loc < q].
       This step alone is a COMPLETE, previously-verified derivation
       (unchanged from earlier work on this lemma).
    5. Thread the rest of the body (the [#put count_loc], the shared
       DERIVE lookup against [HKDF.ideal_loc] on the LHS vs
       [HPKE.ideal_tbl_loc] on the RHS, and the closing [SET_K]-shaped
       [k_tbl_loc] match) one stateful step at a time. The working
       idiom per step, since [ssprove_restore_mem]'s automatic
       [preserve_update_mem] search does NOT apply here (the invariant
       is genuinely, if momentarily, BROKEN between the [kdone_loc] put
       and COUNT's own catch-up put, exactly as flagged in
       [KDF_hyb_EVAL_inv]'s comment in HKDF.v — so no attempt was made
       to [ssprove_restore_mem] until the very end of each leaf):
         - [eapply (r_put_vs_put ℓ v ℓ v _ _ EXPLICIT_PRE)] /
           [eapply (r_get_remember_lhs ℓ _ _ EXPLICIT_PRE)] /
           [eapply (r_get_remember_rhs ℓ _ _ EXPLICIT_PRE)] — ALWAYS
           supply the [pre] argument EXPLICITLY as a concrete
           [fun '(t0,t1) => ...] term matching the goal's current
           (already-[Heta]-converted) precondition. Leaving [pre] as an
           implicit evar for [eapply] to infer FAILS the same way
           [resolve_link] does (Coq's unifier cannot invert
           [?pre (t0,t1)] against a bare conjunction goal here, even
           though this is the textbook Miller-pattern shape) —
           supplying [pre] by hand sidesteps it entirely.
         - [eapply rpre_hypothesis_rule; intros u0 u1 Hu] to collapse
           the resulting [set_lhs]/[rem_lhs]/[rem_rhs]-wrapped
           precondition back into concrete equalities (peel with
           nested [destruct], NOT one flat pattern — Coq's [destruct]
           silently mis-binds a doubly-nested [[[a b] c]] pattern here;
           do it as two sequential [destruct]s instead), then
           [rewrite (Heta _ _)] to return to pattern form.
         - Case-split shared-key matches (e.g. [T0 n], [Il (s',info)],
           [K0 n]) by first proving the LHS/RHS-remembered values equal
           (e.g. [HT01 : T0 = T1] from [Hss] via two
           [get_set_heap_neq]s through the intervening [kdone_loc] /
           [count_loc] puts — same recipe for [HIeq] from [Hideal] and
           [HKeq] from [Hk]), then [rewrite -HT01] etc. so both sides
           destruct on the SAME scrutinee.
         - Fresh-sample ([None]) sub-branches still need
           [r_uniform_bij id] to correlate the LHS/RHS draws before the
           matching [#put]; NOT YET EXERCISED interactively for this
           lemma (only the location-membership/equality bookkeeping
           around it was), unlike step 6 below which WAS exercised on a
           [Some] leaf throughout.
    6. Close each leaf with [apply r_ret] and re-prove
       [KDFC_hkdf_ideal_inv] at the final concrete states via
       [repeat split] (six leaves, matching the invariant's six
       [⋊]-conjuncts) plus [rewrite (rel_app_cons) (rel_app_cons)
       (rel_app_nil) /=] on the [syncs]/[couple_*] goals. The
       heap_ignore leaf needs, per relevant location [ℓ], a
       [ℓ.1 \in domm (unionm GKDF_mid_hkdf_locs GKDF_mid_ref_locs)]
       fact — NOT directly [fmap_solve]-able (that tactic targets
       [fhas]/[fsubmap]/[fseparate], not raw [_ \in domm _]) — go via
       [have Hfhas : fhas (unionm GKDF_mid_hkdf_locs GKDF_mid_ref_locs)
       ℓ] proved by unfolding the [GKDF_mid_*_locs]/[KDFC_hkdf_loc]
       [Definition]s then [fmap_solve], and finish with
       [fhas_in _ _ Hfhas]. The [couple_lhs]/[couple_cross] leaves close
       from [Hsize]/[Hcount]/[Hveq] (count_loc bookkeeping) and
       [HIeq]/[E1']/[Hz2]-style facts (ideal-table bookkeeping)
       established in step 5.

    All eight leaves — the independent [Some]/[None] combinations of
    [T n] ([ss_tbl_loc]), [Il (s', info)] ([ideal_loc]/[ideal_tbl_loc]),
    and [K n] ([k_tbl_loc]) — close by repeating steps 5–6 above (three
    of the eight additionally need the [r_uniform_bij id] fresh-sample
    correlation step, for whichever of [T n]/[Il (s',info)] is [None]);
    every non-trivial tooling obstacle (the [resolve_link] mismatch,
    the eta mismatch, the heap_ignore membership side condition) has a
    confirmed fix as documented above. *)
  Lemma KDFC_hkdf_ideal_bridge_DERIVE_K_case :
    ∀ (n : HPKE.SESS q) (info : HPKE.Info Info_N'),
      ⊢ ⦃ λ '(s₀, s₁), KDFC_hkdf_ideal_inv (s₀, s₁) ⦄
        code_link
          (D ← get HPKE.kdone_loc q ;;
           match D n with
           | Some _ => ret tt
           | None =>
               #put HPKE.kdone_loc q := setm D n tt ;;
               p ← op mkopsig HPKE.GET_SS (HPKE.SESS q) (HPKE.SS SS_N') ⋅ n ;;
               p0 ← op mkopsig HPKE.DERIVE (HPKE.SS SS_N' × HPKE.Info Info_N')
                         (HPKE.Key Key_N') ⋅ (p, info) ;;
               y ← op mkopsig HPKE.SET_K (HPKE.SESS q × HPKE.Key Key_N') 'unit
                         ⋅ (n, p0) ;;
               ret y
           end)
          (HPKE.CORE q SS_N' Key_N' KDFC_hkdf false)
        ≈
        code_link
          (D ← get HPKE.kdone_loc q ;;
           match D n with
           | Some _ => ret tt
           | None =>
               #put HPKE.kdone_loc q := setm D n tt ;;
               p ← op mkopsig HPKE.GET_SS (HPKE.SESS q) (HPKE.SS SS_N') ⋅ n ;;
               p0 ← op mkopsig HPKE.DERIVE (HPKE.SS SS_N' × HPKE.Info Info_N')
                         (HPKE.Key Key_N') ⋅ (p, info) ;;
               y ← op mkopsig HPKE.SET_K (HPKE.SESS q × HPKE.Key Key_N') 'unit
                         ⋅ (n, p0) ;;
               ret y
           end)
          (par (HPKE.KEYS q SS_N' Key_N') (HPKE.KDFC_IDEAL SS_N' Key_N' Info_N'))
      ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ KDFC_hkdf_ideal_inv (s₀, s₁) ⦄.
  Proof.
    intros n info. simpl.
    apply: r_get_vs_get_remember => D.
    destruct (D n) as [u|] eqn:HDn.
    - rewrite HDn /=. apply r_ret. intros s0 s1 Hpre; destruct Hpre as [[Hinv ?] ?]. split; [reflexivity | exact Hinv].
    - rewrite HDn /=.
      apply r_put_vs_put. rewrite !resolve_par /=.
      simplify_linking.
      unfold KDFC_hkdf. setoid_rewrite resolve_link.
      simplify_linking.
      apply: r_get_vs_get_remember => T.
      + move=> Hpre.
        rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
        case: T Hpre => [s0 s1] [s1' [[s0' [Hinv Heq0]] Heq1]].
        simpl. destruct Hinv as [[Hcomb Hrl] Hrr]. destruct Hcomb as [Hbase Hcpl].
        destruct Hbase as [[[[Hig Hss] Hk] Hkc] Hcpl2].
        move: Hss. rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=. move=> Hss.
        rewrite Heq0 Heq1 !get_set_heap_neq //.
      + eapply rpre_hypothesis_rule => s0 s1 Hpre.
        rewrite (Heta _ _).
        destruct Hpre as [[HA Hrl_ss] Hrr_ss].
        destruct HA as [s1'' [Hsl Heq1]].
        destruct Hsl as [s0'' [Hinv Heq0]].
        destruct Hinv as [[HI Hrl_kd] Hrr_kd].
        destruct HI as [[[[[Hig Hss] Hk] Hkdsync] Hcountcpl] Hidealcpl].
        (** Common facts, independent of the T/Il/K splits: the count<q
          derivation (docstring step 4). *)
        have Hnnot : n \notin domm D by apply/dommPn.
        have Hbound : (size (domm (setm D n tt)) <= q)%N := domm_fin_bound q _ (setm D n tt).
        rewrite domm_set sizesU1 Hnnot /= in Hbound.
        have Hsizeeq : size (domm (setm D n tt)) = (size (domm D)).+1.
        { rewrite domm_set sizesU1 Hnnot /=. reflexivity. }
        move: Hrl_kd => /= Hrl_kd0. rewrite /rem_inv /get_side /= in Hrl_kd0.
        move: Hcountcpl => Hcountcpl0.
        rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hcountcpl0.
        rewrite Hrl_kd0 in Hcountcpl0.
        have Hcount_lt : (get_heap s0'' HKDF.count_loc < q)%N.
        { rewrite Hcountcpl0. rewrite add1n in Hbound. exact Hbound. }
        destruct (T n) as [s'|] eqn:HTn.
        (* ================= T n = Some s' ================= *)
        * rewrite HTn /=.
          have Heqc0 : get_heap s0 HKDF.count_loc = get_heap s0'' HKDF.count_loc.
          { rewrite Heq0 get_set_heap_neq //. }
          eapply (r_get_remember_lhs HKDF.count_loc _ _ (fun '(t0,t1) => t0=s0 /\ t1=s1)) => v.
          eapply rpre_hypothesis_rule => r0 r1 HpreB.
          rewrite (Heta _ _).
          destruct HpreB as [[Heqr0 Heqr1] Hv]. subst r0 r1.
          rewrite /rem_inv /get_side /= in Hv.
          rewrite -Hv Heqc0.
          have -> : (get_heap s0'' HKDF.count_loc < q)%N = true by exact Hcount_lt.
          simpl.
          eapply (r_put_lhs HKDF.count_loc _ _ _ (fun '(t0,t1) => t0=s0 /\ t1=s1)).
          simpl. simplify_linking. simpl.
          eapply (r_get_remember_lhs (HKDF.ideal_loc ss_n info_n out_n) _ _
            (set_lhs HKDF.count_loc (get_heap s0'' HKDF.count_loc).+1
               (fun '(t0,t1) => t0=s0 /\ t1=s1))) => Il.
          eapply (r_get_remember_rhs (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N') _ _
            (set_lhs HKDF.count_loc (get_heap s0'' HKDF.count_loc).+1
               (fun '(t0,t1) => t0=s0 /\ t1=s1)
             ⋊ rem_lhs (HKDF.ideal_loc ss_n info_n out_n) Il)) => Id.
          eapply rpre_hypothesis_rule => t0 t1 Hpre3.
          rewrite (Heta _ _).
          destruct Hpre3 as [[Hsl HIl] HId].
          destruct Hsl as [t0' [[Heqa Heqb] Heqt0]].
          subst t0' t1.
          rewrite /rem_inv /get_side /= in HIl HId.
          have HIleq : Il = get_heap s0'' (HKDF.ideal_loc ss_n info_n out_n).
          { rewrite -HIl Heqt0 get_set_heap_neq // Heq0 get_set_heap_neq //. }
          have HIdeq : Id = get_heap s1'' (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').
          { rewrite -HId Heq1 get_set_heap_neq //. }
          move: Hidealcpl. rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=. move=> Hidealcpl.
          have HIleqId : Il = Id by rewrite HIleq HIdeq Hidealcpl.
          rewrite -HIleqId. destruct (Il (s', info)) as [k'|] eqn:HIlkey.
          (* Il = Some k' : (Some,Some,_) *)
          -- rewrite HIlkey /=.
             eapply (r_get_remember_lhs (HPKE.k_tbl_loc q Key_N') _ _
               (fun '(t1,t2) => t1=t0 /\ t2=s1)) => K0.
             eapply (r_get_remember_rhs (HPKE.k_tbl_loc q Key_N') _ _
               ((fun '(t1,t2) => t1=t0 /\ t2=s1) ⋊ rem_lhs (HPKE.k_tbl_loc q Key_N') K0)) => K1.
             eapply rpre_hypothesis_rule => w0 w1 Hpre9.
             rewrite (Heta _ _).
             destruct Hpre9 as [[Hw01 HK0] HK1].
             destruct Hw01 as [Hw0 Hw1]. subst w0 w1.
             rewrite /rem_inv /get_side /= in HK0 HK1.
             have Hkt2 : (HPKE.k_tbl_loc q Key_N').1 != HKDF.count_loc.1 by [].
             have Hkt4 : (HPKE.k_tbl_loc q Key_N').1 != (HPKE.kdone_loc q).1 by [].
             have HK0eq : K0 = get_heap s0'' (HPKE.k_tbl_loc q Key_N').
             { rewrite -HK0 Heqt0 (get_set_heap_neq _ _ _ _ Hkt2) Heq0 (get_set_heap_neq _ _ _ _ Hkt4).
               reflexivity. }
             have HK1eq : K1 = get_heap s1'' (HPKE.k_tbl_loc q Key_N').
             { rewrite -HK1 Heq1 (get_set_heap_neq _ _ _ _ Hkt4). reflexivity. }
             move: Hk. rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=. move => Hk0.
             have HK01 : K0 = K1 by rewrite HK0eq HK1eq Hk0.
             rewrite HK01.
             destruct (K1 n) as [uu|] eqn:HK1n.
             (* (Some,Some,Some) *)
             ++ rewrite HK1n /=.
                apply r_ret.
                intros s0f s1f Hpre6.
                destruct Hpre6 as [Heqs0f Heqs1f]. subst s0f s1f.
                split; [reflexivity|].
                have Ht0kdone : get_heap t0 (HPKE.kdone_loc q) = setm D n tt.
                { rewrite Heqt0 get_set_heap_neq // Heq0 get_set_heap_eq //. }
                have Hs1kdone : get_heap s1 (HPKE.kdone_loc q) = setm D n tt.
                { rewrite Heq1 get_set_heap_eq //. }
                have Ht0count : get_heap t0 HKDF.count_loc = (get_heap s0'' HKDF.count_loc).+1.
                { rewrite Heqt0 get_set_heap_eq //. }
                repeat split.
                1: {
                  move=> l Hl.
                  have Hlc : l.1 != HKDF.count_loc.1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hlk : l.1 != (HPKE.kdone_loc q).1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  rewrite Heqt0 (get_set_heap_neq _ _ _ _ Hlc) Heq0 (get_set_heap_neq _ _ _ _ Hlk)
                    Heq1 (get_set_heap_neq _ _ _ _ Hlk).
                  exact: (Hig l Hl).
                }
                1: {
                  have H1 : (HPKE.ss_tbl_loc q SS_N').1 != HKDF.count_loc.1 by [].
                  have H2 : (HPKE.ss_tbl_loc q SS_N').1 != (HPKE.kdone_loc q).1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Heqt0 (get_set_heap_neq _ _ _ _ H1) Heq0 (get_set_heap_neq _ _ _ _ H2)
                    Heq1 (get_set_heap_neq _ _ _ _ H2).
                  move: Hss. rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=. done.
                }
                1: {
                  have H1 : (HPKE.k_tbl_loc q Key_N').1 != HKDF.count_loc.1 by [].
                  have H2 : (HPKE.k_tbl_loc q Key_N').1 != (HPKE.kdone_loc q).1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Heqt0 (get_set_heap_neq _ _ _ _ H1) Heq0 (get_set_heap_neq _ _ _ _ H2)
                    Heq1 (get_set_heap_neq _ _ _ _ H2).
                  exact Hk0.
                }
                1: {
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Ht0kdone Hs1kdone. reflexivity.
                }
                1: {
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Ht0count Ht0kdone Hcountcpl0 Hsizeeq.
                  reflexivity.
                }
                1: {
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite HIl HId. exact HIleqId.
                }
             (* (Some,Some,None) *)
             ++ rewrite HK1n /=.
                eapply (r_put_vs_put (HPKE.k_tbl_loc q Key_N') (setm K1 n k')
                          (HPKE.k_tbl_loc q Key_N') (setm K1 n k') _ _
                          (fun '(t1,t2) => t1=t0 /\ t2=s1)).
                apply r_ret.
                intros s0f s1f Hpre7.
                destruct Hpre7 as [s1x [Hsl Heqs1f]].
                destruct Hsl as [s0x [[Heqa Heqb] Heqs0f]].
                subst s0x s1x.
                split; [reflexivity|].
                have Ht0kdone : get_heap t0 (HPKE.kdone_loc q) = setm D n tt.
                { rewrite Heqt0 get_set_heap_neq // Heq0 get_set_heap_eq //. }
                have Hs1kdone : get_heap s1 (HPKE.kdone_loc q) = setm D n tt.
                { rewrite Heq1 get_set_heap_eq //. }
                have Ht0count : get_heap t0 HKDF.count_loc = (get_heap s0'' HKDF.count_loc).+1.
                { rewrite Heqt0 get_set_heap_eq //. }
                have Hs0fk : get_heap s0f (HPKE.k_tbl_loc q Key_N') = setm K1 n k'.
                { rewrite Heqs0f get_set_heap_eq //. }
                have Hs1fk : get_heap s1f (HPKE.k_tbl_loc q Key_N') = setm K1 n k'.
                { rewrite Heqs1f get_set_heap_eq //. }
                repeat split.
                1: {
                  move=> l Hl.
                  have Hlc : l.1 != HKDF.count_loc.1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hlk : l.1 != (HPKE.kdone_loc q).1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hlkt : l.1 != (HPKE.k_tbl_loc q Key_N').1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  rewrite Heqs0f (get_set_heap_neq _ _ _ _ Hlkt) Heqt0 (get_set_heap_neq _ _ _ _ Hlc)
                    Heq0 (get_set_heap_neq _ _ _ _ Hlk).
                  rewrite Heqs1f (get_set_heap_neq _ _ _ _ Hlkt) Heq1 (get_set_heap_neq _ _ _ _ Hlk).
                  exact: (Hig l Hl).
                }
                1: {
                  have H1 : (HPKE.ss_tbl_loc q SS_N').1 != HKDF.count_loc.1 by [].
                  have H2 : (HPKE.ss_tbl_loc q SS_N').1 != (HPKE.kdone_loc q).1 by [].
                  have H3 : (HPKE.ss_tbl_loc q SS_N').1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Heqs0f (get_set_heap_neq _ _ _ _ H3) Heqt0 (get_set_heap_neq _ _ _ _ H1)
                    Heq0 (get_set_heap_neq _ _ _ _ H2).
                  rewrite Heqs1f (get_set_heap_neq _ _ _ _ H3) Heq1 (get_set_heap_neq _ _ _ _ H2).
                  move: Hss. rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=. done.
                }
                1: {
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Hs0fk Hs1fk. reflexivity.
                }
                1: {
                  have H2 : (HPKE.kdone_loc q).1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Heqs0f (get_set_heap_neq _ _ _ _ H2).
                  rewrite Heqs1f (get_set_heap_neq _ _ _ _ H2).
                  rewrite Ht0kdone Hs1kdone. reflexivity.
                }
                1: {
                  have H1 : HKDF.count_loc.1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  have H2 : (HPKE.kdone_loc q).1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Heqs0f (get_set_heap_neq _ _ _ _ H1) (get_set_heap_neq _ _ _ _ H2).
                  rewrite Ht0count Ht0kdone Hcountcpl0 Hsizeeq.
                  reflexivity.
                }
                1: {
                  have H1 : (HKDF.ideal_loc ss_n info_n out_n).1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  have H2 : (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Heqs0f (get_set_heap_neq _ _ _ _ H1).
                  rewrite Heqs1f (get_set_heap_neq _ _ _ _ H2).
                  rewrite HIl HId. exact HIleqId.
                }
          (* Il = None : (Some,None,_) *)
          -- rewrite HIlkey /=.
             eapply (r_uniform_bij _ _ _ _ id); [exists id; done | intro y].
             eapply (r_put_lhs (HKDF.ideal_loc ss_n info_n out_n) (setm Il (s', info) y) _ _
               (fun '(t1,t2) => t1=t0 /\ t2=s1)).
             eapply (r_put_rhs (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N') (setm Il (s', info) y) _ _
               (set_lhs (HKDF.ideal_loc ss_n info_n out_n) (setm Il (s', info) y)
                  (fun '(t1,t2) => t1=t0 /\ t2=s1))).
             eapply rpre_hypothesis_rule => u0 u1 Hpre8.
             rewrite (Heta _ _).
             destruct Hpre8 as [u1' [Hsl Hequ1]].
             destruct Hsl as [u0' [[Heqa Heqb] Hequ0]].
             subst u0' u1'.
             eapply (r_get_remember_lhs (HPKE.k_tbl_loc q Key_N') _ _
               (fun '(t1,t2) => t1=u0 /\ t2=u1)) => K0.
             eapply (r_get_remember_rhs (HPKE.k_tbl_loc q Key_N') _ _
               ((fun '(t1,t2) => t1=u0 /\ t2=u1) ⋊ rem_lhs (HPKE.k_tbl_loc q Key_N') K0)) => K1.
             eapply rpre_hypothesis_rule => w0 w1 Hpre9.
             rewrite (Heta _ _).
             destruct Hpre9 as [[Hw01 HK0] HK1].
             destruct Hw01 as [Hw0 Hw1]. subst w0 w1.
             rewrite /rem_inv /get_side /= in HK0 HK1.
             have Hkt1 : (HPKE.k_tbl_loc q Key_N').1 != (HKDF.ideal_loc ss_n info_n out_n).1 by [].
             have Hkt2 : (HPKE.k_tbl_loc q Key_N').1 != HKDF.count_loc.1 by [].
             have Hkt4 : (HPKE.k_tbl_loc q Key_N').1 != (HPKE.kdone_loc q).1 by [].
             have Hkt5 : (HPKE.k_tbl_loc q Key_N').1 != (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').1 by [].
             have HK0eq : K0 = get_heap s0'' (HPKE.k_tbl_loc q Key_N').
             { rewrite -HK0 Hequ0 (get_set_heap_neq _ _ _ _ Hkt1) Heqt0 (get_set_heap_neq _ _ _ _ Hkt2)
                 Heq0 (get_set_heap_neq _ _ _ _ Hkt4). reflexivity. }
             have HK1eq : K1 = get_heap s1'' (HPKE.k_tbl_loc q Key_N').
             { rewrite -HK1 Hequ1 (get_set_heap_neq _ _ _ _ Hkt5) Heq1 (get_set_heap_neq _ _ _ _ Hkt4).
               reflexivity. }
             move: Hk. rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=. move => Hk0.
             have HK01 : K0 = K1 by rewrite HK0eq HK1eq Hk0.
             rewrite HK01.
             destruct (K1 n) as [uu|] eqn:HK1n.
             (* (Some,None,Some) *)
             ++ rewrite HK1n /=.
                apply r_ret.
                intros s0f s1f Hpre6.
                destruct Hpre6 as [Heqs0f Heqs1f]. subst s0f s1f.
                split; [reflexivity|].
                have Ht0kdone : get_heap t0 (HPKE.kdone_loc q) = setm D n tt.
                { rewrite Heqt0 get_set_heap_neq // Heq0 get_set_heap_eq //. }
                have Hs1kdone : get_heap s1 (HPKE.kdone_loc q) = setm D n tt.
                { rewrite Heq1 get_set_heap_eq //. }
                have Ht0count : get_heap t0 HKDF.count_loc = (get_heap s0'' HKDF.count_loc).+1.
                { rewrite Heqt0 get_set_heap_eq //. }
                have Hu0ideal : get_heap u0 (HKDF.ideal_loc ss_n info_n out_n) = setm Il (s', info) y.
                { rewrite Hequ0 get_set_heap_eq //. }
                have Hu1ideal : get_heap u1 (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N') = setm Il (s', info) y.
                { rewrite Hequ1 get_set_heap_eq //. }
                repeat split.
                1: {
                  move=> l Hl.
                  have Hlc : l.1 != HKDF.count_loc.1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hlk : l.1 != (HPKE.kdone_loc q).1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hli : l.1 != (HKDF.ideal_loc ss_n info_n out_n).1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hlid : l.1 != (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  rewrite Hequ0 (get_set_heap_neq _ _ _ _ Hli) Heqt0 (get_set_heap_neq _ _ _ _ Hlc)
                    Heq0 (get_set_heap_neq _ _ _ _ Hlk).
                  rewrite Hequ1 (get_set_heap_neq _ _ _ _ Hlid) Heq1 (get_set_heap_neq _ _ _ _ Hlk).
                  exact: (Hig l Hl).
                }
                1: {
                  have Hs1 : (HPKE.ss_tbl_loc q SS_N').1 != HKDF.count_loc.1 by [].
                  have Hs2 : (HPKE.ss_tbl_loc q SS_N').1 != (HPKE.kdone_loc q).1 by [].
                  have Hs3 : (HPKE.ss_tbl_loc q SS_N').1 != (HKDF.ideal_loc ss_n info_n out_n).1 by [].
                  have Hs4 : (HPKE.ss_tbl_loc q SS_N').1 != (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Hequ0 (get_set_heap_neq _ _ _ _ Hs3) Heqt0 (get_set_heap_neq _ _ _ _ Hs1)
                    Heq0 (get_set_heap_neq _ _ _ _ Hs2).
                  rewrite Hequ1 (get_set_heap_neq _ _ _ _ Hs4) Heq1 (get_set_heap_neq _ _ _ _ Hs2).
                  move: Hss. rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=. done.
                }
                1: {
                  have Hs1 : (HPKE.k_tbl_loc q Key_N').1 != HKDF.count_loc.1 by [].
                  have Hs2 : (HPKE.k_tbl_loc q Key_N').1 != (HPKE.kdone_loc q).1 by [].
                  have Hs4 : (HPKE.k_tbl_loc q Key_N').1 != (HKDF.ideal_loc ss_n info_n out_n).1 by [].
                  have Hs5 : (HPKE.k_tbl_loc q Key_N').1 != (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Hequ0 (get_set_heap_neq _ _ _ _ Hs4) Heqt0 (get_set_heap_neq _ _ _ _ Hs1)
                    Heq0 (get_set_heap_neq _ _ _ _ Hs2).
                  rewrite Hequ1 (get_set_heap_neq _ _ _ _ Hs5) Heq1 (get_set_heap_neq _ _ _ _ Hs2).
                  exact Hk0.
                }
                1: {
                  have Hd1 : (HPKE.kdone_loc q).1 != (HKDF.ideal_loc ss_n info_n out_n).1 by [].
                  have Hd2 : (HPKE.kdone_loc q).1 != (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Hequ0 (get_set_heap_neq _ _ _ _ Hd1).
                  rewrite Hequ1 (get_set_heap_neq _ _ _ _ Hd2).
                  rewrite Ht0kdone Hs1kdone. reflexivity.
                }
                1: {
                  have He1 : HKDF.count_loc.1 != (HKDF.ideal_loc ss_n info_n out_n).1 by [].
                  have Hd1 : (HPKE.kdone_loc q).1 != (HKDF.ideal_loc ss_n info_n out_n).1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Hequ0 (get_set_heap_neq _ _ _ _ He1) (get_set_heap_neq _ _ _ _ Hd1).
                  rewrite Ht0count Ht0kdone Hcountcpl0 Hsizeeq.
                  reflexivity.
                }
                1: {
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Hu0ideal Hu1ideal. reflexivity.
                }
             (* (Some,None,None) *)
             ++ rewrite HK1n /=.
                eapply (r_put_vs_put (HPKE.k_tbl_loc q Key_N') (setm K1 n y)
                          (HPKE.k_tbl_loc q Key_N') (setm K1 n y) _ _
                          (fun '(t1,t2) => t1=u0 /\ t2=u1)).
                apply r_ret.
                intros s0f s1f Hpre7.
                destruct Hpre7 as [s1x [Hsl Heqs1f]].
                destruct Hsl as [s0x [[Heqa Heqb] Heqs0f]].
                subst s0x s1x.
                split; [reflexivity|].
                have Ht0kdone : get_heap t0 (HPKE.kdone_loc q) = setm D n tt.
                { rewrite Heqt0 get_set_heap_neq // Heq0 get_set_heap_eq //. }
                have Hs1kdone : get_heap s1 (HPKE.kdone_loc q) = setm D n tt.
                { rewrite Heq1 get_set_heap_eq //. }
                have Ht0count : get_heap t0 HKDF.count_loc = (get_heap s0'' HKDF.count_loc).+1.
                { rewrite Heqt0 get_set_heap_eq //. }
                have Hu0ideal : get_heap u0 (HKDF.ideal_loc ss_n info_n out_n) = setm Il (s', info) y.
                { rewrite Hequ0 get_set_heap_eq //. }
                have Hu1ideal : get_heap u1 (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N') = setm Il (s', info) y.
                { rewrite Hequ1 get_set_heap_eq //. }
                have Hs0fk : get_heap s0f (HPKE.k_tbl_loc q Key_N') = setm K1 n y.
                { rewrite Heqs0f get_set_heap_eq //. }
                have Hs1fk : get_heap s1f (HPKE.k_tbl_loc q Key_N') = setm K1 n y.
                { rewrite Heqs1f get_set_heap_eq //. }
                repeat split.
                1: {
                  move=> l Hl.
                  have Hlc : l.1 != HKDF.count_loc.1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hlk : l.1 != (HPKE.kdone_loc q).1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hli : l.1 != (HKDF.ideal_loc ss_n info_n out_n).1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hlid : l.1 != (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hlkt : l.1 != (HPKE.k_tbl_loc q Key_N').1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  rewrite Heqs0f (get_set_heap_neq _ _ _ _ Hlkt) Hequ0 (get_set_heap_neq _ _ _ _ Hli)
                    Heqt0 (get_set_heap_neq _ _ _ _ Hlc) Heq0 (get_set_heap_neq _ _ _ _ Hlk).
                  rewrite Heqs1f (get_set_heap_neq _ _ _ _ Hlkt) Hequ1 (get_set_heap_neq _ _ _ _ Hlid)
                    Heq1 (get_set_heap_neq _ _ _ _ Hlk).
                  exact: (Hig l Hl).
                }
                1: {
                  have H1 : (HPKE.ss_tbl_loc q SS_N').1 != HKDF.count_loc.1 by [].
                  have H2 : (HPKE.ss_tbl_loc q SS_N').1 != (HPKE.kdone_loc q).1 by [].
                  have H3 : (HPKE.ss_tbl_loc q SS_N').1 != (HKDF.ideal_loc ss_n info_n out_n).1 by [].
                  have H4 : (HPKE.ss_tbl_loc q SS_N').1 != (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').1 by [].
                  have H5 : (HPKE.ss_tbl_loc q SS_N').1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Heqs0f (get_set_heap_neq _ _ _ _ H5) Hequ0 (get_set_heap_neq _ _ _ _ H3)
                    Heqt0 (get_set_heap_neq _ _ _ _ H1) Heq0 (get_set_heap_neq _ _ _ _ H2).
                  rewrite Heqs1f (get_set_heap_neq _ _ _ _ H5) Hequ1 (get_set_heap_neq _ _ _ _ H4)
                    Heq1 (get_set_heap_neq _ _ _ _ H2).
                  move: Hss. rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=. done.
                }
                1: {
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Hs0fk Hs1fk. reflexivity.
                }
                1: {
                  have Hd3 : (HPKE.kdone_loc q).1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  have Hd1 : (HPKE.kdone_loc q).1 != (HKDF.ideal_loc ss_n info_n out_n).1 by [].
                  have Hd2 : (HPKE.kdone_loc q).1 != (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Heqs0f (get_set_heap_neq _ _ _ _ Hd3) Hequ0 (get_set_heap_neq _ _ _ _ Hd1).
                  rewrite Heqs1f (get_set_heap_neq _ _ _ _ Hd3) Hequ1 (get_set_heap_neq _ _ _ _ Hd2).
                  rewrite Ht0kdone Hs1kdone. reflexivity.
                }
                1: {
                  have He2 : HKDF.count_loc.1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  have Hd3 : (HPKE.kdone_loc q).1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  have He1 : HKDF.count_loc.1 != (HKDF.ideal_loc ss_n info_n out_n).1 by [].
                  have Hd1 : (HPKE.kdone_loc q).1 != (HKDF.ideal_loc ss_n info_n out_n).1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Heqs0f (get_set_heap_neq _ _ _ _ He2) (get_set_heap_neq _ _ _ _ Hd3).
                  rewrite Hequ0 (get_set_heap_neq _ _ _ _ He1) (get_set_heap_neq _ _ _ _ Hd1).
                  rewrite Ht0count Ht0kdone Hcountcpl0 Hsizeeq.
                  reflexivity.
                }
                1: {
                  have Hi1 : (HKDF.ideal_loc ss_n info_n out_n).1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  have Hi2 : (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Heqs0f (get_set_heap_neq _ _ _ _ Hi1).
                  rewrite Heqs1f (get_set_heap_neq _ _ _ _ Hi2).
                  rewrite Hu0ideal Hu1ideal. reflexivity.
                }
        (* ================= T n = None ================= *)
        * rewrite HTn /=.
          eapply (r_uniform_bij _ _ _ _ id); [exists id; done | intro s].
          eapply (r_put_vs_put (HPKE.ss_tbl_loc q SS_N') (setm T n s) (HPKE.ss_tbl_loc q SS_N')
                    (setm T n s) _ _ (fun '(t0,t1) => t0=s0 /\ t1=s1)).
          eapply rpre_hypothesis_rule => p0 p1 HpreA.
          rewrite (Heta _ _).
          destruct HpreA as [p1x [Hsl Heqp1]].
          destruct Hsl as [p0x [[Heqa Heqb] Heqp0]].
          subst p0x p1x.
          have Hssneq1 : (HPKE.ss_tbl_loc q SS_N').1 != HKDF.count_loc.1 by [].
          have Hkdneq1 : (HPKE.kdone_loc q).1 != HKDF.count_loc.1 by [].
          have Heqp0c : get_heap p0 HKDF.count_loc = get_heap s0'' HKDF.count_loc.
          { rewrite Heqp0 get_set_heap_neq // Heq0 get_set_heap_neq //. }
          eapply (r_get_remember_lhs HKDF.count_loc _ _ (fun '(t0,t1) => t0=p0 /\ t1=p1)) => v.
          eapply rpre_hypothesis_rule => r0 r1 HpreB.
          rewrite (Heta _ _).
          destruct HpreB as [[Heqr0 Heqr1] Hv]. subst r0 r1.
          rewrite /rem_inv /get_side /= in Hv.
          rewrite -Hv Heqp0c.
          have -> : (get_heap s0'' HKDF.count_loc < q)%N = true by exact Hcount_lt.
          simpl.
          eapply (r_put_lhs HKDF.count_loc _ _ _ (fun '(t0,t1) => t0=p0 /\ t1=p1)).
          simpl. simplify_linking. simpl.
          eapply (r_get_remember_lhs (HKDF.ideal_loc ss_n info_n out_n) _ _
            (set_lhs HKDF.count_loc (get_heap s0'' HKDF.count_loc).+1
               (fun '(t0,t1) => t0=p0 /\ t1=p1))) => Il.
          eapply (r_get_remember_rhs (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N') _ _
            (set_lhs HKDF.count_loc (get_heap s0'' HKDF.count_loc).+1
               (fun '(t0,t1) => t0=p0 /\ t1=p1)
             ⋊ rem_lhs (HKDF.ideal_loc ss_n info_n out_n) Il)) => Id.
          eapply rpre_hypothesis_rule => t0 t1 Hpre3.
          rewrite (Heta _ _).
          destruct Hpre3 as [[Hsl HIl] HId].
          destruct Hsl as [t0' [[Heqa Heqb] Heqt0]].
          subst t0' t1.
          rewrite /rem_inv /get_side /= in HIl HId.
          have Hssneq2 : (HKDF.ideal_loc ss_n info_n out_n).1 != (HPKE.ss_tbl_loc q SS_N').1 by [].
          have Hkdneq2 : (HKDF.ideal_loc ss_n info_n out_n).1 != (HPKE.kdone_loc q).1 by [].
          have Hssneq3 : (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').1 != (HPKE.ss_tbl_loc q SS_N').1 by [].
          have Hkdneq3 : (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').1 != (HPKE.kdone_loc q).1 by [].
          have HIleq : Il = get_heap s0'' (HKDF.ideal_loc ss_n info_n out_n).
          { rewrite -HIl Heqt0 get_set_heap_neq // Heqp0 get_set_heap_neq // Heq0 get_set_heap_neq //. }
          have HIdeq : Id = get_heap s1'' (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').
          { rewrite -HId Heqp1 get_set_heap_neq // Heq1 get_set_heap_neq //. }
          move: Hidealcpl. rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=. move=> Hidealcpl.
          have HIleqId : Il = Id by rewrite HIleq HIdeq Hidealcpl.
          rewrite -HIleqId. destruct (Il (s, info)) as [k'|] eqn:HIlkey.
          (* Il = Some k' : (None,Some,_) *)
          -- rewrite HIlkey /=.
             eapply (r_get_remember_lhs (HPKE.k_tbl_loc q Key_N') _ _
               (fun '(t1,t2) => t1=t0 /\ t2=p1)) => K0.
             eapply (r_get_remember_rhs (HPKE.k_tbl_loc q Key_N') _ _
               ((fun '(t1,t2) => t1=t0 /\ t2=p1) ⋊ rem_lhs (HPKE.k_tbl_loc q Key_N') K0)) => K1.
             eapply rpre_hypothesis_rule => w0 w1 Hpre9.
             rewrite (Heta _ _).
             destruct Hpre9 as [[Hw01 HK0] HK1].
             destruct Hw01 as [Hw0 Hw1]. subst w0 w1.
             rewrite /rem_inv /get_side /= in HK0 HK1.
             have Hkt1 : (HPKE.k_tbl_loc q Key_N').1 != (HKDF.ideal_loc ss_n info_n out_n).1 by [].
             have Hkt2 : (HPKE.k_tbl_loc q Key_N').1 != HKDF.count_loc.1 by [].
             have Hkt3 : (HPKE.k_tbl_loc q Key_N').1 != (HPKE.ss_tbl_loc q SS_N').1 by [].
             have Hkt4 : (HPKE.k_tbl_loc q Key_N').1 != (HPKE.kdone_loc q).1 by [].
             have Hkt5 : (HPKE.k_tbl_loc q Key_N').1 != (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').1 by [].
             have HK0eq : K0 = get_heap s0'' (HPKE.k_tbl_loc q Key_N').
             { rewrite -HK0 Heqt0 (get_set_heap_neq _ _ _ _ Hkt2) Heqp0 (get_set_heap_neq _ _ _ _ Hkt3)
                 Heq0 (get_set_heap_neq _ _ _ _ Hkt4). reflexivity. }
             have HK1eq : K1 = get_heap s1'' (HPKE.k_tbl_loc q Key_N').
             { rewrite -HK1 Heqp1 (get_set_heap_neq _ _ _ _ Hkt3) Heq1 (get_set_heap_neq _ _ _ _ Hkt4).
               reflexivity. }
             move: Hk. rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=. move => Hk0.
             have HK01 : K0 = K1 by rewrite HK0eq HK1eq Hk0.
             rewrite HK01.
             destruct (K1 n) as [uu|] eqn:HK1n.
             (* (None,Some,Some) *)
             ++ rewrite HK1n /=.
                apply r_ret.
                intros s0f s1f Hpre6.
                destruct Hpre6 as [Heqs0f Heqs1f]. subst s0f s1f.
                split; [reflexivity|].
                have Hkdssneq : (HPKE.kdone_loc q).1 != (HPKE.ss_tbl_loc q SS_N').1 by [].
                have Ht0kdone : get_heap t0 (HPKE.kdone_loc q) = setm D n tt.
                { rewrite Heqt0 get_set_heap_neq // Heqp0 get_set_heap_neq // Heq0 get_set_heap_eq //. }
                have Hp1kdone : get_heap p1 (HPKE.kdone_loc q) = setm D n tt.
                { rewrite Heqp1 get_set_heap_neq // Heq1 get_set_heap_eq //. }
                have Ht0count : get_heap t0 HKDF.count_loc = (get_heap s0'' HKDF.count_loc).+1.
                { rewrite Heqt0 get_set_heap_eq //. }
                have Ht0ss : get_heap t0 (HPKE.ss_tbl_loc q SS_N') = setm T n s.
                { rewrite Heqt0 get_set_heap_neq // Heqp0 get_set_heap_eq //. }
                have Hp1ss : get_heap p1 (HPKE.ss_tbl_loc q SS_N') = setm T n s.
                { rewrite Heqp1 get_set_heap_eq //. }
                repeat split.
                1: {
                  move=> l Hl.
                  have Hlc : l.1 != HKDF.count_loc.1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hlk : l.1 != (HPKE.kdone_loc q).1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hlss : l.1 != (HPKE.ss_tbl_loc q SS_N').1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  rewrite Heqt0 (get_set_heap_neq _ _ _ _ Hlc) Heqp0 (get_set_heap_neq _ _ _ _ Hlss)
                    Heq0 (get_set_heap_neq _ _ _ _ Hlk).
                  rewrite Heqp1 (get_set_heap_neq _ _ _ _ Hlss) Heq1 (get_set_heap_neq _ _ _ _ Hlk).
                  exact: (Hig l Hl).
                }
                1: {
                  have H1 : (HPKE.ss_tbl_loc q SS_N').1 != HKDF.count_loc.1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Heqt0 (get_set_heap_neq _ _ _ _ H1) Heqp0 get_set_heap_eq.
                  rewrite Heqp1 get_set_heap_eq.
                  reflexivity.
                }
                1: {
                  have H1 : (HPKE.k_tbl_loc q Key_N').1 != HKDF.count_loc.1 by [].
                  have H2 : (HPKE.k_tbl_loc q Key_N').1 != (HPKE.kdone_loc q).1 by [].
                  have H3 : (HPKE.k_tbl_loc q Key_N').1 != (HPKE.ss_tbl_loc q SS_N').1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Heqt0 (get_set_heap_neq _ _ _ _ H1) Heqp0 (get_set_heap_neq _ _ _ _ H3)
                    Heq0 (get_set_heap_neq _ _ _ _ H2).
                  rewrite Heqp1 (get_set_heap_neq _ _ _ _ H3) Heq1 (get_set_heap_neq _ _ _ _ H2).
                  exact Hk0.
                }
                1: {
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Ht0kdone Hp1kdone. reflexivity.
                }
                1: {
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Ht0count Ht0kdone Hcountcpl0 Hsizeeq.
                  reflexivity.
                }
                1: {
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite HIl HId. exact HIleqId.
                }
             (* (None,Some,None) *)
             ++ rewrite HK1n /=.
                eapply (r_put_vs_put (HPKE.k_tbl_loc q Key_N') (setm K1 n k')
                          (HPKE.k_tbl_loc q Key_N') (setm K1 n k') _ _
                          (fun '(t1,t2) => t1=t0 /\ t2=p1)).
                apply r_ret.
                intros s0f s1f Hpre7.
                destruct Hpre7 as [s1x [Hsl Heqs1f]].
                destruct Hsl as [s0x [[Heqa Heqb] Heqs0f]].
                subst s0x s1x.
                split; [reflexivity|].
                have Hkdssneq : (HPKE.kdone_loc q).1 != (HPKE.ss_tbl_loc q SS_N').1 by [].
                have Ht0kdone : get_heap t0 (HPKE.kdone_loc q) = setm D n tt.
                { rewrite Heqt0 get_set_heap_neq // Heqp0 get_set_heap_neq // Heq0 get_set_heap_eq //. }
                have Hp1kdone : get_heap p1 (HPKE.kdone_loc q) = setm D n tt.
                { rewrite Heqp1 get_set_heap_neq // Heq1 get_set_heap_eq //. }
                have Ht0count : get_heap t0 HKDF.count_loc = (get_heap s0'' HKDF.count_loc).+1.
                { rewrite Heqt0 get_set_heap_eq //. }
                have Ht0ss : get_heap t0 (HPKE.ss_tbl_loc q SS_N') = setm T n s.
                { rewrite Heqt0 get_set_heap_neq // Heqp0 get_set_heap_eq //. }
                have Hp1ss : get_heap p1 (HPKE.ss_tbl_loc q SS_N') = setm T n s.
                { rewrite Heqp1 get_set_heap_eq //. }
                have Hs0fk : get_heap s0f (HPKE.k_tbl_loc q Key_N') = setm K1 n k'.
                { rewrite Heqs0f get_set_heap_eq //. }
                have Hs1fk : get_heap s1f (HPKE.k_tbl_loc q Key_N') = setm K1 n k'.
                { rewrite Heqs1f get_set_heap_eq //. }
                repeat split.
                1: {
                  move=> l Hl.
                  have Hlc : l.1 != HKDF.count_loc.1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hlk : l.1 != (HPKE.kdone_loc q).1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hlss : l.1 != (HPKE.ss_tbl_loc q SS_N').1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hlkt : l.1 != (HPKE.k_tbl_loc q Key_N').1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  rewrite Heqs0f (get_set_heap_neq _ _ _ _ Hlkt) Heqt0 (get_set_heap_neq _ _ _ _ Hlc)
                    Heqp0 (get_set_heap_neq _ _ _ _ Hlss) Heq0 (get_set_heap_neq _ _ _ _ Hlk).
                  rewrite Heqs1f (get_set_heap_neq _ _ _ _ Hlkt) Heqp1 (get_set_heap_neq _ _ _ _ Hlss)
                    Heq1 (get_set_heap_neq _ _ _ _ Hlk).
                  exact: (Hig l Hl).
                }
                1: {
                  have Hs5 : (HPKE.ss_tbl_loc q SS_N').1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Heqs0f (get_set_heap_neq _ _ _ _ Hs5).
                  rewrite Heqs1f (get_set_heap_neq _ _ _ _ Hs5).
                  rewrite Ht0ss Hp1ss. reflexivity.
                }
                1: {
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Hs0fk Hs1fk. reflexivity.
                }
                1: {
                  have Hd3 : (HPKE.kdone_loc q).1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Heqs0f (get_set_heap_neq _ _ _ _ Hd3).
                  rewrite Heqs1f (get_set_heap_neq _ _ _ _ Hd3).
                  rewrite Ht0kdone Hp1kdone. reflexivity.
                }
                1: {
                  have He2 : HKDF.count_loc.1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  have Hd3 : (HPKE.kdone_loc q).1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Heqs0f (get_set_heap_neq _ _ _ _ He2) (get_set_heap_neq _ _ _ _ Hd3).
                  rewrite Ht0count Ht0kdone Hcountcpl0 Hsizeeq.
                  reflexivity.
                }
                1: {
                  have Hi1 : (HKDF.ideal_loc ss_n info_n out_n).1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  have Hi2 : (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Heqs0f (get_set_heap_neq _ _ _ _ Hi1).
                  rewrite Heqs1f (get_set_heap_neq _ _ _ _ Hi2).
                  rewrite HIl HId. exact HIleqId.
                }
          (* Il = None : (None,None,_) *)
          -- rewrite HIlkey /=.
             eapply (r_uniform_bij _ _ _ _ id); [exists id; done | intro y].
             eapply (r_put_lhs (HKDF.ideal_loc ss_n info_n out_n) (setm Il (s, info) y) _ _
               (fun '(t1,t2) => t1=t0 /\ t2=p1)).
             eapply (r_put_rhs (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N') (setm Il (s, info) y) _ _
               (set_lhs (HKDF.ideal_loc ss_n info_n out_n) (setm Il (s, info) y)
                  (fun '(t1,t2) => t1=t0 /\ t2=p1))).
             eapply rpre_hypothesis_rule => u0 u1 Hpre8.
             rewrite (Heta _ _).
             destruct Hpre8 as [u1' [Hsl Hequ1]].
             destruct Hsl as [u0' [[Heqa Heqb] Hequ0]].
             subst u0' u1'.
             eapply (r_get_remember_lhs (HPKE.k_tbl_loc q Key_N') _ _
               (fun '(t1,t2) => t1=u0 /\ t2=u1)) => K0.
             eapply (r_get_remember_rhs (HPKE.k_tbl_loc q Key_N') _ _
               ((fun '(t1,t2) => t1=u0 /\ t2=u1) ⋊ rem_lhs (HPKE.k_tbl_loc q Key_N') K0)) => K1.
             eapply rpre_hypothesis_rule => w0 w1 Hpre9.
             rewrite (Heta _ _).
             destruct Hpre9 as [[Hw01 HK0] HK1].
             destruct Hw01 as [Hw0 Hw1]. subst w0 w1.
             rewrite /rem_inv /get_side /= in HK0 HK1.
             have Hkt1 : (HPKE.k_tbl_loc q Key_N').1 != (HKDF.ideal_loc ss_n info_n out_n).1 by [].
             have Hkt2 : (HPKE.k_tbl_loc q Key_N').1 != HKDF.count_loc.1 by [].
             have Hkt3 : (HPKE.k_tbl_loc q Key_N').1 != (HPKE.ss_tbl_loc q SS_N').1 by [].
             have Hkt4 : (HPKE.k_tbl_loc q Key_N').1 != (HPKE.kdone_loc q).1 by [].
             have Hkt5 : (HPKE.k_tbl_loc q Key_N').1 != (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').1 by [].
             have HK0eq : K0 = get_heap s0'' (HPKE.k_tbl_loc q Key_N').
             { rewrite -HK0 Hequ0 (get_set_heap_neq _ _ _ _ Hkt1) Heqt0 (get_set_heap_neq _ _ _ _ Hkt2)
                 Heqp0 (get_set_heap_neq _ _ _ _ Hkt3) Heq0 (get_set_heap_neq _ _ _ _ Hkt4).
               reflexivity. }
             have HK1eq : K1 = get_heap s1'' (HPKE.k_tbl_loc q Key_N').
             { rewrite -HK1 Hequ1 (get_set_heap_neq _ _ _ _ Hkt5) Heqp1 (get_set_heap_neq _ _ _ _ Hkt3)
                 Heq1 (get_set_heap_neq _ _ _ _ Hkt4). reflexivity. }
             move: Hk. rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=. move => Hk0.
             have HK01 : K0 = K1 by rewrite HK0eq HK1eq Hk0.
             rewrite HK01.
             destruct (K1 n) as [uu|] eqn:HK1n.
             (* (None,None,Some) *)
             ++ rewrite HK1n /=.
                apply r_ret.
                intros s0f s1f Hpre6.
                destruct Hpre6 as [Heqs0f Heqs1f]. subst s0f s1f.
                split; [reflexivity|].
                have Hkdssneq : (HPKE.kdone_loc q).1 != (HPKE.ss_tbl_loc q SS_N').1 by [].
                have Ht0kdone : get_heap t0 (HPKE.kdone_loc q) = setm D n tt.
                { rewrite Heqt0 get_set_heap_neq // Heqp0 get_set_heap_neq // Heq0 get_set_heap_eq //. }
                have Hp1kdone : get_heap p1 (HPKE.kdone_loc q) = setm D n tt.
                { rewrite Heqp1 get_set_heap_neq // Heq1 get_set_heap_eq //. }
                have Ht0count : get_heap t0 HKDF.count_loc = (get_heap s0'' HKDF.count_loc).+1.
                { rewrite Heqt0 get_set_heap_eq //. }
                have Ht0ss : get_heap t0 (HPKE.ss_tbl_loc q SS_N') = setm T n s.
                { rewrite Heqt0 get_set_heap_neq // Heqp0 get_set_heap_eq //. }
                have Hp1ss : get_heap p1 (HPKE.ss_tbl_loc q SS_N') = setm T n s.
                { rewrite Heqp1 get_set_heap_eq //. }
                have Hu0ideal : get_heap u0 (HKDF.ideal_loc ss_n info_n out_n) = setm Il (s, info) y.
                { rewrite Hequ0 get_set_heap_eq //. }
                have Hu1ideal : get_heap u1 (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N') = setm Il (s, info) y.
                { rewrite Hequ1 get_set_heap_eq //. }
                repeat split.
                1: {
                  move=> l Hl.
                  have Hlc : l.1 != HKDF.count_loc.1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hlk : l.1 != (HPKE.kdone_loc q).1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hlss : l.1 != (HPKE.ss_tbl_loc q SS_N').1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hli : l.1 != (HKDF.ideal_loc ss_n info_n out_n).1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hlid : l.1 != (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  rewrite Hequ0 (get_set_heap_neq _ _ _ _ Hli) Heqt0 (get_set_heap_neq _ _ _ _ Hlc)
                    Heqp0 (get_set_heap_neq _ _ _ _ Hlss) Heq0 (get_set_heap_neq _ _ _ _ Hlk).
                  rewrite Hequ1 (get_set_heap_neq _ _ _ _ Hlid) Heqp1 (get_set_heap_neq _ _ _ _ Hlss)
                    Heq1 (get_set_heap_neq _ _ _ _ Hlk).
                  exact: (Hig l Hl).
                }
                1: {
                  have Hs1 : (HPKE.ss_tbl_loc q SS_N').1 != HKDF.count_loc.1 by [].
                  have Hs2 : (HPKE.ss_tbl_loc q SS_N').1 != (HPKE.kdone_loc q).1 by [].
                  have Hs3 : (HPKE.ss_tbl_loc q SS_N').1 != (HKDF.ideal_loc ss_n info_n out_n).1 by [].
                  have Hs4 : (HPKE.ss_tbl_loc q SS_N').1 != (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Hequ0 (get_set_heap_neq _ _ _ _ Hs3) Heqt0 (get_set_heap_neq _ _ _ _ Hs1)
                    Heqp0 get_set_heap_eq.
                  rewrite Hequ1 (get_set_heap_neq _ _ _ _ Hs4) Heqp1 get_set_heap_eq.
                  reflexivity.
                }
                1: {
                  have Hs1 : (HPKE.k_tbl_loc q Key_N').1 != HKDF.count_loc.1 by [].
                  have Hs2 : (HPKE.k_tbl_loc q Key_N').1 != (HPKE.kdone_loc q).1 by [].
                  have Hs3 : (HPKE.k_tbl_loc q Key_N').1 != (HPKE.ss_tbl_loc q SS_N').1 by [].
                  have Hs4 : (HPKE.k_tbl_loc q Key_N').1 != (HKDF.ideal_loc ss_n info_n out_n).1 by [].
                  have Hs5 : (HPKE.k_tbl_loc q Key_N').1 != (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Hequ0 (get_set_heap_neq _ _ _ _ Hs4) Heqt0 (get_set_heap_neq _ _ _ _ Hs1)
                    Heqp0 (get_set_heap_neq _ _ _ _ Hs3) Heq0 (get_set_heap_neq _ _ _ _ Hs2).
                  rewrite Hequ1 (get_set_heap_neq _ _ _ _ Hs5) Heqp1 (get_set_heap_neq _ _ _ _ Hs3)
                    Heq1 (get_set_heap_neq _ _ _ _ Hs2).
                  exact Hk0.
                }
                1: {
                  have Hd1 : (HPKE.kdone_loc q).1 != (HKDF.ideal_loc ss_n info_n out_n).1 by [].
                  have Hd2 : (HPKE.kdone_loc q).1 != (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Hequ0 (get_set_heap_neq _ _ _ _ Hd1).
                  rewrite Hequ1 (get_set_heap_neq _ _ _ _ Hd2).
                  rewrite Ht0kdone Hp1kdone. reflexivity.
                }
                1: {
                  have He1 : HKDF.count_loc.1 != (HKDF.ideal_loc ss_n info_n out_n).1 by [].
                  have Hd1 : (HPKE.kdone_loc q).1 != (HKDF.ideal_loc ss_n info_n out_n).1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Hequ0 (get_set_heap_neq _ _ _ _ He1) (get_set_heap_neq _ _ _ _ Hd1).
                  rewrite Ht0count Ht0kdone Hcountcpl0 Hsizeeq.
                  reflexivity.
                }
                1: {
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Hu0ideal Hu1ideal. reflexivity.
                }
             (* (None,None,None) *)
             ++ rewrite HK1n /=.
                eapply (r_put_vs_put (HPKE.k_tbl_loc q Key_N') (setm K1 n y)
                          (HPKE.k_tbl_loc q Key_N') (setm K1 n y) _ _
                          (fun '(t1,t2) => t1=u0 /\ t2=u1)).
                apply r_ret.
                intros s0f s1f Hpre7.
                destruct Hpre7 as [s1x [Hsl Heqs1f]].
                destruct Hsl as [s0x [[Heqa Heqb] Heqs0f]].
                subst s0x s1x.
                split; [reflexivity|].
                have Hkdssneq : (HPKE.kdone_loc q).1 != (HPKE.ss_tbl_loc q SS_N').1 by [].
                have Ht0kdone : get_heap t0 (HPKE.kdone_loc q) = setm D n tt.
                { rewrite Heqt0 get_set_heap_neq // Heqp0 get_set_heap_neq // Heq0 get_set_heap_eq //. }
                have Hp1kdone : get_heap p1 (HPKE.kdone_loc q) = setm D n tt.
                { rewrite Heqp1 get_set_heap_neq // Heq1 get_set_heap_eq //. }
                have Ht0count : get_heap t0 HKDF.count_loc = (get_heap s0'' HKDF.count_loc).+1.
                { rewrite Heqt0 get_set_heap_eq //. }
                have Ht0ss : get_heap t0 (HPKE.ss_tbl_loc q SS_N') = setm T n s.
                { rewrite Heqt0 get_set_heap_neq // Heqp0 get_set_heap_eq //. }
                have Hp1ss : get_heap p1 (HPKE.ss_tbl_loc q SS_N') = setm T n s.
                { rewrite Heqp1 get_set_heap_eq //. }
                have Hu0ideal : get_heap u0 (HKDF.ideal_loc ss_n info_n out_n) = setm Il (s, info) y.
                { rewrite Hequ0 get_set_heap_eq //. }
                have Hu1ideal : get_heap u1 (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N') = setm Il (s, info) y.
                { rewrite Hequ1 get_set_heap_eq //. }
                have Hs0fk : get_heap s0f (HPKE.k_tbl_loc q Key_N') = setm K1 n y.
                { rewrite Heqs0f get_set_heap_eq //. }
                have Hs1fk : get_heap s1f (HPKE.k_tbl_loc q Key_N') = setm K1 n y.
                { rewrite Heqs1f get_set_heap_eq //. }
                repeat split.
                1: {
                  move=> l Hl.
                  have Hlc : l.1 != HKDF.count_loc.1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hlk : l.1 != (HPKE.kdone_loc q).1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hlss : l.1 != (HPKE.ss_tbl_loc q SS_N').1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hli : l.1 != (HKDF.ideal_loc ss_n info_n out_n).1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hlid : l.1 != (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  have Hlkt : l.1 != (HPKE.k_tbl_loc q Key_N').1 by
                    (apply/eqP => Heq; case/negP: Hl; rewrite Heq; apply: fhas_in; fmap_solve).
                  rewrite Heqs0f (get_set_heap_neq _ _ _ _ Hlkt) Hequ0 (get_set_heap_neq _ _ _ _ Hli)
                    Heqt0 (get_set_heap_neq _ _ _ _ Hlc) Heqp0 (get_set_heap_neq _ _ _ _ Hlss)
                    Heq0 (get_set_heap_neq _ _ _ _ Hlk).
                  rewrite Heqs1f (get_set_heap_neq _ _ _ _ Hlkt) Hequ1 (get_set_heap_neq _ _ _ _ Hlid)
                    Heqp1 (get_set_heap_neq _ _ _ _ Hlss) Heq1 (get_set_heap_neq _ _ _ _ Hlk).
                  exact: (Hig l Hl).
                }
                1: {
                  have Hs5 : (HPKE.ss_tbl_loc q SS_N').1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  have Hs3 : (HPKE.ss_tbl_loc q SS_N').1 != (HKDF.ideal_loc ss_n info_n out_n).1 by [].
                  have Hs4 : (HPKE.ss_tbl_loc q SS_N').1 != (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').1 by [].
                  have Hs1 : (HPKE.ss_tbl_loc q SS_N').1 != HKDF.count_loc.1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Heqs0f (get_set_heap_neq _ _ _ _ Hs5) Hequ0 (get_set_heap_neq _ _ _ _ Hs3)
                    Heqt0 (get_set_heap_neq _ _ _ _ Hs1) Heqp0 get_set_heap_eq.
                  rewrite Heqs1f (get_set_heap_neq _ _ _ _ Hs5) Hequ1 (get_set_heap_neq _ _ _ _ Hs4)
                    Heqp1 get_set_heap_eq.
                  reflexivity.
                }
                1: {
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Hs0fk Hs1fk. reflexivity.
                }
                1: {
                  have Hd3 : (HPKE.kdone_loc q).1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  have Hd1 : (HPKE.kdone_loc q).1 != (HKDF.ideal_loc ss_n info_n out_n).1 by [].
                  have Hd2 : (HPKE.kdone_loc q).1 != (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Heqs0f (get_set_heap_neq _ _ _ _ Hd3) Hequ0 (get_set_heap_neq _ _ _ _ Hd1).
                  rewrite Heqs1f (get_set_heap_neq _ _ _ _ Hd3) Hequ1 (get_set_heap_neq _ _ _ _ Hd2).
                  rewrite Ht0kdone Hp1kdone. reflexivity.
                }
                1: {
                  have He2 : HKDF.count_loc.1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  have Hd3 : (HPKE.kdone_loc q).1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  have He1 : HKDF.count_loc.1 != (HKDF.ideal_loc ss_n info_n out_n).1 by [].
                  have Hd1 : (HPKE.kdone_loc q).1 != (HKDF.ideal_loc ss_n info_n out_n).1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Heqs0f (get_set_heap_neq _ _ _ _ He2) (get_set_heap_neq _ _ _ _ Hd3).
                  rewrite Hequ0 (get_set_heap_neq _ _ _ _ He1) (get_set_heap_neq _ _ _ _ Hd1).
                  rewrite Ht0count Ht0kdone Hcountcpl0 Hsizeeq.
                  reflexivity.
                }
                1: {
                  have Hi1 : (HKDF.ideal_loc ss_n info_n out_n).1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  have Hi2 : (HPKE.ideal_tbl_loc SS_N' Key_N' Info_N').1 != (HPKE.k_tbl_loc q Key_N').1 by [].
                  rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
                  rewrite Heqs0f (get_set_heap_neq _ _ _ _ Hi1).
                  rewrite Heqs1f (get_set_heap_neq _ _ _ _ Hi2).
                  rewrite Hu0ideal Hu1ideal. reflexivity.
                }
  Qed.

  Lemma KDFC_hkdf_ideal_bridge :
    ∀ (LA : Locations) (A : raw_package),
      ValidPackage LA
        (unionm (HPKE.I_kdf_env q Key_N') (HPKE.KDF_out q Info_N'))
        A_export A →
      fseparate LA GKDF_mid_hkdf_locs →
      fseparate LA GKDF_mid_ref_locs →
      AdvantageE
        (HPKE.GKDF_mid q SS_N' Key_N' Info_N' KDFC_hkdf)
        (HPKE.GKDF_mid_ref q SS_N' Key_N' Info_N') A = 0.
  Proof.
    intros LA A vA hloc1 hloc2.
    have v0 : ValidPackage GKDF_mid_hkdf_locs Game_import
      (unionm (HPKE.I_kdf_env q Key_N') (HPKE.KDF_out q Info_N'))
      (HPKE.GKDF_mid q SS_N' Key_N' Info_N' KDFC_hkdf).
    {
      unfold HPKE.GKDF_mid, HPKE.CORE, GKDF_mid_hkdf_locs.
      have hK := KDFC_hkdf_valid false.
      ssprove_valid.
    }
    have v1 : ValidPackage GKDF_mid_ref_locs Game_import
      (unionm (HPKE.I_kdf_env q Key_N') (HPKE.KDF_out q Info_N'))
      (HPKE.GKDF_mid_ref q SS_N' Key_N' Info_N').
    {
      unfold HPKE.GKDF_mid_ref, GKDF_mid_ref_locs.
      have hK := pack_valid (HPKE.KDFC_IDEAL SS_N' Key_N' Info_N').
      ssprove_valid.
    }
    have Hperf : HPKE.GKDF_mid q SS_N' Key_N' Info_N' KDFC_hkdf ≈₀
      HPKE.GKDF_mid_ref q SS_N' Key_N' Info_N'.
    {
      eapply eq_rel_perf_ind with (inv := KDFC_hkdf_ideal_inv).
      1:{
        unfold KDFC_hkdf_ideal_inv.
        eapply Invariant_inv_conj.
        2:{ eapply SemiInvariant_relApp.
          - simpl. repeat split; try fmap_solve; try done.
          - done.
        }
        eapply Invariant_inv_conj.
        2:{ eapply SemiInvariant_relApp.
          - simpl. repeat split; try fmap_solve; try done.
          - simpl. by rewrite domm0.
        }
        eapply Invariant_inv_conj.
        2:{ eapply SemiInvariant_relApp.
          - simpl. repeat split; try fmap_solve; try done.
          - done.
        }
        eapply Invariant_inv_conj.
        2:{ eapply SemiInvariant_relApp.
          - simpl. repeat split; try fmap_solve; try done.
          - done.
        }
        eapply Invariant_inv_conj.
        - eapply Invariant_heap_ignore. fmap_solve.
        - eapply SemiInvariant_relApp.
          + simpl. repeat split; try fmap_solve; try done.
          + done.
      }
      simplify_eq_rel m.
      1:{
        apply r_get_remember_lhs => T0.
        apply r_get_remember_rhs => T1.
        ssprove_rem_rel 4%N => Heq.
        rewrite -Heq.
        destruct (T0 m) as [s'|] eqn:HT.
        - rewrite HT /=.
          apply r_ret.
          intros s0 s1 Hpre; destruct Hpre as [[Hinv ?] ?].
          split; [reflexivity | exact Hinv].
        - rewrite HT /=.
          eapply (r_uniform_bij _ _ _ _ id); [exists id; done | intro s].
          apply r_put_vs_put.
          ssprove_restore_mem; last by apply r_ret.
          eapply preserve_update_mem_conj.
          1: ssprove_invariant.
          eapply preserve_update_mem_rel; ssprove_invariant.
      }
      1:{
        apply r_get_remember_lhs => T0.
        apply r_get_remember_rhs => T1.
        ssprove_rem_rel 3%N => Heq.
        rewrite -Heq.
        destruct (T0 m) as [k'|] eqn:HT.
        - rewrite HT /=.
          apply r_ret.
          intros s0 s1 Hpre; destruct Hpre as [[Hinv ?] ?].
          split; [reflexivity | exact Hinv].
        - rewrite HT /=.
          eapply (r_uniform_bij _ _ _ _ id); [exists id; done | intro k].
          apply r_put_vs_put.
          ssprove_restore_mem; last by apply r_ret.
          eapply preserve_update_mem_conj.
          1: ssprove_invariant.
          eapply preserve_update_mem_rel; ssprove_invariant.
      }
      1:{ case: m => n info. exact (KDFC_hkdf_ideal_bridge_DERIVE_K_case n info). }
    }
    exact (Hperf LA A vA hloc1 hloc2).
  Qed.

  (** OPTIONAL real-side adequacy — not needed for any bound below; it
    only upgrades the READING of the final theorem: the same
    dead-throttle argument, run on the real branch, shows the throttled
    real game equals the game over the UNTHROTTLED [KDF_real], so the
    theorem is about the actual protocol, not "HPKE whose KDF core gives
    up after q calls". *)
  Lemma GKDF_real_unthrottled :
    ∀ (LA : Locations) (A : raw_package),
      ValidPackage LA
        (unionm (HPKE.I_kdf_env q Key_N') (HPKE.KDF_out q Info_N'))
        A_export A →
      AdvantageE
        (HPKE.GKDF q SS_N' Key_N' Info_N' KDFC_hkdf true)
        (HPKE.GKDF q SS_N' Key_N' Info_N'
           (λ b, pack (HKDF.KDF ss_n prk_n info_n out_n PRF b)) true) A = 0.
  Proof.
  Admitted.

  (** * The other two hops' components, still abstract *)

  Context (Ectx_N Plain_N Cipher_N : nat).

  Context (DHKEM : bool → raw_package).
  Context (DHKEM_loc : Locations).
  Context (DHKEM_valid :
    ∀ b, ValidPackage DHKEM_loc (HPKE.DHKEM_in q SS_N' b)
           (HPKE.DHKEM_out q Ectx_N) (DHKEM b)).

  Context (AEADP : bool → raw_package).
  Context (AEAD_loc : Locations).
  Context (AEAD_valid :
    ∀ b, ValidPackage AEAD_loc (HPKE.AEAD_in q Key_N')
           (HPKE.AEAD_out q Plain_N Cipher_N) (AEADP b)).

  (** * The imported bound

    [HPKE.GKDF_bound] (this repo, HPKE.v) + [HKDF.security_of_KDF]
    (imported, opaque) = the concrete KDF-hop bound. The hypotheses
    below the first are exactly [security_of_KDF]'s own, stated at the
    composed adversary [A ∘ R_core] and its location set [LA']. *)

  (** The spaces are powers of two, so the positivity hypotheses that
    HPKE.v's losslessness discipline needs are facts here. *)
  Lemma SS_N'_gt0 : (0 < SS_N')%N.
  Proof. by rewrite /HKDF.SS_N expn_gt0. Qed.

  Lemma Key_N'_gt0 : (0 < Key_N')%N.
  Proof. by rewrite /HKDF.Out_N expn_gt0. Qed.

  Corollary GKDF_security_from_HKDF :
    ∀ (LA LA' : Locations) (A : raw_package),
      ValidPackage LA
        (unionm (HPKE.I_kdf_env q Key_N') (HPKE.KDF_out q Info_N'))
        A_export A →
      ValidPackage LA' (HKDF.DERIVE_export ss_n info_n out_n) A_export
        (A ∘ HPKE.R_core q SS_N' Key_N' Info_N') →
      fseparate LA GKDF_mid_hkdf_locs →
      fseparate LA GKDF_mid_ref_locs →
      (* GKDF_bound's adversary-side separation premises (the instrumented
        up-to-bad games' locations), at this instantiation: *)
      fseparate LA
        (unionm (HPKE.KDF_loc q)
          (unionm (HPKE.KEYS_bad_loc q SS_N' Key_N')
                  (HPKE.KDFC_IDEAL_loc SS_N' Key_N' Info_N'))) →
      fseparate LA
        (unionm (HPKE.KDF_loc q)
          (unionm (HPKE.KEYS_loc q SS_N' Key_N')
                  (HPKE.KDFC_IDEAL_loc SS_N' Key_N' Info_N'))) →
      fseparate LA
        (unionm (HPKE.KDF_loc q)
          (unionm (HPKE.KEYS_bad_loc q SS_N' Key_N') KDFC_hkdf_loc)) →
      fseparate LA
        (unionm (HPKE.KDF_loc q)
          (unionm (HPKE.KEYS_loc q SS_N' Key_N') KDFC_hkdf_loc)) →
      lossless_valid_adv LA
        (unionm (HPKE.I_kdf_env q Key_N') (HPKE.KDF_out q Info_N'))
        (resolve A RUN tt) →
      fseparate LA' (HKDF.KDF_real_locs ss_n prk_n) →
      fseparate LA' (HKDF.KDF_mid_locs ss_n prk_n info_n out_n) →
      fseparate LA' (HKDF.KDF_ideal_locs ss_n info_n out_n) →
      fseparate LA' (HKDF.KDF_hyb_locs ss_n prk_n info_n out_n) →
      fseparate LA' (HKDF.KDF_hybE_bad_locs ss_n prk_n info_n out_n) →
      fseparate LA' (HKDF.KDF_hyb_bad_locs ss_n prk_n info_n out_n) →
      fseparate LA' (HKDF.KDF_mid'_bad_locs ss_n prk_n info_n out_n) →
      fseparate LA' (mkfmap (HKDF.count_loc :: nil)) →
      fseparate LA' (mkfmap (HKDF.eval_key_loc prk_n :: nil)) →
      fseparate LA' (mkfmap (HKDF.eval_tbl_loc info_n out_n :: nil)) →
      lossless_valid_adv LA' (HKDF.DERIVE_export ss_n info_n out_n)
        (resolve (A ∘ HPKE.R_core q SS_N' Key_N' Info_N') RUN tt) →
      AdvantageE
        (HPKE.GKDF q SS_N' Key_N' Info_N' KDFC_hkdf true)
        (HPKE.GKDF q SS_N' Key_N' Info_N' KDFC_hkdf false) A <=
        (\sum_(i < q)
           HKDF.prf_epsilon prk_n info_n out_n PRF
             (((A ∘ HPKE.R_core q SS_N' Key_N' Info_N')
                 ∘ HKDF.COUNT ss_n info_n out_n q)
                ∘ HKDF.KDF_hyb_EVAL ss_n prk_n info_n out_n PRF i))
        + q%:R * HKDF.birthday_bound prk_n q
        + HKDF.birthday_bound prk_n q
        + HPKE.birthday_ss q SS_N'.
  Proof.
    intros LA LA' A vA vA' hloc1 hloc2 hs1 hs2 hs3 hs4 HlvaHop
      d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 Hlva.
    have fc1 : fcompat (HPKE.KDF_loc q) KDFC_hkdf_loc by fmap_solve.
    have fc2 : fcompat (HPKE.KEYS_loc q SS_N' Key_N') KDFC_hkdf_loc
      by fmap_solve.
    have fc3 : fcompat (HPKE.KEYS_bad_loc q SS_N' Key_N') KDFC_hkdf_loc
      by fmap_solve.
    eapply le_trans.
    1:{
      (* NOTE: completing HPKE.v's proofs SHRANK GKDF_bound's closed-section
        signature — its former Admitted dependencies had dragged the (unused)
        DHKEM/AEAD section context into the generalized argument list; the
        real proof term only depends on the KDF hop, so those arguments are
        gone now. *)
      eapply (HPKE.GKDF_bound
        q SS_N' Key_N' Info_N'
        SS_N'_gt0 Key_N'_gt0
        KDFC_hkdf KDFC_hkdf_loc KDFC_hkdf_valid
        LA A fc1 fc2 fc3 vA hs1 hs2 hs3 hs4 HlvaHop
        (KDFC_hkdf_ideal_bridge LA A vA hloc1 hloc2)).
    }
    apply lerD. 2: apply lexx.
    exact (HKDF.security_of_KDF ss_n prk_n info_n out_n PRF LA'
      (A ∘ HPKE.R_core q SS_N' Key_N' Info_N') q
      vA' d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 Hlva).
  Qed.

End HPKE_from_HKDF.
