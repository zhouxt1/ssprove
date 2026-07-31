(**
  Extract-then-Expand key derivation (à la HKDF, RFC 5869), and the
  "birthday term" that shows up when proving it behaves like a PRF.

  The construction:
  - Extract is modelled as a random oracle [H : SharedSecret -> PRK],
    lazily sampled and cached, exactly like [RandomOracle.v].
  - Expand is a (deterministic, public) PRF [PRF : Info -> PRK -> Out],
    keyed by the [prk] that Extract produced.
  - The composed construction is
        DERIVE (ss, info) := PRF info (H ss).

  We would like [DERIVE] to be indistinguishable from an independent
  uniformly random function of (ss, info). The catch: [H] is a single
  shared table, so if the adversary makes q queries with (say) q distinct
  shared secrets, there is a chance that two of them collide under [H]
  (get assigned the same [prk]). When that happens, the two "independent"
  PRF instances used for Expand are actually the *same* keyed instance,
  which is exactly the situation the usual single-key/multi-key hybrid
  argument does not account for. Bounding the probability of that event is
  the classical birthday bound: with q samples landing in a space of size
  [PRK_N], collisions happen with probability at most roughly
  [q^2 / (2 * PRK_N)].

  PROOF ROADMAP (the development is COMPLETE: every lemma in this file
  is [Qed]'d -- no [Admitted], no [admit], no [Axiom]; the only axioms
  involved are SSProve's ambient ones, cf. [Print Assumptions
  security_of_KDF]):

    KDF_real                     -- Extract (RO) + Expand (real PRF)
       |  hybrid over the <= q distinct SHARED SECRETS Extract has seen;
       |  at each step we swap one instance of Expand for an independent
       |  random function using the security of PRF ([KDF_hyb_EVAL i ∘
       |  EVAL true] vs [KDF_hyb i], a perfect [≈₀] equivalence -- no
       |  birthday assumption needed there). The OTHER leg of the same
       |  hop ([KDF_hyb_EVAL i ∘ EVAL false] vs [KDF_hyb i.+1]) is NOT a
       |  perfect equivalence, though: it can diverge the moment Extract
       |  hands the SAME [prk] to a second, different shared secret (see
       |  the counterexample docstring above [get_prk_bad] for a concrete
       |  proof this is unavoidable), so it is bounded up-to-bad instead,
       |  reusing step 2's own [KDF_mid]/[KDF_mid']/[KDF_bad] birthday
       |  machinery one hop at a time ([KDF_hybE_bad i] / [KDF_hyb_bad j]
       |  / [KDF_hyb_EVAL_false_bound]). This is what puts a SECOND sum,
       |  of per-hop [Pr_bad] terms, into [KDF_hyb_bound]/
       |  [KDF_real_KDF_mid_bound]'s conclusions below (collapsing to
       |  [q * birthday_bound q] once counted, in [security_of_KDF]).
       v
    KDF_mid                      -- Extract (RO) + Expand (now IDEAL, but
                                     still keyed by whatever [prk] Extract
                                     handed out)
       |  identical-until-bad: [KDF_mid] and [KDF_ideal] can only differ
       |  when Extract has assigned the same [prk] to two different
       |  shared secrets ("bad"). This is exactly the birthday bound:
       |  Pr[bad] <= q^2 / (2 * PRK_N) for <= q distinct queries.
       v
    KDF_ideal                    -- one independent uniform output per
                                     (ss, info) pair

  giving, in the end ([security_of_KDF]),

    Advantage KDF A <=
      (\sum_(i < q) prf_epsilon (... i-th hybrid reduction ...))
      + q%:R * birthday_bound q     (* hop-1's per-hop up-to-bad legs *)
      + birthday_bound q.           (* step 2's own up-to-bad argument *)

  Both [KDF_real_KDF_mid_bound] (step 1) and [KDF_mid_KDF_ideal_bound]
  (step 2) are fully assembled and [Qed]'d, INCLUDING the once-open
  mirror lemmas ([KDF_hyb_bad_KDF_hyb_equiv], [KDF_hybE_bad_equiv],
  [KDF_hybE_bad_bad_preserved], [KDF_hyb_bad_bad_preserved],
  [KDF_hybE_bad_Invariant], [KDF_hybE_bad_eq_up_to_bad]) and both
  counting kernels [Pr_bad_adv_bound] / [Pr_bad_adv_bound_hybE] (the
  substantial induction-on-adversary-code arguments the birthday steps
  need -- see their docstrings; earlier revisions of this header listed
  some of these as [Admitted], which is no longer the case).

  [security_of_KDF] is reused as a black box by HPKE.v / HPKE_HKDF.v
  (this directory): there, [COUNT q ∘ KDF b] instantiates the abstract
  KDF core of an HPKE-style 3-hop composition.
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
  pkg_lossless pkg_upto_bad UpToBadState.
From SSProve.Crypt.nominal Require Import Pr.
From SSProve.Crypt.examples Require Import Birthday.

From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.

Import SPropNotations.
Import PackageNotation.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

Section HKDF_example.

  (* All spaces are powers of two, following the convention in PRF.v. *)
  Context (ss_n prk_n info_n out_n : nat).

  Definition SS_N : nat := 2^ss_n.
  Definition PRK_N : nat := 2^prk_n.
  Definition Info_N : nat := 2^info_n.
  Definition Out_N : nat := 2^out_n.

  Definition SS : choice_type := 'fin SS_N.
  Definition PRK : choice_type := 'fin PRK_N.
  Definition Info : choice_type := 'fin Info_N.
  Definition Out : choice_type := 'fin Out_N.

  Notation " 'ss " := SS (in custom pack_type at level 2).
  Notation " 'ss " := SS (at level 2) : package_scope.
  Notation " 'prk " := PRK (in custom pack_type at level 2).
  Notation " 'prk " := PRK (at level 2) : package_scope.
  Notation " 'info " := Info (in custom pack_type at level 2).
  Notation " 'info " := Info (at level 2) : package_scope.
  Notation " 'out " := Out (in custom pack_type at level 2).
  Notation " 'out " := Out (at level 2) : package_scope.

  #[local] Open Scope package_scope.

  (* The Expand step: a public, deterministic PRF keyed by the Extract
     output. Assumed to be a secure PRF (see [prf_epsilon] below). *)
  Context (PRF : Info -> PRK -> Out).

  Definition DERIVE : nat := 0.

  Definition DERIVE_export :=
    [interface #val #[ DERIVE ] : 'ss × 'info → 'out ].

  (** A [q]-query-bounded wrapper on [DERIVE_export]: past the [q]-th
    call, every further [DERIVE] call is answered by an independent
    uniform sample instead of being routed to the underlying game. This
    makes "the adversary makes at most [q] REAL queries" a property of
    the GAME (any [ValidPackage ... A] composed with [COUNT q] only
    ever routes [q] calls to the underlying game, by construction), not
    an extra hypothesis on [A] -- mirrors [PKE/Scheme.v]'s [COUNT]/
    [MI_COUNT] wrapper (itself reused by [MultiInstance.v]/
    [OneToMany.v]), rather than [PRFPRG.v]'s [security_based_on_prf],
    which instead assumes a [q] "exists" for the given adversary as a
    hypothesis. Since a repeat query for an already-seen [ss] costs no
    fresh [prk] sample (see [KDF_mid]/[KDF_bad] above), this bounds the
    number of *fresh Extract samples* by the (coarser, but sufficient)
    bound of [q] real-routed queries.

    Deliberately NOT built via [#assert count < q] (the [PKE/Scheme.v]
    idiom): [#assert b] reduces to [fail] (zero PROBABILITY MASS) when
    [b] is false, so past the [q]-th call the wrapped package would stop
    being LOSSLESS -- fatal for later combining this with up-to-bad
    reasoning ([eq_upto_bad_perf_ind], pkg_upto_bad.v), whose
    [independent_rule]-based coupling genuinely needs both sides to be
    full (mass-1) probability distributions, not just sub-distributions.
    Routing to an independent uniform sample instead keeps [COUNT q]
    lossless UNCONDITIONALLY (for every reachable AND unreachable value
    of [count_loc] alike), so [lossless_valid_adv] (pkg_upto_bad.v) can
    still be established for it with no changes to that shared,
    core-infrastructure file -- and the dummy branch is exactly as
    "independent of everything" as [KDF_ideal]'s own output, so it costs
    no extra advantage beyond the first [q] real queries. *)
  Definition count_loc := mkloc 11 (0 : 'nat).

  Definition COUNT (q : nat) : package DERIVE_export DERIVE_export :=
    [package [fmap count_loc] ;
      #def #[ DERIVE ] ('(ss, info) : 'ss × 'info) : 'out
      {
        #import {sig #[ DERIVE ] : 'ss × 'info → 'out } as derive ;;
        count ← get count_loc ;;
        if count < q then
          #put count_loc := count.+1 ;;
          derive (ss, info)
        else
          y <$ uniform Out_N ;;
          ret y
      }
    ].

  (* --- locations --- *)

  (* Extract's lazily-sampled RO table, shared by [KDF_real] and [KDF_mid]. *)
  Definition extract_loc := mkloc 1 (emptym : chMap 'ss 'prk).

  (* [KDF_ideal]'s table: one independent uniform output per (ss, info). *)
  Definition ideal_loc := mkloc 2 (emptym : chMap ('ss × 'info) 'out).

  (* [KDF_mid]'s table for the idealised Expand step, keyed by [prk]. *)
  Definition mid_loc := mkloc 3 (emptym : chMap ('prk × 'info) 'out).

  (* --- the real construction: Extract (RO) + Expand (real PRF) --- *)

  Definition KDF_real_locs := [fmap extract_loc].

  Definition KDF_real : game DERIVE_export :=
    [package KDF_real_locs ;
      #def #[ DERIVE ] ('(ss, info) : 'ss × 'info) : 'out
      {
        T ← get extract_loc ;;
        prk ← match getm T ss with
        | Some prk => ret prk
        | None =>
            prk <$ uniform PRK_N ;;
            #put extract_loc := setm T ss prk ;;
            ret prk
        end ;;
        ret (PRF info prk)
      }
    ].

  (* --- the ideal functionality: one independent uniform output per query --- *)

  Definition KDF_ideal_locs := [fmap ideal_loc].

  Definition KDF_ideal : game DERIVE_export :=
    [package KDF_ideal_locs ;
      #def #[ DERIVE ] ('(ss, info) : 'ss × 'info) : 'out
      {
        T ← get ideal_loc ;;
        match getm T (ss, info) with
        | Some y => ret y
        | None =>
            y <$ uniform Out_N ;;
            #put ideal_loc := setm T (ss, info) y ;;
            ret y
        end
      }
    ].

  Definition KDF b : game DERIVE_export := if b then KDF_real else KDF_ideal.

  (* --- middle game: real Extract, ideal (per-key) Expand ---

    Same Extract table as [KDF_real], but Expand is replaced by a lazily
    sampled table indexed by (prk, info). If Extract never assigns the
    same [prk] to two different shared secrets, this game and [KDF_ideal]
    are exactly the same distribution (via the bijection ss <-> prk on
    the finitely many shared secrets actually queried). If Extract *does*
    produce such a collision, the two games can diverge, which is exactly
    the birthday event we need to bound.
  *)

  Definition KDF_mid_locs := [fmap extract_loc; mid_loc].

  Definition KDF_mid : game DERIVE_export :=
    [package KDF_mid_locs ;
      #def #[ DERIVE ] ('(ss, info) : 'ss × 'info) : 'out
      {
        T ← get extract_loc ;;
        prk ← match getm T ss with
        | Some prk => ret prk
        | None =>
            prk <$ uniform PRK_N ;;
            #put extract_loc := setm T ss prk ;;
            ret prk
        end ;;
        T2 ← get mid_loc ;;
        match getm T2 (prk, info) with
        | Some y => ret y
        | None =>
            y <$ uniform Out_N ;;
            #put mid_loc := setm T2 (prk, info) y ;;
            ret y
        end
      }
    ].

  (* --- "patched" game: identical to [KDF_ideal], coupled with [KDF_mid]
    up to the birthday collision ---

    The idea (up-to-bad / eager resampling): the *output* of every query is
    always computed exactly as in [KDF_ideal] -- one independent uniform
    sample per (ss, info) pair, via [indep_loc]. Extract's table
    ([extract_loc]) and a set of the [prk]s handed out so far
    ([used_prk_loc]) are carried along purely as *ghost* state, used only to
    flip [bad_loc] the moment Extract assigns a [prk] to a second, different
    shared secret (a birthday collision). None of this ghost state feeds
    back into the actual output, which is exactly what makes
    [KDF_bad_KDF_ideal_equiv] below easy: the ghost computation is dead code
    as far as [indep_loc]/the return value are concerned.

    What makes this game useful (for the still-open step 2b) is a different
    fact, needed to relate it to [KDF_mid]: as long as [bad_loc] has never
    fired, every shared secret seen so far has a *distinct* [prk], so
    [KDF_mid]'s [mid_loc] table (keyed by (prk, info)) and [KDF_bad]'s
    [indep_loc] table (keyed by (ss, info)) agree via the injective
    relabelling ss -> Extract(ss). The moment [bad_loc] fires, that
    injectivity breaks and the two games are allowed to diverge.
  *)

  Definition bad_loc := mkloc 4 (false : bool).
  Definition used_prk_loc := mkloc 5 (emptym : chMap 'prk 'unit).
  Definition indep_loc := mkloc 6 (emptym : chMap ('ss × 'info) 'out).

  Definition KDF_bad_locs :=
    [fmap extract_loc; bad_loc; used_prk_loc; indep_loc].

  Definition KDF_bad : game DERIVE_export :=
    [package KDF_bad_locs ;
      #def #[ DERIVE ] ('(ss, info) : 'ss × 'info) : 'out
      {
        T ← get extract_loc ;;
        (match getm T ss with
         | Some _ => ret tt
         | None =>
             prk <$ uniform PRK_N ;;
             #put extract_loc := setm T ss prk ;;
             Used ← get used_prk_loc ;;
             match getm Used prk with
             | None => #put used_prk_loc := setm Used prk tt ;; ret tt
             | Some _ => #put bad_loc := true ;; ret tt
             end
         end) ;;
        T2 ← get indep_loc ;;
        match getm T2 (ss, info) with
        | Some y => ret y
        | None =>
            y <$ uniform Out_N ;;
            #put indep_loc := setm T2 (ss, info) y ;;
            ret y
        end
      }
    ].

  (* [KDF_bad] and [KDF_ideal] are perfectly indistinguishable: the ghost
    computation (extract_loc / used_prk_loc / bad_loc) never touches
    [indep_loc], so the only thing that matters is that both packages
    compute their output the same way, from a table that starts empty and
    is populated by an independent uniform sample the first time each
    (ss, info) pair is queried. *)
  Definition KDF_bad_ideal_inv : precond :=
    heap_ignore (unionm KDF_bad_locs KDF_ideal_locs) ⋊
    couple_cross indep_loc ideal_loc
      (fun (Ti Td : chMap ('ss × 'info) 'out) => Ti = Td).

  Ltac close_preserve :=
    eapply preserve_update_mem_conj;
    [ ssprove_invariant
    | eapply preserve_update_mem_rel; ssprove_invariant
    ] ; done.

  (* [r_ret]'s postcondition hypothesis packs the base invariant under a
    chain of [rem_lhs]/[rem_rhs] wrappers, one per [get] remembered so far
    on the way to this point -- the exact nesting depth varies by branch,
    so peel wrappers one at a time (via [destruct]'s whnf reduction on
    [⋊], same trick as elsewhere in this file) until what's left matches
    the target invariant exactly, instead of hand-counting brackets. *)
  Ltac extract_base_inv h :=
    first [ exact h | destruct h as [h ?]; extract_base_inv h ].

  (* Like [close_preserve], but for a 3-way [(A ⋊ B) ⋊ C] invariant. *)
  Ltac close_preserve3 :=
    eapply preserve_update_mem_conj;
    [ eapply preserve_update_mem_conj;
      [ ssprove_invariant
      | eapply preserve_update_mem_rel; ssprove_invariant ]
    | eapply preserve_update_mem_rel; ssprove_invariant
    ] ; done.

  (* Like [close_preserve3], but for a 4-way [((A ⋊ B) ⋊ C) ⋊ D] invariant. *)
  Ltac close_preserve4 :=
    eapply preserve_update_mem_conj;
    [ eapply preserve_update_mem_conj;
      [ eapply preserve_update_mem_conj;
        [ ssprove_invariant
        | eapply preserve_update_mem_rel; ssprove_invariant ]
      | eapply preserve_update_mem_rel; ssprove_invariant ]
    | eapply preserve_update_mem_rel; ssprove_invariant
    ] ; done.

  Lemma KDF_bad_KDF_ideal_equiv :
    KDF_bad ≈₀ KDF_ideal.
  Proof.
    apply eq_rel_perf_ind with KDF_bad_ideal_inv.
    1: {
      eapply Invariant_inv_conj.
      - eapply Invariant_heap_ignore. fmap_solve.
      - eapply SemiInvariant_relApp.
        + simpl. repeat split. all: try fmap_solve; try done.
        + done.
    }
    simplify_eq_rel arg.
    destruct arg as [ss info].
    apply r_get_remember_lhs => T.
    destruct (getm T ss) as [prk|] eqn:HT.
    - (* ss already extracted: the ghost branch is just [ret tt] *)
      rewrite HT /=.
      apply r_get_remember_lhs => Tind.
      apply r_get_remember_rhs => Tideal.
      ssprove_rem_rel 0%N => Heq.
      rewrite -Heq.
      destruct (getm Tind (ss, info)) as [y|] eqn:HTi.
      all: rewrite HTi.
      all: try (
        apply r_ret ;
        intros s0 s1 Hpre ; destruct Hpre as [[[Hinv ?] ?] ?] ;
        split ; [ reflexivity | exact Hinv ]
      ).
      all: eapply (r_uniform_bij _ _ _ _ id); [ exists id; done | intro y ].
      all: apply r_put_vs_put.
      all: ssprove_restore_mem; last by apply r_ret.
      all: close_preserve.
    - (* ss is new: sample [prk], update the ghost state, reach the same tail *)
      rewrite HT /=.
      apply r_const_sample_L. 1: exact _.
      intro prk'.
      apply r_put_lhs.
      (* flush this put back down to a clean [KDF_bad_ideal_inv] before the
        next [get] -- interleaving gets between un-flushed puts confuses
        [ssprove_restore_mem]'s automatic folding. *)
      ssprove_restore_mem; [ close_preserve | ].
      apply r_get_remember_lhs => Used.
      destruct (getm Used prk') as [[]|] eqn:HU.
      all: rewrite HU /=.
      all: apply r_put_lhs.
      all: ssprove_restore_mem; [ close_preserve | ].
      all: apply r_get_remember_lhs => Tind.
      all: apply r_get_remember_rhs => Tideal.
      all: ssprove_rem_rel 0%N => Heq.
      all: rewrite -Heq.
      all: destruct (getm Tind (ss, info)) as [y|] eqn:HTi.
      all: rewrite HTi.
      all: try (
        apply r_ret ;
        intros s0 s1 Hpre ; destruct Hpre as [[Hinv ?] ?] ;
        split ; [ reflexivity | exact Hinv ]
      ).
      all: eapply (r_uniform_bij _ _ _ _ id); [ exists id; done | intro y ].
      all: apply r_put_vs_put.
      all: ssprove_restore_mem; last by apply r_ret.
      all: close_preserve.
  Qed.

  (* --- ghost-annotated middle game: [KDF_mid] plus the same
    [bad_loc]/[used_prk_loc] bookkeeping [KDF_bad] carries ---

    [eq_up_to_bad_adversary_link] (pkg_upto_bad.v) needs [bad_loc] to be
    trackable -- and kept in sync by the invariant -- on *both* sides of
    the games it relates. [KDF_mid] itself has no such bookkeeping, so it
    cannot be compared against [KDF_bad] directly via that machinery.
    [KDF_mid'] closes that gap: it is definitionally [KDF_mid] (real
    Extract, ideal per-[prk] Expand via [mid_loc]) with [KDF_bad]'s ghost
    collision-tracking spliced into the very branch that discovers a
    fresh [prk], so the two games maintain [bad_loc]/[used_prk_loc]
    identically. The ghost state is dead code w.r.t. [KDF_mid']'s own
    output, exactly as it is for [KDF_bad] w.r.t. [indep_loc] -- which is
    what makes [KDF_mid_KDF_mid'_equiv] below provable with no
    probability reasoning, mirroring [KDF_real_KDF_hyb0_equiv]'s style. *)

  Definition KDF_mid'_locs :=
    [fmap extract_loc; mid_loc; bad_loc; used_prk_loc].

  Definition KDF_mid' : game DERIVE_export :=
    [package KDF_mid'_locs ;
      #def #[ DERIVE ] ('(ss, info) : 'ss × 'info) : 'out
      {
        T ← get extract_loc ;;
        prk ← match getm T ss with
        | Some prk => ret prk
        | None =>
            prk <$ uniform PRK_N ;;
            #put extract_loc := setm T ss prk ;;
            Used ← get used_prk_loc ;;
            match getm Used prk with
            | None => #put used_prk_loc := setm Used prk tt ;; ret prk
            | Some _ => #put bad_loc := true ;; ret prk
            end
        end ;;
        T2 ← get mid_loc ;;
        match getm T2 (prk, info) with
        | Some y => ret y
        | None =>
            y <$ uniform Out_N ;;
            #put mid_loc := setm T2 (prk, info) y ;;
            ret y
        end
      }
    ].

  Lemma KDF_mid_KDF_mid'_equiv :
    KDF_mid ≈₀ KDF_mid'.
  Proof.
    apply eq_rel_perf_ind_ignore with [fmap bad_loc; used_prk_loc].
    1: fmap_solve.
    simplify_eq_rel arg.
    destruct arg as [ss info].
    apply: r_get_vs_get_remember => T.
    destruct (getm T ss) as [prk|] eqn:HT.
    - (* [ss] already extracted: identical on both sides, no ghost update *)
      rewrite HT /=.
      apply: r_get_vs_get_remember => T2.
      destruct (getm T2 (prk, info)) as [y|] eqn:HT2.
      + rewrite HT2 /=.
        apply: r_ret => s0 s1 h.
        split; [ reflexivity | extract_base_inv h ].
      + rewrite HT2 /=.
        apply: r_uniform_bij => [|y]. 1: exists id; done.
        apply: r_put_vs_put.
        ssprove_restore_mem; last by apply: r_ret.
        by ssprove_invariant.
    - (* [ss] is new: sample the same [prk] on both sides; the RHS alone
        also updates the ghost [used_prk_loc]/[bad_loc] bookkeeping,
        which is ignored by the invariant. *)
      rewrite HT /=.
      apply: r_uniform_bij => [|prk']. 1: exists id; done.
      apply: r_put_vs_put.
      ssprove_restore_mem; [ by ssprove_invariant | ].
      apply: r_get_remember_rhs => Used.
      destruct (getm Used prk') as [[]|] eqn:HU.
      all: rewrite HU /=.
      all: apply: r_put_rhs.
      all: ssprove_restore_mem; [ by ssprove_invariant | ].
      all: apply: r_get_vs_get_remember => T2.
      all: destruct (getm T2 (prk', info)) as [y|] eqn:HT2.
      all: rewrite HT2 /=.
      all: try (
        apply: r_ret => s0 s1 h ;
        split ; [ reflexivity | extract_base_inv h ]
      ).
      all: apply: r_uniform_bij => [|y]; [ exists id; done | ].
      all: apply: r_put_vs_put.
      all: ssprove_restore_mem; last by apply: r_ret.
      all: by ssprove_invariant.
  Qed.

  (* --- relating [KDF_mid'] and [KDF_bad] via up-to-bad reasoning ---

    Both games now maintain [extract_loc]/[used_prk_loc]/[bad_loc]
    identically (the ghost-tracking fragment is literally the same
    code). [mid_bad_match] is the relabelling fact making [mid_loc]
    (keyed by [prk]) and [indep_loc] (keyed by [ss]) agree as long as
    Extract has never assigned the same [prk] to two different [ss]'s,
    i.e. as long as [bad_loc] is still [false]: every [ss] with a
    known [prk] must see the same table entry on both sides. The
    moment [bad_loc] fires this guarantee is dropped, which is exactly
    why [KDF_mid'_bad_inv]'s relational conjunct is gated on
    [b = false] -- required so that [HbadI] below (the invariant must
    hold whenever *both* sides already have [bad_loc = true], with no
    other correlation assumed) is satisfiable. *)

  Definition mid_bad_match
    (T : chMap 'ss 'prk) (Tm : chMap ('prk × 'info) 'out) (Ti : chMap ('ss × 'info) 'out) : Prop :=
    ∀ ss info,
      match getm T ss with
      | Some prk => getm Tm (prk, info) = getm Ti (ss, info)
      | None => True
      end.

  (* [used_prk_loc]'s domain is exactly [extract_loc]'s range -- an
    invariant each game maintains of its OWN ghost bookkeeping alone
    (every fresh [prk] sample immediately registers itself), needed
    here to know a freshly-sampled [prk] with [Used prk = None] can't
    collide with any [ss'] already extracted, which is what lets
    [mid_bad_match] survive extending both tables. *)
  Definition used_prk_correspondence
    (T : chMap 'ss 'prk) (U : chMap 'prk 'unit) : Prop :=
    ∀ prk, getm U prk = Some tt ↔ (∃ ss, getm T ss = Some prk).

  (* [extract_loc] is injective on its domain -- a consequence of the
    games' own semantics (bad_loc only ever fires on a genuine
    collision) that isn't implied by [used_prk_correspondence] alone,
    but is needed to show [mid_bad_match] survives extending
    [mid_loc]/[indep_loc] at a *specific* (already-extracted) [ss]:
    without it, some OTHER [ss'] could share the same [prk] and see
    its own [mid_loc] entry silently change. *)
  Definition extract_injective (T : chMap 'ss 'prk) : Prop :=
    ∀ ss1 ss2 prk, getm T ss1 = Some prk → getm T ss2 = Some prk → ss1 = ss2.

  (* [mid_loc]/[indep_loc] only ever gain an entry keyed at a [prk]/[ss]
    that has already been extracted -- a consequence of the games' own
    semantics ([mid_loc]/[indep_loc] are only written to after [prk]/[ss]
    is already determined) needed to know a FRESHLY-sampled [prk] (not
    yet in [extract_loc]'s range) can't already have a [mid_loc] entry,
    which is what lets [mid_bad_match] extend to a brand new [ss]. *)
  Definition mid_loc_fresh
    (T : chMap 'ss 'prk) (Tm : chMap ('prk × 'info) 'out) : Prop :=
    ∀ prk info, getm Tm (prk, info) <> None → ∃ ss, getm T ss = Some prk.

  Definition indep_loc_fresh
    (T : chMap 'ss 'prk) (Ti : chMap ('ss × 'info) 'out) : Prop :=
    ∀ ss info, getm Ti (ss, info) <> None → getm T ss <> None.

  Definition KDF_mid'_bad_locs := unionm KDF_mid'_locs KDF_bad_locs.

  Definition KDF_mid'_bad_inv : precond :=
    heap_ignore KDF_mid'_bad_locs ⋊
    syncs bad_loc ⋊
    rel_app [:: (lhs, bad_loc); (lhs, extract_loc); (lhs, mid_loc); (lhs, used_prk_loc);
                (rhs, extract_loc); (rhs, used_prk_loc); (rhs, indep_loc)]
      (fun b T Tm U T' U' Ti =>
         b = false →
         T = T' ∧ U = U' ∧ mid_bad_match T Tm Ti ∧ used_prk_correspondence T U
         ∧ extract_injective T ∧ mid_loc_fresh T Tm ∧ indep_loc_fresh T Ti).

  Lemma KDF_mid'_bad_Invariant : Invariant KDF_mid'_locs KDF_bad_locs KDF_mid'_bad_inv.
  Proof.
    eapply Invariant_inv_conj.
    - eapply Invariant_inv_conj.
      + eapply Invariant_heap_ignore. fmap_solve.
      + eapply SemiInvariant_relApp.
        * simpl. repeat split. all: try fmap_solve; try done.
        * done.
    - eapply SemiInvariant_relApp.
      + simpl. repeat split. all: try fmap_solve; try done.
      + simpl. move=> _. repeat split=>//.
        move=> [ss Hss]. move: Hss. by rewrite /heap_init.
  Qed.

  (* [bad_id := 4] throughout: [bad_loc] (this section) and
    [pkg_upto_bad.bad_loc 4] are definitionally the same location. *)

  Lemma KDF_mid'_bad_preserved : bad_preserved DERIVE_export 4 KDF_mid'.
  Proof.
    move=> id S T x h has Hb.
    fmap_invert has.
    simplify_linking.
    case: x => ss info /=.
    have Hlv : lossless_valid KDF_mid'_locs
      (T ← get extract_loc ;;
        prk ← match T ss with
              | Some prk => ret prk
              | None =>
                  prk ← sample uniform PRK_N ;;
                  #put extract_loc := setm T ss prk ;;
                  Used ← get used_prk_loc ;;
                  match Used prk with
                  | Some _ => #put bad_loc := true ;; ret prk
                  | None => #put used_prk_loc := setm Used prk tt ;; ret prk
                  end
              end ;;
        T2 ← get mid_loc ;;
        match T2 (prk, info) with
        | Some y => ret y
        | None =>
            y ← sample uniform Out_N ;;
            #put mid_loc := setm T2 (prk, info) y ;;
            ret y
        end).
    - apply: lv_getr; [fmap_solve | move=> T; case: (T ss) => [prk|] ].
      + apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (prk, info)) => [y|] ].
        * exact: lv_ret.
        * apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
      + apply: lv_sampler => prk. apply: lv_putr; [fmap_solve |
          apply: lv_getr; [fmap_solve | move=> Used; case: (Used prk) => [[]|] ] ].
        * apply: lv_putr; [fmap_solve |
            apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (prk, info)) => [y|] ] ].
          -- exact: lv_ret.
          -- apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
        * apply: lv_putr; [fmap_solve |
            apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (prk, info)) => [y|] ] ].
          -- exact: lv_ret.
          -- apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
    - have Hm : bad_loc_monotone 4
        (T ← get extract_loc ;;
          prk ← match T ss with
                | Some prk => ret prk
                | None =>
                    prk ← sample uniform PRK_N ;;
                    #put extract_loc := setm T ss prk ;;
                    Used ← get used_prk_loc ;;
                    match Used prk with
                    | Some _ => #put bad_loc := true ;; ret prk
                    | None => #put used_prk_loc := setm Used prk tt ;; ret prk
                    end
                end ;;
          T2 ← get mid_loc ;;
          match T2 (prk, info) with
          | Some y => ret y
          | None =>
              y ← sample uniform Out_N ;;
              #put mid_loc := setm T2 (prk, info) y ;;
              ret y
          end).
      + apply: blm_getr => T. case: (T ss) => [prk|].
        * apply: blm_getr => T2. case: (T2 (prk, info)) => [y|].
          -- exact: blm_ret.
          -- apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
        * apply: blm_sampler => prk. apply: blm_putr_other; [done |
            apply: blm_getr => Used; case: (Used prk) => [[]|] ].
          -- apply: blm_putr_bad.
             apply: blm_getr => T2; case: (T2 (prk, info)) => [y|].
             ++ exact: blm_ret.
             ++ apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
          -- apply: blm_putr_other; [done |
               apply: blm_getr => T2; case: (T2 (prk, info)) => [y|] ].
             ++ exact: blm_ret.
             ++ apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
      + exact: (Pr_code_lossless_bad KDF_mid'_locs _ Hlv Hm h Hb).
  Qed.

  Lemma KDF_bad_bad_preserved : bad_preserved DERIVE_export 4 KDF_bad.
  Proof.
    move=> id S T x h has Hb.
    fmap_invert has.
    simplify_linking.
    case: x => ss info /=.
    have Hlv : lossless_valid KDF_bad_locs
      (T ← get extract_loc ;;
       match T ss with
       | Some _ => ret tt
       | None =>
           prk ← sample uniform PRK_N ;;
           #put extract_loc := setm T ss prk ;;
           Used ← get used_prk_loc ;;
           match Used prk with
           | Some _ => #put bad_loc := true ;; ret tt
           | None => #put used_prk_loc := setm Used prk tt ;; ret tt
           end
       end ;;
       T2 ← get indep_loc ;;
       match T2 (ss, info) with
       | Some y => ret y
       | None =>
           y ← sample uniform Out_N ;;
           #put indep_loc := setm T2 (ss, info) y ;;
           ret y
       end).
    - apply: lv_getr; [fmap_solve | move=> T; case: (T ss) => [prk0|] ].
      + apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (ss, info)) => [y|] ].
        * exact: lv_ret.
        * apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
      + apply: lv_sampler => prk. apply: lv_putr; [fmap_solve |
          apply: lv_getr; [fmap_solve | move=> Used; case: (Used prk) => [[]|] ] ].
        * apply: lv_putr; [fmap_solve |
            apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (ss, info)) => [y|] ] ].
          -- exact: lv_ret.
          -- apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
        * apply: lv_putr; [fmap_solve |
            apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (ss, info)) => [y|] ] ].
          -- exact: lv_ret.
          -- apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
    - have Hm : bad_loc_monotone 4
        (T ← get extract_loc ;;
         match T ss with
         | Some _ => ret tt
         | None =>
             prk ← sample uniform PRK_N ;;
             #put extract_loc := setm T ss prk ;;
             Used ← get used_prk_loc ;;
             match Used prk with
             | Some _ => #put bad_loc := true ;; ret tt
             | None => #put used_prk_loc := setm Used prk tt ;; ret tt
             end
         end ;;
         T2 ← get indep_loc ;;
         match T2 (ss, info) with
         | Some y => ret y
         | None =>
             y ← sample uniform Out_N ;;
             #put indep_loc := setm T2 (ss, info) y ;;
             ret y
         end).
      + apply: blm_getr => T. case: (T ss) => [prk0|].
        * apply: blm_getr => T2. case: (T2 (ss, info)) => [y|].
          -- exact: blm_ret.
          -- apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
        * apply: blm_sampler => prk. apply: blm_putr_other; [done |
            apply: blm_getr => Used; case: (Used prk) => [[]|] ].
          -- apply: blm_putr_bad.
             apply: blm_getr => T2; case: (T2 (ss, info)) => [y|].
             ++ exact: blm_ret.
             ++ apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
          -- apply: blm_putr_other; [done |
               apply: blm_getr => T2; case: (T2 (ss, info)) => [y|] ].
             ++ exact: blm_ret.
             ++ apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
      + exact: (Pr_code_lossless_bad KDF_bad_locs _ Hlv Hm h Hb).
  Qed.

  Lemma KDF_mid'_KDF_bad_eq_up_to_bad :
    eq_up_to_bad DERIVE_export KDF_mid'_bad_inv 4 KDF_mid' KDF_bad.
  Proof.
    move=> id S T x hasE.
    fmap_invert hasE.
    simplify_linking.
    case: x => ss info /=.
    apply: rpre_hypothesis_rule => s0 s1 Hpre.
    case: (boolP (get_heap s0 bad_loc)) => Hbad.
    { have Hlv1 : lossless_valid KDF_mid'_locs
        (T ← get extract_loc ;;
          prk ← match T ss with
                | Some prk => ret prk
                | None =>
                    prk ← sample uniform PRK_N ;;
                    #put extract_loc := setm T ss prk ;;
                    Used ← get used_prk_loc ;;
                    match Used prk with
                    | Some _ => #put bad_loc := true ;; ret prk
                    | None => #put used_prk_loc := setm Used prk tt ;; ret prk
                    end
                end ;;
          T2 ← get mid_loc ;;
          match T2 (prk, info) with
          | Some y => ret y
          | None =>
              y ← sample uniform Out_N ;;
              #put mid_loc := setm T2 (prk, info) y ;;
              ret y
          end).
      { apply: lv_getr; [fmap_solve | move=> T; case: (T ss) => [prk|] ].
        { apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (prk, info)) => [y|] ].
          { exact: lv_ret. }
          { apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret]. } }
        { apply: lv_sampler => prk. apply: lv_putr; [fmap_solve |
            apply: lv_getr; [fmap_solve | move=> Used; case: (Used prk) => [[]|] ] ].
          { apply: lv_putr; [fmap_solve |
              apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (prk, info)) => [y|] ] ].
            { exact: lv_ret. }
            { apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret]. } }
          { apply: lv_putr; [fmap_solve |
              apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (prk, info)) => [y|] ] ].
            { exact: lv_ret. }
            { apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret]. } } } }
      have Hm1 : bad_loc_monotone 4
        (T ← get extract_loc ;;
          prk ← match T ss with
                | Some prk => ret prk
                | None =>
                    prk ← sample uniform PRK_N ;;
                    #put extract_loc := setm T ss prk ;;
                    Used ← get used_prk_loc ;;
                    match Used prk with
                    | Some _ => #put bad_loc := true ;; ret prk
                    | None => #put used_prk_loc := setm Used prk tt ;; ret prk
                    end
                end ;;
          T2 ← get mid_loc ;;
          match T2 (prk, info) with
          | Some y => ret y
          | None =>
              y ← sample uniform Out_N ;;
              #put mid_loc := setm T2 (prk, info) y ;;
              ret y
          end).
      { apply: blm_getr => T. case: (T ss) => [prk|].
        { apply: blm_getr => T2. case: (T2 (prk, info)) => [y|].
          { exact: blm_ret. }
          { apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret]. } }
        { apply: blm_sampler => prk. apply: blm_putr_other; [done |
            apply: blm_getr => Used; case: (Used prk) => [[]|] ].
          { apply: blm_putr_bad.
            apply: blm_getr => T2; case: (T2 (prk, info)) => [y|].
            { exact: blm_ret. }
            { apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret]. } }
          { apply: blm_putr_other; [done |
              apply: blm_getr => T2; case: (T2 (prk, info)) => [y|] ].
            { exact: blm_ret. }
            { apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret]. } } } }
      have Hlv2 : lossless_valid KDF_bad_locs
        (T ← get extract_loc ;;
         match T ss with
         | Some _ => ret tt
         | None =>
             prk ← sample uniform PRK_N ;;
             #put extract_loc := setm T ss prk ;;
             Used ← get used_prk_loc ;;
             match Used prk with
             | Some _ => #put bad_loc := true ;; ret tt
             | None => #put used_prk_loc := setm Used prk tt ;; ret tt
             end
         end ;;
         T2 ← get indep_loc ;;
         match T2 (ss, info) with
         | Some y => ret y
         | None =>
             y ← sample uniform Out_N ;;
             #put indep_loc := setm T2 (ss, info) y ;;
             ret y
         end).
      { apply: lv_getr; [fmap_solve | move=> T; case: (T ss) => [prk0|] ].
        { apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (ss, info)) => [y|] ].
          { exact: lv_ret. }
          { apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret]. } }
        { apply: lv_sampler => prk. apply: lv_putr; [fmap_solve |
            apply: lv_getr; [fmap_solve | move=> Used; case: (Used prk) => [[]|] ] ].
          { apply: lv_putr; [fmap_solve |
              apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (ss, info)) => [y|] ] ].
            { exact: lv_ret. }
            { apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret]. } }
          { apply: lv_putr; [fmap_solve |
              apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (ss, info)) => [y|] ] ].
            { exact: lv_ret. }
            { apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret]. } } } }
      have Hm2 : bad_loc_monotone 4
        (T ← get extract_loc ;;
         match T ss with
         | Some _ => ret tt
         | None =>
             prk ← sample uniform PRK_N ;;
             #put extract_loc := setm T ss prk ;;
             Used ← get used_prk_loc ;;
             match Used prk with
             | Some _ => #put bad_loc := true ;; ret tt
             | None => #put used_prk_loc := setm Used prk tt ;; ret tt
             end
         end ;;
         T2 ← get indep_loc ;;
         match T2 (ss, info) with
         | Some y => ret y
         | None =>
             y ← sample uniform Out_N ;;
             #put indep_loc := setm T2 (ss, info) y ;;
             ret y
         end).
      { apply: blm_getr => T. case: (T ss) => [prk0|].
        { apply: blm_getr => T2. case: (T2 (ss, info)) => [y|].
          { exact: blm_ret. }
          { apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret]. } }
        { apply: blm_sampler => prk. apply: blm_putr_other; [done |
            apply: blm_getr => Used; case: (Used prk) => [[]|] ].
          { apply: blm_putr_bad.
            apply: blm_getr => T2; case: (T2 (ss, info)) => [y|].
            { exact: blm_ret. }
            { apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret]. } }
          { apply: blm_putr_other; [done |
              apply: blm_getr => T2; case: (T2 (ss, info)) => [y|] ].
            { exact: blm_ret. }
            { apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret]. } } } }
      apply: from_sem_jdg.
      apply: independent_rule.
      { move=> t0 t1 [/= -> _]. rewrite -Pr_code_theta_bridge. exact: (Pr_code_lossless KDF_mid'_locs _ Hlv1 s0). }
      { move=> t0 t1 [/= _ ->]. rewrite -Pr_code_theta_bridge. exact: (Pr_code_lossless KDF_bad_locs _ Hlv2 s1). }
      move=> t0 t1 [/= -> ->] a1 h1' a2 h2' Hgt1 Hgt2.
      have Hgt1' : (0 < Pr_code (T ← get extract_loc ;;
          prk ← match T ss with
                | Some prk => ret prk
                | None =>
                    prk ← sample uniform PRK_N ;;
                    #put extract_loc := setm T ss prk ;;
                    Used ← get used_prk_loc ;;
                    match Used prk with
                    | Some _ => #put bad_loc := true ;; ret prk
                    | None => #put used_prk_loc := setm Used prk tt ;; ret prk
                    end
                end ;;
          T2 ← get mid_loc ;;
          match T2 (prk, info) with
          | Some y => ret y
          | None =>
              y ← sample uniform Out_N ;;
              #put mid_loc := setm T2 (prk, info) y ;;
              ret y
          end) s0 (a1,h1'))%R.
      { rewrite Pr_code_theta_bridge. exact: Hgt1. }
      have Hgt2' : (0 < Pr_code (T ← get extract_loc ;;
         match T ss with
         | Some _ => ret tt
         | None =>
             prk ← sample uniform PRK_N ;;
             #put extract_loc := setm T ss prk ;;
             Used ← get used_prk_loc ;;
             match Used prk with
             | Some _ => #put bad_loc := true ;; ret tt
             | None => #put used_prk_loc := setm Used prk tt ;; ret tt
             end
         end ;;
         T2 ← get indep_loc ;;
         match T2 (ss, info) with
         | Some y => ret y
         | None =>
             y ← sample uniform Out_N ;;
             #put indep_loc := setm T2 (ss, info) y ;;
             ret y
         end) s1 (a2,h2'))%R.
      { rewrite Pr_code_theta_bridge. exact: Hgt2. }
      have Hbad_s1 : get_heap s1 bad_loc = true.
      { have Hsync0 : get_heap s0 bad_loc = get_heap s1 bad_loc.
        { move: (proj2 (proj1 Hpre)). rewrite /rel_app /get_side /=. done. }
        rewrite -Hsync0. exact: Hbad. }
      have Hbad1' : get_heap h1' bad_loc = true.
      { exact: (proj2 (Pr_code_lossless_bad KDF_mid'_locs _ Hlv1 Hm1 s0 Hbad) a1 h1' Hgt1'). }
      have Hbad2' : get_heap h2' bad_loc = true.
      { exact: (proj2 (Pr_code_lossless_bad KDF_bad_locs _ Hlv2 Hm2 s1 Hbad_s1) a2 h2' Hgt2'). }
      split.
      { split.
        { split.
          { move=> l Hnotin.
            have Hnotin1 : l.1 \notin domm KDF_mid'_locs.
            { move: Hnotin. rewrite /KDF_mid'_bad_locs domm_union in_fsetU negb_or => /andP[] //. }
            have Hnotin2 : l.1 \notin domm KDF_bad_locs.
            { move: Hnotin. rewrite /KDF_mid'_bad_locs domm_union in_fsetU negb_or => /andP[] //. }
            rewrite (theta_frame KDF_mid'_locs _ Hlv1 s0 l Hnotin1 a1 h1' Hgt1).
            rewrite (theta_frame KDF_bad_locs _ Hlv2 s1 l Hnotin2 a2 h2' Hgt2).
            exact: (proj1 (proj1 Hpre) l Hnotin). }
          rewrite /rel_app /get_side /=. by rewrite Hbad1' Hbad2'. }
        rewrite /rel_app /get_side /=. move=> Hf. rewrite Hbad1' in Hf. discriminate. }
      rewrite /rel_app /get_side /=. move=> Hf. rewrite Hbad1' in Hf. discriminate. }
    move: Hbad => /negbTE Hbad.
    have Hg := (proj2 Hpre) Hbad.
    destruct Hg as [HT [HU [Hmid [Hcorr [Hinj [Hmf Hif]]]]]].
    simpl in HT, HU, Hmid, Hcorr, Hinj, Hmf, Hif.
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(s2,s3) => s2=s0 /\ s3=s1).
    2: { move=> t0 t1 [/= -> ->]. done. }
    eapply (r_get_remember_lhs extract_loc _ _ (fun '(s2,s3) => s2=s0 /\ s3=s1)).
    move=> T.
    eapply (r_get_remember_rhs extract_loc _ _ ((fun '(s2,s3) => s2=s0 /\ s3=s1) ⋊ rem_lhs extract_loc T)).
    move=> T'.
    apply: rpre_hypothesis_rule => s2 s3 Hp.
    case: Hp => [[[Heq2 Heq3] HeqT] HeqT'].
    subst s2 s3.
    move: HeqT HeqT'. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=. move=> HeqT HeqT'.
    have HTT' : T = T' := etrans (etrans (esym HeqT) HT) HeqT'.
    subst T'.
    rewrite -HTT'.
    destruct (getm T ss) as [prk|] eqn:HTss.
    { rewrite HTss /=.
      eapply rpre_weaken_rule.
      1: instantiate (1 := fun '(s2,s3) => s2=s0 /\ s3=s1).
      2: { move=> t0 t1 [/= -> ->]. done. }
      eapply (r_get_remember_lhs mid_loc _ _ (fun '(s2,s3) => s2=s0 /\ s3=s1)).
      move=> Tm.
      eapply (r_get_remember_rhs indep_loc _ _ ((fun '(s2,s3) => s2=s0 /\ s3=s1) ⋊ rem_lhs mid_loc Tm)).
      move=> Ti.
      apply: rpre_hypothesis_rule => s2 s3 Hp.
      case: Hp => [[[Heq2 Heq3] HeqTm] HeqTi].
      move: HeqTm HeqTi. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=. move=> HeqTm HeqTi.
      subst s2 s3.
      have Hmatch : getm Tm (prk, info) = getm Ti (ss, info).
      { move: (Hmid ss info). rewrite HeqT HTss HeqTm HeqTi. done. }
      have Hig : heap_ignore KDF_mid'_bad_locs (s0,s1) := proj1 (proj1 Hpre).
      have Hsync : get_heap s0 bad_loc = get_heap s1 bad_loc.
      { move: (proj2 (proj1 Hpre)). rewrite /rel_app /get_side /=. done. }
      destruct (getm Tm (prk, info)) as [y|] eqn:HTm.
      { rewrite HTm -Hmatch.
        apply: r_ret.
        move=> t0 t1 [/= -> ->].
        split; [exact: Hpre | done]. }
      { rewrite HTm -Hmatch.
        eapply (r_uniform_bij _ _ _ _ id). 1: exists id; done.
        move=> y.
        eapply rpre_weaken_rule.
        1: instantiate (1 := fun '(t0,t1) => t0=s0 /\ t1=s1).
        2: { move=> t0 t1 [/= -> ->]. done. }
        apply: (r_put_vs_put mid_loc (setm Tm (prk, info) y) indep_loc (setm Ti (ss, info) y) _ _
          (fun '(t0,t1) => t0=s0 /\ t1=s1)
          (fun '(b0,s0') '(b1,s1') => KDF_mid'_bad_inv (s0',s1') /\ (get_heap s0' (pkg_upto_bad.bad_loc 4) = false -> b0=b1))).
        apply: r_ret.
        move=> t0 t1 [s1'' [[s0'' [[Heq0 Heq1] ->]] ->]].
        subst s0'' s1''.
        split; [ | done].
        rewrite HeqT in Hmid Hcorr Hinj Hmf Hif.
        split.
        { split.
          { move=> l Hnotin.
            have Hne1 : l.1 != mid_loc.1.
            { apply/eqP => Heq. move: Hnotin => /negP; apply.
              have Hmid_in : mid_loc.1 \in domm KDF_mid'_bad_locs.
              { apply: fhas_in. fmap_solve. }
              rewrite Heq. exact: Hmid_in. }
            have Hne2 : l.1 != indep_loc.1.
            { apply/eqP => Heq. move: Hnotin => /negP; apply.
              have Hindep_in : indep_loc.1 \in domm KDF_mid'_bad_locs.
              { apply: fhas_in. fmap_solve. }
              rewrite Heq. exact: Hindep_in. }
            rewrite (get_set_heap_neq _ _ _ _ Hne1) (get_set_heap_neq _ _ _ _ Hne2).
            exact: (Hig l Hnotin). }
          { rewrite /rel_app /get_side /=.
            rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != mid_loc.1)).
            rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != indep_loc.1)).
            exact: Hsync. } }
        rewrite /rel_app /get_side /=. move=> _.
        rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != mid_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != indep_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != mid_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != indep_loc.1)).
        rewrite HeqT -HTT' HU.
        apply: conj; [done | ].
        apply: conj; [done | ].
        apply: conj.
        { move=> ss0 info0.
          case: (eqVneq ss0 ss) => [-> | Hne].
          { rewrite HTss get_set_heap_eq get_set_heap_eq !setmE.
            have Heq1' : ((prk,info0) == (prk,info)) = (info0 == info) by rewrite xpair_eqE eqxx.
            have Heq2' : ((ss,info0) == (ss,info)) = (info0 == info) by rewrite xpair_eqE eqxx.
            rewrite Heq1' Heq2'.
            case: ifP => Hcond.
            { reflexivity. }
            { move: (Hmid ss info0). rewrite HTss -HeqTm -HeqTi. done. } }
          { case HTss0 : (T ss0) => [prk0|] //.
            have Hneprk : prk0 != prk.
            { apply/eqP => Heqp. subst prk0. move/eqP: Hne => Hne'. apply: Hne'. exact: (Hinj ss0 ss prk HTss0 HTss). }
            rewrite get_set_heap_eq get_set_heap_eq !setmE.
            have Heq1' : ((prk0,info0) == (prk,info)) = false.
            { apply/negP => /eqP [] Heqp _. move: Hneprk => /eqP; apply. exact: Heqp. }
            have Heq2' : ((ss0,info0) == (ss,info)) = false.
            { apply/negP => /eqP [] Heqs _. move: Hne => /eqP; apply. exact: Heqs. }
            rewrite Heq1' Heq2'.
            move: (Hmid ss0 info0). rewrite HTss0 -HeqTm -HeqTi. done. } }
        apply: conj; [rewrite -HU; exact: Hcorr | ].
        apply: conj; [exact: Hinj | ].
        split.
        { move=> prk' info' Hne0.
          case: (eqVneq (prk',info') (prk,info)) => [Heqp | Hneqp].
          { exists ss. rewrite HTss.
            have Heqp' : prk' = prk := f_equal fst Heqp.
            rewrite Heqp'. reflexivity. }
          { apply: (Hmf prk' info').
            move: Hne0. rewrite get_set_heap_eq setmE.
            have -> : ((prk',info') == (prk,info)) = false by exact: negbTE.
            rewrite HeqTm. done. } }
        move=> ss' info' Hne0.
        case: (eqVneq (ss',info') (ss,info)) => [Heqs | Hneqs].
        { have Heqs' : ss' = ss := f_equal fst Heqs.
          rewrite Heqs' HTss. discriminate. }
        apply: (Hif ss' info').
        move: Hne0. rewrite get_set_heap_eq setmE.
        have -> : ((ss',info') == (ss,info)) = false by exact: negbTE.
        rewrite HeqTi. done. } }
    rewrite HTss /=.
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(s2,s3) => s2=s0 /\ s3=s1).
    2: { move=> t0 t1 [/= -> ->]. done. }
    eapply (r_uniform_bij _ _ _ _ id). 1: exists id; done.
    move=> prk0.
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(s2,s3) => s2=s0 /\ s3=s1).
    2: { move=> t0 t1 [/= -> ->]. done. }
    apply: (r_put_vs_put extract_loc (setm T ss prk0) extract_loc (setm T ss prk0) _ _
      (fun '(t0,t1) => t0=s0 /\ t1=s1)
      (fun '(b0,s0') '(b1,s1') => KDF_mid'_bad_inv (s0',s1') /\ (get_heap s0' (pkg_upto_bad.bad_loc 4) = false -> b0=b1))).
    apply: rpre_hypothesis_rule => s4 s5 Hp.
    move: Hp => [s5'' [[s4'' [[Heq4 Heq5] ->]] ->]].
    subst s4'' s5''.
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(t0,t1) => t0 = set_heap s0 extract_loc (setm T ss prk0) /\ t1 = set_heap s1 extract_loc (setm T ss prk0)).
    2: { move=> t0 t1 [/= -> ->]. done. }
    eapply (r_get_remember_lhs used_prk_loc _ _ (fun '(t0,t1) => t0 = set_heap s0 extract_loc (setm T ss prk0) /\ t1 = set_heap s1 extract_loc (setm T ss prk0))).
    move=> Used.
    eapply (r_get_remember_rhs used_prk_loc _ _ ((fun '(t0,t1) => t0 = set_heap s0 extract_loc (setm T ss prk0) /\ t1 = set_heap s1 extract_loc (setm T ss prk0)) ⋊ rem_lhs used_prk_loc Used)).
    move=> Used'.
    apply: rpre_hypothesis_rule => s6 s7 Hp.
    case: Hp => [[[Heq6 Heq7] HeqU] HeqU'].
    move: HeqU HeqU'. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=. move=> HeqU HeqU'.
    subst s6 s7.
    rewrite (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != extract_loc.1)) in HeqU.
    rewrite (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != extract_loc.1)) in HeqU'.
    have HUU' : Used = Used'.
    { rewrite -HeqU -HeqU'. exact: HU. }
    subst Used.
    case E: (get_heap s1 used_prk_loc prk0) => [[]|].
    { rewrite HUU' -HeqU' E.
      simpl.
      eapply rpre_weaken_rule.
      1: instantiate (1 := fun '(t0,t1) => t0 = set_heap s0 extract_loc (setm T ss prk0) /\ t1 = set_heap s1 extract_loc (setm T ss prk0)).
      2: { move=> t0 t1 [/= -> ->]. done. }
      apply: (r_put_vs_put bad_loc true bad_loc true _ _
        (fun '(t0,t1) => t0 = set_heap s0 extract_loc (setm T ss prk0) /\ t1 = set_heap s1 extract_loc (setm T ss prk0))
        (fun '(b0,s0') '(b1,s1') => KDF_mid'_bad_inv (s0',s1') /\ (get_heap s0' (pkg_upto_bad.bad_loc 4) = false -> b0=b1))).
      apply: rpre_hypothesis_rule => s8 s9 Hp2.
      move: Hp2 => [s9'' [[s8'' [[Heq8 Heq9] ->]] ->]].
      subst s8'' s9''.
      have Hbada : get_heap (set_heap (set_heap s0 extract_loc (setm T ss prk0)) bad_loc true) bad_loc = true.
      { exact: get_set_heap_eq. }
      have Hbadb : get_heap (set_heap (set_heap s1 extract_loc (setm T ss prk0)) bad_loc true) bad_loc = true.
      { exact: get_set_heap_eq. }
      apply: from_sem_jdg.
      apply: independent_rule.
      { move=> t0 t1 [/= -> _].
        rewrite -Pr_code_theta_bridge.
        apply: (Pr_code_lossless KDF_mid'_locs _ _ _).
        case: (get_heap (set_heap (set_heap s0 extract_loc (setm T ss prk0)) bad_loc true) mid_loc (prk0, info)) => [y|].
        { exact: lv_ret. }
        { apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret]. } }
      { move=> t0 t1 [/= _ ->].
        rewrite -Pr_code_theta_bridge.
        apply: (Pr_code_lossless KDF_bad_locs _ _ _).
        case: (get_heap (set_heap (set_heap s1 extract_loc (setm T ss prk0)) bad_loc true) indep_loc (ss, info)) => [y|].
        { exact: lv_ret. }
        { apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret]. } }
      have Hlv1'' : lossless_valid KDF_mid'_locs
        (T2 ← get mid_loc ;;
         match T2 (prk0, info) with
         | Some y => ret y
         | None =>
             y ← sample uniform Out_N ;;
             #put mid_loc := setm T2 (prk0, info) y ;;
             ret y
         end).
      { apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (prk0, info)) => [y|] ].
        { exact: lv_ret. }
        { apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret]. } }
      have Hlv2'' : lossless_valid KDF_bad_locs
        (T2 ← get indep_loc ;;
         match T2 (ss, info) with
         | Some y => ret y
         | None =>
             y ← sample uniform Out_N ;;
             #put indep_loc := setm T2 (ss, info) y ;;
             ret y
         end).
      { apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (ss, info)) => [y|] ].
        { exact: lv_ret. }
        { apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret]. } }
      have Hm1'' : bad_loc_monotone 4
        (T2 ← get mid_loc ;;
         match T2 (prk0, info) with
         | Some y => ret y
         | None =>
             y ← sample uniform Out_N ;;
             #put mid_loc := setm T2 (prk0, info) y ;;
             ret y
         end).
      { apply: blm_getr => T2. case: (T2 (prk0, info)) => [y|].
        { exact: blm_ret. }
        { apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret]. } }
      have Hm2'' : bad_loc_monotone 4
        (T2 ← get indep_loc ;;
         match T2 (ss, info) with
         | Some y => ret y
         | None =>
             y ← sample uniform Out_N ;;
             #put indep_loc := setm T2 (ss, info) y ;;
             ret y
         end).
      { apply: blm_getr => T2. case: (T2 (ss, info)) => [y|].
        { exact: blm_ret. }
        { apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret]. } }
      move=> t0 t1 [/= -> ->] a1 h1'' a2 h2'' Hgt1'' Hgt2''.
      have Hgt1''' : (0 < Pr_code (T2 ← get mid_loc ;;
           match T2 (prk0, info) with
           | Some y => ret y
           | None =>
               y ← sample uniform Out_N ;;
               #put mid_loc := setm T2 (prk0, info) y ;;
               ret y
           end) (set_heap (set_heap s0 extract_loc (setm T ss prk0)) bad_loc true) (a1,h1''))%R.
      { rewrite Pr_code_theta_bridge. exact: Hgt1''. }
      have Hgt2''' : (0 < Pr_code (T2 ← get indep_loc ;;
           match T2 (ss, info) with
           | Some y => ret y
           | None =>
               y ← sample uniform Out_N ;;
               #put indep_loc := setm T2 (ss, info) y ;;
               ret y
           end) (set_heap (set_heap s1 extract_loc (setm T ss prk0)) bad_loc true) (a2,h2''))%R.
      { rewrite Pr_code_theta_bridge. exact: Hgt2''. }
      have Hbad1'' : get_heap h1'' bad_loc = true.
      { exact: (proj2 (Pr_code_lossless_bad KDF_mid'_locs _ Hlv1'' Hm1'' _ Hbada) a1 h1'' Hgt1'''). }
      have Hbad2'' : get_heap h2'' bad_loc = true.
      { exact: (proj2 (Pr_code_lossless_bad KDF_bad_locs _ Hlv2'' Hm2'' _ Hbadb) a2 h2'' Hgt2'''). }
      split.
      { split.
        { split.
          { move=> l Hnotin.
            have Hnotin1 : l.1 \notin domm KDF_mid'_locs.
            { move: Hnotin. rewrite /KDF_mid'_bad_locs domm_union in_fsetU negb_or => /andP[] //. }
            have Hnotin2 : l.1 \notin domm KDF_bad_locs.
            { move: Hnotin. rewrite /KDF_mid'_bad_locs domm_union in_fsetU negb_or => /andP[] //. }
            rewrite (theta_frame KDF_mid'_locs _ Hlv1'' _ l Hnotin1 a1 h1'' Hgt1'').
            rewrite (theta_frame KDF_bad_locs _ Hlv2'' _ l Hnotin2 a2 h2'' Hgt2'').
            have Hne_e1 : l.1 != extract_loc.1.
            { apply/eqP => Heq. move: Hnotin1 => /negP; apply.
              have : extract_loc.1 \in domm KDF_mid'_locs by apply: fhas_in; fmap_solve.
              by rewrite Heq. }
            have Hne_b1 : l.1 != bad_loc.1.
            { apply/eqP => Heq. move: Hnotin1 => /negP; apply.
              have : bad_loc.1 \in domm KDF_mid'_locs by apply: fhas_in; fmap_solve.
              by rewrite Heq. }
            rewrite (get_set_heap_neq _ _ _ _ Hne_b1) (get_set_heap_neq _ _ _ _ Hne_e1).
            have Hne_e2 : l.1 != extract_loc.1.
            { apply/eqP => Heq. move: Hnotin2 => /negP; apply.
              have : extract_loc.1 \in domm KDF_bad_locs by apply: fhas_in; fmap_solve.
              by rewrite Heq. }
            have Hne_b2 : l.1 != bad_loc.1.
            { apply/eqP => Heq. move: Hnotin2 => /negP; apply.
              have : bad_loc.1 \in domm KDF_bad_locs by apply: fhas_in; fmap_solve.
              by rewrite Heq. }
            rewrite (get_set_heap_neq _ _ _ _ Hne_b2) (get_set_heap_neq _ _ _ _ Hne_e2).
            exact: (proj1 (proj1 Hpre) l Hnotin). }
          rewrite /rel_app /get_side /=. by rewrite Hbad1'' Hbad2''. }
        rewrite /rel_app /get_side /=. move=> Hf. rewrite Hbad1'' in Hf. discriminate. }
      rewrite /rel_app /get_side /=. move=> Hf. rewrite Hbad1'' in Hf. discriminate. }
    rewrite HUU' -HeqU' E.
    simpl.
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(t0,t1) => t0 = set_heap s0 extract_loc (setm T ss prk0) /\ t1 = set_heap s1 extract_loc (setm T ss prk0)).
    2: { move=> t0 t1 [/= -> ->]. done. }
    apply: (r_put_vs_put used_prk_loc (setm (get_heap s1 used_prk_loc) prk0 tt) used_prk_loc (setm (get_heap s1 used_prk_loc) prk0 tt) _ _
      (fun '(t0,t1) => t0 = set_heap s0 extract_loc (setm T ss prk0) /\ t1 = set_heap s1 extract_loc (setm T ss prk0))
      (fun '(b0,s0') '(b1,s1') => KDF_mid'_bad_inv (s0',s1') /\ (get_heap s0' (pkg_upto_bad.bad_loc 4) = false -> b0=b1))).
    apply: rpre_hypothesis_rule => s10 s11 Hp3.
    move: Hp3 => [s11'' [[s10'' [[Heq10 Heq11] ->]] ->]].
    subst s10'' s11''.
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(t0,t1) => t0 = set_heap (set_heap s0 extract_loc (setm T ss prk0)) used_prk_loc (setm (get_heap s1 used_prk_loc) prk0 tt) /\ t1 = set_heap (set_heap s1 extract_loc (setm T ss prk0)) used_prk_loc (setm (get_heap s1 used_prk_loc) prk0 tt)).
    2: { move=> t0 t1 [/= -> ->]. done. }
    eapply (r_get_remember_lhs mid_loc _ _ (fun '(t0,t1) => t0 = set_heap (set_heap s0 extract_loc (setm T ss prk0)) used_prk_loc (setm (get_heap s1 used_prk_loc) prk0 tt) /\ t1 = set_heap (set_heap s1 extract_loc (setm T ss prk0)) used_prk_loc (setm (get_heap s1 used_prk_loc) prk0 tt))).
    move=> Tm.
    eapply (r_get_remember_rhs indep_loc _ _ ((fun '(t0,t1) => t0 = set_heap (set_heap s0 extract_loc (setm T ss prk0)) used_prk_loc (setm (get_heap s1 used_prk_loc) prk0 tt) /\ t1 = set_heap (set_heap s1 extract_loc (setm T ss prk0)) used_prk_loc (setm (get_heap s1 used_prk_loc) prk0 tt)) ⋊ rem_lhs mid_loc Tm)).
    move=> Ti.
    apply: rpre_hypothesis_rule => s12 s13 Hp4.
    case: Hp4 => [[[Heq12 Heq13] HeqTm] HeqTi].
    move: HeqTm HeqTi. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=. move=> HeqTm HeqTi.
    subst s12 s13.
    rewrite (get_set_heap_neq _ _ _ _ (isT : mid_loc.1 != used_prk_loc.1)) in HeqTm.
    rewrite (get_set_heap_neq _ _ _ _ (isT : mid_loc.1 != extract_loc.1)) in HeqTm.
    rewrite (get_set_heap_neq _ _ _ _ (isT : indep_loc.1 != used_prk_loc.1)) in HeqTi.
    rewrite (get_set_heap_neq _ _ _ _ (isT : indep_loc.1 != extract_loc.1)) in HeqTi.
    have HTmNone : Tm (prk0, info) = None.
    { apply/eqP; case Hc: (Tm (prk0,info)) => [y|] //.
      exfalso.
      have Hex : exists ss', T ss' = Some prk0.
      { rewrite -HeqT.
        apply: (Hmf prk0 info).
        rewrite HeqTm Hc. done. }
      destruct Hex as [ss' Hss'].
      have HUsome : getm (get_heap s0 used_prk_loc) prk0 = Some tt.
      { apply: (proj2 (Hcorr prk0)). exists ss'. rewrite HeqT. exact: Hss'. }
      rewrite HU in HUsome.
      rewrite HUsome in E.
      discriminate. }
    have HTiNone : Ti (ss, info) = None.
    { apply/eqP; case Hc: (Ti (ss,info)) => [y|] //.
      exfalso.
      have := (Hif ss info).
      rewrite HeqTi Hc.
      move=> Hcontra.
      have Hne : Some y <> None := fun H => match H with end.
      have Hss0 : get_heap s0 extract_loc ss = None.
      { rewrite HeqT. exact: HTss. }
      exact: (Hcontra Hne Hss0). }
    rewrite HTmNone HTiNone.
    eapply (r_uniform_bij _ _ _ _ id). 1: exists id; done.
    move=> y.
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(t0,t1) => t0 = set_heap (set_heap s0 extract_loc (setm T ss prk0)) used_prk_loc (setm (get_heap s1 used_prk_loc) prk0 tt) /\ t1 = set_heap (set_heap s1 extract_loc (setm T ss prk0)) used_prk_loc (setm (get_heap s1 used_prk_loc) prk0 tt)).
    2: { move=> t0 t1 [/= -> ->]. done. }
    apply: (r_put_vs_put mid_loc (setm Tm (prk0, info) y) indep_loc (setm Ti (ss, info) y) _ _
      (fun '(t0,t1) => t0 = set_heap (set_heap s0 extract_loc (setm T ss prk0)) used_prk_loc (setm (get_heap s1 used_prk_loc) prk0 tt) /\ t1 = set_heap (set_heap s1 extract_loc (setm T ss prk0)) used_prk_loc (setm (get_heap s1 used_prk_loc) prk0 tt))
      (fun '(b0,s0') '(b1,s1') => KDF_mid'_bad_inv (s0',s1') /\ (get_heap s0' (pkg_upto_bad.bad_loc 4) = false -> b0=b1))).
    apply: r_ret.
    move=> t0 t1 [s1'' [[s0'' [[Heq0 Heq1] ->]] ->]].
    subst s0'' s1''.
    split; [ | done].
    have Hig : heap_ignore KDF_mid'_bad_locs (s0,s1) := proj1 (proj1 Hpre).
    have Hsync : get_heap s0 bad_loc = get_heap s1 bad_loc.
    { move: (proj2 (proj1 Hpre)). rewrite /rel_app /get_side /=. done. }
    split.
    { split.
      { move=> l Hnotin.
        have Hne_m : l.1 != mid_loc.1.
        { apply/eqP => Heq. move: Hnotin => /negP; apply.
          have : mid_loc.1 \in domm KDF_mid'_bad_locs by apply: fhas_in; fmap_solve.
          by rewrite Heq. }
        have Hne_i : l.1 != indep_loc.1.
        { apply/eqP => Heq. move: Hnotin => /negP; apply.
          have : indep_loc.1 \in domm KDF_mid'_bad_locs by apply: fhas_in; fmap_solve.
          by rewrite Heq. }
        have Hne_u : l.1 != used_prk_loc.1.
        { apply/eqP => Heq. move: Hnotin => /negP; apply.
          have : used_prk_loc.1 \in domm KDF_mid'_bad_locs by apply: fhas_in; fmap_solve.
          by rewrite Heq. }
        have Hne_e : l.1 != extract_loc.1.
        { apply/eqP => Heq. move: Hnotin => /negP; apply.
          have : extract_loc.1 \in domm KDF_mid'_bad_locs by apply: fhas_in; fmap_solve.
          by rewrite Heq. }
        rewrite (get_set_heap_neq _ _ _ _ Hne_m) (get_set_heap_neq _ _ _ _ Hne_u) (get_set_heap_neq _ _ _ _ Hne_e).
        rewrite (get_set_heap_neq _ _ _ _ Hne_i) (get_set_heap_neq _ _ _ _ Hne_u) (get_set_heap_neq _ _ _ _ Hne_e).
        exact: (Hig l Hnotin). }
      rewrite /rel_app /get_side /=.
      rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != mid_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != used_prk_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != extract_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != indep_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != used_prk_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != extract_loc.1)).
      exact: Hsync. }
    rewrite /rel_app /get_side /=.
    rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != mid_loc.1)).
    rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != used_prk_loc.1)).
    rewrite (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != mid_loc.1)).
    rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != indep_loc.1)).
    rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != used_prk_loc.1)).
    rewrite (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != indep_loc.1)).
    rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != mid_loc.1)).
    rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != used_prk_loc.1)).
    rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != extract_loc.1)).
    rewrite Hbad. move=> _.
    rewrite !get_set_heap_eq.
    split; [done | ].
    split; [done | ].
    have Hfresh_prk0 : ~ (exists ss', T ss' = Some prk0).
    { move=> [ss' Hss'].
      have HUsome : getm (get_heap s0 used_prk_loc) prk0 = Some tt.
      { apply: (proj2 (Hcorr prk0)). exists ss'. rewrite HeqT. exact: Hss'. }
      rewrite HU in HUsome. rewrite HUsome in E. discriminate. }
    have HTmNone_all : forall info0, Tm (prk0, info0) = None.
    { move=> info0. apply/eqP; case Hc: (Tm (prk0,info0)) => [y0|] //.
      exfalso. apply: Hfresh_prk0.
      have := (Hmf prk0 info0). rewrite HeqTm Hc.
      move=> Hcontra.
      have Hne : Some y0 <> None := fun H => match H with end.
      move: (Hcontra Hne) => [ss' Hss']. exists ss'. rewrite -HeqT. exact: Hss'. }
    have HTiNone_all : forall info1, Ti (ss, info1) = None.
    { move=> info1. apply/eqP; case Hc: (Ti (ss,info1)) => [y0|] //.
      exfalso.
      have := (Hif ss info1). rewrite HeqTi Hc.
      move=> Hcontra.
      have Hne2 : Some y0 <> None := fun H => match H with end.
      have Hss0 : get_heap s0 extract_loc ss = None.
      { rewrite HeqT. exact: HTss. }
      exact: (Hcontra Hne2 Hss0). }
    split.
    { move=> ss0 info0.
      case: (eqVneq ss0 ss) => [-> | Hne].
      { rewrite setmE eqxx.
        rewrite !setmE.
        case: (eqVneq info0 info) => [-> | Hnei].
        { by rewrite eqxx eqxx. }
        { have -> : ((prk0,info0) == (prk0,info)) = (info0 == info) by rewrite xpair_eqE eqxx.
          have -> : ((ss,info0) == (ss,info)) = (info0 == info) by rewrite xpair_eqE eqxx.
          rewrite (negbTE Hnei) HTmNone_all HTiNone_all. done. } }
      { rewrite setmE.
        have -> : (ss0 == ss) = false by exact: negbTE.
        case HTss0 : (T ss0) => [prk1|] //.
        have Hneprk : prk1 != prk0.
        { apply/eqP => Heqp. subst prk1. apply: Hfresh_prk0. exists ss0. exact: HTss0. }
        rewrite !setmE.
        have -> : ((prk1,info0) == (prk0,info)) = false.
        { apply/negP => /eqP [] Heqp _. move: Hneprk => /eqP; apply. exact: Heqp. }
        have -> : ((ss0,info0) == (ss,info)) = false.
        { apply/negP => /eqP [] Heqs _. move: Hne => /eqP; apply. exact: Heqs. }
        move: (Hmid ss0 info0). rewrite HeqT HTss0 HeqTm HeqTi. done. } }
    split.
    { move=> prk'.
      split.
      { move=> Hget.
        case: (eqVneq prk' prk0) => [-> | Hneprk'].
        { exists ss. rewrite setmE eqxx. reflexivity. }
        { move: Hget. rewrite setmE.
          have -> : (prk' == prk0) = false by exact: negbTE.
          move=> Hget.
          have Hget0 : get_heap s0 used_prk_loc prk' = Some tt.
          { rewrite HU. exact: Hget. }
          have [ss'0 Hss'0] := (proj1 (Hcorr prk') Hget0).
          exists ss'0. rewrite setmE.
          have -> : (ss'0 == ss) = false.
          { apply/negP => /eqP Heqss. subst ss'0.
            rewrite HeqT HTss in Hss'0. discriminate. }
          rewrite -HeqT. exact: Hss'0. } }
      move=> [ss' Hss'].
      case: (eqVneq ss' ss) => [Heqss | Hness].
      { subst ss'. move: Hss'. rewrite setmE eqxx. move=> [<-]. rewrite setmE eqxx. done. }
      move: Hss'. rewrite setmE.
      have -> : (ss' == ss) = false by exact: negbTE.
      move=> Hss'.
      have Hcorrp : getm (get_heap s0 used_prk_loc) prk' = Some tt.
      { apply: (proj2 (Hcorr prk')). exists ss'. rewrite HeqT. exact: Hss'. }
      rewrite setmE.
      have -> : (prk' == prk0) = false.
      { apply/negP => /eqP Heqp. subst prk'.
        apply: Hfresh_prk0. exists ss'. exact: Hss'. }
      rewrite -HU. exact: Hcorrp. }
    split.
    { move=> ss1 ss2 prk1.
      case: (eqVneq ss1 ss) => [-> | Hne1].
      { rewrite setmE eqxx. move=> [<-].
        case: (eqVneq ss2 ss) => [-> | Hne2].
        { done. }
        { rewrite setmE.
          have -> : (ss2 == ss) = false by exact: negbTE.
          move=> HT2. exfalso. apply: Hfresh_prk0. exists ss2. exact: HT2. } }
      { rewrite setmE.
        have -> : (ss1 == ss) = false by exact: negbTE.
        move=> HT1.
        case: (eqVneq ss2 ss) => [-> | Hne2].
        { rewrite setmE eqxx. move=> [Heq]. subst prk1. exfalso. apply: Hfresh_prk0. exists ss1. exact: HT1. }
        { rewrite setmE.
          have -> : (ss2 == ss) = false by exact: negbTE.
          move=> HT2.
          apply: (Hinj ss1 ss2 prk1); rewrite HeqT; [exact: HT1 | exact: HT2]. } } }
    split.
    { move=> prk' info' Hne0.
      case: (eqVneq (prk',info') (prk0,info)) => [Heqp | Hneqp].
      { have Heqp' : prk' = prk0 := f_equal fst Heqp.
        exists ss. rewrite setmE eqxx. rewrite Heqp'. reflexivity. }
      { move: Hne0. rewrite setmE.
        have -> : ((prk',info') == (prk0,info)) = false by exact: negbTE.
        move=> Hne0.
        have Hne0' : get_heap s0 mid_loc (prk',info') <> None.
        { rewrite HeqTm. exact: Hne0. }
        have [ss'' Hss''] := (Hmf prk' info' Hne0').
        exists ss''. rewrite setmE.
        case: (eqVneq ss'' ss) => [Heqss | Hness].
        { subst ss''. rewrite HeqT HTss in Hss''. discriminate. }
        rewrite -HeqT. exact: Hss''. } }
    move=> ss' info' Hne0.
    case: (eqVneq ss' ss) => [-> | Hne].
    { rewrite setmE eqxx. discriminate. }
    rewrite setmE.
    have -> : (ss' == ss) = false by exact: negbTE.
    move: Hne0. rewrite setmE.
    have -> : ((ss',info') == (ss,info)) = false.
    { apply/negP => /eqP [] Heqs _. move: Hne => /eqP; apply. exact: Heqs. }
    move=> Hne0.
    have Hne0' : get_heap s1 indep_loc (ss',info') <> None.
    { rewrite HeqTi. exact: Hne0. }
    have HT' := (Hif ss' info' Hne0').
    rewrite -HeqT. exact: HT'.
  Qed.
  Local Open Scope ring_scope.

  (** [eq_upto_bad_perf_ind] (pkg_upto_bad.v), the Fundamental Lemma of
    Game-Playing, turns [KDF_mid'_KDF_bad_eq_up_to_bad] into an actual
    probability bound: [KDF_mid'] and [KDF_bad] can only be distinguished
    as often as [bad_loc] ends up [true] when running [A ∘ KDF_mid']. *)
  Lemma KDF_mid'_KDF_bad_bound LA A :
    ValidPackage LA DERIVE_export A_export A →
    fseparate LA KDF_mid'_locs →
    fseparate LA KDF_bad_locs →
    lossless_valid_adv LA DERIVE_export (resolve A RUN tt) →
    AdvantageE KDF_mid' KDF_bad A <= Pr_bad (A ∘ KDF_mid') 4 true.
  Proof.
    intros vA Hsep0 Hsep1 Hlva.
    eapply eq_upto_bad_perf_ind.
    1: exact _.
    1: exact _.
    1: exact vA.
    1: eapply (INV'_to_INV LA KDF_mid'_locs KDF_bad_locs KDF_mid'_bad_inv).
    1: exact: (inv_INV' (Invariant:=KDF_mid'_bad_Invariant)).
    1: exact Hsep0.
    1: exact Hsep1.
    1: exact: (inv_empty (Invariant:=KDF_mid'_bad_Invariant)).
    1: exact Hsep0.
    1: exact Hsep1.
    1: exact Hlva.
    1: eapply (notin_has_separate KDF_mid'_locs LA bad_loc); [ fmap_solve | apply: fseparateC; exact Hsep0 ].
    1: move=> s0 s1 Hpre; exact: (proj2 (proj1 Hpre)).
    1: exact: KDF_mid'_KDF_bad_eq_up_to_bad.
    1: exact: KDF_mid'_bad_preserved.
    1: exact: KDF_bad_bad_preserved.
  Qed.

  (* --- single-key PRF assumption, spent one hybrid step at a time ---

    [EVAL_OP] mirrors [PRF.v]/[PRFPRG.v]'s own [EVAL]: a single, uniformly
    random, hidden key [k] is either sampled once and used for every query
    ([EVAL_pkg_tt], i.e. "real"), or replaced by an independent lazily
    sampled random function ([EVAL_pkg_ff], i.e. "ideal"). [prf_epsilon]
    is the adversary's advantage in telling those two apart -- negligible
    by the security of [PRF], and the sole per-step cost of the hybrid
    argument below.
  *)

  Definition EVAL_OP : nat := 1.

  Definition EVAL_export := [interface #val #[ EVAL_OP ] : 'info → 'out ].

  Definition eval_key_loc := mkloc 7 (None : option 'prk).
  Definition eval_tbl_loc := mkloc 8 (emptym : chMap 'info 'out).

  Definition EVAL_pkg_tt : package [interface] EVAL_export :=
    [package [fmap eval_key_loc] ;
      #def #[ EVAL_OP ] (info : 'info) : 'out
      {
        k ← get eval_key_loc ;;
        match k with
        | Some k => ret (PRF info k)
        | None =>
            k ← sample uniform PRK_N ;;
            #put eval_key_loc := Some k ;;
            ret (PRF info k)
        end
      }
    ].

  Definition EVAL_pkg_ff : package [interface] EVAL_export :=
    [package [fmap eval_tbl_loc] ;
      #def #[ EVAL_OP ] (info : 'info) : 'out
      {
        T ← get eval_tbl_loc ;;
        match getm T info with
        | Some y => ret y
        | None =>
            y <$ uniform Out_N ;;
            #put eval_tbl_loc := setm T info y ;;
            ret y
        end
      }
    ].

  Definition EVAL b : game EVAL_export := if b then EVAL_pkg_tt else EVAL_pkg_ff.

  Definition prf_epsilon (A : raw_package) : R := Advantage EVAL A.

  (* --- hybrid family, indexed by "number of *distinct* shared secrets
    treated as ideal so far" ---

    [KDF_hyb i]: the first [i] distinct SHARED SECRETS Extract has ever
    seen get an ideal (random-function) Expand via [mid_loc]; every
    shared secret discovered after that gets the real [PRF]. Distinct
    shared secrets are numbered by order of first appearance
    ([ss_index_loc] / [ss_count_loc]), so this is well-defined for an
    adaptive adversary exactly like [GEN_HYB_pkg] in PRFPRG.v (indexed
    there by raw query count instead of by distinct-key count).

    Indexing by [ss] (rather than by [prk], as an earlier attempt did)
    is what makes [KDF_hyb_KDF_hyb_EVAL_true_equiv] below provable: the
    index assigned to a query is now decided by [get_ss_idx] alone,
    entirely BEFORE [get_prk] ever samples anything, so the moment a
    brand new [ss] is assigned index exactly [i], [get_prk]'s sample for
    that same [ss] is still pending and can be coupled directly against
    [EVAL]'s own first-use key sample. (Indexing by [prk] instead forces
    the [prk] sample to happen first, in order to even know which
    index/branch to take, leaving nothing left on the LHS to couple
    against.)

    [KDF_hyb 0] is exactly [KDF_real]: no [ss] ever has index < 0, so
    every query takes the real-PRF branch. For any [i] at least the
    number of distinct shared secrets ever queried, [KDF_hyb i] is
    exactly [KDF_mid]: every [ss] has index < i, so every query takes the
    ideal branch. Crucially, swapping *one* shared secret's Expand from
    real to ideal never needs the birthday assumption: [KDF_real] and
    [KDF_mid] already agree on what to do with a *repeated* [prk] (both
    are pure functions of [prk] alone), so nothing here depends on
    distinct shared secrets staying collision-free -- that concern only
    arises when comparing against [KDF_ideal] (step 2).
  *)

  Definition ss_count_loc := mkloc 12 (0 : nat).
  Definition ss_index_loc := mkloc 13 (emptym : chMap 'ss 'nat).

  Definition KDF_hyb_locs :=
    [fmap extract_loc; mid_loc; ss_count_loc; ss_index_loc].

  (* The order in which [ss] was first queried (assigning it a fresh,
    incrementing index the first time it is ever seen), entirely
    independent of [extract_loc]/[get_prk] below. Shared, unchanged,
    between [KDF_hyb] and [KDF_hyb_EVAL]. *)
  Definition get_ss_idx (ss : 'ss) : raw_code 'nat :=
    SIdx ← get ss_index_loc ;;
    match getm SIdx ss with
    | Some idx => ret idx
    | None =>
        cnt ← get ss_count_loc ;;
        #put ss_count_loc := cnt.+1 ;;
        #put ss_index_loc := setm SIdx ss cnt ;;
        ret cnt
    end.

  Lemma get_ss_idx_valid {L I} (ss : 'ss) :
    fhas L ss_index_loc -> fhas L ss_count_loc ->
    ValidCode L I (get_ss_idx ss).
  Proof.
    move=> H1 H2.
    rewrite /get_ss_idx.
    apply: valid_getr => [// | SIdx].
    case: (getm SIdx ss) => [idx|].
    - by apply: valid_ret.
    - apply: valid_getr => [// | cnt].
      apply: valid_putr => //.
      apply: valid_putr => //.
      by apply: valid_ret.
  Qed.

  Hint Extern 1 (ValidCode ?L ?I (get_ss_idx ?ss)) =>
    eapply get_ss_idx_valid ; [ fmap_solve | fmap_solve ]
    : typeclass_instances ssprove_valid_db.

  (* Extract [ss]'s [prk] -- identical to [KDF_real]/[KDF_mid]'s own
    inline Extract step, just factored out so [KDF_hyb]/[KDF_hyb_EVAL]
    can share it verbatim. Deliberately decoupled from [get_ss_idx]: no
    index bookkeeping happens here at all. *)
  Definition get_prk (ss : 'ss) : raw_code 'prk :=
    T ← get extract_loc ;;
    match getm T ss with
    | Some prk => ret prk
    | None =>
        prk <$ uniform PRK_N ;;
        #put extract_loc := setm T ss prk ;;
        ret prk
    end.

  Lemma get_prk_valid {L I} (ss : 'ss) :
    fhas L extract_loc ->
    ValidCode L I (get_prk ss).
  Proof.
    move=> H.
    rewrite /get_prk.
    apply: valid_getr => [// | T].
    case: (getm T ss) => [prk|].
    - by apply: valid_ret.
    - apply: valid_sampler => prk.
      apply: valid_putr => //.
      by apply: valid_ret.
  Qed.

  Hint Extern 1 (ValidCode ?L ?I (get_prk ?ss)) =>
    eapply get_prk_valid ; [ fmap_solve ]
    : typeclass_instances ssprove_valid_db.

  Definition KDF_hyb (i : nat) : game DERIVE_export :=
    [package KDF_hyb_locs ;
      #def #[ DERIVE ] ('(ss, info) : 'ss × 'info) : 'out
      {
        idx ← get_ss_idx ss ;;
        if ltn idx i then
          prk ← get_prk ss ;;
          T2 ← get mid_loc ;;
          match getm T2 (prk, info) with
          | Some y => ret y
          | None =>
              y <$ uniform Out_N ;;
              #put mid_loc := setm T2 (prk, info) y ;;
              ret y
          end
        else
          prk ← get_prk ss ;;
          ret (PRF info prk)
      }
    ].

  (* Connector: handles every [ss] except the one at index exactly [i]
    itself (using [mid_loc] / the real [PRF] as [KDF_hyb] does), and
    delegates that one instance to the imported [EVAL] oracle. Composing
    with [EVAL true] (real) reproduces [KDF_hyb i]; composing with
    [EVAL false] (ideal) reproduces [KDF_hyb i.+1]. *)
  Definition KDF_hyb_EVAL (i : nat) : package EVAL_export DERIVE_export :=
    [package KDF_hyb_locs ;
      #def #[ DERIVE ] ('(ss, info) : 'ss × 'info) : 'out
      {
        #import {sig #[ EVAL_OP ] : 'info → 'out } as eval ;;
        idx ← get_ss_idx ss ;;
        if ltn idx i then
          prk ← get_prk ss ;;
          T2 ← get mid_loc ;;
          match getm T2 (prk, info) with
          | Some y => ret y
          | None =>
              y <$ uniform Out_N ;;
              #put mid_loc := setm T2 (prk, info) y ;;
              ret y
          end
        else if (idx : nat) == i then
          eval info
        else
          prk ← get_prk ss ;;
          ret (PRF info prk)
      }
    ].

  (* The classical birthday bound: with (at most) q samples drawn
     uniformly from a space of size [PRK_N], the probability that two of
     them collide is at most q^2 / (2 * PRK_N). *)
  Definition birthday_bound (q : nat) : R :=
    (q * q)%:R / (2 * PRK_N)%:R.

  Lemma PRK_N_gt0 : (0 < PRK_N)%N.
  Proof. rewrite /PRK_N expn_gt0. by []. Qed.

  (* [fin_family PRK_N] is exactly the finType underlying [uniform PRK_N]'s
    own distribution [Uni_W PRK_N] (see [UniformStateProb.v]'s definitions
    of [fin_family]/[Uni_W]/[uniform_F]), so instantiating [Birthday.v]'s
    development at [F := fin_family PRK_N] connects directly to this
    file's own [uniform PRK_N] sampler with NO separate
    distribution-identification lemma needed -- just this cardinality
    fact, to match [Birthday.v]'s [#|F|] against this file's [PRK_N]. *)
  Lemma card_fin_family_PRK_N : #|fin_family PRK_N| = PRK_N.
  Proof. rewrite /fin_family /=. by rewrite card_ord. Qed.

  (* The one-line arithmetic step promised in [Pr_bad_COUNT_KDF_mid'_bound]'s
    docstring: [bad_bound q 0 <= birthday_bound q], since [q*(q-1) <= q*q]. *)
  Lemma bad_bound_le_birthday_bound q :
    Birthday.bad_bound (fin_family PRK_N) q 0 <= birthday_bound q.
  Proof.
    rewrite /Birthday.bad_bound /birthday_bound card_fin_family_PRK_N.
    rewrite muln0 add0n.
    apply: ler_wpM2r.
    - by rewrite invr_ge0 ler0n.
    - by rewrite ler_nat leq_mul2l leq_subr orbT.
  Qed.

  (* [KDF_hyb 0] is exactly [KDF_real]: no [ss] ever has index < 0, so
    the "ideal" branch is dead, and the [ss_count_loc]/[ss_index_loc]
    bookkeeping is ghost state, exactly like [KDF_bad]'s bookkeeping was
    dead w.r.t. [KDF_bad_KDF_ideal_equiv] above. Since [get_ss_idx] and
    [get_prk] are now fully independent, this needs no cross-referential
    reasoning at all: [get_ss_idx]'s own bookkeeping (whichever of its
    two branches runs) is pure ghost state, and [get_prk]'s code is
    executed identically (shared, unignored [extract_loc]) on both
    sides -- exactly [KDF_real]'s own body. *)
  Lemma KDF_real_KDF_hyb0_equiv :
    KDF_real ≈₀ KDF_hyb 0.
  Proof.
    apply eq_rel_perf_ind_ignore with [fmap mid_loc; ss_count_loc; ss_index_loc].
    1: fmap_solve.
    simplify_eq_rel arg.
    destruct arg as [ss info].
    rewrite /get_ss_idx /get_prk /=.
    apply: r_get_remember_rhs => SIdx.
    destruct (getm SIdx ss) as [idx|] eqn:HSIdx.
    - rewrite HSIdx /=.
      apply: r_get_vs_get_remember => T.
      destruct (getm T ss) as [prk|] eqn:HT.
      + rewrite HT /=.
        apply: r_ret => s0 s1 h.
        split; [ reflexivity | extract_base_inv h ].
      + rewrite HT /=.
        apply: r_uniform_bij => [|prk]. 1: exists id; done.
        apply: r_put_vs_put.
        ssprove_restore_mem; last by apply: r_ret.
        by ssprove_invariant.
    - rewrite HSIdx /=.
      apply: r_get_remember_rhs => cnt.
      apply: r_put_rhs. apply: r_put_rhs.
      ssprove_restore_mem; [ by ssprove_invariant | ].
      apply: r_get_vs_get_remember => T.
      destruct (getm T ss) as [prk|] eqn:HT.
      + rewrite HT /=.
        apply: r_ret => s0 s1 h.
        split; [ reflexivity | extract_base_inv h ].
      + rewrite HT /=.
        apply: r_uniform_bij => [|prk]. 1: exists id; done.
        apply: r_put_vs_put.
        ssprove_restore_mem; last by apply: r_ret.
        by ssprove_invariant.
  Qed.

  (**
    Step 2 of 3 (hop 2): [KDF_hyb i] agrees with [KDF_hyb_EVAL i] composed
    with the *real* single-key oracle [EVAL true]. [KDF_hyb_EVAL i] routes
    exactly the [ss] at index [i] through the imported [eval], and
    [EVAL_pkg_tt] lazily samples one hidden key on first use -- forced (by
    the invariant below) to coincide with that one [ss]'s [prk].

    Indexing by [ss] (not [prk], as an earlier attempt did) is what makes
    this provable: [get_ss_idx]/[get_prk] are fully independent, so the
    moment a brand new [ss] is assigned index exactly [i] (decided purely
    by [get_ss_idx], BEFORE any sampling), [get_prk]'s sample for that
    same [ss] is still pending on the LHS and can be coupled directly
    (via [r_uniform_bij] with [f := id]) against [EVAL_pkg_tt]'s own
    first-use key sample on the RHS.

    Unlike [PRFPRG.v]'s [GEN_GEN_HYB_equiv] (hybrid index = a raw,
    ever-incrementing query counter, so "count = i" happens at most once),
    here "idx = i" can recur: every later query for the *same* [ss] sees
    the same idx again. The invariant's second conjunct handles that:
    once [ss_count_loc] has passed [i], [eval_key_loc] is pinned for
    good (it can only ever have been set by the one [ss] at index [i]),
    so repeat queries just replay the cached branch identically on both
    sides.

    The first conjunct is a structural fact relating [ss_index_loc] and
    [extract_loc] alone (no [eval_key_loc] involved): a shared secret has
    been assigned an index iff it already has a [prk] -- both
    [get_ss_idx]/[get_prk] populate their respective tables for a given
    [ss] on that [ss]'s very first query, and never afterwards. This
    rules out the "index known, but prk somehow isn't" impossible case,
    and conversely guarantees a genuinely fresh [ss] samples a genuinely
    fresh [prk]. *)
  Definition KDF_hyb_EVAL_inv (i : nat) : precond :=
    heap_ignore [fmap eval_key_loc; extract_loc] ⋊
    couple_lhs ss_index_loc extract_loc
      (fun SIdx T => forall ss0, SIdx ss0 = None <-> T ss0 = None) ⋊
    couple_rhs ss_count_loc eval_key_loc
      (fun cnt k => leq cnt i -> k = None) ⋊
    rel_app [:: (lhs, ss_index_loc); (lhs, extract_loc); (rhs, eval_key_loc)]
      (fun SIdx T k => forall ss0 prk0, SIdx ss0 = Some i -> T ss0 = Some prk0 -> k = Some prk0) ⋊
    rel_app [:: (lhs, ss_index_loc); (lhs, extract_loc); (rhs, extract_loc)]
      (fun SIdx T T' => forall ss0, SIdx ss0 <> Some i -> T ss0 = T' ss0).

  (* Since a query's bookkeeping updates ([ss_index_loc]/[ss_count_loc] via
    [get_ss_idx]) happen strictly BEFORE the very same query's sample (via
    [get_prk]/[eval]), the invariant is genuinely, if only momentarily,
    broken in between (e.g. right after [ss_index_loc] learns about a
    brand new [ss], but before [extract_loc] has caught up) -- so any
    [r_get_vs_get_remember] taken in that window needs its own
    [ProvenBy (syncs _) _] side-fact, and the generic search
    (`syncs_proven_by_heap_ignore`, pkg_invariants.v) doesn't see through
    the intervening [set_lhs]/[set_rhs] wrappers left by the still-pending
    puts. These two instances teach it to: peel any [set_lhs ℓ' _]/
    [set_rhs ℓ' _] wrapper for a DIFFERENT location [ℓ' <> ℓ] and recurse,
    exactly the way [heap_ignore] itself is oblivious to updates at other
    locations. *)
  Lemma syncs_provenby_set_lhs_other {ℓ ℓ' : Location} {v} {pre : precond} :
    ℓ'.1 != ℓ.1 ->
    ProvenBy (syncs ℓ) pre ->
    ProvenBy (syncs ℓ) (set_lhs ℓ' v pre).
  Proof.
    move=> Hne Hp [s0 s1] [s0' [Hpre Es0]]. subst.
    move: (Hp _ Hpre).
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
    move=> Hs'.
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
    have Hne' : ℓ.1 != ℓ'.1 by rewrite eq_sym.
    rewrite (get_set_heap_neq _ _ _ _ Hne').
    exact: Hs'.
  Qed.

  (* Two locations updated to the SAME value on both sides, in lockstep,
    never break agreement at any third location [l] -- whether [l] is one
    of the two updated locations (both sides get literally the same
    override) or a completely different one (both sides pass the update
    through unchanged, by [get_set_heap_neq]). This is the generic fact
    that lets a leaf reprove [heap_ignore]/[couple_rhs ss_count_loc
    eval_key_loc]-style conjuncts after [get_ss_idx]'s own two puts,
    without needing to know whether [l] happens to coincide with either
    updated location. *)
  Lemma get_heap_after_common_double_update {ℓ1 : Location} (v1 : ℓ1) {ℓ2 : Location} (v2 : ℓ2)
    (s0y s1y : heap) (l : Location) :
    get_heap s0y l = get_heap s1y l ->
    get_heap (set_heap (set_heap s0y ℓ1 v1) ℓ2 v2) l = get_heap (set_heap (set_heap s1y ℓ1 v1) ℓ2 v2) l.
  Proof.
    move=> Hbase.
    case: (eqVneq l.1 ℓ2.1) => Heq2.
    - rewrite /get_heap /set_heap !setmE Heq2 eq_refl //.
    - rewrite (get_set_heap_neq _ _ _ _ Heq2) (get_set_heap_neq _ _ _ _ Heq2).
      case: (eqVneq l.1 ℓ1.1) => Heq1.
      + rewrite /get_heap /set_heap !setmE Heq1 eq_refl //.
      + rewrite (get_set_heap_neq _ _ _ _ Heq1) (get_set_heap_neq _ _ _ _ Heq1).
        exact: Hbase.
  Qed.

  Lemma syncs_provenby_set_rhs_other {ℓ ℓ' : Location} {v} {pre : precond} :
    ℓ'.1 != ℓ.1 ->
    ProvenBy (syncs ℓ) pre ->
    ProvenBy (syncs ℓ) (set_rhs ℓ' v pre).
  Proof.
    move=> Hne Hp [s0 s1] [s1' [Hpre Es1]]. subst.
    move: (Hp _ Hpre).
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
    move=> Hs'.
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
    have Hne' : ℓ.1 != ℓ'.1 by rewrite eq_sym.
    rewrite (get_set_heap_neq _ _ _ _ Hne').
    exact: Hs'.
  Qed.

  Hint Extern 10 (ProvenBy (syncs _) (set_lhs _ _ _)) =>
    eapply syncs_provenby_set_lhs_other; [ done | ]
    : typeclass_instances.

  Hint Extern 10 (ProvenBy (syncs _) (set_rhs _ _ _)) =>
    eapply syncs_provenby_set_rhs_other; [ done | ]
    : typeclass_instances.

  (* Same idea as the two [syncs_provenby_set_*_other] instances above, but
    for an arbitrary [single_lhs]/[single_rhs] fact (a [rel_app] over just
    ONE location) instead of a two-location [syncs] fact. Needed in the
    "[ss] is brand new" branch of [KDF_hyb_KDF_hyb_EVAL_true_equiv] below:
    once a fresh index is assigned, [ss_index_loc]/[ss_count_loc] get
    wrapped in pending [set_lhs]/[set_rhs] (from [get_ss_idx]'s own puts),
    and any [single_lhs]/[single_rhs] fact about a DIFFERENT location
    (here, [extract_loc]/[eval_key_loc]) needs to be pushed through those
    wrappers to stay usable by [ssprove_rem_rel] on the far side. A
    [single_lhs]/[single_rhs] fact only reads ONE side's heap, so it is
    trivially preserved by an update on the OTHER side (no disjointness
    side-condition needed there at all), and by an update to a DIFFERENT
    location on the SAME side (disjointness side-condition, as with
    [syncs]). *)
  Lemma single_lhs_provenby_set_lhs_other {ℓ ℓ' : Location} {v} {R : ℓ -> Prop} {pre : precond} :
    ℓ'.1 != ℓ.1 ->
    ProvenBy (single_lhs ℓ R) pre ->
    ProvenBy (single_lhs ℓ R) (set_lhs ℓ' v pre).
  Proof.
    move=> Hne Hp [s0 s1] [s0' [Hpre Es0]]. subst.
    move: (Hp _ Hpre).
    rewrite (rel_app_cons) (rel_app_nil) /=.
    move=> HR.
    rewrite (rel_app_cons) (rel_app_nil) /=.
    have Hne' : ℓ.1 != ℓ'.1 by rewrite eq_sym.
    rewrite (get_set_heap_neq _ _ _ _ Hne').
    exact: HR.
  Qed.

  Lemma single_lhs_provenby_set_rhs_other {ℓ ℓ' : Location} {v} {R : ℓ -> Prop} {pre : precond} :
    ProvenBy (single_lhs ℓ R) pre ->
    ProvenBy (single_lhs ℓ R) (set_rhs ℓ' v pre).
  Proof.
    move=> Hp [s0 s1] [s1' [Hpre Es1]]. subst.
    move: (Hp _ Hpre).
    rewrite (rel_app_cons) (rel_app_nil) /=.
    move=> HR.
    rewrite (rel_app_cons) (rel_app_nil) /=.
    exact: HR.
  Qed.

  Lemma single_rhs_provenby_set_rhs_other {ℓ ℓ' : Location} {v} {R : ℓ -> Prop} {pre : precond} :
    ℓ'.1 != ℓ.1 ->
    ProvenBy (single_rhs ℓ R) pre ->
    ProvenBy (single_rhs ℓ R) (set_rhs ℓ' v pre).
  Proof.
    move=> Hne Hp [s0 s1] [s1' [Hpre Es1]]. subst.
    move: (Hp _ Hpre).
    rewrite (rel_app_cons) (rel_app_nil) /=.
    move=> HR.
    rewrite (rel_app_cons) (rel_app_nil) /=.
    have Hne' : ℓ.1 != ℓ'.1 by rewrite eq_sym.
    rewrite (get_set_heap_neq _ _ _ _ Hne').
    exact: HR.
  Qed.

  Lemma single_rhs_provenby_set_lhs_other {ℓ ℓ' : Location} {v} {R : ℓ -> Prop} {pre : precond} :
    ProvenBy (single_rhs ℓ R) pre ->
    ProvenBy (single_rhs ℓ R) (set_lhs ℓ' v pre).
  Proof.
    move=> Hp [s0 s1] [s0' [Hpre Es0]]. subst.
    move: (Hp _ Hpre).
    rewrite (rel_app_cons) (rel_app_nil) /=.
    move=> HR.
    rewrite (rel_app_cons) (rel_app_nil) /=.
    exact: HR.
  Qed.

  Hint Extern 10 (ProvenBy (single_lhs _ _) (set_lhs _ _ _)) =>
    eapply single_lhs_provenby_set_lhs_other; [ done | ]
    : typeclass_instances.

  Hint Extern 10 (ProvenBy (single_lhs _ _) (set_rhs _ _ _)) =>
    eapply single_lhs_provenby_set_rhs_other
    : typeclass_instances.

  Hint Extern 10 (ProvenBy (single_rhs _ _) (set_rhs _ _ _)) =>
    eapply single_rhs_provenby_set_rhs_other; [ done | ]
    : typeclass_instances.

  Hint Extern 10 (ProvenBy (single_rhs _ _) (set_lhs _ _ _)) =>
    eapply single_rhs_provenby_set_lhs_other
    : typeclass_instances.

  (* The "brand new [ss]" branch of [KDF_hyb_KDF_hyb_EVAL_true_equiv]'s
    non-coupling cases (idx < i and idx > i) all reduce, after the shared
    [get_ss_idx] bookkeeping (assigning [ss] index [cnt] on both sides) and
    a fresh, correlated [get_prk] sample (same [a] on both sides, since
    [ss] is fresh so both extract tables miss it), to re-establishing
    [KDF_hyb_EVAL_inv] at the jointly-updated heaps. This is one self
    -contained semantic fact, independent of the surrounding relational
    -Hoare bookkeeping, so it is proved once here (starting from a bare
    [KDF_hyb_EVAL_inv i (s0, s1)] fact obtained via [rpre_weaken_rule],
    rather than by chasing [ssprove_rem_rel] through the pending
    [set_lhs]/[set_rhs] wrappers a second time at the postcondition). *)
  Lemma KDF_hyb_EVAL_inv_fresh_extract_step i s0 s1 SIdx cnt (T T' : extract_loc) (ss0 : 'ss) (a : 'prk) :
    KDF_hyb_EVAL_inv i (s0, s1) ->
    get_heap s0 ss_index_loc = SIdx -> get_heap s1 ss_index_loc = SIdx ->
    get_heap s0 ss_count_loc = cnt -> get_heap s1 ss_count_loc = cnt ->
    get_heap s0 extract_loc = T -> get_heap s1 extract_loc = T' ->
    SIdx ss0 = None -> cnt <> i ->
    KDF_hyb_EVAL_inv i
      (set_heap (set_heap (set_heap s0 ss_count_loc cnt.+1) ss_index_loc (setm SIdx ss0 cnt))
        extract_loc (setm T ss0 a),
       set_heap (set_heap (set_heap s1 ss_count_loc cnt.+1) ss_index_loc (setm SIdx ss0 cnt))
        extract_loc (setm T' ss0 a)).
  Proof.
    move=> Hinv HSI0 HSI1 Hcnt0 Hcnt1 HT0 HT1 HSIss0 Hcnti.
    case: Hinv => [[[[Hig Hc1] Hc2] Hc3] Hc4].
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hc1.
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hc3.
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hc4.
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hc2.
    rewrite HSI0 HT0 in Hc1.
    rewrite HSI0 HT0 HT1 in Hc4.
    rewrite HSI0 HT0 in Hc3.
    have HT0ss0 : T ss0 = None.
    { move: (Hc1 ss0) => [Hf1 _]. exact: (Hf1 HSIss0). }
    have Hne0 : SIdx ss0 <> Some i by rewrite HSIss0.
    have HT1ss0 : T' ss0 = None.
    { move: (Hc4 ss0 Hne0) => Heq. rewrite -Heq. exact: HT0ss0. }
    split.
    1: split.
    2: {
      (* conjunct3: eval_key_loc pinning *)
      rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
      rewrite (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != extract_loc.1)) get_set_heap_eq get_set_heap_eq.
      rewrite (get_set_heap_neq _ _ _ _ (isT : eval_key_loc.1 != extract_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : eval_key_loc.1 != ss_index_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : eval_key_loc.1 != ss_count_loc.1)).
      move=> ss1 prk0.
      case Heqss: (ss1 == ss0).
      { move/eqP in Heqss. subst ss1. rewrite setmE eq_refl. move=> Hcontra. exfalso. apply: Hcnti. by case: Hcontra. }
      rewrite !setmE Heqss. exact: Hc3.
    }
    1: {
      split.
      { split.
        { (* heap_ignore *)
          move=> l Hl.
          have Hlext : l.1 != extract_loc.1.
          { apply/negP => /eqP Heq. move: Hl. rewrite domm_set domm_set domm0 in_fsetU in_fset1 in_fsetU in_fset1 Heq eq_refl orbT //. }
          rewrite (get_set_heap_neq _ _ _ _ Hlext) (get_set_heap_neq _ _ _ _ Hlext).
          apply: get_heap_after_common_double_update.
          exact: (Hig l Hl).
        }
        (* couple_lhs ss_index_loc extract_loc *)
        rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
        move=> ss1.
        rewrite (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != extract_loc.1)) get_set_heap_eq get_set_heap_eq.
        case Heqss: (ss1 == ss0).
        { move/eqP in Heqss. subst ss1. rewrite !setmE eq_refl. split; done. }
        rewrite !setmE Heqss. exact: (Hc1 ss1).
      }
      (* couple_rhs ss_count_loc eval_key_loc *)
      rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
      rewrite (get_set_heap_neq _ _ _ _ (isT : ss_count_loc.1 != extract_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : ss_count_loc.1 != ss_index_loc.1)).
      rewrite get_set_heap_eq.
      rewrite (get_set_heap_neq _ _ _ _ (isT : eval_key_loc.1 != extract_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : eval_key_loc.1 != ss_index_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : eval_key_loc.1 != ss_count_loc.1)).
      move=> Hle. apply: Hc2. rewrite Hcnt1. exact: (leq_trans (leqnSn cnt) Hle).
    }
    (* conjunct5: extract-agreement *)
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
    rewrite (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != extract_loc.1)) get_set_heap_eq get_set_heap_eq get_set_heap_eq.
    move=> ss1 Hss1ne.
    case Heqss: (ss1 == ss0).
    { move/eqP in Heqss. subst ss1. rewrite !setmE eq_refl //. }
    rewrite !setmE Heqss. apply: Hc4. move=> Hcontra. apply: Hss1ne. rewrite setmE Heqss. exact: Hcontra.
  Qed.

  (* The genuinely new sub-case: a brand new [ss] whose freshly-assigned
    index [cnt] equals [i] exactly. Here the LHS's [get_prk] sample lands
    in [extract_loc] while the RHS's [eval] sample lands in [eval_key_loc]
    instead -- the one place [extract_loc] and [eval_key_loc] genuinely
    diverge, which is exactly what the pinning conjunct (conjunct 3) is
    for: it is re-established directly from the fresh coupling ([T
    ss0 = Some a] on the LHS forces [eval_key_loc = Some a] on the RHS by
    definition, not by re-deriving it from anywhere), while for every
    OTHER [ss1] the old pinning conjunct together with the old
    [couple_rhs]-derived [eval_key_loc = None] (since [cnt <= i] here,
    with equality) rules out [SIdx ss1 = Some i] ever having already held
    -- so no other [ss1] can conflict with the freshly-assigned index. *)
  Lemma KDF_hyb_EVAL_inv_fresh_couple_step i s0 s1 SIdx cnt (T : extract_loc) (ss0 : 'ss) (a : 'prk) :
    KDF_hyb_EVAL_inv i (s0, s1) ->
    get_heap s0 ss_index_loc = SIdx -> get_heap s1 ss_index_loc = SIdx ->
    get_heap s0 ss_count_loc = cnt -> get_heap s1 ss_count_loc = cnt ->
    get_heap s0 extract_loc = T ->
    SIdx ss0 = None -> cnt = i ->
    KDF_hyb_EVAL_inv i
      (set_heap (set_heap (set_heap s0 ss_count_loc cnt.+1) ss_index_loc (setm SIdx ss0 cnt))
        extract_loc (setm T ss0 a),
       set_heap (set_heap (set_heap s1 ss_count_loc cnt.+1) ss_index_loc (setm SIdx ss0 cnt))
        eval_key_loc (Some a)).
  Proof.
    move=> Hinv HSI0 HSI1 Hcnt0 Hcnt1 HT0 HSIss0 Hcnti.
    case: Hinv => [[[[Hig Hc1] Hc2] Hc3] Hc4].
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hc1.
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hc3.
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hc4.
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hc2.
    rewrite HSI0 HT0 in Hc1.
    rewrite HSI0 HT0 in Hc4.
    rewrite HSI0 HT0 in Hc3.
    have HevalNone : get_heap s1 eval_key_loc = None.
    { apply: Hc2. rewrite Hcnt1 Hcnti. done. }
    split.
    1: split.
    2: {
      (* conjunct3: pinning *)
      rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
      rewrite (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != extract_loc.1)) get_set_heap_eq get_set_heap_eq.
      rewrite get_set_heap_eq.
      move=> ss1 prk0.
      case Heqss: (ss1 == ss0).
      { move/eqP in Heqss. subst ss1. rewrite setmE eq_refl setmE eq_refl. move=> _ [->]. done. }
      rewrite setmE Heqss setmE Heqss. move=> Hidxeq Hteq.
      move: (Hc3 ss1 prk0 Hidxeq Hteq) => Hcontra.
      exfalso. rewrite HevalNone in Hcontra. discriminate.
    }
    1: {
      split.
      { split.
        { (* heap_ignore *)
          move=> l Hl.
          have Hlext : l.1 != extract_loc.1.
          { apply/negP => /eqP Heq. move: Hl. rewrite domm_set domm_set domm0 in_fsetU in_fset1 in_fsetU in_fset1 Heq eq_refl orbT //. }
          have Hleval : l.1 != eval_key_loc.1.
          { apply/negP => /eqP Heq. move: Hl. rewrite domm_set domm_set domm0 in_fsetU in_fset1 in_fsetU in_fset1 Heq eq_refl //. }
          rewrite (get_set_heap_neq _ _ _ _ Hlext) (get_set_heap_neq _ _ _ _ Hleval).
          apply: get_heap_after_common_double_update.
          exact: (Hig l Hl).
        }
        (* couple_lhs ss_index_loc extract_loc, LHS only *)
        rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
        move=> ss1.
        rewrite (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != extract_loc.1)) get_set_heap_eq get_set_heap_eq.
        case Heqss: (ss1 == ss0).
        { move/eqP in Heqss. subst ss1. rewrite !setmE eq_refl. split; done. }
        rewrite !setmE Heqss. exact: (Hc1 ss1).
      }
      (* couple_rhs ss_count_loc eval_key_loc *)
      rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
      rewrite (get_set_heap_neq _ _ _ _ (isT : ss_count_loc.1 != eval_key_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : ss_count_loc.1 != ss_index_loc.1)).
      rewrite get_set_heap_eq get_set_heap_eq.
      move=> Hlt2.
      move: Hlt2.
      rewrite Hcnti ltnn.
      done.
    }
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
    rewrite (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != extract_loc.1)) get_set_heap_eq get_set_heap_eq.
    rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != eval_key_loc.1)).
    rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_index_loc.1)).
    rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_count_loc.1)).
    move=> ss1 Hne.
    case Heqss: (ss1 == ss0).
    { move/eqP in Heqss. subst ss1. rewrite setmE eq_refl in Hne. exfalso. apply: Hne. by rewrite Hcnti. }
    rewrite setmE Heqss. apply: Hc4. move=> Hcontra. apply: Hne. rewrite setmE Heqss. exact: Hcontra.
  Qed.

  (** STATUS: complete. The [ss]-indexing redesign above (decoupling
    [get_ss_idx] from [get_prk]) is correct and sufficient, and
    [KDF_hyb_KDF_hyb_EVAL_true_equiv] above is now fully proved (no
    admits). The fix that was needed (and has been applied to
    [KDF_hyb_EVAL_inv] above): exclude [extract_loc] from the
    [heap_ignore] set (i.e. [heap_ignore [fmap eval_key_loc;
    extract_loc]]) and add a fifth conjunct recording the weaker fact
    that actually holds -- the two copies of [extract_loc] agree
    pointwise at every [ss0] EXCEPT possibly the one (at most one, ever)
    with index exactly [i]:
      [rel_app [:: (lhs, ss_index_loc); (lhs, extract_loc); (rhs, extract_loc)]
        (fun SIdx T T' => forall ss0, SIdx ss0 <> Some i -> T ss0 = T' ss0)].
    This is exactly what the newly-discovered-[ss]-at-[i] branch
    ([KDF_hyb_EVAL_inv_fresh_couple_step] below) re-establishes, and what
    every OTHER branch ([KDF_hyb_EVAL_inv_fresh_extract_step] for the
    non-coupling "brand new [ss]" cases, plus the "idx already known"
    cases inline below) uses to justify reading [extract_loc] via
    separate [r_get_remember_lhs]/[r_get_remember_rhs] instead of the
    (no longer available) shared [r_get_vs_get_remember]. Two small
    generic helper-lemma families were added above to make this
    mechanical: [single_{lhs,rhs}_provenby_set_{lhs,rhs}_other] (so
    [ssprove_rem_rel]/[r_rem_rel] can see a [single_lhs]/[single_rhs]
    fact for [extract_loc]/[eval_key_loc] through the pending
    [set_lhs]/[set_rhs] wrappers left by [get_ss_idx]'s own puts), and
    the two dedicated invariant-transition lemmas
    [KDF_hyb_EVAL_inv_fresh_extract_step] /
    [KDF_hyb_EVAL_inv_fresh_couple_step] (proving [KDF_hyb_EVAL_inv] is
    re-established after a brand new [ss]'s bookkeeping + sample, in the
    non-coupling and coupling cases respectively). *)
  Lemma KDF_hyb_KDF_hyb_EVAL_true_equiv i :
    KDF_hyb i ≈₀ KDF_hyb_EVAL i ∘ EVAL true.
  Proof.
    apply eq_rel_perf_ind with (KDF_hyb_EVAL_inv i).
    - eapply Invariant_inv_conj;
      [ eapply Invariant_inv_conj;
        [ eapply Invariant_inv_conj;
          [ eapply Invariant_inv_conj;
            [ eapply Invariant_heap_ignore; fmap_solve
            | eapply SemiInvariant_relApp; [ simpl; repeat split; try fmap_solve; try done | done ] ]
          | eapply SemiInvariant_relApp; [ simpl; repeat split; try fmap_solve; try done | done ] ]
        | eapply SemiInvariant_relApp; [ simpl; repeat split; try fmap_solve; try done | done ] ]
      | eapply SemiInvariant_relApp; [ simpl; repeat split; try fmap_solve; try done | done ] ].
    - simplify_eq_rel arg.
      destruct arg as [ss info].
      ssprove_code_simpl.
      apply: r_get_vs_get_remember => SIdx.
      case Hidx: (SIdx ss) => [idx|] /=.
      { (* [ss] already has an assigned index [idx] -- a repeat query. *)
        case Hlt: (idx < i)%N.
        { (* idx < i: both sides take the [mid_loc] lazy-random branch. *)
          apply: r_get_remember_lhs => T.
          apply: r_get_remember_rhs => T'.
          have Hne : SIdx ss <> Some i by rewrite Hidx; move=> [Heq]; move: Hlt; rewrite Heq ltnn.
          ssprove_rem_rel 0%N => Heq5.
          move: (Heq5 ss Hne) => HTeq.
          ssprove_rem_rel 3%N => Hc1.
          move: (Hc1 ss) => Hc1'. rewrite Hidx in Hc1'.
          have HTne : T ss <> None.
          { move=> Habs. case: Hc1' => [_ Hf2]. move: (Hf2 Habs) => //. }
          case Hprk: (T ss) HTeq => [prk|] HTeq.
          2: { exfalso. by apply: HTne. }
          rewrite -HTeq /=.
          apply: r_get_vs_get_remember => T2.
          case: (T2 (prk, info)) => [y|].
          { apply: r_ret => s0 s1 h. split; [reflexivity|]. extract_base_inv h. }
          apply: r_uniform_bij => [|y']. 1: exists id; done.
          apply: r_put_vs_put.
          ssprove_restore_mem; last by apply: r_ret.
          eapply preserve_update_mem_conj;
          [ eapply preserve_update_mem_conj;
            [ eapply preserve_update_mem_conj;
              [ eapply preserve_update_mem_conj;
                [ ssprove_invariant
                | eapply preserve_update_mem_rel; ssprove_invariant ]
              | eapply preserve_update_mem_rel; ssprove_invariant ]
            | eapply preserve_update_mem_rel; ssprove_invariant ]
          | eapply preserve_update_mem_rel; ssprove_invariant
          ] ; done.
        }
        (* idx >= i *)
        case Hcmp: (idx == i).
        { (* idx == i: LHS takes the real branch, RHS calls [eval]; couple
            LHS's cached [prk] against RHS's (already-pinned) [eval_key_loc]. *)
          ssprove_code_simpl.
          apply: r_get_remember_lhs => T.
          apply: r_get_remember_rhs => k.
          ssprove_rem_rel 3%N => Hc1.
          move: (Hc1 ss) => Hc1'. rewrite Hidx in Hc1'.
          have HTne : T ss <> None.
          { move=> Habs. case: Hc1' => [_ Hf2]. move: (Hf2 Habs) => //. }
          move/eqP in Hcmp. subst idx.
          case Hprk: (T ss) => [prk|].
          2: { exfalso. by apply: HTne. }
          ssprove_rem_rel 1%N => Hc3.
          move: (Hc3 ss prk Hidx Hprk) => Hkeq.
          rewrite Hkeq /=.
          apply: r_ret => s0 s1 h. split; [reflexivity|]. extract_base_inv h.
        }
        (* idx > i: both sides take the real-PRF branch. *)
        apply: r_get_remember_lhs => T.
        apply: r_get_remember_rhs => T'.
        have Hne : SIdx ss <> Some i by rewrite Hidx; move=> [Heq]; move: Hcmp; rewrite Heq eq_refl.
        ssprove_rem_rel 0%N => Heq5.
        move: (Heq5 ss Hne) => HTeq.
        ssprove_rem_rel 3%N => Hc1.
        move: (Hc1 ss) => Hc1'. rewrite Hidx in Hc1'.
        have HTne : T ss <> None.
        { move=> Habs. case: Hc1' => [_ Hf2]. move: (Hf2 Habs) => //. }
        case Hprk: (T ss) HTeq => [prk|] HTeq.
        2: { exfalso. by apply: HTne. }
        rewrite -HTeq /=.
        apply: r_ret => s0 s1 h. split; [reflexivity|]. extract_base_inv h.
      }
      (* [ss] is brand new: [get_ss_idx] assigns it a fresh index [v0]. *)
      apply: r_get_vs_get_remember => cnt.
      eapply rpre_weaken_rule with (pre := fun '(s0,s1) =>
        ((KDF_hyb_EVAL_inv i ⋊ rem_lhs ss_index_loc SIdx ⋊ rem_rhs ss_index_loc SIdx
         ⋊ rem_lhs ss_count_loc cnt ⋊ rem_rhs ss_count_loc cnt)
        ⋊ single_lhs extract_loc (fun T : extract_loc => T ss = None)
        ⋊ single_rhs extract_loc (fun T' : extract_loc => T' ss = None)
        ⋊ single_rhs eval_key_loc (fun k : eval_key_loc => (cnt <= i)%N -> k = None)) (s0,s1)).
      2: {
        move=> s0 s1 Hcur.
        case: (Hcur) => [[[[Hinv HSI0] HSI1] Hcnt0] Hcnt1].
        case: Hinv => [[[[Hig Hc1] Hc2] Hc3] Hc4].
        rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hc1.
        rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hc4.
        rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hc2.
        rewrite /rem_inv /get_side /= in HSI0.
        rewrite HSI0 in Hc1.
        have HT0 : get_heap s0 extract_loc ss = None.
        { move: (Hc1 ss) => [Hf1 _]. apply: Hf1. exact: Hidx. }
        have Hne : SIdx ss <> Some i by rewrite Hidx.
        move: (Hc4 ss) => Hc4'. rewrite HSI0 in Hc4'.
        have HT1 : get_heap s1 extract_loc ss = None.
        { rewrite -(Hc4' Hne). exact: HT0. }
        have HevalNone : (cnt <= i)%N -> get_heap s1 eval_key_loc = None.
        { rewrite /rem_inv /get_side /= in Hcnt1. rewrite -Hcnt1. exact: Hc2. }
        split; [split; [split; [exact: Hcur | rewrite (rel_app_cons) (rel_app_nil) /=; exact: HT0]
                        | rewrite (rel_app_cons) (rel_app_nil) /=; exact: HT1]
                | rewrite (rel_app_cons) (rel_app_nil) /=; exact: HevalNone].
      }
      apply: r_put_vs_put.
      apply: r_put_vs_put.
      case Hlt: (cnt < i)%N.
      1: {
        (* fresh [ss], newly-assigned idx = cnt < i: mirrors the "idx known,
          idx < i" case above, but [get_prk]'s sample is now genuinely fresh
          (both [T ss] and [T' ss] are [None], since [ss] itself is new). *)
        apply: r_get_remember_lhs => T.
        apply: r_get_remember_rhs => T'.
        eapply (@r_rem_rel _ _ [:: (lhs, extract_loc)] (fun T0 : extract_loc => T0 ss = None));
          [ typeclasses eauto | typeclasses eauto | move=> HT0 ].
        eapply (@r_rem_rel _ _ [:: (rhs, extract_loc)] (fun T0 : extract_loc => T0 ss = None));
          [ typeclasses eauto | typeclasses eauto | move=> HT1 ].
        rewrite HT0 HT1 /=.
        apply: r_uniform_bij => [|a]. 1: exists id; done.
        apply: r_put_vs_put.
        apply: r_get_vs_get_remember => T2.
        case: (T2 (a, info)) => [y|].
        { apply: r_ret => s0 s1 h.
          case: h => [[hset _] _].
          case: hset => [s1a [hset1 Es1]].
          case: hset1 => [s0a [hset2 Es0]].
          case: hset2 => [[hset3 HremT] HremT'].
          case: hset3 => [s1b [hset4 Es1b]].
          case: hset4 => [s0b [hset5 Es0b]].
          case: hset5 => [s1c [hset6 Es1c]].
          case: hset6 => [s0c [hbase Es0c]].
          subst.
          rewrite /rem_inv /get_side /= in HremT HremT'.
          have HT0eq : get_heap s0c extract_loc = T.
          { rewrite -HremT (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_index_loc.1))
              (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_count_loc.1)). done. }
          have HT1eq : get_heap s1c extract_loc = T'.
          { rewrite -HremT' (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_index_loc.1))
              (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_count_loc.1)). done. }
          move: hbase => [[[[[[[Hinv HSI0] HSI1] Hcnt0] Hcnt1] _] _] _].
          rewrite /rem_inv /get_side /= in HSI0 HSI1 Hcnt0 Hcnt1.
          split; [reflexivity|].
          apply: (KDF_hyb_EVAL_inv_fresh_extract_step _ _ _ _ _ _ _ _ _ Hinv HSI0 HSI1 Hcnt0 Hcnt1 HT0eq HT1eq Hidx).
          move=> Heq. move: Hlt. rewrite Heq ltnn. done.
        }
        apply: r_uniform_bij => [|y']. 1: exists id; done.
        apply: r_put_vs_put.
        apply: r_ret => s0 s1 h. split; [reflexivity|].
        case: h => [s1x [hset0 Es1x]].
        case: hset0 => [s0x [hset00 Es0x]].
        case: hset00 => [[hset _] _].
        case: hset => [s1a [hset1 Es1]].
        case: hset1 => [s0a [hset2 Es0]].
        case: hset2 => [[hset3 HremT] HremT'].
        case: hset3 => [s1b [hset4 Es1b]].
        case: hset4 => [s0b [hset5 Es0b]].
        case: hset5 => [s1c [hset6 Es1c]].
        case: hset6 => [s0c [hbase Es0c]].
        subst.
        rewrite /rem_inv /get_side /= in HremT HremT'.
        have HT0eq : get_heap s0c extract_loc = T.
        { rewrite -HremT (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_index_loc.1))
            (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_count_loc.1)). done. }
        have HT1eq : get_heap s1c extract_loc = T'.
        { rewrite -HremT' (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_index_loc.1))
            (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_count_loc.1)). done. }
        move: hbase => [[[[[[[Hinv HSI0] HSI1] Hcnt0] Hcnt1] _] _] _].
        rewrite /rem_inv /get_side /= in HSI0 HSI1 Hcnt0 Hcnt1.
        have Hcnti : cnt <> i.
        { move=> Heq. move: Hlt. rewrite Heq ltnn. done. }
        have Hpre := KDF_hyb_EVAL_inv_fresh_extract_step _ _ _ _ _ _ _ _ a Hinv HSI0 HSI1 Hcnt0 Hcnt1 HT0eq HT1eq Hidx Hcnti.
        case: Hpre => [[[[Hig Hc1] Hc2] Hc3] Hc4].
        split.
        1: split.
        2: {
          rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
          rewrite (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != mid_loc.1)).
          rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != mid_loc.1)).
          rewrite (get_set_heap_neq _ _ _ _ (isT : eval_key_loc.1 != mid_loc.1)).
          exact: Hc3.
        }
        1: {
          split.
          { split.
            { move=> l Hl.
              case: (eqVneq l.1 mid_loc.1) => Hml.
              { rewrite /get_heap /set_heap !setmE Hml eq_refl //. }
              rewrite (get_set_heap_neq _ _ _ _ Hml) (get_set_heap_neq _ _ _ _ Hml).
              exact: (Hig l Hl).
            }
            rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
            rewrite (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != mid_loc.1)).
            rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != mid_loc.1)).
            exact: Hc1.
          }
          rewrite (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
          rewrite (get_set_heap_neq _ _ _ _ (isT : ss_count_loc.1 != mid_loc.1)).
          rewrite (get_set_heap_neq _ _ _ _ (isT : eval_key_loc.1 != mid_loc.1)).
          exact: Hc2.
        }
        rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
        rewrite (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != mid_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != mid_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != mid_loc.1)).
        exact: Hc4.
      }
      (* fresh [ss], newly-assigned idx = cnt >= i. *)
      case Hcmp: (cnt == i).
      2: {
        (* fresh [ss], newly-assigned idx = cnt > i: mirrors the "idx
          known, idx > i" case, extract-only, no [mid_loc]. *)
        apply: r_get_remember_lhs => T.
        apply: r_get_remember_rhs => T'.
        eapply (@r_rem_rel _ _ [:: (lhs, extract_loc)] (fun T0 : extract_loc => T0 ss = None));
          [ typeclasses eauto | typeclasses eauto | move=> HT0 ].
        eapply (@r_rem_rel _ _ [:: (rhs, extract_loc)] (fun T0 : extract_loc => T0 ss = None));
          [ typeclasses eauto | typeclasses eauto | move=> HT1 ].
        rewrite HT0 HT1 /=.
        apply: r_uniform_bij => [|a]. 1: exists id; done.
        apply: r_put_vs_put.
        apply: r_ret => s0 s1 h. split; [reflexivity|].
        case: h => [s1a [hset1 Es1]].
        case: hset1 => [s0a [hset2 Es0]].
        case: hset2 => [[hset3 HremT] HremT'].
        case: hset3 => [s1b [hset4 Es1b]].
        case: hset4 => [s0b [hset5 Es0b]].
        case: hset5 => [s1c [hset6 Es1c]].
        case: hset6 => [s0c [hbase Es0c]].
        subst.
        rewrite /rem_inv /get_side /= in HremT HremT'.
        have HT0eq : get_heap s0c extract_loc = T.
        { rewrite -HremT (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_index_loc.1))
            (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_count_loc.1)). done. }
        have HT1eq : get_heap s1c extract_loc = T'.
        { rewrite -HremT' (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_index_loc.1))
            (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_count_loc.1)). done. }
        move: hbase => [[[[[[[Hinv HSI0] HSI1] Hcnt0] Hcnt1] _] _] _].
        rewrite /rem_inv /get_side /= in HSI0 HSI1 Hcnt0 Hcnt1.
        apply: (KDF_hyb_EVAL_inv_fresh_extract_step _ _ _ _ _ _ _ _ _ Hinv HSI0 HSI1 Hcnt0 Hcnt1 HT0eq HT1eq Hidx).
        move=> Heq. move: Hcmp. rewrite Heq eq_refl. done.
      }
      (* fresh [ss], newly-assigned idx = cnt = i: the genuinely new
        coupling case -- LHS's [get_prk] sample is coupled directly
        against RHS's [eval]'s own first-use key sample. *)
      ssprove_code_simpl.
      apply: r_get_remember_lhs => T.
      apply: r_get_remember_rhs => k.
      eapply (@r_rem_rel _ _ [:: (lhs, extract_loc)] (fun T0 : extract_loc => T0 ss = None));
        [ typeclasses eauto | typeclasses eauto | move=> HT0 ].
      eapply (@r_rem_rel _ _ [:: (rhs, eval_key_loc)] (fun k0 : eval_key_loc => (cnt <= i)%N -> k0 = None));
        [ typeclasses eauto | typeclasses eauto | move=> Hkfun ].
      have Hkeq : k = None.
      { apply: Hkfun. move/eqP in Hcmp. by rewrite Hcmp. }
      rewrite HT0 Hkeq /=.
      apply: r_uniform_bij => [|a]. 1: exists id; done.
      apply: r_put_vs_put.
      apply: r_ret => s0 s1 h. split; [reflexivity|].
      case: h => [s1a [hset1 Es1]].
      case: hset1 => [s0a [hset2 Es0]].
      case: hset2 => [[hset3 HremT] HremK].
      case: hset3 => [s1b [hset4 Es1b]].
      case: hset4 => [s0b [hset5 Es0b]].
      case: hset5 => [s1c [hset6 Es1c]].
      case: hset6 => [s0c [hbase Es0c]].
      subst.
      rewrite /rem_inv /get_side /= in HremT.
      have HT0eq : get_heap s0c extract_loc = T.
      { rewrite -HremT (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_index_loc.1))
          (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_count_loc.1)). done. }
      move: hbase => [[[[[[[Hinv HSI0] HSI1] Hcnt0] Hcnt1] _] _] _].
      rewrite /rem_inv /get_side /= in HSI0 HSI1 Hcnt0 Hcnt1.
      have Hcnti : cnt = i by move/eqP in Hcmp.
      apply: (KDF_hyb_EVAL_inv_fresh_couple_step _ _ _ _ _ _ _ _ Hinv HSI0 HSI1 Hcnt0 Hcnt1 HT0eq Hidx Hcnti).
  Qed.

  (** HISTORICAL NOTE (kept as documentation): an earlier draft of this
    file stated a lemma [KDF_hyb_KDF_hyb_EVAL_false_equiv] here, claiming
    a perfect [≈₀] equivalence for the EVAL-false leg of the hybrid hop.
    That statement was FALSE, not merely hard to prove -- see the
    concrete counterexample below -- and the lemma has been REMOVED,
    replaced by the per-hop up-to-bad treatment introduced right after
    this comment. The analysis is kept because it explains WHY the
    up-to-bad detour (and its [q * birthday_bound q] cost) exists.

    At first glance the removed claim looks like the mirror image of
    [KDF_hyb_KDF_hyb_EVAL_true_equiv]: composing [KDF_hyb_EVAL i] with
    the *ideal* oracle [EVAL false] instead of [EVAL true], hoping that
    [eval_tbl_loc]'s lazily-sampled table reproduces exactly what
    [KDF_hyb i.+1]'s own "idx <= i" branch does for the [ss] at index
    [i]. But [EVAL_pkg_ff]'s [eval_tbl_loc] is keyed ONLY by [info] --
    an independent random function private to that one [ss] -- whereas
    [KDF_hyb i.+1]'s ideal branch answers through [mid_loc], keyed by
    [(prk, info)] and hence SHARED, by design, across every [ss] that
    happens to have been assigned the same [prk] by Extract. These two
    tables coincide only for as long as no OTHER [ss] ever collides
    with [prk_i] (the [prk] Extract assigns to the index-[i] shared
    secret) -- exactly the "bad" event [KDF_mid]/[KDF_ideal]'s own
    birthday argument exists to bound (see the file header and
    [KDF_mid]'s docstring above: "If Extract does produce such a
    collision, the two games can diverge, which is exactly the
    birthday event we need to bound."). [KDF_hyb_KDF_hyb_EVAL_true_equiv]
    has no such issue only because [EVAL_pkg_tt]'s real branch computes
    the PUBLIC, DETERMINISTIC [PRF info prk] -- a pure function of
    whatever [prk] value is in play, colliding or not -- so it agrees
    with [KDF_hyb]'s own real-PRF branch regardless of collisions.
    [EVAL_pkg_ff]'s table has no such prk-keyed sharing, so the same
    argument does not carry over to the ideal side.

    This is not a defect specific to some clever adversary strategy or
    to some subtle probability tail bound: it is a FLAT-OUT FALSE claim
    already at [PRK_N = 1] (i.e. [prk_n = 0], a perfectly legal
    instantiation of this section's [Context], under which [get_prk]
    is forced to return the unique [PRK] value for every [ss], with
    probability 1 -- no "birthday" needed). Concretely, fix any [i]
    with at least one [ss] already assigned an index below it (e.g.
    [i := 1]), pick two DISTINCT shared secrets [ssA], [ssB] (needs
    [SS_N >= 2], i.e. [ss_n >= 1], again unconstrained by the section)
    and one [info] value [x], and consider the two-query adversary:
      1. query [(ssA, x)]: both sides take the "idx < i" / "idx < i.+1"
         [mid_loc] branch verbatim (identical code, identical coupled
         [get_prk]/lazy-sample steps), landing on some fixed value [y1]
         with [extract_loc ssA = p] (the unique [PRK] value, forced,
         since [PRK_N = 1]) and [mid_loc (p, x) = y1] on BOTH sides.
      2. query [(ssB, x)]: [ssB] is brand new, so [get_ss_idx] hands it
         the fresh index exactly [i] -- the "coupling" branch.
         - LHS ([KDF_hyb_EVAL i ∘ EVAL false]): routes to [eval x],
           i.e. [EVAL_pkg_ff]; [eval_tbl_loc] has never been touched
           (it is entirely disjoint from [mid_loc]), so this SAMPLES A
           FRESH, independent value [z1 <$ uniform Out_N] and returns
           it.
         - RHS ([KDF_hyb i.+1]): [get_prk ssB] samples from [uniform
           PRK_N = uniform 1], which is FORCED (not just likely) to
           equal [p], the SAME value [ssA] already got. The very next
           step, [mid_loc]'s lookup at [(p, x)], HITS THE EXISTING
           ENTRY from query 1 and returns the ALREADY-FIXED value [y1]
           -- no sampling happens at all on this branch.
    So the two games' outputs on query 2 are [z1] (fresh, uniform over
    [Out], independent of [y1]) versus [y1] (already fixed by query 1).
    Whenever [Out_N > 1] (i.e. [out_n >= 1]), [Pr[z1 = y1] = 1 / Out_N
    < 1], so this two-query adversary distinguishes the two games with
    advantage [1 - 1/Out_N > 0] -- contradicting [≈₀] (0-advantage,
    i.e. the two games must be EXACTLY equal in distribution against
    every adversary) outright, for this legal choice of parameters.

    Root cause: [KDF_hyb]/[KDF_hyb_EVAL] were deliberately redesigned
    to index hybrids by DISTINCT SHARED SECRET rather than by distinct
    [prk] (see the long comment on [KDF_hyb] above) specifically to
    make [KDF_hyb_KDF_hyb_EVAL_true_equiv]'s coupling work -- "indexing
    by [prk] instead forces the [prk] sample to happen first ... leaving
    nothing left on the LHS to couple against." But the file's own
    header roadmap explicitly describes hop 1 as a hybrid "over the <=
    q distinct [prk]'s Extract can produce" precisely so that swapping
    one instance never needs the birthday assumption. Indexing by [ss]
    instead reintroduces exactly the prk-collision hazard the roadmap's
    original per-[prk] indexing was designed to avoid, but ONLY on the
    ideal side (the real side is immune, as explained above) -- so the
    [true_equiv] fix (dropping [extract_loc]/[eval_key_loc] from
    [heap_ignore] and tracking their pointwise-except-at-[i] agreement)
    does NOT have an analogous fix here: no invariant relating
    [eval_tbl_loc] and [mid_loc] can be both (a) actually implied by
    the two packages' own step-by-step semantics and (b) strong enough
    to make their outputs agree, because [KDF_hyb_EVAL]'s own "idx < i"
    branch code has, and can have, no way to know or check whether some
    other [ss]'s [prk] happens to equal [prk_i] -- that information is
    exactly what [EVAL] as a black box is supposed to hide.

    Repairing this needs option (1) from an earlier draft of this
    comment: weakening this lemma's conclusion to an approximate bound
    with an added birthday-style error term (mirroring
    [KDF_mid_KDF_ideal_bound]'s [birthday_bound q]), propagated through
    [KDF_hyb_bound]/[KDF_real_KDF_mid_bound]/[security_of_KDF]
    downstream. That is implemented below: [KDF_hyb_KDF_hyb_EVAL_false_equiv]
    is GONE (it was false, not merely hard), replaced by a per-hop
    up-to-bad treatment ([get_prk_bad], [KDF_hyb_bad], [KDF_hybE_bad],
    and the lemmas culminating in [KDF_hyb_EVAL_false_bound]) reusing
    [KDF_mid]/[KDF_mid']/[KDF_bad]'s own birthday/collision machinery
    one hybrid hop at a time. (Redesigning [KDF_hyb]/[KDF_hyb_EVAL] to
    index by distinct [prk] instead, option (2) from that earlier draft,
    remains possible future work, orthogonal to what is done here.) *)

  (* --- weakening false_equiv: the per-hop up-to-bad replacement ---

    [KDF_hyb_EVAL i ∘ EVAL false] and [KDF_hyb i.+1] agree exactly UNTIL
    Extract assigns the same [prk] to two distinct shared secrets (see the
    counterexample analysis above: divergence needs some other [ss] to
    collide with [prk_i]). We therefore replay the step-2b/2c recipe
    ([KDF_mid] / [KDF_mid'] / [KDF_bad]) one hybrid hop at a time:

      KDF_hyb_EVAL i ∘ EVAL false  ≈₀  KDF_hybE_bad i        (ghost inlining)
      AdvantageE (KDF_hybE_bad i) (KDF_hyb_bad i.+1) A
          <= Pr_bad (A ∘ KDF_hybE_bad i) 4 true              (Fundamental Lemma)
      KDF_hyb_bad i.+1  ≈₀  KDF_hyb i.+1                     (ghost erasure)

    The bad event is deliberately the COARSE one KDF_bad/KDF_mid' already
    track -- "Extract hands an already-used prk to a second distinct ss" --
    rather than the tight "...colliding with prk_i specifically": the coarse
    event contains the tight one, is trackable by code IDENTICAL to
    KDF_mid''s (so [used_prk_loc]/[bad_loc]/bad_id 4 and the whole
    pkg_upto_bad + Birthday machinery are reused verbatim), and is still
    bounded by [birthday_bound q] per hop under [COUNT q]. Cost: the final
    theorem picks up [q * birthday_bound q] instead of a per-hop
    [q/PRK_N]-style term summing to one birthday bound -- same asymptotic
    flavour, strictly simpler proof; tightening the event to "collides
    with prk_i" is possible future work. *)

  (* [get_prk] plus KDF_mid'/KDF_bad's verbatim collision bookkeeping:
    the fresh branch registers the sampled prk in [used_prk_loc] and
    flips [bad_loc] on a repeat. Shared by both instrumented games so
    they maintain extract_loc/used_prk_loc/bad_loc IDENTICALLY. *)
  Definition get_prk_bad (ss : 'ss) : raw_code 'prk :=
    T ← get extract_loc ;;
    match getm T ss with
    | Some prk => ret prk
    | None =>
        prk <$ uniform PRK_N ;;
        #put extract_loc := setm T ss prk ;;
        Used ← get used_prk_loc ;;
        match getm Used prk with
        | None => #put used_prk_loc := setm Used prk tt ;; ret prk
        | Some _ => #put bad_loc := true ;; ret prk
        end
    end.

  Lemma get_prk_bad_valid {L I} (ss : 'ss) :
    fhas L extract_loc -> fhas L used_prk_loc -> fhas L bad_loc ->
    ValidCode L I (get_prk_bad ss).
  Proof.
    move=> H1 H2 H3.
    rewrite /get_prk_bad.
    apply: valid_getr => [// | T].
    case: (getm T ss) => [prk|].
    - by apply: valid_ret.
    - apply: valid_sampler => prk.
      apply: valid_putr => //.
      apply: valid_getr => [// | Used].
      case: (getm Used prk) => [u|].
      + apply: valid_putr => //. by apply: valid_ret.
      + apply: valid_putr => //. by apply: valid_ret.
  Qed.

  Hint Extern 1 (ValidCode ?L ?I (get_prk_bad ?ss)) =>
    eapply get_prk_bad_valid ; [ fmap_solve | fmap_solve | fmap_solve ]
    : typeclass_instances ssprove_valid_db.

  (* [KDF_hyb j] carrying the ghost collision bookkeeping (the analogue of
    KDF_mid -> KDF_mid'). Output-wise identical to [KDF_hyb j]. *)
  Definition KDF_hyb_bad_locs :=
    [fmap extract_loc; mid_loc; ss_count_loc; ss_index_loc; bad_loc; used_prk_loc].

  Definition KDF_hyb_bad (j : nat) : game DERIVE_export :=
    [package KDF_hyb_bad_locs ;
      #def #[ DERIVE ] ('(ss, info) : 'ss × 'info) : 'out
      {
        idx ← get_ss_idx ss ;;
        if ltn idx j then
          prk ← get_prk_bad ss ;;
          T2 ← get mid_loc ;;
          match getm T2 (prk, info) with
          | Some y => ret y
          | None =>
              y <$ uniform Out_N ;;
              #put mid_loc := setm T2 (prk, info) y ;;
              ret y
          end
        else
          prk ← get_prk_bad ss ;;
          ret (PRF info prk)
      }
    ].

  (* Monolithic inlining of [KDF_hyb_EVAL i ∘ EVAL false], instrumented:
    - [EVAL false]'s [eval_tbl_loc] table is inlined verbatim in the
      "idx == i" branch;
    - that branch ADDITIONALLY runs [get_prk_bad ss] as GHOST code (its
      result is discarded; output still comes from [eval_tbl_loc]), so
      the index-i shared secret's prk exists in [extract_loc] and takes
      part in the collision bookkeeping -- without this the two sides
      could not keep [bad_loc] in sync ([KDF_hyb_bad i.+1] genuinely
      extracts that ss);
    - the other two branches use [get_prk_bad] in place of [get_prk]. *)
  Definition KDF_hybE_bad_locs :=
    [fmap extract_loc; mid_loc; ss_count_loc; ss_index_loc; bad_loc;
          used_prk_loc; eval_tbl_loc].

  Definition KDF_hybE_bad (i : nat) : game DERIVE_export :=
    [package KDF_hybE_bad_locs ;
      #def #[ DERIVE ] ('(ss, info) : 'ss × 'info) : 'out
      {
        idx ← get_ss_idx ss ;;
        if ltn idx i then
          prk ← get_prk_bad ss ;;
          T2 ← get mid_loc ;;
          match getm T2 (prk, info) with
          | Some y => ret y
          | None =>
              y <$ uniform Out_N ;;
              #put mid_loc := setm T2 (prk, info) y ;;
              ret y
          end
        else if (idx : nat) == i then
          prk ← get_prk_bad ss ;;   (* ghost: result unused, bookkeeping only *)
          T ← get eval_tbl_loc ;;
          match getm T info with
          | Some y => ret y
          | None =>
              y <$ uniform Out_N ;;
              #put eval_tbl_loc := setm T info y ;;
              ret y
          end
        else
          prk ← get_prk_bad ss ;;
          ret (PRF info prk)
      }
    ].

  (* --- ghost erasure: [KDF_hyb_bad j] ≈₀ [KDF_hyb j] ---
    Mirror of [KDF_mid_KDF_mid'_equiv]: eq_rel_perf_ind_ignore on
    [fmap bad_loc; used_prk_loc]; every branch is identical code except
    the RHS-only Used/bad writes inside get_prk_bad's fresh branch. *)
  Lemma KDF_hyb_bad_KDF_hyb_equiv j :
    KDF_hyb_bad j ≈₀ KDF_hyb j.
  Proof.
    apply eq_rel_perf_ind_ignore with [fmap bad_loc; used_prk_loc].
    1: fmap_solve.
    simplify_eq_rel arg.
    destruct arg as [ss info].
    apply: r_get_vs_get_remember => v.
    case: (getm v ss) => [idx|].
    - simpl.
      case: (idx < j)%N.
      + apply: r_get_vs_get_remember => v0.
        case: (getm v0 ss) => [prk|].
        * simpl.
          apply: r_get_vs_get_remember => T2.
          case: (getm T2 (prk, info)) => [y|].
          -- simpl. apply: r_ret => s0 s1 h. split; [reflexivity | extract_base_inv h].
          -- simpl. apply: r_uniform_bij => [|y]. 1: exists id; done.
             apply: r_put_vs_put.
             ssprove_restore_mem; last by apply: r_ret.
             by ssprove_invariant.
        * apply: r_uniform_bij => [|prk']. 1: exists id; done.
          apply: r_put_vs_put.
          ssprove_restore_mem; [by ssprove_invariant | ].
          apply: r_get_remember_lhs => Used.
          case: (getm Used prk') => [[]|].
          all: apply: r_put_lhs.
          all: ssprove_restore_mem; [by ssprove_invariant | ].
          all: apply: r_get_vs_get_remember => T2.
          all: case: (getm T2 (prk', info)) => [y|].
          all: try (
            apply: r_ret => s0 s1 h ;
            split ; [ reflexivity | extract_base_inv h ]
          ).
          all: apply: r_uniform_bij => [|y0]; [ exists id; done | ].
          all: apply: r_put_vs_put.
          all: ssprove_restore_mem; last by apply: r_ret.
          all: by ssprove_invariant.
      + apply: r_get_vs_get_remember => v0.
        case: (getm v0 ss) => [prk|].
        * simpl. apply: r_ret => s0 s1 h. split; [reflexivity | extract_base_inv h].
        * apply: r_uniform_bij => [|prk']. 1: exists id; done.
          apply: r_put_vs_put.
          ssprove_restore_mem; [by ssprove_invariant | ].
          apply: r_get_remember_lhs => Used.
          case: (getm Used prk') => [[]|].
          -- apply: r_put_lhs.
             ssprove_restore_mem; [by ssprove_invariant | ].
             apply: r_ret => s0 s1 h. split; [reflexivity | extract_base_inv h].
          -- apply: r_put_lhs.
             ssprove_restore_mem; [by ssprove_invariant | ].
             apply: r_ret => s0 s1 h. split; [reflexivity | extract_base_inv h].
    - apply: r_get_vs_get_remember => cnt.
      apply: r_put_vs_put.
      apply: r_put_vs_put.
      ssprove_restore_mem; [by ssprove_invariant | ].
      simpl.
      case: (cnt < j)%N.
      + apply: r_get_vs_get_remember => v0.
        case: (getm v0 ss) => [prk|].
        * simpl.
          apply: r_get_vs_get_remember => T2.
          case: (getm T2 (prk, info)) => [y|].
          -- simpl. apply: r_ret => s0 s1 h. split; [reflexivity | extract_base_inv h].
          -- simpl. apply: r_uniform_bij => [|y]. 1: exists id; done.
             apply: r_put_vs_put.
             ssprove_restore_mem; last by apply: r_ret.
             by ssprove_invariant.
        * apply: r_uniform_bij => [|prk']. 1: exists id; done.
          apply: r_put_vs_put.
          ssprove_restore_mem; [by ssprove_invariant | ].
          apply: r_get_remember_lhs => Used.
          case: (getm Used prk') => [[]|].
          -- apply: r_put_lhs.
             ssprove_restore_mem; [by ssprove_invariant | ].
             apply: r_get_vs_get_remember => T2.
             case: (getm T2 (prk', info)) => [y|].
             ++ simpl. apply: r_ret => s0 s1 h. split; [reflexivity | extract_base_inv h].
             ++ simpl. apply: r_uniform_bij => [|y]. 1: exists id; done.
                apply: r_put_vs_put.
                ssprove_restore_mem; last by apply: r_ret.
                by ssprove_invariant.
          -- apply: r_put_lhs.
             ssprove_restore_mem; [by ssprove_invariant | ].
             apply: r_get_vs_get_remember => T2.
             case: (getm T2 (prk', info)) => [y|].
             ++ simpl. apply: r_ret => s0 s1 h. split; [reflexivity | extract_base_inv h].
             ++ simpl. apply: r_uniform_bij => [|y]. 1: exists id; done.
                apply: r_put_vs_put.
                ssprove_restore_mem; last by apply: r_ret.
                by ssprove_invariant.
      + apply: r_get_vs_get_remember => v0.
        case: (getm v0 ss) => [prk|].
        * simpl. apply: r_ret => s0 s1 h. split; [reflexivity | extract_base_inv h].
        * apply: r_uniform_bij => [|prk']. 1: exists id; done.
          apply: r_put_vs_put.
          ssprove_restore_mem; [by ssprove_invariant | ].
          apply: r_get_remember_lhs => Used.
          case: (getm Used prk') => [[]|].
          -- apply: r_put_lhs.
             ssprove_restore_mem; [by ssprove_invariant | ].
             apply: r_ret => s0 s1 h. split; [reflexivity | extract_base_inv h].
          -- apply: r_put_lhs.
             ssprove_restore_mem; [by ssprove_invariant | ].
             apply: r_ret => s0 s1 h. split; [reflexivity | extract_base_inv h].
  Qed.

  (* --- ghost inlining: [KDF_hyb_EVAL i ∘ EVAL false] ≈₀ [KDF_hybE_bad i] ---
    The RHS additionally: (a) tracks Used/bad (ignored), and (b) ghost-
    extracts the index-i ss (so extract tables agree everywhere EXCEPT
    possibly at the index-i ss, where the LHS has no entry). *)
  (* Third conjunct ([unindexed ⇒ unextracted]) strengthens the invariant
    beyond what a predecessor draft stated: without it, the "brand new
    [ss]" branches below have no way to know [get_prk]/[get_prk_bad]'s
    own [extract_loc] lookup at [ss] takes the [None] (fresh-sample)
    case -- that's a real fact about the games' own step-by-step
    semantics (extraction for [ss] can only ever happen AFTER [ss] has
    been assigned an index, since every branch runs [get_ss_idx] first),
    not something derivable from the other two conjuncts alone, so it
    has to be carried explicitly. It is trivially maintained: the only
    place [ss_index_loc] gains a new binding is exactly the place both
    sides are about to extract that very [ss], at which point it no
    longer satisfies [SIdx ss = None]. *)
  Definition hybE_inline_inv (i : nat) : precond :=
    heap_ignore [fmap bad_loc; used_prk_loc; extract_loc] ⋊
    rel_app [:: (lhs, extract_loc); (rhs, extract_loc); (lhs, ss_index_loc)]
      (fun (T T' : chMap 'ss 'prk) (SIdx : chMap 'ss 'nat) =>
         (forall ss, getm SIdx ss = Some i -> getm T ss = None)
         /\ (forall ss, getm SIdx ss <> Some i -> getm T ss = getm T' ss)
         /\ (forall ss, getm SIdx ss = None -> getm T ss = None /\ getm T' ss = None)).

  (* [get_ss_idx]'s own two shared puts (assigning [ss0] a fresh index
    [cnt], identically on both sides), re-establishing [hybE_inline_inv].
    Works UNIFORMLY whether [cnt = i] or not -- conjunct 3 ("unindexed ⇒
    unextracted") supplies [T ss0 = None]/[T' ss0 = None] in either case,
    which is exactly what's needed to re-derive conjuncts 1/2 at the
    freshly-assigned index. *)
  Lemma hybE_inline_inv_index_step i s0 s1 SIdx cnt (ss0 : 'ss) :
    hybE_inline_inv i (s0, s1) ->
    get_heap s0 ss_index_loc = SIdx -> get_heap s1 ss_index_loc = SIdx ->
    get_heap s0 ss_count_loc = cnt -> get_heap s1 ss_count_loc = cnt ->
    SIdx ss0 = None ->
    hybE_inline_inv i
      (set_heap (set_heap s0 ss_count_loc cnt.+1) ss_index_loc (setm SIdx ss0 cnt),
       set_heap (set_heap s1 ss_count_loc cnt.+1) ss_index_loc (setm SIdx ss0 cnt)).
  Proof.
    move=> Hinv HSI0 HSI1 Hcnt0 Hcnt1 HSIss0.
    case: Hinv => [Hig Hrel].
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hrel.
    rewrite HSI0 in Hrel.
    case: Hrel => [Hc1 [Hc2 Hc3]].
    move: (Hc3 ss0 HSIss0) => [HT0 HT1].
    split.
    - move=> l Hl.
      apply: get_heap_after_common_double_update.
      exact: (Hig l Hl).
    - rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
      rewrite !(get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_index_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_count_loc.1)).
      rewrite get_set_heap_eq.
      split.
      + move=> ss1 Hi.
        case Heqss: (ss1 == ss0).
        { move/eqP in Heqss. subst ss1. exact: HT0. }
        move: Hi. rewrite setmE Heqss => Hi. exact: (Hc1 ss1 Hi).
      + split.
        * move=> ss1 Hne.
          case Heqss: (ss1 == ss0).
          { move/eqP in Heqss. subst ss1. rewrite HT0 HT1 //. }
          move: Hne. rewrite setmE Heqss => Hne. exact: (Hc2 ss1 Hne).
        * move=> ss1 Hnone.
          case Heqss: (ss1 == ss0).
          { move/eqP in Heqss. subst ss1. move: Hnone. rewrite setmE eq_refl. discriminate. }
          move: Hnone. rewrite setmE Heqss => Hnone. exact: (Hc3 ss1 Hnone).
  Qed.

  (* A repeat/already-indexed [ss0] whose index is anything OTHER than
    [i] (so LHS and RHS both run [get_prk]/[get_prk_bad]'s own extract
    step): a fresh [prk] sample [a] is written to [extract_loc] IDENTICALLY
    on both sides (regardless of what the old entry was), re-establishing
    [hybE_inline_inv]. Conjunct 1 is vacuous ([SIdx ss0 <> Some i]);
    conjunct 2 is trivial at [ss0] (both become [Some a]) and unaffected
    elsewhere; conjunct 3 is vacuous at [ss0] ([SIdx ss0 <> None]) and
    unaffected elsewhere. *)
  Lemma hybE_inline_inv_extract_both_step i s0 s1 (T T' : extract_loc) SIdx (ss0 : 'ss) (a : 'prk) :
    hybE_inline_inv i (s0, s1) ->
    get_heap s0 extract_loc = T -> get_heap s1 extract_loc = T' ->
    get_heap s0 ss_index_loc = SIdx ->
    SIdx ss0 <> Some i -> SIdx ss0 <> None ->
    hybE_inline_inv i
      (set_heap s0 extract_loc (setm T ss0 a), set_heap s1 extract_loc (setm T' ss0 a)).
  Proof.
    move=> Hinv HT0 HT1 HSI0 Hnei Hneu.
    case: Hinv => [Hig Hrel].
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hrel.
    rewrite HT0 HT1 HSI0 in Hrel.
    case: Hrel => [Hc1 [Hc2 Hc3]].
    split.
    - move=> l Hl.
      have Hlext : l.1 != extract_loc.1.
      { apply/eqP => Heq. case/negP: Hl. rewrite Heq. apply: fhas_in. fmap_solve. }
      rewrite (get_set_heap_neq _ _ _ _ Hlext) (get_set_heap_neq _ _ _ _ Hlext).
      exact: (Hig l Hl).
    - rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
      rewrite (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != extract_loc.1)).
      rewrite get_set_heap_eq get_set_heap_eq.
      rewrite HSI0.
      split.
      + move=> ss1 Hi.
        case Heqss: (ss1 == ss0).
        { move/eqP in Heqss. subst ss1. exfalso. exact: (Hnei Hi). }
        rewrite setmE Heqss. exact: (Hc1 ss1 Hi).
      + split.
        * move=> ss1 Hne.
          case Heqss: (ss1 == ss0).
          { move/eqP in Heqss. subst ss1. rewrite !setmE eq_refl //. }
          rewrite !setmE Heqss. exact: (Hc2 ss1 Hne).
        * move=> ss1 Hnone.
          case Heqss: (ss1 == ss0).
          { move/eqP in Heqss. subst ss1. exfalso. exact: (Hneu Hnone). }
          rewrite !setmE Heqss. exact: (Hc3 ss1 Hnone).
  Qed.

  (* The index-[i] ss: LHS never touches [extract_loc] here (it calls
    the imported [eval] oracle directly), while RHS's ghost [get_prk_bad]
    writes a fresh sample [a] there. Conjunct 1 needs [T ss0 = None],
    already guaranteed by the OLD invariant (conjunct 1 itself, since
    [SIdx ss0 = Some i] already); conjunct 2/3 are vacuous at [ss0]
    ([SIdx ss0 = Some i] rules out both [<> Some i] and [= None]) and
    unaffected elsewhere. *)
  Lemma hybE_inline_inv_extract_rhs_step i s0 s1 (T' : extract_loc) SIdx (ss0 : 'ss) (a : 'prk) :
    hybE_inline_inv i (s0, s1) ->
    get_heap s1 extract_loc = T' ->
    get_heap s0 ss_index_loc = SIdx ->
    SIdx ss0 = Some i ->
    hybE_inline_inv i (s0, set_heap s1 extract_loc (setm T' ss0 a)).
  Proof.
    move=> Hinv HT1 HSI0 Hi.
    case: Hinv => [Hig Hrel].
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hrel.
    rewrite HT1 HSI0 in Hrel.
    case: Hrel => [Hc1 [Hc2 Hc3]].
    split.
    - move=> l Hl.
      have Hlext : l.1 != extract_loc.1.
      { apply/eqP => Heq. case/negP: Hl. rewrite Heq. apply: fhas_in. fmap_solve. }
      rewrite (get_set_heap_neq _ _ _ _ Hlext).
      exact: (Hig l Hl).
    - rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
      rewrite HSI0.
      rewrite get_set_heap_eq.
      split.
      + exact: Hc1.
      + split.
        * move=> ss1 Hne.
          case Heqss: (ss1 == ss0).
          { move/eqP in Heqss. subst ss1. exfalso. apply: Hne. exact: Hi. }
          rewrite setmE Heqss. exact: (Hc2 ss1 Hne).
        * move=> ss1 Hnone.
          case Heqss: (ss1 == ss0).
          { move/eqP in Heqss. subst ss1. exfalso. rewrite Hi in Hnone. discriminate. }
          rewrite setmE Heqss. exact: (Hc3 ss1 Hnone).
  Qed.

  (* Composition of [hybE_inline_inv_index_step] and
    [hybE_inline_inv_extract_both_step]: a brand new [ss0] (fresh index
    [cnt <> i]) whose [get_prk]/[get_prk_bad] sample is ALSO fresh (both
    sides write [a] at [ss0]), all in one shot from the ORIGINAL
    (pre-[get_ss_idx]) heaps -- avoids restoring [hybE_inline_inv] twice
    (once wouldn't retain the [ss_index_loc] = [setm SIdx ss0 cnt] fact
    needed to justify the second restore). *)
  Lemma hybE_inline_inv_fresh_both_step i s0 s1 SIdx cnt (ss0 : 'ss) (T T' : extract_loc) (a : 'prk) :
    hybE_inline_inv i (s0, s1) ->
    get_heap s0 ss_index_loc = SIdx -> get_heap s1 ss_index_loc = SIdx ->
    get_heap s0 ss_count_loc = cnt -> get_heap s1 ss_count_loc = cnt ->
    SIdx ss0 = None -> cnt <> i ->
    get_heap s0 extract_loc = T -> get_heap s1 extract_loc = T' ->
    hybE_inline_inv i
      (set_heap (set_heap (set_heap s0 ss_count_loc cnt.+1) ss_index_loc (setm SIdx ss0 cnt))
        extract_loc (setm T ss0 a),
       set_heap (set_heap (set_heap s1 ss_count_loc cnt.+1) ss_index_loc (setm SIdx ss0 cnt))
        extract_loc (setm T' ss0 a)).
  Proof.
    move=> Hinv HSI0 HSI1 Hcnt0 Hcnt1 HSIss0 Hcnti HT0 HT1.
    have Hstep := hybE_inline_inv_index_step i s0 s1 SIdx cnt ss0 Hinv HSI0 HSI1 Hcnt0 Hcnt1 HSIss0.
    have HSI0' : get_heap (set_heap (set_heap s0 ss_count_loc cnt.+1) ss_index_loc (setm SIdx ss0 cnt))
      ss_index_loc = setm SIdx ss0 cnt by rewrite get_set_heap_eq.
    have HT0' : get_heap (set_heap (set_heap s0 ss_count_loc cnt.+1) ss_index_loc (setm SIdx ss0 cnt))
      extract_loc = T.
    { rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_index_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_count_loc.1)).
      exact: HT0. }
    have HT1' : get_heap (set_heap (set_heap s1 ss_count_loc cnt.+1) ss_index_loc (setm SIdx ss0 cnt))
      extract_loc = T'.
    { rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_index_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_count_loc.1)).
      exact: HT1. }
    apply: (hybE_inline_inv_extract_both_step i _ _ T T' (setm SIdx ss0 cnt) ss0 a Hstep HT0' HT1' HSI0').
    - rewrite setmE eq_refl. move=> [Heq]. exact: (Hcnti Heq).
    - rewrite setmE eq_refl. discriminate.
  Qed.

  (* Companion for the genuinely new coupling case: a brand new [ss0]
    whose freshly-assigned index [cnt] equals [i] exactly. LHS never
    touches [extract_loc] here; only RHS's ghost [get_prk_bad] writes a
    fresh sample [a] there. *)
  Lemma hybE_inline_inv_fresh_couple_step i s0 s1 SIdx cnt (ss0 : 'ss) (T' : extract_loc) (a : 'prk) :
    hybE_inline_inv i (s0, s1) ->
    get_heap s0 ss_index_loc = SIdx -> get_heap s1 ss_index_loc = SIdx ->
    get_heap s0 ss_count_loc = cnt -> get_heap s1 ss_count_loc = cnt ->
    SIdx ss0 = None -> cnt = i ->
    get_heap s1 extract_loc = T' ->
    hybE_inline_inv i
      (set_heap (set_heap s0 ss_count_loc cnt.+1) ss_index_loc (setm SIdx ss0 cnt),
       set_heap (set_heap (set_heap s1 ss_count_loc cnt.+1) ss_index_loc (setm SIdx ss0 cnt))
        extract_loc (setm T' ss0 a)).
  Proof.
    move=> Hinv HSI0 HSI1 Hcnt0 Hcnt1 HSIss0 Hcnti HT1.
    have Hstep := hybE_inline_inv_index_step i s0 s1 SIdx cnt ss0 Hinv HSI0 HSI1 Hcnt0 Hcnt1 HSIss0.
    have HSI0' : get_heap (set_heap (set_heap s0 ss_count_loc cnt.+1) ss_index_loc (setm SIdx ss0 cnt))
      ss_index_loc = setm SIdx ss0 cnt by rewrite get_set_heap_eq.
    have HT1' : get_heap (set_heap (set_heap s1 ss_count_loc cnt.+1) ss_index_loc (setm SIdx ss0 cnt))
      extract_loc = T'.
    { rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_index_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_count_loc.1)).
      exact: HT1. }
    apply: (hybE_inline_inv_extract_rhs_step i _ _ T' (setm SIdx ss0 cnt) ss0 a Hstep HT1' HSI0').
    rewrite setmE eq_refl. by rewrite Hcnti.
  Qed.

  Lemma KDF_hybE_bad_equiv i :
    KDF_hyb_EVAL i ∘ EVAL false ≈₀ KDF_hybE_bad i.
  Proof.
    apply eq_rel_perf_ind with (hybE_inline_inv i).
    - eapply Invariant_inv_conj.
      + eapply Invariant_heap_ignore; fmap_solve.
      + eapply SemiInvariant_relApp; [ simpl; repeat split; try fmap_solve; try done | done ].
    - simplify_eq_rel arg.
      destruct arg as [ss info].
      ssprove_code_simpl.
      apply: r_get_vs_get_remember => SIdx.
      case Hidx: (SIdx ss) => [idx|] /=.
      + case Hlt: (idx < i)%N.
        * apply: r_get_remember_lhs => T.
          apply: r_get_remember_rhs => T'.
          have Hne : SIdx ss <> Some i.
          { rewrite Hidx. move=> [Heq]. move: Hlt. rewrite Heq ltnn. done. }
          ssprove_rem_rel 0%N => Hrel.
          have HTeq := (proj1 (proj2 Hrel)) ss Hne.
          rewrite -HTeq.
          case: (T ss) => [prk|].
          { apply: r_get_vs_get_remember => T2.
            case: (T2 (prk, info)) => [y|].
            { apply: r_ret => s0 s1 h. split; [reflexivity | extract_base_inv h]. }
            apply: r_uniform_bij => [|y']. 1: exists id; done.
            apply: r_put_vs_put.
            ssprove_restore_mem; last by apply: r_ret.
            by close_preserve. }
          apply: r_uniform_bij => [|a]. 1: exists id; done.
          apply: r_put_vs_put.
          ssprove_restore_mem.
          { move=> s0 s1 h.
            case: h => [[[[Hpre HSI0] HSI1] HT0] HT1].
            rewrite /rem_inv /get_side /= in HSI0 HSI1 HT0 HT1.
            have Hnei : SIdx ss <> Some i by exact: Hne.
            have Hneu : SIdx ss <> None by rewrite Hidx.
            exact: (hybE_inline_inv_extract_both_step i s0 s1 T T' SIdx ss a Hpre HT0 HT1 HSI0 Hnei Hneu). }
          apply: r_get_remember_rhs => Used.
          case: (Used a) => [[]|].
          { apply: r_put_rhs.
            ssprove_restore_mem; [ close_preserve | ].
            apply: r_get_vs_get_remember => T2.
            case: (T2 (a, info)) => [y|].
            { apply: r_ret => s0 s1 h. split; [reflexivity | extract_base_inv h]. }
            apply: r_uniform_bij => [|y']. 1: exists id; done.
            apply: r_put_vs_put.
            ssprove_restore_mem; last by apply: r_ret.
            by close_preserve. }
          apply: r_put_rhs.
          ssprove_restore_mem; [ close_preserve | ].
          apply: r_get_vs_get_remember => T2.
          case: (T2 (a, info)) => [y|].
          { apply: r_ret => s0 s1 h. split; [reflexivity | extract_base_inv h]. }
          apply: r_uniform_bij => [|y']. 1: exists id; done.
          apply: r_put_vs_put.
          ssprove_restore_mem; last by apply: r_ret.
          by close_preserve.
        * case Hcmp: (idx == i).
          -- ssprove_code_simpl.
             apply: r_get_remember_rhs => T'.
             have Hi : SIdx ss = Some i by move/eqP in Hcmp; rewrite Hidx Hcmp.
             case: (T' ss) => [prk|].
             { apply: r_get_vs_get_remember => T2.
               case: (T2 info) => [y|].
               - apply: r_ret => s0 s1 h. split; [reflexivity | extract_base_inv h].
               - apply: r_uniform_bij => [|y']. 1: exists id; done.
                 apply: r_put_vs_put.
                 ssprove_restore_mem; last by apply: r_ret.
                 by close_preserve. }
             apply r_const_sample_R. 1: exact _.
             move=> a.
             apply: r_put_rhs.
             ssprove_restore_mem.
             { move=> s0 s1 h.
               case: h => [[[Hpre HSI0] HSI1] HT1].
               rewrite /rem_inv /get_side /= in HSI0 HSI1 HT1.
               exact: (hybE_inline_inv_extract_rhs_step i s0 s1 T' SIdx ss a Hpre HT1 HSI0 Hi). }
             apply: r_get_remember_rhs => Used.
             case: (Used a) => [[]|].
             { apply: r_put_rhs.
               ssprove_restore_mem; [ close_preserve | ].
               apply: r_get_vs_get_remember => T2.
               case: (T2 info) => [y|].
               { apply: r_ret => s0 s1 h. split; [reflexivity | extract_base_inv h]. }
               apply: r_uniform_bij => [|y']. 1: exists id; done.
               apply: r_put_vs_put.
               ssprove_restore_mem; last by apply: r_ret.
               by close_preserve. }
             apply: r_put_rhs.
             ssprove_restore_mem; [ close_preserve | ].
             apply: r_get_vs_get_remember => T2.
             case: (T2 info) => [y|].
             { apply: r_ret => s0 s1 h. split; [reflexivity | extract_base_inv h]. }
             apply: r_uniform_bij => [|y']. 1: exists id; done.
             apply: r_put_vs_put.
             ssprove_restore_mem; last by apply: r_ret.
             by close_preserve.
          -- apply: r_get_remember_lhs => T.
             apply: r_get_remember_rhs => T'.
             have Hne : SIdx ss <> Some i.
             { rewrite Hidx. move=> [Heq]. move: Hcmp. rewrite Heq eq_refl. done. }
             ssprove_rem_rel 0%N => Hrel.
             have HTeq := (proj1 (proj2 Hrel)) ss Hne.
             rewrite -HTeq.
             case: (T ss) => [prk|].
             { apply: r_ret => s0 s1 h. split; [reflexivity | extract_base_inv h]. }
             apply: r_uniform_bij => [|a]. 1: exists id; done.
             apply: r_put_vs_put.
             ssprove_restore_mem.
             { move=> s0 s1 h.
               case: h => [[[[Hpre HSI0] HSI1] HT0] HT1].
               rewrite /rem_inv /get_side /= in HSI0 HSI1 HT0 HT1.
               have Hnei : SIdx ss <> Some i by exact: Hne.
               have Hneu : SIdx ss <> None by rewrite Hidx.
               exact: (hybE_inline_inv_extract_both_step i s0 s1 T T' SIdx ss a Hpre HT0 HT1 HSI0 Hnei Hneu). }
             apply: r_get_remember_rhs => Used.
             case: (Used a) => [[]|].
             { apply: r_put_rhs.
               ssprove_restore_mem; last by apply: r_ret.
               by close_preserve. }
             apply: r_put_rhs.
             ssprove_restore_mem; last by apply: r_ret.
             by close_preserve.
      + apply: r_get_vs_get_remember => cnt.
        eapply rpre_weaken_rule with (pre := fun '(s0,s1) =>
          (hybE_inline_inv i ⋊ rem_lhs ss_index_loc SIdx ⋊ rem_rhs ss_index_loc SIdx
           ⋊ rem_lhs ss_count_loc cnt ⋊ rem_rhs ss_count_loc cnt
           ⋊ single_lhs extract_loc (fun T : extract_loc => T ss = None)
           ⋊ single_rhs extract_loc (fun T' : extract_loc => T' ss = None)) (s0,s1)).
        2: {
          move=> s0 s1 Hcur.
          case: (Hcur) => [[[[Hinv HSI0] HSI1] Hcnt0] Hcnt1].
          case: Hinv => [Hig Hrel].
          rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hrel.
          rewrite /rem_inv /get_side /= in HSI0.
          rewrite HSI0 in Hrel.
          case: Hrel => [Hc1 [Hc2 Hc3]].
          move: (Hc3 ss Hidx) => [HT0 HT1].
          split; [split; [exact: Hcur | rewrite (rel_app_cons) (rel_app_nil) /=; exact: HT0]
                          | rewrite (rel_app_cons) (rel_app_nil) /=; exact: HT1].
        }
        apply: r_put_vs_put.
        apply: r_put_vs_put.
        case Hlt2: (cnt < i)%N.
        { apply: r_get_remember_lhs => T.
          apply: r_get_remember_rhs => T'.
          eapply (@r_rem_rel _ _ [:: (lhs, extract_loc)] (fun T0 : extract_loc => T0 ss = None));
            [ typeclasses eauto | typeclasses eauto | move=> HT0 ].
          eapply (@r_rem_rel _ _ [:: (rhs, extract_loc)] (fun T0 : extract_loc => T0 ss = None));
            [ typeclasses eauto | typeclasses eauto | move=> HT1 ].
          rewrite HT0 HT1 /=.
          apply: r_uniform_bij => [|a]. 1: exists id; done.
          apply: r_put_vs_put.
          eapply rpre_weaken_rule with (pre := fun '(s0,s1) => hybE_inline_inv i (s0,s1)).
          2: {
            move=> s0 s1 h.
            case: h => [s1x [hx Es1x]].
            case: hx => [s0x [hy Es0x]].
            subst.
            case: hy => [[Hbase HremT] HremT'].
            rewrite /rem_inv /get_side /= in HremT HremT'.
            case: Hbase => [s1a [Hbase1 Es1a]].
            case: Hbase1 => [s0a [Hbase2 Es0a]].
            case: Hbase2 => [s1b [Hbase3 Es1b]].
            case: Hbase3 => [s0b [Hbase4 Es0b]].
            subst.
            case: Hbase4 => [[Hrem Hsl] Hsr].
            case: Hrem => [[[[Hpre HSIl] HSIr] Hcntl] Hcntr].
            rewrite /rem_inv /get_side /= in HSIl HSIr Hcntl Hcntr.
            rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_index_loc.1)).
            rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_count_loc.1)).
            rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_index_loc.1)).
            rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_count_loc.1)).
            have Hnei : cnt <> i.
            { move=> Heq. move: Hlt2. rewrite Heq ltnn. done. }
            exact: (hybE_inline_inv_fresh_both_step i s0b s1b SIdx cnt ss (get_heap s0b extract_loc) (get_heap s1b extract_loc) a Hpre HSIl HSIr Hcntl Hcntr Hidx Hnei erefl erefl).
          }
          apply: r_get_remember_rhs => Used.
          case: (Used a) => [[]|].
          { apply: r_put_rhs.
            ssprove_restore_mem; [ close_preserve | ].
            apply: r_get_vs_get_remember => T2.
            case: (T2 (a, info)) => [y|].
            { apply: r_ret => s0 s1 h. split; [reflexivity | extract_base_inv h]. }
            apply: r_uniform_bij => [|y']. 1: exists id; done.
            apply: r_put_vs_put.
            ssprove_restore_mem; last by apply: r_ret.
            by close_preserve. }
          apply: r_put_rhs.
          ssprove_restore_mem; [ close_preserve | ].
          apply: r_get_vs_get_remember => T2.
          case: (T2 (a, info)) => [y|].
          { apply: r_ret => s0 s1 h. split; [reflexivity | extract_base_inv h]. }
          apply: r_uniform_bij => [|y']. 1: exists id; done.
          apply: r_put_vs_put.
          ssprove_restore_mem; last by apply: r_ret.
          by close_preserve.
        }
        case Hcmp2: (cnt == i).
        { ssprove_code_simpl.
          apply: r_get_remember_rhs => T'.
          have Hi : cnt = i by move/eqP in Hcmp2.
          eapply (@r_rem_rel _ _ [:: (rhs, extract_loc)] (fun T0 : extract_loc => T0 ss = None));
            [ typeclasses eauto | typeclasses eauto | move=> HT1 ].
          rewrite HT1 /=.
          apply r_const_sample_R. 1: exact _.
          move=> a.
          apply: r_put_rhs.
          eapply rpre_weaken_rule with (pre := fun '(s0,s1) => hybE_inline_inv i (s0,s1)).
          2: {
            move=> s0 s1 h.
            case: h => [s1x [hx Es1x]].
            subst.
            case: hx => [Hbase HremT'].
            rewrite /rem_inv /get_side /= in HremT'.
            case: Hbase => [s1a [Hbase1 Es1a]].
            case: Hbase1 => [s0a [Hbase2 Es0a]].
            case: Hbase2 => [s1b [Hbase3 Es1b]].
            case: Hbase3 => [s0b [Hbase4 Es0b]].
            subst.
            case: Hbase4 => [[Hrem Hsl] Hsr].
            case: Hrem => [[[[Hpre HSIl] HSIr] Hcntl] Hcntr].
            rewrite /rem_inv /get_side /= in HSIl HSIr Hcntl Hcntr.
            rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_index_loc.1)).
            rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_count_loc.1)).
            rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_index_loc.1)) in HT1.
            rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_count_loc.1)) in HT1.
            exact: (hybE_inline_inv_fresh_couple_step i s0b s1b SIdx i ss (get_heap s1b extract_loc) a Hpre HSIl HSIr Hcntl Hcntr Hidx erefl erefl).
          }
          apply: r_get_remember_rhs => Used.
          case: (Used a) => [[]|].
          { apply: r_put_rhs.
            ssprove_restore_mem; [ close_preserve | ].
            apply: r_get_vs_get_remember => T2.
            case: (T2 info) => [y|].
            { apply: r_ret => s0 s1 h. split; [reflexivity | extract_base_inv h]. }
            apply: r_uniform_bij => [|y']. 1: exists id; done.
            apply: r_put_vs_put.
            ssprove_restore_mem; last by apply: r_ret.
            by close_preserve. }
          apply: r_put_rhs.
          ssprove_restore_mem; [ close_preserve | ].
          apply: r_get_vs_get_remember => T2.
          case: (T2 info) => [y|].
          { apply: r_ret => s0 s1 h. split; [reflexivity | extract_base_inv h]. }
          apply: r_uniform_bij => [|y']. 1: exists id; done.
          apply: r_put_vs_put.
          ssprove_restore_mem; last by apply: r_ret.
          by close_preserve.
        }
        apply: r_get_remember_lhs => T.
        apply: r_get_remember_rhs => T'.
        eapply (@r_rem_rel _ _ [:: (lhs, extract_loc)] (fun T0 : extract_loc => T0 ss = None));
          [ typeclasses eauto | typeclasses eauto | move=> HT0 ].
        eapply (@r_rem_rel _ _ [:: (rhs, extract_loc)] (fun T0 : extract_loc => T0 ss = None));
          [ typeclasses eauto | typeclasses eauto | move=> HT1 ].
        rewrite HT0 HT1 /=.
        apply: r_uniform_bij => [|a]. 1: exists id; done.
        apply: r_put_vs_put.
        eapply rpre_weaken_rule with (pre := fun '(s0,s1) => hybE_inline_inv i (s0,s1)).
        2: {
          move=> s0 s1 h.
          case: h => [s1x [hx Es1x]].
          case: hx => [s0x [hy Es0x]].
          subst.
          case: hy => [[Hbase HremT] HremT'].
          rewrite /rem_inv /get_side /= in HremT HremT'.
          case: Hbase => [s1a [Hbase1 Es1a]].
          case: Hbase1 => [s0a [Hbase2 Es0a]].
          case: Hbase2 => [s1b [Hbase3 Es1b]].
          case: Hbase3 => [s0b [Hbase4 Es0b]].
          subst.
          case: Hbase4 => [[Hrem Hsl] Hsr].
          case: Hrem => [[[[Hpre HSIl] HSIr] Hcntl] Hcntr].
          rewrite /rem_inv /get_side /= in HSIl HSIr Hcntl Hcntr.
          rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_index_loc.1)).
          rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_count_loc.1)).
          rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_index_loc.1)).
          rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_count_loc.1)).
          have Hnei : cnt <> i.
          { move=> Heq. move: Hcmp2. rewrite Heq eq_refl. done. }
          exact: (hybE_inline_inv_fresh_both_step i s0b s1b SIdx cnt ss (get_heap s0b extract_loc) (get_heap s1b extract_loc) a Hpre HSIl HSIr Hcntl Hcntr Hidx Hnei erefl erefl).
        }
        apply: r_get_remember_rhs => Used.
        case: (Used a) => [[]|].
        { apply: r_put_rhs.
          ssprove_restore_mem; last by apply: r_ret.
          by close_preserve. }
        apply: r_put_rhs.
        ssprove_restore_mem; last by apply: r_ret.
        by close_preserve.
  Qed.

  (* --- bad_preserved witnesses: mechanical mirrors of
    [KDF_mid'_bad_preserved]/[KDF_bad_bad_preserved] (lossless_valid +
    bad_loc_monotone + Pr_code_lossless_bad), with get_ss_idx's extra
    get/put steps and the three-way branch. *)
  Lemma KDF_hybE_bad_bad_preserved i : bad_preserved DERIVE_export 4 (KDF_hybE_bad i).
  Proof.
    move=> id S T x h has Hb.
    fmap_invert has.
    simplify_linking.
    case: x => ss info /=.
    apply: (Pr_code_lossless_bad KDF_hybE_bad_locs _ _ _ h Hb).
    - apply: lv_getr; [fmap_solve | move=> v; case: (v ss) => [idx|] ].
      + simpl. case: (idx < i)%N.
        * apply: lv_getr; [fmap_solve | move=> v0; case: (v0 ss) => [prk|] ].
          -- apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (prk, info)) => [y|] ].
             ++ exact: lv_ret.
             ++ apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
          -- apply: lv_sampler => prk. apply: lv_putr; [fmap_solve |
               apply: lv_getr; [fmap_solve | move=> Used; case: (Used prk) => [[]|] ] ].
             ++ apply: lv_putr; [fmap_solve |
                  apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (prk, info)) => [y|] ] ].
                --- exact: lv_ret.
                --- apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
             ++ apply: lv_putr; [fmap_solve |
                  apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (prk, info)) => [y|] ] ].
                --- exact: lv_ret.
                --- apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
        * case: (idx == i).
          -- apply: lv_getr; [fmap_solve | move=> v0; case: (v0 ss) => [prk|] ].
             ++ simpl. apply: lv_getr; [fmap_solve | move=> T; case: (T info) => [y|] ].
                --- exact: lv_ret.
                --- apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
             ++ apply: lv_sampler => prk. apply: lv_putr; [fmap_solve |
                  apply: lv_getr; [fmap_solve | move=> Used; case: (Used prk) => [[]|] ] ].
                --- apply: lv_putr; [fmap_solve |
                     apply: lv_getr; [fmap_solve | move=> T; case: (T info) => [y|] ] ].
                    +++ exact: lv_ret.
                    +++ apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
                --- apply: lv_putr; [fmap_solve |
                     apply: lv_getr; [fmap_solve | move=> T; case: (T info) => [y|] ] ].
                    +++ exact: lv_ret.
                    +++ apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
          -- apply: lv_getr; [fmap_solve | move=> v0; case: (v0 ss) => [prk|] ].
             ++ exact: lv_ret.
             ++ apply: lv_sampler => prk. apply: lv_putr; [fmap_solve |
                  apply: lv_getr; [fmap_solve | move=> Used; case: (Used prk) => [[]|] ] ].
                --- apply: lv_putr; [fmap_solve | exact: lv_ret].
                --- apply: lv_putr; [fmap_solve | exact: lv_ret].
      + apply: lv_getr; [fmap_solve | move=> cnt].
        apply: lv_putr; [fmap_solve | apply: lv_putr; [fmap_solve | simpl] ].
        case: (cnt < i)%N.
        * apply: lv_getr; [fmap_solve | move=> v0; case: (v0 ss) => [prk|] ].
          -- apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (prk, info)) => [y|] ].
             ++ exact: lv_ret.
             ++ apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
          -- apply: lv_sampler => prk. apply: lv_putr; [fmap_solve |
               apply: lv_getr; [fmap_solve | move=> Used; case: (Used prk) => [[]|] ] ].
             ++ apply: lv_putr; [fmap_solve |
                  apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (prk, info)) => [y|] ] ].
                --- exact: lv_ret.
                --- apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
             ++ apply: lv_putr; [fmap_solve |
                  apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (prk, info)) => [y|] ] ].
                --- exact: lv_ret.
                --- apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
        * case: (cnt == i).
          -- apply: lv_getr; [fmap_solve | move=> v0; case: (v0 ss) => [prk|] ].
             ++ simpl. apply: lv_getr; [fmap_solve | move=> T; case: (T info) => [y|] ].
                --- exact: lv_ret.
                --- apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
             ++ apply: lv_sampler => prk. apply: lv_putr; [fmap_solve |
                  apply: lv_getr; [fmap_solve | move=> Used; case: (Used prk) => [[]|] ] ].
                --- apply: lv_putr; [fmap_solve |
                     apply: lv_getr; [fmap_solve | move=> T; case: (T info) => [y|] ] ].
                    +++ exact: lv_ret.
                    +++ apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
                --- apply: lv_putr; [fmap_solve |
                     apply: lv_getr; [fmap_solve | move=> T; case: (T info) => [y|] ] ].
                    +++ exact: lv_ret.
                    +++ apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
          -- apply: lv_getr; [fmap_solve | move=> v0; case: (v0 ss) => [prk|] ].
             ++ exact: lv_ret.
             ++ apply: lv_sampler => prk. apply: lv_putr; [fmap_solve |
                  apply: lv_getr; [fmap_solve | move=> Used; case: (Used prk) => [[]|] ] ].
                --- apply: lv_putr; [fmap_solve | exact: lv_ret].
                --- apply: lv_putr; [fmap_solve | exact: lv_ret].
    - apply: blm_getr => v. case: (v ss) => [idx|].
      + simpl. case: (idx < i)%N.
        * apply: blm_getr => v0. case: (v0 ss) => [prk|].
          -- apply: blm_getr => T2. case: (T2 (prk, info)) => [y|].
             ++ exact: blm_ret.
             ++ apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
          -- apply: blm_sampler => prk. apply: blm_putr_other; [done |
               apply: blm_getr => Used; case: (Used prk) => [[]|] ].
             ++ apply: blm_putr_bad.
                apply: blm_getr => T2; case: (T2 (prk, info)) => [y|].
                --- exact: blm_ret.
                --- apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
             ++ apply: blm_putr_other; [done |
                  apply: blm_getr => T2; case: (T2 (prk, info)) => [y|] ].
                --- exact: blm_ret.
                --- apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
        * case: (idx == i).
          -- apply: blm_getr => v0. case: (v0 ss) => [prk|].
             ++ simpl. apply: blm_getr => T. case: (T info) => [y|].
                --- exact: blm_ret.
                --- apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
             ++ apply: blm_sampler => prk. apply: blm_putr_other; [done |
                  apply: blm_getr => Used; case: (Used prk) => [[]|] ].
                --- apply: blm_putr_bad.
                    apply: blm_getr => T; case: (T info) => [y|].
                    +++ exact: blm_ret.
                    +++ apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
                --- apply: blm_putr_other; [done |
                      apply: blm_getr => T; case: (T info) => [y|] ].
                    +++ exact: blm_ret.
                    +++ apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
          -- apply: blm_getr => v0. case: (v0 ss) => [prk|].
             ++ exact: blm_ret.
             ++ apply: blm_sampler => prk. apply: blm_putr_other; [done |
                  apply: blm_getr => Used; case: (Used prk) => [[]|] ].
                --- apply: blm_putr_bad. exact: blm_ret.
                --- apply: blm_putr_other; [done | exact: blm_ret].
      + apply: blm_getr => cnt.
        apply: blm_putr_other; [done | apply: blm_putr_other; [done | simpl] ].
        case: (cnt < i)%N.
        * apply: blm_getr => v0. case: (v0 ss) => [prk|].
          -- apply: blm_getr => T2. case: (T2 (prk, info)) => [y|].
             ++ exact: blm_ret.
             ++ apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
          -- apply: blm_sampler => prk. apply: blm_putr_other; [done |
               apply: blm_getr => Used; case: (Used prk) => [[]|] ].
             ++ apply: blm_putr_bad.
                apply: blm_getr => T2; case: (T2 (prk, info)) => [y|].
                --- exact: blm_ret.
                --- apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
             ++ apply: blm_putr_other; [done |
                  apply: blm_getr => T2; case: (T2 (prk, info)) => [y|] ].
                --- exact: blm_ret.
                --- apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
        * case: (cnt == i).
          -- apply: blm_getr => v0. case: (v0 ss) => [prk|].
             ++ simpl. apply: blm_getr => T. case: (T info) => [y|].
                --- exact: blm_ret.
                --- apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
             ++ apply: blm_sampler => prk. apply: blm_putr_other; [done |
                  apply: blm_getr => Used; case: (Used prk) => [[]|] ].
                --- apply: blm_putr_bad.
                    apply: blm_getr => T; case: (T info) => [y|].
                    +++ exact: blm_ret.
                    +++ apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
                --- apply: blm_putr_other; [done |
                      apply: blm_getr => T; case: (T info) => [y|] ].
                    +++ exact: blm_ret.
                    +++ apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
          -- apply: blm_getr => v0. case: (v0 ss) => [prk|].
             ++ exact: blm_ret.
             ++ apply: blm_sampler => prk. apply: blm_putr_other; [done |
                  apply: blm_getr => Used; case: (Used prk) => [[]|] ].
                --- apply: blm_putr_bad. exact: blm_ret.
                --- apply: blm_putr_other; [done | exact: blm_ret].
  Qed.

  Lemma KDF_hyb_bad_bad_preserved j : bad_preserved DERIVE_export 4 (KDF_hyb_bad j).
  Proof.
    move=> id S T x h has Hb.
    fmap_invert has.
    simplify_linking.
    case: x => ss info /=.
    apply: (Pr_code_lossless_bad KDF_hyb_bad_locs _ _ _ h Hb).
    - apply: lv_getr; [fmap_solve | move=> v; case: (v ss) => [idx|] ].
      + simpl. case: (idx < j)%N.
        * apply: lv_getr; [fmap_solve | move=> v0; case: (v0 ss) => [prk|] ].
          -- apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (prk, info)) => [y|] ].
             ++ exact: lv_ret.
             ++ apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
          -- apply: lv_sampler => prk. apply: lv_putr; [fmap_solve |
               apply: lv_getr; [fmap_solve | move=> Used; case: (Used prk) => [[]|] ] ].
             ++ apply: lv_putr; [fmap_solve |
                  apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (prk, info)) => [y|] ] ].
                --- exact: lv_ret.
                --- apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
             ++ apply: lv_putr; [fmap_solve |
                  apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (prk, info)) => [y|] ] ].
                --- exact: lv_ret.
                --- apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
        * apply: lv_getr; [fmap_solve | move=> v0; case: (v0 ss) => [prk|] ].
          -- exact: lv_ret.
          -- apply: lv_sampler => prk. apply: lv_putr; [fmap_solve |
               apply: lv_getr; [fmap_solve | move=> Used; case: (Used prk) => [[]|] ] ].
             ++ apply: lv_putr; [fmap_solve | exact: lv_ret].
             ++ apply: lv_putr; [fmap_solve | exact: lv_ret].
      + apply: lv_getr; [fmap_solve | move=> cnt].
        apply: lv_putr; [fmap_solve | apply: lv_putr; [fmap_solve | simpl] ].
        case: (cnt < j)%N.
        * apply: lv_getr; [fmap_solve | move=> v0; case: (v0 ss) => [prk|] ].
          -- apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (prk, info)) => [y|] ].
             ++ exact: lv_ret.
             ++ apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
          -- apply: lv_sampler => prk. apply: lv_putr; [fmap_solve |
               apply: lv_getr; [fmap_solve | move=> Used; case: (Used prk) => [[]|] ] ].
             ++ apply: lv_putr; [fmap_solve |
                  apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (prk, info)) => [y|] ] ].
                --- exact: lv_ret.
                --- apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
             ++ apply: lv_putr; [fmap_solve |
                  apply: lv_getr; [fmap_solve | move=> T2; case: (T2 (prk, info)) => [y|] ] ].
                --- exact: lv_ret.
                --- apply: lv_sampler => y0. apply: lv_putr; [fmap_solve | exact: lv_ret].
        * apply: lv_getr; [fmap_solve | move=> v0; case: (v0 ss) => [prk|] ].
          -- exact: lv_ret.
          -- apply: lv_sampler => prk. apply: lv_putr; [fmap_solve |
               apply: lv_getr; [fmap_solve | move=> Used; case: (Used prk) => [[]|] ] ].
             ++ apply: lv_putr; [fmap_solve | exact: lv_ret].
             ++ apply: lv_putr; [fmap_solve | exact: lv_ret].
    - apply: blm_getr => v. case: (v ss) => [idx|].
      + simpl. case: (idx < j)%N.
        * apply: blm_getr => v0. case: (v0 ss) => [prk|].
          -- apply: blm_getr => T2. case: (T2 (prk, info)) => [y|].
             ++ exact: blm_ret.
             ++ apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
          -- apply: blm_sampler => prk. apply: blm_putr_other; [done |
               apply: blm_getr => Used; case: (Used prk) => [[]|] ].
             ++ apply: blm_putr_bad.
                apply: blm_getr => T2; case: (T2 (prk, info)) => [y|].
                --- exact: blm_ret.
                --- apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
             ++ apply: blm_putr_other; [done |
                  apply: blm_getr => T2; case: (T2 (prk, info)) => [y|] ].
                --- exact: blm_ret.
                --- apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
        * apply: blm_getr => v0. case: (v0 ss) => [prk|].
          -- exact: blm_ret.
          -- apply: blm_sampler => prk. apply: blm_putr_other; [done |
               apply: blm_getr => Used; case: (Used prk) => [[]|] ].
             ++ apply: blm_putr_bad. exact: blm_ret.
             ++ apply: blm_putr_other; [done | exact: blm_ret].
      + apply: blm_getr => cnt. apply: blm_putr_other; [done | apply: blm_putr_other; [done | simpl] ].
        case: (cnt < j)%N.
        * apply: blm_getr => v0. case: (v0 ss) => [prk|].
          -- apply: blm_getr => T2. case: (T2 (prk, info)) => [y|].
             ++ exact: blm_ret.
             ++ apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
          -- apply: blm_sampler => prk. apply: blm_putr_other; [done |
               apply: blm_getr => Used; case: (Used prk) => [[]|] ].
             ++ apply: blm_putr_bad.
                apply: blm_getr => T2; case: (T2 (prk, info)) => [y|].
                --- exact: blm_ret.
                --- apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
             ++ apply: blm_putr_other; [done |
                  apply: blm_getr => T2; case: (T2 (prk, info)) => [y|] ].
                --- exact: blm_ret.
                --- apply: blm_sampler => y0. apply: blm_putr_other; [done | exact: blm_ret].
        * apply: blm_getr => v0. case: (v0 ss) => [prk|].
          -- exact: blm_ret.
          -- apply: blm_sampler => prk. apply: blm_putr_other; [done |
               apply: blm_getr => Used; case: (Used prk) => [[]|] ].
             ++ apply: blm_putr_bad. exact: blm_ret.
             ++ apply: blm_putr_other; [done | exact: blm_ret].
  Qed.

  (* --- the up-to-bad invariant ---
    Since the idx==i branch of [KDF_hybE_bad] ghost-extracts, BOTH games
    run [get_ss_idx] + [get_prk_bad] on every query with identical
    observable effect on extract_loc / used_prk_loc / bad_loc /
    ss_count_loc / ss_index_loc -- so heap_ignore covers ONLY
    [mid_loc; eval_tbl_loc], and equality of all the shared bookkeeping
    (including bad_loc sync) comes for free, UNCONDITIONALLY (post-bad,
    couple both sides' samples identically; only the two answer tables
    and the outputs are allowed to diverge). The rel_app conjunct, gated
    on bad = false, carries the table-match: the index-i ss's prk links
    [eval_tbl_loc] (LHS, keyed info) to the (prk_i, ·) slice of the RHS
    [mid_loc]; every other extracted prk's slice agrees between the two
    [mid_loc]s; and the LHS [mid_loc] has no (prk_i, ·) entries. *)

  Definition ss_index_injective (SIdx : chMap 'ss 'nat) : Prop :=
    forall ss1 ss2 j, getm SIdx ss1 = Some j -> getm SIdx ss2 = Some j -> ss1 = ss2.

  Definition eval_tbl_owner (i : nat) (SIdx : chMap 'ss 'nat)
    (T : chMap 'ss 'prk) (Tev : chMap 'info 'out) : Prop :=
    forall info, getm Tev info <> None ->
      exists ss prk, getm SIdx ss = Some i /\ getm T ss = Some prk.

  Definition hyb_tbl_match (i : nat) (SIdx : chMap 'ss 'nat) (T : chMap 'ss 'prk)
    (TmL TmR : chMap ('prk × 'info) 'out) (Tev : chMap 'info 'out) : Prop :=
    forall ss prk, getm T ss = Some prk ->
      if getm SIdx ss == Some i
      then (forall info, getm TmR (prk, info) = getm Tev info)
           /\ (forall info, getm TmL (prk, info) = None)
      else (forall info, getm TmL (prk, info) = getm TmR (prk, info)).

  (* An [ss] that has never been queried (no [ss_index_loc] entry) has
    also never been extracted -- a consequence of the games' own
    semantics ([get_prk_bad] only ever runs for a given [ss] AFTER
    [get_ss_idx] has already assigned it an index, in the very same
    call), needed to rule out a hypothetical stale [extract_loc] entry
    for a brand new [ss] right when [get_ss_idx] is about to assign it
    the fresh index [i] -- without it, the freshly-assigned owner's
    [hyb_tbl_match] obligation could not be discharged. *)
  Definition ss_unindexed_unextracted (SIdx : chMap 'ss 'nat) (T : chMap 'ss 'prk) : Prop :=
    forall ss, getm SIdx ss = None -> getm T ss = None.

  (* Every index [get_ss_idx] has ever handed out is strictly below the
    NEXT fresh index [ss_count_loc] -- a structural fact about
    [get_ss_idx]'s own bookkeeping (indices are handed out from a
    strictly increasing counter, never reused), needed so that when a
    brand new [ss0] is assigned the fresh index [cnt], no OTHER [ss]
    can already own that same index [cnt] (which is what re-establishes
    [ss_index_injective] after the update). *)
  Definition ss_index_lt_count (SIdx : chMap 'ss 'nat) (cnt : nat) : Prop :=
    forall ss j, getm SIdx ss = Some j -> ltn j cnt.

  Definition KDF_hybE_bad_inv (i : nat) : precond :=
    heap_ignore [fmap mid_loc; eval_tbl_loc] ⋊
    rel_app [:: (lhs, bad_loc); (lhs, extract_loc); (lhs, ss_index_loc);
                (lhs, used_prk_loc); (lhs, mid_loc); (lhs, eval_tbl_loc);
                (rhs, mid_loc); (lhs, ss_count_loc)]
      (fun b T SIdx U TmL Tev TmR cnt =>
         b = false ->
         extract_injective T /\ used_prk_correspondence T U
         /\ ss_index_injective SIdx
         /\ mid_loc_fresh T TmL /\ mid_loc_fresh T TmR
         /\ eval_tbl_owner i SIdx T Tev
         /\ hyb_tbl_match i SIdx T TmL TmR Tev
         /\ ss_unindexed_unextracted SIdx T
         /\ ss_index_lt_count SIdx cnt).

  Lemma KDF_hybE_bad_Invariant i :
    Invariant KDF_hybE_bad_locs KDF_hyb_bad_locs (KDF_hybE_bad_inv i).
  Proof.
    eapply Invariant_inv_conj.
    - eapply Invariant_heap_ignore. fmap_solve.
    - eapply SemiInvariant_relApp.
      + simpl. repeat split. all: try fmap_solve; try done.
      + simpl. move=> _. repeat split=>//.
        move=> [ss Hss]. move: Hss. by rewrite /heap_init.
  Qed.

  (* --- step lemmas for [KDF_hybE_bad_eq_up_to_bad], mirroring the
    [hybE_inline_inv_*_step] family above but for the richer
    [KDF_hybE_bad_inv] invariant. Each takes the ORIGINAL (pre-update)
    heaps and re-establishes the invariant after a specific, concrete
    diagonal (or, for the bad=true escape hatch, unconstrained) update. *)

  (* [get_ss_idx]'s own fresh-index write, diagonally on both sides. *)
  Lemma KDF_hybE_bad_inv_index_step i s0 s1 SIdx cnt (ss0 : 'ss) :
    KDF_hybE_bad_inv i (s0, s1) ->
    get_heap s0 ss_index_loc = SIdx -> get_heap s1 ss_index_loc = SIdx ->
    get_heap s0 ss_count_loc = cnt -> get_heap s1 ss_count_loc = cnt ->
    SIdx ss0 = None ->
    KDF_hybE_bad_inv i
      (set_heap (set_heap s0 ss_count_loc cnt.+1) ss_index_loc (setm SIdx ss0 cnt),
       set_heap (set_heap s1 ss_count_loc cnt.+1) ss_index_loc (setm SIdx ss0 cnt)).
  Proof.
    move=> Hinv HSI0 HSI1 Hcnt0 Hcnt1 HSIss0.
    case: Hinv => [Hig Hrel].
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons)
            (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hrel.
    rewrite HSI0 Hcnt0 in Hrel.
    split.
    - move=> l Hl.
      apply: get_heap_after_common_double_update.
      exact: (Hig l Hl).
    - rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons)
              (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
      rewrite !(get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != ss_index_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != ss_count_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_index_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_count_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != ss_index_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != ss_count_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : mid_loc.1 != ss_index_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : mid_loc.1 != ss_count_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : eval_tbl_loc.1 != ss_index_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : eval_tbl_loc.1 != ss_count_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : ss_count_loc.1 != ss_index_loc.1)).
      rewrite !get_set_heap_eq.
      move=> Hb.
      move: (Hrel Hb) => [Hc1 [Hc2 [Hc3 [Hc4a [Hc4b [Hc5 [Hc6 [Hc7 Hc8]]]]]]]].
      split; [exact: Hc1|].
      split; [exact: Hc2|].
      split.
      { move=> ss1 ss2 j.
        rewrite !setmE.
        case: (eqVneq ss1 ss0) => [-> | Hne1].
        { case: (eqVneq ss2 ss0) => [-> | Hne2] //.
          move=> [<-] Heq2.
          exfalso. move: (Hc8 ss2 cnt Heq2) => Hlt.
          have Hlt2 : (cnt < cnt)%N := Hlt.
          by rewrite ltnn in Hlt2. }
        case: (eqVneq ss2 ss0) => [-> | Hne2].
        { move=> Heq1 [Heq2].
          exfalso.
          move: (Hc8 ss1 j Heq1) => Hlt.
          rewrite -Heq2 in Hlt.
          have Hlt2 : (cnt < cnt)%N := Hlt.
          by rewrite ltnn in Hlt2. }
        exact: Hc3 ss1 ss2 j. }
      split; [exact: Hc4a|].
      split; [exact: Hc4b|].
      split.
      { move=> info Hinfo.
        move: (Hc5 info Hinfo) => [ss [prk [HSss HTss]]].
        exists ss, prk.
        rewrite setmE.
        case: (eqVneq ss ss0) => [Heq | Hne].
        { exfalso. subst ss. rewrite HSIss0 in HSss. discriminate. }
        by rewrite HSss. }
      split.
      { move=> ss1 prk1 HT1.
        rewrite setmE.
        case: (eqVneq ss1 ss0) => [Heq | Hne].
        { exfalso. subst ss1. move: (Hc7 ss0 HSIss0) => HT0. rewrite HT0 in HT1. discriminate. }
        exact: (Hc6 ss1 prk1 HT1). }
      split.
      { move=> ss1.
        rewrite setmE.
        case: (eqVneq ss1 ss0) => [Heq | Hne] //.
        exact: Hc7. }
      move=> ss1 j.
      rewrite setmE.
      case: (eqVneq ss1 ss0) => [Heq [<-] | Hne Heq1].
      { exact: ltnSn cnt. }
      move: (Hc8 ss1 j Heq1) => Hlt.
      exact: ltn_trans Hlt (ltnSn cnt).
  Qed.

  (* [get_prk_bad]'s fresh-sample, no-collision write, diagonally on
    both sides: extends [extract_loc] at [ss0] and registers the fresh
    [prk] in [used_prk_loc]. *)
  Lemma KDF_hybE_bad_inv_extract_fresh_step i s0 s1 (ss0 : 'ss) (T : extract_loc) SIdx (U : used_prk_loc) (prk : 'prk) :
    KDF_hybE_bad_inv i (s0, s1) ->
    get_heap s0 extract_loc = T -> get_heap s1 extract_loc = T ->
    get_heap s0 ss_index_loc = SIdx ->
    get_heap s0 used_prk_loc = U -> get_heap s1 used_prk_loc = U ->
    getm SIdx ss0 <> None ->
    getm T ss0 = None ->
    getm U prk = None ->
    KDF_hybE_bad_inv i
      (set_heap (set_heap s0 extract_loc (setm T ss0 prk)) used_prk_loc (setm U prk tt),
       set_heap (set_heap s1 extract_loc (setm T ss0 prk)) used_prk_loc (setm U prk tt)).
  Proof.
    move=> Hinv HT0 HT1 HSI0 HU0 HU1 HSIss0ne HTss0 HUprk.
    case: Hinv => [Hig Hrel].
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons)
            (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hrel.
    rewrite HT0 HSI0 HU0 in Hrel.
    split.
    - move=> l Hl.
      apply: get_heap_after_common_double_update.
      exact: (Hig l Hl).
    - rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons)
              (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
      rewrite !(get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != used_prk_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != extract_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != used_prk_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != extract_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : mid_loc.1 != used_prk_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : mid_loc.1 != extract_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : eval_tbl_loc.1 != used_prk_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : eval_tbl_loc.1 != extract_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : ss_count_loc.1 != used_prk_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : ss_count_loc.1 != extract_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != used_prk_loc.1)).
      rewrite !get_set_heap_eq.
      move=> Hb.
      move: (Hrel Hb) => [Hc1 [Hc2 [Hc3 [Hc4a [Hc4b [Hc5 [Hc6 [Hc7 Hc8]]]]]]]].
      rewrite HSI0.
      have Hfresh : forall ss', getm T ss' <> Some prk.
      { move=> ss' Heq.
        have Hex : exists ss'', getm T ss'' = Some prk by exists ss'.
        move: ((proj2 (Hc2 prk)) Hex).
        rewrite HUprk. discriminate. }
      split.
      { move=> ss1 ss2 p.
        rewrite !setmE.
        case: (eqVneq ss1 ss0) => [-> | Hne1].
        { case: (eqVneq ss2 ss0) => [-> | Hne2] //.
          move=> [<-] Heq2.
          exfalso. exact: (Hfresh ss2 Heq2). }
        case: (eqVneq ss2 ss0) => [-> | Hne2].
        { move=> Heq1 [Heq2].
          exfalso.
          move: Heq1. rewrite -Heq2. exact: Hfresh ss1. }
        exact: Hc1 ss1 ss2 p. }
      split.
      { move=> p.
        rewrite setmE.
        case: (eqVneq p prk) => [-> | Hnep].
        { split.
          - move=> _. exists ss0. by rewrite setmE eq_refl.
          - done. }
        split.
        - move=> HU'. move: ((proj1 (Hc2 p)) HU') => [ss' HTss'].
          exists ss'. rewrite setmE.
          case: (eqVneq ss' ss0) => [Heq | Hne].
          + exfalso. subst ss'. rewrite HTss0 in HTss'. discriminate.
          + exact: HTss'.
        - move=> [ss' HTss'].
          move: HTss'. rewrite setmE.
          case: (eqVneq ss' ss0) => [Heq | Hne].
          + move=> Heq2. exfalso. move: Heq2 => [Heq2]. move: Hnep => /eqP. rewrite Heq2. done.
          + move=> HTss'. apply: (proj2 (Hc2 p)). exists ss'. exact: HTss'. }
      split; [exact: Hc3|].
      split.
      { move=> p info Hne.
        move: (Hc4a p info Hne) => [ss' HTss'].
        exists ss'.
        rewrite setmE.
        case: (eqVneq ss' ss0) => [Heq | Hne2].
        - exfalso. subst ss'. rewrite HTss0 in HTss'. discriminate.
        - exact: HTss'. }
      split.
      { move=> p info Hne.
        move: (Hc4b p info Hne) => [ss' HTss'].
        exists ss'.
        rewrite setmE.
        case: (eqVneq ss' ss0) => [Heq | Hne2].
        - exfalso. subst ss'. rewrite HTss0 in HTss'. discriminate.
        - exact: HTss'. }
      split.
      { move=> info Hne.
        move: (Hc5 info Hne) => [ss' [p' [HSss' HTss']]].
        exists ss', p'.
        split; [exact: HSss'|].
        rewrite setmE.
        case: (eqVneq ss' ss0) => [Heq | Hne2].
        - exfalso. subst ss'. rewrite HTss0 in HTss'. discriminate.
        - exact: HTss'. }
      split.
      { move=> ss1 p1.
        rewrite setmE.
        case: (eqVneq ss1 ss0) => [-> | Hne1].
        { move=> [<-].
          case: ifP => Heqb.
          { move/eqP: Heqb => Heqi.
            have HTevNone : forall info', get_heap s0 eval_tbl_loc info' = None.
            { move=> info'.
              case Heq: (get_heap s0 eval_tbl_loc info') => [y|] //.
              exfalso.
              have Hne_ : get_heap s0 eval_tbl_loc info' <> None by rewrite Heq.
              move: (Hc5 info' Hne_) => [ss'' [p'' [HSss'' HTss'']]].
              have Heqss : ss'' = ss0 := Hc3 ss'' ss0 i HSss'' Heqi.
              subst ss''.
              rewrite HTss0 in HTss''. discriminate. }
            split.
            - move=> info'. rewrite (HTevNone info').
              case Heq2: (get_heap s1 mid_loc (prk,info')) => [y|] //.
              exfalso.
              have Hne_ : get_heap s1 mid_loc (prk,info') <> None by rewrite Heq2.
              move: (Hc4b prk info' Hne_) => [ss'' HTss''].
              exact: (Hfresh ss'' HTss'').
            - move=> info'.
              case Heq2: (get_heap s0 mid_loc (prk,info')) => [y|] //.
              exfalso.
              have Hne_ : get_heap s0 mid_loc (prk,info') <> None by rewrite Heq2.
              move: (Hc4a prk info' Hne_) => [ss'' HTss''].
              exact: (Hfresh ss'' HTss''). }
          move=> info'.
          case Heq2: (get_heap s0 mid_loc (prk,info')) => [y|].
          - exfalso.
            have Hne_ : get_heap s0 mid_loc (prk,info') <> None by rewrite Heq2.
            move: (Hc4a prk info' Hne_) => [ss'' HTss''].
            exact: (Hfresh ss'' HTss'').
          - case Heq3: (get_heap s1 mid_loc (prk,info')) => [y|] //.
            exfalso.
            have Hne_ : get_heap s1 mid_loc (prk,info') <> None by rewrite Heq3.
            move: (Hc4b prk info' Hne_) => [ss'' HTss''].
            exact: (Hfresh ss'' HTss''). }
        move=> HTss1.
        exact: (Hc6 ss1 p1 HTss1). }
      split.
      { move=> ss1.
        rewrite setmE.
        case: (eqVneq ss1 ss0) => [Heq | Hne].
        - subst ss1. move=> Hcontra. exfalso. exact: (HSIss0ne Hcontra).
        - exact: (Hc7 ss1). }
      exact: Hc8.
  Qed.

  (* Non-owner table extension: [SIdx ss0 <> Some i], the fresh
    (ss0, prk) pair's answer is sampled once and written into BOTH
    [mid_loc]s at the same value [y]. *)
  Lemma KDF_hybE_bad_inv_mid_step i s0 s1 (ss0 : 'ss) (info : 'info) (T : extract_loc) SIdx (TmL TmR : mid_loc) (prk : 'prk) (y : 'out) :
    KDF_hybE_bad_inv i (s0, s1) ->
    get_heap s0 bad_loc = false ->
    get_heap s0 extract_loc = T -> get_heap s0 ss_index_loc = SIdx ->
    get_heap s0 mid_loc = TmL -> get_heap s1 mid_loc = TmR ->
    getm T ss0 = Some prk ->
    getm SIdx ss0 <> Some i ->
    getm TmL (prk, info) = None -> getm TmR (prk, info) = None ->
    KDF_hybE_bad_inv i
      (set_heap s0 mid_loc (setm TmL (prk, info) y),
       set_heap s1 mid_loc (setm TmR (prk, info) y)).
  Proof.
    move=> Hinv Hbad HT0 HSI0 HTmL0 HTmR1 HTss0 HSne HNoneL HNoneR.
    case: Hinv => [Hig Hrel].
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons)
            (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hrel.
    rewrite HT0 HSI0 HTmL0 HTmR1 Hbad in Hrel.
    split.
    - move=> l Hl.
      have Hne : l.1 != mid_loc.1.
      { apply/eqP => Heq.
        case/negP: Hl.
        rewrite Heq.
        apply: fhas_in.
        fmap_solve. }
      rewrite (get_set_heap_neq _ _ _ _ Hne) (get_set_heap_neq _ _ _ _ Hne).
      exact: (Hig l Hl).
    - rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons)
              (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
      rewrite !(get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != mid_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != mid_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != mid_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != mid_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : eval_tbl_loc.1 != mid_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : ss_count_loc.1 != mid_loc.1)).
      rewrite !get_set_heap_eq.
      move=> _.
      move: (Hrel erefl) => [Hc1 [Hc2 [Hc3 [Hc4a [Hc4b [Hc5 [Hc6 [Hc7 Hc8]]]]]]]].
      rewrite HT0 HSI0.
      split; [exact: Hc1|].
      split; [exact: Hc2|].
      split; [exact: Hc3|].
      split.
      { move=> p info' Hne.
        case: (eqVneq (p,info') (prk,info)) => [Heq | Hneq].
        - have Heqp := f_equal fst Heq.
          have Heqi := f_equal snd Heq.
          simpl in Heqp, Heqi.
          subst p info'.
          exists ss0.
          exact: HTss0.
        - move: Hne.
          rewrite setmE (negbTE Hneq).
          exact: Hc4a p info'. }
      split.
      { move=> p info' Hne.
        case: (eqVneq (p,info') (prk,info)) => [Heq | Hneq].
        - have Heqp := f_equal fst Heq.
          have Heqi := f_equal snd Heq.
          simpl in Heqp, Heqi.
          subst p info'.
          exists ss0.
          exact: HTss0.
        - move: Hne.
          rewrite setmE (negbTE Hneq).
          exact: Hc4b p info'. }
      split; [exact: Hc5|].
      split.
      { move=> ss1 p1 HT1.
        move: (Hc6 ss1 p1 HT1).
        case: (eqVneq p1 prk) => [Heqp | Hnep].
        { subst p1.
          have Heqss : ss1 = ss0 := Hc1 ss1 ss0 prk HT1 HTss0.
          subst ss1.
          case: ifP => Heqb.
          { exfalso.
            move/eqP: Heqb => Heqi.
            exact: (HSne Heqi). }
          move=> Hold info'.
          rewrite !setmE.
          case: (eqVneq (prk,info') (prk,info)) => [Heq2 | Hneq2].
          - have Heqi2 := f_equal snd Heq2.
            simpl in Heqi2.
            subst info'.
            done.
          - exact: (Hold info'). }
        move=> Hold.
        case: ifP => Heqb.
        - rewrite Heqb in Hold.
          case: Hold => [HoR HoL].
          split.
          + move=> info'.
            rewrite setmE.
            have -> : ((p1,info') == (prk,info)) = false.
            { apply/negP => /eqP [Heqp' _].
              case/negP: Hnep.
              apply/eqP.
              exact: Heqp'. }
            exact: (HoR info').
          + move=> info'.
            rewrite setmE.
            have -> : ((p1,info') == (prk,info)) = false.
            { apply/negP => /eqP [Heqp' _].
              case/negP: Hnep.
              apply/eqP.
              exact: Heqp'. }
            exact: (HoL info').
        - rewrite Heqb in Hold.
          move=> info'.
          rewrite !setmE.
          have -> : ((p1,info') == (prk,info)) = false.
          { apply/negP => /eqP [Heqp' _].
            case/negP: Hnep.
            apply/eqP.
            exact: Heqp'. }
          exact: (Hold info'). }
      split; [exact: Hc7|exact: Hc8].
  Qed.

  (* Owner table extension: [SIdx ss0 = Some i]; LHS writes the answer
    into [eval_tbl_loc] (keyed by [info]), RHS writes the SAME answer
    into [mid_loc] (keyed by [(prk, info)]). *)
  Lemma KDF_hybE_bad_inv_owner_step i s0 s1 (ss0 : 'ss) (info : 'info) (T : extract_loc) SIdx (Tev : eval_tbl_loc) (TmR : mid_loc) (prk : 'prk) (y : 'out) :
    KDF_hybE_bad_inv i (s0, s1) ->
    get_heap s0 bad_loc = false ->
    get_heap s0 extract_loc = T -> get_heap s0 ss_index_loc = SIdx ->
    get_heap s0 eval_tbl_loc = Tev -> get_heap s1 mid_loc = TmR ->
    getm T ss0 = Some prk ->
    getm SIdx ss0 = Some i ->
    getm Tev info = None -> getm TmR (prk, info) = None ->
    KDF_hybE_bad_inv i
      (set_heap s0 eval_tbl_loc (setm Tev info y),
       set_heap s1 mid_loc (setm TmR (prk, info) y)).
  Proof.
    move=> Hinv Hbad HT0 HSI0 HTev0 HTmR1 HTss0 HSeq HNoneTev HNoneTmR.
    case: Hinv => [Hig Hrel].
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons)
            (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hrel.
    rewrite HT0 HSI0 HTev0 HTmR1 Hbad in Hrel.
    split.
    - move=> l Hl.
      have Hne1 : l.1 != eval_tbl_loc.1.
      { apply/eqP => Heq.
        case/negP: Hl.
        rewrite Heq.
        apply: fhas_in.
        fmap_solve. }
      have Hne2 : l.1 != mid_loc.1.
      { apply/eqP => Heq.
        case/negP: Hl.
        rewrite Heq.
        apply: fhas_in.
        fmap_solve. }
      rewrite (get_set_heap_neq _ _ _ _ Hne1) (get_set_heap_neq _ _ _ _ Hne2).
      exact: (Hig l Hl).
    - rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons)
              (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
      rewrite !(get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != eval_tbl_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != eval_tbl_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != eval_tbl_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != eval_tbl_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : mid_loc.1 != eval_tbl_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : ss_count_loc.1 != eval_tbl_loc.1)).
      rewrite !get_set_heap_eq.
      move=> _.
      move: (Hrel erefl) => [Hc1 [Hc2 [Hc3 [Hc4a [Hc4b [Hc5 [Hc6 [Hc7 Hc8]]]]]]]].
      rewrite HT0 HSI0.
      split; [exact: Hc1|].
      split; [exact: Hc2|].
      split; [exact: Hc3|].
      split; [exact: Hc4a|].
      split.
      { move=> p info' Hne.
        case: (eqVneq (p,info') (prk,info)) => [Heq | Hneq].
        - have Heqp := f_equal fst Heq.
          have Heqi := f_equal snd Heq.
          simpl in Heqp, Heqi.
          subst p info'.
          exists ss0.
          exact: HTss0.
        - move: Hne.
          rewrite setmE (negbTE Hneq).
          exact: Hc4b p info'. }
      split.
      { move=> info' Hne.
        case: (eqVneq info' info) => [Heqi | Hneq].
        - subst info'.
          exists ss0, prk.
          split; [exact: HSeq | exact: HTss0].
        - move: Hne.
          rewrite setmE.
          have -> : (info' == info) = false by exact: negbTE.
          exact: Hc5 info'. }
      split.
      { move=> ss1 p1 HT1.
        move: (Hc6 ss1 p1 HT1) => Hold.
        case: ifP => Heqb.
        - move/eqP: Heqb => Heqi.
          have Heqss : ss1 = ss0 := Hc3 ss1 ss0 i Heqi HSeq.
          subst ss1.
          have Heqp : Some p1 = Some prk.
          { rewrite -HT1 HTss0.
            done. }
          case: Heqp => Heqp.
          subst p1.
          move: Hold.
          rewrite Heqi eq_refl.
          move=> [HoR HoL].
          split.
          + move=> info'.
            rewrite !setmE.
            case: (eqVneq info' info) => [Heqi2 | Hneq2].
            * subst info'.
              by rewrite eq_refl.
            * rewrite xpair_eqE eqxx /= (negbTE Hneq2).
              exact: (HoR info').
          + exact: HoL.
        - move=> info'.
          have Hnep : p1 <> prk.
          { move=> Heqp.
            subst p1.
            have Heqss : ss1 = ss0 := Hc1 ss1 ss0 prk HT1 HTss0.
            subst ss1.
            move: Heqb.
            rewrite HSeq eq_refl.
            done. }
          rewrite setmE.
          have -> : ((p1,info') == (prk,info)) = false.
          { apply/negP => /eqP Hcp.
            apply: Hnep.
            exact: (f_equal fst Hcp). }
          rewrite Heqb in Hold.
          exact: (Hold info'). }
      split; [exact: Hc7|exact: Hc8].
  Qed.

  (* Escape hatch once [bad_loc] is already [true]: the gated payload
    is vacuous, so [mid_loc]/[eval_tbl_loc] may be overwritten with
    ARBITRARY (possibly different, possibly absent) new values on
    either side without disturbing the invariant. *)
  Lemma KDF_hybE_bad_inv_bad_true_step i s0 s1 (mL mR : mid_loc) (eL eR : eval_tbl_loc) :
    KDF_hybE_bad_inv i (s0, s1) ->
    get_heap s0 bad_loc = true ->
    KDF_hybE_bad_inv i
      (set_heap (set_heap s0 mid_loc mL) eval_tbl_loc eL,
       set_heap (set_heap s1 mid_loc mR) eval_tbl_loc eR).
  Proof.
    move=> Hinv Hbad.
    case: Hinv => [Hig Hrel].
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons)
            (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hrel.
    split.
    - move=> l Hl.
      have Hne1 : l.1 != mid_loc.1.
      { apply/eqP => Heq.
        case/negP: Hl.
        rewrite Heq.
        apply: fhas_in.
        fmap_solve. }
      have Hne2 : l.1 != eval_tbl_loc.1.
      { apply/eqP => Heq.
        case/negP: Hl.
        rewrite Heq.
        apply: fhas_in.
        fmap_solve. }
      rewrite !(get_set_heap_neq _ _ _ _ Hne2) !(get_set_heap_neq _ _ _ _ Hne1).
      exact: (Hig l Hl).
    - rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons)
              (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
      rewrite !(get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != eval_tbl_loc.1)).
      rewrite !(get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != mid_loc.1)).
      rewrite Hbad.
      done.
  Qed.

  (* One-sided escape-hatch variants: only ONE side performs a table
    write (the other is untouched), still under [bad_loc = true]. *)
  Lemma KDF_hybE_bad_inv_bad_true_lhs_mid_step i s0 s1 (mL : mid_loc) :
    KDF_hybE_bad_inv i (s0, s1) ->
    get_heap s0 bad_loc = true ->
    KDF_hybE_bad_inv i (set_heap s0 mid_loc mL, s1).
  Proof.
    move=> Hinv Hbad.
    case: Hinv => [Hig Hrel].
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons)
            (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hrel.
    split.
    - move=> l Hl.
      have Hne : l.1 != mid_loc.1.
      { apply/eqP => Heq. case/negP: Hl. rewrite Heq. apply: fhas_in. fmap_solve. }
      rewrite (get_set_heap_neq _ _ _ _ Hne).
      exact: (Hig l Hl).
    - rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons)
              (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
      rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != mid_loc.1)).
      rewrite Hbad.
      done.
  Qed.

  Lemma KDF_hybE_bad_inv_bad_true_rhs_mid_step i s0 s1 (mR : mid_loc) :
    KDF_hybE_bad_inv i (s0, s1) ->
    get_heap s0 bad_loc = true ->
    KDF_hybE_bad_inv i (s0, set_heap s1 mid_loc mR).
  Proof.
    move=> Hinv Hbad.
    case: Hinv => [Hig Hrel].
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons)
            (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hrel.
    split.
    - move=> l Hl.
      have Hne : l.1 != mid_loc.1.
      { apply/eqP => Heq. case/negP: Hl. rewrite Heq. apply: fhas_in. fmap_solve. }
      rewrite (get_set_heap_neq _ _ _ _ Hne).
      exact: (Hig l Hl).
    - rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons)
              (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
      rewrite Hbad.
      done.
  Qed.

  Lemma KDF_hybE_bad_inv_bad_true_lhs_eval_step i s0 s1 (eL : eval_tbl_loc) :
    KDF_hybE_bad_inv i (s0, s1) ->
    get_heap s0 bad_loc = true ->
    KDF_hybE_bad_inv i (set_heap s0 eval_tbl_loc eL, s1).
  Proof.
    move=> Hinv Hbad.
    case: Hinv => [Hig Hrel].
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons)
            (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hrel.
    split.
    - move=> l Hl.
      have Hne : l.1 != eval_tbl_loc.1.
      { apply/eqP => Heq. case/negP: Hl. rewrite Heq. apply: fhas_in. fmap_solve. }
      rewrite (get_set_heap_neq _ _ _ _ Hne).
      exact: (Hig l Hl).
    - rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons)
              (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
      rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != eval_tbl_loc.1)).
      rewrite Hbad.
      done.
  Qed.

  (* Collision write during a fresh sample: [extract_loc] is extended
    diagonally at [ss0 -> prk] (no [used_prk_loc] update -- the collision
    means [prk] was already present) and [bad_loc] flips to [true] on
    both sides. Since the resulting gate is vacuously true, none of
    [Hc1]..[Hc8] need to be replayed. *)
  Lemma KDF_hybE_bad_inv_extract_bad_step i s0 s1 (ss0 : 'ss) (T : extract_loc) (prk : 'prk) :
    KDF_hybE_bad_inv i (s0, s1) ->
    get_heap s0 extract_loc = T -> get_heap s1 extract_loc = T ->
    KDF_hybE_bad_inv i
      (set_heap (set_heap s0 extract_loc (setm T ss0 prk)) bad_loc true,
       set_heap (set_heap s1 extract_loc (setm T ss0 prk)) bad_loc true).
  Proof.
    move=> Hinv HT0 HT1.
    case: Hinv => [Hig Hrel].
    split.
    - move=> l Hl.
      apply: get_heap_after_common_double_update.
      exact: (Hig l Hl).
    - rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons)
              (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
      rewrite get_set_heap_eq.
      move=> Hf; discriminate.
  Qed.

  (* Reusable "run [get_prk_bad ss0] on both sides diagonally" dance:
    covers ALL of [get_prk_bad]'s own internal branching (already-extracted,
    fresh-no-collision, fresh-collision) uniformly, independently of what
    the CALLER does with the resulting [prk] afterwards (the mid_loc leaf,
    the owner leaf, and the trivial [idx > i] leaf all start with exactly
    this). The two sides never diverge (no [mid_loc]/[eval_tbl_loc] access
    inside [get_prk_bad]), so the returned [prk] is equal on both sides
    UNCONDITIONALLY (no [bad_loc] gating needed here). *)
  Lemma KDF_hybE_bad_prk_dance i s0 s1 (ss0 : 'ss) :
    KDF_hybE_bad_inv i (s0, s1) ->
    getm (get_heap s0 ss_index_loc) ss0 <> None ->
    ⊢ ⦃ fun '(a,b) => a = s0 /\ b = s1 ⦄
      get_prk_bad ss0 ≈ get_prk_bad ss0
    ⦃ fun '(p0,s0') '(p1,s1') =>
        KDF_hybE_bad_inv i (s0', s1') /\ p0 = p1 /\
        getm (get_heap s0' extract_loc) ss0 = Some p0 /\
        get_heap s0' ss_index_loc = get_heap s0 ss_index_loc ⦄.
  Proof.
    move=> Hinv0 Hindexed.
    rewrite /get_prk_bad.
    apply: rpre_hypothesis_rule => s0' s1' [-> ->].
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(t0,t1) => t0=s0 /\ t1=s1).
    2: { move=> t0 t1 [/= -> ->]. done. }
    eapply (r_get_remember_lhs extract_loc _ _ (fun '(t0,t1) => t0=s0 /\ t1=s1)).
    move=> T.
    eapply (r_get_remember_rhs extract_loc _ _ ((fun '(t0,t1) => t0=s0 /\ t1=s1) ⋊ rem_lhs extract_loc T)).
    move=> T'.
    apply: rpre_hypothesis_rule => s2 s3 Hp.
    case: Hp => [[[/= -> ->] HT0] HT1].
    move: HT0 HT1. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=.
    move=> HT0 HT1.
    have Hnotin : extract_loc.1 \notin domm [fmap mid_loc;eval_tbl_loc]. { fmap_solve. }
    have HTT' : T = T'.
    { case: Hinv0 => [Hig _]. move: (Hig extract_loc Hnotin) => Heq.
      rewrite HT0 HT1 in Heq. exact: Heq. }
    subst T'.
    rewrite -HTT'.
    case HTss: (T ss0) => [prk|] /=.
    - apply: r_ret => t0 t1 [/= -> ->].
      split; [exact: Hinv0 | split; [done | split; [by rewrite HT0 | done] ] ].
    - eapply rpre_weaken_rule.
      1: instantiate (1 := fun '(t0,t1) => t0=s0 /\ t1=s1).
      2: { move=> t0 t1 [/= -> ->]. done. }
      apply: (r_uniform_bij _ _ _ _ id). 1: exists id; done.
      move=> prk.
      eapply (r_put_vs_put extract_loc (setm T ss0 prk) extract_loc (setm T ss0 prk) _ _
        (fun '(t0,t1) => t0=s0 /\ t1=s1)).
      set X := set_heap s0 extract_loc (setm T ss0 prk).
      set Y := set_heap s1 extract_loc (setm T ss0 prk).
      apply: rpre_hypothesis_rule => s2' s3' Hp.
      case: Hp => [s1'' [[s0'' [[-> ->] ->]] ->]].
      eapply rpre_weaken_rule.
      1: instantiate (1 := fun '(t0,t1) => t0=X /\ t1=Y).
      2: { move=> t0 t1 [/= -> ->]. done. }
      eapply (r_get_remember_lhs used_prk_loc _ _ (fun '(t0,t1) => t0=X /\ t1=Y)).
      move=> U.
      eapply (r_get_remember_rhs used_prk_loc _ _ ((fun '(t0,t1) => t0=X /\ t1=Y) ⋊ rem_lhs used_prk_loc U)).
      move=> U'.
      apply: rpre_hypothesis_rule => s4 s5 Hp2.
      case: Hp2 => [[[/= -> ->] HU0] HU1].
      move: HU0 HU1. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=.
      move=> HU0 HU1.
      have Hnotin2 : used_prk_loc.1 \notin domm [fmap mid_loc;eval_tbl_loc]. { fmap_solve. }
      have HUeq : get_heap s0 used_prk_loc = get_heap s1 used_prk_loc.
      { case: Hinv0 => [Hig _]. exact: (Hig used_prk_loc Hnotin2). }
      have HXU : get_heap X used_prk_loc = get_heap s0 used_prk_loc.
      { rewrite /X. rewrite (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != extract_loc.1)). done. }
      have HYU : get_heap Y used_prk_loc = get_heap s1 used_prk_loc.
      { rewrite /Y. rewrite (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != extract_loc.1)). done. }
      have HUU' : U = U'.
      { rewrite -HU0 -HU1 HXU HYU HUeq. done. }
      subst U'.
      rewrite -HUU'.
      case HUprk: (U prk) => [[]|] /=.
      + eapply rpre_weaken_rule.
        1: instantiate (1 := fun '(t0,t1) => t0=X /\ t1=Y).
        2: { move=> t0 t1 [/= -> ->]. done. }
        eapply (r_put_vs_put bad_loc true bad_loc true _ _ (fun '(t0,t1) => t0=X /\ t1=Y)).
        apply: r_ret => t0 t1 [s1'3 [[s0'3 [[-> ->] ->]] ->]].
        split; [ | split; [done | split] ].
        * rewrite /X /Y. exact: (KDF_hybE_bad_inv_extract_bad_step i s0 s1 ss0 T prk Hinv0 HT0 (esym HTT')).
        * rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != bad_loc.1)).
          rewrite /X get_set_heap_eq setmE eq_refl. done.
        * rewrite (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != bad_loc.1)).
          rewrite /X (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != extract_loc.1)). done.
      + eapply rpre_weaken_rule.
        1: instantiate (1 := fun '(t0,t1) => t0=X /\ t1=Y).
        2: { move=> t0 t1 [/= -> ->]. done. }
        eapply (r_put_vs_put used_prk_loc (setm U prk tt) used_prk_loc (setm U prk tt) _ _ (fun '(t0,t1) => t0=X /\ t1=Y)).
        apply: r_ret => t0 t1 [s1'4 [[s0'4 [[-> ->] ->]] ->]].
        split; [ | split; [done | split] ].
        * rewrite /X /Y.
          apply: (KDF_hybE_bad_inv_extract_fresh_step i s0 s1 ss0 T (get_heap s0 ss_index_loc) U prk
            Hinv0 HT0 (esym HTT') erefl _ _ Hindexed HTss HUprk).
          -- rewrite -HXU. exact: HU0.
          -- rewrite -HYU. exact: esym HUU'.
        * rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != used_prk_loc.1)).
          rewrite /X get_set_heap_eq setmE eq_refl. done.
        * rewrite (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != used_prk_loc.1)).
          rewrite /X (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != extract_loc.1)). done.
  Qed.

  (* Reusable "non-owner [mid_loc] lookup" dance: covers the code shared by
    the [idx < i] and [cnt < i] leaves once [get_prk_bad]'s own dance
    ([KDF_hybE_bad_prk_dance]) has already produced a common [prk] with
    [getm (get_heap s0 extract_loc) ss0 = Some prk]. *)
  Lemma KDF_hybE_bad_mid_dance i s0 s1 (ss0 : 'ss) (info0 : 'info) (prk : 'prk) :
    KDF_hybE_bad_inv i (s0, s1) ->
    getm (get_heap s0 extract_loc) ss0 = Some prk ->
    getm (get_heap s0 ss_index_loc) ss0 <> Some i ->
    ⊢ ⦃ fun '(a,b) => a = s0 /\ b = s1 ⦄
      (T2 ← get mid_loc ;;
       match T2 (prk, info0) with
       | Some y => ret y
       | None => y <$ uniform Out_N ;; #put mid_loc := setm T2 (prk, info0) y ;; ret y
       end)
      ≈
      (T2 ← get mid_loc ;;
       match T2 (prk, info0) with
       | Some y => ret y
       | None => y <$ uniform Out_N ;; #put mid_loc := setm T2 (prk, info0) y ;; ret y
       end)
    ⦃ fun '(b0,s0') '(b1,s1') =>
        KDF_hybE_bad_inv i (s0', s1') /\ (get_heap s0' bad_loc = false -> b0 = b1) ⦄.
  Proof.
    move=> Hinv0 HTss0 Hne.
    eapply (r_get_remember_lhs mid_loc _ _ (fun '(a,b) => a = s0 /\ b = s1)).
    move=> TmL.
    eapply (r_get_remember_rhs mid_loc _ _ ((fun '(a,b) => a = s0 /\ b = s1) ⋊ rem_lhs mid_loc TmL)).
    move=> TmR.
    apply: rpre_hypothesis_rule => s0' s1' Hp.
    case: Hp => [[[/= -> ->] HTmL] HTmR].
    move: HTmL HTmR. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=.
    move=> HTmL HTmR.
    case: (boolP (get_heap s0 bad_loc)) => Hbad.
    - (* bad = true *)
      case HeqL: (TmL (prk, info0)) => [yL|]; case HeqR: (TmR (prk, info0)) => [yR|].
      + apply: r_ret => t0 t1 [/= -> ->].
        split; [exact: Hinv0 | move=> Hf; rewrite Hf in Hbad; discriminate].
      + apply r_const_sample_R. 1: exact _.
        move=> yR'.
        eapply rpre_weaken_rule.
        1: instantiate (1 := fun '(t0,t1) => t0=s0 /\ t1=s1).
        2: { move=> t0 t1 [/= -> ->]. done. }
        eapply (r_put_rhs mid_loc (setm TmR (prk, info0) yR') _ _ (fun '(t0,t1) => t0=s0 /\ t1=s1)).
        apply: r_ret => t0 t1 [s1'' [[-> ->] ->]].
        have Hbad' : get_heap s0 bad_loc = true := Hbad.
        split.
        * exact: (KDF_hybE_bad_inv_bad_true_rhs_mid_step i s0 s1 (setm TmR (prk, info0) yR') Hinv0 Hbad').
        * move=> Hf; rewrite Hf in Hbad'; discriminate.
      + apply r_const_sample_L. 1: exact _.
        move=> yL'.
        eapply rpre_weaken_rule.
        1: instantiate (1 := fun '(t0,t1) => t0=s0 /\ t1=s1).
        2: { move=> t0 t1 [/= -> ->]. done. }
        eapply (r_put_lhs mid_loc (setm TmL (prk, info0) yL') _ _ (fun '(t0,t1) => t0=s0 /\ t1=s1)).
        apply: r_ret => t0 t1 [s0'' [[-> ->] ->]].
        have Hbad' : get_heap s0 bad_loc = true := Hbad.
        split.
        * exact: (KDF_hybE_bad_inv_bad_true_lhs_mid_step i s0 s1 (setm TmL (prk, info0) yL') Hinv0 Hbad').
        * move=> Hf.
          rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != mid_loc.1)) in Hf.
          rewrite Hf in Hbad'; discriminate.
      + apply r_const_sample_L. 1: exact _.
        move=> yL.
        eapply rpre_weaken_rule.
        1: instantiate (1 := fun '(t0,t1) => t0=s0 /\ t1=s1).
        2: { move=> t0 t1 [/= -> ->]. done. }
        eapply (r_put_lhs mid_loc (setm TmL (prk, info0) yL) _ _ (fun '(t0,t1) => t0=s0 /\ t1=s1)).
        apply r_const_sample_R. 1: exact _.
        move=> yR.
        eapply rpre_weaken_rule.
        1: instantiate (1 := fun '(t0,t1) => t0=set_heap s0 mid_loc (setm TmL (prk,info0) yL) /\ t1=s1).
        2: { move=> t0 t1 [s0'' [[-> ->] ->]]. done. }
        eapply (r_put_rhs mid_loc (setm TmR (prk, info0) yR) _ _ (fun '(t0,t1) => t0=set_heap s0 mid_loc (setm TmL (prk,info0) yL) /\ t1=s1)).
        apply: r_ret => t0 t1 [s1'' [[-> ->] ->]].
        have Hbad' : get_heap s0 bad_loc = true := Hbad.
        have Hbad'' : get_heap (set_heap s0 mid_loc (setm TmL (prk, info0) yL)) bad_loc = true.
        { by rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != mid_loc.1)). }
        split.
        * exact: (KDF_hybE_bad_inv_bad_true_rhs_mid_step i (set_heap s0 mid_loc (setm TmL (prk, info0) yL)) s1
             (setm TmR (prk, info0) yR)
             (KDF_hybE_bad_inv_bad_true_lhs_mid_step i s0 s1 (setm TmL (prk, info0) yL) Hinv0 Hbad')
             Hbad'').
        * move=> Hf; rewrite Hf in Hbad''; discriminate.
    - (* bad = false *)
      move/negbTE: Hbad => Hbad.
      have [Hig Hrel] := Hinv0.
      rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons)
              (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hrel.
      rewrite HTmL HTmR Hbad in Hrel.
      move: (Hrel erefl) => [Hc1 [Hc2 [Hc3 [Hc4a [Hc4b [Hc5 [Hc6 [Hc7 Hc8]]]]]]]].
      have Hne' := introF eqP Hne.
      move: (Hc6 ss0 prk HTss0). rewrite Hne' => Heq.
      rewrite -(Heq info0).
      case HeqL: (TmL (prk, info0)) => [y|] /=.
      + apply: r_ret => t0 t1 [/= -> ->].
        split; [exact: Hinv0 | done].
      + have HTmRNone : TmR (prk, info0) = None.
        { rewrite -(Heq info0). exact: HeqL. }
        eapply rpre_weaken_rule.
        1: instantiate (1 := fun '(t0,t1) => t0=s0 /\ t1=s1).
        2: { move=> t0 t1 [/= -> ->]. done. }
        apply: (r_uniform_bij _ _ _ _ id). 1: exists id; done.
        move=> y.
        eapply (r_put_vs_put mid_loc (setm TmL (prk, info0) y) mid_loc (setm TmR (prk, info0) y) _ _
          (fun '(t0,t1) => t0=s0 /\ t1=s1)).
        apply: r_ret => t0 t1 [s1'' [[s0'' [[-> ->] ->]] ->]].
        split; [ | done].
        exact: (KDF_hybE_bad_inv_mid_step i s0 s1 ss0 info0 (get_heap s0 extract_loc) (get_heap s0 ss_index_loc)
          TmL TmR prk y Hinv0 Hbad erefl erefl HTmL HTmR HTss0 Hne HeqL HTmRNone).
  Qed.

  (* Reusable "owner [eval_tbl_loc]/[mid_loc] lookup" dance: covers the code
    shared by the [idx == i] and [cnt == i] leaves once [get_prk_bad]'s own
    dance has produced a common [prk] with
    [getm (get_heap s0 extract_loc) ss0 = Some prk] AND [ss0] owns index
    [i]. LHS reads/writes [eval_tbl_loc] (keyed by [info0]); RHS
    reads/writes [mid_loc] (keyed by [(prk, info0)]). *)
  Lemma KDF_hybE_bad_owner_dance i s0 s1 (ss0 : 'ss) (info0 : 'info) (prk : 'prk) :
    KDF_hybE_bad_inv i (s0, s1) ->
    getm (get_heap s0 extract_loc) ss0 = Some prk ->
    getm (get_heap s0 ss_index_loc) ss0 = Some i ->
    ⊢ ⦃ fun '(a,b) => a = s0 /\ b = s1 ⦄
      (T ← get eval_tbl_loc ;;
       match T info0 with
       | Some y => ret y
       | None => y <$ uniform Out_N ;; #put eval_tbl_loc := setm T info0 y ;; ret y
       end)
      ≈
      (T2 ← get mid_loc ;;
       match T2 (prk, info0) with
       | Some y => ret y
       | None => y <$ uniform Out_N ;; #put mid_loc := setm T2 (prk, info0) y ;; ret y
       end)
    ⦃ fun '(b0,s0') '(b1,s1') =>
        KDF_hybE_bad_inv i (s0', s1') /\ (get_heap s0' bad_loc = false -> b0 = b1) ⦄.
  Proof.
    move=> Hinv0 HTss0 HSeq.
    eapply (r_get_remember_lhs eval_tbl_loc _ _ (fun '(a,b) => a = s0 /\ b = s1)).
    move=> Tev.
    eapply (r_get_remember_rhs mid_loc _ _ ((fun '(a,b) => a = s0 /\ b = s1) ⋊ rem_lhs eval_tbl_loc Tev)).
    move=> TmR.
    apply: rpre_hypothesis_rule => s0' s1' Hp.
    case: Hp => [[[/= -> ->] HTev] HTmR].
    move: HTev HTmR. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=.
    move=> HTev HTmR.
    case: (boolP (get_heap s0 bad_loc)) => Hbad.
    - (* bad = true *)
      case HeqL: (Tev info0) => [yL|]; case HeqR: (TmR (prk, info0)) => [yR|].
      + apply: r_ret => t0 t1 [/= -> ->].
        split; [exact: Hinv0 | move=> Hf; rewrite Hf in Hbad; discriminate].
      + apply r_const_sample_R. 1: exact _.
        move=> yR'.
        eapply rpre_weaken_rule.
        1: instantiate (1 := fun '(t0,t1) => t0=s0 /\ t1=s1).
        2: { move=> t0 t1 [/= -> ->]. done. }
        eapply (r_put_rhs mid_loc (setm TmR (prk, info0) yR') _ _ (fun '(t0,t1) => t0=s0 /\ t1=s1)).
        apply: r_ret => t0 t1 [s1'' [[-> ->] ->]].
        have Hbad' : get_heap s0 bad_loc = true := Hbad.
        split.
        * exact: (KDF_hybE_bad_inv_bad_true_rhs_mid_step i s0 s1 (setm TmR (prk, info0) yR') Hinv0 Hbad').
        * move=> Hf; rewrite Hf in Hbad'; discriminate.
      + apply r_const_sample_L. 1: exact _.
        move=> yL'.
        eapply rpre_weaken_rule.
        1: instantiate (1 := fun '(t0,t1) => t0=s0 /\ t1=s1).
        2: { move=> t0 t1 [/= -> ->]. done. }
        eapply (r_put_lhs eval_tbl_loc (setm Tev info0 yL') _ _ (fun '(t0,t1) => t0=s0 /\ t1=s1)).
        apply: r_ret => t0 t1 [s0'' [[-> ->] ->]].
        have Hbad' : get_heap s0 bad_loc = true := Hbad.
        split.
        * exact: (KDF_hybE_bad_inv_bad_true_lhs_eval_step i s0 s1 (setm Tev info0 yL') Hinv0 Hbad').
        * move=> Hf.
          rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != eval_tbl_loc.1)) in Hf.
          rewrite Hf in Hbad'; discriminate.
      + apply r_const_sample_L. 1: exact _.
        move=> yL.
        eapply rpre_weaken_rule.
        1: instantiate (1 := fun '(t0,t1) => t0=s0 /\ t1=s1).
        2: { move=> t0 t1 [/= -> ->]. done. }
        eapply (r_put_lhs eval_tbl_loc (setm Tev info0 yL) _ _ (fun '(t0,t1) => t0=s0 /\ t1=s1)).
        apply r_const_sample_R. 1: exact _.
        move=> yR.
        eapply rpre_weaken_rule.
        1: instantiate (1 := fun '(t0,t1) => t0=set_heap s0 eval_tbl_loc (setm Tev info0 yL) /\ t1=s1).
        2: { move=> t0 t1 [s0'' [[-> ->] ->]]. done. }
        eapply (r_put_rhs mid_loc (setm TmR (prk, info0) yR) _ _ (fun '(t0,t1) => t0=set_heap s0 eval_tbl_loc (setm Tev info0 yL) /\ t1=s1)).
        apply: r_ret => t0 t1 [s1'' [[-> ->] ->]].
        have Hbad' : get_heap s0 bad_loc = true := Hbad.
        have Hbad'' : get_heap (set_heap s0 eval_tbl_loc (setm Tev info0 yL)) bad_loc = true.
        { by rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != eval_tbl_loc.1)). }
        split.
        * exact: (KDF_hybE_bad_inv_bad_true_rhs_mid_step i (set_heap s0 eval_tbl_loc (setm Tev info0 yL)) s1
             (setm TmR (prk, info0) yR)
             (KDF_hybE_bad_inv_bad_true_lhs_eval_step i s0 s1 (setm Tev info0 yL) Hinv0 Hbad')
             Hbad'').
        * move=> Hf; rewrite Hf in Hbad''; discriminate.
    - (* bad = false *)
      move/negbTE: Hbad => Hbad.
      have [Hig Hrel] := Hinv0.
      rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons)
              (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in Hrel.
      rewrite HTev HTmR Hbad in Hrel.
      move: (Hrel erefl) => [Hc1 [Hc2 [Hc3 [Hc4a [Hc4b [Hc5 [Hc6 [Hc7 Hc8]]]]]]]].
      move: (Hc6 ss0 prk HTss0). rewrite (introT eqP HSeq) => Heq.
      case: Heq => [HoR HoL].
      case HeqL: (Tev info0) => [y|] /=.
      + have HeqR : TmR (prk, info0) = Some y.
        { rewrite (HoR info0). exact: HeqL. }
        rewrite HeqR.
        apply: r_ret => t0 t1 [/= -> ->].
        split; [exact: Hinv0 | done].
      + have HeqR : TmR (prk, info0) = None.
        { rewrite (HoR info0). exact: HeqL. }
        rewrite HeqR.
        eapply rpre_weaken_rule.
        1: instantiate (1 := fun '(t0,t1) => t0=s0 /\ t1=s1).
        2: { move=> t0 t1 [/= -> ->]. done. }
        apply: (r_uniform_bij _ _ _ _ id). 1: exists id; done.
        move=> y.
        eapply (r_put_vs_put eval_tbl_loc (setm Tev info0 y) mid_loc (setm TmR (prk, info0) y) _ _
          (fun '(t0,t1) => t0=s0 /\ t1=s1)).
        apply: r_ret => t0 t1 [s1'' [[s0'' [[-> ->] ->]] ->]].
        split; [ | done].
        exact: (KDF_hybE_bad_inv_owner_step i s0 s1 ss0 info0 (get_heap s0 extract_loc) (get_heap s0 ss_index_loc)
          Tev TmR prk y Hinv0 Hbad erefl erefl HTev HTmR HTss0 HSeq HeqL HeqR).
  Qed.

  (* READING GUIDE for the proof of [KDF_hybE_bad_eq_up_to_bad] below
    (now fully Qed'd; this recipe was the plan it was assembled from and
    is kept as a map of the script): every leaf is the SAME two moves --
    a diagonal walk through the [get_prk_bad]-shaped code, closed by
    [KDF_hybE_bad_inv_extract_fresh_step] / [KDF_hybE_bad_inv_mid_step] /
    [KDF_hybE_bad_inv_owner_step] / the bad_true_* one-sided lemmas.
    Recipe, precisely:

    Opening (shared by everything below):
      move=> id S T x hasE. fmap_invert hasE. simplify_linking.
      case: x => ss info /=. ssprove_code_simpl.
      apply: r_get_vs_get_remember => SIdx.
      case Hidx: (SIdx ss) => [idx|] /=.

    Branch "SIdx ss = Some idx" (already indexed), sub-split
    case Hlt: (idx < i)%N:

    - [idx < i] (true): have Hlt1 : (idx < i.+1)%N := ltn_trans Hlt (ltnSn i).
      rewrite Hlt1. Now LHS/RHS code is LITERALLY identical (both read
      [mid_loc]). apply: r_get_vs_get_remember => T. case HTss: (T ss) =>
      [prk|].
        * [T ss = Some prk] (DONE, Qed'd interactively): remember mid_loc on
          both sides separately (r_get_remember_lhs/rhs), reach concrete
          s0/s1 via rpre_hypothesis_rule, IMMEDIATELY reshape the
          precondition to pair-pattern form via
          `eapply rpre_weaken_rule. 1: instantiate (1 := fun '(t0,t1) =>
          t0=s0/\t1=s1). 2: { move=> t0 t1 [/= -> ->]. done. }`
          (r_put_lhs/r_put_rhs's internal HO unification for `pre` only
          succeeds against a literal `fun '(a,b) => ...` pattern, NOT the
          `fun s => s.1=.. /\ s.2=..` shape `rpre_hypothesis_rule` itself
          produces -- this mismatch is the #1 time-sink in this proof).
          Then `case: (boolP (get_heap s0 bad_loc)) => Hbad`; true branch:
          case on TmL/TmR's (prk,info) lookup independently (4 combos), each
          closed by r_const_sample_L/R + KDF_hybE_bad_inv_bad_true_{lhs,rhs}
          _mid_step (supply `pre` explicitly to r_put_lhs/r_put_rhs every
          time, e.g. `eapply (r_put_rhs mid_loc v _ _ (fun '(a,b) =>
          a=s0/\b=s1))`); false branch: derive `SIdx ss <> Some i` from
          Hidx+Hlt, apply Hc6 (hyb_tbl_match) to get the else-arm equality
          TmL(prk,info)=TmR(prk,info), rewrite, case ONCE (named, `case
          Heq0: (TmL (prk,info)) => [yL|]`) and close via r_ret / r_uniform_
          bij(id)+KDF_hybE_bad_inv_mid_step (needs Hig/Hrel reassembled via
          `split; [exact Hig | rewrite <the 8x rel_app_cons+rel_app_nil
          unfold> HT0 HSI0 HTmL0 HTmR1 Hbad; exact Hrel]`, NOT `exact (conj
          Hig Hrel)` -- `inv_conj`/`rel_app` are `simpl never`, so `split`
          works but `conj` needs the unfolded form spelled out first).
        * [T ss = None] (NOT YET DONE -- this is where the session ran out
          of budget; last live goal, verbatim modulo cosmetic var names):
          `⊢ ⦃ pre ⋊ rem_lhs ss_index_loc SIdx ⋊ rem_rhs ss_index_loc SIdx
             ⋊ rem_lhs extract_loc T ⋊ rem_rhs extract_loc T ⦄
             a ← sample uniform PRK_N ;; #put extract_loc := setm T ss a ;;
             v1 ← get used_prk_loc ;; match v1 a with
             | Some _ => #put bad_loc := true ;; T2 ← get mid_loc ;; ...
             | None => #put used_prk_loc := setm v1 a tt ;;
                 T2 ← get mid_loc ;; ...
             end ≈ <IDENTICAL RHS>
             ⦃ fun '(b0,s0) '(b1,s1) => KDF_hybE_bad_inv i (s0,s1) /\
                 (get_heap s0 (bad_loc 4) = false -> b0=b1) ⦄`
          -- couple the sample (r_uniform_bij id), the extract_loc put
          (r_put_vs_put), the used_prk_loc get (r_get_vs_get_remember),
          then case on `Used a`: None sub-case closes with
          KDF_hybE_bad_inv_extract_fresh_step (needs `SIdx ss <> None`,
          FALSE here since Hidx says Some idx -- fine, that hypothesis IS
          satisfiable) immediately followed by the SAME Some-prk-style
          table-step (hyb_tbl_match else-arm, now using freshness for the
          new (ss,a) pair -- extract_fresh_step's own proof already
          established the else-arm fact for the NEW entry, so after
          restoring the invariant the table step is identical in shape to
          the T-ss-Some-prk leaf above, modulo threading `a` for `prk`);
          Some sub-case (collision) sets bad:=true on both sides
          (r_put_vs_put, trivial heap_ignore/rel_app-vacuous re-establish)
          then falls into the SAME bad=true 4-way table split as above.

    - [idx == i] (owner leaf, NOT YET DONE): LHS ghost-extracts then reads
      [eval_tbl_loc]; RHS extracts then reads [mid_loc]. Diagonal couple
      get_prk_bad exactly as above (T ss Some/None), then close the table
      step with KDF_hybE_bad_inv_owner_step (bad=false case; needs `getm
      Tev info = None` and `getm TmR (prk,info) = None`, both obtained via
      Hc6's owner-arm applied at (ss,prk) -- symmetric to the else-arm
      lookup above) or the same bad=true one-sided escape (using
      KDF_hybE_bad_inv_bad_true_lhs_eval_step for LHS + _rhs_mid_step for
      RHS, composed sequentially, NOT via the retired 4-param
      KDF_hybE_bad_inv_bad_true_step).

    - [else] (idx > i, no table -- the easiest leaf): both sides run
      `... ret (PRF info a)` verbatim identically;
      couple get_prk_bad diagonally (extract_fresh_step / trivial-Some, no
      bad-casing needed at all since there is no table read -- outputs
      `PRF info a = PRF info a` unconditionally), finish with r_ret.

    Branch "SIdx ss = None" (fresh index): get cnt := get_heap ss_count_loc
    (r_get_vs_get_remember), r_put_vs_put twice (ss_count_loc, ss_index_loc)
    restored via KDF_hybE_bad_inv_index_step, THEN split `cnt < i` /
    `cnt == i` / else exactly mirroring the three leaves above -- except
    `T ss = None` is now KNOWN unconditionally (no case needed) via
    `ss_unindexed_unextracted` (Hc7) applied to the fresh `SIdx ss = None`,
    so each of these three leaves is a strict subset of the corresponding
    "Some idx, T ss = None" work above (same lemmas, same shape), with the
    `cnt == i` leaf additionally needing KDF_hybE_bad_inv_owner_step's
    `eval_tbl_owner`+`ss_index_injective`-driven Tev-emptiness argument
    (already fully worked out and proved AS PART OF
    KDF_hybE_bad_inv_extract_fresh_step's own hyb_tbl_match conjunct --
    that lemma's postcondition already gives the freshly-extracted (ss,a)
    pair's owner-arm fact for free, so the table step here is just
    "read known-None on both sides, sample, put").

    All 8 supporting lemmas above (index_step, extract_fresh_step,
    mid_step, owner_step, bad_true_step, bad_true_lhs_mid_step,
    bad_true_rhs_mid_step, bad_true_lhs_eval_step) are Qed'd and are
    exactly what every leaf calls -- the proof script below is precisely
    this assembly, plus the two intro-pattern/precond gotchas documented
    above. *)
  Lemma KDF_hybE_bad_eq_up_to_bad i :
    eq_up_to_bad DERIVE_export (KDF_hybE_bad_inv i) 4
      (KDF_hybE_bad i) (KDF_hyb_bad i.+1).
  Proof.
    move=> id S T x hasE. fmap_invert hasE. simplify_linking.
    case: x => ss info /=. ssprove_code_simpl.
    apply: r_get_vs_get_remember => SIdx.
    case Hidx: (SIdx ss) => [idx|] /=.
    - case Hlt: (idx < i)%N.
      + (* idx < i *)
        have Hlt1 : (idx < i.+1)%N := ltn_trans Hlt (ltnSn i).
        rewrite Hlt1.
        apply: rpre_hypothesis_rule => s0 s1 Hp.
        case: Hp => [[Hinv0 HSI0] HSI1].
        move: HSI0 HSI1. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=. move=> HSI0 HSI1.
        eapply rpre_weaken_rule.
        1: instantiate (1 := fun '(t0,t1) => t0=s0 /\ t1=s1).
        2: { move=> t0 t1 [/= -> ->]. done. }
        rewrite /get_prk_bad.
        eapply (r_get_remember_lhs extract_loc _ _ (fun '(t0,t1) => t0=s0 /\ t1=s1)).
        move=> Tex.
        eapply (r_get_remember_rhs extract_loc _ _ ((fun '(t0,t1) => t0=s0 /\ t1=s1) ⋊ rem_lhs extract_loc Tex)).
        move=> Tex'.
        apply: rpre_hypothesis_rule => s2 s3 Hp.
        case: Hp => [[[/= -> ->] HT0] HT1].
        move: HT0 HT1. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=. move=> HT0 HT1.
        have Hnotin : extract_loc.1 \notin domm [fmap mid_loc;eval_tbl_loc]. { fmap_solve. }
        have HTT' : Tex = Tex'.
        { case: Hinv0 => [Hig _]. move: (Hig extract_loc Hnotin) => Heq. rewrite HT0 HT1 in Heq. exact: Heq. }
        subst Tex'.
        rewrite -HTT'.
        case HTss: (Tex ss) => [prk|] /=.
        * (* T ss = Some prk *)
          eapply rpre_weaken_rule.
          1: instantiate (1 := fun '(t0,t1) => t0=s0 /\ t1=s1).
          2: { move=> t0 t1 [/= -> ->]. done. }
          apply: (KDF_hybE_bad_mid_dance i s0 s1 ss info prk Hinv0).
          -- rewrite HT0. exact: HTss.
          -- rewrite HSI0 Hidx. move=> [Heqi]. move: Hlt. rewrite Heqi ltnn. done.
        * (* T ss = None: fresh sample *)
          eapply rpre_weaken_rule.
          1: instantiate (1 := fun '(t0,t1) => t0=s0 /\ t1=s1).
          2: { move=> t0 t1 [/= -> ->]. done. }
          apply: (r_uniform_bij _ _ _ _ id). 1: exists id; done.
          move=> prk.
          eapply (r_put_vs_put extract_loc (setm Tex ss prk) extract_loc (setm Tex ss prk) _ _
            (fun '(t0,t1) => t0=s0 /\ t1=s1)).
          set X := set_heap s0 extract_loc (setm Tex ss prk).
          set Y := set_heap s1 extract_loc (setm Tex ss prk).
          apply: rpre_hypothesis_rule => s2' s3' Hp.
          case: Hp => [s1'' [[s0'' [[-> ->] ->]] ->]].
          eapply rpre_weaken_rule.
          1: instantiate (1 := fun '(t0,t1) => t0=X /\ t1=Y).
          2: { move=> t0 t1 [/= -> ->]. done. }
          eapply (r_get_remember_lhs used_prk_loc _ _ (fun '(t0,t1) => t0=X /\ t1=Y)).
          move=> U.
          eapply (r_get_remember_rhs used_prk_loc _ _ ((fun '(t0,t1) => t0=X /\ t1=Y) ⋊ rem_lhs used_prk_loc U)).
          move=> U'.
          apply: rpre_hypothesis_rule => s4 s5 Hp2.
          case: Hp2 => [[[/= -> ->] HU0] HU1].
          move: HU0 HU1. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=. move=> HU0 HU1.
          have Hnotin2 : used_prk_loc.1 \notin domm [fmap mid_loc;eval_tbl_loc]. { fmap_solve. }
          have HUeq : get_heap s0 used_prk_loc = get_heap s1 used_prk_loc.
          { case: Hinv0 => [Hig _]. exact: (Hig used_prk_loc Hnotin2). }
          have HXU : get_heap X used_prk_loc = get_heap s0 used_prk_loc.
          { rewrite /X. rewrite (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != extract_loc.1)). done. }
          have HYU : get_heap Y used_prk_loc = get_heap s1 used_prk_loc.
          { rewrite /Y. rewrite (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != extract_loc.1)). done. }
          have HUU' : U = U'.
          { rewrite -HU0 -HU1 HXU HYU HUeq. done. }
          subst U'.
          rewrite -HUU'.
          case HUprk: (U prk) => [[]|] /=.
          -- (* collision: bad := true *)
            eapply rpre_weaken_rule.
            1: instantiate (1 := fun '(t0,t1) => t0=X /\ t1=Y).
            2: { move=> t0 t1 [/= -> ->]. done. }
            eapply (r_put_vs_put bad_loc true bad_loc true _ _ (fun '(t0,t1) => t0=X /\ t1=Y)).
            have Hinv2 : KDF_hybE_bad_inv i (set_heap X bad_loc true, set_heap Y bad_loc true).
            { rewrite /X /Y. exact: (KDF_hybE_bad_inv_extract_bad_step i s0 s1 ss Tex prk Hinv0 HT0 (esym HTT')). }
            have Hne2 : getm (get_heap (set_heap X bad_loc true) ss_index_loc) ss <> Some i.
            { rewrite (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != bad_loc.1)).
              rewrite /X (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != extract_loc.1)).
              rewrite HSI0 Hidx. move=> [Heqi]. move: Hlt. rewrite Heqi ltnn. done. }
            eapply rpre_weaken_rule.
            1: instantiate (1 := fun '(t0,t1) => t0=set_heap X bad_loc true /\ t1=set_heap Y bad_loc true).
            ++ apply: (KDF_hybE_bad_mid_dance i (set_heap X bad_loc true) (set_heap Y bad_loc true) ss info prk Hinv2 _ Hne2).
               rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != bad_loc.1)).
               rewrite /X get_set_heap_eq setmE eq_refl. done.
            ++ move=> t0 t1 [s1x [[s0x [[-> ->] ->]] ->]]. done.
          -- (* fresh: no collision *)
            eapply rpre_weaken_rule.
            1: instantiate (1 := fun '(t0,t1) => t0=X /\ t1=Y).
            2: { move=> t0 t1 [/= -> ->]. done. }
            eapply (r_put_vs_put used_prk_loc (setm U prk tt) used_prk_loc (setm U prk tt) _ _ (fun '(t0,t1) => t0=X /\ t1=Y)).
            have Hinv2 : KDF_hybE_bad_inv i (set_heap X used_prk_loc (setm U prk tt), set_heap Y used_prk_loc (setm U prk tt)).
            { rewrite /X /Y.
              apply: (KDF_hybE_bad_inv_extract_fresh_step i s0 s1 ss Tex (get_heap s0 ss_index_loc) U prk
                Hinv0 HT0 (esym HTT') erefl _ _ (_ : getm (get_heap s0 ss_index_loc) ss <> None) HTss HUprk).
              - rewrite -HXU. exact: HU0.
              - rewrite -HYU. exact: esym HUU'.
              - rewrite HSI0 Hidx. done. }
            have Hne2 : getm (get_heap (set_heap X used_prk_loc (setm U prk tt)) ss_index_loc) ss <> Some i.
            { rewrite (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != used_prk_loc.1)).
              rewrite /X (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != extract_loc.1)).
              rewrite HSI0 Hidx. move=> [Heqi]. move: Hlt. rewrite Heqi ltnn. done. }
            eapply rpre_weaken_rule.
            1: instantiate (1 := fun '(t0,t1) => t0=set_heap X used_prk_loc (setm U prk tt) /\ t1=set_heap Y used_prk_loc (setm U prk tt)).
            ++ apply: (KDF_hybE_bad_mid_dance i (set_heap X used_prk_loc (setm U prk tt)) (set_heap Y used_prk_loc (setm U prk tt)) ss info prk Hinv2 _ Hne2).
               rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != used_prk_loc.1)).
               rewrite /X get_set_heap_eq setmE eq_refl. done.
            ++ move=> t0 t1 [s1x [[s0x [[-> ->] ->]] ->]]. done.
      + (* idx >= i *)
        case Hcmp: (idx == i).
        * (* idx == i: owner leaf *)
          have Hlt2 : (idx < i.+1)%N. { move/eqP: Hcmp => ->. exact: ltnSn i. }
          rewrite Hlt2.
          apply: rpre_hypothesis_rule => s0 s1 Hp.
          case: Hp => [[Hinv0 HSI0] HSI1].
          move: HSI0 HSI1. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=. move=> HSI0 HSI1.
          eapply rpre_weaken_rule.
          1: instantiate (1 := fun '(t0,t1) => t0=s0 /\ t1=s1).
          2: { move=> t0 t1 [/= -> ->]. done. }
          rewrite /get_prk_bad.
          eapply (r_get_remember_lhs extract_loc _ _ (fun '(t0,t1) => t0=s0 /\ t1=s1)).
          move=> Tex.
          eapply (r_get_remember_rhs extract_loc _ _ ((fun '(t0,t1) => t0=s0 /\ t1=s1) ⋊ rem_lhs extract_loc Tex)).
          move=> Tex'.
          apply: rpre_hypothesis_rule => s2 s3 Hp.
          case: Hp => [[[/= -> ->] HT0] HT1].
          move: HT0 HT1. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=. move=> HT0 HT1.
          have Hnotin : extract_loc.1 \notin domm [fmap mid_loc;eval_tbl_loc]. { fmap_solve. }
          have HTT' : Tex = Tex'.
          { case: Hinv0 => [Hig _]. move: (Hig extract_loc Hnotin) => Heq. rewrite HT0 HT1 in Heq. exact: Heq. }
          subst Tex'.
          rewrite -HTT'.
          case HTss: (Tex ss) => [prk|] /=.
          -- eapply rpre_weaken_rule.
             1: instantiate (1 := fun '(t0,t1) => t0=s0 /\ t1=s1).
             2: { move=> t0 t1 [/= -> ->]. done. }
             apply: (KDF_hybE_bad_owner_dance i s0 s1 ss info prk Hinv0).
             ++ rewrite HT0. exact: HTss.
             ++ rewrite HSI0 Hidx. move/eqP: Hcmp => ->. done.
          -- eapply rpre_weaken_rule.
             1: instantiate (1 := fun '(t0,t1) => t0=s0 /\ t1=s1).
             2: { move=> t0 t1 [/= -> ->]. done. }
             apply: (r_uniform_bij _ _ _ _ id). 1: exists id; done.
             move=> prk.
             eapply (r_put_vs_put extract_loc (setm Tex ss prk) extract_loc (setm Tex ss prk) _ _
               (fun '(t0,t1) => t0=s0 /\ t1=s1)).
             set X := set_heap s0 extract_loc (setm Tex ss prk).
             set Y := set_heap s1 extract_loc (setm Tex ss prk).
             apply: rpre_hypothesis_rule => s2' s3' Hp.
             case: Hp => [s1'' [[s0'' [[-> ->] ->]] ->]].
             eapply rpre_weaken_rule.
             1: instantiate (1 := fun '(t0,t1) => t0=X /\ t1=Y).
             2: { move=> t0 t1 [/= -> ->]. done. }
             eapply (r_get_remember_lhs used_prk_loc _ _ (fun '(t0,t1) => t0=X /\ t1=Y)).
             move=> U.
             eapply (r_get_remember_rhs used_prk_loc _ _ ((fun '(t0,t1) => t0=X /\ t1=Y) ⋊ rem_lhs used_prk_loc U)).
             move=> U'.
             apply: rpre_hypothesis_rule => s4 s5 Hp2.
             case: Hp2 => [[[/= -> ->] HU0] HU1].
             move: HU0 HU1. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=. move=> HU0 HU1.
             have Hnotin2 : used_prk_loc.1 \notin domm [fmap mid_loc;eval_tbl_loc]. { fmap_solve. }
             have HUeq : get_heap s0 used_prk_loc = get_heap s1 used_prk_loc.
             { case: Hinv0 => [Hig _]. exact: (Hig used_prk_loc Hnotin2). }
             have HXU : get_heap X used_prk_loc = get_heap s0 used_prk_loc.
             { rewrite /X. rewrite (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != extract_loc.1)). done. }
             have HYU : get_heap Y used_prk_loc = get_heap s1 used_prk_loc.
             { rewrite /Y. rewrite (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != extract_loc.1)). done. }
             have HUU' : U = U'.
             { rewrite -HU0 -HU1 HXU HYU HUeq. done. }
             subst U'.
             rewrite -HUU'.
             case HUprk: (U prk) => [[]|] /=.
             ++ eapply rpre_weaken_rule.
                1: instantiate (1 := fun '(t0,t1) => t0=X /\ t1=Y).
                2: { move=> t0 t1 [/= -> ->]. done. }
                eapply (r_put_vs_put bad_loc true bad_loc true _ _ (fun '(t0,t1) => t0=X /\ t1=Y)).
                have Hinv2 : KDF_hybE_bad_inv i (set_heap X bad_loc true, set_heap Y bad_loc true).
                { rewrite /X /Y. exact: (KDF_hybE_bad_inv_extract_bad_step i s0 s1 ss Tex prk Hinv0 HT0 (esym HTT')). }
                have Heqi2 : getm (get_heap (set_heap X bad_loc true) ss_index_loc) ss = Some i.
                { rewrite (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != bad_loc.1)).
                  rewrite /X (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != extract_loc.1)).
                  rewrite HSI0 Hidx. move/eqP: Hcmp => ->. done. }
                eapply rpre_weaken_rule.
                1: instantiate (1 := fun '(t0,t1) => t0=set_heap X bad_loc true /\ t1=set_heap Y bad_loc true).
                ** apply: (KDF_hybE_bad_owner_dance i (set_heap X bad_loc true) (set_heap Y bad_loc true) ss info prk Hinv2 _ Heqi2).
                   rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != bad_loc.1)).
                   rewrite /X get_set_heap_eq setmE eq_refl. done.
                ** move=> t0 t1 [s1x [[s0x [[-> ->] ->]] ->]]. done.
             ++ eapply rpre_weaken_rule.
                1: instantiate (1 := fun '(t0,t1) => t0=X /\ t1=Y).
                2: { move=> t0 t1 [/= -> ->]. done. }
                eapply (r_put_vs_put used_prk_loc (setm U prk tt) used_prk_loc (setm U prk tt) _ _ (fun '(t0,t1) => t0=X /\ t1=Y)).
                have Hinv2 : KDF_hybE_bad_inv i (set_heap X used_prk_loc (setm U prk tt), set_heap Y used_prk_loc (setm U prk tt)).
                { rewrite /X /Y.
                  apply: (KDF_hybE_bad_inv_extract_fresh_step i s0 s1 ss Tex (get_heap s0 ss_index_loc) U prk
                    Hinv0 HT0 (esym HTT') erefl _ _ (_ : getm (get_heap s0 ss_index_loc) ss <> None) HTss HUprk).
                  - rewrite -HXU. exact: HU0.
                  - rewrite -HYU. exact: esym HUU'.
                  - rewrite HSI0 Hidx. done. }
                have Heqi2 : getm (get_heap (set_heap X used_prk_loc (setm U prk tt)) ss_index_loc) ss = Some i.
                { rewrite (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != used_prk_loc.1)).
                  rewrite /X (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != extract_loc.1)).
                  rewrite HSI0 Hidx. move/eqP: Hcmp => ->. done. }
                eapply rpre_weaken_rule.
                1: instantiate (1 := fun '(t0,t1) => t0=set_heap X used_prk_loc (setm U prk tt) /\ t1=set_heap Y used_prk_loc (setm U prk tt)).
                ** apply: (KDF_hybE_bad_owner_dance i (set_heap X used_prk_loc (setm U prk tt)) (set_heap Y used_prk_loc (setm U prk tt)) ss info prk Hinv2 _ Heqi2).
                   rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != used_prk_loc.1)).
                   rewrite /X get_set_heap_eq setmE eq_refl. done.
                ** move=> t0 t1 [s1x [[s0x [[-> ->] ->]] ->]]. done.
        * (* idx > i: trivial PRF leaf *)
          have Hlt2F : (idx < i.+1)%N = false.
          { rewrite ltnS leq_eqVlt Hcmp Hlt. done. }
          rewrite Hlt2F.
          apply: rpre_hypothesis_rule => s0 s1 Hp.
          case: Hp => [[Hinv0 HSI0] HSI1].
          move: HSI0 HSI1. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=. move=> HSI0 HSI1.
          eapply rpre_weaken_rule.
          1: instantiate (1 := fun '(t0,t1) => t0=s0 /\ t1=s1).
          2: { move=> t0 t1 [/= -> ->]. done. }
          rewrite /get_prk_bad.
          eapply (r_get_remember_lhs extract_loc _ _ (fun '(t0,t1) => t0=s0 /\ t1=s1)).
          move=> Tex.
          eapply (r_get_remember_rhs extract_loc _ _ ((fun '(t0,t1) => t0=s0 /\ t1=s1) ⋊ rem_lhs extract_loc Tex)).
          move=> Tex'.
          apply: rpre_hypothesis_rule => s2 s3 Hp.
          case: Hp => [[[/= -> ->] HT0] HT1].
          move: HT0 HT1. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=. move=> HT0 HT1.
          have Hnotin : extract_loc.1 \notin domm [fmap mid_loc;eval_tbl_loc]. { fmap_solve. }
          have HTT' : Tex = Tex'.
          { case: Hinv0 => [Hig _]. move: (Hig extract_loc Hnotin) => Heq. rewrite HT0 HT1 in Heq. exact: Heq. }
          subst Tex'.
          rewrite -HTT'.
          case HTss: (Tex ss) => [prk|] /=.
          -- apply: r_ret => t0 t1 [/= -> ->].
             split; [exact: Hinv0 | done].
          -- eapply rpre_weaken_rule.
             1: instantiate (1 := fun '(t0,t1) => t0=s0 /\ t1=s1).
             2: { move=> t0 t1 [/= -> ->]. done. }
             apply: (r_uniform_bij _ _ _ _ id). 1: exists id; done.
             move=> prk.
             eapply (r_put_vs_put extract_loc (setm Tex ss prk) extract_loc (setm Tex ss prk) _ _
               (fun '(t0,t1) => t0=s0 /\ t1=s1)).
             set X := set_heap s0 extract_loc (setm Tex ss prk).
             set Y := set_heap s1 extract_loc (setm Tex ss prk).
             apply: rpre_hypothesis_rule => s2' s3' Hp.
             case: Hp => [s1'' [[s0'' [[-> ->] ->]] ->]].
             eapply rpre_weaken_rule.
             1: instantiate (1 := fun '(t0,t1) => t0=X /\ t1=Y).
             2: { move=> t0 t1 [/= -> ->]. done. }
             eapply (r_get_remember_lhs used_prk_loc _ _ (fun '(t0,t1) => t0=X /\ t1=Y)).
             move=> U.
             eapply (r_get_remember_rhs used_prk_loc _ _ ((fun '(t0,t1) => t0=X /\ t1=Y) ⋊ rem_lhs used_prk_loc U)).
             move=> U'.
             apply: rpre_hypothesis_rule => s4 s5 Hp2.
             case: Hp2 => [[[/= -> ->] HU0] HU1].
             move: HU0 HU1. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=. move=> HU0 HU1.
             have Hnotin2 : used_prk_loc.1 \notin domm [fmap mid_loc;eval_tbl_loc]. { fmap_solve. }
             have HUeq : get_heap s0 used_prk_loc = get_heap s1 used_prk_loc.
             { case: Hinv0 => [Hig _]. exact: (Hig used_prk_loc Hnotin2). }
             have HXU : get_heap X used_prk_loc = get_heap s0 used_prk_loc.
             { rewrite /X. rewrite (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != extract_loc.1)). done. }
             have HYU : get_heap Y used_prk_loc = get_heap s1 used_prk_loc.
             { rewrite /Y. rewrite (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != extract_loc.1)). done. }
             have HUU' : U = U'.
             { rewrite -HU0 -HU1 HXU HYU HUeq. done. }
             subst U'.
             rewrite -HUU'.
             case HUprk: (U prk) => [[]|] /=.
             ++ eapply rpre_weaken_rule.
                1: instantiate (1 := fun '(t0,t1) => t0=X /\ t1=Y).
                2: { move=> t0 t1 [/= -> ->]. done. }
                eapply (r_put_vs_put bad_loc true bad_loc true _ _ (fun '(t0,t1) => t0=X /\ t1=Y)).
                apply: r_ret => t0 t1 [s1x [[s0x [[-> ->] ->]] ->]].
                split; [ | done].
                rewrite /X /Y. exact: (KDF_hybE_bad_inv_extract_bad_step i s0 s1 ss Tex prk Hinv0 HT0 (esym HTT')).
             ++ eapply rpre_weaken_rule.
                1: instantiate (1 := fun '(t0,t1) => t0=X /\ t1=Y).
                2: { move=> t0 t1 [/= -> ->]. done. }
                eapply (r_put_vs_put used_prk_loc (setm U prk tt) used_prk_loc (setm U prk tt) _ _ (fun '(t0,t1) => t0=X /\ t1=Y)).
                apply: r_ret => t0 t1 [s1x [[s0x [[-> ->] ->]] ->]].
                split; [ | done].
                rewrite /X /Y.
                apply: (KDF_hybE_bad_inv_extract_fresh_step i s0 s1 ss Tex (get_heap s0 ss_index_loc) U prk
                  Hinv0 HT0 (esym HTT') erefl _ _ (_ : getm (get_heap s0 ss_index_loc) ss <> None) HTss HUprk).
                ** rewrite -HXU. exact: HU0.
                ** rewrite -HYU. exact: esym HUU'.
                ** rewrite HSI0 Hidx. done.
    - (* SIdx ss = None: fresh index, mirrors the idx-based leaves above,
        via get_ss_idx's own index_step *)
      apply: r_get_vs_get_remember => cnt.
      apply: r_put_vs_put.
      apply: r_put_vs_put.
      apply: rpre_hypothesis_rule => s0 s1 Hp.
      case: Hp => [s1a [Hp1 Es1a]].
      case: Hp1 => [s0a [Hp2 Es0a]].
      case: Hp2 => [s1b [Hp3 Es1b]].
      case: Hp3 => [s0b [Hbase Es0b]].
      subst s0 s1 s0a s1a.
      case: Hbase => [[[[Hinv0 HSI0] HSI1] HC0] HC1].
      move: HSI0 HSI1 HC0 HC1.
      rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=.
      move=> HSI0 HSI1 HC0 HC1.
      have Hinv1 := KDF_hybE_bad_inv_index_step i s0b s1b SIdx cnt ss Hinv0 HSI0 HSI1 HC0 HC1 Hidx.
      set X := set_heap (set_heap s0b ss_count_loc cnt.+1) ss_index_loc (setm SIdx ss cnt).
      set Y := set_heap (set_heap s1b ss_count_loc cnt.+1) ss_index_loc (setm SIdx ss cnt).
      have HSInew : get_heap X ss_index_loc = setm SIdx ss cnt.
      {
      rewrite /X get_set_heap_eq.
      done.
      }
      eapply rpre_weaken_rule.
      1: instantiate (1 := fun '(t0,t1) => t0=X /\ t1=Y).
      2: { move=> t0 t1 [/= -> ->].
      done.
      }
      case Hlt2: (cnt < i)%N.
          + have Hlt2' : (cnt < i.+1)%N := ltn_trans Hlt2 (ltnSn i).
          rewrite Hlt2'.
          rewrite /get_prk_bad.
          eapply (r_get_remember_lhs extract_loc _ _ (fun '(t0,t1) => t0=X /\ t1=Y)).
          move=> Tex.
          eapply (r_get_remember_rhs extract_loc _ _ ((fun '(t0,t1) => t0=X /\ t1=Y) ⋊ rem_lhs extract_loc Tex)).
          move=> Tex'.
          apply: rpre_hypothesis_rule => s2 s3 Hp.
          case: Hp => [[[/= -> ->] HT0] HT1].
          move: HT0 HT1.
          rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=.
          move=> HT0 HT1.
          have Hnotin : extract_loc.1 \notin domm [fmap mid_loc;eval_tbl_loc].
          {
          fmap_solve.
          }
          have HTT' : Tex = Tex'.
          {
          case: Hinv1 => [Hig _].
          move: (Hig extract_loc Hnotin) => Heq.
          rewrite HT0 HT1 in Heq.
          exact: Heq.
          }
          subst Tex'.
          rewrite -HTT'.
          case HTss: (Tex ss) => [prk|] /=.
            * eapply rpre_weaken_rule.
            1: instantiate (1 := fun '(t0,t1) => t0=X /\ t1=Y).
            2: { move=> t0 t1 [/= -> ->].
            done.
            }
            apply: (KDF_hybE_bad_mid_dance i X Y ss info prk Hinv1).
              -- rewrite HT0.
              exact: HTss.
              -- rewrite HSInew setmE eq_refl.
              move=> [Heqi].
              move: Hlt2.
              rewrite Heqi ltnn.
              done.
            * eapply rpre_weaken_rule.
            1: instantiate (1 := fun '(t0,t1) => t0=X /\ t1=Y).
            2: { move=> t0 t1 [/= -> ->].
            done.
            }
            apply: (r_uniform_bij _ _ _ _ id).
            1: exists id; done.
            move=> prk.
            eapply (r_put_vs_put extract_loc (setm Tex ss prk) extract_loc (setm Tex ss prk) _ _
  (fun '(t0,t1) => t0=X /\ t1=Y)).
            set X2 := set_heap X extract_loc (setm Tex ss prk).
            set Y2 := set_heap Y extract_loc (setm Tex ss prk).
            apply: rpre_hypothesis_rule => s2' s3' Hp.
            case: Hp => [s1'' [[s0'' [[-> ->] ->]] ->]].
            eapply rpre_weaken_rule.
            1: instantiate (1 := fun '(t0,t1) => t0=X2 /\ t1=Y2).
            2: { move=> t0 t1 [/= -> ->].
            done.
            }
            eapply (r_get_remember_lhs used_prk_loc _ _ (fun '(t0,t1) => t0=X2 /\ t1=Y2)).
            move=> U.
            eapply (r_get_remember_rhs used_prk_loc _ _ ((fun '(t0,t1) => t0=X2 /\ t1=Y2) ⋊ rem_lhs used_prk_loc U)).
            move=> U'.
            apply: rpre_hypothesis_rule => s4 s5 Hp2.
            case: Hp2 => [[[/= -> ->] HU0] HU1].
            move: HU0 HU1.
            rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=.
            move=> HU0 HU1.
            have Hnotin2 : used_prk_loc.1 \notin domm [fmap mid_loc;eval_tbl_loc].
            {
            fmap_solve.
            }
            have HUeq : get_heap X used_prk_loc = get_heap Y used_prk_loc.
            {
            case: Hinv1 => [Hig _].
            exact: (Hig used_prk_loc Hnotin2).
            }
            have HXU : get_heap X2 used_prk_loc = get_heap X used_prk_loc.
            {
            rewrite /X2.
            rewrite (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != extract_loc.1)).
            done.
            }
            have HYU : get_heap Y2 used_prk_loc = get_heap Y used_prk_loc.
            {
            rewrite /Y2.
            rewrite (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != extract_loc.1)).
            done.
            }
            have HUU' : U = U'.
            {
            rewrite -HU0 -HU1 HXU HYU HUeq.
            done.
            }
            subst U'.
            rewrite -HUU'.
            case HUprk: (U prk) => [[]|] /=.
              -- eapply rpre_weaken_rule.
              1: instantiate (1 := fun '(t0,t1) => t0=X2 /\ t1=Y2).
              2: { move=> t0 t1 [/= -> ->].
              done.
              }
              eapply (r_put_vs_put bad_loc true bad_loc true _ _ (fun '(t0,t1) => t0=X2 /\ t1=Y2)).
              have Hinv2 : KDF_hybE_bad_inv i (set_heap X2 bad_loc true, set_heap Y2 bad_loc true).
              {
              rewrite /X2 /Y2.
              exact: (KDF_hybE_bad_inv_extract_bad_step i X Y ss Tex prk Hinv1 HT0 (esym HTT')).
              }
              have Hne2 : getm (get_heap (set_heap X2 bad_loc true) ss_index_loc) ss <> Some i.
              {
              rewrite (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != bad_loc.1)).
              rewrite /X2 (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != extract_loc.1)).
              rewrite HSInew setmE eq_refl.
              move=> [Heqi].
              move: Hlt2.
              rewrite Heqi ltnn.
              done.
              }
              eapply rpre_weaken_rule.
              1: instantiate (1 := fun '(t0,t1) => t0=set_heap X2 bad_loc true /\ t1=set_heap Y2 bad_loc true).
                ++ apply: (KDF_hybE_bad_mid_dance i (set_heap X2 bad_loc true) (set_heap Y2 bad_loc true) ss info prk Hinv2 _ Hne2).
                rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != bad_loc.1)).
                rewrite /X2 get_set_heap_eq setmE eq_refl.
                done.
                ++ move=> t0 t1 [s1x [[s0x [[-> ->] ->]] ->]].
                done.
              -- eapply rpre_weaken_rule.
              1: instantiate (1 := fun '(t0,t1) => t0=X2 /\ t1=Y2).
              2: { move=> t0 t1 [/= -> ->].
              done.
              }
              eapply (r_put_vs_put used_prk_loc (setm U prk tt) used_prk_loc (setm U prk tt) _ _ (fun '(t0,t1) => t0=X2 /\ t1=Y2)).
              have Hinv2 : KDF_hybE_bad_inv i (set_heap X2 used_prk_loc (setm U prk tt), set_heap Y2 used_prk_loc (setm U prk tt)).
              {
              rewrite /X2 /Y2.
              apply: (KDF_hybE_bad_inv_extract_fresh_step i X Y ss Tex (get_heap X ss_index_loc) U prk
    Hinv1 HT0 (esym HTT') erefl _ _ (_ : getm (get_heap X ss_index_loc) ss <> None) HTss HUprk).
        - rewrite -HXU.
        exact: HU0.
        - rewrite -HYU.
        exact: esym HUU'.
        - rewrite HSInew setmE eq_refl.
        done.
        }
        have Hne2 : getm (get_heap (set_heap X2 used_prk_loc (setm U prk tt)) ss_index_loc) ss <> Some i.
        {
        rewrite (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != used_prk_loc.1)).
        rewrite /X2 (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != extract_loc.1)).
        rewrite HSInew setmE eq_refl.
        move=> [Heqi].
        move: Hlt2.
        rewrite Heqi ltnn.
        done.
        }
        eapply rpre_weaken_rule.
        1: instantiate (1 := fun '(t0,t1) => t0=set_heap X2 used_prk_loc (setm U prk tt) /\ t1=set_heap Y2 used_prk_loc (setm U prk tt)).
                ++ apply: (KDF_hybE_bad_mid_dance i (set_heap X2 used_prk_loc (setm U prk tt)) (set_heap Y2 used_prk_loc (setm U prk tt)) ss info prk Hinv2 _ Hne2).
                rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != used_prk_loc.1)).
                rewrite /X2 get_set_heap_eq setmE eq_refl.
                done.
                ++ move=> t0 t1 [s1x [[s0x [[-> ->] ->]] ->]].
                done.
          + case Hcmp2: (cnt == i).
            * have Hlt2T : (cnt < i.+1)%N.
            {
            move/eqP: Hcmp2 => ->.
            exact: ltnSn i.
            }
            rewrite Hlt2T.
            rewrite /get_prk_bad.
            eapply (r_get_remember_lhs extract_loc _ _ (fun '(t0,t1) => t0=X /\ t1=Y)).
            move=> Tex.
            eapply (r_get_remember_rhs extract_loc _ _ ((fun '(t0,t1) => t0=X /\ t1=Y) ⋊ rem_lhs extract_loc Tex)).
            move=> Tex'.
            apply: rpre_hypothesis_rule => s2 s3 Hp.
            case: Hp => [[[/= -> ->] HT0] HT1].
            move: HT0 HT1.
            rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=.
            move=> HT0 HT1.
            have Hnotin : extract_loc.1 \notin domm [fmap mid_loc;eval_tbl_loc].
            {
            fmap_solve.
            }
            have HTT' : Tex = Tex'.
            {
            case: Hinv1 => [Hig _].
            move: (Hig extract_loc Hnotin) => Heq.
            rewrite HT0 HT1 in Heq.
            exact: Heq.
            }
            subst Tex'.
            rewrite -HTT'.
            case HTss: (Tex ss) => [prk|] /=.
              -- eapply rpre_weaken_rule.
              1: instantiate (1 := fun '(t0,t1) => t0=X /\ t1=Y).
              2: { move=> t0 t1 [/= -> ->].
              done.
              }
              apply: (KDF_hybE_bad_owner_dance i X Y ss info prk Hinv1).
                ++ rewrite HT0.
                exact: HTss.
                ++ rewrite HSInew setmE eq_refl.
                move/eqP: Hcmp2 => ->.
                done.
              -- eapply rpre_weaken_rule.
              1: instantiate (1 := fun '(t0,t1) => t0=X /\ t1=Y).
              2: { move=> t0 t1 [/= -> ->].
              done.
              }
              apply: (r_uniform_bij _ _ _ _ id).
              1: exists id; done.
              move=> prk.
              eapply (r_put_vs_put extract_loc (setm Tex ss prk) extract_loc (setm Tex ss prk) _ _
  (fun '(t0,t1) => t0=X /\ t1=Y)).
              set X2 := set_heap X extract_loc (setm Tex ss prk).
              set Y2 := set_heap Y extract_loc (setm Tex ss prk).
              apply: rpre_hypothesis_rule => s2' s3' Hp.
              case: Hp => [s1'' [[s0'' [[-> ->] ->]] ->]].
              eapply rpre_weaken_rule.
              1: instantiate (1 := fun '(t0,t1) => t0=X2 /\ t1=Y2).
              2: { move=> t0 t1 [/= -> ->].
              done.
              }
              eapply (r_get_remember_lhs used_prk_loc _ _ (fun '(t0,t1) => t0=X2 /\ t1=Y2)).
              move=> U.
              eapply (r_get_remember_rhs used_prk_loc _ _ ((fun '(t0,t1) => t0=X2 /\ t1=Y2) ⋊ rem_lhs used_prk_loc U)).
              move=> U'.
              apply: rpre_hypothesis_rule => s4 s5 Hp2.
              case: Hp2 => [[[/= -> ->] HU0] HU1].
              move: HU0 HU1.
              rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=.
              move=> HU0 HU1.
              have Hnotin2 : used_prk_loc.1 \notin domm [fmap mid_loc;eval_tbl_loc].
              {
              fmap_solve.
              }
              have HUeq : get_heap X used_prk_loc = get_heap Y used_prk_loc.
              {
              case: Hinv1 => [Hig _].
              exact: (Hig used_prk_loc Hnotin2).
              }
              have HXU : get_heap X2 used_prk_loc = get_heap X used_prk_loc.
              {
              rewrite /X2.
              rewrite (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != extract_loc.1)).
              done.
              }
              have HYU : get_heap Y2 used_prk_loc = get_heap Y used_prk_loc.
              {
              rewrite /Y2.
              rewrite (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != extract_loc.1)).
              done.
              }
              have HUU' : U = U'.
              {
              rewrite -HU0 -HU1 HXU HYU HUeq.
              done.
              }
              subst U'.
              rewrite -HUU'.
              case HUprk: (U prk) => [[]|] /=.
                ++ eapply rpre_weaken_rule.
                1: instantiate (1 := fun '(t0,t1) => t0=X2 /\ t1=Y2).
                2: { move=> t0 t1 [/= -> ->].
                done.
                }
                eapply (r_put_vs_put bad_loc true bad_loc true _ _ (fun '(t0,t1) => t0=X2 /\ t1=Y2)).
                have Hinv2 : KDF_hybE_bad_inv i (set_heap X2 bad_loc true, set_heap Y2 bad_loc true).
                {
                rewrite /X2 /Y2.
                exact: (KDF_hybE_bad_inv_extract_bad_step i X Y ss Tex prk Hinv1 HT0 (esym HTT')).
                }
                have Heqi2 : getm (get_heap (set_heap X2 bad_loc true) ss_index_loc) ss = Some i.
                {
                rewrite (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != bad_loc.1)).
                rewrite /X2 (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != extract_loc.1)).
                rewrite HSInew setmE eq_refl.
                move/eqP: Hcmp2 => ->.
                done.
                }
                eapply rpre_weaken_rule.
                1: instantiate (1 := fun '(t0,t1) => t0=set_heap X2 bad_loc true /\ t1=set_heap Y2 bad_loc true).
                  ** apply: (KDF_hybE_bad_owner_dance i (set_heap X2 bad_loc true) (set_heap Y2 bad_loc true) ss info prk Hinv2 _ Heqi2).
                  rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != bad_loc.1)).
                  rewrite /X2 get_set_heap_eq setmE eq_refl.
                  done.
                  ** move=> t0 t1 [s1x [[s0x [[-> ->] ->]] ->]].
                  done.
                ++ eapply rpre_weaken_rule.
                1: instantiate (1 := fun '(t0,t1) => t0=X2 /\ t1=Y2).
                2: { move=> t0 t1 [/= -> ->].
                done.
                }
                eapply (r_put_vs_put used_prk_loc (setm U prk tt) used_prk_loc (setm U prk tt) _ _ (fun '(t0,t1) => t0=X2 /\ t1=Y2)).
                have Hinv2 : KDF_hybE_bad_inv i (set_heap X2 used_prk_loc (setm U prk tt), set_heap Y2 used_prk_loc (setm U prk tt)).
                {
                rewrite /X2 /Y2.
                apply: (KDF_hybE_bad_inv_extract_fresh_step i X Y ss Tex (get_heap X ss_index_loc) U prk
    Hinv1 HT0 (esym HTT') erefl _ _ (_ : getm (get_heap X ss_index_loc) ss <> None) HTss HUprk).
        - rewrite -HXU.
        exact: HU0.
        - rewrite -HYU.
        exact: esym HUU'.
        - rewrite HSInew setmE eq_refl.
        done.
        }
        have Heqi2 : getm (get_heap (set_heap X2 used_prk_loc (setm U prk tt)) ss_index_loc) ss = Some i.
        {
        rewrite (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != used_prk_loc.1)).
        rewrite /X2 (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != extract_loc.1)).
        rewrite HSInew setmE eq_refl.
        move/eqP: Hcmp2 => ->.
        done.
        }
        eapply rpre_weaken_rule.
        1: instantiate (1 := fun '(t0,t1) => t0=set_heap X2 used_prk_loc (setm U prk tt) /\ t1=set_heap Y2 used_prk_loc (setm U prk tt)).
                  ** apply: (KDF_hybE_bad_owner_dance i (set_heap X2 used_prk_loc (setm U prk tt)) (set_heap Y2 used_prk_loc (setm U prk tt)) ss info prk Hinv2 _ Heqi2).
                  rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != used_prk_loc.1)).
                  rewrite /X2 get_set_heap_eq setmE eq_refl.
                  done.
                  ** move=> t0 t1 [s1x [[s0x [[-> ->] ->]] ->]].
                  done.
            * have Hlt2F : (cnt < i.+1)%N = false.
            {
            rewrite ltnS leq_eqVlt Hcmp2 Hlt2.
            done.
            }
            rewrite Hlt2F.
            rewrite /get_prk_bad.
            eapply (r_get_remember_lhs extract_loc _ _ (fun '(t0,t1) => t0=X /\ t1=Y)).
            move=> Tex.
            eapply (r_get_remember_rhs extract_loc _ _ ((fun '(t0,t1) => t0=X /\ t1=Y) ⋊ rem_lhs extract_loc Tex)).
            move=> Tex'.
            apply: rpre_hypothesis_rule => s2 s3 Hp.
            case: Hp => [[[/= -> ->] HT0] HT1].
            move: HT0 HT1.
            rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=.
            move=> HT0 HT1.
            have Hnotin : extract_loc.1 \notin domm [fmap mid_loc;eval_tbl_loc].
            {
            fmap_solve.
            }
            have HTT' : Tex = Tex'.
            {
            case: Hinv1 => [Hig _].
            move: (Hig extract_loc Hnotin) => Heq.
            rewrite HT0 HT1 in Heq.
            exact: Heq.
            }
            subst Tex'.
            rewrite -HTT'.
            case HTss: (Tex ss) => [prk|] /=.
              -- apply: r_ret => t0 t1 [/= -> ->].
              split; [exact: Hinv1 | done].
              -- eapply rpre_weaken_rule.
              1: instantiate (1 := fun '(t0,t1) => t0=X /\ t1=Y).
              2: { move=> t0 t1 [/= -> ->].
              done.
              }
              apply: (r_uniform_bij _ _ _ _ id).
              1: exists id; done.
              move=> prk.
              eapply (r_put_vs_put extract_loc (setm Tex ss prk) extract_loc (setm Tex ss prk) _ _
  (fun '(t0,t1) => t0=X /\ t1=Y)).
              set X2 := set_heap X extract_loc (setm Tex ss prk).
              set Y2 := set_heap Y extract_loc (setm Tex ss prk).
              apply: rpre_hypothesis_rule => s2' s3' Hp.
              case: Hp => [s1'' [[s0'' [[-> ->] ->]] ->]].
              eapply rpre_weaken_rule.
              1: instantiate (1 := fun '(t0,t1) => t0=X2 /\ t1=Y2).
              2: { move=> t0 t1 [/= -> ->].
              done.
              }
              eapply (r_get_remember_lhs used_prk_loc _ _ (fun '(t0,t1) => t0=X2 /\ t1=Y2)).
              move=> U.
              eapply (r_get_remember_rhs used_prk_loc _ _ ((fun '(t0,t1) => t0=X2 /\ t1=Y2) ⋊ rem_lhs used_prk_loc U)).
              move=> U'.
              apply: rpre_hypothesis_rule => s4 s5 Hp2.
              case: Hp2 => [[[/= -> ->] HU0] HU1].
              move: HU0 HU1.
              rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=.
              move=> HU0 HU1.
              have Hnotin2 : used_prk_loc.1 \notin domm [fmap mid_loc;eval_tbl_loc].
              {
              fmap_solve.
              }
              have HUeq : get_heap X used_prk_loc = get_heap Y used_prk_loc.
              {
              case: Hinv1 => [Hig _].
              exact: (Hig used_prk_loc Hnotin2).
              }
              have HXU : get_heap X2 used_prk_loc = get_heap X used_prk_loc.
              {
              rewrite /X2.
              rewrite (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != extract_loc.1)).
              done.
              }
              have HYU : get_heap Y2 used_prk_loc = get_heap Y used_prk_loc.
              {
              rewrite /Y2.
              rewrite (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != extract_loc.1)).
              done.
              }
              have HUU' : U = U'.
              {
              rewrite -HU0 -HU1 HXU HYU HUeq.
              done.
              }
              subst U'.
              rewrite -HUU'.
              case HUprk: (U prk) => [[]|] /=.
                ++ eapply rpre_weaken_rule.
                1: instantiate (1 := fun '(t0,t1) => t0=X2 /\ t1=Y2).
                2: { move=> t0 t1 [/= -> ->].
                done.
                }
                eapply (r_put_vs_put bad_loc true bad_loc true _ _ (fun '(t0,t1) => t0=X2 /\ t1=Y2)).
                apply: r_ret => t0 t1 [s1x [[s0x [[-> ->] ->]] ->]].
                split; [ | done].
                rewrite /X2 /Y2.
                exact: (KDF_hybE_bad_inv_extract_bad_step i X Y ss Tex prk Hinv1 HT0 (esym HTT')).
                ++ eapply rpre_weaken_rule.
                1: instantiate (1 := fun '(t0,t1) => t0=X2 /\ t1=Y2).
                2: { move=> t0 t1 [/= -> ->].
                done.
                }
                eapply (r_put_vs_put used_prk_loc (setm U prk tt) used_prk_loc (setm U prk tt) _ _ (fun '(t0,t1) => t0=X2 /\ t1=Y2)).
                apply: r_ret => t0 t1 [s1x [[s0x [[-> ->] ->]] ->]].
                split; [ | done].
                rewrite /X2 /Y2.
                apply: (KDF_hybE_bad_inv_extract_fresh_step i X Y ss Tex (get_heap X ss_index_loc) U prk
     Hinv1 HT0 (esym HTT') erefl _ _ (_ : getm (get_heap X ss_index_loc) ss <> None) HTss HUprk).
                  ** rewrite -HXU.
                  exact: HU0.
                  ** rewrite -HYU.
                  exact: esym HUU'.
                  ** rewrite HSInew setmE eq_refl.
                  done.
  Qed.

  (* --- per-hop Fundamental Lemma, mirror of [KDF_mid'_KDF_bad_bound] --- *)
  Lemma KDF_hybE_bad_KDF_hyb_bad_bound i LA A :
    ValidPackage LA DERIVE_export A_export A →
    fseparate LA KDF_hybE_bad_locs →
    fseparate LA KDF_hyb_bad_locs →
    lossless_valid_adv LA DERIVE_export (resolve A RUN tt) →
    AdvantageE (KDF_hybE_bad i) (KDF_hyb_bad i.+1) A
      <= Pr_bad (A ∘ KDF_hybE_bad i) 4 true.
  Proof.
    intros vA Hsep0 Hsep1 Hlva.
    eapply eq_upto_bad_perf_ind.
    1: exact _.
    1: exact _.
    1: exact vA.
    1: eapply (INV'_to_INV LA KDF_hybE_bad_locs KDF_hyb_bad_locs (KDF_hybE_bad_inv i)).
    1: exact: (inv_INV' (Invariant:=KDF_hybE_bad_Invariant i)).
    1: exact Hsep0.
    1: exact Hsep1.
    1: exact: (inv_empty (Invariant:=KDF_hybE_bad_Invariant i)).
    1: exact Hsep0.
    1: exact Hsep1.
    1: exact Hlva.
    1: eapply (notin_has_separate KDF_hybE_bad_locs LA bad_loc); [ fmap_solve | apply: fseparateC; exact Hsep0 ].
    1: move=> s0 s1 Hpre; apply: (proj1 Hpre); fmap_solve.
    1: exact: KDF_hybE_bad_eq_up_to_bad.
    1: exact: KDF_hybE_bad_bad_preserved.
    1: exact: KDF_hyb_bad_bad_preserved.
  Qed.

  (* --- the WEAKENED replacement for the old (false) false_equiv --- *)
  Lemma KDF_hyb_EVAL_false_bound i LA A :
    ValidPackage LA DERIVE_export A_export A →
    fseparate LA KDF_hyb_locs →
    fseparate LA [fmap eval_tbl_loc] →
    fseparate LA KDF_hybE_bad_locs →
    fseparate LA KDF_hyb_bad_locs →
    lossless_valid_adv LA DERIVE_export (resolve A RUN tt) →
    AdvantageE (KDF_hyb_EVAL i ∘ EVAL false) (KDF_hyb i.+1) A
      <= Pr_bad (A ∘ KDF_hybE_bad i) 4 true.
  Proof.
    intros vA d1 d2 d3 d4 Hlva.
    ssprove triangle (KDF_hyb_EVAL i ∘ EVAL false) [::
      pack (KDF_hybE_bad i) ;
      pack (KDF_hyb_bad i.+1)
    ] (KDF_hyb i.+1) A as ineq.
    apply: le_trans. 1: by apply: ineq.
    have e1 : AdvantageE (KDF_hyb_EVAL i ∘ EVAL false) (KDF_hybE_bad i) A = 0.
    { apply: KDF_hybE_bad_equiv.
      - apply: fseparateUr; [exact d1 | exact d2].
      - exact d3. }
    have e3 : AdvantageE (KDF_hyb_bad i.+1) (KDF_hyb i.+1) A = 0.
    { apply: KDF_hyb_bad_KDF_hyb_equiv.
      - exact d4.
      - exact d1. }
    rewrite e1 e3 GRing.add0r GRing.addr0.
    exact: (KDF_hybE_bad_KDF_hyb_bad_bound i LA A vA d3 d4 Hlva).
  Qed.

  (** Assembles [KDF_hyb_KDF_hyb_EVAL_true_equiv]/[KDF_hyb_EVAL_false_bound]
    into the COUNT-free hybrid bound, by the exact same [elim: q] /
    4-way-triangle argument as [PRFPRG.v]'s [hyb_security_based_on_prf],
    except the EVAL-false leg is now only an up-to-bad BOUND (not an
    equality), so the resulting bound picks up a second sum of per-hop
    [Pr_bad] terms on top of the [prf_epsilon] hybrid sum. *)
  Lemma COUNT_link_valid LA A q :
    ValidPackage LA DERIVE_export A_export A →
    fseparate LA [fmap count_loc] →
    ValidPackage (unionm LA [fmap count_loc]) DERIVE_export A_export (A ∘ COUNT q).
  Proof.
    intros vA hsep.
    eapply valid_link.
    - exact vA.
    - ssprove_valid.
    - exact: (fseparate_compat _ _ hsep).
  Qed.

  (** [COUNT q]'s redesign (see its docstring above) made it lossless
    UNCONDITIONALLY -- for every value of [count_loc] alike, reachable or
    not -- which is exactly what is needed to push [lossless_valid_adv]
    (pkg_upto_bad.v) through [code_link] with [COUNT q] spliced in: no
    reachability/invariant tracking on [count_loc]'s value is needed at
    all, unlike the [#assert]-based design this replaces (see the
    superseded docstring on [KDF_mid_KDF_ideal_bound] below for why THAT
    design was structurally incompatible with [lossless_valid_adv]).

    This is the composition lemma [pkg_upto_bad.v] itself doesn't provide
    (confirmed by grep: [lossless_valid_adv] has no existing [code_link]
    compatibility lemma anywhere in the codebase) -- built locally here,
    by structural induction on the adversary code [Ac]'s own
    [lossless_valid_adv] derivation, mirroring [bad_preserved_link]'s
    shape (pkg_upto_bad.v) but for plain losslessness instead of
    "bad-preserving" losslessness: at every [getr]/[putr] node of [Ac]'s
    own local state, [fhas_union_l] lifts membership in [LA] to
    [unionm LA [fmap count_loc]]; at every [opr] node (a call into
    [DERIVE_export]), [code_link] splices in [COUNT q]'s own handler body
    (via [resolve_link]/[code_link]'s own [opr] equation, exposed by
    [fmap_invert]/[simplify_linking] the same way [simplify_eq_rel] does
    for a game's own oracle body), which is unconditionally lossless: its
    [get count_loc] is in [[fmap count_loc]] (lifted via [fhas_union_r],
    using [fseparate LA [fmap count_loc]] to get [count_loc] fresh for
    [LA]), and BOTH the "count < q" branch (which re-issues the very same
    call into [DERIVE_export], continuing with [Ac]'s own continuation
    [k] -- exactly the recursive [IH]) and the "count >= q" branch
    (independent uniform sample, then likewise continuing with [k] on the
    sampled dummy value -- again exactly [IH]) come back to [IH].

    NOTE: this lemma was relocated here (from just above the OLD
    [COUNT_KDF_mid'_KDF_bad_bound]) so that [COUNT_KDF_hyb_bound] --
    which now also needs to push [lossless_valid_adv] through
    [A ∘ COUNT q] for the per-hop [Pr_bad] sum -- can use it; it has no
    dependency on anything [KDF_mid'/KDF_bad]-specific, so moving it
    earlier is purely a reordering, not a mathematical change. *)
  Lemma lossless_valid_adv_COUNT_link {LA B} (Ac : raw_code B) (q : nat) :
    fseparate LA [fmap count_loc] →
    lossless_valid_adv LA DERIVE_export Ac →
    lossless_valid_adv (unionm LA [fmap count_loc]) DERIVE_export
      (code_link Ac (COUNT q)).
  Proof.
    move=> Hsep Hlva.
    have Hnotin : count_loc.1 \notin domm LA.
    { apply: (notin_has_separate [fmap count_loc] LA count_loc).
      - fmap_solve.
      - apply: fseparateC. exact: Hsep. }
    induction Hlva as [x0 | o x k Ho k' IH | l k Hl k' IH | l v k Hl IH | op k Hop k' IH].
    - exact: lva_ret.
    - rewrite /=.
      fmap_invert Ho.
      simplify_linking.
      case: x => ss info /=.
      apply: lva_getr; [ apply: fhas_union_r; [exact: Hnotin | fmap_solve] | move=> count ].
      case: ifP => Hcount /=.
      + apply: lva_putr; [ apply: fhas_union_r; [exact: Hnotin | fmap_solve] | ].
        apply: lva_opr; [ fmap_solve | move=> y; exact: IH ].
      + apply: lva_sampler => y. exact: IH.
    - rewrite /=.
      have Hl2 : fhas (unionm LA [fmap count_loc]) l.
      { rewrite (surjective_pairing l). apply: fhas_union_l.
        rewrite -(surjective_pairing l). exact: Hl. }
      apply: lva_getr; [ exact: Hl2 | move=> v; exact: IH ].
    - rewrite /=.
      have Hl2 : fhas (unionm LA [fmap count_loc]) l.
      { rewrite (surjective_pairing l). apply: fhas_union_l.
        rewrite -(surjective_pairing l). exact: Hl. }
      apply: lva_putr; [ exact: Hl2 | exact: IHIH ].
    - rewrite /=.
      apply: lva_sampler => v. exact: IH.
  Qed.

  Lemma KDF_hyb_bound LA A q :
    ValidPackage LA DERIVE_export A_export A →
    fseparate LA KDF_hyb_locs →
    fseparate LA [fmap eval_key_loc] →
    fseparate LA [fmap eval_tbl_loc] →
    fseparate LA KDF_hybE_bad_locs →
    fseparate LA KDF_hyb_bad_locs →
    lossless_valid_adv LA DERIVE_export (resolve A RUN tt) →
    AdvantageE (KDF_hyb 0) (KDF_hyb q) A <=
      \sum_(i < q) prf_epsilon (A ∘ KDF_hyb_EVAL i)
      + \sum_(i < q) Pr_bad (A ∘ KDF_hybE_bad i) 4 true.
  Proof.
    move=> vA d1 d2 d3 d4 d5 Hlva.
    elim: q => [|q IHq].
    1: by rewrite 2!big_ord0 GRing.addr0 /AdvantageE GRing.subrr normr0.
    ssprove triangle (KDF_hyb 0) [::
      pack (KDF_hyb q) ;
      KDF_hyb_EVAL q ∘ EVAL true ;
      KDF_hyb_EVAL q ∘ EVAL false
    ] (KDF_hyb q.+1) A
    as ineq.
    apply: le_trans.
    1: by apply: ineq.
    rewrite -> KDF_hyb_KDF_hyb_EVAL_true_equiv by ssprove_valid.
    rewrite GRing.addr0.
    have hterm3 : AdvantageE (KDF_hyb_EVAL q ∘ EVAL true) (KDF_hyb_EVAL q ∘ EVAL false) A
        = prf_epsilon (A ∘ KDF_hyb_EVAL q).
    { by rewrite /prf_epsilon Advantage_E Advantage_link Advantage_sym. }
    rewrite hterm3.
    have hterm4 : AdvantageE (KDF_hyb_EVAL q ∘ EVAL false) (KDF_hyb q.+1) A
        <= Pr_bad (A ∘ KDF_hybE_bad q) 4 true.
    { exact: (KDF_hyb_EVAL_false_bound q LA A vA d1 d3 d4 d5 Hlva). }
    rewrite 2!big_ord_recr.
    rewrite -GRing.addrA.
    apply: le_trans.
    1: apply: lerD; [exact: IHq | apply: lerD; [exact: lexx | exact: hterm4]].
    rewrite GRing.addrACA.
    exact: lexx.
  Qed.

  (* [KDF_hyb_bound] pushed through [Advantage_link] at [P := COUNT q],
    exactly as [COUNT_KDF_mid_KDF_mid'_bound] et al. push the *equality*
    facts below through the same associativity lemma -- here the
    resulting composed adversary [A ∘ COUNT q] is exactly what
    [KDF_hyb_bound]'s own [prf_epsilon (A ∘ KDF_hyb_EVAL i)]/[Pr_bad (A ∘
    KDF_hybE_bad i) 4 true] want, yielding the same terms composed with
    [COUNT q] on the nose. *)
  Lemma COUNT_KDF_hyb_bound LA A q :
    ValidPackage LA DERIVE_export A_export A →
    fseparate LA KDF_hyb_locs →
    fseparate LA [fmap eval_key_loc] →
    fseparate LA [fmap eval_tbl_loc] →
    fseparate LA KDF_hybE_bad_locs →
    fseparate LA KDF_hyb_bad_locs →
    fseparate LA [fmap count_loc] →
    lossless_valid_adv LA DERIVE_export (resolve A RUN tt) →
    AdvantageE (COUNT q ∘ KDF_hyb 0) (COUNT q ∘ KDF_hyb q) A <=
      \sum_(i < q) prf_epsilon ((A ∘ COUNT q) ∘ KDF_hyb_EVAL i)
      + \sum_(i < q) Pr_bad ((A ∘ COUNT q) ∘ KDF_hybE_bad i) 4 true.
  Proof.
    intros vA d1 d2 d3 d4 d5 d6 Hlva.
    have vAC := COUNT_link_valid LA A q vA d6.
    have d1' : fseparate (unionm LA [fmap count_loc]) KDF_hyb_locs.
    { apply: fseparateUl; [exact d1 | apply: fseparateC; fmap_solve]. }
    have d2' : fseparate (unionm LA [fmap count_loc]) [fmap eval_key_loc].
    { apply: fseparateUl; [exact d2 | apply: fseparateC; fmap_solve]. }
    have d3' : fseparate (unionm LA [fmap count_loc]) [fmap eval_tbl_loc].
    { apply: fseparateUl; [exact d3 | apply: fseparateC; fmap_solve]. }
    have d4' : fseparate (unionm LA [fmap count_loc]) KDF_hybE_bad_locs.
    { apply: fseparateUl; [exact d4 | apply: fseparateC; fmap_solve]. }
    have d5' : fseparate (unionm LA [fmap count_loc]) KDF_hyb_bad_locs.
    { apply: fseparateUl; [exact d5 | apply: fseparateC; fmap_solve]. }
    have Hlva' : lossless_valid_adv (unionm LA [fmap count_loc]) DERIVE_export
        (resolve (A ∘ COUNT q) RUN tt).
    { rewrite resolve_link. apply: lossless_valid_adv_COUNT_link; [exact d6 | exact Hlva]. }
    rewrite -(Advantage_link (KDF_hyb 0) (KDF_hyb q) A (COUNT q)).
    exact: (KDF_hyb_bound _ _ q vAC d1' d2' d3' d4' d5' Hlva').
  Qed.

  Lemma COUNT_KDF_real_KDF_hyb0_bound LA A q :
    ValidPackage LA DERIVE_export A_export A →
    fseparate LA KDF_real_locs →
    fseparate LA KDF_hyb_locs →
    fseparate LA [fmap count_loc] →
    AdvantageE (COUNT q ∘ KDF_real) (COUNT q ∘ KDF_hyb 0) A = 0.
  Proof.
    intros vA d1 d2 d3.
    have vAC := COUNT_link_valid LA A q vA d3.
    rewrite -(Advantage_link KDF_real (KDF_hyb 0) A (COUNT q)).
    apply: KDF_real_KDF_hyb0_equiv.
    - apply: fseparateUl; [exact d1 | apply: fseparateC; fmap_solve].
    - apply: fseparateUl; [exact d2 | apply: fseparateC; fmap_solve].
  Qed.

  (** Step 1's LAST piece: past the [q]-th distinct shared secret,
    [KDF_hyb q] and [KDF_mid] agree exactly, no probability reasoning
    needed -- [KDF_hyb q]'s "idx < q" branch is [KDF_mid]'s own
    unconditional [mid_loc] logic verbatim, and [COUNT q] itself
    materialises "the adversary has made at most [q] REAL queries" as a
    HEAP FACT ([count_loc]), not merely as a property of the whole run:
    on the LHS heap of [COUNT q ∘ KDF_hyb q], [ss_count_loc] (the number
    of distinct [ss]'s [get_ss_idx] has ever assigned an index to) never
    exceeds [count_loc] (the number of calls [COUNT q] has ever routed
    through), because every ROUTED call bumps [count_loc] by exactly one
    and [ss_count_loc] by AT MOST one (only on a brand new [ss]); and
    every index [get_ss_idx] ever hands out is [< ss_count_loc] at the
    moment it is assigned (a fresh index is always the OLD
    [ss_count_loc], strictly less than the incremented one). So inside a
    routed call -- where [count_loc] already holds [count_old.+1] with
    [count_old < q], i.e. [count_loc <= q] -- any [idx] [get_ss_idx]
    produces satisfies [idx <= ss_count_loc <= count_loc <= q], in fact
    [idx < q] (from [idx < ss_count_loc <= count_old < q] for a fresh
    index, or from the invariant directly for a repeat one), so
    [KDF_hyb q]'s "idx < q" test always succeeds and its surviving
    branch is exactly [KDF_mid]'s own unconditional [mid_loc] logic.
    This needs only a per-call [eq_rel_perf_ind] invariant tying
    [ss_count_loc]/[count_loc]/[ss_index_loc] together on the LHS heap
    ([KDF_hyb_q_mid_inv] below) -- NOT the induction-on-adversary-code
    machinery [Pr_bad_adv_bound] needs for the birthday step, since
    [COUNT q]'s own wrapper code already turns "at most [q] routed
    calls, ever" into a fact re-established at every single call by the
    invariant, rather than a global property of the run that only
    [code_link]-level induction can see. *)
  Definition KDF_hyb_q_mid_inv : precond :=
    heap_ignore [fmap ss_count_loc; ss_index_loc] ⋊
    rel_app [:: (lhs, ss_count_loc); (lhs, count_loc); (lhs, ss_index_loc)]
      (fun (cnt c : nat) (SIdx : chMap 'ss 'nat) =>
         (cnt <= c)%N /\ forall ss idx, getm SIdx ss = Some idx -> (idx < cnt)%N).

  Lemma KDF_hyb_q_mid_inv_count_step c :
    preserve_update_mem
      [:: hpv_r count_loc c.+1; hpv_l count_loc c.+1]
      [:: hpv_r count_loc c; hpv_l count_loc c]
      KDF_hyb_q_mid_inv.
  Proof.
    eapply preserve_update_mem_conj.
    - ssprove_invariant.
    - move=> s0 s1 h /=.
      have h1 : rel_app [:: (lhs, ss_count_loc); (lhs, count_loc); (lhs, ss_index_loc)]
        (fun (cnt c0 : nat) (SIdx : chMap 'ss 'nat) =>
           (cnt <= c0)%N /\ forall ss idx, getm SIdx ss = Some idx -> (idx < cnt)%N) (s0, s1).
      { move: h.
        rewrite /remember_pre /rem_lhs /rem_rhs /rem_inv /=.
        move=> [[h0 _] _]. exact: h0. }
      rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in h1.
      move: h1 => [Hle Hall].
      rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
      rewrite /remember_pre /rem_lhs /rem_rhs /rem_inv /= in h.
      move: h => [[h0 Hceq] _].
      simpl in Hceq.
      rewrite (get_set_heap_neq _ _ _ _ (isT : ss_count_loc.1 != count_loc.1)) get_set_heap_eq.
      split.
      + rewrite Hceq in Hle. exact: (leqW Hle).
      + move=> ss idx.
        rewrite (get_set_heap_neq _ _ _ _ (isT : ss_index_loc.1 != count_loc.1)).
        exact: (Hall ss idx).
  Qed.

  (** Companion to [KDF_hyb_q_mid_inv_count_step], for the OTHER place
    [KDF_hyb_q_mid_inv]'s bookkeeping locations get updated: [get_ss_idx]
    assigning a brand new [ss] the fresh index [cnt0] (the then-current
    [ss_count_loc]), bumping [ss_count_loc] to [cnt0.+1] and recording
    [ss ↦ cnt0] in [ss_index_loc]. Proved as a bare [preserve_update_mem]
    fact (not inline in the main proof) so it can be discharged via
    [ssprove_restore_mem] like [KDF_hyb_q_mid_inv_count_step] -- going
    through [rpre_hypothesis_rule]/[rpre_weaken_rule] instead (as an
    earlier attempt did) round-trips the code through the semantic
    judgment machinery and reintroduces an unfolded [bind]/[resolve]
    term that no longer unifies with [r_get_vs_get_remember]'s pattern. *)
  Lemma KDF_hyb_q_mid_inv_fresh_ss_step (ss : 'ss) (c cnt0 : nat) (SIdx : chMap 'ss 'nat) :
    (cnt0 <= c)%N ->
    preserve_update_mem
      [:: hpv_l ss_index_loc (setm SIdx ss cnt0); hpv_l ss_count_loc cnt0.+1]
      [:: hpv_l ss_index_loc SIdx; hpv_l ss_count_loc cnt0; hpv_l count_loc c.+1]
      KDF_hyb_q_mid_inv.
  Proof.
    move=> Hcnt0le s0 s1 [[[Hbase Hceq] Hcnteq] HSI].
    rewrite /rem_lhs /rem_inv /= in Hceq Hcnteq HSI.
    have h1 : rel_app [:: (lhs, ss_count_loc); (lhs, count_loc); (lhs, ss_index_loc)]
      (fun (cnt c0 : nat) (SIdx0 : chMap 'ss 'nat) =>
         (cnt <= c0)%N /\ forall ss0 idx0, getm SIdx0 ss0 = Some idx0 -> (idx0 < cnt)%N) (s0, s1).
    { move: Hbase. rewrite /KDF_hyb_q_mid_inv /inv_conj /=. move=> [_ h]. exact: h. }
    rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in h1.
    move: h1 => [Hle Hall].
    rewrite Hcnteq in Hall.
    move: Hbase. rewrite /KDF_hyb_q_mid_inv /inv_conj /=. move=> [Hig _].
    split.
    - move=> l Hl.
      have Hne1 : l.1 != ss_index_loc.1.
      { apply/eqP => Heq. case/negP: Hl. rewrite Heq. apply: fhas_in. fmap_solve. }
      have Hne2 : l.1 != ss_count_loc.1.
      { apply/eqP => Heq. case/negP: Hl. rewrite Heq. apply: fhas_in. fmap_solve. }
      rewrite (get_set_heap_neq _ _ _ _ Hne1) (get_set_heap_neq _ _ _ _ Hne2).
      exact: (Hig l Hl).
    - rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /=.
      rewrite (get_set_heap_neq _ _ _ _ (isT : ss_count_loc.1 != ss_index_loc.1)).
      rewrite get_set_heap_eq.
      rewrite (get_set_heap_neq _ _ _ _ (isT : count_loc.1 != ss_index_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : count_loc.1 != ss_count_loc.1)).
      split.
      + by rewrite Hceq.
      + move=> ss0 idx0.
        rewrite get_set_heap_eq setmE.
        case: ifP => Heq [Hidxeq].
        * rewrite -Hidxeq. exact: ltnSn.
        * rewrite -HSI in Hidxeq.
          exact: (ltn_trans (Hall ss0 idx0 Hidxeq) (ltnSn cnt0)).
  Qed.

  (** The core, probability-free relational argument: on the LHS heap of
    [COUNT q ∘ KDF_hyb q], [ss_count_loc <= count_loc] and every index in
    [ss_index_loc] is [< ss_count_loc] ([KDF_hyb_q_mid_inv]); this makes
    [KDF_hyb q]'s "idx < q" test always true inside a call [COUNT q]
    actually routes through, so its surviving branch collapses onto
    [KDF_mid]'s own [mid_loc] code verbatim. *)
  Lemma COUNT_KDF_hyb_q_KDF_mid_perf q :
    COUNT q ∘ KDF_hyb q ≈₀ COUNT q ∘ KDF_mid.
  Proof.
    apply eq_rel_perf_ind with KDF_hyb_q_mid_inv.
    - eapply Invariant_inv_conj.
      + eapply Invariant_heap_ignore. fmap_solve.
      + eapply SemiInvariant_relApp.
        * simpl. repeat split. all: try fmap_solve; try done.
        * done.
    - simplify_eq_rel arg.
      destruct arg as [ss info].
      ssprove_code_simpl.
      simpl.
      apply: r_get_vs_get_remember => c.
      case Hc: (c < q)%N.
      2: {
        (* budget exhausted: both sides run the identical dummy sample. *)
        apply: r_uniform_bij => [|y]. 1: exists id; done.
        apply: r_ret => s0 s1 h. split; [ reflexivity | extract_base_inv h ].
      }
      (* routed call: [COUNT q] increments [count_loc], both sides run
        the imported [derive]'s body. *)
      simpl.
      simplify_linking.
      apply: r_put_vs_put.
      (* [KDF_hyb_q_mid_inv_count_step] alone only gives the WEAKENED bound
        [ss_count_loc <= count_loc.+1]; the "brand new [ss]" branch below
        needs the SHARPER, transient fact [ss_count_loc <= c] (the OLD
        [count_loc], strictly less than the just-incremented one) to rule
        out [ss_count_loc = q] exactly. [Hweaken] carries that sharper
        bound out of the flush as an ordinary Coq value ([cnt0], with
        [cnt0 <= c] a plain fact alongside it) instead of folding it into
        the invariant itself -- [rem_lhs ss_count_loc cnt0] stays
        [ssprove_restore_mem]-fold-compatible, unlike an inequality-shaped
        [rel_app] conjunct, which is what a first attempt at this ran
        into. *)
      have Hweaken : ∀ s0 s1,
        (set_rhs count_loc c.+1 (set_lhs count_loc c.+1
          (KDF_hyb_q_mid_inv ⋊ rem_lhs count_loc c ⋊ rem_rhs count_loc c))) (s0,s1) ->
        ∃ cnt0, (cnt0 <= c)%N ∧
          (KDF_hyb_q_mid_inv ⋊ rem_lhs count_loc c.+1 ⋊ rem_lhs ss_count_loc cnt0) (s0,s1).
      { move=> s0 s1 [s1' [[s0' [Hpre0 Es0]] Es1]].
        subst s0 s1.
        have h1 : rel_app [:: (lhs, ss_count_loc); (lhs, count_loc); (lhs, ss_index_loc)]
          (fun (cnt c0 : nat) (SIdx0 : chMap 'ss 'nat) =>
             (cnt <= c0)%N /\ forall ss0 idx0, getm SIdx0 ss0 = Some idx0 -> (idx0 < cnt)%N) (s0', s1').
        { move: Hpre0. rewrite /KDF_hyb_q_mid_inv /inv_conj /=. move=> [[[_ h] _] _]. exact: h. }
        rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in h1.
        move: h1 => [Hle0 _].
        have Hbase_new := KDF_hyb_q_mid_inv_count_step c s0' s1' Hpre0.
        move: Hpre0 => [[_ Hceq0] _].
        rewrite /rem_lhs /rem_inv /= in Hceq0.
        rewrite Hceq0 in Hle0.
        exists (get_heap s0' ss_count_loc). split; [exact: Hle0 |].
        split.
        - split.
          + exact: Hbase_new.
          + rewrite /rem_lhs /rem_inv /=. by rewrite get_set_heap_eq.
        - rewrite /rem_lhs /rem_inv /=.
          by rewrite (get_set_heap_neq _ _ _ _ (isT : ss_count_loc.1 != count_loc.1)).
      }
      apply: rpre_hypothesis_rule => s0 s1 Hpre.
      have [cnt0 [Hcnt0le Hnewpre]] := Hweaken s0 s1 Hpre.
      eapply rpre_weaken_rule with
        (pre := λ '(s0',s1'), (KDF_hyb_q_mid_inv ⋊ rem_lhs count_loc c.+1
          ⋊ rem_lhs ss_count_loc cnt0) (s0',s1')).
      2: { move=> s0' s1' [] /= -> ->. exact: Hnewpre. }
      apply: r_get_remember_lhs => SIdx.
      case HSIdx: (SIdx ss) => [idx|].
      + (* [ss] already indexed: read off [idx < ss_count_loc <= c.+1 <= q]
          straight from the invariant. *)
        apply: rpre_hypothesis_rule => t0 t1 Hpre2.
        have Hidxlt : (idx < q)%N.
        { move: Hpre2 => [[[Hbase Hceq] Hcnteq] HSI].
          rewrite /rem_lhs /rem_inv /= in Hceq HSI.
          have h1 : rel_app [:: (lhs, ss_count_loc); (lhs, count_loc); (lhs, ss_index_loc)]
            (fun (cnt c0 : nat) (SIdx0 : chMap 'ss 'nat) =>
               (cnt <= c0)%N /\ forall ss0 idx0, getm SIdx0 ss0 = Some idx0 -> (idx0 < cnt)%N) (t0, t1).
          { move: Hbase. rewrite /KDF_hyb_q_mid_inv /inv_conj /=. move=> [_ h]. exact: h. }
          rewrite (rel_app_cons) (rel_app_cons) (rel_app_cons) (rel_app_nil) /= in h1.
          move: h1 => [Hle Hall].
          have Hidxcnt : (idx < get_heap t0 ss_count_loc)%N.
          { apply: (Hall ss). by rewrite HSI. }
          apply: leq_trans; [exact: Hidxcnt |].
          rewrite Hceq in Hle.
          exact: (leq_trans Hle Hc). }
        eapply rpre_weaken_rule with
          (pre := λ '(s0',s1'), (KDF_hyb_q_mid_inv ⋊ rem_lhs count_loc c.+1
            ⋊ rem_lhs ss_count_loc cnt0
            ⋊ rem_lhs ss_index_loc SIdx) (s0',s1')).
        2: { move=> s0' s1' [] /= -> ->. exact: Hpre2. }
        simpl.
        rewrite Hidxlt /=.
        apply: r_get_vs_get_remember => T.
        case HT: (getm T ss) => [prk|] /=.
        * apply: r_get_vs_get_remember => T2.
          case HT2: (getm T2 (prk, info)) => [y|] /=.
          -- apply: r_ret => s0' s1' h. split; [ reflexivity | extract_base_inv h ].
          -- apply: r_uniform_bij => [|y']. 1: exists id; done.
             apply: r_put_vs_put.
             ssprove_restore_mem; last by apply: r_ret.
             close_preserve.
        * apply: r_uniform_bij => [|prk']. 1: exists id; done.
          apply: r_put_vs_put.
          ssprove_restore_mem; [ close_preserve | ].
          apply: r_get_vs_get_remember => T2.
          case HT2: (getm T2 (prk', info)) => [y|] /=.
          -- apply: r_ret => s0' s1' h. split; [ reflexivity | extract_base_inv h ].
          -- apply: r_uniform_bij => [|y']. 1: exists id; done.
             apply: r_put_vs_put.
             ssprove_restore_mem; last by apply: r_ret.
             close_preserve.
      + (* [ss] is brand new: [get_ss_idx] assigns it the fresh index
          [cnt0] (the [ss_count_loc] we already remembered above), which
          is [<= c < q] by [Hcnt0le]. [KDF_hyb_q_mid_inv_fresh_ss_step]
          (a bare [preserve_update_mem] fact, not an inline manual
          derivation) re-establishes the base invariant after the
          [ss_count_loc]/[ss_index_loc] bump -- going through
          [rpre_hypothesis_rule]/[rpre_weaken_rule] here instead (as
          for the [Some idx] case above) round-trips the remaining code
          through the semantic-judgment machinery and leaves behind an
          unfolded [bind]/[resolve] term that no longer unifies with
          [r_get_vs_get_remember]'s pattern; [ssprove_restore_mem] avoids
          that entirely. *)
        apply: r_get_remind_lhs.
        apply: r_put_lhs.
        apply: r_put_lhs.
        have Hcnt0lt : (cnt0 < q)%N := leq_ltn_trans Hcnt0le Hc.
        rewrite Hcnt0lt /=.
        ssprove_restore_mem; [ exact: (KDF_hyb_q_mid_inv_fresh_ss_step ss c cnt0 SIdx Hcnt0le) | ].
        apply: r_get_vs_get_remember => T.
        case HT: (getm T ss) => [prk|] /=.
        * apply: r_get_vs_get_remember => T2.
          case HT2: (getm T2 (prk, info)) => [y|] /=.
          -- apply: r_ret => s0' s1' h. split; [ reflexivity | extract_base_inv h ].
          -- apply: r_uniform_bij => [|y']. 1: exists id; done.
             apply: r_put_vs_put.
             ssprove_restore_mem; last by apply: r_ret.
             close_preserve.
        * apply: r_uniform_bij => [|prk']. 1: exists id; done.
          apply: r_put_vs_put.
          ssprove_restore_mem; [ close_preserve | ].
          apply: r_get_vs_get_remember => T2.
          case HT2: (getm T2 (prk', info)) => [y|] /=.
          -- apply: r_ret => s0' s1' h. split; [ reflexivity | extract_base_inv h ].
          -- apply: r_uniform_bij => [|y']. 1: exists id; done.
             apply: r_put_vs_put.
             ssprove_restore_mem; last by apply: r_ret.
             close_preserve.
  Qed.

  Lemma COUNT_KDF_hyb_q_KDF_mid_equiv LA A q :
    ValidPackage LA DERIVE_export A_export A →
    fseparate LA KDF_hyb_locs →
    fseparate LA KDF_mid_locs →
    fseparate LA [fmap count_loc] →
    AdvantageE (COUNT q ∘ KDF_hyb q) (COUNT q ∘ KDF_mid) A = 0.
  Proof.
    intros vA d1 d2 d3.
    apply: (COUNT_KDF_hyb_q_KDF_mid_perf q).
    - apply: fseparateUr; [exact d3 | exact d1].
    - apply: fseparateUr; [exact d3 | exact d2].
  Qed.

  (**
    Step 1: hybrid argument over the <= q distinct shared secrets
    Extract can see, swapping the real PRF-Expand computation for an
    independent random one, one instance at a time. This is the same
    shape as [hyb_security_based_on_prf] in PRFPRG.v, generalised from "the
    first i queries" to "the first i *distinct shared secrets*" -- closer
    in spirit to [Adv_hybrid] / [HYB_MI_CPA] in PKE/MultiInstance.v, since
    the adversary chooses which shared secret is "new" adaptively rather
    than in a fixed order. Assembled here from the three pieces above via
    the triangle inequality, exactly as [security_of_KDF] below assembles
    steps 1 and 2.

    NOTE on the bound's shape: the RHS is [prf_epsilon (A ∘ COUNT q ∘
    KDF_hyb_EVAL i)], NOT the "bare" [prf_epsilon A] an earlier draft of
    this theorem used. [prf_epsilon A := Advantage EVAL A] composes [A]
    directly against [EVAL b] ([A ∘ EVAL b]); since [A] here has import
    interface [DERIVE_export] (op id [0]) while [EVAL_export] only ever
    offers op id [EVAL_OP] (id [1]) -- disjoint interfaces -- [A]'s own
    [ValidPackage] constraint (it may only ever call ops in its stated
    import interface) means [A] can NEVER actually invoke [EVAL_OP], so
    [resolve (EVAL b) (0, _) = resolve (EVAL b') (0, _)] identically for
    both [b], for every op [A] could ever perform; a structural induction
    on [A]'s own code shows [code_link (resolve A RUN tt) (EVAL true) =
    code_link (resolve A RUN tt) (EVAL false)] as raw terms, hence
    [prf_epsilon A = 0] UNCONDITIONALLY for every such [A] -- independent
    of [q], of the adversary's strategy, and of [PRF]'s own security.
    Taking that literally would force this theorem's LHS to be exactly
    [0] too, for every [PRF] and every adversary, which is false in
    general (e.g. take [PRF info prk := info], ignoring [prk]: an
    adversary comparing [DERIVE (ss, info)] against [info] directly
    distinguishes [KDF_real] (always equal) from [KDF_mid] (equal only
    with probability [1/Out_N]) with advantage close to [1]). The
    header's OWN roadmap (comment near the top of this file) already
    anticipated this, writing the bound as [prf_epsilon (... i-th hybrid
    reduction ...)] rather than bare [prf_epsilon A] -- i.e. this fixes a
    genuine, provable-unsound placeholder left over from early
    scaffolding, matching the file's own originally documented intent
    (and exactly mirroring [PRFPRG.v]'s own [hyb_security_based_on_prf],
    whose bound is likewise stated at the composed reduction adversary,
    never at the bare top-level one). See [security_of_KDF] below, whose
    final bound is adjusted identically and for the same reason.

    UPDATE: the bound below now ALSO carries a second sum of per-hop
    up-to-bad terms, [\sum_(i<q) Pr_bad ((A ∘ COUNT q) ∘ KDF_hybE_bad i)
    4 true]. This is because the EVAL-false leg of each hybrid hop
    ([KDF_hyb_EVAL i ∘ EVAL false] vs [KDF_hyb i.+1]) is no longer a
    perfect ([≈₀]) equivalence -- see the counterexample docstring above
    [KDF_hybE_bad]/[get_prk_bad] for why the naive claim
    ([KDF_hyb_KDF_hyb_EVAL_false_equiv]) was FALSE -- only an up-to-bad
    BOUND ([KDF_hyb_EVAL_false_bound]), reusing [KDF_mid]/[KDF_mid']/
    [KDF_bad]'s own birthday-collision machinery one hybrid hop at a
    time. See [security_of_KDF]'s own docstring for how this second sum
    collapses to [q * birthday_bound q]. *)
  Theorem KDF_real_KDF_mid_bound LA A q :
    ValidPackage LA DERIVE_export A_export A →
    fseparate LA KDF_real_locs →
    fseparate LA KDF_mid_locs →
    fseparate LA KDF_hyb_locs →
    fseparate LA KDF_hybE_bad_locs →
    fseparate LA KDF_hyb_bad_locs →
    fseparate LA [fmap count_loc] →
    fseparate LA [fmap eval_key_loc] →
    fseparate LA [fmap eval_tbl_loc] →
    lossless_valid_adv LA DERIVE_export (resolve A RUN tt) →
    AdvantageE (COUNT q ∘ KDF_real) (COUNT q ∘ KDF_mid) A <=
      \sum_(i < q) prf_epsilon ((A ∘ COUNT q) ∘ KDF_hyb_EVAL i)
      + \sum_(i < q) Pr_bad ((A ∘ COUNT q) ∘ KDF_hybE_bad i) 4 true.
  Proof.
    intros vA d1 d2 d3 d4 d5 d6 d7 d8 Hlva.
    ssprove triangle (COUNT q ∘ KDF_real)
      [:: COUNT q ∘ KDF_hyb 0 ; COUNT q ∘ KDF_hyb q ] (COUNT q ∘ KDF_mid) A as ineq.
    eapply le_trans. 1: exact ineq.
    have e1 := COUNT_KDF_real_KDF_hyb0_bound LA A q vA d1 d3 d6.
    have e3 := COUNT_KDF_hyb_q_KDF_mid_equiv LA A q vA d3 d2 d6.
    rewrite e1 e3 GRing.add0r GRing.addr0.
    exact: (COUNT_KDF_hyb_bound LA A q vA d3 d7 d8 d4 d5 d6 Hlva).
  Qed.

  (**
    Step 2: bounding the gap between [KDF_mid] and [KDF_ideal], via the
    [KDF_bad] game defined above. It decomposes into three parts:

    (2a) DONE ([KDF_bad_KDF_ideal_equiv] above): [KDF_bad] ≈₀ [KDF_ideal],
         perfect equivalence. This needed no probability reasoning, only
         bookkeeping -- [KDF_bad]'s output always goes through [indep_loc]
         exactly like [KDF_ideal]'s [ideal_loc], regardless of [bad_loc];
         the invariant is simply that these two tables stay equal
         ([KDF_bad_ideal_inv]), and the ghost computation on [extract_loc]
         / [used_prk_loc] / [bad_loc] is dead code with respect to it.

    (2b) DONE ([KDF_mid'_KDF_bad_bound] above, via [KDF_mid_KDF_mid'_equiv]
         + [KDF_mid'_KDF_bad_eq_up_to_bad] + [eq_upto_bad_perf_ind]):
         AdvantageE KDF_mid' KDF_bad A <= Pr_bad (A ∘ KDF_mid') 4 true.
         This was the generic "Fundamental Lemma" of up-to-bad reasoning
         applied to this file's [KDF_mid'_bad_inv]; the reusable pieces
         ([eq_upto_bad_perf_ind], [Pr_bad]) now live in [pkg_upto_bad.v].

    (2c) DONE ([Pr_bad_COUNT_KDF_mid'_bound] below, via
         [Pr_bad_adv_bound]): Pr_bad (A ∘ COUNT q ∘ KDF_mid') 4 true
         <= birthday_bound q (equivalently, [<= bad_bound q 0], which is
         <= [birthday_bound q] by trivial arithmetic). The pure
         combinatorics are [Birthday.v]'s [bad_dist_bound]; the
         connection to the package's actual run semantics is
         [Pr_bad_adv_bound] -- an induction over the adversary's code
         showing that running (an arbitrary, [COUNT q]-bounded adversary
         composed with) [KDF_mid'] can only set [bad_loc] as often as
         [q] adaptively-chosen draws from a size-[PRK_N] space can
         collide (a repeat [ss] query costs no fresh sample, so the
         *distinct*-sample count driving real collisions is <= the
         [COUNT]-bounded *total* query count [q], never more).
  *)

  (* --- (1)/(2): pushing [COUNT q] through a perfect ([≈₀]) equivalence ---

    [Advantage_link] (pkg_advantage.v) is EXACTLY the associativity fact
    needed: [AdvantageE G0 G1 (A ∘ P) = AdvantageE (P ∘ G0) (P ∘ G1) A].
    Reading it right-to-left with [P := COUNT q] reduces the LHS/RHS pair
    we actually care about ([COUNT q ∘ G0] vs [COUNT q ∘ G1], tested by the
    THEOREM's own adversary [A]) to the ORIGINAL (COUNT-free) equivalence
    ([G0] vs [G1]), tested by the composed adversary [A ∘ COUNT q]. This
    composed-adversary reasoning is sound here with NO extra losslessness
    concerns, because [≈₀]/[eq_rel_perf_ind] is EXACT-match relational
    reasoning (a plain RHL coupling argument), which places no requirement
    on either side being lossless -- unlike the up-to-bad machinery below
    (see the docstring on [KDF_mid_KDF_ideal_bound] for why THAT distinction
    matters a great deal here). [COUNT_link_valid] itself now lives above,
    right before its first use in [COUNT_KDF_hyb_bound]. *)

  Lemma COUNT_KDF_mid_KDF_mid'_bound LA A q :
    ValidPackage LA DERIVE_export A_export A →
    fseparate LA KDF_mid_locs →
    fseparate LA KDF_mid'_locs →
    fseparate LA [fmap count_loc] →
    AdvantageE (COUNT q ∘ KDF_mid) (COUNT q ∘ KDF_mid') A = 0.
  Proof.
    intros vA d1 d2 d3.
    have vAC := COUNT_link_valid LA A q vA d3.
    rewrite -(Advantage_link KDF_mid KDF_mid' A (COUNT q)).
    apply: KDF_mid_KDF_mid'_equiv.
    - apply: fseparateUl; [exact d1 | apply: fseparateC; fmap_solve].
    - apply: fseparateUl; [exact d2 | apply: fseparateC; fmap_solve].
  Qed.

  Lemma COUNT_KDF_bad_KDF_ideal_bound LA A q :
    ValidPackage LA DERIVE_export A_export A →
    fseparate LA KDF_bad_locs →
    fseparate LA KDF_ideal_locs →
    fseparate LA [fmap count_loc] →
    AdvantageE (COUNT q ∘ KDF_bad) (COUNT q ∘ KDF_ideal) A = 0.
  Proof.
    intros vA d1 d2 d3.
    have vAC := COUNT_link_valid LA A q vA d3.
    rewrite -(Advantage_link KDF_bad KDF_ideal A (COUNT q)).
    apply: KDF_bad_KDF_ideal_equiv.
    - apply: fseparateUl; [exact d1 | apply: fseparateC; fmap_solve].
    - apply: fseparateUl; [exact d2 | apply: fseparateC; fmap_solve].
  Qed.

  (** [KDF_mid'_KDF_bad_bound] instantiated at the COMPOSED adversary
    [A ∘ COUNT q]: [Advantage_link] (read right-to-left, exactly like
    [COUNT_KDF_mid_KDF_mid'_bound]/[COUNT_KDF_bad_KDF_ideal_bound] above)
    turns the goal into exactly [KDF_mid'_KDF_bad_bound]'s own shape at
    adversary [A ∘ COUNT q], whose [lossless_valid_adv] hypothesis is
    discharged by [lossless_valid_adv_COUNT_link] together with
    [resolve_link] (which identifies [resolve (A ∘ COUNT q) RUN tt] with
    [code_link (resolve A RUN tt) (COUNT q)]). *)
  Lemma COUNT_KDF_mid'_KDF_bad_bound LA A q :
    ValidPackage LA DERIVE_export A_export A →
    fseparate LA KDF_mid'_locs →
    fseparate LA KDF_bad_locs →
    fseparate LA [fmap count_loc] →
    lossless_valid_adv LA DERIVE_export (resolve A RUN tt) →
    AdvantageE (COUNT q ∘ KDF_mid') (COUNT q ∘ KDF_bad) A <=
      Pr_bad ((A ∘ COUNT q) ∘ KDF_mid') 4 true.
  Proof.
    intros vA d1 d2 d3 Hlva.
    have vAC := COUNT_link_valid LA A q vA d3.
    rewrite -(Advantage_link KDF_mid' KDF_bad A (COUNT q)).
    apply: KDF_mid'_KDF_bad_bound.
    - apply: fseparateUl; [exact d1 | apply: fseparateC; fmap_solve].
    - apply: fseparateUl; [exact d2 | apply: fseparateC; fmap_solve].
    - rewrite resolve_link.
      apply: lossless_valid_adv_COUNT_link; [exact d3 | exact Hlva].
  Qed.

  (** Splitting half of [fseparateUr]/[fseparateUl] (not in
    [fmap_extra.v], so re-derived locally): [fseparate] against a union
    splits into [fseparate] against each half. Needed to recover
    [fseparate LA KDF_mid'_locs]/[fseparate LA KDF_bad_locs] (as required
    by e.g. [COUNT_KDF_mid'_KDF_bad_bound] above) from the single,
    more economical hypothesis [fseparate LA KDF_mid'_bad_locs] used in
    [KDF_mid_KDF_ideal_bound]/[security_of_KDF] below. *)
  Lemma fseparate_split_r {T : ordType} {S S'}
    (m : {fmap T → S}) (m' m'' : {fmap T → S'}) :
    fseparate m (unionm m' m'') → fseparate m m' ∧ fseparate m m''.
  Proof.
    move=> [H]. split; apply: fsep; move: H; rewrite domm_union fdisjointUr;
      move=> /andP [] //.
  Qed.

  (* Any adversary location [l] is distinct (at the level of the raw
    [nat] key) from any location [x] that some OTHER location map [M] is
    known [fseparate] from -- the generic form of the "l.1 != loc.1"
    facts already derived ad hoc (via the [isT : _.1 != _.1] trick, only
    usable for two CONCRETE distinct locations) elsewhere in this file;
    here [l] ranges over the adversary's own, abstract locations, so that
    trick doesn't apply and we need the [fhas]/[fseparate] route instead,
    exactly as [bad_preserved_link] (pkg_upto_bad.v) does for its own
    single "[bad_id] fresh for [LA]" fact. *)
  Lemma loc_neq_of_separate {LA M : Locations} (l x : Location) :
    fhas M x → fseparate LA M → fhas LA l → x.1 != l.1.
  Proof.
    move=> Hx Hsep Hl.
    apply/eqP => Heq.
    have Hindomm := fhas_in LA l Hl.
    have Hnotin := notin_has_separate M LA x Hx (fseparateC _ _ Hsep).
    move: Hnotin => /negP; apply.
    rewrite Heq. exact: Hindomm.
  Qed.

  (* Pre-proven in ISOLATION (own, tiny proof context) rather than inline
    via [fmap_solve] inside [Pr_bad_adv_bound]'s putr case: with several
    [have]s each separately calling [fmap_solve] in a context that already
    contains the PREVIOUS [have]s' (nontrivial) proof terms, [fmap_solve]'s
    [eauto]/[Hint Extern ... eassumption]-based search was observed to
    blow up catastrophically (fast with one such [have], but did not
    finish within multiple minutes with two) -- confirmed by direct
    bisection of the proof script under [make]. Applying these as plain
    terms below sidesteps the issue entirely. *)
  Lemma fhas_extract_KDF_mid' : fhas KDF_mid'_locs extract_loc.
  Proof. fmap_solve. Qed.

  Lemma fhas_used_prk_KDF_mid' : fhas KDF_mid'_locs used_prk_loc.
  Proof. fmap_solve. Qed.

  Lemma fhas_bad_KDF_mid' : fhas KDF_mid'_locs bad_loc.
  Proof. fmap_solve. Qed.

  Lemma fhas_count_loc_self : fhas [fmap count_loc] count_loc.
  Proof. fmap_solve. Qed.

  (** THE core new argument (see the docstring on [Pr_bad_COUNT_KDF_mid'_bound]
    below for the informal correspondence this formalises): by induction
    on an ARBITRARY [lossless_valid_adv]-adversary [Ac]'s own code
    (mirroring [pkg_upto_bad.v]'s [bad_preserved_link]/
    [eq_up_to_bad_adversary_link] recursion over [code_link], and
    [lossless_valid_adv_COUNT_link]'s own recursion over the SAME [Ac]
    above), bounding the probability that running [Ac] against
    [COUNT q ∘ KDF_mid'] (starting from an arbitrary heap [h] already
    satisfying [KDF_mid']'s own internal bookkeeping invariants) ever
    ends with [bad_loc] set.

    The bound is exactly [Birthday.bad_bound]'s own shape, read off
    [h]'s own [count_loc]/[used_prk_loc] (playing the role of
    [bad_dist]'s remaining-steps/"used" arguments respectively) -- except
    when [bad_loc] is ALREADY [true] in [h], where the trivial bound [1]
    is used instead (no further structure needed once "bad" has already
    happened). *)
  Lemma Pr_bad_adv_bound {LA : Locations} {B : choiceType} (Ac : raw_code B) (q : nat)
    (Hlva : lossless_valid_adv LA DERIVE_export Ac)
    (Hsep1 : fseparate LA KDF_mid'_locs)
    (Hsep2 : fseparate LA [fmap count_loc]) :
    forall h : heap,
      used_prk_correspondence (get_heap h extract_loc) (get_heap h used_prk_loc) →
      extract_injective (get_heap h extract_loc) →
      (get_heap h count_loc <= q)%N →
      \P_[ Pr_code (code_link Ac (COUNT q ∘ KDF_mid')) h ]
        (fun '(_, h') => get_heap h' bad_loc)
      <= (if get_heap h bad_loc then 1
          else Birthday.bad_bound (fin_family PRK_N) (q - get_heap h count_loc)
                 #|domm (get_heap h used_prk_loc)|).
  Proof.
    induction Hlva as [x0 | o x k Ho k' IH | l k Hl k' IH | l v k Hl IH | op k Hop k' IH];
      move=> h Hcorr Hinj Hcount.
    - (* ret *)
      rewrite /= Pr_code_ret pr_dunit /=.
      case: (boolP (get_heap h bad_loc)) => Hb /=.
      + exact: lexx.
      + exact: bad_bound_ge0.
    - (* opr: the one real DERIVE call *)
      fmap_invert Ho.
      case: x => ss info /=.
      simplify_linking.
      rewrite Pr_code_get.
      case: ifP => Hcnt2 /=.
      { (* count < q: real call routed to KDF_mid' *)
        rewrite Pr_code_put /=.
        rewrite bind_ret.
        simplify_linking.
        rewrite Pr_code_get.
        rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != count_loc.1)).
        case Heqx : (get_heap h extract_loc ss) => [prk|] /=.
        { (* repeat: ss already extracted *)
          have Hcard : (0 < #|fin_family PRK_N|)%N.
          { rewrite card_fin_family_PRK_N. exact: PRK_N_gt0. }
          have Hcorr1 : used_prk_correspondence
              (get_heap (set_heap h count_loc (get_heap h count_loc).+1) extract_loc)
              (get_heap (set_heap h count_loc (get_heap h count_loc).+1) used_prk_loc).
          { rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != count_loc.1))
                    (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != count_loc.1)).
            exact: Hcorr. }
          have Hinj1 : extract_injective (get_heap (set_heap h count_loc (get_heap h count_loc).+1) extract_loc).
          { rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != count_loc.1)). exact: Hinj. }
          have Hcount1 : (get_heap (set_heap h count_loc (get_heap h count_loc).+1) count_loc <= q)%N.
          { rewrite get_set_heap_eq. exact: Hcnt2. }
          have Hbound1 :
            (if get_heap (set_heap h count_loc (get_heap h count_loc).+1) bad_loc then 1
             else bad_bound (fin_family PRK_N) (q - get_heap (set_heap h count_loc (get_heap h count_loc).+1) count_loc)
                    #|domm (get_heap (set_heap h count_loc (get_heap h count_loc).+1) used_prk_loc)|)
            <= (if get_heap h bad_loc then 1
                else bad_bound (fin_family PRK_N) (q - get_heap h count_loc) #|domm (get_heap h used_prk_loc)|).
          { rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != count_loc.1))
                    (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != count_loc.1))
                    get_set_heap_eq.
            case: (get_heap h bad_loc) => //.
            apply: (bad_bound_mono_q (fin_family PRK_N) Hcard).
            exact: (leq_sub2l q (leqnSn (get_heap h count_loc))). }
          rewrite Pr_code_get.
          case: (get_heap (set_heap h count_loc (get_heap h count_loc).+1) mid_loc (prk, info)) => [y|] /=.
          { apply: (le_trans (IH y (set_heap h count_loc (get_heap h count_loc).+1) Hcorr1 Hinj1 Hcount1)).
            exact: Hbound1. }
          { rewrite Pr_code_sample __deprecated__pr_dlet.
            apply: exp_le_bd.
            { case: (get_heap h bad_loc); [exact: ler01 | exact: bad_bound_ge0]. }
            { move=> y.
              rewrite Pr_code_put.
              have Hne_e2 : extract_loc.1 != mid_loc.1 := isT.
              have Hne_u2 : used_prk_loc.1 != mid_loc.1 := isT.
              have Hne_b2 : bad_loc.1 != mid_loc.1 := isT.
              have Hne_c2 : count_loc.1 != mid_loc.1 := isT.
              have Hge0 : 0 <= \P_[Pr_code (code_link (k y) (COUNT q ∘ KDF_mid'))
                  (set_heap (set_heap h count_loc (get_heap h count_loc).+1) mid_loc
                     (setm (get_heap (set_heap h count_loc (get_heap h count_loc).+1) mid_loc) (prk, info) y))]
                (fun '(_, h') => get_heap h' bad_loc) := ge0_pr _ _.
              rewrite (ger0_norm Hge0).
              have Hcorr2 : used_prk_correspondence
                  (get_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1) mid_loc
                     (setm (get_heap (set_heap h count_loc (get_heap h count_loc).+1) mid_loc) (prk, info) y)) extract_loc)
                  (get_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1) mid_loc
                     (setm (get_heap (set_heap h count_loc (get_heap h count_loc).+1) mid_loc) (prk, info) y)) used_prk_loc).
              { rewrite (get_set_heap_neq _ _ _ _ Hne_e2) (get_set_heap_neq _ _ _ _ Hne_u2). exact: Hcorr1. }
              have Hinj2 : extract_injective
                  (get_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1) mid_loc
                     (setm (get_heap (set_heap h count_loc (get_heap h count_loc).+1) mid_loc) (prk, info) y)) extract_loc).
              { rewrite (get_set_heap_neq _ _ _ _ Hne_e2). exact: Hinj1. }
              have Hcount2 : (get_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1) mid_loc
                     (setm (get_heap (set_heap h count_loc (get_heap h count_loc).+1) mid_loc) (prk, info) y)) count_loc <= q)%N.
              { rewrite (get_set_heap_neq _ _ _ _ Hne_c2). exact: Hcount1. }
              have Hbound2 :
                (if get_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1) mid_loc
                     (setm (get_heap (set_heap h count_loc (get_heap h count_loc).+1) mid_loc) (prk, info) y)) bad_loc then 1
                 else bad_bound (fin_family PRK_N)
                        (q - get_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1) mid_loc
                             (setm (get_heap (set_heap h count_loc (get_heap h count_loc).+1) mid_loc) (prk, info) y)) count_loc)
                        #|domm (get_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1) mid_loc
                             (setm (get_heap (set_heap h count_loc (get_heap h count_loc).+1) mid_loc) (prk, info) y)) used_prk_loc)|)
                <= (if get_heap h bad_loc then 1
                    else bad_bound (fin_family PRK_N) (q - get_heap h count_loc) #|domm (get_heap h used_prk_loc)|).
              { rewrite (get_set_heap_neq _ _ _ _ Hne_b2) (get_set_heap_neq _ _ _ _ Hne_c2) (get_set_heap_neq _ _ _ _ Hne_u2).
                exact: Hbound1. }
              apply: (le_trans (IH y (set_heap (set_heap h count_loc (get_heap h count_loc).+1) mid_loc
                  (setm (get_heap (set_heap h count_loc (get_heap h count_loc).+1) mid_loc) (prk, info) y))
                  Hcorr2 Hinj2 Hcount2)).
              exact: Hbound2. } } }
        { (* fresh: ss not yet extracted -- the birthday step *)
          case: (boolP (get_heap h bad_loc)) => Hbadh.
          { exact: le1_pr. }
          { rewrite Pr_code_sample __deprecated__pr_dlet.
            have Hgt0 : (0 < q - get_heap h count_loc)%N.
            { by rewrite subn_gt0. }
            have HcntQ : (q - get_heap h count_loc = (q - get_heap h count_loc).-1.+1)%N.
            { by rewrite (prednK Hgt0). }
            rewrite HcntQ.
            have Htest : (uniform PRK_N).π2 = Birthday.unif_F (fin_family PRK_N) := erefl.
            rewrite Htest.
            have Hcardeq : #|[set x0 : fin_family PRK_N | x0 \in domm (get_heap h used_prk_loc)]|
                         = #|domm (get_heap h used_prk_loc)|.
            { by rewrite cardsE. }
            rewrite -Hcardeq.
            have Hcard : (0 < #|fin_family PRK_N|)%N.
            { rewrite card_fin_family_PRK_N. exact: PRK_N_gt0. }
            apply: (expectation_le_bad_bound (fin_family PRK_N) Hcard
              (q - get_heap h count_loc).-1
              [set x0 : fin_family PRK_N | x0 \in domm (get_heap h used_prk_loc)]).
            { move=> x. exact: ge0_pr. }
            { move=> x.
              rewrite Pr_code_put.
              rewrite in_set.
              have Hne_e3 : extract_loc.1 != count_loc.1 := isT.
              rewrite Pr_code_get.
              have Hne_u3 : used_prk_loc.1 != extract_loc.1 := isT.
              have Hne_u4 : used_prk_loc.1 != count_loc.1 := isT.
              rewrite (get_set_heap_neq _ _ _ _ Hne_u3) (get_set_heap_neq _ _ _ _ Hne_u4).
              case: (boolP (x \in domm (get_heap h used_prk_loc))) => Hxused.
              { have [[] Hget] := dommP Hxused.
                rewrite Hget /=.
                apply: (le_trans (y := 1)); [exact: le1_pr | rewrite lerDl; exact: bad_bound_ge0]. }
              { have Hget2 : get_heap h used_prk_loc x = None.
                { apply/dommPn. exact: Hxused. }
                rewrite Hget2 /=.
                rewrite Pr_code_put.
                have Hfresh : forall ss', get_heap h extract_loc ss' <> Some x.
                { move=> ss' Heq.
                  have Hex : exists ss0, get_heap h extract_loc ss0 = Some x := ex_intro _ ss' Heq.
                  have := (proj2 (Hcorr x) Hex).
                  rewrite Hget2. discriminate. }
                have Hinj3 : extract_injective (setm (get_heap h extract_loc) ss x).
                { move=> ss1 ss2 prk0 H1 H2.
                  case: (eqVneq ss1 ss) => Heq1; case: (eqVneq ss2 ss) => Heq2.
                  - by rewrite Heq1 Heq2.
                  - subst ss1. move: H1. rewrite setmE eqxx => [[Heqx0]].
                    move: H2. rewrite setmE (negbTE Heq2) => H2. subst prk0.
                    exfalso. exact: (Hfresh ss2 H2).
                  - subst ss2. move: H2. rewrite setmE eqxx => [[Heqx0]].
                    move: H1. rewrite setmE (negbTE Heq1) => H1. subst prk0.
                    exfalso. exact: (Hfresh ss1 H1).
                  - move: H1 H2. rewrite setmE (negbTE Heq1) setmE (negbTE Heq2) => H1 H2.
                    exact: (Hinj ss1 ss2 prk0 H1 H2). }
                have Hcorr3 : used_prk_correspondence
                    (setm (get_heap h extract_loc) ss x) (setm (get_heap h used_prk_loc) x tt).
                { move=> prk0. case: (eqVneq prk0 x) => Heqp.
                  - subst prk0. rewrite setmE eqxx. split.
                    + move=> _. by exists ss; rewrite setmE eqxx.
                    + move=> _. reflexivity.
                  - rewrite setmE (negbTE Heqp). split.
                    + move=> HU. have [ss0 Hss0] := (proj1 (Hcorr prk0) HU).
                      exists ss0. rewrite setmE.
                      case: (eqVneq ss0 ss) => Hss.
                      * subst ss0. rewrite Hss0 in Heqx. discriminate.
                      * exact: Hss0.
                    + move=> [ss0 Hss0]. move: Hss0. rewrite setmE.
                      case: (eqVneq ss0 ss) => Hss.
                      * move=> [] Heq0. move: Heqp => /eqP Heqp. exfalso. apply: Heqp. by rewrite -Heq0.
                      * move=> Hss0. apply: (proj2 (Hcorr prk0)). by exists ss0. }
                have Hdommcard : #|domm (setm (get_heap h used_prk_loc) x tt)| = (#|domm (get_heap h used_prk_loc)|).+1.
                { have Heq1' : [set y : fin_family PRK_N | y \in x |: domm (get_heap h used_prk_loc)]
                             = (x |: [set y : fin_family PRK_N | y \in domm (get_heap h used_prk_loc)])%SET.
                  { apply/setP => y.
                    rewrite in_set in_fsetU1.
                    rewrite in_setU1 in_set.
                    reflexivity. }
                  rewrite domm_set.
                  rewrite -cardsE Heq1' cardsU1.
                  rewrite in_set (negbTE Hxused) add1n.
                  by rewrite cardsE. }
                have Hne_eu : extract_loc.1 != used_prk_loc.1 := isT.
                have Hne_cu : count_loc.1 != used_prk_loc.1 := isT.
                have Hne_ce2 : count_loc.1 != extract_loc.1 := isT.
                have Hcorr4 : used_prk_correspondence
                    (get_heap (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1)
                         extract_loc (setm (get_heap h extract_loc) ss x)) used_prk_loc (setm (get_heap h used_prk_loc) x tt)) extract_loc)
                    (get_heap (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1)
                         extract_loc (setm (get_heap h extract_loc) ss x)) used_prk_loc (setm (get_heap h used_prk_loc) x tt)) used_prk_loc).
                { rewrite (get_set_heap_neq _ _ _ _ Hne_eu) get_set_heap_eq get_set_heap_eq.
                  exact: Hcorr3. }
                have Hinj4 : extract_injective
                    (get_heap (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1)
                         extract_loc (setm (get_heap h extract_loc) ss x)) used_prk_loc (setm (get_heap h used_prk_loc) x tt)) extract_loc).
                { rewrite (get_set_heap_neq _ _ _ _ Hne_eu) get_set_heap_eq.
                  exact: Hinj3. }
                have Hcount4 : (get_heap (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1)
                         extract_loc (setm (get_heap h extract_loc) ss x)) used_prk_loc (setm (get_heap h used_prk_loc) x tt)) count_loc <= q)%N.
                { rewrite (get_set_heap_neq _ _ _ _ Hne_cu) (get_set_heap_neq _ _ _ _ Hne_ce2) get_set_heap_eq.
                  exact: Hcnt2. }
                have Hne_be : bad_loc.1 != extract_loc.1 := isT.
                have Hne_bu : bad_loc.1 != used_prk_loc.1 := isT.
                have Hne_bc : bad_loc.1 != count_loc.1 := isT.
                have Hbad4 : get_heap (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1)
                         extract_loc (setm (get_heap h extract_loc) ss x)) used_prk_loc (setm (get_heap h used_prk_loc) x tt)) bad_loc = false.
                { rewrite (get_set_heap_neq _ _ _ _ Hne_bu) (get_set_heap_neq _ _ _ _ Hne_be) (get_set_heap_neq _ _ _ _ Hne_bc).
                  exact: (negbTE Hbadh). }
                have Hcount4' : (q - get_heap (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1)
                         extract_loc (setm (get_heap h extract_loc) ss x)) used_prk_loc (setm (get_heap h used_prk_loc) x tt)) count_loc
                  = (q - get_heap h count_loc).-1)%N.
                { rewrite (get_set_heap_neq _ _ _ _ Hne_cu) (get_set_heap_neq _ _ _ _ Hne_ce2) get_set_heap_eq.
                  rewrite subnS. reflexivity. }
                rewrite Pr_code_get.
                case: (get_heap (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1)
                         extract_loc (setm (get_heap h extract_loc) ss x)) used_prk_loc (setm (get_heap h used_prk_loc) x tt)) mid_loc (x, info)) => [y|] /=.
                { apply: (le_trans (IH y (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1)
                         extract_loc (setm (get_heap h extract_loc) ss x)) used_prk_loc (setm (get_heap h used_prk_loc) x tt))
                    Hcorr4 Hinj4 Hcount4)).
                  rewrite Hbad4 /= Hcount4' get_set_heap_eq GRing.add0r.
                  have -> : #|domm (setm (get_heap h used_prk_loc) x tt)| = #|[set x0 in domm (get_heap h used_prk_loc)]|.+1.
                  { by rewrite Hdommcard Hcardeq. }
                  exact: lexx. }
                { rewrite Pr_code_sample __deprecated__pr_dlet.
                  apply: exp_le_bd.
                  { rewrite GRing.add0r; exact: bad_bound_ge0. }
                  { move=> y.
                    rewrite Pr_code_put.
                    have Hne_em : extract_loc.1 != mid_loc.1 := isT.
                    have Hne_um : used_prk_loc.1 != mid_loc.1 := isT.
                    have Hne_bm : bad_loc.1 != mid_loc.1 := isT.
                    have Hne_cm : count_loc.1 != mid_loc.1 := isT.
                    have Hge0 : 0 <= \P_[Pr_code (code_link (k y) (COUNT q ∘ KDF_mid'))
                        (set_heap (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1)
                             extract_loc (setm (get_heap h extract_loc) ss x)) used_prk_loc (setm (get_heap h used_prk_loc) x tt))
                           mid_loc (setm (get_heap (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1)
                             extract_loc (setm (get_heap h extract_loc) ss x)) used_prk_loc (setm (get_heap h used_prk_loc) x tt)) mid_loc) (x, info) y))]
                      (fun '(_, h') => get_heap h' bad_loc) := ge0_pr _ _.
                    rewrite (ger0_norm Hge0).
                    have Hcorr5 : used_prk_correspondence
                        (get_heap (set_heap (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1)
                             extract_loc (setm (get_heap h extract_loc) ss x)) used_prk_loc (setm (get_heap h used_prk_loc) x tt))
                           mid_loc (setm (get_heap (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1)
                             extract_loc (setm (get_heap h extract_loc) ss x)) used_prk_loc (setm (get_heap h used_prk_loc) x tt)) mid_loc) (x, info) y)) extract_loc)
                        (get_heap (set_heap (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1)
                             extract_loc (setm (get_heap h extract_loc) ss x)) used_prk_loc (setm (get_heap h used_prk_loc) x tt))
                           mid_loc (setm (get_heap (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1)
                             extract_loc (setm (get_heap h extract_loc) ss x)) used_prk_loc (setm (get_heap h used_prk_loc) x tt)) mid_loc) (x, info) y)) used_prk_loc).
                    { rewrite (get_set_heap_neq _ _ _ _ Hne_em) (get_set_heap_neq _ _ _ _ Hne_um).
                      exact: Hcorr4. }
                    have Hinj5 : extract_injective
                        (get_heap (set_heap (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1)
                             extract_loc (setm (get_heap h extract_loc) ss x)) used_prk_loc (setm (get_heap h used_prk_loc) x tt))
                           mid_loc (setm (get_heap (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1)
                             extract_loc (setm (get_heap h extract_loc) ss x)) used_prk_loc (setm (get_heap h used_prk_loc) x tt)) mid_loc) (x, info) y)) extract_loc).
                    { rewrite (get_set_heap_neq _ _ _ _ Hne_em). exact: Hinj4. }
                    have Hcount5 : (get_heap (set_heap (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1)
                             extract_loc (setm (get_heap h extract_loc) ss x)) used_prk_loc (setm (get_heap h used_prk_loc) x tt))
                           mid_loc (setm (get_heap (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1)
                             extract_loc (setm (get_heap h extract_loc) ss x)) used_prk_loc (setm (get_heap h used_prk_loc) x tt)) mid_loc) (x, info) y)) count_loc <= q)%N.
                    { rewrite (get_set_heap_neq _ _ _ _ Hne_cm). exact: Hcount4. }
                    have Hbad5 : get_heap (set_heap (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1)
                             extract_loc (setm (get_heap h extract_loc) ss x)) used_prk_loc (setm (get_heap h used_prk_loc) x tt))
                           mid_loc (setm (get_heap (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1)
                             extract_loc (setm (get_heap h extract_loc) ss x)) used_prk_loc (setm (get_heap h used_prk_loc) x tt)) mid_loc) (x, info) y)) bad_loc = false.
                    { rewrite (get_set_heap_neq _ _ _ _ Hne_bm). exact: Hbad4. }
                    apply: (le_trans (IH y _ Hcorr5 Hinj5 Hcount5)).
                    rewrite Hbad5 /=.
                    rewrite (get_set_heap_neq _ _ _ _ Hne_cm) Hcount4' GRing.add0r.
                    rewrite (get_set_heap_neq _ _ _ _ Hne_um) get_set_heap_eq Hdommcard Hcardeq.
                    exact: lexx. } } } } } } }
      { (* count >= q: dummy branch, independent of any tracked state *)
        rewrite Pr_code_sample __deprecated__pr_dlet.
        apply: exp_le_bd.
        { case: (get_heap h bad_loc); [exact: ler01 | exact: bad_bound_ge0]. }
        { move=> a.
          have Hge0a : 0 <= \P_[Pr_code (code_link (k a) (COUNT q ∘ KDF_mid')) h]
            (fun '(_, h') => get_heap h' bad_loc) := ge0_pr _ _.
          rewrite (ger0_norm Hge0a).
          exact: (IH a h Hcorr Hinj Hcount). } }
    - (* getr: adversary's own state, read-only, heap unchanged *)
      rewrite /= Pr_code_get.
      exact: (IH (get_heap h l) h Hcorr Hinj Hcount).
    - (* putr: adversary's own state, disjoint from everything we track *)
      rewrite /= Pr_code_put.
      have Hne_e : extract_loc.1 != l.1 := loc_neq_of_separate l extract_loc fhas_extract_KDF_mid' Hsep1 Hl.
      have Hne_u : used_prk_loc.1 != l.1 := loc_neq_of_separate l used_prk_loc fhas_used_prk_KDF_mid' Hsep1 Hl.
      have Hne_b : bad_loc.1 != l.1 := loc_neq_of_separate l bad_loc fhas_bad_KDF_mid' Hsep1 Hl.
      have Hne_c : count_loc.1 != l.1 := loc_neq_of_separate l count_loc fhas_count_loc_self Hsep2 Hl.
      have Hcorr' : used_prk_correspondence
        (get_heap (set_heap h l v) extract_loc) (get_heap (set_heap h l v) used_prk_loc).
      { rewrite (get_set_heap_neq h l v extract_loc Hne_e) (get_set_heap_neq h l v used_prk_loc Hne_u).
        exact: Hcorr. }
      have Hinj' : extract_injective (get_heap (set_heap h l v) extract_loc).
      { rewrite (get_set_heap_neq h l v extract_loc Hne_e). exact: Hinj. }
      have Hcount' : (get_heap (set_heap h l v) count_loc <= q)%N.
      { rewrite (get_set_heap_neq h l v count_loc Hne_c). exact: Hcount. }
      rewrite -(get_set_heap_neq h l v bad_loc Hne_b).
      rewrite -(get_set_heap_neq h l v count_loc Hne_c).
      rewrite -(get_set_heap_neq h l v used_prk_loc Hne_u).
      exact: (IHIH (set_heap h l v) Hcorr' Hinj' Hcount').
    - (* sampler: adversary's own randomness, heap unchanged, same bound
        for every outcome *)
      rewrite /= Pr_code_sample __deprecated__pr_dlet.
      apply: exp_le_bd.
      + case: (boolP (get_heap h bad_loc)) => Hb /=.
        * exact: ler01.
        * exact: bad_bound_ge0.
      + move=> y.
        have Hge0 : 0 <= \P_[Pr_code (code_link (k y) (COUNT q ∘ KDF_mid')) h]
          (fun '(_, h') => get_heap h' bad_loc) := ge0_pr _ _.
        rewrite (ger0_norm Hge0).
        exact: (IH y h Hcorr Hinj Hcount).
  Qed.

  (** THE final connective step, now [Qed]'d: [KDF_mid'] and [KDF_bad]
    track the same ghost state ([extract_loc]/[used_prk_loc]/[bad_loc]):
    every FRESH [ss] (one not yet in [extract_loc]'s domain) draws a
    [prk] uniformly from a space of size [PRK_N] and sets [bad_loc] the
    moment that [prk] collides with one already in [used_prk_loc] --
    i.e. [extract_loc]'s domain/[used_prk_loc] play EXACTLY the role of
    [Birthday.v]'s [bad_dist]'s "used" set, one step of [bad_dist] per
    fresh [ss]. A REPEAT [ss] query costs no fresh sample at all (see
    [KDF_mid']'s own definition above), so the number of fresh-sampling
    steps taken along any run is bounded by the number of queries
    [COUNT q] actually routes through to [KDF_mid'], i.e. by [q] (repeat
    queries only make this bound slacker).

    This informal correspondence is formalised by [Pr_bad_adv_bound]
    above: a coupling/domination argument, by induction on the
    ADVERSARY's own code (mirroring [pkg_upto_bad.v]'s own
    [eq_up_to_bad_adversary_link]/[bad_preserved_link] recursion over
    [code_link], the same technique [KDF_mid'_KDF_bad_eq_up_to_bad]
    above already uses per-call), carrying the current heap and
    bounding [Pr[bad_loc ends true]] by [Birthday.bad_bound]'s own
    shape read off [count_loc]/[used_prk_loc] -- a per-step union-bound
    argument ([expectation_le_bad_bound], [Birthday.v]) interleaved with
    the adversary-code induction (rather than [bad_dist_bound]'s own
    induction on a fixed, static query count). Instantiating
    [Pr_bad_adv_bound] at [empty_heap] (so [count_loc = 0] and
    [used_prk_loc] is empty) and closing with the trivial arithmetic
    [bad_bound_le_birthday_bound] (i.e. [bad_bound q 0 <= birthday_bound
    q]) gives exactly the bound below. *)
  Lemma Pr_bad_COUNT_KDF_mid'_bound LA A q :
    ValidPackage LA DERIVE_export A_export A →
    fseparate LA KDF_mid'_bad_locs →
    fseparate LA [fmap count_loc] →
    lossless_valid_adv LA DERIVE_export (resolve A RUN tt) →
    Pr_bad ((A ∘ COUNT q) ∘ KDF_mid') 4 true <= birthday_bound q.
  Proof.
    intros vA d1 d2 Hlva.
    have [d1a d1b] := fseparate_split_r LA KDF_mid'_locs KDF_bad_locs d1.
    rewrite /Pr_bad /Pr_op.
    rewrite resolve_link.
    rewrite resolve_link.
    rewrite code_link_assoc.
    rewrite /SDistr_bind /SDistr_unit dletE.
    have -> : psum
      (fun x : tgt RUN * heap =>
         Pr_code (code_link (resolve A RUN tt) (COUNT q ∘ KDF_mid')) empty_heap x *
         (let '(_, s) := x in dunit (T:=pkg_upto_bad.bad_loc 4) (get_heap s (pkg_upto_bad.bad_loc 4))) true)
      = \P_[Pr_code (code_link (resolve A RUN tt) (COUNT q ∘ KDF_mid')) empty_heap] (fun x => get_heap x.2 bad_loc).
    { rewrite /pr.
      apply: eq_psum => x.
      case: x => x1 x2 /=.
      rewrite dunit1E.
      rewrite eqb_id.
      exact: GRing.mulrC. }
    have Hcorr0 : used_prk_correspondence (get_heap empty_heap extract_loc) (get_heap empty_heap used_prk_loc).
    { move=> prk0.
      rewrite get_empty_heap /heap_init /=.
      split=>//.
      move=> [ss0].
      by rewrite get_empty_heap. }
    have Hinj0 : extract_injective (get_heap empty_heap extract_loc).
    { move=> ss1 ss2 prk0.
      rewrite get_empty_heap /heap_init /=.
      done. }
    have Hcount0 : (get_heap empty_heap count_loc <= q)%N.
    { by rewrite get_empty_heap. }
    have Hstep := Pr_bad_adv_bound (resolve A RUN tt) q Hlva d1a d2 empty_heap Hcorr0 Hinj0 Hcount0.
    have Heq : \P_[Pr_code (code_link (resolve A RUN tt) (COUNT q ∘ KDF_mid')) empty_heap]
        (fun x => get_heap x.2 bad_loc)
      = \P_[Pr_code (code_link (resolve A RUN tt) (COUNT q ∘ KDF_mid')) empty_heap]
        (fun '(_, h') => get_heap h' bad_loc).
    { rewrite /pr.
      apply: eq_psum => x.
      by case: x => x1 x2 /=. }
    rewrite Heq.
    apply: (le_trans Hstep).
    rewrite get_empty_heap /=.
    rewrite (get_empty_heap used_prk_loc) /heap_init /=.
    rewrite -cardsE domm0.
    have -> : [set x : fin_family PRK_N | x \in fset0] = set0.
    { apply/setP => y.
      rewrite in_set.
      reflexivity. }
    rewrite cards0.
    rewrite /heap_init subn0.
    exact: bad_bound_le_birthday_bound.
  Qed.

  (* --- per-hop counting lemma, mirror of [Pr_bad_adv_bound]/
    [Pr_bad_COUNT_KDF_mid'_bound] for [KDF_hybE_bad i] in place of
    [KDF_mid'] --- *)

  (* Isolated [fhas] micro-lemmas for [KDF_hybE_bad_locs], for the same
    reason as [fhas_extract_KDF_mid']/[fhas_used_prk_KDF_mid']/
    [fhas_bad_KDF_mid'] above: proving these inline via [fmap_solve]
    inside [Pr_bad_adv_bound_hybE]'s own putr cases, alongside several
    OTHER nontrivial [have]s in the same proof context, was observed
    (for the structurally analogous [KDF_mid'] argument) to blow up
    [fmap_solve]'s search; pre-proving them in isolation sidesteps that
    entirely. *)
  Lemma fhas_extract_hybE : fhas KDF_hybE_bad_locs extract_loc.
  Proof. fmap_solve. Qed.

  Lemma fhas_used_prk_hybE : fhas KDF_hybE_bad_locs used_prk_loc.
  Proof. fmap_solve. Qed.

  Lemma fhas_bad_hybE : fhas KDF_hybE_bad_locs bad_loc.
  Proof. fmap_solve. Qed.

  Lemma fhas_mid_hybE : fhas KDF_hybE_bad_locs mid_loc.
  Proof. fmap_solve. Qed.

  Lemma fhas_ss_count_hybE : fhas KDF_hybE_bad_locs ss_count_loc.
  Proof. fmap_solve. Qed.

  Lemma fhas_ss_index_hybE : fhas KDF_hybE_bad_locs ss_index_loc.
  Proof. fmap_solve. Qed.

  Lemma fhas_eval_tbl_hybE : fhas KDF_hybE_bad_locs eval_tbl_loc.
  Proof. fmap_solve. Qed.

  (* Mirror of [Pr_bad_adv_bound], with [KDF_hybE_bad i] in place of
    [KDF_mid']: the walk through the oracle body now steps over
    [get_ss_idx]'s ss_count/ss_index bookkeeping (which the tracked
    facts commute past) and splits three ways on the hybrid index, but
    every branch contains the SAME single [get_prk_bad] fresh-sample
    step driving the same Birthday.bad_bound accounting. *)
  Lemma Pr_bad_adv_bound_hybE {LA : Locations} {B : choiceType}
    (i : nat) (Ac : raw_code B) (q : nat)
    (Hlva : lossless_valid_adv LA DERIVE_export Ac)
    (Hsep1 : fseparate LA KDF_hybE_bad_locs)
    (Hsep2 : fseparate LA [fmap count_loc]) :
    forall h : heap,
      used_prk_correspondence (get_heap h extract_loc) (get_heap h used_prk_loc) →
      extract_injective (get_heap h extract_loc) →
      (get_heap h count_loc <= q)%N →
      \P_[ Pr_code (code_link Ac (COUNT q ∘ KDF_hybE_bad i)) h ]
        (fun '(_, h') => get_heap h' bad_loc)
      <= (if get_heap h bad_loc then 1
          else Birthday.bad_bound (fin_family PRK_N) (q - get_heap h count_loc)
                 #|domm (get_heap h used_prk_loc)|).
  Proof.
    induction Hlva as [x0 | o x k Ho k' IH | l k Hl k' IH | l v k Hl IH | op k Hop k' IH];
      move=> h Hcorr Hinj Hcount.
    - (* ret *)
      rewrite /= Pr_code_ret pr_dunit /=.
      case: (boolP (get_heap h bad_loc)) => Hb /=.
      + exact: lexx.
      + exact: bad_bound_ge0.
    - (* opr: the one real DERIVE call *)
      fmap_invert Ho.
      case: x => ss info /=.
      simplify_linking.
      have Hmid : forall (h' : heap) (prk : 'prk),
          used_prk_correspondence (get_heap h' extract_loc) (get_heap h' used_prk_loc) ->
          extract_injective (get_heap h' extract_loc) ->
          (get_heap h' count_loc <= q)%N ->
          \P_[Pr_code (T2 ← get mid_loc ;;
                       y ← match T2 (prk, info) with
                           | Some y0 => ret y0
                           | None => y0 ← sample uniform Out_N ;; #put mid_loc := setm T2 (prk, info) y0 ;; ret y0
                           end ;;
                       code_link (k y) (COUNT q ∘ KDF_hybE_bad i)) h']
            (fun '(_, h'') => get_heap h'' bad_loc) <=
            (if get_heap h' bad_loc then 1
             else bad_bound (fin_family PRK_N) (q - get_heap h' count_loc) #|domm (get_heap h' used_prk_loc)|).
      { move=> h' prk Hcorr' Hinj' Hcount'.
        rewrite Pr_code_get.
        case: (get_heap h' mid_loc (prk, info)) => [y|] /=.
        { exact: (IH y h' Hcorr' Hinj' Hcount'). }
        { rewrite Pr_code_sample __deprecated__pr_dlet.
          apply: exp_le_bd.
          { case: (get_heap h' bad_loc); [exact: ler01 | exact: bad_bound_ge0]. }
          { move=> y.
            rewrite Pr_code_put.
            have Hne_e2 : extract_loc.1 != mid_loc.1 := isT.
            have Hne_u2 : used_prk_loc.1 != mid_loc.1 := isT.
            have Hne_b2 : bad_loc.1 != mid_loc.1 := isT.
            have Hne_c2 : count_loc.1 != mid_loc.1 := isT.
            have Hge0 : 0 <= \P_[Pr_code (code_link (k y) (COUNT q ∘ KDF_hybE_bad i))
                (set_heap h' mid_loc (setm (get_heap h' mid_loc) (prk, info) y))]
              (fun '(_, h'') => get_heap h'' bad_loc) := ge0_pr _ _.
            rewrite (ger0_norm Hge0).
            have Hcorr2 : used_prk_correspondence
                (get_heap (set_heap h' mid_loc (setm (get_heap h' mid_loc) (prk, info) y)) extract_loc)
                (get_heap (set_heap h' mid_loc (setm (get_heap h' mid_loc) (prk, info) y)) used_prk_loc).
            { rewrite (get_set_heap_neq _ _ _ _ Hne_e2) (get_set_heap_neq _ _ _ _ Hne_u2). exact: Hcorr'. }
            have Hinj2 : extract_injective
                (get_heap (set_heap h' mid_loc (setm (get_heap h' mid_loc) (prk, info) y)) extract_loc).
            { rewrite (get_set_heap_neq _ _ _ _ Hne_e2). exact: Hinj'. }
            have Hcount2 : (get_heap (set_heap h' mid_loc (setm (get_heap h' mid_loc) (prk, info) y)) count_loc <= q)%N.
            { rewrite (get_set_heap_neq _ _ _ _ Hne_c2). exact: Hcount'. }
            have Hbound2 :
              (if get_heap (set_heap h' mid_loc (setm (get_heap h' mid_loc) (prk, info) y)) bad_loc then 1
               else bad_bound (fin_family PRK_N)
                      (q - get_heap (set_heap h' mid_loc (setm (get_heap h' mid_loc) (prk, info) y)) count_loc)
                      #|domm (get_heap (set_heap h' mid_loc (setm (get_heap h' mid_loc) (prk, info) y)) used_prk_loc)|)
              <= (if get_heap h' bad_loc then 1
                  else bad_bound (fin_family PRK_N) (q - get_heap h' count_loc) #|domm (get_heap h' used_prk_loc)|).
            { rewrite (get_set_heap_neq _ _ _ _ Hne_b2) (get_set_heap_neq _ _ _ _ Hne_c2) (get_set_heap_neq _ _ _ _ Hne_u2).
              exact: lexx. }
            apply: (le_trans (IH y _ Hcorr2 Hinj2 Hcount2)).
            exact: Hbound2. } } }
      have Heval : forall (h' : heap),
          used_prk_correspondence (get_heap h' extract_loc) (get_heap h' used_prk_loc) ->
          extract_injective (get_heap h' extract_loc) ->
          (get_heap h' count_loc <= q)%N ->
          \P_[Pr_code (T ← get eval_tbl_loc ;;
                       y ← match T info with
                           | Some y0 => ret y0
                           | None => y0 ← sample uniform Out_N ;; #put eval_tbl_loc := setm T info y0 ;; ret y0
                           end ;;
                       code_link (k y) (COUNT q ∘ KDF_hybE_bad i)) h']
            (fun '(_, h'') => get_heap h'' bad_loc) <=
            (if get_heap h' bad_loc then 1
             else bad_bound (fin_family PRK_N) (q - get_heap h' count_loc) #|domm (get_heap h' used_prk_loc)|).
      { move=> h' Hcorr' Hinj' Hcount'.
        rewrite Pr_code_get.
        case: (get_heap h' eval_tbl_loc info) => [y|] /=.
        { exact: (IH y h' Hcorr' Hinj' Hcount'). }
        { rewrite Pr_code_sample __deprecated__pr_dlet.
          apply: exp_le_bd.
          { case: (get_heap h' bad_loc); [exact: ler01 | exact: bad_bound_ge0]. }
          { move=> y.
            rewrite Pr_code_put.
            have Hne_e2 : extract_loc.1 != eval_tbl_loc.1 := isT.
            have Hne_u2 : used_prk_loc.1 != eval_tbl_loc.1 := isT.
            have Hne_b2 : bad_loc.1 != eval_tbl_loc.1 := isT.
            have Hne_c2 : count_loc.1 != eval_tbl_loc.1 := isT.
            have Hge0 : 0 <= \P_[Pr_code (code_link (k y) (COUNT q ∘ KDF_hybE_bad i))
                (set_heap h' eval_tbl_loc (setm (get_heap h' eval_tbl_loc) info y))]
              (fun '(_, h'') => get_heap h'' bad_loc) := ge0_pr _ _.
            rewrite (ger0_norm Hge0).
            have Hcorr2 : used_prk_correspondence
                (get_heap (set_heap h' eval_tbl_loc (setm (get_heap h' eval_tbl_loc) info y)) extract_loc)
                (get_heap (set_heap h' eval_tbl_loc (setm (get_heap h' eval_tbl_loc) info y)) used_prk_loc).
            { rewrite (get_set_heap_neq _ _ _ _ Hne_e2) (get_set_heap_neq _ _ _ _ Hne_u2). exact: Hcorr'. }
            have Hinj2 : extract_injective
                (get_heap (set_heap h' eval_tbl_loc (setm (get_heap h' eval_tbl_loc) info y)) extract_loc).
            { rewrite (get_set_heap_neq _ _ _ _ Hne_e2). exact: Hinj'. }
            have Hcount2 : (get_heap (set_heap h' eval_tbl_loc (setm (get_heap h' eval_tbl_loc) info y)) count_loc <= q)%N.
            { rewrite (get_set_heap_neq _ _ _ _ Hne_c2). exact: Hcount'. }
            have Hbound2 :
              (if get_heap (set_heap h' eval_tbl_loc (setm (get_heap h' eval_tbl_loc) info y)) bad_loc then 1
               else bad_bound (fin_family PRK_N)
                      (q - get_heap (set_heap h' eval_tbl_loc (setm (get_heap h' eval_tbl_loc) info y)) count_loc)
                      #|domm (get_heap (set_heap h' eval_tbl_loc (setm (get_heap h' eval_tbl_loc) info y)) used_prk_loc)|)
              <= (if get_heap h' bad_loc then 1
                  else bad_bound (fin_family PRK_N) (q - get_heap h' count_loc) #|domm (get_heap h' used_prk_loc)|).
            { rewrite (get_set_heap_neq _ _ _ _ Hne_b2) (get_set_heap_neq _ _ _ _ Hne_c2) (get_set_heap_neq _ _ _ _ Hne_u2).
              exact: lexx. }
            apply: (le_trans (IH y _ Hcorr2 Hinj2 Hcount2)).
            exact: Hbound2. } } }
      have Hprk : forall (hs : heap) (c : nat) (Krest : 'prk -> raw_code B),
          get_heap hs count_loc = c.+1 ->
          (c < q)%N ->
          used_prk_correspondence (get_heap hs extract_loc) (get_heap hs used_prk_loc) ->
          extract_injective (get_heap hs extract_loc) ->
          (forall (prk : 'prk) (h'' : heap),
             used_prk_correspondence (get_heap h'' extract_loc) (get_heap h'' used_prk_loc) ->
             extract_injective (get_heap h'' extract_loc) ->
             (get_heap h'' count_loc <= q)%N ->
             \P_[Pr_code (Krest prk) h''] (fun '(_, hh) => get_heap hh bad_loc) <=
               (if get_heap h'' bad_loc then 1
                else bad_bound (fin_family PRK_N) (q - get_heap h'' count_loc) #|domm (get_heap h'' used_prk_loc)|)) ->
          \P_[Pr_code
              (v ← get extract_loc ;;
               prk ← match v ss with
                     | Some prk => ret prk
                     | None =>
                         prk ← sample uniform PRK_N ;;
                         #put extract_loc := setm v ss prk ;;
                         Used ← get used_prk_loc ;;
                         match Used prk with
                         | Some _ => #put bad_loc := true ;; ret prk
                         | None => #put used_prk_loc := setm Used prk tt ;; ret prk
                         end
                     end ;;
               Krest prk) hs]
            (fun '(_, hh) => get_heap hh bad_loc) <=
            (if get_heap hs bad_loc then 1
             else bad_bound (fin_family PRK_N) (q - c) #|domm (get_heap hs used_prk_loc)|).
      { move=> hs c Krest Hhc Hltc Hcorr' Hinj' Htail.
        have Hcard : (0 < #|fin_family PRK_N|)%N.
        { rewrite card_fin_family_PRK_N. exact: PRK_N_gt0. }
        rewrite Pr_code_get.
        case Heqx : (get_heap hs extract_loc ss) => [prk|] /=.
        { have Hle1 : (get_heap hs count_loc <= q)%N.
          { rewrite Hhc. exact: Hltc. }
          apply: (le_trans (Htail prk hs Hcorr' Hinj' Hle1)).
          rewrite Hhc.
          case: (get_heap hs bad_loc) => //.
          apply: (bad_bound_mono_q (fin_family PRK_N) Hcard).
          exact: (leq_sub2l q (leqnSn c)). }
        { case: (boolP (get_heap hs bad_loc)) => Hbadh.
          { exact: le1_pr. }
          { rewrite Pr_code_sample __deprecated__pr_dlet.
            have Hgt0 : (0 < q - c)%N.
            { by rewrite subn_gt0. }
            have HcntQ : (q - c = (q - c).-1.+1)%N.
            { by rewrite (prednK Hgt0). }
            rewrite HcntQ.
            have Htest : (uniform PRK_N).π2 = Birthday.unif_F (fin_family PRK_N) := erefl.
            rewrite Htest.
            have Hcardeq : #|[set x0 : fin_family PRK_N | x0 \in domm (get_heap hs used_prk_loc)]|
                         = #|domm (get_heap hs used_prk_loc)|.
            { by rewrite cardsE. }
            rewrite -Hcardeq.
            apply: (expectation_le_bad_bound (fin_family PRK_N) Hcard
              (q - c).-1
              [set x0 : fin_family PRK_N | x0 \in domm (get_heap hs used_prk_loc)]).
            { move=> x. exact: ge0_pr. }
            { move=> x.
              rewrite Pr_code_put.
              rewrite in_set.
              rewrite Pr_code_get.
              have Hne_u3 : used_prk_loc.1 != extract_loc.1 := isT.
              rewrite (get_set_heap_neq _ _ _ _ Hne_u3).
              case: (boolP (x \in domm (get_heap hs used_prk_loc))) => Hxused.
              { have [[] Hget] := dommP Hxused.
                rewrite Hget /=.
                apply: (le_trans (y := 1)); [exact: le1_pr | rewrite lerDl; exact: bad_bound_ge0]. }
              { have Hget2 : get_heap hs used_prk_loc x = None.
                { apply/dommPn. exact: Hxused. }
                rewrite Hget2 /=.
                rewrite Pr_code_put.
                have Hfresh : forall ss', get_heap hs extract_loc ss' <> Some x.
                { move=> ss' Heq.
                  have Hex : exists ss0, get_heap hs extract_loc ss0 = Some x := ex_intro _ ss' Heq.
                  have := (proj2 (Hcorr' x) Hex).
                  rewrite Hget2. discriminate. }
                have Hinj3 : extract_injective (setm (get_heap hs extract_loc) ss x).
                { move=> ss1 ss2 prk0 H1 H2.
                  case: (eqVneq ss1 ss) => Heq1; case: (eqVneq ss2 ss) => Heq2.
                  - by rewrite Heq1 Heq2.
                  - subst ss1. move: H1. rewrite setmE eqxx => [[Heqx0]].
                    move: H2. rewrite setmE (negbTE Heq2) => H2. subst prk0.
                    exfalso. exact: (Hfresh ss2 H2).
                  - subst ss2. move: H2. rewrite setmE eqxx => [[Heqx0]].
                    move: H1. rewrite setmE (negbTE Heq1) => H1. subst prk0.
                    exfalso. exact: (Hfresh ss1 H1).
                  - move: H1 H2. rewrite setmE (negbTE Heq1) setmE (negbTE Heq2) => H1 H2.
                    exact: (Hinj' ss1 ss2 prk0 H1 H2). }
                have Hcorr3 : used_prk_correspondence
                    (setm (get_heap hs extract_loc) ss x) (setm (get_heap hs used_prk_loc) x tt).
                { move=> prk0. case: (eqVneq prk0 x) => Heqp.
                  - subst prk0. rewrite setmE eqxx. split.
                    + move=> _. by exists ss; rewrite setmE eqxx.
                    + move=> _. reflexivity.
                  - rewrite setmE (negbTE Heqp). split.
                    + move=> HU. have [ss0 Hss0] := (proj1 (Hcorr' prk0) HU).
                      exists ss0. rewrite setmE.
                      case: (eqVneq ss0 ss) => Hss.
                      * subst ss0. rewrite Hss0 in Heqx. discriminate.
                      * exact: Hss0.
                    + move=> [ss0 Hss0]. move: Hss0. rewrite setmE.
                      case: (eqVneq ss0 ss) => Hss.
                      * move=> [] Heq0. move: Heqp => /eqP Heqp. exfalso. apply: Heqp. by rewrite -Heq0.
                      * move=> Hss0. apply: (proj2 (Hcorr' prk0)). by exists ss0. }
                have Hdommcard : #|domm (setm (get_heap hs used_prk_loc) x tt)| = (#|domm (get_heap hs used_prk_loc)|).+1.
                { have Heq1' : [set y : fin_family PRK_N | y \in x |: domm (get_heap hs used_prk_loc)]
                             = (x |: [set y : fin_family PRK_N | y \in domm (get_heap hs used_prk_loc)])%SET.
                  { apply/setP => y.
                    rewrite in_set in_fsetU1.
                    rewrite in_setU1 in_set.
                    reflexivity. }
                  rewrite domm_set.
                  rewrite -cardsE Heq1' cardsU1.
                  rewrite in_set (negbTE Hxused) add1n.
                  by rewrite cardsE. }
                have Hne_eu : extract_loc.1 != used_prk_loc.1 := isT.
                have Hcorr4 : used_prk_correspondence
                    (get_heap (set_heap (set_heap hs extract_loc (setm (get_heap hs extract_loc) ss x)) used_prk_loc (setm (get_heap hs used_prk_loc) x tt)) extract_loc)
                    (get_heap (set_heap (set_heap hs extract_loc (setm (get_heap hs extract_loc) ss x)) used_prk_loc (setm (get_heap hs used_prk_loc) x tt)) used_prk_loc).
                { rewrite (get_set_heap_neq _ _ _ _ Hne_eu) get_set_heap_eq get_set_heap_eq.
                  exact: Hcorr3. }
                have Hinj4 : extract_injective
                    (get_heap (set_heap (set_heap hs extract_loc (setm (get_heap hs extract_loc) ss x)) used_prk_loc (setm (get_heap hs used_prk_loc) x tt)) extract_loc).
                { rewrite (get_set_heap_neq _ _ _ _ Hne_eu) get_set_heap_eq.
                  exact: Hinj3. }
                have Hne_ce2 : count_loc.1 != extract_loc.1 := isT.
                have Hne_cu : count_loc.1 != used_prk_loc.1 := isT.
                have Hcount4 : (get_heap (set_heap (set_heap hs extract_loc (setm (get_heap hs extract_loc) ss x)) used_prk_loc (setm (get_heap hs used_prk_loc) x tt)) count_loc <= q)%N.
                { rewrite (get_set_heap_neq _ _ _ _ Hne_cu) (get_set_heap_neq _ _ _ _ Hne_ce2).
                  rewrite Hhc. exact: Hltc. }
                have Hne_be : bad_loc.1 != extract_loc.1 := isT.
                have Hne_bu : bad_loc.1 != used_prk_loc.1 := isT.
                have Hbad4 : get_heap (set_heap (set_heap hs extract_loc (setm (get_heap hs extract_loc) ss x)) used_prk_loc (setm (get_heap hs used_prk_loc) x tt)) bad_loc = false.
                { rewrite (get_set_heap_neq _ _ _ _ Hne_bu) (get_set_heap_neq _ _ _ _ Hne_be).
                  exact: (negbTE Hbadh). }
                have Hcount4' : (q - get_heap (set_heap (set_heap hs extract_loc (setm (get_heap hs extract_loc) ss x)) used_prk_loc (setm (get_heap hs used_prk_loc) x tt)) count_loc = (q - c).-1)%N.
                { rewrite (get_set_heap_neq _ _ _ _ Hne_cu) (get_set_heap_neq _ _ _ _ Hne_ce2) Hhc.
                  rewrite subnS. reflexivity. }
                apply: (le_trans (Htail x _ Hcorr4 Hinj4 Hcount4)).
                rewrite Hbad4 /= Hcount4' get_set_heap_eq GRing.add0r.
                have -> : #|domm (setm (get_heap hs used_prk_loc) x tt)| = #|[set x0 in domm (get_heap hs used_prk_loc)]|.+1.
                { by rewrite Hdommcard Hcardeq. }
                exact: lexx.
              } } } } }
      have Hthree : forall (idx : nat) (hs : heap) (c : nat),
          get_heap hs count_loc = c.+1 ->
          (c < q)%N ->
          used_prk_correspondence (get_heap hs extract_loc) (get_heap hs used_prk_loc) ->
          extract_injective (get_heap hs extract_loc) ->
          \P_[Pr_code
              (b ← (if (idx < i)%N then
                      v1 ← get extract_loc ;;
                      prk ← match v1 ss with
                            | Some prk => ret prk
                            | None =>
                                prk ← sample uniform PRK_N ;;
                                #put extract_loc := setm v1 ss prk ;;
                                Used ← get used_prk_loc ;;
                                match Used prk with
                                | Some _ => #put bad_loc := true ;; ret prk
                                | None => #put used_prk_loc := setm Used prk tt ;; ret prk
                                end
                            end ;;
                      T2 ← get mid_loc ;;
                      match T2 (prk, info) with
                      | Some y => ret y
                      | None => y ← sample uniform Out_N ;; #put mid_loc := setm T2 (prk, info) y ;; ret y
                      end
                    else if idx == i then
                      v1 ← get extract_loc ;;
                      prk ← match v1 ss with
                            | Some prk => ret prk
                            | None =>
                                prk ← sample uniform PRK_N ;;
                                #put extract_loc := setm v1 ss prk ;;
                                Used ← get used_prk_loc ;;
                                match Used prk with
                                | Some _ => #put bad_loc := true ;; ret prk
                                | None => #put used_prk_loc := setm Used prk tt ;; ret prk
                                end
                            end ;;
                      T ← get eval_tbl_loc ;;
                      match T info with
                      | Some y => ret y
                      | None => y ← sample uniform Out_N ;; #put eval_tbl_loc := setm T info y ;; ret y
                      end
                    else
                      v1 ← get extract_loc ;;
                      prk ← match v1 ss with
                            | Some prk => ret prk
                            | None =>
                                prk ← sample uniform PRK_N ;;
                                #put extract_loc := setm v1 ss prk ;;
                                Used ← get used_prk_loc ;;
                                match Used prk with
                                | Some _ => #put bad_loc := true ;; ret prk
                                | None => #put used_prk_loc := setm Used prk tt ;; ret prk
                                end
                            end ;;
                      ret (PRF info prk)) ;;
               code_link (k b) (COUNT q ∘ KDF_hybE_bad i)) hs]
            (fun '(_, hh) => get_heap hh bad_loc) <=
            (if get_heap hs bad_loc then 1
             else bad_bound (fin_family PRK_N) (q - c) #|domm (get_heap hs used_prk_loc)|).
      { move=> idx hs c Hhc Hltc Hcorr' Hinj'.
        case: ifP => Hlt /=.
        { repeat setoid_rewrite bind_assoc.
          apply: (Hprk hs c
            (fun prk => T2 ← get mid_loc ;;
                        y0 ← match T2 (prk, info) with
                             | Some y => ret y
                             | None => y ← sample uniform Out_N ;; #put mid_loc := setm T2 (prk, info) y ;; ret y
                             end ;;
                        code_link (k y0) (COUNT q ∘ KDF_hybE_bad i))
            Hhc Hltc Hcorr' Hinj').
          move=> prk h'' Ha Hb Hc0. exact: (Hmid h'' prk Ha Hb Hc0). }
        { case: ifP => Heqi /=.
          { repeat setoid_rewrite bind_assoc.
            apply: (Hprk hs c
              (fun prk => T ← get eval_tbl_loc ;;
                          y0 ← match T info with
                               | Some y => ret y
                               | None => y ← sample uniform Out_N ;; #put eval_tbl_loc := setm T info y ;; ret y
                               end ;;
                          code_link (k y0) (COUNT q ∘ KDF_hybE_bad i))
              Hhc Hltc Hcorr' Hinj').
            move=> prk h'' Ha Hb Hc0. exact: (Heval h'' Ha Hb Hc0). }
          { repeat setoid_rewrite bind_assoc.
            apply: (Hprk hs c
              (fun prk => code_link (k (PRF info prk)) (COUNT q ∘ KDF_hybE_bad i))
              Hhc Hltc Hcorr' Hinj').
            move=> prk h'' Ha Hb Hc0. exact: (IH (PRF info prk) h'' Ha Hb Hc0). } } }
      rewrite Pr_code_get.
      case: ifP => Hcnt2 /=.
      { rewrite Pr_code_put /=.
        rewrite bind_ret.
        simplify_linking.
        rewrite Pr_code_get.
        case Heqidx : (get_heap (set_heap h count_loc (get_heap h count_loc).+1) ss_index_loc ss) => [idx0|] /=.
        { have Hhc1 : get_heap (set_heap h count_loc (get_heap h count_loc).+1) count_loc = (get_heap h count_loc).+1.
          { exact: get_set_heap_eq. }
          have Hcorr1 : used_prk_correspondence
              (get_heap (set_heap h count_loc (get_heap h count_loc).+1) extract_loc)
              (get_heap (set_heap h count_loc (get_heap h count_loc).+1) used_prk_loc).
          { rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != count_loc.1))
                    (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != count_loc.1)).
            exact: Hcorr. }
          have Hinj1 : extract_injective (get_heap (set_heap h count_loc (get_heap h count_loc).+1) extract_loc).
          { rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != count_loc.1)). exact: Hinj. }
          apply: (le_trans (Hthree idx0 (set_heap h count_loc (get_heap h count_loc).+1) (get_heap h count_loc) Hhc1 Hcnt2 Hcorr1 Hinj1)).
          rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != count_loc.1))
                  (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != count_loc.1)).
          exact: lexx. }
        rewrite Pr_code_get.
        rewrite Pr_code_put.
        rewrite Pr_code_put.
        simpl.
        have Hhc2 : get_heap (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1) ss_count_loc
                        (get_heap (set_heap h count_loc (get_heap h count_loc).+1) ss_count_loc).+1)
                     ss_index_loc (setm (get_heap (set_heap h count_loc (get_heap h count_loc).+1) ss_index_loc) ss
                        (get_heap (set_heap h count_loc (get_heap h count_loc).+1) ss_count_loc))) count_loc
              = (get_heap h count_loc).+1.
        { rewrite (get_set_heap_neq _ _ _ _ (isT : count_loc.1 != ss_index_loc.1))
                  (get_set_heap_neq _ _ _ _ (isT : count_loc.1 != ss_count_loc.1))
                  get_set_heap_eq.
          reflexivity. }
        have Hcorr2 : used_prk_correspondence
            (get_heap (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1) ss_count_loc
                        (get_heap (set_heap h count_loc (get_heap h count_loc).+1) ss_count_loc).+1)
                     ss_index_loc (setm (get_heap (set_heap h count_loc (get_heap h count_loc).+1) ss_index_loc) ss
                        (get_heap (set_heap h count_loc (get_heap h count_loc).+1) ss_count_loc))) extract_loc)
            (get_heap (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1) ss_count_loc
                        (get_heap (set_heap h count_loc (get_heap h count_loc).+1) ss_count_loc).+1)
                     ss_index_loc (setm (get_heap (set_heap h count_loc (get_heap h count_loc).+1) ss_index_loc) ss
                        (get_heap (set_heap h count_loc (get_heap h count_loc).+1) ss_count_loc))) used_prk_loc).
        { rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_index_loc.1))
                  (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_count_loc.1))
                  (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != ss_index_loc.1))
                  (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != ss_count_loc.1)).
          rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != count_loc.1))
                  (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != count_loc.1)).
          exact: Hcorr. }
        have Hinj2 : extract_injective
            (get_heap (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1) ss_count_loc
                        (get_heap (set_heap h count_loc (get_heap h count_loc).+1) ss_count_loc).+1)
                     ss_index_loc (setm (get_heap (set_heap h count_loc (get_heap h count_loc).+1) ss_index_loc) ss
                        (get_heap (set_heap h count_loc (get_heap h count_loc).+1) ss_count_loc))) extract_loc).
        { rewrite (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_index_loc.1))
                  (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != ss_count_loc.1))
                  (get_set_heap_neq _ _ _ _ (isT : extract_loc.1 != count_loc.1)).
          exact: Hinj. }
        apply: (le_trans (Hthree (get_heap (set_heap h count_loc (get_heap h count_loc).+1) ss_count_loc)
            (set_heap (set_heap (set_heap h count_loc (get_heap h count_loc).+1) ss_count_loc
                        (get_heap (set_heap h count_loc (get_heap h count_loc).+1) ss_count_loc).+1)
                     ss_index_loc (setm (get_heap (set_heap h count_loc (get_heap h count_loc).+1) ss_index_loc) ss
                        (get_heap (set_heap h count_loc (get_heap h count_loc).+1) ss_count_loc)))
            (get_heap h count_loc) Hhc2 Hcnt2 Hcorr2 Hinj2)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != ss_index_loc.1))
                (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != ss_count_loc.1))
                (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != ss_index_loc.1))
                (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != ss_count_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != count_loc.1))
                (get_set_heap_neq _ _ _ _ (isT : used_prk_loc.1 != count_loc.1)).
        exact: lexx. }
      { rewrite Pr_code_sample __deprecated__pr_dlet.
        apply: exp_le_bd.
        { case: (get_heap h bad_loc); [exact: ler01 | exact: bad_bound_ge0]. }
        { move=> a.
          have Hge0a : 0 <= \P_[Pr_code (code_link (k a) (COUNT q ∘ KDF_hybE_bad i)) h]
            (fun '(_, h') => get_heap h' bad_loc) := ge0_pr _ _.
          rewrite (ger0_norm Hge0a).
          exact: (IH a h Hcorr Hinj Hcount). } }
    - (* getr: adversary's own state, read-only, heap unchanged *)
      rewrite /= Pr_code_get.
      exact: (IH (get_heap h l) h Hcorr Hinj Hcount).
    - (* putr: adversary's own state, disjoint from everything we track *)
      rewrite /= Pr_code_put.
      have Hne_e : extract_loc.1 != l.1 := loc_neq_of_separate l extract_loc fhas_extract_hybE Hsep1 Hl.
      have Hne_u : used_prk_loc.1 != l.1 := loc_neq_of_separate l used_prk_loc fhas_used_prk_hybE Hsep1 Hl.
      have Hne_b : bad_loc.1 != l.1 := loc_neq_of_separate l bad_loc fhas_bad_hybE Hsep1 Hl.
      have Hne_c : count_loc.1 != l.1 := loc_neq_of_separate l count_loc fhas_count_loc_self Hsep2 Hl.
      have Hcorr' : used_prk_correspondence
        (get_heap (set_heap h l v) extract_loc) (get_heap (set_heap h l v) used_prk_loc).
      { rewrite (get_set_heap_neq h l v extract_loc Hne_e) (get_set_heap_neq h l v used_prk_loc Hne_u).
        exact: Hcorr. }
      have Hinj' : extract_injective (get_heap (set_heap h l v) extract_loc).
      { rewrite (get_set_heap_neq h l v extract_loc Hne_e). exact: Hinj. }
      have Hcount' : (get_heap (set_heap h l v) count_loc <= q)%N.
      { rewrite (get_set_heap_neq h l v count_loc Hne_c). exact: Hcount. }
      rewrite -(get_set_heap_neq h l v bad_loc Hne_b).
      rewrite -(get_set_heap_neq h l v count_loc Hne_c).
      rewrite -(get_set_heap_neq h l v used_prk_loc Hne_u).
      exact: (IHIH (set_heap h l v) Hcorr' Hinj' Hcount').
    - (* sampler: adversary's own randomness, heap unchanged, same bound
        for every outcome *)
      rewrite /= Pr_code_sample __deprecated__pr_dlet.
      apply: exp_le_bd.
      + case: (boolP (get_heap h bad_loc)) => Hb /=.
        * exact: ler01.
        * exact: bad_bound_ge0.
      + move=> y.
        have Hge0 : 0 <= \P_[Pr_code (code_link (k y) (COUNT q ∘ KDF_hybE_bad i)) h]
          (fun '(_, h') => get_heap h' bad_loc) := ge0_pr _ _.
        rewrite (ger0_norm Hge0).
        exact: (IH y h Hcorr Hinj Hcount).
  Qed.

  Lemma Pr_bad_COUNT_KDF_hybE_bad_bound i LA A q :
    ValidPackage LA DERIVE_export A_export A →
    fseparate LA KDF_hybE_bad_locs →
    fseparate LA [fmap count_loc] →
    lossless_valid_adv LA DERIVE_export (resolve A RUN tt) →
    Pr_bad ((A ∘ COUNT q) ∘ KDF_hybE_bad i) 4 true <= birthday_bound q.
  Proof.
    intros vA d1 d2 Hlva.
    rewrite /Pr_bad /Pr_op.
    rewrite resolve_link.
    rewrite resolve_link.
    rewrite code_link_assoc.
    rewrite /SDistr_bind /SDistr_unit dletE.
    have -> : psum
      (fun x : tgt RUN * heap =>
         Pr_code (code_link (resolve A RUN tt) (COUNT q ∘ KDF_hybE_bad i)) empty_heap x *
         (let '(_, s) := x in dunit (T:=pkg_upto_bad.bad_loc 4) (get_heap s (pkg_upto_bad.bad_loc 4))) true)
      = \P_[Pr_code (code_link (resolve A RUN tt) (COUNT q ∘ KDF_hybE_bad i)) empty_heap] (fun x => get_heap x.2 bad_loc).
    { rewrite /pr.
      apply: eq_psum => x.
      case: x => x1 x2 /=.
      rewrite dunit1E.
      rewrite eqb_id.
      exact: GRing.mulrC. }
    have Hcorr0 : used_prk_correspondence (get_heap empty_heap extract_loc) (get_heap empty_heap used_prk_loc).
    { move=> prk0.
      rewrite get_empty_heap /heap_init /=.
      split=>//.
      move=> [ss0].
      by rewrite get_empty_heap. }
    have Hinj0 : extract_injective (get_heap empty_heap extract_loc).
    { move=> ss1 ss2 prk0.
      rewrite get_empty_heap /heap_init /=.
      done. }
    have Hcount0 : (get_heap empty_heap count_loc <= q)%N.
    { by rewrite get_empty_heap. }
    have Hstep := Pr_bad_adv_bound_hybE i (resolve A RUN tt) q Hlva d1 d2 empty_heap Hcorr0 Hinj0 Hcount0.
    have Heq : \P_[Pr_code (code_link (resolve A RUN tt) (COUNT q ∘ KDF_hybE_bad i)) empty_heap]
        (fun x => get_heap x.2 bad_loc)
      = \P_[Pr_code (code_link (resolve A RUN tt) (COUNT q ∘ KDF_hybE_bad i)) empty_heap]
        (fun '(_, h') => get_heap h' bad_loc).
    { rewrite /pr.
      apply: eq_psum => x.
      by case: x => x1 x2 /=. }
    rewrite Heq.
    apply: (le_trans Hstep).
    rewrite get_empty_heap /=.
    rewrite (get_empty_heap used_prk_loc) /heap_init /=.
    rewrite -cardsE domm0.
    have -> : [set x : fin_family PRK_N | x \in fset0] = set0.
    { apply/setP => y.
      rewrite in_set.
      reflexivity. }
    rewrite cards0.
    rewrite /heap_init subn0.
    exact: bad_bound_le_birthday_bound.
  Qed.

  (** Assembles the triangle [KDF_mid -- KDF_mid' -- KDF_bad -- KDF_ideal]
    (all composed with [COUNT q]): the two outer legs are EXACT
    ([COUNT_KDF_mid_KDF_mid'_bound]/[COUNT_KDF_bad_KDF_ideal_bound], cost
    0), and the middle leg is exactly [COUNT_KDF_mid'_KDF_bad_bound]
    followed by [Pr_bad_COUNT_KDF_mid'_bound] (once the one open gap in
    this file, now fully [Qed]'d via [Pr_bad_adv_bound] -- see its
    docstring immediately above). Every lemma feeding into this proof is
    fully [Qed]'d with 0 admits. *)
  Theorem KDF_mid_KDF_ideal_bound LA A q :
    ValidPackage LA DERIVE_export A_export A →
    fseparate LA KDF_mid_locs →
    fseparate LA KDF_ideal_locs →
    fseparate LA KDF_mid'_bad_locs →
    fseparate LA [fmap count_loc] →
    lossless_valid_adv LA DERIVE_export (resolve A RUN tt) →
    AdvantageE (COUNT q ∘ KDF_mid) (COUNT q ∘ KDF_ideal) A <= birthday_bound q.
  Proof.
    intros vA d1 d2 d3 d4 Hlva.
    have [d3a d3b] := fseparate_split_r LA KDF_mid'_locs KDF_bad_locs d3.
    ssprove triangle (COUNT q ∘ KDF_mid)
      [:: COUNT q ∘ KDF_mid'; COUNT q ∘ KDF_bad ] (COUNT q ∘ KDF_ideal) A as ineq.
    eapply le_trans. 1: exact ineq.
    have e1 : AdvantageE (COUNT q ∘ KDF_mid) (COUNT q ∘ KDF_mid') A = 0.
    { by apply: COUNT_KDF_mid_KDF_mid'_bound. }
    have e2 : AdvantageE (COUNT q ∘ KDF_bad) (COUNT q ∘ KDF_ideal) A = 0.
    { by apply: COUNT_KDF_bad_KDF_ideal_bound. }
    rewrite e1 e2 GRing.add0r GRing.addr0.
    eapply le_trans.
    - apply: COUNT_KDF_mid'_KDF_bad_bound; eassumption.
    - exact: Pr_bad_COUNT_KDF_mid'_bound.
  Qed.

  (** Final statement, assembled from the two steps above via the
    triangle inequality, exactly as in [PRF.v]'s [security_based_on_prf]
    and [PRFPRG.v]'s [security_based_on_prf]. [q] is now a bound on [A]'s
    total number of [DERIVE] queries *by construction* (via [COUNT q]),
    not an extra hypothesis on [A] -- see [COUNT]'s docstring above.

    UPDATE: the bound now ALSO carries [q%:R * birthday_bound q] --
    [KDF_real_KDF_mid_bound]'s per-hop up-to-bad sum
    [\sum_(i<q) Pr_bad ((A ∘ COUNT q) ∘ KDF_hybE_bad i) 4 true], bounded
    hop-by-hop via [Pr_bad_COUNT_KDF_hybE_bad_bound] (mirroring
    [Pr_bad_COUNT_KDF_mid'_bound]) and collapsed via [sumr_const]/
    [card_ord]/[mulr_natl] -- ON TOP OF the original, single
    [birthday_bound q] from step 2 ([KDF_mid_KDF_ideal_bound]). This is
    the [q * birthday_bound q] cost flagged in [KDF_hybE_bad]'s own
    docstring: tracking the COARSE "Extract reused a prk on some other
    ss" event once per hybrid hop, rather than the tighter
    "...specifically collided with prk_i", is strictly simpler to prove
    but pays for it with a factor of [q]. *)
  (* See [KDF_real_KDF_mid_bound]'s docstring for why the bound is stated
    at the composed reduction adversary [(A ∘ COUNT q) ∘ KDF_hyb_EVAL i]
    rather than at the bare top-level [A]: [prf_epsilon A] itself would
    be identically [0] (a disjoint-interface artifact, nothing to do
    with [PRF]'s actual security), making the bare-[A] form of this
    theorem false in general. This mirrors [PRFPRG.v]'s own
    [security_based_on_prf], whose bound is likewise stated at
    [A ∘ GEN_HYB_EVAL_pkg i], never at the bare top-level adversary. *)
  Theorem security_of_KDF LA A q :
    ValidPackage LA DERIVE_export A_export A →
    fseparate LA KDF_real_locs →
    fseparate LA KDF_mid_locs →
    fseparate LA KDF_ideal_locs →
    fseparate LA KDF_hyb_locs →
    fseparate LA KDF_hybE_bad_locs →
    fseparate LA KDF_hyb_bad_locs →
    fseparate LA KDF_mid'_bad_locs →
    fseparate LA [fmap count_loc] →
    fseparate LA [fmap eval_key_loc] →
    fseparate LA [fmap eval_tbl_loc] →
    lossless_valid_adv LA DERIVE_export (resolve A RUN tt) →
    AdvantageE (COUNT q ∘ KDF_real) (COUNT q ∘ KDF_ideal) A <=
      (\sum_(i < q) prf_epsilon ((A ∘ COUNT q) ∘ KDF_hyb_EVAL i))
      + q%:R * birthday_bound q + birthday_bound q.
  Proof.
    intros vA d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 Hlva.
    ssprove triangle (COUNT q ∘ KDF_real) [:: COUNT q ∘ KDF_mid ] (COUNT q ∘ KDF_ideal) A as ineq.
    eapply le_trans. 1: exact ineq.
    have e1 := KDF_real_KDF_mid_bound LA A q vA d1 d2 d4 d5 d6 d8 d9 d10 Hlva.
    have e2 := KDF_mid_KDF_ideal_bound LA A q vA d2 d3 d7 d8 Hlva.
    have e3 : \sum_(i < q) Pr_bad ((A ∘ COUNT q) ∘ KDF_hybE_bad i) 4 true <= q%:R * birthday_bound q.
    { apply: le_trans.
      - apply: ler_sum => i _.
        exact: (Pr_bad_COUNT_KDF_hybE_bad_bound i LA A q vA d5 d8 Hlva).
      - rewrite GRing.sumr_const card_ord GRing.mulr_natl.
        exact: lexx. }
    apply: le_trans.
    1: apply: lerD; [exact: e1 | exact: e2].
    apply: lerD; [ | exact: lexx].
    apply: lerD; [exact: lexx | exact: e3].
  Qed.

End HKDF_example.
