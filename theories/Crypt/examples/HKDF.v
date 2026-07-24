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

  PROOF ROADMAP (this file only lays out the games and the shape of the
  final bound; the two non-trivial lemmas are left as [Admitted] below,
  with pointers to what needs to be proved):

    KDF_real                     -- Extract (RO) + Expand (real PRF)
       |  hybrid over the <= q distinct [prk]'s that Extract can produce;
       |  at each step we swap one instance of Expand for an independent
       |  random function using the security of PRF. This step does NOT
       |  need the birthday assumption: it only concerns one instance at
       |  a time, exactly like the hybrid argument in PRFPRG.v /
       |  HybridArgument.v.
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

  giving, in the end,

    Advantage KDF A <=
      (\sum_(i < q) prf_epsilon (... i-th hybrid reduction ...))
      + birthday_bound q.

  The two missing ingredients are therefore:
  1. [KDF_real_KDF_mid_bound]: a dynamic-key hybrid argument (like
     [HYB_MI_CPA]/[Adv_hybrid] in PKE/MultiInstance.v and HybridArgument.v,
     but keyed by "the i-th distinct shared secret seen so far" instead of
     a statically-known instance count).
  2. [KDF_mid_KDF_ideal_bound]: an "up-to-bad" argument (in the style
     hinted at by [Theta_exCP.v]) together with a plain combinatorial
     birthday-bound counting lemma over [chFin PRK_N], which does not
     currently exist anywhere in SSProve.
*)

From SSProve.Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".
Unset SsrOldRewriteGoalsOrder. (* remove the line when requiring MathComp >= 2.6 *)

From SSProve.Mon Require Import SPropBase.
From SSProve.Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude
  pkg_lossless pkg_upto_bad UpToBadState.

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
  Admitted.

  Local Open Scope ring_scope.

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

  (* --- hybrid family, indexed by "number of *distinct* [prk]'s treated
    as ideal so far" ---

    [KDF_hyb i]: the first [i] distinct [prk] values Extract has ever
    handed out get an ideal (random-function) Expand via [mid_loc]; every
    [prk] discovered after that gets the real [PRF]. Distinct [prk]'s are
    numbered by order of first appearance ([prk_index_loc] /
    [prk_count_loc]), so this is well-defined for an adaptive adversary
    exactly like [GEN_HYB_pkg] in PRFPRG.v (indexed there by raw query
    count instead of by distinct-key count).

    [KDF_hyb 0] is exactly [KDF_real]: no [prk] ever has index < 0, so
    every query takes the real-PRF branch. For any [i] at least the
    number of distinct shared secrets ever queried, [KDF_hyb i] is
    exactly [KDF_mid]: every [prk] has index < i, so every query takes the
    ideal branch. Crucially, swapping *one* [prk]'s Expand from real to
    ideal never needs the birthday assumption: [KDF_real] and [KDF_mid]
    already agree on what to do with a *repeated* [prk] (both are pure
    functions of [prk] alone), so nothing here depends on distinct shared
    secrets staying collision-free -- that concern only arises when
    comparing against [KDF_ideal] (step 2).
  *)

  Definition prk_count_loc := mkloc 9 (0 : nat).
  Definition prk_index_loc := mkloc 10 (emptym : chMap 'prk 'nat).

  Definition KDF_hyb_locs :=
    [fmap extract_loc; mid_loc; prk_count_loc; prk_index_loc].

  (* Extract [ss]'s [prk], and the order in which that [prk] was first
    discovered (assigning it a fresh, incrementing index the first time
    it is ever seen). Shared, unchanged, between [KDF_hyb] and
    [KDF_hyb_EVAL] below -- exactly the [kgen]-style shared fragment
    pattern used in PRF.v / PRFMAC.v / PRFPRG.v. *)
  Definition get_prk_idx (ss : 'ss) : raw_code ('prk × 'nat) :=
    T ← get extract_loc ;;
    prk ← match getm T ss with
    | Some prk => ret prk
    | None =>
        prk <$ uniform PRK_N ;;
        #put extract_loc := setm T ss prk ;;
        ret prk
    end ;;
    PIdx ← get prk_index_loc ;;
    idx ← match getm PIdx prk with
    | Some idx => ret idx
    | None =>
        cnt ← get prk_count_loc ;;
        #put prk_count_loc := cnt.+1 ;;
        #put prk_index_loc := setm PIdx prk cnt ;;
        ret cnt
    end ;;
    ret (prk, idx).

  Lemma get_prk_idx_valid {L I} (ss : 'ss) :
    fhas L extract_loc -> fhas L prk_index_loc -> fhas L prk_count_loc ->
    ValidCode L I (get_prk_idx ss).
  Proof.
    move=> H1 H2 H3.
    rewrite /get_prk_idx.
    apply: valid_getr => [// | T].
    case: (getm T ss) => [prk|].
    - apply: valid_getr => [// | PIdx].
      case: (getm PIdx prk) => [idx|].
      + by apply: valid_ret.
      + apply: valid_getr => [// | cnt].
        apply: valid_putr => //.
        apply: valid_putr => //.
        by apply: valid_ret.
    - apply: valid_sampler => prk.
      apply: valid_putr => //.
      apply: valid_getr => [// | PIdx].
      case: (getm PIdx prk) => [idx|].
      + by apply: valid_ret.
      + apply: valid_getr => [// | cnt].
        apply: valid_putr => //.
        apply: valid_putr => //.
        by apply: valid_ret.
  Qed.

  Hint Extern 1 (ValidCode ?L ?I (get_prk_idx ?ss)) =>
    eapply get_prk_idx_valid ; [ fmap_solve | fmap_solve | fmap_solve ]
    : typeclass_instances ssprove_valid_db.

  Definition KDF_hyb (i : nat) : game DERIVE_export :=
    [package KDF_hyb_locs ;
      #def #[ DERIVE ] ('(ss, info) : 'ss × 'info) : 'out
      {
        '(prk, idx) ← get_prk_idx ss ;;
        if ltn idx i then
          T2 ← get mid_loc ;;
          match getm T2 (prk, info) with
          | Some y => ret y
          | None =>
              y <$ uniform Out_N ;;
              #put mid_loc := setm T2 (prk, info) y ;;
              ret y
          end
        else
          ret (PRF info prk)
      }
    ].

  (* Connector: handles every [prk] except the one at index exactly [i]
    itself (using [mid_loc] / the real [PRF] as [KDF_hyb] does), and
    delegates that one instance to the imported [EVAL] oracle. Composing
    with [EVAL true] (real) reproduces [KDF_hyb i]; composing with
    [EVAL false] (ideal) reproduces [KDF_hyb i.+1]. *)
  Definition KDF_hyb_EVAL (i : nat) : package EVAL_export DERIVE_export :=
    [package KDF_hyb_locs ;
      #def #[ DERIVE ] ('(ss, info) : 'ss × 'info) : 'out
      {
        #import {sig #[ EVAL_OP ] : 'info → 'out } as eval ;;
        '(prk, idx) ← get_prk_idx ss ;;
        if ltn idx i then
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
          ret (PRF info prk)
      }
    ].

  (* The classical birthday bound: with (at most) q samples drawn
     uniformly from a space of size [PRK_N], the probability that two of
     them collide is at most q^2 / (2 * PRK_N). *)
  Definition birthday_bound (q : nat) : R :=
    (q * q)%:R / (2 * PRK_N)%:R.

  (* [KDF_hyb 0] is exactly [KDF_real]: no [prk] ever has index < 0, so
    the "ideal" branch is dead, and the [prk_count_loc]/[prk_index_loc]
    bookkeeping is ghost state, exactly like [KDF_bad]'s bookkeeping was
    dead w.r.t. [KDF_bad_KDF_ideal_equiv] above. *)
  Lemma KDF_real_KDF_hyb0_equiv :
    KDF_real ≈₀ KDF_hyb 0.
  Proof.
    apply eq_rel_perf_ind_ignore with [fmap mid_loc; prk_count_loc; prk_index_loc].
    1: fmap_solve.
    simplify_eq_rel arg.
    destruct arg as [ss info].
    rewrite /get_prk_idx /=.
    apply: r_get_vs_get_remember => T.
    destruct (getm T ss) as [prk|] eqn:HT.
    - rewrite HT /=.
      apply: r_get_remember_rhs => PIdx.
      destruct (getm PIdx prk) as [idx|] eqn:HPIdx.
      + rewrite HPIdx /=.
        apply: r_ret => s0 s1 h.
        destruct h as [[[Hinv ?] ?] ?].
        split; [ reflexivity | exact Hinv ].
      + rewrite HPIdx /=.
        apply: r_get_remember_rhs => cnt.
        apply: r_put_rhs. apply: r_put_rhs.
        ssprove_restore_mem; last by apply: r_ret.
        by ssprove_invariant.
    - rewrite HT /=.
      apply: r_uniform_bij => [|prk].
      1: exists id; done.
      apply: r_put_vs_put.
      (* flush this put back to a clean invariant before the next [get] --
        see the comment on the analogous step in [KDF_bad_KDF_ideal_equiv]. *)
      ssprove_restore_mem; [ by ssprove_invariant | ].
      apply: r_get_remember_rhs => PIdx.
      destruct (getm PIdx prk) as [idx|] eqn:HPIdx.
      + rewrite HPIdx /=.
        apply: r_ret => s0 s1 h.
        destruct h as [Hinv ?].
        split; [ reflexivity | exact Hinv ].
      + rewrite HPIdx /=.
        apply: r_get_remember_rhs => cnt.
        apply: r_put_rhs. apply: r_put_rhs.
        ssprove_restore_mem; last by apply: r_ret.
        by ssprove_invariant.
  Qed.

  (**
    Step 2 of 3 (hop 2): [KDF_hyb i] agrees with [KDF_hyb_EVAL i] composed
    with the *real* single-key oracle [EVAL true]. [KDF_hyb_EVAL i] routes
    exactly the prk at index [i] through the imported [eval], and
    [EVAL_pkg_tt] lazily samples one hidden key on first use -- forced (by
    the invariant below) to coincide with that one prk.

    Unlike [PRFPRG.v]'s [GEN_GEN_HYB_equiv] (hybrid index = a raw,
    ever-incrementing query counter, so "count = i" happens at most once),
    here "idx = i" can recur: every later query resolving to the *same*
    prk sees the same idx again. The invariant's second conjunct handles
    that: once some prk is assigned index [i], [eval_key_loc] is pinned to
    exactly that prk for good, so repeat queries just replay the cached
    branch identically on both sides.

    The third conjunct is a structural fact about [extract_loc] /
    [prk_index_loc] alone (no [eval_key_loc] involved): every [prk] ever
    handed out by [extract_loc] already has an index assigned, since
    [get_prk_idx] always assigns one immediately after determining [prk],
    whether [prk] came from a fresh sample or a [T]-lookup. This is what
    rules out the "prk known, but its index somehow isn't" case below. *)
  Definition KDF_hyb_EVAL_inv (i : nat) : precond :=
    heap_ignore [fmap eval_key_loc] ⋊
    couple_lhs extract_loc prk_index_loc
      (fun T PIdx => forall ss0 prk0, T ss0 = Some prk0 -> exists idx0, PIdx prk0 = Some idx0) ⋊
    couple_rhs prk_count_loc eval_key_loc
      (fun cnt k => leq cnt i -> k = None) ⋊
    couple_rhs prk_index_loc eval_key_loc
      (fun PIdx k => forall prk0, getm PIdx prk0 = Some i -> k = Some prk0).

  Lemma KDF_hyb_KDF_hyb_EVAL_true_equiv i :
    KDF_hyb i ≈₀ KDF_hyb_EVAL i ∘ EVAL true.
  Proof.
    apply eq_rel_perf_ind with (KDF_hyb_EVAL_inv i).
    1: {
      eapply Invariant_inv_conj.
      - eapply Invariant_inv_conj.
        + eapply Invariant_inv_conj.
          * eapply Invariant_heap_ignore.
            rewrite /KDF_hyb /KDF_hyb_EVAL /EVAL /=. fmap_solve.
          * eapply SemiInvariant_relApp.
            -- rewrite /KDF_hyb /KDF_hyb_EVAL /EVAL /KDF_hyb_locs /=. by [].
            -- done.
        + eapply SemiInvariant_relApp.
          * rewrite /KDF_hyb /KDF_hyb_EVAL /EVAL /KDF_hyb_locs /=. by [].
          * done.
      - eapply SemiInvariant_relApp.
        + rewrite /KDF_hyb /KDF_hyb_EVAL /EVAL /KDF_hyb_locs /=. by [].
        + done.
    }
    simplify_eq_rel arg.
    ssprove_code_simpl.
    destruct arg as [ss info].
    rewrite /get_prk_idx /=.
    apply: r_get_vs_get_remember => T.
    destruct (getm T ss) as [prk|] eqn:HT.
    - rewrite HT /=.
      apply: r_get_vs_get_remember => PIdx.
      destruct (getm PIdx prk) as [idx|] eqn:HPIdx.
      + (* prk and idx both already known: no sampling on either side *)
        rewrite HPIdx /=.
        case: (ltnP idx i) => Hlt /=.
        * (* idx < i: identical [mid_loc] code on both sides *)
          apply: r_get_vs_get_remember => T2.
          destruct (getm T2 (prk, info)) as [y|] eqn:HT2.
          -- rewrite HT2 /=.
             apply: r_ret => s0 s1 h.
             split; [ reflexivity | extract_base_inv h ].
          -- rewrite HT2 /=.
             apply: r_uniform_bij => [|y]. 1: exists id; done.
             apply: r_put_vs_put.
             ssprove_restore_mem; last by apply: r_ret.
             close_preserve4.
        * (* i <= idx *)
          case: (eqVneq idx i) => Heq /=.
          -- (* idx = i: RHS's [eval] must agree with LHS's real PRF, via
               the invariant's second conjunct (a [prk] once assigned index
               [i] pins [eval_key_loc] to it for good). *)
             apply: r_get_remember_rhs => k.
             ssprove_rem_rel 0%N => Hinv.
             rewrite Heq in HPIdx.
             rewrite (Hinv prk HPIdx) /=.
             apply: r_ret => s0 s1 h.
             split; [ reflexivity | extract_base_inv h ].
          -- (* idx <> i: RHS falls through to the real-[PRF] branch too *)
             apply: r_ret => s0 s1 h.
             split; [ reflexivity | extract_base_inv h ].
      + (* IMPOSSIBLE: [get_prk_idx] always assigns [prk] an index in the
           very same call it first stores [prk] in [extract_loc], so a
           [prk] already known to [extract_loc] can never be missing from
           [prk_index_loc]. This is exactly the invariant's third
           conjunct. *)
        ssprove_rem_rel 2%N => Hdom.
        exfalso.
        have [idx0 Hidx0] := Hdom ss prk HT.
        rewrite HPIdx in Hidx0. discriminate.
    - (* [T ss = None]: [prk] is freshly sampled. [extract_loc] is shared
         state, so this sample -- call it [a] -- must be the *same* value
         on both sides (that's what "not [heap_ignore]'d" already forces),
         hence coupled via [r_uniform_bij] with [f := id] immediately.

         UNRESOLVED, two compounding gaps:

         (1) Once [a] is sampled and [extract_loc] updated, recovering a
         clean invariant (to then [get prk_index_loc]) requires showing
         the third conjunct survives that update -- true (case on whether
         [a] already has an index or not), but *not* automatic: unlike
         every other [close_preserve]-style call in this file, the
         updated location ([extract_loc]) is one the invariant actually
         quantifies over, so [ssprove_invariant]'s generic search can't
         discharge it; it needs a hand-written [preserve_update_rel]
         proof for this conjunct specifically. Swapping the [get
         prk_index_loc] to happen *before* the [extract_loc] put (via
         [ssprove_swap_lhs]/[ssprove_swap_rhs]) sidesteps needing that at
         the point of the swap, but the same obligation resurfaces at
         whatever leaf eventually restores the invariant.

         (2) Deeper, in the sub-case where [a] is a genuinely brand new
         distinct prk *and* its fresh index equals [i]: the RHS's [eval]
         call independently samples its own hidden key, but the LHS has
         no sample left to couple it against -- [a] was already fixed
         above, to decide *this very branch*. This differs from
         [PRFPRG.v]'s [GEN_GEN_HYB_equiv], where the analogous branch
         decision is on a pure query *counter*, independent of any
         sampled value, so neither side's sample is consumed yet by the
         time the branch is chosen, and swapping brings them adjacent.
         Here the branch decision (is [a] fresh, and is its rank exactly
         [i]?) is itself a function of the sampled value [a], so there is
         no second pending sample on the LHS to couple the RHS's fresh
         key against. Making this sound likely needs the *hybrid* itself
         to sample eagerly (the same eager-vs-lazy technique the birthday
         step already needs for [KDF_mid_KDF_ideal_bound]), not just a
         smarter tactic. *)
      admit.
  Admitted.

  (**
    Step 1 (TODO): hybrid argument over the <= q distinct [prk] values
    Extract can hand out, swapping the real PRF-Expand computation for an
    independent random one, one instance at a time. This is the same
    shape as [hyb_security_based_on_prf] in PRFPRG.v, generalised from "the
    first i queries" to "the first i *distinct shared secrets*" -- closer
    in spirit to [Adv_hybrid] / [HYB_MI_CPA] in PKE/MultiInstance.v, since
    the adversary chooses which shared secret is "new" adaptively rather
    than in a fixed order.
  *)
  Theorem KDF_real_KDF_mid_bound LA A q :
    ValidPackage LA DERIVE_export A_export A →
    fseparate LA KDF_real_locs →
    fseparate LA KDF_mid_locs →
    fseparate LA KDF_hyb_locs →
    AdvantageE KDF_real KDF_mid A <= \sum_(i < q) prf_epsilon A.
  Proof.
  Admitted.

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

    (2b) AdvantageE KDF_mid KDF_bad A <= Pr[bad_loc = true at the end].
         This is the generic "Fundamental Lemma" of up-to-bad reasoning:
         [KDF_mid] and [KDF_bad] are constructed to agree exactly as long
         as [bad_loc] stays [false] (every ss so far uniquely owns its
         [prk], so both games consult [mid_loc] identically). SSProve does
         not currently have this as a reusable lemma; the semantic
         ingredient for it is hinted at in
         [rhl_semantics/only_prob/Theta_exCP.v] (a coupling where the
         "bad" set has negligible mass), but lifting that to a usable
         package-level rule is new work, not just filling in a proof.
         Stating "Pr[bad_loc = true]" itself also needs a small wrapper
         (a canonical adversary that runs [A], then reveals [bad_loc] as
         its verdict), since [Pr]/[Pr_op] in pkg_advantage.v only reads
         off a package's designated boolean [RUN] output, not an arbitrary
         location.

    (2c) Pr[bad_loc = true] <= birthday_bound q: the actual combinatorial
         birthday-bound counting lemma over [chFin PRK_N] (a union bound
         over pairs among the <= q distinct shared secrets queried). This
         does not exist anywhere in SSProve yet and needs to be proved
         from scratch.
  *)
  Theorem KDF_mid_KDF_ideal_bound LA A q :
    ValidPackage LA DERIVE_export A_export A →
    fseparate LA KDF_mid_locs →
    fseparate LA KDF_ideal_locs →
    AdvantageE KDF_mid KDF_ideal A <= birthday_bound q.
  Proof.
  Admitted.

  (** Final statement, assembled from the two steps above via the
    triangle inequality, exactly as in [PRF.v]'s [security_based_on_prf]
    and [PRFPRG.v]'s [security_based_on_prf]. *)
  Theorem security_of_KDF LA A q :
    ValidPackage LA DERIVE_export A_export A →
    fseparate LA KDF_real_locs →
    fseparate LA KDF_mid_locs →
    fseparate LA KDF_ideal_locs →
    fseparate LA KDF_hyb_locs →
    AdvantageE KDF_real KDF_ideal A <=
      (\sum_(i < q) prf_epsilon A) + birthday_bound q.
  Proof.
    intros vA d1 d2 d3 d4.
    ssprove triangle KDF_real [:: pack KDF_mid ] KDF_ideal A as ineq.
    eapply le_trans. 1: exact ineq.
    apply: lerD.
    - by apply: KDF_real_KDF_mid_bound.
    - by apply: KDF_mid_KDF_ideal_bound.
  Qed.

End HKDF_example.
