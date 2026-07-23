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
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude.

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

  Local Open Scope ring_scope.

  (* The advantage of distinguishing [PRF _ k] (for a single, uniformly
     random, hidden key [k]) from an independent uniformly random function.
     Negligible by assumption; reused per hybrid step below. *)
  Definition prf_epsilon (A : raw_package) : R :=
    (* placeholder: same shape as [PRF.v]'s / [PRFPRG.v]'s [prf_epsilon],
       i.e. [Advantage EVAL A] for the appropriate single-key [EVAL] game
       built from [PRF]. Left abstract here until the hybrid reduction
       package (item 1 in the roadmap above) is written. *)
    0.

  (* The classical birthday bound: with (at most) q samples drawn
     uniformly from a space of size [PRK_N], the probability that two of
     them collide is at most q^2 / (2 * PRK_N). *)
  Definition birthday_bound (q : nat) : R :=
    (q * q)%:R / (2 * PRK_N)%:R.

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
    AdvantageE KDF_real KDF_ideal A <=
      (\sum_(i < q) prf_epsilon A) + birthday_bound q.
  Proof.
    intros vA d1 d2 d3.
    ssprove triangle KDF_real [:: pack KDF_mid ] KDF_ideal A as ineq.
    eapply le_trans. 1: exact ineq.
    apply: lerD.
    - by apply: KDF_real_KDF_mid_bound.
    - by apply: KDF_mid_KDF_ideal_bound.
  Qed.

End HKDF_example.
