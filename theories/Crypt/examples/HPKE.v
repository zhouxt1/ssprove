(**
  HPKE-style 3-hop composition (DRAFT / skeleton)

  A KEMDEM-style state-separated game for an HPKE-shaped protocol:

      HPKE b  :=  MOD ∘ (DHKEM b || KDF b || AEAD b) ∘ (KEYS || KDFC true)

  The three hops, mirroring KEMDEM's KEM/DEM split ([KEMDEM.v]):

    - DHKEM b : "ECDH + KDF_1" as ONE abstract component. Real (b = true)
      computes an encapsulation context and a shared secret and stores the
      secret via [SET_SS]; ideal (b = false) asks KEYS to sample a uniform
      one via [GEN_SS]. Kept fully abstract here (a Context raw_package);
      its idealisation cost is ε_mDDH + extractor terms (see conversation /
      future work), NOT this file's business.

    - KDF b : the key-schedule hop ("KDF_2"). CONCRETE glue code: the real
      branch reads the session's shared secret ([GET_SS]), calls an
      abstract KDF core [KDFC] on (ss, info) — whose export interface is
      DELIBERATELY IDENTICAL to HKDF.v's [DERIVE_export] (op id [DERIVE] = 0,
      type 'ss × 'info → 'key) so that [KDFC b] can later be instantiated
      with HKDF.v's [COUNT q ∘ KDF_real] / [COUNT q ∘ KDF_ideal], importing
      [security_of_KDF] wholesale — and stores the derived key ([SET_K]).
      The ideal branch asks KEYS for a fresh uniform session key ([GEN_K]).

    - AEAD b : abstract AEAD component reading the session key via [GET_K].
      Real encrypts; ideal is (e.g.) encryption of a constant / uniform
      ciphertext. Abstract Context raw_package.

    - KEYS : the (single) key-management package, KEMDEM's [KEY]
      generalised to two handle-indexed stores: shared secrets
      ([ss_tbl_loc]) and session keys ([k_tbl_loc]).

  WHAT q MEANS HERE. Sessions are HANDLES of type ['fin q], so
    q = number of sessions = number of shared secrets = number of session
    keys, ENFORCED BY THE TYPE, with no COUNT package and no #assert.
  The KDF slot additionally MEMOISES per handle ([kdone_loc]): the abstract
  KDF core is called AT MOST ONCE PER SESSION, ever, so when [KDFC] is
  instantiated with HKDF.v's [COUNT q ∘ KDF_real], the throttle never
  fires and [security_of_KDF] applies at exactly this q (its hybrid then
  runs over ≤ q distinct shared secrets — the tight reading). AEAD
  encryption queries are NOT bounded here; a per-hop bound for them lives
  inside [AdvantageE (GAE true) (GAE false)] and would get its own COUNT
  wrapper at instantiation time (unbounded-input op ⇒ needs a throttle;
  handle-indexed memoised ops don't).

  LOSSLESSNESS DISCIPLINE. No package in this file uses [#assert]
  (KEMDEM-style asserts make packages non-lossless, which would poison
  [lossless_valid_adv] for the composed reduction adversaries that
  HKDF.v's up-to-bad machinery needs). Instead:
    - KEYS [SET_*]/[GEN_*] are first-write-wins (repeat = no-op);
    - KEYS [GET_*] lazily samples a uniform value on an unset handle
      (dead code along MOD-mediated flows, but total);
    - MOD routes ENC-before-INIT to an independent uniform ciphertext
      (same in both worlds ⇒ costs no advantage);
    - the KDF slot memoises instead of asserting freshness.

  LOCATION / OP-ID BUDGET. To compose with HKDF.v later, location ids and
  op ids here avoid HKDF.v's ranges: HKDF.v uses locations mkloc 1..12 and
  op ids 0 ([DERIVE]) and 1 ([EVAL_OP]); this file uses locations 40+ and
  op ids 20+ (except [DERIVE] = 0, shared ON PURPOSE with HKDF.v since it
  IS that interface).

  STATUS: [hop_dhkem]/[hop_kdf]/[hop_aead] and [GKDF_core_hop] (package
  algebra, same toolbox as the hop lemmas) are Qed'd. [GKDF_mid_ref_ideal]
  (up-to-bad, bad := two sessions drew the same shared secret; Pr[bad] <=
  q^2/(2*SS_N)) is NOW Qed'd IN FULL, feeding a Qed'd
  [GKDF_bad_mid_ref_GKDF_bad_false_bound]:
    - [GKDF_bad_mid_ref_GKDF_bad_false_eq_up_to_bad]: the relational,
      oracle-by-oracle "match until [bad_loc] fires" fact
      [eq_upto_bad_perf_ind] needs, mirroring HKDF.v's
      [KDF_mid'_KDF_bad_eq_up_to_bad] — Qed'd in full (assembled from
      the three per-op case lemmas [GKDF_bad_GEN_SS_case]/
      [GKDF_bad_GET_K_case]/[GKDF_bad_DERIVE_K_case] via [fmap_invert]/
      [simplify_linking]/[code_link_rw_lhs]/[code_link_rw_rhs]).
    - [Pr_bad_GKDF_bad_mid_ref_bound]: bounding the resulting [Pr_bad] by
      [birthday_ss] — Qed'd, in terms of [Pr_bad_GKDF_bad_mid_ref_adv_bound]:
      the core adversary-code induction mirroring HKDF.v's
      [Pr_bad_adv_bound] — NOW Qed'd in full too (the [ret]/[opr]/[getr]/
      [putr]/[sampler] induction, with [opr] split into [GEN_SS]/[GET_K]/
      [DERIVE_K] via [fmap_invert]/[simplify_linking], [DERIVE_K]'s own
      shared "TI-lookup + [k_tbl_loc]" tail factored into a local [Htail]
      reused across its Some-[ss_tbl_loc]/fresh-[ss_tbl_loc] sub-cases, and
      the birthday step itself via [Birthday.expectation_le_bad_bound] —
      see its docstring ~L3606 below for the full shape). No admits remain
      in this development.
  Both dead-ghost-code legs feeding into the kernel
  ([GKDF_bad_mid_ref_GKDF_mid_ref_equiv], [GKDF_bad_false_GKDF_false_equiv])
  ARE Qed'd in full.
  NOTE [GKDF_bound] also takes a [bridge] PREMISE ("the parameter's ideal
  branch behaves as the concrete reference ideal [KDFC_IDEAL]") — that is
  deliberately a hypothesis, not an admitted lemma: it is unprovable (and
  false in general) for an arbitrary Context parameter, and is discharged
  by each instantiation (see the chain diagram before [GKDF_mid]).
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

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.

Section HPKE.

  (** Number of sessions. This IS the q of the final bound: sessions are
    handles of type ['fin q], so "at most q shared secrets" holds by
    construction, not by a hypothesis on the adversary. *)
  Context (q : nat).

  (** Sizes of the value spaces. Abstract; when instantiating the KDF hop
    with HKDF.v, take SS_N/Info_N/Key_N := its SS_N/Info_N/Out_N. *)
  Context (SS_N Key_N Info_N Ectx_N Plain_N Cipher_N : nat).

  (** [KEYS]/[KEYS_bad]/[KDFC_IDEAL] all lazily sample from [uniform SS_N]/
    [uniform Key_N] on the "fresh handle" branches, and the file's header
    ("LOSSLESSNESS DISCIPLINE") explicitly claims these packages are
    TOTAL — which needs [SS_N]/[Key_N] positive ([uniform 0] has zero
    total mass, so a package that could reach it would fail to be
    lossless). Made explicit here (needed by the up-to-bad development
    below, e.g. wherever [LosslessOp (uniform SS_N)] must be exhibited). *)
  Context (SS_N_gt0 : (0 < SS_N)%N) (Key_N_gt0 : (0 < Key_N)%N).

  Definition SESS : choice_type := 'fin q.
  Definition SS : choice_type := 'fin SS_N.
  Definition Key : choice_type := 'fin Key_N.
  Definition Info : choice_type := 'fin Info_N.
  Definition Ectx : choice_type := 'fin Ectx_N.
  Definition Plain : choice_type := 'fin Plain_N.
  Definition Cipher : choice_type := 'fin Cipher_N.

  Notation " 'sess " := SESS (in custom pack_type at level 2).
  Notation " 'sess " := SESS (at level 2) : package_scope.
  Notation " 'ss " := SS (in custom pack_type at level 2).
  Notation " 'ss " := SS (at level 2) : package_scope.
  Notation " 'key " := Key (in custom pack_type at level 2).
  Notation " 'key " := Key (at level 2) : package_scope.
  Notation " 'info " := Info (in custom pack_type at level 2).
  Notation " 'info " := Info (at level 2) : package_scope.
  Notation " 'ectx " := Ectx (in custom pack_type at level 2).
  Notation " 'ectx " := Ectx (at level 2) : package_scope.
  Notation " 'plain " := Plain (in custom pack_type at level 2).
  Notation " 'plain " := Plain (at level 2) : package_scope.
  Notation " 'cipher " := Cipher (in custom pack_type at level 2).
  Notation " 'cipher " := Cipher (at level 2) : package_scope.

  (** Op ids. [DERIVE] = 0 matches HKDF.v's [DERIVE] on purpose: the
    abstract KDF core's export interface below IS HKDF.v's
    [DERIVE_export] (with 'out read as 'key). Everything else lives at
    20+ to stay clear of HKDF.v's ids. *)
  Definition DERIVE : nat := 0.
  Definition XCAP : nat := 20.
  Definition SET_SS : nat := 21.
  Definition GEN_SS : nat := 22.
  Definition GET_SS : nat := 23.
  Definition SET_K : nat := 24.
  Definition GEN_K : nat := 25.
  Definition GET_K : nat := 26.
  Definition DERIVE_K : nat := 27.
  Definition AE_ENC : nat := 28.
  Definition INIT : nat := 29.
  Definition HENC : nat := 30.

  (** Locations: 40+ (HKDF.v owns 1..12). *)
  Definition ss_tbl_loc := mkloc 40 (emptym : chMap SESS SS).
  Definition k_tbl_loc := mkloc 41 (emptym : chMap SESS Key).
  Definition info_loc := mkloc 42 (emptym : chMap SESS Info).
  Definition kdone_loc := mkloc 43 (emptym : chMap SESS 'unit).

  (** * The KEYS package

    KEMDEM's [KEY], generalised to two handle-indexed stores and made
    lossless: SET/GEN are first-write-wins, GET lazily samples on a miss
    (instead of [#assert isSome] — see the header). *)

  Definition KEYS_loc := [fmap ss_tbl_loc ; k_tbl_loc ].

  Definition KEYS_out :=
    [interface
      #val #[ SET_SS ] : 'sess × 'ss → 'unit ;
      #val #[ GEN_SS ] : 'sess → 'unit ;
      #val #[ GET_SS ] : 'sess → 'ss ;
      #val #[ SET_K ] : 'sess × 'key → 'unit ;
      #val #[ GEN_K ] : 'sess → 'unit ;
      #val #[ GET_K ] : 'sess → 'key
    ].

  Definition KEYS : package [interface] KEYS_out :=
    [package KEYS_loc ;
      #def #[ SET_SS ] ('(n, s) : 'sess × 'ss) : 'unit {
        T ← get ss_tbl_loc ;;
        match getm T n with
        | Some _ => ret tt
        | None => #put ss_tbl_loc := setm T n s ;; ret tt
        end
      } ;
      #def #[ GEN_SS ] (n : 'sess) : 'unit {
        T ← get ss_tbl_loc ;;
        match getm T n with
        | Some _ => ret tt
        | None =>
            s <$ uniform SS_N ;;
            #put ss_tbl_loc := setm T n s ;;
            ret tt
        end
      } ;
      #def #[ GET_SS ] (n : 'sess) : 'ss {
        T ← get ss_tbl_loc ;;
        match getm T n with
        | Some s => ret s
        | None =>
            s <$ uniform SS_N ;;
            #put ss_tbl_loc := setm T n s ;;
            ret s
        end
      } ;
      #def #[ SET_K ] ('(n, k) : 'sess × 'key) : 'unit {
        T ← get k_tbl_loc ;;
        match getm T n with
        | Some _ => ret tt
        | None => #put k_tbl_loc := setm T n k ;; ret tt
        end
      } ;
      #def #[ GEN_K ] (n : 'sess) : 'unit {
        T ← get k_tbl_loc ;;
        match getm T n with
        | Some _ => ret tt
        | None =>
            k <$ uniform Key_N ;;
            #put k_tbl_loc := setm T n k ;;
            ret tt
        end
      } ;
      #def #[ GET_K ] (n : 'sess) : 'key {
        T ← get k_tbl_loc ;;
        match getm T n with
        | Some k => ret k
        | None =>
            k <$ uniform Key_N ;;
            #put k_tbl_loc := setm T n k ;;
            ret k
        end
      }
    ].

  (** * Abstract components *)

  (** DHKEM = "ECDH + KDF_1", one abstract package pair, KEMDEM-style
    b-dependent import: real SETs the honestly computed shared secret,
    ideal GENs a uniform one. [XCAP n] is expected to be memoised per
    handle by the instantiation (repeat calls return the cached context);
    with handles in ['fin q] that bounds fresh DH computations by q with
    no COUNT package. *)

  Definition DHKEM_in (b : bool) :=
    if b
    then [interface #val #[ SET_SS ] : 'sess × 'ss → 'unit ]
    else [interface #val #[ GEN_SS ] : 'sess → 'unit ].

  Definition DHKEM_out :=
    [interface #val #[ XCAP ] : 'sess → 'ectx ].

  Context (DHKEM : bool → raw_package).
  Context (DHKEM_loc : Locations).
  Context (DHKEM_valid :
    ∀ b, ValidPackage DHKEM_loc (DHKEM_in b) DHKEM_out (DHKEM b)).

  (** The abstract KDF core. Its interface is HKDF.v's [DERIVE_export]:
    substitute [KDFC b := COUNT q ∘ KDF (HKDF.v) b] (with Out_N := Key_N)
    and [AdvantageE (KDFC true) (KDFC false)] becomes exactly the LHS of
    [security_of_KDF]. The KDF slot below calls it at most once per
    session, so that COUNT q throttle never fires. *)

  Definition KDFC_out :=
    [interface #val #[ DERIVE ] : 'ss × 'info → 'key ].

  Context (KDFC : bool → raw_package).
  Context (KDFC_loc : Locations).
  Context (KDFC_valid :
    ∀ b, ValidPackage KDFC_loc [interface] KDFC_out (KDFC b)).

  (** Abstract AEAD, keyed through KEYS. Real encrypts, ideal (e.g.)
    encrypts a constant or returns uniform ciphertexts; the choice lives
    in the instantiation and its advantage term. NOTE: [AE_ENC] takes an
    unbounded input ('plain), so an eventual concrete bound for this hop
    needs its own COUNT-style throttle — by the file-header principle,
    handle-memoisation cannot bound it. *)

  Definition AEAD_in :=
    [interface #val #[ GET_K ] : 'sess → 'key ].

  Definition AEAD_out :=
    [interface #val #[ AE_ENC ] : 'sess × 'plain → 'cipher ].

  Context (AEADP : bool → raw_package).
  Context (AEAD_loc : Locations).
  Context (AEAD_valid :
    ∀ b, ValidPackage AEAD_loc AEAD_in AEAD_out (AEADP b)).

  (** * The KDF slot (concrete glue)

    Import interface is the SUPERSET of what the two branches use, so the
    package is uniform in [b] (unused imports are harmless; this spares
    us KEMDEM's dependent [KEM_in b] type juggling at the [par] sites).
    Memoised per handle: the abstract core is called at most once per
    session ever (see header). *)

  Definition KDF_in :=
    [interface
      #val #[ GET_SS ] : 'sess → 'ss ;
      #val #[ SET_K ] : 'sess × 'key → 'unit ;
      #val #[ GEN_K ] : 'sess → 'unit ;
      #val #[ DERIVE ] : 'ss × 'info → 'key
    ].

  Definition KDF_out :=
    [interface #val #[ DERIVE_K ] : 'sess × 'info → 'unit ].

  Definition KDF_loc := [fmap kdone_loc ].

  Definition KDF (b : bool) : package KDF_in KDF_out :=
    [package KDF_loc ;
      #def #[ DERIVE_K ] ('(n, info) : 'sess × 'info) : 'unit {
        #import {sig #[ GET_SS ] : 'sess → 'ss } as get_ss ;;
        #import {sig #[ SET_K ] : 'sess × 'key → 'unit } as set_k ;;
        #import {sig #[ GEN_K ] : 'sess → 'unit } as gen_k ;;
        #import {sig #[ DERIVE ] : 'ss × 'info → 'key } as derive ;;
        D ← get kdone_loc ;;
        match getm D n with
        | Some _ => ret tt
        | None =>
            #put kdone_loc := setm D n tt ;;
            if b
            then
              s ← get_ss n ;;
              k ← derive (s, info) ;;
              set_k (n, k)
            else
              gen_k n
        end
      }
    ].

  (** * The MOD package (adversary-facing adapter, KEMDEM's [MOD_CCA])

    [INIT (n, info)]: establish session n — run the DHKEM encapsulation
    and derive the session key with the (first-wins) info label.
    [HENC (n, m)]: AEAD-encrypt under session n's key; if n was never
    initialised, return an independent uniform ciphertext (identical in
    both worlds — the lossless replacement for KEMDEM's [#assert]). *)

  Definition MOD_in :=
    [interface
      #val #[ XCAP ] : 'sess → 'ectx ;
      #val #[ DERIVE_K ] : 'sess × 'info → 'unit ;
      #val #[ AE_ENC ] : 'sess × 'plain → 'cipher
    ].

  Definition MOD_out :=
    [interface
      #val #[ INIT ] : 'sess × 'info → 'ectx ;
      #val #[ HENC ] : 'sess × 'plain → 'cipher
    ].

  Definition MOD_loc := [fmap info_loc ].

  Definition MOD : package MOD_in MOD_out :=
    [package MOD_loc ;
      #def #[ INIT ] ('(n, info) : 'sess × 'info) : 'ectx {
        #import {sig #[ XCAP ] : 'sess → 'ectx } as xcap ;;
        #import {sig #[ DERIVE_K ] : 'sess × 'info → 'unit } as derive_k ;;
        I ← get info_loc ;;
        match getm I n with
        | Some i =>
            ectx ← xcap n ;;
            derive_k (n, i) ;;
            ret ectx
        | None =>
            #put info_loc := setm I n info ;;
            ectx ← xcap n ;;
            derive_k (n, info) ;;
            ret ectx
        end
      } ;
      #def #[ HENC ] ('(n, m) : 'sess × 'plain) : 'cipher {
        #import {sig #[ AE_ENC ] : 'sess × 'plain → 'cipher } as ae_enc ;;
        I ← get info_loc ;;
        match getm I n with
        | Some _ => ae_enc (n, m)
        | None =>
            c <$ uniform Cipher_N ;;
            ret c
        end
      }
    ].

  (** * Composed games *)

  (** Bottom layer: KEYS beside the (real, by default) abstract KDF core.
    The core stays [true] in the game family; the swap to [KDFC false]
    happens only inside the KDF-hop bridge below. *)
  Definition CORE (bc : bool) : raw_package := par KEYS (KDFC bc).

  Definition SLOTS (bdh bkdf bae : bool) : raw_package :=
    par (DHKEM bdh) (par (KDF bkdf) (AEADP bae)).

  Definition HPKE_pkg (bdh bkdf bae : bool) : raw_package :=
    MOD ∘ SLOTS bdh bkdf bae ∘ CORE true.

  Definition HPKE (b : bool) : raw_package := HPKE_pkg b b b.

  (** * Per-hop games and reductions

    Each hop game keeps [CORE] (KEYS, and the core for the KDF hop) plus
    the hop's own slot; everything else — MOD included — moves into the
    reduction, exactly as in KEMDEM's [single_key_a]. The ID interfaces
    below re-export what the OTHER slots import from the bottom layer. *)

  (** DHKEM hop: the other slots ([KDF true], [AEADP true]) import
    [KDF_in] ∪ [AEAD_in] from below. *)
  Definition I_dh_env :=
    [interface
      #val #[ GET_SS ] : 'sess → 'ss ;
      #val #[ SET_K ] : 'sess × 'key → 'unit ;
      #val #[ GEN_K ] : 'sess → 'unit ;
      #val #[ DERIVE ] : 'ss × 'info → 'key ;
      #val #[ GET_K ] : 'sess → 'key
    ].

  Definition GDH (b : bool) : raw_package :=
    (par (DHKEM b) (ID I_dh_env)) ∘ CORE true.

  Definition R_dh : raw_package :=
    MOD ∘ (par (ID DHKEM_out) (par (KDF true) (AEADP true))).

  (** KDF hop: DHKEM is already ideal ([false], importing GEN_SS),
    AEAD still real. *)
  Definition I_kdf_env :=
    [interface
      #val #[ GEN_SS ] : 'sess → 'unit ;
      #val #[ GET_K ] : 'sess → 'key
    ].

  Definition GKDF (b : bool) : raw_package :=
    (par (ID I_kdf_env) (KDF b)) ∘ CORE true.

  Definition R_kdf : raw_package :=
    MOD ∘ (par (DHKEM false) (par (ID KDF_out) (AEADP true))).

  (** AEAD hop: DHKEM and KDF both ideal. [KDF false]'s declared import
    is the full [KDF_in] superset, so the env ID must pass it through. *)
  Definition I_ae_env :=
    [interface
      #val #[ GEN_SS ] : 'sess → 'unit ;
      #val #[ GET_SS ] : 'sess → 'ss ;
      #val #[ SET_K ] : 'sess × 'key → 'unit ;
      #val #[ GEN_K ] : 'sess → 'unit ;
      #val #[ DERIVE ] : 'ss × 'info → 'key
    ].

  Definition GAE (b : bool) : raw_package :=
    (par (ID I_ae_env) (AEADP b)) ∘ CORE true.

  Definition R_ae : raw_package :=
    MOD ∘ (par (DHKEM false) (par (KDF false) (ID AEAD_out))).

  (** * Hop lemmas (assembly only; each is an interchange/Advantage_link
    re-association mirroring KEMDEM's [single_key_a] proof — no
    probabilistic content). *)

  Lemma hop_dhkem :
    ∀ A,
      fcompat KDF_loc AEAD_loc →
      AdvantageE (HPKE_pkg true true true) (HPKE_pkg false true true) A =
      AdvantageE (GDH true) (GDH false) (A ∘ R_dh).
  Proof.
    intros A hloc.
    unfold HPKE_pkg, SLOTS, GDH, R_dh.
    rewrite -Advantage_link.
    have factor_dh : forall b : bool,
      par (DHKEM b) (par (KDF true) (AEADP true)) =
      (par (ID DHKEM_out) (par (KDF true) (AEADP true))) ∘
        (par (DHKEM b) (ID I_dh_env)).
    { intro b.
      erewrite <- interchange.
      2-6: ssprove_valid.
      1: rewrite id_link.
      1: erewrite link_id.
      1: reflexivity.
      1: ssprove_valid.
      apply fsep.
      rewrite -(valid_domm (DHKEM_valid b)) -(valid_domm (valid_ID I_dh_env)).
      fmap_solve.
    }
    rewrite (factor_dh true) (factor_dh false).
    rewrite -!link_assoc.
    rewrite (link_assoc A MOD (par (ID DHKEM_out) (par (KDF true) (AEADP true)))).
    rewrite (Advantage_link (GDH true) (GDH false) (A ∘ MOD)
      (par (ID DHKEM_out) (par (KDF true) (AEADP true)))).
    reflexivity.
  Qed.

  Lemma hop_kdf :
    ∀ A,
      fcompat DHKEM_loc AEAD_loc →
      AdvantageE (HPKE_pkg false true true) (HPKE_pkg false false true) A =
      AdvantageE (GKDF true) (GKDF false) (A ∘ R_kdf).
  Proof.
    intros A hloc.
    unfold HPKE_pkg, SLOTS, GKDF, R_kdf.
    rewrite -Advantage_link.
    have reassoc_kdf : forall b : bool,
      par (DHKEM false) (par (KDF b) (AEADP true)) =
      par (KDF b) (par (DHKEM false) (AEADP true)).
    { intro b.
      rewrite par_assoc.
      rewrite (par_commut (DHKEM false) (pack (KDF b))).
      1: {
        apply fsep.
        rewrite -(valid_domm (DHKEM_valid false)) -(valid_domm (KDF b).(pack_valid)).
        fmap_solve.
      }
      rewrite -par_assoc.
      reflexivity.
    }
    rewrite (reassoc_kdf true) (reassoc_kdf false).
    have factor_kdf : forall b : bool,
      par (KDF b) (par (DHKEM false) (AEADP true)) =
      (par (ID KDF_out) (par (DHKEM false) (AEADP true))) ∘
        (par (KDF b) (ID I_kdf_env)).
    { intro b.
      erewrite <- interchange.
      2-6: ssprove_valid.
      rewrite id_link. erewrite link_id.
      1: reflexivity.
      1: ssprove_valid.
    }
    have commute_kdf : forall b : bool,
      par (KDF b) (ID I_kdf_env) = par (ID I_kdf_env) (KDF b).
    { intro b.
      apply par_commut.
      apply fsep.
      rewrite -(valid_domm (KDF b).(pack_valid)) -(valid_domm (valid_ID I_kdf_env)).
      fmap_solve.
    }
    have reassoc_fixed : par (ID KDF_out) (par (DHKEM false) (AEADP true)) =
      par (DHKEM false) (par (ID KDF_out) (AEADP true)).
    { rewrite par_assoc.
      rewrite (par_commut (pack (ID KDF_out)) (DHKEM false)).
      1: {
        apply fsep.
        rewrite -(valid_domm (valid_ID KDF_out)) -(valid_domm (DHKEM_valid false)).
        fmap_solve.
      }
      rewrite -par_assoc.
      reflexivity.
    }
    rewrite (factor_kdf true) (factor_kdf false).
    rewrite (commute_kdf true) (commute_kdf false) reassoc_fixed.
    rewrite -!link_assoc.
    rewrite (link_assoc A MOD (par (DHKEM false) (par (ID KDF_out) (AEADP true)))).
    rewrite (Advantage_link (GKDF true) (GKDF false) (A ∘ MOD)
      (par (DHKEM false) (par (ID KDF_out) (AEADP true)))).
    reflexivity.
  Qed.

  Lemma hop_aead :
    ∀ A,
      fcompat DHKEM_loc AEAD_loc →
      fcompat KDF_loc AEAD_loc →
      fcompat DHKEM_loc KDF_loc →
      AdvantageE (HPKE_pkg false false true) (HPKE_pkg false false false) A =
      AdvantageE (GAE true) (GAE false) (A ∘ R_ae).
  Proof.
    intros A hloc hloc2 hloc3.
    unfold HPKE_pkg, SLOTS, GAE, R_ae.
    rewrite -Advantage_link.
    rewrite !par_assoc.
    have factor_ae : forall b : bool,
      par (par (DHKEM false) (KDF false)) (AEADP b) =
      (par (par (DHKEM false) (KDF false)) (ID AEAD_out)) ∘
        (par (ID I_ae_env) (AEADP b)).
    { intro b.
      erewrite <- interchange.
      2-6: ssprove_valid.
      1: erewrite link_id.
      1: erewrite id_link.
      1: reflexivity.
      1: ssprove_valid.
      1: ssprove_valid.
      apply fsep.
      rewrite -(valid_domm (valid_ID I_ae_env)) -(valid_domm (AEAD_valid b)).
      fmap_solve.
    }
    rewrite (factor_ae true) (factor_ae false).
    rewrite -(par_assoc (DHKEM false) (KDF false) (pack (ID AEAD_out))).
    rewrite -!link_assoc.
    rewrite (link_assoc A MOD (par (DHKEM false) (par (KDF false) (ID AEAD_out)))).
    rewrite (Advantage_link (GAE true) (GAE false) (A ∘ MOD)
      (par (DHKEM false) (par (KDF false) (ID AEAD_out)))).
    reflexivity.
  Qed.

  (** * Main theorem: the 3-hop KEMDEM-style bound.

    No explicit q anywhere — q lives in the games (handle types, and the
    memoised call discipline). All q-dependence surfaces upon
    instantiating the three per-hop advantages (see [GKDF_bound] below
    for the KDF one). *)

  Theorem HPKE_security :
    ∀ LA (A : raw_package),
      fcompat DHKEM_loc AEAD_loc →
      fcompat KDF_loc AEAD_loc →
      fcompat DHKEM_loc KDF_loc →
      ValidPackage LA MOD_out A_export A →
      AdvantageE (HPKE true) (HPKE false) A <=
        AdvantageE (GDH true) (GDH false) (A ∘ R_dh) +
        AdvantageE (GKDF true) (GKDF false) (A ∘ R_kdf) +
        AdvantageE (GAE true) (GAE false) (A ∘ R_ae).
  Proof.
    intros LA A hloc hloc2 hloc3 vA.
    ssprove triangle (HPKE_pkg true true true) [::
      HPKE_pkg false true true ;
      HPKE_pkg false false true
    ] (HPKE_pkg false false false) A as ineq.
    eapply le_trans. 1: exact ineq.
    rewrite (hop_dhkem A hloc2) (hop_kdf A hloc) (hop_aead A hloc hloc2 hloc3).
    apply lexx.
  Qed.

  (** * Bridging the KDF hop to the abstract core (→ HKDF.v)

    The chain, and where each piece of knowledge about [KDFC] lives:

      GKDF true  =  glue ∘ KDFC true
         │  [GKDF_core_hop]  — pure package algebra; KDFC stays an opaque
         │  box on BOTH sides, so this is provable for ANY valid core.
         │  Cost: AdvantageE (KDFC true) (KDFC false) at [A ∘ R_core] —
         │  after substitution this is [security_of_KDF]'s LHS verbatim.
         ▼
      GKDF_mid   =  glue ∘ KDFC false
         │  [bridge, an HYPOTHESIS of GKDF_bound]  — "KDFC false really
         │  is the per-(ss,info) random function". This CANNOT be proven
         │  here (KDFC is a parameter; for a degenerate core the claim is
         │  simply false — e.g. a constant-output core is distinguishable
         │  from ideal through the GET_K passthrough). The instantiation
         │  discharges it: for [COUNT q ∘ KDF_ideal] it is a perfect
         │  equivalence because the glue's per-handle memoisation makes
         │  the COUNT throttle dead code ("dead-throttle" argument).
         ▼
      GKDF_mid_ref  =  glue ∘ KDFC_IDEAL          (fully concrete)
         │  [GKDF_mid_ref_ideal]  — the ss-collision up-to-bad, now a
         │  statement about two CONCRETE games; provable via Birthday.v
         │  at SS_N. Two sessions drawing the same ss share outputs in
         │  GKDF_mid_ref but not in GKDF false.
         ▼
      GKDF false =  per-session GEN_K ideal

    The real branch, by contrast, needs NO reference semantics: it only
    ever appears inside [GKDF_core_hop], on both sides of an equality, as
    an opaque box — its meaning is entirely the imported assumption's
    business. (Optionally, an instantiation may also prove
    [glue ∘ COUNT q ∘ KDF_real ≈₀ glue ∘ KDF_real] — the same
    dead-throttle argument on the real branch — to read the final theorem
    as being about the UNTHROTTLED protocol.) *)

  Definition GKDF_mid : raw_package :=
    (par (ID I_kdf_env) (KDF true)) ∘ CORE false.

  Definition R_core : raw_package :=
    (par (ID I_kdf_env) (KDF true)) ∘ (par KEYS (ID KDFC_out)).

  Definition birthday_ss : R := (q * q)%:R / (2 * SS_N)%:R.

  (** The REFERENCE ideal core: the per-(ss, info) lazily-sampled random
    function, concretely. This is what "the core's ideal branch" is
    REQUIRED to mean for the KDF hop to reach the per-session ideal —
    the semantic anchor that an abstract [KDFC false] cannot provide.
    (It is HKDF.v's [KDF_ideal] at this file's types, minus the COUNT
    throttle.) *)

  Definition ideal_tbl_loc := mkloc 44 (emptym : chMap ('ss × 'info) 'key).

  Definition KDFC_IDEAL_loc := [fmap ideal_tbl_loc ].

  Definition KDFC_IDEAL : package [interface] KDFC_out :=
    [package KDFC_IDEAL_loc ;
      #def #[ DERIVE ] ('(s, info) : 'ss × 'info) : 'key
      {
        T ← get ideal_tbl_loc ;;
        match getm T (s, info) with
        | Some k => ret k
        | None =>
            k <$ uniform Key_N ;;
            #put ideal_tbl_loc := setm T (s, info) k ;;
            ret k
        end
      }
    ].

  (** The reference middle game: the real glue over the reference ideal
    core. Fully concrete — no Context parameter occurs in it. *)
  Definition GKDF_mid_ref : raw_package :=
    (par (ID I_kdf_env) (KDF true)) ∘ (par KEYS KDFC_IDEAL).

  (** Reduction to the core: package algebra only, [KDFC] opaque.
    Provable for any valid core (same interchange/[Advantage_link]
    toolbox as [hop_dhkem]/[hop_kdf]/[hop_aead]; expect [trimmed]/
    [fcompat] premises to surface, as there). *)
  Lemma GKDF_core_hop :
    ∀ A,
      AdvantageE (GKDF true) GKDF_mid A =
      AdvantageE (KDFC true) (KDFC false) (A ∘ R_core).
  Proof.
    intro A.
    have core_absorb : forall bc,
      (par KEYS (ID KDFC_out)) ∘ (KDFC bc) = par KEYS (KDFC bc).
    {
      intro bc.
      replace (KDFC bc) with (par (ID (mkfmap [::] : Interface)) (KDFC bc)) at 1.
      2: {
        apply eq_fmap => n.
        rewrite /par unionmE mapimE //=.
      }
      erewrite <- interchange.
      2-6: ssprove_valid.
      rewrite link_id.
      rewrite id_link.
      reflexivity.
    }
    have eqT : GKDF true = R_core ∘ KDFC true.
    {
      unfold GKDF, CORE, R_core.
      rewrite -link_assoc core_absorb.
      reflexivity.
    }
    have eqF : GKDF_mid = R_core ∘ KDFC false.
    {
      unfold GKDF_mid, CORE, R_core.
      rewrite -link_assoc core_absorb.
      reflexivity.
    }
    rewrite eqT eqF.
    exact (esym (Advantage_link (KDFC true) (KDFC false) A R_core)).
  Qed.

  (** * The ss-collision instrumentation (scaffolding for [GKDF_mid_ref_ideal])

    [KEYS_bad] is [KEYS] with a ghost collision flag spliced into the two
    sites that draw a FRESH shared secret ([GEN_SS]'s and [GET_SS]'s
    None-branch): a fresh draw that already occurs in the ghost
    [used_ss_loc] set flips [bad_loc]; either way the draw is recorded in
    [used_ss_loc] and stored in [ss_tbl_loc] exactly as [KEYS] does. This
    is the SAME idiom as HKDF.v's [KDF_bad] (ghost [used_prk_loc]/
    [bad_loc] spliced into the "fresh prk" branch, dead w.r.t. the actual
    output) — here simpler because "fresh" only ever means "a NEW session
    handle's shared secret", never info-dependent. [SET_SS]/[SET_K]/
    [GEN_K]/[GET_K] are copied verbatim (no bad-relevant sampling there).

    [bad_loc] fires the moment two of the (at most [q], one per handle)
    shared secrets coincide — exactly the birthday-collision event that
    makes [GKDF_mid_ref] (real [DERIVE_K], hence real [KDFC_IDEAL] lookups
    keyed by (ss, info)) diverge from [GKDF false] (per-session
    independent [GEN_K]): a query into [KDFC_IDEAL] can only replay an
    EARLIER answer if its (ss, info) key repeats, and since [info] is
    adversary-chosen per call, the safe (bad-flag-only, not
    info-conditioned) over-approximation is "some two sessions' shared
    secrets coincide", matching [birthday_ss] = q²/(2·SS_N) (no Info_N
    dependence). *)

  Definition bad_loc := mkloc 45 (false : bool).
  Definition used_ss_loc := mkloc 46 (emptym : chMap SS 'unit).

  Definition KEYS_bad_loc := [fmap ss_tbl_loc ; k_tbl_loc ; bad_loc ; used_ss_loc ].

  Definition KEYS_bad : package [interface] KEYS_out :=
    [package KEYS_bad_loc ;
      #def #[ SET_SS ] ('(n, s) : 'sess × 'ss) : 'unit {
        T ← get ss_tbl_loc ;;
        match getm T n with
        | Some _ => ret tt
        | None => #put ss_tbl_loc := setm T n s ;; ret tt
        end
      } ;
      #def #[ GEN_SS ] (n : 'sess) : 'unit {
        T ← get ss_tbl_loc ;;
        match getm T n with
        | Some _ => ret tt
        | None =>
            s <$ uniform SS_N ;;
            U ← get used_ss_loc ;;
            (match getm U s with
             | Some _ => #put bad_loc := true ;; ret tt
             | None => #put used_ss_loc := setm U s tt ;; ret tt
             end) ;;
            #put ss_tbl_loc := setm T n s ;;
            ret tt
        end
      } ;
      #def #[ GET_SS ] (n : 'sess) : 'ss {
        T ← get ss_tbl_loc ;;
        match getm T n with
        | Some s => ret s
        | None =>
            s <$ uniform SS_N ;;
            U ← get used_ss_loc ;;
            (match getm U s with
             | Some _ => #put bad_loc := true ;; ret tt
             | None => #put used_ss_loc := setm U s tt ;; ret tt
             end) ;;
            #put ss_tbl_loc := setm T n s ;;
            ret s
        end
      } ;
      #def #[ SET_K ] ('(n, k) : 'sess × 'key) : 'unit {
        T ← get k_tbl_loc ;;
        match getm T n with
        | Some _ => ret tt
        | None => #put k_tbl_loc := setm T n k ;; ret tt
        end
      } ;
      #def #[ GEN_K ] (n : 'sess) : 'unit {
        T ← get k_tbl_loc ;;
        match getm T n with
        | Some _ => ret tt
        | None =>
            k <$ uniform Key_N ;;
            #put k_tbl_loc := setm T n k ;;
            ret tt
        end
      } ;
      #def #[ GET_K ] (n : 'sess) : 'key {
        T ← get k_tbl_loc ;;
        match getm T n with
        | Some k => ret k
        | None =>
            k <$ uniform Key_N ;;
            #put k_tbl_loc := setm T n k ;;
            ret k
        end
      }
    ].

  (** [KDF false]'s own [DERIVE_K] never calls [GET_SS] (it goes straight
    to [gen_k n]), unlike [KDF true]'s (which always calls [get_ss n]
    first). If [GKDF_bad_false] routed through plain [KDF false], its
    [ss_tbl_loc]/[used_ss_loc]/[bad_loc] bookkeeping would only ever grow
    via the adversary's own [GEN_SS] calls, while [GKDF_bad_mid_ref]'s
    (routed through [KDF true]) ALSO grows it on every [DERIVE_K] call for
    a session that was never [GEN_SS]'d — an extra, LHS-only sampling
    site. That breaks [eq_upto_bad_perf_ind]'s sync hypothesis
    (get_heap s₀ bad_loc = get_heap s₁ bad_loc for all invariant-related
    states), since after such a call [bad_loc] could flip on the LHS with
    literally no matching RHS code path to couple it against.

    [KDF_bad_false_glue] fixes this the same way [KDF_bad] fixes the
    analogous mismatch in HKDF.v: splice in a GHOST [get_ss n] call
    (discarding its result) at exactly the point [KDF true] would have
    made a real one, so both sides visit [GET_SS]'s collision-tracking
    code at the same call sites, in lockstep, and only then diverge into
    [derive]/[set_k] (LHS) vs [gen_k] (RHS). This is dead code w.r.t. the
    actual output (the discarded [s] never influences [gen_k]'s draw),
    exactly like [used_prk_loc]/[bad_loc] are dead w.r.t. [indep_loc] in
    HKDF.v's own [KDF_bad] — see [GKDF_bad_false_GKDF_false_equiv] below. *)
  Definition KDF_bad_false_glue : package KDF_in KDF_out :=
    [package KDF_loc ;
      #def #[ DERIVE_K ] ('(n, info) : 'sess × 'info) : 'unit {
        #import {sig #[ GET_SS ] : 'sess → 'ss } as get_ss ;;
        #import {sig #[ SET_K ] : 'sess × 'key → 'unit } as set_k ;;
        #import {sig #[ GEN_K ] : 'sess → 'unit } as gen_k ;;
        #import {sig #[ DERIVE ] : 'ss × 'info → 'key } as derive ;;
        D ← get kdone_loc ;;
        match getm D n with
        | Some _ => ret tt
        | None =>
            #put kdone_loc := setm D n tt ;;
            _ ← get_ss n ;;
            gen_k n
        end
      }
    ].

  (** Instrumented copies of the two games being compared, both routed
    through [KEYS_bad] (independent of the outer [b], exactly like
    [KEYS]); [GKDF_bad_mid_ref] additionally uses the real
    [DERIVE_K]/[KDFC_IDEAL] path, [GKDF_bad_false] the per-session
    [GEN_K] path (via [KDF_bad_false_glue], see its docstring for why a
    literal [KDF false] would NOT work here) — the pair
    [eq_upto_bad_perf_ind] relates. *)
  Definition GKDF_bad_mid_ref : raw_package :=
    (par (ID I_kdf_env) (KDF true)) ∘ (par KEYS_bad KDFC_IDEAL).

  (** NOTE: backed by [KDFC true] (matching [GKDF false]'s own [CORE true]
    bottom layer — recall [GKDF b := ... ∘ CORE true] for BOTH [b]s, see
    the header), NOT [KDFC_IDEAL]. [KDF_bad_false_glue]'s [DERIVE] import
    is dead code (never called — the [b = false] branch only ever calls
    [gen_k]), so which concrete package backs it is irrelevant to
    [GKDF_bad_false]'s own behaviour; using [KDFC true] here (rather than
    [KDFC_IDEAL]) is what makes [GKDF_bad_false_GKDF_false_equiv] below a
    same-code-plus-ghost-state argument instead of also having to relate
    two different [DERIVE] backends. *)
  Definition GKDF_bad_false : raw_package :=
    (par (ID I_kdf_env) KDF_bad_false_glue) ∘ (par KEYS_bad (KDFC true)).

  Lemma GKDF_bad_mid_ref_GKDF_mid_ref_equiv :
    ∀ LA (A : raw_package),
      ValidPackage LA (unionm I_kdf_env KDF_out) A_export A →
      fseparate LA (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc)) →
      fseparate LA (unionm KDF_loc (unionm KEYS_loc KDFC_IDEAL_loc)) →
      AdvantageE GKDF_bad_mid_ref GKDF_mid_ref A = 0.
  Proof.
    intros LA A vA hd0 hd1.
    have vID : ValidPackage emptym I_kdf_env I_kdf_env (ID I_kdf_env) by ssprove_valid.
    have vKDFt : ValidPackage KDF_loc KDF_in KDF_out (KDF true) by ssprove_valid.
    have vKEYSbad : ValidPackage KEYS_bad_loc [interface] KEYS_out KEYS_bad by ssprove_valid.
    have vKDFCI : ValidPackage KDFC_IDEAL_loc [interface] KDFC_out KDFC_IDEAL by ssprove_valid.
    have vP1 : ValidPackage (unionm emptym KDF_loc) (unionm I_kdf_env KDF_in)
      (unionm I_kdf_env KDF_out) (par (ID I_kdf_env) (KDF true)).
    { eapply valid_par.
      1: exact vID.
      1: exact vKDFt.
      all: fmap_solve. }
    have vP2 : ValidPackage (unionm KEYS_bad_loc KDFC_IDEAL_loc) (unionm [interface] [interface])
      (unionm KEYS_out KDFC_out) (par KEYS_bad KDFC_IDEAL).
    { eapply valid_par.
      1: exact vKEYSbad.
      1: exact vKDFCI.
      all: fmap_solve. }
    have v0 : ValidPackage (unionm (unionm emptym KDF_loc) (unionm KEYS_bad_loc KDFC_IDEAL_loc))
      (unionm [interface] [interface]) (unionm I_kdf_env KDF_out) GKDF_bad_mid_ref.
    { eapply valid_link_weak.
      1: exact vP1.
      1: exact vP2.
      all: fmap_solve. }
    have vKEYS : ValidPackage KEYS_loc [interface] KEYS_out KEYS by ssprove_valid.
    have vQ2 : ValidPackage (unionm KEYS_loc KDFC_IDEAL_loc) (unionm [interface] [interface])
      (unionm KEYS_out KDFC_out) (par KEYS KDFC_IDEAL).
    { eapply valid_par.
      1: exact vKEYS.
      1: exact vKDFCI.
      all: fmap_solve. }
    have v1 : ValidPackage (unionm (unionm emptym KDF_loc) (unionm KEYS_loc KDFC_IDEAL_loc))
      (unionm [interface] [interface]) (unionm I_kdf_env KDF_out) GKDF_mid_ref.
    { eapply valid_link_weak.
      1: exact vP1.
      1: exact vQ2.
      all: fmap_solve. }
    eapply eq_upto_inv_perf_ind.
    1: exact v0.
    1: exact v1.
    1: exact vA.
    1: eapply (INV'_heap_ignore (mkfmap [:: bad_loc; used_ss_loc])).
    1: fmap_solve.
    1: done.
    1: fmap_solve.
    1: fmap_solve.
    simplify_eq_rel arg.
    Ltac extract_base_inv h :=
      first [ exact h | destruct h as [h ?]; extract_base_inv h ].
    1:{
      apply: r_get_vs_get_remember => v.
      destruct (v arg) as [s0|] eqn:Hv.
      - rewrite Hv /=.
        apply: r_ret => s0' s1' h.
        split; [ reflexivity | extract_base_inv h ].
      - rewrite Hv /=.
        apply: r_uniform_bij => [|s].
        1: exists id; done.
        apply: r_get_remember_lhs => U.
        destruct (U s) as [[]|] eqn:HU.
        all: rewrite HU /=.
        all: apply: r_put_lhs.
        all: apply: r_put_vs_put.
        all: ssprove_restore_mem; last by apply: r_ret.
        all: by ssprove_invariant.
    }
    1:{
      apply: r_get_vs_get_remember => v.
      destruct (v arg) as [k|] eqn:Hv.
      - rewrite Hv /=.
        apply: r_ret => s0 s1 h.
        split; [ reflexivity | extract_base_inv h ].
      - rewrite Hv /=.
        apply: r_uniform_bij => [|k].
        1: exists id; done.
        apply: r_put_vs_put.
        ssprove_restore_mem; last by apply: r_ret.
        by ssprove_invariant.
    }
    destruct arg as [n info].
    ssprove_code_simpl.
    apply: r_get_vs_get_remember => D.
    destruct (D n) as [[]|] eqn:HD.
    - rewrite HD /=.
      apply: r_ret => s0 s1 h.
      split; [ reflexivity | extract_base_inv h ].
    - rewrite HD /=.
      apply: r_put_lhs.
      apply: r_put_rhs.
      ssprove_restore_mem; [ by ssprove_invariant | ].
      simplify_linking.
      apply: r_get_vs_get_remember => v.
      destruct (v n) as [s|] eqn:Hv.
      1:{
        rewrite Hv /=.
        apply: r_get_vs_get_remember => v2.
        destruct (v2 (s, info)) as [k|] eqn:Hv2.
        1:{
          rewrite Hv2 /=.
          apply: r_get_vs_get_remember => v3.
          destruct (v3 n) as [[]|] eqn:Hv3.
          1:{ rewrite Hv3 /=. apply: r_ret => s0 s1 h. split; [ reflexivity | extract_base_inv h ]. }
          1:{ rewrite Hv3 /=. apply: r_put_vs_put. ssprove_restore_mem; last by apply: r_ret. by ssprove_invariant. }
        }
        1:{
          rewrite Hv2 /=.
          apply: r_uniform_bij => [|k].
          1: exists id; done.
          apply: r_put_vs_put.
          ssprove_restore_mem; [ by ssprove_invariant | ].
          apply: r_get_vs_get_remember => v3.
          destruct (v3 n) as [[]|] eqn:Hv3.
          1:{ rewrite Hv3 /=. apply: r_ret => s0 s1 h. split; [ reflexivity | extract_base_inv h ]. }
          1:{ rewrite Hv3 /=. apply: r_put_vs_put. ssprove_restore_mem; last by apply: r_ret. by ssprove_invariant. }
        }
      }
      rewrite Hv /=.
      apply: r_uniform_bij => [|s].
      1: exists id; done.
      apply: r_get_remember_lhs => U.
      destruct (U s) as [[]|] eqn:HU.
      1:{
        rewrite HU /=.
        apply: r_put_lhs.
        apply: r_put_vs_put.
        ssprove_restore_mem; [ by ssprove_invariant | ].
        apply: r_get_vs_get_remember => v2.
        destruct (v2 (s, info)) as [k|] eqn:Hv2.
        1:{
          rewrite Hv2 /=.
          apply: r_get_vs_get_remember => v3.
          destruct (v3 n) as [[]|] eqn:Hv3.
          1:{ rewrite Hv3 /=. apply: r_ret => s0 s1 h. split; [ reflexivity | extract_base_inv h ]. }
          1:{ rewrite Hv3 /=. apply: r_put_vs_put. ssprove_restore_mem; last by apply: r_ret. by ssprove_invariant. }
        }
        1:{
          rewrite Hv2 /=.
          apply: r_uniform_bij => [|k].
          1: exists id; done.
          apply: r_put_vs_put.
          ssprove_restore_mem; [ by ssprove_invariant | ].
          apply: r_get_vs_get_remember => v3.
          destruct (v3 n) as [[]|] eqn:Hv3.
          1:{ rewrite Hv3 /=. apply: r_ret => s0 s1 h. split; [ reflexivity | extract_base_inv h ]. }
          1:{ rewrite Hv3 /=. apply: r_put_vs_put. ssprove_restore_mem; last by apply: r_ret. by ssprove_invariant. }
        }
      }
      1:{
        rewrite HU /=.
        apply: r_put_lhs.
        apply: r_put_vs_put.
        ssprove_restore_mem; [ by ssprove_invariant | ].
        apply: r_get_vs_get_remember => v2.
        destruct (v2 (s, info)) as [k|] eqn:Hv2.
        1:{
          rewrite Hv2 /=.
          apply: r_get_vs_get_remember => v3.
          destruct (v3 n) as [[]|] eqn:Hv3.
          1:{ rewrite Hv3 /=. apply: r_ret => s0 s1 h. split; [ reflexivity | extract_base_inv h ]. }
          1:{ rewrite Hv3 /=. apply: r_put_vs_put. ssprove_restore_mem; last by apply: r_ret. by ssprove_invariant. }
        }
        1:{
          rewrite Hv2 /=.
          apply: r_uniform_bij => [|k].
          1: exists id; done.
          apply: r_put_vs_put.
          ssprove_restore_mem; [ by ssprove_invariant | ].
          apply: r_get_vs_get_remember => v3.
          destruct (v3 n) as [[]|] eqn:Hv3.
          1:{ rewrite Hv3 /=. apply: r_ret => s0 s1 h. split; [ reflexivity | extract_base_inv h ]. }
          1:{ rewrite Hv3 /=. apply: r_put_vs_put. ssprove_restore_mem; last by apply: r_ret. by ssprove_invariant. }
        }
      }
  Qed.

  Lemma GKDF_bad_false_GKDF_false_equiv :
    ∀ LA (A : raw_package),
      fcompat KDF_loc KDFC_loc →
      fcompat KEYS_loc KDFC_loc →
      fcompat KEYS_bad_loc KDFC_loc →
      ValidPackage LA (unionm I_kdf_env KDF_out) A_export A →
      fseparate LA (unionm KDF_loc (unionm KEYS_bad_loc KDFC_loc)) →
      fseparate LA (unionm KDF_loc (unionm KEYS_loc KDFC_loc)) →
      AdvantageE GKDF_bad_false (GKDF false) A = 0.
  Proof.
    intros LA A hcompD hcomp' hcomp vA hd0 hd1.
    have vID : ValidPackage emptym I_kdf_env I_kdf_env (ID I_kdf_env) by ssprove_valid.
    have vGlue : ValidPackage KDF_loc KDF_in KDF_out KDF_bad_false_glue by ssprove_valid.
    have vKDFf : ValidPackage KDF_loc KDF_in KDF_out (KDF false) by ssprove_valid.
    have vKEYSbad : ValidPackage KEYS_bad_loc [interface] KEYS_out KEYS_bad by ssprove_valid.
    have vKEYS : ValidPackage KEYS_loc [interface] KEYS_out KEYS by ssprove_valid.
    have vKDFCt : ValidPackage KDFC_loc [interface] KDFC_out (KDFC true) := KDFC_valid true.
    have vP1 : ValidPackage (unionm emptym KDF_loc) (unionm I_kdf_env KDF_in)
      (unionm I_kdf_env KDF_out) (par (ID I_kdf_env) KDF_bad_false_glue).
    { eapply valid_par.
      1: exact vID.
      1: exact vGlue.
      all: fmap_solve. }
    have vP1' : ValidPackage (unionm emptym KDF_loc) (unionm I_kdf_env KDF_in)
      (unionm I_kdf_env KDF_out) (par (ID I_kdf_env) (KDF false)).
    { eapply valid_par.
      1: exact vID.
      1: exact vKDFf.
      all: fmap_solve. }
    have vP2 : ValidPackage (unionm KEYS_bad_loc KDFC_loc) (unionm [interface] [interface])
      (unionm KEYS_out KDFC_out) (par KEYS_bad (KDFC true)).
    { eapply valid_par.
      1: exact vKEYSbad.
      1: exact vKDFCt.
      all: fmap_solve. }
    have vP2' : ValidPackage (unionm KEYS_loc KDFC_loc) (unionm [interface] [interface])
      (unionm KEYS_out KDFC_out) (par KEYS (KDFC true)).
    { eapply valid_par.
      1: exact vKEYS.
      1: exact vKDFCt.
      all: fmap_solve. }
    have v0 : ValidPackage (unionm (unionm emptym KDF_loc) (unionm KEYS_bad_loc KDFC_loc))
      (unionm [interface] [interface]) (unionm I_kdf_env KDF_out) GKDF_bad_false.
    { eapply valid_link_weak.
      1: exact vP1.
      1: exact vP2.
      all: fmap_solve. }
    have v1 : ValidPackage (unionm (unionm emptym KDF_loc) (unionm KEYS_loc KDFC_loc))
      (unionm [interface] [interface]) (unionm I_kdf_env KDF_out) (GKDF false).
    { eapply valid_link_weak.
      1: exact vP1'.
      1: exact vP2'.
      all: fmap_solve. }
    eapply eq_upto_inv_perf_ind.
    1: exact v0.
    1: exact v1.
    1: exact vA.
    1: eapply (INV'_heap_ignore (mkfmap [:: ss_tbl_loc; bad_loc; used_ss_loc])).
    1: fmap_solve.
    1: done.
    1: fmap_solve.
    1: fmap_solve.
    simplify_eq_rel arg.
    1:{
      apply: r_get_remember_lhs => vL.
      apply: r_get_remember_rhs => vR.
      destruct (vL arg) as [s0|] eqn:HvL.
      1:{ rewrite HvL /=.
        destruct (vR arg) as [s1|] eqn:HvR.
        1:{ rewrite HvR /=.
          apply: r_ret => s0' s1' h.
          split; [ reflexivity | extract_base_inv h ].
        }
        1:{ rewrite HvR /=.
          apply: r_const_sample_R.
          move=> s1.
          apply: r_put_rhs.
          ssprove_restore_mem; last by apply: r_ret.
          by ssprove_invariant.
        }
      }
      1:{ rewrite HvL /=.
        apply: r_const_sample_L.
        move=> s0.
        apply: r_get_remember_lhs => U.
        destruct (U s0) as [[]|] eqn:HU.
        1:{ rewrite HU /=.
          apply: r_put_lhs.
          apply: r_put_lhs.
          destruct (vR arg) as [s1|] eqn:HvR.
          1:{ rewrite HvR /=.
            ssprove_restore_mem; last by apply: r_ret.
            by ssprove_invariant.
          }
          1:{ rewrite HvR /=.
            apply: r_const_sample_R.
            move=> s1.
            apply: r_put_rhs.
            ssprove_restore_mem; last by apply: r_ret.
            by ssprove_invariant.
          }
        }
        1:{ rewrite HU /=.
          apply: r_put_lhs.
          apply: r_put_lhs.
          destruct (vR arg) as [s1|] eqn:HvR.
          1:{ rewrite HvR /=.
            ssprove_restore_mem; last by apply: r_ret.
            by ssprove_invariant.
          }
          1:{ rewrite HvR /=.
            apply: r_const_sample_R.
            move=> s1.
            apply: r_put_rhs.
            ssprove_restore_mem; last by apply: r_ret.
            by ssprove_invariant.
          }
        }
      }
    }
    1:{
      apply: r_get_vs_get_remember => v.
      destruct (v arg) as [k|] eqn:Hv.
      - rewrite Hv /=.
        apply: r_ret => s0 s1 h.
        split; [ reflexivity | extract_base_inv h ].
      - rewrite Hv /=.
        apply: r_uniform_bij => [|k].
        1: exists id; done.
        apply: r_put_vs_put.
        ssprove_restore_mem; last by apply: r_ret.
        by ssprove_invariant.
    }
    destruct arg as [n info].
    ssprove_code_simpl.
    apply: r_get_vs_get_remember => D.
    destruct (D n) as [[]|] eqn:HD.
    - rewrite HD /=.
      apply: r_ret => s0 s1 h.
      split; [ reflexivity | extract_base_inv h ].
    - rewrite HD /=.
      apply: r_put_lhs.
      apply: r_put_rhs.
      ssprove_restore_mem; [ by ssprove_invariant | ].
      simplify_linking.
      apply: r_get_remember_lhs => v.
      destruct (v n) as [s|] eqn:Hv.
      1:{ rewrite Hv /=.
        apply: r_get_vs_get_remember => v2.
        destruct (v2 n) as [k|] eqn:Hv2.
        1:{ rewrite Hv2 /=.
          apply: r_ret => s0 s1 h.
          split; [ reflexivity | extract_base_inv h ].
        }
        1:{ rewrite Hv2 /=.
          apply: r_uniform_bij => [|k].
          1: exists id; done.
          apply: r_put_vs_put.
          ssprove_restore_mem; last by apply: r_ret.
          by ssprove_invariant.
        }
      }
      1:{ rewrite Hv /=.
        apply: r_const_sample_L.
        move=> s.
        apply: r_get_remember_lhs => U.
        destruct (U s) as [[]|] eqn:HU.
        1:{ rewrite HU /=.
          apply: r_put_lhs.
          apply: r_put_lhs.
          ssprove_restore_mem; [ by ssprove_invariant | ].
          apply: r_get_vs_get_remember => v2.
          destruct (v2 n) as [k|] eqn:Hv2.
          1:{ rewrite Hv2 /=.
            apply: r_ret => s0 s1 h.
            split; [ reflexivity | extract_base_inv h ].
          }
          1:{ rewrite Hv2 /=.
            apply: r_uniform_bij => [|k].
            1: exists id; done.
            apply: r_put_vs_put.
            ssprove_restore_mem; last by apply: r_ret.
            by ssprove_invariant.
          }
        }
        1:{ rewrite HU /=.
          apply: r_put_lhs.
          apply: r_put_lhs.
          ssprove_restore_mem; [ by ssprove_invariant | ].
          apply: r_get_vs_get_remember => v2.
          destruct (v2 n) as [k|] eqn:Hv2.
          1:{ rewrite Hv2 /=.
            apply: r_ret => s0 s1 h.
            split; [ reflexivity | extract_base_inv h ].
          }
          1:{ rewrite Hv2 /=.
            apply: r_uniform_bij => [|k].
            1: exists id; done.
            apply: r_put_vs_put.
            ssprove_restore_mem; last by apply: r_ret.
            by ssprove_invariant.
          }
        }
      }
  Qed.

  (** Local copy of HPKE_HKDF.v's own 8-line helper (cannot import that
    file; task instructions require duplicating it here): the domain of
    a [chMap] keyed by ['fin n] has size at most [n], since ['fin n]'s
    enumeration already has that size and [domm] is duplicate-free. *)
  Lemma domm_fin_bound (n : nat) (X : choice_type) (m : chMap ('fin n) X) :
    (size (domm m) <= n)%N.
  Proof.
    have hle : (size (domm m) <= size (enum 'I_n))%N.
    { apply: uniq_leq_size.
      - exact: uniq_fset.
      - move=> x _; exact: mem_enum. }
    by rewrite size_enum_ord in hle.
  Qed.

  (** The ss-collision birthday step, now between two CONCRETE games.

    Steps 1 (the two dead-ghost-code equivalences,
    [GKDF_bad_mid_ref_GKDF_mid_ref_equiv] / [GKDF_bad_false_GKDF_false_equiv]
    above) are Qed'd in full, mirroring HKDF.v's [KDF_bad_KDF_ideal_equiv]/
    [KDF_mid_KDF_mid'_equiv].

    Steps 2-3 — [eq_upto_bad_perf_ind] (pkg_upto_bad.v) applied to
    [GKDF_bad_mid_ref]/[GKDF_bad_false] at [bad_loc] (needing an
    [Invariant] coupling the two games' [ss_tbl_loc]/[k_tbl_loc]/
    [used_ss_loc]/[bad_loc] plus two [bad_preserved] proofs, mirroring
    HKDF.v's [KDF_mid'_bad_inv]/[KDF_mid'_bad_preserved]/
    [KDF_bad_bad_preserved]/[KDF_mid'_KDF_bad_eq_up_to_bad] ~L602-1521),
    THEN bounding the resulting [Pr_bad] by [birthday_ss] via a
    structural induction over the adversary's resolved code (mirroring
    HKDF.v's [Pr_bad_adv_bound], HKDF.v:6333-6651, ~320 lines, itself
    documented there as a bespoke, game-shape-specific argument with NO
    reusable bridge from [Pr_bad] to Birthday.v elsewhere in the shared
    infrastructure) — feed [GKDF_bad_mid_ref_GKDF_bad_false_bound] below,
    which is Qed'd. Both steps are NOW Qed'd IN FULL: step 2's relational
    content ([GKDF_bad_mid_ref_GKDF_bad_false_eq_up_to_bad]) is Qed'd in
    full; step 3's counting argument ([Pr_bad_GKDF_bad_mid_ref_bound]) is
    Qed'd in terms of [Pr_bad_GKDF_bad_mid_ref_adv_bound] (the bespoke
    adversary-code induction itself), which is ALSO now Qed'd in full —
    see its own docstring ~L3606 below for the induction's shape. The
    [GKDF_bad] instance IS SIMPLER than HKDF's, as anticipated below: shared
    secrets are drawn once per handle regardless of adversary strategy —
    no adversary-chosen ss -> prk indirection — and bounded by [q]
    directly via the handle type ['fin q], e.g. via a
    [domm_fin_bound]-style lemma: [size (domm (m : chMap ('fin q) X)) <=
    q], by [uniq_leq_size]/[card_ord] — see HPKE_HKDF.v's own copy of
    this 8-line helper), but still requires an induction of comparable
    shape to HKDF's. *)

  (** * Step (c): the up-to-bad coupling invariant

    Unlike HKDF.v's [KDF_mid'_locs]/[KDF_bad_locs] (two DISJOINT location
    sets, needing [lhs]/[rhs]-tagged [rel_app] pairs to relate DIFFERENT
    location ids across sides), [GKDF_bad_mid_ref] and [GKDF_bad_false]
    both route through [KEYS_bad] and (the same) [KDF_loc] — i.e. the SAME
    location ids ([kdone_loc], [ss_tbl_loc], [used_ss_loc], [bad_loc]) on
    both sides, just two separate heap instances. So the coupling is
    mostly literal equality ("syncs") of those tables, gated on
    [bad_loc = false] exactly as [KDF_mid'_bad_inv] gates its own
    [T = T' /\ ...] conjunct. The one genuinely relational fact is
    [k_tbl_loc]: [GKDF_bad_mid_ref] populates it via [KDFC_IDEAL]'s
    [ideal_tbl_loc] (keyed by [(ss, info)]), [GKDF_bad_false] via a fresh
    per-session [GEN_K] draw (keyed directly by session) — as long as no
    two sessions ever shared a shared secret (bad = false), each
    session's [(ss, info)] key into [ideal_tbl_loc] is guaranteed FRESH
    (see [ideal_fresh] below), so the two draws couple as literally the
    same uniform sample, keeping [k_tbl_loc] equal on both sides too. *)

  (** [used_ss_loc]'s domain is exactly [ss_tbl_loc]'s range: the
    session-side analogue of HKDF's [used_prk_correspondence]. *)
  Definition ss_used_correspondence
    (T : chMap SESS SS) (U : chMap SS 'unit) : Prop :=
    ∀ s, getm U s = Some tt ↔ (∃ n, getm T n = Some s).

  (** [ss_tbl_loc] is injective on its domain: the session-side analogue
    of HKDF's [extract_injective] (a consequence of [bad_loc] only ever
    firing on a genuine collision). *)
  Definition ss_tbl_injective (T : chMap SESS SS) : Prop :=
    ∀ n1 n2 s, getm T n1 = Some s → getm T n2 = Some s → n1 = n2.

  (** [ideal_tbl_loc] only ever gains an entry keyed at an [(s, info)]
    whose [s] belongs to a session that has ALREADY COMPLETED its
    [DERIVE_K] call (tracked via [kdone_loc]) — the analogue of HKDF's
    [mid_loc_fresh]/[indep_loc_fresh], but strengthened to reference
    [kdone_loc] (not just [used_ss_loc]): combined with
    [ss_tbl_injective], this is what lets the DERIVE_K proof show
    [ideal_tbl_loc]'s lookup at THIS session's [(s, info)] is fresh
    regardless of whether [s] was assigned by an earlier [GEN_SS] call or
    freshly drawn right here — either way, [s] belongs EXCLUSIVELY to the
    current (not-yet-[kdone]) session, so no completed session could have
    written that key. *)
  Definition derive_fresh
    (D : chMap SESS 'unit) (T : chMap SESS SS) (TI : chMap ('ss × 'info) 'key) : Prop :=
    ∀ s info, getm TI (s, info) <> None →
      ∃ n, getm D n = Some tt ∧ getm T n = Some s.

  Definition GKDF_bad_bad_locs :=
    unionm (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc))
           (unionm KDF_loc (unionm KEYS_bad_loc KDFC_loc)).

  Definition GKDF_bad_bad_inv : precond :=
    heap_ignore GKDF_bad_bad_locs ⋊
    syncs bad_loc ⋊
    rel_app [:: (lhs, bad_loc); (lhs, kdone_loc); (lhs, ss_tbl_loc); (lhs, used_ss_loc);
                (lhs, k_tbl_loc); (lhs, ideal_tbl_loc);
                (rhs, kdone_loc); (rhs, ss_tbl_loc); (rhs, used_ss_loc); (rhs, k_tbl_loc)]
      (fun b D T U K TI D' T' U' K' =>
         b = false →
         D = D' ∧ T = T' ∧ U = U' ∧ K = K'
         ∧ ss_used_correspondence T U ∧ ss_tbl_injective T ∧ derive_fresh D T TI).

  Lemma GKDF_bad_bad_Invariant :
    Invariant (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc))
              (unionm KDF_loc (unionm KEYS_bad_loc KDFC_loc))
              GKDF_bad_bad_inv.
  Proof.
    eapply Invariant_inv_conj.
    - eapply Invariant_inv_conj.
      + eapply Invariant_heap_ignore. exact: fsubmapxx.
      + eapply SemiInvariant_relApp.
        * ssprove_invariant.
        * done.
    - eapply SemiInvariant_relApp.
      + ssprove_invariant.
      + simpl. move=> _. repeat split=>//.
        move=> [n Hn]. move: Hn. by rewrite /heap_init.
  Qed.

  (** Small rewriting helper used to reach the flattened per-op code
    (as [ssprove_code_simpl] does on relational goals, but here for the
    UNARY [bad_lossless] goals [bad_preserved] needs): [eapply
    bad_lossless_rw] leaves [?c' = c] as a goal with a fresh evar on the
    LEFT and the concrete term on the RIGHT — exactly the shape
    [ssprove_match_commut_gen] (pkg_user_util.v) is built to walk down
    via [code_link_bind]/[resolve_par]-style congruence, instantiating
    [?c'] to the fully flattened code as a side effect. *)
  Lemma bad_lossless_rw {A : choiceType} (bad_id : nat) (c c' : raw_code A) (h : heap) :
    c' = c -> bad_lossless bad_id c' h -> bad_lossless bad_id c h.
  Proof. move=> -> //. Qed.

  (** The same trick, specialised to each side of a relational
    [⊢ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄] judgement: [eapply code_link_rw_lhs]
    (resp. [_rhs]) leaves [?c' = c] with the evar on the left, again
    exactly [ssprove_match_commut_gen]'s shape, letting it flatten a
    [code_link (match ... with ... end) (par ...)] term stuck on an
    abstract scrutinee (as [GKDF_bad_mid_ref]/[GKDF_bad_false]'s
    [DERIVE_K] op produces, since it composes THROUGH the [KDF]
    package's own op-calls, unlike [GEN_SS]/[GET_K] which resolve
    directly against [KEYS_bad]) into the concrete per-branch code the
    rest of the up-to-bad proof needs. *)
  Lemma code_link_rw_lhs {A B : choiceType} (pre : precond) (post : postcond A B)
    (c c' : raw_code A) (c2 : raw_code B) :
    c' = c -> ⊢ ⦃ pre ⦄ c' ≈ c2 ⦃ post ⦄ -> ⊢ ⦃ pre ⦄ c ≈ c2 ⦃ post ⦄.
  Proof. move=> -> //. Qed.

  Lemma code_link_rw_rhs {A B : choiceType} (pre : precond) (post : postcond A B)
    (c1 : raw_code A) (c c' : raw_code B) :
    c' = c -> ⊢ ⦃ pre ⦄ c1 ≈ c' ⦃ post ⦄ -> ⊢ ⦃ pre ⦄ c1 ≈ c ⦃ post ⦄.
  Proof. move=> -> //. Qed.

  Lemma GKDF_bad_mid_ref_bad_preserved :
    bad_preserved (unionm I_kdf_env KDF_out) 45 GKDF_bad_mid_ref.
  Proof.
    move=> id S T x h has Hb.
    fmap_invert has.
    all: simplify_linking.
    1: {
      have Hlv : lossless_valid (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc))
        (v ← get ss_tbl_loc ;;
         b ← match v x with
             | Some _ => ret tt
             | None =>
                 s ← sample uniform SS_N ;;
                 U ← get used_ss_loc ;;
                 match U s with
                 | Some _ => #put bad_loc := true ;; ret tt
                 | None => #put used_ss_loc := setm U s tt ;; ret tt
                 end ;;
                 #put ss_tbl_loc := setm v x s ;;
                 ret tt
             end ;;
         ret b).
      { apply: lv_getr; [fmap_solve | move=> v; case: (v x) => [ss1|] /=].
        - exact: lv_ret.
        - apply: lv_sampler => s.
          apply: lv_getr; [fmap_solve | move=> U; case: (U s) => [[]|] /=].
          + apply: lv_putr; [fmap_solve | apply: lv_putr; [fmap_solve | exact: lv_ret]].
          + apply: lv_putr; [fmap_solve | apply: lv_putr; [fmap_solve | exact: lv_ret]]. }
      have Hm : bad_loc_monotone 45
        (v ← get ss_tbl_loc ;;
         b ← match v x with
             | Some _ => ret tt
             | None =>
                 s ← sample uniform SS_N ;;
                 U ← get used_ss_loc ;;
                 match U s with
                 | Some _ => #put bad_loc := true ;; ret tt
                 | None => #put used_ss_loc := setm U s tt ;; ret tt
                 end ;;
                 #put ss_tbl_loc := setm v x s ;;
                 ret tt
             end ;;
         ret b).
      { apply: blm_getr => v. case: (v x) => [ss1|] /=.
        - exact: blm_ret.
        - apply: blm_sampler => s. apply: blm_getr => U. case: (U s) => [[]|] /=.
          + apply: blm_putr_bad. apply: blm_putr_other; [done | exact: blm_ret].
          + apply: blm_putr_other; [done | apply: blm_putr_other; [done | exact: blm_ret]]. }
      exact: (Pr_code_lossless_bad (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc)) _ Hlv Hm h Hb).
    }
    1: {
      have Hlv : lossless_valid (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc))
        (v ← get k_tbl_loc ;;
         b ← match v x with
             | Some k => ret k
             | None =>
                 k ← sample uniform Key_N ;;
                 #put k_tbl_loc := setm v x k ;;
                 ret k
             end ;;
         ret b).
      { apply: lv_getr; [fmap_solve | move=> v; case: (v x) => [k0|] /=].
        - exact: lv_ret.
        - apply: lv_sampler => k. apply: lv_putr; [fmap_solve | exact: lv_ret]. }
      have Hm : bad_loc_monotone 45
        (v ← get k_tbl_loc ;;
         b ← match v x with
             | Some k => ret k
             | None =>
                 k ← sample uniform Key_N ;;
                 #put k_tbl_loc := setm v x k ;;
                 ret k
             end ;;
         ret b).
      { apply: blm_getr => v. case: (v x) => [k0|] /=.
        - exact: blm_ret.
        - apply: blm_sampler => k. apply: blm_putr_other; [done | exact: blm_ret]. }
      exact: (Pr_code_lossless_bad (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc)) _ Hlv Hm h Hb).
    }
    case: x => n info /=.
    eapply bad_lossless_rw.
    1: solve [ssprove_match_commut_gen].
    have Htail_lv : forall s : SS, lossless_valid (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc))
      (TI ← get ideal_tbl_loc ;;
       match TI (s, info) with
       | Some k => K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
       | None => k ← sample uniform Key_N ;; #put ideal_tbl_loc := setm TI (s, info) k ;; K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
       end).
    { move=> s. apply: lv_getr; [fmap_solve | move=> TI; case: (TI (s,info)) => [k|] /=].
      - apply: lv_getr; [fmap_solve | move=> K; case: (K n) => [k0|] /=].
        + exact: lv_ret.
        + apply: lv_putr; [fmap_solve | exact: lv_ret].
      - apply: lv_sampler => k. apply: lv_putr; [fmap_solve |
          apply: lv_getr; [fmap_solve | move=> K; case: (K n) => [k0|] /=] ].
        + exact: lv_ret.
        + apply: lv_putr; [fmap_solve | exact: lv_ret]. }
    have Hlv : lossless_valid (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc))
      (D ← get kdone_loc ;;
       match D n with
       | Some _ => ret tt
       | None =>
           #put kdone_loc := setm D n tt ;;
           T ← get ss_tbl_loc ;;
           match T n with
           | Some s =>
               TI ← get ideal_tbl_loc ;;
               match TI (s, info) with
               | Some k => K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
               | None => k ← sample uniform Key_N ;; #put ideal_tbl_loc := setm TI (s, info) k ;; K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
               end
           | None =>
               s ← sample uniform SS_N ;;
               U ← get used_ss_loc ;;
               match U s with
               | Some _ =>
                   #put bad_loc := true ;;
                   #put ss_tbl_loc := setm T n s ;;
                   TI ← get ideal_tbl_loc ;;
                   match TI (s, info) with
                   | Some k => K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                   | None => k ← sample uniform Key_N ;; #put ideal_tbl_loc := setm TI (s, info) k ;; K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                   end
               | None =>
                   #put used_ss_loc := setm U s tt ;;
                   #put ss_tbl_loc := setm T n s ;;
                   TI ← get ideal_tbl_loc ;;
                   match TI (s, info) with
                   | Some k => K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                   | None => k ← sample uniform Key_N ;; #put ideal_tbl_loc := setm TI (s, info) k ;; K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                   end
               end
           end
       end).
    { apply: lv_getr; [fmap_solve | move=> D; case: (D n) => [[]|] /=].
      - exact: lv_ret.
      - apply: lv_putr; [fmap_solve |
          apply: lv_getr; [fmap_solve | move=> T; case: (T n) => [s|] /=] ].
        + exact: (Htail_lv s).
        + apply: lv_sampler => s. apply: lv_getr; [fmap_solve | move=> U; case: (U s) => [[]|] /=].
          * apply: lv_putr; [fmap_solve | apply: lv_putr; [fmap_solve | exact: (Htail_lv s)]].
          * apply: lv_putr; [fmap_solve | apply: lv_putr; [fmap_solve | exact: (Htail_lv s)]]. }
    have Htail_blm : forall s : SS, bad_loc_monotone 45
      (TI ← get ideal_tbl_loc ;;
       match TI (s, info) with
       | Some k => K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
       | None => k ← sample uniform Key_N ;; #put ideal_tbl_loc := setm TI (s, info) k ;; K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
       end).
    { move=> s. apply: blm_getr => TI. case: (TI (s,info)) => [k|] /=.
      - apply: blm_getr => K. case: (K n) => [k0|] /=.
        + exact: blm_ret.
        + apply: blm_putr_other; [done | exact: blm_ret].
      - apply: blm_sampler => k. apply: blm_putr_other; [done |
          apply: blm_getr => K; case: (K n) => [k0|] /=].
        + exact: blm_ret.
        + apply: blm_putr_other; [done | exact: blm_ret]. }
    have Hm : bad_loc_monotone 45
      (D ← get kdone_loc ;;
       match D n with
       | Some _ => ret tt
       | None =>
           #put kdone_loc := setm D n tt ;;
           T ← get ss_tbl_loc ;;
           match T n with
           | Some s =>
               TI ← get ideal_tbl_loc ;;
               match TI (s, info) with
               | Some k => K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
               | None => k ← sample uniform Key_N ;; #put ideal_tbl_loc := setm TI (s, info) k ;; K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
               end
           | None =>
               s ← sample uniform SS_N ;;
               U ← get used_ss_loc ;;
               match U s with
               | Some _ =>
                   #put bad_loc := true ;;
                   #put ss_tbl_loc := setm T n s ;;
                   TI ← get ideal_tbl_loc ;;
                   match TI (s, info) with
                   | Some k => K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                   | None => k ← sample uniform Key_N ;; #put ideal_tbl_loc := setm TI (s, info) k ;; K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                   end
               | None =>
                   #put used_ss_loc := setm U s tt ;;
                   #put ss_tbl_loc := setm T n s ;;
                   TI ← get ideal_tbl_loc ;;
                   match TI (s, info) with
                   | Some k => K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                   | None => k ← sample uniform Key_N ;; #put ideal_tbl_loc := setm TI (s, info) k ;; K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                   end
               end
           end
       end).
    { apply: blm_getr => D. case: (D n) => [[]|] /=.
      - exact: blm_ret.
      - apply: blm_putr_other; [done |
          apply: blm_getr => T; case: (T n) => [s|] /=].
        + exact: (Htail_blm s).
        + apply: blm_sampler => s. apply: blm_getr => U. case: (U s) => [[]|] /=.
          * apply: blm_putr_bad. apply: blm_putr_other; [done | exact: (Htail_blm s)].
          * apply: blm_putr_other; [done | apply: blm_putr_other; [done | exact: (Htail_blm s)]]. }
    exact: (Pr_code_lossless_bad (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc)) _ Hlv Hm h Hb).
  Qed.

  Lemma GKDF_bad_false_bad_preserved :
    bad_preserved (unionm I_kdf_env KDF_out) 45 GKDF_bad_false.
  Proof.
    move=> id S T x h has Hb.
    fmap_invert has.
    all: simplify_linking.
    1: {
      have Hlv : lossless_valid (unionm KDF_loc (unionm KEYS_bad_loc KDFC_loc))
        (v ← get ss_tbl_loc ;;
         b ← match v x with
             | Some _ => ret tt
             | None =>
                 s ← sample uniform SS_N ;;
                 U ← get used_ss_loc ;;
                 match U s with
                 | Some _ => #put bad_loc := true ;; ret tt
                 | None => #put used_ss_loc := setm U s tt ;; ret tt
                 end ;;
                 #put ss_tbl_loc := setm v x s ;;
                 ret tt
             end ;;
         ret b).
      { apply: lv_getr; [fmap_solve | move=> v; case: (v x) => [ss1|] /=].
        - exact: lv_ret.
        - apply: lv_sampler => s.
          apply: lv_getr; [fmap_solve | move=> U; case: (U s) => [[]|] /=].
          + apply: lv_putr; [fmap_solve | apply: lv_putr; [fmap_solve | exact: lv_ret]].
          + apply: lv_putr; [fmap_solve | apply: lv_putr; [fmap_solve | exact: lv_ret]]. }
      have Hm : bad_loc_monotone 45
        (v ← get ss_tbl_loc ;;
         b ← match v x with
             | Some _ => ret tt
             | None =>
                 s ← sample uniform SS_N ;;
                 U ← get used_ss_loc ;;
                 match U s with
                 | Some _ => #put bad_loc := true ;; ret tt
                 | None => #put used_ss_loc := setm U s tt ;; ret tt
                 end ;;
                 #put ss_tbl_loc := setm v x s ;;
                 ret tt
             end ;;
         ret b).
      { apply: blm_getr => v. case: (v x) => [ss1|] /=.
        - exact: blm_ret.
        - apply: blm_sampler => s. apply: blm_getr => U. case: (U s) => [[]|] /=.
          + apply: blm_putr_bad. apply: blm_putr_other; [done | exact: blm_ret].
          + apply: blm_putr_other; [done | apply: blm_putr_other; [done | exact: blm_ret]]. }
      exact: (Pr_code_lossless_bad (unionm KDF_loc (unionm KEYS_bad_loc KDFC_loc)) _ Hlv Hm h Hb).
    }
    1: {
      have Hlv : lossless_valid (unionm KDF_loc (unionm KEYS_bad_loc KDFC_loc))
        (v ← get k_tbl_loc ;;
         b ← match v x with
             | Some k => ret k
             | None =>
                 k ← sample uniform Key_N ;;
                 #put k_tbl_loc := setm v x k ;;
                 ret k
             end ;;
         ret b).
      { apply: lv_getr; [fmap_solve | move=> v; case: (v x) => [k0|] /=].
        - exact: lv_ret.
        - apply: lv_sampler => k. apply: lv_putr; [fmap_solve | exact: lv_ret]. }
      have Hm : bad_loc_monotone 45
        (v ← get k_tbl_loc ;;
         b ← match v x with
             | Some k => ret k
             | None =>
                 k ← sample uniform Key_N ;;
                 #put k_tbl_loc := setm v x k ;;
                 ret k
             end ;;
         ret b).
      { apply: blm_getr => v. case: (v x) => [k0|] /=.
        - exact: blm_ret.
        - apply: blm_sampler => k. apply: blm_putr_other; [done | exact: blm_ret]. }
      exact: (Pr_code_lossless_bad (unionm KDF_loc (unionm KEYS_bad_loc KDFC_loc)) _ Hlv Hm h Hb).
    }
    case: x => n info /=.
    eapply bad_lossless_rw.
    1: solve [ssprove_match_commut_gen].
    have Htail_lv : lossless_valid (unionm KDF_loc (unionm KEYS_bad_loc KDFC_loc))
      (K ← get k_tbl_loc ;;
       match K n with
       | Some _ => ret tt
       | None => k ← sample uniform Key_N ;; #put k_tbl_loc := setm K n k ;; ret tt
       end).
    { apply: lv_getr; [fmap_solve | move=> K; case: (K n) => [k0|] /=].
      - exact: lv_ret.
      - apply: lv_sampler => k. apply: lv_putr; [fmap_solve | exact: lv_ret]. }
    have Hlv : lossless_valid (unionm KDF_loc (unionm KEYS_bad_loc KDFC_loc))
      (D ← get kdone_loc ;;
       match D n with
       | Some _ => ret tt
       | None =>
           #put kdone_loc := setm D n tt ;;
           T ← get ss_tbl_loc ;;
           match T n with
           | Some s =>
               K ← get k_tbl_loc ;;
               match K n with
               | Some _ => ret tt
               | None => k ← sample uniform Key_N ;; #put k_tbl_loc := setm K n k ;; ret tt
               end
           | None =>
               s ← sample uniform SS_N ;;
               U ← get used_ss_loc ;;
               match U s with
               | Some _ =>
                   #put bad_loc := true ;;
                   #put ss_tbl_loc := setm T n s ;;
                   K ← get k_tbl_loc ;;
                   match K n with
                   | Some _ => ret tt
                   | None => k ← sample uniform Key_N ;; #put k_tbl_loc := setm K n k ;; ret tt
                   end
               | None =>
                   #put used_ss_loc := setm U s tt ;;
                   #put ss_tbl_loc := setm T n s ;;
                   K ← get k_tbl_loc ;;
                   match K n with
                   | Some _ => ret tt
                   | None => k ← sample uniform Key_N ;; #put k_tbl_loc := setm K n k ;; ret tt
                   end
               end
           end
       end).
    { apply: lv_getr; [fmap_solve | move=> D; case: (D n) => [[]|] /=].
      - exact: lv_ret.
      - apply: lv_putr; [fmap_solve |
          apply: lv_getr; [fmap_solve | move=> T; case: (T n) => [s|] /=] ].
        + exact: Htail_lv.
        + apply: lv_sampler => s. apply: lv_getr; [fmap_solve | move=> U; case: (U s) => [[]|] /=].
          * apply: lv_putr; [fmap_solve | apply: lv_putr; [fmap_solve | exact: Htail_lv]].
          * apply: lv_putr; [fmap_solve | apply: lv_putr; [fmap_solve | exact: Htail_lv]]. }
    have Htail_blm : bad_loc_monotone 45
      (K ← get k_tbl_loc ;;
       match K n with
       | Some _ => ret tt
       | None => k ← sample uniform Key_N ;; #put k_tbl_loc := setm K n k ;; ret tt
       end).
    { apply: blm_getr => K. case: (K n) => [k0|] /=.
      - exact: blm_ret.
      - apply: blm_sampler => k. apply: blm_putr_other; [done | exact: blm_ret]. }
    have Hm : bad_loc_monotone 45
      (D ← get kdone_loc ;;
       match D n with
       | Some _ => ret tt
       | None =>
           #put kdone_loc := setm D n tt ;;
           T ← get ss_tbl_loc ;;
           match T n with
           | Some s =>
               K ← get k_tbl_loc ;;
               match K n with
               | Some _ => ret tt
               | None => k ← sample uniform Key_N ;; #put k_tbl_loc := setm K n k ;; ret tt
               end
           | None =>
               s ← sample uniform SS_N ;;
               U ← get used_ss_loc ;;
               match U s with
               | Some _ =>
                   #put bad_loc := true ;;
                   #put ss_tbl_loc := setm T n s ;;
                   K ← get k_tbl_loc ;;
                   match K n with
                   | Some _ => ret tt
                   | None => k ← sample uniform Key_N ;; #put k_tbl_loc := setm K n k ;; ret tt
                   end
               | None =>
                   #put used_ss_loc := setm U s tt ;;
                   #put ss_tbl_loc := setm T n s ;;
                   K ← get k_tbl_loc ;;
                   match K n with
                   | Some _ => ret tt
                   | None => k ← sample uniform Key_N ;; #put k_tbl_loc := setm K n k ;; ret tt
                   end
               end
           end
       end).
    { apply: blm_getr => D. case: (D n) => [[]|] /=.
      - exact: blm_ret.
      - apply: blm_putr_other; [done |
          apply: blm_getr => T; case: (T n) => [s|] /=].
        + exact: Htail_blm.
        + apply: blm_sampler => s. apply: blm_getr => U. case: (U s) => [[]|] /=.
          * apply: blm_putr_bad. apply: blm_putr_other; [done | exact: Htail_blm].
          * apply: blm_putr_other; [done | apply: blm_putr_other; [done | exact: Htail_blm]]. }
    exact: (Pr_code_lossless_bad (unionm KDF_loc (unionm KEYS_bad_loc KDFC_loc)) _ Hlv Hm h Hb).
  Qed.

  (** * Step (c), the Fundamental-Lemma application.

    [GKDF_bad_mid_ref]/[GKDF_bad_false] are both closed (no imports),
    concrete games, so [eq_upto_bad_perf_ind] needs [ValidPackage _
    Game_import _ _] for each — pure package algebra, same
    [valid_par]/[valid_link_weak] toolbox as [GKDF_bad_mid_ref_GKDF_mid_ref_equiv]
    above (the RHS additionally needs [fcompat KDF_loc KDFC_loc]/
    [fcompat KEYS_bad_loc KDFC_loc], since [KDFC_loc] is abstract —
    threaded here exactly as the task's PREMISE POLICY prescribes: both
    facts are already premises of [GKDF_mid_ref_ideal] below (as
    [hcompD]/[hcomp]), so no NEW obligation is pushed onto callers beyond
    what threading them one lemma further down requires. *)
  Lemma GKDF_bad_mid_ref_valid :
    ValidPackage (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc)) Game_import
      (unionm I_kdf_env KDF_out) GKDF_bad_mid_ref.
  Proof.
    have vID : ValidPackage emptym I_kdf_env I_kdf_env (ID I_kdf_env) by ssprove_valid.
    have vKDFt : ValidPackage KDF_loc KDF_in KDF_out (KDF true) by ssprove_valid.
    have vKEYSbad : ValidPackage KEYS_bad_loc [interface] KEYS_out KEYS_bad by ssprove_valid.
    have vKDFCI : ValidPackage KDFC_IDEAL_loc [interface] KDFC_out KDFC_IDEAL by ssprove_valid.
    have vP1 : ValidPackage (unionm emptym KDF_loc) (unionm I_kdf_env KDF_in)
      (unionm I_kdf_env KDF_out) (par (ID I_kdf_env) (KDF true)).
    { eapply valid_par. 1: exact vID. 1: exact vKDFt. all: fmap_solve. }
    have vP2 : ValidPackage (unionm KEYS_bad_loc KDFC_IDEAL_loc) (unionm [interface] [interface])
      (unionm KEYS_out KDFC_out) (par KEYS_bad KDFC_IDEAL).
    { eapply valid_par. 1: exact vKEYSbad. 1: exact vKDFCI. all: fmap_solve. }
    eapply valid_package_inject_locations.
    1: instantiate (1 := unionm (unionm emptym KDF_loc) (unionm KEYS_bad_loc KDFC_IDEAL_loc)).
    1: fmap_solve.
    eapply valid_link_weak.
    1: exact vP1.
    1: exact vP2.
    all: fmap_solve.
  Qed.

  Lemma GKDF_bad_false_valid (hcompD : fcompat KDF_loc KDFC_loc) (hcomp : fcompat KEYS_bad_loc KDFC_loc) :
    ValidPackage (unionm KDF_loc (unionm KEYS_bad_loc KDFC_loc)) Game_import
      (unionm I_kdf_env KDF_out) GKDF_bad_false.
  Proof.
    have vID : ValidPackage emptym I_kdf_env I_kdf_env (ID I_kdf_env) by ssprove_valid.
    have vGlue : ValidPackage KDF_loc KDF_in KDF_out KDF_bad_false_glue by ssprove_valid.
    have vKEYSbad : ValidPackage KEYS_bad_loc [interface] KEYS_out KEYS_bad by ssprove_valid.
    have vKDFCt : ValidPackage KDFC_loc [interface] KDFC_out (KDFC true) := KDFC_valid true.
    have vP1 : ValidPackage (unionm emptym KDF_loc) (unionm I_kdf_env KDF_in)
      (unionm I_kdf_env KDF_out) (par (ID I_kdf_env) KDF_bad_false_glue).
    { eapply valid_par. 1: exact vID. 1: exact vGlue. all: fmap_solve. }
    have vP2 : ValidPackage (unionm KEYS_bad_loc KDFC_loc) (unionm [interface] [interface])
      (unionm KEYS_out KDFC_out) (par KEYS_bad (KDFC true)).
    { eapply valid_par. 1: exact vKEYSbad. 1: exact vKDFCt. all: try fmap_solve. }
    eapply valid_package_inject_locations.
    1: instantiate (1 := unionm (unionm emptym KDF_loc) (unionm KEYS_bad_loc KDFC_loc)).
    1: fmap_solve.
    eapply valid_link_weak.
    1: exact vP1.
    1: exact vP2.
    2: fmap_solve.
    fmap_solve.
  Qed.

  (** General "already bad" independence step, reused at every op-case
    (and at the DERIVE_K collision sub-branch) of
    [GKDF_bad_mid_ref_GKDF_bad_false_eq_up_to_bad] below: once [bad_loc]
    is true entering an op call, the two sides no longer need to match
    at all -- each just needs to keep running independently while
    [bad_loc] stays true, which is exactly what [independent_rule]
    packages up given [lossless_valid]/[bad_loc_monotone] facts for each
    side's own code (the same facts [GKDF_bad_mid_ref_bad_preserved]/
    [GKDF_bad_false_bad_preserved] establish per op-case, above --
    [bad_preserved]'s own conclusion is Pr_code-level only and doesn't
    carry the location-set framing fact [theta_frame] needs to reprove
    the [heap_ignore] part of the postcondition, hence this takes
    [lossless_valid]/[bad_loc_monotone] directly rather than reusing
    those two lemmas). *)
  Lemma GKDF_bad_already_bad_indep {AT : choiceType} (LL LR : Locations)
    (cL cR : raw_code AT)
    (HnotinL : ∀ l : Location, l.1 \notin domm GKDF_bad_bad_locs → l.1 \notin domm LL)
    (HnotinR : ∀ l : Location, l.1 \notin domm GKDF_bad_bad_locs → l.1 \notin domm LR)
    (Hlv0 : lossless_valid LL cL) (Hm0 : bad_loc_monotone 45 cL)
    (Hlv1 : lossless_valid LR cR) (Hm1 : bad_loc_monotone 45 cR)
    (s0 s1 : heap)
    (Hbad0 : get_heap s0 bad_loc = true) (Hbad1 : get_heap s1 bad_loc = true)
    (Hig : heap_ignore GKDF_bad_bad_locs (s0, s1)) :
    ⊢ ⦃ fun '(t0,t1) => t0 = s0 /\ t1 = s1 ⦄
      cL ≈ cR
    ⦃ fun '(b0,t0) '(b1,t1) => GKDF_bad_bad_inv (t0,t1) /\ (get_heap t0 bad_loc = false -> b0 = b1) ⦄.
  Proof.
    apply: from_sem_jdg.
    apply: independent_rule.
    { move=> t0 t1 [/= -> _]. rewrite -Pr_code_theta_bridge. exact: (Pr_code_lossless LL cL Hlv0 s0). }
    { move=> t0 t1 [/= _ ->]. rewrite -Pr_code_theta_bridge. exact: (Pr_code_lossless LR cR Hlv1 s1). }
    move=> t0 t1 [/= -> ->] a1 h1' a2 h2' Hgt1 Hgt2.
    have Hgt1' : (0 < Pr_code cL s0 (a1,h1'))%R.
    { rewrite Pr_code_theta_bridge. exact: Hgt1. }
    have Hgt2' : (0 < Pr_code cR s1 (a2,h2'))%R.
    { rewrite Pr_code_theta_bridge. exact: Hgt2. }
    have Hbad1' : get_heap h1' bad_loc = true.
    { exact: (Pr_code_bad_monotone cL Hm0 s0 Hbad0 a1 h1' Hgt1'). }
    have Hbad2' : get_heap h2' bad_loc = true.
    { exact: (Pr_code_bad_monotone cR Hm1 s1 Hbad1 a2 h2' Hgt2'). }
    split.
    { split.
      { split.
        { move=> l Hnotin.
          rewrite (theta_frame LL cL Hlv0 s0 l (HnotinL l Hnotin) a1 h1' Hgt1).
          rewrite (theta_frame LR cR Hlv1 s1 l (HnotinR l Hnotin) a2 h2' Hgt2).
          exact: (Hig l Hnotin). }
        rewrite /rel_app /get_side /=. by rewrite Hbad1' Hbad2'. }
      rewrite /rel_app /get_side /=. move=> Hf. rewrite Hbad1' in Hf. discriminate. }
    move=> Hf. rewrite Hbad1' in Hf. discriminate.
  Qed.

  (** The two concrete [Locations] arguments [GKDF_bad_already_bad_indep]
    is always instantiated at below (the LHS/RHS packages' own location
    sets are each one half of [GKDF_bad_bad_locs]'s outer [unionm]) are
    trivially inside [GKDF_bad_bad_locs] -- factored out once here to
    keep each call site to a one-liner. *)
  Lemma GKDF_bad_bad_locs_notinL :
    ∀ l : Location, l.1 \notin domm GKDF_bad_bad_locs →
      l.1 \notin domm (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc)).
  Proof.
    move=> l. rewrite /GKDF_bad_bad_locs domm_union in_fsetU negb_or => /andP[] //.
  Qed.

  Lemma GKDF_bad_bad_locs_notinR :
    ∀ l : Location, l.1 \notin domm GKDF_bad_bad_locs →
      l.1 \notin domm (unionm KDF_loc (unionm KEYS_bad_loc KDFC_loc)).
  Proof.
    move=> l. rewrite /GKDF_bad_bad_locs domm_union in_fsetU negb_or => /andP[] //.
  Qed.

  (** Generic constructor for [GKDF_bad_bad_inv], factoring the
    [(heap_ignore ⋊ syncs bad_loc) ⋊ rel_app [...]] nesting into a single
    application everywhere the "not yet bad" real-coupling branches
    (below) need to re-establish the invariant after a [r_put_vs_put]. *)
  Lemma GKDF_bad_bad_inv_intro (h0 h1 : heap)
    (Hig : heap_ignore GKDF_bad_bad_locs (h0, h1))
    (Hsync : get_heap h0 bad_loc = get_heap h1 bad_loc)
    (Hgated : get_heap h0 bad_loc = false →
       get_heap h0 kdone_loc = get_heap h1 kdone_loc ∧
       get_heap h0 ss_tbl_loc = get_heap h1 ss_tbl_loc ∧
       get_heap h0 used_ss_loc = get_heap h1 used_ss_loc ∧
       get_heap h0 k_tbl_loc = get_heap h1 k_tbl_loc ∧
       ss_used_correspondence (get_heap h0 ss_tbl_loc) (get_heap h0 used_ss_loc) ∧
       ss_tbl_injective (get_heap h0 ss_tbl_loc) ∧
       derive_fresh (get_heap h0 kdone_loc) (get_heap h0 ss_tbl_loc) (get_heap h0 ideal_tbl_loc)) :
    GKDF_bad_bad_inv (h0, h1).
  Proof.
    split.
    { split; [exact: Hig | rewrite /rel_app /get_side /=; exact: Hsync]. }
    rewrite /rel_app /get_side /=. exact: Hgated.
  Qed.

  (** Generic "just transitioned to bad" constructor: once both sides'
    [bad_loc] is [true] and the states agree with some [heap_ignore]d
    pair (h0,h1) outside [GKDF_bad_bad_locs] (the usual shape after a
    [r_put_vs_put] sequence that only touches locations inside
    [GKDF_bad_bad_locs]), [GKDF_bad_bad_inv] holds -- [syncs]
    (true = true) and the [rel_app] gate (vacuous, since its antecedent
    is now false) need no further information. *)
  Lemma GKDF_bad_now_bad (h0 h1 h0' h1' : heap)
    (Hig : heap_ignore GKDF_bad_bad_locs (h0, h1))
    (Hframe0 : ∀ l : Location, l.1 \notin domm GKDF_bad_bad_locs → get_heap h0' l = get_heap h0 l)
    (Hframe1 : ∀ l : Location, l.1 \notin domm GKDF_bad_bad_locs → get_heap h1' l = get_heap h1 l)
    (Hbad0' : get_heap h0' bad_loc = true) (Hbad1' : get_heap h1' bad_loc = true) :
    GKDF_bad_bad_inv (h0', h1').
  Proof.
    apply: GKDF_bad_bad_inv_intro.
    - move=> l Hnotin. rewrite (Hframe0 l Hnotin) (Hframe1 l Hnotin). exact: (Hig l Hnotin).
    - by rewrite Hbad0' Hbad1'.
    - move=> Hf. rewrite Hbad0' in Hf. discriminate.
  Qed.

  (** [ss_used_correspondence] survives extending [T]/[U] with a
    matching FRESH pair -- the session-side analogue of HKDF's own
    by-hand [used_prk_correspondence] extension (inlined there; named
    here since it recurs at both [GEN_SS]/[GET_SS]'s fresh branch and
    [DERIVE_K]'s own inlined copy of it). *)
  Lemma ss_used_correspondence_extend (T : chMap SESS SS) (U : chMap SS 'unit)
    (n : SESS) (s : SS) :
    ss_used_correspondence T U → getm T n = None → getm U s = None →
    ss_used_correspondence (setm T n s) (setm U s tt).
  Proof.
    move=> Hcorr HTn HUs s0. rewrite setmE.
    case: (eqVneq s0 s) => [-> | Hne].
    1:{
      split.
      - move=> _. exists n. by rewrite setmE eqxx.
      - move=> _. done.
    }
    split.
    - move=> HU0. have [n0 Hn0] := (proj1 (Hcorr s0) HU0). exists n0.
      rewrite setmE. case: (eqVneq n0 n) => [Heq | Hneq].
      * subst n0. rewrite HTn in Hn0. discriminate.
      * exact: Hn0.
    - move=> [n0 Hn0]. move: Hn0. rewrite setmE.
      case Heq: (n0 == n).
      { move/eqP: Heq => Heq. subst n0. move=> [Heq2]. subst s0. move: Hne => /eqP; done. }
      { move=> HTn0. apply: (proj2 (Hcorr s0)). exists n0. exact: HTn0. }
  Qed.

  (** [ss_tbl_injective] survives extending [T] at a FRESH key with a
    value outside [T]'s existing range. *)
  Lemma ss_tbl_injective_extend (T : chMap SESS SS) (n : SESS) (s : SS) :
    ss_tbl_injective T → getm T n = None → (∀ n', getm T n' <> Some s) →
    ss_tbl_injective (setm T n s).
  Proof.
    move=> Hinj HTn Hnotrange n1 n2 s'. rewrite !setmE.
    case Heq1: (n1 == n).
    { move/eqP: Heq1 => Heq1. subst n1.
      move=> [Heq]. subst s'.
      case Heq2: (n2 == n).
      { move/eqP: Heq2 => Heq2. subst n2. done. }
      { move=> H2. exfalso. exact: (Hnotrange n2 H2). }
    }
    { move=> H1.
      case Heq2: (n2 == n).
      { move/eqP: Heq2 => Heq2. subst n2. move=> [Heq]. subst s'. exfalso. exact: (Hnotrange n1 H1). }
      { move=> H2. exact: (Hinj n1 n2 s' H1 H2). }
    }
  Qed.

  (** [derive_fresh] is monotone in [T]: extending it at a FRESH key
    (one [T] didn't already map) preserves every existing witness. *)
  Lemma derive_fresh_extend_T (D : chMap SESS 'unit) (T : chMap SESS SS)
    (TI : chMap ('ss × 'info) 'key) (n : SESS) (s : SS) :
    derive_fresh D T TI → getm T n = None → derive_fresh D (setm T n s) TI.
  Proof.
    move=> Hfresh HTn s0 info0 Hne.
    have [n0 [HDn0 HTn0]] := Hfresh s0 info0 Hne.
    exists n0. split; [exact: HDn0 |].
    rewrite setmE. case Heq: (n0 == n) => //.
    move/eqP: Heq => Heq. subst n0. rewrite HTn0 in HTn. discriminate.
  Qed.

  (** [derive_fresh] is also monotone in [D]: extending it at a
    (possibly new) key never invalidates an existing witness, since the
    witness's own [D]-entry is untouched unless the witness's session is
    literally the one being marked done, which only ADDS information. *)
  Lemma derive_fresh_extend_D (D : chMap SESS 'unit) (T : chMap SESS SS)
    (TI : chMap ('ss × 'info) 'key) (n : SESS) :
    derive_fresh D T TI → derive_fresh (setm D n tt) T TI.
  Proof.
    move=> Hfresh s0 info0 Hne.
    have [n0 [HDn0 HTn0]] := Hfresh s0 info0 Hne.
    exists n0. split; [| exact: HTn0].
    rewrite setmE. case Heq: (n0 == n) => //.
  Qed.

  (** [get_set_heap_neq]'s side condition, packaged for the common shape
    "[l] isn't in [GKDF_bad_bad_locs], [loc] is" (the by-hand
    [heap_ignore]/table-reconstruction steps below need this at every
    [#put], for every location the [#put] didn't touch). *)
  Lemma GKDF_bad_bad_locs_neq (l loc : Location) :
    l.1 \notin domm GKDF_bad_bad_locs -> fhas GKDF_bad_bad_locs loc -> l.1 != loc.1.
  Proof.
    move=> Hnotin Hin. apply/eqP => Heq. move: Hnotin => /negP; apply.
    rewrite Heq. apply: fhas_in. exact: Hin.
  Qed.

  (** The one genuinely open piece of the up-to-bad argument: the
    relational, oracle-by-oracle "match until [bad_loc] fires" fact
    [eq_upto_bad_perf_ind] needs, mirroring HKDF.v's
    [KDF_mid'_KDF_bad_eq_up_to_bad] (~L787-1521, itself the single
    hardest lemma in that file per [ROCQ_MCP_SESSION_NOTES.md]).
    [GEN_SS]/[GET_K] are IDENTICAL code on both sides (both route through
    [KEYS_bad]), so their cases are a direct coupled derivation once
    [GKDF_bad_bad_inv]'s "[b = false] -> ..." equalities are unpacked
    (confirmed tractable interactively: the get/put coupling needs the
    [rpre_hypothesis_rule]-then-[rpre_weaken_rule]-with-an-explicit-[pre]
    idiom from HKDF's own template, since [r_get_vs_get_remember]'s
    automatic [ProvenBy (syncs ℓ) pre] search does not fire on a
    [b = false]-GATED equality — and each of [r_put_lhs]/[r_put_vs_put]
    needs its [pre] argument supplied EXPLICITLY, matching the
    session notes' "always pass pre explicitly" lesson, since a
    projection-form precondition from [rpre_hypothesis_rule] does not
    unify against a pair-pattern-form one without a
    [functional_extensionality] bridge). [DERIVE_K] is the substantive
    content: after [GET_SS]'s shared bad-tracking code determines the
    session's [s] identically on both sides, [derive_fresh]/
    [ss_tbl_injective] show [KDFC_IDEAL]'s lookup at [(s, info)] is
    GUARANTEED fresh whenever [bad_loc] is still false (this session's
    [s] cannot have been used by any COMPLETED session's own
    [DERIVE_K]), so the derived key and [GEN_K]'s independent draw
    couple as the literal same uniform sample via [r_uniform_bij id].
    What remains, concretely: transcribing that argument (case-split on
    [GEN_SS]'s two branches x2 for the "already extracted"/"fresh"
    session-secret split, x2 again for "collision"/"no collision" within
    the fresh branch, each ending in an explicit, by-hand invariant
    reconstruction in the style of HKDF.v's own PUT branches ~L1049-1126,
    NOT via [ssprove_restore_mem]/[ssprove_invariant] automation, which
    does not fire on this file's gated invariant shape).

    The three op-cases are split into standalone lemmas below
    ([GKDF_bad_GEN_SS_case]/[GKDF_bad_GET_K_case]/[GKDF_bad_DERIVE_K_case])
    so each can be checked (and, per the session notes, transcribed)
    independently; the main lemma is then pure assembly. *)
  Lemma GKDF_bad_GEN_SS_case (x : SESS) :
    ⊢ ⦃ fun '(s0,s1) => GKDF_bad_bad_inv (s0,s1) ⦄
      (v ← get ss_tbl_loc ;;
       b ← match v x with
           | Some _ => ret tt
           | None =>
               s ← sample uniform SS_N ;;
               U ← get used_ss_loc ;;
               match U s with
               | Some _ => #put bad_loc := true ;; ret tt
               | None => #put used_ss_loc := setm U s tt ;; ret tt
               end ;;
               #put ss_tbl_loc := setm v x s ;;
               ret tt
           end ;;
       ret b)
      ≈
      (v ← get ss_tbl_loc ;;
       b ← match v x with
           | Some _ => ret tt
           | None =>
               s ← sample uniform SS_N ;;
               U ← get used_ss_loc ;;
               match U s with
               | Some _ => #put bad_loc := true ;; ret tt
               | None => #put used_ss_loc := setm U s tt ;; ret tt
               end ;;
               #put ss_tbl_loc := setm v x s ;;
               ret tt
           end ;;
       ret b)
    ⦃ fun '(b0,s0) '(b1,s1) => GKDF_bad_bad_inv (s0,s1) /\ (get_heap s0 bad_loc = false -> b0 = b1) ⦄.
  Proof.
    apply: rpre_hypothesis_rule => s0 s1 Hpre.
    have Hsync : get_heap s0 bad_loc = get_heap s1 bad_loc.
    { move: (proj2 (proj1 Hpre)). rewrite /rel_app /get_side /=. done. }
    case: (boolP (get_heap s0 bad_loc)) => Hbad.
    1:{
      eapply rpre_weaken_rule.
      1: instantiate (1 := fun '(t0,t1) => t0 = s0 /\ t1 = s1).
      2: { move=> t0 t1 [/= -> ->]. done. }
      have Hbad1 : get_heap s1 bad_loc = true. { by rewrite -Hsync. }
      have Hlv0 : lossless_valid (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc))
        (v ← get ss_tbl_loc ;;
         b ← match v x with
             | Some _ => ret tt
             | None =>
                 s ← sample uniform SS_N ;;
                 U ← get used_ss_loc ;;
                 match U s with
                 | Some _ => #put bad_loc := true ;; ret tt
                 | None => #put used_ss_loc := setm U s tt ;; ret tt
                 end ;;
                 #put ss_tbl_loc := setm v x s ;;
                 ret tt
             end ;;
         ret b).
      { apply: lv_getr; [fmap_solve | move=> v; case: (v x) => [ss1|] /=].
        - exact: lv_ret.
        - apply: lv_sampler => s.
          apply: lv_getr; [fmap_solve | move=> U; case: (U s) => [[]|] /=].
          + apply: lv_putr; [fmap_solve | apply: lv_putr; [fmap_solve | exact: lv_ret]].
          + apply: lv_putr; [fmap_solve | apply: lv_putr; [fmap_solve | exact: lv_ret]]. }
      have Hm0 : bad_loc_monotone 45
        (v ← get ss_tbl_loc ;;
         b ← match v x with
             | Some _ => ret tt
             | None =>
                 s ← sample uniform SS_N ;;
                 U ← get used_ss_loc ;;
                 match U s with
                 | Some _ => #put bad_loc := true ;; ret tt
                 | None => #put used_ss_loc := setm U s tt ;; ret tt
                 end ;;
                 #put ss_tbl_loc := setm v x s ;;
                 ret tt
             end ;;
         ret b).
      { apply: blm_getr => v. case: (v x) => [ss1|] /=.
        - exact: blm_ret.
        - apply: blm_sampler => s. apply: blm_getr => U. case: (U s) => [[]|] /=.
          + apply: blm_putr_bad. apply: blm_putr_other; [done | exact: blm_ret].
          + apply: blm_putr_other; [done | apply: blm_putr_other; [done | exact: blm_ret]]. }
      have Hlv1 : lossless_valid (unionm KDF_loc (unionm KEYS_bad_loc KDFC_loc))
        (v ← get ss_tbl_loc ;;
         b ← match v x with
             | Some _ => ret tt
             | None =>
                 s ← sample uniform SS_N ;;
                 U ← get used_ss_loc ;;
                 match U s with
                 | Some _ => #put bad_loc := true ;; ret tt
                 | None => #put used_ss_loc := setm U s tt ;; ret tt
                 end ;;
                 #put ss_tbl_loc := setm v x s ;;
                 ret tt
             end ;;
         ret b).
      { apply: lv_getr; [fmap_solve | move=> v; case: (v x) => [ss1|] /=].
        - exact: lv_ret.
        - apply: lv_sampler => s.
          apply: lv_getr; [fmap_solve | move=> U; case: (U s) => [[]|] /=].
          + apply: lv_putr; [fmap_solve | apply: lv_putr; [fmap_solve | exact: lv_ret]].
          + apply: lv_putr; [fmap_solve | apply: lv_putr; [fmap_solve | exact: lv_ret]]. }
      have Hm1 : bad_loc_monotone 45
        (v ← get ss_tbl_loc ;;
         b ← match v x with
             | Some _ => ret tt
             | None =>
                 s ← sample uniform SS_N ;;
                 U ← get used_ss_loc ;;
                 match U s with
                 | Some _ => #put bad_loc := true ;; ret tt
                 | None => #put used_ss_loc := setm U s tt ;; ret tt
                 end ;;
                 #put ss_tbl_loc := setm v x s ;;
                 ret tt
             end ;;
         ret b).
      { apply: blm_getr => v. case: (v x) => [ss1|] /=.
        - exact: blm_ret.
        - apply: blm_sampler => s. apply: blm_getr => U. case: (U s) => [[]|] /=.
          + apply: blm_putr_bad. apply: blm_putr_other; [done | exact: blm_ret].
          + apply: blm_putr_other; [done | apply: blm_putr_other; [done | exact: blm_ret]]. }
      exact: (GKDF_bad_already_bad_indep _ _ _ _ GKDF_bad_bad_locs_notinL GKDF_bad_bad_locs_notinR
        Hlv0 Hm0 Hlv1 Hm1 s0 s1 Hbad Hbad1 (proj1 (proj1 Hpre))).
    }
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(t0,t1) => t0 = s0 /\ t1 = s1).
    2: { move=> t0 t1 [/= -> ->]. done. }
    move: Hbad => /negbTE Hbad'.
    have Hg := (proj2 Hpre) Hbad'.
    move: Hg. rewrite /rel_app /get_side /=.
    move=> [HD [HT [HU [HK [Hcorr [Hinj Hfresh]]]]]].
    eapply (r_get_remember_lhs ss_tbl_loc _ _ (fun '(t0,t1) => t0 = s0 /\ t1 = s1)).
    move=> v.
    eapply (r_get_remember_rhs ss_tbl_loc _ _ ((fun '(t0,t1) => t0 = s0 /\ t1 = s1) ⋊ rem_lhs ss_tbl_loc v)).
    move=> v'.
    apply: rpre_hypothesis_rule => t0 t1 Hp.
    case: Hp => [[[Heq0 Heq1] Heqv] Heqv'].
    subst t0 t1.
    move: Heqv Heqv'. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=. move=> Heqv Heqv'.
    have Hvv' : v = v'.
    { rewrite -Heqv -Heqv'. exact: HT. }
    subst v'.
    case Hv: (v x) => [ssv|].
    1:{
      rewrite -Hvv' Hv /=.
      apply: r_ret => t0 t1 h.
      split; [ | done].
      move: h => [/= -> ->]. exact: Hpre.
    }
    rewrite -Hvv' Hv /=.
    apply: r_uniform_bij => [|s].
    1: exists id; done.
    simpl.
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(t0,t1) => t0 = s0 /\ t1 = s1).
    2: { move=> t0 t1 [/= -> ->]. done. }
    eapply (r_get_remember_lhs used_ss_loc _ _ (fun '(t0,t1) => t0 = s0 /\ t1 = s1)).
    move=> u.
    eapply (r_get_remember_rhs used_ss_loc _ _ ((fun '(t0,t1) => t0 = s0 /\ t1 = s1) ⋊ rem_lhs used_ss_loc u)).
    move=> u'.
    apply: rpre_hypothesis_rule => t2 t3 Hp2.
    case: Hp2 => [[[Heq2 Heq3] Hequ] Hequ'].
    subst t2 t3.
    move: Hequ Hequ'. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=. move=> Hequ Hequ'.
    have Huu' : u = u'.
    { rewrite -Hequ -Hequ'. exact: HU. }
    subst u'.
    case Hus: (u s) => [[]|].
    1:{
      rewrite -Huu' Hus /=.
      eapply rpre_weaken_rule.
      1: instantiate (1 := fun '(t0,t1) => t0 = s0 /\ t1 = s1).
      2: { move=> t0 t1 [/= -> ->]. done. }
      eapply (r_put_vs_put bad_loc true bad_loc true _ _
        (fun '(t0,t1) => t0 = s0 /\ t1 = s1)).
      apply: rpre_hypothesis_rule => t4 t5 Hp3.
      case: Hp3 => [t5'' [[t4'' [[Heq4 Heq5] ->]] ->]].
      subst t4'' t5''.
      eapply rpre_weaken_rule.
      1: instantiate (1 := fun '(t0,t1) => t0 = set_heap s0 bad_loc true /\ t1 = set_heap s1 bad_loc true).
      2: { move=> t0 t1 [/= -> ->]. done. }
      eapply (r_put_vs_put ss_tbl_loc (setm v x s) ss_tbl_loc (setm v x s) _ _
        (fun '(t0,t1) => t0 = set_heap s0 bad_loc true /\ t1 = set_heap s1 bad_loc true)).
      apply: r_ret => t6 t7 h.
      move: h => [t7'' [[t6'' [[Heq6 Heq7] ->]] ->]].
      subst t6'' t7''.
      split; [ | done].
      apply: (GKDF_bad_now_bad s0 s1 _ _ (proj1 (proj1 Hpre))).
      - move=> l Hnotin.
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l ss_tbl_loc Hnotin (ltac:(fmap_solve)))).
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l bad_loc Hnotin (ltac:(fmap_solve)))).
        reflexivity.
      - move=> l Hnotin.
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l ss_tbl_loc Hnotin (ltac:(fmap_solve)))).
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l bad_loc Hnotin (ltac:(fmap_solve)))).
        reflexivity.
      - rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != ss_tbl_loc.1)) get_set_heap_eq. reflexivity.
      - rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != ss_tbl_loc.1)) get_set_heap_eq. reflexivity.
    }
    rewrite -Huu' Hus /=.
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(t0,t1) => t0 = s0 /\ t1 = s1).
    2: { move=> t0 t1 [/= -> ->]. done. }
    eapply (r_put_vs_put used_ss_loc (setm u s tt) used_ss_loc (setm u s tt) _ _
      (fun '(t0,t1) => t0 = s0 /\ t1 = s1)).
    apply: rpre_hypothesis_rule => t4 t5 Hp3.
    case: Hp3 => [t5'' [[t4'' [[Heq4 Heq5] ->]] ->]].
    subst t4'' t5''.
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(t0,t1) => t0 = set_heap s0 used_ss_loc (setm u s tt) /\ t1 = set_heap s1 used_ss_loc (setm u s tt)).
    2: { move=> t0 t1 [/= -> ->]. done. }
    eapply (r_put_vs_put ss_tbl_loc (setm v x s) ss_tbl_loc (setm v x s) _ _
      (fun '(t0,t1) => t0 = set_heap s0 used_ss_loc (setm u s tt) /\ t1 = set_heap s1 used_ss_loc (setm u s tt))).
    apply: r_ret => t6 t7 h.
    move: h => [t7'' [[t6'' [[Heq6 Heq7] ->]] ->]].
    subst t6'' t7''.
    split; [ | done].
    apply: GKDF_bad_bad_inv_intro.
    - move=> l Hnotin.
      rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l ss_tbl_loc Hnotin (ltac:(fmap_solve)))).
      rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l used_ss_loc Hnotin (ltac:(fmap_solve)))).
      rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l ss_tbl_loc Hnotin (ltac:(fmap_solve)))).
      rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l used_ss_loc Hnotin (ltac:(fmap_solve)))).
      exact: (proj1 (proj1 Hpre) l Hnotin).
    - rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != ss_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != used_ss_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != ss_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != used_ss_loc.1)).
      exact: Hsync.
    - move=> _.
      rewrite !get_set_heap_eq.
      rewrite (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != ss_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != ss_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != used_ss_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != used_ss_loc.1)).
      split; [exact: HD | ].
      rewrite (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != ss_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != ss_tbl_loc.1)).
      rewrite !get_set_heap_eq.
      split; [reflexivity | ].
      split; [reflexivity | ].
      rewrite (get_set_heap_neq _ _ _ _ (isT : k_tbl_loc.1 != ss_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : k_tbl_loc.1 != used_ss_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : k_tbl_loc.1 != ss_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : k_tbl_loc.1 != used_ss_loc.1)).
      split; [exact: HK | ].
      rewrite (get_set_heap_neq _ _ _ _ (isT : ideal_tbl_loc.1 != ss_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : ideal_tbl_loc.1 != used_ss_loc.1)).
      split; [ | split].
      1:{
        have HTfresh : v x = None. { exact: Hv. }
        have HUfresh : u s = None. { exact: Hus. }
        apply: (ss_used_correspondence_extend v u x s).
        { rewrite -Heqv -Hequ. exact: Hcorr. }
        { exact: HTfresh. }
        { exact: HUfresh. }
      }
      1:{
        apply: (ss_tbl_injective_extend v x s).
        { rewrite -Heqv. exact: Hinj. }
        { exact: Hv. }
        { move=> n' Hcontra.
          have HUsome : u s = Some tt.
          { rewrite -Hequ. apply: (proj2 (Hcorr s)). exists n'. rewrite Heqv. exact: Hcontra. }
          rewrite HUsome in Hus. discriminate.
        }
      }
      apply: (derive_fresh_extend_T (get_heap s0 kdone_loc) v (get_heap s0 ideal_tbl_loc) x s).
      { rewrite -Heqv. exact: Hfresh. }
      { exact: Hv. }
  Qed.

  Lemma GKDF_bad_GET_K_case (x : SESS) :
    ⊢ ⦃ fun '(s0,s1) => GKDF_bad_bad_inv (s0,s1) ⦄
      (v ← get k_tbl_loc ;;
       b ← match v x with
           | Some k => ret k
           | None =>
               k ← sample uniform Key_N ;;
               #put k_tbl_loc := setm v x k ;;
               ret k
           end ;;
       ret b)
      ≈
      (v ← get k_tbl_loc ;;
       b ← match v x with
           | Some k => ret k
           | None =>
               k ← sample uniform Key_N ;;
               #put k_tbl_loc := setm v x k ;;
               ret k
           end ;;
       ret b)
    ⦃ fun '(b0,s0) '(b1,s1) => GKDF_bad_bad_inv (s0,s1) /\ (get_heap s0 bad_loc = false -> b0 = b1) ⦄.
  Proof.
    apply: rpre_hypothesis_rule => s0 s1 Hpre.
    have Hsync : get_heap s0 bad_loc = get_heap s1 bad_loc.
    { move: (proj2 (proj1 Hpre)). rewrite /rel_app /get_side /=. done. }
    case: (boolP (get_heap s0 bad_loc)) => Hbad.
    2:{
      eapply rpre_weaken_rule.
      1: instantiate (1 := fun '(t0,t1) => t0 = s0 /\ t1 = s1).
      2: { move=> t0 t1 [/= -> ->]. done. }
      move: Hbad => /negbTE Hbad'.
      have Hg := (proj2 Hpre) Hbad'.
      move: Hg. rewrite /rel_app /get_side /=.
      move=> [HD [HT [HU [HK [Hcorr [Hinj Hfresh]]]]]].
      eapply (r_get_remember_lhs k_tbl_loc _ _ (fun '(t0,t1) => t0 = s0 /\ t1 = s1)).
      move=> v.
      eapply (r_get_remember_rhs k_tbl_loc _ _ ((fun '(t0,t1) => t0 = s0 /\ t1 = s1) ⋊ rem_lhs k_tbl_loc v)).
      move=> v'.
      apply: rpre_hypothesis_rule => t0 t1 Hp.
      case: Hp => [[[Heq0 Heq1] Heqv] Heqv'].
      subst t0 t1.
      move: Heqv Heqv'. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=. move=> Heqv Heqv'.
      have Hvv' : v = v'.
      { rewrite -Heqv -Heqv'. exact: HK. }
      subst v'.
      case Hv: (v x) => [k0|].
      1:{
        rewrite -Hvv' Hv /=.
        apply: r_ret => t0 t1 h.
        split; [ | done].
        move: h => [/= -> ->]. exact: Hpre.
      }
      rewrite -Hvv' Hv /=.
      apply: r_uniform_bij => [|k].
      1: exists id; done.
      simpl.
      eapply rpre_weaken_rule.
      1: instantiate (1 := fun '(t0,t1) => t0 = s0 /\ t1 = s1).
      2: { move=> t0 t1 [/= -> ->]. done. }
      eapply (r_put_vs_put k_tbl_loc (setm v x k) k_tbl_loc (setm v x k) _ _
        (fun '(t0,t1) => t0 = s0 /\ t1 = s1)).
      apply: r_ret => t2 t3 h.
      move: h => [t3'' [[t2'' [[Heq2 Heq3] ->]] ->]].
      subst t2'' t3''.
      split; [ | done].
      apply: GKDF_bad_bad_inv_intro.
      - move=> l Hnotin.
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l k_tbl_loc Hnotin (ltac:(fmap_solve)))).
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l k_tbl_loc Hnotin (ltac:(fmap_solve)))).
        exact: (proj1 (proj1 Hpre) l Hnotin).
      - rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != k_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != k_tbl_loc.1)).
        exact: Hsync.
      - move=> _.
        rewrite !get_set_heap_eq.
        rewrite (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != k_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != k_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : ss_tbl_loc.1 != k_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : ss_tbl_loc.1 != k_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != k_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != k_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : ideal_tbl_loc.1 != k_tbl_loc.1)).
        split; [exact: HD | ].
        split; [exact: HT | ].
        split; [exact: HU | ].
        split; [reflexivity | ].
        split; [exact: Hcorr | ].
        split; [exact: Hinj | ].
        exact: Hfresh.
    }
    have Hbad1 : get_heap s1 bad_loc = true. { by rewrite -Hsync. }
    have Hlv0 : lossless_valid (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc))
      (v ← get k_tbl_loc ;;
       b ← match v x with
           | Some k => ret k
           | None =>
               k ← sample uniform Key_N ;;
               #put k_tbl_loc := setm v x k ;;
               ret k
           end ;;
       ret b).
    { apply: lv_getr; [fmap_solve | move=> v; case: (v x) => [k0|] /=].
      - exact: lv_ret.
      - apply: lv_sampler => k. apply: lv_putr; [fmap_solve | exact: lv_ret]. }
    have Hm0 : bad_loc_monotone 45
      (v ← get k_tbl_loc ;;
       b ← match v x with
           | Some k => ret k
           | None =>
               k ← sample uniform Key_N ;;
               #put k_tbl_loc := setm v x k ;;
               ret k
           end ;;
       ret b).
    { apply: blm_getr => v. case: (v x) => [k0|] /=.
      - exact: blm_ret.
      - apply: blm_sampler => k. apply: blm_putr_other; [done | exact: blm_ret]. }
    have Hlv1 : lossless_valid (unionm KDF_loc (unionm KEYS_bad_loc KDFC_loc))
      (v ← get k_tbl_loc ;;
       b ← match v x with
           | Some k => ret k
           | None =>
               k ← sample uniform Key_N ;;
               #put k_tbl_loc := setm v x k ;;
               ret k
           end ;;
       ret b).
    { apply: lv_getr; [fmap_solve | move=> v; case: (v x) => [k0|] /=].
      - exact: lv_ret.
      - apply: lv_sampler => k. apply: lv_putr; [fmap_solve | exact: lv_ret]. }
    have Hm1 : bad_loc_monotone 45
      (v ← get k_tbl_loc ;;
       b ← match v x with
           | Some k => ret k
           | None =>
               k ← sample uniform Key_N ;;
               #put k_tbl_loc := setm v x k ;;
               ret k
           end ;;
       ret b).
    { apply: blm_getr => v. case: (v x) => [k0|] /=.
      - exact: blm_ret.
      - apply: blm_sampler => k. apply: blm_putr_other; [done | exact: blm_ret]. }
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(t0,t1) => t0 = s0 /\ t1 = s1).
    2: { move=> t0 t1 [/= -> ->]. done. }
    exact: (GKDF_bad_already_bad_indep _ _ _ _ GKDF_bad_bad_locs_notinL GKDF_bad_bad_locs_notinR
      Hlv0 Hm0 Hlv1 Hm1 s0 s1 Hbad Hbad1 (proj1 (proj1 Hpre))).
  Qed.

  Lemma GKDF_bad_DERIVE_K_case (n : SESS) (info : Info) :
    ⊢ ⦃ fun '(s0,s1) => GKDF_bad_bad_inv (s0,s1) ⦄
      (D ← get kdone_loc ;;
       match D n with
       | Some _ => ret tt
       | None =>
           #put kdone_loc := setm D n tt ;;
           T ← get ss_tbl_loc ;;
           match T n with
           | Some s =>
               TI ← get ideal_tbl_loc ;;
               match TI (s, info) with
               | Some k => K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
               | None => k ← sample uniform Key_N ;; #put ideal_tbl_loc := setm TI (s, info) k ;; K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
               end
           | None =>
               s ← sample uniform SS_N ;;
               U ← get used_ss_loc ;;
               match U s with
               | Some _ =>
                   #put bad_loc := true ;;
                   #put ss_tbl_loc := setm T n s ;;
                   TI ← get ideal_tbl_loc ;;
                   match TI (s, info) with
                   | Some k => K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                   | None => k ← sample uniform Key_N ;; #put ideal_tbl_loc := setm TI (s, info) k ;; K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                   end
               | None =>
                   #put used_ss_loc := setm U s tt ;;
                   #put ss_tbl_loc := setm T n s ;;
                   TI ← get ideal_tbl_loc ;;
                   match TI (s, info) with
                   | Some k => K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                   | None => k ← sample uniform Key_N ;; #put ideal_tbl_loc := setm TI (s, info) k ;; K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                   end
               end
           end
       end)
      ≈
      (D ← get kdone_loc ;;
       match D n with
       | Some _ => ret tt
       | None =>
           #put kdone_loc := setm D n tt ;;
           T ← get ss_tbl_loc ;;
           match T n with
           | Some s =>
               K ← get k_tbl_loc ;;
               match K n with
               | Some _ => ret tt
               | None => k ← sample uniform Key_N ;; #put k_tbl_loc := setm K n k ;; ret tt
               end
           | None =>
               s ← sample uniform SS_N ;;
               U ← get used_ss_loc ;;
               match U s with
               | Some _ =>
                   #put bad_loc := true ;;
                   #put ss_tbl_loc := setm T n s ;;
                   K ← get k_tbl_loc ;;
                   match K n with
                   | Some _ => ret tt
                   | None => k ← sample uniform Key_N ;; #put k_tbl_loc := setm K n k ;; ret tt
                   end
               | None =>
                   #put used_ss_loc := setm U s tt ;;
                   #put ss_tbl_loc := setm T n s ;;
                   K ← get k_tbl_loc ;;
                   match K n with
                   | Some _ => ret tt
                   | None => k ← sample uniform Key_N ;; #put k_tbl_loc := setm K n k ;; ret tt
                   end
               end
           end
       end)
    ⦃ fun '(b0,s0) '(b1,s1) => GKDF_bad_bad_inv (s0,s1) /\ (get_heap s0 bad_loc = false -> b0 = b1) ⦄.
  Proof.
    apply: rpre_hypothesis_rule => s0 s1 Hpre.
    have Hsync : get_heap s0 bad_loc = get_heap s1 bad_loc.
    { move: (proj2 (proj1 Hpre)). rewrite /rel_app /get_side /=. done. }
    case: (boolP (get_heap s0 bad_loc)) => Hbad.
    1:{
      eapply rpre_weaken_rule.
      1: instantiate (1 := fun '(t0,t1) => t0 = s0 /\ t1 = s1).
      2: { move=> t0 t1 [/= -> ->]. done. }
      have Hbad1 : get_heap s1 bad_loc = true. { by rewrite -Hsync. }
      have Htail_lv : forall s : SS, lossless_valid (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc))
        (TI ← get ideal_tbl_loc ;;
         match TI (s, info) with
         | Some k => K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
         | None => k ← sample uniform Key_N ;; #put ideal_tbl_loc := setm TI (s, info) k ;; K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
         end).
      { move=> s. apply: lv_getr; [fmap_solve | move=> TI; case: (TI (s,info)) => [k|] /=].
        - apply: lv_getr; [fmap_solve | move=> K; case: (K n) => [k0|] /=].
          + exact: lv_ret.
          + apply: lv_putr; [fmap_solve | exact: lv_ret].
        - apply: lv_sampler => k. apply: lv_putr; [fmap_solve |
            apply: lv_getr; [fmap_solve | move=> K; case: (K n) => [k0|] /=] ].
          + exact: lv_ret.
          + apply: lv_putr; [fmap_solve | exact: lv_ret]. }
      have Hlv0 : lossless_valid (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc))
        (D ← get kdone_loc ;;
         match D n with
         | Some _ => ret tt
         | None =>
             #put kdone_loc := setm D n tt ;;
             T ← get ss_tbl_loc ;;
             match T n with
             | Some s => TI ← get ideal_tbl_loc ;;
                 match TI (s, info) with
                 | Some k => K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                 | None => k ← sample uniform Key_N ;; #put ideal_tbl_loc := setm TI (s, info) k ;; K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                 end
             | None =>
                 s ← sample uniform SS_N ;;
                 U ← get used_ss_loc ;;
                 match U s with
                 | Some _ =>
                     #put bad_loc := true ;;
                     #put ss_tbl_loc := setm T n s ;;
                     TI ← get ideal_tbl_loc ;;
                     match TI (s, info) with
                     | Some k => K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                     | None => k ← sample uniform Key_N ;; #put ideal_tbl_loc := setm TI (s, info) k ;; K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                     end
                 | None =>
                     #put used_ss_loc := setm U s tt ;;
                     #put ss_tbl_loc := setm T n s ;;
                     TI ← get ideal_tbl_loc ;;
                     match TI (s, info) with
                     | Some k => K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                     | None => k ← sample uniform Key_N ;; #put ideal_tbl_loc := setm TI (s, info) k ;; K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                     end
                 end
             end
         end).
      { apply: lv_getr; [fmap_solve | move=> D; case: (D n) => [[]|] /=].
        - exact: lv_ret.
        - apply: lv_putr; [fmap_solve |
            apply: lv_getr; [fmap_solve | move=> T; case: (T n) => [s|] /=] ].
          + exact: (Htail_lv s).
          + apply: lv_sampler => s. apply: lv_getr; [fmap_solve | move=> U; case: (U s) => [[]|] /=].
            * apply: lv_putr; [fmap_solve | apply: lv_putr; [fmap_solve | exact: (Htail_lv s)]].
            * apply: lv_putr; [fmap_solve | apply: lv_putr; [fmap_solve | exact: (Htail_lv s)]]. }
      have Htail_blm : forall s : SS, bad_loc_monotone 45
        (TI ← get ideal_tbl_loc ;;
         match TI (s, info) with
         | Some k => K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
         | None => k ← sample uniform Key_N ;; #put ideal_tbl_loc := setm TI (s, info) k ;; K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
         end).
      { move=> s. apply: blm_getr => TI. case: (TI (s,info)) => [k|] /=.
        - apply: blm_getr => K. case: (K n) => [k0|] /=.
          + exact: blm_ret.
          + apply: blm_putr_other; [done | exact: blm_ret].
        - apply: blm_sampler => k. apply: blm_putr_other; [done |
            apply: blm_getr => K; case: (K n) => [k0|] /=].
          + exact: blm_ret.
          + apply: blm_putr_other; [done | exact: blm_ret]. }
      have Hm0 : bad_loc_monotone 45
        (D ← get kdone_loc ;;
         match D n with
         | Some _ => ret tt
         | None =>
             #put kdone_loc := setm D n tt ;;
             T ← get ss_tbl_loc ;;
             match T n with
             | Some s => TI ← get ideal_tbl_loc ;;
                 match TI (s, info) with
                 | Some k => K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                 | None => k ← sample uniform Key_N ;; #put ideal_tbl_loc := setm TI (s, info) k ;; K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                 end
             | None =>
                 s ← sample uniform SS_N ;;
                 U ← get used_ss_loc ;;
                 match U s with
                 | Some _ =>
                     #put bad_loc := true ;;
                     #put ss_tbl_loc := setm T n s ;;
                     TI ← get ideal_tbl_loc ;;
                     match TI (s, info) with
                     | Some k => K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                     | None => k ← sample uniform Key_N ;; #put ideal_tbl_loc := setm TI (s, info) k ;; K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                     end
                 | None =>
                     #put used_ss_loc := setm U s tt ;;
                     #put ss_tbl_loc := setm T n s ;;
                     TI ← get ideal_tbl_loc ;;
                     match TI (s, info) with
                     | Some k => K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                     | None => k ← sample uniform Key_N ;; #put ideal_tbl_loc := setm TI (s, info) k ;; K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n k ;; ret tt end
                     end
                 end
             end
         end).
      { apply: blm_getr => D. case: (D n) => [[]|] /=.
        - exact: blm_ret.
        - apply: blm_putr_other; [done |
            apply: blm_getr => T; case: (T n) => [s|] /=].
          + exact: (Htail_blm s).
          + apply: blm_sampler => s. apply: blm_getr => U. case: (U s) => [[]|] /=.
            * apply: blm_putr_bad. apply: blm_putr_other; [done | exact: (Htail_blm s)].
            * apply: blm_putr_other; [done | apply: blm_putr_other; [done | exact: (Htail_blm s)]]. }
      have Htail_lv' : lossless_valid (unionm KDF_loc (unionm KEYS_bad_loc KDFC_loc))
        (K ← get k_tbl_loc ;;
         match K n with
         | Some _ => ret tt
         | None => k ← sample uniform Key_N ;; #put k_tbl_loc := setm K n k ;; ret tt
         end).
      { apply: lv_getr; [fmap_solve | move=> K; case: (K n) => [k0|] /=].
        - exact: lv_ret.
        - apply: lv_sampler => k. apply: lv_putr; [fmap_solve | exact: lv_ret]. }
      have Hlv1 : lossless_valid (unionm KDF_loc (unionm KEYS_bad_loc KDFC_loc))
        (D ← get kdone_loc ;;
         match D n with
         | Some _ => ret tt
         | None =>
             #put kdone_loc := setm D n tt ;;
             T ← get ss_tbl_loc ;;
             match T n with
             | Some s =>
                 K ← get k_tbl_loc ;;
                 match K n with
                 | Some _ => ret tt
                 | None => k ← sample uniform Key_N ;; #put k_tbl_loc := setm K n k ;; ret tt
                 end
             | None =>
                 s ← sample uniform SS_N ;;
                 U ← get used_ss_loc ;;
                 match U s with
                 | Some _ =>
                     #put bad_loc := true ;;
                     #put ss_tbl_loc := setm T n s ;;
                     K ← get k_tbl_loc ;;
                     match K n with
                     | Some _ => ret tt
                     | None => k ← sample uniform Key_N ;; #put k_tbl_loc := setm K n k ;; ret tt
                     end
                 | None =>
                     #put used_ss_loc := setm U s tt ;;
                     #put ss_tbl_loc := setm T n s ;;
                     K ← get k_tbl_loc ;;
                     match K n with
                     | Some _ => ret tt
                     | None => k ← sample uniform Key_N ;; #put k_tbl_loc := setm K n k ;; ret tt
                     end
                 end
             end
         end).
      { apply: lv_getr; [fmap_solve | move=> D; case: (D n) => [[]|] /=].
        - exact: lv_ret.
        - apply: lv_putr; [fmap_solve |
            apply: lv_getr; [fmap_solve | move=> T; case: (T n) => [s|] /=] ].
          + exact: Htail_lv'.
          + apply: lv_sampler => s. apply: lv_getr; [fmap_solve | move=> U; case: (U s) => [[]|] /=].
            * apply: lv_putr; [fmap_solve | apply: lv_putr; [fmap_solve | exact: Htail_lv']].
            * apply: lv_putr; [fmap_solve | apply: lv_putr; [fmap_solve | exact: Htail_lv']]. }
      have Htail_blm' : bad_loc_monotone 45
        (K ← get k_tbl_loc ;;
         match K n with
         | Some _ => ret tt
         | None => k ← sample uniform Key_N ;; #put k_tbl_loc := setm K n k ;; ret tt
         end).
      { apply: blm_getr => K. case: (K n) => [k0|] /=.
        - exact: blm_ret.
        - apply: blm_sampler => k. apply: blm_putr_other; [done | exact: blm_ret]. }
      have Hm1 : bad_loc_monotone 45
        (D ← get kdone_loc ;;
         match D n with
         | Some _ => ret tt
         | None =>
             #put kdone_loc := setm D n tt ;;
             T ← get ss_tbl_loc ;;
             match T n with
             | Some s =>
                 K ← get k_tbl_loc ;;
                 match K n with
                 | Some _ => ret tt
                 | None => k ← sample uniform Key_N ;; #put k_tbl_loc := setm K n k ;; ret tt
                 end
             | None =>
                 s ← sample uniform SS_N ;;
                 U ← get used_ss_loc ;;
                 match U s with
                 | Some _ =>
                     #put bad_loc := true ;;
                     #put ss_tbl_loc := setm T n s ;;
                     K ← get k_tbl_loc ;;
                     match K n with
                     | Some _ => ret tt
                     | None => k ← sample uniform Key_N ;; #put k_tbl_loc := setm K n k ;; ret tt
                     end
                 | None =>
                     #put used_ss_loc := setm U s tt ;;
                     #put ss_tbl_loc := setm T n s ;;
                     K ← get k_tbl_loc ;;
                     match K n with
                     | Some _ => ret tt
                     | None => k ← sample uniform Key_N ;; #put k_tbl_loc := setm K n k ;; ret tt
                     end
                 end
             end
         end).
      { apply: blm_getr => D. case: (D n) => [[]|] /=.
        - exact: blm_ret.
        - apply: blm_putr_other; [done |
            apply: blm_getr => T; case: (T n) => [s|] /=].
          + exact: Htail_blm'.
          + apply: blm_sampler => s. apply: blm_getr => U. case: (U s) => [[]|] /=.
            * apply: blm_putr_bad. apply: blm_putr_other; [done | exact: Htail_blm'].
            * apply: blm_putr_other; [done | apply: blm_putr_other; [done | exact: Htail_blm']]. }
      exact: (GKDF_bad_already_bad_indep _ _ _ _ GKDF_bad_bad_locs_notinL GKDF_bad_bad_locs_notinR
        Hlv0 Hm0 Hlv1 Hm1 s0 s1 Hbad Hbad1 (proj1 (proj1 Hpre))).
    }
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(t0,t1) => t0 = s0 /\ t1 = s1).
    2: { move=> t0 t1 [/= -> ->]. done. }
    move: Hbad => /negbTE Hbad'.
    have Hg := (proj2 Hpre) Hbad'.
    move: Hg. rewrite /rel_app /get_side /=.
    move=> [HD [HT [HU [HK [Hcorr [Hinj Hfresh]]]]]].
    eapply (r_get_remember_lhs kdone_loc _ _ (fun '(t0,t1) => t0 = s0 /\ t1 = s1)).
    move=> D.
    eapply (r_get_remember_rhs kdone_loc _ _ ((fun '(t0,t1) => t0 = s0 /\ t1 = s1) ⋊ rem_lhs kdone_loc D)).
    move=> D'.
    apply: rpre_hypothesis_rule => t0 t1 Hp.
    case: Hp => [[[Heq0 Heq1] HeqD] HeqD'].
    subst t0 t1.
    move: HeqD HeqD'. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=. move=> HeqD HeqD'.
    have HDD' : D = D'.
    { rewrite -HeqD -HeqD'. exact: HD. }
    subst D'.
    case HDn: (D n) => [[]|].
    1:{
      rewrite -HDD' HDn /=.
      apply: r_ret => t0 t1 h.
      split; [ | done].
      move: h => [/= -> ->]. exact: Hpre.
    }
    rewrite -HDD' HDn /=.
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(t0,t1) => t0 = s0 /\ t1 = s1).
    2: { move=> t0 t1 [/= -> ->]. done. }
    eapply (r_put_vs_put kdone_loc (setm D n tt) kdone_loc (setm D n tt) _ _
      (fun '(t0,t1) => t0 = s0 /\ t1 = s1)).
    apply: rpre_hypothesis_rule => t2 t3 Hp2.
    case: Hp2 => [t3'' [[t2'' [[Heq2 Heq3] ->]] ->]].
    subst t2'' t3''.
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(t0,t1) => t0 = set_heap s0 kdone_loc (setm D n tt) /\ t1 = set_heap s1 kdone_loc (setm D n tt)).
    2: { move=> t0 t1 [/= -> ->]. done. }
    eapply (r_get_remember_lhs ss_tbl_loc _ _ (fun '(t0,t1) => t0 = set_heap s0 kdone_loc (setm D n tt) /\ t1 = set_heap s1 kdone_loc (setm D n tt))).
    move=> T.
    eapply (r_get_remember_rhs ss_tbl_loc _ _ ((fun '(t0,t1) => t0 = set_heap s0 kdone_loc (setm D n tt) /\ t1 = set_heap s1 kdone_loc (setm D n tt)) ⋊ rem_lhs ss_tbl_loc T)).
    move=> T'.
    apply: rpre_hypothesis_rule => t4 t5 Hp3.
    case: Hp3 => [[[Heq4 Heq5] HeqT] HeqT'].
    subst t4 t5.
    move: HeqT HeqT'. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=. move=> HeqT HeqT'.
    have HTT' : T = T'.
    { rewrite -HeqT -HeqT'.
      rewrite (get_set_heap_neq _ _ _ _ (isT : ss_tbl_loc.1 != kdone_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : ss_tbl_loc.1 != kdone_loc.1)).
      exact: HT. }
    subst T'.
    case HTn: (T n) => [s|].
    1:{
      rewrite -HTT' HTn /=.
      eapply rpre_weaken_rule.
      1: instantiate (1 := fun '(t0,t1) => t0 = set_heap s0 kdone_loc (setm D n tt) /\ t1 = set_heap s1 kdone_loc (setm D n tt)).
      2: { move=> t0 t1 [/= -> ->]. done. }
      eapply (r_get_remember_lhs ideal_tbl_loc _ _ (fun '(t0,t1) => t0 = set_heap s0 kdone_loc (setm D n tt) /\ t1 = set_heap s1 kdone_loc (setm D n tt))).
      move=> TI.
      apply: rpre_hypothesis_rule => t6 t7 Hp4.
      case: Hp4 => [[Heq6 Heq7] HeqTI].
      subst t6 t7.
      move: HeqTI. rewrite /rem_lhs /get_side /=. move=> HeqTI.
      have HeqT0 : get_heap s0 ss_tbl_loc = T.
      { rewrite -HeqT (get_set_heap_neq _ _ _ _ (isT : ss_tbl_loc.1 != kdone_loc.1)). reflexivity. }
      have HeqTI0 : get_heap s0 ideal_tbl_loc = TI.
      { rewrite -HeqTI (get_set_heap_neq _ _ _ _ (isT : ideal_tbl_loc.1 != kdone_loc.1)). reflexivity. }
      case HTIeq: (TI (s,info)) => [k|].
      1:{
        exfalso.
        have HneTI : get_heap s0 ideal_tbl_loc (s, info) <> None.
        { rewrite HeqTI0 HTIeq. discriminate. }
        have Hex := Hfresh s info HneTI.
        destruct Hex as [n0 [HDn0 HTn0]].
        have HTn0' : get_heap s0 ss_tbl_loc n = Some s.
        { rewrite HeqT0. exact: HTn. }
        have Heqn0 : n0 = n.
        { exact: (Hinj n0 n s HTn0 HTn0'). }
        subst n0.
        rewrite HeqD in HDn0.
        rewrite HDn in HDn0.
        discriminate.
      }
      ssprove_swap_seq_lhs [:: 1 ; 0 ]%N.
      eapply rpre_weaken_rule.
      1: instantiate (1 := fun '(t0,t1) => t0 = set_heap s0 kdone_loc (setm D n tt) /\ t1 = set_heap s1 kdone_loc (setm D n tt)).
      2: { move=> t0 t1 [/= -> ->]. done. }
      eapply (r_get_remember_lhs k_tbl_loc _ _ (fun '(t0,t1) => t0 = set_heap s0 kdone_loc (setm D n tt) /\ t1 = set_heap s1 kdone_loc (setm D n tt))).
      move=> K0.
      eapply (r_get_remember_rhs k_tbl_loc _ _ ((fun '(t0,t1) => t0 = set_heap s0 kdone_loc (setm D n tt) /\ t1 = set_heap s1 kdone_loc (setm D n tt)) ⋊ rem_lhs k_tbl_loc K0)).
      move=> K1.
      apply: rpre_hypothesis_rule => t8 t9 Hp5.
      case: Hp5 => [[[Heq8 Heq9] HeqK0] HeqK1].
      subst t8 t9.
      move: HeqK0 HeqK1. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=. move=> HeqK0 HeqK1.
      have HeqK00 : get_heap s0 k_tbl_loc = K0.
      { rewrite -HeqK0 (get_set_heap_neq _ _ _ _ (isT : k_tbl_loc.1 != kdone_loc.1)). reflexivity. }
      have HeqK11 : get_heap s1 k_tbl_loc = K1.
      { rewrite -HeqK1 (get_set_heap_neq _ _ _ _ (isT : k_tbl_loc.1 != kdone_loc.1)). reflexivity. }
      have HK01 : K0 = K1.
      { rewrite -HeqK00 -HeqK11. exact: HK. }
      subst K1.
      case HK0n: (K0 n) => [k0|].
      1:{
        rewrite -HK01 HK0n /=.
        apply r_const_sample_L. 1: exact _.
        move=> a1.
        eapply rpre_weaken_rule.
        1: instantiate (1 := fun '(t0,t1) => t0 = set_heap s0 kdone_loc (setm D n tt) /\ t1 = set_heap s1 kdone_loc (setm D n tt)).
        2: { move=> t0 t1 [/= -> ->]. done. }
        eapply (r_put_lhs ideal_tbl_loc (setm TI (s, info) a1) _ _
          (fun '(t0,t1) => t0 = set_heap s0 kdone_loc (setm D n tt) /\ t1 = set_heap s1 kdone_loc (setm D n tt))).
        apply: rpre_hypothesis_rule => t10 t11 Hp6.
        case: Hp6 => [s0'''' [Heq26 ->]].
        case: Heq26 => [-> ->].
        apply: r_ret => t12 t13 h.
        move: h => [/= -> ->].
        split; [ | done].
        apply: GKDF_bad_bad_inv_intro.
        - move=> l Hnotin.
          rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l ideal_tbl_loc Hnotin (ltac:(fmap_solve)))).
          rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l kdone_loc Hnotin (ltac:(fmap_solve)))).
          rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l kdone_loc Hnotin (ltac:(fmap_solve)))).
          exact: (proj1 (proj1 Hpre) l Hnotin).
        - rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != ideal_tbl_loc.1)).
          rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != kdone_loc.1)).
          rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != kdone_loc.1)).
          exact: Hsync.
        - move=> _.
          rewrite (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != ideal_tbl_loc.1)) get_set_heap_eq.
          rewrite get_set_heap_eq.
          split; [reflexivity | ].
          rewrite (get_set_heap_neq _ _ _ _ (isT : ss_tbl_loc.1 != ideal_tbl_loc.1)).
          rewrite (get_set_heap_neq _ _ _ _ (isT : ss_tbl_loc.1 != kdone_loc.1)).
          rewrite (get_set_heap_neq _ _ _ _ (isT : ss_tbl_loc.1 != kdone_loc.1)).
          split; [exact: HT | ].
          rewrite (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != ideal_tbl_loc.1)).
          rewrite (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != kdone_loc.1)).
          rewrite (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != kdone_loc.1)).
          split; [exact: HU | ].
          rewrite (get_set_heap_neq _ _ _ _ (isT : k_tbl_loc.1 != ideal_tbl_loc.1)).
          rewrite (get_set_heap_neq _ _ _ _ (isT : k_tbl_loc.1 != kdone_loc.1)).
          rewrite (get_set_heap_neq _ _ _ _ (isT : k_tbl_loc.1 != kdone_loc.1)).
          split; [exact: HK | ].
          split; [exact: Hcorr | ].
          split; [exact: Hinj | ].
          rewrite get_set_heap_eq.
          move=> s' info' Hne.
          move: Hne.
          rewrite setmE.
          case Heq: ((s', info') == (s, info)).
          { move=> _. exists n. split.
            - rewrite setmE eq_refl. reflexivity.
            - rewrite HeqT0. move/eqP: Heq => Heq. case: Heq => -> _. exact: HTn.
          }
          { move=> HneTI2.
            rewrite -HeqTI0 in HneTI2.
            have [n0 [HDn0 HTn0]] := Hfresh s' info' HneTI2.
            exists n0. split.
            - rewrite setmE.
              case Heqn: (n0 == n).
              + move/eqP: Heqn => Heqn. subst n0. rewrite HeqD in HDn0. rewrite HDn in HDn0. discriminate.
              + rewrite -HeqD. exact: HDn0.
            - exact: HTn0.
          }
      }
      rewrite -HK01 HK0n /=.
      eapply rpre_weaken_rule.
      1: instantiate (1 := fun '(t0,t1) => t0 = set_heap s0 kdone_loc (setm D n tt) /\ t1 = set_heap s1 kdone_loc (setm D n tt)).
      2: { move=> t0 t1 [/= -> ->]. done. }
      eapply (r_uniform_bij _ _ _ _ id).
      1: exists id; done.
      move=> a1.
      eapply rpre_weaken_rule.
      1: instantiate (1 := fun '(t0,t1) => t0 = set_heap s0 kdone_loc (setm D n tt) /\ t1 = set_heap s1 kdone_loc (setm D n tt)).
      2: { move=> t0 t1 [/= -> ->]. done. }
      eapply (r_put_lhs ideal_tbl_loc (setm TI (s, info) a1) _ _
        (fun '(t0,t1) => t0 = set_heap s0 kdone_loc (setm D n tt) /\ t1 = set_heap s1 kdone_loc (setm D n tt))).
      apply: rpre_hypothesis_rule => t8' t9' Hp6'.
      move: Hp6' => [s0'''' [Heq26' ->]].
      case: Heq26' => [-> ->].
      eapply rpre_weaken_rule.
      1: instantiate (1 := fun '(t0,t1) => t0 = set_heap (set_heap s0 kdone_loc (setm D n tt)) ideal_tbl_loc (setm TI (s, info) a1) /\ t1 = set_heap s1 kdone_loc (setm D n tt)).
      2: { move=> t0 t1 [/= -> ->]. done. }
      eapply (r_put_vs_put k_tbl_loc (setm K0 n a1) k_tbl_loc (setm K0 n a1) _ _
        (fun '(t0,t1) => t0 = set_heap (set_heap s0 kdone_loc (setm D n tt)) ideal_tbl_loc (setm TI (s, info) a1) /\ t1 = set_heap s1 kdone_loc (setm D n tt))).
      apply: r_ret => tt2 tt3 h.
      move: h => [tt3'' [[tt2'' [[Heq27 Heq28] ->]] ->]].
      subst tt2'' tt3''.
      split; [ | done].
      apply: GKDF_bad_bad_inv_intro.
      - move=> l Hnotin.
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l k_tbl_loc Hnotin (ltac:(fmap_solve)))).
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l ideal_tbl_loc Hnotin (ltac:(fmap_solve)))).
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l kdone_loc Hnotin (ltac:(fmap_solve)))).
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l k_tbl_loc Hnotin (ltac:(fmap_solve)))).
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l kdone_loc Hnotin (ltac:(fmap_solve)))).
        exact: (proj1 (proj1 Hpre) l Hnotin).
      - rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != k_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != ideal_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != kdone_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != k_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != kdone_loc.1)).
        exact: Hsync.
      - move=> _.
        rewrite (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != k_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != ideal_tbl_loc.1)).
        rewrite get_set_heap_eq.
        rewrite (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != k_tbl_loc.1)).
        rewrite get_set_heap_eq.
        split; [reflexivity | ].
        rewrite (get_set_heap_neq _ _ _ _ (isT : ss_tbl_loc.1 != k_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : ss_tbl_loc.1 != ideal_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : ss_tbl_loc.1 != kdone_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : ss_tbl_loc.1 != k_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : ss_tbl_loc.1 != kdone_loc.1)).
        split; [exact: HT | ].
        rewrite (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != k_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != ideal_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != kdone_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != k_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != kdone_loc.1)).
        split; [exact: HU | ].
        rewrite get_set_heap_eq.
        rewrite get_set_heap_eq.
        split; [reflexivity | ].
        split; [exact: Hcorr | ].
        split; [exact: Hinj | ].
        rewrite (get_set_heap_neq _ _ _ _ (isT : ideal_tbl_loc.1 != k_tbl_loc.1)).
        rewrite get_set_heap_eq.
        move=> s' info' Hne.
        move: Hne.
        rewrite setmE.
        case Heq: ((s', info') == (s, info)).
        { move=> _. exists n. split.
          - rewrite setmE eq_refl. reflexivity.
          - rewrite HeqT0. move/eqP: Heq => Heq. case: Heq => -> _. exact: HTn.
        }
        { move=> HneTI2.
          rewrite -HeqTI0 in HneTI2.
          have [n0 [HDn0 HTn0]] := Hfresh s' info' HneTI2.
          exists n0. split.
          - rewrite setmE. case Heqn: (n0 == n).
            + move/eqP: Heqn => Heqn. subst n0. rewrite HeqD in HDn0. rewrite HDn in HDn0. discriminate.
            + rewrite -HeqD. exact: HDn0.
          - exact: HTn0.
        }
    }
    rewrite -HTT' HTn /=.
    eapply (r_uniform_bij _ _ _ _ id).
    1: exists id; done.
    move=> s.
    simpl.
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(t0,t1) => t0 = set_heap s0 kdone_loc (setm D n tt) /\ t1 = set_heap s1 kdone_loc (setm D n tt)).
    2: { move=> t0 t1 [/= -> ->]. done. }
    eapply (r_get_remember_lhs used_ss_loc _ _ (fun '(t0,t1) => t0 = set_heap s0 kdone_loc (setm D n tt) /\ t1 = set_heap s1 kdone_loc (setm D n tt))).
    move=> U0.
    eapply (r_get_remember_rhs used_ss_loc _ _ ((fun '(t0,t1) => t0 = set_heap s0 kdone_loc (setm D n tt) /\ t1 = set_heap s1 kdone_loc (setm D n tt)) ⋊ rem_lhs used_ss_loc U0)).
    move=> U1.
    apply: rpre_hypothesis_rule => t14 t15 Hp7.
    case: Hp7 => [[[Heq14 Heq15] HeqU0] HeqU1].
    subst t14 t15.
    move: HeqU0 HeqU1. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=. move=> HeqU0 HeqU1.
    have HeqU00 : get_heap s0 used_ss_loc = U0.
    { rewrite -HeqU0 (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != kdone_loc.1)). reflexivity. }
    have HeqU11 : get_heap s1 used_ss_loc = U1.
    { rewrite -HeqU1 (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != kdone_loc.1)). reflexivity. }
    have HU01 : U0 = U1.
    { rewrite -HeqU00 -HeqU11. exact: HU. }
    subst U1.
    case HU0s: (U0 s) => [[]|].
    1:{
      rewrite -HU01 HU0s /=.
      eapply rpre_weaken_rule.
      1: instantiate (1 := fun '(t0,t1) => t0 = set_heap s0 kdone_loc (setm D n tt) /\ t1 = set_heap s1 kdone_loc (setm D n tt)).
      2: { move=> t0 t1 [/= -> ->]. done. }
      eapply (r_put_vs_put bad_loc true bad_loc true _ _
        (fun '(t0,t1) => t0 = set_heap s0 kdone_loc (setm D n tt) /\ t1 = set_heap s1 kdone_loc (setm D n tt))).
      apply: rpre_hypothesis_rule => tA tB HpA.
      case: HpA => [tB'' [[tA'' [[HeqA HeqB] ->]] ->]].
      subst tA'' tB''.
      eapply rpre_weaken_rule.
      1: instantiate (1 := fun '(t0,t1) => t0 = set_heap (set_heap s0 kdone_loc (setm D n tt)) bad_loc true /\ t1 = set_heap (set_heap s1 kdone_loc (setm D n tt)) bad_loc true).
      2: { move=> t0 t1 [/= -> ->]. done. }
      eapply (r_put_vs_put ss_tbl_loc (setm T n s) ss_tbl_loc (setm T n s) _ _
        (fun '(t0,t1) => t0 = set_heap (set_heap s0 kdone_loc (setm D n tt)) bad_loc true /\ t1 = set_heap (set_heap s1 kdone_loc (setm D n tt)) bad_loc true)).
      apply: rpre_hypothesis_rule => tC tD HpC.
      case: HpC => [tD'' [[tC'' [[HeqC HeqDp] ->]] ->]].
      subst tC'' tD''.
      eapply rpre_weaken_rule.
      1: instantiate (1 := fun '(t0,t1) => t0 = set_heap (set_heap (set_heap s0 kdone_loc (setm D n tt)) bad_loc true) ss_tbl_loc (setm T n s) /\ t1 = set_heap (set_heap (set_heap s1 kdone_loc (setm D n tt)) bad_loc true) ss_tbl_loc (setm T n s)).
      2: { move=> t0 t1 [/= -> ->]. done. }
      eapply (GKDF_bad_already_bad_indep _ _ _ _ GKDF_bad_bad_locs_notinL GKDF_bad_bad_locs_notinR).
      - apply: lv_getr. 1: fmap_solve.
        move=> TI0. case: (TI0 (s,info)) => [k|] /=.
        + apply: lv_getr. 1: fmap_solve.
          move=> K0; case: (K0 n) => [k0|] /=.
          * exact: lv_ret.
          * apply: lv_putr; [fmap_solve | exact: lv_ret].
        + apply: lv_sampler => k. apply: lv_putr; [fmap_solve |
            apply: lv_getr; [fmap_solve | move=> K0; case: (K0 n) => [k0|] /=] ].
          * exact: lv_ret.
          * apply: lv_putr; [fmap_solve | exact: lv_ret].
      - apply: blm_getr => TI0. case: (TI0 (s,info)) => [k|] /=.
        + apply: blm_getr => K0. case: (K0 n) => [k0|] /=.
          * exact: blm_ret.
          * apply: blm_putr_other; [done | exact: blm_ret].
        + apply: blm_sampler => k. apply: blm_putr_other; [done |
            apply: blm_getr => K0; case: (K0 n) => [k0|] /=].
          * exact: blm_ret.
          * apply: blm_putr_other; [done | exact: blm_ret].
      - apply: lv_getr. 1: fmap_solve.
        move=> K0; case: (K0 n) => [k0|] /=.
        + exact: lv_ret.
        + apply: lv_sampler => k. apply: lv_putr; [fmap_solve | exact: lv_ret].
      - apply: blm_getr => K0. case: (K0 n) => [k0|] /=.
        + exact: blm_ret.
        + apply: blm_sampler => k. apply: blm_putr_other; [done | exact: blm_ret].
      - rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != ss_tbl_loc.1)) get_set_heap_eq. reflexivity.
      - rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != ss_tbl_loc.1)) get_set_heap_eq. reflexivity.
      - move=> l Hnotin.
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l ss_tbl_loc Hnotin (ltac:(fmap_solve)))).
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l bad_loc Hnotin (ltac:(fmap_solve)))).
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l kdone_loc Hnotin (ltac:(fmap_solve)))).
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l ss_tbl_loc Hnotin (ltac:(fmap_solve)))).
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l bad_loc Hnotin (ltac:(fmap_solve)))).
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l kdone_loc Hnotin (ltac:(fmap_solve)))).
        exact: (proj1 (proj1 Hpre) l Hnotin).
    }
    rewrite -HU01 HU0s /=.
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(t0,t1) => t0 = set_heap s0 kdone_loc (setm D n tt) /\ t1 = set_heap s1 kdone_loc (setm D n tt)).
    2: { move=> t0 t1 [/= -> ->]. done. }
    eapply (r_put_vs_put used_ss_loc (setm U0 s tt) used_ss_loc (setm U0 s tt) _ _
      (fun '(t0,t1) => t0 = set_heap s0 kdone_loc (setm D n tt) /\ t1 = set_heap s1 kdone_loc (setm D n tt))).
    apply: rpre_hypothesis_rule => tE tF HpE.
    case: HpE => [tF'' [[tE'' [[HeqE HeqF] ->]] ->]].
    subst tE'' tF''.
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(t0,t1) => t0 = set_heap (set_heap s0 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt) /\ t1 = set_heap (set_heap s1 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)).
    2: { move=> t0 t1 [/= -> ->]. done. }
    eapply (r_put_vs_put ss_tbl_loc (setm T n s) ss_tbl_loc (setm T n s) _ _
      (fun '(t0,t1) => t0 = set_heap (set_heap s0 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt) /\ t1 = set_heap (set_heap s1 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt))).
    apply: rpre_hypothesis_rule => tG tH HpG.
    case: HpG => [tH'' [[tG'' [[HeqG HeqHh] ->]] ->]].
    subst tG'' tH''.
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(t0,t1) => t0 = set_heap (set_heap (set_heap s0 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s) /\ t1 = set_heap (set_heap (set_heap s1 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s)).
    2: { move=> t0 t1 [/= -> ->]. done. }
    eapply (r_get_remember_lhs ideal_tbl_loc _ _ (fun '(t0,t1) => t0 = set_heap (set_heap (set_heap s0 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s) /\ t1 = set_heap (set_heap (set_heap s1 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s))).
    move=> TI.
    apply: rpre_hypothesis_rule => tI tJ HpI.
    case: HpI => [[HeqI HeqJ] HeqTI].
    subst tI tJ.
    move: HeqTI. rewrite /rem_lhs /get_side /=. move=> HeqTI.
    have HeqTI0 : get_heap s0 ideal_tbl_loc = TI.
    { rewrite -HeqTI.
      rewrite (get_set_heap_neq _ _ _ _ (isT : ideal_tbl_loc.1 != ss_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : ideal_tbl_loc.1 != used_ss_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : ideal_tbl_loc.1 != kdone_loc.1)).
      reflexivity. }
    have HeqT0 : get_heap s0 ss_tbl_loc = T.
    { rewrite -HeqT (get_set_heap_neq _ _ _ _ (isT : ss_tbl_loc.1 != kdone_loc.1)). reflexivity. }
    case HTIeq: (TI (s,info)) => [k|].
    1:{
      exfalso.
      have HneTI : get_heap s0 ideal_tbl_loc (s, info) <> None.
      { rewrite HeqTI0 HTIeq. discriminate. }
      have [n0 [HDn0 HTn0]] := Hfresh s info HneTI.
      have HUs0 : get_heap s0 used_ss_loc s = None.
      { rewrite HeqU00. exact: HU0s. }
      have HUsome : get_heap s0 used_ss_loc s = Some tt.
      { apply: (proj2 (Hcorr s)). exists n0. exact: HTn0. }
      rewrite HUsome in HUs0. discriminate.
    }
    ssprove_swap_seq_lhs [:: 1 ; 0 ]%N.
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(t0,t1) => t0 = set_heap (set_heap (set_heap s0 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s) /\ t1 = set_heap (set_heap (set_heap s1 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s)).
    2: { move=> t0 t1 [/= -> ->]. done. }
    eapply (r_get_remember_lhs k_tbl_loc _ _ (fun '(t0,t1) => t0 = set_heap (set_heap (set_heap s0 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s) /\ t1 = set_heap (set_heap (set_heap s1 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s))).
    move=> K0.
    eapply (r_get_remember_rhs k_tbl_loc _ _ ((fun '(t0,t1) => t0 = set_heap (set_heap (set_heap s0 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s) /\ t1 = set_heap (set_heap (set_heap s1 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s)) ⋊ rem_lhs k_tbl_loc K0)).
    move=> K1.
    apply: rpre_hypothesis_rule => tK tL HpK.
    case: HpK => [[[HeqK HeqL] HeqK0] HeqK1].
    subst tK tL.
    move: HeqK0 HeqK1. rewrite /rem_lhs /rem_rhs /rem_inv /get_side /=. move=> HeqK0 HeqK1.
    have HeqK00 : get_heap s0 k_tbl_loc = K0.
    { rewrite -HeqK0.
      rewrite (get_set_heap_neq _ _ _ _ (isT : k_tbl_loc.1 != ss_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : k_tbl_loc.1 != used_ss_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : k_tbl_loc.1 != kdone_loc.1)).
      reflexivity. }
    have HeqK11 : get_heap s1 k_tbl_loc = K1.
    { rewrite -HeqK1.
      rewrite (get_set_heap_neq _ _ _ _ (isT : k_tbl_loc.1 != ss_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : k_tbl_loc.1 != used_ss_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : k_tbl_loc.1 != kdone_loc.1)).
      reflexivity. }
    have HK01 : K0 = K1.
    { rewrite -HeqK00 -HeqK11. exact: HK. }
    subst K1.
    case HK0n: (K0 n) => [k0|].
    1:{
      rewrite -HK01 HK0n /=.
      apply r_const_sample_L. 1: exact _.
      move=> a1.
      eapply rpre_weaken_rule.
      1: instantiate (1 := fun '(t0,t1) => t0 = set_heap (set_heap (set_heap s0 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s) /\ t1 = set_heap (set_heap (set_heap s1 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s)).
      2: { move=> t0 t1 [/= -> ->]. done. }
      eapply (r_put_lhs ideal_tbl_loc (setm TI (s, info) a1) _ _
        (fun '(t0,t1) => t0 = set_heap (set_heap (set_heap s0 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s) /\ t1 = set_heap (set_heap (set_heap s1 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s))).
      apply: rpre_hypothesis_rule => tM tN HpM.
      case: HpM => [sM'' [HeqM ->]].
      case: HeqM => [-> ->].
      apply: r_ret => tO tP h.
      move: h => [/= -> ->].
      split; [ | done].
      apply: GKDF_bad_bad_inv_intro.
      - move=> l Hnotin.
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l ideal_tbl_loc Hnotin (ltac:(fmap_solve)))).
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l ss_tbl_loc Hnotin (ltac:(fmap_solve)))).
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l used_ss_loc Hnotin (ltac:(fmap_solve)))).
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l kdone_loc Hnotin (ltac:(fmap_solve)))).
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l ss_tbl_loc Hnotin (ltac:(fmap_solve)))).
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l used_ss_loc Hnotin (ltac:(fmap_solve)))).
        rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l kdone_loc Hnotin (ltac:(fmap_solve)))).
        exact: (proj1 (proj1 Hpre) l Hnotin).
      - rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != ideal_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != ss_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != used_ss_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != kdone_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != ss_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != used_ss_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != kdone_loc.1)).
        exact: Hsync.
      - move=> _.
        rewrite (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != ideal_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != ss_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != ss_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != used_ss_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != used_ss_loc.1)).
        rewrite !get_set_heap_eq.
        split; [reflexivity | ].
        rewrite (get_set_heap_neq _ _ _ _ (isT : ss_tbl_loc.1 != ideal_tbl_loc.1)).
        rewrite get_set_heap_eq.
        split; [reflexivity | ].
        rewrite (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != ideal_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != ss_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != ss_tbl_loc.1)).
        rewrite !get_set_heap_eq.
        split; [reflexivity | ].
        rewrite (get_set_heap_neq _ _ _ _ (isT : k_tbl_loc.1 != ideal_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : k_tbl_loc.1 != ss_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : k_tbl_loc.1 != ss_tbl_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : k_tbl_loc.1 != used_ss_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : k_tbl_loc.1 != used_ss_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : k_tbl_loc.1 != kdone_loc.1)).
        rewrite (get_set_heap_neq _ _ _ _ (isT : k_tbl_loc.1 != kdone_loc.1)).
        split; [exact: HK | ].
        split.
        { rewrite -HeqT0 -HeqU00.
          eapply (ss_used_correspondence_extend (get_heap s0 ss_tbl_loc) (get_heap s0 used_ss_loc) n s Hcorr).
          - rewrite HeqT0. exact: HTn.
          - rewrite HeqU00. exact: HU0s.
        }
        split.
        { rewrite -HeqT0.
          eapply (ss_tbl_injective_extend (get_heap s0 ss_tbl_loc) n s Hinj).
          - rewrite HeqT0. exact: HTn.
          - move=> n' Hcontra.
            have HUsome : U0 s = Some tt.
            { rewrite -HeqU00. apply: (proj2 (Hcorr s)). exists n'. exact: Hcontra. }
            rewrite HUsome in HU0s. discriminate.
        }
        move=> s' info' Hne.
        move: Hne. rewrite setmE.
        case Heq: ((s', info') == (s, info)).
        { move=> _.
          move/eqP: Heq => Heq. case: Heq => Heqs Heqinfo. subst s' info'.
          exists n. split.
          - rewrite setmE eq_refl. reflexivity.
          - rewrite setmE eq_refl. reflexivity.
        }
        { move=> HneTI2.
          rewrite -HeqTI0 in HneTI2.
          have [n0 [HDn0 HTn0]] := Hfresh s' info' HneTI2.
          exists n0. split.
          - rewrite setmE. case Heqn: (n0 == n).
            + move/eqP: Heqn => Heqn. subst n0. rewrite HeqD in HDn0. rewrite HDn in HDn0. discriminate.
            + rewrite -HeqD. exact: HDn0.
          - rewrite setmE. case Heqn2: (n0 == n).
            + move/eqP: Heqn2 => Heqn2. subst n0. rewrite HeqT0 in HTn0. rewrite HTn in HTn0. discriminate.
            + rewrite -HeqT0. exact: HTn0.
        }
    }
    rewrite -HK01 HK0n /=.
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(t0,t1) => t0 = set_heap (set_heap (set_heap s0 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s) /\ t1 = set_heap (set_heap (set_heap s1 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s)).
    2: { move=> t0 t1 [/= -> ->]. done. }
    eapply (r_uniform_bij _ _ _ _ id).
    1: exists id; done.
    move=> a1.
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(t0,t1) => t0 = set_heap (set_heap (set_heap s0 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s) /\ t1 = set_heap (set_heap (set_heap s1 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s)).
    2: { move=> t0 t1 [/= -> ->]. done. }
    eapply (r_put_lhs ideal_tbl_loc (setm TI (s, info) a1) _ _
      (fun '(t0,t1) => t0 = set_heap (set_heap (set_heap s0 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s) /\ t1 = set_heap (set_heap (set_heap s1 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s))).
    apply: rpre_hypothesis_rule => tQ tR HpQ.
    move: HpQ => [sQ'' [HeqQ ->]].
    case: HeqQ => [-> ->].
    eapply rpre_weaken_rule.
    1: instantiate (1 := fun '(t0,t1) => t0 = set_heap (set_heap (set_heap (set_heap s0 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s)) ideal_tbl_loc (setm TI (s, info) a1) /\ t1 = set_heap (set_heap (set_heap s1 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s)).
    2: { move=> t0 t1 [/= -> ->]. done. }
    eapply (r_put_vs_put k_tbl_loc (setm K0 n a1) k_tbl_loc (setm K0 n a1) _ _
      (fun '(t0,t1) => t0 = set_heap (set_heap (set_heap (set_heap s0 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s)) ideal_tbl_loc (setm TI (s, info) a1) /\ t1 = set_heap (set_heap (set_heap s1 kdone_loc (setm D n tt)) used_ss_loc (setm U0 s tt)) ss_tbl_loc (setm T n s))).
    apply: r_ret => tS tT h.
    move: h => [tT'' [[tS'' [[HeqS HeqTt] ->]] ->]].
    subst tS'' tT''.
    split; [ | done].
    apply: GKDF_bad_bad_inv_intro.
    - move=> l Hnotin.
      rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l k_tbl_loc Hnotin (ltac:(fmap_solve)))).
      rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l ideal_tbl_loc Hnotin (ltac:(fmap_solve)))).
      rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l ss_tbl_loc Hnotin (ltac:(fmap_solve)))).
      rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l used_ss_loc Hnotin (ltac:(fmap_solve)))).
      rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l kdone_loc Hnotin (ltac:(fmap_solve)))).
      rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l k_tbl_loc Hnotin (ltac:(fmap_solve)))).
      rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l ss_tbl_loc Hnotin (ltac:(fmap_solve)))).
      rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l used_ss_loc Hnotin (ltac:(fmap_solve)))).
      rewrite (get_set_heap_neq _ _ _ _ (GKDF_bad_bad_locs_neq l kdone_loc Hnotin (ltac:(fmap_solve)))).
      exact: (proj1 (proj1 Hpre) l Hnotin).
    - rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != k_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != ideal_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != ss_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != used_ss_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != kdone_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != k_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != ss_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != used_ss_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != kdone_loc.1)).
      exact: Hsync.
    - move=> _.
      rewrite (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != k_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != k_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != ideal_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != ss_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != ss_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != used_ss_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != used_ss_loc.1)).
      rewrite !get_set_heap_eq.
      split; [reflexivity | ].
      rewrite (get_set_heap_neq _ _ _ _ (isT : ss_tbl_loc.1 != k_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : ss_tbl_loc.1 != k_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : ss_tbl_loc.1 != ideal_tbl_loc.1)).
      rewrite !get_set_heap_eq.
      split; [reflexivity | ].
      rewrite (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != k_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != k_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != ideal_tbl_loc.1)).
      rewrite (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != ss_tbl_loc.1)).
      rewrite !get_set_heap_eq.
      rewrite (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != ss_tbl_loc.1)).
      rewrite get_set_heap_eq.
      split; [reflexivity | ].
      split; [reflexivity | ].
      split.
      { rewrite -HeqT0 -HeqU00.
        eapply (ss_used_correspondence_extend (get_heap s0 ss_tbl_loc) (get_heap s0 used_ss_loc) n s Hcorr).
        - rewrite HeqT0. exact: HTn.
        - rewrite HeqU00. exact: HU0s.
      }
      split.
      { rewrite -HeqT0.
        eapply (ss_tbl_injective_extend (get_heap s0 ss_tbl_loc) n s Hinj).
        - rewrite HeqT0. exact: HTn.
        - move=> n' Hcontra.
          have HUsome : U0 s = Some tt.
          { rewrite -HeqU00. apply: (proj2 (Hcorr s)). exists n'. exact: Hcontra. }
          rewrite HUsome in HU0s. discriminate.
      }
      rewrite (get_set_heap_neq _ _ _ _ (isT : ideal_tbl_loc.1 != k_tbl_loc.1)).
      rewrite get_set_heap_eq.
      move=> s' info' Hne.
      move: Hne. rewrite setmE.
      case Heq: ((s', info') == (s, info)).
      { move=> _.
        move/eqP: Heq => Heq. case: Heq => Heqs Heqinfo. subst s' info'.
        exists n. split.
        - rewrite setmE eq_refl. reflexivity.
        - rewrite setmE eq_refl. reflexivity.
      }
      { move=> HneTI2.
        rewrite -HeqTI0 in HneTI2.
        have [n0 [HDn0 HTn0]] := Hfresh s' info' HneTI2.
        exists n0. split.
        - rewrite setmE. case Heqn: (n0 == n).
          + move/eqP: Heqn => Heqn. subst n0. rewrite HeqD in HDn0. rewrite HDn in HDn0. discriminate.
          + rewrite -HeqD. exact: HDn0.
        - rewrite setmE. case Heqn2: (n0 == n).
          + move/eqP: Heqn2 => Heqn2. subst n0. rewrite HeqT0 in HTn0. rewrite HTn in HTn0. discriminate.
          + rewrite -HeqT0. exact: HTn0.
      }
  Qed.

  Lemma GKDF_bad_mid_ref_GKDF_bad_false_eq_up_to_bad :
    eq_up_to_bad (unionm I_kdf_env KDF_out) GKDF_bad_bad_inv 45 GKDF_bad_mid_ref GKDF_bad_false.
  Proof.
    move=> id S T x hasE.
    fmap_invert hasE.
    all: simplify_linking.
    1: exact: (GKDF_bad_GEN_SS_case x).
    1: exact: (GKDF_bad_GET_K_case x).
    destruct x as [n info].
    ssprove_code_simpl.
    simplify_linking.
    eapply code_link_rw_lhs.
    1: solve [ssprove_match_commut_gen].
    eapply code_link_rw_rhs.
    1: solve [ssprove_match_commut_gen].
    exact: (GKDF_bad_DERIVE_K_case n info).
  Qed.

  (** [eq_upto_bad_perf_ind] itself: Qed'd in full. Mirrors HKDF.v's
    [KDF_mid'_KDF_bad_bound] (~L1525) verbatim in structure. *)
  Lemma GKDF_bad_mid_ref_GKDF_bad_false_pr_bad_bound LA A
    (hcompD : fcompat KDF_loc KDFC_loc) (hcomp : fcompat KEYS_bad_loc KDFC_loc)
    (vA : ValidPackage LA (unionm I_kdf_env KDF_out) A_export A)
    (Hsep0 : fseparate LA (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc)))
    (Hsep1 : fseparate LA (unionm KDF_loc (unionm KEYS_bad_loc KDFC_loc)))
    (Hlva : lossless_valid_adv LA (unionm I_kdf_env KDF_out) (resolve A RUN tt)) :
    AdvantageE GKDF_bad_mid_ref GKDF_bad_false A <= Pr_bad (A ∘ GKDF_bad_mid_ref) 45 true.
  Proof.
    eapply eq_upto_bad_perf_ind.
    1: exact: GKDF_bad_mid_ref_valid.
    1: exact: (GKDF_bad_false_valid hcompD hcomp).
    1: exact vA.
    1: eapply (INV'_to_INV LA (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc))
      (unionm KDF_loc (unionm KEYS_bad_loc KDFC_loc)) GKDF_bad_bad_inv).
    1: exact: (inv_INV' (Invariant:=GKDF_bad_bad_Invariant)).
    1: exact Hsep0.
    1: exact Hsep1.
    1: exact: (inv_empty (Invariant:=GKDF_bad_bad_Invariant)).
    1: exact Hsep0.
    1: exact Hsep1.
    1: exact Hlva.
    1: eapply (notin_has_separate (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc)) LA bad_loc);
         [ fmap_solve | apply: fseparateC; exact Hsep0 ].
    1: move=> s0 s1 Hpre; exact: (proj2 (proj1 Hpre)).
    1: exact: GKDF_bad_mid_ref_GKDF_bad_false_eq_up_to_bad.
    1: exact: GKDF_bad_mid_ref_bad_preserved.
    1: exact: GKDF_bad_false_bad_preserved.
  Qed.

  (** * Step (d): [Pr_bad ... <= birthday_ss], the counting kernel.

    Mirrors HKDF.v's [Pr_bad_adv_bound] (~L6333-6651, ~320 lines, an
    induction on the resolved adversary's own code —
    [ret]/[opr]/[getr]/[putr]/[sampler] cases — bounding
    [Pr[bad_loc ends true]] by [Birthday.bad_bound] read off a per-run
    counter/used-set pair) composed with its [empty_heap] instantiation
    and the arithmetic finish ([bad_bound_le_birthday_ss] above). The
    instance here is SIMPLER than HKDF's own (no adversary-chosen
    ss -> prk indirection; shared secrets are drawn at most once per
    handle, directly bounded by [q] via the handle type ['fin q] and
    [domm_fin_bound] above, in place of HKDF's [count_loc]-threaded
    [COUNT q] wrapper) — NOW Qed'd in full below, in
    [Pr_bad_GKDF_bad_mid_ref_adv_bound]'s own proof. *)
  (** [fin_family SS_N]'s cardinality, matching [SS_N] -- local mirror of
    HKDF.v's [card_fin_family_PRK_N], needed to instantiate [Birthday.v]
    at [F := fin_family SS_N] against this file's own [uniform SS_N]
    sampler. *)
  Lemma card_fin_family_SS_N : #|fin_family SS_N| = SS_N.
  Proof. rewrite /fin_family /=. by rewrite card_ord. Qed.

  (** The one-line arithmetic step, local mirror of HKDF.v's
    [bad_bound_le_birthday_bound]: [bad_bound q 0 <= birthday_ss], since
    [q*(q-1) <= q*q]. *)
  Lemma bad_bound_le_birthday_ss :
    Birthday.bad_bound (fin_family SS_N) q 0 <= birthday_ss.
  Proof.
    rewrite /Birthday.bad_bound /birthday_ss card_fin_family_SS_N.
    rewrite muln0 add0n.
    apply: ler_wpM2r.
    - by rewrite invr_ge0 ler0n.
    - by rewrite ler_nat leq_mul2l leq_subr orbT.
  Qed.

  (** THE core adversary-code induction (mirroring HKDF.v's
    [Pr_bad_adv_bound], ~320 lines) -- bounding, by induction on an
    ARBITRARY [lossless_valid_adv] adversary's own resolved code, the
    probability that running it against [GKDF_bad_mid_ref] (starting
    from any heap already satisfying the ghost-state bookkeeping facts
    [ss_used_correspondence]/[ss_tbl_injective]/[derive_fresh]) ever ends
    with [bad_loc] set. The bound reads off [h]'s own
    [ss_tbl_loc]/[used_ss_loc] (playing [Birthday.bad_bound]'s
    remaining-budget/"used" arguments respectively). Remaining budget is
    [q - size (domm (get_heap h ss_tbl_loc))] rather than an explicit
    adversary-facing counter (unlike HKDF's [count_loc]): since sessions
    are handles of type ['fin q], [ss_tbl_loc]'s domain is bounded by
    [q] STRUCTURALLY ([domm_fin_bound] above), so no [COUNT] wrapper is
    needed -- a fresh [GEN_SS]/[GET_SS] draw can only occur at a session
    not yet in [ss_tbl_loc]'s domain, and there are at most
    [q - size (domm ...)] of those.

    NOW Qed'd in full: an induction over [Ac]'s
    [ret]/[opr]/[getr]/[putr]/[sampler] cases, with the [opr] case
    itself splitting on [GEN_SS]/[GET_K]/[DERIVE_K] (via
    [fmap_invert]/[simplify_linking], the same idiom
    [GKDF_bad_GEN_SS_case]/[GKDF_bad_GET_K_case]/[GKDF_bad_DERIVE_K_case]
    above use). [GEN_SS]'s fresh-[ss] sub-case runs the birthday-step
    argument ([expectation_le_bad_bound], Birthday.v) directly, the same
    way HKDF.v's own induction does for its fresh-[prk] sub-case.
    [GET_K] is a pure frame case (only touches [k_tbl_loc], disjoint
    from every tracked location). [DERIVE_K] is the substantive case:
    after flattening [resolve GKDF_bad_mid_ref (DERIVE_K,_) (n,info)]
    via [ssprove_match_commut_gen] (using a local unary "rewrite the
    [Pr_code] argument up to equality" helper, [Pr_code_eq_rw], mirroring
    [bad_lossless_rw]/[code_link_rw_lhs] above), its [kdone_loc] dispatch
    and [ss_tbl_loc] Some/None split are handled directly (the [None]
    branch running its OWN birthday step, structurally identical to
    [GEN_SS]'s but budgeted off [ss_tbl_loc] via the session handle [n]
    itself rather than an adversary-chosen value), and the shared
    "[ideal_tbl_loc] lookup + [k_tbl_loc] update" tail common to both
    branches is factored into a local lemma [Htail] (parameterised over
    the session's shared secret and the heap reached so far) to avoid
    duplicating it. The genuinely new ingredient relative to HKDF's own
    induction is carrying [derive_fresh] through every step: extending it
    at a session's OWN [(kdone_loc, ss_tbl_loc)] entry when
    [ideal_tbl_loc] gains a fresh entry keyed at that session's shared
    secret (via [derive_fresh_extend_T]/[derive_fresh_extend_D] above, or
    a direct case split against [Hcorr] when the shared secret comes from
    an EARLIER [GEN_SS]/[GET_SS] draw). Everything else needed for step
    (d) -- unfolding [Pr_bad] to a [Pr_code] statement at [empty_heap],
    and the concluding [Birthday.bad_bound q 0 <= birthday_ss] arithmetic
    ([bad_bound_le_birthday_ss] above) -- is [Qed]'d in
    [Pr_bad_GKDF_bad_mid_ref_bound] below. No admits remain. *)
  Lemma Pr_bad_GKDF_bad_mid_ref_adv_bound {LA : Locations} {B : choiceType}
    (Ac : raw_code B)
    (Hlva : lossless_valid_adv LA (unionm I_kdf_env KDF_out) Ac)
    (Hsep : fseparate LA (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc))) :
    forall h : heap,
      ss_used_correspondence (get_heap h ss_tbl_loc) (get_heap h used_ss_loc) →
      ss_tbl_injective (get_heap h ss_tbl_loc) →
      derive_fresh (get_heap h kdone_loc) (get_heap h ss_tbl_loc) (get_heap h ideal_tbl_loc) →
      (size (domm (get_heap h ss_tbl_loc)) <= q)%N →
      \P_[ Pr_code (code_link Ac GKDF_bad_mid_ref) h ]
        (fun '(_, h') => get_heap h' bad_loc)
      <= (if get_heap h bad_loc then 1
          else Birthday.bad_bound (fin_family SS_N)
                 (q - size (domm (get_heap h ss_tbl_loc)))
                 #|domm (get_heap h used_ss_loc)|).
  Proof.
    induction Hlva as [x0 | o x k Ho k' IH | l k Hl k' IH | l v k Hl IH | op k Hop k' IH];
      move=> h Hcorr Hinj Hfresh Hcount.
    - (* ret *)
      rewrite /= Pr_code_ret pr_dunit /=.
      case: (boolP (get_heap h bad_loc)) => Hb /=.
      + exact: lexx.
      + exact: bad_bound_ge0.
    - (* opr: split GEN_SS / GET_K / DERIVE_K *)
      fmap_invert Ho.
      all: simplify_linking.
      1: { (* GEN_SS *)
        rewrite Pr_code_get.
        case Hv: (get_heap h ss_tbl_loc x) => [ssv|] /=.
        - exact: (IH tt h Hcorr Hinj Hfresh Hcount).
        - case: (boolP (get_heap h bad_loc)) => Hbadh /=.
          + rewrite Pr_code_sample __deprecated__pr_dlet.
            apply: exp_le_bd.
            1: exact: ler01.
            1: move=> y; rewrite ger0_norm; [exact: ge0_pr | exact: le1_pr].
          + rewrite Pr_code_sample __deprecated__pr_dlet.
            have Hxnotin : x \notin domm (get_heap h ss_tbl_loc).
            { apply/dommPn. exact: Hv. }
            have Hbound : (size (domm (setm (mapm (fun _ : SS => tt) (get_heap h ss_tbl_loc)) x tt)) <= q)%N
              := domm_fin_bound q _ _.
            rewrite domm_set domm_map sizesU1 Hxnotin /= in Hbound.
            have Hgt0 : (0 < q - size (domm (get_heap h ss_tbl_loc)))%N.
            { by rewrite subn_gt0. }
            have HcntQ : (q - size (domm (get_heap h ss_tbl_loc)) = (q - size (domm (get_heap h ss_tbl_loc))).-1.+1)%N.
            { by rewrite (prednK Hgt0). }
            rewrite HcntQ.
            have Hcard : (0 < #|fin_family SS_N|)%N.
            { rewrite card_fin_family_SS_N. exact: SS_N_gt0. }
            have Htest : (uniform SS_N).π2 = Birthday.unif_F (fin_family SS_N) := erefl.
            rewrite Htest.
            have Hcardeq : #|[set x0 : fin_family SS_N | x0 \in domm (get_heap h used_ss_loc)]|
                         = #|domm (get_heap h used_ss_loc)|.
            { by rewrite cardsE. }
            rewrite -Hcardeq.
            apply: (expectation_le_bad_bound (fin_family SS_N) Hcard
              (q - size (domm (get_heap h ss_tbl_loc))).-1
              [set x0 : fin_family SS_N | x0 \in domm (get_heap h used_ss_loc)]).
            1: move=> z; exact: ge0_pr.
            move=> z.
            rewrite Pr_code_get.
            rewrite in_set.
            case: (boolP (z \in domm (get_heap h used_ss_loc))) => Hzused.
            1: {
              have [[] Hget] := dommP Hzused.
              rewrite Hget /=.
              apply: (le_trans (y := 1)); [exact: le1_pr | rewrite lerDl; exact: bad_bound_ge0].
            }
            have Hget2 : get_heap h used_ss_loc z = None. { apply/dommPn. exact: Hzused. }
            rewrite Hget2 /=.
            rewrite Pr_code_put Pr_code_put.
            set h1 := set_heap h used_ss_loc (setm (get_heap h used_ss_loc) z tt).
            set h2 := set_heap h1 ss_tbl_loc (setm (get_heap h ss_tbl_loc) x z).
            have HeqSS : get_heap h2 ss_tbl_loc = setm (get_heap h ss_tbl_loc) x z.
            { rewrite /h2 get_set_heap_eq. reflexivity. }
            have HeqUS : get_heap h2 used_ss_loc = setm (get_heap h used_ss_loc) z tt.
            { rewrite /h2 (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != ss_tbl_loc.1)) /h1 get_set_heap_eq. reflexivity. }
            have HeqKD : get_heap h2 kdone_loc = get_heap h kdone_loc.
            { rewrite /h2 (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != ss_tbl_loc.1)) /h1 (get_set_heap_neq _ _ _ _ (isT : kdone_loc.1 != used_ss_loc.1)). reflexivity. }
            have HeqID : get_heap h2 ideal_tbl_loc = get_heap h ideal_tbl_loc.
            { rewrite /h2 (get_set_heap_neq _ _ _ _ (isT : ideal_tbl_loc.1 != ss_tbl_loc.1)) /h1 (get_set_heap_neq _ _ _ _ (isT : ideal_tbl_loc.1 != used_ss_loc.1)). reflexivity. }
            have HeqBad : get_heap h2 bad_loc = false.
            { rewrite /h2 (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != ss_tbl_loc.1)) /h1 (get_set_heap_neq _ _ _ _ (isT : bad_loc.1 != used_ss_loc.1)). exact: (negbTE Hbadh). }
            have Hcorr2 : ss_used_correspondence (get_heap h2 ss_tbl_loc) (get_heap h2 used_ss_loc).
            { rewrite HeqSS HeqUS. exact: (ss_used_correspondence_extend (get_heap h ss_tbl_loc) (get_heap h used_ss_loc) x z Hcorr Hv Hget2). }
            have Hinj2 : ss_tbl_injective (get_heap h2 ss_tbl_loc).
            { rewrite HeqSS. apply: (ss_tbl_injective_extend (get_heap h ss_tbl_loc) x z Hinj Hv).
              move=> n' Hcontra.
              have HUsome : get_heap h used_ss_loc z = Some tt. { apply: (proj2 (Hcorr z)). exists n'. exact: Hcontra. }
              rewrite HUsome in Hget2. discriminate. }
            have Hfresh2 : derive_fresh (get_heap h2 kdone_loc) (get_heap h2 ss_tbl_loc) (get_heap h2 ideal_tbl_loc).
            { rewrite HeqKD HeqSS HeqID. exact: (derive_fresh_extend_T (get_heap h kdone_loc) (get_heap h ss_tbl_loc) (get_heap h ideal_tbl_loc) x z Hfresh Hv). }
            have Hdommcard : #|domm (setm (get_heap h used_ss_loc) z tt)| = (#|domm (get_heap h used_ss_loc)|).+1.
            { have Heq1' : [set y0 : fin_family SS_N | y0 \in z |: domm (get_heap h used_ss_loc)]
                         = (z |: [set y0 : fin_family SS_N | y0 \in domm (get_heap h used_ss_loc)])%SET.
              { apply/setP => y0. rewrite in_set in_fsetU1 in_setU1 in_set. reflexivity. }
              rewrite domm_set -cardsE Heq1' cardsU1 in_set (negbTE Hzused) add1n cardsE. reflexivity. }
            have Hcount2 : (size (domm (get_heap h2 ss_tbl_loc)) <= q)%N.
            { rewrite HeqSS domm_set sizesU1 Hxnotin /=. exact: Hbound. }
            apply: (le_trans (IH tt h2 Hcorr2 Hinj2 Hfresh2 Hcount2)).
            rewrite HeqBad /=.
            rewrite HeqSS domm_set sizesU1 Hxnotin /= add1n subnS.
            rewrite HeqUS Hdommcard Hcardeq.
            rewrite GRing.add0r. exact: lexx.
      }
      1: { (* GET_K: a frame case -- only touches k_tbl_loc, disjoint from
             every tracked location, so the invariants and the budget
             transfer unchanged to the continuation. *)
        rewrite Pr_code_get.
        case Hv: (get_heap h k_tbl_loc x) => [k0|] /=.
        - exact: (IH k0 h Hcorr Hinj Hfresh Hcount).
        - rewrite Pr_code_sample __deprecated__pr_dlet.
          apply: exp_le_bd.
          1: case: (boolP (get_heap h bad_loc)) => Hb /=; [exact: ler01 | exact: bad_bound_ge0].
          move=> y.
          rewrite Pr_code_put.
          have Hne_ssk : ss_tbl_loc.1 != k_tbl_loc.1 := isT.
          have Hne_usk : used_ss_loc.1 != k_tbl_loc.1 := isT.
          have Hne_bk : bad_loc.1 != k_tbl_loc.1 := isT.
          have Hne_kdk : kdone_loc.1 != k_tbl_loc.1 := isT.
          have Hne_idk : ideal_tbl_loc.1 != k_tbl_loc.1 := isT.
          have Hcorr' : ss_used_correspondence (get_heap (set_heap h k_tbl_loc (setm (get_heap h k_tbl_loc) x y)) ss_tbl_loc) (get_heap (set_heap h k_tbl_loc (setm (get_heap h k_tbl_loc) x y)) used_ss_loc).
          { rewrite (get_set_heap_neq _ _ _ _ Hne_ssk) (get_set_heap_neq _ _ _ _ Hne_usk). exact: Hcorr. }
          have Hinj' : ss_tbl_injective (get_heap (set_heap h k_tbl_loc (setm (get_heap h k_tbl_loc) x y)) ss_tbl_loc).
          { rewrite (get_set_heap_neq _ _ _ _ Hne_ssk). exact: Hinj. }
          have Hfresh' : derive_fresh (get_heap (set_heap h k_tbl_loc (setm (get_heap h k_tbl_loc) x y)) kdone_loc) (get_heap (set_heap h k_tbl_loc (setm (get_heap h k_tbl_loc) x y)) ss_tbl_loc) (get_heap (set_heap h k_tbl_loc (setm (get_heap h k_tbl_loc) x y)) ideal_tbl_loc).
          { rewrite (get_set_heap_neq _ _ _ _ Hne_kdk) (get_set_heap_neq _ _ _ _ Hne_ssk) (get_set_heap_neq _ _ _ _ Hne_idk). exact: Hfresh. }
          have Hcount' : (size (domm (get_heap (set_heap h k_tbl_loc (setm (get_heap h k_tbl_loc) x y)) ss_tbl_loc)) <= q)%N.
          { rewrite (get_set_heap_neq _ _ _ _ Hne_ssk). exact: Hcount. }
          rewrite ger0_norm; first exact: ge0_pr.
          rewrite -(get_set_heap_neq h k_tbl_loc (setm (get_heap h k_tbl_loc) x y) bad_loc Hne_bk).
          rewrite -(get_set_heap_neq h k_tbl_loc (setm (get_heap h k_tbl_loc) x y) ss_tbl_loc Hne_ssk).
          rewrite -(get_set_heap_neq h k_tbl_loc (setm (get_heap h k_tbl_loc) x y) used_ss_loc Hne_usk).
          exact: (IH y (set_heap h k_tbl_loc (setm (get_heap h k_tbl_loc) x y)) Hcorr' Hinj' Hfresh' Hcount').
      }
      1: { (* DERIVE_K: the substantive case -- kdone_loc dispatch, then
             ss_tbl_loc's Some/None split (the latter a birthday step
             identical in shape to GEN_SS's), then a shared "TI+k_tbl_loc"
             tail (factored into [Htail] below, reused from both the
             already-done-ss and the freshly-drawn-ss sub-cases). *)
        destruct x as [n info].
        have Pr_code_eq_rw : forall (A : choiceType) (post : pred (A * heap)) (bound : R)
            (c c' : raw_code A) (hh : heap),
            c' = c -> \P_[ Pr_code c' hh ] post <= bound -> \P_[ Pr_code c hh ] post <= bound.
        { move=> A post bound c c' hh -> //. }
        eapply Pr_code_eq_rw.
        1: solve [ssprove_match_commut_gen].
        eapply Pr_code_eq_rw.
        1: solve [ssprove_match_commut_gen].
        have Htail : forall (s0 : SS) (h0 : heap),
          ss_used_correspondence (get_heap h0 ss_tbl_loc) (get_heap h0 used_ss_loc) ->
          ss_tbl_injective (get_heap h0 ss_tbl_loc) ->
          derive_fresh (get_heap h0 kdone_loc) (get_heap h0 ss_tbl_loc) (get_heap h0 ideal_tbl_loc) ->
          (size (domm (get_heap h0 ss_tbl_loc)) <= q)%N ->
          get_heap h0 kdone_loc n = Some tt ->
          get_heap h0 ss_tbl_loc n = Some s0 ->
          \P_[ Pr_code
                (b ← (TI ← get ideal_tbl_loc ;;
                      match TI (s0, info) with
                      | Some kv => K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n kv ;; ret tt end
                      | None => kk ← sample uniform Key_N ;; #put ideal_tbl_loc := setm TI (s0,info) kk ;; K ← get k_tbl_loc ;; match K n with Some _ => ret tt | None => #put k_tbl_loc := setm K n kk ;; ret tt end
                      end) ;;
                 code_link (k b) GKDF_bad_mid_ref)
              h0 ]
              (fun '(_,h') => get_heap h' bad_loc)
          <= (if get_heap h0 bad_loc then 1 else bad_bound (fin_family SS_N) (q - size(domm(get_heap h0 ss_tbl_loc))) #|domm (get_heap h0 used_ss_loc)|).
        {
          move=> s0 h0 Hcorr0 Hinj0 Hfresh0 Hcount0 HDn0 HTn0.
          rewrite Pr_code_get.
          case HTI: (get_heap h0 ideal_tbl_loc (s0, info)) => [kv|] /=.
          - rewrite Pr_code_get.
            case HK: (get_heap h0 k_tbl_loc n) => [kk0|] /=.
            + exact: (IH tt h0 Hcorr0 Hinj0 Hfresh0 Hcount0).
            + rewrite Pr_code_put.
              have Hcorr1 : ss_used_correspondence (get_heap (set_heap h0 k_tbl_loc (setm (get_heap h0 k_tbl_loc) n kv)) ss_tbl_loc) (get_heap (set_heap h0 k_tbl_loc (setm (get_heap h0 k_tbl_loc) n kv)) used_ss_loc).
              { rewrite (get_set_heap_neq _ _ _ _ (isT: ss_tbl_loc.1 != k_tbl_loc.1)) (get_set_heap_neq _ _ _ _ (isT: used_ss_loc.1 != k_tbl_loc.1)). exact: Hcorr0. }
              have Hinj1 : ss_tbl_injective (get_heap (set_heap h0 k_tbl_loc (setm (get_heap h0 k_tbl_loc) n kv)) ss_tbl_loc).
              { rewrite (get_set_heap_neq _ _ _ _ (isT: ss_tbl_loc.1 != k_tbl_loc.1)). exact: Hinj0. }
              have Hfresh1 : derive_fresh (get_heap (set_heap h0 k_tbl_loc (setm (get_heap h0 k_tbl_loc) n kv)) kdone_loc) (get_heap (set_heap h0 k_tbl_loc (setm (get_heap h0 k_tbl_loc) n kv)) ss_tbl_loc) (get_heap (set_heap h0 k_tbl_loc (setm (get_heap h0 k_tbl_loc) n kv)) ideal_tbl_loc).
              { rewrite (get_set_heap_neq _ _ _ _ (isT: kdone_loc.1 != k_tbl_loc.1)) (get_set_heap_neq _ _ _ _ (isT: ss_tbl_loc.1 != k_tbl_loc.1)) (get_set_heap_neq _ _ _ _ (isT: ideal_tbl_loc.1 != k_tbl_loc.1)). exact: Hfresh0. }
              have Hcount1 : (size (domm (get_heap (set_heap h0 k_tbl_loc (setm (get_heap h0 k_tbl_loc) n kv)) ss_tbl_loc)) <= q)%N.
              { rewrite (get_set_heap_neq _ _ _ _ (isT: ss_tbl_loc.1 != k_tbl_loc.1)). exact: Hcount0. }
              apply: (le_trans (IH tt (set_heap h0 k_tbl_loc (setm (get_heap h0 k_tbl_loc) n kv)) Hcorr1 Hinj1 Hfresh1 Hcount1)).
              rewrite (get_set_heap_neq _ _ _ _ (isT: bad_loc.1 != k_tbl_loc.1)) (get_set_heap_neq _ _ _ _ (isT: ss_tbl_loc.1 != k_tbl_loc.1)) (get_set_heap_neq _ _ _ _ (isT: used_ss_loc.1 != k_tbl_loc.1)).
              exact: lexx.
          - rewrite Pr_code_sample __deprecated__pr_dlet.
            apply: exp_le_bd.
            1: case: (boolP (get_heap h0 bad_loc)) => Hb0 /=; [exact: ler01 | exact: bad_bound_ge0].
            move=> kk1.
            rewrite Pr_code_put.
            rewrite Pr_code_get.
            rewrite ger0_norm; first exact: ge0_pr.
            set h1 := set_heap h0 ideal_tbl_loc (setm (get_heap h0 ideal_tbl_loc) (s0, info) kk1).
            have HeqK1 : get_heap h1 k_tbl_loc = get_heap h0 k_tbl_loc.
            { rewrite /h1 (get_set_heap_neq _ _ _ _ (isT: k_tbl_loc.1 != ideal_tbl_loc.1)). reflexivity. }
            rewrite HeqK1.
            have HeqSS1 : get_heap h1 ss_tbl_loc = get_heap h0 ss_tbl_loc.
            { rewrite /h1 (get_set_heap_neq _ _ _ _ (isT: ss_tbl_loc.1 != ideal_tbl_loc.1)). reflexivity. }
            have HeqUS1 : get_heap h1 used_ss_loc = get_heap h0 used_ss_loc.
            { rewrite /h1 (get_set_heap_neq _ _ _ _ (isT: used_ss_loc.1 != ideal_tbl_loc.1)). reflexivity. }
            have HeqKD1 : get_heap h1 kdone_loc = get_heap h0 kdone_loc.
            { rewrite /h1 (get_set_heap_neq _ _ _ _ (isT: kdone_loc.1 != ideal_tbl_loc.1)). reflexivity. }
            have HeqBad1 : get_heap h1 bad_loc = get_heap h0 bad_loc.
            { rewrite /h1 (get_set_heap_neq _ _ _ _ (isT: bad_loc.1 != ideal_tbl_loc.1)). reflexivity. }
            have HeqID1 : get_heap h1 ideal_tbl_loc = setm (get_heap h0 ideal_tbl_loc) (s0, info) kk1.
            { rewrite /h1 get_set_heap_eq. reflexivity. }
            have Hfresh1 : derive_fresh (get_heap h1 kdone_loc) (get_heap h1 ss_tbl_loc) (get_heap h1 ideal_tbl_loc).
            { rewrite HeqKD1 HeqSS1 HeqID1.
              move=> s' info' Hne.
              move: Hne. rewrite setmE.
              case: (eqVneq (s', info') (s0, info)) => Heqp.
              - move=> _. move: Heqp => [Heqs Heqi]. subst s' info'. exists n. split; [exact: HDn0 | exact: HTn0].
              - move=> Hne0. exact: (Hfresh0 s' info' Hne0). }
            have Hcorr1 : ss_used_correspondence (get_heap h1 ss_tbl_loc) (get_heap h1 used_ss_loc).
            { rewrite HeqSS1 HeqUS1. exact: Hcorr0. }
            have Hinj1 : ss_tbl_injective (get_heap h1 ss_tbl_loc).
            { rewrite HeqSS1. exact: Hinj0. }
            have Hcount1 : (size (domm (get_heap h1 ss_tbl_loc)) <= q)%N.
            { rewrite HeqSS1. exact: Hcount0. }
            have HDn1 : get_heap h1 kdone_loc n = Some tt. { rewrite HeqKD1. exact: HDn0. }
            have HTn1 : get_heap h1 ss_tbl_loc n = Some s0. { rewrite HeqSS1. exact: HTn0. }
            case HK: (get_heap h0 k_tbl_loc n) => [kk0|] /=.
            + apply: (le_trans (IH tt h1 Hcorr1 Hinj1 Hfresh1 Hcount1)).
              rewrite HeqBad1 HeqSS1 HeqUS1.
              exact: lexx.
            + rewrite Pr_code_put.
              have Hcorr2 : ss_used_correspondence (get_heap (set_heap h1 k_tbl_loc (setm (get_heap h0 k_tbl_loc) n kk1)) ss_tbl_loc) (get_heap (set_heap h1 k_tbl_loc (setm (get_heap h0 k_tbl_loc) n kk1)) used_ss_loc).
              { rewrite (get_set_heap_neq _ _ _ _ (isT: ss_tbl_loc.1 != k_tbl_loc.1)) (get_set_heap_neq _ _ _ _ (isT: used_ss_loc.1 != k_tbl_loc.1)). exact: Hcorr1. }
              have Hinj2 : ss_tbl_injective (get_heap (set_heap h1 k_tbl_loc (setm (get_heap h0 k_tbl_loc) n kk1)) ss_tbl_loc).
              { rewrite (get_set_heap_neq _ _ _ _ (isT: ss_tbl_loc.1 != k_tbl_loc.1)). exact: Hinj1. }
              have Hfresh2 : derive_fresh (get_heap (set_heap h1 k_tbl_loc (setm (get_heap h0 k_tbl_loc) n kk1)) kdone_loc) (get_heap (set_heap h1 k_tbl_loc (setm (get_heap h0 k_tbl_loc) n kk1)) ss_tbl_loc) (get_heap (set_heap h1 k_tbl_loc (setm (get_heap h0 k_tbl_loc) n kk1)) ideal_tbl_loc).
              { rewrite (get_set_heap_neq _ _ _ _ (isT: kdone_loc.1 != k_tbl_loc.1)) (get_set_heap_neq _ _ _ _ (isT: ss_tbl_loc.1 != k_tbl_loc.1)) (get_set_heap_neq _ _ _ _ (isT: ideal_tbl_loc.1 != k_tbl_loc.1)). exact: Hfresh1. }
              have Hcount2 : (size (domm (get_heap (set_heap h1 k_tbl_loc (setm (get_heap h0 k_tbl_loc) n kk1)) ss_tbl_loc)) <= q)%N.
              { rewrite (get_set_heap_neq _ _ _ _ (isT: ss_tbl_loc.1 != k_tbl_loc.1)). exact: Hcount1. }
              apply: (le_trans (IH tt (set_heap h1 k_tbl_loc (setm (get_heap h0 k_tbl_loc) n kk1)) Hcorr2 Hinj2 Hfresh2 Hcount2)).
              rewrite (get_set_heap_neq _ _ _ _ (isT: bad_loc.1 != k_tbl_loc.1)) (get_set_heap_neq _ _ _ _ (isT: ss_tbl_loc.1 != k_tbl_loc.1)) (get_set_heap_neq _ _ _ _ (isT: used_ss_loc.1 != k_tbl_loc.1)).
              rewrite HeqBad1 HeqSS1 HeqUS1.
              exact: lexx.
        }
        rewrite Pr_code_get.
        case Hd: (get_heap h kdone_loc n) => [du|] /=.
        1: exact: (IH tt h Hcorr Hinj Hfresh Hcount).
        rewrite Pr_code_put.
        have HeqSS0 : get_heap (set_heap h kdone_loc (setm (get_heap h kdone_loc) n tt)) ss_tbl_loc = get_heap h ss_tbl_loc.
        { exact: (get_set_heap_neq _ _ _ _ (isT : ss_tbl_loc.1 != kdone_loc.1)). }
        rewrite Pr_code_get HeqSS0.
        case HT: (get_heap h ss_tbl_loc n) => [s|] /=.
        1: {
          apply: (le_trans (Htail s (set_heap h kdone_loc (setm (get_heap h kdone_loc) n tt)) _ _ _ _ _ _)).
          - rewrite HeqSS0 (get_set_heap_neq _ _ _ _ (isT: used_ss_loc.1 != kdone_loc.1)). exact: Hcorr.
          - rewrite HeqSS0. exact: Hinj.
          - rewrite get_set_heap_eq HeqSS0 (get_set_heap_neq _ _ _ _ (isT: ideal_tbl_loc.1 != kdone_loc.1)).
            exact: (derive_fresh_extend_D (get_heap h kdone_loc) (get_heap h ss_tbl_loc) (get_heap h ideal_tbl_loc) n Hfresh).
          - rewrite HeqSS0. exact: Hcount.
          - by rewrite get_set_heap_eq setmE eqxx.
          - rewrite HeqSS0. exact: HT.
          - rewrite (get_set_heap_neq _ _ _ _ (isT: bad_loc.1 != kdone_loc.1)) HeqSS0 (get_set_heap_neq _ _ _ _ (isT: used_ss_loc.1 != kdone_loc.1)).
            exact: lexx.
        }
        case: (boolP (get_heap h bad_loc)) => Hbadh /=.
        1: {
          rewrite Pr_code_sample __deprecated__pr_dlet.
          apply: exp_le_bd.
          1: exact: ler01.
          1: move=> y; rewrite ger0_norm; [exact: ge0_pr | exact: le1_pr].
        }
        rewrite Pr_code_sample __deprecated__pr_dlet.
        have Hxnotin : n \notin domm (get_heap h ss_tbl_loc).
        { apply/dommPn. exact: HT. }
        have Hbound : (size (domm (setm (mapm (fun _ : SS => tt) (get_heap h ss_tbl_loc)) n tt)) <= q)%N
          := domm_fin_bound q _ _.
        rewrite domm_set domm_map sizesU1 Hxnotin /= in Hbound.
        have Hgt0 : (0 < q - size (domm (get_heap h ss_tbl_loc)))%N.
        { by rewrite subn_gt0. }
        have HcntQ : (q - size (domm (get_heap h ss_tbl_loc)) = (q - size (domm (get_heap h ss_tbl_loc))).-1.+1)%N.
        { by rewrite (prednK Hgt0). }
        rewrite HcntQ.
        have Hcard : (0 < #|fin_family SS_N|)%N.
        { rewrite card_fin_family_SS_N. exact: SS_N_gt0. }
        have Htest : (uniform SS_N).π2 = Birthday.unif_F (fin_family SS_N) := erefl.
        rewrite Htest.
        have Hcardeq : #|[set x0 : fin_family SS_N | x0 \in domm (get_heap h used_ss_loc)]|
                     = #|domm (get_heap h used_ss_loc)|.
        { by rewrite cardsE. }
        rewrite -Hcardeq.
        apply: (expectation_le_bad_bound (fin_family SS_N) Hcard
          (q - size (domm (get_heap h ss_tbl_loc))).-1
          [set x0 : fin_family SS_N | x0 \in domm (get_heap h used_ss_loc)]).
        1: move=> z; exact: ge0_pr.
        move=> z.
        rewrite Pr_code_get.
        rewrite in_set.
        have HeqUS0 : get_heap (set_heap h kdone_loc (setm (get_heap h kdone_loc) n tt)) used_ss_loc = get_heap h used_ss_loc.
        { exact: (get_set_heap_neq _ _ _ _ (isT : used_ss_loc.1 != kdone_loc.1)). }
        rewrite HeqUS0.
        case: (boolP (z \in domm (get_heap h used_ss_loc))) => Hzused.
        1: {
          have [[] Hget] := dommP Hzused.
          rewrite Hget /=.
          apply: (le_trans (y := 1)); [exact: le1_pr | rewrite lerDl; exact: bad_bound_ge0].
        }
        have Hune : get_heap h used_ss_loc z = None. { apply/dommPn. exact: Hzused. }
        rewrite Hune /=.
        rewrite Pr_code_put Pr_code_put.
        set hstart := set_heap h kdone_loc (setm (get_heap h kdone_loc) n tt).
        set h1 := set_heap hstart used_ss_loc (setm (get_heap h used_ss_loc) z tt).
        set h2 := set_heap h1 ss_tbl_loc (setm (get_heap h ss_tbl_loc) n z).
        have HeqSS2 : get_heap h2 ss_tbl_loc = setm (get_heap h ss_tbl_loc) n z.
        { rewrite /h2 get_set_heap_eq. reflexivity. }
        have HeqUS2 : get_heap h2 used_ss_loc = setm (get_heap h used_ss_loc) z tt.
        { rewrite /h2 (get_set_heap_neq _ _ _ _ (isT: used_ss_loc.1 != ss_tbl_loc.1)) /h1 get_set_heap_eq. reflexivity. }
        have HeqKD2 : get_heap h2 kdone_loc = setm (get_heap h kdone_loc) n tt.
        { rewrite /h2 (get_set_heap_neq _ _ _ _ (isT: kdone_loc.1 != ss_tbl_loc.1)) /h1 (get_set_heap_neq _ _ _ _ (isT: kdone_loc.1 != used_ss_loc.1)) /hstart get_set_heap_eq. reflexivity. }
        have HeqID2 : get_heap h2 ideal_tbl_loc = get_heap h ideal_tbl_loc.
        { rewrite /h2 (get_set_heap_neq _ _ _ _ (isT: ideal_tbl_loc.1 != ss_tbl_loc.1)) /h1 (get_set_heap_neq _ _ _ _ (isT: ideal_tbl_loc.1 != used_ss_loc.1)) /hstart (get_set_heap_neq _ _ _ _ (isT: ideal_tbl_loc.1 != kdone_loc.1)). reflexivity. }
        have HeqBad2 : get_heap h2 bad_loc = false.
        { rewrite /h2 (get_set_heap_neq _ _ _ _ (isT: bad_loc.1 != ss_tbl_loc.1)) /h1 (get_set_heap_neq _ _ _ _ (isT: bad_loc.1 != used_ss_loc.1)) /hstart (get_set_heap_neq _ _ _ _ (isT: bad_loc.1 != kdone_loc.1)). exact: (negbTE Hbadh). }
        have HDn2 : get_heap h2 kdone_loc n = Some tt. { rewrite HeqKD2 setmE eqxx. reflexivity. }
        have HTn2 : get_heap h2 ss_tbl_loc n = Some z. { rewrite HeqSS2 setmE eqxx. reflexivity. }
        have Hfreshz : forall n', get_heap h ss_tbl_loc n' <> Some z.
        { move=> n' Heq.
          have Hex : exists n0, get_heap h ss_tbl_loc n0 = Some z := ex_intro _ n' Heq.
          have := (proj2 (Hcorr z) Hex).
          rewrite Hune. discriminate. }
        have Hcorr2 : ss_used_correspondence (get_heap h2 ss_tbl_loc) (get_heap h2 used_ss_loc).
        { rewrite HeqSS2 HeqUS2. exact: (ss_used_correspondence_extend (get_heap h ss_tbl_loc) (get_heap h used_ss_loc) n z Hcorr HT Hune). }
        have Hinj2 : ss_tbl_injective (get_heap h2 ss_tbl_loc).
        { rewrite HeqSS2. exact: (ss_tbl_injective_extend (get_heap h ss_tbl_loc) n z Hinj HT Hfreshz). }
        have Hfresh2 : derive_fresh (get_heap h2 kdone_loc) (get_heap h2 ss_tbl_loc) (get_heap h2 ideal_tbl_loc).
        { rewrite HeqKD2 HeqSS2 HeqID2.
          exact: (derive_fresh_extend_T (setm (get_heap h kdone_loc) n tt) (get_heap h ss_tbl_loc) (get_heap h ideal_tbl_loc) n z (derive_fresh_extend_D (get_heap h kdone_loc) (get_heap h ss_tbl_loc) (get_heap h ideal_tbl_loc) n Hfresh) HT). }
        have Hcount2 : (size (domm (get_heap h2 ss_tbl_loc)) <= q)%N.
        { rewrite HeqSS2 domm_set sizesU1 Hxnotin /=. exact: Hbound. }
        apply: (le_trans (Htail z h2 Hcorr2 Hinj2 Hfresh2 Hcount2 HDn2 HTn2)).
        rewrite HeqBad2 /=.
        rewrite HeqSS2 domm_set sizesU1 Hxnotin /= add1n subnS.
        have Hdommcard2 : #|domm (setm (get_heap h used_ss_loc) z tt)| = (#|domm (get_heap h used_ss_loc)|).+1.
        { have Heq1' : [set y0 : fin_family SS_N | y0 \in z |: domm (get_heap h used_ss_loc)]
                     = (z |: [set y0 : fin_family SS_N | y0 \in domm (get_heap h used_ss_loc)])%SET.
          { apply/setP => y0. rewrite in_set in_fsetU1 in_setU1 in_set. reflexivity. }
          rewrite domm_set -cardsE Heq1' cardsU1 in_set (negbTE Hzused) add1n cardsE. reflexivity. }
        rewrite HeqUS2 Hdommcard2 Hcardeq.
        rewrite GRing.add0r.
        exact: lexx.
      }
    - (* getr: adversary's own state, read-only, heap unchanged *)
      rewrite /= Pr_code_get.
      exact: (IH (get_heap h l) h Hcorr Hinj Hfresh Hcount).
    - (* putr: adversary's own state, disjoint from everything we track *)
      rewrite /= Pr_code_put.
      have Hloc_neq : forall xloc : Location,
        fhas (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc)) xloc -> xloc.1 != l.1.
      { move=> xloc Hxloc. apply/eqP => Heq.
        have Hindomm := fhas_in LA l Hl.
        have Hnotin := notin_has_separate (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc)) LA xloc Hxloc (fseparateC _ _ Hsep).
        move: Hnotin => /negP; apply.
        rewrite Heq. exact: Hindomm. }
      have Hne_ss : ss_tbl_loc.1 != l.1 := Hloc_neq ss_tbl_loc ltac:(fmap_solve).
      have Hne_us : used_ss_loc.1 != l.1 := Hloc_neq used_ss_loc ltac:(fmap_solve).
      have Hne_bad : bad_loc.1 != l.1 := Hloc_neq bad_loc ltac:(fmap_solve).
      have Hne_kd : kdone_loc.1 != l.1 := Hloc_neq kdone_loc ltac:(fmap_solve).
      have Hne_id : ideal_tbl_loc.1 != l.1 := Hloc_neq ideal_tbl_loc ltac:(fmap_solve).
      have Hcorr' : ss_used_correspondence (get_heap (set_heap h l v) ss_tbl_loc) (get_heap (set_heap h l v) used_ss_loc).
      { rewrite (get_set_heap_neq h l v ss_tbl_loc Hne_ss) (get_set_heap_neq h l v used_ss_loc Hne_us). exact: Hcorr. }
      have Hinj' : ss_tbl_injective (get_heap (set_heap h l v) ss_tbl_loc).
      { rewrite (get_set_heap_neq h l v ss_tbl_loc Hne_ss). exact: Hinj. }
      have Hfresh' : derive_fresh (get_heap (set_heap h l v) kdone_loc) (get_heap (set_heap h l v) ss_tbl_loc) (get_heap (set_heap h l v) ideal_tbl_loc).
      { rewrite (get_set_heap_neq h l v kdone_loc Hne_kd) (get_set_heap_neq h l v ss_tbl_loc Hne_ss) (get_set_heap_neq h l v ideal_tbl_loc Hne_id). exact: Hfresh. }
      have Hcount' : (size (domm (get_heap (set_heap h l v) ss_tbl_loc)) <= q)%N.
      { rewrite (get_set_heap_neq h l v ss_tbl_loc Hne_ss). exact: Hcount. }
      rewrite -(get_set_heap_neq h l v bad_loc Hne_bad).
      rewrite -(get_set_heap_neq h l v ss_tbl_loc Hne_ss).
      rewrite -(get_set_heap_neq h l v used_ss_loc Hne_us).
      exact: (IHIH (set_heap h l v) Hcorr' Hinj' Hfresh' Hcount').
    - (* sampler: adversary's own randomness, heap unchanged, same bound
        for every outcome *)
      rewrite /= Pr_code_sample __deprecated__pr_dlet.
      apply: exp_le_bd.
      + case: (boolP (get_heap h bad_loc)) => Hb /=.
        * exact: ler01.
        * exact: bad_bound_ge0.
      + move=> y.
        have Hge0 : 0 <= \P_[Pr_code (code_link (k y) GKDF_bad_mid_ref) h] (fun '(_, h') => get_heap h' bad_loc) := ge0_pr _ _.
        rewrite (ger0_norm Hge0).
        exact: (IH y h Hcorr Hinj Hfresh Hcount).
  Qed.

  (** Step (d): [Pr_bad ... <= birthday_ss], now [Qed]'d in terms of the
    (also fully [Qed]'d) adversary-code induction above
    ([Pr_bad_GKDF_bad_mid_ref_adv_bound]): unfold [Pr_bad] down to a
    [Pr_code] statement at [empty_heap]
    (mirroring HKDF.v's [Pr_bad_COUNT_KDF_mid'_bound]), discharge the
    ghost-state facts trivially at [empty_heap], apply the induction,
    and close with the arithmetic finish
    [bad_bound_le_birthday_ss]. *)
  Lemma Pr_bad_GKDF_bad_mid_ref_bound :
    ∀ LA (A : raw_package),
      ValidPackage LA (unionm I_kdf_env KDF_out) A_export A →
      fseparate LA (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc)) →
      lossless_valid_adv LA (unionm I_kdf_env KDF_out) (resolve A RUN tt) →
      Pr_bad (A ∘ GKDF_bad_mid_ref) 45 true <= birthday_ss.
  Proof.
    intros LA A vA hsep hlva.
    rewrite /Pr_bad /Pr_op.
    rewrite resolve_link.
    rewrite /SDistr_bind /SDistr_unit dletE.
    have -> : psum
      (fun x : tgt RUN * heap =>
         Pr_code (code_link (resolve A RUN tt) GKDF_bad_mid_ref) empty_heap x *
         (let '(_, s) := x in dunit (T:=pkg_upto_bad.bad_loc 45) (get_heap s (pkg_upto_bad.bad_loc 45))) true)
      = \P_[Pr_code (code_link (resolve A RUN tt) GKDF_bad_mid_ref) empty_heap] (fun x => get_heap x.2 bad_loc).
    { rewrite /pr.
      apply: eq_psum => x.
      case: x => x1 x2 /=.
      rewrite dunit1E.
      rewrite eqb_id.
      exact: GRing.mulrC. }
    have Hcorr0 : ss_used_correspondence (get_heap empty_heap ss_tbl_loc) (get_heap empty_heap used_ss_loc).
    { move=> s.
      rewrite get_empty_heap /heap_init /=.
      split.
      - discriminate.
      - move=> [n].
        rewrite get_empty_heap.
        discriminate. }
    have Hinj0 : ss_tbl_injective (get_heap empty_heap ss_tbl_loc).
    { move=> n1 n2 s.
      rewrite get_empty_heap /heap_init /=.
      discriminate. }
    have Hfresh0 : derive_fresh (get_heap empty_heap kdone_loc) (get_heap empty_heap ss_tbl_loc) (get_heap empty_heap ideal_tbl_loc).
    { move=> s info.
      rewrite get_empty_heap /heap_init /=.
      done. }
    have Hcount0 : (size (domm (get_heap empty_heap ss_tbl_loc)) <= q)%N.
    { rewrite get_empty_heap /heap_init /=.
      rewrite domm0.
      done. }
    have Hstep := Pr_bad_GKDF_bad_mid_ref_adv_bound (resolve A RUN tt) hlva hsep empty_heap Hcorr0 Hinj0 Hfresh0 Hcount0.
    have Heq : \P_[Pr_code (code_link (resolve A RUN tt) GKDF_bad_mid_ref) empty_heap] (fun x => get_heap x.2 bad_loc)
      = \P_[Pr_code (code_link (resolve A RUN tt) GKDF_bad_mid_ref) empty_heap] (fun '(_, h') => get_heap h' bad_loc).
    { rewrite /pr.
      apply: eq_psum => x.
      by case: x => x1 x2 /=. }
    rewrite Heq.
    apply: (le_trans Hstep).
    rewrite (get_empty_heap ss_tbl_loc) (get_empty_heap used_ss_loc) /heap_init /=.
    rewrite domm0 domm0.
    rewrite subn0.
    have -> : #|(fset0 : {fset SS})| = 0%N.
    { rewrite (eq_card (B := pred0)) ?card0 //. }
    exact: bad_bound_le_birthday_ss.
  Qed.

  (** Qed'd in full: [GKDF_bad_mid_ref_GKDF_bad_false_eq_up_to_bad] —
    step (c)'s relational content — is Qed'd, and
    [Pr_bad_GKDF_bad_mid_ref_bound] — step (d)'s counting argument — is
    Qed'd in terms of the (also fully Qed'd) bespoke adversary-code
    induction [Pr_bad_GKDF_bad_mid_ref_adv_bound] (see its docstring
    above for its shape). The [Invariant], both [bad_preserved]
    obligations, the two [ValidPackage] facts, and the
    [eq_upto_bad_perf_ind] application itself are all [Qed]'d above too.
    This is the last piece of the up-to-bad ss-collision argument: the
    whole HPKE.v development now has zero mandatory admits. *)
  Lemma GKDF_bad_mid_ref_GKDF_bad_false_bound :
    ∀ LA (A : raw_package),
      fcompat KDF_loc KDFC_loc →
      fcompat KEYS_bad_loc KDFC_loc →
      ValidPackage LA (unionm I_kdf_env KDF_out) A_export A →
      fseparate LA (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc)) →
      fseparate LA (unionm KDF_loc (unionm KEYS_bad_loc KDFC_loc)) →
      lossless_valid_adv LA (unionm I_kdf_env KDF_out) (resolve A RUN tt) →
      AdvantageE GKDF_bad_mid_ref GKDF_bad_false A <= birthday_ss.
  Proof.
    intros LA A hcompD hcomp vA hsep0 hsep1 hlva.
    eapply le_trans.
    1: exact: (GKDF_bad_mid_ref_GKDF_bad_false_pr_bad_bound LA A hcompD hcomp vA hsep0 hsep1 hlva).
    exact: (Pr_bad_GKDF_bad_mid_ref_bound LA A vA hsep0 hlva).
  Qed.

  Lemma GKDF_mid_ref_ideal :
    ∀ LA (A : raw_package),
      fcompat KDF_loc KDFC_loc →
      fcompat KEYS_loc KDFC_loc →
      fcompat KEYS_bad_loc KDFC_loc →
      ValidPackage LA (unionm I_kdf_env KDF_out) A_export A →
      fseparate LA (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc)) →
      fseparate LA (unionm KDF_loc (unionm KEYS_loc KDFC_IDEAL_loc)) →
      fseparate LA (unionm KDF_loc (unionm KEYS_bad_loc KDFC_loc)) →
      fseparate LA (unionm KDF_loc (unionm KEYS_loc KDFC_loc)) →
      lossless_valid_adv LA (unionm I_kdf_env KDF_out) (resolve A RUN tt) →
      AdvantageE GKDF_mid_ref (GKDF false) A <= birthday_ss.
  Proof.
    intros LA A hcompD hcomp' hcomp vA hsep0 hsep1 hsep2 hsep3 hlva.
    ssprove triangle GKDF_mid_ref [:: GKDF_bad_mid_ref ; GKDF_bad_false ] (GKDF false) A as ineq.
    eapply le_trans. 1: exact ineq.
    rewrite -(Advantage_sym GKDF_bad_mid_ref GKDF_mid_ref A).
    rewrite (GKDF_bad_mid_ref_GKDF_mid_ref_equiv LA A vA hsep0 hsep1).
    rewrite (GKDF_bad_false_GKDF_false_equiv LA A hcompD hcomp' hcomp vA hsep2 hsep3).
    rewrite GRing.add0r GRing.addr0.
    exact: (GKDF_bad_mid_ref_GKDF_bad_false_bound LA A hcompD hcomp vA hsep0 hsep2 hlva).
  Qed.

  (** The KDF-hop bound. The [bridge] premise is the one
    instantiation-specific fact: the parameter's ideal branch, in
    context, behaves as the reference ideal. See the chain diagram
    above for why it is a premise and not a lemma.

    PREMISE POLICY (see [GKDF_mid_ref_ideal] above): the [fcompat]/
    [fseparate]/[lossless_valid_adv] premises are exactly what threading
    the ss-collision up-to-bad argument through [GKDF_mid_ref_ideal]
    forces — none of them were needed by the pre-existing chain
    ([GKDF_core_hop]/[bridge]) alone. *)
  Corollary GKDF_bound :
    ∀ LA (A : raw_package),
      fcompat KDF_loc KDFC_loc →
      fcompat KEYS_loc KDFC_loc →
      fcompat KEYS_bad_loc KDFC_loc →
      ValidPackage LA (unionm I_kdf_env KDF_out) A_export A →
      fseparate LA (unionm KDF_loc (unionm KEYS_bad_loc KDFC_IDEAL_loc)) →
      fseparate LA (unionm KDF_loc (unionm KEYS_loc KDFC_IDEAL_loc)) →
      fseparate LA (unionm KDF_loc (unionm KEYS_bad_loc KDFC_loc)) →
      fseparate LA (unionm KDF_loc (unionm KEYS_loc KDFC_loc)) →
      lossless_valid_adv LA (unionm I_kdf_env KDF_out) (resolve A RUN tt) →
      AdvantageE GKDF_mid GKDF_mid_ref A = 0 →
      AdvantageE (GKDF true) (GKDF false) A <=
        AdvantageE (KDFC true) (KDFC false) (A ∘ R_core) + birthday_ss.
  Proof.
    intros LA A hcompD hcomp' hcomp vA hsep0 hsep1 hsep2 hsep3 hlva bridge.
    ssprove triangle (GKDF true) [:: GKDF_mid ; GKDF_mid_ref ] (GKDF false) A as ineq.
    eapply le_trans. 1: exact ineq.
    rewrite (GKDF_core_hop A) bridge GRing.addr0.
    apply lerD. 1: apply lexx.
    exact: (GKDF_mid_ref_ideal LA A hcompD hcomp' hcomp vA hsep0 hsep1 hsep2 hsep3 hlva).
  Qed.

  (** Instantiation recipe (future work, in order):
      1. [KDFC b := COUNT q ∘ KDF (HKDF.v) b] (Out_N := Key_N; needs the
         location-id disjointness already respected here). Then
         [AdvantageE (KDFC true) (KDFC false) (A ∘ R_core)] is bounded by
         [security_of_KDF] at adversary [A ∘ R_core] — hypotheses to
         discharge: ValidPackage / fseparate for LA ∪ locs(R_core),
         and [lossless_valid_adv] (all packages here are assert-free
         precisely for this).
      2. [DHKEM]: an mDDH-style assumption package (static key + 'fin q
         ephemerals) + an extractor game — see conversation notes; gives
         ε_mDDH + q·ε_ext at composed adversaries.
      3. [AEADP]: a multi-instance AEAD assumption, throttled by its own
         COUNT on [AE_ENC].  *)

End HPKE.
