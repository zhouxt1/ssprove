# Research log: HKDF Extract-then-Expand PRF example and the "up-to-bad" infrastructure

Branch: `hkdf-birthday-example` (pushed to `zhouxt1/ssprove` fork).

## 1. Motivation and original question

The starting question was: **are "birthday terms" (the standard `q^2/2^n`-style
collision bounds from a birthday-bound argument) representable in SSProve?**
To answer it concretely, we built a real example: an HKDF-style
Extract-then-Expand PRF, proved via a hybrid argument, in
`theories/Crypt/examples/HKDF.v`. The proof structure needed a genuine
birthday bound (bounding the probability that Extract's internal PRK
sampling collides with an earlier one) which in turn needed a
"Fundamental-Lemma-of-Game-Playing"-style **up-to-bad** argument. SSProve
did not have this piece, so most of this effort has gone into building it
from scratch as reusable infrastructure, alongside the concrete example
that needs it.

**Update (this pass): the up-to-bad infrastructure, the birthday-bound
step (step 2, `KDF_mid_KDF_ideal_bound`/`security_of_KDF`), and the
`COUNT`-based query-bound formalization are now ALL complete and proved
(0 admits) end to end** — `security_of_KDF` is a fully `Qed`'d theorem,
independently confirmed via `Print Assumptions` to rest on nothing but
standard classical-logic axioms plus the pre-existing library axiom
`__admitted__interchange_psum`. What remains is entirely confined to
**step 1** (`KDF_real_KDF_mid_bound`, the dynamic-key hybrid argument
swapping real-PRF for ideal-random one distinct shared secret at a
time): 3 precisely-diagnosed, currently `Admitted` lemmas, all blocked
by the same root cause (see Section 11).

## 2. Status at a glance

| Piece | File | Status |
|---|---|---|
| Birthday-bound combinatorics (`bad_dist`/`bad_dist_bound`, generalized to arbitrary `finType`) | `theories/Crypt/examples/Birthday.v` | **Proved, 0 admits** |
| `COUNT` query-bound wrapper (redesigned to be unconditionally lossless — see Section 11) | `theories/Crypt/examples/HKDF.v` | **Proved, 0 admits** |
| `KDF_mid'_KDF_bad_eq_up_to_bad` (the up-to-bad relational proof between the two birthday-step ghost games) | `theories/Crypt/examples/HKDF.v` | **Proved, 0 admits** (~700 lines) |
| `KDF_mid'_KDF_bad_bound` (`eq_upto_bad_perf_ind` applied) | `theories/Crypt/examples/HKDF.v` | **Proved, 0 admits** |
| `Pr_bad_adv_bound`/`Pr_bad_COUNT_KDF_mid'_bound` (the birthday-combinatorics connector: bounding the actual run's `Pr[bad]` via `Birthday.v`'s `bad_dist_bound`) | `theories/Crypt/examples/HKDF.v` | **Proved, 0 admits** |
| **`KDF_mid_KDF_ideal_bound`** (step 2, the birthday bound itself) | `theories/Crypt/examples/HKDF.v` | **Proved, 0 admits** |
| **`security_of_KDF`** (final top-level theorem) | `theories/Crypt/examples/HKDF.v` | **`Qed`'d**, resting only on step 1's 3 remaining admits (below) plus standard axioms |
| Hop 1 of step-1 hybrid chain (`KDF_real_KDF_hyb0_equiv`, redone for the `ss`-indexed redesign) | `theories/Crypt/examples/HKDF.v` | **Proved, 0 admits** |
| `KDF_hyb_KDF_hyb_EVAL_true_equiv` | `theories/Crypt/examples/HKDF.v` | `Admitted` — root cause diagnosed precisely, fix designed but not carried out (Section 11) |
| `KDF_hyb_KDF_hyb_EVAL_false_equiv` | `theories/Crypt/examples/HKDF.v` | `Admitted` — same root cause |
| `COUNT_KDF_hyb_q_KDF_mid_equiv` | `theories/Crypt/examples/HKDF.v` | `Admitted` — needs the same adversary-code-induction technique as `Pr_bad_adv_bound`, not yet carried out |
| Final assembly `KDF_real_KDF_mid_bound` | `theories/Crypt/examples/HKDF.v` | **Mechanically `Qed`'d already** (the induction/triangle-inequality assembly itself needs no new probabilistic reasoning) — its only remaining dependencies are the 3 admits directly above |
| Up-to-bad semantic core (`pr_up_to_bad`) | `theories/Crypt/rhl_semantics/only_prob/UpToBad.v` | **Proved, 0 admits** |
| Independent/product coupling (`indp`, `indp_lmg`, `indp_rmg`, `indp_coupling`) | same file | **Proved, 0 admits** |
| `independent_rule` (combine two unary facts into a relational judgement) | `theories/Crypt/rules/UpToBadState.v` | **Proved, 0 admits** |
| Heap-generic losslessness for `raw_code` (`Pr_code_lossless`) + bridge to `θ_dens∘θ0∘repr` (`Pr_code_theta_bridge`, `theta_lossless`) | `theories/Crypt/package/pkg_lossless.v` | **Proved, 0 admits** |
| `eq_up_to_bad`/`bad_preserved`/`bad_lossless` (the relaxed up-to-bad contract) | `theories/Crypt/package/pkg_upto_bad.v` | **Proved, 0 admits** |
| `lossless_valid_adv`, `bad_lossless_bind`, `bad_preserved_link`, `theta_bad_lossless` (transporting bad-preservation through an adversary's whole continuation) | same file | **Proved, 0 admits** |
| **`eq_up_to_bad_adversary_link`** (the main adversary-linking induction) | same file | **Proved, 0 admits** |
| `Pr_bound`, `Pr_bad`, **`eq_upto_bad_perf_ind`** (the top-level Fundamental Lemma: `AdvantageE p₀ p₁ A <= Pr_bad (A ∘ p₀) bad_id true`) | same file | **Proved, 0 admits** |

`pkg_upto_bad.v` (and all other core/shared files) were **deliberately
left untouched** throughout the `COUNT`/birthday-bound/step-1 work below
— every fix was kept local to `HKDF.v` (and, for the birthday-bound
combinatorics, `Birthday.v`), to avoid changing shared infrastructure
other proofs might come to depend on. See Section 11 for why an
apparently-natural generalization of `pkg_upto_bad.v` was considered and
rejected in favor of a local fix.

All work compiles cleanly via the project's real build
(`make -f Makefile.rocq <file>.vo`) and a full project rebuild, verified
independently of the IDE (see Section 9, "tooling gotchas" — the IDE's
own diagnostics are unreliable in this environment), and independently
double-checked via `Print Assumptions` on `KDF_mid_KDF_ideal_bound`/
`security_of_KDF` (not just trusting a reported `Qed`). None of this
work has been committed yet, per a standing instruction to hold off
until step 1 is also fully closed.

## 3. Why a generic "up-to-bad" lemma is unavoidable here

We initially tried to prove hop 2's blocked leaf and the birthday
connection directly, without building general infrastructure. Both
attempts hit the **same underlying wall**: SSProve's existing relational
equivalence machinery, `eq_up_to_inv` / `eq_up_to_inv_adversary_link`
(`theories/Crypt/package/pkg_rhl.v:316-414`), is hardwired to an *exact*
equality postcondition (`b₀ = b₁ ∧ I(s₀,s₁)`) at every single oracle
call. Its adversary-linking induction (over the adversary's code,
case-split on the `raw_code` constructors `ret`/`opr`/`getr`/`putr`/
`sampler`) needs, at the `opr` (oracle-call) case, to `subst` the two
sides' return values into being *the same* value before it can invoke
the induction hypothesis on the shared continuation `k`. This is fine
when the two games are *exactly* equivalent, but breaks down completely
the moment the two sides can genuinely **diverge** (e.g. hop 2's last
leaf: one side samples a fresh PRK, the other looks one up, and once in
a while these disagree) — there is no way to `subst` two values that are
allowed to differ.

This is *exactly* the situation "up-to-bad" reasoning is for: allow the
two sides to diverge once some `bad` event fires, and bound the
probability of divergence by `Pr[bad]`. We searched
`pkg_advantage.v`/`pkg_rhl.v`/`Theta_exCP.v`/`Couplings.v` and confirmed
SSProve has no such lemma (the "Fundamental Lemma of Game Playing",
Bellare-Rogaway). Since the exact same gap blocks **two** separate proof
obligations (hop 2's leaf, and `KDF_mid_KDF_ideal_bound`), the decision
(explicit user call) was to build it once, generically, rather than
hand-roll a one-off argument twice.

## 4. Design of the up-to-bad construction (all parts now DONE)

### 4a. Semantic core — `UpToBad.v`, section `UpToBad`

Pure probability-theory statement, no packages/pRHL/adversaries
involved. Given:
- two distributions `d0`, `d1` on the same outcome type `T`,
- a coupling `d` of them (`dfst d = d0`, `dsnd d = d1`),
- a `bad : pred T` and `event : pred T` such that, across the coupling's
  support, `event` agrees whenever `bad` is false on the left
  (`d (x,y) > 0 -> bad x = false -> event x = event y`),

then `pr_up_to_bad : `|\P_[d0] event - \P_[d1] event| <= \P_[d0] bad`.
Proved via pointwise bounds (`AG_bound`/`BG_bound`/`GH_eq`) collapsed
through `psum`/marginal lemmas (`A_collapse`/`B_collapse`/`G_collapse`/
`H_collapse`). **Note (discovered later, see Section 6):
`pr_up_to_bad`'s final statement never actually needs `bad` to be
*synced* across the coupling's support** (`bad x = bad y`) — only the
one-sided "agree outside bad" hypothesis. The `Hbad_sync` context
variable and `pr_bad_sync` lemma exist in the file but turned out
unused by `pr_up_to_bad` itself; they're harmless leftovers from the
original design, not a bug.

### 4b. Independent (product) coupling — `UpToBad.v`, section `IndependentCoupling`

This is the tool for the "bad already happened" branch: once `bad` is
already true, the two sides of a coupling no longer need to be related
at all — each side only needs to keep `bad` true *on its own*. The
product coupling `indp c1 c2 := \dlet_(x<-c1) \dlet_(y<-c2) dunit (x,y)`
combines two independent unary facts into one relational fact for free.
Key discovery: this is only a *valid* coupling (correct marginals) if
both `c1`/`c2` are **lossless** (`psum c = 1` exactly, not just `<= 1`
as subdistributions normally guarantee) — proved as `indp_lmg`/
`indp_rmg`/`indp_coupling`, each taking the *other* side's losslessness
as an explicit hypothesis (e.g. `indp_lmg` needs `psum c2 = 1`, not
`psum c1 = 1` — only one side's losslessness is needed per marginal).
This completes/generalizes an abandoned, fully-commented-out section at
the bottom of `Couplings.v` (`Independent_coupling`, ending in 3 bare
`Admitted`s, scoped to a globally-fixed `R`).

### 4c. `independent_rule` — `UpToBadState.v`

State-level lifting: combines two *separately proved* unary Hoare-style
facts about `c1`/`c2` into a relational judgement `⊨⦃P⦄c1≈c2⦃Q⦄`. See
Section 5 for the full statement and the gotchas hit building it.
**One later revision**: `Hlossless1`/`Hlossless2` were generalized from
`∀s1, psum(...) = 1` to `∀s1 s2, P(s1,s2) -> psum(...) = 1` (i.e.
losslessness only needs to hold when the precondition actually holds at
that state pair, not for literally any starting state) — needed because
in the actual adversary-linking use, `code_link (k a) p` is only known
lossless once `bad_loc` is already true entering it, not
unconditionally for every possible heap.

### 4d. Bridging `Pr_code` and `θ_dens∘θ0∘repr` — `pkg_lossless.v`

This was the first real blocker (see Section 6 below for the full
story): SSProve has *two different* denotational semantics for
`raw_code`, and the existing losslessness machinery
(`nominal/Pr.v`'s `Pr_code`) was stated in one, while `independent_rule`
needs the other. Resolved by proving a direct bridge lemma
`Pr_code_theta_bridge : Pr_code c h = θ_dens (θ0 (repr c) h)` by
induction on `raw_code`, then transporting `Pr_code_lossless` through it
(`theta_lossless`).

### 4e. `eq_up_to_bad`, `bad_preserved`, `bad_lossless` — `pkg_upto_bad.v`

The relaxed per-oracle contract, mirroring `eq_up_to_inv` but matching
only "until `bad_loc` fires":

```coq
Definition bad_loc (bad_id : nat) : Location := mkloc bad_id (false : bool).

Definition eq_up_to_bad (E : Interface) (I : precond) (bad_id : nat)
  (p₀ p₁ : raw_package) :=
  ∀ (id : ident) (S T : choice_type) (x : S),
    fhas E (id, (S, T)) →
    ⊢ ⦃ λ '(s₀, s₁), I (s₀, s₁) ⦄
      resolve p₀ (id, (S, T)) x ≈ resolve p₁ (id, (S, T)) x
      ⦃ λ '(b₀, s₀) '(b₁, s₁),
          I (s₀, s₁) ∧ (get_heap s₀ (bad_loc bad_id) = false → b₀ = b₁) ⦄.

Definition bad_lossless (bad_id : nat) {A} (c : raw_code A) (h : heap) : Prop :=
  psum (Pr_code c h) = 1 ∧
  (∀ a h', (0 < Pr_code c h (a, h'))%R → get_heap h' (bad_loc bad_id) = true).

Definition bad_preserved (E : Interface) (bad_id : nat) (p : raw_package) :=
  ∀ (id : ident) (S T : choice_type) (x : S) (h : heap),
    fhas E (id, (S, T)) →
    get_heap h (bad_loc bad_id) = true →
    bad_lossless bad_id (resolve p (id, (S, T)) x) h.
```

`bad_preserved` is the per-*single-oracle-call* fact the caller supplies:
once `bad_loc` is true entering a call, it stays true and the call is
lossless — stated in the `Pr_code` vocabulary (simpler equations,
matches how a concrete package's proof would establish it).

### 4f. Transporting `bad_preserved` through a whole adversary — `pkg_upto_bad.v`

The adversary calls *many* oracles across its execution, and once
`bad_loc` fires partway through, the *entire remaining continuation*
(not just the next single call) needs to keep it true and stay
lossless. This needed genuinely new infrastructure beyond a single
`bad_preserved` hypothesis:

- **`lossless_valid_adv`**: like `pkg_lossless.v`'s `lossless_valid`, but
  *allows* `opr` nodes (unlike a package's own code, adversary code
  genuinely calls oracles — those calls' losslessness is discharged
  separately via `bad_preserved`, not required of the "op" itself).
- **`bad_lossless_bind`**: bind-composition of `bad_lossless`, mirroring
  `Pr_code_bind`'s structure — "if `c`'s denotation is `bad_lossless`
  and every reachable continuation is too, so is the whole bind."
- **`bad_preserved_link`**: `bad_preserved` (one call) transported
  through `code_link`'s entire structural recursion over the
  adversary's code, by induction using `bad_lossless_bind` at each
  `opr` node. Needs `bad_id \notin domm LA` (NOT `¬ fhas LA (bad_loc
  bad_id)`, which turned out too weak — same key with a *different*
  type tag isn't actually ruled out by `fhas`-non-membership; only
  `domm`-non-membership genuinely prevents the adversary's own
  gets/puts from touching that key at all) so the adversary's own
  locations can't disturb `bad_loc`.
- **`theta_bad_lossless`**: bridges `bad_lossless` (`Pr_code`
  vocabulary) into `θ_dens∘θ0∘repr` terms via `Pr_code_theta_bridge`,
  for the one place `independent_rule` actually needs it.

### 4g. `eq_up_to_bad_adversary_link` — the main induction, `pkg_upto_bad.v`

```coq
Lemma eq_up_to_bad_adversary_link :
  ∀ {L₀ L₁ LA E} (p₀ p₁ : raw_package) (I : precond) (bad_id : nat)
    {B} (A : raw_code B)
    `{ValidPackage L₀ Game_import E p₀} `{ValidPackage L₁ Game_import E p₁}
    `{@ValidCode LA E B A},
    INV LA I →
    lossless_valid_adv LA E A →
    bad_id \notin domm LA →
    (∀ s₀ s₁, I (s₀, s₁) → get_heap s₀ (bad_loc bad_id) = get_heap s₁ (bad_loc bad_id)) →
    (∀ s₀ s₁, get_heap s₀ (bad_loc bad_id) = true →
       get_heap s₁ (bad_loc bad_id) = true → I (s₀, s₁)) →
    eq_up_to_bad E I bad_id p₀ p₁ →
    bad_preserved E bad_id p₀ →
    bad_preserved E bad_id p₁ →
    r⊨ ⦃ I ⦄ code_link A p₀ ≈ code_link A p₁
      ⦃ λ '(b₀, s₀) '(b₁, s₁),
          I (s₀, s₁) ∧ (get_heap s₀ (bad_loc bad_id) = false → b₀ = b₁) ⦄.
```

Structural induction on the adversary's `raw_code`
(`ret`/`opr`/`getr`/`putr`/`sampler`), mirroring
`eq_up_to_inv_adversary_link` in every case *except* `opr`, where it
case-splits on `get_heap s₀ (bad_loc bad_id)` entering the call:

- **false**: `eq_up_to_bad`'s per-op postcondition gives `a₀ = a₁` here
  (the antecedent of the "match unless bad" implication is met) — from
  there it's identical to `eq_up_to_inv_adversary_link`'s own proof,
  `subst`-ing and recursing on the structural IH.
- **true**: `a₀`/`a₁` may genuinely differ, so there's no `a₀ = a₁` to
  `subst` and the shared-continuation IH can't be invoked directly.
  Instead: derive `get_heap s₁ (bad_loc bad_id) = true` too (via the
  sync hypothesis), then apply `independent_rule`, supplying
  `bad_preserved_link` (bridged via `theta_bad_lossless`) as the
  losslessness hypotheses on each side separately, and reconstructing
  the postcondition's `I(s₀',s₁')` conjunct from the "bad-implies-I"
  hypothesis (both sides' `bad_loc` stay true via `bad_preserved_link`'s
  monotonicity half) — the `b₀=b₁` conjunct is discharged vacuously
  since its antecedent (`bad_loc s₀' = false`) is false.

### 4h. The top-level Fundamental Lemma — `Pr_bound`, `Pr_bad`, `eq_upto_bad_perf_ind`

`eq_up_to_bad_adversary_link`'s conclusion is a *relational judgement*
(a coupling-existence fact), not yet a number. Turning it into an
actual `AdvantageE` bound needed one more layer, mirroring
`eq_upto_inv_perf_ind` (`pkg_rhl.v`, which does the analogous thing for
exact-match equivalences, producing `AdvantageE p₀ p₁ A = 0` via
`Pr_eq_empty`):

```coq
Lemma Pr_bound {X : ord_choiceType} {S : choiceType} {event bad : pred (X * S)}
  (Psi : S * S → Prop) (phi : (X * S) → (X * S) → Prop)
  (c1 c2 : RulesStateProb.FrStP S X)
  (H : ⊨ ⦃ Psi ⦄ c1 ≈ c2 ⦃ phi ⦄)
  {s1 s2 : S} (HPsi : Psi (s1, s2))
  (Hagree : ∀ x y, phi x y → bad x = false → event x = event y) :
  `| \P_[θ_dens (θ0 c1 s1)] event - \P_[θ_dens (θ0 c2 s2)] event |
  <= \P_[θ_dens (θ0 c1 s1)] bad.

Definition Pr_bad (p : raw_package) (bad_id : nat) : SDistr (bool : choiceType) :=
  SDistr_bind (fun '(_, s) => SDistr_unit _ (get_heap s (bad_loc bad_id)))
    (Pr_op p RUN tt empty_heap).

Lemma eq_upto_bad_perf_ind :
  ∀ {L₀ L₁ LA E} (p₀ p₁ : raw_package) (I : precond) (bad_id : nat) (A : raw_package)
    `{ValidPackage L₀ Game_import E p₀} `{ValidPackage L₁ Game_import E p₁}
    `{ValidPackage LA E A_export A},
    INV LA I → I (empty_heap, empty_heap) → fseparate LA L₀ → fseparate LA L₁ →
    lossless_valid_adv LA E (resolve A RUN tt) → bad_id \notin domm LA →
    (∀ s₀ s₁, I (s₀, s₁) → get_heap s₀ (bad_loc bad_id) = get_heap s₁ (bad_loc bad_id)) →
    (∀ s₀ s₁, get_heap s₀ (bad_loc bad_id) = true →
       get_heap s₁ (bad_loc bad_id) = true → I (s₀, s₁)) →
    eq_up_to_bad E I bad_id p₀ p₁ → bad_preserved E bad_id p₀ → bad_preserved E bad_id p₁ →
    AdvantageE p₀ p₁ A <= Pr_bad (A ∘ p₀) bad_id true.
```

`Pr_bound` mirrors `Pr_eq`'s coupling-extraction technique
(`RulesStateProb.v:609`) but feeds the extracted coupling to
`pr_up_to_bad` instead of proving an equality directly (note it only
needs `Hagree`, matching the `pr_up_to_bad`-doesn't-need-sync discovery
from Section 4a). `eq_upto_bad_perf_ind`'s proof mirrors
`eq_upto_inv_perf_ind`'s long rewrite chain almost verbatim — connecting
`Pr_op`/`thetaFstd` to `code_link` via `resolve_link`, unfolding
`SDistr_bind`/`dletE`, then the same
`TransformingLaxMorph.rlmm_from_lmla_obligation_1`/`SDistr_rightneutral`
unfolds `pkg_rhl.v`'s own proof needs — the one new step is an extra
`Hrew2` lemma for the bad-reading marginal (`get_heap s (bad_loc
bad_id)`), alongside the original's `Hrew` for the event-reading one
(the run's own boolean output).

## 5. `independent_rule` — full statement and gotchas

`theories/Crypt/rules/UpToBadState.v`, fully proved, 0 admits. Current
statement (post the `Hlossless1`/`Hlossless2` generalization, Section 4c):

```coq
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
```

I.e.: given `c1`/`c2` are lossless *whenever `P` holds of the starting
state pair* (not necessarily for literally any state), and a purely
*unary* argument that "if `P` held, and `c1` from `s1` can reach
`(a1,s1')`, and `c2` from `s2` can reach `(a2,s2')`, then `Q` holds of
that pair" (this argument never needs to relate `c1`'s and `c2`'s
executions to each other — proved by reasoning about each side's
support *separately*), we get the full relational judgement
`⊨⦃P⦄c1≈c2⦃Q⦄`.

Proof mirrors `reflexivity_rule`'s shape exactly
(`theories/Crypt/rules/RulesStateProb.v:797-807`, which builds the
*diagonal* self-coupling `coupling_self_SDistr` for the "same program,
same input" case) — just substituting the *product* coupling `indp` for
the diagonal, and closing the coupling obligation via `indp_lmg`/
`indp_rmg`/`indp_ext` instead of `coupling_self`/`aux_lemma`.

### Notable gotchas hit while building this (useful if repeating this pattern)

- **`{A : ord_choiceType}` as a binder type requires an EXTRA import.**
  `ord_choiceType : ord_category` is not itself a sort; using it as a
  binder type relies on the record-field coercion `Obj :> Type`
  declared in `OrderEnrichedCategory.v` (`{ Obj :> Type ... }`,
  line 22). This coercion does **not** propagate merely by transitively
  requiring a file that itself required `OrderEnrichedCategory` — you
  must `From SSProve.Relational Require Import OrderEnrichedCategory.`
  directly in any new file that uses `ord_choiceType` as a type, even
  though `RulesStateProb.v` (which the new file also imports) already
  does so internally. (General Rocq behavior: `Require Import Foo` does
  *not* re-open modules that `Foo` itself only `Require Import`'d
  rather than `Require Export`'d — coercions declared via `:>` follow
  the same "must be brought into scope by name" rule as any other
  notation/coercion registered by a plain, non-`Export`ed import. This
  bit us repeatedly across the whole session — see also `bindrFree`
  needing `FreeProbProg` directly, and `pr_up_to_bad` needing
  `rhl_semantics.only_prob.UpToBad` directly despite `UpToBadState`
  already requiring it.)
- **`move => [s1 s2] π [Hpre Himp] /=.` in one go silently fails**
  ("No assumption...") on the `⊨⦃P⦄c1≈c2⦃Q⦄` goal — it must be split
  into two separate `move` calls with a `/=` in between:
  `move => [s1 s2] /=. move => π [Hpre Himp] /=.` (mirrors
  `reflexivity_rule`'s own two-step `move` exactly — this is not
  cosmetic, the combined form does not typecheck).
- **`indp` does NOT take the losslessness hypotheses as arguments** —
  only `indp_lmg`/`indp_rmg`/`indp_ext` do. This is because Rocq's
  section-variable generalization only adds a `Context` hypothesis to a
  *constant* if that constant's *body* actually uses it; `indp`'s body
  never touches `Hc1`/`Hc2`, so post-section its type is just
  `indp : ∀{R T1 T2}, distr T1 → distr T2 → distr(T1*T2)`. Passing extra
  arguments to `indp c1 c2` silently type-checks *against the wrong
  slot* by coercing the resulting distribution value through its own
  `mu`-function coercion (a `distr` coerces to its underlying `T → R`
  function!) — producing a deeply confusing error where a *proof term*
  (`Hlossless1 s1`) is reported as having the wrong type against some
  `Choice.sort (...)` expression, rather than a sensible "too many
  arguments" error. Lesson: always double check a lemma's *actual*
  post-section signature via `About`, don't assume section-context
  hypotheses survive into every lemma/definition declared inside that
  section.
- **`0 < x*y → 0 < x ∧ 0 < y` (given `x,y ≥ 0`) has no one-line stock
  lemma that worked here** (`pmulr_rgt0` didn't have the right shape,
  `mulf_eq0` wasn't in scope under this name) — resolved manually via
  `lt0r` (`(0<x) = (x!=0) && (0<=x)`) plus a proof-by-contradiction on
  each factor being `0` (`apply/eqP=>Hz; move: Hgt; by rewrite Hz
  GRing.mul0r Order.POrderTheory.ltxx`).
- **`GRing.Theory`/`Order.POrderTheory` names need explicit
  qualification** unless `Import GRing.Theory.`/`Import
  Order.POrderTheory.` are added.

## 6. The `Pr_code` vs `θ_dens∘θ0∘repr` blocker — how it was resolved

This was the blocker that stalled progress for a while. **Resolved**;
recorded here for anyone hitting the same wall again.

`pkg_lossless.v`'s `Pr_code_lossless` (heap-generic losslessness for
`raw_code`) was proved in terms of `Pr_code` (`theories/Crypt/nominal/
Pr.v`), which interprets `raw_code` *directly* via the `SDistr` relative
monad (`SubDistr.v`'s `SDistr_bind`/`SDistr_unit`), with per-constructor
equations `Pr_code_ret`/`Pr_code_get`/`Pr_code_put`/`Pr_code_sample`/
`Pr_code_call` (`= dnull`) and a `Pr_code_bind` commutation lemma.

But `independent_rule` needs **`θ_dens (θ0 c s)`**, which interprets
`raw_code` *indirectly*: first translate to the free monad via `repr`
(`pkg_semantics.v:42-60`), then interpret via `θ0 := @unaryIntState S A`
(state-threading, `RulesStateProb.v:52`), then `θ_dens` turns the result
into an actual `SDistr`.

**Confirmed via a live proof-state check that these are NOT
definitionally equal** (`erefl : Pr_code c h = θ_dens (θ0 (repr c) h)`
fails to unify). The fix taken was the bridge-lemma route: prove
`Pr_code_theta_bridge : ∀{A}(c:raw_code A)(h:heap), Pr_code c h =
θ_dens (θ0 (repr c) h)` by induction on `c`, mirroring `Pr_code_bind`'s
five-case structure. Each non-trivial case reduces, after `cbn`, to the
exact same "doubly wrapped `SDistr_obligation_2`" shape `Pr_code_ret`'s
own proof already had to unwind — i.e. the SAME rewrite recipe
(`rewrite /SubDistr.SDistr_obligation_2 2!SubDistr.SDistr_rightneutral
//`) worked for `getr`/`putr`/`sampler` too, discovered by stepping
through the goal live via `rocq_check` rather than reasoning about it
abstractly. The `opr`/`call` case used `dlet_null_ext`. The `sampler`
case needed the same `__admitted__interchange_psum` dlet-interchange
technique as `Pr_code_lossless` itself.

`theta_lossless` then transports `Pr_code_lossless` through the bridge
in one line (`rewrite -Pr_code_theta_bridge; exact: Pr_code_lossless`).

**A second, similar mismatch surfaced later** (Section 8, `thetaFstd` vs
`θ_dens∘θ0`) — same underlying lesson: SSProve has more than two
notionally-equivalent encodings of "run this code and get a
distribution over outcomes", and none of them are definitionally equal
to each other even when propositionally so. Always check via a live
`erefl` probe before assuming two such expressions interchange for
free.

## 7. Design notes / facts established along the way

- `F_choice_prod_obj⟨C1,C2⟩ := (C1*C2)%type` (`ChoiceAsOrd.v:40-45`) —
  confirmed to be mathcomp's plain pair type, not a bespoke wrapper —
  BUT when it appears as the argument to `θ0`/`θ_dens`'s type family, it
  shows up wrapped in extra functor applications rather than literally
  `F_choice_prod_obj⟨A1,S1⟩` — these reduce to the same thing but aren't
  syntactically identical; didn't end up mattering anywhere in this
  construction (unification handled it whenever the implicit type
  arguments were inferred from actual values rather than pre-specified).
- `LosslessOp` (`pkg_distr.v:203-204`) is a **single-field `Class`**,
  which Rocq compiles as a transparent alias for the field's own type
  (`psum op.π2 = 1`) rather than a wrapping record — so a hypothesis
  `Hop : LosslessOp op` can be used directly as a term of type
  `psum op.π2 = 1` (e.g. via `rewrite -Hop`), no projection needed. This
  is NOT true for multi-field classes/records — don't assume it
  generalizes.
- **`rewrite (lemma_with_hypotheses)` puts side-condition goals in the
  ORDER THE `rewrite` HAPPENS TO PRODUCE THEM, not always "side
  conditions first" or "main goal first" consistently** — confirmed by
  direct observation across several proofs in this session: sometimes
  the main (rewritten) goal came first with side conditions after
  (`pkg_lossless.v`'s own `Pr_code_lossless`), sometimes the reverse
  (`bad_lossless_bind`'s first `rewrite __admitted__interchange_psum`).
  **Do not assume the order from one proof carries to the next** —
  always check the live goal list via `rocq_check`/`rocq_start` before
  writing bullets for a multi-goal state produced by a conditional
  `rewrite`.
- `nominal/Pr.v`, despite its directory name, is **not** a separate DSL
  — it imports and reuses the main `pkg_*` framework directly, and
  connects to `pkg_advantage.v`'s own `Pr`/`Pr_op` via `Pr_Pr_code`/
  `Pr_Pr_fst` (`Pr.v:87-92`, `152-157`) — but those bridge lemmas are
  only stated for the **empty starting heap**.
- `theories/Crypt/nominal/packages/HybridArgument.v` (and its sibling
  `TotalProbability.v`) already implements a **full, working hybrid-
  argument reduction** (`Adv_hybrid`, `Adv_hybrid_dep`, with a clean
  triangle-inequality sum over `q` hybrids) — but it's built on the
  **`nom_package`/renaming ("nominal") layer**, a different, higher-level
  DSL from the plain `ValidPackage`/`raw_package` layer HKDF.v is
  written against. Good precedent for how the *final* assembly step
  (`KDF_real_KDF_mid_bound`, induction on `i` + triangle inequality)
  should look, but not directly reusable without a framework switch
  we're not planning to make.
- `fhas m (k,v)` (membership of a specific key-value pair) is
  **strictly weaker** than `k \in domm m` (key membership) for ruling
  out interference: `¬ fhas LA (bad_loc bad_id)` does NOT prevent `LA`
  from containing a *different* location at the *same* key `bad_id`
  with a different type tag — only `bad_id \notin domm LA` does. Cost
  us a wrong lemma statement in `bad_preserved_link` before the fix.

## 8. `pkg_rhl.v`'s `r⊨⦃⦄` notation — the exact import/scope recipe

Getting `pkg_upto_bad.v` to even *state* `eq_up_to_bad_adversary_link`
took real trial and error, independent of the proof content:

- **Import list/order matters for canonical structure resolution.**
  `pkg_rhl.v`'s own import list/order had to be matched *almost
  verbatim* (`Prelude Axioms ChoiceAsOrd SubDistr Couplings
  RulesStateProb UniformStateProb UniformDistrLemmas StateTransfThetaDens
  StateTransformingLaxMorph choice_type pkg_core_definition pkg_notation
  pkg_tactics pkg_composition pkg_heap pkg_semantics pkg_advantage
  pkg_invariants pkg_distr Casts fmap_extra pkg_rhl`, appending our own
  imports after) — reordering it (e.g. moving `RulesStateProb` after
  `pkg_rhl` instead of before `pkg_core_definition`) broke the
  `r⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄` notation's elaboration: `pre : precond`
  stopped unifying against `fromPrePost`'s implicit `choiceType`
  argument ("The term ... has type precond while it is expected to have
  type choice.Choice.sort ?S1 * ... -> Prop"), apparently because
  `heap`'s canonical choice-type structure resolution is genuinely
  import-order-sensitive in this codebase.
- **Both `rsemantic_scope` AND `package_scope` need to be open, in THAT
  ORDER** (`rsemantic_scope` first, `package_scope` last — matching
  `pkg_rhl.v:41,46` exactly). Opening only one, or opening them in the
  reverse order, breaks either the `⊨⦃⦄` notation (needed for
  `match goal` patterns inside `bind_rule_pp`-style proofs at the
  `getr`/`putr`/`sampler` cases) or the `r⊨⦃⦄` one (needed everywhere
  else) — never both at once. This was found by noticing `pkg_rhl.v`
  itself opens BOTH, in that specific order, rather than assuming
  `package_scope` alone (which is what earlier work in this session
  had settled on, since at that point only `r⊨⦃⦄` was needed) sufficed
  once `⊨⦃⦄`-based tactics were needed too.
- **Name collisions between transitively-imported modules are silent
  and confusing.** `pkg_upto_bad.v` imports both `RulesStateProb`
  (defining `FrStP (S:choiceType) := @StateTransformingLaxMorph.FrStP
  S`, a thin wrapper) and `StateTransformingLaxMorph` directly (defining
  its OWN `FrStP : choiceType -> ord_relativeMonad choice_incl`,
  imported later so its **plain, unqualified name wins** over
  `RulesStateProb`'s wrapper). Using bare `FrStP S X` in a new lemma
  statement silently picked the WRONG one and produced a confusing
  "Illegal application (Non-functional construction)" error rather than
  a name-not-found error. Fix: qualify explicitly as
  `RulesStateProb.FrStP S X` wherever this ambiguity can arise.
- **`thetaFstd A c s` (pkg_advantage.v's own semantics, used by its
  `Pr_code`/`Pr_op`/`Pr`) is yet a THIRD encoding, not convertible with
  `θ_dens (θ0 c s)` via `exact`/`apply`/`simpl` alone** — despite both
  ultimately being "run this code from this heap". The existing
  `eq_upto_inv_perf_ind` (pkg_rhl.v) proof already contains the exact
  recipe for bridging them: `unfold
  TransformingLaxMorph.rlmm_from_lmla_obligation_1; simpl; unfold
  SubDistr.SDistr_obligation_2; simpl; unfold
  OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1; rewrite
  !SDistr_rightneutral; simpl; rewrite
  /StateTransfThetaDens.unaryStateBeta'_obligation_1` — this sequence of
  unfolds, applied to the GOAL (not just to a derived hypothesis), is
  what finally makes a `thetaFstd`-shaped expression match a
  `θ_dens∘θ0`-shaped one syntactically. Skipping any of these unfolds
  and trying `exact`/`apply` directly fails even though the two sides
  are provably (and, it turns out, actually) equal.
- **`rocq_compile_file` does not persist a fresh `.vo` by default** —
  editing a file (e.g. `UpToBadState.v`, to generalize
  `independent_rule`'s hypotheses) and recompiling it standalone via
  `rocq_compile_file` leaves the OLD, stale `.vo` on disk for anything
  that later `Require`s it (e.g. `pkg_upto_bad.v`'s interactive
  session), silently working against the pre-edit signature. Symptom:
  `About` on the changed lemma, inside a *different* file's interactive
  session, shows the OLD type. Fix: a real
  `make -f Makefile.rocq <file>.vo` (or `rocq_compile_file` with
  `keep_vo:true`) after any edit to a file something else depends on,
  before continuing interactive work downstream.

## 9. Tooling notes

- **rocq-mcp is fully working**, including the interactive tools
  (`rocq_start`/`rocq_check`/`rocq_step_multi`/`rocq_query`), after the
  user installed `coq-lsp` (bundled with `pet`) directly into the live
  `ssprove` opam switch. This *did* initially break the build (ppxlib/
  ppx_deriving/ppx_optcomp downgrade forced a mathcomp recompile,
  leaving stale/inconsistent `.vo` files) — exactly the risk flagged
  before the user did it — but a full clean rebuild (done by the user)
  fixed it. `.mcp.json` (project-scoped MCP server config, hardcoded
  local paths) is **intentionally not committed** to the repo.
- **The IDE's own inline diagnostics are unreliable throughout this
  entire environment** (a separate, version-mismatched Rocq checker
  instance from the one rocq-mcp/`make` actually use) — they report
  bogus errors (stale `.vo` "bad version number", "cannot find
  all_ssreflect", phantom syntax errors) on nearly every edit. The
  established, correct workflow is to **always** verify via
  `mcp__rocq-mcp__rocq_compile_file` and/or real
  `make -f Makefile.rocq <file>.vo`, and ignore the IDE diagnostics
  entirely.
- **Using the interactive MCP tools to inspect live goal states was
  consistently far more effective than reasoning abstractly about
  tactic/notation/unification behavior.** Nearly every non-trivial bug
  in this whole effort (wrong bullet order after a conditional
  `rewrite`, the `indp` extra-arguments mis-elaboration, the missing
  `ord_choiceType` coercion import, the `r⊨⦃⦄` scope-order issue, the
  `FrStP` name collision, the `thetaFstd` vs `θ_dens∘θ0` mismatch, the
  stale-`.vo` issue) was diagnosed in one or two live queries after
  spending much longer trying to reason about it from reading source
  alone. Prefer reaching for `rocq_start`/`rocq_check`/`rocq_step_multi`
  early whenever a proof step's actual goal shape, or a notation's
  actual elaborated form, is uncertain — don't try to hand-simulate
  Rocq's elaborator.
- Mathcomp/ssreflect gotchas re-confirmed across this whole effort:
  `lia`/`lra` don't work on mathcomp `nat`/`realType`; `case: (boolP
  P)`/`(eqVneq x y)`/`(ltnP x y)` views auto-substitute into the goal (a
  subsequent explicit `rewrite` of the same fact then fails with "does
  not match any subterm"); `have H := lemma args` with an unpinned
  implicit `{R:realType}` can spuriously generalize over a fresh
  `t:realType` unless fully explicit (`@lemma R ...`) is used in both
  the term and any type ascription.

## 10. Applying the up-to-bad machinery: `COUNT`, the birthday bound, and the `ss`-indexing redesign

Sections 1-9 above describe the up-to-bad *infrastructure* (all done, 0
admits, and never touched again after this point). This section covers
everything built on top of it, in the order it happened.

### 10a. The birthday step (`KDF_mid_KDF_ideal_bound`) — now fully done

1. Built the ghost game `KDF_mid'` (real Extract + ideal Expand, plus
   `KDF_bad`-style `bad_loc`/`used_prk_loc` bookkeeping) and proved
   `KDF_mid ≈₀ KDF_mid'` (exact equivalence, mirroring
   `KDF_real_KDF_hyb0_equiv`'s ignore-invariant style).
2. Designed `KDF_mid'_bad_inv` (a `heap_ignore ⋊ syncs ⋊ rel_app` stack,
   left-associative `⋊`) relating `KDF_mid'` and `KDF_bad`, and proved
   `KDF_mid'_KDF_bad_eq_up_to_bad : eq_up_to_bad DERIVE_export
   KDF_mid'_bad_inv 4 KDF_mid' KDF_bad` — a ~700-line relational proof,
   the single largest individual proof in this whole effort. `bad_loc`
   fires exactly when Extract's lazily-sampled table assigns the same
   `prk` to two different shared secrets (the birthday collision).
3. Applied `eq_upto_bad_perf_ind` (Section 4h) to get
   `KDF_mid'_KDF_bad_bound : AdvantageE KDF_mid' KDF_bad A <= Pr_bad (A
   ∘ KDF_mid') 4 true`.
4. **Formalizing "the adversary makes at most `q` queries".** `A` is an
   arbitrary adversary with no built-in query bound, so `Pr_bad(...) <=
   birthday_bound q` can't hold for a free `q` without *some* way to tie
   `q` to `A`'s behavior. Two established SSProve conventions exist for
   this: (a) `PRFPRG.v`'s `security_based_on_prf` leaves `q` free and
   adds a side hypothesis pinning down which `q` applies to a given `A`
   (with an explicit comment admitting such a `q` "might not exist for
   some adversaries"); (b) `PKE/Scheme.v`'s `COUNT`/`MI_COUNT` wrapper,
   which `#assert`s a per-call counter `< q` before answering — making
   the bound unconditionally true for *any* adversary, since queries
   past the `q`-th just get zero-mass `fail`. We chose (b) — an
   unconditional theorem is strictly better than one with an existence
   caveat.
5. **First design of `COUNT q` (later found broken, then fixed):**
   mirroring `Scheme.v`'s own `#assert count < q` exactly. This
   compiled and three `≈₀`-based "push `COUNT q` through a perfect
   equivalence via `Advantage_link`" triangle legs went through fine
   (`COUNT_KDF_mid_KDF_mid'_bound`, `COUNT_KDF_bad_KDF_ideal_bound`,
   `COUNT_link_valid`) — because exact-match `≈₀`/`eq_rel_perf_ind`
   reasoning places no losslessness requirement on either side.
6. **The `#assert` design turned out to be structurally incompatible
   with up-to-bad reasoning.** Applying `eq_upto_bad_perf_ind` at the
   composed adversary `A ∘ COUNT q` needs `lossless_valid_adv LA'
   DERIVE_export (resolve (A ∘ COUNT q) RUN tt)`. Since `resolve (A ∘
   COUNT q) RUN tt` literally splices `COUNT q`'s own `count ← get
   count_loc ;; #assert count < q ;; ...` in at every one of `A`'s
   `DERIVE` calls, and `lossless_valid_adv`'s `getr` case demands
   losslessness for **every** possible value the `get` could return
   (not just reachable ones — confirmed directly against `pkg_upto_bad.v`'s
   literal `lva_getr` constructor, which has no reachability caveat),
   this obligation is unconditionally FALSE for any `count >= q` reading
   (where `#assert` reduces to `fail`, zero mass — `dnull` is not a
   `LosslessOp`). `bad_preserved` has the identical problem from the
   other direction (it quantifies over an arbitrary heap, not just a
   reachable one). This is not a proof-difficulty problem, it's a type
   mismatch between "sub-distribution" and "the full probability
   distribution `independent_rule`'s product coupling genuinely needs."
7. **Two possible fixes were considered**: (A) generalize
   `lossless_valid_adv`/`bad_preserved`/`eq_upto_bad_perf_ind` in
   `pkg_upto_bad.v` to be relative to a heap-reachability invariant —
   rejected as a shared-infrastructure change with a large blast radius,
   and (on closer analysis) one that would ITSELF need an "adversary
   makes ≤ q queries" assumption to discharge the relativized
   obligation soundly, quietly reintroducing exactly the existence
   caveat `COUNT` was meant to avoid. (B) **Redesign `COUNT q` itself to
   never fail at all**: past the `q`-th query, route to an independent
   uniform sample instead of asserting:
   ```coq
   Definition COUNT (q : nat) : package DERIVE_export DERIVE_export :=
     [package [fmap count_loc] ;
       #def #[ DERIVE ] ('(ss, info) : 'ss × 'info) : 'out
       {
         #import {sig #[ DERIVE ] : 'ss × 'info → 'out } as derive ;;
         count ← get count_loc ;;
         if count < q then
           #put count_loc := count.+1 ;; derive (ss, info)
         else
           y <$ uniform Out_N ;; ret y
       }
     ].
   ```
   This is unconditionally lossless for *every* value of `count_loc`
   (both branches are lossless), so `lossless_valid_adv` is now
   establishable with **zero changes to `pkg_upto_bad.v`** — and the
   dummy branch costs no extra advantage (it's exactly as independent
   of everything as `KDF_ideal`'s own output). Chose (B).
8. Built `lossless_valid_adv_COUNT_link` (a new composition lemma —
   confirmed via grep that `pkg_upto_bad.v` has no existing `code_link`
   compatibility lemma for `lossless_valid_adv`, so this had to be built
   from scratch, by structural induction on the adversary's own code
   mirroring `bad_preserved_link`'s shape) and
   `COUNT_KDF_mid'_KDF_bad_bound` (instantiating
   `KDF_mid'_KDF_bad_bound` at the composed adversary `A ∘ COUNT q`).
9. **The actual birthday combinatorics connector**,
   `Pr_bad_adv_bound`/`Pr_bad_COUNT_KDF_mid'_bound`: bounding
   `Pr_bad ((A ∘ COUNT q) ∘ KDF_mid') 4 true <= birthday_bound q` for an
   ARBITRARY adversary. Key structural fact: a repeat `ss` query costs
   no fresh `prk` sample at all, so only fresh-`ss` queries advance the
   birthday process, and `COUNT q` bounds the number of those to at
   most `q`. Proved by induction on the adversary's own code (mirroring
   `pkg_upto_bad.v`'s `eq_up_to_bad_adversary_link`/`bad_preserved_link`
   recursion over `code_link`), carrying the current heap and bounding
   `Pr[bad ends true]` by `Birthday.bad_bound (q - count) #|used_prk_loc|`
   (or `1` if already bad) — a per-step union-bound argument
   (`Birthday.v`'s `expectation_le_bad_bound`, extracted from
   `bad_dist_bound`'s own inductive step as a reusable lemma) interleaved
   with the adversary-code induction, rather than `bad_dist_bound`'s own
   induction on a fixed, static query count. `Birthday.v` itself was
   generalized from a fixed `Context (N : nat)` to `Context (F :
   finType)` to support this. Instantiating at `empty_heap` and closing
   with the trivial arithmetic `bad_bound_le_birthday_bound` (`bad_bound
   q 0 <= birthday_bound q`) finishes `KDF_mid_KDF_ideal_bound` and
   `security_of_KDF`, both now fully `Qed`'d.
10. One diagnostic pitfall hit along the way: calling `fmap_solve`
    repeatedly in a context accumulating prior `have`-introduced proof
    terms caused catastrophic slowdown (one call: ~14s; two: still
    running after 150s+). Fixed by hoisting the needed `fhas` facts into
    standalone top-level lemmas proved in isolation, then using them as
    plain terms inline.

### 10b. Step 1 (`KDF_real_KDF_mid_bound`) — in progress, 3 admits left

`KDF_hyb i`/`KDF_hyb_EVAL i` (the per-distinct-PRK hybrid family) and
`KDF_hyb_KDF_hyb_EVAL_true_equiv` pre-date this pass and were blocked.
Reading the blocked proof's own comments identified the root cause:
`get_prk_idx` assigned indices **by PRK** (`prk_index_loc`), sampling
`prk` *before* deciding its index — so "is this the `i`-th distinct
key?" depended on the just-sampled `prk` value itself, leaving no
still-pending sample to couple against `EVAL`'s own fresh key (unlike
`PRFPRG.v`, whose hybrid index is a raw query counter, decided
independently of any sampled value).

**Fix**: index by **shared secret** (`ss`), not by PRK — sound
specifically for this step because (unlike step 2) it doesn't need to
track PRK collisions at all. Replaced `get_prk_idx`/`prk_index_loc`/
`prk_count_loc` with decoupled `get_ss_idx`/`get_prk`/`ss_index_loc`/
`ss_count_loc`, and redefined `KDF_hyb`/`KDF_hyb_EVAL` accordingly.
`KDF_real_KDF_hyb0_equiv` was redone for the new design and re-`Qed`'d.

**A second, independent bug was found and fixed** while restating the
final theorems for the new design: `prf_epsilon A` (for the *bare*
top-level adversary `A`, whose import interface is `DERIVE_export`) is
provably `0` for every valid `A`, since `Advantage`/`AdvantageE`/`Pr_op`
place no static interface constraint on their arguments (they're raw
functions of `raw_package`), and `A`'s own code structurally never
calls `EVAL_export`'s operation id at all — so composing it with `EVAL
true`/`EVAL false` is a complete no-op, making the two sides identical
and the advantage exactly `0` (counterexample confirming the original
statement was simply false in general: `PRF info prk := info`). This
means the versions of `KDF_real_KDF_mid_bound`/`security_of_KDF` from
earlier in this pass (using bare `prf_epsilon A`) were WRONG statements
(they compiled as `Admitted` stubs, which Rocq doesn't check for
truth). Fixed by composing `A` with `KDF_hyb_EVAL i` first
(`prf_epsilon ((A ∘ COUNT q) ∘ KDF_hyb_EVAL i)`), exactly matching
`PRFPRG.v`'s own `hyb_security_based_on_prf` convention
(`prf_epsilon (A ∘ GEN_HYB_EVAL_pkg i)`).

With the redesign and the bugfix in place, the mechanical assembly of
`KDF_real_KDF_mid_bound`/`security_of_KDF` (the `elim: q` / 4-way
triangle argument, mirroring `hyb_security_based_on_prf` exactly) is
**already `Qed`'d** — it type-checks and composes correctly right now,
resting on exactly 3 remaining lemmas, all `Admitted` with precisely
diagnosed (not vague) remaining gaps — see Section 11.

## 11. Current blocker: `extract_loc`/`eval_key_loc` divergence in the `ss`-indexed hybrid step

Interactively closing `KDF_hyb_KDF_hyb_EVAL_true_equiv`'s case tree
against the `ss`-indexed redesign succeeded for **every branch except
one**: all "idx already known" branches (`< i`, `= i`, `> i`), and the
"freshly discovered, new idx `< i`" and "new idx `> i`" branches, close
cleanly with the invariant as originally stated (`heap_ignore
[fmap eval_key_loc]` plus the usual `extract_loc`/`ss_index_loc`
bookkeeping conjuncts).

**The one remaining branch is exactly the one the whole redesign was
aimed at**: a brand new `ss` whose freshly-assigned index equals `i` —
the ONE time this can ever happen, for a fixed `i`. There, the LHS
(`KDF_hyb i`'s "else"/real-PRF branch) samples fresh `prk` and writes
`extract_loc := setm T ss prk`, while the RHS (`KDF_hyb_EVAL i`
composed with `EVAL true`) instead calls the imported `eval`, which
samples into `eval_key_loc` and never touches `extract_loc` for this
(or any later) query. From this point on, `extract_loc`'s LHS and RHS
copies **permanently, genuinely differ** (the LHS map gets an entry at
this one `ss`; the RHS map never will) — so `heap_ignore [fmap
eval_key_loc]`, which claims `extract_loc` agrees as a WHOLE map on
both sides forever, becomes false exactly at this step. This is a
structural fact about the redesign, not a proof-search failure — no
amount of tactic cleverness closes a false invariant.

**The fix (diagnosed, not yet carried out)**: exclude `extract_loc` from
the `heap_ignore` set and add a fifth invariant conjunct recording the
weaker fact that actually holds:
```coq
rel_app [:: (lhs, ss_index_loc); (lhs, extract_loc); (rhs, extract_loc)]
  (fun SIdx T T' => forall ss0, SIdx ss0 <> Some i -> T ss0 = T' ss0)
```
i.e. the two copies of `extract_loc` agree pointwise at every `ss0`
*except possibly* the one (at most one, ever) with index exactly `i`.
The newly-discovered-`ss`-at-`i` branch re-establishes this easily
(its own hypothesis excludes the very key that changed). The knock-on
cost: every OTHER branch currently reading `extract_loc` via the
convenient shared `r_get_vs_get_remember` (which demands a single
`ProvenBy (syncs extract_loc) _`, i.e. literal map equality) needs
redoing with `r_get_remember_lhs` + `r_get_remember_rhs` separately,
deriving the needed per-key equality from the new conjunct instead
(trivial when the queried `ss'` provably has index `<> i`, which every
such branch already establishes via its own case split). Mechanical,
but touches the whole case tree, not a small patch.

**`KDF_hyb_KDF_hyb_EVAL_false_equiv`** (composing `KDF_hyb_EVAL i` with
`EVAL false` instead — the mirror-image lemma needed for the "ideal"
half of the hybrid step, matching `PRFPRG.v`'s `GEN_GEN_HYB_EVAL_equiv`)
is blocked by exactly the same root cause (there: the LHS's `eval` call
samples into `eval_key_loc` while the RHS's real-Extract branch would
have sampled into `extract_loc` instead, for that one `ss`).

**`COUNT_KDF_hyb_q_KDF_mid_equiv`** (`AdvantageE (COUNT q ∘ KDF_hyb q)
(COUNT q ∘ KDF_mid) A = 0` — the fact that past the `q`-th distinct
shared secret, `KDF_hyb q` and `KDF_mid` agree exactly, no probability
reasoning needed) is a *different* remaining gap: it needs the same
adversary-code-induction technique `Pr_bad_adv_bound` (Section 10a)
already carries out for the birthday step — tracking `count_loc`/
`ss_count_loc` together through `code_link` to show a `COUNT
q`-bounded adversary can trigger `get_ss_idx`'s fresh-index branch at
most `q` times total, hence every `idx` ever handed out is `< q`, hence
`KDF_hyb q` never takes its "idx >= q" branch. Not yet carried out, but
should follow `Pr_bad_adv_bound`'s established pattern closely.

`Print Assumptions security_of_KDF` confirms these are the ONLY 3
non-standard dependencies of the entire top-level theorem.

## 12. Immediate next steps (where to resume)

1. **Rework `KDF_hyb_EVAL_inv`** per the diagnosed fix in Section 11
   (drop `extract_loc` from `heap_ignore`, add the "agree except
   possibly at index `i`" conjunct), then redo
   `KDF_hyb_KDF_hyb_EVAL_true_equiv`'s case tree against the new
   invariant (mechanical but touches every branch, not just the
   previously-blocked one).
2. **`KDF_hyb_KDF_hyb_EVAL_false_equiv`**: same invariant rework,
   mirroring `PRFPRG.v`'s `GEN_GEN_HYB_EVAL_equiv` for the proof
   technique.
3. **`COUNT_KDF_hyb_q_KDF_mid_equiv`**: an adversary-code induction
   mirroring `Pr_bad_adv_bound`'s technique (Section 10a), tracking
   `count_loc` and `ss_count_loc` together.
4. Once all three are `Qed`'d, `KDF_real_KDF_mid_bound` and
   `security_of_KDF` become unconditional (they're already assembled
   and `Qed`'d modulo exactly these three facts) — at that point the
   entire multi-month effort (up-to-bad infrastructure, the birthday
   bound, and the dynamic-key hybrid argument) is complete, and the
   standing "don't commit yet" instruction can finally be revisited.

## 13. Session 2026-07-25: all gaps closed — zero admits in HKDF.v

Both remaining `Admitted`s are gone; `security_of_KDF` is now
unconditional (modulo the library's pre-existing
`__admitted__interchange_psum` in `pkg_upto_bad.v` and the standard
`Axioms.v`/mathcomp-analysis axioms — re-confirmed by
`Print Assumptions` on both `security_of_KDF` and
`KDF_real_KDF_mid_bound`).

**`COUNT_KDF_hyb_q_KDF_mid_equiv`: proved, and Section 11/12's
diagnosis was wrong in a useful way.** No adversary-code induction is
needed: the `COUNT` wrapper *materializes* the run-length in the heap
as `count_loc`, so a per-call `eq_rel_perf_ind` invariant suffices —
`heap_ignore [ss_count_loc; ss_index_loc] ⋊ rel_app` carrying
`ss_count_loc <= count_loc` plus "every stored index < ss_count_loc"
(`KDF_hyb_q_mid_inv`). One subtlety: the fresh-`ss` branch needs the
*transient* pre-increment bound, carried as an explicit existential
plus standalone `preserve_update_mem` step lemmas
(`KDF_hyb_q_mid_inv_count_step` / `_fresh_ss_step`), because
`ssprove_restore_mem`'s folding only recognizes `rem_lhs`/`rem_rhs`
shapes. Helper: `COUNT_KDF_hyb_q_KDF_mid_perf`.

**`KDF_hyb_KDF_hyb_EVAL_false_equiv`: deleted, not proved — it was
FALSE as stated** (the counterexample analysis is retained as the long
docstring above `get_prk_bad`). Section 12's plan 2 (invariant rework
mirroring `GEN_GEN_HYB_EVAL_equiv`) cannot work: no invariant fixes a
false statement. Instead the EVAL-false leg of each hybrid hop is now
an **up-to-bad step**, replaying the step-2b/2c recipe per hop:

- `get_prk_bad` = `get_prk` + `KDF_mid'`'s verbatim
  `used_prk_loc`/`bad_loc` collision bookkeeping (bad_id 4 reused).
- `KDF_hyb_bad j` = instrumented `KDF_hyb j`;
  `KDF_hybE_bad i` = monolithic inlining of
  `KDF_hyb_EVAL i ∘ EVAL false` whose `idx == i` branch ghost-extracts
  the index-`i` `ss` (output-dead, but keeps both sides' bookkeeping
  identical — the key trick that lets `bad_loc` stay synced across the
  EVAL abstraction boundary).
- Chain per hop: `KDF_hybE_bad_equiv` (perfect, invariant
  `hybE_inline_inv` incl. "unindexed ⇒ unextracted") →
  `KDF_hybE_bad_KDF_hyb_bad_bound` (Fundamental Lemma via
  `KDF_hybE_bad_eq_up_to_bad`, invariant `KDF_hybE_bad_inv`:
  `heap_ignore [mid_loc; eval_tbl_loc]` only — all shared bookkeeping
  stays *equal* even post-bad, so the whole per-call proof is one
  coupled walk, no independent/lossless coupling anywhere; the gated
  `rel_app` carries `hyb_tbl_match` linking `eval_tbl_loc` to the
  `(prk_i, ·)` slice of the RHS `mid_loc`) → `KDF_hyb_bad_KDF_hyb_equiv`
  (ghost erasure). Assembled as `KDF_hyb_EVAL_false_bound`:
  `AdvantageE (KDF_hyb_EVAL i ∘ EVAL false) (KDF_hyb i.+1) A
   <= Pr_bad (A ∘ KDF_hybE_bad i) 4 true`.
- Counting: `Pr_bad_adv_bound_hybE` (mirror of `Pr_bad_adv_bound`,
  factored via generic `Hprk`/`Hmid`/`Heval` continuation facts;
  needed `setoid_rewrite bind_assoc` to reassociate under `raw_code`
  binders) → `Pr_bad_COUNT_KDF_hybE_bad_bound`:
  per hop `<= birthday_bound q` under `COUNT q`.

**Final theorem (new shape):**
```coq
AdvantageE (COUNT q ∘ KDF_real) (COUNT q ∘ KDF_ideal) A <=
  (\sum_(i < q) prf_epsilon ((A ∘ COUNT q) ∘ KDF_hyb_EVAL i))
  + q%:R * birthday_bound q   (* per-hop up-to-bad, coarse event *)
  + birthday_bound q.         (* step-2 birthday, unchanged *)
```
Deliberate looseness: the per-hop bad event is the COARSE "any Extract
collision" (maximal reuse of the KDF_bad machinery), costing
`q * birthday_bound q` = Θ(q³/N). Two documented tightening options,
decided against for this pass (user chose coarse):
(a) restrict the event to "collides with prk_i" → Θ(q²/N) explicit
term, at the cost of a bespoke two-phase counting induction;
(b) re-index hybrids per-`ss` (per-ss ideal tables) → *perfect* hops,
no explicit birthday term at all (the q²/N migrates inside the
reductions' `prf_epsilon` via key-collision testing), but takes
`KDF_mid`/`KDF_bad`/Birthday off the main path.

Proof-engineering notes that materially helped (beyond
`ROCQ_MCP_SESSION_NOTES.md`): residual `x ← ret v ;; k` after `case:`
on a `getm` match needs a bare `simpl.` per branch per side;
`r_put_lhs/rhs` preconditions must be literal `fun '(a,b) => …`
pair-patterns (reshape via `rpre_weaken_rule`); reassemble `⋊`-stacked
invariants with `split`, never `conj` (`simpl never`); factoring
repeated per-branch arguments into standalone step/"dance" lemmas
(`KDF_hybE_bad_prk_dance`/`_mid_dance`/`_owner_dance`) beats literal
transcription — the eq-up-to-bad proof landed at ~758 lines + helpers.

File: 7397 lines, compiles clean under `make -f Makefile.rocq`,
`grep Admitted\.|admit\.` returns nothing. Not yet committed (standing
instruction); ready for commit review.
