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
did not have this piece, so most of this session has been building it
from scratch as reusable infrastructure, alongside the concrete example
that needs it.

## 2. Status at a glance

| Piece | File | Status |
|---|---|---|
| Birthday-bound combinatorics | `theories/Crypt/examples/Birthday.v` | Proved, 0 admits |
| Hop 1 of hybrid chain (`KDF_real_KDF_hyb0_equiv`) | `theories/Crypt/examples/HKDF.v` | Proved, 0 admits |
| Hop 2 of hybrid chain (`KDF_hyb_KDF_hyb_EVAL_true_equiv`) | `theories/Crypt/examples/HKDF.v` | 3 of 4 leaves proved; 1 leaf `admit`ted with a detailed comment (needs up-to-bad) |
| Hop 3 of hybrid chain | `theories/Crypt/examples/HKDF.v` | Not started |
| `KDF_mid_KDF_ideal_bound` (the birthday connection) | `theories/Crypt/examples/HKDF.v` | `Admitted` stub only; not started beyond the pure-math result in `Birthday.v` |
| Final assembly `KDF_real_KDF_mid_bound` | `theories/Crypt/examples/HKDF.v` | Not started |
| Up-to-bad semantic core (`pr_up_to_bad`) | `theories/Crypt/rhl_semantics/only_prob/UpToBad.v` | Proved, 0 admits |
| Independent/product coupling (`indp`, `indp_lmg`, `indp_rmg`, `indp_coupling`) | same file | Proved, 0 admits |
| Heap-generic losslessness for `raw_code` (`Pr_code_lossless`) | `theories/Crypt/package/pkg_lossless.v` | Proved, 0 admits — **but see Section 6, it's in the wrong "vocabulary" for what's needed next** |
| `independent_rule` (combine two unary facts into a relational judgement) | `theories/Crypt/rules/UpToBadState.v` | Proved, 0 admits |
| `eq_up_to_bad` (the relaxed up-to-bad invariant machinery, mirroring `eq_up_to_inv`) | — | **Not started** — this is the current frontier |
| Adversary-linking induction for `eq_up_to_bad` | — | Not started (blocked on the above) |
| RUN-wrapper to state `Pr[bad]` in `AdvantageE`'s vocabulary | — | Not started, no existing template |
| Top-level Fundamental Lemma (`AdvantageE p0 p1 A <= Pr[bad]`) | — | Not started |

All committed/pushed work compiles cleanly via the project's real build
(`make -f Makefile.rocq <file>.vo`), verified independently of the IDE
(see Section 8, "tooling gotchas" — the IDE's own diagnostics are
unreliable in this environment).

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

## 4. Design of the up-to-bad construction

The plan has three parts, of which the first two are done:

### 4a. Semantic core — DONE (`UpToBad.v`, section `UpToBad`)

Pure probability-theory statement, no packages/pRHL/adversaries
involved. Given:
- two distributions `d0`, `d1` on the same outcome type `T`,
- a coupling `d` of them (`dfst d = d0`, `dsnd d = d1`),
- a `bad : pred T` that's "synced" across the coupling's support
  (`d (x,y) > 0 -> bad x = bad y`),
- an `event : pred T` that agrees across the coupling's support outside
  of `bad` (`d (x,y) > 0 -> bad x = false -> event x = event y`),

then `pr_up_to_bad : `|\P_[d0] event - \P_[d1] event| <= \P_[d0] bad`.
Proved via pointwise bounds (`AG_bound`/`BG_bound`/`GH_eq`) collapsed
through `psum`/marginal lemmas (`A_collapse`/`B_collapse`/`G_collapse`/
`H_collapse`) and `pr_bad_sync`. **0 admits.**

### 4b. Independent (product) coupling — DONE (`UpToBad.v`, section `IndependentCoupling`)

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
`Admitted`s, scoped to a globally-fixed `R`). **0 admits.**

### 4c. Lifting through the relational program logic — IN PROGRESS

This is the genuinely hard, still-open part. Plan:

1. **`independent_rule`** (state-level: combine two *separately proved*
   unary Hoare-style facts about `c1`/`c2` into a relational judgement
   `⊨⦃P⦄c1≈c2⦃Q⦄`) — **DONE**, see Section 5.
2. **`eq_up_to_bad`** — a relaxed version of `eq_up_to_inv`: instead of
   requiring `b₀=b₁ ∧ I` at every oracle call, require
   `I(s₀,s₁) ∧ (bad_loc-is-false → b₀=b₁)`, where `bad_loc` is a shared,
   monotone (write-once, false→true only) location folded into `I`
   itself (`I := bad synced ∧ (bad=false → BaseInv)`). **NOT STARTED.**
3. **Adversary-linking induction for `eq_up_to_bad`** — mirrors
   `eq_up_to_inv_adversary_link`'s structural induction on the
   adversary's `raw_code`, but at each oracle call must case-split on
   whether `bad` is already true *entering* that call:
   - **bad=false entering:** proceed with today's `subst`-based
     induction, using `eq_up_to_bad`'s per-op guarantee — this part is
     unchanged from `eq_up_to_inv_adversary_link`.
   - **bad=true entering:** the two sides may have *already diverged*,
     so there is no `a₀=a₁` to `subst`. Instead, use `independent_rule`
     to combine two *separate, unary* facts, one per side: "if bad is
     true entering this call, it stays true after" (monotonicity) and
     "this call's code is lossless" (needed for `independent_rule`'s
     product-coupling construction to be valid at all). This is the
     part still to be designed/proved.
   
   **NOT STARTED** (blocked, see Section 6 for the exact current
   snag).
4. **RUN-wrapper for `Pr[bad]`** — a way to state "the probability that
   `bad_loc` ends up true" in `AdvantageE`'s vocabulary (i.e. as
   `Pr[some package] true` for some package whose `RUN` operation reads
   `bad_loc` and returns it). No existing template found in the
   codebase; will need to be built from scratch. **NOT STARTED.**
5. **Top-level Fundamental Lemma**: `AdvantageE p₀ p₁ A <= Pr[bad]`,
   assembled from pieces 3+4 plus `pr_up_to_bad`. **NOT STARTED.**

## 5. `independent_rule` — the state-level lifting, done

`theories/Crypt/rules/UpToBadState.v`, fully proved, 0 admits. Statement
(lightly reformatted):

```coq
Lemma independent_rule
  { A1 A2 : ord_choiceType } { S1 S2 : choiceType }
  (c1 : FrStP S1 A1) (c2 : FrStP S2 A2)
  (P : (S1 * S2) → Prop) (Q : (A1 * S1) → (A2 * S2) → Prop)
  (Hlossless1 : ∀ s1, psum (θ_dens (θ0 c1 s1)) = 1)
  (Hlossless2 : ∀ s2, psum (θ_dens (θ0 c2 s2)) = 1)
  (HQ : ∀ s1 s2, P (s1, s2) →
    ∀ a1 s1' a2 s2',
      (0 < θ_dens (θ0 c1 s1) (a1, s1'))%R →
      (0 < θ_dens (θ0 c2 s2) (a2, s2'))%R →
      Q (a1, s1') (a2, s2'))
  : ⊨ ⦃ P ⦄ c1 ≈ c2 ⦃ Q ⦄.
```

I.e.: given `c1`/`c2` are each lossless from any starting state, and
given a purely *unary* argument that "if the precondition held, and
`c1` from `s1` can reach `(a1,s1')`, and `c2` from `s2` can reach
`(a2,s2')`, then `Q` holds of that pair" (note: this argument never
needs to relate `c1`'s and `c2`'s executions to each other — it's proved
by reasoning about each side's support *separately*), we get the full
relational judgement `⊨⦃P⦄c1≈c2⦃Q⦄`.

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
  notation/coercion registered by a plain, non-`Export`ed import.)
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
  GRing.mul0r Order.POrderTheory.ltxx`), branched with `{ ... }` braces
  rather than `-`/`+` bullets (bullets produced a confusing "Wrong
  bullet" error in this spot for reasons not fully tracked down —
  braces just worked).
- **`GRing.Theory`/`Order.POrderTheory` names need explicit
  qualification** unless `Import GRing.Theory.`/`Import
  Order.POrderTheory.` are added — the file only had `Import
  Num.Theory.`, so `mul0r`/`mulr0`/`ltxx` had to be written
  `GRing.mul0r`/`GRing.mulr0`/`Order.POrderTheory.ltxx` throughout.

## 6. Current blocker: two incompatible "denotational semantics" for `raw_code`

This is where work stopped and where the next session should resume.

`pkg_lossless.v`'s `Pr_code_lossless` (heap-generic losslessness for
`raw_code`) is proved in terms of **`Pr_code`**
(`theories/Crypt/nominal/Pr.v`), which interprets `raw_code` *directly*
via the `SDistr` relative monad (`SubDistr.v`'s `SDistr_bind`/
`SDistr_unit`), with per-constructor equations `Pr_code_ret`/
`Pr_code_get`/`Pr_code_put`/`Pr_code_sample`/`Pr_code_call` (`= dnull`)
and a `Pr_code_bind` commutation lemma.

But `independent_rule` (Section 5) — and hence anything using it, like
the planned `eq_up_to_bad` adversary-linking induction — is stated
against **`θ_dens (θ0 c s)`**, which interprets `raw_code` *indirectly*:
first translate to the free monad via `repr`
(`theories/Crypt/package/pkg_semantics.v:42-60`, using primitives
`retrFree`/`ropr`/`bindrFree` with `gett`/`putt`/`op_iota`), then
interpret that free monad via `θ0 := @unaryIntState S A` (state-
threading, `RulesStateProb.v:52`), then `θ_dens` turns the result into
an actual `SDistr`.

**These are two different encodings of "the same" semantics, and I
confirmed via a live proof-state check
(`Check (fun ... => erefl : Pr_code c h = θ_dens (θ0 (repr c) h))`)
that they are NOT definitionally equal** — `erefl` fails with "cannot
unify". So `pkg_lossless.v`'s lemma, as it stands, cannot be directly
plugged into `independent_rule`'s `Hlossless1`/`Hlossless2` hypotheses
for arbitrary package code (which is stated in `raw_code`/`Pr_code`
terms in HKDF.v, but needs to enter `independent_rule` in `θ_dens∘θ0∘
repr` terms).

**Two ways to resolve this, not yet attempted:**

(a) **Bridge lemma**: prove
`∀{A}(c:raw_code A)(h:heap), Pr_code c h = θ_dens (θ0 (repr c) h)`
by induction on `c`, matching `Pr_code_bind`'s five-case structure
against `repr`'s five-case structure plus whatever equations `θ0`/
`θ_dens` have for interpreting the primitives `ropr gett k` / `ropr
(putt s') k` / `ropr (op_iota op) k` / `retrFree x`. **Not yet
investigated** — I do not yet know the exact equations for how
`unaryIntState`/`θ0` interpret those three specific primitives (this is
what the aborted research-agent call in this session was about to look
up, in `StateTransformingLaxMorph.v` and around
`RulesStateProb.v:1429` (`θ_dens_vs_bind'`) and `RulesStateProb.v:1458`
/`1487` (`θ_dens_OF_θ0_sample_c_s0` / `θ_dens_OF_θ0_c_sample_s0`, which
look like relevant precedent but are stated at the free-monad-primitive
level, not the `raw_code`/`repr` level, so still need connecting).

(b) **Redo the induction directly**: skip `Pr_code` entirely and prove
losslessness (and, separately, monotonicity of `bad_loc`) directly
against `θ_dens∘θ0∘repr`'s own equations, mirroring
`pkg_lossless.v`'s proof technique (its `lossless_valid` inductive
predicate plus the `__admitted__interchange_psum` dlet-interchange
trick) but retargeted. This avoids needing a bridge lemma at all, at
the cost of redoing the same induction a second time in a different
vocabulary.

Both are viable; (a) is more reusable (a bridge lemma is broadly useful
elsewhere too, and keeps `pkg_lossless.v`'s existing work from being
"wasted"), (b) is more directly scoped to just what's needed. This
choice, plus the actual proof, is the immediate next step.

## 7. Design notes / facts established along the way (useful context, not yet acted on)

- `F_choice_prod_obj⟨C1,C2⟩ := (C1*C2)%type` (`ChoiceAsOrd.v:40-45`) —
  confirmed to be mathcomp's plain pair type, not a bespoke wrapper —
  BUT when it appears as the argument to `θ0`/`θ_dens`'s type family, it
  shows up wrapped in extra functor applications
  (`F_choice_prod_obj ⟨ ord_functor_id ord_choiceType A1,
  OrderEnrichedRelativeAdjunctionsExamples.mkConstFunc ord_choiceType
  ord_choiceType S1 A1 ⟩` rather than literally `F_choice_prod_obj⟨A1,
  S1⟩`) — these reduce to the same thing but aren't syntactically
  identical; this didn't end up mattering for `independent_rule`'s proof
  (unification handled it once `indp`'s implicit `T1`/`T2` were inferred
  from the actual values passed, rather than being pre-specified), but
  could resurface as a gotcha in future proofs about this type.
- `LosslessOp` (`pkg_distr.v:203-204`) is a **single-field `Class`**,
  which Rocq compiles as a transparent alias for the field's own type
  (`psum op.π2 = 1`) rather than a wrapping record — so a hypothesis
  `Hop : LosslessOp op` can be used directly as a term of type
  `psum op.π2 = 1` (e.g. via `rewrite -Hop`), no projection needed. This
  is NOT true for multi-field classes/records — don't assume it
  generalizes.
- `rewrite (lemma_with_hypotheses)` puts side-condition goals **before**
  the main (rewritten) goal, in the lemma's hypothesis order — confirmed
  both by reading an existing proof (`Pr.v`'s `Lossless_sample`, which
  chains five `1: tac.` bullets before finally handling the main goal
  unbulleted) and by directly inspecting the live goal list via
  `rocq_check` after `rewrite __admitted__interchange_psum` in
  `pkg_lossless.v`'s own proof (see that file's `Pr_code_lossless` for
  the resulting bullet order: two `1: ...` side-condition bullets, then
  the main goal).
- `nominal/Pr.v`, despite its directory name, is **not** a separate DSL
  — it imports and reuses the main `pkg_*` framework directly, and
  connects to `pkg_advantage.v`'s own `Pr`/`Pr_op` via `Pr_Pr_code`/
  `Pr_Pr_fst` (`Pr.v:87-92`, `152-157`) — but those bridge lemmas are
  only stated for the **empty starting heap** (`Pr_fst`/`Pr` are both
  hardwired to `emptym`), so they don't directly help with the
  heap-generic bridge needed in Section 6 either.
- `theories/Crypt/nominal/packages/HybridArgument.v` (and its sibling
  `TotalProbability.v`) already implements a **full, working hybrid-
  argument reduction** (`Adv_hybrid`, `Adv_hybrid_dep`, with a clean
  triangle-inequality sum over `q` hybrids) — but it's built on the
  **`nom_package`/renaming ("nominal") layer**, a different, higher-level
  DSL from the plain `ValidPackage`/`raw_package` layer HKDF.v is
  written against. It's a good precedent for how the *final* assembly
  step (`KDF_real_KDF_mid_bound`, induction on `i` + triangle inequality)
  should look, but is not directly reusable without a framework switch
  we're not planning to make.

## 8. Tooling notes

- **rocq-mcp is now fully working**, including the interactive tools
  (`rocq_start`/`rocq_check`/`rocq_step_multi`/`rocq_query`), after the
  user installed `coq-lsp` (bundled with `pet`) directly into the live
  `ssprove` opam switch. This *did* initially break the build (ppxlib/
  ppx_deriving/ppx_optcomp downgrade forced a mathcomp recompile,
  leaving stale/inconsistent `.vo` files) — exactly the risk flagged
  before the user did it — but a full clean rebuild (done by the user)
  fixed it, confirmed via `rocq_health` and a real `make` compile.
  `.mcp.json` (project-scoped MCP server config, hardcoded local paths)
  is **intentionally not committed** to the repo.
- **The IDE's own inline diagnostics are unreliable throughout this
  entire environment** (a separate, version-mismatched Rocq checker
  instance from the one rocq-mcp/`make` actually use) — they report
  bogus errors (stale `.vo` "bad version number", "cannot find
  all_ssreflect", phantom syntax errors) on nearly every edit. The
  established, correct workflow is to **always** verify via
  `mcp__rocq-mcp__rocq_compile_file` and/or real
  `make -f Makefile.rocq <file>.vo`, and ignore the IDE diagnostics
  entirely.
- Using the interactive MCP tools (`rocq_start` + `rocq_check` +
  `rocq_step_multi` + `rocq_query`) to inspect **live goal states** was
  far more effective than reasoning abstractly about tactic behavior —
  several of the trickiest bugs in this session (wrong bullet order
  after a conditional `rewrite`, the `indp` extra-arguments
  mis-elaboration, the missing `ord_choiceType` coercion import) were
  each diagnosed in one or two live queries after having spent much
  longer trying to reason about them from reading source alone. Prefer
  reaching for these tools early when a proof step's actual goal shape
  is uncertain.
- Mathcomp/ssreflect gotchas re-confirmed this session (see also
  Section 5's list): `lia`/`lra` don't work on mathcomp `nat`/
  `realType`; `case: (boolP P)`/`(eqVneq x y)`/`(ltnP x y)` views
  auto-substitute into the goal (a subsequent explicit `rewrite` of the
  same fact then fails with "does not match any subterm"); `have H :=
  lemma args` with an unpinned implicit `{R:realType}` can spuriously
  generalize over a fresh `t:realType` unless fully explicit (`@lemma R
  ...`) is used in both the term and any type ascription.

## 9. Immediate next step (where to resume)

Pick (a) or (b) from Section 6 and execute it:
- If (a): read `StateTransformingLaxMorph.v` and the definitions behind
  `ops_StP`/`ar_StP`/`unaryIntState` (`RulesStateProb.v:27-53`) to get
  the exact interpretation of `ropr gett k`/`ropr (putt s') k`/
  `ropr (op_iota op) k`/`retrFree x`, then prove the bridge lemma by
  induction on `raw_code`, using `repr`'s equations
  (`pkg_semantics.v:42-73`) plus `θ_dens`'s bind-distributivity
  (`θ_dens_vs_bind'`, `RulesStateProb.v:~1429`, exact statement not yet
  confirmed — read it first).
- If (b): mirror `pkg_lossless.v`'s `lossless_valid` inductive-predicate
  proof technique, but state and prove it directly for
  `θ_dens (θ0 (repr c) h)` instead of `Pr_code c h`, using whatever
  equations come out of the (a)-investigation anyway (so (a)'s research
  step is needed either way).

Once losslessness is available in the right vocabulary, proceed to:
`eq_up_to_bad`'s definition → its adversary-linking induction (case
split on `bad_loc` entering each oracle call, bad-false branch reusing
`eq_up_to_inv_adversary_link`'s structure, bad-true branch using
`independent_rule` + the bridged losslessness + a new monotonicity
hypothesis on `bad_loc`) → the RUN-wrapper for `Pr[bad]` → the top-level
Fundamental Lemma → apply to hop 2's blocked leaf and to
`KDF_mid_KDF_ideal_bound` → hop 3 → final assembly.
