# Changelog

All notable changes to nix-effects are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.8.0] - 2026-04-17

A macro layer for user-defined datatypes lands on top of the kernel's description universe. Declaring an inductive type now means naming its fields; the macro compiles them to descriptions, flattens saturated and linear-recursive constructor chains to flat `desc-con` terms at elaboration time, and threads type parameters through a plain Π-binder so universe-typed components sit at the outside of the definition. `Nat`, `List`, and `Sum` are rebuilt through this surface. The category-theory example library is rewritten as a five-chapter guided tour that uses exactly the same macros users have.

### Added

- **Datatype macro layer** (`fx.types.hoas.datatype` / `fx.types.hoas.datatypeP` + `field`, `fieldD`, `piField`, `piFieldD`, `recField`) — declarative HOAS surface for single- or multi-constructor inductive types. Dependent fields receive a `prev` marker map so later fields reference earlier ones by name; `datatypeP` parameters thread through a `paramPi` (plain Π) binder, outside the description's `descArg`; duplicate constructor names and zero-constructor datatypes are rejected eagerly
- **Constructor-chain flattening at elaboration** — saturated (all-data) and linear-recursive (data-fields then one `rec`) shapes flatten to a single `desc-con` Tm (or a `genericClosure`-walked pyramid for the recursive shape). Deeply nested constructor applications (5000+ cons cells, 5000+ succs) type-check without blowing the C++ stack. Non-flattenable shapes fall through to the ann-wrapped λ-cascade path and behave identically to the pre-macro spelling
- **`W`-type datatype macro** — self-application inside `datatypeP` for M-like datatypes (`W A P` with `A : U₀`, `P : A → U₀`, `sup : Π a. (P a → W) → W`)
- **Dependent-field laws in the macro surface** — `fieldD`'s type function receives the full `prev` marker map, so associativity laws reference `prev.op`, category laws reference `prev.id` / `prev.comp`, etc. No projection chains
- **Category-theory library rewritten as a guided tour** — five chapters that build on each other:
  - `combinators.nix` — `sym`/`trans`/`cong` from J.
  - `arithmetic.nix` — `add` with seven verified properties.
  - `algebra.nix` — `Monoid` and `Category` as macro datatypes; instances `natAddMonoid`, `natCategory`; `compComm` stated categorically through `natCategory.comp`.
  - `functor.nix` — `MonoidHom` and `Functor` as macro datatypes; doubling packaged as both `doubleHom` (monoid homomorphism) and `doubleFunctor` (endofunctor on `natCategory`).
  - `yoneda.nix` — Yoneda's lemma as an equivalence of types.

### Changed

- **`Nat`, `List`, `Sum` use the macro surface for their µ/ctor/elim construction** — their HOAS forwarding stays unchanged from the user view; internally they flow through `datatype` / `datatypeP`, so every test-suite improvement on the macro improves the kernel primitives too
- **`apps/category-theory/algebra.nix`** — old nested-Σ `MonoidOf` / `CategoryTy` encoding replaced by macro datatypes. `natAddMonoid` and `natCategory` are exposed as HOAS records carrying both the component HOAS terms (`.op`, `.e`, `.comp`, …) and the bundled `(ty, impl)` pair that the kernel checks
- **Example-library invocations** — README and apps use `nix eval` rather than `nix-instantiate --eval --strict`

### Documented

- **`desc-arg` universe rule** — a principled note at check.nix's `desc-arg` rule explains why `S : U 0` is required, the parameter-lifting idiom that threads universe-typed components through `datatypeP` parameters, and that the category-theory library currently encodes `Obj` / `Hom` as parameters specifically because of this rule

## [0.7.0] - 2026-04-16

Six upstream PRs land alongside a kernel-level description universe. From @vic: Kyo-style handler rotation and a `scope` module for lexically scoped handlers (#8), `bind.*` operators for attrset/computation/function composition (#12), an `isComp` predicate on the computation ADT (#13), a first-class `state.update` (#15), and CI for pull requests (#16). From @sini (first contribution, landing via #14): effectful-resume handlers that can reply with a computation and have its effects spliced into the continuation. Thanks to both.

On the kernel side, `Desc` and `μ` join as primitives, and `Nat`, `List`, `Sum`, and `Unit` are rebuilt as HOAS descriptions on top — so further inductives can be added as ordinary data rather than new kernel nodes. Σ-η and ⊤-η conversion rules are added. A follow-up fix (`effectRotateSlow` now splices computation resumes correctly; see Fixed) closes a bug found during review of #14.

### Added

- **Kyo-style handler rotation** (`fx.rotate`) — handles matching effects and rotates unknown ones outward so an enclosing handler can resume them. Implements the law `handle(t1, suspend(t2, i, k), f) = suspend(t2, i, x → handle(t1, k(x), f))`. Credit: @vic (#8)
- **Scoped handlers** (`fx.effects.scope`) — `scope.run` installs handlers for a subcomputation and hides the scope's internal state, `scope.runWith` exposes it, and `scope.stateful` threads caller state across rotation. Credit: @vic (#8)
- **Effectful-resume handlers** — a handler may return a computation as its `resume` value; its effects are spliced before the pending continuation. Fast path uses `resumeCompOrValue` which dispatches on whether the resume is a computation. Credit: @sini (#14)
- **Description universe in the kernel** — `Desc` and `μ` as kernel primitives, with strict positivity guard, HOAS descriptor pieces (`descArg`, `descRec`, `descPi`, `descRet`), `descElim`/`descInd` elimination, and `interpHoas` for description interpretation
- **Nat/List/Sum/Unit rebound as HOAS descriptions** — kernel representations live entirely in the description universe; no dedicated kernel nodes for each type
- **Σ-η and ⊤-η conv rules** — `pair (fst p) (snd p) ≡ p` for Sigma and `tt ≡ _` for Unit, at the kernel conversion level
- **`bind.*` operators** — `bindAttrs`, `bindFx`, `bindFn` for monadic composition over attrset projections, computations, and Kleisli arrows. Credit: @vic (#12)
- **`state.update`** — effectful state transformer obeying `get >>= f >>= ({s, v}: put s >> pure v)`. Credit: @vic (#15)
- **`isComp`** — tag-based predicate on the computation ADT boundary. Credit: @vic (#13)
- **Pull-request CI** (`.github/workflows/flake-check.yml`) — runs `nix flake check -L` on PR events. Credit: @vic (#16)
- **CI and release badges** on the README

### Fixed

- **`effectRotateSlow` now splices computation resumes correctly.** When the depth ≥ 500 fast-to-slow threshold was crossed and a handler returned a computation as its `resume`, the slow path previously used `resumeWithQueue`, which treats the resume as a plain value. For the common case of an Identity continuation queue this wrapped the computation in `pure`, short-circuiting the loop with the inner effects unrun. Swap to `resumeCompOrValue` to match the fast path. Regression test: `effectRotationSlowPathEffectfulResume`.

### Changed

- **README** — rewritten intro, new `## Features` section covering effects-layer and MLTT kernel capabilities, old "No handler layering" limitation removed (superseded by `fx.effects.scope`), old "single source of truth" paragraph refocused on the real underlying limitation (`Certified` carries a Boolean witness, not an inhabitation proof)

## [0.6.0] - 2026-04-14

### Added

- **Opaque lambda** (`mkOpaqueLam`) — trust boundary for negative types (Pi). The kernel verifies domain match but cannot reduce the body. Follows the axiomatized literal pattern (`mkFnLit`/`mkAnyLit`). Conv uses `_fnBox` wrapper for thunk-identity comparison
- **Verified combinators** (`src/tc/verified.nix`) — `fn` combinator produces values carrying both a Nix callable (`__functor`) and an HOAS body (`_hoasImpl`). The kernel type-checks the full body, not just domain
- **Pi elaboration** — `elaborateValue` handles Pi types: verified values use `_hoasImpl` directly, raw Nix functions wrap in opaque lambda. `extractInner` returns Nix functions from `VOpaqueLam` and `VLam`
- **HOAS substitution for dependent Sigma** — `elaborateValue` Sigma case uses `body(â)` for correct dependent type computation, replacing the sentinel test heuristic
- **`_kernelPrecise` / `_kernelSufficient`** — orthogonal decomposition of the old `_kernelExact`. `_kernelPrecise` drives parent kernel building; `_kernelSufficient` drives guard decisions. Constructors compose both independently
- **`.diagnose` method** on all types — returns `{ kernel; guard; agreement; }` for independent kernel/guard reporting
- **Category theory library** (`apps/category-theory/`) — formally verified proofs running at Nix eval time. Proof combinators (sym, trans, cong) derived from J elimination; natural number arithmetic with 7 verified properties including commutativity; Monoid and Category as dependent sigma types with (Nat,+,0) instances; commutativity of composition in the endomorphism monoid; doubling endofunctor with functoriality proof via 5-step equational rewriting
- **Cross-cutting integration tests** — Record(Pi, Sigma(refined)), Maybe(DepRecord(dependent ListOf)), ListOf(Pi), Either(Sigma, Pi) verifying conjunction across compound types

### Changed

- **Universal conjunction** — every type with a guard uses `kernelDecide ∧ guard`. Replacement mode removed entirely from `effectiveCheck`
- **Polarity-aware elaboration** — positive types (Sigma, Sum, Nat) elaborate structurally; negative types (Pi) elaborate opaquely
- **Pair syntax** — `mkPair` is now 2-arg (Curry-style), removing the vestigial Church-style annotation that no computational layer maintained. Pair inference case removed from `check.nix`; use `Ann` for synthesis
- **Pi guard removed** — Pi with `kernelType` sets `guard = null`; opaque lambda domain check subsumes `isFunction`
- **Refined types** set `approximate = false`, enabling parent constructors to build precise kernels from refined children under conjunction
- **Constructor composition** — `Record`, `ListOf`, `Maybe`, `Either`, `Variant` split decisions into `allPrecise` (kernel building) and `allSufficient` (guard propagation)
- **DepRecord** `buildSigma` uses `_kernelPrecise` for precise nested Sigma kernels on non-dependent fields

### Removed

- `_kernelExact` — replaced by `_kernelPrecise` / `_kernelSufficient` with no backward-compatibility shim
- Replacement mode in `effectiveCheck` — all types use conjunction
- Pair inference case in `check.nix` — introduction forms check, not synthesize

## [0.5.2] - 2026-04-13

### Fixed

- **Soundness: refined type composition** — `refine`/`refined` exposed `_kernel` without marking themselves approximate, allowing `Maybe`/`Either` to bypass refinement predicates via the weaker kernel. `Maybe (refined "Nat" Int (x: x >= 0)).check (-1)` returned `true`. Fixed via Galois connection model: `_kernelExact` separates kernel availability from sufficiency, dual-mode conjunction/replacement semantics in `mkType`
- **`elaborate.decide` totality for records** — `elaborateValue` record case did raw `v.${field}` access without checking field presence. Missing-attribute errors are uncatchable by `builtins.tryEval`, making `decide` crash instead of returning `false`. Fixed with safe `fieldOf` helper

### Added

- `_kernelExact` field on all types — `true` when the kernel alone is sufficient for correct checking (no guard residual needed)
- `Record` per-field blame tracking via custom `verify` — delegates to each field type's `.validate` for recursive decomposition (context: `Record{age, name}.age`)
- `Variant` per-branch blame tracking via custom `verify` — delegates to active branch's `.validate`
- Composition soundness tests: deep composition, kernel-exact propagation, chained refinements, adequacy property

### Changed

- Type constructors (`Record`, `ListOf`, `Maybe`, `Either`, `Variant`) use `_kernelExact` instead of `? _kernel` for guard decisions and set explicit `approximate` flags
- `_kernel` is now always exposed on all types as the best kernel approximation; `kernelCheck` and `prove` remain gated on `!isApproximate`
- `Pi` without explicit `kernelType` omits redundant `isFunction` guard (conjunction with `kernelDecide` handles it)
- Locked nixpkgs via `nixpkgs.nix` for deterministic non-flake builds (@vic, kleisli-io/nix-effects#9)

## [0.5.1] - 2026-04-13

### Changed

- `Justfile`: `just test` now accepts an optional suite argument (`just test <suite>`) to selectively run a single test suite instead of all tests (kleisli-io/nix-effects#11, contributed by @vic)

## [0.5.0] - 2026-04-12

### Added

- `comp.nix`: Computation ADT module — single source of truth for `Pure`/`Impure` construction and elimination via `pure`, `impure`, `isPure`, and `match`. All modules now use these constructors instead of raw `_tag` attrset literals (closes #7)
- `kernel.pipe`: chain a computation through Kleisli arrows, threading results via bind (closes #6)
- `kernel.kleisli`: Kleisli composition `(a -> M b) -> (b -> M c) -> (a -> M c)`
- `queue.identity`: sentinel variant representing the identity continuation, letting the trampoline skip queue application for bare `send` effects
- Benchmark infrastructure: `nix run .#bench` / `nix run .#bench-compare` with named history, 3-run median, and comparison tables
- Benchmark apps: expression interpreter (`apps/interp`) and dependency graph evaluator (`apps/build-sim`) with scalable workload generators
- Benchmark stress tests: effectHeavy, bindHeavy, mixed, rawGC microbenchmarks for diagnosing bottlenecks
- Per-module test result reporting in `tests` output

### Changed

- Trampoline interpreter processes continuation queues inline via recursive `applyQueue` (depth-limited to 500, with genericClosure fallback for deep pure chains), keeping 1 genericClosure step per effect — 78% faster on effectHeavy 100k, 72% faster on mixed 100k vs 0.4.0
- `send` uses Identity queue instead of `singleton pure`, eliminating one wasted identity continuation application per effect
- `queue.viewlGo` fast-path: returns immediately when left child is already a Leaf, skipping genericClosure entry for the common case
- `queue.snoc` and `queue.append` handle Identity variant transparently
- All source modules migrated from raw `{ _tag = "Pure"; ... }` / `{ _tag = "Impure"; ... }` literals to `comp.pure` / `comp.impure` constructors, and from `._tag == "Pure"` checks to `comp.isPure`
- README and book reframed around the effect layer as the primary abstraction; removed Fire Triangle framing
- Book: trampoline guide updated to use `isPure`

### Fixed

- `build.materialize`: step-script env test matched exact quoting instead of presence

### Removed

- `examples/typed-derivation.nix` and the proof-gated derivation showcase wired through it. The example was contrived (the same policy is expressible with `assert`) and did not reflect how the library is actually used. The `api-server` package output and the book's "Proof-gated derivations" section in the Proof Guide are removed along with it. The `v.verify` verified-extraction pipeline it demonstrated is still available and documented in the remaining `examples/` and in the Proof Guide.

## [0.4.0] - 2026-04-06

### Changed

- **Breaking:** `mk`-wrapped functions are now directly callable, removing the need for `.value` (@vic, #1)
- Test extraction produces nested attrsets instead of flat dotted keys, enabling targeted `nix-unit` runs (@vic, #5)

### Added

- `CONTRIBUTING.md` explaining the josh mirror workflow
- `shell.nix`, `Justfile`, `tests.nix` for non-flake dev workflow (@vic, #4)

### Removed

- Unused flake inputs (@vic, #3)

## [0.3.0] - 2026-02-27

### Added

- Effects-powered build module (`fx.build`): typed build steps, eval-time validation, and derivation materialization
- `fx.build.BuildStep` and `fx.build.BuildPlan` Record types for describing build pipelines
- `fx.build.plan`: eval-time validation pipeline that type-checks steps and filters conditional steps via `when` predicates, collecting all errors without throwing
- `fx.build.materialize`: converts a validated BuildPlan + pkgs into a `pkgs.runCommand` derivation with per-step env isolation, source copying, and shell generation

## [0.2.0] - 2026-02-27

### Added

- Typed pipeline framework (`fx.pipeline`): composable stages with `mkStage`, `compose`, and `run`, wiring reader, error, acc, and typecheck effects with typed boundaries between stages
- Pipeline convenience re-exports: `ask`, `asks`, `raise`, `raiseWith`, `warn`, `pure`, `bind`, `map` for use inside stage transforms
- 14 inline tests and 2 integration tests for the pipeline module

## [0.1.0] - 2026-02-25

Initial release.

### Added

- Freer monad core with FTCQueue (O(1) bind) and `genericClosure` trampoline (O(1) stack depth)
- MLTT type-checking kernel (`src/tc/`) with bidirectional type checking and normalization by evaluation
- HOAS elaboration bridge between Nix values and kernel terms
- Verified computation layer: prove functions total, extract certified Nix functions from proof terms
- Proof-gated derivation builder: reject invalid configs at `nix eval` time via kernel proof obligations
- Primitive types: String, Int, Bool, Float, Attrs, Path, Function, Null, Unit, Any
- Compound type constructors: Record, ListOf, Maybe, Either, Variant
- Dependent types: Pi, Sigma, Certified, Vector, DepRecord
- Refinement types with predicate combinators: `refined`, `allOf`, `anyOf`, `negate`, `positive`, `nonNegative`, `inRange`, `nonEmpty`, `matching`
- Linear types: Linear, Affine, Graded
- Universe hierarchy: `typeAt n` for arbitrary levels, convenience aliases Type_0 through Type_4
- Algebraic effect handlers: state, error, reader, writer, acc, choice, conditions, typecheck, linear
- Handler `resume`/`abort` distinction for continuation control
- Effectful lazy streams: `fromList`, `iterate`, `range`, `replicate`, `map`, `filter`, `scanl`, `take`, `takeWhile`, `drop`, `fold`, `toList`, `length`, `sum`, `any`, `all`, `concat`, `interleave`, `zip`, `zipWith`
- `adapt` and `adaptHandlers` for handler state composition
- `mk { doc, value, tests }` structured module pattern with inline documentation and tests
- `extractDocs` for per-module API markdown generation
- Flake with lib, tests, packages, and checks outputs
- nix-unit integration for `nix flake check`
- Documentation: 8 book chapters (introduction, getting started, proof guide, theory, trampoline, systems architecture, kernel architecture, kernel formal specification)
- Examples: equality proofs, proof basics, typed derivation, verified functions
- MIT license
