# Lean formalization of the scheduling paper

This is the Lean 4 / mathlib formalization accompanying the manuscript in
`Exact-Deterministic-Ratios-Uniform-Testing-arXiv-source/`.  The current
submission bundle, including the paper's Lean-formalization appendix, is
`Exact-Deterministic-Ratios-Uniform-Testing-arXiv-source-with-Lean-appendix.zip`.
The similarly named archive without `with-Lean-appendix` is a legacy snapshot,
not the current submission package.

The project now checks substantially more than the initial static model:

- finite-cap and obligatory-testing instances, effective lengths, the exact
  offline optimum, shortest-first optimality, and pair accounting;
- deterministic transcript-only online semantics, adaptive oracles, freezing,
  timed execution, and the replay theorem;
- the Raw, AdaptiveThreshold, parameterized AdaptiveThreshold, hidden-stopping,
  and ForcedPrefixUTE constructions;
- all constants and algebraic identities defining the six-branch exact curve,
  including joins, continuity, and its global maximum;
- the maximum-density stationary threshold and sharp `4/3` fluid
  worst-case certificate for randomized obligatory testing, the cutoff-32
  sample learner with threshold closure, finite histogram concentration,
  good/fallback/bad-event accounting, and the explicit `20378` coefficient;
- a concrete transcript-only sampled learn/fallback strategy with a proved
  `2n+1` completion bound, a fully discharged operational expected-cost bound,
  and a finite Yao lower bound on actual `0/2` instances whose coefficient
  `4n/(3n+5)` tends to `4/3`;
- bounded obligatory-testing instance optimality for the literal
  growing-cutoff learner against every finite randomized completing test-only
  competitor, including an input-size-only parameter family and a checked
  vanishing error;
- bounded common-upper revealing-optimization instance optimality for the
  literal pilot-learned test/process/raw strategy against every finite
  randomized completing observed policy, again with an input-size-only
  vanishing error;
- the binary stopping scalar game, Zero-prefix interpolation, the full UTE
  endpoint game, and reduction from arbitrary feasible endpoint masses;
- harmonic finite sums and their limiting optimization;
- ordinary and capped bank potentials, exact local rewards, Taylor bounds,
  reachable-state telescoping, the complete finite cap-reserve remainder,
  and the plateau reduction;
- honest upper- and lower-bound assembly theorems over genuine fixed inputs.

The top-level theorem is
`SchedulingPaper.exact_ratio_main` in
`SchedulingPaper/MainTheorems.lean`.  It proves both advertised exact-ratio
directions unconditionally: for every positive finite cap it packages the
fixed-instance lower bound together with an actual deterministic strategy
for the matching size-asymptotic upper bound, and it does the same at the
obligatory-testing endpoint.  The internal lower- and upper-bound interface
records are filled by `VerifiedLowerBoundFinalAssembly` and
`UpperBoundFinalAssembly`; they are not premises of the theorem.

The source contains no `sorry`, `admit`, or project-defined `axiom`.

## Randomized analyses and proof status

The three randomized analyses are developed analytically before their Lean
formalization:

- `RANDOMIZED_UNKNOWN_MULTISET_PROOF.md` gives a completed self-contained
  proof of the exact asymptotic `4/3` ratio for obligatory testing against an
  oblivious adversary, without an announced multiset and without a bound on
  processing times. Its explicit finite guarantee is
  `E ALG <= 4OPT/3+20378 n^(7/4)`, equivalently
  `E ALG <= (4/3+40756 n^(-1/4))OPT`; the matching fixed binary instances give
  `4/3-O(n^(-1/2))`.
- `OPTIONAL_TWO_PHASE_PROOF.md` gives a completed self-contained proof of the
  bounded optional-testing instance-optimality theorem at the `n^2` scale:
  blind pilot, threshold-testing prefix, monotone tested medium block, YOLO
  block, and monotone tested high tail.  It includes the adaptive
  first-touch trace bijection, simultaneous predictable-urn bound, finite
  growing-grid transfer for arbitrary bounded multisets, matching finite
  implementation, empirical optimization, and the fixed-oblivious-labelling
  Yao wrapper.  Its uniform error is
  `O_L(n^(-1/6)*sqrt(log(n+2)))` after normalization by `n^2`.
- `STATIONARY_THRESHOLD_PROOF.md` is a supplementary stronger result for the
  announced obligatory model: its lower transfer is mean-sensitive and needs
  no bounded-support assumption, and the stationary policy is exactly
  finite `4/3`-competitive.  The universal unknown-multiset `4/3` proof does
  not depend on its general lower-transfer theorem.

`RANDOMIZED_COMMON_UPPER_INSTANCE_OPTIMAL_PROOF.md` is the standalone
analytic proof for the finite common-upper model with raw execution of length
`u`.  It derives the explicit fixed-distribution quadratic benchmark,
proves its announced-multiset lower envelope against every adaptive policy,
removes the announcement by a tested pilot sample, and identifies the
instance-specific asymptotic ratio `Phi_u(D)/Omega_u(D)`.  It also solves the
outer optimization over distributions, giving an explicit four-branch exact
randomized curve with global maximum `1.6257523846...`.  Both the
instance-optimal theorem and the exact curve are incorporated as separate
main sections of the manuscript.  Lean checks the scalar curve, the explicit
announced stationary-or-raw upper endpoint, and the randomized lower bound
end-to-end for literal transcript-only strategies: a generic operational
compiler, exact finite clairvoyant denominator, fixed-input weighted Yao
selection, and convergence of the finite coefficients to the curve.  Lean now
also checks common-upper instance optimality end to end: the raw-duration
observed semantics, completion-envelope lower transfer, fixed-placement Yao
selection, the shared raw-block benchmark, the pilot-learned operational
upper, the all-zero branch, and an input-size-only vanishing rate.

The obligatory analytic proof is complete. Lean checks its exact and
robust fluid certificates, maximum-density optimizer and sample-empty-bin
closure, quantization and histogram concentration, fallback and bad-event
analysis, explicit constants, a terminating transcript-only implementation,
the conditional and outer permutation averages, the concrete floor and
fourth-root parameters, and a matching finite Yao lower bound whose offline
expression is proved equal to the literal clairvoyant objective.
`RandomizedFourThirds.lean` exposes unconditional operational upper and lower
theorems; the lower theorem includes the generic compiler from every
terminating public-transcript `Online.Strategy` to its fair binary tree. Thus
Lean proves the exact asymptotic randomized ratio `4/3`.

The bounded obligatory instance-optimal theorem is now also assembled end to
end. `ObligatoryGrowingCutoffTrace`,
`ObligatoryGrowingCutoffOperationalUpper`, and
`ObligatoryGrowingCutoffConditionalOrder` identify and bound the actual
completion cost of the learned growing-cutoff transcript strategy.
`ObligatoryMaximumDensityTemplate`, `ObligatoryGrowingCutoffAnalytic`, and
`ObligatoryGrowingCutoffExpected` prove population-template optimality and the
uniform pilot upper bound. `ObligatoryGrowingCutoffBenchmark` aligns that
upper bound exactly with the rounded benchmark used by the arbitrary adaptive
test-only lower transfer and finite Yao selection. The positive- and
zero-mean branches are joined in `ObligatoryGrowingCutoffRates`, while
`ObligatoryGrowingCutoffUniversalRates` supplies one parameter family
independent of the input bound: with
`m=floor(sqrt(sixteenthRoot n))`, the same literal policy is within
`800 (L+3)^2/m` of every finite randomized completing test-only competitor
after normalization by `n^2`, and Lean proves that this error tends to zero
for each fixed `L`. This checked rate is deliberately slower than the sharper
rate derived in the manuscript.

`ObligatoryGrowingCutoffFourThirds` and `ObligatoryPaperAlgorithm` strengthen
this assembly for the literal parameter family printed in the paper:
pilot size `floor(n^(3/4))`, grid size `floor(n^(1/4))`, cutoff
`32+n^(1/20)`, and mesh equal to cutoff/grid size.  The same
`physicalGrowingRunCost` now has both the vanishing `4/3` worst-case export
`paperGrowingPolicy_four_thirds_multiplicative` and the bounded-multiset
comparison
`exists_fixedPlacement_paperGrowingPolicy_concrete_rate`.  The slower
`n^(1/32)` grid remains only an auxiliary discretization in the competitor
lower bound, not a second online policy.

The common-upper revealing instance-optimal theorem is likewise closed for
the literal compiled learner. `RevealingOptimizationRawObserved` records raw
completion durations in the observed trace;
`RevealingOptimizationObservedEnvelope` and
`RevealingOptimizationObservedAreaLower` turn every completing adaptive
observed policy into the same finite raw-block lower benchmark and use finite
Yao to select one placement before its private seed.
`RevealingOptimizationBenchmarkBridge` proves the exact fluid/grid quadratic
identity, constructs an integral quota close to the benchmark minimizer, and
bounds the learner by that benchmark with explicit quota, sampling, kernel,
and pilot terms. `RevealingOptimizationInstanceOptimal` joins both directions,
handles the zero-mean population by a completion-triangle lower bound, and
exports the direct comparison
`exists_fixedPlacement_compiled_le_randomizedCompetitor_concrete_rate`.
With `m=floor(n^(1/16))`, its normalized direct error is
`1000 (u+1)^2/m`; Lean proves this tends to zero for every fixed `u`.
This checked rate is intentionally slower than the manuscript rate.

For the optional proof Lean now checks the pointwise fractional-knapsack envelope, the
long-test area bound, classwise grid repair and integral-shift transfer,
one-/two-job finite kernel corrections, a `12(L+1)` histogram stability bound,
the uniform `O_L(n)` fixed-operation-word/product-law lemma (27a), and the
sampled empirical-minimization wrapper.  The finite
random-permutation development also proves policy-uniform predictable-urn
concentration for adaptive selected counts and bounded selected work via an
orthogonality/Chebyshev/checkpoint argument, with an explicit checked
`n=R^8` instantiation giving `4R^7` error and failure probability at most
`5/R` per category, plus a checked all-grid union regime `K<=S`, `S^2<=R`
whose joint failure and aggregate repair error both vanish.  Lean also has the correct actual-processing-time semantics for blind
jobs, including a separate full-information optional runtime in which blind
completion reveals the elapsed processing time, its relabelling/cost
accounting, and a literal randomized four-block transcript-only strategy.
The arbitrary adaptive first-touch order is now compiled by a finite trace
bijection into the predictable selector required by the urn bounds, including
policies that react to observed blind durations.  The optional proof now also
contains a common finite grid-template family, empirical minimization from a
uniform blind pilot, the actual-time finite canonical kernel, and a physical
blind-pilot compiler which deletes already completed pilot jobs from an
independent canonical word. `RandomizedOptionalUnknownInstanceOptimal` joins
this construction to the arbitrary-adaptive announced lower bound and proves
a finite unknown-multiset instance-optimal comparison with every error term
explicit. `RandomizedOptionalUnknownRates` instantiates all seven errors for
every `n >= m^16`: with `m` grid cells and inverse-power pilot, suffix, and
checkpoint parameters, the universal blind-pilot schedule is within
`7830 (L+1)^2/m` of every complete announced policy after normalization by
`n^2`. It separately discharges the zero-mean case for the same learned
algorithm, then sets `m=floor(n^(1/16))` and formally proves that the resulting
error tends to zero. Thus the full bounded unknown-multiset theorem now has a
literal input-size-only vanishing parameter family in Lean. The supplementary
announced proof has its fluid certificate checked.

## Build

The project is pinned to Lean and mathlib 4.30.0.

```sh
lake update
lake exe cache get
lake build
```

The root module `SchedulingPaper.lean` imports the complete development.

The manuscript additionally studies the blind-optimization model in which a
unit-time optimization changes a raw duration `u` to a hidden duration
`p <= u` without revealing `p` before execution.  Its deterministic
impossibility and exact curve, universal mean-sampling instance-optimal
policy, and exact oblivious-randomized curve are all formalized operationally,
including fixed-input Yao selection and the `sqrt(u)/2` asymptotics.

For revealing optimization, the announced fixed-threshold endpoint and the
finite binary-family lower bound are connected to literal online runs.  The
universal-policy development additionally contains the model-specific
learnable grid templates, their uniform histogram Lipschitz and empirical
minimization bounds, an executable mixed test/process/raw quota strategy with
proved termination and exact completion labels, and its bounded finite
random-placement pair kernel.  The canonical-trace layer now proves the
literal strategy's exact one- and two-label projection grammar and identifies
its completion cost exactly with that kernel (including stable SPT ties).
The finite kernel is in turn connected to the empirical fluid objective with
an explicit normalized `(5u+8)/(2n)` error.  The same bridge compiles finite
grid templates into executable value selectors and composes the literal
randomized run with the uniform-pilot template learner.
For upward zero-preserving grids, the selector is pulled back to the actual
revealed values and charge monotonicity compares the unrounded literal run
directly with the rounded learned objective, without an extra mesh loss.
The operational layer also supports a public-transcript-dependent selector:
its pilot/quota specialization completes the first pilot outcomes immediately,
then uses a supplied post-pilot selector, and is proved to terminate after
`2n+1` steps under every private relabelling.
The literal learned policy now goes one step further: it recomputes its quota
and selector solely from the first `k` public test-result records, stabilizes
after that pilot prefix, and terminates with the empirical grid-minimizing
template without receiving the input histogram as hidden advice.
Its analysis identifies the entire learned execution with the realized fixed
pilot/quota run and proves that the histogram read from the public transcript
is exactly the standard without-replacement sample histogram under private
random relabelling.
A physical two-permutation compiler executes each pilot occurrence only once,
deletes those owners from the virtual learned quota run, and proves the full
rounded-grid expected bound with explicit normalized pilot overhead
`2 k (u+1) / n`.
The corresponding unknown-input `Online.Strategy` is defined using only the
public grid, two private seeds, and the live transcript.  Its public value
classifier and literal pilot histogram are proved equal to the rounded cells
and without-replacement histogram used by the analytic compiler.
`RevealingOptimizationRawObserved` then equips the arbitrary observed-policy
side with revealing raw timings.  Its completion envelope and integrated area
lower bound meet the learned upper at one `RawBenchmarkData` value.
`RevealingOptimizationBenchmarkBridge` performs the exact benchmark algebra
and quota rounding; `RevealingOptimizationInstanceOptimal` packages the
positive- and zero-mean branches, the fixed-placement finite Yao comparison,
and the concrete vanishing direct error `1000 (u+1)^2/floor(n^(1/16))`.
