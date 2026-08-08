# Formalization map

## Fully checked components

### Randomized obligatory testing and the `4/3` proof

The mathematical core of `RANDOMIZED_UNKNOWN_MULTISET_PROOF.md` is now split
into small checked modules. `RandomizedStationaryCost` proves the exact
uniform-random-order stationary cost identity. `RandomizedDensityOptimizer`
constructs a finite maximum-density optimizer, while
`RandomizedThresholdClosure` proves that closing it by `q <= theta` preserves
the density identity even for sample-empty bins. `RandomizedQuantization`,
`RandomizedHistogramTransfer`, and `RandomizedLearnedThreshold` implement the
literal cutoff-32 histogram and transfer the learned threshold to the true
population. `RandomizedGoodLearned` then proves the complete robust finite
fluid certificate for a good learned sample.

`RandomPermutation`, `RandomizedHypergeometric`, `RandomizedHistogram`,
`RandomizedHistogramL1`, and `RandomizedHistogramConcentration` prove the
finite-sampling chain through
`E[histogram L1 error] <= sqrt(D/k)`. `RandomizedObligatoryUpper` checks the
robust `4/3+(2/3)s` inequality, good fallback, bad-event excess accounting,
sample-first overhead, and the explicit coefficient `20378`.
`RandomizedFiniteObjective` identifies the normalized formula with the actual
clairvoyant SPT objective on effective lengths `1+p`.

`RandomizedOperationalStrategy` defines the sampled learn/fallback policy as
an actual public-transcript strategy, including permutation relabelling. Lean
proves that the empirical learner supplies the closed-threshold density and
mass certificates and that the policy stops normally with every job completed
within `2n+1` operations. `RandomizedOperationalAnalytic` identifies the
literal transcript cost with the stationary/sample-first formulas and proves
all deterministic good-learned, good-fallback, and bad-sample bounds.
`RandomizedOperationalExpected` performs the conditional and outer
permutation averages. `RandomizedParameterChoice` verifies the actual floor
choices `d=floor(n^(1/4))`, `k=floor(n^(3/4))`, and `eta=32/d`, including all
positivity and square-root estimates.

`RandomizedIidBinaryLower` gives a slightly cleaner matching lower bound than
the balanced-bridge proof in the note: independent fair `0/2` inputs yield
coefficient `4n/(3n+5) -> 4/3`. `RandomizedOnlineBinaryCompiler` unfolds an
arbitrary terminating public-transcript `Online.Strategy` into the adaptive
fair binary tree, proves exact equality with its literal completion cost, and
then applies finite Yao selection to obtain one fixed oblivious input. The
offline expression is proved equal to the literal finite `OPT`.

`RandomizedFourThirds` is the public assembly module. The operational upper
theorem has no assumed good/bad schedule inequalities. For
`R=fourthRoot n >= 12`, the concrete floor-parameter strategy satisfies
`E ALG <= 4 OPT/3 + 20378 R^7`, hence
`E ALG <= (4/3 + 40756/R) OPT`. Its public operational lower theorem quantifies
over arbitrary finite families of terminating `Online.Strategy` seeds and
returns a fixed `0/2` input with ratio `4n/(3n+5)`. These two statements give
the sharp asymptotic randomized ratio `4/3` entirely inside Lean. The
small-`n` test-all convention used only to make the paper's displayed additive
bound literally uniform over every `n` is not needed for the asymptotic theorem
and is not packaged as a separate piecewise Lean strategy.

### Randomized optional-testing structure

`RandomizedOptionalFluid` checks the exact fractional full-module replacement,
the finite fractional-knapsack supporting certificate, and the pointwise
completion-envelope dominance theorem.  It also proves the long-test density
and area lower bounds, the simultaneous class-by-class grid repair, its
composition with the completion envelope (the deterministic core of (36)),
and the horizontal/vertical integral-shift estimate (38).  The canonical
test/medium/YOLO/high area formula, its quadratic normal form, both optimizer
cases, and the three-point witness are checked in the same file.
`RandomizedOptionalGridBridge` strengthens (36) to the form needed by an
actual urn prefix: it repairs every positive class, accounts separately for
the zero-class discrepancy, rebuilds the low test module from repaired
counts, and proves the pointwise envelope bound with exactly
`(numberOfPositiveClasses+1)*gamma` vertical slack.

`RandomizedOptionalKernel` proves the one-draw and two-draw histogram
Lipschitz estimates, the exact without-replacement/product-law correction,
the fixed-template cost bound with constant `12(L+1)`, and both deterministic
and expected empirical-minimizer sandwiches.
`RandomizedOptionalFiniteKernel` proves the uniform finite implementation
lemma (27a) for arbitrary position-dependent bounded one-job and ordered
two-job kernels: replacing the random-permutation pair law by the empirical
product law costs at most `(Bsingle+2*Bpair)/n`, independently of the grid
and the fixed template. `RandomizedOptionalLearning`
combines this with the finite histogram theorem to obtain the explicit
`2 C sqrt(K/k)` pilot-learning loss. `RandomizedOptionalUrn` proves the
pathwise predictable-selection decomposition, remaining-urn drift bound, and
the transfer of a centered-increment estimate to the adaptively selected test
and blind subsequences. `RandomizedOptionalPermutationUrn` then supplies the
missing probabilistic input directly in the project's finite uniform-average
semantics: suffix-symmetry, pairwise orthogonality of arbitrary predictable
increments, fixed-suffix variance, Chebyshev concentration, checkpoint
interpolation, and policy-uniform selected-count and selected-work bounds.
`RandomizedOptionalRates` instantiates these inequalities with literal finite
parameters: for `n=R^8`, adaptively selected category counts have error at
most `4R^7`, and blind work in `[0,L]` has error at most `4LR^7`, except with
probability at most `5/R` per category.  It also performs the finite union
bound: for at most `S` positive grid classes with `S^2<=R`, the joint
count/work failure is at most `10/S` and the aggregate normalized revelation
repair is at most `8/S`.  This gives a fully checked, slower vanishing mesh;
the draft's sharper `n^(-1/6)*sqrt(log n)` rate still relies on its
exponential Azuma estimate. `RandomizedOptionalOperational` gives blind
execution its actual processing time (without changing the older finite-cap
semantics), proves exact completion-area and work decompositions, reachable
prefix invariants, relabelling invariance, and the classwise operational
revelation constraint. `RandomizedOptionalStrategy` defines the literal
transcript-only test/low/medium/blind/high policy for that restricted public
transcript. `RandomizedOptionalOnline` supplies the full intended optional
information model: a blind completion reveals its elapsed processing time to
later decisions, with exact cost/area/work accounting, reachable-prefix
truthfulness and classwise revelation invariants, a strategy-independent
`2n+1` settling rank, and cost-preserving private relabeling.
`RandomizedOptionalObservedStrategy` defines the same canonical
four-block policy in this richer model.  The distinction matters for the
announced lower bound, whose arbitrary comparison policy may learn from blind
durations.

`RandomizedOptionalTraceBijection` and
`RandomizedOptionalObservedTrace` now close the arbitrary adaptive-touch
compiler without conditional probabilities.  Occurrences are distinguished,
the completed operational transcript is converted to its permutation of
first-touched public labels, and a lockstep theorem proves prefix causality
even when later decisions use observed blind durations.  The induced hidden
reveal order is an injective self-map of the finite placement space and hence
a bijection.  Reindexing by this bijection preserves the uniform average
exactly and produces a predictable `0/1` test selector.  Lean also checks the
pathwise selected-class and blind-work sum identities.  The older suffix-swap
lemmas remain available but are not used by this compiler.

The English instance-optimality proof is complete, but this is not yet a
formal proof of the full adaptive theorem.  The remaining
major layer is to connect the operational schedule, and an arbitrary
announced-multiset policy for the lower bound, to the complete fluid envelope
at every physical-time prefix and realized stopping fraction.  The adaptive
first-touch order and predictable test/blind selector are now fully compiled;
the remaining bridge must translate every operation-time prefix into the
already checked repaired completion envelope. The concrete canonical
transcript must still be decomposed into the already verified
generic finite kernels; the final announced-minimax/Yao wrapper and the
pilot-plus-main unknown-multiset strategy must then be assembled.
The detailed analytic proof is in `OPTIONAL_TWO_PHASE_PROOF.md`; this map
reports only what Lean currently checks.

### Model, optimum, and asymptotics

`Model`, `OfflineOptimal`, and `UnifiedOffline` formalize both cap models,
clairvoyant effective lengths, mode selection, shortest-first optimality, the
diagonal-plus-pairs formula, and quadratic lower bounds on `OPT`.
`Asymptotics` proves that a uniform `ALG ≤ c OPT + Cn` estimate gives the
paper's size-asymptotic coefficient and additive admissibility of every
`c + ε`.

### Online semantics and replay

`OnlineModel`, `Replay`, and `TimedOnline` define deterministic public-
transcript strategies, fixed and adaptive oracles, fuelled execution,
admissibility, freezing of adaptive answers, exact transcript replay, elapsed
time, and total completion cost.  `TranscriptPairAccounting` proves the exact
suffix-weighted pair formula for the completion cost of any timed transcript.
`RawStrategy` and `RawExecution` evaluate
the executable Raw strategy exactly.

### Constants and exact curve

`Constants`, `AlgebraicBranch`, `MixedCurve`, and `ExactCurve` prove the
algebraic and transcendental facts behind every branch and join of the exact
curve.  This includes the obligatory constant `RStar`, the algebraic root
branch, the reciprocal branch, the mixed implicit branch, continuity at all
joins, and the global maximum.

### Lower-bound analysis already internalized

`BinaryCurve`, `HiddenStopping`, and `HiddenStoppingOracle` contain the scalar
binary stopping inequalities and a concrete admissible revelation oracle,
including crossing persistence, overshoot control, binary freezing, and
replay.  `HiddenStoppingCostAccounting` additionally fixes the universal
fuel, closes settledness and the incomplete branch, proves the terminal
crossing dichotomy, and identifies the literal online completion objective
and offline pair objective. `HiddenStoppingPairAccounting` evaluates the
frozen binary offline objective in closed triangular form and reduces the
last premise to a literal suffix-weighted operation-pair exchange.
`HarmonicCore` and `HarmonicLimit` contain the exact finite harmonic
calculation and its optimized limit.  `LowerBoundAssembly` proves replay from
adaptive certificates to genuine fixed inputs and performs the full six-way
curve case split.  `LowBaseline` proves the complete `0 < u ≤ 1` adversarial
baseline for arbitrary strategies, including strategy-independent settling,
constant freezing, completion-record accounting, and the exact all-`u`
offline value.

`HiddenStoppingGlobalExchange` closes the literal completed-transcript
operation-pair exchange and discharges the hidden-stopping finite-cost
bridge.  `MixedQuotaHistory`, `MixedQuotaGlobalExchange`,
`MixedQuotaCrossingWindow`, `MixedQuotaRunAccounting`,
`MixedQuotaExchangeRuntimeGlue`, and `MixedQuotaVerifiedBridge` construct the
mixed-quota adversary, retain its first crossing, identify the frozen
multiset and exact offline value, and prove the full physical online
exchange in both the zero- and positive-tail cases.  `MixedQuotaAdaptive`
then performs the integral parameter choice and asymptotic absorption.
`HarmonicOperational` and `BoundedHarmonic` discharge respectively the
obligatory and finite-cap harmonic constructions.
`VerifiedLowerBoundFinalAssembly` fills every field of
`OperationalLowerInterfaces` with these verified theorems.

### Upper-bound analysis already internalized

`AdaptiveThreshold`, `ParameterizedAdaptiveStrategy`, and `ForcedPrefixUTE`
give concrete transcript-only strategies.  `EndpointReduction`,
`BoundaryRelaxation`, `ZeroPrefixGame`, `UTEEndpointGame`, and
`UTEEndpointReduction` prove the endpoint reductions and the complete scalar
games used by the low and two middle branches.

`ZeroPrefixPairAccounting` derives the normalized Zero-prefix polynomials
from literal endpoint pair charges and proves their exact identification with
`zeroPrefixAlg` and `zeroPrefixOpt`.
`UTEPairAccounting` analogously derives `uteA` and `uteO` from literal
four-class UTE pair charges and connects their excess exactly to `uteGap`.
`ZeroPrefixRuntime` and `UTERuntimeAccounting` prove the exact operational
shape of the corresponding fixed-input runs: all labels are tested with
their actual values, immediate decisions agree with the stated threshold
predicate, every job completes, and the deferred suffix uses the public SPT
selector.

`ObligatoryPairAccounting` evaluates every four-letter boundary word at its
successive adaptive thresholds, identifies its literal online and offline
pair objectives with the bank's exact local rewards, and proves the complete
telescoping identity.  It also proves coordinatewise convexity and endpoint
reduction for an arbitrary processing vector on a fixed symbolic word.

`BankPotential`, `BankAccounting`, `ParameterizedBank`, `CapReserve`,
`CappedBankAccounting`, `CapEndpointAccounting`, `UniformBankRemainder`,
`ReachableBankRemainder`, `ReachableCappedBankRemainder`,
`CompleteCapReserveRemainder`, `CapReservePathGeometry`,
`CapReserveFiniteRemainder`, `BankTelescope`, and `PlateauBank` prove the exact
ordinary/capped local rewards, bank inequalities, reachable countdown
invariant, finite telescoping, uniform ordinary remainder, and plateau
reduction.  The reachable parameterized base remainder includes all five
directions, the active/flat crossing, and the terminal step; the only capped
reserve term is reduced to a one-dimensional perspective in `(x,K)`.
`CapReserveFiniteRemainder` completes its finite-step estimate, including the
active region, cutoff crossing, inactive region, and terminal `x = 1` step.
Thus the complete five-endpoint capped bank now has an unconditional
reachable uniform remainder. `PlateauRuntimeInvariant` additionally proves
the parameterized counter balance and that, above `zStar`, every value in the
capped interval is necessarily classified as deferred.
`UpperBoundAssembly` turns these estimates into genuine
size-asymptotic upper certificates and checks the complete branch split.

`VerifiedUTEBelowTwoBridgeFinal`, `UTEEndpointFiniteBridge`,
`VerifiedZeroPrefixBridge`, `VerifiedMixedBoundaryBridge`, and
`VerifiedBoundaryBridges` discharge the remaining runtime-to-scalar and
boundary bridges.  `UpperBoundFinalAssembly` fills every field of
`OperationalUpperInterfaces` and exports the unconditional finite-cap
certificate.

### Top-level statement

`MainTheorems` packages the lower and upper directions into
`FiniteExactRatioConclusion`, `ObligatoryExactRatioConclusion`, and
`exact_ratio_main`.  The latter has no theorem or interface parameters:
it states the finite-cap result for every positive cap together with the
obligatory-testing endpoint.

## Verification status

`OperationalLowerInterfaces` and `OperationalUpperInterfaces` remain useful
internal assembly records, but their verified instances fill every field.
No operational interface is a premise of the public main theorems.  No
missing claim is hidden behind `sorry`, `admit`, or a project-defined
`axiom`; the root module `SchedulingPaper.lean` imports the complete
development.
