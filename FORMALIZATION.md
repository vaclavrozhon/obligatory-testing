# Formalization map

## Fully checked components

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
