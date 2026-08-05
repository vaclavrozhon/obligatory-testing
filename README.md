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

## Build

The project is pinned to Lean and mathlib 4.30.0.

```sh
lake update
lake exe cache get
lake build
```

The root module `SchedulingPaper.lean` imports the complete development.
