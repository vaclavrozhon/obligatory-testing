# Scheduling with Uniform Tests: Information and Optimization

This directory is a self-contained arXiv source tree for the manuscript
`paper.tex`.

## Build

Run

```sh
latexmk -pdf paper.tex
```

from this directory for the complete manuscript, including all appendices.

The build uses only standard LaTeX packages and the
included vector figures.  The three introduction figures are native
TikZ/pgfplots sources in `curves_overview_tikz.tex`,
`randomized_curve_tikz.tex`, and `blind_optimization_curve_tikz.tex`.

If `latexmk` is unavailable, the equivalent manual build is

```sh
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
bibtex paper
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

## Submission metadata

The manuscript title and PDF metadata are `Scheduling with Uniform Tests:
Information and Optimization`; the current author block names Václav Rozhoň.
The bibliography contains DOI/arXiv metadata for the cited literature, and the
acknowledgements disclose the use of Bolzano and GPT-5.6 in developing the
results and formalization.

## Exact scope of the claims

The deterministic theorems concern **size-asymptotic** competitive ratios.
Their algorithms prove bounds of the form

```text
ALG <= R OPT + O_u(n),
```

with fixed finite `u`.  The endpoint `u = infinity` is exactly obligatory
testing.  Since `OPT = Omega_u(n^2)`, this gives
the stated exact asymptotic coefficients and every larger coefficient under
the additive-constant convention.

On the plateau `u >= z_*`, including `u = infinity`, the same
Adaptive-Threshold algorithm satisfies

```text
ALG <= R_* OPT + C n
```

with one absolute constant `C` independent of `u`.

The deterministic revealing-optimization theorem is per parameter: it gives the full
six-branch function `R_det_RO(u)`, not only its worst value.  The three upper-bound
policies are specified in numbered `algorithmic` environments.  Its
mixed-regime upper bound is presented by a direct cap-reserve potential and
accompanied by an independent adjacent-exchange cross-check.

The randomized results give the exact four-piece revealing-optimization
curve, the sharp unbounded obligatory ratio `4/3`, and instance-optimal
leading values for bounded obligatory testing, blind execution, revealing
optimization, and blind optimization.  In obligatory testing, the worst-case
algorithm uses the fixed cutoff `32`; the bounded-bag instance-optimal policy
is its variant with a slowly growing cutoff.
The full revealing-optimization instance-optimal proof is Section 4 of the
manuscript; its outer worst-case optimization is the separate four-piece
curve in Section 5.  Lean now checks this instance theorem end to end for a
literal pilot-learned transcript-only strategy against every finite
randomization of completing adaptive observed policies, including the
fixed-placement Yao lower bound, the zero-mean branch, and a concrete
input-size-only vanishing error.  It also checks the four-piece randomized
scalar maximization, including transition uniqueness, attainment, the
plateau, and the global maximum.

The blind-execution theorem is formalized in Lean.  For blind optimization,
Lean checks the deterministic counterexample and curve, the universal pilot
upper, the randomized reduction for arbitrary finite empirical
distributions, and literal operational fixed-input Yao selection.  For
obligatory testing, Lean checks the fixed-cutoff `4/3` theorem, the full
growing-cutoff bounded instance-optimal comparison and its universal
vanishing parameter family, the shared fluid algebra, and the deterministic
balanced-input impossibility.

## Source organization

The main file is intentionally short: `paper.tex` contains the build switch,
preamble, front matter, and chapter order, while the shared model definitions
and technical tools live in `models_and_preliminaries.tex`.

Section 3 is assembled by `deterministic_revealing.tex` from policy
guarantees, branchwise lower bounds, curve assembly, and the obligatory
endpoint.  The independent cap-bubbling certificate is the normal appendix
source `cap_bubbling.tex`.  Superseded proofs, generated PDF plots, and their
plotting scripts are retained under `old/`; the manuscript uses only the
native TikZ sources listed above.
