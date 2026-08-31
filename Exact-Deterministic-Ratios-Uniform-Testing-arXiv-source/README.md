# Test or Run? Scheduling Jobs of Unknown Length

This directory is a self-contained source tree for the main manuscript
`paper.tex` and the separate Lean audit `lean_appendix.tex`.

## Build

Run

```sh
latexmk -pdf paper.tex
latexmk -pdf lean_appendix.tex
```

from this directory to build the two documents.  The main manuscript contains
the mathematical preliminaries and proofs; the second document records the
Lean coverage, exported theorem statements, and reproduction instructions.

The build uses only standard LaTeX packages and included vector figures.
The introduction's deterministic overview is a native TikZ/pgfplots source
in `curves_overview_tikz.tex`; standalone sources for the randomized and
blind-optimization curves are retained alongside it.

The main-paper-only arXiv upload archive contains neither the audit nor Lean
sources.  The fuller companion archive additionally contains
`anc/lean-audit.pdf` and `anc/obligatory-testing-lean-artifact.zip`; the latter
is the complete pinned Lean project and can be checked independently with the
commands documented in the audit.

If `latexmk` is unavailable, the equivalent manual build is

```sh
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
bibtex paper
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex

pdflatex -interaction=nonstopmode -halt-on-error lean_appendix.tex
bibtex lean_appendix
pdflatex -interaction=nonstopmode -halt-on-error lean_appendix.tex
pdflatex -interaction=nonstopmode -halt-on-error lean_appendix.tex
pdflatex -interaction=nonstopmode -halt-on-error lean_appendix.tex
```

## Submission metadata

The manuscript title and PDF metadata are `Test or Run? Scheduling Jobs of
Unknown Length`; the current author block names Václav Rozhoň.
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
algorithms are specified in numbered `algorithmic` environments.  Its
upper bound for the interval from the fourth to the fifth transition point
is presented by a direct cap-reserve potential and
accompanied by an independent adjacent-exchange cross-check.

The randomized results give the exact four-piece revealing-optimization
curve, the sharp unbounded obligatory ratio `4/3`, and instance-optimal
leading values for bounded obligatory testing, blind execution, revealing
optimization, and blind optimization.  In obligatory testing, the worst-case
algorithm uses the fixed cutoff `32`; the bounded-bag instance-optimal algorithm
is its variant with a slowly growing cutoff.
The full revealing-optimization instance-optimal proof is Section 5 of the
manuscript; its outer worst-case optimization is the separate four-piece
curve in Section 6.  Lean now checks this instance theorem end to end for a
literal sample-learned transcript-only strategy against every finite
randomization of completing adaptive observed algorithms, including the
fixed-placement Yao lower bound, the zero-mean branch, and a concrete
input-size-only vanishing error.  It also checks the four-piece randomized
scalar maximization, including transition uniqueness, attainment, the
plateau, and the global maximum.

The paper-facing comparison and lower-bound corollaries additionally
quantify over arbitrary private probability spaces with integrable
real-valued run costs.  Lean proves the finite-input/integral interchange and
selects each fixed adversarial input outside the general private-seed
integral; no finite-support approximation is left to prose.

The blind-execution theorem is formalized in Lean.  For blind optimization,
Lean checks the deterministic counterexample and curve, the universal sample
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

The concentration tools are part of Section 2.5: the standard estimates in
`standard_concentration.tex` are included by `models_and_preliminaries.tex`.
The finite-dimensional fluid model and its common pointwise optimality
theorem form Section 3 in `fluid_benchmark.tex`.  Section 4 is assembled by
`deterministic_revealing.tex` from algorithm
guarantees, branchwise lower bounds, curve assembly, and the obligatory
endpoint.  The file `formal_verification.tex` supplies the body of the
standalone Lean audit `lean_appendix.tex`.  Superseded proofs, generated PDF
plots, and their plotting scripts are retained under `old/`; the manuscript
uses only the native TikZ sources listed above.
