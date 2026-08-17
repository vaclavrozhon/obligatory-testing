# Exact deterministic ratios for uniform testing

This directory is a self-contained arXiv source tree for the manuscript
`paper.tex`.

## Build

Run

```sh
latexmk -pdf paper.tex
```

from this directory.  The build uses only standard LaTeX packages and the
included vector figure `curve.pdf`.

If `latexmk` is unavailable, the equivalent manual build is

```sh
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
bibtex paper
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

Both main theorems concern deterministic **size-asymptotic** competitive
ratios.  The algorithms prove bounds of the form

```text
ALG <= R OPT + O_u(n),
```

with fixed finite `u`.  The endpoint `u = infinity` is exactly obligatory
testing.  Since `OPT = Omega_u(n^2)`, this gives
the stated exact asymptotic coefficients and every larger coefficient under
the additive-constant convention.  The manuscript does not claim a single
finite additive constant at the endpoint coefficient.

On the plateau `u >= z_*`, including `u = infinity`, the same
Adaptive-Threshold algorithm satisfies

```text
ALG <= R_* OPT + C n
```

with one absolute constant `C` independent of `u`.

The optional common-upper theorem is per parameter: it gives the full
six-branch function `V(u)`, not only its worst value.  The three upper-bound
policies are specified in numbered `algorithmic` environments.  Its
mixed-regime upper bound is presented by a direct cap-reserve potential and
accompanied by an independent adjacent-exchange cross-check.
