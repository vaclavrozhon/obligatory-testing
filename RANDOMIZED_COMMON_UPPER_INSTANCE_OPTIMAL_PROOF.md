# Randomized instance optimality for a common upper bound

Self-contained analytic proof, 17 August 2026.

## 1. Model and statement

Fix a constant `u>0`.  There are `n` labelled nonpreemptive jobs on one
machine.  Job `i` has an unknown value

```text
p_i in [0,u].
```

At an idle machine a nonanticipating policy may perform one of the following
actions.

1. **Raw execution.**  Execute an untouched job for exactly `u` time and
   complete it.  Its hidden value `p_i` is not revealed to the policy.
2. **Test.**  Spend one unit of time testing an untouched job and reveal
   `p_i`.  If `p_i=0`, the job completes at the end of the test.
3. **Known processing.**  Process a previously tested positive job for
   `p_i` time and complete it.

The objective is the sum of completion times.  Policies are required to
complete every job.  A policy that fails to do so has infinite cost.

The adversary is oblivious: it fixes the labelled vector before the policy
draws its random bits.  If `M` is the underlying multiset, let `D_M` be its
empirical probability distribution.  All constants hidden in `O_u(.)` may
depend on the fixed common upper bound `u`, but not on `M`, its labelling, or
the policy.

This document defines an explicit benchmark `Phi_u(D)` and proves the
following theorem.

> **Theorem 1 (common-upper instance optimality).**  For every fixed `u>0`
> there are randomized nonanticipating policies `A*_{n,u}`, depending only
> on `n,u`, and a deterministic sequence `epsilon_u(n)->0` such that, for
> every size-`n` multiset `M subseteq [0,u]`, the following hold.
>
> **Universal upper bound.**  For every fixed labelling `sigma(M)`,
>
> ```text
> E C_{A*_{n,u}}(sigma(M))
>     <= n^2 Phi_u(D_M)+epsilon_u(n)n^2.               (1.1)
> ```
>
> **Announced-multiset lower bound.**  For every randomized
> nonanticipating policy `A`, even if `A` is told `M`, there is a fixed
> labelling `sigma(M)`, chosen before the private seed of `A`, such that
>
> ```text
> E C_A(sigma(M))
>     >= n^2 Phi_u(D_M)-epsilon_u(n)n^2.               (1.2)
> ```
>
> One may take
>
> ```text
> epsilon_u(n)=O_u(n^(-1/6)*sqrt(log(n+2))).           (1.3)
> ```

The expectation in both statements is only over the private randomness of
the policy.  Equivalently, in the random-urn formulation in which the
adversary chooses only `M` and each new access returns a uniformly random
remaining occurrence, `n^2 Phi_u(D_M)+o_u(n^2)` is the optimal announced-
multiset value.  A policy not told `M` attains the same value after a
sublinear pilot sample.

The proof has five parts.

1. We identify the exact clairvoyant optimum.
2. For every fixed final tested fraction `q`, a completion-envelope argument
   solves the deterministic fluid relaxation exactly.
3. An adaptive first-touch trace is a bijective relabelling of the finite
   permutation space.  Predictable sampling without replacement therefore
   controls every adaptive policy simultaneously over all touch prefixes.
4. A growing grid transfers the fluid lower bound to arbitrary bounded
   finite multisets.
5. A sublinear random pilot estimates the grid histogram and selects an
   asymptotically optimal canonical policy.

No exchange of nodes in an adaptive policy tree is used.

## 2. The exact clairvoyant benchmark

For a value `p`, define its effective clairvoyant length

```text
s_u(p)=min{u,1+p}.                                    (2.1)
```

The two alternatives in (2.1) are raw execution and a test immediately
followed by known processing.  Put `s_i=s_u(p_i)`.

### Lemma 2.1 (exact offline optimum)

The clairvoyant optimum schedules the jobs in nondecreasing order of `s_i`
and, for every job, uses the alternative attaining (2.1).  Its exact cost is

```text
OPT_u(M)
 = sum_i s_i + sum_{i<j} min(s_i,s_j)
 = (1/2) sum_{i,j} min(s_i,s_j)+(1/2)sum_i s_i.        (2.2)
```

#### Proof

Take an arbitrary feasible schedule and list jobs in their order of
completion, `j_1,...,j_n`.  Before `j_r` completes, the schedule has
performed, for every `l<=r`, either a raw operation of length `u` or both a
test and a processing operation of total length `1+p_{j_l}`.  Therefore

```text
C_{j_r} >= sum_{l<=r} s_{j_l}.                        (2.3)
```

Summing (2.3), an adjacent interchange shows that the right side is
minimized by nondecreasing `s_i`.  Conversely, process jobs in that order,
using raw execution when `u<=1+p_i` and a contiguous test-processing block
when `1+p_i<u`.  Every inequality (2.3) is then an equality.  This proves
(2.2).  The argument includes `p_i=0`: its test is a length-one completing
block. `QED`

For a probability distribution `D` on `[0,u]`, define the leading offline
coefficient

```text
Omega_u(D)=(1/2) E[min(s_u(P),s_u(Q))],               (2.4)
```

where `P,Q` are independent with law `D`.  For an empirical distribution,
(2.2) becomes

```text
OPT_u(M)=n^2 Omega_u(D_M)+(1/2)sum_i s_u(p_i).         (2.5)
```

In particular, with `c_u=min{u,1}>0`,

```text
Omega_u(D)>=c_u/2.                                    (2.6)
```

This uniform positive lower bound is why additive `o(n^2)` instance
optimality will also give a meaningful multiplicative ratio for every
multiset in this model.

## 3. The deterministic fluid benchmark

We first take `D` to be a finite probability distribution on `[0,u]`.  Let
`D_0=Pr[P=0]` and `mu=E[P]`.

### 3.1 The maximum-density test module

A test always spends one unit of work.  It automatically completes a zero
outcome.  After a positive outcome `p`, a fluid policy may choose to process
some fraction of that outcome immediately.  For a selection vector
`0<=g(p)<=1` on the positive support, put

```text
A(g)=D_0+E[g(P) 1{P>0}],
W(g)=1+E[P g(P) 1{P>0}].                              (3.1)
```

Thus one unit mass of tests together with its selected positive outcomes
completes mass `A(g)` and uses work `W(g)`.  Define

```text
rho(D)=max_g A(g)/W(g),
tau(D)=1/rho(D).                                      (3.2)
```

The ratio is declared to be zero when `A(g)=0`.  The maximum is positive and
attained because the support is finite and the selection box is compact.

### Lemma 3.1 (threshold form)

There is a maximizing selection `g*` such that

```text
g*(p)=1  for p<tau,
g*(p)=0  for p>tau,                                   (3.3)
```

with an arbitrary fraction of a possible atom at `p=tau`.  If

```text
a   = A(g*),
ell = E[P g*(P) 1{P>0}],
w   = 1+ell,
```

then

```text
w=a*tau,
E[(tau-P)^+]=1.                                      (3.4)
```

Moreover, for every other selection `0<=h<=1`,

```text
tau [D_0+E[h(P)1{P>0}]]
    <=1+E[P h(P)1{P>0}].                             (3.5)
```

#### Proof

Let `rho=A(g*)/W(g*)` and `tau=W(g*)/A(g*)`.  Increasing selected mass `d`
at a positive value `p` changes numerator and denominator by `d` and `pd`.
Cross multiplication shows that it increases density exactly when
`p<tau`.  Removing selected mass increases density exactly when `p>tau`.
Consequently a maximizer may be chosen in the threshold form (3.3), with a
neutral split at equality.

The identity `w=a tau` is the definition of `tau`.  Expanding it gives

```text
1=tau D_0+E[(tau-P)g*(P)1{P>0}].                     (3.6)
```

By (3.3), the right side is exactly `E[(tau-P)^+]`; a boundary atom makes no
contribution.  This proves (3.4).  Finally, maximality says
`A(h)/W(h)<=1/tau`; cross multiplication yields (3.5). `QED`

The equation in (3.4) also proves uniqueness of `tau`: the function
`x -> E[(x-P)^+]` is continuous, and after it becomes positive it is
strictly increasing until and beyond the value one.

The full test module has completion capacity `a` per unit test mass and work
`w`, hence work per completion `w/a=tau`.  Raw execution has work per
completion `u`.  Thus testing can be useful only in the **short-test regime**

```text
tau<u.                                                (3.7)
```

Since `P<=u`, (3.4) gives the equivalent test

```text
tau<u  iff  E[u-P]>1  iff  1+mu-u<0.                 (3.8)
```

### 3.2 The fixed-tested-fraction envelope

Fix `q in [0,1]`, interpreted as the final mass of tested jobs.  Split a
boundary atom at `tau` into selected and residual virtual copies according
to `g*`.  Let `R_i` be the residual mass at a positive support point `p_i`.
Then

```text
sum_i R_i=1-a,
p_i>=tau whenever R_i>0.                             (3.9)
```

At an arbitrary prefix of a fluid schedule write

```text
t   = mass tested so far,
b   = mass completed raw so far,
c_i = tested mass of positive class i already processed.            (3.10)
```

Its completed mass and work are

```text
y=D_0 t+b+sum_i c_i,
x=t+u b+sum_i p_i c_i.                               (3.11)
```

Every prefix of a schedule whose final tested mass is `q` satisfies

```text
0<=t<=q,
0<=b<=1-q,
0<=c_i<=D_i t.                                       (3.12)
```

Let `H^u_{D,q}(x)` be the maximum possible value of `y` over (3.11)--(3.12)
with work at most `x`.  Set it to zero for negative `x`; once all unit mass
can be completed, extend it by the value one.

### Lemma 3.2 (exact fractional-knapsack envelope)

The completion envelope `H^u_{D,q}` is the ordinary divisible-knapsack curve
for these items:

| item | completion capacity | work per completion |
|---|---:|---:|
| maximum-density test module | `a q` | `tau` |
| residual tested class `i` | `q R_i` | `p_i` |
| raw module | `1-q` | `u` |

If `tau<u`, its greedy order is

```text
test module
-> residual known classes in nondecreasing p_i
-> raw module,                                        (3.13)
```

where a residual class at `p_i=u` may be placed on either side of the raw
module.  If `tau>=u`, the all-raw curve pointwise dominates every solution
with positive tested mass.

#### Proof

Consider a feasible prefix `(t,b,c)`.  If an atom at `tau` was split, assign
its processed mass first to the selected virtual copy, up to its revelation
capacity, and the remainder to the residual copy.  This preserves all
constraints.

Let `y_L` and `x_L` be the completed mass and work contributed by the tests,
tested zeros, and processed selected positive copies.  Dividing their
positive processed masses by `t` and applying (3.5) gives

```text
tau*y_L<=x_L.                                         (3.14)
```

The revelation constraints also give `y_L<=a t`.  Put `lambda=y_L/a`.
Then

```text
0<=lambda<=t<=q,
lambda*a=y_L,
lambda*w=tau*y_L<=x_L.                               (3.15)
```

Thus the complete low part can be replaced by `lambda` full test modules,
preserving its completed mass and weakly decreasing its work.  Every
residual class has capacity at most `qR_i`, and raw mass has capacity at most
`1-q`.  This maps every feasible point of the original envelope into the
displayed ordinary knapsack.

Conversely, choose the tie order in which the test module comes first.  While
the greedy knapsack is partway through that item, run the corresponding
fraction of the `q` tests and process all selected outcomes.  No residual
class is used.  After all `q` tests have run, every residual capacity `qR_i`
is available, so the remaining items can be processed in greedy order.  A
partial final item is implemented by the corresponding fraction of its
mass.  Hence the knapsack trajectory lies in the closure of the original
fluid trajectories, and the two envelopes agree pointwise.

Ordinary fractional knapsack fills items in nondecreasing work per
completion: if a more expensive item is used while a cheaper item is not
full, moving a small amount of completion mass from the former to the latter
strictly reduces work.  In the regime `tau<u`, (3.9) and `p_i<=u` therefore
give (3.13).

If `tau>=u`, the test module costs at least `u`.  Every residual class costs
at least `tau`, except that when all support lies below `tau` there is no
residual class.  Thus every knapsack completion unit costs at least `u`,
whereas one raw item of capacity one has cost exactly `u`.  The triangular
all-raw completion curve pointwise dominates. `QED`

### 3.3 Integrating the envelope

Let

```text
m_R = sum_i p_i R_i = mu-ell,
K_R = sum_{i,j} min(p_i,p_j) R_i R_j.                 (3.16)
```

### Lemma 3.3 (fixed-`q` value)

In the short-test regime `tau<u`,

```text
integral_0^infinity [1-H^u_{D,q}(x)] dx=F_{u,D}(q),   (3.17)
```

where

```text
F_{u,D}(q)
 = (1+ell)(q-aq^2/2)
   +q m_R(1-q)
   +q^2 K_R/2
   +u(1-q)^2/2.                                      (3.18)
```

If `tau>=u`, every fixed-`q` envelope has area at least `u/2`, and `q=0`
attains `u/2`.

#### Proof

For a divisible block of completion mass `v`, cost `c` per completion, and
later unfinished mass `r`, the remaining-mass area contributed by that block
is

```text
c(vr+v^2/2).                                          (3.19)
```

The test module has mass `aq`, cost `tau`, and later mass `1-aq`.  Its area is

```text
tau[aq(1-aq)+(aq)^2/2]
 =tau(aq-a^2q^2/2)
 =(1+ell)(q-aq^2/2).                                 (3.20)
```

The residual known stock has class masses `qR_i`.  Its total processing work
`q m_R` delays all raw mass `1-q`.  Its internal SPT area is

```text
(q^2/2) sum_{i,j} min(p_i,p_j)R_iR_j=q^2K_R/2.        (3.21)
```

Finally the homogeneous raw block has mass `1-q` and cost `u`, giving area
`u(1-q)^2/2`.  Summing (3.20)--(3.21) proves (3.18).  The total work horizon
is

```text
q(1+ell)+q m_R+u(1-q)=q(1+mu)+u(1-q),                (3.22)
```

after which the envelope equals one.

For `tau>=u`, Lemma 3.2 bounds the completion curve by the triangular raw
curve `min{1,x/u}`.  Its remaining-mass area is `u/2`, attained by `q=0`.
`QED`

Define

```text
Phi_u(D)=min_{0<=q<=1} F_{u,D}(q),  if tau<u,
Phi_u(D)=u/2,                       if tau>=u.          (3.23)
```

The formula is completely explicit.  Indeed,

```text
F_{u,D}(q)=u/2+Aq+Bq^2,                              (3.24)
```

where

```text
A=1+mu-u,
B= -a(1+ell)/2-m_R+K_R/2+u/2.                        (3.25)
```

For every fixed `x`, the feasible set (3.12) is affine in `q`: convexly
combining feasible points for `q_1,q_2` gives a feasible point for the same
convex combination of the parameters.  Therefore `H^u_{D,q}(x)` is concave
in `q`.  Integrating `1-H` on the common fixed horizon `[0,1+u]` proves that
`F_{u,D}` is convex, hence

```text
B>=0.                                                  (3.26)
```

In the short-test regime, (3.8) gives `A<0`.  The minimizing tested fraction
is consequently

```text
q*=1                         if B=0,
q*=min{1,-A/(2B)}            if B>0.                  (3.27)
```

This proves the deterministic fluid structure theorem: even if the stopping
fraction is selected adaptively, once its realized value is `q`, no fluid
trajectory can have smaller area than `F_{u,D}(q)>=Phi_u(D)`.

## 4. Adaptive first touches form a uniform urn

The preceding theorem fixed the final fraction `q`.  A finite policy may
adaptively select public labels, interleave known processing with new
touches, and stop testing according to all test outcomes.  We now convert
such a run into predictable sampling without replacement.

The fact that raw execution does not reveal `p_i` requires a small but
important distinction: the reveal sequence below is an **analytical hidden
sequence**, not the policy's observation sequence.

Distinguish equal-valued occurrences.  Let `J` be the `n` public labels,
`Omega` the `n` occurrence tokens, and `v:Omega->[0,u]` their values.  A
placement is a bijection `sigma:J->Omega`.

Fix a deterministic completing policy `A`.  In its run on `sigma`, let

```text
ell_1(sigma),...,ell_n(sigma)                          (4.1)
```

be the labels in order of first touch, where a first touch is either a test
or a raw execution.  This list is a permutation of `J`.  Let
`kind_k(sigma)` record whether touch `k` is a test or raw execution, and
define the hidden occurrence order

```text
R_A(sigma)_k=sigma(ell_k(sigma)).                     (4.2)
```

### Lemma 4.1 (adaptive-reveal bijection)

The map `sigma -> R_A(sigma)` is a bijection from placements to permutations
of `Omega`.  Moreover, `kind_k(sigma)` is determined by the preceding hidden
values

```text
v(R_A(sigma)_1),...,v(R_A(sigma)_{k-1}).              (4.3)
```

#### Proof

Suppose `R_A(sigma)=R_A(sigma')`.  We prove by induction on `k` that the two
runs have identical observable histories immediately before first touch
`k`.  This is true initially.  Between consecutive first touches, a
deterministic policy may only process already tested known jobs; equal
observable histories make it perform the same such operations.

It then chooses the same next fresh label and the same touch kind.  If this
kind is a test, equality of the hidden occurrence order gives the same token
and hence the same observed value, so the histories remain equal.  If it is
raw, both operations last the public deterministic time `u` and reveal no
value, so again the histories remain equal.  Therefore

```text
ell_k(sigma)=ell_k(sigma')                             (4.4)
```

for all `k`.  Equation (4.2) now implies
`sigma(ell_k)=sigma'(ell_k)` for every `k`; because these labels enumerate
`J`, `sigma=sigma'`.  The reveal map is injective between two finite sets of
cardinality `n!`, hence bijective.

The same lockstep induction with only a common hidden-value prefix proves
the second assertion.  A raw-hidden value is more information than the
policy actually receives, but this is harmless: the observable history is a
deterministic function of that richer prefix. `QED`

Consequently, under a uniform random placement, `R_A(sigma)` is a uniform
random permutation of the occurrence tokens.  If

```text
X_k=v(R_A(sigma)_k),
A_k=1{kind_k(sigma)=test},                             (4.5)
```

then `A_k` is predictable with respect to the filtration generated by
`X_1,...,X_{k-1}`.  Duplicate values cause no problem because uniformity was
proved on occurrence tokens.  For a randomized policy, fix its private seed,
apply the lemma, and average over seeds at the end.

### Lemma 4.2 (simultaneous predictable-urn discrepancy)

Partition `[0,u]` into `K+1` cells, with `{0}` separate.  Let `D_j` be the
exact fraction of occurrences in cell `j`.  Fix `delta in (0,1)`.  There is
an event `G` such that, simultaneously for every touch prefix ending before
only `delta n` labels remain and every cell `j`,

```text
|sum_{k<=m} A_k 1{X_k in j}-D_j sum_{k<=m}A_k|
    <=Gamma_n,                                        (4.6)
```

where one may take

```text
e_n=sqrt(8n log(n(K+2))),
Gamma_n=(1+1/delta)e_n.                               (4.7)
```

If `K` is polynomial in `n`, then `Pr(not G)=o(1)`.

#### Proof

Let `N_j(k)` count cell `j` among the first `k` entries of the uniform
permutation.  Hoeffding's inequality for sampling without replacement,
followed by a union bound over all `k<=n` and all cells, gives except with
probability `o(1)`

```text
|N_j(k)-kD_j|<=e_n                                    (4.8)
```

simultaneously.  If `R_{k,j}` is the conditional proportion of cell `j`
among the occurrences remaining after `k` touches, then for
`k<=(1-delta)n`,

```text
|R_{k,j}-D_j|
 =|kD_j-N_j(k)|/(n-k)
 <=e_n/(delta n).                                    (4.9)
```

For a fixed cell,

```text
M_j(m)=sum_{k<=m} A_k(1{X_k in j}-R_{k-1,j})          (4.10)
```

is a martingale because `A_k` is predictable; its increments have absolute
value at most one.  Maximal Azuma--Hoeffding and another union bound put
`max_m |M_j(m)|<=e_n` simultaneously for all cells except with probability
`o(1)`.  On the intersection with (4.8),

```text
|sum_{k<=m}A_k(1{X_k in j}-D_j)|
 <=e_n+sum_{k<=m}A_k |R_{k-1,j}-D_j|
 <=e_n+e_n/delta=Gamma_n.                            (4.11)
```

This proves (4.6).  The displayed choice of `e_n` makes each exponential
tail inverse-polynomial with enough margin for every stated union bound.
`QED`

Unlike the blind-actual-processing-time model, no selected-work martingale
is needed: every raw completion has the deterministic public duration `u`.

## 5. The announced-multiset lower bound

We first prove the lower bound for a fixed finite grid, then let its number of
cells grow.

### 5.1 Suffix editing

Fix a deterministic policy, equivalently a randomized policy with its seed
held fixed.  Remove idle time and redundant operations; this can only reduce
its cost.  Stop the first-touch sequence after
`floor((1-delta)n)` distinct labels have been touched.  Let `qn` be the
number of tests among these touches.

Modify the remaining schedule as follows.  Every still-untouched job that
the original schedule would later test is instead run raw at the position of
its first original operation; delete its test and any later known-processing
operation.  Jobs that were already destined for raw execution are unchanged,
and all unaffected records retain their relative order.  The edited schedule
performs exactly `qn` tests and runs every other job raw.

At most `delta n+O(1)` jobs are affected, and at most three bounded operation
records per affected job are replaced, moved, or deleted.  Every operation
has length at most `max{1,u}`.  Moving or replacing one such operation can
alter each of at most `n` completion times by at most a constant depending
only on `u`.  Hence

```text
|C_original-C_edited|<=C_u delta n^2+O_u(n).          (5.1)
```

We use only the direction

```text
C_original>=C_edited-C_u delta n^2-O_u(n).            (5.2)
```

This edit is why concentration is needed only while at least `delta n`
untouched occurrences remain.

### 5.2 Pathwise repair to the envelope

First suppose the multiset values lie on a fixed finite support

```text
0=p_0<p_1<...<p_s<=u,                                 (5.3)
```

with empirical masses `D_{n,i}`.  Work on the single good event of Lemma
4.2 and only now substitute the realized value `q`.  Put
`gamma_n=Gamma_n/n`.

At an arbitrary operation boundary of the edited schedule, normalize counts
and physical work by `n`, and write

```text
t   = tested mass so far,
b   = raw-completed mass so far,
z   = zero mass completed by tests,
c_i = processed known positive mass of class i.       (5.4)
```

Before the cutoff, (4.6) applies at the current touch prefix.  After the
cutoff there are no new tests, so it continues to control the fixed tested
stock.  Therefore

```text
z<=D_{n,0}t+gamma_n,
c_i<=D_{n,i}t+gamma_n.                                (5.5)
```

Set `c_i'=(c_i-gamma_n)^+`.  Then

```text
c_i'<=D_{n,i}t,
t<=q,
b<=1-q.                                               (5.6)
```

If `x` is the actual normalized work of the prefix, raw work is exactly
`u b`, and reducing the known masses can only reduce processing work.  Thus

```text
t+u b+sum_i p_i c_i'<=x.                              (5.7)
```

The completed mass satisfies

```text
z+b+sum_i c_i
 <=D_{n,0}t+b+sum_i c_i'+(s+1)gamma_n.                (5.8)
```

By the definition of the empirical completion envelope,

```text
completed_fraction(x)
 <=H^u_{D_n,q}(x)+(s+1)gamma_n                       (5.9)
```

at every operation boundary.  Between boundaries, an operation has
normalized length at most `max{1,u}/n`; using the step-function area identity

```text
C/n^2=integral_0^infinity
       (1-completed_fraction(x)) dx                  (5.10)
```

therefore adds only `O_u(1/n)` to the normalized error.  The normalized
horizon is at most `1+u`, so vertical slack in (5.9) costs at most
`(1+u)(s+1)gamma_n`.  Lemma 3.3 and (5.2) give, pathwise on the good event,

```text
C_original/n^2
 >=Phi_u(D_n)
   -C_{u,s}(gamma_n+delta+1/n).                       (5.11)
```

This holds in both regimes.  When `tau<u`, insert the realized `q` and use
`F_{u,D_n}(q)>=Phi_u(D_n)`.  When `tau>=u`, use the all-raw dominance part of
Lemma 3.3.

Crucially, we never condition on `q`.  The event controls every touch prefix
simultaneously; `q` is substituted only in the deterministic pathwise
inequality.

### 5.3 A growing grid

An arbitrary multiset can have `n` distinct positive values.  Keep zero as a
separate cell, divide `(0,u]` into

```text
K_n=floor(n^(1/6))                                    (5.12)
```

positive bins, and round every positive value upward to its bin endpoint.
For sufficiently large `n`, the mesh is

```text
h_n=u/K_n=O_u(n^(-1/6)).                              (5.13)
```

Let `D_n^grid` be the rounded empirical distribution.  Zero must remain
separate because a tested zero completes at its test while a positive job
does not.

We first record stability of the benchmark.

### Lemma 5.1 (zero-preserving rounding stability)

If `D,D'` admit a coupling `(P,P')` such that

```text
|P-P'|<=h almost surely,
P=0 iff P'=0,                                         (5.14)
```

then

```text
|Phi_u(D)-Phi_u(D')|<=h.                              (5.15)
```

#### Proof

Take any feasible fluid policy for `D`.  Under `D'`, whenever a test reveals
`p'`, draw a private auxiliary mark `p` from the conditional coupling law and
make the subsequent decisions using that mark.  A raw action reveals neither
`p` nor `p'`, so no mark is needed for its decision.  The simulated marks
have law `D`, hence the transported policy is nonanticipating and has the
same action/completion order as the original simulated policy.

Raw durations are exactly `u` in both systems.  Tests have length one in
both.  Corresponding known-processing operations differ by at most `h` per
unit job mass.  Because (5.14) preserves zero, a tested job completes at its
test in one system exactly when it does in the other.  The total absolute
change in normalized processing work is at most `h`, while unfinished mass
is at most one.  Thus the two normalized completion areas differ by at most
`h`.  Taking the infimum over policies and then reversing `D,D'` proves
(5.15).  By Lemma 3.2, that fluid infimum is exactly `Phi_u`. `QED`

For the finite lower bound, aggregate processed known jobs by grid bin.  Let
`v_j` be the upper endpoint of positive bin `j`, let `c_j` be its processed
known mass, and set `c_j'=(c_j-gamma_n)^+`.  The actual processing work of
that bin is at least `(v_j-h_n)c_j`.  Therefore

```text
sum_j v_j c_j'
 <=actual known-processing work+h_n.                  (5.16)
```

The repaired variables obey the exact grid revelation constraints, while
completed mass loses at most `(K_n+1)gamma_n`.  Consequently the growing-grid
analogue of (5.9) is

```text
completed_fraction(x)
 <=H^u_{D_n^grid,q}(x+h_n)+(K_n+1)gamma_n.            (5.17)
```

A horizontal shift by `h_n` loses at most `h_n` area because
`0<=1-H<=1`.  Choose

```text
delta_n=n^(-1/6),
e_n=sqrt(8n log(n(K_n+2))),
Gamma_n=(1+1/delta_n)e_n.                             (5.18)
```

Then

```text
(K_n+1)Gamma_n/n
 =O(n^(-1/6)*sqrt(log(n+2))).                         (5.19)
```

The union of the prefix and martingale bad events has probability `o(1)`;
with the constants in Lemma 4.2 it can be made `O(n^(-3))`.  On the good
event, integrate (5.17), apply the fixed-`q` theorem, and restore the suffix
edit.  On the bad event use only nonnegativity of cost and
`0<=Phi_u<=u/2`.  Averaging gives

```text
E_uniform placement C_A/n^2
 >=Phi_u(D_n^grid)
   -O_u(n^(-1/6)*sqrt(log(n+2))).                     (5.20)
```

Finally (5.15) gives, uniformly over all multisets,

```text
E_uniform placement C_A/n^2
 >=Phi_u(D_M)
   -O_u(n^(-1/6)*sqrt(log(n+2))).                     (5.21)
```

The bound is uniform over deterministic announced policies.  Fixing and then
averaging over the private seed proves it for randomized announced policies.

### 5.4 From a uniform placement to a fixed oblivious labelling

For a randomized policy `A` told `M`, average first over a uniform placement
and then over its seed.  Inequality (5.21) lower-bounds this average.  Hence
at least one placement `sigma` in the finite support satisfies

```text
E_seed C_A(sigma(M))
 >=n^2 Phi_u(D_M)
   -O_u(n^(11/6)*sqrt(log(n+2))).                     (5.22)
```

This `sigma` may depend on `A` and `M`, but it is chosen before the seed and
is therefore a fixed oblivious input.  This proves the lower half of Theorem
1.

Equivalently, if

```text
U_u(M)=inf_A E_uniform placement C_A(M),              (5.23)
```

where `A` is told `M`, then the preceding argument proves
`U_u(M)>=n^2Phi_u(D_M)-o_u(n^2)`.  Conversely, a policy can privately relabel
the physical labels before running any urn policy, so the uniform-placement
and oblivious-labelling formulations have the same minimax value.  This is
the precise equivalence with the model in which the adversary chooses only a
multiset and every new access draws a uniform remaining occurrence.

## 6. Matching announced policy and finite kernel estimate

Before learning an unknown multiset, we record that the canonical fluid
schedule has a matching finite implementation.

Fix a grid distribution `D`, a low prefix containing the zero cell, and a
tested count `r`; put `q=r/n`.  Select `r` labels uniformly without
replacement.  Test them in a uniform order, processing every selected-low
positive outcome immediately after its test.  After all tests, process the
tested residual outcomes in SPT order and finally run every untested job raw.
Call this canonical template `pi` and let `Psi_D(pi)` be the right side of
(3.18), computed using the chosen low prefix.  The prefix need not be the
maximum-density prefix for this definition.

### Lemma 6.1 (finite one-/two-occurrence expansion)

Uniformly over the empirical grid distribution, low prefix, and tested count,

```text
E C_n(pi)=n^2 Psi_D(pi)+O_u(n).                       (6.1)
```

#### Proof

Let `L_i` indicate that occurrence `i` belongs to the selected low prefix,
and put `b_i=1+p_iL_i`.  If the tested occurrences in their test order are
`J_1,...,J_r`, the exact area accumulated during testing and immediate-low
processing is

```text
T_phase=sum_{k=1}^r b_{J_k}
            (n-sum_{h<k}L_{J_h}).                    (6.2)
```

Indeed, the test of `J_k`, and also its contiguous low processing operation
when present, see precisely all jobs except the selected-low outcomes
completed at earlier test positions.  Expanding (6.2) gives a one-occurrence
sum `n sum_k b_{J_k}` and, for each unordered pair of tested occurrences, the
bounded relative-order kernel

```text
(1/2)[L_i b_j+L_j b_i]                                (6.3)
```

after averaging over its two possible test orders.  Under the empirical
product law the expectation of (6.3) is `a(1+ell)`.  Thus the leading test
phase contribution is exactly

```text
n^2(1+ell)(q-aq^2/2).                                 (6.4)
```

Let `R_i=1-L_i` on positive occurrences and zero on selected zeros.  After
the tests, the known residual SPT block has exact cost

```text
(n-r) sum_{i tested} p_i R_i
+sum_{i tested} p_i R_i
+sum_{unordered tested {i,j}}
       min(p_i,p_j)R_iR_j.                            (6.5)
```

The first term is residual processing work delaying every raw job; the last
two terms are the exact SPT cost internal to the residual stock.  Their
leading contributions are

```text
n^2 q(1-q)m_R,
n^2 q^2K_R/2.                                         (6.6)
```

The internal completion cost of the `n-r` homogeneous raw jobs is exactly

```text
u(n-r)(n-r+1)/2
 =n^2u(1-q)^2/2+O_u(n).                              (6.7)
```

It remains to justify replacing finite sample coefficients by empirical
product-law values.  Every kernel above is bounded by a constant depending
only on `u`.  For distinct occurrences `i,j`, the relevant probabilities are

```text
Pr(i,j tested)       =r(r-1)/(n(n-1)),
Pr(i tested,j raw)   =r(n-r)/(n(n-1)),
Pr(i,j raw)          =(n-r)(n-r-1)/(n(n-1)).          (6.8)
```

Relative order inside a uniform block contributes a factor `1/2`.  The
coefficients in (6.8) differ uniformly by `O(1/n)` from `q^2`, `q(1-q)`, and
`(1-q)^2`.  There are fewer than `n^2` distinct ordered pairs, so replacing
all finite coefficients changes total expected cost by `O_u(n)`.  The
one-occurrence and diagonal terms contribute another `O_u(n)`.  Equations
(6.4), (6.6), and (6.7) are exactly the four terms in (3.18), proving (6.1).
`QED`

If a real fraction `q` is implemented by `r=floor(qn)`, the quadratic
`Psi_D` changes by `O_u(1/n)`, which becomes another `O_u(n)` after
multiplication by `n^2`.

For the announced multiset, compute the maximum-density grid prefix and the
minimizer (3.27), then apply Lemma 6.1.  Rounding actual positive values
upward can only lengthen the simulated known-processing operations; raw
operations remain exactly `u`.  Therefore the actual cost is no larger than
the simulated grid cost.  Together with Lemma 5.1,

```text
VAL_ann,u(M)/n^2
 <=Phi_u(D_M)+O_u(n^(-1/6)+1/n).                     (6.3)
```

Combined with (5.21), this already proves announced-multiset instance
optimality.

## 7. Removing the announcement by a pilot sample

The universal policy is not told `M`.  It uses the same growing grid as in
(5.12) and chooses

```text
k_n=ceil(n^(1/2)).                                    (7.1)
```

Draw a private uniform permutation of the public labels.

1. **Pilot.** Test its first `k_n` labels.  Sampled zeros complete; keep
   sampled positive jobs pending.
2. Round positive pilot outcomes upward and form their grid histogram
   `Dhat_n`.
3. Over all grid low prefixes containing zero and all `q in [0,1]`, minimize
   the explicit quadratic template cost.  Call a minimizer `pihat`.
4. Apply `pihat` to the remaining jobs in a fresh uniform order: test the
   chosen fraction, immediately process its selected-low outcomes, process
   the tested residual stock in SPT order, and run the untouched stock raw.
5. Finish the positive pilot jobs in SPT order.

The crude placement of the pilot jobs costs only lower order.  Put `k=k_n`,
`N=n-k`.  The pilot tests delay every main completion by at most `k`.  The
main schedule has duration at most `(1+u)N`; the positive pilot tail has
duration at most `uk`.  Hence the total pilot delay and the completion cost
of all pilot jobs are bounded by

```text
C_u n k=O_u(n^(3/2))=o(n^2).                         (7.2)
```

### 7.1 Histogram estimation

Let `D_n` be the full rounded histogram, `Dhat_n` the pilot histogram, and
`D_n^R` the histogram of the remaining `N` jobs.  Sampling without
replacement only decreases coordinate variances, so

```text
E ||Dhat_n-D_n||_1
 <=sum_j sqrt(D_{n,j}/k)
 <=sqrt((K_n+1)/k).                                  (7.3)
```

The exact mixture identity

```text
D_n=(k/n)Dhat_n+(N/n)D_n^R                           (7.4)
```

gives

```text
E ||Dhat_n-D_n^R||_1
 <=(n/N)sqrt((K_n+1)/k),
||D_n^R-D_n||_1<=2k/N.                               (7.5)
```

### 7.2 A common template family

Let `Pi_K` contain `q=0` and, for `q>0`, every grid prefix containing zero
together with every real `q in [0,1]`.  For `pi in Pi_K`, define
`Psi_D(pi)` by (3.18), using the low prefix specified by `pi` and its
complement as residual stock.

### Lemma 7.1 (template completeness)

For every grid histogram `D`,

```text
min_{pi in Pi_K} Psi_D(pi)=Phi_u(D).                  (7.6)
```

#### Proof

If `tau>=u`, the all-raw template `q=0` attains `u/2`, and Lemma 3.2 proves
that nothing is better.  If `tau<u`, Lemma 3.1 supplies a threshold low
prefix and Lemma 3.2 orders every residual class before the raw module.
Minimizing its quadratic over `q` gives `Phi_u(D)`.  A boundary grid cell at
`tau` has the same density as the full module, and moving it between the two
equal-cost knapsack items does not change the envelope, so an endpoint prefix
is sufficient.  Conversely, every template is a feasible fluid policy and
therefore cannot beat the fluid optimum. `QED`

### Lemma 7.2 (histogram Lipschitz bound)

For every fixed template and grid histograms `D,E`,

```text
|Psi_D(pi)-Psi_E(pi)|
 <=4(u+1)||D-E||_1.                                  (7.7)
```

The same bound holds for the minima over `Pi_K`.

#### Proof

Write `Delta=||D-E||_1`.  Since the template's low/residual indicators are
fixed,

```text
|a_D-a_E|<=Delta,
|ell_D-ell_E|<=u Delta,
|m_{R,D}-m_{R,E}|<=u Delta.                           (7.8)
```

For the residual pair kernel, bounded by `u`, inserting the intermediate
product measure `E x D` gives

```text
|K_{R,D}-K_{R,E}|<=2u Delta.                          (7.9)
```

Apply (7.8)--(7.9) term by term to (3.18).  The test term changes by at most

```text
[u+(1+u)/2]Delta,
```

the residual/raw cross term by at most `uDelta`, the residual pair term by
at most `uDelta`, and the raw self-term does not change.  Their sum is at
most `4(u+1)Delta`.  If `pi_D` minimizes for `D`, then

```text
min_pi Psi_E(pi)
 <=Psi_E(pi_D)
 <=Psi_D(pi_D)+4(u+1)Delta.
```

Swap `D,E` for the reverse inequality. `QED`

### 7.3 Empirical optimization

Condition on the entire pilot sample.  The learned template `pihat` is now
fixed, while the remaining permutation is uniform on the fixed remaining
multiset.  Let `pi_R` minimize for `D_n^R`.  Lemma 7.2 gives the standard
empirical-minimization sandwich

```text
Psi_{D_n^R}(pihat)
 <=Psi_{Dhat_n}(pihat)
      +C_u||Dhat_n-D_n^R||_1
 <=Psi_{Dhat_n}(pi_R)
      +C_u||Dhat_n-D_n^R||_1
 <=Phi_u(D_n^R)
      +2C_u||Dhat_n-D_n^R||_1.                       (7.10)
```

Lemma 6.1 therefore yields

```text
E[main cost | pilot]
 <=N^2[Phi_u(D_n^R)
       +2C_u||Dhat_n-D_n^R||_1]+O_u(N).              (7.11)
```

Use Lemma 7.2 and (7.5) to replace `D_n^R` by `D_n`, then take expectations,
add (7.2), and use zero-preserving rounding stability.  The normalized total
cost is at most

```text
Phi_u(D_M)
 +O_u(h_n
      +sqrt((K_n+1)/k_n)
      +k_n/n
      +1/n).                                          (7.12)
```

For `K_n=floor(n^(1/6))` and `k_n=ceil(n^(1/2))`, every displayed error is
`O_u(n^(-1/6))` or smaller.  The initial private permutation makes the law of
the policy identical against every fixed public labelling.  Thus (7.12)
proves the universal upper bound (1.1).  Combining it with the larger
growing-grid lower error in (5.21) gives (1.3).

## 8. Instance-specific competitive ratios

Define

```text
alpha_u(D)=Phi_u(D)/Omega_u(D).                       (8.1)
```

The denominator is positive by (2.6), and `Phi_u(D)<=u/2`, so `alpha_u(D)`
is uniformly bounded for fixed `u`.  Equations (2.5), (1.1), and (1.2) imply
the following equivalent multiplicative form.

> **Corollary 8.1 (multiplicative instance optimality).**  For every
> multiset `M` and every fixed labelling,
>
> ```text
> E C_{A*_{n,u}}(sigma(M))
>  <=alpha_u(D_M) OPT_u(M)+o_u(n^2).                  (8.2)
> ```
>
> Conversely, for every randomized policy, even one told `M`, some fixed
> oblivious labelling satisfies
>
> ```text
> E C_A(sigma(M))
>  >=alpha_u(D_M) OPT_u(M)-o_u(n^2).                  (8.3)
> ```

Indeed, `n^2Phi_u=alpha_u n^2Omega_u`, while the diagonal correction in
(2.5) is `O_u(n)`.  Its product with `alpha_u` is still `O_u(n)`.

Consequently the exact asymptotic randomized competitive curve for the
common-upper model is the distributional optimization

```text
R_rand(u)=sup_D Phi_u(D)/Omega_u(D),                  (8.4)
```

where it is enough to take finite-support distributions, or limits of
empirical distributions.  We now solve this outer optimization exactly.

Let `u_0` be the unique real root greater than one of

```text
u_0^3-6u_0^2+5u_0-1=0,
u_0=5.04891733952231... .                             (8.5)
```

Equivalently, `sqrt(u_0)` is the root greater than two of
`t^3-2t^2-t+1=0`.  Uniqueness above one follows directly from the two
critical points of the cubic in (8.5): its larger critical point is below
four, the value at four is negative, and the polynomial is strictly
increasing thereafter.

> **Theorem 8.2 (exact randomized common-upper curve).**  The exact
> size-asymptotic randomized competitive ratio against an oblivious
> adversary is
>
> ```text
>                  { 1,                                  0<u<=1,
>                  {
> R_rand(u)=       { u^3/(u^3-2u^2+3u-1),              1<=u<=u_0,
>                  {
>                  { 1+1/[2(sqrt(u)-1)],                u_0<=u<=25/4,
>                  {
>                  { 4/3,                               u>=25/4.
>                                                               (8.6)
> ```
>
> The global maximum over all common upper bounds is attained at
>
> ```text
> u=(3+sqrt(3))/2=2.3660254037...                      (8.7)
> ```
>
> and equals
>
> ```text
> (27+6sqrt(3))/23=1.6257523846... .                  (8.8)
> ```

The proof occupies the rest of this section.  Its main point is that the
outer optimization over arbitrary probability distributions has an exact
one-dimensional reduction.

### 8.1 Survival-function representation

Assume first that `u>1`.  For `P~D`, let

```text
s(t)=Pr[P>=t],                                        (8.9)
```

where changing endpoint conventions at atoms does not affect any integral.
Extend `s` by zero beyond `u`.  It is nonincreasing and takes values in
`[0,1]`.  The threshold equation (3.4) is equivalent to

```text
integral_0^tau s(t)dt=tau-1.                         (8.10)
```

Indeed, layer-cake integration gives

```text
E[(tau-P)^+]
 =integral_0^tau Pr[P<t]dt
 =tau-integral_0^tau s(t)dt.                         (8.11)
```

Define the doubled offline coefficient

```text
Ocal_u(D)=2Omega_u(D).                                (8.12)
```

Since `s_u(P)=min{u,1+P}` is at least one and
`s_u(P)>=x` for `1<=x<=u` exactly when `P>=x-1`, another layer-cake identity
gives

```text
Ocal_u(D)=1+integral_0^(u-1) s(t)^2dt.                (8.13)
```

There are two particularly simple feasible online policies: run everything
raw, of doubled leading cost `u`, or test everything using the stationary
threshold policy.  For the latter, every selected-low outcome behaves in the
fluid SPT calculation as an item of cost `tau`, while every residual outcome
keeps its cost `p>=tau`.  Thus its effective item is

```text
Z=max{P,tau}.                                         (8.14)
```

If `T_u(D)` is the leading cost of this test-all policy and
`Tcal_u(D)=2T_u(D)`, then

```text
Tcal_u(D)
 = E[min(Z,Z')]
 = tau+integral_tau^u s(t)^2dt,       if tau<=u,
 = tau,                               if tau>=u,       (8.15)
```

for independent `Z,Z'`.  Because `Phi_u` minimizes over `q` and contains
both endpoint policies,

```text
Phi_u(D)/Omega_u(D)
 <=min{u,Tcal_u(D)}/Ocal_u(D).                        (8.16)
```

We shall maximize the right side exactly.  The hard distributions found
below have endpoint-optimal `q`, so (8.16) loses nothing in the supremum.

### 8.2 Flattening the prefix

First suppose `1<=tau<=u` and put

```text
y=(tau-1)/tau.                                        (8.17)
```

Equation (8.10) says that the average of `s` on `[0,tau]` is `y`.  Since
`s` is nonincreasing, its average on every initial subinterval is at least
`y`.  Hence, for every `0<a<=tau`, Cauchy--Schwarz gives

```text
integral_0^a s(t)^2dt>=a y^2.                        (8.18)
```

Moreover, `s(t)<=y` almost everywhere for `t>tau`: the terminal value of a
nonincreasing function cannot exceed its average over the preceding prefix.

Replace `s` on `[0,tau]` by the constant `y` and leave its tail unchanged.
The result is still a valid nonincreasing survival function: it has an atom
of mass `1-y` at zero and its tail starts at a value at most `y`.  It still
satisfies (8.10), leaves `Tcal` unchanged, and by (8.18) weakly decreases
`Ocal`.  Therefore, for fixed `tau`, the ratio in (8.16) is maximized only
after this flattening.  We may henceforth assume

```text
s(t)=y for 0<t<tau.                                  (8.19)
```

Write `g(t)=s(t)^2` on the remaining interval.  Then `g` is nonincreasing
and `0<=g<=y^2`.

If `u-1<=tau<=u`, the denominator interval lies entirely in the flattened
prefix, while the numerator increases with every tail value.  Consequently

```text
min{u,Tcal}/Ocal
 <= [tau+(u-tau)y^2]/[1+(u-1)y^2].                   (8.20)
```

The numerator in (8.20) is at most `u`, so the minimum with `u` is inactive.
Equality is obtained by taking `g=y^2` on the entire tail, namely by the
binary distribution with mass `1-y=1/tau` at zero and mass `y` at `u`.

Now suppose `tau<u-1`.  Put

```text
L=u-1-tau,
E=integral_tau^(u-1) g(t)dt,
H=integral_(u-1)^u g(t)dt.                            (8.21)
```

Monotonicity says that the average on the later unit interval is no larger
than the average on the preceding interval of length `L`.  Therefore

```text
H<=E/L,
0<=E<=L y^2.                                         (8.22)
```

Using (8.13), (8.15), and (8.22),

```text
min{u,Tcal}/Ocal
 <= [tau+((u-tau)/(u-1-tau))E]
       /[1+tau y^2+E].                               (8.23)
```

Again the numerator is at most `tau+(u-tau)y^2<=u`.  The right side of
(8.23) is a linear-fractional function of `E`, so its derivative has constant
sign.  Its maximum on `[0,Ly^2]` is attained at an endpoint.

At `E=0`, monotonicity also forces `H=0`; the survival function is the
rectangle of height `y` ending at `tau`.  At `E=Ly^2`, equality throughout
(8.22) is attained by extending the same rectangle through `u`.  Thus every
distribution with threshold `tau<=u` is bounded by one of two binary
families:

```text
A(tau)=tau/[1+tau y^2]
      =tau^2/(tau^2-tau+1),                           (8.24)

B_u(tau)=[tau+(u-tau)y^2]/[1+(u-1)y^2],              (8.25)
```

where `A(tau)` is available only for `tau<=u-1`, while `B_u(tau)` is
available for every `1<=tau<=u`.

It remains to cover `tau>u`.  In that regime (8.10) and the zero extension
of `s` give

```text
integral_0^u s(t)dt=tau-1>=u-1.                      (8.26)
```

The average of a nonincreasing function on `[0,u-1]` is no smaller than its
average on `[0,u]`.  Cauchy--Schwarz therefore yields

```text
integral_0^(u-1)s(t)^2dt
 >=(u-1)((tau-1)/u)^2
 >=(u-1)^3/u^2.                                      (8.27)
```

Here `Tcal=tau>u`, so the raw endpoint is chosen.  Equations (8.13) and
(8.27) show that its ratio is no larger than `B_u(u)`.  We have proved the
exact reduction

```text
sup_D min{u,Tcal_u(D)}/Ocal_u(D)
 =max { sup_{1<=tau<=u-1} A(tau),
        sup_{1<=tau<=u}   B_u(tau) },                 (8.28)
```

with the first supremum omitted when `u<2`.  Both sides are attained by
two-point distributions.  Together with (8.16), (8.28) is the desired upper
reduction.

### 8.3 Solving the two scalar maximizations

The first family is elementary:

```text
A'(tau)=tau(2-tau)/(tau^2-tau+1)^2.                  (8.29)
```

Hence its maximum is at `tau=min{2,u-1}` and equals `4/3` as soon as
`u>=3`.

For the second family, substitution of `y=(tau-1)/tau` gives

```text
B_u(tau)
 =[tau^2 u+2tau^2-2tau u-tau+u]
   /[tau^2u-2tau u+2tau+u-1].                        (8.30)
```

The sign of its derivative is the sign of

```text
g_u(tau)=(4-u)tau^2+(2u-4)tau+1-u
          =(2tau-1)^2-u(tau-1)^2.                   (8.31)
```

We have `g_u(1)=1`.  If `u<=4`, the last expression in (8.31) is positive
for every finite `tau>=1`.  For `u>4`, its only root above one is

```text
tau_*(u)
 =(u-2+sqrt(u))/(u-4)
 =(sqrt(u)-1)/(sqrt(u)-2).                            (8.32)
```

The derivative is positive before this root and negative afterwards.  The
condition `tau_*(u)=u` is exactly (8.5).  Thus the maximum of `B_u` is at
`tau=u` until `u=u_0`, and at `tau=tau_*(u)` afterwards.  The two values
simplify to

```text
B_u(u)=u^3/(u^3-2u^2+3u-1),                          (8.33)

B_u(tau_*(u))=1+1/[2(sqrt(u)-1)].                    (8.34)
```

For completeness, the comparison with the `A` family has no hidden
optimization.  On `2<=u<=3`, subtracting `A(u-1)` from `B_u(u)` has, after
clearing positive denominators and writing `v=u-2`, numerator

```text
v^4+3v^3+3v^2+3v+3>0.                                (8.35)
```

On `3<=u<=u_0`, `B_u(u)>4/3`; after clearing denominators this is
`-u^3+8u^2-12u+4>0`, which follows by elementary derivative inspection on
that interval and the identity
`u_0^3=6u_0^2-5u_0+1`.  On `u_0<=u<=25/4`, (8.34) is at least `4/3`.
It equals `4/3` exactly when `sqrt(u)=5/2`, and is smaller afterwards.
Equations (8.29)--(8.35) therefore give precisely the upper bound (8.6).

### 8.4 Matching distributions

It remains to verify that the endpoint upper bound (8.16) is exact on every
branch.

For `1<u<=u_0`, take

```text
D=(1/u) delta_0+(1-1/u)delta_u.                      (8.36)
```

Its threshold is `tau=u`.  Hence raw execution is fluid-optimal and

```text
Phi_u(D)=u/2,
2Omega_u(D)=1+(u-1)(1-1/u)^2.                        (8.37)
```

Their ratio is (8.33).

For `u_0<=u<=25/4`, put `t=sqrt(u)` and take

```text
D=z delta_0+(1-z)delta_u,
z=(t-2)/(t-1),
tau=1/z=(t-1)/(t-2).                                 (8.38)
```

For a general binary distribution `z delta_0+(1-z)delta_u` with `uz>=1`,
the fixed-`q` quadratic (3.24) becomes

```text
F(q)=u/2+(1-uz)q+[z(uz-1)/2]q^2.                    (8.39)
```

Its derivative is

```text
F'(q)=-(uz-1)(1-zq)<=0                               (8.40)
```

on `[0,1]`.  Therefore `q=1` is optimal.  Substituting (8.38) into
`F(1)/Omega_u(D)` gives (8.34).

Finally, for `u>=25/4`, take

```text
D=(1/2)delta_0+(1/2)delta_2.                         (8.41)
```

Here `tau=2`, and

```text
F(q)=u/2+(2-u)q+(u-2)q^2/2.                         (8.42)
```

Thus `q=1` is optimal, `Phi_u(D)=1`, and the offline effective lengths are
one and three with equal mass.  Consequently

```text
Omega_u(D)=3/4,
Phi_u(D)/Omega_u(D)=4/3.                             (8.43)
```

The weights in (8.36), (8.38), and (8.41) may be approximated by rational
empirical frequencies.  The uniform error in Theorem 1 and continuity of
the displayed finite formulas then turn them into fixed oblivious lower-bound
sequences.  Thus the distributional upper bound is the actual randomized
competitive ratio, proving Theorem 8.2.

If `0<u<=1`, every test-plus-processing alternative has length at least one
while raw execution has length `u`.  Therefore `Phi_u(D)=Omega_u(D)=u/2`
for every `D`, proving the first branch.

Finally, differentiating (8.33) gives a numerator proportional to

```text
-u^2(2u^2-6u+3).                                    (8.44)
```

The only critical point above one before `u_0` is (8.7); the remaining
branches are decreasing until the final plateau.  Substitution yields (8.8).

## 9. What is genuinely new relative to blind execution

The proof parallels the bounded blind-actual-time theorem, but it is not a
literal specialization.  In that theorem an untouched blind job runs for
its hidden `p`, reveals `p` through its duration, and creates a blind module
of fluid cost `mu=E[P]`.  Here a raw job always runs for the public upper
bound `u` and does not reveal `p`.  The corresponding changes are:

1. replace the blind item of cost `mu` by a raw item of cost `u`;
2. every residual tested value satisfies `p<=u`, so the entire residual SPT
   stock precedes the raw block and there is no high tail;
3. predictable concentration is needed only for tested class counts, not for
   blind work;
4. the trace bijection uses hidden occurrence tokens after raw touches, even
   though those values are absent from the policy's observable history;
5. the clairvoyant coefficient is bounded away from zero, so the additive
   theorem immediately yields per-instance multiplicative ratios.

These simplifications are exactly why sublinear sampling lets a universal
randomized policy behave, at the `n^2` scale, as though the multiset had been
announced.

## 10. Conclusion

For a known common upper bound `u`, the leading optimal online cost of every
multiset is determined by one threshold and one scalar optimization:

```text
E[(tau-P)^+]=1,
Phi_u(D)=min_{0<=q<=1} F_{u,D}(q).                    (10.1)
```

The canonical policy tests a fraction `q`, immediately completes outcomes
below `tau`, drains every tested residual outcome in SPT order, and finally
runs the untouched jobs raw.  The completion envelope proves this structure
against arbitrary adaptive announced policies.  The trace bijection and a
single simultaneous urn event allow the realized adaptive stopping fraction
to be substituted pathwise.  A growing zero-preserving grid makes the bound
uniform over all bounded multisets, and an `o(n)` pilot removes the
announcement.

Thus, up to additive `o_u(n^2)`, knowing the multiset in advance gives no
advantage to a randomized policy against an oblivious adversary, and the
instance-specific competitive ratio is the explicit quantity
`alpha_u(D_M)=Phi_u(D_M)/Omega_u(D_M)`.  Maximizing this quantity gives the
four-branch curve (8.6).  The hard distributions are binary throughout:
`{0,u}` with zero mass `1/u`, then `{0,u}` with zero mass
`(sqrt(u)-2)/(sqrt(u)-1)`, and finally the balanced distribution on
`{0,2}`.  The exact worst common upper bound is `(3+sqrt(3))/2`, where the
randomized ratio is `1.6257523846...`.
