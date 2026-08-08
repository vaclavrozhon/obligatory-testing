# Instance-optimal randomized optional testing against an oblivious adversary

Self-contained, paper-grade proof, 8 August 2026.

## 1. Model and main theorem

There are `n` labelled nonpreemptive jobs on one machine.  Job `i` has an
unknown processing time `p_i in [0,L]`, where `L<infinity` is fixed and known.
At any idle time a nonanticipating policy may do one of three things:

1. run an untouched job blindly for `p_i` time, completing it and observing
   `p_i`;
2. test an untouched job for one unit of time, observing `p_i`;
3. process a previously tested positive job for `p_i` time.

A tested zero job completes at the end of its test.  Processing a tested zero
afterwards, if the formal scheduler uses such an administrative operation,
takes no time and does not complete the job a second time.  The objective is
the sum of completion times.

The adversary is oblivious: before the policy draws its random bits it fixes a
labelled vector `p`.  Let `M` be the underlying multiset and let `D_M` be its
empirical probability distribution.  All distributions below are finite
empirical distributions; no measure-theoretic approximation is hidden in the
statement.

We define an instance-specific fluid benchmark `Phi(D)` in Section 2.  The
definition is explicit: for each tested fraction `q`, `F_D(q)` is the cost of
a threshold-testing / known-medium / blind / known-high fluid schedule, and

```text
Phi(D) = min_{0<=q<=1} F_D(q).                         (1.1)
```

> **Theorem 1 (instance-optimality at the quadratic scale).**  For every
> fixed `L<infinity` there are a sequence `epsilon_L(n)->0` and randomized
> nonanticipating policies `A*_{n,L}`, depending only on `n,L`, with the
> following properties for every size-`n` multiset `M subseteq [0,L]`.
>
> **Universal upper bound.**  For every fixed labelling `sigma(M)`,
>
> ```text
> E C_{A*_{n,L}}(sigma(M))
>     <= n^2 Phi(D_M)+epsilon_L(n)n^2.                 (1.2)
> ```
>
> **Announced-multiset lower bound.**  For every randomized
> nonanticipating policy `A`, even if `A` is told `M`, some fixed labelling
> `sigma(M)` satisfies
>
> ```text
> E C_A(sigma(M))
>     >= n^2 Phi(D_M)-epsilon_L(n)n^2.                 (1.3)
> ```
>
> The expectation is only over the policy's private randomness.  The
> labelling in (1.3) is selected before those random bits and is therefore an
> oblivious input.

Policies are required to complete all jobs.  A policy that fails to do so has
infinite objective and is irrelevant to the lower bound.  The theorem is an
additive `o(n^2)` statement.  It deliberately does not claim a bounded ratio
to the clairvoyant SPT optimum on instances whose optimum is `o(n^2)`.

The proof gives, with unoptimized constants depending only on `L`,

```text
epsilon_L(n)=O_L(n^(-1/6)*sqrt(log(n+2))).             (1.4)
```

The rest of the document proves Theorem 1.  A single event controls all touch
prefixes, the realized tested fraction is substituted pathwise, and only then
are expectations taken.

## 2. The deterministic fluid benchmark

Let `D` be a finite probability distribution on `[0,L]`.  Write

```text
mu = E_D[P].                                           (2.1)
```

The case `mu=0` is trivial: every job is zero, blind execution costs no time,
and we set `Phi(D)=0`.  Henceforth assume `mu>0`.

### 2.1 The maximum-density test module

Write `D_0=Pr[P=0]`.  For every selection rule `g` on the positive support,
with `0<=g(p)<=1`, define

```text
A(g) = D_0 + E[g(P) 1{P>0}],
W(g) = 1   + E[P g(P) 1{P>0}].                        (2.2)
```

One unit mass of tests together with immediate processing of the selected
positive outcomes completes mass `A(g)` and uses work `W(g)`.  Define

```text
rho(D) = max_g A(g)/W(g),
tau(D) = 1/rho(D).                                    (2.3)
```

The maximum exists because the support is finite and the box of selection
vectors is compact.  Also `A(g)>0` for some `g`, because `D` has positive
total mass, so `tau` is finite and positive.

### Lemma 2.1 (threshold form of a maximum-density module)

There is a maximizer `g*` such that

```text
g*(p)=1  if p<tau,
g*(p)=0  if p>tau,                                    (2.4)
```

with an arbitrary fraction of an atom at `p=tau`.  If

```text
a   = A(g*),
ell = E[P g*(P) 1{P>0}],
w   = 1+ell,
```

then

```text
w=a*tau,
E[(tau-P)^+]=1.                                      (2.5)
```

#### Proof

Let `rho=A(g*)/W(g*)` and `tau=1/rho=W(g*)/A(g*)`.
Increasing a coordinate of mass at value `p` by `d>0` changes the numerator
by `d` and the denominator by `pd`.  Cross multiplication shows that the
density increases exactly when

```text
p < W(g*)/A(g*)=tau.
```

Thus a maximizing vector can leave no positive mass unselected below `tau`.
The reverse perturbation shows that it can select no positive mass above
`tau`.  A coordinate at equality is neutral.  This proves (2.4).  The first
identity in (2.5) is the definition of `tau`.  Expanding it and cancelling
the neutral boundary atom gives

```text
1 = tau*D_0 + E[(tau-P)1{0<P<tau}]
  = E[(tau-P)^+].
```

`QED`

The same argument gives a form that will be used repeatedly.  For every
other selection `0<=h<=1`,

```text
tau [D_0+E[h(P)1{P>0}]]
    <= 1+E[P h(P)1{P>0}].                             (2.6)
```

Thus the full test module has the greatest completion density among all
possible test-plus-immediate-processing modules.

### 2.2 The fixed-tested-fraction completion envelope

Fix `q in [0,1]`.  Split a possible boundary atom at `tau` into two virtual
classes according to `g*`.  Let `R_i` be the residual mass of positive class
`i`, after removing the selected part of that class.  Then

```text
sum_i R_i = 1-a,
p_i >= tau whenever R_i>0.                            (2.7)
```

At a prefix of an arbitrary fluid schedule write

```text
t   = mass tested so far,
b   = mass completed blindly so far,
c_i = mass of tested positive class i already processed.             (2.8)
```

The completed mass and ideal work are

```text
y = D_0 t+b+sum_i c_i,
x = t+mu*b+sum_i p_i c_i.                             (2.9)
```

Every prefix of a policy whose final tested mass is `q` satisfies

```text
0<=t<=q,
0<=b<=1-q,
0<=c_i<=D_i t.                                        (2.10)
```

Let `H_{D,q}(x)` be the maximum of (2.9)'s completed mass over the finite
linear program (2.10) with ideal work at most `x`.  Extend `H_{D,q}` by zero
to negative `x` and by one after all unit job mass can be completed.

### Lemma 2.2 (exact fractional-knapsack envelope)

The envelope `H_{D,q}` is the ordinary divisible-knapsack completion curve
for the following items:

| item | completion capacity | work per completion |
|---|---:|---:|
| maximum-density test module | `a q` | `tau` |
| residual positive class `i` | `q R_i` | `p_i` |
| untouched blind jobs | `1-q` | `mu` |

In particular, in the regime `tau<mu`, the pointwise-optimal order is

```text
test module
-> residual known classes p_i<mu in SPT order
-> blind block
-> residual known classes p_i>mu in SPT order,        (2.11)
```

with arbitrary tie breaking at `tau` and `mu`.

#### Proof

Take any feasible prefix `(t,b,c)`.  If a boundary atom at `tau` was split,
allocate its processed mass first to the selected virtual copy, up to its
capacity at test mass `t`, and allocate the rest to the residual copy.  If
the original processed boundary mass is `c`, this is

```text
c^L=min(c,g*(tau)D_tau t),
c^R=c-c^L.
```

Then `c^L` and `c^R` obey their separate revelation constraints, because
`c<=D_tau t`.

Let `y_L` and `x_L` be the completed mass and work formed by the tests, the
tested zeros, and all processed selected-low virtual classes.  For `t>0`,
divide the processed selected-low masses by `t` and apply (2.6); for `t=0`
the assertion is trivial.  We obtain

```text
tau*y_L <= x_L,
y_L<=a t.                                             (2.12)
```

Put `lambda=y_L/a`.  Then

```text
0<=lambda<=t<=q,
lambda*a=y_L,
lambda*w=tau*y_L<=x_L.                                (2.13)
```

Consequently the entire low part can be replaced by `y_L` units of completed
test-module mass, of work `tau*y_L`, without losing a completion or using
more work.  Every residual processed class has capacity at most `qR_i`, and
the blind completed mass has capacity at most `1-q`.  This embeds every
feasible prefix in the displayed ordinary fractional knapsack.

Conversely, consider the greedy trajectory of that knapsack.  While it is
partway through the test-module item, run the corresponding fraction of the
`q` tests and process exactly the selected outcomes.  No residual item is
used.  Once all `q` test modules have run, every residual capacity `qR_i` is
available, and the remaining items can be processed in increasing cost.
Thus every point of the greedy knapsack trajectory is feasible in the
original fluid relaxation.

For completeness, the ordinary fractional-knapsack fact used here is the
following elementary exchange argument.  In a maximizing allocation, if an
item of cost `c_2` is used while an item of smaller cost `c_1` is not full,
move a sufficiently small amount of work from the former to the latter.
The completed mass strictly increases because `1/c_1>1/c_2`.  Compactness of
the finite capacity box supplies a maximizer, so iterating the exchange shows
that every maximizer fills items in nondecreasing cost order, with at most
one partially filled cost level.  This also proves pointwise equality of the
two envelopes, not only equality of their terminal work.

Finally, (2.7) and `tau<mu` put the module first and the blind item exactly at
cost `mu`, yielding (2.11).  `QED`

### 2.3 Area of the greedy envelope

In the short-test regime `tau<mu`, partition the residual positive mass into

```text
M={i: tau<=p_i<mu},
H={i: p_i>mu},                                        (2.14)
```

with a virtual copy of any atom at `mu` assigned arbitrarily to either side.
Thus the displayed strict inequalities are shorthand for an exhaustive
partition after this tie assignment.  Define

```text
m   = sum_{i in M} p_i R_i,
d   = sum_{i in H} R_i,
K_M = sum_{i,j in M} min(p_i,p_j) R_i R_j,
K_H = sum_{i,j in H} min(p_i,p_j) R_i R_j.            (2.15)
```

### Lemma 2.3 (fixed-`q` value)

For `tau<mu`,

```text
integral_0^(q+mu) [1-H_{D,q}(x)] dx = F_D(q),         (2.16)
```

where

```text
F_D(q)
 = (1+ell)(q-aq^2/2)
   + q m ((1-q)+qd) + q^2 K_M/2
   + mu ((1-q)qd+(1-q)^2/2)
   + q^2 K_H/2.                                      (2.17)
```

#### Proof

A homogeneous divisible block of mass `v`, cost `c` per completion, and
later unfinished mass `r` contributes

```text
c(vr+v^2/2)                                           (2.18)
```

to the remaining-mass area.  The test module has mass `aq`, cost `tau`, and
later mass `1-aq`.  Its contribution is

```text
tau[aq(1-aq)+(aq)^2/2]
  = tau(aq-a^2q^2/2)
  = (1+ell)(q-aq^2/2).                                (2.19)
```

For divisible deterministic classes of masses `v_i` processed in SPT order,
their internal area is

```text
(1/2) sum_{i,j} min(p_i,p_j)v_i v_j.                  (2.20)
```

Indeed, after sorting, every distinct pair is charged the smaller processing
time and every diagonal class contributes half of its rectangular
self-interaction.  Formula (2.20) also follows by expanding (2.18) class by
class.

The medium stock has masses `qR_i`.  Its total work `qm` delays the untouched
mass `1-q` and high mass `qd`, while (2.20) gives internal area `q^2K_M/2`.
The blind block has mass `1-q`, cost `mu`, and later mass `qd`.  The high
stock contributes only its internal SPT area `q^2K_H/2`.  Adding these four
contributions gives (2.17).  The total knapsack work is

```text
tau*aq + q sum_i p_i R_i + mu(1-q)
  = q(1+ell)+q(mu-ell)+mu(1-q)
  = q+mu,                                             (2.21)
```

so the integration horizon in (2.16) is exact.  `QED`

### Lemma 2.4 (long-test regime)

If `tau>=mu`, every fluid policy has cost at least `mu/2`, and pure blind
execution attains `mu/2`.

#### Proof

In the fractional relaxation, the module costs `tau>=mu`, every residual
class costs at least `tau`, and the blind item costs `mu`.  Hence every
completed unit costs at least `mu`, so `H_{D,q}(x)<=min(1,x/mu)`.  Integrating
the resulting triangular remaining-mass lower envelope gives `mu/2`.  With
`q=0`, the all-blind block has mass one and cost `mu`, attaining equality.
`QED`

We now define

```text
Phi(D) = min_{0<=q<=1} F_D(q)       if tau<mu,
Phi(D) = mu/2                       if tau>=mu,
Phi(D) = 0                          if mu=0.           (2.22)
```

The minimum exists because (2.17) is a quadratic polynomial on a compact
interval.  Lemmas 2.2--2.4 prove a stronger structural statement:

> **Fixed-fraction fluid theorem.**  Every fluid policy whose realized final
> tested fraction is `q` costs at least `F_D(q)` in the short regime, and the
> four-block policy (2.11) attains equality.  Therefore allowing `q` to be
> random or adaptively selected cannot beat `Phi(D)`.

No exchange of nodes in an adaptive decision tree is used in this theorem.

## 3. Adaptive first touches are a uniform urn

We next pass from an arbitrary finite policy to the without-replacement urn
used in the concentration argument.  This step is exact and contains no
conditional-probability approximation.

Distinguish the `n` occurrences of the multiset, even when several have the
same processing time.  Let both the public labels and the hidden occurrence
tokens be copies of `{1,...,n}`.  A placement `sigma` is a permutation:
public label `i` has processing time `p(sigma(i))`.

Fix a deterministic completing policy `A`.  In its run on placement `sigma`,
list the public labels in order of their first touch, where a first touch is
either a test or a blind execution:

```text
ell_1(sigma),...,ell_n(sigma).                         (3.1)
```

The list is a permutation, because a legal completing run first-touches every
job exactly once.  Record also `kind_k(sigma) in {test,blind}`.  Define the
hidden reveal order

```text
R_A(sigma)_k = sigma(ell_k(sigma)).                    (3.2)
```

### Lemma 3.1 (trace bijection)

The map `R_A` is a bijection of the finite placement space.  After
reparametrizing by `r=R_A(sigma)`, the indicator

```text
A_k(r)=1{kind_k(R_A^{-1}(r))=test}                    (3.3)
```

is predictable: it is determined by the processing times revealed in
positions `1,...,k-1`.  Consequently, a uniform random placement induces a
uniform random occurrence permutation `r` and a predictable test/blind
selector on that permutation.

#### Proof

The scheduler-specific fact is prefix causality.  We prove the following
slightly stronger invariant by induction on the number of first touches.  If
two runs have revealed the same processing-time sequence through their first
`k-1` first touches, then they have used the same public labels and action
kinds at those touches, and their complete visible transcripts immediately
after touch `k-1` are identical.

The base case is the common initial transcript.  For the induction step,
start from identical transcripts.  A deterministic policy issues the same
next command in both runs.  If the command processes a pending known job, it
uses the same public label and the already recorded same length, reveals no
new input, and leaves identical transcripts; repeat this argument through
all such intervening commands.  The next command that first-touches an
unknown label is therefore the same public label and the same kind
`test/blind` in both runs.  These choices are recorded before its unknown
length is exposed.  By the hypothesis on the reveal sequences, the two new
lengths agree, so the two updated test or blind-completion records agree as
well.  This closes the induction and, in particular, gives

```text
ell_k(sigma)=ell_k(sigma'),
kind_k(sigma)=kind_k(sigma').                          (3.4)
```

The observation produced by a blind execution must include its elapsed
processing time; this is the only model detail needed in the induction.

To prove injectivity, suppose `R_A(sigma)=R_A(sigma')`.  By induction on `k`,
the equality of the first `k-1` revealed values and (3.4) imply that the two
runs use the same `k`-th public label, call it `ell_k`.  Then

```text
sigma(ell_k)=R_A(sigma)_k
            =R_A(sigma')_k
            =sigma'(ell_k).                           (3.5)
```

The labels `ell_k` exhaust the public label set, so `sigma=sigma'`.  Thus
`R_A` is injective.  An injective self-map of a finite set is bijective.
Reindexing the uniform sum by this bijection proves uniformity of `r`.

Finally, apply prefix causality to `R_A^{-1}(r)` and `R_A^{-1}(r')`.  If `r`
and `r'` expose the same processing times before position `k`, (3.4) gives
the same action kind at `k`, proving predictability of (3.3).  `QED`

The reparametrization preserves the prefix statistics needed below exactly.
For every class `j` and every first-touch prefix `m`,

```text
number of tests through m
  =sum_{k<=m} A_k(r),                                 (3.5a)

number of tested class-j occurrences through m
  =sum_{k<=m} A_k(r)1{r_k in j},                     (3.5b)

processing work of blind occurrences through m
  =sum_{k<=m}(1-A_k(r))p(r_k).                       (3.5c)
```

Processing pending known jobs between two first touches changes none of
these three identities.  Thus the trace bijection loses no scheduler
information needed by the urn argument.

Randomized policies are handled seedwise.  For each fixed private seed there
is a different bijection and selector, but every concentration estimate below
is uniform over all predictable selectors.

### Lemma 3.2 (simultaneous predictable-urn discrepancy)

Let the `n` occurrences carry fixed attributes, including values
`v_1,...,v_n in [0,L]` and a partition into `K+1` classes, and let `D_j` be
the population fraction of class `j`.  Let `r` be a uniform random
permutation and let `A_k in {0,1}` be any selector measurable with respect to
the complete attributes of occurrences `r_1,...,r_{k-1}`.  In particular,
the selector may use the exact earlier processing times even when the
classes and the `v_i` used in the estimate are rounded versions of them.
Fix `0<delta<1/2` and put

```text
N_delta=floor((1-delta)n),
e=sqrt(8n log(2n(K+2))),
Gamma=(1+1/delta)e.                                   (3.6)
```

With probability at least `1-beta_n`, where

```text
beta_n <= C (K+2)[2n(K+2)]^(-3),                     (3.7)
```

the following hold simultaneously for every `m<=N_delta` and every class
`j`:

```text
|sum_{k<=m} A_k 1{r_k in j} - D_j sum_{k<=m} A_k|
    <= Gamma,                                         (3.8)

|sum_{k<=m} (1-A_k)v_{r_k}
      - mu sum_{k<=m}(1-A_k)|
    <= L Gamma,                                       (3.9)
```

where `mu=n^{-1}sum_i v_i`.  The constant `C` is universal.  The same event
works for all prefixes; no stopping time is conditioned upon.

#### Proof

For a fixed class, ordinary sampling-without-replacement Hoeffding bounds and
a union bound over all `m<=n` give

```text
max_m |#{k<=m:r_k in j}-mD_j| <= e                    (3.10)
```

except with probability at most `2n exp(-2e^2/n)`.  The identical bound,
after division by `L`, applies to prefix sums of the bounded values `v_i`.
Union bound over the classes and the value sum is absorbed by (3.7).

Let `R_{k-1,j}` be the fraction of class `j` in the urn immediately before
draw `k`.  For `k<=N_delta`, (3.10) implies

```text
|R_{k-1,j}-D_j| <= e/(delta n).                       (3.11)
```

Since `A_k` is chosen before draw `k`, even in this enlarged filtration,

```text
M_m=sum_{k<=m} A_k(1{r_k in j}-R_{k-1,j})             (3.12)
```

is a martingale with increments bounded by one.  The maximal
Azuma--Hoeffding inequality gives

```text
Pr[max_{m<=N_delta}|M_m|>e]
    <=2 exp(-e^2/(2n)).                               (3.13)
```

Combining (3.11)--(3.13), uniformly in `m`,

```text
|sum_{k<=m} A_k(1{r_k in j}-D_j)|
 <= e + n*e/(delta n)=Gamma.                          (3.14)
```

For (3.9), use the predictable selector `1-A_k`, replace the class indicator
by `v_{r_k}`, and replace the remaining class fraction by the remaining-urn
mean.  Its martingale increments are bounded by `L`, and (3.10) gives
remaining-mean drift at most `Le/(delta n)`.  The same calculation yields
`LGamma`.  A final union bound proves (3.7)--(3.9).  `QED`

## 4. Finite announced multisets: lower bound for every adaptive policy

This section uses Lemmas 2.2 and 3.2 to lower-bound an arbitrary policy.  We
work directly with a growing grid, because this is the form needed for the
uniform theorem.

Assume `L>0`.  Keep zero as a separate class and partition `(0,L]` into `K`
intervals of width

```text
h=L/K.                                                (4.1)
```

Round a positive processing time upward to the right endpoint of its bin;
write `u_i` for the rounded value of occurrence `i`, `D^g` for the empirical
grid distribution, and `mu_g=n^{-1}sum_i u_i`.  Then

```text
p_i<=u_i<=p_i+h,
p_i=0 iff u_i=0.                                      (4.2)
```

### 4.1 Removing the uncontrolled suffix

Fix a deterministic completing policy and a realized placement.  Policies
may be assumed non-idling: deleting idle intervals preserves feasibility and
can only decrease every completion time.  Let
`N_delta=floor((1-delta)n)`.  Modify its realized schedule word as follows.
For every job whose first touch is after position `N_delta`, replace a test
first touch by a blind execution at that position and delete the later known
processing operation of that job.  A suffix job that was already blind is
unchanged.  Keep the relative order of every other operation.  Call the
result the edited schedule.

The edited word is feasible: each changed suffix job is untouched at its
replacement operation and is completed there; only its now-redundant later
processing is deleted.  All tests of the edited schedule occur in the
controlled first-touch prefix.  Let `q` be their number divided by `n`.
Exactly `1-q` job mass is executed blindly.

### Lemma 4.1 (suffix-edit cost)

There is a constant `c_L`, depending only on `L`, such that pathwise

```text
|C_original-C_edited|
    <= c_L(delta*n^2+n).                              (4.3)
```

#### Proof

At most `delta n+1` jobs are changed.  A job contributes at most one test and
one processing operation, each of length at most `B=max{1,L}`.  Use the
pair-delay decomposition of total completion time: an operation of length
`d` contributes `d` once for each job that is unfinished during it.  Deleting
or inserting one operation changes this contribution by at most `Bn`.
Moving the completion record of one changed job across the unchanged word
changes its completion time by at most the total word length, at most `2Bn`.
Thus changing one job costs at most a universal multiple of `Bn`; summing
over the suffix jobs proves (4.3).  Zero-duration administrative operations
contribute nothing.  `QED`

### 4.2 Every physical prefix fits the repaired fluid envelope

Work on the event of Lemma 3.2 for the actual test selector and the rounded
values `u_i`.  Consider any physical-time prefix of the edited schedule and
normalize counts and work by `n`.  Let

```text
t   = number of tests completed / n,
b   = number of blind jobs completed / n,
z   = number of tested-zero jobs completed / n,
c_j = number of positive tested jobs from grid bin j
      whose known processing has completed / n,
x   = actual physical work used / n,
y   = total completed jobs / n.                       (4.4)
```

Every test is in the controlled first-touch prefix, so (3.8), including its
zero class, and the elementary fact that a known job must be tested before it
is processed give

```text
z   <=D^g_0 t+gamma,
c_j <=D^g_j t+gamma,
gamma=Gamma/n.                                        (4.5)
```

Also, pathwise,

```text
0<=t<=q,
0<=b<=1-q,
y=z+b+sum_j c_j.                                      (4.6)
```

Split the blind jobs completed by the physical prefix into those first
touched before `N_delta` and those in the suffix.  The former are exactly a
prefix sum with selector `1-A_k`, so they satisfy (3.9).  The latter have
total mass at most `delta+1/n`; since both their average rounded work and
`mu_g` lie in `[0,L]`, their rounded work can differ from `mu_g` times their
mass by at most `L(delta+1/n)`.  Adding the two parts gives

```text
mu_g b <= rounded blind work/n
              +L gamma+L(delta+1/n).                 (4.7)
```

Put

```text
c'_j=max(c_j-gamma,0).                                (4.8)
```

Then `0<=c'_j<=D^g_j t`.  Replacing actual processing times by rounded ones
in all already completed processing operations adds at most `h`, because
the total processed job mass is at most one.  Combining this with (4.7),

```text
t+mu_g b+sum_j u_j c'_j <= x+zeta,                    (4.9)

zeta=h+L gamma+L(delta+1/n).                          (4.10)
```

Finally, (4.5), (4.8), and (4.6) give

```text
y <=D^g_0 t+b+sum_j c'_j+(K+1)gamma.                 (4.11)
```

The variables on the right of (4.11) are feasible in the LP defining
`H_{D^g,q}` at work `x+zeta`.  Hence every physical prefix simultaneously
satisfies

```text
y(x) <= H_{D^g,q}(x+zeta)+(K+1)gamma.                (4.12)
```

Notice that `q` is the realized final tested fraction.  We did not condition
on it.  The good event was fixed first, simultaneously for all touch
prefixes; only then was the realized `q` inserted pathwise into (4.6)--(4.12).

### 4.3 Integrating the prefix bound

Let `T` be the normalized terminal work of the edited actual schedule.  Its
completion-time objective obeys the exact area identity

```text
C_edited/n^2 = integral_0^T [1-y(x)] dx.              (4.13)
```

Every edited job is either tested once or run blindly, and every processing
requirement is executed exactly once.  Hence `T=q+mu_actual`.  The terminal
work of the rounded fluid instance is `q+mu_g`, and (4.2) gives
`mu_g<=mu_actual+h`; because `zeta>=h`, we have
`T+zeta>=q+mu_g`.  Extend `H` to equal one after that terminal work.  Since
`0<=1-H<=1`, translating the remaining-mass curve by `zeta` loses at most
`zeta` area:

```text
integral_0^T [1-H(x+zeta)] dx
  >= integral_0^(q+mu_g) [1-H(x)] dx-zeta.            (4.14)
```

Using (4.12), `T<=1+L`, and the fixed-fraction theorem of Section 2, on the
good event we obtain

```text
C_edited/n^2
 >= F_{D^g}(q)-zeta-(1+L)(K+1)gamma
 >= Phi(D^g)-zeta-(1+L)(K+1)gamma.                   (4.15)
```

On the bad event use the trivial lower bound zero.  Every fluid benchmark is
at most `1+L`, so averaging (4.15) without conditioning on `q` gives

```text
E[C_edited]/n^2
 >= Phi(D^g)
    -zeta-(1+L)(K+1)gamma-(1+L)beta_n.                (4.16)
```

Restoring the original schedule using (4.3) proves the following finite
statement.

### Theorem 4.2 (announced grid lower bound)

For every deterministic completing policy that is told the multiset, under
a uniform random placement of its occurrences,

```text
E[C_policy]/n^2
 >= Phi(D^g)-Err_lower,                               (4.17)

Err_lower
 <= c_L(delta+1/n)
    +h+L gamma+L(delta+1/n)
    +(1+L)(K+1)gamma+(1+L)beta_n.                    (4.18)
```

The same inequality holds for a randomized policy by conditioning on its
private seed, because every term on the right is independent of that seed.

## 5. Rounding stability and arbitrary announced multisets

We now compare the grid benchmark in (4.17) with the benchmark of the actual
empirical distribution.

### Lemma 5.1 (zero-preserving perturbation)

Let finite distributions `D,D'` be coupled so that

```text
|P-P'|<=h,
P=0 iff P'=0                                           (5.1)
```

almost surely.  Then

```text
|Phi(D)-Phi(D')|<=h.                                  (5.2)
```

#### Proof

By the fixed-fraction theorem, `Phi(D)` is the optimal value of the fluid
optional-testing problem for `D`; the same is true for `D'`.  Take any
possibly randomized fluid policy `T` for `D`.  We transport it to `D'` using
the coupling.

When the transported policy tests a job and observes `p'`, privately draw a
coupled auxiliary mark `p` from the conditional coupling law given `p'`, and
feed `p` to the simulated copy of `T`.  When it runs a job blindly, draw the
mark only after the blind execution finishes, exactly when `T` would learn
that job's value.  Thus the transported policy is nonanticipating and its
auxiliary history has exactly law `D`.

Couple corresponding actions.  They test, process, and complete the same job
mass in the same action order.  Condition (5.1) is essential here: a tested
job completes at its test in one execution exactly when it does in the other.
Test work is unchanged.  Across unit total job mass, total processing work
changes in absolute value by at most `h`.  Since unfinished mass is always in
`[0,1]`, the remaining-mass area changes by at most `h`.  Therefore

```text
V(D')<=V(D)+h.                                        (5.3)
```

Interchanging `D,D'` gives the reverse inequality.  Since `V=Phi` by Section
2, (5.2) follows.  For empirical distributions the conditional coupling is
just a finite random mark; no regular-conditional-probability issue arises.
`QED`

Apply Lemma 5.1 to the occurrencewise coupling `(p_i,u_i)` from (4.2):

```text
|Phi(D_M)-Phi(D^g)|<=h.                               (5.4)
```

Choose, for all sufficiently large `n`,

```text
K=floor(n^(1/6)),
delta=n^(-1/6),
h=L/K.                                                (5.5)
```

Floors are harmless: once `n^(1/6)>=2`,

```text
n^(1/6)/2<=K<=n^(1/6),
h<=2L n^(-1/6).                                       (5.6)
```

For the `e,Gamma` of (3.6),

```text
gamma=Gamma/n=O(n^(-1/3)*sqrt(log(n+2))),
(K+1)gamma=O(n^(-1/6)*sqrt(log(n+2))),                (5.7)
```

and (3.7) gives `beta_n=o(n^{-2})`.  Equations
(4.17)--(4.18) and (5.4)--(5.7) prove:

### Theorem 5.2 (uniform announced lower bound)

For every fixed `L`, every size-`n` multiset `M subseteq[0,L]`, and every
randomized completing policy that is told `M`,

```text
E_uniform placement[C_policy]
 >= n^2 Phi(D_M)-C_L n^(11/6)*sqrt(log(n+2)).          (5.8)
```

The constant is independent of the multiset and the policy.  Enlarging it
covers the finitely many small values of `n`.

## 6. Matching finite canonical policies

We next show that the fluid value is attainable by a sequential finite
policy with only `O_L(n)` expected implementation error when the multiset is
known.

Fix a finite empirical distribution `D`, its maximum-density selection `g*`,
and a tested fraction `q`.  Let `r` be an integer with `|r-qn|<=1`.  The
canonical finite policy privately permutes the labels and:

1. tests the first `r` labels;
2. after a positive result selected by `g*`, processes that job immediately;
3. after all tests, processes residual tested jobs below `mu` in SPT order;
4. executes every untouched job blindly in the private permutation order;
5. processes the remaining tested jobs in SPT order.

At a fractional boundary atom, the selection `g*` is implemented by an
independent private coin.  Ties at `mu` may be placed on either side of the
blind block.

### Lemma 6.1 (uniform finite implementation)

There is a constant `c_L`, independent of the support size, `D,q`, and the
multiset, such that

```text
|E C_canonical - n^2 F_D(q)| <= c_L n.                (6.1)
```

The same assertion holds for every fixed four-block grid template of Section
7, with `F_D(q)` replaced by that template's fluid value `Psi_D(pi)`.

#### Proof

For an operation word `W`, write `d(o)` for the duration of operation `o`
and `J(o)` for the set of jobs not yet complete immediately before it.  The
area identity gives the exact discrete pair-delay representation

```text
C(W)=sum_{o in W} d(o)|J(o)|.                         (6.1a)
```

For the canonical policy, whether the operation of occurrence `i` is counted
in the completion time of occurrence `j` depends only on the two occurrence
types, their test/untouched memberships, their independent boundary coins,
and their relative order in the relevant random block.  SPT comparisons use
only the two processing times.  Thus (6.1a) is a sum of:

* one-occurrence contributions, coming from a job's own test/processing
  operation and finite diagonal corrections;
* ordered two-distinct-occurrence kernels, recording whether the operation
  of one occurrence delays completion of the other.

Every kernel is bounded by `1+L`.  Conditional on the private permutation and
boundary coins, membership in the tested set, membership in the blind set,
and ordering inside a random block determine all kernels.  For two distinct
occurrences,

```text
Pr[both tested]       = r(r-1)/(n(n-1)),
Pr[first tested,
   second untouched]  = r(n-r)/(n(n-1)),
Pr[both untouched]    = (n-r)(n-r-1)/(n(n-1)).        (6.2)
```

The corresponding product-law coefficients are `q^2`, `q(1-q)`, and
`(1-q)^2`.  Because `|r-qn|<=1`, each coefficient in (6.2) differs from its
product-law value by `O(1/n)`, uniformly in `q`.  A uniformly ordered pair in
the same block has either orientation with probability one half.  Replacing
the without-replacement pair law by the empirical product law therefore
changes fewer than `n^2` bounded pair terms by total `O_L(n)`.  All
one-occurrence and diagonal terms contribute another `O_L(n)`.

After this replacement, group the product kernels by phase.  The discovery
phase gives (2.19); medium/medium and high/high pairs give `q^2K_M/2` and
`q^2K_H/2`; medium work delays the blind and high stocks; and the blind block
gives its two terms in (2.17).  The grouped value is exactly `n^2F_D(q)`.
This proves (6.1).  Nothing in the pair-kernel argument used threshold
optimality: replacing `g*` and the split at `mu` by any fixed classwise
immediate/medium/high selectors gives exactly the corresponding five-term
value `Psi_D(pi)` with the same `O_L(n)` error.  `QED`

Choose a minimizer `q*` of `F_D`.  Lemma 6.1 gives an announced policy with

```text
E C_canonical <=n^2 Phi(D)+c_L n.                    (6.3)
```

In the long-test regime it is simply a uniformly random blind order; its
expected cost is `mu*n(n+1)/2=n^2mu/2+O_L(n)`.

Combining (5.8) and (6.3), the announced minimax value is

```text
VAL_ann(M)=n^2 Phi(D_M)
             +/-O_L(n^(11/6)*sqrt(log(n+2))).         (6.4)
```

The lower side of (6.4) is valid against every adaptive policy, including
policies that use blind durations and choose a random stopping fraction.

## 7. Learning the instance-specific policy

The final upper algorithm is not told the multiset.  We first formulate a
compact finite-dimensional family of policy templates over a common grid so that empirical
optimization is robust even when a sample-empty bin later has positive
population mass.

### 7.1 A distribution-independent template family

On a fixed grid, a template `pi` specifies:

* for each positive grid class `j`, fractions `g_j,m_j,h_j in [0,1]` with
  `g_j+m_j+h_j=1`;
* a tested fraction `q in [0,1]`.

After a test, fraction `g_j` is processed immediately, fraction `m_j` is put
in the known block before blind execution, and fraction `h_j` in the known
tail.  The fractions are implemented by private coins.  A tested zero always
completes at its test.  The classwise selectors, including choices on
sample-empty bins, are part of the template and therefore do not change when
the histogram changes.

Let `Psi_D(pi)` be the fluid cost of this four-block policy.  It is given by
the same five-term formula (2.17), with moments computed from the template's
three selectors.  Let `Pi_K` be the compact finite-dimensional family of all
such templates.

### Lemma 7.1 (template minimum equals the envelope value)

For every grid distribution `D`,

```text
min_{pi in Pi_K} Psi_D(pi)=Phi(D).                    (7.1)
```

#### Proof

Every template describes a feasible fluid policy, so the fixed-fraction
envelope theorem gives `Psi_D(pi)>=Phi(D)`.  Conversely, the template formed
from the maximum-density selector `g*`, the residual split at `mu`, and an
optimal `q*` is precisely the greedy policy of Lemma 2.2 and has value
`Phi(D)`.  Compactness and continuity give existence of a minimizer. `QED`

### Lemma 7.2 (uniform histogram stability)

There is a constant `C_L`, independent of the number of grid cells, such that
for every fixed template and any two grid histograms `D,E`,

```text
|Psi_D(pi)-Psi_E(pi)|<=C_L ||D-E||_1.                 (7.2)
```

Consequently their minimum values satisfy the same bound.

#### Proof

For a fixed template, every one-draw statistic in (2.17) is the expectation
of a function bounded by `1` or `L`; its change is at most respectively
`||D-E||_1` or `L||D-E||_1`.  Every two-draw statistic has a kernel bounded
by `L`.  Inserting the intermediate product measure `E x D` shows that its
change is at most `2L||D-E||_1`.  The coefficients `q,1-q` and all selector
values lie in `[0,1]`.  Applying the triangle inequality to the five terms of
(2.17) gives, for example, `C_L=20(L+1)`.  The bound for minima follows by
evaluating the `D`-minimizer under `E` and conversely. `QED`

### 7.2 The blind-pilot policy

Use the grid (5.5) and choose

```text
k=ceil(n^(1/2)),
N=n-k.                                                (7.3)
```

For the finitely many `n` with `k>=n`, use pure blind execution and absorb
the cost in the final constant.  Otherwise the universal policy is:

1. privately permute all labels;
2. execute the first `k` jobs blindly, completing them and observing their
   lengths;
3. round their positive lengths upward and form the pilot histogram `Dhat`;
4. choose a minimizer `pihat` of `Psi_Dhat` over `Pi_K`;
5. apply the finite canonical implementation of `pihat` to the remaining
   `N` jobs in fresh private random order.

The algorithm uses only `n,L`, observed values, and private randomness.

Let `D^g` be the full grid histogram and `D^R` the fixed histogram of the
remaining jobs after the realized pilot.  Sampling without replacement gives

```text
E||Dhat-D^g||_1 <=sqrt((K+1)/k),                      (7.4)

D^g=(k/n)Dhat+(N/n)D^R,                              (7.5)

E||Dhat-D^R||_1
 <=(n/N)sqrt((K+1)/k).                                (7.6)
```

Equation (7.4) follows by summing the square roots of the coordinate
variances and applying Cauchy--Schwarz.  Equation (7.6) follows algebraically
from (7.5).

Let `pi_R` minimize `Psi_{D^R}`.  Twice applying Lemma 7.2 and using the
sample optimality of `pihat` gives the deterministic empirical-optimization
sandwich

```text
Psi_{D^R}(pihat)
 <=Phi(D^R)+2C_L||Dhat-D^R||_1.                       (7.7)
```

Conditional on the entire pilot, the unused tail of the private permutation
is uniform over the remaining fixed multiset and the chosen template is
fixed.  Analyze the main schedule first with every positive processing time
replaced by its grid upper endpoint.  Lemma 6.1, in its template form, gives

```text
E[main cost | pilot]
 <=N^2[Phi(D^R)+2C_L||Dhat-D^R||_1]+c_L N.            (7.8)
```

The actual schedule uses the same random choices and the same operation
order, but every processing operation is weakly shorter than in this rounded
simulation.  Its completion times are therefore no larger, which justifies
the upper inequality in (7.8) for the actual instance.

The pilot has work at most `Lk`.  It delays each main job by at most that
amount, and the pilot jobs themselves complete by time at most `Lk`.
Therefore its total contribution and its delay to the main phase are at most

```text
O_L(nk).                                              (7.9)
```

From (7.5), `||D^R-D^g||_1<=2k/n`.  Lemma 7.2 and (7.1) imply

```text
Phi(D^R)<=Phi(D^g)+2C_L k/n.                          (7.10)
```

Take expectations in (7.8), add (7.9), use (7.6), and enlarge `N^2` to
`n^2` (all benchmark costs are nonnegative).  We get

```text
E C_universal/n^2
 <=Phi(D^g)
   +O_L(sqrt((K+1)/k)+k/n+1/n).                       (7.11)
```

Finally apply the zero-preserving perturbation Lemma 5.1 to the full
occurrencewise rounding:

```text
Phi(D^g)<=Phi(D_M)+h.                                 (7.12)
```

With `K=floor(n^(1/6))` and `k=ceil(n^(1/2))`,

```text
h=O_L(n^(-1/6)),
sqrt((K+1)/k)=O(n^(-1/6)),
k/n=O(n^(-1/2)).                                      (7.13)
```

Thus, uniformly over every fixed labelling,

```text
E C_universal
 <=n^2 Phi(D_M)+O_L(n^(11/6)).                        (7.14)
```

## 8. From the uniform-permutation experiment to an oblivious adversary

We now prove the two assertions in Theorem 1.  This step is short, but it is
where the quantifiers have to be put in the right order.

### 8.1 The universal upper bound

Fix an arbitrary labelled vector `p in [0,L]^n`.  The policy of Section 7
first draws a uniform private permutation of the physical labels.  Therefore
the ordered multiset seen by the policy has exactly the uniform-placement
law, independently of the adversary's fixed labelling.  Equation (7.14)
applies and gives

```text
E C_A*(p)
 <=n^2 Phi(D_p)+C_L n^(11/6).                         (8.1)
```

The expectation is only over the private permutation, the pilot sample, and
the policy's other private coins.  In particular, the input was fixed before
all of them.

### 8.2 The announced lower bound and Yao's averaging step

Fix a multiset `M`.  Let `Sigma_M` be the finite set of placements of its
distinguished occurrences on the physical labels.  Distinguishing equal
occurrences does not change any execution cost; it only makes `Sigma_M` a
uniform finite permutation space.

First fix a deterministic policy `A` that is told `M`.  Apply Theorem 5.2 to
the uniform random variable `sigma in Sigma_M`.  It gives

```text
(1/|Sigma_M|) sum_sigma C_A(sigma(M))
 >=n^2 Phi(D_M)-C_L n^(11/6)sqrt(log(n+2)).            (8.2)
```

Now let `A` be randomized.  For every fixed private seed `omega`, the policy
`A_omega` is deterministic and (8.2) applies with the same constant.  Average
that inequality over `omega` and interchange the finite sum over `sigma`
with the seed expectation:

```text
(1/|Sigma_M|) sum_sigma E_omega C_Aomega(sigma(M))
 >=n^2 Phi(D_M)-C_L n^(11/6)sqrt(log(n+2)).            (8.3)
```

At least one fixed placement `sigma_*` is no smaller than the average on the
left.  This placement depends on the policy and on `M`, but not on its
subsequent random seed.  It is therefore a legitimate oblivious adversarial
input, and

```text
E C_A(sigma_*(M))
 >=n^2 Phi(D_M)-C_L n^(11/6)sqrt(log(n+2)).            (8.4)
```

Giving `M` to the policy can only reduce its cost, so (8.4) also lower-bounds
policies that do not know the multiset.

### 8.3 Completion of the main theorem

Enlarge the constant to cover the finitely many small values of `n`, and put

```text
epsilon_L(n)=C_L n^(-1/6)sqrt(log(n+2)).               (8.5)
```

The upper error in (8.1) is no larger than
`epsilon_L(n)n^2`, while (8.4) gives the lower assertion with the same
sequence.  Since `epsilon_L(n)->0`, Theorem 1 follows.  When `L=0`, all jobs
are zero and test-all is exact.  For every fixed `L>0`, the general
construction and its additive guarantee already cover all-zero and sparse
inputs.

The proof never conditions on the random final number of tests.  The good urn
event holds simultaneously over every first-touch prefix; only after that
pathwise statement is established is the realized `q` inserted into the
deterministic envelope inequality `F_D(q)>=Phi(D)`.

## 9. The one-dimensional optimizer is explicit

For interpretation, assume first that there are no boundary atoms at `tau`
or `mu`; the virtual splitting convention gives the same formula with atoms.
Expanding (2.17) yields

```text
F_D(q)=mu/2+Aq+Bq^2,                                  (9.1)

A=1+ell+m+mu(d-1)
 =1-E[(mu-P)^+],                                      (9.2)

B= -a(1+ell)/2+m(d-1)+K_M/2
    +mu(1/2-d)+K_H/2.                                 (9.3)
```

If `tau<mu`, then

```text
E[(mu-P)^+]>E[(tau-P)^+]=1,
```

so `A<0`.  Hence the minimizing tested fraction is

```text
q*=1                              if B<=0,
q*=min{1,-A/(2B)}                 if B>0.             (9.4)
```

If `tau>=mu`, Lemma 2.4 gives `q*=0`.  Thus the fluid structural theorem
reduces all possible adaptive stopping rules to one explicit scalar
optimization.

As a concrete check, take

```text
Pr[P=0]=1/5,   Pr[P=9]=1/5,   Pr[P=16]=3/5.
```

Then `mu=57/5`, `tau=5`, and

```text
F_D(q)=57/10-(44/25)q+(11/10)q^2.                    (9.5)
```

The minimizer is `q*=4/5` and the value is `4.996`.  Known jobs of length
nine occur before the blind block, while known jobs of length sixteen occur
after it.  Omitting the medium known prefix changes the leading-order value,
so the four-block structure is genuinely richer than a single threshold
followed immediately by YOLO.

## 10. Relation to the exact i.i.d. theorem

In the independent Bayesian model, the same four-block normal form follows
from the structural theorem of Levi, Magnanti, and Shaposhnik, *Scheduling
with Testing*, Management Science 65(2), 2019, 776--793,
https://doi.org/10.1287/mnsc.2017.2973.  With unit weights and unit test time,
their testing ratio is exactly the solution of `E[(tau-P)^+]=1`, and an
untouched job has expected processing ratio `mu`.

That citation is not used in the adversarial proof above.  The announced
multiset contains draws without replacement, and an adaptive policy changes
the composition of the remaining urn.  Sections 3--5 instead use the
trace-bijection, simultaneous predictable-prefix concentration, and the
completion envelope.  Consequently the proof does not interchange nodes of
an adaptive policy tree and does not assume independence between the stopping
fraction and the tested histogram.

## 11. Dependency audit

For clarity, here is the complete logical chain of the proof.

1. Lemma 2.1 identifies the maximum-density test module and proves the
   threshold equation.
2. Lemma 2.2 replaces every fixed-`q` fluid prefix by an exact divisible
   knapsack; Lemma 2.3 integrates its pointwise envelope and defines
   `Phi`.
3. Lemma 3.1 proves, without probabilistic assumptions, that the adaptive
   first-touch reveal map is a bijection of the placement space and compiles
   every deterministic scheduler into a predictable selector.
4. Lemma 3.2 proves one concentration event simultaneously for every touch
   prefix and every grid class.
5. Lemmas 4.1 and the inequalities (4.6)--(4.15) edit only the uncontrolled
   suffix, repair every revelation constraint, and transfer every adaptive
   finite execution to the fixed-`q` completion envelope.  No stopping-time
   conditioning appears.
6. Lemma 5.1 and the growing grid make the lower bound uniform over all
   bounded multisets, including multisets with `n` distinct positive values.
7. Lemma 6.1 implements every canonical fluid template with only `O_L(n)`
   finite error.
8. Lemma 7.2 makes empirical template optimization stable; the blind pilot
   learns the instance-specific benchmark with `o(n^2)` loss.
9. Section 8 converts uniform placements into a fixed oblivious lower-bound
   placement and proves both quantifier directions of Theorem 1.

Every asymptotic error is uniform in the multiset and its labelling; constants
depend only on the fixed bound `L`.  All equal processing-time occurrences
are distinguished analytically, boundary atoms may be split fractionally,
and zero is kept as a separate grid class so that completion-at-test semantics
is preserved.  This completes the English proof.  The remaining task is
formal verification in Lean; no part of that formalization is assumed in the
argument above.
