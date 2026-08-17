# The exact randomized curve for finite common upper limits

Proof draft, 17 August 2026.

## 1. Model and statement

Fix a common upper limit `u>0`.  A job has an unknown processing time
`p in [0,u]`.  An untouched job may either be run raw for exactly `u` time,
or tested for one unit; after a test, its revealed processing operation has
length `p`.  Operations are nonpreemptive and the objective is total
completion time.  The adversary fixes the labelled input before the
algorithm draws its private random seed.

All ratios below are size-asymptotic.  Thus an estimate

```text
E ALG <= R OPT + o_u(n^2)
```

is an upper bound, and a sequence of fixed oblivious inputs satisfying the
reverse inequality up to `o_u(n^2)` is a matching lower bound.

Let `ubar>1` be the unique root larger than one of

```text
ubar^3-6 ubar^2+5 ubar-1=0,
ubar=5.048917339522306...
```

Equivalently, if `t=sqrt(ubar)`, then

```text
t^3-2t^2-t+1=0.
```

Define

```text
                 1,                                      0<u<=1,
Rrand(u) =       u^3/[u^2+(u-1)^3],                       1<=u<=ubar,
                 1+1/[2(sqrt(u)-1)],                      ubar<=u<=25/4,
                 4/3,                                    25/4<=u<infinity.
```

> **Theorem.**  Against an oblivious adversary, the exact randomized
> size-asymptotic competitive ratio in the finite common-upper model is
> `Rrand(u)`.

The curve is continuous at all three joins.  Its global maximum is attained
at

```text
u=(3+sqrt(3))/2
```

and equals

```text
(27+6sqrt(3))/23 = 1.625752384583185...
```

The rest of this document proves the theorem.  Sections 2--5 prove the
distributional upper bound.  Section 6 removes advance knowledge of the
multiset.  Sections 7--8 give fixed-oblivious-input lower bounds.

## 2. Fluid pair objectives

Assume first that `u>1` and put

```text
s=u-1.
```

Let `D` be a finite probability distribution on `[0,u]`, and let

```text
H(t)=Pr_D[P>t]
```

be its survival function, extended by zero for `t>u`.  Ties in the definition
of `H` are immaterial to all integrals below.

The clairvoyant effective length of a job is

```text
q(P)=min(u,1+P)=1+min(s,P).
```

The leading `n^2` coefficient of the offline SPT objective is therefore

```text
O_u(D) = (1+K_s)/2,
K_s    = integral_0^s H(t)^2 dt.                       (2.1)
```

Indeed, for two independent draws `P,P'`,

```text
E min(q(P),q(P'))
  =1+E min(P,P',s)
  =1+integral_0^s H(t)^2 dt.
```

We compare two randomized policies for an announced multiset.

1. **Raw:** run every job raw in an arbitrary order.  Its leading cost is
   `u/2`.
2. **Stationary:** choose a maximum-density processing-time prefix, test all
   jobs in a uniformly random order, process prefix outcomes immediately,
   and process the remaining tested jobs in SPT order after all tests.

For a prefix of mass `a` and first moment `m`, its completion density is

```text
a/(1+m).
```

Let `theta` be the reciprocal of the maximum density.  The usual one-point
addition/removal argument shows that there is a maximizing prefix containing
all values below `theta`, no values above `theta`, and an arbitrary fraction
of an atom at equality.  In particular,

```text
E (theta-P)^+ = 1,
integral_0^theta [1-H(t)] dt = 1.                     (2.2)
```

The second identity remains valid when `theta>u`, because `H` is extended by
zero.

### Lemma 2.1 (survival form of the stationary cost)

The leading stationary cost is

```text
P(D) = (1/2) [theta+integral_theta^infinity H(t)^2 dt]. (2.3)
```

#### Proof

Let `h=1-a` be the late mass.  The density identity is `1+m=a theta`.
The exact stationary pair formula is

```text
P(D)=(1+m)(1-a/2)+K_L/2,
```

where `K_L` is the late--late minimum kernel.  Layer-cake integration gives

```text
K_L=theta h^2+integral_theta^infinity H(t)^2 dt.
```

Also

```text
(1+m)(1-a/2)
 =theta(1-h)(1+h)/2
 =theta(1-h^2)/2.
```

Adding the two expressions proves (2.3).  The calculation is unchanged if a
boundary atom is split. `QED`

Write

```text
J(D)=theta+integral_theta^infinity H(t)^2 dt = 2P(D).
```

The better announced policy consequently has ratio

```text
min(u,J(D))/(1+K_s).                                  (2.4)
```

We now maximize (2.4) over all `D`.

## 3. The cap side: `theta>=s`

Put

```text
lambda=sqrt(K_s/s).
```

Since `0<=H<=1`, one has `0<=lambda<=1`.

### Lemma 3.1 (cap envelope)

If `theta>=s`, then

```text
J(D) <= 1+lambda+u lambda^2.                           (3.1)
```

#### Proof

First suppose `s<=theta<=u`.  Monotonicity and Cauchy--Schwarz give

```text
H(s)<=lambda,
integral_0^s H(t)dt <= s lambda,
integral_s^theta H(t)dt <=(theta-s)lambda.
```

By (2.2),

```text
theta-1=integral_0^theta H(t)dt <=theta lambda.
```

For `lambda<1`, this says `theta<=1/(1-lambda)`.  Moreover,

```text
integral_theta^u H(t)^2dt <=(u-theta)lambda^2.
```

Consequently

```text
J(D)
 <=theta+(u-theta)lambda^2
 =u lambda^2+theta(1-lambda^2)
 <=u lambda^2+1+lambda.
```

The case `lambda=1` follows directly by continuity, or from
`J(D)<=u+1<=u+2`.

It remains to consider `theta>u`.  Then the maximum-density prefix is the
whole distribution,

```text
J(D)=theta=1+E P.
```

Again by monotonicity and Cauchy--Schwarz,

```text
E P=integral_0^u H(t)dt
 <=s lambda+H(s)
 <=u lambda.
```

Since `theta>u`, one has `E P>s`, hence `lambda>s/u`.  Therefore

```text
J(D)<=1+u lambda
    <=1+lambda+u lambda^2,
```

where the last inequality is
`lambda(1-u+u lambda)>=0`. `QED`

Combining (2.4) and (3.1), every distribution in this case has ratio at most

```text
min { u/(1+s lambda^2),
      (1+lambda+u lambda^2)/(1+s lambda^2) }.          (3.2)
```

This is exactly the ratio obtained from a binary distribution with survival
function `H=lambda` on `(0,u)`, that is, mass `1-lambda` at zero and mass
`lambda` at `u`.

## 4. The obligatory side: `theta<=s`

This case can occur only when `s>=1`.  Define

```text
B = integral_0^theta H(t)[1-H(t)]dt,
c = H(s),
K = K_s.
```

### Lemma 4.1 (two-plateau reduction)

One has

```text
0<=c<=B<1,
B<=1-1/s,                                             (4.1)

K >= k_s(B,c)
   :=(B^2-c^2)/(1-B)+s c^2,                           (4.2)

J(D) <=1+K+B+c^2.                                    (4.3)
```

#### Proof

Equation (2.2) and the definition of `B` give

```text
integral_0^theta [1-H(t)]^2dt=1-B.
```

Cauchy--Schwarz therefore yields

```text
theta>=1/(1-B).                                      (4.4)
```

Since `theta<=s`, this also gives the last inequality in (4.1).  Moreover,
`H(t)>=c` on `[0,theta]`, and hence

```text
B>=c integral_0^theta[1-H(t)]dt=c.
```

For the early square integral, use (2.2) once more:

```text
integral_0^theta H(t)^2dt
 =integral_0^theta H(t)dt-B
 =theta-1-B.                                         (4.5)
```

On `[theta,s]`, monotonicity gives `H(t)>=c`.  Thus

```text
K >=theta-1-B+(s-theta)c^2
   =theta(1-c^2)-1-B+s c^2.
```

Substitute (4.4).  A direct simplification gives

```text
(1-c^2)/(1-B)-1-B+s c^2
 =(B^2-c^2)/(1-B)+s c^2,
```

which proves (4.2).

Finally, the interval `[s,u]` has length one and `H(t)<=c` there.  Using
(4.5),

```text
J(D)
 =theta+[K-integral_0^theta H(t)^2dt]
   +integral_s^u H(t)^2dt
 <=1+K+B+c^2.
```

This is (4.3). `QED`

The inequalities are sharp simultaneously.  Equality is attained by the
two-plateau survival function

```text
H(t)=B,   0<t<1/(1-B),
H(t)=c,   1/(1-B)<t<u.
```

It corresponds to a three-point distribution on
`{0,1/(1-B),u}`.  The next lemma shows that even these three-point
distributions cannot create a new branch.

### Lemma 4.2 (only the two boundary plateaus matter)

In the case `theta<=s`,

```text
J(D)/(1+K)
 <=max { 4/3,
          sup_0<=b<=1
          min(u,1+b+u b^2)/(1+s b^2) }.               (4.6)
```

#### Proof

Since `theta<=u` and `0<=H<=1`, formula (2.3) gives `J(D)<=u`.  Hence raw
execution cannot improve the left side in this case.

By Lemma 4.1 and monotonicity in `K`,

```text
J(D)/(1+K)
 <=1+(B+c^2)/(1+k_s(B,c)).                            (4.7)
```

Fix `B` and put `y=c^2`.  Then

```text
k_s(B,c)=k_0+A y,
k_0=B^2/(1-B),
A=s-1/(1-B)>=0.
```

The nonconstant part of (4.7) is

```text
f_B(y)=(B+y)/(1+k_0+A y),       0<=y<=B^2.
```

Its derivative has the constant sign of

```text
1+k_0-A B.
```

Therefore its maximum is at `y=0` or `y=B^2`.

At `y=0`,

```text
1+f_B(0)=1+B/[1+B^2/(1-B)] <=4/3,                    (4.8)
```

because, after multiplication by `1-B`, the required inequality is

```text
(2B-1)^2>=0.
```

At `y=B^2`,

```text
1+f_B(B^2)
 =(1+B+u B^2)/(1+s B^2).                             (4.9)
```

The constraint `B<=1-1/s` implies
`1+B+uB^2<=u`; alternatively this is immediate from the corresponding
constant-survival schedule.  Thus (4.9) is the second term in (4.6), with
the harmless raw minimum inserted. `QED`

Equality in (4.8) is `B=1/2,c=0`: half the mass is zero and half is at two.
Equality on the other boundary is a distribution supported on `{0,u}`.

## 5. Solving the remaining scalar game

Define

```text
M(u)=sup_0<=x<=1
     min { u/(1+s x^2),
           (1+x+u x^2)/(1+s x^2) }.                  (5.1)
```

The two numerators cross when

```text
x+u x^2=s,
```

whose unique nonnegative solution is

```text
x_0=s/u.                                              (5.2)
```

Thus the tested expression is the minimum on `[0,x_0]`, and the raw
expression is the minimum on `[x_0,1]`.  The raw expression is decreasing,
so its maximum on the latter interval is at `x_0`.

The derivative of the tested expression has the sign of

```text
1+2x-s x^2.
```

Its positive stationary point is

```text
x_*=(1+sqrt(u))/s=1/(sqrt(u)-1).                      (5.3)
```

The points `x_*` and `x_0` coincide precisely at `u=ubar`.  Indeed, after
putting `t=sqrt(u)`, their equality is

```text
t^3-2t^2-t+1=0,
```

or equivalently `u^3-6u^2+5u-1=0` on the relevant root.  The cubic is
negative from `u=1` through its last critical point and then strictly
increasing, so it has exactly one root larger than one.

For `u<=ubar`, the tested expression is still increasing at `x_0`; hence

```text
M(u)=u/(1+s(s/u)^2)
    =u^3/[u^2+s^3].                                   (5.4)
```

For `u>=ubar`, the maximum is at `x_*`.  Using
`s x_*^2=1+2x_*`, one obtains

```text
M(u)=1+x_*/2
    =1+1/[2(sqrt(u)-1)].                              (5.5)
```

The second value equals `4/3` exactly at `u=25/4`, is larger before that
point, and smaller afterwards.  For completeness, `M(u)>4/3` also on
`[2,ubar]`: the derivative of (5.4) has the sign of
`u^2-3(u-1)^2`, so this branch first increases and then decreases; its two
endpoint values are `M(2)=8/5` and
`M(ubar)=1+1/[2(sqrt(ubar)-1)]>4/3`, since `ubar<25/4`.  In the range where
the obligatory case `theta<=s` exists but `u<3`, its boundary (4.8) is in
addition restricted to `B<=1-1/s<1/2`.
Consequently Lemmas 3.1 and 4.2 prove

```text
min(u,J(D))/(1+K_s) <=Rrand(u)                        (5.6)
```

for every finite distribution `D` on `[0,u]`.  When `0<u<=1`, raw execution
is itself clairvoyantly optimal, so (5.6) holds with value one.

This completes the announced-distribution fluid upper bound.

For reference, differentiating the first branch shows that its unique
maximum is at `u=(3+sqrt(3))/2`.  Substitution gives
`(27+6sqrt(3))/23`.

## 6. Removing knowledge of the multiset

The upper theorem must use one algorithm depending only on `n,u`, not on
`D`.  Since `u` is fixed and the support is bounded, a standard pilot and
finite-grid argument loses only `o_u(n^2)`.  We include the details needed to
fix the quantifiers.

Choose

```text
k=floor(n^(2/3)),
d=floor(n^(1/3)),
eta=u/d.
```

Keep zero as a separate category and round every positive value upward to
one of the `d` grid endpoints.  The algorithm draws a uniform random
permutation, tests its first `k` jobs, and forms the sample histogram.  On
that histogram it evaluates the following finite family of templates:

1. raw execution of all jobs;
2. for each grid prefix, the stationary all-test policy that processes that
   prefix immediately and defers its complement.

It selects a minimum-cost empirical template.  If it selected raw, it runs
the untouched jobs raw and finishes the at most `k` already tested positive
jobs in any fixed position.  If it selected a stationary prefix, it executes
the sample-first version of that policy: sampled early positives are
processed, the remaining jobs are tested in their unused random order with
early outcomes immediate, and the deferred tail is finished in SPT order.

### Lemma 6.1 (finite learned upper bound)

For every fixed `u` there is a deterministic sequence `eps_u(n)->0` such
that every fixed labelled input with empirical distribution `D` satisfies

```text
E ALG <=n^2 min{u/2,P(D)}+eps_u(n)n^2.                (6.1)
```

One may take `eps_u(n)=O_u(n^(-1/6))` with the parameters above.

#### Proof

Let `Dhat` be the sample grid histogram and `Dg` the population grid
histogram.  Hypergeometric variance, followed by Cauchy--Schwarz over the
`d+1` categories, gives

```text
E ||Dhat-Dg||_1 <=sqrt((d+1)/k)=O(n^(-1/6)).          (6.2)
```

For every fixed grid prefix, its stationary coefficient is a quadratic
polynomial in the category masses, with all coefficients bounded by a
constant depending only on `u`.  Hence all templates simultaneously satisfy

```text
|C_Dhat(template)-C_Dg(template)|
 <=C_u ||Dhat-Dg||_1.                                (6.3)
```

The usual empirical-minimization sandwich applies: the true cost of the
empirically chosen template is at most the true cost of the best grid
template plus twice the right side of (6.3).  Moving a processing time by at
most `eta` changes every normalized pair coefficient by `O(eta)`, so the
best grid prefix is within `O_u(1/d)` of the best actual prefix.

Finally, putting the sample first rather than interleaving it into one
uniform stationary order changes at most `O(nk+k^2)` bounded operation--job
pairs.  The same bound covers the already tested pilot jobs in raw mode.
After division by `n^2`, these three errors are

```text
O_u(sqrt(d/k)+1/d+k/n)=O_u(n^(-1/6)).
```

This proves (6.1). `QED`

Combining Lemma 6.1 with (5.6) and the exact finite offline pair formula
gives

```text
E ALG <=Rrand(u) OPT+o_u(n^2).                        (6.4)
```

For `u>1`, every effective length is at least one, so
`OPT>=n(n+1)/2`; the additive error is therefore multiplicatively
negligible.  For `u<=1`, the exact raw policy was already handled.  This
proves the randomized upper bound against every fixed oblivious labelling.

## 7. Binary random-labelling lower envelope

Fix masses `z` and `x=1-z`, and consider a multiset with `zn+O(1)` zero jobs
and `xn+O(1)` jobs of value `u`, placed uniformly on the labels.  We first
fix an arbitrary deterministic nonanticipating algorithm, possibly told the
multiset.

Expose processing times analytically in the algorithm's order of first
touches, including the values of raw-touched occurrences which remain hidden
from the algorithm.  The first-touch trace map is a bijection of the finite
placement space: two placements with the same occurrence word give the same
observable run, hence the same next label and touch kind, and induction
recovers the placement.  Thus the occurrence word is a uniform permutation.
Before each fresh touch, the algorithm's test/raw indicator is predictable
from the earlier word.

We need a small suffix cutoff because a predictable sample drawn almost to
exhaustion need not have an `O(sqrt(n))` discrepancy from the original
population proportion.  Fix `delta_n->0` slowly, for example
`delta_n=n^(-1/4)`.  Simultaneous predictable-urn concentration gives an
event of probability `1-o(1)` on which, for every first-touch prefix ending
while at least `delta_n n` labels remain and containing `t` selected tests,

```text
|number of tested zeros-z t|<=Delta_n,
Delta_n=O(delta_n^(-1)sqrt(n log n))=o(n).            (7.1)
```

For completeness, expose the whole uniform first-touch word.  Uniform-prefix
hypergeometric concentration controls the conditional zero proportion of
the remaining urn up to the cutoff.  Subtracting this conditional proportion
from each predictably selected indicator gives a bounded-increment
martingale; maximal Azuma--Hoeffding then proves (7.1), simultaneously over
all prefixes.

Edit the realized schedule after the cutoff: every still-untouched job which
would later be tested is run raw at its first later operation, and its later
known-processing operation is deleted.  At most `delta_n n+O(1)` jobs are
affected, so this changes total completion cost by at most
`O_u(delta_n n^2+n)`.  The edited schedule has a final tested fraction `q`
whose every test occurred in the controlled prefix.  We insert this realized
`q` only after the simultaneous event has been established; no conditioning
on a stopping time is used.

Ignoring the `O(Delta_n)` perturbation, every prefix of the edited completion
curve is dominated by
the following divisible items:

| item | completion capacity | work per completion |
|---|---:|---:|
| zero-test module | `zq` | `1/z` |
| tested long processing | `xq` | `u` |
| raw jobs | `1-q` | `u` |

Indeed, `t` tests complete at most `zt+Delta_n` zeros and expose at most
`xt+Delta_n` processable long jobs; raw and known-long processing each consume
`u` work per completion.  The divisible-knapsack exchange argument therefore
upper-bounds completed mass at every amount of work.  Integrating the
remaining-mass envelope lower-bounds total completion time.  The vertical
repair `O(Delta_n/n)`, the suffix edit, and the bad-event contribution are
all `o_u(1)` after normalization by `n^2`.

If `z<=1/u`, every item has work per completion at least `u`, and hence

```text
E ALG/n^2 >=u/2-o(1).                                (7.3)
```

If `z>=1/u`, the zero-test module comes first.  For fixed `q`, the normalized
area of the greedy envelope is

```text
F_z(q)=q-zq^2/2 + (u/2)(1-zq)^2.                     (7.4)
```

Its derivative is

```text
F_z'(q)=(1-zq)(1-uz).
```

Thus it is minimized at `q=1`, and

```text
E ALG/n^2
 >=F_z(1)-o(1)
 =(1+x+u x^2)/2-o(1).                                (7.5)
```

At `z=1/u`, every `q` has the same leading cost `u/2`.

Every placement in this distribution has the same offline leading
coefficient

```text
O_u(x)=(1+s x^2)/2.                                  (7.6)
```

Equations (7.3)--(7.6) prove, even against an algorithm told the multiset,

```text
E ALG/n^2 >=Phi_u(x)-o_u(1),

Phi_u(x)= u/2,                    x>=s/u,
          (1+x+u x^2)/2,          x<=s/u.             (7.7)
```

The estimates were proved for every fixed deterministic policy.  For a
randomized policy, condition on its private seed, average (7.7) over seeds,
and interchange the seed average with the finite uniform average over
placements.  At least one fixed placement has expected cost at least the
joint average.  This placement is selected before the subsequent private
seed and is therefore a legitimate oblivious input.  This is the finite Yao
step.

## 8. Matching the four branches

For `1<u<=ubar`, choose

```text
x=s/u.
```

This is the equality case `z=1/u` of (7.7).  Together with (7.6), it gives

```text
Phi_u(x)/O_u(x)
 =u^3/[u^2+s^3].                                     (8.1)
```

For `ubar<=u<=25/4`, choose

```text
x=1/(sqrt(u)-1).
```

The definition of `ubar` says precisely that `x<=s/u`, so (7.5) applies.
The stationary identity `s x^2=1+2x` gives

```text
Phi_u(x)/O_u(x)=1+x/2
 =1+1/[2(sqrt(u)-1)].                                (8.2)
```

Irrational masses in (8.1)--(8.2) are handled by rational approximation and
integer rounding; all diagonal and rounding errors are `O_u(n)`.

For `u>=25/4`, use instead a uniformly labelled multiset with half the jobs
at zero and half at processing time two.  Apply the same trace,
predictable-urn, and suffix-edit argument as in Section 7.  Its fluid
completion items are

| item | completion capacity | work per completion |
|---|---:|---:|
| zero-test module | `q/2` | `2` |
| tested two processing | `q/2` | `2` |
| raw jobs | `1-q` | `u` |

Every item costs at least two per completion.  Therefore the completion
envelope lies below the triangle `min{1,t/2}`, independently of the realized
tested fraction `q`.  The `o(n)` predictable-urn repair and suffix edit give

```text
E ALG>=n^2-o(n^2).                                    (8.3)
```

Since `u>=3`, the effective lengths are one and three, and

```text
OPT=(3/4)n^2+O(n).                                    (8.4)
```

The same finite Yao averaging selects one fixed oblivious labelling, proving
the lower ratio `4/3`.

For `u<=1`, every effective length is `u` and raw execution is exactly
optimal, so the lower value is one.

The lower bounds (8.1)--(8.4) match the upper bound (6.4) in every regime.
This completes the proof of the theorem.

## 9. Proof-dependency audit

The genuinely new analytic step is the survival-function split:

```text
theta>=u-1  -> Lemma 3.1 -> binary cap envelope,
theta<=u-1  -> Lemma 4.1 -> two plateau variables
             -> linear-fractional endpoint reduction
             -> cap binary or half-zero/half-two.
```

The finite probabilistic ingredients are already present in stronger forms
elsewhere in the project:

* exact stationary random-order pair accounting;
* hypergeometric histogram concentration;
* adaptive first-touch trace bijection and predictable-urn concentration;
* finite empirical-minimization and grid-transfer arguments;
* finite Yao selection of one fixed oblivious labelling.

In particular, `RANDOMIZED_COMMON_UPPER_INSTANCE_OPTIMAL_PROOF.md` proves the
stronger statement that the full quadratic benchmark obtained by optimizing
the tested fraction `q`, rather than only the two endpoint policies used for
the curve upper bound, is attainable without an announced multiset and is a
lower bound against every announced adaptive policy.

For a paper version, Lemma 6.1 and the predictable-urn paragraph in Section 7
can either cite those earlier lemmas or be restated with explicit constants.
No adaptive-adversary replay is used anywhere in the randomized lower bound.
