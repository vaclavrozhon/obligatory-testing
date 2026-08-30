# Randomized obligatory testing: the sharp asymptotic ratio is `4/3`

Self-contained proof, revised 6 August 2026.

## The theorem

There are `n` labelled jobs on one nonpreemptive machine. Job `i` has an
unknown processing time `p_i>=0`. A unit-time test must be completed before
the job can be processed and reveals `p_i`. If `p_i>0`, processing then takes
`p_i` time; if `p_i=0`, the job completes at the end of its test. Every job
must be tested. The objective is the sum of completion times.

The adversary is oblivious: it fixes the labelled vector `p` before the
algorithm draws its random bits. The algorithm is not told the multiset of
processing times.

> **Theorem 1 (sharp randomized ratio).** There are randomized
> nonanticipating algorithms `A_n`, depending only on `n`, such that for
> every `n` and every input `p in [0,infinity)^n`,
>
> ```text
> E ALG_A_n(p) <= 4 OPT(p)/3 + 20378 n^(7/4)
>              <= (4/3+40756 n^(-1/4)) OPT(p).      (T1)
> ```
>
> Conversely, for every randomized algorithm and every sufficiently large
> even `n`, some fixed labelling of `n/2` zero jobs and `n/2` jobs of
> processing time two satisfies
>
> ```text
> E ALG(p) >= n^2-O(n^(3/2)),                       (T2)
> ```
>
> while `OPT(p)=3n^2/4+n`. Consequently the exact asymptotic randomized
> competitive ratio against an oblivious adversary is `4/3`.

The expectation is only over the algorithm's private randomness. No adaptive
adversary and no announced multiset are used in the upper bound.

The proof has four ingredients.

1. A stationary random-order policy for a known processing-time prefix has
   an exact expected-cost formula.
2. A maximum-density prefix satisfies an algebraic `4/3` certificate.
3. A sublinear random sample learns an approximately threshold-separated
   prefix. A fixed safety cutoff makes this uniform over unbounded inputs.
4. A random labelling of half zeros and half twos gives the matching Yao
   lower bound.

## 1. The exact offline objective

There are `n` labelled jobs.  Job `i` has a processing time `p_i >= 0` fixed
by the oblivious adversary.  Testing a job takes one unit of machine time and
reveals `p_i`.  Every job must be tested.  If `p_i > 0`, processing it after
its test takes `p_i` additional units.  A zero job completes at the end of its
test.  Operations are nonpreemptive and the objective is the sum of
completion times.

Put

```text
K(p) = (1/n^2) sum_{i,j} min(p_i,p_j)
O(p) = (1 + K(p))/2
D(p) = (n + sum_i p_i)/2.
```

Order the jobs by their actual order of completion in an arbitrary feasible
schedule, say `j_1,...,j_n`. By the time `j_r` completes, all required work
of every `j_l`, `l<=r`, has been performed. Therefore

```text
C_(j_r) >= sum_(l<=r) (1+p_(j_l)).                 (1.0)
```

Summing (1.0), this lower bound is minimized by placing smaller `p_i` first.
The schedule that tests and immediately processes each job in this SPT order
attains equality for every `r`. Thus

```text
OPT(p)
  = n(n+1)/2 + sum_i p_i
      + sum_(i<j) min(p_i,p_j)
  = n^2 O(p) + D(p).                              (1.1)
```

Indeed,

```text
n^2 O(p)
  = n^2/2 + (1/2) sum_i p_i
      + sum_{i<j} min(p_i,p_j),
```

whereas the exact shortest-first cost is

```text
n(n+1)/2 + sum_i p_i
  + sum_{i<j} min(p_i,p_j).
```

Their difference is precisely `D(p)`.

In particular,

```text
OPT(p) >= n(n+1)/2.                               (1.2)
```

## 2. A stationary policy for an arbitrary prefix split

Fix a set `E` of early jobs which is a processing-time prefix: every job in
`E` is no longer than every job outside `E`.  We additionally require

```text
{i : p_i=0} is a subset of E.                    (2.0)
```

This condition is essential operationally: a zero job completes at its test
and therefore cannot be deferred to the final tail.  All maximum-density
prefixes used below satisfy (2.0).  Let `L` be the complement of `E` and
write

```text
e = |E|,                 a = e/n,
h = 1-a,
m = (1/n) sum_{i in E} p_i,
K_E = (1/n^2) sum_{i,j in E} min(p_i,p_j),
K_L = (1/n^2) sum_{i,j in L} min(p_i,p_j),
w = 1+m.
```

Because `E` is a prefix, every early/late pair has minimum equal to its early
processing time.  Therefore

```text
K(p) = K_E + 2hm + K_L.                          (2.1)
```

Define the normalized fluid cost of this split by

```text
P(p,E) = (1+m)(1-a/2) + K_L/2.                  (2.2)
```

The stationary policy for `E` tests jobs in a uniform random order, processes
an early positive job immediately after discovering it, defers every late
job, and finally processes the late jobs in shortest-processing-time order.

### Lemma 2.1: exact stationary cost

The expected cost of this policy is

```text
E ALG_stat(p,E)
  = n^2 P(p,E) + (e + sum_i p_i)/2.              (2.3)
```

#### Proof

Let

```text
W   = n + sum_{i in E} p_i,
L_E = e + sum_{i in E} p_i.
```

The discovery phase consists of `n` blocks.  A late block is only its unit
test; an early block is its test followed by its processing and completes its
job.  Assumption (2.0) ensures that every late job is positive and really is
still unfinished after its test.  For an early job, every other discovery
block precedes its completion with probability one half.  Hence the expected
sum of early completion times is

```text
eW/2 + L_E/2.
```

Every late job receives the common discovery offset `W`.  The SPT tail costs

```text
(n-e)W + sum_{i in L} p_i
  + sum_{i<j, i,j in L} min(p_i,p_j).
```

Adding the two expressions and expanding `n^2 P(p,E)` proves (2.3).  More
explicitly,

```text
n^2 P(p,E)
  = (n-e/2) W
    + (1/2) sum_{i in L} p_i
    + sum_{i<j, i,j in L} min(p_i,p_j),
```

and the remaining diagonal term is

```text
(e + sum_i p_i)/2.
```

This proves the identity.  Without (2.0) the formula is false: for
`p=(0,0)` and `E=empty`, the real cost is `3`, whereas (2.3) would give `4`.
Notice that no concentration theorem is used in this upper bound.  Only pair
symmetry of a uniform permutation is needed.

## 3. The exact `4/3` certificate

For a nonempty processing-time prefix `E`, define its completion density by

```text
rho(E)=a/(1+m).
```

Choose a prefix of maximum density and put

```text
theta = (1+m)/a.                                  (3.1)
```

Thus `m=a theta-1` and `theta=1/rho(E)`. All zero jobs belong to every
maximum-density prefix: adding an omitted zero increases the numerator and
does not increase the denominator.

There is a maximizing prefix for which every early value is at most `theta`
and every late value is at least `theta`. Indeed, removing one selected
boundary job of value `x`, with normalized mass `delta=1/n`, changes the
density to

```text
(a-delta)/(1+m-x delta).
```

Cross multiplication shows that this is larger precisely when `x>theta`,
contradicting maximality. Similarly, adding the next unselected boundary job
increases density precisely when its value is less than `theta`. A value
equal to `theta` leaves the density unchanged and may be put on either side.

For early `x,y <= theta`,

```text
xy <= theta min(x,y).
```

After averaging,

```text
m^2 <= theta K_E.                                 (3.2)
```

For late `x,y >= theta`,

```text
theta <= min(x,y),
```

and therefore

```text
theta h^2 <= K_L.                                 (3.3)
```

Using (2.1), define again

```text
O = (1 + K_E + 2hm + K_L)/2,
P = theta a(1-a/2) + K_L/2.
```

Direct expansion gives the exact identity

```text
2 theta (4O-3P)
  = (theta-2)^2
      + 4(theta K_E-m^2)
      + theta(K_L-theta h^2).                    (3.4)
```

Every term on the right is nonnegative by (3.2) and (3.3).  Thus

```text
P <= 4O/3.                                        (3.5)
```

Combining (1.1), (2.3), and (3.5) even gives the exact finite upper bound

```text
E ALG_stat(p,E) <= 4 OPT(p)/3,                    (3.6)
```

because

```text
(e + sum_i p_i)/2 <= D(p) <= 4D(p)/3.
```

The issue in the unknown-multiset model is therefore not the stationary
policy itself.  It is learning a sufficiently good prefix `E` without seeing
the multiset.

## 4. A robust approximate-threshold lemma

The sampled optimizer need not be close to the true optimizer.  For example,
the density curve can have a long almost-flat region.  We therefore prove a
value guarantee for the selected split rather than stability of the argmax.

The following form is designed for the unbounded proof.

### Lemma 4.1: approximate split certificate

Let `E,L` be an ordered prefix split of a probability distribution on
nonnegative processing times.  Use `a,h,m,K_E,K_L,P,O` as above and suppose
`a>0`.  Define `theta=(1+m)/a`.  Suppose that for some `s>=0`:

```text
every early value is at most theta+s,
every late value is at least theta-s.
```

Then

```text
P <= 4O/3 + (2/3) s.                              (4.1)
```

#### Proof

The upper bound on early values gives

```text
m^2 <= (theta+s)K_E.
```

Equivalently, `theta K_E-m^2>=-sK_E`. There is also a
scale-free bound on `K_E`. Since `min(x,y)<=x`,

```text
K_E <= a m <= a^2 theta.
```

Consequently

```text
theta K_E-m^2 >= -sK_E.                          (4.2)
```

The lower bound on late values gives

```text
K_L-theta h^2 >= -s h^2.                         (4.3)
```

Insert (4.2) and (4.3) into the identity (3.4). Since the square term is
nonnegative,

```text
4O-3P >= -2sK_E/theta-(s/2)h^2.
```

Using `K_E<=a^2 theta`, this yields

```text
P <= 4O/3+(2/3)s a^2+(1/6)s h^2
  <= 4O/3+(2/3)s,                                (4.4)
```

because `(2/3)a^2+(1/6)(1-a)^2<=2/3` on `[0,1]`. This proves
(4.1).

### Lemma 4.2: a bad learned split is still bounded

If `R>=1`, `E` is an ordered prefix containing every zero job, and every
early value is at most `R`,
then

```text
P(p,E) <= O(p) + R/2.                             (4.5)
```

#### Proof

Direct expansion gives the exact identity

```text
P-O = (h+a m-K_E)/2.                              (4.6)
```

Now `K_E>=0`, `m<=aR`, and

```text
h+a m <= 1-a+R a^2 <= R.
```

The last inequality follows because `1-a+a^2<=1`. Equation (4.6) proves
(4.5). This bound is important on the rare event that
the sample histogram is inaccurate.  It is independent of arbitrarily large
late processing times.

## 5. Sampling a quantized histogram

Fix a safety cutoff `B>0` and a positive integer `d`.  Put

```text
eta = B/d.
```

Use one category for zero, partition `(0,B]` into `d` consecutive bins, and
add one overflow category for values larger than `B`.  Thus there are
`D=d+2` categories.  A positive value in a finite bin is rounded upward to
the right endpoint of its bin; zero remains zero.  Thus

```text
p <= q(p) <= p+eta                               (5.1)
```

for non-overflow values.  A prefix of rounded categories induces an ordered
prefix of the actual values: every selected actual value is no larger than
every unselected actual value.

Choose a uniformly random subset `S` of exactly `k` labels.  Equivalently,
take the first `k` labels of a uniform random permutation.  Let `mu_b` be the
population fraction in category `b` and `muHat_b` its sample fraction.  Set

```text
Delta = sum_b |muHat_b-mu_b|.
```

### Lemma 5.1: expected histogram error

For `n>1` and `1<=k<n`, with `D=d+2` categories,

```text
E Delta <= sqrt(D/k).                             (5.2)
```

#### Proof

For a fixed category with population fraction `mu_b`, its sample count `X_b`
is hypergeometric.  Writing it as a sum of `k` exchangeable indicators gives

```text
E[X_b/k]=mu_b,
Var(X_b/k)
  = ((n-k)/(n-1)) mu_b(1-mu_b)/k
  <= mu_b/k.
```

By Cauchy--Schwarz,

```text
E |X_b/k-mu_b| <= sqrt(mu_b/k).
```

Summing over categories and applying Cauchy--Schwarz once more,

```text
E Delta
  <= (1/sqrt(k)) sum_b sqrt(mu_b)
  <= sqrt(D/k),
```

because `sum_b mu_b=1`.

### Corollary 5.2: a good sample event

For any `tau>0`, define

```text
G = {Delta <= tau}.
```

Markov's inequality and (5.2) give

```text
Pr(not G) <= sqrt(D/k)/tau.                       (5.3)
```

This elementary estimate is sufficient for the upper bound.  No uniform CDF
concentration theorem is needed.

## 6. Learning a maximum-density prefix

For every nonempty prefix `J` of finite sample categories not containing the
overflow category, define

```text
aHat(J) = sum_{b in J} muHat_b,
mHat(J) = sum_{b in J} q_b muHat_b,
rhoHat(J) = aHat(J)/(1+mHat(J)).                  (6.1)
```

Choose a prefix `J_0` maximizing `rhoHat`; ties are broken canonically, and
write

```text
thetaHat=1/rhoHat(J_0).                           (6.2)
```

If every finite category is absent from the sample, define the maximum
density to be zero and use the fallback below.

The algorithm does **not** use `J_0` itself as its early category set.  It
uses its threshold closure

```text
J = {finite categories b : q_b <= thetaHat}.      (6.3)
```

Define `aHat,mHat` from this closed set `J`.

### Lemma 6.1: threshold closure of the sample maximizer

The closure `J` has the same maximum density as `J_0`, and hence

```text
thetaHat=(1+mHat)/aHat.                           (6.4)
```

For every category, including categories of zero sample mass, every selected
finite representative satisfies `q_b<=thetaHat` and every unselected finite
representative satisfies `q_b>thetaHat`. In particular, the zero category is
selected.

#### Proof

For a category of positive sample mass, the usual ratio comparison applies.
If a selected top category has representative `q>thetaHat`, removing it
increases density; if an unselected next category has `q<thetaHat`, adding it
increases density.  Iterating over empty intervening bins shows that every
positive-mass category below the threshold is in `J_0` and every
positive-mass category above it is outside `J_0`.

Adding or removing sample-empty categories changes neither `aHat` nor
`mHat`.  Adding a category with `q=thetaHat` changes numerator and denominator
in exactly the current ratio and therefore preserves density.  Closing
`J_0` as in (6.3) thus preserves its density and gives (6.4). Since positive
sample density implies `thetaHat>0`, the closure contains zero. The final
threshold statement follows from the definition of `J`, without any premise
about sample mass. This last point is why the closure is necessary: the
uncanonicalized maximizer alone says nothing about an empty sample bin that
has positive population mass.

## 7. The unbounded sample-based algorithm

For sufficiently large `n`, choose

```text
B     = 32,
k     = floor(n^(3/4)),
d     = floor(n^(1/4)),
eta   = B/d,
gamma = 1/(B(1+B)).                               (7.1)
```

Small values of `n` may use test-all-then-SPT.

Choose one uniform random permutation of the labels.  Its first `k` labels
form the sample and its remaining order will be the later test order.

The algorithm performs the following steps.

1. Test the first `k` sample jobs without processing positive sample jobs.
2. Form the rounded histogram on `[0,B]` plus the overflow category.
3. Find a maximum-density sample prefix among non-overflow categories,
   compute its inverse density `thetaHat`, and replace the chosen prefix by
   the threshold closure (6.3).
4. If its density is less than `2/B`, enter **fallback mode**: test every
   remaining job and then process all positive jobs in SPT order.
5. Otherwise its inverse density satisfies `thetaHat<=B/2`.  Enter
   **learned mode**:
   - process the sampled jobs belonging to the learned prefix in SPT order;
   - test remaining labels in permutation order and immediately process a
     job exactly when its rounded category belongs to the learned prefix;
   - after the final test, process all deferred jobs, including overflow
     sample jobs, in SPT order.

The safety rule is crucial: a job above `B` is never processed during
discovery.  Thus a huge value missed by the sample cannot be accidentally
placed before many jobs.

## 8. Learned mode on a good sample

Assume the fixed histogram event `G={Delta<=gamma}` and that the algorithm enters
learned mode.  Let `E` be the population prefix induced by the learned sample
categories.  Let `a,m,theta` be its true population statistics, where

```text
theta=(1+m)/a.
```

The sample threshold satisfies `thetaHat<=B/2`, and hence

```text
aHat=(1+mHat)/thetaHat >= 2/B.                    (8.1)
```

Because `gamma<=1/B`,

```text
a >= aHat-Delta >= 1/B.                           (8.2)
```

The selected rounded values are at most `B/2`.  Histogram error and upward
rounding give

```text
|a-aHat| <= Delta,
|m-mHat| <= B Delta+eta.                          (8.3)
```

Using `a>=1/B` and `thetaHat<=B/2`,

```text
|theta-thetaHat|
  = |(1+m)/a-(1+mHat)/aHat|
  <= (B Delta+eta)/a + thetaHat |a-aHat|/a
  <= (3/2)B^2 Delta+B eta.                        (8.4)
```

For convenience put

```text
u = (3/2)B^2 Delta+B eta,
s = u+eta.                                        (8.5)
```

The threshold closure, rather than merely the sampled maximizing prefix, now
gives the required statement for **all population categories**.  Upward
rounding implies:

- every early actual value is at most `thetaHat`;
- every late actual value is at least `thetaHat-eta` (overflow values satisfy
  this as well because `thetaHat<=B/2`);
- the split is ordered, so every early/late minimum is the early value.

In particular all zero jobs are early, as required by (2.0).  Combining these
facts with `|theta-thetaHat|<=u`, early values are at most `theta+s` and late
values are at least `theta-s`.

Consequently Lemma 4.1 applies with error `s` and yields

```text
P(p,E) <= 4O(p)/3 + (2/3)s.                      (8.6)
```

The normalized learned-mode error is therefore

```text
O_B(Delta+eta).                                   (8.7)
```

This is the central robustness estimate.  It uses no upper bound on a late
processing time.  The unbounded `K_L` term stays in both `P` and `O`, while
only the bounded early statistics have to be learned.

## 9. Fallback mode on a good sample

We show that fallback is safe because it can occur on a good sample only when
the true optimum is already large.

Let `rhoGrid` be the maximum density of a prefix in the full rounded
population, again excluding overflow.  For any fixed prefix, histogram `L1`
error at most `Delta` changes its mass by at most `Delta` and its first moment
by at most `B Delta`.  Since every density denominator is at least one,

```text
|rhoSample-rhoGrid| <= (1+B)Delta.                (9.1)
```

In fallback mode `rhoSample<2/B`.  On `G`, the definition of `gamma` gives

```text
(1+B)Delta <= 1/B.                               (9.2)
```

Thus

```text
rhoGrid <= 3/B.                                   (9.3)
```

Let `thetaStar` be the inverse maximum density of the true, unrounded
population.  If `thetaStar+eta<=B`, round its maximizing prefix upward and,
if necessary, include the rest of the boundary bin.  Original selected work
is `a thetaStar`; rounding adds at most `a eta`, and every additionally
included boundary value is at most `thetaStar+eta`.  Hence the rounded
population has a prefix of inverse density at most `thetaStar+eta`.  Therefore

```text
rhoGrid >= 1/(thetaStar+eta).                     (9.4)
```

If `thetaStar+eta>B`, then `thetaStar>B-eta` directly.  Combining this case
with (9.3)--(9.4), and using `eta<=B/12` for all sufficiently large `n`,
gives

```text
thetaStar >= B/4                                  (9.5)
```

for all sufficiently large `n`.

We next turn a large density threshold into a lower bound on `OPT`.  Split the
true distribution at its maximum-density threshold and use its
`a,h,m,K_E,K_L`.  Equations (3.2) and (3.3) imply

```text
K(p)
  = K_E+2hm+K_L
  >= m^2/thetaStar + 2hm + thetaStar h^2
  = (m+thetaStar h)^2/thetaStar.
```

Since `m=a thetaStar-1` and `h=1-a`,

```text
m+thetaStar h=thetaStar-1.
```

Thus

```text
K(p) >= (thetaStar-1)^2/thetaStar,                (9.6)
O(p) >= (thetaStar-1+1/thetaStar)/2.              (9.7)
```

Since `B=32`, (9.5) gives `thetaStar>=8`, and (9.7) gives the exact
constant

```text
O(p) >= (8-1+1/8)/2 = 57/16.                     (9.8)
```

Finally compare fallback to the clairvoyant optimum. If there are `z` zero
jobs and `l=n-z` positive jobs, every zero completes by time `n`. Their total
extra completion time relative to their first `z` SPT positions is at most
`zn-z(z+1)/2`. Deferring the positive SPT tail until all tests finish adds
exactly `l(l-1)/2`. These quantities sum to `n(n-1)/2`, so

```text
ALG_fallback <= OPT+n(n-1)/2.                     (9.9)
```

Using `OPT>=n^2O(p)` and (9.8),

```text
ALG_fallback
  <= OPT+n^2/2
  <= (1+8/57)OPT
  < 4OPT/3.                                       (9.10)
```

Thus good-sample fallback has no positive excess over the target bound.

## 10. The cost of putting the sample first

In learned mode compare the actual schedule with an ideal prefix-stationary
schedule which uses the same learned `E`, the same sample set, and the same
permutation, but processes a sampled early job immediately after its test.

Let

```text
e_S,e_R = numbers of early jobs in the sample and remainder,
W_S = k+(sum of early sample processing times),
W_R = n-k+(sum of early remainder processing times),
L_S = e_S+(sum of early sample processing times),
L_R = e_R+(sum of early remainder processing times).
```

Conditional on the unordered sample set, its internal order and the remaining
order are independent uniform permutations.  The expected early completion
cost of the ideal prefix-stationary schedule is

```text
(e_S W_S+L_S)/2
  + e_R W_S
  + (e_R W_R+L_R)/2.                              (10.1)
```

The corresponding expected early cost under a fully uniform stationary
order is

```text
((e_S+e_R)(W_S+W_R)+L_S+L_R)/2.                  (10.2)
```

Subtracting (10.2) from (10.1) gives

```text
(e_R W_S-e_S W_R)/2 <= e_R W_S/2.                (10.3)
```

Late completion cost is identical in the two schedules: by (2.0) every late
job is positive and remains pending after its test, and every such job sees
the same total discovery work and the same SPT tail.

In learned mode every early value is at most `B/2`, so

```text
W_S <= k(1+B/2).
```

Thus the cost of forcing the whole sample prefix before the remainder is at
most

```text
n k(1+B/2)/2.                                     (10.4)
```

The actual schedule postpones sampled early processing until all sample tests
are complete.  This does not change the prefix length or any later completion
time.  It can delay at most `k` sampled early jobs by at most `W_S` each, so
it adds at most

```text
k^2(1+B/2).                                       (10.5)
```

Combining (10.4)--(10.5), the normalized sample-order error is

```text
O(kB/n+k^2B/n^2).                                 (10.6)
```

No unbounded sample processing time appears here: overflow sample jobs remain
deferred to the common SPT tail.

## 11. The bad sample event

The raw cost can contain arbitrarily large late processing times. On the bad
event we therefore bound excess over `4OPT/3`, rather than multiplying a raw
cost bound by the bad-event probability. Markov's inequality and
`gamma=1/(B(B+1))` give

```text
Pr(not G)
  <= B(B+1) E Delta
  <= B(B+1) sqrt((d+2)/k).                       (11.1)
```

In learned mode every early value is at most `B/2`, regardless of histogram
accuracy. Lemma 4.2 with `R=B/2` and the exact stationary formula imply, for
the fully uniform comparator,

```text
E ALG_ideal <= OPT+(B/4)n^2.                      (11.2)
```

Put

```text
H_n=(1+B/2)(nk/2+k^2).                            (11.3)
```

Section 10 shows that `H_n` bounds the total sample-first overhead. Thus a
bad learned sample has conditional excess over `4OPT/3` at most
`(B/4)n^2+H_n`. A bad fallback sample has excess at most `n^2/2` by (9.9).
For `B=32`, both branches are covered by `8n^2+H_n`.

On a good learned sample, (8.4)--(8.6) give the explicit bound

```text
E[ALG | S]-4OPT/3
  <= n^2[B^2 Delta+(2/3)(B+1)eta]+H_n.           (11.4)
```

Good fallback excess is nonpositive. The crucial point is that the
sample-order term is charged once globally, whereas only the bounded
`8n^2` excess is multiplied by the bad-event probability.

## 12. Completion of the upper bound

Average the good learned, good fallback, bad learned, and bad fallback cases.
Using (11.1)--(11.4) and `E Delta<=sqrt((d+2)/k)` gives the explicit uniform
estimate

```text
E ALG(p)
  <= 4OPT(p)/3
      +n^2[9472 sqrt((d+2)/k)+704/d]
      +17(nk/2+k^2).                              (12.1)
```

Indeed,

```text
9472 = B^2+8B(B+1),
704  = (2/3)(B+1)B,
17   = 1+B/2                                      (12.2)
```

for `B=32`. For `n>=12^4`, the floors in (7.1) satisfy

```text
sqrt((d+2)/k) <= 2n^(-1/4),
1/d             <= 2n^(-1/4),
k               <= n^(3/4).                     (12.3)
```

Substitution into (12.1), with room for the `k^2` term, yields

```text
E ALG(p) <= 4OPT(p)/3+20378 n^(7/4).              (12.4)
```

For `n<12^4`, the algorithm uses test-all-then-SPT. Its excess over `4OPT/3`
is at most `n^2/2` by (9.9), while
`n^2/2<6n^(7/4)<20378n^(7/4)`. Hence (12.4) holds for every `n`.

Finally `OPT>=n^2/2` turns (12.4) into

```text
E ALG(p)
  <= (4/3+40756 n^(-1/4))OPT(p).                 (12.5)
```

This is uniform over all nonnegative processing vectors. The algorithm never
receives the multiset of processing times.

## 13. Matching binary lower bound

It remains to show that `4/3` cannot be improved.  Let `n` be even and let the
multiset consist of `n/2` zeros and `n/2` jobs of processing time two.  Assign
this multiset uniformly at random to the labels.  The multiset may even be
announced to the algorithm; this only strengthens the lower bound.

Fix a deterministic algorithm which completes every job.  List test outcomes
in the adaptive order in which the algorithm performs tests.  Because the
assignment is uniform and untested labels are symmetric, this outcome list is
a uniform random permutation of the binary multiset, even though the test
times and tested labels are chosen adaptively.

Let `Z_k` be the number of zeros among the first `k` tests and define

```text
Delta = max_{0<=k<=n} |Z_k-k/2|.
```

The logarithm can be avoided by using the bridge martingale.  Put

```text
S_k=2Z_k-k,              m=n/2.
```

For `0<=k<=m`,

```text
M_k=S_k/(n-k)
```

is a martingale: conditional on `S_k`, the expected next increment is
`-S_k/(n-k)`, and hence
`E[S_(k+1)|S_k]=S_k(n-k-1)/(n-k)`.  At the midpoint, the exact
hypergeometric variance is

```text
E[M_m^2]=1/(n-1).
```

Let `A=max_(0<=k<=m)|S_k|`. Doob's `L2` maximal inequality gives

```text
E A^2
  <= 4n^2 E M_m^2
  = 4n^2/(n-1).                                   (13.1)
```

By time reversal, the second-half maximum has the same distribution as `A`.
The square of the overall maximum is at most the sum of the squares of the
two half-maxima. Hence

```text
E max_k |S_k| <= 2sqrt(2)n/sqrt(n-1),
E Delta       <= sqrt(2)n/sqrt(n-1).              (13.2)
```

At physical time `t`, suppose the algorithm has completed `k` tests and has
processed `x` positive jobs.  At most `Z_k+x` jobs have completed.  The machine
has spent at least `k+2x` time, so

```text
completed(t)
  <= Z_k+x
  <= k/2+Delta+x
  = (k+2x)/2+Delta
  <= t/2+Delta.                                    (13.3)
```

Therefore, until time `2(n-Delta)`, the number of unfinished jobs is at least

```text
n-Delta-t/2.
```

Using the area identity for total completion time,

```text
ALG
  = integral_0^infinity unfinished(t) dt
  >= integral_0^(2(n-Delta)) (n-Delta-t/2) dt
  = (n-Delta)^2.                                  (13.4)
```

This bound is pathwise, with no exceptional event.  Taking expectations,
using (13.2), and discarding the nonnegative `E[Delta^2]` term gives

```text
E ALG >= E[(n-Delta)^2]
      >= n^2-2sqrt(2)n^2/sqrt(n-1)
       = n^2-O(n^(3/2)).                          (13.5)
```

The offline optimum of this multiset is exact.  Put `n=2m`.  The `m` zero
blocks of length one come first, followed by `m` blocks of length three:

```text
OPT
  = m(m+1)/2 + sum_{j=1}^m (m+3j)
  = 3m^2+2m
  = 3n^2/4+n.                                     (13.6)
```

Hence the expected ratio under the random assignment is
`4/3-O(n^(-1/2))`.

For a randomized algorithm, average first over its seed and then over the
uniform assignments. Every deterministic seeded strategy satisfies (13.5),
so the joint average does as well.  Consequently at least one fixed
assignment has expected randomized cost at least the joint average.  This is
the finite form of Yao's principle and produces an oblivious fixed instance.

Thus every randomized algorithm has asymptotic competitive ratio at least
`4/3`. Together with (12.5), the ratio is exactly `4/3`.

## 14. Conclusion

The upper algorithm is universal: it uses only `n`, its private random
permutation, and values already revealed by completed tests. In particular,
it is never given the input multiset. Equation (12.5) proves an asymptotic
ratio at most `4/3`, while the fixed oblivious instances from Section 13
force a ratio at least `4/3`. Hence the sharp asymptotic randomized
competitive ratio is `4/3`.
