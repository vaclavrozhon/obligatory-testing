# Stationary thresholds are asymptotically instance-optimal

Supplementary analytic proof draft, revised 6 August 2026.  This is the stronger
announced-multiset instance-optimal statement; it is not needed for the
unknown-multiset `4/3` theorem.  Its fluid algebra is Lean-checked, while the
bounded-grid random-permutation lower transfer is now a public Lean theorem.
The sharper unbounded, mean-sensitive rate stated in this supplementary note
is not separately packaged in Lean.

This note proves the fluid part of the stationary-threshold conjecture and
gives a quantile transfer to every finite announced multiset.
The exact finite statement is false: finite Bellman policies can exploit
random-permutation fluctuations.  The correct statement is an additive
`o(n^2)` sandwich whenever the empirical mean grows slowly enough.

## 1. Model and theorem

Let

\[
M=\{p_1,\ldots,p_n\},
\qquad p_j\ge0,
\]

be announced, while its assignment to job labels is hidden.  The adversary is
oblivious.  A randomized algorithm tests a uniformly random untested label,
so the revealed processing times form a uniformly random permutation of `M`.

Let `VAL(M)` be the minimax expected sum of completion times in this announced
model.  Write `mu_M` for the empirical probability measure of `M` and put

\[
H=1+\int p\,d\mu_M(p)
 =1+\frac1n\sum_{j=1}^n p_j.
\]

The candidate fluid value `Phi(mu_M)` is defined explicitly below.  The target
finite theorem is

\[
\boxed{
n^2\Phi(\mu_M)
-O\!\left(Hn^{3/2}\sqrt{\log n}\right)
\le \operatorname{VAL}(M)
\le n^2\Phi(\mu_M)+\frac12Hn.
}
\]

The constant in the lower bound is universal.  In particular, for every
family with `H=o(sqrt(n/log n))`, and hence for every fixed mean bound,

\[
\operatorname{VAL}(M)
=n^2\Phi(\mu_M)+o(n^2)
\]

uniformly over all such multisets, even when the maximum or the number of
distinct processing times grows with `n`.

Since every schedule has cost at least `n(n+1)/2`, the stationary policy is
instance-optimal up to relative error

\[
O\!\left(H\sqrt{\frac{\log n}{n}}\right).
\]

The upper bound and the fluid theorem below are complete.  The finite lower
bound uses a standard uniform concentration lemma and a whole-measure
quantile coupling.  No bounded-support assumption or good/bad-event split is
needed; constants have not been optimized.

## 2. The maximum-density prefix

First suppose `mu` has finite support

\[
0=p_0<p_1<\cdots<p_d
\]

with masses `mu_i`.  For `i>0`, choose an amount

\[
0\le x_i\le\mu_i
\]

of class `i` to process during the testing phase.  One unit mass of tests,
together with these early processing operations, has work

\[
w(x)=1+\sum_{i=1}^d p_i x_i
\]

and completes mass

\[
a(x)=\mu_0+\sum_{i=1}^d x_i.
\]

Its completion density is

\[
\rho(x)=\frac{a(x)}{w(x)}.
\]

Let `x*` maximize `rho`, and put

\[
a_*=a(x^*),
\qquad
w_*=w(x^*),
\qquad
\rho_* = \frac{a_*}{w_*},
\qquad
\theta_* = \frac1{\rho_*}.
\]

If there are no zeros, the all-zero vector has density zero and is harmless;
some positive coordinate is selected.

### Lemma 1 (the density maximizer is a threshold)

There is a maximizer satisfying

\[
x_i^*=\begin{cases}
\mu_i,&p_i<\theta_*,\\
0,&p_i>\theta_*,
\end{cases}
\]

with an arbitrary amount of a class for which `p_i=theta_*`.

**Proof.** At a point of density `rho`, increasing coordinate `x_i` changes
the ratio with the sign of

\[
1-\rho p_i.
\]

Thus every coordinate with `p_i<1/rho` is saturated, every coordinate with
`p_i>1/rho` is zero, and only equality permits a fractional coordinate.  This
is exactly the asserted threshold structure. `square`

For an empirical distribution it is enough to sort the occurrences and scan
the prefixes.  If `E_k` consists of zero plus the first `k` positive
occurrences, compute

\[
\rho_k
=\frac{|E_k|/n}
       {1+n^{-1}\sum_{j\in E_k}p_j}.
\]

Any maximizing prefix gives the stationary policy.  Equal values can be
included together; if an atom is exactly tied, including none, some, or all
of it has the same density.

## 3. The fluid deadline relaxation

Let `T` be the fraction of tests completed by scaled time `s`, and let `c_i`
be the fraction of class-`i` jobs completed by processing.  Every fluid
schedule satisfies

\[
0\le T\le1,
\qquad
0\le c_i\le\mu_iT,
\qquad
T+\sum_i p_i c_i\le s.
\]

The completed mass is

\[
\mu_0T+\sum_i c_i.
\]

Define the deadline envelope

\[
F_\mu(s)
=\max\left\{
\mu_0T+\sum_i c_i:
0\le T\le1,
0\le c_i\le\mu_iT,
T+\sum_i p_i c_i\le s
\right\}.
\]

Every feasible fluid schedule has completed at most `F_mu(s)` mass by time
`s`.  Therefore

\[
\int_0^\infty(1-F_\mu(s))\,ds
\]

is a lower bound on its normalized total completion time.  The key fact is
that one schedule attains this envelope simultaneously at every time.

## 4. Solving the completion envelope

Let `nu` be the residual processing-time measure after removing `x*`; that is,
`nu_i=mu_i-x_i*` for `i>0`.  All support points of `nu` are at least
`theta_*`, apart from an arbitrary tied fraction.

Consider the following curve `F*`.

1. On `0<=s<=w_*`, set

   \[
   F^*(s)=\rho_*s.
   \]

2. At time `w_*`, all tests and all `x*` processing are complete, so
   `F*(w_*)=a_*`.

3. After `w_*`, process `nu` in nondecreasing processing-time order.  Thus the
   slopes of `F*` are `1/p_i`, in nonincreasing order.

Because every residual `p_i>=theta_*=1/rho_*`, the slope does not increase at
`w_*`.  Hence `F*` is nondecreasing and concave, with `F*(0)=0`.

### Lemma 2 (pointwise completion envelope)

For every `s>=0`,

\[
F_\mu(s)=F^*(s).
\]

**Proof.** Take any feasible deadline point `(T,c)`.  If `T=0`, then `c=0`.
Otherwise put

\[
x_i=\frac{c_i}{T},
\qquad
w(x)=1+\sum_i p_ix_i,
\qquad
a(x)=\mu_0+\sum_i x_i.
\]

The point has work `T w(x)` and completion `T a(x)`.

First consider a full-test endpoint `T=1`.  If `w(x)<=w_*`, maximality of
`rho_*` gives

\[
a(x)\le\rho_*w(x)=F^*(w(x)).
\]

If `w(x)>=w_*`, then `x` is a feasible fractional selection of processing
mass with budget `w(x)-1`.  The maximum number of jobs under such a budget is
obtained by taking processing times in increasing order.  By Lemma 1, `x*` is
exactly the initial part of this fractional-knapsack order, and the tail of
`F*` continues the same order.  Consequently,

\[
a(x)\le F^*(w(x)).
\]

Now use concavity and `F*(0)=0`:

\[
F^*(Tw(x))
\ge T F^*(w(x))
\ge T a(x).
\]

Since `Tw(x)<=s` and `F*` is nondecreasing, the completion of every feasible
deadline point is at most `F*(s)`.  This proves `F_mu<=F*`.

For the reverse inequality, repeat infinitesimal blocks consisting of `dT`
tests followed by `x_i^* dT` processing of each selected class.  Each block
has work `w_*dT` and completes mass `a_*dT`.  As the block size tends to zero,
the resulting completion curve is `rho_*s` until `T=1`.  Then process the
residual classes in SPT order.  This feasible fluid schedule attains `F*` at
all times. `square`

This is the special fluid version of a maximum-density initial-set
decomposition.  It is closely related to Sidney decompositions for
precedence-constrained weighted completion time, but the proof above is
self-contained for this model.

## 5. Explicit fluid value

The fluid optimum is

\[
\Phi(\mu)=\int_0^\infty(1-F_\mu(s))\,ds.
\]

The discovery phase contributes

\[
\int_0^{w_*}(1-\rho_*s)\,ds
=w_*-\frac12a_*w_*
=w_*\left(1-\frac{a_*}{2}\right).
\]

The SPT tail contributes

\[
\frac12
\iint\min(p,q)\,d\nu(p)\,d\nu(q).
\]

Therefore

\[
\boxed{
\Phi(\mu)
=w_*\left(1-\frac{a_*}{2}\right)
+\frac12
 \iint\min(p,q)\,d\nu(p)\,d\nu(q).
}
\]

This is both a lower bound for every fluid policy and the value of the single
stationary-threshold policy.

## 6. Exact finite upper bound

Choose a whole-atom maximizing prefix `E` of the empirical distribution.  Let

\[
e=|E|,
\qquad
W=n+\sum_{j\in E}p_j,
\qquad
L_E=e+\sum_{j\in E}p_j,
\qquad
h=n-e.
\]

Run the following randomized policy.

1. Test a uniformly random untested label.
2. If its processing time belongs to `E`, process it immediately.
3. Otherwise defer it.
4. After all tests, process the deferred jobs in SPT order.

The discovery phase is a uniformly random permutation of blocks.  An early
block has length `1+p_j` and completes its job; a deferred block has length
one and completes no job.

For each early job, every other discovery block precedes it with probability
one half.  Hence the expected sum of early completion times is

\[
\frac12eW+\frac12L_E.
\]

Every late job receives the common discovery-phase offset `W`.  Its tail cost
is its own processing time plus `min(p_i,p_j)` for every unordered pair of
late jobs.  Therefore

\[
\begin{aligned}
\mathbb E[\operatorname{ALG}_{\rm stat}]
= {}&\frac12eW+\frac12L_E+hW\\
&+\sum_{j\notin E}p_j
 +\sum_{\{i,j\}\subseteq M\setminus E}\min(p_i,p_j).
\end{aligned}
\]

Comparing this expression with the empirical-measure formula for `Phi` gives
the exact identity

\[
\boxed{
\mathbb E[\operatorname{ALG}_{\rm stat}]
=n^2\Phi(\mu_M)
 +\frac12\left(e+\sum_{j=1}^np_j\right).
}
\]

In particular,

\[
\operatorname{VAL}(M)
\le n^2\Phi(\mu_M)+\frac12Hn.
\]

No law of large numbers is needed for the upper bound.

## 7. Random-permutation lower bound

For the lower bound, assign `M` uniformly at random to labels.  Under any
adaptive deterministic algorithm, the sequence of revealed values is a
uniform random permutation

\[
P_1,\ldots,P_n
\]

of `M`.

For every prefix length `k` and threshold `z`, let

\[
N_k(z)=|\{j\le k:P_j\le z\}|,
\qquad
N(z)=|\{j\le n:p_j\le z\}|.
\]

Define the two-parameter prefix discrepancy

\[
\Delta
=\max_{0\le k\le n}\max_z
\left|N_k(z)-\frac{k}{n}N(z)\right|.
\]

It is enough to maximize over the at most `n+1` thresholds immediately after
distinct values of `M`.

### Lemma 3 (uniform permutation concentration)

For universal constants `c,C>0`,

\[
\Pr(\Delta\ge u)
\le 2(n+1)^2e^{-cu^2/n},
\qquad
\mathbb E\Delta\le C\sqrt{n\log n}.
\]

**Proof.** For fixed `k,z`, `N_k(z)` is hypergeometric with mean
`kN(z)/n`.  Hoeffding--Serfling concentration gives a tail of the form

\[
\Pr(|N_k(z)-kN(z)/n|\ge u)
\le2\exp(-c u^2/n).
\]

A union bound over at most `(n+1)^2` pairs gives the first display.  Integrate
this tail, splitting the integral at `C_0 sqrt(n log n)` for a sufficiently
large universal `C_0`, to obtain the expectation bound. `square`

Serfling's original sampling-without-replacement inequality is:
<https://projecteuclid.org/download/pdf_1/euclid.aos/1176342611>.

### Lemma 4 (whole-measure prefix quantile transfer)

For a finite subprobability measure `lambda` on `R_+`, write

\[
Q_\lambda(u)=\inf\{z\ge0:\lambda([0,z])\ge u\},
\qquad 0<u\le\lambda(\mathbb R_+),
\]

and set `Q_lambda(0)=0`.  At an atom, integration of `Q_lambda` corresponds
to taking the required fractional amount of that atom.  Thus

\[
W_\lambda(c)=\int_0^c Q_\lambda(u)\,du
\]

is exactly the least processing work of a submeasure of `lambda` having mass
`c`.

Fix a prefix length `k` and define the two subprobability measures

\[
R_k=\frac1n\sum_{j\le k}\delta_{P_j},
\qquad
A_k=\frac{k}{n}\mu_M.
\]

Both have total mass `T=k/n`, and the definition of `Delta` gives

\[
\sup_z|R_k([0,z])-A_k([0,z])|\le\delta,
\qquad \delta=\Delta/n.                           \tag{7.1}
\]

If a schedule has completed mass `c` from the revealed prefix using scaled
processing work `q`, then the deterministic supply `A_k` contains mass
`(c-delta)_+` whose processing work is at most `q`.  More precisely, when
`c>=delta`,

\[
\boxed{
\int_0^{c-\delta}Q_{A_k}(v)\,dv
\le
\int_\delta^c Q_{R_k}(u)\,du
\le q.}                                           \tag{7.2}
\]

**Proof.** Replacing the completed revealed submeasure by the shortest mass
`c` of `R_k` can only decrease its work, so

\[
\int_0^cQ_{R_k}(u)\,du\le q.
\]

From (7.1), for every `delta<u<=c`,

\[
Q_{A_k}(u-\delta)\le Q_{R_k}(u).                 \tag{7.3}
\]

Indeed, whenever `R_k([0,z])>=u`, (7.1) implies
`A_k([0,z])>=u-delta`; taking infima, with right limits at atom endpoints,
gives (7.3).  Integrating (7.3) and substituting `v=u-delta` proves (7.2).
If `c<delta`, the claimed retained mass is zero and the statement is
immediate.  This argument uses the whole measures, including the zero atom;
there is no extra loss for separating zeros. `square`

### Lemma 5 (pointwise discrete completion bound)

For every realized permutation, at every physical time `t`, every adaptive
policy has completed at most

\[
nF_{\mu_M}(t/n)+\Delta
\]

jobs.

**Proof.** Suppose `k` tests have completed by time `t`, put `T=k/n`, and let
the completed jobs have scaled mass `c` and scaled processing work `q`.
Completed zero jobs are included in `c` and contribute zero to `q`.  Since
the machine has also performed the tests,

\[
T+q\le t/n.
\]

By Lemma 4, the deterministic supply `A_k=T mu_M` has a submeasure of mass
`(c-delta)_+` and processing work at most `q`.  Together with `T` tests this
is a feasible point of the deadline LP defining `F_mu(t/n)`.  Hence

\[
F_{\mu_M}(t/n)\ge(c-\delta)_+,
\]

which rearranges to `nc<=nF_mu(t/n)+Delta`. `square`

### Integrating the pointwise bound

The fluid completion curve equals one by time `H`.  Using the area identity
for total completion time and Lemma 5,

\[
\begin{aligned}
\operatorname{ALG}
&=\int_0^\infty
  \bigl(n-\#\text{ completed jobs at time }t\bigr)\,dt\\
&\ge
  \int_0^{nH}
  \left[n\bigl(1-F_{\mu_M}(t/n)\bigr)-\Delta\right]dt\\
&=n^2\Phi(\mu_M)-Hn\Delta.
\end{aligned}
\]

This inequality is pathwise; its right-hand side is allowed to be negative,
so no good/bad-event bookkeeping is needed.  Taking expectations and using
Lemma 3 gives

\[
\mathbb E[\operatorname{ALG}]
\ge n^2\Phi(\mu_M)
-O\!\left(Hn^{3/2}\sqrt{\log n}\right).
\]

This holds for every deterministic algorithm under the uniform random
assignment.  Yao's principle therefore gives the same lower bound for
randomized algorithms against an oblivious adversary, even though the
multiset is announced for free.

Combining this with Section 6 proves the theorem stated in Section 1.

## 8. Worst-case competitive ratio: exactly `4/3`

We can optimize the instance-specific fluid value exactly over all
processing-time distributions.  The upper bound below is in fact finite,
not merely asymptotic.

Let `eta` be the early subdistribution selected by the maximum-density
threshold and `nu` the deferred subdistribution.  Write

\[
a=\eta(\mathbb R_+),
\qquad
h=\nu(\mathbb R_+)=1-a,
\qquad
m=\int p\,d\eta(p),
\]

and

\[
K_E=\iint\min(p,q)\,d\eta(p)d\eta(q),
\qquad
K_L=\iint\min(p,q)\,d\nu(p)d\nu(q).
\]

If `theta=1/rho_*`, the maximum-density identity is

\[
1+m=a\theta.
\]

All early values are at most `theta` and all late values are at least
`theta`.  The stationary value and offline value are

\[
\Phi
=a\theta\left(1-\frac a2\right)+\frac12K_L
\]

and

\[
O
=\frac12\left(1+K_E+2hm+K_L\right).
\]

The cross term is `2hm` because the minimum of an early and a late value is
the early value.

Two pointwise inequalities contain the whole extremal argument.  For early
`p,q<=theta`,

\[
\min(p,q)\ge\frac{pq}{\theta},
\]

and hence

\[
\theta K_E\ge m^2.
\]

For late `p,q>=theta`,

\[
\min(p,q)\ge\theta,
\]

and hence

\[
K_L\ge\theta h^2.
\]

Using `h=1-a` and `m=a theta-1`, direct expansion gives the exact certificate

\[
\boxed{
2\theta(4O-3\Phi)
=(\theta-2)^2
+4(\theta K_E-m^2)
+\theta(K_L-\theta h^2).
}
\]

Every term on the right is nonnegative.  Therefore

\[
\Phi\le\frac43O
\]

for every distribution.

For the empirical measure of a finite instance, Section 6 and the exact SPT
formula read

\[
\mathbb E\operatorname{ALG}_{\rm stat}
=n^2\Phi+\frac12\left(e+\sum_i p_i\right),
\]

\[
\operatorname{OPT}
=n^2O+\frac12\left(n+\sum_i p_i\right).
\]

Since `e<=n`, the diagonal correction of the stationary policy is at most
the corresponding correction of `OPT`, and therefore certainly at most
`4/3` times that correction.  Combining this with `Phi<=4O/3` gives the exact
finite guarantee

\[
\boxed{
\mathbb E\operatorname{ALG}_{\rm stat}
\le\frac43\operatorname{OPT}.}
\]

This conclusion has no boundedness or asymptotic assumption.

Equality is attained by

\[
\mu^*=\frac12\delta_0+\frac12\delta_2.
\]

Here `theta=2`, `Phi=1`, and `O=3/4`.  Equality in the two pair inequalities
also shows the extremal shape: early positive mass can only lie at the
threshold, the remaining early mass lies at zero, and the tail lies at the
threshold.  The density identity then forces zero mass `1/theta`; maximizing
the resulting binary ratio forces `theta=2`.

Consequently, the announced-multiset randomized model has asymptotic
worst-case competitive ratio exactly

\[
\boxed{\frac43}.
\]

The same distribution is a `4/3` Yao lower bound for the original
unknown-multiset model because announcing the multiset only helps the
algorithm.  The matching sample-based upper bound is proved separately in
`RANDOMIZED_UNKNOWN_MULTISET_PROOF.md`.

The finite-dimensional algebraic certificate, including equality, is checked
in `SchedulingPaper/RandomizedAnnouncedFluid.lean`.

## 9. Interpretation

The theorem explains why the exact Bellman threshold can fluctuate while a
single threshold is sufficient asymptotically.

- A typical random prefix differs from the proportional fluid prefix by only
  `O(sqrt(n log n))` jobs in expectation uniformly over time and thresholds.
- An adaptive policy can exploit these deviations, but Lemma 5 limits the
  resulting completion-count advantage at every time to `Delta` jobs.
- The relevant scheduling horizon is exactly `Hn`, so the total possible
  advantage is `O(H n^(3/2)sqrt(log n))`.
- The stationary policy already matches the fluid optimum up to an exact
  `O(n)` correction.

The threshold changes only at the final phase transition: while tests remain,
use `theta_*`; after the last test, the discovery block disappears and all
deferred jobs are processed in SPT order.

## 10. Sanity check: binary support

Let

\[
\Pr(P=0)=\alpha,
\qquad
\Pr(P=p)=\beta.
\]

Deferring the positive class gives density `rho_0=alpha`, while including it
gives

\[
\rho_1=\frac1{1+\beta p}.
\]

The positive class is processed early exactly when

\[
p<\frac1\alpha.
\]

At `alpha=beta=1/2` and `p=2`, the two densities tie.  Both immediate
processing and complete deferral have fluid value one, while offline has
fluid value `3/4`, giving ratio `4/3`.  Finite adaptive Bellman policies gain
only the subquadratic random-bridge correction.

## 11. What is and is not proved

Proved in this draft:

1. the density maximizer is a single threshold;
2. its fluid schedule pointwise dominates every other fluid schedule;
3. the explicit formula for `Phi(mu)`;
4. the exact expected cost identity for the finite stationary policy;
5. reduction of the discrete lower bound to uniform permutation discrepancy;
6. the mean-sensitive pathwise lower bound and resulting `o(n^2)` sandwich;
7. the sharp worst-case fluid ratio `4/3` and its critical binary witness;
8. the exact finite `4/3` guarantee for the stationary policy.

Still worth checking carefully before promoting this to the paper:

1. formalize the whole-measure quantile inequality (7.2), including
   generalized-inverse endpoint conventions;
2. choose and state explicit numerical constants in Lemma 3;
3. handle randomization at a threshold atom in a notation-independent way;
4. decide whether to replace the `sqrt(log n)` union bound by a sharper
   permutation empirical-process inequality;
5. connect the abstract completion envelope to the operational Lean model;
6. formalize the finite Yao averaging step.  The unknown-multiset transfer is
   handled separately by the sublinear-sample theorem.

For context, maximum-density initial sets are classical in precedence-
constrained weighted completion scheduling; see Sidney's original
decomposition paper:
<https://pubsonline.informs.org/doi/10.1287/opre.23.2.283>.  The proof here
only uses the much simpler one-dimensional fractional structure of obligatory
testing.  Sidney's 1981 paper gives a broader decomposition framework:
<https://pubsonline.informs.org/doi/10.1287/moor.6.2.190>.
