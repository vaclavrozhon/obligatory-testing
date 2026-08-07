# The two-phase structure for optional processing-time information

## 1. Executive conclusion

### 1.1 Target theorem and current status

Fix `L<infinity`.  The adversary chooses a labelled vector
`p=(p_1,...,p_n) in [0,L]^n` before the algorithm draws any random bits.  A
job may either be run blind for time `p_i`, or tested for one unit and then,
possibly after a delay, run for time `p_i`.  A zero job tested by the
algorithm completes at the end of its test.  Let `C_A(p)` denote the sum of
completion times of a randomized nonanticipating policy `A`.

For a multiset `M`, let `D_M` be its empirical probability distribution and
define `Phi(D_M)` by (30)--(32).  The target is a deterministic sequence
`epsilon_L(n)->0` and a single policy `A*`, which knows `n,L` but is not told
`M`, such that simultaneously for every size-`n` multiset `M subseteq [0,L]`,

```text
max over labellings sigma  E C_A*(sigma(M))
    <= n^2 Phi(D_M)+epsilon_L(n)n^2,                  (A)

inf over randomized A that are told M
    max over labellings sigma E C_A(sigma(M))
    >= n^2 Phi(D_M)-epsilon_L(n)n^2.                  (B)
```

If (A)--(B) are established, even advance knowledge of the multiset cannot improve on the universal
sampled policy by more than `o(n^2)`.  The expectation in both displays is
only over the policy's private randomness; every labelling selected in the
maximum is a fixed oblivious input.

Up to `o(n^2)`, `A*` has exactly the following form: take an `o(n)` pilot
sample, test a deterministic fraction `q` of the remaining jobs while
immediately completing outcomes below a threshold `tau`, stop all testing,
run the tested residual outcomes below the empirical mean in SPT order, run
all untouched jobs blind, and finish the tested residual outcomes above the
mean in SPT order.  The number `q` minimizes the explicit quadratic (28).

The correct canonical policy is slightly richer than

```text
test with one threshold -> blind everything -> tested tail.
```

For an unweighted job-size distribution `D` and a unit testing time, define

```text
mu  = E[P],
tau = the unique solution of E[(tau-P)^+] = 1.
```

When `tau < mu`, the canonical policy has the form

```text
Phase I:
    test unknown jobs;
    whenever a test reveals p < tau, process that job immediately;
    stop testing at an optimally chosen stopping time;

Phase II:
    process known jobs tau < p < mu in increasing p;
    process every still-unknown job blindly (the YOLO block);
    process known jobs p > mu in increasing p.
```

When `tau >= mu`, testing is never useful and the policy is pure YOLO.

The corresponding structure is an exact theorem in the **Bayesian i.i.d.
stochastic model** of Levi, Magnanti, and Shaposhnik, under the assumptions
listed precisely in Section 11.  Sections 5--7 below record the local
interchange calculations that explain that theorem; they are not, by
themselves, an exchange proof for a general adaptive policy tree.  More
importantly for our model,
Section 8 gives a separate completion-envelope proof in the announced-multiset
fluid limit.  It avoids trying to interchange nodes of an adaptive policy
tree: after conditioning on the final tested fraction, every policy prefix is
relaxed to a fractional knapsack whose items are the test module, the known
processing classes, and the blind module.  This proves that no adaptive policy
improves the four-block policy by more than `o(n^2)` on bounded finite-support
announced multisets.  The extension in Sections 12--13 to arbitrary bounded
multisets and an unannounced multiset depends on two finite technical lemmas:
the kernel expansion (27a) and the uniform grid-envelope transfer (36).
Sections 8.6 and 12.3 now give explicit candidate proofs rather than merely
announcing them.  Until those proofs receive an independent line-by-line
check (and eventually Lean verification), (A)--(B) remain a target theorem,
not a result we should advertise as finished.

Apart from the initial sublinear sample, the only decision not fixed by the
structural theorem is **when to stop testing**.  In the fluid limit this
reduces to a one-dimensional optimization over the tested fraction `q`.

## 2. Model

There are `n` non-preemptive jobs on one machine.  Initially every job is
unknown and has processing time distributed as `P ~ D`.

At an idle machine the policy can:

1. test an unknown job, spending one unit of machine time and revealing `p`;
2. process an unknown job blindly, spending its actual `p` and completing it;
3. process a previously tested job of known length `p`.

The objective is the expected sum of completion times.  In the exact
stochastic theorem the jobs are i.i.d.  In the announced-multiset version the
algorithm applies a uniformly random permutation to the labels, so successive
unknown jobs are draws without replacement from the announced empirical
distribution.

## 3. The two relevant ratios

### 3.1 The YOLO ratio

An unknown job has expected processing time

```text
mu = E[P].
```

Blindly processing it completes one job using expected work `mu`.  Its
completion density is therefore `1/mu`.  Equivalently, in an expected-SPT
comparison we can treat every unknown job as having processing ratio `mu`.

### 3.2 The testing threshold

Define `tau` by

```text
E[(tau-P)^+] = 1.                                      (T)
```

The left side is continuous and nondecreasing in `tau`, is zero below the
support, and tends to infinity, so the solution exists.  It is unique apart
from harmless flat/tie conventions.

Let

```text
a = Pr[P < tau],
m = E[P 1{P < tau}].
```

Equation (T) says

```text
a tau - m = 1,
```

or equivalently

```text
tau = (1+m)/a.                                         (1)
```

One unit mass of tests, together with immediate processing of all revealed
jobs below `tau`, uses expected work `1+m` and completes mass `a`.  Hence its
completion density is

```text
a/(1+m) = 1/tau.
```

Thus `tau` is precisely the reciprocal of the best test-module density.  It
is the same stationary threshold that appears in the obligatory-testing
fluid problem.

Testing can compete with YOLO only when

```text
1/tau > 1/mu,
```

that is, when `tau < mu`.

## 4. Pairwise delay accounting

For two completed jobs `i,j`, putting `i` before `j` makes the processing time
of `i` delay `j`.  With unit weights, the pair contribution is therefore the
length of the earlier job.  This gives the usual SPT interchange rule.

The same accounting makes the value of a test transparent.  Moving a test
across one job changes two things:

1. the one-unit test either does or does not delay that job;
2. if the test reveals a sufficiently short job, testing earlier permits the
   revealed job to be moved before the comparison job.

All other jobs see the same total work in the two **fixed schedule words**, so
their contributions cancel.  This gives the two local calculations below.
It does not yet justify moving the action across an adaptive continuation:
the test outcome can change which continuation branch is visited.

## 5. Local calculation I: jobs below `tau` are immediate

**Local comparison 1.** Suppose a tested pending job has known length
`x < tau`, and compare the two displayed fixed continuations below.

### Proof

Compare two locally identical policies:

```text
A: test a new job first, then process x at its appropriate position;
B: process x first, then perform the same test.
```

Testing first makes the unit test delay job `x`, which costs `1`.  Its only
possible benefit is when the test reveals `P < x`: policy A can put `P` before
`x`, saving the pairwise inversion cost `x-P`.  Therefore

```text
cost(A)-cost(B) = 1 - E[(x-P)^+].                       (2)
```

Because `x < tau`, monotonicity and (T) give

```text
E[(x-P)^+] < E[(tau-P)^+] = 1.
```

Thus (2) is positive, so B is better for this fixed continuation.  The exact
claim that every optimal adaptive policy drains such a job requires a
Bellman dominance argument; it follows in the LMS model from their low-ratio
lemma cited in Section 11.  Equation (2) is intuition for that lemma, not a
standalone proof of it. `QED`

For a finite distribution with atoms at the boundary, weak inequalities and
arbitrary tie breaking give the same value.

## 6. Local calculation II: no test after a non-low job

Assume from now on that `tau < mu`.

**Local comparison 2.** For the two displayed fixed schedule words, moving a
test left is beneficial after either

1. a known job of length `x > tau`, or
2. an unknown job blindly.

### Known comparison job

Compare

```text
A: process known x, then test;
B: test first; if P < tau, process P immediately; then process x.
```

Moving the test before `x` costs one unit of delay to `x`.  If `P < tau`, it
allows the shorter revealed job to move before `x`, saving `x-P`.  Therefore

```text
cost(B)-cost(A)
  = 1 - E[(x-P) 1{P<tau}].                             (3)
```

Since `x > tau`,

```text
E[(x-P) 1{P<tau}]
  > E[(tau-P)^+]
  = 1.
```

Hence (3) is negative: testing before `x` is better.

### Blind comparison job in the i.i.d. model

Let `X` be the processing time of the blind job and `P` the outcome of the
test.  Independence gives `E[X]=mu`, so the identical calculation yields

```text
cost(test before blind)-cost(blind before test)
  = 1 - E[(mu-P)1{P<tau}].                             (4)
```

Because `mu > tau`, the expectation in (4) is strictly larger than
`E[(tau-P)^+]=1`.  Thus a test should be moved before a blind execution.

### Blind comparison without replacement

There is also a direct finite-pool analogue.  Suppose the current unknown
pool has size `N`, mean `mu_R`, and current threshold `tau_R`.  Let `Y` be the
job selected for testing and `X` a distinct job selected for blind execution.
Conditional on `Y`,

```text
E[X | Y] = (N mu_R-Y)/(N-1).
```

Consequently,

```text
E[(X-Y)1{Y<tau_R}]
  = N/(N-1) E[(mu_R-Y)1{Y<tau_R}]
  > N/(N-1) E[(tau_R-Y)^+]
  = N/(N-1) > 1
```

whenever `tau_R < mu_R`.  Thus the same adjacent exchange strictly favors
test-before-blind in the announced-pool model.  The remaining technical issue
is only that `tau_R` and `mu_R` evolve after observations; concentration in
Section 8 makes them asymptotically stationary.

### Heuristic consequence and the missing adaptive step

If these local swaps could be performed without changing the continuation
branch, repeating them would show:

> All tests occur in one prefix, interleaved only with immediate completions
> of tested jobs below `tau`.  Once the policy performs any medium/high known
> job or any blind job, it never tests again.

For an adaptive policy tree, however, the decision to test after a blind job
may depend on the blind realization, and the continuation after the moved
test may itself contain further tests.  Moving the test can therefore change
which branch exists, so the preceding paragraph is not a proof.  In the
Bayesian i.i.d. model the stopping-time structure follows instead from the
Bellman induction of LMS (Section 11).  In the announced-multiset fluid model
we avoid this issue entirely through the completion envelope in Section 8.

## 7. What happens after testing stops

Once the policy stops testing, the problem contains only:

* known jobs with deterministic lengths `p`;
* exchangeable unknown jobs, each with expected length `mu`, which will all be
  processed blindly.

The expected interchange comparison is exactly SPT:

* two known jobs are ordered by increasing `p`;
* a known job `p` goes before an unknown job iff `p < mu`;
* all unknown jobs are equivalent and therefore form one contiguous block.

The known jobs below `tau` have already been drained by Lemma 1.  Since
`tau < mu`, the stop phase is consequently

```text
known tau < p < mu, in SPT order
-> every unknown job blindly
-> known p > mu, in SPT order.
```

Conditional on the no-more-testing decision, this proves the ordering of the
last three blocks.  Combining it with the LMS Bellman theorem, or separately
with the fluid envelope below, gives the four-block canonical form.

If instead `tau >= mu`, the YOLO module has at least as high a completion
density as the best test module.  The Bellman argument of Levi, Magnanti, and
Shaposhnik shows that testing is never optimal.  From an empty
initial state the policy is therefore pure YOLO.  This is their long-test
regime specialized to unit weights.

## 8. The announced-multiset fluid theorem

The LMS structure theorem is exact for independent jobs; the local
calculations in Sections 5--7 are only its intuition.  Our adversarial
model is different: a bounded multiset is announced, its values are hidden
behind labels, and the randomized policy touches those labels in a random
order.  Trying to transplant the exchange proof directly is dangerous,
because moving a test in a policy tree changes the information available to
the continuation policy.  The following proof never interchanges policy-tree
nodes.  Instead it upper-bounds how much job mass an arbitrary policy can have
completed by every physical time.

### 8.1 Precise statement

Let

```text
0 = p_0 < p_1 < ... < p_s <= Pmax
```

be a fixed finite support and let `D_i=Pr[P=p_i]`.  Assume `mu=E[P]>0`.
Let `M_n` be announced `n`-job multisets whose empirical frequencies converge
to `D`.  The assignment of occurrences to labels is oblivious.  A randomized
policy may test an untouched label for one unit of time, process an untouched
label blindly, or process a tested pending job.

Define

```text
rho = max_{0<=x_i<=1}
      (D_0 + sum_{i>0} D_i x_i)
      ---------------------------------,               (10)
      (1   + sum_{i>0} p_i D_i x_i)

tau = 1/rho.
```

The fractional variables only matter for an atom at the boundary.  The usual
fractional-knapsack comparison shows that a maximizer includes every
`p_i<tau`, excludes every `p_i>tau`, and may mix arbitrarily at `p_i=tau`.
Indeed, adding outcome mass of length `p_i` raises the current ratio exactly
when `1/p_i>rho`, equivalently `p_i<tau`; removing mass gives the reverse
condition.  Multiplying `rho=a/w` by `tau=1/rho` consequently gives

```text
E[(tau-P)^+] = 1.                                     (11)
```

Let `F_D(q)` be the four-block cost in Section 9, with boundary atoms split
according to the maximizing `x_i` and ties at `mu` placed arbitrarily.

**Theorem 3 (announced-multiset two-phase theorem).** If `tau<mu`, then

```text
VAL(M_n)/n^2 -> min_{0<=q<=1} F_D(q).                  (12)
```

Here `VAL` is the minimax expected online cost when the multiset is announced
but its labeling is chosen obliviously.  In particular, there exists an
asymptotically optimal policy of the form

```text
test + immediately process p<tau
-> stop testing
-> known tau<p<mu in SPT order
-> blind all untouched jobs
-> known p>mu in SPT order.
```

No adaptive policy has a smaller leading `n^2` coefficient.  If `tau>=mu`,
pure YOLO is optimal at fluid scale and `VAL(M_n)/n^2 -> mu/2`.

The proof has two parts.  First we solve the deterministic fluid problem for
every fixed final tested fraction `q`.  Then a predictable-sampling
concentration lemma transfers its completion envelope to every adaptive
finite policy.

### 8.2 The prefix fluid relaxation

Fix a final tested fraction `q`.  Consider an arbitrary prefix of a fluid
schedule and write

```text
t   = mass tested so far,
b   = mass completed blindly so far,
c_i = tested mass of class i>0 processed so far.
```

A test of a zero job completes it, so the completed mass is

```text
y = D_0 t + b + sum_{i>0} c_i.                         (13)
```

The physical work used is

```text
x = t + mu b + sum_{i>0} p_i c_i.                     (14)
```

Every actual schedule prefix satisfies the relaxation

```text
0 <= t <= q,
0 <= b <= 1-q,
0 <= c_i <= D_i t.                                    (15)
```

The last inequality is simply the revelation constraint: class `i` cannot be
processed as a known job faster than tests reveal it.  Define the maximum
completion envelope

```text
H_q(x) = max { D_0 t+b+sum_i c_i : (14)--(15),
                                      used work <= x }.
                                                                    (16)
```

Every feasible fluid policy with final tested fraction `q` has completed at
most `H_q(x)` mass by work time `x`.  Therefore its remaining-mass curve is at
least `1-H_q(x)`, and the area identity gives

```text
cost >= integral (1-H_q(x)) dx.                        (17)
```

It remains to solve the small LP (16).

### 8.3 Reduction of the envelope to fractional knapsack

Let `L` be the positive classes selected by a maximizer of (10), including a
chosen fraction of a possible atom at `tau`, and put

```text
a = D_0 + sum_{i in L} D_i,
w = 1   + sum_{i in L} p_i D_i.
```

Then `a/w=rho=1/tau`.  For any feasible `(t,c)` involving only the test and
the selected low classes,

```text
D_0 t + sum_{i in L} c_i
--------------------------------- <= rho.              (18)
t       + sum_{i in L} p_i c_i
```

Indeed, divide by `t` and set `x_i=c_i/(D_i t)`; the resulting ratio is one
of the candidates in (10).  If `t=0`, the claim is trivial.

Now take any feasible point of (16).  Split its work and completions into

1. the test together with processed classes in `L`;
2. processed tested classes outside `L`;
3. blind executions.

By (18), the first part can be replaced, with no more work and no fewer
completions, by a fractional amount of the **full test module**

```text
one unit test mass + all its L outcomes,
work w, completion mass a.
```

Here is the exact replacement calculation.  Let

```text
y_L = D_0 t+sum_{i in L} c_i,
x_L = t+sum_{i in L} p_i c_i,
lambda = y_L/a.
```

The revelation constraints give `y_L<=at`, hence `lambda<=t<=q`.  Inequality
(18) gives `y_L<=rho x_L=(a/w)x_L`, hence
`lambda w<=x_L`.  Replacing the original low part by `lambda` full modules
therefore preserves its completed mass exactly and weakly decreases its
work.  For the purpose of an upper bound, relax the remaining tested-class
capacities from `c_i<=D_i t` to `c_i<=D_i q`.  We have reduced (16) to an
ordinary fractional knapsack with the following item types:

(If an atom at `tau` is split, regard its selected and unselected fractions
as two virtual classes.)

| item | capacity | work per completed job |
|---|---:|---:|
| full test module | `q` modules | `tau=w/a` |
| known class `p_i` outside `L` | `qD_i` jobs | `p_i` |
| blind module | `1-q` jobs | `mu` |

The relaxation looks potentially stronger, but its greedy solution is
feasible in the original fluid problem at every work budget.  While the
greedy solution is partway through the test-module item, run exactly the same
fraction of the `q` tests and process its selected low outcomes.  It uses no
residual tested class yet.  Once all `q` test modules have run, every residual
capacity `qD_i` is genuinely available, and the remaining fractional items
can be processed in greedy order.  A final partially used item is implemented
by the corresponding fraction of its mass.  Thus the relaxed knapsack and
the original fluid envelope agree pointwise, not only at the terminal time.

When `tau<mu`, every excluded known class has `p_i>=tau`.  Fractional-knapsack
greedy therefore orders the item types by increasing work per completion:

```text
test modules of cost tau
-> excluded known classes with p_i<mu, in increasing p_i
-> blind jobs of cost mu
-> excluded known classes with p_i>mu, in increasing p_i.             (19)
```

This is exactly the four-block policy.  It traces `H_q(x)` pointwise, not
merely at the final time.  Hence (17) is tight, and its area is precisely the
quantity `F_D(q)` computed in Section 9.  We have proved:

**Lemma 3 (fixed-q envelope).** Every fluid policy that tests total mass `q`
has cost at least `F_D(q)`, and the four-block policy attains equality.

Notice what made the proof global: it compared complete-mass envelopes, not
adjacent actions in an adaptive decision tree.

If `tau>=mu`, the blind item has at least the density of the best possible
test module.  Every class excluded from that module also has `p_i>=tau>=mu`.
Thus the all-blind envelope pointwise dominates every solution with `q>0`;
choosing `q=0` gives cost `mu/2`.

### 8.4 Predictable sampling without replacement

We next justify that an adaptive urn policy obeys the fluid constraints up to
`o(n)` jobs.  Reveal a value whenever the policy first touches an unknown
label, whether by testing or blind execution.  Conditional on the history,
the next value is uniform in the remaining announced urn.  The policy chooses
`test` or `blind` before seeing that value.

**Lemma 3.1 (predictable urn discrepancy, finite support).** Fix `delta>0` and
stop when `delta n` labels remain untouched.  Uniformly over every
nonanticipating policy, with probability `1-o(1)`, simultaneously for every
earlier touch prefix and every support class,

```text
tested_count_i = D_i * number_of_tests
                 + O_delta(sqrt(n log n)),             (20)

blind_work = mu * number_of_blind_jobs
             + O_delta(Pmax sqrt(n log n)).            (21)
```

Here and below the converging empirical frequencies of `M_n` may replace
`D_i`, changing the right side by `o(n)`.

Here is one quantitative version.  Put

```text
e_n     = sqrt(8 n log n),
Gamma_n = (1+1/delta)e_n.
```

Use the exact empirical frequencies `D_{n,i}` in this paragraph.  For each
fixed touch prefix, Hoeffding's inequality for sampling without replacement
controls both every class count and the sum of the touched processing times.
A union bound over at most `n` prefixes and the fixed support gives, except
with probability `O_s(n^{-3})`,

```text
max_k |prefix_count_i(k)-kD_{n,i}| <= e_n,
max_k |prefix_work(k)-k mu_n|      <= Pmax e_n.         (20a)
```

If `R_{k,i}` is the fraction of class `i` left after `k` touches, then for
`k<=(1-delta)n`,

```text
|R_{k,i}-D_{n,i}| <= e_n/(delta n).                    (20b)
```

The analogous bound on the mean of the remaining urn is
`Pmax e_n/(delta n)`.

Now let `A_k` be the predictable indicator that touch `k` is a test.  Then

```text
sum_{k<=m} A_k
  (1{X_k=p_i} - R_{k-1,i})
```

is a martingale with increments bounded by one.  Maximal Azuma--Hoeffding
puts its absolute running maximum below `e_n` except with probability
`2n^{-4}`.  Combining this with (20b) yields, simultaneously for every
`m<=(1-delta)n`,

```text
|tested_count_i(m)-D_{n,i} tests(m)| <= Gamma_n.        (20c)
```

Apply the same argument to the martingale differences

```text
(1-A_k)(X_k-E[X_k | history before touch k]),
```

whose absolute values are bounded by `Pmax`, and combine it with the remaining
urn mean bound following (20b).  This gives

```text
|blind_work(m)-mu_n blind_count(m)| <= Pmax Gamma_n.    (21a)
```

Equations (20c)--(21a) imply (20)--(21), since
`Gamma_n=O_delta(sqrt(n log n))`.  This proof is uniform in the policy: only
predictability of `A_k`, not the rule producing it, was used.  The constants
deteriorate as `delta->0`, which is why the last `delta n` labels are handled
separately. `QED`

### 8.5 Lower bound for every adaptive policy

Condition first on the policy's private random seed.  Let `Q_{n,delta}` be
the fraction tested when only `delta n` labels remain untouched.  On a fixed
realized schedule, replace the test-and-later-process pair of each of those
last labels by one blind execution, while preserving the relative order of
all other operations.  This edits or moves at most `2 delta n` bounded
operations.  Moving one bounded operation across the rest of a schedule
changes total completion cost by `O((Pmax+1)n)`.  Thus the edited schedule,
in which the last labels are declared blind, differs in cost by at most

```text
O((Pmax+1) delta n^2).                                 (22)
```

On the event (20)--(21), normalize all counts and physical work by `n`.
Before the edit point, the resulting point satisfies (13)--(15) with additive

```text
epsilon_n(delta)=O_delta(sqrt(log n/n))+o(1)            (23)
```

slack.  After the edit point, the uncontrolled last `delta n` blind values
add at most `O(Pmax delta)` further slack, uniformly over all later prefixes.

Here is an explicit perturbation argument.  If
`c_i<=D_i t+epsilon`, replace `c_i` by
`c_i'=max(c_i-epsilon,0)`.  This restores every revelation constraint and
loses at most `s epsilon` completed mass.  Equation (21) says that the ideal
fluid work of the repaired point is at most `epsilon` larger than its actual
work.  Finally, `H_q` is piecewise linear and its largest slope is at most

```text
R_D = max{rho, 1/mu, 1/p_1}.
```

Therefore the completed fraction at every normalized work time `x` is at
most

```text
H_{Q_{n,delta}}(x)
  + O_D(epsilon_n(delta)+delta).                        (24)
```

Integrating the remaining-mass curve over a horizon of length at most
`Pmax+1`, using Lemma 3 and then restoring the suffix (22), gives

```text
cost/n^2
 >= F_D(Q_{n,delta})
    - O_D(epsilon_n(delta)+delta).                       (25)
```

The exceptional event contributes `o(1)` because every schedule costs at
most `(Pmax+1)n^2`.  Averaging over both the urn permutation and the private
seed therefore yields

```text
E[cost]/n^2
 >= E[F_D(Q_{n,delta})] - o_n(1) - O_D(delta)
 >= min_q F_D(q)       - o_n(1) - O_D(delta).           (26)
```

First let `n->infinity` and then `delta->0`.  This is the required lower
bound, including fully adaptive stopping rules.

The minimax announced-label model equals the random-urn model used above.
To see this explicitly, let `U(M_n)` be the minimum expected cost of a
deterministic policy under a uniformly random labeling.  The uniform labeling
is a valid Yao distribution, so

```text
VAL(M_n) >= U(M_n).                                    (26a)
```

Conversely, take an urn-optimal deterministic policy and first apply an
independent uniform random permutation to the physical labels.  Against every
fixed oblivious assignment, the induced assignment seen by the policy is
uniform, and hence this symmetrized policy has expected cost exactly
`U(M_n)`.  Therefore

```text
VAL(M_n) <= U(M_n).                                    (26b)
```

Thus equality holds, and (26) is a lower bound on `VAL(M_n)`, not only on one
chosen random assignment.

### 8.6 Matching policy and scope

Choose `q*` minimizing `F_D`, test `q*n+O(1)` uniformly random labels, process
the selected low outcomes between tests, and then execute the medium / blind /
high blocks in order (19).  The same concentration argument, or direct
hypergeometric moment calculations, gives

```text
E[cost]/n^2 = F_D(q*)+o(1).                             (27)
```

Equations (26)--(27) prove Theorem 3.  Sequential single-job execution is an
`o(n^2)` implementation of the fluid test module; equivalently one may use
microbatches of size `h_n->infinity`, `h_n=o(n)`, and SPT the low outcomes
inside each batch.

The implementation error can in fact be made uniform without a concentration
argument.

**Lemma 3.2 (finite kernel expansion).** For any fixed canonical grid template
`pi`, any empirical distribution `D_n` on `[0,L]`, and any tested count
`r in {0,...,n}`, put `q=r/n`.  Then, uniformly in `pi,r,D_n`,

```text
E[cost_n(pi)] = n^2 Psi_{D_n}(pi) + O_L(n).             (27a)
```

**Proof.** Fix the multiset occurrences and expose only the independent
uniform permutation used by the template.  Pairwise delay accounting writes
the completion objective as a sum of one-occurrence terms and ordered
two-distinct-occurrence terms.  Every kernel is bounded by `1+L`: it records
either one test, one processing operation, or the delay that one such
operation imposes on another occurrence.

The only probabilities multiplying the two-occurrence kernels are generated
by membership in the tested set, membership in its complement, and relative
order inside one of the random blocks.  For two distinct labels they are

```text
Pr(i,j tested)       = r(r-1)/(n(n-1)),
Pr(i tested,j blind) = r(n-r)/(n(n-1)),
Pr(i,j blind)        = (n-r)(n-r-1)/(n(n-1)),
Pr(i before j | same random block) = 1/2.             (27b)
```

The corresponding fluid coefficients are `q^2`, `q(1-q)`, `(1-q)^2`, and
`1/2`.  Each finite coefficient in (27b) differs from its fluid counterpart
by at most `2/(n-1)`, uniformly in `r`.  The low/medium/high class indicators
and any boundary mixing probabilities merely multiply these kernels by
numbers in `[0,1]`.

There are fewer than `n^2` ordered distinct pairs, so replacing all finite
coefficients by their fluid values changes their total by `O_L(n)`.  The
one-occurrence terms, including the diagonal pieces suppressed by the
two-distinct-job formula and the rounding of `qn` to `r`, contribute another
`O_L(n)`.  After the replacement, grouping pair kernels by the four blocks
gives exactly the five terms in (28), i.e. `n^2 Psi_{D_n}(pi)`.  This proves
(27a). `QED`

This lemma is useful below when `pi` itself is chosen from a preliminary
sample: conditional on that sample, apply (27a) to a fresh random permutation
of the remaining jobs.

Atoms at `tau` are split by an independent coin with the maximizing fraction
from (10), and atoms at `mu` may be placed on either side of the blind block.
This changes neither the envelope nor its area.  For general bounded
distributions, discretization into bins gives the same conclusion after
standard quantile-coupling bookkeeping; the theorem above deliberately keeps
finite support so that the new structural argument is visible without
measure-theoretic notation.

## 9. The remaining one-dimensional optimization

For clarity, first assume there are no atoms at `tau` or `mu`; the virtual
class convention from Section 8 gives the identical formula with ties.
Let the three regions be

```text
L = {p < tau},
M = {tau < p < mu},
H = {p > mu}.
```

Define

```text
a   = Pr[P in L],
l   = E[P 1{P in L}],
c   = Pr[P in M],
m   = E[P 1{P in M}],
d   = Pr[P in H],
K_M = E[min(P,Q) 1{P,Q in M}],
K_H = E[min(P,Q) 1{P,Q in H}],
```

for independent `P,Q ~ D`.  Test a deterministic fraction `q` and apply the
canonical ordering.  With `r=1-q`, direct remaining-mass accounting gives

```text
F_D(q)
  = (1+l)(q-aq^2/2)                  test plus immediate low jobs
    + q m (r+qd) + q^2 K_M/2         known medium prefix
    + mu (rqd+r^2/2)                 YOLO block
  + q^2 K_H/2.                     known high tail                (28)
```

For completeness, each summand follows from one application of the area
identity.  During `dq` units of test mass, the full test module uses work
`(1+l)dq` and the unfinished mass falls linearly from `1` to `1-aq`; its area
is `(1+l)(q-aq^2/2)`.  After testing, the medium stock has mass `qc` and total
work `qm`.  Every unit of medium work delays all `r` untouched jobs and the
`qd` high jobs, giving `qm(r+qd)`, while SPT interactions internal to the
medium stock contribute `q^2K_M/2`.  During the blind block, high mass `qd`
remains throughout and blind mass decreases linearly from `r` to zero, giving
`mu(rqd+r^2/2)`.  Finally, SPT interactions internal to the high stock give
`q^2K_H/2`.  These blocks partition all unfinished-mass area, so no cross term
is omitted.

Every term is at most quadratic in `q`.  Expanding (28) gives the more useful
normal form

```text
F_D(q) = mu/2 + A_D q + B_D q^2,                       (29)

A_D = 1 - E[(mu-P)^+],

B_D = -(1+l)a/2 + m(d-1) + K_M/2
      + mu(1/2-d) + K_H/2.                            (29a)
```

To check the linear coefficient, differentiate the five terms of (28) at
`q=0`:

```text
F_D'(0)=1+l+m+mu(d-1)
       =1-[mu(a+c)-(l+m)]
       =1-E[(mu-P)^+].
```

The quadratic coefficient is nonnegative.  Indeed, for fixed work budget
`x`, the LP value `H_q(x)` is concave in `q`: a convex combination of a point
feasible for `q_1` and a point feasible for `q_2` satisfies all affine
capacity constraints for the same convex combination of `q_1,q_2`.
Therefore

```text
F_D(q)=integral (1-H_q(x)) dx
```

is convex, and since it is quadratic, `B_D>=0`.

In the testing regime `tau<mu`,

```text
E[(mu-P)^+] > E[(tau-P)^+] = 1,
```

so `A_D<0`; in particular `q=0` is never optimal.  The optimizer is explicit:

```text
q* = 1,                                  if B_D=0,
q* = min{1, -A_D/(2B_D)},                if B_D>0.     (29b)
```

In the non-testing regime the envelope argument gives `q*=0` directly.

For an adaptive finite policy, the stopping time may depend on the realized
tested stock.  Under concentration, the normalized stock follows its
deterministic fluid trajectory; adaptivity improves (28) by at most `o(n^2)`.

Equation (28) also explains why a genuine interior `q*` is possible.  The test
prefix has high initial information value, but accumulating deferred jobs and
shrinking the unknown pool make the marginal value of later tests smaller.

## 10. A three-point example showing the medium prefix matters

Let

```text
Pr[P=0]  = 1/5,
Pr[P=9]  = 1/5,
Pr[P=16] = 3/5.
```

Then

```text
mu = 57/5 = 11.4,
tau = 5,
```

because `E[(5-P)^+]=(1/5)5=1`.  Hence zero jobs are immediate,
known nine-jobs belong before YOLO, and known sixteen-jobs belong after YOLO.
Formula (28) becomes

```text
F_D(q) = 57/10 - (44/25)q + (11/10)q^2.
```

Its minimizer is

```text
q* = 4/5,
```

with value `4.996`.  If all tested nonzero jobs are incorrectly placed after
YOLO, the best simpler one-threshold policy has value `5.04`.  The gap is a
positive constant times `n^2`, so the known medium prefix is structurally
necessary.

## 11. Relation to the literature

The relevant published source is:

* Retsef Levi, Thomas Magnanti, Yaron Shaposhnik, *Scheduling with Testing*,
  Management Science 65(2), 2019, 776--793,
  https://doi.org/10.1287/mnsc.2017.2973

The accessible precursor gives fully checkable numbering:

* Yaron Shaposhnik, *Exploration vs. Exploitation: Reducing Uncertainty in
  Operational Problems*, MIT PhD thesis, 2016, Chapter 2,
  https://dspace.mit.edu/handle/1721.1/106681

The precise assumptions in thesis Section 2.2 are: one nonpreemptive server;
`N_0` jobs whose processing-time/weight pairs `(T,W)` are independent and
identically distributed from a known joint distribution supported on
`[1,D] x [1,V]`; a deterministic test time `t_a`; optional testing that
reveals both coordinates; and objective `E[sum_i W_i C_i]`.  An untested job
may instead be processed blindly.

In this notation, Lemma 2.3.3 says that a known low-ratio job is processed
immediately, Lemma 2.3.4 rules out a test immediately after a job whose ratio
exceeds the testing ratio, Theorem 2.3.5 gives the test-or-stop normal form
when `rho_a<rho`, and Theorem 2.3.6 says that testing is never optimal when
`rho<rho_a`.  These are Bellman/DP statements about the full adaptive policy,
which is exactly the step not supplied by our local equations (2)--(4).

Their general model uses Smith ratios `p/w`.  Their testing ratio `rho_a`
solves

```text
test_time = E[(rho_a W - P)^+].
```

For unit weights and unit test time this is exactly equation (T).  The
theorem's second phase processes all pending objects by expected Smith ratio.  Unknown
jobs have ratio `E[P]`, which produces exactly the known-medium / YOLO /
known-high order above.

There is one assumption mismatch that must remain explicit.  The verified
thesis statement assumes processing times at least one, whereas our optional
model permits `P=0` and declares a tested zero complete at its test.  The
unit-weight positive-processing-time case is a literal specialization; the
zero-atom case requires either a continuity argument from `P+epsilon` with
careful completion semantics, or a direct Bellman proof.  The fluid envelope
in Section 8 handles zero directly and does not rely on this literature
specialization.  We therefore do not cite unverified theorem numbers from the
typeset Management Science version.

The adversarial processing-time-oracle paper later conjectured an analogous
two-phase structure for its deterministic adversarial binary game.  That is a
different statement: the stochastic theorem relies on exchangeability and,
for the exact i.i.d. version, independence.  Our oblivious announced-multiset
fluid limit sits much closer to the stochastic theorem.

## 12. Uniform transfer to arbitrary bounded announced multisets

Section 8 fixed a finite support while `n` grew.  An oblivious adversary need
not respect such a support: all `n` processing times may be distinct and may
change with `n`.  We now remove that restriction with a grid whose mesh tends
to zero slowly enough that concentration remains uniform over its bins.

### 12.1 The distributional benchmark

For any probability distribution `D` on `[0,L]`, define the best discovery
density by

```text
rho(D) = sup_{measurable 0<=g<=1}
         E[g(P)] / (1+E[P g(P)]),

tau(D) = 1/rho(D).                                    (30)
```

The maximizer is a threshold: `g(p)=1` below `tau`, `g(p)=0` above `tau`,
with possible mixing at the boundary.  For a fixed tested fraction `q`, let
`F_D(q)` be the area under the remaining-mass curve obtained by ordering

```text
test module of cost tau(D)
-> tested residual outcomes p<mu(D)
-> blind mass of cost mu(D)
-> tested residual outcomes p>mu(D).                  (31)
```

Equivalently, `F_D(q)=integral (1-H_{D,q}(x)) dx`, where `H` is the
completion envelope (16), interpreted with measures.  Put

```text
Phi(D) = min_{0<=q<=1} F_D(q).                         (32)
```

If `tau(D)>=mu(D)`, this definition chooses `q=0` and `Phi(D)=mu(D)/2`.
For a finite multiset `M`, write `D_M` for its empirical distribution.

### 12.2 Rounding stability

**Lemma 4 (processing-time perturbation).** Suppose `P~D` and `P'~D'` admit
a coupling with `|P-P'|<=h` almost surely, with zero values coupled to zero
values and positive values coupled to positive values.  Then

```text
|Phi(D)-Phi(D')| <= h.                                (33)
```

The same statement holds for the cost of any fixed fluid action template.

**Proof.** Couple every infinitesimal job occurrence.  Run the same tests,
the same immediate/deferred decisions, and the same completion order in both
instances.  Test work and the completed mass after each corresponding action
are identical.  The total absolute change in processing work over unit job
mass is at most `h`.  Since the unfinished mass is always between zero and
one, inserting or deleting that work changes the area under the unfinished-
mass curve by at most `h`.  Apply the comparison in both directions and then
take the infimum over policies.  If several original values collapse to one
grid atom, subtype-dependent decisions are implemented in the collapsed
instance by mixing the corresponding fractions of that atom.  All collapsed
subtypes have the same grid duration, so their identities carry no additional
scheduling value. `QED`

At finite `n`, the identical argument says that changing every processing
time by at most `h` changes the cost of a fixed operation word by at most
`hn^2`: each total unit of changed work delays at most `n` completions.

### 12.3 A growing grid

Fix the following concrete parameters (many slower choices work):

```text
K_n     = floor(n^(1/6)),
h_n     = L/K_n,
delta_n = n^(-1/6).                                   (34)
```

Keep zero as a separate atom and partition `(0,L]` into `K_n` bins.  Round
every positive processing time to the upper endpoint of its bin and let
`D_n^grid` be the resulting empirical distribution.  Thus no positive job is
turned into a job that completes at the end of its test.  Lemma 4 gives

```text
|Phi(D_M)-Phi(D_n^grid)| <= h_n.                       (35)
```

Run the lower-bound argument of Sections 8.4--8.5 on **bin counts** rather
than exact processing-time classes.  With

```text
e_n = sqrt(8n log(nK_n)),
Gamma_n = (1+1/delta_n)e_n,
```

every bin's adaptively tested count has error at most `Gamma_n`, and the
blind grid-work error is at most `L Gamma_n`, until only `delta_n n` labels
remain.

**Lemma 6 (finite prefix-to-grid envelope).** Let `q` be the final tested
fraction after declaring the last `delta_n n` touched labels blind.  On the
simultaneous discrepancy event, at every normalized physical time `x`,

```text
completed_fraction(x)
 <= H^grid_q(x+zeta_n) + zeta_n,                       (36)
```

where

```text
zeta_n = O_L(
    (K_n+1) Gamma_n/n   bin-count repair
  + h_n                 rounding work
  + delta_n             uncontrolled final urn
).                                                               (37)
```

**Proof.** First take a prefix before the final uncontrolled urn.  Let `t`
be its number of tests divided by `n`, `b` its number of blind completions
divided by `n`, and `c_i` the mass of already processed tested jobs in
positive grid bin `i`.  Let `z_0` be its tested-zero completion mass.  By
definition of the edited final tested fraction,

```text
0<=t<=q,                 0<=b<=1-q.
```

The simultaneous predictable-count bounds give

```text
z_0 <= D^grid_0 t + Gamma_n/n,
c_i <= D^grid_i t + Gamma_n/n.                         (36a)
```

Set `c_i'=(c_i-Gamma_n/n)_+`.  Then
`c_i'<=D^grid_i t`, and repairing all `K_n` positive-bin constraints plus
the separate zero estimate loses at most `(K_n+1)Gamma_n/n` completed mass.
Thus the repaired completion amount is feasible for the mass constraints in
the LP defining `H^grid_q`.

For work, apply the predictable martingale estimate to the **rounded grid
values** of blind jobs.  Their ideal work `mu_grid b` exceeds their actual
rounded sum by at most `L Gamma_n/n`.  Replacing every actual positive length
by its upper grid endpoint changes the total processing work of all completed
known and blind jobs by at most `h_n`, because total job mass is at most one.
Repairing `c_i` only decreases work.  Consequently the repaired LP point uses
at most

```text
x + h_n + L Gamma_n/n
```

work.  This proves (36) before the cutoff, with the first two error terms in
(37); the bin-count term dominates the single blind-work term.

For a prefix entering the final `delta_n n` labels, remove those suffix
actions temporarily.  They can add at most `delta_n` completed mass and at
most `L delta_n` processing work.  Apply the preceding bound to the remaining
prefix, then restore this vertical and horizontal slack.  Monotonicity of
`H^grid_q` gives (36)--(37), after enlarging a constant depending only on
`L`.  This argument explicitly includes the zero bin, blind-work error, and
the last uncontrolled labels. `QED`

There is no need for a lower bound on the smallest positive processing time.

To integrate (36), shift the envelope horizontally instead of bounding its
slope:

```text
integral_0^T (1-H^grid_q(x+zeta_n)) dx
 >= integral_0^T (1-H^grid_q(x)) dx - zeta_n.          (38)
```

This uses only `0<=1-H<=1`, so the estimate stays uniform even if a bin lies
arbitrarily close to zero.  More explicitly, the rounded total work exceeds
the actual total work by at most `h_n`; since `h_n` is included in `zeta_n`,
the shifted interval `[zeta_n,T_actual+zeta_n]` reaches the end of the grid
envelope.  It misses at most the first `zeta_n` units of its area.  The
vertical `zeta_n` slack in (36) contributes at most
`(L+1)zeta_n`, because the normalized horizon is at most `L+1+o(1)`.
The parameter choice (34) gives

```text
(K_n+1) Gamma_n/n
 = O(n^(-1/6) sqrt(log n)),

zeta_n = o(1).                                         (39)
```

The floors in (34) do not hide another asymptotic assumption.  Once
`n^(1/6)>=2`,

```text
n^(1/6)/2 <= K_n <= n^(1/6),
h_n <= 2L n^(-1/6),
e_n <= 4 sqrt(n log n),
Gamma_n <= 8 n^(2/3) sqrt(log n),
(K_n+1) Gamma_n/n <= 16 n^(-1/6) sqrt(log n).          (39a)
```

Here `log(nK_n)<=2log n` and
`1+1/delta_n=1+n^(1/6)<=2n^(1/6)`.  These inequalities also show directly
that all constants in (36)--(41) depend only on `L`, uniformly over the
empirical multiset.

On the upper side, run the canonical policy computed from `D_n^grid` and round
every observed time upward internally.  Actual processing operations are no
longer than their simulated grid operations.  The pair-accounting estimate
(27a) gives simulated cost `n^2 Phi(D_n^grid)+O_L(n)`, uniformly in the grid
and the chosen template.  Combining this with (35)--(39) proves the uniform
statement below.

**Candidate Theorem 4 (arbitrary bounded announced multiset).** For every fixed
`L<infinity` there is a deterministic sequence `r_L(n)->0` such that every
announced multiset `M subseteq [0,L]` of size `n` satisfies

```text
| VAL_ann(M)/n^2 - Phi(D_M) | <= r_L(n).               (40)
```

One may take, up to constants depending only on `L`,

```text
r_L(n) = O_L(n^(-1/6)sqrt(log n)).                     (41)
```

Thus no convergence assumption on the empirical distributions is needed.
For each individual bounded multiset, an asymptotically optimal announced
policy has the four-block form (31), up to the vanishing grid width and
`o(n)` boundary jobs.

## 13. Removing the announcement by sublinear sampling

We now construct one policy which is not told `M`.  The adversary fixes an
arbitrary vector in `[0,L]^n` before the random seed is drawn.  The policy
knows only `n`, `L`, and the unit test time.

### 13.1 The universal policy

Choose

```text
k_n = ceil(n^(1/2))                                   (42)
```

and use the grid from (34).  The policy is:

1. Draw a uniform random permutation of the labels.
2. Run its first `k_n` labels blindly.  These pilot jobs are completed while
   revealing their processing times, so there are no pending pilot jobs.
3. Let `Dhat_n` be the empirical grid histogram of this sample, rounding
   processing times upward.
4. On the grid, enumerate the canonical policy parameters: the immediate
   prefix, the insertion position of the blind block among known SPT classes,
   and `q in [0,1]`.  For each discrete pair the objective is quadratic in
   `q`, so its minimum is explicit.  Choose a minimizer for `Dhat_n`.
5. Run that policy on the remaining labels in fresh random order: test the
   selected fraction, immediately execute selected low outcomes, then run
   the known-medium / blind / known-high blocks.

The blind pilot has total work at most `Lk_n` while at most `n` jobs are
unfinished.  Moving these `k_n` jobs from their positions in an ideal
canonical schedule to the front changes at most `nk_n` bounded pair delays.
Hence the total price of sampling is

```text
O_L(nk_n)=O_L(n^(3/2))=o(n^2).                         (43)
```

### 13.2 Histogram estimation

Let `D_n` be the full grid histogram, `Dhat_n` the sample histogram, and
`D_n^R` the histogram of the remaining `n-k_n` jobs.  Sampling without
replacement only reduces coordinate variances, so

```text
E[||Dhat_n-D_n||_1]
 <= sum_j sqrt(D_{n,j}/k_n)
 <= sqrt((K_n+1)/k_n).                                 (44)
```

The `+1` is the separate zero atom.  For all sufficiently large `n`,

```text
n^(1/2) <= k_n <= 2n^(1/2),
n-k_n >= n/2,
K_n+1 <= 2n^(1/6),
sqrt((K_n+1)/k_n) <= sqrt(2)n^(-1/6).                 (44a)
```

The identity

```text
D_n = (k_n/n) Dhat_n + ((n-k_n)/n) D_n^R              (45)
```

also gives

```text
||D_n^R-D_n||_1 <= 2k_n/n,

E[||Dhat_n-D_n^R||_1]
 <= (n/(n-k_n)) sqrt((K_n+1)/k_n).                     (46)
```

### 13.3 Robust empirical optimization

Let `Pi_K` be the finite family of grid policy templates described in Step 4,
with the continuous parameter `q`.  For `pi in Pi_K`, let `Psi_D(pi)` be its
normalized fluid cost under histogram `D`.

**Lemma 5 (histogram Lipschitz bound).** Uniformly over `K`, `pi`, and
distributions `D,E` on the grid,

```text
|Psi_D(pi)-Psi_E(pi)|
 <= C_L ||D-E||_1,                                    (47)
```

for a constant depending only on `L`.  Consequently the same bound holds for
`min_pi Psi_D(pi)`.

**Proof.** Fix the template, including any fractional choices at boundary
atoms.  Its three class indicators are now fixed functions with values in
`[0,1]`; they do not change when `D` is replaced by `E`.  Formula (28) remains
valid with

```text
a_D = E_D[1_L],       l_D = E_D[P 1_L],
m_D = E_D[P 1_M],     d_D = E_D[1_H],
mu_D = E_D[P],
K_{M,D} = E_{D x D}[min(P,Q)1_M(P)1_M(Q)],
K_{H,D} = E_{D x D}[min(P,Q)1_H(P)1_H(Q)].
```

Write `Delta=||D-E||_1`.  The one-draw terms satisfy

```text
|a_D-a_E|, |d_D-d_E| <= Delta,
|l_D-l_E|, |m_D-m_E|, |mu_D-mu_E| <= L Delta.          (47a)
```

For a two-draw kernel `g` bounded by `L`, insert the intermediate product
measure `E x D`:

```text
|E_{D x D}g-E_{E x E}g|
 <= |E_{D x D}g-E_{E x D}g|
      +|E_{E x D}g-E_{E x E}g|
 <= 2L Delta.                                         (47b)
```

All coefficients `q,r,a,d` lie in `[0,1]`.  Apply (47a)--(47b) to the five
summands of (28), using `|uv-u'v'|<=|u-u'||v|+|u'||v-v'|` for the two products.
The first summand costs at most
`[L+(1+L)/2]Delta`, the medium cross term at most `2LDelta`,
the medium pair term at most `LDelta`, the blind term at most
`(5L/2)Delta`, and the high pair term at most `LDelta`.  Their sum is below
`20(L+1)Delta`, proving (47) with the advertised constant, independently of
the number of grid cells.

Finally, if `pi_D` minimizes `Psi_D`, then

```text
min_pi Psi_E(pi) <= Psi_E(pi_D)
                  <= Psi_D(pi_D)+C_L Delta
                  = min_pi Psi_D(pi)+C_L Delta.
```

Swap `D,E` for the reverse inequality. `QED`

Let `pihat` minimize `Psi_{Dhat_n}` and let `pi_R` minimize
`Psi_{D_n^R}`.  The standard empirical-optimization sandwich gives

```text
Psi_{D_n^R}(pihat)
 <= Psi_{Dhat_n}(pihat)
      + C_L ||Dhat_n-D_n^R||_1
 <= Psi_{Dhat_n}(pi_R)
      + C_L ||Dhat_n-D_n^R||_1
 <= Phi(D_n^R)
      + 2C_L ||Dhat_n-D_n^R||_1.                       (48)
```

For a grid distribution, the fixed-`q` envelope theorem says that the
grid-template minimum is exactly `Phi`.  Equations (44)--(48), together with
the conditional finite implementation estimate (27a), give for
`N=n-k_n`

```text
E[main cost | sample]
 <= N^2 (Phi(D_n^R)
          +2C_L ||Dhat_n-D_n^R||_1) + O_L(N).          (48a)
```

Lemma 5 and (46) imply
`|Phi(D_n^R)-Phi(D_n)|<=2C_Lk_n/n`; replacing `N^2` by `n^2` only increases
this nonnegative upper bound.  After taking expectations, adding the sample
overhead (43), and using the rounding bound (35), the full schedule has
expected normalized cost at most

```text
Phi(D_M)
 + O_L(h_n
       + sqrt((K_n+1)/k_n)
       + k_n/n
       + zeta_n).                                      (49)
```

For the choices (34) and (42), every error tends to zero; in particular
`sqrt((K_n+1)/k_n)=O(n^(-1/6))`.

### 13.4 Final oblivious-adversary theorem

**Candidate Theorem 5 (unknown multiset, oblivious adversary).** Fix `L<infinity`.
There exists a single randomized nonclairvoyant policy `A*`, not given the
multiset of processing times, and a sequence `eps_L(n)->0`, such that for
every size-`n` multiset `M subseteq [0,L]` and every fixed labeling `sigma`,

```text
E[cost(A*,sigma(M))]
 <= n^2 Phi(D_M) + eps_L(n)n^2.                        (50)
```

Conversely, for every randomized policy `A` and every multiset `M`, some
oblivious fixed labeling `sigma` satisfies

```text
E[cost(A,sigma(M))]
 >= n^2 Phi(D_M) - eps_L(n)n^2.                        (51)
```

**Proof.** The upper bound is the sampled policy of Section 13.1.  Its initial
random permutation makes its distribution identical under every fixed
labeling, and (43) and (49) prove (50).  For the lower bound, reveal `M` to the
policy for free.  This can only help.  The uniform distribution over the fixed
labelings of `M` is an oblivious Yao distribution, and Theorem 4 lower-bounds
its optimal announced cost by the right side of (51).  Some labeling in the
support of that distribution attains at least its average. `QED`

With the concrete choices (34) and (42), the same sequence can be used in
both directions and, after enlarging a constant depending only on `L`, one
may take

```text
eps_L(n) <= C_L n^(-1/6) sqrt(log n).              (53)
```

The grid rounding, unregulated final urn, predictable bin-count repair,
histogram estimation, and blind-pilot overhead are all covered by this rate.
Floors and ceilings only alter `C_L`.  In particular the theorem
has a completely uniform error sequence; the `o(n^2)` does not depend on the
multiset or its labelling.

Consequently, up to additive `o(n^2)`, the optimal policy against an oblivious
adversary really has the promised form:

```text
o(n)-sample
-> threshold testing prefix
-> tested jobs between tau and mu in SPT order
-> YOLO block
-> tested jobs above mu in SPT order.                  (52)
```

The stopping fraction is the minimizer of the one-dimensional quadratic
`F_D(q)`, estimated from the sample.  Neither an adaptive stopping rule nor a
nonmonotone sequence of finite Bellman thresholds improves the leading
`n^2` coefficient.

## 14. Scope and remaining formalization work

The proved analytic core is the fixed-`q` completion envelope and its
four-block optimizer.  The finite-support predictable-urn concentration now
also has a checked finite-permutation Lean proof, using an `L^2` checkpoint
argument instead of the draft's exponential Azuma bound.  The
arbitrary-support and unknown-multiset statements remain candidate theorems:
the analytic revision supplies expanded proofs of the two previously missing
technical lemmas (27a) and (36), including the zero bin, blind-work error, and
uncontrolled suffix, but the complete operational assembly has not yet been
formalized or independently audited line by line.

The draft also includes floor/ceiling arithmetic, an explicit histogram
Lipschitz bound, the improved parameter rate (53), and a blind pilot.  The
intended
formalization order is: deterministic envelope/fractional-knapsack Lemma 3;
finite predictable urn discrepancy; growing-grid perturbation; empirical
optimization; and finally the minimax/Yao wrapper.  No Lean theorem for this
full optional-testing result is claimed by this document yet.

The deterministic and empirical layers are now substantially checked in
Lean. `SchedulingPaper/RandomizedOptionalFluid.lean` proves the exact
fractional full-module replacement `lambda=y/a`, the pointwise
fractional-knapsack envelope certificate, the long-test area lower bound, the
classwise revelation repair and its pointwise completion consequence, and
the horizontal/vertical integral-shift estimate.  It also checks the
five-term cost formula (28), its quadratic normal form and minimizers, and the
three-point witness with `q*=4/5` and value `4.996`.

`SchedulingPaper/RandomizedOptionalGridBridge.lean` proves the strengthened
all-class form of (36) used by finite urn prefixes.  It repairs every positive
class, charges one additional allowance for the separate zero class, derives
the selected-low module's density from the maximum-density inequality, and
then applies the pointwise fractional-knapsack envelope.  Thus the low part
is no longer assumed to satisfy an exact revelation constraint before the
repair.

`SchedulingPaper/RandomizedOptionalKernel.lean` proves the finite one-job and
two-distinct-job kernel estimates, a `12(L+1)` fixed-template histogram
Lipschitz bound, and the empirical-minimizer sandwich;
`SchedulingPaper/RandomizedOptionalFiniteKernel.lean` proves the full generic
finite operation-word form of (27a): arbitrary position-dependent bounded
one-job and ordered two-job kernels differ from their empirical-product fluid
replacement by `O_L(n)`, with a normalized bound independent of the grid and
template;
`SchedulingPaper/RandomizedOptionalLearning.lean` combines these with finite
histogram concentration. `SchedulingPaper/RandomizedOptionalUrn.lean`
formalizes the pathwise predictable-selection decomposition and remaining-urn
drift calculation. `SchedulingPaper/RandomizedOptionalPermutationUrn.lean`
proves the random-permutation concentration layer without a measure-theoretic
filtration: suffix-symmetry, orthogonality of arbitrary predictable
increments, finite `L^2`/Chebyshev bounds, checkpoint interpolation, and the
resulting policy-uniform count and bounded-work estimates.
`SchedulingPaper/RandomizedOptionalRates.lean` supplies a fully concrete
finite instantiation: for `n=R^8`, selected-count deviation is at most
`4R^7`, and selected processing work in `[0,L]` deviates by at most `4LR^7`,
outside an event of probability at most `5/R` for each scalar estimate.  The
same file now proves the required grid union explicitly: with at most `S`
positive cells and `S^2<=R`, the joint count/work bad event is at most `10/S`
and the normalized all-class repair loss is at most `8/S`.  Thus the checked
`L^2` route supports a slower but still vanishing grid (for example
`S=floor(sqrt R)`); it does not by itself justify the sharper grid/rate in
(52), which uses the exponential Azuma estimate in the analytic proof.
`SchedulingPaper/RandomizedOptionalOperational.lean` formalizes the correct
optional timing in which blind execution lasts the actual hidden `p_i`, its
exact area/work identities, reachable-prefix truthfulness and lifecycle
invariants, the classwise revelation inequality, and cost-preserving private
relabeling. `SchedulingPaper/RandomizedOptionalStrategy.lean` defines the
literal test/immediate-low/known-medium/blind/known-high transcript policy.

There is an information distinction that the first operational file alone
does not express: after a blind nonpreemptive execution, the algorithm observes
its duration from the clock. `SchedulingPaper/RandomizedOptionalOnline.lean`
therefore defines the full optional model in which a blind-completion record
contains that realized duration; it proves the exact area identity and the
private-relabeling cost identity in this richer model, along with reachable
truthfulness/lifecycle invariants, classwise revelation, and a universal
finite settling rank.
`SchedulingPaper/RandomizedOptionalObservedStrategy.lean` defines the
canonical four-block policy there.  This richer semantics is the one used for
the arbitrary-policy announced lower bound; the older runtime is only a
restricted-policy convenience layer.

`SchedulingPaper/RandomizedOptionalTraceBijection.lean` and
`SchedulingPaper/RandomizedOptionalObservedTrace.lean` now give the simpler
global compiler.  Distinct occurrences turn a placement into a permutation;
the operational `startedLabels` list is the permutation of public labels in
first-touch order.  A lockstep theorem proves that equal exposed-value
prefixes force the same next label and `test`/`blind` action, including after
observed blind durations.  Consequently the adaptive reveal map is a
bijection of the finite placement space, uniform averages reindex exactly,
and the compiled test selector is predictable.  The selected-class and
blind-work sums are identified pathwise.  No suffix-swap composition or
conditional-probability semantics is used in this compiler.

The main missing formal layer is now the physical-operation-prefix-to-envelope
assembly after the completed adaptive-touch compiler, the specialization of
the generic finite-kernel theorem to the
concrete canonical transcript, and the final minimax/Yao plus pilot-learning
wrappers.

This theorem does **not** claim a bounded competitive ratio against the
clairvoyant SPT optimum on every instance.  Sparse instances can have
`OPT=o(n^2)`, so the allowed additive `o(n^2)` may dominate that benchmark.
The statement is instance-optimal at the `n^2` scale requested here.
