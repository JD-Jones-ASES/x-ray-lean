# Constructive families and an extension theorem for binary permutation X-rays

Private mathematical draft, 15 September 2026. The arguments below are
informal proofs assembled from the Lab notes. Formal verification is in progress; see [VERIFICATION.md](VERIFICATION.md)
for the exact completed scope. The unrestricted binary X-ray conjecture remains open.

## Abstract

The binary permutation X-ray conjecture asks whether the usual density
inequalities suffice to realize a prescribed set of distinct antidiagonal
labels by a permutation matrix. We prove this for every admissible profile
whose ith smallest label differs from 2i-1 by at most two. The construction
works at every order and allows unbounded density slack. Its main extension
step takes any permutation realizing a multiset L at order n to one
realizing {3,2n+1} union (L+2) at order n+2. We also prove two one-sided
deviation families and a lower bound for their numbers of realizations.
The proofs give a restriction on any least counterexample to the full
conjecture.

## 1. Labels and the main results

Write [n]={1,...,n}, for n>=1. The label of cell (r,c) is r+c-1.
The label multiset of a permutation p of [n] is

    X(p) = multiset {r+p(r)-1 : r in [n]}.

It records the antidiagonal sums of the permutation matrix. A profile is
binary when these labels are distinct. For an increasing binary profile
L=(l_1,...,l_n), define its density slacks and rank deviations by

    delta_0=0,    delta_k=sum_(i=1)^k l_i-k^2,
    d_i=l_i-(2i-1)=delta_i-delta_(i-1).

Call L admissible if its labels lie in [1,2n-1], every delta_k is
nonnegative, and delta_n=0. These conditions are necessary: any k
permutation cells have k distinct rows and k distinct columns, so their
labels sum to at least k^2. The sum of all labels is n^2.

The conjecture is that every admissible binary profile is X(p) for some
permutation p. We prove the following restricted statements.

**Theorem A (two-sided deviations).** Every admissible binary profile with
-2<=d_i<=2 for every i has a permutation realization.

**Theorem B (one-sided deviations).** Every admissible binary profile
with d_i>=-1 for every i has a realization whose minimum-label
undirected edge is {1,l_1}. If u is the number of positive d_i, there
are at least 2^u distinct realizations. By reflection, every admissible
profile with d_i<=1 for every i is realizable, and has at least 2^u
realizations when u counts its negative deviations.

**Theorem C (extension).** If L is the label multiset of a permutation
of [n], then

    Q(L) = {3,2n+1} multiset-union (L+2)

is the label multiset of a permutation of [n+2]. If all source labels
lie in [2,2n-2], the construction gives an injection from source
permutations, each with a choice of an eligible path, into the target
fiber. In particular h(Q(L))>=h(L), where h counts realizations.

Theorem A bounds sorted labels relative to the odd staircase 2i-1.
It does not bound the occupied diagonals to five possible positions.
The two alternatives in Theorem B apply to the entire profile; they
cannot be chosen independently at different ranks.

The standard conjecture and its tournament interpretation appear in
Bebeacua, Mansour, Postnikov and Severini [1]. Nordh [2,3] relates the
problem to extremal Skolem sets and gives reflection and composition
constructions. Li, Liu and Yao [5] prove realization by doubly stochastic
matrices for all admissible binary profiles. Their theorem leaves
permutation realization open. Our proofs below use direct integer
constructions and do not depend on fractional rounding.

Davis and Schroeder [6] study tournament decompositions and restrictions
on label multiplicities. Their Lemma 3.5 requires a suitable selection
of tournaments; their Conjecture 4.17 includes binary realization.
Neither supplies general integer realization. In their zero-based
notation our labels become c_i=l_(i+1)-1. The deviation families here
concern label positions rather than multiplicity partitions.

## 2. Elementary constructions

We regard a permutation cell (r,c) as the directed edge r to c. After
forgetting its direction, its label is unchanged. The underlying
multigraph has degree two at every vertex, with a loop counted twice.
Conversely, every finite multigraph of degree two can be oriented to
give indegree and outdegree one at each vertex: its components are
cycles, including isolated loops and pairs of parallel edges. Choosing
a direction on each component gives a permutation with the same labels.

### Zero cuts and reflection

If delta_k=0 for 0<k<n, then L splits into the profiles

    A=(l_1,...,l_k),    B=(l_(k+1)-2k,...,l_n-2k).

Both are admissible. For the board endpoints, l_k<=2k-1 follows from
the preceding density inequality, and l_(k+1)>=2k+1 from the next one.
The local slacks of A and B are the corresponding slacks of L. Their
rank deviations are the corresponding segments of d. Realizations of
A and B give a realization of L by placing their matrices in consecutive
diagonal blocks.

Reflecting both board coordinates replaces L by
(2n-l_n,...,2n-l_1). Its deviation word is (-d_n,...,-d_1), and its
slacks are the original slacks in reverse order. Transposition preserves
all labels and reverses all directed edges.

Call a profile primitive if all its internal slacks are positive.
It is enough to handle primitive profiles after splitting at zero cuts.

### Compression with two specified cells

Suppose a binary profile S=(s_1,...,s_n), n>=2, is realized by a permutation
having cells (1,b) and (c,n), where b=s_1 and c=s_n-n+1. Suppose also
that

    T=(s_1+1,s_2,...,s_(n-1),s_n-1)

is binary. Then T has a realization.

Delete those two cells and translate each remaining cell by (-1,+1).
The translated rows are [1,n-1] except c-1, and the translated columns
are [2,n] except b+1. On forgetting direction, its four missing
incidences are {1,n,c-1,b+1}, with multiplicity. Add the two edges
{1,b+1} and {c-1,n}. The graph now has degree two throughout. Its
labels are exactly T, so orienting its cycles proves the assertion.

### Promotion of a specified first-row cell

Let p be a permutation of [m], m>=2, with p(1)=b and label multiset K.
There are two recoverable extensions to order m+1 with label multiset

    (K minus one occurrence of b) multiset-union {b+1,2m}.

Delete (1,b) and translate the remaining cells by (-1,+1). On [m+1],
the missing incidences are {1,b+1,m,m+1}. Add edges {1,b+1} and
{m,m+1}. This produces a degree-two graph with the required labels.

For the two choices and their inverse, keep the directions of the
translated core. It has two paths from {1,b+1} to {m,m+1}, and possibly
some directed cycles. A vertex shared by the two sets is an isolated
path. The two new edges join the paths into a cycle containing the
three distinct vertices 1,m,m+1. Its two orientations give distinct
permutations; keep every other cycle's direction as supplied.

From either output, delete the specified two edges from that common
cycle, orient its remaining paths from {1,b+1} toward {m,m+1},
translate back by (+1,-1), and restore (1,b). This recovers p. The
output direction at {1,b+1} records the choice of orientation. Thus
for fixed b this is an injection of two copies of the source family.
The marked edges are identified by their positions, so repeated labels
do not affect the inverse. The restriction m>=2 ensures the cycle has
at least three vertices.

## 3. Proof of the extension theorem

Given a permutation p of [n], draw the arcs r to p(r)-3 on the integer
vertices [-2,n]. Every vertex has at most one incoming and one outgoing
arc. The three sources are n-2,n-1,n, and the three sinks are -2,-1,0.
A coincident source and sink is an isolated path. The source paths end
at distinct sinks: they cannot merge or enter a directed cycle.

At least one path starts at s in {n-2,n-1} and ends at t in {-1,0},
since at most one of these two sources can end at -2. Let I be its
nonterminal vertices. Replace each source cell (r,c) by

    (c-1,r+3), if r is in I;
    (r+2,c), otherwise.

Add the cells (1-t,t+3) and (s+2,2n-s). The old labels increase by
two and the new labels are 3 and 2n+1.

To check the margins, first put every old cell at (r+2,c). These
occupy rows [3,n+2] and columns [1,n]. Switching the path arc v to w
replaces (v+2,w+3) by (w+2,v+3). Summing these changes along the path
removes row s+2, adds row t+2, removes column t+3 and adds column s+3.
The added cells restore the removed row and column. The remaining
boundary coordinates satisfy

    {t+2,1-t}={1,2},    {s+3,2n-s}={n+1,n+2}.

Thus every row and column in [n+2] occurs once. This also covers the
isolated paths at small orders and proves ordinary realization of Q(L).

For the injection, assume all source labels are in [2,2n-2]. The new
labels 3 and 2n+1 are unique. Their cells recover t and s respectively
from t=column(low)-3 and s=row(high)-2. Delete them. Starting with
state s, read the remaining cell in column state+3. If its row is a,
recover source cell (state,a+1), and change state to a-2. Continue to
t. The other cells (r,c) recover (r-2,c). This recovers both the source
and the chosen path. Each source has at least one eligible path, proving
the counting assertion. For a binary interior source the target is binary.

The extension does not prescribe both outer extreme edges. A new label
3 may occur at (2,2). This distinction is why the extension is usable
without a general boundary-selection theorem.

## 4. Proof of the two-sided theorem

Use strong induction on n. The order-one profile is (1). A zero cut
reduces to smaller profiles with the same deviation bound, as in Section
2. We may therefore suppose L primitive and n>1. Then
d_1 is 1 or 2 and d_n is -1 or -2. The following cases exhaust these
possibilities.

**Case 1: d_n=-1.** Here l_n=2n-2. Set

    K=(l_1-1,l_2,...,l_(n-1)), of order n-1.

Its slacks are delta_k(L)-1 and are nonnegative, with the last zero.
Its labels remain distinct and positive. Strictness gives
l_(n-1)<=2n-3, so it lies on the smaller board. Its deviation word is
(d_1-1,d_2,...,d_(n-1)), still in [-2,2].

Induction realizes K. Its minimum label is 1 or 2. Label 1 forces
(1,1), while label 2 forces (1,2) or (2,1). Transpose if necessary
to put that cell in row one. Promotion raises its label by one and
adds 2n-2, producing L. There is no primitive admissible binary profile
of order two, so the promotion source always has order at least two.

**Case 2: d_1=1 and d_n=-2.** Reflect L, apply the reduction in
Case 1 to obtain a smaller child, and reflect the resulting realization
back. Only the smaller child invokes induction.

**Case 3: d_1=2, d_n=-2, and every internal slack is at least two.**
Here the extreme labels are 3 and 2n-3. Set

    K=(l_2-2,...,l_(n-1)-2), of order m=n-2.

Its slacks are delta_j(K)=delta_(j+1)(L)-2, including both endpoints.
They are nonnegative and end at zero. Its labels are distinct and lie
in [2,2m-2], and its deviations are (d_2,...,d_(n-1)). Induction
realizes K. The extension theorem then realizes
{3,2m+1} union (K+2), which is exactly L.

**Case 4: d_1=2, d_n=-2, and some internal slack is one.** Set

    S=(2,l_2,...,l_(n-1),2n-2).

Every internal slack drops by one, so S is admissible and has an
internal zero cut. Its deviations stay in [-2,2]. Split at all zero
cuts and realize the smaller blocks by induction.

The first block's minimum label 2 forces the edge {1,2}; the last
block's maximum local label 2m-2 forces {m-1,m}. They are different
blocks, so we can transpose them independently. Choose the first
orientation to supply cell (1,2), and the last to supply cell (n-1,n)
in the combined permutation. The other labels lie between 4 and
2n-4. The compression construction therefore replaces the extremes
2 and 2n-2 by 3 and 2n-3, giving L.

Every induction input has smaller order and remains admissible and
binary. This completes the proof of Theorem A.

## 5. One-sided profiles, counting, and consequences

### Proof of Theorem B

Assume every d_i>=-1. Induct on order while retaining a minimum edge
{1,l_1}. Zero-cut decomposition preserves that property in the first
block. For a primitive profile, d_n=-delta_(n-1) is negative, so the
one-sided bound forces d_n=-1 and l_n=2n-2.

Put a=l_1-1 and use the same child
K=(l_1-1,l_2,...,l_(n-1)) as in Case 1. Its first deviation is d_1-1
and every other deviation is unchanged, so it remains in the one-sided
class. By induction choose a realization with minimum edge {1,a}.
Transpose if necessary to put that cell at (1,a), and promote it.
The resulting minimum edge is {1,a+1}={1,l_1}. This closes the
induction. Reflection proves the other one-sided existence statement.

For the count, construct an injective family of 2^u permutations,
all retaining that minimum edge. Counts multiply over zero-cut blocks,
since the blocks occupy fixed disjoint index intervals and their u
values add. In a primitive step there are two possibilities.

If a=1, the child minimum is a loop and is already in row one. The
number of positive deviations in the child is u-1. The two-copy
promotion injection doubles the selected child family, giving 2^u.

If a>1, the child has u positive deviations. For each selected child
permutation q record a bit epsilon indicating whether it must be
transposed to orient {1,a} from 1 to a. That edge has exactly one
direction: both directions would repeat label a. Promote the oriented
source using epsilon as the output cycle-orientation bit. The inverse
recovers the oriented source and epsilon, and hence recovers q by
transposing back when needed. This preserves all 2^u selected children
injectively. The singleton starts with one realization. Reflection
transfers the count to negative deviations in the other family.

### Unbounded examples

For each k>=1, the word

    (2 repeated k times, 1, 0, -1, -2 repeated k times)

has length 2k+3, sum zero, nonnegative partial sums, and no adjacent
drop greater than one. Hence l_i=2i-1+d_i gives an admissible binary
profile. Its maximum slack is 2k+1. Theorem A realizes these profiles
even though neither one-sided hypothesis applies. The theorem includes
all admissible deviation words in the interval, beyond these examples.

The word (m,m-1,...,1,0,-1 repeated m(m+1)/2 times), for m>=1,
likewise gives an admissible binary profile in Theorem B. Its maximum
positive deviation is m and its maximum slack is m(m+1)/2. Thus the
unrestricted side of Theorem B has no hidden fixed deviation bound.

### A least-counterexample restriction

If the full conjecture has a least-order counterexample, it cannot
satisfy both l_1<=3 and l_n>=2n-3. A least counterexample is primitive,
and under these endpoint bounds the same four cases of Section 4 apply.
The interior deviations need not be bounded: all smaller admissible
children are realizable by minimality. The source cells needed in Cases
1, 2 and 4 are still forced by their extreme labels, and Case 3 uses
ordinary extension. Each case would realize the alleged counterexample.

Equivalently such a counterexample has d_1>=3 or d_n<=-3. After
reflection it may be taken to have l_1>=4. This does not settle profiles
with those remaining endpoint shapes.

## 6. Verification and scope

The informal proofs above were developed in Analytic-Lab, probe P0175.
The two-sided Python construction was independently replayed on all
44,984 admissible profiles through order 13. Those finite checks test the
implementation; they do not replace the induction.

The Lean development and current verification boundary are recorded in
[VERIFICATION.md](VERIFICATION.md). This note describes the full intended
mathematical scope, including statements whose formal proofs are still in
progress. The separate slack-22 computational theorem is not a premise.

No result here proves general anchor selection or general rounding to a
permutation. The unrestricted conjecture remains open. No worldwide
priority claim is made. Nordh's composition constructions are prior work.
The full construction section of Brualdi–Fritscher [4] has not yet been
retrieved for detailed comparison; only its publisher abstract was available.

The extraction source is Analytic-Lab commit
`391d59f60d405155b145c69c3a4639797e4c28fd`. This document contains the positive
proofs needed to read the note without access to that private repository.

## References

1. C. Bebeacua, T. Mansour, A. Postnikov and S. Severini,
   [On the X-rays of permutations](https://math.mit.edu/~apost/papers/xray.pdf),
   2005, Section 4.
2. G. Nordh, [Perfect Skolem sets](https://gustavnordh.com/perfskolfinal.pdf),
   Discrete Mathematics 308 (2008), 1653–1664.
3. G. Nordh, [A note on X-rays of permutations and a problem of Brualdi and Fritscher](https://arxiv.org/abs/1707.03928),
   2017.
4. R. A. Brualdi and E. Fritscher,
   [Hankel and Toeplitz X-rays of permutations](https://doi.org/10.1016/j.laa.2014.02.037),
   Linear Algebra and its Applications 449 (2014), 350–380.
5. B. Li, Y. Liu and Y. Yao,
   [Binary X-rays of doubly stochastic matrices](https://arxiv.org/html/2608.01442v2),
   arXiv:2608.01442v2, 2026.
6. M. Davis and M. W. Schroeder,
   [Relating tournaments and permutations with xrays](https://arxiv.org/html/2606.21532v1),
   arXiv:2606.21532v1, 2026.

## Disclosure

This work was developed with assistance from OpenAI Codex. The proofs
and verification status are stated above; no external review is claimed.
