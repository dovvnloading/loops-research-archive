# Recovering an external-angle portrait from two distance counts

The archive records nine pairs of external angles at a real Misiurewicz parameter. Suppose an observer discards the labels, the pairings, the orientation and the multiplicities. The observer keeps the distinct chord lengths between **every** pair of the 18 angle points on the unit circle. **Nineteen different configurations up to rotation produce exactly that list.** Two selected multiplicities identify the archive configuration. Every individual multiplicity leaves an ambiguity.

The site set is a modular copy of the signed powers of two. The ambiguity has an exact classification in the infinite family of cyclic groups of order $2^n-1$ for every $n\ge6$. The proof joins a six-term binary carry bound to a finite exhaustion of the smaller periods.

## The measurement

Write distances in units of 1/511 of a turn. The unlabelled angle set is the following subset of the cyclic group of order 511.

$$
S=\{\pm228\,2^j\bmod 511:0\le j<9\}.
$$

This follows by reading the numerators in the [archive manifest](https://github.com/dovvnloading/loops-research-archive/blob/0a28eb11b0a2636db5a766081b1455a346e3837c/results/period27_tip_ray_portrait.json). Let $C_A(d)$ count ordered pairs of sites with $x-y=d$, and write $D_A$ for its support. For $1\le d\le255$, $C_A(d)$ is also the number of unordered chords of angular distance $d/511$. The Euclidean chord length is $2\sin(\pi d/511)$, a strictly increasing function on this range. The measurement therefore has the same information in either unit. The experiment concerns the 153 pairwise chords, including the nine landing-pair chords.

For $S$, precisely 63 positive distances occur. Of those, 45 have multiplicity two, nine have multiplicity three and nine have multiplicity four. Their total multiplicity is $45\cdot2+9\cdot3+9\cdot4=153$.

## Exact recovery at period nine

Let $E=S\cup\{0\}$. Every 18-site configuration on the unit circle with the same length support as $S$ is a rotation of $E\setminus\{x\}$ for some $x\in E$. The 19 deletions give 19 distinct rotation classes. Reflection identifies the deletions indexed by $x$ and $-x$, leaving ten classes under rotations and reflections.

Among these configurations the following two measurements determine $S$ up to rotation.

| Distance in turns | Required multiplicity | False deletions surviving this count, in the coordinates of $E$ |
|---|---:|---|
| $55/511$ | 3 | $x=55,456$ |
| $57/511$ | 3 | $x=57,454$ |

There is no common false deletion. For every one of the 255 distances on the grid at least one false deletion agrees with its count. The experiment specifies the number of sites and the complete list of occupied lengths first. The optimality statement counts individual multiplicities disclosed in addition to that information.

**Why the search covers the whole circle.** Rotate one site to angle zero. Its possible distances to every other site put all other sites in the 511-grid. A unit gap occurs, so rotate again to arrange two sites at 0 and 1 in grid coordinates. Every additional candidate $v$ must have both $v$ and $v-1$ in $D_S$. This leaves precisely 43 candidates besides the two anchors. Two candidates coexist exactly when their difference lies in $D_S$. Thus every normalized solution is a 16-element clique among those 43 candidates. Enumeration finds 34 cliques. They consist exactly of deletions from $E-227$ and $E-283$ that preserve both anchors. In fact each 19-set allows 17 such deletions. The verifier compares the enumerated **sets** with the predicted sets, checks the rotation-class count, and checks each deletion's full support. Its recursion lists the candidates in increasing order and prunes a branch only when the remaining count cannot reach 18. The enumeration assumes no symmetry or dynamics of the competitor.

## An ambiguity at all scales

In any finite abelian group of odd order take a nonempty set $S$ with $-S=S$, $2S=S$, and $0\notin S$. For every $x\in S$, replacing $x$ with 0 preserves the support of the pair-separation histogram.

To see this, put $E=S\cup\{0\}$. The new differences involving zero already belong to $S-S$, since $s=2s-s$. On deleting $x$, a difference originally represented by $(a,b)$ is also represented by $(-b,-a)$. For a nonzero difference the two representations have disjoint site sets, since $a,b$ are nonzero, unless $a=-b$. In that exceptional case the difference is $2a\in S$, and at least one of $(2a,0)$ and $(0,-2a)$ survives deletion. Zero remains represented by a diagonal pair. Thus $D_{E\setminus\{x\}}=D_S$. These sets can be congruent in small groups.

There is a second consequence of the same involution. With the symmetry center fixed at zero, $C_S(d)$ is odd exactly when $d\in 2S=S$. Fixed ordered pairs are $(a,-a)$, uniquely determined by $d=2a$ since the ambient group has odd order. This elementary parity decoder uses the symmetry of the true set. The preceding clique computation establishes uniqueness against unrestricted competitors at period nine.

## Classification for every Mersenne period

For $N_n=2^n-1$, put $H_n=\{\pm2^j\bmod N_n:0\le j<n\}$. The archive case is carried to $H_9$ by multiplication by the modular inverse of 228. This multiplication permutes the bins, and need not preserve their actual lengths. It preserves equality of supports and of corresponding multiplicities.

**Theorem.** For each integer $n\ge6$, every $2n$-element set with $D_A=D_{H_n}$ is a translate of $(H_n\cup\{0\})\setminus\{x\}$. At $n=5$, the set $\{0,3,5,8,16,20,26,27,28,30\}$ has the same support (all 31 residues) and fits in no translate of $H_5\cup\{0\}$.

For $6\le n\le59$ the finite verifier uses anchors $0,9$, available because $9=8-(-1)$. For $7\le n\le59$, the initial intersection leaves $4n+7$ extra vertices. The program lists exactly $4n-2$ anchored completions even with the weaker requirement $D_A\subseteq D_{H_n}$. They match the predicted deletions. At $n=6$ the weaker condition admits additional cliques, so the verifier filters explicitly on equality of supports. The all-scale replacement argument proves the converse for every $n$. The default regression also covers $60\le n\le64$, where the following proof applies independently.

### A uniform proof for $n\ge60$

Write $H=H_n$, $E=H\cup\{0\}$ and $D=H-H=H+H$. Since $H$ is stable under doubling and negation, $E-E=D$. Normalize the unknown configuration $Q$ to contain $0,9$. Every difference of sites of $Q$ belongs to $D$.

**Six-term carry lemma.** In a minimal nonempty zero-sum multiset of $k\le6$ signed powers of two modulo $2^n-1$, the exponent of any leaf is within cyclic distance $k-2$ of the exponent of every other leaf. Here $n>6$. To prove this, if two opposite terms at one exponent occur they already form a zero pair. Otherwise there must be repeated equal signs at some exponent. Indeed, with all exponents distinct, the largest power exceeds the sum of the smaller ones and the sum of magnitudes is strictly below $2^n-1$ because fewer than $n$ positions occur. Merge two same-sign equal powers by carrying one exponent upward modulo $n$. Minimality is preserved since any proper zero submultiset after merging lifts to one before merging. Iteration ends with two opposite terms at one exponent $r$. The resulting two carry trees have $k-2$ internal merges altogether. Every original exponent equals $r-h$ modulo $n$, where its depth $h$ lies between 0 and $k-2$. The depths of two leaves thus differ by at most $k-2$, proving the claim.

**Bound on the two-anchor intersection.** Put $L=1+E$ and $R=8+E$. We show that every $q\in Q$ belongs to $L\cup R$ except for at most nine possible values. Choose $u,v,w,z\in H$ with $q=u+v$ and $q-9=w+z$. Decompose the zero-sum multiset

$$
(u,v,-w,-z,-1,-8)
$$

into minimal zero submultisets. If one contains only variable terms, it has exactly two of them. A single term is nonzero, and using three or more would express 9 as at most one signed power. If these two come from the same side, $q=0$ or $q=9$. If they come from opposite sides, the other two variable terms sum to 9 with their displayed signs. The only signed-powers pair summing to 9 is $1,8$: in $n$ cyclic binary positions, 9 has two isolated ones and more than two zeros. A difference of distinct positive powers gives one cyclic run of ones; a negative sum of distinct powers gives two zeros; a repeated power with equal sign gives an element of $H$. Hence $q\in L\cup R$.

In the other case, each variable lies in a minimal component meeting one of the fixed exponents 0 and 3. The carry lemma puts all four exponents in the cyclic interval $[-4,7]$. Multiply by 16 to unwrap this interval. The four terms become ordinary signed powers $P=\{\pm2^j:0\le j\le11\}$. Their relation is an equality of integers: the absolute value of the potential congruence error is at most $4\cdot2^{11}+144<2^n-1$. Enumerate the elementary set $W=(P+P)\cap(144+P+P)$. It has 57 elements. Removing all $y\in W$ for which $y-16$ or $y-128$ is zero or a signed power leaves the following nine integers:

$$
-144,\;-120,\;-96,\;-80,\;72,\;224,\;240,\;264,\;288.
$$

The short function `carry_window_check` verifies that identity by computing at most $24^2$ two-term sums. Thus any $q\notin L\cup R$ lies among these nine values divided by 16 in the cyclic group.

**Bound on neighbors of an exterior site.** For any $g\notin E$, at most 55 elements $h\in E$ satisfy $g-h\in D$. Reserve one slot for $h=0$. If there is any qualifying nonzero $h$, fix one representation $g=c_1+c_2+c_3$ by elements of $H$. Any other qualifying nonzero $h$ gives $g=h+a+b$ for $a,b\in H$. In the six-term difference of the two representations, each minimal zero component meets both triples. A zero submultiset on a single side would leave at most one term on that side, forcing $g\in E$. The carry lemma therefore puts the exponent of $h$ within four positions of one of the three $c_i$. This gives at most $3\cdot9\cdot2=54$ signed powers and proves the bound.

If $Q$ lies in neither $L$ nor $R$, use a site of $Q\setminus L$ and apply the exterior-neighbor bound after translating $L$ to $E$. This gives $|Q\cap L|\le55$. A site of $Q\setminus R$ gives $|Q\cap R|\le55$. With the nine exceptional possibilities, $|Q|\le119<2n$. Consequently $Q$ lies in one translate of $E$, which has $2n+1$ elements. It must be one of its single-site deletions. This completes the necessity proof for $n\ge60$.

The choice of diagnostic counts also scales. In the unscaled model use $d=1,2$. For $n\ge6$, $C_{H_n}(1)=3$. The three representations are $(2,1)$, $(-1,-2)$ and $(2^{n-1},-2^{n-1})$ modulo $2^n-1$. To check exhaustion, take signed representatives: a difference congruent to 1 is 1 or $1-(2^n-1)$ or $1+(2^n-1)$. Ordinary adjacent powers give the first two pairs. Two signed powers cannot differ by $2^n-2$ for $n\ge 4$ (the next largest possible magnitude below $2^n$ is $3\cdot2^{n-2}$). The final case gives $(2^{n-1},-2^{n-1})$, since its signed difference is $2^n$. Doubling yields the corresponding statement for $d=2$. In $H_n\cup\{0\}$ the pairs at gap 1 form two more edges, $(1,0)$ and $(0,-1)$. Of the nonzero sites only $\pm1$ occur in two edges; exactly these deletions restore the count to three. For gap 2 the corresponding sites are $\pm2$. These pairs of sites are disjoint.

One fixed count cannot separate all the deletion models in any of these groups. For $d\in H_n$, delete $d$ itself; symmetry and doubling reduce this case to $d=1$. For $d\notin H_n$ with $d\ne0$, enlarging the set adds no pair at $d$. A site $x\in H_n$ avoids all pairs at $d$ provided $x\pm d\notin H_n$. This holds for some $x$ whenever $2C_{H_n}(d)<2n$. In signed binary, a nonzero residue can occur as a difference of two signed powers in at most four ways outside $H_n$ for $n\ge5$. Indeed, the binary cyclic word of the residue is either a nonconstant cyclic run of ones (difference of positive powers, also negative powers), a word with two ones (sum of two distinct positive powers), or a word with two zeroes (negative of such a sum). Each category contributes two orderings/representations. A word cannot simultaneously have two ones and two zeroes for $n\ge5$. Thus at most four representations occur. Counts at $d=0$ agree by cardinality. The $2n+1$ deletions are all distinct up to rotation. Indeed $C_E(d)\le5$ for every nonzero $d$. The bins in $H_n$ have multiplicity $3+2=5$, and all others have multiplicity at most four. If a nonzero translate related two deletions, the two translates of $E$ would intersect in at least $2n>5$ sites, contrary to the bound. Reflection pairs each deletion at $x$ with the one at $-x$, giving $n+1$ dihedral classes. Thus two additional counts are necessary and sufficient at every $n\ge6$.

## Recovering the pairings

The two independent doubling cycles are $O=\{228\,2^i\}$ and $-O$. A perfect matching of the 18 sites that commutes with doubling must pair the two cycles. An internally matched cycle would have to admit a fixed-point-free involution on nine elements. A match between cycles determines a phase shift $j\in\{0,\ldots,8\}$, pairing $a_i$ with $-a_{i+j}$. In order of increasing shift, the exact counts of crossing chord pairs are

$$
(0,17,11,3,17,17,3,11,17).
$$

Thus with the archive's dynamical origin restored, doubling and absence of crossings recover the nine landing pairs. These conditions do not follow from the distances alone. There is also a way to fix the rotation after reconstructing the shape. If $S+t$ is doubling-invariant then $S+2t=S+t$, hence $S+t=S$. Its stabilizer is trivial: its order divides both 511 and 18. Consequently $t=0$.

## Prior work and interpretation

Periodic phase retrieval and the circular distance reconstruction problem are classical. Fourier transforming the circular pair-separation histogram gives the power spectrum of equal unit scatterers at the angle sites. The two measurements here are **histogram bins**; a lone Fourier intensity is a different observable. The archive-specific result is the classification of candidates after multiplicities are discarded, together with the sharp count budget and its Mersenne extension. A targeted search found no matching result for this family. Global publication priority remains unverified.

- [J. Mandereau, D. Ghisi, E. Amiot, M. Andreatta and C. Agon, *Discrete phase retrieval in musical structures*](https://doi.org/10.1080/17459737.2011.608820), for cyclic interval content and the beltway problem.
- [G. Averkov, *Detecting and reconstructing centrally symmetric sets from the autocorrelation*](https://www.sciencedirect.com/science/article/pii/S0893965909001505), for reconstruction of finite sets in Euclidean space from full autocorrelation.
- [J. Milnor, *Periodic orbits, external rays and the Mandelbrot set*](https://www.numdam.org/item/AST_2000__261__277_0/), for the dynamical setting and orbit portraits.

Run `python verify.py` from this directory with Python 3.9 or newer. The verifier uses exact rational and integer arithmetic in the standard library. With `--manifest /path/to/results/period27_tip_ray_portrait.json`, it also compares the reconstructed chord with both ordered angle fields at each archived phase from 10 through 18.
