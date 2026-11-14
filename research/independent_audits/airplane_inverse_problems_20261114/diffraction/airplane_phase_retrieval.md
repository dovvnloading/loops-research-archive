# The airplane angle and the unique worst case of binary phase retrieval at powers of three

For a chain of equally spaced scatterers with real amplitudes $+1$ and $-1$, a complete far-field intensity measurement determines its aperiodic autocorrelation. How many binary chains could have produced exactly the same intensity? At length $3^k$, the unique intensity with the most possible answers comes from the archive's angular substitution $0\mapsto011, 1\mapsto100$. At period 27, even the angular kneading itineraries of two of those answers differ at only one mark.

## Extremal theorem

Let $P(z)=\sum_{r=0}^{N-1}a_rz^r$, with $a_r\in\{-1,1\}$, $a_0=1$, and $N=3^k$, $k\geq1$. Fix the origin and the left-to-right order. Define the intensity as $I_P(t)=|P(e^{it})|^2$ for every real $t$. An intensity fiber is the set of normalized binary words giving that intensity. For $q_j=3^j$, set

$$
 F_{j,s}(z)=1+s z^{q_j}-z^{2q_j},\qquad s\in\{-1,1\}.
$$

**Theorem.** Every intensity fiber has at most $2^k$ words. Exactly one intensity fiber attains this bound. Its members are all the products $P_{\boldsymbol s}=\prod_{j=0}^{k-1}F_{j,s_j}$, and its intensity is

$$
 I_*(t)=\prod_{j=0}^{k-1}\bigl(3-2\cos(2\cdot 3^j t)\bigr).
$$

Allowing the global sign gives $2^{k+1}$ words in this fiber. Identifying normalized reversal gives $2^{k-1}$ reversal classes. These conventions concern the continuous-frequency intensity of a finite chain. Cyclic autocorrelation alone is a different inverse problem.

**Proof of the upper bound.** For every binary $P$, reduction modulo two gives

$$
 \bar P=1+z+\cdots+z^{3^k-1}=\prod_{j=0}^{k-1}(1+z^{3^j}+z^{2\cdot3^j}).
$$

The factor indexed by $j$ is the cyclotomic polynomial $\Phi_{3^{j+1}}$, irreducible over $\mathbb F_2$. Indeed its roots have order $3^{j+1}$, and their Frobenius orbit length is the multiplicative order of 2 modulo $3^{j+1}$, which is $2\cdot3^j$. For $m=2u$ the identity $v_3(2^m-1)=1+v_3(u)$ follows from $4^u-1=(4-1)(1+4+\cdots+4^{u-1})$ when $3\nmid u$ and successive cubing, which adds one to the valuation. Odd $m$ cannot give $2^m\equiv1\pmod3$. Thus all $k$ factors are distinct and reciprocal over $\mathbb F_2$.

Factor $P$ over $\mathbb Z[z]$, normalizing every factor to constant term 1. Every leading coefficient is $\pm1$, so modulo two each nonconstant factor retains its degree. Unique factorization and squarefreeness imply that $P$ has $r\leq k$ distinct irreducible factors $f_i$, whose reductions are products of disjoint, nonempty sets of the displayed cyclotomic factors. Write $f_i^\dagger(z)=\operatorname{lc}(f_i)z^{\deg f_i}f_i(z^{-1})$ for normalized reversal. Since each reduction is reciprocal, $f_i^\dagger$ cannot be any different factor $f_j$.

A second normalized binary $Q$ has the same intensity exactly when $Q(z)Q(z^{-1})=P(z)P(z^{-1})$ as Laurent polynomials. The extremes of their autocorrelations fix the same leading coefficient. Unique factorization implies that $Q$ chooses either $f_i$ or $f_i^\dagger$ for each $i$, with a self-reciprocal factor forced. This gives at most $2^r\leq2^k$ normalized possibilities. A flip can produce coefficients outside the binary alphabet for a general word.

**Attainment.** The displayed $F_{j,s}$ are normalized reversals of each other at fixed $j$. Multiplying by a new factor concatenates three signed copies of the previous word, so every product is binary. Its coefficient at position $3^j$ is $s_j$, giving $2^k$ distinct words. A single factor has squared modulus $3-z^{2q_j}-z^{-2q_j}$ on the unit circle, giving the stated common intensity. Reversing the whole product and normalizing flips every $s_j$.

**Rigidity of equality.** Suppose $2^k$ normalized binary words achieve some intensity. Every inequality in the upper bound is an equality. There must be $k$ irreducible non-self-reciprocal factors, each lifting exactly one cyclotomic polynomial, and *every* independent reversal must yield a binary word.

The factor lifting $1+z+z^2$ has the form $f=1+a z-z^2$ with $a$ odd. A positive leading coefficient would make this quadratic self-reciprocal. Let $G$ be the product, constant-normalized, of any reversal choices for the other $k-1$ factors. Both $fG$ and $f^\dagger G$ are binary. Their difference $2azG$ has entries in $\{-2,0,2\}$. As $G(0)=1$, this forces $|a|=1$, and every coefficient of $G$ lies in $\{-1,0,1\}$. Modulo two,

$$
 \bar G=1+z^3+z^6+\cdots+z^{3^k-3}.
$$

Hence $G=H(z^3)$ where $H$ is a normalized binary word of length $3^{k-1}$. The $2^{k-1}$ choices of $G$ are distinct by unique factorization. All corresponding $H$ have the same intensity, since all $G$ do and the map $z\mapsto z^3$ covers the unit circle. Induction from the single word of length 1 now determines their intensity uniquely. Multiplying by the sole possible quadratic intensity $3-2\cos(2t)$ proves uniqueness at level $k$. ∎

## Which external angle sits in that fiber?

Use bit 0 for the sign $+1$. The all-minus phase vector produces precisely $\sigma^k(0)$, with $\sigma(0)=011$ and $\sigma(1)=100$. This follows by applying the substitution to each sign, which replaces $P(z)$ by $(1-z-z^2)P(z^3)$. Among the normalized words in this fiber it is the lexicographically largest bit word. The first differing phase $j$, reading from fine to coarse, changes its first differing bit at index $3^j$ from 1 to 0. For periodic binary fractions, the same comparison gives numerical order. Reading the signs at indices $1,3,\dots,3^{k-1}$ recovers every phase. Among additional one-bit observations this count is minimal even with adaptive observations, since there are $2^k$ alternatives.

The finite endpoints fixed by the archive are $3/7$, $228/511$, and $59914011/134217727$ for $k=1,2,3$. Deeper words in this note require only the angular substitution. The interpretation of their intensities is a one-dimensional signed-scattering model.

## A pair whose kneading words differ at one position

Take the periodic seed words $011$ and $001$ and substitute each $k-1$ times. These have the same intensity because only the coarsest sign $s_{k-1}$ changes. Their exact angular kneading words differ at just position $2\cdot3^{k-1}$, counted from 1. At period 27 the two periodic numerators, over the common denominator $134217727$, are

| Numerator | Binary block | Angular kneading |
|---:|---|---|
| 59914011 | 011100100100011011100011011 | 10010110110010110010010110* |
| 59885851 | 011100100011100100100011011 | 10010110110010110110010110* |

The first is the archive's lower characteristic root angle. The second provides an alternative symbolic observation. The two self-referenced angular partitions use their respective interval boundaries $\theta/2$ and $(1+\theta)/2$.

**Proof.** If $x=0.\overline w{}_2$ and the $j$-th bit is $b$, let $y$ be the tail beginning with the next bit, cyclically. The $j$-th kneading mark is 1 if $b=0,y>x$ or $b=1,y<x$. Equality gives a star. Assume $w$ starts in 0 and contains both bits. The substituted reference $x'$ starts $011$. At the first position of a substituted block $011$ or $100$, the tail starts $11$ or $00$, giving mark 1 in both cases. At the second position of $011$ the tail starts $1$, giving mark 0. At the second position of $100$, the tail starts $00$ if the next block is $011$ and starts $010$ if it is $100$. Both are below $011\ldots$, again giving 0. At the third position the bit is $1-b$, and the tail begins at a block boundary. The substitution preserves lexicographic order of tails, so this third mark is the complement of the original mark, with stars fixed. Thus each original mark $u$ is replaced by $10\bar u$. The original seed kneadings $10*$ and $11*$ differ only at position 2, and a difference at position $d$ moves to position $3d$. This also proves exact period $3^k$ for these two angles because each expanded block has one star only at its final return. ∎

## Exact correlation at every lag

The coefficient at lag $h$ in the Fourier expansion of $I_*$ is $C(h)=\sum_r a_r a_{r+h}$, summing only over overlapping indices. It vanishes at odd $h$. At even $h=2m$ with $|h|<3^k$, write $m=\sum_{j=0}^{k-1}d_j3^j$ in balanced ternary, $d_j\in\{-1,0,1\}$, and let $w$ count nonzero digits. Then

$$
 C(2m)=(-1)^w3^{k-w}.
$$

Each term in the Laurent product selects $3$, $-z^{2\cdot3^j}$, or $-z^{-2\cdot3^j}$. Uniqueness of balanced ternary gives the coefficient without cancellation.

## What is known, and how to check the specialization

Baake, Gähler and Grimm studied the generalized Thue–Morse substitutions, including this signed word as their $(1,2)$ case. Their results include the infinite singular continuous diffraction and its Riesz product. Bary-Soroker, Hokken, Kozma and Poonen use cyclotomic reductions in their work on random Littlewood polynomials. Katz, Rahman and Ward's Theorem 1.1 gives general integer factor-reversal theory. Their exhaustive Table 1 records precisely one reversal-class volume of 2 at length 9, and one volume of 4 at length 27 alongside 348 classes of volume 2. The inequality and rigidity argument above identify the archive's word with both exceptional classes, and classify every power of three. Searches for the specific all-powers-of-three equality classification did not locate a prior statement. Priority remains open to literature review.

- [Baake, Gähler and Grimm, *Spectral and topological properties of a family of generalised Thue–Morse sequences*](https://arxiv.org/abs/1201.1423)
- [Bary-Soroker, Hokken, Kozma and Poonen, *Irreducibility of Littlewood polynomials of special degrees*](https://doi.org/10.1093/imrn/rnaf326)
- [Katz, Rahman and Ward, *Sequences with identical autocorrelation functions*, Theorem 1.1 and Table 1](https://arxiv.org/html/2308.07467v3)
- [Archive, certified period-27 center and characteristic-angle identification](https://github.com/dovvnloading/loops-research-archive/blob/0a28eb11b0a2636db5a766081b1455a346e3837c/research/independent_audits/period27_center_tuning_identification_20261106.md)

Run the companion `verify_airplane_phase_retrieval.py` with Python 3. It enumerates every normalized word at lengths 3 and 9, inverts the period-27 autocorrelation with an independent coefficient search, checks all lags and phases through length 243, and checks the single kneading difference through length 2187. These finite computations complement the arbitrary-depth proof.
