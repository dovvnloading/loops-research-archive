# How the Mandelbrot plane separates the diffraction twins

Let $N=3^k$ and read a normalized sign word in coefficient order as an $N$-bit binary fraction, repeated periodically. A positive coefficient is bit 0. All $2^k$ words in the extremal intensity class have exact doubling period $N$ and land, as parameter-ray angles, at $2^k$ **distinct** parabolic roots. Exactly one of those roots is real. A first entry time of the doubling orbit determines exactly where a nonreal twin first departed from the real airplane construction.

## The kneading measurements

Write $s_0,\ldots,s_{k-1}\in\{-1,+1\}$ in increasing order of factor scale and let $b_j=(s_j+1)/2$. The finest substitution is $\tau_s(0)=0(1-b)1$ and $\tau_s(1)$ is its bitwise complement, with $b=(s+1)/2$. Thus the negative choice gives $011/100$, the positive choice $001/110$. Apply the coarsest choice first. Both substitutions preserve the order of distinct infinite binary strings and commute with bitwise complementation.

For a periodic angle $x$ let $D(x)=2x\pmod 1$. The entry $K_i(x)$ is 1 if $D^{i-1}x$ is strictly between $x/2$ and $(1+x)/2$, 0 in the exterior, and a star at an endpoint. Then, with addition modulo two,

$$K_{2\cdot 3^j}(x)=b_j\mathbin{\oplus}(j\bmod 2),\qquad 0\le j<k.$$

**Proof.** At a position carrying bit $a$ and followed by tail $y$, the mark is 1 precisely when $a=0$ and $y>x$, or $a=1$ and $y<x$. Equality gives a star. At the second position of the reference word its next bit is 1 and the reference starts in 0. Its mark is therefore $b_0$. At the third position of any substituted block, the bit is the complement of its source letter and the remaining tail is the order-preserving substitution of the source tail. Thus $K_{3i}(\tau_s x)$ is the complement of $K_i(x)$ for either sign, with the star fixed. Iterating yields the formula. To recover the last sign, the innermost word is the periodic repetition of a single three-bit block, whose second mark is given by the same comparison. The angular period divides $N$; a proper divisor divides $N/3$, but the first and third blocks of length $N/3$ are complements. Thus the period is exactly $N$.

Two different sign vectors differ in a sampled mark. Periodic parameter rays land, and two landing together must have the same kneading sequence. Consequently the $2^k$ normalized words reach different roots. Even allowing adaptive queries of kneading entries takes at least $k$ binary answers to resolve all the roots: the star occurs only at multiples of the common period. [Schleicher, *Internal Addresses of the Mandelbrot Set and Galois Groups of Polynomials*, §3, Lemma 3.1 and the discussion preceding it](https://armj.math.stonybrook.edu/html-articles/Files-2015-2024/16-42/). [Zakeri, *External rays and the real slice of the Mandelbrot set*, §2](https://arxiv.org/pdf/math/0210382).

## When a nonreal ray reveals itself

Let $H(x)=\min\{m\ge1:x<D^m x<1-x\}$, with $H=\infty$ for an empty set. For these normalized angles $0<x<1/2$. If $j$ is the least index with $s_j=+1$, then

$$H(x)=3^j.$$

For the all-minus word $H=\infty$. In particular the class contains exactly $2^{k-1-j}$ words with first hit $3^j$, and one word with no hit. This is a deterministic first entry time for the doubling map, measured in iterates.

**Proof.** Let $B=\tau_-^j(0)$, of length $q=3^j$, and let $\overline B$ denote its bitwise complement in this paragraph. The reference starts with $BB\overline B$. After $q$ shifts it starts $B\overline B$, so it lies strictly between the reference and its complement. For $0<m<q$ its first $q$ bits are a nontrivial cyclic rotation of $B$. The angle given by repeating $B$ is the lower root ray of the real $j$-fold airplane by the tuning theorem. Zakeri's Theorem 3.7 forbids every doubling iterate of that angle from the open interval bounded by it and its reflection. No nontrivial rotation equals $B$, by exact period. No rotation equals its complement, since $q$ is odd and their counts of ones differ. The rotation is therefore strictly outside the closed interval already at the level of its first $q$ bits. For $j=0$ there are no earlier positive times to check. The all-minus word itself is the iteratively tuned real root ray and has no hit. Applying Theorem 3.7 to the periodic angles identifies precisely this word as the one with real landing point. [Zakeri, §2 and Theorem 3.7](https://arxiv.org/pdf/math/0210382).

The word with only the coarsest sign changed is the genuine airplane tuning, $k-1$ times, of the lower rabbit ray $1/7=0.\overline{001}_2$. Its companion dynamical construction starts from the real airplane ray $3/7=0.\overline{011}_2$. The full kneading itineraries differ only at position $2\cdot3^{k-1}$. For the true airplane substitution, every mark $u$ expands to $10\overline u$ (star fixed), as proved in the companion extremal theorem. The two initial itineraries are $10*$ and $11*$. The positive factor choice $001/110$ elsewhere in this classification is an algebraic operation. The use of the rabbit here takes only its lower seed angle and then applies genuine airplane tuning. [Zakeri, §2, equation (2.2)](https://arxiv.org/pdf/math/0210382). [Milnor, *Periodic Orbits, External Rays and the Mandelbrot Set*, orbit portraits and the characteristic arc](https://arxiv.org/abs/math/9905169).

## A phase-sensitive measurement and a distance formula

Let $P_s(z)=\prod_{j=0}^{k-1}(1+s_j z^{3^j}-z^{2\cdot3^j})$. A single phase-sensitive readout separates all $2^k$ intensity twins. For a locally continuous phase of $P_s(e^{it})$ about $t=0$, its derivative, in lattice-site units, is

$$T_s=\left.\frac{d}{dt}\arg P_s(e^{it})\right|_{t=0}
=\frac{P'_s(1)}{P_s(1)}
=\frac{N-1}{2}-2\sum_{j=0}^{k-1}s_j3^j.$$

Indeed $P_s(1)=\prod s_j=\pm1$, and the logarithmic derivative of each factor at 1 is $3^j(1-2s_j)$. The highest differing ternary power exceeds the sum of all smaller ones, so the readouts are distinct. Differences are multiples of 4, and flipping just the finest sign attains 4. An absolute slope error less than 2 therefore suffices in this ideal model with fixed origin and orientation.

For two phase vectors differing at $h$ coordinates, the underlying binary words' Hamming distance is exactly $(3^k-3^{k-h})/2$. Indeed ternary site digits independently index vector factors $(1,s_j,-1)$. The inner product of two such factors is 3 when equal and 1 otherwise. Tensor multiplication gives $3^{k-h}$ for the total inner product, and the distance formula follows. In particular the airplane and its tuned-rabbit twin disagree at exactly one third of their raw bits, despite having identical intensity and a single differing kneading mark per period.

## Reproducibility

The independent script constructs every coefficient directly from its ternary site digits and computes the angular itineraries by exact modular arithmetic. It checks all 254 phase choices through length 2187, including exact periods, individual kneading readouts, first hits and phase slopes. It checks every pairwise Hamming formula through length 243. The eight exact period-27 records are in `period27_readout.json`. Run `python3 verify_geometric_readout.py` from this directory.

These proofs apply to signed scattering from the angular bit encoding. Their geometric conclusions concern actual periodic parameter-ray landing where the cited theorems apply. The scattering experiment is a mathematical model; the claims imply no measured diffraction law for the Julia or Mandelbrot set.
