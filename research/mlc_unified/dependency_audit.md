# Backward dependency audit

## 1. Final statement

Target:

\[
\boxed{\text{The Mandelbrot set }{\cal M}\text{ is locally connected.}}
\]

Current status: `NOT PROVED`.

The following graph is read from the target backward. A checked node is either proved in
this package or imported under source-locked hypotheses. An open node is not currently
available in the required generality.

```text
MLC at every c in M
|
+-- c not infinitely ql-renormalizable
|   `-- Yoccoz puzzle theorem                                  [IMPORTED]
|
`-- c infinitely renormalizable
    |
    +-- connected relative-neighborhood basis at c             [OPEN-GLOBAL]
    |   |
    |   +-- marked tower rigidity                               [OPEN M7]
    |   +-- phase-parameter holonomy for every mixed tower      [OPEN M7]
    |   +-- bounded puzzle Teichmuller diameter or replacement  [OPEN M7]
    |   `-- shrinking connected basis, not diameter alone       [OPEN M7]
    |
    `-- compact controlled marked tower                         [OPEN-GLOBAL]
        |
        +-- coercivity of response/Value densities              [OPEN M6]
        +-- uniform side constraints, raw cell count unbounded  [OPEN M6]
        +-- future-faithful symbolic/end topology              [PROVED ABSTRACT]
        +-- analytic admissibility of compactified limits       [OPEN M6]
        |
        `-- uniform bound on D#                                 [CONDITIONAL]
            |
            +-- backward record lemma                           [PROVED]
            |
            `-- Marked Backward Transition Theorem              [OPEN]
                |
                +-- canonical entropy-clock checkpoints         [OPEN M1/M4]
                +-- virtual hull with full partial marking      [OPEN M1]
                +-- recursive-carrier fullness                  [PROVED MODEL]
                +-- bounded access/translation incidence        [OPEN M1]
                +-- finite cell-tree extraction                 [OPEN M1]
                +-- analytic prime-end/access realization       [OPEN M1]
                +-- finite-horizon psi-ql topology              [PARTLY PROVED]
                +-- selected fiber-product routing/degree       [OPEN]
                +-- local saturation / orbit admissibility      [OPEN M1]
                +-- finite-horizon analytic localization        [OPEN M1/M2]
                +-- active/corridor decomposition               [OPEN M1]
                +-- bounded interaction types modulo translation [PARTLY PROVED]
                +-- WAD corridor sandwich                       [PROVED]
                +-- marking/replica congestion calibration      [PROVED CONDITIONAL]
                +-- DL per-tile/total normalization              [IMPORTED]
                +-- bounded-terminal response calculus          [PROVED ABSTRACT]
                +-- fixed-electrode surface response            [PROVED]
                +-- WAD domination gives Loewner domination     [PROVED CONDITIONAL]
                +-- fixed-block spectral comparison             [PROVED NONUNIFORM]
                +-- future-closed port realization              [OPEN ANALYTIC]
                +-- Value-faithful ports or Value moments       [OPEN ANALYTIC]
                +-- lifted Value observability/rank criterion   [PROVED]
                +-- one primitive Value block contraction       [PROVED]
                +-- typed KKL Value incidence/eigenweights      [PROVED]
                +-- printed KKL clone equation counterexample   [PROVED NO-GO]
                +-- corrected fixed-clone theorem/eigenvectors  [PROVED INTERNAL]
                +-- fixed-clone complete-block contraction      [PROVED]
                +-- bounded-dimension clone entropy gap         [PROVED]
                +-- exact corridor-to-clone graph criterion     [PROVED]
                +-- bounded endpoint-defect absorption          [PROVED]
                +-- finite corridor union under cross section   [PROVED]
                +-- cross section iff active quotient acyclic   [PROVED]
                +-- delay-robust clone primitivity witness      [PROVED]
                +-- finite-state graph corridor certificate     [PROVED]
                +-- conditional KKL Value corollary             [PROVED CONDITIONAL]
                +-- virtual corridor transition graph           [OPEN ANALYTIC]
                +-- virtual reduced-clone realization           [OPEN ANALYTIC]
                +-- framed-return spectral invariance           [PROVED]
                +-- nonzero irreducible entropy dichotomy       [PROVED]
                +-- extinction/shear normal form                [PROVED]
                +-- finite Boolean-support pumping              [PROVED]
                +-- future-equivalence/counter/stack no-go      [PROVED]
                +-- projected-memory pumping obstruction        [PROVED]
                +-- virtual source core/WAD cocycle             [OPEN ANALYTIC]
                +-- Markov-signature automaton criterion        [PROVED ABSTRACT]
                +-- WAD transport-quotient criterion            [PROVED ABSTRACT]
                +-- WAD future-observability criterion          [PROVED ABSTRACT]
                +-- uniform virtual counter/stack follower      [OPEN ANALYTIC]
                +-- uniform core/WAD module dimensions          [OPEN ANALYTIC]
                +-- memory-safe checkpoint/pumping compilation  [OPEN ANALYTIC]
                +-- virtual source-faithful support automaton   [OPEN ANALYTIC]
                +-- virtual transfer/shear trichotomy           [OPEN ANALYTIC]
                +-- KKL large-width occupancy trichotomy        [IMPORTED]
                +-- access-complete limb-tree interval bound    [PROVED]
                +-- abstract Section-4 static trichotomy        [PROVED CONDITIONAL]
                +-- virtual Section-4 interface                 [OPEN ANALYTIC]
                +-- KKL tame amplification in native category  [IMPORTED]
                +-- critical-encounter/marking/Value reductions [PROVED]
                +-- conditional virtual tame transfer           [PROVED CONDITIONAL]
                +-- virtual tame full-return closure            [OPEN ANALYTIC]
                +-- KKL Wave amplification in native category  [OPEN SOURCE-STATED]
                +-- bounded-visits interval-growth repair       [OPEN SOURCE GAP]
                +-- stationary proper-path/lamination repair    [OPEN SOURCE GAP]
                +-- complete Wave finite-horizon bound          [PROVED CONDITIONAL]
                +-- single degree-two fast-forward no-go        [PROVED NO-GO]
                +-- simultaneous inverse-tree fan saturation    [PROVED]
                +-- forward-full-hull component no-go           [PROVED NO-GO]
                +-- connected-seed component saturation         [PROVED]
                +-- finite obstacle forward closure             [PROVED]
                +-- exact fan ribbon pullback                   [PROVED]
                +-- degree-weighted endpoint-birth ledger       [PROVED]
                +-- local carrier-equality no-birth criterion   [PROVED]
                +-- one-root pullback-forest equivalence        [PROVED]
                +-- virtual root component separation           [OPEN TOPOLOGICAL]
                +-- KKL native interval pullback/properness     [IMPORTED]
                +-- attachment-support reduction               [PROVED]
                +-- corridor attachment transport              [PROVED]
                +-- univalent complete-pair transport           [PROVED]
                +-- anchor underdetermination no-go             [PROVED]
                +-- finite attachment-orbit closure             [PROVED]
                +-- minimal typed proof-use inventory            [PROVED]
                +-- finite geometric saturation                 [PROVED]
                +-- least-connected-carrier no-go               [PROVED]
                +-- quadratic protected-access collision        [PROVED NO-GO]
                +-- canonical virtual interface carrier         [OPEN]
                +-- virtual carrier-pair naturality             [OPEN]
                +-- virtual attachment-free anchor              [OPEN]
                +-- virtual bounded attachment support          [OPEN ANALYTIC]
                +-- conditional finite-horizon Wave transfer    [PROVED CONDITIONAL]
                +-- virtual long-iterate wave closure           [OPEN ANALYTIC]
                +-- branch-parameter quantifier assembly        [PROVED]
                +-- complete-block contraction reduction        [PROVED ABSTRACT]
                +-- response-calibrated block contraction       [OPEN ANALYTIC]
                +-- complexity amortization                     [OPEN M2/M3]
                +-- ql/WAD/sectorial/virtual calibration        [OPEN M2]
                +-- balance/bottleneck or homogeneous dynamics  [OPEN M2]
                +-- forward contraction or backward expansion   [OPEN M2]
                +-- admissible chart-cycle expansion audit      [OPEN M2]
                +-- absolute/relative antirenormalization error [OPEN M3]
                +-- discounted entropy error charge             [OPEN ANALYTIC]
                +-- chart-cycle expansion audit                 [OPEN ANALYTIC]
                +-- entropy or full regularization dichotomy    [OPEN M4]
                `-- backward Wave/Wanderers transport           [OPEN M5]
```

The same open branch is now packaged, without deleting any node, as:

```text
UNIVERSAL_PROTECTED_TOWER_CLOSURE (UPTCR)                        [OPEN]
|
+-- UPTCR-1 canonical protected carrier                         [OPEN H1]
+-- UPTCR-2 exact analytic realization                          [OPEN H1]
+-- UPTCR-3 uniformly finite Value-observable response state    [OPEN H2]
+-- UPTCR-4 backward transition and complete error charge       [OPEN MBTT]
+-- UPTCR-5 coercive marked compactness                         [OPEN H3]
`-- UPTCR-6 tower rigidity and connected parameter fiber        [OPEN H4]

UPTCR + Yoccoz + backward record
`-- MLC                                                        [PROVED IMPLICATION,
                                                                OPEN HYPOTHESIS]
```

The last arrow is `UPTCR_IMPLIES_MLC`; it is a proved conditional
implication. It is not a proof of UPTCR or MLC.

## 2. Claims proved in this package

| ID | Claim | Proof location |
|---|---|---|
| P1 | The KKL finite/infinite precedence gives an exhaustive, disjoint four-way partition of families. | `regime_and_hulls.md`, Proposition 2.1 |
| P2 | A uniformly bounded scalar cannot be universally additively comparable to inverse root modulus over unbounded satellite periods. | `master_transition.md`, Theorem 2.1 |
| P3 | A forward amplification lower bound alone does not imply boundedness. | `master_transition.md`, Proposition 3.1 |
| P4 | A backward amplification recurrence implies a uniform record bound along each tower. | `master_transition.md`, Lemma 7.1 |
| P5 | Under `H1`--`H4`, MLC follows. | `manuscript.md`, Theorem C |
| P6 | A quotient preserving \(N\) distinct labeled return accesses requires at least \(N\) target marks. | `virtual_block_quotient.md`, Theorem 2.2 |
| P7 | Short interactions in a translation corridor have a number of orbit types independent of corridor length. | `virtual_block_quotient.md`, Lemma 4.2 |
| P8 | Expanding positive chart covectors convert a vector transition inequality into the scalar backward recurrence needed by the record lemma. | `master_transition.md`, Lemma 5.1 |
| P8b | Monotone subadditive homogeneous chart gauges convert expanding nonlinear homogeneous transitions into the same backward scalar recurrence. | `master_transition.md`, Lemma 5.2 |
| P8c | Error-stable homogeneous gauges, including bottleneck minima, give the same recurrence without subadditivity. | `master_transition.md`, Lemma 5.3 |
| P9 | Under the nondegenerate/full and hyperbolic-complement hypotheses, proper holomorphic returns between hull complements act canonically as finite-degree coverings on prime-end circles. | `virtual_block_quotient.md`, Lemma 7.4 |
| P10 | Fullification preserves genuine forward invariance under a polynomial. | `virtual_block_quotient.md`, Lemma 7.1 |
| P11 | A full hull containing every critical value of a polynomial return has a full connected preimage and a proper complement return. | `virtual_block_quotient.md`, Lemma 7.2 |
| P12 | For the nondegenerate full-hull setup of Corollary 7.3/Lemma 7.4, the global complement return \(f^q\) has prime-end degree \(2^q\), so bounded-degree virtual renormalization requires selected pullback data. | `virtual_block_quotient.md`, Proposition 7.6 |
| P13 | Any proper factorization of a degree-two return has exactly one quadratic factor and all other factors conformal. | `virtual_block_quotient.md`, Lemma 7.7 |
| P14 | Quadratic pullback of a full continuum has a conformal two-component or quadratic one-component form according to whether it avoids or contains the critical value. | `virtual_block_quotient.md`, Lemma 7.8 |
| P15 | A finite inverse itinerary of nondegenerate full hulls with one critical target admits a simultaneous compatible Jordan-neighborhood factorization of total degree two. | `virtual_block_quotient.md`, Corollary 7.9, adapting `finite_horizon_inflation.md`, Lemma 10.1 |
| P17 | A genuine quadratic-like endpoint return canonically factors through proper intermediate preimage components with one quadratic step. | `virtual_block_quotient.md`, Lemma 8.3 |
| P18 | Every genuine all-horizon \(\psi\)-ql map has a depth-\(q\) truncation for each finite \(q\). | `finite_horizon_inflation.md`, Lemma 3.2 |
| P19 | A stage complement inclusion exists exactly when the stage marking maps into the next marking. | `finite_horizon_inflation.md`, Lemma 4.1 |
| P20 | The existence of a map between selected relative covers is governed by the fundamental-group subgroup criterion. | `finite_horizon_inflation.md`, Lemma 5.1 |
| P22 | Topological finite-horizon data do not control either natural inverse modulus, even for ordinary quadratic-like maps. | `finite_horizon_inflation.md`, Theorem 7.1 |
| P23 | Once a controlled local target collar embeds conformally into its inflation, target inverse annular modulus cannot increase. | `finite_horizon_inflation.md`, Proposition 8.2 |
| P24 | A finite inverse itinerary of nondegenerate full continua with separated obstacles, exactly one critical-value target, and every other target collar avoiding the critical value admits a qualitative locally saturated Jordan telescope with exactly one quadratic stage. | `finite_horizon_inflation.md`, Theorem 10.2 |
| P25 | For disjoint nondegenerate \(H,E\) with connected complement of their union, Jordan target collars recover the exact marked annular width with arbitrarily small error. | `marked_collar_calibration.md`, Theorem 2.1 and Proposition 2.2 |
| P26 | A translation-realized WAD decomposition satisfies \(Q\le W\le Q+4S+C\kappa\). | `corridor_network_calibration.md`, Theorem 4.1 |
| P27 | Raw unbounded marking complexity cannot have a positive coefficient in a uniformly bounded coercive potential. | `corridor_network_calibration.md`, Proposition 5.1 |
| P28 | Harmonic series width is not uniformly comparable to any fixed positive linear form on unrestricted branch widths. | `corridor_network_calibration.md`, Theorem 6.2 |
| P29 | Bounded-fanout harmonic transport is controlled, up to the fanout, by the minimum branch width. | `corridor_network_calibration.md`, Lemma 6.1 |
| P30 | The number of good translation classes is bounded by marked arc-support complexity divided by usable corridor length. | `corridor_network_calibration.md`, Lemma 9.1 |
| P31 | An \((n,p)\)-translation marking has exactly \(2p\) ideal labels per translation step, so longer corridors do not dilute unbounded \(p\). | `corridor_network_calibration.md`, Lemma 10.1 |
| P32 | A square-root chart loss is bounded by \(\delta x+O_\delta(1)\) for every chosen \(\delta>0\). | `neutral_transition_interface.md`, Lemma 4.1 |
| P33 | If total orbit width is \(\asymp rA\) and aggregate loss is \(O(r\sqrt A+r)\), its relative size is \(O(A^{-1/2}+A^{-1})\), independently of tile count. | `neutral_transition_interface.md`, Proposition 4.2 |
| P34 | If active width replicates as \(rD\) while standard width and topology grow as \(O(r)\), their relative contribution is \(O(1/D)\), uniformly in \(r\). | `corridor_network_calibration.md`, Lemma 11.1 |
| P35 | A finite recursive union of full branch continua attached along connected intersections is full. | `virtual_hull_realization.md`, Lemma 2.2 |
| P36 | An \(O(R)\)-occupancy carrier has \(\kappa=O(R)\) after access completeness and bounded translation/access incidence are assumed. | `virtual_hull_realization.md`, Proposition 3.2 |
| P37 | Distinct active WAD summands on disjoint support replicate their weights additively. | `virtual_hull_realization.md`, Lemma 4.1 |
| P38 | Finite topology does not imply replication: serial cells and isotopic returns have vanishing replication efficiency. | `virtual_hull_realization.md`, Proposition 4.3 |
| P39 | With marking count \(r_{\rm mark}\) and parallel count \(r_\parallel\), the relative corridor error is \(O(\rho_B/D)\), where \(\rho_B=r_{\rm mark}/r_\parallel\). | `corridor_network_calibration.md`, Corollary 12.1 |
| P40 | DL25's \(A_m=\ell_mK_F\) is a per-tile scale; total parallel width is \(\asymp r_mA_m\asymp K_F\). | `neutral_transition_interface.md`, Section 2 |
| P41 | Calibrating two coordinates to one common marked width transfers explicit two-sided bounds. | `neutral_transition_interface.md`, Lemma 5.1 |
| P42 | The entropy recurrence has an exact future-entropy-discounted error formula. | `entropy_and_cycle_bookkeeping.md`, Lemma 2.1 |
| P43 | A discounted error budget with coefficient \(\theta<1\) gives uniform contraction when accumulated entropy is bounded below. | `entropy_and_cycle_bookkeeping.md`, Theorem 3.1 |
| P44 | Positive accumulated entropy alone does not control an unweighted number of local errors. | `entropy_and_cycle_bookkeeping.md`, Proposition 4.1 |
| P45 | A common backward-expanding (respectively forward-contracting) chart gauge must expand (respectively contract) every admissible directed chart cycle; an identity cycle obstructs either strict calibration. | `entropy_and_cycle_bookkeeping.md`, Section 6 |
| P46 | A bounded-terminal response matrix adds under parallel gluing and transforms by Schur complement under serial elimination. | `network_response_state.md`, Propositions 3.1--3.2 |
| P47 | A forward upper transition with a strict error-stable scalar contraction yields an explicit backward amplification inequality. | `master_transition.md`, Lemma 5.4 |
| P48 | A complete grouped entropy-clock block with contraction factor \(\mu<1\) and output-relative error \(\delta<1-\mu\) yields backward factor \((1-\delta)/\mu>1\). | `block_contraction_program.md`, Theorem 4.1 |
| P49 | Every fixed finite-electrode surface has an exact positive-semidefinite response matrix with componentwise-constant kernel and a conductance-graph representation. | `bc1_finite_port_response.md`, Theorem 2.1 |
| P50 | A port quotient that merges electrodes which later separate loses their differential response and is not a sufficient block state. | `bc1_finite_port_response.md`, Proposition 3.3 |
| P51 | Under an itinerary-faithful port assignment, KKL WAD domination implies Loewner domination after intermediate ports are eliminated. | `bc1_finite_port_response.md`, Theorem 5.1 |
| P52 | Exact surface and WAD responses on one finite terminal space are two-sided comparable precisely when their kernels agree; the comparison constants are generalized eigenvalues and need not be uniform. | `bc1_finite_port_response.md`, Proposition 6.1 |
| P53 | Total WAD weight, terminal response, and unweighted port data do not determine KKL Value after response compression merges support classes with different Value coefficients; any additional aggregate coordinate needs a separate proof that it recovers the lost distribution. | `bc1_finite_port_response.md`, Theorem 7.1 |
| P54 | For a finite lifted linear WAD state, a family of valuations is observable exactly when its coefficient rows lie in the state row space; the rank defect is the exact minimum number of additional moments. | `bc2_value_feature.md`, Theorem 3.1 and Corollary 3.2 |
| P55 | One retained scalar Value coordinate closes the homogeneous algebra of one source-licensed KKL primitive pullback block, with the exact additive error \(V_F(E)\). | `bc2_value_feature.md`, Theorem 5.1 |
| P56 | The internally corrected literal-clone theorem gives \(\lambda_n^n\to\rho(H(1))>1\) for a fixed typed datum, hence every sufficiently long source-licensed complete cloned block has uniform strict Value contraction. | `bc2_value_feature.md`, Corollary 6.1 |
| P57 | Every irreducible non-permutation integer transition graph of dimension at most \(d\) has Perron root at least \(2^{1/d}\). | `virtual_clone_entropy.md`, Theorem 3.1 |
| P58 | A source-licensed corrected clone with gate dimension at most \(d\), maximum first-return length \(K\le N\), and delay \(n>N\) has multiplier at least \(2^{n/[d(n+K)]}>2^{1/(2d)}\) and complete-block Value factor \(<2^{-1/(2d)}\). | `virtual_clone_entropy.md`, Theorem 4.1 |
| P59 | In the exact bounded-reduced-entropy branch with \(n\ge N\), both reduced Perron rays have uniformly bounded coordinate ratios and the clone-layer factor is at most \(H\); one-sided perturbation domination alone does not imply this. | `virtual_clone_entropy.md`, Theorem 5.2 |
| P60 | Reduced dimension cannot be omitted: directed cycles with one self-loop are primitive while their Perron roots tend to \(1\) as dimension grows. | `virtual_clone_entropy.md`, Proposition 8.1 |
| P61 | A weighted \((1-\epsilon)\)-retained transition satisfying its own corrected equation has multiplier at least \(((1-\epsilon)2^{1/d})^{n/(n+K)}\), and keeps strict total expansion when \(\epsilon<1-2^{-1/d}\). | `virtual_clone_entropy.md`, Theorem 4.2 |
| P62 | A finite directed multigraph is a KKL cross-section clone exactly when its corridor has only the declared label-preserving chain edges, all other incidences occur at its endpoints, and deletion/identification gives the stated cross-sectional reduced quotient. | `corridor_clone_criterion.md`, Theorem 3.2 |
| P63 | Entry and exit defects confined to fixed endpoint windows can be absorbed into the active graph without increasing reduced cross-section cardinality, provided the central reduced quotient retains the cross-section property. | `corridor_clone_criterion.md`, Lemma 4.2 |
| P64 | Equal-length disjoint exact corridors combine into one clone when their union is a cross section of the combined reduced quotient; its dimension is the sum of their cross-section sizes. | `corridor_clone_criterion.md`, Proposition 5.1 |
| P65 | A finite gate \(E\) meets every sufficiently long directed walk exactly when the induced active complement is acyclic; an avoiding walk then has at most \(|V\setminus E|-1\) edges. | `dynamical_corridor_certificate.md`, Lemma 2.1 |
| P66 | Cloning a nonempty cross section preserves strong connectivity when the base is strongly connected and every gate vertex lies on a positive-length closed walk. | `dynamical_corridor_certificate.md`, Lemma 3.1 |
| P67 | Two closed walks with equal gate-passage count and lengths differing by one certify primitivity of every clone delay. | `dynamical_corridor_certificate.md`, Theorem 3.2 |
| P68 | A primitive base need not have primitive clones: the bouquet of directed \(3\)- and \(5\)-cycles has a period-two length-one clone. | `dynamical_corridor_certificate.md`, Proposition 3.3 |
| P69 | The complete finite-state corridor certificate implies an exact primitive bounded-dimensional clone graph with uniform gate and label depth. | `dynamical_corridor_certificate.md`, Theorem 4.1 |
| P70 | A source-column cocycle of permutation layer transfers has an identity interior gauge after transporting labels; clone purity remains separate. | `corridor_entropy_shear_dichotomy.md`, Lemma 2.1 |
| P71 | A nonzero irreducible nonnegative integer \(d\times d\) transfer is either one directed-cycle permutation or has Perron root at least \(2^{1/d}\). | `corridor_entropy_shear_dichotomy.md`, Theorem 3.1 |
| P72 | A nonnegative integer matrix of spectral radius at most one has only cycle/zero Frobenius diagonal blocks and polynomial feed-forward growth; without a recurrent cycle it is nilpotent. | `corridor_entropy_shear_dichotomy.md`, Theorem 4.1 |
| P73 | Removing \(q\) non-permutation layers leaves at most \(q+1\) identity-gauged interior runs; bounded local type count does not bound \(q\), and exact corridor purity is not implied. | `corridor_entropy_shear_dichotomy.md`, Lemma 5.1 |
| P74 | Constant unipotent shear has one local type and zero exponential entropy but unbounded linear transport, refuting an exhaustive exact-clone/positive-entropy dichotomy. | `corridor_entropy_shear_dichotomy.md`, Example 4.2 |
| P75 | Nonnegative matrix support is functorial under multiplication via Boolean support product. | `corridor_support_automaton.md`, Lemma 2.1 |
| P76 | An \(s\)-state automaton with \(d\)-dimensional nonnegative transfers reduces every accepted path to a support skeleton of length at most \(s2^{d^2}-1\), with every erased segment retained in its ordered, prefix-face-dependent insertion history. | `corridor_support_automaton.md`, Theorem 3.1 |
| P77 | If the automaton language contains a product with a cyclic non-simple support SCC, it contains one of length at most \(s2^{d^2}-1\), and the displayed square matrix has Perron root at least \(2^{1/d}\); dynamical entropy additionally needs a framed repeatable return. | `corridor_support_automaton.md`, Theorem 4.1 and Corollary 4.2 |
| P78 | Exact deterministic automaton size is the index of right future equivalence for the fully decorated dynamical language. | `virtual_language_memory.md`, Theorem 2.1 |
| P79 | Fixed local alphabet and finite horizon do not bound faithful automaton size: copy languages have exponential index and exact exits have linear index. | `virtual_language_memory.md`, Propositions 3.1--3.2 |
| P80 | Universal finite memory \(R\) and mode set \(M\) give an exact automaton with at most \(|M|\sum_{j=0}^R|\mathcal A|^j\) states. | `virtual_language_memory.md`, Theorem 4.1 |
| P81 | Loop deletion preserves a counter endpoint exactly on the reachable fiber where the endpoint predicate has equal values with and without the loop increment; zero increment or fiber invariance is sufficient, not pathwise necessary. | `virtual_language_memory.md`, Lemma 5.1 |
| P82 | Fixed finite control and bounded additive counter increments yield only polynomially many configurations after \(m\) symbols, so counters cannot conceal arbitrary exponential future memory. | `virtual_language_memory.md`, Proposition 5.3 |
| P83 | Under the full source \(\psi\)-ql hypotheses, a literal-clone graph with typed core incidence and coefficientwise WAD domination \(Y\le(f^r)^*X+E\), where the actual pullback exponent \(r\) is at least the clone delay \(n\), activates the corrected internal clone equation and yields the stated KKL Value contraction; its outgoing error is separate. | `dynamical_corridor_certificate.md`, Corollary 4.2 |
| P84 | A framed closed source-column return changes by similarity under base relabeling, while an open transfer can change spectral radius under target relabeling. | `transfer_convention_and_frame.md`, Lemma 4.1 |
| P85 | Reverse-copy prefixes have exponential DFA index but admit finite control plus one finite-alphabet stack; actual LIFO antirenormalization remains open. | `virtual_language_memory.md`, Proposition 3.3 |
| P86 | A resolved source-locked presentation has a canonical minimal future-equivalence quotient preserving its decorated trace language and labeled cocycle. | `virtual_support_automaton_construction.md`, Theorem 3.2 |
| P87 | After exact memory compilation, a bounded Markov-complete marked-cell signature gives a uniformly finite source-faithful transfer automaton at the compiled trace resolution; it does not bound the transfer-module dimensions. | `virtual_support_automaton_construction.md`, Theorems 4.1 and 5.1 |
| P88 | For a fixed complete observation family, a WAD compression is output-exact exactly when every declared future observation factors through it; partition classes must have identical profiles. | `virtual_support_automaton_construction.md`, Lemma 6.1 and Theorem 6.3 |
| P89 | A checkpoint-pure run admits exact parametric macro compression at checkpoints, but the macro does not preserve layerwise prefixes. | `virtual_support_automaton_construction.md`, Proposition 5.2 |
| P90 | Zero counter increment plus identity stack action preserves the augmented configuration of a specified loop; it neither produces a safe pigeonhole repetition nor deletes that loop's emitted numerical and proof-used records. | `virtual_support_automaton_construction.md`, Lemma 5.3 |
| P91 | Unbounded discrete counter values or finite stack words are not precompact, and multiplying them by a compact geometric state does not restore precompactness. | `virtual_language_memory.md`, Proposition 6.1 |
| P92 | For raw KKL source-to-target incidence \(N\), project source-column transport is \(B=N^{\mathsf T}\); KKL \(v,w\) are project-left/project-right and Value uses \(v^2w\), without relying on the ambiguous \(T_F\) label. | `kkl_transfer_orientation_audit.md`, Sections 1 and 5 |
| P93 | Projecting counters or a stack away does not license accepted-word pumping: repeated finite-control/support pairs may all change exact memory. | `virtual_language_memory.md`, Section 5 |
| P94 | A compressed WAD state transports compositionally exactly when every enabled branch satisfies \(P_{\rm out}R_\gamma=\bar R_\gamma P_{\rm in}\); output observability alone is insufficient. | `virtual_support_automaton_construction.md`, Lemma 6.2 |
| P95 | The printed KKL \(+\lambda^k\) finite-\(n\) clone equation fails under the literal definitions on an explicit primitive three-vertex cross-section graph; the limiting theorem is instead repaired internally by P56 and the corrected literal-graph derivation. | `kkl_transfer_orientation_audit.md`, Section 6.1 |
| P96 | For every \(B,M\), KKL Proposition 3.7 and Remark 4.14 give a threshold \(A(B,M)\) for the static amplification/tame/controllable-wave trichotomy inside the full KKL \(\psi\)-ql category under per-limb occupancy \(B\); they do not close either the tame or wave branch. | `kkl_virtual_occupancy_source_audit.md`, Theorem 4.1 |
| P97 | A reduced anchored limb tree spanning \(m\) non-anchor access-complete atoms has at most \(4m-2\) oriented tree sides and, charging at most two local decorations at every prescribed vertex including the anchor, at most \(6m\) ideal intervals; selected-component occupancy alone cannot bound this when extra access atoms are unbounded. | `virtual_limb_marking_bound.md`, Theorem 3.2 and Proposition 4.1 |
| P98 | Invoking the static split at the wave-selector parameter, applying a same-parameter tame closure, and taking the maximum of every displayed threshold composes the three virtual branches; two unrelated branch-input parameters do not compose without a common-input or monotonicity theorem. | `virtual_branch_assembly.md`, Theorem 4.1 and Proposition 5.1 |
| P99 | KKL Proposition 3.8 closes the \(P\)-tame branch in the full parabolically \(B\)-bounded prime primitive \(\psi\)-ql category after its high-type and successor-width thresholds; it does not realize those hypotheses for a virtual hull. | `virtual_tame_full_return.md`, Section 3 |
| P100 | KKL Proposition 3.9 states the controllable-Wave amplification theorem in the native category, but this project does not certify the v1 proof: the bounded-visits interval-growth implication and the stationary proper-path/measurable-lamination extraction remain open. | `direct_decoration_wave_proof_use_ledger.md`, Sections 3.2--3.4; `pql_iterate_filled_graph_naturality.md`, Sections 5--6 |
| P101 | A static datum satisfying `S4-AC`--`S4-END` and \(D\ge\max\{1,5E_X(B)\}\) is \(M\)-amplifying, \(M\)-tame, or carries an \(M\)-wide controllable wave; realization of the interface is separate. | `virtual_section4_interface.md`, Theorem 7.1 |
| P102 | A selected proper telescope with \(m_I\) quadratic stages and all other stages conformal has total degree \(2^{m_I}\). | `virtual_tame_full_return.md`, Lemma 7.1 |
| P103 | Linear complete-marking growth is absorbed by a WAD lower bound linear in the return period, with error \(O(1/W_R)\) independent of that period. | `virtual_tame_full_return.md`, Lemma 7.2 |
| P104 | Near-self-domination contradicts strict Value contraction whenever \(C_V\delta<1-\mu^{-1}\). | `virtual_tame_full_return.md`, Lemma 7.3 |
| P105 | Under `VR0`--`VR5` and `VR7`, the same-parameter implication \(\operatorname{Tame}_P\Rightarrow\operatorname{Amp}_P\) holds in the realized KKL coordinate; `VR6` and all geometric realization clauses remain open. | `virtual_tame_full_return.md`, Theorem 7.4 |
| P106 | Conjugating a reduced rotation \(a/q\) to translation by one through multiplication by \(a^{-1}\bmod q\) generally destroys cyclic order, so a geometric accelerated corridor is required. | `virtual_tame_full_return.md`, Section 9.2 |
| P107 | Conditional on the separately open bounded-visits interval-growth implication, every pullback in the KKL Wave terminality program lies within the conservative horizon \(H_B(q)=(216B^2+1)(q+B+4)\). | `virtual_long_iterate_wave.md`, Proposition 6.1; `direct_decoration_wave_proof_use_ledger.md`, Section 3.2 |
| P108 | One selected proper long-return component of total degree two cannot realize the terminal degree-\(2^L\) fan used by KKL when \(L\ge2\). | `virtual_long_iterate_wave.md`, Proposition 5.1 |
| P109 | Conditional also on the two open native Wave proof repairs, a virtual block satisfying `WA1`--`WA12` through \(H_B(q)\), including the degree-one central corridor and bounded auxiliary marked fan, admits the stated synchronized selectors; realizing those axioms remains open. | `virtual_long_iterate_wave.md`, Theorem 8.2; `direct_decoration_wave_proof_use_ledger.md`, Section 3; `pql_iterate_filled_graph_naturality.md`, Section 6 |
| P110 | A finite full inverse-component tree with separated compact obstacles admits one simultaneous system of disjoint proper Jordan pullback sheets; each branch has degree \(2^m\) for its critical-encounter count \(m\), and branches \(m=0,\ldots,M\) have total degree \(2^{M+1}-1\). | `selected_marked_fast_forward_fan.md`, Theorem 5.1 and Corollary 6.1 |
| P111 | Fullness, critical-orbit inclusion, and surjective forward invariance do not imply pullback-component saturation: under \(z^2\), the right half-disk maps onto the unit disk but is not its unique pullback component. | `selected_marked_fast_forward_fan.md`, Proposition 3.3 |
| P112 | A finite forward-coherent connected seed forest has a unique canonical pullback-component saturation relative to its filled root; with sibling separation it is a disjoint full inverse forest with branch degree \(2^m\). | `saturated_virtual_seed_forest.md`, Theorem 3.1 and Propositions 3.2--3.3 |
| P113 | Finite compact obstacles disjoint from a saturated forest admit simultaneous separated neighborhoods; forward closure of the obstacle-or-carrier sets gives the exact stage complement inclusions. | `saturated_virtual_seed_forest.md`, Propositions 5.2--5.3 |
| P114 | On the simultaneous Jordan fan, a finite root endpoint marking pulls back functorially with cyclic order and exact cardinality; a dyadic fan has \(|P_r|(2^{M+1}-1)\) endpoints and intervals, conditional on root future completeness. | `saturated_virtual_seed_forest.md`, Theorem 6.2 and Corollary 6.3 |
| P115 | Intermediate endpoint births satisfy \(p_0=D_{0,N-1}p_N+\sum_jD_{0,j-1}b_j\). Bounded births per degree-one corridor stage can grow linearly, whereas births confined to a bounded terminal quadratic window have a period-independent geometric-sum bound. | `marked_endpoint_birth_ledger.md`, Theorem 3.1 and Proposition 5.1 |
| P116 | On a degree-one marked interval, no attached component in the pulled carrier plus one interval lift and conformal endpoint lifts imply zero genuine endpoint births. | `marked_endpoint_birth_ledger.md`, Proposition 7.1 |
| P117 | In KKL's native parabolically bounded Hubbard-tree category, Proposition 6.5 identifies the immersion pullback of an ideal interval with its inverse image plus the ideal boundaries of attached components of \(\mathcal T'\setminus\mathcal T\), while Proposition 6.7 proves \(\mathcal T'\cap\mathcal L_{[B,q-B-2]}=\mathcal T\cap\mathcal L_{[B,q-B-2]}\), so no pulled excess meets the relevant central intervals and the interval action is proper there.  It does not prove global equality \(\mathcal T'=\mathcal T\). | `kkl_translation_no_birth_source_audit.md`, Section 2 |
| P118 | Under an exact KKL-form interval pullback description, births vanish off the attachment support; if all support and births lie in a terminal depth-\(M\), degree-at-most-two window with at most \(b_*\) births per stage, then \(\mathfrak b_0\le b_*(2^M-1)\). | `kkl_translation_no_birth_source_audit.md`, Theorem 4.1 |
| P119 | The virtual Wave branch still needs an exact interval pullback description, empty central attachment support, bounded defect-window attachments, access/cyclic-order preservation, and proper or end-proper relative-cover lifts. This is an open realization premise, not a consequence of P112. | `kkl_translation_no_birth_source_audit.md`, Section 5 |
| P120 | A saturated finite carrier forest is equivalently one full root continuum together with the routed components of all its finite iterated pullbacks containing the whole required packages; same-depth sheet separation is exactly separation in this component partition. | `root_pullback_virtual_carrier.md`, Theorem 3.1 |
| P121 | For a quadratic polynomial, a full target carrier has one degree-two pullback component exactly when it contains the critical value and two degree-one components exactly when it avoids the critical value; this is an exact corridor compatibility test. | `root_pullback_virtual_carrier.md`, Proposition 4.1 and Corollary 4.2 |
| P122 | Root enlargement can only merge iterated-pullback component classes. Thus all future-required root data and all selected-sheet separation must be realized simultaneously by the still-open Virtual Root-Carrier Certificate. | `root_pullback_virtual_carrier.md`, Proposition 5.2 and Section 7 |
| P123 | A commuting orientation-preserving homeomorphism of access-complete marked carrier pairs bijects their excess components, attachment intervals, and proof-used prime-end sides. Hence attachment support transports exactly through a marked-pair natural degree-one corridor. | `corridor_attachment_transport.md`, Theorem 4.1 |
| P124 | Along such a corridor, one attachment-free anchor forces every central stage to be attachment-free; a persistent supported defect produces at least linear endpoint charge whenever it exposes a genuine proof-used endpoint at each stage. | `corridor_attachment_transport.md`, Corollaries 4.2--4.3 |
| P125 | Degree-one root routing controls only the selected polynomial carriers. It does not construct a commuting homeomorphism of the pulled/immersed carrier pairs or its prime-end extension. Virtual pair naturality and an attachment-free anchor remain open. | `corridor_attachment_transport.md`, Sections 5--6 |
| P126 | Transporting one actual marked anchor pair in its entirety through critical-value-free conformal corridor branches produces commuting carrier-pair squares, equivariant package/obstacle ledgers, and orientation-preserving prime-end marking maps without Euclidean boundary local connectivity. | `virtual_corridor_pair_naturality.md`, Theorem 4.1 |
| P127 | Dudko's published package, connectedness, partial-orbit, and degree-one selected-dynamics data do not force anchor equality: an interval and an interval embedded in a triod have the same required package and selected dynamics, while only the triod pair has attached excess. | `virtual_corridor_pair_naturality.md`, Proposition 5.1 |
| P128 | An inflationary monotone completion rule on a finite resolved carrier has a least finite attachment-orbit fixed point, functorial under conjugate corridor maps. Every sheet, critical-word, obstacle, access, or localization collision in that least closure persists in all monotone attachment-complete enlargements. | `virtual_corridor_pair_naturality.md`, Theorem 6.1 and Corollary 6.3 |
| P129 | A finite proof-use ledger has a unique minimal typed inventory containing every component, orbit index, access, obstacle, return word, curve family, and intervening transport stage read by the proof. This inventories required objects but constructs no connected carrier. | `canonical_virtual_interface_carrier.md`, Proposition 3.1 |
| P130 | On a fixed finite implication-complete and implication-sound resolved universe, monotone geometric completion has one order-independent least fixed point and agrees with its cell quotient. | `canonical_virtual_interface_carrier.md`, Theorem 4.1 and Proposition 4.2 |
| P131 | Two prescribed points have no least connected full planar carrier: the upper and lower semicircle carriers intersect only in the disconnected package. A regulated connector datum is therefore unavoidable. | `canonical_virtual_interface_carrier.md`, Theorem 5.1 and Corollary 5.2 |
| P132 | On an explicit critical-value-free branch of \(z^2\), the first pulled excess is an upper half-disk over the immersed interval and has a complete zero-critical itinerary, but every monotone absorption erases a protected upper prime-end access. The replacement invariant retains attachment traces and protected-access survival maps. | `canonical_virtual_interface_carrier.md`, Proposition 6.1, Theorem 6.2, and Section 7 |
| P133 | Nested nonempty compact sets with singleton intersection have diameters tending to zero. Connectedness is additionally required when the sets are to form a connected relative-neighborhood basis. | `mlc_closure_proposition.md`, Lemma 7.1 |
| P134 | If all six clauses of UPTCR hold, the backward-record lemma bounds the calibrated tower, coercivity supplies marked compactness, rigidity makes the full combinatorial fiber a singleton, and the connected relative parapuzzle neighborhoods shrink; with Yoccoz's complementary theorem, MLC follows. | `mlc_closure_proposition.md`, Theorem 7.2 |
| P135 | “Exactly one degree-two stage” is valid only on the selected quadratic return spine. A complete Wave horizon also needs the bounded auxiliary critical-word fan with branch degrees \(2^m\); a lone degree-two component is insufficient. | `uptcr_cross_validation.md`, CV-1 |
| P136 | A bounded defect window does not make a nonzero protected collision admissible. The replacement local model itself must have zero sheet, critical, obstacle, access, and localization collision on its protected core before its cost is charged. | `uptcr_cross_validation.md`, CV-2 |
| P137 | With the selected-spine/fan, zero-collision, inclusive-route, global-conjugacy, affine-normalization, and relative-neighborhood corrections made explicit, UPTCR still conditionally implies MLC; current sources do not prove UPTCR-1. | `uptcr_cross_validation.md`, Theorem 4.1 and Section 5 |
| P138 | A finite protected ribbon-routing certificate has an actual compact connected full carrier with singleton attachment traces, injective cyclic-order-preserving prime-end crosscut-chain survival, and exact univalent naturality; no local connectivity of the atoms is required. | `protected_regulated_connector.md`, Theorem 4.3 and Proposition 5.1 |
| P139 | A monotone semiconjugacy and a regulated tree in a locally connected combinatorial model define a canonical connected full lamination-lifted carrier, but connectedness and forward coherence do not imply protected-collar avoidance or iterated component routing. | `protected_regulated_connector.md`, Proposition 7.1 |
| P140 | The first live UPTCR-1 input is the Virtual Protected Routing Certificate: the actual lamination-lifted or puzzle-cell tree must avoid every protected collar, realize every package route, sheet, and critical word, close the obstacle/localization audit, and control future access incidence. | `protected_regulated_connector.md`, Section 8 |
| P141 | After the finite future-complete collars, obstacles, critical exclusion, localization boundary, and root-shadow atoms are frozen, a protected connector exists exactly when one component of their complement has simultaneous singleton ports to all atoms. | `virtual_protected_routing_domain.md`, Theorem 4.1 |
| P142 | The first collar or obstacle that separates two required port classes is monotone-unrepairable inside the current localization: every connected connector joining them must meet the forbidden set. | `virtual_protected_routing_domain.md`, Corollary 4.2 |
| P143 | Dudko's public connected-hull data and KKL's native primitive tree do not prove that an actual virtual-Molecule block has the common free component. This exact dynamical assertion is `VIRTUAL_COMMON_FREE_COMPONENT`. | `virtual_protected_routing_domain.md`, Sections 6--7 |
| P144 | A finite family of pairwise disjoint full continua compactly contained in a Jordan disk has connected common complement. Therefore a future-complete augmented-atom packet with explicit surviving free ports implies `VIRTUAL_COMMON_FREE_COMPONENT` and supplies a protected connector. | `virtual_common_free_component.md`, Lemmas 4.1--4.2 and Theorem 4.3 |
| P145 | A nonzero augmented-packet collision refutes only that sufficient packet construction. It refutes `VIRTUAL_COMMON_FREE_COMPONENT` only when an actual separator tuple for the original frozen free domain is also proved. | `virtual_common_free_component.md`, Section 5 |
| P146 | The public connected-hull data do not determine `VIRTUAL_COMMON_FREE_COMPONENT`: two explicit frozen routing extensions have the same atoms, connected full carrier, and package dynamics, while a separating annulus makes only one extension fail. | `virtual_common_free_component.md`, Proposition 7.1 |
| P147 | For a fixed finite typed assignment, fullification is an order-independent closure. Completed-packet mergers, localization escapes, and empty original-atom exposure loci persist under monotone enlargement with fixed labels; individual unprotected access arcs can always be truncated to a pairwise disjoint simultaneous family. | `augmented_packet_closure_audit.md`, Theorem 7.1 |
| P148 | For a fixed finite Wave-horizon dependency graph, reachability from the complete proof-use seed set is the unique least inventory. Under horizon extension it is monotone, and its old-stage slice is stable exactly when no extended seed reaches an omitted old record. | `vaapc_inventory_source_audit.md`, Theorem 4.1 |
| P149 | Dudko's public virtual-Molecule paragraph does not instantiate `VAAPC-I`: the first missing datum is the stopping horizon for the “appropriate number” of first returns. KKL's native inventory cannot be copied without a typed bridge preserving components, dependencies, branches, critical words, sheets, and proof-used prime ends. | `vaapc_inventory_source_audit.md`, Sections 7--8 |
| P150 | Every finite Kahn iterate has one connected full complementary equalizer.  For one fixed KL-eligible seed and every source tile \(a\), oriented annular degree \(+1\) identifies the pullback of its target tile \(j_\iota(a)\) with the connected source universal-cover tile after compatible lifted basepoints fix the deck phase; distinct source labels over one target remain distinct.  **Conditional on a separately supplied annular covering/embedding factorization** \(A_s\xrightarrow qP\xrightarrow eA_t\) with \(eq=\iota\), exact base change yields a connected resolved intermediate.  This family-valued interior theorem neither identifies the canonical infinite sheet-resolution factorization with the whole actual KL tile nor constructs any resolved ideal boundary. | `kahn_iterate_complementary_component_alignment.md`, Theorems 4.1, 5.1, 6.1, and 6.2; scope correction in `resolved_intermediate_relative_ideal_boundary.md`, Sections 3 and 8 |
| P151 | For a typed annular factorization \(A_s\xrightarrow qP\xrightarrow eA_t\) with \(eq=\iota\) and \(\iota_*=\mathrm{id}_{\mathbb Z}\), \(G=\pi_1(P)\) splits as \(G=N\rtimes H\), where \(H=q_*\pi_1(A_s)\) and \(N=\ker e_*\); after tilewise pullback, \(q_a:\mathcal E_a\to\mathcal R_a\) is the universal cover with deck group \(N\) and unchanged fibers.  A nonconstant universal cover, or any nonconstant deck-invariant composite, has no continuous point-valued extension at a deck-limit point.  Hence a nontrivial resolved cover has no full prime-end extension, while exact descent is available on a supplied invariant subset \(J\subset\partial\mathbb D\setminus\Lambda(N)\).  On the actual KL source tile, \(L_a\) extends at wrapping points \(\omega_\pm\); the based cover biholomorphism satisfies \(\overline\Phi_a(\omega_\pm)=\zeta_\pm\), and the resolved-source composite is \(K_a=L_a\Phi_a^{-1}=e_aq_a\).  Since \(\zeta_\pm\in\Lambda(N)\) for \(N\ne1\), every whole-actual-KL-tile covering/embedding factorization of this type is one-sheeted. | `resolved_intermediate_relative_ideal_boundary.md`, Lemma 4.1, Proposition 5.3, Theorem 6.2, Corollary 6.4, Theorems 7.1, 8.3, and 9.1 |
| P152 | Let \(\mathcal E\xrightarrow q\mathcal R\xrightarrow eT\) be a canonical resolved factorization with nontrivial universal-cover deck group \(N\).  No whole-tile comparison to the actual KL map can simultaneously be a based source-cover biholomorphism, conjugate the annular deck generators, separate the canonical target image, commute with the complete composites, and carry a wrapping point in \(\Lambda(N)\) to KL's named continuous wrapping vertex.  A deck sequence approaching that point would make the actual KL boundary value equal to every interior composite value.  The ordinary primitive canonical kernel is infinite, so its whole-tile option is excluded.  This no-go itself leaves restricted, relation-valued, retimed, and revised-localization branches open; P153 subsequently constructs and classifies the relation-valued interior branch for supplied same-source data. | `canonical_resolution_kl_tile_correspondence_no_go.md`, Theorem 5.1 and Corollaries 5.2--5.3 |
| P153 | For every supplied fixed labeled same-source canonical/KL tile datum, the based source-cover identification constructs a canonical span \(\mathcal R\leftarrow\mathcal E\to\widehat A_t^{\rm KL}\).  The tagged disjoint union of parametrized path pullbacks over all declared source labels is an étale family whose components are exactly the maximal parameter-compatible interior lifts and retain labels, resolved traces, sheets, and deck phases.  A nontrivial kernel forbids descent through \(q\); the two source-locked wrapping values, but not unproved values on the whole limit set, are common clusters of every resolved fiber orbit.  Kahn's annulus hypotheses alone do not bound the unscaled complete collar/target crossing-width difference, unchanged finite equalizer base change preserves every infinite fiber, and a revised localization is one-sheeted exactly under subgroup reflection after its lift condition is checked.  This constructs neither the aligned datum at every Wave stage nor KKL geometric-trace exhaustion, map properness on complete end-intervals, full standalone-tile boundary extension, uniform omitted-family control, final-root no-birth, or parameter realization. | `canonical_kl_restricted_interface_classification.md`, Propositions 4.2--4.3, Theorems 5.2 and 6.1, Propositions 7.1 and 8.1, and Section 9 |
| P154 | For one supplied full KL pseudo-piece inclusion immersion between conformal disks with KL's continuous full ideal extension, every maximal parametrized lift of a KKL proper target path has unique source ideal endpoints.  Exact endpoint naturality holds, including source ideal endpoints that map to an internal target break point.  The proof excludes source-interior clusters by maximality and makes each connected boundary cluster a singleton by bounded-holomorphic boundary uniqueness.  This proves path properness, not map properness on an ideal interval, geometric-trace exhaustion, uniqueness, or a Wave-uniform theorem. | `canonical_kl_geometric_trace_proper_end_response.md`, Theorem 3.1 |
| P155 | Parametrized pullback does not exhaust KKL's geometric restriction.  For the identity disk, a proper lollipop trace contains a loop-omitting proper path absent from the parametrized graph.  Separately, \(K(z)=\exp(-(1+z)/(1-z))\) gives one proper target diameter infinitely many proper source restrictions indexed by logarithmic deck phase.  Disjoint logarithmic rectangles prove only an unbounded raw sheetwise **interior-crossing** width, not a complete KKL-marked WAD/Value counterexample.  Hence neither unique proper restriction nor a uniform response follows from local univalence and sheet labels alone. | `canonical_kl_geometric_trace_proper_end_response.md`, Propositions 4.1, 5.1, and 6.1 |
| P156 | For any certified finite binder-aware source package, reachability from the atomic proof-use seeds is the unique least dependency-closed ledger.  SCC condensation is canonical, every fair work-list terminates at the same ledger, and a shortest seed path gives an omission certificate.  Under syntactic extension, exact stability requires all enlarged seeds to remain in the old image and no enlarged dependency edge to leave it.  This theorem compiles a supplied package; it does not construct the actual direct-decoration execution or prove geometric final-root no-birth. | `direct_decoration_wave_proof_use_ledger.md`, Definitions 5.1--5.2 and Theorems 8.2--8.3 |
| P157 | The active KKL Wave/Value/WAD/Wanderers source slice has 378 active reference occurrences, 18 citation occurrences, 161 distinct reference labels, and eight explicit outside-slice boundary labels.  Its D/W/T table is a target-first semantic schema map, not an atomic least ledger.  Source defects and missing formal-to-actual substitutions keep `DIRECT_DECORATION_WAVE_PROOF_USE_LEDGER` open. | `direct_decoration_wave_proof_use_ledger.md`, Sections 2--3 and Theorem 8.1 |
| P158 | Conditional on the stated Wanderers theorem, the localized KKL application is repaired by decomposing \(\widehat X_I=Z_I+R_I\), realizing \(Z_I\) by K06's actual itinerary foliations, and retaining both the Wanderers topology/degree constant and \(\|R_I\|\le C_0(b,L_1)\).  The resulting route-tail coefficient is \(4/m\), with additive terms independent of satellite period after \(b,L_1\) are fixed.  The Wanderers theorem's own omitted work-backwards proof remains open. | `direct_decoration_wave_proof_use_ledger.md`, Propositions 7.1--7.2 |
| P159 | Direct-decoration cylinders form a strict bigraded stage grid: geometric nesting \(Q_{wb}\hookrightarrow Q_w\) deletes the last symbol, while \(f^q:Q_{aw}\to Q_w\) deletes the first; the two operations commute on \(Q_{awb}\).  Every long edge resolves into \(q\) univalent unit stages.  Intrinsic KL path-space functoriality lifts the complete grid, including central/tile seams, to actual pseudo-pieces. | `direct_decoration_bigraded_kl_stage_grid.md`, Theorems 4.1 and 5.2 |
| P160 | The bigraded grid cannot be collapsed to one physical-inclusion chain: \(I_w\circ f^q|_{Q_{aw}}=I_{aw}\) would imply \(f^q=\mathrm{id}\) on an open cylinder, contradicting \(\deg f^q=2^q>1\).  The remaining PE-2 datum is a relation from every KKL geometric Wave trace to actual grid cells, path-space tiles, phases, and relative ends, compatible with both grid directions. | `direct_decoration_bigraded_kl_stage_grid.md`, Proposition 6.1 and Section 7 |

P5 and P134 are conditional implications. Neither is evidence that its
hypotheses hold.

Former claims `P16` and `P21` were withdrawn after the fiber-product audit. Proper
degrees of the stage maps do not automatically multiply through a correspondence:
selected fiber-product components can split or acquire projection multiplicity. The
selected-component routing and degree-preservation theorem is now an open dependency.

## 3. Forbidden dependency shortcuts

The following implications are invalid or unsupported.

| Shortcut | Reason |
|---|---|
| “Exactly one degree-two stage controls every branch in a complete Wave horizon.” | The condition belongs to the selected quadratic return spine. The proof-used auxiliary fan has branches of degree \(2^m\). |
| “A fatal protected collision is harmless inside a bounded defect window.” | A window bounds charge only after retiming or replacement produces a collision-free protected local model. |
| “The entropy, pseudo-Siegel, and transient/shear routes are disjoint.” | No disjointness theorem is available. Coverage requires at least one certified route; deterministic bookkeeping may impose a priority. |
| “The formal UPTCR proposition closes the six clauses it names.” | A named conjunction is not a proof. `UNIVERSAL_PROTECTED_TOWER_CLOSURE` is open and each clause retains its existing gate. |
| “A singleton combinatorial fiber alone proves local connectivity.” | One also needs nested compact connected relative neighborhoods whose intersection is exactly that fiber; UPTCR-6 states this separately. |
| “No invariant line fields may be invoked before constructing a controlled limit conjugacy.” | The argument applies only after UPTCR-5 and the finite-depth pullbacks in UPTCR-6 produce the limiting invariant Beltrami form. |
| “Pseudo-Siegel regularization gives a bounded scalar comparable to every satellite root width.” | Contradicted by P2/BLOT. |
| “Forward exponential amplification contradicts global geometry.” | No independent universal growth cap is imported; P3 shows the logical gap. |
| “The KKL four-family classification canonically decomposes every individual tower.” | The classification uses suprema over families; a stopping rule is additional. |
| “Partial invariance is enough for Wave/Wanderers.” | Every critical value and access used by each finite pullback chain must be marked and audited. |
| “An \(O(1)\) transition error is harmless.” | An unbounded block contains unboundedly many transitions; summability is required. |
| “A priori bounds imply MLC automatically.” | KKL26 separately requires bounded puzzle Teichmüller diameter for its rigidity theorem. |
| “The virtual hull has bounded WAD topology because it is connected.” | False for faithfully marked translation corridors: \(N\) distinct access labels require at least \(N\) target marks. What can be bounded is active interaction complexity modulo translation. |
| “A finite orbit marking automatically replaces global forward invariance.” | False unless the stage markings satisfy \(f(\Upsilon_j)\subset\Upsilon_{j+1}\), and even then the relative-cover lift and core properness require separate checks. |
| “Topological finite-horizon inflation gives a uniform extremal-width bound.” | False by P22: rescaled \(z^2\) restrictions have identical topology and arbitrarily varying width. |
| “Counting at most \(q\) iterates validates a proof on a depth-\(q\) truncation.” | False unless every curve pullback remains in the selected covering locus and meets only declared critical values/accesses. |
| “Raw marking complexity can be included in the positive cone state.” | False for a uniformly bounded potential when marking cardinality is unbounded; it must be amortized first. |
| “WAD chart changes automatically give nonnegative matrices.” | False for unbalanced serial branches: harmonic sum has no uniform positive linearization. |
| “Bounded fanout at each elementary scale is corridor-uniform.” | False if its comparison loss is repeated through an unbounded corridor; compress before applying it. |
| “Numerical tests validate MBTT.” | Computation cannot establish uniformity over arbitrary periods or all infinite towers. |

| “A finite tree of continua has \(O(r)\) complete marking complexity.” | False unless every dynamically required access and every KKL interval has bounded-incidence assignment to declared cells. |
| “\(r\) usable returns produce \(r\) active replicas.” | False: serial returns combine harmonically, while repeated isotopic returns do not add WAD weight. |
| “The total corridor weight is comparable to DL25's \(A_m\).” | Mis-scaled: \(A_m\) is per tile; total neutral width is \(\asymp r_mA_m\asymp K_F\). |
| “Matching access labels makes neutral and corridor widths comparable.” | False without controlled distortion, lift multiplicity, and preservation of parallel/serial orientation. |
| “Positive total entropy pays all block errors.” | False without the discounted or telescoping local charge of P42--P44. |
| “Expanding every chart edge separately gives a common Lyapunov gauge.” | False when an admissible directed chart cycle has neutral composition; every cycle must be audited. |
| “A forward upper transition can be read backward.” | False without a strict contracting gauge or an independent inverse/lower estimate; the identity map is an immediate counterexample. |
| “Raw cell count is a coercive homogeneous coordinate.” | False for the intended unbounded-period program; it is side/multiplicity data, while only response densities are scaled. |
| “Shrinking diameters of nested parameter pieces prove local connectivity.” | False unless the pieces supply connected relative neighborhoods forming a basis, or a theorem derives that basis from the fiber statement. |
| “Distinct translated drawings are distinct WAD coordinates.” | False unless their proper-arc classes remain distinct in the global marked surface. |

| “A finite response matrix automatically solves BC1.” | False: every individual electrode surface has a response, but future-closed port count and the generalized comparison eigenvalues must be uniform over all blocks. |
| “Present translation equivalence is a safe port quotient.” | False if a later pullback separates two presently merged accesses; their differential response has already been erased. |
| “Response and total WAD weight determine KKL Value.” | False by P53 whenever merged support classes have different Hubbard-tree coefficients. Use Value-faithful ports, coefficient comparison, or retained Value moments. |
| “Schur elimination applies to an arbitrary surface crosscut.” | False unless the crosscut is realized as an equipotential floating electrode or a gate-equilibration theorem compares the two variational problems. |
| “Primitive combinatorics give a uniform entropy gap.” | False when reduced graph dimension is unbounded; P60 gives primitive spectral radii tending to \(1\). |
| “A translation-like virtual corridor satisfies KKL's clone equation.” | Unsupported until its reduced graph, edge labels, finite-horizon WAD itineraries, and omitted critical branches are constructed. |
| “Collapsing a visible corridor automatically produces a KKL cross section.” | False: recurrence of the reduced quotient is independent of the local chain rule and must be proved; the distinguished chain edges must be deleted before label identification. |
| “A primitive reduced base has primitive clones for every corridor length.” | False by P68; delay changes every cycle length according to its number of gate passages. A delay-robust period witness or a direct gcd proof is required. |
| “The KKL clone graph is the WAD response graph.” | False: KKL clones the finite Hubbard-tree/core transition defining Perron eigenweights. WAD pullbacks must carry a separately proved, complete itinerary incidence with that core graph. |
| “Every bounded-type corridor is either an exact clone or has a uniform positive-entropy gap.” | False by P72/P74: reducible unit-spectral-radius transfers can accumulate polynomial shear. They require a pseudo-Siegel/sectorial regularization or an additional calibrated shear state. |
| “Classifying each nonstationary layer by its individual spectral radius classifies the product.” | False: upper and lower unipotent shears each have spectral radius one, while their product has Perron root \((3+\sqrt5)/2\). A common Frobenius flag or a grouped product analysis is required. |
| “A repeated Boolean-support prefix can be deleted from the numerical transition.” | False: the unipotent shear has constant support but linearly growing coefficients. The support automaton compresses only the finite skeleton and retains every pumped loop for entropy/shear analysis. |
| “A cyclic-looking support component includes every non-cycle SCC.” | False: an acyclic zero singleton is an SCC under the standard convention but has no entropy. The component must contain a positive-length closed walk. |
| “The spectral radius of an accepted open transfer is dynamical entropy.” | False by P84: an independent target relabeling can change it. Require a closed repeatable framed return or a canonical source endpoint identification. |
| “Permutation layer matrices prove an exact clone corridor.” | False by P70: they prove only an identity interior gauge. Side-edge exclusion, endpoint multiplicity, the cross section, source identity, and WAD incidence remain separate. |
| “A finite transfer alphabet is automatically the correct virtual language.” | False unless its automaton state preserves future admissibility. Enlarging the language may create branch-recurrent products not realizable by the dynamics. |
| “Finite postcritical horizon and finitely many local atom types bound the faithful automaton.” | False by P79; future-equivalence index can grow exponentially with horizon even when every core support is the identity. |
| “Exact corridor length can be represented by a one-state translation loop.” | False if the exit time is prescribed: the loop accepts all lengths. Retain the length as an explicit counter and keep its weighted spectral effect. |
| “One integer counter can harmlessly encode the whole satellite itinerary.” | Formally possible only with arbitrary coding/decoding, which makes bounded counter dimension vacuous. Counters need declared geometric semantics and universal restricted update/guard rules. |
| “A nested satellite chain automatically gives a LIFO stack.” | Unsupported: D25/KKL give ordered chains, not matched reverse push/pop, no-skipping, or WAD/access-state recovery. The stack rule is an open source theorem. |
| “The depth of a nested chain determines its labeled future.” | False without a bounded follower theorem: different rotation/decoration words can have the same depth and different admissible unwindings. Retain the word or prove a safe quotient. |
| “A checkpoint macro preserves the layerwise automaton language.” | False by P89. It preserves only checkpoint paths and the exact parameterized matrix power after every proof-used interior event has been excluded. |
| “Finite-control pumping remains exact after counters or stack words are projected away.” | False by P93. The repeated projected pair selected by pigeonhole may have nonidentity memory action; compile exact checkpoint macros or prove a finite memory congruence first. |
| “A bounded signature catalog bounds the core or WAD transfer dimension.” | False: one state with the loop \(I_d\) has one signature for every \(d\). Prove \(d\le d_0\) and \(w\le w_0\) independently. |
| “Future output observability constructs a compositional WAD quotient.” | False by P94. Every branch must additionally descend through the proposed quotient. |
| “The project matrix is unconditionally \(T_F\), or unconditionally \(T_F^{\mathsf T}\), in KKL notation.” | Unsupported because the checked source symbol has incompatible orientation cues. Lock the raw incidence \(N\), use \(B=N^{\mathsf T}\), and state the left/right equations. |
| “Transposition repairs KKL's printed clone equation.” | False by P95. Transposition preserves spectral radius and cannot change the exponent sign; the finite-\(n\) recurrence needs an independent corrected proof. |
| “Bounded reduced entropy controls all Value coefficients.” | It controls Perron eigencones only after reduced dimension and label depth are bounded; arbitrary Hubbard-tree intersection length remains separate. |
| “KKL Remark 4.14 transfers the tame and wave amplification proofs to a virtual hull.” | False by P96. The remark transfers only Proposition 3.7's static split. Propositions 3.8 and 3.9 use full-return and long-iterate structure absent from a partially invariant hull. |
| “A bound on selected virtual components is KKL's limb-occupancy hypothesis.” | False. KKL uses the finite Hubbard tree to obtain the access-complete ideal multi-interval bound \(|\mathcal L_j|\le6B\). Virtual fjords, dams, omitted components, and additional prime ends must be included or independently bounded. |
| “Separate tame and wave constants can be chosen independently and then fed to the static trichotomy.” | False by P98. The trichotomy returns a branch at one parameter. Invoke it at the wave-selector parameter and require the tame closure at that same parameter, or prove an explicit monotonicity/common-input theorem. |
| “The abstract Section-4 trichotomy realizes the virtual hull interface.” | False by P101. The theorem begins with `S4-AC`--`S4-END`; access completeness, all-cycle width comparison, restriction multiplicity, and faithful flux/wave decomposition are open geometric inputs. |
| “Bounded selected component count bounds the degree of the tame full return.” | False by P102. Degree is \(2^{m_I}\), where \(m_I\) counts critical encounters; a dynamical injection or encounter bound is required. |
| “Every rotation \(a/q\) can be reduced to \(1/q\) by relabeling the limbs.” | False by P106. The algebraic conjugacy generally fails to preserve cyclic order, geometric intervals, and the defect region. |
| “A degree-two endpoint return supplies the long-Wave fast-forward.” | False by P108. KKL uses a degree-one central corridor and a bounded auxiliary fan containing higher-degree proof-used sheets. |
| “The simultaneous inverse-tree fan theorem constructs the marked Wave fan.” | False by P110's hypotheses and scope. It assumes the full inverse tree and separated obstacles and proves proper sheets/degree only; cyclic access order, immersion properness, itinerary exhaustion, and width transport remain open. |
| “A full partially invariant virtual hull automatically supplies the inverse tree used by the fan theorem.” | False by P111. Even surjective forward invariance and critical-orbit inclusion do not imply that the smaller hull is an entire pullback component. |
| “Forward dynamics on the Cantor atoms makes an arbitrary connected hull forward coherent.” | Unsupported. The connector images must also remain in the declared parent seed/carrier before P112 applies. |
| “The exact dyadic pullback count proves access completeness.” | False by P114's qualification. It counts preimages of the declared root endpoints; every proof-used future end must first be shown to project to that root set. |
| “Finite obstacle complement inclusions give the relative-cover immersion.” | False by P113's scope. The subgroup lift criterion, core properness, and end-properness remain independent. |
| “Boundedly many new endpoints at each corridor stage give a period-independent marking.” | False by P115. In a degree-one corridor the total count is the terminal count plus the sum of all genuine births. |
| “Equal translation labels imply zero endpoint births.” | False without P116's geometric hypotheses. A new attached carrier component can create additional prime ends even when coarse labels agree. |
| “Pullback-component saturation proves KKL's corridor carrier equality.” | False by P119. Saturation compares a selected source with the pullback of its target; KKL's no-birth argument separately compares the pulled carrier with the carrier embedded by the immersion. |
| “KKL Proposition 6.7 applies to a virtual hull because its labels translate.” | False by P117. The source proof uses the restricted actual-Hubbard-tree equality on \(\mathcal L_{[B,q-B-2]}\), equivalently no pulled excess meeting the relevant central intervals. |
| “Root-shadow inclusion puts one disconnected package in one pullback component.” | False by P120. Every forward shadow can lie in the root while different pieces of the package occupy different pullback components. |
| “Future-completing the root after sheet separation is harmless.” | False by P122. Enlarging the root coarsens the pullback-component partition and may merge selected sheets. |
| “A central carrier containing the critical value can still be a degree-one translation step.” | False by P121. Its selected pullback is the unique degree-two critical component. |
| “The minimal connected full hull canonically supplies the virtual connectors.” | False by P131: no minimum exists even for a two-point package. |
| “A collision-free absorbed-cell quotient preserves the complete prime-end marking.” | False by P132 if the quotient omits an erased protected access or its full attachment trace. |
| “Monotone absorption repairs every central carrier excess.” | False by P132: absorption can irreversibly destroy a proof-used access while leaving sheet, critical, obstacle, and localization flags zero. |
| “A monotone preimage of the model Hubbard tree automatically preserves every virtual access.” | False by P139. A projection fiber or filled complementary component may enter a protected collar even though the lifted set is connected and forward coherent. |
| “The abstract protected connector theorem constructs the virtual carrier.” | False by P140. It realizes an explicit certificate; constructing that certificate from the actual virtual-Molecule dynamics remains open. |
| “The connector-side bound is universal because the routing tree is finite.” | False by P138. The bound is \(4s-6\) in the retained atom count \(s\), which may grow with the satellite combinatorics until a uniform bound or faithful compression is proved. |
| “A favorable processing order can prevent a collision between fixed assigned packets.” | False by P147. Every sequential fillification ends at the filled hull of the same raw union. |
| “Individual ports may be unusable because their long representatives cross.” | False after completed-packet disjointness. P147 truncates each port inside a disjoint neighborhood of its own packet. The real issue is existence of an unprotected access landing on the original atom. |
| “A post-fill merger can be repaired by monotonically adding more pieces to the same packet labels.” | False by P147 and monotonicity of the filled hull. The repair must change the assignment, root/sheet partition, timing, or localization. |
| “Choose a very large Wave horizon and call the inventory final.” | False by P148. Finality is exclusion of every later dependency path to an omitted old record, not largeness of the stopping integer. |
| “The minimal dependency closure chooses the packet assignment.” | False. The same unlabelled inventory graph can occur with different source attachment data and hence different source-faithful labels. |
| “KKL's native Hubbard-tree inventory is automatically the virtual inventory.” | False by P149. A typed branch- and prime-end-preserving bridge is a separate unproved input. |

## 4. Circularity audit

### Virtual-hull construction

It is circular to deduce an a priori virtual-hull bound by assuming uniform
hyperbolicity or precompactness of the unified renormalization operator. D25 notes that
such an a posteriori deduction is possible; the requested proof needs it a priori.

### Coercivity

It is circular to define \(D^\#\) by minimizing over a compact family of normalized
virtual hulls and then use bounded \(D^\#\) to prove that same compactness.

### Parameter transfer

It is circular to assume a shrinking connected relative-neighborhood basis in order
to prove the trivial-fiber/rigidity theorem that is supposed to produce that basis.
Diameter decay of a non-neighborhood sequence is not a substitute.

### Rigidity

It is circular to invoke “no invariant line field” as if it identified a unique
parameter without also supplying the combinatorial/Teichmüller control needed to build
the conjugacy and transfer it to parameter space.

## 5. Constant audit

Every future proof must expose the dependence of:

\[
D_*,\lambda_{\rm raw},\lambda,\delta,C,E_0,\eta_0,T_0
\]

before selecting a tower. They must not depend on:

- satellite relative periods \(s_n\);
- rotation numbers or continued-fraction entries;
- continued-fraction depth;
- virtual-molecule chain length;
- transition depth;
- the number of alternating neutral/primitive interfaces.

Map-dependent finite-prefix widths may enter a parameter-specific a priori bound, but
they cannot be hidden inside constants advertised as universal or beau.

## 6. Orbit-marking audit template

For every application of Wave, Wanderers, covering, or quasi-additivity, record:

| Field | Required entry |
|---|---|
| checkpoint/block | indices \(p(n),n\) |
| curve family | exact \(\Gamma\) and homotopy class |
| forward/pullback length | integer number of iterates/returns |
| branch degree | \(1\), \(2\), or explicit product |
| encountered critical values | list of marked orbit indices |
| base/neutral accesses | elements of \(B_n\cup{\cal I}_n\) |
| omitted postcritical points | proof that they do not enter the branch domains |
| width loss | explicit \(e_j\) |
| accumulation | bound on the sum over the block |

An argument with a blank field has not established compatibility.

## 7. Adversarial dependency tests

### Test A: \(s_n\) grows faster than any prescribed function

Expected behavior: ordinary root width may diverge arbitrarily. The proof must remain in
the marked sectorial chart and must not invoke a global width-growth cap.

### Test B: entropy \(\epsilon_n\downarrow0\)

Expected behavior: elementary Value contraction is nonuniform. Blocks must be grouped
until accumulated entropy reaches \(\eta_0\), with error controlled by `M3`.

### Test C: \(N,P,N,P,\ldots\)

Expected behavior: the number of chart changes is unbounded. The proof must provide a
telescoping/summable interface estimate.

### Test D: long virtual-molecule chain with many Cantor components

Expected behavior: raw marking cardinality is unbounded. The proof must retain every
required access and critical return, isolate a bounded active core, and show bounded
interaction types modulo the accelerated translation action.

## 8. Minimal next proof target

Before the analytic response theorem, the first genuinely new geometric
theorem remains `VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE`, which is a
sufficient source-faithful route to `VIRTUAL_COMMON_FREE_COMPONENT`.
The processing-order and global port-untangling subproblems are now removed
by P147.  P148 orders the first clause: the Wave stopping interface must be
proved before the component inventory can be frozen.  The first replacement
input is `VIRTUAL_WAVE_HORIZON_CERTIFICATE`.  The live source-facing clauses
are:

> For one actual virtual-Molecule block, define the finite stopping rule,
> stage branches, proof-use ledger, and dependency universe; prove that the
> final root enlargement leaves no dependency path to an omitted earlier
> record (`VIRTUAL_WAVE_HORIZON_CERTIFICATE`).  Then construct the frozen
> component-level inventory and typed assignment `VAAPC-I`; compute its unique completed
> packets; prove zero completed collision `VAAPC-C` and one actual
> unprotected original-atom exposure `VAAPC-P`; transport the full packets
> through the complete horizon (`VAAPC-H`); and prove the period-independent
> incidence/compression clause (`VAAPC-U`). If this fails, emit the
> chamber-refined closure or port tuple from
> `augmented_packet_closure_audit.md`, equations (9.1)--(9.2). If the
> original free domain itself is separated, also emit the separator tuple
> from `virtual_protected_routing_domain.md`, equation (7.1).

The proved augmented-domain theorem then gives the common component, and the
proved free-component criterion constructs the protected root connector.
The remaining clauses of `VIRTUAL_PROTECTED_ROUTING_CERTIFICATE` must still
verify the iterated package components, parent routes, selected sheets,
critical words, future marking, and uniform-complexity interface.

Once that gate is available, the first genuinely new analytic theorem is:

> For one selected virtual-molecule block, construct the monotone finite cell-tree and
> separated future-closed electrode ports; prove bounded access/translation incidence,
> standard-width density, and uniform generalized response eigenvalue bounds; and show
> that the marking-to-parallel-replica congestion \(\rho_B\) is bounded or
> \(\rho_B/D\) lies below the expansion margin. Make every outgoing KKL valuation
> observable by a Value-faithful port refinement or a uniformly finite Value-moment
> vector. Construct a universally bounded-dimensional finite core-transfer cocycle
> with complete WAD incidence and a source-column endpoint frame, locking the raw
> incidence \(N\), \(B=N^{\mathsf T}\), and the KKL left/right Value roles. Prove
> the core and WAD dimensions separately from the signature count, verify every WAD
> transport-quotient commuting square, and compile counter/stack memory exactly
> before applying finite-control pumping. Route permutation
> interiors to the clone certificate only after its purity/gate clauses hold, route
> cyclic branching to source-licensed positive entropy only on a closed repeatable
> framed return, and route every nonexpanding transfer to transient extinction,
> pseudo-Siegel regularization, or a calibrated finite shear/flag state. Retain
> counter and stack side data and all loop emissions, including nonstationary frame
> changes. Any clone branch must realize the literal-graph hypotheses of the proved
> typed \(t^{-k}\) recurrence, not use the quarantined printed \(+\lambda^k\)
> equation. It must also prove the actual return-depth bound \(K<n\). Then calibrate
> the resulting augmented response form to both KKL and DL25 curve families with
> controlled distortion, multiplicity, and electrical orientation.

The bounded-marking quotient version is refuted in `virtual_block_quotient.md`. The
topological prerequisites and the independent width no-go are now isolated in
`finite_horizon_inflation.md`; the abstract width estimate is now proved once the
corridor realization exists. Linear complexity is also proved after complete bounded
incidence is supplied, but finite topology does not supply that incidence or
replication. The response calculus remains the correct exact language for parallel and
serial structure, but P53 proves that the response-only state is not a complete Value
state. The replacement combines `M1`, the nonlinear localization and Value-feature
parts of `M2`, and the indispensable complexity charge in `M3`. Without it,
Value/Wave machinery cannot be stated with universal constants on a virtual block.
With it, blockwise summability and the entropy/sectorial dichotomy become well-posed.

## 9. Wave-horizon compiler dependency refinement

The finite stopping and final-root algorithms are no longer the first open
step.  `RESOLVED_FINITE_WAVE_HORIZON_COMPILER` proves them after the
analytic proof program is resolved, and `KKL_NATIVE_WAVE_HORIZON_CONTROL`
checks the architecture in KKL's native category with the
\(216b^2\) visit-chain cap **conditional on**
`KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR`.  The conditional architecture
certificate is not a proof of the missing interval-growth implication or
of Wave amplification.

The first unfilled analytic dependency is now
`VIRTUAL_WAVE_MARKED_CORRESPONDENCE`:

> Define a horizon-independent prefix-closed language of admissible finite
> return words.  For every finite provisional root package and compatible
> word, construct an actual marked hyperbolic complement and
> covering/immersion pair whose pulled marking refines the immersed marking,
> whose marked action is exact, whose used intervals are proper or
> end-proper, and whose certified assertions commute with collision-free
> package enlargement.

Only after this correspondence exists can the virtual proof-use ledger be
typed, its dynamical iterate horizon be summed, and the proved compiler be
applied.  The native KKL identity
\((f^r)_*\iota_r^*I=F_*^rI\) cannot be replaced by equality of component
labels.  Likewise the KKL visit cap depends on the fixed parabolic bound
\(b\) and is not the period-independent virtual bound required later.

The refined dependency order is therefore
\[
\texttt{VIRTUAL\_WAVE\_MARKED\_CORRESPONDENCE}
\Longrightarrow
\texttt{VIRTUAL\_WAVE\_HORIZON\_CERTIFICATE}
\Longrightarrow
\texttt{VAAPC-I}.
\]
All three implications are construction requirements, not proved analytic
existence statements.

The word language and provisional-package quantifiers are essential for
noncircularity.  Defining the correspondence only “for every proof-used
word” would presuppose the horizon which the correspondence is meant to
construct.

## 10. Marked-correspondence dependency correction

The direct dependency from the generic carrier and prime-end lemmas to
`VIRTUAL_WAVE_MARKED_CORRESPONDENCE` was too coarse.  Those lemmas construct
or recognize:

- routed full pullback components;
- complement coverings;
- relative-cover lifts;
- qualitative Jordan localizations; and
- prime-end boundary circles.

They do not determine the prime-end action of the immersion.  On
\(V=\mathbb C\setminus\overline{\mathbb D}\), the pairs
\[
  g(z)=z^2,\qquad \iota_\alpha(z)=e^{i\alpha}z
\]
have identical carrier and degree data.  For the marking with endpoint
\(E=\{1\}\), the covering endpoint pullback is \(\{1,-1\}\), while the
immersion endpoint pullback is \(\{e^{-i\alpha}\}\).  Marked action holds
exactly for \(\alpha=0,\pi\pmod{2\pi}\).  Thus an unnormalized boundary
phase is a genuine missing dependency.

The proved `PRIME_END_MARKING_ACTION_CRITERION` identifies the exact
condition:
\[
  E^\iota_{P,r}\subset E^g_{P,r}.
\]
When the immersion induces a prime-end circle homeomorphism, this is
forward invariance of the endpoint set under
\(\beta=g_\partial\iota_\partial^{-1}\).  The least endpoint set containing
the proof-used accesses is the closure of their forward \(\beta\)-orbits;
it defines an ideal marking exactly when it is nowhere dense.

The corrected pre-horizon dependency is
\[
\begin{split}
 &\texttt{VIRTUAL\_RETURN\_BRANCH\_LANGUAGE}\\
 {}\land{}&
 \texttt{VIRTUAL\_PROVISIONAL\_COMPLEMENT\_PAIR}\\
 {}\land{}&
 \texttt{VIRTUAL\_ACCESS\_ACTION\_CERTIFICATE}\\
 {}\land{}&
 \texttt{MARKED\_PAIR\_ENLARGEMENT\_NATURALITY}\\
 &\Longrightarrow
 \texttt{VIRTUAL\_WAVE\_MARKED\_CORRESPONDENCE}.
\end{split}
\]

The first three antecedents are open source-facing theorems.  The last is
proved.  None depends on the completed Wave horizon: each quantifies over a
finite provisional package and a finite path in a return graph fixed before
the stopping execution.  Hence the correction exposes missing data without
creating a cycle through `VIRTUAL_WAVE_HORIZON_CERTIFICATE`.

## 11. Return-branch dependency refinement

The path-language lemma alone was too weak to realize an analytic return
language.  A directed sequence of actual edge labels need not have a
nonempty analytic composite domain.  The new atlas construction corrects
this by defining every child domain as an actual connected component
\[
 C\in\pi_0\bigl(\Phi_\nu^{-1}(A_b)\bigr)
\]
and proving
\[
 F_b\circ\Phi_\nu|_C=f^{S_\nu+q_b}|_C.
\]

The generic compiler is now proved:
\[
\begin{split}
 &\texttt{VIRTUAL\_RETURN\_BASE\_ATLAS}\\
 {}\land{}&
 \texttt{VIRTUAL\_WAVE\_DEMAND\_SCHEMA}\\
 {}\land{}&
 \texttt{DEMAND\_CLOSED\_RETURN\_ATLAS\_COMPILER}\\
 {}\land{}&
 \texttt{RETURN\_ATLAS\_ENLARGEMENT\_NATURALITY}\\
 &\Longrightarrow
 \texttt{VIRTUAL\_RETURN\_BRANCH\_LANGUAGE}.
\end{split}
\]

The last two inputs are proved.  The first two are open source-facing
constructions.  The first missing field is an open return base:
Dudko's virtual paragraph specifies compact small-Julia data but no open
localization relative to which a first return is taken.  This is substantive,
not notational.  For \(f(z)=z^2-1\) and compact seed \(\{-1\}\), two explicit
Jordan disks give first-return times two and one.

Final-root stability also splits into two logically distinct conclusions.
An injective exact atlas morphism preserves old words.  Equality of complete
languages additionally requires a bijection on demanded branch-component
pairs at every prefix.  Without that condition, late-root enlargement may
create a new child even when every old analytic square continues to commute.

Neither open source-facing input depends on a completed Wave horizon.  The
return bases and syntactic continuation relation must be fixed first; the
stopping execution then selects a finite subtree.  Thus the refinement does
not introduce a dependency cycle.

## 12. Native return atlas versus virtual selector

The source pass in `virtual_return_base_atlas.md` resolves the native
analytic subproblem.  In Lyubich's principal nest, the stronger boundary
avoidance

\[
 f^m(\partial V^{n-1})\cap\operatorname{int}V^{n-2}=\varnothing
\]

and \(V^{n-1}\Subset\operatorname{int}V^{n-2}\) imply that
\(\operatorname{int}V^{n-1}\) is nice.  Markov pullback then produces the
actual return components, exact iterates, and degree words.  This gives

\[
\texttt{LYUBICH\_PRINCIPAL\_RETURN\_MAP}
\Longrightarrow
\texttt{NATIVE\_PRINCIPAL\_NEST\_RETURN\_ATLAS}.
\]

The implication cannot be composed directly with the virtual copy-chain
data.  A new typed bridge is required:

\[
\begin{split}
 &\texttt{NATIVE\_PRINCIPAL\_NEST\_RETURN\_ATLAS}\\
 {}\land{}&
 \texttt{VIRTUAL\_SCALE\_TO\_PUZZLE\_SELECTOR}\\
 &\Longrightarrow
 \text{the analytic-base portion of }
 \texttt{VIRTUAL\_RETURN\_BASE\_ATLAS}.
\end{split}
\]

The selector is open.  It must map each intermediate virtual copy index to
an actual embedded nice base and prove carrier placement, return and access
completeness, obstacle/sheet compatibility, and exact enlargement maps.
The need for an actual embedding cannot be weakened to isotopy relative to
the carrier: the concentric-disk example in
`ISOTOPY_CLASS_RETURN_UNDERDETERMINATION` changes the return time inside one
explicit relative-isotopy class.

This refinement does not add a cycle.  The selector must be fixed from
regulated puzzle/renormalization data before the Wave demand execution and
before any width bound, compactness, or rigidity conclusion.  The order is

\[
\texttt{VIRTUAL\_SCALE\_TO\_PUZZLE\_SELECTOR}
\to
\texttt{VIRTUAL\_RETURN\_BASE\_ATLAS}
\to
\texttt{VIRTUAL\_RETURN\_BRANCH\_LANGUAGE}
\to
\texttt{VIRTUAL\_WAVE\_MARKED\_CORRESPONDENCE}.
\]

## 13. First direct-decoration selector refinement

The universal selector now has a proved first-scale analytic subpath:

\[
\begin{split}
\texttt{KL\_DECORATION\_ESCAPE\_PUZZLE}
&\Longrightarrow
\texttt{FIRST\_DECORATION\_SCALE\_ESCAPE\_ATLAS},\\
\texttt{FIRST\_DECORATION\_SCALE\_ESCAPE\_ATLAS}
&\Longrightarrow
\texttt{CRITICAL\_BASE\_CYCLE\_EXCLUSION}.
\end{split}
\]

For a fixed non-principal decoration outside a directly attached
satellite \(M_{p/q}\), the selected relative depth is

\[
\nu_{\rm dec}(1)=nq+1,
\]

where \(n\) is the least critical \(q\)-return entering an off-critical
decoration piece.  This field is therefore no longer unknown at the first
direct-decoration scale.

The path does not reach the universal selector.  At the terminal primitive
first return \(f^P:A_0\to B\), every \(K_i=f^i(K_0)\), \(1\le i<P\), is
outside \(B\).  The replacement analytic object is the chain

\[
A_0\to A_1\to\cdots\to A_{P-1}\to B
\]

with the inclusion \(A_0\hookrightarrow B\).  The missing edge is not a
holomorphic iterate: it is the protected continuum and prime-end
attachment data needed to connect the pairwise-disjoint \(K_i\) inside
\(J(f)\).

There is also a concrete incidence path to VAAPC-U/H2:

\[
\texttt{KL\_DECORATION\_ESCAPE\_PUZZLE}
\Longrightarrow
\texttt{DECORATION\_FAN\_GROWTH}
\Longrightarrow
\begin{matrix}
\text{raw candidate count }2^n\\
\text{requires bounded complete selection or faithful compression}.
\end{matrix}
\]

The last arrow is an obstruction statement, not a proof that every raw
vertex is a Wave demand or a proof of compression.
Any proposed quotient must separately satisfy
`WAD_TRANSPORT_QUOTIENT_CRITERION` and
`WAD_FUTURE_OBSERVABILITY`.

The corrected local dependency order is

\[
\begin{gathered}
\text{direct-decoration escape atlas}\\
\downarrow\\
\text{multi-base primitive return chain}\\
\downarrow\\
\text{protected connector + complete access marking}\\
\downarrow\\
\text{future-faithful fan compression}\\
\downarrow\\
\texttt{VIRTUAL\_RETURN\_BASE\_ATLAS}.
\end{gathered}
\]

At deeper copies \(s\ge2\), the first arrow itself remains open because
the preceding intermediate satellite object is disconnected.  Reusing the
direct-decoration construction there would assume the virtual
renormalization under construction and create a dependency cycle.

## 14. Terminal Hubbard anchor and the \(s=2\) vertex-package gate

The native terminal connector is no longer wholly missing.  KKL's native
prime primitive category supplies the complete small-Julia cycle and its
compact forward-invariant Hubbard tree:

\[
\texttt{KKL\_NATIVE\_TERMINAL\_HUBBARD\_TREE}
\Longrightarrow
\begin{cases}
\texttt{NATIVE\_HUBBARD\_SUBTREE\_FUNCTORIALITY},\\
\texttt{TERMINAL\_CYCLE\_HUBBARD\_ANCHOR}.
\end{cases}
\]

The internal finite-tree theorem proves, for a finite selected vertex
package \(S\),

\[
[\Phi(S)]\subset\Phi([S]),
\]

with equality on a branch that is injective on the whole selected subtree.
If \(S\subset S^+\), the enlarged hull differs from the old hull by a forest
whose components each have one old-tree gate.  These are exact
component-level transport and enlargement statements; they do not prove
protected prime-end survival.

For the terminal cycle, the selected set is
\(\{K_0,\ldots,K_{P-1}\}\), its hull is the native Hubbard tree, and the
first edge on the unique path from \(K_1\) to \(K_0\) selects a native ideal
attachment side.  The earlier missing-access record is therefore refined
to

\[
\chi_{\rm ideal}=0,
\qquad
\chi_{\rm protected\ analytic}=\bot.
\]

This refinement does not select the virtual \(s=2\) package.  The copy-chain
label and ambient terminal tree do not determine which vertices, retained
critical returns, protected sides, obstacles, and proof-use demands belong
to that scale.  The missing prior map is

\[
\texttt{VIRTUAL\_VERTEX\_PACKAGE\_SELECTOR}.
\]

The corrected order is

\[
\begin{gathered}
\text{native terminal Hubbard tree}\\
\downarrow\\
\text{terminal anchor + finite subtree functoriality}\\
\downarrow\\
\texttt{VIRTUAL\_VERTEX\_PACKAGE\_SELECTOR}\\
\downarrow\\
\texttt{VIRTUAL\_SCALE\_TO\_PUZZLE\_SELECTOR}\\
\downarrow\\
\texttt{VIRTUAL\_RETURN\_BASE\_ATLAS}.
\end{gathered}
\]

There is no new dependency cycle: the vertex package must be selected from
copy-chain and actual orbit data before a Wave stopping execution or any
width, compactness, or rigidity conclusion.  The selector remains open
because neither Dudko's public interpolation paragraph nor KKL's native
terminal construction defines that scale-to-package map.

## 15. Cantor-package/type audit at the first recursive scale

The phrase “Cantor small Julia sets” cannot be replaced silently by a
finite list of terminal-tree vertices.  The audited types are

\[
\begin{array}{c}
\text{virtual component family }\mathfrak C_s\\
\downarrow\quad\text{freeze proof-use horizon}\\
\text{finite trace or future-faithful quotient }
\mathfrak F_{s,\mathscr D}\\
\downarrow\quad\text{prove partial factor}\\
\text{native terminal Hubbard tree}.
\end{array}
\]

If the component family is infinite, no finite package can enumerate it
injectively.  A quotient \(q\) is valid for a joint observable
\(\mathcal O\) exactly when

\[
 q(X)=q(Y)\Longrightarrow \mathcal O(X)=\mathcal O(Y).
\]

This is recorded by the proved
`FINITE_EXACT_CANTOR_ENCODING_OBSTRUCTION` and
`FINITE_QUOTIENT_OBSERVABILITY_CRITERION`.  They are interface theorems,
not virtual-carrier constructions.

The corrected open dependency order is

\[
\begin{gathered}
\texttt{VIRTUAL\_CANTOR\_PACKAGE\_REALIZATION}\\
\downarrow\\
\texttt{VIRTUAL\_PROOF\_USE\_TRACE\_SELECTOR}\\
\downarrow\\
\texttt{VIRTUAL\_VERTEX\_PACKAGE\_SELECTOR}\\
\downarrow\\
\texttt{VIRTUAL\_SCALE\_TO\_PUZZLE\_SELECTOR}.
\end{gathered}
\]

At \(s=2\), the checked copy-chain sources do not define the address space,
the embedded components, or their analytic branch action.  Hence the first
failure record is a type obstruction
\(\mathfrak X^{\rm type}_2\), before any actual excess component can be
named.  Its access, sheet, localization, and itinerary coordinates are
bottom symbols, not zero.  This is not a counterexample to the unpublished
virtual-renormalization construction and does not promote any downstream
gate.

## 16. Direct-decoration pullback compactification

The type obstruction has now been narrowed in the direct-decoration source
category.  Kahn--Lyubich's two actual univalent pullbacks of the separator
\(P\) give

\[
\texttt{KL\_DECORATION\_ESCAPE\_PUZZLE}
\Longrightarrow
\texttt{DIRECT\_DECORATION\_PULLBACK\_COMPACTIFICATION}.
\]

For finite words \(w\), the fibers are actual pullbacks
\(K_w=\phi_w(K_0)\).  For infinite words \(\omega\), they are actual nested
puzzle fibers

\[
E_\omega=\bigcap_{m\ge1}Q_{\omega|m}.
\]

The address compactification consists of terminated finite words and
binary ends.  The resulting planar union is compact, and its connected
components are exactly the \(K_w\) and \(E_\omega\).  The two address maps
must remain distinct:

\[
\operatorname{gpar}(wa)=w
\quad\text{(geometric nesting)},\qquad
\sigma_{\rm pre}(aw)=w
\quad\text{(\(f^q\)-shift)}.
\]

The second formula is defined only away from the empty address.  The root
uses the separately typed terminal-cycle arrow \(\tau_{\rm root}\).

This distinction prevents a false itinerary reversal.

For connected roots remaining in the first-level gap, the package is
natural:

\[
\texttt{DIRECT\_DECORATION\_PULLBACK\_COMPACTIFICATION}
\Longrightarrow
\texttt{PULLBACK\_GAP\_ENLARGEMENT\_NATURALITY}.
\]

The theorem is deliberately local to one directly visible decoration.
It neither proves that every end fiber is a small Julia set nor places the
second satellite portrait on those fibers.  The corrected open dependency
order is

\[
\begin{gathered}
\texttt{DIRECT\_DECORATION\_PULLBACK\_COMPACTIFICATION}
+\texttt{PULLBACK\_GAP\_ENLARGEMENT\_NATURALITY}\\
\downarrow\\
\texttt{VIRTUAL\_DISCONNECTED\_MARKING\_TRANSFER}\\
\downarrow\\
\texttt{VIRTUAL\_CANTOR\_PACKAGE\_REALIZATION}\\
\downarrow\\
\texttt{VIRTUAL\_PROOF\_USE\_TRACE\_SELECTOR}.
\end{gathered}
\]

Thus the first scale-two bottom field has moved from the entire outer
component map to the marking transfer

\[
\mu_2=\bot.
\]

No width, compactness, rigidity, VAAPC-I, UPTCR, or MLC statement is used
in this construction.

## 17. Post-referee dependency repair

The direct-decoration compactification does not itself determine where a
source-defined return branch lands among equal-depth cylinders.  The exact
finite-cylinder application order is

\[
\begin{gathered}
\texttt{DIRECT\_DECORATION\_PULLBACK\_COMPACTIFICATION}\\
\downarrow\\
\texttt{VIRTUAL\_CYLINDER\_TARGET\_ADDRESS\_SELECTOR}
+
\texttt{FINITE\_CYLINDER\_COMMUTING\_ITERATE\_LIFT}\\
\downarrow\\
\texttt{VIRTUAL\_DISCONNECTED\_MARKING\_TRANSFER}.
\end{gathered}
\]

The commuting-lift theorem is logically independent of the selector and is
already proved as a conditional statement.  Its application is available
only after
an equal-depth target cylinder \(Q_v\) has been selected and actual
containment \(f^r(A_w)\subset Q_v\) has been verified, commutation of the
two polynomial iterates forces

\[
 f^r|_{A_w}=h_v^{-1}\circ F\circ h_w.
\]

It does not construct \(v\), transport prime ends, or reconstruct critical
chronology.  Those fields remain obligations of the target-address
selector and marked transfer.

The virtual-scale dependency order is now split to remove a hidden semantic
cycle:

\[
\begin{gathered}
\texttt{VIRTUAL\_CANTOR\_PACKAGE\_REALIZATION}\\
\downarrow\\
\texttt{VIRTUAL\_PREFIX\_LOCAL\_SCALE\_SELECTOR}\\
\downarrow\\
\texttt{VIRTUAL\_RETURN\_BASE\_ATLAS}
\longrightarrow
\texttt{VIRTUAL\_RETURN\_BRANCH\_LANGUAGE}\\
\downarrow\\
\texttt{VIRTUAL\_WAVE\_MARKED\_CORRESPONDENCE}\\
\downarrow\\
\texttt{VIRTUAL\_WAVE\_HORIZON\_CERTIFICATE}\\
\downarrow\\
\texttt{VIRTUAL\_PROOF\_USE\_TRACE\_SELECTOR}\\
\downarrow\\
\texttt{VIRTUAL\_VERTEX\_PACKAGE\_SELECTOR}
\longrightarrow
\texttt{VIRTUAL\_SCALE\_TO\_PUZZLE\_SELECTOR}.
\end{gathered}
\]

The prefix-local selector is not permitted to depend on the final frozen
trace.  The final selector is not permitted to feed any construction
upstream of the horizon.

Two further directions are corrected:

1. `VIRTUAL_UNPROTECTED_ATOM_EXPOSURE` is an independent input to VAAPC;
   it is not inferred from the downstream common-free-component theorem.
2. `VIRTUAL_ATTACHMENT_RESOLUTION` is the disjunction used by bounded
   attachment support: either an actual attachment-free anchor, or the
   collision-free analytic realization of the least attachment closure
   with empty central support.

The machine graph has been checked for cycles after these changes.  The
remaining open gates are mathematical, not graph artifacts.

## Push II critical-chronology dependency audit

The supplied Push II patch attempted to promote the two existing compiler
gates after rewriting them to assume compatible stages.  That would remove
the very existence statements those nodes were created to track.  The
correct split is:

\[
\begin{gathered}
\text{actual virtual relative-cover stages and critical spine}\\
\Downarrow\\
\texttt{MAPPING\_TELESCOPE}\quad(\text{open})\\
\Downarrow\\
\texttt{PLANAR\_CRITICAL\_SPINE\_TELESCOPE\_COMPILER}
\quad(\text{proved tool}),\\[3pt]
\text{actual protected depth-}q\text{ stage data}\\
\Downarrow\\
\texttt{FINITE\_HORIZON\_ASSEMBLY}\quad(\text{open})\\
\Downarrow\\
\texttt{FINITE\_PLANAR\_TELESCOPE\_IDENTITY}
\quad(\text{proved algebraic tool}).
\end{gathered}
\]

The arrows are application arrows, not proof-dependency reversals: the
proved tools state what follows once the open analytic inputs have been
constructed.  They do not construct those inputs.

The finite-word branch is now:

\[
\begin{gathered}
\texttt{RETIMED\_FINITE\_CYLINDER\_PAIR}\quad(\text{proved conditionally
on a named root pair})\\
\Downarrow\\
\texttt{VIRTUAL\_FINITE\_WORD\_ROOT\_PORTRAIT\_AUTHORIZATION}
\quad(\text{open})\\
\Downarrow\\
\texttt{VIRTUAL\_DISCONNECTED\_MARKING\_TRANSFER}
\quad(\text{open}).
\end{gathered}
\]

The open authorization node also depends explicitly on
`VIRTUAL_CYLINDER_TARGET_ADDRESS_SELECTOR` and
`VIRTUAL_WAVE_DEMAND_SCHEMA`.  The former supplies the actual reached
finite-cylinder ownership; the latter supplies the quantified complete
Wave demand with respect to which naturality is asserted.  Omitting the
second edge would leave “complete-Wave-demand naturality” without its
declared quantifier source.  The added edge creates no dependency cycle.

The end branch is:

\[
\begin{gathered}
\texttt{PLANAR\_END\_COLLAPSE\_NO\_GO}
\quad+\quad
\texttt{NORMALIZED\_RETIMED\_GERM\_CONSTANCY}\\
\Downarrow\\
\texttt{DIRECT\_DECORATION\_END\_PRIME\_END\_COFINALITY}
\quad+\quad
\texttt{VIRTUAL\_END\_BLOWUP\_REALIZATION}\\
\Downarrow\\
\texttt{VIRTUAL\_DISCONNECTED\_MARKING\_TRANSFER}.
\end{gathered}
\]

The first row contains necessary constraints, not a construction of either
open row.

### Forbidden shortcuts added by this audit

1. A retimed pair for a given \(F\) may not be cited as construction of
   the source-defined scale-two \(F\).
2. The degree-two product may not replace the stagewise chronological
   word.
3. Critical-value retention may not replace relative-cover component,
   deck-phase, and protected-boundary realization.
4. A conformal embedding may not be treated as a homeomorphism of the
   target prime-end circle.
5. Angular contraction may not be treated as prime-end impression
   equality without a cofinal fundamental-chain proof.
6. Planar collapse may not be treated as existence of a blow-up or rescaled
   end object.
7. Persistence of old demand words under enlargement may not replace a
   bijection on the complete enlarged demand catalog.

After adding fourteen proved local tools and three explicit open residuals,
the ledger is acyclic with 256 obligations: 16 imported, 182 proved, and
58 open.  The open-count increase is intentional: it exposes hypotheses
that the supplied patch would otherwise have hidden.

### Second-pass proof-dependency repair

The first release audit located two proof-text gaps beneath the planar
compiler chain.  They have now been closed without changing statuses:

1. `QUADRATIC_JORDAN_BASE_CHANGE_DICHOTOMY` now uses
   Riemann--Hurwitz to prove that its connected branched pullback has one
   boundary component; and
2. the compiler's separated two-sheet failure certificate applies only
   when the propagated critical value is strictly outside the closure of
   the next base.  Boundary contact is a separate stopped
   boundary-critical collision.

The fixed-iterate compact-intersection theorem now states its Hausdorff
ambient hypothesis.  This is essential: nested compact tails in the
cofinite topology give an exact counterexample without it.  These repairs
close omitted hypotheses and proof sentences in the local tools; they do
not discharge any virtual realization node.

The release-surface order was checked against the graph as well:
`VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION` is an explicit prerequisite
of `VIRTUAL_CYLINDER_TARGET_ADDRESS_SELECTOR`.  The former must therefore
appear first in every prose roadmap.  The manuscript's planar compiler was
also retitled “critical-spine,” not “protected-spine,” because protected
marking remains an open downstream realization requirement.

## 17. Research Push III end-rescaling and response audit

The supplied Push III dependency deletion is rejected.  The valid narrow
chain is

\[
\begin{gathered}
\texttt{RETIMED\_FINITE\_CYLINDER\_PAIR}
\longrightarrow
\texttt{NORMALIZED\_END\_DIRECT\_LIMIT}
\longrightarrow
\texttt{END\_CHART\_OBSERVABLE\_INVARIANCE},\\
\texttt{SERIAL\_EXHAUSTION\_RESISTANCE\_BOUND}
\quad+\quad
\texttt{SCALAR\_NECK\_TRACE\_MODE\_NO\_GO}\\
\longrightarrow
\texttt{END\_PLUMBING\_TRACE\_RESPONSE\_CONTROL}
\quad(\text{open})\\
\longrightarrow
\texttt{H2\_RESPONSE\_REALIZATION}
\quad(\text{open}).
\end{gathered}
\]

The first row is a normalized coordinate statement for a root portrait
already supplied independently.  It does not depend on, or prove,
`VIRTUAL_END_BLOWUP_REALIZATION`.  The second row identifies the missing
analytic interface theorem.  Scalar series resistance controls the constant
mode only; it cannot delete the functional trace space of a cut
cross-section.

The supplied finite-horizon claim also cites a nonexistent renamed assembly
node.  Its intended authoritative dependency is
`FINITE_HORIZON_ASSEMBLY`, which remains open and depends on the open
`MAPPING_TELESCOPE`.  Therefore none of
`H1_FINITE_HORIZON_INFLATION`, `H2_RESPONSE_REALIZATION`, or
`H2_FORWARD_CONTRACTION_CALIBRATION` is promoted.

After adding five proved narrow results and the one explicit open
trace-response gate, the ledger is acyclic with 262 obligations:
16 imported, 187 proved, and 59 open.  VAAPC-I, UPTCR, and MLC remain open.

## 18. Research Push IV full-trace audit

Push IV correctly repairs the scalar trace-mode defect for a genuine
rectangle, but its proposed source-facing collar edge is invalid.  The
accepted abstract chain is

\[
\begin{gathered}
\texttt{FULL\_TRACE\_RECTANGLE\_DTN}\\
\Downarrow\\
\texttt{TRACE\_RESPONSE\_SEMIGROUP},
\quad
\texttt{EQUIPOTENTIAL\_COLLAPSE\_CRITERION},
\quad
\texttt{TRACE\_RENORMALIZED\_NECK\_ESTIMATE}\\
\Downarrow\\
\texttt{END\_TRACE\_RESPONSE\_COMPACTIFICATION},
\quad
\texttt{TRACE\_STABLE\_STRICT\_TRANSITION\_TRANSFER}.
\end{gathered}
\]

`HILBERT_TRACE_GLUE_CALCULUS` is an independent variational input to the
last transition node.  Every statement in this diagram is conditional on
an already supplied complete trace-compatible rectangle or response form.

The physical application has the different chain

\[
\begin{gathered}
\texttt{DIRECT\_DECORATION\_PULLBACK\_COMPACTIFICATION}
\quad+\quad
\texttt{PULLED\_EQUIPOTENTIAL\_SERIAL\_RECTANGLE\_NO\_GO}\\
\Downarrow\\
\texttt{DIRECT\_DECORATION\_TRACE\_COLLAR\_REALIZATION}
\quad(\text{open})\\
\Downarrow\\
\texttt{END\_PLUMBING\_TRACE\_RESPONSE\_CONTROL}
\quad(\text{open})\\
\Downarrow\\
\texttt{H2\_RESPONSE\_REALIZATION}
\quad(\text{open}).
\end{gathered}
\]

The no-go edge is necessary because inverse pullback divides the angular
footprint by \(2^q\).  It prevents the false inference that conformal copies
of a rectangle make the annular differences between nested copies into
serial rectangles.

The strict-transfer lemma does not introduce an edge to MBTT.  It requires
an independently proved root contraction and a physical accumulated
resistance large enough to meet its explicit margin.  Neither is supplied
by Push IV.

The ledger patch therefore adds nine proved local statements and one open
geometric interface, while retaining the principal plumbing gate as open.
After regeneration the expected totals are 272 obligations: 16 imported,
196 proved, and 60 open.  VAAPC-I, UPTCR, and MLC remain open.

## 19. Research Push V physical-contact and welding audit

Push V proves a conditional one-cell topology theorem and several narrow
variational identities.  It does not realize the iterated physical collar.
The accepted local chain is

\[
\begin{gathered}
\texttt{ACTIVE\_INACTIVE\_PHYSICAL\_CELL},
\quad
\texttt{ATTACHMENT\_ARC\_OPEN\_ATOM\_REFINEMENT},\\
\texttt{REGULAR\_INTERFACE\_FIBER\_PRODUCT\_RESPONSE},
\quad
\texttt{INFIMUM\_PUSHFORWARD\_FUNCTORIALITY},\\
\texttt{CLOSED\_FORM\_PUSHFORWARD\_NO\_GO},
\quad
\texttt{FIXED\_STANDARD\_NECK\_MULTIPORT\_COMPACTIFICATION}.
\end{gathered}
\]

The first node assumes that the complete boundary intersection of two
nested Jordan disks is exactly one arc.  It does not derive that
intersection pattern for the binary Kahn--Lyubich package.  The fiber
product node assumes a regular common Sobolev interface.  Infimum
pushforward is functorial only as an extended-valued variational identity;
the no-go node proves that arbitrary continuous projection does not
preserve closedness.  The compactification node assumes fixed Cartesian
cap spaces and fixed endpoint coordinates on a genuine standard neck.

The physical chain is instead

\[
\begin{gathered}
\texttt{DIRECT\_DECORATION\_PULLBACK\_COMPACTIFICATION}\\
\Downarrow\\
\left.
\begin{array}{c}
\texttt{DIRECT\_DECORATION\_ALL\_DEPTH\_CONTACT\_CLOSURE}\\
\texttt{FINITE\_LIVE\_COMMON\_REFINEMENT\_FRONTIER}\\
\texttt{DIRECT\_DECORATION\_TRACE\_WELDING\_COMPACTNESS}
\end{array}
\right\}
\quad(\text{all open})\\
\Downarrow\\
\texttt{DIRECT\_DECORATION\_TRACE\_COLLAR\_REALIZATION}
\quad(\text{open})\\
\Downarrow\\
\texttt{END\_PLUMBING\_TRACE\_RESPONSE\_CONTROL}
\quad(\text{open})\\
\Downarrow\\
\texttt{H2\_RESPONSE\_REALIZATION}
\quad(\text{open}).
\end{gathered}
\]

The new contact-closure edge is forced by the exact alternating-attachment
counterexample: shell \(C_1\) and shell \(C_3\) approach the same physical
arc while \(C_2\) does not, so a one-sided port reactivates and bypasses the
middle shell.  Pairwise consecutive refinement therefore cannot establish
the chronological crossing hypothesis of
`SERIAL_EXHAUSTION_RESISTANCE_BOUND`.

The welding edge is independent.  Whole-tail uniformization gives

\[
 (J_w^-\oplus J_w^+)^*
 \mathcal N_{R_w}
 (J_w^-\oplus J_w^+)
\]

in fixed physical coordinates.  Push V omits the word-dependent
\(J_w^\pm\).  Absorbing them into the caps makes the caps word-dependent;
finite combinatorial type supplies no compact analytic welding theorem.

The proposed promotion of `END_PLUMBING_TRACE_RESPONSE_CONTROL` with an
open dependency is also invalid under the machine semantics.  A proved
node must have discharged proof dependencies; a genuinely conditional
result must be a separate node with its assumptions explicitly typed.

At the close of the earlier Push-V snapshot, after adding six proved narrow
statements and three explicit open source-facing obligations, the ledger was
acyclic with 281 obligations: 16 imported, 202 proved, and 63 open.  These
figures are historical; the current ledger totals are recorded at the end of
the next section.  `VAAPC-I`, UPTCR, and MLC remained open.

## Side-research library integration

The cumulative side-library intake adds seven imported and six proved narrow
nodes, without changing any open status.  The imported nodes are
`BLOT_NONPARABOLIC_LIMIT_MODULUS_COLLAPSE`,
`FATOU_PARABOLIC_BASIN_CRITICAL_CYCLE`,
`CHERAGHI_SHISHIKURA_QG_MLC`,
`LEVIN_EXPONENTIAL_RENORMALIZATION_MLC`,
`LEVIN_FAST_SMALL_ROTATION_MLC`,
`LEVIN_THEOREM7_SATELLITE_MLC`, and
`ELEPHANT_EYES_APRIORI_BOUNDS`; their exact hypotheses and conclusion
boundaries are source-locked in `source_ledger.md`.  The six proved nodes
are:

\[
\begin{gathered}
\texttt{FATOU\_PARABOLIC\_BASIN\_CRITICAL\_CYCLE}
\Longrightarrow
\texttt{QUADRATIC\_PRIMITIVE\_ROOT\_PARABOLIC\_NONDEGENERACY},
\\
\texttt{BLOT\_NONPARABOLIC\_LIMIT\_MODULUS\_COLLAPSE}
\quad(\text{imported independently}),
\\
\texttt{FIXED\_MODULUS\_AMBIENT\_END\_NO\_GO},
\quad
\texttt{SERIAL\_ANNULUS\_SINGLETON\_BRIDGE},
\\
\texttt{MULTIPORT\_TRACE\_GAUGE\_AND\_STRICTNESS\_NO\_GO},
\quad
\texttt{WOT\_WELDING\_ALGEBRA\_NO\_GO},
\\
\texttt{DYADIC\_BOTTCHER\_EXTERNAL\_TRACE\_ISOMETRY}.
\end{gathered}
\]

The response-side dependency is sharpened to

\[
\begin{gathered}
\texttt{FIXED\_MODULUS\_AMBIENT\_END\_NO\_GO}
\;+\;
\texttt{SERIAL\_ANNULUS\_SINGLETON\_BRIDGE}
\;+\;
\texttt{MULTIPORT\_TRACE\_GAUGE\_AND\_STRICTNESS\_NO\_GO}
\\
\Downarrow\\
\texttt{DIRECT\_DECORATION\_TRACE\_COLLAR\_REALIZATION}
\quad(\text{open}),
\\[1ex]
\texttt{WOT\_WELDING\_ALGEBRA\_NO\_GO}
\;+\;
\texttt{DYADIC\_BOTTCHER\_EXTERNAL\_TRACE\_ISOMETRY}
\\
\Downarrow\\
\texttt{DIRECT\_DECORATION\_TRACE\_WELDING\_COMPACTNESS}
\quad(\text{open}).
\end{gathered}
\]

The first line says that fixed conjugated modulus is insufficient and gives
the exact sufficient serial-annulus implication once its physical
hypotheses are realized.  The second line gives one uniformly controlled
external coordinate but proves that weak-operator subsequence extraction
cannot supply the missing physical welding algebra.

No finite-lift node is added: the corrected conjugacy statement duplicates
`RETIMED_FINITE_CYLINDER_PAIR` and
`NORMALIZED_RETIMED_GERM_CONSTANCY`.  The neutral-attractor theorem reported
through the unavailable `[DLL26]` manuscript is not imported.  At the close
of this side-library snapshot, the ledger was acyclic with 294 obligations:
23 imported, 208 proved, and 63 open.  `VAAPC-I`, UPTCR, and MLC remained
open.

## Independent Push-V re-verification

The independent report received on 2026-07-25 corroborates the source
package, all-depth bypass, closed-form pushforward, welding, and numerical
conditioning audits.  It corrects one missing plus sign in the Markdown cap
estimate; the ledger and LaTeX estimate were already correct.

The source refinement is:

\[
 g=f^q|_{Q_L\cup Q_R},
 \qquad
 \{Q^v\}=\pi_0(\operatorname{dom}(g^n)).
\]

Thus the binary and \(2^n\)-piece families are related, but a one-step
branch and a length-\(n\) macrobranch are not interchangeable state
presentations.  The unresolved source task is to choose one granularity and
prove its complete physical contact data, or prove a component-level
transport theorem preserving that data.

The audit yields the proved finite compiler

\[
\texttt{FINITE\_TAME\_CONTACT\_OVERLAY\_RESPONSE},
\]

which identifies \(H^1\) of a finite Lipschitz cell overlay with the fiber
product of the cellwise \(H^1\) spaces over matching paired traces.  It
assumes the finite tame overlay and therefore does not close the source
geometry.

The open physical order is sharpened to

\[
\begin{gathered}
\texttt{DIRECT\_DECORATION\_ALL\_DEPTH\_CONTACT\_CLOSURE}\\
\Downarrow\\
\texttt{DIRECT\_DECORATION\_TRACE\_WELDING\_COMPACTNESS}\\
\Downarrow\\
\texttt{DIRECT\_DECORATION\_TRACE\_COLLAR\_REALIZATION}.
\end{gathered}
\]

The first node now requires canonical maximal contact atoms with full
incidence, active-side, phase, orientation, endpoint, and itinerary data.
The second explicitly depends on the first because the completed contact
structure determines its trace spaces and welding maps.  Weak-operator
subsequence extraction is not an algebra-compatible welding
compactification.

The ledger is acyclic with 295 obligations: 23 imported, 209 proved, and
63 open.  `VAAPC-I`, UPTCR, and MLC remain open.

## Research Push VI dependency correction

Push VI adds one proved local edge and does not promote a broad gate:

\[
\begin{gathered}
\texttt{DIRECT\_DECORATION\_PULLBACK\_COMPACTIFICATION}
\;+\;
\texttt{REGULAR\_INTERFACE\_FIBER\_PRODUCT\_RESPONSE}
\;+\;
\texttt{FINITE\_TAME\_CONTACT\_OVERLAY\_RESPONSE}
\\
\Downarrow\\
\texttt{BINARY\_DIRECT\_DECORATION\_NESTED\_SEPARATOR\_CALCULUS}
\quad(\text{proved}).
\end{gathered}
\]

The first dependency supplies the actual nested binary \(f^q\) pullbacks.
The latter two are invoked only conditionally after a finite admissible
Sobolev interface has been independently realized.  The new theorem proves
that an accumulated prefix can contact any future shell only on the current
separator and that physical boundary persistence is interval-convex.

The remaining dependency chain is

\[
\begin{gathered}
\texttt{BINARY\_DIRECT\_DECORATION\_NESTED\_SEPARATOR\_CALCULUS}
\\
\Downarrow\\
\texttt{DIRECT\_DECORATION\_ALL\_DEPTH\_CONTACT\_CLOSURE}
\quad(\text{open})
\\
\Downarrow\\
\left.
\begin{array}{c}
\texttt{FINITE\_LIVE\_COMMON\_REFINEMENT\_FRONTIER}\\
\texttt{DIRECT\_DECORATION\_TRACE\_WELDING\_COMPACTNESS}
\end{array}
\right\}
\quad(\text{open})
\\
\Downarrow\\
\texttt{DIRECT\_DECORATION\_TRACE\_COLLAR\_REALIZATION}
\quad(\text{open})
\\
\Downarrow\\
\texttt{END\_PLUMBING\_TRACE\_RESPONSE\_CONTROL}
\quad(\text{open})
\\
\Downarrow\\
\texttt{H2\_RESPONSE\_REALIZATION}
\quad(\text{open}).
\end{gathered}
\]

The second line is not redundant.  It must still construct the marked
multi-branch separator interface, an incidence-valued boundary transport,
the correctly grounded homogeneous trace category, the stage-normalized
protected overlay, and final-root-enlargement naturality.

The submitted Push-VI graph is rejected because its finite atom-to-atom map
fails in the expanding-ray model, its protected overlay is not a fixed
root-cell catalog, and its full-\(H^1\) trace norm is not conformally
isometric.  Consequently there are no valid edges from the local separator
theorem directly to a compact response cocycle, H2, or MBTT.

The current ledger is acyclic with 296 obligations: 23 imported, 210
proved, and 63 open.  VAAPC-I, H2, MBTT, H3, H4, UPTCR, and MLC remain
open.

## Research Push VII dependency correction

Push VII adds two narrow proved nodes:

\[
\begin{gathered}
\texttt{KL\_DECORATION\_ESCAPE\_PUZZLE}
\;+\;
\texttt{DIRECT\_DECORATION\_PULLBACK\_COMPACTIFICATION}
\;+\;
\texttt{BINARY\_DIRECT\_DECORATION\_NESTED\_SEPARATOR\_CALCULUS}
\\
\Downarrow\\
\texttt{FIXED\_BLOCK\_BINARY\_CONTACT\_AUTOMATON}
\quad(\text{proved}),
\end{gathered}
\]

and

\[
\begin{gathered}
\texttt{KKL\_VALUE\_CONTRACTION}
\;+\;
\texttt{KKL\_TYPED\_VALUE\_INCIDENCE}
\\
\Downarrow\\
\texttt{FIXED\_KKL\_PAIR\_STATE\_MOMENT\_FACTORIZATION}
\quad(\text{proved}).
\end{gathered}
\]

The first theorem determines the unmarked structural contact skeleton for
one fixed actual binary decoration block.  It proves exact normalized
contact recursion, all pairwise cylinder contacts, prefix endpoint deletion,
and the post-source-depth states consisting of the complete
\(\alpha\)-ray port or the empty state.  It does not bound the state
uniformly in \(q,n\) and does not include protected, obstacle, carrier,
trace, WAD, Value, or enlargement marks.

The second theorem rewrites KKL Value on one fixed finite terminal Hubbard
tree as a linear functional of a positive-semidefinite pair-state moment.
Its dimension depends on the terminal edge set.  The direct-decoration
branch-to-Hubbard incidence, completely positive transport, universal
dimension, and future-observability gap remain open.

There is no valid edge from either theorem directly to response realization
or MBTT.  The dependency chain remains

\[
\begin{gathered}
\texttt{FIXED\_BLOCK\_BINARY\_CONTACT\_AUTOMATON}
\\
\Downarrow\\
\texttt{DIRECT\_DECORATION\_ALL\_DEPTH\_CONTACT\_CLOSURE}
\quad(\text{open})
\\
\Downarrow\\
\left.
\begin{array}{c}
\texttt{FINITE\_LIVE\_COMMON\_REFINEMENT\_FRONTIER}\\
\texttt{DIRECT\_DECORATION\_TRACE\_WELDING\_COMPACTNESS}
\end{array}
\right\}
\quad(\text{open})
\\
\Downarrow\\
\texttt{DIRECT\_DECORATION\_TRACE\_COLLAR\_REALIZATION}
\quad(\text{open})
\\
\Downarrow\\
\texttt{END\_PLUMBING\_TRACE\_RESPONSE\_CONTROL}
\quad(\text{open})
\\
\Downarrow\\
\texttt{H2\_RESPONSE\_REALIZATION}
\quad(\text{open}).
\end{gathered}
\]

The missing first arrow now has a sharper meaning: construct the
connector-aware complete marked overlay, both the dynamical covering and
inclusion-immersed interface copies, admissible ideal-arc trace Hilbert
spaces, the welding/relative-cover correspondence, and protected
final-root naturality.

The proposed fifteen-node Push-VII patch is rejected.  Its pseudo-trace and
response nodes bypass these open analytic dependencies, its generic
Kronecker identity is supporting algebra rather than a geometric quotient,
and its new open umbrella duplicates live gates.

The ledger is acyclic with 298 obligations: 23 imported, 212 proved, and
63 open.  VAAPC-I, H2, MBTT, H3, H4, UPTCR, and MLC remain open.

## Research Push VIII dependency correction

Push VIII does not construct the actual marked pulled/immersed interface.
Its valid finite contribution has the deliberately isolated type

\[
\text{declared finite label-hull model}
\Longrightarrow
\texttt{FINITE\_LINEAR\_LABEL\_MARKING\_ENUMERATOR}
\quad(\text{proved}).
\]

There is no reverse edge from the enumerator to an actual KKL immersion
pullback.  That missing realization requires proper target paths, unique
proper lifts, subordination homotopy, relative-cover subgroup data, and
component exhaustion.  The source-facing chain is therefore

\[
\begin{gathered}
\texttt{FINITE\_LINEAR\_LABEL\_MARKING\_ENUMERATOR}
\\
\text{plus actual path-lift/component-exhaustion certificate}
\\
\Downarrow\\
\texttt{DIRECT\_DECORATION\_ALL\_DEPTH\_CONTACT\_CLOSURE}
\quad(\text{open}).
\end{gathered}
\]

The proposed welding word law is blocked independently:

\[
\texttt{PULL\_PUSH\_WELDING\_WORD\_COMPOSITION\_NO\_GO}
\quad(\text{proved}).
\]

For consecutive correspondences, \(W_j=P_jR_j\) acts on the target trace
space at stage \(j\).  The one-step operators are not typed to compose
without additional identifications, and even after an artificial
identification the composite-pair factor order need not equal the
chronological product.  A valid edge to word naturality must pass through an
actual fiber-product span and a Beck-Chevalley/interchange square:

\[
\begin{gathered}
\text{path-lifted pulled/immersed pair}
\;+\;
\text{whole-end-interval properness}
\;+\;
\text{coherent collar maps}
\;+\;
\text{fiber-product/interchange square}
\\
\Downarrow\\
\texttt{DIRECT\_DECORATION\_TRACE\_WELDING\_COMPACTNESS}
\quad(\text{open})
\\
\Downarrow\\
\texttt{DIRECT\_DECORATION\_TRACE\_COLLAR\_REALIZATION}
\quad(\text{open}).
\end{gathered}
\]

The Push-VIII compiler does not discharge these premises.  Its advertised
success fixture violates its own degree-one covering-atom axiom, almost all
random tables are nonrealizable, and its end-proper flag tests edge
micro-atoms instead of whole \(f^*\mathcal I\) end intervals.  Compiler
success can therefore occur with no component carrying the required proper
source path and no pulled multi-interval on which the immersion is
end-proper; it does not imply that a welding operator exists.

The proposed final-root node also has no new valid edge.  The already proved
`MARKED_PAIR_ENLARGEMENT_NATURALITY` remains a conditional endpoint theorem;
complete trace naturality additionally requires a bijection of proof-used
pullback components, no new sheet or nonproper bridge, relative-cover
subgroup compatibility, and coherent collar transport.

The thirteen proposed analytic promotions and the duplicate universal open
umbrella are rejected.  At this first Push-VIII integration point, no
pre-existing open status changed; the two narrow finite/no-go additions gave
300 obligations: 23 imported, 214 proved, and 63 open.

### Source-specific path-lifted continuation

The subsequent
[direct-decoration path-lifted collar certificate](direct_decoration_path_lifted_collar_certificate.md)
starts from an actual fixed Kahn--Lyubich direct-decoration branch.  Its
original embedding promotion was retracted after a hostile source audit.
The corrected statuses are:

```text
DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING            [OPEN; NON-GATING RESTRICTED CLASS]
DIRECT_DECORATION_TILE_CENTRAL_OVERLAP_REFLECTION        [OPEN; NON-GATING SATURATION]
DEGREE_ONE_ANNULUS_IMMERSION_INJECTIVITY_NO_GO           [PROVED]
KAHN_ANNULUS_GLOBAL_INJECTIVITY_NO_GO                    [PROVED]
KL_TILE_INJECTIVITY_BASE_ANNULUS_REDUCTION               [PROVED]
KL_CANONICAL_LOCALIZATION_FORCED_COLLISION               [PROVED]
TILE_INJECTIVITY_GLUE_EMBEDDING_CRITERION                [PROVED]
KL_TILE_INTERIOR_HOMOGENEOUS_TRACE                       [PROVED]
NONPROPER_LABEL_HULL_PULLBACK_NO_GO                      [PROVED]
DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION      [OPEN]
```

The component map is bijective.  A later relation-reflection audit removed
an overstrong dependency from the full-pair theorem.  For the unique
\(i\) with \(j(i)=j\),

\[
 Q\cap P_j=Q_i.
\]

Thus a tile--central collision can see only the target overlap over
\(Q_i\).  Forward overlap commutation and injectivity of the **full** tile
map reflect this relative overlap automatically.  A complete
central/central, same-tile, different-tile, and tile/central audit gives

\[
 \boldsymbol\iota:\mathbf Q\to\mathbf P\text{ injective}
 \quad\Longleftrightarrow\quad
 \text{every full tile map is injective}.
\]

Full inverse-image reflection over all of \(P_j\) is stronger than needed
and remains only a non-gating saturation question.  KL still supply only
tile immersions at a general \(\psi\)-ql stage, so the full embedding gate
remains open.  The explicit map
\(z+a e^{2\pi iz}/(2\pi i)\) is a locally univalent degree-one strip map
with a same-tile self-collision, so degree plus immersion cannot discharge
the missing premise.

The second proved node has the deliberately narrow type

\[
\begin{gathered}
J\Subset\operatorname{relint}(\text{one KL universal-cover tile arc})
\\
\Downarrow\\
\text{a selected coordinate-Lipschitz quadrilateral collar}
\\
\Downarrow\\
\dot{\mathcal T}(J)
=
\operatorname{Tr}_{J}
\left\{
u\in H^1_{\mathrm{loc}}(Q):
\int_Q|\nabla u|^2<\infty
\right\}/\mathbb R
\quad\text{is Hilbert}.
\end{gathered}
\]

A conformal isomorphism between the selected transported collars is an exact
isometry for this homogeneous minimum-energy quotient.  This node supplies
no canonical collar, no collar across the globally glued pseudo-boundary, no
physical Julia-boundary collar, no full gauge, no uniform comparison between
independently selected collars, and no word or immersion naturality.  Those
omissions are dependencies, not cosmetic qualifications.

The third proved node is an analytic counterexample to a reverse edge from
the finite enumerator.  Let the source disk embed conformally as the upper
half-disk in the target disk.  The source arc mapped to the upper target
circle is proper, while the source arc mapped to the diameter is nonproper.
For the upper/lower two-interval target marking, the deletion-and-seed label
hull of the upper interval retains every open source atom, including the
nonproper diameter-side atom.  A target proper
crosscut with both ideal endpoints in the lower interval, however, has a
unique source proper lift subordinate to a nondegenerate part of the
diameter-side arc.  It is not subordinate to the upper interval.  Hence the
KKL implication excludes that source arc, and

\[
\texttt{FINITE\_LINEAR\_LABEL\_MARKING\_ENUMERATOR}
\not\Longrightarrow
\text{actual KKL immersion pullback}.
\]

The remaining actual obstruction must now be named sheetwise.  The proved
canonical collision supplies a non-base element of the pointed coset set
\[
 \mathscr S_{\rm loc}=a_*^{-1}(H_t)/H_s.
\]
Thus the full canonical map cannot be inserted into the embedded-disk
safe-set theorem.  For every source prime end \(p\) and every retained
\(\mathfrak s\in\mathscr S_{\rm loc}\), the footprint record must include
\[
 \mathfrak F(p,\mathfrak s)
 =
 \left(
 \mathfrak s,\overline{\boldsymbol\iota}(p),
 \{(C,\mathfrak s):C\text{ lands at }
      \overline{\boldsymbol\iota}(p)\},
 \Phi(p,\mathfrak s)
 \right),
\]
together with the central component, tile side, wrapping or vertex access,
target ideal footprint, sheet, localization coset, and return word.

The outer-side component is resolved only in the additional
common-coordinate model.  A general degree-one annulus immersion need not
be a translation or exact lower strip, as witnessed by
\(z+\varepsilon\sin(2\pi z)\).  Therefore the sheet-sensitive actual KL
\(O\)-footprint remains open.

The source-specific sequence is now: retain every live localization coset
and sheet; compute the complete \(O\)-side footprint on each; compute the
nonproper \(\xi/\eta\) central-seam footprints with the same state; prove a
sheet-sensitive replacement for the embedded formula; and prove
family-level pullback disjointness, covering refinement, and
proper/end-proper action.  A retained-collar alternative must instead
record and charge every discarded coset and sheet.  Whole covering end
intervals, subgroup, deck phase, cyclic order, and sheet multiplicity must
survive this classification.

The corrected local dependency graph is therefore

\[
\begin{gathered}
\texttt{KL\_DECORATION\_ESCAPE\_PUZZLE}
\Longrightarrow
\begin{cases}
\texttt{TILE\_INJECTIVITY\_GLUE\_EMBEDDING\_CRITERION},\\
\texttt{KL\_TILE\_INTERIOR\_HOMOGENEOUS\_TRACE},\\
\texttt{KL\_PSEUDOPIECE\_CONFORMAL\_IDEAL\_BOUNDARY},
\end{cases}
\\[1mm]
\texttt{DEGREE\_ONE\_ANNULUS\_IMMERSION\_INJECTIVITY\_NO\_GO}
\quad(\text{proved independently}),
\\[1mm]
\texttt{KAHN\_ANNULUS\_GLOBAL\_INJECTIVITY\_NO\_GO}
\quad(\text{proved independently; full abstract Kahn-annulus hypotheses}),
\\[1mm]
\texttt{KL\_DECORATION\_ESCAPE\_PUZZLE}
\Longrightarrow
\texttt{KL\_TILE\_INJECTIVITY\_BASE\_ANNULUS\_REDUCTION}
\quad(\text{proved}),
\\[1mm]
\texttt{GENERAL\_ANNULUS\_IMMERSION\_LOWER\_STRIP\_NO\_GO}
\quad(\text{proved independently}),
\\[1mm]
\texttt{KKL\_IDEAL\_PULLBACK\_NATIVE}
\Longrightarrow
\texttt{EMBEDDED\_DISK\_ACCESSIBLE\_FOOTPRINT\_THEOREM},
\\[1mm]
\texttt{KL\_CANONICAL\_LOCALIZATION\_FORCED\_COLLISION}
\quad(\text{proved})
\Longrightarrow
\text{full canonical pseudo-piece embedding unavailable},
\\[1mm]
\texttt{DIRECT\_DECORATION\_DEGREE\_ONE\_PSEUDO\_EMBEDDING}
\quad(\text{open, restricted-class, non-gating, no descendants}),
\\[1mm]
\texttt{KL\_CANONICAL\_LOCALIZATION\_FORCED\_COLLISION}
+
\texttt{KL\_PSEUDOPIECE\_CONFORMAL\_IDEAL\_BOUNDARY}
+
\texttt{GENERAL\_ANNULUS\_IMMERSION\_LOWER\_STRIP\_NO\_GO}
\\
\Downarrow\\
\texttt{DIRECT\_DECORATION\_OUTER\_CAP\_FOOTPRINT}
\quad(\text{open: sheet-sensitive actual KL \(O\)-footprint})
\\[1mm]
\text{common-coordinate hypothesis (CI)}
+
\texttt{TILE\_INJECTIVITY\_GLUE\_EMBEDDING\_CRITERION}
+
\texttt{KL\_PSEUDOPIECE\_CONFORMAL\_IDEAL\_BOUNDARY}
+
\texttt{EMBEDDED\_DISK\_ACCESSIBLE\_FOOTPRINT\_THEOREM}
\Longrightarrow
\texttt{COMMON\_COORDINATE\_NESTED\_ANNULUS\_OUTER\_CAP}
\quad(\text{proved under its explicit common-coordinate hypothesis}),
\\[1mm]
\texttt{DIRECT\_DECORATION\_OUTER\_CAP\_FOOTPRINT}
+
\texttt{NONPROPER\_LABEL\_HULL\_PULLBACK\_NO\_GO}
\\
\Downarrow\\
\texttt{DIRECT\_DECORATION\_PSEUDO\_PIECE\_PATH\_LIFT\_EXHAUSTION}
\quad(\text{open})
\\
\Downarrow\\
\texttt{DIRECT\_DECORATION\_ALL\_DEPTH\_CONTACT\_CLOSURE}
\quad(\text{open}).
\end{gathered}
\]

Trace-word composition remains conditional.  For collared spans

\[
X\xleftarrow aM\xrightarrow bY,
\qquad
Y\xleftarrow cN\xrightarrow dZ,
\qquad
P=M\times_YN,
\]

with projections \(p:P\to M\) and \(q:P\to N\), the formal calculation is

\[
d_*c^*b_*a^*
=d_*q_*p^*a^*
=(d\circ q)_*(a\circ p)^*
\]

only after proving the Beck--Chevalley identity

\[
c^*b_*=q_*p^*.
\]

For the analytic application this requires a Cartesian square of selected
collars, the same fibers and multiplicities on both sides, actual proper
collar branches, compatible connected homogeneous quotients or transported
gauges, whole-end properness, and explicit treatment of every nonproper
middle arc.  Thus `DIRECT_DECORATION_TRACE_WELDING_COMPACTNESS` and
`DIRECT_DECORATION_TRACE_COLLAR_REALIZATION` remain open.

Final-root enlargement has an independent no-birth dependency.  Commutation
on the old subdiagram and equality of old endpoint inverse images do not
exclude a new source sheet or nonproper bridge over the enlarged interval.
The required theorem must give a component bijection between all old and
enlarged proof-used lifts and preserve the based cover subgroup, deck phase,
subordination class, proper/nonproper status, whole-end decomposition, and
collar component.

The abstract whole-annulus route now has two additional exact terminal
results.  `PSI_QL_GLOBAL_INJECTIVITY_NO_GO` constructs a complete
degree-two \(\psi\)-quadratic-like pair satisfying the proper companion,
common connected inverse, local embedding, and complementary degree-one
clauses while retaining a remote self-collision.  Therefore the complete
abstract \(\psi\)-ql axiom package cannot discharge
`DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING`.

For an actual localization of a physical embedding,
`KL_LOCALIZATION_SUBGROUP_REFLECTION_CRITERION` gives the exact remaining
cover condition:

\[
 \widehat a\text{ injective}
 \quad\Longleftrightarrow\quad
 a_*^{-1}(H_t)=H_s.
\]

Kahn's localization functor proves only
\(a_*(H_s)\subseteq H_t\), which is the lift-existence direction.
The missing equality is equivalent to reflecting target path equivalence
back to source path equivalence.  A failure class
\([\gamma]\in a_*^{-1}(H_t)\setminus H_s\) supplies the two distinct source
lift endpoints and their common target endpoint.

The new source-locked theorem
`KL_CANONICAL_LOCALIZATION_FORCED_COLLISION` realizes exactly this failure
at every ordinary primitive canonical seed.  Let
\[
 F=f^p:U^p\to U^0,\qquad
 A=K_p,\qquad
 B=\mathcal K_p.
\]
The physical inclusion
\[
 a=i^p:
 U^p\setminus F^{-1}B\hookrightarrow U^0\setminus B
\]
is an embedding, so the subgroup-reflection criterion applies.  Global
degree \(2^p\) and central degree two produce an excess component
\(X\ne A\) of \(F^{-1}A\).  A finite full-pullback lemma makes
\(F^{-1}B\) a finite family of pairwise-disjoint full continua.
Primitivity and \(F(K_p(j))=K_p(j)\) give \(X\cap B=\varnothing\), so a
Jordan disk \(D_X\Subset U^p\) isolates \(X\) from both \(B\) and the other
pulled components.  A based peripheral loop \(\gamma\) has winding one
about \(X\), while every source-local loop has winding zero; hence
\[
 [\gamma]\notin H_s.
\]
The same loop contracts across \(D_X\) after physical inclusion into the
target complement, so
\[
 a_*[\gamma]=1\in H_t.
\]
Thus \(a_*^{-1}(H_t)/H_s\) is nontrivial and the actual localized inclusion
is noninjective.

Kahn's exact equalizer pullback
\[
 \mathbf U^{r+2}
 =\{(x,y):i_r(x)=f_r(y)\},
 \qquad i_{r+1}(x,y)=y
\]
propagates the point collision to every later \(i_r\).  Whenever the same
seed carries KL direct-decoration data, it therefore reaches the exact
depths
\[
 m=\nu q+1,\qquad n=(\nu-1)q+1,
\]
and the degree-one deck calculation forces a collision in every full tile
lift and in the full glued pseudo-piece immersion.  The same-seed
stage-alignment implication is kept explicit; it is not used to assert an
unsourced parameter subclass.

Consequently the former universal embedded-pseudo-piece route has no
descendants in the authoritative ledger.  The \(O\)-footprint,
path-exhaustion, and all-depth contact nodes now depend on
`KL_CANONICAL_LOCALIZATION_FORCED_COLLISION` and require a sheet-sensitive
path groupoid retaining every live coset in
\[
 a_*^{-1}(H_t)/H_s.
\]
At a genuinely general bold stage whose underlying map is already only an
immersion, a base-point collision remains a separate obstruction; the
canonical theorem does not erase that typing distinction.

The new proved node
`KL_LOCALIZATION_SHEET_RESOLUTION_FACTORIZATION` constructs the required
cover-level groupoid without pretending that the localized inclusion is
embedded.  If
\[
 K=a_*^{-1}(H_t),
\]
the selected component \(P_K\) of
\(X_s\times_{X_t}\widehat X_t\) is the \(K\)-cover, and
\[
 \widehat X_s\xrightarrow qP_K\xrightarrow e\widehat X_t,
 \qquad A=e\circ q,
\]
with \(q\) a covering and \(e\) embedded.  The kernel pairs of \(A\) and
\(q\) agree, and this is the unique connected intermediate-cover
factorization with embedded second leg in the based, commuting comparison
class stated in the proof.

The defect is infinite, not merely nontrivial.  Winding gives
\[
 w(H_s)=0,\qquad w(\gamma)=1,\qquad\gamma\in K,
\]
so the cosets \(\gamma^nH_s\) are pairwise distinct and
\[
 [K:H_s]=\infty.
\]
Consequently raw finite sheet enumeration is impossible.  The category of
elements of the monodromy functor of \(q\) is the exact state; any finite
downstream representation must be proved future-faithful for all path,
access, and Value observables.

Once a typed covering/embedding factorization has been supplied, exact
base change preserves it through the full, unselected Kahn equalizers on
the complementary-cover locus.  Exact base change does not itself prove
that the canonical infinite sheet-resolution factorization is the
covering/embedding factorization of a whole actual KL tile.

The new proved node
`KAHN_ITERATE_COMPLEMENTARY_COMPONENT_ALIGNMENT` closes the ambient
component and fixed-seed interior typing that base change alone left open.
Kahn's membership chain identifies the full complementary equalizer with
the fiber product of the two complementary annuli, and the disk/FJ
pullback theorem makes that equalizer connected.  Surjectivity of the
base-changed \(q\)-cover makes the resolved intermediate connected
**provided the annular \(q/e\) factorization is separately supplied**.
Because the inclusion immersion has oriented annular degree \(+1\), for
each source tile \(a\) the pullback of its declared target tile
\(j_\iota(a)\) is the connected source universal-cover tile after the KL
lifted basepoints fix the deck phase.  Distinct source labels over a
repeated target index are retained.  Conditional on the typed annular
\(q/e\) input, its base change gives a connected resolved intermediate
embedded tilewise in the target.
For one fixed seed, KL's \(\mathbf U^m\)-tower is Kahn's same iterate
tower.

This node is family-valued over the separately glued KL tiles.  It does
not collapse those tiles, identify the dynamical covering component map
with the inclusion component map, extend either \(q/e\) factor to an ideal
boundary, or assert that every canonical seed realizes prescribed
direct-decoration combinatorics.  In particular, it does not identify
the canonical infinite sheet-resolution cover with a whole actual KL
tile.

The new proved node
`RESOLVED_INTERMEDIATE_RELATIVE_IDEAL_BOUNDARY` determines the exact
boundary obstruction and the strongest presently justified replacement.
For a typed analytic annular factorization
\[
 A_s\xrightarrow qP\xrightarrow eA_t,\qquad eq=\iota,\qquad
 \iota_*=\operatorname{id}_{\mathbb Z},
\]
put
\[
 G=\pi_1(P),\qquad H=q_*\pi_1(A_s),\qquad N=\ker e_*.
\]
Then \(G=N\rtimes H\).  In the single based universal-cover action, the
tilewise pullback \(q_a:\mathcal E_a\to\mathcal R_a\) is the universal
cover with deck group literally \(N\leq G\), and its fibers are
canonically the fibers of \(q\).

If \(\zeta\in\Lambda(N)\), a sequence of deck transformations sends every
point of \(\mathbb D\) to \(\zeta\) while \(q_a\), and every
nonconstant \(N\)-invariant composite, is constant on each deck orbit.
Continuity at \(\zeta\) would therefore identify all interior image
points.  Thus no nontrivial resolved universal cover has a continuous
point-valued extension through its deck limit set.  The positive
replacement is exact quotient descent only on a supplied
\(N\)-invariant set
\[
 J\subset\Omega(N)=\partial\mathbb D\setminus\Lambda(N).
\]
This is a relative ideal bordification, not a full prime-end extension.

KL's source-defined tile presents a sharper compatibility test.  Their
strip uniformization identifies actual-tile fixed endpoints
\(\omega_\pm\) with the two named infinitely wrapping \(\lambda/J\)
vertices, and their actual inclusion-induced tile map \(L_a\) extends
continuously there.  The based source-cover biholomorphism extends with
\(\overline\Phi_a(\omega_\pm)=\zeta_\pm\), and the transported
resolved-source composite is \(K_a=L_a\Phi_a^{-1}=e_aq_a\).  If that
whole actual tile map admitted the same covering/embedding factorization
with \(N\ne1\), normality forces \(\zeta_\pm\) into \(\Lambda(N)\), while
the invariant-composite
no-go forbids the asserted continuous limits.  Hence every such
whole-actual-KL-tile factorization is one-sheeted.  The former
canonical-infinite-cover/whole-KL-tile identification is quarantined;
the abstract equalizer and conditional base-change theorems remain
valid.

The correspondence audit now proves that the **whole-tile** comparison
square does not exist for the canonical infinite kernel.  A based
source-cover biholomorphism would transport a deck sequence to KL's named
wrapping vertex, and composite commutation plus target separation would
make the source-locked boundary value equal to every interior value.
This promotes
`CANONICAL_KL_WHOLE_TILE_CORRESPONDENCE_NO_GO`.

The next audit constructs one restricted branch.  For every **supplied
fixed labeled same-source datum**, the based source-cover isomorphism
defines
\[
 \mathcal R\mathop{\longleftarrow}^{q}\mathcal E
 \mathop{\longrightarrow}^{K}\widehat A_t^{\rm KL}.
\]
For a target path, the tagged disjoint union of its fiber products over
all declared source labels is an étale space; its path components are
exactly the maximal parameter-compatible interior lifts.  This proves
enumeration without descending through \(q\), identifying labels, or
asserting proper endpoints.  The two transported wrapping values are
common clusters of every \(q\)-fiber orbit.  KL does not supply the
standalone-tile extension needed to make the same claim on all of
\(\Lambda(N)\).

The same classification closes two nominated alternatives narrowly.
Exact finite base change preserves the full \(q\)-fiber, so selection of a
later unchanged Kahn equalizer cannot make an infinite factor
one-sheeted.  The identity inclusions
\(\mathbb A(1,e^{\varepsilon/2})\hookrightarrow
\mathbb A(1,e^\varepsilon)\) show that Kahn's hypotheses do not bound the
**unscaled** additive difference of complete collar and target crossing
widths.  This does not refute calibrated or source-specific responses.
A revised localization satisfies the algebraic one-sheet criterion only
after its based lift condition is supplied.

The subsequent geometric-trace audit proves P154 and P155.  In particular,
path properness, map properness on an ideal subset, and end-properness on
complete pulled end-intervals have different types.  The corrected open
chain is

\[
\begin{gathered}
\texttt{DIRECT\_DECORATION\_WAVE\_PROOF\_USE\_LEDGER}\\
\Downarrow\\
\texttt{DIRECT\_DECORATION\_CANONICAL\_KL\_STAGE\_ALIGNMENT}\\
\Downarrow\\
\texttt{DIRECT\_DECORATION\_RELATION\_PROPER\_PATH\_END\_INTERVAL\_CLASSIFICATION}\\
\swarrow\qquad\searrow\\
\texttt{DIRECT\_DECORATION\_CANONICAL\_KL\_RELATION\_PROPER\_END\_RESPONSE}
\qquad
\texttt{DIRECT\_DECORATION\_FINAL\_ROOT\_RELATION\_NO\_BIRTH}.
\end{gathered}
\]

The two last nodes are parallel: the response node proves the
Value-observable analytic charge, while final-root proves Cartesian
geometric no-birth.  The former feeds the physical outer-footprint node;
the latter feeds final path-lift exhaustion.

Connectedness still gives no filled or prime-end extension.  Nor does compact path lifting
imply the KKL unique-proper-lift predicate: every footprint witness must
isolate one proper coset or classify every competing proper lift.  The
safe-set reduction additionally requires the endpoint-subordination axioms
on an authorized ideal-boundary model; it cannot infer them from a
ribbon-tree quotient.

For an enlargement homomorphism \(\varphi\), the based coset map is
injective exactly when
\[
 K\cap\varphi^{-1}(H_s^+)=H_s
\]
and surjective exactly when
\[
 K^+=\varphi(K)H_s^+.
\]
These equalities do not prove geometric no-birth.  All groups can be
trivial while a simply connected lobe adds a new path or access.
Therefore the final-root gate still requires a Cartesian geometric cover
square, complete component/path-fiber bijection, obstacle and
nonproper-bridge audit, and authorized endpoint compatibility.

The proved `FINITE_HORIZON_KAHN_COLLAR_EMBEDDING` supplies a strictly
smaller replacement domain.  For one fixed finite chain, embedded central
maps, bijective tile-component maps, exact gluing, and Kahn degree-one
base-annulus data, together with the additional overlap-reflection
equality on the retained Kahn collars, imply the existence of coherent
distinguished inner collars.  Finite inverse-germ shrinking makes every retained base map
biholomorphic; deck equivariance and the quotient-collision audit make
every collar-truncated pseudo-piece map an embedding.  With separately
supplied conformal-disk prime-end extensions and complete footprints, the
maximal connected marked pullbacks are the connected components of the
safe set \(\{p:\Phi_H(p)\subset I\}\).

This node does not imply
`DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING`: omitted outer-return
sheets are outside its domain, and the checked Kahn/KL sources do not prove
global univalence on those full tiles.  The collar-level reflection
equality is an explicit hypothesis of the truncated theorem, not an
additional dependency of the full-pair gluing theorem.  Nor does it imply
`DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION`,
`DIRECT_DECORATION_TRACE_COLLAR_REALIZATION`, or final-root naturality.
Those descendants still require actual proof-use exhaustion or a uniform
outer-defect charge, complete footprints, subgroup and whole-end
compatibility, and a no-birth/no-loss theorem.  Safe-set connectedness and
finite footprint state are also not consequences of a finite horizon.

At this earlier dependency-audit checkpoint, the authoritative ledger was
acyclic with 407 obligations: 25 imported, 283 proved, and 99 open.  No global
gate was promoted:
`VIRTUAL_WAVE_MARKED_CORRESPONDENCE`,
`VIRTUAL_WAVE_HORIZON_CERTIFICATE`, VAAPC-I,
`H2_RESPONSE_REALIZATION`, MBTT, H3, H4,
`UNIVERSAL_PROTECTED_TOWER_CLOSURE`, and MLC all remain open.

## 20. Terminal dense-obstacle reroute and crest-compatible width branch

The terminal dependency graph formerly treated an obstacle-free native
collar as the prospective positive gate.  That route is now closed
negatively.  The proved dependencies are
\[
\begin{gathered}
\text{Douady--Hubbard external prime-end exactness}
\\
{}\quad+\quad
\texttt{TERMINAL\_LC\_NATIVE\_HUBBARD\_CARRIER\_PROPER}
\\
{}\quad+\quad
\texttt{TERMINAL\_ACCESS\_SURVIVAL\_EQUIVALENCE}
\\
\Downarrow\\
\texttt{TERMINAL\_FORWARD\_INVARIANT\_CARRIER\_DENSE\_OBSTACLE\_NO\_GO}.
\end{gathered}
\]
For a proper forward-invariant carrier, the relative obstacle
\(K\setminus T\) accumulates at every inner prime end.  Thus no descendant
may require a nondegenerate obstacle-free terminal collar as a universal
hypothesis.

The width branch is instead
\[
\begin{gathered}
\texttt{TERMINAL\_KL\_ORDERED\_MULTICURVE\_OVERFLOW}
\\
{}\quad+\quad
\text{KL Lemma `lifts'}
\\
\Downarrow\\
\texttt{TERMINAL\_KL\_SUBMULTICURVE\_OVERFLOW\_TRANSFER}
\\
\Downarrow\\
\texttt{TERMINAL\_WAVE\_KL\_CONNECTING\_SUBFAMILY}
\quad(\text{open})
\\
\Downarrow\\
\texttt{TERMINAL\_KL\_SUBMULTICURVE\_BINDER\_SELECTOR}
\quad(\text{open}).
\end{gathered}
\]
The proved transfer has sharp coefficient one.  The first open arrow is
geometric, not analytic bookkeeping: for every retained Wave occurrence
it must produce a literal physical restriction joining one fixed pair of
KL exterior continua, with order and multiplicity retained.

For KKL's native Wave theorem, the source-stated amplification node now
has two independent proof-repair predecessors:
\[
\begin{gathered}
\texttt{KKL\_BOUNDED\_VISITS\_INTERVAL\_GROWTH\_REPAIR}
\quad(\text{open})
\\
{}\quad+\quad
\texttt{KKL\_PARABOLIC\_WAVE\_STATIONARY\_PROOF\_REPAIR}
\quad(\text{open})
\\
\Downarrow\\
\texttt{KKL\_PARABOLIC\_WAVE\_AMPLIFICATION}
\quad(\text{open, source-stated}).
\end{gathered}
\]
The first repair must justify the corrected
\(6b+k-1\) interval count, a strict pigeonhole excess, and an
interval-level strict-growth or no-periodicity lemma.  Global
Perron--Frobenius expansion alone does not exclude a periodic marked
interval.

The native stationary proof-repair subchain is
\[
\begin{gathered}
\texttt{PQL\_ITERATE\_FILLED\_GRAPH\_NATURALITY}
\quad(\text{proved})
\\
\Downarrow\\
\texttt{KKL\_STATIONARY\_FINAL\_COMPONENT\_REALIZATION}
\quad(\text{proved})
\\
\Downarrow\\
\texttt{KKL\_STATIONARY\_DEGREE\_TWO\_CORRECTION}
\quad(\text{proved})
\end{gathered}
\]
Independently, filled-set graph naturality constructs the canonical lifts
of \(K_0^b\) and \(K_0^{b+1}\), proves that they are whole, distinct
components of the single final \(\mathcal K^{N-1}\), and shows that each
selected final restriction has degree two, not the degree one printed in
KKL.  These filled-set facts do not validate the occurrence argument at
KKL line 1603.

The occurrence chain is now typed separately:
\[
\begin{gathered}
\texttt{KKL\_STATIONARY\_ONE\_RETAINED\_CHAIN}
\quad(\text{proved})
\\
{}\quad+\quad
\texttt{PQL\_STRICT\_SYNCHRONIZED\_CHAIN\_RECONSTRUCTION}
\quad(\text{proved special case})
\\
\Downarrow\\
\texttt{PQL\_SEGMENTED\_OCCURRENCE\_RECONSTRUCTION}
\quad(\text{proved})
\\
{}\quad+\quad
\texttt{KKL\_STATIONARY\_FINITE\_EMBEDDED\_COLLAR\_NATURALITY}
\quad(\text{proved})
\\
\Downarrow\\
\texttt{KKL\_STATIONARY\_TWO\_OCCURRENCE\_BINDER}
\quad(\text{open})
\\
\Downarrow\\
\left.
\begin{array}{c}
\texttt{KKL\_STATIONARY\_RETAINED\_PORTION\_REALIZATION}\\
\texttt{KKL\_STATIONARY\_MARKED\_ACCESS\_ITINERARY}\\
\texttt{KKL\_STATIONARY\_SELECTED\_CORRIDOR\_CONFINEMENT}\\
\texttt{KKL\_STATIONARY\_SELECTED\_COLLAR\_DECK\_NONCOLLISION}
\end{array}
\right\}
\quad(\text{all open})
\\
\Downarrow\\
\texttt{KKL\_STATIONARY\_TWO\_SIDED\_WAVE\_NONCOLLISION}
\quad(\text{open})
\\
\Downarrow\\
\texttt{KKL\_STATIONARY\_TWO\_PULLBACK\_PASS\_THROUGH}
\quad(\text{open})
\\
\Downarrow\\
\texttt{KKL\_STATIONARY\_FINAL\_PASS\_THROUGH\_PATH\_EXTRACTION}
\quad(\text{open})
\\
\Downarrow\\
\texttt{KKL\_PARABOLIC\_WAVE\_STATIONARY\_PROOF\_REPAIR}
\quad(\text{open}).
\end{gathered}
\]
Only the indexing implication is proved conditionally:
`KKL_STATIONARY_OFF_BY_ONE_PASS_THROUGH_REDUCTION` says that, once the
two-sided noncollision theorem validates line 1603, applying it at
\(n=b\) and \(n=b+1\) gives both source predicates on the actually
defined \(A_{N-1}\).  The undefined \(A_N\) is never used.

The need for the deck clause is not formal bookkeeping.  The explicit
proved node `PQL_RAW_UNTAGGED_PATH_IMAGE_COLLISION` gives two distinct
proper immersion-restriction components with one identical untagged
degree-two image.  Its common image joins different ideal-boundary
components and is therefore not a KKL Wave; it is a no-go for inferring
occurrence multiplicity from an untagged image, not a counterexample to
the exact KKL antecedent.  In the actual selected KKL collar, every
possible collision is reduced to the nontrivial deck involution of the
single quadratic stage, but retained realization, whole-corridor
confinement, and deck-path separation remain open.

There is one positive source-level retention result:
`KKL_STATIONARY_ONE_RETAINED_CHAIN` proves that \(N\)-unbreakability
forces a nonempty retained component at every stage and that all retained
components at one stage have the same singleton untagged image.  It
cannot identify the two full segmented extension towers, their nested
occurrence windows, or their complete prefix flags.  Exact
common-parameter equality of all full stage paths gives one complete
fiber-product path only in the strict special case
`PQL_STRICT_SYNCHRONIZED_CHAIN_RECONSTRUCTION`.  General KKL containment
is instead encoded by the proved
`PQL_SEGMENTED_OCCURRENCE_RECONSTRUCTION`: every full stage path is kept,
and each finite tower prefix records the cumulative truncations produced
by its occurrence windows.  One deepest path is not the actual general
invariant because it forgets the discarded proper-path shoulders.
KKL's itinerary
proposition permits adjacency and same-pulled-interval transitions, and
its pullback formula can absorb a new tree attachment into one coarse
\(\iota^*\mathcal I\)-interval, where a subordinate path is filtered.
The source does not provide the attachment itinerary needed to turn that
hazard into a counterexample.  The exact next gate is therefore
`KKL_STATIONARY_TWO_OCCURRENCE_BINDER`.

There is also a proved but nonuniform collar branch:
\[
\begin{gathered}
\texttt{KKL\_STATIONARY\_FINITE\_EMBEDDED\_COLLAR\_NATURALITY}
\quad(\text{proved})
\\
\Downarrow\\
\texttt{KKL\_STATIONARY\_COLLAR\_EXIT\_OVERFLOW}
\quad(\text{proved for a selected source-crossing class})
\\
{}\quad+\quad
\texttt{KAHN\_QUALITATIVE\_COLLAR\_VERTICAL\_CHARGE\_NO\_GO}
\quad(\text{proved})
\\
\Downarrow\\
\texttt{KKL\_STATIONARY\_UNIFORM\_COLLAR\_EXIT\_CHARGE}
\quad(\text{open}).
\end{gathered}
\]
For a fixed collar of modulus \(\mu_h>0\), a measurably selected family
whose actual source-lift segment crosses from the inner to the outer
collar has width at most \(1/\mu_h\).  This does not cover every `D1`
label: a target trace may only touch and reenter the collar or continue on
another global immersion sheet.  Complete `D1` coverage requires a
measurable source-crossing realization in addition to the uniform
calibration
\[
 \mu_h^{-1}\le C_b\bigl(\mathcal W(U\setminus T)+1\bigr)
\]
together with measurable selection.

The failure of derivation from Kahn's qualitative hypotheses is exact.
For \(1<R<2\), \(0<a<1\), take
\[
 U_R=\mathbb D_R,\quad U'_R=\mathbb D_{\sqrt R},\quad
 K=\overline{\mathbb D},\quad T=[-a,a],\quad
 f(z)=z^2,\quad\iota(z)=z.
\]
Then \(\mathcal W(U_R\setminus T)\) is uniformly bounded as
\(R\downarrow1\), whereas every horizon-\(h\) filled-set collar satisfies
\[
 \mu_h^{-1}\ge\frac{2\pi\,2^h}{\log R}\longrightarrow\infty.
\]
This proves `KAHN_QUALITATIVE_COLLAR_VERTICAL_CHARGE_NO_GO`.  The model
is not a native periodically repelling primitive KKL block, so it refutes
source derivability from the qualitative pseudo-polynomial-like data, not
the intended native uniform theorem.

The weaker quantitative repair route is
\[
\begin{gathered}
\texttt{KKL\_STATIONARY\_QUANTITATIVE\_DEFECT\_BOUND}
\quad(\text{QSDB; open})
\\
\Downarrow\\
\texttt{KKL\_STATIONARY\_QSDB\_SUFFICIENCY}
\quad(\text{proved conditional implication})
\\
\Downarrow\\
\texttt{KKL\_PARABOLIC\_WAVE\_STATIONARY\_PROOF\_REPAIR}
\quad(\text{still open}).
\end{gathered}
\]
QSDB asks for a good/defect partition in KKL's native transverse width
measure, with the restricted measures equal to the proof-used lamination
widths and with a uniform defect charge.  Its proved sufficiency theorem
also assumes an HTND or explicit \(R(F)+1\) absolute scale, the disjoint
estimate for
\[
 B=A^{N\text{-br}}\cup A^{\rm sh},
\]
and KKL's small-breaking theorem.  One chooses
\(\theta>\max\{\lambda/\lambda_3,1/(1+\delta_3)\}\); terminality of \(B\)
then transfers quantitatively to \(A\), while the unbreakable branch lies
in \(A^{\rm sh}\) and is strictly \(\lambda\)-short.  This conditional
implication proves neither QSDB nor the stationary repair.

Conditional on the noncollision and final path-extraction gates, the
corrected estimate is
\[
 \mathcal W(B)\le 2\mathcal W(C)+4,
 \qquad
 \mathcal W(A_{N-1})\le4\mathcal W(\mathcal RF)+4.
\]
The extraction must additionally land at the correct prime ends, assemble
as a Borel lamination, and dominate \(\mathcal W(A_{N-1})\).

The stronger fixed-pair/order/KL branch is separate:
\[
\begin{gathered}
\texttt{KKL\_STATIONARY\_FINAL\_COMPONENT\_REALIZATION}
\quad(\text{proved})
\\
{}\quad+\quad
\texttt{KKL\_STATIONARY\_FINAL\_PASS\_THROUGH\_PATH\_EXTRACTION}
\quad(\text{open})
\\
{}\quad+\quad
\texttt{DIRECT\_DECORATION\_WAVE\_PROOF\_USE\_LEDGER}
\quad(\text{open})
\\
\Downarrow\\
\texttt{KKL\_STATIONARY\_FINAL\_INCIDENCE\_REFINEMENT}
\quad(\text{open})
\\
\Downarrow\\
\texttt{KKL\_STATIONARY\_NESTED\_INCIDENCE\_ORDER}
\quad(\text{open})
\\
\Downarrow\\
\texttt{KKL\_STATIONARY\_FIXED\_PAIR\_PROPER\_RESTRICTION}
\quad(\text{open})
\\
\Downarrow\\
\texttt{TERMINAL\_STATIONARY\_RESTRICTION\_KL\_PUZZLE\_SELECTOR}
\quad(\text{open}).
\end{gathered}
\]
Whole distinct graph components do not prove that two shallower
pass-through predicates refine to one final restriction occurrence, do
not order repeated incidences, and do not select a common physical KL
puzzle certificate.

There is a further crest-compatible branch.  KKL's terminal side is in the
Wave crest, not automatically at an end.  To invoke KL's skipping-over
estimate one must additionally construct distinct endpoint vertices
\(v,w\), a fixed separating piece \(Z\), and a componentwise skip witness.
The two tagged half-accesses at \(v_*\) lie in adjacent tiles, while KL's
one-tile family joins the two \(J\)-sides of a single tile.  Those objects
cannot be identified.

Under a supplied literal restriction, fixed separating piece, and
componentwise skip witness,
`TERMINAL_WAVE_CREST_TO_KL_WIDTH_CONDITIONAL` is proved.  Its application
gate is
`TERMINAL_WAVE_CREST_TO_KL_SKIPPING_BINDER`, which remains open and feeds
the full binder selector.  The published depth charge
\(2^{2m+q+2}/\mu\) is not universal when \(m\) or \(q\) grows.

The exact carrier-pair branch remains separate:
\[
\texttt{TERMINAL\_TAGGED\_ENDPOINT\_ACCESS\_MATCH}
\longrightarrow
\text{prime-end/corridor naturality}.
\]
The width-only relation does not prove equality of the original KKL and KL
prime ends; conversely, an endpoint label without a literal restriction
subcurve does not prove the width inequality.

The non-locally-connected physical properness of KKL's lifted carrier is a
separate open node and is not needed for the universal-collar no-go,
because the locally connected native subcategory already refutes that
universal claim.

## Stationary survivor dependency cut (2026-07-26)

This dependency cut is source-locked to:

```text
.tmp_wave_audit/waves-with-Misha.tex
AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
.tmp_wave_audit/not-all-good2.tex
B5D40812E40D2E44037A8FC249DB687211CD67275E66EFFF8E7F29BC7CEDFB01
.tmp_kl06_source/wad.tex
B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580
.tmp_kl06_source/psiql2.tex
E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228
.tmp_kl06_source/appendix.tex
EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3
```

The backward dependency chain is now:

\[
\begin{array}{c}
\text{native single-valued marked occurrence selector}\\
\Downarrow\\
E_A^{\rm br}\sqcup E_A^{\rm sh}\sqcup E_A^{\rm surv}\\
\Downarrow\\
\text{fixed-end full/exit WAD split}
\;+\;
\text{pointwise retained-predecessor switch}\\
\Downarrow\\
\text{Borel replacement packets with uniform/summable multiplicity}\\
\Downarrow\\
\text{vertical/incidence/bounded/response/critical residual partition}\\
\Downarrow\\
\text{QSDRA or a numerical survivor charge}\\
\Downarrow\\
\text{stationary Wave repair}.
\end{array}
\]

The first arrow is not supplied merely by a finite record.  It requires
a standard Borel occurrence presentation, one priority record per
physical target leaf, native transverse-width typing, and survival of
all KKL filters.  A finite route horizon does not make the raw
occurrence or access alphabet uniformly finite.  Finite response
extraction is valid only after a separate quotient
\(q_A\to\mathcal L_b\) with \(|\mathcal L_b|\le L(b)\) is proved.
Without it, the raw label family remains an uncontrolled discrete
factor.

The ambient horizon and the route horizon have distinct jobs:

\[
N=H=b+3,\qquad m=N-1=b+2.
\]

Ambient breaking and membership in
\(B_A=A^{N\text{-br}}\cup A^{\rm sh}\) use \(N\).  The route packets and
the degree sum use only \(1\le h\le m\).  Replacing either by the other
is an off-by-one error that changes the absorbed/residual partition.

The exact set-theoretic reduction is

\[
\begin{aligned}
E_A^{\rm br}&=E_A\cap A^{N\text{-br}},\\
E_A^{\rm sh}&=E_A\cap A^{N\text{-nbr}}\cap A^{\rm sh},\\
E_A^{\rm surv}&=E_A\cap A^{N\text{-nbr}}\setminus A^{\rm sh}.
\end{aligned}
\]

Only \(E_A^{\rm surv}\) is new.  Its ambient \(F_*\)-image remains a
nonempty singleton, so every stage has at least one retained
predecessor.  A first named-route failure is consequently either a
strict-path replacement or a marked-state mismatch, and pointwise
choices give a segmented alternative through the finite horizon.  The
logical output is relation-valued; it supplies no Borel replacement WAD
or uniform multiplicity bound.

KKL's fixed-end theorem closes only the following local dependency:

\[
\begin{array}{c}
\text{valid target WAD + supplied proper degree-one starting end}\\
\Downarrow\\
\text{paired valid full/other-end WAD split with equal coefficient
norms}.
\end{array}
\]

It does not construct the starting end.  Even after a finite eligible
end set is supplied, the least-end Borel selector requires a previously
proved Borel nonempty candidate relation and a saturation theorem for
the target transversal.  Finiteness of each surface does not bound the
marked-end, access, sheet, window, or retained-fiber multiplicity
uniformly in the primitive period.

The two desired line-1603 portions have the exact remaining dependency

\[
C_h^-\wedge X_h^-\wedge C_h^+\wedge X_h^+
\wedge P_h\wedge M_h.
\]

Here \(C_h^\pm\) are the incoming/remote eligible-end certificates,
\(X_h^\pm\) force both maximal lifts to exit at the same deep
\(L_0^h\) occurrence, \(P_h\) couples the leaf, transverse parameter,
window, sheet, and access, and \(M_h\) proves filter survival and the
asserted covering outputs.  Unconditionally, the marked
\(L_0^h\)-access is not a Freudenthal end eligible for the imported
theorem.  Under \(\mathrm{TWO}_h\wedge\mathrm{INC}_h\), the unsplit
physical inner Freudenthal end is additionally nonproper.

Once a proper measurable vertical packet exists, source domination and
pushforward give

\[
\mathcal W(\mathscr S_h^{\rm ver})
\le2^h(V(F)+2),\qquad
\sum_{h=1}^{b+2}\mathcal W(\mathscr S_h^{\rm ver})
\le(2^{b+4}-4)(V(F)+1).
\]

This closes the estimate arrow only for that certified packet.  It
does not construct the packet.  The first output left outside the
independent source estimates is a retained survivor Wave ending at
\(BL_0\).  Charging it by the critical-limb proposition is circular,
because that proposition uses the disputed stationary alignment.

Thus the immediate dependency is a marked fixed-end survivor
partition and response theorem.  Until it constructs the packets,
controls their multiplicity, and resolves the \(BL_0\) residual,
`KKL_PARABOLIC_WAVE_STATIONARY_PROOF_REPAIR` remains open.  No
downstream status changes follow: VAAPC-I, UPTCR, MBTT, coercive
compactness, rigidity, and MLC remain open.  The independently
completed machine-ledger integration at that checkpoint recorded
414 obligations: 26 imported, 287 proved, and 101 open.

## Access-local and paired-response dependency cut (2026-07-26)

The stationary residual now has two independently verified positive
arrows:

\[
\begin{array}{c}
\text{Borel-compatible continuous product family}\\
+\text{ continuous lifted access seed}\\
\Downarrow\\
\text{open maximal-lift domain, continuous lift, l.s.c. exit time,}\\
\text{Borel landing and finite-horizon first-failure code},
\end{array}
\]

and

\[
\begin{array}{c}
\text{exact full-width disjoint untrimmed occurrence realization}\\
\Downarrow\\
\mathcal W(S)\le\bigoplus_i\mathcal W(B^i)\\
\Downarrow\quad
\text{actual source Waves + whole-ending degrees + uniform }c_{\rm W}\\
\max_i\mathcal W(C^i)\ge r\mathcal W(S)-C_b.
\end{array}
\]

Neither arrow constructs its left-hand analytic data.  The complete
backward chain is now

\[
\begin{gathered}
\texttt{KKL\_WAVE\_PUSHFORWARD\_UNIFORM\_PACKET\_CONSTANT}
\quad(\text{open}),\\
\texttt{KKL\_STATIONARY\_TYPED\_PAIRED\_WAVE\_REALIZATION}
\quad(\text{open})\\
\Downarrow\\
\texttt{KKL\_STATIONARY\_BL0\_UNIFORM\_SURVIVOR\_RESPONSE}
\quad(\text{open})\\
\Downarrow\\
\texttt{KKL\_STATIONARY\_SURVIVOR\_EXCLUSION\_OR\_CHARGE}
\quad(\text{open})\\
\Downarrow\\
\texttt{KKL\_PARABOLIC\_WAVE\_STATIONARY\_PROOF\_REPAIR}
\quad(\text{open}).
\end{gathered}
\]

`KKL_STATIONARY_MARKED_FIXED_END_PAIR_CERTIFICATE` remains open only as
the optional `FREUDENTHAL` route.  It is no longer treated as a
necessary predecessor: `DIRECT_WAVE` and `ACCESS_LOCAL` are separately
typed alternatives.  The access-local route still needs `RLS-A+`,
seed-side properness, product exhaustion, marking survival, and
transverse accounting.

The packet-local factor \(r\) is not yet a global response.  To obtain
KKL terminality one must also prove a no-duplication partition of the
entire residual, a sufficiently large ambient-width fraction, an
absolute threshold absorbing \(C_b\), and output controllability
depending only on \(b\).

At the pre-QA freeze the ledger contained 423 obligations: 28 imported, 291 proved,
and 104 open.  Every global closure node remains open.

## Post-freeze QA correction: native stationary frontier (2026-07-26)

The preceding “complete backward chain” is superseded as a description
of the **native** KKL repair.  It remains an optional, stronger
paired-response research route.  The line-by-line reconstruction in
`qa_native_kkl_stationary_2026-07-26.md` proves that the printed native
argument consumes four different gates:

\[
\begin{gathered}
\texttt{KKL\_STATIONARY\_RELATIVE\_WAVE\_CONTINUATION}
\quad\text{(N1: preliminary relative telescope)},\\
\texttt{KKL\_STATIONARY\_POINTWISE\_TWO\_PATH\_BREAK}
\quad\text{(N2: line-1603 contradiction)},\\
\texttt{KKL\_STATIONARY\_FINAL\_FIXED\_COMPONENT\_EXIT}
\quad\text{(N3: measurable final lamination)},\\
\texttt{KKL\_STATIONARY\_TYPED\_BOUNDED\_DEGREE\_PUSHFORWARD}
\quad\text{(N4: final width estimate)}\\
\Downarrow\\
\texttt{KKL\_PARABOLIC\_WAVE\_STATIONARY\_PROOF\_REPAIR}.
\end{gathered}
\]

The corrections are substantive:

1. line 1576 does not prove the relative telescope and is false as
   written;
2. a pointwise two-distinct-output certificate is sufficient for
   line 1603, so doubled-width paired-Wave response is not a native
   dependency;
3. \(A_N\) is undefined and must be replaced by
   \(A_{N-1}=A_{b+2}\);
4. the final component degree is \(2\), not \(1\), but continuum degree
   alone does not certify degree on the whole marked ending
   multi-interval;
5. the correctly quantified conclusion is
   \(O_b(1+\mathcal W(\mathcal RF))\), becoming
   \(O_b(\mathcal W(\mathcal RF))\) only in an explicit large-width
   regime.

The independent extremal-width audit
`qa_extremal_wave_2026-07-26.md` also refutes the candidate
full-base collision theorem and the literal broad KKL coefficient-one
Wave statement under its printed definitions.  The source statement is
now documentary only.  The narrower Dudko--Lyubich theorem for one Wave
above one fixed boundary interval remains imported in that native
scope.  A usable stationary Wave theorem must either certify a coherent
single-crest/single-WAD-coordinate packet or retain and linearly charge
the multiplicity of source coordinates collapsing downstairs.

The paired-response nodes therefore remain valid only as abstract
conditional or optional-alternative nodes; they do not feed the active
native repair.  No global gate is promoted.

At this QA reconciliation the live ledger has:

```text
430 obligations
30 imported
292 proved
108 open
MLC open
UPTCR open
VAAPC-I open
native KKL stationary repair open
```

## Gate N1 dependency closure — 2026-07-26

The relative telescope has now been proved, without changing any
later-gate status.  The accepted acyclic dependency graph is

\[
\begin{gathered}
\texttt{N1\_PREPRUNING\_BOREL\_WAVE\_ATLAS}
\quad(\text{proved})
\ \Longrightarrow\
\texttt{N1\_BOREL\_RECTIFIABLE\_CORE\_REDUCTION}
\quad(\text{proved}),\\
\texttt{DL\_NATIVE\_RECTIFIABLE\_RELATIVE\_DISCARD\_BOUND}
\quad(\text{imported}),\\
\texttt{N1\_BOREL\_RECTIFIABLE\_CORE\_REDUCTION}
\ +\
\texttt{DL\_NATIVE\_RECTIFIABLE\_RELATIVE\_DISCARD\_BOUND}\\
\Downarrow\\
\texttt{DL\_RELATIVE\_DISCARD\_FAMILY\_BOUND}
\quad(\text{proved}),\\
\texttt{BOREL\_WIDTH\_ENVELOPE\_PRUNING}
\quad(\text{proved}),\\
\texttt{KKL\_STATIONARY\_ONE\_RETAINED\_CHAIN}
\quad(\text{proved})\\
\Downarrow\\
\texttt{STANDARD\_BOREL\_ORDERED\_WAVE\_REALIZATION}
\quad(\text{proved})\\
\Downarrow\\
\texttt{KKL\_STATIONARY\_RELATIVE\_WAVE\_CONTINUATION\_ANALYTIC}
\quad(\text{proved})\\
\Downarrow\\
\texttt{KKL\_STATIONARY\_RELATIVE\_WAVE\_CONTINUATION}
\quad(\text{proved}).
\end{gathered}
\]

The pre-pruning atlas explicitly includes BOWR Sections 2--5 and 7.2.
It does not depend on the later pruning construction.  It supplies the
Borel total-variation predicate used to split a KKL packet into its
rectifiable core and zero-width nonrectifiable complement.  The native
DL import is applied only to that core.  Their combination proves the
complete KKL relative-discard bound; the Borel envelope then
regularizes the complete discard, and the full BOWR theorem performs
the pruning and source saturation.  Thus the apparent atlas/pruning
cycle is absent.

The optional implication

```text
genuine subwave
  -> measurable retained support
  -> measurable-support width additivity
  -> relative discard
```

is not in the accepted graph.  Its first arrow is not explicitly
source-locked.  The accepted native rectifiable DL import instead
obtains the discarded width directly from the \(O(\log m)\) deleted
packet inventory in Feigen 2830--2841, after the independent
rectifiable-core reduction.

The downstream graph is now

\[
\begin{gathered}
\texttt{KKL\_STATIONARY\_RELATIVE\_WAVE\_CONTINUATION}
\quad(\text{proved}),\\
\texttt{KKL\_STATIONARY\_POINTWISE\_TWO\_PATH\_BREAK}
\quad(\text{open}),\\
\texttt{KKL\_STATIONARY\_FINAL\_FIXED\_COMPONENT\_EXIT}
\quad(\text{open}),\\
\texttt{KKL\_STATIONARY\_TYPED\_BOUNDED\_DEGREE\_PUSHFORWARD}
\quad(\text{open})\\
\Downarrow\\
\texttt{KKL\_PARABOLIC\_WAVE\_STATIONARY\_PROOF\_REPAIR}
\quad(\text{open}).
\end{gathered}
\]

The proof-ledger audit reports 437 obligations: 31 imported, 299
proved, and 107 open.  MLC, UPTCR, VAAPC-I, MBTT, coercivity, and
rigidity remain open.

## 2026-07-27 — Gate N2 selected-predecessor dependency refinement

The accepted set-theoretic chain is now

\[
\begin{gathered}
\texttt{KKL\_STATIONARY\_CRITICAL\_LIMB\_INVERSE\_BRANCH}
\Longrightarrow
\texttt{KKL\_STATIONARY\_SELECTED\_SMALL\_JULIA\_PREDECESSOR\_CHAIN}
\Longrightarrow
\texttt{KKL\_STATIONARY\_SELECTED\_PREDECESSOR\_CHAIN},\\
\texttt{KKL\_STATIONARY\_SELECTED\_ALPHA\_PREDECESSOR\_CHAIN}
\ +\
\texttt{KKL\_STATIONARY\_CRITICAL\_LIMB\_INVERSE\_BRANCH}
\Longrightarrow
\texttt{KKL\_STATIONARY\_TERMINAL\_CRITICAL\_LIMB\_INVERSE\_SHEETS},\\
\texttt{KKL\_STATIONARY\_TERMINAL\_CRITICAL\_LIMB\_INVERSE\_SHEETS}
\ +\
\texttt{FINITE\_MARKED\_TREE\_TERMINAL\_PRUNING}
\ +\
\texttt{LC/DENDRITE\ INPUT}
\Longrightarrow
\texttt{KKL\_STATIONARY\_LC\_TERMINAL\_SHEET\_MCI}.
\end{gathered}
\]

The terminal inverse-sheet node is proved without local connectivity.
Local connectivity enters only to make the physical carrier a
dendritic minimal tree with literal marked-continuum fibers.

The exact non-LC branch is:

\[
\begin{gathered}
\texttt{KKL\_STATIONARY\_MODEL\_TERMINAL\_SHEET\_INCIDENCE}
\quad(\text{proved}),\\
\texttt{KKL\_STATIONARY\_NONLC\_SELECTED\_GEOMETRIC\_CONTINUUM\_LIFT}
\quad(\text{open})\\
\Downarrow\\
\texttt{KKL\_STATIONARY\_SELECTED\_PREDECESSOR\_MARKED\_COMPONENT\_INCIDENCE}
\quad(\text{open globally}).
\end{gathered}
\]

There is also a proved sufficient implication

```text
KKL_STATIONARY_MONOTONE_FULL_LIFT_IDENTIFICATION  [open hypothesis]
    -> KKL_STATIONARY_MONOTONE_FULL_LIFT_IMPLIES_MCI [proved conditional]
    -> physical non-LC MCI
```

The open identification package requires a monotone semiconjugacy,
correct predecessor labels and a singleton fixed fiber, the full lift
\(T=\pi^{-1}(T_{\rm com})\), selected-sheet correspondence, and
\(\pi(K_i)\subset\bar K_i\) for the geometric model small-Julia
continua.  The later quotient that collapses \(\bar K_i\) to an
abstract tree vertex is a different map.  The package is not imported
from KKL's phrase
“lift by \(\pi\).”

The independent separator branch remains

```text
KKL_STATIONARY_SELECTED_SMALL_JULIA_PREDECESSOR_CHAIN [proved]
    -> KKL_STATIONARY_SELECTED_SEPARATOR_REALIZATION [open]
    -> KKL_STATIONARY_MARKED_ACCESS_ITINERARY [open]
```

Thus a \(Q_n\) pullback continuum is not used as a full-carrier
separator before `KKL_STATIONARY_SELECTED_SEPARATOR_REALIZATION`.
The conditional line-1598 counting theorem remains separate from the
incoming proper-occurrence anchor.  The ledger contains 465
obligations: 34 imported, 316 proved, and 115 open.  MLC remains open.
