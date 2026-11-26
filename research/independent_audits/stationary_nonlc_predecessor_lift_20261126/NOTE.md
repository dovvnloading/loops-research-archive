# Stationary predecessor incidence and separation without local connectivity

Date: 2026-11-26. Base: 6ba50a4b452f7703c17200dd3b3bab4b117ee413.

## Target, status, claim

- Primary: **KKL_STATIONARY_NONLC_SELECTED_GEOMETRIC_CONTINUUM_LIFT** (open).
- Direct downstream: **KKL_STATIONARY_SELECTED_PREDECESSOR_MARKED_COMPONENT_INCIDENCE** (open).
- Additional subclauses: **KKL_STATIONARY_MONOTONE_FULL_LIFT_IDENTIFICATION** and **KKL_STATIONARY_SELECTED_SEPARATOR_REALIZATION** (both open).

**Result (b), actual quadratic class, with an exact boundary.** For every connected periodically repelling quadratic polynomial with a primitive quadratic-like renormalization and the rotation-\(1/q\) limb data of KKL §2.4, the canonical rational-cut monotone quotient has disjoint nondegenerate geometric small-Julia continua, with their original period labels. The full inverse lift of their model hull has the exact selected-predecessor identities at every finite depth. More importantly, marked-core incidence holds on the *actual* filled Julia set, for both the least physical compact carrier and the full lift, and every invariant subcontinuum between them. This gives the line-1598 counting conclusion in the range \(q>b\). A separate actual polynomial argument proves the global continuum separator clause, not merely separation inside an inverse sheet.

This is a proof about actual maps, not a finite tree model. No a priori modulus bound, beau bound, local connectivity of the physical Julia set, or uniform lower bound on an annulus is imported. The scope excludes touching/satellite little Julia sets, disconnected Julia sets, neutral or attracting periodic orbits, virtual molecule scales, and arbitrary unrelated models. The finite-width native same-filled restriction and straightening transport the set-level claims as explained below. We do not identify an independently preassigned, unspecified KKL lift and all its marked accesses by notation alone.

## 1. Inputs and notation

Write \(f(z)=z^2+c\), \(X=K(f)\), with \(X\) connected and all finite periodic orbits repelling. Let \(K_0\) be the actual connected filled set of a degree-two polynomial-like restriction of \(f^P\), \(P>1\), containing 0, and \(K_i=f^i(K_0)\) for \(0\le i<P\). Require the primitive hypothesis: these compact connected sets are pairwise disjoint and \(f(K_i)=K_{i+1\bmod P}\).

As in KKL §2.4, assume the dividing fixed point \(\alpha=\alpha_F\) has the finitely many open limbs \(D_j\) of \(X\setminus\{\alpha\}\), cyclically numbered so \(0\in D_0,\ c\in D_1\). Their closures are \(D_j\cup\{\alpha\}\); \(f:D_j\to D_{j+1\bmod q}\) is a homeomorphism for \(j\ne0\), and \(f(D_0)=X\). Here \(q\ge2\). The high-type count will assume \(q>b\) and at most \(b\) cycle members in \(D_0\); no high-type assumption is needed for the other claims.

By the same-filled empty-interior theorem (dependencies in §9), \(X=J(f)\), full and with empty interior. The critical point is not periodic. Define \(\phi:D_0\to D_0\) to be the unique inverse with image in \(D_0\), \(\Omega_n=\phi^n(D_0)\), \(\Omega_0=D_0\), and \(Q_n=\phi^n(K_0)\). Use the actual point chain \(\alpha^0=\alpha,\ \alpha^1=-\alpha,\ \alpha^{n+1}=\phi(\alpha^n)\) for \(n\ge1\).

For clarity the terminal-sheet theorem already proved in the archive gives
\[
 \Omega_n\in\pi_0(X\setminus\{\alpha^n\}),\qquad
 \overline{\Omega_n}=\Omega_n\cup\{\alpha^n\}.
\tag{1}
\]
Each sheet is open in \(X\). Its proof uses the two distinct noncritical preimages of \(D_0\), one in \(D_{q-1}\) and one in \(D_0\), and the limb closure formula. If the latter inverse sheet accumulated at \(\alpha\), both inverse points would accumulate at \(\alpha\), contradicting local injectivity there. Thus its only boundary is \(-\alpha\); induction with the homeomorphism \(\phi\) on \(D_0\) gives (1). In particular \(\phi\) extends to a homeomorphism \(\overline{D_0}\to\overline{\Omega_1}\) taking \(\alpha\) to \(\alpha^1\) (compactness and the unique boundary point). Compositions give homeomorphisms \(\overline{D_0}\to\overline{\Omega_n}\).

No \(\alpha^n\) is in any \(K_i\): applying \(f^n\) would put the fixed point \(\alpha\) in a cycle member, hence in every cycle member, contradicting disjointness. In particular \(K_0\subset D_0\), \(K_1\subset D_1\). The noncritical limb dynamics put \(K_j\) in \(D_j\) for \(0\le j<q\); hence \(P\ge q\).

## 2. Two elementary physical continuum facts

**Lemma 2.1 (hereditary unicoherence).** Every nonempty intersection of two subcontinua of \(X\) is connected.

Every compact subset \(E\subset X\) has connected complement: the unbounded complementary component of \(E\) contains the connected complement of \(X\), and any other component would be a nonempty plane open subset of \(X\). This contradicts empty interior. If subcontinua \(A,B\subset X\) have disconnected nonempty intersection, Janiszewski's separation theorem on the sphere gives a disconnected complement of \(A\cup B\), a contradiction. This proves the lemma. It uses actual fullness and empty interior, not a picture of a tree.

**Lemma 2.2 (least compact carrier).** There is a least subcontinuum \(S\subset X\) containing \(\bigcup_iK_i\), and \(f(S)\subset S\).

Take the intersection of all subcontinua containing the marked union. Finite intersections are nonempty subcontinua by Lemma 2.1. Their total intersection is a subcontinuum: a separation of that intersection into two compact parts has disjoint open neighborhoods; compactness would put some finite intersection inside their union while meeting both, impossible. The intersection is thus the least such continuum.

For forward invariance, \(f^{-1}(S)\) is compact, in \(X\), and connected. Here is the connectedness argument, also useful below. For any full subcontinuum \(E\subset X\) containing the critical value \(c\), take decreasing closed Jordan neighborhoods of \(E\) obtained by equipotentials of the conformal map of its exterior, with intersection \(E\). Their open interiors contain \(c\). The inverse of each interior under \(z^2+c\) is path connected: for any inverse point, a path in the interior to \(c\) avoiding \(c\) until its endpoint lifts by the ordinary double covering away from \(c\), and ends at 0. The preimage of the closed Jordan neighborhood is the closure of this connected open inverse, since the polynomial is open. Compact nested intersection gives connectedness of \(f^{-1}(E)\). Apply this to \(S\), which contains \(c\in K_1\). Its inverse contains every \(K_i\) because the cycle permutes onto itself. Minimality gives \(S\subset f^{-1}(S)\), as required.

## 3. Construct the canonical geometric quotient and its marks

Use Kiwi's actual fiber quotient \(p:X\to Y\), not the later vertex collapse. By Kiwi (2004), Theorem 2, Corollary 2.15, Proposition 4.2, Corollary 4.5 and Theorem 5.12, the fibers are compact connected, those containing finite-orbit points are singletons, the plane quotient is a plane, and \(p f=g p\) where \(g\) is the degree-two branched covering induced on that plane. A nonsingleton fiber \(C\) has mutually disjoint positive forward images, and \(f^n(C)\) is a complete fiber. These theorems apply because \(J(f)\) is connected and there are no irrationally neutral cycles.

**Dendrite, not just a locally connected model.** The plane quotient collapses only subsets of \(X\), with singleton classes outside \(X\). Thus the complement of \(Y=p(X)\) is the continuous image of \(\mathbb C\setminus X\) and is connected. If \(Y\) had interior, the inverse image of a nonempty open subset of \(Y\) under the plane quotient would be a nonempty open subset of \(X\), impossible. By Kiwi Proposition 4.7 and Corollary 4.8 the angle-circle landing map \(w:\mathbb R/\mathbb Z\to Y\) is continuous and onto. The Hahn–Mazurkiewicz theorem gives local connectivity. Fullness plus empty interior exclude a simple closed curve (its bounded Jordan domain would lie in \(Y\)). Hence \(Y\) is a dendrite.

**Rational-cut description.** The circle quotient here is not just an unspecified existential monotone model. Let \(R\) be the rational external-ray landing equivalence of \(f\). For any full \(R\)-class \(E\), and any distinct \(a,b\in E\), say that the pair \((a,b)\) separates angles \(t,s\) when both are outside the whole class \(E\) and lie in the two different open circular intervals bounded by \(a,b\). Then
\[
 w(t)=w(s)\quad\Longleftrightarrow\quad
 \text{no such rational pair separates }t,s.
\tag{2}
\]
Indeed rational landing points are finite-orbit points and have singleton complete fibers. Conversely an angle whose impression projects to such a point lands there, by Kiwi Corollary 3.14 and Theorem 2. All angles landing at a finite-orbit point are rational: the set of such rays at a periodic point is finite and permuted by the return angle map (Kiwi Proposition 2.13 uses precisely this finiteness); taking preimages gives rational angles also at preperiodic points. Thus exclusion of the whole \(R\)-class in the test is exactly exclusion of the landing-point fiber. The two rational rays and their common landing point form a Jordan separation on the sphere, and a connected fiber other than the landing-point fiber is confined to one side. Each angle's ray is on its corresponding side and its impression lies in the closure of that side. This proves one implication. For the converse use Kiwi Corollary 2.18: distinct fibers are separated by rational rays with common landing point or by a pair through a bounded Fatou component. The second possibility is absent here. The separating pair avoids the two chosen points and their whole fibers (singleton landing-point fiber), so their impressions and the rays at \(t,s\) are on opposite sides. This proves (2), including angles in rational classes. In particular the geometric circle quotient, with its landing marking and doubling map, is determined by the rational lamination with this explicit completion rule. We do not infer a conformal-width identity from it.

**Disjoint geometric marks.** Put \(A_i=p(K_i)\). These are compact connected, \(g(A_i)=A_{i+1\bmod P}\), and nondegenerate: straighten the little return \(f^P\) on \(K_0\); its two fixed points are distinct, since the repeated-root case is the polynomial with parameter \(1/4\), whose filled set has interior. Their images under \(f^i\) remain distinct by application of \(f^{P-i}\) and are periodic for \(f\), so their \(p\)-fibers are singletons. This recovers the archive's no-point-collapse clause.

We additionally prove pairwise disjointness, not supplied by no-point-collapse. Suppose \(p(K_i)\cap p(K_j)\ne\varnothing\) with \(i\ne j\). The complete fiber \(C\) over an intersection point meets both disjoint continua, so is nonsingleton. By Kiwi's wandering-fiber theorem \(C\cap f^P(C)=\varnothing\); the image fiber still meets both \(K_i,K_j\), since \(f^P(K_i)=K_i,\ f^P(K_j)=K_j\). The two subcontinua
\[
 K_i\cup C\cup K_j,\qquad K_i\cup f^P(C)\cup K_j
\]
have intersection exactly \(K_i\cup K_j\), disconnected. This contradicts Lemma 2.1. The geometric marks are therefore pairwise disjoint.

They also have a rational marking characterization independent of declaring an entire unknown fiber to be a little Julia set. Let \(\Theta_i\) consist of the rational angles landing at the periodic points of the actual \(K_i\). Then
\[
 A_i=\overline{w(\Theta_i)}.
\tag{3}
\]
Periodic points are dense in \(K_0\) by straightening, empty interior, and density of repelling cycles in the Julia set; their images are dense in \(K_i\). Each of these points has a rational landing ray. Continuity of \(p\) gives (3). This describes the marks as the closures of the corresponding period-labelled rational portraits in the geometric model. It is not a collapse of \(K_i\) to a finite graph vertex. We have not proved that a fiber meeting \(K_i\) must be contained in \(K_i\), nor is that needed.

## 4. Component transport at actual roots

For a continuous monotone surjection of compact continua the inverse of any compact connected set is connected: otherwise compact separated pieces of the inverse have disjoint images, since fibers are connected, contradicting connectedness of the set. In a dendrite every connected subset is arc-convex (omitting an interior point of the joining arc separates its endpoints). Consequently the inverse under \(p\) of any connected subset of \(Y\), not necessarily compact, is connected: it is the union of the inverse images of arcs from one fixed model point to each point of the subset, and those inverse images are compact connected and share a fiber.

Every \(\alpha^n\) has singleton fiber by its finite forward orbit. The components of \(X\setminus\{\alpha^n\}\) are therefore in bijection with those of \(Y\setminus\{p(\alpha^n)\}\). Specifically the inverse of each model component is connected by the previous paragraph, and the image of each physical component is connected and avoids the model root; maximality gives the bijection and saturation. Write \(\bar\alpha^n=p(\alpha^n)\) and \(\bar\Omega_n=p(\Omega_n)\). Thus
\[
 p^{-1}(\bar\Omega_n)=\Omega_n.
\tag{4}
\]
In particular the critical limb labels transport as whole components; at a rational cut their angular sectors transport under (2). The noncritical limb homeomorphisms transport too: for a model fiber in the target limb, its inverse by the physical homeomorphism is connected and its image under \(p\) lies in a finite \(g\)-fiber, hence is a point. This gives a continuous descended inverse (a restriction of a closed quotient to a saturated subset is again a quotient map). The same argument for \(\phi\) on \(D_0\) gives the inverse branch \(\bar\phi:\bar\Omega_0\to\bar\Omega_1\), a homeomorphism satisfying \(p\phi=\bar\phi p\). Thus \(\bar\Omega_n=\bar\phi^n(\bar\Omega_0)\), and \(p(Q_n)=\bar\phi^n(A_0)\) with the original physical selection labels.

The model critical point is \(p(0)\), not a point chosen by a graph convention: the complete fiber over \(p(c)\) is connected and contains \(c\). Its full inverse under \(f\) is connected by the proof in Lemma 2.2. Its image under \(p\) is exactly \(g^{-1}(p(c))\), a finite set, hence a singleton. This singleton is \(p(0)\); no additional preimage outside \(Y\) is possible since \(X\) is completely invariant and outside classes are singletons. The plane branched covering has degree two, so the point has local degree two.

**Physical intersection lemma.** For every subcontinuum \(U\subset X\), \(U\cap\Omega_n\), if nonempty, is connected, indeed any two of its points lie in a compact connected subset of that intersection. For \(x,y\in U\cap\Omega_n\), take the model arc \([p(x),p(y)]\subset\bar\Omega_n\), with a singleton allowed. Its full inverse is a subcontinuum of \(\Omega_n\) containing \(x,y\). Intersect with \(U\) and apply Lemma 2.1. Taking the union of these subcontinua from one fixed point proves the assertion. This is the key improvement over using local connectivity of \(X\).

## 5. Exact full lift and direct physical incidence

Let \(B\) be the least subcontinuum of the dendrite \(Y\) containing all \(A_i\), equivalently their arc hull, and let \(T^*=p^{-1}(B)\). This is an actual compact connected subset of \(X\) containing all \(K_i\). Since \(p(S)\) contains all the \(A_i\), \(B\subset p(S)\). Since \(S\subset T^*\) by leastness, \(p(S)\subset B\). Hence
\[
 S\subset T^*,\qquad p(S)=B,\qquad g(B)\subset B,\qquad f(T^*)\subset T^*.
\tag{5}
\]
The invariance assertions follow from Lemma 2.2 and semiconjugacy.

Take any compact connected forward invariant physical carrier \(T\) with \(S\subset T\subset T^*\). In particular \(S\) and \(T^*\) are both choices. Define \(L^0(T)=T\cap D_0\). By the physical intersection lemma this is nonempty and connected. The archive's \(Q_0\)-selected component construction therefore gives at every depth \(n\)
\[
 L^n(T)=\phi^n(L^0(T))=f^{-n}(T)\cap\Omega_n,\qquad
 Q_n\subset L^n(T).
\tag{6}
\]
For the component assertion: if a connected set in \(f^{-1}(L^{n-1})\) meets \(D_0\), it cannot leave \(D_0\) because the inverse omits \(\alpha\); the homeomorphic inverse of \(L^{n-1}\) in \(D_0\) is then the whole component. This is the actual set recursion. In the geometric model define \(\bar L^n=\bar\phi^n(B\cap\bar\Omega_0)=g^{-n}(B)\cap\bar\Omega_n\). Since \(p(T)=B\) and (4) holds, the transported selected component is exactly \(p(L^n(T))=\bar L^n\). In particular for the full carrier
\[
 \boxed{p^{-1}(\bar L^n)=L^n(T^*)},\qquad p(K_i)=A_i.
\tag{7}
\]
The first identity follows by taking the inverse in the model formula for \(\bar L^n\), using (4), (5), and semiconjugacy. Thus the full geometric two-level lift and the whole monotone-full-lift package hold for this specified rational-cut construction, for every \(n\), not only through \(b+2\). For the minimal carrier \(S\) we proved the image identity; its inverse identity would require \(L^n(S)\) itself to be saturated, which is not proved.

**Direct physical incidence, independently of full-lift equality for \(T\).** Suppose \(L^n(T)\cap T\ne\varnothing\). By (6), \(T\cap\Omega_n\ne\varnothing\). Its projection meets \(\bar\Omega_n\); by \(p(S)=p(T)=B\) and (4) we have \(S\cap\Omega_n\ne\varnothing\).

If \(\alpha^n\notin S\), connectedness and (1) force \(S\subset\Omega_n\), so every \(K_i\subset\Omega_n\). Otherwise suppose no cycle member meets \(\Omega_n\). The map \(r:X\to X\) that is the identity on \(X\setminus\Omega_n\) and sends \(\overline{\Omega_n}\) to \(\alpha^n\) is continuous by the closed-set pasting lemma and (1). Then \(r(S)=S\setminus\Omega_n\) is a proper compact connected subset of \(S\) containing all marked sets, impossible. Thus some actual \(K_i\) meets \(\Omega_n\), and because it avoids the root, connectedness forces \(K_i\subset\Omega_n\). It also lies in \(T\), and forward invariance places it in \(f^{-n}(T)\). We conclude
\[
 \boxed{L^n(T)\cap T\ne\varnothing\ \Longrightarrow\
            \exists i:\ K_i\subset L^n(T)} .
\tag{8}
\]
This proof never uses incidence of an abstract marked vertex. It also proves that every such \(T\) has exactly the same occupied terminal sheets as the least physical carrier \(S\), namely those containing some \(K_i\).

At \(n=b\), a nonempty intersection in (8) would give \(b+1\) different members \(K_i,f(K_i),\ldots,f^b(K_i)\) lying in \(D_0\) by (6). They are distinct because \(P\ge q>b\). This contradicts the occupancy hypothesis. Therefore \(T\cap L^b(T)=T\cap\Omega_b=\varnothing\) (the second equality uses forward invariance in (6)). Forward invariance and the predecessor recursion also give
\[
 T\cap L^n(T)=T\cap\Omega_n=\varnothing\quad(n\ge b).
\tag{9}
\]
This is precisely the set-level conclusion needed at line 1598, including both later depths, without an assumed local connectivity or assumed exact lift equality for \(S\).

## 6. A physical separator proof (additional subclause)

This is an independent actual-polynomial argument, so it does not rely on model fibers containing critical points being singletons.

**Symmetry.** The actual little filled set \(K_0\) is invariant under \(z\mapsto-z\). Indeed \(f^P\) is even, and the connected degree-two restriction domain containing 0 is a component of the full inverse of its target (properness makes it relatively closed there). Its reflected domain is another component containing 0, hence is equal to it. Membership in the filled set is invariant under reflection because \(f^P(-z)=f^P(z)\). Also \(X=-X\). We have \(\alpha^1=-\alpha\), \(\alpha\ne0\), and \(\alpha,\alpha^1\notin K_0\).

Choose a periodic point \(z\in K_0\) of the return; it is repelling for the ambient polynomial and is not 0. At least one rational external ray \(R\) of \(X\) lands at \(z\). Its reflected ray \(-R\) lands at \(-z\in K_0\). These rays are disjoint, avoid \(X\) in their interiors, and their landing points are distinct. The exterior uniformizing map of the full nondegenerate \(K_0\), normalized at infinity with positive leading coefficient, is odd by uniqueness. In its exterior disk coordinates, \(R\) and \(-R\) are disjoint opposite proper arcs from the inner boundary circle to infinity. More explicitly each has a prime-end angle at the inner boundary, since a curve landing on a full continuum determines an access (Kiwi Lemma 2.8, or Lindelöf's theorem); the angles are opposite and distinct by oddness. At infinity the angles are also opposite, by the asymptotics of the ambient Böttcher ray and the little exterior map. After radial compactification at infinity these are two disjoint spanning arcs of a closed annulus with distinct endpoints on each boundary circle. Cutting the annulus along these arcs gives two regions; reflection interchanges them since it interchanges the complementary outer boundary intervals. Thus \(\alpha,-\alpha\), which are outside \(K_0\) and the rays, are in opposite regions. Every connected subset of \(X\setminus K_0\) avoids both rays and lies in a single region. This proves separation in the *full physical set*, including potentially non-path-connected routes.

The set \(K_0\) is disjoint from \(\Omega_1\): it avoids \(\alpha^1\), so if it met \(\Omega_1\) it would lie entirely in \(\Omega_1\); then \(0\in\Omega_1\), impossible because \(f(0)=c\in D_1\). By (1), \(\overline{\Omega_1}\) is connected, lies in \(X\setminus K_0\), and contains \(\alpha^1\). Hence \(K_0\) separates \(\alpha\) from all of \(\Omega_1\) in \(X\).

Transport by the actual homeomorphism \(\overline{D_0}\to\overline{\Omega_n}\) of §1. It takes \(K_0\) to \(Q_n\), \(\alpha\) to \(\alpha^n\), and \(\Omega_1\) to \(\Omega_{n+1}\). We get separation within \(\overline{\Omega_n}\). To rule out *all* routes leaving the sheet, use the global continuous retraction \(s_n:X\to\overline{\Omega_n}\) that is the identity on \(\overline{\Omega_n}\) and sends \(X\setminus\Omega_n\) to \(\alpha^n\); this is again closed-set pasting. Since \(Q_n\subset\Omega_n\), \(s_n^{-1}(Q_n)=Q_n\). The image of any connected subset of \(X\setminus Q_n\) meeting \(\alpha^n\) and \(\Omega_{n+1}\) would contradict the separation in \(\overline{\Omega_n}\). Thus for every \(n\),
\[
 \boxed{Q_n\text{ separates }\alpha^n\text{ from }\Omega_{n+1}
           \text{ in }X,\ \text{hence from }L^{n+1}(T)}.
\tag{10}
\]
For \(n\ge b\), (9) says \(T\) is outside \(\Omega_n\); the same retraction proves \(Q_n\) separates the entire \(T\) from \(L^{n+1}(T)\). This establishes the set-level separator and no-bypass clauses of KSEP, not the specified collar, marked prime-end access, or Wave occurrence.

For an additional base-dynamical attachment check, \(T\cap D_0\) accumulates at \(\alpha\), since \(T\) is connected, meets both \(D_0\) and \(D_1\), and their closures meet the rest only at \(\alpha\). Its closure in \(T\) is \((T\cap D_0)\cup\{\alpha\}\). By (6) and the closed-sheet homeomorphisms the closure of \(L^n(T)\) in \(f^{-n}(T)\) is \(L^n(T)\cup\{\alpha^n\}\). Points of \(T\cap D_1\) likewise accumulate at \(\alpha\); their inverse by a local branch of \(f^n\) at \(\alpha^n\) accumulates there from outside \(\Omega_n\). The branch exists since each point \(\alpha^m\) for \(m\ge1\) maps to \(D_0\) or to \(\alpha\), whereas 0 maps to \(c\in D_1\); also \(\alpha\ne0\). Hence the boundary between this selected set and the rest of the base inverse is exactly \(\{\alpha^n\}\). This is not an assertion about a particular ambient fiber-product carrier \(\widehat T_n\), or its ideal boundary.

## 7. Actual example and executable diagnostic

The repository's period-27 tip parameter is the real root of \(x_{18}(c)+x_9(c)=0\), \(x_0=0,\ x_{j+1}=x_j^2+c\), in the closed interval with endpoints
\[
 \frac{-607918036626757496169199575185708826140}{2^{128}},
 \quad
 \frac{-607918036626757496169199575185708826139}{2^{128}}.
\]
Our independent standard-library checker uses outward-rounded dyadic intervals at denominator \(2^{256}\) (exact integers; no float, no random seed). It proves opposite endpoint signs and a nonzero derivative throughout, pairwise separation of \(x_0,\ldots,x_{18}\), and the repelling multiplier of the 9-cycle. The equation gives \(x_{19}=x_{10}\), so the critical preperiod and eventual period are exactly 10 and 9. Standard postcritically finite dynamics then give a connected periodically repelling filled Julia set (the only finite critical orbit is strictly preperiodic).

It also verifies independently a positive Rouché margin for \(f^3(z)-w\) on \(|z|=1/4\) uniformly for \(|w|\le1/4\): writing \(f^j(z)=x_j+A_jz^2+E_j(z)\), the exact recurrence bounds the whole remainder by \(e_{j+1}\le2|x_j|e_j+d_j^2\), where \(d_j\) bounds \(|f^j(z)-x_j|\), \(d_{j+1}\le 2|x_j|d_j+d_j^2\). The coefficient \(A_1=1,\ A_{j+1}=2x_j A_j\). Strict domination of \(|A_3|/16\) over \(|x_3|+e_3+1/4\) gives exactly two preimages of each target point in the disk, counted with multiplicity. The component of \((f^3)^{-1}(D(0,1/4))\) containing 0 is compactly contained in the target disk, proper and degree two (both preimages of \(x_3\) are already accounted for at 0), and is simply connected by the maximum modulus principle for polynomial disk-preimage components. Every critical return is in the disk by the verified orbit bounds and the exact eventual relation; every such preimage in the disk is in this one component, so the filled set is connected. The three phase images of the disk are enclosed in pairwise disjoint balls by the checked deviations. This is an actual primitive period-3 quadratic-like cycle; since 3 is prime its type is prime. It is in the real \(1/2\) wake (negative fixed-point multiplier less than \(-1\), and real \(c\) in the period-two limb); alternatively the general incidence theorem only needs the given native limb data. The checker does not certify a non-LC example, a high-type \(q>b\) example, or an analytic Wave. Its 9-real-interval check is an extra exact regression, not the proof of the complex carrier theorem. The non-LC portion of the theorem is universal within the stated class whether or not a currently known parameter in that class has non-LC Julia set.

Run from repo root:

    python -B research/independent_audits/stationary_nonlc_predecessor_lift_20261126/verify.py

Expected one JSON line, including critical_preperiod=10, critical_period=9, disjoint_real_interval_cycle=9, and positive rouche_period3_margin_lower_millionths. An assertion failure is a hard failure. Tested with the local Python runtime; CI is separately pinned to Python 3.12 and needs no installed packages. No generated files, seeds or tolerance choices. Prior exact bracket and phase definitions credited to the repository's results/period27_misiurewicz_tip.json, results/tip_complex_domains.json and results/tip_root_interval_geometry.json and their original verifiers.

## 8. Transport and precise promotion boundary

For a finite-width native periodically repelling psi-quadratic-like map, KKL Theorem 2.1 supplies a restriction on neighborhoods of the same filled continuum. Douady–Hubbard straightening conjugates it near the filled set to a quadratic polynomial, preserving physical connected sets, the critical point, little cycle, finite-orbit labels, and actual component recursion. For the little return, shrink its polynomial-like neighborhoods around the compact little filled set, and all intermediate iterates, inside the neighborhood of the ambient conjugacy; this can be done by taking smaller equipotential restrictions of the little return. Thus the transported little return is a degree-two proper restriction of the ambient polynomial iterate. The proofs of §§2–6 transport back by the conjugacy. No conformal modulus, ideal marking, or ambient immersion transport is claimed.

The exact KKL written convention (p.13, §2.5) calls for a rational-lamination model and lifting its objects, but does not define the extension of the rational relation, the geometric renormalization portrait, or whether the carrier denotes the minimal compact hull or a full preimage. Formula (2) specifies a rational-cut realization, (3) specifies geometric marks, and (5) constructs both canonical physical carriers; (7) proves the literal full-lift identities for the full lift. In particular the incidence argument (8) works for either choice without needing to decide that convention. The first unproved identification for the *exact preassigned source object*, if different from this construction, is a marked intertwiner taking its circle quotient and renormalization portraits to (2)–(3) and its physical carrier into the interval \([S,T^*]\) (equality with \(T^*\) for the full-preimage clause). We do not claim equality of full lift and minimal physical hull; no actual counterexample to it is supplied. Beyond this, the first unproved geometric step is realization of the specified proof-used collar/prime-end access and occurrence on the actual ambient iterated psi-ql carrier. A separator in \(X\) is not by itself such a collar.

Proposed integration, subject to independent review:
- Add proved scoped subclaims for hereditary unicoherence/least carrier, canonical rational-cut dendrite, marked geometric disjointness and portrait closure, critical and terminal-sheet transport, physical intersection connectedness, full-lift selected components, physical MCI and the global set separator.
- Keep the exact named-lift and optional full-identification ledger rows open unless the reviewed integration fixes their convention to the construction here. If it does, (7) proves their set-level clauses for that convention. For MCI, replace the requirement of that exact lift equality by the direct argument (8) for the stated carrier choices; this is a genuine alternative proof and does not depend on the open identification.
- Keep KSEP open at its collar/access/occurrence clauses. Do not promote EGC for an ambient pullback or the incoming Wave anchor, stationary repair, MBTT, VAAPC-I, any H1–H4 gate, UPTCR, or MLC. No ledger status is changed by this PR.

## 9. Dependencies, sources, attribution, verification

Internal source notes at the base SHA: research/mlc_unified/kkl_stationary_n2_selected_predecessor_endpoint.md, Lemmas 2.1–2.2, Theorem 4.3 (first two steps), Proposition 4.5 (prior sufficient package), Proposition 4.6, Lemmas 5.1–5.2 and Proposition 6.1; research/mlc_unified/kkl_stationary_n2_kiwi_model_identification_audit_20260727.md; research/mlc_unified/kkl_stationary_n2_frontier_audit_20260727.md; research/mlc_unified/terminal_hubbard_anchor.md §2; research/mlc_unified/terminal_relative_cover_alignment.md §§2–3. Dependencies consumed: KKL_NATIVE_TERMINAL_HUBBARD_TREE, KKL_PRIMITIVE_ROTATION_LIMB_CYCLE_DATA, KKL_STATIONARY_CRITICAL_LIMB_INVERSE_BRANCH, KKL_STATIONARY_SELECTED_ALPHA_PREDECESSOR_CHAIN, KKL_STATIONARY_SELECTED_SMALL_JULIA_PREDECESSOR_CHAIN, KKL_STATIONARY_SELECTED_PREDECESSOR_CHAIN, KKL_STATIONARY_TERMINAL_CRITICAL_LIMB_INVERSE_SHEETS, KKL_STATIONARY_SELECTED_ENDPOINT_CYCLE_AVOIDANCE, PERIODICALLY_REPELLING_PQL_FILLED_JULIA_EMPTY_INTERIOR, PQL_SAME_FILLED_CONTINUUM_QUADRATIC_LIKE_RESTRICTION. The previous model incidence theorem is not needed as a premise of (8).

Primary and standard theorem imports:
- Jeremy Kahn, Alex Kapiamba, Mikhail Lyubich, [MLC for parabolically bounded primitive renormalization](https://arxiv.org/abs/2606.27272v1), Theorem 2.1 (p.11), §§2.3–2.5 (pp.11–13), §3.1 (occupancy bound), §3.2 (p.20, high type), Lemma 6.31 (p.50). Locked archive TeX lines 451–457, 478–504, 514–543, 661–715, 1597–1605. We use the hypotheses and limb structure, not the disputed proof step, nor Theorems A–D.
- Jan Kiwi, [Real laminations and the topological dynamics of complex polynomials](https://doi.org/10.1016/S0001-8708(03)00144-0), Adv. Math. 184 (2004), 207–267: Theorem 2 pp.209–210; Lemma 2.8 pp.215–216; Prop. 2.13 pp.217–218; Cor. 2.15 p.218; Cor. 2.18 pp.220–221; Cor. 3.14 pp.231–232; Prop. 4.2 pp.233–234; Cor. 4.5 p.235; Prop. 4.7 and Cor. 4.8 pp.235–236; Lemma 5.5 pp.239–240; Thm. 5.12 pp.243–244. The new arguments use actual complete fibers, not merely injectivity of the finite-orbit restriction. The characterization (2), geometric-mark disjointness, physical intersection lemma and pruning argument are derived here.
- K. Kuratowski, Topology, vol. II, Academic Press 1968, §61 I, Theorem 2, p.506 (Janiszewski separation property of the sphere); Hahn–Mazurkiewicz theorem; standard characterization of dendrites as locally connected continua containing no simple closed curve; standard annular crosscut separation and Riemann mapping theorem for a full continuum. These are classical topology/analysis imports, not dynamical a priori bounds.
- A. Douady and J. H. Hubbard, On the dynamics of polynomial-like mappings, Ann. Sci. Éc. Norm. Sup. 18 (1985), 287–343, [Theorem 1, pp. 296–297](https://www.numdam.org/item/ASENS_1985_4_18_2_287_0/) (straightening, connected case); Sullivan's no-wandering theorem and Fatou classification, as used in terminal_relative_cover_alignment §3; J. Milnor, Dynamics in One Complex Variable, 3rd ed., Princeton 2006, §14 pp.156–160 (repelling periodic point density), §18 pp.188–204 (rational-ray landing and Douady–Yoccoz converse, Theorems 18.1–18.2, Lemma 18.3), §11 (postcritically finite corollaries); §16 pp.167–173 (Fatou classification), Appendix F pp.259–265 (no wandering). No a priori bounds imported.
- D. Dudko and M. Lyubich, [arXiv:2309.02107](https://arxiv.org/abs/2309.02107), locked Feigen.tex lines 953–978, and the archive's preceding model-lift criterion are background for the naming distinction, not an additional geometric identification imported here.

Repository graph: the base has 465 obligations, of which 316 proved, 34 imported and 115 open. The branch is an independent submission only. Per the task's file restriction only this directory, one workflow and one executable-registration row are added; the other proof-register/index changes requested by CONTRIBUTING are left for reviewed integration. Core prerequisite notes and relevant statements were examined; large unrelated portions of the repository-wide narrative/ledger output were fetched and parsed but not individually proof-checked. The author is GPT-6.2 (OpenAI), used for proof search, derivation, source checking, exact arithmetic regression and drafting. No independent human verification has occurred; all claims are submitted for mathematical review, and the executable is not a machine proof of the continuum claims.
