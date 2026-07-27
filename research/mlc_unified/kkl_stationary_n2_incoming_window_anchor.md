# Gate N2 frontier: the incoming occurrence-window anchor

Date: 2026-07-27  
Status: host-component reduction and two independence witnesses proved;
the KKL-specific contact, side, representative, interior, and anchor
clauses remain open

## 1. Result and exact boundary

This note attacks only the first analytic clause of
`KKL_STATIONARY_POINTWISE_TWO_PATH_BREAK` (Gate N2).  It does not use
Gate N2, a later stationary gate, VAAPC-I, UPTCR, or MLC.

Fix

\[
 n\in\{b,b+1\},\qquad h=n+1.
\tag{1.1}
\]

For an embedded target leaf \(\alpha\), every connected component \(C\)
of the inverse trace \(I_h^{-1}(|\alpha|)\) has one canonical open
target-parameter window

\[
 J(C)=(a,c)\subset(0,1).
\tag{1.2}
\]

This is a theorem about the host component \(C\).  It is **not** a
theorem about an arbitrary KKL proper path contained in \(C\): KKL
proper paths are not defined to be simple or component-maximal and can
retrace.

Fix a particular occurrence of the selected \(L_0^h\) access at target
parameter \(u\in(0,1)\).  To realize the incoming portion named at KKL
line 1603,

\[
 B L_0\rightsquigarrow L_0^h,
\tag{1.3}
\]

the proof must separately establish:

1. a typed one-sided germ at that exact contact occurrence;
2. a connected host \(C\) whose canonical window has \(c=u\), rather
   than \(a=u\);
3. an embedded component-maximal proper representative of \(C\);
4. proper landing at an interior deep encounter \(0<u<1\);
5. the anchored equality \(a=0\); and
6. the actual marked lift of the target \(B L_0\) endpoint access at
   the other end.

The locked source proves none of these six clauses for one common
restriction.  The first failure codes are

```text
N2-R00A_NO_TYPED_DEEP_COMPONENT
N2-R00B_WRONG_ONE_SIDED_INCIDENCE
N2-R00C_RETRACING_OR_NONMAXIMAL_REPRESENTATIVE
N2-R01_DEEP_NONLANDING_OR_NONINTERIOR
N2-R02_INCOMING_WINDOW_START_POSITIVE
N2-R03_ZERO_START_WRONG_BL0_LIFT
```

These failures occur before bilateral incidence, filter survival,
corridor confinement, and deck noncollision.  Gate N2 remains open.

## 2. Source lock and exact range

The KKL source is

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The Kahn source used to audit the local embedding alternative is

```text
.tmp_kl06_source/psiql2.tex
SHA-256 E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228
```

The proof-used indices are

\[
\begin{array}{c|c|c|c}
n&h&\text{leaf family}&\text{corrected source continuum}\\ \hline
b&b+1=N-2&A_{b+1}&Q_b\\
b+1&b+2=N-1&A_{b+2}&Q_{b+1}.
\end{array}
\tag{2.1}
\]

Here \(Q_0\) is the actual critical member of the primitive
small-Julia cycle and \(Q_n=\phi_0^n(Q_0)\).  This is the corrected
package replacing the undefined printed \(K_0^0\); it does not yet
give \(Q_n\) a full-carrier separator role.

No \(A_N\) is defined.  The corrected N2 proof-use range uses only
\(A_{N-2}\) and \(A_{N-1}\); the occurrence of \(A_N\) in the
printed concluding sentence at line 1605 is ill-typed and is not used
by the corrected argument.

The authoritative native QA classifies two printed source assertions
as open or conditional:

- line 1598, \(L_0^b\cap T=\varnothing\), is now reduced to the exact
  marked-core incidence predicate \(\mathrm{MCI}_b\); it is proved in
  the locally connected physical category and in the combinatorial
  model.  The terminal inverse-sheet geometry used in that proof is
  valid without local connectivity.  A proved monotone full-lift
  criterion reduces the remaining non-locally-connected case to
  monotonicity, singleton selected-preperiodic fibers, exact
  full-carrier lift, and marked limb/component correspondence; those
  source-identification clauses remain open;
- line 1600, existence of one proper retained restriction ending at
  \(L_0^h\), lacks complete-horizon properness, marking/filter
  survival, and occurrence provenance.

Accordingly neither assertion is silently imported below.

## 3. Host-component occurrence-window theorem

### Theorem 3.1

Let

\[
 \alpha:(0,1)\longrightarrow Y
\tag{3.1}
\]

be a topological embedding and let

\[
 I:X\longrightarrow Y
\tag{3.2}
\]

be a local homeomorphism.  For every connected component \(C\) of

\[
 I^{-1}(|\alpha|),
\tag{3.3}
\]

there are unique \(0\leq a<c\leq1\) and a unique homeomorphism

\[
 t_C:C\xrightarrow{\;\cong\;}(a,c)
\tag{3.4}
\]

such that

\[
 I|_C=\alpha\circ t_C.
\tag{3.5}
\]

Fix a selected \(L_0^h\) contact occurrence
\(\xi=(u,e_{\rm deep})\), where \(u\in(0,1)\) is its parameter along
\(\alpha\) and \(e_{\rm deep}\) is its marked access.  Suppose
additionally that:

1. the specified one-sided germ at \(\xi\) is the incoming germ
   \(\alpha((u-\epsilon,u))\), and its lift belongs to \(C\);
2. \(C\) is proper at both ideal ends in the marked source surface;
3. the \(c\)-end of \(C\) lands at \(e_{\rm deep}\) and \(c=u\); and
4. the proof-used restriction is an embedded, component-maximal
   parametrization of \(C\).

Then that restriction realizes the entire incoming portion (1.3) if
and only if

\[
 a=0
\tag{3.6}
\]

and its \(a\)-end is the actual marked lift of the target
\(B L_0\) endpoint access.

#### Proof

Because \(I\) is a local homeomorphism and \(\alpha\) is embedded,
\(I^{-1}(|\alpha|)\) is locally a one-manifold.  Define

\[
 t_C=\alpha^{-1}\circ I|_C:C\longrightarrow(0,1).
\tag{3.7}
\]

This is a local homeomorphism.  The component \(C\) is a connected,
second-countable one-manifold without boundary, so it is homeomorphic
to either a circle or a line.  A circular component is impossible:
its image under \(t_C\) would be nonempty, compact, and open in
\((0,1)\).

Choose an orientation on the line-type component \(C\).  The local
orientation sign of \(t_C\) is locally constant and therefore constant.
In an oriented coordinate \(C\cong\mathbb R\), a locally increasing
map is globally strictly increasing: for \(x<y\), compactness of
\([x,y]\) gives a finite ordered subdivision on which every successive
restriction is increasing.  The same argument applies after reversing
orientation if the sign is negative.  Hence \(t_C\) is injective.
It is open because it is a local homeomorphism, so its connected image
is one open interval \((a,c)\).  The inverse is continuous because
\(t_C\) is an open continuous bijection onto its image.  This proves
(3.4)--(3.5), including uniqueness of \(a,c\) and \(t_C\).

Under the four additional hypotheses, the incoming target portion has
parameter window \((0,u)\), whereas \(C\) has window \((a,u)\).
They agree exactly when \(a=0\).  Equality of windows does not identify
an ideal access.  Thus the \(a\)-end must independently be the actual
marked lift of the endpoint access of \(\alpha\) at \(B L_0\), not
merely an end carrying the same coarse \(B L_0\) label.  These
conditions are also sufficient. \(\square\)

### Corollary 3.2 (the exact hidden premises)

Even granting KKL line 1600 an existential proper path
\(\theta^*\subset I_h^{-1}(|\alpha|)\) ending at a named deep access
does not select a contact occurrence or one-sided germ.  It also does
not imply:

\[
\theta^*\text{ is an embedded component-maximal parametrization},
\tag{3.8}
\]

\[
0<u<1,
\tag{3.9}
\]

\[
a=0,
\tag{3.10}
\]

or that the deep access is the \(c\)-end rather than the \(a\)-end of
the host window.  Several inverse-trace components can meet the same
coarse \(L_0^h\) locus.  The component used by the proof is fixed only
after the contact occurrence and one-sided germ have been specified.
Failure of an arbitrarily chosen later component is therefore not a
countercertificate to the KKL claim.

Thus the target-level wording "starts at \(B L_0\), passes through
\(L_0^h\), and terminates elsewhere" does not by itself construct the
incoming proper restriction component used at line 1603.

## 4. Independence witnesses

### 4.1 Properness does not remove retracing

Take \(X=Y=\mathbb D\), \(I=\operatorname{id}\), and

\[
 \alpha(t)=i(2t-1),\qquad 0<t<1.
\tag{4.1}
\]

Let

\[
 g(t)=t+\frac1{10}\sin(4\pi t),\qquad
 \theta^*(t)=\alpha(g(t)).
\tag{4.2}
\]

The map \(g\) takes \((0,1)\) into itself.  On the first and last
quarter-intervals this follows from the sign of the sine term; on the
two middle quarter-intervals it follows from
\(t-\frac1{10}>0\) and \(t+\frac1{10}<1\), respectively.  It also has
endpoint limits \(0,1\).  Therefore \(\theta^*\) is a proper path
contained in \(I^{-1}(|\alpha|)\).  But

\[
 g'(t)=1+\frac{2\pi}{5}\cos(4\pi t)
\tag{4.3}
\]

is negative where \(\cos(4\pi t)=-1\).  Hence \(\theta^*\) retraces and
is not a monotone parametrization of its host component.  Quotienting
paths by homeomorphic reparametrization does not erase retracing.

This disproves the inference

\[
\text{proper path in an inverse trace}
\Longrightarrow
\text{embedded component-maximal representative}.
\tag{4.4}
\]

### 4.2 A deep-ending host need not be anchored

Let

\[
 Y=\mathbb D,\qquad
 X=\mathbb D\setminus[0,1),\qquad
 I:X\hookrightarrow Y.
\tag{4.5}
\]

Because \(1\notin\mathbb D\), the slit is relatively closed and \(X\)
is a Riemann surface.  Let \(\alpha\) be the polygonal proper path,
oriented in the listed order, through

\[
\begin{aligned}
p&=i,&s_1&=0.8,&u_1&=0.65-0.15i,\\
r&=0.5,&u_2&=0.35+0.15i,&s_2&=0.2,&q&=-i.
\end{aligned}
\tag{4.6}
\]

The five supporting lines, with their respective \(x\)-ranges, are

\[
\begin{array}{c|c}
\text{piece}&\text{equation}\\ \hline
p s_1&y=1-\frac54x,\quad 0\leq x\leq\frac45,\\
s_1u_1&y=x-\frac45,\quad \frac{13}{20}\leq x\leq\frac45,\\
u_1r\cup ru_2&y=\frac12-x,\quad
  \frac7{20}\leq x\leq\frac{13}{20},\\
u_2s_2&y=x-\frac15,\quad
  \frac15\leq x\leq\frac7{20},\\
s_2q&y=5x-1,\quad 0\leq x\leq\frac15.
\end{array}
\tag{4.7}
\]

Solving the line equations shows that every nonadjacent intersection
has \(x\)-coordinate outside at least one of the displayed ranges:
\(2,\ 8/15,\ 8/25,\ 1/20,\ 1/4\), as applicable; the remaining
nonadjacent pair is parallel.  Adjacent pieces meet only at their
listed common vertex.  The zeros of the displayed equations occur
exactly at \(x=4/5,1/2,1/5\), so the slit encounters are exactly
\(s_1,r,s_2\).  Strict convexity of \(\mathbb D\) puts the open polygon
in \(\mathbb D\), with only \(p,q\) on \(\partial\mathbb D\).

The open subpath

\[
 s_1\longrightarrow u_1\longrightarrow r
\tag{4.8}
\]

is therefore a proper connected component of the inverse trace ending
at the access over \(r\), but its window begins strictly after the
initial target end \(p\).  The earlier slit encounter at \(s_1\)
prevents any one inverse component from joining \(p\) to \(r\).

This is not a KKL stationary block.  It proves the abstract
independence

\[
\begin{split}
 &\alpha\text{ has a specified initial target end},\\
 &\exists\text{ a proper inverse component ending at a later encounter}
\end{split}
\not\Longrightarrow
\text{that component has }a=0.
\tag{4.9}
\]

It also shows why an arbitrary late component is not the desired
negative certificate: the KKL-specific proof must first select the
contact occurrence and incoming-side germ that it claims to use.

## 5. The unproved interior-encounter clause

KKL line 1598 counts small-Julia cycle components in the critical limb
and then states

\[
 L_0^b\cap T=\varnothing.
\tag{5.1}
\]

The separate endpoint audit now proves five parts that were formerly
bundled into one alleged endpoint lemma:

1. the \(Q_0\)-selected component chain \(\mathrm{SC}_H\), its
   small-Julia predecessor chain, and the point chain
   \(\mathrm{APC}_H\) exist through \(H=b+2\);
2. the domains \(\Omega_n=\phi_0^n(\mathfrak L_0)\) have the exact
   singleton boundary \(\{\alpha^n\}\) and are punctured-filled-set
   components, without assuming local connectivity;
3. actual contact of a cycle component with \(L_0^n\) forces
   containment of that whole component;
4. the primitive component period satisfies \(P\ge q\);
5. the explicit high-type inequality \(q>b\) excludes repetition
   among the first \(b+1\) cycle components.

The audit then proves the following predicate in the locally connected
physical category and in KKL's finite combinatorial model:

\[
 \mathrm{MCI}_b:\qquad
 L_0^b\cap T\ne\varnothing
 \Longrightarrow
 \exists K\in\operatorname{Comp}\mathcal K
 \text{ with }K\cap L_0^b\ne\varnothing .
\tag{5.2}
\]

The only remaining set-theoretic line-1598 clause is its physical
non-locally-connected lift.  The endpoint audit proves that a
continuous monotone semiconjugacy with singleton
\(\alpha^0\) fiber, correctly matched
\(\alpha^0,\ldots,\alpha^H\) labels (which then force singleton
predecessor fibers), exact
\(T=\pi^{-1}(T_{\rm com})\), and marked component/limb correspondence
forces
\(\pi^{-1}(L_{0,\rm com}^n)=L_0^n\) and hence actual \(K\)-contact.
The locked KKL and Dudko--Lyubich passages do not state this full
package.  Under it, the parabolic \(b\)-bound and \(q>b\) complete the
counting contradiction.  The constructed horizon recursion gives

\[
 F^{h-b}(L_0^h)\subset L_0^b
\tag{5.3}
\]

for \(h=b+1,b+2\), so forward invariance then gives the deeper set
disjointness.  What remains for the incoming anchor is still geometric:
prove the full-carrier separator predicate \(\mathrm{KSEP}_H\), prove
conditional compatibility of any supplied proof-used occurrence with
the canonical chain, either prove the selected endpoint/access coherence
\(\mathrm{EGC}_H\), or construct the marked access directly, and then
realize the selected contact as a proper interior occurrence at some
\(u\in(0,1)\).  The present note promotes neither the non-LC physical
lift nor that access theorem.

## 6. What local embeddedness does and does not supply

Kahn proves that the immersion embeds a neighborhood of the pulled
filled set.  When a selected encounter is independently shown to lie
in that neighborhood, this supplies a local embedded collar.  It does
not:

1. turn an arbitrary retracing proper path into a component
   parametrization;
2. prove proper landing at both ends of the host component;
3. prove, where needed, the non-LC selected-component and marked-fiber
   lift of \(\mathrm{MCI}_b\);
4. exclude an earlier component or repeated access along \((0,u)\);
5. exclude exit from the domain of the direct inclusion, incidence
   with a removed tree component, or landing at the wrong ideal access.

For the direct \(I_h\) arrow used here, the relevant map is an
inclusion, so "sheet change" is not a correctly typed direct
obstruction.  Sequential sheet words arise only later, when the two
portions are transported through the complete binder horizon.  A local
collar near one endpoint cannot supply the global target portion.

## 7. Exact anchor and failure records

The positive one-stage anchor record is

\[
\mathfrak a^-_{h,\alpha}
=
\left(
\alpha,h;\xi,\varepsilon=-;
C^-,J^-;
e^-_{\rm far},e^-_{\rm deep};
X^-_{\rm far},\mathbf p^-
\right).
\tag{7.1}
\]

It must certify

\[
\begin{split}
 &\xi=(u,e_{L_0^h})\text{ is the selected contact occurrence},\\
 &\varepsilon=-\text{ selects the incoming target germ }(u-\epsilon,u),\\
 &C^-\text{ is embedded, component-maximal, and proper at both ends},\\
 &0<u<1,\qquad J^-=(0,u),\\
 &e^-_{\rm far}=\widetilde e_{B L_0}\text{ is the actual marked lift},\\
 &e^-_{\rm deep}=e_{L_0^h}.
\end{split}
\tag{7.2}
\]

The parent datum \(\mathbf p^-\) distinguishes repeated components
with the same coarse locus.  Sheet, filter, and complete segmented
prefix words are deliberately absent from this early record: they
belong to the later two-occurrence binder, not to the one-stage anchor.

On failure, record the first applicable certificate:

1. `N2-R00A_NO_TYPED_DEEP_COMPONENT`: no specified contact occurrence,
   one-sided germ, or connected host;
2. `N2-R00B_WRONG_ONE_SIDED_INCIDENCE`: the chosen host has
   \(u=a\), not \(u=c\);
3. `N2-R00C_RETRACING_OR_NONMAXIMAL_REPRESENTATIVE`: the supplied
   restriction retraces or is not the whole host component;
4. `N2-R01_DEEP_NONLANDING_OR_NONINTERIOR`: the selected host does not
   land properly at an interior target parameter \(0<u<1\);
5. `N2-R02_INCOMING_WINDOW_START_POSITIVE`: the incoming host has
   \(J^-=(a,u)\) with \(a>0\);
6. `N2-R03_ZERO_START_WRONG_BL0_LIFT`: \(a=0\), but the far end is not
   the actual marked lift \(\widetilde e_{B L_0}\).

A coarse statement that the target path "reaches \(L_0^h\)" is not a
substitute for (7.2).

## 8. Selected sufficient architecture for the remainder of Gate N2

The project selects the following sufficient architecture for the
remainder of Gate N2.  This is a dependency discipline for this proof
program, not a claim that every logically possible repair must proceed
in this order.  Once (7.2) is established, the program will:

1. construct the outgoing record at the **same** target parameter
   \(u\), with one-sided germ \((u,u+\epsilon)\) and window \((u,1)\);
2. couple both records to that same complete contact occurrence
   \(\xi=(u,e_{L_0^h})\);
3. propagate both segmented records through the same horizon;
4. prove fine-marking and coarse-filter survival; and
5. test terminal geometric noncollision.

For the selected-collar route, the exact final test is

\[
 [\lambda^+]\ne[\tau_n(\lambda^-)],
\tag{8.1}
\]

not merely a comparison of coarse component or sheet labels.

The selected sufficient dependency order is

\[
\boxed{
\begin{array}{c}
\text{typed contact occurrence and one-sided host component}\\
\downarrow\\
\text{component-maximal proper representative and incoming anchor}\\
\downarrow\\
\text{bilateral realization and filter/horizon survival}\\
\downarrow\\
\text{collar confinement and deck-path noncollision}.
\end{array}}
\tag{8.2}
\]

## 9. Skeptic audit

1. KKL line 1600 is granted neither properness nor retention as a
   theorem of this note.
2. A KKL proper path is not assumed embedded or component-maximal.
3. The component theorem is not transferred to a retracing path.
4. A deep-ending component is not reoriented into an incoming one.
5. Multiple components at one coarse deep locus are not conflated.
6. Line 1598 is not treated as globally or unconditionally proved;
   only its locally connected case and a conditional non-LC reduction
   are proved.
7. The actual access clause is separate from \(a=0\).
8. Kahn's local embedding is not extended beyond its proved domain.
9. The planar witnesses are not called KKL counterexamples.
10. No filter survival follows from host-component topology.
11. The corrected range is \(n=b,b+1\); the printed \(A_N\) is
    undefined and is not imported.
12. N2, N3, N4, the stationary repair, VAAPC-I, UPTCR, and MLC remain
    open.

## 10. Binary status

| assertion | status |
|---|---|
| canonical open window for each fixed inverse-trace host component | **proved** |
| conditional incoming criterion \(c=u\), \(a=0\), and actual \(B L_0\) lift | **proved** |
| proper path implies embedded component-maximal representative | **refuted in the abstract** |
| deep-ending host is automatically on the incoming side | **refuted as an inference** |
| line-1598 interior-deep conclusion | **open/conditional** |
| actual KKL typed contact and incoming-side host | **open** |
| actual KKL component-maximal proper representative | **open** |
| actual KKL incoming anchor | **open** |
| Gate N2 pointwise terminal two-path break | **open** |
