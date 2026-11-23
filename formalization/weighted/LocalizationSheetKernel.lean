import Mathlib.Topology.Homotopy.Lifting

/-!
# Paper 1: algebraic kernel of canonical localization sheets

Source: Paper 1, "Canonical sheet resolution", especially the pullback
subgroup K = a_*⁻¹(H_t), the based fiber K/H_s, and the unique embedded
intermediate factor. The statements below formalize the **group/coset
part** of this picture for arbitrary (possibly nonnormal) subgroups.

The last section constructs the correspondence for actual based covering
maps with path-connected total space, by lifting paths. A particular
KL covering square and a peripheral word in its subgroup difference
remain separate source-specific obligations.

A group is written multiplicatively. We use left cosets gH, with
g ~ h iff g⁻¹h ∈ H. Inversion exchanges the left/right conventions
used in the paper; no normality or group structure on cosets is assumed.
-/

namespace LoopsFormal.LocalizationSheets

variable {G : Type*} [Group G]

/-- The equivalence relation for left cosets by an arbitrary subgroup. -/
def cosetSetoid (H : Subgroup G) : Setoid G where
  r a b := a⁻¹ * b ∈ H
  iseqv := ⟨
    by intro a; simp,
    by
      intro a b hab
      simpa [mul_inv_rev] using H.inv_mem hab,
    by
      intro a b c hab hbc
      simpa [mul_assoc] using H.mul_mem hab hbc⟩

/-- A pointed sheet fiber, without assuming that the subgroup is normal. -/
def Sheets (H : Subgroup G) := Quotient (cosetSetoid H)

/-- The coset represented by a group element. -/
def sheet (H : Subgroup G) (g : G) : Sheets H := Quotient.mk _ g

/-- Exact membership test for equality of sheet representatives. -/
theorem sheet_eq_iff (H : Subgroup G) (a b : G) :
    sheet H a = sheet H b ↔ a⁻¹ * b ∈ H := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound h

/-- Reversing the order of the difference word can reject equal cosets
when conjugation takes a subgroup element outside the subgroup. -/
theorem reversed_difference_can_reject_equal_sheets (H : Subgroup G)
    (a k : G) (hk : k ∈ H) (hconj : a * k * a⁻¹ ∉ H) :
    sheet H a = sheet H (a * k) ∧ (a * k) * a⁻¹ ∉ H :=
  ⟨(sheet_eq_iff H a (a * k)).2 (by simpa using hk), hconj⟩

/-- In particular, the base sheet records exactly subgroup membership. -/
theorem base_sheet_eq_iff (H : Subgroup G) (g : G) :
    sheet H (1 : G) = sheet H g ↔ g ∈ H := by
  simpa using sheet_eq_iff H (1 : G) g

/-- Inclusion of localization subgroups induces a canonical
coarsening map between their based sheet fibers. -/
def coarsen {H K : Subgroup G} (hHK : H ≤ K) : Sheets H → Sheets K :=
  Quotient.lift (fun g => sheet K g) (by
    intro a b hab
    exact (sheet_eq_iff K a b).2 (hHK hab))

@[simp] theorem coarsen_sheet {H K : Subgroup G} (hHK : H ≤ K) (g : G) :
    coarsen hHK (sheet H g) = sheet K g := rfl

/-- Every coarser sheet has a representative in the finer cover. -/
theorem coarsen_surjective {H K : Subgroup G} (hHK : H ≤ K) :
    Function.Surjective (coarsen hHK) := by
  intro y
  refine Quotient.inductionOn y ?_
  intro g
  exact ⟨sheet H g, rfl⟩

/-- Coarsening loses no information when its two subgroups agree. -/
theorem coarsen_injective_of_eq {H K : Subgroup G}
    (hHK : H ≤ K) (heq : H = K) :
    Function.Injective (coarsen hHK) := by
  subst K
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b => exact hxy

/-- The exact one-sheet criterion: coarsening is injective precisely
when the source and pullback subgroups are equal. -/
theorem coarsen_injective_iff {H K : Subgroup G} (hHK : H ≤ K) :
    Function.Injective (coarsen hHK) ↔ H = K := by
  constructor
  · intro hinj
    apply le_antisymm hHK
    intro g hg
    have hK : coarsen hHK (sheet H (1 : G)) =
        coarsen hHK (sheet H g) := by
      change sheet K (1 : G) = sheet K g
      exact (base_sheet_eq_iff K g).2 hg
    exact (base_sheet_eq_iff H g).1 (hinj hK)
  · exact coarsen_injective_of_eq hHK

/-- A defect element in K \\ H explicitly creates two different
source sheets which the coarsened map identifies. -/
theorem defect_forces_collision {H K : Subgroup G}
    (hHK : H ≤ K) (g : G) (hgK : g ∈ K) (hgH : g ∉ H) :
    ∃ x y : Sheets H, x ≠ y ∧ coarsen hHK x = coarsen hHK y := by
  refine ⟨sheet H 1, sheet H g, ?_, ?_⟩
  · intro h
    exact hgH ((base_sheet_eq_iff H g).1 h)
  · change sheet K 1 = sheet K g
    exact (base_sheet_eq_iff K g).2 hgK

/-- All and only the K-equivalent source representatives are merged. -/
theorem coarsen_representatives_iff {H K : Subgroup G}
    (hHK : H ≤ K) (a b : G) :
    coarsen hHK (sheet H a) = coarsen hHK (sheet H b) ↔
      a⁻¹ * b ∈ K := by
  change sheet K a = sheet K b ↔ _
  exact sheet_eq_iff K a b

/-- Sequential sheet coarsening is exactly coarsening by the composite
subgroup inclusion (no normal-subgroup hypothesis). -/
theorem coarsen_comp {H L K : Subgroup G}
    (hHL : H ≤ L) (hLK : L ≤ K) (x : Sheets H) :
    coarsen hLK (coarsen hHL x) =
      coarsen (hHL.trans hLK) x := by
  induction x using Quotient.inductionOn with
  | h g => rfl

/-- The kernel-equivalence relation of a coarsening map uniquely
determines its intermediate subgroup among all subgroups above H. -/
theorem equal_sheet_kernels_force_equal_subgroups
    {H K L : Subgroup G} (hHK : H ≤ K) (hHL : H ≤ L)
    (hkernels : ∀ x y : Sheets H,
      (coarsen hHK x = coarsen hHK y ↔
       coarsen hHL x = coarsen hHL y)) : K = L := by
  apply le_antisymm
  · intro g hg
    have hK : coarsen hHK (sheet H 1) =
        coarsen hHK (sheet H g) := by
      change sheet K 1 = sheet K g
      exact (base_sheet_eq_iff K g).2 hg
    have hL := (hkernels _ _).mp hK
    exact (base_sheet_eq_iff L g).1 (by simpa using hL)
  · intro g hg
    have hL : coarsen hHL (sheet H 1) =
        coarsen hHL (sheet H g) := by
      change sheet L 1 = sheet L g
      exact (base_sheet_eq_iff L g).2 hg
    have hK := (hkernels _ _).mpr hL
    exact (base_sheet_eq_iff K g).1 (by simpa using hK)

/-- If a proposed intermediate subgroup L is between H and K,
its remaining map to the K-fiber is injective iff L = K.
This is the algebraic reflection/optimality part of Paper 1. -/
theorem intermediate_injective_iff
    {H L K : Subgroup G} (_hHL : H ≤ L) (hLK : L ≤ K) :
    Function.Injective (coarsen hLK) ↔ L = K :=
  coarsen_injective_iff hLK

section Target

variable {T : Type*} [Group T]

/-- The subgroup selected by the target cover, pulled back along a
map of fundamental groups. -/
def pullbackSubgroup (φ : G →* T) (J : Subgroup T) : Subgroup G :=
  J.comap φ

/-- The induced target-sheet map at the *exact* pullback subgroup. -/
def resolvedTarget (φ : G →* T) (J : Subgroup T) :
    Sheets (pullbackSubgroup φ J) → Sheets J :=
  Quotient.lift (fun g => sheet J (φ g)) (by
    intro a b hab
    apply (sheet_eq_iff J (φ a) (φ b)).2
    change φ (a⁻¹ * b) ∈ J at hab
    simpa only [map_mul, map_inv] using hab)

@[simp] theorem resolvedTarget_sheet
    (φ : G →* T) (J : Subgroup T) (g : G) :
    resolvedTarget φ J (sheet (pullbackSubgroup φ J) g) =
      sheet J (φ g) := rfl

/-- This resolved leg is injective, even when φ itself has a kernel.
Its source cosets have already identified exactly that kernel. -/
theorem resolvedTarget_injective (φ : G →* T) (J : Subgroup T) :
    Function.Injective (resolvedTarget φ J) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
      apply (sheet_eq_iff (pullbackSubgroup φ J) a b).2
      have hJ : (φ a)⁻¹ * φ b ∈ J := by
        apply (sheet_eq_iff J (φ a) (φ b)).1
        exact hxy
      change φ (a⁻¹ * b) ∈ J
      simpa only [map_mul, map_inv] using hJ

/-- The original target leg factors through the canonical sheet
coarsening. The only assumption is source-subgroup compatibility. -/
def originalTarget (φ : G →* T) (J : Subgroup T)
    {H : Subgroup G} (hHK : H ≤ pullbackSubgroup φ J) :
    Sheets H → Sheets J :=
  resolvedTarget φ J ∘ coarsen hHK

@[simp] theorem originalTarget_sheet
    (φ : G →* T) (J : Subgroup T)
    {H : Subgroup G} (hHK : H ≤ pullbackSubgroup φ J) (g : G) :
    originalTarget φ J hHK (sheet H g) = sheet J (φ g) := rfl

/-- Exact equality of the kernel pairs of the original map and the
canonical coarsening (Paper 1, sheet-resolution items 4 and 5). -/
theorem original_kernel_eq_resolved_kernel
    (φ : G →* T) (J : Subgroup T)
    {H : Subgroup G} (hHK : H ≤ pullbackSubgroup φ J)
    (x y : Sheets H) :
    originalTarget φ J hHK x = originalTarget φ J hHK y ↔
      coarsen hHK x = coarsen hHK y := by
  constructor
  · intro h
    exact resolvedTarget_injective φ J h
  · exact congrArg (resolvedTarget φ J)

/-- A detected collision is exactly membership of the difference
word in the target subgroup: neither winding nor normality suffices. -/
theorem original_representatives_collision_iff
    (φ : G →* T) (J : Subgroup T)
    {H : Subgroup G} (hHK : H ≤ pullbackSubgroup φ J)
    (a b : G) :
    originalTarget φ J hHK (sheet H a) =
      originalTarget φ J hHK (sheet H b) ↔
      φ (a⁻¹ * b) ∈ J := by
  rw [original_kernel_eq_resolved_kernel]
  exact coarsen_representatives_iff hHK a b

/-- The exact subgroup reflection criterion for the original lift's
sheet action, with no assumption that φ is injective. -/
theorem original_injective_iff_pullback_equal
    (φ : G →* T) (J : Subgroup T)
    {H : Subgroup G} (hHK : H ≤ pullbackSubgroup φ J) :
    Function.Injective (originalTarget φ J hHK) ↔
      H = pullbackSubgroup φ J := by
  constructor
  · intro hinj
    apply (coarsen_injective_iff hHK).mp
    intro x y hxy
    apply hinj
    exact congrArg (resolvedTarget φ J) hxy
  · intro heq
    have hcoarse := (coarsen_injective_iff hHK).mpr heq
    intro x y hxy
    apply hcoarse
    exact (resolvedTarget_injective φ J) hxy

/-- The canonical peripheral-word defect creates a genuine collision
at the abstract sheet-fiber level. Geometric existence of such a word
is the separate input from Paper 1's forced-collision theorem. -/
theorem original_defect_collision
    (φ : G →* T) (J : Subgroup T)
    {H : Subgroup G} (hHK : H ≤ pullbackSubgroup φ J)
    (g : G) (hTarget : φ g ∈ J) (hSource : g ∉ H) :
    ∃ x y : Sheets H, x ≠ y ∧
      originalTarget φ J hHK x = originalTarget φ J hHK y := by
  obtain ⟨x, y, hne, heq⟩ :=
    defect_forces_collision hHK g hTarget hSource
  exact ⟨x, y, hne, congrArg (resolvedTarget φ J) heq⟩

end Target

section BasedCover

open Set Path.Homotopic

variable {E X F Y : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [TopologicalSpace F] [TopologicalSpace Y]

/-- Paper 1, Theorem `sheet-resolution`, based-fiber step. A loop closes
up at the chosen point exactly when its class comes from a loop upstairs. -/
theorem endpoint_closed_iff (p : C(E, X)) (hp : IsCoveringMap p) (e : E)
    (g : FundamentalGroup X (p e)) :
    hp.monodromy g ⟨e, rfl⟩ = ⟨e, rfl⟩ ↔ g ∈ (FundamentalGroup.map p e).range := by
  let b : p ⁻¹' {p e} := ⟨e, rfl⟩
  constructor
  · intro h
    have hend : (hp.monodromy g b).val = e := congrArg Subtype.val h
    let γ := (hp.liftPathQuotient g b).cast rfl hend.symm
    refine ⟨FundamentalGroup.fromPath γ, ?_⟩
    change γ.map p = g
    dsimp only [γ]
    have hproj : (hp.liftPathQuotient g b).map p =
        g.toPath.cast b.property (hp.monodromy g b).property :=
      hp.map_liftPathQuotient g b
    rw [Quotient.map_cast, hproj]
    simp
  · rintro ⟨γ, rfl⟩
    exact hp.monodromy_map γ

/-- Equality of two actual lift endpoints uses g⁻¹h (the gH convention).
The subgroup is constructed as the image of the induced map on π₁. -/
theorem endpoints_eq_iff (p : C(E, X)) (hp : IsCoveringMap p) (e : E)
    (g h : FundamentalGroup X (p e)) :
    hp.monodromy g ⟨e, rfl⟩ = hp.monodromy h ⟨e, rfl⟩ ↔
      g⁻¹ * h ∈ (FundamentalGroup.map p e).range := by
  letI := hp.fundamentalGroupMulAction (p e)
  let b : p ⁻¹' {p e} := ⟨e, rfl⟩
  rw [← endpoint_closed_iff p hp e]
  change g • b = h • b ↔ (g⁻¹ * h) • b = b
  rw [mul_smul]
  constructor
  · intro hab
    rw [← hab, inv_smul_smul]
  · intro hab
    calc
      g • b = g • (g⁻¹ • (h • b)) := congrArg (g • ·) hab.symm
      _ = h • b := smul_inv_smul _ _

/-- Endpoint lifting constructs the bijection to the *whole* based fiber.
Path connectedness is used only for surjectivity. -/
noncomputable def sheetsEquivFiber (p : C(E, X)) (hp : IsCoveringMap p)
    [PathConnectedSpace E] (e : E) :
    Sheets (FundamentalGroup.map p e).range ≃ (p ⁻¹' {p e}) := by
  let f : Sheets (FundamentalGroup.map p e).range → (p ⁻¹' {p e}) :=
    _root_.Quotient.lift (fun g => hp.monodromy g ⟨e, rfl⟩)
      (fun g h hgh => (endpoints_eq_iff p hp e g h).2 hgh)
  apply Equiv.ofBijective f
  constructor
  · intro x y
    induction x using _root_.Quotient.inductionOn with | h g =>
      induction y using _root_.Quotient.inductionOn with | h h =>
        exact fun heq => (sheet_eq_iff _ g h).2 ((endpoints_eq_iff p hp e g h).1 heq)
  · intro z
    let γ := Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath e z.val)
    let loop := (γ.map p).cast rfl z.property.symm
    refine ⟨sheet _ (FundamentalGroup.fromPath loop), ?_⟩
    apply hp.monodromy_eq_of_map_eq γ
    simp [loop]
    rfl

@[simp] theorem sheetsEquivFiber_sheet (p : C(E, X)) (hp : IsCoveringMap p)
    [PathConnectedSpace E] (e : E) (g : FundamentalGroup X (p e)) :
    sheetsEquivFiber p hp e (sheet _ g) = hp.monodromy g ⟨e, rfl⟩ := rfl

/-- The map on actual fibers is induced by the upper map of the covering
square. The equality of base maps fixes the marking used in both fibers. -/
def mapFiber (p : C(E, X)) (q : C(F, Y)) (a : C(X, Y)) (A : C(E, F))
    (square : q.comp A = a.comp p) {x : X} (e : p ⁻¹' {x}) : q ⁻¹' {a x} :=
  ⟨A e.val, (DFunLike.congr_fun square e.val).trans (congrArg a e.property)⟩

/-- Naturality is proved from the commutative square and uniqueness of
lifting. It is not an extra identification of an abstract table with A. -/
theorem mapFiber_monodromy (p : C(E, X)) (hp : IsCoveringMap p)
    (q : C(F, Y)) (hq : IsCoveringMap q) (a : C(X, Y)) (A : C(E, F))
    (square : q.comp A = a.comp p) {x y : X} (γ : Path.Homotopic.Quotient x y) (e : p ⁻¹' {x}) :
    hq.monodromy (γ.map a) (mapFiber p q a A square e) =
      mapFiber p q a A square (hp.monodromy γ e) := by
  let δ := hp.liftPathQuotient γ e
  apply hq.monodromy_eq_of_map_eq (δ.map A)
  apply eq_of_heq
  have hA : (δ.map A).map ⟨q, hq.continuous⟩ = δ.map (q.comp A) :=
    Quotient.map_comp.symm
  have hsquare : HEq (δ.map (q.comp A)) (δ.map (a.comp p)) := by rw [square]
  have hpA : δ.map (a.comp p) = (δ.map p).map a := Quotient.map_comp
  have hproj : δ.map p = γ.cast e.property (hp.monodromy γ e).property :=
    hp.map_liftPathQuotient γ e
  have hbase : HEq ((δ.map p).map a) (γ.map a) := by
    rw [hproj, Quotient.map_cast]
    exact Quotient.cast_heq ..
  exact (heq_of_eq hA).trans (hsquare.trans ((heq_of_eq hpA).trans
    (hbase.trans (Quotient.cast_heq ..).symm)))

/-- A defect on a specified physical square, witnessed by a loop which
fails to close upstairs on the source but closes on the target, forces a
collision of the actual upper map A. No embedding is needed here. -/
theorem physical_defect_collision (p : C(E, X)) (hp : IsCoveringMap p)
    (q : C(F, Y)) (hq : IsCoveringMap q) (a : C(X, Y)) (A : C(E, F))
    (square : q.comp A = a.comp p) (e : E) (g : FundamentalGroup X (p e))
    (hSource : g ∉ (FundamentalGroup.map p e).range)
    (hTarget : FundamentalGroup.mapOfEq a (DFunLike.congr_fun square e).symm g ∈
      (FundamentalGroup.map q (A e)).range) :
    ∃ z : E, z ≠ e ∧ p z = p e ∧ A z = A e := by
  let b : p ⁻¹' {p e} := ⟨e, rfl⟩
  let z := hp.monodromy g b
  refine ⟨z.val, ?_, z.property, ?_⟩
  · exact fun h => hSource ((endpoint_closed_iff p hp e g).1 (Subtype.ext h))
  · obtain ⟨δ, hδ⟩ := hTarget
    have hclosed : hq.monodromy (g.toPath.map a) (mapFiber p q a A square b) =
        mapFiber p q a A square b := by
      apply hq.monodromy_eq_of_map_eq (ex := mapFiber p q a A square b) (ey := mapFiber p q a A square b) δ.toPath
      rw [FundamentalGroup.mapOfEq_apply] at hδ
      change δ.toPath.map q = (g.toPath.map a).cast _ _ at hδ
      exact hδ
    exact congrArg Subtype.val ((mapFiber_monodromy p hp q hq a A square g b).symm.trans hclosed)

end BasedCover

#print axioms endpoint_closed_iff
#print axioms sheetsEquivFiber
#print axioms mapFiber_monodromy
#print axioms physical_defect_collision
#print axioms coarsen_injective_iff
#print axioms equal_sheet_kernels_force_equal_subgroups
#print axioms resolvedTarget_injective
#print axioms original_kernel_eq_resolved_kernel
#print axioms original_injective_iff_pullback_equal

end LoopsFormal.LocalizationSheets
