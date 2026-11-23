import ParabolicCenterBranch

/-! Match the archive's three independently isolated 2^-160 parameter
brackets to the exit-itinerary criterion, uniformly at every point of each
parameter bracket. All displayed rounded rows are rechecked in ℝ. -/

namespace LoopsParabolic
open Set
noncomputable section

private abbrev Box := ℝ × ℝ
private def grid (a b : ℕ) : Box := (a/1000000,b/1000000)
private def Valid (a b : ℝ) (target X : Box) : List Box → Prop
  | [] => target.1 ≤ X.1 ∧ X.2 ≤ target.2
  | Y::rest => 0 ≤ X.1 ∧ X.2 ≤ cap ∧ Y.1 ≤ H a X.1 ∧ H b X.2 ≤ Y.2 ∧
      Y.1 ≤ cap ∧ Valid a b target Y rest

private theorem replay {a b t : ℝ} (hab : t ∈ Icc a b)
    (ha : 0 ≤ a) (hb : b ≤ 1/100) (target : Box) (X : Box) (rest : List Box)
    (ok : Valid a b target X rest) {z : ℝ} (hz : z ∈ Icc X.1 X.2) :
    flight t z rest.length ∈ Icc target.1 target.2 := by
  induction rest generalizing z X with
  | nil => exact ⟨ok.1.trans hz.1,hz.2.trans ok.2⟩
  | cons Y rest ih =>
    obtain ⟨hX₁,hX₂,hY₁,hY₂,hcap,hv⟩ := ok
    have ht : t ∈ Icc 0 (1/100:ℝ) := ⟨ha.trans hab.1,hab.2.trans hb⟩
    have ha' : a ∈ Icc 0 (1/100:ℝ) := ⟨ha,hab.1.trans ht.2⟩
    have hb' : b ∈ Icc 0 (1/100:ℝ) := ⟨ht.1.trans hab.2,hb⟩
    have zl : X.1 ∈ Icc 0 cap := ⟨hX₁,(hz.1.trans hz.2).trans hX₂⟩
    have zu : X.2 ∈ Icc 0 cap := ⟨(hX₁.trans hz.1).trans hz.2,hX₂⟩
    have zm : z ∈ Icc 0 cap := ⟨hX₁.trans hz.1,hz.2.trans hX₂⟩
    have h₁ := ((channel_parameter_strictMono zl).monotoneOn ha' ht hab.1).trans
      (channel_mono ht zl zm hz.1)
    have h₂ := (channel_mono ht zm zu hz.2).trans
      ((channel_parameter_strictMono zu).monotoneOn ht hb' hab.2)
    rw [List.length_cons, ← flight_shift]
    exact ih Y hv ⟨le_min hcap (hY₁.trans h₁),(min_le_right _ _).trans (h₂.trans hY₂)⟩

/-- A closed cell of the exact grid used by the near-parabolic fixture. -/
def archiveDyadicCell (n : ℤ) : Set ℝ := Icc ((n:ℝ)/2^160) (((n:ℝ)+1)/2^160)

private def rows24 := [grid 48952 48958,grid 70670 70682,grid 94025 94047,
  grid 128240 128283,grid 194615 194716,grid 372715 373036]
private def rows27 := [grid 43824 43831,grid 61285 61297,grid 77869 77888,
  grid 98580 98613,grid 131059 131123,grid 196136 196286,grid 373128 373605]
private def rows30 := [grid 40350 40356,grid 55182 55193,grid 68026 68044,
  grid 82302 82330,grid 101543 101590,grid 132963 133054,grid 197238 197453,
  grid 373660 374346]

private theorem slab_of_rows {c a b : ℝ} (h : c+7/4 ∈ Icc a b)
    (ha : 0 ≤ a) (hb : b ≤ 1/100) (rows : List Box)
    (ok : Valid a b (7/20,19/50) (0,0) rows) : c+7/4 ∈ exitSlab rows.length := by
  refine ⟨⟨ha.trans h.1,h.2.trans hb⟩,?_⟩
  exact replay h ha hb _ _ _ ok (z := 0) ⟨le_rfl,le_rfl⟩

set_option maxRecDepth 4096 in
theorem archive_period24_exit {c : ℝ}
    (hc : c ∈ archiveDyadicCell (-2551914465108484579617401324842852154640068134308)) :
    c+7/4 ∈ exitSlab 6 := by
  apply slab_of_rows (a := 3909/1000000) (b := 3910/1000000) (rows := rows24)
  · obtain ⟨hl,hu⟩ := hc; norm_num at hl hu; constructor <;> linarith
  · norm_num
  · norm_num
  · norm_num [rows24,Valid,grid,H,cap]

set_option maxRecDepth 4096 in
theorem archive_period27_exit {c : ℝ}
    (hc : c ∈ archiveDyadicCell (-2553275755570421998660459007092359881945255630742)) :
    c+7/4 ∈ exitSlab 7 := by
  apply slab_of_rows (a := 2977/1000000) (b := 2978/1000000) (rows := rows27)
  · obtain ⟨hl,hu⟩ := hc; norm_num at hl hu; constructor <;> linarith
  · norm_num
  · norm_num
  · norm_num [rows27,Valid,grid,H,cap]

set_option maxRecDepth 4096 in
theorem archive_period30_exit {c : ℝ}
    (hc : c ∈ archiveDyadicCell (-2554197062530014440012717955456885164630387263690)) :
    c+7/4 ∈ exitSlab 8 := by
  apply slab_of_rows (a := 2347/1000000) (b := 2348/1000000) (rows := rows30)
  · obtain ⟨hl,hu⟩ := hc; norm_num at hl hu; constructor <;> linarith
  · norm_num
  · norm_num
  · norm_num [rows30,Valid,grid,H,cap]

#print axioms archive_period24_exit
#print axioms archive_period27_exit
#print axioms archive_period30_exit

end
end LoopsParabolic
