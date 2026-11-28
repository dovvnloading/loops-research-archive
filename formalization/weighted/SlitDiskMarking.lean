import SlitDiskCayley
import MarkedSlitTransport

/-!
# The actual four cuts in squared Cayley coordinates

The order of all four physical cuts is preserved by the explicit real
restriction of the disk-to-slit-plane map.
-/

namespace SlitDiskMarking

open Set MarkedSlitTransport
noncomputable section

theorem marking_left_mem_Ioo {R : ℝ} (M : Marking)
    (hleft : -R < M.left) (hright : M.right < R) : M.left ∈ Ioo (-R) R :=
  ⟨hleft, lt_trans M.left_lt_first (lt_trans M.first_lt_second
    (lt_trans M.second_lt_right hright))⟩

theorem marking_first_mem_Ioo {R : ℝ} (M : Marking)
    (hleft : -R < M.left) (hright : M.right < R) : M.first ∈ Ioo (-R) R :=
  ⟨lt_trans hleft M.left_lt_first, lt_trans M.first_lt_second
    (lt_trans M.second_lt_right hright)⟩

theorem marking_second_mem_Ioo {R : ℝ} (M : Marking)
    (hleft : -R < M.left) (hright : M.right < R) : M.second ∈ Ioo (-R) R :=
  ⟨lt_trans hleft (lt_trans M.left_lt_first M.first_lt_second),
    lt_trans M.second_lt_right hright⟩

theorem marking_right_mem_Ioo {R : ℝ} (M : Marking)
    (hleft : -R < M.left) (hright : M.right < R) : M.right ∈ Ioo (-R) R :=
  ⟨lt_trans hleft (lt_trans M.left_lt_first
    (lt_trans M.first_lt_second M.second_lt_right)), hright⟩

/-- The four actual real cuts after applying the squared Cayley map. -/
def transformedMarking {R : ℝ} (hR : 0 < R) (M : Marking)
    (hleft : -R < M.left) (hright : M.right < R) : Marking where
  left := SlitDiskCayley.realMap R M.left
  first := SlitDiskCayley.realMap R M.first
  second := SlitDiskCayley.realMap R M.second
  right := SlitDiskCayley.realMap R M.right
  left_lt_first := SlitDiskCayley.realMap_strictMonoOn hR
    (marking_left_mem_Ioo M hleft hright) (marking_first_mem_Ioo M hleft hright)
    M.left_lt_first
  first_lt_second := SlitDiskCayley.realMap_strictMonoOn hR
    (marking_first_mem_Ioo M hleft hright) (marking_second_mem_Ioo M hleft hright)
    M.first_lt_second
  second_lt_right := SlitDiskCayley.realMap_strictMonoOn hR
    (marking_second_mem_Ioo M hleft hright) (marking_right_mem_Ioo M hleft hright)
    M.second_lt_right

@[simp] theorem transformedMarking_left {R : ℝ} (hR : 0 < R) (M : Marking)
    (hleft : -R < M.left) (hright : M.right < R) :
    (transformedMarking hR M hleft hright).left = SlitDiskCayley.realMap R M.left := rfl

@[simp] theorem transformedMarking_first {R : ℝ} (hR : 0 < R) (M : Marking)
    (hleft : -R < M.left) (hright : M.right < R) :
    (transformedMarking hR M hleft hright).first = SlitDiskCayley.realMap R M.first := rfl

@[simp] theorem transformedMarking_second {R : ℝ} (hR : 0 < R) (M : Marking)
    (hleft : -R < M.left) (hright : M.right < R) :
    (transformedMarking hR M hleft hright).second = SlitDiskCayley.realMap R M.second := rfl

@[simp] theorem transformedMarking_right {R : ℝ} (hR : 0 < R) (M : Marking)
    (hleft : -R < M.left) (hright : M.right < R) :
    (transformedMarking hR M hleft hright).right = SlitDiskCayley.realMap R M.right := rfl

theorem transformedMarking_left_neg {R : ℝ} (hR : 0 < R) (M : Marking)
    (hleft : -R < M.left) (hright : M.right < R) :
    (transformedMarking hR M hleft hright).left < 0 :=
  SlitDiskCayley.realMap_neg (marking_left_mem_Ioo M hleft hright)

theorem transformedMarking_second_neg {R : ℝ} (hR : 0 < R) (M : Marking)
    (hleft : -R < M.left) (hright : M.right < R) :
    (transformedMarking hR M hleft hright).second < 0 :=
  SlitDiskCayley.realMap_neg (marking_second_mem_Ioo M hleft hright)

end
end SlitDiskMarking
