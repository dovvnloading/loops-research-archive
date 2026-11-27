import ChebyshevFibers
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

/-!
# Physical exterior sectors for the quadratic Chebyshev map

The projection in this file takes values in the actual complex plane:
`J (exp (t + 2 pi theta I))`, for the archive's quadratic `cquad (-2)`.
Its positive-height values lie outside the genuine bounded-orbit set.
The direct-branch sector maps and the central-overlap defect are proved
from this projection, without a hypothesis identifying a symbolic space
with a physical tile.
-/

namespace LoopsChebyshevDecoration

open Set Function LoopsChebyshev LoopsParabolic

noncomputable section

def address (theta t : ℝ) : ℂ :=
  Complex.exp ((t : ℂ) + ((2 * Real.pi * theta : ℝ) : ℂ) * Complex.I)

def point (theta t : ℝ) : ℂ := J (address theta t)

def sector (a b h : ℝ) : Set ℂ :=
  {z | ∃ theta t : ℝ, a < theta ∧ theta < b ∧ 0 < t ∧ t < h ∧
    point theta t = z}

def parentPiece (h : ℝ) : Set ℂ :=
  sector (1/6) (1/3) (h/2) ∪ sector (2/3) (5/6) (h/2) ∪
    {z : ℂ | ∃ x : ℝ, -1 < x ∧ x < 1 ∧ (x : ℂ) = z}

def leftExterior (h : ℝ) : Set ℂ :=
  sector (7/24) (1/3) (h/8) ∪ sector (2/3) (17/24) (h/8)

def rightExterior (h : ℝ) : Set ℂ :=
  sector (1/6) (5/24) (h/8) ∪ sector (19/24) (5/6) (h/8)

/-- Signed logarithmic height fills the real spine as well as both
exterior components. Negative height represents the lower component
through the reciprocal symmetry of the physical Joukowski map. -/
def puzzle (a b r : ℝ) : Set ℂ :=
  {z | ∃ theta t : ℝ, a < theta ∧ theta < b ∧ -r < t ∧ t < r ∧
    point theta t = z}

def parentDomain (h : ℝ) : Set ℂ := puzzle (1/6) (1/3) (h/2)

def leftDomain (h : ℝ) : Set ℂ := puzzle (7/24) (1/3) (h/8)

def rightDomain (h : ℝ) : Set ℂ := puzzle (1/6) (5/24) (h/8)

theorem address_norm (theta t : ℝ) : ‖address theta t‖ = Real.exp t := by
  simp [address, Complex.norm_exp]

theorem point_exterior (theta : ℝ) {t : ℝ} (ht : 0 < t) :
    point theta t ∉ realSegment 2 := by
  apply (exterior_image_iff _).mpr
  refine ⟨address theta t, ?_, rfl⟩
  rw [address_norm]
  exact Real.one_lt_exp_iff.mpr ht

/-- A full turn changes the logarithmic sheet, not its physical point. -/
theorem address_add_one (theta t : ℝ) :
    address (theta + 1) t = address theta t := by
  unfold address
  have he : (t : ℂ) + ((2 * Real.pi * (theta + 1) : ℝ) : ℂ) * Complex.I =
      ((t : ℂ) + ((2 * Real.pi * theta : ℝ) : ℂ) * Complex.I) +
        2 * Real.pi * Complex.I := by push_cast; ring
  rw [he, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem point_add_one (theta t : ℝ) :
    point (theta + 1) t = point theta t := by
  simp only [point, address_add_one]

private theorem address_equality {theta phi t s : ℝ}
    (ha : address theta t = address phi s) :
    t = s ∧ ∃ n : ℤ, theta = phi + (n : ℝ) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp ha
  have hr := congrArg Complex.re hn
  have hi := congrArg Complex.im hn
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    Complex.I_re, mul_one, mul_zero, zero_mul, zero_add, add_zero,
    sub_zero, Complex.intCast_re, Complex.intCast_im] at hr hi
  norm_num at hr hi
  refine ⟨hr, n, ?_⟩
  apply mul_left_cancel₀ (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
  nlinarith [hi]

theorem address_neg (theta t : ℝ) :
    address (-theta) (-t) = (address theta t)⁻¹ := by
  unfold address
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

theorem point_neg (theta t : ℝ) : point (-theta) (-t) = point theta t := by
  simp only [point, address_neg, J, inv_inv, add_comm]

theorem point_one_sub (theta t : ℝ) :
    point (1 - theta) (-t) = point theta t := by
  have he : 1 - theta = -theta + 1 := by ring
  rw [he, point_add_one, point_neg]

/-- The signed chart meets the genuine filled Julia set exactly on
its zero-height spine. -/
theorem point_mem_filled_iff (theta t : ℝ) :
    point theta t ∈ realSegment 2 ↔ t = 0 := by
  constructor
  · intro hz
    rcases lt_trichotomy t 0 with ht | ht | ht
    · have he := point_neg theta t
      exact (point_exterior (-theta) (neg_pos.mpr ht) (he.symm ▸ hz)).elim
    · exact ht
    · exact (point_exterior theta ht hz).elim
  · rintro rfl
    apply unit_image_realSegment
    change ‖address theta 0‖ = 1
    rw [address_norm, Real.exp_zero]

/-- The two exterior sectors are the complete complement of the real
spine in the whole physical puzzle, with exact reflected endpoints. -/
theorem puzzle_exterior_split (a b r : ℝ) :
    puzzle a b r \ realSegment 2 = sector a b r ∪ sector (1-b) (1-a) r := by
  ext z
  constructor
  · rintro ⟨⟨theta, t, ha, hb, ht0, ht1, rfl⟩, hz⟩
    have ht : t ≠ 0 := fun he => hz ((point_mem_filled_iff theta t).mpr he)
    rcases lt_or_gt_of_ne ht with ht | ht
    · right
      refine ⟨1-theta, -t, by linarith, by linarith, by linarith,
        by linarith, ?_⟩
      exact point_one_sub theta t
    · exact Or.inl ⟨theta, t, ha, hb, ht, ht1, rfl⟩
  · rintro (⟨theta, t, ha, hb, ht0, ht1, rfl⟩ |
      ⟨theta, t, ha, hb, ht0, ht1, rfl⟩)
    · exact ⟨⟨theta, t, ha, hb, by linarith, ht1, rfl⟩, point_exterior theta ht0⟩
    · refine ⟨⟨1-theta, -t, by linarith, by linarith, by linarith,
        by linarith, point_one_sub theta t⟩, point_exterior theta ht0⟩

theorem left_domain_exterior (h : ℝ) :
    leftDomain h \ realSegment 2 = leftExterior h := by
  have he := puzzle_exterior_split (7/24) (1/3) (h/8)
  norm_num at he
  exact he

theorem right_domain_exterior (h : ℝ) :
    rightDomain h \ realSegment 2 = rightExterior h := by
  have he := puzzle_exterior_split (1/6) (5/24) (h/8)
  norm_num at he
  exact he

theorem point_zero_height (theta : ℝ) :
    point theta 0 = ((2 * Real.cos (2 * Real.pi * theta) : ℝ) : ℂ) := by
  unfold point J address
  simp only [Complex.ofReal_zero, zero_add]
  rw [← Complex.exp_neg]
  rw [show -(((2 * Real.pi * theta : ℝ) : ℂ) * Complex.I) =
    -((2 * Real.pi * theta : ℝ) : ℂ) * Complex.I by ring,
    ← Complex.two_cos]
  push_cast
  rfl

theorem quarter_zero_is_critical : point (1/4) 0 = 0 := by
  rw [point_zero_height]
  have he : 2 * Real.pi * (1/4 : ℝ) = Real.pi / 2 := by ring
  rw [he, Real.cos_pi_div_two]
  norm_num

/-- The saturation witness has an explicit value in the physical plane. -/
theorem quarter_point_formula (t : ℝ) :
    point (1/4) t = ((Real.exp t - Real.exp (-t) : ℝ) : ℂ) * Complex.I := by
  have ha : address (1/4) t = (Real.exp t : ℂ) * Complex.I := by
    unfold address
    have he : ((2 * Real.pi * (1/4 : ℝ) : ℝ) : ℂ) = (Real.pi : ℂ)/2 := by
      push_cast
      ring
    rw [he, Complex.exp_add, Complex.exp_pi_div_two_mul_I, ← Complex.ofReal_exp]
  have hi : ((Real.exp t : ℝ) : ℂ)⁻¹ = (Real.exp (-t) : ℂ) := by
    rw [Real.exp_neg, Complex.ofReal_inv]
  unfold point
  rw [ha]
  unfold J
  rw [mul_inv_rev, Complex.inv_I, hi]
  push_cast
  ring

theorem parent_ray_vertices : point (1/6) 0 = 1 ∧ point (1/3) 0 = -1 := by
  constructor
  · rw [point_zero_height]
    have he : 2 * Real.pi * (1/6 : ℝ) = Real.pi / 3 := by ring
    rw [he, Real.cos_pi_div_three]
    norm_num
  · rw [point_zero_height]
    have he : 2 * Real.pi * (1/3 : ℝ) = Real.pi - Real.pi / 3 := by ring
    rw [he, Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num

private theorem point_ne_two {theta t : ℝ}
    (h0 : 0 < theta) (h1 : theta < 1) : point theta t ≠ 2 := by
  intro he
  have hJ : J (address theta t) = J 1 := he.trans (by norm_num [J])
  have ha : address theta t = 1 := by
    rcases (joukowski_fiber (Complex.exp_ne_zero _) one_ne_zero).mp hJ with ha | ha
    · exact ha
    · rw [inv_one] at ha
      exact ha
  have ha' : address theta t = address 0 0 := by simpa [address] using ha
  obtain ⟨_, n, hn⟩ := address_equality ha'
  have hlo : (0 : ℝ) < (n : ℝ) := by linarith
  have hhi : (n : ℝ) < 1 := by linarith
  have hlo' : (0 : ℤ) < n := by exact_mod_cast hlo
  have hhi' : n < (1 : ℤ) := by exact_mod_cast hhi
  omega

/-- The physical map is injective on the complete signed-height
half-turn chart. The reciprocal ambiguity is ruled out by the sum
of the two angles, rather than by a positive-height assumption. -/
theorem point_injective_half_turn {theta phi t s : ℝ}
    (hth0 : 0 < theta) (hth1 : theta < 1/2)
    (hph0 : 0 < phi) (hph1 : phi < 1/2)
    (he : point theta t = point phi s) : theta = phi ∧ t = s := by
  rcases (joukowski_fiber (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)).mp he with
    ha | ha
  · obtain ⟨hts, n, hn⟩ := address_equality ha
    have hnlo : (-1 : ℝ) < (n : ℝ) := by linarith
    have hnhi : (n : ℝ) < 1 := by linarith
    have hnlo' : (-1 : ℤ) < n := by exact_mod_cast hnlo
    have hnhi' : n < (1 : ℤ) := by exact_mod_cast hnhi
    have hn0 : n = 0 := by omega
    exact ⟨by simpa [hn0] using hn, hts⟩
  · have ha' : address theta t = address (-phi) (-s) := by
      rw [address_neg]
      exact ha
    obtain ⟨_, n, hn⟩ := address_equality ha'
    have hnlo : (0 : ℝ) < (n : ℝ) := by linarith
    have hnhi : (n : ℝ) < 1 := by linarith
    have hnlo' : (0 : ℤ) < n := by exact_mod_cast hnlo
    have hnhi' : n < (1 : ℤ) := by exact_mod_cast hnhi
    omega

/-- Membership in a physical puzzle image reflects its exact signed
rectangle, since the projection has no hidden second physical sheet. -/
theorem point_mem_puzzle_iff {a b r theta t : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1/2)
    (hth0 : 0 < theta) (hth1 : theta < 1/2) :
    point theta t ∈ puzzle a b r ↔
      a < theta ∧ theta < b ∧ -r < t ∧ t < r := by
  constructor
  · rintro ⟨phi, s, hp0, hp1, hs0, hs1, he⟩
    obtain ⟨hangle, hheight⟩ := point_injective_half_turn hth0 hth1
      (ha.trans_lt hp0) (hp1.trans_le hb) he.symm
    subst phi
    subst s
    exact ⟨hp0, hp1, hs0, hs1⟩
  · rintro ⟨ha, hb, ht0, ht1⟩
    exact ⟨theta, t, ha, hb, ht0, ht1, rfl⟩

/-- The positive-height angular chart on one full turn is injective.
This is injectivity of actual physical complex points. -/
theorem point_injective_on_turn {theta phi t s : ℝ}
    (hth0 : 0 < theta) (hth1 : theta < 1)
    (hph0 : 0 < phi) (hph1 : phi < 1)
    (ht : 0 < t) (hs : 0 < s)
    (he : point theta t = point phi s) : theta = phi ∧ t = s := by
  have hw : 1 < ‖address theta t‖ := by
    rw [address_norm]; exact Real.one_lt_exp_iff.mpr ht
  have hv : 1 < ‖address phi s‖ := by
    rw [address_norm]; exact Real.one_lt_exp_iff.mpr hs
  have ha := exterior_joukowski_injective hw hv he
  obtain ⟨hts, n, hangle⟩ := address_equality ha
  have hnlo : (-1 : ℝ) < (n : ℝ) := by linarith
  have hnhi : (n : ℝ) < 1 := by linarith
  have hnlo' : (-1 : ℤ) < n := by exact_mod_cast hnlo
  have hnhi' : n < (1 : ℤ) := by exact_mod_cast hnhi
  have hn0 : n = 0 := by omega
  constructor
  · simpa [hn0] using hangle
  · exact hts

/-- The exact second iterate doubles angle and height twice. -/
theorem point_second_iterate (theta t : ℝ) :
    (cquad (-2))^[2] (point theta t) = point (4 * theta) (4 * t) := by
  change (cquad (-2))^[2] (J (address theta t)) = J (address (4 * theta) (4 * t))
  rw [joukowski_iterate (show address theta t ≠ 0 from Complex.exp_ne_zero _)]
  change J ((address theta t)^4) = J (address (4 * theta) (4 * t))
  congr 1
  unfold address
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem point_second_iterate_left (theta t : ℝ) :
    (cquad (-2))^[2] (point theta t) = point (4 * theta - 1) (4 * t) := by
  rw [point_second_iterate]
  have he := point_add_one (4 * theta - 1) (4 * t)
  simpa only [sub_add_cancel] using he

theorem point_second_iterate_right (theta t : ℝ) :
    (cquad (-2))^[2] (point theta t) = point (1 - 4 * theta) (-4 * t) := by
  rw [point_second_iterate]
  simpa only [neg_mul] using (point_one_sub (4 * theta) (4 * t)).symm

/-- The whole physical left branch, including its real spine and both
exterior components, maps bijectively onto the whole parent domain. -/
theorem left_domain_second_iterate_bijOn (h : ℝ) :
    BijOn ((cquad (-2))^[2]) (leftDomain h) (parentDomain h) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro z ⟨theta, t, h0, h1, ht0, hth, rfl⟩
    refine ⟨4 * theta - 1, 4 * t, by linarith, by linarith,
      by linarith, by linarith, ?_⟩
    exact (point_second_iterate_left theta t).symm
  · rintro z ⟨theta, t, h0, h1, ht0, hth, rfl⟩
      w ⟨phi, s, hp0, hp1, hs0, hsh, rfl⟩ he
    rw [point_second_iterate_left, point_second_iterate_left] at he
    obtain ⟨ha, hb⟩ := point_injective_half_turn
      (by linarith : 0 < 4 * theta - 1) (by linarith : 4 * theta - 1 < 1/2)
      (by linarith : 0 < 4 * phi - 1) (by linarith : 4 * phi - 1 < 1/2) he
    have htheta : theta = phi := by linarith
    have htime : t = s := by linarith
    rw [htheta, htime]
  · rintro z ⟨theta, t, h0, h1, ht0, hth, rfl⟩
    refine ⟨point ((theta + 1) / 4) (t / 4), ?_, ?_⟩
    · exact ⟨(theta + 1) / 4, t / 4, by linarith, by linarith,
        by linarith, by linarith, rfl⟩
    · rw [point_second_iterate_left]
      congr 1 <;> ring

/-- The whole physical right branch reverses the signed coordinate
before the second iterate identifies it with the parent domain. -/
theorem right_domain_second_iterate_bijOn (h : ℝ) :
    BijOn ((cquad (-2))^[2]) (rightDomain h) (parentDomain h) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro z ⟨theta, t, h0, h1, ht0, hth, rfl⟩
    refine ⟨1 - 4 * theta, -4 * t, by linarith, by linarith,
      by linarith, by linarith, ?_⟩
    exact (point_second_iterate_right theta t).symm
  · rintro z ⟨theta, t, h0, h1, ht0, hth, rfl⟩
      w ⟨phi, s, hp0, hp1, hs0, hsh, rfl⟩ he
    rw [point_second_iterate_right, point_second_iterate_right] at he
    obtain ⟨ha, hb⟩ := point_injective_half_turn
      (by linarith : 0 < 1 - 4 * theta) (by linarith : 1 - 4 * theta < 1/2)
      (by linarith : 0 < 1 - 4 * phi) (by linarith : 1 - 4 * phi < 1/2) he
    have htheta : theta = phi := by linarith
    have htime : t = s := by linarith
    rw [htheta, htime]
  · rintro z ⟨theta, t, h0, h1, ht0, hth, rfl⟩
    refine ⟨point ((1 - theta) / 4) (-t / 4), ?_, ?_⟩
    · exact ⟨(1 - theta) / 4, -t / 4, by linarith, by linarith,
        by linarith, by linarith, rfl⟩
    · rw [point_second_iterate_right]
      congr 1 <;> ring

theorem branch_domains_subset_parent {h : ℝ} (hh : 0 < h) :
    leftDomain h ⊆ parentDomain h ∧ rightDomain h ⊆ parentDomain h := by
  constructor
  · rintro z ⟨theta, t, ha, hb, ht, hth, rfl⟩
    exact ⟨theta, t, by linarith, hb, by linarith, by linarith, rfl⟩
  · rintro z ⟨theta, t, ha, hb, ht, hth, rfl⟩
    exact ⟨theta, t, ha, by linarith, by linarith, by linarith, rfl⟩

theorem branch_domains_disjoint (h : ℝ) : Disjoint (leftDomain h) (rightDomain h) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨theta, t, ha, hb, _, _, rfl⟩ ⟨phi, s, hc, hd, _, _, he⟩
  obtain ⟨heq, _⟩ := point_injective_half_turn
    (by linarith : 0 < theta) (by linarith : theta < 1/2)
    (by linarith : 0 < phi) (by linarith : phi < 1/2) he.symm
  linarith

/-- The direct-branch saturation defect is outside the entire physical
source domain, not only outside a selected exterior component. -/
theorem quarter_whole_domain_defect {h t : ℝ}
    (hh : 0 < h) (ht : 0 < t) (hth : t < h/8) :
    point (1/4) t ∈ parentDomain h ∧
    point (1/4) t ∉ leftDomain h ∧
    point (1/4) t ∉ rightDomain h := by
  refine ⟨⟨1/4, t, by norm_num, by norm_num, by linarith, by linarith, rfl⟩,
    ?_, ?_⟩
  · rintro ⟨theta, s, ha, hb, _, _, he⟩
    obtain ⟨heq, _⟩ := point_injective_half_turn
      (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (1/4 : ℝ) < 1/2)
      (by linarith : 0 < theta) (by linarith : theta < 1/2) he.symm
    linarith
  · rintro ⟨theta, s, ha, hb, _, _, he⟩
    obtain ⟨heq, _⟩ := point_injective_half_turn
      (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (1/4 : ℝ) < 1/2)
      (by linarith : 0 < theta) (by linarith : theta < 1/2) he.symm
    linarith

/-- The concrete first parent contains the actual critical point; its
second iterate is the fixed endpoint 2, which is outside that domain. -/
theorem critical_exits_whole_parent {h : ℝ} (hh : 0 < h) :
    (0 : ℂ) ∈ parentDomain h ∧
    (cquad (-2))^[2] (0 : ℂ) = 2 ∧
    (2 : ℂ) ∉ parentDomain h := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨1/4, 0, by norm_num, by norm_num, by linarith, by linarith,
      quarter_zero_is_critical⟩
  · norm_num [Function.iterate_succ_apply', cquad]
  · rintro ⟨theta, t, ha, hb, _, _, he⟩
    exact point_ne_two (by linarith) (by linarith) he

/-- The physical left upper exterior component maps bijectively to
the corresponding parent component by the genuine second iterate. -/
theorem left_upper_second_iterate_bijOn (h : ℝ) :
    BijOn ((cquad (-2))^[2]) (sector (7/24) (1/3) (h/8))
      (sector (1/6) (1/3) (h/2)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro z ⟨theta, t, h0, h1, ht0, hth, rfl⟩
    refine ⟨4 * theta - 1, 4 * t, by linarith, by linarith,
      by positivity, by linarith, ?_⟩
    exact (point_second_iterate_left theta t).symm
  · rintro z ⟨theta, t, h0, h1, ht0, hth, rfl⟩
      w ⟨phi, s, hp0, hp1, hs0, hsh, rfl⟩ he
    rw [point_second_iterate_left, point_second_iterate_left] at he
    obtain ⟨ha, hb⟩ := point_injective_on_turn
      (by linarith : 0 < 4 * theta - 1) (by linarith : 4 * theta - 1 < 1)
      (by linarith : 0 < 4 * phi - 1) (by linarith : 4 * phi - 1 < 1)
      (by positivity : 0 < 4 * t) (by positivity : 0 < 4 * s) he
    have htheta : theta = phi := by linarith
    have htime : t = s := by linarith
    rw [htheta, htime]
  · rintro z ⟨theta, t, h0, h1, ht0, hth, rfl⟩
    refine ⟨point ((theta + 1) / 4) (t / 4), ?_, ?_⟩
    · exact ⟨(theta + 1) / 4, t / 4, by linarith, by linarith,
        by positivity, by linarith, rfl⟩
    · rw [point_second_iterate_left]
      congr 1 <;> ring

theorem left_exterior_subset_parent {h : ℝ} (hh : 0 < h) :
    leftExterior h ⊆ parentPiece h := by
  rintro z (⟨theta, t, ha, hb, ht, hth, rfl⟩ |
    ⟨theta, t, ha, hb, ht, hth, rfl⟩)
  · exact Or.inl (Or.inl ⟨theta, t, by linarith, hb, ht, by linarith, rfl⟩)
  · exact Or.inl (Or.inr ⟨theta, t, ha, by linarith, ht, by linarith, rfl⟩)

theorem right_exterior_subset_parent {h : ℝ} (hh : 0 < h) :
    rightExterior h ⊆ parentPiece h := by
  rintro z (⟨theta, t, ha, hb, ht, hth, rfl⟩ |
    ⟨theta, t, ha, hb, ht, hth, rfl⟩)
  · exact Or.inl (Or.inl ⟨theta, t, ha, by linarith, ht, by linarith, rfl⟩)
  · exact Or.inl (Or.inr ⟨theta, t, by linarith, hb, ht, by linarith, rfl⟩)

private theorem quarter_not_sector {a b h t : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (ht : 0 < t)
    (hgap : b ≤ 1/4 ∨ 1/4 ≤ a) :
    point (1/4) t ∉ sector a b h := by
  rintro ⟨theta, s, hth0, hth1, hs0, _, he⟩
  obtain ⟨heq, _⟩ := point_injective_on_turn
    (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (1/4 : ℝ) < 1)
    (ha.trans_lt hth0) (hth1.trans_le hb) ht hs0 he.symm
  rcases hgap with hgap | hgap <;> linarith

/-- An actual physical exterior point enters the parent central
piece while missing both direct-branch exterior pieces. -/
theorem quarter_physical_overlap_defect {h t : ℝ}
    (hh : 0 < h) (ht : 0 < t) (hth : t < h/8) :
    point (1/4) t ∈ parentPiece h ∧
    point (1/4) t ∉ leftExterior h ∧
    point (1/4) t ∉ rightExterior h ∧
    point (1/4) t ∉ realSegment 2 := by
  refine ⟨?_, ?_, ?_, point_exterior _ ht⟩
  · exact Or.inl (Or.inl ⟨1/4, t, by norm_num, by norm_num, ht,
      by linarith, rfl⟩)
  · rintro (hz | hz)
    · exact quarter_not_sector (by norm_num) (by norm_num) ht
        (Or.inr (by norm_num)) hz
    · exact quarter_not_sector (by norm_num) (by norm_num) ht
        (Or.inr (by norm_num)) hz
  · rintro (hz | hz)
    · exact quarter_not_sector (by norm_num) (by norm_num) ht
        (Or.inl (by norm_num)) hz
    · exact quarter_not_sector (by norm_num) (by norm_num) ht
        (Or.inr (by norm_num)) hz

/-- The physical defect survives every positive height truncation. -/
theorem arbitrarily_thin_physical_overlap_defect {h delta : ℝ}
    (hh : 0 < h) (hd : 0 < delta) :
    ∃ t : ℝ, 0 < t ∧ t < delta ∧ t < h/8 ∧
      point (1/4) t ∈ parentPiece h ∧
      point (1/4) t ∉ leftExterior h ∧
      point (1/4) t ∉ rightExterior h ∧
      point (1/4) t ∉ realSegment 2 := by
  let t := min delta (h/8) / 2
  have hm : 0 < min delta (h/8) := lt_min hd (by positivity)
  have ht : 0 < t := by dsimp [t]; positivity
  have htd : t < delta := by
    have := min_le_left delta (h/8)
    dsimp [t]
    linarith
  have hth : t < h/8 := by
    have := min_le_right delta (h/8)
    dsimp [t]
    linarith
  exact ⟨t, ht, htd, hth, quarter_physical_overlap_defect hh ht hth⟩

/-- The critical point belongs to the concrete parent piece, and its
second iterate has already escaped that piece. -/
theorem critical_second_iterate_exits_parent (h : ℝ) :
    (0 : ℂ) ∈ parentPiece h ∧ (cquad (-2))^[2] 0 ∉ parentPiece h := by
  constructor
  · exact Or.inr ⟨0, by norm_num, by norm_num, by simp⟩
  · have he : (cquad (-2))^[2] (0 : ℂ) = 2 := by
      norm_num [Function.iterate_succ_apply', cquad]
    rw [he]
    have hmem : (2 : ℂ) ∈ realSegment 2 := by
      exact ⟨2, by norm_num, rfl⟩
    rintro ((⟨theta, t, _, _, ht, _, heq⟩ |
      ⟨theta, t, _, _, ht, _, heq⟩) | ⟨x, hx0, hx1, heq⟩)
    · exact point_exterior theta ht (heq.symm ▸ hmem)
    · exact point_exterior theta ht (heq.symm ▸ hmem)
    · have hx : x = 2 := by exact_mod_cast heq
      linarith

end

end LoopsChebyshevDecoration
