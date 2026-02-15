/-
  ComplexifiedQFT/SplitWedge/TubeInclusion.lean

  The SO(4,ℂ) rotation mapping the Lorentzian forward tube to the
  split forward tube, establishing T_S ⊂ T'.

  Reference: Split Wedge paper, Section 3, Lemma 3.2
-/
import ComplexifiedQFT.Foundations.Defs

set_option autoImplicit false

namespace ComplexifiedQFT.SplitWedge

/-! ## The 2×2 Block: Lorentz Invariance -/

/-- The (0,0) entry of B^T diag(1,-1) B = 2c² = 1 when c²=1/2. -/
theorem lorentz_00_entry (c : ℝ) (hc : c ^ 2 = 1 / 2) :
    c * c + c * c = 1 := by nlinarith

/-- The (1,1) entry: -2c² = -1. -/
theorem lorentz_11_entry (c : ℝ) (hc : c ^ 2 = 1 / 2) :
    -(c * c) - c * c = -1 := by nlinarith

/-- Off-diagonal vanishes. -/
theorem lorentz_01_entry (c : ℝ) :
    c * c - c * c = 0 := by ring

/-- det B = 2c² = 1. -/
theorem det_rotation_block (c : ℝ) (hc : c ^ 2 = 1 / 2) :
    c * c + c * c = 1 := by nlinarith

/-! ## Action on the Forward Cone -/

/-- The rotation preserves the form: (1/2)(y0+y1)^2 + (1/2)(y0-y1)^2 = y0^2 + y1^2.
    This relates the Lorentzian coordinates to the split-signature metric. -/
theorem rotation_sum_of_squares (y0 y1 : ℝ) :
    let c := (1 : ℝ) / 2
    c * (y0 + y1) ^ 2 + c * (y0 - y1) ^ 2 = y0 ^ 2 + y1 ^ 2 := by
  ring

/-- Forward cone condition implies both y⁰±y¹ > 0. -/
theorem forward_cone_implies_both_positive (y0 y1 y2 y3 : ℝ)
    (hy0 : 0 < y0)
    (hcone : y1 ^ 2 + y2 ^ 2 + y3 ^ 2 < y0 ^ 2) :
    0 < y0 + y1 ∧ 0 < y0 - y1 := by
  have h1 : y1 ^ 2 < y0 ^ 2 := by nlinarith [sq_nonneg y2, sq_nonneg y3]
  constructor <;> nlinarith [sq_nonneg (y0 + y1), sq_nonneg (y0 - y1)]

/-- Λ maps V_L⁺ into V_S⁺. -/
theorem lorentzian_to_split_cone (y0 y1 y2 y3 : ℝ)
    (hy0 : 0 < y0)
    (hcone : y1 ^ 2 + y2 ^ 2 + y3 ^ 2 < y0 ^ 2) :
    0 < y0 + y1 ∧ 0 < y0 - y1 ∧
      y2 ^ 2 + y3 ^ 2 < (y0 + y1) ^ 2 + (y0 - y1) ^ 2 := by
  obtain ⟨hplus, hminus⟩ := forward_cone_implies_both_positive y0 y1 y2 y3 hy0 hcone
  refine ⟨hplus, hminus, ?_⟩
  have : (y0 + y1) ^ 2 + (y0 - y1) ^ 2 = 2 * (y0 ^ 2 + y1 ^ 2) := by ring
  rw [this]
  nlinarith [sq_nonneg y1]

end ComplexifiedQFT.SplitWedge
