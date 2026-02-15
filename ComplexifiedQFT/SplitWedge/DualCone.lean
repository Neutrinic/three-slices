/-
  ComplexifiedQFT/SplitWedge/DualCone.lean

  Dual cone structure for split-signature spacetime.
  Key result: V_S⁺ is NOT self-dual (unlike the Lorentz cone).

  Reference: Split Wedge paper, eq. (2); Bridge paper, Lines 729-739
-/
import ComplexifiedQFT.Foundations.Defs

set_option autoImplicit false

namespace ComplexifiedQFT.SplitWedge

open SplitPoint

/-! ## Dual Cone ⊂ Forward Cone -/

theorem dualCone_subset_forwardConeClosed (p : SplitPoint)
    (hp : splitDualCone p) : splitForwardConeClosed p := by
  obtain ⟨hu, hv, htrans⟩ := hp
  refine ⟨hu, hv, ?_⟩
  have hmin_sq : min p.u p.v ^ 2 ≤ p.u ^ 2 + p.v ^ 2 := by
    rcases le_total p.u p.v with h | h
    · simp [min_eq_left h]; nlinarith [sq_nonneg p.v]
    · simp [min_eq_right h]; nlinarith [sq_nonneg p.u]
  linarith

/-! ## Non-Empty Dual Cone -/

theorem dualCone_nonempty : splitDualCone ⟨1, 1, 0, 0⟩ := by
  simp [splitDualCone, transNormSq, min_self]

theorem dualCone_diagonal (a : ℝ) (ha : 0 < a) :
    splitDualCone ⟨a, a, 0, 0⟩ := by
  refine ⟨le_of_lt ha, le_of_lt ha, ?_⟩
  simp [transNormSq, min_self]; positivity

/-! ## Inner Product Positivity -/

theorem splitInner_nonneg_diagonal (a : ℝ) (ha : 0 < a) (y : SplitPoint)
    (hy : splitDualCone y) :
    0 ≤ splitInner ⟨a, a, 0, 0⟩ y := by
  obtain ⟨hyu, hyv, hytrans⟩ := hy
  simp [splitInner, transNormSq] at *
  nlinarith [min_le_left y.u y.v, min_le_right y.u y.v,
             sq_nonneg y.x, sq_nonneg y.y]

/-! ## Non-Self-Duality: V_S⁺ ≠ (V_S⁺)* -/

theorem counterexample_p_in_cone : splitForwardCone ⟨10, 1, 7, 0⟩ := by
  refine ⟨by norm_num, by norm_num, ?_⟩; simp [transNormSq]; norm_num

theorem counterexample_y_in_cone : splitForwardCone ⟨1, 10, 7, 0⟩ := by
  refine ⟨by norm_num, by norm_num, ?_⟩; simp [transNormSq]; norm_num

theorem counterexample_negative_inner :
    splitInner ⟨10, 1, 7, 0⟩ ⟨1, 10, 7, 0⟩ = -29 := by
  simp [splitInner]; norm_num

/-- V_S⁺ is not self-dual: ∃ p y ∈ V_S⁺ with g_S(p,y) < 0. -/
theorem splitForwardCone_not_self_dual :
    ∃ p y : SplitPoint, splitForwardCone p ∧ splitForwardCone y ∧
      splitInner p y < 0 :=
  ⟨⟨10, 1, 7, 0⟩, ⟨1, 10, 7, 0⟩,
    counterexample_p_in_cone, counterexample_y_in_cone,
    by rw [counterexample_negative_inner]; norm_num⟩

theorem dualCone_strictly_smaller :
    ∃ p : SplitPoint, splitForwardCone p ∧ ¬ splitDualCone p :=
  ⟨⟨10, 1, 5, 0⟩,
    ⟨by norm_num, by norm_num, by simp [transNormSq]; norm_num⟩,
    by simp [splitDualCone, transNormSq]⟩

/-! ## Cauchy-Schwarz in ℝ² -/

theorem cauchy_schwarz_R2 (a₁ a₂ b₁ b₂ : ℝ) :
    (a₁ * b₁ + a₂ * b₂) ^ 2 ≤ (a₁ ^ 2 + a₂ ^ 2) * (b₁ ^ 2 + b₂ ^ 2) := by
  nlinarith [sq_nonneg (a₁ * b₂ - a₂ * b₁)]

end ComplexifiedQFT.SplitWedge
