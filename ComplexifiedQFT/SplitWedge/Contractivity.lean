/-
  ComplexifiedQFT/SplitWedge/Contractivity.lean

  The contraction semigroup structure in split signature.
  Key identity: Θ_S(ξ+a) - (η+a) = Θ_S(ξ) - η - 2a,
  where the 2a shift provides the damping factor e^{-2ip·a}.

  Reference: Split Wedge paper, Section 6, Step 3 (Lemma 6.3)
-/
import ComplexifiedQFT.Foundations.Defs

set_option autoImplicit false

namespace ComplexifiedQFT.SplitWedge

open SplitPoint

/-! ## Damping Factor Analysis -/

/-- The split inner product of forward-cone vectors is positive:
    p_u·a_u + p_v·a_v > 0 when all components are positive. -/
theorem damping_positive (p_u p_v a_u a_v : ℝ)
    (hpu : 0 < p_u) (hpv : 0 < p_v) (hau : 0 < a_u) (hav : 0 < a_v) :
    0 < p_u * a_u + p_v * a_v :=
  add_pos (mul_pos hpu hau) (mul_pos hpv hav)

/-- Tube regularization: ε · (p·y) > 0 for ε > 0 and p·y > 0. -/
theorem tube_damping_positive (ε p_y : ℝ) (hε : 0 < ε) (hpy : 0 < p_y) :
    0 < ε * p_y :=
  mul_pos hε hpy

/-! ## The Contractivity Inequality -/

/-- Multiplying by a bounded factor doesn't increase absolute value. -/
theorem contractivity_bound (c w : ℝ) (hc : |c| ≤ 1) (hw : 0 ≤ w) :
    |c * w| ≤ w := by
  rw [abs_mul]
  calc |c| * |w| ≤ 1 * |w| := mul_le_mul_of_nonneg_right hc (abs_nonneg w)
    _ = |w| := one_mul _
    _ = w := abs_of_nonneg hw

/-! ## Semigroup Composition -/

/-- Timelike translations compose: T(a) ∘ T(b) = T(a+b). -/
theorem semigroup_composition (a_u a_v b_u b_v : ℝ) :
    SplitPoint.add (SplitPoint.timelike a_u a_v) (SplitPoint.timelike b_u b_v) =
    SplitPoint.timelike (a_u + b_u) (a_v + b_v) := by
  simp [SplitPoint.add, SplitPoint.timelike]

/-- The identity translation. -/
theorem semigroup_identity : SplitPoint.timelike 0 0 = SplitPoint.zero := rfl

/-- For timelike translations, the 2a shift only affects (u,v). -/
theorem timelike_double_shift (a_u a_v : ℝ) :
    SplitPoint.scale 2 (SplitPoint.timelike a_u a_v) =
    SplitPoint.timelike (2 * a_u) (2 * a_v) := by
  simp [SplitPoint.scale, SplitPoint.timelike]

end ComplexifiedQFT.SplitWedge
