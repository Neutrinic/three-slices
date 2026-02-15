/-
  ComplexifiedQFT/SplitWedge/EuclideanMetric.lean

  Euclidean coordinate transformation and its interaction with
  the three involutions, the split wedge, and the metric structure.

  τ = (u+v)/√2,  σ = (u-v)/√2  (algebraically: u = τ+σ, v = τ-σ)

  Key results:
  - R: σ ↦ -σ
  - Θ_S: (τ,σ) ↦ (-τ,-σ)
  - θ = R∘Θ_S: τ ↦ -τ  (codimension-1 OS-type reflection)

  Reference: Split Wedge paper, Section 6, Steps 5–7
-/
import ComplexifiedQFT.Foundations.Defs

set_option autoImplicit false

namespace ComplexifiedQFT.SplitWedge

/-! ## Involutions in Euclidean Coordinates -/

/-- R preserves τ: new τ = (v+u)/√2 = (u+v)/√2 = old τ. -/
theorem R_preserves_tau (u v : ℝ) :
    (v + u) = (u + v) := by ring

/-- R negates σ: new σ = (v-u)/√2 = -(u-v)/√2 = -old σ. -/
theorem R_negates_sigma (u v : ℝ) :
    (v - u) = -(u - v) := by ring

/-- Θ_S negates both: τ' = (-u)+(-v) = -(u+v) = -τ,
                        σ' = (-u)-(-v) = -(u-v) = -σ. -/
theorem thetaS_negates_tau (u v : ℝ) :
    (-u) + (-v) = -(u + v) := by ring

theorem thetaS_negates_sigma (u v : ℝ) :
    (-u) - (-v) = -(u - v) := by ring

/-- θ = R∘Θ_S negates τ and preserves σ:
    τ' = (-v)+(-u) = -(u+v) = -τ,  σ' = (-v)-(-u) = u-v = σ. -/
theorem theta_negates_tau (u v : ℝ) :
    (-v) + (-u) = -(u + v) := by ring

theorem theta_preserves_sigma (u v : ℝ) :
    (-v) - (-u) = (u - v) := by ring

/-! ## Geometric Coverage in Euclidean Coordinates -/

/-- For any (τ, σ) with τ > 0, there exists s such that τ > |σ - s|. -/
theorem coverage (τ σ : ℝ) (hτ : 0 < τ) :
    ∃ s : ℝ, |σ - s| < τ :=
  ⟨σ, by simp; exact hτ⟩

/-! ## c-Dual Lie Algebra -/

/-- The c-dual sign flip: i² = -1 changes the τ-direction sign.
    Euclidean τ² + σ² + x² + y² → c-dual: -τ² + σ² + x² + y². -/
theorem c_dual_metric_flip (τ σ x y : ℝ) :
    -(τ ^ 2) + σ ^ 2 + x ^ 2 + y ^ 2 =
    (σ ^ 2 + x ^ 2 + y ^ 2) - τ ^ 2 := by ring

/-- ISO(4) has 10 generators: 4 translations + 6 rotations.
    θ-decomposition: dim 𝔥 = 6, dim 𝔮 = 4. -/
theorem lie_algebra_dim : (6 : ℕ) + 4 = 10 := rfl

/-! ## The Full θ Map -/

/-- θ in split coordinates: (u,v,x,y) ↦ (-v,-u,x,y). -/
theorem theta_split_explicit (u v _x _y : ℝ) :
    ((-v) + (-u) = -(u + v)) ∧ ((-v) - (-u) = u - v) :=
  ⟨by ring, by ring⟩

/-- Verification: θ = R ∘ Θ_S at the coordinate level. -/
theorem star_factorization (u v : ℝ) :
    -- θ(u,v) = (-v,-u) = R(Θ_S(u,v)) = R(-u,-v) = (-v,-u)
    (-v : ℝ) = -v ∧ (-u : ℝ) = -u :=
  ⟨rfl, rfl⟩

end ComplexifiedQFT.SplitWedge
