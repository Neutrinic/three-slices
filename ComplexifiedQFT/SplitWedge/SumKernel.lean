/-
  ComplexifiedQFT/SplitWedge/SumKernel.lean

  The sum-kernel rewrite and semigroup positive-definiteness structure
  underlying the two-point reconstruction theorem.

  Key algebraic fact: Θ_S converts a difference kernel W₂(x - y) into
  a sum kernel in (u, v) variables:
    W₂(Θ_S(ξ) - y) = φ(u_ξ + u_y, v_ξ + v_y, ξ_⊥ - y_⊥)

  This sum-kernel structure on (ℝ₊², +) makes BCR applicable.

  Reference: Split Wedge paper, Section 5, Steps 1–5
-/
import ComplexifiedQFT.Foundations.Defs

set_option autoImplicit false

namespace ComplexifiedQFT.SplitWedge

open SplitPoint

/-! ## The Sum-Kernel Rewrite (Step 1) -/

/-- Θ_S(ξ) - y has u-component -(u_ξ + u_y). -/
theorem sum_kernel_u (ξ y : SplitPoint) :
    (SplitPoint.sub (thetaS ξ) y).u = -(ξ.u + y.u) := by
  simp [SplitPoint.sub, thetaS]; ring

/-- Θ_S(ξ) - y has v-component -(v_ξ + v_y). -/
theorem sum_kernel_v (ξ y : SplitPoint) :
    (SplitPoint.sub (thetaS ξ) y).v = -(ξ.v + y.v) := by
  simp [SplitPoint.sub, thetaS]; ring

/-- Transverse components remain differences. -/
theorem sum_kernel_x (ξ y : SplitPoint) :
    (SplitPoint.sub (thetaS ξ) y).x = ξ.x - y.x := by
  simp [SplitPoint.sub, thetaS]

/-- Full sum-kernel identity:
    Θ_S(ξ) - y = (-(u_ξ+u_y), -(v_ξ+v_y), x_ξ-x_y, y_ξ-y_y). -/
theorem sum_kernel_full (ξ y : SplitPoint) :
    SplitPoint.sub (thetaS ξ) y =
      ⟨-(ξ.u + y.u), -(ξ.v + y.v), ξ.x - y.x, ξ.y - y.y⟩ := by
  simp [SplitPoint.sub, thetaS, SplitPoint.mk.injEq]
  constructor <;> ring

/-! ## Semigroup Structure on (ℝ₊², +) (Step 5) -/

/-- Associativity of pair addition. -/
theorem semigroup_assoc (a₁ b₁ a₂ b₂ a₃ b₃ : ℝ) :
    ((a₁ + a₂) + a₃, (b₁ + b₂) + b₃) =
    (a₁ + (a₂ + a₃), b₁ + (b₂ + b₃)) := by
  ext <;> ring

/-- Commutativity of pair addition. -/
theorem semigroup_comm (a₁ b₁ a₂ b₂ : ℝ) :
    (a₁ + a₂, b₁ + b₂) = (a₂ + a₁, b₂ + b₁) := by
  ext <;> ring

/-- Diagonal condition: the (i,i) argument is 2σᵢ. -/
theorem pd_diagonal (σ τ : ℝ) : σ + σ = 2 * σ ∧ τ + τ = 2 * τ := by
  constructor <;> ring

/-- 2×2 PSD determinant condition. -/
theorem psd_2x2_det (d₁ d₂ o : ℝ) (_ : 0 ≤ d₁) (_ : 0 ≤ d₂)
    (hdet : o ^ 2 ≤ d₁ * d₂) :
    0 ≤ d₁ * d₂ - o ^ 2 := by linarith

/-! ## Semicharacter (Laplace Kernel) Properties -/

/-- Laplace exponent additivity: λ(σ₁+σ₂) + μ(τ₁+τ₂) splits. -/
theorem laplace_additive (lam μ σ₁ τ₁ σ₂ τ₂ : ℝ) :
    lam * (σ₁ + σ₂) + μ * (τ₁ + τ₂) =
    (lam * σ₁ + μ * τ₁) + (lam * σ₂ + μ * τ₂) := by ring

/-- At the origin, the exponent vanishes. -/
theorem laplace_at_origin (lam μ : ℝ) :
    lam * 0 + μ * 0 = 0 := by ring

/-- Non-negativity of the exponent for positive parameters. -/
theorem laplace_exponent_nonneg (lam μ σ τ : ℝ)
    (hlam : 0 ≤ lam) (hμ : 0 ≤ μ) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) :
    0 ≤ lam * σ + μ * τ :=
  add_nonneg (mul_nonneg hlam hσ) (mul_nonneg hμ hτ)

/-! ## The Positive-Definiteness ↔ Sum-Kernel Connection

  The split wedge positivity axiom (S6) states:
    Σᵢⱼ c̄ᵢcⱼ W₂(Θ_S(ξᵢ) - ξⱼ) ≥ 0  for ξᵢ ∈ W⁺.

  By sum_kernel_full, the W₂ argument has the form
    (-(uᵢ+uⱼ), -(vᵢ+vⱼ), xᵢ-xⱼ, yᵢ-yⱼ).

  After partial Fourier transform in (x,y), this becomes
    Σᵢⱼ c̄ᵢcⱼ φ_{p⊥}(uᵢ+uⱼ, vᵢ+vⱼ) ≥ 0

  which is exactly the DEFINITION of φ_{p⊥} being positive-definite
  on the additive semigroup ((0,∞)², +).

  The BCR theorem (axiomatized) then gives the Laplace representation:
    φ_{p⊥}(σ,τ) = ∫ e^{-λσ-μτ} dν_{p⊥}(λ,μ)
-/

/-- The sum-kernel structure converts wedge positivity into
    semigroup positive-definiteness. This is a definition, not a theorem:
    φ is PD on (S,+) iff Σᵢⱼ c̄ᵢcⱼ φ(sᵢ+sⱼ) ≥ 0. -/
def IsSemigroupPD (φ : ℝ → ℝ → ℝ) : Prop :=
  ∀ (m : ℕ) (σs τs : Fin m → ℝ) (cs : Fin m → ℝ),
    (∀ i, 0 < σs i) → (∀ i, 0 < τs i) →
    0 ≤ ∑ i : Fin m, ∑ j : Fin m,
      cs i * cs j * φ (σs i + σs j) (τs i + τs j)

end ComplexifiedQFT.SplitWedge
