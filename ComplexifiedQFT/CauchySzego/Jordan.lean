/-
  ComplexifiedQFT/CauchySzego/Jordan.lean

  The spin factor Jordan algebra V_N = ℝ × ℝ^{N-1} and its
  associated structures: Jordan product, Jordan determinant
  (= Lorentzian quadratic form), and the Lorentz cone Ω.

  Reference: Cauchy-Szegő paper, Section 2.2 (The Tube Realisation)
  Faraut-Korányi (1994), Analysis on Symmetric Cones
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace ComplexifiedQFT.CauchySzego

/-! ## The Spin Factor Jordan Algebra

The spin factor of rank N has underlying space ℝ × ℝ^{N-1}.
For the formalization we work with a concrete element u = (u₀, u').
-/

/-- An element of the spin factor Jordan algebra V_N,
    written as (u₀, u₁, ..., u_{N-1}) but stored as u₀ and ‖u'‖². -/
structure SpinFactorElt where
  u₀ : ℝ
  /-- The squared norm of the transverse part: ‖u'‖² = u₁² + ... + u_{N-1}². -/
  uPrimeSq : ℝ
  uPrimeSq_nonneg : 0 ≤ uPrimeSq

namespace SpinFactorElt

/-- The Jordan determinant: Δ(u) = u₀² - ‖u'‖². -/
def det (u : SpinFactorElt) : ℝ :=
  u.u₀ ^ 2 - u.uPrimeSq

/-- The spectral values λ₁ = u₀ + ‖u'‖, λ₂ = u₀ - ‖u'‖. -/
noncomputable def spectralValue₁ (u : SpinFactorElt) : ℝ :=
  u.u₀ + Real.sqrt u.uPrimeSq

noncomputable def spectralValue₂ (u : SpinFactorElt) : ℝ :=
  u.u₀ - Real.sqrt u.uPrimeSq

/-- The determinant equals the product of spectral values. -/
theorem det_eq_spectral_product (u : SpinFactorElt) :
    u.det = u.spectralValue₁ * u.spectralValue₂ := by
  unfold det spectralValue₁ spectralValue₂
  have hsq : Real.sqrt u.uPrimeSq * Real.sqrt u.uPrimeSq = u.uPrimeSq :=
    Real.mul_self_sqrt u.uPrimeSq_nonneg
  nlinarith [hsq]

end SpinFactorElt

/-! ## The Lorentz Cone -/

/-- The Lorentz cone Ω = {y : y₀ > ‖y'‖}, equivalently
    {y : both spectral values positive}. -/
def lorentzCone (u : SpinFactorElt) : Prop :=
  0 < u.u₀ ∧ u.uPrimeSq < u.u₀ ^ 2

/-- In the Lorentz cone, the determinant is positive. -/
theorem det_pos_of_cone (u : SpinFactorElt) (h : lorentzCone u) :
    0 < u.det := by
  unfold SpinFactorElt.det lorentzCone at *
  linarith [h.2]

/-- The Lorentz cone is convex: if y, y' ∈ Ω then y + y' ∈ Ω
    (at the level of determinants). -/
theorem cone_sum_det_pos (a₀ b₀ aSq bSq : ℝ)
    (ha0 : 0 < a₀) (hb0 : 0 < b₀)
    (_haSq : 0 ≤ aSq) (hbSq : 0 ≤ bSq)
    (hacone : aSq < a₀ ^ 2) (hbcone : bSq < b₀ ^ 2) :
    aSq + bSq + 2 * Real.sqrt (aSq * bSq) < (a₀ + b₀) ^ 2 := by
  have h1 : Real.sqrt (aSq * bSq) ≤ Real.sqrt (a₀ ^ 2 * b₀ ^ 2) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul (le_of_lt hacone) (le_of_lt hbcone) hbSq (by positivity)
  have h2 : Real.sqrt (a₀ ^ 2 * b₀ ^ 2) = a₀ * b₀ := by
    rw [show a₀ ^ 2 * b₀ ^ 2 = (a₀ * b₀) ^ 2 from by ring]
    exact Real.sqrt_sq (by positivity : 0 ≤ a₀ * b₀)
  nlinarith

/-! ## Domain Parameters -/

/-- For d-dimensional spacetime, the Type IV domain parameter is N = 2d-2. -/
def domainParam (d : ℕ) : ℕ := 2 * d - 2

/-- The rank of the Type IV domain is always 2. -/
def typeIV_rank : ℕ := 2

/-- The Peirce constant: a = N - 2. -/
def peirceConst (N : ℕ) : ℤ := (N : ℤ) - 2

/-- The genus: g = N (for Type IV). -/
def genus (N : ℕ) : ℕ := N

/-- The Szegő parameter: ν = N/2 (always in the continuous Wallach set). -/
noncomputable def szegoParam (N : ℕ) : ℚ := (N : ℚ) / 2

/-- The Szegő parameter is above the Wallach threshold:
    N/2 > (N-2)/2 for all N ≥ 1. -/
theorem szego_above_wallach (N : ℕ) (_hN : 1 ≤ N) :
    (N : ℤ) - 2 < N := by omega

end ComplexifiedQFT.CauchySzego
