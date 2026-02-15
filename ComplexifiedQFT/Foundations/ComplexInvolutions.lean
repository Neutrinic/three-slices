/-
  ComplexifiedQFT/Foundations/ComplexInvolutions.lean

  Formalization of the three antiholomorphic involutions on complexified
  spacetime C^4 whose fixed-point sets are the Lorentzian, Euclidean,
  and split-signature real slices.

  Reference: A. Abrahams, "Split Signature as a Third Axiomatization of QFT"
  Section 2: Geometry of Complexified Spacetime
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace ComplexifiedQFT

/-! ## Complexified Spacetime -/

/-- A point in complexified spacetime C^4 with coordinates (z^0, z^1, z^2, z^3). -/
structure ComplexPoint where
  z0 : ℂ
  z1 : ℂ
  z2 : ℂ
  z3 : ℂ
  deriving Inhabited

namespace ComplexPoint

/-- The complexified Minkowski quadratic form: Q(z) = (z^0)^2 - (z^1)^2 - (z^2)^2 - (z^3)^2. -/
def complexQuadratic (p : ComplexPoint) : ℂ :=
  p.z0 ^ 2 - p.z1 ^ 2 - p.z2 ^ 2 - p.z3 ^ 2

end ComplexPoint

/-! ## The Three Antiholomorphic Involutions -/

/-- The Lorentzian involution sigma_L: z^mu -> conj(z^mu) (componentwise conjugation).
    Fixed set: R^{1,3} with metric (+,-,-,-). -/
def sigmaL (p : ComplexPoint) : ComplexPoint :=
  ⟨starRingEnd ℂ p.z0, starRingEnd ℂ p.z1,
   starRingEnd ℂ p.z2, starRingEnd ℂ p.z3⟩

/-- The Euclidean involution sigma_E: (z^0, z^1, z^2, z^3) -> (-conj(z^0), conj(z^1), conj(z^2), conj(z^3)).
    Fixed set: R^{0,4} with positive-definite metric. -/
def sigmaE (p : ComplexPoint) : ComplexPoint :=
  ⟨-(starRingEnd ℂ p.z0), starRingEnd ℂ p.z1,
   starRingEnd ℂ p.z2, starRingEnd ℂ p.z3⟩

/-- The split involution sigma_S: (z^0, z^1, z^2, z^3) -> (conj(z^0), -conj(z^1), conj(z^2), conj(z^3)).
    Fixed set: R^{2,2} with signature (+,+,-,-). -/
def sigmaS (p : ComplexPoint) : ComplexPoint :=
  ⟨starRingEnd ℂ p.z0, -(starRingEnd ℂ p.z1),
   starRingEnd ℂ p.z2, starRingEnd ℂ p.z3⟩

/-! ### Involution Properties: sigma^2 = id

The key lemma is `star_star`: star(star z) = z for all z : C.
-/

/-- sigma_L is an involution: sigma_L . sigma_L = id. -/
theorem sigmaL_involution (p : ComplexPoint) : sigmaL (sigmaL p) = p := by
  simp [sigmaL]

/-- sigma_E is an involution: sigma_E . sigma_E = id. -/
theorem sigmaE_involution (p : ComplexPoint) : sigmaE (sigmaE p) = p := by
  simp [sigmaE, map_neg, neg_neg]

/-- sigma_S is an involution: sigma_S . sigma_S = id. -/
theorem sigmaS_involution (p : ComplexPoint) : sigmaS (sigmaS p) = p := by
  simp [sigmaS, map_neg, neg_neg]

/-! ### Composition Laws -/

/-- sigma_E . sigma_L implements z^0 -> -z^0 (Wick rotation). -/
theorem sigmaE_comp_sigmaL (p : ComplexPoint) :
    sigmaE (sigmaL p) = ⟨-p.z0, p.z1, p.z2, p.z3⟩ := by
  simp [sigmaE, sigmaL]

/-- sigma_S . sigma_L implements z^1 -> -z^1. -/
theorem sigmaS_comp_sigmaL (p : ComplexPoint) :
    sigmaS (sigmaL p) = ⟨p.z0, -p.z1, p.z2, p.z3⟩ := by
  simp [sigmaS, sigmaL]

/-- sigma_S . sigma_E = sigma_E . sigma_S (the involutions commute). -/
theorem sigmaS_comp_sigmaE (p : ComplexPoint) :
    sigmaS (sigmaE p) = sigmaE (sigmaS p) := by
  simp [sigmaS, sigmaE, map_neg]

/-! ### Fixed-Point Set Characterization

We work directly with re/im components via Complex.ext_iff,
using Complex.conj_re and Complex.conj_im.
-/

private theorem conj_eq_self_iff_im_zero (z : ℂ) :
    starRingEnd ℂ z = z ↔ z.im = 0 := by
  constructor
  · intro h
    have := congr_arg Complex.im h
    simp [Complex.conj_im] at this
    linarith
  · intro h
    apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im, h]

private theorem neg_conj_eq_self_iff_re_zero (z : ℂ) :
    -(starRingEnd ℂ z) = z ↔ z.re = 0 := by
  constructor
  · intro h
    have := congr_arg Complex.re h
    simp [Complex.neg_re, Complex.conj_re] at this
    linarith
  · intro h
    apply Complex.ext <;> simp [Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im, h]

/-- sigma_L(z) = z iff all components are real:
    conj(z_j) = z_j iff z_j.im = 0. -/
theorem sigmaL_fixed_iff (p : ComplexPoint) :
    sigmaL p = p ↔ (p.z0.im = 0 ∧ p.z1.im = 0 ∧ p.z2.im = 0 ∧ p.z3.im = 0) := by
  constructor
  · intro h
    have h0 := congr_arg ComplexPoint.z0 h
    have h1 := congr_arg ComplexPoint.z1 h
    have h2 := congr_arg ComplexPoint.z2 h
    have h3 := congr_arg ComplexPoint.z3 h
    simp [sigmaL] at h0 h1 h2 h3
    exact ⟨(conj_eq_self_iff_im_zero _).mp h0,
           (conj_eq_self_iff_im_zero _).mp h1,
           (conj_eq_self_iff_im_zero _).mp h2,
           (conj_eq_self_iff_im_zero _).mp h3⟩
  · intro ⟨h0, h1, h2, h3⟩
    simp [sigmaL, (conj_eq_self_iff_im_zero _).mpr h0,
          (conj_eq_self_iff_im_zero _).mpr h1,
          (conj_eq_self_iff_im_zero _).mpr h2,
          (conj_eq_self_iff_im_zero _).mpr h3]

/-- sigma_E(z) = z iff z^0 is purely imaginary and z^1,z^2,z^3 are real. -/
theorem sigmaE_fixed_iff (p : ComplexPoint) :
    sigmaE p = p ↔ (p.z0.re = 0 ∧ p.z1.im = 0 ∧ p.z2.im = 0 ∧ p.z3.im = 0) := by
  constructor
  · intro h
    have h0 := congr_arg ComplexPoint.z0 h
    have h1 := congr_arg ComplexPoint.z1 h
    have h2 := congr_arg ComplexPoint.z2 h
    have h3 := congr_arg ComplexPoint.z3 h
    simp [sigmaE] at h0 h1 h2 h3
    exact ⟨(neg_conj_eq_self_iff_re_zero _).mp h0,
           (conj_eq_self_iff_im_zero _).mp h1,
           (conj_eq_self_iff_im_zero _).mp h2,
           (conj_eq_self_iff_im_zero _).mp h3⟩
  · intro ⟨h0, h1, h2, h3⟩
    simp [sigmaE, (neg_conj_eq_self_iff_re_zero _).mpr h0,
          (conj_eq_self_iff_im_zero _).mpr h1,
          (conj_eq_self_iff_im_zero _).mpr h2,
          (conj_eq_self_iff_im_zero _).mpr h3]

/-- sigma_S(z) = z iff z^0,z^2,z^3 are real and z^1 is purely imaginary. -/
theorem sigmaS_fixed_iff (p : ComplexPoint) :
    sigmaS p = p ↔ (p.z0.im = 0 ∧ p.z1.re = 0 ∧ p.z2.im = 0 ∧ p.z3.im = 0) := by
  constructor
  · intro h
    have h0 := congr_arg ComplexPoint.z0 h
    have h1 := congr_arg ComplexPoint.z1 h
    have h2 := congr_arg ComplexPoint.z2 h
    have h3 := congr_arg ComplexPoint.z3 h
    simp [sigmaS] at h0 h1 h2 h3
    exact ⟨(conj_eq_self_iff_im_zero _).mp h0,
           (neg_conj_eq_self_iff_re_zero _).mp h1,
           (conj_eq_self_iff_im_zero _).mp h2,
           (conj_eq_self_iff_im_zero _).mp h3⟩
  · intro ⟨h0, h1, h2, h3⟩
    simp [sigmaS, (conj_eq_self_iff_im_zero _).mpr h0,
          (neg_conj_eq_self_iff_re_zero _).mpr h1,
          (conj_eq_self_iff_im_zero _).mpr h2,
          (conj_eq_self_iff_im_zero _).mpr h3]

/-! ### Signature Verification

When restricted to fixed sets, the complex quadratic form Q(z)
reduces to the appropriate real signature.
-/

/-- On the fixed set of sigma_L, Q restricts to Lorentzian signature:
    Q(t, x_1, x_2, x_3) = t^2 - x_1^2 - x_2^2 - x_3^2. -/
theorem lorentzian_signature_from_quadratic (t x₁ x₂ x₃ : ℝ) :
    (ComplexPoint.complexQuadratic ⟨↑t, ↑x₁, ↑x₂, ↑x₃⟩) =
      ↑(t ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2) := by
  simp only [ComplexPoint.complexQuadratic]
  push_cast
  ring

/-- On the fixed set of sigma_S, Q restricts to split signature:
    Q(u, iv, x, y) = u^2 + v^2 - x^2 - y^2.
    Key: (iv)^2 = i^2*v^2 = -v^2, so -(iv)^2 = v^2. -/
theorem split_signature_from_quadratic (u v x y : ℝ) :
    (ComplexPoint.complexQuadratic ⟨↑u, ↑v * Complex.I, ↑x, ↑y⟩) =
      ↑(u ^ 2 + v ^ 2 - x ^ 2 - y ^ 2) := by
  simp only [ComplexPoint.complexQuadratic]
  have hI2 : Complex.I ^ 2 = -1 := by
    rw [sq]; exact Complex.I_mul_I
  rw [mul_pow, hI2]
  push_cast
  ring

/-- On the fixed set of sigma_E, Q restricts to Euclidean (negative-definite) signature:
    Q(i*tau, x_1, x_2, x_3) = -(tau^2 + x_1^2 + x_2^2 + x_3^2). -/
theorem euclidean_signature_from_quadratic (τ x₁ x₂ x₃ : ℝ) :
    (ComplexPoint.complexQuadratic ⟨↑τ * Complex.I, ↑x₁, ↑x₂, ↑x₃⟩) =
      ↑(-(τ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) := by
  simp only [ComplexPoint.complexQuadratic]
  have hI2 : Complex.I ^ 2 = -1 := by
    rw [sq]; exact Complex.I_mul_I
  rw [mul_pow, hI2]
  push_cast
  ring

end ComplexifiedQFT
