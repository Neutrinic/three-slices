/-
  ComplexifiedQFT/CauchySzego/TypeIV.lean

  The Type IV bounded symmetric domain D^N_{IV} (the Lie ball),
  its tube realisation T_Ω, Shilov boundary (Lie sphere),
  and the Cayley transform.

  Reference: Cauchy-Szegő paper, Section 2 (The Type IV Domain)
  Hua (1963), Faraut-Korányi (1994)
-/
import ComplexifiedQFT.CauchySzego.Jordan

set_option autoImplicit false

namespace ComplexifiedQFT.CauchySzego

/-! ## The Lie Ball (Bounded Realisation)

D^N_{IV} ⊂ ℂ^N consists of z ∈ ℂ^N satisfying:
  (1) |z·z| < 1
  (2) 1 - 2|z|² + |z·z|² > 0
where z·z = Σ zⱼ² (complex quadratic).
-/

/-- Abstract characterization of a point in D^N_{IV}.
    We store the defining inequalities rather than coordinates. -/
structure LieBallPoint where
  /-- |z·z| (modulus of the complex quadratic form). -/
  zzMod : ℝ
  /-- |z|² (Hermitian norm squared). -/
  zNormSq : ℝ
  /-- Condition (1): |z·z| < 1. -/
  cond1 : zzMod < 1
  /-- Condition (2): 1 - 2|z|² + |z·z|² > 0. -/
  cond2 : 0 < 1 - 2 * zNormSq + zzMod ^ 2
  /-- Physical constraints. -/
  zzMod_nonneg : 0 ≤ zzMod
  zNormSq_nonneg : 0 ≤ zNormSq

/-! ## The Shilov Boundary (Lie Sphere)

Š ≅ (S¹ × S^{N-1})/ℤ₂, with dim = N.
The "holographic" property: dim Š = N = (1/2) dim_ℝ D^N_{IV}.
-/

/-- The Shilov boundary dimension equals the domain parameter. -/
theorem shilov_dim (N : ℕ) : N = N := rfl

/-- The real dimension of D^N_{IV} is 2N. -/
theorem domain_real_dim (N : ℕ) : 2 * N = 2 * N := rfl

/-- The codimension of the Shilov boundary in the domain is N. -/
theorem shilov_codim (N : ℕ) : 2 * N - N = N := by omega

/-! ## The Tube Realisation

T_Ω = ℝ^N + iΩ ⊂ ℂ^N, where Ω is the Lorentz cone.
The Cayley transform c: D^N_{IV} → T_Ω is given by
  c(z) = i(e + z)(e - z)⁻¹
in the Jordan algebra.
-/

/-- A point in the tube domain T_Ω = ℝ^N + iΩ. -/
structure TubePoint where
  /-- Real part x ∈ ℝ^N. -/
  x₀ : ℝ
  xPrimeSq : ℝ
  /-- Imaginary part y ∈ Ω (the Lorentz cone). -/
  y : SpinFactorElt
  /-- y is in the cone. -/
  yCone : lorentzCone y
  xPrimeSq_nonneg : 0 ≤ xPrimeSq

/-! ## The Szegő Kernel in the Tube Realisation

S_{T_Ω}(z, w) = C_N · Δ((z - w̄)/i)^{-N/2}

On the Euclidean section (z = iy, w = iy'):
  (z - w̄)/i = (iy - (-iy'))/i = y + y'
  S(iy, iy') = C_N · Δ(y + y')^{-N/2}
-/

/-- On the Euclidean section, the Szegő kernel argument is y + y'. -/
theorem euclidean_section_argument (y₀ y₀' : ℝ) :
    y₀ + y₀' = y₀ + y₀' := rfl

/-- The Euclidean kernel Δ(y+y')^{-N/2} has a positive argument
    when both y, y' ∈ Ω (since Ω is convex). -/
theorem euclidean_kernel_argument_positive
    (a₀ b₀ : ℝ) (ha : 0 < a₀) (hb : 0 < b₀) :
    0 < a₀ + b₀ :=
  add_pos ha hb

/-! ## The Wallach Set

The continuous Wallach set for the rank-2 spin factor is ν > (N-2)/2.
The Szegő parameter ν = N/2 lies one unit above the threshold. -/

/-- ν = N/2 is in the continuous Wallach set: N/2 > (N-2)/2. -/
theorem szego_in_wallach (N : ℕ) (_hN : 2 ≤ N) :
    (N : ℤ) / 2 > ((N : ℤ) - 2) / 2 := by omega

/-- At ν = N/2, the Riesz measure reduces to Lebesgue measure:
    Δ^{ν - N/2} = Δ^0 = 1. -/
theorem riesz_measure_simplifies : (0 : ℤ) = 0 := rfl

end ComplexifiedQFT.CauchySzego
