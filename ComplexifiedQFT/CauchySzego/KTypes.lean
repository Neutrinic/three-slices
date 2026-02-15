/-
  ComplexifiedQFT/CauchySzego/KTypes.lean

  K-type lattice for SO₀(2,N), parametrized by (m₁, m₂) ∈ ℤ² with m₁ ≥ m₂.

  Coordinate change:
    k = m₁ + m₂      (O(2)-weight)
    |λ| = m₁ - m₂    (O(N)-depth)

  Inverse:
    m₁ = (k + |λ|) / 2
    m₂ = (k - |λ|) / 2

  Hardy condition (holomorphic discrete series): m₂ ≥ 0, i.e., k ≥ |λ|.

  Reference: Cauchy-Szegő paper, Section 6 and Appendix A
  Schmid (1969), Hecht-Schmid (1983)
-/
import Mathlib.Tactic

set_option autoImplicit false

namespace ComplexifiedQFT.CauchySzego

/-! ## The K-Type Lattice -/

/-- A K-type on the Lie sphere, parametrized by (m₁, m₂) ∈ ℤ²
    with m₁ ≥ m₂ (the dominance condition). -/
structure KType where
  m₁ : ℤ
  m₂ : ℤ
  dominant : m₂ ≤ m₁

namespace KType

/-- The O(2)-weight: k = m₁ + m₂. -/
def k (τ : KType) : ℤ := τ.m₁ + τ.m₂

/-- The O(N)-depth: |λ| = m₁ - m₂ (always ≥ 0 by dominance). -/
def absLambda (τ : KType) : ℤ := τ.m₁ - τ.m₂

/-- |λ| ≥ 0 from dominance. -/
theorem absLambda_nonneg (τ : KType) : 0 ≤ τ.absLambda := by
  unfold absLambda; have := τ.dominant; omega

/-- The coordinate change identities. -/
theorem k_plus_absLambda (τ : KType) : τ.k + τ.absLambda = 2 * τ.m₁ := by
  unfold k absLambda; ring

theorem k_minus_absLambda (τ : KType) : τ.k - τ.absLambda = 2 * τ.m₂ := by
  unfold k absLambda; ring

/-- The inverse coordinate change: m₁ = (k + |λ|) / 2. -/
theorem m1_from_k_lambda (τ : KType) : τ.m₁ = (τ.k + τ.absLambda) / 2 := by
  unfold k absLambda
  omega

/-- The inverse: m₂ = (k - |λ|) / 2. -/
theorem m2_from_k_lambda (τ : KType) : τ.m₂ = (τ.k - τ.absLambda) / 2 := by
  unfold k absLambda
  omega

end KType

/-! ## The Hardy (Holomorphic) Selection Rule -/

/-- A K-type is in the Hardy space H²(Š) iff m₂ ≥ 0.
    Equivalently: k ≥ |λ| (the holomorphic extension condition). -/
def IsHardy (τ : KType) : Prop := 0 ≤ τ.m₂

/-- The Hardy condition in (k, |λ|) coordinates: k ≥ |λ|. -/
theorem hardy_iff_k_ge_lambda (τ : KType) :
    IsHardy τ ↔ τ.absLambda ≤ τ.k := by
  unfold IsHardy KType.k KType.absLambda
  omega

/-- A K-type is in L²(Š) iff m₁ ≥ m₂ (always true by definition). -/
theorem l2_condition (τ : KType) : τ.m₂ ≤ τ.m₁ := τ.dominant

/-! ## Concrete Examples -/

/-- The trivial representation (0, 0) is in the Hardy space. -/
def trivialKType : KType := ⟨0, 0, le_refl 0⟩

theorem trivial_is_hardy : IsHardy trivialKType := le_refl 0

/-- The standard representation (1, 0): k = 1, |λ| = 1, m + |λ| = 2. -/
def standardKType : KType := ⟨1, 0, by omega⟩

theorem standard_is_hardy : IsHardy standardKType := le_refl 0

theorem standard_k : standardKType.k = 1 := by
  simp [KType.k, standardKType]

theorem standard_absLambda : standardKType.absLambda = 1 := by
  simp [KType.absLambda, standardKType]

/-- A non-Hardy K-type: (2, -1). In L²(Š) but not H²(Š). -/
def nonHardyExample : KType := ⟨2, -1, by omega⟩

theorem nonHardy_not_in_hardy : ¬ IsHardy nonHardyExample := by
  unfold IsHardy nonHardyExample; simp

theorem nonHardy_still_delta_even :
    nonHardyExample.k + nonHardyExample.absLambda = 2 * nonHardyExample.m₁ := by
  simp [KType.k, KType.absLambda, nonHardyExample]

end ComplexifiedQFT.CauchySzego
