/-
  ComplexifiedQFT/CauchySzego/DeltaEvenness.lean

  THE central theorem of the Cauchy-Szegő paper:

    For all K-types (m₁, m₂) ∈ ℤ² on the Lie sphere:
      k + |λ| = (m₁ + m₂) + (m₁ - m₂) = 2m₁

    Therefore (-1)^{k + |λ|} = (-1)^{2m₁} = +1 for every K-type.

  This is a one-line arithmetic proof. It implies that no δ-odd
  K-types exist in L²(Š), a fortiori none in H²(Š).

  Reference: Cauchy-Szegő paper, Theorem 7.2 and Appendix A.3
-/
import ComplexifiedQFT.CauchySzego.KTypes

set_option autoImplicit false

namespace ComplexifiedQFT.CauchySzego

open KType

/-! ## The δ-Evenness Theorem -/

/-- **Theorem 7.2 (δ-Evenness).**
    For every K-type on the Lie sphere: k + |λ| = 2m₁.

    This is the paper's central result. The proof is arithmetic:
    k + |λ| = (m₁ + m₂) + (m₁ - m₂) = 2m₁. -/
theorem delta_evenness (τ : KType) : τ.k + τ.absLambda = 2 * τ.m₁ := by
  unfold KType.k KType.absLambda; ring

/-- Corollary: k + |λ| is always even. -/
theorem k_plus_lambda_even (τ : KType) : Even (τ.k + τ.absLambda) := by
  rw [delta_evenness]
  exact ⟨τ.m₁, by ring⟩

/-- The δ-eigenvalue is always +1: (-1)^{k+|λ|} = (-1)^{2m₁} = 1. -/
theorem delta_eigenvalue_positive (τ : KType) :
    (-1 : ℤ) ^ (τ.k + τ.absLambda).toNat = 1 := by
  rw [delta_evenness]
  rcases le_or_gt 0 τ.m₁ with hm | hm
  · -- m₁ ≥ 0: toNat (2*m₁) = 2 * m₁.toNat
    have h2 : (2 * τ.m₁).toNat = 2 * τ.m₁.toNat := by omega
    rw [h2, pow_mul]; norm_num
  · -- m₁ < 0: toNat (2*m₁) = 0
    have h2 : (2 * τ.m₁).toNat = 0 := by omega
    rw [h2]; norm_num

/-- **No δ-odd K-types exist on the Lie sphere.**
    This holds in all of L²(Š), not just H²(Š). -/
theorem no_delta_odd_Ktypes (τ : KType) :
    ¬ Odd (τ.k + τ.absLambda) := by
  intro ⟨n, hn⟩
  have := delta_evenness τ
  omega

/-- The Hardy condition m₂ ≥ 0 is NOT needed for δ-evenness.
    Even non-Hardy K-types are δ-even. -/
theorem delta_even_without_hardy (m₁ m₂ : ℤ) (_ : m₂ ≤ m₁) :
    Even ((m₁ + m₂) + (m₁ - m₂)) := by
  have : (m₁ + m₂) + (m₁ - m₂) = 2 * m₁ := by ring
  rw [this]; exact ⟨m₁, by ring⟩

/-- δ-odd K-types would require half-integer m₁, which is impossible. -/
theorem half_integer_impossible (τ : KType) :
    ¬ ∃ n : ℤ, τ.k + τ.absLambda = 2 * n + 1 := by
  intro ⟨n, hn⟩
  have := delta_evenness τ
  omega

/-! ## The d = 4 (N = 6) Verification -/

/-- For d = 4: the trivial K-type (0,0). k + |λ| = 0 (even). -/
example : (trivialKType.k + trivialKType.absLambda) = 0 := by
  simp [KType.k, KType.absLambda, trivialKType]

/-- For d = 4: the standard K-type (1,0). k + |λ| = 1 + 1 = 2 (even). -/
example : (standardKType.k + standardKType.absLambda) = 2 := by
  simp [KType.k, KType.absLambda, standardKType]

/-- The (2,0) K-type: k + |λ| = 2 + 2 = 4 (even). -/
example : let τ : KType := ⟨2, 0, by omega⟩
    τ.k + τ.absLambda = 4 := by
  simp [KType.k, KType.absLambda]

/-- The (2,1) K-type: k + |λ| = 3 + 1 = 4 (even). -/
example : let τ : KType := ⟨2, 1, by omega⟩
    τ.k + τ.absLambda = 4 := by
  simp [KType.k, KType.absLambda]

/-- The (3,2) K-type: k + |λ| = 5 + 1 = 6 (even). -/
example : let τ : KType := ⟨3, 2, by omega⟩
    τ.k + τ.absLambda = 6 := by
  simp [KType.k, KType.absLambda]

/-! ## Appendix A.4: The N = 10 (d = 6) Non-Hardy Example -/

/-- The K-type (2, -1): in L²(Š) but not H²(Š).
    k = 1, |λ| = 3, k + |λ| = 4 = 2·2 (even).
    δ-even despite being non-Hardy. -/
example : let τ : KType := ⟨2, -1, by omega⟩
    τ.k + τ.absLambda = 4 ∧ ¬ IsHardy τ := by
  constructor
  · simp [KType.k, KType.absLambda]
  · unfold IsHardy; simp

/-! ## The Punchline -/

/-- **The δ-odd obstruction from the Bridge paper does not arise
    from the scalar K-type lattice.**

    For ANY K-type (m₁, m₂) ∈ ℤ² with m₁ ≥ m₂:
    - k + |λ| = 2m₁ (even)
    - (-1)^{k+|λ|} = +1
    - The scalar δ-eigenvalue is always +1

    The obstruction lives entirely in the fiber representation
    (the intertwiner J_τ), resolved for bosonic fields by J_τ = +id. -/
theorem scalar_lattice_uniformly_delta_even :
    ∀ (m₁ m₂ : ℤ), m₂ ≤ m₁ →
      Even ((m₁ + m₂) + (m₁ - m₂)) := by
  intro m₁ m₂ _
  have : (m₁ + m₂) + (m₁ - m₂) = 2 * m₁ := by ring
  rw [this]; exact ⟨m₁, by ring⟩

end ComplexifiedQFT.CauchySzego
