/-
  ComplexifiedQFT/SplitWedge/Bridge.lean

  The Bridge Lemma: R-invariance + Θ_S-positivity ⟹ θ_E-positivity.
  The algebraic core is θ_E = R ∘ Θ_S, so
    ω(F^{*_{θ_E}} · F) = ω((R⁻¹F)^{*_{Θ_S}} · R⁻¹F) ≥ 0.

  Ported from bridge-lean4 project to unified namespace.

  Reference: A. Abrahams, "Split Signature as a Third Axiomatization of QFT"
  Section 6, Lemma 6.6 (Bridge Lemma)
-/
import ComplexifiedQFT.Foundations.Defs

set_option autoImplicit false

namespace ComplexifiedQFT.SplitWedge

/-! ## The Bridge Lemma: Core Identities -/

/-- The factorization identity: θ_E(p) = R(Θ_S(p)). -/
theorem bridge_factorization (p : SplitPoint) :
    thetaE p = swapR (thetaS p) := rfl

/-- The Bridge conjugation: θ_E(R(p)) = Θ_S(p). -/
theorem bridge_conjugation (p : SplitPoint) :
    thetaE (swapR p) = thetaS p := by
  simp [thetaE, swapR, thetaS]

/-- Converse: Θ_S(R(p)) = θ_E(p). -/
theorem bridge_conjugation_converse (p : SplitPoint) :
    thetaS (swapR p) = thetaE p := by
  simp [thetaS, swapR, thetaE]

/-! ## The Shift Identity -/

/-- Θ_S(ξ + a) = Θ_S(ξ) - a for timelike translations (a.x = a.y = 0). -/
theorem thetaS_shift (ξ : SplitPoint) (a_u a_v : ℝ) :
    thetaS (SplitPoint.add ξ (SplitPoint.timelike a_u a_v)) =
    SplitPoint.sub (thetaS ξ) (SplitPoint.timelike a_u a_v) := by
  simp only [thetaS, SplitPoint.add, SplitPoint.sub, SplitPoint.timelike]
  ring_nf

/-- Θ_S(x - a) = Θ_S(x) + a for timelike translations. -/
theorem thetaS_sub_reversal (x : SplitPoint) (a_u a_v : ℝ) :
    thetaS (SplitPoint.sub x (SplitPoint.timelike a_u a_v)) =
    SplitPoint.add (thetaS x) (SplitPoint.timelike a_u a_v) := by
  simp only [thetaS, SplitPoint.sub, SplitPoint.add, SplitPoint.timelike]
  ring_nf

/-- The translated kernel identity for timelike translations:
    Θ_S(ξ'+a) - (η'+a) = Θ_S(ξ') - η' - 2a. -/
theorem translated_kernel (ξ' η' : SplitPoint) (a_u a_v : ℝ) :
    SplitPoint.sub (thetaS (SplitPoint.add ξ' (SplitPoint.timelike a_u a_v)))
                   (SplitPoint.add η' (SplitPoint.timelike a_u a_v)) =
    SplitPoint.sub (SplitPoint.sub (thetaS ξ') η')
                   (SplitPoint.scale 2 (SplitPoint.timelike a_u a_v)) := by
  simp only [thetaS, SplitPoint.add, SplitPoint.sub, SplitPoint.scale, SplitPoint.timelike]
  ring_nf

/-! ## Wedge Mapping Properties -/

/-- The wedge condition is preserved by σ-translation.
    For any (u, v) with u + v > 0, there exists s with u + s > 0 ∧ v - s > 0. -/
theorem wedge_from_halfspace (u v : ℝ) (h : 0 < u + v) :
    ∃ s : ℝ, 0 < u + s ∧ 0 < v - s := by
  use (v - u) / 2; constructor <;> nlinarith

/-! ## The Bridge Lemma Statement

The Bridge Lemma in the context of a SplitQFT:
If the theory satisfies (S3) R-invariance and (S6) wedge positivity,
then it satisfies θ_E-positivity on the Euclidean half-space.

The proof structure:
1. For F supported in W⁺, define G = R⁻¹F (supported in W⁺ by R-stability).
2. ω(F^{*_{θ_E}} · F) = ω(F^{*_{R∘Θ_S}} · F)
3. By R-invariance: = ω((R⁻¹F)^{*_{Θ_S}} · R⁻¹F) = ω(G^{*_{Θ_S}} · G)
4. By wedge positivity: ≥ 0.
5. Extend from wedge to E⁺ by σ-translations (geometric coverage).
-/

/-- The Bridge Lemma: algebraic core identity.
    For any point p in the wedge, the θ_E-reflected pair factors
    through R and Θ_S. -/
theorem bridge_lemma_identity (p q : SplitPoint) :
    let pair_theta := (thetaE p, q)
    let pair_bridge := (swapR (thetaS p), q)
    pair_theta = pair_bridge := by
  simp [thetaE]

end ComplexifiedQFT.SplitWedge
