/-
  ComplexifiedQFT/Foundations/Defs.lean

  Core definitions shared across the trilogy formalization.
  Split-signature spacetime ℝ^{2,2}, forward cones, wedge,
  the three involutions Θ_S, R, θ_E, and their algebraic properties.

  This absorbs and unifies definitions from the bridge project.

  Reference: A. Abrahams, "Split Signature as a Third Axiomatization of QFT"
  Sections 2, 4, 6; and "The Bridge" Sections 3–5.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace ComplexifiedQFT

/-! ## Split-Signature Spacetime -/

/-- A point in split-signature spacetime ℝ^{2,2} with coordinates (u, v, x, y).
    u, v are the two timelike directions; x, y are spacelike.
    The metric is ds² = du² + dv² - dx² - dy². -/
structure SplitPoint where
  u : ℝ
  v : ℝ
  x : ℝ
  y : ℝ
  deriving Inhabited

namespace SplitPoint

/-- The zero point. -/
def zero : SplitPoint := ⟨0, 0, 0, 0⟩

/-- Pointwise addition. -/
def add (p q : SplitPoint) : SplitPoint :=
  ⟨p.u + q.u, p.v + q.v, p.x + q.x, p.y + q.y⟩

/-- Pointwise subtraction. -/
def sub (p q : SplitPoint) : SplitPoint :=
  ⟨p.u - q.u, p.v - q.v, p.x - q.x, p.y - q.y⟩

/-- Negation. -/
def neg (p : SplitPoint) : SplitPoint :=
  ⟨-p.u, -p.v, -p.x, -p.y⟩

/-- Scalar multiplication. -/
def scale (c : ℝ) (p : SplitPoint) : SplitPoint :=
  ⟨c * p.u, c * p.v, c * p.x, c * p.y⟩

/-- A purely timelike translation (x = y = 0). -/
def timelike (a_u a_v : ℝ) : SplitPoint := ⟨a_u, a_v, 0, 0⟩

/-- The split-signature bilinear form: g_S(p,q) = p_u q_u + p_v q_v - p_x q_x - p_y q_y. -/
def splitInner (p q : SplitPoint) : ℝ :=
  p.u * q.u + p.v * q.v - p.x * q.x - p.y * q.y

/-- The split-signature quadratic form: Q_S(p) = u² + v² - x² - y². -/
def splitNormSq (p : SplitPoint) : ℝ :=
  p.u ^ 2 + p.v ^ 2 - p.x ^ 2 - p.y ^ 2

/-- The transverse norm squared: |p_⊥|² = x² + y². -/
def transNormSq (p : SplitPoint) : ℝ :=
  p.x ^ 2 + p.y ^ 2

theorem splitInner_self (p : SplitPoint) :
    splitInner p p = splitNormSq p := by
  simp [splitInner, splitNormSq, sq]

theorem splitInner_comm (p q : SplitPoint) :
    splitInner p q = splitInner q p := by
  unfold splitInner; ring

end SplitPoint

/-! ## The Three Involutions -/

/-- The split wedge reflection Θ_S: (u, v, x, y) ↦ (-u, -v, x, y).
    Codimension-2 reflection (negates both timelike directions). -/
def thetaS (p : SplitPoint) : SplitPoint :=
  ⟨-p.u, -p.v, p.x, p.y⟩

/-- The R-symmetry (coordinate swap): (u, v, x, y) ↦ (v, u, x, y).
    Split-signature analogue of parity. -/
def swapR (p : SplitPoint) : SplitPoint :=
  ⟨p.v, p.u, p.x, p.y⟩

/-- The Euclidean time reflection θ := R ∘ Θ_S.
    In split coordinates: (u, v, x, y) ↦ (-v, -u, x, y).
    In Euclidean coordinates: (τ, σ, x, y) ↦ (-τ, σ, x, y). -/
def thetaE (p : SplitPoint) : SplitPoint :=
  swapR (thetaS p)

/-! ## Involution Properties -/

theorem thetaS_involution (p : SplitPoint) : thetaS (thetaS p) = p := by
  simp [thetaS]

theorem swapR_involution (p : SplitPoint) : swapR (swapR p) = p := by
  simp [swapR]

theorem thetaE_involution (p : SplitPoint) : thetaE (thetaE p) = p := by
  simp [thetaE, swapR, thetaS]

/-- θ_E = R ∘ Θ_S (definition). -/
theorem thetaE_eq_swapR_thetaS (p : SplitPoint) :
    thetaE p = swapR (thetaS p) := rfl

/-- Θ_S = R ∘ θ_E. -/
theorem thetaS_eq_swapR_thetaE (p : SplitPoint) :
    thetaS p = swapR (thetaE p) := by
  simp [thetaS, thetaE, swapR]

/-- The Klein four-group identity: θ_E ∘ R = Θ_S. -/
theorem klein_four_identity (p : SplitPoint) :
    thetaE (swapR p) = thetaS p := by
  simp [thetaE, swapR, thetaS]

/-- θ_E in explicit split coordinates. -/
theorem thetaE_explicit (p : SplitPoint) :
    thetaE p = ⟨-p.v, -p.u, p.x, p.y⟩ := by
  simp [thetaE, swapR, thetaS]

/-! ## Euclidean Coordinate Properties -/

/-- θ_E negates τ = (u+v)/√2. -/
theorem thetaE_negates_tau (p : SplitPoint) :
    (thetaE p).u + (thetaE p).v = -(p.u + p.v) := by
  simp [thetaE, swapR, thetaS]

/-- θ_E preserves σ = (u-v)/√2. -/
theorem thetaE_preserves_sigma (p : SplitPoint) :
    (thetaE p).u - (thetaE p).v = p.u - p.v := by
  simp [thetaE, swapR, thetaS]; ring

/-! ## Quadratic Form Preservation -/

theorem thetaS_preserves_norm (p : SplitPoint) :
    SplitPoint.splitNormSq (thetaS p) = SplitPoint.splitNormSq p := by
  unfold SplitPoint.splitNormSq thetaS; ring

theorem swapR_preserves_norm (p : SplitPoint) :
    SplitPoint.splitNormSq (swapR p) = SplitPoint.splitNormSq p := by
  unfold SplitPoint.splitNormSq swapR; ring

theorem thetaE_preserves_norm (p : SplitPoint) :
    SplitPoint.splitNormSq (thetaE p) = SplitPoint.splitNormSq p := by
  unfold SplitPoint.splitNormSq thetaE swapR thetaS; ring

/-! ## Linearity of Θ_S -/

theorem thetaS_add (p q : SplitPoint) :
    thetaS (SplitPoint.add p q) = SplitPoint.add (thetaS p) (thetaS q) := by
  simp [thetaS, SplitPoint.add]; constructor <;> ring

theorem thetaS_neg_timelike (a_u a_v : ℝ) :
    thetaS ⟨a_u, a_v, 0, 0⟩ = SplitPoint.neg ⟨a_u, a_v, 0, 0⟩ := by
  simp [thetaS, SplitPoint.neg]

/-! ## The Split Wedge and Forward Cones -/

/-- The split wedge W⁺ = {(u, v, x, y) : u > 0 ∧ v > 0}. -/
def splitWedge (p : SplitPoint) : Prop :=
  0 < p.u ∧ 0 < p.v

/-- The backward wedge W⁻ = {u < 0 ∧ v < 0}. -/
def splitWedgeMinus (p : SplitPoint) : Prop :=
  p.u < 0 ∧ p.v < 0

/-- The Euclidean half-space E⁺ = {τ > 0}, equivalently {u + v > 0}. -/
def euclideanHalf (p : SplitPoint) : Prop :=
  0 < p.u + p.v

/-- The split forward cone V_S⁺. -/
def splitForwardCone (p : SplitPoint) : Prop :=
  0 < p.u ∧ 0 < p.v ∧ p.transNormSq < p.u ^ 2 + p.v ^ 2

/-- The dual cone (V_S⁺)*. -/
def splitDualCone (p : SplitPoint) : Prop :=
  0 ≤ p.u ∧ 0 ≤ p.v ∧ p.transNormSq ≤ min p.u p.v ^ 2

/-- The closed split forward cone. -/
def splitForwardConeClosed (p : SplitPoint) : Prop :=
  0 ≤ p.u ∧ 0 ≤ p.v ∧ p.transNormSq ≤ p.u ^ 2 + p.v ^ 2

/-! ## Wedge Mapping Properties -/

theorem swapR_preserves_wedge (p : SplitPoint) (hp : splitWedge p) :
    splitWedge (swapR p) :=
  ⟨hp.2, hp.1⟩

theorem thetaS_sends_wedge_to_minus (p : SplitPoint) (hp : splitWedge p) :
    splitWedgeMinus (thetaS p) := by
  exact ⟨by simp [thetaS]; linarith [hp.1], by simp [thetaS]; linarith [hp.2]⟩

/-! ## Geometric Coverage: ∪_s W⁺(s) = E⁺ -/

theorem geometric_coverage (p : SplitPoint) (hp : euclideanHalf p) :
    ∃ s : ℝ, 0 < p.u + s ∧ 0 < p.v - s := by
  use (p.v - p.u) / 2
  unfold euclideanHalf at hp
  constructor <;> nlinarith

/-- The wedge condition in Euclidean coordinates: W⁺ ↔ τ > |σ|. -/
theorem wedge_iff_tau_gt_abs (τ σ : ℝ) :
    (0 < τ + σ ∧ 0 < τ - σ) ↔ |σ| < τ := by
  constructor
  · intro ⟨h1, h2⟩; rw [abs_lt]; exact ⟨by linarith, by linarith⟩
  · intro h; rw [abs_lt] at h; exact ⟨by linarith, by linarith⟩

/-! ## Coordinate Identity -/

/-- (a+b)² + (a-b)² = 2(a² + b²): split metric = Euclidean metric. -/
theorem metric_identity (a b : ℝ) :
    (a + b) ^ 2 + (a - b) ^ 2 = 2 * (a ^ 2 + b ^ 2) := by
  ring

end ComplexifiedQFT
