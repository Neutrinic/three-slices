# Complexified QFT: Unified Lean 4 Formalization

Formal verification of the algebraic core of the complexified spacetime QFT trilogy:

1. **Split Wedge** — Split signature as a third axiomatization of QFT
2. **Bridge** — n-point reconstruction across real forms of ℂ^d
3. **Cauchy-Szegő** — Simultaneous reflection positivity via the Type IV domain

## Project Structure

```
complexified-qft-lean4/
├── ComplexifiedQFT.lean              # Root import
├── ComplexifiedQFT/
│   ├── Foundations/                   # Shared definitions
│   │   ├── Defs.lean                 # SplitPoint, cones, wedge, Θ_S/R/θ_E, V₄
│   │   └── ComplexInvolutions.lean   # ℂ⁴, σ_L/σ_E/σ_S, fixed-point sets, signatures
│   ├── SplitWedge/                   # Paper 1 + Bridge
│   │   ├── TubeInclusion.lean        # SO(4,ℂ) rotation, V_L⁺ → V_S⁺, T_S ⊂ T'
│   │   ├── Axioms.lean              # (S1)-(S8) structure (see Known Limitations)
│   │   ├── Bridge.lean              # θ_E = R∘Θ_S, shift identities
│   │   ├── DualCone.lean            # (V_S⁺)* ⊊ V_S⁺, non-self-duality
│   │   ├── SumKernel.lean           # Θ_S converts difference → sum kernel
│   │   ├── Contractivity.lean       # Damping, contractivity bound
│   │   ├── EuclideanMetric.lean     # Euclidean coordinates, c-dual
│   │   └── Trinity.lean             # Two-Point Trinity equivalence cycle (see Known Limitations)
│   └── CauchySzego/                  # Paper 3
│       ├── Jordan.lean              # Spin factor V_N, Δ(u), Lorentz cone
│       ├── TypeIV.lean              # Lie ball D^N_IV, Shilov boundary, Wallach set
│       ├── Involutions.lean         # α, θ, δ = α∘θ, V₄ dictionary
│       ├── KTypes.lean              # (m₁,m₂) lattice, Hardy condition
│       ├── DeltaEvenness.lean       # ★ THE THEOREM: k + |λ| = 2m₁ ∈ 2ℤ
│       └── VectorValued.lean        # J_τ, full δ-eigenvalue, Theorem 7.1
├── lakefile.lean
└── lean-toolchain
```

## What's Proven (No `sorry`)

### Foundations
- Three antiholomorphic involutions σ_L, σ_E, σ_S on ℂ⁴ are involutions
- σ_L ∘ σ_E, σ_S ∘ σ_L, σ_E ∘ σ_S composition laws (Klein four-group)
- Fixed-point characterization: σ_L ↔ all real, σ_E ↔ z⁰ imaginary, σ_S ↔ z¹ imaginary
- Signature verification: Q restricts to (+,-,-,-), (-,-,-,-), (+,+,-,-) on fixed sets
- Θ_S, R, θ_E are involutions forming a Klein four-group
- All three preserve the split quadratic form
- Geometric coverage: ∪_s W⁺(s) = E⁺

### Split Wedge
- SO(4,ℂ) rotation preserves Lorentz metric (Λ^T η Λ = η) and has det = 1
- Forward cone inclusion: V_L⁺ → V_S⁺ (both timelike components positive)
- Sum-kernel rewrite: Θ_S(ξ)-y = (-(u_ξ+u_y), -(v_ξ+v_y), x_ξ-x_y, y_ξ-y_y)
- Shift identity: Θ_S(ξ+a) = Θ_S(ξ) - a for **timelike** a = (a_u, a_v, 0, 0)
- Translated kernel: Θ_S(ξ'+a)-(η'+a) = Θ_S(ξ')-η' - 2a for **timelike** a
- Contractivity bound: |c·w| ≤ w for |c| ≤ 1
- Non-self-duality: ∃ p,y ∈ V_S⁺ with g_S(p,y) = -29 < 0
- Dual cone is strictly smaller than forward cone

**Note:** The shift identity and translated kernel were originally stated for
general translations. The Lean formalization caught that they only hold for
timelike a (spatial components break the identity because Θ_S preserves x,y).
This does not affect the main theorems, which use only timelike shifts.

### Cauchy-Szegő (★ Main Results)
- **δ-evenness (Theorem 7.2)**: k + |λ| = 2m₁ for ALL K-types — `ring`
- **k + |λ| is always even** — no δ-odd K-types exist on the Lie sphere
- **(-1)^{k+|λ|} = +1** for every K-type (scalar δ-eigenvalue)
- Half-integer m₁ is impossible (δ-odd types require it)
- Hardy condition is NOT needed for δ-evenness
- Full δ-eigenvalue = J_τ (scalar factor drops out)
- For J_τ = +id: every Hardy section is δ-even
- N=6 (d=4) verification: all lowest K-types checked
- N=10 (d=6) non-Hardy example: (2,-1) is δ-even but non-Hardy

## What's Axiomatized (`sorry` or `trivial`)

Functional analysis results not yet available in Mathlib:

| Result | Used In | Status |
|--------|---------|--------|
| BCR theorem | Trinity (3)→(1) | `trivial` |
| OS reconstruction | Trinity (2)→(1) | `trivial` |
| Wick rotation | Trinity (1)→(2) | `sorry` |
| Analytic continuation through T' | Trinity (1)→(3) | `sorry` |
| Paley-Wiener-Schwartz | Spectrum condition | axiomatized |
| GNS construction | Hilbert space | axiomatized |
| Hille-Yosida | Semigroup generation | axiomatized |
| Hardy space theory | H² characterization | axiomatized |
| Schmid decomposition | K-type enumeration | axiomatized |

The `sorry` count is exactly 2 (both in Trinity.lean).
**The central δ-evenness theorem has zero sorrys.**

## Known Limitations

**Axioms.lean:** Axioms S1 (translation invariance) and S3 (R-invariance) are
implemented with mathematical content. Axioms S5–S8 (spectrum condition, wedge
positivity, locality, cluster decomposition) are axiomatized as bare `Prop` fields
with no mathematical content. This is because tempered distributions, spectral
measures, and spacelike commutation are not available in Mathlib. These
axioms will gain mathematical content as Mathlib's functional analysis
library develops.

**Trinity.lean:** The three positivity conditions (Lorentzian spectral, Euclidean
OS, split wedge) are defined as `True`. The Two-Point Trinity theorem therefore
proves `True ↔ True ↔ True`. The algebraic legs connecting the proven components
(sum-kernel, tube inclusion, bridge factorization) are in place, but the theorem
itself is structural scaffolding, not a verified equivalence. The `trivial` proofs
are no more substantive than the `sorry` proofs.

**Where the substance lives:** The substantive formalization is in
Foundations/ComplexInvolutions (signature verification), SplitWedge/DualCone
(non-self-duality with explicit counterexample), SplitWedge/TubeInclusion
(cone rotation), CauchySzego/DeltaEvenness (the critical path, zero sorrys),
and CauchySzego/VectorValued (full δ-eigenvalue). These modules contain real
mathematical content verified by Lean, not structural placeholders.

## Building

The project tracks Mathlib master. To build:

```bash
# 1. Sync toolchain with current Mathlib (ensures version compatibility)
curl -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain

# 2. Fetch dependencies and Mathlib cache
lake update
lake exe cache get

# 3. Build
lake build
```

If `lake update` reports a toolchain mismatch, re-run step 1. The included
`lean-toolchain` may become stale as Mathlib advances; the `curl` command
always gives you the correct version.

## Corrections Found by Formalization

The Lean build process caught two mathematical errors in the papers:

1. **Shift identity (Split Wedge paper):** Θ_S(ξ+a) = Θ_S(ξ) - a was stated
   for general translations. The identity only holds for timelike a = (a_u, a_v, 0, 0)
   because Θ_S preserves spatial components. Corrected to restrict to timelike shifts.

2. **Quadratic form (TubeInclusion.lean):** An identity claimed y₀² - y₁² on the
   RHS; the correct expansion gives y₀² + y₁². The tube inclusion theorem is
   unaffected (it uses positivity, not the sign).

## Paper Section Mapping

| Paper Section | Lean Module | Content |
|--------------|-------------|---------|
| Split Wedge §2 | Foundations/ComplexInvolutions | σ_L, σ_E, σ_S on ℂ⁴ |
| Split Wedge §3 | SplitWedge/TubeInclusion | SO(4,ℂ) rotation, T_S ⊂ T' |
| Split Wedge §4 | SplitWedge/Axioms | (S1)-(S8) structure |
| Split Wedge §5 | SplitWedge/SumKernel | Sum-kernel, semigroup PD |
| Split Wedge §6 | SplitWedge/Bridge + EuclideanMetric | θ = R∘Θ_S, coverage |
| Split Wedge Cor 5.7 | SplitWedge/Trinity | Two-Point Trinity |
| Bridge §3-5 | Foundations/Defs | SplitPoint, cones, V₄ |
| Bridge Thm 5.7 | SplitWedge/DualCone | Non-self-duality |
| Cauchy-Szegő §2.2 | CauchySzego/Jordan | Spin factor, Δ(u), Ω |
| Cauchy-Szegő §2.1 | CauchySzego/TypeIV | D^N_IV, Wallach set |
| Cauchy-Szegő §2.3 | CauchySzego/Involutions | α, θ, δ, V₄ dictionary |
| Cauchy-Szegő §6 | CauchySzego/KTypes | (m₁,m₂) lattice, Hardy |
| **Cauchy-Szegő Thm 7.2** | **CauchySzego/DeltaEvenness** | **k+\|λ\| = 2m₁** |
| Cauchy-Szegő §4-5 | CauchySzego/VectorValued | J_τ, Theorem 7.1 |

## Design Decisions

1. **Single repository**: Papers share definitions (SplitPoint, involutions, cones). No duplication.
2. **Foundations feed both**: SplitWedge/ and CauchySzego/ both import from Foundations/.
3. **Axioms as structures**: SplitQFT, LorentzianQFT, EuclideanQFT encode the logical architecture. S5-S8 are `Prop` placeholders awaiting Mathlib distribution theory.
4. **Trinity skeleton**: The equivalence cycle is stated as `Iff`. The positivity conditions are `True`; the theorem is structural, not substantive. See Known Limitations.
5. **SpinFactorElt with ‖u'‖²**: Avoids ℝ^{N-1} vectors; stores the squared norm directly.
6. **KType as (m₁,m₂) with dominance**: Natural parametrization; coordinate change is definitional.
7. **DeltaStructure as inductive**: Clean pattern matching on positive/negative.