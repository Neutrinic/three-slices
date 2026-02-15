# VERIFICATION.md -- Lean-to-Paper Theorem Map

This document maps every formally verified result in the Lean 4 + Mathlib
formalization to its corresponding location in the three source papers.

## Summary

| Metric | Value |
|--------|-------|
| Total Lean declarations (theorem/lemma/def/example) | 206 |
| Theorems and lemmas with proofs | 144 |
| Definitions, structures, and inductives | 56 |
| Computed examples | 6 |
| `sorry` count | **2** (both in `Trinity.lean`) |
| Critical path (`DeltaEvenness`) sorry count | **0** |

The two `sorry`s are both functional-analytic results requiring heavy Mathlib
extensions (distributions, analytic continuation, OS reconstruction). They are
intentionally axiomatized as they fall outside the algebraic core that this
formalization targets.

---

## Key Theorems

The 10 most important formally verified results, ordered by paper significance:

| # | Lean Name | File:Line | Paper Reference | Status |
|---|-----------|-----------|-----------------|--------|
| 1 | `delta_evenness` | `DeltaEvenness.lean:31` | Paper 3, Thm 7.2 (`thm:disjointness`), eq. (A.9) | Verified |
| 2 | `k_plus_lambda_even` | `DeltaEvenness.lean:35` | Paper 3, Thm 7.2 corollary | Verified |
| 3 | `delta_eigenvalue_positive` | `DeltaEvenness.lean:40` | Paper 3, Thm 7.2, eq. (7.2) | Verified |
| 4 | `no_delta_odd_Ktypes` | `DeltaEvenness.lean:53` | Paper 3, Thm 7.2 / Remark 7.3 | Verified |
| 5 | `scalar_lattice_uniformly_delta_even` | `DeltaEvenness.lean:121` | Paper 3, Thm 7.2 (universal version) | Verified |
| 6 | `trilogy_resolved` | `VectorValued.lean:148` | Paper 3, Thm 8.1 (`thm:main`) | Verified |
| 7 | `sigmaL/E/S_involution` | `ComplexInvolutions.lean:62,66,70` | Paper 1, Sec. 2.2 | Verified |
| 8 | `split_signature_from_quadratic` | `ComplexInvolutions.lean:195` | Paper 1, Remark 2.3 (Verification of Split Signature) | Verified |
| 9 | `splitForwardCone_not_self_dual` | `DualCone.lean:62` | Paper 1, Sec. 2.3, footnote; Paper 2, Sec. 3 | Verified |
| 10 | `two_point_trinity` | `Trinity.lean:69` | Paper 1, Cor. 5.7 (`cor:trinity`) | 2 sorry legs |

---

## Part 1: Foundations (Shared by Papers 1 and 2)

### Foundations/Defs.lean

Core definitions for split-signature spacetime R^{2,2}, the three involutions,
forward cones, and the split wedge.

**Reference:** Paper 1, Sections 2 and 4; Paper 2, Sections 2--3.

| Lean Name | Type | Line | Paper Reference | Description |
|-----------|------|------|-----------------|-------------|
| `SplitPoint` | structure | 26 | Paper 1, Sec. 2.3 (Def. 4.2) | Point in R^{2,2} with coordinates (u,v,x,y) |
| `SplitPoint.zero` | def | 36 | -- | The zero point |
| `SplitPoint.add` | def | 39 | -- | Pointwise addition |
| `SplitPoint.sub` | def | 43 | -- | Pointwise subtraction |
| `SplitPoint.neg` | def | 47 | -- | Negation |
| `SplitPoint.scale` | def | 51 | -- | Scalar multiplication |
| `SplitPoint.timelike` | def | 55 | Paper 1, Sec. 6, Step 3 | Purely timelike translation (x=y=0) |
| `SplitPoint.splitInner` | def | 58 | Paper 1, Sec. 2.3, eq. (2.4) | Split bilinear form g_S(p,q) |
| `SplitPoint.splitNormSq` | def | 62 | Paper 1, Sec. 2.3, eq. (2.5) | Quadratic form Q_S(p) = u^2+v^2-x^2-y^2 |
| `SplitPoint.transNormSq` | def | 66 | Paper 1, Sec. 2.3 | Transverse norm |p_perp|^2 = x^2+y^2 |
| `splitInner_self` | theorem | 69 | -- | g_S(p,p) = Q_S(p) |
| `splitInner_comm` | theorem | 73 | -- | g_S is symmetric |
| `thetaS` | def | 83 | Paper 1, Def. 4.3 (Split Reflection) | Theta_S: (u,v,x,y) -> (-u,-v,x,y) |
| `swapR` | def | 88 | Paper 1, Axiom (S3); Paper 1, Remark 6.5 | R-symmetry: (u,v,x,y) -> (v,u,x,y) |
| `thetaE` | def | 94 | Paper 1, Sec. 6, Step 5 | theta_E = R . Theta_S: Euclidean time reflection |
| `thetaS_involution` | theorem | 99 | Paper 1, Sec. 4.1 | Theta_S^2 = id |
| `swapR_involution` | theorem | 102 | Paper 1, Remark 6.5 | R^2 = id |
| `thetaE_involution` | theorem | 105 | Paper 1, Sec. 6 | theta_E^2 = id |
| `thetaE_eq_swapR_thetaS` | theorem | 109 | Paper 1, Sec. 6, Step 5 | theta_E = R . Theta_S (definition) |
| `thetaS_eq_swapR_thetaE` | theorem | 113 | Paper 1, Sec. 6 | Theta_S = R . theta_E |
| `klein_four_identity` | theorem | 118 | Paper 1, Remark 6.8; Paper 2, Prop. 2.1 (`prop:V4`) | Klein V4: theta_E . R = Theta_S |
| `thetaE_explicit` | theorem | 123 | Paper 1, Sec. 6, Step 5 | theta_E in split coordinates |
| `thetaE_negates_tau` | theorem | 130 | Paper 1, Sec. 6, Step 5 | theta_E negates tau = (u+v)/sqrt(2) |
| `thetaE_preserves_sigma` | theorem | 135 | Paper 1, Sec. 6, Step 5 | theta_E preserves sigma = (u-v)/sqrt(2) |
| `thetaS_preserves_norm` | theorem | 141 | Paper 1, Sec. 4 | Theta_S preserves Q_S |
| `swapR_preserves_norm` | theorem | 145 | Paper 1, Axiom (S2)/(S3) | R preserves Q_S |
| `thetaE_preserves_norm` | theorem | 149 | Paper 1, Sec. 6 | theta_E preserves Q_S |
| `thetaS_add` | theorem | 155 | Paper 1, Sec. 5, Step 1 | Theta_S is linear (additivity) |
| `thetaS_neg_timelike` | theorem | 159 | Paper 1, Sec. 5 | Theta_S negates timelike vectors |
| `splitWedge` | def | 166 | Paper 1, Def. 4.1 (Split Wedge) | W+ = {u > 0, v > 0} |
| `splitWedgeMinus` | def | 170 | Paper 1, Sec. 5, Step 1 | W- = {u < 0, v < 0} |
| `euclideanHalf` | def | 174 | Paper 1, Sec. 6, Step 6 | E+ = {tau > 0}, i.e., {u+v > 0} |
| `splitForwardCone` | def | 178 | Paper 1, Def. 2.5 (Forward Cones) | V_S+ |
| `splitDualCone` | def | 182 | Paper 1, eq. (2.2) (`eq:dual-cone`) | (V_S+)* |
| `splitForwardConeClosed` | def | 186 | Paper 1, Sec. 2.3 | Closed split forward cone |
| `swapR_preserves_wedge` | theorem | 191 | Paper 1, Lemma 6.6 proof (`lemma:bridge`) | R preserves W+ |
| `thetaS_sends_wedge_to_minus` | theorem | 195 | Paper 1, Sec. 5, Step 1 | Theta_S maps W+ to W- |
| `geometric_coverage` | theorem | 201 | Paper 1, Sec. 6, Step 6, eq. (6.10) | Union of shifted wedges = E+ |
| `wedge_iff_tau_gt_abs` | theorem | 208 | Paper 1, Sec. 6, Step 5 | W+ iff tau > |sigma| |
| `metric_identity` | theorem | 217 | Paper 1, Sec. 6 | (a+b)^2 + (a-b)^2 = 2(a^2+b^2) |

### Foundations/ComplexInvolutions.lean

The three antiholomorphic involutions on complexified spacetime C^4.

**Reference:** Paper 1, Section 2.2 (The Three Real Slices); Paper 2, Def. 2.1 (`def:involutions`).

| Lean Name | Type | Line | Paper Reference | Description |
|-----------|------|------|-----------------|-------------|
| `ComplexPoint` | structure | 21 | Paper 1, Sec. 2.1 | Point in C^4 |
| `ComplexPoint.complexQuadratic` | def | 31 | Paper 1, Sec. 2.1, eq. (2.1) | Q(z) = (z^0)^2 - (z^1)^2 - (z^2)^2 - (z^3)^2 |
| `sigmaL` | def | 40 | Paper 1, Sec. 2.2(i); Paper 2, eq. (2.3) | sigma_L: componentwise conjugation |
| `sigmaE` | def | 46 | Paper 1, Sec. 2.2(ii); Paper 2, eq. (2.1) | sigma_E: negate-conjugate z^0 |
| `sigmaS` | def | 52 | Paper 1, Sec. 2.2(iii); Paper 2, eq. (2.2) | sigma_S: negate-conjugate z^1 |
| `sigmaL_involution` | theorem | 62 | Paper 1, Sec. 2.2 | sigma_L^2 = id |
| `sigmaE_involution` | theorem | 66 | Paper 1, Sec. 2.2 | sigma_E^2 = id |
| `sigmaS_involution` | theorem | 70 | Paper 1, Sec. 2.2 | sigma_S^2 = id |
| `sigmaE_comp_sigmaL` | theorem | 76 | Paper 1, Remark 2.4 | sigma_E . sigma_L: Wick rotation z^0 -> -z^0 |
| `sigmaS_comp_sigmaL` | theorem | 81 | Paper 2, Def. 2.2 (`def:holo_auto`) | sigma_S . sigma_L implements z^1 -> -z^1 |
| `sigmaS_comp_sigmaE` | theorem | 86 | Paper 2, Prop. 2.1 (`prop:V4`) | Involutions commute: sigma_S . sigma_E = sigma_E . sigma_S |
| `conj_eq_self_iff_im_zero` | theorem | 96 | Paper 1, Sec. 2.2 | Helper: conj(z) = z iff Im(z) = 0 |
| `neg_conj_eq_self_iff_re_zero` | theorem | 106 | Paper 1, Sec. 2.2 | Helper: -conj(z) = z iff Re(z) = 0 |
| `sigmaL_fixed_iff` | theorem | 118 | Paper 1, Sec. 2.2(i) | Fixed set of sigma_L: all components real (R^{1,3}) |
| `sigmaE_fixed_iff` | theorem | 138 | Paper 1, Sec. 2.2(ii) | Fixed set of sigma_E: z^0 purely imaginary (R^{0,4}) |
| `sigmaS_fixed_iff` | theorem | 158 | Paper 1, Sec. 2.2(iii) | Fixed set of sigma_S: z^1 purely imaginary (R^{2,2}) |
| `lorentzian_signature_from_quadratic` | theorem | 185 | Paper 1, Sec. 2.2(i) | Q restricts to (+,-,-,-) on sigma_L fixed set |
| `split_signature_from_quadratic` | theorem | 195 | Paper 1, Remark 2.3 (Verification of Split Signature) | Q restricts to (+,+,-,-) on sigma_S fixed set |
| `euclidean_signature_from_quadratic` | theorem | 207 | Paper 1, Sec. 2.2(ii) | Q restricts to (0,-,-,-,-) = neg-definite on sigma_E fixed set |

---

## Part 2: Split Wedge (Papers 1 and 2)

### SplitWedge/TubeInclusion.lean

The SO(4,C) rotation mapping the Lorentzian forward tube into the split forward tube.

**Reference:** Paper 1, Section 3, Lemma 3.2 (`lemma:split-tube`).

| Lean Name | Type | Line | Paper Reference | Description |
|-----------|------|------|-----------------|-------------|
| `lorentz_00_entry` | theorem | 18 | Paper 1, Lemma 3.2 proof | B^T diag(1,-1) B: (0,0) entry = 1 |
| `lorentz_11_entry` | theorem | 22 | Paper 1, Lemma 3.2 proof | (1,1) entry = -1 |
| `lorentz_01_entry` | theorem | 26 | Paper 1, Lemma 3.2 proof | Off-diagonal vanishes |
| `det_rotation_block` | theorem | 30 | Paper 1, Lemma 3.2 proof | det B = 1 |
| `rotation_sum_of_squares` | theorem | 37 | Paper 1, Lemma 3.2 proof | Rotation preserves form |
| `forward_cone_implies_both_positive` | theorem | 43 | Paper 1, Lemma 3.2 proof | V_L+ implies y^0 +/- y^1 > 0 |
| `lorentzian_to_split_cone` | theorem | 51 | Paper 1, Lemma 3.2 | Lambda maps V_L+ into V_S+ |

### SplitWedge/Axioms.lean

The (S1)--(S8) axiom system for split-signature QFT.

**Reference:** Paper 1, Section 6.1, Def. 6.1 (`def:split-axioms`).

| Lean Name | Type | Line | Paper Reference | Description |
|-----------|------|------|-----------------|-------------|
| `SplitQFT` | structure | 21 | Paper 1, Def. 6.1 (`def:split-axioms`) | Split-signature QFT structure with axioms (S1)--(S8) |
| `translate_then_swap` | theorem | 50 | Paper 1, Axioms (S1)+(S3) | Combined translation + R-swap identity |
| `LorentzianQFT` | structure | 59 | Paper 1, Sec. 5.3 (Wightman axioms) | Lorentzian QFT (Wightman) structure |
| `EuclideanQFT` | structure | 65 | Paper 1, Sec. 5.2 (OS axioms) | Euclidean QFT (Osterwalder-Schrader) structure |

### SplitWedge/Bridge.lean

The Bridge Lemma: algebraic core of the theta_E-positivity transfer.

**Reference:** Paper 1, Section 6, Lemma 6.6 (`lemma:bridge`); Paper 2, Sections 2--5.

| Lean Name | Type | Line | Paper Reference | Description |
|-----------|------|------|-----------------|-------------|
| `bridge_factorization` | theorem | 22 | Paper 1, Sec. 6, Step 5; Paper 2, Prop. 2.1 | theta_E(p) = R(Theta_S(p)) |
| `bridge_conjugation` | theorem | 26 | Paper 1, Lemma 6.6 proof | theta_E(R(p)) = Theta_S(p) |
| `bridge_conjugation_converse` | theorem | 31 | Paper 1, Sec. 6 | Theta_S(R(p)) = theta_E(p) |
| `thetaS_shift` | theorem | 38 | Paper 1, Sec. 6, eq. (6.6) (`eq:theta-shift`) | Theta_S(xi+a) = Theta_S(xi) - a (timelike a) |
| `thetaS_sub_reversal` | theorem | 45 | Paper 1, Sec. 6, Step 3 | Theta_S(x-a) = Theta_S(x) + a |
| `translated_kernel` | theorem | 53 | Paper 1, Sec. 6, Step 3, Lemma 6.3 | Translated kernel: damping by 2a |
| `wedge_from_halfspace` | theorem | 65 | Paper 1, Sec. 6, Step 6 | E+ covered by shifted wedges |
| `bridge_lemma_identity` | theorem | 86 | Paper 1, Lemma 6.6 (`lemma:bridge`) | Bridge Lemma algebraic core identity |

### SplitWedge/DualCone.lean

Dual cone geometry and non-self-duality of V_S+.

**Reference:** Paper 1, Section 2.3, eq. (2.2); Paper 2, Section 3.

| Lean Name | Type | Line | Paper Reference | Description |
|-----------|------|------|-----------------|-------------|
| `dualCone_subset_forwardConeClosed` | theorem | 19 | Paper 1, Sec. 2.3 | (V_S+)* subset closed V_S+ |
| `dualCone_nonempty` | theorem | 31 | Paper 1, Sec. 2.3 | (1,1,0,0) in dual cone |
| `dualCone_diagonal` | theorem | 34 | Paper 1, Sec. 2.3 | (a,a,0,0) in dual cone for a > 0 |
| `splitInner_nonneg_diagonal` | theorem | 41 | Paper 1, Sec. 2.3 | g_S >= 0 for diagonal vs dual cone |
| `counterexample_p_in_cone` | theorem | 51 | Paper 1, Sec. 2.3, footnote 3 | (10,1,7,0) in V_S+ |
| `counterexample_y_in_cone` | theorem | 54 | Paper 1, Sec. 2.3, footnote 3 | (1,10,7,0) in V_S+ |
| `counterexample_negative_inner` | theorem | 57 | Paper 1, Sec. 2.3, footnote 3 | g_S(p,y) = -29 |
| `splitForwardCone_not_self_dual` | theorem | 62 | Paper 1, Sec. 2.3, footnote 3 | V_S+ is not self-dual |
| `dualCone_strictly_smaller` | theorem | 69 | Paper 1, Sec. 2.3, eq. (2.2) | (V_S+)* strictly contained in V_S+ |
| `cauchy_schwarz_R2` | theorem | 77 | Paper 1, Sec. 5 (auxiliary) | Cauchy-Schwarz in R^2 |

### SplitWedge/SumKernel.lean

The sum-kernel rewrite and semigroup positive-definiteness.

**Reference:** Paper 1, Section 5, Lemma 5.1 (`lemma:spectral`), Steps 1--5.

| Lean Name | Type | Line | Paper Reference | Description |
|-----------|------|------|-----------------|-------------|
| `sum_kernel_u` | theorem | 26 | Paper 1, Sec. 5.1, Step 1, eq. (5.4) | Theta_S(xi)-y has u-component -(u_xi+u_y) |
| `sum_kernel_v` | theorem | 31 | Paper 1, Sec. 5.1, Step 1, eq. (5.4) | v-component: -(v_xi+v_y) |
| `sum_kernel_x` | theorem | 36 | Paper 1, Sec. 5.1, Step 1 | Transverse: difference |
| `sum_kernel_full` | theorem | 42 | Paper 1, Sec. 5.1, Step 1, eq. (5.3)--eq. (5.5) | Full sum-kernel identity |
| `semigroup_assoc` | theorem | 51 | Paper 1, Sec. 5.1, Step 5 | (R+^2, +) associativity |
| `semigroup_comm` | theorem | 57 | Paper 1, Sec. 5.1, Step 5 | (R+^2, +) commutativity |
| `pd_diagonal` | theorem | 62 | Paper 1, Sec. 5.1, Step 5 | Diagonal element: sigma_i + sigma_i = 2 sigma_i |
| `psd_2x2_det` | theorem | 66 | Paper 1, Sec. 5.1 (auxiliary) | 2x2 PSD determinant condition |
| `laplace_additive` | theorem | 73 | Paper 1, Sec. 5.1, Step 6, eq. (5.11) (`eq:laplace`) | Laplace exponent additivity |
| `laplace_at_origin` | theorem | 78 | Paper 1, Sec. 5.1, Step 6 | Laplace exponent vanishes at origin |
| `laplace_exponent_nonneg` | theorem | 82 | Paper 1, Sec. 5.1, Step 6 | Laplace exponent non-negative |
| `IsSemigroupPD` | def | 108 | Paper 1, Sec. 5.1, Step 5 | Semigroup positive-definiteness |

### SplitWedge/Contractivity.lean

The contraction semigroup structure from timelike translations.

**Reference:** Paper 1, Section 6, Step 3, Lemma 6.3 (`lemma:contractivity-n`).

| Lean Name | Type | Line | Paper Reference | Description |
|-----------|------|------|-----------------|-------------|
| `damping_positive` | theorem | 22 | Paper 1, Sec. 6, Step 3 | p_u a_u + p_v a_v > 0 for positive components |
| `tube_damping_positive` | theorem | 28 | Paper 1, Sec. 6, Step 3 | Tube regularization: eps * (p.y) > 0 |
| `contractivity_bound` | theorem | 35 | Paper 1, Lemma 6.3 (`lemma:contractivity-n`); Paper 2, Thm 5.2 (`thm:contractivity`) | |c * w| <= w for |c| <= 1 |
| `semigroup_composition` | theorem | 45 | Paper 1, Sec. 6, Step 3 | T(a) . T(b) = T(a+b) |
| `semigroup_identity` | theorem | 51 | Paper 1, Sec. 6, Step 3 | T(0) = id |
| `timelike_double_shift` | theorem | 54 | Paper 1, Sec. 6, Step 3 | scale(2, timelike(a)) = timelike(2a) |

### SplitWedge/EuclideanMetric.lean

Euclidean coordinate involutions and metric structure.

**Reference:** Paper 1, Section 6, Steps 5--7.

| Lean Name | Type | Line | Paper Reference | Description |
|-----------|------|------|-----------------|-------------|
| `R_preserves_tau` | theorem | 25 | Paper 1, Sec. 6, Step 5 | R preserves tau |
| `R_negates_sigma` | theorem | 29 | Paper 1, Sec. 6, Step 5 | R negates sigma |
| `thetaS_negates_tau` | theorem | 34 | Paper 1, Sec. 6, Step 5 | Theta_S negates tau |
| `thetaS_negates_sigma` | theorem | 37 | Paper 1, Sec. 6, Step 5 | Theta_S negates sigma |
| `theta_negates_tau` | theorem | 42 | Paper 1, Sec. 6, Step 5 | theta = R . Theta_S negates tau |
| `theta_preserves_sigma` | theorem | 45 | Paper 1, Sec. 6, Step 5 | theta preserves sigma |
| `coverage` | theorem | 51 | Paper 1, Sec. 6, Step 6 | For tau > 0, exists s with |sigma-s| < tau |
| `c_dual_metric_flip` | theorem | 59 | Paper 1, Sec. 6, Step 7 | c-dual sign flip: -tau^2 + sigma^2 + ... |
| `lie_algebra_dim` | theorem | 65 | Paper 1, Sec. 6, Step 7 | ISO(4) has 10 generators: 6+4 |
| `theta_split_explicit` | theorem | 70 | Paper 1, Sec. 6, Step 5 | theta in split coordinates |
| `star_factorization` | theorem | 75 | Paper 1, Sec. 6, Step 5 | theta = R . Theta_S at coordinate level |

### SplitWedge/Trinity.lean

The Two-Point Trinity: equivalence of three positivity formulations.

**Reference:** Paper 1, Corollary 5.7 (`cor:trinity`).

**NOTE: Contains the only 2 `sorry`s in the entire codebase.**

| Lean Name | Type | Line | Paper Reference | Description |
|-----------|------|------|-----------------|-------------|
| `TwoPointData` | structure | 27 | Paper 1, Sec. 5 | Two-point distribution W_2 |
| `LorentzianSpectralPositivity` | def | 32 | Paper 1, Cor. 5.7 item (1) | Kallen-Lehmann with rho >= 0 |
| `EuclideanOSPositivity` | def | 35 | Paper 1, Cor. 5.7 item (2) | OS reflection positivity |
| `SplitWedgePositivity` | def | 38 | Paper 1, Cor. 5.7 item (3) | Split wedge reflection positivity |
| `split_implies_lorentzian` | theorem | 44 | Paper 1, Cor. 5.7: (3)=>(1) | Split -> Lorentzian (via sum-kernel + BCR) |
| `lorentzian_implies_euclidean` | theorem | 49 | Paper 1, Cor. 5.7: (1)=>(2) | **SORRY**: Wick rotation (OS reconstruction) |
| `euclidean_implies_lorentzian` | theorem | 56 | Paper 1, Cor. 5.7: (2)=>(1) | Euclidean -> Lorentzian (OS reconstruction) |
| `lorentzian_implies_split` | theorem | 61 | Paper 1, Cor. 5.7: (1)=>(3) | **SORRY**: Analytic continuation through T' |
| `two_point_trinity` | theorem | 69 | Paper 1, Cor. 5.7 (`cor:trinity`) | Split <-> Lorentzian equivalence |
| `two_point_trinity_full` | theorem | 73 | Paper 1, Cor. 5.7 (`cor:trinity`) | Full three-way equivalence cycle |

---

## Part 3: Cauchy-Szego (Paper 3)

### CauchySzego/Jordan.lean

The spin factor Jordan algebra and Lorentz cone.

**Reference:** Paper 3, Section 2.2 (`subsec:tube`); Faraut-Koranyi (1994).

| Lean Name | Type | Line | Paper Reference | Description |
|-----------|------|------|-----------------|-------------|
| `SpinFactorElt` | structure | 28 | Paper 3, Sec. 2.2, eq. (2.4) | Element of spin factor V_N = (u_0, u') |
| `SpinFactorElt.det` | def | 37 | Paper 3, Sec. 2.2, eq. (2.6) (`eq:jordan-det`) | Jordan determinant Delta(u) = u_0^2 - ||u'||^2 |
| `SpinFactorElt.spectralValue1` | def | 41 | Paper 3, Sec. 2.2 | lambda_1 = u_0 + ||u'|| |
| `SpinFactorElt.spectralValue2` | def | 44 | Paper 3, Sec. 2.2 | lambda_2 = u_0 - ||u'|| |
| `det_eq_spectral_product` | theorem | 48 | Paper 3, Sec. 2.2 | Delta = lambda_1 * lambda_2 |
| `lorentzCone` | def | 61 | Paper 3, Sec. 2.2, eq. (2.5) (`eq:light-cone`) | Omega = {y : y_0 > ||y'||} |
| `det_pos_of_cone` | theorem | 65 | Paper 3, Sec. 2.2 | y in Omega => Delta(y) > 0 |
| `cone_sum_det_pos` | theorem | 72 | Paper 3, Sec. 4.1 (`subsec:euclidean-restriction`) | Omega is convex (at determinant level) |
| `domainParam` | def | 88 | Paper 3, Sec. 2, paragraph | N = 2d-2 |
| `typeIV_rank` | def | 91 | Paper 3, Sec. 2.2 | Rank of Type IV domain = 2 |
| `peirceConst` | def | 94 | Paper 3, Sec. 3.1 (`rem:wallach`) | Peirce constant a = N-2 |
| `genus` | def | 97 | Paper 3, Sec. 3.1 | Genus g = N |
| `szegoParam` | def | 100 | Paper 3, Sec. 3.1, eq. (3.3) (`eq:szego-constant`) | Szego parameter nu = N/2 |
| `szego_above_wallach` | theorem | 104 | Paper 3, Sec. 3.1, Remark 3.1 (`rem:wallach`) | nu > (N-2)/2 (Wallach threshold) |

### CauchySzego/TypeIV.lean

The Lie ball D^N_IV, Shilov boundary, and tube domain.

**Reference:** Paper 3, Section 2 (`sec:domain`).

| Lean Name | Type | Line | Paper Reference | Description |
|-----------|------|------|-----------------|-------------|
| `LieBallPoint` | structure | 27 | Paper 3, Sec. 2.1, Def. 2.1, eqs. (2.1)--(2.2) | Point in D^N_IV with defining inequalities |
| `shilov_dim` | theorem | 47 | Paper 3, Sec. 2.1, eq. (2.3) (`eq:shilov`) | dim(Shilov boundary) = N |
| `domain_real_dim` | theorem | 50 | Paper 3, Sec. 2.1 | dim_R(D^N_IV) = 2N |
| `shilov_codim` | theorem | 53 | Paper 3, Sec. 2.1 | Codimension of Shilov boundary = N |
| `TubePoint` | structure | 64 | Paper 3, Sec. 2.2, eq. (2.7) (`eq:tube`) | Point in T_Omega = R^N + i*Omega |
| `euclidean_section_argument` | theorem | 84 | Paper 3, Sec. 4.1, eq. (4.1) (`eq:euclidean-kernel`) | Euclidean section: kernel argument is y+y' |
| `euclidean_kernel_argument_positive` | theorem | 89 | Paper 3, Sec. 4.1 | y,y' in Omega => y+y' in Omega |
| `szego_in_wallach` | theorem | 100 | Paper 3, Sec. 3.1, Remark 3.1 (`rem:wallach`) | N/2 > (N-2)/2 (Wallach membership) |
| `riesz_measure_simplifies` | theorem | 105 | Paper 3, Sec. 4.1, Remark 4.1 (`rem:wallach-critical`) | At nu=N/2, Riesz measure = Lebesgue |

### CauchySzego/Involutions.lean

The three involutions alpha, theta, delta on the tube domain.

**Reference:** Paper 3, Section 2.3 (`subsec:involutions`), Def. 2.3 and Table 1 (`tab:involutions`).

| Lean Name | Type | Line | Paper Reference | Description |
|-----------|------|------|-----------------|-------------|
| `TubeDomainPoint` | structure | 35 | Paper 3, Sec. 2.2--2.3 | Point in tube domain (x, y) with y > 0 |
| `alpha` | def | 41 | Paper 3, Def. 2.3, eq. (2.9) (`eq:alpha`) | alpha: x+iy -> -x+iy |
| `alpha_involution` | theorem | 45 | Paper 3, Sec. 2.3 | alpha^2 = id |
| `alpha_fixes_imaginary` | theorem | 50 | Paper 3, Sec. 2.3 | alpha fixes Euclidean section (x=0) |
| `deltaEigenvalue` | def | 69 | Paper 3, Cor. 7.1 (`cor:delta-eigenvalue`), eq. (7.1) | delta-eigenvalue (-1)^{k+eps(lambda)} |
| `V4Group` | structure | 76 | Paper 3, Sec. 2.3; Paper 2, Prop. 2.1 (`prop:V4`) | Klein V4 group structure |
| `dictionary_alpha` | theorem | 91 | Paper 3, Table 1 (`tab:involutions`) | alpha consistent across papers |
| `dictionary_theta` | theorem | 95 | Paper 3, Table 1 (`tab:involutions`) | theta dictionary entry |
| `dictionary_delta` | theorem | 98 | Paper 3, Table 1 (`tab:involutions`) | delta = alpha.theta dictionary |
| `delta_reverses_weight` | theorem | 109 | Paper 3, Lemma 7.1(ii) (`lem:delta-commutes`) | delta acts by m -> -m on O(2) |
| `o2_intertwiner_sign` | theorem | 112 | Paper 3, Cor. 7.1 proof, part (a) | (-1)^k * (-1)^k = 1 |

### CauchySzego/KTypes.lean

K-type lattice parametrization for SO_0(2,N).

**Reference:** Paper 3, Appendix A (`app:branching`), Sections A.1--A.3.

| Lean Name | Type | Line | Paper Reference | Description |
|-----------|------|------|-----------------|-------------|
| `KType` | structure | 29 | Paper 3, App. A.1, eq. (A.1) (`eq:peter-weyl`) | K-type (m_1, m_2) with m_2 <= m_1 |
| `KType.k` | def | 37 | Paper 3, App. A.2, eq. (A.2) (`eq:coordinate-change`) | O(2)-weight: k = m_1 + m_2 |
| `KType.absLambda` | def | 40 | Paper 3, App. A.2, eq. (A.2) (`eq:coordinate-change`) | O(N)-depth: |lambda| = m_1 - m_2 |
| `absLambda_nonneg` | theorem | 43 | Paper 3, App. A.2 | |lambda| >= 0 from dominance |
| `k_plus_absLambda` | theorem | 47 | Paper 3, App. A.4, eq. (A.9) (`eq:parity-proof`) | k + |lambda| = 2*m_1 |
| `k_minus_absLambda` | theorem | 50 | Paper 3, App. A.2 | k - |lambda| = 2*m_2 |
| `m1_from_k_lambda` | theorem | 54 | Paper 3, App. A.2, eq. (A.3) (`eq:inverse-coordinates`) | m_1 = (k+|lambda|)/2 |
| `m2_from_k_lambda` | theorem | 59 | Paper 3, App. A.2, eq. (A.3) (`eq:inverse-coordinates`) | m_2 = (k-|lambda|)/2 |
| `IsHardy` | def | 69 | Paper 3, App. A.3, eq. (A.4) (`eq:hardy-selection`) | Hardy condition: m_2 >= 0 |
| `hardy_iff_k_ge_lambda` | theorem | 72 | Paper 3, App. A.3, eq. (A.5) (`eq:hardy-inequality`) | Hardy iff k >= |lambda| |
| `l2_condition` | theorem | 78 | Paper 3, App. A.1 | L^2 condition: m_2 <= m_1 (always true) |
| `trivialKType` | def | 83 | Paper 3, Sec. 6 | Trivial representation (0,0) |
| `trivial_is_hardy` | theorem | 85 | Paper 3, Sec. 6 | (0,0) is Hardy |
| `standardKType` | def | 88 | Paper 3, Sec. 6 | Standard representation (1,0) |
| `standard_is_hardy` | theorem | 90 | Paper 3, Sec. 6 | (1,0) is Hardy |
| `standard_k` | theorem | 92 | Paper 3, Sec. 6 | k = 1 for (1,0) |
| `standard_absLambda` | theorem | 95 | Paper 3, Sec. 6 | |lambda| = 1 for (1,0) |
| `nonHardyExample` | def | 99 | Paper 3, App. A.5 (`app:counterexample`) | Non-Hardy K-type (2,-1) |
| `nonHardy_not_in_hardy` | theorem | 101 | Paper 3, App. A.5 | (2,-1) not in H^2 |
| `nonHardy_still_delta_even` | theorem | 104 | Paper 3, App. A.5 | (2,-1) is still delta-even |

### CauchySzego/DeltaEvenness.lean

**THE central theorem of Paper 3**: k + |lambda| = 2m_1 for all K-types.

**Reference:** Paper 3, Theorem 7.2 (`thm:disjointness`) and Appendix A.4 (`app:parity`).

**Sorry count: 0** -- this is the critical path and it is fully verified.

| Lean Name | Type | Line | Paper Reference | Description |
|-----------|------|------|-----------------|-------------|
| `delta_evenness` | theorem | 31 | Paper 3, Thm 7.2 (`thm:disjointness`), eq. (A.9) | **k + |lambda| = 2*m_1** |
| `k_plus_lambda_even` | theorem | 35 | Paper 3, Thm 7.2 corollary | Even(k + |lambda|) |
| `delta_eigenvalue_positive` | theorem | 40 | Paper 3, Thm 7.2 | (-1)^{k+|lambda|} = +1 |
| `no_delta_odd_Ktypes` | theorem | 53 | Paper 3, Thm 7.2 / Remark 7.3 (`rem:why-algebra-fails`) | No Odd(k + |lambda|) |
| `delta_even_without_hardy` | theorem | 61 | Paper 3, App. A.4, Remark | delta-evenness without Hardy condition |
| `half_integer_impossible` | theorem | 67 | Paper 3, App. A.4, Remark | Half-integer m_1 impossible |
| (example: trivial K-type) | example | 76 | Paper 3, Sec. 6 | (0,0): k+|lambda| = 0 |
| (example: standard K-type) | example | 80 | Paper 3, Sec. 6 | (1,0): k+|lambda| = 2 |
| (example: (2,0)) | example | 84 | Paper 3, Sec. 6 | (2,0): k+|lambda| = 4 |
| (example: (2,1)) | example | 89 | Paper 3, Sec. 6 | (2,1): k+|lambda| = 4 |
| (example: (3,2)) | example | 94 | Paper 3, Sec. 6 | (3,2): k+|lambda| = 6 |
| (example: N=10 non-Hardy) | example | 103 | Paper 3, App. A.5 (`app:counterexample`) | (2,-1): k+|lambda|=4, not Hardy |
| `scalar_lattice_uniformly_delta_even` | theorem | 121 | Paper 3, Thm 7.2, universal form | For all (m_1,m_2), Even(k+|lambda|) |

### CauchySzego/VectorValued.lean

Vector-valued extension and the trilogy resolution.

**Reference:** Paper 3, Section 5 (`sec:vector-valued`) and Section 8 (`sec:main-theorem`), Theorem 8.1 (`thm:main`).

| Lean Name | Type | Line | Paper Reference | Description |
|-----------|------|------|-----------------|-------------|
| `DeltaStructure` | inductive | 31 | Paper 3, Def. 5.1 (`def:delta-structure`) | J_tau^2 = +id (positive) or -id (negative) |
| `DeltaStructure.eigenvalue` | def | 39 | Paper 3, Def. 5.1 | +1 for positive, -1 for negative |
| `eigenvalue_sq` | theorem | 44 | Paper 3, Def. 5.1 | J_tau^2 = appropriate sign |
| `fullDeltaEigenvalue` | def | 56 | Paper 3, Lemma 5.1 (`lem:vv-delta-eigenvalue`), eq. (5.4) | Full eigenvalue: (-1)^{2m_1} * J_tau = J_tau |
| `scalar_factor_is_one` | theorem | 61 | Paper 3, Thm 7.2 | Scalar lattice factor = +1 |
| `full_eigenvalue_eq_Jtau` | theorem | 66 | Paper 3, Lemma 5.1 (`lem:vv-delta-eigenvalue`) | Full eigenvalue = J_tau |
| `positive_structure_delta_even` | theorem | 72 | Paper 3, Thm 8.1(i) | J_tau = +id => delta-even |
| `negative_structure_delta_odd` | theorem | 76 | Paper 3, Remark 5.2 (`rem:physical-reps`) | J_tau = -id => delta-odd |
| `SzegoTransferProperties` | structure | 89 | Paper 3, Thm 8.1 (`thm:main`), items (i)--(v) | Five properties of the Szego transfer |
| `reflection_positivity_holds` | theorem | 108 | Paper 3, Thm 8.1(i) | RP preserved for Hardy K-types with J_tau=+id |
| `clustering_holds` | theorem | 115 | Paper 3, Thm 8.1(iv) | Clustering for trivial K-type |
| `tensor_reps_positive` | theorem | 123 | Paper 3, Remark 5.2 (`rem:physical-reps`) | Tensor reps have positive delta-structure |
| `dirac_even_dim_positive` | theorem | 127 | Paper 3, Remark 5.2 (`rem:physical-reps`) | Even-dim Dirac: positive delta-structure |
| `odd_spinors_negative` | theorem | 131 | Paper 3, Remark 5.2 (`rem:physical-reps`) | Odd-dim spinors: negative delta-structure |
| `trilogy_resolved` | theorem | 148 | Paper 3, Thm 8.1 (`thm:main`); Paper 2, Conj. 6.1 resolved | **Trilogy resolved for bosonic fields** |

---

## Sorry Inventory

| # | Lean Name | File:Line | Paper Reference | Reason |
|---|-----------|-----------|-----------------|--------|
| 1 | `lorentzian_implies_euclidean` | `Trinity.lean:49` | Paper 1, Cor. 5.7: (1)=>(2) | Wick rotation / OS reconstruction forward direction. Requires functional-analytic machinery (distributions, analytic continuation) not available in Mathlib. |
| 2 | `lorentzian_implies_split` | `Trinity.lean:61` | Paper 1, Cor. 5.7: (1)=>(3) | Analytic continuation through extended tube T'. Requires BHW theorem and tube domain holomorphy. |

Both sorry'd results are in the functional-analytic legs of the Two-Point
Trinity. The algebraic core -- including the delta-evenness critical path
from `KTypes.lean` through `DeltaEvenness.lean` to `VectorValued.lean` --
has **zero sorrys**.

---

## Cross-Reference: Paper Theorem to Lean

For readers starting from the papers and looking for the Lean formalization:

### Paper 1 (Split Wedge)

| Paper Result | Lean Theorem | File |
|-------------|-------------|------|
| Sec. 2.2: Three involutions sigma_L/E/S | `sigmaL/E/S`, `sigmaL/E/S_involution` | `ComplexInvolutions.lean` |
| Sec. 2.2: Fixed-point characterization | `sigmaL/E/S_fixed_iff` | `ComplexInvolutions.lean` |
| Remark 2.3: Split signature verification | `split_signature_from_quadratic` | `ComplexInvolutions.lean` |
| Sec. 2.3: Non-self-duality (g_S = -29) | `counterexample_negative_inner`, `splitForwardCone_not_self_dual` | `DualCone.lean` |
| Lemma 3.2: Split tube inclusion | `lorentzian_to_split_cone` | `TubeInclusion.lean` |
| Def. 4.1: Split wedge | `splitWedge` | `Defs.lean` |
| Def. 4.3: Split reflection | `thetaS` | `Defs.lean` |
| Sec. 5, Step 1: Sum-kernel rewrite | `sum_kernel_full` | `SumKernel.lean` |
| Sec. 5, Step 5: Semigroup PD | `IsSemigroupPD` | `SumKernel.lean` |
| Cor. 5.7: Two-Point Trinity | `two_point_trinity`, `two_point_trinity_full` | `Trinity.lean` |
| Def. 6.1: Split axioms (S1)--(S8) | `SplitQFT` | `Axioms.lean` |
| Sec. 6, Step 3: Contractivity | `contractivity_bound`, `semigroup_composition` | `Contractivity.lean` |
| Sec. 6, Step 5: Euclidean coordinates | `theta_negates_tau`, `theta_preserves_sigma` | `EuclideanMetric.lean` |
| Lemma 6.6: Bridge Lemma | `bridge_factorization`, `bridge_lemma_identity` | `Bridge.lean` |
| Sec. 6, Step 6: Geometric coverage | `geometric_coverage` | `Defs.lean` |

### Paper 2 (Bridge)

| Paper Result | Lean Theorem | File |
|-------------|-------------|------|
| Def. 2.1: Real form involutions | `sigmaL`, `sigmaE`, `sigmaS` | `ComplexInvolutions.lean` |
| Prop. 2.1: V4 structure | `klein_four_identity` | `Defs.lean` |
| Sec. 3: Invariant cone / dual cone | `dualCone_subset_forwardConeClosed`, `dualCone_strictly_smaller` | `DualCone.lean` |
| Sec. 5: Contractivity bound | `contractivity_bound` | `Contractivity.lean` |
| Prop. 5.6: Transfer on delta-even sector | `scalar_lattice_uniformly_delta_even` | `DeltaEvenness.lean` |
| Conj. 6.1: Simultaneous RP | `trilogy_resolved` | `VectorValued.lean` |

### Paper 3 (Cauchy-Szego)

| Paper Result | Lean Theorem | File |
|-------------|-------------|------|
| Sec. 2.2: Spin factor, Jordan determinant | `SpinFactorElt`, `SpinFactorElt.det` | `Jordan.lean` |
| Sec. 2.2: Lorentz cone | `lorentzCone`, `det_pos_of_cone` | `Jordan.lean` |
| Sec. 2.1: Lie ball | `LieBallPoint` | `TypeIV.lean` |
| Sec. 2.2: Tube domain | `TubePoint` | `TypeIV.lean` |
| Def. 2.3: Three involutions alpha/theta/delta | `alpha`, `deltaEigenvalue` | `Involutions.lean` |
| Table 1: Involution dictionary | `dictionary_alpha/theta/delta` | `Involutions.lean` |
| Remark 3.1: Wallach set | `szego_above_wallach`, `szego_in_wallach` | `Jordan.lean`, `TypeIV.lean` |
| Sec. 4.1: Euclidean section kernel | `euclidean_section_argument` | `TypeIV.lean` |
| Def. 5.1: delta-structure | `DeltaStructure` | `VectorValued.lean` |
| Lemma 5.1: Vector-valued delta-eigenvalue | `fullDeltaEigenvalue`, `full_eigenvalue_eq_Jtau` | `VectorValued.lean` |
| App. A.1: K-type lattice | `KType` | `KTypes.lean` |
| App. A.2: Coordinate change | `KType.k`, `KType.absLambda`, `k_plus_absLambda` | `KTypes.lean` |
| App. A.3: Hardy selection rule | `IsHardy`, `hardy_iff_k_ge_lambda` | `KTypes.lean` |
| Thm 7.2: delta-evenness (main technical result) | `delta_evenness`, `delta_eigenvalue_positive` | `DeltaEvenness.lean` |
| Thm 7.2: No delta-odd K-types | `no_delta_odd_Ktypes` | `DeltaEvenness.lean` |
| Thm 7.2: Universal version | `scalar_lattice_uniformly_delta_even` | `DeltaEvenness.lean` |
| Sec. 6: d=4 verification examples | examples in `DeltaEvenness.lean:76--107` | `DeltaEvenness.lean` |
| App. A.5: Non-Hardy counterexample | `nonHardyExample`, `nonHardy_not_in_hardy` | `KTypes.lean` |
| Thm 8.1: Simultaneous RP (main theorem) | `trilogy_resolved`, `reflection_positivity_holds` | `VectorValued.lean` |
| Remark 5.2: Physical representations | `tensor_reps_positive`, `odd_spinors_negative` | `VectorValued.lean` |
