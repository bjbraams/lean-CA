/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib

/-!
# Principal theorems of lean-CA: statements

24 headline results from `ComplexAnalysis`, selected from SYNOPSIS.md, stated over Mathlib
alone: this file imports only Mathlib. Results available in Mathlib or in the TauCeti library are
not included. The supporting definitions below reproduce the library definitions; only the 24
theorem proofs are left as holes. The matching proofs are in Solution.lean, and the pair can be
checked with the Lean comparator (`comparator.json`), which confirms that each statement here is
proved by the library with only the standard axioms.

Integration and singularities (1–5), approximation (6–9), products and factorization (10–14),
univalent functions (15–17), potential theory (18–23), and boundary behavior (24). Source
alignment and automation are recorded in formalization.yaml; CREDITS.md gives detailed
comparisons with related formalizations.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology unitInterval ComplexConjugate

-- Use the same normed-field instance path as the library's narrower Mathlib imports.
attribute [-instance] instCommCStarAlgebraComplex

/-- Reset auxiliary proof sharing at the boundaries of the copied library modules. -/
elab "clear_aux_lemma_cache" : command =>
  Lean.modifyEnv fun env ↦ Lean.Meta.auxLemmasExt.modifyState env fun _ ↦ {}

namespace Complex

section
attribute [local instance 2000] IsModuleTopology.toContinuousSMul

/-- The normalized Cauchy-kernel integral of a closed curve. -/
def curveIndex {a : ℂ} (γ : Path a a) (w : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) γ

end

/-- A closed path packaged with its base point. -/
abbrev Loop := Σ a : ℂ, Path a a

/-- A cycle is a finite family of closed paths. -/
structure Cycle where
  /-- The number of paths. -/
  n : ℕ
  /-- The paths with their base points. -/
  loop : Fin n → Loop

namespace Cycle
variable (Γ : Cycle)

/-- The union of the images of a cycle's paths. -/
def range : Set ℂ := ⋃ i, Set.range (Γ.loop i).2

/-- Each constituent path has a continuously differentiable extension to the unit interval. -/
def IsC1 : Prop := ∀ i, ContDiffOn ℝ 1 (Γ.loop i).2.extend unitInterval

/-- The sum of the integrals over the constituent paths. -/
def integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ω : ℂ → ℂ →L[ℂ] F) : F := ∑ i, curveIntegral ω (Γ.loop i).2

/-- The sum of the winding indices of the constituent paths. -/
def index (w : ℂ) : ℂ := ∑ i, curveIndex (Γ.loop i).2 w
end Cycle

section BanachDefinitions
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

clear_aux_lemma_cache

/-- Residue as the limit of normalized circle integrals over shrinking positive radii.
Related scalar definition: Roman Kvasnytskyi's PR #29588; see CREDITS.md. -/
def residue (f : ℂ → F) (c : ℂ) : F :=
  limUnder (𝓝[>] (0 : ℝ)) (fun r ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(c, r), f z)

clear_aux_lemma_cache

/-- A Laurent coefficient computed on the circle of radius `r` about zero. -/
def circleLaurentCoeff (f : ℂ → F) (r : ℝ) (k : ℤ) : F :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ w in C(0, r), w ^ (-k - 1) • f w
end BanachDefinitions

/-- Uniform approximation on `K` by members of a specified set of functions. -/
def UniformApproxOn (K : Set ℂ) (S : Set (ℂ → ℂ)) (h : ℂ → ℂ) : Prop :=
  ∀ ε > 0, ∃ r ∈ S, ∀ z ∈ K, ‖h z - r z‖ ≤ ε

/-- Generators for rational functions with poles in `A`, including polynomials. -/
def rungeGenerators (A : Set ℂ) : Set (ℂ → ℂ) :=
  insert (fun z ↦ z) ((fun a ↦ fun z : ℂ ↦ (a - z)⁻¹) '' A)

clear_aux_lemma_cache

/-- The antiholomorphic part of a real-linear map along a direction.
Related operators: Will (Ziang) Li and Stefan Kebekus; see CREDITS.md. -/
def dbarAlong {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (L : E →L[ℝ] F) (v : E) : F :=
  (2 : ℂ)⁻¹ • (L v + Complex.I • L (Complex.I • v))

/-- The Weierstrass elementary factor of genus `p`.
The same factor appears in Matteo Cipollina's development; see CREDITS.md. -/
def elementaryFactor (p : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1))

/-- The canonical product using genus `n` for the `n`th factor. -/
def weierstrassProduct (a : ℕ → ℂ) (z : ℂ) : ℂ := ∏' n, elementaryFactor n (z / a n)

/-- A canonical product with a fixed genus and an arbitrary index type. -/
def canonicalProduct {ι : Type*} (k : ℕ) (a : ι → ℂ) (z : ℂ) : ℂ :=
  ∏' i, elementaryFactor k (z / a i)

/-- An explicit exponential growth bound of exponent `ρ`. -/
def HasExpRpowBound (f : ℂ → ℂ) (ρ : ℝ) : Prop :=
  ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z, ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ)

/-- Order at most `ρ`: the growth bound holds for every exponent `ρ' > ρ`. -/
def HasOrderLE (f : ℂ → ℂ) (ρ : ℝ) : Prop :=
  ∀ ρ', ρ < ρ' → HasExpRpowBound f ρ'

/-- The normalized Blaschke factor. -/
def blaschkeFactor (a z : ℂ) : ℂ := (‖a‖ / a) * (a - z) / (1 - conj a * z)

/-- The product of the Blaschke factors of an indexed family. -/
def blaschkeProduct {ι : Type*} (a : ι → ℂ) (z : ℂ) : ℂ :=
  ∏' i, blaschkeFactor (a i) z

/-- The submean inequality and circle integrability for all sufficiently small radii. -/
def HasSubmeanAt (u : ℂ → ℝ) (a : ℂ) : Prop :=
  ∀ᶠ r in 𝓝[>] (0 : ℝ), CircleIntegrable u a r ∧ u a ≤ Real.circleAverage u a r

/-- Real-valued subharmonicity: upper semicontinuity and the local submean property. -/
def SubharmonicOn (u : ℂ → ℝ) (U : Set ℂ) : Prop :=
  UpperSemicontinuousOn u U ∧ ∀ a ∈ U, HasSubmeanAt u a

/-- The lacunary power series with exponents `2 ^ n`. -/
def lacunary (z : ℂ) : ℂ := ∑' n : ℕ, z ^ (2 ^ n)

end Complex

-- Restore the full Mathlib instance set for the theorem statements.
attribute [instance] instCommCStarAlgebraComplex

namespace LeanCA

universe u_1

/-- 1. Primitives on simply connected open sets, with prescribed value; Banach-valued.
Related covering-space approaches: Beffara (Curvint) and Xu (PR #26950). See CREDITS.md.
Library: `DifferentiableOn.exists_primitive_of_isSimplyConnected`. -/
theorem primitives :
    ∀ {F : Type u_1} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {U : Set ℂ} {f : ℂ → F},
    DifferentiableOn ℂ f U →
    IsOpen U → IsSimplyConnected U → ∀ (z₀ : ℂ) (v : F), ∃ (P : ℂ → F), P z₀ = v ∧ ∀ z ∈ U,
    HasDerivAt P (f z) z := by sorry

/-- 2. The residue theorem for a cycle and finitely many isolated singularities of any type.
Related scalar residues: Kvasnytskyi; rectangular simple-pole cases: PNT+ and Tan. See
CREDITS.md.
Library: `Complex.Cycle.integral_eq_sum_index_smul_residue`. -/
theorem residue_theorem :
    ∀ {F : Type u_1} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] (Γ : Complex.Cycle) {U : Set ℂ},
    IsOpen U →
    ∀ (S : Finset ℂ),
    Γ.IsC1 →
    Γ.range ⊆ U \ ↑S →
    (∀ w ∉ U, Γ.index w = 0) →
    ∀ {f : ℂ → F},
    DifferentiableOn ℂ f (U \ ↑S) →
    (Γ.integral fun (w : ℂ) ↦ ContinuousLinearMap.toSpanSingleton ℂ (f w)) =
    ∑ a ∈ S, (2 * ↑Real.pi * Complex.I * Γ.index a) • Complex.residue f a := by sorry

/-- 3. The bilateral Laurent expansion on an annulus; Banach-valued.
Library: `Complex.hasSum_circleLaurentCoeff_annulus`. -/
theorem laurent_expansion :
    ∀ {F : Type u_1} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {f : ℂ → F} {r R : ℝ},
    0 < r →
    ∀ {z : ℂ},
    r < ‖z‖ →
    ‖z‖ < R →
    AnalyticOnNhd ℂ f (Metric.closedBall 0 R \ Metric.ball 0 r) →
    HasSum (fun (k : ℤ) ↦ z ^ k • Complex.circleLaurentCoeff f r k) (f z) := by sorry

/-- 4. Casorati–Weierstrass: every punctured neighborhood of an essential singularity has dense
image.
Library: `Complex.dense_image_of_not_meromorphicAt`. -/
theorem casorati_weierstrass :
    ∀ {f : ℂ → ℂ} {c : ℂ},
    (∀ᶠ (z : ℂ) in nhdsWithin c {c}ᶜ, AnalyticAt ℂ f z) →
    ¬MeromorphicAt f c → ∀ {s : Set ℂ}, s ∈ nhdsWithin c {c}ᶜ → Dense (f '' s) := by sorry

/-- 5. An isolated singularity is removable, a pole, or has dense image on each punctured
neighborhood.
Library: `Complex.isolatedSingularity_trichotomy`. -/
theorem isolated_singularity :
    ∀ {f : ℂ → ℂ} {c : ℂ},
    (∀ᶠ (z : ℂ) in nhdsWithin c {c}ᶜ, AnalyticAt ℂ f z) →
    (∃ (g : ℂ → ℂ), AnalyticAt ℂ g c ∧ f =ᶠ[nhdsWithin c {c}ᶜ] g) ∨
    Filter.Tendsto (fun (z : ℂ) ↦ ‖f z‖) (nhdsWithin c {c}ᶜ) Filter.atTop ∨ ∀ s ∈ nhdsWithin c
    {c}ᶜ, Dense (f '' s) := by sorry

/-- 6. Runge approximation with poles in a set meeting every bounded complementary component.
Library: `Complex.runge`. -/
theorem runge :
    ∀ {K : Set ℂ},
    IsCompact K →
    ∀ {A : Set ℂ},
    A ∩ K = ∅ →
    (∀ w ∉ K, Bornology.IsBounded (connectedComponentIn Kᶜ w) → ∃ a ∈ A, a ∈ connectedComponentIn
    Kᶜ w) →
    ∀ {U : Set ℂ},
    IsOpen U →
    K ⊆ U →
    ∀ {f : ℂ → ℂ},
    DifferentiableOn ℂ f U → Complex.UniformApproxOn K (↑(Algebra.adjoin ℂ
    (Complex.rungeGenerators A))) f := by sorry

/-- 7. Polynomial Runge approximation on a compact set with connected complement.
Library: `Complex.exists_polynomial_approx_of_isPreconnected_compl`. -/
theorem runge_polynomial :
    ∀ {K : Set ℂ},
    IsCompact K →
    IsPreconnected Kᶜ →
    ∀ {U : Set ℂ},
    IsOpen U →
    K ⊆ U →
    ∀ {f : ℂ → ℂ},
    DifferentiableOn ℂ f U → ∀ {ε : ℝ}, 0 < ε → ∃ (p : Polynomial ℂ), ∀ z ∈ K, ‖f z -
    Polynomial.eval z p‖ ≤ ε := by sorry

/-- 8. Mittag–Leffler on an arbitrary open set for a set of singularities with no accumulation
point in the open set (every point of `U` has positive distance from the other singularities).
Library: `Complex.mittagLeffler_of_forall_le_dist`. -/
theorem mittag_leffler :
    ∀ {U : Set ℂ},
    IsOpen U →
    ∀ {S : Set ℂ},
    S ⊆ U →
    (∀ z ∈ U, ∃ ε > 0, ∀ w ∈ S, w ≠ z → ε ≤ dist w z) →
    ∀ {P : ℂ → ℂ → ℂ},
    (∀ a ∈ S, DifferentiableOn ℂ (P a) {a}ᶜ) →
    ∃ (f : ℂ → ℂ),
    DifferentiableOn ℂ f (U \ S) ∧
    ∀ a ∈ S, ∃ (g : ℂ → ℂ), AnalyticAt ℂ g a ∧
        f =ᶠ[nhdsWithin a {a}ᶜ] fun (z : ℂ) ↦ P a z + g z := by sorry

/-- 9. The compact-support C¹ Cauchy–Pompeiu identity; Banach-valued.
Related scalar theorem: Will (Ziang) Li (RiemannDynamics). See CREDITS.md.
Library: `Complex.integral_inv_smul_dbarAlong_fderiv`. -/
theorem cauchy_pompeiu :
    ∀ {F : Type u_1} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {φ : ℂ → F},
    ContDiff ℝ 1 φ → HasCompactSupport φ → ∫ (w : ℂ), w⁻¹ • Complex.dbarAlong (fderiv ℝ φ w) 1 =
    -(↑Real.pi • φ 0) := by sorry

/-- 10. The Weierstrass product is entire and has precisely the prescribed zeros, with
multiplicities.
Related elementary factors: Matteo Cipollina’s Hadamard development. See CREDITS.md.
Library: `Complex.analyticOrderAt_weierstrassProduct`. -/
theorem weierstrass_product :
    ∀ {a : ℕ → ℂ}, (∀ n, a n ≠ 0) →
    Filter.Tendsto (fun n ↦ ‖a n‖) Filter.atTop Filter.atTop →
    Differentiable ℂ (Complex.weierstrassProduct a) ∧
    ∀ w : ℂ, analyticOrderAt (Complex.weierstrassProduct a) w =
    ({n : ℕ | a n = w}.ncard : ℕ∞) := by sorry

/-- 11. Weierstrass factorization for a nonzero zero sequence tending to infinity, counted with
multiplicity.
Library: `Complex.exists_exp_mul_weierstrassProduct`. -/
theorem weierstrass_factorization :
    ∀ {a : ℕ → ℂ} {f : ℂ → ℂ}, Differentiable ℂ f →
    (∀ n, a n ≠ 0) → Filter.Tendsto (fun n ↦ ‖a n‖) Filter.atTop Filter.atTop →
    (∀ w : ℂ, analyticOrderAt f w = ({n : ℕ | a n = w}.ncard : ℕ∞)) →
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
    ∀ z : ℂ, f z = Complex.exp (g z) * Complex.weierstrassProduct a z := by sorry

/-- 12. Hadamard factorization for entire functions of order at most `ρ`, with polynomial degree
at most the genus.
Related factorization theorem: Matteo Cipollina (PrimeNumberTheoremAnd fork). See CREDITS.md.
Library: `Complex.exists_hadamard_factorization`. -/
theorem hadamard :
    ∀ {f : ℂ → ℂ},
    Differentiable ℂ f →
    (∃ (z : ℂ), f z ≠ 0) →
    ∀ {ρ : ℝ},
    Complex.HasOrderLE f ρ →
    ∀ {k : ℕ},
    ρ < ↑k + 1 →
    ∃ (ι : Type) (_ : Countable ι) (a : ι → ℂ) (m : ℕ) (P : Polynomial ℂ),
    (∀ (i : ι), a i ≠ 0) ∧
    Filter.Tendsto (fun (i : ι) ↦ ‖a i‖) Filter.cofinite Filter.atTop ∧
    (∀ (i : ι), f (a i) = 0) ∧
    (Summable fun (i : ι) ↦ ‖a i‖⁻¹ ^ (k + 1)) ∧
    P.natDegree ≤ k ∧
    ∀ (z : ℂ), f z = Complex.exp (Polynomial.eval z P) * z ^ m *
        Complex.canonicalProduct k a z := by sorry

/-- 13. The multiplicity-weighted Blaschke condition for nonzero zeros of a bounded nontrivial
holomorphic function.
Library: `Complex.summable_analyticOrderAt_toNat_mul_one_sub_norm_of_bounded`. -/
theorem blaschke_condition :
    ∀ {f : ℂ → ℂ},
    DifferentiableOn ℂ f (Metric.ball 0 1) →
    ∀ {M : ℝ},
    (∀ z ∈ Metric.ball 0 1, ‖f z‖ ≤ M) →
    (∃ z ∈ Metric.ball 0 1, f z ≠ 0) →
    Summable fun (w : { w : ℂ // ‖w‖ < 1 ∧ f w = 0 ∧ w ≠ 0 }) ↦
        ((analyticOrderAt f (w : ℂ)).toNat : ℝ) *
    (1 - ‖(w : ℂ)‖) := by sorry

/-- 14. Riesz factorization into an origin power, a Blaschke product and a zero-free bounded
holomorphic factor.
Library: `Complex.exists_rieszFactorization`. -/
theorem riesz_factorization :
    ∀ {f : ℂ → ℂ},
    DifferentiableOn ℂ f (Metric.ball 0 1) →
    ∀ {M : ℝ},
    (∀ z ∈ Metric.ball 0 1, ‖f z‖ ≤ M) →
    (∃ z ∈ Metric.ball 0 1, f z ≠ 0) →
    ∃ (ι : Type) (_ : Countable ι) (a : ι → ℂ) (m : ℕ) (g : ℂ → ℂ),
    (∀ (i : ι), a i ≠ 0) ∧
    (∀ (i : ι), ‖a i‖ < 1) ∧
    (Summable fun (i : ι) ↦ 1 - ‖a i‖) ∧
    (∀ (i : ι), f (a i) = 0) ∧
    DifferentiableOn ℂ g (Metric.ball 0 1) ∧
    (∀ z ∈ Metric.ball 0 1, g z ≠ 0) ∧
    (∀ z ∈ Metric.ball 0 1, ‖g z‖ ≤ M) ∧
    ∀ z ∈ Metric.ball 0 1, f z = z ^ m * Complex.blaschkeProduct a z * g z := by sorry

/-- 15. Koebe’s quarter theorem for a normalized univalent function.
Library: `Complex.ball_subset_image_of_injOn`. -/
theorem koebe_quarter :
    ∀ {f : ℂ → ℂ},
    DifferentiableOn ℂ f (Metric.ball 0 1) →
    Set.InjOn f (Metric.ball 0 1) → f 0 = 0 → deriv f 0 = 1 → Metric.ball 0 (1 / 4) ⊆ f ''
    Metric.ball 0 1 := by sorry

/-- 16. The two-sided Koebe distortion bound for the derivative of a univalent function.
Library: `Complex.distortion_le_of_class_S`. -/
theorem koebe_distortion :
    ∀ {f : ℂ → ℂ},
    DifferentiableOn ℂ f (Metric.ball 0 1) →
    Set.InjOn f (Metric.ball 0 1) →
    deriv f 0 = 1 →
    ∀ {z₀ : ℂ},
    z₀ ∈ Metric.ball 0 1 → (1 - ‖z₀‖) / (1 + ‖z₀‖) ^ 3 ≤ ‖deriv f z₀‖ ∧ ‖deriv f z₀‖ ≤ (1 + ‖z₀‖)
    / (1 - ‖z₀‖) ^ 3 := by sorry

/-- 17. The upper Koebe growth bound for a normalized univalent function.
Library: `Complex.norm_le_div_one_sub_sq_of_class_S`. -/
theorem koebe_growth :
    ∀ {f : ℂ → ℂ},
    DifferentiableOn ℂ f (Metric.ball 0 1) →
    Set.InjOn f (Metric.ball 0 1) →
    f 0 = 0 → deriv f 0 = 1 → ∀ {z₀ : ℂ},
        z₀ ∈ Metric.ball 0 1 → ‖f z₀‖ ≤ ‖z₀‖ / (1 - ‖z₀‖) ^ 2 := by sorry

/-- 18. The Dirichlet problem on a disc with arbitrary continuous boundary data.
Library: `Complex.exists_harmonicContOnCl_eqOn_sphere`. -/
theorem dirichlet_disc :
    ∀ {c : ℂ} {R : ℝ} {g : ℂ → ℝ},
    0 < R →
    ContinuousOn g (Metric.sphere c R) →
    ∃ (u : ℂ → ℝ), InnerProductSpace.HarmonicContOnCl u (Metric.ball c R) ∧ Set.EqOn u g
    (Metric.sphere c R) := by sorry

/-- 19. Harnack convergence for an increasing harmonic sequence bounded above at one point.
Library: `Complex.exists_harmonicOnNhd_tendstoLocallyUniformlyOn_of_monotone`. -/
theorem harnack_convergence :
    ∀ {U : Set ℂ},
    IsOpen U →
    IsPreconnected U →
    ∀ {u : ℕ → ℂ → ℝ},
    (∀ (n : ℕ), InnerProductSpace.HarmonicOnNhd (u n) U) →
    (∀ z ∈ U, Monotone fun (n : ℕ) ↦ u n z) →
    ∀ {z₀ : ℂ},
    z₀ ∈ U →
    BddAbove (Set.range fun (n : ℕ) ↦ u n z₀) →
    ∃ (f : ℂ → ℝ), InnerProductSpace.HarmonicOnNhd f U ∧ TendstoLocallyUniformlyOn u f
    Filter.atTop U := by sorry

/-- 20. The strong maximum principle for real-valued subharmonic functions.
Library: `Complex.SubharmonicOn.eqOn_const_of_isMaxOn`. -/
theorem subharmonic_maximum :
    ∀ {u : ℂ → ℝ} {U : Set ℂ} {a : ℂ},
    IsOpen U → IsPreconnected U → Complex.SubharmonicOn u U → a ∈ U → (∀ z ∈ U, u z ≤ u a) → ∀ z ∈
    U, u z = u a := by sorry

/-- 21. A C² function with nonnegative Laplacian is subharmonic.
Library: `Complex.subharmonicOn_of_laplacian_nonneg`. -/
theorem subharmonic_laplacian :
    ∀ {g : ℂ → ℝ} {U : Set ℂ},
    IsOpen U → ContDiffOn ℝ 2 g U → (∀ t ∈ U, 0 ≤ Laplacian.laplacian g t) → Complex.SubharmonicOn
    g U := by sorry

/-- 22. The Dirichlet problem on bounded open sets satisfying an exterior-disc condition at every
boundary point.
Library: `Complex.exists_harmonicOnNhd_tendsto_of_exteriorDisc`. -/
theorem dirichlet_exterior_disc :
    ∀ {U : Set ℂ} {g : ℂ → ℝ},
    IsOpen U →
    Bornology.IsBounded U →
    (∀ ζ ∈ frontier U, ∃ (c : ℂ) (R : ℝ), 0 < R ∧ Metric.closedBall c R ∩ closure U = {ζ}) →
    ContinuousOn g (frontier U) →
    ∃ (u : ℂ → ℝ),
    InnerProductSpace.HarmonicOnNhd u U ∧ ∀ ζ ∈ frontier U, Filter.Tendsto u (nhdsWithin ζ U)
    (nhds (g ζ)) := by sorry

/-- 23. A nonnegative Green function with logarithmic singularity and zero boundary limits on such a
domain.
Library: `Complex.exists_greenFunction`. -/
theorem green_function :
    ∀ {U : Set ℂ},
    IsOpen U →
    Bornology.IsBounded U →
    (∀ ζ ∈ frontier U, ∃ (c : ℂ) (R : ℝ), 0 < R ∧ Metric.closedBall c R ∩ closure U = {ζ}) →
    ∀ {w : ℂ},
    w ∈ U →
    ∃ (G : ℂ → ℝ),
    InnerProductSpace.HarmonicOnNhd (fun (z : ℂ) ↦ G z + Real.log ‖z - w‖) U ∧
    (∀ ζ ∈ frontier U, Filter.Tendsto G (nhdsWithin ζ U) (nhds 0)) ∧
      ∀ z ∈ U, z ≠ w → 0 ≤ G z := by sorry

/-- 24. The lacunary series with exponents `2 ^ n` has no continuous extension across any point of
the unit circle.
Library: `Complex.not_exists_continuousOn_extension_lacunary`. -/
theorem natural_boundary :
    ∀ {ζ₀ : ℂ},
    ‖ζ₀‖ = 1 →
    ∀ {ε : ℝ},
    0 < ε →
    ¬∃ (g : ℂ → ℂ),
    ContinuousOn g (Metric.ball ζ₀ ε) ∧ Set.EqOn Complex.lacunary g (Metric.ball ζ₀ ε ∩
    Metric.ball 0 1) := by sorry

end LeanCA
