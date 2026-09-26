/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
import ComplexAnalysis

/-!
# Principal theorems of lean-CA: proofs

Proofs of the 45 statements in Challenge.lean, using the substantive development in
ComplexAnalysis. The declarations have the same names and types as the challenge; the two
modules are compared in separate environments and must not be imported together.
The Weierstrass statements use set cardinality to avoid proof-dependent finite-set notation.
See formalization.yaml for source alignment and CREDITS.md for related formalizations.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology unitInterval ComplexConjugate

universe u_1

namespace LeanCA

/-- 1. Primitives on simply connected open sets, with prescribed value; Banach-valued.
Related covering-space approaches: Beffara (Curvint) and Xu (PR #26950). See CREDITS.md.
Library: `DifferentiableOn.exists_primitive_of_isSimplyConnected`. -/
theorem primitives :
    ∀ {F : Type u_1} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {U : Set ℂ} {f : ℂ → F},
    DifferentiableOn ℂ f U →
    IsOpen U → IsSimplyConnected U → ∀ (z₀ : ℂ) (v : F), ∃ (P : ℂ → F), P z₀ = v ∧ ∀ z ∈ U,
    HasDerivAt P (f z) z := by
  exact @DifferentiableOn.exists_primitive_of_isSimplyConnected

/-- 2. A normalized holomorphic logarithm of a nonvanishing function on a simply connected domain.
Related disc theorem: Geoffrey Irving (ray). See CREDITS.md.
Library: `Complex.exists_analyticOnNhd_logBranch_eq`. -/
theorem logarithm :
    ∀ {U : Set ℂ},
    IsOpen U →
    IsSimplyConnected U →
    ∀ {g : ℂ → ℂ},
    DifferentiableOn ℂ g U →
    (∀ z ∈ U, g z ≠ 0) →
    ∀ {z₀ w₀ : ℂ},
    z₀ ∈ U →
    Complex.exp w₀ = g z₀ → ∃ (L : ℂ → ℂ), AnalyticOnNhd ℂ L U ∧ Set.EqOn (Complex.exp ∘ L) g U ∧
    L z₀ = w₀ := by
  exact @Complex.exists_analyticOnNhd_logBranch_eq

/-- 3. The Cauchy formula for every iterated derivative at any interior point of a disc.
Related derivative formulas: JJYYY-JJY and ajirving (PR #43100). See CREDITS.md.
Library: `DiffContOnCl.iteratedDeriv_eq_circleIntegral_sub_zpow_smul`. -/
theorem cauchy_derivatives :
    ∀ {E : Type u_1} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {c : ℂ} {R : ℝ} {f : ℂ → E},
    DiffContOnCl ℂ f (Metric.ball c R) →
    0 < R →
    ∀ (n : ℕ) {w : ℂ},
    w ∈ Metric.ball c R →
    iteratedDeriv n f w =
    (↑n.factorial * (2 * ↑Real.pi * Complex.I)⁻¹) • ∮ (s : ℂ) in C(c, R), (s - w) ^ (-((n : ℤ) + 1)) •
    f s := by
  exact @DiffContOnCl.iteratedDeriv_eq_circleIntegral_sub_zpow_smul

/-- 4. The winding index of a closed C¹ curve avoiding the evaluation point is an integer.
Library: `Complex.exists_int_curveIndex`. -/
theorem winding_integer :
    ∀ {a w : ℂ} (γ : Path a a),
    ContDiffOn ℝ 1 (⇑γ.extend) unitInterval → (∀ (t : ↑unitInterval), γ t ≠ w) → ∃ (n : ℤ),
    Complex.curveIndex γ w = ↑n := by
  exact @Complex.exists_int_curveIndex

/-- 5. Cauchy’s theorem for cycles homologous to zero in an open set; Banach-valued.
Library: `Complex.Cycle.integral_eq_zero`. -/
theorem cauchy_theorem :
    ∀ {F : Type u_1} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (Γ : Complex.Cycle) {U : Set ℂ},
    IsOpen U →
    Γ.IsC1 →
    Γ.range ⊆ U →
    (∀ w ∉ U, Γ.index w = 0) →
    ∀ {f : ℂ → F},
    DifferentiableOn ℂ f U → (Γ.integral fun (w : ℂ) ↦ ContinuousLinearMap.toSpanSingleton ℂ (f
    w)) = 0 := by
  exact @Complex.Cycle.integral_eq_zero

/-- 6. The index-weighted Cauchy formula for cycles homologous to zero; Banach-valued.
Library: `Complex.Cycle.integral_sub_inv_smul_eq_index_smul`. -/
theorem cauchy_formula :
    ∀ {F : Type u_1} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] (Γ : Complex.Cycle) {U : Set ℂ},
    IsOpen U →
    Γ.IsC1 →
    Γ.range ⊆ U →
    (∀ w ∉ U, Γ.index w = 0) →
    ∀ {f : ℂ → F},
    DifferentiableOn ℂ f U →
    ∀ {z : ℂ},
    z ∈ U →
    z ∉ Γ.range →
    (Γ.integral fun (w : ℂ) ↦ ContinuousLinearMap.toSpanSingleton ℂ ((w - z)⁻¹ • f w)) =
    (2 * ↑Real.pi * Complex.I * Γ.index z) • f z := by
  exact @Complex.Cycle.integral_sub_inv_smul_eq_index_smul

/-- 7. The residue theorem for a cycle and finitely many isolated singularities of any type.
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
    ∑ a ∈ S, (2 * ↑Real.pi * Complex.I * Γ.index a) • Complex.residue f a := by
  exact @Complex.Cycle.integral_eq_sum_index_smul_residue

/-- 8. The bilateral Laurent expansion on an annulus; Banach-valued.
Library: `Complex.hasSum_circleLaurentCoeff_annulus`. -/
theorem laurent_expansion :
    ∀ {F : Type u_1} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {f : ℂ → F} {r R : ℝ},
    0 < r →
    ∀ {z : ℂ},
    r < ‖z‖ →
    ‖z‖ < R →
    AnalyticOnNhd ℂ f (Metric.closedBall 0 R \ Metric.ball 0 r) →
    HasSum (fun (k : ℤ) ↦ z ^ k • Complex.circleLaurentCoeff f r k) (f z) := by
  exact @Complex.hasSum_circleLaurentCoeff_annulus

/-- 9. The residue of a holomorphic numerator divided by an arbitrary positive power.
Related simple-pole theorem: Roman Kvasnytskyi (PR #29588). See CREDITS.md.
Library: `Complex.residue_sub_zpow_smul`. -/
theorem residue_higher_pole :
    ∀ {F : Type u_1} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {f : ℂ → F} {c : ℂ},
    AnalyticAt ℂ f c →
    ∀ (n : ℕ), Complex.residue (fun (z : ℂ) ↦ (z - c) ^ (-((n : ℤ) + 1)) • f z) c = (n.factorial : ℂ)⁻¹ •
    iteratedDeriv n f c := by
  exact @Complex.residue_sub_zpow_smul

/-- 10. The argument principle on a disc, counting meromorphic zeros minus poles.
Related holomorphic argument principle: Yury Kudryashov (PR #33505). See CREDITS.md.
Library: `Complex.circleIntegral_logDeriv_eq_sum_divisor`. -/
theorem argument_principle :
    ∀ {f : ℂ → ℂ} {c : ℂ} {R : ℝ},
    0 < R →
    MeromorphicOn f (Metric.closedBall c R) →
    (∀ z ∈ Metric.closedBall c R, meromorphicOrderAt f z ≠ ⊤) →
    (∀ z ∈ Metric.sphere c R, meromorphicOrderAt f z = 0) →
    ∮ (z : ℂ) in C(c, R), logDeriv f z =
    2 * ↑Real.pi * Complex.I * ∑ᶠ (z : ℂ), ↑((MeromorphicOn.divisor f (Metric.closedBall c R)) z) := by
  exact @Complex.circleIntegral_logDeriv_eq_sum_divisor

/-- 11. Rouché’s theorem on a disc: a strict boundary inequality preserves the total divisor.
Library: `Complex.sum_divisor_eq_of_norm_sub_lt`. -/
theorem rouche :
    ∀ {f g : ℂ → ℂ} {c : ℂ} {R : ℝ},
    0 < R →
    AnalyticOnNhd ℂ f (Metric.closedBall c R) →
    AnalyticOnNhd ℂ g (Metric.closedBall c R) →
    (∀ z ∈ Metric.sphere c R, ‖g z - f z‖ < ‖f z‖) →
    ∑ᶠ (z : ℂ), (MeromorphicOn.divisor f (Metric.closedBall c R)) z =
    ∑ᶠ (z : ℂ), (MeromorphicOn.divisor g (Metric.closedBall c R)) z := by
  exact @Complex.sum_divisor_eq_of_norm_sub_lt

/-- 12. Hurwitz: a locally uniform limit of nonvanishing holomorphic functions is zero or
nonvanishing.
Related results: Vincent Beffara (RMT4) and Yury Kudryashov (PR #33505). See CREDITS.md.
Library: `Complex.eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn`. -/
theorem hurwitz_zero_free :
    ∀ {ι : Type u_1} {l : Filter ι} [l.NeBot]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ},
    IsOpen U →
    IsPreconnected U →
    (∀ᶠ (n : ι) in l, DifferentiableOn ℂ (F n) U) →
    (∀ᶠ (n : ι) in l, ∀ z ∈ U, F n z ≠ 0) → TendstoLocallyUniformlyOn F f l U → Set.EqOn f 0 U ∨ ∀
    z ∈ U, f z ≠ 0 := by
  exact @Complex.eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn

/-- 13. Hurwitz: a locally uniform limit of injective holomorphic functions is constant or
injective.
Related results: Vincent Beffara (RMT4) and Yury Kudryashov (PR #33505). See CREDITS.md.
Library: `Complex.eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn`. -/
theorem hurwitz_injective :
    ∀ {ι : Type u_1} {l : Filter ι} [l.NeBot] {F : ι → ℂ → ℂ}
    {f : ℂ → ℂ} {U : Set ℂ},
    IsOpen U →
    IsPreconnected U →
    (∀ᶠ (n : ι) in l, DifferentiableOn ℂ (F n) U) →
    (∀ᶠ (n : ι) in l, Set.InjOn (F n) U) →
    TendstoLocallyUniformlyOn F f l U → (∃ (v : ℂ), Set.EqOn f (fun (_x : ℂ) ↦ v) U) ∨ Set.InjOn f
    U := by
  exact @Complex.eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn

/-- 14. Casorati–Weierstrass: every punctured neighborhood of an essential singularity has dense
image.
Library: `Complex.dense_image_of_not_meromorphicAt`. -/
theorem casorati_weierstrass :
    ∀ {f : ℂ → ℂ} {c : ℂ},
    (∀ᶠ (z : ℂ) in nhdsWithin c {c}ᶜ, AnalyticAt ℂ f z) →
    ¬MeromorphicAt f c → ∀ {s : Set ℂ}, s ∈ nhdsWithin c {c}ᶜ → Dense (f '' s) := by
  exact @Complex.dense_image_of_not_meromorphicAt

/-- 15. An isolated singularity is removable, a pole, or has dense image on each punctured
neighborhood.
Library: `Complex.isolatedSingularity_trichotomy`. -/
theorem isolated_singularity :
    ∀ {f : ℂ → ℂ} {c : ℂ},
    (∀ᶠ (z : ℂ) in nhdsWithin c {c}ᶜ, AnalyticAt ℂ f z) →
    (∃ (g : ℂ → ℂ), AnalyticAt ℂ g c ∧ f =ᶠ[nhdsWithin c {c}ᶜ] g) ∨
    Filter.Tendsto (fun (z : ℂ) ↦ ‖f z‖) (nhdsWithin c {c}ᶜ) Filter.atTop ∨ ∀ s ∈ nhdsWithin c
    {c}ᶜ, Dense (f '' s) := by
  exact @Complex.isolatedSingularity_trichotomy

/-- 16. Local mapping with multiplicity: nearby noncritical values have exactly `m` simple
preimages.
Library: `Complex.exists_forall_ncard_preimage_eq`. -/
theorem local_mapping :
    ∀ {f : ℂ → ℂ} {a : ℂ},
    AnalyticAt ℂ f a →
    ∀ {m : ℕ},
    analyticOrderAt (fun (z : ℂ) ↦ f z - f a) a = ↑m →
    ∃ ε₀ > 0,
    ∀ (ε : ℝ),
    0 < ε →
    ε ≤ ε₀ →
    ∃ δ > 0,
    ∀ (w : ℂ),
    w ≠ f a →
    ‖w - f a‖ < δ →
    {z : ℂ | z ∈ Metric.ball a ε ∧ f z = w}.Finite ∧
    {z : ℂ | z ∈ Metric.ball a ε ∧ f z = w}.ncard = m ∧
    ∀ z ∈ Metric.ball a ε, f z = w → deriv f z ≠ 0 := by
  exact @Complex.exists_forall_ncard_preimage_eq

/-- 17. Montel: compact-local boundedness gives a holomorphic subsequential limit;
finite-dimensional values.
Related scalar results: Beffara (RMT4) and phasetr/ising-model contributors. See CREDITS.md.
Library: `Complex.exists_subseq_tendstoLocallyUniformlyOn_of_bounded_on_compacts`. -/
theorem montel :
    ∀ {F : Type u_1} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] [FiniteDimensional ℂ F] {U : Set ℂ},
    IsOpen U →
    ∀ {f : ℕ → ℂ → F},
    (∀ (n : ℕ), DifferentiableOn ℂ (f n) U) →
    (∀ K ⊆ U, IsCompact K → ∃ (M : ℝ), ∀ (n : ℕ), ∀ z ∈ K, ‖f n z‖ ≤ M) →
    ∃ (g : ℂ → F) (φ : ℕ → ℕ),
    StrictMono φ ∧ DifferentiableOn ℂ g U ∧ TendstoLocallyUniformlyOn (fun (n : ℕ) ↦ f (φ n)) g
    Filter.atTop U := by
  exact @Complex.exists_subseq_tendstoLocallyUniformlyOn_of_bounded_on_compacts

/-- 18. Vitali–Porter: convergence on a set with an interior accumulation point implies local
uniform convergence.
Related scalar theorem: phasetr/ising-model contributors. See CREDITS.md.
Library: `Complex.exists_tendstoLocallyUniformlyOn_of_forall_exists_tendsto`. -/
theorem vitali :
    ∀ {F : Type u_1} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] [FiniteDimensional ℂ F] {D V : Set ℂ},
    IsOpen D →
    IsPreconnected D →
    ∀ {f : ℕ → ℂ → F},
    (∀ (n : ℕ), DifferentiableOn ℂ (f n) D) →
    (∀ K ⊆ D, IsCompact K → ∃ (M : ℝ), ∀ (n : ℕ), ∀ z ∈ K, ‖f n z‖ ≤ M) →
    V ⊆ D →
    ∀ {a : ℂ},
    a ∈ D →
    a ∈ closure (V \ {a}) →
    (∀ z ∈ V, ∃ (y : F), Filter.Tendsto (fun (n : ℕ) ↦ f n z) Filter.atTop (nhds y)) →
    ∃ (g : ℂ → F), DifferentiableOn ℂ g D ∧ TendstoLocallyUniformlyOn f g Filter.atTop D := by
  exact @Complex.exists_tendstoLocallyUniformlyOn_of_forall_exists_tendsto

/-- 19. Locally uniform convergence of holomorphic functions implies pointwise convergence of every
derivative.
Library: `Complex.tendsto_iteratedDeriv_of_tendstoLocallyUniformlyOn`. -/
theorem derivative_convergence :
    ∀ {V : Set ℂ},
    IsOpen V →
    ∀ (j : ℕ) (F : ℕ → ℂ → ℂ) (f' : ℂ → ℂ),
    TendstoLocallyUniformlyOn F f' Filter.atTop V →
    (∀ (n : ℕ), DifferentiableOn ℂ (F n) V) →
    ∀ {x : ℂ},
    x ∈ V → Filter.Tendsto (fun (n : ℕ) ↦ iteratedDeriv j (F n) x) Filter.atTop (nhds
    (iteratedDeriv j f' x)) := by
  exact @Complex.tendsto_iteratedDeriv_of_tendstoLocallyUniformlyOn

/-- 20. Runge approximation with poles in a set meeting every bounded complementary component.
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
    (Complex.rungeGenerators A))) f := by
  intro K hK A hAK hA U hU hKU f hf
  exact Complex.runge hK (Set.disjoint_iff_inter_eq_empty.mpr hAK) hA hU hKU hf

/-- 21. Polynomial Runge approximation on a compact set with connected complement.
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
    Polynomial.eval z p‖ ≤ ε := by
  exact @Complex.exists_polynomial_approx_of_isPreconnected_compl

/-- 22. Mittag–Leffler on an arbitrary open set for a set of singularities with no accumulation
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
    ∀ a ∈ S, ∃ (g : ℂ → ℂ), AnalyticAt ℂ g a ∧ f =ᶠ[nhdsWithin a {a}ᶜ] fun (z : ℂ) ↦ P a z + g z := by
  exact @Complex.mittagLeffler_of_forall_le_dist

/-- 23. The compact-support C¹ Cauchy–Pompeiu identity; Banach-valued.
Related scalar theorem: Will (Ziang) Li (RiemannDynamics). See CREDITS.md.
Library: `Complex.integral_inv_smul_dbarAlong_fderiv`. -/
theorem cauchy_pompeiu :
    ∀ {F : Type u_1} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {φ : ℂ → F},
    ContDiff ℝ 1 φ → HasCompactSupport φ → ∫ (w : ℂ), w⁻¹ • Complex.dbarAlong (fderiv ℝ φ w) 1 =
    -(↑Real.pi • φ 0) := by
  exact @Complex.integral_inv_smul_dbarAlong_fderiv

/-- 24. The Weierstrass product is entire and has precisely the prescribed zeros, with
multiplicities.
Related elementary factors: Matteo Cipollina’s Hadamard development. See CREDITS.md.
Library: `Complex.analyticOrderAt_weierstrassProduct`. -/
theorem weierstrass_product :
    ∀ {a : ℕ → ℂ}, (∀ n, a n ≠ 0) →
    Filter.Tendsto (fun n ↦ ‖a n‖) Filter.atTop Filter.atTop →
    Differentiable ℂ (Complex.weierstrassProduct a) ∧
    ∀ w : ℂ, analyticOrderAt (Complex.weierstrassProduct a) w =
    ({n : ℕ | a n = w}.ncard : ℕ∞) := by
  intro a ha hlim
  refine ⟨Complex.differentiable_weierstrassProduct ha hlim, fun w ↦ ?_⟩
  rw [Set.ncard_eq_toFinset_card _ (Complex.finite_setOf_eq_of_tendsto hlim w)]
  exact Complex.analyticOrderAt_weierstrassProduct ha hlim w

/-- 25. Weierstrass factorization for a nonzero zero sequence tending to infinity, counted with
multiplicity.
Library: `Complex.exists_exp_mul_weierstrassProduct`. -/
theorem weierstrass_factorization :
    ∀ {a : ℕ → ℂ} {f : ℂ → ℂ}, Differentiable ℂ f →
    (∀ n, a n ≠ 0) → Filter.Tendsto (fun n ↦ ‖a n‖) Filter.atTop Filter.atTop →
    (∀ w : ℂ, analyticOrderAt f w = ({n : ℕ | a n = w}.ncard : ℕ∞)) →
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
    ∀ z : ℂ, f z = Complex.exp (g z) * Complex.weierstrassProduct a z := by
  intro a f hf ha hlim hzero
  apply Complex.exists_exp_mul_weierstrassProduct hf ha hlim
  intro w
  rw [← Set.ncard_eq_toFinset_card _ (Complex.finite_setOf_eq_of_tendsto hlim w)]
  exact hzero w

/-- 26. Hadamard factorization under an explicit growth bound, with polynomial degree at most the
genus.
Related factorization theorem: Matteo Cipollina (PrimeNumberTheoremAnd fork). See CREDITS.md.
Library: `Complex.exists_hadamard_factorization`. -/
theorem hadamard :
    ∀ {f : ℂ → ℂ},
    Differentiable ℂ f →
    (∃ (z : ℂ), f z ≠ 0) →
    ∀ {ρ : ℝ},
    0 ≤ ρ →
    Complex.HasOrderLE f ρ →
    ∀ {k : ℕ},
    ρ < ↑k + 1 →
    ∃ (ι : Type) (_ : Countable ι) (a : ι → ℂ) (m : ℕ) (P : Polynomial ℂ),
    (∀ (i : ι), a i ≠ 0) ∧
    Filter.Tendsto (fun (i : ι) ↦ ‖a i‖) Filter.cofinite Filter.atTop ∧
    (∀ (i : ι), f (a i) = 0) ∧
    (Summable fun (i : ι) ↦ ‖a i‖⁻¹ ^ (k + 1)) ∧
    P.natDegree ≤ k ∧
    ∀ (z : ℂ), f z = Complex.exp (Polynomial.eval z P) * z ^ m * Complex.canonicalProduct k a z := by
  exact @Complex.exists_hadamard_factorization

/-- 27. The multiplicity-weighted Blaschke condition for nonzero zeros of a bounded nontrivial
holomorphic function.
Library: `Complex.summable_analyticOrderAt_toNat_mul_one_sub_norm_of_bounded`. -/
theorem blaschke_condition :
    ∀ {f : ℂ → ℂ},
    DifferentiableOn ℂ f (Metric.ball 0 1) →
    ∀ {M : ℝ},
    (∀ z ∈ Metric.ball 0 1, ‖f z‖ ≤ M) →
    (∃ z ∈ Metric.ball 0 1, f z ≠ 0) →
    Summable fun (w : { w : ℂ // ‖w‖ < 1 ∧ f w = 0 ∧ w ≠ 0 }) ↦ ((analyticOrderAt f (w : ℂ)).toNat : ℝ) *
    (1 - ‖(w : ℂ)‖) := by
  exact @Complex.summable_analyticOrderAt_toNat_mul_one_sub_norm_of_bounded

/-- 28. Riesz factorization into an origin power, a Blaschke product and a zero-free bounded
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
    ∀ z ∈ Metric.ball 0 1, f z = z ^ m * Complex.blaschkeProduct a z * g z := by
  exact @Complex.exists_rieszFactorization

/-- 29. The normalized Riemann mapping theorem for a proper simply connected open subset of the
plane.
Related proofs: Vincent Beffara (RMT4) and Yury Kudryashov (PR #33505). See CREDITS.md.
Library: `Complex.exists_riemannMap`. -/
theorem riemann_mapping :
    ∀ {U : Set ℂ} {z₀ : ℂ},
    IsOpen U →
    IsSimplyConnected U →
    U ≠ Set.univ →
    z₀ ∈ U →
    ∃ (f : ℂ → ℂ),
    DifferentiableOn ℂ f U ∧
    Set.InjOn f U ∧ f '' U = Metric.ball 0 1 ∧ f z₀ = 0 ∧ ∃ (r : ℝ), 0 < r ∧ deriv f z₀ = ↑r := by
  exact @Complex.exists_riemannMap

/-- 30. Uniqueness of the Riemann map normalized by its value and a positive real derivative.
Library: `Complex.eqOn_of_riemannMap`. -/
theorem riemann_mapping_unique :
    ∀ {U : Set ℂ} {z₀ : ℂ},
    IsOpen U →
    z₀ ∈ U →
    ∀ {f₁ f₂ : ℂ → ℂ},
    DifferentiableOn ℂ f₁ U →
    Set.InjOn f₁ U →
    f₁ '' U = Metric.ball 0 1 →
    f₁ z₀ = 0 →
    ∀ {r₁ : ℝ},
    0 < r₁ →
    deriv f₁ z₀ = ↑r₁ →
    DifferentiableOn ℂ f₂ U →
    Set.InjOn f₂ U →
    f₂ '' U = Metric.ball 0 1 →
    f₂ z₀ = 0 → ∀ {r₂ : ℝ}, 0 < r₂ → deriv f₂ z₀ = ↑r₂ → Set.EqOn f₁ f₂ U := by
  exact @Complex.eqOn_of_riemannMap

/-- 31. Schwarz–Pick contraction of the pseudohyperbolic distance on the unit disc.
Related disc shifts: Yury Kudryashov (PR #33368). See CREDITS.md.
Library: `Complex.norm_discMobius_apply_apply_le`. -/
theorem schwarz_pick :
    ∀ {f : ℂ → ℂ},
    DifferentiableOn ℂ f (Metric.ball 0 1) →
    Set.MapsTo f (Metric.ball 0 1) (Metric.ball 0 1) →
    ∀ {a w : ℂ}, ‖a‖ < 1 → ‖w‖ < 1 → ‖(f a).discMobius (f w)‖ ≤ ‖a.discMobius w‖ := by
  exact @Complex.norm_discMobius_apply_apply_le

/-- 32. The differential Schwarz–Pick inequality on the unit disc.
Library: `Complex.norm_deriv_div_one_sub_normSq_le`. -/
theorem schwarz_pick_derivative :
    ∀ {f : ℂ → ℂ},
    DifferentiableOn ℂ f (Metric.ball 0 1) →
    Set.MapsTo f (Metric.ball 0 1) (Metric.ball 0 1) →
    ∀ {a : ℂ}, ‖a‖ < 1 → ‖deriv f a‖ / (1 - Complex.normSq (f a)) ≤ 1 / (1 - Complex.normSq a) := by
  exact @Complex.norm_deriv_div_one_sub_normSq_le

/-- 33. Koebe’s quarter theorem for a normalized univalent function.
Library: `Complex.ball_subset_image_of_injOn`. -/
theorem koebe_quarter :
    ∀ {f : ℂ → ℂ},
    DifferentiableOn ℂ f (Metric.ball 0 1) →
    Set.InjOn f (Metric.ball 0 1) → f 0 = 0 → deriv f 0 = 1 → Metric.ball 0 (1 / 4) ⊆ f ''
    Metric.ball 0 1 := by
  exact @Complex.ball_subset_image_of_injOn

/-- 34. The two-sided Koebe distortion bound for the derivative of a univalent function.
Library: `Complex.distortion_le_of_class_S`. -/
theorem koebe_distortion :
    ∀ {f : ℂ → ℂ},
    DifferentiableOn ℂ f (Metric.ball 0 1) →
    Set.InjOn f (Metric.ball 0 1) →
    deriv f 0 = 1 →
    ∀ {z₀ : ℂ},
    z₀ ∈ Metric.ball 0 1 → (1 - ‖z₀‖) / (1 + ‖z₀‖) ^ 3 ≤ ‖deriv f z₀‖ ∧ ‖deriv f z₀‖ ≤ (1 + ‖z₀‖)
    / (1 - ‖z₀‖) ^ 3 := by
  exact @Complex.distortion_le_of_class_S

/-- 35. The upper Koebe growth bound for a normalized univalent function.
Library: `Complex.norm_le_div_one_sub_sq_of_class_S`. -/
theorem koebe_growth :
    ∀ {f : ℂ → ℂ},
    DifferentiableOn ℂ f (Metric.ball 0 1) →
    Set.InjOn f (Metric.ball 0 1) →
    f 0 = 0 → deriv f 0 = 1 → ∀ {z₀ : ℂ}, z₀ ∈ Metric.ball 0 1 → ‖f z₀‖ ≤ ‖z₀‖ / (1 - ‖z₀‖) ^ 2 := by
  exact @Complex.norm_le_div_one_sub_sq_of_class_S

/-- 36. The Dirichlet problem on a disc with arbitrary continuous boundary data.
Library: `Complex.exists_harmonicContOnCl_eqOn_sphere`. -/
theorem dirichlet_disc :
    ∀ {c : ℂ} {R : ℝ} {g : ℂ → ℝ},
    0 < R →
    ContinuousOn g (Metric.sphere c R) →
    ∃ (u : ℂ → ℝ), InnerProductSpace.HarmonicContOnCl u (Metric.ball c R) ∧ Set.EqOn u g
    (Metric.sphere c R) := by
  exact @Complex.exists_harmonicContOnCl_eqOn_sphere

/-- 37. The two-sided Harnack inequality for a harmonic function nonnegative on the boundary circle.
Library: `Complex.harnack`. -/
theorem harnack :
    ∀ {c w : ℂ} {R : ℝ},
    0 < R →
    ∀ {u : ℂ → ℝ},
    InnerProductSpace.HarmonicContOnCl u (Metric.ball c R) →
    (∀ z ∈ Metric.sphere c R, 0 ≤ u z) →
    w ∈ Metric.ball c R → (R - ‖w - c‖) / (R + ‖w - c‖) * u c ≤ u w ∧ u w ≤ (R + ‖w - c‖) / (R -
    ‖w - c‖) * u c := by
  exact @Complex.harnack

/-- 38. Harnack convergence for an increasing harmonic sequence bounded above at one point.
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
    Filter.atTop U := by
  exact @Complex.exists_harmonicOnNhd_tendstoLocallyUniformlyOn_of_monotone

/-- 39. The strong maximum principle for real-valued subharmonic functions.
Library: `Complex.SubharmonicOn.eqOn_const_of_isMaxOn`. -/
theorem subharmonic_maximum :
    ∀ {u : ℂ → ℝ} {U : Set ℂ} {a : ℂ},
    IsOpen U → IsPreconnected U → Complex.SubharmonicOn u U → a ∈ U → (∀ z ∈ U, u z ≤ u a) → ∀ z ∈
    U, u z = u a := by
  exact @Complex.SubharmonicOn.eqOn_const_of_isMaxOn

/-- 40. A C² function with nonnegative Laplacian is subharmonic.
Library: `Complex.subharmonicOn_of_laplacian_nonneg`. -/
theorem subharmonic_laplacian :
    ∀ {g : ℂ → ℝ} {U : Set ℂ},
    IsOpen U → ContDiffOn ℝ 2 g U → (∀ t ∈ U, 0 ≤ Laplacian.laplacian g t) → Complex.SubharmonicOn
    g U := by
  exact @Complex.subharmonicOn_of_laplacian_nonneg

/-- 41. The Dirichlet problem on bounded open sets satisfying an exterior-disc condition at every
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
    (nhds (g ζ)) := by
  exact @Complex.exists_harmonicOnNhd_tendsto_of_exteriorDisc

/-- 42. A nonnegative Green function with logarithmic singularity and zero boundary limits on such a
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
    (∀ ζ ∈ frontier U, Filter.Tendsto G (nhdsWithin ζ U) (nhds 0)) ∧ ∀ z ∈ U, z ≠ w → 0 ≤ G z := by
  exact @Complex.exists_greenFunction

/-- 43. Schwarz reflection across the real axis on a conjugation-invariant open set.
Library: `Complex.analyticOnNhd_schwarzReflection`. -/
theorem schwarz_reflection :
    ∀ {U : Set ℂ} {f : ℂ → ℂ},
    IsOpen U →
    Set.MapsTo (⇑(starRingEnd ℂ)) U U →
    ContinuousOn f (U ∩ {z : ℂ | 0 ≤ z.im}) →
    DifferentiableOn ℂ f (U ∩ {z : ℂ | 0 < z.im}) →
    (∀ z ∈ U, z.im = 0 → (f z).im = 0) → AnalyticOnNhd ℂ (Complex.schwarzReflection f) U := by
  exact @Complex.analyticOnNhd_schwarzReflection

/-- 44. The lacunary series with exponents `2 ^ n` has no continuous extension across any point of
the unit circle.
Library: `Complex.not_exists_continuousOn_extension_lacunary`. -/
theorem natural_boundary :
    ∀ {ζ₀ : ℂ},
    ‖ζ₀‖ = 1 →
    ∀ {ε : ℝ},
    0 < ε →
    ¬∃ (g : ℂ → ℂ),
    ContinuousOn g (Metric.ball ζ₀ ε) ∧ Set.EqOn Complex.lacunary g (Metric.ball ζ₀ ε ∩
    Metric.ball 0 1) := by
  exact @Complex.not_exists_continuousOn_extension_lacunary

/-- 45. Removability of a countable exceptional set for a continuous, otherwise holomorphic
Banach-valued function.
Library: `Complex.analyticOnNhd_of_continuousOn_off_countable`. -/
theorem removability :
    ∀ {F : Type u_1} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {U S : Set ℂ} {f : ℂ → F},
    IsOpen U → S.Countable → ContinuousOn f U → AnalyticOnNhd ℂ f (U \ S) → AnalyticOnNhd ℂ f U := by
  exact @Complex.analyticOnNhd_of_continuousOn_off_countable

end LeanCA
