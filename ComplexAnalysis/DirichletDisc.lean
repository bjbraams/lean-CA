/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Harnack
public import ComplexAnalysis.Subharmonic.Basic

/-!
# The Dirichlet problem on a disc

For continuous boundary data `g` on the circle `‖z - c‖ = R`, the Poisson integral
`w ↦ circleAverage (poissonKernel c w • g) c R` is harmonic on the open disc and tends to
`g ζ₀` as `w` tends to a boundary point `ζ₀` from inside. Hence the Dirichlet problem on the disc
has a solution, continuous on the closed disc, and by the maximum principle the solution is
unique.

Harmonicity comes from Mathlib's analyticity of the Herglotz–Riesz integral in the pole
parameter. The boundary behavior is the classical approximate identity argument: the kernel is
nonnegative with total mass one, and it is uniformly small on the part of the circle away from
`ζ₀` when `w` is close to `ζ₀`.

## Main results

* `Complex.harmonicOnNhd_poissonIntegral`: the Poisson integral is harmonic.
* `Complex.tendsto_poissonIntegral`: boundary values.
* `Complex.exists_harmonicContOnCl_eqOn_sphere`: **solution of the Dirichlet problem**.
* `Complex.eqOn_of_harmonicContOnCl_of_eqOn_sphere`: uniqueness.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Theorem X.2.4.
* T. W. Gamelin, *Complex Analysis*, Section X.1.
* B. Simon, *Basic Complex Analysis*, Section 5.3.
-/

@[expose] public noncomputable section

open Set Metric Filter Function InnerProductSpace Real
open scoped Topology

namespace Complex

variable {c w z : ℂ} {R : ℝ} {g : ℂ → ℝ}

/-- The Poisson integral of boundary data `g` on the circle of center `c` and radius `R`. -/
def poissonIntegral (c : ℂ) (R : ℝ) (g : ℂ → ℝ) (w : ℂ) : ℝ :=
  circleAverage (poissonKernel c w • g) c R

/-- Harmonic functions on an open set are subharmonic. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.subharmonicOn {u : ℂ → ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hu : HarmonicOnNhd u U) : SubharmonicOn u U := by
  have hcont : ContinuousOn u U := hu.contDiffOn.continuousOn
  refine ⟨hcont.upperSemicontinuousOn, fun a ha => ?_⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hU a ha
  refine hasSubmeanAt_of_circleAverage_eq hρ (hcont.mono hball) fun r hr hrρ => ?_
  have : HarmonicOnNhd u (closedBall a |r|) :=
    hu.mono ((closedBall_subset_ball (by rwa [abs_of_pos hr])).trans hball)
  exact this.circleAverage_eq

/-- The Poisson integral of continuous boundary data is harmonic on the open disc. -/
theorem harmonicOnNhd_poissonIntegral (hR : 0 < R) (hg : ContinuousOn g (sphere c R)) :
    HarmonicOnNhd (poissonIntegral c R g) (ball c R) := by
  set g' : ℂ → ℝ := fun ζ => g (ζ + c) with hg'_def
  have hg'c : ContinuousOn g' (sphere 0 R) := by
    refine hg.comp (continuous_id.add continuous_const).continuousOn fun ζ hζ => ?_
    rw [mem_sphere_zero_iff_norm] at hζ
    rw [mem_sphere_iff_norm, add_sub_cancel_right, hζ]
  have hg' : CircleIntegrable g' 0 R := ContinuousOn.circleIntegrable hR.le hg'c
  have hg'C : CircleIntegrable (fun ζ => (g' ζ : ℂ)) 0 R :=
    ContinuousOn.circleIntegrable hR.le (continuous_ofReal.comp_continuousOn hg'c)
  set H : ℂ → ℂ := fun v => circleAverage (fun ζ => herglotzRieszKernel 0 v ζ • (g' ζ : ℂ)) 0 R
    with hH_def
  have hH : AnalyticOnNhd ℂ H (sphere (0 : ℂ) |R|)ᶜ :=
    analyticOnNhd_circleAverage_herglotzRieszKernel_smul hg'C
  have hmem : ∀ w ∈ ball c R, w - c ∉ sphere (0 : ℂ) |R| := by
    intro w hw
    rw [mem_sphere_zero_iff_norm, abs_of_pos hR]
    exact (mem_ball_iff_norm.mp hw).ne
  have hrepr : ∀ w ∈ ball c R, poissonIntegral c R g w = (H (w - c)).re := by
    intro w hw
    rw [hH_def]
    dsimp only
    rw [re_circleAverage_herglotzRieszKernel_smul hg' (hmem w hw), poissonIntegral,
      ← circleAverage_map_add_const]
    congr 1
    ext ζ
    simp only [poissonKernel_eq_re_herglotzRieszKernel, Pi.smul_apply', comp_apply,
      herglotzRieszKernel_add_const, hg'_def]
  intro w hw
  have hev : poissonIntegral c R g =ᶠ[𝓝 w] fun v => (H (v - c)).re := by
    filter_upwards [isOpen_ball.mem_nhds hw] with v hv
    exact hrepr v hv
  rw [harmonicAt_congr_nhds hev]
  have hsub : AnalyticAt ℂ (fun v : ℂ => v - c) w := analyticAt_id.sub analyticAt_const
  have hHan : AnalyticAt ℂ (H ∘ fun v => v - c) w :=
    AnalyticAt.comp (g := H) (f := fun v : ℂ => v - c) (x := w) (hH _ (hmem w hw)) hsub
  exact hHan.harmonicAt_re

/-- The elementary estimate `R ^ 2 - ‖w - c‖ ^ 2 ≤ 2 * R * dist w ζ₀` for `w` in the disc and
`ζ₀` on the circle. -/
theorem sq_sub_norm_sq_le (hR : 0 < R) {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ sphere c R) (hw : w ∈ ball c R) :
    R ^ 2 - ‖w - c‖ ^ 2 ≤ 2 * R * dist w ζ₀ := by
  rw [mem_sphere_iff_norm] at hζ₀
  rw [mem_ball_iff_norm] at hw
  have h1 : R - ‖w - c‖ ≤ dist w ζ₀ := by
    rw [dist_eq_norm, ← hζ₀]
    have := norm_sub_norm_le (ζ₀ - c) (w - c)
    rw [show ζ₀ - c - (w - c) = -(w - ζ₀) by ring, norm_neg] at this
    linarith
  have h2 : R + ‖w - c‖ ≤ 2 * R := by linarith
  calc R ^ 2 - ‖w - c‖ ^ 2 = (R - ‖w - c‖) * (R + ‖w - c‖) := by ring
    _ ≤ dist w ζ₀ * (2 * R) := by
        apply mul_le_mul h1 h2 (by linarith [norm_nonneg (w - c)]) dist_nonneg
    _ = 2 * R * dist w ζ₀ := by ring

/-- **Boundary values of the Poisson integral.** For continuous boundary data `g`, the Poisson
integral tends to `g ζ₀` as `w` tends to the boundary point `ζ₀` from inside the disc. -/
theorem tendsto_poissonIntegral (hR : 0 < R) (hg : ContinuousOn g (sphere c R)) {ζ₀ : ℂ}
    (hζ₀ : ζ₀ ∈ sphere c R) :
    Tendsto (poissonIntegral c R g) (𝓝[ball c R] ζ₀) (𝓝 (g ζ₀)) := by
  have hR' : |R| = R := abs_of_pos hR
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- a bound for `g` and a modulus of continuity at `ζ₀`
  obtain ⟨M, hM⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn hg
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM ζ₀ hζ₀)
  obtain ⟨δ, hδ, hδg⟩ : ∃ δ > 0, ∀ z ∈ sphere c R, dist z ζ₀ < δ → |g z - g ζ₀| ≤ ε / 2 := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuousWithinAt_iff.mp (hg ζ₀ hζ₀) (ε / 2) (half_pos hε)
    exact ⟨δ, hδ, fun z hz hzd => by simpa [Real.dist_eq] using (h hz hzd).le⟩
  set A : ℝ := (δ / 2) ^ 2 with hA_def
  have hA : 0 < A := by positivity
  set B : ℝ := 4 * R * M with hB_def
  have hB : 0 ≤ B := by positivity
  set η : ℝ := min (δ / 2) (ε / 2 * A / (B + 1)) with hη_def
  have hη : 0 < η := lt_min (half_pos hδ) (by positivity)
  refine ⟨η, hη, fun w hw hwζ => ?_⟩
  have hwδ : dist w ζ₀ < δ / 2 := hwζ.trans_le (min_le_left _ _)
  have hwη : dist w ζ₀ < ε / 2 * A / (B + 1) := hwζ.trans_le (min_le_right _ _)
  -- the size of the kernel away from `ζ₀`
  set C : ℝ := 2 * M * ((R ^ 2 - ‖w - c‖ ^ 2) / A) with hC_def
  have hC0 : 0 ≤ C := by
    have := sq_sub_norm_sq_le hR hζ₀ hw
    have h2 : 0 ≤ R ^ 2 - ‖w - c‖ ^ 2 := by
      rw [mem_ball_iff_norm] at hw
      nlinarith [norm_nonneg (w - c)]
    positivity
  -- pointwise bound on the circle
  have hpt : ∀ z ∈ sphere c R,
      |poissonKernel c w z * (g z - g ζ₀)| ≤ ε / 2 * poissonKernel c w z + C := by
    intro z hz
    have hK0 := poissonKernel_nonneg hz hw
    rw [abs_mul, abs_of_nonneg hK0]
    by_cases hzd : dist z ζ₀ < δ
    · have := hδg z hz hzd
      nlinarith
    · push Not at hzd
      have hzw : δ / 2 ≤ ‖z - w‖ := by
        have h1 := dist_triangle z w ζ₀
        have h2 : dist z w = ‖z - w‖ := dist_eq_norm z w
        linarith
      have hKle : poissonKernel c w z ≤ (R ^ 2 - ‖w - c‖ ^ 2) / A := by
        rw [poissonKernel_def, mem_sphere_iff_norm.mp hz,
          show z - c - (w - c) = z - w by ring]
        have hnum : 0 ≤ R ^ 2 - ‖w - c‖ ^ 2 := by
          rw [mem_ball_iff_norm] at hw
          nlinarith [norm_nonneg (w - c)]
        apply div_le_div_of_nonneg_left hnum hA
        rw [hA_def]
        exact pow_le_pow_left₀ (by positivity) hzw 2
      have hgb : |g z - g ζ₀| ≤ 2 * M := by
        calc |g z - g ζ₀| ≤ |g z| + |g ζ₀| := abs_sub _ _
          _ ≤ M + M := add_le_add (hM z hz) (hM ζ₀ hζ₀)
          _ = 2 * M := by ring
      have hnum' : 0 ≤ (R ^ 2 - ‖w - c‖ ^ 2) / A := by
        apply div_nonneg _ hA.le
        rw [mem_ball_iff_norm] at hw
        nlinarith [norm_nonneg (w - c)]
      calc poissonKernel c w z * |g z - g ζ₀| ≤ (R ^ 2 - ‖w - c‖ ^ 2) / A * (2 * M) :=
            mul_le_mul hKle hgb (abs_nonneg _) hnum'
        _ = C := by rw [hC_def]; ring
        _ ≤ ε / 2 * poissonKernel c w z + C := by nlinarith
  -- integrability
  have hgc : ContinuousOn g (sphere c |R|) := by rwa [hR']
  have hKc : ContinuousOn (poissonKernel c w) (sphere c |R|) := by
    rw [hR']
    exact continuousOn_poissonKernel_sphere hw
  have hint1 : CircleIntegrable (fun z => poissonKernel c w z * (g z - g ζ₀)) c R :=
    (hKc.mul (hgc.sub continuousOn_const)).circleIntegrable'
  have hint2 : CircleIntegrable (fun z => ε / 2 * poissonKernel c w z + C) c R :=
    ((continuousOn_const.mul hKc).add continuousOn_const).circleIntegrable'
  -- the difference as a circle average
  have hdiff : poissonIntegral c R g w - g ζ₀ =
      circleAverage (fun z => poissonKernel c w z * (g z - g ζ₀)) c R := by
    have h1 : CircleIntegrable (fun z => poissonKernel c w z * g z) c R :=
      (hKc.mul hgc).circleIntegrable'
    have h2 : CircleIntegrable (fun z => g ζ₀ * poissonKernel c w z) c R :=
      (continuousOn_const.mul hKc).circleIntegrable'
    have : (fun z => poissonKernel c w z * (g z - g ζ₀)) =
        fun z => poissonKernel c w z * g z - g ζ₀ * poissonKernel c w z := by
      ext z
      ring
    have h3 : circleAverage (fun z => g ζ₀ * poissonKernel c w z) c R = g ζ₀ := by
      have h4 := (circleAverage_fun_smul : circleAverage (fun z => g ζ₀ • poissonKernel c w z) c R =
        g ζ₀ • circleAverage (poissonKernel c w) c R)
      simp only [smul_eq_mul] at h4
      rw [h4, circleAverage_poissonKernel hw, mul_one]
    rw [this, circleAverage_fun_sub h1 h2, h3, poissonIntegral]
    rfl
  rw [Real.dist_eq, hdiff]
  calc |circleAverage (fun z => poissonKernel c w z * (g z - g ζ₀)) c R|
      ≤ circleAverage |fun z => poissonKernel c w z * (g z - g ζ₀)| c R :=
        abs_circleAverage_le_circleAverage_abs
    _ ≤ circleAverage (fun z => ε / 2 * poissonKernel c w z + C) c R := by
        refine circleAverage_mono hint1.abs hint2 fun z hz => ?_
        rw [hR'] at hz
        exact hpt z hz
    _ = ε / 2 + C := by
        have h4 : circleAverage (fun z => ε / 2 * poissonKernel c w z) c R = ε / 2 := by
          have h5 := (circleAverage_fun_smul :
            circleAverage (fun z => (ε / 2) • poissonKernel c w z) c R =
              (ε / 2) • circleAverage (poissonKernel c w) c R)
          simp only [smul_eq_mul] at h5
          rw [h5, circleAverage_poissonKernel hw, mul_one]
        have hint3 : CircleIntegrable (fun z => ε / 2 * poissonKernel c w z) c R :=
          (continuousOn_const.mul hKc).circleIntegrable'
        rw [circleAverage_fun_add hint3 (circleIntegrable_const C c R), h4, circleAverage_const]
    _ < ε := by
        have hC : C ≤ ε / 2 * (B / (B + 1)) := by
          have h1 : R ^ 2 - ‖w - c‖ ^ 2 ≤ 2 * R * (ε / 2 * A / (B + 1)) :=
            (sq_sub_norm_sq_le hR hζ₀ hw).trans
              (mul_le_mul_of_nonneg_left hwη.le (by positivity))
          calc C = 2 * M * ((R ^ 2 - ‖w - c‖ ^ 2) / A) := rfl
            _ ≤ 2 * M * (2 * R * (ε / 2 * A / (B + 1)) / A) := by gcongr
            _ = ε / 2 * (B / (B + 1)) := by
                rw [hB_def]
                field_simp
                ring
        have hB1 : B / (B + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
        have : ε / 2 * (B / (B + 1)) < ε / 2 := mul_lt_of_lt_one_right (half_pos hε) hB1
        linarith

open Classical in
/-- The Poisson extension of boundary data: the Poisson integral inside the disc, the data
itself outside. -/
def poissonExtension (c : ℂ) (R : ℝ) (g : ℂ → ℝ) (w : ℂ) : ℝ :=
  if w ∈ ball c R then poissonIntegral c R g w else g w

/-- Inside the open disc, the Poisson extension agrees with the Poisson integral. -/
theorem poissonExtension_of_mem (hw : w ∈ ball c R) :
    poissonExtension c R g w = poissonIntegral c R g w := by
  classical
  simp only [poissonExtension]
  rw [ite_eq_left_iff]
  exact fun h => absurd hw h

/-- Outside the open disc, including its boundary, the Poisson extension agrees with the prescribed
function. -/
theorem poissonExtension_of_notMem (hw : w ∉ ball c R) : poissonExtension c R g w = g w := by
  classical
  simp only [poissonExtension]
  rw [ite_eq_right_iff]
  exact fun h => absurd h hw

/-- A point on the boundary circle does not belong to the corresponding open disc. -/
theorem sphere_notMem_ball (hw : w ∈ sphere c R) : w ∉ ball c R := fun hwb => by
  rw [mem_sphere] at hw
  rw [mem_ball, hw] at hwb
  exact lt_irrefl _ hwb

/-- The Poisson extension is harmonic on the open disc. -/
theorem harmonicOnNhd_poissonExtension (hR : 0 < R) (hg : ContinuousOn g (sphere c R)) :
    HarmonicOnNhd (poissonExtension c R g) (ball c R) := by
  intro w hw
  have hev : poissonExtension c R g =ᶠ[𝓝 w] poissonIntegral c R g := by
    filter_upwards [isOpen_ball.mem_nhds hw] with v hv
    exact poissonExtension_of_mem hv
  rw [harmonicAt_congr_nhds hev]
  exact harmonicOnNhd_poissonIntegral hR hg w hw

/-- The Poisson extension is continuous on the closed disc. -/
theorem continuousOn_poissonExtension_closedBall (hR : 0 < R)
    (hg : ContinuousOn g (sphere c R)) :
    ContinuousOn (poissonExtension c R g) (closedBall c R) := by
  have hharm := harmonicOnNhd_poissonIntegral hR hg
  intro w hw
  by_cases hwb : w ∈ ball c R
  · have hev : poissonExtension c R g =ᶠ[𝓝 w] poissonIntegral c R g := by
      filter_upwards [isOpen_ball.mem_nhds hwb] with v hv
      exact poissonExtension_of_mem hv
    have hcont : ContinuousAt (poissonIntegral c R g) w :=
      hharm.contDiffOn.continuousOn.continuousAt (isOpen_ball.mem_nhds hwb)
    exact (ContinuousAt.congr hcont (Filter.EventuallyEq.symm hev)).continuousWithinAt
  · have hws : w ∈ sphere c R := by
      rw [mem_closedBall] at hw
      rw [mem_ball] at hwb
      exact mem_sphere.mpr (le_antisymm hw (not_lt.mp hwb))
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.tendsto_nhdsWithin_nhds.mp
      (tendsto_poissonIntegral hR hg hws) ε hε
    obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuousWithinAt_iff.mp (hg w hws) ε hε
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx hxw => ?_⟩
    rw [poissonExtension_of_notMem hwb]
    by_cases hxb : x ∈ ball c R
    · rw [poissonExtension_of_mem hxb]
      exact h₁ hxb (hxw.trans_le (min_le_left _ _))
    · have hxs : x ∈ sphere c R := by
        rw [mem_closedBall] at hx
        rw [mem_ball] at hxb
        exact mem_sphere.mpr (le_antisymm hx (not_lt.mp hxb))
      rw [poissonExtension_of_notMem hxb]
      exact h₂ hxs (hxw.trans_le (min_le_right _ _))

/-- The Poisson extension of a function continuous on a set containing the closed disc is
continuous on that set. -/
theorem continuousOn_poissonExtension (hR : 0 < R) {U : Set ℂ} (hcl : closedBall c R ⊆ U)
    (hg : ContinuousOn g U) : ContinuousOn (poissonExtension c R g) U := by
  have hgs : ContinuousOn g (sphere c R) := hg.mono (sphere_subset_closedBall.trans hcl)
  intro w hw
  by_cases hwc : w ∈ closedBall c R
  · by_cases hwb : w ∈ ball c R
    · exact ((continuousOn_poissonExtension_closedBall hR hgs).continuousAt
        (closedBall_mem_nhds_of_mem hwb)).continuousWithinAt
    · have hws : w ∈ sphere c R := by
        rw [mem_closedBall] at hwc
        rw [mem_ball] at hwb
        exact mem_sphere.mpr (le_antisymm hwc (not_lt.mp hwb))
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.tendsto_nhdsWithin_nhds.mp
        (tendsto_poissonIntegral hR hgs hws) ε hε
      obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuousWithinAt_iff.mp (hg w hw) ε hε
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx hxw => ?_⟩
      rw [poissonExtension_of_notMem hwb]
      by_cases hxb : x ∈ ball c R
      · rw [poissonExtension_of_mem hxb]
        exact h₁ hxb (hxw.trans_le (min_le_left _ _))
      · rw [poissonExtension_of_notMem hxb]
        exact h₂ hx (hxw.trans_le (min_le_right _ _))
  · have hev : poissonExtension c R g =ᶠ[𝓝 w] g := by
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hwc] with v hv
      exact poissonExtension_of_notMem fun h => hv (ball_subset_closedBall h)
    exact (hg w hw).congr_of_eventuallyEq (hev.filter_mono nhdsWithin_le_nhds)
      (poissonExtension_of_notMem fun h => hwc (ball_subset_closedBall h))

/-- The Poisson extension of continuous boundary data is harmonic on the disc and continuous
on the closed disc. -/
theorem harmonicContOnCl_poissonExtension (hR : 0 < R) (hg : ContinuousOn g (sphere c R)) :
    HarmonicContOnCl (poissonExtension c R g) (ball c R) :=
  HarmonicContOnCl.mk_ball (harmonicOnNhd_poissonExtension hR hg)
    (continuousOn_poissonExtension_closedBall hR hg)

/-- **The Dirichlet problem on a disc.** Continuous boundary data on the circle extend to a
function harmonic on the open disc and continuous on the closed disc. -/
theorem exists_harmonicContOnCl_eqOn_sphere (hR : 0 < R) (hg : ContinuousOn g (sphere c R)) :
    ∃ u : ℂ → ℝ, HarmonicContOnCl u (ball c R) ∧ EqOn u g (sphere c R) :=
  ⟨poissonExtension c R g, harmonicContOnCl_poissonExtension hR hg, fun _ hw =>
    poissonExtension_of_notMem (sphere_notMem_ball hw)⟩

/-- The Poisson integral is monotone in the boundary data. -/
theorem poissonIntegral_mono (hR : 0 < R) {g₁ g₂ : ℂ → ℝ} (hg₁ : ContinuousOn g₁ (sphere c R))
    (hg₂ : ContinuousOn g₂ (sphere c R)) (h : ∀ z ∈ sphere c R, g₁ z ≤ g₂ z) (hw : w ∈ ball c R) :
    poissonIntegral c R g₁ w ≤ poissonIntegral c R g₂ w := by
  have hR' : |R| = R := abs_of_pos hR
  have hKc : ContinuousOn (poissonKernel c w) (sphere c |R|) := by
    rw [hR']
    exact continuousOn_poissonKernel_sphere hw
  have hg₁' : ContinuousOn g₁ (sphere c |R|) := by rw [hR']; exact hg₁
  have hg₂' : ContinuousOn g₂ (sphere c |R|) := by rw [hR']; exact hg₂
  refine circleAverage_mono ((hKc.smul hg₁').circleIntegrable')
    ((hKc.smul hg₂').circleIntegrable') fun z hz => ?_
  rw [hR'] at hz
  exact mul_le_mul_of_nonneg_left (h z hz) (poissonKernel_nonneg hz hw)

/-- The Poisson extension is monotone in the data. -/
theorem poissonExtension_mono (hR : 0 < R) {g₁ g₂ : ℂ → ℝ} {U : Set ℂ}
    (hcl : closedBall c R ⊆ U) (hg₁ : ContinuousOn g₁ U) (hg₂ : ContinuousOn g₂ U)
    (h : ∀ z ∈ U, g₁ z ≤ g₂ z) :
    ∀ z ∈ U, poissonExtension c R g₁ z ≤ poissonExtension c R g₂ z := by
  intro z hz
  by_cases hzb : z ∈ ball c R
  · rw [poissonExtension_of_mem hzb, poissonExtension_of_mem hzb]
    exact poissonIntegral_mono hR (hg₁.mono (sphere_subset_closedBall.trans hcl))
      (hg₂.mono (sphere_subset_closedBall.trans hcl))
      (fun w hw => h w (hcl (sphere_subset_closedBall hw))) hzb
  · rw [poissonExtension_of_notMem hzb, poissonExtension_of_notMem hzb]
    exact h z hz

/-- **Uniqueness for the Dirichlet problem.** Two functions harmonic on the disc and continuous
on the closed disc that agree on the circle agree on the closed disc. -/
theorem eqOn_of_harmonicContOnCl_of_eqOn_sphere (hR : 0 < R) {u v : ℂ → ℝ}
    (hu : HarmonicContOnCl u (ball c R)) (hv : HarmonicContOnCl v (ball c R))
    (h : EqOn u v (sphere c R)) : EqOn u v (closedBall c R) := by
  have key : ∀ {u v : ℂ → ℝ}, HarmonicContOnCl u (ball c R) → HarmonicContOnCl v (ball c R) →
      EqOn u v (sphere c R) → ∀ z ∈ closedBall c R, u z ≤ v z := by
    intro u v hu hv h
    have hd : HarmonicContOnCl (u - v) (ball c R) := hu.sub hv
    have hsub : SubharmonicOn (u - v) (ball c R) := hd.harmonicOnNhd.subharmonicOn isOpen_ball
    have husc : UpperSemicontinuousOn (u - v) (closedBall c R) :=
      hd.continuousOn_ball.upperSemicontinuousOn
    have := hsub.le_of_le_sphere hR husc (M := 0) fun z hz => by
      simp [h hz]
    intro z hz
    have := this z hz
    simp only [Pi.sub_apply] at this
    linarith
  intro z hz
  exact le_antisymm (key hu hv h z hz) (key hv hu (fun x hx => (h hx).symm) z hz)

end Complex

end
