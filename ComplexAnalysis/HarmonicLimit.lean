/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.DirichletDisc

/-!
# Limits of harmonic functions and Harnack's principle

A locally uniform limit of harmonic functions is harmonic: on every small closed disc the
functions are Poisson integrals of their boundary values, the circle averages pass to the
limit, and the Poisson integral of continuous data is harmonic. **Harnack's principle** then
follows from Harnack's inequality: a monotone sequence of harmonic functions on a connected
open set that is bounded at one point converges locally uniformly to a harmonic function.

## Main results

* `Complex.tendsto_circleAverage_of_tendstoUniformlyOn`: circle averages of a uniformly
  convergent sequence converge.
* `Complex.harmonicOnNhd_of_tendstoLocallyUniformlyOn`: harmonicity of locally uniform limits.
* `Complex.exists_harmonicOnNhd_tendstoLocallyUniformlyOn_of_monotone`: Harnack's principle.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Theorems X.2.10 (Harnack's principle)
  and X.2.11.
* T. W. Gamelin, *Complex Analysis*, Section XV.3.
-/

public noncomputable section

open Set Metric Filter Function InnerProductSpace Real
open scoped Topology

namespace Complex

variable {c : ℂ} {R : ℝ}

/-- Circle averages of a uniformly convergent sequence of continuous functions converge. -/
theorem tendsto_circleAverage_of_tendstoUniformlyOn {F : ℕ → ℂ → ℝ} {f : ℂ → ℝ}
    (hF : TendstoUniformlyOn F f atTop (sphere c |R|))
    (hFc : ∀ n, ContinuousOn (F n) (sphere c |R|)) :
    Tendsto (fun n => circleAverage (F n) c R) atTop (𝓝 (circleAverage f c R)) := by
  have hfc : ContinuousOn f (sphere c |R|) := hF.continuousOn (Eventually.of_forall hFc).frequently
  have hint : ∀ n, CircleIntegrable (F n) c R := fun n => (hFc n).circleIntegrable'
  have hfint : CircleIntegrable f c R := hfc.circleIntegrable'
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendstoUniformlyOn_iff] at hF
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hF (ε / 2) (half_pos hε))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, circleAverage_def, circleAverage_def, smul_eq_mul, smul_eq_mul, ← mul_sub,
    abs_mul, abs_of_pos (inv_pos.mpr two_pi_pos), ← intervalIntegral.integral_sub (hint n) hfint]
  have hbound : ‖∫ θ in (0 : ℝ)..2 * π, (F n (circleMap c R θ) - f (circleMap c R θ))‖ ≤
      ε / 2 * |2 * π - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    rw [Real.norm_eq_abs, abs_sub_comm, ← Real.dist_eq]
    exact (hN n hn _ (circleMap_mem_sphere' c R θ)).le
  rw [Real.norm_eq_abs] at hbound
  calc (2 * π)⁻¹ * |∫ θ in (0 : ℝ)..2 * π, (F n (circleMap c R θ) - f (circleMap c R θ))|
      ≤ (2 * π)⁻¹ * (ε / 2 * |2 * π - 0|) := by gcongr
    _ = ε / 2 := by
        rw [sub_zero, abs_of_pos two_pi_pos]
        field_simp
    _ < ε := half_lt_self hε

/-- **Locally uniform limits of harmonic functions are harmonic.** -/
theorem harmonicOnNhd_of_tendstoLocallyUniformlyOn {U : Set ℂ} (hU : IsOpen U)
    {u : ℕ → ℂ → ℝ} {f : ℂ → ℝ} (hu : ∀ n, HarmonicOnNhd (u n) U)
    (hlim : TendstoLocallyUniformlyOn u f atTop U) : HarmonicOnNhd f U := by
  intro a ha
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU a ha
  set r : ℝ := R / 2 with hr_def
  have hr : 0 < r := half_pos hR
  have hr' : |r| = r := abs_of_pos hr
  have hcl : closedBall a r ⊆ U := (closedBall_subset_ball (half_lt_self hR)).trans hRU
  have hunif : TendstoUniformlyOn u f atTop (closedBall a r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hlim _ hcl (isCompact_closedBall a r)
  have hsph : TendstoUniformlyOn u f atTop (sphere a |r|) := by
    rw [hr']
    exact hunif.mono sphere_subset_closedBall
  have hcont : ∀ n, ContinuousOn (u n) (sphere a |r|) := fun n => by
    rw [hr']
    exact (hu n).continuousOn.mono (sphere_subset_closedBall.trans hcl)
  have hfc : ContinuousOn f (sphere a r) := by
    have := hsph.continuousOn (Eventually.of_forall hcont).frequently
    rwa [hr'] at this
  -- the limit is the Poisson integral of its boundary values
  have hrepr : ∀ w ∈ ball a r, f w = poissonIntegral a r f w := by
    intro w hw
    have hwU : w ∈ U := hcl (ball_subset_closedBall hw)
    have h1 : ∀ n, u n w = circleAverage (poissonKernel a w • u n) a r := fun n =>
      (((hu n).mono hcl).circleAverage_poissonKernel_smul hw).symm
    have h2 : Tendsto (fun n => u n w) atTop (𝓝 (f w)) := hlim.tendsto_at hwU
    have hK : ∀ z ∈ sphere a |r|, |poissonKernel a w z| ≤ (r + ‖w - a‖) / (r - ‖w - a‖) := by
      intro z hz
      rw [hr'] at hz
      rw [abs_of_nonneg (poissonKernel_nonneg hz hw)]
      exact poissonKernel_le hz hw
    set C : ℝ := (r + ‖w - a‖) / (r - ‖w - a‖) with hC_def
    have hC0 : 0 ≤ C := by
      have := mem_ball_iff_norm.mp hw
      positivity
    have hunifK : TendstoUniformlyOn (fun n => poissonKernel a w • u n) (poissonKernel a w • f)
        atTop (sphere a |r|) := by
      rw [Metric.tendstoUniformlyOn_iff] at hsph ⊢
      intro ε hε
      filter_upwards [hsph (ε / (C + 1)) (by positivity)] with n hn z hz
      have h := hn z hz
      rw [Real.dist_eq] at h ⊢
      change |poissonKernel a w z * f z - poissonKernel a w z * u n z| < ε
      rw [← mul_sub, abs_mul]
      calc |poissonKernel a w z| * |f z - u n z| ≤ C * (ε / (C + 1)) :=
            mul_le_mul (hK z hz) h.le (abs_nonneg _) hC0
        _ < ε := by
            rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
            nlinarith
    have hKc : ∀ n, ContinuousOn (poissonKernel a w • u n) (sphere a |r|) := fun n => by
      rw [hr'] at hcont ⊢
      exact (continuousOn_poissonKernel_sphere hw).smul (hcont n)
    have h3 := tendsto_circleAverage_of_tendstoUniformlyOn hunifK hKc
    have h2' : Tendsto (fun n => circleAverage (poissonKernel a w • u n) a r) atTop (𝓝 (f w)) := by
      refine h2.congr fun n => ?_
      exact h1 n
    exact tendsto_nhds_unique h2' h3
  have hharm : HarmonicOnNhd (poissonIntegral a r f) (ball a r) :=
    harmonicOnNhd_poissonIntegral hr hfc
  have hev : f =ᶠ[𝓝 a] poissonIntegral a r f := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with w hw
    exact hrepr w hw
  exact (harmonicAt_congr_nhds hev).mpr (hharm a (mem_ball_self hr))

/-- **Local Harnack estimate for monotone sequences.** Around every point `a` of `U` there is a
ball on which the increments `u n - u m` are comparable to their values at `a`. -/
theorem exists_ball_harnack_of_monotone {U : Set ℂ} (hU : IsOpen U) {u : ℕ → ℂ → ℝ}
    (hu : ∀ n, HarmonicOnNhd (u n) U) (hmono : ∀ z ∈ U, Monotone fun n => u n z) (a : ℂ) :
    ∃ ρ > 0, a ∈ U → (ball a ρ ⊆ U ∧ ∀ w ∈ ball a ρ, ∀ m n, m ≤ n →
      u n a - u m a ≤ 3 * (u n w - u m w) ∧ u n w - u m w ≤ 3 * (u n a - u m a)) := by
  by_cases ha : a ∈ U
  · obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU a ha
    set r : ℝ := R / 2 with hr_def
    have hr : 0 < r := half_pos hR
    have hcl : closedBall a r ⊆ U := (closedBall_subset_ball (half_lt_self hR)).trans hRU
    refine ⟨r / 2, half_pos hr, fun _ => ⟨(ball_subset_ball (by linarith)).trans hRU,
      fun w hw m n hmn => ?_⟩⟩
    -- Harnack's inequality for the nonnegative harmonic function `u n - u m`
    set v : ℂ → ℝ := fun z => u n z - u m z with hv_def
    have hv : HarmonicContOnCl v (ball a r) := by
      have h : HarmonicOnNhd v (closure (ball a r)) := by
        rw [closure_ball _ hr.ne']
        exact ((hu n).sub (hu m)).mono hcl
      exact h.harmonicContOnCl
    have hpos : ∀ z ∈ sphere a r, 0 ≤ v z := fun z hz => by
      have hzU : z ∈ U := hcl (sphere_subset_closedBall hz)
      exact sub_nonneg.mpr (hmono z hzU hmn)
    have hwr : w ∈ ball a r := ball_subset_ball (by linarith) hw
    obtain ⟨hlo, hup⟩ := harnack hr hv hpos hwr
    have hd : ‖w - a‖ < r / 2 := mem_ball_iff_norm.mp hw
    have hd0 : 0 ≤ ‖w - a‖ := norm_nonneg _
    have hva : 0 ≤ v a := sub_nonneg.mpr (hmono a ha hmn)
    constructor
    · -- `v a ≤ 3 v w` from the lower bound
      have h1 : (1 / 3 : ℝ) ≤ (r - ‖w - a‖) / (r + ‖w - a‖) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        linarith
      have : (1 / 3 : ℝ) * v a ≤ v w := (mul_le_mul_of_nonneg_right h1 hva).trans hlo
      linarith
    · have h1 : (r + ‖w - a‖) / (r - ‖w - a‖) ≤ 3 := by
        rw [div_le_iff₀ (by linarith)]
        linarith
      have : v w ≤ 3 * v a := hup.trans (mul_le_mul_of_nonneg_right h1 hva)
      exact this
  · exact ⟨1, one_pos, fun h => absurd h ha⟩

/-- **Harnack's principle.** A monotone sequence of harmonic functions on a connected open set
that is bounded above at one point converges locally uniformly to a harmonic function. -/
theorem exists_harmonicOnNhd_tendstoLocallyUniformlyOn_of_monotone {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) {u : ℕ → ℂ → ℝ} (hu : ∀ n, HarmonicOnNhd (u n) U)
    (hmono : ∀ z ∈ U, Monotone fun n => u n z) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hbdd : BddAbove (range fun n => u n z₀)) :
    ∃ f : ℂ → ℝ, HarmonicOnNhd f U ∧ TendstoLocallyUniformlyOn u f atTop U := by
  classical
  choose ρ hρ0 hρ using exists_ball_harnack_of_monotone hU hu hmono
  set S : Set ℂ := {a | a ∈ U ∧ BddAbove (range fun n => u n a)} with hS_def
  -- boundedness propagates along the Harnack balls
  have hS_ball : ∀ a ∈ S, ball a (ρ a) ⊆ S := by
    intro a ha w hw
    obtain ⟨hball, hcomp⟩ := hρ a ha.1
    obtain ⟨M, hM⟩ := ha.2
    refine ⟨hball hw, ⟨u 0 w + 3 * (M - u 0 a), ?_⟩⟩
    rintro _ ⟨n, rfl⟩
    have h1 := (hcomp w hw 0 n (Nat.zero_le n)).2
    have h2 : u n a ≤ M := hM ⟨n, rfl⟩
    linarith
  have hnS_ball : ∀ a ∈ U \ S, ∀ w ∈ ball a (ρ a), w ∉ S := by
    intro a ha w hw hwS
    obtain ⟨hball, hcomp⟩ := hρ a ha.1
    apply ha.2
    obtain ⟨M, hM⟩ := hwS.2
    refine ⟨ha.1, ⟨u 0 a + 3 * (M - u 0 w), ?_⟩⟩
    rintro _ ⟨n, rfl⟩
    have h1 := (hcomp w hw 0 n (Nat.zero_le n)).1
    have h2 : u n w ≤ M := hM ⟨n, rfl⟩
    linarith
  -- connectedness: every point of `U` is a point of boundedness
  have hUS : U ⊆ S := by
    set A : Set ℂ := ⋃ a ∈ S, ball a (ρ a) with hA_def
    set B : Set ℂ := ⋃ a ∈ U \ S, ball a (ρ a) with hB_def
    have hA : IsOpen A := isOpen_biUnion fun a _ => isOpen_ball
    have hB : IsOpen B := isOpen_biUnion fun a _ => isOpen_ball
    have hAB : Disjoint A B := by
      rw [Set.disjoint_left]
      intro w hwA hwB
      obtain ⟨a, ha, hwa⟩ := mem_iUnion₂.mp hwA
      obtain ⟨b, hb, hwb⟩ := mem_iUnion₂.mp hwB
      exact hnS_ball b hb w hwb (hS_ball a ha hwa)
    have hcover : U ⊆ A ∪ B := by
      intro a ha
      by_cases haS : a ∈ S
      · exact Or.inl (mem_iUnion₂.mpr ⟨a, haS, mem_ball_self (hρ0 a)⟩)
      · exact Or.inr (mem_iUnion₂.mpr ⟨a, ⟨ha, haS⟩, mem_ball_self (hρ0 a)⟩)
    have hne : (U ∩ A).Nonempty :=
      ⟨z₀, hz₀, mem_iUnion₂.mpr ⟨z₀, ⟨hz₀, hbdd⟩, mem_ball_self (hρ0 z₀)⟩⟩
    have hUA : U ⊆ A := hUc.subset_left_of_subset_union hA hB hAB hcover hne
    intro a ha
    obtain ⟨b, hb, hab⟩ := mem_iUnion₂.mp (hUA ha)
    exact hS_ball b hb hab
  -- the limit function
  set f : ℂ → ℝ := fun w => ⨆ n, u n w with hf_def
  have hbddU : ∀ w ∈ U, BddAbove (range fun n => u n w) := fun w hw => (hUS hw).2
  have htend : ∀ w ∈ U, Tendsto (fun n => u n w) atTop (𝓝 (f w)) := fun w hw =>
    tendsto_atTop_ciSup (hmono w hw) (hbddU w hw)
  have hle : ∀ w ∈ U, ∀ n, u n w ≤ f w := fun w hw n => le_ciSup (hbddU w hw) n
  -- locally uniform convergence
  have hlim : TendstoLocallyUniformlyOn u f atTop U := by
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε a ha
    obtain ⟨hball, hcomp⟩ := hρ a ha
    refine ⟨ball a (ρ a), mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self (hρ0 a))),
      ?_⟩
    have h1 : ∀ᶠ n in atTop, 3 * (f a - u n a) < ε := by
      have := (htend a ha).eventually (lt_mem_nhds (show f a - ε / 3 < f a by linarith))
      filter_upwards [this] with n hn
      linarith
    filter_upwards [h1] with n hn w hw
    have hwU : w ∈ U := hball hw
    have hupper : f w - u n w ≤ 3 * (f a - u n a) := by
      rw [sub_le_iff_le_add]
      refine ciSup_le fun m => ?_
      rcases le_or_gt m n with hmn | hmn
      · have h2 : u m w ≤ u n w := hmono w hwU hmn
        have h3 : u n a ≤ f a := hle a ha n
        linarith
      · have h2 := (hcomp w hw n m hmn.le).2
        have h3 : u m a ≤ f a := hle a ha m
        linarith
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hle w hwU n))]
    linarith
  exact ⟨f, harmonicOnNhd_of_tendstoLocallyUniformlyOn hU hu hlim, hlim⟩

end Complex

end
