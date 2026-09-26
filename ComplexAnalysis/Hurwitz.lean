/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Rouche
public import ComplexAnalysis.ZeroPersistence
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Hurwitz's theorem

Uniform approximation on a closed disk with a zero-free boundary eventually preserves
the total number of zeros counted with multiplicity. On a connected open set, a locally
uniform limit of zero-free holomorphic functions is zero-free or identically zero.

## Main results

* `Complex.exists_zero_of_norm_lt_sphere`: The center-versus-boundary zero criterion on a disk
  with arbitrary center.
* `Complex.eventually_sum_divisor_eq_of_tendstoUniformlyOn`: Uniform convergence on a closed
  disk eventually preserves its divisor degree if the holomorphic limit has no boundary zeros.
* `Complex.eventually_exists_zero_of_tendstoUniformlyOn`: A zero of the limit persists under
  uniform holomorphic approximation on a closed disk whose boundary contains no zeros of the
  limit.
* `Complex.eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn`: **Hurwitz's theorem.** A
  locally uniform limit of zero-free holomorphic functions on a connected open set is
  identically zero or has no zeros.
* `Complex.eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn`: A locally uniform limit of
  injective holomorphic functions on a connected open set is constant or injective.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Set Filter Metric MeromorphicOn
open scoped Topology

namespace Complex

/-- The center-versus-boundary zero criterion on a disk with arbitrary center. -/
theorem exists_zero_of_norm_lt_sphere {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hlt : ∀ z ∈ sphere c R, ‖f c‖ < ‖f z‖) :
    ∃ z ∈ ball c R, f z = 0 := by
  obtain ⟨w, hw, he⟩ := exists_zero_of_norm_lt_boundary (f := fun w ↦ f (c + w)) hR
    (fun w hw ↦ ((hf (c + w) (by simpa [dist_eq_norm] using hw)).differentiableAt.comp w
      ((differentiableAt_const c).add differentiableAt_id)).differentiableWithinAt)
    (fun w hw ↦ by simpa using hlt (c + w) (by simpa [dist_eq_norm] using hw))
  exact ⟨c + w, by simpa [dist_eq_norm] using hw, he⟩

/-- Uniform convergence on a closed disk eventually preserves its divisor degree if the
holomorphic limit has no boundary zeros. -/
theorem eventually_sum_divisor_eq_of_tendstoUniformlyOn {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hF : ∀ᶠ n in l, AnalyticOnNhd ℂ (F n) (closedBall c R))
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hb : ∀ z ∈ sphere c R, f z ≠ 0)
    (hlim : TendstoUniformlyOn F f l (closedBall c R)) :
    ∀ᶠ n in l, (∑ᶠ z, divisor (F n) (closedBall c R) z) =
      ∑ᶠ z, divisor f (closedBall c R) z := by
  obtain ⟨b, hb', hmin⟩ := (isCompact_sphere c R).exists_isMinOn
    ⟨c + R, by simp [abs_of_pos hR]⟩
    (hf.continuousOn.norm.mono sphere_subset_closedBall)
  have hpos := norm_pos_iff.mpr (hb b hb')
  filter_upwards [hF, Metric.tendstoUniformlyOn_iff.mp hlim _ hpos] with n hn hclose
  apply (sum_divisor_eq_of_norm_sub_lt hR hf hn _).symm
  intro z hz
  have hh := hclose z (sphere_subset_closedBall hz)
  have hh' : ‖F n z - f z‖ < ‖f b‖ := by
    simpa [dist_eq_norm, norm_sub_rev] using hh
  exact hh'.trans_le (hmin hz)

/-- A zero of the limit persists under uniform holomorphic approximation on a closed disk
whose boundary contains no zeros of the limit. -/
theorem eventually_exists_zero_of_tendstoUniformlyOn {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hF : ∀ᶠ n in l, AnalyticOnNhd ℂ (F n) (closedBall c R))
    (hf : ContinuousOn f (closedBall c R)) (hz : f c = 0)
    (hb : ∀ z ∈ sphere c R, f z ≠ 0)
    (hlim : TendstoUniformlyOn F f l (closedBall c R)) :
    ∀ᶠ n in l, ∃ z ∈ ball c R, F n z = 0 := by
  obtain ⟨b, hb', hmin⟩ := (isCompact_sphere c R).exists_isMinOn
    ⟨c + R, by simp [abs_of_pos hR]⟩ (hf.norm.mono sphere_subset_closedBall)
  have hpos := norm_pos_iff.mpr (hb b hb')
  filter_upwards [hF, Metric.tendstoUniformlyOn_iff.mp hlim _ (by positivity :
    0 < ‖f b‖ / 3)] with n hn hclose
  apply exists_zero_of_norm_lt_sphere hR hn
  intro z hz'
  have hcenter : ‖F n c‖ < ‖f b‖ / 3 := by
    simpa [hz] using hclose c (mem_closedBall_self hR.le)
  have hboundary : ‖f z - F n z‖ < ‖f b‖ / 3 := by
    simpa [dist_eq_norm] using hclose z (sphere_subset_closedBall hz')
  have hnorm := norm_sub_norm_le (f z) (F n z)
  have hmin' : ‖f b‖ ≤ ‖f z‖ := hmin hz'
  linarith

/-- **Hurwitz's theorem.** A locally uniform limit of zero-free holomorphic functions on
a connected open set is identically zero or has no zeros.

Related formalizations: Vincent Beffara's RMT4 and Yury Kudryashov's Mathlib PR #33505. See
`CREDITS.md`. -/
theorem eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn
    {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U)
    (hne : ∀ᶠ n in l, ∀ z ∈ U, F n z ≠ 0)
    (hlim : TendstoLocallyUniformlyOn F f l U) :
    EqOn f 0 U ∨ ∀ z ∈ U, f z ≠ 0 := by
  have hf := (hlim.differentiableOn hF hU).analyticOnNhd hU
  by_cases hall : EqOn f 0 U
  · exact Or.inl hall
  right
  intro c hc hzero
  have hp : ∀ᶠ z in 𝓝[≠] c, f z ≠ 0 :=
    (hf c hc).eventually_eq_zero_or_eventually_ne_zero.resolve_left (fun he ↦
      hall (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hc he))
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhdsWithin_iff.mp hp
  obtain ⟨S, hS, hSsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hc)
  let r := min (R / 2) S
  have hr : 0 < r := lt_min (by positivity) hS
  have hrR : r < R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hKU : closedBall c r ⊆ U := (closedBall_subset_closedBall (min_le_right _ _)).trans hSsub
  have hb : ∀ z ∈ sphere c r, f z ≠ 0 := by
    intro z hz
    exact hball ⟨(mem_sphere.mp hz).trans_lt hrR, ne_of_mem_sphere hz hr.ne'⟩
  have hFn : ∀ᶠ n in l, AnalyticOnNhd ℂ (F n) (closedBall c r) :=
    hF.mono (fun _ hn ↦ (hn.analyticOnNhd hU).mono hKU)
  have he := eventually_exists_zero_of_tendstoUniformlyOn hr hFn
    (hf.continuousOn.mono hKU) hzero hb
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_closedBall c r)).mp (hlim.mono hKU))
  obtain ⟨n, ⟨z, hz, hnz⟩, hn⟩ := (he.and hne).exists
  exact hn z (hKU (ball_subset_closedBall hz)) hnz

/-- A locally uniform limit of injective holomorphic functions on a connected open set
is constant or injective.

Related formalizations: Vincent Beffara's RMT4 and Yury Kudryashov's Mathlib PR #33505. See
`CREDITS.md`. -/
theorem eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn
    {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U)
    (hinj : ∀ᶠ n in l, InjOn (F n) U)
    (hlim : TendstoLocallyUniformlyOn F f l U) :
    (∃ v : ℂ, EqOn f (fun _ ↦ v) U) ∨ InjOn f U := by
  by_cases hconst : ∃ v : ℂ, EqOn f (fun _ ↦ v) U
  · exact Or.inl hconst
  right
  intro a ha b hb hab
  by_contra hne
  have hV : IsOpen (U \ {a}) := hU.sdiff isClosed_singleton
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hV b ⟨hb, Ne.symm hne⟩
  have hballU : ball b r ⊆ U := fun z hz ↦ (hsub hz).1
  have hFd : ∀ᶠ n in l, DifferentiableOn ℂ (fun z ↦ F n z - F n a) (ball b r) :=
    hF.mono (fun n hn ↦ (hn.mono hballU).sub_const (F n a))
  have hFn : ∀ᶠ n in l, ∀ z ∈ ball b r, F n z - F n a ≠ 0 := by
    filter_upwards [hinj] with n hn z hz
    exact sub_ne_zero.mpr (fun he ↦ (hsub hz).2 (hn (hballU hz) ha he))
  have hlim' : TendstoLocallyUniformlyOn (fun n z ↦ F n z - F n a)
      (fun z ↦ f z - f a) l (ball b r) :=
    (hlim.sub ((hlim.tendsto_at ha).tendstoUniformlyOn_const U).tendstoLocallyUniformlyOn).mono
      hballU
  have he : EqOn (fun z ↦ f z - f a) 0 (ball b r) :=
    (eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn isOpen_ball
      (convex_ball b r).isPreconnected hFd hFn hlim').resolve_right (fun h ↦
        h b (mem_ball_self hr) (sub_eq_zero.mpr hab.symm))
  have he' : f =ᶠ[𝓝 b] (fun _ ↦ f a) := by
    filter_upwards [ball_mem_nhds b hr] with z hz
    exact sub_eq_zero.mp (he hz)
  have hf := (hlim.differentiableOn hF hU).analyticOnNhd hU
  exact hconst ⟨f a, hf.eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_const hconn hb he'⟩

end Complex
