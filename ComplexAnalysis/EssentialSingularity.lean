/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Meromorphic.Order

/-!
# Isolated essential singularities and Casorati–Weierstrass

A function holomorphic on a punctured neighborhood has a removable singularity, a pole,
or an essential singularity. Meromorphic germs are exactly those admitting a finite limit
or tending to infinity in norm. At a nonmeromorphic isolated holomorphic singularity,
the image of every punctured neighborhood is dense in the complex plane.

The assigned value at the singular point is irrelevant throughout. Removability is expressed
by an analytic germ agreeing with the function on a punctured neighborhood.

## Main results

* `Complex.exists_analyticAt_eventuallyEq_of_eventually_norm_le`: A bounded isolated holomorphic
  singularity admits an analytic extension as a germ.
* `Complex.meromorphicAt_of_eventually_le_norm_sub`: Omitting a disk near an isolated
  holomorphic singularity forces it to be meromorphic. The reciprocal of the difference from the
  omitted center has a removable singularity.
* `Complex.dense_image_of_not_meromorphicAt`: **Casorati–Weierstrass.** At an isolated essential
  singularity, the image of every punctured neighborhood is dense in the complex plane.
  Essential means nonmeromorphic.
* `Complex.meromorphicAt_iff_exists_tendsto_or_tendsto_norm_atTop`: An isolated holomorphic
  singularity is meromorphic exactly when the punctured germ has a finite limit or tends to
  infinity in norm.
* `Complex.isolatedSingularity_trichotomy`: The isolated-singularity alternatives: an analytic
  extension, a pole, or dense image on every punctured neighborhood. The last conclusion is
  supplied by Casorati–Weierstrass.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Filter Function Metric Set
open scoped Topology

namespace Complex

/-- A bounded isolated holomorphic singularity admits an analytic extension as a germ. -/
theorem exists_analyticAt_eventuallyEq_of_eventually_norm_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : ℂ → F} {c : ℂ} {M : ℝ}
    (hf : ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ f z)
    (hb : ∀ᶠ z in 𝓝[≠] c, ‖f z‖ ≤ M) :
    ∃ g : ℂ → F, AnalyticAt ℂ g c ∧ f =ᶠ[𝓝[≠] c] g := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp (hf.and hb)
  have hd : DifferentiableOn ℂ f (ball c r \ {c}) :=
    fun z hz ↦ (hball hz).1.differentiableAt.differentiableWithinAt
  have hbound : BddAbove ((norm ∘ f) '' (ball c r \ {c})) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact (hball hz).2
  refine ⟨update f c (limUnder (𝓝[≠] c) f),
    (differentiableOn_update_limUnder_of_bddAbove
      (ball_mem_nhds c hr) hd hbound).analyticAt (ball_mem_nhds c hr), ?_⟩
  exact (update_eventuallyEq_nhdsNE f c c _).symm

/-- Boundedness near an isolated holomorphic singularity implies meromorphy there,
regardless of the assigned value at the center. -/
theorem meromorphicAt_of_eventually_norm_le {f : ℂ → ℂ} {c : ℂ} {M : ℝ}
    (hf : ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ f z)
    (hb : ∀ᶠ z in 𝓝[≠] c, ‖f z‖ ≤ M) : MeromorphicAt f c := by
  obtain ⟨g, hg, he⟩ := exists_analyticAt_eventuallyEq_of_eventually_norm_le hf hb
  exact hg.meromorphicAt.congr he.symm

/-- Omitting a disk near an isolated holomorphic singularity forces it to be meromorphic.
The reciprocal of the difference from the omitted center has a removable singularity. -/
theorem meromorphicAt_of_eventually_le_norm_sub {f : ℂ → ℂ} {c w : ℂ} {ε : ℝ}
    (hf : ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ f z) (hε : 0 < ε)
    (hb : ∀ᶠ z in 𝓝[≠] c, ε ≤ ‖f z - w‖) : MeromorphicAt f c := by
  have hg : MeromorphicAt (fun z ↦ (f z - w)⁻¹) c := by
    apply meromorphicAt_of_eventually_norm_le (M := ε⁻¹)
    · filter_upwards [hf, hb] with z hz hbound
      exact (hz.sub analyticAt_const).inv (norm_pos_iff.mp (hε.trans_le hbound))
    · filter_upwards [hb] with z hz
      rw [norm_inv]
      exact (inv_le_inv₀ (hε.trans_le hz) hε).mpr hz
  have hsub : MeromorphicAt (fun z ↦ f z - w) c := by
    simpa only [inv_inv] using hg.fun_inv
  simpa only [sub_add_cancel] using hsub.fun_add (MeromorphicAt.const w c)

/-- **Casorati–Weierstrass.** At an isolated essential singularity, the image of every
punctured neighborhood is dense in the complex plane. Essential means nonmeromorphic. -/
theorem dense_image_of_not_meromorphicAt {f : ℂ → ℂ} {c : ℂ}
    (hf : ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ f z) (he : ¬ MeromorphicAt f c)
    {s : Set ℂ} (hs : s ∈ 𝓝[≠] c) : Dense (f '' s) := by
  rw [Metric.dense_iff]
  intro w ε hε
  by_contra hn
  apply he
  apply meromorphicAt_of_eventually_le_norm_sub (w := w) hf hε
  filter_upwards [hs] with z hz
  apply le_of_not_gt
  intro hlt
  exact hn ⟨f z, by simpa [dist_eq_norm] using hlt, mem_image_of_mem f hz⟩

/-- An isolated holomorphic singularity is meromorphic exactly when the punctured germ
has a finite limit or tends to infinity in norm. -/
theorem meromorphicAt_iff_exists_tendsto_or_tendsto_norm_atTop {f : ℂ → ℂ} {c : ℂ}
    (hf : ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ f z) :
    MeromorphicAt f c ↔ (∃ w : ℂ, Tendsto f (𝓝[≠] c) (𝓝 w)) ∨
      Tendsto (fun z ↦ ‖f z‖) (𝓝[≠] c) atTop := by
  constructor
  · intro hm
    rcases lt_or_ge (meromorphicOrderAt f c) 0 with ho | ho
    · exact Or.inr (tendsto_norm_atTop_iff_cobounded.mpr
        (tendsto_cobounded_of_meromorphicOrderAt_neg ho))
    · exact Or.inl (tendsto_nhds_of_meromorphicOrderAt_nonneg hm ho)
  · rintro (⟨w, hw⟩ | htop)
    · apply meromorphicAt_of_eventually_norm_le hf (M := ‖w‖ + 1)
      exact (hw.norm.eventually (gt_mem_nhds (lt_add_one ‖w‖))).mono (fun _ h ↦ h.le)
    · apply meromorphicAt_of_eventually_le_norm_sub (w := 0) hf zero_lt_one
      simpa only [sub_zero] using htop.eventually (eventually_ge_atTop (1 : ℝ))

/-- The isolated-singularity alternatives: an analytic extension, a pole, or dense image
on every punctured neighborhood. The last conclusion is supplied by Casorati–Weierstrass. -/
theorem isolatedSingularity_trichotomy {f : ℂ → ℂ} {c : ℂ}
    (hf : ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ f z) :
    (∃ g : ℂ → ℂ, AnalyticAt ℂ g c ∧ f =ᶠ[𝓝[≠] c] g) ∨
      Tendsto (fun z ↦ ‖f z‖) (𝓝[≠] c) atTop ∨
      (∀ s ∈ 𝓝[≠] c, Dense (f '' s)) := by
  by_cases hm : MeromorphicAt f c
  · rcases (meromorphicAt_iff_exists_tendsto_or_tendsto_norm_atTop hf).mp hm with
      ⟨w, hw⟩ | htop
    · exact Or.inl (exists_analyticAt_eventuallyEq_of_eventually_norm_le hf
        ((hw.norm.eventually (gt_mem_nhds (lt_add_one ‖w‖))).mono fun _ h ↦ h.le))
    · exact Or.inr (Or.inl htop)
  · exact Or.inr (Or.inr (fun _ hs ↦ dense_image_of_not_meromorphicAt hf hm hs))

end Complex
