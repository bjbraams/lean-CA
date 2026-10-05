/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.CurveIndex
public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.Analysis.Contour.Winding.LocallyConstant
public import TauCeti.Analysis.Contour.Winding.UnboundedComponent

/-!
# Dependence of the curve index on the pole

The analytic index of a closed piecewise `C¹` curve is locally constant, and hence
continuous, on the complement of its image. In particular, moving the pole within a connected
region avoiding the curve does not change the index.
The index also vanishes outside a sufficiently large ball, and consequently on every
unbounded connected component of the complement. These facts do not require simplicity
of the curve or any Jordan separation theorem.

On such curves the index is the winding number of the Tau Ceti contributors
(`Complex.curveIndex_eq_windingNumber`), and the constancy on components of the complement and
the vanishing on unbounded components are imported from
`TauCeti.Analysis.Contour.Winding.LocallyConstant` and
`TauCeti.Analysis.Contour.Winding.UnboundedComponent`. A `C¹` path satisfies the hypothesis by
`Complex.isPiecewiseC1On_extend_of_contDiffOn`.

## Main results

* `Complex.curveIndex_eq_of_mem_connectedComponentIn`: The index is constant on each connected
  component of the complement of the curve.
* `Complex.continuousOn_curveIndex`: The index of a closed piecewise `C¹` curve depends
  continuously on the pole away from its image.
* `Complex.curveIndex_eq_zero_of_notMem_ball`: A closed piecewise `C¹` curve contained in a ball
  has index zero about every point outside that ball.
* `Complex.exists_pos_curveIndex_eq_zero_outside_ball`: The index of a closed piecewise `C¹`
  curve vanishes outside some ball about any prescribed center.
* `Complex.curveIndex_eq_zero_of_isPreconnected_of_not_isBounded`: The index vanishes on every
  unbounded preconnected set disjoint from the curve.
* `Complex.curveIndex_eq_zero_of_not_isBounded_connectedComponentIn`: The index is zero on any
  unbounded connected component of the complement of the curve.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Set Filter Metric
open scoped Topology unitInterval

namespace Complex

variable {a : ℂ} (γ : Path a a)

/-- The image of `[0, 1]` under the extension of a path is its range. -/
private theorem image_extend_uIcc : γ.extend '' uIcc 0 1 = range γ :=
  γ.image_extend_of_subset (by rw [uIcc_of_le zero_le_one])

/-- The index is constant on each connected component of the complement of the curve.

This adapts `TauCeti.Contour.IsPiecewiseC1On.windingNumber_eq_of_mem_connectedComponentIn` by the
Tau Ceti contributors. -/
theorem curveIndex_eq_of_mem_connectedComponentIn
    (hγ : TauCeti.Contour.IsPiecewiseC1On γ.extend 0 1) {v w : ℂ} (hv : v ∉ range γ)
    (hw : w ∈ connectedComponentIn (range γ)ᶜ v) :
    curveIndex γ w = curveIndex γ v := by
  have hw' : w ∉ range γ := connectedComponentIn_subset _ _ hw
  rw [curveIndex_eq_windingNumber hγ fun t ht ↦ hw' ⟨t, ht⟩,
    curveIndex_eq_windingNumber hγ fun t ht ↦ hv ⟨t, ht⟩]
  exact hγ.windingNumber_eq_of_mem_connectedComponentIn (by simp)
    (by rwa [image_extend_uIcc])

/-- Moving the pole in a preconnected set disjoint from the curve preserves the index.
The set need not be open or path connected. -/
theorem curveIndex_eq_of_isPreconnected
    (hγ : TauCeti.Contour.IsPiecewiseC1On γ.extend 0 1) {U : Set ℂ} (hU : IsPreconnected U)
    (hUγ : U ⊆ (range γ)ᶜ) {v w : ℂ} (hv : v ∈ U) (hw : w ∈ U) :
    curveIndex γ v = curveIndex γ w :=
  (curveIndex_eq_of_mem_connectedComponentIn γ hγ (hUγ hw)
    (hU.subset_connectedComponentIn hw hUγ hv))

/-- Every pole off a closed piecewise `C¹` curve has a disk avoiding the curve on which the
index is constant. This gives an ambient-plane version of local constancy. -/
theorem exists_ball_curveIndex_eq
    (hγ : TauCeti.Contour.IsPiecewiseC1On γ.extend 0 1) {w : ℂ} (hw : w ∉ range γ) :
    ∃ r > 0, ball w r ⊆ (range γ)ᶜ ∧
      ∀ z ∈ ball w r, curveIndex γ z = curveIndex γ w := by
  have hU := (isCompact_range γ.continuous).isClosed.isOpen_compl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU w hw
  exact ⟨r, hr, hball, fun z hz ↦ curveIndex_eq_of_isPreconnected γ hγ
    (convex_ball w r).isPreconnected hball hz (mem_ball_self hr)⟩

/-- The index is locally constant on the complement of a closed piecewise `C¹` curve. -/
theorem isLocallyConstant_curveIndex (hγ : TauCeti.Contour.IsPiecewiseC1On γ.extend 0 1) :
    IsLocallyConstant (fun w : ((range γ)ᶜ : Set ℂ) ↦ curveIndex γ w) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun w ↦ ?_
  obtain ⟨r, hr, -, heq⟩ := exists_ball_curveIndex_eq γ hγ w.property
  exact Filter.mem_of_superset
    (continuous_subtype_val.continuousAt.preimage_mem_nhds (ball_mem_nhds (w : ℂ) hr))
    fun z hz ↦ heq z hz

/-- The index of a closed piecewise `C¹` curve depends continuously on the pole away from its
image. -/
theorem continuousOn_curveIndex (hγ : TauCeti.Contour.IsPiecewiseC1On γ.extend 0 1) :
    ContinuousOn (curveIndex γ) (range γ)ᶜ := by
  intro w hw
  obtain ⟨r, hr, -, heq⟩ := exists_ball_curveIndex_eq γ hγ hw
  exact (continuousAt_const.congr (eventually_of_mem (ball_mem_nhds w hr)
    fun z hz ↦ (heq z hz).symm)).continuousWithinAt

/-- A closed piecewise `C¹` curve contained in a ball has index zero about every point outside
that ball. -/
theorem curveIndex_eq_zero_of_notMem_ball {c w : ℂ} {R : ℝ}
    (hγ : TauCeti.Contour.IsPiecewiseC1On γ.extend 0 1) (hball : ∀ t, γ t ∈ ball c R)
    (hw : w ∉ ball c R) : curveIndex γ w = 0 := by
  have hcw : w ≠ c := fun h ↦ hw (h ▸ mem_ball_self (pos_of_mem_ball (hball 0)))
  have hwr : ∀ t, γ t ≠ w := fun t h ↦ hw (h ▸ hball t)
  rw [curveIndex_eq_windingNumber hγ hwr]
  refine hγ.windingNumber_eq_zero_of_ray (by simp) (sub_ne_zero.mpr hcw) fun s hs hmem ↦ ?_
  rw [image_extend_uIcc] at hmem
  obtain ⟨t, ht⟩ := hmem
  have hd : dist (w + (s : ℂ) * (w - c)) c = (1 + s) * dist w c := by
    rw [dist_eq_norm, dist_eq_norm, show w + (s : ℂ) * (w - c) - c = ((1 + s : ℝ) : ℂ) * (w - c)
      by push_cast; ring, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have h1 := mem_ball.mp (ht ▸ hball t)
  rw [hd] at h1
  have h2 : R ≤ dist w c := not_lt.mp hw
  nlinarith [dist_nonneg (x := w) (y := c)]

/-- The index of a closed piecewise `C¹` curve vanishes outside some ball about any prescribed
center. -/
theorem exists_pos_curveIndex_eq_zero_outside_ball
    (hγ : TauCeti.Contour.IsPiecewiseC1On γ.extend 0 1) (c : ℂ) :
    ∃ R > 0, ∀ w, w ∉ ball c R → curveIndex γ w = 0 := by
  obtain ⟨R, hR, hball⟩ := (isCompact_range γ.continuous).isBounded.subset_ball_lt 0 c
  exact ⟨R, hR, fun w hw ↦ curveIndex_eq_zero_of_notMem_ball γ hγ
    (fun t ↦ hball ⟨t, rfl⟩) hw⟩

/-- The index is zero on any unbounded connected component of the complement of the curve.

This adapts `TauCeti.Contour.IsPiecewiseC1On.windingNumber_eq_zero_of_unbounded_component` by
the Tau Ceti contributors. -/
theorem curveIndex_eq_zero_of_not_isBounded_connectedComponentIn
    (hγ : TauCeti.Contour.IsPiecewiseC1On γ.extend 0 1) {w : ℂ} (hw : w ∉ range γ)
    (hUb : ¬ Bornology.IsBounded (connectedComponentIn (range γ)ᶜ w)) :
    curveIndex γ w = 0 := by
  rw [curveIndex_eq_windingNumber hγ fun t ht ↦ hw ⟨t, ht⟩]
  exact hγ.windingNumber_eq_zero_of_unbounded_component (by simp)
    (by rwa [image_extend_uIcc])

/-- The index vanishes on every unbounded preconnected set disjoint from the curve. -/
theorem curveIndex_eq_zero_of_isPreconnected_of_not_isBounded
    (hγ : TauCeti.Contour.IsPiecewiseC1On γ.extend 0 1) {U : Set ℂ} (hU : IsPreconnected U)
    (hUγ : U ⊆ (range γ)ᶜ) (hUb : ¬ Bornology.IsBounded U) {w : ℂ} (hw : w ∈ U) :
    curveIndex γ w = 0 :=
  curveIndex_eq_zero_of_not_isBounded_connectedComponentIn γ hγ (hUγ hw)
    fun hb ↦ hUb (hb.subset (hU.subset_connectedComponentIn hw hUγ))

end Complex
