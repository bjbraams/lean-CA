/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.CauchyIntegral
public import Mathlib.Geometry.Polygon.Basic

/-!
# Integration around polygons

The integral around a polygon is the sum of Mathlib curve integrals over its oriented edges.
Exact functions have zero polygon integral. Cauchy's theorem follows on simply connected open sets.
No simplicity or nondegeneracy assumption is needed for these results, and empty polygons
and polygons with repeated vertices are allowed. Interior and separation theory are separate
from this algebraic and analytic interface.

## Main results

* `Polygon.complexIntegral_zero_vertices`: The integral around a polygon with no vertices is
  zero.
* `Polygon.complexIntegral_eq_zero_of_isExactOn`: An exact continuous function has zero integral
  around a polygon whose boundary lies in its domain. This does not require the polygon to be
  simple.
* `Polygon.complexIntegral_eq_zero_of_differentiableOn_convex`: Cauchy's integral theorem for
  polygon boundaries in a convex open domain.
* `Polygon.complexIntegral_eq_zero_of_differentiableOn_isSimplyConnected`: Cauchy's integral
  theorem for polygon boundaries in a simply connected open domain. No simplicity assumption on
  the polygon is needed, including for zero or one vertex.
* `Polygon.complexIntegral_eq_zero_of_vertices`: On a convex domain it suffices to check the
  polygon's vertices.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

@[expose] public noncomputable section

open Set Complex

namespace Polygon

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {n : ℕ}

/-- Integrate a complex Banach-valued function around the oriented edges of a polygon. -/
def complexIntegral (p : Polygon ℂ n) (f : ℂ → F) : F :=
  ∑ i, curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z))
    (Path.segment (p i) (p (finRotate n i)))

/-- The integral around a polygon with no vertices is zero. -/
@[simp] theorem complexIntegral_zero_vertices (p : Polygon ℂ 0) (f : ℂ → F) :
    p.complexIntegral f = 0 := by simp [complexIntegral]

/-- A one-vertex polygon has zero integral. -/
@[simp] theorem complexIntegral_one_vertex (p : Polygon ℂ 1) (f : ℂ → F) :
    p.complexIntegral f = 0 := by
  unfold complexIntegral
  apply Finset.sum_eq_zero
  intro i _
  rw [show finRotate 1 i = i from Subsingleton.elim _ _, Path.segment_same,
    curveIntegral_refl]

variable [CompleteSpace F]

/-- An exact continuous function has zero integral around a polygon whose boundary lies
in its domain. This does not require the polygon to be simple. -/
theorem complexIntegral_eq_zero_of_isExactOn (p : Polygon ℂ n) {U : Set ℂ} {f : ℂ → F}
    (hf : Complex.IsExactOn f U) (hfc : ContinuousOn f U) (hp : p.boundary ℝ ⊆ U) :
    p.complexIntegral f = 0 := by
  obtain ⟨P, hP⟩ := hf
  have hω : ContinuousOn (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) U :=
    (ContinuousLinearMap.toSpanSingletonLIE ℂ F).continuous.comp_continuousOn hfc
  have hedge (i : Fin n) : segment ℝ (p i) (p (finRotate n i)) ⊆ U := by
    intro z hz
    apply hp
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    simpa only [edgeSet, affineSegment_eq_segment] using hz
  unfold complexIntegral
  simp_rw [curveIntegral_segment_eq_sub_of_hasFDerivAt
    (fun z hz ↦ (hP z hz).hasFDerivAt) hω (hedge _)]
  rw [Finset.sum_sub_distrib, Equiv.sum_comp (finRotate n) (fun i ↦ P (p i)), sub_self]

/-- Cauchy's integral theorem for polygon boundaries in a convex open domain. -/
theorem complexIntegral_eq_zero_of_differentiableOn_convex (p : Polygon ℂ n)
    {U : Set ℂ} {f : ℂ → F} (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : DifferentiableOn ℂ f U) (hp : p.boundary ℝ ⊆ U) :
    p.complexIntegral f = 0 := by
  obtain ⟨P, hP⟩ := hUc.exists_forall_hasDerivWithinAt hf
  exact p.complexIntegral_eq_zero_of_isExactOn
    ⟨P, fun z hz ↦ (hP z hz).hasDerivAt (hU.mem_nhds hz)⟩ hf.continuousOn hp

/-- Cauchy's integral theorem for polygon boundaries in a simply connected open domain.
No simplicity assumption on the polygon is needed, including for zero or one vertex. -/
theorem complexIntegral_eq_zero_of_differentiableOn_isSimplyConnected (p : Polygon ℂ n)
    {U : Set ℂ} {f : ℂ → F} (hU : IsOpen U) (hUc : IsSimplyConnected U)
    (hf : DifferentiableOn ℂ f U) (hp : p.boundary ℝ ⊆ U) :
    p.complexIntegral f = 0 :=
  p.complexIntegral_eq_zero_of_isExactOn
    (hf.isExactOn_of_isSimplyConnected hU hUc) hf.continuousOn hp

/-- On a convex domain it suffices to check the polygon's vertices. -/
theorem complexIntegral_eq_zero_of_vertices (p : Polygon ℂ n)
    {U : Set ℂ} {f : ℂ → F} (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : DifferentiableOn ℂ f U) (hp : ∀ i, p i ∈ U) : p.complexIntegral f = 0 := by
  apply p.complexIntegral_eq_zero_of_differentiableOn_convex hU hUc hf
  intro z hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp hz
  exact hUc.segment_subset (hp i) (hp (finRotate n i))
    (by simpa only [edgeSet, affineSegment_eq_segment] using hi)

end Polygon
