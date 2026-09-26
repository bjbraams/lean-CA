/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.UnivalentDisk.Geometry
public import ComplexAnalysis.LaurentSeries.Geometry

/-!
# Separation by holomorphic disk boundaries

For an injective holomorphic map on a disk, the image of a smaller concentric circle
separates the plane into precisely its image disk and the complement of its image
closed disk. The exterior is connected because the larger image disk supplies a
connected outer annulus. This proves separation for this class of analytic contours,
without invoking the Jordan theorem for arbitrary embedded circles.

## Main results

* `Complex.isConnected_ball_sdiff_closedBall`: A translated open annulus is connected.
* `Complex.isConnected_compl_image_closedBall_of_injOn_holomorphic`: The exterior of a univalent
  image of a closed disk is connected. The map only needs to be injective and holomorphic on a
  slightly larger open disk.
* `Complex.compl_image_sphere_eq_union_of_injOn_holomorphic`: The complement of the image circle
  is the disjoint union of the image open disk and the connected exterior of the image closed
  disk.
* `Complex.connectedComponentIn_compl_image_sphere`: Every point off a univalent image circle
  belongs to exactly one of its two complementary components: the image disk or its exterior.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section
open Set Metric

namespace Complex

/-- A translated open annulus is connected. -/
theorem isConnected_ball_sdiff_closedBall (c : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    IsConnected (ball c R \ closedBall c r) := by
  have he : (fun z : ℂ ↦ z + c) '' {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R} =
      ball c R \ closedBall c r := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [mem_sdiff, mem_ball, mem_closedBall, dist_eq_norm,
        add_sub_cancel_right, not_le] using And.symm hx
    · intro hz
      have hz' : ‖z - c‖ < R ∧ r < ‖z - c‖ := by
        simpa only [mem_sdiff, mem_ball, mem_closedBall, dist_eq_norm, not_le] using hz
      exact ⟨z - c, hz'.symm, sub_add_cancel z c⟩
  rw [← he]
  exact (isConnected_complex_annulus hr hrR).image _ (by fun_prop)

/-- The exterior of a univalent image of a closed disk is connected. The map only needs
to be injective and holomorphic on a slightly larger open disk. -/
theorem isConnected_compl_image_closedBall_of_injOn_holomorphic
    {f : ℂ → ℂ} {c : ℂ} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hi : InjOn f (ball c R)) :
    IsConnected (f '' closedBall c r)ᶜ := by
  have hsub : closedBall c r ⊆ ball c R := closedBall_subset_ball hrR
  have hk := isCompact_image_closedBall_of_holomorphic hf hsub
  refine ⟨nonempty_compl.mpr hk.ne_univ, ?_⟩
  apply hk.isClosed.isPreconnected_compl_of_isPreconnected_sdiff
    (isOpen_image_of_injOn_holomorphic isOpen_ball hf hi isOpen_ball Subset.rfl)
    (image_mono hsub)
  rw [← hi.image_sdiff_subset hsub]
  exact ((isConnected_ball_sdiff_closedBall c hr hrR).image f
    (hf.continuousOn.mono sdiff_subset)).isPreconnected

/-- The complement of the image circle is the disjoint union of the image open disk
and the connected exterior of the image closed disk. -/
theorem compl_image_sphere_eq_union_of_injOn_holomorphic
    {f : ℂ → ℂ} {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hi : InjOn f (ball c R)) :
    (f '' sphere c r)ᶜ = (f '' ball c r) ∪ (f '' closedBall c r)ᶜ := by
  rw [← frontier_image_ball_of_injOn_holomorphic isOpen_ball hf hi hr
    (closedBall_subset_ball hrR), frontier,
    (isOpen_image_of_injOn_holomorphic isOpen_ball hf hi isOpen_ball
      (ball_subset_ball hrR.le)).interior_eq,
    closure_image_ball hr (hf.continuousOn.mono (closedBall_subset_ball hrR))]
  ext z
  simp only [mem_compl_iff, mem_sdiff, mem_union]
  tauto

open scoped Classical in
/-- Every point off a univalent image circle belongs to exactly one of its two
complementary components: the image disk or its exterior. -/
theorem connectedComponentIn_compl_image_sphere
    {f : ℂ → ℂ} {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hi : InjOn f (ball c R))
    {z : ℂ} (hz : z ∉ f '' sphere c r) :
    connectedComponentIn (f '' sphere c r)ᶜ z =
      if z ∈ f '' ball c r then f '' ball c r else (f '' closedBall c r)ᶜ := by
  have hsub : closedBall c r ⊆ ball c R := closedBall_subset_ball hrR
  have ho := isOpen_image_of_injOn_holomorphic isOpen_ball hf hi isOpen_ball
    (ball_subset_ball hrR.le)
  have he := compl_image_sphere_eq_union_of_injOn_holomorphic hr hrR hf hi
  have hk := isCompact_image_closedBall_of_holomorphic hf hsub
  have hd : Disjoint (f '' ball c r) (f '' closedBall c r)ᶜ :=
    disjoint_compl_right.mono_left (image_mono ball_subset_closedBall)
  split_ifs with hzinside
  · rw [← frontier_image_ball_of_injOn_holomorphic isOpen_ball hf hi hr hsub]
    exact ho.connectedComponentIn_compl_frontier
      (isConnected_image_ball_of_holomorphic hf hr (ball_subset_ball hrR.le)).isPreconnected
          hzinside
  · have hzoutside : z ∈ (f '' closedBall c r)ᶜ :=
      (he ▸ (show z ∈ (f '' sphere c r)ᶜ from hz)).resolve_left hzinside
    apply le_antisymm
    · exact isPreconnected_connectedComponentIn.subset_right_of_subset_union ho
        hk.isClosed.isOpen_compl hd
        (by rw [← he]; exact connectedComponentIn_subset _ _)
        ⟨z, mem_connectedComponentIn hz, hzoutside⟩
    · have hc := isConnected_compl_image_closedBall_of_injOn_holomorphic hr.le hrR hf hi
      exact hc.isPreconnected.subset_connectedComponentIn hzoutside
        (by rw [he]; exact subset_union_right)

end Complex
