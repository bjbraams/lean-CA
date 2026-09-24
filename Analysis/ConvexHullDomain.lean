/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Convex.Hull

/-!
# Connectedness of convex-hull-admissible configurations

Configurations whose convex hull stays in a path-connected set form a path-connected
set. Each configuration contracts to one of its nodes inside its own convex hull;
constant configurations are then joined along a path in the original set.
The index type may be empty or infinite, and the ambient space need not be finite-dimensional.

## Main results

* `IsPathConnected.convexHull_range_subset`: If a set is path connected, so is the space of
  configurations whose entire convex hull lies in it. No convexity of the original set is
  required.

## References

* `Mathlib.Analysis.Convex.PathConnected`: formal background used by this module.
* `Mathlib.Analysis.Convex.Hull`: formal background used by this module.
-/

public section
open Set

/-- If a set is path connected, so is the space of configurations whose entire convex hull
lies in it. No convexity of the original set is required. -/
theorem IsPathConnected.convexHull_range_subset
    {E ι : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E] {D : Set E} (hD : IsPathConnected D) :
    IsPathConnected {z : ι → E | convexHull ℝ (range z) ⊆ D} := by
  classical
  have hdiag (x : E) (hx : x ∈ D) :
      (fun _ : ι => x) ∈ {z : ι → E | convexHull ℝ (range z) ⊆ D} := by
    apply (convexHull_min (t := {x}) (by rintro _ ⟨i, rfl⟩; rfl) (convex_singleton x)).trans
    exact singleton_subset_iff.mpr hx
  obtain ⟨c, hc⟩ := hD.nonempty
  refine ⟨fun _ => c, hdiag c hc, ?_⟩
  intro z hz
  rcases isEmpty_or_nonempty ι with hι | hι
  · have he : z = fun _ => c := funext fun i => isEmptyElim i
    rw [he]
    exact JoinedIn.refl (hdiag c hc)
  · obtain ⟨i⟩ := hι
    let C : Set (ι → E) := Set.pi univ (fun _ => convexHull ℝ (range z))
    have hzC : z ∈ C := fun j _ => subset_convexHull ℝ _ ⟨j, rfl⟩
    have hiC : (fun _ : ι => z i) ∈ C := fun _ _ => subset_convexHull ℝ _ ⟨i, rfl⟩
    have hC : IsPathConnected C :=
      (convex_pi (fun _ _ => convex_convexHull ℝ (range z))).isPathConnected ⟨z, hzC⟩
    have hsub : C ⊆ {w : ι → E | convexHull ℝ (range w) ⊆ D} := by
      intro w hw
      exact (convexHull_min (by rintro _ ⟨j, rfl⟩; exact hw j (mem_univ j))
        (convex_convexHull ℝ (range z))).trans hz
    have hd := hD.image (f := fun x : E => fun _ : ι => x) (by fun_prop)
    refine ((hd.joinedIn _ ⟨c, hc, rfl⟩ _
      ⟨z i, hz (subset_convexHull ℝ _ ⟨i, rfl⟩), rfl⟩).mono ?_).trans
        ((hC.joinedIn _ hiC _ hzC).mono hsub)
    rintro _ ⟨x, hx, rfl⟩
    exact hdiag x hx
