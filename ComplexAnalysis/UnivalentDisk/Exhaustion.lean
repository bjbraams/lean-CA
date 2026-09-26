/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.UnivalentDisk.Geometry
public import Mathlib.Topology.Order.IsLUB

/-!
# Exhaustion of univalent disk images

Given an injective holomorphic map on an open disk, smaller concentric disks give an
exhaustion of its image by relatively compact domains with embedded circle boundaries.
Every compact subset of the image lies in a single term, and each term's closure lies
in the next term. Only holomorphy on the open disk is needed: no boundary extension at
the limiting radius is assumed.

The disk parametrization is an explicit hypothesis. Its existence on arbitrary simply
connected proper planar domains is the separate Riemann mapping theorem.

## Main results

* `Complex.exists_exhaustion_image_ball_of_injOn_holomorphic`: An injective holomorphic disk
  image admits a relatively compact exhaustion by smaller disk images, with nested closures and
  eventual containment of every compact subset. The geometry of each boundary is provided by
  `frontier_image_ball_of_injOn_holomorphic` and
  `isClosedEmbedding_sphere_of_injOn_holomorphic`.
* `Complex.exists_image_ball_neighborhood_of_isCompact`: Any compact set in a univalent disk
  image is contained in a smaller image disk whose compact closure remains in the original
  image. Its boundary is an embedded circle.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section
open Set Metric Filter
open scoped Topology

namespace Complex

/-- An injective holomorphic disk image admits a relatively compact exhaustion by smaller
disk images, with nested closures and eventual containment of every compact subset.
The geometry of each boundary is provided by `frontier_image_ball_of_injOn_holomorphic`
and `isClosedEmbedding_sphere_of_injOn_holomorphic`. -/
theorem exists_exhaustion_image_ball_of_injOn_holomorphic {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball c R)) (hi : InjOn f (ball c R)) :
    ∃ r : ℕ → ℝ, StrictMono r ∧ (∀ n, r n ∈ Ioo 0 R) ∧
      (∀ n, IsOpen (f '' ball c (r n))) ∧
      (∀ n, IsConnected (f '' ball c (r n))) ∧
      (∀ n, IsSimplyConnected (f '' ball c (r n))) ∧
      (∀ n, IsCompact (closure (f '' ball c (r n)))) ∧
      (∀ n, closure (f '' ball c (r n)) ⊆ f '' ball c (r (n + 1))) ∧
      (⋃ n, f '' ball c (r n)) = f '' ball c R ∧
      ∀ K, IsCompact K → K ⊆ f '' ball c R → ∃ n, K ⊆ f '' ball c (r n) := by
  obtain ⟨r, hrm, hr, hlim⟩ := exists_seq_strictMono_tendsto' hR
  have hsub (n : ℕ) : closedBall c (r n) ⊆ ball c R := closedBall_subset_ball (hr n).2
  have hopen (n : ℕ) : IsOpen (f '' ball c (r n)) :=
    isOpen_image_of_injOn_holomorphic isOpen_ball hf hi isOpen_ball
      (ball_subset_closedBall.trans (hsub n))
  have hcl (n : ℕ) : closure (f '' ball c (r n)) = f '' closedBall c (r n) :=
    closure_image_ball (hr n).1 (hf.continuousOn.mono (hsub n))
  have hmono : Monotone (fun n ↦ f '' ball c (r n)) :=
    fun n m hnm ↦ image_mono (ball_subset_ball (hrm.monotone hnm))
  have hcover : (⋃ n, f '' ball c (r n)) = f '' ball c R := by
    apply le_antisymm
    · exact iUnion_subset fun n ↦ image_mono (ball_subset_ball (hr n).2.le)
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨n, hn⟩ := ((tendsto_order.mp hlim).1 (dist z c) hz).exists
      exact mem_iUnion.mpr ⟨n, z, hn, rfl⟩
  refine ⟨r, hrm, hr, hopen, ?_, ?_, ?_, ?_, hcover, ?_⟩
  · intro n
    exact isConnected_image_ball_of_holomorphic hf (hr n).1
      (ball_subset_closedBall.trans (hsub n))
  · intro n
    exact isSimplyConnected_image_ball_of_injOn_holomorphic (hr n).1
      (hf.mono (ball_subset_ball (hr n).2.le)) (hi.mono (ball_subset_ball (hr n).2.le))
  · intro n
    rw [hcl]
    exact isCompact_image_closedBall_of_holomorphic hf (hsub n)
  · intro n
    rw [hcl]
    exact image_mono (closedBall_subset_ball (hrm (Nat.lt_succ_self n)))
  · intro K hK hKU
    exact hK.elim_directed_cover _ hopen (hcover.symm ▸ hKU) hmono.directed_le

/-- Any compact set in a univalent disk image is contained in a smaller image disk whose
compact closure remains in the original image. Its boundary is an embedded circle. -/
theorem exists_image_ball_neighborhood_of_isCompact {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball c R)) (hi : InjOn f (ball c R))
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ f '' ball c R) :
    ∃ r ∈ Ioo 0 R, K ⊆ f '' ball c r ∧ IsOpen (f '' ball c r) ∧
      IsConnected (f '' ball c r) ∧ IsSimplyConnected (f '' ball c r) ∧
      IsCompact (closure (f '' ball c r)) ∧
      closure (f '' ball c r) ⊆ f '' ball c R ∧
      frontier (f '' ball c r) = f '' sphere c r ∧
      Topology.IsClosedEmbedding (fun z : sphere c r ↦ f z) := by
  obtain ⟨r, _, hr, ho, hc, hsc, hk, _, _, hco⟩ :=
    exists_exhaustion_image_ball_of_injOn_holomorphic hR hf hi
  obtain ⟨n, hn⟩ := hco K hK hKU
  have hsub : closedBall c (r n) ⊆ ball c R := closedBall_subset_ball (hr n).2
  refine ⟨r n, hr n, hn, ho n, hc n, hsc n, hk n, ?_, ?_, ?_⟩
  · rw [closure_image_ball (hr n).1 (hf.continuousOn.mono hsub)]
    exact image_mono hsub
  · exact frontier_image_ball_of_injOn_holomorphic isOpen_ball hf hi (hr n).1 hsub
  · exact isClosedEmbedding_sphere_of_injOn_holomorphic hf hi (sphere_subset_closedBall.trans hsub)

end Complex
