/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Injective
public import Topology.Frontier
public import Topology.SimplyConnected
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Geometry of disks under injective holomorphic maps

An injective holomorphic map on a neighborhood of a closed disk maps its open disk to
a bounded open connected domain. Its closure is the image of the closed disk, and its
frontier is the embedded image of the circle. Thus this constructs actual Jordan
boundaries from analytic disk parametrizations without assuming a general Jordan theorem.
No existence of a disk parametrization for an arbitrary simply connected domain is asserted.

## Main results

* `Complex.isOpen_image_of_injOn_holomorphic`: An injective holomorphic function maps open
  subsets of its domain to open sets.
* `Complex.closure_image_ball`: For a map continuous on a closed disk, the closure of the image
  of the open disk is the image of the closed disk. Injectivity is not needed.
* `Complex.frontier_image_ball_of_injOn_holomorphic`: The boundary of the image disk is exactly
  the image circle for an injective holomorphic map on a neighborhood of the closed disk.
* `Complex.isClosedEmbedding_sphere_of_injOn_holomorphic`: Restriction of an injective
  holomorphic map to the circle is a closed embedding.
* `Complex.connectedComponentIn_compl_image_sphere_of_injOn_holomorphic`: The image disk is the
  connected component of the image-circle complement containing the image of its center. In
  particular this constructs a bounded complementary component.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Set Metric Filter
open scoped Topology

namespace Complex

/-- An injective holomorphic function maps open subsets of its domain to open sets. -/
theorem isOpen_image_of_injOn_holomorphic {U V : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hi : InjOn f U)
    (hV : IsOpen V) (hVU : V ⊆ U) : IsOpen (f '' V) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨z, hz, rfl⟩
  have hmap := (hf.analyticOnNhd hU z (hVU hz)).eventually_constant_or_nhds_le_map_nhds
  exact (hmap.resolve_left
    (not_eventually_constant_of_injOn_complex (hU.mem_nhds (hVU hz)) hi))
      (image_mem_map (hV.mem_nhds hz))

/-- Restricting an injective holomorphic map to its open domain gives an open embedding. -/
theorem isOpenEmbedding_of_injOn_holomorphic {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) :
    Topology.IsOpenEmbedding (fun z : U ↦ f z) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuousOn_iff_continuous_domRestrict.mp hf.continuousOn)
    (fun x y h ↦ Subtype.ext (hi x.property y.property h))
  intro V hV
  change IsOpen ((fun z : U ↦ f z) '' V)
  simpa only [image_image, Function.comp_def] using
    (isOpen_image_of_injOn_holomorphic hU hf hi
      (hU.isOpenMap_subtype_val V hV) (by rintro _ ⟨z, _, rfl⟩; exact z.property))

/-- Injective holomorphic maps preserve simple connectedness of open domains. -/
theorem isSimplyConnected_image_of_injOn_holomorphic {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hi : InjOn f U)
    (hc : IsSimplyConnected U) : IsSimplyConnected (f '' U) := by
  let : SimplyConnectedSpace U := hc
  let e := (isOpenEmbedding_of_injOn_holomorphic hU hf hi).isEmbedding.toHomeomorph
  have h := e.symm.toHomotopyEquiv.simplyConnectedSpace
  have he : range (fun z : U ↦ f z) = f '' U := by
    ext z
    simp
  change IsSimplyConnected (range (fun z : U ↦ f z)) at h
  rwa [he] at h

/-- An injective holomorphic image of a nonempty disk is simply connected. -/
theorem isSimplyConnected_image_ball_of_injOn_holomorphic {f : ℂ → ℂ}
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball c R))
    (hi : InjOn f (ball c R)) : IsSimplyConnected (f '' ball c R) :=
  isSimplyConnected_image_of_injOn_holomorphic isOpen_ball hf hi
    ((convex_ball c R).isSimplyConnected (nonempty_ball.mpr hR))

/-- The image of a closed disk is compact when the map is holomorphic on its neighborhood. -/
theorem isCompact_image_closedBall_of_holomorphic {U : Set ℂ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) {c : ℂ} {R : ℝ} (hRU : closedBall c R ⊆ U) :
    IsCompact (f '' closedBall c R) :=
  (isCompact_closedBall c R).image_of_continuousOn (hf.continuousOn.mono hRU)

/-- A nondegenerate disk has connected image under a holomorphic function. -/
theorem isConnected_image_ball_of_holomorphic {U : Set ℂ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hRU : ball c R ⊆ U) : IsConnected (f '' ball c R) :=
  (convex_ball c R).isConnected (nonempty_ball.mpr hR) |>.image f (hf.continuousOn.mono hRU)

/-- For a map continuous on a closed disk, the closure of the image of the open disk is
the image of the closed disk. Injectivity is not needed. -/
theorem closure_image_ball {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f (closedBall c R)) :
    closure (f '' ball c R) = f '' closedBall c R := by
  apply le_antisymm
  · exact closure_minimal (image_mono ball_subset_closedBall)
      ((isCompact_closedBall c R).image_of_continuousOn hf).isClosed
  · have h := hf
    rw [← closure_ball c hR.ne'] at h ⊢
    exact h.image_closure

/-- The boundary of the image disk is exactly the image circle for an injective
holomorphic map on a neighborhood of the closed disk. -/
theorem frontier_image_ball_of_injOn_holomorphic {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hi : InjOn f U)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hRU : closedBall c R ⊆ U) :
    frontier (f '' ball c R) = f '' sphere c R := by
  rw [frontier, (isOpen_image_of_injOn_holomorphic hU hf hi isOpen_ball
    (ball_subset_closedBall.trans hRU)).interior_eq,
    closure_image_ball hR (hf.continuousOn.mono hRU)]
  ext z
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hn⟩
    refine ⟨x, ?_, rfl⟩
    rw [← closedBall_sdiff_ball]
    exact ⟨hx, fun h ↦ hn ⟨x, h, rfl⟩⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, sphere_subset_closedBall hx, rfl⟩, ?_⟩
    rintro ⟨y, hy, he⟩
    have hxy := hi (hRU (ball_subset_closedBall hy)) (hRU (sphere_subset_closedBall hx)) he
    exact sphere_disjoint_ball.le_bot ⟨hx, hxy ▸ hy⟩

/-- Restriction of an injective holomorphic map to the circle is a closed embedding. -/
theorem isClosedEmbedding_sphere_of_injOn_holomorphic {U : Set ℂ}
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hi : InjOn f U)
    {c : ℂ} {R : ℝ} (hRU : sphere c R ⊆ U) :
    Topology.IsClosedEmbedding (fun z : sphere c R ↦ f z) := by
  apply (continuousOn_iff_continuous_domRestrict.mp (hf.continuousOn.mono hRU)).isClosedEmbedding
  intro x y hxy
  exact Subtype.ext (hi (hRU x.property) (hRU y.property) hxy)

/-- The image disk is the connected component of the image-circle complement containing
the image of its center. In particular this constructs a bounded complementary component. -/
theorem connectedComponentIn_compl_image_sphere_of_injOn_holomorphic
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hi : InjOn f U)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hRU : closedBall c R ⊆ U) :
    connectedComponentIn (f '' sphere c R)ᶜ (f c) = f '' ball c R := by
  rw [← frontier_image_ball_of_injOn_holomorphic hU hf hi hR hRU]
  exact (isOpen_image_of_injOn_holomorphic hU hf hi isOpen_ball
    (ball_subset_closedBall.trans hRU)).connectedComponentIn_compl_frontier
      (isConnected_image_ball_of_holomorphic hf hR
        (ball_subset_closedBall.trans hRU)).isPreconnected ⟨c, mem_ball_self hR, rfl⟩

end Complex
