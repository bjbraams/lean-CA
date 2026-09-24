/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.HasPrimitives
public import ComplexAnalysis.CauchyIntegral

/-!
# Primitives pulled back along continuous maps

Local holomorphic primitives pull back along a continuous map from a simply
connected, locally path connected space. Their locally constant differences
glue to a continuous function on the source with the same local increments.
The source need not have a differentiable structure, and the planar target
domain need not be simply connected.

Along a path in the source whose image is differentiable and curve integrable,
the increments of this function compute the complex curve integral. This is
useful for continuous homotopies, without smoothing the interior of the homotopy.

## Main results

* `DifferentiableOn.exists_continuous_primitive_pullback`: A holomorphic function has a
  continuous primitive after pullback to a simply connected space. Locally its increments are
  those of a holomorphic primitive composed with the map.
* `Complex.curveIntegral_map_eq_sub_of_locally_primitive`: A continuous function locally
  obtained from primitives computes the integral along the image of a path. Only the image path
  needs to be differentiable and integrable.
* `Complex.curveIntegral_eq_sub_of_locally_primitive`: A parametrization in the source computes
  a planar curve integral from the increments of a pulled-back primitive. The parametrization
  need only be continuous.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology unitInterval

/-- A holomorphic function has a continuous primitive after pullback to a simply connected
space. Locally its increments are those of a holomorphic primitive composed with the map. -/
theorem DifferentiableOn.exists_continuous_primitive_pullback
    {X F : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {U : Set ℂ} {f : ℂ → F} (hf : DifferentiableOn ℂ f U)
    (hU : IsOpen U) {g : X → ℂ} (hg : Continuous g) (hgU : range g ⊆ U)
    (x₀ : X) (v₀ : F) :
    ∃ Q : X → F, Continuous Q ∧ Q x₀ = v₀ ∧ ∀ x, ∃ P : ℂ → F,
      HasDerivAt P (f (g x)) (g x) ∧
      ∀ᶠ y in 𝓝 x, Q y = Q x + (P (g y) - P (g x)) := by
  classical
  have hlocal (x : X) : ∃ r > 0, Complex.IsExactOn f (ball (g x) r) := by
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU (g x) (hgU (mem_range_self x))
    exact ⟨r, hr, (hf.mono hsub).isExactOn_ball⟩
  choose r hr P hP using hlocal
  let V : X → Set X := fun x => g ⁻¹' ball (g x) (r x)
  have hV : ∀ x, IsOpen (V x) := fun x => isOpen_ball.preimage hg
  have hcover : ∀ x : X, ∃ i, x ∈ V i := fun x => ⟨x, mem_ball_self (hr x)⟩
  have hdiff : ∀ i j x : X, x ∈ V i ∩ V j →
      ∀ᶠ y in 𝓝 x, P i (g y) - P j (g y) = P i (g x) - P j (g x) := by
    intro i j x hx
    have hd : ∀ z ∈ ball (g i) (r i) ∩ ball (g j) (r j),
        HasDerivAt (fun w => P i w - P j w) 0 z := by
      intro z hz
      change HasDerivAt (P i - P j) 0 z
      simpa only [sub_self] using (hP i z hz.1).sub (hP j z hz.2)
    filter_upwards [((hV i).inter (hV j)).mem_nhds hx] with y hy
    exact (isOpen_ball.inter isOpen_ball).is_const_of_deriv_eq_zero
      ((convex_ball (g i) (r i)).inter (convex_ball (g j) (r j))).isPreconnected
      (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hd z hz).deriv) hy hx
  obtain ⟨Q, hQ₀, hQ⟩ := exists_locally_eq_add_of_locally_constant_sub
    V hV hcover (fun i x => P i (g x)) hdiff x₀ v₀
  refine ⟨Q, ?_, hQ₀, fun x => ⟨P x, hP x (g x) (mem_ball_self (hr x)),
    hQ x x (mem_ball_self (hr x))⟩⟩
  apply continuous_iff_continuousAt.mpr
  intro x
  have hc : ContinuousAt (P x ∘ g) x :=
    (hP x (g x) (mem_ball_self (hr x))).continuousAt.comp hg.continuousAt
  have hc' : ContinuousAt (fun y => Q x + (P x (g y) - P x (g x))) x :=
    continuousAt_const.add (hc.sub continuousAt_const)
  exact hc'.congr_of_eventuallyEq (hQ x x (mem_ball_self (hr x)))

namespace Complex

/-- A continuous function locally obtained from primitives computes the integral along
the image of a path. Only the image path needs to be differentiable and integrable. -/
theorem curveIntegral_map_eq_sub_of_locally_primitive
    {X F : Type*} [TopologicalSpace X] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {g : X → ℂ} (hg : Continuous g) {Q : X → F} (hQ : Continuous Q)
    {f : ℂ → F} (hlocal : ∀ x, ∃ P : ℂ → F, HasDerivAt P (f (g x)) (g x) ∧
      ∀ᶠ y in 𝓝 x, Q y = Q x + (P (g y) - P (g x)))
    {x y : X} (η : Path x y) (hη : DifferentiableOn ℝ (η.map hg).extend I)
    (hint : CurveIntegrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z))
      (η.map hg)) :
    curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) (η.map hg) =
      Q y - Q x := by
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (Q ∘ η.extend)
        (curveIntegralFun (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z))
          (η.map hg) t) t := by
    obtain ⟨P, hP, he⟩ := hlocal (η.extend t)
    have htI : t ∈ I := ⟨ht.1.le, ht.2.le⟩
    rw [curveIntegralFun_def, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    have hder := (hP.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
      ((hη t htI).differentiableAt (Icc_mem_nhds ht.1 ht.2)).hasDerivAt
    apply ((hder.sub_const (P (g (η.extend t)))).const_add (Q (η.extend t))).congr_of_eventuallyEq
    exact η.continuous_extend.continuousAt.eventually he
  simpa only [curveIntegral_def, Function.comp_apply, η.extend_one, η.extend_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      (hQ.comp η.continuous_extend).continuousOn hd hint

/-- A parametrization in the source computes a planar curve integral from the increments
of a pulled-back primitive. The parametrization need only be continuous. -/
theorem curveIntegral_eq_sub_of_locally_primitive
    {X F : Type*} [TopologicalSpace X] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {g : X → ℂ} (hg : Continuous g) {Q : X → F} (hQ : Continuous Q)
    {f : ℂ → F} (hlocal : ∀ x, ∃ P : ℂ → F, HasDerivAt P (f (g x)) (g x) ∧
      ∀ᶠ y in 𝓝 x, Q y = Q x + (P (g y) - P (g x)))
    {r : I → X} (hr : Continuous r) {a b : ℂ} {γ : Path a b}
    (hcomp : ∀ t, g (r t) = γ t) (hγ : DifferentiableOn ℝ γ.extend I)
    (hint : CurveIntegrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ) :
    curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ = Q (r 1) - Q (r 0) := by
  let η : Path (r 0) (r 1) := ⟨⟨r, hr⟩, rfl, rfl⟩
  have he : η.map hg = γ.cast ((hcomp 0).trans γ.source) ((hcomp 1).trans γ.target) := by
    ext t
    exact hcomp t
  have h := curveIntegral_map_eq_sub_of_locally_primitive hg hQ hlocal η
    (by simpa only [he, Path.extend_cast] using hγ)
    (by simpa only [he, curveIntegrable_cast_iff] using hint)
  simpa only [he, curveIntegral_cast] using h

end Complex
