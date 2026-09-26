/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Cycle.Residue
public import Analysis.Integral.CurveIntegral.SmoothConcat
public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

/-!
# Piecewise-`C¹` closed curves as cycles

The constituents of a `Complex.Cycle` are closed `C¹` curves. A closed curve made of several
`C¹` pieces meeting at corners, such as the boundary of a polygon, a rectangle or a keyhole
contour, is turned into such a curve by the smooth concatenation `Path.smoothConcat`, which
traverses each piece with a reparametrization that is flat at both of its ends. The integral
of a one-form, and hence the index, of the resulting closed curve is the sum over the pieces, so
the homology forms of Cauchy's theorem, Cauchy's formula and the residue theorem apply directly
to piecewise-`C¹` contours.

## Main definitions

* `Complex.Loop.piecewise x γ hx`: the closed curve through the chain of paths `γ i` from `x i`
  to `x (i + 1)`, `i < n`, with `x n = x 0`.
* `Complex.Loop.polygon v hv`: the closed polygon with vertices `v 0, …, v (n - 1)`.

## Main results

* `Complex.Loop.contDiffOn_piecewise`: a piecewise loop with `C¹` pieces is `C¹`, so that
  `Cycle.single (Loop.piecewise x γ hx)` satisfies `Cycle.IsC1`.
* `Complex.Loop.range_piecewise_subset`: the loop lies on the union of its pieces.
* `Complex.Loop.curveIntegral_piecewise`: integrals over the loop are sums over the pieces.
* `Complex.Loop.curveIndex_piecewise`: the index of the loop is the sum of the pieces'
  Cauchy-kernel integrals divided by `2πi`.
* `Complex.Loop.sum_curveIntegral_eq_zero_of_piecewise`,
  `Complex.Loop.sum_curveIntegral_sub_inv_smul_of_piecewise`,
  `Complex.Loop.sum_curveIntegral_eq_sum_residue_of_piecewise`: Cauchy's theorem, Cauchy's
  formula and the residue theorem for piecewise-`C¹` closed curves, stated entirely in terms of
  integrals over the pieces.
* `Complex.Loop.contDiffOn_polygon`, `Complex.Loop.curveIntegral_polygon`: polygons are `C¹`
  closed curves, and their integrals are sums of edge integrals written over `[0, 1]`.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped unitInterval

namespace Complex

namespace Loop

variable {n : ℕ} {x : ℕ → ℂ} (γ : (i : Fin n) → Path (x i) (x (i + 1)))

/-- The closed curve through a chain of paths `γ i` from `x i` to `x (i + 1)`, `i < n`, with
`x n = x 0`, smoothly concatenated so that corners between the pieces are allowed. -/
def piecewise (hx : x n = x 0) : Loop := ⟨x 0, (Path.smoothConcat γ).cast rfl hx.symm⟩

variable (hx : x n = x 0)

/-- A piecewise loop with `C¹` pieces is `C¹`. -/
theorem contDiffOn_piecewise (hγ : ∀ i, ContDiffOn ℝ 1 (γ i).extend I) :
    ContDiffOn ℝ 1 (piecewise γ hx).2.extend I :=
  Path.contDiffOn_smoothConcat_extend γ hγ

/-- A single piecewise loop with `C¹` pieces is a `C¹` cycle. -/
theorem isC1_single_piecewise (hγ : ∀ i, ContDiffOn ℝ 1 (γ i).extend I) :
    (Cycle.single (piecewise γ hx)).IsC1 :=
  fun _ ↦ contDiffOn_piecewise γ hx hγ

/-- A piecewise loop with at least one piece lies on the union of its pieces. -/
theorem range_piecewise_subset (hn : 0 < n) :
    range (piecewise γ hx).2 ⊆ ⋃ i, range (γ i) :=
  Path.range_smoothConcat_subset γ hn

/-- The range of the single cycle formed by a piecewise loop with at least one piece lies on the
union of the pieces. -/
theorem range_single_piecewise_subset (hn : 0 < n) :
    (Cycle.single (piecewise γ hx)).range ⊆ ⋃ i, range (γ i) :=
  iUnion_subset fun _ ↦ range_piecewise_subset γ hx hn

/-- **Integrals over a piecewise loop.** The curve integral of a one-form over a piecewise loop
with differentiable, integrable pieces is the sum of the integrals over the pieces. -/
theorem curveIntegral_piecewise {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ω : ℂ → ℂ →L[ℂ] F) (hγ : ∀ i, DifferentiableOn ℝ (γ i).extend I)
    (hint : ∀ i, CurveIntegrable ω (γ i)) :
    curveIntegral ω (piecewise γ hx).2 = ∑ i, curveIntegral ω (γ i) := by
  rw [piecewise, curveIntegral_cast, Path.curveIntegral_smoothConcat γ ω hγ hint]

/-- The integral of a one-form over the single cycle formed by a piecewise loop is the sum of
the integrals over the pieces. -/
theorem integral_single_piecewise {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ω : ℂ → ℂ →L[ℂ] F) (hγ : ∀ i, DifferentiableOn ℝ (γ i).extend I)
    (hint : ∀ i, CurveIntegrable ω (γ i)) :
    (Cycle.single (piecewise γ hx)).integral ω = ∑ i, curveIntegral ω (γ i) := by
  change ∑ _i : Fin 1, _ = _
  rw [Fin.sum_univ_one]
  exact curveIntegral_piecewise γ hx ω hγ hint

/-- The index of a piecewise loop about a point off its `C¹` pieces is the sum of the pieces'
Cauchy-kernel integrals divided by `2πi`. -/
theorem curveIndex_piecewise (hγ : ∀ i, ContDiffOn ℝ 1 (γ i).extend I) {w : ℂ}
    (hw : ∀ i t, γ i t ≠ w) :
    curveIndex (piecewise γ hx).2 w = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      ∑ i, curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) (γ i) := by
  rw [curveIndex, curveIntegral_piecewise γ hx _ (fun i ↦ (hγ i).differentiableOn one_ne_zero)
    fun i ↦ curveIntegrable_of_continuousOn (U := {w}ᶜ) (f := fun z ↦ (z - w)⁻¹)
      (ContinuousOn.inv₀ (f := fun z : ℂ ↦ z - w) (by fun_prop) fun z hz ↦ sub_ne_zero.mpr hz)
      (hγ i) fun t ↦ hw i t]

/-- The index of the single cycle formed by a piecewise loop, about a point off its `C¹` pieces,
is the sum of the pieces' Cauchy-kernel integrals divided by `2πi`. -/
theorem index_single_piecewise (hγ : ∀ i, ContDiffOn ℝ 1 (γ i).extend I) {w : ℂ}
    (hw : ∀ i t, γ i t ≠ w) :
    (Cycle.single (piecewise γ hx)).index w = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      ∑ i, curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) (γ i) := by
  change ∑ _i : Fin 1, _ = _
  rw [Fin.sum_univ_one]
  exact curveIndex_piecewise γ hx hγ hw

/-- `2πi` times the index of a piecewise loop is the sum of the pieces' Cauchy-kernel
integrals. -/
private theorem two_pi_I_mul_index_single_piecewise (hγ : ∀ i, ContDiffOn ℝ 1 (γ i).extend I)
    {w : ℂ} (hw : ∀ i t, γ i t ≠ w) :
    2 * (Real.pi : ℂ) * Complex.I * (Cycle.single (piecewise γ hx)).index w =
      ∑ i, curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) (γ i) := by
  rw [index_single_piecewise γ hx hγ hw, ← mul_assoc, mul_inv_cancel₀ two_pi_I_ne_zero, one_mul]

section Cauchy

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {U : Set ℂ}

include hx

/-- The hypotheses of the cycle theorems for the single cycle formed by a piecewise loop, from
hypotheses on the pieces. -/
private theorem single_piecewise_hyps (hn : 0 < n) (hγ : ∀ i, ContDiffOn ℝ 1 (γ i).extend I)
    (hγU : ∀ i t, γ i t ∈ U)
    (hind : ∀ w ∉ U,
      ∑ i, curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) (γ i) = 0) :
    (Cycle.single (piecewise γ hx)).IsC1 ∧ (Cycle.single (piecewise γ hx)).range ⊆ U ∧
      ∀ w ∉ U, (Cycle.single (piecewise γ hx)).index w = 0 := by
  refine ⟨isC1_single_piecewise γ hx hγ,
    (range_single_piecewise_subset γ hx hn).trans (iUnion_subset fun i ↦ ?_), fun w hw ↦ ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact hγU i t
  · rw [index_single_piecewise γ hx hγ fun i t h ↦ hw (by rw [← h]; exact hγU i t), hind w hw,
      mul_zero]

/-- **Cauchy's theorem for a piecewise-`C¹` closed curve.** If the `C¹` pieces of a closed curve
lie in an open set `U` and their Cauchy-kernel integrals sum to zero about every point outside
`U`, then the integrals of every holomorphic function on `U` over the pieces sum to zero. -/
theorem sum_curveIntegral_eq_zero_of_piecewise (hU : IsOpen U)
    (hγ : ∀ i, ContDiffOn ℝ 1 (γ i).extend I) (hγU : ∀ i t, γ i t ∈ U)
    (hind : ∀ w ∉ U,
      ∑ i, curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) (γ i) = 0)
    {f : ℂ → F} (hf : DifferentiableOn ℂ f U) :
    ∑ i, curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) (γ i) = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨hC1, hΓU, hΓind⟩ := single_piecewise_hyps γ hx hn hγ hγU hind
  rw [← integral_single_piecewise γ hx _ (fun i ↦ (hγ i).differentiableOn one_ne_zero)
    fun i ↦ curveIntegrable_of_continuousOn hf.continuousOn (hγ i) (hγU i)]
  exact Cycle.integral_eq_zero _ hU hC1 hΓU hΓind hf

/-- **Cauchy's integral formula for a piecewise-`C¹` closed curve.** Under the hypotheses of
`sum_curveIntegral_eq_zero_of_piecewise`, for `z ∈ U` off the pieces, the Cauchy integrals of `f`
over the pieces sum to the Cauchy-kernel integrals times `f z`. -/
theorem sum_curveIntegral_sub_inv_smul_of_piecewise (hU : IsOpen U)
    (hγ : ∀ i, ContDiffOn ℝ 1 (γ i).extend I) (hγU : ∀ i t, γ i t ∈ U)
    (hind : ∀ w ∉ U,
      ∑ i, curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) (γ i) = 0)
    {f : ℂ → F} (hf : DifferentiableOn ℂ f U) {z : ℂ} (hz : z ∈ U) (hzγ : ∀ i t, γ i t ≠ z) :
    ∑ i, curveIntegral (fun w ↦ ContinuousLinearMap.toSpanSingleton ℂ ((w - z)⁻¹ • f w)) (γ i) =
      (∑ i, curveIntegral (fun w ↦ ContinuousLinearMap.toSpanSingleton ℂ ((w - z)⁻¹)) (γ i)) •
        f z := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨hC1, hΓU, hΓind⟩ := single_piecewise_hyps γ hx hn hγ hγU hind
  have hcont : ContinuousOn (fun w ↦ (w - z)⁻¹ • f w) ({z}ᶜ ∩ U) :=
    ((ContinuousOn.inv₀ (f := fun w : ℂ ↦ w - z) (by fun_prop) fun w hw ↦
      sub_ne_zero.mpr hw.1).smul (hf.continuousOn.mono inter_subset_right))
  rw [← integral_single_piecewise γ hx _ (fun i ↦ (hγ i).differentiableOn one_ne_zero)
    fun i ↦ curveIntegrable_of_continuousOn hcont (hγ i) fun t ↦ ⟨hzγ i t, hγU i t⟩,
    ← two_pi_I_mul_index_single_piecewise γ hx hγ hzγ]
  exact Cycle.integral_sub_inv_smul_eq_index_smul _ hU hC1 hΓU hΓind hf hz
    fun hzΓ ↦ by
      obtain ⟨i, hi⟩ := mem_iUnion.mp (range_single_piecewise_subset γ hx hn hzΓ)
      obtain ⟨t, ht⟩ := hi
      exact hzγ i t ht

/-- **The residue theorem for a piecewise-`C¹` closed curve.** If the `C¹` pieces of a closed
curve lie in `U \ S` for an open set `U` and a finite set `S`, and their Cauchy-kernel integrals
sum to zero about every point outside `U`, then for `f` holomorphic on `U \ S` the integrals
over the pieces sum to `∑ a ∈ S, (∑ i, ∫_{γ i} dz / (z - a)) • Res(f, a)`. -/
theorem sum_curveIntegral_eq_sum_residue_of_piecewise (hU : IsOpen U) (S : Finset ℂ)
    (hγ : ∀ i, ContDiffOn ℝ 1 (γ i).extend I) (hγU : ∀ i t, γ i t ∈ U \ S)
    (hind : ∀ w ∉ U,
      ∑ i, curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) (γ i) = 0)
    {f : ℂ → F} (hf : DifferentiableOn ℂ f (U \ S)) :
    ∑ i, curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) (γ i) =
      ∑ a ∈ S, (∑ i, curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - a)⁻¹))
        (γ i)) • residue f a := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨hC1, hΓU, hΓind⟩ := single_piecewise_hyps γ hx hn hγ (fun i t ↦ (hγU i t).1) hind
  have hΓUS : (Cycle.single (piecewise γ hx)).range ⊆ U \ S :=
    (range_single_piecewise_subset γ hx hn).trans (iUnion_subset fun i ↦ by
      rintro _ ⟨t, rfl⟩
      exact hγU i t)
  rw [← integral_single_piecewise γ hx _ (fun i ↦ (hγ i).differentiableOn one_ne_zero)
    fun i ↦ curveIntegrable_of_continuousOn hf.continuousOn (hγ i) (hγU i),
    Cycle.integral_eq_sum_index_smul_residue _ hU S hC1 hΓUS hΓind hf]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [two_pi_I_mul_index_single_piecewise γ hx hγ fun i t h ↦ (hγU i t).2 (h ▸ ha)]

end Cauchy

section Polygon

/-- A segment path is smooth. -/
theorem contDiffOn_segment_extend {m : ℕ∞} (a b : ℂ) :
    ContDiffOn ℝ m (Path.segment a b).extend I :=
  (AffineMap.contDiff_lineMap a b).contDiffOn.congr (Path.eqOn_extend_segment a b)

variable (v : ℕ → ℂ)

/-- The closed polygon with vertices `v 0, …, v (n - 1)` (and `v n = v 0`): the edges are the
segments from `v i` to `v (i + 1)`, smoothly concatenated. -/
def polygon (hv : v n = v 0) : Loop :=
  piecewise (fun i : Fin n ↦ Path.segment (v i) (v (i + 1))) hv

variable {v} (hv : v n = v 0)

/-- A polygon is a `C¹` closed curve. -/
theorem contDiffOn_polygon : ContDiffOn ℝ 1 (polygon v hv).2.extend I :=
  contDiffOn_piecewise _ hv fun _ ↦ contDiffOn_segment_extend _ _

/-- A single polygon is a `C¹` cycle. -/
theorem isC1_single_polygon : (Cycle.single (polygon v hv)).IsC1 :=
  isC1_single_piecewise _ hv fun _ ↦ contDiffOn_segment_extend _ _

/-- A polygon with at least one edge lies on the union of its edges. -/
theorem range_polygon_subset (hn : 0 < n) :
    range (polygon v hv).2 ⊆ ⋃ i : Fin n, segment ℝ (v i) (v (i + 1)) := by
  refine (range_piecewise_subset _ hv hn).trans (iUnion_mono fun i ↦ ?_)
  rw [Path.range_segment]

/-- **Integrals over a polygon.** The curve integral of a one-form continuous on the edges of a
polygon is the sum of the edge integrals
`∫₀¹ ω (v i + t (v (i + 1) - v i)) (v (i + 1) - v i) dt`. -/
theorem curveIntegral_polygon {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ω : ℂ → ℂ →L[ℂ] F) (hω : ∀ i : Fin n, ContinuousOn ω (segment ℝ (v i) (v (i + 1)))) :
    curveIntegral ω (polygon v hv).2 = ∑ i : Fin n,
      ∫ t in (0 : ℝ)..1, ω (AffineMap.lineMap (v i) (v (i + 1)) t) (v (i + 1) - v i) := by
  rw [polygon, curveIntegral_piecewise _ hv ω
    (fun _ ↦ (contDiffOn_segment_extend _ _).differentiableOn one_ne_zero)
    fun i ↦ (hω i).curveIntegrable_of_contDiffOn (contDiffOn_segment_extend _ _)
      fun t ↦ Path.range_segment (v i) (v (i + 1)) ▸ mem_range_self t]
  exact Finset.sum_congr rfl fun i _ ↦ curveIntegral_segment ω _ _

end Polygon

end Loop

end Complex
