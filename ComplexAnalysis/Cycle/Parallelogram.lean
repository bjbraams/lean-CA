/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.CurveIndex.Homotopy
public import ComplexAnalysis.Cycle.Piecewise
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# The boundary of a parallelogram as a smooth cycle, and its index

The boundary of the parallelogram with vertices `c, c + w1, c + w1 + w2, c + w2` is the closed
polygon through these vertices (`Complex.Loop.polygon`), a single `C^∞` closed curve: the four
edges are smoothly concatenated with reparametrizations that are flat at the corners. Curve
integrals around it are sums of four straight edge integrals over `[0, 1]`
(`Complex.curveIntegral_parallelogramLoop`).

For a point `w` outside the closed parallelogram, the analytic index of the boundary about
`w` vanishes: `parallelogramLoop` is nullhomotopic within the closed (convex) parallelogram
by coning it toward the vertex `c`, a straight-line homotopy that avoids every exterior point
automatically, by convexity.

For `w1, w2` positively oriented (`Im (conj w1 * w2) > 0`) and `w` strictly inside the open
parallelogram, the index is `1`. Each of the four straight edges'
contribution to the real "turning" integral `∫ Im [γ'/(γ - w)]` is computed as an explicit
`Real.arctan` antiderivative (justified by the Lagrange identity, which makes the relevant
quadratic denominator positive-definite); `Real.arctan`'s range bound then gives, for free,
that each edge's contribution lies in `(0, π)`, so the total lies in `(0, 4π)`. Since the
index is already known to be an integer (`Complex.exists_int_curveIndex`), this pins it to
exactly `1` without ever computing the total directly or gluing branches across corners.

## Main definitions

* `Complex.parallelogramVertex c w1 w2`: the vertices, in order of traversal.
* `Complex.parallelogramLoop c w1 w2`: the parallelogram boundary as a `Path c c`, the closed
  polygon through the vertices.
* `Complex.parallelogramFun c w1 w2`: its `C^∞` parametrization `ℝ → ℂ`.
* `Complex.parallelogramBoundary c w1 w2`: the union of the four edges.
* `Complex.closedParallelogram c w1 w2`: the closed (filled) parallelogram.

## Main results

* `Complex.curveIndex_parallelogramLoop_eq_zero`: the index of the parallelogram boundary
  vanishes at every point outside the closed parallelogram.
* `Complex.curveIndex_parallelogramLoop_eq_one`: **the index of the parallelogram boundary is
  `1` at every point of the open parallelogram**, for positively oriented `w1, w2`.
* `Complex.curveIntegral_parallelogramLoop`: integrals around the parallelogram as sums of four
  straight edge integrals.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Section IV.2 (polygons as chains).
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology unitInterval ComplexConjugate

namespace Complex

/-- The vertices `c, c + w1, c + w1 + w2, c + w2, c` of the parallelogram boundary, listed in
the order of traversal and closing up at index `4`. -/
def parallelogramVertex (c w1 w2 : ℂ) : ℕ → ℂ
  | 0 => c
  | 1 => c + w1
  | 2 => c + w1 + w2
  | 3 => c + w2
  | _ => c

/-- The parallelogram boundary with vertices `c, c + w1, c + w1 + w2, c + w2`, as the closed
polygon through these vertices (`Complex.Loop.polygon`), a `C^∞` closed path. The traversal is
counterclockwise when `0 < (conj w1 * w2).im`. -/
def parallelogramLoop (c w1 w2 : ℂ) : Path c c :=
  (Loop.polygon (n := 4) (parallelogramVertex c w1 w2) rfl).2

/-- The boundary of the parallelogram, as the union of its four edges. -/
def parallelogramBoundary (c w1 w2 : ℂ) : Set ℂ :=
  ⋃ i : Fin 4, segment ℝ (parallelogramVertex c w1 w2 i) (parallelogramVertex c w1 w2 (i + 1))

/-- Each edge lies in the boundary of the parallelogram. -/
theorem segment_subset_parallelogramBoundary (c w1 w2 : ℂ) (i : Fin 4) :
    segment ℝ (parallelogramVertex c w1 w2 i) (parallelogramVertex c w1 w2 (i + 1)) ⊆
      parallelogramBoundary c w1 w2 :=
  subset_iUnion (fun i : Fin 4 ↦ segment ℝ (parallelogramVertex c w1 w2 i)
    (parallelogramVertex c w1 w2 (i + 1))) i

/-- **Integrals around the parallelogram.** The curve integral of a one-form continuous on the
boundary is the sum of the four edge integrals in the affine parametrization over `[0, 1]`. -/
theorem curveIntegral_parallelogramLoop {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {c w1 w2 : ℂ} (ω : ℂ → ℂ →L[ℂ] F) (hω : ContinuousOn ω (parallelogramBoundary c w1 w2)) :
    curveIntegral ω (parallelogramLoop c w1 w2) = ∑ i : Fin 4,
      ∫ t in (0 : ℝ)..1, ω (AffineMap.lineMap (parallelogramVertex c w1 w2 i)
        (parallelogramVertex c w1 w2 (i + 1)) t)
        (parallelogramVertex c w1 w2 (i + 1) - parallelogramVertex c w1 w2 i) :=
  Loop.curveIntegral_polygon _ ω fun i ↦ hω.mono (segment_subset_parallelogramBoundary c w1 w2 i)

/-- The parametrization `ℝ → ℂ` of the parallelogram boundary: the smooth concatenation of the
four edges, each traversed on a quarter of `[0, 1]`. -/
def parallelogramFun (c w1 w2 : ℂ) : ℝ → ℂ :=
  Path.smoothConcatFun (parallelogramVertex c w1 w2) fun _ : Fin 4 ↦ Path.segment _ _

/-- The explicit form of the parametrization: each of the four terms is flat (all derivatives
vanish) at its own transition. -/
theorem parallelogramFun_eq (c w1 w2 : ℂ) (s : ℝ) :
    parallelogramFun c w1 w2 s =
      c + ((Real.smoothTransition (4 * s - 0) - Real.smoothTransition (4 * s - 2) : ℝ) : ℂ) * w1
        + ((Real.smoothTransition (4 * s - 1) - Real.smoothTransition (4 * s - 3) : ℝ) : ℂ) *
          w2 := by
  have hseg : ∀ a b : ℂ, ∀ s : ℝ, (Path.segment a b).extend (Real.smoothTransition s) =
      a + (Real.smoothTransition s : ℂ) * (b - a) := fun a b s ↦ by
    rw [Path.eqOn_extend_segment a b ⟨Real.smoothTransition.nonneg _,
      Real.smoothTransition.le_one _⟩, AffineMap.lineMap_apply_module']
    simp only [Complex.real_smul]
    ring
  simp only [parallelogramFun, Path.smoothConcatFun, Fin.sum_univ_four, hseg]
  simp [parallelogramVertex]
  ring

/-- The extension of the parallelogram loop to `ℝ` is `parallelogramFun`. -/
theorem parallelogramLoop_extend (c w1 w2 : ℂ) :
    ((parallelogramLoop c w1 w2).extend : ℝ → ℂ) = parallelogramFun c w1 w2 :=
  Path.smoothConcat_extend _

/-- The parallelogram loop at a parameter `t ∈ [0, 1]` is `parallelogramFun t`. -/
@[simp]
theorem parallelogramLoop_apply (c w1 w2 : ℂ) (t : I) :
    parallelogramLoop c w1 w2 t = parallelogramFun c w1 w2 t := by
  rw [← Path.extend_extends', parallelogramLoop_extend]

/-- `parallelogramFun` is `C^∞` on all of `ℝ`. -/
theorem contDiff_parallelogramFun (c w1 w2 : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (parallelogramFun c w1 w2) :=
  Path.contDiff_smoothConcatFun _ fun _ ↦ Loop.contDiffOn_segment_extend _ _

/-- `parallelogramFun` is continuous. -/
theorem continuous_parallelogramFun (c w1 w2 : ℂ) : Continuous (parallelogramFun c w1 w2) :=
  Path.continuous_smoothConcatFun _

/-- The parametrization starts at the base vertex. -/
theorem parallelogramFun_zero (c w1 w2 : ℂ) : parallelogramFun c w1 w2 0 = c :=
  Path.smoothConcatFun_zero _

/-- The parametrization returns to the base vertex, closing the loop. -/
theorem parallelogramFun_one (c w1 w2 : ℂ) : parallelogramFun c w1 w2 1 = c :=
  Path.smoothConcatFun_one _

/-- The parallelogram loop is `C^1` (indeed `C^∞`) on `[0, 1]`. -/
theorem contDiffOn_parallelogramLoop_extend (c w1 w2 : ℂ) :
    ContDiffOn ℝ 1 (parallelogramLoop c w1 w2).extend I :=
  Loop.contDiffOn_polygon _

/-- The closed (filled) parallelogram with vertices `c, c + w1, c + w1 + w2, c + w2`. -/
def closedParallelogram (c w1 w2 : ℂ) : Set ℂ :=
  (fun p : ℝ × ℝ ↦ c + (p.1 : ℂ) * w1 + (p.2 : ℂ) * w2) '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)

/-- The parallelogram loop stays within the closed parallelogram at every parameter, not only
at the vertices. -/
theorem parallelogramFun_mem_closedParallelogram (c w1 w2 : ℂ) (s : ℝ) :
    parallelogramFun c w1 w2 s ∈ closedParallelogram c w1 w2 := by
  rw [parallelogramFun_eq]
  refine ⟨(Real.smoothTransition (4 * s - 0) - Real.smoothTransition (4 * s - 2),
    Real.smoothTransition (4 * s - 1) - Real.smoothTransition (4 * s - 3)), ⟨⟨?_, ?_⟩, ?_, ?_⟩,
    rfl⟩
  · have h1 := Real.smoothTransition.monotone (show 4 * s - 2 ≤ 4 * s - 0 by linarith)
    linarith
  · have h1 := Real.smoothTransition.le_one (4 * s - 0)
    have h2 := Real.smoothTransition.nonneg (4 * s - 2)
    linarith
  · have h1 := Real.smoothTransition.monotone (show 4 * s - 3 ≤ 4 * s - 1 by linarith)
    linarith
  · have h1 := Real.smoothTransition.le_one (4 * s - 1)
    have h2 := Real.smoothTransition.nonneg (4 * s - 3)
    linarith

/-- Coning a point of the closed parallelogram toward the vertex `c` stays inside it. -/
theorem cone_mem_closedParallelogram {c w1 w2 z : ℂ} (hz : z ∈ closedParallelogram c w1 w2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - (t : ℂ)) * z + (t : ℂ) * c ∈ closedParallelogram c w1 w2 := by
  obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩ := hz
  simp only at hxy
  refine ⟨((1 - t) * x, (1 - t) * y), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · exact mul_nonneg (by linarith) hx.1
  · nlinarith [hx.2, hx.1]
  · exact mul_nonneg (by linarith) hy.1
  · nlinarith [hy.2, hy.1]
  · simp only [← hxy]
    push_cast
    ring

/-- The raw underlying function of the coning homotopy from the parallelogram loop to the
constant loop at `c`. -/
def coningToFun (c w1 w2 : ℂ) : I × I → ℂ :=
  fun p ↦ (1 - (p.1 : ℂ)) * parallelogramFun c w1 w2 (p.2 : ℝ) + (p.1 : ℂ) * c

/-- The coning homotopy's underlying function is continuous. -/
theorem continuous_coningToFun (c w1 w2 : ℂ) : Continuous (coningToFun c w1 w2) := by
  unfold coningToFun
  have h1 : Continuous (fun p : I × I ↦ (1 - (p.1 : ℂ))) := by fun_prop
  have h2 : Continuous (fun p : I × I ↦ parallelogramFun c w1 w2 (p.2 : ℝ)) :=
    (contDiff_parallelogramFun c w1 w2).continuous.comp (by fun_prop)
  have h3 : Continuous (fun p : I × I ↦ (p.1 : ℂ)) := by fun_prop
  exact (h1.mul h2).add (h3.mul continuous_const)

/-- Every point of the coning homotopy lies in the closed parallelogram. -/
theorem coningToFun_mem_closedParallelogram (c w1 w2 : ℂ) (p : I × I) :
    coningToFun c w1 w2 p ∈ closedParallelogram c w1 w2 :=
  cone_mem_closedParallelogram (parallelogramFun_mem_closedParallelogram c w1 w2 (p.2 : ℝ))
    p.1.2.1 p.1.2.2

/-- The coning homotopy from the parallelogram loop to the constant loop at `c`, straight-line
toward the vertex `c`. Since `c` and the loop both lie in the closed convex parallelogram, so
does the whole homotopy. -/
def coningHomotopy (c w1 w2 : ℂ) : (parallelogramLoop c w1 w2).Homotopy (Path.refl c) where
  toFun := coningToFun c w1 w2
  continuous_toFun := continuous_coningToFun c w1 w2
  map_zero_left x := by simp [coningToFun]
  map_one_left x := by simp [coningToFun]
  prop' t x hx := by
    rcases hx with rfl | hx
    · change coningToFun c w1 w2 (t, 0) = parallelogramLoop c w1 w2 0
      simp only [coningToFun, Icc.coe_zero, parallelogramFun_zero, Path.source]
      ring
    · rw [Set.mem_singleton_iff.mp hx]
      change coningToFun c w1 w2 (t, 1) = parallelogramLoop c w1 w2 1
      simp only [coningToFun, Icc.coe_one, parallelogramFun_one, Path.target]
      ring

/-- **The index of the parallelogram boundary vanishes outside the closed parallelogram.** -/
theorem curveIndex_parallelogramLoop_eq_zero {c w1 w2 w : ℂ}
    (hw : w ∉ closedParallelogram c w1 w2) :
    curveIndex (parallelogramLoop c w1 w2) w = 0 :=
  curveIndex_eq_zero_of_continuous_nullhomotopy (coningHomotopy c w1 w2)
    (fun p hp ↦ hw (hp ▸ coningToFun_mem_closedParallelogram c w1 w2 p))
    (contDiffOn_parallelogramLoop_extend c w1 w2)

/-! ### Toward the interior index

The cross-product-type quantity `Im (v * conj (p - w))` controls the sign of the rate of
turning of the ray from `w` along an edge from `p` in direction `v`, and is unchanged by
moving along that edge (a `u`-independence fact used to pin its sign once, at the edge's
start). Combined with an explicit `Real.arctan`-based antiderivative for the resulting
rational integrand, each edge's contribution to the total turning is pinned to lie strictly
in `(0, π)` without ever tracking a branch of `Complex.log`. -/

/-- The cross-product-type quantity `Im (v * conj (p + u • v - w))` does not depend on `u`,
since `Im (v * conj v) = 0`. -/
theorem im_mul_conj_add_ofReal_mul_sub (v p w : ℂ) (u : ℝ) :
    (v * conj (p + (u : ℂ) * v - w)).im = (v * conj (p - w)).im := by
  have h : p + (u : ℂ) * v - w = (p - w) + (u : ℂ) * v := by ring
  rw [h, map_add, map_mul, Complex.conj_ofReal, mul_add]
  have hz : v * ((u : ℂ) * conj v) = (u : ℂ) * (v * conj v) := by ring
  rw [hz, Complex.add_im]
  have h2 : ((u : ℂ) * (v * conj v)).im = 0 := by
    rw [Complex.mul_conj]
    simp
  rw [h2, add_zero]

/-- **An explicit real antiderivative of a positive-definite rational function**, via
`Real.arctan`. Given the Lagrange-type identity `4 A D' = B ^ 2 + 4 C ^ 2` (which forces the
quadratic `A u ^ 2 + B u + D'` to be everywhere positive when `A > 0`), the function
`u ↦ arctan ((2 A u + B) / (2 C))` has derivative `C / (A u ^ 2 + B u + D')` at every point. -/
theorem hasDerivAt_arctan_quadratic {A B D' C : ℝ} (hA : 0 < A) (hC : 0 < C)
    (hLagrange : 4 * A * D' = B ^ 2 + 4 * C ^ 2) (u : ℝ) :
    HasDerivAt (fun u ↦ Real.arctan ((2 * A * u + B) / (2 * C)))
      (C / (A * u ^ 2 + B * u + D')) u := by
  have hpos : 0 < A * u ^ 2 + B * u + D' := by
    nlinarith [sq_nonneg (2 * A * u + B), sq_nonneg C, mul_pos hA hC]
  have hlin : HasDerivAt (fun u : ℝ ↦ 2 * A * u + B) (2 * A) u := by
    simpa using ((hasDerivAt_id u).const_mul (2 * A)).add_const B
  have h1 : HasDerivAt (fun u : ℝ ↦ (2 * A * u + B) / (2 * C)) (2 * A / (2 * C)) u :=
    hlin.div_const (2 * C)
  have h2 := h1.arctan
  have heq : 1 / (1 + ((2 * A * u + B) / (2 * C)) ^ 2) * (2 * A / (2 * C)) =
      C / (A * u ^ 2 + B * u + D') := by
    have hpos' : (1:ℝ) + ((2 * A * u + B) / (2 * C)) ^ 2 ≠ 0 := by positivity
    have hC0 : (2:ℝ) * C ≠ 0 := by positivity
    rw [eq_div_iff hpos.ne']
    field_simp
    nlinarith [hLagrange]
  rwa [heq] at h2

/-- **The endpoint difference of the `arctan` antiderivative lies strictly in `(0, π)`.** -/
theorem arctan_quadratic_one_sub_zero_mem_Ioo {A B C : ℝ} (hA : 0 < A) (hC : 0 < C) :
    Real.arctan ((2 * A * 1 + B) / (2 * C)) - Real.arctan ((2 * A * 0 + B) / (2 * C)) ∈
      Set.Ioo (0:ℝ) Real.pi := by
  have hC2 : (0:ℝ) < 2 * C := by linarith
  have h0 : (2:ℝ) * A * 0 + B = B := by ring
  rw [h0]
  constructor
  · have hmono : Real.arctan (B / (2 * C)) < Real.arctan ((2 * A * 1 + B) / (2 * C)) := by
      apply Real.arctan_strictMono
      rw [div_lt_div_iff_of_pos_right hC2]
      nlinarith
    linarith
  · have h1 := Real.arctan_lt_pi_div_two ((2 * A * 1 + B) / (2 * C))
    have h2 := Real.neg_pi_div_two_lt_arctan (B / (2 * C))
    linarith

/-- **An edge's total turning lies strictly in `(0, π)`.** The `u = 0` to `u = 1` integral of
the antiderivative from `hasDerivAt_arctan_quadratic`. -/
theorem integral_arctan_quadratic_mem_Ioo {A B D' C : ℝ} (hA : 0 < A) (hC : 0 < C)
    (hLagrange : 4 * A * D' = B ^ 2 + 4 * C ^ 2) :
    (∫ u in (0:ℝ)..1, C / (A * u ^ 2 + B * u + D')) ∈ Set.Ioo (0:ℝ) Real.pi := by
  have hne : ∀ u : ℝ, A * u ^ 2 + B * u + D' ≠ 0 := fun u ↦ by
    nlinarith [sq_nonneg (2 * A * u + B), sq_nonneg C, mul_pos hA hC]
  have hderiv : ∀ u ∈ Set.uIcc (0:ℝ) 1, HasDerivAt
      (fun u ↦ Real.arctan ((2 * A * u + B) / (2 * C))) (C / (A * u ^ 2 + B * u + D')) u :=
    fun u _ ↦ hasDerivAt_arctan_quadratic hA hC hLagrange u
  have hint : IntervalIntegrable (fun u ↦ C / (A * u ^ 2 + B * u + D')) MeasureTheory.volume
      0 1 := by
    apply Continuous.intervalIntegrable
    exact continuous_const.div (by fun_prop) hne
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  exact arctan_quadratic_one_sub_zero_mem_Ioo hA hC

/-- The Lagrange-type identity relating `A = normSq v`, `B = 2 Re (conj (p - w) * v)`,
`D' = normSq (p - w)`, `C = Im (v * conj (p - w))`. -/
theorem lagrange_identity (v pw : ℂ) :
    4 * normSq v * normSq pw =
      (2 * (v * conj pw).re) ^ 2 + 4 * (v * conj pw).im ^ 2 := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- `normSq (a + u • v)` expands to the real quadratic `normSq v * u ^ 2 + 2 Re (conj a * v) * u
+ normSq a`. -/
theorem normSq_add_ofReal_mul (a v : ℂ) (u : ℝ) :
    normSq (a + (u : ℂ) * v) =
      normSq v * u ^ 2 + 2 * (conj a * v).re * u + normSq a := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The imaginary part of `v / z` equals `(v * conj z).im / normSq z`. -/
theorem im_div_eq (v z : ℂ) : (v / z).im = (v * conj z).im / normSq z := by
  rw [Complex.div_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- **A single edge's contribution to the total turning lies strictly in `(0, π)`.** For the
edge from `p` to `q` and a point `w` strictly to its left, `C := Im ((q - p) * conj (p - w)) > 0`,
the imaginary part of `∫₀¹ (q - p) / (p + t (q - p) - w) dt` lies in `(0, π)`. -/
theorem im_integral_segment_mem_Ioo {p q w : ℂ} (hv : q - p ≠ 0)
    (hC : 0 < ((q - p) * conj (p - w)).im) :
    (∫ t in (0 : ℝ)..1, (q - p) • (AffineMap.lineMap p q t - w)⁻¹).im ∈
      Set.Ioo (0 : ℝ) Real.pi := by
  set v := q - p
  set A := normSq v
  set B := 2 * (conj (p - w) * v).re
  set D' := normSq (p - w)
  set C := (v * conj (p - w)).im
  have hA : 0 < A := normSq_pos.mpr hv
  have hLagrange : 4 * A * D' = B ^ 2 + 4 * C ^ 2 := by
    simp only [A, B, D', C, show conj (p - w) * v = v * conj (p - w) by ring]
    exact lagrange_identity v (p - w)
  have hline : ∀ t : ℝ, AffineMap.lineMap p q t - w = (p - w) + (t : ℂ) * v := fun t ↦ by
    rw [AffineMap.lineMap_apply_module', Complex.real_smul]
    ring
  -- the integrand's imaginary part is the positive rational function of the `arctan` lemma
  have him : ∀ t : ℝ, (v • (AffineMap.lineMap p q t - w)⁻¹).im =
      C / (A * t ^ 2 + B * t + D') := fun t ↦ by
    rw [smul_eq_mul, ← div_eq_mul_inv, im_div_eq, hline,
      show (p - w) + (t : ℂ) * v = p + (t : ℂ) * v - w by ring, im_mul_conj_add_ofReal_mul_sub,
      show p + (t : ℂ) * v - w = (p - w) + (t : ℂ) * v by ring, normSq_add_ofReal_mul]
  have hne : ∀ t : ℝ, AffineMap.lineMap p q t - w ≠ 0 := fun t h ↦ by
    have hq := normSq_add_ofReal_mul (p - w) v t
    rw [← hline, h, map_zero] at hq
    nlinarith [sq_nonneg (2 * A * t + B), sq_nonneg C, mul_pos hA hC]
  have hcont : Continuous (fun t : ℝ ↦ v • (AffineMap.lineMap p q t - w)⁻¹) :=
    (Continuous.inv₀ (f := fun t : ℝ ↦ AffineMap.lineMap p q t - w)
      ((AffineMap.contDiff_lineMap p q (n := 0)).continuous.sub continuous_const) hne).const_smul v
  have hint : IntervalIntegrable (fun t : ℝ ↦ v • (AffineMap.lineMap p q t - w)⁻¹)
      MeasureTheory.volume 0 1 := hcont.intervalIntegrable 0 1
  rw [← Complex.imCLM_apply, ← imCLM.intervalIntegral_comp_comm hint]
  simp only [Complex.imCLM_apply, him]
  exact integral_arctan_quadratic_mem_Ioo hA hC hLagrange

/-- A point strictly to the left of the edge from `p` to `q` does not lie on that edge. -/
theorem ne_of_mem_segment_of_im_pos {p q w z : ℂ} (hC : 0 < ((q - p) * conj (p - w)).im)
    (hz : z ∈ segment ℝ p q) : z ≠ w := by
  intro h
  subst h
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, -, rfl⟩ := hz
  rw [AffineMap.lineMap_apply_module', Complex.real_smul,
    show p - ((t : ℂ) * (q - p) + p) = ((-t : ℝ) : ℂ) * (q - p) by push_cast; ring, map_mul,
    conj_ofReal, show (q - p) * (((-t : ℝ) : ℂ) * conj (q - p)) =
      ((-t : ℝ) : ℂ) * ((q - p) * conj (q - p)) by ring, mul_conj] at hC
  simp at hC

/-- `Im (conj w1 * (r • w1 + s • w2)) = s * Im (conj w1 * w2)`. -/
theorem im_conj_w1_mul_combo (w1 w2 : ℂ) (r s : ℝ) :
    (conj w1 * ((r : ℂ) * w1 + (s : ℂ) * w2)).im = s * (conj w1 * w2).im := by
  have h1 : (conj w1 * w1).im = 0 := by
    rw [show conj w1 * w1 = w1 * conj w1 by ring, Complex.mul_conj]; simp
  rw [mul_add, Complex.add_im,
    show conj w1 * ((r : ℂ) * w1) = (r : ℂ) * (conj w1 * w1) by ring,
    show conj w1 * ((s : ℂ) * w2) = (s : ℂ) * (conj w1 * w2) by ring,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, h1, mul_zero,
    zero_add, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

/-- `Im (conj w2 * (r • w1 + s • w2)) = r * Im (conj w2 * w1)`. -/
theorem im_conj_w2_mul_combo (w1 w2 : ℂ) (r s : ℝ) :
    (conj w2 * ((r : ℂ) * w1 + (s : ℂ) * w2)).im = r * (conj w2 * w1).im := by
  have h1 : (conj w2 * w2).im = 0 := by
    rw [show conj w2 * w2 = w2 * conj w2 by ring, Complex.mul_conj]; simp
  rw [mul_add, Complex.add_im,
    show conj w2 * ((r : ℂ) * w1) = (r : ℂ) * (conj w2 * w1) by ring,
    show conj w2 * ((s : ℂ) * w2) = (s : ℂ) * (conj w2 * w2) by ring]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, h1,
    mul_zero]

/-- The cross-product antisymmetry `Im (conj w2 * w1) = -Im (conj w1 * w2)`. -/
theorem im_conj_w2_w1_eq_neg (w1 w2 : ℂ) : (conj w2 * w1).im = -(conj w1 * w2).im := by
  rw [show conj w2 * w1 = conj (conj w1 * w2) by simp [mul_comm]]
  simp only [Complex.conj_im, Complex.mul_im, Complex.conj_re]

/-- `Im (v * conj z) = -Im (conj v * z)`. -/
theorem im_mul_conj_eq_neg_im_conj_mul (v z : ℂ) : (v * conj z).im = -(conj v * z).im := by
  rw [show v * conj z = conj (conj v * z) by rw [map_mul, Complex.conj_conj]]
  simp only [Complex.conj_im]

/-- An interior point lies strictly to the left of each oriented edge of a positively
oriented parallelogram. -/
private theorem parallelogram_edge_crossProducts_pos {c w1 w2 w : ℂ}
    (hD : 0 < (conj w1 * w2).im) {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1)
    (hw : w = c + (x : ℂ) * w1 + (y : ℂ) * w2) :
    0 < (w1 * conj (c - w)).im ∧
      0 < (w2 * conj (c + w1 - w)).im ∧
      0 < ((-w1) * conj (c + w1 + w2 - w)).im ∧
      0 < ((-w2) * conj (c + w2 - w)).im := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : (w1 * conj (c - w)).im = y * (conj w1 * w2).im := by
      rw [im_mul_conj_eq_neg_im_conj_mul,
        show c - w = ((-x : ℝ) : ℂ) * w1 + ((-y : ℝ) : ℂ) * w2 by rw [hw]; push_cast; ring,
        im_conj_w1_mul_combo]
      ring
    rw [h1]; positivity
  · have h1 : (w2 * conj (c + w1 - w)).im = (1 - x) * (conj w1 * w2).im := by
      rw [im_mul_conj_eq_neg_im_conj_mul,
        show c + w1 - w = ((1 - x : ℝ) : ℂ) * w1 + ((-y : ℝ) : ℂ) * w2 by
          rw [hw]; push_cast; ring,
        im_conj_w2_mul_combo, im_conj_w2_w1_eq_neg]
      ring
    rw [h1]; positivity
  · have h1 : ((-w1) * conj (c + w1 + w2 - w)).im = (1 - y) * (conj w1 * w2).im := by
      rw [show (-w1) * conj (c + w1 + w2 - w) = -(w1 * conj (c + w1 + w2 - w)) by ring,
        Complex.neg_im, im_mul_conj_eq_neg_im_conj_mul,
        show c + w1 + w2 - w = ((1 - x : ℝ) : ℂ) * w1 + ((1 - y : ℝ) : ℂ) * w2 by
          rw [hw]; push_cast; ring,
        im_conj_w1_mul_combo]
      ring
    rw [h1]; positivity
  · have h1 : ((-w2) * conj (c + w2 - w)).im = x * (conj w1 * w2).im := by
      rw [show (-w2) * conj (c + w2 - w) = -(w2 * conj (c + w2 - w)) by ring,
        Complex.neg_im, im_mul_conj_eq_neg_im_conj_mul,
        show c + w2 - w = ((-x : ℝ) : ℂ) * w1 + ((1 - y : ℝ) : ℂ) * w2 by
          rw [hw]; push_cast; ring,
        im_conj_w2_mul_combo, im_conj_w2_w1_eq_neg]
      ring
    rw [h1]; positivity

/-- The parallelogram loop lies on the boundary of the parallelogram. -/
theorem range_parallelogramLoop_subset (c w1 w2 : ℂ) :
    Set.range (parallelogramLoop c w1 w2) ⊆ parallelogramBoundary c w1 w2 :=
  Loop.range_polygon_subset _ (by norm_num)

/-- **The index of the parallelogram boundary is `1` at every point of the open
parallelogram**, given `w1, w2` positively oriented (`Im (conj w1 * w2) > 0`). -/
theorem curveIndex_parallelogramLoop_eq_one {c w1 w2 : ℂ} (hD : 0 < (conj w1 * w2).im)
    {x y : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    curveIndex (parallelogramLoop c w1 w2) (c + (x : ℂ) * w1 + (y : ℂ) * w2) = 1 := by
  set w := c + (x : ℂ) * w1 + (y : ℂ) * w2 with hw_def
  have hv1 : w1 ≠ 0 := fun h ↦ by simp [h] at hD
  have hv2 : w2 ≠ 0 := fun h ↦ by simp [h] at hD
  obtain ⟨hC1, hC2, hC3, hC4⟩ := parallelogram_edge_crossProducts_pos hD hx0 hx1 hy0 hy1 hw_def
  -- the four edges, from `v i` to `v (i + 1)`, with `w` strictly to the left of each
  have hC : ∀ i : Fin 4, 0 < ((parallelogramVertex c w1 w2 (i + 1) -
      parallelogramVertex c w1 w2 i) * conj (parallelogramVertex c w1 w2 i - w)).im := by
    intro i
    fin_cases i
    · simpa [parallelogramVertex] using hC1
    · simpa [parallelogramVertex, show c + w1 + w2 - (c + w1) = w2 by ring] using hC2
    · simpa [parallelogramVertex, show c + w2 - (c + w1 + w2) = -w1 by ring] using hC3
    · simpa [parallelogramVertex, show c - (c + w2) = -w2 by ring] using hC4
  have hv : ∀ i : Fin 4, parallelogramVertex c w1 w2 (i + 1) - parallelogramVertex c w1 w2 i ≠ 0 :=
    fun i h ↦ by simpa [h] using hC i
  have hwB : w ∉ parallelogramBoundary c w1 w2 := fun hw ↦ by
    obtain ⟨i, hi⟩ := mem_iUnion.mp hw
    exact ne_of_mem_segment_of_im_pos (hC i) hi rfl
  -- the index is an integer `n`, and `2πi n` is the sum of the four edge integrals
  obtain ⟨n, hn⟩ := exists_int_curveIndex (w := w) (parallelogramLoop c w1 w2)
    (contDiffOn_parallelogramLoop_extend c w1 w2)
    fun t h ↦ hwB (by rw [← h]; exact range_parallelogramLoop_subset c w1 w2 (mem_range_self t))
  have hCI := curveIntegral_sub_inv_eq_two_pi_I_mul_curveIndex (parallelogramLoop c w1 w2) w
  rw [hn, curveIntegral_parallelogramLoop
    (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹))
    ((ContinuousLinearMap.toSpanSingletonLIE ℂ ℂ).continuous.comp_continuousOn
      (ContinuousOn.inv₀ (f := fun z : ℂ ↦ z - w) (by fun_prop)
        fun z hz ↦ sub_ne_zero.mpr fun h ↦ hwB (h ▸ hz)))] at hCI
  simp only [ContinuousLinearMap.toSpanSingleton_apply] at hCI
  -- the imaginary part of the total lies in `(0, 4π)`, so `n = 1`
  have hIm := congrArg Complex.im hCI
  have hR : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)).im = 2 * Real.pi * n := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [hR, Complex.im_sum, Fin.sum_univ_four] at hIm
  have hbound := fun i : Fin 4 ↦ im_integral_segment_mem_Ioo (hv i) (hC i)
  have hnbound : (0 : ℝ) < n ∧ (n : ℝ) < 2 := by
    constructor <;> nlinarith [(hbound 0).1, (hbound 1).1, (hbound 2).1, (hbound 3).1,
      (hbound 0).2, (hbound 1).2, (hbound 2).2, (hbound 3).2, Real.pi_pos]
  have : n = 1 := by
    have h1 : (0 : ℤ) < n := by exact_mod_cast hnbound.1
    have h2 : n < 2 := by exact_mod_cast hnbound.2
    omega
  rw [hn, this]
  norm_num

end Complex

end
