/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.CurveIndex.Homotopy
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# The boundary of a parallelogram as a smooth cycle, and its index

The boundary of the parallelogram with vertices `c, c + w1, c + w1 + w2, c + w2` is realized
as a single `C^∞` closed curve, by gluing the four edges with `Real.smoothTransition`: each
edge is traversed with a reparametrization that is flat (all derivatives vanish) at its two
endpoints, so the concatenation is smooth across the corners with no case analysis on
differentiability there.

For a point `w` outside the closed parallelogram, the analytic index of the boundary about
`w` vanishes: `parallelogramLoop` is nullhomotopic within the closed (convex) parallelogram
by coning it toward the vertex `c`, a straight-line homotopy that avoids every exterior point
automatically, by convexity.

For `w1, w2` positively oriented (`Im (conj w1 * w2) > 0`) and `w` strictly inside the open
parallelogram, the index is `1`. Each of the four edges'
contribution to the real "turning" integral `∫ Im [γ'/(γ - w)]` is computed as an explicit
`Real.arctan` antiderivative (justified by the Lagrange identity, which makes the relevant
quadratic denominator positive-definite); `Real.arctan`'s range bound then gives, for free,
that each edge's contribution lies in `(0, π)`, so the total lies in `(0, 4π)`. Since the
index is already known to be an integer (`Complex.exists_int_curveIndex`), this pins it to
exactly `1` without ever computing the total directly or gluing branches across corners.

## Main definitions

* `Complex.parallelogramFun c w1 w2`: the `C^∞` parametrization `ℝ → ℂ`.
* `Complex.parallelogramLoop c w1 w2`: the parallelogram boundary as a `Path c c`.
* `Complex.closedParallelogram c w1 w2`: the closed (filled) parallelogram.

## Main results

* `Complex.curveIndex_parallelogramLoop_eq_zero`: the index of the parallelogram boundary
  vanishes at every point outside the closed parallelogram.
* `Complex.curveIndex_parallelogramLoop_eq_one`: **the index of the parallelogram boundary is
  `1` at every point of the open parallelogram**, for positively oriented `w1, w2`.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Section IV.2 (polygons as chains).
-/

public noncomputable section

open Set Metric Filter
open scoped Topology unitInterval ComplexConjugate

namespace Complex

/-- The `C^∞` parametrization of the parallelogram boundary with vertices
`c, c + w1, c + w1 + w2, c + w2`, traversed in the indicated vertex order. The traversal is
counterclockwise when `0 < (conj w1 * w2).im`. Each of the four terms is flat (all derivatives
vanish) at its own transition, so the sum glues smoothly across the corners. -/
def parallelogramFun (c w1 w2 : ℂ) (s : ℝ) : ℂ :=
  c + ((Real.smoothTransition (4 * s - 0) - Real.smoothTransition (4 * s - 2) : ℝ) : ℂ) * w1
    + ((Real.smoothTransition (4 * s - 1) - Real.smoothTransition (4 * s - 3) : ℝ) : ℂ) * w2

/-- `parallelogramFun` is `C^∞` on all of `ℝ`. -/
theorem contDiff_parallelogramFun (c w1 w2 : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (parallelogramFun c w1 w2) := by
  unfold parallelogramFun
  have hst : ∀ k : ℝ, ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ ↦ Real.smoothTransition (4 * s - k)) :=
    fun k ↦ Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hor : ∀ k1 k2 : ℝ, ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ ↦ ((Real.smoothTransition (4 * s - k1)
        - Real.smoothTransition (4 * s - k2) : ℝ) : ℂ)) :=
    fun k1 k2 ↦ Complex.ofRealCLM.contDiff.comp ((hst k1).sub (hst k2))
  exact (contDiff_const.add ((hor 0 2).mul contDiff_const)).add ((hor 1 3).mul contDiff_const)

/-- `parallelogramFun` is continuous, as it is `C^∞`. -/
theorem continuous_parallelogramFun (c w1 w2 : ℂ) : Continuous (parallelogramFun c w1 w2) :=
  (contDiff_parallelogramFun c w1 w2).continuous

/-- `parallelogramFun` is unaffected by clamping its argument into `[0, 1]`: it already takes
the value at `0` for all `s ≤ 0` and the value at `1` for all `s ≥ 1`. -/
theorem parallelogramFun_projIcc (c w1 w2 : ℂ) (s : ℝ) :
    parallelogramFun c w1 w2 (projIcc (0 : ℝ) 1 zero_le_one s) = parallelogramFun c w1 w2 s := by
  by_cases h0 : (0 : ℝ) ≤ s
  · by_cases h1 : s ≤ (1 : ℝ)
    · rw [projIcc_of_mem _ ⟨h0, h1⟩]
    · have h1' : (1 : ℝ) < s := not_le.mp h1
      rw [projIcc_of_right_le zero_le_one h1'.le]
      unfold parallelogramFun
      congr 2
      · congr 1
        · have e1 : (4 : ℝ) * 1 - 0 = 4 := by ring
          have e2 : (4 : ℝ) * 1 - 2 = 2 := by ring
          have e3 : (4 : ℝ) * s - 0 = 4 * s := by ring
          have e4 : (4 : ℝ) * s - 2 = 4 * s - 2 := by ring
          rw [e1, e2, e3, e4, Real.smoothTransition.one_of_one_le (by norm_num),
            Real.smoothTransition.one_of_one_le (by norm_num),
            Real.smoothTransition.one_of_one_le (by linarith),
            Real.smoothTransition.one_of_one_le (by linarith)]
      · congr 1
        · have e1 : (4 : ℝ) * 1 - 1 = 3 := by ring
          have e2 : (4 : ℝ) * 1 - 3 = 1 := by ring
          rw [e1, e2, Real.smoothTransition.one_of_one_le (by norm_num),
            Real.smoothTransition.one_of_one_le (by norm_num),
            Real.smoothTransition.one_of_one_le (by linarith),
            Real.smoothTransition.one_of_one_le (by linarith)]
  · have h0' : s < (0 : ℝ) := not_le.mp h0
    rw [projIcc_of_le_left zero_le_one h0'.le]
    unfold parallelogramFun
    congr 2
    · congr 1
      · rw [Real.smoothTransition.zero_of_nonpos (by norm_num : (4 : ℝ) * 0 - 0 ≤ 0),
          Real.smoothTransition.zero_of_nonpos (by norm_num : (4 : ℝ) * 0 - 2 ≤ 0),
          Real.smoothTransition.zero_of_nonpos (by linarith : (4 : ℝ) * s - 0 ≤ 0),
          Real.smoothTransition.zero_of_nonpos (by linarith : (4 : ℝ) * s - 2 ≤ 0)]
    · congr 1
      · rw [Real.smoothTransition.zero_of_nonpos (by norm_num : (4 : ℝ) * 0 - 1 ≤ 0),
          Real.smoothTransition.zero_of_nonpos (by norm_num : (4 : ℝ) * 0 - 3 ≤ 0),
          Real.smoothTransition.zero_of_nonpos (by linarith : (4 : ℝ) * s - 1 ≤ 0),
          Real.smoothTransition.zero_of_nonpos (by linarith : (4 : ℝ) * s - 3 ≤ 0)]

/-- The value of `parallelogramFun` at the base vertex. -/
theorem parallelogramFun_zero (c w1 w2 : ℂ) : parallelogramFun c w1 w2 0 = c := by
  unfold parallelogramFun
  norm_num
  rw [Real.smoothTransition.zero_of_nonpos (by norm_num : (-2 : ℝ) ≤ 0),
    Real.smoothTransition.zero_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0),
    Real.smoothTransition.zero_of_nonpos (by norm_num : (-3 : ℝ) ≤ 0)]
  simp

/-- The value of `parallelogramFun` at the second vertex. -/
theorem parallelogramFun_quarter (c w1 w2 : ℂ) : parallelogramFun c w1 w2 (1 / 4) = c + w1 := by
  unfold parallelogramFun
  have e1 : (4 : ℝ) * (1 / 4) - 0 = 1 := by ring
  have e2 : (4 : ℝ) * (1 / 4) - 2 = -1 := by ring
  have e3 : (4 : ℝ) * (1 / 4) - 1 = 0 := by ring
  have e4 : (4 : ℝ) * (1 / 4) - 3 = -2 := by ring
  rw [e1, e2, e3, e4, Real.smoothTransition.one_of_one_le (le_refl 1),
    Real.smoothTransition.zero_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0),
    Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ)),
    Real.smoothTransition.zero_of_nonpos (by norm_num : (-2 : ℝ) ≤ 0)]
  push_cast
  ring

/-- The value of `parallelogramFun` at the third vertex. -/
theorem parallelogramFun_half (c w1 w2 : ℂ) :
    parallelogramFun c w1 w2 (1 / 2) = c + w1 + w2 := by
  unfold parallelogramFun
  have e1 : (4 : ℝ) * (1 / 2) - 0 = 2 := by ring
  have e2 : (4 : ℝ) * (1 / 2) - 2 = 0 := by ring
  have e3 : (4 : ℝ) * (1 / 2) - 1 = 1 := by ring
  have e4 : (4 : ℝ) * (1 / 2) - 3 = -1 := by ring
  rw [e1, e2, e3, e4, Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2),
    Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ)),
    Real.smoothTransition.one_of_one_le (le_refl 1),
    Real.smoothTransition.zero_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0)]
  push_cast
  ring

/-- The value of `parallelogramFun` at the fourth vertex. -/
theorem parallelogramFun_three_quarter (c w1 w2 : ℂ) :
    parallelogramFun c w1 w2 (3 / 4) = c + w2 := by
  unfold parallelogramFun
  have e1 : (4 : ℝ) * (3 / 4) - 0 = 3 := by ring
  have e2 : (4 : ℝ) * (3 / 4) - 2 = 1 := by ring
  have e3 : (4 : ℝ) * (3 / 4) - 1 = 2 := by ring
  have e4 : (4 : ℝ) * (3 / 4) - 3 = 0 := by ring
  rw [e1, e2, e3, e4, Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 3),
    Real.smoothTransition.one_of_one_le (le_refl 1),
    Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2),
    Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))]
  push_cast
  ring

/-- The value of `parallelogramFun` back at the base vertex, closing the loop. -/
theorem parallelogramFun_one (c w1 w2 : ℂ) : parallelogramFun c w1 w2 1 = c := by
  unfold parallelogramFun
  have e1 : (4 : ℝ) * 1 - 0 = 4 := by ring
  have e2 : (4 : ℝ) * 1 - 2 = 2 := by ring
  have e3 : (4 : ℝ) * 1 - 1 = 3 := by ring
  have e4 : (4 : ℝ) * 1 - 3 = 1 := by ring
  rw [e1, e2, e3, e4, Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 4),
    Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2),
    Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 3),
    Real.smoothTransition.one_of_one_le (le_refl 1)]
  push_cast
  ring

/-- The parallelogram boundary with vertices `c, c + w1, c + w1 + w2, c + w2`, as a `C^∞`
closed path. -/
def parallelogramLoop (c w1 w2 : ℂ) : Path c c where
  toFun t := parallelogramFun c w1 w2 (t : ℝ)
  continuous_toFun := (contDiff_parallelogramFun c w1 w2).continuous.comp continuous_subtype_val
  source' := parallelogramFun_zero c w1 w2
  target' := parallelogramFun_one c w1 w2

/-- The extension of the parallelogram loop to `ℝ` is `parallelogramFun` itself, since the
latter already takes its boundary values outside `[0, 1]`. -/
theorem parallelogramLoop_extend (c w1 w2 : ℂ) :
    (parallelogramLoop c w1 w2).extend = parallelogramFun c w1 w2 := by
  funext s
  exact parallelogramFun_projIcc c w1 w2 s

/-- The parallelogram loop is `C^1` (indeed `C^∞`) on `[0, 1]`. -/
theorem contDiffOn_parallelogramLoop_extend (c w1 w2 : ℂ) :
    ContDiffOn ℝ 1 (parallelogramLoop c w1 w2).extend I := by
  rw [parallelogramLoop_extend]
  exact ((contDiff_parallelogramFun c w1 w2).of_le (by norm_num)).contDiffOn

/-- The closed (filled) parallelogram with vertices `c, c + w1, c + w1 + w2, c + w2`. -/
def closedParallelogram (c w1 w2 : ℂ) : Set ℂ :=
  (fun p : ℝ × ℝ ↦ c + (p.1 : ℂ) * w1 + (p.2 : ℂ) * w2) '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)

/-- The parallelogram loop stays within the closed parallelogram at every parameter, not only
at the vertices. -/
theorem parallelogramFun_mem_closedParallelogram (c w1 w2 : ℂ) (s : ℝ) :
    parallelogramFun c w1 w2 s ∈ closedParallelogram c w1 w2 := by
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
  map_zero_left x := by simp [coningToFun, parallelogramLoop]
  map_one_left x := by simp [coningToFun]
  prop' t x hx := by
    rcases hx with hx | hx
    · simp only [coningToFun, hx, parallelogramLoop]
      norm_num [parallelogramFun_zero]
      ring
    · simp only [Set.mem_singleton_iff] at hx
      simp only [coningToFun, hx, parallelogramLoop]
      norm_num [parallelogramFun_one]
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

/-- **A single edge's contribution to the total turning lies strictly in `(0, π)`.** For a
curve `γ = parallelogramFun c w1 w2` that agrees with the affine parametrization
`t ↦ p + φ (t) • v` throughout the open interval `(a, b)`, with `φ` continuous on `[a, b]`,
`φ (a) = 0`, `φ (b) = 1`, `v ≠ 0`, and `w` positioned so that `C := Im (v * conj (p - w)) > 0`
(and never equal to a point of the loop), the contribution of `[a, b]` to the total turning
`∫ Im (γ' (t) / (γ (t) - w)) dt` lies in `(0, π)`. -/
theorem im_edge_integral_mem_Ioo {c w1 w2 w p v : ℂ} {a b : ℝ} (hab : a < b) (hv : v ≠ 0)
    (hC : 0 < (v * conj (p - w)).im) (hwne : ∀ t : ℝ, parallelogramFun c w1 w2 t ≠ w)
    {φ : ℝ → ℝ} (hφcont : ContinuousOn φ (Icc a b))
    (hφderiv : ∀ t ∈ Ioo a b, HasDerivAt φ (deriv φ t) t)
    (hφa : φ a = 0) (hφb : φ b = 1)
    (heq : Set.EqOn (parallelogramFun c w1 w2) (fun t ↦ p + (φ t : ℂ) * v) (Ioo a b)) :
    (∫ t in a..b, (deriv (parallelogramFun c w1 w2) t *
      (parallelogramFun c w1 w2 t - w)⁻¹).im) ∈ Set.Ioo (0:ℝ) Real.pi := by
  set A := normSq v with hA_def
  set B := 2 * (conj (p - w) * v).re with hB_def
  set D' := normSq (p - w) with hD_def
  set C := (v * conj (p - w)).im with hC_def
  have hA : 0 < A := by
    rw [hA_def]; exact normSq_pos.mpr hv
  have hLagrange : 4 * A * D' = B ^ 2 + 4 * C ^ 2 := by
    rw [hA_def, hB_def, hD_def, hC_def]
    rw [show conj (p - w) * v = v * conj (p - w) by ring]
    exact lagrange_identity v (p - w)
  -- The integrand, restricted to the open interval, is the derivative of `G ∘ φ`.
  have hderiv_eq : ∀ t ∈ Ioo a b,
      HasDerivAt (fun t ↦ Real.arctan ((2 * A * φ t + B) / (2 * C)))
        ((deriv (parallelogramFun c w1 w2) t * (parallelogramFun c w1 w2 t - w)⁻¹).im) t := by
    intro t ht
    have hOpen : IsOpen (Ioo a b) := isOpen_Ioo
    have heqf : parallelogramFun c w1 w2 =ᶠ[𝓝 t] (fun t ↦ p + (φ t : ℂ) * v) :=
      Filter.eventually_of_mem (hOpen.mem_nhds ht) heq
    have hφt := hφderiv t ht
    have haff : HasDerivAt (fun t ↦ p + (φ t : ℂ) * v) (((deriv φ t : ℝ) : ℂ) * v) t := by
      have h1 : HasDerivAt (fun t : ℝ ↦ (φ t : ℂ)) ((deriv φ t : ℝ) : ℂ) t := hφt.ofReal_comp
      simpa using (h1.mul_const v).const_add p
    have hcurve : HasDerivAt (parallelogramFun c w1 w2) (((deriv φ t : ℝ) : ℂ) * v) t :=
      haff.congr_of_eventuallyEq heqf
    have hderivval : deriv (parallelogramFun c w1 w2) t = ((deriv φ t : ℝ) : ℂ) * v := hcurve.deriv
    have hptval : parallelogramFun c w1 w2 t = p + (φ t : ℂ) * v := heq ht
    rw [hderivval, hptval]
    have hne0 : p + (φ t : ℂ) * v - w ≠ 0 := by
      rw [← hptval]; exact sub_ne_zero.mpr (hwne t)
    have hden : p + (φ t : ℂ) * v - w = (p - w) + (φ t : ℂ) * v := by ring
    have hkey : (((deriv φ t : ℝ) : ℂ) * v * (p + (φ t : ℂ) * v - w)⁻¹).im =
        deriv φ t * (C / (A * φ t ^ 2 + B * φ t + D')) := by
      rw [show ((deriv φ t : ℝ) : ℂ) * v * (p + (φ t : ℂ) * v - w)⁻¹
          = ((deriv φ t : ℝ) : ℂ) * (v / (p + (φ t : ℂ) * v - w)) by rw [div_eq_mul_inv]; ring]
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      congr 1
      rw [im_div_eq, im_mul_conj_add_ofReal_mul_sub, hden, normSq_add_ofReal_mul]
    rw [hkey]
    have hchain := (hasDerivAt_arctan_quadratic hA hC hLagrange (φ t)).comp t hφt
    have hval : deriv φ t * (C / (A * φ t ^ 2 + B * φ t + D')) =
        C / (A * φ t ^ 2 + B * φ t + D') * deriv φ t := mul_comm _ _
    rw [hval]
    convert hchain using 1
    exact rfl
  -- Assemble via the fundamental theorem of calculus on `[a, b]`.
  have hcontG : ContinuousOn (fun t ↦ Real.arctan ((2 * A * φ t + B) / (2 * C))) (Icc a b) := by
    apply Real.continuous_arctan.comp_continuousOn
    apply ContinuousOn.div ((continuousOn_const.mul hφcont).add continuousOn_const)
      continuousOn_const
    intro t _
    linarith
  have hcont1 : Continuous (deriv (parallelogramFun c w1 w2)) :=
    ((contDiff_parallelogramFun c w1 w2).iterate_deriv 1).continuous
  have hcont2 : Continuous (fun t ↦ (parallelogramFun c w1 w2 t - w)⁻¹) := by
    apply Continuous.inv₀ ((continuous_parallelogramFun c w1 w2).sub continuous_const)
    exact fun t ↦ sub_ne_zero.mpr (hwne t)
  have hcontI0 : Continuous (fun t ↦ (deriv (parallelogramFun c w1 w2) t *
      (parallelogramFun c w1 w2 t - w)⁻¹).im) :=
    Complex.continuous_im.comp (hcont1.mul hcont2)
  have hcontI : ContinuousOn (fun t ↦ (deriv (parallelogramFun c w1 w2) t *
      (parallelogramFun c w1 w2 t - w)⁻¹).im) (Icc a b) := hcontI0.continuousOn
  have hint : IntervalIntegrable (fun t ↦ (deriv (parallelogramFun c w1 w2) t *
      (parallelogramFun c w1 w2 t - w)⁻¹).im) MeasureTheory.volume a b :=
    hcontI0.intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le hcontG hderiv_eq hint,
    hφa, hφb]
  exact arctan_quadratic_one_sub_zero_mem_Ioo hA hC

/-- On `t ≤ 1/4`, the loop agrees with the first edge, from `c` in direction `w1`. -/
theorem parallelogramFun_eq_edge1 (c w1 w2 : ℂ) {t : ℝ} (ht : t ≤ 1 / 4) :
    parallelogramFun c w1 w2 t = c + (Real.smoothTransition (4 * t) : ℂ) * w1 := by
  unfold parallelogramFun
  rw [show (4:ℝ) * t - 0 = 4 * t by ring,
    Real.smoothTransition.zero_of_nonpos (by linarith : (4:ℝ) * t - 2 ≤ 0),
    Real.smoothTransition.zero_of_nonpos (by linarith : (4:ℝ) * t - 1 ≤ 0),
    Real.smoothTransition.zero_of_nonpos (by linarith : (4:ℝ) * t - 3 ≤ 0)]
  push_cast; ring

/-- On `1/4 ≤ t ≤ 1/2`, the loop agrees with the second edge, from `c + w1` in direction `w2`. -/
theorem parallelogramFun_eq_edge2 (c w1 w2 : ℂ) {t : ℝ} (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 1 / 2) :
    parallelogramFun c w1 w2 t = c + w1 + (Real.smoothTransition (4 * t - 1) : ℂ) * w2 := by
  unfold parallelogramFun
  rw [Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ 4 * t - 0),
    Real.smoothTransition.zero_of_nonpos (by linarith : (4:ℝ) * t - 2 ≤ 0),
    Real.smoothTransition.zero_of_nonpos (by linarith : (4:ℝ) * t - 3 ≤ 0)]
  push_cast; ring

/-- On `1/2 ≤ t ≤ 3/4`, the loop agrees with the third edge, from `c + w1 + w2` in
direction `-w1`. -/
theorem parallelogramFun_eq_edge3 (c w1 w2 : ℂ) {t : ℝ} (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 3 / 4) :
    parallelogramFun c w1 w2 t =
      c + w1 + w2 + (Real.smoothTransition (4 * t - 2) : ℂ) * (-w1) := by
  unfold parallelogramFun
  rw [Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ 4 * t - 0),
    Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ 4 * t - 1),
    Real.smoothTransition.zero_of_nonpos (by linarith : (4:ℝ) * t - 3 ≤ 0)]
  push_cast; ring

/-- On `3/4 ≤ t ≤ 1`, the loop agrees with the fourth edge, from `c + w2` in direction
`-w2`. -/
theorem parallelogramFun_eq_edge4 (c w1 w2 : ℂ) {t : ℝ} (ht0 : 3 / 4 ≤ t) :
    parallelogramFun c w1 w2 t = c + w2 + (Real.smoothTransition (4 * t - 3) : ℂ) * (-w2) := by
  unfold parallelogramFun
  rw [Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ 4 * t - 0),
    Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ 4 * t - 2),
    Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ 4 * t - 1)]
  push_cast; ring

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

/-- **The parallelogram boundary avoids every strictly interior point.** -/
theorem parallelogramFun_ne_of_mem_Ioo {c w1 w2 : ℂ} (hD : 0 < (conj w1 * w2).im)
    {x y : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) (t : ℝ) :
    parallelogramFun c w1 w2 t ≠ c + (x : ℂ) * w1 + (y : ℂ) * w2 := by
  intro heq
  by_cases ht : t ≤ 1/4
  · rw [parallelogramFun_eq_edge1 c w1 w2 ht] at heq
    have h0 : (conj w1 *
        ((c + (Real.smoothTransition (4 * t) : ℂ) * w1) -
          (c + (x : ℂ) * w1 + (y : ℂ) * w2))).im = 0 := by rw [heq]; simp
    rw [show (c + (Real.smoothTransition (4 * t) : ℂ) * w1) -
        (c + (x : ℂ) * w1 + (y : ℂ) * w2) =
        ((Real.smoothTransition (4 * t) - x : ℝ) : ℂ) * w1 + ((-y : ℝ) : ℂ) * w2 by push_cast; ring,
      im_conj_w1_mul_combo] at h0
    nlinarith
  push Not at ht
  by_cases ht2 : t ≤ 1/2
  · rw [parallelogramFun_eq_edge2 c w1 w2 ht.le ht2] at heq
    have h0 : (conj w2 *
        ((c + w1 + (Real.smoothTransition (4 * t - 1) : ℂ) * w2) -
          (c + (x : ℂ) * w1 + (y : ℂ) * w2))).im = 0 := by rw [heq]; simp
    rw [show (c + w1 + (Real.smoothTransition (4 * t - 1) : ℂ) * w2) -
        (c + (x : ℂ) * w1 + (y : ℂ) * w2) =
        ((1 - x : ℝ) : ℂ) * w1 + ((Real.smoothTransition (4 * t - 1) - y : ℝ) : ℂ) * w2 by
        push_cast; ring,
      im_conj_w2_mul_combo, im_conj_w2_w1_eq_neg] at h0
    nlinarith
  push Not at ht2
  by_cases ht3 : t ≤ 3/4
  · rw [parallelogramFun_eq_edge3 c w1 w2 ht2.le ht3] at heq
    have h0 : (conj w1 *
        ((c + w1 + w2 + (Real.smoothTransition (4 * t - 2) : ℂ) * (-w1)) -
          (c + (x : ℂ) * w1 + (y : ℂ) * w2))).im = 0 := by rw [heq]; simp
    rw [show (c + w1 + w2 + (Real.smoothTransition (4 * t - 2) : ℂ) * (-w1)) -
        (c + (x : ℂ) * w1 + (y : ℂ) * w2) =
        ((1 - Real.smoothTransition (4 * t - 2) - x : ℝ) : ℂ) * w1 + ((1 - y : ℝ) : ℂ) * w2 by
        push_cast; ring,
      im_conj_w1_mul_combo] at h0
    nlinarith
  · push Not at ht3
    rw [parallelogramFun_eq_edge4 c w1 w2 ht3.le] at heq
    have h0 : (conj w2 *
        ((c + w2 + (Real.smoothTransition (4 * t - 3) : ℂ) * (-w2)) -
          (c + (x : ℂ) * w1 + (y : ℂ) * w2))).im = 0 := by rw [heq]; simp
    rw [show (c + w2 + (Real.smoothTransition (4 * t - 3) : ℂ) * (-w2)) -
        (c + (x : ℂ) * w1 + (y : ℂ) * w2) =
        ((-x : ℝ) : ℂ) * w1 + ((1 - Real.smoothTransition (4 * t - 3) - y : ℝ) : ℂ) * w2 by
        push_cast; ring,
      im_conj_w2_mul_combo, im_conj_w2_w1_eq_neg] at h0
    nlinarith

/-- `Im (v * conj z) = -Im (conj v * z)`. -/
theorem im_mul_conj_eq_neg_im_conj_mul (v z : ℂ) : (v * conj z).im = -(conj v * z).im := by
  rw [show v * conj z = conj (conj v * z) by rw [map_mul, Complex.conj_conj]]
  simp only [Complex.conj_im]

/-- The reparametrization `t ↦ smoothTransition (4 t - k)` is differentiable on all of `ℝ`,
for any shift `k`. -/
theorem differentiable_smoothTransition_sub (k : ℝ) :
    Differentiable ℝ (fun t : ℝ ↦ Real.smoothTransition (4 * t - k)) :=
  ((Real.smoothTransition.contDiff (n := ⊤)).comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)).differentiable (by norm_num)

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

/-- The logarithmic-derivative integrand of a smooth parallelogram loop is continuous
when the evaluation point avoids the loop. -/
private theorem continuous_parallelogram_logDeriv {c w1 w2 w : ℂ}
    (hwne : ∀ t : ℝ, parallelogramFun c w1 w2 t ≠ w) :
    Continuous (fun t ↦ deriv (parallelogramFun c w1 w2) t *
      (parallelogramFun c w1 w2 t - w)⁻¹) := by
  have hcont1 : Continuous (deriv (parallelogramFun c w1 w2)) :=
    ((contDiff_parallelogramFun c w1 w2).iterate_deriv 1).continuous
  have hcont2 : Continuous (fun t ↦ (parallelogramFun c w1 w2 t - w)⁻¹) := by
    apply Continuous.inv₀ ((continuous_parallelogramFun c w1 w2).sub continuous_const)
    exact fun t ↦ sub_ne_zero.mpr (hwne t)
  have hcontF : Continuous (fun t ↦ deriv (parallelogramFun c w1 w2) t *
      (parallelogramFun c w1 w2 t - w)⁻¹) := hcont1.mul hcont2
  exact hcontF

/-- The total turning integral of the positively oriented parallelogram about an interior
point lies strictly between zero and `4π`. -/
private theorem parallelogram_turning_integral_mem_Ioo {c w1 w2 : ℂ}
    (hD : 0 < (conj w1 * w2).im) {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    (∫ t in (0 : ℝ)..1, (deriv (parallelogramFun c w1 w2) t *
      (parallelogramFun c w1 w2 t - (c + (x : ℂ) * w1 + (y : ℂ) * w2))⁻¹).im) ∈
      Set.Ioo (0 : ℝ) (4 * Real.pi) := by
  set w := c + (x : ℂ) * w1 + (y : ℂ) * w2 with hw_def
  have hwne : ∀ t : ℝ, parallelogramFun c w1 w2 t ≠ w :=
    parallelogramFun_ne_of_mem_Ioo hD hx0 hx1 hy0 hy1
  have hv1 : w1 ≠ 0 := fun h ↦ by simp [h] at hD
  have hv2 : w2 ≠ 0 := fun h ↦ by simp [h] at hD
  have hcontF := continuous_parallelogram_logDeriv hwne
  obtain ⟨hC1, hC2, hC3, hC4⟩ :=
    parallelogram_edge_crossProducts_pos hD hx0 hx1 hy0 hy1 hw_def
  -- The four edges' contributions.
  have hI1 := im_edge_integral_mem_Ioo (c := c) (w1 := w1) (w2 := w2) (w := w) (p := c)
    (v := w1) (a := 0) (b := 1/4) (by norm_num) hv1
    hC1
    hwne (φ := fun t ↦ Real.smoothTransition (4 * t - 0))
    (differentiable_smoothTransition_sub 0).continuous.continuousOn
    (fun t _ ↦ (differentiable_smoothTransition_sub 0).differentiableAt.hasDerivAt)
    (Real.smoothTransition.zero_of_nonpos (by norm_num))
    (Real.smoothTransition.one_of_one_le (by norm_num))
    (fun t ht ↦ by
      simp only [parallelogramFun_eq_edge1 c w1 w2 ht.2.le, sub_zero])
  have hI2 := im_edge_integral_mem_Ioo (c := c) (w1 := w1) (w2 := w2) (w := w) (p := c + w1)
    (v := w2) (a := 1/4) (b := 1/2) (by norm_num) hv2
    hC2
    hwne (φ := fun t ↦ Real.smoothTransition (4 * t - 1))
    (differentiable_smoothTransition_sub 1).continuous.continuousOn
    (fun t _ ↦ (differentiable_smoothTransition_sub 1).differentiableAt.hasDerivAt)
    (Real.smoothTransition.zero_of_nonpos (by norm_num))
    (Real.smoothTransition.one_of_one_le (by norm_num))
    (fun t ht ↦ parallelogramFun_eq_edge2 c w1 w2 ht.1.le ht.2.le)
  have hI3 := im_edge_integral_mem_Ioo (c := c) (w1 := w1) (w2 := w2) (w := w) (p := c + w1 + w2)
    (v := -w1) (a := 1/2) (b := 3/4) (by norm_num) (neg_ne_zero.mpr hv1)
    hC3
    hwne (φ := fun t ↦ Real.smoothTransition (4 * t - 2))
    (differentiable_smoothTransition_sub 2).continuous.continuousOn
    (fun t _ ↦ (differentiable_smoothTransition_sub 2).differentiableAt.hasDerivAt)
    (Real.smoothTransition.zero_of_nonpos (by norm_num))
    (Real.smoothTransition.one_of_one_le (by norm_num))
    (fun t ht ↦ parallelogramFun_eq_edge3 c w1 w2 ht.1.le ht.2.le)
  have hI4 := im_edge_integral_mem_Ioo (c := c) (w1 := w1) (w2 := w2) (w := w) (p := c + w2)
    (v := -w2) (a := 3/4) (b := 1) (by norm_num) (neg_ne_zero.mpr hv2)
    hC4
    hwne (φ := fun t ↦ Real.smoothTransition (4 * t - 3))
    (differentiable_smoothTransition_sub 3).continuous.continuousOn
    (fun t _ ↦ (differentiable_smoothTransition_sub 3).differentiableAt.hasDerivAt)
    (Real.smoothTransition.zero_of_nonpos (by norm_num))
    (Real.smoothTransition.one_of_one_le (by norm_num))
    (fun t ht ↦ parallelogramFun_eq_edge4 c w1 w2 ht.1.le)
  have hcontIm : Continuous (fun t ↦ (deriv (parallelogramFun c w1 w2) t *
      (parallelogramFun c w1 w2 t - w)⁻¹).im) := Complex.continuous_im.comp hcontF
  have hIntIm : ∀ a b : ℝ, IntervalIntegrable (fun t ↦ (deriv (parallelogramFun c w1 w2) t *
      (parallelogramFun c w1 w2 t - w)⁻¹).im) MeasureTheory.volume a b :=
    fun a b ↦ hcontIm.intervalIntegrable a b
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (hIntIm 0 (1/4)) (hIntIm (1/4) (1/2))
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (hIntIm 0 (1/2)) (hIntIm (1/2) (3/4))
  have hsplit3 := intervalIntegral.integral_add_adjacent_intervals
    (hIntIm 0 (3/4)) (hIntIm (3/4) 1)
  have hTotalBound : (∫ t in (0:ℝ)..1, (deriv (parallelogramFun c w1 w2) t *
      (parallelogramFun c w1 w2 t - w)⁻¹).im) ∈ Set.Ioo (0:ℝ) (4 * Real.pi) := by
    rw [← hsplit3, ← hsplit2, ← hsplit1]
    exact ⟨by linarith [hI1.1, hI2.1, hI3.1, hI4.1], by linarith [hI1.2, hI2.2, hI3.2, hI4.2]⟩
  exact hTotalBound

/-- **The index of the parallelogram boundary is `1` at every point of the open
parallelogram**, given `w1, w2` positively oriented (`Im (conj w1 * w2) > 0`). -/
theorem curveIndex_parallelogramLoop_eq_one {c w1 w2 : ℂ} (hD : 0 < (conj w1 * w2).im)
    {x y : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    curveIndex (parallelogramLoop c w1 w2) (c + (x : ℂ) * w1 + (y : ℂ) * w2) = 1 := by
  set w := c + (x : ℂ) * w1 + (y : ℂ) * w2
  have hwne : ∀ t : ℝ, parallelogramFun c w1 w2 t ≠ w :=
    parallelogramFun_ne_of_mem_Ioo hD hx0 hx1 hy0 hy1
  have hcontF := continuous_parallelogram_logDeriv hwne
  have hTotalBound := parallelogram_turning_integral_mem_Ioo (c := c) hD hx0 hx1 hy0 hy1
  have hwneI : ∀ t : I, parallelogramLoop c w1 w2 t ≠ w := fun t ↦ hwne (t : ℝ)
  obtain ⟨n, hn⟩ := exists_int_curveIndex (parallelogramLoop c w1 w2)
    (contDiffOn_parallelogramLoop_extend c w1 w2) hwneI
  have hCI := curveIntegral_sub_inv_eq_two_pi_I_mul_curveIndex (parallelogramLoop c w1 w2) w
  rw [hn] at hCI
  have hCIeq : curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹))
      (parallelogramLoop c w1 w2) =
      ∫ t in (0:ℝ)..1, deriv (parallelogramFun c w1 w2) t *
        (parallelogramFun c w1 w2 t - w)⁻¹ := by
    rw [curveIntegral_eq_intervalIntegral_deriv, parallelogramLoop_extend]
    simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  rw [hCIeq] at hCI
  have hInt : IntervalIntegrable (fun t ↦ deriv (parallelogramFun c w1 w2) t *
      (parallelogramFun c w1 w2 t - w)⁻¹) MeasureTheory.volume 0 1 := hcontF.intervalIntegrable 0 1
  have himeq : (∫ t in (0:ℝ)..1, (deriv (parallelogramFun c w1 w2) t *
      (parallelogramFun c w1 w2 t - w)⁻¹).im) = (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)).im := by
    have h := intervalIntegral.intervalIntegral_im hInt
    simp only [RCLike.im_eq_complex_im] at h
    rw [h, hCI]
  have hRHS : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)).im = 2 * Real.pi * (n : ℝ) := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [hRHS] at himeq
  rw [himeq] at hTotalBound
  have hnbound : (0:ℝ) < (n:ℝ) ∧ (n:ℝ) < 2 := by
    constructor
    · nlinarith [hTotalBound.1, Real.pi_pos]
    · nlinarith [hTotalBound.2, Real.pi_pos]
  have : n = 1 := by
    have h1 : (0:ℤ) < n := by exact_mod_cast hnbound.1
    have h2 : n < 2 := by exact_mod_cast hnbound.2
    omega
  rw [hn, this]
  norm_num

end Complex

end
