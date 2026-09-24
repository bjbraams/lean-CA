/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# The chordal metric on the Riemann sphere

The chordal (spherical) metric on `ℂ ∪ {∞}` (Mathlib's `OnePoint ℂ`) is the Euclidean distance
between the images of two points under inverse stereographic projection onto the unit sphere in
`ℝ³`. This file defines the projection `stereographicInv`, shows it lands on the unit sphere,
and defines the chordal distance `chordalDist` as the pulled-back Euclidean distance — which
gives every metric-space axiom (symmetry, the triangle inequality, nonnegativity) for free from
the ambient Euclidean metric, rather than by a direct (and considerably messier) algebraic
argument. The classical closed-form formula
`chordalDist z w = 2 ‖z - w‖ / (√(1 + ‖z‖²) √(1 + ‖w‖²))`
is then recovered as a theorem about this definition.

## Main definitions

* `Complex.stereographicInv`: inverse stereographic projection `OnePoint ℂ → EuclideanSpace ℝ
  (Fin 3)`.
* `Complex.chordalDist`: the chordal distance on `OnePoint ℂ`.

## Main results

* `Complex.norm_stereographicInv`: the projection lands on the unit sphere.
* `Complex.stereographicInv_injective`: the projection is injective.
* `Complex.chordalDist_triangle`, `Complex.chordalDist_comm`, `Complex.chordalDist_nonneg`,
  `Complex.chordalDist_eq_zero_iff`: the chordal distance is a genuine metric.
* `Complex.chordalDist_coe_coe`, `Complex.chordalDist_coe_infty`: the classical closed-form
  formula.
* `Complex.chordalDist_lt_two`: the chordal distance is bounded by the diameter of the sphere.

## References

* L. V. Ahlfors, *Complex Analysis*, Chapter 1, Section 2.3.
* J. B. Conway, *Functions of One Complex Variable*, Chapter 1, Section 6.
-/

public noncomputable section

open Set Function
open scoped Topology OnePoint

namespace Complex

/-- **Inverse stereographic projection.** Sends a finite point `z` to
`(2 Re z, 2 Im z, ‖z‖² - 1) / (‖z‖² + 1)` on the unit sphere in `ℝ³`, and `∞` to the north pole
`(0, 0, 1)`. -/
def stereographicInv : OnePoint ℂ → EuclideanSpace ℝ (Fin 3)
  | (z : ℂ) => !₂[2 * z.re / (normSq z + 1), 2 * z.im / (normSq z + 1),
      (normSq z - 1) / (normSq z + 1)]
  | ∞ => !₂[0, 0, 1]

/-- **Inverse stereographic projection lands on the unit sphere.** -/
theorem norm_stereographicInv (p : OnePoint ℂ) : ‖stereographicInv p‖ = 1 := by
  induction p using OnePoint.rec with
  | infty =>
    simp [stereographicInv, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  | coe z =>
    have hd : (0:ℝ) < normSq z + 1 := by
      have := normSq_nonneg z; linarith
    simp only [stereographicInv]
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    have heq : ‖(!₂[2 * z.re / (normSq z + 1), 2 * z.im / (normSq z + 1),
          (normSq z - 1) / (normSq z + 1)] : EuclideanSpace ℝ (Fin 3)) 0‖ ^ 2 +
        ‖(!₂[2 * z.re / (normSq z + 1), 2 * z.im / (normSq z + 1),
          (normSq z - 1) / (normSq z + 1)] : EuclideanSpace ℝ (Fin 3)) 1‖ ^ 2 +
        ‖(!₂[2 * z.re / (normSq z + 1), 2 * z.im / (normSq z + 1),
          (normSq z - 1) / (normSq z + 1)] : EuclideanSpace ℝ (Fin 3)) 2‖ ^ 2 = 1 := by
      simp only [Real.norm_eq_abs, sq_abs,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]
      rw [Complex.normSq_apply] at hd ⊢
      field_simp
      ring
    rw [heq, Real.sqrt_one]

/-- **Inverse stereographic projection is injective.** -/
theorem stereographicInv_injective : Injective stereographicInv := by
  intro p q hpq
  induction p using OnePoint.rec with
  | infty =>
    induction q using OnePoint.rec with
    | infty => rfl
    | coe w =>
      exfalso
      have h2 := congrFun (congrArg WithLp.ofLp hpq) 2
      simp only [stereographicInv, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h2
      have hd : (0:ℝ) < normSq w + 1 := by have := normSq_nonneg w; linarith
      rw [eq_div_iff hd.ne'] at h2
      linarith
  | coe z =>
    induction q using OnePoint.rec with
    | infty =>
      exfalso
      have h2 := congrFun (congrArg WithLp.ofLp hpq) 2
      simp only [stereographicInv, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h2
      have hd : (0:ℝ) < normSq z + 1 := by have := normSq_nonneg z; linarith
      rw [div_eq_one_iff_eq hd.ne'] at h2
      linarith
    | coe w =>
      have h0 := congrFun (congrArg WithLp.ofLp hpq) 0
      have h1 := congrFun (congrArg WithLp.ofLp hpq) 1
      have h2 := congrFun (congrArg WithLp.ofLp hpq) 2
      simp only [stereographicInv, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
      have hdz : (0:ℝ) < normSq z + 1 := by have := normSq_nonneg z; linarith
      have hdw : (0:ℝ) < normSq w + 1 := by have := normSq_nonneg w; linarith
      rw [div_eq_div_iff hdz.ne' hdw.ne'] at h2
      have hnn : normSq z = normSq w := by linarith
      rw [hnn, div_eq_div_iff hdw.ne' hdw.ne'] at h0
      rw [hnn, div_eq_div_iff hdw.ne' hdw.ne'] at h1
      have hzre : z.re = w.re := by
        have := mul_right_cancel₀ hdw.ne' h0; linarith
      have hzim : z.im = w.im := by
        have := mul_right_cancel₀ hdw.ne' h1; linarith
      exact congrArg (↑· : ℂ → OnePoint ℂ) (Complex.ext hzre hzim)

/-- **The chordal (spherical) distance.** The Euclidean distance between the images of `p` and
`q` under inverse stereographic projection onto the unit sphere in `ℝ³`. -/
def chordalDist (p q : OnePoint ℂ) : ℝ := dist (stereographicInv p) (stereographicInv q)

/-- The chordal distance is symmetric. -/
theorem chordalDist_comm (p q : OnePoint ℂ) : chordalDist p q = chordalDist q p := dist_comm _ _

/-- The chordal distance is nonnegative. -/
theorem chordalDist_nonneg (p q : OnePoint ℂ) : 0 ≤ chordalDist p q := dist_nonneg

/-- The chordal distance from a point to itself is zero. -/
@[simp] theorem chordalDist_self (p : OnePoint ℂ) : chordalDist p p = 0 := dist_self _

/-- **The chordal distance satisfies the triangle inequality**, inherited directly from the
Euclidean distance on `ℝ³` via `stereographicInv`. -/
theorem chordalDist_triangle (p q r : OnePoint ℂ) :
    chordalDist p r ≤ chordalDist p q + chordalDist q r := dist_triangle _ _ _

/-- The chordal distance is definite: it vanishes only between a point and itself. -/
theorem chordalDist_eq_zero_iff {p q : OnePoint ℂ} : chordalDist p q = 0 ↔ p = q :=
  dist_eq_zero.trans stereographicInv_injective.eq_iff

/-- The chordal distance is bounded by the diameter of the unit sphere. -/
theorem chordalDist_le_two (p q : OnePoint ℂ) : chordalDist p q ≤ 2 := by
  rw [chordalDist]
  calc dist (stereographicInv p) (stereographicInv q)
      = ‖stereographicInv p - stereographicInv q‖ := dist_eq_norm _ _
    _ ≤ ‖stereographicInv p‖ + ‖stereographicInv q‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_stereographicInv, norm_stereographicInv]; norm_num

/-- **The classical closed-form formula for the chordal distance between two finite points.** -/
theorem chordalDist_coe_coe (z w : ℂ) :
    chordalDist (z : OnePoint ℂ) (w : OnePoint ℂ) =
      2 * ‖z - w‖ / (Real.sqrt (1 + normSq z) * Real.sqrt (1 + normSq w)) := by
  have hdz : (0:ℝ) < normSq z + 1 := by have := normSq_nonneg z; linarith
  have hdw : (0:ℝ) < normSq w + 1 := by have := normSq_nonneg w; linarith
  rw [chordalDist]
  simp only [stereographicInv]
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp only [Real.dist_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, sq_abs]
  have hsum : (2 * z.re / (normSq z + 1) - 2 * w.re / (normSq w + 1)) ^ 2 +
      (2 * z.im / (normSq z + 1) - 2 * w.im / (normSq w + 1)) ^ 2 +
      ((normSq z - 1) / (normSq z + 1) - (normSq w - 1) / (normSq w + 1)) ^ 2 =
      4 * normSq (z - w) / ((normSq z + 1) * (normSq w + 1)) := by
    rw [Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im]
    field_simp
    ring
  rw [hsum]
  have hAsq : Real.sqrt (1 + normSq z) ^ 2 = 1 + normSq z :=
    Real.sq_sqrt (by linarith)
  have hBsq : Real.sqrt (1 + normSq w) ^ 2 = 1 + normSq w :=
    Real.sq_sqrt (by linarith)
  have hzw : ‖z - w‖ ^ 2 = normSq (z - w) := Complex.sq_norm (z - w)
  rw [show (4:ℝ) * normSq (z - w) / ((normSq z + 1) * (normSq w + 1)) =
      (2 * ‖z - w‖ / (Real.sqrt (1 + normSq z) * Real.sqrt (1 + normSq w))) ^ 2 by
    rw [div_pow, mul_pow, mul_pow, hAsq, hBsq, hzw]
    ring]
  rw [Real.sqrt_sq (by positivity)]

/-- **The classical closed-form formula for the chordal distance from a finite point to
`∞`.** -/
theorem chordalDist_coe_infty (z : ℂ) :
    chordalDist (z : OnePoint ℂ) ∞ = 2 / Real.sqrt (1 + normSq z) := by
  have hdz : (0:ℝ) < normSq z + 1 := by have := normSq_nonneg z; linarith
  rw [chordalDist]
  simp only [stereographicInv]
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp only [Real.dist_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, sq_abs]
  have hsum : (2 * z.re / (normSq z + 1) - 0) ^ 2 + (2 * z.im / (normSq z + 1) - 0) ^ 2 +
      ((normSq z - 1) / (normSq z + 1) - 1) ^ 2 = 4 / (normSq z + 1) := by
    rw [Complex.normSq_apply]
    field_simp
    ring
  rw [hsum]
  have hAsq : Real.sqrt (1 + normSq z) ^ 2 = 1 + normSq z := Real.sq_sqrt (by linarith)
  rw [show (4:ℝ) / (normSq z + 1) = (2 / Real.sqrt (1 + normSq z)) ^ 2 by
    rw [div_pow, hAsq]; ring]
  rw [Real.sqrt_sq (by positivity)]

end Complex
end
