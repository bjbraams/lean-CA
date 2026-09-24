/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Geometry of the right half-plane

Products and quotients of right-half-plane points avoid the principal branch cut.
Square roots lie in a smaller sector, and finite families fit inside a disk tangent
to the imaginary axis. These results do not depend on special-function domains.

## Main results

* `Complex.mul_mem_slitPlane_of_re_pos`: A product of two right-half-plane numbers avoids the
  principal branch cut.
* `Complex.sq_mem_slitPlane_of_re_pos`: Squaring a right-half-plane number can leave that
  half-plane but not the slit plane.
* `Complex.div_mem_slitPlane_of_re_pos`: A ratio of two right-half-plane numbers cannot lie on
  the nonpositive real axis.
* `Complex.exists_sq_eq_of_re_pos`: A number with positive real part has a square root in the
  sector `|im x| < re x`.
* `Complex.exists_pos_real_center_norm_sub_lt`: A finite right-half-plane node vector lies in a
  disk centered on the positive real axis whose open disk is contained in the right half-plane.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section
open Set
namespace Complex

/-- A product of two right-half-plane numbers avoids the principal branch cut. -/
theorem mul_mem_slitPlane_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    x * y ∈ slitPlane := by
  apply mem_slitPlane_iff.mpr
  by_cases hi : (x * y).im = 0
  · left
    have hid : x.re * (x * y).re = y.re * (x.re ^ 2 + x.im ^ 2) - x.im * (x * y).im := by
      simp only [mul_re, mul_im]
      ring
    rw [hi, mul_zero, sub_zero] at hid
    have hp : 0 < y.re * (x.re ^ 2 + x.im ^ 2) :=
      mul_pos hy (add_pos_of_pos_of_nonneg (sq_pos_of_pos hx) (sq_nonneg _))
    exact (mul_pos_iff_of_pos_left hx).mp (hid.symm ▸ hp)
  · exact Or.inr hi

/-- Squaring a right-half-plane number can leave that half-plane but not the slit plane. -/
theorem sq_mem_slitPlane_of_re_pos {x : ℂ} (hx : 0 < x.re) : x ^ 2 ∈ slitPlane := by
  simpa only [pow_two] using mul_mem_slitPlane_of_re_pos hx hx

/-- A ratio of two right-half-plane numbers cannot lie on the nonpositive real axis. -/
theorem div_mem_slitPlane_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    x / y ∈ slitPlane := by
  apply mem_slitPlane_iff.mpr
  by_cases hi : (x / y).im = 0
  · left
    have h := congrArg Complex.re (div_mul_cancel₀ x (ne_zero_of_re_pos hy))
    rw [mul_re, hi, zero_mul, sub_zero] at h
    nlinarith
  · exact Or.inr hi

/-- A number with positive real part has a square root in the sector `|im x| < re x`. -/
theorem exists_sq_eq_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ∃ x : ℂ, x ^ 2 = z ∧ 0 < x.re ∧ |x.im| < x.re := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq z (show 0 < (2 : ℕ) by omega)
  have hs : u.im ^ 2 < u.re ^ 2 := by
    have H := congrArg Complex.re hu
    simp only [pow_two, mul_re] at H
    nlinarith
  have hn : u.re ≠ 0 := by intro h; rw [h] at hs; nlinarith [sq_nonneg u.im]
  have hp : ∀ v : ℂ, v ^ 2 = z → 0 < v.re → |v.im| < v.re := by
    intro v hv hvp
    have H := congrArg Complex.re hv
    simp only [pow_two, mul_re] at H
    exact (sq_lt_sq₀ (abs_nonneg _) hvp.le).mp (by rw [sq_abs]; nlinarith)
  rcases lt_or_gt_of_ne hn with h | h
  · refine ⟨-u, by simpa using hu, by simpa using neg_pos.mpr h, ?_⟩
    exact hp (-u) (by simpa using hu) (by simpa using neg_pos.mpr h)
  · exact ⟨u, hu, h, hp u hu h⟩

/-- A finite right-half-plane node vector lies in a disk centered on the positive
real axis whose open disk is contained in the right half-plane. -/
theorem exists_pos_real_center_norm_sub_lt {ι : Type*} [Fintype ι]
    {z : ι → ℂ} (hz : ∀ i, 0 < (z i).re) :
    ∃ A : ℝ, 0 < A ∧ ‖fun i => z i - (A : ℂ)‖ < A := by
  let d := fun i => normSq (z i) / (2 * (z i).re)
  have hd (i : ι) : 0 ≤ d i :=
    div_nonneg (normSq_nonneg _) (mul_nonneg (by norm_num) (hz i).le)
  let A := (∑ i, d i) + 1
  have hA : 0 < A :=
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun i _ => hd i)) zero_lt_one
  refine ⟨A, hA, (pi_norm_lt_iff hA).mpr (fun i => ?_)⟩
  have hi : d i < A := lt_of_le_of_lt
    (Finset.single_le_sum (fun j _ => hd j) (Finset.mem_univ i)) (by dsimp [A]; linarith)
  have hip : normSq (z i) < A * (2 * (z i).re) :=
    (div_lt_iff₀ (mul_pos (by norm_num) (hz i))).mp hi
  have hs : ‖z i - (A : ℂ)‖ ^ 2 = normSq (z i) + A ^ 2 - 2 * (z i).re * A := by
    rw [Complex.sq_norm, normSq_sub]
    simp [normSq_ofReal, mul_re, pow_two, mul_assoc]
  nlinarith [norm_nonneg (z i - (A : ℂ))]

end Complex
end
