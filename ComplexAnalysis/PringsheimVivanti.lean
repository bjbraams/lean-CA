/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.LaurentSeries.Basic

/-!
# The Pringsheim–Vivanti theorem

A power series `∑ a_n z^n` with nonnegative real coefficients and finite positive radius of convergence
`R` cannot be continued holomorphically across the boundary point `z = R`: if it could, the
series would in fact converge at some real point beyond `R`, contradicting that `R` is the
radius of convergence.

The proof is the classical one. Fix a point `x0` strictly between `0` and `R`, close enough to
`R` that the holomorphic extension near `R` provides a genuinely larger disc of convergence for
the Taylor series of the extension at `x0` than the disc of convergence at `0` alone would give.
The Taylor coefficients of the extension at `x0`, computed on a small circle entirely inside the
original disc of convergence, are then explicit convergent sums
`∑ₖ a_k C(k, n) x0^(k - n)` — manifestly nonnegative, since every `a_k`, binomial coefficient,
and power of `x0` is nonnegative. Evaluating this Taylor series at a real point `z0` beyond `R`
(available because the disc of convergence at `x0` reaches past `R`) gives a convergent series
of nonnegative terms. Summability of the coefficient rows and their sums allows the resulting
nonnegative double series to be summed in the opposite order. Each resulting finite binomial
row evaluates to `a_k z0^k`, so `∑ a_k z0^k` converges.

The Taylor coefficients themselves are computed via `Complex.circleLaurentCoeff`
(`LaurentSeries.Basic`) applied to the extension composed with translation by `x0`, together
with an explicit term-by-term circle integration of the original series (justified by uniform
convergence on the small circle, Weierstrass's `M`-test) and the elementary evaluation of
`∮ z^m dz` around the origin.

## Main results

* `Complex.exists_gt_summable_of_forall_nonneg_of_differentiableOn_union_ball`:
  **the Pringsheim–Vivanti theorem**. If the sum of a power series with nonnegative
  coefficients extends holomorphically to a neighborhood of the positive real boundary point `R` of its disc of
  convergence, the series converges at some real point beyond `R`.

## References

* R. Remmert, *Theory of Complex Functions*, Chapter 5, Section 5.1 (the Pringsheim–Vivanti
  theorem).
* R. B. Burckel, *An Introduction to Classical Complex Analysis*, Section 11.3.
-/

public noncomputable section

open Set Metric Filter MeasureTheory Complex
open scoped Topology Real

namespace Complex

/-- Term-by-term circle integration of a power series recentered at `x0`, on a circle of
radius `r` with `x0 + r` inside the original radius of convergence: interchanging the circle
integral with the sum is justified by uniform convergence of the partial sums on the circle
(Weierstrass's `M`-test). -/
theorem circleIntegral_zpow_mul_tsum_add_eq (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (x0 r : ℝ)
    (hx0 : 0 ≤ x0) (hr : 0 < r) (hconv : Summable (fun k => a k * (x0 + r) ^ k)) (n : ℤ) :
    (∮ w in C(0, r), w ^ n * (∑' k, (a k : ℂ) * ((x0 : ℂ) + w) ^ k)) =
      ∑' k, (a k : ℂ) * ∮ w in C(0, r), w ^ n * ((x0 : ℂ) + w) ^ k := by
  set f : ℕ → ℂ → ℂ := fun k w => w ^ n * ((a k : ℂ) * ((x0 : ℂ) + w) ^ k) with hf_def
  have hfcont : ∀ k, ContinuousOn (f k) (sphere (0 : ℂ) r) := by
    intro k
    rw [hf_def]
    apply ContinuousOn.mul
    · exact (continuousOn_zpow₀ n).mono (fun w hw => by
        rw [mem_sphere_zero_iff_norm] at hw
        rintro rfl
        simp at hw
        linarith)
    · fun_prop
  have hbound : ∀ k w, ‖w‖ = r → ‖f k w‖ ≤ r ^ n * (a k * (x0 + r) ^ k) := by
    intro k w hw
    rw [hf_def]
    simp only
    rw [norm_mul, norm_zpow, hw, norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha k), norm_pow]
    have h1 : ‖(x0 : ℂ) + w‖ ≤ x0 + r := by
      calc ‖(x0 : ℂ) + w‖ ≤ ‖(x0 : ℂ)‖ + ‖w‖ := norm_add_le _ _
        _ = x0 + r := by rw [Complex.norm_real, Real.norm_of_nonneg hx0, hw]
    gcongr
    exact ha k
  have hsum2 : Summable (fun k => r ^ n * (a k * (x0 + r) ^ k)) := hconv.mul_left _
  have htu : TendstoUniformlyOn (fun N => fun w => ∑ k ∈ Finset.range N, f k w)
      (fun w => ∑' k, f k w) atTop (sphere (0 : ℂ) r) := by
    apply tendstoUniformlyOn_tsum_nat (f := f) hsum2
    intro k w hw
    rw [mem_sphere_zero_iff_norm] at hw
    exact hbound k w hw
  have hcont : ∀ᶠ N in atTop,
      ContinuousOn (fun w => ∑ k ∈ Finset.range N, f k w) (sphere (0 : ℂ) r) := by
    filter_upwards with N
    exact continuousOn_finsetSum _ fun k _ => hfcont k
  have htend := TendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn hr.le hcont htu
  have hgeq : (fun w => ∑' k, f k w) = fun w => w ^ n * ∑' k, (a k : ℂ) * ((x0 : ℂ) + w) ^ k := by
    funext w
    rw [hf_def]
    simp only
    rw [tsum_mul_left]
  rw [hgeq] at htend
  have hrhs : ∀ N : ℕ, (∮ w in C(0, r), (∑ k ∈ Finset.range N, f k w)) =
      ∑ k ∈ Finset.range N, ∮ w in C(0, r), f k w := by
    intro N
    unfold circleIntegral
    rw [show (fun θ : ℝ => deriv (circleMap 0 r) θ • ∑ k ∈ Finset.range N, f k (circleMap 0 r θ))
        = fun θ => ∑ k ∈ Finset.range N, deriv (circleMap 0 r) θ • f k (circleMap 0 r θ) by
      funext θ; rw [Finset.smul_sum]]
    have hderiv : Continuous (fun θ => deriv (circleMap (0 : ℂ) r) θ) := by
      simp_rw [deriv_circleMap]; fun_prop
    exact intervalIntegral.integral_finsetSum (fun k _ =>
      (hderiv.smul ((hfcont k).comp_continuous (continuous_circleMap 0 r)
        (fun θ => circleMap_mem_sphere 0 hr.le θ))).intervalIntegrable 0 (2 * Real.pi))
  simp only [hrhs] at htend
  have hnormbound : ∀ k,
      ‖∮ w in C(0, r), f k w‖ ≤ 2 * Real.pi * r * (r ^ n * (a k * (x0 + r) ^ k)) := by
    intro k
    have := circleIntegral.norm_integral_le_of_norm_le_const hr.le
      (f := f k) (C := r ^ n * (a k * (x0 + r) ^ k)) (fun w hw => hbound k w (by
        rw [mem_sphere_zero_iff_norm] at hw; exact hw))
    linarith
  have hcompsum : Summable (fun k => ‖∮ w in C(0, r), f k w‖) := by
    apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) hnormbound
    exact hsum2.mul_left _
  have hsummable : Summable (fun k => ∮ w in C(0, r), f k w) := hcompsum.of_norm
  have hlim1 := hsummable.hasSum.tendsto_sum_nat
  have heq := tendsto_nhds_unique hlim1 htend
  rw [← heq]
  refine tsum_congr fun k => ?_
  rw [hf_def]
  simp only
  rw [show (fun w : ℂ => w ^ n * ((a k : ℂ) * ((x0 : ℂ) + w) ^ k)) =
      fun w => (a k : ℂ) • (w ^ n * ((x0 : ℂ) + w) ^ k) by
    funext w; rw [smul_eq_mul]; ring]
  rw [circleIntegral.integral_smul]
  rfl

/-- Finite-sum linearity of the circle integral, given continuity of each summand on the
circle. -/
theorem circleIntegral_finsetSum {ι : Type*} (s : Finset ι) (g : ι → ℂ → ℂ) (c : ℂ) {R : ℝ}
    (hR : 0 ≤ R) (hg : ∀ i ∈ s, ContinuousOn (g i) (sphere c R)) :
    (∮ w in C(c, R), ∑ i ∈ s, g i w) = ∑ i ∈ s, ∮ w in C(c, R), g i w := by
  unfold circleIntegral
  rw [show (fun θ : ℝ => deriv (circleMap c R) θ • ∑ i ∈ s, g i (circleMap c R θ))
      = fun θ => ∑ i ∈ s, deriv (circleMap c R) θ • g i (circleMap c R θ) by
    funext θ; rw [Finset.smul_sum]]
  have hderiv : Continuous (fun θ => deriv (circleMap c R) θ) := by
    simp_rw [deriv_circleMap]; fun_prop
  refine intervalIntegral.integral_finsetSum (fun i hi => ?_)
  exact (hderiv.smul ((hg i hi).comp_continuous (continuous_circleMap c R)
    (fun θ => circleMap_mem_sphere c hR θ))).intervalIntegrable 0 (2 * Real.pi)

/-- The circle integral of `z^m` around its own center: `2πi` if `m = -1`, else `0`. -/
theorem circleIntegral_zpow_eq (r : ℝ) (hr : 0 < r) (m : ℤ) :
    (∮ z in C(0, r), z ^ m) = if m = -1 then 2 * Real.pi * I else 0 := by
  split_ifs with hm
  · subst hm
    rw [show (fun z : ℂ => z ^ (-1 : ℤ)) = fun z => (z - 0)⁻¹ by funext z; simp]
    exact circleIntegral.integral_sub_inv_of_mem_ball (by simpa using hr)
  · simpa using circleIntegral.integral_sub_zpow_of_ne (w := 0) hm 0 r

/-- Binomial expansion of the circle integral of `w^(-(m+1)) * (x0+w)^k`. -/
theorem circleIntegral_negSucc_mul_add_pow (r x0 : ℝ) (hr : 0 < r) (m k : ℕ) :
    (∮ w in C(0, r), w ^ (-(m : ℤ) - 1) * ((x0 : ℂ) + w) ^ k) =
      if m ≤ k then (k.choose m : ℂ) * (x0 : ℂ) ^ (k - m) * (2 * Real.pi * I) else 0 := by
  have hexpand : ∀ w : ℂ, ((x0 : ℂ) + w) ^ k =
      ∑ j ∈ Finset.range (k + 1), (x0 : ℂ) ^ j * w ^ (k - j) * (k.choose j : ℂ) := by
    intro w; exact add_pow (x0 : ℂ) w k
  have hcongr : (∮ w in C(0, r), w ^ (-(m : ℤ) - 1) * ((x0 : ℂ) + w) ^ k) =
      ∮ w in C(0, r), ∑ j ∈ Finset.range (k + 1),
        (x0 : ℂ) ^ j * (k.choose j : ℂ) * w ^ (-(m : ℤ) - 1 + (k - j)) := by
    apply circleIntegral.integral_congr hr.le
    intro w hw
    rw [mem_sphere_zero_iff_norm] at hw
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw; linarith
    simp only
    rw [hexpand w, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hjk : j ≤ k := by omega
    have hcast : ((k - j : ℕ) : ℤ) = (k : ℤ) - (j : ℤ) := Nat.cast_sub hjk
    have hpow : w ^ (k - j) = w ^ ((k : ℤ) - (j : ℤ)) := by rw [← hcast, zpow_natCast]
    rw [hpow, show w ^ (-(m : ℤ) - 1) * ((x0 : ℂ) ^ j * w ^ ((k : ℤ) - (j : ℤ)) *
        (k.choose j : ℂ)) =
        (x0 : ℂ) ^ j * (k.choose j : ℂ) * (w ^ (-(m : ℤ) - 1) * w ^ ((k : ℤ) - (j : ℤ))) by ring,
      ← zpow_add₀ hw0]
  rw [hcongr, circleIntegral_finsetSum _ _ _ hr.le (fun j _ => by
    have h1 : ContinuousOn (fun w : ℂ => w ^ (-(m : ℤ) - 1 + ((k : ℤ) - (j : ℤ))))
        (sphere (0 : ℂ) r) :=
      (continuousOn_zpow₀ _).mono (fun w hw => by
        rw [mem_sphere_zero_iff_norm] at hw; rintro rfl; simp at hw; linarith)
    exact continuousOn_const.mul h1)]
  have hval : ∀ j : ℕ,
      (∮ w in C(0, r), (x0 : ℂ) ^ j * (k.choose j : ℂ) * w ^ (-(m : ℤ) - 1 + ((k : ℤ) - (j : ℤ)))) =
      if -(m : ℤ) - 1 + ((k : ℤ) - (j : ℤ)) = -1 then
        (x0 : ℂ) ^ j * (k.choose j : ℂ) * (2 * Real.pi * I)
      else 0 := by
    intro j
    rw [show (fun w : ℂ => (x0 : ℂ) ^ j * (k.choose j : ℂ) * w ^ (-(m : ℤ) - 1 + ((k : ℤ) -
        (j : ℤ)))) =
        fun w => ((x0 : ℂ) ^ j * (k.choose j : ℂ)) • w ^ (-(m : ℤ) - 1 + ((k : ℤ) - (j : ℤ))) by
      funext w; rw [smul_eq_mul]]
    rw [circleIntegral.integral_smul, circleIntegral_zpow_eq r hr]
    split_ifs with h <;> simp [smul_eq_mul]
  by_cases hmk : m ≤ k
  · simp only [hmk, ite_true]
    have hj0 : k - m ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
    refine Finset.sum_eq_single (k - m) (fun j hj hjne => ?_) (fun h => absurd hj0 h) |>.trans ?_
    · rw [hval j]
      simp only [show ¬ (-(m : ℤ) - 1 + ((k : ℤ) - (j : ℤ)) = -1) from (by
        intro heq
        apply hjne
        rw [Finset.mem_range] at hj
        omega), ite_false]
    · rw [hval (k - m)]
      simp only [show -(m : ℤ) - 1 + ((k : ℤ) - ((k - m : ℕ) : ℤ)) = -1 from (by
        have : ((k - m : ℕ) : ℤ) = (k : ℤ) - (m : ℤ) := Nat.cast_sub hmk
        omega), ite_true]
      have hsymm : k.choose (k - m) = k.choose m := Nat.choose_symm hmk
      rw [hsymm]
      ring
  · simp only [hmk, ite_false]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_range] at hj
    rw [hval j]
    simp only [show ¬ (-(m : ℤ) - 1 + ((k : ℤ) - (j : ℤ)) = -1) from (by omega), ite_false]

/-- The explicit, manifestly nonnegative value of the small-circle Laurent coefficient of a
translated nonnegative power series: it is the convergent Taylor-recentering series
`∑ₖ a_k C(k, n) x0^(k - n)`. -/
theorem circleLaurentCoeff_translate_eq (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (x0 r : ℝ)
    (hx0 : 0 ≤ x0) (hr : 0 < r) (hconv : Summable (fun k => a k * (x0 + r) ^ k)) (m : ℕ) :
    circleLaurentCoeff (fun w => ∑' k, (a k : ℂ) * ((x0 : ℂ) + w) ^ k) r (m : ℤ) =
      ((∑' k, if m ≤ k then a k * (k.choose m : ℝ) * x0 ^ (k - m) else 0 : ℝ) : ℂ) := by
  unfold circleLaurentCoeff
  have hint := circleIntegral_zpow_mul_tsum_add_eq a ha x0 r hx0 hr hconv (-(m : ℤ) - 1)
  rw [show (fun w : ℂ => w ^ (-(m : ℤ) - 1) • (∑' k, (a k : ℂ) * ((x0 : ℂ) + w) ^ k)) =
    (fun w : ℂ => w ^ (-(m : ℤ) - 1) * (∑' k, (a k : ℂ) * ((x0 : ℂ) + w) ^ k)) from rfl]
  rw [hint]
  have hval : ∀ k, (a k : ℂ) * ∮ w in C(0, r), w ^ (-(m : ℤ) - 1) * ((x0 : ℂ) + w) ^ k =
      ((if m ≤ k then a k * (k.choose m : ℝ) * x0 ^ (k - m) else 0 : ℝ) : ℂ) *
        (2 * Real.pi * I) := by
    intro k
    rw [circleIntegral_negSucc_mul_add_pow r x0 hr m k]
    split_ifs with h
    · push_cast; ring
    · simp
  rw [tsum_congr hval, tsum_mul_right, smul_eq_mul, mul_comm ((2 * (Real.pi : ℂ) * I)⁻¹),
    mul_assoc, mul_inv_cancel₀ (by simp [Real.pi_ne_zero] : (2 * (Real.pi : ℂ) * I) ≠ 0),
    mul_one, ← Complex.ofReal_tsum]

/-- Each translated coefficient of a nonnegative power series converges when the series
converges at a strictly larger positive argument. -/
private theorem summable_translated_coefficients (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    {x r : ℝ} (hx : 0 ≤ x) (hr : 0 < r) (hconv : Summable fun k => a k * (x + r) ^ k)
    (n : ℕ) : Summable fun k =>
      if n ≤ k then a k * (k.choose n : ℝ) * x ^ (k - n) else 0 := by
  refine Summable.of_nonneg_of_le (fun k => by
      split_ifs with h
      · exact mul_nonneg (mul_nonneg (ha k) (Nat.cast_nonneg _)) (pow_nonneg hx _)
      · exact le_refl 0)
    (f := fun k => a k * (x + r) ^ k * (r ^ n)⁻¹) (fun k => ?_) (hconv.mul_right _)
  split_ifs with h
  · have hbin : (k.choose n : ℝ) * x ^ (k - n) * r ^ n ≤ (x + r) ^ k := by
      have hexp := add_pow r x k
      have hmem : n ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
      calc (k.choose n : ℝ) * x ^ (k - n) * r ^ n
          = r ^ n * x ^ (k - n) * (k.choose n : ℝ) := by ring
        _ ≤ ∑ m ∈ Finset.range (k + 1), r ^ m * x ^ (k - m) * (k.choose m : ℝ) :=
            Finset.single_le_sum (f := fun m => r ^ m * x ^ (k - m) * (k.choose m : ℝ))
              (fun m _ => by positivity) hmem
        _ = (r + x) ^ k := hexp.symm
        _ = (x + r) ^ k := by ring
    have hrn : (0 : ℝ) < r ^ n := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ hrn]
    calc a k * (k.choose n : ℝ) * x ^ (k - n) * r ^ n
        = a k * ((k.choose n : ℝ) * x ^ (k - n) * r ^ n) := by ring
      _ ≤ a k * (x + r) ^ k := mul_le_mul_of_nonneg_left hbin (ha k)
  · exact mul_nonneg (mul_nonneg (ha k) (pow_nonneg (by positivity) k)) (by positivity)

/-- Summing a binomial row, extended by zero beyond its degree, evaluates the translated
monomial. -/
private theorem tsum_binomial_translate (c x t : ℝ) (k : ℕ) :
    (∑' n, t ^ n * (if n ≤ k then c * (k.choose n : ℝ) * x ^ (k - n) else 0)) =
      c * (x + t) ^ k := by
  calc
    _ = ∑ n ∈ Finset.range (k + 1),
        t ^ n * (if n ≤ k then c * (k.choose n : ℝ) * x ^ (k - n) else 0) :=
      tsum_eq_sum (fun n hn => by
        have hnk : ¬n ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
        simp only [ite_eq_right hnk, mul_zero])
    _ = c * (x + t) ^ k := by
      rw [add_comm x t, add_pow, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [ite_eq_left (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn)]
      ring

/-- A nonnegative double series with summable rows and summable row sums has summable
column sums. -/
private theorem summable_tsum_transpose {v : ℕ → ℕ → ℝ}
    (hv : ∀ n k, 0 ≤ v n k) (hrows : ∀ n, Summable (v n))
    (hsum : Summable fun n => ∑' k, v n k) : Summable fun k => ∑' n, v n k := by
  have hprod : Summable (Function.uncurry v) :=
    (summable_prod_of_nonneg (fun p => hv p.1 p.2)).mpr ⟨hrows, hsum⟩
  exact hprod.prod_symm.prod

/-- Summability of a nonnegative translated binomial series implies summability of the
original series at the sum of the two arguments. -/
private theorem summable_binomial_of_summable_translate (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t)
    (hrows : ∀ n, Summable fun k =>
      if n ≤ k then a k * (k.choose n : ℝ) * x ^ (k - n) else 0)
    (hsum : Summable fun n => t ^ n *
      ∑' k, if n ≤ k then a k * (k.choose n : ℝ) * x ^ (k - n) else 0) :
    Summable fun k => a k * (x + t) ^ k := by
  let b : ℕ → ℕ → ℝ := fun n k => t ^ n *
    (if n ≤ k then a k * (k.choose n : ℝ) * x ^ (k - n) else 0)
  have hb : ∀ n k, 0 ≤ b n k := by
    intro n k
    apply mul_nonneg (pow_nonneg ht _)
    split_ifs
    · exact mul_nonneg (mul_nonneg (ha _) (Nat.cast_nonneg _)) (pow_nonneg hx _)
    · exact le_rfl
  have hcol : Summable fun k => ∑' n, b n k := summable_tsum_transpose hb
    (fun n => (hrows n).mul_left (t ^ n)) (by simpa only [b, tsum_mul_left] using hsum)
  exact hcol.congr fun k => tsum_binomial_translate (a k) x t k

/-- **The Pringsheim–Vivanti theorem.** If the sum of a power series `∑ a_n z^n` with
nonnegative coefficients and radius of convergence `R` (`0 < R`) extends holomorphically to a
neighborhood `ball 0 R ∪ ball R ρ` of the boundary point `R`, then the series in fact converges
at some real point `z0 > R`. In particular, a power series with nonnegative coefficients and
finite radius of convergence `R` always has `R` itself as a singular point: it cannot be
continued holomorphically across any neighborhood of `R`. -/
theorem exists_gt_summable_of_forall_nonneg_of_differentiableOn_union_ball
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {R : ℝ} (hR : 0 < R)
    (hconv : ∀ r, 0 ≤ r → r < R → Summable (fun n => a n * r ^ n))
    {ρ : ℝ} (hρ : 0 < ρ) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 R ∪ ball (R : ℂ) ρ))
    (hFeq : ∀ z ∈ ball (0 : ℂ) R, F z = ∑' n, (a n : ℂ) * z ^ n) :
    ∃ z0 : ℝ, R < z0 ∧ Summable (fun n => a n * z0 ^ n) := by
  set δ : ℝ := min ρ R / 4 with hδ_def
  have hδpos : 0 < δ := by positivity
  have hδR : δ < R := by
    rw [hδ_def]; have := min_le_right ρ R; linarith
  have hδρ4 : δ ≤ ρ / 4 := by rw [hδ_def]; have := min_le_left ρ R; linarith
  set x0 : ℝ := R - δ with hx0_def
  have hx0pos : 0 < x0 := by rw [hx0_def]; linarith
  have hx0R : x0 < R := by rw [hx0_def]; linarith
  set s' : ℝ := ρ / 2 with hs'_def
  have hs'pos : 0 < s' := by positivity
  have hdist : dist (x0 : ℂ) (R : ℂ) = δ := by
    rw [Complex.dist_eq,
      show (x0 : ℂ) - (R : ℂ) = (-(δ : ℝ) : ℂ) by push_cast [hx0_def]; ring]
    simp [abs_of_pos hδpos]
  have hnear : closedBall (x0 : ℂ) s' ⊆ ball (R : ℂ) ρ :=
    closedBall_subset_ball' (by rw [hdist]; dsimp [s']; linarith)
  have hcontain : closedBall (x0 : ℂ) s' ⊆ ball (0 : ℂ) R ∪ ball (R : ℂ) ρ :=
    hnear.trans subset_union_right
  set G : ℂ → ℂ := fun w => F ((x0 : ℂ) + w) with hG_def
  have hFanBig : AnalyticOnNhd ℂ F (ball (0 : ℂ) R ∪ ball (R : ℂ) ρ) :=
    hF.analyticOnNhd (isOpen_ball.union isOpen_ball)
  have hFanS' : AnalyticOnNhd ℂ F (closedBall (x0 : ℂ) s') := hFanBig.mono hcontain
  have hGanS' : AnalyticOnNhd ℂ G (closedBall 0 s') := by
    intro w hw
    have hw' : (x0 : ℂ) + w ∈ closedBall (x0 : ℂ) s' := by
      rw [mem_closedBall, dist_eq_norm] at hw ⊢
      simpa using hw
    exact (hFanS' ((x0 : ℂ) + w) hw').comp (analyticAt_const.add analyticAt_id)
  set r : ℝ := δ / 2 with hr_def
  have hrpos : 0 < r := by positivity
  have hrδ : r < δ := by rw [hr_def]; linarith
  set z0 : ℝ := R + δ / 2 with hz0_def
  have hz0R : R < z0 := by rw [hz0_def]; linarith
  have hz0x0 : z0 - x0 = δ + δ / 2 := by rw [hz0_def, hx0_def]; ring
  have hrz0 : r < z0 - x0 := by rw [hr_def, hz0x0]; linarith
  have hz0s' : z0 - x0 < s' := by
    rw [hz0x0]
    have h1 : δ + δ / 2 = 3 * δ / 2 := by ring
    rw [h1]
    have h2 : 3 * δ / 2 ≤ 3 * ρ / 8 := by linarith [hδρ4]
    have h3 : (3 : ℝ) * ρ / 8 < ρ / 2 := by linarith
    calc 3 * δ / 2 ≤ 3 * ρ / 8 := h2
      _ < ρ / 2 := h3
      _ = s' := hs'_def.symm
  have hGeqOn : Set.EqOn G (fun w => ∑' k, (a k : ℂ) * ((x0 : ℂ) + w) ^ k) (sphere 0 r) := by
    intro w hw
    rw [mem_sphere_zero_iff_norm] at hw
    rw [hG_def]
    simp only
    rw [hFeq]
    rw [mem_ball_zero_iff]
    calc ‖(x0 : ℂ) + w‖ ≤ ‖(x0 : ℂ)‖ + ‖w‖ := norm_add_le _ _
      _ = x0 + r := by rw [Complex.norm_real, Real.norm_of_nonneg hx0pos.le, hw]
      _ < R := by rw [hx0_def]; linarith
  have hLC_eq : circleLaurentCoeff G r = circleLaurentCoeff (fun w => ∑' k, (a k : ℂ) *
      ((x0 : ℂ) + w) ^ k) r := by
    funext n
    unfold circleLaurentCoeff
    congr 1
    apply circleIntegral.integral_congr hrpos.le
    intro w hw
    simp only [hGeqOn hw]
  have hconvxr : Summable (fun k => a k * (x0 + r) ^ k) := hconv (x0 + r) (by positivity)
    (by rw [hx0_def, hr_def]; linarith)
  have hLC_nonneg : ∀ n : ℕ, circleLaurentCoeff G r (n : ℤ) =
      ((∑' k, if n ≤ k then a k * (k.choose n : ℝ) * x0 ^ (k - n) else 0 : ℝ) : ℂ) := by
    intro n
    rw [hLC_eq]
    exact circleLaurentCoeff_translate_eq a ha x0 r hx0pos.le hrpos hconvxr n
  have hHS : HasSum (fun k : ℤ => ((z0 - x0 : ℝ) : ℂ) ^ k • circleLaurentCoeff G r k) (F z0) := by
    have hann : AnalyticOnNhd ℂ G (closedBall 0 s' \ ball 0 r) := hGanS'.mono Set.sdiff_subset
    have := hasSum_circleLaurentCoeff_annulus hrpos
      (z := ((z0 - x0 : ℝ) : ℂ)) (r := r) (R := s') (by
        rw [Complex.norm_real, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ z0 - x0)]
        exact hrz0) (by
        rw [Complex.norm_real, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ z0 - x0)]
        exact hz0s') hann
    rw [show G (((z0 - x0 : ℝ) : ℂ)) = F z0 by
      rw [hG_def]; simp only
      rw [show (x0 : ℂ) + ((z0 - x0 : ℝ) : ℂ) = (z0 : ℂ) by push_cast; ring]] at this
    exact this
  have hsummableZ : Summable (fun k : ℤ => ((z0 - x0 : ℝ) : ℂ) ^ k • circleLaurentCoeff G r k) :=
    hHS.summable
  have hsummableN :
      Summable (fun n : ℕ => ((z0 - x0 : ℝ) : ℂ) ^ (n : ℤ) • circleLaurentCoeff G r (n : ℤ)) :=
    hsummableZ.comp_injective (fun a b hab => by exact_mod_cast hab)
  have hsummableN' : Summable (fun n : ℕ =>
      (z0 - x0) ^ n * (∑' k, if n ≤ k then a k * (k.choose n : ℝ) * x0 ^ (k - n) else 0)) := by
    have heq : (fun n : ℕ => ((z0 - x0 : ℝ) : ℂ) ^ (n : ℤ) • circleLaurentCoeff G r (n : ℤ)) =
        fun n : ℕ => (((z0 - x0) ^ n *
          (∑' k, if n ≤ k then a k * (k.choose n : ℝ) * x0 ^ (k - n) else 0) : ℝ) : ℂ) := by
      funext n
      rw [hLC_nonneg n, zpow_natCast, smul_eq_mul]
      push_cast
      ring
    rw [heq] at hsummableN
    have h2 := Complex.reCLM.summable hsummableN
    have heq2 : (fun n : ℕ => (Complex.reCLM (((z0 - x0) ^ n *
        (∑' k, if n ≤ k then a k * (k.choose n : ℝ) * x0 ^ (k - n) else 0) : ℝ) : ℂ))) =
        fun n : ℕ => (z0 - x0) ^ n *
          (∑' k, if n ≤ k then a k * (k.choose n : ℝ) * x0 ^ (k - n) else 0) := by
      funext n
      rw [Complex.reCLM_apply, Complex.ofReal_re]
    rwa [heq2] at h2
  refine ⟨z0, hz0R, ?_⟩
  have hs := summable_binomial_of_summable_translate a ha hx0pos.le
    (show 0 ≤ z0 - x0 by linarith)
    (summable_translated_coefficients a ha hx0pos.le hrpos hconvxr) hsummableN'
  simpa only [show x0 + (z0 - x0) = z0 by ring] using hs

end Complex

end
