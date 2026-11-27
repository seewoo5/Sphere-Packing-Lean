/-
Copyright (c) 2024 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import Mathlib.Analysis.Normed.Group.Tannery
import SpherePacking.ForMathlib.AtImInfty
import SpherePacking.ForMathlib.QSeriesBounds

/-!
# Limits at infinity

In this file we establishes basic results about q-expansions. The results are put under the `QExp`
namespace.

TODO:
* Are any of these results in Mathlib, perhaps phrased in some other way?
-/

@[expose] public section

open scoped Real
open UpperHalfPlane hiding I
open Complex Asymptotics Topology Filter

namespace QExp

lemma tendsto_nat (a : ℕ → ℂ) (ha : Summable fun n : ℕ ↦ ‖a n‖ * rexp (-2 * π * n)) :
    Tendsto (fun z : ℍ ↦ ∑' n, a n * cexp (2 * π * I * z * n)) atImInfty (𝓝 (a 0)) := by
  convert tendsto_tsum_of_dominated_convergence (f := fun z n ↦ a n * cexp (2 * π * I * z * n))
    (𝓕 := atImInfty) (g := Set.indicator {0} (fun _ ↦ a 0)) ha ?_ ?_
  · simp
  · intro k
    rcases eq_or_ne k 0 with (rfl | hk)
    · simp
    · simp only [Set.mem_singleton_iff, hk, not_false_eq_true, Set.indicator_of_notMem]
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simp_rw [norm_mul, mul_right_comm _ I, norm_exp_mul_I]
      rw [← mul_zero ‖a k‖]
      refine Tendsto.const_mul ‖a k‖ <| (Real.tendsto_exp_atBot).comp ?_
      simp only [mul_im, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero,
        coe_re, zero_mul, add_zero, coe_im, natCast_im, natCast_re, zero_add, tendsto_neg_atBot_iff]
      rw [tendsto_mul_const_atTop_of_pos, tendsto_const_mul_atTop_of_pos] <;> try positivity
      exact tendsto_im_atImInfty
  · rw [eventually_atImInfty]
    use 1
    intro z hz k
    simp_rw [norm_mul, mul_right_comm _ I, norm_exp_mul_I, mul_right_comm]
    simp only [mul_im, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero,
      sub_zero, coe_re, zero_mul, add_zero, coe_im, natCast_im, natCast_re, neg_mul]
    gcongr
    linarith [mul_le_mul_of_nonneg_left hz (by positivity : (0 : ℝ) ≤ 2 * π * k)]

/-- A `q`-series whose coefficients are summable against `e^{-2πm}` differs from its partial
sum of length `N` by `O(qᴺ)` at `i∞`. -/
lemma isBigO_tsum_sub_sum_range {a : ℕ → ℂ} (ha : Summable fun m : ℕ ↦ ‖a m‖ * rexp (-2 * π * m))
    (N : ℕ) :
      (fun z : ℍ ↦ ∑' m : ℕ, a m * cexp (2 * π * I * m * z) -
        ∑ m ∈ Finset.range N, a m * cexp (2 * π * I * m * z)) =O[atImInfty]
          fun z ↦ cexp (2 * π * I * z) ^ N := by
  refine .of_bound (∑' m : ℕ, ‖a (m + N)‖ * rexp (-(2 * π * 1) * m)) <|
    eventually_atImInfty.mpr ⟨1, fun z hz ↦ ?_⟩
  have hsum : Summable fun m : ℕ ↦ a m * cexp (2 * π * I * m * z) :=
    ha.of_norm_bounded fun m ↦ by
      rw [norm_mul, Complex.norm_exp]
      gcongr _ * rexp ?_
      simp [Complex.mul_re, Complex.mul_im]
      linarith [mul_le_mul_of_nonneg_left hz (by positivity : (0 : ℝ) ≤ 2 * π * m)]
  rw [← hsum.sum_add_tsum_nat_add N, add_sub_cancel_left, norm_pow, Complex.norm_exp,
    ← Real.exp_natCast_mul]
  refine (Complex.norm_qseries_shift_le N ?_ (by simpa using hz)).trans_eq
    (by congr 2; simp; ring)
  refine (((summable_nat_add_iff N).mpr ha).mul_left (rexp (2 * π * N))).congr fun m ↦ ?_
  rw [mul_left_comm, ← Real.exp_add]
  grind

end QExp
