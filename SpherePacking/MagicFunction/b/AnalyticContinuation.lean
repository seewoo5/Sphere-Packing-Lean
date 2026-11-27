/-
Copyright (c) 2026 mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib contributors:
-/
module

public import SpherePacking.MagicFunction.AnalyticContinuation
public import SpherePacking.MagicFunction.b.Schwartz
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Asymptotics
import SpherePacking.ModularForms.ResToImagAxis

/-!
# Double zeroes of `b`

For `s > 2`, `b(s) = -4i sin(π s / 2)² ∫₀^∞ ψ_I(it) e^{-π s t} dt`, where `s` is the squared
radius `‖x‖²`.
-/

@[expose] public section

open Set Filter MeasureTheory Real Complex MagicFunction.DoubleZeroes
open scoped Topology

namespace MagicFunction

private theorem ψS'_axis_isBigO :
    (fun t : ℝ ↦ ψS' (I * t)) =O[atTop] fun t ↦ rexp (-π * t) := by
  have hlim := tendsto_resToImagAxis_of_tendsto_atImInfty ψS_div_exp_tendsto
  obtain ⟨A, hA⟩ := Metric.tendsto_atTop.mp hlim 1 zero_lt_one
  refine Asymptotics.IsBigO.of_bound (10241 : ℝ) ?_
  filter_upwards [eventually_ge_atTop A, eventually_gt_atTop (0 : ℝ)] with t ht ht0
  have he : (π : ℂ) * I * (I * (t : ℂ)) = -π * (t : ℂ) := by
    linear_combination (π : ℂ) * (t : ℂ) * I_sq
  have h := hA t ht
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht0, ↓reduceDIte, he,
    ← ψS'_def (show 0 < (I * (t : ℂ)).im by simpa using ht0)] at h
  have hnorm :
      ‖ψS' (I * (t : ℂ)) / cexp (-(π : ℂ) * t)‖ ≤ 10241 := by
    rw [dist_eq_norm] at h
    calc
      _ = ‖ψS' (I * (t : ℂ)) / cexp (-(π : ℂ) * t) - (-10240) + (-10240)‖ := by
        rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := by
        have hn : ‖(-10240 : ℂ)‖ = (10240 : ℝ) := by norm_num
        rw [hn]
        linarith
  rw [norm_div, Complex.norm_exp, Complex.mul_re] at hnorm
  simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
    (div_le_iff₀ (Real.exp_pos _)).mp hnorm

/-- `ψ_I(it) = O(t² e^{-π/t})` as `t → 0`. -/
theorem ψI'_I_mul_isBigO_nhdsGT_zero :
    (fun t : ℝ ↦ ψI' (I * t)) =O[𝓝[>] 0] fun t ↦ t ^ 2 * rexp (-π / t) := by
  have h := (ψS'_axis_isBigO.comp_tendsto tendsto_inv_nhdsGT_zero).mul
    (Asymptotics.isBigO_of_le (𝓝[>] (0 : ℝ))
      (f := fun t : ℝ ↦ (I * (t : ℂ)) ^ 2) (g := fun t : ℝ ↦ t ^ 2)
      (fun t ↦ by simp [norm_pow]))
  refine h.congr' ?_ (Eventually.of_forall ?_)
  · filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with t ht
    have ht0 : 0 < t := ht
    rw [ψS_slash_S_explicit (show 0 < (I * (t : ℂ)).im by simpa using ht0)]
    change ψS' (I * (↑(t⁻¹) : ℂ)) * _ = ψS' (-1 / (I * (t : ℂ))) * _
    rw [Complex.ofReal_inv]
    have he : I * (t : ℂ)⁻¹ = -1 / (I * (t : ℂ)) := by
      field_simp [Complex.I_ne_zero, show (t : ℂ) ≠ 0 by exact_mod_cast ht0.ne']
      linear_combination I_sq
    rw [he]
  · intro t
    simp only [Function.comp_apply, div_eq_mul_inv, mul_comm]

/-- `ψ_I(it) = O(e^{2πt})` as `t → ∞`. -/
theorem ψI'_I_mul_isBigO_atTop :
    (fun t : ℝ ↦ ψI' (I * t)) =O[atTop] fun t ↦ rexp (2 * π * t) := by
  have hlim := tendsto_resToImagAxis_of_tendsto_atImInfty ψI_mul_exp_tendsto
  obtain ⟨A, hA⟩ := Metric.tendsto_atTop.mp hlim 1 zero_lt_one
  refine Asymptotics.IsBigO.of_bound (2 : ℝ) ?_
  filter_upwards [eventually_ge_atTop A, eventually_gt_atTop (0 : ℝ)] with t ht ht0
  have he : 2 * (π : ℂ) * I * (I * (t : ℂ)) = -(2 * π * (t : ℂ)) := by
    linear_combination 2 * (π : ℂ) * (t : ℂ) * I_sq
  have h := hA t ht
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht0, ↓reduceDIte, he,
    ← ψI'_def (show 0 < (I * (t : ℂ)).im by simpa using ht0), dist_eq_norm] at h
  have hnorm : ‖ψI' (I * (t : ℂ)) * cexp (-(2 * π * (t : ℂ)))‖ ≤ 2 := by
    calc
      _ = ‖ψI' (I * (t : ℂ)) * cexp (-(2 * π * (t : ℂ))) - 1 + 1‖ := by
        rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := by rw [norm_one]; linarith
  rw [norm_mul, Complex.norm_exp] at hnorm
  have he' : (-(2 * (π : ℂ) * (t : ℂ))).re = -(2 * π * t) := by simp
  rw [he', Real.exp_neg, ← div_eq_mul_inv] at hnorm
  simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
    (div_le_iff₀ (Real.exp_pos _)).mp hnorm

theorem ψI'_imaginaryAxis_continuousOn :
    ContinuousOn (fun t : ℝ ↦ ψI' (I * t)) (Ici 0) := by
  intro t ht
  rcases eq_or_lt_of_le (mem_Ici.mp ht) with rfl | ht'
  · have hExp : Tendsto (fun t : ℝ ↦ rexp (-π / t)) (𝓝[>] 0) (𝓝 0) := by
      simpa only [Function.comp_def, id, div_eq_mul_inv] using
        (Real.tendsto_exp_atBot.comp
          (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr Real.pi_pos))).comp
            tendsto_inv_nhdsGT_zero
    have hSq : Tendsto (fun t : ℝ ↦ t ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have hi : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using hi.pow 2
    have hRight := ψI'_I_mul_isBigO_nhdsGT_zero.trans_tendsto
      (by simpa only [zero_mul] using hSq.mul hExp)
    have hzero : ψI' (I * ((0 : ℝ) : ℂ)) = 0 := by simp [ψI']
    change Tendsto _ (𝓝[Ici 0] 0) (𝓝 (ψI' (I * ((0 : ℝ) : ℂ))))
    rw [hzero, ← insert_Ioi, nhdsWithin_insert]
    refine tendsto_sup.2 ⟨?_, hRight⟩
    simpa only [hzero] using tendsto_pure_nhds (fun t : ℝ ↦ ψI' (I * t)) 0
  · have hψ : (fun t : ℝ ↦ ψI' (I * t)) = ψI.resToImagAxis := by
      ext t
      by_cases ht : 0 < t <;> simp [ψI', ResToImagAxis, ht]
    rw [hψ]
    exact (ResToImagAxis.Differentiable ψI ψI_mdifferentiable t ht').continuousAt.continuousWithinAt

theorem integrableOn_ψI'_mul_cexp {s : ℝ} (hr : 2 < s) :
    IntegrableOn (fun t : ℝ ↦ ψI' (I * t) * cexp (-π * s * t)) (Ioi 0) := by
  let f : ℝ → ℂ := fun t ↦ ψI' (I * t) * cexp (-π * s * t)
  have hcont : ContinuousOn f (Ici 0) :=
    ψI'_imaginaryAxis_continuousOn.mul (by fun_prop)
  have hdecay : -(π * (s - 2)) < 0 :=
    neg_lt_zero.mpr (mul_pos Real.pi_pos (sub_pos.mpr hr))
  have hO : f =O[atTop] fun t ↦ rexp (-(π * (s - 2)) * t) := by
    have hkernel : (fun t : ℝ ↦ cexp (-π * s * t)) =O[atTop]
        fun t ↦ rexp (-π * s * t) := by
      apply Asymptotics.isBigO_of_le
      intro t
      simp [Complex.norm_exp, Complex.mul_re]
    refine (ψI'_I_mul_isBigO_atTop.mul hkernel).congr_right fun t ↦ ?_
    rw [← Real.exp_add]
    congr 1
    ring
  exact ((hcont.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop hO
    ⟨Ioi 0, Ioi_mem_atTop 0, integrableOn_exp_mul_Ioi hdecay 0⟩).mono_set Ioi_subset_Ici_self

open b.RealIntegrals in
/-- Combined unbounded contour deformation from Proposition 7.40. The six finite and
infinite pieces defining the contour sum equal the three vertical ray contributions.
The two translated rays contribute phases `exp (π i s)` and `exp (-π i s)`, and the
central ray has coefficient `-2`. -/
theorem b_unbounded_contour_deformation {s : ℝ} (hs : 2 < s) :
    J₁' s + J₂' s + J₃' s + J₄' s + J₅' s + J₆' s =
      I * (∫ t in Ioi (0 : ℝ),
        ψT' (-1 + I * t) * cexp (π * I * s * (-1 + I * t))) -
      2 * I * (∫ t in Ioi (0 : ℝ), ψI' (I * t) * cexp (-π * s * t)) +
      I * (∫ t in Ioi (0 : ℝ),
        ψT' (1 + I * t) * cexp (π * I * s * (1 + I * t))) := by
  sorry

private theorem integral_ψT'_shift {s : ℝ} {a : ℂ} (ha : a = -1 ∨ a = 1) :
    (∫ t in Ioi (0 : ℝ), ψT' (a + I * t) * cexp (π * I * s * (a + I * t))) =
      cexp (π * I * s * a) * ∫ t in Ioi (0 : ℝ), ψI' (I * t) * cexp (-π * s * t) := by
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht' : 0 < t := ht
  have hi : (I * (t : ℂ)).im = t := by simp
  have him : 0 < (a + I * (t : ℂ)).im := by
    rcases ha with rfl | rfl <;> simpa [hi] using ht'
  have hψ : ψT' (a + I * t) = ψI' (I * t) := by
    rcases ha with rfl | rfl
    · rw [← ψI'_add_one him]
      congr 1
      ring
    · rw [← ψI'_sub_one him]
      congr 1
      ring
  have he : (π : ℂ) * I * s * (a + I * t) = π * I * s * a + -π * s * t := by
    linear_combination (π : ℂ) * (s : ℂ) * (t : ℂ) * I_sq
  dsimp only
  rw [hψ, he, Complex.exp_add]
  ring

private theorem exp_phase_sum (x : ℂ) :
    cexp (x * I) - 2 + cexp (-(x * I)) = -4 * Complex.sin (x / 2) ^ 2 := by
  have hcos : Complex.cos (2 * (x / 2)) = Complex.cos x := by
    congr 1
    ring
  rw [Complex.cos_two_mul] at hcos
  have he : Complex.cos x = (cexp (x * I) + cexp (-(x * I))) / 2 := by
    rw [Complex.cos, neg_mul]
  rw [he] at hcos
  linear_combination -2 * hcos + 4 * Complex.sin_sq_add_cos_sq (x / 2)

theorem b'_eq_neg_four_mul_I_mul_sin_sq_mul_integral {s : ℝ} (hr : 2 < s) :
    b.RealIntegrals.b' s = -4 * I * (Real.sin (π * s / 2) : ℂ) ^ 2 *
      ∫ t in Ioi (0 : ℝ), ψI' (I * t) * cexp (-π * s * t) := by
  rw [b.RealIntegrals.b', b_unbounded_contour_deformation hr,
    integral_ψT'_shift (Or.inl rfl), integral_ψT'_shift (Or.inr rfl)]
  rw [show (π : ℂ) * I * s * (-1) = -(π * s * I) by ring,
    show (π : ℂ) * I * s * 1 = π * s * I by ring]
  have hphase := exp_phase_sum ((π : ℂ) * s)
  have hsin : Complex.sin ((π : ℂ) * s / 2) = (Real.sin (π * s / 2) : ℂ) := by
    push_cast
    rfl
  rw [hsin] at hphase
  linear_combination
    (I * ∫ t in Ioi (0 : ℝ), ψI' (I * t) * cexp (-π * s * t)) * hphase

theorem b_eq_neg_four_mul_I_mul_sin_sq_mul_integral {x : EuclideanSpace ℝ (Fin 8)} (hx : √2 < ‖x‖) :
    FourierEigenfunctions.b x = -4 * I * (Real.sin (π * ‖x‖ ^ 2 / 2) : ℂ) ^ 2 *
      ∫ t in Ioi (0 : ℝ), ψI' (I * t) * cexp (-π * ‖x‖ ^ 2 * t) := by
  change b.RealIntegrals.b' (‖x‖ ^ 2) = _
  rw [b'_eq_neg_four_mul_I_mul_sin_sq_mul_integral (lt_sq_of_sqrt_lt hx)]
  norm_num

/-- Bound a theta-series tail after removing the terms in a finite set. -/
private theorem theta_tail_bound (a : ℤ → ℝ) (c : ℤ → ℂ) (S : Finset ℤ)
    (m : ℝ) (ha0 : ∀ n, 0 ≤ a n) (hc : ∀ n, ‖c n‖ = 1) (ha : ∀ n ∉ S, m ≤ a n)
    (hs : Summable (fun n ↦ rexp (-π * a n))) :
    (fun t : ℝ ↦ (∑' n : ℤ, c n * (rexp (-π * a n * t) : ℂ)) -
      ∑ n ∈ S, c n * (rexp (-π * a n * t) : ℂ)) =O[atTop]
      fun t ↦ rexp (-π * m * t) := by
  classical
  refine Asymptotics.IsBigO.of_bound (rexp (π * m) * ∑' n : ℤ, rexp (-π * a n)) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have hsum : Summable (fun n : ℤ ↦ c n * (rexp (-π * a n * t) : ℂ)) := by
    apply Summable.of_norm
    simp_rw [norm_mul, hc, one_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    apply hs.of_nonneg_of_le (fun n ↦ Real.exp_nonneg _)
    intro n
    exact Real.exp_le_exp.mpr
      (by nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (ha0 n)) (sub_nonneg.mpr ht)])
  rw [← hsum.sum_add_tsum_subtype_compl S, add_sub_cancel_left]
  calc
    _ ≤ ∑' n : {n // n ∉ S}, ‖c n * (rexp (-π * a n * t) : ℂ)‖ :=
      norm_tsum_le_tsum_norm (hsum.subtype (fun n ↦ n ∉ S)).norm
    _ ≤ ∑' n : {n // n ∉ S}, rexp (-π * a n) * (rexp (π * m) * rexp (-π * m * t)) := by
      apply Summable.tsum_le_tsum
      · intro n
        simp only [norm_mul, hc, one_mul, Complex.norm_real,
          Real.norm_of_nonneg (Real.exp_pos _).le]
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hn := ha n n.property
        nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hn))
          (sub_nonneg.mpr ht)]
      · exact (hsum.subtype (fun n ↦ n ∉ S)).norm
      · exact (hs.subtype (fun n ↦ n ∉ S)).mul_right _
    _ ≤ _ := by
      rw [tsum_mul_right, Real.norm_of_nonneg (Real.exp_pos _).le, ← mul_assoc,
        mul_comm (∑' n : {n // n ∉ S}, rexp (-π * a n))]
      gcongr
      exact hs.tsum_subtype_le _ {n | n ∉ S} (fun _ ↦ Real.exp_nonneg _)

private theorem theta_axis_tails :
    ((fun t : ℝ ↦ (∑' n : ℤ, (rexp (-π * ((n : ℝ)^2 + n) * t) : ℂ)) -
      (2 + 2 * (rexp (-π * 2 * t) : ℂ))) =O[atTop] fun t ↦ rexp (-π * 3 * t)) ∧
    ((fun t : ℝ ↦ (∑' n : ℤ, (rexp (-π * (n : ℝ)^2 * t) : ℂ)) -
      (1 + 2 * (rexp (-π * t) : ℂ))) =O[atTop] fun t ↦ rexp (-π * 3 * t)) ∧
    ((fun t : ℝ ↦ (∑' n : ℤ, (-1 : ℂ)^n * (rexp (-π * (n : ℝ)^2 * t) : ℂ)) -
      (1 - 2 * (rexp (-π * t) : ℂ))) =O[atTop] fun t ↦ rexp (-π * 3 * t)) := by
  classical
  have hsum (v : ℂ) :
      Summable (jacobiTheta₂_term · v I) :=
    (summable_jacobiTheta₂_term_iff _ _).2 (by simp)
  have norm_term (n : ℤ) (u : ℝ) :
      ‖jacobiTheta₂_term n ((u : ℂ) * I) I‖ =
        rexp (-π * ((n : ℝ)^2 + 2 * u * n)) := by
    rw [jacobiTheta₂_term, Complex.norm_exp]
    simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re]
    ring
  have hs₃ : Summable (fun n : ℤ ↦ rexp (-π * (n : ℝ)^2)) := by
    have h := (hsum ((↑(0 : ℝ) : ℂ) * I)).norm
    simp_rw [norm_term] at h
    simpa using h
  have hs₂ : Summable (fun n : ℤ ↦ rexp (-π * ((n : ℝ)^2 + n))) := by
    have he (n : ℤ) : 2 * (1 / 2 : ℝ) * n = (n : ℝ) := by ring
    simpa only [norm_term, he] using (hsum ((↑(1 / 2 : ℝ) : ℂ) * I)).norm
  have hskip (n : ℤ) (hn : n ∉ ({-1, 0, 1} : Finset ℤ)) : (3 : ℝ) ≤ (n : ℝ)^2 := by
    simp at hn
    have h : n ≤ -2 ∨ 2 ≤ n := by omega
    rcases h with h | h <;> have hr : (n : ℝ) ≤ -2 ∨ 2 ≤ (n : ℝ) := by
      first | exact Or.inl (by exact_mod_cast h) | exact Or.inr (by exact_mod_cast h)
    all_goals rcases hr with hr | hr <;> nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have h0 (n : ℤ) : 0 ≤ (n : ℝ)^2 + n := by
      have hn : n ≤ -1 ∨ 0 ≤ n := by omega
      rcases hn with hn | hn
      · have h : (n : ℝ) ≤ -1 := by exact_mod_cast hn
        nlinarith [mul_nonneg (show 0 ≤ -(n : ℝ) by linarith)
          (show 0 ≤ -(n : ℝ) - 1 by linarith)]
      · have h : 0 ≤ (n : ℝ) := by exact_mod_cast hn
        positivity
    have hskip₂ (n : ℤ) (hn : n ∉ ({-2, -1, 0, 1} : Finset ℤ)) :
        (3 : ℝ) ≤ (n : ℝ)^2 + n := by
      simp at hn
      have h : n ≤ -3 ∨ 2 ≤ n := by omega
      rcases h with h | h
      · have h' : (n : ℝ) ≤ -3 := by exact_mod_cast h
        nlinarith [sq_nonneg ((n : ℝ) + 3)]
      · have h' : (2 : ℝ) ≤ n := by exact_mod_cast h
        nlinarith [sq_nonneg ((n : ℝ) - 2)]
    refine (theta_tail_bound _ (fun _ ↦ 1) {-2, -1, 0, 1} 3 h0 (by simp) hskip₂ hs₂).congr_left ?_
    intro t
    norm_num [Finset.sum_insert, Finset.sum_singleton]
    ring
  · refine (theta_tail_bound _ (fun _ ↦ 1) {-1, 0, 1} 3 (fun n ↦ sq_nonneg (n : ℝ))
      (by simp) hskip hs₃).congr_left ?_
    intro t
    norm_num [Finset.sum_insert, Finset.sum_singleton]
    ring
  · refine (theta_tail_bound _ (fun n ↦ (-1 : ℂ)^n) {-1, 0, 1} 3 (fun n ↦ sq_nonneg (n : ℝ))
      (by simp) hskip hs₃).congr_left ?_
    intro t
    norm_num [Finset.sum_insert, Finset.sum_singleton]
    ring

private theorem theta_axis_expansions :
    ((fun t : ℝ ↦ Function.resToImagAxis
      (fun z ↦ jacobiTheta₂ ((z : ℂ) / 2) z) t -
      (2 + 2 * (rexp (-π * 2 * t) : ℂ))) =O[atTop] fun t ↦ rexp (-π * 3 * t)) ∧
    ((fun t : ℝ ↦ Θ₃.resToImagAxis t -
      (1 + 2 * (rexp (-π * t) : ℂ))) =O[atTop] fun t ↦ rexp (-π * 3 * t)) ∧
    ((fun t : ℝ ↦ Θ₄.resToImagAxis t -
      (1 - 2 * (rexp (-π * t) : ℂ))) =O[atTop] fun t ↦ rexp (-π * 3 * t)) := by
  obtain ⟨h₂, h₃, h₄⟩ := theta_axis_tails
  have hexp (a t : ℝ) : cexp (π * I * (a : ℂ) * (I * (t : ℂ))) =
      (rexp (-π * a * t) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    linear_combination (π : ℂ) * (a : ℂ) * (t : ℂ) * I_sq
  refine ⟨h₂.congr' ?_ Filter.EventuallyEq.rfl, h₃.congr' ?_ Filter.EventuallyEq.rfl,
    h₄.congr' ?_ Filter.EventuallyEq.rfl⟩
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte, jacobiTheta₂]
    congr 1
    apply tsum_congr
    intro n
    rw [jacobiTheta₂_term]
    rw [← hexp ((n : ℝ)^2 + n) t]
    congr 1
    push_cast
    ring
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte, Θ₃, Θ₃_term]
    congr 1
    apply tsum_congr
    intro n
    have he := hexp ((n : ℝ)^2) t
    push_cast at he ⊢
    exact he.symm
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte, Θ₄, Θ₄_term]
    congr 1
    apply tsum_congr
    intro n
    have he := hexp ((n : ℝ)^2) t
    push_cast at he
    push_cast
    rw [he]

private theorem pow_sub_pow_isBigO {f g : ℝ → ℂ} {w : ℝ → ℝ}
    (hf : f =O[atTop] fun _ ↦ (1 : ℝ)) (hg : g =O[atTop] fun _ ↦ (1 : ℝ))
    (hfg : (fun t ↦ f t - g t) =O[atTop] w) (n : ℕ) :
    (fun t ↦ f t ^ n - g t ^ n) =O[atTop] w := by
  induction n with
  | zero => simpa using (Asymptotics.isBigO_zero (E' := ℂ) w atTop)
  | succ n ih =>
    have h₁ : (fun t ↦ f t ^ n * (f t - g t)) =O[atTop] w := by
      simpa only [one_pow, one_mul] using (hf.pow n).mul hfg
    have h₂' : (fun t ↦ (f t ^ n - g t ^ n) * g t) =O[atTop] w := by
      simpa only [mul_one] using ih.mul hg
    exact (h₁.add h₂').congr_left fun t ↦ by
      ring

/-- `ψ_I(it) = e^{2πt} + 144 + O(e^{-πt})` as `t → ∞`. -/
theorem ψI'_I_mul_sub_isBigO_atTop :
    (fun t : ℝ ↦ ψI' (I * t) - (cexp (2 * π * t) + 144)) =O[atTop] fun t ↦ rexp (-π * t) := by
  let q : ℝ → ℂ := fun t ↦ (rexp (-π * t) : ℂ)
  let w : ℝ → ℝ := fun t ↦ rexp (-π * 3 * t)
  let X : ℝ → ℂ := (fun z : UpperHalfPlane ↦ jacobiTheta₂ ((z : ℂ) / 2) z).resToImagAxis
  let Y : ℝ → ℂ := Θ₃.resToImagAxis
  let Z : ℝ → ℂ := Θ₄.resToImagAxis
  let X₀ : ℝ → ℂ := fun t ↦ 2 + 2 * q t ^ 2
  let Y₀ : ℝ → ℂ := fun t ↦ 1 + 2 * q t
  let Z₀ : ℝ → ℂ := fun t ↦ 1 - 2 * q t
  have hq : Tendsto q atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr Real.pi_pos))
    simpa [q, Function.comp_def] using (Complex.continuous_ofReal.continuousAt.tendsto.comp h)
  have hqpow (n : ℕ) (t : ℝ) : q t ^ n = (rexp (-π * n * t) : ℂ) := by
    dsimp [q]
    rw [Complex.ofReal_exp, ← Complex.exp_natCast_mul, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  obtain ⟨hx, hy, hz⟩ := theta_axis_expansions
  have hx : (fun t ↦ X t - X₀ t) =O[atTop] w := by
    simpa only [X, X₀, w, hqpow 2, Nat.cast_ofNat] using hx
  have hy : (fun t ↦ Y t - Y₀ t) =O[atTop] w := hy
  have hz : (fun t ↦ Z t - Z₀ t) =O[atTop] w := hz
  have hw : Tendsto w atTop (𝓝 0) := by
    exact Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (show -π * 3 < 0 by linarith [Real.pi_pos]))
  have hx₀ : Tendsto X₀ atTop (𝓝 2) := by
    simpa using tendsto_const_nhds.add ((hq.pow 2).const_mul (2 : ℂ))
  have hy₀ : Tendsto Y₀ atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (hq.const_mul (2 : ℂ))
  have hz₀ : Tendsto Z₀ atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hq.const_mul (2 : ℂ))
  have hX : Tendsto X atTop (𝓝 2) := by
    simpa [sub_add_cancel] using (hx.trans_tendsto hw).add hx₀
  have hY : Tendsto Y atTop (𝓝 1) := by
    simpa [sub_add_cancel] using (hy.trans_tendsto hw).add hy₀
  have hZ : Tendsto Z atTop (𝓝 1) := by
    simpa [sub_add_cancel] using (hz.trans_tendsto hw).add hz₀
  have bounded {f : ℝ → ℂ} {a : ℂ} (hf : Tendsto f atTop (𝓝 a)) :
      f =O[atTop] fun _ ↦ (1 : ℝ) :=
    Asymptotics.isBigO_const_of_tendsto hf one_ne_zero
  have hx8 := pow_sub_pow_isBigO (bounded hX) (bounded hx₀) hx 8
  have hy4 := pow_sub_pow_isBigO (bounded hY) (bounded hy₀) hy 4
  have hz4 := pow_sub_pow_isBigO (bounded hZ) (bounded hz₀) hz 4
  have hq3 : (fun t ↦ q t ^ 3) =O[atTop] w := by
    apply Asymptotics.isBigO_of_le
    intro t
    rw [hqpow, Complex.norm_real]
    rfl
  -- The first quotient has polar term q⁻² and constant term 16.
  let P : ℂ → ℂ := fun z ↦ (1 + 16 * z ^ 2)
  have hP : Tendsto (P ∘ q) atTop (𝓝 1) := by
    simpa [P, Function.comp_def] using tendsto_const_nhds.add ((hq.pow 2).const_mul (16 : ℂ))
  have hfirst_err : (fun t ↦
      (128 : ℂ) * (Y t ^ 4 + Z t ^ 4) - P (q t) * X t ^ 8 -
      (128 * (Y₀ t ^ 4 + Z₀ t ^ 4) - P (q t) * X₀ t ^ 8)) =O[atTop] w := by
    have h₁ := (hy4.add hz4).const_mul_left (128 : ℂ)
    have h₂ : (fun t ↦ P (q t) * (X t ^ 8 - X₀ t ^ 8)) =O[atTop] w := by
      simpa only [one_mul, Function.comp_apply] using (bounded hP).mul hx8
    exact (h₁.sub h₂).congr_left (fun t ↦ by ring)
  have hmodel : (fun t ↦
      (128 : ℂ) * (Y₀ t ^ 4 + Z₀ t ^ 4) - P (q t) * X₀ t ^ 8) =O[atTop] w := by
    -- Expand (1 + z²)^4 first, then square it to isolate the terms of degree ≥ 4.
    let R : ℂ → ℂ := fun z ↦
      let a := 6 + 4 * z ^ 2 + z ^ 4
      (-256) * z * (112 + (1 + 16 * z ^ 2) * (2 * a + (4 + z ^ 2 * a) ^ 2))
    have hR : Tendsto (R ∘ q) atTop (𝓝 0) := by
      have hcont : Continuous R := by dsimp [R]; fun_prop
      simpa [R] using (hcont.continuousAt (x := (0 : ℂ))).tendsto.comp hq
    have h := hq3.mul (bounded hR)
    have h' : (fun t ↦ q t ^ 3 * R (q t)) =O[atTop] w := by
      simpa only [mul_one, Function.comp_apply] using h
    exact h'.congr_left (fun t ↦ by dsimp [R, X₀, Y₀, Z₀, P]; ring)
  have hn₁ : (fun t ↦
      (128 : ℂ) * (Y t ^ 4 + Z t ^ 4) - P (q t) * X t ^ 8) =O[atTop] w :=
    (hfirst_err.add hmodel).congr_left fun t ↦ sub_add_cancel _ _
  have hiX : Tendsto (fun t ↦ (X t ^ 8)⁻¹) atTop (𝓝 ((2 : ℂ) ^ 8)⁻¹) :=
    (hX.pow 8).inv₀ (by norm_num)
  have hiY : Tendsto (fun t ↦ (Y t ^ 8)⁻¹) atTop (𝓝 ((1 : ℂ) ^ 8)⁻¹) :=
    (hY.pow 8).inv₀ (by norm_num)
  have hf₁ : (fun t ↦
      ((128 : ℂ) * (Y t ^ 4 + Z t ^ 4) - P (q t) * X t ^ 8) / X t ^ 8) =O[atTop] w := by
    simpa only [mul_one, div_eq_mul_inv] using hn₁.mul (bounded hiX)
  let v : ℝ → ℝ := fun t ↦ rexp (-π * t)
  have hwv : w =O[atTop] v := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simp only [w, v, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg Real.pi_pos.le ht])
  have hqv : q =O[atTop] v := by
    apply Asymptotics.isBigO_of_le
    intro t
    change ‖(rexp (-π * t) : ℂ)‖ ≤ ‖rexp (-π * t)‖
    exact (Complex.norm_real _).le
  have hY₁ : (fun t ↦ Y t - 1) =O[atTop] v :=
    ((hy.trans hwv).add (hqv.const_mul_left (2 : ℂ))).congr_left
      fun t ↦ by dsimp [Y₀]; ring
  have hZ₁ : (fun t ↦ Z t - 1) =O[atTop] v :=
    ((hz.trans hwv).sub (hqv.const_mul_left (2 : ℂ))).congr_left
      fun t ↦ by dsimp [Z₀]; ring
  have hOne : (fun _ : ℝ ↦ (1 : ℂ)) =O[atTop] fun _ ↦ (1 : ℝ) :=
    bounded tendsto_const_nhds
  -- The second quotient contributes the remaining constant 128.
  have hf₂ : (fun t ↦
      128 * (Z t ^ 4 - q t * X t ^ 4 - Y t ^ 8) / Y t ^ 8) =O[atTop] v := by
    have hY8 := pow_sub_pow_isBigO (bounded hY) hOne hY₁ 8
    have hZ4 := pow_sub_pow_isBigO (bounded hZ) hOne hZ₁ 4
    have hqX : (fun t ↦ q t * X t ^ 4) =O[atTop] v := by
      simpa only [mul_one] using hqv.mul (bounded (hX.pow 4))
    have h := (((hZ4.sub hY8).sub hqX).const_mul_left (128 : ℂ)).mul (bounded hiY)
    have h' : (fun t ↦
        128 * ((Z t ^ 4 - 1 ^ 4) - (Y t ^ 8 - 1 ^ 8) - q t * X t ^ 4) *
          (Y t ^ 8)⁻¹) =O[atTop] v := by
      simpa only [mul_one] using h
    exact h'.congr_left (fun t ↦ by rw [div_eq_mul_inv]; ring)
  have hqp (t : ℝ) : q t ≠ 0 := by
    change (rexp (-π * t) : ℂ) ≠ 0
    exact_mod_cast (Real.exp_ne_zero (-π * t))
  have hf₁' : (fun t ↦
      (((128 : ℂ) * (Y t ^ 4 + Z t ^ 4) - P (q t) * X t ^ 8) / X t ^ 8) /
        q t ^ 2) =O[atTop] v := by
    obtain ⟨C, hC⟩ := hf₁.isBigOWith
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [hC.bound] with t ht
    rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr (pow_ne_zero 2 (hqp t)))]
    rw [hqpow, Complex.norm_real]
    have he : ‖v t‖ * ‖rexp (-π * ↑(2 : ℕ) * t)‖ = ‖w t‖ := by
      simp only [v, w, Nat.cast_ofNat, Real.norm_of_nonneg (Real.exp_nonneg _)]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_assoc]
    convert ht using 2
  refine (hf₁'.add hf₂).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ), hX.eventually_ne (by norm_num : (2 : ℂ) ≠ 0),
    hY.eventually_ne (by norm_num : (1 : ℂ) ≠ 0)] with t ht hXt hYt
  let z : UpperHalfPlane := ⟨I * (t : ℂ), by simpa using ht⟩
  have h₂ : H₂ z = q t * X t ^ 4 := by
    rw [H₂, Θ₂_as_jacobiTheta₂, mul_pow, ← Complex.exp_natCast_mul]
    have he : (4 : ℂ) * (π * I * (z : ℂ) / 4) = -π * (t : ℂ) := by
      change (4 : ℂ) * (π * I * (I * (t : ℂ)) / 4) = _
      linear_combination (π : ℂ) * (t : ℂ) * I_sq
    norm_num only [Nat.cast_ofNat]
    rw [he]
    simp [X, q, ResToImagAxis, ht, z, Complex.ofReal_exp]
  have h₃ : H₃ z = Y t ^ 4 := by simp [Y, ResToImagAxis, ht, z, H₃]
  have h₄ : H₄ z = Z t ^ 4 := by simp [Z, ResToImagAxis, ht, z, H₄]
  have hpolar : cexp (2 * π * (t : ℂ)) = (q t ^ 2)⁻¹ := by
    rw [hqpow, Complex.ofReal_exp, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  change _ = ψI' (I * (t : ℂ)) - _
  rw [ψI'_def z.coe_im_pos, congrFun ψI_eq z]
  simp only [Pi.smul_apply, nsmul_eq_mul, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply]
  rw [h₂, h₃, h₄, hpolar]
  dsimp only [P]
  field_simp [hqp t, hXt, hYt]
  ring

theorem expPoly_ψI' (t : ℝ) :
    expPoly 1 (fun k ↦ if k = 0 then 144 else 1) 0 t = cexp (2 * π * t) + 144 := by
  simp [Finset.sum_range_succ, add_comm]

theorem ψI'_I_mul_sub_expPoly_isBigO_atTop :
    (fun t : ℝ ↦ ψI' (I * t) - expPoly 1 (fun k ↦ if k = 0 then 144 else 1) 0 t) =O[atTop]
      fun t ↦ rexp (-π * t) :=
  /- We could add `gcongr` to `IsBigO` and `IsLittleO`, after we do that,
    we could use `grw` here. -/
  ψI'_I_mul_sub_isBigO_atTop.congr_left fun t ↦ by rw [expPoly_ψI']

end MagicFunction
