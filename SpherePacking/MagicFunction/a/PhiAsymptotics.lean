/-
Copyright (c) 2026 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/
module

public import SpherePacking.ModularForms.PhiTransform

import SpherePacking.ModularForms.Delta
import SpherePacking.ModularForms.E2
import SpherePacking.ModularForms.EisensteinAsymptotics
import SpherePacking.ModularForms.FG

/-!
# Asymptotics of `φ₀`, `φ₋₂`, `φ₋₄` at `i∞`

Writing `q = e^{2πiz}`, we show that as `z → i∞`
* `φ₀ = O(q)` (`φ₀_isBigO_atImInfty`),
* `φ₋₂ = 720 + O(q)` (`φ₂'_sub_isBigO_atImInfty`),
* `φ₋₄ = q⁻¹ + 504 + O(q)` (`φ₄'_sub_isBigO_atImInfty`).

These are the inputs, via the `S`-transformation `φ₀_S_transform`, to the asymptotic expansion
`φ₀(i/t) t² = 36/π² e^{2πt} - 8640/π t + 18144/π² + O(t² e^{-2πt})` of the blueprint's
`lemma:phi0-asymptotic`.

The proof follows the blueprint: from `E₄ = 1 + 240q + 2160q² + O(q³)` and
`E₆ = 1 - 504q - 16632q² + O(q³)` (`E₄_sub_isBigO`, `E₆_sub_isBigO`),
`E₂E₄ - E₆ = 720q + O(q²)` (`E₂_mul_E₄_sub_E₆_sub_isBigO`) and `1728 Δ = E₄³ - E₆²`, the
numerators `E₄(E₂E₄ - E₆) - 720Δ` and `E₄² - (q⁻¹ + 504)Δ` are `O(q²)`, while `Δ⁻¹ = O(q⁻¹)`.
-/

@[expose] public section

open UpperHalfPlane hiding I
open ModularForm hiding E₄ E₆
open Real Complex Filter Asymptotics
open scoped Topology

noncomputable section

namespace PhiAsymptotics

/-! ### Abstract algebra of the expansions

We work with abstract functions `q, e₄, e₆, f₁, d` on a filter, standing for
`e^{2πiz}, E₄, E₆, E₂E₄ - E₆, Δ` at `i∞`. -/

variable {α : Type*} {l : Filter α} {q e₄ e₆ f₁ d : α → ℂ}

/-- If `f - p = O(qⁿ)` with `n > 0`, `q → 0` and `p → c`, then `f → c`. -/
private lemma tendsto_of_sub_isBigO (hq : Tendsto q l (𝓝 0)) {f p : α → ℂ} {c : ℂ} {n : ℕ}
    (hn : n ≠ 0) (hp : Tendsto p l (𝓝 c)) (hf : (fun x ↦ f x - p x) =O[l] fun x ↦ q x ^ n) :
    Tendsto f l (𝓝 c) := by
  simpa using (hf.trans_tendsto (by simpa [zero_pow hn] using hq.pow n)).add hp

/-- `e₄ f₁ / d = 720 + O(q)`. -/
private lemma mul_div_sub_isBigO (hq : Tendsto q l (𝓝 0))
    (h4 : (fun x ↦ e₄ x - (1 + 240 * q x + 2160 * q x ^ 2)) =O[l] fun x ↦ q x ^ 3)
    (h6 : (fun x ↦ e₆ x - (1 - 504 * q x - 16632 * q x ^ 2)) =O[l] fun x ↦ q x ^ 3)
    (h1 : (fun x ↦ f₁ x - 720 * q x) =O[l] fun x ↦ q x ^ 2)
    (hd : ∀ x, 1728 * d x = e₄ x ^ 3 - e₆ x ^ 2) (hd0 : ∀ x, d x ≠ 0)
    (hdinv : (fun x ↦ (d x)⁻¹) =O[l] fun x ↦ (q x)⁻¹) (hq0 : ∀ x, q x ≠ 0) :
    (fun x ↦ e₄ x * f₁ x / d x - 720) =O[l] q := by
  -- `e₄ f₁ / d - 720 = M / (1728 d)` and `d⁻¹ = O(q⁻¹)`, so it suffices that
  -- `M = 1728 e₄ f₁ - 720 (e₄³ - e₆²) = O(q²)`
  refine (((?_ : (fun x ↦ 1728 * e₄ x * f₁ x - 720 * (e₄ x ^ 3 - e₆ x ^ 2)) =O[l]
    fun x ↦ q x ^ 2).mul hdinv).const_mul_left (1728⁻¹ : ℂ)).congr
      (fun x ↦ by rw [← hd x]; field_simp [hd0 x]) fun x ↦ by field_simp [hq0 x]
  -- `M = q² Q + (e₄ - P₄) A + (f₁ - 720q) B + (e₆ - P₆) C`, where `P₄`, `P₆` are the polynomial
  -- parts of `e₄`, `e₆`, and the factors `Q`, `A`, `B`, `C` converge, so are bounded
  have hP₄ := ((hq.const_mul 240).const_add 1).add ((hq.pow 2).const_mul 2160)
  have hP₆ := ((hq.const_mul 504).const_sub 1).sub ((hq.pow 2).const_mul 16632)
  have he₄ := tendsto_of_sub_isBigO hq (by norm_num) hP₄ h4
  have hQ := (((((hq.const_mul 2565457920).const_add 328458240).sub
    ((hq.pow 2).const_mul 79647390720)).sub ((hq.pow 3).const_mul 2418647040000)).sub
      ((hq.pow 4).const_mul 7255941120000)).isBigO_one ℂ
  have hA := (((tendsto_of_sub_isBigO hq (by norm_num) (hq.const_mul 720) h1).const_mul 1728).sub
    ((((he₄.pow 2).add (he₄.mul hP₄)).add (hP₄.pow 2)).const_mul 720)).isBigO_one ℂ
  have hB := (hP₄.const_mul 1728).isBigO_one ℂ
  have hC := (((tendsto_of_sub_isBigO hq (by norm_num) hP₆ h6).add hP₆).const_mul 720).isBigO_one ℂ
  have h32 := (isLittleO_pow_pow (𝕜 := ℂ) (by norm_num : 2 < 3)).isBigO.comp_tendsto hq
  refine (((((isBigO_refl (fun x ↦ q x ^ 2) l).mul hQ).add ((h4.trans h32).mul hA)).add
    ((h1.mul hB).add ((h6.trans h32).mul hC))).congr (fun x ↦ ?_) fun x ↦ mul_one _)
  ring

/-- `e₄² / d = q⁻¹ + 504 + O(q)`. -/
private lemma sq_div_sub_isBigO (hq : Tendsto q l (𝓝 0))
    (h4 : (fun x ↦ e₄ x - (1 + 240 * q x + 2160 * q x ^ 2)) =O[l] fun x ↦ q x ^ 3)
    (h6 : (fun x ↦ e₆ x - (1 - 504 * q x - 16632 * q x ^ 2)) =O[l] fun x ↦ q x ^ 3)
    (hd : ∀ x, 1728 * d x = e₄ x ^ 3 - e₆ x ^ 2) (hd0 : ∀ x, d x ≠ 0)
    (hdinv : (fun x ↦ (d x)⁻¹) =O[l] fun x ↦ (q x)⁻¹) (hq0 : ∀ x, q x ≠ 0) :
    (fun x ↦ e₄ x ^ 2 / d x - (q x)⁻¹ - 504) =O[l] q := by
  -- `e₄² / d - q⁻¹ - 504 = N / (1728 q d)` and `(q d)⁻¹ = O(q⁻²)`, so it suffices that
  -- `N = 1728 q e₄² - (1 + 504q) (e₄³ - e₆²) = O(q³)`
  refine (((?_ : (fun x ↦ 1728 * q x * e₄ x ^ 2 - (1 + 504 * q x) * (e₄ x ^ 3 - e₆ x ^ 2))
    =O[l] fun x ↦ q x ^ 3).mul ((isBigO_refl (fun x ↦ (q x)⁻¹) l).mul hdinv)).const_mul_left
      (1728⁻¹ : ℂ)).congr (fun x ↦ by rw [← hd x]; field_simp [hd0 x, hq0 x]; ring)
        fun x ↦ by field_simp [hq0 x]
  -- `N = q³ Q + (e₄ - P₄) A + (e₆ - P₆) B`, where `P₄`, `P₆` are the polynomial parts of `e₄`,
  -- `e₆`, and the factors `Q`, `A`, `B` converge, so are bounded
  have hP₄ := ((hq.const_mul 240).const_add 1).add ((hq.pow 2).const_mul 2160)
  have hP₆ := ((hq.const_mul 504).const_sub 1).sub ((hq.pow 2).const_mul 16632)
  have he₄ := tendsto_of_sub_isBigO hq (by norm_num) hP₄ h4
  have hP := (hq.const_mul 504).const_add 1
  have hQ := (((((hq.const_mul 1595619648).const_add 127730304).sub
    ((hq.pow 2).const_mul 51050248704)).sub ((hq.pow 3).const_mul 1703130624000)).sub
      ((hq.pow 4).const_mul 5079158784000)).isBigO_one ℂ
  have hA := ((((hq.const_mul 1728).mul (he₄.add hP₄))).sub
    (hP.mul (((he₄.pow 2).add (he₄.mul hP₄)).add (hP₄.pow 2)))).isBigO_one ℂ
  have hB := (hP.mul ((tendsto_of_sub_isBigO hq (by norm_num) hP₆ h6).add hP₆)).isBigO_one ℂ
  refine ((((isBigO_refl (fun x ↦ q x ^ 3) l).mul hQ).add (h4.mul hA)).add (h6.mul hB)).congr
    (fun x ↦ ?_) fun x ↦ mul_one _
  ring

end PhiAsymptotics

open PhiAsymptotics

/-! ### The expansions of `φ₀`, `φ₋₂`, `φ₋₄` at `i∞` -/

/-- `Δ⁻¹ = O(q⁻¹)` at `i∞`. -/
lemma inv_Δ_isBigO :
    (fun z : ℍ ↦ (Δ z)⁻¹) =O[atImInfty] fun z ↦ (cexp (2 * π * I * z))⁻¹ := by
  suffices h : (fun z : ℍ ↦ cexp (2 * π * I * z)) =O[atImInfty] Δ by
    exact h.inv_rev (.of_forall fun z hz ↦ absurd hz (Complex.exp_ne_zero _))
  rw [← isBigO_norm_left]
  exact exp_isBigO_discriminant.congr_left fun z ↦ by simp [Complex.norm_exp]

/-- `φ₀ = O(q)` at `i∞`. -/
theorem φ₀_isBigO_atImInfty : φ₀ =O[atImInfty] fun z ↦ cexp (2 * π * I * z) := by
  have hq : Tendsto (fun z : ℍ ↦ cexp (2 * π * I * z)) atImInfty (𝓝 0) := by
    simpa [Function.Periodic.qParam] using qParam_tendsto_atImInfty one_pos
  refine ((?_ : (fun z ↦ (E₂ z * E₄ z - E₆ z) ^ 2) =O[atImInfty]
    fun z ↦ cexp (2 * π * I * z) ^ 2).mul inv_Δ_isBigO).congr
      (fun z ↦ (div_eq_mul_inv _ _).symm) fun z ↦ by field_simp [Complex.exp_ne_zero]
  refine IsBigO.pow ?_ 2
  refine ((E₂_mul_E₄_sub_E₆_sub_isBigO.trans ?_).add
    ((isBigO_refl _ _).const_mul_left 720)).congr_left fun z ↦ by ring
  simpa [Function.comp_def] using (isLittleO_pow_pow (by norm_num : 1 < 2)).isBigO.comp_tendsto hq

/-- `φ₋₂ = 720 + O(q)` at `i∞`. -/
theorem φ₂'_sub_isBigO_atImInfty :
    (fun z ↦ φ₂' z - 720) =O[atImInfty] fun z ↦ cexp (2 * π * I * z) :=
  mul_div_sub_isBigO (by simpa [Function.Periodic.qParam] using qParam_tendsto_atImInfty one_pos)
    E₄_sub_isBigO E₆_sub_isBigO E₂_mul_E₄_sub_E₆_sub_isBigO
    (fun z ↦ by simp [congrFun Δ_eq_E₄_cube_sub_E₆_sq z]) ModularForm.discriminant_ne_zero
    inv_Δ_isBigO fun _ ↦ Complex.exp_ne_zero _

/-- `φ₋₄ = q⁻¹ + 504 + O(q)` at `i∞`. -/
theorem φ₄'_sub_isBigO_atImInfty : (fun z ↦ φ₄' z - (cexp (2 * π * I * z))⁻¹ - 504) =O[atImInfty]
      fun z ↦ cexp (2 * π * I * z) :=
  sq_div_sub_isBigO (by simpa [Function.Periodic.qParam] using qParam_tendsto_atImInfty one_pos)
    E₄_sub_isBigO E₆_sub_isBigO (fun z ↦ by simp [congrFun Δ_eq_E₄_cube_sub_E₆_sq z])
    ModularForm.discriminant_ne_zero inv_Δ_isBigO fun _ ↦ Complex.exp_ne_zero _

end
