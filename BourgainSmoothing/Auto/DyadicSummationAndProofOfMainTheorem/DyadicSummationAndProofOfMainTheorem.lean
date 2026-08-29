/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import BourgainSmoothing.Auto.NondecayingEndpointAndInterpolation.NondecayingEndpointAndInterpolation
import Mathlib.Algebra.Field.GeomSum

/-!
# Dyadic summation and proof of the main theorem

Formalizations of the labeled auxiliary estimates in the corresponding
section of `blueprint/blueprint.tex`.  The introduction contains the statement
of the main theorem itself; this file supplies the four labeled estimates used
in its dyadic proof.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Real FourierTransform Topology

namespace Auto

/--
If \(f_0\in L^\infty(\mathbb R)\) and \(f_1,f_2\in L^2(\mathbb R)\), then
\[
\mathcal I_\chi(f_0,f_1,f_2)
\leq
\lVert\chi\rVert_1\lVert f_0\rVert_\infty
\lVert f_1\rVert_2\lVert f_2\rVert_2.
\]
-/
theorem elementaryL2Endpoint
    (χ : ℝ → ℝ) (f₀ f₁ f₂ : ℝ → ℂ)
    (hχ_memLp : MemLp χ (1 : ℝ≥0∞) volume)
    (hf₀_memLp : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁_memLp : MemLp f₁ (2 : ℝ≥0∞) volume)
    (hf₂_memLp : MemLp f₂ (2 : ℝ≥0∞) volume) :
    trilinearFormAbs χ f₀ f₁ f₂ ≤
      (eLpNorm χ (1 : ℝ≥0∞) volume).toReal *
        (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
          (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal *
            (eLpNorm f₂ (2 : ℝ≥0∞) volume).toReal := by
  have hχint : Integrable (fun t : ℝ ↦ (χ t : ℂ)) :=
    memLp_one_iff_integrable.mp hχ_memLp.ofReal
  have hχnorm : (∫ t : ℝ, ‖(χ t : ℂ)‖) =
      (eLpNorm χ (1 : ℝ≥0∞) volume).toReal := by
    calc
      (∫ t : ℝ, ‖(χ t : ℂ)‖) = ∫ t : ℝ, ‖χ t‖ := by
        apply integral_congr_ae
        filter_upwards with t
        simp
      _ = lpNorm χ 1 volume :=
        (lpNorm_one_eq_integral_norm hχ_memLp.aestronglyMeasurable).symm
      _ = _ := (toReal_eLpNorm hχ_memLp.aestronglyMeasurable).symm
  rw [← hχnorm]
  exact aux_trilinearFormAbs_le_linf_l2_l2 χ f₀ f₁ f₂ hχint hf₀_memLp hf₁_memLp hf₂_memLp

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: the negative Sobolev multiplier preserves `L²`. -/
lemma aux_weight_memLp_two (σ : ℝ) (hσ : 0 ≤ σ)
    (G : Lp (α := ℝ) ℂ 2 volume) :
    MemLp (fun ζ ↦ (japaneseBracket ζ ^ (-σ)) • G ζ)
      (2 : ℝ≥0∞) volume := by
  have hjap_cont : Continuous japaneseBracket := by
    unfold japaneseBracket
    fun_prop
  have hweight_cont : Continuous
      (fun ζ : ℝ ↦ japaneseBracket ζ ^ (-σ)) := by
    exact hjap_cont.rpow continuous_const (fun ζ ↦ Or.inl (by
      have hpos : 0 < japaneseBracket ζ := by
        unfold japaneseBracket
        exact Real.sqrt_pos.2 (by positivity)
      exact hpos.ne'))
  have hweight_bound : ∀ ζ : ℝ,
      ‖japaneseBracket ζ ^ (-σ)‖ ≤ 1 := by
    intro ζ
    have hjap_nonneg : 0 ≤ japaneseBracket ζ := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hjap_nonneg _)]
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · unfold japaneseBracket
      have harg : (1 : ℝ) ≤ 1 + |ζ| ^ 2 := by
        nlinarith [sq_nonneg |ζ|]
      simpa using (Real.sqrt_le_sqrt harg)
    · linarith
  have hweight : MemLp (fun ζ : ℝ ↦ japaneseBracket ζ ^ (-σ))
      (∞ : ℝ≥0∞) volume :=
    memLp_top_of_bound hweight_cont.aestronglyMeasurable 1
      (Filter.Eventually.of_forall hweight_bound)
  letI : (∞ : ℝ≥0∞).HolderTriple 2 2 := ENNReal.HolderTriple.symm
  exact (Lp.memLp G).smul hweight

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: the Sobolev norm used below is finite. -/
lemma aux_sobolevNorm_lt_top (σ : ℝ) (hσ : 0 ≤ σ)
    (G : Lp (α := ℝ) ℂ 2 volume) :
    sobolevNorm σ G < ∞ := by
  unfold sobolevNorm
  exact (aux_weight_memLp_two σ hσ (Lp.fourierTransformₗᵢ ℝ ℂ G)).eLpNorm_lt_top

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: transfers a pointwise multiplier bound to an `L²` norm bound. -/
lemma aux_weighted_multiplier_toReal_bound
    (σ : ℝ) (m F : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ ζ : ℝ, ‖m ζ‖ ≤ C * japaneseBracket ζ ^ (-σ))
    (hFfinite : eLpNorm
      (fun ζ ↦ (japaneseBracket ζ ^ (-σ)) • F ζ)
      (2 : ℝ≥0∞) volume < ∞) :
    (eLpNorm (fun ζ ↦ m ζ * F ζ) (2 : ℝ≥0∞) volume).toReal ≤
      C * (eLpNorm
        (fun ζ ↦ (japaneseBracket ζ ^ (-σ)) • F ζ)
        (2 : ℝ≥0∞) volume).toReal := by
  have hbound : eLpNorm (fun ζ ↦ m ζ * F ζ) (2 : ℝ≥0∞) volume ≤
      ENNReal.ofReal C * eLpNorm
        (fun ζ ↦ (japaneseBracket ζ ^ (-σ)) • F ζ)
          (2 : ℝ≥0∞) volume := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    filter_upwards with ζ
    rw [norm_mul]
    calc
      ‖m ζ‖ * ‖F ζ‖ ≤
          (C * japaneseBracket ζ ^ (-σ)) * ‖F ζ‖ :=
        mul_le_mul_of_nonneg_right (hm ζ) (norm_nonneg _)
      _ = C * ‖(japaneseBracket ζ ^ (-σ)) • F ζ‖ := by
        have hbracket : 0 ≤ japaneseBracket ζ := Real.sqrt_nonneg _
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg hbracket _)]
        ring
  have hright_ne : ENNReal.ofReal C * eLpNorm
      (fun ζ ↦ (japaneseBracket ζ ^ (-σ)) • F ζ)
      (2 : ℝ≥0∞) volume ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFfinite.ne
  have hreal := ENNReal.toReal_mono hright_ne hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at hreal
  exact hreal

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: bounds the Japanese bracket on the low-frequency support. -/
lemma aux_japaneseBracket_le_sqrt_five {ξ : ℝ} (hξ : |ξ| ≤ 2) :
    japaneseBracket ξ ≤ Real.sqrt 5 := by
  unfold japaneseBracket
  rw [← sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hξ) (by positivity : 0 ≤ 2 + |ξ|)]

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: rewrites the low-frequency constant. -/
lemma aux_sqrt_five_rpow (σ : ℝ) :
    (Real.sqrt 5) ^ σ = (5 : ℝ) ^ (σ / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : 0 ≤ (5 : ℝ))]
  congr 1
  ring

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: pointwise low-frequency multiplier estimate. -/
lemma aux_low_multiplier_bound (σ : ℝ) (hσ : 0 ≤ σ) (ξ : ℝ) :
    ‖(lowFrequencyCutoff ξ : ℂ)‖ ≤
      (5 : ℝ) ^ (σ / 2) * japaneseBracket ξ ^ (-σ) := by
  by_cases hzero : lowFrequencyCutoff ξ = 0
  · simp only [hzero, Complex.ofReal_zero, norm_zero]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have habs_lt : |ξ| < 2 := by
    by_contra hnot
    exact hzero (aux_lowFrequencyCutoff_eq_zero_of_two_le_abs (le_of_not_gt hnot))
  have hjap_le : japaneseBracket ξ ≤ Real.sqrt 5 :=
    aux_japaneseBracket_le_sqrt_five habs_lt.le
  have hjap_pos : 0 < japaneseBracket ξ := by
    unfold japaneseBracket
    exact Real.sqrt_pos.2 (by positivity)
  have hsqrt_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hpow : japaneseBracket ξ ^ σ ≤ (Real.sqrt 5) ^ σ :=
    Real.rpow_le_rpow hjap_pos.le hjap_le hσ
  have hfactor : 1 ≤ (Real.sqrt 5) ^ σ * japaneseBracket ξ ^ (-σ) := by
    rw [Real.rpow_neg hjap_pos.le]
    rw [show (Real.sqrt 5) ^ σ * (japaneseBracket ξ ^ σ)⁻¹ =
        (Real.sqrt 5) ^ σ / japaneseBracket ξ ^ σ by rw [div_eq_mul_inv]]
    exact (one_le_div₀ (Real.rpow_pos_of_pos hjap_pos σ)).mpr hpow
  have hcut : ‖(lowFrequencyCutoff ξ : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real]
    unfold lowFrequencyCutoff
    rw [Real.norm_eq_abs,
      abs_of_nonneg (aux_smoothStep_nonneg_le_one _).1]
    exact (aux_smoothStep_nonneg_le_one _).2
  rw [← aux_sqrt_five_rpow σ]
  exact hcut.trans hfactor

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: proves its low-frequency estimate. -/
lemma aux_low_projection_estimate (σ : ℝ) (hσ : 0 ≤ σ)
    (f : ℝ → ℂ) (hf : MemLp f (2 : ℝ≥0∞) volume) :
    (eLpNorm (P 0 f) (2 : ℝ≥0∞) volume).toReal ≤
      (5 : ℝ) ^ (σ / 2) *
        (sobolevNorm σ (hf.toLp f)).toReal := by
  have hP : MemLp (P 0 f) (2 : ℝ≥0∞) volume := aux_memLp_P_zero f hf
  have hfinite : eLpNorm
      (fun ζ ↦ (japaneseBracket ζ ^ (-σ)) • aux_l2Fourier f ζ)
      (2 : ℝ≥0∞) volume < ∞ := by
    rw [aux_l2Fourier, dite_eq_left hf]
    exact aux_sobolevNorm_lt_top σ hσ (hf.toLp f)
  have hmult := aux_weighted_multiplier_toReal_bound σ
    (fun ζ ↦ (lowFrequencyCutoff ζ : ℂ)) (aux_l2Fourier f)
    ((5 : ℝ) ^ (σ / 2))
    (Real.rpow_nonneg (by norm_num) _)
    (aux_low_multiplier_bound σ hσ) hfinite
  have hFourier := aux_l2Fourier_P_zero_ae_eq_multiplier f hf
  calc
    (eLpNorm (P 0 f) (2 : ℝ≥0∞) volume).toReal =
        (eLpNorm (aux_l2Fourier (P 0 f)) (2 : ℝ≥0∞) volume).toReal := by
      rw [aux_eLpNorm_aux_l2Fourier_eq (P 0 f) hP]
    _ = (eLpNorm (fun ζ ↦ (lowFrequencyCutoff ζ : ℂ) * aux_l2Fourier f ζ)
        (2 : ℝ≥0∞) volume).toReal := by
      rw [eLpNorm_congr_ae hFourier]
    _ ≤ (5 : ℝ) ^ (σ / 2) *
        (eLpNorm (fun ζ ↦ (japaneseBracket ζ ^ (-σ)) • aux_l2Fourier f ζ)
          (2 : ℝ≥0∞) volume).toReal := hmult
    _ = (5 : ℝ) ^ (σ / 2) *
        (sobolevNorm σ (hf.toLp f)).toReal := by
      rw [aux_l2Fourier, dite_eq_left hf]
      rfl

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: monotonicity of the cutoff transition. -/
lemma aux_smoothStep_monotoneOn_unit : MonotoneOn smoothStep (Set.Icc (0 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact aux_continuous_smoothStep.continuousOn
  · intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa using hx
    exact (aux_smoothStep_differentiableAt_of_ne x (ne_of_gt hx'.1)
      (ne_of_lt hx'.2)).differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa using hx
    rw [aux_smoothStep_deriv_on_Ioo x hx'.1 hx'.2]
    have hprod : 0 ≤ x * (1 - x) := mul_nonneg hx'.1.le (by linarith [hx'.2])
    nlinarith

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: global monotonicity needed for dyadic telescoping. -/
lemma aux_smoothStep_monotone : Monotone smoothStep := by
  intro x y hxy
  by_cases hy0 : y ≤ 0
  · have hx0 : x ≤ 0 := le_trans hxy hy0
    rw [aux_smoothStep_eq_zero_of_nonpos hx0, aux_smoothStep_eq_zero_of_nonpos hy0]
  by_cases hx1 : 1 ≤ x
  · have hy1 : 1 ≤ y := le_trans hx1 hxy
    rw [aux_smoothStep_eq_one_of_one_le hx1, aux_smoothStep_eq_one_of_one_le hy1]
  by_cases hx0 : x ≤ 0
  · rw [aux_smoothStep_eq_zero_of_nonpos hx0]
    exact (aux_smoothStep_nonneg_le_one y).1
  by_cases hy1 : 1 ≤ y
  · rw [aux_smoothStep_eq_one_of_one_le hy1]
    exact (aux_smoothStep_nonneg_le_one x).2
  · apply aux_smoothStep_monotoneOn_unit
    · exact ⟨le_of_not_ge hx0, (lt_of_not_ge hx1).le⟩
    · exact ⟨le_trans (le_of_not_ge hx0) hxy, (lt_of_not_ge hy1).le⟩
    · exact hxy

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: nonnegativity of each dyadic cutoff. -/
lemma aux_dyadicCutoff_nonneg (ξ : ℝ) : 0 ≤ dyadicCutoff ξ := by
  unfold dyadicCutoff lowFrequencyCutoff
  have habs : |2 * ξ| = 2 * |ξ| := by
    rw [abs_mul]
    norm_num
  rw [habs]
  have h : 2 - 2 * |ξ| ≤ 2 - |ξ| := by nlinarith [abs_nonneg ξ]
  exact sub_nonneg.mpr (aux_smoothStep_monotone h)

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: upper bound for each dyadic cutoff. -/
lemma aux_dyadicCutoff_le_one (ξ : ℝ) : dyadicCutoff ξ ≤ 1 := by
  unfold dyadicCutoff lowFrequencyCutoff
  have h1 := (aux_smoothStep_nonneg_le_one (2 - |ξ|)).2
  have h2 := (aux_smoothStep_nonneg_le_one (2 - |2 * ξ|)).1
  linarith

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: square cutoff domination used in telescoping. -/
lemma aux_dyadicCutoff_sq_le_self (ξ : ℝ) : dyadicCutoff ξ ^ 2 ≤ dyadicCutoff ξ := by
  have h0 := aux_dyadicCutoff_nonneg ξ
  have h1 := aux_dyadicCutoff_le_one ξ
  nlinarith

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: finite square-sum cutoff bound. -/
lemma aux_dyadicCutoff_finite_square_sum_le_one (N : ℕ) (ξ : ℝ) :
    ∑ k ∈ Finset.range N, dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) ^ 2 ≤ 1 := by
  calc
    ∑ k ∈ Finset.range N, dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) ^ 2 ≤
        ∑ k ∈ Finset.range N, dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) := by
      gcongr with k hk
      exact aux_dyadicCutoff_sq_le_self _
    _ ≤ 1 := by
      have htel := aux_dyadic_telescoping N ξ
      have hleft : 0 ≤ lowFrequencyCutoff ξ :=
        (aux_smoothStep_nonneg_le_one _).1
      have hright : lowFrequencyCutoff (ξ / (2 : ℝ) ^ N) ≤ 1 :=
        (aux_smoothStep_nonneg_le_one _).2
      linarith

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: Plancherel energy identity for a positive dyadic projection. -/
lemma aux_positive_projection_energy_eq (f : ℝ → ℂ)
    (hf : MemLp f (2 : ℝ≥0∞) volume) (k : ℕ) :
    (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume) ^ (2 : ℝ) =
      ∫⁻ ξ : ℝ,
        ‖(dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) : ℂ) *
          aux_l2Fourier f ξ‖ₑ ^ (2 : ℝ) := by
  have hP : MemLp (P (k + 1) f) (2 : ℝ≥0∞) volume :=
    aux_memLp_P_succ f hf k
  have hFourier := aux_l2Fourier_P_ae_eq_multiplier f hf (k + 1) (by omega)
  calc
    (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume) ^ (2 : ℝ) =
        (eLpNorm (aux_l2Fourier (P (k + 1) f)) (2 : ℝ≥0∞) volume) ^ (2 : ℝ) := by
      rw [aux_eLpNorm_aux_l2Fourier_eq (P (k + 1) f) hP]
    _ = ∫⁻ ξ : ℝ, ‖aux_l2Fourier (P (k + 1) f) ξ‖ₑ ^ (2 : ℝ) := by
      exact eLpNorm_nnreal_pow_eq_lintegral (by norm_num)
    _ = ∫⁻ ξ : ℝ,
        ‖(dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) : ℂ) *
          aux_l2Fourier f ξ‖ₑ ^ (2 : ℝ) := by
      apply lintegral_congr_ae
      filter_upwards [hFourier] with ξ hξ
      rw [hξ]

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: sharp support-based Japanese bracket bound. -/
lemma aux_japaneseBracket_sq_le_dyadic_sharp (k : ℕ) (ξ : ℝ)
    (hφ : dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) ≠ 0) :
    japaneseBracket ξ ^ 2 ≤ (2 : ℝ) ^ (2 * k + 5) := by
  have hsupp := aux_scaled_dyadicCutoff_support (k := k + 1) (by omega) hφ
  have hupper : |ξ| ≤ (2 : ℝ) ^ (k + 2) := by
    convert hsupp.2 using 1 <;> omega
  have hpow : ((2 : ℝ) ^ (k + 2)) ^ 2 = (2 : ℝ) ^ (2 * k + 4) := by
    rw [← pow_mul]
    congr 1
    omega
  have hsq : |ξ| ^ 2 ≤ (2 : ℝ) ^ (2 * k + 4) := by
    calc
      |ξ| ^ 2 ≤ ((2 : ℝ) ^ (k + 2)) ^ 2 := by
        exact (sq_le_sq₀ (abs_nonneg ξ) (by positivity)).mpr hupper
      _ = _ := hpow
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * k + 4) :=
    one_le_pow₀ (by norm_num)
  have hpowtwo : (2 : ℝ) ^ (2 * k + 5) = 2 * (2 : ℝ) ^ (2 * k + 4) := by
    rw [show 2 * k + 5 = (2 * k + 4) + 1 by omega, pow_succ]
    ring
  rw [japaneseBracket]
  rw [Real.sq_sqrt (by positivity)]
  rw [hpowtwo]
  linarith

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: raises the sharp support bound to the Sobolev exponent. -/
lemma aux_japaneseBracket_weight_bound_sharp (σ : ℝ) (hσ : 0 ≤ σ) (k : ℕ) (ξ : ℝ)
    (hφ : dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) ≠ 0) :
    japaneseBracket ξ ^ (2 * σ) ≤
      (2 : ℝ) ^ (σ * (2 * (k : ℝ) + 5)) := by
  have hsq := aux_japaneseBracket_sq_le_dyadic_sharp k ξ hφ
  have hjap : 0 ≤ japaneseBracket ξ := Real.sqrt_nonneg _
  have hjpow : japaneseBracket ξ ^ (2 : ℝ) = japaneseBracket ξ ^ (2 : ℕ) := by
    exact Real.rpow_natCast _ 2
  have hsq' : japaneseBracket ξ ^ (2 : ℝ) ≤ (2 : ℝ) ^ (2 * k + 5) := by
    rw [hjpow]
    exact hsq
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg hjap _) hsq' hσ
  calc
    japaneseBracket ξ ^ (2 * σ) = (japaneseBracket ξ ^ (2 : ℝ)) ^ σ := by
      exact Real.rpow_mul (x := japaneseBracket ξ) hjap (2 : ℝ) σ
    _ ≤ ((2 : ℝ) ^ (2 * k + 5)) ^ σ := hp
    _ = (2 : ℝ) ^ (σ * (2 * (k : ℝ) + 5)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      push_cast
      ring

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: sharp `3σ` scalar dyadic weight estimate. -/
lemma aux_dyadic_weight_bound_sharp (σ : ℝ) (hσ : 0 < σ) (k : ℕ) (ξ : ℝ)
    (hφ : dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) ≠ 0) :
    (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) ≤
      (2 : ℝ) ^ (3 * σ) * japaneseBracket ξ ^ (-2 * σ) := by
  have hJ := aux_japaneseBracket_weight_bound_sharp σ hσ.le k ξ hφ
  have hjpos : 0 < japaneseBracket ξ := by
    unfold japaneseBracket
    positivity
  have hJpos : 0 < japaneseBracket ξ ^ (2 * σ) :=
    Real.rpow_pos_of_pos hjpos _
  have hcancel : japaneseBracket ξ ^ (2 * σ) *
      japaneseBracket ξ ^ (-2 * σ) = 1 := by
    rw [← Real.rpow_add hjpos]
    norm_num
  apply le_of_mul_le_mul_left _ hJpos
  calc
    japaneseBracket ξ ^ (2 * σ) *
        (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) ≤
        (2 : ℝ) ^ (σ * (2 * (k : ℝ) + 5)) *
          (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hJ (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ (3 * σ) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      push_cast
      ring
    _ = japaneseBracket ξ ^ (2 * σ) *
        ((2 : ℝ) ^ (3 * σ) * japaneseBracket ξ ^ (-2 * σ)) := by
      calc
        (2 : ℝ) ^ (3 * σ) = (2 : ℝ) ^ (3 * σ) * 1 := (mul_one _).symm
        _ = (2 : ℝ) ^ (3 * σ) *
            (japaneseBracket ξ ^ (2 * σ) * japaneseBracket ξ ^ (-2 * σ)) := by
              rw [hcancel]
        _ = _ := by ring

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: real pointwise weighted dyadic energy bound. -/
lemma aux_pointwise_weighted_projection_energy_bound
    (σ : ℝ) (hσ : 0 < σ) (k : ℕ) (ξ : ℝ) (F : ℂ) :
    (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) *
        ‖(dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) : ℂ) * F‖ ^ 2 ≤
      (2 : ℝ) ^ (3 * σ) *
        dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) ^ 2 *
          ‖(japaneseBracket ξ ^ (-σ)) • F‖ ^ 2 := by
  let φ : ℝ := dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1))
  let B : ℝ := japaneseBracket ξ
  have hφnonneg : 0 ≤ φ := aux_dyadicCutoff_nonneg _
  have hBnonneg : 0 ≤ B := Real.sqrt_nonneg _
  have hBpos : 0 < B := by
    dsimp [B, japaneseBracket]
    positivity
  have hpow : B ^ (-2 * σ) = (B ^ (-σ)) ^ 2 := by
    calc
      B ^ (-2 * σ) = B ^ ((-σ) * (2 : ℝ)) := by congr 1 <;> ring
      _ = (B ^ (-σ)) ^ (2 : ℝ) := Real.rpow_mul hBnonneg (-σ) (2 : ℝ)
      _ = (B ^ (-σ)) ^ (2 : ℕ) := Real.rpow_natCast _ 2
  by_cases hφ : φ = 0
  · simp [φ, hφ]
  have hweight : (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) ≤
      (2 : ℝ) ^ (3 * σ) * B ^ (-2 * σ) := by
    simpa only [φ, B] using aux_dyadic_weight_bound_sharp σ hσ k ξ hφ
  have hscaled := mul_le_mul_of_nonneg_right hweight
    (mul_nonneg (sq_nonneg φ) (sq_nonneg ‖F‖))
  have hnormφ : ‖(φ : ℂ) * F‖ = φ * ‖F‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hφnonneg]
  have hnormB : ‖(B ^ (-σ)) • F‖ = B ^ (-σ) * ‖F‖ := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hBnonneg _)]
  dsimp [φ, B] at hweight hscaled hnormφ hnormB ⊢
  rw [hnormφ, hnormB]
  calc
    (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) *
        (dyadicCutoff (ξ / 2 ^ (k + 1)) * ‖F‖) ^ 2 =
        (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) *
          (dyadicCutoff (ξ / 2 ^ (k + 1)) ^ 2 * ‖F‖ ^ 2) := by ring
    _ ≤ ((2 : ℝ) ^ (3 * σ) * japaneseBracket ξ ^ (-2 * σ)) *
          (dyadicCutoff (ξ / 2 ^ (k + 1)) ^ 2 * ‖F‖ ^ 2) := hscaled
    _ = (2 : ℝ) ^ (3 * σ) * dyadicCutoff (ξ / 2 ^ (k + 1)) ^ 2 *
          (japaneseBracket ξ ^ (-σ) * ‖F‖) ^ 2 := by
      rw [hpow]
      ring

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: ENNReal version of the pointwise dyadic energy bound. -/
lemma aux_ennreal_pointwise_weighted_projection_energy_bound
    (σ : ℝ) (hσ : 0 < σ) (k : ℕ) (ξ : ℝ) (F : ℂ) :
    ENNReal.ofReal ((2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ))) *
        ‖(dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) : ℂ) * F‖ₑ ^ (2 : ℕ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (3 * σ)) *
        ENNReal.ofReal (dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) ^ 2) *
          ‖(japaneseBracket ξ ^ (-σ)) • F‖ₑ ^ (2 : ℕ) := by
  have hreal := aux_pointwise_weighted_projection_energy_bound σ hσ k ξ F
  have henn := ENNReal.ofReal_le_ofReal hreal
  have hC : 0 ≤ (2 : ℝ) ^ (3 * σ) := Real.rpow_nonneg (by norm_num) _
  have hφsq : 0 ≤ dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) ^ 2 := sq_nonneg _
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)] at henn
  rw [ENNReal.ofReal_mul (mul_nonneg hC hφsq)] at henn
  rw [ENNReal.ofReal_mul hC] at henn
  rw [ENNReal.ofReal_pow (norm_nonneg _) 2,
    ENNReal.ofReal_pow (norm_nonneg _) 2,
    ofReal_norm_eq_enorm, ofReal_norm_eq_enorm] at henn
  exact henn

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: measurability for Tonelli's theorem. -/
lemma aux_weighted_projection_integrand_aemeasurable
    (σ : ℝ) (f : ℝ → ℂ) (hf : MemLp f (2 : ℝ≥0∞) volume) (k : ℕ) :
    AEMeasurable (fun ξ : ℝ ↦
      ENNReal.ofReal ((2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ))) *
        ‖(dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) : ℂ) *
          aux_l2Fourier f ξ‖ₑ ^ (2 : ℕ)) volume := by
  have hscale : Continuous (fun ξ : ℝ ↦ ξ / (2 : ℝ) ^ (k + 1)) :=
    continuous_id.div_const _
  have hφ : AEStronglyMeasurable
      (fun ξ : ℝ ↦ (dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) : ℂ)) volume :=
    (Complex.continuous_ofReal.comp (aux_continuous_dyadicCutoff.comp hscale)).aestronglyMeasurable
  have hF : AEStronglyMeasurable (aux_l2Fourier f) volume := by
    rw [aux_l2Fourier, dite_eq_left hf]
    exact (Lp.memLp _).aestronglyMeasurable
  exact ((hφ.mul hF).aemeasurable.enorm.pow_const (2 : ℕ)).const_mul _

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: measurability of a positive projection energy. -/
lemma aux_positive_projection_fourier_energy_aemeasurable
    (f : ℝ → ℂ) (hf : MemLp f (2 : ℝ≥0∞) volume) (k : ℕ) :
    AEMeasurable (fun ξ : ℝ ↦
      ‖(dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) : ℂ) *
        aux_l2Fourier f ξ‖ₑ ^ (2 : ℕ)) volume := by
  have hscale : Continuous (fun ξ : ℝ ↦ ξ / (2 : ℝ) ^ (k + 1)) :=
    continuous_id.div_const _
  have hφ : AEStronglyMeasurable
      (fun ξ : ℝ ↦ (dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) : ℂ)) volume :=
    (Complex.continuous_ofReal.comp (aux_continuous_dyadicCutoff.comp hscale)).aestronglyMeasurable
  have hF : AEStronglyMeasurable (aux_l2Fourier f) volume := by
    rw [aux_l2Fourier, dite_eq_left hf]
    exact (Lp.memLp _).aestronglyMeasurable
  exact (hφ.mul hF).aemeasurable.enorm.pow_const (2 : ℕ)

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: Sobolev energy as a Fourier `lintegral`. -/
lemma aux_sobolev_energy_eq_lintegral (σ : ℝ)
    (f : ℝ → ℂ) (hf : MemLp f (2 : ℝ≥0∞) volume) :
    (sobolevNorm σ (hf.toLp f)) ^ (2 : ℝ) =
      ∫⁻ ξ : ℝ,
        ‖(japaneseBracket ξ ^ (-σ)) • aux_l2Fourier f ξ‖ₑ ^ (2 : ℝ) := by
  unfold sobolevNorm
  rw [aux_l2Fourier, dite_eq_left hf]
  convert eLpNorm_nnreal_pow_eq_lintegral
    (f := fun ξ : ℝ ↦ (japaneseBracket ξ ^ (-σ)) •
      (Lp.fourierTransformₗᵢ ℝ ℂ (hf.toLp f)) ξ)
    (μ := volume) (p := (2 : NNReal)) (by norm_num) using 1 <;> norm_num

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: ENNReal dyadic cutoff square-sum bound. -/
lemma aux_dyadicCutoff_ennreal_tsum_square_le_one (ξ : ℝ) :
    ∑' k : ℕ,
      ENNReal.ofReal (dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) ^ 2) ≤ 1 := by
  apply tsum_le_of_sum_le' (by norm_num)
  intro s
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k hk ↦ sq_nonneg _)]
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  obtain ⟨N, hsN⟩ := Finset.exists_nat_subset_range s
  calc
    ∑ k ∈ s, dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) ^ 2 ≤
        ∑ k ∈ Finset.range N, dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsN
      intro k hk hks
      positivity
    _ ≤ 1 := aux_dyadicCutoff_finite_square_sum_le_one N ξ

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: pointwise ENNReal weighted energy summation. -/
lemma aux_ennreal_pointwise_tsum_weighted_projection_energy_bound
    (σ : ℝ) (hσ : 0 < σ) (ξ : ℝ) (F : ℂ) :
    ∑' k : ℕ,
      ENNReal.ofReal ((2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ))) *
        ‖(dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) : ℂ) * F‖ₑ ^ (2 : ℕ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (3 * σ)) *
        ‖(japaneseBracket ξ ^ (-σ)) • F‖ₑ ^ (2 : ℕ) := by
  let C : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (3 * σ))
  let W : ℝ≥0∞ := ‖(japaneseBracket ξ ^ (-σ)) • F‖ₑ ^ (2 : ℕ)
  let φsq : ℕ → ℝ≥0∞ := fun k ↦
    ENNReal.ofReal (dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) ^ 2)
  calc
    ∑' k : ℕ,
        ENNReal.ofReal ((2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ))) *
          ‖(dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) : ℂ) * F‖ₑ ^ (2 : ℕ) ≤
        ∑' k : ℕ, C * φsq k * W := by
          apply ENNReal.tsum_le_tsum
          intro k
          exact aux_ennreal_pointwise_weighted_projection_energy_bound σ hσ k ξ F
    _ = C * (∑' k : ℕ, φsq k * W) := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro k
      rw [mul_assoc]
    _ = C * ((∑' k : ℕ, φsq k) * W) := by rw [ENNReal.tsum_mul_right]
    _ ≤ C * (1 * W) := by
      gcongr
      exact aux_dyadicCutoff_ennreal_tsum_square_le_one ξ
    _ = ENNReal.ofReal ((2 : ℝ) ^ (3 * σ)) *
        ‖(japaneseBracket ξ ^ (-σ)) • F‖ₑ ^ (2 : ℕ) := by
      simp [C, W]

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: Tonelli transfer of the sharp pointwise estimate. -/
lemma aux_weighted_dyadic_energy_ennreal_bound
    (σ : ℝ) (hσ : 0 < σ)
    (f : ℝ → ℂ) (hf : MemLp f (2 : ℝ≥0∞) volume) :
    ∑' k : ℕ,
      ENNReal.ofReal ((2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ))) *
        (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume) ^ (2 : ℝ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (3 * σ)) *
        (sobolevNorm σ (hf.toLp f)) ^ (2 : ℝ) := by
  let a : ℕ → ℝ≥0∞ := fun k ↦
    ENNReal.ofReal ((2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)))
  let g : ℕ → ℝ → ℝ≥0∞ := fun k ξ ↦
    a k * ‖(dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) : ℂ) *
      aux_l2Fourier f ξ‖ₑ ^ (2 : ℕ)
  let C : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (3 * σ))
  let W : ℝ → ℝ≥0∞ := fun ξ ↦
    ‖(japaneseBracket ξ ^ (-σ)) • aux_l2Fourier f ξ‖ₑ ^ (2 : ℕ)
  have hgmeas : ∀ k, AEMeasurable (g k) volume := by
    intro k
    exact aux_weighted_projection_integrand_aemeasurable σ f hf k
  have hWmem : MemLp (fun ξ ↦
      (japaneseBracket ξ ^ (-σ)) • aux_l2Fourier f ξ)
      (2 : ℝ≥0∞) volume := by
    rw [aux_l2Fourier, dite_eq_left hf]
    exact aux_weight_memLp_two σ hσ.le (Lp.fourierTransformₗᵢ ℝ ℂ (hf.toLp f))
  have hWmeas : AEMeasurable W volume :=
    hWmem.aestronglyMeasurable.aemeasurable.enorm.pow_const (2 : ℕ)
  have hSob : (sobolevNorm σ (hf.toLp f)) ^ (2 : ℝ) =
      ∫⁻ ξ : ℝ, W ξ := by
    calc
      (sobolevNorm σ (hf.toLp f)) ^ (2 : ℝ) =
          ∫⁻ ξ : ℝ,
            ‖(japaneseBracket ξ ^ (-σ)) • aux_l2Fourier f ξ‖ₑ ^ (2 : ℝ) :=
        aux_sobolev_energy_eq_lintegral σ f hf
      _ = ∫⁻ ξ : ℝ,
            ‖(japaneseBracket ξ ^ (-σ)) • aux_l2Fourier f ξ‖ₑ ^ (2 : ℕ) := by
        apply lintegral_congr
        intro ξ
        exact ENNReal.rpow_natCast _ 2
  have hpoint : ∀ ξ : ℝ, ∑' k : ℕ, g k ξ ≤ C * W ξ := by
    intro ξ
    exact aux_ennreal_pointwise_tsum_weighted_projection_energy_bound σ hσ ξ
      (aux_l2Fourier f ξ)
  have hEnergyNat (k : ℕ) :
      (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume) ^ (2 : ℝ) =
        ∫⁻ ξ : ℝ, ‖(dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) : ℂ) *
          aux_l2Fourier f ξ‖ₑ ^ (2 : ℕ) := by
    calc
      (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume) ^ (2 : ℝ) =
          ∫⁻ ξ : ℝ, ‖(dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) : ℂ) *
            aux_l2Fourier f ξ‖ₑ ^ (2 : ℝ) :=
        aux_positive_projection_energy_eq f hf k
      _ = ∫⁻ ξ : ℝ, ‖(dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) : ℂ) *
            aux_l2Fourier f ξ‖ₑ ^ (2 : ℕ) := by
        apply lintegral_congr
        intro ξ
        exact ENNReal.rpow_natCast _ 2
  calc
    ∑' k : ℕ,
        ENNReal.ofReal ((2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ))) *
          (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume) ^ (2 : ℝ) =
        ∑' k : ℕ, ∫⁻ ξ : ℝ, g k ξ := by
      apply tsum_congr
      intro k
      rw [hEnergyNat k]
      simpa only [g] using (lintegral_const_mul'' (a k)
        (aux_positive_projection_fourier_energy_aemeasurable f hf k)).symm
    _ = ∫⁻ ξ : ℝ, ∑' k : ℕ, g k ξ := (lintegral_tsum hgmeas).symm
    _ ≤ ∫⁻ ξ : ℝ, C * W ξ := lintegral_mono hpoint
    _ = C * ∫⁻ ξ : ℝ, W ξ := lintegral_const_mul'' C hWmeas
    _ = ENNReal.ofReal ((2 : ℝ) ^ (3 * σ)) *
        (sobolevNorm σ (hf.toLp f)) ^ (2 : ℝ) := by
      rw [hSob]

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: converts a finite ENNReal squared energy to a real expression. -/
lemma aux_toReal_ofReal_mul_rpow_two (a : ℝ) (ha : 0 ≤ a) (x : ℝ≥0∞) :
    (ENNReal.ofReal a * x ^ (2 : ℝ)).toReal = a * x.toReal ^ (2 : ℕ) := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha, ← ENNReal.toReal_rpow]
  exact congrArg (fun y : ℝ ↦ a * y) (Real.rpow_natCast x.toReal 2)

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: real infinite weighted dyadic energy bound. -/
lemma aux_weighted_dyadic_energy_toReal_bound
    (σ : ℝ) (hσ : 0 < σ)
    (f : ℝ → ℂ) (hf : MemLp f (2 : ℝ≥0∞) volume) :
    ∑' k : ℕ,
      (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) *
        (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume).toReal ^ 2 ≤
      (2 : ℝ) ^ (3 * σ) *
        (sobolevNorm σ (hf.toLp f)).toReal ^ 2 := by
  let S : ℝ≥0∞ := sobolevNorm σ (hf.toLp f)
  have hSlt : S < ∞ := by
    dsimp [S]
    exact aux_sobolevNorm_lt_top σ hσ.le (hf.toLp f)
  have hRne : ENNReal.ofReal ((2 : ℝ) ^ (3 * σ)) * S ^ (2 : ℝ) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hSlt.ne)
  have htermne (k : ℕ) :
      ENNReal.ofReal ((2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ))) *
        (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume) ^ (2 : ℝ) ≠ ∞ := by
    have hPk : MemLp (P (k + 1) f) (2 : ℝ≥0∞) volume :=
      aux_memLp_P_succ f hf k
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hPk.eLpNorm_lt_top.ne)
  have hbound := aux_weighted_dyadic_energy_ennreal_bound σ hσ f hf
  have hreal :
      (∑' k : ℕ,
        ENNReal.ofReal ((2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ))) *
          (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume) ^ (2 : ℝ)).toReal ≤
        (ENNReal.ofReal ((2 : ℝ) ^ (3 * σ)) * S ^ (2 : ℝ)).toReal :=
    ENNReal.toReal_mono hRne hbound
  have htermReal (k : ℕ) :
      (ENNReal.ofReal ((2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ))) *
        (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume) ^ (2 : ℝ)).toReal =
        (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) *
          (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume).toReal ^ 2 :=
    aux_toReal_ofReal_mul_rpow_two _ (Real.rpow_nonneg (by norm_num) _) _
  rw [ENNReal.tsum_toReal_eq htermne] at hreal
  simp_rw [htermReal] at hreal
  rw [aux_toReal_ofReal_mul_rpow_two _ (Real.rpow_nonneg (by norm_num) _) S] at hreal
  exact hreal

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: finite weighted dyadic energy bound for later summation. -/
lemma aux_weighted_dyadic_energy_partial_sum_bound
    (σ : ℝ) (hσ : 0 < σ)
    (f : ℝ → ℂ) (hf : MemLp f (2 : ℝ≥0∞) volume) (N : ℕ) :
    ∑ k ∈ Finset.range N,
      (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) *
        (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume).toReal ^ 2 ≤
      (2 : ℝ) ^ (3 * σ) *
        (sobolevNorm σ (hf.toLp f)).toReal ^ 2 := by
  let S : ℝ≥0∞ := sobolevNorm σ (hf.toLp f)
  have hSlt : S < ∞ := by
    dsimp [S]
    exact aux_sobolevNorm_lt_top σ hσ.le (hf.toLp f)
  have hRne : ENNReal.ofReal ((2 : ℝ) ^ (3 * σ)) * S ^ (2 : ℝ) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hSlt.ne)
  have htermne (k : ℕ) :
      ENNReal.ofReal ((2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ))) *
        (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume) ^ (2 : ℝ) ≠ ∞ := by
    have hPk : MemLp (P (k + 1) f) (2 : ℝ≥0∞) volume :=
      aux_memLp_P_succ f hf k
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hPk.eLpNorm_lt_top.ne)
  have hbound := aux_weighted_dyadic_energy_ennreal_bound σ hσ f hf
  have hfullne :
      (∑' k : ℕ,
        ENNReal.ofReal ((2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ))) *
          (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume) ^ (2 : ℝ)) ≠ ∞ :=
    ne_top_of_le_ne_top hRne hbound
  have htermReal (k : ℕ) :
      (ENNReal.ofReal ((2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ))) *
        (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume) ^ (2 : ℝ)).toReal =
        (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) *
          (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume).toReal ^ 2 :=
    aux_toReal_ofReal_mul_rpow_two _ (Real.rpow_nonneg (by norm_num) _) _
  calc
    ∑ k ∈ Finset.range N,
        (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) *
          (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume).toReal ^ 2 =
        (∑ k ∈ Finset.range N,
          ENNReal.ofReal ((2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ))) *
            (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume) ^ (2 : ℝ)).toReal := by
      rw [ENNReal.toReal_sum (fun k hk ↦ htermne k)]
      simp_rw [htermReal]
    _ ≤ (∑' k : ℕ,
        ENNReal.ofReal ((2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ))) *
          (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume) ^ (2 : ℝ)).toReal :=
      ENNReal.toReal_mono hfullne (ENNReal.sum_le_tsum _)
    _ ≤ (ENNReal.ofReal ((2 : ℝ) ^ (3 * σ)) * S ^ (2 : ℝ)).toReal :=
      ENNReal.toReal_mono hRne hbound
    _ = (2 : ℝ) ^ (3 * σ) * S.toReal ^ 2 :=
      aux_toReal_ofReal_mul_rpow_two _ (Real.rpow_nonneg (by norm_num) _) S

/-- Auxiliary for \label{lem:weighted-dyadic-square} and `weightedDyadicSquareEstimate`: summability of the weighted dyadic energy sequence. -/
lemma aux_weighted_dyadic_energy_summable
    (σ : ℝ) (hσ : 0 < σ)
    (f : ℝ → ℂ) (hf : MemLp f (2 : ℝ≥0∞) volume) :
    Summable (fun k : ℕ ↦
      (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) *
        (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume).toReal ^ 2) := by
  apply summable_of_sum_range_le
  · intro k
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (sq_nonneg _)
  · intro N
    exact aux_weighted_dyadic_energy_partial_sum_bound σ hσ f hf N

/--
Let \(0<\sigma\leq1\).  For every \(f\in L^2(\mathbb R)\),
\[
\lVert P_0f\rVert_2\leq5^{\sigma/2}\lVert f\rVert_{H^{-\sigma}},
\]
\[
\sum_{k=1}^\infty2^{-2\sigma k}\lVert P_kf\rVert_2^2
\leq3\cdot2^{3\sigma}\lVert f\rVert_{H^{-\sigma}}^2.
\]
-/
theorem weightedDyadicSquareEstimate
    (σ : ℝ) (hσ_pos : 0 < σ) (hσ_le_one : σ ≤ 1)
    (f : ℝ → ℂ) (hf_memLp : MemLp f (2 : ℝ≥0∞) volume) :
    (eLpNorm (P 0 f) (2 : ℝ≥0∞) volume).toReal ≤
      (5 : ℝ) ^ (σ / 2) * (sobolevNorm σ (hf_memLp.toLp f)).toReal ∧
      ∑' k : ℕ,
        (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) *
          (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume).toReal ^ 2 ≤
        3 * (2 : ℝ) ^ (3 * σ) *
          (sobolevNorm σ (hf_memLp.toLp f)).toReal ^ 2 := by
  refine ⟨aux_low_projection_estimate σ hσ_pos.le f hf_memLp, ?_⟩
  calc
    ∑' k : ℕ,
        (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) *
          (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume).toReal ^ 2 ≤
        (2 : ℝ) ^ (3 * σ) *
          (sobolevNorm σ (hf_memLp.toLp f)).toReal ^ 2 :=
      aux_weighted_dyadic_energy_toReal_bound σ hσ_pos f hf_memLp
    _ ≤ 3 * (2 : ℝ) ^ (3 * σ) *
          (sobolevNorm σ (hf_memLp.toLp f)).toReal ^ 2 := by
      have hC : 0 ≤ (2 : ℝ) ^ (3 * σ) := Real.rpow_nonneg (by norm_num) _
      have hS : 0 ≤ (sobolevNorm σ (hf_memLp.toLp f)).toReal ^ 2 := sq_nonneg _
      nlinarith

/--
The exponent \(\sigma_{\mathrm B}=2^{-14}\) in
\(\label{lem:geometric-summation}\), shared with the Sobolev exponent in
\(\label{thm:main}\).
-/
def aux_bourgainSmoothingExponent : ℝ :=
  (2 : ℝ) ^ (-14 : ℤ)

/--
Set \(\sigma_{\mathrm B}:=2^{-14}\).  Then
\[
\left(
\frac{3\cdot2^{3\sigma_{\mathrm B}}}
{2^{2\sigma_{\mathrm B}}-1}
\right)^{1/2}
\leq2^8.
\]
-/
theorem geometricSummationConstant :
    (3 * (2 : ℝ) ^ (3 * aux_bourgainSmoothingExponent) /
        ((2 : ℝ) ^ (2 * aux_bourgainSmoothingExponent) - 1)) ^
          (1 / (2 : ℝ)) ≤
      (2 : ℝ) ^ 8 := by
  have hσ : aux_bourgainSmoothingExponent = (1 : ℝ) / 16384 := by
    norm_num [aux_bourgainSmoothingExponent]
  have htwoσ : 2 * aux_bourgainSmoothingExponent = (1 : ℝ) / 8192 := by
    norm_num [aux_bourgainSmoothingExponent]
  have hthreeσ : 3 * aux_bourgainSmoothingExponent ≤ (1 : ℝ) / 3 := by
    norm_num [aux_bourgainSmoothingExponent]
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
    apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)).mpr
    calc
      Real.exp ((1 : ℝ) / 2) ≤
          (2 + (1 : ℝ) / 2) / (2 - (1 : ℝ) / 2) :=
        Real.exp_le_two_add_div_two_sub (by norm_num) (by norm_num)
      _ ≤ 2 := by norm_num
  have hnumroot : (2 : ℝ) ^ ((1 : ℝ) / 3) ≤ (4 : ℝ) / 3 := by
    apply (Real.rpow_le_rpow_iff
      (Real.rpow_nonneg (by norm_num) _) (by norm_num) (by norm_num : (0 : ℝ) < 3)).mp
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [Real.rpow_natCast]
  have hnum : (2 : ℝ) ^ (3 * aux_bourgainSmoothingExponent) ≤ (4 : ℝ) / 3 :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hthreeσ).trans hnumroot
  have harg : (1 : ℝ) / 16384 ≤
      Real.log 2 * (2 * aux_bourgainSmoothingExponent) := by
    rw [htwoσ]
    nlinarith
  have hdenplus : 1 + (1 : ℝ) / 16384 ≤
      (2 : ℝ) ^ (2 * aux_bourgainSmoothingExponent) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      1 + (1 : ℝ) / 16384 ≤ Real.exp ((1 : ℝ) / 16384) := by
        nlinarith [Real.add_one_le_exp ((1 : ℝ) / 16384)]
      _ ≤ Real.exp (Real.log 2 * (2 * aux_bourgainSmoothingExponent)) :=
        (Real.exp_le_exp.mpr harg)
  have hden : (1 : ℝ) / 16384 ≤
      (2 : ℝ) ^ (2 * aux_bourgainSmoothingExponent) - 1 := by
    linarith
  have hdenpos : 0 <
      (2 : ℝ) ^ (2 * aux_bourgainSmoothingExponent) - 1 :=
    lt_of_lt_of_le (by norm_num) hden
  have hratio :
      3 * (2 : ℝ) ^ (3 * aux_bourgainSmoothingExponent) /
        ((2 : ℝ) ^ (2 * aux_bourgainSmoothingExponent) - 1) ≤
        (2 : ℝ) ^ (16 : ℕ) := by
    apply (div_le_iff₀ hdenpos).mpr
    calc
      3 * (2 : ℝ) ^ (3 * aux_bourgainSmoothingExponent) ≤ 3 * ((4 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_left hnum (by norm_num)
      _ = 4 := by norm_num
      _ = (2 : ℝ) ^ (16 : ℕ) * ((1 : ℝ) / 16384) := by norm_num
      _ ≤ (2 : ℝ) ^ (16 : ℕ) *
          ((2 : ℝ) ^ (2 * aux_bourgainSmoothingExponent) - 1) :=
        mul_le_mul_of_nonneg_left hden (by positivity)
  have hratio_nonneg : 0 ≤
      3 * (2 : ℝ) ^ (3 * aux_bourgainSmoothingExponent) /
        ((2 : ℝ) ^ (2 * aux_bourgainSmoothingExponent) - 1) := by
    positivity
  calc
    (3 * (2 : ℝ) ^ (3 * aux_bourgainSmoothingExponent) /
        ((2 : ℝ) ^ (2 * aux_bourgainSmoothingExponent) - 1)) ^
          (1 / (2 : ℝ)) ≤ ((2 : ℝ) ^ (16 : ℕ)) ^ (1 / (2 : ℝ)) :=
      Real.rpow_le_rpow hratio_nonneg hratio (by norm_num)
    _ = (2 : ℝ) ^ 8 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num

/--
The unmaximized size expression in \(\label{thm:main}\).

This auxiliary definition records the exact sum occurring in the source
constant and is used by `C_bourgainTrilinearSmoothing` and
`bourgainTrilinearSmoothing`.
-/
def aux_mainSize (K : Set ℝ) (χ : ℝ → ℝ) : ℝ :=
  2 + intervalLength K + supportRadius χ ^ 2 +
    (eLpNorm χ 1 volume).toReal + (eLpNorm χ 2 volume).toReal +
      (eLpNorm (deriv χ) 1 volume).toReal +
        (eLpNorm (deriv χ) 2 volume).toReal

/--
For \(K=[a,b]\), write
\[
\Sigma_{K,\chi}:=
2+|K|+R_\chi^2+\lVert\chi\rVert_1+\lVert\chi\rVert_2
+\lVert\chi'\rVert_1+\lVert\chi'\rVert_2.
\]
Then the interaction size from \(\label{def:main-interaction-data}\) obeys
\[
\mathcal S(A_0,A_1,A_2,J_\chi;\chi)
\leq2^2\Sigma_{K,\chi}.
\]
The right-hand side is `aux_mainSize (Set.Icc a b) χ`, the exact size
expression used by the main-theorem constant.
-/
theorem interactionSizeComparison
    (a b : ℝ) (χ : ℝ → ℝ) (hab : a ≤ b)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1) :
    sizeParameter ![
      aux_mainInteractionA0 a b,
      aux_mainInteractionA1 a b χ,
      aux_mainInteractionA2 a b χ,
      aux_mainInteractionJ χ] χ ≤
      (2 : ℝ) ^ 2 * aux_mainSize (Set.Icc a b) χ := by
  let L : ℝ := intervalLength (Set.Icc a b)
  let R : ℝ := supportRadius χ
  let N₁ : ℝ := (eLpNorm χ 1 volume).toReal
  let N₂ : ℝ := (eLpNorm χ 2 volume).toReal
  let D₁ : ℝ := (eLpNorm (deriv χ) 1 volume).toReal
  let D₂ : ℝ := (eLpNorm (deriv χ) 2 volume).toReal
  let M : ℝ := aux_mainSize (Set.Icc a b) χ
  let I : Fin 4 → Set ℝ := ![
    aux_mainInteractionA0 a b,
    aux_mainInteractionA1 a b χ,
    aux_mainInteractionA2 a b χ,
    aux_mainInteractionJ χ]
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact ENNReal.toReal_nonneg
  have hR1 : 1 ≤ R := by
    simpa [R] using aux_u3_one_le_supportRadius χ hχ_compact
  have hR0 : 0 ≤ R := by linarith
  have hRleSq : R ≤ R ^ 2 := by
    have hprod : 0 ≤ R * (R - 1) :=
      mul_nonneg hR0 (sub_nonneg.mpr hR1)
    nlinarith
  have hN₁0 : 0 ≤ N₁ := by
    dsimp [N₁]
    exact ENNReal.toReal_nonneg
  have hN₂0 : 0 ≤ N₂ := by
    dsimp [N₂]
    exact ENNReal.toReal_nonneg
  have hD₁0 : 0 ≤ D₁ := by
    dsimp [D₁]
    exact ENNReal.toReal_nonneg
  have hD₂0 : 0 ≤ D₂ := by
    dsimp [D₂]
    exact ENNReal.toReal_nonneg
  have hMexpand : M = 2 + L + R ^ 2 + N₁ + N₂ + D₁ + D₂ := by
    rfl
  have hMbase : 2 + L + R ^ 2 ≤ M := by
    rw [hMexpand]
    linarith
  have hMtwo : 2 ≤ M := by
    rw [hMexpand]
    nlinarith [sq_nonneg R]
  have hMnonneg : 0 ≤ M := by linarith
  have hMleTwoM : M ≤ 2 * M := by linarith
  have hRsqleM : R ^ 2 ≤ M := by
    rw [hMexpand]
    nlinarith [sq_nonneg R]
  have hN₁leM : N₁ ≤ M := by
    rw [hMexpand]
    nlinarith [sq_nonneg R]
  have hN₂leM : N₂ ≤ M := by
    rw [hMexpand]
    nlinarith [sq_nonneg R]
  have hD₁leM : D₁ ≤ M := by
    rw [hMexpand]
    nlinarith [sq_nonneg R]
  have hD₂leM : D₂ ≤ M := by
    rw [hMexpand]
    nlinarith [sq_nonneg R]
  have hIcc : ∀ u v : ℝ, u ≤ v → intervalLength (Set.Icc u v) = v - u := by
    intro u v huv
    unfold intervalLength
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr huv)]
  have hA₀len : intervalLength (aux_mainInteractionA0 a b) = L + 2 := by
    rw [aux_mainInteractionA0, hIcc (a - 1) (b + 1) (by linarith)]
    dsimp [L]
    rw [hIcc a b hab]
    ring
  have hA₁len : intervalLength (aux_mainInteractionA1 a b χ) = L + 2 * R + 2 := by
    have hI₁order : a - R ≤ b + R := by linarith
    have hadd : intervalLength (aux_mainInteractionA1 a b χ) =
        intervalLength (Set.Icc (a - R) (b + R)) +
          intervalLength (Set.Icc (-1 : ℝ) 1) := by
      simpa [aux_mainInteractionA1, aux_mainInteractionI1, R] using
        intervalAdd (a - supportRadius χ) (b + supportRadius χ) (-1) 1
          (by simpa [R] using hI₁order) (by norm_num)
    have hI₁ : intervalLength (Set.Icc (a - R) (b + R)) = L + 2 * R := by
      rw [hIcc (a - R) (b + R) hI₁order]
      dsimp [L]
      rw [hIcc a b hab]
      ring
    have hunit : intervalLength (Set.Icc (-1 : ℝ) 1) = 2 := by
      calc
        intervalLength (Set.Icc (-1 : ℝ) 1) = 1 - (-1) := hIcc (-1) 1 (by norm_num)
        _ = 2 := by ring
    calc
      intervalLength (aux_mainInteractionA1 a b χ) =
          intervalLength (Set.Icc (a - R) (b + R)) +
            intervalLength (Set.Icc (-1 : ℝ) 1) := by
        exact hadd
      _ = L + 2 * R + 2 := by rw [hI₁, hunit]
  have hA₂len : intervalLength (aux_mainInteractionA2 a b χ) = L + R ^ 2 + 2 := by
    have hI₂order : a ≤ b + R ^ 2 := by
      nlinarith [sq_nonneg R]
    have hadd : intervalLength (aux_mainInteractionA2 a b χ) =
        intervalLength (Set.Icc a (b + R ^ 2)) +
          intervalLength (Set.Icc (-1 : ℝ) 1) := by
      simpa [aux_mainInteractionA2, aux_mainInteractionI2, R] using
        intervalAdd a (b + supportRadius χ ^ 2) (-1) 1
          (by simpa [R] using hI₂order) (by norm_num)
    have hI₂ : intervalLength (Set.Icc a (b + R ^ 2)) = L + R ^ 2 := by
      rw [hIcc a (b + R ^ 2) hI₂order]
      dsimp [L]
      rw [hIcc a b hab]
      ring
    have hunit : intervalLength (Set.Icc (-1 : ℝ) 1) = 2 := by
      calc
        intervalLength (Set.Icc (-1 : ℝ) 1) = 1 - (-1) := hIcc (-1) 1 (by norm_num)
        _ = 2 := by ring
    calc
      intervalLength (aux_mainInteractionA2 a b χ) =
          intervalLength (Set.Icc a (b + R ^ 2)) +
            intervalLength (Set.Icc (-1 : ℝ) 1) := by
        exact hadd
      _ = L + R ^ 2 + 2 := by rw [hI₂, hunit]
  have hJlen : intervalLength (aux_mainInteractionJ χ) = 2 * R := by
    change intervalLength (Set.Icc (-R) R) = 2 * R
    rw [hIcc (-R) R (by linarith)]
    ring
  have hA₀bound : intervalLength (aux_mainInteractionA0 a b) ≤ 2 * M := by
    rw [hA₀len]
    nlinarith [hMbase, sq_nonneg R]
  have hA₁bound : intervalLength (aux_mainInteractionA1 a b χ) ≤ 2 * M := by
    rw [hA₁len]
    nlinarith [hMbase]
  have hA₂bound : intervalLength (aux_mainInteractionA2 a b χ) ≤ 2 * M := by
    rw [hA₂len]
    nlinarith [hMbase]
  have hJbound : intervalLength (aux_mainInteractionJ χ) ≤ 2 * M := by
    rw [hJlen]
    nlinarith [hMbase]
  have hsup : sSup (Set.range fun i ↦ intervalLength (I i)) ≤ 2 * M := by
    apply csSup_le
    · exact ⟨intervalLength (I 0), ⟨0, rfl⟩⟩
    · intro x hx
      rcases hx with ⟨i, rfl⟩
      fin_cases i
      · simpa [I] using hA₀bound
      · simpa [I] using hA₁bound
      · simpa [I] using hA₂bound
      · simpa [I] using hJbound
  have hother : max (R ^ 2) (max N₁ (max N₂ (max D₁ D₂))) ≤ 2 * M := by
    apply max_le
    · exact hRsqleM.trans hMleTwoM
    · apply max_le
      · exact hN₁leM.trans hMleTwoM
      · apply max_le
        · exact hN₂leM.trans hMleTwoM
        · apply max_le
          · exact hD₁leM.trans hMleTwoM
          · exact hD₂leM.trans hMleTwoM
  have hmax : max (sSup (Set.range fun i ↦ intervalLength (I i)))
      (max (R ^ 2) (max N₁ (max N₂ (max D₁ D₂)))) ≤ 2 * M :=
    max_le hsup hother
  change 2 + max (sSup (Set.range fun i ↦ intervalLength (I i)))
      (max (R ^ 2) (max N₁ (max N₂ (max D₁ D₂)))) ≤ (2 : ℝ) ^ 2 * M
  nlinarith


/-- Auxiliary for `bourgainTrilinearSmoothing` (`\label{thm:main}`): compares
the dyadic smoothing constant to the main size expression. -/
theorem aux_main_dyadic_constant_bound
    (a b : ℝ) (χ : ℝ → ℝ) (hab : a ≤ b)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1) :
    C_dyadicL2Smoothing a b χ ≤
      (2 : ℝ) ^ 14 * aux_mainSize (Set.Icc a b) χ ^ 2 := by
  let I : ℝ := sizeParameter ![
    aux_mainInteractionA0 a b,
    aux_mainInteractionA1 a b χ,
    aux_mainInteractionA2 a b χ,
    aux_mainInteractionJ χ] χ
  let S : ℝ := aux_mainSize (Set.Icc a b) χ
  have hI : I ≤ (2 : ℝ) ^ 2 * S := by
    simpa only [I, S] using interactionSizeComparison a b χ hab hχ_smooth hχ_compact
      hχ_nonneg hχ_le_one
  have hI0 : 0 ≤ I := by
    have htwo := aux_two_le_sizeParameter_four
      (aux_mainInteractionA0 a b) (aux_mainInteractionA1 a b χ)
      (aux_mainInteractionA2 a b χ) (aux_mainInteractionJ χ) χ
    dsimp only [I]
    linarith
  have hS0 : 0 ≤ S := by
    unfold S aux_mainSize intervalLength
    have hvol : 0 ≤ (volume (Set.Icc a b)).toReal := ENNReal.toReal_nonneg
    have hrad : 0 ≤ supportRadius χ ^ 2 := sq_nonneg _
    have hχ₁ : 0 ≤ (eLpNorm χ 1 volume).toReal := ENNReal.toReal_nonneg
    have hχ₂ : 0 ≤ (eLpNorm χ 2 volume).toReal := ENNReal.toReal_nonneg
    have hdχ₁ : 0 ≤ (eLpNorm (deriv χ) 1 volume).toReal := ENNReal.toReal_nonneg
    have hdχ₂ : 0 ≤ (eLpNorm (deriv χ) 2 volume).toReal := ENNReal.toReal_nonneg
    linarith
  have hIsq : I ^ 2 ≤ ((2 : ℝ) ^ 2 * S) ^ 2 :=
    (sq_le_sq₀ hI0 (by positivity)).mpr hI
  unfold C_dyadicL2Smoothing
  change (2 : ℝ) ^ 10 * I ^ 2 ≤ (2 : ℝ) ^ 14 * S ^ 2
  calc
    (2 : ℝ) ^ 10 * I ^ 2 ≤ (2 : ℝ) ^ 10 * ((2 : ℝ) ^ 2 * S) ^ 2 :=
      mul_le_mul_of_nonneg_left hIsq (by positivity)
    _ = (2 : ℝ) ^ 14 * S ^ 2 := by ring

/-- Auxiliary for `bourgainTrilinearSmoothing` (`\label{thm:main}`):
normalizes the dyadic decay exponent to the Sobolev exponent. -/
theorem aux_main_dyadic_exponent (k : ℕ) :
    -((2 : ℝ) ^ (-13 : ℝ)) * ((k + 1 : ℕ) : ℝ) =
      -2 * aux_bourgainSmoothingExponent * ((k + 1 : ℕ) : ℝ) := by
  norm_num [aux_bourgainSmoothingExponent]

/-- Auxiliary for `bourgainTrilinearSmoothing` (`\label{thm:main}`): bounds
one positive dyadic frequency contribution. -/
theorem aux_main_high_frequency_term_bound
    (a b : ℝ) (χ : ℝ → ℝ) (hab : a ≤ b)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (f₀ f₁ f₂ : ℝ → ℂ)
    (hf₀ : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁ : MemLp f₁ (2 : ℝ≥0∞) volume)
    (hf₂ : MemLp f₂ (2 : ℝ≥0∞) volume)
    (hf₀_support : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f₀ x = 0)
    (k : ℕ) :
    trilinearFormAbs χ f₀ f₁ (P (k + 1) f₂) ≤
      (2 : ℝ) ^ 14 * aux_mainSize (Set.Icc a b) χ ^ 2 *
        (2 : ℝ) ^ (-2 * aux_bourgainSmoothingExponent * ((k + 1 : ℕ) : ℝ)) *
          (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
            (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal *
              (eLpNorm (P (k + 1) f₂) (2 : ℝ≥0∞) volume).toReal := by
  have hQP := (dyadicReconstructionAndMultiplierBounds f₂ hf₂).2.2.1 (k + 1) (by omega)
  have hdyadic := dyadicL2Smoothing a b χ hab hχ_smooth hχ_compact hχ_nonneg hχ_le_one
    (k + 1) (by omega) f₀ f₁ (P (k + 1) f₂) hf₀ hf₁
      (aux_memLp_P_succ f₂ hf₂ k) hf₀_support
  calc
    trilinearFormAbs χ f₀ f₁ (P (k + 1) f₂) =
        trilinearFormAbs χ f₀ f₁ (Q (k + 1) (P (k + 1) f₂)) := by
      rw [hQP]
    _ ≤ C_dyadicL2Smoothing a b χ *
          (2 : ℝ) ^ (-((2 : ℝ) ^ (-13 : ℝ)) * ((k + 1 : ℕ) : ℝ)) *
            (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
              (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal *
                (eLpNorm (P (k + 1) f₂) (2 : ℝ≥0∞) volume).toReal := hdyadic
    _ ≤ (2 : ℝ) ^ 14 * aux_mainSize (Set.Icc a b) χ ^ 2 *
          (2 : ℝ) ^ (-((2 : ℝ) ^ (-13 : ℝ)) * ((k + 1 : ℕ) : ℝ)) *
            (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
              (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal *
                (eLpNorm (P (k + 1) f₂) (2 : ℝ≥0∞) volume).toReal := by
      gcongr
      exact aux_main_dyadic_constant_bound a b χ hab hχ_smooth hχ_compact
        hχ_nonneg hχ_le_one
    _ = (2 : ℝ) ^ 14 * aux_mainSize (Set.Icc a b) χ ^ 2 *
        (2 : ℝ) ^ (-2 * aux_bourgainSmoothingExponent * ((k + 1 : ℕ) : ℝ)) *
          (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
            (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal *
              (eLpNorm (P (k + 1) f₂) (2 : ℝ≥0∞) volume).toReal := by
      rw [aux_main_dyadic_exponent]

/-- Auxiliary for `bourgainTrilinearSmoothing` (`\label{thm:main}`): the
finite weighted Cauchy--Schwarz inequality used to sum dyadic pieces. -/
theorem aux_main_weighted_cauchy
    (σ : ℝ) (p : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N,
      (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) * p k ≤
      Real.sqrt (∑ k ∈ Finset.range N,
        (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) * p k ^ 2) *
        Real.sqrt (∑ k ∈ Finset.range N,
          (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) ) := by
  let u : ℕ → ℝ := fun k ↦
    (2 : ℝ) ^ (-σ * ((k + 1 : ℕ) : ℝ)) * p k
  let v : ℕ → ℝ := fun k ↦
    (2 : ℝ) ^ (-σ * ((k + 1 : ℕ) : ℝ))
  have huv (k : ℕ) : u k * v k =
      (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) * p k := by
    dsimp only [u, v]
    calc
      (2 : ℝ) ^ (-σ * ((k + 1 : ℕ) : ℝ)) * p k *
          (2 : ℝ) ^ (-σ * ((k + 1 : ℕ) : ℝ)) =
          (2 : ℝ) ^ (-σ * ((k + 1 : ℕ) : ℝ)) *
            (2 : ℝ) ^ (-σ * ((k + 1 : ℕ) : ℝ)) * p k := by ring
      _ = (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) * p k := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
  have hu2 (k : ℕ) : u k ^ 2 =
      (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) * p k ^ 2 := by
    dsimp only [u]
    rw [mul_pow]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hv2 (k : ℕ) : v k ^ 2 =
      (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) := by
    dsimp only [v]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [show (∑ k ∈ Finset.range N,
      (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) * p k) =
      ∑ k ∈ Finset.range N, u k * v k by
        apply Finset.sum_congr rfl
        intro k hk
        exact (huv k).symm]
  rw [show (∑ k ∈ Finset.range N,
      (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) * p k ^ 2) =
      ∑ k ∈ Finset.range N, u k ^ 2 by
        apply Finset.sum_congr rfl
        intro k hk
        exact (hu2 k).symm]
  rw [show (∑ k ∈ Finset.range N,
      (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ))) =
      ∑ k ∈ Finset.range N, v k ^ 2 by
        apply Finset.sum_congr rfl
        intro k hk
        exact (hv2 k).symm]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- Auxiliary for `bourgainTrilinearSmoothing` (`\label{thm:main}`): bounds
the finite geometric factor in the high-frequency Cauchy--Schwarz step. -/
theorem aux_main_geometric_partial_sum
    (σ : ℝ) (hσ : 0 < σ) (N : ℕ) :
    ∑ k ∈ Finset.range N,
      (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) ≤
        ((2 : ℝ) ^ (2 * σ) - 1)⁻¹ := by
  let q : ℝ := (2 : ℝ) ^ (-2 * σ)
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hqlt : q < 1 := by
    dsimp only [q]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    nlinarith
  have hgeom : ∑ k ∈ Finset.range N, q ^ (k + 1) ≤ q * (1 - q)⁻¹ := by
    rw [show (∑ k ∈ Finset.range N, q ^ (k + 1)) =
      q * ∑ k ∈ Finset.range N, q ^ k by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [pow_succ]
        ring]
    have hne : q ≠ 1 := ne_of_lt hqlt
    rw [geom_sum_eq hne]
    rw [div_eq_mul_inv]
    rw [show (q ^ N - 1) * (q - 1)⁻¹ =
      (1 - q ^ N) * (1 - q)⁻¹ by field_simp; ring]
    calc
      q * ((1 - q ^ N) * (1 - q)⁻¹) ≤ q * (1 * (1 - q)⁻¹) := by
        gcongr
        exact sub_le_self _ (pow_nonneg hq0 _)
      _ = q * (1 - q)⁻¹ := by ring
  have hterm (k : ℕ) :
      (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) = q ^ (k + 1) := by
    dsimp only [q]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show (∑ k ∈ Finset.range N,
      (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ))) =
      ∑ k ∈ Finset.range N, q ^ (k + 1) by
        apply Finset.sum_congr rfl
        intro k hk
        exact hterm k]
  calc
    ∑ k ∈ Finset.range N, q ^ (k + 1) ≤ q * (1 - q)⁻¹ := hgeom
    _ = ((2 : ℝ) ^ (2 * σ) - 1)⁻¹ := by
      let A : ℝ := (2 : ℝ) ^ (2 * σ)
      have hA : 1 < A := by
        dsimp only [A]
        exact Real.one_lt_rpow (by norm_num) (by positivity)
      have hq : q = A⁻¹ := by
        dsimp only [q, A]
        rw [show -2 * σ = -(2 * σ) by ring]
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hq]
      field_simp
      ring

/-- Auxiliary for `bourgainTrilinearSmoothing` (`\label{thm:main}`): sums
the weighted scalar dyadic norms over a finite range. -/
theorem aux_main_high_frequency_weighted_sum
    (f : ℝ → ℂ) (H : ℝ) (hH : 0 ≤ H) (N : ℕ)
    (hEnergy : ∑ k ∈ Finset.range N,
      (2 : ℝ) ^ (-2 * aux_bourgainSmoothingExponent * ((k + 1 : ℕ) : ℝ)) *
        (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume).toReal ^ 2 ≤
      3 * (2 : ℝ) ^ (3 * aux_bourgainSmoothingExponent) * H ^ 2) :
    ∑ k ∈ Finset.range N,
      (2 : ℝ) ^ (-2 * aux_bourgainSmoothingExponent * ((k + 1 : ℕ) : ℝ)) *
        (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume).toReal ≤
      (2 : ℝ) ^ 8 * H := by
  let C : ℝ := 3 * (2 : ℝ) ^ (3 * aux_bourgainSmoothingExponent)
  let D : ℝ := (2 : ℝ) ^ (2 * aux_bourgainSmoothingExponent) - 1
  let E : ℝ := ∑ k ∈ Finset.range N,
    (2 : ℝ) ^ (-2 * aux_bourgainSmoothingExponent * ((k + 1 : ℕ) : ℝ)) *
      (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume).toReal ^ 2
  let G : ℝ := ∑ k ∈ Finset.range N,
    (2 : ℝ) ^ (-2 * aux_bourgainSmoothingExponent * ((k + 1 : ℕ) : ℝ))
  have hσ : 0 < aux_bourgainSmoothingExponent := by
    norm_num [aux_bourgainSmoothingExponent]
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hE : E ≤ C * H ^ 2 := by
    simpa only [E, C] using hEnergy
  have hG : G ≤ D⁻¹ := by
    simpa only [G, D] using
      aux_main_geometric_partial_sum aux_bourgainSmoothingExponent hσ N
  have hCS := aux_main_weighted_cauchy aux_bourgainSmoothingExponent
    (fun k ↦ (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume).toReal) N
  change _ ≤ _
  calc
    ∑ k ∈ Finset.range N,
        (2 : ℝ) ^ (-2 * aux_bourgainSmoothingExponent * ((k + 1 : ℕ) : ℝ)) *
          (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume).toReal ≤
        Real.sqrt E * Real.sqrt G := by
      simpa only [E, G] using hCS
    _ ≤ Real.sqrt (C * H ^ 2) * Real.sqrt D⁻¹ := by
      apply mul_le_mul
      · exact Real.sqrt_le_sqrt hE
      · exact Real.sqrt_le_sqrt hG
      · exact Real.sqrt_nonneg _
      · exact Real.sqrt_nonneg _
    _ = (C / D) ^ (1 / (2 : ℝ)) * H := by
      calc
        Real.sqrt (C * H ^ 2) * Real.sqrt D⁻¹ =
            (Real.sqrt C * Real.sqrt (H ^ 2)) * Real.sqrt D⁻¹ := by
          rw [Real.sqrt_mul hC]
        _ = (Real.sqrt C * H) * Real.sqrt D⁻¹ := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hH]
        _ = H * (Real.sqrt C * Real.sqrt D⁻¹) := by ring
        _ = H * Real.sqrt (C * D⁻¹) := by rw [← Real.sqrt_mul hC]
        _ = H * (C * D⁻¹) ^ (1 / (2 : ℝ)) := by
          rw [← Real.sqrt_eq_rpow]
        _ = (C / D) ^ (1 / (2 : ℝ)) * H := by
          rw [div_eq_mul_inv]
          ring
    _ ≤ (2 : ℝ) ^ 8 * H := by
      apply mul_le_mul_of_nonneg_right geometricSummationConstant hH

/-- Auxiliary for `bourgainTrilinearSmoothing` (`\label{thm:main}`): turns
termwise high-frequency estimates into a finite partial-form estimate. -/
theorem aux_main_high_frequency_partial_bound
    (χ : ℝ → ℝ) (f₀ f₁ f₂ : ℝ → ℂ) (S A B H : ℝ) (N : ℕ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hterm : ∀ k : ℕ,
      trilinearFormAbs χ f₀ f₁ (P (k + 1) f₂) ≤
        (2 : ℝ) ^ 14 * S ^ 2 *
          (2 : ℝ) ^ (-2 * aux_bourgainSmoothingExponent * ((k + 1 : ℕ) : ℝ)) *
            A * B * (eLpNorm (P (k + 1) f₂) (2 : ℝ≥0∞) volume).toReal)
    (hsum : ∑ k ∈ Finset.range N,
      (2 : ℝ) ^ (-2 * aux_bourgainSmoothingExponent * ((k + 1 : ℕ) : ℝ)) *
        (eLpNorm (P (k + 1) f₂) (2 : ℝ≥0∞) volume).toReal ≤
      (2 : ℝ) ^ 8 * H) :
    ∑ k ∈ Finset.range N, trilinearFormAbs χ f₀ f₁ (P (k + 1) f₂) ≤
      (2 : ℝ) ^ 22 * S ^ 2 * A * B * H := by
  let L : ℝ := (2 : ℝ) ^ 14 * S ^ 2 * A * B
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  calc
    ∑ k ∈ Finset.range N, trilinearFormAbs χ f₀ f₁ (P (k + 1) f₂) ≤
        ∑ k ∈ Finset.range N,
          (2 : ℝ) ^ 14 * S ^ 2 *
            (2 : ℝ) ^ (-2 * aux_bourgainSmoothingExponent * ((k + 1 : ℕ) : ℝ)) *
              A * B * (eLpNorm (P (k + 1) f₂) (2 : ℝ≥0∞) volume).toReal := by
      apply Finset.sum_le_sum
      intro k hk
      exact hterm k
    _ = L * ∑ k ∈ Finset.range N,
        (2 : ℝ) ^ (-2 * aux_bourgainSmoothingExponent * ((k + 1 : ℕ) : ℝ)) *
          (eLpNorm (P (k + 1) f₂) (2 : ℝ≥0∞) volume).toReal := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only [L]
      ring
    _ ≤ L * ((2 : ℝ) ^ 8 * H) :=
      mul_le_mul_of_nonneg_left hsum hL
    _ = (2 : ℝ) ^ 22 * S ^ 2 * A * B * H := by
      dsimp only [L]
      ring

/-- Auxiliary for `bourgainTrilinearSmoothing` (`\label{thm:main}`): the
uniform finite high-frequency partial-form estimate. -/
theorem aux_main_high_frequency_bound
    (a b : ℝ) (χ : ℝ → ℝ) (hab : a ≤ b)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (f₀ f₁ f₂ : ℝ → ℂ)
    (hf₀ : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁ : MemLp f₁ (2 : ℝ≥0∞) volume)
    (hf₂ : MemLp f₂ (2 : ℝ≥0∞) volume)
    (hf₀_support : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f₀ x = 0)
    (N : ℕ) :
    ∑ k ∈ Finset.range N, trilinearFormAbs χ f₀ f₁ (P (k + 1) f₂) ≤
      (2 : ℝ) ^ 22 * aux_mainSize (Set.Icc a b) χ ^ 2 *
        (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
          (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal *
            (sobolevNorm aux_bourgainSmoothingExponent (hf₂.toLp f₂)).toReal := by
  let S : ℝ := aux_mainSize (Set.Icc a b) χ
  let A : ℝ := (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal
  let B : ℝ := (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal
  let H : ℝ := (sobolevNorm aux_bourgainSmoothingExponent (hf₂.toLp f₂)).toReal
  have hσ : 0 < aux_bourgainSmoothingExponent := by
    norm_num [aux_bourgainSmoothingExponent]
  have hEnergyStrong := aux_weighted_dyadic_energy_partial_sum_bound
    aux_bourgainSmoothingExponent hσ f₂ hf₂ N
  have hEnergy : ∑ k ∈ Finset.range N,
      (2 : ℝ) ^ (-2 * aux_bourgainSmoothingExponent * ((k + 1 : ℕ) : ℝ)) *
        (eLpNorm (P (k + 1) f₂) (2 : ℝ≥0∞) volume).toReal ^ 2 ≤
      3 * (2 : ℝ) ^ (3 * aux_bourgainSmoothingExponent) * H ^ 2 := by
    calc
      ∑ k ∈ Finset.range N,
          (2 : ℝ) ^ (-2 * aux_bourgainSmoothingExponent * ((k + 1 : ℕ) : ℝ)) *
            (eLpNorm (P (k + 1) f₂) (2 : ℝ≥0∞) volume).toReal ^ 2 ≤
          (2 : ℝ) ^ (3 * aux_bourgainSmoothingExponent) * H ^ 2 := by
        simpa only [H] using hEnergyStrong
      _ ≤ 3 * (2 : ℝ) ^ (3 * aux_bourgainSmoothingExponent) * H ^ 2 := by
        have hC : 0 ≤ (2 : ℝ) ^ (3 * aux_bourgainSmoothingExponent) :=
          Real.rpow_nonneg (by norm_num) _
        have hHsq : 0 ≤ H ^ 2 := sq_nonneg _
        nlinarith
  have hsum : ∑ k ∈ Finset.range N,
      (2 : ℝ) ^ (-2 * aux_bourgainSmoothingExponent * ((k + 1 : ℕ) : ℝ)) *
        (eLpNorm (P (k + 1) f₂) (2 : ℝ≥0∞) volume).toReal ≤
      (2 : ℝ) ^ 8 * H :=
    aux_main_high_frequency_weighted_sum f₂ H ENNReal.toReal_nonneg N hEnergy
  have hterm : ∀ k : ℕ,
      trilinearFormAbs χ f₀ f₁ (P (k + 1) f₂) ≤
        (2 : ℝ) ^ 14 * S ^ 2 *
          (2 : ℝ) ^ (-2 * aux_bourgainSmoothingExponent * ((k + 1 : ℕ) : ℝ)) *
            A * B * (eLpNorm (P (k + 1) f₂) (2 : ℝ≥0∞) volume).toReal := by
    intro k
    simpa only [S, A, B] using
      aux_main_high_frequency_term_bound a b χ hab hχ_smooth hχ_compact
        hχ_nonneg hχ_le_one f₀ f₁ f₂ hf₀ hf₁ hf₂ hf₀_support k
  have hpartial := aux_main_high_frequency_partial_bound χ f₀ f₁ f₂ S A B H N
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg hterm hsum
  simpa only [S, A, B, H] using hpartial

/-- Auxiliary scalar bookkeeping for `bourgainTrilinearSmoothing` (`\label{thm:main}`). -/
theorem aux_mainSize_norm_one_le (K : Set ℝ) (χ : ℝ → ℝ) :
    (eLpNorm χ (1 : ℝ≥0∞) volume).toReal ≤ aux_mainSize K χ := by
  unfold aux_mainSize intervalLength
  have hvol : 0 ≤ (volume K).toReal := ENNReal.toReal_nonneg
  have hrad : 0 ≤ supportRadius χ ^ 2 := sq_nonneg _
  have hχ₁ : 0 ≤ (eLpNorm χ 1 volume).toReal := ENNReal.toReal_nonneg
  have hχ₂ : 0 ≤ (eLpNorm χ 2 volume).toReal := ENNReal.toReal_nonneg
  have hdχ₁ : 0 ≤ (eLpNorm (deriv χ) 1 volume).toReal := ENNReal.toReal_nonneg
  have hdχ₂ : 0 ≤ (eLpNorm (deriv χ) 2 volume).toReal := ENNReal.toReal_nonneg
  linarith

/-- Auxiliary scalar bookkeeping for `bourgainTrilinearSmoothing` (`\label{thm:main}`). -/
theorem aux_mainSize_two_le (K : Set ℝ) (χ : ℝ → ℝ) :
    2 ≤ aux_mainSize K χ := by
  unfold aux_mainSize intervalLength
  have hvol : 0 ≤ (volume K).toReal := ENNReal.toReal_nonneg
  have hrad : 0 ≤ supportRadius χ ^ 2 := sq_nonneg _
  have hχ₁ : 0 ≤ (eLpNorm χ 1 volume).toReal := ENNReal.toReal_nonneg
  have hχ₂ : 0 ≤ (eLpNorm χ 2 volume).toReal := ENNReal.toReal_nonneg
  have hdχ₁ : 0 ≤ (eLpNorm (deriv χ) 1 volume).toReal := ENNReal.toReal_nonneg
  have hdχ₂ : 0 ≤ (eLpNorm (deriv χ) 2 volume).toReal := ENNReal.toReal_nonneg
  linarith

/-- Auxiliary numerical constant for the low-frequency contribution to
`bourgainTrilinearSmoothing` (`\label{thm:main}`). -/
theorem aux_main_low_weight_constant :
    (5 : ℝ) ^ (aux_bourgainSmoothingExponent / 2) ≤ 2 := by
  have hσ : aux_bourgainSmoothingExponent / 2 ≤ (1 : ℝ) / 4 := by
    norm_num [aux_bourgainSmoothingExponent]
  calc
    (5 : ℝ) ^ (aux_bourgainSmoothingExponent / 2) ≤
        (5 : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ
    _ ≤ 2 := by
      apply (Real.rpow_le_rpow_iff
        (Real.rpow_nonneg (by norm_num) _) (by norm_num)
        (by norm_num : (0 : ℝ) < 4)).mp
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5)]
      norm_num [Real.rpow_natCast]

/-- Auxiliary low-frequency dyadic estimate for `bourgainTrilinearSmoothing`
(`\label{thm:main}`). -/
theorem aux_main_low_frequency_bound
    (K : Set ℝ) (χ : ℝ → ℝ) (f₀ f₁ f₂ : ℝ → ℂ)
    (hχ_memLp : MemLp χ (1 : ℝ≥0∞) volume)
    (hf₀ : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁ : MemLp f₁ (2 : ℝ≥0∞) volume)
    (hf₂ : MemLp f₂ (2 : ℝ≥0∞) volume) :
    trilinearFormAbs χ f₀ f₁ (P 0 f₂) ≤
      2 * aux_mainSize K χ *
        (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
          (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal *
            (sobolevNorm aux_bourgainSmoothingExponent (hf₂.toLp f₂)).toReal := by
  have hW := (weightedDyadicSquareEstimate aux_bourgainSmoothingExponent
    (by norm_num [aux_bourgainSmoothingExponent])
    (by norm_num [aux_bourgainSmoothingExponent]) f₂ hf₂).1
  have hEndpoint := elementaryL2Endpoint χ f₀ f₁ (P 0 f₂) hχ_memLp hf₀ hf₁
    (aux_memLp_P_zero f₂ hf₂)
  have hP : (eLpNorm (P 0 f₂) (2 : ℝ≥0∞) volume).toReal ≤
      2 * (sobolevNorm aux_bourgainSmoothingExponent (hf₂.toLp f₂)).toReal := by
    calc
      (eLpNorm (P 0 f₂) (2 : ℝ≥0∞) volume).toReal ≤
          (5 : ℝ) ^ (aux_bourgainSmoothingExponent / 2) *
            (sobolevNorm aux_bourgainSmoothingExponent (hf₂.toLp f₂)).toReal := hW
      _ ≤ 2 * (sobolevNorm aux_bourgainSmoothingExponent (hf₂.toLp f₂)).toReal := by
        gcongr
        exact aux_main_low_weight_constant
  have hNχ := aux_mainSize_norm_one_le K χ
  have hS : 0 ≤ aux_mainSize K χ :=
    le_trans (by norm_num) (aux_mainSize_two_le K χ)
  have hA : 0 ≤ (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal := ENNReal.toReal_nonneg
  have hB : 0 ≤ (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal := ENNReal.toReal_nonneg
  have hH : 0 ≤ (sobolevNorm aux_bourgainSmoothingExponent (hf₂.toLp f₂)).toReal :=
    ENNReal.toReal_nonneg
  calc
    trilinearFormAbs χ f₀ f₁ (P 0 f₂) ≤
        (eLpNorm χ (1 : ℝ≥0∞) volume).toReal *
          (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
            (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal *
              (eLpNorm (P 0 f₂) (2 : ℝ≥0∞) volume).toReal := hEndpoint
    _ ≤ aux_mainSize K χ *
          (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
            (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal *
              (2 * (sobolevNorm aux_bourgainSmoothingExponent (hf₂.toLp f₂)).toReal) := by
      gcongr
    _ = 2 * aux_mainSize K χ *
        (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
          (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal *
            (sobolevNorm aux_bourgainSmoothingExponent (hf₂.toLp f₂)).toReal := by ring

theorem aux_main_trilinearForm_dyadic_partial_sum
    (χ : ℝ → ℝ) (f₀ f₁ f₂ : ℝ → ℂ)
    (hχ : Integrable (fun t : ℝ ↦ (χ t : ℂ)))
    (hf₀ : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁ : MemLp f₁ (2 : ℝ≥0∞) volume)
    (hf₂ : MemLp f₂ (2 : ℝ≥0∞) volume) (N : ℕ) :
    trilinearForm χ f₀ f₁
        (fun x ↦ P 0 f₂ x + ∑ k ∈ Finset.range N, P (k + 1) f₂ x) =
      trilinearForm χ f₀ f₁ (P 0 f₂) +
        ∑ k ∈ Finset.range N, trilinearForm χ f₀ f₁ (P (k + 1) f₂) := by
  have hPzero : MemLp (P 0 f₂) (2 : ℝ≥0∞) volume := aux_memLp_P_zero f₂ hf₂
  have hP : ∀ k : ℕ, MemLp (P (k + 1) f₂) (2 : ℝ≥0∞) volume :=
    fun k ↦ aux_memLp_P_succ f₂ hf₂ k
  have hsumMem : ∀ N : ℕ,
      MemLp (fun x ↦ ∑ k ∈ Finset.range N, P (k + 1) f₂ x) (2 : ℝ≥0∞) volume := by
    intro n
    exact memLp_finsetSum (s := Finset.range n)
      (f := fun k ↦ P (k + 1) f₂) (fun k _ ↦ hP k)
  have hInt : ∀ g : ℝ → ℂ, MemLp g (2 : ℝ≥0∞) volume →
      Integrable (aux_u3_trilinearIntegrand f₀ f₁ g χ) (volume.prod volume) := by
    intro g hg
    exact aux_trilinearIntegrand_integrable_l2 χ f₀ f₁ g hχ hf₀ hf₁ hg
  have hsum : ∀ n : ℕ,
      trilinearForm χ f₀ f₁ (fun x ↦ ∑ k ∈ Finset.range n, P (k + 1) f₂ x) =
        ∑ k ∈ Finset.range n, trilinearForm χ f₀ f₁ (P (k + 1) f₂) := by
    intro n
    induction n with
    | zero =>
        simp [trilinearForm]
    | succ n ih =>
        have hfun :
            (fun x ↦ ∑ k ∈ Finset.range (n + 1), P (k + 1) f₂ x) =
              (fun x ↦ ∑ k ∈ Finset.range n, P (k + 1) f₂ x) +
                P (n + 1) f₂ := by
          ext x
          simp [Finset.sum_range_succ]
        rw [hfun, aux_trilinearForm_add_last χ f₀ f₁
          (fun x ↦ ∑ k ∈ Finset.range n, P (k + 1) f₂ x)
          (P (n + 1) f₂) (hInt _ (hsumMem n)) (hInt _ (hP n)), ih,
          Finset.sum_range_succ]
  have hfun :
      (fun x ↦ P 0 f₂ x + ∑ k ∈ Finset.range N, P (k + 1) f₂ x) =
        P 0 f₂ + (fun x ↦ ∑ k ∈ Finset.range N, P (k + 1) f₂ x) := by
    rfl
  rw [hfun, aux_trilinearForm_add_last χ f₀ f₁ (P 0 f₂)
    (fun x ↦ ∑ k ∈ Finset.range N, P (k + 1) f₂ x)
    (hInt _ hPzero) (hInt _ (hsumMem N)), hsum]

/-- Auxiliary for `bourgainTrilinearSmoothing` (`\label{thm:main}`): dyadic finite partial forms converge to the original raw form in `L²`. -/
theorem aux_main_tendsto_trilinearForm_dyadic_partial
    (χ : ℝ → ℝ) (f₀ f₁ f₂ : ℝ → ℂ)
    (hχ : Integrable (fun t : ℝ ↦ (χ t : ℂ)))
    (hf₀ : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁ : MemLp f₁ (2 : ℝ≥0∞) volume)
    (hf₂ : MemLp f₂ (2 : ℝ≥0∞) volume) :
    Filter.Tendsto
      (fun N : ℕ ↦ trilinearForm χ f₀ f₁
        (fun x ↦ P 0 f₂ x + ∑ k ∈ Finset.range N, P (k + 1) f₂ x))
      Filter.atTop (𝓝 (trilinearForm χ f₀ f₁ f₂)) := by
  let F : ℕ → ℝ → ℂ := fun N x ↦
    P 0 f₂ x + ∑ k ∈ Finset.range N, P (k + 1) f₂ x
  have hPzero : MemLp (P 0 f₂) (2 : ℝ≥0∞) volume := aux_memLp_P_zero f₂ hf₂
  have hP : ∀ k : ℕ, MemLp (P (k + 1) f₂) (2 : ℝ≥0∞) volume :=
    fun k ↦ aux_memLp_P_succ f₂ hf₂ k
  have hF : ∀ N : ℕ, MemLp (F N) (2 : ℝ≥0∞) volume := by
    intro n
    apply hPzero.add
    exact memLp_finsetSum (s := Finset.range n)
      (f := fun k ↦ P (k + 1) f₂) (fun k _ ↦ hP k)
  have hrec := (dyadicReconstructionAndMultiplierBounds f₂ hf₂).1
  have hdiff : Filter.Tendsto (fun N : ℕ ↦
      eLpNorm (F N - f₂) (2 : ℝ≥0∞) volume) Filter.atTop (𝓝 0) := by
    refine hrec.congr' (Filter.Eventually.of_forall fun N ↦ ?_)
    change eLpNorm (fun x ↦ f₂ x - P 0 f₂ x -
      ∑ k ∈ Finset.range N, P (k + 1) f₂ x) (2 : ℝ≥0∞) volume =
        eLpNorm (F N - f₂) (2 : ℝ≥0∞) volume
    symm
    rw [show F N - f₂ = - (fun x ↦ f₂ x - P 0 f₂ x -
        ∑ k ∈ Finset.range N, P (k + 1) f₂ x) by
      ext x
      simp only [F, Pi.sub_apply, Pi.neg_apply]
      ring]
    exact eLpNorm_neg _ _ _
  have hconv : Filter.Tendsto (fun N ↦ (hF N).toLp (F N)) Filter.atTop
      (𝓝 (hf₂.toLp f₂)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F hF f₂ hf₂).mpr hdiff
  exact aux_trilinearForm_tendsto_last_l2 χ f₀ f₁ f₂ F hχ hf₀ hf₁ hF hf₂ hconv

/-- Auxiliary finite-to-infinite assembly for `bourgainTrilinearSmoothing`
(`\label{thm:main}`): uniform
dyadic partial-form bounds pass to the reconstructed trilinear form. -/
theorem aux_main_from_dyadic_partial_bounds
    (χ : ℝ → ℝ) (f₀ f₁ f₂ : ℝ → ℂ)
    (hχ : Integrable (fun t : ℝ ↦ (χ t : ℂ)))
    (hf₀ : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁ : MemLp f₁ (2 : ℝ≥0∞) volume)
    (hf₂ : MemLp f₂ (2 : ℝ≥0∞) volume)
    (S A B H : ℝ) (hS : 2 ≤ S) (hABH : 0 ≤ A * B * H)
    (hLow : trilinearFormAbs χ f₀ f₁ (P 0 f₂) ≤ 2 * S * A * B * H)
    (hHigh : ∀ N : ℕ, ∑ k ∈ Finset.range N,
      trilinearFormAbs χ f₀ f₁ (P (k + 1) f₂) ≤
        (2 : ℝ) ^ 22 * S ^ 2 * A * B * H) :
    trilinearFormAbs χ f₀ f₁ f₂ ≤ (2 : ℝ) ^ 23 * S ^ 2 * A * B * H := by
  have hlim := aux_main_tendsto_trilinearForm_dyadic_partial χ f₀ f₁ f₂
    hχ hf₀ hf₁ hf₂
  have hscalar : 2 * S + (2 : ℝ) ^ 22 * S ^ 2 ≤ (2 : ℝ) ^ 23 * S ^ 2 := by
    norm_num at hS ⊢
    nlinarith [sq_nonneg S]
  refine le_of_tendsto' hlim.norm (fun N ↦ ?_)
  rw [aux_main_trilinearForm_dyadic_partial_sum χ f₀ f₁ f₂ hχ hf₀ hf₁ hf₂ N]
  change ‖trilinearForm χ f₀ f₁ (P 0 f₂) +
      ∑ k ∈ Finset.range N, trilinearForm χ f₀ f₁ (P (k + 1) f₂)‖ ≤ _
  calc
    ‖trilinearForm χ f₀ f₁ (P 0 f₂) +
        ∑ k ∈ Finset.range N, trilinearForm χ f₀ f₁ (P (k + 1) f₂)‖ ≤
        ‖trilinearForm χ f₀ f₁ (P 0 f₂)‖ +
          ‖∑ k ∈ Finset.range N, trilinearForm χ f₀ f₁ (P (k + 1) f₂)‖ :=
      norm_add_le _ _
    _ ≤ ‖trilinearForm χ f₀ f₁ (P 0 f₂)‖ +
          ∑ k ∈ Finset.range N, ‖trilinearForm χ f₀ f₁ (P (k + 1) f₂)‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ 2 * S * A * B * H + (2 : ℝ) ^ 22 * S ^ 2 * A * B * H := by
      exact add_le_add hLow (hHigh N)
    _ = (2 * S + (2 : ℝ) ^ 22 * S ^ 2) * (A * B * H) := by ring
    _ ≤ (2 : ℝ) ^ 23 * S ^ 2 * (A * B * H) :=
      mul_le_mul_of_nonneg_right hscalar hABH
    _ = (2 : ℝ) ^ 23 * S ^ 2 * A * B * H := by ring

end Auto
