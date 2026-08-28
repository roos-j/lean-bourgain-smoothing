/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import BourgainSmoothing.Auto.ConventionsAndFoundationalDefinitions.ConventionsAndFoundationalDefinitions
import Mathlib.Analysis.Distribution.Sobolev
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Fourier estimates for products of cutoffs

Formalizations of the labeled estimates in the corresponding section of
`blueprint/blueprint.tex`.
-/

noncomputable section

open MeasureTheory FourierTransform TemperedDistribution
open scoped ENNReal Real FourierTransform LineDeriv

namespace Auto

/-- The right-hand-side coefficient in `\label{lem:fourier-l1-h1}`, used by
`fourierL1LeFromH1`. -/
noncomputable def C_fourierL1LeFromH1
    (g dg : Lp (α := ℝ) ℂ 2 volume) : ℝ :=
  Real.sqrt 2 * ‖g‖ +
    (Real.sqrt 2 / (2 * Real.pi)) * ‖dg‖

/-- The positive half-line reciprocal-square integral used in the tail estimate for
`\label{lem:fourier-l1-h1}` and `fourierL1LeFromH1`. -/
lemma aux_positiveReciprocalSquareIntegral :
    ∫ x : ℝ in Set.Ioi 1, (x⁻¹) ^ 2 = 1 := by
  have h := integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) (c := 1) (by norm_num)
  rw [show -((1 : ℝ) ^ ((-2 : ℝ) + 1)) / ((-2 : ℝ) + 1) = 1 by norm_num] at h
  calc
    ∫ x : ℝ in Set.Ioi 1, (x⁻¹) ^ 2 =
        ∫ x : ℝ in Set.Ioi 1, x ^ (-2 : ℝ) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change 1 < x at hx
      dsimp
      rw [Real.rpow_neg (le_trans (by norm_num) (le_of_lt hx))]
      rw [inv_pow]
      exact congrArg Inv.inv (Real.rpow_natCast x 2).symm
    _ = 1 := h

/-- The negative half-line reciprocal-square integral used in the tail estimate for
`\label{lem:fourier-l1-h1}` and `fourierL1LeFromH1`. -/
lemma aux_negativeReciprocalSquareIntegral :
    ∫ x : ℝ in Set.Iio (-1), (x⁻¹) ^ 2 = 1 := by
  rw [← MeasureTheory.integral_Iic_eq_integral_Iio]
  rw [← integral_comp_neg_Ioi]
  have h : (fun x : ℝ ↦ ((-x)⁻¹) ^ 2) = fun x : ℝ ↦ (x⁻¹) ^ 2 := by
    funext x
    ring
  rw [h]
  exact by
    have h := integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) (c := 1) (by norm_num)
    rw [show -((1 : ℝ) ^ ((-2 : ℝ) + 1)) / ((-2 : ℝ) + 1) = 1 by norm_num] at h
    calc
      ∫ x : ℝ in Set.Ioi 1, (x⁻¹) ^ 2 =
          ∫ x : ℝ in Set.Ioi 1, x ^ (-2 : ℝ) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        change 1 < x at hx
        dsimp
        rw [Real.rpow_neg (le_trans (by norm_num) (le_of_lt hx))]
        rw [inv_pow]
        exact congrArg Inv.inv (Real.rpow_natCast x 2).symm
    _ = 1 := h

set_option maxHeartbeats 800000 in
-- The explicit tail-integrability calculation requires substantial normalization.
/-- Square-integrability of the reciprocal tail weight used to split the Fourier integral in
`\label{lem:fourier-l1-h1}` for `fourierL1LeFromH1`. -/
lemma aux_tailReciprocalMemLp :
    MemLp ((Set.Icc (-1 : ℝ) 1)ᶜ.indicator (fun x : ℝ ↦ x⁻¹)) 2 volume := by
  rw [MeasureTheory.memLp_two_iff_integrable_sq]
  · let S : Set ℝ := Set.Icc (-1) 1
    have hS : MeasurableSet S := measurableSet_Icc
    have hposR : IntegrableOn (fun x : ℝ ↦ x ^ (-2 : ℝ)) (Set.Ioi 1) volume :=
      integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) (by norm_num)
    have hpos : IntegrableOn (fun x : ℝ ↦ (x⁻¹) ^ 2) (Set.Ioi 1) volume := by
      refine hposR.congr_fun ?_ measurableSet_Ioi
      intro x hx
      change 1 < x at hx
      dsimp
      rw [Real.rpow_neg (le_trans (by norm_num) (le_of_lt hx))]
      rw [inv_pow]
      exact congrArg Inv.inv (Real.rpow_natCast x 2)
    have hneg : IntegrableOn (fun x : ℝ ↦ (x⁻¹) ^ 2) (Set.Iio (-1)) volume := by
      have hpos' : IntegrableOn (fun x : ℝ ↦ (x ^ 2)⁻¹)
          (Set.Ioi (-(-1 : ℝ))) volume := by
        norm_num
        simpa only [inv_pow] using hpos
      have hraw : IntegrableOn (fun x : ℝ ↦ ((-x) ^ 2)⁻¹) (Set.Iio (-1)) volume := by
        simpa using (MeasureTheory.IntegrableOn.comp_neg_Iio
          (f := fun x : ℝ ↦ (x ^ 2)⁻¹) (c := (-1 : ℝ)) hpos')
      refine hraw.congr_fun ?_ measurableSet_Iio
      intro x hx
      dsimp
      rw [← inv_pow]
      ring
    have hSc : IntegrableOn (fun x : ℝ ↦ (x⁻¹) ^ 2) Sᶜ volume := by
      have hset : Sᶜ = Set.Iio (-1) ∪ Set.Ioi 1 := by
        ext x
        dsimp [S]
        change (x ∉ Set.Icc (-1) 1) ↔ (x ∈ Set.Iio (-1) ∨ x ∈ Set.Ioi 1)
        simp only [Set.mem_Icc, Set.mem_Iio, Set.mem_Ioi]
        constructor
        · intro h
          by_cases hleft : x < -1
          · exact Or.inl hleft
          · right
            apply lt_of_not_ge
            intro hright
            apply h
            exact ⟨le_of_not_gt hleft, hright⟩
        · rintro (hleft | hright) h
          · exact (not_lt_of_ge h.1) hleft
          · exact (not_lt_of_ge h.2) hright
      rw [hset]
      exact hneg.union hpos
    have heq : (fun x : ℝ ↦ (Sᶜ.indicator (fun y : ℝ ↦ y⁻¹) x) ^ 2) =
        Sᶜ.indicator (fun x : ℝ ↦ (x⁻¹) ^ 2) := by
      funext x
      by_cases hx : x ∈ Sᶜ <;> simp [hx]
    rw [show (Set.Icc (-1 : ℝ) 1)ᶜ = Sᶜ by rfl, heq,
      MeasureTheory.integrable_indicator_iff hS.compl]
    exact hSc
  · exact ((measurable_id.inv).indicator (measurableSet_Icc.compl)).aestronglyMeasurable

set_option maxHeartbeats 800000 in
-- Splitting the reciprocal-square integral into two half-lines is normalization-intensive.
/-- Exact square integral of the reciprocal tail weight used by
`\label{lem:fourier-l1-h1}` and `fourierL1LeFromH1`. -/
lemma aux_tailReciprocalSquareIntegral :
    ∫ x : ℝ, (((Set.Icc (-1 : ℝ) 1)ᶜ.indicator (fun y : ℝ ↦ y⁻¹) x) ^ 2) = 2 := by
  let S : Set ℝ := Set.Icc (-1) 1
  have hS : MeasurableSet S := measurableSet_Icc
  have hw2 := aux_tailReciprocalMemLp.integrable_sq
  have heq : (fun x : ℝ ↦ (Sᶜ.indicator (fun y : ℝ ↦ y⁻¹) x) ^ 2) =
      Sᶜ.indicator (fun x : ℝ ↦ (x⁻¹) ^ 2) := by
    funext x
    by_cases hx : x ∈ Sᶜ <;> simp [hx]
  have hinvSc : IntegrableOn (fun x : ℝ ↦ (x⁻¹) ^ 2) Sᶜ volume := by
    rw [← MeasureTheory.integrable_indicator_iff hS.compl]
    rw [← heq]
    simpa only [show S = Set.Icc (-1 : ℝ) 1 by rfl] using hw2
  have hset : Sᶜ = Set.Iio (-1) ∪ Set.Ioi 1 := by
    ext x
    dsimp [S]
    change (x ∉ Set.Icc (-1) 1) ↔ (x ∈ Set.Iio (-1) ∨ x ∈ Set.Ioi 1)
    simp only [Set.mem_Icc, Set.mem_Iio, Set.mem_Ioi]
    constructor
    · intro h
      by_cases hleft : x < -1
      · exact Or.inl hleft
      · right
        apply lt_of_not_ge
        intro hright
        apply h
        exact ⟨le_of_not_gt hleft, hright⟩
    · rintro (hleft | hright) h
      · exact (not_lt_of_ge h.1) hleft
      · exact (not_lt_of_ge h.2) hright
  have hneg : IntegrableOn (fun x : ℝ ↦ (x⁻¹) ^ 2) (Set.Iio (-1)) volume := by
    apply hinvSc.mono_set
    rw [hset]
    exact Set.subset_union_left
  have hpos : IntegrableOn (fun x : ℝ ↦ (x⁻¹) ^ 2) (Set.Ioi 1) volume := by
    apply hinvSc.mono_set
    rw [hset]
    exact Set.subset_union_right
  change ∫ x : ℝ, (Sᶜ.indicator (fun y : ℝ ↦ y⁻¹) x) ^ 2 = 2
  rw [heq, MeasureTheory.integral_indicator hS.compl, hset]
  rw [MeasureTheory.setIntegral_union]
  · rw [aux_negativeReciprocalSquareIntegral, aux_positiveReciprocalSquareIntegral]
    norm_num
  · refine Set.disjoint_left.2 ?_
    intro x hxneg hxpos
    change x < -1 at hxneg
    change 1 < x at hxpos
    linarith
  · exact measurableSet_Ioi
  · exact hneg
  · exact hpos

/-- The Cauchy--Schwarz step for the two (L^2) factors in
`\label{lem:fourier-l1-h1}` and `fourierL1LeFromH1`. -/
lemma aux_cauchySchwarzTwo (f g : ℝ → ℂ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    lpNorm (fun x : ℝ ↦ f x * g x) 1 volume ≤
      lpNorm f 2 volume * lpNorm g 2 volume := by
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) volume := by
    norm_num
    exact hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) volume := by
    norm_num
    exact hg
  have hfg : MemLp (fun x : ℝ ↦ f x * g x) 1 volume := hg.mul hf
  rw [lpNorm_one_eq_integral_norm hfg.aestronglyMeasurable]
  calc
    ∫ x : ℝ, ‖f x * g x‖ = ∫ x : ℝ, ‖f x‖ * ‖g x‖ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [norm_mul]
    _ ≤ (∫ x : ℝ, ‖f x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (∫ x : ℝ, ‖g x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
      simpa using (integral_mul_norm_le_Lp_mul_Lq
        (μ := volume) (p := (2 : ℝ)) (q := (2 : ℝ))
        (by norm_num [Real.holderConjugate_iff]) hf' hg')
    _ = lpNorm f 2 volume * lpNorm g 2 volume := by
      rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
        hf.aestronglyMeasurable]
      rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
        hg.aestronglyMeasurable]
      norm_num

/-- Norm of the Fourier differentiation scalar appearing in
`\label{lem:fourier-l1-h1}` and `fourierL1LeFromH1`. -/
lemma aux_fourierDerivativeScalarNorm :
    ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ = 1 / (2 * Real.pi) := by
  rw [norm_inv, norm_mul, norm_mul]
  norm_num [Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- (L^2) membership of the unit-interval indicator used in the low-frequency piece of
`\label{lem:fourier-l1-h1}` and `fourierL1LeFromH1`. -/
lemma aux_unitIntervalMemLp :
    MemLp ((Set.Icc (-1 : ℝ) 1).indicator (fun _ : ℝ ↦ (1 : ℂ))) 2 volume := by
  refine memLp_indicator_const 2 measurableSet_Icc (1 : ℂ) (Or.inr ?_)
  rw [Real.volume_Icc]
  norm_num

/-- Exact (L^2) norm of the unit-interval indicator used in
`\label{lem:fourier-l1-h1}` and `fourierL1LeFromH1`. -/
lemma aux_unitIntervalLpNorm :
    lpNorm ((Set.Icc (-1 : ℝ) 1).indicator (fun _ : ℝ ↦ (1 : ℂ)))
      (2 : ℝ≥0∞) volume = Real.sqrt 2 := by
  rw [← toReal_eLpNorm ((measurable_const.indicator measurableSet_Icc).aestronglyMeasurable)]
  rw [eLpNorm_indicator_const measurableSet_Icc (by norm_num) (by norm_num)]
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
  norm_num [Real.volume_Icc, Real.sqrt_eq_rpow]

set_option maxHeartbeats 800000 in
-- Converting the explicit integral into an `L^2` norm requires substantial normalization.
/-- Exact (L^2) norm of the real reciprocal tail weight used in
`\label{lem:fourier-l1-h1}` and `fourierL1LeFromH1`. -/
lemma aux_tailReciprocalRealLpNorm :
    lpNorm ((Set.Icc (-1 : ℝ) 1)ᶜ.indicator (fun x : ℝ ↦ x⁻¹))
      (2 : ℝ≥0∞) volume = Real.sqrt 2 := by
  rw [← toReal_eLpNorm (f := (Set.Icc (-1 : ℝ) 1)ᶜ.indicator (fun x : ℝ ↦ x⁻¹))
    ((measurable_id.inv).indicator (measurableSet_Icc.compl)).aestronglyMeasurable]
  have hw := aux_tailReciprocalMemLp
  have hsq := aux_tailReciprocalSquareIntegral
  have hnormsq : ∫ x : ℝ,
      ‖(Set.Icc (-1 : ℝ) 1)ᶜ.indicator (fun y : ℝ ↦ y⁻¹) x‖ ^ (2 : ℝ) = 2 := by
    calc
      ∫ x : ℝ, ‖(Set.Icc (-1 : ℝ) 1)ᶜ.indicator (fun y : ℝ ↦ y⁻¹) x‖ ^ (2 : ℝ) =
          ∫ x : ℝ, ((Set.Icc (-1 : ℝ) 1)ᶜ.indicator (fun y : ℝ ↦ y⁻¹) x) ^ 2 := by
        apply integral_congr_ae
        filter_upwards with x
        change |(Set.Icc (-1 : ℝ) 1)ᶜ.indicator (fun y : ℝ ↦ y⁻¹) x| ^ (2 : ℝ) =
          ((Set.Icc (-1 : ℝ) 1)ᶜ.indicator (fun y : ℝ ↦ y⁻¹) x) ^ (2 : ℕ)
        calc
          |(Set.Icc (-1 : ℝ) 1)ᶜ.indicator (fun y : ℝ ↦ y⁻¹) x| ^ (2 : ℝ) =
              |(Set.Icc (-1 : ℝ) 1)ᶜ.indicator (fun y : ℝ ↦ y⁻¹) x| ^ (2 : ℕ) :=
            Real.rpow_natCast _ 2
          _ = ((Set.Icc (-1 : ℝ) 1)ᶜ.indicator (fun y : ℝ ↦ y⁻¹) x) ^ (2 : ℕ) :=
            sq_abs _
      _ = 2 := hsq
  rw [hw.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat]
  rw [hnormsq]
  rw [ENNReal.toReal_ofReal (by positivity)]
  exact (Real.sqrt_eq_rpow 2).symm

/-- The complex reciprocal tail is in (L^2), as used for the high-frequency piece of
`\label{lem:fourier-l1-h1}` and `fourierL1LeFromH1`. -/
lemma aux_tailReciprocalComplexMemLp :
    MemLp ((Set.Icc (-1 : ℝ) 1)ᶜ.indicator
      (fun x : ℝ ↦ ((x⁻¹ : ℝ) : ℂ))) 2 volume := by
  convert aux_tailReciprocalMemLp.ofReal using 1
  funext x
  by_cases hx : x ∈ (Set.Icc (-1 : ℝ) 1)ᶜ <;> simp [hx]

/-- Exact (L^2) norm of the complex reciprocal tail used in
`\label{lem:fourier-l1-h1}` and `fourierL1LeFromH1`. -/
lemma aux_tailReciprocalComplexLpNorm :
    lpNorm ((Set.Icc (-1 : ℝ) 1)ᶜ.indicator
      (fun x : ℝ ↦ ((x⁻¹ : ℝ) : ℂ))) 2 volume = Real.sqrt 2 := by
  calc
    lpNorm ((Set.Icc (-1 : ℝ) 1)ᶜ.indicator
        (fun x : ℝ ↦ ((x⁻¹ : ℝ) : ℂ))) 2 volume =
        (eLpNorm ((Set.Icc (-1 : ℝ) 1)ᶜ.indicator
          (fun x : ℝ ↦ ((x⁻¹ : ℝ) : ℂ))) 2 volume).toReal := by
      rw [toReal_eLpNorm]
      exact aux_tailReciprocalComplexMemLp.aestronglyMeasurable
    _ = (eLpNorm ((Set.Icc (-1 : ℝ) 1)ᶜ.indicator
          (fun x : ℝ ↦ (x⁻¹ : ℝ))) 2 volume).toReal := by
      apply congrArg ENNReal.toReal
      apply eLpNorm_congr_norm_ae
      filter_upwards with x
      by_cases hx : x ∈ (Set.Icc (-1 : ℝ) 1)ᶜ <;> simp [hx]
    _ = lpNorm ((Set.Icc (-1 : ℝ) 1)ᶜ.indicator
          (fun x : ℝ ↦ (x⁻¹ : ℝ))) 2 volume := by
      rw [toReal_eLpNorm]
      exact ((measurable_id.inv).indicator measurableSet_Icc.compl).aestronglyMeasurable
    _ = Real.sqrt 2 := aux_tailReciprocalRealLpNorm

/-- The Fourier transform of the weak derivative relation, represented almost everywhere, for
`\label{lem:fourier-l1-h1}` and `fourierL1LeFromH1`. -/
lemma aux_fourierDerivativeAe (g dg : Lp (α := ℝ) ℂ 2 volume)
    (hdg : ∂_{(1 : ℝ)} (Lp.toTemperedDistribution g) = Lp.toTemperedDistribution dg) :
    ∀ᵐ ξ : ℝ ∂volume,
      (ξ : ℂ) * (Lp.fourierTransformₗᵢ ℝ ℂ g) ξ =
        (2 * Real.pi * Complex.I)⁻¹ * (Lp.fourierTransformₗᵢ ℝ ℂ dg) ξ := by
  let F : Lp (α := ℝ) ℂ 2 volume := Lp.fourierTransformₗᵢ ℝ ℂ g
  let G : Lp (α := ℝ) ℂ 2 volume := Lp.fourierTransformₗᵢ ℝ ℂ dg
  have hdist : Lp.toTemperedDistribution G =
      (2 * Real.pi * Complex.I) •
        TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ))
          (Lp.toTemperedDistribution F) := by
    dsimp [F, G]
    calc
      Lp.toTemperedDistribution (Lp.fourierTransformₗᵢ ℝ ℂ dg) =
          𝓕 (Lp.toTemperedDistribution dg) :=
        (Lp.fourier_toTemperedDistribution_eq dg).symm
      _ = 𝓕 (∂_{(1 : ℝ)} (Lp.toTemperedDistribution g)) := by rw [hdg]
      _ = (2 * Real.pi * Complex.I) •
          TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ))
            (𝓕 (Lp.toTemperedDistribution g)) := by
        simpa using
          (TemperedDistribution.fourier_lineDerivOp_eq
            (Lp.toTemperedDistribution g) (1 : ℝ))
      _ = (2 * Real.pi * Complex.I) •
          TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ))
            (Lp.toTemperedDistribution (Lp.fourierTransformₗᵢ ℝ ℂ g)) := by
        rw [Lp.fourier_toTemperedDistribution_eq g]
        rfl
  have hF : MemLp (fun ξ : ℝ ↦ F ξ) 2 volume := Lp.memLp F
  have hG : MemLp (fun ξ : ℝ ↦ G ξ) 2 volume := Lp.memLp G
  have hXF_loc : LocallyIntegrable (fun ξ : ℝ ↦ (ξ : ℂ) * F ξ) volume := by
    exact hF.locallyIntegrable (by norm_num) |>.continuous_mul
      (Complex.continuous_ofReal.comp continuous_id)
  have hX_loc : LocallyIntegrable
      (fun ξ : ℝ ↦ (2 * Real.pi * Complex.I)⁻¹ * G ξ) volume := by
    convert (hG.const_smul (2 * Real.pi * Complex.I)⁻¹).locallyIntegrable (by norm_num) using 1
    ext ξ
    simp [smul_eq_mul]
  apply (ae_eq_of_integral_contDiff_smul_eq hXF_loc hX_loc)
  intro φ hφ hφc
  have hφc_complex : HasCompactSupport (Complex.ofReal ∘ φ) :=
    hφc.comp_left (show Complex.ofReal (0 : ℝ) = 0 by simp)
  let Φ : SchwartzMap ℝ ℂ :=
    hφc_complex.toSchwartzMap (by
      change ContDiff ℝ _ (Complex.ofRealCLM ∘ φ)
      exact Complex.ofRealCLM.contDiff.comp hφ)
  have happly := congrArg (fun T : TemperedDistribution ℝ ℂ ↦ T Φ) hdist
  dsimp [Φ] at happly
  have hidtemp : Function.HasTemperateGrowth (fun x : ℝ ↦ (x : ℂ)) := by fun_prop
  simp only [MeasureTheory.Lp.toTemperedDistribution_apply,
    TemperedDistribution.smulLeftCLM_apply_apply, smul_apply] at happly
  simp only [HasCompactSupport.toSchwartzMap_toFun,
    SchwartzMap.smulLeftCLM_apply_apply hidtemp] at happly
  have happly' : (∫ x : ℝ, (φ x : ℂ) * G x) =
      (2 * Real.pi * Complex.I) *
        ∫ x : ℝ, ((x : ℂ) * (φ x : ℂ)) * F x := by
    simpa [smul_eq_mul, Function.comp_apply] using happly
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    norm_num [Real.pi_ne_zero]
  calc
    (∫ x : ℝ, φ x • ((x : ℂ) * F x)) =
        ∫ x : ℝ, (φ x : ℂ) * ((x : ℂ) * F x) := by
          apply integral_congr_ae
          filter_upwards with x
          simp
    _ = ∫ x : ℝ, ((x : ℂ) * (φ x : ℂ)) * F x := by
          apply integral_congr_ae
          filter_upwards with x
          ring
    _ = (2 * Real.pi * Complex.I)⁻¹ *
        ((2 * Real.pi * Complex.I) *
          ∫ x : ℝ, ((x : ℂ) * (φ x : ℂ)) * F x) := by
          field_simp
    _ = (2 * Real.pi * Complex.I)⁻¹ *
        ∫ x : ℝ, (φ x : ℂ) * G x := by rw [← happly']
    _ = ∫ x : ℝ, φ x • ((2 * Real.pi * Complex.I)⁻¹ * G x) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with x
          simp
          ring

/-- The weak-derivative form of the estimate in `\label{lem:fourier-l1-h1}`.
It isolates the sufficient `L²` distributional derivative hypothesis used by
`fourierL1LeFromH1`. -/
lemma aux_fourierL1LeFromWeakDerivative
    (g dg : Lp (α := ℝ) ℂ 2 volume)
    (hdg : ∂_{(1 : ℝ)} (Lp.toTemperedDistribution g) = Lp.toTemperedDistribution dg) :
    (eLpNorm (fun ξ : ℝ ↦ (Lp.fourierTransformₗᵢ ℝ ℂ g) ξ)
      (1 : ℝ≥0∞) volume).toReal ≤ C_fourierL1LeFromH1 g dg := by
  let F : Lp (α := ℝ) ℂ 2 volume := Lp.fourierTransformₗᵢ ℝ ℂ g
  let G : Lp (α := ℝ) ℂ 2 volume := Lp.fourierTransformₗᵢ ℝ ℂ dg
  let S : Set ℝ := Set.Icc (-1) 1
  let u : ℝ → ℂ := S.indicator (fun _ : ℝ ↦ 1)
  let w : ℝ → ℂ := Sᶜ.indicator (fun x : ℝ ↦ ((x⁻¹ : ℝ) : ℂ))
  let c : ℂ := (2 * Real.pi * Complex.I)⁻¹
  let T : ℝ → ℂ := fun x ↦ c * G x
  have hF : MemLp (fun x : ℝ ↦ F x) 2 volume := Lp.memLp F
  have hG : MemLp (fun x : ℝ ↦ G x) 2 volume := Lp.memLp G
  have hderiv : ∀ᵐ x : ℝ ∂volume, (x : ℂ) * F x = c * G x := by
    simpa [F, G, c] using aux_fourierDerivativeAe g dg hdg
  have hu : MemLp u 2 volume := by
    simpa [u, S] using aux_unitIntervalMemLp
  have hnu : lpNorm u 2 volume = Real.sqrt 2 := by
    simpa [u, S] using aux_unitIntervalLpNorm
  have hw : MemLp w 2 volume := by
    simpa [w, S] using aux_tailReciprocalComplexMemLp
  have hnw : lpNorm w 2 volume = Real.sqrt 2 := by
    simpa [w, S] using aux_tailReciprocalComplexLpNorm
  have hT : MemLp T 2 volume := by
    have hTc : MemLp (c • (fun x : ℝ ↦ G x)) 2 volume := hG.const_smul c
    convert hTc using 1
    ext x
    simp [T, smul_eq_mul]
  have hFnorm : lpNorm (fun x : ℝ ↦ F x) 2 volume = ‖g‖ := by
    calc
      lpNorm (fun x : ℝ ↦ F x) 2 volume =
          (eLpNorm (fun x : ℝ ↦ F x) 2 volume).toReal := by
        rw [toReal_eLpNorm hF.aestronglyMeasurable]
      _ = ‖F‖ := (Lp.norm_def F).symm
      _ = ‖g‖ := by
        dsimp [F]
        exact Lp.norm_fourier_eq g
  have hGnorm : lpNorm (fun x : ℝ ↦ G x) 2 volume = ‖dg‖ := by
    calc
      lpNorm (fun x : ℝ ↦ G x) 2 volume =
          (eLpNorm (fun x : ℝ ↦ G x) 2 volume).toReal := by
        rw [toReal_eLpNorm hG.aestronglyMeasurable]
      _ = ‖G‖ := (Lp.norm_def G).symm
      _ = ‖dg‖ := by
        dsimp [G]
        exact Lp.norm_fourier_eq dg
  have hTnorm : lpNorm T 2 volume = (1 / (2 * Real.pi)) * ‖dg‖ := by
    calc
      lpNorm T 2 volume = ‖c‖ * lpNorm (fun x : ℝ ↦ G x) 2 volume := by
        have hTc := lpNorm_const_smul c (fun x : ℝ ↦ G x) volume (p := (2 : ℝ≥0∞))
        convert hTc using 1
        · apply congrArg (fun f : ℝ → ℂ ↦ lpNorm f 2 volume)
          funext x
          simp [T, smul_eq_mul]
        · simp
      _ = (1 / (2 * Real.pi)) * ‖dg‖ := by
        rw [hGnorm]
        dsimp [c]
        rw [aux_fourierDerivativeScalarNorm]
  have hsmall_eq : S.indicator (fun x : ℝ ↦ F x) = fun x ↦ u x * F x := by
    funext x
    by_cases hx : x ∈ S <;> simp [u, hx]
  have htail_eq : Sᶜ.indicator (fun x : ℝ ↦ F x) =ᵐ[volume] fun x ↦ w x * T x := by
    filter_upwards [hderiv] with x hx
    by_cases hxs : x ∈ S
    · simp [w, hxs]
    · have hxsc : x ∈ Sᶜ := hxs
      have hx0 : x ≠ 0 := by
        intro hx0
        apply hxs
        subst x
        dsimp [S]
        norm_num
      have hx0C : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
      dsimp [w, T]
      simp only [Set.indicator_of_mem hxsc]
      calc
        F x = (x : ℂ)⁻¹ * ((x : ℂ) * F x) := by field_simp
        _ = (x : ℂ)⁻¹ * (c * G x) := by rw [hx]
        _ = ((x⁻¹ : ℝ) : ℂ) * (c * G x) := by simp
  have hsmall_prod : MemLp (fun x : ℝ ↦ u x * F x) 1 volume := hF.mul hu
  have htail_prod : MemLp (fun x : ℝ ↦ w x * T x) 1 volume := hT.mul hw
  have hsmall : MemLp (S.indicator (fun x : ℝ ↦ F x)) 1 volume := by
    rw [hsmall_eq]
    exact hsmall_prod
  have htail : MemLp (Sᶜ.indicator (fun x : ℝ ↦ F x)) 1 volume :=
    (memLp_congr_ae htail_eq).mpr htail_prod
  have hsmall_bound : lpNorm (S.indicator (fun x : ℝ ↦ F x)) 1 volume ≤
      Real.sqrt 2 * ‖g‖ := by
    rw [hsmall_eq]
    calc
      lpNorm (fun x : ℝ ↦ u x * F x) 1 volume ≤
          lpNorm u 2 volume * lpNorm (fun x : ℝ ↦ F x) 2 volume :=
        aux_cauchySchwarzTwo u (fun x : ℝ ↦ F x) hu hF
      _ = Real.sqrt 2 * ‖g‖ := by rw [hnu, hFnorm]
  have htail_bound : lpNorm (Sᶜ.indicator (fun x : ℝ ↦ F x)) 1 volume ≤
      Real.sqrt 2 * ((1 / (2 * Real.pi)) * ‖dg‖) := by
    calc
      lpNorm (Sᶜ.indicator (fun x : ℝ ↦ F x)) 1 volume =
          lpNorm (fun x : ℝ ↦ w x * T x) 1 volume := by
        rw [← toReal_eLpNorm htail.aestronglyMeasurable,
          ← toReal_eLpNorm htail_prod.aestronglyMeasurable,
          eLpNorm_congr_ae htail_eq]
      _ ≤ lpNorm w 2 volume * lpNorm T 2 volume :=
        aux_cauchySchwarzTwo w T hw hT
      _ = Real.sqrt 2 * ((1 / (2 * Real.pi)) * ‖dg‖) := by rw [hnw, hTnorm]
  have hsum : S.indicator (fun x : ℝ ↦ F x) + Sᶜ.indicator (fun x : ℝ ↦ F x) =
      fun x ↦ F x := by
    funext x
    simp
  change (eLpNorm (fun x : ℝ ↦ F x) 1 volume).toReal ≤ C_fourierL1LeFromH1 g dg
  rw [toReal_eLpNorm hF.aestronglyMeasurable]
  calc
    lpNorm (fun x : ℝ ↦ F x) 1 volume =
        lpNorm (S.indicator (fun x : ℝ ↦ F x) + Sᶜ.indicator (fun x : ℝ ↦ F x)) 1 volume := by
      rw [hsum]
    _ ≤ lpNorm (S.indicator (fun x : ℝ ↦ F x)) 1 volume +
        lpNorm (Sᶜ.indicator (fun x : ℝ ↦ F x)) 1 volume :=
      lpNorm_add_le hsmall (by norm_num)
    _ ≤ Real.sqrt 2 * ‖g‖ + Real.sqrt 2 * ((1 / (2 * Real.pi)) * ‖dg‖) :=
      add_le_add hsmall_bound htail_bound
    _ = C_fourierL1LeFromH1 g dg := by
      simp only [C_fourierL1LeFromH1]
      ring

/--
If \(g\in H^1(\mathbb R)\), then
\[
\lVert\widehat g\rVert_1
\leq
\sqrt2\lVert g\rVert_2+
\frac{\sqrt2}{2\pi}\lVert g'\rVert_2.
\]
-/
theorem fourierL1LeFromH1
    (g dg : Lp (α := ℝ) ℂ 2 volume)
    (_hg : MemSobolev (E := ℝ) 1 2 (Lp.toTemperedDistribution g))
    (hdg : ∂_{(1 : ℝ)} (Lp.toTemperedDistribution g) = Lp.toTemperedDistribution dg) :
    (eLpNorm (fun ξ : ℝ ↦ (Lp.fourierTransformₗᵢ ℝ ℂ g) ξ)
      (1 : ℝ≥0∞) volume).toReal ≤ C_fourierL1LeFromH1 g dg :=
  aux_fourierL1LeFromWeakDerivative g dg hdg

/-- The raw Fourier integral and its `L²` Plancherel representative agree almost everywhere.
This is the bridge needed to apply `fourierL1LeFromH1` to the raw Fourier integral in
`\label{lem:product-cutoff-fourier}`. -/
lemma aux_l2Fourier_eq_raw_ae (f : ℝ → ℂ)
    (hf1 : MemLp f 1 volume) (hf2 : MemLp f 2 volume) :
    ∀ᵐ ξ : ℝ ∂volume,
      (Lp.fourierTransformₗᵢ ℝ ℂ hf2.toLp) ξ = 𝓕 f ξ := by
  let g2 : Lp (α := ℝ) ℂ 2 volume := hf2.toLp f
  let F : Lp (α := ℝ) ℂ 2 volume := Lp.fourierTransformₗᵢ ℝ ℂ g2
  have hF : MemLp (fun x : ℝ ↦ F x) 2 volume := Lp.memLp F
  have hrawcont : Continuous (𝓕 f) := by
    rw [← Real.fourierTransform_toLp hf1]
    exact (Real.Lp.fourierTransform hf1.toLp).continuous
  apply ae_eq_of_integral_contDiff_smul_eq (hF.locallyIntegrable (by norm_num))
    hrawcont.locallyIntegrable
  intro φ hφ hφc
  have hφc_complex : HasCompactSupport (Complex.ofReal ∘ φ) :=
    hφc.comp_left (show Complex.ofReal (0 : ℝ) = 0 by simp)
  let Φ : SchwartzMap ℝ ℂ :=
    hφc_complex.toSchwartzMap (by
      change ContDiff ℝ _ (Complex.ofRealCLM ∘ φ)
      exact Complex.ofRealCLM.contDiff.comp hφ)
  have hdist := Lp.fourier_toTemperedDistribution_eq g2
  change 𝓕 (Lp.toTemperedDistribution (hf2.toLp f)) =
    Lp.toTemperedDistribution (Lp.fourierTransformₗᵢ ℝ ℂ (hf2.toLp f)) at hdist
  have happly := congrArg (fun T : TemperedDistribution ℝ ℂ ↦ T Φ) hdist
  rw [TemperedDistribution.fourier_apply,
    MeasureTheory.Lp.toTemperedDistribution_apply] at happly
  simp only [MeasureTheory.Lp.toTemperedDistribution_apply] at happly
  change (∫ x : ℝ, (𝓕 Φ) x • ((hf2.toLp f : Lp (α := ℝ) ℂ 2 volume) x)) =
    ∫ x : ℝ, Φ x • (Lp.fourierTransformₗᵢ ℝ ℂ (hf2.toLp f)) x at happly
  have hfint : Integrable f volume := memLp_one_iff_integrable.mp hf1
  have hFubini0 := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := volume) (ν := volume) (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner hfint Φ.integrable
  change (∫ ξ : ℝ, (𝓕 f) ξ • Φ ξ) =
    ∫ x : ℝ, f x • VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ).flip Φ x at hFubini0
  have hflip : (fun x : ℝ ↦ VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ).flip Φ x) =
      𝓕 Φ := by
    ext x
    change (∫ y : ℝ, 𝐞 (-((innerₗ ℝ).flip y x)) • Φ y) =
      ∫ y : ℝ, 𝐞 (-((innerₗ ℝ) y x)) • Φ y
    congr 3
    funext y
    congr 2
    simp
  have hFubini : ∫ ξ : ℝ, (𝓕 f) ξ • Φ ξ =
      ∫ x : ℝ, f x • (𝓕 Φ) x := by
    rw [← hflip]
    exact hFubini0
  have hcoe : (fun x : ℝ ↦ ((hf2.toLp f : Lp (α := ℝ) ℂ 2 volume) x)) =ᵐ[volume] f :=
    hf2.coeFn_toLp
  calc
    (∫ x : ℝ, φ x • (Lp.fourierTransformₗᵢ ℝ ℂ hf2.toLp) x) =
        ∫ x : ℝ, (Φ x) • (Lp.fourierTransformₗᵢ ℝ ℂ hf2.toLp) x := by
      apply integral_congr_ae
      filter_upwards with x
      simp [Φ]
    _ = ∫ x : ℝ, (𝓕 Φ) x • ((hf2.toLp f : Lp (α := ℝ) ℂ 2 volume) x) := by
      simpa [smul_eq_mul] using happly.symm
    _ = ∫ x : ℝ, f x • (𝓕 Φ) x := by
      apply integral_congr_ae
      filter_upwards [hcoe] with x hx
      rw [hx]
      ring
    _ = ∫ x : ℝ, (𝓕 f) x • Φ x := by
      exact hFubini.symm
    _ = ∫ x : ℝ, φ x • 𝓕 f x := by
      apply integral_congr_ae
      filter_upwards with x
      simp [Φ]
      ring

/-- A compactly supported `C¹` function has its classical derivative as its weak derivative.
This supplies the `H¹` input for `productCutoffFourierBounds` and
`\label{lem:product-cutoff-fourier}`. -/
lemma aux_weakDerivativeOfContDiffCompact (f df : ℝ → ℂ)
    (hfs : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hfmem : MemLp f (2 : ℝ≥0∞) volume)
    (hdf : ∀ x : ℝ, deriv f x = df x)
    (hdfmem : MemLp df (2 : ℝ≥0∞) volume) :
    ∂_{(1 : ℝ)} (Lp.toTemperedDistribution
      (hfmem.toLp f)) =
      Lp.toTemperedDistribution (hdfmem.toLp df) := by
  have hdercont : Continuous (fun x : ℝ ↦ fderiv ℝ f x 1) := by
    have h := hfs.continuous_deriv (by norm_num : (1 : WithTop ℕ∞) ≤ 1)
    simpa only [fderiv_apply_one_eq_deriv] using h
  have hdercomp : HasCompactSupport (fun x : ℝ ↦ fderiv ℝ f x 1) := by
    have h := hfc.deriv
    simpa only [fderiv_apply_one_eq_deriv] using h
  change ∂_{(1 : ℝ)} (Lp.toTemperedDistribution (hfmem.toLp f)) =
      Lp.toTemperedDistribution (hdfmem.toLp df)
  ext φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply,
    MeasureTheory.Lp.toTemperedDistribution_apply]
  have hφdercont : Continuous (fun x : ℝ ↦ fderiv ℝ (φ : ℝ → ℂ) x 1) := by
    simpa only [← SchwartzMap.lineDerivOp_apply_eq_fderiv] using
      ((∂_{(1 : ℝ)} φ : SchwartzMap ℝ ℂ).continuous)
  have hi₁ : Integrable (fun x : ℝ ↦ fderiv ℝ (φ : ℝ → ℂ) x 1 • f x) volume :=
    hφdercont.locallyIntegrable.integrable_smul_right_of_hasCompactSupport
      hfs.continuous hfc
  have hi₂ : Integrable (fun x : ℝ ↦ (φ : ℝ → ℂ) x • fderiv ℝ f x 1) volume :=
    φ.continuous.locallyIntegrable.integrable_smul_right_of_hasCompactSupport
      hdercont hdercomp
  have hi₃ : Integrable (fun x : ℝ ↦ (φ : ℝ → ℂ) x • f x) volume :=
    φ.continuous.locallyIntegrable.integrable_smul_right_of_hasCompactSupport
      hfs.continuous hfc
  have hibp := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (μ := volume) (v := (1 : ℝ)) hi₁ hi₂ hi₃
    (fun x _ ↦ φ.differentiableAt) (fun x _ ↦ (hfs.differentiable (by norm_num)) x)
  have hibp' :
      (∫ x : ℝ, -(fderiv ℝ (φ : ℝ → ℂ) x 1) • f x) =
        ∫ x : ℝ, (φ : ℝ → ℂ) x • df x := by
    calc
      ∫ x : ℝ, -(fderiv ℝ (φ : ℝ → ℂ) x 1) • f x =
          ∫ x : ℝ, -((fderiv ℝ (φ : ℝ → ℂ) x 1) • f x) := by
        apply integral_congr_ae
        filter_upwards with x
        simp
      _ = -∫ x : ℝ, fderiv ℝ (φ : ℝ → ℂ) x 1 • f x := by rw [integral_neg]
      _ =
          ∫ x : ℝ, (φ : ℝ → ℂ) x • fderiv ℝ f x 1 := hibp.symm
      _ = ∫ x : ℝ, (φ : ℝ → ℂ) x • df x := by
        apply integral_congr_ae
        filter_upwards with x
        rw [fderiv_apply_one_eq_deriv, hdf x]
  have hfae := hfmem.coeFn_toLp
  have hdfae := hdfmem.coeFn_toLp
  calc
    ∫ x : ℝ, (-∂_{(1 : ℝ)} φ x) • (hfmem.toLp f) x =
        ∫ x : ℝ, -(fderiv ℝ (φ : ℝ → ℂ) x 1) • f x := by
      apply integral_congr_ae
      filter_upwards [hfae] with x hx
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
      simp [hx]
    _ = ∫ x : ℝ, (φ : ℝ → ℂ) x • df x := hibp'
    _ = ∫ x : ℝ, φ x • (hdfmem.toLp df) x := by
      apply integral_congr_ae
      filter_upwards [hdfae] with x hx
      simp [hx]

/-- The explicit constant in `\label{lem:product-cutoff-fourier}`, used by
`productCutoffFourierBounds`. -/
noncomputable def C_productCutoffFourierBounds (ψ : ℝ → ℝ) : ℝ :=
  Real.sqrt 2 * (eLpNorm ψ (2 : ℝ≥0∞) volume).toReal +
    (Real.sqrt 2 / Real.pi) * (eLpNorm (deriv ψ) (2 : ℝ≥0∞) volume).toReal

/-- Smoothness of the translated cutoff product used by
`productCutoffFourierBounds` for `\label{lem:product-cutoff-fourier}`. -/
lemma aux_productCutoffSmooth (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ) (u : ℝ) :
    ContDiff ℝ 1 (fun t : ℝ ↦ ψ t * ψ (t + u)) := by
  exact hψ.mul (hψ.comp (contDiff_id.add contDiff_const))

/-- Compact support of the translated cutoff product used by
`productCutoffFourierBounds` for `\label{lem:product-cutoff-fourier}`. -/
lemma aux_productCutoffCompact (ψ : ℝ → ℝ) (hψ : HasCompactSupport ψ) (u : ℝ) :
    HasCompactSupport (fun t : ℝ ↦ ψ t * ψ (t + u)) := by
  exact hψ.mul_right

/-- The complex translated cutoff product is integrable, as needed to compare raw and `L²`
Fourier transforms in `productCutoffFourierBounds` for `\label{lem:product-cutoff-fourier}`. -/
lemma aux_productCutoffMemLpOne (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) (u : ℝ) :
    MemLp (fun t : ℝ ↦ ((ψ t * ψ (t + u) : ℝ) : ℂ)) (1 : ℝ≥0∞) volume := by
  exact ((aux_productCutoffSmooth ψ hψ u).continuous.memLp_of_hasCompactSupport
    (aux_productCutoffCompact ψ hψc u)).ofReal

/-- The complex translated cutoff product belongs to `L²`, as needed by
`productCutoffFourierBounds` for `\label{lem:product-cutoff-fourier}`. -/
lemma aux_productCutoffMemLpTwo (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) (u : ℝ) :
    MemLp (fun t : ℝ ↦ ((ψ t * ψ (t + u) : ℝ) : ℂ)) (2 : ℝ≥0∞) volume := by
  exact ((aux_productCutoffSmooth ψ hψ u).continuous.memLp_of_hasCompactSupport
    (aux_productCutoffCompact ψ hψc u)).ofReal

/-- Coercion from real- to complex-valued functions preserves the `eLpNorm` used in
`productCutoffFourierBounds` for `\label{lem:product-cutoff-fourier}`. -/
lemma aux_eLpNormRealToComplex (f : ℝ → ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun t : ℝ ↦ (f t : ℂ)) p volume = eLpNorm f p volume := by
  apply eLpNorm_congr_norm_ae
  filter_upwards with t
  simp

/-- Translation invariance of the real `eLpNorm` used for the derivative estimate in
`productCutoffFourierBounds` for `\label{lem:product-cutoff-fourier}`. -/
lemma aux_eLpNormTranslateReal (f : ℝ → ℝ) (hf : AEStronglyMeasurable f volume)
    (p : ℝ≥0∞) (u : ℝ) :
    eLpNorm (fun t : ℝ ↦ f (t + u)) p volume = eLpNorm f p volume := by
  simpa only [Function.comp_def] using
    (eLpNorm_comp_measurePreserving hf (measurePreserving_add_right volume u))

/-- The `L²` estimate for the translated cutoff product in
`productCutoffFourierBounds` for `\label{lem:product-cutoff-fourier}`. -/
lemma aux_productCutoffELpNormBound (ψ : ℝ → ℝ)
    (hψ_nonneg : ∀ t : ℝ, 0 ≤ ψ t) (hψ_le_one : ∀ t : ℝ, ψ t ≤ 1)
    (u : ℝ) :
    eLpNorm (fun t : ℝ ↦ ψ t * ψ (t + u)) (2 : ℝ≥0∞) volume ≤
      eLpNorm ψ (2 : ℝ≥0∞) volume := by
  apply eLpNorm_mono
  intro t
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (hψ_nonneg t), abs_of_nonneg (hψ_nonneg (t + u))]
  simpa using mul_le_mul_of_nonneg_left (hψ_le_one (t + u)) (hψ_nonneg t)

/-- The first Leibniz term in the derivative estimate for
`productCutoffFourierBounds` and `\label{lem:product-cutoff-fourier}`. -/
lemma aux_productCutoffDerivativeLeftELpNormBound (ψ : ℝ → ℝ)
    (hψ_nonneg : ∀ t : ℝ, 0 ≤ ψ t) (hψ_le_one : ∀ t : ℝ, ψ t ≤ 1)
    (u : ℝ) :
    eLpNorm (fun t : ℝ ↦ deriv ψ t * ψ (t + u)) (2 : ℝ≥0∞) volume ≤
      eLpNorm (deriv ψ) (2 : ℝ≥0∞) volume := by
  apply eLpNorm_mono
  intro t
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (hψ_nonneg (t + u))]
  exact (mul_le_mul_of_nonneg_left (hψ_le_one (t + u)) (abs_nonneg _)).trans_eq
    (by ring)

/-- The second Leibniz term in the derivative estimate for
`productCutoffFourierBounds` and `\label{lem:product-cutoff-fourier}`. -/
lemma aux_productCutoffDerivativeRightELpNormBound (ψ : ℝ → ℝ)
    (hψ_nonneg : ∀ t : ℝ, 0 ≤ ψ t) (hψ_le_one : ∀ t : ℝ, ψ t ≤ 1)
    (u : ℝ) :
    eLpNorm (fun t : ℝ ↦ ψ t * deriv ψ (t + u)) (2 : ℝ≥0∞) volume ≤
      eLpNorm (fun t : ℝ ↦ deriv ψ (t + u)) (2 : ℝ≥0∞) volume := by
  apply eLpNorm_mono
  intro t
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (hψ_nonneg t)]
  exact (mul_le_mul_of_nonneg_right (hψ_le_one t) (abs_nonneg _)).trans_eq
    (by ring)

/-- The `L²` derivative estimate for the translated cutoff product in
`productCutoffFourierBounds` for `\label{lem:product-cutoff-fourier}`. -/
lemma aux_productCutoffDerivativeELpNormBound (ψ : ℝ → ℝ) (hψ_smooth : ContDiff ℝ 1 ψ)
    (hψ_nonneg : ∀ t : ℝ, 0 ≤ ψ t) (hψ_le_one : ∀ t : ℝ, ψ t ≤ 1)
    (u : ℝ) :
    eLpNorm (fun t : ℝ ↦ deriv ψ t * ψ (t + u) + ψ t * deriv ψ (t + u))
      (2 : ℝ≥0∞) volume ≤
      2 * eLpNorm (deriv ψ) (2 : ℝ≥0∞) volume := by
  have hdercont : Continuous (deriv ψ) :=
    hψ_smooth.continuous_deriv (by norm_num : (1 : WithTop ℕ∞) ≤ 1)
  have hshiftcont : Continuous (fun t : ℝ ↦ ψ (t + u)) :=
    hψ_smooth.continuous.comp (continuous_id.add continuous_const)
  have hdershiftcont : Continuous (fun t : ℝ ↦ deriv ψ (t + u)) :=
    hdercont.comp (continuous_id.add continuous_const)
  calc
    eLpNorm (fun t : ℝ ↦ deriv ψ t * ψ (t + u) + ψ t * deriv ψ (t + u))
        (2 : ℝ≥0∞) volume ≤
        eLpNorm (fun t : ℝ ↦ deriv ψ t * ψ (t + u)) (2 : ℝ≥0∞) volume +
          eLpNorm (fun t : ℝ ↦ ψ t * deriv ψ (t + u)) (2 : ℝ≥0∞) volume := by
      change eLpNorm ((deriv ψ * fun t : ℝ ↦ ψ (t + u)) +
          ψ * fun t : ℝ ↦ deriv ψ (t + u)) (2 : ℝ≥0∞) volume ≤
        eLpNorm (deriv ψ * fun t : ℝ ↦ ψ (t + u)) (2 : ℝ≥0∞) volume +
          eLpNorm (ψ * fun t : ℝ ↦ deriv ψ (t + u)) (2 : ℝ≥0∞) volume
      exact eLpNorm_add_le
        (hdercont.mul hshiftcont).aestronglyMeasurable
        (hψ_smooth.continuous.mul hdershiftcont).aestronglyMeasurable (by norm_num)
    _ ≤ eLpNorm (deriv ψ) (2 : ℝ≥0∞) volume +
          eLpNorm (fun t : ℝ ↦ deriv ψ (t + u)) (2 : ℝ≥0∞) volume := by
      exact add_le_add
        (aux_productCutoffDerivativeLeftELpNormBound ψ hψ_nonneg hψ_le_one u)
        (aux_productCutoffDerivativeRightELpNormBound ψ hψ_nonneg hψ_le_one u)
    _ = eLpNorm (deriv ψ) (2 : ℝ≥0∞) volume +
          eLpNorm (deriv ψ) (2 : ℝ≥0∞) volume := by
      rw [aux_eLpNormTranslateReal (deriv ψ) hdercont.aestronglyMeasurable 2 u]
    _ = 2 * eLpNorm (deriv ψ) (2 : ℝ≥0∞) volume := by ring

/-- The classical derivative formula for the real cutoff product used in
`productCutoffFourierBounds` for `\label{lem:product-cutoff-fourier}`. -/
lemma aux_productCutoffDerivativeFormula (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ) (u t : ℝ) :
    deriv (fun s : ℝ ↦ ψ s * ψ (s + u)) t =
      deriv ψ t * ψ (t + u) + ψ t * deriv ψ (t + u) := by
  have hψdiff : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hshiftsmooth : ContDiff ℝ 1 (fun s : ℝ ↦ ψ (s + u)) :=
    hψ.comp (contDiff_id.add contDiff_const)
  have hshiftdiff : Differentiable ℝ (fun s : ℝ ↦ ψ (s + u)) :=
    hshiftsmooth.differentiable (by norm_num)
  change deriv (ψ * fun s : ℝ ↦ ψ (s + u)) t = _
  rw [deriv_mul (hψdiff t) (hshiftdiff t)]
  rw [deriv_comp_add_const]

/-- The classical derivative formula for the complex cutoff product used in
`productCutoffFourierBounds` for `\label{lem:product-cutoff-fourier}`. -/
lemma aux_productCutoffDerivativeComplexFormula (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (u t : ℝ) :
    deriv (fun s : ℝ ↦ ((ψ s * ψ (s + u) : ℝ) : ℂ)) t =
      ((deriv ψ t * ψ (t + u) + ψ t * deriv ψ (t + u) : ℝ) : ℂ) := by
  have hψdiff : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hfirst : HasDerivAt ψ (deriv ψ t) t := (hψdiff t).hasDerivAt
  have hsecond : HasDerivAt (fun s : ℝ ↦ ψ (s + u)) (deriv ψ (t + u)) t :=
    ((hψdiff (t + u)).hasDerivAt.comp_add_const t u)
  have hreal : HasDerivAt (fun s : ℝ ↦ ψ s * ψ (s + u))
      (deriv ψ t * ψ (t + u) + ψ t * deriv ψ (t + u)) t := by
    change HasDerivAt (ψ * fun s : ℝ ↦ ψ (s + u)) _ t
    exact hfirst.mul hsecond
  simpa using hreal.ofReal_comp.deriv

/-- The explicit derivative of the complex cutoff product belongs to `L²`, as required by
`productCutoffFourierBounds` for `\label{lem:product-cutoff-fourier}`. -/
lemma aux_productCutoffDerivativeMemLpTwo (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) (u : ℝ) :
    MemLp (fun t : ℝ ↦
      ((deriv ψ t * ψ (t + u) + ψ t * deriv ψ (t + u) : ℝ) : ℂ))
      (2 : ℝ≥0∞) volume := by
  have hs : ContDiff ℝ 1 (fun t : ℝ ↦ ψ t * ψ (t + u)) :=
    aux_productCutoffSmooth ψ hψ u
  have hc : HasCompactSupport (fun t : ℝ ↦ ψ t * ψ (t + u)) :=
    aux_productCutoffCompact ψ hψc u
  have hder : HasCompactSupport (deriv (fun t : ℝ ↦ ψ t * ψ (t + u))) := hc.deriv
  have hcont : Continuous (deriv (fun t : ℝ ↦ ψ t * ψ (t + u))) := by
    exact hs.continuous_deriv (by norm_num)
  have hmem : MemLp (deriv (fun t : ℝ ↦ ψ t * ψ (t + u)))
      (2 : ℝ≥0∞) volume := hcont.memLp_of_hasCompactSupport hder
  convert hmem.ofReal using 1
  funext t
  exact congrArg Complex.ofReal (aux_productCutoffDerivativeFormula ψ hψ u t).symm

/--
Let \(\psi\in C_c^1(\mathbb R)\) satisfy \(0\leq\psi\leq1\). Define
\[
C_{\ref{lem:product-cutoff-fourier},\,\psi}
:=
\sqrt2\lVert\psi\rVert_2+\frac{\sqrt2}{\pi}\lVert\psi'\rVert_2.
\]
Then, for every \(u\in\mathbb R\),
\[
\left\lVert\mathcal F\{\psi(\cdot)\psi(\cdot+u)\}\right\rVert_1
\leq
C_{\ref{lem:product-cutoff-fourier},\,\psi}.
\]
-/
theorem productCutoffFourierBounds
    (ψ : ℝ → ℝ)
    (hψ_smooth : ContDiff ℝ 1 ψ) (hψ_compact : HasCompactSupport ψ)
    (hψ_nonneg : ∀ t : ℝ, 0 ≤ ψ t) (hψ_le_one : ∀ t : ℝ, ψ t ≤ 1) :
    ∀ u : ℝ,
      (eLpNorm
          (𝓕 (fun t : ℝ ↦ ((ψ t * ψ (t + u) : ℝ) : ℂ)))
          (1 : ℝ≥0∞) volume).toReal ≤
        C_productCutoffFourierBounds ψ := by
  intro u
  let f : ℝ → ℂ := fun t ↦ ((ψ t * ψ (t + u) : ℝ) : ℂ)
  let df : ℝ → ℂ := fun t ↦
    ((deriv ψ t * ψ (t + u) + ψ t * deriv ψ (t + u) : ℝ) : ℂ)
  have hfs : ContDiff ℝ 1 f := by
    change ContDiff ℝ 1 (Complex.ofRealCLM ∘ fun t : ℝ ↦ ψ t * ψ (t + u))
    exact Complex.ofRealCLM.contDiff.comp (aux_productCutoffSmooth ψ hψ_smooth u)
  have hfc : HasCompactSupport f := by
    change HasCompactSupport (Complex.ofRealCLM ∘ fun t : ℝ ↦ ψ t * ψ (t + u))
    exact (aux_productCutoffCompact ψ hψ_compact u).comp_left rfl
  have hf1 : MemLp f (1 : ℝ≥0∞) volume := by
    exact aux_productCutoffMemLpOne ψ hψ_smooth hψ_compact u
  have hf2 : MemLp f (2 : ℝ≥0∞) volume := by
    exact aux_productCutoffMemLpTwo ψ hψ_smooth hψ_compact u
  have hdf2 : MemLp df (2 : ℝ≥0∞) volume := by
    exact aux_productCutoffDerivativeMemLpTwo ψ hψ_smooth hψ_compact u
  have hdf : ∀ x : ℝ, deriv f x = df x := by
    intro x
    exact aux_productCutoffDerivativeComplexFormula ψ hψ_smooth u x
  have hweak := aux_weakDerivativeOfContDiffCompact f df hfs hfc hf2 hdf hdf2
  have hfourier := aux_fourierL1LeFromWeakDerivative (hf2.toLp f) (hdf2.toLp df) hweak
  have hraw := aux_l2Fourier_eq_raw_ae f hf1 hf2
  have hrawnorm :
      (eLpNorm (𝓕 f) (1 : ℝ≥0∞) volume).toReal =
        (eLpNorm (fun ξ : ℝ ↦ (Lp.fourierTransformₗᵢ ℝ ℂ hf2.toLp) ξ)
          (1 : ℝ≥0∞) volume).toReal := by
    rw [eLpNorm_congr_ae (Filter.EventuallyEq.symm hraw)]
  rw [show (fun t : ℝ ↦ ((ψ t * ψ (t + u) : ℝ) : ℂ)) = f by rfl]
  rw [hrawnorm]
  have hψmem : MemLp ψ (2 : ℝ≥0∞) volume :=
    hψ_smooth.continuous.memLp_of_hasCompactSupport hψ_compact
  have hdermem : MemLp (deriv ψ) (2 : ℝ≥0∞) volume :=
    (hψ_smooth.continuous_deriv (by norm_num)).memLp_of_hasCompactSupport hψ_compact.deriv
  have hgnorm : ‖hf2.toLp f‖ ≤ (eLpNorm ψ (2 : ℝ≥0∞) volume).toReal := by
    rw [Lp.norm_toLp]
    rw [show eLpNorm f (2 : ℝ≥0∞) volume =
        eLpNorm (fun t : ℝ ↦ ψ t * ψ (t + u)) (2 : ℝ≥0∞) volume by
      change eLpNorm (fun t : ℝ ↦ ((ψ t * ψ (t + u) : ℝ) : ℂ)) (2 : ℝ≥0∞) volume = _
      exact aux_eLpNormRealToComplex _ _]
    exact ENNReal.toReal_mono hψmem.eLpNorm_ne_top
      (aux_productCutoffELpNormBound ψ hψ_nonneg hψ_le_one u)
  have hdfnorm : ‖hdf2.toLp df‖ ≤
      2 * (eLpNorm (deriv ψ) (2 : ℝ≥0∞) volume).toReal := by
    rw [Lp.norm_toLp]
    rw [show eLpNorm df (2 : ℝ≥0∞) volume =
        eLpNorm (fun t : ℝ ↦ deriv ψ t * ψ (t + u) + ψ t * deriv ψ (t + u))
          (2 : ℝ≥0∞) volume by
      change eLpNorm (fun t : ℝ ↦
        ((deriv ψ t * ψ (t + u) + ψ t * deriv ψ (t + u) : ℝ) : ℂ))
          (2 : ℝ≥0∞) volume = _
      exact aux_eLpNormRealToComplex _ _]
    calc
      (eLpNorm (fun t : ℝ ↦ deriv ψ t * ψ (t + u) + ψ t * deriv ψ (t + u))
          (2 : ℝ≥0∞) volume).toReal ≤
          (2 * eLpNorm (deriv ψ) (2 : ℝ≥0∞) volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hdermem.eLpNorm_ne_top)
          (aux_productCutoffDerivativeELpNormBound ψ hψ_smooth hψ_nonneg hψ_le_one u)
      _ = 2 * (eLpNorm (deriv ψ) (2 : ℝ≥0∞) volume).toReal := by
        rw [ENNReal.toReal_mul]
        norm_num
  calc
    (eLpNorm (fun ξ : ℝ ↦ (Lp.fourierTransformₗᵢ ℝ ℂ hf2.toLp) ξ)
        (1 : ℝ≥0∞) volume).toReal ≤
      Real.sqrt 2 * ‖hf2.toLp f‖ +
        (Real.sqrt 2 / (2 * Real.pi)) * ‖hdf2.toLp df‖ := hfourier
    _ ≤ Real.sqrt 2 * (eLpNorm ψ (2 : ℝ≥0∞) volume).toReal +
        (Real.sqrt 2 / (2 * Real.pi)) *
          (2 * (eLpNorm (deriv ψ) (2 : ℝ≥0∞) volume).toReal) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hgnorm (Real.sqrt_nonneg _))
        (mul_le_mul_of_nonneg_left hdfnorm (by positivity))
    _ = C_productCutoffFourierBounds ψ := by
      simp [C_productCutoffFourierBounds]
      have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      field_simp

/-- The final coefficient comparison for the χ-specialization in
`productCutoffFourierBoundsChi` and `\label{lem:product-cutoff-fourier}`. -/
lemma aux_productCutoffChiConstantAlgebra (x y a b : ℝ) (hx : x ≤ a) (hy : y ≤ 2 * b) :
    Real.sqrt 2 * x + (Real.sqrt 2 / Real.pi) * y ≤
      Real.sqrt 2 * a + ((2 * Real.sqrt 2) / Real.pi) * b := by
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hden : 0 ≤ Real.pi := by positivity
  have hcoef : 0 ≤ Real.sqrt 2 / Real.pi := div_nonneg hsqrt hden
  calc
    Real.sqrt 2 * x + (Real.sqrt 2 / Real.pi) * y ≤
        Real.sqrt 2 * a + (Real.sqrt 2 / Real.pi) * (2 * b) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hx hsqrt)
        (mul_le_mul_of_nonneg_left hy hcoef)
    _ = Real.sqrt 2 * a + ((2 * Real.sqrt 2) / Real.pi) * b := by ring

/--
For \(\psi_h(t):=\chi(t)\chi(t+h)\), one has the uniform explicit bound
\[
C_{\ref{lem:product-cutoff-fourier},\,\psi_h}
\leq
\sqrt2\lVert\chi\rVert_2+\frac{2\sqrt2}{\pi}\lVert\chi'\rVert_2.
\]
-/
theorem productCutoffFourierBoundsChi
    (χ : ℝ → ℝ)
    (hχ_smooth : ContDiff ℝ 1 χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1) :
    ∀ h : ℝ,
      C_productCutoffFourierBounds (fun t : ℝ ↦ χ t * χ (t + h)) ≤
        Real.sqrt 2 * (eLpNorm χ (2 : ℝ≥0∞) volume).toReal +
          ((2 * Real.sqrt 2) / Real.pi) *
            (eLpNorm (deriv χ) (2 : ℝ≥0∞) volume).toReal := by
  intro h
  have hχmem : MemLp χ (2 : ℝ≥0∞) volume :=
    hχ_smooth.continuous.memLp_of_hasCompactSupport hχ_compact
  have hderχmem : MemLp (deriv χ) (2 : ℝ≥0∞) volume :=
    (hχ_smooth.continuous_deriv (by norm_num)).memLp_of_hasCompactSupport hχ_compact.deriv
  have hprod :
      eLpNorm (fun t : ℝ ↦ χ t * χ (t + h)) (2 : ℝ≥0∞) volume ≤
        eLpNorm χ (2 : ℝ≥0∞) volume :=
    aux_productCutoffELpNormBound χ hχ_nonneg hχ_le_one h
  have hderiv_fun :
      deriv (fun s : ℝ ↦ χ s * χ (s + h)) =
        fun t : ℝ ↦ deriv χ t * χ (t + h) + χ t * deriv χ (t + h) := by
    funext t
    exact aux_productCutoffDerivativeFormula χ hχ_smooth h t
  have hderiv :
      eLpNorm (deriv (fun s : ℝ ↦ χ s * χ (s + h))) (2 : ℝ≥0∞) volume ≤
        2 * eLpNorm (deriv χ) (2 : ℝ≥0∞) volume := by
    rw [hderiv_fun]
    exact aux_productCutoffDerivativeELpNormBound χ hχ_smooth hχ_nonneg hχ_le_one h
  have hprod_real :
      (eLpNorm (fun t : ℝ ↦ χ t * χ (t + h)) (2 : ℝ≥0∞) volume).toReal ≤
        (eLpNorm χ (2 : ℝ≥0∞) volume).toReal :=
    ENNReal.toReal_mono hχmem.eLpNorm_ne_top hprod
  have hderiv_real :
      (eLpNorm (deriv (fun s : ℝ ↦ χ s * χ (s + h))) (2 : ℝ≥0∞) volume).toReal ≤
        2 * (eLpNorm (deriv χ) (2 : ℝ≥0∞) volume).toReal := by
    calc
      (eLpNorm (deriv (fun s : ℝ ↦ χ s * χ (s + h))) (2 : ℝ≥0∞) volume).toReal ≤
          (2 * eLpNorm (deriv χ) (2 : ℝ≥0∞) volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hderχmem.eLpNorm_ne_top) hderiv
      _ = 2 * (eLpNorm (deriv χ) (2 : ℝ≥0∞) volume).toReal := by
        rw [ENNReal.toReal_mul]
        norm_num
  change Real.sqrt 2 *
      (eLpNorm (fun t : ℝ ↦ χ t * χ (t + h)) (2 : ℝ≥0∞) volume).toReal +
      (Real.sqrt 2 / Real.pi) *
        (eLpNorm (deriv (fun s : ℝ ↦ χ s * χ (s + h))) (2 : ℝ≥0∞) volume).toReal ≤
    Real.sqrt 2 * (eLpNorm χ (2 : ℝ≥0∞) volume).toReal +
      ((2 * Real.sqrt 2) / Real.pi) *
        (eLpNorm (deriv χ) (2 : ℝ≥0∞) volume).toReal
  exact aux_productCutoffChiConstantAlgebra _ _ _ _ hprod_real hderiv_real

end Auto
