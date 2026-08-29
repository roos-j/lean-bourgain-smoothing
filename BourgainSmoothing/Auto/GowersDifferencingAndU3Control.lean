import BourgainSmoothing.Auto.FourierEstimatesForProductsOfCutoffs
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Group.Prod

/-!
# Gowers differencing and \(u^3\) control

Formalizations of the labeled estimates in the corresponding section of
`blueprint/blueprint.tex`.
-/

noncomputable section

open MeasureTheory Set FourierTransform
open scoped ENNReal Real FourierTransform Convolution

namespace Auto

/-- The constant in \(\label{prop:gowers-differencing}\), used by
`gowersDifferencing`:
\[
C_{\ref{prop:gowers-differencing},\,A,J,\psi}
:=
2^2\Ssize{A,J}{\psi}^{2}.
\]
-/
def C_gowersDifferencing (A J : Set ℝ) (ψ : ℝ → ℝ) : ℝ :=
  (2 : ℝ) ^ 2 * sizeParameter ![A, J] ψ ^ 2

/-- This is the one-dimensional coordinate form of the `u^3` quantity used in
the proof of \(\label{prop:gowers-differencing}\) by `gowersDifferencing`.
It removes the singleton `Fin 1 → ℝ` parameter occurring in the foundational
definition. -/
lemma aux_uNorm_three_eq_real_parameter (f : ℝ → ℂ) :
    uNorm 3 f =
      (∫⁻ h : ℝ, eLpNorm (𝓕 (multiplicativeDifference h f)) ∞ volume) ^
        (1 / (2 : ℝ)) := by
  have hunfold :
      uNorm 3 f =
        (∫⁻ h : Fin 1 → ℝ,
          eLpNorm (𝓕 (iteratedMultiplicativeDifference 1 h f)) ∞ volume) ^
          (1 / (2 : ℝ)) := by
    norm_num [uNorm]
  rw [hunfold]
  let e : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.piUnique _
  have he : MeasurePreserving e volume volume :=
    volume_preserving_piUnique _
  congr 1
  rw [he.lintegral_map_equiv
    (fun h : ℝ ↦ eLpNorm (𝓕 (multiplicativeDifference h f)) ∞ volume) e]
  apply lintegral_congr
  intro h
  simp [e, iteratedMultiplicativeDifference]

/-- The squared coordinate form of the `u^3` quantity used in
\(\label{prop:gowers-differencing}\) by `gowersDifferencing`.  It is the
form matched directly by the final integration in the Gowers differencing
argument. -/
lemma aux_uNorm_three_sq_real_parameter (f : ℝ → ℂ) :
    (uNorm 3 f) ^ (2 : ℝ) =
      ∫⁻ h : ℝ, eLpNorm (𝓕 (multiplicativeDifference h f)) ∞ volume := by
  rw [aux_uNorm_three_eq_real_parameter, ← ENNReal.rpow_mul]
  norm_num

/-- A compactly supported, almost-everywhere one-bounded input is in every
`Lᵖ` space.  This packages the integrability bookkeeping needed for the
compact controlled input and its multiplicative differences in
\(\label{prop:gowers-differencing}\), formalized by `gowersDifferencing`. -/
lemma aux_memLp_of_ae_bound_hasCompactSupport
    (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1) (hcompact : HasCompactSupport f)
    (p : ℝ≥0∞) : MemLp f p volume := by
  exact hcompact.memLp_of_bound hf 1 hbound

/-- The affine coordinate `p ↦ p₀ + c p₁` is quasi-measure-preserving from
two-dimensional Lebesgue measure to one-dimensional Lebesgue measure.  This
allows the measurable and almost-everywhere bounded input hypotheses in
\(\label{prop:gowers-differencing}\) to be pulled back to the `(x,t)`
variables used by `gowersDifferencing`. -/
lemma aux_quasiMeasurePreserving_affine (c : ℝ) :
    Measure.QuasiMeasurePreserving (fun p : ℝ × ℝ ↦ p.1 + c * p.2)
      (volume.prod volume) volume := by
  refine QuasiMeasurePreserving.prod_of_left (by fun_prop)
    (Filter.Eventually.of_forall fun t ↦ ?_)
  exact (measurePreserving_add_right volume (c * t)).quasiMeasurePreserving

/-- Pullback of an almost-everywhere strongly measurable input along the
affine coordinate used in \(\label{prop:gowers-differencing}\), formalized
by `gowersDifferencing`. -/
lemma aux_aestronglyMeasurable_comp_affine
    (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume) (c : ℝ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ ↦ f (p.1 + c * p.2))
      (volume.prod volume) := by
  exact hf.comp_quasiMeasurePreserving (aux_quasiMeasurePreserving_affine c)

/-- The affine two-variable change of variables used in the Fourier part of
\(\label{prop:gowers-differencing}\), formalized by `gowersDifferencing`.
The statement records the exact determinant factor for Lebesgue measure. -/
lemma aux_integral_comp_linearMap_volume
    (L : (Fin 2 → ℝ) →ₗ[ℝ] Fin 2 → ℝ)
    (hdet : LinearMap.det L ≠ 0)
    (F : (Fin 2 → ℝ) → ℂ)
    (hF : AEStronglyMeasurable F volume) :
    ∫ x : Fin 2 → ℝ, F (L x) =
      |(LinearMap.det L)⁻¹| • ∫ y : Fin 2 → ℝ, F y := by
  have hmap : Measure.map L volume = ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume :=
    Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet
  have hFmap : AEStronglyMeasurable F (Measure.map L volume) := by
    rw [hmap]
    exact hF.mono_ac Measure.smul_absolutelyContinuous
  calc
    ∫ x : Fin 2 → ℝ, F (L x) = ∫ y : Fin 2 → ℝ, F y ∂Measure.map L volume := by
      exact (integral_map (LinearMap.continuous_of_finiteDimensional L).measurable.aemeasurable
        hFmap).symm
    _ = ∫ y : Fin 2 → ℝ, F y ∂(ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume) := by
      rw [hmap]
    _ = |(LinearMap.det L)⁻¹| • ∫ y : Fin 2 → ℝ, F y := by
      rw [integral_smul_measure]
      simp

/-- Multiplicative differences of the compact controlled input in
\(\label{prop:gowers-differencing}\), formalized by `gowersDifferencing`,
are integrable and square-integrable.  This is the prerequisite for comparing
their raw and `L²` Fourier transforms. -/
lemma aux_memLp_multiplicativeDifference_of_ae_bound_hasCompactSupport
    (g : ℝ → ℂ) (hgmeas : AEStronglyMeasurable g volume)
    (hgbdd : ∀ᵐ x ∂volume, ‖g x‖ ≤ 1) (hcomp : HasCompactSupport g) (h : ℝ) :
    MemLp (multiplicativeDifference h g) (1 : ℝ≥0∞) volume ∧
      MemLp (multiplicativeDifference h g) (2 : ℝ≥0∞) volume := by
  have hshiftmeas : AEStronglyMeasurable (fun x : ℝ ↦ g (x + h)) volume := by
    simpa only [Function.comp_def] using
      hgmeas.comp_quasiMeasurePreserving
        (measurePreserving_add_right volume h).quasiMeasurePreserving
  have hdiffmeas : AEStronglyMeasurable (multiplicativeDifference h g) volume := by
    exact hgmeas.mul hshiftmeas.star
  have hshiftbdd : ∀ᵐ x ∂volume, ‖g (x + h)‖ ≤ 1 := by
    exact (measurePreserving_add_right volume h).quasiMeasurePreserving.tendsto_ae.eventually hgbdd
  have hdiffbdd : ∀ᵐ x ∂volume, ‖multiplicativeDifference h g x‖ ≤ 1 := by
    filter_upwards [hgbdd, hshiftbdd] with x hx hxshift
    have hprod : ‖g x‖ * ‖g (x + h)‖ ≤ 1 := by
      nlinarith [norm_nonneg (g x), norm_nonneg (g (x + h))]
    simpa [multiplicativeDifference] using hprod
  have hdiffcomp : HasCompactSupport (multiplicativeDifference h g) := by
    exact hcomp.mul_right
  exact ⟨hdiffcomp.memLp_of_bound hdiffmeas 1 hdiffbdd,
    hdiffcomp.memLp_of_bound hdiffmeas 1 hdiffbdd⟩

/-- A one-bounded input has one-bounded multiplicative differences.  This
is the pointwise norm bookkeeping for the localized Fourier factors in
`gowersDifferencing`. -/
lemma aux_multiplicativeDifference_ae_one_bounded
    (g : ℝ → ℂ) (hgbdd : ∀ᵐ x ∂volume, ‖g x‖ ≤ 1) (h : ℝ) :
    ∀ᵐ x ∂volume, ‖multiplicativeDifference h g x‖ ≤ 1 := by
  have hshiftbdd : ∀ᵐ x ∂volume, ‖g (x + h)‖ ≤ 1 := by
    exact (measurePreserving_add_right volume h).quasiMeasurePreserving.tendsto_ae.eventually hgbdd
  filter_upwards [hgbdd, hshiftbdd] with x hx hxshift
  have hprod : ‖g x‖ * ‖g (x + h)‖ ≤ 1 := by
    nlinarith [norm_nonneg (g x), norm_nonneg (g (x + h))]
  simpa [multiplicativeDifference] using hprod

/-- The raw Fourier transform is bounded by the `L¹` norm.  This supplies the
measurable `L^∞` input needed in the Fourier duality portion of
\(\label{prop:gowers-differencing}\), formalized by `gowersDifferencing`. -/
lemma aux_eLpNorm_fourier_le_integral_norm (f : ℝ → ℂ) :
    eLpNorm (𝓕 f) ∞ volume ≤ ENNReal.ofReal (∫ x : ℝ, ‖f x‖) := by
  rw [eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards with ξ
  exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ) f ξ

/-- Fourier inversion turns a physical-space pairing against a continuous
kernel with integrable Fourier transform into a Fourier-side pairing.  This
is the kernel-duality step used in the Fourier estimate inside
\(\label{prop:gowers-differencing}\), formalized by `gowersDifferencing`. -/
lemma aux_integral_mul_eq_fourier_pairing
    (f k : ℝ → ℂ) (hf : Integrable f volume) (hk : Integrable k volume)
    (hFk : Integrable (𝓕 k) volume) (hkc : Continuous k) :
    ∫ x : ℝ, f x * k x = ∫ ξ : ℝ, (𝓕 k ξ) * (𝓕 f (-ξ)) := by
  have hinv : 𝓕⁻ (𝓕 k) = k :=
    Continuous.fourierInv_fourier_eq hkc hk hFk
  calc
    ∫ x : ℝ, f x * k x = ∫ x : ℝ, (𝓕⁻ (𝓕 k)) x * f x := by
      rw [hinv]
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = ∫ ξ : ℝ, (𝓕 k ξ) * (𝓕⁻ f) ξ := by
      have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
        (μ := volume) (ν := volume) (L := -(innerₗ ℝ))
        Real.continuous_fourierChar (continuous_inner.neg) hFk hf
      simpa [VectorFourier.fourierIntegral, Real.fourierInv_eq, smul_eq_mul,
        neg_apply, LinearMap.flip_apply, mul_comm] using h
    _ = ∫ ξ : ℝ, (𝓕 k ξ) * (𝓕 f (-ξ)) := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [Real.fourierInv_eq_fourier_neg]

/-- The `L^∞`--`L¹` bound for the Fourier pairing from
`aux_integral_mul_eq_fourier_pairing`.  The raw Fourier transform of an
integrable function has finite essential supremum, so the bound can be stated
with the manuscript's `eLpNorm` convention.  This is used in the Fourier
portion of \(\label{prop:gowers-differencing}\), formalized by
`gowersDifferencing`. -/
lemma aux_norm_integral_mul_le_fourier_pairing
    (f k : ℝ → ℂ) (hf : Integrable f volume) (hk : Integrable k volume)
    (hFk : Integrable (𝓕 k) volume) (hkc : Continuous k) :
    ‖∫ x : ℝ, f x * k x‖ ≤
      (eLpNorm (𝓕 f) ∞ volume).toReal * ∫ ξ : ℝ, ‖𝓕 k ξ‖ := by
  have hlinfty : eLpNorm (𝓕 f) ∞ volume ≤ ENNReal.ofReal (∫ x : ℝ, ‖f x‖) := by
    rw [eLpNorm_exponent_top]
    apply eLpNormEssSup_le_of_ae_enorm_bound
    filter_upwards with ξ
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal
      (VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ) f ξ)
  have htop : eLpNorm (𝓕 f) ∞ volume ≠ ∞ := by
    apply ne_of_lt
    exact lt_of_le_of_lt hlinfty ENNReal.ofReal_lt_top
  have hess : ∀ᵐ ξ : ℝ ∂volume,
      ‖𝓕 f ξ‖ₑ ≤ eLpNorm (𝓕 f) ∞ volume := by
    simpa only [eLpNorm_exponent_top] using
      (MeasureTheory.ae_le_eLpNormEssSup (f := 𝓕 f) (μ := volume))
  have hreflect : ∀ᵐ ξ : ℝ ∂volume,
      ‖𝓕 f (-ξ)‖ₑ ≤ eLpNorm (𝓕 f) ∞ volume := by
    exact (Measure.measurePreserving_neg volume).quasiMeasurePreserving.tendsto_ae hess
  rw [aux_integral_mul_eq_fourier_pairing f k hf hk hFk hkc, ← integral_const_mul]
  apply MeasureTheory.norm_integral_le_of_norm_le
    ((hFk.norm).const_mul (eLpNorm (𝓕 f) ∞ volume).toReal)
  filter_upwards [hreflect] with ξ hξ
  rw [norm_mul]
  have hξ' : ENNReal.ofReal ‖𝓕 f (-ξ)‖ ≤ eLpNorm (𝓕 f) ∞ volume := by
    simpa only [ofReal_norm] using hξ
  have hreal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top htop).mpr hξ'
  have hnonneg : 0 ≤ ‖𝓕 k ξ‖ := norm_nonneg _
  have hbound : ‖𝓕 f (-ξ)‖ ≤ (eLpNorm (𝓕 f) ∞ volume).toReal := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (norm_nonneg _)] using hreal
  nlinarith

/-- Plancherel gives the Fourier pairing identity for merely measurable
`L¹ ∩ L²` functions.  Unlike `aux_integral_mul_eq_fourier_pairing`, this
version does not impose a continuity hypothesis on the second factor.  It is
the form required for the rough bounded factors in
\(\label{prop:gowers-differencing}\), formalized by `gowersDifferencing`. -/
lemma aux_integral_mul_eq_l2Fourier_pairing
    (f k : ℝ → ℂ)
    (hf1 : MemLp f (1 : ℝ≥0∞) volume) (hf2 : MemLp f (2 : ℝ≥0∞) volume)
    (hk1 : MemLp k (1 : ℝ≥0∞) volume) (hk2 : MemLp k (2 : ℝ≥0∞) volume) :
    ∫ x : ℝ, f x * k x = ∫ ξ : ℝ, (𝓕 f (-ξ)) * (𝓕 k ξ) := by
  have hfst1 : MemLp (star f) (1 : ℝ≥0∞) volume := hf1.star
  have hfst2 : MemLp (star f) (2 : ℝ≥0∞) volume := hf2.star
  have hrawf := aux_l2Fourier_eq_raw_ae (star f) hfst1 hfst2
  have hrawk := aux_l2Fourier_eq_raw_ae k hk1 hk2
  have hconj : 𝓕 (star f) = fun ξ ↦ starRingEnd ℂ ((𝓕 f) (-ξ)) := by
    change 𝓕 (fun x : ℝ ↦ starRingEnd ℂ (f x)) = _
    exact aux_fourier_conj f
  have hplanch := Lp.inner_fourier_eq hfst2.toLp hk2.toLp
  calc
    ∫ x : ℝ, f x * k x = inner ℂ hfst2.toLp hk2.toLp := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hfst2.coeFn_toLp, hk2.coeFn_toLp] with x hfx hkx
      rw [RCLike.inner_apply, hfx, hkx]
      change f x * k x = k x * star (star (f x))
      simp [mul_comm]
    _ = inner ℂ (𝓕 hfst2.toLp) (𝓕 hk2.toLp) := hplanch.symm
    _ = ∫ ξ : ℝ, (𝓕 f (-ξ)) * (𝓕 k ξ) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hrawf, hrawk] with ξ hξf hξk
      rw [hconj] at hξf
      change inner ℂ
          ((Lp.fourierTransformₗᵢ ℝ ℂ hfst2.toLp) ξ)
          ((Lp.fourierTransformₗᵢ ℝ ℂ hk2.toLp) ξ) = _
      rw [RCLike.inner_apply, hξf, hξk]
      change 𝓕 k ξ * star (star (𝓕 f (-ξ))) = 𝓕 f (-ξ) * 𝓕 k ξ
      simp [mul_comm]

/-- The raw Fourier transform under a non-singular scalar change of variables.
This records one of the affine-frequency transformations used in the Fourier
estimate within \(\label{prop:gowers-differencing}\), formalized by
`gowersDifferencing`. -/
lemma aux_fourier_comp_mul (f : ℝ → ℂ) (a ξ : ℝ) (ha : a ≠ 0) :
    𝓕 (fun x : ℝ ↦ f (a * x)) ξ =
      |a⁻¹| • 𝓕 f (a⁻¹ * ξ) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  change (∫ x : ℝ, 𝐞 (-(x * ξ)) • f (a * x)) =
    |a⁻¹| • ∫ y : ℝ, 𝐞 (-(y * (a⁻¹ * ξ))) • f y
  have hphase : (fun y : ℝ ↦ 𝐞 (-(y * (a⁻¹ * ξ))) • f y) =
      fun y : ℝ ↦ 𝐞 (-((a⁻¹ * y) * ξ)) • f y := by
    funext y
    congr 2
    ring
  rw [hphase]
  rw [← Measure.integral_comp_mul_left
    (fun y : ℝ ↦ 𝐞 (-((a⁻¹ * y) * ξ)) • f y) a]
  apply integral_congr_ae
  filter_upwards with x
  congr 2
  field_simp

/-- Modulating an input translates its raw Fourier transform.  This is the
frequency shift used after Fourier inversion of the cutoff in
\(\label{prop:gowers-differencing}\), formalized by `gowersDifferencing`. -/
lemma aux_fourier_modulate (f : ℝ → ℂ) (s ξ : ℝ) :
    𝓕 (fun x : ℝ ↦ 𝐞 (s * x) • f x) ξ = 𝓕 f (ξ - s) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  apply integral_congr_ae
  filter_upwards with x
  rw [smul_smul, ← AddChar.map_add_eq_mul]
  congr 2
  ring

/-- The Fourier transform of an `L¹` convolution has an `L¹` bound obtained
by Plancherel and Cauchy--Schwarz from the two `L²` inputs.  This is the
convolution estimate used to control the modulated affine kernel in
\(\label{prop:gowers-differencing}\), formalized by `gowersDifferencing`. -/
lemma aux_fourier_convolution_l1_le_l2
    (f g : ℝ → ℂ)
    (hf1 : MemLp f (1 : ℝ≥0∞) volume) (hf2 : MemLp f (2 : ℝ≥0∞) volume)
    (hg1 : MemLp g (1 : ℝ≥0∞) volume) (hg2 : MemLp g (2 : ℝ≥0∞) volume) :
    (eLpNorm (𝓕 (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g))
        (1 : ℝ≥0∞) volume).toReal ≤
      (eLpNorm f (2 : ℝ≥0∞) volume).toReal *
        (eLpNorm g (2 : ℝ≥0∞) volume).toReal := by
  have hrawf := aux_l2Fourier_eq_raw_ae f hf1 hf2
  have hrawg := aux_l2Fourier_eq_raw_ae g hg1 hg2
  have hFf : MemLp (𝓕 f) (2 : ℝ≥0∞) volume := by
    refine (memLp_congr_ae (Filter.EventuallyEq.symm hrawf)).mpr ?_
    exact Lp.memLp (Lp.fourierTransformₗᵢ ℝ ℂ hf2.toLp)
  have hFg : MemLp (𝓕 g) (2 : ℝ≥0∞) volume := by
    refine (memLp_congr_ae (Filter.EventuallyEq.symm hrawg)).mpr ?_
    exact Lp.memLp (Lp.fourierTransformₗᵢ ℝ ℂ hg2.toLp)
  have hconv : ∀ ξ : ℝ,
      𝓕 (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) ξ = (𝓕 f ξ) * (𝓕 g ξ) :=
    fun ξ ↦ Real.fourier_mul_convolution_eq
      (memLp_one_iff_integrable.mp hf1) (memLp_one_iff_integrable.mp hg1) ξ
  rw [show 𝓕 (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) =
      fun ξ ↦ 𝓕 f ξ * 𝓕 g ξ by
    funext ξ
    exact hconv ξ]
  change (eLpNorm (𝓕 f * 𝓕 g) (1 : ℝ≥0∞) volume).toReal ≤ _
  have hprod : MemLp (𝓕 f * 𝓕 g) (1 : ℝ≥0∞) volume := hFg.mul hFf
  rw [toReal_eLpNorm hprod.aestronglyMeasurable]
  rw [lpNorm_one_eq_integral_norm hprod.aestronglyMeasurable]
  calc
    ∫ x : ℝ, ‖𝓕 f x * 𝓕 g x‖ = ∫ x : ℝ, ‖𝓕 f x‖ * ‖𝓕 g x‖ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [norm_mul]
    _ ≤ (∫ x : ℝ, ‖𝓕 f x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (∫ x : ℝ, ‖𝓕 g x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
      have hFf' : MemLp (𝓕 f) (ENNReal.ofReal (2 : ℝ)) volume := by
        norm_num
        exact hFf
      have hFg' : MemLp (𝓕 g) (ENNReal.ofReal (2 : ℝ)) volume := by
        norm_num
        exact hFg
      simpa using (integral_mul_norm_le_Lp_mul_Lq
        (μ := volume) (p := (2 : ℝ)) (q := (2 : ℝ))
        (by norm_num [Real.holderConjugate_iff]) hFf' hFg')
    _ = (eLpNorm (𝓕 f) (2 : ℝ≥0∞) volume).toReal *
        (eLpNorm (𝓕 g) (2 : ℝ≥0∞) volume).toReal := by
      have hpf : (∫ x : ℝ, ‖𝓕 f x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) =
          (eLpNorm (𝓕 f) (2 : ℝ≥0∞) volume).toReal := by
        rw [toReal_eLpNorm hFf.aestronglyMeasurable,
          lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
            hFf.aestronglyMeasurable]
        norm_num
      have hpg : (∫ x : ℝ, ‖𝓕 g x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) =
          (eLpNorm (𝓕 g) (2 : ℝ≥0∞) volume).toReal := by
        rw [toReal_eLpNorm hFg.aestronglyMeasurable,
          lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
            hFg.aestronglyMeasurable]
        norm_num
      rw [hpf, hpg]
    _ = (eLpNorm f (2 : ℝ≥0∞) volume).toReal *
        (eLpNorm g (2 : ℝ≥0∞) volume).toReal := by
      have hnormf : eLpNorm (𝓕 f) (2 : ℝ≥0∞) volume =
          eLpNorm f (2 : ℝ≥0∞) volume := by
        rw [eLpNorm_congr_ae (Filter.EventuallyEq.symm hrawf)]
        let F := Lp.fourierTransformₗᵢ ℝ ℂ hf2.toLp
        have hnorm : ‖F‖ = ‖hf2.toLp‖ := Lp.norm_fourier_eq hf2.toLp
        calc
          eLpNorm (⇑F) 2 volume = ‖F‖ₑ := (Lp.enorm_def F).symm
          _ = ‖hf2.toLp‖ₑ := by
            rw [← ofReal_norm, ← ofReal_norm, hnorm]
          _ = eLpNorm f 2 volume := Lp.enorm_toLp hf2
      have hnormg : eLpNorm (𝓕 g) (2 : ℝ≥0∞) volume =
          eLpNorm g (2 : ℝ≥0∞) volume := by
        rw [eLpNorm_congr_ae (Filter.EventuallyEq.symm hrawg)]
        let F := Lp.fourierTransformₗᵢ ℝ ℂ hg2.toLp
        have hnorm : ‖F‖ = ‖hg2.toLp‖ := Lp.norm_fourier_eq hg2.toLp
        calc
          eLpNorm (⇑F) 2 volume = ‖F‖ₑ := (Lp.enorm_def F).symm
          _ = ‖hg2.toLp‖ₑ := by
            rw [← ofReal_norm, ← ofReal_norm, hnorm]
          _ = eLpNorm g 2 volume := Lp.enorm_toLp hg2
      rw [hnormf, hnormg]

/-- A one-bounded factor supported almost everywhere on a finite-measure set
has squared energy at most the measure of that set.  This is the support
factor in the first Cauchy--Schwarz step of
\(\label{prop:gowers-differencing}\), formalized by `gowersDifferencing`. -/
lemma aux_energy_le_measure
    (A : Set ℝ) (hAmeas : MeasurableSet A) (hAfin : volume A ≠ ∞)
    (f : ℝ → ℂ) (hf : MemLp f (2 : ℝ≥0∞) volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hzero : ∀ᵐ x ∂volume, x ∉ A → f x = 0) :
    (∫ x : ℝ, ‖f x‖ ^ (2 : ℝ)) ≤ volume.real A := by
  have hfint : Integrable (fun x : ℝ ↦ ‖f x‖ ^ (2 : ℝ)) volume := by
    convert hf.integrable_norm_rpow (by norm_num) (by norm_num) using 1
    norm_num
  have hind : Integrable (A.indicator (fun _ : ℝ ↦ (1 : ℝ))) volume := by
    rw [integrable_indicator_iff hAmeas]
    exact integrableOn_const hAfin
  calc
    (∫ x : ℝ, ‖f x‖ ^ (2 : ℝ)) ≤
        ∫ x : ℝ, A.indicator (fun _ : ℝ ↦ (1 : ℝ)) x := by
      apply integral_mono_ae hfint hind
      filter_upwards [hbound, hzero] with x hxbound hxzero
      by_cases hxA : x ∈ A
      · rw [Set.indicator_of_mem hxA, Real.rpow_two]
        nlinarith [norm_nonneg (f x)]
      · rw [Set.indicator_of_notMem hxA]
        simp [hxzero hxA]
    _ = volume.real A := by
      rw [integral_indicator_const 1 hAmeas]
      simp

/-- The Fubini reordering that puts the difference variable outermost in the
autocorrelation calculation for \(\label{prop:gowers-differencing}\),
formalized by `gowersDifferencing`. -/
lemma aux_triple_integral_swap
    (R : ℝ → ℝ → ℝ → ℂ)
    (hR : Integrable
      (fun p : (ℝ × ℝ) × ℝ ↦ R p.1.1 p.1.2 p.2)
      ((volume.prod volume).prod volume)) :
    (∫ x : ℝ, ∫ t : ℝ, ∫ h : ℝ, R x t h) =
      ∫ h : ℝ, ∫ x : ℝ, ∫ t : ℝ, R x t h := by
  let Q : ℝ × ℝ → ℂ := fun p ↦ ∫ h : ℝ, R p.1 p.2 h
  have hQ : Integrable Q (volume.prod volume) := by
    simpa [Q] using hR.integral_prod_left
  have hfib : ∀ᵐ h : ℝ ∂volume,
      Integrable (fun p : ℝ × ℝ ↦ R p.1 p.2 h) (volume.prod volume) :=
    hR.prod_left_ae
  calc
    (∫ x : ℝ, ∫ t : ℝ, ∫ h : ℝ, R x t h) = ∫ p : ℝ × ℝ, Q p := by
      exact (integral_prod Q hQ).symm
    _ = ∫ h : ℝ, ∫ p : ℝ × ℝ, R p.1 p.2 h :=
      integral_integral_swap hR
    _ = ∫ h : ℝ, ∫ x : ℝ, ∫ t : ℝ, R x t h := by
      apply integral_congr_ae
      filter_upwards [hfib] with h hh
      exact integral_prod _ hh

/-- The elementary coordinate substitution `s = t + h` used in the
autocorrelation expansion for \(\label{prop:gowers-differencing}\),
formalized by `gowersDifferencing`. -/
lemma aux_time_difference_change (K : ℝ → ℝ → ℂ) :
    (∫ t : ℝ, ∫ h : ℝ, K t (t + h)) =
      ∫ t : ℝ, ∫ s : ℝ, K t s := by
  apply integral_congr_ae
  filter_upwards with t
  exact integral_add_left_eq_self (K t) t

/-- Exact autocorrelation expansion of a squared inner integral.  The two
explicit hypotheses are precisely the Fubini obligations; compactly supported
bounded applications in `gowersDifferencing` supply them. -/
lemma aux_autocorrelation
    (P : ℝ → ℝ → ℂ)
    (hKfib : ∀ x : ℝ, Integrable
      (Function.uncurry (fun t s : ℝ ↦ P x t * starRingEnd ℂ (P x s)))
      (volume.prod volume))
    (hR : Integrable
      (fun p : (ℝ × ℝ) × ℝ ↦
        P p.1.1 p.1.2 * starRingEnd ℂ (P p.1.1 (p.1.2 + p.2)))
      ((volume.prod volume).prod volume)) :
    (∫ x : ℝ,
      (∫ t : ℝ, P x t) * starRingEnd ℂ (∫ t : ℝ, P x t)) =
      ∫ h : ℝ, ∫ x : ℝ, ∫ t : ℝ,
        P x t * starRingEnd ℂ (P x (t + h)) := by
  calc
    (∫ x : ℝ,
      (∫ t : ℝ, P x t) * starRingEnd ℂ (∫ t : ℝ, P x t)) =
        ∫ x : ℝ, ∫ z : ℝ × ℝ,
          P x z.1 * starRingEnd ℂ (P x z.2) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [← integral_conj]
      exact (integral_prod_mul (P x) (fun s : ℝ ↦ starRingEnd ℂ (P x s))).symm
    _ = ∫ x : ℝ, ∫ t : ℝ, ∫ s : ℝ,
        P x t * starRingEnd ℂ (P x s) := by
      apply integral_congr_ae
      filter_upwards with x
      exact integral_prod _ (hKfib x)
    _ = ∫ x : ℝ, ∫ t : ℝ, ∫ h : ℝ,
        P x t * starRingEnd ℂ (P x (t + h)) := by
      apply integral_congr_ae
      filter_upwards with x
      exact (aux_time_difference_change
        (fun t s : ℝ ↦ P x t * starRingEnd ℂ (P x s))).symm
    _ = ∫ h : ℝ, ∫ x : ℝ, ∫ t : ℝ,
        P x t * starRingEnd ℂ (P x (t + h)) := by
      simpa using (aux_triple_integral_swap
        (fun x t h : ℝ ↦ P x t * starRingEnd ℂ (P x (t + h))) hR)

/-- The outer Cauchy--Schwarz inequality used before the autocorrelation
expansion in \(\label{prop:gowers-differencing}\), formalized by
`gowersDifferencing`. -/
lemma aux_outer_cauchy
    (f u : ℝ → ℂ) (hf : MemLp f (2 : ℝ≥0∞) volume)
    (hu : MemLp u (2 : ℝ≥0∞) volume) :
    ‖∫ x : ℝ, f x * u x‖ ≤
      (∫ x : ℝ, ‖f x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (∫ x : ℝ, ‖u x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) volume := by
    norm_num
    exact hf
  have hu' : MemLp u (ENNReal.ofReal (2 : ℝ)) volume := by
    norm_num
    exact hu
  calc
    ‖∫ x : ℝ, f x * u x‖ ≤ ∫ x : ℝ, ‖f x * u x‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x : ℝ, ‖f x‖ * ‖u x‖ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [norm_mul]
    _ ≤ (∫ x : ℝ, ‖f x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (∫ x : ℝ, ‖u x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
      integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hf' hu'

/-- The compact interaction range of a factor evaluated at `x + c t`, with
`x` in the outer interval and `t` in the cutoff interval.  It is used to
localize the two non-uniform factors before the Cauchy--Schwarz step in
\(\label{prop:gowers-differencing}\), formalized by `gowersDifferencing`. -/
def aux_gowersInteractionRange (A J : Set ℝ) (c : ℝ) : Set ℝ :=
  Set.image2 (fun x t : ℝ ↦ x + c * t) A J

/-- Compactness of the interaction range used to localize `g₂` and `g₃` in
the proof of \(\label{prop:gowers-differencing}\), formalized by
`gowersDifferencing`. -/
lemma aux_gowersInteractionRange_compact (A J : Set ℝ) (c : ℝ)
    (hA : IsCompact A) (hJ : IsCompact J) :
    IsCompact (aux_gowersInteractionRange A J c) := by
  rw [aux_gowersInteractionRange, ← Set.image_prod]
  exact (hA.prod hJ).image
    (continuous_fst.add (continuous_const.mul continuous_snd))

/-- Measurability of the compact interaction range used in
\(\label{prop:gowers-differencing}\), formalized by `gowersDifferencing`. -/
lemma aux_gowersInteractionRange_measurable (A J : Set ℝ) (c : ℝ)
    (hA : IsCompact A) (hJ : IsCompact J) :
    MeasurableSet (aux_gowersInteractionRange A J c) :=
  (aux_gowersInteractionRange_compact A J c hA hJ).measurableSet

/-- Explicit interval form of a positive-slope interaction range.  This is
used to control the localized `g₂` and `g₃` factors in
\(\label{prop:gowers-differencing}\), formalized by `gowersDifferencing`. -/
lemma aux_gowersInteractionRange_Icc_of_pos
    (a b p q c : ℝ) (hab : a ≤ b) (hpq : p ≤ q) (hc : 0 < c) :
    aux_gowersInteractionRange (Set.Icc a b) (Set.Icc p q) c =
      Set.Icc (a + c * p) (b + c * q) := by
  ext y
  constructor
  · rintro ⟨x, hx, t, ht, rfl⟩
    rcases hx with ⟨hxa, hxb⟩
    rcases ht with ⟨htp, htq⟩
    change a + c * p ≤ x + c * t ∧ x + c * t ≤ b + c * q
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left htp hc.le,
      mul_le_mul_of_nonneg_left htq hc.le]
  · intro hy
    rcases le_total y (a + c * q) with h | h
    · refine ⟨a, ⟨le_rfl, hab⟩, (y - a) / c, ?_, ?_⟩
      constructor
      · have hdiv : c * ((y - a) / c) = y - a := by field_simp
        nlinarith [hy.1]
      · have hdiv : c * ((y - a) / c) = y - a := by field_simp
        nlinarith
      · have hdiv : c * ((y - a) / c) = y - a := by field_simp
        nlinarith
    · refine ⟨y - c * q, ?_, q, ⟨hpq, le_rfl⟩, ?_⟩
      constructor <;> nlinarith [hy.2]
      ring

/-- Explicit interval form of the zero-slope interaction range used in
\(\label{prop:gowers-differencing}\), formalized by `gowersDifferencing`. -/
lemma aux_gowersInteractionRange_Icc_of_zero
    (a b p q : ℝ) (_hab : a ≤ b) (hpq : p ≤ q) :
    aux_gowersInteractionRange (Set.Icc a b) (Set.Icc p q) 0 = Set.Icc a b := by
  ext y
  constructor
  · rintro ⟨x, hx, t, ht, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨y, hy, p, ⟨le_rfl, hpq⟩, by ring⟩

/-- Explicit interval form of a negative-slope interaction range.  This is
used in the support-size estimate for \(\label{prop:gowers-differencing}\),
formalized by `gowersDifferencing`. -/
lemma aux_gowersInteractionRange_Icc_of_neg
    (a b p q c : ℝ) (hab : a ≤ b) (hpq : p ≤ q) (hc : c < 0) :
    aux_gowersInteractionRange (Set.Icc a b) (Set.Icc p q) c =
      Set.Icc (a + c * q) (b + c * p) := by
  ext y
  constructor
  · rintro ⟨x, hx, t, ht, rfl⟩
    rcases hx with ⟨hxa, hxb⟩
    rcases ht with ⟨htp, htq⟩
    change a + c * q ≤ x + c * t ∧ x + c * t ≤ b + c * p
    constructor <;> nlinarith [mul_le_mul_of_nonpos_left htp hc.le,
      mul_le_mul_of_nonpos_left htq hc.le]
  · intro hy
    rcases le_total y (a + c * p) with h | h
    · refine ⟨a, ⟨le_rfl, hab⟩, (y - a) / c, ?_, ?_⟩
      constructor
      · have hdiv : c * ((y - a) / c) = y - a := by field_simp [ne_of_lt hc]
        nlinarith
      · have hdiv : c * ((y - a) / c) = y - a := by field_simp [ne_of_lt hc]
        nlinarith [hy.1]
      · have hdiv : c * ((y - a) / c) = y - a := by field_simp [ne_of_lt hc]
        nlinarith
    · refine ⟨y - c * p, ?_, p, ⟨le_rfl, hpq⟩, ?_⟩
      constructor <;> nlinarith [hy.2]
      ring

/-- The real measure of an interaction range is controlled by the two input
interval lengths and the coefficient bound.  This supplies the `L²` bounds
for the localized factors in \(\label{prop:gowers-differencing}\),
formalized by `gowersDifferencing`. -/
lemma aux_gowersInteractionRange_volume_real_le
    (a b p q c M : ℝ) (hab : a ≤ b) (hpq : p ≤ q)
    (hMone : 1 ≤ M) (hcM : |c| ≤ M) :
    volume.real (aux_gowersInteractionRange (Set.Icc a b) (Set.Icc p q) c) ≤
      M * ((volume (Set.Icc a b)).toReal + (volume (Set.Icc p q)).toReal) := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · rw [aux_gowersInteractionRange_Icc_of_neg a b p q c hab hpq hc]
    have hba : 0 ≤ b - a := sub_nonneg.mpr hab
    have hqp : 0 ≤ q - p := sub_nonneg.mpr hpq
    have hmc : -c ≤ M := by
      simpa [abs_of_neg hc] using hcM
    have hmul : (-c) * (q - p) ≤ M * (q - p) :=
      mul_le_mul_of_nonneg_right hmc hqp
    have hMa : b - a ≤ M * (b - a) := by
      nlinarith [mul_le_mul_of_nonneg_right hMone hba]
    simp only [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal,
      sub_nonneg.mpr hab, sub_nonneg.mpr hpq,
      sub_nonneg.mpr (by nlinarith [mul_le_mul_of_nonpos_left hpq hc.le] :
        a + c * q ≤ b + c * p)]
    nlinarith
  · rw [aux_gowersInteractionRange_Icc_of_zero a b p q hab hpq]
    have hba : 0 ≤ b - a := sub_nonneg.mpr hab
    have hqp : 0 ≤ q - p := sub_nonneg.mpr hpq
    simp only [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal, hba,
      hqp]
    nlinarith [mul_le_mul_of_nonneg_right hMone hba]
  · rw [aux_gowersInteractionRange_Icc_of_pos a b p q c hab hpq hc]
    have hba : 0 ≤ b - a := sub_nonneg.mpr hab
    have hqp : 0 ≤ q - p := sub_nonneg.mpr hpq
    have hcm : c ≤ M := by
      simpa [abs_of_pos hc] using hcM
    have hmul : c * (q - p) ≤ M * (q - p) :=
      mul_le_mul_of_nonneg_right hcm hqp
    have hMa : b - a ≤ M * (b - a) := by
      nlinarith [mul_le_mul_of_nonneg_right hMone hba]
    simp only [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal, hba,
      hqp, sub_nonneg.mpr (by nlinarith [mul_le_mul_of_nonneg_left hpq hc.le] :
        a + c * p ≤ b + c * q)]
    nlinarith

/-- Interval-hypothesis wrapper for the interaction-range measure estimate
used by `gowersDifferencing` in \(\label{prop:gowers-differencing}\). -/
lemma aux_gowersInteractionRange_volume_real_le_of_intervals
    (A J : Set ℝ) (c M : ℝ)
    (hA : ∃ a b : ℝ, a < b ∧ A = Set.Icc a b)
    (hJ : ∃ p q : ℝ, p < q ∧ J = Set.Icc p q)
    (hMone : 1 ≤ M) (hcM : |c| ≤ M) :
    volume.real (aux_gowersInteractionRange A J c) ≤
      M * ((volume A).toReal + (volume J).toReal) := by
  rcases hA with ⟨a, b, hab, rfl⟩
  rcases hJ with ⟨p, q, hpq, rfl⟩
  exact aux_gowersInteractionRange_volume_real_le a b p q c M hab.le hpq.le hMone hcM

/-- Each interval length entering the two-set size parameter is bounded by
that size parameter.  This is the constant bookkeeping used in
`gowersDifferencing`. -/
lemma aux_intervalLength_le_sizeParameter_two
    (A J : Set ℝ) (ψ : ℝ → ℝ) (i : Fin 2) :
    intervalLength (![A, J] i) ≤ sizeParameter ![A, J] ψ := by
  let v : Fin 2 → ℝ := fun k ↦ intervalLength (![A, J] k)
  have hbdd : BddAbove (Set.range v) := by
    refine ⟨max (intervalLength A) (intervalLength J), ?_⟩
    rintro x ⟨k, rfl⟩
    fin_cases k <;> simp [v, le_max_iff]
  have hmem : intervalLength (![A, J] i) ∈ Set.range v := ⟨i, by simp [v]⟩
  have hsup : intervalLength (![A, J] i) ≤ sSup (Set.range v) := le_csSup hbdd hmem
  let r : ℝ := max (supportRadius ψ ^ 2)
    (max (eLpNorm ψ 1 volume).toReal
      (max (eLpNorm ψ 2 volume).toReal
        (max (eLpNorm (deriv ψ) 1 volume).toReal
          (eLpNorm (deriv ψ) 2 volume).toReal)))
  have hmax : sSup (Set.range v) ≤ max (sSup (Set.range v)) r := le_max_left _ _
  change intervalLength (![A, J] i) ≤ 2 + max (sSup (Set.range v)) r
  linarith

/-- The sum of the two interval lengths is at most twice the corresponding
size parameter.  This bounds the localized interaction ranges in
`gowersDifferencing`. -/
lemma aux_intervalLength_sum_le_two_mul_sizeParameter
    (A J : Set ℝ) (ψ : ℝ → ℝ) :
    intervalLength A + intervalLength J ≤ 2 * sizeParameter ![A, J] ψ := by
  have h0 := aux_intervalLength_le_sizeParameter_two A J ψ 0
  have h1 := aux_intervalLength_le_sizeParameter_two A J ψ 1
  norm_num at h0 h1 ⊢
  linarith

/-- The restriction of a bounded factor to its compact interaction range.
This auxiliary map is used only to make the `g₂` and `g₃` factors globally
integrable in the Fourier part of \(\label{prop:gowers-differencing}\),
formalized by `gowersDifferencing`. -/
def aux_gowersRestrict (B : Set ℝ) (f : ℝ → ℂ) : ℝ → ℂ := B.indicator f

/-- A restricted factor is almost-everywhere strongly measurable whenever
the original factor is.  This supports the localization in
\(\label{prop:gowers-differencing}\), formalized by `gowersDifferencing`. -/
lemma aux_gowersRestrict_aestronglyMeasurable
    (B : Set ℝ) (f : ℝ → ℂ) (hB : MeasurableSet B)
    (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (aux_gowersRestrict B f) volume := by
  exact hf.indicator hB

/-- The unit bound persists under restriction to an interaction range.  This
is used by `gowersDifferencing` for \(\label{prop:gowers-differencing}\). -/
lemma aux_gowersRestrict_ae_one_bounded
    (B : Set ℝ) (f : ℝ → ℂ)
    (hf : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1) :
    ∀ᵐ x ∂volume, ‖aux_gowersRestrict B f x‖ ≤ 1 := by
  filter_upwards [hf] with x hx
  by_cases hB : x ∈ B
  · rw [aux_gowersRestrict, Set.indicator_of_mem hB]
    exact hx
  · rw [aux_gowersRestrict, Set.indicator_of_notMem hB]
    simp

/-- Restriction to a compact interaction range has compact support.  This is
the compactness input for the Fourier estimates in
\(\label{prop:gowers-differencing}\), formalized by `gowersDifferencing`. -/
lemma aux_gowersRestrict_hasCompactSupport
    (B : Set ℝ) (f : ℝ → ℂ) (hB : IsCompact B) :
    HasCompactSupport (aux_gowersRestrict B f) := by
  apply HasCompactSupport.intro hB
  intro x hx
  rw [aux_gowersRestrict, Set.indicator_of_notMem hx]

/-- A measurable unit-bounded factor restricted to a compact interaction
range belongs to every `Lᵖ`.  This provides the global `L¹ ∩ L²` inputs in
the Fourier portion of \(\label{prop:gowers-differencing}\), formalized by
`gowersDifferencing`. -/
lemma aux_gowersRestrict_memLp
    (B : Set ℝ) (f : ℝ → ℂ) (p : ℝ≥0∞)
    (hB : IsCompact B) (hfmeas : AEStronglyMeasurable f volume)
    (hfbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1) :
    MemLp (aux_gowersRestrict B f) p volume := by
  exact (aux_gowersRestrict_hasCompactSupport B f hB).memLp_of_bound
    (aux_gowersRestrict_aestronglyMeasurable B f hB.measurableSet hfmeas)
    1 (aux_gowersRestrict_ae_one_bounded B f hfbound)

/-- An interaction-range restricted factor has multiplicative differences
whose `L²` norm is controlled by the square root of that range's measure.
This is the localized-factor estimate in the Fourier step of
`gowersDifferencing`. -/
lemma aux_eLpNorm_multiplicativeDifference_restrict_le
    (B : Set ℝ) (f : ℝ → ℂ) (h : ℝ) (hB : IsCompact B)
    (hfmeas : AEStronglyMeasurable f volume)
    (hfbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1) :
    (eLpNorm (multiplicativeDifference h (aux_gowersRestrict B f))
      (2 : ℝ≥0∞) volume).toReal ≤ (volume.real B) ^ (1 / (2 : ℝ)) := by
  let F : ℝ → ℂ := aux_gowersRestrict B f
  have hFmeas : AEStronglyMeasurable F volume := by
    exact aux_gowersRestrict_aestronglyMeasurable B f hB.measurableSet hfmeas
  have hFbound : ∀ᵐ x ∂volume, ‖F x‖ ≤ 1 := by
    exact aux_gowersRestrict_ae_one_bounded B f hfbound
  have hFcomp : HasCompactSupport F := aux_gowersRestrict_hasCompactSupport B f hB
  have hdiff := aux_memLp_multiplicativeDifference_of_ae_bound_hasCompactSupport
    F hFmeas hFbound hFcomp h
  have hdiffbound : ∀ᵐ x ∂volume, ‖multiplicativeDifference h F x‖ ≤ 1 := by
    exact aux_multiplicativeDifference_ae_one_bounded F hFbound h
  have hdiffzero : ∀ᵐ x ∂volume, x ∉ B → multiplicativeDifference h F x = 0 := by
    filter_upwards with x
    intro hx
    simp [F, multiplicativeDifference, aux_gowersRestrict,
      Set.indicator_of_notMem hx]
  have henergy : (∫ x : ℝ, ‖multiplicativeDifference h F x‖ ^ (2 : ℝ)) ≤
      volume.real B := by
    exact aux_energy_le_measure B hB.measurableSet hB.measure_lt_top.ne
      (multiplicativeDifference h F) hdiff.2 hdiffbound hdiffzero
  have hnorm : (eLpNorm (multiplicativeDifference h F) (2 : ℝ≥0∞) volume).toReal =
      (∫ x : ℝ, ‖multiplicativeDifference h F x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    rw [toReal_eLpNorm hdiff.2.aestronglyMeasurable,
      lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
        hdiff.2.aestronglyMeasurable]
    norm_num
  change (eLpNorm (multiplicativeDifference h F) (2 : ℝ≥0∞) volume).toReal ≤ _
  rw [hnorm]
  exact Real.rpow_le_rpow
    (integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _) henergy (by norm_num)

/-- A bounded almost-everywhere measurable function supported almost
everywhere on a measurable finite-measure set belongs to every `Lᵖ`.  This
general product-space form supplies the Fubini bookkeeping in
\(\label{prop:gowers-differencing}\), formalized by `gowersDifferencing`. -/
lemma aux_memLp_of_ae_bound_of_ae_support
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (f : α → E) (hf : AEStronglyMeasurable f μ)
    (C : ℝ) (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ C)
    (S : Set α) (hS : MeasurableSet S) (hSfinite : μ S < ∞)
    (hsupp : ∀ᵐ x ∂μ, x ∉ S → f x = 0) (p : ℝ≥0∞) :
    MemLp f p μ := by
  have heq : f =ᵐ[μ] S.indicator f := by
    filter_upwards [hsupp] with x hx
    by_cases hxin : x ∈ S
    · simp [hxin]
    · simp [hxin, hx hxin]
  have hindicator : MemLp (S.indicator f) p μ := by
    rw [memLp_indicator_iff_restrict hS]
    have : Fact (μ S < ∞) := ⟨hSfinite⟩
    exact MemLp.of_bound hf.restrict C (ae_restrict_of_ae hbound)
  exact (memLp_congr_ae heq).mpr hindicator

/-- Before the outer Cauchy--Schwarz step, the two uncontrolled factors may
be restricted to their compact interaction ranges without changing the
integrand almost everywhere.  This is the localization which makes the
subsequent Fourier kernel factors globally integrable in
\(\label{prop:gowers-differencing}\), formalized by `gowersDifferencing`. -/
lemma aux_gowers_integrand_restrict_g2g3_eq_ae
    (A J : Set ℝ) (ψ : ℝ → ℝ) (c : Fin 4 → ℝ) (g : Fin 4 → ℝ → ℂ)
    (hg0support : ∀ᵐ x ∂volume, x ∉ A → g 0 x = 0)
    (hψsupport : tsupport ψ ⊆ J) :
    (fun p : ℝ × ℝ ↦
      g 0 p.1 * g 1 (p.1 + c 1 * p.2) * g 2 (p.1 + c 2 * p.2) *
        g 3 (p.1 + c 3 * p.2) * (ψ p.2 : ℂ)) =ᵐ[volume.prod volume]
      fun p ↦
        g 0 p.1 * g 1 (p.1 + c 1 * p.2) *
          aux_gowersRestrict (aux_gowersInteractionRange A J (c 2)) (g 2)
            (p.1 + c 2 * p.2) *
          aux_gowersRestrict (aux_gowersInteractionRange A J (c 3)) (g 3)
            (p.1 + c 3 * p.2) * (ψ p.2 : ℂ) := by
  have h0prod : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
      p.1 ∉ A → g 0 p.1 = 0 := by
    exact (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).tendsto_ae.eventually
      hg0support
  filter_upwards [h0prod] with p hp0
  by_cases hg0 : g 0 p.1 = 0
  · simp [hg0]
  by_cases hψ : ψ p.2 = 0
  · simp [hψ]
  have hpA : p.1 ∈ A := by
    by_contra hpA
    exact hg0 (hp0 hpA)
  have hpJ : p.2 ∈ J := by
    by_contra hpJ
    have hts : p.2 ∉ tsupport ψ := fun ht ↦ hpJ (hψsupport ht)
    exact hψ (image_eq_zero_of_notMem_tsupport hts)
  have hpB2 : p.1 + c 2 * p.2 ∈ aux_gowersInteractionRange A J (c 2) := by
    rw [aux_gowersInteractionRange]
    exact Set.mem_image2_of_mem hpA hpJ
  have hpB3 : p.1 + c 3 * p.2 ∈ aux_gowersInteractionRange A J (c 3) := by
    rw [aux_gowersInteractionRange]
    exact Set.mem_image2_of_mem hpA hpJ
  rw [aux_gowersRestrict, Set.indicator_of_mem hpB2,
    aux_gowersRestrict, Set.indicator_of_mem hpB3]

/-- The compact spatial projection forced by the compact support of the
first nontrivial factor and the time cutoff in `gowersDifferencing`. -/
def aux_gowersSpatialRange (c : ℝ) (g : ℝ → ℂ) (J : Set ℝ) : Set ℝ :=
  Set.image2 (fun y t : ℝ ↦ y - c * t) (tsupport g) J

/-- The spatial projection used for the time-integral Cauchy--Schwarz step
in `gowersDifferencing` is compact. -/
lemma aux_gowersSpatialRange_compact (c : ℝ) (g : ℝ → ℂ) (J : Set ℝ)
    (hg : HasCompactSupport g) (hJ : IsCompact J) :
    IsCompact (aux_gowersSpatialRange c g J) := by
  rw [aux_gowersSpatialRange, ← Set.image_prod]
  exact (hg.isCompact.prod hJ).image
    (continuous_fst.sub (continuous_const.mul continuous_snd))

/-- The three non-outer factors of the Gowers integrand.  This is the compact
kernel to which the physical autocorrelation reduction is applied in
`gowersDifferencing`. -/
def aux_gowersKernel (c : Fin 4 → ℝ) (g : Fin 4 → ℝ → ℂ)
    (ψ : ℝ → ℝ) : ℝ → ℝ → ℂ :=
  fun x t ↦ g 1 (x + c 1 * t) * g 2 (x + c 2 * t) *
    g 3 (x + c 3 * t) * (ψ t : ℂ)

/-- Measurability of the compact kernel used in `gowersDifferencing`. -/
lemma aux_gowersKernel_aestronglyMeasurable
    (c : Fin 4 → ℝ) (g : Fin 4 → ℝ → ℂ) (ψ : ℝ → ℝ)
    (hg : ∀ i : Fin 4, AEStronglyMeasurable (g i) volume)
    (hψ : Continuous ψ) :
    AEStronglyMeasurable (Function.uncurry (aux_gowersKernel c g ψ))
      (volume.prod volume) := by
  have h1 := aux_aestronglyMeasurable_comp_affine (g 1) (hg 1) (c 1)
  have h2 := aux_aestronglyMeasurable_comp_affine (g 2) (hg 2) (c 2)
  have h3 := aux_aestronglyMeasurable_comp_affine (g 3) (hg 3) (c 3)
  have hψ' : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ (ψ p.2 : ℂ))
      (volume.prod volume) :=
    (Complex.continuous_ofReal.comp (hψ.comp continuous_snd)).aestronglyMeasurable
  exact h1.mul h2 |>.mul h3 |>.mul hψ'

/-- The compact Gowers kernel remains almost-everywhere one-bounded under
the hypotheses of `gowersDifferencing`. -/
lemma aux_gowersKernel_ae_one_bounded
    (c : Fin 4 → ℝ) (g : Fin 4 → ℝ → ℂ) (ψ : ℝ → ℝ)
    (hg : ∀ i : Fin 4, ∀ᵐ x ∂volume, ‖g i x‖ ≤ 1)
    (hψnonneg : ∀ t : ℝ, 0 ≤ ψ t) (hψone : ∀ t : ℝ, ψ t ≤ 1) :
    ∀ᵐ p : ℝ × ℝ ∂volume.prod volume,
      ‖aux_gowersKernel c g ψ p.1 p.2‖ ≤ 1 := by
  have h1 := (aux_quasiMeasurePreserving_affine (c 1)).tendsto_ae (hg 1)
  have h2 := (aux_quasiMeasurePreserving_affine (c 2)).tendsto_ae (hg 2)
  have h3 := (aux_quasiMeasurePreserving_affine (c 3)).tendsto_ae (hg 3)
  filter_upwards [h1, h2, h3] with p hp1 hp2 hp3
  change ‖g 1 (p.1 + c 1 * p.2)‖ ≤ 1 at hp1
  change ‖g 2 (p.1 + c 2 * p.2)‖ ≤ 1 at hp2
  change ‖g 3 (p.1 + c 3 * p.2)‖ ≤ 1 at hp3
  rw [aux_gowersKernel, norm_mul, norm_mul, norm_mul]
  have hψnorm : ‖(ψ p.2 : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hψnonneg _)]
    exact hψone _
  calc
    ‖g 1 (p.1 + c 1 * p.2)‖ * ‖g 2 (p.1 + c 2 * p.2)‖ *
        ‖g 3 (p.1 + c 3 * p.2)‖ * ‖(ψ p.2 : ℂ)‖ ≤
        1 * 1 * 1 * 1 := by
      gcongr
    _ = 1 := by norm_num

/-- The compact kernel vanishes outside the spatial/time box forced by the
support of `g₁` and of the cutoff in `gowersDifferencing`. -/
lemma aux_gowersKernel_ae_zero_outside_spatial_time
    (c : Fin 4 → ℝ) (g : Fin 4 → ℝ → ℂ) (ψ : ℝ → ℝ) (J : Set ℝ)
    (hψ : tsupport ψ ⊆ J) :
    ∀ p : ℝ × ℝ,
      p ∉ aux_gowersSpatialRange (c 1) (g 1) J ×ˢ J →
        aux_gowersKernel c g ψ p.1 p.2 = 0 := by
  intro p hp
  by_cases ht : p.2 ∈ J
  · have hx : p.1 ∉ aux_gowersSpatialRange (c 1) (g 1) J := by
      intro hx
      exact hp ⟨hx, ht⟩
    have hgzero : g 1 (p.1 + c 1 * p.2) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      apply hx
      refine ⟨p.1 + c 1 * p.2, hmem, p.2, ht, ?_⟩
      ring
    simp [aux_gowersKernel, hgzero]
  · have hnot : p.2 ∉ tsupport ψ := fun hmem ↦ ht (hψ hmem)
    have hψzero : ψ p.2 = 0 := image_eq_zero_of_notMem_tsupport hnot
    simp [aux_gowersKernel, hψzero]

/-- A nonzero one-dimensional affine coordinate is quasi-measure-preserving.
This is used for the fibrewise integrability bookkeeping in
`gowersDifferencing`. -/
lemma aux_gowers_local_qmp_affine_t (x c : ℝ) (hc : c ≠ 0) :
    Measure.QuasiMeasurePreserving (fun t : ℝ ↦ x + c * t) volume volume := by
  have hscale : Measure.QuasiMeasurePreserving (fun t : ℝ ↦ c * t) volume volume := by
    refine ⟨by fun_prop, ?_⟩
    rw [Real.map_volume_mul_left hc]
    exact Measure.smul_absolutelyContinuous
  convert (measurePreserving_add_left volume x).quasiMeasurePreserving.comp hscale using 1
  rfl

/-- The nondegenerate affine coordinate on the product space is
quasi-measure-preserving.  This supports the original-integrand
integrability argument in `gowersDifferencing`. -/
lemma aux_gowers_local_qmp_affine_xt (c : ℝ) (hc : c ≠ 0) :
    Measure.QuasiMeasurePreserving (fun p : ℝ × ℝ ↦ p.1 + c * p.2)
      (volume.prod volume) volume := by
  apply QuasiMeasurePreserving.prod_of_right
  · fun_prop
  filter_upwards with x
  exact aux_gowers_local_qmp_affine_t x c hc

/-- The full four-factor integrand in `gowersDifferencing`, viewed as a
function on the product space. -/
def aux_gowersIntegrand (ψ : ℝ → ℝ) (c : Fin 4 → ℝ)
    (g : Fin 4 → ℝ → ℂ) : ℝ × ℝ → ℂ := fun p ↦
  g 0 p.1 * g 1 (p.1 + c 1 * p.2) * g 2 (p.1 + c 2 * p.2) *
    g 3 (p.1 + c 3 * p.2) * (ψ p.2 : ℂ)

/-- Strong measurability of the full Gowers integrand. -/
lemma aux_gowers_integrand_aestronglyMeasurable
    (ψ : ℝ → ℝ) (c : Fin 4 → ℝ) (g : Fin 4 → ℝ → ℂ)
    (hgmeas : ∀ i : Fin 4, AEStronglyMeasurable (g i) volume)
    (hc1 : c 1 ≠ 0) (hc2 : c 2 ≠ 0) (hc3 : c 3 ≠ 0)
    (hψcont : Continuous ψ) :
    AEStronglyMeasurable (aux_gowersIntegrand ψ c g) (volume.prod volume) := by
  have h0 : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ g 0 p.1) (volume.prod volume) := by
    simpa only [Function.comp_def] using
      (hgmeas 0).comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume))
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ g 1 (p.1 + c 1 * p.2))
      (volume.prod volume) := by
    simpa only [Function.comp_def] using
      (hgmeas 1).comp_quasiMeasurePreserving (aux_gowers_local_qmp_affine_xt (c 1) hc1)
  have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ g 2 (p.1 + c 2 * p.2))
      (volume.prod volume) := by
    simpa only [Function.comp_def] using
      (hgmeas 2).comp_quasiMeasurePreserving (aux_gowers_local_qmp_affine_xt (c 2) hc2)
  have h3 : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ g 3 (p.1 + c 3 * p.2))
      (volume.prod volume) := by
    simpa only [Function.comp_def] using
      (hgmeas 3).comp_quasiMeasurePreserving (aux_gowers_local_qmp_affine_xt (c 3) hc3)
  have hψ : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ (ψ p.2 : ℂ))
      (volume.prod volume) := by
    exact (Complex.continuous_ofReal.comp (hψcont.comp continuous_snd)).aestronglyMeasurable
  exact h0.mul h1 |>.mul h2 |>.mul h3 |>.mul hψ

/-- The full Gowers integrand is integrable from compact outer and cutoff
support.  This lets `gowersDifferencing` pass the pre-localization through
the iterated integral. -/
lemma aux_gowers_integrand_integrable
    (A J : Set ℝ) (ψ : ℝ → ℝ) (c : Fin 4 → ℝ) (g : Fin 4 → ℝ → ℂ)
    (hA : IsCompact A) (hJ : IsCompact J)
    (hgmeas : ∀ i : Fin 4, AEStronglyMeasurable (g i) volume)
    (hgbdd : ∀ i : Fin 4, ∀ᵐ x ∂volume, ‖g i x‖ ≤ 1)
    (hg0support : ∀ᵐ x ∂volume, x ∉ A → g 0 x = 0)
    (hc1 : c 1 ≠ 0) (hc2 : c 2 ≠ 0) (hc3 : c 3 ≠ 0)
    (hψcont : Continuous ψ) (hψnonneg : ∀ t : ℝ, 0 ≤ ψ t)
    (hψle : ∀ t : ℝ, ψ t ≤ 1) (hψsupport : tsupport ψ ⊆ J) :
    Integrable (aux_gowersIntegrand ψ c g) (volume.prod volume) := by
  have hmeas := aux_gowers_integrand_aestronglyMeasurable ψ c g hgmeas hc1 hc2 hc3 hψcont
  have hb0 : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), ‖g 0 p.1‖ ≤ 1 := by
    exact (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).tendsto_ae.eventually
      (hgbdd 0)
  have hb1 : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), ‖g 1 (p.1 + c 1 * p.2)‖ ≤ 1 := by
    exact (aux_gowers_local_qmp_affine_xt (c 1) hc1).tendsto_ae.eventually (hgbdd 1)
  have hb2 : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), ‖g 2 (p.1 + c 2 * p.2)‖ ≤ 1 := by
    exact (aux_gowers_local_qmp_affine_xt (c 2) hc2).tendsto_ae.eventually (hgbdd 2)
  have hb3 : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), ‖g 3 (p.1 + c 3 * p.2)‖ ≤ 1 := by
    exact (aux_gowers_local_qmp_affine_xt (c 3) hc3).tendsto_ae.eventually (hgbdd 3)
  have h0prod : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
      p.1 ∉ A → g 0 p.1 = 0 := by
    exact (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).tendsto_ae.eventually
      hg0support
  have hind : Integrable ((A ×ˢ J).indicator (fun _ : ℝ × ℝ ↦ (1 : ℝ)))
      (volume.prod volume) := by
    rw [integrable_indicator_iff (hA.prod hJ).measurableSet]
    exact integrableOn_const (hA.prod hJ).measure_lt_top.ne
  apply Integrable.mono' hind hmeas
  filter_upwards [hb0, hb1, hb2, hb3, h0prod] with p hp0 hp1 hp2 hp3 hpsupp
  by_cases hpA : p.1 ∈ A
  · by_cases hpJ : p.2 ∈ J
    · have hpAJ : p ∈ A ×ˢ J := ⟨hpA, hpJ⟩
      rw [Set.indicator_of_mem hpAJ]
      have hψ : ‖(ψ p.2 : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hψnonneg _)]
        exact hψle _
      rw [aux_gowersIntegrand, norm_mul, norm_mul, norm_mul, norm_mul]
      have h01 : ‖g 0 p.1‖ * ‖g 1 (p.1 + c 1 * p.2)‖ ≤ 1 :=
        (mul_le_of_le_one_left (norm_nonneg _) hp0).trans hp1
      have h012 : (‖g 0 p.1‖ * ‖g 1 (p.1 + c 1 * p.2)‖) *
          ‖g 2 (p.1 + c 2 * p.2)‖ ≤ 1 :=
        (mul_le_of_le_one_left (norm_nonneg _) h01).trans hp2
      have h0123 : ((‖g 0 p.1‖ * ‖g 1 (p.1 + c 1 * p.2)‖) *
          ‖g 2 (p.1 + c 2 * p.2)‖) * ‖g 3 (p.1 + c 3 * p.2)‖ ≤ 1 :=
        (mul_le_of_le_one_left (norm_nonneg _) h012).trans hp3
      exact (mul_le_of_le_one_left (norm_nonneg _) h0123).trans hψ
    · rw [Set.indicator_of_notMem (by simp [hpJ])]
      have hts : p.2 ∉ tsupport ψ := fun ht ↦ hpJ (hψsupport ht)
      have hψzero : ψ p.2 = 0 := image_eq_zero_of_notMem_tsupport hts
      simp [aux_gowersIntegrand, hψzero]
  · rw [Set.indicator_of_notMem (by simp [hpA])]
    simp [aux_gowersIntegrand, hpsupp hpA]

/-- The almost-everywhere pre-localization of the two rough factors passes
through the original nested integral in `gowersDifferencing`. -/
lemma aux_gowers_double_integral_restrict_g2g3
    (A J : Set ℝ) (ψ : ℝ → ℝ) (c : Fin 4 → ℝ) (g : Fin 4 → ℝ → ℂ)
    (hg0support : ∀ᵐ x ∂volume, x ∉ A → g 0 x = 0)
    (hψsupport : tsupport ψ ⊆ J)
    (hInt : Integrable (aux_gowersIntegrand ψ c g) (volume.prod volume)) :
    (∫ x : ℝ, ∫ t : ℝ,
      g 0 x * g 1 (x + c 1 * t) * g 2 (x + c 2 * t) *
        g 3 (x + c 3 * t) * (ψ t : ℂ)) =
      ∫ x : ℝ, ∫ t : ℝ,
        g 0 x * g 1 (x + c 1 * t) *
          aux_gowersRestrict (aux_gowersInteractionRange A J (c 2)) (g 2) (x + c 2 * t) *
          aux_gowersRestrict (aux_gowersInteractionRange A J (c 3)) (g 3) (x + c 3 * t) *
          (ψ t : ℂ) := by
  let F : ℝ × ℝ → ℂ := aux_gowersIntegrand ψ c g
  let R : ℝ × ℝ → ℂ := fun p ↦
    g 0 p.1 * g 1 (p.1 + c 1 * p.2) *
      aux_gowersRestrict (aux_gowersInteractionRange A J (c 2)) (g 2) (p.1 + c 2 * p.2) *
      aux_gowersRestrict (aux_gowersInteractionRange A J (c 3)) (g 3) (p.1 + c 3 * p.2) *
      (ψ p.2 : ℂ)
  have hEq' : aux_gowersIntegrand ψ c g =ᵐ[volume.prod volume] R := by
    change (fun p : ℝ × ℝ ↦
      g 0 p.1 * g 1 (p.1 + c 1 * p.2) * g 2 (p.1 + c 2 * p.2) *
        g 3 (p.1 + c 3 * p.2) * (ψ p.2 : ℂ)) =ᵐ[volume.prod volume] R
    simpa only [R] using
      aux_gowers_integrand_restrict_g2g3_eq_ae A J ψ c g hg0support hψsupport
  have hEq : F =ᵐ[volume.prod volume] R := by
    simpa only [F] using hEq'
  have hR : Integrable R (volume.prod volume) := hInt.congr hEq
  change (∫ x : ℝ, ∫ t : ℝ, F (x, t)) = ∫ x : ℝ, ∫ t : ℝ, R (x, t)
  calc
    (∫ x : ℝ, ∫ t : ℝ, F (x, t)) = ∫ p : ℝ × ℝ, F p :=
      (integral_prod F hInt).symm
    _ = ∫ p : ℝ × ℝ, R p := integral_congr_ae hEq
    _ = ∫ x : ℝ, ∫ t : ℝ, R (x, t) := integral_prod R hR

/-- Separation from the zero coefficient forces each nonzero-index
coefficient to be nonzero in `gowersDifferencing`. -/
lemma aux_gowers_coeff_ne_zero_of_separated
    (δ : ℝ) (hδ_pos : 0 < δ) (c : Fin 4 → ℝ) (hc_zero : c 0 = 0)
    (hc_separated : ∀ i j : Fin 4, i < j → δ ≤ |c i - c j|)
    (i : Fin 4) (hi : 0 < i) : c i ≠ 0 := by
  intro hci
  have hsep := hc_separated 0 i hi
  have : δ ≤ 0 := by simpa [hc_zero, hci] using hsep
  exact (not_le_of_gt hδ_pos) this

/-- Main-data wrapper for the integrability prerequisite of the localization
step in `gowersDifferencing`. -/
lemma aux_gowers_integrand_integrable_of_main_data
    (A J : Set ℝ) (ψ : ℝ → ℝ)
    (hA : ∃ a b : ℝ, a < b ∧ A = Set.Icc a b)
    (hJ : ∃ a b : ℝ, a < b ∧ J = Set.Icc a b)
    (hψ_smooth : ContDiff ℝ 1 ψ)
    (hψ_nonneg : ∀ t : ℝ, 0 ≤ ψ t) (hψ_le_one : ∀ t : ℝ, ψ t ≤ 1)
    (hψ_support : tsupport ψ ⊆ J)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (c : Fin 4 → ℝ) (hc_zero : c 0 = 0)
    (hc_separated : ∀ i j : Fin 4, i < j → δ ≤ |c i - c j|)
    (g : Fin 4 → ℝ → ℂ)
    (hg_measurable : ∀ i : Fin 4, AEStronglyMeasurable (g i) volume)
    (hg_one_bounded : ∀ i : Fin 4, ∀ᵐ x ∂volume, ‖g i x‖ ≤ 1)
    (hg_zero_support : ∀ᵐ x ∂volume, x ∉ A → g 0 x = 0) :
    Integrable (aux_gowersIntegrand ψ c g) (volume.prod volume) := by
  rcases hA with ⟨a, b, hab, rfl⟩
  rcases hJ with ⟨p, q, hpq, rfl⟩
  apply aux_gowers_integrand_integrable (Set.Icc a b) (Set.Icc p q) ψ c g
    isCompact_Icc isCompact_Icc hg_measurable hg_one_bounded hg_zero_support
  · exact aux_gowers_coeff_ne_zero_of_separated δ hδ_pos c hc_zero hc_separated 1 (by decide)
  · exact aux_gowers_coeff_ne_zero_of_separated δ hδ_pos c hc_zero hc_separated 2 (by decide)
  · exact aux_gowers_coeff_ne_zero_of_separated δ hδ_pos c hc_zero hc_separated 3 (by decide)
  · exact hψ_smooth.continuous
  · exact hψ_nonneg
  · exact hψ_le_one
  · exact hψ_support

/-- The difference set of a compact subset of `ℝ` is compact.  This gives
the compact range of the time-shift parameter in the autocorrelation step of
`gowersDifferencing`. -/
lemma aux_isCompact_image2_sub (J : Set ℝ) (hJ : IsCompact J) :
    IsCompact (Set.image2 (fun s t : ℝ ↦ s - t) J J) := by
  rw [← Set.image_prod]
  exact (hJ.prod hJ).image (continuous_fst.sub continuous_snd)

/-- The first projection used to pull a two-variable function to the
autocorrelation variables `(x,h,t)`. -/
lemma aux_autocorrelation_qmp_unshifted :
    Measure.QuasiMeasurePreserving
      (fun z : (ℝ × ℝ) × ℝ ↦ (z.1.1, z.2))
      ((volume.prod volume).prod volume) (volume.prod volume) := by
  have hproj : Measure.QuasiMeasurePreserving
      (fun z : ℝ × (ℝ × ℝ) ↦ (z.1, z.2.2))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    exact MeasureTheory.QuasiMeasurePreserving.prodMap
      (Measure.QuasiMeasurePreserving.id (α := ℝ) volume)
      (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume))
  convert hproj.comp
    (measurePreserving_prodAssoc volume volume volume).quasiMeasurePreserving using 1
  rfl

/-- The shifted projection used to pull a two-variable function to the
autocorrelation variables `(x,h,t)`. -/
lemma aux_autocorrelation_qmp_shifted :
    Measure.QuasiMeasurePreserving
      (fun z : (ℝ × ℝ) × ℝ ↦ (z.1.1, z.2 + z.1.2))
      ((volume.prod volume).prod volume) (volume.prod volume) := by
  have hadd : Measure.QuasiMeasurePreserving (fun p : ℝ × ℝ ↦ p.2 + p.1)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) (volume : Measure ℝ) := by
    refine MeasureTheory.QuasiMeasurePreserving.prod_of_left (by fun_prop) ?_
    filter_upwards with t
    exact (measurePreserving_add_left volume t).quasiMeasurePreserving
  have hpair : Measure.QuasiMeasurePreserving
      (fun z : ℝ × (ℝ × ℝ) ↦ (z.1, z.2.2 + z.2.1))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    exact MeasureTheory.QuasiMeasurePreserving.prodMap
      (Measure.QuasiMeasurePreserving.id (α := ℝ) volume) hadd
  convert hpair.comp
    (measurePreserving_prodAssoc volume volume volume).quasiMeasurePreserving using 1
  rfl

/-- Measurability of the three-variable autocorrelation integrand. -/
lemma aux_autocorrelation_aestronglyMeasurable
    (Q : ℝ → ℝ → ℂ)
    (hQ : AEStronglyMeasurable (Function.uncurry Q) (volume.prod volume)) :
    AEStronglyMeasurable
      (fun z : (ℝ × ℝ) × ℝ ↦
        Q z.1.1 z.2 * starRingEnd ℂ (Q z.1.1 (z.2 + z.1.2)))
      ((volume.prod volume).prod volume) := by
  have hleft : AEStronglyMeasurable (fun z : (ℝ × ℝ) × ℝ ↦ Q z.1.1 z.2)
      ((volume.prod volume).prod volume) := by
    change AEStronglyMeasurable
      ((Function.uncurry Q) ∘ fun z : (ℝ × ℝ) × ℝ ↦ (z.1.1, z.2))
      ((volume.prod volume).prod volume)
    exact hQ.comp_quasiMeasurePreserving aux_autocorrelation_qmp_unshifted
  have hright : AEStronglyMeasurable (fun z : (ℝ × ℝ) × ℝ ↦ Q z.1.1 (z.2 + z.1.2))
      ((volume.prod volume).prod volume) := by
    change AEStronglyMeasurable
      ((Function.uncurry Q) ∘ fun z : (ℝ × ℝ) × ℝ ↦ (z.1.1, z.2 + z.1.2))
      ((volume.prod volume).prod volume)
    exact hQ.comp_quasiMeasurePreserving aux_autocorrelation_qmp_shifted
  exact hleft.mul hright.star

/-- The autocorrelation of a bounded function supported on `X ×ˢ J` is
integrable.  Its support is contained in
`(X ×ˢ image2 (· - ·) J J) ×ˢ J`. -/
lemma aux_autocorrelation_integrable_compactSupport
    (X J : Set ℝ) (hX : IsCompact X) (hJ : IsCompact J) (Q : ℝ → ℝ → ℂ)
    (hQmeas : AEStronglyMeasurable (Function.uncurry Q) (volume.prod volume))
    (hQbound : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖Q z.1 z.2‖ ≤ 1)
    (hQsupport : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∉ X ×ˢ J → Q z.1 z.2 = 0) :
    Integrable
      (Function.uncurry fun p : ℝ × ℝ ↦ fun t : ℝ ↦
        Q p.1 t * starRingEnd ℂ (Q p.1 (t + p.2)))
      ((volume.prod volume).prod volume) := by
  let T : Set (ℝ × ℝ) := X ×ˢ J
  let D : Set ℝ := Set.image2 (fun s t : ℝ ↦ s - t) J J
  let S : Set ((ℝ × ℝ) × ℝ) := (X ×ˢ D) ×ˢ J
  have hDcompact : IsCompact D := by
    dsimp only [D]
    exact aux_isCompact_image2_sub J hJ
  have hRmeas := aux_autocorrelation_aestronglyMeasurable Q hQmeas
  have hleftbound : ∀ᵐ z : (ℝ × ℝ) × ℝ ∂(volume.prod volume).prod volume,
      ‖Q z.1.1 z.2‖ ≤ 1 := by
    exact aux_autocorrelation_qmp_unshifted.ae hQbound
  have hrightbound : ∀ᵐ z : (ℝ × ℝ) × ℝ ∂(volume.prod volume).prod volume,
      ‖Q z.1.1 (z.2 + z.1.2)‖ ≤ 1 := by
    exact aux_autocorrelation_qmp_shifted.ae hQbound
  have hRbound : ∀ᵐ z : (ℝ × ℝ) × ℝ ∂(volume.prod volume).prod volume,
      ‖Q z.1.1 z.2 * starRingEnd ℂ (Q z.1.1 (z.2 + z.1.2))‖ ≤ 1 := by
    filter_upwards [hleftbound, hrightbound] with z hz₁ hz₂
    rw [norm_mul]
    change ‖Q z.1.1 z.2‖ * ‖star (Q z.1.1 (z.2 + z.1.2))‖ ≤ 1
    rw [norm_star]
    nlinarith [norm_nonneg (Q z.1.1 z.2), norm_nonneg (Q z.1.1 (z.2 + z.1.2))]
  have hleftzero : ∀ᵐ z : (ℝ × ℝ) × ℝ ∂(volume.prod volume).prod volume,
      (z.1.1, z.2) ∉ T → Q z.1.1 z.2 = 0 := by
    exact aux_autocorrelation_qmp_unshifted.ae hQsupport
  have hrightzero : ∀ᵐ z : (ℝ × ℝ) × ℝ ∂(volume.prod volume).prod volume,
      (z.1.1, z.2 + z.1.2) ∉ T → Q z.1.1 (z.2 + z.1.2) = 0 := by
    exact aux_autocorrelation_qmp_shifted.ae hQsupport
  have hScompact : IsCompact S := by
    dsimp only [S]
    exact (hX.prod hDcompact).prod hJ
  have hSmeas : MeasurableSet S := hScompact.isClosed.measurableSet
  have hSfinite : ((volume.prod volume).prod volume) S < ∞ := hScompact.measure_lt_top
  have hRsupp : ∀ᵐ z : (ℝ × ℝ) × ℝ ∂(volume.prod volume).prod volume,
      z ∉ S → Q z.1.1 z.2 * starRingEnd ℂ (Q z.1.1 (z.2 + z.1.2)) = 0 := by
    filter_upwards [hleftzero, hrightzero] with z hzleft hzright
    intro hzS
    by_cases hleft : (z.1.1, z.2) ∈ T
    · have hx : z.1.1 ∈ X := by
        change z.1.1 ∈ X ∧ z.2 ∈ J at hleft
        exact hleft.1
      have ht : z.2 ∈ J := by
        change z.1.1 ∈ X ∧ z.2 ∈ J at hleft
        exact hleft.2
      have hh : z.1.2 ∉ D := by
        intro hhd
        apply hzS
        change z.1 ∈ X ×ˢ D ∧ z.2 ∈ J
        exact ⟨⟨hx, hhd⟩, ht⟩
      have hnotT : (z.1.1, z.2 + z.1.2) ∉ T := by
        intro hmem
        have hshift : z.2 + z.1.2 ∈ J := by
          change z.1.1 ∈ X ∧ z.2 + z.1.2 ∈ J at hmem
          exact hmem.2
        apply hh
        change z.1.2 ∈ Set.image2 (fun s t : ℝ ↦ s - t) J J
        exact ⟨z.2 + z.1.2, hshift, z.2, ht, by ring⟩
      simp [hzright hnotT]
    · simp [hzleft hleft]
  have hmem : MemLp
      (fun z : (ℝ × ℝ) × ℝ ↦
        Q z.1.1 z.2 * starRingEnd ℂ (Q z.1.1 (z.2 + z.1.2)))
      1 ((volume.prod volume).prod volume) :=
    aux_memLp_of_ae_bound_of_ae_support _ hRmeas 1 hRbound S hSmeas hSfinite hRsupp 1
  exact memLp_one_iff_integrable.mp hmem

/-- A bounded integrand supported on `X ×ˢ J`, for compact `X,J`, has
integrable time sections and an `L²` time integral supported on `X`. -/
lemma aux_timeIntegral_memLp_compactSupport
    (X J : Set ℝ) (hX : IsCompact X) (hJ : IsCompact J) (Q : ℝ → ℝ → ℂ)
    (hQmeas : AEStronglyMeasurable (Function.uncurry Q) (volume.prod volume))
    (hQbound : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖Q z.1 z.2‖ ≤ 1)
    (hQsupport : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∉ X ×ˢ J → Q z.1 z.2 = 0) :
    (∀ᵐ x : ℝ ∂volume, Integrable (Q x) volume) ∧
      MemLp (fun x : ℝ ↦ ∫ t : ℝ, Q x t) 2 volume := by
  let T : Set (ℝ × ℝ) := X ×ˢ J
  have hTmeas : MeasurableSet T := hX.isClosed.measurableSet.prod hJ.isClosed.measurableSet
  have hTfinite : (volume.prod volume) T < ∞ := (hX.prod hJ).measure_lt_top
  have hQmem : MemLp (Function.uncurry Q) 1 (volume.prod volume) :=
    aux_memLp_of_ae_bound_of_ae_support _ hQmeas 1 hQbound T hTmeas hTfinite hQsupport 1
  have hQint : Integrable (Function.uncurry Q) (volume.prod volume) :=
    memLp_one_iff_integrable.mp hQmem
  have hsections : ∀ᵐ x : ℝ ∂volume, Integrable (Q x) volume :=
    hQint.prod_right_ae
  have hboundsections : ∀ᵐ x : ℝ ∂volume, ∀ᵐ t : ℝ ∂volume, ‖Q x t‖ ≤ 1 :=
    Measure.ae_ae_of_ae_prod hQbound
  have hsupportsections : ∀ᵐ x : ℝ ∂volume, ∀ᵐ t : ℝ ∂volume,
      (x, t) ∉ T → Q x t = 0 :=
    Measure.ae_ae_of_ae_prod hQsupport
  have hJmeas : MeasurableSet J := hJ.isClosed.measurableSet
  have hJfinite : volume J < ∞ := hJ.measure_lt_top
  have hJint : Integrable (J.indicator (1 : ℝ → ℝ)) volume := by
    rw [← memLp_one_iff_integrable]
    exact memLp_indicator_const 1 hJmeas 1 (Or.inr hJfinite.ne)
  have hHmeas : AEStronglyMeasurable (fun x : ℝ ↦ ∫ t : ℝ, Q x t) volume := by
    change AEStronglyMeasurable
      (fun x : ℝ ↦ ∫ t : ℝ, (Function.uncurry Q) (x, t)) volume
    exact hQmeas.integral_prod_right'
  have hHbound : ∀ᵐ x : ℝ ∂volume,
      ‖∫ t : ℝ, Q x t‖ ≤ (volume J).toReal := by
    filter_upwards [hsections, hboundsections, hsupportsections] with x hxint hxbound hxsupport
    calc
      ‖∫ t : ℝ, Q x t‖ ≤ ∫ t : ℝ, ‖Q x t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, J.indicator (1 : ℝ → ℝ) t := by
        apply integral_mono_ae hxint.norm hJint
        filter_upwards [hxbound, hxsupport] with t htbound htsupport
        by_cases ht : t ∈ J
        · simp [ht, htbound]
        · have hnotT : (x, t) ∉ T := by
            intro hmem
            change x ∈ X ∧ t ∈ J at hmem
            exact ht hmem.2
          simp [ht, htsupport hnotT]
      _ = (volume J).toReal := by
        simpa only [Measure.real] using (integral_indicator_one (μ := volume) hJmeas)
  have hHsupport : ∀ᵐ x : ℝ ∂volume, x ∉ X → (∫ t : ℝ, Q x t) = 0 := by
    filter_upwards [hsupportsections] with x hxsupport
    intro hx
    rw [← integral_zero]
    apply integral_congr_ae
    filter_upwards [hxsupport] with t htsupport
    have hnotT : (x, t) ∉ T := by
      intro hmem
      change x ∈ X ∧ t ∈ J at hmem
      exact hx hmem.1
    exact htsupport hnotT
  have hXmeas : MeasurableSet X := hX.isClosed.measurableSet
  have hXfinite : volume X < ∞ := hX.measure_lt_top
  refine ⟨hsections, ?_⟩
  exact aux_memLp_of_ae_bound_of_ae_support _ hHmeas (volume J).toReal hHbound
    X hXmeas hXfinite hHsupport 2

/-- The exact autocorrelation identity for one integrable time section. -/
lemma aux_single_autocorrelation_integral (f : ℝ → ℂ) (hf : Integrable f volume) :
    (↑(‖∫ t : ℝ, f t‖ ^ (2 : ℕ)) : ℂ) =
      ∫ h : ℝ, ∫ t : ℝ, f t * starRingEnd ℂ (f (t + h)) := by
  let K : ℝ × ℝ → ℂ := fun z ↦ f z.1 * starRingEnd ℂ (f z.2)
  have hfstar : Integrable (fun t : ℝ ↦ starRingEnd ℂ (f t)) volume := by
    change Integrable (star f) volume
    rw [← memLp_one_iff_integrable] at hf ⊢
    exact hf.star
  have hK : Integrable K (volume.prod volume) := by
    exact hf.mul_prod hfstar
  have hKshear : Integrable (fun z : ℝ × ℝ ↦
      f z.1 * starRingEnd ℂ (f (z.1 + z.2))) (volume.prod volume) := by
    change Integrable (K ∘ fun z : ℝ × ℝ ↦ (z.1, z.1 + z.2)) (volume.prod volume)
    rw [← memLp_one_iff_integrable] at hK ⊢
    exact hK.comp_measurePreserving (measurePreserving_prod_add volume volume)
  calc
    (↑(‖∫ t : ℝ, f t‖ ^ (2 : ℕ)) : ℂ) =
        (∫ t : ℝ, f t) * ∫ s : ℝ, starRingEnd ℂ (f s) := by
      rw [integral_conj]
      convert (RCLike.mul_conj (∫ t : ℝ, f t)).symm using 1 ; simp
    _ = ∫ z : ℝ × ℝ, K z ∂volume.prod volume := by
      exact (integral_prod_mul f (fun s : ℝ ↦ starRingEnd ℂ (f s))).symm
    _ = ∫ z : ℝ × ℝ, f z.1 * starRingEnd ℂ (f (z.1 + z.2)) ∂volume.prod volume := by
      exact ((measurePreserving_prod_add volume volume).integral_comp
        (MeasurableEquiv.shearAddRight ℝ).measurableEmbedding K).symm
    _ = ∫ h : ℝ, ∫ t : ℝ, f t * starRingEnd ℂ (f (t + h)) := by
      simpa using (integral_prod_symm _ hKshear)

/-- Autocorrelation identity with only almost-everywhere integrable time
sections; the three-variable integrability hypothesis justifies Fubini. -/
lemma aux_autocorrelation_integral_ae
    (F : ℝ → ℝ → ℂ) (hF : ∀ᵐ x : ℝ ∂volume, Integrable (F x) volume)
    (hR : Integrable
      (Function.uncurry fun p : ℝ × ℝ ↦ fun t : ℝ ↦
        F p.1 t * starRingEnd ℂ (F p.1 (t + p.2)))
      ((volume.prod volume).prod volume)) :
    ∫ x : ℝ, (↑(‖∫ t : ℝ, F x t‖ ^ (2 : ℕ)) : ℂ) =
      ∫ h : ℝ, ∫ x : ℝ, ∫ t : ℝ,
        F x t * starRingEnd ℂ (F x (t + h)) := by
  let R : (ℝ × ℝ) → ℝ → ℂ := fun p t ↦
    F p.1 t * starRingEnd ℂ (F p.1 (t + p.2))
  have hD : Integrable (fun p : ℝ × ℝ ↦ ∫ t : ℝ, R p t) (volume.prod volume) := by
    exact hR.integral_prod_left
  calc
    ∫ x : ℝ, (↑(‖∫ t : ℝ, F x t‖ ^ (2 : ℕ)) : ℂ) =
        ∫ x : ℝ, ∫ h : ℝ, ∫ t : ℝ,
          F x t * starRingEnd ℂ (F x (t + h)) := by
      apply integral_congr_ae
      filter_upwards [hF] with x hx
      exact aux_single_autocorrelation_integral (F x) hx
    _ = ∫ h : ℝ, ∫ x : ℝ, ∫ t : ℝ,
        F x t * starRingEnd ℂ (F x (t + h)) := by
      simpa only [R] using (integral_integral_swap hD)

/-- Taking norms in the autocorrelation identity bounds the squared `L²`
mass of a time integral by the integral of the absolute autocorrelation. -/
lemma aux_integral_norm_sq_le_autocorrelation
    (H D : ℝ → ℂ) (hH : MemLp H 2 volume)
    (hEq : ∫ x : ℝ, (↑(‖H x‖ ^ (2 : ℕ)) : ℂ) = ∫ h : ℝ, D h) :
    ∫ x : ℝ, ‖H x‖ ^ (2 : ℕ) ≤ ∫ h : ℝ, ‖D h‖ := by
  have hHsq : Integrable (fun x : ℝ ↦ ‖H x‖ ^ (2 : ℕ)) volume :=
    hH.integrable_norm_pow (by norm_num)
  have hnonneg : 0 ≤ ∫ x : ℝ, ‖H x‖ ^ (2 : ℕ) :=
    integral_nonneg fun x ↦ sq_nonneg ‖H x‖
  calc
    ∫ x : ℝ, ‖H x‖ ^ (2 : ℕ) =
        ‖(↑(∫ x : ℝ, ‖H x‖ ^ (2 : ℕ)) : ℂ)‖ := by
      exact ((RCLike.norm_ofReal (∫ x : ℝ, ‖H x‖ ^ (2 : ℕ))).trans
        (abs_of_nonneg hnonneg)).symm
    _ = ‖∫ x : ℝ, (↑(‖H x‖ ^ (2 : ℕ)) : ℂ)‖ := by
      congr 1
      exact (integral_ofReal (f := fun x : ℝ ↦ ‖H x‖ ^ (2 : ℕ))).symm
    _ = ‖∫ h : ℝ, D h‖ := congrArg norm hEq
    _ ≤ ∫ h : ℝ, ‖D h‖ := norm_integral_le_integral_norm _

/-- The compact-support physical Cauchy--Schwarz/Fubini reduction used in
the Gowers differencing argument. -/
lemma aux_square_timeIntegral_le_autocorrelation_compactSupport
    (X J : Set ℝ) (hX : IsCompact X) (hJ : IsCompact J) (Q : ℝ → ℝ → ℂ)
    (hQmeas : AEStronglyMeasurable (Function.uncurry Q) (volume.prod volume))
    (hQbound : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖Q z.1 z.2‖ ≤ 1)
    (hQsupport : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∉ X ×ˢ J → Q z.1 z.2 = 0) :
    ∫ x : ℝ, ‖∫ t : ℝ, Q x t‖ ^ (2 : ℕ) ≤
      ∫ h : ℝ, ‖∫ x : ℝ, ∫ t : ℝ,
        Q x t * starRingEnd ℂ (Q x (t + h))‖ := by
  rcases aux_timeIntegral_memLp_compactSupport X J hX hJ Q
    hQmeas hQbound hQsupport with ⟨hsections, hH⟩
  exact aux_integral_norm_sq_le_autocorrelation _ _ hH
    (aux_autocorrelation_integral_ae Q hsections
      (aux_autocorrelation_integrable_compactSupport X J hX hJ Q
        hQmeas hQbound hQsupport))

/-- Squared outer Cauchy--Schwarz with a supplied bound on the first factor's
energy.  This is used by the compact physical reduction in
`gowersDifferencing`. -/
lemma aux_outer_cauchy_sq_of_energy_bound
    (f u : ℝ → ℂ) (hf : MemLp f (2 : ℝ≥0∞) volume)
    (hu : MemLp u (2 : ℝ≥0∞) volume) (B : ℝ)
    (hB : (∫ x : ℝ, ‖f x‖ ^ (2 : ℝ)) ≤ B) :
    ‖∫ x : ℝ, f x * u x‖ ^ (2 : ℕ) ≤
      B * (∫ x : ℝ, ‖u x‖ ^ (2 : ℝ)) := by
  let F : ℝ := ∫ x : ℝ, ‖f x‖ ^ (2 : ℝ)
  let U : ℝ := ∫ x : ℝ, ‖u x‖ ^ (2 : ℝ)
  have hF0 : 0 ≤ F := by
    exact integral_nonneg (fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)
  have hU0 : 0 ≤ U := by
    exact integral_nonneg (fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)
  have hB0 : 0 ≤ B := hF0.trans hB
  have hFroot : F ^ (1 / (2 : ℝ)) ≤ B ^ (1 / (2 : ℝ)) := by
    exact Real.rpow_le_rpow hF0 hB (by norm_num)
  have hroot0 : 0 ≤ B ^ (1 / (2 : ℝ)) * U ^ (1 / (2 : ℝ)) := by
    exact mul_nonneg (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hU0 _)
  have hTbound : ‖∫ x : ℝ, f x * u x‖ ≤
      B ^ (1 / (2 : ℝ)) * U ^ (1 / (2 : ℝ)) := by
    calc
      ‖∫ x : ℝ, f x * u x‖ ≤ F ^ (1 / (2 : ℝ)) * U ^ (1 / (2 : ℝ)) := by
        simpa only [F, U] using aux_outer_cauchy f u hf hu
      _ ≤ B ^ (1 / (2 : ℝ)) * U ^ (1 / (2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hFroot (Real.rpow_nonneg hU0 _)
  calc
    ‖∫ x : ℝ, f x * u x‖ ^ (2 : ℕ) ≤
        (B ^ (1 / (2 : ℝ)) * U ^ (1 / (2 : ℝ))) ^ (2 : ℕ) :=
      (sq_le_sq₀ (norm_nonneg _) hroot0).mpr hTbound
    _ = B * U := by
      rw [mul_pow]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hB0]
      norm_num
      rw [← Real.rpow_natCast, ← Real.rpow_mul hU0]
      norm_num
    _ = B * (∫ x : ℝ, ‖u x‖ ^ (2 : ℝ)) := by rfl

/-- The outer Cauchy--Schwarz and compact-support autocorrelation reduction.
This bounds a localized Gowers-type bilinear pairing by the physical
autocorrelation of its compact time kernel. -/
lemma aux_outer_cauchy_sq_le_autocorrelation_compactSupport
    (A X J : Set ℝ) (hA : IsCompact A) (hX : IsCompact X) (hJ : IsCompact J)
    (g₀ : ℝ → ℂ) (hg₀ : MemLp g₀ (2 : ℝ≥0∞) volume)
    (hg₀bound : ∀ᵐ x : ℝ ∂volume, ‖g₀ x‖ ≤ 1)
    (hg₀support : ∀ᵐ x : ℝ ∂volume, x ∉ A → g₀ x = 0)
    (Q : ℝ → ℝ → ℂ)
    (hQmeas : AEStronglyMeasurable (Function.uncurry Q) (volume.prod volume))
    (hQbound : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖Q z.1 z.2‖ ≤ 1)
    (hQsupport : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∉ X ×ˢ J → Q z.1 z.2 = 0) :
    ‖∫ x : ℝ, g₀ x * ∫ t : ℝ, Q x t‖ ^ (2 : ℕ) ≤
      volume.real A * ∫ h : ℝ, ‖∫ x : ℝ, ∫ t : ℝ,
        Q x t * starRingEnd ℂ (Q x (t + h))‖ := by
  let H : ℝ → ℂ := fun x ↦ ∫ t : ℝ, Q x t
  have henergy : (∫ x : ℝ, ‖g₀ x‖ ^ (2 : ℝ)) ≤ volume.real A := by
    exact aux_energy_le_measure A hA.isClosed.measurableSet hA.measure_lt_top.ne
      g₀ hg₀ hg₀bound hg₀support
  have hH : MemLp H 2 volume := by
    simpa only [H] using
      (aux_timeIntegral_memLp_compactSupport X J hX hJ Q hQmeas hQbound hQsupport).2
  have houter : ‖∫ x : ℝ, g₀ x * H x‖ ^ (2 : ℕ) ≤
      volume.real A * (∫ x : ℝ, ‖H x‖ ^ (2 : ℝ)) := by
    exact aux_outer_cauchy_sq_of_energy_bound g₀ H hg₀ hH _ henergy
  have hauto : (∫ x : ℝ, ‖H x‖ ^ (2 : ℝ)) ≤
      ∫ h : ℝ, ‖∫ x : ℝ, ∫ t : ℝ,
        Q x t * starRingEnd ℂ (Q x (t + h))‖ := by
    simpa only [H, Real.rpow_two] using
      (aux_square_timeIntegral_le_autocorrelation_compactSupport
        X J hX hJ Q hQmeas hQbound hQsupport)
  calc
    ‖∫ x : ℝ, g₀ x * ∫ t : ℝ, Q x t‖ ^ (2 : ℕ) =
        ‖∫ x : ℝ, g₀ x * H x‖ ^ (2 : ℕ) := by rfl
    _ ≤ volume.real A * (∫ x : ℝ, ‖H x‖ ^ (2 : ℝ)) := houter
    _ ≤ volume.real A * ∫ h : ℝ, ‖∫ x : ℝ, ∫ t : ℝ,
        Q x t * starRingEnd ℂ (Q x (t + h))‖ := by
      exact mul_le_mul_of_nonneg_left hauto MeasureTheory.measureReal_nonneg

/-- A change of variables for a nonnegative extended-real integral under a
nonzero scalar dilation.  The inequality form needs no measurability
assumption on the integrand and is sufficient for the final `u³` comparison
in `gowersDifferencing`. -/
lemma aux_lintegral_comp_mul_le (F : ℝ → ℝ≥0∞) (c : ℝ) (hc : c ≠ 0) :
    ∫⁻ h : ℝ, F (c * h) ≤ ENNReal.ofReal |c⁻¹| * ∫⁻ r : ℝ, F r := by
  let G : ℝ → ℝ≥0∞ := fun h ↦ F (c * h)
  have hmap := MeasureTheory.lintegral_map_le (μ := volume) G (fun r : ℝ ↦ c⁻¹ * r)
  have hmap' : (ENNReal.ofReal |c|) * (∫⁻ h : ℝ, G h) ≤ ∫⁻ r : ℝ, F r := by
    calc
      (ENNReal.ofReal |c|) * (∫⁻ h : ℝ, G h) =
          ∫⁻ h : ℝ, G h ∂Measure.map (fun r : ℝ ↦ c⁻¹ * r) volume := by
        have hc' : c⁻¹ ≠ 0 := inv_ne_zero hc
        rw [Real.map_volume_mul_left hc', lintegral_smul_measure]
        simp [inv_inv, smul_eq_mul]
      _ ≤ ∫⁻ r : ℝ, G (c⁻¹ * r) := hmap
      _ = ∫⁻ r : ℝ, F r := by
        apply lintegral_congr
        intro r
        dsimp [G]
        congr 1
        field_simp
  calc
    ∫⁻ h : ℝ, F (c * h) = 1 * ∫⁻ h : ℝ, G h := by simp [G]
    _ = (ENNReal.ofReal |c⁻¹| * ENNReal.ofReal |c|) * ∫⁻ h : ℝ, G h := by
      rw [← ENNReal.ofReal_mul]
      · have hprod : |c⁻¹| * |c| = 1 := by
          rw [← abs_mul]
          field_simp
          simp
        rw [hprod]
        simp
      · exact abs_nonneg _
    _ = ENNReal.ofReal |c⁻¹| * ((ENNReal.ofReal |c|) * ∫⁻ h : ℝ, G h) := by
      ring
    _ ≤ ENNReal.ofReal |c⁻¹| * ∫⁻ r : ℝ, F r :=
      by simpa [mul_comm] using
        (mul_le_mul_left hmap' (ENNReal.ofReal |c⁻¹|))

/-- The determinant-one shear `(x,t) ↦ (x-c*t,t)` preserves product
Lebesgue measure.  It aligns the first affine factor in the autocorrelation
calculation of `gowersDifferencing`. -/
lemma aux_measurePreserving_sub_mul_prod (c : ℝ) :
    MeasurePreserving (fun z : ℝ × ℝ ↦ (z.1 - c * z.2, z.2))
      (volume.prod volume) (volume.prod volume) := by
  let shear : ℝ × ℝ → ℝ × ℝ := fun z ↦ (z.1, z.2 - c * z.1)
  have hshear : MeasurePreserving shear (volume.prod volume) (volume.prod volume) := by
    refine MeasurePreserving.skew_product (g := fun t x : ℝ ↦ x - c * t)
      (MeasurePreserving.id (α := ℝ) volume) ?_ ?_
    · fun_prop
    · filter_upwards with t
      simpa only [sub_eq_add_neg] using
        (measurePreserving_add_right volume (-(c * t))).map_eq
  have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ)
      (volume.prod volume) (volume.prod volume) := Measure.measurePreserving_swap
  apply (hswap.comp (hshear.comp hswap)).congr
  · fun_prop
  · filter_upwards with z
    rcases z with ⟨x, t⟩
    simp [shear]

/-- Applying the determinant-one shear to an integrable two-variable
function does not change its iterated integral. -/
lemma aux_integral_shear_sub_mul
    (F : ℝ → ℝ → ℂ) (hF : Integrable (Function.uncurry F) (volume.prod volume))
    (c : ℝ) :
    (∫ x : ℝ, ∫ t : ℝ, F (x - c * t) t) = ∫ x : ℝ, ∫ t : ℝ, F x t := by
  have hG : Integrable
      (Function.uncurry fun x t : ℝ ↦ F (x - c * t) t) (volume.prod volume) := by
    change Integrable
      ((Function.uncurry F) ∘ fun z : ℝ × ℝ ↦ (z.1 - c * z.2, z.2))
      (volume.prod volume)
    rw [← memLp_one_iff_integrable] at hF ⊢
    exact hF.comp_measurePreserving (aux_measurePreserving_sub_mul_prod c)
  calc
    (∫ x : ℝ, ∫ t : ℝ, F (x - c * t) t) =
        ∫ t : ℝ, ∫ x : ℝ, F (x - c * t) t := integral_integral_swap hG
    _ = ∫ t : ℝ, ∫ x : ℝ, F x t := by
      apply integral_congr_ae
      filter_upwards with t
      simpa only [sub_eq_add_neg] using
        (integral_add_right_eq_self (fun x : ℝ ↦ F x t) (-(c * t)))
    _ = ∫ x : ℝ, ∫ t : ℝ, F x t := (integral_integral_swap hF).symm

/-- Pointwise algebra for the determinant-one shear that aligns the first
factor of the autocorrelation of `aux_gowersKernel`. -/
lemma aux_gowersKernel_correlation_shear_pointwise
    (g₁ g₂ g₃ : ℝ → ℂ) (ψ : ℝ → ℝ)
    (c₁ c₂ c₃ h x t : ℝ) :
    (g₁ (x - c₁ * t + c₁ * t) *
        g₂ (x - c₁ * t + c₂ * t) *
        g₃ (x - c₁ * t + c₃ * t) * (ψ t : ℂ)) *
      starRingEnd ℂ
        (g₁ (x - c₁ * t + c₁ * (t + h)) *
          g₂ (x - c₁ * t + c₂ * (t + h)) *
          g₃ (x - c₁ * t + c₃ * (t + h)) * (ψ (t + h) : ℂ)) =
      multiplicativeDifference (c₁ * h) g₁ x *
        multiplicativeDifference (c₂ * h) g₂ (x + (c₂ - c₁) * t) *
        multiplicativeDifference (c₃ * h) g₃ (x + (c₃ - c₁) * t) *
          ((ψ t * ψ (t + h) : ℝ) : ℂ) := by
  have h₁₁ : x - c₁ * t + c₁ * t = x := by ring
  have h₂₁ : x - c₁ * t + c₂ * t = x + (c₂ - c₁) * t := by ring
  have h₃₁ : x - c₁ * t + c₃ * t = x + (c₃ - c₁) * t := by ring
  have h₁₂ : x - c₁ * t + c₁ * (t + h) = x + c₁ * h := by ring
  have h₂₂ : x - c₁ * t + c₂ * (t + h) = x + (c₂ - c₁) * t + c₂ * h := by ring
  have h₃₂ : x - c₁ * t + c₃ * (t + h) = x + (c₃ - c₁) * t + c₃ * h := by ring
  rw [h₁₁, h₂₁, h₃₁, h₁₂, h₂₂, h₃₂]
  simp only [multiplicativeDifference, map_mul]
  rw [Complex.conj_ofReal, Complex.ofReal_mul]
  ring

/-- At a fixed time difference, align the first factor in the
autocorrelation of `aux_gowersKernel` by the coordinate `y = x + c 1 * t`. -/
lemma aux_gowersKernel_correlation_change
    (c : Fin 4 → ℝ) (g : Fin 4 → ℝ → ℂ) (ψ : ℝ → ℝ) (h : ℝ)
    (hF : Integrable
      (Function.uncurry fun x t : ℝ ↦
        aux_gowersKernel c g ψ x t *
          starRingEnd ℂ (aux_gowersKernel c g ψ x (t + h)))
      (volume.prod volume)) :
    (∫ x : ℝ, ∫ t : ℝ,
      aux_gowersKernel c g ψ x t *
        starRingEnd ℂ (aux_gowersKernel c g ψ x (t + h))) =
      ∫ y : ℝ, ∫ t : ℝ,
        multiplicativeDifference (c 1 * h) (g 1) y *
          multiplicativeDifference (c 2 * h) (g 2)
            (y + (c 2 - c 1) * t) *
          multiplicativeDifference (c 3 * h) (g 3)
            (y + (c 3 - c 1) * t) *
          ((ψ t * ψ (t + h) : ℝ) : ℂ) := by
  let F : ℝ → ℝ → ℂ := fun x t ↦
    aux_gowersKernel c g ψ x t *
      starRingEnd ℂ (aux_gowersKernel c g ψ x (t + h))
  have hshear : (∫ x : ℝ, ∫ t : ℝ, F (x - c 1 * t) t) =
      ∫ x : ℝ, ∫ t : ℝ, F x t := by
    apply aux_integral_shear_sub_mul F
    simpa only [F] using hF
  calc
    (∫ x : ℝ, ∫ t : ℝ,
      aux_gowersKernel c g ψ x t *
        starRingEnd ℂ (aux_gowersKernel c g ψ x (t + h))) =
        ∫ y : ℝ, ∫ t : ℝ, F (y - c 1 * t) t := by
      simpa only [F] using hshear.symm
    _ = ∫ y : ℝ, ∫ t : ℝ,
        multiplicativeDifference (c 1 * h) (g 1) y *
          multiplicativeDifference (c 2 * h) (g 2)
            (y + (c 2 - c 1) * t) *
          multiplicativeDifference (c 3 * h) (g 3)
            (y + (c 3 - c 1) * t) *
          ((ψ t * ψ (t + h) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with y
      apply integral_congr_ae
      filter_upwards with t
      exact aux_gowersKernel_correlation_shear_pointwise
        (g 1) (g 2) (g 3) ψ (c 1) (c 2) (c 3) h y t

/-- Rescale the time difference in
`aux_gowersKernel_correlation_change` so the first difference is `Δ_h`. -/
lemma aux_gowersKernel_correlation_change_rescaled
    (c : Fin 4 → ℝ) (g : Fin 4 → ℝ → ℂ) (ψ : ℝ → ℝ)
    (hc₁ : c 1 ≠ 0) (h : ℝ)
    (hF : Integrable
      (Function.uncurry fun x t : ℝ ↦
        aux_gowersKernel c g ψ x t *
          starRingEnd ℂ
            (aux_gowersKernel c g ψ x (t + (c 1)⁻¹ * h)))
      (volume.prod volume)) :
    (∫ x : ℝ, ∫ t : ℝ,
      aux_gowersKernel c g ψ x t *
        starRingEnd ℂ
          (aux_gowersKernel c g ψ x (t + (c 1)⁻¹ * h))) =
      ∫ y : ℝ, ∫ t : ℝ,
        multiplicativeDifference h (g 1) y *
          multiplicativeDifference ((c 2 / c 1) * h) (g 2)
            (y + (c 2 - c 1) * t) *
          multiplicativeDifference ((c 3 / c 1) * h) (g 3)
            (y + (c 3 - c 1) * t) *
          ((ψ t * ψ (t + (c 1)⁻¹ * h) : ℝ) : ℂ) := by
  have h₁ : c 1 * ((c 1)⁻¹ * h) = h := by
    field_simp
  have h₂ : c 2 * ((c 1)⁻¹ * h) = (c 2 / c 1) * h := by
    field_simp
  have h₃ : c 3 * ((c 1)⁻¹ * h) = (c 3 / c 1) * h := by
    field_simp
  simpa only [h₁, h₂, h₃] using
    aux_gowersKernel_correlation_change c g ψ ((c 1)⁻¹ * h) hF

/-- The inverse coordinate reorder from `(h,(x,t))` to `((x,h),t)` preserves
product volume.  It converts compact autocorrelation integrability into
almost-everywhere integrability of the fixed-difference sections. -/
lemma aux_measurePreserving_autocorrelation_reorder_symm :
    MeasurePreserving
      (fun z : ℝ × (ℝ × ℝ) ↦ ((z.2.1, z.1), z.2.2))
      (volume.prod (volume.prod volume)) ((volume.prod volume).prod volume) := by
  have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ)
      (volume.prod volume) (volume.prod volume) := Measure.measurePreserving_swap
  have hfirst : MeasurePreserving
      (Prod.map (Prod.swap : ℝ × ℝ → ℝ × ℝ) (id : ℝ → ℝ))
      ((volume.prod volume).prod volume) ((volume.prod volume).prod volume) := by
    exact hswap.prod (MeasurePreserving.id (α := ℝ) volume)
  have hassoc : MeasurePreserving (MeasurableEquiv.prodAssoc :
      (ℝ × ℝ) × ℝ → ℝ × (ℝ × ℝ))
      ((volume.prod volume).prod volume) (volume.prod (volume.prod volume)) :=
    measurePreserving_prodAssoc volume volume volume
  apply (hfirst.comp (hassoc.symm MeasurableEquiv.prodAssoc)).congr
  · fun_prop
  · filter_upwards with z
    rfl

/-- Three-variable autocorrelation integrability gives integrability of the
`(x,t)` correlation section for almost every difference parameter. -/
lemma aux_autocorrelation_section_integrable_ae
    (Q : ℝ → ℝ → ℂ)
    (hR : Integrable
      (Function.uncurry fun p : ℝ × ℝ ↦ fun t : ℝ ↦
        Q p.1 t * starRingEnd ℂ (Q p.1 (t + p.2)))
      ((volume.prod volume).prod volume)) :
    ∀ᵐ h : ℝ ∂volume, Integrable
      (Function.uncurry fun x t : ℝ ↦
        Q x t * starRingEnd ℂ (Q x (t + h)))
      (volume.prod volume) := by
  have hR' : Integrable
      (Function.uncurry fun (h : ℝ) (z : ℝ × ℝ) ↦
        Q z.1 z.2 * starRingEnd ℂ (Q z.1 (z.2 + h)))
      (volume.prod (volume.prod volume)) := by
    change Integrable
      ((Function.uncurry fun p : ℝ × ℝ ↦ fun t : ℝ ↦
        Q p.1 t * starRingEnd ℂ (Q p.1 (t + p.2))) ∘
          fun z : ℝ × (ℝ × ℝ) ↦ ((z.2.1, z.1), z.2.2))
      (volume.prod (volume.prod volume))
    rw [← memLp_one_iff_integrable] at hR ⊢
    exact hR.comp_measurePreserving
      aux_measurePreserving_autocorrelation_reorder_symm
  exact hR'.prod_right_ae

/-- Apply the rescaled Gowers-kernel coordinate identity for almost every
difference parameter, using three-variable autocorrelation integrability. -/
lemma aux_gowersKernel_correlation_change_rescaled_ae
    (c : Fin 4 → ℝ) (g : Fin 4 → ℝ → ℂ) (ψ : ℝ → ℝ)
    (hc₁ : c 1 ≠ 0)
    (hR : Integrable
      (Function.uncurry fun p : ℝ × ℝ ↦ fun t : ℝ ↦
        aux_gowersKernel c g ψ p.1 t *
          starRingEnd ℂ (aux_gowersKernel c g ψ p.1 (t + p.2)))
      ((volume.prod volume).prod volume)) :
    (fun h : ℝ ↦ ∫ x : ℝ, ∫ t : ℝ,
      aux_gowersKernel c g ψ x t *
        starRingEnd ℂ
          (aux_gowersKernel c g ψ x (t + (c 1)⁻¹ * h))) =ᵐ[volume]
      (fun h : ℝ ↦ ∫ y : ℝ, ∫ t : ℝ,
        multiplicativeDifference h (g 1) y *
          multiplicativeDifference ((c 2 / c 1) * h) (g 2)
            (y + (c 2 - c 1) * t) *
          multiplicativeDifference ((c 3 / c 1) * h) (g 3)
            (y + (c 3 - c 1) * t) *
          ((ψ t * ψ (t + (c 1)⁻¹ * h) : ℝ) : ℂ)) := by
  have hsections := aux_autocorrelation_section_integrable_ae
    (aux_gowersKernel c g ψ) hR
  have hscaled : ∀ᵐ h : ℝ ∂volume, Integrable
      (Function.uncurry fun x t : ℝ ↦
        aux_gowersKernel c g ψ x t *
          starRingEnd ℂ
            (aux_gowersKernel c g ψ x (t + (c 1)⁻¹ * h)))
      (volume.prod volume) := by
    have hqmp := aux_gowers_local_qmp_affine_t 0 (c 1)⁻¹ (inv_ne_zero hc₁)
    simpa using hqmp.ae hsections
  filter_upwards [hscaled] with h hh
  exact aux_gowersKernel_correlation_change_rescaled c g ψ hc₁ h hh

/-- The factor vector obtained by restricting the two uncontrolled factors
to their compact interaction ranges before the Cauchy--Schwarz step in
`gowersDifferencing`. -/
def aux_gowersLocalizedFactors (A J : Set ℝ) (c : Fin 4 → ℝ)
    (g : Fin 4 → ℝ → ℂ) : Fin 4 → ℝ → ℂ :=
  ![g 0, g 1,
    aux_gowersRestrict (aux_gowersInteractionRange A J (c 2)) (g 2),
    aux_gowersRestrict (aux_gowersInteractionRange A J (c 3)) (g 3)]

/-- Measurability of the pre-localized factor vector used in
`gowersDifferencing`. -/
lemma aux_gowersLocalizedFactors_aestronglyMeasurable
    (A J : Set ℝ) (c : Fin 4 → ℝ) (g : Fin 4 → ℝ → ℂ)
    (hA : IsCompact A) (hJ : IsCompact J)
    (hg : ∀ i : Fin 4, AEStronglyMeasurable (g i) volume) :
    ∀ i : Fin 4,
      AEStronglyMeasurable (aux_gowersLocalizedFactors A J c g i) volume := by
  intro i
  fin_cases i
  · simpa [aux_gowersLocalizedFactors] using hg 0
  · simpa [aux_gowersLocalizedFactors] using hg 1
  · simpa [aux_gowersLocalizedFactors] using
      (aux_gowersRestrict_aestronglyMeasurable
        (aux_gowersInteractionRange A J (c 2)) (g 2)
        (aux_gowersInteractionRange_measurable A J (c 2) hA hJ) (hg 2))
  · simpa [aux_gowersLocalizedFactors] using
      (aux_gowersRestrict_aestronglyMeasurable
        (aux_gowersInteractionRange A J (c 3)) (g 3)
        (aux_gowersInteractionRange_measurable A J (c 3) hA hJ) (hg 3))

/-- The one-bound persists under the pre-localization used in
`gowersDifferencing`. -/
lemma aux_gowersLocalizedFactors_ae_one_bounded
    (A J : Set ℝ) (c : Fin 4 → ℝ) (g : Fin 4 → ℝ → ℂ)
    (hg : ∀ i : Fin 4, ∀ᵐ x ∂volume, ‖g i x‖ ≤ 1) :
    ∀ i : Fin 4, ∀ᵐ x ∂volume,
      ‖aux_gowersLocalizedFactors A J c g i x‖ ≤ 1 := by
  intro i
  fin_cases i
  · simpa [aux_gowersLocalizedFactors] using hg 0
  · simpa [aux_gowersLocalizedFactors] using hg 1
  · simpa [aux_gowersLocalizedFactors] using
      (aux_gowersRestrict_ae_one_bounded
        (aux_gowersInteractionRange A J (c 2)) (g 2) (hg 2))
  · simpa [aux_gowersLocalizedFactors] using
      (aux_gowersRestrict_ae_one_bounded
        (aux_gowersInteractionRange A J (c 3)) (g 3) (hg 3))

/-- The coordinate map `(x,t) ↦ (x + a t, x + b t)` used in the Fourier kernel. -/
def aux_gowersFourier_linearMap_x_t_to_ax_bt (a b : ℝ) :
    (Fin 2 → ℝ) →ₗ[ℝ] Fin 2 → ℝ :=
  Matrix.toLin' !![1, a; 1, b]

lemma aux_gowersFourier_det_linearMap_x_t_to_ax_bt (a b : ℝ) :
    LinearMap.det (aux_gowersFourier_linearMap_x_t_to_ax_bt a b) = b - a := by
  rw [aux_gowersFourier_linearMap_x_t_to_ax_bt, LinearMap.det_toLin', Matrix.det_fin_two]
  simp

lemma aux_gowersFourier_integral_x_t_to_ax_bt (a b : ℝ) (hab : a ≠ b)
    (F : (Fin 2 → ℝ) → ℂ) (hF : AEStronglyMeasurable F volume) :
    ∫ p : Fin 2 → ℝ, F (aux_gowersFourier_linearMap_x_t_to_ax_bt a b p) =
      |(b - a)⁻¹| • ∫ q : Fin 2 → ℝ, F q := by
  rw [← aux_gowersFourier_det_linearMap_x_t_to_ax_bt]
  apply aux_integral_comp_linearMap_volume
  · rw [aux_gowersFourier_det_linearMap_x_t_to_ax_bt]
    exact sub_ne_zero.mpr hab.symm
  · exact hF

/-- A nonzero affine change of variables preserves `L^p` membership.  The
explicit scale factor is absorbed into the measure before using
`MemLp.comp_of_map`; this is useful for the two Fourier factors in the
bilinear kernel calculation. -/
lemma aux_gowersFourier_memLp_comp_affine (F : ℝ → ℂ) (p : ℝ≥0∞)
    (hF : MemLp F p volume) (a b : ℝ) (ha : a ≠ 0) :
    MemLp (fun x : ℝ ↦ F (a * x + b)) p volume := by
  let s : ℝ → ℝ := fun x ↦ a * x
  have htrans : MemLp (fun y : ℝ ↦ F (y + b)) p volume := by
    simpa only [Function.comp_def] using
      hF.comp_measurePreserving (measurePreserving_add_right volume b)
  have hmap : Measure.map s volume = ENNReal.ofReal |a⁻¹| • volume := by
    simpa only [s, smul_eq_mul, Module.finrank_self, pow_one] using
      (Measure.map_addHaar_smul (μ := volume) (E := ℝ) ha)
  have htransmap : MemLp (fun y : ℝ ↦ F (y + b)) p (Measure.map s volume) := by
    rw [hmap]
    exact htrans.smul_measure ENNReal.ofReal_ne_top
  have hmeas : AEMeasurable s volume :=
    (continuous_const.mul continuous_id).aemeasurable
  have hcomp := htransmap.comp_of_map hmeas
  simpa only [s, Function.comp_def] using hcomp

/-- Exact one-dimensional affine change of variables for the squared norm.
This is the scale computation used after Cauchy--Schwarz on the two Fourier
factors. -/
lemma aux_gowersFourier_integral_norm_sq_comp_affine (F : ℝ → ℂ) (a b : ℝ) :
    ∫ x : ℝ, ‖F (a * x + b)‖ ^ 2 =
      |a⁻¹| * ∫ y : ℝ, ‖F y‖ ^ 2 := by
  let q : ℝ → ℝ := fun y ↦ ‖F (y + b)‖ ^ 2
  calc
    ∫ x : ℝ, ‖F (a * x + b)‖ ^ 2 = ∫ x : ℝ, q (a * x) := by
      congr with x
    _ = |a⁻¹| • ∫ y : ℝ, q y := Measure.integral_comp_mul_left q a
    _ = |a⁻¹| * ∫ y : ℝ, ‖F y‖ ^ 2 := by
      rw [show (∫ y : ℝ, q y) = ∫ y : ℝ, ‖F y‖ ^ 2 by
        exact integral_add_right_eq_self (fun y : ℝ ↦ ‖F y‖ ^ 2) b]
      simp [smul_eq_mul]

/-- Cauchy--Schwarz for two independently affinely reparameterized Fourier
factors.  Combined with `aux_gowersFourier_integral_norm_sq_comp_affine`, this gives the
Jacobian factor in the bilinear kernel Fourier-`L¹` estimate. -/
lemma aux_gowersFourier_integral_norm_mul_comp_affine_le
    (F H : ℝ → ℂ) (hF : MemLp F (2 : ℝ≥0∞) volume)
    (hH : MemLp H (2 : ℝ≥0∞) volume)
    (a b r s : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∫ x : ℝ, ‖F (a * x + r)‖ * ‖H (b * x + s)‖ ≤
      (∫ x : ℝ, ‖F (a * x + r)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (∫ x : ℝ, ‖H (b * x + s)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  have hFa : MemLp (fun x : ℝ ↦ F (a * x + r)) (ENNReal.ofReal (2 : ℝ)) volume := by
    convert aux_gowersFourier_memLp_comp_affine F (2 : ℝ≥0∞) hF a r ha using 1 ; norm_num
  have hHa : MemLp (fun x : ℝ ↦ H (b * x + s)) (ENNReal.ofReal (2 : ℝ)) volume := by
    convert aux_gowersFourier_memLp_comp_affine H (2 : ℝ≥0∞) hH b s hb using 1 ; norm_num
  simpa using
    (MeasureTheory.integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
      hFa hHa)

/-- The affine Cauchy--Schwarz estimate with its scale factors made explicit. -/
lemma aux_gowersFourier_integral_norm_mul_comp_affine_le_scaled
    (F H : ℝ → ℂ) (hF : MemLp F (2 : ℝ≥0∞) volume)
    (hH : MemLp H (2 : ℝ≥0∞) volume)
    (a b r s : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∫ x : ℝ, ‖F (a * x + r)‖ * ‖H (b * x + s)‖ ≤
      (|a⁻¹| * ∫ x : ℝ, ‖F x‖ ^ 2) ^ (1 / (2 : ℝ)) *
        (|b⁻¹| * ∫ x : ℝ, ‖H x‖ ^ 2) ^ (1 / (2 : ℝ)) := by
  simpa only [Real.rpow_two, aux_gowersFourier_integral_norm_sq_comp_affine] using
    aux_gowersFourier_integral_norm_mul_comp_affine_le F H hF hH a b r s ha hb

/-- A Fubini wrapper for the Fourier-kernel argument.  It turns a uniform
`L¹` bound on the inner bilinear Fourier product into joint integrability
after weighting by an `L¹` Fourier cutoff. -/
lemma aux_gowersFourier_integrable_weighted_bilinear_of_section_bound
    (W : ℝ → ℂ) (hW : Integrable W volume)
    (B : ℝ → ℝ → ℂ)
    (hBmeas : AEStronglyMeasurable (Function.uncurry B) (volume.prod volume))
    (hBint : ∀ ξ : ℝ, Integrable (B ξ) volume)
    (C : ℝ) (hBbound : ∀ ξ : ℝ, ∫ η : ℝ, ‖B ξ η‖ ≤ C) :
    Integrable (fun z : ℝ × ℝ ↦ W z.1 * B z.1 z.2) (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable
      (fun z : ℝ × ℝ ↦ W z.1 * B z.1 z.2) (volume.prod volume) :=
    hW.aestronglyMeasurable.comp_fst.mul hBmeas
  apply (integrable_prod_iff hmeas).mpr
  refine ⟨?_, ?_⟩
  · filter_upwards with ξ
    simpa only [Function.uncurry_apply_pair] using (hBint ξ).const_mul (W ξ)
  · apply Integrable.mono' (hW.norm.const_mul C)
      hmeas.norm.integral_prod_right'
    filter_upwards with ξ
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun η ↦ norm_nonneg (W ξ * B ξ η))]
    simp_rw [norm_mul]
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left (hBbound ξ) (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- The Fourier-`L¹` estimate for a single modulated affine kernel once its
standard factored Fourier formula has been established.  The two factors are
handled by the preceding affine Cauchy--Schwarz estimate. -/
lemma aux_gowersFourier_integral_norm_smul_affine_fourier_product_le
    (F H : ℝ → ℂ) (hF : MemLp F (2 : ℝ≥0∞) volume)
    (hH : MemLp H (2 : ℝ≥0∞) volume)
    (d α β r s : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0) :
    ∫ ξ : ℝ, ‖d • (F (α * ξ + r) * H (β * ξ + s))‖ ≤
      |d| *
        ((|α⁻¹| * ∫ x : ℝ, ‖F x‖ ^ 2) ^ (1 / (2 : ℝ)) *
          (|β⁻¹| * ∫ x : ℝ, ‖H x‖ ^ 2) ^ (1 / (2 : ℝ))) := by
  rw [show (fun ξ : ℝ ↦ ‖d • (F (α * ξ + r) * H (β * ξ + s))‖) =
      fun ξ ↦ |d| * (‖F (α * ξ + r)‖ * ‖H (β * ξ + s)‖) by
    funext ξ
    rw [norm_smul, Real.norm_eq_abs, norm_mul]]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (aux_gowersFourier_integral_norm_mul_comp_affine_le_scaled F H hF hH α β r s hα hβ)
    (abs_nonneg d)

/-- Phase algebra for the modulated affine kernel. -/
lemma aux_gowersFourier_modulated_affine_phase_change
    (a b s ξ x t : ℝ) (hab : a ≠ b) :
    (𝐞 (-(x * ξ)) : ℂ) * (𝐞 (s * t) : ℂ) =
      (𝐞 (-((x + a * t) * ((s + b * ξ) / (b - a)))) : ℂ) *
        (𝐞 (-((x + b * t) * (-(s + a * ξ) / (b - a)))) : ℂ) := by
  rw [← Circle.coe_mul, ← Circle.coe_mul]
  congr 1
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  field_simp [sub_ne_zero.mpr hab.symm]
  ring

def aux_gowersFourier_modulatedAffineKernel (a b s : ℝ) (G H : ℝ → ℂ) : ℝ → ℂ :=
  fun x ↦ ∫ t : ℝ, G (x + a * t) * H (x + b * t) * (𝐞 (s * t) : ℂ)

def aux_gowersFourier_modulatedKernelJoint (a b s ξ : ℝ) (G H : ℝ → ℂ)
    (p : Fin 2 → ℝ) : ℂ :=
  ((𝐞 (-(p 0 * ξ)) : ℂ) * (𝐞 (s * p 1) : ℂ)) *
    (G (p 0 + a * p 1) * H (p 0 + b * p 1))

def aux_gowersFourier_modulatedKernelJointTrans (a b s ξ : ℝ) (G H : ℝ → ℂ)
    (q : Fin 2 → ℝ) : ℂ :=
  ((𝐞 (-(q 0 * ((s + b * ξ) / (b - a)))) : ℂ) * G (q 0)) *
    ((𝐞 (-(q 1 * (-(s + a * ξ) / (b - a))) : ℝ) : ℂ) * H (q 1))

lemma aux_gowersFourier_modulatedKernelJointTrans_comp_linear
    (a b s ξ : ℝ) (G H : ℝ → ℂ) (hab : a ≠ b) (p : Fin 2 → ℝ) :
    aux_gowersFourier_modulatedKernelJointTrans a b s ξ G H
        (aux_gowersFourier_linearMap_x_t_to_ax_bt a b p) =
      aux_gowersFourier_modulatedKernelJoint a b s ξ G H p := by
  have h0 : !![1, a; 1, b].mulVec p 0 = p 0 + a * p 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h1 : !![1, a; 1, b].mulVec p 1 = p 0 + b * p 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  simp only [aux_gowersFourier_modulatedKernelJointTrans, aux_gowersFourier_modulatedKernelJoint,
    aux_gowersFourier_linearMap_x_t_to_ax_bt, Matrix.toLin'_apply]
  rw [h0, h1]
  calc
    _ = ((𝐞 (-((p 0 + a * p 1) * ((s + b * ξ) / (b - a)))) : ℂ) *
          (𝐞 (-((p 0 + b * p 1) * (-(s + a * ξ) / (b - a))) : ℝ) : ℂ)) *
        (G (p 0 + a * p 1) * H (p 0 + b * p 1)) := by ring
    _ = ((𝐞 (-(p 0 * ξ)) : ℂ) * (𝐞 (s * p 1) : ℂ)) *
        (G (p 0 + a * p 1) * H (p 0 + b * p 1)) := by
      rw [(aux_gowersFourier_modulated_affine_phase_change a b s ξ (p 0) (p 1) hab).symm]
    _ = _ := by ring

lemma aux_gowersFourier_integral_modulatedKernelJointTrans
    (a b s ξ : ℝ) (G H : ℝ → ℂ) :
    ∫ q : Fin 2 → ℝ, aux_gowersFourier_modulatedKernelJointTrans a b s ξ G H q =
      (𝓕 G ((s + b * ξ) / (b - a))) *
        (𝓕 H (-(s + a * ξ) / (b - a))) := by
  let f₀ : ℝ → ℂ := fun u ↦
    (𝐞 (-(u * ((s + b * ξ) / (b - a))) : ℝ) : ℂ) * G u
  let f₁ : ℝ → ℂ := fun v ↦
    (𝐞 (-(v * (-(s + a * ξ) / (b - a))) : ℝ) : ℂ) * H v
  have hfactor : aux_gowersFourier_modulatedKernelJointTrans a b s ξ G H =
      fun q ↦ f₀ (q 0) * f₁ (q 1) := by
    funext q
    rfl
  rw [hfactor]
  have hprod : (fun q : Fin 2 → ℝ ↦ f₀ (q 0) * f₁ (q 1)) =
      fun q ↦ ∏ i : Fin 2, ![f₀, f₁] i (q i) := by
    funext q
    simp
  rw [hprod, integral_fintype_prod_volume_eq_prod]
  simp only [Fin.prod_univ_two]
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  simp [f₀, f₁, Circle.smul_def, smul_eq_mul]

/-- The two-variable joint integrand, written on the product measure so that
Fubini can expose the raw Fourier transform of the affine kernel. -/
def aux_gowersFourier_modulatedKernelJointPair (a b s ξ : ℝ) (G H : ℝ → ℂ)
    (z : ℝ × ℝ) : ℂ :=
  aux_gowersFourier_modulatedKernelJoint a b s ξ G H ![z.1, z.2]

lemma aux_gowersFourier_fourier_modulatedAffineKernel_eq_joint_pair
    (a b s ξ : ℝ) (G H : ℝ → ℂ) :
    𝓕 (aux_gowersFourier_modulatedAffineKernel a b s G H) ξ =
      ∫ x : ℝ, ∫ t : ℝ,
        aux_gowersFourier_modulatedKernelJointPair a b s ξ G H (x, t) := by
  rw [Real.fourier_real_eq]
  simp only [aux_gowersFourier_modulatedAffineKernel]
  apply integral_congr_ae
  filter_upwards with x
  rw [Circle.smul_def, smul_eq_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  simp [aux_gowersFourier_modulatedKernelJointPair,
    aux_gowersFourier_modulatedKernelJoint]
  ring

lemma aux_gowersFourier_integral_modulatedKernelJoint_eq_joint_pair
    (a b s ξ : ℝ) (G H : ℝ → ℂ) :
    ∫ p : Fin 2 → ℝ, aux_gowersFourier_modulatedKernelJoint a b s ξ G H p =
      ∫ z : ℝ × ℝ, aux_gowersFourier_modulatedKernelJointPair a b s ξ G H z
        ∂(volume.prod volume) := by
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)
  calc
    ∫ p : Fin 2 → ℝ, aux_gowersFourier_modulatedKernelJoint a b s ξ G H p =
        ∫ p : Fin 2 → ℝ, aux_gowersFourier_modulatedKernelJointPair a b s ξ G H (e p) := by
      apply integral_congr_ae
      filter_upwards with p
      have hp : p = ![p 0, p 1] := by
        funext i
        fin_cases i <;> simp
      rw [hp]
      simp [e, aux_gowersFourier_modulatedKernelJointPair]
    _ = ∫ z : ℝ × ℝ, aux_gowersFourier_modulatedKernelJointPair a b s ξ G H z := by
      exact (volume_preserving_piFinTwo (fun _ : Fin 2 ↦ ℝ)).integral_comp' _
    _ = ∫ z : ℝ × ℝ, aux_gowersFourier_modulatedKernelJointPair a b s ξ G H z
        ∂(volume.prod volume) := by rw [← Measure.volume_eq_prod]

/-- Exact raw Fourier formula for the modulated affine kernel.  The two
analytic hypotheses are precisely the Fubini and change-of-variables
measurability obligations; they can be derived, for example, from compactly
supported continuous inputs. -/
lemma aux_gowersFourier_fourier_modulatedAffineKernel_eq
    (a b s ξ : ℝ) (G H : ℝ → ℂ) (hab : a ≠ b)
    (hjoint : Integrable (aux_gowersFourier_modulatedKernelJointPair a b s ξ G H)
      (volume.prod volume))
    (htrans : AEStronglyMeasurable
      (aux_gowersFourier_modulatedKernelJointTrans a b s ξ G H) volume) :
    𝓕 (aux_gowersFourier_modulatedAffineKernel a b s G H) ξ =
      |(b - a)⁻¹| •
        ((𝓕 G ((s + b * ξ) / (b - a))) *
          (𝓕 H (-(s + a * ξ) / (b - a)))) := by
  rw [aux_gowersFourier_fourier_modulatedAffineKernel_eq_joint_pair]
  rw [← integral_prod _ hjoint]
  rw [← aux_gowersFourier_integral_modulatedKernelJoint_eq_joint_pair]
  calc
    ∫ p : Fin 2 → ℝ, aux_gowersFourier_modulatedKernelJoint a b s ξ G H p =
        ∫ p : Fin 2 → ℝ,
          aux_gowersFourier_modulatedKernelJointTrans a b s ξ G H
            (aux_gowersFourier_linearMap_x_t_to_ax_bt a b p) := by
      apply integral_congr_ae
      filter_upwards with p
      exact (aux_gowersFourier_modulatedKernelJointTrans_comp_linear a b s ξ G H hab p).symm
    _ = |(b - a)⁻¹| •
        ∫ q : Fin 2 → ℝ, aux_gowersFourier_modulatedKernelJointTrans a b s ξ G H q :=
      aux_gowersFourier_integral_x_t_to_ax_bt a b hab _ htrans
    _ = _ := by rw [aux_gowersFourier_integral_modulatedKernelJointTrans]

lemma aux_gowersFourier_integrable_fourier_phase_mul (G : ℝ → ℂ) (hG : Integrable G volume)
    (r : ℝ) :
    Integrable (fun x : ℝ ↦ (𝐞 (-(x * r)) : ℂ) * G x) volume := by
  apply hG.bdd_mul (c := 1)
  · exact (continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards with x
    simp

lemma aux_gowersFourier_integrable_modulatedKernelJointTrans
    (a b s ξ : ℝ) (G H : ℝ → ℂ)
    (hG : Integrable G volume) (hH : Integrable H volume) :
    Integrable (aux_gowersFourier_modulatedKernelJointTrans a b s ξ G H) volume := by
  let f₀ : ℝ → ℂ := fun u ↦
    (𝐞 (-(u * ((s + b * ξ) / (b - a))) : ℝ) : ℂ) * G u
  let f₁ : ℝ → ℂ := fun v ↦
    (𝐞 (-(v * (-(s + a * ξ) / (b - a))) : ℝ) : ℂ) * H v
  have hf₀ : Integrable f₀ volume := by
    exact aux_gowersFourier_integrable_fourier_phase_mul G hG _
  have hf₁ : Integrable f₁ volume := by
    exact aux_gowersFourier_integrable_fourier_phase_mul H hH _
  have hprod : Integrable (fun q : Fin 2 → ℝ ↦
      ∏ i : Fin 2, ![f₀, f₁] i (q i)) volume := by
    rw [volume_pi]
    apply Integrable.fintype_prod
    intro i
    fin_cases i
    · exact hf₀
    · exact hf₁
  convert hprod using 1
  funext q
  simp [aux_gowersFourier_modulatedKernelJointTrans, f₀, f₁]

lemma aux_gowersFourier_integrable_modulatedKernelJointPair
    (a b s ξ : ℝ) (G H : ℝ → ℂ) (hab : a ≠ b)
    (hG : Integrable G volume) (hH : Integrable H volume) :
    Integrable (aux_gowersFourier_modulatedKernelJointPair a b s ξ G H)
      (volume.prod volume) := by
  let L := aux_gowersFourier_linearMap_x_t_to_ax_bt a b
  let T := aux_gowersFourier_modulatedKernelJointTrans a b s ξ G H
  have hT : Integrable T volume := by
    exact aux_gowersFourier_integrable_modulatedKernelJointTrans a b s ξ G H hG hH
  have hdet : LinearMap.det L ≠ 0 := by
    rw [show L = aux_gowersFourier_linearMap_x_t_to_ax_bt a b by rfl,
      aux_gowersFourier_det_linearMap_x_t_to_ax_bt]
    exact sub_ne_zero.mpr hab.symm
  have hmap : Measure.map L volume =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume :=
    Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet
  have hTmap : Integrable T (Measure.map L volume) := by
    rw [hmap]
    exact hT.smul_measure ENNReal.ofReal_ne_top
  have hcomp : Integrable (T ∘ L) volume := by
    exact hTmap.comp_measurable
      (LinearMap.continuous_of_finiteDimensional L).measurable
  have hJ : Integrable (aux_gowersFourier_modulatedKernelJoint a b s ξ G H) volume := by
    convert hcomp using 1
    funext p
    exact (aux_gowersFourier_modulatedKernelJointTrans_comp_linear a b s ξ G H hab p).symm
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)
  have hcompPair :
      Integrable (aux_gowersFourier_modulatedKernelJointPair a b s ξ G H ∘ e) volume := by
    convert hJ using 1
    funext p
    have hp : p = ![p 0, p 1] := by
      funext i
      fin_cases i <;> simp
    rw [hp]
    simp [e, aux_gowersFourier_modulatedKernelJointPair]
  rw [← Measure.volume_eq_prod]
  exact ((volume_preserving_piFinTwo (fun _ : Fin 2 ↦ ℝ)).integrable_comp_emb
    (MeasurableEquiv.piFinTwo _).measurableEmbedding).mp hcompPair

/-- Raw Fourier factorization for the modulated affine kernel, now with all
Fubini and change-of-variable side conditions derived just from `L¹` input.
This is the form to combine with `L²` Plancherel/Cauchy--Schwarz. -/
lemma aux_gowersFourier_fourier_modulatedAffineKernel_eq_of_integrable
    (a b s ξ : ℝ) (G H : ℝ → ℂ) (hab : a ≠ b)
    (hG : Integrable G volume) (hH : Integrable H volume) :
    𝓕 (aux_gowersFourier_modulatedAffineKernel a b s G H) ξ =
      |(b - a)⁻¹| •
        ((𝓕 G ((s + b * ξ) / (b - a))) *
          (𝓕 H (-(s + a * ξ) / (b - a)))) := by
  apply aux_gowersFourier_fourier_modulatedAffineKernel_eq a b s ξ G H hab
  · exact aux_gowersFourier_integrable_modulatedKernelJointPair a b s ξ G H hab hG hH
  · exact
      (aux_gowersFourier_integrable_modulatedKernelJointTrans
        a b s ξ G H hG hH).aestronglyMeasurable

lemma aux_gowersFourier_integrable_fourier_modulatedAffineKernel
    (a b s : ℝ) (G H : ℝ → ℂ) (hab : a ≠ b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hG : Integrable G volume) (hH : Integrable H volume)
    (hFG : MemLp (𝓕 G) (2 : ℝ≥0∞) volume)
    (hFH : MemLp (𝓕 H) (2 : ℝ≥0∞) volume) :
    Integrable (𝓕 (aux_gowersFourier_modulatedAffineKernel a b s G H)) volume := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  let α : ℝ := b / (b - a)
  let β : ℝ := -a / (b - a)
  let r : ℝ := s / (b - a)
  let q : ℝ := -s / (b - a)
  have hα : α ≠ 0 := by
    exact div_ne_zero hb hba
  have hβ : β ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr ha) hba
  have hFGα : MemLp (fun ξ : ℝ ↦ 𝓕 G (α * ξ + r)) (2 : ℝ≥0∞) volume := by
    exact aux_gowersFourier_memLp_comp_affine (𝓕 G) 2 hFG α r hα
  have hFHβ : MemLp (fun ξ : ℝ ↦ 𝓕 H (β * ξ + q)) (2 : ℝ≥0∞) volume := by
    exact aux_gowersFourier_memLp_comp_affine (𝓕 H) 2 hFH β q hβ
  have hprod : MemLp (fun ξ : ℝ ↦
      (𝓕 G (α * ξ + r)) * (𝓕 H (β * ξ + q))) (1 : ℝ≥0∞) volume := by
    exact hFHβ.mul hFGα
  have hmod : Integrable (fun ξ : ℝ ↦ |(b - a)⁻¹| •
      ((𝓕 G (α * ξ + r)) * (𝓕 H (β * ξ + q))) ) volume := by
    rw [← memLp_one_iff_integrable]
    exact hprod.const_smul (|(b - a)⁻¹| : ℝ)
  apply hmod.congr
  filter_upwards with ξ
  rw [aux_gowersFourier_fourier_modulatedAffineKernel_eq_of_integrable a b s ξ G H hab hG hH]
  congr 3
  · dsimp [α, r]
    field_simp [hba]
    ring_nf
  · dsimp [β, q]
    field_simp [hba]
    ring_nf

/-- The Fourier `L¹` bound following from the raw factorization and affine
Cauchy--Schwarz. `G,H` are required in `L¹` only for the raw factorization;
the actual bound uses their raw Fourier `L²` representatives. -/
lemma aux_gowersFourier_integral_norm_fourier_modulatedAffineKernel_le
    (a b s : ℝ) (G H : ℝ → ℂ) (hab : a ≠ b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hG : Integrable G volume) (hH : Integrable H volume)
    (hFG : MemLp (𝓕 G) (2 : ℝ≥0∞) volume)
    (hFH : MemLp (𝓕 H) (2 : ℝ≥0∞) volume) :
    ∫ ξ : ℝ, ‖𝓕 (aux_gowersFourier_modulatedAffineKernel a b s G H) ξ‖ ≤
      |(b - a)⁻¹| *
        ((|(b / (b - a))⁻¹| * ∫ x : ℝ, ‖𝓕 G x‖ ^ 2) ^ (1 / (2 : ℝ)) *
          (|(-a / (b - a))⁻¹| * ∫ x : ℝ, ‖𝓕 H x‖ ^ 2) ^ (1 / (2 : ℝ))) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hα : b / (b - a) ≠ 0 := div_ne_zero hb hba
  have hβ : -a / (b - a) ≠ 0 := div_ne_zero (neg_ne_zero.mpr ha) hba
  calc
    ∫ ξ : ℝ, ‖𝓕 (aux_gowersFourier_modulatedAffineKernel a b s G H) ξ‖ =
        ∫ ξ : ℝ, ‖|(b - a)⁻¹| •
          ((𝓕 G ((b / (b - a)) * ξ + s / (b - a))) *
            (𝓕 H ((-a / (b - a)) * ξ + -s / (b - a))))‖ := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [aux_gowersFourier_fourier_modulatedAffineKernel_eq_of_integrable a b s ξ G H hab hG hH]
      congr 3 <;> field_simp [hba] <;> ring_nf
    _ ≤ _ := by
      simpa only [abs_abs] using
        (aux_gowersFourier_integral_norm_smul_affine_fourier_product_le (𝓕 G) (𝓕 H) hFG hFH
          |(b - a)⁻¹| (b / (b - a)) (-a / (b - a))
          (s / (b - a)) (-s / (b - a)) hα hβ)

lemma aux_gowersFourier_affine_jacobian_coefficient_sqrt
    (a b : ℝ) (hab : a ≠ b) (ha : a ≠ 0) (hb : b ≠ 0) :
    |(b - a)⁻¹| *
        (|(b / (b - a))⁻¹| ^ (1 / (2 : ℝ)) *
          |(-a / (b - a))⁻¹| ^ (1 / (2 : ℝ))) =
      |(a * b)⁻¹| ^ (1 / (2 : ℝ)) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hid : |(b - a)⁻¹| ^ 2 * |(b / (b - a))⁻¹| *
      |(-a / (b - a))⁻¹| = |(a * b)⁻¹| := by
    rw [show |(b - a)⁻¹| ^ 2 = |(b - a)⁻¹ * (b - a)⁻¹| by
      rw [abs_mul, pow_two]]
    rw [← abs_mul, ← abs_mul]
    have hprod : (b - a)⁻¹ * (b - a)⁻¹ * (b / (b - a))⁻¹ *
        (-a / (b - a))⁻¹ = -((a * b)⁻¹) := by
      field_simp [hba, ha, hb]
    rw [hprod, abs_neg]
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (abs_nonneg _),
    Real.sq_sqrt (abs_nonneg _), Real.sq_sqrt (abs_nonneg _)]
  nlinarith

/-- The physical modulated affine kernel is integrable when both input factors
are integrable.  This is the `ξ = 0` instance of the joint Fubini package
behind the raw Fourier factorization. -/
lemma aux_gowersFourier_integrable_modulatedAffineKernel
    (a b s : ℝ) (G H : ℝ → ℂ) (hab : a ≠ b)
    (hG : Integrable G volume) (hH : Integrable H volume) :
    Integrable (aux_gowersFourier_modulatedAffineKernel a b s G H) volume := by
  have hjoint := aux_gowersFourier_integrable_modulatedKernelJointPair a b s 0 G H hab hG hH
  have hjoint' : Integrable
      (fun z : ℝ × ℝ ↦ G (z.1 + a * z.2) * H (z.1 + b * z.2) *
        (𝐞 (s * z.2) : ℂ)) (volume.prod volume) := by
    convert hjoint using 1
    funext z
    simp [aux_gowersFourier_modulatedKernelJointPair,
      aux_gowersFourier_modulatedKernelJoint]
    ring
  have hleft := hjoint'.integral_prod_left
  change Integrable (fun x : ℝ ↦ ∫ t : ℝ,
    G (x + a * t) * H (x + b * t) * (𝐞 (s * t) : ℂ)) volume
  exact hleft

/-- Pointwise Cauchy--Schwarz bound for the physical modulated affine kernel.
The phase has norm one, so the bound is uniform in the modulation parameter
and spatial point. -/
lemma aux_gowersFourier_norm_modulatedAffineKernel_le
    (a b s x : ℝ) (G H : ℝ → ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hG : MemLp G (2 : ℝ≥0∞) volume)
    (hH : MemLp H (2 : ℝ≥0∞) volume) :
    ‖aux_gowersFourier_modulatedAffineKernel a b s G H x‖ ≤
      (|a⁻¹| * ∫ z : ℝ, ‖G z‖ ^ 2) ^ (1 / (2 : ℝ)) *
        (|b⁻¹| * ∫ z : ℝ, ‖H z‖ ^ 2) ^ (1 / (2 : ℝ)) := by
  calc
    ‖aux_gowersFourier_modulatedAffineKernel a b s G H x‖ ≤
        ∫ t : ℝ, ‖G (x + a * t) * H (x + b * t) * (𝐞 (s * t) : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ t : ℝ, ‖G (a * t + x)‖ * ‖H (b * t + x)‖ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [norm_mul, norm_mul]
      rw [add_comm x (a * t), add_comm x (b * t)]
      simp
    _ ≤ _ := aux_gowersFourier_integral_norm_mul_comp_affine_le_scaled G H hG hH
      a b x x ha hb

/-- `L¹` plus the preceding uniform physical-space bound puts the modulated
affine kernel in `L²`.  This is the bridge needed to use the measurable
Plancherel pairing without assuming continuity of either rough input. -/
lemma aux_gowersFourier_memLp_modulatedAffineKernel_two
    (a b s : ℝ) (G H : ℝ → ℂ) (hab : a ≠ b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hG1 : Integrable G volume) (hH1 : Integrable H volume)
    (hG2 : MemLp G (2 : ℝ≥0∞) volume)
    (hH2 : MemLp H (2 : ℝ≥0∞) volume) :
    MemLp (aux_gowersFourier_modulatedAffineKernel a b s G H) (2 : ℝ≥0∞) volume := by
  let K := aux_gowersFourier_modulatedAffineKernel a b s G H
  let B : ℝ :=
    (|a⁻¹| * ∫ z : ℝ, ‖G z‖ ^ 2) ^ (1 / (2 : ℝ)) *
      (|b⁻¹| * ∫ z : ℝ, ‖H z‖ ^ 2) ^ (1 / (2 : ℝ))
  have hK1 : Integrable K volume := by
    exact aux_gowersFourier_integrable_modulatedAffineKernel a b s G H hab hG1 hH1
  have hbound : ∀ x : ℝ, ‖K x‖ ≤ B := by
    intro x
    exact aux_gowersFourier_norm_modulatedAffineKernel_le a b s x G H ha hb hG2 hH2
  have hsq : Integrable (fun x : ℝ ↦ ‖K x‖ ^ 2) volume := by
    have hmul := hK1.norm.bdd_mul hK1.norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ by simpa using hbound x)
    simpa only [pow_two] using hmul
  exact (memLp_two_iff_integrable_sq_norm hK1.aestronglyMeasurable).mpr hsq

/-- The raw Fourier integral of an `L¹ ∩ L²` function is itself an `L²`
function, via the already-proved raw--Plancherel representative bridge. -/
lemma aux_gowersFourier_memLp_rawFourier_two (f : ℝ → ℂ)
    (hf1 : MemLp f (1 : ℝ≥0∞) volume)
    (hf2 : MemLp f (2 : ℝ≥0∞) volume) :
    MemLp (𝓕 f) (2 : ℝ≥0∞) volume := by
  refine (memLp_congr_ae (Filter.EventuallyEq.symm
    (Auto.aux_l2Fourier_eq_raw_ae f hf1 hf2))).mpr ?_
  exact Lp.memLp (Lp.fourierTransformₗᵢ ℝ ℂ hf2.toLp)

/-- Plancherel expressed in the real-integral normalization used by the
affine kernel bound. -/
lemma aux_gowersFourier_rawFourier_l2_norm_eq (f : ℝ → ℂ)
    (hf1 : MemLp f (1 : ℝ≥0∞) volume)
    (hf2 : MemLp f (2 : ℝ≥0∞) volume) :
    (∫ x : ℝ, ‖𝓕 f x‖ ^ 2) ^ (1 / (2 : ℝ)) =
      (eLpNorm f (2 : ℝ≥0∞) volume).toReal := by
  have hraw := Auto.aux_l2Fourier_eq_raw_ae f hf1 hf2
  have hF : MemLp (𝓕 f) (2 : ℝ≥0∞) volume :=
    aux_gowersFourier_memLp_rawFourier_two f hf1 hf2
  have hnorm : eLpNorm (𝓕 f) (2 : ℝ≥0∞) volume =
      eLpNorm f (2 : ℝ≥0∞) volume := by
    rw [eLpNorm_congr_ae (Filter.EventuallyEq.symm hraw)]
    let F := Lp.fourierTransformₗᵢ ℝ ℂ hf2.toLp
    have hFnorm : ‖F‖ = ‖hf2.toLp‖ := Lp.norm_fourier_eq hf2.toLp
    calc
      eLpNorm (⇑F) 2 volume = ‖F‖ₑ := (Lp.enorm_def F).symm
      _ = ‖hf2.toLp‖ₑ := by
        rw [← ofReal_norm, ← ofReal_norm, hFnorm]
      _ = eLpNorm f 2 volume := Lp.enorm_toLp hf2
  calc
    (∫ x : ℝ, ‖𝓕 f x‖ ^ 2) ^ (1 / (2 : ℝ)) =
        (eLpNorm (𝓕 f) (2 : ℝ≥0∞) volume).toReal := by
      rw [toReal_eLpNorm hF.aestronglyMeasurable,
        lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
          hF.aestronglyMeasurable]
      norm_num
    _ = _ := by rw [hnorm]

/-- Sharp `L¹` estimate for the raw Fourier transform of the modulated affine
kernel, now in physical `L²` norms. -/
lemma aux_gowersFourier_integral_norm_fourier_modulatedAffineKernel_le_l2
    (a b s : ℝ) (G H : ℝ → ℂ) (hab : a ≠ b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hG1 : MemLp G (1 : ℝ≥0∞) volume)
    (hH1 : MemLp H (1 : ℝ≥0∞) volume)
    (hG2 : MemLp G (2 : ℝ≥0∞) volume)
    (hH2 : MemLp H (2 : ℝ≥0∞) volume) :
    ∫ ξ : ℝ, ‖𝓕 (aux_gowersFourier_modulatedAffineKernel a b s G H) ξ‖ ≤
      |(a * b)⁻¹| ^ (1 / (2 : ℝ)) *
        (eLpNorm G (2 : ℝ≥0∞) volume).toReal *
          (eLpNorm H (2 : ℝ≥0∞) volume).toReal := by
  have hraw := aux_gowersFourier_integral_norm_fourier_modulatedAffineKernel_le a b s G H hab ha hb
    (memLp_one_iff_integrable.mp hG1) (memLp_one_iff_integrable.mp hH1)
    (aux_gowersFourier_memLp_rawFourier_two G hG1 hG2)
    (aux_gowersFourier_memLp_rawFourier_two H hH1 hH2)
  have hGnorm := aux_gowersFourier_rawFourier_l2_norm_eq G hG1 hG2
  have hHnorm := aux_gowersFourier_rawFourier_l2_norm_eq H hH1 hH2
  have hIG : 0 ≤ ∫ x : ℝ, ‖𝓕 G x‖ ^ 2 := integral_nonneg fun x ↦ sq_nonneg _
  have hIH : 0 ≤ ∫ x : ℝ, ‖𝓕 H x‖ ^ 2 := integral_nonneg fun x ↦ sq_nonneg _
  have hsplit :
      |(b - a)⁻¹| *
          ((|(b / (b - a))⁻¹| * ∫ x : ℝ, ‖𝓕 G x‖ ^ 2) ^ (1 / (2 : ℝ)) *
            (|(-a / (b - a))⁻¹| * ∫ x : ℝ, ‖𝓕 H x‖ ^ 2) ^ (1 / (2 : ℝ))) =
        (|(b - a)⁻¹| *
          (|(b / (b - a))⁻¹| ^ (1 / (2 : ℝ)) *
            |(-a / (b - a))⁻¹| ^ (1 / (2 : ℝ)))) *
          ((∫ x : ℝ, ‖𝓕 G x‖ ^ 2) ^ (1 / (2 : ℝ)) *
            (∫ x : ℝ, ‖𝓕 H x‖ ^ 2) ^ (1 / (2 : ℝ))) := by
    rw [Real.mul_rpow (abs_nonneg _) hIG, Real.mul_rpow (abs_nonneg _) hIH]
    ring
  calc
    ∫ ξ : ℝ, ‖𝓕 (aux_gowersFourier_modulatedAffineKernel a b s G H) ξ‖ ≤
        |(b - a)⁻¹| *
          ((|(b / (b - a))⁻¹| * ∫ x : ℝ, ‖𝓕 G x‖ ^ 2) ^ (1 / (2 : ℝ)) *
            (|(-a / (b - a))⁻¹| * ∫ x : ℝ, ‖𝓕 H x‖ ^ 2) ^ (1 / (2 : ℝ))) := hraw
    _ = (|(b - a)⁻¹| *
          (|(b / (b - a))⁻¹| ^ (1 / (2 : ℝ)) *
            |(-a / (b - a))⁻¹| ^ (1 / (2 : ℝ)))) *
          ((∫ x : ℝ, ‖𝓕 G x‖ ^ 2) ^ (1 / (2 : ℝ)) *
            (∫ x : ℝ, ‖𝓕 H x‖ ^ 2) ^ (1 / (2 : ℝ))) := hsplit
    _ = |(a * b)⁻¹| ^ (1 / (2 : ℝ)) *
          ((∫ x : ℝ, ‖𝓕 G x‖ ^ 2) ^ (1 / (2 : ℝ)) *
            (∫ x : ℝ, ‖𝓕 H x‖ ^ 2) ^ (1 / (2 : ℝ))) := by
      rw [aux_gowersFourier_affine_jacobian_coefficient_sqrt a b hab ha hb]
    _ = _ := by
      rw [hGnorm, hHnorm]
      ring

/-- The measurable Plancherel pairing followed by the elementary
`L^∞`--`L¹` estimate.  Unlike the raw inversion version, this imposes no
continuity condition on the kernel. -/
lemma aux_gowersFourier_norm_integral_mul_le_l2Fourier_pairing
    (f k : ℝ → ℂ)
    (hf1 : MemLp f (1 : ℝ≥0∞) volume) (hf2 : MemLp f (2 : ℝ≥0∞) volume)
    (hk1 : MemLp k (1 : ℝ≥0∞) volume) (hk2 : MemLp k (2 : ℝ≥0∞) volume)
    (hFk : Integrable (𝓕 k) volume) :
    ‖∫ x : ℝ, f x * k x‖ ≤
      (eLpNorm (𝓕 f) ∞ volume).toReal * ∫ ξ : ℝ, ‖𝓕 k ξ‖ := by
  have hlinfty : eLpNorm (𝓕 f) ∞ volume ≤ ENNReal.ofReal (∫ x : ℝ, ‖f x‖) := by
    rw [eLpNorm_exponent_top]
    apply eLpNormEssSup_le_of_ae_enorm_bound
    filter_upwards with ξ
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal
      (VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ) f ξ)
  have htop : eLpNorm (𝓕 f) ∞ volume ≠ ∞ := by
    apply ne_of_lt
    exact lt_of_le_of_lt hlinfty ENNReal.ofReal_lt_top
  have hess : ∀ᵐ ξ : ℝ ∂volume,
      ‖𝓕 f ξ‖ₑ ≤ eLpNorm (𝓕 f) ∞ volume := by
    simpa only [eLpNorm_exponent_top] using
      (MeasureTheory.ae_le_eLpNormEssSup (f := 𝓕 f) (μ := volume))
  have hreflect : ∀ᵐ ξ : ℝ ∂volume,
      ‖𝓕 f (-ξ)‖ₑ ≤ eLpNorm (𝓕 f) ∞ volume := by
    exact (Measure.measurePreserving_neg volume).quasiMeasurePreserving.tendsto_ae hess
  rw [Auto.aux_integral_mul_eq_l2Fourier_pairing f k hf1 hf2 hk1 hk2,
    ← integral_const_mul]
  apply MeasureTheory.norm_integral_le_of_norm_le
    ((hFk.norm).const_mul (eLpNorm (𝓕 f) ∞ volume).toReal)
  filter_upwards [hreflect] with ξ hξ
  rw [norm_mul]
  have hξ' : ENNReal.ofReal ‖𝓕 f (-ξ)‖ ≤ eLpNorm (𝓕 f) ∞ volume := by
    simpa only [ofReal_norm] using hξ
  have hreal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top htop).mpr hξ'
  have hbound : ‖𝓕 f (-ξ)‖ ≤ (eLpNorm (𝓕 f) ∞ volume).toReal := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (norm_nonneg _)] using hreal
  nlinarith [norm_nonneg (𝓕 k ξ)]

/-- The source-Fourier estimate for one fixed modulation: pair the rough
first factor with the affine kernel through Plancherel, then use its factored
raw Fourier transform. -/
lemma aux_gowersFourier_modulatedAffineKernel_pairing_le
    (a b s : ℝ) (f G H : ℝ → ℂ) (hab : a ≠ b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hf1 : MemLp f (1 : ℝ≥0∞) volume) (hf2 : MemLp f (2 : ℝ≥0∞) volume)
    (hG1 : MemLp G (1 : ℝ≥0∞) volume) (hH1 : MemLp H (1 : ℝ≥0∞) volume)
    (hG2 : MemLp G (2 : ℝ≥0∞) volume) (hH2 : MemLp H (2 : ℝ≥0∞) volume) :
    ‖∫ y : ℝ, f y * aux_gowersFourier_modulatedAffineKernel a b s G H y‖ ≤
      (eLpNorm (𝓕 f) ∞ volume).toReal * |(a * b)⁻¹| ^ (1 / (2 : ℝ)) *
        (eLpNorm G (2 : ℝ≥0∞) volume).toReal *
          (eLpNorm H (2 : ℝ≥0∞) volume).toReal := by
  let K := aux_gowersFourier_modulatedAffineKernel a b s G H
  have hK1 : MemLp K (1 : ℝ≥0∞) volume := by
    rw [memLp_one_iff_integrable]
    exact aux_gowersFourier_integrable_modulatedAffineKernel a b s G H hab
      (memLp_one_iff_integrable.mp hG1) (memLp_one_iff_integrable.mp hH1)
  have hK2 : MemLp K (2 : ℝ≥0∞) volume := by
    exact aux_gowersFourier_memLp_modulatedAffineKernel_two a b s G H hab ha hb
      (memLp_one_iff_integrable.mp hG1) (memLp_one_iff_integrable.mp hH1) hG2 hH2
  have hFK : Integrable (𝓕 K) volume := by
    exact aux_gowersFourier_integrable_fourier_modulatedAffineKernel a b s G H hab ha hb
      (memLp_one_iff_integrable.mp hG1) (memLp_one_iff_integrable.mp hH1)
      (aux_gowersFourier_memLp_rawFourier_two G hG1 hG2)
      (aux_gowersFourier_memLp_rawFourier_two H hH1 hH2)
  have hpair := aux_gowersFourier_norm_integral_mul_le_l2Fourier_pairing f K hf1 hf2 hK1 hK2 hFK
  have hkernel := aux_gowersFourier_integral_norm_fourier_modulatedAffineKernel_le_l2
    a b s G H hab ha hb hG1 hH1 hG2 hH2
  calc
    ‖∫ y : ℝ, f y * aux_gowersFourier_modulatedAffineKernel a b s G H y‖ =
        ‖∫ y : ℝ, f y * K y‖ := by rfl
    _ ≤ (eLpNorm (𝓕 f) ∞ volume).toReal * ∫ ξ : ℝ, ‖𝓕 K ξ‖ := hpair
    _ ≤ (eLpNorm (𝓕 f) ∞ volume).toReal *
        (|(a * b)⁻¹| ^ (1 / (2 : ℝ)) *
          (eLpNorm G (2 : ℝ≥0∞) volume).toReal *
            (eLpNorm H (2 : ℝ≥0∞) volume).toReal) :=
      mul_le_mul_of_nonneg_left hkernel ENNReal.toReal_nonneg
    _ = _ := by ring

/-- Fourier inversion of the cutoff, followed by the three-variable Fubini
swap.  The explicit `hR` is the only analytic side condition; the next lemma
derives it from the generic `L¹ ∩ L²` hypotheses. -/
lemma aux_gowersFourier_trilinear_eq_frequency_integral
    (a b : ℝ) (f G H w : ℝ → ℂ)
    (hwc : Continuous w) (hw : Integrable w volume)
    (hFw : Integrable (𝓕 w) volume)
    (hR : Integrable
      (fun p : (ℝ × ℝ) × ℝ ↦
        (𝓕 w p.2) *
          (f p.1.1 * G (p.1.1 + a * p.1.2) * H (p.1.1 + b * p.1.2) *
            (𝐞 (p.2 * p.1.2) : ℂ)))
      ((volume.prod volume).prod volume)) :
    (∫ y : ℝ, ∫ t : ℝ,
      f y * G (y + a * t) * H (y + b * t) * w t) =
      ∫ s : ℝ, (𝓕 w s) *
        (∫ y : ℝ, f y * aux_gowersFourier_modulatedAffineKernel a b s G H y) := by
  have hinv : 𝓕⁻ (𝓕 w) = w :=
    Continuous.fourierInv_fourier_eq hwc hw hFw
  let R : ℝ → ℝ → ℝ → ℂ := fun y t s ↦
    (𝓕 w s) *
      (f y * G (y + a * t) * H (y + b * t) * (𝐞 (s * t) : ℂ))
  have hR' : Integrable
      (fun p : (ℝ × ℝ) × ℝ ↦ R p.1.1 p.1.2 p.2)
      ((volume.prod volume).prod volume) := by
    exact hR
  calc
    (∫ y : ℝ, ∫ t : ℝ,
      f y * G (y + a * t) * H (y + b * t) * w t) =
        ∫ y : ℝ, ∫ t : ℝ,
          f y * G (y + a * t) * H (y + b * t) * (𝓕⁻ (𝓕 w)) t := by
      rw [hinv]
    _ = ∫ y : ℝ, ∫ t : ℝ, ∫ s : ℝ, R y t s := by
      apply integral_congr_ae
      filter_upwards with y
      apply integral_congr_ae
      filter_upwards with t
      rw [Real.fourierInv_eq, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with s
      rw [Circle.smul_def, Real.inner_apply]
      dsimp [R]
      ring
    _ = ∫ s : ℝ, ∫ y : ℝ, ∫ t : ℝ, R y t s :=
      Auto.aux_triple_integral_swap R hR'
    _ = ∫ s : ℝ, ∫ y : ℝ, (𝓕 w s) *
        (f y * aux_gowersFourier_modulatedAffineKernel a b s G H y) := by
      apply integral_congr_ae
      filter_upwards with s
      apply integral_congr_ae
      filter_upwards with y
      rw [aux_gowersFourier_modulatedAffineKernel]
      rw [show (𝓕 w s) * (f y *
          ∫ t : ℝ, G (y + a * t) * H (y + b * t) * (𝐞 (s * t) : ℂ)) =
          ((𝓕 w s) * f y) *
            ∫ t : ℝ, G (y + a * t) * H (y + b * t) * (𝐞 (s * t) : ℂ) by ring]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      dsimp [R]
      ring
    _ = ∫ s : ℝ, (𝓕 w s) *
        (∫ y : ℝ, f y * aux_gowersFourier_modulatedAffineKernel a b s G H y) := by
      apply integral_congr_ae
      filter_upwards with s
      rw [integral_const_mul]

/-- Uniform-in-modulation joint integrability of the two affine `L²` factors
after multiplying by an `L¹` factor in the physical variable. -/
lemma aux_gowersFourier_integrable_weighted_modulatedAffineJoint
    (a b s : ℝ) (f G H : ℝ → ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hf : Integrable f volume)
    (hG : MemLp G (2 : ℝ≥0∞) volume)
    (hH : MemLp H (2 : ℝ≥0∞) volume) :
    Integrable
      (fun z : ℝ × ℝ ↦
        f z.1 * (G (z.1 + a * z.2) * H (z.1 + b * z.2) *
          (𝐞 (s * z.2) : ℂ)))
      (volume.prod volume) := by
  let B : ℝ → ℝ → ℂ := fun y t ↦
    G (y + a * t) * H (y + b * t) * (𝐞 (s * t) : ℂ)
  have hBmeas : AEStronglyMeasurable (Function.uncurry B) (volume.prod volume) := by
    change AEStronglyMeasurable
      (fun z : ℝ × ℝ ↦ G (z.1 + a * z.2) * H (z.1 + b * z.2) *
        (𝐞 (s * z.2) : ℂ)) (volume.prod volume)
    have hGa := Auto.aux_aestronglyMeasurable_comp_affine G hG.aestronglyMeasurable a
    have hHb := Auto.aux_aestronglyMeasurable_comp_affine H hH.aestronglyMeasurable b
    have hphase : AEStronglyMeasurable
        (fun z : ℝ × ℝ ↦ (𝐞 (s * z.2) : ℂ)) (volume.prod volume) :=
      (continuous_subtype_val.comp
        (Real.continuous_fourierChar.comp (by fun_prop))).aestronglyMeasurable
    exact (hGa.mul hHb).mul hphase
  have hBint : ∀ y : ℝ, Integrable (B y) volume := by
    intro y
    have hGa : MemLp (fun t : ℝ ↦ G (a * t + y)) (2 : ℝ≥0∞) volume :=
      aux_gowersFourier_memLp_comp_affine G 2 hG a y ha
    have hHb : MemLp (fun t : ℝ ↦ H (b * t + y)) (2 : ℝ≥0∞) volume :=
      aux_gowersFourier_memLp_comp_affine H 2 hH b y hb
    have hprod : MemLp (fun t : ℝ ↦ G (a * t + y) * H (b * t + y))
        (1 : ℝ≥0∞) volume := hHb.mul hGa
    have hprodint : Integrable (fun t : ℝ ↦ G (a * t + y) * H (b * t + y)) volume :=
      memLp_one_iff_integrable.mp hprod
    have hphase : AEStronglyMeasurable (fun t : ℝ ↦ (𝐞 (s * t) : ℂ)) volume :=
      (continuous_subtype_val.comp
        (Real.continuous_fourierChar.comp (by fun_prop))).aestronglyMeasurable
    have hmod := hprodint.bdd_mul (c := 1) hphase
      (Filter.Eventually.of_forall fun t ↦ by simp)
    convert hmod using 1
    funext t
    dsimp [B]
    rw [add_comm y (a * t), add_comm y (b * t)]
    ring
  let C : ℝ :=
    (|a⁻¹| * ∫ z : ℝ, ‖G z‖ ^ 2) ^ (1 / (2 : ℝ)) *
      (|b⁻¹| * ∫ z : ℝ, ‖H z‖ ^ 2) ^ (1 / (2 : ℝ))
  have hBbound : ∀ y : ℝ, ∫ t : ℝ, ‖B y t‖ ≤ C := by
    intro y
    dsimp [B, C]
    calc
      ∫ t : ℝ, ‖G (y + a * t) * H (y + b * t) * (𝐞 (s * t) : ℂ)‖ =
          ∫ t : ℝ, ‖G (a * t + y)‖ * ‖H (b * t + y)‖ := by
        apply integral_congr_ae
        filter_upwards with t
        rw [norm_mul, norm_mul, add_comm y (a * t), add_comm y (b * t)]
        simp
      _ ≤ _ := aux_gowersFourier_integral_norm_mul_comp_affine_le_scaled G H hG hH
        a b y y ha hb
  apply aux_gowersFourier_integrable_weighted_bilinear_of_section_bound
    f hf B hBmeas hBint C hBbound

/-- The uniform `L¹` bound for the preceding joint integrand. -/
lemma aux_gowersFourier_integral_norm_weighted_modulatedAffineJoint_le
    (a b s : ℝ) (f G H : ℝ → ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hf : Integrable f volume)
    (hG : MemLp G (2 : ℝ≥0∞) volume)
    (hH : MemLp H (2 : ℝ≥0∞) volume) :
    ∫ z : ℝ × ℝ,
      ‖f z.1 * (G (z.1 + a * z.2) * H (z.1 + b * z.2) *
        (𝐞 (s * z.2) : ℂ))‖ ≤
      (∫ y : ℝ, ‖f y‖) *
        ((|a⁻¹| * ∫ z : ℝ, ‖G z‖ ^ 2) ^ (1 / (2 : ℝ)) *
          (|b⁻¹| * ∫ z : ℝ, ‖H z‖ ^ 2) ^ (1 / (2 : ℝ))) := by
  let Q : ℝ × ℝ → ℂ := fun z ↦
    f z.1 * (G (z.1 + a * z.2) * H (z.1 + b * z.2) *
      (𝐞 (s * z.2) : ℂ))
  let B : ℝ → ℝ → ℂ := fun y t ↦
    G (y + a * t) * H (y + b * t) * (𝐞 (s * t) : ℂ)
  let C : ℝ :=
    (|a⁻¹| * ∫ z : ℝ, ‖G z‖ ^ 2) ^ (1 / (2 : ℝ)) *
      (|b⁻¹| * ∫ z : ℝ, ‖H z‖ ^ 2) ^ (1 / (2 : ℝ))
  have hQ : Integrable Q (volume.prod volume) :=
    aux_gowersFourier_integrable_weighted_modulatedAffineJoint a b s f G H ha hb hf hG hH
  have hBbound : ∀ y : ℝ, ∫ t : ℝ, ‖B y t‖ ≤ C := by
    intro y
    dsimp [B, C]
    calc
      ∫ t : ℝ, ‖G (y + a * t) * H (y + b * t) * (𝐞 (s * t) : ℂ)‖ =
          ∫ t : ℝ, ‖G (a * t + y)‖ * ‖H (b * t + y)‖ := by
        apply integral_congr_ae
        filter_upwards with t
        rw [norm_mul, norm_mul, add_comm y (a * t), add_comm y (b * t)]
        simp
      _ ≤ _ := aux_gowersFourier_integral_norm_mul_comp_affine_le_scaled G H hG hH
        a b y y ha hb
  have hright : Integrable (fun y : ℝ ↦ ‖f y‖ * C) volume := hf.norm.mul_const C
  change ∫ z : ℝ × ℝ, ‖Q z‖ ≤ (∫ y : ℝ, ‖f y‖) * C
  calc
    ∫ z : ℝ × ℝ, ‖Q z‖ = ∫ y : ℝ, ∫ t : ℝ, ‖Q (y, t)‖ :=
      integral_prod _ hQ.norm
    _ = ∫ y : ℝ, ‖f y‖ * ∫ t : ℝ, ‖B y t‖ := by
      apply integral_congr_ae
      filter_upwards with y
      have hinner : (fun t : ℝ ↦ ‖Q (y, t)‖) =
          fun t ↦ ‖f y‖ * ‖B y t‖ := by
        funext t
        dsimp [Q, B]
        rw [norm_mul]
      rw [hinner, integral_const_mul]
    _ ≤ ∫ y : ℝ, ‖f y‖ * C := by
      have hnonneg :
          ∀ᵐ y : ℝ ∂volume, 0 ≤ ‖f y‖ * ∫ t : ℝ, ‖B y t‖ := by
        exact Filter.Eventually.of_forall fun y ↦
          mul_nonneg (norm_nonneg _) (integral_nonneg fun t ↦ norm_nonneg _)
      have hle :
          ∀ᵐ y : ℝ ∂volume,
            ‖f y‖ * ∫ t : ℝ, ‖B y t‖ ≤ ‖f y‖ * C := by
        exact Filter.Eventually.of_forall fun y ↦
          mul_le_mul_of_nonneg_left (hBbound y) (norm_nonneg _)
      exact integral_mono_of_nonneg hnonneg hright hle
    _ = _ := integral_mul_const C (fun y : ℝ ↦ ‖f y‖)

/-- The full Fubini condition for cutoff inversion follows from `L¹` for the
Fourier cutoff and `L¹ × L² × L²` for the three physical factors. -/
lemma aux_gowersFourier_integrable_frequency_trilinear_joint
    (a b : ℝ) (f G H w : ℝ → ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hf : Integrable f volume)
    (hG : MemLp G (2 : ℝ≥0∞) volume)
    (hH : MemLp H (2 : ℝ≥0∞) volume)
    (hFw : Integrable (𝓕 w) volume) :
    Integrable
      (fun p : (ℝ × ℝ) × ℝ ↦
        (𝓕 w p.2) *
          (f p.1.1 * G (p.1.1 + a * p.1.2) * H (p.1.1 + b * p.1.2) *
            (𝐞 (p.2 * p.1.2) : ℂ)))
      ((volume.prod volume).prod volume) := by
  have hYpair : Measure.QuasiMeasurePreserving (fun z : ℝ × ℝ ↦ z.1)
      (volume.prod volume) volume := by
    simpa using (Auto.aux_quasiMeasurePreserving_affine (0 : ℝ))
  have hY : Measure.QuasiMeasurePreserving (fun p : (ℝ × ℝ) × ℝ ↦ p.1.1)
      ((volume.prod volume).prod volume) volume := by
    apply QuasiMeasurePreserving.prod_of_left (by fun_prop)
    filter_upwards with s
    exact hYpair
  have hA : Measure.QuasiMeasurePreserving
      (fun p : (ℝ × ℝ) × ℝ ↦ p.1.1 + a * p.1.2)
      ((volume.prod volume).prod volume) volume := by
    apply QuasiMeasurePreserving.prod_of_left (by fun_prop)
    filter_upwards with s
    exact Auto.aux_quasiMeasurePreserving_affine a
  have hB : Measure.QuasiMeasurePreserving
      (fun p : (ℝ × ℝ) × ℝ ↦ p.1.1 + b * p.1.2)
      ((volume.prod volume).prod volume) volume := by
    apply QuasiMeasurePreserving.prod_of_left (by fun_prop)
    filter_upwards with s
    exact Auto.aux_quasiMeasurePreserving_affine b
  have hS : Measure.QuasiMeasurePreserving (fun p : (ℝ × ℝ) × ℝ ↦ p.2)
      ((volume.prod volume).prod volume) volume := by
    apply QuasiMeasurePreserving.prod_of_right (by fun_prop)
    filter_upwards with z
    convert (MeasurePreserving.id volume).quasiMeasurePreserving using 1 ; rfl
  have hphase : AEStronglyMeasurable
      (fun p : (ℝ × ℝ) × ℝ ↦ (𝐞 (p.2 * p.1.2) : ℂ))
      ((volume.prod volume).prod volume) :=
    (continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (by fun_prop))).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun p : (ℝ × ℝ) × ℝ ↦
        (𝓕 w p.2) *
          (f p.1.1 * G (p.1.1 + a * p.1.2) * H (p.1.1 + b * p.1.2) *
            (𝐞 (p.2 * p.1.2) : ℂ)))
      ((volume.prod volume).prod volume) := by
    exact (hFw.aestronglyMeasurable.comp_quasiMeasurePreserving hS).mul
      (((hf.aestronglyMeasurable.comp_quasiMeasurePreserving hY).mul
        (hG.aestronglyMeasurable.comp_quasiMeasurePreserving hA)).mul
          (hH.aestronglyMeasurable.comp_quasiMeasurePreserving hB) |>.mul hphase)
  apply (integrable_prod_iff' hmeas).mpr
  refine ⟨Filter.Eventually.of_forall fun s ↦ ?_, ?_⟩
  · have hQ := aux_gowersFourier_integrable_weighted_modulatedAffineJoint
      a b s f G H ha hb hf hG hH
    convert hQ.const_mul (𝓕 w s) using 1
    funext z
    ring
  · let D : ℝ := (∫ y : ℝ, ‖f y‖) *
      ((|a⁻¹| * ∫ z : ℝ, ‖G z‖ ^ 2) ^ (1 / (2 : ℝ)) *
        (|b⁻¹| * ∫ z : ℝ, ‖H z‖ ^ 2) ^ (1 / (2 : ℝ)))
    apply Integrable.mono' (hFw.norm.mul_const D)
      hmeas.prod_swap.norm.integral_prod_right'
    filter_upwards with s
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun z ↦ norm_nonneg _)]
    calc
      ∫ z : ℝ × ℝ,
          ‖(𝓕 w s) *
            (f z.1 * G (z.1 + a * z.2) * H (z.1 + b * z.2) *
              (𝐞 (s * z.2) : ℂ))‖ =
          ‖𝓕 w s‖ * ∫ z : ℝ × ℝ,
            ‖f z.1 * (G (z.1 + a * z.2) * H (z.1 + b * z.2) *
              (𝐞 (s * z.2) : ℂ))‖ := by
        rw [show (fun z : ℝ × ℝ ↦ ‖(𝓕 w s) *
            (f z.1 * G (z.1 + a * z.2) * H (z.1 + b * z.2) *
              (𝐞 (s * z.2) : ℂ))‖) =
            fun z ↦ ‖𝓕 w s‖ * ‖f z.1 *
              (G (z.1 + a * z.2) * H (z.1 + b * z.2) *
                (𝐞 (s * z.2) : ℂ))‖ by
          funext z
          rw [norm_mul]
          ring_nf]
        rw [integral_const_mul]
      _ ≤ ‖𝓕 w s‖ * D := by
        apply mul_le_mul_of_nonneg_left
          (aux_gowersFourier_integral_norm_weighted_modulatedAffineJoint_le
            a b s f G H ha hb hf hG hH)
          (norm_nonneg _)

/-- Generic source-Fourier trilinear estimate.  Fourier inversion of `w`,
Fubini, the measurable Plancherel pairing, and the affine Fourier factorization
are all internal to this statement. -/
lemma aux_gowersFourier_trilinear_fourier_bound
    (a b : ℝ) (f G H w : ℝ → ℂ) (hab : a ≠ b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hf1 : MemLp f (1 : ℝ≥0∞) volume) (hf2 : MemLp f (2 : ℝ≥0∞) volume)
    (hG1 : MemLp G (1 : ℝ≥0∞) volume) (hH1 : MemLp H (1 : ℝ≥0∞) volume)
    (hG2 : MemLp G (2 : ℝ≥0∞) volume) (hH2 : MemLp H (2 : ℝ≥0∞) volume)
    (hwc : Continuous w) (hw : Integrable w volume)
    (hFw : Integrable (𝓕 w) volume) :
    ‖∫ y : ℝ, ∫ t : ℝ,
      f y * G (y + a * t) * H (y + b * t) * w t‖ ≤
      (eLpNorm (𝓕 f) ∞ volume).toReal *
        (∫ s : ℝ, ‖𝓕 w s‖) * |(a * b)⁻¹| ^ (1 / (2 : ℝ)) *
          (eLpNorm G (2 : ℝ≥0∞) volume).toReal *
            (eLpNorm H (2 : ℝ≥0∞) volume).toReal := by
  let C : ℝ := (eLpNorm (𝓕 f) ∞ volume).toReal *
    |(a * b)⁻¹| ^ (1 / (2 : ℝ)) *
      (eLpNorm G (2 : ℝ≥0∞) volume).toReal *
        (eLpNorm H (2 : ℝ≥0∞) volume).toReal
  have hR := aux_gowersFourier_integrable_frequency_trilinear_joint a b f G H w ha hb
    (memLp_one_iff_integrable.mp hf1) hG2 hH2 hFw
  have hident := aux_gowersFourier_trilinear_eq_frequency_integral a b f G H w hwc hw hFw hR
  calc
    ‖∫ y : ℝ, ∫ t : ℝ,
        f y * G (y + a * t) * H (y + b * t) * w t‖ =
        ‖∫ s : ℝ, (𝓕 w s) *
          (∫ y : ℝ, f y * aux_gowersFourier_modulatedAffineKernel a b s G H y)‖ := by
      rw [hident]
    _ ≤ ∫ s : ℝ, ‖𝓕 w s‖ * C := by
      apply MeasureTheory.norm_integral_le_of_norm_le (hFw.norm.mul_const C)
      filter_upwards with s
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (aux_gowersFourier_modulatedAffineKernel_pairing_le a b s f G H hab ha hb
          hf1 hf2 hG1 hH1 hG2 hH2)
        (norm_nonneg _)
    _ = (∫ s : ℝ, ‖𝓕 w s‖) * C :=
      integral_mul_const C (fun s : ℝ ↦ ‖𝓕 w s‖)
    _ = _ := by
      dsimp [C]
      ring

/-- `aux_gowersFourier_trilinear_fourier_bound` in the exact `eLpNorm` form convenient for
composition with a Fourier cutoff estimate. -/
lemma aux_gowersFourier_trilinear_fourier_bound_eLpNorm
    (a b : ℝ) (f G H w : ℝ → ℂ) (hab : a ≠ b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hf1 : MemLp f (1 : ℝ≥0∞) volume) (hf2 : MemLp f (2 : ℝ≥0∞) volume)
    (hG1 : MemLp G (1 : ℝ≥0∞) volume) (hH1 : MemLp H (1 : ℝ≥0∞) volume)
    (hG2 : MemLp G (2 : ℝ≥0∞) volume) (hH2 : MemLp H (2 : ℝ≥0∞) volume)
    (hwc : Continuous w) (hw : Integrable w volume)
    (hFw1 : MemLp (𝓕 w) (1 : ℝ≥0∞) volume) :
    ‖∫ y : ℝ, ∫ t : ℝ,
      f y * G (y + a * t) * H (y + b * t) * w t‖ ≤
      (eLpNorm (𝓕 f) ∞ volume).toReal *
        (eLpNorm (𝓕 w) (1 : ℝ≥0∞) volume).toReal *
          |(a * b)⁻¹| ^ (1 / (2 : ℝ)) *
            (eLpNorm G (2 : ℝ≥0∞) volume).toReal *
              (eLpNorm H (2 : ℝ≥0∞) volume).toReal := by
  have hFw : Integrable (𝓕 w) volume := memLp_one_iff_integrable.mp hFw1
  have hraw := aux_gowersFourier_trilinear_fourier_bound a b f G H w hab ha hb
    hf1 hf2 hG1 hH1 hG2 hH2 hwc hw hFw
  have hFwNorm : (∫ s : ℝ, ‖𝓕 w s‖) =
      (eLpNorm (𝓕 w) (1 : ℝ≥0∞) volume).toReal := by
    rw [toReal_eLpNorm hFw1.aestronglyMeasurable,
      lpNorm_one_eq_integral_norm hFw1.aestronglyMeasurable]
  calc
    ‖∫ y : ℝ, ∫ t : ℝ,
        f y * G (y + a * t) * H (y + b * t) * w t‖ ≤
        (eLpNorm (𝓕 f) ∞ volume).toReal *
          (∫ s : ℝ, ‖𝓕 w s‖) * |(a * b)⁻¹| ^ (1 / (2 : ℝ)) *
            (eLpNorm G (2 : ℝ≥0∞) volume).toReal *
              (eLpNorm H (2 : ℝ≥0∞) volume).toReal := hraw
    _ = _ := by rw [hFwNorm]

/-- The dilation direction needed after introducing the normalized difference
parameter: an unscaled nonnegative integral is controlled by the integral in
the `c⁻¹`-rescaled parameter. -/
lemma aux_gowers_lintegral_ofReal_rescale_le
    (d : ℝ → ℝ) (c : ℝ) (hc : c ≠ 0) :
    ∫⁻ r : ℝ, ENNReal.ofReal (d r) ≤
      ENNReal.ofReal |c⁻¹| *
        ∫⁻ h : ℝ, ENNReal.ofReal (d (c⁻¹ * h)) := by
  have h := aux_lintegral_comp_mul_le
    (fun h : ℝ ↦ ENNReal.ofReal (d (c⁻¹ * h))) c hc
  calc
    ∫⁻ r : ℝ, ENNReal.ofReal (d r) =
        ∫⁻ r : ℝ, (fun h : ℝ ↦ ENNReal.ofReal (d (c⁻¹ * h))) (c * r) := by
      apply MeasureTheory.lintegral_congr
      intro r
      congr 2
      field_simp
    _ ≤ ENNReal.ofReal |c⁻¹| *
        ∫⁻ h : ℝ, (fun h : ℝ ↦ ENNReal.ofReal (d (c⁻¹ * h))) h := h
    _ = ENNReal.ofReal |c⁻¹| *
        ∫⁻ h : ℝ, ENNReal.ofReal (d (c⁻¹ * h)) := rfl

/-- The real autocorrelation-energy estimate, a normalized-difference
pointwise estimate, and dilation combine directly into a squared ENNReal
bound.  This is the final measure-theoretic bridge before the `uNorm³`
identity. -/
lemma aux_gowers_ennreal_sq_of_real_energy_bound_rescaled
    (T : ℂ) (B : ℝ) (d : ℝ → ℝ) (E : ℝ → ℝ≥0∞) (K c : ℝ)
    (hB : 0 ≤ B) (hd_int : Integrable d volume)
    (hd_nonneg : ∀ᵐ h : ℝ ∂volume, 0 ≤ d h)
    (hc : c ≠ 0)
    (henergy : ‖T‖ ^ (2 : ℕ) ≤ B * ∫ h : ℝ, d h)
    (hpoint : ∀ᵐ h : ℝ ∂volume,
      ENNReal.ofReal (d (c⁻¹ * h)) ≤ ENNReal.ofReal K * E h) :
    (ENNReal.ofReal ‖T‖) ^ (2 : ℕ) ≤
      ENNReal.ofReal B * ENNReal.ofReal |c⁻¹| * ENNReal.ofReal K *
        ∫⁻ h : ℝ, E h := by
  calc
    (ENNReal.ofReal ‖T‖) ^ (2 : ℕ) = ENNReal.ofReal (‖T‖ ^ (2 : ℕ)) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _) 2]
    _ ≤ ENNReal.ofReal (B * ∫ h : ℝ, d h) := ENNReal.ofReal_le_ofReal henergy
    _ = ENNReal.ofReal B * ENNReal.ofReal (∫ h : ℝ, d h) := by
      rw [ENNReal.ofReal_mul hB]
    _ = ENNReal.ofReal B * ∫⁻ h : ℝ, ENNReal.ofReal (d h) := by
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hd_int hd_nonneg]
    _ ≤ ENNReal.ofReal B *
        (ENNReal.ofReal |c⁻¹| * ∫⁻ h : ℝ, ENNReal.ofReal (d (c⁻¹ * h))) := by
      exact mul_le_mul_of_nonneg_left
        (aux_gowers_lintegral_ofReal_rescale_le d c hc) bot_le
    _ ≤ ENNReal.ofReal B *
        (ENNReal.ofReal |c⁻¹| *
          (ENNReal.ofReal K * ∫⁻ h : ℝ, E h)) := by
      apply mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ?_ bot_le) bot_le
      calc
        ∫⁻ h : ℝ, ENNReal.ofReal (d (c⁻¹ * h)) ≤
            ∫⁻ h : ℝ, ENNReal.ofReal K * E h :=
          MeasureTheory.lintegral_mono_ae hpoint
        _ = ENNReal.ofReal K * ∫⁻ h : ℝ, E h := by
          rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal B * ENNReal.ofReal |c⁻¹| * ENNReal.ofReal K *
        ∫⁻ h : ℝ, E h := by ring

/-- Compact autocorrelation integrability also gives integrability of the
real-valued absolute correlation as a function of the difference parameter.
This supplies the `Integrable d` premise in the ENNReal bridge. -/
lemma aux_gowers_autocorrelation_norm_integrable
    (Q : ℝ → ℝ → ℂ)
    (hR : Integrable
      (Function.uncurry fun p : ℝ × ℝ ↦ fun t : ℝ ↦
        Q p.1 t * starRingEnd ℂ (Q p.1 (t + p.2)))
      ((volume.prod volume).prod volume)) :
    Integrable (fun h : ℝ ↦ ‖∫ x : ℝ, ∫ t : ℝ,
      Q x t * starRingEnd ℂ (Q x (t + h))‖) volume := by
  have hR' : Integrable
      (Function.uncurry fun (h : ℝ) (z : ℝ × ℝ) ↦
        Q z.1 z.2 * starRingEnd ℂ (Q z.1 (z.2 + h)))
      (volume.prod (volume.prod volume)) := by
    change Integrable
      ((Function.uncurry fun p : ℝ × ℝ ↦ fun t : ℝ ↦
        Q p.1 t * starRingEnd ℂ (Q p.1 (t + p.2))) ∘
          fun z : ℝ × (ℝ × ℝ) ↦ ((z.2.1, z.1), z.2.2))
      (volume.prod (volume.prod volume))
    rw [← memLp_one_iff_integrable] at hR ⊢
    exact hR.comp_measurePreserving
      aux_measurePreserving_autocorrelation_reorder_symm
  have hsections : ∀ᵐ h : ℝ ∂volume, Integrable
      (Function.uncurry fun x t : ℝ ↦
        Q x t * starRingEnd ℂ (Q x (t + h)))
      (volume.prod volume) := hR'.prod_right_ae
  have hinner : Integrable (fun h : ℝ ↦ ∫ z : ℝ × ℝ,
      Q z.1 z.2 * starRingEnd ℂ (Q z.1 (z.2 + h))) volume :=
    hR'.integral_prod_left
  apply hinner.norm.congr
  filter_upwards [hsections] with h hh
  apply congrArg norm
  let F : ℝ → ℝ → ℂ := fun x t ↦
    Q x t * starRingEnd ℂ (Q x (t + h))
  calc
    ∫ z : ℝ × ℝ, Q z.1 z.2 * starRingEnd ℂ (Q z.1 (z.2 + h)) =
        ∫ t : ℝ, ∫ x : ℝ, F x t := by
      convert integral_prod_symm (Function.uncurry F) hh using 1 <;> rfl
    _ = ∫ x : ℝ, ∫ t : ℝ, F x t := (integral_integral_swap hh).symm
    _ = ∫ x : ℝ, ∫ t : ℝ,
        Q x t * starRingEnd ℂ (Q x (t + h)) := by rfl

/-- Direct version of the extended-real bridge for the compact Gowers
kernel, ending in the squared real-parameter form of `uNorm 3`. -/
lemma aux_gowers_autocorrelation_to_uNorm_sq
    (T : ℂ) (Q : ℝ → ℝ → ℂ) (f : ℝ → ℂ) (B K c : ℝ)
    (hB : 0 ≤ B) (hc : c ≠ 0)
    (hR : Integrable
      (Function.uncurry fun p : ℝ × ℝ ↦ fun t : ℝ ↦
        Q p.1 t * starRingEnd ℂ (Q p.1 (t + p.2)))
      ((volume.prod volume).prod volume))
    (henergy : ‖T‖ ^ (2 : ℕ) ≤ B * ∫ h : ℝ, ‖∫ x : ℝ, ∫ t : ℝ,
      Q x t * starRingEnd ℂ (Q x (t + h))‖)
    (hpoint : ∀ᵐ h : ℝ ∂volume,
      ENNReal.ofReal ‖∫ x : ℝ, ∫ t : ℝ,
        Q x t * starRingEnd ℂ (Q x (t + c⁻¹ * h))‖ ≤
        ENNReal.ofReal K *
          eLpNorm (𝓕 (multiplicativeDifference h f)) ∞ volume) :
    (ENNReal.ofReal ‖T‖) ^ (2 : ℕ) ≤
      ENNReal.ofReal B * ENNReal.ofReal |c⁻¹| * ENNReal.ofReal K *
        (uNorm 3 f) ^ (2 : ℝ) := by
  let d : ℝ → ℝ := fun h ↦ ‖∫ x : ℝ, ∫ t : ℝ,
    Q x t * starRingEnd ℂ (Q x (t + h))‖
  have hd_int : Integrable d volume := by
    simpa only [d] using aux_gowers_autocorrelation_norm_integrable Q hR
  have hd_nonneg : ∀ᵐ h : ℝ ∂volume, 0 ≤ d h := by
    filter_upwards with h
    exact norm_nonneg _
  have hsq := aux_gowers_ennreal_sq_of_real_energy_bound_rescaled
    T B d (fun h : ℝ ↦ eLpNorm (𝓕 (multiplicativeDifference h f)) ∞ volume)
    K c hB hd_int hd_nonneg hc (by simpa only [d] using henergy) (by
      simpa only [d] using hpoint)
  rw [← aux_uNorm_three_sq_real_parameter f] at hsq
  exact hsq

/-- A squared ENNReal bound gives the corresponding unsquared bound. -/
lemma aux_gowers_ennreal_le_of_sq_le
    (x y : ℝ≥0∞) (h : x ^ (2 : ℕ) ≤ y ^ (2 : ℕ)) : x ≤ y := by
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  rw [show x ^ (2 : ℝ) = x ^ (2 : ℕ) by
    exact ENNReal.rpow_natCast x 2,
    show y ^ (2 : ℝ) = y ^ (2 : ℕ) by
      exact ENNReal.rpow_natCast y 2]
  exact h

open scoped LineDeriv

/-- The `H¹` argument underlying `aux_fourierL1LeFromWeakDerivative` also
gives `L¹` membership of the Plancherel Fourier representative.  This is the
membership form needed for the cutoff inversion step in `gowersDifferencing`. -/
lemma aux_gowersFourier_memLp_l2Fourier_one_of_weakDerivative
    (g dg : Lp (α := ℝ) ℂ 2 volume)
    (hdg : ∂_{(1 : ℝ)} (Lp.toTemperedDistribution g) = Lp.toTemperedDistribution dg) :
    MemLp (fun ξ : ℝ ↦ (Lp.fourierTransformₗᵢ ℝ ℂ g) ξ)
      (1 : ℝ≥0∞) volume := by
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
  have hw : MemLp w 2 volume := by
    simpa [w, S] using aux_tailReciprocalComplexMemLp
  have hT : MemLp T 2 volume := by
    have hTc : MemLp (c • (fun x : ℝ ↦ G x)) 2 volume := hG.const_smul c
    convert hTc using 1
    ext x
    simp [T, smul_eq_mul]
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
  have hsum : S.indicator (fun x : ℝ ↦ F x) + Sᶜ.indicator (fun x : ℝ ↦ F x) =
      fun x ↦ F x := by
    funext x
    simp
  rw [← hsum]
  exact hsmall.add htail

/-- Transfer the preceding `L¹` membership from the `L²` Fourier
representative to the raw Fourier integral. -/
lemma aux_gowersFourier_memLp_rawFourier_one_of_weakDerivative
    (f df : ℝ → ℂ) (hf1 : MemLp f (1 : ℝ≥0∞) volume)
    (hf2 : MemLp f (2 : ℝ≥0∞) volume) (hdf2 : MemLp df (2 : ℝ≥0∞) volume)
    (hweak : ∂_{(1 : ℝ)} (Lp.toTemperedDistribution hf2.toLp) =
      Lp.toTemperedDistribution hdf2.toLp) :
    MemLp (𝓕 f) (1 : ℝ≥0∞) volume := by
  have hl2 := aux_gowersFourier_memLp_l2Fourier_one_of_weakDerivative
    (hf2.toLp f) (hdf2.toLp df) hweak
  have hraw := aux_l2Fourier_eq_raw_ae f hf1 hf2
  exact (memLp_congr_ae (Filter.EventuallyEq.symm hraw)).mpr hl2

/-- The raw Fourier transform of every translated product cutoff is in
`L¹`.  This packages the membership prerequisite for the Fourier inversion
argument in `gowersDifferencing`. -/
lemma aux_gowersFourier_productCutoff_memLp_rawFourier_one
    (ψ : ℝ → ℝ) (hψ_smooth : ContDiff ℝ 1 ψ) (hψ_compact : HasCompactSupport ψ)
    (u : ℝ) :
    MemLp (𝓕 (fun t : ℝ ↦ ((ψ t * ψ (t + u) : ℝ) : ℂ)))
      (1 : ℝ≥0∞) volume := by
  let f : ℝ → ℂ := fun t ↦ ((ψ t * ψ (t + u) : ℝ) : ℂ)
  let df : ℝ → ℂ := fun t ↦
    ((deriv ψ t * ψ (t + u) + ψ t * deriv ψ (t + u) : ℝ) : ℂ)
  have hfs : ContDiff ℝ 1 f := by
    change ContDiff ℝ 1 (Complex.ofRealCLM ∘ fun t : ℝ ↦ ψ t * ψ (t + u))
    exact Complex.ofRealCLM.contDiff.comp (aux_productCutoffSmooth ψ hψ_smooth u)
  have hfc : HasCompactSupport f := by
    change HasCompactSupport (Complex.ofRealCLM ∘ fun t : ℝ ↦ ψ t * ψ (t + u))
    exact (aux_productCutoffCompact ψ hψ_compact u).comp_left rfl
  have hf1 : MemLp f (1 : ℝ≥0∞) volume :=
    aux_productCutoffMemLpOne ψ hψ_smooth hψ_compact u
  have hf2 : MemLp f (2 : ℝ≥0∞) volume :=
    aux_productCutoffMemLpTwo ψ hψ_smooth hψ_compact u
  have hdf2 : MemLp df (2 : ℝ≥0∞) volume :=
    aux_productCutoffDerivativeMemLpTwo ψ hψ_smooth hψ_compact u
  have hdf : ∀ x : ℝ, deriv f x = df x := by
    intro x
    exact aux_productCutoffDerivativeComplexFormula ψ hψ_smooth u x
  have hweak := aux_weakDerivativeOfContDiffCompact f df hfs hfc hf2 hdf hdf2
  have hraw := aux_gowersFourier_memLp_rawFourier_one_of_weakDerivative
    f df hf1 hf2 hdf2 hweak
  simpa only [f] using hraw

/-- The cutoff Fourier constant is at most twice the two-interval size
parameter.  This is the final cutoff-constant bookkeeping needed by
`gowersDifferencing` for `\label{prop:gowers-differencing}`. -/
lemma aux_gowers_productCutoffConstant_le_two_mul_sizeParameter
    (A J : Set ℝ) (ψ : ℝ → ℝ) :
    C_productCutoffFourierBounds ψ ≤ 2 * sizeParameter ![A, J] ψ := by
  let S : ℝ := sizeParameter ![A, J] ψ
  have hS_L2 : (eLpNorm ψ (2 : ℝ≥0∞) volume).toReal ≤ S := by
    change (eLpNorm ψ (2 : ℝ≥0∞) volume).toReal ≤
      2 + max (sSup (Set.range fun i ↦ intervalLength (![A, J] i)))
        (max (supportRadius ψ ^ 2)
          (max (eLpNorm ψ 1 volume).toReal
            (max (eLpNorm ψ 2 volume).toReal
              (max (eLpNorm (deriv ψ) 1 volume).toReal
                (eLpNorm (deriv ψ) 2 volume).toReal))))
    have : (eLpNorm ψ (2 : ℝ≥0∞) volume).toReal ≤
        max (sSup (Set.range fun i ↦ intervalLength (![A, J] i)))
          (max (supportRadius ψ ^ 2)
            (max (eLpNorm ψ 1 volume).toReal
              (max (eLpNorm ψ 2 volume).toReal
                (max (eLpNorm (deriv ψ) 1 volume).toReal
                  (eLpNorm (deriv ψ) 2 volume).toReal)))) := by
      exact le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right (le_max_of_le_left le_rfl)))
    linarith
  have hS_deriv : (eLpNorm (deriv ψ) (2 : ℝ≥0∞) volume).toReal ≤ S := by
    change (eLpNorm (deriv ψ) (2 : ℝ≥0∞) volume).toReal ≤
      2 + max (sSup (Set.range fun i ↦ intervalLength (![A, J] i)))
        (max (supportRadius ψ ^ 2)
          (max (eLpNorm ψ 1 volume).toReal
            (max (eLpNorm ψ 2 volume).toReal
              (max (eLpNorm (deriv ψ) 1 volume).toReal
                (eLpNorm (deriv ψ) 2 volume).toReal))))
    have : (eLpNorm (deriv ψ) (2 : ℝ≥0∞) volume).toReal ≤
        max (sSup (Set.range fun i ↦ intervalLength (![A, J] i)))
          (max (supportRadius ψ ^ 2)
            (max (eLpNorm ψ 1 volume).toReal
              (max (eLpNorm ψ 2 volume).toReal
                (max (eLpNorm (deriv ψ) 1 volume).toReal
                  (eLpNorm (deriv ψ) 2 volume).toReal)))) := by
      exact le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right
          (le_max_of_le_right (le_max_of_le_right le_rfl))))
    linarith
  have hsqrt : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
    have hsquare : (Real.sqrt 2) ^ 2 = 2 := by
      rw [Real.sq_sqrt]
      norm_num
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hsqrt_div_pi : Real.sqrt 2 / Real.pi ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  have hS_nonneg : 0 ≤ S := by
    change 0 ≤ 2 + max (sSup (Set.range fun i ↦ intervalLength (![A, J] i)))
      (max (supportRadius ψ ^ 2)
        (max (eLpNorm ψ 1 volume).toReal
          (max (eLpNorm ψ 2 volume).toReal
            (max (eLpNorm (deriv ψ) 1 volume).toReal
              (eLpNorm (deriv ψ) 2 volume).toReal))))
    positivity
  change Real.sqrt 2 * (eLpNorm ψ (2 : ℝ≥0∞) volume).toReal +
      (Real.sqrt 2 / Real.pi) * (eLpNorm (deriv ψ) (2 : ℝ≥0∞) volume).toReal ≤ 2 * S
  have hcoeff : Real.sqrt 2 + Real.sqrt 2 / Real.pi ≤ 2 := by
    linarith
  calc
    Real.sqrt 2 * (eLpNorm ψ (2 : ℝ≥0∞) volume).toReal +
        (Real.sqrt 2 / Real.pi) * (eLpNorm (deriv ψ) (2 : ℝ≥0∞) volume).toReal ≤
        Real.sqrt 2 * S + (Real.sqrt 2 / Real.pi) * S := by
      exact add_le_add
        (calc
          Real.sqrt 2 * (eLpNorm ψ (2 : ℝ≥0∞) volume).toReal ≤
              Real.sqrt 2 * S :=
            mul_le_mul_of_nonneg_left hS_L2 (Real.sqrt_nonneg _))
        (calc
          (Real.sqrt 2 / Real.pi) * (eLpNorm (deriv ψ) (2 : ℝ≥0∞) volume).toReal ≤
              (Real.sqrt 2 / Real.pi) * S :=
            mul_le_mul_of_nonneg_left hS_deriv (by positivity))
    _ = (Real.sqrt 2 + Real.sqrt 2 / Real.pi) * S := by ring
    _ ≤ 2 * S := mul_le_mul_of_nonneg_right hcoeff hS_nonneg

/-- A product of two square-root measure bounds is bounded by their common
nonnegative upper bound.  This is used for the localized factors in
`gowersDifferencing`. -/
lemma aux_gowers_rpow_half_mul_le
    {x y R : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hR : 0 ≤ R)
    (hxR : x ≤ R) (hyR : y ≤ R) :
    x ^ (1 / (2 : ℝ)) * y ^ (1 / (2 : ℝ)) ≤ R := by
  have hxhalf : x ^ (1 / (2 : ℝ)) ≤ R ^ (1 / (2 : ℝ)) :=
    Real.rpow_le_rpow hx hxR (by norm_num)
  have hyhalf : y ^ (1 / (2 : ℝ)) ≤ R ^ (1 / (2 : ℝ)) :=
    Real.rpow_le_rpow hy hyR (by norm_num)
  calc
    x ^ (1 / (2 : ℝ)) * y ^ (1 / (2 : ℝ)) ≤
        R ^ (1 / (2 : ℝ)) * R ^ (1 / (2 : ℝ)) :=
      mul_le_mul hxhalf hyhalf (Real.rpow_nonneg hy _) (Real.rpow_nonneg hR _)
    _ = R := by
      rw [← Real.rpow_add' hR (by norm_num : (1 / (2 : ℝ)) + 1 / 2 ≠ 0)]
      norm_num

/-- The two interaction-range localized differences have an `L²`-norm
product controlled by the common interaction-range measure.  This is the
localization bookkeeping for `gowersDifferencing`. -/
lemma aux_gowers_restricted_difference_l2_product_le
    (A J : Set ℝ) (M : ℝ) (c : Fin 4 → ℝ) (g : Fin 4 → ℝ → ℂ)
    (hA : ∃ a b : ℝ, a < b ∧ A = Set.Icc a b)
    (hJ : ∃ p q : ℝ, p < q ∧ J = Set.Icc p q)
    (hMone : 1 ≤ M) (hc2M : |c 2| ≤ M) (hc3M : |c 3| ≤ M)
    (hgmeas : ∀ i : Fin 4, AEStronglyMeasurable (g i) volume)
    (hgbound : ∀ i : Fin 4, ∀ᵐ x ∂volume, ‖g i x‖ ≤ 1)
    (h₂ h₃ : ℝ) :
    (eLpNorm (multiplicativeDifference h₂
        (aux_gowersRestrict (aux_gowersInteractionRange A J (c 2)) (g 2)))
        (2 : ℝ≥0∞) volume).toReal *
      (eLpNorm (multiplicativeDifference h₃
        (aux_gowersRestrict (aux_gowersInteractionRange A J (c 3)) (g 3)))
        (2 : ℝ≥0∞) volume).toReal ≤
      M * (volume.real A + volume.real J) := by
  have hAcompact : IsCompact A := by
    rcases hA with ⟨a, b, hab, rfl⟩
    exact isCompact_Icc
  have hJcompact : IsCompact J := by
    rcases hJ with ⟨p, q, hpq, rfl⟩
    exact isCompact_Icc
  have hB2compact : IsCompact (aux_gowersInteractionRange A J (c 2)) :=
    aux_gowersInteractionRange_compact A J (c 2) hAcompact hJcompact
  have hB3compact : IsCompact (aux_gowersInteractionRange A J (c 3)) :=
    aux_gowersInteractionRange_compact A J (c 3) hAcompact hJcompact
  have hnorm2 := aux_eLpNorm_multiplicativeDifference_restrict_le
    (aux_gowersInteractionRange A J (c 2)) (g 2) h₂ hB2compact (hgmeas 2) (hgbound 2)
  have hnorm3 := aux_eLpNorm_multiplicativeDifference_restrict_le
    (aux_gowersInteractionRange A J (c 3)) (g 3) h₃ hB3compact (hgmeas 3) (hgbound 3)
  have hmeasure2 := aux_gowersInteractionRange_volume_real_le_of_intervals
    A J (c 2) M hA hJ hMone hc2M
  have hmeasure3 := aux_gowersInteractionRange_volume_real_le_of_intervals
    A J (c 3) M hA hJ hMone hc3M
  have hRnonneg : 0 ≤ M * (volume.real A + volume.real J) := by
    positivity
  have hB2nonneg : 0 ≤ volume.real (aux_gowersInteractionRange A J (c 2)) :=
    MeasureTheory.measureReal_nonneg
  have hB3nonneg : 0 ≤ volume.real (aux_gowersInteractionRange A J (c 3)) :=
    MeasureTheory.measureReal_nonneg
  calc
    (eLpNorm (multiplicativeDifference h₂
        (aux_gowersRestrict (aux_gowersInteractionRange A J (c 2)) (g 2)))
        (2 : ℝ≥0∞) volume).toReal *
      (eLpNorm (multiplicativeDifference h₃
        (aux_gowersRestrict (aux_gowersInteractionRange A J (c 3)) (g 3)))
        (2 : ℝ≥0∞) volume).toReal ≤
      (volume.real (aux_gowersInteractionRange A J (c 2))) ^ (1 / (2 : ℝ)) *
        (volume.real (aux_gowersInteractionRange A J (c 3))) ^ (1 / (2 : ℝ)) := by
        exact mul_le_mul hnorm2 hnorm3
          ENNReal.toReal_nonneg (Real.rpow_nonneg hB2nonneg _)
    _ ≤ M * (volume.real A + volume.real J) :=
      aux_gowers_rpow_half_mul_le hB2nonneg hB3nonneg hRnonneg hmeasure2 hmeasure3

/-- The localized interaction-range `L²` product is at most `2 M S`.
This is the size-parameter form used by `gowersDifferencing`. -/
lemma aux_gowers_restricted_difference_l2_product_le_two_mul_M_mul_size
    (A J : Set ℝ) (ψ : ℝ → ℝ) (M : ℝ) (c : Fin 4 → ℝ) (g : Fin 4 → ℝ → ℂ)
    (hA : ∃ a b : ℝ, a < b ∧ A = Set.Icc a b)
    (hJ : ∃ p q : ℝ, p < q ∧ J = Set.Icc p q)
    (hMone : 1 ≤ M) (hc2M : |c 2| ≤ M) (hc3M : |c 3| ≤ M)
    (hgmeas : ∀ i : Fin 4, AEStronglyMeasurable (g i) volume)
    (hgbound : ∀ i : Fin 4, ∀ᵐ x ∂volume, ‖g i x‖ ≤ 1)
    (h₂ h₃ : ℝ) :
    (eLpNorm (multiplicativeDifference h₂
        (aux_gowersRestrict (aux_gowersInteractionRange A J (c 2)) (g 2)))
        (2 : ℝ≥0∞) volume).toReal *
      (eLpNorm (multiplicativeDifference h₃
        (aux_gowersRestrict (aux_gowersInteractionRange A J (c 3)) (g 3)))
        (2 : ℝ≥0∞) volume).toReal ≤
      2 * M * sizeParameter ![A, J] ψ := by
  have hsum : volume.real A + volume.real J ≤ 2 * sizeParameter ![A, J] ψ := by
    simpa only [intervalLength, Measure.real] using
      aux_intervalLength_sum_le_two_mul_sizeParameter A J ψ
  have hMnonneg : 0 ≤ M := zero_le_one.trans hMone
  calc
    (eLpNorm (multiplicativeDifference h₂
        (aux_gowersRestrict (aux_gowersInteractionRange A J (c 2)) (g 2)))
        (2 : ℝ≥0∞) volume).toReal *
      (eLpNorm (multiplicativeDifference h₃
        (aux_gowersRestrict (aux_gowersInteractionRange A J (c 3)) (g 3)))
        (2 : ℝ≥0∞) volume).toReal ≤
        M * (volume.real A + volume.real J) :=
      aux_gowers_restricted_difference_l2_product_le A J M c g hA hJ hMone hc2M hc3M
        hgmeas hgbound h₂ h₃
    _ ≤ M * (2 * sizeParameter ![A, J] ψ) :=
      mul_le_mul_of_nonneg_left hsum hMnonneg
    _ = 2 * M * sizeParameter ![A, J] ψ := by ring

/-- Combining the cutoff Fourier and localized `L²` factors gives the
`4 M S²` constant used before the coefficient and uniformity factors in
`gowersDifferencing`. -/
lemma aux_gowers_cutoff_l2_constant_le_four_mul_M_mul_size_sq
    (A J : Set ℝ) (ψ : ℝ → ℝ) (M P : ℝ)
    (hPnonneg : 0 ≤ P)
    (hP : P ≤ 2 * M * sizeParameter ![A, J] ψ) :
    C_productCutoffFourierBounds ψ * P ≤
      4 * M * sizeParameter ![A, J] ψ ^ (2 : ℕ) := by
  have hC := aux_gowers_productCutoffConstant_le_two_mul_sizeParameter A J ψ
  have hSnonneg : 0 ≤ sizeParameter ![A, J] ψ := by
    unfold sizeParameter
    positivity
  calc
    C_productCutoffFourierBounds ψ * P ≤
        (2 * sizeParameter ![A, J] ψ) * (2 * M * sizeParameter ![A, J] ψ) :=
      mul_le_mul hC hP hPnonneg (by positivity)
    _ = 4 * M * sizeParameter ![A, J] ψ ^ (2 : ℕ) := by ring

/-- Separation yields the reciprocal bound used for each affine coefficient
in the Fourier step of `gowersDifferencing`. -/
lemma aux_gowers_abs_inv_le_inv_of_le_abs
    (δ x : ℝ) (hδpos : 0 < δ) (hδx : δ ≤ |x|) :
    |x⁻¹| ≤ δ⁻¹ := by
  rw [abs_inv]
  exact inv_anti₀ hδpos hδx

/-- A numerator bounded by `M` and a denominator separated by `δ` have
ratio at most `M / δ`.  This supports affine frequency bookkeeping in
`gowersDifferencing`. -/
lemma aux_gowers_abs_div_le_div
    (a b δ M : ℝ) (hδpos : 0 < δ) (hnum : |a| ≤ M)
    (hden : δ ≤ |b|) :
    |a / b| ≤ M / δ := by
  rw [abs_div, div_eq_mul_inv, div_eq_mul_inv]
  have hinv : |b|⁻¹ ≤ δ⁻¹ := inv_anti₀ hδpos hden
  exact mul_le_mul hnum hinv (inv_nonneg.mpr (abs_nonneg _))
    (le_trans (abs_nonneg _) hnum)

/-- The zero coefficient and separation bound every nonzero-index
coefficient from below by `δ`.  This is used in `gowersDifferencing`. -/
lemma aux_gowers_delta_le_abs_coeff
    (δ : ℝ) (c : Fin 4 → ℝ) (hczero : c 0 = 0)
    (hcseparated : ∀ i j : Fin 4, i < j → δ ≤ |c i - c j|)
    (i : Fin 4) (hi : 0 < i) :
    δ ≤ |c i| := by
  have h := hcseparated 0 i hi
  simpa [hczero, abs_neg] using h

/-- The pairwise upper-separation condition bounds each nonzero-index
coefficient by `M`; this is auxiliary ratio bookkeeping for
`gowersDifferencing`. -/
lemma aux_gowers_abs_coeff_le_M
    (M : ℝ) (c : Fin 4 → ℝ) (hczero : c 0 = 0)
    (hcbounded : ∀ i j : Fin 4, i < j → |c i - c j| ≤ M)
    (i : Fin 4) (hi : 0 < i) :
    |c i| ≤ M := by
  have h := hcbounded 0 i hi
  simpa [hczero, abs_neg] using h

/-- All affine frequency ratios occurring after differencing are bounded by
`M / δ`.  This packages the coefficient conditions for
`gowersDifferencing`. -/
lemma aux_gowers_abs_difference_div_coeff_le
    (δ M : ℝ) (hδpos : 0 < δ) (c : Fin 4 → ℝ) (hczero : c 0 = 0)
    (hcseparated : ∀ i j : Fin 4, i < j → δ ≤ |c i - c j|)
    (hcbounded : ∀ i j : Fin 4, i < j → |c i - c j| ≤ M)
    (i j k : Fin 4) (hij : i < j) (hk : 0 < k) :
    |(c j - c i) / c k| ≤ M / δ := by
  apply aux_gowers_abs_div_le_div _ _ δ M hδpos
  · simpa [abs_sub_comm] using hcbounded i j hij
  · exact aux_gowers_delta_le_abs_coeff δ c hczero hcseparated k hk

/-- The coefficient occurring before the final square root is at most
`δ⁻³`.  This is the squared coefficient estimate used by
`gowersDifferencing`. -/
lemma aux_gowers_squared_coefficient_le
    (δ : ℝ) (hδpos : 0 < δ) (hδleone : δ ≤ 1)
    (c : Fin 4 → ℝ) (hczero : c 0 = 0)
    (hcseparated : ∀ i j : Fin 4, i < j → δ ≤ |c i - c j|) :
    |((c 2 - c 1) * (c 3 - c 1))⁻¹| ^ (1 / (2 : ℝ)) *
        |(c 1)⁻¹| ≤ δ ^ (-3 : ℝ) := by
  have h21 : δ ≤ |c 2 - c 1| := by
    simpa [abs_sub_comm] using hcseparated 1 2 (by decide)
  have h31 : δ ≤ |c 3 - c 1| := by
    simpa [abs_sub_comm] using hcseparated 1 3 (by decide)
  have h1 : δ ≤ |c 1| :=
    aux_gowers_delta_le_abs_coeff δ c hczero hcseparated 1 (by decide)
  have hinv21 : |(c 2 - c 1)⁻¹| ≤ δ⁻¹ :=
    aux_gowers_abs_inv_le_inv_of_le_abs δ (c 2 - c 1) hδpos h21
  have hinv31 : |(c 3 - c 1)⁻¹| ≤ δ⁻¹ :=
    aux_gowers_abs_inv_le_inv_of_le_abs δ (c 3 - c 1) hδpos h31
  have hinv1 : |(c 1)⁻¹| ≤ δ⁻¹ :=
    aux_gowers_abs_inv_le_inv_of_le_abs δ (c 1) hδpos h1
  have hinv21' : |c 2 - c 1|⁻¹ ≤ δ⁻¹ := by
    simpa [abs_inv] using hinv21
  have hinv31' : |c 3 - c 1|⁻¹ ≤ δ⁻¹ := by
    simpa [abs_inv] using hinv31
  have hdet : |((c 2 - c 1) * (c 3 - c 1))⁻¹| ≤ δ⁻¹ * δ⁻¹ := by
    rw [abs_inv, abs_mul, mul_inv]
    exact mul_le_mul hinv21' hinv31' (inv_nonneg.mpr (abs_nonneg _))
      (inv_nonneg.mpr hδpos.le)
  have hdetroot : |((c 2 - c 1) * (c 3 - c 1))⁻¹| ^ (1 / (2 : ℝ)) ≤ δ⁻¹ := by
    calc
      |((c 2 - c 1) * (c 3 - c 1))⁻¹| ^ (1 / (2 : ℝ)) ≤
          (δ⁻¹ * δ⁻¹) ^ (1 / (2 : ℝ)) :=
        Real.rpow_le_rpow (abs_nonneg _) hdet (by norm_num)
      _ = δ⁻¹ := by
        rw [← Real.rpow_neg_one δ]
        rw [← Real.rpow_add hδpos, ← Real.rpow_mul hδpos.le]
        norm_num
  have htwopow : δ⁻¹ * δ⁻¹ = δ ^ (-2 : ℝ) := by
    rw [← Real.rpow_neg_one δ]
    rw [← Real.rpow_add hδpos]
    norm_num
  calc
    |((c 2 - c 1) * (c 3 - c 1))⁻¹| ^ (1 / (2 : ℝ)) *
        |(c 1)⁻¹| ≤ δ⁻¹ * δ⁻¹ :=
      mul_le_mul hdetroot hinv1 (abs_nonneg _) (inv_nonneg.mpr hδpos.le)
    _ = δ ^ (-2 : ℝ) := htwopow
    _ ≤ δ ^ (-3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hδpos hδleone (by norm_num)

/--
Let $A,J$ be positive-length compact intervals. Let $\psi\in C_c^1(\R)$ satisfy
$0\leq\psi\leq1$ and $\supp\psi\subset J$. Let
$c_0=0,c_1,c_2,c_3\in\R$ satisfy
\[
0<\delta\leq\min_{0\leq i<j\leq3}|c_i-c_j|,
\]
\[
\max_{0\leq i<j\leq3}|c_i-c_j|\leq M,
\]
where $0<\delta\leq1$ and $M\geq1$. Let $g_0,g_1,g_2,g_3$ be $1$-bounded,
assume $g_0$ is supported in $A$, and assume $g_1$ is compactly supported. Define
\[
C_{\ref{prop:gowers-differencing},\,A,J,\psi}
:=
2^2\Ssize{A,J}{\psi}^{2}.
\]
Then
\[
\left|
\iint g_0(x)g_1(x+c_1t)g_2(x+c_2t)g_3(x+c_3t)\psi(t)
\dd t\dd x
\right|
\leq
C_{\ref{prop:gowers-differencing},\,A,J,\psi}
M\delta^{-3/2}\uNorm{g_1}3.
\]
-/
theorem gowersDifferencing
    (A J : Set ℝ) (ψ : ℝ → ℝ)
    (hA : ∃ a b : ℝ, a < b ∧ A = Set.Icc a b)
    (hJ : ∃ a b : ℝ, a < b ∧ J = Set.Icc a b)
    (hψ_smooth : ContDiff ℝ 1 ψ) (hψ_compact : HasCompactSupport ψ)
    (hψ_nonneg : ∀ t : ℝ, 0 ≤ ψ t) (hψ_le_one : ∀ t : ℝ, ψ t ≤ 1)
    (hψ_support : tsupport ψ ⊆ J)
    (δ M : ℝ) (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1) (hM_one : 1 ≤ M)
    (c : Fin 4 → ℝ) (hc_zero : c 0 = 0)
    (hc_separated : ∀ i j : Fin 4, i < j → δ ≤ |c i - c j|)
    (hc_bounded : ∀ i j : Fin 4, i < j → |c i - c j| ≤ M)
    (g : Fin 4 → ℝ → ℂ)
    (hg_measurable : ∀ i : Fin 4, AEStronglyMeasurable (g i) volume)
    (hg_one_bounded : ∀ i : Fin 4, ∀ᵐ x ∂volume, ‖g i x‖ ≤ 1)
    (hg_zero_support : ∀ᵐ x ∂volume, x ∉ A → g 0 x = 0)
    (hg_one_compact : HasCompactSupport (g 1)) :
    ENNReal.ofReal ‖∫ x : ℝ, ∫ t : ℝ,
        g 0 x * g 1 (x + c 1 * t) * g 2 (x + c 2 * t) * g 3 (x + c 3 * t) *
          (ψ t : ℂ)‖ ≤
      ENNReal.ofReal
          (C_gowersDifferencing A J ψ * M * δ ^ (-(3 / 2 : ℝ))) *
        uNorm 3 (g 1) := by
  rcases hA with ⟨a, b, hab, rfl⟩
  rcases hJ with ⟨p, q, hpq, rfl⟩
  have hAcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  have hJcompact : IsCompact (Set.Icc p q) := isCompact_Icc
  have hc1 : c 1 ≠ 0 :=
    aux_gowers_coeff_ne_zero_of_separated δ hδ_pos c hc_zero hc_separated 1 (by decide)
  have hc2 : c 2 ≠ 0 :=
    aux_gowers_coeff_ne_zero_of_separated δ hδ_pos c hc_zero hc_separated 2 (by decide)
  have hc3 : c 3 ≠ 0 :=
    aux_gowers_coeff_ne_zero_of_separated δ hδ_pos c hc_zero hc_separated 3 (by decide)
  have hInt := aux_gowers_integrand_integrable_of_main_data (Set.Icc a b) (Set.Icc p q) ψ
    ⟨a, b, hab, rfl⟩ ⟨p, q, hpq, rfl⟩ hψ_smooth hψ_nonneg hψ_le_one hψ_support
    δ hδ_pos c hc_zero hc_separated g hg_measurable hg_one_bounded hg_zero_support
  have hloc := aux_gowers_double_integral_restrict_g2g3 (Set.Icc a b) (Set.Icc p q) ψ c g
    hg_zero_support hψ_support hInt
  let gL : Fin 4 → ℝ → ℂ := aux_gowersLocalizedFactors (Set.Icc a b) (Set.Icc p q) c g
  have hgLmeas : ∀ i : Fin 4, AEStronglyMeasurable (gL i) volume := by
    simpa only [gL] using aux_gowersLocalizedFactors_aestronglyMeasurable
      (Set.Icc a b) (Set.Icc p q) c g hAcompact hJcompact hg_measurable
  have hgLbound : ∀ i : Fin 4, ∀ᵐ x ∂volume, ‖gL i x‖ ≤ 1 := by
    simpa only [gL] using aux_gowersLocalizedFactors_ae_one_bounded
      (Set.Icc a b) (Set.Icc p q) c g hg_one_bounded
  have hQmeas : AEStronglyMeasurable (Function.uncurry (aux_gowersKernel c gL ψ))
      (volume.prod volume) :=
    aux_gowersKernel_aestronglyMeasurable c gL ψ hgLmeas hψ_smooth.continuous
  have hQbound : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      ‖aux_gowersKernel c gL ψ z.1 z.2‖ ≤ 1 :=
    aux_gowersKernel_ae_one_bounded c gL ψ hgLbound hψ_nonneg hψ_le_one
  let X : Set ℝ := aux_gowersSpatialRange (c 1) (gL 1) (Set.Icc p q)
  have hXcompact : IsCompact X := by
    change IsCompact (aux_gowersSpatialRange (c 1) (g 1) (Set.Icc p q))
    exact aux_gowersSpatialRange_compact (c 1) (g 1) (Set.Icc p q) hg_one_compact hJcompact
  have hQsupport : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∉ X ×ˢ Set.Icc p q → aux_gowersKernel c gL ψ z.1 z.2 = 0 := by
    filter_upwards with z
    apply aux_gowersKernel_ae_zero_outside_spatial_time c gL ψ (Set.Icc p q)
    simpa only [X, gL, aux_gowersLocalizedFactors] using hψ_support
  have hg0L2 : MemLp (gL 0) (2 : ℝ≥0∞) volume := by
    change MemLp (g 0) (2 : ℝ≥0∞) volume
    apply aux_memLp_of_ae_bound_of_ae_support (gL 0) (hgLmeas 0) 1 (hgLbound 0)
      (Set.Icc a b) hAcompact.isClosed.measurableSet hAcompact.measure_lt_top
    change ∀ᵐ x ∂volume, x ∉ Set.Icc a b → g 0 x = 0
    exact hg_zero_support
  have houter := aux_outer_cauchy_sq_le_autocorrelation_compactSupport
    (Set.Icc a b) X (Set.Icc p q) hAcompact hXcompact hJcompact (gL 0) hg0L2
      (hgLbound 0) (by
        change ∀ᵐ x ∂volume, x ∉ Set.Icc a b → g 0 x = 0
        exact hg_zero_support)
      (aux_gowersKernel c gL ψ) hQmeas hQbound hQsupport
  have hR := aux_autocorrelation_integrable_compactSupport X (Set.Icc p q)
    hXcompact hJcompact (aux_gowersKernel c gL ψ) hQmeas hQbound hQsupport
  let C : ℝ → ℂ := fun h ↦ ∫ x : ℝ, ∫ t : ℝ,
    aux_gowersKernel c gL ψ x t *
      starRingEnd ℂ (aux_gowersKernel c gL ψ x (t + h))
  let D : ℝ → ℂ := fun h ↦ ∫ y : ℝ, ∫ t : ℝ,
    multiplicativeDifference h (gL 1) y *
      multiplicativeDifference ((c 2 / c 1) * h) (gL 2)
        (y + (c 2 - c 1) * t) *
      multiplicativeDifference ((c 3 / c 1) * h) (gL 3)
        (y + (c 3 - c 1) * t) *
      ((ψ t * ψ (t + (c 1)⁻¹ * h) : ℝ) : ℂ)
  have hcoord := aux_gowersKernel_correlation_change_rescaled_ae c gL ψ hc1 hR
  have hcoordScaled : C =ᵐ[volume] fun h ↦ D (c 1 * h) := by
    have hpull := (aux_gowers_local_qmp_affine_t 0 (c 1) hc1).ae hcoord
    filter_upwards [hpull] with h hh
    have hscale : (c 1)⁻¹ * (c 1 * h) = h := by
      field_simp
    simpa [C, D, hscale] using hh
  have hc12 : c 1 ≠ c 2 := by
    intro h
    have hs := hc_separated 1 2 (by decide)
    rw [h, sub_self, abs_zero] at hs
    exact (not_le_of_gt hδ_pos) hs
  have hc13 : c 1 ≠ c 3 := by
    intro h
    have hs := hc_separated 1 3 (by decide)
    rw [h, sub_self, abs_zero] at hs
    exact (not_le_of_gt hδ_pos) hs
  have hc23 : c 2 ≠ c 3 := by
    intro h
    have hs := hc_separated 2 3 (by decide)
    rw [h, sub_self, abs_zero] at hs
    exact (not_le_of_gt hδ_pos) hs
  have ha : c 2 - c 1 ≠ 0 := sub_ne_zero.mpr hc12.symm
  have hb : c 3 - c 1 ≠ 0 := sub_ne_zero.mpr hc13.symm
  have hab' : c 2 - c 1 ≠ c 3 - c 1 := by
    intro h
    apply hc23
    linarith
  have hB2 : IsCompact (aux_gowersInteractionRange (Set.Icc a b) (Set.Icc p q) (c 2)) :=
    aux_gowersInteractionRange_compact (Set.Icc a b) (Set.Icc p q) (c 2) hAcompact hJcompact
  have hB3 : IsCompact (aux_gowersInteractionRange (Set.Icc a b) (Set.Icc p q) (c 3)) :=
    aux_gowersInteractionRange_compact (Set.Icc a b) (Set.Icc p q) (c 3) hAcompact hJcompact
  have hgL1compact : HasCompactSupport (gL 1) := by
    change HasCompactSupport (g 1)
    exact hg_one_compact
  have hgL2compact : HasCompactSupport (gL 2) := by
    change HasCompactSupport
      (aux_gowersRestrict (aux_gowersInteractionRange (Set.Icc a b) (Set.Icc p q) (c 2)) (g 2))
    exact aux_gowersRestrict_hasCompactSupport _ _ hB2
  have hgL3compact : HasCompactSupport (gL 3) := by
    change HasCompactSupport
      (aux_gowersRestrict (aux_gowersInteractionRange (Set.Icc a b) (Set.Icc p q) (c 3)) (g 3))
    exact aux_gowersRestrict_hasCompactSupport _ _ hB3
  have hDfourier (h : ℝ) :
      ‖D h‖ ≤ (eLpNorm (𝓕 (multiplicativeDifference h (gL 1))) ∞ volume).toReal *
        (eLpNorm (𝓕 (fun t : ℝ ↦ ((ψ t * ψ (t + (c 1)⁻¹ * h) : ℝ) : ℂ)))
          (1 : ℝ≥0∞) volume).toReal *
          |((c 2 - c 1) * (c 3 - c 1))⁻¹| ^ (1 / (2 : ℝ)) *
          (eLpNorm (multiplicativeDifference ((c 2 / c 1) * h) (gL 2))
            (2 : ℝ≥0∞) volume).toReal *
          (eLpNorm (multiplicativeDifference ((c 3 / c 1) * h) (gL 3))
            (2 : ℝ≥0∞) volume).toReal := by
    have hf := aux_memLp_multiplicativeDifference_of_ae_bound_hasCompactSupport
      (gL 1) (hgLmeas 1) (hgLbound 1) hgL1compact h
    have hG := aux_memLp_multiplicativeDifference_of_ae_bound_hasCompactSupport
      (gL 2) (hgLmeas 2) (hgLbound 2) hgL2compact ((c 2 / c 1) * h)
    have hH := aux_memLp_multiplicativeDifference_of_ae_bound_hasCompactSupport
      (gL 3) (hgLmeas 3) (hgLbound 3) hgL3compact ((c 3 / c 1) * h)
    let w : ℝ → ℂ := fun t ↦ ((ψ t * ψ (t + (c 1)⁻¹ * h) : ℝ) : ℂ)
    have hwc : Continuous w := by
      exact Complex.continuous_ofReal.comp
        (aux_productCutoffSmooth ψ hψ_smooth ((c 1)⁻¹ * h)).continuous
    have hw : Integrable w volume := by
      exact memLp_one_iff_integrable.mp
        (aux_productCutoffMemLpOne ψ hψ_smooth hψ_compact ((c 1)⁻¹ * h))
    have hFw1 : MemLp (𝓕 w) (1 : ℝ≥0∞) volume := by
      exact aux_gowersFourier_productCutoff_memLp_rawFourier_one
        ψ hψ_smooth hψ_compact ((c 1)⁻¹ * h)
    simpa only [D, w] using
      aux_gowersFourier_trilinear_fourier_bound_eLpNorm
        (c 2 - c 1) (c 3 - c 1)
        (multiplicativeDifference h (gL 1))
        (multiplicativeDifference ((c 2 / c 1) * h) (gL 2))
        (multiplicativeDifference ((c 3 / c 1) * h) (gL 3)) w
        hab' ha hb hf.1 hf.2 hG.1 hH.1 hG.2 hH.2 hwc hw hFw1
  let S : ℝ := sizeParameter ![Set.Icc a b, Set.Icc p q] ψ
  let kdet : ℝ := |((c 2 - c 1) * (c 3 - c 1))⁻¹| ^ (1 / (2 : ℝ))
  let K : ℝ := 4 * M * S ^ (2 : ℕ) * kdet
  have hD_uniform (h : ℝ) :
      ‖D h‖ ≤ (eLpNorm (𝓕 (multiplicativeDifference h (gL 1))) ∞ volume).toReal * K := by
    let E : ℝ := (eLpNorm (𝓕 (multiplicativeDifference h (gL 1))) ∞ volume).toReal
    let W : ℝ := (eLpNorm
      (𝓕 (fun t : ℝ ↦ ((ψ t * ψ (t + (c 1)⁻¹ * h) : ℝ) : ℂ)))
      (1 : ℝ≥0∞) volume).toReal
    let N₂ : ℝ := (eLpNorm (multiplicativeDifference ((c 2 / c 1) * h) (gL 2))
      (2 : ℝ≥0∞) volume).toReal
    let N₃ : ℝ := (eLpNorm (multiplicativeDifference ((c 3 / c 1) * h) (gL 3))
      (2 : ℝ≥0∞) volume).toReal
    let P : ℝ := N₂ * N₃
    have hc2M : |c 2| ≤ M := by
      simpa [hc_zero, abs_neg] using hc_bounded 0 2 (by decide)
    have hc3M : |c 3| ≤ M := by
      simpa [hc_zero, abs_neg] using hc_bounded 0 3 (by decide)
    have hP : P ≤ 2 * M * S := by
      dsimp only [P, N₂, N₃]
      change
        (eLpNorm (multiplicativeDifference ((c 2 / c 1) * h)
          (aux_gowersRestrict (aux_gowersInteractionRange (Set.Icc a b) (Set.Icc p q) (c 2))
            (g 2))) (2 : ℝ≥0∞) volume).toReal *
          (eLpNorm (multiplicativeDifference ((c 3 / c 1) * h)
            (aux_gowersRestrict (aux_gowersInteractionRange (Set.Icc a b) (Set.Icc p q) (c 3))
              (g 3))) (2 : ℝ≥0∞) volume).toReal ≤ 2 * M * S
      simpa only [S] using
        (aux_gowers_restricted_difference_l2_product_le_two_mul_M_mul_size
          (Set.Icc a b) (Set.Icc p q) ψ M c g
          ⟨a, b, hab, rfl⟩ ⟨p, q, hpq, rfl⟩ hM_one hc2M hc3M
          hg_measurable hg_one_bounded ((c 2 / c 1) * h) ((c 3 / c 1) * h))
    have hPnonneg : 0 ≤ P := by
      dsimp only [P, N₂, N₃]
      exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    have hcut : W ≤ C_productCutoffFourierBounds ψ := by
      dsimp only [W]
      exact productCutoffFourierBounds ψ hψ_smooth hψ_compact hψ_nonneg hψ_le_one
        ((c 1)⁻¹ * h)
    have hcutP : C_productCutoffFourierBounds ψ * P ≤ 4 * M * S ^ (2 : ℕ) := by
      simpa only [S] using
        (aux_gowers_cutoff_l2_constant_le_four_mul_M_mul_size_sq
          (Set.Icc a b) (Set.Icc p q) ψ M P hPnonneg (by simpa only [S] using hP))
    have hWP : W * P ≤ 4 * M * S ^ (2 : ℕ) := by
      exact (mul_le_mul_of_nonneg_right hcut hPnonneg).trans hcutP
    have hE0 : 0 ≤ E := ENNReal.toReal_nonneg
    have hkdet0 : 0 ≤ kdet := by
      dsimp only [kdet]
      exact Real.rpow_nonneg (abs_nonneg _) _
    have hraw := hDfourier h
    change ‖D h‖ ≤ E * W * kdet * N₂ * N₃ at hraw
    calc
      ‖D h‖ ≤ E * W * kdet * N₂ * N₃ := hraw
      _ = (E * kdet) * (W * P) := by simp only [P]; ring
      _ ≤ (E * kdet) * (4 * M * S ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hWP (mul_nonneg hE0 hkdet0)
      _ = E * K := by simp only [K]; ring
  have hpoint : ∀ᵐ h : ℝ ∂volume,
      ENNReal.ofReal ‖∫ x : ℝ, ∫ t : ℝ,
        aux_gowersKernel c gL ψ x t *
          starRingEnd ℂ (aux_gowersKernel c gL ψ x (t + (c 1)⁻¹ * h))‖ ≤
        ENNReal.ofReal K *
          eLpNorm (𝓕 (multiplicativeDifference h (gL 1))) ∞ volume := by
    filter_upwards [hcoord] with h hh
    have hEtop : eLpNorm (𝓕 (multiplicativeDifference h (gL 1))) ∞ volume ≠ ∞ := by
      apply ne_of_lt
      exact lt_of_le_of_lt
        (aux_eLpNorm_fourier_le_integral_norm (multiplicativeDifference h (gL 1)))
        ENNReal.ofReal_lt_top
    have hreal : ‖D h‖ ≤
        (eLpNorm (𝓕 (multiplicativeDifference h (gL 1))) ∞ volume).toReal * K :=
      hD_uniform h
    calc
      ENNReal.ofReal ‖∫ x : ℝ, ∫ t : ℝ,
          aux_gowersKernel c gL ψ x t *
            starRingEnd ℂ (aux_gowersKernel c gL ψ x (t + (c 1)⁻¹ * h))‖ =
          ENNReal.ofReal ‖D h‖ := by rw [hh]
      _ ≤ ENNReal.ofReal
          ((eLpNorm (𝓕 (multiplicativeDifference h (gL 1))) ∞ volume).toReal * K) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal
          (eLpNorm (𝓕 (multiplicativeDifference h (gL 1))) ∞ volume).toReal *
          ENNReal.ofReal K := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      _ = ENNReal.ofReal K *
          eLpNorm (𝓕 (multiplicativeDifference h (gL 1))) ∞ volume := by
        rw [ENNReal.ofReal_toReal hEtop]
        ring
  let T : ℂ := ∫ x : ℝ, gL 0 x * ∫ t : ℝ, aux_gowersKernel c gL ψ x t
  have hbridge := aux_gowers_autocorrelation_to_uNorm_sq
    T (aux_gowersKernel c gL ψ) (gL 1) (volume.real (Set.Icc a b)) K (c 1)
    MeasureTheory.measureReal_nonneg hc1 hR (by simpa only [T] using houter) hpoint
  have hT : (∫ x : ℝ, ∫ t : ℝ,
      g 0 x * g 1 (x + c 1 * t) * g 2 (x + c 2 * t) * g 3 (x + c 3 * t) *
        (ψ t : ℂ)) = T := by
    rw [hloc]
    change (∫ x : ℝ, ∫ t : ℝ,
      g 0 x * g 1 (x + c 1 * t) *
        aux_gowersRestrict (aux_gowersInteractionRange (Set.Icc a b) (Set.Icc p q) (c 2))
          (g 2) (x + c 2 * t) *
        aux_gowersRestrict (aux_gowersInteractionRange (Set.Icc a b) (Set.Icc p q) (c 3))
          (g 3) (x + c 3 * t) * (ψ t : ℂ)) =
      ∫ x : ℝ, gL 0 x * ∫ t : ℝ, aux_gowersKernel c gL ψ x t
    calc
      (∫ x : ℝ, ∫ t : ℝ,
          g 0 x * g 1 (x + c 1 * t) *
            aux_gowersRestrict (aux_gowersInteractionRange (Set.Icc a b) (Set.Icc p q) (c 2))
              (g 2) (x + c 2 * t) *
            aux_gowersRestrict (aux_gowersInteractionRange (Set.Icc a b) (Set.Icc p q) (c 3))
              (g 3) (x + c 3 * t) * (ψ t : ℂ)) =
          ∫ x : ℝ, ∫ t : ℝ, gL 0 x * aux_gowersKernel c gL ψ x t := by
            apply integral_congr_ae
            filter_upwards with x
            apply integral_congr_ae
            filter_upwards with t
            change g 0 x * g 1 (x + c 1 * t) *
              aux_gowersRestrict (aux_gowersInteractionRange (Set.Icc a b) (Set.Icc p q) (c 2))
                (g 2) (x + c 2 * t) *
              aux_gowersRestrict (aux_gowersInteractionRange (Set.Icc a b) (Set.Icc p q) (c 3))
                (g 3) (x + c 3 * t) * (ψ t : ℂ) =
              g 0 x * aux_gowersKernel c gL ψ x t
            simp only [aux_gowersKernel]
            change g 0 x * g 1 (x + c 1 * t) *
              aux_gowersRestrict (aux_gowersInteractionRange (Set.Icc a b) (Set.Icc p q) (c 2))
                (g 2) (x + c 2 * t) *
              aux_gowersRestrict (aux_gowersInteractionRange (Set.Icc a b) (Set.Icc p q) (c 3))
                (g 3) (x + c 3 * t) * (ψ t : ℂ) =
              g 0 x *
                (g 1 (x + c 1 * t) *
                  aux_gowersRestrict (aux_gowersInteractionRange (Set.Icc a b) (Set.Icc p q) (c 2))
                    (g 2) (x + c 2 * t) *
                  aux_gowersRestrict (aux_gowersInteractionRange (Set.Icc a b) (Set.Icc p q) (c 3))
                    (g 3) (x + c 3 * t) * (ψ t : ℂ))
            ring
      _ = T := by
        simp only [T]
        apply integral_congr_ae
        filter_upwards with x
        rw [integral_const_mul]
  let R : ℝ := C_gowersDifferencing (Set.Icc a b) (Set.Icc p q) ψ * M *
    δ ^ (-(3 / 2 : ℝ))
  have hRnonneg : 0 ≤ R := by
    have hMnonneg : 0 ≤ M := zero_le_one.trans hM_one
    dsimp only [R, C_gowersDifferencing]
    positivity
  have hcoeffReal : volume.real (Set.Icc a b) * |(c 1)⁻¹| * K ≤ R ^ (2 : ℕ) := by
    have hB0 : 0 ≤ volume.real (Set.Icc a b) := MeasureTheory.measureReal_nonneg
    have hBS : volume.real (Set.Icc a b) ≤ S := by
      dsimp only [S]
      have hsize := aux_intervalLength_le_sizeParameter_two
        (Set.Icc a b) (Set.Icc p q) ψ 0
      change (volume (Set.Icc a b)).toReal ≤ sizeParameter ![Set.Icc a b, Set.Icc p q] ψ
      exact hsize
    have hS2 : 2 ≤ S := by
      dsimp only [S]
      unfold sizeParameter
      exact le_add_of_nonneg_right (by positivity)
    have hS0 : 0 ≤ S := zero_le_two.trans hS2
    have hM0 : 0 ≤ M := zero_le_one.trans hM_one
    have hq0 : 0 ≤ |(c 1)⁻¹| := abs_nonneg _
    have hk0 : 0 ≤ kdet := by
      dsimp only [kdet]
      exact Real.rpow_nonneg (abs_nonneg _) _
    have hδpow0 : 0 ≤ δ ^ (-3 : ℝ) := Real.rpow_nonneg hδ_pos.le _
    have hcoeff : kdet * |(c 1)⁻¹| ≤ δ ^ (-3 : ℝ) := by
      simpa only [kdet] using
        aux_gowers_squared_coefficient_le δ hδ_pos hδ_le_one c hc_zero hc_separated
    have hpre0 : 0 ≤ 4 * M * S ^ (2 : ℕ) * volume.real (Set.Icc a b) := by
      positivity
    have hfirst :
        volume.real (Set.Icc a b) * |(c 1)⁻¹| * K ≤
          (4 * M * S ^ (2 : ℕ) * volume.real (Set.Icc a b)) * (δ ^ (-3 : ℝ)) := by
      calc
        volume.real (Set.Icc a b) * |(c 1)⁻¹| * K =
            (4 * M * S ^ (2 : ℕ) * volume.real (Set.Icc a b)) *
              (kdet * |(c 1)⁻¹|) := by
                simp only [K]
                ring
        _ ≤ (4 * M * S ^ (2 : ℕ) * volume.real (Set.Icc a b)) *
              (δ ^ (-3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hcoeff hpre0
    have hfactor : volume.real (Set.Icc a b) ≤ 4 * M * S ^ (2 : ℕ) := by
      calc
        volume.real (Set.Icc a b) ≤ S := hBS
        _ ≤ 4 * M * S ^ (2 : ℕ) := by
          nlinarith [sq_nonneg S]
    have hbase : 4 * M * S ^ (2 : ℕ) * volume.real (Set.Icc a b) ≤
        (4 * M * S ^ (2 : ℕ)) ^ (2 : ℕ) := by
      have hbase0 : 0 ≤ 4 * M * S ^ (2 : ℕ) := by positivity
      calc
        4 * M * S ^ (2 : ℕ) * volume.real (Set.Icc a b) ≤
            (4 * M * S ^ (2 : ℕ)) * (4 * M * S ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hfactor hbase0
        _ = (4 * M * S ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
    have hδsq : (δ ^ (-(3 / 2 : ℝ))) ^ (2 : ℕ) = δ ^ (-3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hδ_pos.le]
      norm_num
    have hC : C_gowersDifferencing (Set.Icc a b) (Set.Icc p q) ψ = 4 * S ^ (2 : ℕ) := by
      simp only [C_gowersDifferencing, S]
      ring
    calc
      volume.real (Set.Icc a b) * |(c 1)⁻¹| * K ≤
          (4 * M * S ^ (2 : ℕ) * volume.real (Set.Icc a b)) * (δ ^ (-3 : ℝ)) := hfirst
      _ ≤ (4 * M * S ^ (2 : ℕ)) ^ (2 : ℕ) * (δ ^ (-3 : ℝ)) :=
        mul_le_mul_of_nonneg_right hbase hδpow0
      _ = R ^ (2 : ℕ) := by
        rw [← hδsq]
        dsimp only [R]
        rw [hC]
        ring
  have hKnonneg : 0 ≤ K := by
    dsimp [K, kdet]
    positivity
  have hcoeffENN : ENNReal.ofReal (volume.real (Set.Icc a b)) *
      ENNReal.ofReal |(c 1)⁻¹| * ENNReal.ofReal K ≤ (ENNReal.ofReal R) ^ (2 : ℕ) := by
    calc
      ENNReal.ofReal (volume.real (Set.Icc a b)) *
          ENNReal.ofReal |(c 1)⁻¹| * ENNReal.ofReal K =
          ENNReal.ofReal (volume.real (Set.Icc a b) * |(c 1)⁻¹| * K) := by
            rw [← ENNReal.ofReal_mul MeasureTheory.measureReal_nonneg,
              ← ENNReal.ofReal_mul
                (mul_nonneg MeasureTheory.measureReal_nonneg (abs_nonneg _))]
      _ ≤ ENNReal.ofReal (R ^ (2 : ℕ)) := ENNReal.ofReal_le_ofReal hcoeffReal
      _ = (ENNReal.ofReal R) ^ (2 : ℕ) := by rw [ENNReal.ofReal_pow hRnonneg]
  rw [hT]
  apply aux_gowers_ennreal_le_of_sq_le
  calc
    (ENNReal.ofReal ‖T‖) ^ (2 : ℕ) ≤
        ENNReal.ofReal (volume.real (Set.Icc a b)) * ENNReal.ofReal |(c 1)⁻¹| *
          ENNReal.ofReal K * (uNorm 3 (gL 1)) ^ (2 : ℝ) := hbridge
    _ ≤ (ENNReal.ofReal R) ^ (2 : ℕ) * (uNorm 3 (gL 1)) ^ (2 : ℝ) := by
      exact mul_le_mul_of_nonneg_right hcoeffENN bot_le
    _ = (ENNReal.ofReal R * uNorm 3 (gL 1)) ^ (2 : ℕ) := by
      rw [show (uNorm 3 (gL 1)) ^ (2 : ℝ) = (uNorm 3 (gL 1)) ^ (2 : ℕ) by
        exact ENNReal.rpow_natCast _ 2]
      rw [mul_pow]
    _ = (ENNReal.ofReal
        (C_gowersDifferencing (Set.Icc a b) (Set.Icc p q) ψ * M *
          δ ^ (-(3 / 2 : ℝ))) * uNorm 3 (g 1)) ^ (2 : ℕ) := by
      rfl


/--
Let $E\subset\R$ be measurable and suppose $|E|\geq m$ with $0<m\leq1$. Then there
exists $h\in E$ such that the four numbers
\[
0,\quad -2h,\quad 1,\quad 1-2h
\]
are pairwise separated by at least $2^{-2}m$.
-/
theorem separationSelection
    (E : Set ℝ) (hE_measurable : MeasurableSet E)
    (m : ℝ) (hm_pos : 0 < m) (hm_le_one : m ≤ 1)
    (hE_measure : ENNReal.ofReal m ≤ volume E) :
    ∃ h ∈ E, ∀ i j : Fin 4, i ≠ j →
      m / 4 ≤
        |(![0, -2 * h, 1, 1 - 2 * h] i : ℝ) -
          (![0, -2 * h, 1, 1 - 2 * h] j : ℝ)| := by
  have _hE := hE_measurable
  let B₀ : Set ℝ := Set.Ioo (-(m / 8)) (m / 8)
  let B₁ : Set ℝ := Set.Ioo ((1 - m / 4) / 2) ((1 + m / 4) / 2)
  let B₂ : Set ℝ := Set.Ioo (-(1 + m / 4) / 2) (-(1 - m / 4) / 2)
  let U : Set ℝ := (B₀ ∪ B₁) ∪ B₂
  have hB₀ : volume B₀ = ENNReal.ofReal (m / 4) := by
    change volume (Set.Ioo (-(m / 8)) (m / 8)) = ENNReal.ofReal (m / 4)
    rw [Real.volume_Ioo]
    congr 1
    ring
  have hB₁ : volume B₁ = ENNReal.ofReal (m / 4) := by
    change volume (Set.Ioo ((1 - m / 4) / 2) ((1 + m / 4) / 2)) = ENNReal.ofReal (m / 4)
    rw [Real.volume_Ioo]
    congr 1
    ring
  have hB₂ : volume B₂ = ENNReal.ofReal (m / 4) := by
    change volume (Set.Ioo (-(1 + m / 4) / 2) (-(1 - m / 4) / 2)) = ENNReal.ofReal (m / 4)
    rw [Real.volume_Ioo]
    congr 1
    ring
  have hm4 : 0 ≤ m / 4 := by positivity
  have hUle : volume U ≤ ENNReal.ofReal (3 * m / 4) := by
    calc
      volume U = volume ((B₀ ∪ B₁) ∪ B₂) := rfl
      _ ≤ volume (B₀ ∪ B₁) + volume B₂ := measure_union_le _ _
      _ ≤ (volume B₀ + volume B₁) + volume B₂ := by
        exact add_le_add (measure_union_le _ _) le_rfl
      _ = ENNReal.ofReal (3 * m / 4) := by
        rw [hB₀, hB₁, hB₂]
        rw [← ENNReal.ofReal_add hm4 hm4]
        rw [← ENNReal.ofReal_add (by positivity) hm4]
        congr 1
        ring
  have hmstrict : 3 * m / 4 < m := by nlinarith
  have hUstrict : volume U < ENNReal.ofReal m := by
    exact hUle.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hm_pos).mpr hmstrict)
  have hnotEU : ¬ E ⊆ U := by
    intro hEU
    have hEUmeasure : ENNReal.ofReal m ≤ volume U :=
      hE_measure.trans (measure_mono hEU)
    exact (not_le_of_gt hUstrict) hEUmeasure
  rcases Set.not_subset.mp hnotEU with ⟨h, hhE, hhU⟩
  have hhB₀ : h ∉ B₀ := fun hh ↦ hhU (Or.inl (Or.inl hh))
  have hhB₁ : h ∉ B₁ := fun hh ↦ hhU (Or.inl (Or.inr hh))
  have hhB₂ : h ∉ B₂ := fun hh ↦ hhU (Or.inr hh)
  have hzero : m / 4 ≤ |2 * h| := by
    by_contra hbad
    have hlt : |2 * h| < m / 4 := lt_of_not_ge hbad
    apply hhB₀
    change -(m / 8) < h ∧ h < m / 8
    rw [abs_lt] at hlt
    constructor <;> nlinarith [hlt.1, hlt.2]
  have hminus : m / 4 ≤ |1 - 2 * h| := by
    by_contra hbad
    have hlt : |1 - 2 * h| < m / 4 := lt_of_not_ge hbad
    apply hhB₁
    change (1 - m / 4) / 2 < h ∧ h < (1 + m / 4) / 2
    rw [abs_lt] at hlt
    constructor <;> nlinarith [hlt.1, hlt.2]
  have hplus : m / 4 ≤ |1 + 2 * h| := by
    by_contra hbad
    have hlt : |1 + 2 * h| < m / 4 := lt_of_not_ge hbad
    apply hhB₂
    change -(1 + m / 4) / 2 < h ∧ h < -(1 - m / 4) / 2
    rw [abs_lt] at hlt
    constructor <;> nlinarith [hlt.1, hlt.2]
  have hone : m / 4 ≤ (1 : ℝ) := by nlinarith
  refine ⟨h, hhE, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [abs_sub_comm]


/-- Almost-everywhere equality of inputs propagates to their multiplicative
differences. -/
lemma aux_u3_multiplicativeDifference_congr_ae
    (f g : ℝ → ℂ) (hfg : f =ᵐ[volume] g) (h : ℝ) :
    multiplicativeDifference h f =ᵐ[volume] multiplicativeDifference h g := by
  have hshift : (fun x : ℝ ↦ f (x + h)) =ᵐ[volume] fun x ↦ g (x + h) := by
    exact (measurePreserving_add_right volume h).quasiMeasurePreserving.tendsto_ae.eventually hfg
  filter_upwards [hfg, hshift] with x hx hxshift
  simp only [multiplicativeDifference, hx, hxshift]

/-- The `u^3` seminorm is invariant under equality almost everywhere. -/
lemma aux_u3_uNorm_three_congr_ae
    (f g : ℝ → ℂ) (hfg : f =ᵐ[volume] g) : uNorm 3 f = uNorm 3 g := by
  rw [aux_uNorm_three_eq_real_parameter, aux_uNorm_three_eq_real_parameter]
  congr 1
  apply lintegral_congr_ae
  filter_upwards with h
  apply eLpNorm_congr_ae
  apply Filter.Eventually.of_forall
  intro ξ
  exact Real.fourier_congr_ae (aux_u3_multiplicativeDifference_congr_ae f g hfg h) ξ

/-- Restricting a function to a set on which it is already supported does
not change it almost everywhere. -/
lemma aux_u3_restrict_eq_ae_of_ae_zero_outside
    (B : Set ℝ) (f : ℝ → ℂ)
    (hf : ∀ᵐ x ∂volume, x ∉ B → f x = 0) :
    aux_gowersRestrict B f =ᵐ[volume] f := by
  filter_upwards [hf] with x hx
  by_cases hB : x ∈ B
  · rw [aux_gowersRestrict, Set.indicator_of_mem hB]
  · rw [aux_gowersRestrict, Set.indicator_of_notMem hB, hx hB]

/-- The time kernel after the preliminary change `y = x + t²` in the
first Cauchy--Schwarz step of `u3Control`. -/
def aux_u3_kernel (f₀ f₁ : ℝ → ℂ) (χ : ℝ → ℝ) : ℝ → ℝ → ℂ :=
  fun y t ↦ f₀ (y - t ^ 2) * f₁ (y - t ^ 2 + t) * (χ t : ℂ)

/-- Its compact spatial range when the first factor is supported in `A` and
the time cutoff in `J`. -/
def aux_u3_spatialRange (A J : Set ℝ) : Set ℝ :=
  Set.image2 (fun x t : ℝ ↦ x + t ^ 2) A J

/-- The nonlinear coordinate `y - t²` is quasi-measure-preserving. -/
lemma aux_u3_qmp_sub_sq :
    Measure.QuasiMeasurePreserving (fun z : ℝ × ℝ ↦ z.1 - z.2 ^ 2)
      (volume.prod volume) volume := by
  refine QuasiMeasurePreserving.prod_of_left (by fun_prop)
    (Filter.Eventually.of_forall fun t ↦ ?_)
  simpa only [sub_eq_add_neg] using
    (measurePreserving_add_right volume (-(t ^ 2))).quasiMeasurePreserving

/-- The nonlinear coordinate `y - t² + t` is quasi-measure-preserving. -/
lemma aux_u3_qmp_sub_sq_add :
    Measure.QuasiMeasurePreserving (fun z : ℝ × ℝ ↦ z.1 - z.2 ^ 2 + z.2)
      (volume.prod volume) volume := by
  refine QuasiMeasurePreserving.prod_of_left (by fun_prop)
    (Filter.Eventually.of_forall fun t ↦ ?_)
  convert (measurePreserving_add_right volume (-(t ^ 2) + t)).quasiMeasurePreserving using 1
  funext x
  ring

/-- Almost-everywhere strong measurability of the preliminary time kernel. -/
lemma aux_u3_kernel_aestronglyMeasurable
    (f₀ f₁ : ℝ → ℂ) (χ : ℝ → ℝ)
    (hf₀ : AEStronglyMeasurable f₀ volume)
    (hf₁ : AEStronglyMeasurable f₁ volume) (hχ : Continuous χ) :
    AEStronglyMeasurable (Function.uncurry (aux_u3_kernel f₀ f₁ χ))
      (volume.prod volume) := by
  have h0 : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ f₀ (z.1 - z.2 ^ 2))
      (volume.prod volume) := by
    change AEStronglyMeasurable (f₀ ∘ fun z : ℝ × ℝ ↦ z.1 - z.2 ^ 2)
      (volume.prod volume)
    exact hf₀.comp_quasiMeasurePreserving aux_u3_qmp_sub_sq
  have h1 : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ f₁ (z.1 - z.2 ^ 2 + z.2))
      (volume.prod volume) := by
    change AEStronglyMeasurable (f₁ ∘ fun z : ℝ × ℝ ↦ z.1 - z.2 ^ 2 + z.2)
      (volume.prod volume)
    exact hf₁.comp_quasiMeasurePreserving aux_u3_qmp_sub_sq_add
  have hχ' : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ (χ z.2 : ℂ))
      (volume.prod volume) :=
    (Complex.continuous_ofReal.comp (hχ.comp continuous_snd)).aestronglyMeasurable
  exact h0.mul h1 |>.mul hχ'

/-- A one-bounded input gives a one-bounded preliminary time kernel. -/
lemma aux_u3_kernel_ae_one_bounded
    (f₀ f₁ : ℝ → ℂ) (χ : ℝ → ℝ)
    (hf₀ : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₁ : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hχ₀ : ∀ t : ℝ, 0 ≤ χ t) (hχ₁ : ∀ t : ℝ, χ t ≤ 1) :
    ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖aux_u3_kernel f₀ f₁ χ z.1 z.2‖ ≤ 1 := by
  have h0 := aux_u3_qmp_sub_sq.tendsto_ae hf₀
  have h1 := aux_u3_qmp_sub_sq_add.tendsto_ae hf₁
  filter_upwards [h0, h1] with z hz0 hz1
  change ‖f₀ (z.1 - z.2 ^ 2)‖ ≤ 1 at hz0
  change ‖f₁ (z.1 - z.2 ^ 2 + z.2)‖ ≤ 1 at hz1
  rw [aux_u3_kernel, norm_mul, norm_mul]
  have hχnorm : ‖(χ z.2 : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ₀ _)]
    exact hχ₁ _
  calc
    ‖f₀ (z.1 - z.2 ^ 2)‖ * ‖f₁ (z.1 - z.2 ^ 2 + z.2)‖ * ‖(χ z.2 : ℂ)‖ ≤
        1 * 1 * 1 := by gcongr
    _ = 1 := by norm_num

/-- The spatial range of the preliminary kernel is compact. -/
lemma aux_u3_spatialRange_compact (A J : Set ℝ)
    (hA : IsCompact A) (hJ : IsCompact J) :
    IsCompact (aux_u3_spatialRange A J) := by
  rw [aux_u3_spatialRange, ← Set.image_prod]
  exact (hA.prod hJ).image (continuous_fst.add (continuous_snd.pow 2))

/-- The preliminary kernel vanishes outside its compact spatial-time box. -/
lemma aux_u3_kernel_zero_outside
    (A J : Set ℝ) (f₀ f₁ : ℝ → ℂ) (χ : ℝ → ℝ)
    (hf₀ : ∀ x : ℝ, x ∉ A → f₀ x = 0) (hχ : tsupport χ ⊆ J) :
    ∀ z : ℝ × ℝ, z ∉ aux_u3_spatialRange A J ×ˢ J →
      aux_u3_kernel f₀ f₁ χ z.1 z.2 = 0 := by
  intro z hz
  by_cases ht : z.2 ∈ J
  · have hy : z.1 ∉ aux_u3_spatialRange A J := by
      intro hy
      exact hz ⟨hy, ht⟩
    have hx : z.1 - z.2 ^ 2 ∉ A := by
      intro hx
      apply hy
      rw [aux_u3_spatialRange]
      exact ⟨z.1 - z.2 ^ 2, hx, z.2, ht, by ring⟩
    simp [aux_u3_kernel, hf₀ _ hx]
  · have hnot : z.2 ∉ tsupport χ := fun hz' ↦ ht (hχ hz')
    have hzero : χ z.2 = 0 := image_eq_zero_of_notMem_tsupport hnot
    simp [aux_u3_kernel, hzero]

/-- The shear `(x,t) ↦ (x - t²,t)` preserves product Lebesgue measure. -/
lemma aux_u3_measurePreserving_sub_sq_prod :
    MeasurePreserving (fun z : ℝ × ℝ ↦ (z.1 - z.2 ^ 2, z.2))
      (volume.prod volume) (volume.prod volume) := by
  let shear : ℝ × ℝ → ℝ × ℝ := fun z ↦ (z.1, z.2 - z.1 ^ 2)
  have hshear : MeasurePreserving shear (volume.prod volume) (volume.prod volume) := by
    refine MeasurePreserving.skew_product (g := fun t x : ℝ ↦ x - t ^ 2)
      (MeasurePreserving.id (α := ℝ) volume) ?_ ?_
    · fun_prop
    · filter_upwards with t
      simpa only [sub_eq_add_neg] using
        (measurePreserving_add_right volume (-(t ^ 2))).map_eq
  have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ)
      (volume.prod volume) (volume.prod volume) := Measure.measurePreserving_swap
  apply (hswap.comp (hshear.comp hswap)).congr
  · fun_prop
  · filter_upwards with z
    rcases z with ⟨x, t⟩
    simp [shear]

/-- Integration is invariant under the shear `(x,t) ↦ (x - t²,t)`. -/
lemma aux_u3_integral_shear_sub_sq
    (F : ℝ → ℝ → ℂ) (hF : Integrable (Function.uncurry F) (volume.prod volume)) :
    (∫ x : ℝ, ∫ t : ℝ, F (x - t ^ 2) t) = ∫ x : ℝ, ∫ t : ℝ, F x t := by
  have hG : Integrable
      (Function.uncurry fun x t : ℝ ↦ F (x - t ^ 2) t) (volume.prod volume) := by
    change Integrable ((Function.uncurry F) ∘ fun z : ℝ × ℝ ↦ (z.1 - z.2 ^ 2, z.2))
      (volume.prod volume)
    rw [← memLp_one_iff_integrable] at hF ⊢
    exact hF.comp_measurePreserving aux_u3_measurePreserving_sub_sq_prod
  calc
    (∫ x : ℝ, ∫ t : ℝ, F (x - t ^ 2) t) =
        ∫ t : ℝ, ∫ x : ℝ, F (x - t ^ 2) t := integral_integral_swap hG
    _ = ∫ t : ℝ, ∫ x : ℝ, F x t := by
      apply integral_congr_ae
      filter_upwards with t
      simpa only [sub_eq_add_neg] using
        (integral_add_right_eq_self (fun x : ℝ ↦ F x t) (-(t ^ 2)))
    _ = ∫ x : ℝ, ∫ t : ℝ, F x t := (integral_integral_swap hF).symm

/-- The shear `(x,t) ↦ (x + t²,t)` preserves product Lebesgue measure. -/
lemma aux_u3_measurePreserving_add_sq_prod :
    MeasurePreserving (fun z : ℝ × ℝ ↦ (z.1 + z.2 ^ 2, z.2))
      (volume.prod volume) (volume.prod volume) := by
  let shear : ℝ × ℝ → ℝ × ℝ := fun z ↦ (z.1, z.2 + z.1 ^ 2)
  have hshear : MeasurePreserving shear (volume.prod volume) (volume.prod volume) := by
    refine MeasurePreserving.skew_product (g := fun t x : ℝ ↦ x + t ^ 2)
      (MeasurePreserving.id (α := ℝ) volume) ?_ ?_
    · fun_prop
    · filter_upwards with t
      exact (measurePreserving_add_right volume (t ^ 2)).map_eq
  have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ)
      (volume.prod volume) (volume.prod volume) := Measure.measurePreserving_swap
  apply (hswap.comp (hshear.comp hswap)).congr
  · fun_prop
  · filter_upwards with z
    rcases z with ⟨x, t⟩
    simp [shear]

/-- Integration is invariant under the shear `(x,t) ↦ (x + t²,t)`. -/
lemma aux_u3_integral_shear_add_sq
    (F : ℝ → ℝ → ℂ) (hF : Integrable (Function.uncurry F) (volume.prod volume)) :
    (∫ x : ℝ, ∫ t : ℝ, F (x + t ^ 2) t) = ∫ x : ℝ, ∫ t : ℝ, F x t := by
  have hG : Integrable
      (Function.uncurry fun x t : ℝ ↦ F (x + t ^ 2) t) (volume.prod volume) := by
    change Integrable ((Function.uncurry F) ∘ fun z : ℝ × ℝ ↦ (z.1 + z.2 ^ 2, z.2))
      (volume.prod volume)
    rw [← memLp_one_iff_integrable] at hF ⊢
    exact hF.comp_measurePreserving aux_u3_measurePreserving_add_sq_prod
  calc
    (∫ x : ℝ, ∫ t : ℝ, F (x + t ^ 2) t) =
        ∫ t : ℝ, ∫ x : ℝ, F (x + t ^ 2) t := integral_integral_swap hG
    _ = ∫ t : ℝ, ∫ x : ℝ, F x t := by
      apply integral_congr_ae
      filter_upwards with t
      simpa only using (integral_add_right_eq_self (fun x : ℝ ↦ F x t) (t ^ 2))
    _ = ∫ x : ℝ, ∫ t : ℝ, F x t := (integral_integral_swap hF).symm

/-- Pointwise expansion of the autocorrelation after the quadratic shear. -/
lemma aux_u3_kernel_correlation_shear_pointwise
    (f₀ f₁ : ℝ → ℂ) (χ : ℝ → ℝ) (h x t : ℝ) :
    aux_u3_kernel f₀ f₁ χ (x + t ^ 2) t *
        starRingEnd ℂ (aux_u3_kernel f₀ f₁ χ (x + t ^ 2) (t + h)) =
      f₀ x * f₁ (x + t) *
        starRingEnd ℂ (f₀ (x - 2 * h * t - h ^ 2)) *
        starRingEnd ℂ (f₁ (x + (1 - 2 * h) * t + h - h ^ 2)) *
        ((χ t * χ (t + h) : ℝ) : ℂ) := by
  have h00 : x + t ^ 2 - t ^ 2 = x := by ring
  have h01 : x + t ^ 2 - (t + h) ^ 2 = x - 2 * h * t - h ^ 2 := by ring
  have h11 : x + t ^ 2 - (t + h) ^ 2 + (t + h) =
      x + (1 - 2 * h) * t + h - h ^ 2 := by ring
  have h11' : x - 2 * h * t - h ^ 2 + (t + h) =
      x + (1 - 2 * h) * t + h - h ^ 2 := by ring
  simp only [aux_u3_kernel]
  simp only [h00, h01, h11']
  simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
  ring

/-- The quadratic shear rewrites the kernel autocorrelation as the
four-factor correlation used below. -/
lemma aux_u3_kernel_correlation_change
    (f₀ f₁ : ℝ → ℂ) (χ : ℝ → ℝ) (h : ℝ)
    (hF : Integrable
      (Function.uncurry fun y t : ℝ ↦
        aux_u3_kernel f₀ f₁ χ y t *
          starRingEnd ℂ (aux_u3_kernel f₀ f₁ χ y (t + h)))
      (volume.prod volume)) :
    (∫ y : ℝ, ∫ t : ℝ,
      aux_u3_kernel f₀ f₁ χ y t *
        starRingEnd ℂ (aux_u3_kernel f₀ f₁ χ y (t + h))) =
      ∫ x : ℝ, ∫ t : ℝ,
        f₀ x * f₁ (x + t) *
          starRingEnd ℂ (f₀ (x - 2 * h * t - h ^ 2)) *
          starRingEnd ℂ (f₁ (x + (1 - 2 * h) * t + h - h ^ 2)) *
          ((χ t * χ (t + h) : ℝ) : ℂ) := by
  let F : ℝ → ℝ → ℂ := fun y t ↦
    aux_u3_kernel f₀ f₁ χ y t *
      starRingEnd ℂ (aux_u3_kernel f₀ f₁ χ y (t + h))
  have hshear : (∫ x : ℝ, ∫ t : ℝ, F (x + t ^ 2) t) =
      ∫ y : ℝ, ∫ t : ℝ, F y t := by
    apply aux_u3_integral_shear_add_sq F
    simpa only [F] using hF
  calc
    (∫ y : ℝ, ∫ t : ℝ,
      aux_u3_kernel f₀ f₁ χ y t *
        starRingEnd ℂ (aux_u3_kernel f₀ f₁ χ y (t + h))) =
        ∫ x : ℝ, ∫ t : ℝ, F (x + t ^ 2) t := by
          simpa only [F] using hshear.symm
    _ = ∫ x : ℝ, ∫ t : ℝ,
        f₀ x * f₁ (x + t) *
          starRingEnd ℂ (f₀ (x - 2 * h * t - h ^ 2)) *
          starRingEnd ℂ (f₁ (x + (1 - 2 * h) * t + h - h ^ 2)) *
          ((χ t * χ (t + h) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      apply integral_congr_ae
      filter_upwards with t
      exact aux_u3_kernel_correlation_shear_pointwise f₀ f₁ χ h x t

/-- The first Cauchy--Schwarz/autocorrelation reduction in the proof of
`u3Control`, after `y = x + t²`.  The first input is pointwise supported so
the time kernel has a compact spatial box. -/
lemma aux_u3_first_cauchy_energy
    (A C J : Set ℝ) (hA : IsCompact A) (hC : IsCompact C) (hJ : IsCompact J)
    (f₀ f₁ f₂ : ℝ → ℂ) (χ : ℝ → ℝ)
    (hf₀meas : AEStronglyMeasurable f₀ volume)
    (hf₁meas : AEStronglyMeasurable f₁ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₀bound : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₁bound : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₀support : ∀ x : ℝ, x ∉ A → f₀ x = 0)
    (hf₂support : ∀ᵐ x ∂volume, x ∉ C → f₂ x = 0)
    (hχcont : Continuous χ) (hχ₀ : ∀ t : ℝ, 0 ≤ χ t)
    (hχ₁ : ∀ t : ℝ, χ t ≤ 1) (hχsupport : tsupport χ ⊆ J) :
    ‖∫ y : ℝ, f₂ y * ∫ t : ℝ, aux_u3_kernel f₀ f₁ χ y t‖ ^ (2 : ℕ) ≤
      volume.real C * ∫ h : ℝ, ‖∫ x : ℝ, ∫ t : ℝ,
        f₀ x * f₁ (x + t) *
          starRingEnd ℂ (f₀ (x - 2 * h * t - h ^ 2)) *
          starRingEnd ℂ (f₁ (x + (1 - 2 * h) * t + h - h ^ 2)) *
          ((χ t * χ (t + h) : ℝ) : ℂ)‖ := by
  let X : Set ℝ := aux_u3_spatialRange A J
  let Q : ℝ → ℝ → ℂ := aux_u3_kernel f₀ f₁ χ
  have hX : IsCompact X := by
    simpa only [X] using aux_u3_spatialRange_compact A J hA hJ
  have hQmeas : AEStronglyMeasurable (Function.uncurry Q) (volume.prod volume) := by
    simpa only [Q] using aux_u3_kernel_aestronglyMeasurable f₀ f₁ χ
      hf₀meas hf₁meas hχcont
  have hQbound : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖Q z.1 z.2‖ ≤ 1 := by
    simpa only [Q] using aux_u3_kernel_ae_one_bounded f₀ f₁ χ
      hf₀bound hf₁bound hχ₀ hχ₁
  have hQsupport : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∉ X ×ˢ J → Q z.1 z.2 = 0 := by
    filter_upwards with z
    simpa only [X, Q] using aux_u3_kernel_zero_outside A J f₀ f₁ χ hf₀support hχsupport z
  have hf₂L2 : MemLp f₂ (2 : ℝ≥0∞) volume := by
    exact aux_memLp_of_ae_bound_of_ae_support f₂ hf₂meas 1 hf₂bound C
      hC.isClosed.measurableSet hC.measure_lt_top hf₂support 2
  have houter := aux_outer_cauchy_sq_le_autocorrelation_compactSupport
    C X J hC hX hJ f₂ hf₂L2 hf₂bound hf₂support Q hQmeas hQbound hQsupport
  have hR := aux_autocorrelation_integrable_compactSupport X J hX hJ Q
    hQmeas hQbound hQsupport
  have hsections := aux_autocorrelation_section_integrable_ae Q hR
  have hcoord : (fun h : ℝ ↦ ∫ y : ℝ, ∫ t : ℝ,
      Q y t * starRingEnd ℂ (Q y (t + h))) =ᵐ[volume]
      (fun h ↦ ∫ x : ℝ, ∫ t : ℝ,
        f₀ x * f₁ (x + t) *
          starRingEnd ℂ (f₀ (x - 2 * h * t - h ^ 2)) *
          starRingEnd ℂ (f₁ (x + (1 - 2 * h) * t + h - h ^ 2)) *
          ((χ t * χ (t + h) : ℝ) : ℂ)) := by
    filter_upwards [hsections] with h hh
    simpa only [Q] using aux_u3_kernel_correlation_change f₀ f₁ χ h hh
  calc
    ‖∫ y : ℝ, f₂ y * ∫ t : ℝ, aux_u3_kernel f₀ f₁ χ y t‖ ^ (2 : ℕ) =
        ‖∫ y : ℝ, f₂ y * ∫ t : ℝ, Q y t‖ ^ (2 : ℕ) := by rfl
    _ ≤ volume.real C * ∫ h : ℝ, ‖∫ y : ℝ, ∫ t : ℝ,
        Q y t * starRingEnd ℂ (Q y (t + h))‖ := houter
    _ = volume.real C * ∫ h : ℝ, ‖∫ x : ℝ, ∫ t : ℝ,
        f₀ x * f₁ (x + t) *
          starRingEnd ℂ (f₀ (x - 2 * h * t - h ^ 2)) *
          starRingEnd ℂ (f₁ (x + (1 - 2 * h) * t + h - h ^ 2)) *
          ((χ t * χ (t + h) : ℝ) : ℂ)‖ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hcoord] with h hh
      rw [hh]

/-- The original trilinear integrand, viewed on the product space. -/
def aux_u3_trilinearIntegrand (f₀ f₁ f₂ : ℝ → ℂ) (χ : ℝ → ℝ) :
    ℝ × ℝ → ℂ :=
  fun z ↦ f₀ z.1 * f₁ (z.1 + z.2) * f₂ (z.1 + z.2 ^ 2) * (χ z.2 : ℂ)

/-- The coordinate `(x,t) ↦ x + t²` is quasi-measure-preserving. -/
lemma aux_u3_qmp_add_sq :
    Measure.QuasiMeasurePreserving (fun z : ℝ × ℝ ↦ z.1 + z.2 ^ 2)
      (volume.prod volume) volume := by
  refine QuasiMeasurePreserving.prod_of_left (by fun_prop)
    (Filter.Eventually.of_forall fun t ↦ ?_)
  exact (measurePreserving_add_right volume (t ^ 2)).quasiMeasurePreserving

/-- Almost-everywhere strong measurability of the original trilinear
integrand. -/
lemma aux_u3_trilinearIntegrand_aestronglyMeasurable
    (f₀ f₁ f₂ : ℝ → ℂ) (χ : ℝ → ℝ)
    (hf₀ : AEStronglyMeasurable f₀ volume)
    (hf₁ : AEStronglyMeasurable f₁ volume)
    (hf₂ : AEStronglyMeasurable f₂ volume) (hχ : Continuous χ) :
    AEStronglyMeasurable (aux_u3_trilinearIntegrand f₀ f₁ f₂ χ)
      (volume.prod volume) := by
  have h0 : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ f₀ z.1)
      (volume.prod volume) := by
    change AEStronglyMeasurable (f₀ ∘ fun z : ℝ × ℝ ↦ z.1) (volume.prod volume)
    exact hf₀.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_fst
      (μ := volume) (ν := volume))
  have h1 : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ f₁ (z.1 + z.2))
      (volume.prod volume) := by
    change AEStronglyMeasurable (f₁ ∘ fun z : ℝ × ℝ ↦ z.1 + z.2) (volume.prod volume)
    have h1' := hf₁.comp_quasiMeasurePreserving (aux_quasiMeasurePreserving_affine 1)
    simpa only [Function.comp_apply, one_mul] using h1'
  have h2 : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ f₂ (z.1 + z.2 ^ 2))
      (volume.prod volume) := by
    change AEStronglyMeasurable (f₂ ∘ fun z : ℝ × ℝ ↦ z.1 + z.2 ^ 2)
      (volume.prod volume)
    exact hf₂.comp_quasiMeasurePreserving aux_u3_qmp_add_sq
  have hχ' : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ (χ z.2 : ℂ))
      (volume.prod volume) :=
    (Complex.continuous_ofReal.comp (hχ.comp continuous_snd)).aestronglyMeasurable
  exact h0.mul h1 |>.mul h2 |>.mul hχ'

/-- A one-bounded trilinear integrand is one-bounded on the product space. -/
lemma aux_u3_trilinearIntegrand_ae_one_bounded
    (f₀ f₁ f₂ : ℝ → ℂ) (χ : ℝ → ℝ)
    (hf₀ : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₁ : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₂ : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hχ₀ : ∀ t : ℝ, 0 ≤ χ t) (hχ₁ : ∀ t : ℝ, χ t ≤ 1) :
    ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      ‖aux_u3_trilinearIntegrand f₀ f₁ f₂ χ z‖ ≤ 1 := by
  have h0 : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖f₀ z.1‖ ≤ 1 := by
    exact (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).tendsto_ae hf₀
  have h1' : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖f₁ (z.1 + 1 * z.2)‖ ≤ 1 := by
    exact (aux_quasiMeasurePreserving_affine 1).tendsto_ae hf₁
  have h1 : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖f₁ (z.1 + z.2)‖ ≤ 1 := by
    simpa only [one_mul] using h1'
  have h2 : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖f₂ (z.1 + z.2 ^ 2)‖ ≤ 1 := by
    exact aux_u3_qmp_add_sq.tendsto_ae hf₂
  filter_upwards [h0, h1, h2] with z hz0 hz1 hz2
  change ‖f₀ z.1‖ ≤ 1 at hz0
  change ‖f₁ (z.1 + z.2)‖ ≤ 1 at hz1
  change ‖f₂ (z.1 + z.2 ^ 2)‖ ≤ 1 at hz2
  rw [aux_u3_trilinearIntegrand, norm_mul, norm_mul, norm_mul]
  have hχnorm : ‖(χ z.2 : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ₀ _)]
    exact hχ₁ _
  calc
    ‖f₀ z.1‖ * ‖f₁ (z.1 + z.2)‖ * ‖f₂ (z.1 + z.2 ^ 2)‖ * ‖(χ z.2 : ℂ)‖ ≤
        1 * 1 * 1 * 1 := by gcongr
    _ = 1 := by norm_num

/-- The original trilinear integrand vanishes outside `A × J`. -/
lemma aux_u3_trilinearIntegrand_zero_outside
    (A J : Set ℝ) (f₀ f₁ f₂ : ℝ → ℂ) (χ : ℝ → ℝ)
    (hf₀ : ∀ x : ℝ, x ∉ A → f₀ x = 0) (hχ : tsupport χ ⊆ J) :
    ∀ z : ℝ × ℝ, z ∉ A ×ˢ J → aux_u3_trilinearIntegrand f₀ f₁ f₂ χ z = 0 := by
  intro z hz
  by_cases hx : z.1 ∈ A
  · have ht : z.2 ∉ J := by
      intro ht
      exact hz ⟨hx, ht⟩
    have hnot : z.2 ∉ tsupport χ := fun hz' ↦ ht (hχ hz')
    have hzero : χ z.2 = 0 := image_eq_zero_of_notMem_tsupport hnot
    simp [aux_u3_trilinearIntegrand, hzero]
  · simp [aux_u3_trilinearIntegrand, hf₀ _ hx]

/-- Compact support and one-boundedness make the original trilinear
integrand integrable. -/
lemma aux_u3_trilinearIntegrand_integrable
    (A J : Set ℝ) (hA : IsCompact A) (hJ : IsCompact J)
    (f₀ f₁ f₂ : ℝ → ℂ) (χ : ℝ → ℝ)
    (hf₀meas : AEStronglyMeasurable f₀ volume)
    (hf₁meas : AEStronglyMeasurable f₁ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₀bound : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₁bound : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₀support : ∀ x : ℝ, x ∉ A → f₀ x = 0)
    (hχcont : Continuous χ) (hχ₀ : ∀ t : ℝ, 0 ≤ χ t)
    (hχ₁ : ∀ t : ℝ, χ t ≤ 1) (hχsupport : tsupport χ ⊆ J) :
    Integrable (aux_u3_trilinearIntegrand f₀ f₁ f₂ χ) (volume.prod volume) := by
  rw [← memLp_one_iff_integrable]
  apply aux_memLp_of_ae_bound_of_ae_support
    (aux_u3_trilinearIntegrand f₀ f₁ f₂ χ)
    (aux_u3_trilinearIntegrand_aestronglyMeasurable f₀ f₁ f₂ χ
      hf₀meas hf₁meas hf₂meas hχcont)
    1 (aux_u3_trilinearIntegrand_ae_one_bounded f₀ f₁ f₂ χ
      hf₀bound hf₁bound hf₂bound hχ₀ hχ₁)
    (A ×ˢ J) (hA.isClosed.measurableSet.prod hJ.isClosed.measurableSet)
    (hA.prod hJ).measure_lt_top
    (Filter.Eventually.of_forall
      (aux_u3_trilinearIntegrand_zero_outside A J f₀ f₁ f₂ χ hf₀support hχsupport)) 1

/-- The preliminary quadratic shear identifies the original trilinear form
with the outer pairing of the time kernel. -/
lemma aux_u3_trilinearForm_eq_u3Outer
    (A J : Set ℝ) (hA : IsCompact A) (hJ : IsCompact J)
    (f₀ f₁ f₂ : ℝ → ℂ) (χ : ℝ → ℝ)
    (hf₀meas : AEStronglyMeasurable f₀ volume)
    (hf₁meas : AEStronglyMeasurable f₁ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₀bound : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₁bound : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₀support : ∀ x : ℝ, x ∉ A → f₀ x = 0)
    (hχcont : Continuous χ) (hχ₀ : ∀ t : ℝ, 0 ≤ χ t)
    (hχ₁ : ∀ t : ℝ, χ t ≤ 1) (hχsupport : tsupport χ ⊆ J) :
    trilinearForm χ f₀ f₁ f₂ =
      ∫ y : ℝ, f₂ y * ∫ t : ℝ, aux_u3_kernel f₀ f₁ χ y t := by
  let P : ℝ → ℝ → ℂ := fun x t ↦ aux_u3_trilinearIntegrand f₀ f₁ f₂ χ (x, t)
  have hP : Integrable (Function.uncurry P) (volume.prod volume) := by
    change Integrable (aux_u3_trilinearIntegrand f₀ f₁ f₂ χ) (volume.prod volume)
    exact aux_u3_trilinearIntegrand_integrable A J hA hJ f₀ f₁ f₂ χ
      hf₀meas hf₁meas hf₂meas hf₀bound hf₁bound hf₂bound hf₀support
      hχcont hχ₀ hχ₁ hχsupport
  have hshear := aux_u3_integral_shear_sub_sq P hP
  calc
    trilinearForm χ f₀ f₁ f₂ = ∫ x : ℝ, ∫ t : ℝ, P x t := by rfl
    _ = ∫ y : ℝ, ∫ t : ℝ, P (y - t ^ 2) t := hshear.symm
    _ = ∫ y : ℝ, ∫ t : ℝ,
        f₂ y * aux_u3_kernel f₀ f₁ χ y t := by
      apply integral_congr_ae
      filter_upwards with y
      apply integral_congr_ae
      filter_upwards with t
      simp only [P, aux_u3_kernel]
      have h₁ : y - t ^ 2 + t = y + t - t ^ 2 := by ring
      have h₂ : y - t ^ 2 + t ^ 2 = y := by ring
      simp only [aux_u3_trilinearIntegrand, h₁, h₂]
      ring
    _ = ∫ y : ℝ, f₂ y * ∫ t : ℝ, aux_u3_kernel f₀ f₁ χ y t := by
      apply integral_congr_ae
      filter_upwards with y
      rw [integral_const_mul]

/-- A compact-box, unit-bound estimate for a double integral.  This gives
the uniform `I_h ≤ |A| |J|` part of the energy selection argument. -/
lemma aux_u3_norm_doubleIntegral_le_measure_product
    (A J : Set ℝ) (hA : IsCompact A) (hJ : IsCompact J)
    (F : ℝ → ℝ → ℂ)
    (hFmeas : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume))
    (hFbound : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖F z.1 z.2‖ ≤ 1)
    (hFsupp : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∉ A ×ˢ J → F z.1 z.2 = 0) :
    ‖∫ x : ℝ, ∫ t : ℝ, F x t‖ ≤ volume.real A * volume.real J := by
  let S : Set (ℝ × ℝ) := A ×ˢ J
  have hSmeas : MeasurableSet S := hA.isClosed.measurableSet.prod hJ.isClosed.measurableSet
  have hSfinite : (volume.prod volume) S < ∞ := (hA.prod hJ).measure_lt_top
  have hFmem : MemLp (Function.uncurry F) 1 (volume.prod volume) :=
    aux_memLp_of_ae_bound_of_ae_support _ hFmeas 1 hFbound S hSmeas hSfinite hFsupp 1
  have hFint : Integrable (Function.uncurry F) (volume.prod volume) :=
    memLp_one_iff_integrable.mp hFmem
  have hIndint : Integrable (S.indicator (1 : ℝ × ℝ → ℝ))
      (volume.prod volume) := by
    rw [integrable_indicator_iff hSmeas]
    exact integrableOn_const hSfinite.ne
  have hdom : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      ‖F z.1 z.2‖ ≤ S.indicator (1 : ℝ × ℝ → ℝ) z := by
    filter_upwards [hFbound, hFsupp] with z hzbound hzsupport
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem hz]
      exact hzbound
    · rw [Set.indicator_of_notMem hz]
      simp [hzsupport hz]
  have hnorm : ∫ z : ℝ × ℝ, ‖F z.1 z.2‖ ∂(volume.prod volume) ≤
      ∫ z : ℝ × ℝ, S.indicator (1 : ℝ × ℝ → ℝ) z ∂(volume.prod volume) :=
    integral_mono_ae hFint.norm hIndint hdom
  have hIndeq : ∫ z : ℝ × ℝ, S.indicator (1 : ℝ × ℝ → ℝ) z ∂(volume.prod volume) =
      volume.real A * volume.real J := by
    calc
      ∫ z : ℝ × ℝ, S.indicator (1 : ℝ × ℝ → ℝ) z ∂(volume.prod volume) =
          (volume.prod volume).real S := by
            simpa only [Measure.real] using
              (integral_indicator_one (μ := volume.prod volume) hSmeas)
      _ = volume.real A * volume.real J := by
        simp only [S, measureReal_prod_prod]
  calc
    ‖∫ x : ℝ, ∫ t : ℝ, F x t‖ = ‖∫ z : ℝ × ℝ, F z.1 z.2 ∂(volume.prod volume)‖ := by
      congr 1
      simpa only [Function.uncurry] using (integral_prod (Function.uncurry F) hFint).symm
    _ ≤ ∫ z : ℝ × ℝ, ‖F z.1 z.2‖ ∂(volume.prod volume) := norm_integral_le_integral_norm _
    _ ≤ ∫ z : ℝ × ℝ, S.indicator (1 : ℝ × ℝ → ℝ) z ∂(volume.prod volume) := hnorm
    _ = volume.real A * volume.real J := hIndeq

/-- The fixed-parameter four-factor correlation which appears after the
nonlinear shear in the first `U³` Cauchy--Schwarz step. -/
def aux_u3_correlationIntegrand (h : ℝ) (f₀ f₁ : ℝ → ℂ) (χ : ℝ → ℝ) :
    ℝ → ℝ → ℂ :=
  fun x t ↦
    f₀ x * f₁ (x + t) *
      starRingEnd ℂ (f₀ (x - 2 * h * t - h ^ 2)) *
      starRingEnd ℂ (f₁ (x + (1 - 2 * h) * t + h - h ^ 2)) *
      ((χ t * χ (t + h) : ℝ) : ℂ)

/-- An affine coordinate with an arbitrary constant translation is
quasi-measure-preserving on the product Lebesgue space.  In contrast to the
usual change-of-variables lemma, this does not need the coefficient of the
second coordinate to be nonzero, because the first coordinate is retained. -/
lemma aux_u3_qmp_affine_const (c d : ℝ) :
    Measure.QuasiMeasurePreserving
      (fun z : ℝ × ℝ ↦ z.1 + c * z.2 + d) (volume.prod volume) volume := by
  refine QuasiMeasurePreserving.prod_of_left (by fun_prop)
    (Filter.Eventually.of_forall fun t ↦ ?_)
  convert (measurePreserving_add_right volume (c * t + d)).quasiMeasurePreserving using 1
  funext x
  ring

/-- The coordinate `(x,t) ↦ x + t` is quasi-measure-preserving. -/
lemma aux_u3_qmp_add :
    Measure.QuasiMeasurePreserving (fun z : ℝ × ℝ ↦ z.1 + z.2)
      (volume.prod volume) volume := by
  convert aux_u3_qmp_affine_const 1 0 using 1
  ext z
  ring

/-- The shifted first correlation coordinate is quasi-measure-preserving. -/
lemma aux_u3_qmp_correlation_left (h : ℝ) :
    Measure.QuasiMeasurePreserving
      (fun z : ℝ × ℝ ↦ z.1 - 2 * h * z.2 - h ^ 2)
      (volume.prod volume) volume := by
  convert aux_u3_qmp_affine_const (-2 * h) (-(h ^ 2)) using 1
  ext z
  ring

/-- The shifted second correlation coordinate is quasi-measure-preserving. -/
lemma aux_u3_qmp_correlation_right (h : ℝ) :
    Measure.QuasiMeasurePreserving
      (fun z : ℝ × ℝ ↦ z.1 + (1 - 2 * h) * z.2 + h - h ^ 2)
      (volume.prod volume) volume := by
  convert aux_u3_qmp_affine_const (1 - 2 * h) (h - h ^ 2) using 1
  ext z
  ring

/-- Almost-everywhere strong measurability of a fixed correlation integrand. -/
lemma aux_u3_correlationIntegrand_aestronglyMeasurable
    (h : ℝ) (f₀ f₁ : ℝ → ℂ) (χ : ℝ → ℝ)
    (hf₀ : AEStronglyMeasurable f₀ volume)
    (hf₁ : AEStronglyMeasurable f₁ volume) (hχ : Continuous χ) :
    AEStronglyMeasurable (Function.uncurry (aux_u3_correlationIntegrand h f₀ f₁ χ))
      (volume.prod volume) := by
  have h0 : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ f₀ z.1)
      (volume.prod volume) := by
    change AEStronglyMeasurable (f₀ ∘ fun z : ℝ × ℝ ↦ z.1)
      (volume.prod volume)
    exact hf₀.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume))
  have h1 : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ f₁ (z.1 + z.2))
      (volume.prod volume) := by
    change AEStronglyMeasurable (f₁ ∘ fun z : ℝ × ℝ ↦ z.1 + z.2)
      (volume.prod volume)
    exact hf₁.comp_quasiMeasurePreserving aux_u3_qmp_add
  have h2 : AEStronglyMeasurable
      (fun z : ℝ × ℝ ↦ f₀ (z.1 - 2 * h * z.2 - h ^ 2))
      (volume.prod volume) := by
    change AEStronglyMeasurable
      (f₀ ∘ fun z : ℝ × ℝ ↦ z.1 - 2 * h * z.2 - h ^ 2) (volume.prod volume)
    exact hf₀.comp_quasiMeasurePreserving (aux_u3_qmp_correlation_left h)
  have h3 : AEStronglyMeasurable
      (fun z : ℝ × ℝ ↦ f₁ (z.1 + (1 - 2 * h) * z.2 + h - h ^ 2))
      (volume.prod volume) := by
    change AEStronglyMeasurable
      (f₁ ∘ fun z : ℝ × ℝ ↦ z.1 + (1 - 2 * h) * z.2 + h - h ^ 2)
      (volume.prod volume)
    exact hf₁.comp_quasiMeasurePreserving (aux_u3_qmp_correlation_right h)
  have hχ' : AEStronglyMeasurable
      (fun z : ℝ × ℝ ↦ ((χ z.2 * χ (z.2 + h) : ℝ) : ℂ))
      (volume.prod volume) := by
    exact
      (Complex.continuous_ofReal.comp
        ((hχ.comp continuous_snd).mul
          (hχ.comp (continuous_snd.add continuous_const)))).aestronglyMeasurable
  exact h0.mul h1 |>.mul h2.star |>.mul h3.star |>.mul hχ'

/-- A fixed correlation integrand is one-bounded when its factors and
cutoff are one-bounded. -/
lemma aux_u3_correlationIntegrand_ae_one_bounded
    (h : ℝ) (f₀ f₁ : ℝ → ℂ) (χ : ℝ → ℝ)
    (hf₀ : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₁ : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hχ₀ : ∀ t : ℝ, 0 ≤ χ t) (hχ₁ : ∀ t : ℝ, χ t ≤ 1) :
    ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      ‖aux_u3_correlationIntegrand h f₀ f₁ χ z.1 z.2‖ ≤ 1 := by
  have h0 : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖f₀ z.1‖ ≤ 1 := by
    exact (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).tendsto_ae.eventually hf₀
  have h1 : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖f₁ (z.1 + z.2)‖ ≤ 1 := by
    exact aux_u3_qmp_add.tendsto_ae.eventually hf₁
  have h2 : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      ‖f₀ (z.1 - 2 * h * z.2 - h ^ 2)‖ ≤ 1 := by
    exact (aux_u3_qmp_correlation_left h).tendsto_ae.eventually hf₀
  have h3 : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      ‖f₁ (z.1 + (1 - 2 * h) * z.2 + h - h ^ 2)‖ ≤ 1 := by
    exact (aux_u3_qmp_correlation_right h).tendsto_ae.eventually hf₁
  filter_upwards [h0, h1, h2, h3] with z hz0 hz1 hz2 hz3
  have hχnorm : ‖((χ z.2 * χ (z.2 + h) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hχ₀ _) (hχ₀ _))]
    nlinarith [hχ₀ z.2, hχ₁ z.2, hχ₀ (z.2 + h), hχ₁ (z.2 + h)]
  rw [aux_u3_correlationIntegrand, norm_mul, norm_mul, norm_mul, norm_mul]
  change ‖f₀ z.1‖ * ‖f₁ (z.1 + z.2)‖ * ‖star (f₀ (z.1 - 2 * h * z.2 - h ^ 2))‖ *
      ‖star (f₁ (z.1 + (1 - 2 * h) * z.2 + h - h ^ 2))‖ *
      ‖((χ z.2 * χ (z.2 + h) : ℝ) : ℂ)‖ ≤ 1
  rw [norm_star, norm_star]
  calc
    ‖f₀ z.1‖ * ‖f₁ (z.1 + z.2)‖ * ‖f₀ (z.1 - 2 * h * z.2 - h ^ 2)‖ *
        ‖f₁ (z.1 + (1 - 2 * h) * z.2 + h - h ^ 2)‖ *
        ‖((χ z.2 * χ (z.2 + h) : ℝ) : ℂ)‖ ≤ 1 * 1 * 1 * 1 * 1 := by
          gcongr
    _ = 1 := by norm_num

/-- A fixed correlation integrand vanishes outside `A × J`. -/
lemma aux_u3_correlationIntegrand_zero_outside
    (A J : Set ℝ) (h : ℝ) (f₀ f₁ : ℝ → ℂ) (χ : ℝ → ℝ)
    (hf₀ : ∀ x : ℝ, x ∉ A → f₀ x = 0) (hχ : tsupport χ ⊆ J) :
    ∀ z : ℝ × ℝ, z ∉ A ×ˢ J →
      aux_u3_correlationIntegrand h f₀ f₁ χ z.1 z.2 = 0 := by
  intro z hz
  by_cases hx : z.1 ∈ A
  · by_cases ht : z.2 ∈ J
    · exact (hz ⟨hx, ht⟩).elim
    · have hts : z.2 ∉ tsupport χ := fun hmem ↦ ht (hχ hmem)
      have hzero : χ z.2 = 0 := image_eq_zero_of_notMem_tsupport hts
      simp [aux_u3_correlationIntegrand, hzero]
  · simp [aux_u3_correlationIntegrand, hf₀ z.1 hx]

/-- The compactly supported, fixed correlation integrand is integrable. -/
lemma aux_u3_correlationIntegrand_integrable
    (A J : Set ℝ) (hA : IsCompact A) (hJ : IsCompact J)
    (h : ℝ) (f₀ f₁ : ℝ → ℂ) (χ : ℝ → ℝ)
    (hf₀meas : AEStronglyMeasurable f₀ volume)
    (hf₁meas : AEStronglyMeasurable f₁ volume)
    (hf₀bound : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₁bound : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₀support : ∀ x : ℝ, x ∉ A → f₀ x = 0)
    (hχcont : Continuous χ) (hχ₀ : ∀ t : ℝ, 0 ≤ χ t)
    (hχ₁ : ∀ t : ℝ, χ t ≤ 1) (hχsupport : tsupport χ ⊆ J) :
    Integrable (Function.uncurry (aux_u3_correlationIntegrand h f₀ f₁ χ))
      (volume.prod volume) := by
  have hmeas := aux_u3_correlationIntegrand_aestronglyMeasurable h f₀ f₁ χ
    hf₀meas hf₁meas hχcont
  have hbound := aux_u3_correlationIntegrand_ae_one_bounded h f₀ f₁ χ
    hf₀bound hf₁bound hχ₀ hχ₁
  have hsupp : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∉ A ×ˢ J → aux_u3_correlationIntegrand h f₀ f₁ χ z.1 z.2 = 0 :=
    Filter.Eventually.of_forall (aux_u3_correlationIntegrand_zero_outside A J h f₀ f₁ χ
      hf₀support hχsupport)
  exact memLp_one_iff_integrable.mp <|
    aux_memLp_of_ae_bound_of_ae_support _ hmeas 1 hbound (A ×ˢ J)
      (hA.prod hJ).measurableSet (hA.prod hJ).measure_lt_top hsupp 1

/-- Uniform `|A| |J|` bound for every fixed correlation integral. -/
lemma aux_u3_correlationIntegrand_norm_integral_le
    (A J : Set ℝ) (hA : IsCompact A) (hJ : IsCompact J)
    (h : ℝ) (f₀ f₁ : ℝ → ℂ) (χ : ℝ → ℝ)
    (hf₀meas : AEStronglyMeasurable f₀ volume)
    (hf₁meas : AEStronglyMeasurable f₁ volume)
    (hf₀bound : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₁bound : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₀support : ∀ x : ℝ, x ∉ A → f₀ x = 0)
    (hχcont : Continuous χ) (hχ₀ : ∀ t : ℝ, 0 ≤ χ t)
    (hχ₁ : ∀ t : ℝ, χ t ≤ 1) (hχsupport : tsupport χ ⊆ J) :
    ‖∫ x : ℝ, ∫ t : ℝ, aux_u3_correlationIntegrand h f₀ f₁ χ x t‖ ≤
      volume.real A * volume.real J := by
  apply aux_u3_norm_doubleIntegral_le_measure_product A J hA hJ
  · exact aux_u3_correlationIntegrand_aestronglyMeasurable h f₀ f₁ χ hf₀meas hf₁meas hχcont
  · exact aux_u3_correlationIntegrand_ae_one_bounded h f₀ f₁ χ hf₀bound hf₁bound hχ₀ hχ₁
  · exact Filter.Eventually.of_forall
      (aux_u3_correlationIntegrand_zero_outside A J h f₀ f₁ χ hf₀support hχsupport)

/-- Each interval component of the three-set size parameter is bounded by its nonconstant part. -/
lemma aux_u3_intervalLength_three_le_sub_two
    (A C J : Set ℝ) (χ : ℝ → ℝ) (i : Fin 3) :
    intervalLength (![A, C, J] i) ≤ sizeParameter ![A, C, J] χ - 2 := by
  let R : Set ℝ := Set.range fun k : Fin 3 ↦ intervalLength (![A, C, J] k)
  have hRbdd : BddAbove R := Set.finite_range _ |>.bddAbove
  have hmem : intervalLength (![A, C, J] i) ∈ R := ⟨i, rfl⟩
  have hle : intervalLength (![A, C, J] i) ≤ sSup R := le_csSup hRbdd hmem
  change intervalLength (![A, C, J] i) ≤
    2 + max (sSup R) (max (supportRadius χ ^ 2)
      (max (eLpNorm χ 1 volume).toReal
        (max (eLpNorm χ 2 volume).toReal
          (max (eLpNorm (deriv χ) 1 volume).toReal
            (eLpNorm (deriv χ) 2 volume).toReal)))) - 2
  have hmax : sSup R ≤ max (sSup R) (max (supportRadius χ ^ 2)
      (max (eLpNorm χ 1 volume).toReal
        (max (eLpNorm χ 2 volume).toReal
          (max (eLpNorm (deriv χ) 1 volume).toReal
            (eLpNorm (deriv χ) 2 volume).toReal)))) := le_max_left _ _
  linarith

/-- The four differencing coefficients are uniformly bounded on the time difference set. -/
lemma aux_u3_coefficients_bounded_on_sub
    (A C J : Set ℝ) (χ : ℝ → ℝ)
    (hJ : ∃ p q : ℝ, p < q ∧ J = Set.Icc p q)
    (h : ℝ) (hh : h ∈ Set.image2 (fun s t : ℝ ↦ s - t) J J) :
    ∀ i j : Fin 4, i < j →
      |(![0, -2 * h, 1, 1 - 2 * h] i : ℝ) -
        (![0, -2 * h, 1, 1 - 2 * h] j : ℝ)| ≤
        2 * sizeParameter ![A, C, J] χ := by
  let S : ℝ := sizeParameter ![A, C, J] χ
  have hS_two : 2 ≤ S := by
    unfold S sizeParameter
    exact le_add_of_nonneg_right (by positivity)
  have hJlen : intervalLength J ≤ S - 2 := by
    simpa [S] using aux_u3_intervalLength_three_le_sub_two A C J χ 2
  rcases hJ with ⟨p, q, hpq, rfl⟩
  rcases hh with ⟨s, hs, t, ht, rfl⟩
  have hlen : intervalLength (Set.Icc p q) = q - p := by
    simp [intervalLength, sub_nonneg.mpr hpq.le]
  have habs : |s - t| ≤ S - 2 := by
    rw [hlen] at hJlen
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2, hJlen]
  have habs' : -(S - 2) ≤ s - t ∧ s - t ≤ S - 2 := abs_le.mp habs
  have htwo : |2 * (s - t)| ≤ 2 * S := by
    rw [abs_le]
    constructor <;> nlinarith [habs'.1, habs'.2]
  have hminus : |1 - 2 * (s - t)| ≤ 2 * S := by
    rw [abs_le]
    constructor <;> nlinarith [habs'.1, habs'.2]
  have hplus : |1 + 2 * (s - t)| ≤ 2 * S := by
    rw [abs_le]
    constructor <;> nlinarith [habs'.1, habs'.2]
  have hone : (1 : ℝ) ≤ 2 * S := by linarith
  have hdifference : |s - t| ≤ S := by linarith
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals norm_num
  · simpa [S] using hdifference
  · simpa [S] using hone
  · calc
      |2 * (s - t) - 1| = |1 - 2 * (s - t)| := abs_sub_comm _ _
      _ ≤ 2 * sizeParameter ![A, C, Set.Icc p q] χ := by simpa [S] using hminus
  · calc
      |-(2 * (s - t)) - 1| = |-(1 + 2 * (s - t))| := by
        congr 1
        ring
      _ = |1 + 2 * (s - t)| := abs_neg _
      _ ≤ 2 * sizeParameter ![A, C, Set.Icc p q] χ := by simpa [S] using hplus
  · calc
      |-(2 * (s - t)) - (1 - 2 * (s - t))| = 1 := by
        rw [show -(2 * (s - t)) - (1 - 2 * (s - t)) = -(1 : ℝ) by ring,
          abs_neg, abs_one]
      _ ≤ 2 * sizeParameter ![A, C, Set.Icc p q] χ := by simpa [S] using hone
  · simpa [S] using hdifference

lemma aux_u3_integral_le_levelSet_bound
    (F : ℝ → ℝ) (D : Set ℝ) (r U : ℝ)
    (hF : Integrable F volume) (hFmeas : Measurable F)
    (hDmeas : MeasurableSet D) (hDfinite : volume D < ∞)
    (hFsupp : ∀ x : ℝ, x ∉ D → F x = 0)
    (hFbound : ∀ x : ℝ, F x ≤ U)
    (hrnonneg : 0 ≤ r) :
    let E : Set ℝ := D ∩ {x | r ≤ F x}
    ∫ x : ℝ, F x ≤ U * volume.real E + r * volume.real D := by
  dsimp only
  let E : Set ℝ := D ∩ {x | r ≤ F x}
  have hEmeas : MeasurableSet E := by
    exact hDmeas.inter (measurableSet_le measurable_const hFmeas)
  have hEsub : E ⊆ D := fun _ hx ↦ hx.1
  have hEfinite : volume E < ∞ := lt_of_le_of_lt (measure_mono hEsub) hDfinite
  have hDEmeas : MeasurableSet (D \ E) := hDmeas.diff hEmeas
  have hDEsub : D \ E ⊆ D := fun _ hx ↦ hx.1
  have hDEfinite : volume (D \ E) < ∞ :=
    lt_of_le_of_lt (measure_mono hDEsub) hDfinite
  have hEint : Integrable (E.indicator fun _ : ℝ ↦ U) volume := by
    rw [← memLp_one_iff_integrable]
    exact memLp_indicator_const 1 hEmeas U (Or.inr hEfinite.ne)
  have hDEint : Integrable ((D \ E).indicator fun _ : ℝ ↦ r) volume := by
    rw [← memLp_one_iff_integrable]
    exact memLp_indicator_const 1 hDEmeas r (Or.inr hDEfinite.ne)
  let G : ℝ → ℝ := E.indicator (fun _ ↦ U) + (D \ E).indicator (fun _ ↦ r)
  have hG : Integrable G volume := hEint.add hDEint
  have hFG : ∀ x : ℝ, F x ≤ G x := by
    intro x
    by_cases hxE : x ∈ E
    · have hxU : F x ≤ U := hFbound x
      simp [G, hxE, hxU]
    by_cases hxD : x ∈ D
    · have hxlt : F x < r := by
        apply lt_of_not_ge
        intro hxr
        exact hxE ⟨hxD, hxr⟩
      simp [G, hxE, hxD, hxlt.le]
    · have hxzero : F x = 0 := hFsupp x hxD
      simp [G, hxE, hxD, hxzero]
  have hmain : ∫ x : ℝ, F x ≤
      U * volume.real E + r * volume.real (D \ E) := by
    calc
      ∫ x : ℝ, F x ≤ ∫ x : ℝ, G x :=
        integral_mono hF hG hFG
      _ = ∫ x : ℝ, E.indicator (fun _ : ℝ ↦ U) x +
          (D \ E).indicator (fun _ : ℝ ↦ r) x := by
        rfl
      _ = (∫ x : ℝ, E.indicator (fun _ : ℝ ↦ U) x) +
          ∫ x : ℝ, (D \ E).indicator (fun _ : ℝ ↦ r) x := by
        exact integral_add hEint hDEint
      _ = U * volume.real E + r * volume.real (D \ E) := by
        rw [integral_indicator_const U hEmeas,
          integral_indicator_const r hDEmeas]
        simp [smul_eq_mul, mul_comm]
  have hDEreal : volume.real (D \ E) ≤ volume.real D :=
    measureReal_mono hDEsub hDfinite.ne
  simpa [E] using hmain.trans (add_le_add_right
    (mul_le_mul_of_nonneg_left hDEreal hrnonneg) _)

/-- The same level-set estimate for an a.e.-measurable function.  The output
is a measurable subset of the literal superlevel set, so it is suitable for
pointwise applications such as `separationSelection`. -/
lemma aux_u3_integral_le_ae_levelSet_bound
    (F : ℝ → ℝ) (D : Set ℝ) (r U : ℝ)
    (hF : Integrable F volume) (hFmeas : AEMeasurable F volume)
    (hDmeas : MeasurableSet D) (hDfinite : volume D < ∞)
    (hFsupp : ∀ᵐ x : ℝ ∂volume, x ∉ D → F x = 0)
    (hFbound : ∀ᵐ x : ℝ ∂volume, F x ≤ U)
    (hrnonneg : 0 ≤ r) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ D ∩ {x | r ≤ F x} ∧
      ∫ x : ℝ, F x ≤ U * volume.real E + r * volume.real D := by
  let Raw : Set ℝ := D ∩ F ⁻¹' Set.Ici r
  have hRawNull : NullMeasurableSet Raw volume := by
    exact hDmeas.nullMeasurableSet.inter
      (hFmeas.nullMeasurableSet_preimage measurableSet_Ici)
  rcases hRawNull.exists_measurable_subset_ae_eq with ⟨E, hEsub, hEmeas, hEeq⟩
  have hEsubD : E ⊆ D := fun x hx ↦ (hEsub hx).1
  have hEfinite : volume E < ∞ := lt_of_le_of_lt (measure_mono hEsubD) hDfinite
  have hDEmeas : MeasurableSet (D \ E) := hDmeas.diff hEmeas
  have hDEsub : D \ E ⊆ D := fun x hx ↦ hx.1
  have hDEfinite : volume (D \ E) < ∞ :=
    lt_of_le_of_lt (measure_mono hDEsub) hDfinite
  have hEint : Integrable (E.indicator fun _ : ℝ ↦ U) volume := by
    rw [← memLp_one_iff_integrable]
    exact memLp_indicator_const 1 hEmeas U (Or.inr hEfinite.ne)
  have hDEint : Integrable ((D \ E).indicator fun _ : ℝ ↦ r) volume := by
    rw [← memLp_one_iff_integrable]
    exact memLp_indicator_const 1 hDEmeas r (Or.inr hDEfinite.ne)
  let G : ℝ → ℝ := E.indicator (fun _ ↦ U) + (D \ E).indicator (fun _ ↦ r)
  have hG : Integrable G volume := hEint.add hDEint
  have hFG : F ≤ᵐ[volume] G := by
    filter_upwards [hEeq, hFsupp, hFbound] with x hxEq hxSupp hxBound
    by_cases hxE : x ∈ E
    · have hxD : x ∈ D := hEsubD hxE
      simp [G, hxE, hxD, hxBound]
    by_cases hxD : x ∈ D
    · have hxnotRaw : x ∉ Raw := fun hxRaw ↦ hxE (hxEq.mpr hxRaw)
      have hxlt : F x < r := by
        apply lt_of_not_ge
        intro hxr
        apply hxnotRaw
        change x ∈ D ∩ F ⁻¹' Set.Ici r
        exact ⟨hxD, hxr⟩
      simp [G, hxE, hxD, hxlt.le]
    · have hxzero : F x = 0 := hxSupp hxD
      have hxE' : x ∉ E := fun hx ↦ hxD (hEsubD hx)
      simp [G, hxE', hxD, hxzero]
  have hmain : ∫ x : ℝ, F x ≤
      U * volume.real E + r * volume.real (D \ E) := by
    calc
      ∫ x : ℝ, F x ≤ ∫ x : ℝ, G x := integral_mono_ae hF hG hFG
      _ = ∫ x : ℝ, E.indicator (fun _ : ℝ ↦ U) x +
          (D \ E).indicator (fun _ : ℝ ↦ r) x := by
        rfl
      _ = (∫ x : ℝ, E.indicator (fun _ : ℝ ↦ U) x) +
          ∫ x : ℝ, (D \ E).indicator (fun _ : ℝ ↦ r) x := by
        exact integral_add hEint hDEint
      _ = U * volume.real E + r * volume.real (D \ E) := by
        rw [integral_indicator_const U hEmeas,
          integral_indicator_const r hDEmeas]
        simp [smul_eq_mul, mul_comm]
  have hDEreal : volume.real (D \ E) ≤ volume.real D :=
    measureReal_mono hDEsub hDfinite.ne
  refine ⟨E, hEmeas, ?_, ?_⟩
  · intro x hx
    have hxRaw := hEsub hx
    exact ⟨hxRaw.1, hxRaw.2⟩
  · exact hmain.trans (add_le_add_right
      (mul_le_mul_of_nonneg_left hDEreal hrnonneg) _)

/-- The numerical level-set extraction used after the compact outer
Cauchy--Schwarz/autocorrelation estimate in `u3Control`. -/
lemma aux_u3_levelSet_measure_lower
    (F : ℝ → ℝ) (D : Set ℝ) (I a c j : ℝ)
    (hF : Integrable F volume) (hFmeas : Measurable F)
    (hDmeas : MeasurableSet D) (hDfinite : volume D < ∞)
    (hFsupp : ∀ x : ℝ, x ∉ D → F x = 0)
    (hFbound : ∀ x : ℝ, F x ≤ a * j)
    (hIcs : I ^ (2 : ℕ) ≤ c * ∫ x : ℝ, F x)
    (ha : 0 < a) (hc : 0 < c) (hj : 0 < j)
    (hDmeasure : volume.real D ≤ 2 * j) :
    let α : ℝ := (4 * c * j)⁻¹
    let E : Set ℝ := D ∩ {x | α * I ^ (2 : ℕ) ≤ F x}
    (2 * c * j * a)⁻¹ * I ^ (2 : ℕ) ≤ volume.real E := by
  dsimp only
  let α : ℝ := (4 * c * j)⁻¹
  let E : Set ℝ := D ∩ {x | α * I ^ (2 : ℕ) ≤ F x}
  have hα0 : 0 ≤ α := by
    dsimp [α]
    positivity
  have hthreshold0 : 0 ≤ α * I ^ (2 : ℕ) :=
    mul_nonneg hα0 (sq_nonneg I)
  have hupper := aux_u3_integral_le_levelSet_bound F D
    (α * I ^ (2 : ℕ)) (a * j) hF hFmeas hDmeas hDfinite
    hFsupp hFbound hthreshold0
  have hupper' : ∫ x : ℝ, F x ≤
      a * j * volume.real E + (α * I ^ (2 : ℕ)) * (2 * j) := by
    calc
      ∫ x : ℝ, F x ≤
          a * j * volume.real E + (α * I ^ (2 : ℕ)) * volume.real D := by
        simpa [E] using hupper
      _ ≤ a * j * volume.real E + (α * I ^ (2 : ℕ)) * (2 * j) := by
        gcongr
  have hmain : I ^ (2 : ℕ) ≤
      c * (a * j * volume.real E + (α * I ^ (2 : ℕ)) * (2 * j)) :=
    hIcs.trans (mul_le_mul_of_nonneg_left hupper' hc.le)
  have hcj : c * j ≠ 0 := mul_ne_zero hc.ne' hj.ne'
  have htarget : I ^ (2 : ℕ) ≤ 2 * c * j * a * volume.real E := by
    dsimp [α] at hmain
    field_simp [hcj] at hmain
    nlinarith
  change (2 * c * j * a)⁻¹ * I ^ (2 : ℕ) ≤ volume.real E
  apply (inv_mul_le_iff₀ (by positivity : 0 < 2 * c * j * a)).mpr
  exact htarget

/-- A.e.-measurable version of `aux_u3_u3_levelSet_measure_lower`.  Its
measurable witness lies inside the literal correlation superlevel set, which
is the form required by `separationSelection`. -/
lemma aux_u3_levelSet_measure_lower_ae
    (F : ℝ → ℝ) (D : Set ℝ) (I a c j : ℝ)
    (hF : Integrable F volume) (hFmeas : AEMeasurable F volume)
    (hDmeas : MeasurableSet D) (hDfinite : volume D < ∞)
    (hFsupp : ∀ᵐ x : ℝ ∂volume, x ∉ D → F x = 0)
    (hFbound : ∀ᵐ x : ℝ ∂volume, F x ≤ a * j)
    (hIcs : I ^ (2 : ℕ) ≤ c * ∫ x : ℝ, F x)
    (ha : 0 < a) (hc : 0 < c) (hj : 0 < j)
    (hDmeasure : volume.real D ≤ 2 * j) :
    ∃ E : Set ℝ, MeasurableSet E ∧
      E ⊆ D ∩ {x | (4 * c * j)⁻¹ * I ^ (2 : ℕ) ≤ F x} ∧
      (2 * c * j * a)⁻¹ * I ^ (2 : ℕ) ≤ volume.real E := by
  let α : ℝ := (4 * c * j)⁻¹
  rcases aux_u3_integral_le_ae_levelSet_bound F D
      (α * I ^ (2 : ℕ)) (a * j) hF hFmeas hDmeas hDfinite hFsupp hFbound
      (mul_nonneg (by dsimp [α]; positivity) (sq_nonneg I)) with
    ⟨E, hEmeas, hEsub, hupper⟩
  have hupper' : ∫ x : ℝ, F x ≤
      a * j * volume.real E + (α * I ^ (2 : ℕ)) * (2 * j) := by
    calc
      ∫ x : ℝ, F x ≤
          a * j * volume.real E + (α * I ^ (2 : ℕ)) * volume.real D := hupper
      _ ≤ a * j * volume.real E + (α * I ^ (2 : ℕ)) * (2 * j) := by
        gcongr
  have hmain : I ^ (2 : ℕ) ≤
      c * (a * j * volume.real E + (α * I ^ (2 : ℕ)) * (2 * j)) :=
    hIcs.trans (mul_le_mul_of_nonneg_left hupper' hc.le)
  have hcj : c * j ≠ 0 := mul_ne_zero hc.ne' hj.ne'
  have htarget : I ^ (2 : ℕ) ≤ 2 * c * j * a * volume.real E := by
    dsimp [α] at hmain
    field_simp [hcj] at hmain
    nlinarith
  refine ⟨E, hEmeas, ?_, ?_⟩
  · change E ⊆ D ∩ {x | α * I ^ (2 : ℕ) ≤ F x}
    exact hEsub
  · exact (inv_mul_le_iff₀ (by positivity : 0 < 2 * c * j * a)).mpr htarget

/-- The preceding extraction in the exact `ENNReal` measure form consumed
by `separationSelection`. -/
lemma aux_u3_levelSet_measure_lower_ae_ennreal
    (F : ℝ → ℝ) (D : Set ℝ) (I a c j : ℝ)
    (hF : Integrable F volume) (hFmeas : AEMeasurable F volume)
    (hDmeas : MeasurableSet D) (hDfinite : volume D < ∞)
    (hFsupp : ∀ᵐ x : ℝ ∂volume, x ∉ D → F x = 0)
    (hFbound : ∀ᵐ x : ℝ ∂volume, F x ≤ a * j)
    (hIcs : I ^ (2 : ℕ) ≤ c * ∫ x : ℝ, F x)
    (ha : 0 < a) (hc : 0 < c) (hj : 0 < j)
    (hDmeasure : volume.real D ≤ 2 * j) :
    ∃ E : Set ℝ, MeasurableSet E ∧
      E ⊆ D ∩ {x | (4 * c * j)⁻¹ * I ^ (2 : ℕ) ≤ F x} ∧
      ENNReal.ofReal ((2 * c * j * a)⁻¹ * I ^ (2 : ℕ)) ≤ volume E := by
  rcases aux_u3_levelSet_measure_lower_ae F D I a c j
      hF hFmeas hDmeas hDfinite hFsupp hFbound hIcs ha hc hj hDmeasure with
    ⟨E, hEmeas, hEsub, hEmeasure⟩
  have hEsubD : E ⊆ D := fun x hx ↦ (hEsub hx).1
  have hEfinite : volume E < ∞ := lt_of_le_of_lt (measure_mono hEsubD) hDfinite
  refine ⟨E, hEmeas, hEsub, ?_⟩
  apply (ENNReal.ofReal_le_iff_le_toReal hEfinite.ne).mpr
  simpa only [Measure.real] using hEmeasure

lemma aux_u3_autocorrelation_norm_ae_support_difference
    (X J : Set ℝ) (Q : ℝ → ℝ → ℂ)
    (hQsupport : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∉ X ×ˢ J → Q z.1 z.2 = 0)
    (hR : Integrable
      (Function.uncurry fun p : ℝ × ℝ ↦ fun t : ℝ ↦
        Q p.1 t * starRingEnd ℂ (Q p.1 (t + p.2)))
      ((volume.prod volume).prod volume)) :
    ∀ᵐ h : ℝ ∂volume, h ∉ Set.image2 (fun s t : ℝ ↦ s - t) J J →
      ‖∫ x : ℝ, ∫ t : ℝ,
        Q x t * starRingEnd ℂ (Q x (t + h))‖ = 0 := by
  let R : ℝ → (ℝ × ℝ) → ℂ := fun h z ↦
    Q z.1 z.2 * starRingEnd ℂ (Q z.1 (z.2 + h))
  have hR' : Integrable (Function.uncurry R) (volume.prod (volume.prod volume)) := by
    change Integrable
      ((Function.uncurry fun p : ℝ × ℝ ↦ fun t : ℝ ↦
        Q p.1 t * starRingEnd ℂ (Q p.1 (t + p.2))) ∘
          fun z : ℝ × (ℝ × ℝ) ↦ ((z.2.1, z.1), z.2.2))
      (volume.prod (volume.prod volume))
    rw [← memLp_one_iff_integrable] at hR ⊢
    exact hR.comp_measurePreserving
      aux_measurePreserving_autocorrelation_reorder_symm
  have hleftqmp : Measure.QuasiMeasurePreserving
      (fun z : ℝ × (ℝ × ℝ) ↦ (z.2.1, z.2.2))
      (volume.prod (volume.prod volume)) (volume.prod volume) := by
    exact aux_autocorrelation_qmp_unshifted.comp
      aux_measurePreserving_autocorrelation_reorder_symm.quasiMeasurePreserving
  have hrightqmp : Measure.QuasiMeasurePreserving
      (fun z : ℝ × (ℝ × ℝ) ↦ (z.2.1, z.2.2 + z.1))
      (volume.prod (volume.prod volume)) (volume.prod volume) := by
    exact aux_autocorrelation_qmp_shifted.comp
      aux_measurePreserving_autocorrelation_reorder_symm.quasiMeasurePreserving
  have hleft : ∀ᵐ z : ℝ × (ℝ × ℝ) ∂volume.prod (volume.prod volume),
      (z.2.1, z.2.2) ∉ X ×ˢ J → Q z.2.1 z.2.2 = 0 :=
    hleftqmp.ae hQsupport
  have hright : ∀ᵐ z : ℝ × (ℝ × ℝ) ∂volume.prod (volume.prod volume),
      (z.2.1, z.2.2 + z.1) ∉ X ×ˢ J → Q z.2.1 (z.2.2 + z.1) = 0 :=
    hrightqmp.ae hQsupport
  have hleft' : ∀ᵐ h : ℝ ∂volume, ∀ᵐ z : ℝ × ℝ ∂volume,
      (z.1, z.2) ∉ X ×ˢ J → Q z.1 z.2 = 0 := by
    exact Measure.ae_ae_of_ae_prod hleft
  have hright' : ∀ᵐ h : ℝ ∂volume, ∀ᵐ z : ℝ × ℝ ∂volume,
      (z.1, z.2 + h) ∉ X ×ˢ J → Q z.1 (z.2 + h) = 0 := by
    exact Measure.ae_ae_of_ae_prod hright
  have hsections : ∀ᵐ h : ℝ ∂volume, Integrable (R h) volume := hR'.prod_right_ae
  filter_upwards [hleft', hright', hsections] with h hleft hright hsection
  intro hh
  have hzero : ∫ z : ℝ × ℝ, R h z ∂(volume.prod volume) = 0 := by
    rw [← integral_zero]
    apply integral_congr_ae
    filter_upwards [hleft, hright] with z hzleft hzright
    by_cases hz : (z.1, z.2) ∈ X ×ˢ J
    · have htz : z.2 ∈ J := hz.2
      have hnot : (z.1, z.2 + h) ∉ X ×ˢ J := by
        intro hmem
        apply hh
        exact ⟨z.2 + h, hmem.2, z.2, htz, by ring⟩
      change Q z.1 z.2 * starRingEnd ℂ (Q z.1 (z.2 + h)) = 0
      rw [hzright hnot]
      simp
    · change Q z.1 z.2 * starRingEnd ℂ (Q z.1 (z.2 + h)) = 0
      rw [hzleft hz]
      simp
  have heq : (∫ x : ℝ, ∫ t : ℝ,
      Q x t * starRingEnd ℂ (Q x (t + h))) =
        ∫ z : ℝ × ℝ, R h z ∂(volume.prod volume) := by
    simpa only [R] using (integral_prod (R h) hsection).symm
  rw [heq, hzero]
  exact norm_zero

/-- The difference set of a compact interval has twice its length. -/
lemma aux_u3_difference_set_measure_Icc (p q : ℝ) (hpq : p ≤ q) :
    volume.real (Set.image2 (fun s t : ℝ ↦ s - t)
      (Set.Icc p q) (Set.Icc p q)) = 2 * volume.real (Set.Icc p q) := by
  simpa only [intervalLength, Measure.real, two_mul] using intervalSub p q p q hpq hpq


/-- Support-radius monotonicity under inclusion of topological supports. -/
lemma aux_u3_supportRadius_mono
    (f g : ℝ → ℝ) (hgcompact : HasCompactSupport g)
    (hsub : tsupport f ⊆ tsupport g) :
    supportRadius f ≤ supportRadius g := by
  classical
  by_cases hf : f = 0
  · subst f
    by_cases hgzero : g = 0
    · simp [supportRadius, hgzero]
    · have hr0 : supportRadius (0 : ℝ → ℝ) = 1 := by
        simp [supportRadius]
      have hrg : supportRadius g =
          1 + sSup (Set.image (fun t : ℝ ↦ |t|) (tsupport g)) := by
        simp [supportRadius, hgzero]
      rw [hr0, hrg]
      have hnonempty : (tsupport g).Nonempty := by
        by_contra h
        have hempty : tsupport g = ∅ := not_nonempty_iff_eq_empty.mp h
        exact hgzero (tsupport_eq_empty_iff.mp hempty)
      obtain ⟨x, hx⟩ := hnonempty
      have hmem : |x| ∈ Set.image (fun t : ℝ ↦ |t|) (tsupport g) := ⟨x, hx, rfl⟩
      have hbdd : BddAbove (Set.image (fun t : ℝ ↦ |t|) (tsupport g)) :=
        hgcompact.isCompact.image continuous_abs |>.bddAbove
      have hsup : 0 ≤ sSup (Set.image (fun t : ℝ ↦ |t|) (tsupport g)) :=
        le_trans (abs_nonneg x) (le_csSup hbdd hmem)
      linarith
  by_cases hgzero : g = 0
  · have hempty : tsupport f = ∅ := by
      apply not_nonempty_iff_eq_empty.mp
      intro hnonempty
      rcases hnonempty with ⟨x, hx⟩
      have : x ∈ tsupport g := hsub hx
      simp [hgzero] at this
    exact (hf (tsupport_eq_empty_iff.mp hempty)).elim
  have hrf : supportRadius f =
      1 + sSup (Set.image (fun t : ℝ ↦ |t|) (tsupport f)) := by
    simp [supportRadius, hf]
  have hrg : supportRadius g =
      1 + sSup (Set.image (fun t : ℝ ↦ |t|) (tsupport g)) := by
    simp [supportRadius, hgzero]
  have himage : Set.image (fun t : ℝ ↦ |t|) (tsupport f) ⊆
      Set.image (fun t : ℝ ↦ |t|) (tsupport g) := Set.image_mono hsub
  have hbdd : BddAbove (Set.image (fun t : ℝ ↦ |t|) (tsupport g)) :=
    hgcompact.isCompact.image continuous_abs |>.bddAbove
  have hsup : sSup (Set.image (fun t : ℝ ↦ |t|) (tsupport f)) ≤
      sSup (Set.image (fun t : ℝ ↦ |t|) (tsupport g)) := by
    apply csSup_le
    · have hnonempty : (tsupport f).Nonempty := by
        by_contra h
        have hempty : tsupport f = ∅ := not_nonempty_iff_eq_empty.mp h
        exact hf (tsupport_eq_empty_iff.mp hempty)
      exact hnonempty.image _
    · intro x hx
      exact le_csSup hbdd (himage hx)
  rw [hrf, hrg]
  linarith

/-- Every compactly supported cutoff has support radius at least one. -/
lemma aux_u3_one_le_supportRadius (f : ℝ → ℝ) (hcompact : HasCompactSupport f) :
    1 ≤ supportRadius f := by
  classical
  by_cases hf : f = 0
  · simp [supportRadius, hf]
  · have hnonempty : (tsupport f).Nonempty := by
      by_contra h
      have hempty : tsupport f = ∅ := not_nonempty_iff_eq_empty.mp h
      exact hf (tsupport_eq_empty_iff.mp hempty)
    obtain ⟨x, hx⟩ := hnonempty
    have hmem : |x| ∈ Set.image (fun t : ℝ ↦ |t|) (tsupport f) := ⟨x, hx, rfl⟩
    have hbdd : BddAbove (Set.image (fun t : ℝ ↦ |t|) (tsupport f)) :=
      hcompact.isCompact.image continuous_abs |>.bddAbove
    rw [show supportRadius f = 1 + sSup (Set.image (fun t : ℝ ↦ |t|) (tsupport f)) by
      simp [supportRadius, hf]]
    have : 0 ≤ sSup (Set.image (fun t : ℝ ↦ |t|) (tsupport f)) :=
      le_trans (abs_nonneg x) (le_csSup hbdd hmem)
    linarith

/-- Each interval length is bounded by the three-set size parameter. -/
lemma aux_u3_intervalLength_le_size_three
    (A C J : Set ℝ) (χ : ℝ → ℝ) (i : Fin 3) :
    intervalLength (![A, C, J] i) ≤ sizeParameter ![A, C, J] χ := by
  let v : Fin 3 → ℝ := fun k ↦ intervalLength (![A, C, J] k)
  have hbdd : BddAbove (Set.range v) := by
    refine ⟨max (intervalLength A) (max (intervalLength C) (intervalLength J)), ?_⟩
    rintro x ⟨k, rfl⟩
    fin_cases k <;> simp [v, le_max_iff]
  have hmem : intervalLength (![A, C, J] i) ∈ Set.range v := ⟨i, by simp [v]⟩
  have hsup : intervalLength (![A, C, J] i) ≤ sSup (Set.range v) := le_csSup hbdd hmem
  let r : ℝ := max (supportRadius χ ^ 2)
    (max (eLpNorm χ 1 volume).toReal
      (max (eLpNorm χ 2 volume).toReal
        (max (eLpNorm (deriv χ) 1 volume).toReal
          (eLpNorm (deriv χ) 2 volume).toReal)))
  have hmax : sSup (Set.range v) ≤ max (sSup (Set.range v)) r := le_max_left _ _
  change intervalLength (![A, C, J] i) ≤ 2 + max (sSup (Set.range v)) r
  linarith

/-- A translated product cutoff has no larger `L¹` norm. -/
lemma aux_u3_productCutoff_eLpNorm_one
    (χ : ℝ → ℝ) (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t)
    (hχ_le_one : ∀ t : ℝ, χ t ≤ 1) (u : ℝ) :
    eLpNorm (fun t : ℝ ↦ χ t * χ (t + u)) (1 : ℝ≥0∞) volume ≤
      eLpNorm χ (1 : ℝ≥0∞) volume := by
  apply eLpNorm_mono
  intro t
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (hχ_nonneg t), abs_of_nonneg (hχ_nonneg (t + u))]
  simpa using mul_le_mul_of_nonneg_left (hχ_le_one (t + u)) (hχ_nonneg t)

/-- The derivative of a translated product cutoff has controlled `L¹` norm. -/
lemma aux_u3_productCutoff_deriv_eLpNorm_one
    (χ : ℝ → ℝ) (hχ_smooth : ContDiff ℝ 1 χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (u : ℝ) :
    eLpNorm (deriv (fun t : ℝ ↦ χ t * χ (t + u))) (1 : ℝ≥0∞) volume ≤
      2 * eLpNorm (deriv χ) (1 : ℝ≥0∞) volume := by
  have hdercont : Continuous (deriv χ) :=
    hχ_smooth.continuous_deriv (by norm_num : (1 : WithTop ℕ∞) ≤ 1)
  have hshiftcont : Continuous (fun t : ℝ ↦ χ (t + u)) :=
    hχ_smooth.continuous.comp (continuous_id.add continuous_const)
  have hdershiftcont : Continuous (fun t : ℝ ↦ deriv χ (t + u)) :=
    hdercont.comp (continuous_id.add continuous_const)
  have hleft : eLpNorm (fun t : ℝ ↦ deriv χ t * χ (t + u)) (1 : ℝ≥0∞) volume ≤
      eLpNorm (deriv χ) (1 : ℝ≥0∞) volume := by
    apply eLpNorm_mono
    intro t
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (hχ_nonneg (t + u))]
    exact (mul_le_mul_of_nonneg_left (hχ_le_one (t + u)) (abs_nonneg _)).trans_eq (by ring)
  have hright : eLpNorm (fun t : ℝ ↦ χ t * deriv χ (t + u)) (1 : ℝ≥0∞) volume ≤
      eLpNorm (fun t : ℝ ↦ deriv χ (t + u)) (1 : ℝ≥0∞) volume := by
    apply eLpNorm_mono
    intro t
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (hχ_nonneg t)]
    exact (mul_le_mul_of_nonneg_right (hχ_le_one t) (abs_nonneg _)).trans_eq (by ring)
  have hformula : deriv (fun t : ℝ ↦ χ t * χ (t + u)) =
      fun t : ℝ ↦ deriv χ t * χ (t + u) + χ t * deriv χ (t + u) := by
    funext t
    exact aux_productCutoffDerivativeFormula χ hχ_smooth u t
  rw [hformula]
  calc
    eLpNorm (fun t : ℝ ↦ deriv χ t * χ (t + u) + χ t * deriv χ (t + u))
        (1 : ℝ≥0∞) volume ≤
        eLpNorm (fun t : ℝ ↦ deriv χ t * χ (t + u)) (1 : ℝ≥0∞) volume +
          eLpNorm (fun t : ℝ ↦ χ t * deriv χ (t + u)) (1 : ℝ≥0∞) volume := by
        exact eLpNorm_add_le (hdercont.mul hshiftcont).aestronglyMeasurable
          (hχ_smooth.continuous.mul hdershiftcont).aestronglyMeasurable (by norm_num)
    _ ≤ eLpNorm (deriv χ) (1 : ℝ≥0∞) volume +
          eLpNorm (fun t : ℝ ↦ deriv χ (t + u)) (1 : ℝ≥0∞) volume :=
      add_le_add hleft hright
    _ = eLpNorm (deriv χ) (1 : ℝ≥0∞) volume +
          eLpNorm (deriv χ) (1 : ℝ≥0∞) volume := by
      rw [aux_eLpNormTranslateReal (deriv χ) hdercont.aestronglyMeasurable 1 u]
    _ = 2 * eLpNorm (deriv χ) (1 : ℝ≥0∞) volume := by ring

/-- The two-interval size of a translated product cutoff is at most four times the ambient size. -/
lemma aux_u3_productCutoff_size_le_four_mul
    (A C J : Set ℝ) (χ : ℝ → ℝ)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (u : ℝ) :
    sizeParameter ![A, J] (fun t : ℝ ↦ χ t * χ (t + u)) ≤
      4 * sizeParameter ![A, C, J] χ := by
  let ψ : ℝ → ℝ := fun t ↦ χ t * χ (t + u)
  let S : ℝ := sizeParameter ![A, C, J] χ
  have hχ₁ : ContDiff ℝ 1 χ := hχ_smooth.of_le (by norm_num)
  have hψcompact : HasCompactSupport ψ := by
    exact aux_productCutoffCompact χ hχ_compact u
  have hS2 : 2 ≤ S := by
    dsimp [S, sizeParameter]
    exact le_add_of_nonneg_right (by positivity)
  have hS0 : 0 ≤ S := by linarith
  have hA : intervalLength A ≤ S := by
    simpa only [S, Matrix.cons_val_zero] using
      aux_u3_intervalLength_le_size_three A C J χ 0
  have hJ : intervalLength J ≤ S := by
    change intervalLength (![A, C, J] (2 : Fin 3)) ≤ S
    exact aux_u3_intervalLength_le_size_three A C J χ 2
  let Tχ : ℝ := max (supportRadius χ ^ 2)
    (max (eLpNorm χ 1 volume).toReal
      (max (eLpNorm χ 2 volume).toReal
        (max (eLpNorm (deriv χ) 1 volume).toReal
          (eLpNorm (deriv χ) 2 volume).toReal)))
  have hTχ : Tχ ≤ S := by
    change Tχ ≤ 2 + max (sSup (Set.range fun i : Fin 3 ↦ intervalLength (![A, C, J] i))) Tχ
    nlinarith [le_max_right (sSup (Set.range fun i : Fin 3 ↦ intervalLength (![A, C, J] i))) Tχ]
  have hradχ : supportRadius χ ^ 2 ≤ S := by
    exact (le_max_left _ _).trans hTχ
  have hnormχ1 : (eLpNorm χ (1 : ℝ≥0∞) volume).toReal ≤ S := by
    apply (show (eLpNorm χ (1 : ℝ≥0∞) volume).toReal ≤ Tχ by
      dsimp [Tχ]
      exact (le_max_left _ _).trans (le_max_right _ _)).trans hTχ
  have hnormχ2 : (eLpNorm χ (2 : ℝ≥0∞) volume).toReal ≤ S := by
    apply (show (eLpNorm χ (2 : ℝ≥0∞) volume).toReal ≤ Tχ by
      dsimp [Tχ]
      exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hTχ
  have hderχ1 : (eLpNorm (deriv χ) (1 : ℝ≥0∞) volume).toReal ≤ S := by
    apply (show (eLpNorm (deriv χ) (1 : ℝ≥0∞) volume).toReal ≤ Tχ by
      dsimp [Tχ]
      calc
        (eLpNorm (deriv χ) (1 : ℝ≥0∞) volume).toReal ≤
            max (eLpNorm (deriv χ) 1 volume).toReal
              (eLpNorm (deriv χ) 2 volume).toReal := le_max_left _ _
        _ ≤ max (eLpNorm χ 2 volume).toReal
              (max (eLpNorm (deriv χ) 1 volume).toReal
                (eLpNorm (deriv χ) 2 volume).toReal) := le_max_right _ _
        _ ≤ max (eLpNorm χ 1 volume).toReal
              (max (eLpNorm χ 2 volume).toReal
                (max (eLpNorm (deriv χ) 1 volume).toReal
                  (eLpNorm (deriv χ) 2 volume).toReal)) := le_max_right _ _
        _ ≤ max (supportRadius χ ^ 2)
              (max (eLpNorm χ 1 volume).toReal
                (max (eLpNorm χ 2 volume).toReal
                  (max (eLpNorm (deriv χ) 1 volume).toReal
                    (eLpNorm (deriv χ) 2 volume).toReal))) := le_max_right _ _).trans hTχ
  have hderχ2 : (eLpNorm (deriv χ) (2 : ℝ≥0∞) volume).toReal ≤ S := by
    apply (show (eLpNorm (deriv χ) (2 : ℝ≥0∞) volume).toReal ≤ Tχ by
      dsimp [Tχ]
      calc
        (eLpNorm (deriv χ) (2 : ℝ≥0∞) volume).toReal ≤
            max (eLpNorm (deriv χ) 1 volume).toReal
              (eLpNorm (deriv χ) 2 volume).toReal := le_max_right _ _
        _ ≤ max (eLpNorm χ 2 volume).toReal
              (max (eLpNorm (deriv χ) 1 volume).toReal
                (eLpNorm (deriv χ) 2 volume).toReal) := le_max_right _ _
        _ ≤ max (eLpNorm χ 1 volume).toReal
              (max (eLpNorm χ 2 volume).toReal
                (max (eLpNorm (deriv χ) 1 volume).toReal
                  (eLpNorm (deriv χ) 2 volume).toReal)) := le_max_right _ _
        _ ≤ max (supportRadius χ ^ 2)
              (max (eLpNorm χ 1 volume).toReal
                (max (eLpNorm χ 2 volume).toReal
                  (max (eLpNorm (deriv χ) 1 volume).toReal
                    (eLpNorm (deriv χ) 2 volume).toReal))) := le_max_right _ _).trans hTχ
  have hχmem1 : MemLp χ (1 : ℝ≥0∞) volume :=
    hχ_smooth.continuous.memLp_of_hasCompactSupport hχ_compact
  have hχmem2 : MemLp χ (2 : ℝ≥0∞) volume :=
    hχ_smooth.continuous.memLp_of_hasCompactSupport hχ_compact
  have hdermem1 : MemLp (deriv χ) (1 : ℝ≥0∞) volume :=
    (hχ_smooth.continuous_deriv (by norm_num)).memLp_of_hasCompactSupport hχ_compact.deriv
  have hdermem2 : MemLp (deriv χ) (2 : ℝ≥0∞) volume :=
    (hχ_smooth.continuous_deriv (by norm_num)).memLp_of_hasCompactSupport hχ_compact.deriv
  have hprod1 : (eLpNorm ψ (1 : ℝ≥0∞) volume).toReal ≤ S := by
    have hraw := aux_u3_productCutoff_eLpNorm_one χ hχ_nonneg hχ_le_one u
    calc
      (eLpNorm ψ (1 : ℝ≥0∞) volume).toReal ≤
          (eLpNorm χ (1 : ℝ≥0∞) volume).toReal := by
        simpa only [ψ] using ENNReal.toReal_mono hχmem1.eLpNorm_ne_top hraw
      _ ≤ S := hnormχ1
  have hprod2 : (eLpNorm ψ (2 : ℝ≥0∞) volume).toReal ≤ S := by
    have hraw := aux_productCutoffELpNormBound χ hχ_nonneg hχ_le_one u
    calc
      (eLpNorm ψ (2 : ℝ≥0∞) volume).toReal ≤
          (eLpNorm χ (2 : ℝ≥0∞) volume).toReal := by
        simpa only [ψ] using ENNReal.toReal_mono hχmem2.eLpNorm_ne_top hraw
      _ ≤ S := hnormχ2
  have hderprod1 : (eLpNorm (deriv ψ) (1 : ℝ≥0∞) volume).toReal ≤ 2 * S := by
    have hraw := aux_u3_productCutoff_deriv_eLpNorm_one χ hχ₁ hχ_nonneg hχ_le_one u
    calc
      (eLpNorm (deriv ψ) (1 : ℝ≥0∞) volume).toReal ≤
          (2 * eLpNorm (deriv χ) (1 : ℝ≥0∞) volume).toReal := by
        simpa only [ψ] using ENNReal.toReal_mono
          (ENNReal.mul_ne_top (by norm_num) hdermem1.eLpNorm_ne_top) hraw
      _ = 2 * (eLpNorm (deriv χ) (1 : ℝ≥0∞) volume).toReal := by
        rw [ENNReal.toReal_mul]
        norm_num
      _ ≤ 2 * S := by gcongr
  have hderprod2 : (eLpNorm (deriv ψ) (2 : ℝ≥0∞) volume).toReal ≤ 2 * S := by
    have hraw := aux_productCutoffDerivativeELpNormBound χ hχ₁ hχ_nonneg hχ_le_one u
    have hformula : deriv ψ =
        fun t : ℝ ↦ deriv χ t * χ (t + u) + χ t * deriv χ (t + u) := by
      funext t
      dsimp [ψ]
      exact aux_productCutoffDerivativeFormula χ hχ₁ u t
    calc
      (eLpNorm (deriv ψ) (2 : ℝ≥0∞) volume).toReal ≤
          (2 * eLpNorm (deriv χ) (2 : ℝ≥0∞) volume).toReal := by
        rw [hformula]
        exact ENNReal.toReal_mono
          (ENNReal.mul_ne_top (by norm_num) hdermem2.eLpNorm_ne_top) hraw
      _ = 2 * (eLpNorm (deriv χ) (2 : ℝ≥0∞) volume).toReal := by
        rw [ENNReal.toReal_mul]
        norm_num
      _ ≤ 2 * S := by gcongr
  have hrad : supportRadius ψ ≤ supportRadius χ := by
    refine aux_u3_supportRadius_mono ψ χ hχ_compact ?_
    dsimp [ψ]
    exact tsupport_mul_subset_left
  have hradψ0 : 0 ≤ supportRadius ψ :=
    zero_le_one.trans (aux_u3_one_le_supportRadius ψ hψcompact)
  have hradχ0 : 0 ≤ supportRadius χ :=
    zero_le_one.trans (aux_u3_one_le_supportRadius χ hχ_compact)
  have hradprod : supportRadius ψ ^ 2 ≤ S := by
    have hsquare : supportRadius ψ ^ 2 ≤ supportRadius χ ^ 2 := by
      nlinarith
    exact hsquare.trans hradχ
  have hrange : sSup (Set.range fun i : Fin 2 ↦ intervalLength (![A, J] i)) ≤ S := by
    apply csSup_le
    · exact Set.range_nonempty _
    · rintro x ⟨i, rfl⟩
      fin_cases i
      · exact hA
      · exact hJ
  have hSle2S : S ≤ 2 * S := by nlinarith
  have hinner : max (supportRadius ψ ^ 2)
      (max (eLpNorm ψ 1 volume).toReal
        (max (eLpNorm ψ 2 volume).toReal
          (max (eLpNorm (deriv ψ) 1 volume).toReal
            (eLpNorm (deriv ψ) 2 volume).toReal))) ≤ 2 * S := by
    apply max_le
    · exact hradprod.trans hSle2S
    apply max_le
    · exact hprod1.trans hSle2S
    apply max_le
    · exact hprod2.trans hSle2S
    apply max_le
    · exact hderprod1
    · exact hderprod2
  change 2 + max (sSup (Set.range fun i : Fin 2 ↦ intervalLength (![A, J] i)))
    (max (supportRadius ψ ^ 2)
      (max (eLpNorm ψ 1 volume).toReal
        (max (eLpNorm ψ 2 volume).toReal
          (max (eLpNorm (deriv ψ) 1 volume).toReal
            (eLpNorm (deriv ψ) 2 volume).toReal)))) ≤ 4 * S
  have hmax : max (sSup (Set.range fun i : Fin 2 ↦ intervalLength (![A, J] i)))
      (max (supportRadius ψ ^ 2)
        (max (eLpNorm ψ 1 volume).toReal
          (max (eLpNorm ψ 2 volume).toReal
            (max (eLpNorm (deriv ψ) 1 volume).toReal
              (eLpNorm (deriv ψ) 2 volume).toReal)))) ≤ 2 * S :=
    max_le (hrange.trans hSle2S) hinner
  nlinarith

/-- A translated conjugate of an interval restriction has compact support. -/
lemma aux_u3_hasCompactSupport_shift_star_indicator
    (A : Set ℝ) (hA : IsCompact A) (f : ℝ → ℂ) (r : ℝ) :
    HasCompactSupport (fun x : ℝ ↦ starRingEnd ℂ (A.indicator f (x - r))) := by
  let B : Set ℝ := (fun y : ℝ ↦ y + r) '' A
  have hB : IsCompact B := by
    dsimp [B]
    exact hA.image (continuous_id.add continuous_const)
  apply HasCompactSupport.intro hB
  intro x hx
  change x ∉ (fun y : ℝ ↦ y + r) '' A at hx
  have hnot : x - r ∉ A := by
    intro hmem
    apply hx
    exact ⟨x - r, hmem, by ring⟩
  simp [Set.indicator_of_notMem hnot]

/-- Measurability of a translated conjugate interval restriction. -/
lemma aux_u3_shift_star_indicator_aestronglyMeasurable
    (A : Set ℝ) (hA : MeasurableSet A) (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f volume) (r : ℝ) :
    AEStronglyMeasurable (fun x : ℝ ↦ starRingEnd ℂ (A.indicator f (x - r))) volume := by
  have hfI : AEStronglyMeasurable (A.indicator f) volume := hf.indicator hA
  have hshift : AEStronglyMeasurable (fun x : ℝ ↦ A.indicator f (x - r)) volume := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      hfI.comp_quasiMeasurePreserving
        (measurePreserving_add_right volume (-r)).quasiMeasurePreserving
  exact hshift.star

/-- A translated conjugate interval restriction remains one-bounded. -/
lemma aux_u3_shift_star_indicator_ae_one_bounded
    (A : Set ℝ) (f : ℝ → ℂ)
    (hf : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1) (r : ℝ) :
    ∀ᵐ x ∂volume, ‖starRingEnd ℂ (A.indicator f (x - r))‖ ≤ 1 := by
  have hI : ∀ᵐ x ∂volume, ‖A.indicator f x‖ ≤ 1 :=
    aux_gowersRestrict_ae_one_bounded A f hf
  have hshift : ∀ᵐ x ∂volume, ‖A.indicator f (x - r)‖ ≤ 1 := by
    exact (measurePreserving_add_right volume (-r)).quasiMeasurePreserving.tendsto_ae.eventually hI
  filter_upwards [hshift] with x hx
  simpa using hx

/-- The `u³` seminorm is invariant under translations. -/
lemma aux_u3_uNorm_three_translate (f : ℝ → ℂ) (y : ℝ) :
    uNorm 3 (fun x : ℝ ↦ f (x + y)) = uNorm 3 f := by
  rw [aux_uNorm_three_eq_real_parameter, aux_uNorm_three_eq_real_parameter]
  congr 1
  apply lintegral_congr
  intro h
  have hdiff : multiplicativeDifference h (fun x : ℝ ↦ f (x + y)) =
      fun x ↦ multiplicativeDifference h f (x + y) := by
    funext x
    simp only [multiplicativeDifference]
    ring_nf
  rw [hdiff, aux_fourier_linf_translate]

/-- The `u³` seminorm is invariant under complex conjugation. -/
lemma aux_u3_uNorm_three_star (f : ℝ → ℂ) :
    uNorm 3 (fun x : ℝ ↦ starRingEnd ℂ (f x)) = uNorm 3 f := by
  rw [aux_uNorm_three_eq_real_parameter, aux_uNorm_three_eq_real_parameter]
  congr 1
  apply lintegral_congr
  intro h
  have hdiff : multiplicativeDifference h (fun x : ℝ ↦ starRingEnd ℂ (f x)) =
      fun x ↦ starRingEnd ℂ (multiplicativeDifference h f x) := by
    funext x
    simp [multiplicativeDifference]
  rw [hdiff, aux_fourier_linf_conj]

/-- The selected four-factor correlation is an instance of
`gowersDifferencing`. -/
lemma aux_u3_fixed_h_gowers_bound
    (A J : Set ℝ) (χ : ℝ → ℝ)
    (hA : ∃ a b : ℝ, a < b ∧ A = Set.Icc a b)
    (hJ : ∃ a b : ℝ, a < b ∧ J = Set.Icc a b)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (hχ_support : tsupport χ ⊆ J)
    (f₀ f₁ : ℝ → ℂ)
    (hf₀_measurable : AEStronglyMeasurable f₀ volume)
    (hf₁_measurable : AEStronglyMeasurable f₁ volume)
    (hf₀_one_bounded : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₁_one_bounded : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₀_support : ∀ᵐ x ∂volume, x ∉ A → f₀ x = 0)
    (h δ M : ℝ) (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1) (hM_one : 1 ≤ M)
    (hsep : ∀ i j : Fin 4, i < j →
      δ ≤ |(![0, -2 * h, 1, 1 - 2 * h] i : ℝ) -
        (![0, -2 * h, 1, 1 - 2 * h] j : ℝ)|)
    (hbound : ∀ i j : Fin 4, i < j →
      |(![0, -2 * h, 1, 1 - 2 * h] i : ℝ) -
        (![0, -2 * h, 1, 1 - 2 * h] j : ℝ)| ≤ M) :
    ENNReal.ofReal ‖∫ x : ℝ, ∫ t : ℝ,
      A.indicator f₀ x * f₁ (x + t) *
        starRingEnd ℂ (A.indicator f₀ (x - 2 * h * t - h ^ (2 : ℕ))) *
        starRingEnd ℂ (f₁ (x + (1 - 2 * h) * t + h - h ^ (2 : ℕ))) *
        ((χ t * χ (t + h) : ℝ) : ℂ)‖ ≤
      ENNReal.ofReal
        (C_gowersDifferencing A J (fun t : ℝ ↦ χ t * χ (t + h)) * M *
          δ ^ (-(3 / 2 : ℝ))) * uNorm 3 f₀ := by
  rcases hA with ⟨a, b, hab, rfl⟩
  rcases hJ with ⟨p, q, hpq, rfl⟩
  let f₀' : ℝ → ℂ := Set.Icc a b |>.indicator f₀
  let c : Fin 4 → ℝ := ![0, -2 * h, 1, 1 - 2 * h]
  let g : Fin 4 → ℝ → ℂ := ![
    f₀',
    fun y : ℝ ↦ starRingEnd ℂ (f₀' (y - h ^ (2 : ℕ))),
    f₁,
    fun y : ℝ ↦ starRingEnd ℂ (f₁ (y + h - h ^ (2 : ℕ)))]
  let ψh : ℝ → ℝ := fun t ↦ χ t * χ (t + h)
  have hAcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  have hAmeas : MeasurableSet (Set.Icc a b) := measurableSet_Icc
  have hχ₁ : ContDiff ℝ 1 χ := hχ_smooth.of_le (by norm_num)
  have hψh_smooth : ContDiff ℝ 1 ψh := by
    exact aux_productCutoffSmooth χ hχ₁ h
  have hψh_compact : HasCompactSupport ψh := by
    exact aux_productCutoffCompact χ hχ_compact h
  have hψh_nonneg : ∀ t : ℝ, 0 ≤ ψh t := by
    intro t
    exact mul_nonneg (hχ_nonneg _) (hχ_nonneg _)
  have hψh_le_one : ∀ t : ℝ, ψh t ≤ 1 := by
    intro t
    exact (mul_le_of_le_one_left (hχ_nonneg _) (hχ_le_one _)).trans (hχ_le_one _)
  have hψh_support : tsupport ψh ⊆ Set.Icc p q := by
    exact (show tsupport (fun t : ℝ ↦ χ t * χ (t + h)) ⊆ tsupport χ from
      tsupport_mul_subset_left).trans hχ_support
  have hf₀'meas : AEStronglyMeasurable f₀' volume := by
    exact hf₀_measurable.indicator hAmeas
  have hf₀'bound : ∀ᵐ x ∂volume, ‖f₀' x‖ ≤ 1 := by
    exact aux_gowersRestrict_ae_one_bounded (Set.Icc a b) f₀ hf₀_one_bounded
  have hgmeas : ∀ i : Fin 4, AEStronglyMeasurable (g i) volume := by
    intro i
    fin_cases i
    · exact hf₀'meas
    · exact aux_u3_shift_star_indicator_aestronglyMeasurable (Set.Icc a b) hAmeas f₀
        hf₀_measurable (h ^ (2 : ℕ))
    · exact hf₁_measurable
    · have hshift : AEStronglyMeasurable
          (fun y : ℝ ↦ f₁ (y + h - h ^ (2 : ℕ))) volume := by
        simpa only [sub_eq_add_neg, add_assoc, Function.comp_def] using
          hf₁_measurable.comp_quasiMeasurePreserving
            (measurePreserving_add_right volume (h - h ^ (2 : ℕ))).quasiMeasurePreserving
      exact hshift.star
  have hgbound : ∀ i : Fin 4, ∀ᵐ x ∂volume, ‖g i x‖ ≤ 1 := by
    intro i
    fin_cases i
    · exact hf₀'bound
    · exact aux_u3_shift_star_indicator_ae_one_bounded (Set.Icc a b) f₀
        hf₀_one_bounded (h ^ (2 : ℕ))
    · exact hf₁_one_bounded
    · have hshift : ∀ᵐ x ∂volume, ‖f₁ (x + h - h ^ (2 : ℕ))‖ ≤ 1 := by
        simpa only [sub_eq_add_neg, add_assoc] using
          ((measurePreserving_add_right volume (h - h ^ (2 : ℕ))).quasiMeasurePreserving
            |>.tendsto_ae.eventually hf₁_one_bounded)
      filter_upwards [hshift] with x hx
      change ‖starRingEnd ℂ (f₁ (x + h - h ^ (2 : ℕ)))‖ ≤ 1
      simpa using hx
  have hg0support : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → g 0 x = 0 := by
    filter_upwards with x
    intro hx
    simp [g, f₀', Set.indicator_of_notMem hx]
  have hg1compact : HasCompactSupport (g 1) := by
    exact aux_u3_hasCompactSupport_shift_star_indicator (Set.Icc a b) hAcompact f₀
      (h ^ (2 : ℕ))
  have hc_zero : c 0 = 0 := by simp [c]
  have hc_sep : ∀ i j : Fin 4, i < j → δ ≤ |c i - c j| := by
    simpa only [c] using hsep
  have hc_bound : ∀ i j : Fin 4, i < j → |c i - c j| ≤ M := by
    simpa only [c] using hbound
  have hraw := gowersDifferencing (Set.Icc a b) (Set.Icc p q) ψh
    ⟨a, b, hab, rfl⟩ ⟨p, q, hpq, rfl⟩ hψh_smooth hψh_compact
    hψh_nonneg hψh_le_one hψh_support δ M hδ_pos hδ_le_one hM_one c hc_zero hc_sep hc_bound
    g hgmeas hgbound hg0support hg1compact
  have hfg : f₀' =ᵐ[volume] f₀ := by
    simpa only [f₀', aux_gowersRestrict] using
      aux_u3_restrict_eq_ae_of_ae_zero_outside (Set.Icc a b) f₀ hf₀_support
  have hu₀' : uNorm 3 f₀' = uNorm 3 f₀ := aux_u3_uNorm_three_congr_ae f₀' f₀ hfg
  have hg1unorm : uNorm 3 (fun y : ℝ ↦ starRingEnd ℂ (f₀' (y - h ^ (2 : ℕ)))) =
      uNorm 3 f₀ := by
    calc
      uNorm 3 (fun y : ℝ ↦ starRingEnd ℂ (f₀' (y - h ^ (2 : ℕ)))) =
          uNorm 3 (fun y : ℝ ↦ f₀' (y - h ^ (2 : ℕ))) :=
        aux_u3_uNorm_three_star _
      _ = uNorm 3 f₀' := by
        simpa only [sub_eq_add_neg] using aux_u3_uNorm_three_translate f₀' (-(h ^ (2 : ℕ)))
      _ = uNorm 3 f₀ := hu₀'
  change
    ENNReal.ofReal ‖∫ x : ℝ, ∫ t : ℝ,
        f₀' x *
          starRingEnd ℂ (f₀' (x + (-2 * h) * t - h ^ (2 : ℕ))) *
          f₁ (x + 1 * t) *
          starRingEnd ℂ (f₁ (x + (1 - 2 * h) * t + h - h ^ (2 : ℕ))) *
          ((χ t * χ (t + h) : ℝ) : ℂ)‖ ≤
      ENNReal.ofReal
          (C_gowersDifferencing (Set.Icc a b) (Set.Icc p q)
            (fun t : ℝ ↦ χ t * χ (t + h)) * M * δ ^ (-(3 / 2 : ℝ))) *
        uNorm 3 (fun y : ℝ ↦ starRingEnd ℂ (f₀' (y - h ^ (2 : ℕ))))
    at hraw
  rw [hg1unorm] at hraw
  simp only [ofReal_norm] at hraw
  convert hraw using 1
  · rw [ofReal_norm]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    apply integral_congr_ae
    filter_upwards with t
    dsimp [f₀']
    ring_nf

/-- Elementary real `rpow` evaluation used in the selected-parameter
constant calculation. -/
lemma aux_u3_rpow_square_three_halves (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (2 : ℕ)) ^ (3 / 2 : ℝ) = x ^ (3 : ℕ) := by
  rw [← Real.rpow_natCast x 2]
  rw [← Real.rpow_mul hx]
  norm_num

/-- A companion `rpow` evaluation for the fourth power of the ambient
size parameter. -/
lemma aux_u3_rpow_six_three_halves (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (4 : ℕ)) ^ (3 / 2 : ℝ) = x ^ (6 : ℕ) := by
  rw [← Real.rpow_natCast x 4]
  rw [← Real.rpow_mul hx]
  norm_num

/-- The numerical part of the selected-difference reciprocal power. -/
lemma aux_u3_sixteen_rpow_three_halves : (16 : ℝ) ^ (3 / 2 : ℝ) = 64 := by
  norm_num [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num,
    ← Real.rpow_natCast (2 : ℝ) 4, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- Exact evaluation of the separation scale raised to `-3/2`. -/
lemma aux_u3_delta_rpow
    (I S : ℝ) (hI : 0 < I) (hS : 0 < S) :
    (I ^ (2 : ℕ) / (16 * S ^ (4 : ℕ))) ^ (-(3 / 2 : ℝ)) =
      64 * S ^ (6 : ℕ) / I ^ (3 : ℕ) := by
  have hnum : 0 ≤ I ^ (2 : ℕ) := sq_nonneg I
  have hden : 0 ≤ 16 * S ^ (4 : ℕ) := by positivity
  rw [show -(3 / 2 : ℝ) = -(3 / 2 : ℝ) by ring,
    Real.rpow_neg (by positivity : 0 ≤ I ^ (2 : ℕ) / (16 * S ^ (4 : ℕ)))]
  rw [Real.div_rpow hnum hden]
  rw [aux_u3_rpow_square_three_halves I hI.le]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16) (pow_nonneg hS.le _)]
  rw [aux_u3_sixteen_rpow_three_halves, aux_u3_rpow_six_three_halves S hS.le]
  field_simp

/-- Replaces the selected fixed-parameter Gowers estimate by the uniform
product-cutoff coefficient bound. -/
lemma aux_u3_selected_from_fixed
    (I S Cg δ F : ℝ) (U3 : ℝ≥0∞)
    (hS : 0 < S) (hδ : δ = I ^ (2 : ℕ) / (16 * S ^ (4 : ℕ)))
    (hthreshold : ENNReal.ofReal (I ^ (2 : ℕ) / (4 * S ^ (2 : ℕ))) ≤
      ENNReal.ofReal F)
    (hfixed : ENNReal.ofReal F ≤
      ENNReal.ofReal (Cg * (4 * S) * δ ^ (-(3 / 2 : ℝ))) * U3)
    (hCg : Cg ≤ 64 * S ^ (2 : ℕ)) :
    ENNReal.ofReal (I ^ (2 : ℕ) / (4 * S ^ (2 : ℕ))) ≤
      ENNReal.ofReal
        (64 * S ^ (2 : ℕ) * (4 * S) *
          (I ^ (2 : ℕ) / (16 * S ^ (4 : ℕ))) ^ (-(3 / 2 : ℝ))) * U3 := by
  have hδpow0 : 0 ≤ δ ^ (-(3 / 2 : ℝ)) := by
    rw [hδ]
    exact Real.rpow_nonneg (by positivity) _
  have hscalar : Cg * (4 * S) * δ ^ (-(3 / 2 : ℝ)) ≤
      64 * S ^ (2 : ℕ) * (4 * S) *
        (I ^ (2 : ℕ) / (16 * S ^ (4 : ℕ))) ^ (-(3 / 2 : ℝ)) := by
    rw [← hδ]
    have hmul0 : 0 ≤ (4 * S) * δ ^ (-(3 / 2 : ℝ)) := by positivity
    nlinarith
  calc
    ENNReal.ofReal (I ^ (2 : ℕ) / (4 * S ^ (2 : ℕ))) ≤ ENNReal.ofReal F :=
      hthreshold
    _ ≤ ENNReal.ofReal (Cg * (4 * S) * δ ^ (-(3 / 2 : ℝ))) * U3 := hfixed
    _ ≤ ENNReal.ofReal
          (64 * S ^ (2 : ℕ) * (4 * S) *
            (I ^ (2 : ℕ) / (16 * S ^ (4 : ℕ))) ^ (-(3 / 2 : ℝ))) * U3 := by
      simpa [mul_comm] using
        (mul_le_mul_right (ENNReal.ofReal_le_ofReal hscalar) U3)

/-- Clearing the selected-parameter denominator produces the fifth-power
estimate used at the end of `u3Control`. -/
lemma aux_u3_fifth_power_from_selected
    (I S : ℝ) (U : ℝ≥0∞)
    (hI : 0 < I) (hS : 0 < S)
    (hselected :
      ENNReal.ofReal (I ^ (2 : ℕ) / (4 * S ^ (2 : ℕ))) ≤
        ENNReal.ofReal
          (64 * S ^ (2 : ℕ) * (4 * S) *
            (I ^ (2 : ℕ) / (16 * S ^ (4 : ℕ))) ^ (-(3 / 2 : ℝ))) * U) :
    (ENNReal.ofReal I) ^ (5 : ℕ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (16 : ℕ) * S ^ (11 : ℕ)) * U := by
  let P : ℝ := 4 * S ^ (2 : ℕ) * I ^ (3 : ℕ)
  let B : ℝ := 64 * S ^ (2 : ℕ) * (4 * S) *
    (I ^ (2 : ℕ) / (16 * S ^ (4 : ℕ))) ^ (-(3 / 2 : ℝ))
  have hP0 : 0 ≤ P := by
    dsimp [P]
    positivity
  have hscalarReal : P * B = (2 : ℝ) ^ (16 : ℕ) * S ^ (11 : ℕ) := by
    dsimp [P, B]
    rw [aux_u3_delta_rpow I S hI hS]
    field_simp [hI.ne']
    ring
  have hleft : (ENNReal.ofReal I) ^ (5 : ℕ) =
      ENNReal.ofReal P * ENNReal.ofReal (I ^ (2 : ℕ) / (4 * S ^ (2 : ℕ))) := by
    rw [← ENNReal.ofReal_pow hI.le 5]
    rw [← ENNReal.ofReal_mul hP0]
    congr 1
    dsimp [P]
    field_simp [hI.ne', hS.ne']
  have hscalarENN : ENNReal.ofReal P * ENNReal.ofReal B =
      ENNReal.ofReal ((2 : ℝ) ^ (16 : ℕ) * S ^ (11 : ℕ)) := by
    rw [← ENNReal.ofReal_mul hP0, hscalarReal]
  calc
    (ENNReal.ofReal I) ^ (5 : ℕ) =
        ENNReal.ofReal P * ENNReal.ofReal (I ^ (2 : ℕ) / (4 * S ^ (2 : ℕ))) := hleft
    _ ≤ ENNReal.ofReal P * (ENNReal.ofReal B * U) :=
      mul_le_mul_right hselected (ENNReal.ofReal P)
    _ = (ENNReal.ofReal P * ENNReal.ofReal B) * U := by ring
    _ = ENNReal.ofReal ((2 : ℝ) ^ (16 : ℕ) * S ^ (11 : ℕ)) * U := by
      rw [hscalarENN]

/-- The final fifth-root conversion from the real coefficient bound to the
stated ENNReal `u³` estimate. -/
lemma aux_u3_final_from_fifth
    (I S : ℝ) (U : ℝ≥0∞)
    (hS : 2 ≤ S)
    (hfive : (ENNReal.ofReal I) ^ (5 : ℕ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (16 : ℕ) * S ^ (11 : ℕ)) * U) :
    ENNReal.ofReal I ≤
      ENNReal.ofReal ((2 : ℝ) ^ (4 : ℕ) * S ^ (3 : ℕ)) *
        U ^ (1 / (5 : ℝ)) := by
  let C : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (4 : ℕ) * S ^ (3 : ℕ))
  have hS0 : 0 ≤ S := by linarith
  have hS1 : 1 ≤ S := by linarith
  have hC0 : 0 ≤ (2 : ℝ) ^ (4 : ℕ) * S ^ (3 : ℕ) := by positivity
  have hcoeffReal : (2 : ℝ) ^ (16 : ℕ) * S ^ (11 : ℕ) ≤
      ((2 : ℝ) ^ (4 : ℕ) * S ^ (3 : ℕ)) ^ (5 : ℕ) := by
    have htwopow : (2 : ℝ) ^ (16 : ℕ) ≤ (2 : ℝ) ^ (20 : ℕ) :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)
    have hSpow : S ^ (11 : ℕ) ≤ S ^ (15 : ℕ) :=
      pow_le_pow_right₀ hS1 (by norm_num)
    calc
      (2 : ℝ) ^ (16 : ℕ) * S ^ (11 : ℕ) ≤
          (2 : ℝ) ^ (20 : ℕ) * S ^ (11 : ℕ) :=
        mul_le_mul_of_nonneg_right htwopow (pow_nonneg hS0 _)
      _ ≤ (2 : ℝ) ^ (20 : ℕ) * S ^ (15 : ℕ) :=
        mul_le_mul_of_nonneg_left hSpow (by positivity)
      _ = ((2 : ℝ) ^ (4 : ℕ) * S ^ (3 : ℕ)) ^ (5 : ℕ) := by ring
  have hcoeffENN : ENNReal.ofReal ((2 : ℝ) ^ (16 : ℕ) * S ^ (11 : ℕ)) ≤ C ^ (5 : ℕ) := by
    calc
      ENNReal.ofReal ((2 : ℝ) ^ (16 : ℕ) * S ^ (11 : ℕ)) ≤
          ENNReal.ofReal (((2 : ℝ) ^ (4 : ℕ) * S ^ (3 : ℕ)) ^ (5 : ℕ)) :=
        ENNReal.ofReal_le_ofReal hcoeffReal
      _ = C ^ (5 : ℕ) := by
        dsimp [C]
        exact ENNReal.ofReal_pow hC0 5
  have hfive' : (ENNReal.ofReal I) ^ (5 : ℕ) ≤ C ^ (5 : ℕ) * U :=
    hfive.trans (mul_le_mul_left hcoeffENN U)
  have htargetpow : (C * U ^ (1 / (5 : ℝ))) ^ (5 : ℕ) = C ^ (5 : ℕ) * U := by
    rw [← ENNReal.rpow_natCast (C * U ^ (1 / (5 : ℝ))) 5]
    rw [ENNReal.mul_rpow_of_nonneg C (U ^ (1 / (5 : ℝ)))
      (z := ((5 : ℕ) : ℝ)) (by norm_num)]
    rw [ENNReal.rpow_natCast C 5]
    rw [← ENNReal.rpow_mul]
    norm_num
  have hroot : (ENNReal.ofReal I) ^ (5 : ℝ) ≤
      (C * U ^ (1 / (5 : ℝ))) ^ (5 : ℝ) := by
    change (ENNReal.ofReal I) ^ ((5 : ℕ) : ℝ) ≤
      (C * U ^ (1 / (5 : ℝ))) ^ ((5 : ℕ) : ℝ)
    rw [ENNReal.rpow_natCast (ENNReal.ofReal I) 5,
      ENNReal.rpow_natCast (C * U ^ (1 / (5 : ℝ))) 5, htargetpow]
    exact hfive'
  simpa only [C] using
    (ENNReal.rpow_le_rpow_iff (by norm_num : 0 < (5 : ℝ))).mp hroot

/-- Complete numerical endgame after a selected parameter has supplied its
superlevel bound and fixed-parameter Gowers estimate. -/
lemma aux_u3_numerical_assembly
    (I S Cg δ F : ℝ) (U3 : ℝ≥0∞)
    (hI : 0 < I) (hS : 2 ≤ S)
    (hδ : δ = I ^ (2 : ℕ) / (16 * S ^ (4 : ℕ)))
    (hthreshold : ENNReal.ofReal (I ^ (2 : ℕ) / (4 * S ^ (2 : ℕ))) ≤
      ENNReal.ofReal F)
    (hfixed : ENNReal.ofReal F ≤
      ENNReal.ofReal (Cg * (4 * S) * δ ^ (-(3 / 2 : ℝ))) * U3)
    (hCg : Cg ≤ 64 * S ^ (2 : ℕ)) :
    ENNReal.ofReal I ≤
      ENNReal.ofReal ((2 : ℝ) ^ (4 : ℕ) * S ^ (3 : ℕ)) *
        U3 ^ (1 / (5 : ℝ)) := by
  have hSpos : 0 < S := by linarith
  have hselected := aux_u3_selected_from_fixed I S Cg δ F U3
    hSpos hδ hthreshold hfixed hCg
  exact aux_u3_final_from_fifth I S U3 hS
    (aux_u3_fifth_power_from_selected I S U3 hI hSpos hselected)

/-- Selects a shift in the cutoff difference set whose four associated
points are separated and whose correlation is quantitatively large. -/
lemma aux_u3_select_separated_shift
    (A C J : Set ℝ) (χ : ℝ → ℝ)
    (hA : ∃ a b : ℝ, a < b ∧ A = Set.Icc a b)
    (hC : ∃ a b : ℝ, a < b ∧ C = Set.Icc a b)
    (hJ : ∃ a b : ℝ, a < b ∧ J = Set.Icc a b)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (_hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (hχ_support : tsupport χ ⊆ J)
    (f₀ f₁ f₂ : ℝ → ℂ)
    (hf_measurable : ∀ i : Fin 3, AEStronglyMeasurable (![f₀, f₁, f₂] i) volume)
    (hf_one_bounded : ∀ i : Fin 3, ∀ᵐ x ∂volume, ‖![f₀, f₁, f₂] i x‖ ≤ 1)
    (hf_zero_support : ∀ᵐ x ∂volume, x ∉ A → f₀ x = 0)
    (hf_two_support : ∀ᵐ x ∂volume, x ∉ C → f₂ x = 0)
    (hIpos : 0 < trilinearFormAbs χ f₀ f₁ f₂) :
    ∃ h ∈ Set.image2 (fun s t : ℝ ↦ s - t) J J,
      (∀ i j : Fin 4, i ≠ j →
        (trilinearFormAbs χ f₀ f₁ f₂) ^ (2 : ℕ) /
            (4 * sizeParameter ![A, C, J] χ ^ (4 : ℕ)) / 4 ≤
          |(![0, -2 * h, 1, 1 - 2 * h] i : ℝ) -
            (![0, -2 * h, 1, 1 - 2 * h] j : ℝ)|) ∧
      (trilinearFormAbs χ f₀ f₁ f₂) ^ (2 : ℕ) /
          (4 * sizeParameter ![A, C, J] χ ^ (2 : ℕ)) ≤
        ‖∫ x : ℝ, ∫ t : ℝ,
          aux_u3_correlationIntegrand h (aux_gowersRestrict A f₀) f₁ χ x t‖ := by
  let f₀A : ℝ → ℂ := aux_gowersRestrict A f₀
  let I : ℝ := trilinearFormAbs χ f₀ f₁ f₂
  let S : ℝ := sizeParameter ![A, C, J] χ
  let D : Set ℝ := Set.image2 (fun s t : ℝ ↦ s - t) J J
  let F : ℝ → ℝ := fun h ↦
    ‖∫ x : ℝ, ∫ t : ℝ, aux_u3_correlationIntegrand h f₀A f₁ χ x t‖
  rcases hA with ⟨a0, a1, ha, hAeq⟩
  rcases hC with ⟨c0, c1, hc, hCeq⟩
  rcases hJ with ⟨j0, j1, hj, hJeq⟩
  have hAcompact : IsCompact A := by rw [hAeq]; exact isCompact_Icc
  have hCcompact : IsCompact C := by rw [hCeq]; exact isCompact_Icc
  have hJcompact : IsCompact J := by rw [hJeq]; exact isCompact_Icc
  have hAmeas : MeasurableSet A := hAcompact.isClosed.measurableSet
  have hf₀A_meas : AEStronglyMeasurable f₀A volume := by
    dsimp [f₀A]
    exact (hf_measurable 0).indicator hAmeas
  have hf₀A_bound : ∀ᵐ x ∂volume, ‖f₀A x‖ ≤ 1 := by
    dsimp [f₀A]
    exact aux_gowersRestrict_ae_one_bounded A f₀ (hf_one_bounded 0)
  have hf₀A_support : ∀ x : ℝ, x ∉ A → f₀A x = 0 := by
    intro x hx
    simp [f₀A, aux_gowersRestrict, hx]
  have hf₀A_eq : f₀A =ᵐ[volume] f₀ := by
    dsimp [f₀A]
    exact aux_u3_restrict_eq_ae_of_ae_zero_outside A f₀ hf_zero_support
  have hform_eq : trilinearForm χ f₀A f₁ f₂ = trilinearForm χ f₀ f₁ f₂ := by
    unfold trilinearForm
    apply integral_congr_ae
    filter_upwards [hf₀A_eq] with x hx
    apply integral_congr_ae
    filter_upwards with t
    rw [hx]
  have houter : trilinearForm χ f₀A f₁ f₂ =
      ∫ y : ℝ, f₂ y * ∫ t : ℝ, aux_u3_kernel f₀A f₁ χ y t := by
    exact aux_u3_trilinearForm_eq_u3Outer A J hAcompact hJcompact f₀A f₁ f₂ χ
      hf₀A_meas (hf_measurable 1) (hf_measurable 2)
      hf₀A_bound (hf_one_bounded 1) (hf_one_bounded 2) hf₀A_support
      hχ_smooth.continuous hχ_nonneg hχ_le_one hχ_support
  have hIouter : I = ‖∫ y : ℝ, f₂ y * ∫ t : ℝ,
      aux_u3_kernel f₀A f₁ χ y t‖ := by
    dsimp [I, trilinearFormAbs]
    rw [← hform_eq, houter]
  have henergy_raw := aux_u3_first_cauchy_energy A C J hAcompact hCcompact hJcompact
    f₀A f₁ f₂ χ hf₀A_meas (hf_measurable 1) (hf_measurable 2)
    hf₀A_bound (hf_one_bounded 1) (hf_one_bounded 2) hf₀A_support hf_two_support
    hχ_smooth.continuous hχ_nonneg hχ_le_one hχ_support
  have henergy : I ^ (2 : ℕ) ≤ volume.real C * ∫ h : ℝ, F h := by
    rw [hIouter]
    simpa only [F, aux_u3_correlationIntegrand] using henergy_raw
  let X : Set ℝ := aux_u3_spatialRange A J
  let Q : ℝ → ℝ → ℂ := aux_u3_kernel f₀A f₁ χ
  have hXcompact : IsCompact X := by
    dsimp [X]
    exact aux_u3_spatialRange_compact A J hAcompact hJcompact
  have hQmeas : AEStronglyMeasurable (Function.uncurry Q) (volume.prod volume) := by
    dsimp [Q]
    exact aux_u3_kernel_aestronglyMeasurable f₀A f₁ χ
      hf₀A_meas (hf_measurable 1) hχ_smooth.continuous
  have hQbound : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖Q z.1 z.2‖ ≤ 1 := by
    dsimp [Q]
    exact aux_u3_kernel_ae_one_bounded f₀A f₁ χ
      hf₀A_bound (hf_one_bounded 1) hχ_nonneg hχ_le_one
  have hQsupport : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∉ X ×ˢ J → Q z.1 z.2 = 0 := by
    filter_upwards with z
    dsimp [X, Q]
    exact aux_u3_kernel_zero_outside A J f₀A f₁ χ hf₀A_support hχ_support z
  have hR := aux_autocorrelation_integrable_compactSupport X J hXcompact hJcompact Q
    hQmeas hQbound hQsupport
  have hsections := aux_autocorrelation_section_integrable_ae Q hR
  have hcoord : (fun h : ℝ ↦ ∫ x : ℝ, ∫ t : ℝ,
      Q x t * starRingEnd ℂ (Q x (t + h))) =ᵐ[volume]
      (fun h ↦ ∫ x : ℝ, ∫ t : ℝ,
        aux_u3_correlationIntegrand h f₀A f₁ χ x t) := by
    filter_upwards [hsections] with h hh
    dsimp [Q]
    simpa only [aux_u3_correlationIntegrand] using
      aux_u3_kernel_correlation_change f₀A f₁ χ h hh
  have hGint := aux_gowers_autocorrelation_norm_integrable Q hR
  have hcoordNorm : (fun h : ℝ ↦ ‖∫ x : ℝ, ∫ t : ℝ,
      Q x t * starRingEnd ℂ (Q x (t + h))‖) =ᵐ[volume]
      (fun h ↦ ‖∫ x : ℝ, ∫ t : ℝ,
        aux_u3_correlationIntegrand h f₀A f₁ χ x t‖) := by
    filter_upwards [hcoord] with h hh
    rw [hh]
  have hFint : Integrable F volume := by
    dsimp [F]
    exact hGint.congr hcoordNorm
  have hFmeas : AEMeasurable F volume := hFint.aestronglyMeasurable.aemeasurable
  have hFbound : ∀ᵐ h : ℝ ∂volume, F h ≤ volume.real A * volume.real J := by
    filter_upwards with h
    dsimp [F]
    exact aux_u3_correlationIntegrand_norm_integral_le A J hAcompact hJcompact h
      f₀A f₁ χ hf₀A_meas (hf_measurable 1) hf₀A_bound (hf_one_bounded 1)
      hf₀A_support hχ_smooth.continuous hχ_nonneg hχ_le_one hχ_support
  have hGsupport := aux_u3_autocorrelation_norm_ae_support_difference X J Q hQsupport hR
  have hFsupport : ∀ᵐ h : ℝ ∂volume, h ∉ D → F h = 0 := by
    filter_upwards [hGsupport, hcoord] with h hs hc
    intro hnot
    dsimp [F]
    rw [← hc]
    exact hs (by simpa [D] using hnot)
  have hDcompact : IsCompact D := by
    dsimp [D]
    exact aux_isCompact_image2_sub J hJcompact
  have hDmeas : MeasurableSet D := hDcompact.isClosed.measurableSet
  have hDfinite : volume D < ∞ := hDcompact.measure_lt_top
  have hjmeasure : volume.real D ≤ 2 * volume.real J := by
    change volume.real (Set.image2 (fun s t : ℝ ↦ s - t) J J) ≤
      2 * volume.real J
    rw [hJeq]
    rw [aux_u3_difference_set_measure_Icc j0 j1 hj.le]
  have ha_pos : 0 < volume.real A := by
    rw [hAeq]
    rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr ha.le)]
    exact sub_pos.mpr ha
  have hc_pos : 0 < volume.real C := by
    rw [hCeq]
    rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hc.le)]
    exact sub_pos.mpr hc
  have hj_pos : 0 < volume.real J := by
    rw [hJeq]
    rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hj.le)]
    exact sub_pos.mpr hj
  have hlevel := aux_u3_levelSet_measure_lower_ae_ennreal F D I
      (volume.real A) (volume.real C) (volume.real J)
      hFint hFmeas hDmeas hDfinite hFsupport hFbound henergy
      ha_pos hc_pos hj_pos hjmeasure
  rcases hlevel with ⟨E, hEmeas, hEsub, hEmeasure⟩
  have hS_two : 2 ≤ S := by
    dsimp [S, sizeParameter]
    exact le_add_of_nonneg_right (by positivity)
  have hS0 : 0 ≤ S := by linarith
  have hS1 : 1 ≤ S := by linarith
  have haS : volume.real A ≤ S := by
    simpa [S, intervalLength, Measure.real] using aux_u3_intervalLength_le_size_three A C J χ 0
  have hcS : volume.real C ≤ S := by
    simpa [S, intervalLength, Measure.real] using aux_u3_intervalLength_le_size_three A C J χ 1
  have hjS : volume.real J ≤ S := by
    simpa [S, intervalLength, Measure.real] using aux_u3_intervalLength_le_size_three A C J χ 2
  have hIpos' : 0 < I := by simpa [I] using hIpos
  have hIbound : I ≤ volume.real A * volume.real J := by
    let T : ℝ → ℝ → ℂ := fun x t ↦
      f₀A x * f₁ (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ)
    have htri_bound := aux_u3_norm_doubleIntegral_le_measure_product A J hAcompact hJcompact
      T
      (by
        apply (aux_u3_trilinearIntegrand_aestronglyMeasurable f₀A f₁ f₂ χ
          hf₀A_meas (hf_measurable 1) (hf_measurable 2) hχ_smooth.continuous).congr
        filter_upwards with z
        rcases z with ⟨x, t⟩
        rfl)
      (by
        simpa [T, aux_u3_trilinearIntegrand] using
          aux_u3_trilinearIntegrand_ae_one_bounded f₀A f₁ f₂ χ
            hf₀A_bound (hf_one_bounded 1) (hf_one_bounded 2) hχ_nonneg hχ_le_one)
      (by
        filter_upwards with z
        simpa [T, aux_u3_trilinearIntegrand] using
          aux_u3_trilinearIntegrand_zero_outside A J f₀A f₁ f₂ χ
            hf₀A_support hχ_support z)
    dsimp [I, trilinearFormAbs]
    rw [← hform_eq]
    simpa only [T, trilinearForm] using htri_bound
  have hIleS2 : I ≤ S ^ (2 : ℕ) := by
    calc
      I ≤ volume.real A * volume.real J := hIbound
      _ ≤ S * S := mul_le_mul haS hjS hj_pos.le hS0
      _ = S ^ (2 : ℕ) := by ring
  have hI2leS4 : I ^ (2 : ℕ) ≤ S ^ (4 : ℕ) := by
    calc
      I ^ (2 : ℕ) = I * I := by ring
      _ ≤ S ^ (2 : ℕ) * S ^ (2 : ℕ) := mul_self_le_mul_self hIpos'.le hIleS2
      _ = S ^ (4 : ℕ) := by ring
  let m : ℝ := I ^ (2 : ℕ) / (4 * S ^ (4 : ℕ))
  have hm_pos : 0 < m := by
    dsimp [m]
    positivity
  have hm_le_one : m ≤ 1 := by
    dsimp [m]
    apply (div_le_one₀ (by positivity : 0 < 4 * S ^ (4 : ℕ))).mpr
    nlinarith
  have hprod : volume.real C * volume.real J * volume.real A ≤ S ^ (3 : ℕ) := by
    have hcj : volume.real C * volume.real J ≤ S * S :=
      mul_le_mul hcS hjS hj_pos.le hS0
    calc
      volume.real C * volume.real J * volume.real A ≤ (S * S) * volume.real A :=
        mul_le_mul_of_nonneg_right hcj ha_pos.le
      _ ≤ (S * S) * S := mul_le_mul_of_nonneg_left haS (mul_nonneg hS0 hS0)
      _ = S ^ (3 : ℕ) := by ring
  have hden : 2 * volume.real C * volume.real J * volume.real A ≤ 4 * S ^ (4 : ℕ) := by
    calc
      2 * volume.real C * volume.real J * volume.real A =
          2 * (volume.real C * volume.real J * volume.real A) := by ring
      _ ≤ 2 * S ^ (3 : ℕ) := mul_le_mul_of_nonneg_left hprod (by positivity)
      _ ≤ 4 * S ^ (4 : ℕ) := by
        have hpow : S ^ (3 : ℕ) ≤ S ^ (4 : ℕ) :=
          pow_le_pow_right₀ hS1 (by norm_num)
        nlinarith
  have hm_lower : m ≤ (2 * volume.real C * volume.real J * volume.real A)⁻¹ * I ^ (2 : ℕ) := by
    dsimp [m]
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_left (sq_nonneg I)
      (by positivity : 0 < 2 * volume.real C * volume.real J * volume.real A) hden
  have hm_measure : ENNReal.ofReal m ≤ volume E := by
    calc
      ENNReal.ofReal m ≤ ENNReal.ofReal
          ((2 * volume.real C * volume.real J * volume.real A)⁻¹ * I ^ (2 : ℕ)) :=
        ENNReal.ofReal_le_ofReal hm_lower
      _ ≤ volume E := hEmeasure
  rcases separationSelection E hEmeas m hm_pos hm_le_one hm_measure with
    ⟨h, hhE, hsep⟩
  have hhD : h ∈ D := (hEsub hhE).1
  have hthreshold : (4 * volume.real C * volume.real J)⁻¹ * I ^ (2 : ℕ) ≤ F h :=
    (hEsub hhE).2
  have hthreshold' : I ^ (2 : ℕ) / (4 * S ^ (2 : ℕ)) ≤ F h := by
    have hcj : volume.real C * volume.real J ≤ S * S :=
      mul_le_mul hcS hjS hj_pos.le hS0
    have hden' : 4 * volume.real C * volume.real J ≤ 4 * S ^ (2 : ℕ) := by
      nlinarith
    have hdiv : I ^ (2 : ℕ) / (4 * S ^ (2 : ℕ)) ≤
        I ^ (2 : ℕ) / (4 * volume.real C * volume.real J) :=
      div_le_div_of_nonneg_left (sq_nonneg I)
        (by positivity : 0 < 4 * volume.real C * volume.real J) hden'
    rw [inv_mul_eq_div] at hthreshold
    exact hdiv.trans hthreshold
  refine ⟨h, ?_, ?_, ?_⟩
  · simpa [D] using hhD
  · intro i j hij
    simpa [I, S, m] using hsep i j hij
  · simpa [I, S, F, f₀A] using hthreshold'

/-- The constant in \(\label{prop:u3-control}\), used by `u3Control`:
\[
C_{\ref{prop:u3-control},\,A,C,J,\chi}
:=
2^4\Ssize{A,C,J}{\chi}^{3}.
\]
-/
def C_u3Control (A C J : Set ℝ) (χ : ℝ → ℝ) : ℝ :=
  (2 : ℝ) ^ 4 * sizeParameter ![A, C, J] χ ^ 3

/--
Let $A,C,J$ be positive-length compact intervals. Let $\chi\in C_c^\infty(\R)$ satisfy
$0\leq\chi\leq1$ and $\supp\chi\subset J$. Define
\[
C_{\ref{prop:u3-control},\,A,C,J,\chi}
:=
2^4\Ssize{A,C,J}{\chi}^{3}.
\]
If $f_0,f_1,f_2$ are $1$-bounded, $f_0$ is supported in $A$, and $f_2$ is
supported in $C$, then
\[
\Ichi(f_0,f_1,f_2)
\leq
C_{\ref{prop:u3-control},\,A,C,J,\chi}
\uNorm{f_0}3^{1/5}.
\]
-/
theorem u3Control
    (A C J : Set ℝ) (χ : ℝ → ℝ)
    (hA : ∃ a b : ℝ, a < b ∧ A = Set.Icc a b)
    (hC : ∃ a b : ℝ, a < b ∧ C = Set.Icc a b)
    (hJ : ∃ a b : ℝ, a < b ∧ J = Set.Icc a b)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (hχ_support : tsupport χ ⊆ J)
    (f₀ f₁ f₂ : ℝ → ℂ)
    (hf_measurable : ∀ i : Fin 3, AEStronglyMeasurable (![f₀, f₁, f₂] i) volume)
    (hf_one_bounded : ∀ i : Fin 3, ∀ᵐ x ∂volume, ‖![f₀, f₁, f₂] i x‖ ≤ 1)
    (hf_zero_support : ∀ᵐ x ∂volume, x ∉ A → f₀ x = 0)
    (hf_two_support : ∀ᵐ x ∂volume, x ∉ C → f₂ x = 0) :
    ENNReal.ofReal (trilinearFormAbs χ f₀ f₁ f₂) ≤
      ENNReal.ofReal (C_u3Control A C J χ) * uNorm 3 f₀ ^ (1 / (5 : ℝ)) := by
  let I : ℝ := trilinearFormAbs χ f₀ f₁ f₂
  let S : ℝ := sizeParameter ![A, C, J] χ
  have hS : 2 ≤ S := by
    dsimp [S, sizeParameter]
    exact le_add_of_nonneg_right (by positivity)
  have hS0 : 0 ≤ S := by linarith
  have hSpos : 0 < S := by linarith
  have hI0 : 0 ≤ I := by
    dsimp [I, trilinearFormAbs]
    exact norm_nonneg _
  change ENNReal.ofReal I ≤
    ENNReal.ofReal (C_u3Control A C J χ) * uNorm 3 f₀ ^ (1 / (5 : ℝ))
  by_cases hIzero : I = 0
  · simp [hIzero]
  have hIpos : 0 < I := lt_of_le_of_ne hI0 (Ne.symm hIzero)
  rcases aux_u3_select_separated_shift A C J χ hA hC hJ hχ_smooth hχ_compact
      hχ_nonneg hχ_le_one hχ_support f₀ f₁ f₂ hf_measurable hf_one_bounded
      hf_zero_support hf_two_support (by simpa [I] using hIpos) with
    ⟨h, hhD, hsep, hthreshold⟩
  let δ : ℝ := I ^ (2 : ℕ) / (4 * S ^ (4 : ℕ)) / 4
  let Fh : ℝ := ‖∫ x : ℝ, ∫ t : ℝ,
    aux_u3_correlationIntegrand h (aux_gowersRestrict A f₀) f₁ χ x t‖
  have hδformula : δ = I ^ (2 : ℕ) / (16 * S ^ (4 : ℕ)) := by
    dsimp [δ]
    field_simp [hSpos.ne']
    norm_num
  have hδpos : 0 < δ := by
    rw [hδformula]
    positivity
  have hAcompact : IsCompact A := by
    rcases hA with ⟨a, b, hab, rfl⟩
    exact isCompact_Icc
  have hJcompact : IsCompact J := by
    rcases hJ with ⟨p, q, hpq, rfl⟩
    exact isCompact_Icc
  have hAmeas : MeasurableSet A := hAcompact.isClosed.measurableSet
  have hf₀Ameas : AEStronglyMeasurable (aux_gowersRestrict A f₀) volume := by
    exact (hf_measurable 0).indicator hAmeas
  have hf₀Abound : ∀ᵐ x ∂volume, ‖aux_gowersRestrict A f₀ x‖ ≤ 1 := by
    exact aux_gowersRestrict_ae_one_bounded A f₀ (hf_one_bounded 0)
  have hf₀Asupport : ∀ x : ℝ, x ∉ A → aux_gowersRestrict A f₀ x = 0 := by
    intro x hx
    simp [aux_gowersRestrict, Set.indicator_of_notMem hx]
  have hthreshold' : I ^ (2 : ℕ) / (4 * S ^ (2 : ℕ)) ≤ Fh := by
    simpa [I, S, Fh] using hthreshold
  have hFbound : Fh ≤ volume.real A * volume.real J := by
    dsimp [Fh]
    exact aux_u3_correlationIntegrand_norm_integral_le A J hAcompact hJcompact h
      (aux_gowersRestrict A f₀) f₁ χ hf₀Ameas (hf_measurable 1) hf₀Abound
      (hf_one_bounded 1) hf₀Asupport hχ_smooth.continuous hχ_nonneg hχ_le_one hχ_support
  have hA_size : volume.real A ≤ S := by
    simpa [S, intervalLength, Measure.real] using aux_u3_intervalLength_le_size_three A C J χ 0
  have hJ_size : volume.real J ≤ S := by
    simpa [S, intervalLength, Measure.real] using aux_u3_intervalLength_le_size_three A C J χ 2
  have hFboundS : Fh ≤ S ^ (2 : ℕ) := by
    calc
      Fh ≤ volume.real A * volume.real J := hFbound
      _ ≤ S * S := by gcongr
      _ = S ^ (2 : ℕ) := by ring
  have hI2le : I ^ (2 : ℕ) ≤ 4 * S ^ (4 : ℕ) := by
    have hdiv := hthreshold'.trans hFboundS
    field_simp [hSpos.ne'] at hdiv
    nlinarith
  have hδle : δ ≤ 1 := by
    rw [hδformula]
    exact (div_le_one₀ (by positivity : 0 < 16 * S ^ (4 : ℕ))).mpr (by nlinarith)
  have hMone : 1 ≤ 4 * S := by linarith
  have hsep' : ∀ i j : Fin 4, i < j →
      δ ≤ |(![0, -2 * h, 1, 1 - 2 * h] i : ℝ) -
        (![0, -2 * h, 1, 1 - 2 * h] j : ℝ)| := by
    intro i j hij
    simpa [δ, I, S] using hsep i j (ne_of_lt hij)
  have hbound' : ∀ i j : Fin 4, i < j →
      |(![0, -2 * h, 1, 1 - 2 * h] i : ℝ) -
        (![0, -2 * h, 1, 1 - 2 * h] j : ℝ)| ≤ 4 * S := by
    intro i j hij
    have hraw := aux_u3_coefficients_bounded_on_sub A C J χ hJ h hhD i j hij
    exact hraw.trans (by nlinarith)
  have hfixed_raw := aux_u3_fixed_h_gowers_bound A J χ hA hJ hχ_smooth hχ_compact
    hχ_nonneg hχ_le_one hχ_support f₀ f₁ (hf_measurable 0) (hf_measurable 1)
    (hf_one_bounded 0) (hf_one_bounded 1) hf_zero_support h δ (4 * S)
    hδpos hδle hMone hsep' hbound'
  have hfixed : ENNReal.ofReal Fh ≤
      ENNReal.ofReal
        (C_gowersDifferencing A J (fun t : ℝ ↦ χ t * χ (t + h)) * (4 * S) *
          δ ^ (-(3 / 2 : ℝ))) * uNorm 3 f₀ := by
    simpa [Fh, aux_gowersRestrict, aux_u3_correlationIntegrand] using hfixed_raw
  have hsize := aux_u3_productCutoff_size_le_four_mul A C J χ hχ_smooth hχ_compact
    hχ_nonneg hχ_le_one h
  have hCg : C_gowersDifferencing A J (fun t : ℝ ↦ χ t * χ (t + h)) ≤
      64 * S ^ (2 : ℕ) := by
    unfold C_gowersDifferencing
    have hsmall0 : 0 ≤ sizeParameter ![A, J] (fun t : ℝ ↦ χ t * χ (t + h)) := by
      unfold sizeParameter
      positivity
    dsimp [S] at hsize ⊢
    nlinarith [sq_nonneg (sizeParameter ![A, J] (fun t : ℝ ↦ χ t * χ (t + h)) -
      4 * sizeParameter ![A, C, J] χ)]
  have hfinal := aux_u3_numerical_assembly I S
    (C_gowersDifferencing A J (fun t : ℝ ↦ χ t * χ (t + h))) δ Fh (uNorm 3 f₀)
    hIpos hS hδformula (ENNReal.ofReal_le_ofReal hthreshold') hfixed hCg
  simpa [I, S, C_u3Control] using hfinal

end Auto
