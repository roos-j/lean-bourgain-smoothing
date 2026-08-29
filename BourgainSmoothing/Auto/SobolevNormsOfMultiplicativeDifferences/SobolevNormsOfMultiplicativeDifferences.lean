/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import BourgainSmoothing.Auto.QuadraticOscillationAndBilinearSmoothing.QuadraticOscillationAndBilinearSmoothing

/-!
# Sobolev norms of multiplicative differences

Formalizations of the labeled estimates in the corresponding section of
`blueprint/blueprint.tex`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Real FourierTransform Topology Convolution

namespace Auto

/--
The raw-function form of the `L²` Sobolev norm.

The foundational `sobolevNorm` takes an `Lp` representative so that its Fourier
transform is the Plancherel extension.  This wrapper supplies that representative
when it exists, and is zero otherwise.  In the source-facing estimates below,
the bounded compact-support hypotheses prove that the nonzero branch applies.
-/
def aux_sobolevNormRaw (σ : ℝ) (g : ℝ → ℂ) : ℝ≥0∞ := by
  classical
  exact if hg : MemLp g 2 volume then sobolevNorm σ hg.toLp else 0

/--
For `s ≥ 1` and `σ > 0`, the exponent in
`\label{thm:sobolev-difference}` is
\[
\gamma_{s,\sigma}:=\frac{2^s\sigma}{1+2\sigma}.
\]
-/
def gammaSobolevDifference (s : ℕ) (σ : ℝ) : ℝ :=
  (2 : ℝ) ^ s * σ / (1 + 2 * σ)

/-- The constant in `\(\label{thm:sobolev-difference}\)`, used by
`sobolevDifferenceEstimate`:
\[
C_{\ref{thm:sobolev-difference},\,s,A}
:=
2^{s+1}(1+|A|)^{s+1}.
\]
-/
def C_sobolevDifferenceEstimate (s : ℕ) (A : Set ℝ) : ℝ :=
  (2 : ℝ) ^ (s + 1) * (1 + intervalLength A) ^ (s + 1)

/-- Balances the two frequency-splitting powers used in
`sobolevDifferenceEstimate`. -/
lemma aux_sobolevDifference_rpow_balance
    (U : ℝ≥0∞) (hU0 : U ≠ 0) (hUtop : U ≠ ∞)
    (a σ : ℝ) (hσ : 0 < σ) :
    let R : ℝ≥0∞ := U ^ (-(a / (1 + 2 * σ)))
    R ^ (-(2 * σ)) = U ^ (2 * a * σ / (1 + 2 * σ)) ∧
      R * U ^ a = U ^ (2 * a * σ / (1 + 2 * σ)) := by
  dsimp
  have hden : 1 + 2 * σ ≠ 0 := by linarith
  constructor
  · rw [← ENNReal.rpow_mul]
    congr 1
    field_simp
  · rw [← ENNReal.rpow_add _ _ hU0 hUtop]
    congr 1
    field_simp
    ring

/-- Applies the balanced frequency scale in the finite, nonzero uniformity
norm case of `sobolevDifferenceEstimate`. -/
lemma aux_sobolevDifference_optimize
    (X H L U : ℝ≥0∞) (hU0 : U ≠ 0) (hUtop : U ≠ ∞)
    (a σ : ℝ) (hσ : 0 < σ)
    (hX : X ≤
      H * (U ^ (-(a / (1 + 2 * σ)))) ^ (-(2 * σ)) +
        L * (U ^ (-(a / (1 + 2 * σ))) * U ^ a)) :
    X ≤ (H + L) * U ^ (2 * a * σ / (1 + 2 * σ)) := by
  have hbalance := aux_sobolevDifference_rpow_balance U hU0 hUtop a σ hσ
  calc
    X ≤ H * (U ^ (-(a / (1 + 2 * σ)))) ^ (-(2 * σ)) +
          L * (U ^ (-(a / (1 + 2 * σ))) * U ^ a) := hX
    _ = H * U ^ (2 * a * σ / (1 + 2 * σ)) +
          L * U ^ (2 * a * σ / (1 + 2 * σ)) := by
      rw [hbalance.1, hbalance.2]
    _ = (H + L) * U ^ (2 * a * σ / (1 + 2 * σ)) := by
      rw [add_mul]

/-- Converts an all-positive-real-scale high/low estimate into its optimized
extended-real form for `sobolevDifferenceEstimate`. -/
lemma aux_sobolevDifference_optimize_real
    (X H L U : ℝ≥0∞) (hU0 : U ≠ 0) (hUtop : U ≠ ∞)
    (a σ : ℝ) (hσ : 0 < σ)
    (hX : ∀ R : ℝ, 0 < R → X ≤
      H * (ENNReal.ofReal R) ^ (-(2 * σ)) +
        L * ENNReal.ofReal R * U ^ a) :
    X ≤ (H + L) * U ^ (2 * a * σ / (1 + 2 * σ)) := by
  let R : ℝ := U.toReal ^ (-(a / (1 + 2 * σ)))
  have hRpos : 0 < R := by
    dsimp [R]
    exact Real.rpow_pos_of_pos (ENNReal.toReal_pos hU0 hUtop) _
  have hRenn : ENNReal.ofReal R = U ^ (-(a / (1 + 2 * σ))) := by
    dsimp [R]
    rw [← ENNReal.ofReal_rpow_of_pos (ENNReal.toReal_pos hU0 hUtop)]
    exact congrArg (fun V : ℝ≥0∞ ↦ V ^ (-(a / (1 + 2 * σ))))
      (ENNReal.ofReal_toReal hUtop)
  apply aux_sobolevDifference_optimize X H L U hU0 hUtop a σ hσ
  have h := hX R hRpos
  rw [hRenn] at h
  simpa [mul_assoc] using h

/-- Identifies the optimized exponent with `gammaSobolevDifference`. -/
lemma aux_sobolevDifference_balance_exponent
    (s : ℕ) (hs : 1 ≤ s) (σ : ℝ) :
    2 * ((2 : ℝ) ^ (s - 1)) * σ / (1 + 2 * σ) =
      gammaSobolevDifference s σ := by
  unfold gammaSobolevDifference
  have hspos : 0 < s := by omega
  have hpow : (2 : ℝ) ^ s = 2 * (2 : ℝ) ^ (s - 1) := by
    calc
      (2 : ℝ) ^ s = (2 : ℝ) ^ ((s - 1) + 1) := by
        congr 1
        omega
      _ = 2 * (2 : ℝ) ^ (s - 1) := by
        rw [pow_succ]
        ring
  rw [hpow]

/-- Bounds the two splitting coefficients by the stated source constant. -/
lemma aux_sobolevDifference_coefficient_bound
    (s : ℕ) (hs : 1 ≤ s) (m : ℝ) (hm : 0 ≤ m) :
    (2 : ℝ) ^ s * m ^ (s + 1) + 2 * m ^ 2 ≤
      (2 : ℝ) ^ (s + 1) * (1 + m) ^ (s + 1) := by
  have hmone : m ≤ 1 + m := by linarith
  have hone : 1 ≤ 1 + m := by linarith
  have hmain : m ^ (s + 1) ≤ (1 + m) ^ (s + 1) :=
    pow_le_pow_left₀ hm hmone _
  have hsmall : m ^ 2 ≤ (1 + m) ^ (s + 1) := by
    calc
      m ^ 2 ≤ (1 + m) ^ 2 := pow_le_pow_left₀ hm hmone _
      _ ≤ (1 + m) ^ (s + 1) := pow_le_pow_right₀ hone (by omega)
  have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ s := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
      _ ≤ (2 : ℝ) ^ s := pow_le_pow_right₀ (by norm_num) hs
  have hfirst : (2 : ℝ) ^ s * m ^ (s + 1) ≤
      (2 : ℝ) ^ s * (1 + m) ^ (s + 1) :=
    mul_le_mul_of_nonneg_left hmain (by positivity)
  have hsecond : 2 * m ^ 2 ≤ (2 : ℝ) ^ s * (1 + m) ^ (s + 1) := by
    calc
      2 * m ^ 2 ≤ 2 * (1 + m) ^ (s + 1) :=
        mul_le_mul_of_nonneg_left hsmall (by norm_num)
      _ ≤ (2 : ℝ) ^ s * (1 + m) ^ (s + 1) :=
        mul_le_mul_of_nonneg_right htwo (by positivity)
  calc
    (2 : ℝ) ^ s * m ^ (s + 1) + 2 * m ^ 2 ≤
        (2 : ℝ) ^ s * (1 + m) ^ (s + 1) +
          (2 : ℝ) ^ s * (1 + m) ^ (s + 1) := add_le_add hfirst hsecond
    _ = (2 : ℝ) ^ (s + 1) * (1 + m) ^ (s + 1) := by
      rw [pow_succ]
      ring

/-- Performs the finite nonzero branch of the final numerical estimate in
`sobolevDifferenceEstimate`. -/
lemma aux_sobolevDifference_optimize_to_target
    (s : ℕ) (hs : 1 ≤ s) (σ : ℝ) (hσ : 0 < σ) (m : ℝ) (hm : 0 ≤ m)
    (X U : ℝ≥0∞) (hU0 : U ≠ 0) (hUtop : U ≠ ∞)
    (hX : ∀ R : ℝ, 0 < R → X ≤
      ENNReal.ofReal ((2 : ℝ) ^ s * m ^ (s + 1)) *
          (ENNReal.ofReal R) ^ (-(2 * σ)) +
        ENNReal.ofReal (2 * m ^ 2) * ENNReal.ofReal R *
          U ^ ((2 : ℝ) ^ (s - 1))) :
    X ≤ ENNReal.ofReal ((2 : ℝ) ^ (s + 1) * (1 + m) ^ (s + 1)) *
      U ^ gammaSobolevDifference s σ := by
  have hA : 0 ≤ (2 : ℝ) ^ s * m ^ (s + 1) := by positivity
  have hB : 0 ≤ 2 * m ^ 2 := by positivity
  have hopt := aux_sobolevDifference_optimize_real X
    (ENNReal.ofReal ((2 : ℝ) ^ s * m ^ (s + 1)))
    (ENNReal.ofReal (2 * m ^ 2)) U hU0 hUtop
    ((2 : ℝ) ^ (s - 1)) σ hσ hX
  rw [aux_sobolevDifference_balance_exponent s hs σ] at hopt
  have hcoeff :
      ENNReal.ofReal ((2 : ℝ) ^ s * m ^ (s + 1)) + ENNReal.ofReal (2 * m ^ 2) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (s + 1) * (1 + m) ^ (s + 1)) := by
    rw [← ENNReal.ofReal_add hA hB]
    exact ENNReal.ofReal_le_ofReal
      (aux_sobolevDifference_coefficient_bound s hs m hm)
  exact hopt.trans (mul_le_mul_of_nonneg_right hcoeff bot_le)

/-- Shows a nonnegative extended-real quantity is zero when it is bounded by
an arbitrary negative power of every positive frequency scale. -/
lemma aux_sobolevDifference_zero_of_high_frequency_bound
    (X H : ℝ≥0∞) (σ : ℝ) (hσ : 0 < σ) (hHtop : H ≠ ∞)
    (hbound : ∀ R : ℝ, 0 < R →
      X ≤ H * (ENNReal.ofReal R) ^ (-(2 * σ))) :
    X = 0 := by
  have hXtop : X ≠ ∞ := by
    apply ne_of_lt
    calc
      X ≤ H * (ENNReal.ofReal (1 : ℝ)) ^ (-(2 * σ)) := hbound 1 zero_lt_one
      _ = H := by norm_num
      _ < ∞ := lt_top_iff_ne_top.mpr hHtop
  have hreal : X.toReal ≤ 0 := by
    have hlim : Filter.Tendsto
        (fun R : ℝ ↦ H.toReal * R ^ (-(2 * σ))) Filter.atTop (𝓝 0) := by
      simpa using
        (tendsto_const_nhds.mul (tendsto_rpow_neg_atTop (by linarith : 0 < 2 * σ)))
    apply ge_of_tendsto hlim
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
    have hR0 : ENNReal.ofReal R ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hR
    have hpowtop : (ENNReal.ofReal R) ^ (-(2 * σ)) ≠ ∞ := by
      simp [ENNReal.rpow_eq_top_iff, hR0]
    have h := (ENNReal.toReal_le_toReal hXtop
      (ENNReal.mul_ne_top hHtop hpowtop)).mpr (hbound R hR)
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal hR.le] at h
    exact h
  rcases (ENNReal.toReal_eq_zero_iff X).mp
      (le_antisymm hreal ENNReal.toReal_nonneg) with h | h
  · exact h
  · exact (hXtop h).elim

/-- Handles the zero-uniformity-norm branch of the frequency split. -/
lemma aux_sobolevDifference_zero_of_high_low_frequency_bound
    (X H L U : ℝ≥0∞) (a σ : ℝ) (ha : 0 < a) (hσ : 0 < σ)
    (hU : U = 0) (hHtop : H ≠ ∞)
    (hbound : ∀ R : ℝ, 0 < R → X ≤
      H * (ENNReal.ofReal R) ^ (-(2 * σ)) + L * ENNReal.ofReal R * U ^ a) :
    X = 0 := by
  apply aux_sobolevDifference_zero_of_high_frequency_bound X H σ hσ hHtop
  intro R hR
  have hpow : U ^ a = 0 := by
    rw [hU]
    exact ENNReal.zero_rpow_of_pos ha
  simpa [hpow] using hbound R hR

/-- Performs the zero branch of the final numerical estimate in
`sobolevDifferenceEstimate`. -/
lemma aux_sobolevDifference_optimize_zero_to_target
    (s : ℕ) (σ : ℝ) (hσ : 0 < σ) (m : ℝ)
    (X U : ℝ≥0∞) (hU : U = 0)
    (hX : ∀ R : ℝ, 0 < R → X ≤
      ENNReal.ofReal ((2 : ℝ) ^ s * m ^ (s + 1)) *
          (ENNReal.ofReal R) ^ (-(2 * σ)) +
        ENNReal.ofReal (2 * m ^ 2) * ENNReal.ofReal R *
          U ^ ((2 : ℝ) ^ (s - 1))) :
    X ≤ ENNReal.ofReal ((2 : ℝ) ^ (s + 1) * (1 + m) ^ (s + 1)) *
      U ^ gammaSobolevDifference s σ := by
  have hzero := aux_sobolevDifference_zero_of_high_low_frequency_bound X
    (ENNReal.ofReal ((2 : ℝ) ^ s * m ^ (s + 1)))
    (ENNReal.ofReal (2 * m ^ 2)) U ((2 : ℝ) ^ (s - 1)) σ
    (by positivity) hσ hU ENNReal.ofReal_ne_top hX
  rw [hzero]
  exact bot_le

/-- Closes the numerical part of `sobolevDifferenceEstimate` after its
high/low frequency estimate has been established. -/
lemma aux_sobolevDifference_finalize_high_low
    (s : ℕ) (hs : 1 ≤ s) (σ : ℝ) (hσ : 0 < σ) (m : ℝ) (hm : 0 ≤ m)
    (X U : ℝ≥0∞)
    (hX : ∀ R : ℝ, 0 < R → X ≤
      ENNReal.ofReal ((2 : ℝ) ^ s * m ^ (s + 1)) *
          (ENNReal.ofReal R) ^ (-(2 * σ)) +
        ENNReal.ofReal (2 * m ^ 2) * ENNReal.ofReal R *
          U ^ ((2 : ℝ) ^ (s - 1))) :
    X ≤ ENNReal.ofReal ((2 : ℝ) ^ (s + 1) * (1 + m) ^ (s + 1)) *
      U ^ gammaSobolevDifference s σ := by
  by_cases hUtop : U = ∞
  · have hgamma : 0 < gammaSobolevDifference s σ := by
      unfold gammaSobolevDifference
      have hden : 0 < 1 + 2 * σ := by linarith
      exact div_pos (mul_pos (by positivity) hσ) hden
    have hC : 0 < (2 : ℝ) ^ (s + 1) * (1 + m) ^ (s + 1) := by
      positivity
    rw [hUtop, ENNReal.top_rpow_of_pos hgamma,
      ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.2 hC))]
    exact le_top
  by_cases hUzero : U = 0
  · exact aux_sobolevDifference_optimize_zero_to_target s σ hσ m X U hUzero hX
  · exact aux_sobolevDifference_optimize_to_target s hs σ hσ m hm X U hUzero hUtop hX

/-- The reflected, modulated factor whose convolution is the Fourier transform
of a multiplicative difference as a function of the difference parameter. -/
def aux_sobolevDifference_differenceKernel (ξ : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun t ↦ (𝐞 (ξ * t) : ℂ) * g (-t)

/-- The correlation curve in the difference parameter. -/
def aux_sobolevDifference_differenceCorrelation (ξ : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  aux_convolution (aux_sobolevDifference_differenceKernel ξ g)
    (fun x ↦ starRingEnd ℂ (g x))

/-- The convolution correlation curve is exactly the raw Fourier transform of
the corresponding multiplicative difference. -/
lemma aux_sobolevDifference_differenceCorrelation_eq_fourier_difference
    (ξ : ℝ) (g : ℝ → ℂ) (h : ℝ) :
    aux_sobolevDifference_differenceCorrelation ξ g h =
      𝓕 (multiplicativeDifference h g) ξ := by
  rw [aux_sobolevDifference_differenceCorrelation, aux_convolution, Real.fourier_eq]
  rw [← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards with x
  simp only [aux_sobolevDifference_differenceKernel, Circle.smul_def,
    multiplicativeDifference, Real.inner_apply]
  change (𝐞 (ξ * (-x)) : ℂ) * g (-(-x)) * starRingEnd ℂ (g (h - -x)) =
    (𝐞 (-(x * ξ)) : ℂ) * (g x * starRingEnd ℂ (g (x + h)))
  have hphase : ξ * (-x) = -(x * ξ) := by ring
  rw [hphase]
  ring_nf

/-- The reflected-modulated convolution kernel is integrable whenever the
underlying function is integrable. -/
lemma aux_sobolevDifference_differenceKernel_integrable
    (ξ : ℝ) (g : ℝ → ℂ) (hg : Integrable g volume) :
    Integrable (aux_sobolevDifference_differenceKernel ξ g) volume := by
  have hneg : Integrable (fun t : ℝ ↦ g (-t)) volume := by
    apply memLp_one_iff_integrable.mp
    simpa only [Function.comp_def] using
      (memLp_one_iff_integrable.mpr hg).comp_measurePreserving
        (Measure.measurePreserving_neg volume)
  have hphase : AEStronglyMeasurable (fun t : ℝ ↦ (𝐞 (ξ * t) : ℂ)) volume := by
    exact (continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (by fun_prop))).aestronglyMeasurable
  have hmul := hneg.bdd_mul (c := 1) hphase
    (Filter.Eventually.of_forall fun t ↦ by simp)
  change Integrable (fun t : ℝ ↦ (𝐞 (ξ * t) : ℂ) * g (-t)) volume
  exact hmul

/-- Fourier transform of the reflected-modulated convolution kernel. -/
lemma aux_sobolevDifference_fourier_differenceKernel
    (ξ η : ℝ) (g : ℝ → ℂ) :
    𝓕 (aux_sobolevDifference_differenceKernel ξ g) η = 𝓕 g (ξ - η) := by
  change 𝓕 (fun t : ℝ ↦ (𝐞 (ξ * t) : ℂ) * g (-t)) η = 𝓕 g (ξ - η)
  rw [show (fun t : ℝ ↦ (𝐞 (ξ * t) : ℂ) * g (-t)) =
    fun t ↦ (𝐞 (ξ * t) : Circle) • g (-t) by
      funext t
      simp only [Circle.smul_def, smul_eq_mul]]
  rw [aux_fourier_modulate]
  have hreflect := aux_fourier_comp_mul g (-1) (η - ξ) (by norm_num : (-1 : ℝ) ≠ 0)
  rw [show (fun x : ℝ ↦ g ((-1 : ℝ) * x)) = fun x ↦ g (-x) by
    funext x
    congr 1
    ring] at hreflect
  rw [hreflect]
  simp only [inv_neg, inv_one, abs_neg, abs_one, one_smul]
  ring

/-- Plancherel identifies the Fourier transform in the difference parameter
with a product of two raw Fourier transforms. -/
lemma aux_sobolevDifference_l2Fourier_differenceCorrelation_ae
    (ξ : ℝ) (g : ℝ → ℂ)
    (hg1 : MemLp g (1 : ℝ≥0∞) volume)
    (hg2 : MemLp g (2 : ℝ≥0∞) volume) :
    aux_l2Fourier (aux_sobolevDifference_differenceCorrelation ξ g) =ᵐ[volume]
      fun η ↦ (𝓕 g (ξ - η)) * starRingEnd ℂ (𝓕 g (-η)) := by
  have hκ : Integrable (aux_sobolevDifference_differenceKernel ξ g) volume :=
    aux_sobolevDifference_differenceKernel_integrable ξ g
      (memLp_one_iff_integrable.mp hg1)
  have hstarfun : (star g : ℝ → ℂ) = fun x ↦ starRingEnd ℂ (g x) := by
    funext x
    rfl
  have hg1star : MemLp (fun x ↦ starRingEnd ℂ (g x)) (1 : ℝ≥0∞) volume := by
    rw [← hstarfun]
    exact hg1.star
  have hg2star : MemLp (fun x ↦ starRingEnd ℂ (g x)) (2 : ℝ≥0∞) volume := by
    rw [← hstarfun]
    exact hg2.star
  have hconv := aux_l2Fourier_aux_convolution_ae_eq_multiplier
    (aux_sobolevDifference_differenceKernel ξ g) (fun x ↦ starRingEnd ℂ (g x)) hκ hg2star
  have hstar0 := aux_l2Fourier_eq_raw_ae
    (fun x ↦ starRingEnd ℂ (g x)) hg1star hg2star
  have hstar : aux_l2Fourier (fun x ↦ starRingEnd ℂ (g x)) =ᵐ[volume]
      𝓕 (fun x ↦ starRingEnd ℂ (g x)) := by
    rw [aux_l2Fourier, dif_pos hg2star]
    exact hstar0
  change aux_l2Fourier
      (aux_convolution (aux_sobolevDifference_differenceKernel ξ g)
        (fun x ↦ starRingEnd ℂ (g x))) =ᵐ[volume] _
  filter_upwards [hconv, hstar] with η hη hstarη
  rw [hη, hstarη, aux_sobolevDifference_fourier_differenceKernel, aux_fourier_conj]

/-- The correlation curve belongs to `L²` by Young's inequality. -/
lemma aux_sobolevDifference_differenceCorrelation_memLp_two
    (ξ : ℝ) (g : ℝ → ℂ)
    (hg1 : MemLp g (1 : ℝ≥0∞) volume)
    (hg2 : MemLp g (2 : ℝ≥0∞) volume) :
    MemLp (aux_sobolevDifference_differenceCorrelation ξ g) (2 : ℝ≥0∞) volume := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  rw [aux_sobolevDifference_differenceCorrelation]
  have hκ : Integrable (aux_sobolevDifference_differenceKernel ξ g) volume :=
    aux_sobolevDifference_differenceKernel_integrable ξ g
      (memLp_one_iff_integrable.mp hg1)
  have hstarfun : (star g : ℝ → ℂ) = fun x ↦ starRingEnd ℂ (g x) := by
    funext x
    rfl
  have hg2star : MemLp (fun x ↦ starRingEnd ℂ (g x)) (2 : ℝ≥0∞) volume := by
    rw [← hstarfun]
    exact hg2.star
  exact aux_convolution_memLp_of_memLp_one _ _ hκ hg2star

/-- Exact fixed-frequency Plancherel identity behind the low-frequency
estimate. -/
lemma aux_sobolevDifference_eLpNorm_fourier_difference_eq_product
    (ξ : ℝ) (g : ℝ → ℂ)
    (hg1 : MemLp g (1 : ℝ≥0∞) volume)
    (hg2 : MemLp g (2 : ℝ≥0∞) volume) :
    eLpNorm (fun h ↦ 𝓕 (multiplicativeDifference h g) ξ)
      (2 : ℝ≥0∞) volume =
      eLpNorm (fun η ↦ (𝓕 g (ξ - η)) * starRingEnd ℂ (𝓕 g (-η)))
        (2 : ℝ≥0∞) volume := by
  have hcorr : aux_sobolevDifference_differenceCorrelation ξ g =
      fun h ↦ 𝓕 (multiplicativeDifference h g) ξ := by
    funext h
    exact aux_sobolevDifference_differenceCorrelation_eq_fourier_difference ξ g h
  have hmem := aux_sobolevDifference_differenceCorrelation_memLp_two ξ g hg1 hg2
  calc
    eLpNorm (fun h ↦ 𝓕 (multiplicativeDifference h g) ξ)
        (2 : ℝ≥0∞) volume =
        eLpNorm (aux_sobolevDifference_differenceCorrelation ξ g) (2 : ℝ≥0∞) volume := by
      rw [hcorr]
    _ = eLpNorm (aux_l2Fourier (aux_sobolevDifference_differenceCorrelation ξ g))
        (2 : ℝ≥0∞) volume := (aux_eLpNorm_aux_l2Fourier_eq _ hmem).symm
    _ = _ := eLpNorm_congr_ae
      (aux_sobolevDifference_l2Fourier_differenceCorrelation_ae ξ g hg1 hg2)

/-- Squaring an `L²` seminorm recovers its nonnegative energy integral. -/
lemma aux_sobolevDifference_eLpNorm_two_sq_eq_lintegral_enorm
    (F : ℝ → ℂ) :
    (eLpNorm F (2 : ℝ≥0∞) volume) ^ (2 : ℝ) =
      ∫⁻ x : ℝ, ‖F x‖ₑ ^ (2 : ℕ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞), ← ENNReal.rpow_mul]
  norm_num

/-- The fixed-frequency Plancherel identity in squared-energy form. -/
lemma aux_sobolevDifference_lintegral_fourier_difference_eq_product_energy
    (ξ : ℝ) (g : ℝ → ℂ)
    (hg1 : MemLp g (1 : ℝ≥0∞) volume)
    (hg2 : MemLp g (2 : ℝ≥0∞) volume) :
    ∫⁻ h : ℝ, ‖𝓕 (multiplicativeDifference h g) ξ‖ₑ ^ (2 : ℕ) =
      ∫⁻ η : ℝ, ‖(𝓕 g (ξ - η)) * starRingEnd ℂ (𝓕 g (-η))‖ₑ ^ (2 : ℕ) := by
  rw [← aux_sobolevDifference_eLpNorm_two_sq_eq_lintegral_enorm
    (fun h ↦ 𝓕 (multiplicativeDifference h g) ξ),
    aux_sobolevDifference_eLpNorm_fourier_difference_eq_product ξ g hg1 hg2,
    aux_sobolevDifference_eLpNorm_two_sq_eq_lintegral_enorm]

/-- Cauchy--Schwarz controls the overlap of a translate and a reflection by
the squared `L²` size. -/
lemma aux_sobolevDifference_lintegral_enorm_mul_translate_reflect_le
    (F : ℝ → ℂ) (hF : AEStronglyMeasurable F volume) (ξ : ℝ) :
    ∫⁻ η : ℝ, ‖F (ξ - η)‖ₑ * ‖F (-η)‖ₑ ≤
      eLpNorm F (2 : ℝ≥0∞) volume * eLpNorm F (2 : ℝ≥0∞) volume := by
  have hleft : AEStronglyMeasurable (fun η : ℝ ↦ F (ξ - η)) volume := by
    exact hF.comp_measurePreserving (volume.measurePreserving_sub_left ξ)
  have hright : AEStronglyMeasurable (fun η : ℝ ↦ F (-η)) volume := by
    exact hF.comp_measurePreserving (Measure.measurePreserving_neg volume)
  calc
    ∫⁻ η : ℝ, ‖F (ξ - η)‖ₑ * ‖F (-η)‖ₑ ≤
        (∫⁻ η : ℝ, ‖F (ξ - η)‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫⁻ η : ℝ, ‖F (-η)‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
      ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
        hleft.enorm hright.enorm
    _ = eLpNorm (fun η : ℝ ↦ F (ξ - η)) (2 : ℝ≥0∞) volume *
          eLpNorm (fun η : ℝ ↦ F (-η)) (2 : ℝ≥0∞) volume := by
      rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞),
        eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
      norm_num
    _ = _ := by
      have hleftnorm : eLpNorm (fun η : ℝ ↦ F (ξ - η)) (2 : ℝ≥0∞) volume =
          eLpNorm F (2 : ℝ≥0∞) volume := by
        simpa only [Function.comp_def] using
          (eLpNorm_comp_measurePreserving hF (volume.measurePreserving_sub_left ξ)
            (p := (2 : ℝ≥0∞)))
      have hrightnorm : eLpNorm (fun η : ℝ ↦ F (-η)) (2 : ℝ≥0∞) volume =
          eLpNorm F (2 : ℝ≥0∞) volume := by
        simpa only [Function.comp_def] using
          (eLpNorm_comp_measurePreserving hF (Measure.measurePreserving_neg volume)
            (p := (2 : ℝ≥0∞)))
      rw [hleftnorm, hrightnorm]

/-- The product-side energy at one frequency is bounded by one pointwise
Fourier bound, one essential Fourier bound, and the `L²` energy. -/
lemma aux_sobolevDifference_lintegral_squared_fourier_product_le
    (F : ℝ → ℂ) (hF : AEStronglyMeasurable F volume)
    (B M : ℝ≥0∞)
    (hB : ∀ x : ℝ, ‖F x‖ₑ ≤ B)
    (hM : ∀ᵐ x : ℝ ∂volume, ‖F x‖ₑ ≤ M)
    (ξ : ℝ) :
    ∫⁻ η : ℝ, ‖F (ξ - η) * starRingEnd ℂ (F (-η))‖ₑ ^ (2 : ℕ) ≤
      B * M * (eLpNorm F (2 : ℝ≥0∞) volume * eLpNorm F (2 : ℝ≥0∞) volume) := by
  have hMneg : ∀ᵐ η : ℝ ∂volume, ‖F (-η)‖ₑ ≤ M := by
    exact (Measure.measurePreserving_neg volume).quasiMeasurePreserving.tendsto_ae hM
  have hleft : AEStronglyMeasurable (fun η : ℝ ↦ F (ξ - η)) volume := by
    exact hF.comp_measurePreserving (volume.measurePreserving_sub_left ξ)
  have hright : AEStronglyMeasurable (fun η : ℝ ↦ F (-η)) volume := by
    exact hF.comp_measurePreserving (Measure.measurePreserving_neg volume)
  have hprodmeas : AEMeasurable
      (fun η : ℝ ↦ ‖F (ξ - η)‖ₑ * ‖F (-η)‖ₑ) volume :=
    hleft.enorm.mul hright.enorm
  calc
    ∫⁻ η : ℝ, ‖F (ξ - η) * starRingEnd ℂ (F (-η))‖ₑ ^ (2 : ℕ) ≤
        ∫⁻ η : ℝ, B * M * (‖F (ξ - η)‖ₑ * ‖F (-η)‖ₑ) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [hMneg] with η hη
      have hξ : ‖F (ξ - η)‖ₑ ≤ B := hB _
      have hmul : ‖F (ξ - η)‖ₑ * ‖F (-η)‖ₑ ≤ B * M :=
        mul_le_mul hξ hη bot_le bot_le
      have hstar : ‖starRingEnd ℂ (F (-η))‖ₑ = ‖F (-η)‖ₑ := by
        rw [← ofReal_norm]
        change ENNReal.ofReal ‖star (F (-η))‖ = ‖F (-η)‖ₑ
        rw [norm_star, ofReal_norm]
      rw [enorm_mul, hstar, pow_two]
      calc
        (‖F (ξ - η)‖ₑ * ‖F (-η)‖ₑ) * (‖F (ξ - η)‖ₑ * ‖F (-η)‖ₑ) ≤
            (B * M) * (‖F (ξ - η)‖ₑ * ‖F (-η)‖ₑ) :=
          mul_le_mul_left hmul _
        _ = B * M * (‖F (ξ - η)‖ₑ * ‖F (-η)‖ₑ) := by ring
    _ = B * M * ∫⁻ η : ℝ, ‖F (ξ - η)‖ₑ * ‖F (-η)‖ₑ := by
      rw [MeasureTheory.lintegral_const_mul'' (B * M) hprodmeas]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (aux_sobolevDifference_lintegral_enorm_mul_translate_reflect_le F hF ξ) bot_le

/-- The symmetric frequency window has Lebesgue measure `2 * R`. -/
lemma aux_sobolevDifference_lintegral_Icc_const
    (R : ℝ) (_hR : 0 ≤ R) (C : ℝ≥0∞) :
    ∫⁻ ξ : ℝ in Set.Icc (-R) R, C = ENNReal.ofReal (2 * R) * C := by
  rw [MeasureTheory.lintegral_const]
  simp only [Measure.restrict_apply_univ, Real.volume_Icc]
  have hlength : R - -R = 2 * R := by ring
  rw [hlength]
  exact mul_comm _ _

/-- Integrating the product-side estimate over a symmetric frequency window
costs exactly the window length. -/
lemma aux_sobolevDifference_lintegral_squared_fourier_product_Icc_le
    (F : ℝ → ℂ) (hF : AEStronglyMeasurable F volume)
    (B M : ℝ≥0∞)
    (hB : ∀ x : ℝ, ‖F x‖ₑ ≤ B)
    (hM : ∀ᵐ x : ℝ ∂volume, ‖F x‖ₑ ≤ M)
    (R : ℝ) (hR : 0 ≤ R) :
    ∫⁻ ξ : ℝ in Set.Icc (-R) R,
      ∫⁻ η : ℝ, ‖F (ξ - η) * starRingEnd ℂ (F (-η))‖ₑ ^ (2 : ℕ) ≤
      ENNReal.ofReal (2 * R) * B * M *
        (eLpNorm F (2 : ℝ≥0∞) volume * eLpNorm F (2 : ℝ≥0∞) volume) := by
  let C : ℝ≥0∞ := B * M *
    (eLpNorm F (2 : ℝ≥0∞) volume * eLpNorm F (2 : ℝ≥0∞) volume)
  calc
    ∫⁻ ξ : ℝ in Set.Icc (-R) R,
        ∫⁻ η : ℝ, ‖F (ξ - η) * starRingEnd ℂ (F (-η))‖ₑ ^ (2 : ℕ) ≤
        ∫⁻ _ξ : ℝ in Set.Icc (-R) R, C := by
      apply MeasureTheory.lintegral_mono
      intro ξ
      exact aux_sobolevDifference_lintegral_squared_fourier_product_le F hF B M hB hM ξ
    _ = ENNReal.ofReal (2 * R) * C := aux_sobolevDifference_lintegral_Icc_const R hR C
    _ = _ := by
      dsimp [C]
      ring

/-- The three-variable integrand whose integral is the Fourier transform of a
multiplicative difference, viewed jointly in the difference and frequency. -/
def aux_sobolevDifference_jointDifferenceIntegrand (g : ℝ → ℂ) : (ℝ × ℝ) × ℝ → ℂ :=
  fun z ↦ (𝐞 (z.1.2 * z.2) : ℂ) * g (-z.2) * starRingEnd ℂ (g (z.1.1 - z.2))

/-- The raw Fourier transform of multiplicative differences is jointly almost
everywhere strongly measurable in its difference and frequency variables. -/
lemma aux_sobolevDifference_joint_aestronglyMeasurable_fourier_difference
    (g : ℝ → ℂ) (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable
      (fun z : ℝ × ℝ ↦ 𝓕 (multiplicativeDifference z.1 g) z.2)
      (volume.prod volume) := by
  have hneg_map : Measure.QuasiMeasurePreserving
      (fun z : (ℝ × ℝ) × ℝ ↦ -z.2) ((volume.prod volume).prod volume) volume := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.comp
      (Measure.quasiMeasurePreserving_snd
        (μ := (volume : Measure ℝ).prod (volume : Measure ℝ))
        (ν := (volume : Measure ℝ)))
    convert h using 1
    ext z
    rfl
  have hsub_map : Measure.QuasiMeasurePreserving
      (fun z : (ℝ × ℝ) × ℝ ↦ z.1.1 - z.2) ((volume.prod volume).prod volume) volume := by
    refine MeasureTheory.QuasiMeasurePreserving.prod_of_left (by fun_prop) ?_
    filter_upwards with t
    have h := ((Measure.measurePreserving_neg (volume : Measure ℝ)).comp
      (Measure.measurePreserving_sub_left (volume : Measure ℝ) t)).quasiMeasurePreserving.comp
      (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
        (ν := (volume : Measure ℝ)))
    convert h using 1
    ext z
    simp only [Function.comp_apply]
    ring
  have hneg : AEStronglyMeasurable (fun z : (ℝ × ℝ) × ℝ ↦ g (-z.2))
      ((volume.prod volume).prod volume) :=
    hg.comp_quasiMeasurePreserving hneg_map
  have hsub : AEStronglyMeasurable (fun z : (ℝ × ℝ) × ℝ ↦ g (z.1.1 - z.2))
      ((volume.prod volume).prod volume) :=
    hg.comp_quasiMeasurePreserving hsub_map
  have hphase : StronglyMeasurable (fun z : (ℝ × ℝ) × ℝ ↦
      (𝐞 (z.1.2 * z.2) : ℂ)) := by
    exact (continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (by fun_prop))).stronglyMeasurable
  have hint : AEStronglyMeasurable (aux_sobolevDifference_jointDifferenceIntegrand g)
      ((volume.prod volume).prod volume) := by
    exact (hphase.aestronglyMeasurable.mul hneg).mul hsub.star
  have hcorr : AEStronglyMeasurable
      (fun z : ℝ × ℝ ↦ aux_sobolevDifference_differenceCorrelation z.2 g z.1)
      (volume.prod volume) := by
    convert hint.integral_prod_right' using 1
    rfl
  have heq : (fun z : ℝ × ℝ ↦
      aux_sobolevDifference_differenceCorrelation z.2 g z.1) =
      fun z : ℝ × ℝ ↦ 𝓕 (multiplicativeDifference z.1 g) z.2 := by
    funext z
    exact aux_sobolevDifference_differenceCorrelation_eq_fourier_difference z.2 g z.1
  rwa [heq] at hcorr

/-- The nonnegative Fourier energy of a multiplicative difference is jointly
almost everywhere measurable in the difference and frequency variables. -/
lemma aux_sobolevDifference_joint_aemeasurable_fourier_difference_energy
    (g : ℝ → ℂ) (hg : AEStronglyMeasurable g volume) :
    AEMeasurable
      (fun z : ℝ × ℝ ↦ ‖𝓕 (multiplicativeDifference z.1 g) z.2‖ₑ ^ (2 : ℕ))
      (volume.prod volume) := by
  exact (aux_sobolevDifference_joint_aestronglyMeasurable_fourier_difference g hg).enorm.pow
    measurable_const.aemeasurable

/-- Tonelli may swap a Lebesgue integral with an integral over a symmetric
frequency window whenever the integrand is jointly almost everywhere
measurable. -/
lemma aux_sobolevDifference_lintegral_lintegral_swap_Icc
    (K : ℝ → ℝ → ℝ≥0∞) (R : ℝ)
    (hK : AEMeasurable (Function.uncurry K) (volume.prod volume)) :
    (∫⁻ h : ℝ, ∫⁻ ξ : ℝ in Set.Icc (-R) R, K h ξ) =
      ∫⁻ ξ : ℝ in Set.Icc (-R) R, ∫⁻ h : ℝ, K h ξ := by
  have hle : (volume : Measure ℝ).prod
      ((volume : Measure ℝ).restrict (Set.Icc (-R) R)) ≤
      (volume : Measure ℝ).prod (volume : Measure ℝ) := by
    exact Measure.prod_mono le_rfl Measure.restrict_le_self
  have hK' : AEMeasurable (Function.uncurry K)
      ((volume : Measure ℝ).prod
        ((volume : Measure ℝ).restrict (Set.Icc (-R) R))) :=
    hK.mono_measure hle
  change (∫⁻ h : ℝ, ∫⁻ ξ : ℝ, K h ξ ∂(volume.restrict (Set.Icc (-R) R))) =
      ∫⁻ ξ : ℝ, ∫⁻ h : ℝ, K h ξ ∂volume ∂(volume.restrict (Set.Icc (-R) R))
  exact MeasureTheory.lintegral_lintegral_swap hK'

/-- A low-frequency fixed-function estimate for multiplicative differences.
The constant is a pointwise Fourier bound times an essential Fourier bound
times the Fourier `L²` energy, multiplied by the frequency-window length. -/
lemma aux_sobolevDifference_low_frequency_fourier_difference_energy_le
    (g : ℝ → ℂ) (hg : AEStronglyMeasurable g volume)
    (hg1 : MemLp g (1 : ℝ≥0∞) volume)
    (hg2 : MemLp g (2 : ℝ≥0∞) volume)
    (B M : ℝ≥0∞)
    (hB : ∀ ξ : ℝ, ‖𝓕 g ξ‖ₑ ≤ B)
    (hM : ∀ᵐ ξ : ℝ ∂volume, ‖𝓕 g ξ‖ₑ ≤ M)
    (R : ℝ) (hR : 0 ≤ R) :
    (∫⁻ h : ℝ, ∫⁻ ξ : ℝ in Set.Icc (-R) R,
      ‖𝓕 (multiplicativeDifference h g) ξ‖ₑ ^ (2 : ℕ)) ≤
      ENNReal.ofReal (2 * R) * B * M *
        (eLpNorm (𝓕 g) (2 : ℝ≥0∞) volume *
          eLpNorm (𝓕 g) (2 : ℝ≥0∞) volume) := by
  calc
    (∫⁻ h : ℝ, ∫⁻ ξ : ℝ in Set.Icc (-R) R,
        ‖𝓕 (multiplicativeDifference h g) ξ‖ₑ ^ (2 : ℕ)) =
        ∫⁻ ξ : ℝ in Set.Icc (-R) R, ∫⁻ h : ℝ,
          ‖𝓕 (multiplicativeDifference h g) ξ‖ₑ ^ (2 : ℕ) :=
      aux_sobolevDifference_lintegral_lintegral_swap_Icc _ R
        (aux_sobolevDifference_joint_aemeasurable_fourier_difference_energy g hg)
    _ = ∫⁻ ξ : ℝ in Set.Icc (-R) R, ∫⁻ η : ℝ,
        ‖(𝓕 g (ξ - η)) * starRingEnd ℂ (𝓕 g (-η))‖ₑ ^ (2 : ℕ) := by
      apply MeasureTheory.lintegral_congr
      intro ξ
      exact aux_sobolevDifference_lintegral_fourier_difference_eq_product_energy ξ g hg1 hg2
    _ ≤ _ := aux_sobolevDifference_lintegral_squared_fourier_product_Icc_le
      (𝓕 g) (aux_fourier_aestronglyMeasurable g) B M hB hM R hR

/-- For an `L¹ ∩ L²` function, the raw Sobolev norm is the weighted raw
Fourier energy.  This makes the low-frequency estimate applicable to the
source-facing Sobolev wrapper. -/
lemma aux_sobolevDifference_sobolevNormRaw_sq_eq_raw_fourier_energy
    (σ : ℝ) (g : ℝ → ℂ)
    (hg1 : MemLp g (1 : ℝ≥0∞) volume)
    (hg2 : MemLp g (2 : ℝ≥0∞) volume) :
    aux_sobolevNormRaw σ g ^ (2 : ℝ) =
      ∫⁻ ξ : ℝ, ‖(japaneseBracket ξ ^ (-σ)) • 𝓕 g ξ‖ₑ ^ (2 : ℕ) := by
  have hraw : (fun ξ : ℝ ↦
      (Lp.fourierTransformₗᵢ ℝ ℂ (hg2.toLp g)) ξ) =ᵐ[volume] 𝓕 g :=
    aux_l2Fourier_eq_raw_ae g hg1 hg2
  rw [aux_sobolevNormRaw, dif_pos hg2, sobolevNorm,
    aux_sobolevDifference_eLpNorm_two_sq_eq_lintegral_enorm]
  apply MeasureTheory.lintegral_congr_ae
  filter_upwards [hraw] with ξ hξ
  rw [hξ]

/-- The set of possible first-order difference parameters of points in `A`. -/
def aux_sobolevDifference_differenceSet (A : Set ℝ) : Set ℝ :=
  Set.image2 (fun x y : ℝ ↦ x - y) A A

/-- Forgetting the leading parameter and retaining the iterated-difference
tail is quasi-measure-preserving. -/
lemma aux_sobolevDifference_qmp_tail_unshifted (s : ℕ) :
    Measure.QuasiMeasurePreserving
      (fun p : ℝ × ((Fin s → ℝ) × ℝ) ↦ (p.2.1, p.2.2))
      (volume.prod (volume.prod volume)) (volume.prod volume) := by
  exact Measure.quasiMeasurePreserving_snd

/-- Forgetting the leading parameter after translating the spatial variable
by it is quasi-measure-preserving. -/
lemma aux_sobolevDifference_qmp_tail_shifted (s : ℕ) :
    Measure.QuasiMeasurePreserving
      (fun p : ℝ × ((Fin s → ℝ) × ℝ) ↦ (p.2.1, p.2.2 + p.1))
      (volume.prod (volume.prod volume)) (volume.prod volume) := by
  refine MeasureTheory.QuasiMeasurePreserving.prod_of_right (by fun_prop) ?_
  filter_upwards with h
  have hmap := (MeasureTheory.MeasurePreserving.id (volume : Measure (Fin s → ℝ))).prod
    (measurePreserving_add_right volume h)
  convert hmap.quasiMeasurePreserving using 1
  rfl

/-- Splitting a `Fin (s + 1)` parameter into its head and tail preserves
Lebesgue product measure. -/
lemma aux_sobolevDifference_measurePreserving_cons (s : ℕ) :
    MeasurePreserving
      (fun p : (Fin (s + 1) → ℝ) × ℝ ↦
        (p.1 0, (fun i : Fin s ↦ p.1 i.succ, p.2)))
      (volume.prod volume) (volume.prod (volume.prod volume)) := by
  let e : (Fin (s + 1) → ℝ) ≃ᵐ (ℝ × (Fin s → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (s + 1) ↦ ℝ) 0
  have he : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (s + 1) ↦ ℝ) 0
  have hprod := he.prod (MeasureTheory.MeasurePreserving.id (volume : Measure ℝ))
  have hassoc := measurePreserving_prodAssoc (volume : Measure ℝ)
    (volume : Measure (Fin s → ℝ)) (volume : Measure ℝ)
  have h := hassoc.comp hprod
  have hzero (q : Fin (s + 1) → ℝ) : (e q).1 = q 0 := by
    have hq := congrFun (e.symm_apply_apply q) 0
    simpa [e] using hq
  have htail (q : Fin (s + 1) → ℝ) (i : Fin s) : (e q).2 i = q i.succ := by
    have hq := congrFun (e.symm_apply_apply q) i.succ
    simpa [e] using hq
  have hfun :
      (fun p : (Fin (s + 1) → ℝ) × ℝ ↦
        (p.1 0, (fun i : Fin s ↦ p.1 i.succ, p.2))) =
        MeasurableEquiv.prodAssoc ∘ Prod.map e id := by
    funext p
    apply Prod.ext
    · exact (hzero p.1).symm
    · apply Prod.ext
      · funext i
        exact (htail p.1 i).symm
      · rfl
  rw [hfun]
  exact h

/-- Joint measurability, one-boundedness, and spatial/parameter support for
iterated multiplicative differences of a one-bounded function supported in
`A`. -/
lemma aux_sobolevDifference_iteratedDifference_joint_data
    (s : ℕ) (A : Set ℝ) (f : ℝ → ℂ)
    (hfmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hsupp : ∀ᵐ x ∂volume, x ∉ A → f x = 0) :
    AEStronglyMeasurable
      (fun p : (Fin s → ℝ) × ℝ ↦ iteratedMultiplicativeDifference s p.1 f p.2)
      (volume.prod volume) ∧
    (∀ᵐ p : (Fin s → ℝ) × ℝ ∂volume.prod volume,
      ‖iteratedMultiplicativeDifference s p.1 f p.2‖ ≤ 1) ∧
    (∀ᵐ p : (Fin s → ℝ) × ℝ ∂volume.prod volume,
      (p.2 ∉ A ∨ ∃ i : Fin s, p.1 i ∉ aux_sobolevDifference_differenceSet A) →
        iteratedMultiplicativeDifference s p.1 f p.2 = 0) := by
  induction s with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · simpa [iteratedMultiplicativeDifference] using hfmeas.comp_snd
      · simpa [iteratedMultiplicativeDifference] using
          (Measure.quasiMeasurePreserving_snd.ae hbound)
      · have hpull : ∀ᵐ p : (Fin 0 → ℝ) × ℝ ∂volume.prod volume,
            p.2 ∉ A → f p.2 = 0 :=
          (Measure.quasiMeasurePreserving_snd
            (μ := (volume : Measure (Fin 0 → ℝ))) (ν := volume)).ae hsupp
        filter_upwards [hpull] with p hp
        intro hbad
        rcases hbad with hx | hfalse
        · simpa [iteratedMultiplicativeDifference] using hp hx
        · rcases hfalse with ⟨i, hi⟩
          exact Fin.elim0 i
  | succ s ih =>
      rcases ih with ⟨ihmeas, ihbound, ihsupp⟩
      let L : ℝ × ((Fin s → ℝ) × ℝ) → ℂ :=
        fun p ↦ iteratedMultiplicativeDifference s p.2.1 f p.2.2
      let R : ℝ × ((Fin s → ℝ) × ℝ) → ℂ :=
        fun p ↦ iteratedMultiplicativeDifference s p.2.1 f (p.2.2 + p.1)
      have hLmeas : AEStronglyMeasurable L (volume.prod (volume.prod volume)) := by
        simpa [L, Function.comp_def] using ihmeas.comp_quasiMeasurePreserving
          (aux_sobolevDifference_qmp_tail_unshifted s)
      have hRmeas : AEStronglyMeasurable R (volume.prod (volume.prod volume)) := by
        simpa [R, Function.comp_def] using ihmeas.comp_quasiMeasurePreserving
          (aux_sobolevDifference_qmp_tail_shifted s)
      have hLbound : ∀ᵐ p : ℝ × ((Fin s → ℝ) × ℝ) ∂volume.prod (volume.prod volume),
          ‖L p‖ ≤ 1 := by
        simpa [L] using (aux_sobolevDifference_qmp_tail_unshifted s).ae ihbound
      have hRbound : ∀ᵐ p : ℝ × ((Fin s → ℝ) × ℝ) ∂volume.prod (volume.prod volume),
          ‖R p‖ ≤ 1 := by
        simpa [R] using (aux_sobolevDifference_qmp_tail_shifted s).ae ihbound
      have hLsupp : ∀ᵐ p : ℝ × ((Fin s → ℝ) × ℝ) ∂volume.prod (volume.prod volume),
          (p.2.2 ∉ A ∨ ∃ i : Fin s, p.2.1 i ∉ aux_sobolevDifference_differenceSet A) →
            L p = 0 := by
        simpa [L] using (aux_sobolevDifference_qmp_tail_unshifted s).ae ihsupp
      have hRsupp : ∀ᵐ p : ℝ × ((Fin s → ℝ) × ℝ) ∂volume.prod (volume.prod volume),
          (p.2.2 + p.1 ∉ A ∨ ∃ i : Fin s,
            p.2.1 i ∉ aux_sobolevDifference_differenceSet A) → R p = 0 := by
        simpa [R] using (aux_sobolevDifference_qmp_tail_shifted s).ae ihsupp
      have hmidmeas : AEStronglyMeasurable (fun p ↦ L p * starRingEnd ℂ (R p))
          (volume.prod (volume.prod volume)) := hLmeas.mul hRmeas.star
      have hmidbound : ∀ᵐ p : ℝ × ((Fin s → ℝ) × ℝ) ∂volume.prod (volume.prod volume),
          ‖L p * starRingEnd ℂ (R p)‖ ≤ 1 := by
        filter_upwards [hLbound, hRbound] with p hp hq
        rw [norm_mul]
        have hstar : ‖starRingEnd ℂ (R p)‖ = ‖R p‖ := by simp
        rw [hstar]
        nlinarith [norm_nonneg (L p), norm_nonneg (R p)]
      have hmidsupp : ∀ᵐ p : ℝ × ((Fin s → ℝ) × ℝ) ∂volume.prod (volume.prod volume),
          (p.2.2 ∉ A ∨ p.1 ∉ aux_sobolevDifference_differenceSet A ∨
            ∃ i : Fin s, p.2.1 i ∉ aux_sobolevDifference_differenceSet A) →
            L p * starRingEnd ℂ (R p) = 0 := by
        filter_upwards [hLsupp, hRsupp] with p hp hq
        intro hbad
        rcases hbad with hx | hh | htail
        · simp [hp (Or.inl hx)]
        · by_cases hL : L p = 0
          · simp [hL]
          · by_cases hR : R p = 0
            · simp [hR]
            · exfalso
              apply hh
              have hxmem : p.2.2 ∈ A := by
                by_contra hnot
                exact hL (hp (Or.inl hnot))
              have hxshiftmem : p.2.2 + p.1 ∈ A := by
                by_contra hnot
                exact hR (hq (Or.inl hnot))
              exact ⟨p.2.2 + p.1, hxshiftmem, p.2.2, hxmem, by ring⟩
        · simp [hp (Or.inr htail)]
      let P : (Fin (s + 1) → ℝ) × ℝ → ℝ × ((Fin s → ℝ) × ℝ) :=
        fun p ↦ (p.1 0, (fun i : Fin s ↦ p.1 i.succ, p.2))
      have hP := aux_sobolevDifference_measurePreserving_cons s
      have hsrcmeas : AEStronglyMeasurable (fun p ↦
          L (P p) * starRingEnd ℂ (R (P p))) (volume.prod volume) := by
        exact hmidmeas.comp_quasiMeasurePreserving hP.quasiMeasurePreserving
      have hsrcbound : ∀ᵐ p : (Fin (s + 1) → ℝ) × ℝ ∂volume.prod volume,
          ‖L (P p) * starRingEnd ℂ (R (P p))‖ ≤ 1 :=
        hP.quasiMeasurePreserving.ae hmidbound
      have hsrcsupport : ∀ᵐ p : (Fin (s + 1) → ℝ) × ℝ ∂volume.prod volume,
          (p.2 ∉ A ∨ ∃ i : Fin (s + 1),
            p.1 i ∉ aux_sobolevDifference_differenceSet A) →
            L (P p) * starRingEnd ℂ (R (P p)) = 0 := by
        filter_upwards [hP.quasiMeasurePreserving.ae hmidsupp] with p hp
        intro hbad
        apply hp
        rcases hbad with hx | ⟨i, hi⟩
        · exact Or.inl hx
        · revert hi
          refine Fin.cases ?_ ?_ i
          · intro hi
            exact Or.inr (Or.inl (by simpa [P] using hi))
          · intro j hi
            exact Or.inr (Or.inr ⟨j, by simpa [P] using hi⟩)
      refine ⟨?_, ?_, ?_⟩
      · simpa [P, L, R, iteratedMultiplicativeDifference, multiplicativeDifference] using hsrcmeas
      · simpa [P, L, R, iteratedMultiplicativeDifference, multiplicativeDifference] using hsrcbound
      · simpa [P, L, R, iteratedMultiplicativeDifference, multiplicativeDifference] using hsrcsupport

/-- A one-bounded iterated difference supported in `[a,b]` has joint energy
supported in the spatial interval and the parameter box `[a-b,b-a]^s`. -/
lemma aux_sobolevDifference_iteratedDifference_energy_le
    (s : ℕ) (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℂ)
    (hfmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hsupp : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f x = 0) :
    (∫⁻ h : Fin s → ℝ, ∫⁻ x : ℝ,
      ‖iteratedMultiplicativeDifference s h f x‖ₑ ^ (2 : ℝ)) ≤
      volume (Set.Icc (fun _ : Fin s ↦ a - b) (fun _ : Fin s ↦ b - a)) *
        volume (Set.Icc a b) := by
  let A : Set ℝ := Set.Icc a b
  let P : Set (Fin s → ℝ) :=
    Set.Icc (fun _ : Fin s ↦ a - b) (fun _ : Fin s ↦ b - a)
  have hdiffsubset : aux_sobolevDifference_differenceSet A ⊆ Set.Icc (a - b) (b - a) := by
    rintro z ⟨x, hx, y, hy, rfl⟩
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hjoint := aux_sobolevDifference_iteratedDifference_joint_data s A f hfmeas hbound (by
    simpa [A] using hsupp)
  rcases hjoint with ⟨hjmeas, hjbound, hjsupp⟩
  have hrawmeas : AEMeasurable
      (fun p : (Fin s → ℝ) × ℝ ↦
        ‖iteratedMultiplicativeDifference s p.1 f p.2‖ₑ ^ (2 : ℝ))
      (volume.prod volume) :=
    (ENNReal.continuous_rpow_const.aemeasurable.comp_aemeasurable hjmeas.enorm)
  have hpoint : ∀ᵐ p : (Fin s → ℝ) × ℝ ∂volume.prod volume,
      ‖iteratedMultiplicativeDifference s p.1 f p.2‖ₑ ^ (2 : ℝ) ≤
        P.indicator (fun _ ↦ (1 : ℝ≥0∞)) p.1 *
          A.indicator (fun _ ↦ (1 : ℝ≥0∞)) p.2 := by
    filter_upwards [hjbound, hjsupp] with p hpbound hpsupp
    by_cases hp : p.1 ∈ P
    · by_cases hx : p.2 ∈ A
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hx, mul_one]
        have henorm : ‖iteratedMultiplicativeDifference s p.1 f p.2‖ₑ ≤ 1 := by
          rw [← ofReal_norm, ← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal hpbound
        exact ENNReal.rpow_le_one henorm (by norm_num)
      · rw [Set.indicator_of_mem hp, Set.indicator_of_notMem hx, mul_zero]
        simpa [hpsupp (Or.inl hx)]
    · rw [Set.indicator_of_notMem hp, zero_mul]
      have hbad : ∃ i : Fin s, p.1 i ∉ aux_sobolevDifference_differenceSet A := by
        by_contra hnone
        push_neg at hnone
        apply hp
        constructor
        · intro i
          exact (hdiffsubset (hnone i)).1
        · intro i
          exact (hdiffsubset (hnone i)).2
      simpa [hpsupp (Or.inr hbad)]
  have hPmeas : MeasurableSet P := measurableSet_Icc
  have hAmeas : MeasurableSet A := measurableSet_Icc
  have hPind_meas : AEMeasurable (P.indicator (fun _ ↦ (1 : ℝ≥0∞))) volume :=
    (measurable_const.indicator hPmeas).aemeasurable
  have hAind_meas : AEMeasurable (A.indicator (fun _ ↦ (1 : ℝ≥0∞))) volume :=
    (measurable_const.indicator hAmeas).aemeasurable
  calc
    ∫⁻ h : Fin s → ℝ, ∫⁻ x : ℝ,
        ‖iteratedMultiplicativeDifference s h f x‖ₑ ^ (2 : ℝ) =
        ∫⁻ p : (Fin s → ℝ) × ℝ,
          ‖iteratedMultiplicativeDifference s p.1 f p.2‖ₑ ^ (2 : ℝ) := by
            exact (lintegral_prod _ hrawmeas).symm
    _ ≤ ∫⁻ p : (Fin s → ℝ) × ℝ,
        P.indicator (fun _ ↦ (1 : ℝ≥0∞)) p.1 *
          A.indicator (fun _ ↦ (1 : ℝ≥0∞)) p.2 :=
      lintegral_mono_ae hpoint
    _ = ∫⁻ h : Fin s → ℝ, ∫⁻ x : ℝ,
        P.indicator (fun _ ↦ (1 : ℝ≥0∞)) h *
          A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
            exact lintegral_prod _ (hPind_meas.comp_fst.mul hAind_meas.comp_snd)
    _ = ∫⁻ h : Fin s → ℝ,
        P.indicator (fun _ ↦ (1 : ℝ≥0∞)) h *
          ∫⁻ x : ℝ, A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
            apply lintegral_congr
            intro h
            rw [lintegral_const_mul'' _ hAind_meas]
    _ = ∫⁻ h : Fin s → ℝ,
        P.indicator (fun _ ↦ (1 : ℝ≥0∞)) h * volume A := by
            congr 1
            rw [lintegral_indicator hAmeas, setLIntegral_one]
    _ = (∫⁻ h : Fin s → ℝ, P.indicator (fun _ ↦ (1 : ℝ≥0∞)) h) * volume A := by
            rw [lintegral_mul_const'' _ hPind_meas]
    _ = volume P * volume A := by
            rw [lintegral_indicator hPmeas, setLIntegral_one]
    _ = volume (Set.Icc (fun _ : Fin s ↦ a - b) (fun _ : Fin s ↦ b - a)) *
          volume (Set.Icc a b) := by rfl

/-- Every fixed iterated difference of a one-bounded function supported in
`A` remains one-bounded and supported in the same spatial set. -/
lemma aux_sobolevDifference_iteratedDifference_section_data
    (s : ℕ) (h : Fin s → ℝ) (A : Set ℝ) (f : ℝ → ℂ)
    (hfmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hsupp : ∀ᵐ x ∂volume, x ∉ A → f x = 0) :
    AEStronglyMeasurable (iteratedMultiplicativeDifference s h f) volume ∧
    (∀ᵐ x ∂volume, ‖iteratedMultiplicativeDifference s h f x‖ ≤ 1) ∧
    (∀ᵐ x ∂volume, x ∉ A → iteratedMultiplicativeDifference s h f x = 0) := by
  induction s with
  | zero =>
      exact ⟨by simpa [iteratedMultiplicativeDifference] using hfmeas,
        by simpa [iteratedMultiplicativeDifference] using hbound,
        by simpa [iteratedMultiplicativeDifference] using hsupp⟩
  | succ s ih =>
      let g : ℝ → ℂ := iteratedMultiplicativeDifference s (fun i ↦ h i.succ) f
      rcases ih (fun i ↦ h i.succ) with ⟨hgmeas, hgbound, hgsupp⟩
      have hshiftmeas : AEStronglyMeasurable (fun x : ℝ ↦ g (x + h 0)) volume := by
        simpa [Function.comp_def] using hgmeas.comp_quasiMeasurePreserving
          (measurePreserving_add_right volume (h 0)).quasiMeasurePreserving
      have hshiftbound : ∀ᵐ x ∂volume, ‖g (x + h 0)‖ ≤ 1 := by
        exact (measurePreserving_add_right volume (h 0)).quasiMeasurePreserving.tendsto_ae
          hgbound
      refine ⟨?_, ?_, ?_⟩
      · change AEStronglyMeasurable
          (fun x ↦ g x * starRingEnd ℂ (g (x + h 0))) volume
        exact hgmeas.mul hshiftmeas.star
      · filter_upwards [hgbound, hshiftbound] with x hx hxshift
        have hprod : ‖g x‖ * ‖g (x + h 0)‖ ≤ 1 := by
          nlinarith [norm_nonneg (g x), norm_nonneg (g (x + h 0))]
        simpa [g, iteratedMultiplicativeDifference, multiplicativeDifference] using hprod
      · filter_upwards [hgsupp] with x hx
        intro hxA
        simp [g, iteratedMultiplicativeDifference, multiplicativeDifference, hx hxA]

/-- Every fixed interval-supported iterated difference lies in every `Lᵖ`.
In particular, it has a canonical `L²` representative. -/
lemma aux_sobolevDifference_iteratedDifference_memLp_Icc
    (s : ℕ) (h : Fin s → ℝ) (a b : ℝ) (f : ℝ → ℂ)
    (hfmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hsupp : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f x = 0)
    (p : ℝ≥0∞) :
    MemLp (iteratedMultiplicativeDifference s h f) p volume := by
  rcases aux_sobolevDifference_iteratedDifference_section_data s h (Set.Icc a b) f
    hfmeas hbound hsupp with ⟨hgmeas, hgbound, hgsupp⟩
  exact aux_memLp_of_ae_bound_of_ae_support _ hgmeas 1 hgbound (Set.Icc a b)
    measurableSet_Icc isCompact_Icc.measure_lt_top hgsupp p

/-- Unfolds the raw Sobolev wrapper once an `L²` representative is known. -/
lemma aux_sobolevDifference_sobolevNormRaw_eq_sobolevNorm
    (σ : ℝ) (g : ℝ → ℂ) (hg : MemLp g 2 volume) :
    aux_sobolevNormRaw σ g = sobolevNorm σ hg.toLp := by
  simp only [aux_sobolevNormRaw, dif_pos hg]

/-- The raw Sobolev wrapper for each interval-supported iterated difference
is on its `L²` branch. -/
lemma aux_sobolevDifference_iterated_sobolevNormRaw_eq
    (s : ℕ) (h : Fin s → ℝ) (a b σ : ℝ) (f : ℝ → ℂ)
    (hfmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hsupp : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f x = 0) :
    aux_sobolevNormRaw σ (iteratedMultiplicativeDifference s h f) =
      sobolevNorm σ
        (aux_sobolevDifference_iteratedDifference_memLp_Icc s h a b f hfmeas hbound hsupp 2).toLp := by
  exact aux_sobolevDifference_sobolevNormRaw_eq_sobolevNorm _ _
    (aux_sobolevDifference_iteratedDifference_memLp_Icc s h a b f hfmeas hbound hsupp 2)

/-- The compact-support estimate expressed as the square of each iterated
difference's `L²` extended norm. -/
lemma aux_sobolevDifference_iteratedDifference_l2_energy_le
    (s : ℕ) (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℂ)
    (hfmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hsupp : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f x = 0) :
    (∫⁻ h : Fin s → ℝ,
      (eLpNorm (iteratedMultiplicativeDifference s h f) 2 volume) ^ (2 : ℝ)) ≤
      volume (Set.Icc (fun _ : Fin s ↦ a - b) (fun _ : Fin s ↦ b - a)) *
        volume (Set.Icc a b) := by
  calc
    ∫⁻ h : Fin s → ℝ,
        (eLpNorm (iteratedMultiplicativeDifference s h f) 2 volume) ^ (2 : ℝ) =
        ∫⁻ h : Fin s → ℝ, ∫⁻ x : ℝ,
          ‖iteratedMultiplicativeDifference s h f x‖ₑ ^ (2 : ℝ) := by
            apply lintegral_congr
            intro h
            simpa using
              (eLpNorm_nnreal_pow_eq_lintegral
                (f := iteratedMultiplicativeDifference s h f) (p := (2 : NNReal))
                (by norm_num))
    _ ≤ volume (Set.Icc (fun _ : Fin s ↦ a - b) (fun _ : Fin s ↦ b - a)) *
          volume (Set.Icc a b) :=
      aux_sobolevDifference_iteratedDifference_energy_le s a b hab f hfmeas hbound hsupp

/-- Exact volume of the iterated-difference parameter box times the spatial
interval. -/
lemma aux_sobolevDifference_difference_box_volume_eq
    (s : ℕ) (a b : ℝ) (hab : a ≤ b) :
    volume (Set.Icc (fun _ : Fin s ↦ a - b) (fun _ : Fin s ↦ b - a)) *
        volume (Set.Icc a b) =
      ENNReal.ofReal ((2 : ℝ) ^ s * intervalLength (Set.Icc a b) ^ (s + 1)) := by
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  rw [Real.volume_Icc_pi, Real.volume_Icc]
  simp only [Finset.prod_const,
    intervalLength, Real.volume_Icc, ENNReal.toReal_ofReal hba]
  rw [show b - a - (a - b) = 2 * (b - a) by ring]
  have hcard : (Finset.univ : Finset (Fin s)).card = s := Fintype.card_fin s
  rw [hcard]
  have hleft : ENNReal.ofReal (2 * (b - a)) =
      ENNReal.ofReal 2 * ENNReal.ofReal (b - a) :=
    ENNReal.ofReal_mul (by norm_num)
  have hright : ENNReal.ofReal ((2 : ℝ) ^ s * (b - a) ^ (s + 1)) =
      ENNReal.ofReal ((2 : ℝ) ^ s) * ENNReal.ofReal ((b - a) ^ (s + 1)) :=
    ENNReal.ofReal_mul (by positivity)
  rw [hleft, hright, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_pow hba]
  rw [mul_pow]
  ring

/-- The exact compact-support `L²` energy constant
`2^s * |[a,b]|^(s+1)`. -/
lemma aux_sobolevDifference_iteratedDifference_l2_energy_exact_le
    (s : ℕ) (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℂ)
    (hfmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hsupp : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f x = 0) :
    (∫⁻ h : Fin s → ℝ,
      (eLpNorm (iteratedMultiplicativeDifference s h f) 2 volume) ^ (2 : ℝ)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ s * intervalLength (Set.Icc a b) ^ (s + 1)) := by
  calc
    ∫⁻ h : Fin s → ℝ,
        (eLpNorm (iteratedMultiplicativeDifference s h f) 2 volume) ^ (2 : ℝ) ≤
        volume (Set.Icc (fun _ : Fin s ↦ a - b) (fun _ : Fin s ↦ b - a)) *
          volume (Set.Icc a b) :=
      aux_sobolevDifference_iteratedDifference_l2_energy_le s a b hab f hfmeas hbound hsupp
    _ = ENNReal.ofReal ((2 : ℝ) ^ s * intervalLength (Set.Icc a b) ^ (s + 1)) :=
      aux_sobolevDifference_difference_box_volume_eq s a b hab

/-- The unweighted `L²` energy of an iterated difference is measurable in
all difference parameters. -/
lemma aux_sobolevDifference_iteratedDifference_l2_energy_aemeasurable
    (s : ℕ) (A : Set ℝ) (f : ℝ → ℂ)
    (hfmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hsupp : ∀ᵐ x ∂volume, x ∉ A → f x = 0) :
    AEMeasurable (fun h : Fin s → ℝ ↦
      (eLpNorm (iteratedMultiplicativeDifference s h f) 2 volume) ^ (2 : ℝ)) volume := by
  have hjoint := aux_sobolevDifference_iteratedDifference_joint_data s A f hfmeas hbound hsupp
  have hrawmeas : AEMeasurable
      (fun p : (Fin s → ℝ) × ℝ ↦
        ‖iteratedMultiplicativeDifference s p.1 f p.2‖ₑ ^ (2 : ℝ))
      (volume.prod volume) :=
    ENNReal.continuous_rpow_const.aemeasurable.comp_aemeasurable hjoint.1.enorm
  have hinter := hrawmeas.lintegral_prod_right'
  convert hinter using 1
  funext h
  simpa using
    (eLpNorm_nnreal_pow_eq_lintegral
      (f := iteratedMultiplicativeDifference s h f) (p := (2 : NNReal))
      (by norm_num))

/-- Frequencies strictly above radius `R`. -/
def aux_sobolevDifference_highFrequency (R : ℝ) : Set ℝ := {ξ | R < |ξ|}

/-- Frequencies at most `R` in absolute value. -/
def aux_sobolevDifference_lowFrequency (R : ℝ) : Set ℝ := Set.Icc (-R) R

/-- The high-frequency region is the complement of the closed low-frequency
interval. -/
lemma aux_sobolevDifference_highFrequency_eq_lowFrequency_compl (R : ℝ) :
    aux_sobolevDifference_highFrequency R = (aux_sobolevDifference_lowFrequency R)ᶜ := by
  ext ξ
  simp only [aux_sobolevDifference_highFrequency, aux_sobolevDifference_lowFrequency,
    Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le]
  rw [lt_abs]
  constructor
  · rintro (hleft | hright)
    · exact Or.inr hleft
    · exact Or.inl (by linarith)
  · rintro (hleft | hright)
    · exact Or.inr (by linarith)
    · exact Or.inl hright

/-- The high-frequency cutoff set is measurable. -/
lemma aux_sobolevDifference_measurableSet_highFrequency (R : ℝ) :
    MeasurableSet (aux_sobolevDifference_highFrequency R) := by
  rw [aux_sobolevDifference_highFrequency_eq_lowFrequency_compl]
  have hlow : MeasurableSet (aux_sobolevDifference_lowFrequency R) := by
    simpa [aux_sobolevDifference_lowFrequency] using
      (measurableSet_Icc : MeasurableSet (Set.Icc (-R) R))
  exact hlow.compl

/-- The Japanese bracket dominates absolute value. -/
lemma aux_sobolevDifference_japaneseBracket_ge_abs (ξ : ℝ) :
    |ξ| ≤ japaneseBracket ξ := by
  unfold japaneseBracket
  rw [← sq_le_sq₀ (abs_nonneg ξ) (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
  nlinarith [sq_nonneg |ξ|]

/-- On the high-frequency region, the negative Sobolev weight is at most the
cutoff weight. -/
lemma aux_sobolevDifference_highFrequency_weight_bound
    (σ R ξ : ℝ) (hσ : 0 ≤ σ) (hR : 0 < R)
    (hξ : ξ ∈ aux_sobolevDifference_highFrequency R) :
    ‖japaneseBracket ξ ^ (-σ)‖ ≤ R ^ (-σ) := by
  have hjap_nonneg : 0 ≤ japaneseBracket ξ := Real.sqrt_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hjap_nonneg _)]
  apply Real.rpow_le_rpow_of_nonpos hR
  · exact le_trans hξ.le (aux_sobolevDifference_japaneseBracket_ge_abs ξ)
  · linarith

/-- The high-frequency weighted `L²` piece is controlled by the unweighted
`L²` norm with factor `R^{-σ}`. -/
lemma aux_sobolevDifference_highFrequency_weighted_eLpNorm_le
    (σ R : ℝ) (hσ : 0 ≤ σ) (hR : 0 < R) (F : ℝ → ℂ) :
    eLpNorm ((aux_sobolevDifference_highFrequency R).indicator
      (fun ξ ↦ (japaneseBracket ξ ^ (-σ)) • F ξ)) 2 volume ≤
      ENNReal.ofReal (R ^ (-σ)) * eLpNorm F 2 volume := by
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
  filter_upwards with ξ
  by_cases hξ : ξ ∈ aux_sobolevDifference_highFrequency R
  · rw [Set.indicator_of_mem hξ, norm_smul]
    exact mul_le_mul_of_nonneg_right
      (aux_sobolevDifference_highFrequency_weight_bound σ R ξ hσ hR hξ) (norm_nonneg _)
  · rw [Set.indicator_of_notMem hξ, norm_zero]
    positivity

/-- Squaring the high-frequency estimate produces the factor
`R ^ (-2 * σ)` used in the frequency split. -/
lemma aux_sobolevDifference_highFrequency_weighted_energy_le
    (σ R : ℝ) (hσ : 0 ≤ σ) (hR : 0 < R) (F : ℝ → ℂ) :
    (eLpNorm ((aux_sobolevDifference_highFrequency R).indicator
      (fun ξ ↦ (japaneseBracket ξ ^ (-σ)) • F ξ)) 2 volume) ^ (2 : ℝ) ≤
      ENNReal.ofReal (R ^ (-2 * σ)) * (eLpNorm F 2 volume) ^ (2 : ℝ) := by
  have hbase := aux_sobolevDifference_highFrequency_weighted_eLpNorm_le σ R hσ hR F
  calc
    (eLpNorm ((aux_sobolevDifference_highFrequency R).indicator
      (fun ξ ↦ (japaneseBracket ξ ^ (-σ)) • F ξ)) 2 volume) ^ (2 : ℝ) ≤
        (ENNReal.ofReal (R ^ (-σ)) * eLpNorm F 2 volume) ^ (2 : ℝ) :=
      ENNReal.rpow_le_rpow hbase (by norm_num)
    _ = ENNReal.ofReal (R ^ (-2 * σ)) * (eLpNorm F 2 volume) ^ (2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      have hRnonneg : 0 ≤ R := hR.le
      rw [ENNReal.ofReal_rpow_of_nonneg
        (Real.rpow_nonneg hRnonneg _) (by norm_num)]
      rw [← Real.rpow_mul hRnonneg]
      ring_nf

/-- Plancherel preserves the `L²` extended norm in the form used by the
cutoff estimates. -/
lemma aux_sobolevDifference_eLpNorm_fourier_eq
    (g : Lp (α := ℝ) ℂ 2 volume) :
    eLpNorm (Lp.fourierTransformₗᵢ ℝ ℂ g : ℝ → ℂ) 2 volume =
      eLpNorm (g : ℝ → ℂ) 2 volume := by
  calc
    eLpNorm (Lp.fourierTransformₗᵢ ℝ ℂ g : ℝ → ℂ) 2 volume =
        ‖Lp.fourierTransformₗᵢ ℝ ℂ g‖ₑ := (Lp.enorm_def _).symm
    _ = ‖g‖ₑ := (Lp.fourierTransformₗᵢ ℝ ℂ).enorm_map g
    _ = eLpNorm (g : ℝ → ℂ) 2 volume := Lp.enorm_def _

/-- The high-frequency portion of a Sobolev Fourier energy is controlled by
the original unweighted `L²` energy. -/
lemma aux_sobolevDifference_highFrequency_sobolev_energy_le
    (σ R : ℝ) (hσ : 0 ≤ σ) (hR : 0 < R)
    (g : Lp (α := ℝ) ℂ 2 volume) :
    (eLpNorm ((aux_sobolevDifference_highFrequency R).indicator
      (fun ξ ↦ (japaneseBracket ξ ^ (-σ)) •
        (Lp.fourierTransformₗᵢ ℝ ℂ g) ξ)) 2 volume) ^ (2 : ℝ) ≤
      ENNReal.ofReal (R ^ (-2 * σ)) *
        (eLpNorm (g : ℝ → ℂ) 2 volume) ^ (2 : ℝ) := by
  calc
    (eLpNorm ((aux_sobolevDifference_highFrequency R).indicator
      (fun ξ ↦ (japaneseBracket ξ ^ (-σ)) •
        (Lp.fourierTransformₗᵢ ℝ ℂ g) ξ)) 2 volume) ^ (2 : ℝ) ≤
        ENNReal.ofReal (R ^ (-2 * σ)) *
          (eLpNorm (Lp.fourierTransformₗᵢ ℝ ℂ g : ℝ → ℂ) 2 volume) ^ (2 : ℝ) :=
      aux_sobolevDifference_highFrequency_weighted_energy_le σ R hσ hR _
    _ = ENNReal.ofReal (R ^ (-2 * σ)) *
          (eLpNorm (g : ℝ → ℂ) 2 volume) ^ (2 : ℝ) := by
      rw [aux_sobolevDifference_eLpNorm_fourier_eq]

/-- The squared Sobolev norm splits exactly into its low- and high-frequency
Fourier energies. -/
lemma aux_sobolevDifference_sobolevNorm_energy_split
    (σ R : ℝ) (g : Lp (α := ℝ) ℂ 2 volume) :
    sobolevNorm σ g ^ (2 : ℝ) =
      (∫⁻ ξ : ℝ in aux_sobolevDifference_lowFrequency R,
        ‖(japaneseBracket ξ ^ (-σ)) •
          (Lp.fourierTransformₗᵢ ℝ ℂ g) ξ‖ₑ ^ (2 : ℝ)) +
      ∫⁻ ξ : ℝ in aux_sobolevDifference_highFrequency R,
        ‖(japaneseBracket ξ ^ (-σ)) •
          (Lp.fourierTransformₗᵢ ℝ ℂ g) ξ‖ₑ ^ (2 : ℝ) := by
  unfold sobolevNorm
  change
    (eLpNorm (fun ξ : ℝ ↦ (japaneseBracket ξ ^ (-σ)) •
      (Lp.fourierTransformₗᵢ ℝ ℂ g) ξ) (↑(2 : NNReal)) volume) ^
        (↑(2 : NNReal) : ℝ) = _
  rw [eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) (by norm_num)]
  rw [← lintegral_add_compl _ (A := aux_sobolevDifference_lowFrequency R)
    (by simpa [aux_sobolevDifference_lowFrequency] using
      (measurableSet_Icc : MeasurableSet (Set.Icc (-R) R)))]
  rw [← aux_sobolevDifference_highFrequency_eq_lowFrequency_compl]
  norm_num

/-- The high-frequency set integral is the square of the `L²` norm of its
indicator cutoff. -/
lemma aux_sobolevDifference_highFrequency_set_energy_eq
    (σ R : ℝ) (F : ℝ → ℂ) :
    ∫⁻ ξ : ℝ in aux_sobolevDifference_highFrequency R,
      ‖(japaneseBracket ξ ^ (-σ)) • F ξ‖ₑ ^ (2 : ℝ) =
      (eLpNorm ((aux_sobolevDifference_highFrequency R).indicator
        (fun ξ ↦ (japaneseBracket ξ ^ (-σ)) • F ξ)) 2 volume) ^ (2 : ℝ) := by
  symm
  change
    (eLpNorm ((aux_sobolevDifference_highFrequency R).indicator
      (fun ξ ↦ (japaneseBracket ξ ^ (-σ)) • F ξ)) (↑(2 : NNReal)) volume) ^
        (↑(2 : NNReal) : ℝ) = _
  rw [eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) (by norm_num)]
  calc
    ∫⁻ ξ : ℝ, ‖(aux_sobolevDifference_highFrequency R).indicator
        (fun ξ ↦ (japaneseBracket ξ ^ (-σ)) • F ξ) ξ‖ₑ ^ (↑(2 : NNReal) : ℝ) =
        ∫⁻ ξ : ℝ, (aux_sobolevDifference_highFrequency R).indicator
          (fun ξ ↦ ‖(japaneseBracket ξ ^ (-σ)) • F ξ‖ₑ ^ (↑(2 : NNReal) : ℝ)) ξ := by
      apply lintegral_congr
      intro ξ
      by_cases hξ : ξ ∈ aux_sobolevDifference_highFrequency R
      · simp [Set.indicator_of_mem hξ]
      · simp [Set.indicator_of_notMem hξ]
    _ = ∫⁻ ξ : ℝ in aux_sobolevDifference_highFrequency R,
        ‖(japaneseBracket ξ ^ (-σ)) • F ξ‖ₑ ^ (↑(2 : NNReal) : ℝ) :=
      lintegral_indicator (aux_sobolevDifference_measurableSet_highFrequency R) _

/-- The high-frequency set integral of a Sobolev Fourier energy has the
cutoff bound `R ^ (-2 * σ)` times the original `L²` energy. -/
lemma aux_sobolevDifference_highFrequency_sobolev_set_energy_le
    (σ R : ℝ) (hσ : 0 ≤ σ) (hR : 0 < R)
    (g : Lp (α := ℝ) ℂ 2 volume) :
    ∫⁻ ξ : ℝ in aux_sobolevDifference_highFrequency R,
      ‖(japaneseBracket ξ ^ (-σ)) •
        (Lp.fourierTransformₗᵢ ℝ ℂ g) ξ‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (R ^ (-2 * σ)) *
        (eLpNorm (g : ℝ → ℂ) 2 volume) ^ (2 : ℝ) := by
  calc
    ∫⁻ ξ : ℝ in aux_sobolevDifference_highFrequency R,
        ‖(japaneseBracket ξ ^ (-σ)) •
          (Lp.fourierTransformₗᵢ ℝ ℂ g) ξ‖ₑ ^ (2 : ℝ) =
        (eLpNorm ((aux_sobolevDifference_highFrequency R).indicator
          (fun ξ ↦ (japaneseBracket ξ ^ (-σ)) •
            (Lp.fourierTransformₗᵢ ℝ ℂ g) ξ)) 2 volume) ^ (2 : ℝ) :=
      aux_sobolevDifference_highFrequency_set_energy_eq σ R _
    _ ≤ ENNReal.ofReal (R ^ (-2 * σ)) *
          (eLpNorm (g : ℝ → ℂ) 2 volume) ^ (2 : ℝ) :=
      aux_sobolevDifference_highFrequency_sobolev_energy_le σ R hσ hR g

/-- Integrating the high-frequency cutoff estimate requires only
measurability of the unweighted `L²` energy of the parameter family. -/
lemma aux_sobolevDifference_lintegral_highFrequency_sobolev_energy_le
    {ι : Type*} [MeasurableSpace ι] (μ : Measure ι)
    (σ R : ℝ) (hσ : 0 ≤ σ) (hR : 0 < R)
    (G : ι → Lp (α := ℝ) ℂ 2 volume)
    (henergy : AEMeasurable (fun i ↦
      (eLpNorm (G i : ℝ → ℂ) 2 volume) ^ (2 : ℝ)) μ) :
    (∫⁻ i : ι, (∫⁻ ξ : ℝ in aux_sobolevDifference_highFrequency R,
      ‖(japaneseBracket ξ ^ (-σ)) •
        (Lp.fourierTransformₗᵢ ℝ ℂ (G i)) ξ‖ₑ ^ (2 : ℝ) ∂volume) ∂μ) ≤
      ENNReal.ofReal (R ^ (-2 * σ)) *
        ∫⁻ i : ι, (eLpNorm (G i : ℝ → ℂ) 2 volume) ^ (2 : ℝ) ∂μ := by
  calc
    (∫⁻ i : ι, (∫⁻ ξ : ℝ in aux_sobolevDifference_highFrequency R,
        ‖(japaneseBracket ξ ^ (-σ)) •
          (Lp.fourierTransformₗᵢ ℝ ℂ (G i)) ξ‖ₑ ^ (2 : ℝ) ∂volume) ∂μ) ≤
        ∫⁻ i : ι, ENNReal.ofReal (R ^ (-2 * σ)) *
          (eLpNorm (G i : ℝ → ℂ) 2 volume) ^ (2 : ℝ) ∂μ := by
      apply lintegral_mono
      intro i
      exact aux_sobolevDifference_highFrequency_sobolev_set_energy_le σ R hσ hR (G i)
    _ = ENNReal.ofReal (R ^ (-2 * σ)) *
        ∫⁻ i : ι, (eLpNorm (G i : ℝ → ℂ) 2 volume) ^ (2 : ℝ) ∂μ :=
      lintegral_const_mul'' _ henergy

/-- The canonical `L²` representative of a bounded, interval-supported
iterated difference. -/
def aux_sobolevDifference_iteratedDifferenceLp
    (s : ℕ) (h : Fin s → ℝ) (a b : ℝ) (f : ℝ → ℂ)
    (hfmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hsupp : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f x = 0) :
    Lp (α := ℝ) ℂ 2 volume :=
  (aux_sobolevDifference_iteratedDifference_memLp_Icc s h a b f hfmeas hbound hsupp 2).toLp

/-- The canonical representative agrees almost everywhere with its raw
iterated difference. -/
lemma aux_sobolevDifference_iteratedDifferenceLp_coeFn_ae
    (s : ℕ) (h : Fin s → ℝ) (a b : ℝ) (f : ℝ → ℂ)
    (hfmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hsupp : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f x = 0) :
    (aux_sobolevDifference_iteratedDifferenceLp s h a b f hfmeas hbound hsupp : ℝ → ℂ) =ᵐ[volume]
      iteratedMultiplicativeDifference s h f := by
  exact (aux_sobolevDifference_iteratedDifference_memLp_Icc s h a b f hfmeas hbound hsupp 2).coeFn_toLp

/-- The full parameter-integrated high-frequency Sobolev energy of iterated
differences has the exact compact-support bound used in the main estimate. -/
lemma aux_sobolevDifference_iterated_highFrequency_sobolev_energy_exact_le
    (s : ℕ) (a b σ R : ℝ) (hab : a ≤ b)
    (hσ : 0 ≤ σ) (hR : 0 < R) (f : ℝ → ℂ)
    (hfmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hsupp : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f x = 0) :
    (∫⁻ h : Fin s → ℝ, (∫⁻ ξ : ℝ in aux_sobolevDifference_highFrequency R,
      ‖(japaneseBracket ξ ^ (-σ)) •
        (Lp.fourierTransformₗᵢ ℝ ℂ
          (aux_sobolevDifference_iteratedDifferenceLp s h a b f hfmeas hbound hsupp)) ξ‖ₑ ^
          (2 : ℝ) ∂volume) ∂volume) ≤
      ENNReal.ofReal ((2 : ℝ) ^ s * intervalLength (Set.Icc a b) ^ (s + 1)) *
        ENNReal.ofReal (R ^ (-2 * σ)) := by
  let G : (Fin s → ℝ) → Lp (α := ℝ) ℂ 2 volume :=
    fun h ↦ aux_sobolevDifference_iteratedDifferenceLp s h a b f hfmeas hbound hsupp
  have hrawEnergy := aux_sobolevDifference_iteratedDifference_l2_energy_aemeasurable
    s (Set.Icc a b) f hfmeas hbound hsupp
  have hpoint (h : Fin s → ℝ) :
      (eLpNorm (G h : ℝ → ℂ) 2 volume) ^ (2 : ℝ) =
        (eLpNorm (iteratedMultiplicativeDifference s h f) 2 volume) ^ (2 : ℝ) := by
    dsimp [G]
    rw [eLpNorm_congr_ae
      (aux_sobolevDifference_iteratedDifferenceLp_coeFn_ae s h a b f hfmeas hbound hsupp)]
  have henergy : AEMeasurable (fun h : Fin s → ℝ ↦
      (eLpNorm (G h : ℝ → ℂ) 2 volume) ^ (2 : ℝ)) volume := by
    apply hrawEnergy.congr
    filter_upwards with h
    exact (hpoint h).symm
  have hintegral := aux_sobolevDifference_lintegral_highFrequency_sobolev_energy_le
    (μ := volume) σ R hσ hR G henergy
  have henergy_eq :
      (∫⁻ h : Fin s → ℝ,
        (eLpNorm (G h : ℝ → ℂ) 2 volume) ^ (2 : ℝ)) =
      ∫⁻ h : Fin s → ℝ,
        (eLpNorm (iteratedMultiplicativeDifference s h f) 2 volume) ^ (2 : ℝ) := by
    apply lintegral_congr
    intro h
    exact hpoint h
  calc
    (∫⁻ h : Fin s → ℝ, (∫⁻ ξ : ℝ in aux_sobolevDifference_highFrequency R,
        ‖(japaneseBracket ξ ^ (-σ)) •
          (Lp.fourierTransformₗᵢ ℝ ℂ
            (aux_sobolevDifference_iteratedDifferenceLp s h a b f hfmeas hbound hsupp)) ξ‖ₑ ^
            (2 : ℝ) ∂volume) ∂volume) =
        ∫⁻ h : Fin s → ℝ, (∫⁻ ξ : ℝ in aux_sobolevDifference_highFrequency R,
          ‖(japaneseBracket ξ ^ (-σ)) •
            (Lp.fourierTransformₗᵢ ℝ ℂ (G h)) ξ‖ₑ ^ (2 : ℝ) ∂volume) ∂volume := by
      rfl
    _ ≤ ENNReal.ofReal (R ^ (-2 * σ)) *
        ∫⁻ h : Fin s → ℝ, (eLpNorm (G h : ℝ → ℂ) 2 volume) ^ (2 : ℝ) := hintegral
    _ = ENNReal.ofReal (R ^ (-2 * σ)) *
        ∫⁻ h : Fin s → ℝ,
          (eLpNorm (iteratedMultiplicativeDifference s h f) 2 volume) ^ (2 : ℝ) := by
      rw [henergy_eq]
    _ ≤ ENNReal.ofReal (R ^ (-2 * σ)) *
        ENNReal.ofReal ((2 : ℝ) ^ s * intervalLength (Set.Icc a b) ^ (s + 1)) := by
      exact mul_le_mul_right
        (aux_sobolevDifference_iteratedDifference_l2_energy_exact_le
          s a b hab f hfmeas hbound hsupp) _
    _ = ENNReal.ofReal ((2 : ℝ) ^ s * intervalLength (Set.Icc a b) ^ (s + 1)) *
        ENNReal.ofReal (R ^ (-2 * σ)) := by ring

/-- Iterated multiplicative differences are jointly almost everywhere strongly
measurable in all difference parameters and the spatial variable. -/
lemma aux_sobolevDifference_iteratedDifference_joint_aestronglyMeasurable
    (s : ℕ) (f : ℝ → ℂ) (hfmeas : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable
      (fun p : (Fin s → ℝ) × ℝ ↦ iteratedMultiplicativeDifference s p.1 f p.2)
      (volume.prod volume) := by
  induction s with
  | zero =>
      simpa [iteratedMultiplicativeDifference] using hfmeas.comp_snd
  | succ s ih =>
      let L : ℝ × ((Fin s → ℝ) × ℝ) → ℂ :=
        fun p ↦ iteratedMultiplicativeDifference s p.2.1 f p.2.2
      let R : ℝ × ((Fin s → ℝ) × ℝ) → ℂ :=
        fun p ↦ iteratedMultiplicativeDifference s p.2.1 f (p.2.2 + p.1)
      have hLmeas : AEStronglyMeasurable L (volume.prod (volume.prod volume)) := by
        simpa [L, Function.comp_def] using ih.comp_quasiMeasurePreserving
          (aux_sobolevDifference_qmp_tail_unshifted s)
      have hRmeas : AEStronglyMeasurable R (volume.prod (volume.prod volume)) := by
        simpa [R, Function.comp_def] using ih.comp_quasiMeasurePreserving
          (aux_sobolevDifference_qmp_tail_shifted s)
      have hmidmeas : AEStronglyMeasurable (fun p ↦ L p * starRingEnd ℂ (R p))
          (volume.prod (volume.prod volume)) := hLmeas.mul hRmeas.star
      let P : (Fin (s + 1) → ℝ) × ℝ → ℝ × ((Fin s → ℝ) × ℝ) :=
        fun p ↦ (p.1 0, (fun i : Fin s ↦ p.1 i.succ, p.2))
      have hP := aux_sobolevDifference_measurePreserving_cons s
      have hsrcmeas : AEStronglyMeasurable (fun p ↦
          L (P p) * starRingEnd ℂ (R (P p))) (volume.prod volume) := by
        exact hmidmeas.comp_quasiMeasurePreserving hP.quasiMeasurePreserving
      simpa [P, L, R, iteratedMultiplicativeDifference, multiplicativeDifference] using hsrcmeas

/-- Dropping the middle real coordinate from `((a,h),x)` is
quasi-measure-preserving onto `(a,x)`. -/
lemma aux_sobolevDifference_qmp_drop_middle {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] :
    Measure.QuasiMeasurePreserving
      (fun z : (α × ℝ) × ℝ ↦ (z.1.1, z.2))
      ((μ.prod volume).prod volume) (μ.prod volume) := by
  have hproj : Measure.QuasiMeasurePreserving
      (fun z : α × (ℝ × ℝ) ↦ (z.1, z.2.2))
      (μ.prod ((volume : Measure ℝ).prod volume)) (μ.prod volume) := by
    exact MeasureTheory.QuasiMeasurePreserving.prodMap
      (Measure.QuasiMeasurePreserving.id μ)
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := volume))
  convert hproj.comp (measurePreserving_prodAssoc μ volume volume).quasiMeasurePreserving using 1
  rfl

/-- The physical-space integrand obtained by adding one difference is jointly
almost everywhere strongly measurable in the tail, new parameter, and space. -/
lemma aux_sobolevDifference_iteratedDifference_next_joint_aestronglyMeasurable
    (n : ℕ) (f : ℝ → ℂ) (hfmeas : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable
      (fun z : ((Fin n → ℝ) × ℝ) × ℝ ↦
        iteratedMultiplicativeDifference n z.1.1 f z.2 *
          starRingEnd ℂ (iteratedMultiplicativeDifference n z.1.1 f (z.2 + z.1.2)))
      ((volume.prod volume).prod volume) := by
  have hG := aux_sobolevDifference_iteratedDifference_joint_aestronglyMeasurable n f hfmeas
  have hleft : AEStronglyMeasurable
      (fun z : ((Fin n → ℝ) × ℝ) × ℝ ↦
        iteratedMultiplicativeDifference n z.1.1 f z.2)
      ((volume.prod volume).prod volume) := by
    exact hG.comp_quasiMeasurePreserving
      (aux_sobolevDifference_qmp_drop_middle (volume : Measure (Fin n → ℝ)))
  have hadd : Measure.QuasiMeasurePreserving (fun p : ℝ × ℝ ↦ p.2 + p.1)
      ((volume : Measure ℝ).prod volume) volume := by
    refine MeasureTheory.QuasiMeasurePreserving.prod_of_left (by fun_prop) ?_
    filter_upwards with x
    exact (measurePreserving_add_left volume x).quasiMeasurePreserving
  have hpair : Measure.QuasiMeasurePreserving
      (fun z : (Fin n → ℝ) × (ℝ × ℝ) ↦ (z.1, z.2.2 + z.2.1))
      ((volume : Measure (Fin n → ℝ)).prod ((volume : Measure ℝ).prod volume))
      ((volume : Measure (Fin n → ℝ)).prod volume) := by
    exact MeasureTheory.QuasiMeasurePreserving.prodMap
      (Measure.QuasiMeasurePreserving.id (volume : Measure (Fin n → ℝ))) hadd
  have hshift_map : Measure.QuasiMeasurePreserving
      (fun z : ((Fin n → ℝ) × ℝ) × ℝ ↦ (z.1.1, z.2 + z.1.2))
      ((volume.prod volume).prod volume) (volume.prod volume) := by
    convert hpair.comp
      (measurePreserving_prodAssoc (volume : Measure (Fin n → ℝ)) volume volume).quasiMeasurePreserving
      using 1
    rfl
  have hright : AEStronglyMeasurable
      (fun z : ((Fin n → ℝ) × ℝ) × ℝ ↦
        iteratedMultiplicativeDifference n z.1.1 f (z.2 + z.1.2))
      ((volume.prod volume).prod volume) := by
    exact hG.comp_quasiMeasurePreserving hshift_map
  exact hleft.mul hright.star

/-- The Fourier integrand of a first difference of a jointly parameterized
iterated difference. -/
def aux_sobolevDifference_iteratedDifference_fourierIntegrand (n : ℕ) (f : ℝ → ℂ) :
    (((Fin n → ℝ) × ℝ) × ℝ) × ℝ → ℂ :=
  fun z ↦ (𝐞 (-(z.2 * z.1.2)) : ℂ) *
    (iteratedMultiplicativeDifference n z.1.1.1 f z.2 *
      starRingEnd ℂ
        (iteratedMultiplicativeDifference n z.1.1.1 f (z.2 + z.1.1.2)))

/-- The raw Fourier transform after adding one multiplicative difference is
jointly almost everywhere strongly measurable in the remaining parameters,
the new difference parameter, and frequency. -/
lemma aux_sobolevDifference_iteratedDifference_next_fourier_joint_aestronglyMeasurable
    (n : ℕ) (f : ℝ → ℂ) (hfmeas : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable
      (fun q : (Fin n → ℝ) × (ℝ × ℝ) ↦
        𝓕 (iteratedMultiplicativeDifference (n + 1) (Fin.cons q.2.1 q.1) f) q.2.2)
      (volume.prod (volume.prod volume)) := by
  have hdiff := aux_sobolevDifference_iteratedDifference_next_joint_aestronglyMeasurable
    n f hfmeas
  have hdrop : Measure.QuasiMeasurePreserving
      (fun z : (((Fin n → ℝ) × ℝ) × ℝ) × ℝ ↦ (z.1.1, z.2))
      (((volume.prod volume).prod volume).prod volume)
      ((volume.prod volume).prod volume) := by
    exact aux_sobolevDifference_qmp_drop_middle
      ((volume : Measure (Fin n → ℝ)).prod volume)
  have hdiff' : AEStronglyMeasurable
      (fun z : (((Fin n → ℝ) × ℝ) × ℝ) × ℝ ↦
        iteratedMultiplicativeDifference n z.1.1.1 f z.2 *
          starRingEnd ℂ
            (iteratedMultiplicativeDifference n z.1.1.1 f (z.2 + z.1.1.2)))
      (((volume.prod volume).prod volume).prod volume) := by
    exact hdiff.comp_quasiMeasurePreserving hdrop
  have hphase : StronglyMeasurable
      (fun z : (((Fin n → ℝ) × ℝ) × ℝ) × ℝ ↦ (𝐞 (-(z.2 * z.1.2)) : ℂ)) := by
    exact (continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (by fun_prop))).stronglyMeasurable
  have hint : AEStronglyMeasurable
      (aux_sobolevDifference_iteratedDifference_fourierIntegrand n f)
      (((volume.prod volume).prod volume).prod volume) := by
    exact hphase.aestronglyMeasurable.mul hdiff'
  have hinter : AEStronglyMeasurable
      (fun p : ((Fin n → ℝ) × ℝ) × ℝ ↦
        ∫ x : ℝ, aux_sobolevDifference_iteratedDifference_fourierIntegrand n f (p, x))
      ((volume.prod volume).prod volume) :=
    hint.integral_prod_right'
  have hassoc := measurePreserving_prodAssoc (volume : Measure (Fin n → ℝ))
    (volume : Measure ℝ) (volume : Measure ℝ)
  have houter : AEStronglyMeasurable
      (fun q : (Fin n → ℝ) × (ℝ × ℝ) ↦
        ∫ x : ℝ, aux_sobolevDifference_iteratedDifference_fourierIntegrand n f
          (((q.1, q.2.1), q.2.2), x))
      (volume.prod (volume.prod volume)) := by
    exact hinter.comp_quasiMeasurePreserving
      (hassoc.symm MeasurableEquiv.prodAssoc).quasiMeasurePreserving
  have heq : (fun q : (Fin n → ℝ) × (ℝ × ℝ) ↦
      ∫ x : ℝ, aux_sobolevDifference_iteratedDifference_fourierIntegrand n f
        (((q.1, q.2.1), q.2.2), x)) =
      fun q : (Fin n → ℝ) × (ℝ × ℝ) ↦
        𝓕 (iteratedMultiplicativeDifference (n + 1) (Fin.cons q.2.1 q.1) f) q.2.2 := by
    funext q
    rw [iteratedMultiplicativeDifference, Real.fourier_eq]
    apply integral_congr_ae
    filter_upwards with x
    simp only [aux_sobolevDifference_iteratedDifference_fourierIntegrand,
      multiplicativeDifference, Real.inner_apply]
    have htail : (fun i : Fin n ↦
        (Fin.cons q.2.1 q.1 : Fin (n + 1) → ℝ) i.succ) = q.1 := by
      funext i
      simp
    have hzero : (Fin.cons q.2.1 q.1 : Fin (n + 1) → ℝ) 0 = q.2.1 := by simp
    rw [htail, hzero]
    simp only [Circle.smul_def]
    ring
  rwa [heq] at houter

/-- The nonnegative raw Fourier energy after adding one difference is jointly
almost everywhere measurable in the tail, new difference, and frequency. -/
lemma aux_sobolevDifference_iteratedDifference_next_fourier_joint_aemeasurable_energy
    (n : ℕ) (f : ℝ → ℂ) (hfmeas : AEStronglyMeasurable f volume) :
    AEMeasurable
      (fun q : (Fin n → ℝ) × (ℝ × ℝ) ↦
        ‖𝓕 (iteratedMultiplicativeDifference (n + 1) (Fin.cons q.2.1 q.1) f) q.2.2‖ₑ ^
          (2 : ℕ))
      (volume.prod (volume.prod volume)) := by
  exact
    (aux_sobolevDifference_iteratedDifference_next_fourier_joint_aestronglyMeasurable
      n f hfmeas).enorm.pow measurable_const.aemeasurable

/-- Separates the first difference parameter from the remaining parameters,
while retaining the frequency coordinate as the innermost coordinate. -/
def aux_sobolevDifference_lowTailCoordinates (n : ℕ) :
    (Fin (n + 1) → ℝ) × ℝ → (Fin n → ℝ) × (ℝ × ℝ) :=
  fun p ↦ (fun i : Fin n ↦ p.1 i.succ, (p.1 0, p.2))

/-- The low-frequency parameter coordinate permutation preserves product
Lebesgue measure after restricting the frequency coordinate. -/
lemma aux_sobolevDifference_measurePreserving_lowTailCoordinates (n : ℕ) (R : ℝ) :
    MeasurePreserving (aux_sobolevDifference_lowTailCoordinates n)
      (volume.prod (volume.restrict (Set.Icc (-R) R)))
      (volume.prod (volume.prod (volume.restrict (Set.Icc (-R) R)))) := by
  let e : (Fin (n + 1) → ℝ) ≃ᵐ (ℝ × (Fin n → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
  have he : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
  have hfirst := he.prod
    (MeasureTheory.MeasurePreserving.id (volume.restrict (Set.Icc (-R) R)))
  have hassoc := measurePreserving_prodAssoc (volume : Measure ℝ)
    (volume : Measure (Fin n → ℝ))
    (volume.restrict (Set.Icc (-R) R))
  have hswap₁ := (Measure.measurePreserving_swap
    (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (Fin n → ℝ)).prod
      (volume.restrict (Set.Icc (-R) R))))
  have hassoc₂ := measurePreserving_prodAssoc (volume : Measure (Fin n → ℝ))
    (volume.restrict (Set.Icc (-R) R)) (volume : Measure ℝ)
  have hswap₂ := (MeasureTheory.MeasurePreserving.id
    (volume : Measure (Fin n → ℝ))).prod
      (Measure.measurePreserving_swap
        (μ := volume.restrict (Set.Icc (-R) R)) (ν := (volume : Measure ℝ)))
  have h := hswap₂.comp (hassoc₂.comp (hswap₁.comp (hassoc.comp hfirst)))
  have hzero (q : Fin (n + 1) → ℝ) : (e q).1 = q 0 := by
    have hq := congrFun (e.symm_apply_apply q) 0
    simpa [e] using hq
  have htail (q : Fin (n + 1) → ℝ) (i : Fin n) : (e q).2 i = q i.succ := by
    have hq := congrFun (e.symm_apply_apply q) i.succ
    simpa [e] using hq
  have hfun : aux_sobolevDifference_lowTailCoordinates n =
      (Prod.map id Prod.swap ∘ MeasurableEquiv.prodAssoc ∘ Prod.swap ∘
        MeasurableEquiv.prodAssoc ∘ Prod.map e id) := by
    funext p
    apply Prod.ext
    · funext i
      exact (htail p.1 i).symm
    · apply Prod.ext
      · exact (hzero p.1).symm
      · rfl
  rw [hfun]
  exact h

/-- A one-step low-frequency estimate in the first difference parameter lifts
to all parameters after Tonelli reindexing. -/
lemma aux_sobolevDifference_lowFrequency_integrate_reindex
    (n : ℕ) (R : ℝ)
    (E : (Fin (n + 1) → ℝ) → ℝ → ℝ≥0∞)
    (N : (Fin n → ℝ) → ℝ≥0∞) (K : ℝ≥0∞)
    (hE : AEMeasurable
      (fun q : (Fin n → ℝ) × (ℝ × ℝ) ↦ E (Fin.cons q.2.1 q.1) q.2.2)
      (volume.prod (volume.prod (volume.restrict (Set.Icc (-R) R)))))
    (hKtop : K ≠ ∞)
    (hone : ∀ l : Fin n → ℝ,
      (∫⁻ h : ℝ, ∫⁻ ξ : ℝ in Set.Icc (-R) R,
        E (Fin.cons h l) ξ) ≤ K * N l) :
    (∫⁻ h : Fin (n + 1) → ℝ, ∫⁻ ξ : ℝ in Set.Icc (-R) R, E h ξ) ≤
      K * ∫⁻ l : Fin n → ℝ, N l := by
  let P := aux_sobolevDifference_lowTailCoordinates n
  let F : (Fin n → ℝ) × (ℝ × ℝ) → ℝ≥0∞ :=
    fun q ↦ E (Fin.cons q.2.1 q.1) q.2.2
  have hP := aux_sobolevDifference_measurePreserving_lowTailCoordinates n R
  have hF : AEMeasurable F
      (volume.prod (volume.prod (volume.restrict (Set.Icc (-R) R)))) := by
    simpa [F] using hE
  have htransport :
      (∫⁻ p : (Fin (n + 1) → ℝ) × ℝ,
        F (P p) ∂(volume.prod (volume.restrict (Set.Icc (-R) R)))) =
        ∫⁻ q : (Fin n → ℝ) × (ℝ × ℝ), F q ∂
          (volume.prod (volume.prod (volume.restrict (Set.Icc (-R) R)))) := by
    calc
      (∫⁻ p : (Fin (n + 1) → ℝ) × ℝ,
          F (P p) ∂(volume.prod (volume.restrict (Set.Icc (-R) R)))) =
          ∫⁻ q : (Fin n → ℝ) × (ℝ × ℝ), F q ∂
            Measure.map P (volume.prod (volume.restrict (Set.Icc (-R) R))) :=
        MeasureTheory.lintegral_comp'
          (by rw [hP.map_eq]; exact hF) hP.measurable.aemeasurable
      _ = ∫⁻ q : (Fin n → ℝ) × (ℝ × ℝ), F q ∂
            (volume.prod (volume.prod (volume.restrict (Set.Icc (-R) R)))) := by
        rw [hP.map_eq]
  have hpoint (p : (Fin (n + 1) → ℝ) × ℝ) : F (P p) = E p.1 p.2 := by
    dsimp [F, P, aux_sobolevDifference_lowTailCoordinates]
    congr 2
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      rfl
  have hsource : AEMeasurable (fun p : (Fin (n + 1) → ℝ) × ℝ ↦ E p.1 p.2)
      (volume.prod (volume.restrict (Set.Icc (-R) R))) := by
    apply (hF.comp_quasiMeasurePreserving hP.quasiMeasurePreserving).congr
    filter_upwards with p
    exact hpoint p
  let Q : ((Fin n → ℝ) × ℝ) × ℝ → (Fin n → ℝ) × (ℝ × ℝ) :=
    MeasurableEquiv.prodAssoc
  have hQ := measurePreserving_prodAssoc (volume : Measure (Fin n → ℝ))
    (volume : Measure ℝ) (volume.restrict (Set.Icc (-R) R))
  let G : ((Fin n → ℝ) × ℝ) × ℝ → ℝ≥0∞ := fun q ↦ F (Q q)
  have hG : AEMeasurable G
      ((volume.prod volume).prod (volume.restrict (Set.Icc (-R) R))) := by
    exact hF.comp_quasiMeasurePreserving hQ.quasiMeasurePreserving
  have hassocTransport :
      (∫⁻ q : ((Fin n → ℝ) × ℝ) × ℝ, G q ∂
          ((volume.prod volume).prod (volume.restrict (Set.Icc (-R) R)))) =
        ∫⁻ q : (Fin n → ℝ) × (ℝ × ℝ), F q ∂
          (volume.prod (volume.prod (volume.restrict (Set.Icc (-R) R)))) := by
    calc
      (∫⁻ q : ((Fin n → ℝ) × ℝ) × ℝ, G q ∂
          ((volume.prod volume).prod (volume.restrict (Set.Icc (-R) R)))) =
        ∫⁻ q : (Fin n → ℝ) × (ℝ × ℝ), F q ∂
          Measure.map Q ((volume.prod volume).prod
            (volume.restrict (Set.Icc (-R) R))) :=
        MeasureTheory.lintegral_comp'
          (by rw [hQ.map_eq]; exact hF) hQ.measurable.aemeasurable
      _ = _ := by rw [hQ.map_eq]
  have hGinner : AEMeasurable
      (fun p : (Fin n → ℝ) × ℝ ↦
        ∫⁻ ξ : ℝ in Set.Icc (-R) R, G (p, ξ)) (volume.prod volume) := by
    exact hG.lintegral_prod_right'
  calc
    (∫⁻ h : Fin (n + 1) → ℝ, ∫⁻ ξ : ℝ in Set.Icc (-R) R, E h ξ) =
        ∫⁻ p : (Fin (n + 1) → ℝ) × ℝ,
          E p.1 p.2 ∂(volume.prod (volume.restrict (Set.Icc (-R) R))) := by
            exact (MeasureTheory.lintegral_prod
              (fun p : (Fin (n + 1) → ℝ) × ℝ ↦ E p.1 p.2) hsource).symm
    _ = ∫⁻ p : (Fin (n + 1) → ℝ) × ℝ,
          F (P p) ∂(volume.prod (volume.restrict (Set.Icc (-R) R))) := by
            apply MeasureTheory.lintegral_congr
            intro p
            exact (hpoint p).symm
    _ = ∫⁻ q : (Fin n → ℝ) × (ℝ × ℝ), F q ∂
          (volume.prod (volume.prod (volume.restrict (Set.Icc (-R) R)))) := htransport
    _ = ∫⁻ l : Fin n → ℝ, ∫⁻ h : ℝ, ∫⁻ ξ : ℝ in Set.Icc (-R) R,
          E (Fin.cons h l) ξ := by
            rw [← hassocTransport]
            rw [MeasureTheory.lintegral_prod G hG]
            rw [MeasureTheory.lintegral_prod _ hGinner]
            rfl
    _ ≤ ∫⁻ l : Fin n → ℝ, K * N l := by
            apply MeasureTheory.lintegral_mono
            exact hone
    _ = K * ∫⁻ l : Fin n → ℝ, N l := by
            rw [MeasureTheory.lintegral_const_mul' K N hKtop]

/-- For `s ≥ 1`, expanding the definition of the uniformity norm gives the
integral of the next lower order Fourier `L∞` profile. -/
lemma aux_sobolevDifference_uNorm_succ_rpow_eq_lintegral
    (s : ℕ) (hs : 1 ≤ s) (f : ℝ → ℂ) :
    uNorm (s + 1) f ^ ((2 : ℝ) ^ (s - 1)) =
      ∫⁻ h : Fin (s - 1) → ℝ,
        eLpNorm (𝓕 (iteratedMultiplicativeDifference (s - 1) h f)) ∞ volume := by
  rcases Nat.eq_or_lt_of_le hs with hs | hs
  · subst s
    norm_num [uNorm]
    change eLpNorm (𝓕 f) ∞ volume =
      ∫⁻ h : Fin 0 → ℝ,
        eLpNorm (𝓕 (iteratedMultiplicativeDifference 0 h f)) ∞ volume
    simp [iteratedMultiplicativeDifference, volume_pi,
      Measure.pi_of_empty fun _ : Fin 0 ↦ (volume : Measure ℝ)]
  · have htwo : 2 ≤ s := by omega
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' htwo
    have hne : n + 2 + 1 ≠ 2 := by omega
    have hgt : 2 < n + 2 + 1 := by omega
    have hsub₁ : n + 2 + 1 - 2 = n + 1 := by omega
    have hsub₂ : n + 2 - 1 = n + 1 := by omega
    rw [uNorm, if_neg hne, if_pos hgt, hsub₁, hsub₂]
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp
    simp

/-- A unit-bounded interval-supported function has raw Fourier `L²` energy
at most the interval length. -/
lemma aux_sobolevDifference_eLpNorm_fourier_two_mul_le_interval
    (a b : ℝ) (hab : a ≤ b) (g : ℝ → ℂ)
    (hg : AEStronglyMeasurable g volume)
    (hbound : ∀ᵐ x : ℝ ∂volume, ‖g x‖ ≤ 1)
    (hsupp : ∀ᵐ x : ℝ ∂volume, x ∉ Set.Icc a b → g x = 0) :
    eLpNorm (𝓕 g) (2 : ℝ≥0∞) volume *
        eLpNorm (𝓕 g) (2 : ℝ≥0∞) volume ≤ ENNReal.ofReal (b - a) := by
  have hg2 : MemLp g (2 : ℝ≥0∞) volume :=
    aux_memLp_of_ae_bound_of_ae_support g hg 1 hbound (Set.Icc a b)
      measurableSet_Icc isCompact_Icc.measure_lt_top hsupp 2
  have hraw : aux_l2Fourier g =ᵐ[volume] 𝓕 g := by
    rw [aux_l2Fourier, dif_pos hg2]
    exact aux_l2Fourier_eq_raw_ae g
      (aux_memLp_of_ae_bound_of_ae_support g hg 1 hbound (Set.Icc a b)
        measurableSet_Icc isCompact_Icc.measure_lt_top hsupp 1) hg2
  have hfourier : eLpNorm (𝓕 g) (2 : ℝ≥0∞) volume =
      eLpNorm g (2 : ℝ≥0∞) volume := by
    rw [← eLpNorm_congr_ae hraw]
    exact aux_eLpNorm_aux_l2Fourier_eq g hg2
  have hpoint : ∀ᵐ x : ℝ ∂volume,
      ‖g x‖ₑ ^ (2 : ℕ) ≤
        (Set.Icc a b).indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
    filter_upwards [hbound, hsupp] with x hx hzero
    by_cases hxA : x ∈ Set.Icc a b
    · rw [Set.indicator_of_mem hxA]
      have henorm : ‖g x‖ₑ ≤ 1 := by
        rw [← ofReal_norm, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hx
      exact pow_le_one₀ bot_le henorm
    · rw [Set.indicator_of_notMem hxA]
      simp [hzero hxA]
  have henergy : eLpNorm g (2 : ℝ≥0∞) volume *
      eLpNorm g (2 : ℝ≥0∞) volume ≤ ENNReal.ofReal (b - a) := by
    calc
      eLpNorm g (2 : ℝ≥0∞) volume * eLpNorm g (2 : ℝ≥0∞) volume =
          (eLpNorm g (2 : ℝ≥0∞) volume) ^ (2 : ℝ) := by
            rw [ENNReal.rpow_two, pow_two]
      _ = ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2 : ℕ) :=
        aux_sobolevDifference_eLpNorm_two_sq_eq_lintegral_enorm g
      _ ≤ ∫⁻ x : ℝ, (Set.Icc a b).indicator (fun _ ↦ (1 : ℝ≥0∞)) x :=
        MeasureTheory.lintegral_mono_ae hpoint
      _ = volume (Set.Icc a b) := by
        rw [MeasureTheory.lintegral_indicator measurableSet_Icc, setLIntegral_one]
      _ = ENNReal.ofReal (b - a) := by
        rw [Real.volume_Icc]
  rw [hfourier]
  exact henergy

/-- The raw Fourier transform of a unit-bounded interval-supported function
is pointwise bounded by the interval length. -/
lemma aux_sobolevDifference_enorm_fourier_le_interval
    (a b : ℝ) (hab : a ≤ b) (g : ℝ → ℂ)
    (hg : AEStronglyMeasurable g volume)
    (hbound : ∀ᵐ x : ℝ ∂volume, ‖g x‖ ≤ 1)
    (hsupp : ∀ᵐ x : ℝ ∂volume, x ∉ Set.Icc a b → g x = 0) (ξ : ℝ) :
    ‖𝓕 g ξ‖ₑ ≤ ENNReal.ofReal (b - a) := by
  have hg1 : MemLp g (1 : ℝ≥0∞) volume :=
    aux_memLp_of_ae_bound_of_ae_support g hg 1 hbound (Set.Icc a b)
      measurableSet_Icc isCompact_Icc.measure_lt_top hsupp 1
  have hgint : Integrable (fun x : ℝ ↦ ‖g x‖) volume := by
    convert hg1.integrable_norm_rpow (by norm_num) (by norm_num) using 1 <;> norm_num
  have hind : Integrable ((Set.Icc a b).indicator (fun _ ↦ (1 : ℝ))) volume := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const isCompact_Icc.measure_lt_top.ne
  have hpoint : ∀ᵐ x : ℝ ∂volume, ‖g x‖ ≤
      (Set.Icc a b).indicator (fun _ ↦ (1 : ℝ)) x := by
    filter_upwards [hbound, hsupp] with x hx hzero
    by_cases hxA : x ∈ Set.Icc a b
    · simpa [Set.indicator_of_mem hxA] using hx
    · simp [Set.indicator_of_notMem hxA, hzero hxA]
  have hreal : (∫ x : ℝ, ‖g x‖) ≤ b - a := by
    calc
      (∫ x : ℝ, ‖g x‖) ≤
          ∫ x : ℝ, (Set.Icc a b).indicator (fun _ ↦ (1 : ℝ)) x :=
        integral_mono_ae hgint hind hpoint
      _ = volume.real (Set.Icc a b) := by
        rw [integral_indicator_const 1 measurableSet_Icc]
        simp
      _ = b - a := by
        rw [Measure.real, Real.volume_Icc,
          ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal
    ((VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume
      (innerₗ ℝ) g ξ).trans hreal)

/-- The fixed-function low-frequency estimate after applying the interval
support and one-boundedness hypotheses. -/
lemma aux_sobolevDifference_lowFrequency_one_step_interval
    (a b R : ℝ) (hab : a ≤ b) (hR : 0 ≤ R) (g : ℝ → ℂ)
    (hg : AEStronglyMeasurable g volume)
    (hbound : ∀ᵐ x : ℝ ∂volume, ‖g x‖ ≤ 1)
    (hsupp : ∀ᵐ x : ℝ ∂volume, x ∉ Set.Icc a b → g x = 0) :
    (∫⁻ h : ℝ, ∫⁻ ξ : ℝ in Set.Icc (-R) R,
      ‖𝓕 (multiplicativeDifference h g) ξ‖ₑ ^ (2 : ℕ)) ≤
      ENNReal.ofReal (2 * R) * ENNReal.ofReal (b - a) *
        eLpNorm (𝓕 g) ∞ volume * ENNReal.ofReal (b - a) := by
  have hg1 : MemLp g (1 : ℝ≥0∞) volume :=
    aux_memLp_of_ae_bound_of_ae_support g hg 1 hbound (Set.Icc a b)
      measurableSet_Icc isCompact_Icc.measure_lt_top hsupp 1
  have hg2 : MemLp g (2 : ℝ≥0∞) volume :=
    aux_memLp_of_ae_bound_of_ae_support g hg 1 hbound (Set.Icc a b)
      measurableSet_Icc isCompact_Icc.measure_lt_top hsupp 2
  have hM : ∀ᵐ ξ : ℝ ∂volume,
      ‖𝓕 g ξ‖ₑ ≤ eLpNorm (𝓕 g) ∞ volume := by
    simpa only [eLpNorm_exponent_top] using
      (MeasureTheory.ae_le_eLpNormEssSup (f := 𝓕 g) (μ := volume))
  have hE := aux_sobolevDifference_low_frequency_fourier_difference_energy_le
    g hg hg1 hg2 (ENNReal.ofReal (b - a)) (eLpNorm (𝓕 g) ∞ volume)
    (fun ξ ↦ aux_sobolevDifference_enorm_fourier_le_interval a b hab g hg hbound hsupp ξ)
    hM R hR
  have htwo := aux_sobolevDifference_eLpNorm_fourier_two_mul_le_interval
    a b hab g hg hbound hsupp
  calc
    (∫⁻ h : ℝ, ∫⁻ ξ : ℝ in Set.Icc (-R) R,
        ‖𝓕 (multiplicativeDifference h g) ξ‖ₑ ^ (2 : ℕ)) ≤
        ENNReal.ofReal (2 * R) * ENNReal.ofReal (b - a) *
          eLpNorm (𝓕 g) ∞ volume *
            (eLpNorm (𝓕 g) 2 volume * eLpNorm (𝓕 g) 2 volume) := hE
    _ ≤ ENNReal.ofReal (2 * R) * ENNReal.ofReal (b - a) *
          eLpNorm (𝓕 g) ∞ volume * ENNReal.ofReal (b - a) := by
      gcongr

/-- Normalizes the one-step low-frequency coefficient to the manuscript
form. -/
lemma aux_sobolevDifference_lowFrequency_one_step_coefficient
    (m R : ℝ) (hm : 0 ≤ m) (_hR : 0 ≤ R) (U : ℝ≥0∞) :
    ENNReal.ofReal (2 * R) * ENNReal.ofReal m * U * ENNReal.ofReal m =
      ENNReal.ofReal (2 * m ^ 2) * ENNReal.ofReal R * U := by
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_pow hm]
  ring

/-- The fixed-function low-frequency estimate after fixing all but the first
difference parameter. -/
lemma aux_sobolevDifference_iterated_lowFrequency_one_step
    (n : ℕ) (a b R : ℝ) (hab : a ≤ b) (hR : 0 ≤ R) (f : ℝ → ℂ)
    (hfmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x : ℝ ∂volume, ‖f x‖ ≤ 1)
    (hsupp : ∀ᵐ x : ℝ ∂volume, x ∉ Set.Icc a b → f x = 0)
    (l : Fin n → ℝ) :
    (∫⁻ h : ℝ, ∫⁻ ξ : ℝ in Set.Icc (-R) R,
      ‖𝓕 (iteratedMultiplicativeDifference (n + 1) (Fin.cons h l) f) ξ‖ₑ ^ (2 : ℕ)) ≤
      ENNReal.ofReal (2 * (b - a) ^ 2) * ENNReal.ofReal R *
        eLpNorm (𝓕 (iteratedMultiplicativeDifference n l f)) ∞ volume := by
  rcases aux_sobolevDifference_iteratedDifference_section_data n l (Set.Icc a b) f
    hfmeas hbound hsupp with ⟨hgmeas, hgbound, hgsupp⟩
  have hraw := aux_sobolevDifference_lowFrequency_one_step_interval a b R hab hR
    (iteratedMultiplicativeDifference n l f) hgmeas hgbound hgsupp
  calc
    (∫⁻ h : ℝ, ∫⁻ ξ : ℝ in Set.Icc (-R) R,
        ‖𝓕 (iteratedMultiplicativeDifference (n + 1) (Fin.cons h l) f) ξ‖ₑ ^ (2 : ℕ)) =
        ∫⁻ h : ℝ, ∫⁻ ξ : ℝ in Set.Icc (-R) R,
          ‖𝓕 (multiplicativeDifference h (iteratedMultiplicativeDifference n l f)) ξ‖ₑ ^
            (2 : ℕ) := by rfl
    _ ≤ ENNReal.ofReal (2 * R) * ENNReal.ofReal (b - a) *
          eLpNorm (𝓕 (iteratedMultiplicativeDifference n l f)) ∞ volume *
            ENNReal.ofReal (b - a) := hraw
    _ = ENNReal.ofReal (2 * (b - a) ^ 2) * ENNReal.ofReal R *
          eLpNorm (𝓕 (iteratedMultiplicativeDifference n l f)) ∞ volume := by
      rw [aux_sobolevDifference_lowFrequency_one_step_coefficient (b - a) R
        (sub_nonneg.mpr hab) hR]

/-- The complete low-frequency energy bound for all iterated difference
parameters. -/
lemma aux_sobolevDifference_iterated_lowFrequency_energy_le
    (n : ℕ) (a b R : ℝ) (hab : a ≤ b) (hR : 0 ≤ R) (f : ℝ → ℂ)
    (hfmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x : ℝ ∂volume, ‖f x‖ ≤ 1)
    (hsupp : ∀ᵐ x : ℝ ∂volume, x ∉ Set.Icc a b → f x = 0) :
    (∫⁻ h : Fin (n + 1) → ℝ, ∫⁻ ξ : ℝ in Set.Icc (-R) R,
      ‖𝓕 (iteratedMultiplicativeDifference (n + 1) h f) ξ‖ₑ ^ (2 : ℕ)) ≤
      ENNReal.ofReal (2 * (b - a) ^ 2) * ENNReal.ofReal R *
        uNorm (n + 2) f ^ ((2 : ℝ) ^ n) := by
  let E : (Fin (n + 1) → ℝ) → ℝ → ℝ≥0∞ :=
    fun h ξ ↦ ‖𝓕 (iteratedMultiplicativeDifference (n + 1) h f) ξ‖ₑ ^ (2 : ℕ)
  let N : (Fin n → ℝ) → ℝ≥0∞ :=
    fun l ↦ eLpNorm (𝓕 (iteratedMultiplicativeDifference n l f)) ∞ volume
  let K : ℝ≥0∞ := ENNReal.ofReal (2 * (b - a) ^ 2) * ENNReal.ofReal R
  have hEfull :=
    aux_sobolevDifference_iteratedDifference_next_fourier_joint_aemeasurable_energy n f hfmeas
  have hE : AEMeasurable
      (fun q : (Fin n → ℝ) × (ℝ × ℝ) ↦ E (Fin.cons q.2.1 q.1) q.2.2)
      (volume.prod (volume.prod (volume.restrict (Set.Icc (-R) R)))) := by
    apply hEfull.mono_measure
    exact Measure.prod_mono le_rfl
      (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hKtop : K ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hone : ∀ l : Fin n → ℝ,
      (∫⁻ h : ℝ, ∫⁻ ξ : ℝ in Set.Icc (-R) R,
        E (Fin.cons h l) ξ) ≤ K * N l := by
    intro l
    exact aux_sobolevDifference_iterated_lowFrequency_one_step n a b R hab hR f
      hfmeas hbound hsupp l
  have hlow := aux_sobolevDifference_lowFrequency_integrate_reindex n R E N K hE hKtop hone
  have hu := aux_sobolevDifference_uNorm_succ_rpow_eq_lintegral (n + 1) (by omega) f
  change (∫⁻ h : Fin (n + 1) → ℝ, ∫⁻ ξ : ℝ in Set.Icc (-R) R,
      E h ξ) ≤ K * uNorm (n + 2) f ^ ((2 : ℝ) ^ n)
  calc
    (∫⁻ h : Fin (n + 1) → ℝ, ∫⁻ ξ : ℝ in Set.Icc (-R) R,
        E h ξ) ≤ K * ∫⁻ l : Fin n → ℝ, N l := hlow
    _ = K * uNorm (n + 2) f ^ ((2 : ℝ) ^ n) := by
      congr 1
      simpa [N] using hu.symm

/-- A nonnegative negative-order Sobolev weight is bounded by one. -/
lemma aux_sobolevDifference_sobolev_weight_norm_le_one
    (σ ξ : ℝ) (hσ : 0 ≤ σ) :
    ‖japaneseBracket ξ ^ (-σ)‖ ≤ 1 := by
  have hjap_nonneg : 0 ≤ japaneseBracket ξ := Real.sqrt_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hjap_nonneg _)]
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · unfold japaneseBracket
    have harg : (1 : ℝ) ≤ 1 + |ξ| ^ 2 := by
      nlinarith [sq_nonneg |ξ|]
    simpa using (Real.sqrt_le_sqrt harg)
  · linarith

/-- On every frequency set, nonnegative-order Sobolev weighting can only
decrease the Fourier `L²` energy. -/
lemma aux_sobolevDifference_low_weighted_energy_le_unweighted
    (σ : ℝ) (hσ : 0 ≤ σ) (S : Set ℝ) (F : ℝ → ℂ) :
    (∫⁻ ξ : ℝ in S,
      ‖(japaneseBracket ξ ^ (-σ)) • F ξ‖ₑ ^ (2 : ℝ)) ≤
      ∫⁻ ξ : ℝ in S, ‖F ξ‖ₑ ^ (2 : ℝ) := by
  apply MeasureTheory.lintegral_mono
  intro ξ
  have hnorm : ‖(japaneseBracket ξ ^ (-σ)) • F ξ‖ₑ ≤ ‖F ξ‖ₑ := by
    rw [enorm_smul, ← ofReal_norm]
    calc
      ENNReal.ofReal ‖japaneseBracket ξ ^ (-σ)‖ * ‖F ξ‖ₑ ≤
          (1 : ℝ≥0∞) * ‖F ξ‖ₑ := by
        apply mul_le_mul_left
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal
          (aux_sobolevDifference_sobolev_weight_norm_le_one σ ξ hσ)
      _ = ‖F ξ‖ₑ := one_mul _
  exact ENNReal.rpow_le_rpow hnorm (by norm_num)

/-- A raw Sobolev energy is bounded by its unweighted raw low-frequency
energy plus the Plancherel high-frequency energy. -/
lemma aux_sobolevDifference_sobolevNormRaw_high_low_split_le
    (σ R : ℝ) (hσ : 0 ≤ σ) (g : ℝ → ℂ)
    (hg1 : MemLp g (1 : ℝ≥0∞) volume)
    (hg2 : MemLp g (2 : ℝ≥0∞) volume) :
    aux_sobolevNormRaw σ g ^ (2 : ℝ) ≤
      (∫⁻ ξ : ℝ in aux_sobolevDifference_lowFrequency R,
        ‖𝓕 g ξ‖ₑ ^ (2 : ℝ)) +
      ∫⁻ ξ : ℝ in aux_sobolevDifference_highFrequency R,
        ‖(japaneseBracket ξ ^ (-σ)) •
          (Lp.fourierTransformₗᵢ ℝ ℂ hg2.toLp) ξ‖ₑ ^ (2 : ℝ) := by
  have hFraw : (fun ξ : ℝ ↦ (Lp.fourierTransformₗᵢ ℝ ℂ hg2.toLp) ξ) =ᵐ[volume]
      𝓕 g := aux_l2Fourier_eq_raw_ae g hg1 hg2
  have hlow_raw :
      (∫⁻ ξ : ℝ in aux_sobolevDifference_lowFrequency R,
        ‖(Lp.fourierTransformₗᵢ ℝ ℂ hg2.toLp) ξ‖ₑ ^ (2 : ℝ)) =
      ∫⁻ ξ : ℝ in aux_sobolevDifference_lowFrequency R,
        ‖𝓕 g ξ‖ₑ ^ (2 : ℝ) := by
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards [hFraw.restrict] with ξ hξ
    rw [hξ]
  rw [aux_sobolevDifference_sobolevNormRaw_eq_sobolevNorm σ g hg2,
    aux_sobolevDifference_sobolevNorm_energy_split σ R hg2.toLp]
  apply add_le_add_left
  calc
    (∫⁻ ξ : ℝ in aux_sobolevDifference_lowFrequency R,
        ‖(japaneseBracket ξ ^ (-σ)) •
          (Lp.fourierTransformₗᵢ ℝ ℂ hg2.toLp) ξ‖ₑ ^ (2 : ℝ)) ≤
        ∫⁻ ξ : ℝ in aux_sobolevDifference_lowFrequency R,
          ‖(Lp.fourierTransformₗᵢ ℝ ℂ hg2.toLp) ξ‖ₑ ^ (2 : ℝ) :=
      aux_sobolevDifference_low_weighted_energy_le_unweighted σ hσ _ _
    _ = ∫⁻ ξ : ℝ in aux_sobolevDifference_lowFrequency R,
        ‖𝓕 g ξ‖ₑ ^ (2 : ℝ) := hlow_raw

/-- The all-parameter raw low-frequency energy is measurable.  It is the
pullback of the tail/head/frequency energy along the product-coordinate
permutation used in the low-frequency estimate. -/
lemma aux_sobolevDifference_iterated_low_energy_aemeasurable
    (n : ℕ) (R : ℝ) (f : ℝ → ℂ)
    (hfmeas : AEStronglyMeasurable f volume) :
    AEMeasurable (fun h : Fin (n + 1) → ℝ ↦
      ∫⁻ ξ : ℝ in aux_sobolevDifference_lowFrequency R,
        ‖𝓕 (iteratedMultiplicativeDifference (n + 1) h f) ξ‖ₑ ^ (2 : ℕ)) volume := by
  let E : (Fin (n + 1) → ℝ) → ℝ → ℝ≥0∞ :=
    fun h ξ ↦ ‖𝓕 (iteratedMultiplicativeDifference (n + 1) h f) ξ‖ₑ ^ (2 : ℕ)
  let F : (Fin n → ℝ) × (ℝ × ℝ) → ℝ≥0∞ :=
    fun q ↦ E (Fin.cons q.2.1 q.1) q.2.2
  have hFfull :=
    aux_sobolevDifference_iteratedDifference_next_fourier_joint_aemeasurable_energy
      n f hfmeas
  have hF : AEMeasurable F
      (volume.prod (volume.prod
        (volume.restrict (aux_sobolevDifference_lowFrequency R)))) := by
    apply hFfull.mono_measure
    exact Measure.prod_mono le_rfl
      (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hP := aux_sobolevDifference_measurePreserving_lowTailCoordinates n R
  have hpull : AEMeasurable (fun p : (Fin (n + 1) → ℝ) × ℝ ↦
      F (aux_sobolevDifference_lowTailCoordinates n p))
      (volume.prod (volume.restrict (aux_sobolevDifference_lowFrequency R))) := by
    exact hF.comp_quasiMeasurePreserving hP.quasiMeasurePreserving
  have heq : (fun p : (Fin (n + 1) → ℝ) × ℝ ↦
      F (aux_sobolevDifference_lowTailCoordinates n p)) =
      fun p : (Fin (n + 1) → ℝ) × ℝ ↦ E p.1 p.2 := by
    funext p
    simp only [F, E, aux_sobolevDifference_lowTailCoordinates]
    have hcons : Fin.cons (p.1 0) (fun i : Fin n ↦ p.1 i.succ) = p.1 := by
      funext i
      refine Fin.cases ?_ ?_ i
      · simp
      · intro j
        simp
    rw [hcons]
  rw [heq] at hpull
  exact hpull.lintegral_prod_right'

/-- Combines the raw high/low-frequency split with the integrated estimates at
an arbitrary positive frequency scale. -/
lemma aux_sobolevDifference_all_scale_bound
    (n : ℕ) (σ : ℝ) (hσ : 0 < σ)
    (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℂ)
    (hfmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hsupp : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f x = 0) :
    ∀ R : ℝ, 0 < R →
      (∫⁻ h : Fin (n + 1) → ℝ,
        aux_sobolevNormRaw σ (iteratedMultiplicativeDifference (n + 1) h f) ^ (2 : ℝ)) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (n + 1) *
          intervalLength (Set.Icc a b) ^ (n + 2)) *
          (ENNReal.ofReal R) ^ (-(2 * σ)) +
        ENNReal.ofReal (2 * intervalLength (Set.Icc a b) ^ 2) *
          ENNReal.ofReal R *
          uNorm (n + 2) f ^ ((2 : ℝ) ^ n) := by
  intro R hR
  let L : (Fin (n + 1) → ℝ) → ℝ≥0∞ := fun h ↦
    ∫⁻ ξ : ℝ in aux_sobolevDifference_lowFrequency R,
      ‖𝓕 (iteratedMultiplicativeDifference (n + 1) h f) ξ‖ₑ ^ (2 : ℝ)
  let H : (Fin (n + 1) → ℝ) → ℝ≥0∞ := fun h ↦
    ∫⁻ ξ : ℝ in aux_sobolevDifference_highFrequency R,
      ‖(japaneseBracket ξ ^ (-σ)) •
        (Lp.fourierTransformₗᵢ ℝ ℂ
          (aux_sobolevDifference_iteratedDifferenceLp (n + 1) h a b f
            hfmeas hbound hsupp)) ξ‖ₑ ^ (2 : ℝ)
  have hLmeas : AEMeasurable L volume := by
    simpa [L, aux_sobolevDifference_lowFrequency] using
      (aux_sobolevDifference_iterated_low_energy_aemeasurable n R f hfmeas)
  have hpoint : ∀ h : Fin (n + 1) → ℝ,
      aux_sobolevNormRaw σ (iteratedMultiplicativeDifference (n + 1) h f) ^ (2 : ℝ) ≤
        L h + H h := by
    intro h
    have hg1 := aux_sobolevDifference_iteratedDifference_memLp_Icc
      (n + 1) h a b f hfmeas hbound hsupp 1
    have hg2 := aux_sobolevDifference_iteratedDifference_memLp_Icc
      (n + 1) h a b f hfmeas hbound hsupp 2
    simpa [L, H, aux_sobolevDifference_lowFrequency,
      aux_sobolevDifference_iteratedDifferenceLp] using
      (aux_sobolevDifference_sobolevNormRaw_high_low_split_le σ R hσ.le
        (iteratedMultiplicativeDifference (n + 1) h f) hg1 hg2)
  have hsplit :
      (∫⁻ h : Fin (n + 1) → ℝ,
        aux_sobolevNormRaw σ (iteratedMultiplicativeDifference (n + 1) h f) ^ (2 : ℝ)) ≤
        (∫⁻ h : Fin (n + 1) → ℝ, L h) +
          ∫⁻ h : Fin (n + 1) → ℝ, H h := by
    calc
      (∫⁻ h : Fin (n + 1) → ℝ,
          aux_sobolevNormRaw σ (iteratedMultiplicativeDifference (n + 1) h f) ^ (2 : ℝ)) ≤
          ∫⁻ h : Fin (n + 1) → ℝ, L h + H h :=
        MeasureTheory.lintegral_mono hpoint
      _ = (∫⁻ h : Fin (n + 1) → ℝ, L h) +
            ∫⁻ h : Fin (n + 1) → ℝ, H h :=
        MeasureTheory.lintegral_add_left' hLmeas _
  have hlow := aux_sobolevDifference_iterated_lowFrequency_energy_le
    n a b R hab hR.le f hfmeas hbound hsupp
  have hhigh := aux_sobolevDifference_iterated_highFrequency_sobolev_energy_exact_le
    (n + 1) a b σ R hab hσ.le hR f hfmeas hbound hsupp
  have hlength : intervalLength (Set.Icc a b) = b - a := by
    simp [intervalLength, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  have hlow' : (∫⁻ h : Fin (n + 1) → ℝ, L h) ≤
      ENNReal.ofReal (2 * intervalLength (Set.Icc a b) ^ 2) * ENNReal.ofReal R *
        uNorm (n + 2) f ^ ((2 : ℝ) ^ n) := by
    simpa [L, aux_sobolevDifference_lowFrequency, hlength] using hlow
  have hhigh' : (∫⁻ h : Fin (n + 1) → ℝ, H h) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (n + 1) *
        intervalLength (Set.Icc a b) ^ (n + 2)) *
        (ENNReal.ofReal R) ^ (-(2 * σ)) := by
    calc
      (∫⁻ h : Fin (n + 1) → ℝ, H h) ≤
          ENNReal.ofReal ((2 : ℝ) ^ (n + 1) *
            intervalLength (Set.Icc a b) ^ ((n + 1) + 1)) *
            ENNReal.ofReal (R ^ (-(2 * σ))) := by
        simpa [H] using hhigh
      _ = ENNReal.ofReal ((2 : ℝ) ^ (n + 1) *
            intervalLength (Set.Icc a b) ^ (n + 2)) *
            (ENNReal.ofReal R) ^ (-(2 * σ)) := by
        rw [ENNReal.ofReal_rpow_of_pos hR]
  calc
    (∫⁻ h : Fin (n + 1) → ℝ,
        aux_sobolevNormRaw σ (iteratedMultiplicativeDifference (n + 1) h f) ^ (2 : ℝ)) ≤
        (∫⁻ h : Fin (n + 1) → ℝ, L h) +
          ∫⁻ h : Fin (n + 1) → ℝ, H h := hsplit
    _ ≤ (ENNReal.ofReal (2 * intervalLength (Set.Icc a b) ^ 2) * ENNReal.ofReal R *
          uNorm (n + 2) f ^ ((2 : ℝ) ^ n)) +
        (ENNReal.ofReal ((2 : ℝ) ^ (n + 1) *
          intervalLength (Set.Icc a b) ^ (n + 2)) *
          (ENNReal.ofReal R) ^ (-(2 * σ))) := add_le_add hlow' hhigh'
    _ = _ := by ac_rfl

/--
Let `s ≥ 1`, `σ > 0`, and let `A` be a positive-length compact interval. Define
\[
\gamma_{s,\sigma}:=\frac{2^s\sigma}{1+2\sigma},
\qquad
C_{\ref{thm:sobolev-difference},\,s,A}
:=2^{s+1}(1+|A|)^{s+1}.
\]
If `f` is $1$-bounded and supported in `A`, then
\[
\int_{\mathbb R^s}\|\Delta_{\mathbf h}f\|_{H^{-\sigma}}^2
\,d\mathbf h
\leq
C_{\ref{thm:sobolev-difference},\,s,A}
\|f\|_{u^{s+1}}^{\gamma_{s,\sigma}}.
\]
-/
theorem sobolevDifferenceEstimate
    (s : ℕ) (hs : 1 ≤ s) (σ : ℝ) (hσ : 0 < σ)
    (A : Set ℝ) (hA : ∃ a b : ℝ, a < b ∧ A = Set.Icc a b)
    (f : ℝ → ℂ) (hf_measurable : AEStronglyMeasurable f volume)
    (hf_one_bounded : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hf_support : ∀ᵐ x ∂volume, x ∉ A → f x = 0) :
    (∫⁻ h : Fin s → ℝ,
      aux_sobolevNormRaw σ (iteratedMultiplicativeDifference s h f) ^ (2 : ℝ)) ≤
        ENNReal.ofReal (C_sobolevDifferenceEstimate s A) *
          uNorm (s + 1) f ^ gammaSobolevDifference s σ := by
  rcases hA with ⟨a, b, hablt, rfl⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  have hab : a ≤ b := hablt.le
  have hm : 0 ≤ intervalLength (Set.Icc a b) := ENNReal.toReal_nonneg
  have hall := aux_sobolevDifference_all_scale_bound n σ hσ a b hab f
    hf_measurable hf_one_bounded hf_support
  have hfinal := aux_sobolevDifference_finalize_high_low
    (n + 1) (by omega) σ hσ
    (intervalLength (Set.Icc a b)) hm
    (∫⁻ h : Fin (n + 1) → ℝ,
      aux_sobolevNormRaw σ (iteratedMultiplicativeDifference (n + 1) h f) ^ (2 : ℝ))
    (uNorm (n + 2) f)
    hall
  simpa [C_sobolevDifferenceEstimate] using hfinal

/--
Let `A` be a positive-length compact interval. If `f` is $1$-bounded and
supported in `A`, then
\[
\int_\mathbb R\|\Delta_h f\|_{H^{-1/2}}^2\,dh
\leq
C_{\ref{thm:sobolev-difference},\,1,A}\|f\|_{u^2}^{1/2}.
\]
-/
theorem sobolevDifferenceEstimateS1
    (A : Set ℝ) (hA : ∃ a b : ℝ, a < b ∧ A = Set.Icc a b)
    (f : ℝ → ℂ) (hf_measurable : AEStronglyMeasurable f volume)
    (hf_one_bounded : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hf_support : ∀ᵐ x ∂volume, x ∉ A → f x = 0) :
    (∫⁻ h : ℝ,
      aux_sobolevNormRaw (1 / 2 : ℝ) (multiplicativeDifference h f) ^ (2 : ℝ)) ≤
        ENNReal.ofReal (C_sobolevDifferenceEstimate 1 A) *
          uNorm 2 f ^ (1 / 2 : ℝ) := by
  have hmain := sobolevDifferenceEstimate 1 (by norm_num) (1 / 2 : ℝ) (by norm_num)
    A hA f hf_measurable hf_one_bounded hf_support
  let e : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.piUnique _
  have he : MeasurePreserving e volume volume := volume_preserving_piUnique _
  calc
    (∫⁻ h : ℝ,
        aux_sobolevNormRaw (1 / 2 : ℝ) (multiplicativeDifference h f) ^ (2 : ℝ)) =
        ∫⁻ h : Fin 1 → ℝ,
          aux_sobolevNormRaw (1 / 2 : ℝ)
            (iteratedMultiplicativeDifference 1 h f) ^ (2 : ℝ) := by
      rw [he.lintegral_map_equiv
        (fun h : ℝ ↦
          aux_sobolevNormRaw (1 / 2 : ℝ) (multiplicativeDifference h f) ^ (2 : ℝ)) e]
      apply lintegral_congr
      intro h
      simp [e, iteratedMultiplicativeDifference]
    _ ≤ ENNReal.ofReal (C_sobolevDifferenceEstimate 1 A) *
          uNorm (1 + 1) f ^ gammaSobolevDifference 1 (1 / 2 : ℝ) := hmain
    _ = ENNReal.ofReal (C_sobolevDifferenceEstimate 1 A) *
          uNorm 2 f ^ (1 / 2 : ℝ) := by
      norm_num [gammaSobolevDifference]

end Auto
