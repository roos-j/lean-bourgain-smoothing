import BourgainSmoothing.Auto.LocalizationAndDyadicLInfinityDecay
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# The nondecaying endpoint and interpolation

Formalizations of the labeled estimates in the corresponding section of
`blueprint/blueprint.tex`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Real FourierTransform Topology

namespace Auto

/--
The quadratic averaging operator from \(\label{lem:quadratic-average}\):
\[
\mathcal A_\chi f(x)=\int_\mathbb R |f(x+t^2-t)|\chi(t)\,dt.
\]
-/
def quadraticAverage (χ : ℝ → ℝ) (f : ℝ → ℂ) : ℝ → ℝ :=
  fun x ↦ ∫ t : ℝ, ‖f (x + t ^ 2 - t)‖ * χ t

/-- The explicit constant in \(\label{lem:quadratic-average}\), used by
`quadraticAveragingOperator`:
\[
C_{\ref{lem:quadratic-average},\,\chi}
=2^2(1+R_\chi)^{1/3}.
\]
-/
noncomputable def C_quadraticAveragingOperator (χ : ℝ → ℝ) : ℝ :=
  (2 : ℝ) ^ 2 * (1 + supportRadius χ) ^ (1 / (3 : ℝ))

/-- The two-root density of the pushforward of `t ↦ t² - t`, after centering
the quadratic at `1 / 2`. -/
noncomputable def aux_quadraticDensity (χ : ℝ → ℝ) (u : ℝ) : ℝ :=
  if 0 < u then
    (χ (1 / 2 + Real.sqrt u) + χ (1 / 2 - Real.sqrt u)) / (2 * Real.sqrt u)
  else 0

/-- The quadratic density is nonnegative when the cutoff is nonnegative. -/
lemma aux_quadraticDensity_nonneg (χ : ℝ → ℝ)
    (hχ : ∀ t : ℝ, 0 ≤ χ t) :
    ∀ u : ℝ, 0 ≤ aux_quadraticDensity χ u := by
  intro u
  unfold aux_quadraticDensity
  split_ifs with hu
  · exact div_nonneg (add_nonneg (hχ _) (hχ _)) (by positivity)
  · simp

/-- Pointwise reciprocal-square-root majorant for the quadratic density. -/
lemma aux_quadraticDensity_le_root (χ : ℝ → ℝ)
    (hχone : ∀ t : ℝ, χ t ≤ 1) :
    ∀ u : ℝ, aux_quadraticDensity χ u ≤
      if 0 < u then (Real.sqrt u)⁻¹ else 0 := by
  intro u
  unfold aux_quadraticDensity
  split_ifs with hu
  · apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt u)).2
    calc
      χ (1 / 2 + Real.sqrt u) + χ (1 / 2 - Real.sqrt u) ≤ 1 + 1 :=
        add_le_add (hχone _) (hχone _)
      _ = 2 := by norm_num
      _ = (Real.sqrt u)⁻¹ * (2 * Real.sqrt u) := by field_simp
  · simp

/-- The density vanishes beyond the support-radius square envelope. -/
lemma aux_quadraticDensity_eq_zero_of_radius_lt
    (χ : ℝ → ℝ) (hχcompact : HasCompactSupport χ)
    {u : ℝ} (hu : (supportRadius χ + 1) ^ 2 < u) :
    aux_quadraticDensity χ u = 0 := by
  have hR : 1 ≤ supportRadius χ := aux_u3_one_le_supportRadius χ hχcompact
  have hu0 : 0 < u := lt_of_le_of_lt (sq_nonneg _) hu
  have hsqrt_sq : (Real.sqrt u) ^ 2 = u := Real.sq_sqrt hu0.le
  have hsqrt_nonneg : 0 ≤ Real.sqrt u := Real.sqrt_nonneg _
  have hsqrt_gt : supportRadius χ + 1 < Real.sqrt u := by nlinarith
  have hsupport := aux_quadratic_support_subset_Ioc_radius χ hχcompact
  have hplus : χ (1 / 2 + Real.sqrt u) = 0 := by
    by_contra hne
    have hmem := hsupport hne
    have : supportRadius χ < 1 / 2 + Real.sqrt u := by linarith
    exact (not_lt_of_ge hmem.2) this
  have hminus : χ (1 / 2 - Real.sqrt u) = 0 := by
    by_contra hne
    have hmem := hsupport hne
    have : 1 / 2 - Real.sqrt u < -supportRadius χ := by linarith
    exact (not_lt_of_ge hmem.1.le) this
  unfold aux_quadraticDensity
  rw [ite_eq_left hu0, hplus, hminus]
  norm_num

/-- Compact reciprocal-square-root envelope for the quadratic density. -/
noncomputable def aux_quadraticEnvelope (R u : ℝ) : ℝ :=
  if u ∈ Set.Ioc (0 : ℝ) ((R + 1) ^ 2) then (Real.sqrt u)⁻¹ else 0

/-- The compact reciprocal-square-root envelope is nonnegative. -/
lemma aux_quadraticEnvelope_nonneg (R : ℝ) :
    ∀ u : ℝ, 0 ≤ aux_quadraticEnvelope R u := by
  intro u
  unfold aux_quadraticEnvelope
  split_ifs with hu
  · exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  · simp

/-- The compact reciprocal-square-root envelope dominates the density. -/
lemma aux_quadraticDensity_le_envelope
    (χ : ℝ → ℝ) (hχcompact : HasCompactSupport χ)
    (hχone : ∀ t : ℝ, χ t ≤ 1) :
    ∀ u : ℝ, aux_quadraticDensity χ u ≤
      aux_quadraticEnvelope (supportRadius χ) u := by
  intro u
  by_cases hu0 : 0 < u
  · by_cases huL : u ≤ (supportRadius χ + 1) ^ 2
    · have hmem : u ∈ Set.Ioc (0 : ℝ) ((supportRadius χ + 1) ^ 2) := ⟨hu0, huL⟩
      rw [aux_quadraticEnvelope, ite_eq_left hmem]
      simpa [hu0] using aux_quadraticDensity_le_root χ hχone u
    · have hlt : (supportRadius χ + 1) ^ 2 < u := lt_of_not_ge huL
      have hzero := aux_quadraticDensity_eq_zero_of_radius_lt χ hχcompact hlt
      have hnotmem : u ∉ Set.Ioc (0 : ℝ) ((supportRadius χ + 1) ^ 2) := by
        intro h
        exact (not_le_of_gt hlt) h.2
      rw [aux_quadraticEnvelope, ite_eq_right hnotmem, hzero]
  · have hnotmem : u ∉ Set.Ioc (0 : ℝ) ((supportRadius χ + 1) ^ 2) := by
      intro h
      exact hu0 (lt_of_lt_of_le h.1 (le_refl _))
    rw [aux_quadraticEnvelope, ite_eq_right hnotmem]
    unfold aux_quadraticDensity
    rw [ite_eq_right hu0]

/-- Indicator representation of the compact reciprocal-square-root envelope. -/
lemma aux_quadraticEnvelope_eq_indicator (R : ℝ) :
    aux_quadraticEnvelope R =
      (Set.Ioc (0 : ℝ) ((R + 1) ^ 2)).indicator
        (fun u : ℝ ↦ (Real.sqrt u)⁻¹) := by
  funext u
  by_cases hu : u ∈ Set.Ioc (0 : ℝ) ((R + 1) ^ 2)
  · rw [aux_quadraticEnvelope, ite_eq_left hu, Set.indicator_of_mem hu]
  · rw [aux_quadraticEnvelope, ite_eq_right hu, Set.indicator_of_notMem hu]

/-- Measurability of the compact reciprocal-square-root envelope. -/
lemma aux_quadraticEnvelope_aestronglyMeasurable (R : ℝ) :
    AEStronglyMeasurable (aux_quadraticEnvelope R) volume := by
  rw [aux_quadraticEnvelope_eq_indicator]
  apply AEStronglyMeasurable.indicator
  · exact (measurable_inv.comp Real.continuous_sqrt.measurable).aestronglyMeasurable
  · exact measurableSet_Ioc

/-- The envelope belongs to `L^(3/2)`. -/
lemma aux_quadraticEnvelope_memLp_threeHalves (R : ℝ) :
    MemLp (aux_quadraticEnvelope R) (3 / 2 : ℝ≥0∞) volume := by
  have hL : 0 ≤ (R + 1) ^ 2 := sq_nonneg _
  have hpow : IntegrableOn (fun u : ℝ ↦ u ^ (-(3 : ℝ) / 4))
      (Set.Ioc (0 : ℝ) ((R + 1) ^ 2)) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hL]
    exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  rw [← integrable_norm_rpow_iff
    (aux_quadraticEnvelope_aestronglyMeasurable R) (by norm_num)
    (by finiteness : (3 / 2 : ℝ≥0∞) ≠ ∞)]
  rw [aux_quadraticEnvelope_eq_indicator]
  rw [show (fun u : ℝ ↦
      ‖(Set.Ioc (0 : ℝ) ((R + 1) ^ 2)).indicator
        (fun u : ℝ ↦ (Real.sqrt u)⁻¹) u‖ ^
        ((3 / 2 : ℝ≥0∞).toReal)) =
      (Set.Ioc (0 : ℝ) ((R + 1) ^ 2)).indicator
        (fun u : ℝ ↦ u ^ (-(3 : ℝ) / 4)) by
      funext u
      by_cases hu : u ∈ Set.Ioc (0 : ℝ) ((R + 1) ^ 2)
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
        rw [Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
        norm_num
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hu.1.le]
        rw [← Real.rpow_mul hu.1.le]
        norm_num
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
        norm_num]
  exact (integrable_indicator_iff measurableSet_Ioc).2 hpow

/-- The envelope belongs to `L¹`. -/
lemma aux_quadraticEnvelope_memLp_one (R : ℝ) :
    MemLp (aux_quadraticEnvelope R) (1 : ℝ≥0∞) volume := by
  have hL : 0 ≤ (R + 1) ^ 2 := sq_nonneg _
  have hpow : IntegrableOn (fun u : ℝ ↦ u ^ (-(1 : ℝ) / 2))
      (Set.Ioc (0 : ℝ) ((R + 1) ^ 2)) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hL]
    exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  rw [← integrable_norm_rpow_iff
    (aux_quadraticEnvelope_aestronglyMeasurable R) (by norm_num)
    (by finiteness : (1 : ℝ≥0∞) ≠ ∞)]
  rw [aux_quadraticEnvelope_eq_indicator]
  rw [show (fun u : ℝ ↦
      ‖(Set.Ioc (0 : ℝ) ((R + 1) ^ 2)).indicator
        (fun u : ℝ ↦ (Real.sqrt u)⁻¹) u‖ ^
        ((1 : ℝ≥0∞).toReal)) =
      (Set.Ioc (0 : ℝ) ((R + 1) ^ 2)).indicator
        (fun u : ℝ ↦ u ^ (-(1 : ℝ) / 2)) by
      funext u
      by_cases hu : u ∈ Set.Ioc (0 : ℝ) ((R + 1) ^ 2)
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
        rw [Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
        norm_num
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hu.1.le]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
        norm_num]
  exact (integrable_indicator_iff measurableSet_Ioc).2 hpow

/-- Measurability of the two-root density. -/
lemma aux_quadraticDensity_aestronglyMeasurable (χ : ℝ → ℝ)
    (hχ_smooth : ContDiff ℝ ⊤ χ) :
    AEStronglyMeasurable (aux_quadraticDensity χ) volume := by
  have hχ : Measurable χ := hχ_smooth.continuous.measurable
  have hsqrt : Measurable (fun u : ℝ ↦ Real.sqrt u) := measurable_id.sqrt
  have hplus : Measurable (fun u : ℝ ↦ χ (1 / 2 + Real.sqrt u)) :=
    hχ.comp (measurable_const.add hsqrt)
  have hminus : Measurable (fun u : ℝ ↦ χ (1 / 2 - Real.sqrt u)) :=
    hχ.comp (measurable_const.sub hsqrt)
  have hnum : Measurable (fun u : ℝ ↦
      χ (1 / 2 + Real.sqrt u) + χ (1 / 2 - Real.sqrt u)) := hplus.add hminus
  have hden : Measurable (fun u : ℝ ↦ 2 * Real.sqrt u) :=
    measurable_const.mul hsqrt
  unfold aux_quadraticDensity
  exact (Measurable.ite measurableSet_Ioi (hnum.div hden) measurable_const).aestronglyMeasurable

/-- Measurability of the ENNReal-valued quadratic density used in the
nonnegative coarea formula. -/
lemma aux_quadraticDensity_measurable_ennreal
    (χ : ℝ → ℝ) (hχ_smooth : ContDiff ℝ ⊤ χ) :
    Measurable (fun u : ℝ ↦ ENNReal.ofReal (aux_quadraticDensity χ u)) := by
  apply ENNReal.continuous_ofReal.measurable.comp
  have hχ : Measurable χ := hχ_smooth.continuous.measurable
  have hsqrt : Measurable (fun u : ℝ ↦ Real.sqrt u) := measurable_id.sqrt
  have hplus : Measurable (fun u : ℝ ↦ χ (1 / 2 + Real.sqrt u)) :=
    hχ.comp (measurable_const.add hsqrt)
  have hminus : Measurable (fun u : ℝ ↦ χ (1 / 2 - Real.sqrt u)) :=
    hχ.comp (measurable_const.sub hsqrt)
  have hnum : Measurable (fun u : ℝ ↦
      χ (1 / 2 + Real.sqrt u) + χ (1 / 2 - Real.sqrt u)) := hplus.add hminus
  have hden : Measurable (fun u : ℝ ↦ 2 * Real.sqrt u) :=
    measurable_const.mul hsqrt
  unfold aux_quadraticDensity
  exact Measurable.ite measurableSet_Ioi (hnum.div hden) measurable_const

/-- The two-root density belongs to `L^(3/2)`. -/
lemma aux_quadraticDensity_memLp_threeHalves
    (χ : ℝ → ℝ) (hχ_smooth : ContDiff ℝ ⊤ χ)
    (hχcompact : HasCompactSupport χ) (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t)
    (hχ_le_one : ∀ t : ℝ, χ t ≤ 1) :
    MemLp (aux_quadraticDensity χ) (3 / 2 : ℝ≥0∞) volume := by
  refine (aux_quadraticEnvelope_memLp_threeHalves (supportRadius χ)).mono
    (aux_quadraticDensity_aestronglyMeasurable χ hχ_smooth) ?_
  filter_upwards with u
  rw [Real.norm_of_nonneg (aux_quadraticDensity_nonneg χ hχ_nonneg u),
    Real.norm_of_nonneg (aux_quadraticEnvelope_nonneg (supportRadius χ) u)]
  exact aux_quadraticDensity_le_envelope χ hχcompact hχ_le_one u

/-- The two-root density belongs to `L¹`. -/
lemma aux_quadraticDensity_memLp_one
    (χ : ℝ → ℝ) (hχ_smooth : ContDiff ℝ ⊤ χ)
    (hχcompact : HasCompactSupport χ) (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t)
    (hχ_le_one : ∀ t : ℝ, χ t ≤ 1) :
    MemLp (aux_quadraticDensity χ) (1 : ℝ≥0∞) volume := by
  refine (aux_quadraticEnvelope_memLp_one (supportRadius χ)).mono
    (aux_quadraticDensity_aestronglyMeasurable χ hχ_smooth) ?_
  filter_upwards with u
  rw [Real.norm_of_nonneg (aux_quadraticDensity_nonneg χ hχ_nonneg u),
    Real.norm_of_nonneg (aux_quadraticEnvelope_nonneg (supportRadius χ) u)]
  exact aux_quadraticDensity_le_envelope χ hχcompact hχ_le_one u

/-- Exact integral of the `-3/4` power on a positive finite interval. -/
lemma aux_integral_Ioc_rpow_neg_three_four (L : ℝ) (hL : 0 ≤ L) :
    (∫ u in Set.Ioc (0 : ℝ) L, u ^ (-(3 : ℝ) / 4)) =
      4 * L ^ ((1 : ℝ) / 4) := by
  rw [← intervalIntegral.integral_of_le hL]
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(3 : ℝ) / 4))]
  norm_num
  ring

/-- Exact `3/2`-power integral of the reciprocal-square-root envelope. -/
lemma aux_quadraticEnvelope_integral_norm_rpow_threeHalves (R : ℝ) :
    (∫ u : ℝ, ‖aux_quadraticEnvelope R u‖ ^ (3 / 2 : ℝ)) =
      4 * ((R + 1) ^ 2) ^ ((1 : ℝ) / 4) := by
  rw [aux_quadraticEnvelope_eq_indicator]
  rw [show (fun u : ℝ ↦
      ‖(Set.Ioc (0 : ℝ) ((R + 1) ^ 2)).indicator
        (fun u : ℝ ↦ (Real.sqrt u)⁻¹) u‖ ^ (3 / 2 : ℝ)) =
      (Set.Ioc (0 : ℝ) ((R + 1) ^ 2)).indicator
        (fun u : ℝ ↦ u ^ (-(3 : ℝ) / 4)) by
      funext u
      by_cases hu : u ∈ Set.Ioc (0 : ℝ) ((R + 1) ^ 2)
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
        rw [Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hu.1.le]
        rw [← Real.rpow_mul hu.1.le]
        norm_num
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
        norm_num]
  rw [integral_indicator measurableSet_Ioc]
  exact aux_integral_Ioc_rpow_neg_three_four _ (sq_nonneg _)

/-- Exact `L^(3/2)` norm of the reciprocal-square-root envelope. -/
lemma aux_quadraticEnvelope_eLpNorm_threeHalves_toReal (R : ℝ) :
    (eLpNorm (aux_quadraticEnvelope R) (3 / 2 : ℝ≥0∞) volume).toReal =
      (4 * ((R + 1) ^ 2) ^ ((1 : ℝ) / 4)) ^ ((2 : ℝ) / 3) := by
  have hmem := aux_quadraticEnvelope_memLp_threeHalves R
  have hnonneg : 0 ≤
      (∫ u : ℝ, ‖aux_quadraticEnvelope R u‖ ^
        ((3 / 2 : ℝ≥0∞).toReal)) ^ ((3 / 2 : ℝ≥0∞).toReal)⁻¹ := by
    positivity
  have h := congrArg ENNReal.toReal
    (hmem.eLpNorm_eq_integral_rpow_norm (by norm_num)
      (by finiteness : (3 / 2 : ℝ≥0∞) ≠ ∞))
  rw [ENNReal.toReal_ofReal hnonneg] at h
  norm_num at h
  have hI : (∫ u : ℝ, |aux_quadraticEnvelope R u| ^ (3 / 2 : ℝ)) =
      4 * ((R + 1) ^ 2) ^ ((1 : ℝ) / 4) := by
    simpa only [Real.norm_eq_abs] using
      aux_quadraticEnvelope_integral_norm_rpow_threeHalves R
  rw [hI] at h
  exact h

/-- Scalar simplification of the envelope norm using the support-radius scale. -/
lemma aux_scalar_quadraticEnvelope_bound (R : ℝ) (hR : 0 ≤ R) :
    (4 * ((R + 1) ^ 2) ^ ((1 : ℝ) / 4)) ^ ((2 : ℝ) / 3) ≤
      4 * (1 + R) ^ ((1 : ℝ) / 3) := by
  have hbase : 0 ≤ R + 1 := by linarith
  have hpow : ((R + 1) ^ 2) ^ ((1 : ℝ) / 4) =
      (R + 1) ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hbase]
    norm_num
  rw [hpow, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hbase _)]
  have hfour : (4 : ℝ) ^ ((2 : ℝ) / 3) ≤ 4 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      (by norm_num : (2 : ℝ) / 3 ≤ 1)
  have hright : 0 ≤ (R + 1) ^ ((1 : ℝ) / 3) :=
    Real.rpow_nonneg hbase _
  have hhalf : ((R + 1) ^ ((1 : ℝ) / 2)) ^ ((2 : ℝ) / 3) =
      (R + 1) ^ ((1 : ℝ) / 3) := by
    rw [← Real.rpow_mul hbase]
    norm_num
  rw [hhalf]
  calc
    4 ^ ((2 : ℝ) / 3) * (R + 1) ^ ((1 : ℝ) / 3) ≤
        4 * (R + 1) ^ ((1 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_right hfour hright
    _ = 4 * (1 + R) ^ ((1 : ℝ) / 3) := by ring_nf

/-- The `L^(3/2)` density norm obeys the advertised support-radius bound. -/
lemma aux_quadraticDensity_eLpNorm_threeHalves_toReal_le
    (χ : ℝ → ℝ) (hχcompact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1) :
    (eLpNorm (aux_quadraticDensity χ) (3 / 2 : ℝ≥0∞) volume).toReal ≤
      4 * (1 + supportRadius χ) ^ ((1 : ℝ) / 3) := by
  have henv := aux_quadraticEnvelope_memLp_threeHalves (supportRadius χ)
  have hmono : eLpNorm (aux_quadraticDensity χ) (3 / 2 : ℝ≥0∞) volume ≤
      eLpNorm (aux_quadraticEnvelope (supportRadius χ))
        (3 / 2 : ℝ≥0∞) volume := by
    apply eLpNorm_mono_ae
    filter_upwards with u
    rw [Real.norm_of_nonneg (aux_quadraticDensity_nonneg χ hχ_nonneg u),
      Real.norm_of_nonneg (aux_quadraticEnvelope_nonneg (supportRadius χ) u)]
    exact aux_quadraticDensity_le_envelope χ hχcompact hχ_le_one u
  calc
    (eLpNorm (aux_quadraticDensity χ) (3 / 2 : ℝ≥0∞) volume).toReal ≤
        (eLpNorm (aux_quadraticEnvelope (supportRadius χ))
          (3 / 2 : ℝ≥0∞) volume).toReal :=
      ENNReal.toReal_mono henv.eLpNorm_ne_top hmono
    _ = (4 * ((supportRadius χ + 1) ^ 2) ^ ((1 : ℝ) / 4)) ^ ((2 : ℝ) / 3) :=
      aux_quadraticEnvelope_eLpNorm_threeHalves_toReal (supportRadius χ)
    _ ≤ 4 * (1 + supportRadius χ) ^ ((1 : ℝ) / 3) :=
      aux_scalar_quadraticEnvelope_bound _
        (zero_le_one.trans (aux_u3_one_le_supportRadius χ hχcompact))

/-- The reflected and translated density matching the convolution shift. -/
noncomputable def aux_quadraticKernel (χ : ℝ → ℝ) (s : ℝ) : ℝ :=
  aux_quadraticDensity χ (1 / 4 - s)

/-- Nonnegativity of the reflected quadratic kernel. -/
lemma aux_quadraticKernel_nonneg (χ : ℝ → ℝ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) :
    ∀ s : ℝ, 0 ≤ aux_quadraticKernel χ s := by
  intro s
  exact aux_quadraticDensity_nonneg χ hχ_nonneg _

/-- Reflection and translation preserve density `Lᵖ` membership. -/
lemma aux_quadraticKernel_memLp
    (χ : ℝ → ℝ) (p : ℝ≥0∞)
    (hD : MemLp (aux_quadraticDensity χ) p volume) :
    MemLp (aux_quadraticKernel χ) p volume := by
  have hmp : MeasurePreserving (fun s : ℝ ↦ 1 / 4 - s) volume volume :=
    volume.measurePreserving_sub_left _
  change MemLp (aux_quadraticDensity χ ∘ fun s : ℝ ↦ 1 / 4 - s) p volume
  exact hD.comp_measurePreserving hmp

/-- Reflection and translation preserve the density `Lᵖ` seminorm. -/
lemma aux_quadraticKernel_eLpNorm (χ : ℝ → ℝ) (p : ℝ≥0∞)
    (hD : MemLp (aux_quadraticDensity χ) p volume) :
    eLpNorm (aux_quadraticKernel χ) p volume =
      eLpNorm (aux_quadraticDensity χ) p volume := by
  have hmp : MeasurePreserving (fun s : ℝ ↦ 1 / 4 - s) volume volume :=
    volume.measurePreserving_sub_left _
  change eLpNorm (aux_quadraticDensity χ ∘ fun s : ℝ ↦ 1 / 4 - s) p volume = _
  exact eLpNorm_comp_measurePreserving hD.aestronglyMeasurable hmp

/-- Splitting a nonnegative integral about a center into its two positive branches. -/
lemma aux_lintegral_center_split (B : ℝ → ℝ≥0∞) (hB : Measurable B) (c : ℝ) :
    (∫⁻ t : ℝ, B t) =
      ∫⁻ s : ℝ in Ioi (0 : ℝ), B (c + s) + B (c - s) := by
  let F : ℝ → ℝ≥0∞ := fun s ↦ B (c + s)
  have hF : Measurable F := hB.comp (measurable_const.add measurable_id)
  have htrans : (∫⁻ s : ℝ, F s) = ∫⁻ t : ℝ, B t := by
    simpa [F] using
      (measurePreserving_add_left (volume : Measure ℝ) c).lintegral_comp hB
  have hneg : (∫⁻ s : ℝ in Ici (0 : ℝ), F (-s)) =
      ∫⁻ t : ℝ in Iic (0 : ℝ), F t := by
    have hpre : (fun s : ℝ ↦ -s) ⁻¹' Iic (0 : ℝ) = Ici 0 := by
      ext s
      change (-s ≤ 0) ↔ 0 ≤ s
      constructor <;> intro hs <;> linarith
    have hraw :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage
        (s := Iic (0 : ℝ)) measurableSet_Iic hF
    rw [hpre] at hraw
    exact hraw
  have hneg' : (∫⁻ s : ℝ in Ioi (0 : ℝ), F (-s)) =
      ∫⁻ t : ℝ in Iic (0 : ℝ), F t := by
    rw [← hneg]
    exact setLIntegral_congr (Ioi_ae_eq_Ici : Ioi (0 : ℝ) =ᵐ[volume] Ici 0)
  calc
    (∫⁻ t : ℝ, B t) = ∫⁻ s : ℝ, F s := htrans.symm
    _ = (∫⁻ s : ℝ in Ioi (0 : ℝ), F s) +
        ∫⁻ s : ℝ in Iic (0 : ℝ), F s :=
      by simpa only [compl_Ioi] using (lintegral_add_compl F measurableSet_Ioi).symm
    _ = (∫⁻ s : ℝ in Ioi (0 : ℝ), F s) +
        ∫⁻ s : ℝ in Ioi (0 : ℝ), F (-s) := by rw [hneg']
    _ = ∫⁻ s : ℝ in Ioi (0 : ℝ), F s + F (-s) := by
      rw [← lintegral_add_left (μ := volume.restrict (Ioi (0 : ℝ))) hF]
    _ = ∫⁻ s : ℝ in Ioi (0 : ℝ), B (c + s) + B (c - s) := by
      simp [F, sub_eq_add_neg]

/-- Positive-half-line square change of variables in `lintegral` form. -/
lemma aux_lintegral_comp_sq_Ioi (U : ℝ → ℝ≥0∞) :
    (∫⁻ u in Set.Ioi (0 : ℝ), U u) =
      ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (2 * s) * U (s ^ 2) := by
  have himage : (fun s : ℝ ↦ s ^ 2) '' Set.Ioi (0 : ℝ) = Set.Ioi (0 : ℝ) := by
    ext u
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact sq_pos_of_pos (mem_Ioi.mp hs)
    · intro hu
      refine ⟨Real.sqrt u, Real.sqrt_pos.2 hu, ?_⟩
      exact Real.sq_sqrt hu.le
  have hderiv : ∀ s ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun s : ℝ ↦ s ^ 2) (2 * s) (Set.Ioi (0 : ℝ)) s := by
    intro s _
    simpa using (hasDerivAt_pow 2 s).hasDerivWithinAt
  have hmono : MonotoneOn (fun s : ℝ ↦ s ^ 2) (Set.Ioi (0 : ℝ)) := by
    intro s hs t _ hst
    exact pow_le_pow_left₀ (le_of_lt hs) hst 2
  have h := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn measurableSet_Ioi
    hderiv hmono U
  rw [himage] at h
  exact h

/-- The square change of variables realizes the two-root density. -/
lemma aux_lintegral_quadraticDensity_square (χ A : ℝ → ℝ) :
    (∫⁻ u in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (A (u - 1 / 4) * aux_quadraticDensity χ u)) =
      ∫⁻ s in Set.Ioi (0 : ℝ),
        ENNReal.ofReal
          (A (s ^ 2 - 1 / 4) * χ (1 / 2 + s) +
            A (s ^ 2 - 1 / 4) * χ (1 / 2 - s)) := by
  rw [aux_lintegral_comp_sq_Ioi]
  refine setLIntegral_congr_fun measurableSet_Ioi ?_
  intro s hs
  have hs0 : 0 < s := mem_Ioi.mp hs
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs0
  unfold aux_quadraticDensity
  dsimp
  rw [ite_eq_left hs2, Real.sqrt_sq_eq_abs, abs_of_pos hs0]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * s)]
  congr 1
  field_simp

/-- Global nonnegative pushforward of `t ↦ t² - t` through the explicit
two-root density. -/
lemma aux_lintegral_quadratic_pushforward
    (χ A : ℝ → ℝ) (hA : ∀ u : ℝ, 0 ≤ A u) (hχ : ∀ t : ℝ, 0 ≤ χ t)
    (hB : Measurable (fun t : ℝ ↦ ENNReal.ofReal (A (t ^ 2 - t) * χ t))) :
    (∫⁻ t : ℝ, ENNReal.ofReal (A (t ^ 2 - t) * χ t)) =
      ∫⁻ u : ℝ, ENNReal.ofReal (A (u - 1 / 4) * aux_quadraticDensity χ u) := by
  let B : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (A (t ^ 2 - t) * χ t)
  have hsplit := aux_lintegral_center_split B hB (1 / 2)
  have hbranches :
      (∫⁻ s : ℝ in Ioi (0 : ℝ), B (1 / 2 + s) + B (1 / 2 - s)) =
        ∫⁻ s : ℝ in Ioi (0 : ℝ),
          ENNReal.ofReal
            (A (s ^ 2 - 1 / 4) * χ (1 / 2 + s) +
              A (s ^ 2 - 1 / 4) * χ (1 / 2 - s)) := by
    refine setLIntegral_congr_fun measurableSet_Ioi ?_
    intro s hs
    have hplus : (1 / 2 + s) ^ 2 - (1 / 2 + s) = s ^ 2 - 1 / 4 := by ring
    have hminus : (1 / 2 - s) ^ 2 - (1 / 2 - s) = s ^ 2 - 1 / 4 := by ring
    change B (1 / 2 + s) + B (1 / 2 - s) = _
    simp only [B, hplus, hminus]
    rw [← ENNReal.ofReal_add]
    · exact mul_nonneg (hA _) (hχ _)
    · exact mul_nonneg (hA _) (hχ _)
  let P : ℝ → ℝ≥0∞ :=
    fun u ↦ ENNReal.ofReal (A (u - 1 / 4) * aux_quadraticDensity χ u)
  have hzero : (∫⁻ u : ℝ in Iic (0 : ℝ), P u) = 0 := by
    calc
      (∫⁻ u : ℝ in Iic (0 : ℝ), P u) = ∫⁻ u : ℝ in Iic (0 : ℝ), 0 := by
        refine setLIntegral_congr_fun measurableSet_Iic ?_
        intro u hu
        have hu : ¬ 0 < u := not_lt.mpr (mem_Iic.mp hu)
        simp [P, aux_quadraticDensity, hu]
      _ = 0 := by simp
  have hglobal : (∫⁻ u : ℝ, P u) = ∫⁻ u : ℝ in Ioi (0 : ℝ), P u := by
    calc
      (∫⁻ u : ℝ, P u) =
          (∫⁻ u : ℝ in Ioi (0 : ℝ), P u) + ∫⁻ u : ℝ in Iic (0 : ℝ), P u := by
        simpa only [compl_Ioi] using
          (lintegral_add_compl (μ := volume) P measurableSet_Ioi).symm
      _ = ∫⁻ u : ℝ in Ioi (0 : ℝ), P u := by rw [hzero, add_zero]
  calc
    (∫⁻ t : ℝ, ENNReal.ofReal (A (t ^ 2 - t) * χ t)) =
        ∫⁻ s : ℝ in Ioi (0 : ℝ), B (1 / 2 + s) + B (1 / 2 - s) := by
      simpa [B] using hsplit
    _ = ∫⁻ s : ℝ in Ioi (0 : ℝ),
        ENNReal.ofReal
          (A (s ^ 2 - 1 / 4) * χ (1 / 2 + s) +
            A (s ^ 2 - 1 / 4) * χ (1 / 2 - s)) := hbranches
    _ = ∫⁻ u : ℝ in Ioi (0 : ℝ), P u := by
      simpa [P] using (aux_lintegral_quadraticDensity_square χ A).symm
    _ = ∫⁻ u : ℝ, P u := hglobal.symm
    _ = ∫⁻ u : ℝ, ENNReal.ofReal (A (u - 1 / 4) * aux_quadraticDensity χ u) := rfl

/-- Reflection about `1 / 8` puts the two-root density into the raw
convolution orientation. -/
lemma aux_lintegral_reflect_translate (D F : ℝ → ℝ≥0∞)
    (hD : Measurable D) (hF : Measurable F) (x : ℝ) :
    (∫⁻ u : ℝ, D u * F (x + u - 1 / 4)) =
      ∫⁻ y : ℝ, D (1 / 4 - y) * F (x - y) := by
  let Q : ℝ → ℝ≥0∞ := fun y ↦ D (1 / 4 - y) * F (x - y)
  have hQ : Measurable Q :=
    (hD.comp (measurable_const.sub measurable_id)).mul
      (hF.comp (measurable_const.sub measurable_id))
  have htrans :=
    ((volume : Measure ℝ).measurePreserving_sub_left (1 / 4)).lintegral_comp hQ
  calc
    (∫⁻ u : ℝ, D u * F (x + u - 1 / 4)) = ∫⁻ u : ℝ, Q (1 / 4 - u) := by
      apply lintegral_congr
      intro u
      dsimp [Q]
      congr 2 <;> ring
    _ = ∫⁻ y : ℝ, D (1 / 4 - y) * F (x - y) := by
      simpa [Q] using htrans

/-- The quadratic pushforward identity in the reflected convolution
orientation. -/
lemma aux_lintegral_quadratic_to_convolution
    (χ : ℝ → ℝ) (hχ : ∀ t : ℝ, 0 ≤ χ t)
    (f : ℝ → ℂ) (hF : Measurable (fun y : ℝ ↦ ‖f y‖ₑ))
    (hD : Measurable (fun u : ℝ ↦ ENNReal.ofReal (aux_quadraticDensity χ u)))
    (x : ℝ)
    (hB : Measurable (fun t : ℝ ↦
      ENNReal.ofReal (‖f (x + (t ^ 2 - t))‖ * χ t))) :
    (∫⁻ t : ℝ, ENNReal.ofReal (‖f (x + (t ^ 2 - t))‖ * χ t)) =
      ∫⁻ y : ℝ, ENNReal.ofReal (aux_quadraticDensity χ (1 / 4 - y)) * ‖f (x - y)‖ₑ := by
  let A : ℝ → ℝ := fun u ↦ ‖f (x + u)‖
  have hA : ∀ u : ℝ, 0 ≤ A u := fun u ↦ norm_nonneg _
  have hpush := aux_lintegral_quadratic_pushforward χ A hA hχ (by
    simpa [A] using hB)
  have hdensity :
      (∫⁻ u : ℝ, ENNReal.ofReal (A (u - 1 / 4) * aux_quadraticDensity χ u)) =
        ∫⁻ u : ℝ, ENNReal.ofReal (aux_quadraticDensity χ u) * ‖f (x + u - 1 / 4)‖ₑ := by
    apply lintegral_congr
    intro u
    rw [ENNReal.ofReal_mul (hA _), ofReal_norm]
    rw [mul_comm]
    congr 1
    congr 1
    ring_nf
  calc
    (∫⁻ t : ℝ, ENNReal.ofReal (‖f (x + (t ^ 2 - t))‖ * χ t)) =
        ∫⁻ u : ℝ, ENNReal.ofReal (A (u - 1 / 4) * aux_quadraticDensity χ u) := by
      simpa [A] using hpush
    _ = ∫⁻ u : ℝ, ENNReal.ofReal (aux_quadraticDensity χ u) * ‖f (x + u - 1 / 4)‖ₑ :=
      hdensity
    _ = ∫⁻ y : ℝ, ENNReal.ofReal (aux_quadraticDensity χ (1 / 4 - y)) * ‖f (x - y)‖ₑ :=
      aux_lintegral_reflect_translate _ _ hD hF x

/-- The Bochner-defined quadratic average is pointwise dominated by the
nonnegative reflected density convolution. -/
lemma aux_enorm_quadraticAverage_le_densityConvolution
    (χ : ℝ → ℝ) (hχ : ∀ t : ℝ, 0 ≤ χ t)
    (f : ℝ → ℂ) (hF : Measurable (fun y : ℝ ↦ ‖f y‖ₑ))
    (hD : Measurable (fun u : ℝ ↦ ENNReal.ofReal (aux_quadraticDensity χ u)))
    (x : ℝ)
    (hB : Measurable (fun t : ℝ ↦
      ENNReal.ofReal (‖f (x + (t ^ 2 - t))‖ * χ t))) :
    ‖quadraticAverage χ f x‖ₑ ≤
      ∫⁻ y : ℝ, ENNReal.ofReal (aux_quadraticDensity χ (1 / 4 - y)) * ‖f (x - y)‖ₑ := by
  have hbridge := aux_lintegral_quadratic_to_convolution χ hχ f hF hD x hB
  calc
    ‖quadraticAverage χ f x‖ₑ =
        ‖∫ t : ℝ, ‖f (x + t ^ 2 - t)‖ * χ t‖ₑ := rfl
    _ ≤ ∫⁻ t : ℝ, ‖‖f (x + t ^ 2 - t)‖ * χ t‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ t : ℝ, ENNReal.ofReal (‖f (x + t ^ 2 - t)‖ * χ t) := by
      apply lintegral_congr
      intro t
      rw [← ofReal_norm, Real.norm_of_nonneg]
      exact mul_nonneg (norm_nonneg _) (hχ _)
    _ = ∫⁻ t : ℝ, ENNReal.ofReal (‖f (x + (t ^ 2 - t))‖ * χ t) := by
      apply lintegral_congr
      intro t
      congr 2
      congr 2
      ring
    _ = ∫⁻ y : ℝ, ENNReal.ofReal (aux_quadraticDensity χ (1 / 4 - y)) * ‖f (x - y)‖ₑ :=
      hbridge

/-- The quadratic spatial translation is quasi-measure-preserving on the
product space. -/
lemma aux_quadratic_shift_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (fun z : ℝ × ℝ ↦ z.1 + z.2 ^ 2 - z.2)
      (volume.prod volume) volume := by
  refine QuasiMeasurePreserving.prod_of_left (by fun_prop)
    (Filter.Eventually.of_forall fun t ↦ ?_)
  convert (measurePreserving_add_right volume (t ^ 2 - t)).quasiMeasurePreserving using 1
  funext x
  ring

/-- Changing the input on a null set changes its quadratic average only on a
null set. -/
lemma aux_quadraticAverage_congr_ae
    (χ : ℝ → ℝ) (f g : ℝ → ℂ) (hfg : f =ᵐ[volume] g) :
    quadraticAverage χ f =ᵐ[volume] quadraticAverage χ g := by
  have hnorm : (fun y : ℝ ↦ ‖f y‖) =ᵐ[volume] fun y ↦ ‖g y‖ :=
    hfg.fun_comp norm
  have hjoint : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      ‖f (z.1 + z.2 ^ 2 - z.2)‖ = ‖g (z.1 + z.2 ^ 2 - z.2)‖ :=
    aux_quadratic_shift_quasiMeasurePreserving.tendsto_ae hnorm
  filter_upwards [Measure.ae_ae_of_ae_prod hjoint] with x hx
  change (∫ t : ℝ, ‖f (x + t ^ 2 - t)‖ * χ t) =
    ∫ t : ℝ, ‖g (x + t ^ 2 - t)‖ * χ t
  apply integral_congr_ae
  filter_upwards [hx] with t ht
  rw [ht]

/-- After choosing a strongly measurable representative, the quadratic
average is a.e. bounded by its reflected density convolution. -/
lemma aux_enorm_quadraticAverage_le_densityConvolution_mk
    (χ : ℝ → ℝ) (hχ : ∀ t : ℝ, 0 ≤ χ t) (hχmeas : Measurable χ)
    (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hD : Measurable (fun u : ℝ ↦ ENNReal.ofReal (aux_quadraticDensity χ u))) :
    ∀ᵐ x : ℝ ∂volume, ‖quadraticAverage χ f x‖ₑ ≤
      ∫⁻ y : ℝ, ENNReal.ofReal (aux_quadraticDensity χ (1 / 4 - y)) *
        ‖(hf.mk f) (x - y)‖ₑ := by
  let f₀ : ℝ → ℂ := hf.mk f
  have hf₀sm : StronglyMeasurable f₀ := hf.stronglyMeasurable_mk
  have hf₀meas : Measurable f₀ := hf₀sm.measurable
  have hF : Measurable (fun y : ℝ ↦ ‖f₀ y‖ₑ) := hf₀meas.enorm
  have hcongr : quadraticAverage χ f =ᵐ[volume] quadraticAverage χ f₀ :=
    aux_quadraticAverage_congr_ae χ f f₀ hf.ae_eq_mk
  filter_upwards [hcongr] with x hx
  rw [hx]
  apply aux_enorm_quadraticAverage_le_densityConvolution χ hχ f₀ hF hD x
  have hsq : Measurable (fun t : ℝ ↦ t ^ (2 : ℕ)) :=
    measurable_id.pow measurable_const
  have harg' : Measurable (fun t : ℝ ↦ x + t ^ 2 - t) :=
    (measurable_const.add hsq).sub measurable_id
  have harg : Measurable (fun t : ℝ ↦ x + (t ^ 2 - t)) := by
    convert harg' using 1
    ext t
    ring
  exact ENNReal.continuous_ofReal.measurable.comp ((hf₀meas.norm.comp harg).mul hχmeas)

/-- An integrable kernel times a finite-`Lᵖ` input has integrable raw
convolution sections for almost every spatial point. -/
lemma aux_ae_integrable_aux_convolution_sections {p : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    (κ f : ℝ → ℂ) (hκ : Integrable κ volume) (hf : MemLp f p volume) :
    ∀ᵐ x : ℝ ∂volume, Integrable (fun t : ℝ ↦ κ t * f (x - t)) volume := by
  let s : ℕ → Set ℝ := fun n ↦ Icc (-(n : ℝ)) n
  have hlocal (n : ℕ) :
      Integrable (fun z : ℝ × ℝ ↦ κ z.2 * f (z.1 - z.2))
        ((volume.restrict (s n)).prod volume) := by
    apply aux_local_convolution_integrable_prod κ f hκ hf (s n)
    · exact measurableSet_Icc
    · exact measure_Icc_lt_top
  have hper (n : ℕ) :
      ∀ᵐ x : ℝ ∂volume, x ∈ s n → Integrable (fun t : ℝ ↦ κ t * f (x - t)) volume :=
    ae_imp_of_ae_restrict (hlocal n).prod_right_ae
  have hall : ∀ᵐ x : ℝ ∂volume, ∀ n : ℕ,
      x ∈ s n → Integrable (fun t : ℝ ↦ κ t * f (x - t)) volume :=
    ae_all_iff.2 hper
  filter_upwards [hall] with x hx
  obtain ⟨n, hn⟩ := exists_nat_ge |x|
  apply hx n
  change -(n : ℝ) ≤ x ∧ x ≤ n
  constructor <;> linarith [neg_le_abs x, le_abs_self x]

/-- The `p = 3/2` section-integrability specialization needed at the
quadratic endpoint. -/
lemma aux_ae_integrable_aux_convolution_sections_threeHalves
    (κ f : ℝ → ℂ) (hκ : Integrable κ volume)
    (hf : MemLp f (3 / 2 : ℝ≥0∞) volume) :
    ∀ᵐ x : ℝ ∂volume, Integrable (fun t : ℝ ↦ κ t * f (x - t)) volume := by
  let : Fact (1 ≤ (3 / 2 : ℝ≥0∞)) := ⟨by
    refine (ENNReal.le_div_iff_mul_le (a := 1) (b := 2) (c := 3)
      (by simp) (by simp)).2 ?_
    norm_num⟩
  let : Fact ((3 / 2 : ℝ≥0∞) ≠ ∞) :=
    ⟨ENNReal.div_ne_top (by simp) (by norm_num)⟩
  exact aux_ae_integrable_aux_convolution_sections κ f hκ hf

/-- Section integrability in the exact quadratic-kernel orientation. -/
lemma aux_ae_integrable_quadraticKernel_sections_of_memLp
    (χ : ℝ → ℝ) (f : ℝ → ℂ)
    (hκ : MemLp (aux_quadraticKernel χ) (1 : ℝ≥0∞) volume)
    (hf : MemLp f (3 / 2 : ℝ≥0∞) volume) :
    ∀ᵐ x : ℝ ∂volume,
      Integrable (fun t : ℝ ↦ (aux_quadraticKernel χ t : ℂ) *
        (‖f (x - t)‖ : ℂ)) volume := by
  have hκc : Integrable (fun t : ℝ ↦ (aux_quadraticKernel χ t : ℂ)) volume :=
    memLp_one_iff_integrable.mp hκ.ofReal
  have hfc : MemLp (fun y : ℝ ↦ (‖f y‖ : ℂ)) (3 / 2 : ℝ≥0∞) volume :=
    hf.norm.ofReal
  exact aux_ae_integrable_aux_convolution_sections_threeHalves
    (fun t : ℝ ↦ (aux_quadraticKernel χ t : ℂ))
    (fun y : ℝ ↦ (‖f y‖ : ℂ)) hκc hfc

/-- For nonnegative real factors, an integrable complex raw convolution has
ENNReal norm equal to the corresponding nonnegative `lintegral`. -/
lemma aux_enorm_aux_convolution_eq_lintegral_of_nonneg
    (K F : ℝ → ℝ) (hK : ∀ t : ℝ, 0 ≤ K t) (hF : ∀ y : ℝ, 0 ≤ F y)
    (x : ℝ)
    (hint : Integrable (fun t : ℝ ↦ (K t : ℂ) * (F (x - t) : ℂ)) volume) :
    ‖aux_convolution (fun t : ℝ ↦ (K t : ℂ)) (fun y : ℝ ↦ (F y : ℂ)) x‖ₑ =
      ∫⁻ t : ℝ, ENNReal.ofReal (K t) * ENNReal.ofReal (F (x - t)) := by
  let r : ℝ → ℝ := fun t ↦ K t * F (x - t)
  have hr : Integrable r volume := by
    simpa [r] using hint.re
  have hr_nonneg (t : ℝ) : 0 ≤ r t := mul_nonneg (hK _) (hF _)
  have hint_eq : (∫ t : ℝ, (K t : ℂ) * (F (x - t) : ℂ)) =
      (∫ t : ℝ, r t : ℝ) := by
    calc
      (∫ t : ℝ, (K t : ℂ) * (F (x - t) : ℂ)) = ∫ t : ℝ, (r t : ℂ) := by
        apply integral_congr_ae
        filter_upwards with t
        simp [r]
      _ = (∫ t : ℝ, r t : ℝ) := integral_ofReal
  calc
    ‖aux_convolution (fun t : ℝ ↦ (K t : ℂ)) (fun y : ℝ ↦ (F y : ℂ)) x‖ₑ =
        ‖(∫ t : ℝ, r t : ℝ)‖ₑ := by
      simp only [aux_convolution, hint_eq, enorm_eq_nnnorm, Complex.nnnorm_real]
    _ = ENNReal.ofReal (∫ t : ℝ, r t) := by
      rw [← ofReal_norm, Real.norm_of_nonneg]
      exact integral_nonneg hr_nonneg
    _ = ENNReal.ofReal (∫ t : ℝ, ‖r t‖) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      rw [Real.norm_of_nonneg (hr_nonneg t)]
    _ = ∫⁻ t : ℝ, ‖r t‖ₑ := ofReal_integral_norm_eq_lintegral_enorm hr
    _ = ∫⁻ t : ℝ, ENNReal.ofReal (r t) := by
      apply lintegral_congr
      intro t
      rw [← ofReal_norm, Real.norm_of_nonneg (hr_nonneg t)]
    _ = ∫⁻ t : ℝ, ENNReal.ofReal (K t) * ENNReal.ofReal (F (x - t)) := by
      apply lintegral_congr
      intro t
      rw [← ENNReal.ofReal_mul (hK _)]

/-- Converts an a.e. nonnegative-lintegral convolution domination into the
same domination by the project's complex raw convolution. -/
lemma aux_ae_le_aux_convolution_of_ennreal
    (A : ℝ → ℝ≥0∞) (K F : ℝ → ℝ)
    (hK : ∀ t : ℝ, 0 ≤ K t) (hF : ∀ y : ℝ, 0 ≤ F y)
    (hdom : ∀ᵐ x : ℝ ∂volume, A x ≤
      ∫⁻ t : ℝ, ENNReal.ofReal (K t) * ENNReal.ofReal (F (x - t)))
    (hsections : ∀ᵐ x : ℝ ∂volume,
      Integrable (fun t : ℝ ↦ (K t : ℂ) * (F (x - t) : ℂ)) volume) :
    ∀ᵐ x : ℝ ∂volume, A x ≤
      ‖aux_convolution (fun t : ℝ ↦ (K t : ℂ)) (fun y : ℝ ↦ (F y : ℂ)) x‖ₑ := by
  filter_upwards [hdom, hsections] with x hx hix
  rw [aux_enorm_aux_convolution_eq_lintegral_of_nonneg K F hK hF x hix]
  exact hx

/-- The specialized conversion from the quadratic coarea domination to raw
convolution. -/
lemma aux_ae_quadraticAverage_le_aux_convolution_of_sections
    (χ : ℝ → ℝ) (f : ℝ → ℂ)
    (hdom : ∀ᵐ x : ℝ ∂volume, ‖quadraticAverage χ f x‖ₑ ≤
      ∫⁻ t : ℝ, ENNReal.ofReal (aux_quadraticKernel χ t) *
        ENNReal.ofReal ‖f (x - t)‖)
    (hsections : ∀ᵐ x : ℝ ∂volume,
      Integrable (fun t : ℝ ↦ (aux_quadraticKernel χ t : ℂ) *
        (‖f (x - t)‖ : ℂ)) volume)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) :
    ∀ᵐ x : ℝ ∂volume, ‖quadraticAverage χ f x‖ₑ ≤
      ‖aux_convolution (fun t : ℝ ↦ (aux_quadraticKernel χ t : ℂ))
        (fun y : ℝ ↦ (‖f y‖ : ℂ)) x‖ₑ := by
  exact aux_ae_le_aux_convolution_of_ennreal _ _ _
    (aux_quadraticKernel_nonneg χ hχ_nonneg) (fun y ↦ norm_nonneg _)
    hdom hsections

/-- Pointwise factorization of the weighted Cauchy--Schwarz integrand. -/
lemma aux_ennreal_weighted_factorization (k f : ℝ≥0∞) :
    (k * f ^ ((3 : ℝ) / 2)) ^ ((1 : ℝ) / 2) *
        (k * f ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2) = k * f := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  simp_rw [← ENNReal.rpow_mul]
  calc
    (k ^ ((1 : ℝ) / 2) * f ^ (((3 : ℝ) / 2) * ((1 : ℝ) / 2))) *
          (k ^ ((1 : ℝ) / 2) * f ^ (((1 : ℝ) / 2) * ((1 : ℝ) / 2))) =
        (k ^ ((1 : ℝ) / 2) * k ^ ((1 : ℝ) / 2)) *
          (f ^ (((3 : ℝ) / 2) * ((1 : ℝ) / 2)) *
            f ^ (((1 : ℝ) / 2) * ((1 : ℝ) / 2))) := by ac_rfl
    _ = k ^ (((1 : ℝ) / 2) + ((1 : ℝ) / 2)) *
          f ^ ((((3 : ℝ) / 2) * ((1 : ℝ) / 2)) +
            (((1 : ℝ) / 2) * ((1 : ℝ) / 2))) := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity),
        ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)]
    _ = k * f := by norm_num

/-- Squaring an ENNReal half-power recovers the original value. -/
lemma aux_ennreal_rpow_half_sq (a : ℝ≥0∞) :
    (a ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) = a := by
  rw [← ENNReal.rpow_mul]
  norm_num

/-- Weighted Cauchy--Schwarz for the nonnegative convolution factorization
at the `L^(3/2)` endpoint. -/
lemma aux_lintegral_weighted_cauchy_sq
    (K F : ℝ → ℝ≥0∞) (hK : AEMeasurable K volume)
    (hF : AEMeasurable F volume) (x : ℝ) :
    (∫⁻ t : ℝ, K t * F (x - t)) ^ (2 : ℝ) ≤
      (∫⁻ t : ℝ, K t * F (x - t) ^ ((3 : ℝ) / 2)) *
        ∫⁻ t : ℝ, K t * F (x - t) ^ ((1 : ℝ) / 2) := by
  let Fx : ℝ → ℝ≥0∞ := fun t ↦ F (x - t)
  have hFx : AEMeasurable Fx volume := by
    change AEMeasurable (F ∘ fun t : ℝ ↦ x - t) volume
    exact hF.comp_quasiMeasurePreserving
      (volume.measurePreserving_sub_left x).quasiMeasurePreserving
  let U : ℝ → ℝ≥0∞ := fun t ↦
    (K t * Fx t ^ ((3 : ℝ) / 2)) ^ ((1 : ℝ) / 2)
  let V : ℝ → ℝ≥0∞ := fun t ↦
    (K t * Fx t ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2)
  have hU : AEMeasurable U volume :=
    ((hK.mul (hFx.pow_const _)).pow_const _)
  have hV : AEMeasurable V volume :=
    ((hK.mul (hFx.pow_const _)).pow_const _)
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume (p := (2 : ℝ))
    (q := (2 : ℝ)) (by
      rw [Real.holderConjugate_iff]
      constructor <;> norm_num) hU hV
  have hleft : (∫⁻ t : ℝ, (U * V) t) = ∫⁻ t : ℝ, K t * Fx t := by
    apply lintegral_congr
    intro t
    exact aux_ennreal_weighted_factorization (K t) (Fx t)
  have hU_sq : (∫⁻ t : ℝ, U t ^ (2 : ℝ)) =
      ∫⁻ t : ℝ, K t * Fx t ^ ((3 : ℝ) / 2) := by
    apply lintegral_congr
    intro t
    exact aux_ennreal_rpow_half_sq _
  have hV_sq : (∫⁻ t : ℝ, V t ^ (2 : ℝ)) =
      ∫⁻ t : ℝ, K t * Fx t ^ ((1 : ℝ) / 2) := by
    apply lintegral_congr
    intro t
    exact aux_ennreal_rpow_half_sq _
  have hroot : (∫⁻ t : ℝ, K t * Fx t) ≤
      (∫⁻ t : ℝ, K t * Fx t ^ ((3 : ℝ) / 2)) ^ ((1 : ℝ) / 2) *
        (∫⁻ t : ℝ, K t * Fx t ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2) := by
    rw [hleft, hU_sq, hV_sq] at hholder
    exact hholder
  have hsq := ENNReal.rpow_le_rpow hroot (by norm_num : (0 : ℝ) ≤ 2)
  have hright :
      ((∫⁻ t : ℝ, K t * Fx t ^ ((3 : ℝ) / 2)) ^ ((1 : ℝ) / 2) *
        (∫⁻ t : ℝ, K t * Fx t ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) =
      (∫⁻ t : ℝ, K t * Fx t ^ ((3 : ℝ) / 2)) *
        ∫⁻ t : ℝ, K t * Fx t ^ ((1 : ℝ) / 2) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      aux_ennreal_rpow_half_sq, aux_ennreal_rpow_half_sq]
  rw [hright] at hsq
  simpa only [Fx] using hsq

/-- Converts a raw complex convolution of real-valued inputs into its real
Bochner integral. -/
lemma aux_convolution_ofReal_eq_integral
    (g K : ℝ → ℝ) (x : ℝ) :
    aux_convolution (fun t : ℝ ↦ (g t : ℂ)) (fun t : ℝ ↦ (K t : ℂ)) x =
      (∫ t : ℝ, g t * K (x - t) : ℝ) := by
  change (∫ t : ℝ, (g t : ℂ) * (K (x - t) : ℂ)) = _
  simp_rw [← Complex.ofReal_mul]
  exact integral_complex_ofReal

/-- At an integrable nonnegative convolution section, the raw convolution's
ENNReal norm is its nonnegative `lintegral`. -/
lemma aux_enorm_convolution_ofReal_eq_lintegral_of_nonneg
    (g K : ℝ → ℝ) (x : ℝ)
    (hint : Integrable (fun t : ℝ ↦ g t * K (x - t)) volume)
    (hnonneg : ∀ t : ℝ, 0 ≤ g t * K (x - t)) :
    ‖aux_convolution (fun t : ℝ ↦ (g t : ℂ))
      (fun t : ℝ ↦ (K t : ℂ)) x‖ₑ =
      ∫⁻ t : ℝ, ENNReal.ofReal (g t * K (x - t)) := by
  rw [aux_convolution_ofReal_eq_integral]
  have hI : 0 ≤ ∫ t : ℝ, g t * K (x - t) :=
    integral_nonneg fun t ↦ hnonneg t
  rw [← ofReal_norm]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hI]
  exact ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall hnonneg)

/-- The a.e. raw-convolution version of the weighted Cauchy--Schwarz
factorization. -/
lemma aux_weighted_cauchy_sq_ae
    (K F : ℝ → ℝ) (hKmeas : AEMeasurable K volume)
    (hFmeas : AEMeasurable F volume)
    (hKnonneg : ∀ t : ℝ, 0 ≤ K t) (hFnonneg : ∀ t : ℝ, 0 ≤ F t)
    (hA : ∀ᵐ x : ℝ ∂volume,
      Integrable (fun t : ℝ ↦ K t * F (x - t) ^ ((3 : ℝ) / 2)) volume)
    (hB : ∀ᵐ x : ℝ ∂volume,
      Integrable (fun t : ℝ ↦ K t * F (x - t) ^ ((1 : ℝ) / 2)) volume) :
    ∀ᵐ x : ℝ ∂volume,
      ‖aux_convolution (fun t : ℝ ↦ (K t : ℂ))
        (fun t : ℝ ↦ (F t : ℂ)) x‖ₑ ^ (2 : ℝ) ≤
        ‖aux_convolution (fun t : ℝ ↦ (K t : ℂ))
          (fun t : ℝ ↦ ((F t ^ ((3 : ℝ) / 2) : ℝ) : ℂ)) x‖ₑ *
          ‖aux_convolution (fun t : ℝ ↦ (K t : ℂ))
            (fun t : ℝ ↦ ((F t ^ ((1 : ℝ) / 2) : ℝ) : ℂ)) x‖ₑ := by
  let KE : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (K t)
  let FE : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (F t)
  have hKE : AEMeasurable KE volume := hKmeas.ennreal_ofReal
  have hFE : AEMeasurable FE volume := hFmeas.ennreal_ofReal
  filter_upwards [hA, hB] with x hxA hxB
  have hC :
      ‖aux_convolution (fun t : ℝ ↦ (K t : ℂ))
        (fun t : ℝ ↦ (F t : ℂ)) x‖ₑ ≤
      ∫⁻ t : ℝ, KE t * FE (x - t) := by
    calc
      ‖aux_convolution (fun t : ℝ ↦ (K t : ℂ))
          (fun t : ℝ ↦ (F t : ℂ)) x‖ₑ ≤
          ∫⁻ t : ℝ, ‖(K t : ℂ) * (F (x - t) : ℂ)‖ₑ :=
        enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ t : ℝ, KE t * FE (x - t) := by
        apply lintegral_congr
        intro t
        change ‖(K t : ℂ) * (F (x - t) : ℂ)‖ₑ =
          ENNReal.ofReal (K t) * ENNReal.ofReal (F (x - t))
        rw [← ofReal_norm, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (hKnonneg t),
          Real.norm_eq_abs, abs_of_nonneg (hFnonneg (x - t)),
          ENNReal.ofReal_mul (hKnonneg t)]
  have hAeq :
      ‖aux_convolution (fun t : ℝ ↦ (K t : ℂ))
        (fun t : ℝ ↦ ((F t ^ ((3 : ℝ) / 2) : ℝ) : ℂ)) x‖ₑ =
      ∫⁻ t : ℝ, KE t * FE (x - t) ^ ((3 : ℝ) / 2) := by
    rw [aux_enorm_convolution_ofReal_eq_lintegral_of_nonneg
      (fun t ↦ K t) (fun t ↦ F t ^ ((3 : ℝ) / 2)) x hxA]
    · apply lintegral_congr
      intro t
      rw [ENNReal.ofReal_mul (hKnonneg t), ← ENNReal.ofReal_rpow_of_nonneg
        (hFnonneg (x - t)) (by positivity)]
    · intro t
      exact mul_nonneg (hKnonneg t) (Real.rpow_nonneg (hFnonneg (x - t)) _)
  have hBeq :
      ‖aux_convolution (fun t : ℝ ↦ (K t : ℂ))
        (fun t : ℝ ↦ ((F t ^ ((1 : ℝ) / 2) : ℝ) : ℂ)) x‖ₑ =
      ∫⁻ t : ℝ, KE t * FE (x - t) ^ ((1 : ℝ) / 2) := by
    rw [aux_enorm_convolution_ofReal_eq_lintegral_of_nonneg
      (fun t ↦ K t) (fun t ↦ F t ^ ((1 : ℝ) / 2)) x hxB]
    · apply lintegral_congr
      intro t
      rw [ENNReal.ofReal_mul (hKnonneg t), ← ENNReal.ofReal_rpow_of_nonneg
        (hFnonneg (x - t)) (by positivity)]
    · intro t
      exact mul_nonneg (hKnonneg t) (Real.rpow_nonneg (hFnonneg (x - t)) _)
  have hweight := aux_lintegral_weighted_cauchy_sq KE FE hKE hFE x
  exact (ENNReal.rpow_le_rpow hC (by norm_num : (0 : ℝ) ≤ 2)).trans
    (by simpa only [hAeq, hBeq] using hweight)

/-- Raw convolution is commutative for complex multiplication. -/
lemma aux_convolution_comm (K g : ℝ → ℂ) :
    aux_convolution K g = aux_convolution g K := by
  rw [aux_convolution_eq_measureTheory_convolution,
    aux_convolution_eq_measureTheory_convolution]
  simpa using
    (convolution_flip (L := ContinuousLinearMap.mul ℂ ℂ)
      (f := K) (g := g) (μ := volume)).symm

/-- Pointwise `L^(3/2)`--`L³` Hölder bound for raw convolution. -/
lemma aux_enorm_convolution_le_threeHalves_three
    (κ g : ℝ → ℂ)
    (hκ : MemLp κ (3 / 2 : ℝ≥0∞) volume)
    (hg : MemLp g (3 : ℝ≥0∞) volume)
    (x : ℝ) :
    ‖aux_convolution κ g x‖ₑ ≤
      eLpNorm κ (3 / 2 : ℝ≥0∞) volume * eLpNorm g (3 : ℝ≥0∞) volume := by
  have hgx : MemLp (g ∘ fun t : ℝ ↦ x - t) (3 : ℝ≥0∞) volume :=
    hg.comp_measurePreserving (volume.measurePreserving_sub_left x)
  calc
    ‖aux_convolution κ g x‖ₑ ≤ ∫⁻ t : ℝ, ‖κ t * g (x - t)‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ t : ℝ, ‖κ t‖ₑ * ‖g (x - t)‖ₑ := by simp only [enorm_mul]
    _ ≤ (∫⁻ t : ℝ, ‖κ t‖ₑ ^ (3 / 2 : ℝ)) ^ (1 / (3 / 2 : ℝ)) *
          (∫⁻ t : ℝ, ‖g (x - t)‖ₑ ^ (3 : ℝ)) ^ (1 / (3 : ℝ)) :=
      ENNReal.lintegral_mul_le_Lp_mul_Lq volume (by
        rw [Real.holderConjugate_iff]
        constructor <;> norm_num)
        hκ.1.enorm hgx.1.enorm
    _ = eLpNorm κ (3 / 2 : ℝ≥0∞) volume *
          eLpNorm (g ∘ fun t : ℝ ↦ x - t) (3 : ℝ≥0∞) volume := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (3 / 2 : ℝ≥0∞) ≠ 0)
            (by finiteness : (3 / 2 : ℝ≥0∞) ≠ ∞),
          eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (3 : ℝ≥0∞) ≠ 0)
            (by norm_num : (3 : ℝ≥0∞) ≠ ∞)]
      norm_num
    _ = eLpNorm κ (3 / 2 : ℝ≥0∞) volume * eLpNorm g (3 : ℝ≥0∞) volume := by
      rw [eLpNorm_comp_measurePreserving hg.1 (volume.measurePreserving_sub_left x)]

/-- The ENNReal exponent `3/2` agrees with the corresponding real constant. -/
lemma aux_ennreal_ofReal_threeHalves :
    ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- The ENNReal exponent `1/2` agrees with the corresponding real constant. -/
lemma aux_ennreal_ofReal_half :
    ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- Dividing the endpoint exponent `3/2` by `1/2` yields `3`. -/
lemma aux_ennreal_threeHalves_div_half :
    (3 / 2 : ℝ≥0∞) / (1 / 2 : ℝ≥0∞) = 3 := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  rw [one_mul, inv_inv, mul_assoc]
  have htwo : (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞) = 1 := by
    rw [mul_comm]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  rw [htwo, mul_one]

/-- The `3/2` power of an `L^(3/2)` function is in `L¹`. -/
lemma aux_memLp_norm_rpow_threeHalves_one (f : ℝ → ℂ)
    (hf : MemLp f (3 / 2 : ℝ≥0∞) volume) :
    MemLp (fun x : ℝ ↦ ((‖f x‖ ^ (3 / 2 : ℝ) : ℝ) : ℂ))
      (1 : ℝ≥0∞) volume := by
  have hreal : MemLp (fun x : ℝ ↦ ‖f x‖ ^ (3 / 2 : ℝ))
      (1 : ℝ≥0∞) volume := by
    simpa using hf.norm_rpow (by norm_num : (3 / 2 : ℝ≥0∞) ≠ 0)
      (by finiteness : (3 / 2 : ℝ≥0∞) ≠ ∞)
  exact (hreal.ofReal :
    MemLp (fun x : ℝ ↦ ((‖f x‖ ^ (3 / 2 : ℝ) : ℝ) : ℂ))
      (1 : ℝ≥0∞) volume)

/-- The square root of an `L^(3/2)` function is in `L³`. -/
lemma aux_memLp_norm_rpow_half_three (f : ℝ → ℂ)
    (hf : MemLp f (3 / 2 : ℝ≥0∞) volume) :
    MemLp (fun x : ℝ ↦ ((‖f x‖ ^ (1 / 2 : ℝ) : ℝ) : ℂ))
      (3 : ℝ≥0∞) volume := by
  have hreal := hf.norm_rpow_div (1 / 2 : ℝ≥0∞)
  have hp : (3 / 2 : ℝ≥0∞) / (1 / 2 : ℝ≥0∞) = 3 :=
    aux_ennreal_threeHalves_div_half
  rw [hp] at hreal
  convert hreal.ofReal using 1
  all_goals norm_num

/-- Exact `L¹` seminorm of the `3/2` power used in the factorization. -/
lemma aux_eLpNorm_norm_rpow_threeHalves_one (f : ℝ → ℂ) :
    eLpNorm (fun x : ℝ ↦ ((‖f x‖ ^ (3 / 2 : ℝ) : ℝ) : ℂ))
      (1 : ℝ≥0∞) volume =
      eLpNorm f (3 / 2 : ℝ≥0∞) volume ^ (3 / 2 : ℝ) := by
  calc
    eLpNorm (fun x : ℝ ↦ ((‖f x‖ ^ (3 / 2 : ℝ) : ℝ) : ℂ))
        (1 : ℝ≥0∞) volume =
        eLpNorm (fun x : ℝ ↦ ‖f x‖ ^ (3 / 2 : ℝ))
          (1 : ℝ≥0∞) volume :=
      eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x ↦ by
        simp [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)])
    _ = eLpNorm f ((1 : ℝ≥0∞) * ENNReal.ofReal (3 / 2 : ℝ)) volume ^
          (3 / 2 : ℝ) := by
      rw [eLpNorm_norm_rpow f (by norm_num)]
    _ = eLpNorm f (3 / 2 : ℝ≥0∞) volume ^ (3 / 2 : ℝ) := by
      rw [aux_ennreal_ofReal_threeHalves]
      norm_num

/-- Exact `L³` seminorm of the square-root factor. -/
lemma aux_eLpNorm_norm_rpow_half_three (f : ℝ → ℂ) :
    eLpNorm (fun x : ℝ ↦ ((‖f x‖ ^ (1 / 2 : ℝ) : ℝ) : ℂ))
      (3 : ℝ≥0∞) volume =
      eLpNorm f (3 / 2 : ℝ≥0∞) volume ^ (1 / 2 : ℝ) := by
  calc
    eLpNorm (fun x : ℝ ↦ ((‖f x‖ ^ (1 / 2 : ℝ) : ℝ) : ℂ))
        (3 : ℝ≥0∞) volume =
        eLpNorm (fun x : ℝ ↦ ‖f x‖ ^ (1 / 2 : ℝ))
          (3 : ℝ≥0∞) volume :=
      eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x ↦ by
        simp [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)])
    _ = eLpNorm f ((3 : ℝ≥0∞) * ENNReal.ofReal (1 / 2 : ℝ)) volume ^
          (1 / 2 : ℝ) := by
      rw [eLpNorm_norm_rpow f (by norm_num)]
    _ = eLpNorm f (3 / 2 : ℝ≥0∞) volume ^ (1 / 2 : ℝ) := by
      rw [aux_ennreal_ofReal_half]
      simp only [div_eq_mul_inv, one_mul]

/-- An a.e. pointwise square factorization gives the corresponding `L³`
seminorm estimate. -/
lemma aux_eLpNorm_sq_le_mul_of_ae_sq_le_mul
    (C A B : ℝ → ℂ) (hA : AEStronglyMeasurable A volume)
    (hpoint : ∀ᵐ x : ℝ ∂volume, ‖C x‖ ^ (2 : ℝ) ≤ ‖A x‖ * ‖B x‖) :
    eLpNorm C (3 : ℝ≥0∞) volume ^ (2 : ℝ) ≤
      eLpNorm A (3 / 2 : ℝ≥0∞) volume * eLpNorm B (∞ : ℝ≥0∞) volume := by
  let Csq : ℝ → ℂ := fun x ↦ ((‖C x‖ ^ (2 : ℝ) : ℝ) : ℂ)
  have hmono : eLpNorm Csq (3 / 2 : ℝ≥0∞) volume ≤
      eLpNorm (fun x ↦ A x * B x) (3 / 2 : ℝ≥0∞) volume := by
    apply eLpNorm_mono_ae
    filter_upwards [hpoint] with x hx
    simpa [Csq] using hx
  have hprod : eLpNorm (fun x ↦ A x * B x) (3 / 2 : ℝ≥0∞) volume ≤
      eLpNorm A (3 / 2 : ℝ≥0∞) volume * eLpNorm B (∞ : ℝ≥0∞) volume := by
    simpa using
      (eLpNorm_le_eLpNorm_mul_eLpNorm_top (p := (3 / 2 : ℝ≥0∞)) hA B
        (fun a b : ℂ ↦ a * b) 1
        (Filter.Eventually.of_forall fun x ↦ by simp))
  have hCsq : eLpNorm Csq (3 / 2 : ℝ≥0∞) volume =
      eLpNorm C (3 : ℝ≥0∞) volume ^ (2 : ℝ) := by
    calc
      eLpNorm Csq (3 / 2 : ℝ≥0∞) volume =
          eLpNorm (fun x ↦ ‖C x‖ ^ (2 : ℝ)) (3 / 2 : ℝ≥0∞) volume := by
        apply eLpNorm_congr_norm_ae
        exact Filter.Eventually.of_forall fun x ↦ by simp [Csq]
      _ = eLpNorm C ((3 / 2 : ℝ≥0∞) * ENNReal.ofReal (2 : ℝ)) volume ^
          (2 : ℝ) := by
        rw [eLpNorm_norm_rpow C (by norm_num : (0 : ℝ) < 2)]
      _ = eLpNorm C (3 : ℝ≥0∞) volume ^ (2 : ℝ) := by
        have h : (3 / 2 : ℝ≥0∞) * ENNReal.ofReal (2 : ℝ) = 3 := by
          rw [show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num,
            div_eq_mul_inv]
          calc
            3 * (2 : ℝ≥0∞)⁻¹ * 2 = 3 * ((2 : ℝ≥0∞)⁻¹ * 2) := by ac_rfl
            _ = 3 * 1 := by rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
            _ = 3 := by simp
        rw [h]
  calc
    eLpNorm C (3 : ℝ≥0∞) volume ^ (2 : ℝ) =
        eLpNorm Csq (3 / 2 : ℝ≥0∞) volume := hCsq.symm
    _ ≤ eLpNorm (fun x ↦ A x * B x) (3 / 2 : ℝ≥0∞) volume := hmono
    _ ≤ eLpNorm A (3 / 2 : ℝ≥0∞) volume * eLpNorm B (∞ : ℝ≥0∞) volume := hprod

/-- Specialized `L^(3/2) → L³` Young inequality for a nonnegative real
kernel in both `L¹` and `L^(3/2)`. -/
lemma aux_eLpNorm_convolution_nonneg_real_threeHalves
    (K : ℝ → ℝ) (hKone : MemLp K (1 : ℝ≥0∞) volume)
    (hKthree : MemLp K (3 / 2 : ℝ≥0∞) volume)
    (hKnonneg : ∀ x : ℝ, 0 ≤ K x)
    (f : ℝ → ℂ) (hf : MemLp f (3 / 2 : ℝ≥0∞) volume) :
    eLpNorm
      (aux_convolution (fun x : ℝ ↦ (K x : ℂ))
        (fun x : ℝ ↦ (‖f x‖ : ℂ))) (3 : ℝ≥0∞) volume ≠ ∞ ∧
      (eLpNorm
        (aux_convolution (fun x : ℝ ↦ (K x : ℂ))
          (fun x : ℝ ↦ (‖f x‖ : ℂ))) (3 : ℝ≥0∞) volume).toReal ≤
        (eLpNorm K (3 / 2 : ℝ≥0∞) volume).toReal *
          (eLpNorm f (3 / 2 : ℝ≥0∞) volume).toReal := by
  let KC : ℝ → ℂ := fun x ↦ (K x : ℂ)
  let FC : ℝ → ℂ := fun x ↦ (‖f x‖ : ℂ)
  let FP : ℝ → ℂ := fun x ↦ ((‖f x‖ ^ (3 / 2 : ℝ) : ℝ) : ℂ)
  let FH : ℝ → ℂ := fun x ↦ ((‖f x‖ ^ (1 / 2 : ℝ) : ℝ) : ℂ)
  let C : ℝ → ℂ := aux_convolution KC FC
  let A : ℝ → ℂ := aux_convolution KC FP
  let B : ℝ → ℂ := aux_convolution KC FH
  change eLpNorm C (3 : ℝ≥0∞) volume ≠ ∞ ∧
    (eLpNorm C (3 : ℝ≥0∞) volume).toReal ≤ _
  have hKCone : MemLp KC (1 : ℝ≥0∞) volume := by
    change MemLp (fun x : ℝ ↦ (K x : ℂ)) (1 : ℝ≥0∞) volume
    exact hKone.ofReal
  have hKCthree : MemLp KC (3 / 2 : ℝ≥0∞) volume := by
    change MemLp (fun x : ℝ ↦ (K x : ℂ)) (3 / 2 : ℝ≥0∞) volume
    exact hKthree.ofReal
  have hFP : MemLp FP (1 : ℝ≥0∞) volume := by
    simpa only [FP] using aux_memLp_norm_rpow_threeHalves_one f hf
  have hFH : MemLp FH (3 : ℝ≥0∞) volume := by
    simpa only [FH] using aux_memLp_norm_rpow_half_three f hf
  have hFpowR : MemLp (fun x : ℝ ↦ ‖f x‖ ^ (3 / 2 : ℝ))
      (1 : ℝ≥0∞) volume := by
    simpa using hf.norm_rpow (by norm_num : (3 / 2 : ℝ≥0∞) ≠ 0)
      (by finiteness : (3 / 2 : ℝ≥0∞) ≠ ∞)
  have hFhalfR : MemLp (fun x : ℝ ↦ ‖f x‖ ^ (1 / 2 : ℝ))
      (3 : ℝ≥0∞) volume := by
    have h := hf.norm_rpow_div (1 / 2 : ℝ≥0∞)
    rw [aux_ennreal_threeHalves_div_half] at h
    convert h using 1; norm_num
  have hAint : ∀ᵐ x : ℝ ∂volume,
      Integrable (fun t : ℝ ↦ K t * ‖f (x - t)‖ ^ (3 / 2 : ℝ)) volume := by
    have hraw : ∀ᵐ x : ℝ ∂volume,
        ConvolutionExistsAt K (fun y : ℝ ↦ ‖f y‖ ^ (3 / 2 : ℝ)) x
          (ContinuousLinearMap.mul ℝ ℝ) volume :=
      (memLp_one_iff_integrable.mp hKone).ae_convolution_exists
        (L := ContinuousLinearMap.mul ℝ ℝ)
        (memLp_one_iff_integrable.mp hFpowR)
    filter_upwards [hraw] with x hx
    exact hx.integrable
  have hBint : ∀ᵐ x : ℝ ∂volume,
      Integrable (fun t : ℝ ↦ K t * ‖f (x - t)‖ ^ (1 / 2 : ℝ)) volume := by
    filter_upwards with x
    have hshift : MemLp ((fun y : ℝ ↦ ‖f y‖ ^ (1 / 2 : ℝ)) ∘
        fun t : ℝ ↦ x - t) (3 : ℝ≥0∞) volume :=
      hFhalfR.comp_measurePreserving (volume.measurePreserving_sub_left x)
    let : ENNReal.HolderTriple (3 / 2 : ℝ≥0∞) (3 : ℝ≥0∞) 1 := ⟨by
      rw [ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      calc
        2 * (3 : ℝ≥0∞)⁻¹ + 3⁻¹ = (2 + 1) * 3⁻¹ := by ring
        _ = 3 * 3⁻¹ := by norm_num
        _ = (1 : ℝ≥0∞)⁻¹ := by
          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
          simp⟩
    change Integrable
      (K * ((fun y : ℝ ↦ ‖f y‖ ^ (1 / 2 : ℝ)) ∘ fun t : ℝ ↦ x - t)) volume
    exact hKthree.integrable_mul hshift
  have hpointE : ∀ᵐ x : ℝ ∂volume,
      ‖C x‖ₑ ^ (2 : ℝ) ≤ ‖A x‖ₑ * ‖B x‖ₑ := by
    simpa only [C, A, B, KC, FC, FP, FH] using
      aux_weighted_cauchy_sq_ae K (fun x : ℝ ↦ ‖f x‖)
        hKone.1.aemeasurable hf.norm.1.aemeasurable hKnonneg
        (fun x ↦ norm_nonneg _) hAint hBint
  have hpoint : ∀ᵐ x : ℝ ∂volume,
      ‖C x‖ ^ (2 : ℝ) ≤ ‖A x‖ * ‖B x‖ := by
    filter_upwards [hpointE] with x hx
    have hx' := ENNReal.toReal_mono
      (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top) hx
    simpa using hx'
  let : Fact (1 ≤ (3 / 2 : ℝ≥0∞)) := ⟨by
    apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
      (Or.inl (by norm_num))).mpr
    norm_num⟩
  let : Fact ((3 / 2 : ℝ≥0∞) ≠ ∞) := ⟨by finiteness⟩
  have hAeq : A = aux_convolution FP KC := by
    simpa only [A, KC, FP] using aux_convolution_comm KC FP
  have hAraw : MemLp A (3 / 2 : ℝ≥0∞) volume := by
    rw [hAeq]
    exact aux_convolution_memLp_of_memLp_one FP KC
      (memLp_one_iff_integrable.mp hFP) hKCthree
  have hAbound : eLpNorm A (3 / 2 : ℝ≥0∞) volume ≤
      eLpNorm FP (1 : ℝ≥0∞) volume * eLpNorm KC (3 / 2 : ℝ≥0∞) volume := by
    rw [hAeq]
    exact aux_eLpNorm_aux_convolution_le_of_memLp_one FP KC hFP hKCthree
  have hBbound : eLpNorm B (∞ : ℝ≥0∞) volume ≤
      eLpNorm KC (3 / 2 : ℝ≥0∞) volume * eLpNorm FH (3 : ℝ≥0∞) volume := by
    rw [eLpNorm_exponent_top]
    apply eLpNormEssSup_le_of_ae_enorm_bound
    filter_upwards with x
    exact aux_enorm_convolution_le_threeHalves_three KC FH hKCthree hFH x
  have hfac : eLpNorm C (3 : ℝ≥0∞) volume ^ (2 : ℝ) ≤
      eLpNorm A (3 / 2 : ℝ≥0∞) volume * eLpNorm B (∞ : ℝ≥0∞) volume :=
    aux_eLpNorm_sq_le_mul_of_ae_sq_le_mul C A B hAraw.aestronglyMeasurable hpoint
  have hKCnorm : eLpNorm KC (3 / 2 : ℝ≥0∞) volume =
      eLpNorm K (3 / 2 : ℝ≥0∞) volume := by
    apply eLpNorm_congr_norm_ae
    filter_upwards with x
    simp [KC]
  have hFPnorm : eLpNorm FP (1 : ℝ≥0∞) volume =
      eLpNorm f (3 / 2 : ℝ≥0∞) volume ^ (3 / 2 : ℝ) := by
    simpa only [FP] using aux_eLpNorm_norm_rpow_threeHalves_one f
  have hFHnorm : eLpNorm FH (3 : ℝ≥0∞) volume =
      eLpNorm f (3 / 2 : ℝ≥0∞) volume ^ (1 / 2 : ℝ) := by
    simpa only [FH] using aux_eLpNorm_norm_rpow_half_three f
  have hCbound : eLpNorm C (3 : ℝ≥0∞) volume ^ (2 : ℝ) ≤
      (eLpNorm f (3 / 2 : ℝ≥0∞) volume ^ (3 / 2 : ℝ) *
        eLpNorm K (3 / 2 : ℝ≥0∞) volume) *
      (eLpNorm K (3 / 2 : ℝ≥0∞) volume *
        eLpNorm f (3 / 2 : ℝ≥0∞) volume ^ (1 / 2 : ℝ)) := by
    calc
      eLpNorm C (3 : ℝ≥0∞) volume ^ (2 : ℝ) ≤
          eLpNorm A (3 / 2 : ℝ≥0∞) volume * eLpNorm B (∞ : ℝ≥0∞) volume := hfac
      _ ≤ (eLpNorm FP (1 : ℝ≥0∞) volume *
          eLpNorm KC (3 / 2 : ℝ≥0∞) volume) *
          (eLpNorm KC (3 / 2 : ℝ≥0∞) volume *
          eLpNorm FH (3 : ℝ≥0∞) volume) :=
        mul_le_mul hAbound hBbound bot_le bot_le
      _ = (eLpNorm f (3 / 2 : ℝ≥0∞) volume ^ (3 / 2 : ℝ) *
          eLpNorm K (3 / 2 : ℝ≥0∞) volume) *
          (eLpNorm K (3 / 2 : ℝ≥0∞) volume *
          eLpNorm f (3 / 2 : ℝ≥0∞) volume ^ (1 / 2 : ℝ)) := by
        rw [hKCnorm, hFPnorm, hFHnorm]
  have hKtop : eLpNorm K (3 / 2 : ℝ≥0∞) volume ≠ ∞ :=
    hKthree.eLpNorm_ne_top
  have hFtop : eLpNorm f (3 / 2 : ℝ≥0∞) volume ≠ ∞ :=
    hf.eLpNorm_ne_top
  have hFthreeTop : eLpNorm f (3 / 2 : ℝ≥0∞) volume ^ (3 / 2 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hFtop
  have hFhalfTop : eLpNorm f (3 / 2 : ℝ≥0∞) volume ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hFtop
  have hrightTop :
      (eLpNorm f (3 / 2 : ℝ≥0∞) volume ^ (3 / 2 : ℝ) *
        eLpNorm K (3 / 2 : ℝ≥0∞) volume) *
      (eLpNorm K (3 / 2 : ℝ≥0∞) volume *
        eLpNorm f (3 / 2 : ℝ≥0∞) volume ^ (1 / 2 : ℝ)) ≠ ∞ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hFthreeTop hKtop)
      (ENNReal.mul_ne_top hKtop hFhalfTop)
  have hCpowTop : eLpNorm C (3 : ℝ≥0∞) volume ^ (2 : ℝ) ≠ ∞ :=
    ne_top_of_le_ne_top hrightTop hCbound
  have hCtop : eLpNorm C (3 : ℝ≥0∞) volume ≠ ∞ := by
    intro htop
    apply hCpowTop
    rw [htop]
    norm_num
  refine ⟨hCtop, ?_⟩
  have hCboundReal := ENNReal.toReal_mono hrightTop hCbound
  have hCsq : (eLpNorm C (3 : ℝ≥0∞) volume).toReal ^ (2 : ℝ) ≤
      ((eLpNorm f (3 / 2 : ℝ≥0∞) volume).toReal ^ (3 / 2 : ℝ) *
        (eLpNorm K (3 / 2 : ℝ≥0∞) volume).toReal) *
      ((eLpNorm K (3 / 2 : ℝ≥0∞) volume).toReal *
        (eLpNorm f (3 / 2 : ℝ≥0∞) volume).toReal ^ (1 / 2 : ℝ)) := by
    simpa only [ENNReal.toReal_rpow, ENNReal.toReal_mul] using hCboundReal
  have hFpow : (eLpNorm f (3 / 2 : ℝ≥0∞) volume).toReal ^ (3 / 2 : ℝ) *
      (eLpNorm f (3 / 2 : ℝ≥0∞) volume).toReal ^ (1 / 2 : ℝ) =
      (eLpNorm f (3 / 2 : ℝ≥0∞) volume).toReal ^ (2 : ℝ) := by
    rw [← Real.rpow_add' ENNReal.toReal_nonneg (by norm_num :
      (3 / 2 : ℝ) + 1 / 2 ≠ 0)]
    norm_num
  have hsq : (eLpNorm C (3 : ℝ≥0∞) volume).toReal ^ (2 : ℝ) ≤
      ((eLpNorm K (3 / 2 : ℝ≥0∞) volume).toReal *
        (eLpNorm f (3 / 2 : ℝ≥0∞) volume).toReal) ^ (2 : ℝ) := by
    calc
      (eLpNorm C (3 : ℝ≥0∞) volume).toReal ^ (2 : ℝ) ≤
          ((eLpNorm f (3 / 2 : ℝ≥0∞) volume).toReal ^ (3 / 2 : ℝ) *
            (eLpNorm K (3 / 2 : ℝ≥0∞) volume).toReal) *
          ((eLpNorm K (3 / 2 : ℝ≥0∞) volume).toReal *
            (eLpNorm f (3 / 2 : ℝ≥0∞) volume).toReal ^ (1 / 2 : ℝ)) := hCsq
      _ = ((eLpNorm K (3 / 2 : ℝ≥0∞) volume).toReal *
          (eLpNorm f (3 / 2 : ℝ≥0∞) volume).toReal) ^ (2 : ℝ) := by
        calc
          ((eLpNorm f (3 / 2 : ℝ≥0∞) volume).toReal ^ (3 / 2 : ℝ) *
              (eLpNorm K (3 / 2 : ℝ≥0∞) volume).toReal) *
              ((eLpNorm K (3 / 2 : ℝ≥0∞) volume).toReal *
                (eLpNorm f (3 / 2 : ℝ≥0∞) volume).toReal ^ (1 / 2 : ℝ)) =
              (eLpNorm K (3 / 2 : ℝ≥0∞) volume).toReal ^ (2 : ℕ) *
                ((eLpNorm f (3 / 2 : ℝ≥0∞) volume).toReal ^ (3 / 2 : ℝ) *
                  (eLpNorm f (3 / 2 : ℝ≥0∞) volume).toReal ^ (1 / 2 : ℝ)) := by
            ring
          _ = (eLpNorm K (3 / 2 : ℝ≥0∞) volume).toReal ^ (2 : ℕ) *
              (eLpNorm f (3 / 2 : ℝ≥0∞) volume).toReal ^ (2 : ℝ) := by
            rw [hFpow]
          _ = ((eLpNorm K (3 / 2 : ℝ≥0∞) volume).toReal *
              (eLpNorm f (3 / 2 : ℝ≥0∞) volume).toReal) ^ (2 : ℝ) := by
            have htwo (x : ℝ) : x ^ (2 : ℝ) = x ^ (2 : ℕ) := by norm_num
            rw [htwo (eLpNorm f (3 / 2 : ℝ≥0∞) volume).toReal,
              htwo ((eLpNorm K (3 / 2 : ℝ≥0∞) volume).toReal *
                (eLpNorm f (3 / 2 : ℝ≥0∞) volume).toReal), mul_pow]
  apply (sq_le_sq₀ ENNReal.toReal_nonneg
    (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)).mp
  simpa using hsq

/--
Define
\[
\mathcal A_\chi f(x):=\int_\mathbb R|f(x+t^2-t)|\chi(t)\,dt,
\qquad
C_{\ref{lem:quadratic-average},\,\chi}:=2^2(1+R_\chi)^{1/3}.
\]
Then, for every \(f\in L^{3/2}(\mathbb R)\),
\[
\lVert\mathcal A_\chi f\rVert_3
\leq C_{\ref{lem:quadratic-average},\,\chi}\lVert f\rVert_{3/2}.
\]
-/
theorem quadraticAveragingOperator
    (χ : ℝ → ℝ)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (f : ℝ → ℂ) (hf : MemLp f (3 / 2 : ℝ≥0∞) volume) :
    (eLpNorm (quadraticAverage χ f) (3 : ℝ≥0∞) volume).toReal ≤
      C_quadraticAveragingOperator χ *
        (eLpNorm f (3 / 2 : ℝ≥0∞) volume).toReal := by
  let f₀ : ℝ → ℂ := hf.1.mk f
  have hχmeas : Measurable χ := hχ_smooth.continuous.measurable
  have hDmeas : Measurable (fun u : ℝ ↦ ENNReal.ofReal (aux_quadraticDensity χ u)) :=
    aux_quadraticDensity_measurable_ennreal χ hχ_smooth
  have hDone : MemLp (aux_quadraticDensity χ) (1 : ℝ≥0∞) volume :=
    aux_quadraticDensity_memLp_one χ hχ_smooth hχ_compact hχ_nonneg hχ_le_one
  have hDthree : MemLp (aux_quadraticDensity χ) (3 / 2 : ℝ≥0∞) volume :=
    aux_quadraticDensity_memLp_threeHalves χ hχ_smooth hχ_compact hχ_nonneg hχ_le_one
  have hκone : MemLp (aux_quadraticKernel χ) (1 : ℝ≥0∞) volume :=
    aux_quadraticKernel_memLp χ 1 hDone
  have hκthree : MemLp (aux_quadraticKernel χ) (3 / 2 : ℝ≥0∞) volume :=
    aux_quadraticKernel_memLp χ (3 / 2 : ℝ≥0∞) hDthree
  have hf₀ : MemLp f₀ (3 / 2 : ℝ≥0∞) volume := by
    simpa only [f₀] using MemLp.ae_eq hf.1.ae_eq_mk hf
  have hquad : quadraticAverage χ f =ᵐ[volume] quadraticAverage χ f₀ :=
    aux_quadraticAverage_congr_ae χ f f₀ hf.1.ae_eq_mk
  have hbase := aux_enorm_quadraticAverage_le_densityConvolution_mk
    χ hχ_nonneg hχmeas f hf.1 hDmeas
  have hdom : ∀ᵐ x : ℝ ∂volume, ‖quadraticAverage χ f₀ x‖ₑ ≤
      ∫⁻ t : ℝ, ENNReal.ofReal (aux_quadraticKernel χ t) *
        ENNReal.ofReal ‖f₀ (x - t)‖ := by
    filter_upwards [hbase, hquad] with x hx hq
    rw [← hq]
    simpa only [f₀, aux_quadraticKernel, ofReal_norm] using hx
  have hsections := aux_ae_integrable_quadraticKernel_sections_of_memLp χ f₀ hκone hf₀
  have hraw : ∀ᵐ x : ℝ ∂volume, ‖quadraticAverage χ f₀ x‖ₑ ≤
      ‖aux_convolution (fun t : ℝ ↦ (aux_quadraticKernel χ t : ℂ))
        (fun y : ℝ ↦ (‖f₀ y‖ : ℂ)) x‖ₑ :=
    aux_ae_quadraticAverage_le_aux_convolution_of_sections χ f₀ hdom hsections hχ_nonneg
  have hrawf : ∀ᵐ x : ℝ ∂volume, ‖quadraticAverage χ f x‖ₑ ≤
      ‖aux_convolution (fun t : ℝ ↦ (aux_quadraticKernel χ t : ℂ))
        (fun y : ℝ ↦ (‖f₀ y‖ : ℂ)) x‖ₑ := by
    filter_upwards [hquad, hraw] with x hq hr
    rw [hq]
    exact hr
  have hendpoint := aux_eLpNorm_convolution_nonneg_real_threeHalves
    (aux_quadraticKernel χ) hκone hκthree
    (aux_quadraticKernel_nonneg χ hχ_nonneg) f₀ hf₀
  have hmono : eLpNorm (quadraticAverage χ f) (3 : ℝ≥0∞) volume ≤
      eLpNorm (aux_convolution (fun t : ℝ ↦ (aux_quadraticKernel χ t : ℂ))
        (fun y : ℝ ↦ (‖f₀ y‖ : ℂ))) (3 : ℝ≥0∞) volume := by
    apply eLpNorm_mono_ae
    filter_upwards [hrawf] with x hx
    have hx' := ENNReal.toReal_mono enorm_ne_top hx
    simpa using hx'
  have hqtop : eLpNorm (quadraticAverage χ f) (3 : ℝ≥0∞) volume ≠ ∞ :=
    ne_top_of_le_ne_top hendpoint.1 hmono
  have hmonoreal : (eLpNorm (quadraticAverage χ f) (3 : ℝ≥0∞) volume).toReal ≤
      (eLpNorm (aux_convolution (fun t : ℝ ↦ (aux_quadraticKernel χ t : ℂ))
        (fun y : ℝ ↦ (‖f₀ y‖ : ℂ))) (3 : ℝ≥0∞) volume).toReal :=
    (ENNReal.toReal_le_toReal hqtop hendpoint.1).mpr hmono
  have hf₀norm : eLpNorm f₀ (3 / 2 : ℝ≥0∞) volume =
      eLpNorm f (3 / 2 : ℝ≥0∞) volume := by
    apply eLpNorm_congr_ae
    exact hf.1.ae_eq_mk.symm
  have hκnorm : (eLpNorm (aux_quadraticKernel χ) (3 / 2 : ℝ≥0∞) volume).toReal ≤
      C_quadraticAveragingOperator χ := by
    calc
      (eLpNorm (aux_quadraticKernel χ) (3 / 2 : ℝ≥0∞) volume).toReal =
          (eLpNorm (aux_quadraticDensity χ) (3 / 2 : ℝ≥0∞) volume).toReal := by
        rw [aux_quadraticKernel_eLpNorm χ (3 / 2 : ℝ≥0∞) hDthree]
      _ ≤ 4 * (1 + supportRadius χ) ^ ((1 : ℝ) / 3) :=
        aux_quadraticDensity_eLpNorm_threeHalves_toReal_le χ hχ_compact hχ_nonneg hχ_le_one
      _ = C_quadraticAveragingOperator χ := by
        rw [C_quadraticAveragingOperator]
        norm_num
  calc
    (eLpNorm (quadraticAverage χ f) (3 : ℝ≥0∞) volume).toReal ≤
        (eLpNorm (aux_convolution (fun t : ℝ ↦ (aux_quadraticKernel χ t : ℂ))
          (fun y : ℝ ↦ (‖f₀ y‖ : ℂ))) (3 : ℝ≥0∞) volume).toReal := hmonoreal
    _ ≤ (eLpNorm (aux_quadraticKernel χ) (3 / 2 : ℝ≥0∞) volume).toReal *
        (eLpNorm f₀ (3 / 2 : ℝ≥0∞) volume).toReal := hendpoint.2
    _ = (eLpNorm (aux_quadraticKernel χ) (3 / 2 : ℝ≥0∞) volume).toReal *
        (eLpNorm f (3 / 2 : ℝ≥0∞) volume).toReal := by rw [hf₀norm]
    _ ≤ C_quadraticAveragingOperator χ *
        (eLpNorm f (3 / 2 : ℝ≥0∞) volume).toReal :=
      mul_le_mul_of_nonneg_right hκnorm ENNReal.toReal_nonneg

/--
If \(f_0\in L^\infty(\mathbb R)\) and \(f_1,f_2\in L^{3/2}(\mathbb R)\), then
\[
\mathcal I_\chi(f_0,f_1,f_2)
\leq C_{\ref{lem:quadratic-average},\,\chi}
\lVert f_0\rVert_\infty
\lVert f_1\rVert_{3/2}
\lVert f_2\rVert_{3/2}.
\]
-/
theorem nondecayingLThreeHalvesEndpoint
    (χ : ℝ → ℝ)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (f₀ f₁ f₂ : ℝ → ℂ)
    (hf₀ : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁ : MemLp f₁ (3 / 2 : ℝ≥0∞) volume)
    (hf₂ : MemLp f₂ (3 / 2 : ℝ≥0∞) volume) :
    trilinearFormAbs χ f₀ f₁ f₂ ≤
      C_quadraticAveragingOperator χ *
        (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
          (eLpNorm f₁ (3 / 2 : ℝ≥0∞) volume).toReal *
            (eLpNorm f₂ (3 / 2 : ℝ≥0∞) volume).toReal := by
  let g₀ : ℝ → ℂ := hf₀.1.mk f₀
  let g₁ : ℝ → ℂ := hf₁.1.mk f₁
  let g₂ : ℝ → ℂ := hf₂.1.mk f₂
  have hg₀sm : StronglyMeasurable g₀ := hf₀.1.stronglyMeasurable_mk
  have hg₁sm : StronglyMeasurable g₁ := hf₁.1.stronglyMeasurable_mk
  have hg₂sm : StronglyMeasurable g₂ := hf₂.1.stronglyMeasurable_mk
  have hfg₀ : f₀ =ᵐ[volume] g₀ := hf₀.1.ae_eq_mk
  have hfg₁ : f₁ =ᵐ[volume] g₁ := hf₁.1.ae_eq_mk
  have hfg₂ : f₂ =ᵐ[volume] g₂ := hf₂.1.ae_eq_mk
  have hform : trilinearForm χ f₀ f₁ f₂ = trilinearForm χ g₀ g₁ g₂ := by
    have h0 : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, f₀ z.1 = g₀ z.1 :=
      (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).tendsto_ae hfg₀
    have h1 : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, f₁ (z.1 + z.2) = g₁ (z.1 + z.2) :=
      aux_u3_qmp_add.tendsto_ae hfg₁
    have h2 : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
        f₂ (z.1 + z.2 ^ 2) = g₂ (z.1 + z.2 ^ 2) :=
      aux_u3_qmp_add_sq.tendsto_ae hfg₂
    have hjoint : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
        f₀ z.1 * f₁ (z.1 + z.2) * f₂ (z.1 + z.2 ^ 2) * (χ z.2 : ℂ) =
          g₀ z.1 * g₁ (z.1 + z.2) * g₂ (z.1 + z.2 ^ 2) * (χ z.2 : ℂ) := by
      filter_upwards [h0, h1, h2] with z hz0 hz1 hz2
      rw [hz0, hz1, hz2]
    unfold trilinearForm
    apply integral_congr_ae
    filter_upwards [Measure.ae_ae_of_ae_prod hjoint] with x hx
    apply integral_congr_ae
    filter_upwards [hx] with t ht
    exact ht
  have hg₁lp : MemLp g₁ (3 / 2 : ℝ≥0∞) volume := by
    simpa only [g₁] using MemLp.ae_eq hf₁.1.ae_eq_mk hf₁
  have hg₂lp : MemLp g₂ (3 / 2 : ℝ≥0∞) volume := by
    simpa only [g₂] using MemLp.ae_eq hf₂.1.ae_eq_mk hf₂
  have hg₀bound : ∀ᵐ x : ℝ ∂volume,
      ‖g₀ x‖ₑ ≤ ENNReal.ofReal (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal := by
    have hbase : ∀ᵐ x : ℝ ∂volume, ‖f₀ x‖ₑ ≤ eLpNorm f₀ (∞ : ℝ≥0∞) volume := by
      simpa only [eLpNorm_exponent_top] using
        (ae_le_eLpNormEssSup (f := f₀) (μ := volume))
    filter_upwards [hfg₀, hbase] with x hx hxb
    rw [← hx, ENNReal.ofReal_toReal hf₀.eLpNorm_ne_top]
    exact hxb
  have hχmeas : Measurable χ := hχ_smooth.continuous.measurable
  have hDmeas : Measurable (fun u : ℝ ↦ ENNReal.ofReal (aux_quadraticDensity χ u)) :=
    aux_quadraticDensity_measurable_ennreal χ hχ_smooth
  have hDone : MemLp (aux_quadraticDensity χ) (1 : ℝ≥0∞) volume :=
    aux_quadraticDensity_memLp_one χ hχ_smooth hχ_compact hχ_nonneg hχ_le_one
  have hDthree : MemLp (aux_quadraticDensity χ) (3 / 2 : ℝ≥0∞) volume :=
    aux_quadraticDensity_memLp_threeHalves χ hχ_smooth hχ_compact hχ_nonneg hχ_le_one
  have hκone : MemLp (aux_quadraticKernel χ) (1 : ℝ≥0∞) volume :=
    aux_quadraticKernel_memLp χ 1 hDone
  have hκthree : MemLp (aux_quadraticKernel χ) (3 / 2 : ℝ≥0∞) volume :=
    aux_quadraticKernel_memLp χ (3 / 2 : ℝ≥0∞) hDthree
  let K : ℝ → ℂ := fun t ↦ (aux_quadraticKernel χ t : ℂ)
  let F : ℝ → ℂ := fun y ↦ (‖g₂ y‖ : ℂ)
  let C : ℝ → ℂ := aux_convolution K F
  have hKone : MemLp K (1 : ℝ≥0∞) volume := by
    change MemLp (fun t : ℝ ↦ (aux_quadraticKernel χ t : ℂ)) (1 : ℝ≥0∞) volume
    exact hκone.ofReal
  have hKthree : MemLp K (3 / 2 : ℝ≥0∞) volume := by
    change MemLp (fun t : ℝ ↦ (aux_quadraticKernel χ t : ℂ))
      (3 / 2 : ℝ≥0∞) volume
    exact hκthree.ofReal
  have hFthree : MemLp F (3 / 2 : ℝ≥0∞) volume := by
    change MemLp (fun y : ℝ ↦ (‖g₂ y‖ : ℂ)) (3 / 2 : ℝ≥0∞) volume
    exact hg₂lp.norm.ofReal
  let : Fact (1 ≤ (3 / 2 : ℝ≥0∞)) := ⟨by
    apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
      (Or.inl (by norm_num))).mpr
    norm_num⟩
  let : Fact ((3 / 2 : ℝ≥0∞) ≠ ∞) := ⟨by finiteness⟩
  have hCthree : MemLp C (3 / 2 : ℝ≥0∞) volume := by
    simpa only [C] using aux_convolution_memLp_of_memLp_one K F
      (memLp_one_iff_integrable.mp hKone) hFthree
  have hCendpoint := aux_eLpNorm_convolution_nonneg_real_threeHalves
    (aux_quadraticKernel χ) hκone hκthree
    (aux_quadraticKernel_nonneg χ hχ_nonneg) g₂ hg₂lp
  have hCnorm : eLpNorm C (3 : ℝ≥0∞) volume ≠ ∞ ∧
      (eLpNorm C (3 : ℝ≥0∞) volume).toReal ≤
        (eLpNorm (aux_quadraticKernel χ) (3 / 2 : ℝ≥0∞) volume).toReal *
          (eLpNorm g₂ (3 / 2 : ℝ≥0∞) volume).toReal := by
    simpa only [C, K, F] using hCendpoint
  have hCthreeLp : MemLp C (3 : ℝ≥0∞) volume :=
    ⟨hCthree.1, hCnorm.1.lt_top⟩
  let H : ℝ × ℝ → ℝ≥0∞ := fun z ↦
    ‖g₁ (z.1 + z.2)‖ₑ * ‖g₂ (z.1 + z.2 ^ 2)‖ₑ * ENNReal.ofReal (χ z.2)
  have hHmeas : Measurable H := by
    have h1 : Measurable (fun z : ℝ × ℝ ↦ ‖g₁ (z.1 + z.2)‖ₑ) :=
      hg₁sm.measurable.enorm.comp (continuous_fst.add continuous_snd).measurable
    have h2 : Measurable (fun z : ℝ × ℝ ↦ ‖g₂ (z.1 + z.2 ^ 2)‖ₑ) :=
      hg₂sm.measurable.enorm.comp
        (continuous_fst.add (continuous_snd.pow 2)).measurable
    have h3 : Measurable (fun z : ℝ × ℝ ↦ ENNReal.ofReal (χ z.2)) :=
      ENNReal.continuous_ofReal.measurable.comp (hχmeas.comp continuous_snd.measurable)
    exact (h1.mul h2).mul h3
  have hraw : ‖trilinearForm χ g₀ g₁ g₂‖ₑ ≤
      ENNReal.ofReal (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
        ∫⁻ z : ℝ × ℝ, H z ∂volume.prod volume := by
    calc
      ‖trilinearForm χ g₀ g₁ g₂‖ₑ =
          ‖∫ x : ℝ, ∫ t : ℝ,
            g₀ x * g₁ (x + t) * g₂ (x + t ^ 2) * (χ t : ℂ)‖ₑ := rfl
      _ ≤ ∫⁻ x : ℝ, ‖∫ t : ℝ,
          g₀ x * g₁ (x + t) * g₂ (x + t ^ 2) * (χ t : ℂ)‖ₑ :=
        enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x : ℝ, ∫⁻ t : ℝ,
          ‖g₀ x * g₁ (x + t) * g₂ (x + t ^ 2) * (χ t : ℂ)‖ₑ := by
        apply lintegral_mono
        intro x
        exact enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x : ℝ, ∫⁻ t : ℝ,
          ENNReal.ofReal (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal * H (x, t) := by
        apply lintegral_mono_ae
        filter_upwards [hg₀bound] with x hx
        apply lintegral_mono
        intro t
        have hχE : ‖(χ t : ℂ)‖ₑ = ENNReal.ofReal (χ t) := by
          rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hχ_nonneg t)]
        change ‖g₀ x * g₁ (x + t) * g₂ (x + t ^ 2) * (χ t : ℂ)‖ₑ ≤
          ENNReal.ofReal (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal * H (x, t)
        rw [enorm_mul, enorm_mul, enorm_mul, hχE]
        calc
          ‖g₀ x‖ₑ * ‖g₁ (x + t)‖ₑ * ‖g₂ (x + t ^ 2)‖ₑ *
              ENNReal.ofReal (χ t) =
              ‖g₀ x‖ₑ * (‖g₁ (x + t)‖ₑ * ‖g₂ (x + t ^ 2)‖ₑ *
                ENNReal.ofReal (χ t)) := by ac_rfl
          _ ≤
              ENNReal.ofReal (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
                (‖g₁ (x + t)‖ₑ * ‖g₂ (x + t ^ 2)‖ₑ * ENNReal.ofReal (χ t)) :=
            mul_le_mul_of_nonneg_right hx (by positivity)
          _ = ENNReal.ofReal (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal * H (x, t) := by
            rfl
      _ = ENNReal.ofReal (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
          ∫⁻ z : ℝ × ℝ, H z ∂volume.prod volume := by
        rw [lintegral_lintegral ((measurable_const.mul hHmeas).aemeasurable),
          lintegral_const_mul'' _ hHmeas.aemeasurable]
  let J : ℝ × ℝ → ℝ≥0∞ := fun z ↦
    ‖g₁ z.1‖ₑ * ‖g₂ (z.1 + z.2 ^ 2 - z.2)‖ₑ * ENNReal.ofReal (χ z.2)
  have hJmeas : Measurable J := by
    have h1 : Measurable (fun z : ℝ × ℝ ↦ ‖g₁ z.1‖ₑ) :=
      hg₁sm.measurable.enorm.comp measurable_fst
    have h2 : Measurable (fun z : ℝ × ℝ ↦ ‖g₂ (z.1 + z.2 ^ 2 - z.2)‖ₑ) :=
      hg₂sm.measurable.enorm.comp
        ((continuous_fst.add (continuous_snd.pow 2)).sub continuous_snd).measurable
    have h3 : Measurable (fun z : ℝ × ℝ ↦ ENNReal.ofReal (χ z.2)) :=
      ENNReal.continuous_ofReal.measurable.comp (hχmeas.comp continuous_snd.measurable)
    exact (h1.mul h2).mul h3
  have hHshea : (∫⁻ z : ℝ × ℝ, H z ∂volume.prod volume) =
      ∫⁻ z : ℝ × ℝ, J z ∂volume.prod volume := by
    have hmp := aux_measurePreserving_sub_mul_prod (1 : ℝ)
    calc
      (∫⁻ z : ℝ × ℝ, H z ∂volume.prod volume) =
          ∫⁻ z : ℝ × ℝ, H (z.1 - (1 : ℝ) * z.2, z.2) ∂volume.prod volume := by
        symm
        exact hmp.lintegral_comp hHmeas
      _ = ∫⁻ z : ℝ × ℝ, J z ∂volume.prod volume := by
        apply lintegral_congr
        intro z
        dsimp [H, J]
        have h1 : z.1 - (1 : ℝ) * z.2 + z.2 = z.1 := by ring_nf
        have h2 : z.1 - (1 : ℝ) * z.2 + z.2 ^ 2 = z.1 + z.2 ^ 2 - z.2 := by ring_nf
        rw [h1, h2]
  have hinnermeas (y : ℝ) : Measurable (fun t : ℝ ↦
      ‖g₂ (y + t ^ 2 - t)‖ₑ * ENNReal.ofReal (χ t)) := by
    have harg : Measurable (fun t : ℝ ↦ y + t ^ 2 - t) :=
      ((measurable_const.add (measurable_id.pow measurable_const)).sub measurable_id)
    exact (hg₂sm.measurable.enorm.comp harg).mul
      (ENNReal.continuous_ofReal.measurable.comp hχmeas)
  have hJfactor : (∫⁻ z : ℝ × ℝ, J z ∂volume.prod volume) =
      ∫⁻ y : ℝ, ‖g₁ y‖ₑ *
        ∫⁻ t : ℝ, ‖g₂ (y + t ^ 2 - t)‖ₑ * ENNReal.ofReal (χ t) := by
    calc
      (∫⁻ z : ℝ × ℝ, J z ∂volume.prod volume) =
          ∫⁻ y : ℝ, ∫⁻ t : ℝ, J (y, t) :=
        lintegral_prod J hJmeas.aemeasurable
      _ = ∫⁻ y : ℝ, ‖g₁ y‖ₑ *
          ∫⁻ t : ℝ, ‖g₂ (y + t ^ 2 - t)‖ₑ * ENNReal.ofReal (χ t) := by
        apply lintegral_congr
        intro y
        calc
          (∫⁻ t : ℝ, J (y, t)) = ∫⁻ t : ℝ,
              ‖g₁ y‖ₑ * (‖g₂ (y + t ^ 2 - t)‖ₑ * ENNReal.ofReal (χ t)) := by
            apply lintegral_congr
            intro t
            dsimp [J]
            ac_rfl
          _ = ‖g₁ y‖ₑ *
              ∫⁻ t : ℝ, ‖g₂ (y + t ^ 2 - t)‖ₑ * ENNReal.ofReal (χ t) :=
            lintegral_const_mul _ (hinnermeas y)
  have hB (y : ℝ) : Measurable (fun t : ℝ ↦
      ENNReal.ofReal (‖g₂ (y + (t ^ 2 - t))‖ * χ t)) := by
    have harg : Measurable (fun t : ℝ ↦ y + (t ^ 2 - t)) :=
      measurable_const.add ((measurable_id.pow measurable_const).sub measurable_id)
    exact ENNReal.continuous_ofReal.measurable.comp
      ((hg₂sm.measurable.norm.comp harg).mul hχmeas)
  have hinnerConv (y : ℝ) :
      (∫⁻ t : ℝ, ‖g₂ (y + t ^ 2 - t)‖ₑ * ENNReal.ofReal (χ t)) =
        ∫⁻ s : ℝ, ENNReal.ofReal (aux_quadraticKernel χ s) * ‖g₂ (y - s)‖ₑ := by
    calc
      (∫⁻ t : ℝ, ‖g₂ (y + t ^ 2 - t)‖ₑ * ENNReal.ofReal (χ t)) =
          ∫⁻ t : ℝ, ENNReal.ofReal (‖g₂ (y + (t ^ 2 - t))‖ * χ t) := by
        apply lintegral_congr
        intro t
        rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
        congr 1
        ring_nf
      _ = ∫⁻ s : ℝ, ENNReal.ofReal (aux_quadraticDensity χ (1 / 4 - s)) *
          ‖g₂ (y - s)‖ₑ :=
        aux_lintegral_quadratic_to_convolution χ hχ_nonneg g₂
          hg₂sm.measurable.enorm hDmeas y (hB y)
      _ = ∫⁻ s : ℝ, ENNReal.ofReal (aux_quadraticKernel χ s) * ‖g₂ (y - s)‖ₑ := by
        rfl
  have hsections := aux_ae_integrable_quadraticKernel_sections_of_memLp
    χ g₂ hκone hg₂lp
  have hconvEq : ∀ᵐ y : ℝ ∂volume,
      (∫⁻ s : ℝ, ENNReal.ofReal (aux_quadraticKernel χ s) * ‖g₂ (y - s)‖ₑ) = ‖C y‖ₑ := by
    filter_upwards [hsections] with y hy
    symm
    simpa only [C, K, F, ofReal_norm] using
      aux_enorm_aux_convolution_eq_lintegral_of_nonneg
        (aux_quadraticKernel χ) (fun x : ℝ ↦ ‖g₂ x‖)
        (aux_quadraticKernel_nonneg χ hχ_nonneg) (fun x ↦ norm_nonneg _) y hy
  have hHtoC : (∫⁻ z : ℝ × ℝ, H z ∂volume.prod volume) =
      eLpNorm (fun y : ℝ ↦ g₁ y * C y) (1 : ℝ≥0∞) volume := by
    calc
      (∫⁻ z : ℝ × ℝ, H z ∂volume.prod volume) =
          ∫⁻ z : ℝ × ℝ, J z ∂volume.prod volume := hHshea
      _ = ∫⁻ y : ℝ, ‖g₁ y‖ₑ *
          ∫⁻ t : ℝ, ‖g₂ (y + t ^ 2 - t)‖ₑ * ENNReal.ofReal (χ t) := hJfactor
      _ = ∫⁻ y : ℝ, ‖g₁ y‖ₑ * ‖C y‖ₑ := by
        apply lintegral_congr_ae
        filter_upwards [hconvEq] with y hy
        rw [hinnerConv y, hy]
      _ = eLpNorm (fun y : ℝ ↦ g₁ y * C y) (1 : ℝ≥0∞) volume := by
        rw [eLpNorm_one_eq_lintegral_enorm]
        apply lintegral_congr
        intro y
        rw [enorm_mul]
  let : ENNReal.HolderTriple (3 / 2 : ℝ≥0∞) (3 : ℝ≥0∞) 1 := ⟨by
    rw [ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    calc
      2 * (3 : ℝ≥0∞)⁻¹ + 3⁻¹ = (2 + 1) * 3⁻¹ := by
        rw [add_mul]
        norm_num
      _ = 3 * 3⁻¹ := by norm_num
      _ = (1 : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
        simp⟩
  have hPone : MemLp (fun y : ℝ ↦ g₁ y * C y) (1 : ℝ≥0∞) volume := by
    change MemLp (g₁ * C) (1 : ℝ≥0∞) volume
    exact hCthreeLp.mul hg₁lp
  have hPbound : eLpNorm (fun y : ℝ ↦ g₁ y * C y) (1 : ℝ≥0∞) volume ≤
      eLpNorm g₁ (3 / 2 : ℝ≥0∞) volume * eLpNorm C (3 : ℝ≥0∞) volume := by
    simpa using
      (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hg₁lp.1 hCthreeLp.1 (· * ·) 1
        (Filter.Eventually.of_forall fun y ↦ by simp))
  have hPboundR :
      (eLpNorm (fun y : ℝ ↦ g₁ y * C y) (1 : ℝ≥0∞) volume).toReal ≤
        (eLpNorm g₁ (3 / 2 : ℝ≥0∞) volume).toReal *
          (eLpNorm C (3 : ℝ≥0∞) volume).toReal := by
    have htop : eLpNorm g₁ (3 / 2 : ℝ≥0∞) volume * eLpNorm C (3 : ℝ≥0∞) volume ≠ ∞ :=
      ENNReal.mul_ne_top hg₁lp.eLpNorm_ne_top hCthreeLp.eLpNorm_ne_top
    simpa only [ENNReal.toReal_mul] using ENNReal.toReal_mono htop hPbound
  have hg₁norm : eLpNorm g₁ (3 / 2 : ℝ≥0∞) volume =
      eLpNorm f₁ (3 / 2 : ℝ≥0∞) volume := by
    exact eLpNorm_congr_ae hfg₁.symm
  have hg₂norm : eLpNorm g₂ (3 / 2 : ℝ≥0∞) volume =
      eLpNorm f₂ (3 / 2 : ℝ≥0∞) volume := by
    exact eLpNorm_congr_ae hfg₂.symm
  have hCboundR : (eLpNorm C (3 : ℝ≥0∞) volume).toReal ≤
      (eLpNorm (aux_quadraticKernel χ) (3 / 2 : ℝ≥0∞) volume).toReal *
        (eLpNorm f₂ (3 / 2 : ℝ≥0∞) volume).toReal := by
    rw [← hg₂norm]
    exact hCnorm.2
  have hκnorm : (eLpNorm (aux_quadraticKernel χ) (3 / 2 : ℝ≥0∞) volume).toReal ≤
      C_quadraticAveragingOperator χ := by
    calc
      (eLpNorm (aux_quadraticKernel χ) (3 / 2 : ℝ≥0∞) volume).toReal =
          (eLpNorm (aux_quadraticDensity χ) (3 / 2 : ℝ≥0∞) volume).toReal := by
        rw [aux_quadraticKernel_eLpNorm χ (3 / 2 : ℝ≥0∞) hDthree]
      _ ≤ 4 * (1 + supportRadius χ) ^ ((1 : ℝ) / 3) :=
        aux_quadraticDensity_eLpNorm_threeHalves_toReal_le χ hχ_compact hχ_nonneg hχ_le_one
      _ = C_quadraticAveragingOperator χ := by
        rw [C_quadraticAveragingOperator]
        norm_num
  have hformE : ‖trilinearForm χ f₀ f₁ f₂‖ₑ ≤
      ENNReal.ofReal (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
        eLpNorm (fun y : ℝ ↦ g₁ y * C y) (1 : ℝ≥0∞) volume := by
    calc
      ‖trilinearForm χ f₀ f₁ f₂‖ₑ = ‖trilinearForm χ g₀ g₁ g₂‖ₑ := by rw [hform]
      _ ≤ ENNReal.ofReal (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
          ∫⁻ z : ℝ × ℝ, H z ∂volume.prod volume := hraw
      _ = ENNReal.ofReal (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
          eLpNorm (fun y : ℝ ↦ g₁ y * C y) (1 : ℝ≥0∞) volume := by rw [hHtoC]
  have hformR : trilinearFormAbs χ f₀ f₁ f₂ ≤
      (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
        (eLpNorm (fun y : ℝ ↦ g₁ y * C y) (1 : ℝ≥0∞) volume).toReal := by
    have htop : ENNReal.ofReal (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
        eLpNorm (fun y : ℝ ↦ g₁ y * C y) (1 : ℝ≥0∞) volume ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPone.eLpNorm_ne_top
    have h := ENNReal.toReal_mono htop hformE
    simpa [trilinearFormAbs, enorm_eq_nnnorm] using h
  calc
    trilinearFormAbs χ f₀ f₁ f₂ ≤
        (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
          (eLpNorm (fun y : ℝ ↦ g₁ y * C y) (1 : ℝ≥0∞) volume).toReal := hformR
    _ ≤ (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
        ((eLpNorm g₁ (3 / 2 : ℝ≥0∞) volume).toReal *
          (eLpNorm C (3 : ℝ≥0∞) volume).toReal) := by
      gcongr
    _ = (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
        ((eLpNorm f₁ (3 / 2 : ℝ≥0∞) volume).toReal *
          (eLpNorm C (3 : ℝ≥0∞) volume).toReal) := by rw [hg₁norm]
    _ ≤ (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
        ((eLpNorm f₁ (3 / 2 : ℝ≥0∞) volume).toReal *
          ((eLpNorm (aux_quadraticKernel χ) (3 / 2 : ℝ≥0∞) volume).toReal *
            (eLpNorm f₂ (3 / 2 : ℝ≥0∞) volume).toReal)) := by
      gcongr
    _ ≤ (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
        ((eLpNorm f₁ (3 / 2 : ℝ≥0∞) volume).toReal *
          (C_quadraticAveragingOperator χ *
            (eLpNorm f₂ (3 / 2 : ℝ≥0∞) volume).toReal)) := by
      gcongr
    _ = C_quadraticAveragingOperator χ *
        (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
          (eLpNorm f₁ (3 / 2 : ℝ≥0∞) volume).toReal *
            (eLpNorm f₂ (3 / 2 : ℝ≥0∞) volume).toReal := by ring

/-- The submodule of bounded, compactly supported simple functions on
\(\mathbb R\).  A simple function is bounded because its range is finite; the
predicate records the compact-support condition in
\(\label{prop:special-interpolation}\). -/
def compactlySupportedSimpleSubmodule : Submodule ℂ (SimpleFunc ℝ ℂ) where
  carrier := {f | HasCompactSupport (f : ℝ → ℂ)}
  zero_mem' := by
    simpa using (HasCompactSupport.zero : HasCompactSupport (0 : ℝ → ℂ))
  add_mem' := by
    intro f g hf hg
    change HasCompactSupport ((f + g : SimpleFunc ℝ ℂ) : ℝ → ℂ)
    simpa only [SimpleFunc.coe_add, Pi.add_apply] using hf.add hg
  smul_mem' := by
    intro c f hf
    change HasCompactSupport ((c • f : SimpleFunc ℝ ℂ) : ℝ → ℂ)
    convert hf.smul_left (f := fun _ : ℝ ↦ c) using 1
    ext x
    change c * f x = (fun _ : ℝ ↦ c) x * f x
    rfl

/-- The source domain of `specialBilinearInterpolation`. -/
abbrev CompactSimple : Type := compactlySupportedSimpleSubmodule

/-- A compactly supported simple function is an `L²` function. -/
theorem compactSimpleMemLpTwo (f : CompactSimple) :
    MemLp (f.1 : ℝ → ℂ) (2 : ℝ≥0∞) volume := by
  obtain ⟨C, hC⟩ := (f.1.map (fun z : ℂ ↦ ‖z‖)).exists_forall_le
  refine f.2.memLp_of_bound f.1.aestronglyMeasurable C ?_
  exact Filter.Eventually.of_forall fun x ↦ by simpa using hC x

/-- The canonical embedding of source-domain functions into `L²`. -/
noncomputable def compactSimpleToLpTwo (f : CompactSimple) :
    Lp (α := ℝ) ℂ 2 volume :=
  (compactSimpleMemLpTwo f).toLp (f.1 : ℝ → ℂ)

/-- Compactly supported simple approximation used in
`\label{prop:special-interpolation}` and `specialBilinearInterpolation`. -/
noncomputable def aux_compactSimpleApprox (g : ℝ → ℂ) (hg : Measurable g) (n : ℕ) :
    SimpleFunc ℝ ℂ :=
  (SimpleFunc.approxOn g hg (range g ∪ {0}) 0 (by simp) n).restrict (tsupport g)

/-- The approximation in `aux_compactSimpleApprox` has compact support, as
needed for `\label{prop:special-interpolation}` and `specialBilinearInterpolation`. -/
theorem aux_compactSimpleApprox_hasCompactSupport (g : ℝ → ℂ) (hg : Measurable g)
    (hgc : HasCompactSupport g) (n : ℕ) :
    HasCompactSupport (aux_compactSimpleApprox g hg n : ℝ → ℂ) := by
  apply HasCompactSupport.of_support_subset_isCompact hgc
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxt
  apply hx
  let a : SimpleFunc ℝ ℂ :=
    SimpleFunc.approxOn g hg (range g ∪ {0}) 0 (by simp) n
  have hrestrict := congr_fun
    (SimpleFunc.coe_restrict a (isClosed_tsupport g).measurableSet) x
  change (a.restrict (tsupport g)) x = 0
  rw [hrestrict, Set.indicator_of_notMem hxt]

/-- The compact-simple source element associated to the approximation for
`\label{prop:special-interpolation}` and `specialBilinearInterpolation`. -/
noncomputable def aux_compactSimpleApproxCS (g : ℝ → ℂ) (hg : Measurable g)
    (hgc : HasCompactSupport g) (n : ℕ) : CompactSimple :=
  ⟨aux_compactSimpleApprox g hg n, aux_compactSimpleApprox_hasCompactSupport g hg hgc n⟩

/-- Rewrites the error of the compact-simple approximation as a support cutoff,
for `\label{prop:special-interpolation}` and `specialBilinearInterpolation`. -/
theorem aux_compactSimpleApprox_sub_eq_indicator (g : ℝ → ℂ) (hg : Measurable g) (n : ℕ) :
    (aux_compactSimpleApprox g hg n : ℝ → ℂ) - g =
      (tsupport g).indicator
        ((SimpleFunc.approxOn g hg (range g ∪ {0}) 0 (by simp) n : ℝ → ℂ) - g) := by
  ext x
  let a : SimpleFunc ℝ ℂ :=
    SimpleFunc.approxOn g hg (range g ∪ {0}) 0 (by simp) n
  have hrestrict := congr_fun
    (SimpleFunc.coe_restrict a (isClosed_tsupport g).measurableSet) x
  by_cases hx : x ∈ tsupport g
  · change (a.restrict (tsupport g)) x - g x =
      (tsupport g).indicator ((a : ℝ → ℂ) - g) x
    rw [hrestrict, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    rfl
  · have hgzero : g x = 0 := by
      by_contra hne
      exact hx (subset_tsupport g (Function.mem_support.mpr hne))
    change (a.restrict (tsupport g)) x - g x =
      (tsupport g).indicator ((a : ℝ → ℂ) - g) x
    rw [hrestrict, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, hgzero]
    simp

/-- The compact-simple approximations converge in `L²`, supplying the density
step in `\label{prop:special-interpolation}` and `specialBilinearInterpolation`. -/
theorem aux_tendsto_compactSimpleApprox_toLpTwo (g : ℝ → ℂ) (hg : Measurable g)
    (hgc : HasCompactSupport g) (hgm : MemLp g (2 : ℝ≥0∞) volume) :
    Filter.Tendsto (fun n => compactSimpleToLpTwo (aux_compactSimpleApproxCS g hg hgc n))
      Filter.atTop (𝓝 (hgm.toLp g)) := by
  have hbase : Filter.Tendsto
      (fun n => eLpNorm
        ((SimpleFunc.approxOn g hg (range g ∪ {0}) 0 (by simp) n : ℝ → ℂ) - g)
        (2 : ℝ≥0∞) volume)
      Filter.atTop (𝓝 0) :=
    SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm (p := (2 : ℝ≥0∞)) ENNReal.ofNat_ne_top hg hgm.2
  have hcut : Filter.Tendsto
      (fun n => eLpNorm ((aux_compactSimpleApprox g hg n : ℝ → ℂ) - g) (2 : ℝ≥0∞) volume)
      Filter.atTop (𝓝 0) := by
    refine Filter.Tendsto.squeeze
      (f := fun n : ℕ => eLpNorm ((aux_compactSimpleApprox g hg n : ℝ → ℂ) - g)
        (2 : ℝ≥0∞) volume)
      tendsto_const_nhds hbase ?_ ?_
    · intro n
      exact bot_le
    · intro n
      change eLpNorm ((aux_compactSimpleApprox g hg n : ℝ → ℂ) - g) (2 : ℝ≥0∞) volume ≤
        eLpNorm
          ((SimpleFunc.approxOn g hg (range g ∪ {0}) 0 (by simp) n : ℝ → ℂ) - g)
          (2 : ℝ≥0∞) volume
      rw [aux_compactSimpleApprox_sub_eq_indicator]
      exact eLpNorm_indicator_le _
  let fseq : ℕ → ℝ → ℂ := fun n x => (aux_compactSimpleApproxCS g hg hgc n).1 x
  have hfseq : ∀ n : ℕ, MemLp (fseq n) (2 : ℝ≥0∞) volume :=
    fun n => compactSimpleMemLpTwo (aux_compactSimpleApproxCS g hg hgc n)
  have hcut' : Filter.Tendsto
      (fun n => eLpNorm (fseq n - g) (2 : ℝ≥0∞) volume) Filter.atTop (𝓝 0) := by
    simpa [fseq, aux_compactSimpleApproxCS] using hcut
  have hmain := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fseq hfseq g hgm).mpr hcut'
  simpa [fseq, aux_compactSimpleApproxCS, compactSimpleToLpTwo] using hmain

/-- The compact-simple functions have dense image in `L²`, as required to
extend the form in `\label{prop:special-interpolation}` and `specialBilinearInterpolation`. -/
theorem aux_compactSimpleToLpTwo_denseRange :
    DenseRange compactSimpleToLpTwo := by
  let D : Set (Lp (α := ℝ) ℂ 2 volume) :=
    {f | ∃ g : ℝ → ℂ, (f : ℝ → ℂ) =ᵐ[volume] g ∧
      HasCompactSupport g ∧ ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g}
  have hD : Dense D := by
    simpa [D] using
      (Lp.dense_hasCompactSupport_contDiff (E := ℝ) (F := ℂ) (μ := volume)
        (p := (2 : ℝ≥0∞)) ENNReal.ofNat_ne_top)
  change ∀ x : Lp (α := ℝ) ℂ 2 volume,
    x ∈ closure (Set.range compactSimpleToLpTwo)
  apply isClosed_property hD.denseRange_val isClosed_closure
  intro x
  rcases x.2 with ⟨g, hxg, hgc, hcont⟩
  have hgm : MemLp g (2 : ℝ≥0∞) volume :=
    hcont.continuous.memLp_of_hasCompactSupport hgc
  have hxEq : x.1 = hgm.toLp g := by
    rw [← Lp.toLp_coeFn x.1 (Lp.memLp x.1)]
    exact (MemLp.toLp_eq_toLp_iff _ _).2 hxg
  rw [hxEq]
  exact mem_closure_of_tendsto
    (aux_tendsto_compactSimpleApprox_toLpTwo g hcont.continuous.measurable hgc hgm)
    (Filter.Eventually.of_forall fun n => Set.mem_range_self _)

/-- The complex-linear compact-simple-to-`L²` embedding used by
`\label{prop:special-interpolation}` and `specialBilinearInterpolation`. -/
noncomputable def aux_compactSimpleToLpTwoCLM :
    CompactSimple →ₗ[ℂ] Lp (α := ℝ) ℂ 2 volume where
  toFun := compactSimpleToLpTwo
  map_add' f g := by
    calc
      compactSimpleToLpTwo (f + g) =
          ((compactSimpleMemLpTwo f).add (compactSimpleMemLpTwo g)).toLp
            ((f.1 : ℝ → ℂ) + (g.1 : ℝ → ℂ)) := by
        apply MemLp.toLp_congr
        filter_upwards [] with x
        rfl
      _ = compactSimpleToLpTwo f + compactSimpleToLpTwo g :=
        MemLp.toLp_add (compactSimpleMemLpTwo f) (compactSimpleMemLpTwo g)
  map_smul' c f := by
    calc
      compactSimpleToLpTwo (c • f) =
          ((compactSimpleMemLpTwo f).const_smul c).toLp (c • (f.1 : ℝ → ℂ)) := by
        apply MemLp.toLp_congr
        filter_upwards [] with x
        rfl
      _ = c • compactSimpleToLpTwo f :=
        MemLp.toLp_const_smul c (compactSimpleMemLpTwo f)

/-- Evaluation of the linear embedding agrees with `compactSimpleToLpTwo` in
`\label{prop:special-interpolation}` and `specialBilinearInterpolation`. -/
lemma aux_compactSimpleToLpTwoCLM_apply (f : CompactSimple) :
    aux_compactSimpleToLpTwoCLM f = compactSimpleToLpTwo f := rfl

/-- The complex-linear compact-simple-to-`L²` embedding has dense range for
`\label{prop:special-interpolation}` and `specialBilinearInterpolation`. -/
theorem aux_compactSimpleToLpTwoCLM_denseRange :
    DenseRange aux_compactSimpleToLpTwoCLM := by
  change DenseRange compactSimpleToLpTwo
  exact aux_compactSimpleToLpTwo_denseRange

/-- Extends the complex bilinear form in
`specialBilinearInterpolation` along a dense complex-linear embedding, while
preserving its product norm bound (cf. \(\label{prop:special-interpolation}\)). -/
lemma aux_extend_bilinear_of_dense
    {E H : Type*}
    [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (e : E →ₗ[ℂ] H) (hdense : DenseRange e)
    (T : E →ₗ[ℂ] E →ₗ[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ f g : E, ‖T f g‖ ≤ C * ‖e f‖ * ‖e g‖) :
    ∃ T₂ : H →L[ℂ] H →L[ℂ] ℂ,
      (∀ f g : E, T₂ (e f) (e g) = T f g) ∧
      ∀ f g : H, ‖T₂ f g‖ ≤ C * ‖f‖ * ‖g‖ := by
  let F : E →ₗ[ℂ] H →L[ℂ] ℂ :=
    { toFun := fun f ↦ (T f).extendOfNorm e
      map_add' := by
        intro f g
        ext x
        refine hdense.induction ?_ (isClosed_eq (by fun_prop) (by fun_prop)) x
        rintro _ ⟨y, rfl⟩
        simp only [add_apply]
        rw [LinearMap.extendOfNorm_eq hdense
          ⟨C * ‖e (f + g)‖, fun z ↦ by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hT (f + g) z⟩]
        rw [LinearMap.extendOfNorm_eq hdense
          ⟨C * ‖e f‖, fun z ↦ by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hT f z⟩]
        rw [LinearMap.extendOfNorm_eq hdense
          ⟨C * ‖e g‖, fun z ↦ by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hT g z⟩]
        simp
      map_smul' := by
        intro c f
        ext x
        refine hdense.induction ?_ (isClosed_eq (by fun_prop) (by fun_prop)) x
        rintro _ ⟨y, rfl⟩
        simp only [smul_apply, RingHom.id_apply]
        rw [LinearMap.extendOfNorm_eq hdense
          ⟨C * ‖e (c • f)‖, fun z ↦ by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hT (c • f) z⟩]
        rw [LinearMap.extendOfNorm_eq hdense
          ⟨C * ‖e f‖, fun z ↦ by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hT f z⟩]
        simp }
  have hF : ∀ f : E, ‖F f‖ ≤ C * ‖e f‖ := by
    intro f
    apply (F f).opNorm_le_bound (mul_nonneg hC (norm_nonneg _))
    intro x
    exact LinearMap.norm_extendOfNorm_apply_le hdense (C * ‖e f‖)
      (fun z ↦ by simpa [mul_assoc, mul_left_comm, mul_comm] using hT f z) x
  let T₂ : H →L[ℂ] H →L[ℂ] ℂ := F.extendOfNorm e
  refine ⟨T₂, ?_, ?_⟩
  · intro f g
    change F.extendOfNorm e (e f) (e g) = T f g
    rw [LinearMap.extendOfNorm_eq hdense ⟨C, hF⟩]
    exact LinearMap.extendOfNorm_eq hdense
      ⟨C * ‖e f‖, fun z ↦ by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hT f z⟩ g
  · intro f g
    calc
      ‖T₂ f g‖ ≤ ‖T₂ f‖ * ‖g‖ := (T₂ f).le_opNorm g
      _ ≤ (C * ‖f‖) * ‖g‖ := by
        gcongr
        exact LinearMap.norm_extendOfNorm_apply_le hdense C hF f
      _ = C * ‖f‖ * ‖g‖ := by ring

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_three_lines_at_three_quarters
    (F : ℂ → ℂ) (a b : ℝ)
    (hF : DiffContOnCl ℂ F
      (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ F) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (hleft : ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ), ‖F z‖ ≤ a)
    (hright : ∀ z ∈ Complex.re ⁻¹' ({1} : Set ℝ), ‖F z‖ ≤ b) :
    ‖F ((3 / 4 : ℝ) : ℂ)‖ ≤ a ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) := by
  have hz : ((3 / 4 : ℝ) : ℂ) ∈
      Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp [Complex.HadamardThreeLines.verticalClosedStrip]
    norm_num
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
    F hz hF hB hleft hright
  convert h using 1
  norm_num

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
def aux_scalarFamily (c z : ℂ) : ℂ :=
  if c = 0 then 0 else
    (‖c‖ : ℂ) ^ (((4 : ℂ) / 3) * z) * (c / ‖c‖)

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_differentiable_scalarFamily (c : ℂ) :
    Differentiable ℂ (aux_scalarFamily c) := by
  unfold aux_scalarFamily
  split_ifs with hc
  · exact differentiable_zero
  · apply Differentiable.mul
    · apply Differentiable.const_cpow (differentiable_id.const_mul _)
      left
      exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hc)
    · exact differentiable_const _

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_scalarFamily_at_three_quarters (c : ℂ) :
    aux_scalarFamily c ((3 / 4 : ℝ) : ℂ) = c := by
  unfold aux_scalarFamily
  by_cases hc : c = 0
  · simp [hc]
  · rw [ite_eq_right hc]
    have hnorm : (‖c‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hc)
    have hexp : ((4 : ℂ) / 3) * ((3 / 4 : ℝ) : ℂ) = 1 := by norm_num
    rw [hexp, Complex.cpow_one]
    field_simp

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_norm_scalarFamily_of_ne_zero (c z : ℂ) (hc : c ≠ 0) :
    ‖aux_scalarFamily c z‖ = ‖c‖ ^ ((((4 : ℂ) / 3) * z).re) := by
  unfold aux_scalarFamily
  rw [ite_eq_right hc, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr hc)]
  have hdiv : ‖c / (‖c‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr hc)]
  rw [hdiv, mul_one]

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_norm_scalarFamily_le_max (c z : ℂ)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) :
    ‖aux_scalarFamily c z‖ ≤ max 1 (‖c‖ ^ (4 / 3 : ℝ)) := by
  by_cases hc : c = 0
  · simp [hc, aux_scalarFamily]
  rw [aux_norm_scalarFamily_of_ne_zero c z hc]
  have heq : ((((4 : ℂ) / 3) * z).re : ℝ) = (4 / 3 : ℝ) * z.re := by
    simp [Complex.mul_re]
  have he0 : 0 ≤ (((4 : ℂ) / 3) * z).re := by
    rw [heq]
    positivity
  have he1 : (((4 : ℂ) / 3) * z).re ≤ (4 / 3 : ℝ) := by
    rw [heq]
    nlinarith
  by_cases hbase : 1 ≤ ‖c‖
  · exact (Real.rpow_le_rpow_of_exponent_le hbase he1).trans (le_max_right _ _)
  · have hbase' : ‖c‖ ≤ 1 := le_of_lt (lt_of_not_ge hbase)
    exact (Real.rpow_le_one (norm_nonneg _) hbase' he0).trans (le_max_left _ _)

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_norm_scalarFamily_of_re_eq_zero (c z : ℂ) (hz : z.re = 0) :
    ‖aux_scalarFamily c z‖ ≤ 1 := by
  unfold aux_scalarFamily
  by_cases hc : c = 0
  · simp [hc]
  · rw [ite_eq_right hc, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr hc)]
    have hpow : ((((4 : ℂ) / 3) * z).re : ℝ) = 0 := by
      simp [Complex.mul_re, hz]
    rw [hpow, Real.rpow_zero]
    have hdiv : ‖c / (‖c‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr hc)]
    rw [hdiv]
    norm_num

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_norm_scalarFamily_of_re_eq_one (c z : ℂ) (hz : z.re = 1) :
    ‖aux_scalarFamily c z‖ = ‖c‖ ^ (4 / 3 : ℝ) := by
  unfold aux_scalarFamily
  by_cases hc : c = 0
  · simp [hc]
  · rw [ite_eq_right hc, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr hc)]
    have hpow : ((((4 : ℂ) / 3) * z).re : ℝ) = 4 / 3 := by
      simp [Complex.mul_re, hz]
    rw [hpow]
    have hdiv : ‖c / (‖c‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr hc)]
    rw [hdiv, mul_one]

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
def aux_compactSimpleFamily (f : Auto.CompactSimple) (z : ℂ) : Auto.CompactSimple :=
  ⟨f.1.map fun c ↦ aux_scalarFamily c z, by
    have h := f.2.comp_left (g := fun c ↦ aux_scalarFamily c z) (by simp [aux_scalarFamily])
    change HasCompactSupport
      ((f.1.map fun c ↦ aux_scalarFamily c z : SimpleFunc ℝ ℂ) : ℝ → ℂ)
    simpa only [SimpleFunc.coe_map, Function.comp_apply] using h⟩

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
@[simp]
theorem aux_compactSimpleFamily_apply (f : Auto.CompactSimple) (z : ℂ) (x : ℝ) :
    (aux_compactSimpleFamily f z).1 x = aux_scalarFamily (f.1 x) z := rfl

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_compactSimpleFamily_at_three_quarters (f : Auto.CompactSimple) :
    aux_compactSimpleFamily f ((3 / 4 : ℝ) : ℂ) = f := by
  apply Subtype.ext
  apply SimpleFunc.ext
  intro x
  exact aux_scalarFamily_at_three_quarters (f.1 x)

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
def aux_compactSimpleFiber (f : Auto.CompactSimple) (c : ℂ) (hc : c ≠ 0) : Auto.CompactSimple :=
  ⟨(SimpleFunc.const ℝ (1 : ℂ)).restrict (f.1 ⁻¹' {c}), by
    apply f.2.mono
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    by_contra hfx
    have hnot : x ∉ f.1 ⁻¹' ({c} : Set ℂ) := by
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      intro hxc
      exact hc (hxc.symm.trans hfx)
    rw [SimpleFunc.restrict_apply _ (f.1.measurableSet_fiber c)] at hx
    simp [hnot] at hx⟩

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
@[simp]
theorem aux_compactSimpleFiber_apply (f : Auto.CompactSimple) (c : ℂ) (hc : c ≠ 0) (x : ℝ) :
    (aux_compactSimpleFiber f c hc).1 x =
      Set.indicator (f.1 ⁻¹' ({c} : Set ℂ)) (fun _ : ℝ ↦ (1 : ℂ)) x := by
  simp [aux_compactSimpleFiber, SimpleFunc.restrict_apply, f.1.measurableSet_fiber]
  rfl

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
def aux_compactSimpleFiberAll (f : Auto.CompactSimple) (c : ℂ) : Auto.CompactSimple :=
  if hc : c = 0 then 0 else aux_compactSimpleFiber f c hc

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_compactSimpleFiberAll_apply (f : Auto.CompactSimple) (c : ℂ) (x : ℝ) :
    (aux_compactSimpleFiberAll f c).1 x =
      if c = 0 then 0 else
        Set.indicator (f.1 ⁻¹' ({c} : Set ℂ)) (fun _ : ℝ ↦ (1 : ℂ)) x := by
  by_cases hc : c = 0
  · simp [aux_compactSimpleFiberAll, hc]
  · simp [aux_compactSimpleFiberAll, hc, aux_compactSimpleFiber_apply]

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_simpleFunc_finset_sum_apply {ι : Type*} (s : Finset ι)
    (F : ι → SimpleFunc ℝ ℂ) (x : ℝ) :
    (∑ i ∈ s, F i) x = ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih]

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_compactSimpleFamily_eq_fiber_sum (f : Auto.CompactSimple) (z : ℂ) :
    aux_compactSimpleFamily f z =
      ∑ c ∈ f.1.range, aux_scalarFamily c z • aux_compactSimpleFiberAll f c := by
  classical
  apply Subtype.ext
  apply SimpleFunc.ext
  intro x
  rw [aux_compactSimpleFamily_apply]
  rw [Submodule.coe_sum, aux_simpleFunc_finset_sum_apply]
  change aux_scalarFamily (f.1 x) z =
    ∑ c ∈ f.1.range, aux_scalarFamily c z * (aux_compactSimpleFiberAll f c).1 x
  simp_rw [aux_compactSimpleFiberAll_apply]
  have hxrange : f.1 x ∈ f.1.range := f.1.mem_range_self x
  have hsum :
      (∑ c ∈ f.1.range,
        aux_scalarFamily c z *
          (if c = 0 then 0 else
            Set.indicator (f.1 ⁻¹' ({c} : Set ℂ)) (fun _ : ℝ ↦ (1 : ℂ)) x)) =
        aux_scalarFamily (f.1 x) z := by
    rw [Finset.sum_eq_single (f.1 x)]
    · by_cases hzero : f.1 x = 0
      · simp [hzero, aux_scalarFamily]
      · simp [hzero]
    · intro c hc hcx
      have hnot : x ∉ f.1 ⁻¹' ({c} : Set ℂ) := by
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact fun h ↦ hcx h.symm
      simp [hnot]
    · intro hnot
      exact (hnot hxrange).elim
  exact hsum.symm

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_bilinear_family_eq_finite_sum
    (T : Auto.CompactSimple →ₗ[ℂ] Auto.CompactSimple →ₗ[ℂ] ℂ)
    (f g : Auto.CompactSimple) (z : ℂ) :
    T (aux_compactSimpleFamily f z) (aux_compactSimpleFamily g z) =
      ∑ c ∈ f.1.range, ∑ d ∈ g.1.range,
        aux_scalarFamily c z * aux_scalarFamily d z *
          T (aux_compactSimpleFiberAll f c) (aux_compactSimpleFiberAll g d) := by
  classical
  rw [aux_compactSimpleFamily_eq_fiber_sum, aux_compactSimpleFamily_eq_fiber_sum]
  simp_rw [map_sum, map_smul]
  simp_rw [LinearMap.sum_apply, LinearMap.smul_apply]
  simp only [smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_eLpNorm_compactSimpleFamily_top_le_one
    (f : Auto.CompactSimple) (z : ℂ) (hz : z.re = 0) :
    (eLpNorm ((aux_compactSimpleFamily f z).1 : ℝ → ℂ) (∞ : ℝ≥0∞) volume).toReal ≤ 1 := by
  have hbound : eLpNorm ((aux_compactSimpleFamily f z).1 : ℝ → ℂ) (∞ : ℝ≥0∞) volume ≤ 1 := by
    rw [eLpNorm_exponent_top]
    change eLpNormEssSup (fun x : ℝ ↦ aux_scalarFamily (f.1 x) z) volume ≤ (1 : ℝ≥0∞)
    simpa using eLpNormEssSup_le_of_ae_bound
      (Filter.Eventually.of_forall fun x ↦ aux_norm_scalarFamily_of_re_eq_zero (f.1 x) z hz)
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top hbound

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_eLpNorm_compactSimpleFamily_threeHalves_of_re_eq_one
    (f : Auto.CompactSimple) (z : ℂ) (hz : z.re = 1) :
    eLpNorm ((aux_compactSimpleFamily f z).1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume =
      eLpNorm (f.1 : ℝ → ℂ) (2 : ℝ≥0∞) volume ^ (4 / 3 : ℝ) := by
  have hpoint : (fun x : ℝ ↦ ‖(aux_compactSimpleFamily f z).1 x‖) =
      fun x ↦ ‖f.1 x‖ ^ (4 / 3 : ℝ) := by
    ext x
    exact aux_norm_scalarFamily_of_re_eq_one (f.1 x) z hz
  calc
    eLpNorm ((aux_compactSimpleFamily f z).1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume =
        eLpNorm (fun x : ℝ ↦ ‖(aux_compactSimpleFamily f z).1 x‖) (3 / 2 : ℝ≥0∞) volume :=
      (eLpNorm_norm _).symm
    _ = eLpNorm (fun x : ℝ ↦ ‖f.1 x‖ ^ (4 / 3 : ℝ)) (3 / 2 : ℝ≥0∞) volume := by
      rw [hpoint]
    _ = eLpNorm (f.1 : ℝ → ℂ)
        ((3 / 2 : ℝ≥0∞) * ENNReal.ofReal (4 / 3 : ℝ)) volume ^ (4 / 3 : ℝ) :=
      eLpNorm_norm_rpow _ (by norm_num)
    _ = eLpNorm (f.1 : ℝ → ℂ) (2 : ℝ≥0∞) volume ^ (4 / 3 : ℝ) := by
      have hfourThirds : ENNReal.ofReal (4 / 3 : ℝ) = (4 / 3 : ℝ≥0∞) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
        norm_num
      have hp : (3 / 2 : ℝ≥0∞) * ENNReal.ofReal (4 / 3 : ℝ) = 2 := by
        rw [hfourThirds, div_eq_mul_inv, div_eq_mul_inv]
        calc
          3 * (2 : ℝ≥0∞)⁻¹ * (4 * (3 : ℝ≥0∞)⁻¹) =
              (3 * (3 : ℝ≥0∞)⁻¹) * ((2 : ℝ≥0∞)⁻¹ * 4) := by ac_rfl
          _ = 1 * ((2 : ℝ≥0∞)⁻¹ * 4) := by
            rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
          _ = 2 := by
            rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num]
            calc
              1 * ((2 : ℝ≥0∞)⁻¹ * (2 * 2)) = 1 * ((2 : ℝ≥0∞)⁻¹ * 2) * 2 := by ac_rfl
              _ = 1 * 1 * 2 := by
                rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
              _ = 2 := by simp
      rw [hp]

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_normalized_special_interpolation_core
    (T : Auto.CompactSimple →ₗ[ℂ] Auto.CompactSimple →ₗ[ℂ] ℂ)
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (_hA₁ : 0 ≤ A₁)
    (hInfinity : ∀ f g : Auto.CompactSimple,
      ‖T f g‖ ≤ A₀ *
        (eLpNorm (f.1 : ℝ → ℂ) (∞ : ℝ≥0∞) volume).toReal *
          (eLpNorm (g.1 : ℝ → ℂ) (∞ : ℝ≥0∞) volume).toReal)
    (hThreeHalves : ∀ f g : Auto.CompactSimple,
      ‖T f g‖ ≤ A₁ *
        (eLpNorm (f.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal *
          (eLpNorm (g.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal)
    (f g : Auto.CompactSimple)
    (hf : (eLpNorm (f.1 : ℝ → ℂ) (2 : ℝ≥0∞) volume).toReal = 1)
    (hg : (eLpNorm (g.1 : ℝ → ℂ) (2 : ℝ≥0∞) volume).toReal = 1)
    (hF : DiffContOnCl ℂ (fun z ↦ T (aux_compactSimpleFamily f z) (aux_compactSimpleFamily g z))
      (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hB : BddAbove
      ((norm ∘ fun z ↦ T (aux_compactSimpleFamily f z) (aux_compactSimpleFamily g z)) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1)) :
    ‖T f g‖ ≤ A₀ ^ (1 / 4 : ℝ) * A₁ ^ (3 / 4 : ℝ) := by
  have hleft : ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ),
      ‖T (aux_compactSimpleFamily f z) (aux_compactSimpleFamily g z)‖ ≤ A₀ := by
    intro z hz
    have hfn := aux_eLpNorm_compactSimpleFamily_top_le_one f z hz
    have hgn := aux_eLpNorm_compactSimpleFamily_top_le_one g z hz
    calc
      ‖T (aux_compactSimpleFamily f z) (aux_compactSimpleFamily g z)‖ ≤
          A₀ *
            (eLpNorm ((aux_compactSimpleFamily f z).1 : ℝ → ℂ) (∞ : ℝ≥0∞) volume).toReal *
              (eLpNorm ((aux_compactSimpleFamily g z).1 : ℝ → ℂ) (∞ : ℝ≥0∞) volume).toReal :=
        hInfinity _ _
      _ ≤ A₀ * 1 * 1 := by gcongr
      _ = A₀ := by ring
  have hright : ∀ z ∈ Complex.re ⁻¹' ({1} : Set ℝ),
      ‖T (aux_compactSimpleFamily f z) (aux_compactSimpleFamily g z)‖ ≤ A₁ := by
    intro z hz
    have hfn :
        (eLpNorm ((aux_compactSimpleFamily f z).1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal = 1 := by
      rw [aux_eLpNorm_compactSimpleFamily_threeHalves_of_re_eq_one f z hz,
        ← ENNReal.toReal_rpow, hf]
      norm_num
    have hgn :
        (eLpNorm ((aux_compactSimpleFamily g z).1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal = 1 := by
      rw [aux_eLpNorm_compactSimpleFamily_threeHalves_of_re_eq_one g z hz,
        ← ENNReal.toReal_rpow, hg]
      norm_num
    calc
      ‖T (aux_compactSimpleFamily f z) (aux_compactSimpleFamily g z)‖ ≤
          A₁ *
            (eLpNorm ((aux_compactSimpleFamily f z).1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal *
              (eLpNorm ((aux_compactSimpleFamily g z).1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal :=
        hThreeHalves _ _
      _ = A₁ := by rw [hfn, hgn]; ring
  have hinterp := aux_three_lines_at_three_quarters
    (fun z ↦ T (aux_compactSimpleFamily f z) (aux_compactSimpleFamily g z)) A₀ A₁ hF hB hleft hright
  simpa only [aux_compactSimpleFamily_at_three_quarters] using hinterp

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_differentiable_finset_bilinear_family
    {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (K : ι → κ → ℂ) (u : ι → ℂ) (v : κ → ℂ) :
    Differentiable ℂ (fun z : ℂ ↦
      ∑ i ∈ s, ∑ j ∈ t, K i j * aux_scalarFamily (u i) z * aux_scalarFamily (v j) z) := by
  classical
  have h : Differentiable ℂ (∑ i ∈ s, ∑ j ∈ t, fun z ↦
      K i j * aux_scalarFamily (u i) z * aux_scalarFamily (v j) z) := by
    apply Differentiable.sum
    intro i hi
    apply Differentiable.sum
    intro j hj
    exact ((differentiable_const _).mul (aux_differentiable_scalarFamily _)).mul
      (aux_differentiable_scalarFamily _)
  convert h using 1
  ext z
  simp

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_bddAbove_finite_bilinear_family
    {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (K : ι → κ → ℂ) (u : ι → ℂ) (v : κ → ℂ) :
    BddAbove ((norm ∘ (fun z : ℂ ↦
      ∑ i ∈ s, ∑ j ∈ t, K i j * aux_scalarFamily (u i) z * aux_scalarFamily (v j) z)) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  classical
  let Bu : ι → ℝ := fun i ↦ max 1 (‖u i‖ ^ (4 / 3 : ℝ))
  let Bv : κ → ℝ := fun j ↦ max 1 (‖v j‖ ^ (4 / 3 : ℝ))
  let B : ℝ := ∑ i ∈ s, ∑ j ∈ t, ‖K i j‖ * Bu i * Bv j
  rw [bddAbove_def]
  refine ⟨B, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  have hz0 : 0 ≤ z.re := hz.1
  have hz1 : z.re ≤ 1 := hz.2
  have hterm : ∀ i ∈ s, ∀ j ∈ t,
      ‖K i j * aux_scalarFamily (u i) z * aux_scalarFamily (v j) z‖ ≤
        ‖K i j‖ * Bu i * Bv j := by
    intro i hi j hj
    rw [norm_mul, norm_mul]
    dsimp only [Bu, Bv]
    gcongr
    · exact aux_norm_scalarFamily_le_max (u i) z hz0 hz1
    · exact aux_norm_scalarFamily_le_max (v j) z hz0 hz1
  calc
    ‖∑ i ∈ s, ∑ j ∈ t, K i j * aux_scalarFamily (u i) z * aux_scalarFamily (v j) z‖ ≤
        ∑ i ∈ s, ∑ j ∈ t, ‖K i j * aux_scalarFamily (u i) z * aux_scalarFamily (v j) z‖ := by
      calc
        ‖∑ i ∈ s, ∑ j ∈ t, K i j * aux_scalarFamily (u i) z * aux_scalarFamily (v j) z‖ ≤
            ∑ i ∈ s, ‖∑ j ∈ t, K i j * aux_scalarFamily (u i) z * aux_scalarFamily (v j) z‖ :=
          norm_sum_le s _
        _ ≤ ∑ i ∈ s, ∑ j ∈ t, ‖K i j * aux_scalarFamily (u i) z * aux_scalarFamily (v j) z‖ := by
          gcongr with i hi
          exact norm_sum_le t _
    _ ≤ B := by
      dsimp only [B]
      gcongr with i hi j hj
      exact hterm i hi j hj

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_bddAbove_bilinear_family
    (T : Auto.CompactSimple →ₗ[ℂ] Auto.CompactSimple →ₗ[ℂ] ℂ)
    (f g : Auto.CompactSimple) :
    BddAbove ((norm ∘ fun z ↦ T (aux_compactSimpleFamily f z) (aux_compactSimpleFamily g z)) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  have hEq : (fun z ↦ T (aux_compactSimpleFamily f z) (aux_compactSimpleFamily g z)) =
      (fun z ↦ ∑ c ∈ f.1.range, ∑ d ∈ g.1.range,
        aux_scalarFamily c z * aux_scalarFamily d z *
          T (aux_compactSimpleFiberAll f c) (aux_compactSimpleFiberAll g d)) := by
    funext z
    exact aux_bilinear_family_eq_finite_sum T f g z
  rw [hEq]
  have hSumEq :
      (fun z : ℂ ↦ ∑ c ∈ f.1.range, ∑ d ∈ g.1.range,
        aux_scalarFamily c z * aux_scalarFamily d z *
          T (aux_compactSimpleFiberAll f c) (aux_compactSimpleFiberAll g d)) =
      (fun z : ℂ ↦ ∑ c ∈ f.1.range, ∑ d ∈ g.1.range,
        T (aux_compactSimpleFiberAll f c) (aux_compactSimpleFiberAll g d) *
          aux_scalarFamily c z * aux_scalarFamily d z) := by
    funext z
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hSumEq]
  exact aux_bddAbove_finite_bilinear_family f.1.range g.1.range
    (fun c d ↦ T (aux_compactSimpleFiberAll f c) (aux_compactSimpleFiberAll g d)) id id

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_diffContOnCl_bilinear_family
    (T : Auto.CompactSimple →ₗ[ℂ] Auto.CompactSimple →ₗ[ℂ] ℂ)
    (f g : Auto.CompactSimple) :
    DiffContOnCl ℂ (fun z ↦ T (aux_compactSimpleFamily f z) (aux_compactSimpleFamily g z))
      (Complex.HadamardThreeLines.verticalStrip 0 1) := by
  have hEq : (fun z ↦ T (aux_compactSimpleFamily f z) (aux_compactSimpleFamily g z)) =
      (fun z ↦ ∑ c ∈ f.1.range, ∑ d ∈ g.1.range,
        aux_scalarFamily c z * aux_scalarFamily d z *
          T (aux_compactSimpleFiberAll f c) (aux_compactSimpleFiberAll g d)) := by
    funext z
    exact aux_bilinear_family_eq_finite_sum T f g z
  rw [hEq]
  apply Differentiable.diffContOnCl
  have hSumEq :
      (fun z : ℂ ↦ ∑ c ∈ f.1.range, ∑ d ∈ g.1.range,
        aux_scalarFamily c z * aux_scalarFamily d z *
          T (aux_compactSimpleFiberAll f c) (aux_compactSimpleFiberAll g d)) =
      (fun z : ℂ ↦ ∑ c ∈ f.1.range, ∑ d ∈ g.1.range,
        T (aux_compactSimpleFiberAll f c) (aux_compactSimpleFiberAll g d) *
          aux_scalarFamily c z * aux_scalarFamily d z) := by
    funext z
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hSumEq]
  exact aux_differentiable_finset_bilinear_family f.1.range g.1.range
    (fun c d ↦ T (aux_compactSimpleFiberAll f c) (aux_compactSimpleFiberAll g d)) id id

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_normalized_special_interpolation
    (T : Auto.CompactSimple →ₗ[ℂ] Auto.CompactSimple →ₗ[ℂ] ℂ)
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hInfinity : ∀ f g : Auto.CompactSimple,
      ‖T f g‖ ≤ A₀ *
        (eLpNorm (f.1 : ℝ → ℂ) (∞ : ℝ≥0∞) volume).toReal *
          (eLpNorm (g.1 : ℝ → ℂ) (∞ : ℝ≥0∞) volume).toReal)
    (hThreeHalves : ∀ f g : Auto.CompactSimple,
      ‖T f g‖ ≤ A₁ *
        (eLpNorm (f.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal *
          (eLpNorm (g.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal)
    (f g : Auto.CompactSimple)
    (hf : (eLpNorm (f.1 : ℝ → ℂ) (2 : ℝ≥0∞) volume).toReal = 1)
    (hg : (eLpNorm (g.1 : ℝ → ℂ) (2 : ℝ≥0∞) volume).toReal = 1) :
    ‖T f g‖ ≤ A₀ ^ (1 / 4 : ℝ) * A₁ ^ (3 / 4 : ℝ) := by
  exact aux_normalized_special_interpolation_core T A₀ A₁ hA₀ hA₁ hInfinity hThreeHalves f g hf hg
    (aux_diffContOnCl_bilinear_family T f g) (aux_bddAbove_bilinear_family T f g)

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_eLpNorm_normalize_two (f : ℝ → ℂ) (a : ℝ) (ha : 0 < a)
    (hfa : (eLpNorm f (2 : ℝ≥0∞) volume).toReal = a) :
    (eLpNorm (((a : ℂ)⁻¹) • f) (2 : ℝ≥0∞) volume).toReal = 1 := by
  rw [eLpNorm_const_smul, ENNReal.toReal_mul, hfa]
  have hscalar : ‖((a : ℂ)⁻¹)‖ₑ.toReal = a⁻¹ := by
    rw [enorm_inv (by exact_mod_cast ha.ne')]
    simp [Complex.norm_real, abs_of_pos ha]
  rw [hscalar, inv_mul_cancel₀ ha.ne']

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_norm_compactSimpleToLpTwo (f : Auto.CompactSimple) :
    ‖Auto.compactSimpleToLpTwo f‖ =
      (eLpNorm (f.1 : ℝ → ℂ) (2 : ℝ≥0∞) volume).toReal := by
  exact Lp.norm_toLp (f.1 : ℝ → ℂ) (Auto.compactSimpleMemLpTwo f)

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_eLpNorm_two_eq_zero_of_toReal_eq_zero (f : Auto.CompactSimple)
    (hzero : (eLpNorm (f.1 : ℝ → ℂ) (2 : ℝ≥0∞) volume).toReal = 0) :
    eLpNorm (f.1 : ℝ → ℂ) (2 : ℝ≥0∞) volume = 0 := by
  rcases (ENNReal.toReal_eq_zero_iff _).mp hzero with h | h
  · exact h
  · exact (Auto.compactSimpleMemLpTwo f).eLpNorm_ne_top h |>.elim

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_eLpNorm_threeHalves_eq_zero_of_two_toReal_eq_zero (f : Auto.CompactSimple)
    (hzero : (eLpNorm (f.1 : ℝ → ℂ) (2 : ℝ≥0∞) volume).toReal = 0) :
    eLpNorm (f.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume = 0 := by
  have htwo : eLpNorm (f.1 : ℝ → ℂ) (2 : ℝ≥0∞) volume = 0 :=
    aux_eLpNorm_two_eq_zero_of_toReal_eq_zero f hzero
  have hae : (f.1 : ℝ → ℂ) =ᵐ[volume] 0 :=
    (eLpNorm_eq_zero_iff f.1.aestronglyMeasurable (by norm_num)).mp htwo
  exact eLpNorm_eq_zero_of_ae_zero hae

/-- Auxiliary component of the proof of `prop:special-interpolation` and
`specialBilinearInterpolation`. -/
theorem aux_unnormalize_real_bound (a b C x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a⁻¹ * b⁻¹ * x ≤ C) :
    x ≤ C * a * b := by
  calc
    x = (a * b) * (a⁻¹ * b⁻¹ * x) := by
      field_simp
    _ ≤ (a * b) * C := by
      exact mul_le_mul_of_nonneg_left h (mul_nonneg ha.le hb.le)
    _ = C * a * b := by ring

/-- Reduces the general compact-simple estimate in `prop:special-interpolation`
to the normalized three-lines estimate used by `specialBilinearInterpolation`. -/
theorem aux_unnormalized_special_interpolation
    (T : Auto.CompactSimple →ₗ[ℂ] Auto.CompactSimple →ₗ[ℂ] ℂ)
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hInfinity : ∀ f g : Auto.CompactSimple,
      ‖T f g‖ ≤ A₀ *
        (eLpNorm (f.1 : ℝ → ℂ) (∞ : ℝ≥0∞) volume).toReal *
          (eLpNorm (g.1 : ℝ → ℂ) (∞ : ℝ≥0∞) volume).toReal)
    (hThreeHalves : ∀ f g : Auto.CompactSimple,
      ‖T f g‖ ≤ A₁ *
        (eLpNorm (f.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal *
          (eLpNorm (g.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal) :
    ∀ f g : Auto.CompactSimple,
      ‖T f g‖ ≤ A₀ ^ (1 / 4 : ℝ) * A₁ ^ (3 / 4 : ℝ) *
        ‖Auto.compactSimpleToLpTwo f‖ * ‖Auto.compactSimpleToLpTwo g‖ := by
  intro f g
  let a : ℝ := (eLpNorm (f.1 : ℝ → ℂ) (2 : ℝ≥0∞) volume).toReal
  let b : ℝ := (eLpNorm (g.1 : ℝ → ℂ) (2 : ℝ≥0∞) volume).toReal
  have hfa : (eLpNorm (f.1 : ℝ → ℂ) (2 : ℝ≥0∞) volume).toReal = a := rfl
  have hgb : (eLpNorm (g.1 : ℝ → ℂ) (2 : ℝ≥0∞) volume).toReal = b := rfl
  have hLpF : ‖Auto.compactSimpleToLpTwo f‖ = a := by
    exact aux_norm_compactSimpleToLpTwo f
  have hLpG : ‖Auto.compactSimpleToLpTwo g‖ = b := by
    exact aux_norm_compactSimpleToLpTwo g
  by_cases ha0 : a = 0
  · have hF32 : eLpNorm (f.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume = 0 :=
      aux_eLpNorm_threeHalves_eq_zero_of_two_toReal_eq_zero f (by simpa [hfa] using ha0)
    have hzero : ‖T f g‖ ≤ 0 := by
      calc
        ‖T f g‖ ≤ A₁ *
            (eLpNorm (f.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal *
              (eLpNorm (g.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal :=
          hThreeHalves f g
        _ = 0 := by rw [hF32]; simp
    simpa [hLpF, hLpG, ha0] using hzero
  by_cases hb0 : b = 0
  · have hG32 : eLpNorm (g.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume = 0 :=
      aux_eLpNorm_threeHalves_eq_zero_of_two_toReal_eq_zero g (by simpa [hgb] using hb0)
    have hzero : ‖T f g‖ ≤ 0 := by
      calc
        ‖T f g‖ ≤ A₁ *
            (eLpNorm (f.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal *
              (eLpNorm (g.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal :=
          hThreeHalves f g
        _ = 0 := by rw [hG32]; simp
    simpa [hLpF, hLpG, hb0] using hzero
  have ha : 0 < a := lt_of_le_of_ne (by positivity) (Ne.symm ha0)
  have hb : 0 < b := lt_of_le_of_ne (by positivity) (Ne.symm hb0)
  let f' : Auto.CompactSimple := ((a : ℂ)⁻¹) • f
  let g' : Auto.CompactSimple := ((b : ℂ)⁻¹) • g
  have hf' : (eLpNorm (f'.1 : ℝ → ℂ) (2 : ℝ≥0∞) volume).toReal = 1 := by
    change (eLpNorm (((a : ℂ)⁻¹) • (f.1 : ℝ → ℂ)) (2 : ℝ≥0∞) volume).toReal = 1
    exact aux_eLpNorm_normalize_two (f.1 : ℝ → ℂ) a ha hfa
  have hg' : (eLpNorm (g'.1 : ℝ → ℂ) (2 : ℝ≥0∞) volume).toReal = 1 := by
    change (eLpNorm (((b : ℂ)⁻¹) • (g.1 : ℝ → ℂ)) (2 : ℝ≥0∞) volume).toReal = 1
    exact aux_eLpNorm_normalize_two (g.1 : ℝ → ℂ) b hb hgb
  have hnormalized := aux_normalized_special_interpolation T A₀ A₁ hA₀ hA₁ hInfinity hThreeHalves
    f' g' hf' hg'
  have hscale : T f' g' = ((a : ℂ)⁻¹) * ((b : ℂ)⁻¹) * T f g := by
    simp [f', g']
    ring
  rw [hscale, norm_mul, norm_mul] at hnormalized
  have hinvA : ‖((a : ℂ)⁻¹)‖ = a⁻¹ := by
    rw [norm_inv]
    simp [Complex.norm_real, abs_of_pos ha]
  have hinvB : ‖((b : ℂ)⁻¹)‖ = b⁻¹ := by
    rw [norm_inv]
    simp [Complex.norm_real, abs_of_pos hb]
  rw [hinvA, hinvB] at hnormalized
  have hresult := aux_unnormalize_real_bound a b
    (A₀ ^ (1 / 4 : ℝ) * A₁ ^ (3 / 4 : ℝ)) ‖T f g‖ ha hb hnormalized
  simpa [hLpF, hLpG] using hresult

/--
Let \(T\) be a complex bilinear form on bounded, compactly supported simple
functions.  Suppose
\[
|T(f,g)|\leq A_0\lVert f\rVert_\infty\lVert g\rVert_\infty,
\qquad
|T(f,g)|\leq A_1\lVert f\rVert_{3/2}\lVert g\rVert_{3/2},
\]
where \(A_0,A_1\geq0\).  Then \(T\) extends to
\(L^2(\mathbb R)\times L^2(\mathbb R)\) and
\[
|T(f,g)|\leq A_0^{1/4}A_1^{3/4}\lVert f\rVert_2\lVert g\rVert_2.
\]
-/
theorem specialBilinearInterpolation
    (T : CompactSimple →ₗ[ℂ] CompactSimple →ₗ[ℂ] ℂ)
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hInfinity : ∀ f g : CompactSimple,
      ‖T f g‖ ≤ A₀ *
        (eLpNorm (f.1 : ℝ → ℂ) (∞ : ℝ≥0∞) volume).toReal *
          (eLpNorm (g.1 : ℝ → ℂ) (∞ : ℝ≥0∞) volume).toReal)
    (hThreeHalves : ∀ f g : CompactSimple,
      ‖T f g‖ ≤ A₁ *
        (eLpNorm (f.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal *
          (eLpNorm (g.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal) :
    ∃ T₂ : Lp (α := ℝ) ℂ 2 volume →L[ℂ]
        Lp (α := ℝ) ℂ 2 volume →L[ℂ] ℂ,
      (∀ f g : CompactSimple,
        T₂ (compactSimpleToLpTwo f) (compactSimpleToLpTwo g) = T f g) ∧
        ∀ f g : Lp (α := ℝ) ℂ 2 volume,
          ‖T₂ f g‖ ≤
            A₀ ^ (1 / (4 : ℝ)) * A₁ ^ (3 / (4 : ℝ)) * ‖f‖ * ‖g‖ := by
  have hC : 0 ≤ A₀ ^ (1 / (4 : ℝ)) * A₁ ^ (3 / (4 : ℝ)) := by
    positivity
  have hcompact : ∀ f g : CompactSimple,
      ‖T f g‖ ≤ A₀ ^ (1 / (4 : ℝ)) * A₁ ^ (3 / (4 : ℝ)) *
        ‖aux_compactSimpleToLpTwoCLM f‖ * ‖aux_compactSimpleToLpTwoCLM g‖ := by
    intro f g
    simpa only [aux_compactSimpleToLpTwoCLM_apply] using
      aux_unnormalized_special_interpolation T A₀ A₁ hA₀ hA₁ hInfinity hThreeHalves f g
  rcases aux_extend_bilinear_of_dense aux_compactSimpleToLpTwoCLM
      aux_compactSimpleToLpTwoCLM_denseRange T
      (A₀ ^ (1 / (4 : ℝ)) * A₁ ^ (3 / (4 : ℝ))) hC hcompact with
    ⟨T₂, hagree, hbound⟩
  refine ⟨T₂, ?_, ?_⟩
  · intro f g
    simpa only [aux_compactSimpleToLpTwoCLM_apply] using hagree f g
  · intro f g
    exact hbound f g

/-- The explicit constant in \(\label{prop:dyadic-l2-decay}\), used by
`dyadicL2Smoothing`:
\[
C_{\ref{prop:dyadic-l2-decay},\,K,\chi}
=2^{10}\mathcal S(A_0,A_1,A_2,J_\chi;\chi)^2,
\]
where the intervals are those of \(\label{def:main-interaction-data}\). -/
def C_dyadicL2Smoothing (a b : ℝ) (χ : ℝ → ℝ) : ℝ :=
  (2 : ℝ) ^ 10 *
    sizeParameter ![
      aux_mainInteractionA0 a b,
      aux_mainInteractionA1 a b χ,
      aux_mainInteractionA2 a b χ,
      aux_mainInteractionJ χ] χ ^ 2

/-- Supplies the Fubini hypothesis for the compact-simple bilinear form and
the limiting argument in `prop:dyadic-l2-decay`, formalized by
`dyadicL2Smoothing`.  This is the elementary `L∞ × L² × L²` absolute
integrability estimate for the raw trilinear kernel. -/
theorem aux_trilinearIntegrand_integrable_l2
    (χ : ℝ → ℝ) (f₀ f₁ f₂ : ℝ → ℂ)
    (hχ : Integrable (fun t : ℝ ↦ (χ t : ℂ)))
    (hf₀ : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁ : MemLp f₁ (2 : ℝ≥0∞) volume)
    (hf₂ : MemLp f₂ (2 : ℝ≥0∞) volume) :
    Integrable (aux_u3_trilinearIntegrand f₀ f₁ f₂ χ) (volume.prod volume) := by
  let B : ℝ → ℝ → ℂ := fun t x ↦
    f₀ x * (f₁ (x + t) * f₂ (x + t ^ 2))
  let N : ℝ := (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal
  let C : ℝ := N *
    ((|((1 : ℝ)⁻¹)| * ∫ x : ℝ, ‖f₁ x‖ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) *
      (|((1 : ℝ)⁻¹)| * ∫ x : ℝ, ‖f₂ x‖ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)))
  have hNbound : ∀ᵐ x : ℝ ∂volume, ‖f₀ x‖ ≤ N := by
    simpa [N] using aux_homogeneous_ae_norm_le_toReal f₀ hf₀
  have hNnonneg : 0 ≤ N := by simp [N]
  have hBmeas : AEStronglyMeasurable (Function.uncurry B) (volume.prod volume) := by
    have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ)
        (volume.prod volume) (volume.prod volume) := Measure.measurePreserving_swap
    have hsum : Measure.QuasiMeasurePreserving (fun z : ℝ × ℝ ↦ z.2 + z.1)
        (volume.prod volume) volume := by
      simpa [Function.comp_def] using
        aux_u3_qmp_add.comp hswap.quasiMeasurePreserving
    have hsq : Measure.QuasiMeasurePreserving (fun z : ℝ × ℝ ↦ z.2 + z.1 ^ 2)
        (volume.prod volume) volume := by
      simpa [Function.comp_def] using
        aux_u3_qmp_add_sq.comp hswap.quasiMeasurePreserving
    change AEStronglyMeasurable
      (fun z : ℝ × ℝ ↦ f₀ z.2 * (f₁ (z.2 + z.1) * f₂ (z.2 + z.1 ^ 2)))
      (volume.prod volume)
    exact (hf₀.aestronglyMeasurable.comp_snd).mul
      ((hf₁.aestronglyMeasurable.comp_quasiMeasurePreserving hsum).mul
        (hf₂.aestronglyMeasurable.comp_quasiMeasurePreserving hsq))
  have hBint : ∀ t : ℝ, Integrable (B t) volume := by
    intro t
    have h₁t : MemLp (fun x : ℝ ↦ f₁ ((1 : ℝ) * x + t)) (2 : ℝ≥0∞) volume :=
      aux_gowersFourier_memLp_comp_affine f₁ 2 hf₁ 1 t one_ne_zero
    have h₂t : MemLp (fun x : ℝ ↦ f₂ ((1 : ℝ) * x + t ^ 2)) (2 : ℝ≥0∞) volume :=
      aux_gowersFourier_memLp_comp_affine f₂ 2 hf₂ 1 (t ^ 2) one_ne_zero
    have hprod : Integrable (fun x : ℝ ↦
        f₁ ((1 : ℝ) * x + t) * f₂ ((1 : ℝ) * x + t ^ 2)) volume := by
      exact h₁t.integrable_mul h₂t
    have hmul := hprod.bdd_mul hf₀.aestronglyMeasurable hNbound
    convert hmul using 1
    funext x
    dsimp [B]
    simp [one_mul]
  have hBbound : ∀ t : ℝ, ∫ x : ℝ, ‖B t x‖ ≤ C := by
    intro t
    have h₁t : MemLp (fun x : ℝ ↦ f₁ ((1 : ℝ) * x + t)) (2 : ℝ≥0∞) volume :=
      aux_gowersFourier_memLp_comp_affine f₁ 2 hf₁ 1 t one_ne_zero
    have h₂t : MemLp (fun x : ℝ ↦ f₂ ((1 : ℝ) * x + t ^ 2)) (2 : ℝ≥0∞) volume :=
      aux_gowersFourier_memLp_comp_affine f₂ 2 hf₂ 1 (t ^ 2) one_ne_zero
    have hprod : Integrable (fun x : ℝ ↦
        f₁ ((1 : ℝ) * x + t) * f₂ ((1 : ℝ) * x + t ^ 2)) volume := by
      exact h₁t.integrable_mul h₂t
    have hprodNorm : Integrable (fun x : ℝ ↦
        ‖f₁ ((1 : ℝ) * x + t)‖ * ‖f₂ ((1 : ℝ) * x + t ^ 2)‖) volume := by
      simpa only [norm_mul] using hprod.norm
    calc
      ∫ x : ℝ, ‖B t x‖ = ∫ x : ℝ,
          ‖f₀ x‖ *
            (‖f₁ ((1 : ℝ) * x + t)‖ * ‖f₂ ((1 : ℝ) * x + t ^ 2)‖) := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp [B]
        rw [norm_mul, norm_mul]
        simp [one_mul]
      _ ≤ ∫ x : ℝ, N *
          (‖f₁ ((1 : ℝ) * x + t)‖ * ‖f₂ ((1 : ℝ) * x + t ^ 2)‖) := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x ↦
            mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
          (hprodNorm.const_mul N)
        filter_upwards [hNbound] with x hx
        exact mul_le_mul_of_nonneg_right hx
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = N * ∫ x : ℝ,
          ‖f₁ ((1 : ℝ) * x + t)‖ * ‖f₂ ((1 : ℝ) * x + t ^ 2)‖ := by
        rw [integral_const_mul]
      _ ≤ C := by
        dsimp [C]
        apply mul_le_mul_of_nonneg_left
          (aux_gowersFourier_integral_norm_mul_comp_affine_le_scaled f₁ f₂ hf₁ hf₂
            1 1 t (t ^ 2) one_ne_zero one_ne_zero)
          hNnonneg
  have hjoint : Integrable (fun z : ℝ × ℝ ↦ (χ z.1 : ℂ) * B z.1 z.2)
      (volume.prod volume) :=
    aux_gowersFourier_integrable_weighted_bilinear_of_section_bound
      (fun t : ℝ ↦ (χ t : ℂ)) hχ B hBmeas hBint C hBbound
  have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ)
      (volume.prod volume) (volume.prod volume) := Measure.measurePreserving_swap
  have hcomp : Integrable ((fun z : ℝ × ℝ ↦ (χ z.1 : ℂ) * B z.1 z.2) ∘ Prod.swap)
      (volume.prod volume) :=
    (hswap.integrable_comp hjoint.aestronglyMeasurable).mpr hjoint
  convert hcomp using 1
  funext z
  dsimp [B, Function.comp_def, aux_u3_trilinearIntegrand]
  ring

/-- Gives the `L²` mapping property of the dyadic piece needed to make the
compact-simple form in `prop:dyadic-l2-decay`, formalized by
`dyadicL2Smoothing`, bilinear. -/
theorem aux_Q_memLp_two (k : ℕ) (g : ℝ → ℂ)
    (hg : MemLp g (2 : ℝ≥0∞) volume) :
    MemLp (Q k g) (2 : ℝ≥0∞) volume := by
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hκ : Integrable
      (aux_scaledInverseFourierKernel (fun ξ ↦ (annularCutoff ξ : ℂ)) k) volume :=
    memLp_one_iff_integrable.mp (aux_scaledAnnularInverseFourierKernel_memLp_one k)
  unfold Q
  exact aux_convolution_memLp_of_memLp_one _ _ hκ hg

/-- Supplies the finite-`Lp` and endpoint membership of compact simple
functions used in `prop:dyadic-l2-decay`, formalized by `dyadicL2Smoothing`. -/
theorem aux_compactSimple_memLp (f : CompactSimple) (p : ℝ≥0∞) :
    MemLp (f.1 : ℝ → ℂ) p volume := by
  obtain ⟨C, hC⟩ := (f.1.map (fun z : ℂ ↦ ‖z‖)).exists_forall_le
  refine f.2.memLp_of_bound f.1.aestronglyMeasurable C ?_
  exact Filter.Eventually.of_forall fun x ↦ by simpa using hC x

/-- Records additivity of the dyadic piece on `L²` inputs for the compact
simple form used in `prop:dyadic-l2-decay`, formalized by `dyadicL2Smoothing`. -/
theorem aux_Q_add_of_memLp_two (k : ℕ) (f g : ℝ → ℂ)
    (hf : MemLp f (2 : ℝ≥0∞) volume)
    (hg : MemLp g (2 : ℝ≥0∞) volume) :
    Q k (f + g) = Q k f + Q k g := by
  let κ : ℝ → ℂ :=
    aux_scaledInverseFourierKernel (fun ξ ↦ (annularCutoff ξ : ℂ)) k
  change aux_convolution κ (f + g) = aux_convolution κ f + aux_convolution κ g
  rw [aux_convolution_eq_measureTheory_convolution,
    aux_convolution_eq_measureTheory_convolution,
    aux_convolution_eq_measureTheory_convolution]
  apply ConvolutionExists.distrib_add
  · intro x
    exact aux_convolutionExistsAt_of_memLp_two
      (by simpa [κ] using aux_scaledAnnularInverseFourierKernel_memLp_two k) hf x
  · intro x
    exact aux_convolutionExistsAt_of_memLp_two
      (by simpa [κ] using aux_scaledAnnularInverseFourierKernel_memLp_two k) hg x

/-- Records complex homogeneity of the dyadic piece for the compact-simple
bilinear form used in `prop:dyadic-l2-decay`, formalized by
`dyadicL2Smoothing`. -/
theorem aux_Q_smul (k : ℕ) (c : ℂ) (f : ℝ → ℂ) :
    Q k (c • f) = c • Q k f := by
  let κ : ℝ → ℂ :=
    aux_scaledInverseFourierKernel (fun ξ ↦ (annularCutoff ξ : ℂ)) k
  change aux_convolution κ (c • f) = c • aux_convolution κ f
  rw [aux_convolution_eq_measureTheory_convolution,
    aux_convolution_eq_measureTheory_convolution]
  exact convolution_smul

/-- Supplies additivity in the middle variable for the compact-simple
bilinear form in `prop:dyadic-l2-decay`, formalized by `dyadicL2Smoothing`. -/
theorem aux_trilinearForm_add_middle
    (χ : ℝ → ℝ) (f₀ f₁ f₁' f₂ : ℝ → ℂ)
    (h₁ : Integrable (aux_u3_trilinearIntegrand f₀ f₁ f₂ χ) (volume.prod volume))
    (h₂ : Integrable (aux_u3_trilinearIntegrand f₀ f₁' f₂ χ) (volume.prod volume)) :
    trilinearForm χ f₀ (f₁ + f₁') f₂ =
      trilinearForm χ f₀ f₁ f₂ + trilinearForm χ f₀ f₁' f₂ := by
  calc
    trilinearForm χ f₀ (f₁ + f₁') f₂ =
        ∫ x : ℝ, ∫ t : ℝ,
          aux_u3_trilinearIntegrand f₀ f₁ f₂ χ (x, t) +
            aux_u3_trilinearIntegrand f₀ f₁' f₂ χ (x, t) := by
              apply integral_congr_ae
              filter_upwards with x
              apply integral_congr_ae
              filter_upwards with t
              simp only [aux_u3_trilinearIntegrand, Pi.add_apply]
              ring
    _ = trilinearForm χ f₀ f₁ f₂ + trilinearForm χ f₀ f₁' f₂ := by
      change
        (∫ x : ℝ, ∫ t : ℝ,
          aux_u3_trilinearIntegrand f₀ f₁ f₂ χ (x, t) +
            aux_u3_trilinearIntegrand f₀ f₁' f₂ χ (x, t)) =
          (∫ x : ℝ, ∫ t : ℝ,
            aux_u3_trilinearIntegrand f₀ f₁ f₂ χ (x, t)) +
            ∫ x : ℝ, ∫ t : ℝ,
              aux_u3_trilinearIntegrand f₀ f₁' f₂ χ (x, t)
      exact integral_integral_add h₁ h₂

/-- Supplies additivity in the last variable for the compact-simple bilinear
form in `prop:dyadic-l2-decay`, formalized by `dyadicL2Smoothing`. -/
theorem aux_trilinearForm_add_last
    (χ : ℝ → ℝ) (f₀ f₁ f₂ f₂' : ℝ → ℂ)
    (h₁ : Integrable (aux_u3_trilinearIntegrand f₀ f₁ f₂ χ) (volume.prod volume))
    (h₂ : Integrable (aux_u3_trilinearIntegrand f₀ f₁ f₂' χ) (volume.prod volume)) :
    trilinearForm χ f₀ f₁ (f₂ + f₂') =
      trilinearForm χ f₀ f₁ f₂ + trilinearForm χ f₀ f₁ f₂' := by
  calc
    trilinearForm χ f₀ f₁ (f₂ + f₂') =
        ∫ x : ℝ, ∫ t : ℝ,
          aux_u3_trilinearIntegrand f₀ f₁ f₂ χ (x, t) +
            aux_u3_trilinearIntegrand f₀ f₁ f₂' χ (x, t) := by
              apply integral_congr_ae
              filter_upwards with x
              apply integral_congr_ae
              filter_upwards with t
              simp only [aux_u3_trilinearIntegrand, Pi.add_apply]
              ring
    _ = trilinearForm χ f₀ f₁ f₂ + trilinearForm χ f₀ f₁ f₂' := by
      change
        (∫ x : ℝ, ∫ t : ℝ,
          aux_u3_trilinearIntegrand f₀ f₁ f₂ χ (x, t) +
            aux_u3_trilinearIntegrand f₀ f₁ f₂' χ (x, t)) =
          (∫ x : ℝ, ∫ t : ℝ,
            aux_u3_trilinearIntegrand f₀ f₁ f₂ χ (x, t)) +
            ∫ x : ℝ, ∫ t : ℝ,
              aux_u3_trilinearIntegrand f₀ f₁ f₂' χ (x, t)
      exact integral_integral_add h₁ h₂

/-- Supplies complex homogeneity in the middle variable for the compact-simple
bilinear form in `prop:dyadic-l2-decay`, formalized by `dyadicL2Smoothing`. -/
theorem aux_trilinearForm_smul_middle
    (χ : ℝ → ℝ) (f₀ f₁ f₂ : ℝ → ℂ) (c : ℂ) :
    trilinearForm χ f₀ (c • f₁) f₂ = c • trilinearForm χ f₀ f₁ f₂ := by
  unfold trilinearForm
  calc
    (∫ x : ℝ, ∫ t : ℝ,
        f₀ x * (c • f₁) (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ)) =
      ∫ x : ℝ, ∫ t : ℝ,
        c • (f₀ x * f₁ (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ)) := by
          apply integral_congr_ae
          filter_upwards with x
          apply integral_congr_ae
          filter_upwards with t
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
    _ = ∫ x : ℝ, c • ∫ t : ℝ,
        f₀ x * f₁ (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ) := by
          apply integral_congr_ae
          filter_upwards with x
          exact integral_smul c _
    _ = c • ∫ x : ℝ, ∫ t : ℝ,
        f₀ x * f₁ (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ) := by
          exact integral_smul c _

/-- Supplies complex homogeneity in the last variable for the compact-simple
bilinear form in `prop:dyadic-l2-decay`, formalized by `dyadicL2Smoothing`. -/
theorem aux_trilinearForm_smul_last
    (χ : ℝ → ℝ) (f₀ f₁ f₂ : ℝ → ℂ) (c : ℂ) :
    trilinearForm χ f₀ f₁ (c • f₂) = c • trilinearForm χ f₀ f₁ f₂ := by
  unfold trilinearForm
  calc
    (∫ x : ℝ, ∫ t : ℝ,
        f₀ x * f₁ (x + t) * (c • f₂) (x + t ^ 2) * (χ t : ℂ)) =
      ∫ x : ℝ, ∫ t : ℝ,
        c • (f₀ x * f₁ (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ)) := by
          apply integral_congr_ae
          filter_upwards with x
          apply integral_congr_ae
          filter_upwards with t
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
    _ = ∫ x : ℝ, c • ∫ t : ℝ,
        f₀ x * f₁ (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ) := by
          apply integral_congr_ae
          filter_upwards with x
          exact integral_smul c _
    _ = c • ∫ x : ℝ, ∫ t : ℝ,
        f₀ x * f₁ (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ) := by
          exact integral_smul c _

/-- The compact-simple bilinear form to which `specialBilinearInterpolation`
is applied in `prop:dyadic-l2-decay`, formalized by `dyadicL2Smoothing`. -/
noncomputable def aux_compactSimpleDyadicForm
    (χ : ℝ → ℝ) (f₀ : ℝ → ℂ) (k : ℕ)
    (hraw : ∀ f g : CompactSimple,
      Integrable (aux_u3_trilinearIntegrand f₀ (f.1 : ℝ → ℂ) (Q k (g.1 : ℝ → ℂ)) χ)
        (volume.prod volume)) :
    CompactSimple →ₗ[ℂ] CompactSimple →ₗ[ℂ] ℂ where
  toFun f :=
    { toFun := fun g ↦ trilinearForm χ f₀ (f.1 : ℝ → ℂ) (Q k (g.1 : ℝ → ℂ))
      map_add' := by
        intro g g'
        change trilinearForm χ f₀ (f.1 : ℝ → ℂ)
          (Q k ((g + g').1 : ℝ → ℂ)) =
            trilinearForm χ f₀ (f.1 : ℝ → ℂ) (Q k (g.1 : ℝ → ℂ)) +
              trilinearForm χ f₀ (f.1 : ℝ → ℂ) (Q k (g'.1 : ℝ → ℂ))
        have hq : Q k ((g + g').1 : ℝ → ℂ) =
            Q k (g.1 : ℝ → ℂ) + Q k (g'.1 : ℝ → ℂ) := by
          change Q k ((g.1 : ℝ → ℂ) + g'.1) =
            Q k (g.1 : ℝ → ℂ) + Q k (g'.1 : ℝ → ℂ)
          exact aux_Q_add_of_memLp_two k (g.1 : ℝ → ℂ) (g'.1 : ℝ → ℂ)
            (compactSimpleMemLpTwo g) (compactSimpleMemLpTwo g')
        rw [hq]
        exact aux_trilinearForm_add_last χ f₀ (f.1 : ℝ → ℂ)
          (Q k (g.1 : ℝ → ℂ)) (Q k (g'.1 : ℝ → ℂ)) (hraw f g) (hraw f g')
      map_smul' := by
        intro c g
        change trilinearForm χ f₀ (f.1 : ℝ → ℂ)
          (Q k ((c • g).1 : ℝ → ℂ)) =
            c • trilinearForm χ f₀ (f.1 : ℝ → ℂ) (Q k (g.1 : ℝ → ℂ))
        have hq : Q k ((c • g).1 : ℝ → ℂ) = c • Q k (g.1 : ℝ → ℂ) := by
          change Q k (c • (g.1 : ℝ → ℂ)) = c • Q k (g.1 : ℝ → ℂ)
          exact aux_Q_smul k c (g.1 : ℝ → ℂ)
        rw [hq]
        exact aux_trilinearForm_smul_last χ f₀ (f.1 : ℝ → ℂ) (Q k (g.1 : ℝ → ℂ)) c }
  map_add' := by
    intro f f'
    ext g
    change trilinearForm χ f₀ ((f + f').1 : ℝ → ℂ) (Q k (g.1 : ℝ → ℂ)) =
      trilinearForm χ f₀ (f.1 : ℝ → ℂ) (Q k (g.1 : ℝ → ℂ)) +
        trilinearForm χ f₀ (f'.1 : ℝ → ℂ) (Q k (g.1 : ℝ → ℂ))
    change trilinearForm χ f₀ ((f.1 : ℝ → ℂ) + f'.1) (Q k (g.1 : ℝ → ℂ)) = _
    exact aux_trilinearForm_add_middle χ f₀ (f.1 : ℝ → ℂ) (f'.1 : ℝ → ℂ)
      (Q k (g.1 : ℝ → ℂ)) (hraw f g) (hraw f' g)
  map_smul' := by
    intro c f
    ext g
    change trilinearForm χ f₀ ((c • f).1 : ℝ → ℂ) (Q k (g.1 : ℝ → ℂ)) =
      c • trilinearForm χ f₀ (f.1 : ℝ → ℂ) (Q k (g.1 : ℝ → ℂ))
    change trilinearForm χ f₀ (c • (f.1 : ℝ → ℂ)) (Q k (g.1 : ℝ → ℂ)) = _
    exact aux_trilinearForm_smul_middle χ f₀ (f.1 : ℝ → ℂ) (Q k (g.1 : ℝ → ℂ)) c

/-- Instantiates the compact-simple dyadic form in `prop:dyadic-l2-decay`,
formalized by `dyadicL2Smoothing`, with its canonical absolute-integrability
witness. -/
noncomputable def aux_compactSimpleDyadicFormOf
    (χ : ℝ → ℝ) (f₀ : ℝ → ℂ) (k : ℕ)
    (hχ : Integrable (fun t : ℝ ↦ (χ t : ℂ)))
    (hf₀ : MemLp f₀ (∞ : ℝ≥0∞) volume) :
    CompactSimple →ₗ[ℂ] CompactSimple →ₗ[ℂ] ℂ :=
  aux_compactSimpleDyadicForm χ f₀ k (fun f g ↦
    aux_trilinearIntegrand_integrable_l2 χ f₀ (f.1 : ℝ → ℂ)
      (Q k (g.1 : ℝ → ℂ)) hχ hf₀ (compactSimpleMemLpTwo f)
        (aux_Q_memLp_two k (g.1 : ℝ → ℂ) (compactSimpleMemLpTwo g)))

/-- Supplies the `L∞` endpoint hypothesis for `specialBilinearInterpolation`
in the proof of `prop:dyadic-l2-decay`, formalized by `dyadicL2Smoothing`. -/
theorem aux_compactSimpleDyadicFormOf_infinity_bound
    (a b : ℝ) (χ : ℝ → ℝ) (hab : a ≤ b)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) (f₀ : ℝ → ℂ)
    (hχ : Integrable (fun t : ℝ ↦ (χ t : ℂ)))
    (hf₀ : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₀support : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f₀ x = 0)
    (f g : CompactSimple) :
    ‖aux_compactSimpleDyadicFormOf χ f₀ k hχ hf₀ f g‖ ≤
      (C_dyadicLInfinityDecay a b χ *
        (2 : ℝ) ^ (-((2 : ℝ) ^ (-11 : ℝ)) * (k : ℝ)) *
          (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal) *
            (eLpNorm (f.1 : ℝ → ℂ) (∞ : ℝ≥0∞) volume).toReal *
              (eLpNorm (g.1 : ℝ → ℂ) (∞ : ℝ≥0∞) volume).toReal := by
  change trilinearFormAbs χ f₀ (f.1 : ℝ → ℂ) (Q k (g.1 : ℝ → ℂ)) ≤ _
  simpa [mul_assoc] using
    (dyadicLInfinityDecay a b χ hab hχ_smooth hχ_compact hχ_nonneg hχ_le_one k hk
      f₀ (f.1 : ℝ → ℂ) (g.1 : ℝ → ℂ) hf₀ (aux_compactSimple_memLp f ∞)
      (aux_compactSimple_memLp g ∞) hf₀support)

/-- Supplies the `L^{3/2}` endpoint hypothesis for
`specialBilinearInterpolation` in `prop:dyadic-l2-decay`, formalized by
`dyadicL2Smoothing`. -/
theorem aux_compactSimpleDyadicFormOf_threeHalves_bound
    (χ : ℝ → ℝ)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (k : ℕ) (f₀ : ℝ → ℂ)
    (hχ : Integrable (fun t : ℝ ↦ (χ t : ℂ)))
    (hf₀ : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (f g : CompactSimple) :
    ‖aux_compactSimpleDyadicFormOf χ f₀ k hχ hf₀ f g‖ ≤
      (C_quadraticAveragingOperator χ *
        (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal * (2 : ℝ) ^ 6) *
          (eLpNorm (f.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal *
            (eLpNorm (g.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal := by
  let : Fact (1 ≤ (3 / 2 : ℝ≥0∞)) := ⟨by
    refine (ENNReal.le_div_iff_mul_le (a := 1) (b := 2) (c := 3)
      (by simp) (by simp)).2 ?_
    norm_num⟩
  let : Fact ((3 / 2 : ℝ≥0∞) ≠ ∞) :=
    ⟨ENNReal.div_ne_top (by simp) (by norm_num)⟩
  have hκ : Integrable
      (aux_scaledInverseFourierKernel (fun ξ ↦ (annularCutoff ξ : ℂ)) k) volume :=
    memLp_one_iff_integrable.mp (aux_scaledAnnularInverseFourierKernel_memLp_one k)
  have hgthree : MemLp (g.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume :=
    aux_compactSimple_memLp g (3 / 2 : ℝ≥0∞)
  have hQthree : MemLp (Q k (g.1 : ℝ → ℂ)) (3 / 2 : ℝ≥0∞) volume := by
    unfold Q
    exact aux_convolution_memLp_of_memLp_one _ _ hκ hgthree
  have hQbound : eLpNorm (Q k (g.1 : ℝ → ℂ)) (3 / 2 : ℝ≥0∞) volume ≤
      (2 : ℝ≥0∞) ^ 6 * eLpNorm (g.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume :=
    aux_eLpNorm_Q_le (g.1 : ℝ → ℂ) (compactSimpleMemLpTwo g) k (3 / 2 : ℝ≥0∞)
      (by
        refine (ENNReal.le_div_iff_mul_le (a := 1) (b := 2) (c := 3)
          (by simp) (by simp)).2 ?_
        norm_num)
  have hrighttop :
      (2 : ℝ≥0∞) ^ 6 * eLpNorm (g.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hgthree.eLpNorm_ne_top
  have hQreal : (eLpNorm (Q k (g.1 : ℝ → ℂ)) (3 / 2 : ℝ≥0∞) volume).toReal ≤
      (2 : ℝ) ^ 6 *
        (eLpNorm (g.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal := by
    calc
      (eLpNorm (Q k (g.1 : ℝ → ℂ)) (3 / 2 : ℝ≥0∞) volume).toReal ≤
          ((2 : ℝ≥0∞) ^ 6 *
            eLpNorm (g.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal :=
        ENNReal.toReal_mono hrighttop hQbound
      _ = (2 : ℝ) ^ 6 *
          (eLpNorm (g.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal := by
        rw [ENNReal.toReal_mul]
        norm_num
  have hCquad : 0 ≤ C_quadraticAveragingOperator χ := by
    unfold C_quadraticAveragingOperator
    have hR : 0 ≤ supportRadius χ :=
      zero_le_one.trans (aux_u3_one_le_supportRadius χ hχ_compact)
    positivity
  change trilinearFormAbs χ f₀ (f.1 : ℝ → ℂ) (Q k (g.1 : ℝ → ℂ)) ≤ _
  calc
    trilinearFormAbs χ f₀ (f.1 : ℝ → ℂ) (Q k (g.1 : ℝ → ℂ)) ≤
        C_quadraticAveragingOperator χ *
          (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
            (eLpNorm (f.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal *
              (eLpNorm (Q k (g.1 : ℝ → ℂ)) (3 / 2 : ℝ≥0∞) volume).toReal :=
      nondecayingLThreeHalvesEndpoint χ hχ_smooth hχ_compact hχ_nonneg hχ_le_one
        f₀ (f.1 : ℝ → ℂ) (Q k (g.1 : ℝ → ℂ)) hf₀
        (aux_compactSimple_memLp f (3 / 2 : ℝ≥0∞)) hQthree
    _ ≤ C_quadraticAveragingOperator χ *
          (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
            (eLpNorm (f.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal *
              ((2 : ℝ) ^ 6 *
                (eLpNorm (g.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal) := by
      apply mul_le_mul_of_nonneg_left hQreal
      exact mul_nonneg
        (mul_nonneg hCquad ENNReal.toReal_nonneg)
        ENNReal.toReal_nonneg
    _ = (C_quadraticAveragingOperator χ *
        (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal * (2 : ℝ) ^ 6) *
          (eLpNorm (f.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal *
            (eLpNorm (g.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal := by
      ring

/-- The raw `L¹` norm estimate behind the `L∞ × L² × L²` continuity bridge
for `prop:dyadic-l2-decay` and `dyadicL2Smoothing`. -/
theorem aux_trilinearIntegrand_norm_integral_le_linf_l2_l2
    (χ : ℝ → ℝ) (f₀ f₁ f₂ : ℝ → ℂ)
    (hχ : Integrable (fun t : ℝ ↦ (χ t : ℂ)))
    (hf₀ : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁ : MemLp f₁ (2 : ℝ≥0∞) volume)
    (hf₂ : MemLp f₂ (2 : ℝ≥0∞) volume) :
    ∫ z : ℝ × ℝ, ‖aux_u3_trilinearIntegrand f₀ f₁ f₂ χ z‖ ≤
      (∫ t : ℝ, ‖(χ t : ℂ)‖) *
        (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
          ((∫ x : ℝ, ‖f₁ x‖ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) *
            (∫ x : ℝ, ‖f₂ x‖ ^ (2 : ℕ)) ^ (1 / (2 : ℝ))) := by
  let B : ℝ → ℝ → ℂ := fun t x ↦
    f₀ x * (f₁ (x + t) * f₂ (x + t ^ 2))
  let N : ℝ := (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal
  let D : ℝ :=
    ((∫ x : ℝ, ‖f₁ x‖ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) *
      (∫ x : ℝ, ‖f₂ x‖ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)))
  let C : ℝ := N * D
  have hNbound : ∀ᵐ x : ℝ ∂volume, ‖f₀ x‖ ≤ N := by
    simpa [N] using aux_homogeneous_ae_norm_le_toReal f₀ hf₀
  have hNnonneg : 0 ≤ N := by simp [N]
  have hBbound : ∀ t : ℝ, ∫ x : ℝ, ‖B t x‖ ≤ C := by
    intro t
    have h₁t : MemLp (fun x : ℝ ↦ f₁ ((1 : ℝ) * x + t)) (2 : ℝ≥0∞) volume :=
      aux_gowersFourier_memLp_comp_affine f₁ 2 hf₁ 1 t one_ne_zero
    have h₂t : MemLp (fun x : ℝ ↦ f₂ ((1 : ℝ) * x + t ^ 2)) (2 : ℝ≥0∞) volume :=
      aux_gowersFourier_memLp_comp_affine f₂ 2 hf₂ 1 (t ^ 2) one_ne_zero
    have hprod : Integrable (fun x : ℝ ↦
        f₁ ((1 : ℝ) * x + t) * f₂ ((1 : ℝ) * x + t ^ 2)) volume := by
      exact h₁t.integrable_mul h₂t
    have hprodNorm : Integrable (fun x : ℝ ↦
        ‖f₁ ((1 : ℝ) * x + t)‖ * ‖f₂ ((1 : ℝ) * x + t ^ 2)‖) volume := by
      simpa only [norm_mul] using hprod.norm
    calc
      ∫ x : ℝ, ‖B t x‖ = ∫ x : ℝ,
          ‖f₀ x‖ *
            (‖f₁ ((1 : ℝ) * x + t)‖ * ‖f₂ ((1 : ℝ) * x + t ^ 2)‖) := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp [B]
        rw [norm_mul, norm_mul]
        simp [one_mul]
      _ ≤ ∫ x : ℝ, N *
          (‖f₁ ((1 : ℝ) * x + t)‖ * ‖f₂ ((1 : ℝ) * x + t ^ 2)‖) := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x ↦
            mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
          (hprodNorm.const_mul N)
        filter_upwards [hNbound] with x hx
        exact mul_le_mul_of_nonneg_right hx
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = N * ∫ x : ℝ,
          ‖f₁ ((1 : ℝ) * x + t)‖ * ‖f₂ ((1 : ℝ) * x + t ^ 2)‖ := by
        rw [integral_const_mul]
      _ ≤ C := by
        dsimp [C, D]
        have haffine :
            ∫ x : ℝ, ‖f₁ ((1 : ℝ) * x + t)‖ * ‖f₂ ((1 : ℝ) * x + t ^ 2)‖ ≤ D := by
          dsimp [D]
          simpa only [one_mul, inv_one, abs_one, one_mul] using
            aux_gowersFourier_integral_norm_mul_comp_affine_le_scaled
              f₁ f₂ hf₁ hf₂ 1 1 t (t ^ 2) one_ne_zero one_ne_zero
        exact mul_le_mul_of_nonneg_left haffine hNnonneg
  have hraw := aux_trilinearIntegrand_integrable_l2 χ f₀ f₁ f₂ hχ hf₀ hf₁ hf₂
  have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ)
      (volume.prod volume) (volume.prod volume) := Measure.measurePreserving_swap
  have hcomp : Integrable (aux_u3_trilinearIntegrand f₀ f₁ f₂ χ ∘ Prod.swap)
      (volume.prod volume) :=
    (hswap.integrable_comp hraw.aestronglyMeasurable).mpr hraw
  have hjoint : Integrable (fun z : ℝ × ℝ ↦ (χ z.1 : ℂ) * B z.1 z.2)
      (volume.prod volume) := by
    convert hcomp using 1
    funext z
    dsimp [B, Function.comp_def, aux_u3_trilinearIntegrand]
    ring
  have hjointBound :
      ∫ z : ℝ × ℝ, ‖(χ z.1 : ℂ) * B z.1 z.2‖ ≤
        (∫ t : ℝ, ‖(χ t : ℂ)‖) * C := by
    calc
      ∫ z : ℝ × ℝ, ‖(χ z.1 : ℂ) * B z.1 z.2‖ =
          ∫ t : ℝ, ∫ x : ℝ, ‖(χ t : ℂ) * B t x‖ :=
        integral_prod _ hjoint.norm
      _ = ∫ t : ℝ, ‖(χ t : ℂ)‖ * ∫ x : ℝ, ‖B t x‖ := by
        apply integral_congr_ae
        filter_upwards with t
        rw [show (fun x : ℝ ↦ ‖(χ t : ℂ) * B t x‖) =
          fun x ↦ ‖(χ t : ℂ)‖ * ‖B t x‖ by
            funext x
            rw [norm_mul]]
        rw [integral_const_mul]
      _ ≤ ∫ t : ℝ, ‖(χ t : ℂ)‖ * C := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun t ↦
            mul_nonneg (norm_nonneg _) (integral_nonneg fun x ↦ norm_nonneg _))
          (hχ.norm.mul_const C)
        filter_upwards with t
        exact mul_le_mul_of_nonneg_left (hBbound t) (norm_nonneg _)
      _ = _ := integral_mul_const C (fun t : ℝ ↦ ‖(χ t : ℂ)‖)
  have hnormSwap :
      ∫ z : ℝ × ℝ, ‖aux_u3_trilinearIntegrand f₀ f₁ f₂ χ z‖ =
        ∫ z : ℝ × ℝ, ‖(χ z.1 : ℂ) * B z.1 z.2‖ := by
    calc
      ∫ z : ℝ × ℝ, ‖aux_u3_trilinearIntegrand f₀ f₁ f₂ χ z‖ =
          ∫ z : ℝ × ℝ, ‖(χ z.swap.1 : ℂ) * B z.swap.1 z.swap.2‖ := by
        apply integral_congr_ae
        filter_upwards with z
        dsimp [B, aux_u3_trilinearIntegrand]
        ring_nf
      _ = _ := hswap.integral_comp MeasurableEquiv.prodComm.measurableEmbedding
        (fun z : ℝ × ℝ ↦ ‖(χ z.1 : ℂ) * B z.1 z.2‖)
  calc
    ∫ z : ℝ × ℝ, ‖aux_u3_trilinearIntegrand f₀ f₁ f₂ χ z‖ =
        ∫ z : ℝ × ℝ, ‖(χ z.1 : ℂ) * B z.1 z.2‖ := hnormSwap
    _ ≤ (∫ t : ℝ, ‖(χ t : ℂ)‖) * C := hjointBound
    _ = _ := by
      dsimp [C, D, N]
      ring

/-- Identifies the elementary square-integral expression with the `L²`
norm used in `prop:dyadic-l2-decay` and `dyadicL2Smoothing`. -/
theorem aux_l2_root_integral_eq_eLpNorm (f : ℝ → ℂ)
    (hf : MemLp f (2 : ℝ≥0∞) volume) :
    (∫ x : ℝ, ‖f x‖ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) =
      (eLpNorm f (2 : ℝ≥0∞) volume).toReal := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num
  rw [ENNReal.toReal_ofReal (by positivity)]

/-- The raw `L∞ × L² × L²` trilinear estimate used to pass the interpolated
form to arbitrary representatives in `prop:dyadic-l2-decay` and
`dyadicL2Smoothing`. -/
theorem aux_trilinearFormAbs_le_linf_l2_l2
    (χ : ℝ → ℝ) (f₀ f₁ f₂ : ℝ → ℂ)
    (hχ : Integrable (fun t : ℝ ↦ (χ t : ℂ)))
    (hf₀ : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁ : MemLp f₁ (2 : ℝ≥0∞) volume)
    (hf₂ : MemLp f₂ (2 : ℝ≥0∞) volume) :
    trilinearFormAbs χ f₀ f₁ f₂ ≤
      (∫ t : ℝ, ‖(χ t : ℂ)‖) *
        (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
          (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal *
            (eLpNorm f₂ (2 : ℝ≥0∞) volume).toReal := by
  have hF := aux_trilinearIntegrand_integrable_l2 χ f₀ f₁ f₂ hχ hf₀ hf₁ hf₂
  have hnorm := aux_trilinearIntegrand_norm_integral_le_linf_l2_l2 χ f₀ f₁ f₂
    hχ hf₀ hf₁ hf₂
  unfold trilinearFormAbs
  let F : ℝ × ℝ → ℂ := aux_u3_trilinearIntegrand f₀ f₁ f₂ χ
  change ‖∫ x : ℝ, ∫ t : ℝ, F (x, t)‖ ≤ _
  calc
    ‖∫ x : ℝ, ∫ t : ℝ, F (x, t)‖ ≤
        ∫ x : ℝ, ‖∫ t : ℝ, F (x, t)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, ∫ t : ℝ, ‖F (x, t)‖ := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun x ↦ norm_nonneg _)
        hF.norm.integral_prod_left
      filter_upwards with x
      exact norm_integral_le_integral_norm _
    _ = ∫ z : ℝ × ℝ, ‖F z‖ := (integral_prod _ hF.norm).symm
    _ ≤ (∫ t : ℝ, ‖(χ t : ℂ)‖) *
        (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
          ((∫ x : ℝ, ‖f₁ x‖ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) *
            (∫ x : ℝ, ‖f₂ x‖ ^ (2 : ℕ)) ^ (1 / (2 : ℝ))) := by
      simpa [F] using hnorm
    _ = _ := by
      rw [aux_l2_root_integral_eq_eLpNorm f₁ hf₁,
        aux_l2_root_integral_eq_eLpNorm f₂ hf₂]
      ring

/-- Selects compact-simple `L²` approximants for the density passage in
`prop:dyadic-l2-decay`, formalized by `dyadicL2Smoothing`. -/
theorem aux_compactSimple_sequence_approximation
    (f : ℝ → ℂ) (hf : MemLp f (2 : ℝ≥0∞) volume) :
    ∃ u : ℕ → CompactSimple,
      Filter.Tendsto (fun n ↦ compactSimpleToLpTwo (u n)) Filter.atTop
        (𝓝 (hf.toLp f)) := by
  have hclosure : hf.toLp f ∈ closure (Set.range compactSimpleToLpTwo) :=
    aux_compactSimpleToLpTwo_denseRange (hf.toLp f)
  rcases mem_closure_iff_seq_limit.mp hclosure with ⟨v, hv, hvlim⟩
  let u : ℕ → CompactSimple := fun n ↦ (hv n).choose
  have hu : ∀ n : ℕ, compactSimpleToLpTwo (u n) = v n :=
    fun n ↦ (hv n).choose_spec
  refine ⟨u, ?_⟩
  refine hvlim.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
  exact (hu n).symm

/-- Subtraction compatibility of the dyadic piece on `L²`, used in the raw
continuity step for `prop:dyadic-l2-decay` and `dyadicL2Smoothing`. -/
theorem aux_Q_sub_of_memLp_two (k : ℕ) (f g : ℝ → ℂ)
    (hf : MemLp f (2 : ℝ≥0∞) volume)
    (hg : MemLp g (2 : ℝ≥0∞) volume) :
    Q k (f - g) = Q k f - Q k g := by
  have hneg : MemLp ((-1 : ℂ) • g) (2 : ℝ≥0∞) volume := hg.const_smul (-1 : ℂ)
  rw [show f - g = f + (-1 : ℂ) • g by
    ext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring]
  rw [aux_Q_add_of_memLp_two k f ((-1 : ℂ) • g) hf hneg, aux_Q_smul]
  ext x
  change Q k f x + (-1 : ℂ) * Q k g x = Q k f x - Q k g x
  ring

/-- The dyadic piece preserves `L²` convergence, providing the final-input
continuity bridge for `prop:dyadic-l2-decay` and `dyadicL2Smoothing`. -/
theorem aux_Q_tendsto_l2 (k : ℕ) (u : ℕ → ℝ → ℂ) (f : ℝ → ℂ)
    (hu : ∀ n : ℕ, MemLp (u n) (2 : ℝ≥0∞) volume)
    (hf : MemLp f (2 : ℝ≥0∞) volume)
    (hconv : Filter.Tendsto (fun n ↦ (hu n).toLp (u n)) Filter.atTop
      (𝓝 (hf.toLp f))) :
    Filter.Tendsto
      (fun n ↦ (aux_Q_memLp_two k (u n) (hu n)).toLp (Q k (u n))) Filter.atTop
      (𝓝 ((aux_Q_memLp_two k f hf).toLp (Q k f))) := by
  have hEN : Filter.Tendsto
      (fun n ↦ eLpNorm (u n - f) (2 : ℝ≥0∞) volume) Filter.atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' u hu f hf).mp hconv
  have hupper : Filter.Tendsto
      (fun n ↦ (2 : ℝ≥0∞) ^ 6 * eLpNorm (u n - f) (2 : ℝ≥0∞) volume)
      Filter.atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hEN
      (a := (2 : ℝ≥0∞) ^ 6) (Or.inr (by norm_num : (2 : ℝ≥0∞) ^ 6 ≠ ∞))
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n ↦ Q k (u n)) (fun n ↦ aux_Q_memLp_two k (u n) (hu n))
    (Q k f) (aux_Q_memLp_two k f hf)).mpr
  refine Filter.Tendsto.squeeze tendsto_const_nhds hupper ?_ ?_
  · intro n
    exact bot_le
  · intro n
    change eLpNorm (Q k (u n) - Q k f) (2 : ℝ≥0∞) volume ≤
      (2 : ℝ≥0∞) ^ 6 * eLpNorm (u n - f) (2 : ℝ≥0∞) volume
    rw [← aux_Q_sub_of_memLp_two k (u n) f (hu n) hf]
    exact aux_eLpNorm_Q_le (u n - f) ((hu n).sub hf) k 2 (by norm_num)

/-- Exact middle-variable subtraction for the raw `L²` form in
`prop:dyadic-l2-decay` and `dyadicL2Smoothing`. -/
theorem aux_trilinearForm_sub_middle_l2
    (χ : ℝ → ℝ) (f₀ f₁ g₁ f₂ : ℝ → ℂ)
    (hχ : Integrable (fun t : ℝ ↦ (χ t : ℂ)))
    (hf₀ : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁ : MemLp f₁ (2 : ℝ≥0∞) volume)
    (hg₁ : MemLp g₁ (2 : ℝ≥0∞) volume)
    (hf₂ : MemLp f₂ (2 : ℝ≥0∞) volume) :
    trilinearForm χ f₀ (f₁ - g₁) f₂ =
      trilinearForm χ f₀ f₁ f₂ - trilinearForm χ f₀ g₁ f₂ := by
  have hsub : MemLp (f₁ - g₁) (2 : ℝ≥0∞) volume := hf₁.sub hg₁
  have hFsub := aux_trilinearIntegrand_integrable_l2 χ f₀ (f₁ - g₁) f₂
    hχ hf₀ hsub hf₂
  have hF₁ := aux_trilinearIntegrand_integrable_l2 χ f₀ f₁ f₂ hχ hf₀ hf₁ hf₂
  have hG₁ := aux_trilinearIntegrand_integrable_l2 χ f₀ g₁ f₂ hχ hf₀ hg₁ hf₂
  have hEqSub : trilinearForm χ f₀ (f₁ - g₁) f₂ =
      ∫ z : ℝ × ℝ, aux_u3_trilinearIntegrand f₀ (f₁ - g₁) f₂ χ z := by
    unfold trilinearForm
    exact (integral_prod _ hFsub).symm
  have hEqF : trilinearForm χ f₀ f₁ f₂ =
      ∫ z : ℝ × ℝ, aux_u3_trilinearIntegrand f₀ f₁ f₂ χ z := by
    unfold trilinearForm
    exact (integral_prod _ hF₁).symm
  have hEqG : trilinearForm χ f₀ g₁ f₂ =
      ∫ z : ℝ × ℝ, aux_u3_trilinearIntegrand f₀ g₁ f₂ χ z := by
    unfold trilinearForm
    exact (integral_prod _ hG₁).symm
  rw [hEqSub, hEqF, hEqG]
  calc
    ∫ z : ℝ × ℝ, aux_u3_trilinearIntegrand f₀ (f₁ - g₁) f₂ χ z =
        ∫ z : ℝ × ℝ,
          (aux_u3_trilinearIntegrand f₀ f₁ f₂ χ z -
            aux_u3_trilinearIntegrand f₀ g₁ f₂ χ z) := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [aux_u3_trilinearIntegrand, Pi.sub_apply]
      ring
    _ = _ := integral_sub hF₁ hG₁

/-- Exact last-variable subtraction for the raw `L²` form in
`prop:dyadic-l2-decay` and `dyadicL2Smoothing`. -/
theorem aux_trilinearForm_sub_last_l2
    (χ : ℝ → ℝ) (f₀ f₁ f₂ g₂ : ℝ → ℂ)
    (hχ : Integrable (fun t : ℝ ↦ (χ t : ℂ)))
    (hf₀ : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁ : MemLp f₁ (2 : ℝ≥0∞) volume)
    (hf₂ : MemLp f₂ (2 : ℝ≥0∞) volume)
    (hg₂ : MemLp g₂ (2 : ℝ≥0∞) volume) :
    trilinearForm χ f₀ f₁ (f₂ - g₂) =
      trilinearForm χ f₀ f₁ f₂ - trilinearForm χ f₀ f₁ g₂ := by
  have hsub : MemLp (f₂ - g₂) (2 : ℝ≥0∞) volume := hf₂.sub hg₂
  have hFsub := aux_trilinearIntegrand_integrable_l2 χ f₀ f₁ (f₂ - g₂)
    hχ hf₀ hf₁ hsub
  have hF₂ := aux_trilinearIntegrand_integrable_l2 χ f₀ f₁ f₂ hχ hf₀ hf₁ hf₂
  have hG₂ := aux_trilinearIntegrand_integrable_l2 χ f₀ f₁ g₂ hχ hf₀ hf₁ hg₂
  have hEqSub : trilinearForm χ f₀ f₁ (f₂ - g₂) =
      ∫ z : ℝ × ℝ, aux_u3_trilinearIntegrand f₀ f₁ (f₂ - g₂) χ z := by
    unfold trilinearForm
    exact (integral_prod _ hFsub).symm
  have hEqF : trilinearForm χ f₀ f₁ f₂ =
      ∫ z : ℝ × ℝ, aux_u3_trilinearIntegrand f₀ f₁ f₂ χ z := by
    unfold trilinearForm
    exact (integral_prod _ hF₂).symm
  have hEqG : trilinearForm χ f₀ f₁ g₂ =
      ∫ z : ℝ × ℝ, aux_u3_trilinearIntegrand f₀ f₁ g₂ χ z := by
    unfold trilinearForm
    exact (integral_prod _ hG₂).symm
  rw [hEqSub, hEqF, hEqG]
  calc
    ∫ z : ℝ × ℝ, aux_u3_trilinearIntegrand f₀ f₁ (f₂ - g₂) χ z =
        ∫ z : ℝ × ℝ,
          (aux_u3_trilinearIntegrand f₀ f₁ f₂ χ z -
            aux_u3_trilinearIntegrand f₀ f₁ g₂ χ z) := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [aux_u3_trilinearIntegrand, Pi.sub_apply]
      ring
    _ = _ := integral_sub hF₂ hG₂

/-- The quantitative middle-variable `L²` continuity bound for
`prop:dyadic-l2-decay` and `dyadicL2Smoothing`. -/
theorem aux_trilinearForm_difference_middle_l2_bound
    (χ : ℝ → ℝ) (f₀ f₁ g₁ f₂ : ℝ → ℂ)
    (hχ : Integrable (fun t : ℝ ↦ (χ t : ℂ)))
    (hf₀ : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁ : MemLp f₁ (2 : ℝ≥0∞) volume)
    (hg₁ : MemLp g₁ (2 : ℝ≥0∞) volume)
    (hf₂ : MemLp f₂ (2 : ℝ≥0∞) volume) :
    ‖trilinearForm χ f₀ f₁ f₂ - trilinearForm χ f₀ g₁ f₂‖ ≤
      (∫ t : ℝ, ‖(χ t : ℂ)‖) *
        (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
          (eLpNorm (f₁ - g₁) (2 : ℝ≥0∞) volume).toReal *
            (eLpNorm f₂ (2 : ℝ≥0∞) volume).toReal := by
  rw [← aux_trilinearForm_sub_middle_l2 χ f₀ f₁ g₁ f₂ hχ hf₀ hf₁ hg₁ hf₂]
  exact aux_trilinearFormAbs_le_linf_l2_l2 χ f₀ (f₁ - g₁) f₂ hχ hf₀
    (hf₁.sub hg₁) hf₂

/-- The quantitative last-variable `L²` continuity bound for
`prop:dyadic-l2-decay` and `dyadicL2Smoothing`. -/
theorem aux_trilinearForm_difference_last_l2_bound
    (χ : ℝ → ℝ) (f₀ f₁ f₂ g₂ : ℝ → ℂ)
    (hχ : Integrable (fun t : ℝ ↦ (χ t : ℂ)))
    (hf₀ : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁ : MemLp f₁ (2 : ℝ≥0∞) volume)
    (hf₂ : MemLp f₂ (2 : ℝ≥0∞) volume)
    (hg₂ : MemLp g₂ (2 : ℝ≥0∞) volume) :
    ‖trilinearForm χ f₀ f₁ f₂ - trilinearForm χ f₀ f₁ g₂‖ ≤
      (∫ t : ℝ, ‖(χ t : ℂ)‖) *
        (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
          (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal *
            (eLpNorm (f₂ - g₂) (2 : ℝ≥0∞) volume).toReal := by
  rw [← aux_trilinearForm_sub_last_l2 χ f₀ f₁ f₂ g₂ hχ hf₀ hf₁ hf₂ hg₂]
  exact aux_trilinearFormAbs_le_linf_l2_l2 χ f₀ f₁ (f₂ - g₂) hχ hf₀ hf₁
    (hf₂.sub hg₂)

/-- Raw middle-variable convergence from `L²` convergence for
`prop:dyadic-l2-decay` and `dyadicL2Smoothing`. -/
theorem aux_trilinearForm_tendsto_middle_l2
    (χ : ℝ → ℝ) (f₀ f₂ f : ℝ → ℂ) (u : ℕ → ℝ → ℂ)
    (hχ : Integrable (fun t : ℝ ↦ (χ t : ℂ)))
    (hf₀ : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₂ : MemLp f₂ (2 : ℝ≥0∞) volume)
    (hu : ∀ n : ℕ, MemLp (u n) (2 : ℝ≥0∞) volume)
    (hf : MemLp f (2 : ℝ≥0∞) volume)
    (hconv : Filter.Tendsto (fun n ↦ (hu n).toLp (u n)) Filter.atTop
      (𝓝 (hf.toLp f))) :
    Filter.Tendsto (fun n ↦ trilinearForm χ f₀ (u n) f₂) Filter.atTop
      (𝓝 (trilinearForm χ f₀ f f₂)) := by
  have hEN : Filter.Tendsto
      (fun n ↦ eLpNorm (u n - f) (2 : ℝ≥0∞) volume) Filter.atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' u hu f hf).mp hconv
  have hdiff : Filter.Tendsto
      (fun n ↦ (eLpNorm (u n - f) (2 : ℝ≥0∞) volume).toReal)
      Filter.atTop (𝓝 0) := by
    change Filter.Tendsto
      (ENNReal.toReal ∘ fun n ↦ eLpNorm (u n - f) (2 : ℝ≥0∞) volume)
      Filter.atTop (𝓝 0)
    exact (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hEN
  let K : ℝ := (∫ t : ℝ, ‖(χ t : ℂ)‖) *
    (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal
  let L : ℝ := (eLpNorm f₂ (2 : ℝ≥0∞) volume).toReal
  have hupper : Filter.Tendsto
      (fun n ↦ K * (eLpNorm (u n - f) (2 : ℝ≥0∞) volume).toReal * L)
      Filter.atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hdiff).mul tendsto_const_nhds
  have hnorm : Filter.Tendsto
      (fun n ↦ ‖trilinearForm χ f₀ (u n) f₂ - trilinearForm χ f₀ f f₂‖)
      Filter.atTop (𝓝 0) := by
    refine Filter.Tendsto.squeeze tendsto_const_nhds hupper ?_ ?_
    · intro n
      exact norm_nonneg _
    · intro n
      simpa [K, L, mul_assoc] using
        aux_trilinearForm_difference_middle_l2_bound χ f₀ (u n) f f₂ hχ hf₀
          (hu n) hf hf₂
  have hzero : Filter.Tendsto
      (fun n ↦ trilinearForm χ f₀ (u n) f₂ - trilinearForm χ f₀ f f₂)
      Filter.atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hconst : Filter.Tendsto (fun _ : ℕ ↦ trilinearForm χ f₀ f f₂)
      Filter.atTop (𝓝 (trilinearForm χ f₀ f f₂)) := tendsto_const_nhds
  simpa only [sub_add_cancel, zero_add] using hzero.add hconst

/-- Raw last-variable convergence from `L²` convergence for
`prop:dyadic-l2-decay` and `dyadicL2Smoothing`. -/
theorem aux_trilinearForm_tendsto_last_l2
    (χ : ℝ → ℝ) (f₀ f₁ f : ℝ → ℂ) (u : ℕ → ℝ → ℂ)
    (hχ : Integrable (fun t : ℝ ↦ (χ t : ℂ)))
    (hf₀ : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁ : MemLp f₁ (2 : ℝ≥0∞) volume)
    (hu : ∀ n : ℕ, MemLp (u n) (2 : ℝ≥0∞) volume)
    (hf : MemLp f (2 : ℝ≥0∞) volume)
    (hconv : Filter.Tendsto (fun n ↦ (hu n).toLp (u n)) Filter.atTop
      (𝓝 (hf.toLp f))) :
    Filter.Tendsto (fun n ↦ trilinearForm χ f₀ f₁ (u n)) Filter.atTop
      (𝓝 (trilinearForm χ f₀ f₁ f)) := by
  have hEN : Filter.Tendsto
      (fun n ↦ eLpNorm (u n - f) (2 : ℝ≥0∞) volume) Filter.atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' u hu f hf).mp hconv
  have hdiff : Filter.Tendsto
      (fun n ↦ (eLpNorm (u n - f) (2 : ℝ≥0∞) volume).toReal)
      Filter.atTop (𝓝 0) := by
    change Filter.Tendsto
      (ENNReal.toReal ∘ fun n ↦ eLpNorm (u n - f) (2 : ℝ≥0∞) volume)
      Filter.atTop (𝓝 0)
    exact (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hEN
  let K : ℝ := (∫ t : ℝ, ‖(χ t : ℂ)‖) *
    (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal
  let L : ℝ := (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal
  have hupper : Filter.Tendsto
      (fun n ↦ K * L * (eLpNorm (u n - f) (2 : ℝ≥0∞) volume).toReal)
      Filter.atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul tendsto_const_nhds).mul hdiff
  have hnorm : Filter.Tendsto
      (fun n ↦ ‖trilinearForm χ f₀ f₁ (u n) - trilinearForm χ f₀ f₁ f‖)
      Filter.atTop (𝓝 0) := by
    refine Filter.Tendsto.squeeze tendsto_const_nhds hupper ?_ ?_
    · intro n
      exact norm_nonneg _
    · intro n
      simpa [K, L, mul_assoc] using
        aux_trilinearForm_difference_last_l2_bound χ f₀ f₁ (u n) f hχ hf₀ hf₁
          (hu n) hf
  have hzero : Filter.Tendsto
      (fun n ↦ trilinearForm χ f₀ f₁ (u n) - trilinearForm χ f₀ f₁ f)
      Filter.atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hconst : Filter.Tendsto (fun _ : ℕ ↦ trilinearForm χ f₀ f₁ f)
      Filter.atTop (𝓝 (trilinearForm χ f₀ f₁ f)) := tendsto_const_nhds
  simpa only [sub_add_cancel, zero_add] using hzero.add hconst

/-- The interaction size parameter controls `1 + supportRadius`; this is
the scalar input that absorbs the nondecaying endpoint in
`prop:dyadic-l2-decay`, formalized by `dyadicL2Smoothing`. -/
theorem aux_mainInteraction_one_add_supportRadius_le_size
    (a b : ℝ) (χ : ℝ → ℝ) :
    1 + supportRadius χ ≤ sizeParameter ![
      aux_mainInteractionA0 a b,
      aux_mainInteractionA1 a b χ,
      aux_mainInteractionA2 a b χ,
      aux_mainInteractionJ χ] χ := by
  let R := supportRadius χ
  let I : Fin 4 → Set ℝ := ![
    aux_mainInteractionA0 a b,
    aux_mainInteractionA1 a b χ,
    aux_mainInteractionA2 a b χ,
    aux_mainInteractionJ χ]
  have hquad : 1 + R ≤ 2 + R ^ 2 := by
    nlinarith [sq_nonneg (R - 1 / 2)]
  have hrad : R ^ 2 ≤ max (sSup (Set.range fun i ↦ intervalLength (I i)))
      (max (R ^ 2)
        (max (eLpNorm χ 1 volume).toReal
          (max (eLpNorm χ 2 volume).toReal
            (max (eLpNorm (deriv χ) 1 volume).toReal
              (eLpNorm (deriv χ) 2 volume).toReal)))) := by
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  change 1 + R ≤ 2 + max (sSup (Set.range fun i ↦ intervalLength (I i)))
    (max (R ^ 2)
      (max (eLpNorm χ 1 volume).toReal
        (max (eLpNorm χ 2 volume).toReal
          (max (eLpNorm (deriv χ) 1 volume).toReal
            (eLpNorm (deriv χ) 2 volume).toReal))))
  linarith

/-- Bounds the nondecaying quadratic-endpoint constant by four times the
interaction size in `prop:dyadic-l2-decay`, formalized by
`dyadicL2Smoothing`. -/
theorem aux_quadraticEndpointConstant_le_mainInteraction_size
    (a b : ℝ) (χ : ℝ → ℝ) (hχcompact : HasCompactSupport χ) :
    C_quadraticAveragingOperator χ ≤ 4 * sizeParameter ![
      aux_mainInteractionA0 a b,
      aux_mainInteractionA1 a b χ,
      aux_mainInteractionA2 a b χ,
      aux_mainInteractionJ χ] χ := by
  let R := supportRadius χ
  let S := sizeParameter ![
    aux_mainInteractionA0 a b,
    aux_mainInteractionA1 a b χ,
    aux_mainInteractionA2 a b χ,
    aux_mainInteractionJ χ] χ
  have hR : 0 ≤ R := zero_le_one.trans (aux_u3_one_le_supportRadius χ hχcompact)
  have hbase : 1 ≤ 1 + R := by linarith
  have hRS : 1 + R ≤ S := by
    simpa [R, S] using aux_mainInteraction_one_add_supportRadius_le_size a b χ
  have hpow : (1 + R) ^ (1 / (3 : ℝ)) ≤ S := by
    calc
      (1 + R) ^ (1 / (3 : ℝ)) ≤ (1 + R) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
      _ = 1 + R := by rw [Real.rpow_one]
      _ ≤ S := hRS
  change (2 : ℝ) ^ 2 * (1 + R) ^ (1 / (3 : ℝ)) ≤ 4 * S
  calc
    (2 : ℝ) ^ 2 * (1 + R) ^ (1 / (3 : ℝ)) =
        4 * (1 + R) ^ (1 / (3 : ℝ)) := by norm_num
    _ ≤ 4 * S := mul_le_mul_of_nonneg_left hpow (by norm_num)

/-- Computes the quarter of the dyadic decay exponent arising in
`prop:dyadic-l2-decay`, formalized by `dyadicL2Smoothing`. -/
theorem aux_dyadicL2_quarter_decay (k : ℕ) :
    ((2 : ℝ) ^ (-((2 : ℝ) ^ (-11 : ℝ)) * (k : ℝ))) ^ (1 / (4 : ℝ)) =
      (2 : ℝ) ^ (-((2 : ℝ) ^ (-13 : ℝ)) * (k : ℝ)) := by
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h11 : (2 : ℝ) ^ (-11 : ℝ) = 1 / 2048 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h13 : (2 : ℝ) ^ (-13 : ℝ) = 1 / 8192 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [h11, h13]
  congr 1
  ring

/-- Interpolates the two explicit powers of two in
`prop:dyadic-l2-decay`, formalized by `dyadicL2Smoothing`. -/
theorem aux_dyadicL2_two_constant_interpolation :
    ((2 : ℝ) ^ 13) ^ (1 / (4 : ℝ)) *
      ((2 : ℝ) ^ 8) ^ (3 / (4 : ℝ)) ≤ (2 : ℝ) ^ 10 := by
  have h13 : ((2 : ℝ) ^ 13) ^ (1 / (4 : ℝ)) =
      (2 : ℝ) ^ ((13 : ℝ) * (1 / (4 : ℝ))) := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) 13 (1 / (4 : ℝ))).symm
  have h8 : ((2 : ℝ) ^ 8) ^ (3 / (4 : ℝ)) =
      (2 : ℝ) ^ ((8 : ℝ) * (3 / (4 : ℝ))) := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) 8 (3 / (4 : ℝ))).symm
  rw [h13, h8, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  norm_num

/-- Interpolates the size-parameter contribution in
`prop:dyadic-l2-decay`, formalized by `dyadicL2Smoothing`. -/
theorem aux_dyadicL2_size_interpolation (S : ℝ) (hS : 2 ≤ S) :
    (S ^ (4 : ℕ)) ^ (1 / (4 : ℝ)) * S ^ (3 / (4 : ℝ)) ≤ S ^ (2 : ℝ) := by
  have hS0 : 0 ≤ S := by linarith
  have hSpos : 0 < S := by linarith
  have hfirst : (S ^ (4 : ℕ)) ^ (1 / (4 : ℝ)) = S := by
    rw [← Real.rpow_natCast]
    calc
      (S ^ (4 : ℝ)) ^ (1 / (4 : ℝ)) =
          S ^ ((4 : ℝ) * (1 / (4 : ℝ))) :=
        (Real.rpow_mul hS0 4 (1 / (4 : ℝ))).symm
      _ = S := by norm_num
  rw [hfirst]
  calc
    S * S ^ (3 / (4 : ℝ)) = S ^ (1 : ℝ) * S ^ (3 / (4 : ℝ)) := by
      rw [Real.rpow_one]
    _ = S ^ ((1 : ℝ) + 3 / 4) := (Real.rpow_add hSpos 1 (3 / 4)).symm
    _ ≤ S ^ (2 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      norm_num

/-- Combines the two interpolation powers of a nonnegative norm factor in
`prop:dyadic-l2-decay`, formalized by `dyadicL2Smoothing`. -/
theorem aux_dyadicL2_norm_interpolation (N : ℝ) (hN : 0 ≤ N) :
    N ^ (1 / (4 : ℝ)) * N ^ (3 / (4 : ℝ)) = N := by
  by_cases hzero : N = 0
  · simp [hzero]
  · have hpos : 0 < N := lt_of_le_of_ne hN (Ne.symm hzero)
    rw [← Real.rpow_add hpos]
    norm_num

/-- Performs the scalar interpolation calculation with the schematic
`2⁸ S` second endpoint from `prop:dyadic-l2-decay`, formalized by
`dyadicL2Smoothing`. -/
theorem aux_dyadicL2_interpolation_numeric (S N : ℝ) (k : ℕ)
    (hS : 2 ≤ S) (hN : 0 ≤ N) :
    (((2 : ℝ) ^ 13 * S ^ (4 : ℕ) *
      (2 : ℝ) ^ (-((2 : ℝ) ^ (-11 : ℝ)) * (k : ℝ)) * N) ^ (1 / (4 : ℝ))) *
      (((2 : ℝ) ^ 8 * S * N) ^ (3 / (4 : ℝ))) ≤
      (2 : ℝ) ^ 10 * S ^ (2 : ℝ) *
        (2 : ℝ) ^ (-((2 : ℝ) ^ (-13 : ℝ)) * (k : ℝ)) * N := by
  have hS0 : 0 ≤ S := by linarith
  have hD0 : 0 ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ (-11 : ℝ)) * (k : ℝ)) := by positivity
  have hA0 :
      ((2 : ℝ) ^ 13 * S ^ (4 : ℕ) *
        (2 : ℝ) ^ (-((2 : ℝ) ^ (-11 : ℝ)) * (k : ℝ)) * N) ^ (1 / (4 : ℝ)) =
        ((2 : ℝ) ^ 13) ^ (1 / (4 : ℝ)) *
          (S ^ (4 : ℕ)) ^ (1 / (4 : ℝ)) *
            ((2 : ℝ) ^ (-((2 : ℝ) ^ (-11 : ℝ)) * (k : ℝ))) ^ (1 / (4 : ℝ)) *
              N ^ (1 / (4 : ℝ)) := by
    calc
      ((2 : ℝ) ^ 13 * S ^ (4 : ℕ) *
          (2 : ℝ) ^ (-((2 : ℝ) ^ (-11 : ℝ)) * (k : ℝ)) * N) ^ (1 / (4 : ℝ)) =
          (((2 : ℝ) ^ 13 * S ^ (4 : ℕ) *
            (2 : ℝ) ^ (-((2 : ℝ) ^ (-11 : ℝ)) * (k : ℝ))) ^ (1 / (4 : ℝ))) *
              N ^ (1 / (4 : ℝ)) :=
        Real.mul_rpow (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hS0 _)) hD0) hN
      _ = (((2 : ℝ) ^ 13 * S ^ (4 : ℕ)) ^ (1 / (4 : ℝ)) *
            ((2 : ℝ) ^ (-((2 : ℝ) ^ (-11 : ℝ)) * (k : ℝ))) ^ (1 / (4 : ℝ))) *
              N ^ (1 / (4 : ℝ)) := by
        congr 1
        exact Real.mul_rpow (mul_nonneg (by positivity) (pow_nonneg hS0 _)) hD0
      _ = ((2 : ℝ) ^ 13) ^ (1 / (4 : ℝ)) *
            (S ^ (4 : ℕ)) ^ (1 / (4 : ℝ)) *
              ((2 : ℝ) ^ (-((2 : ℝ) ^ (-11 : ℝ)) * (k : ℝ))) ^ (1 / (4 : ℝ)) *
                N ^ (1 / (4 : ℝ)) := by
        congr 2
        exact Real.mul_rpow (by positivity) (pow_nonneg hS0 _)
  have hA1 : ((2 : ℝ) ^ 8 * S * N) ^ (3 / (4 : ℝ)) =
      ((2 : ℝ) ^ 8) ^ (3 / (4 : ℝ)) * S ^ (3 / (4 : ℝ)) *
        N ^ (3 / (4 : ℝ)) := by
    calc
      ((2 : ℝ) ^ 8 * S * N) ^ (3 / (4 : ℝ)) =
          (((2 : ℝ) ^ 8 * S) ^ (3 / (4 : ℝ))) * N ^ (3 / (4 : ℝ)) :=
        Real.mul_rpow (mul_nonneg (by positivity) hS0) hN
      _ = (((2 : ℝ) ^ 8) ^ (3 / (4 : ℝ)) * S ^ (3 / (4 : ℝ))) *
          N ^ (3 / (4 : ℝ)) := by
        congr 1
        exact Real.mul_rpow (by positivity) hS0
      _ = ((2 : ℝ) ^ 8) ^ (3 / (4 : ℝ)) * S ^ (3 / (4 : ℝ)) *
          N ^ (3 / (4 : ℝ)) := by ring
  rw [hA0, hA1, aux_dyadicL2_quarter_decay]
  have hconst := aux_dyadicL2_two_constant_interpolation
  have hsize := aux_dyadicL2_size_interpolation S hS
  have hnorm := aux_dyadicL2_norm_interpolation N hN
  calc
    ((2 : ℝ) ^ 13) ^ (1 / (4 : ℝ)) *
          (S ^ (4 : ℕ)) ^ (1 / (4 : ℝ)) *
            (2 : ℝ) ^ (-((2 : ℝ) ^ (-13 : ℝ)) * (k : ℝ)) * N ^ (1 / (4 : ℝ)) *
        (((2 : ℝ) ^ 8) ^ (3 / (4 : ℝ)) * S ^ (3 / (4 : ℝ)) *
          N ^ (3 / (4 : ℝ))) =
        (((2 : ℝ) ^ 13) ^ (1 / (4 : ℝ)) * ((2 : ℝ) ^ 8) ^ (3 / (4 : ℝ))) *
          ((S ^ (4 : ℕ)) ^ (1 / (4 : ℝ)) * S ^ (3 / (4 : ℝ))) *
            (2 : ℝ) ^ (-((2 : ℝ) ^ (-13 : ℝ)) * (k : ℝ)) *
              (N ^ (1 / (4 : ℝ)) * N ^ (3 / (4 : ℝ))) := by ring
    _ ≤ ((2 : ℝ) ^ 10 * S ^ (2 : ℝ)) *
          (2 : ℝ) ^ (-((2 : ℝ) ^ (-13 : ℝ)) * (k : ℝ)) * N := by
      rw [hnorm]
      gcongr
    _ = (2 : ℝ) ^ 10 * S ^ (2 : ℝ) *
        (2 : ℝ) ^ (-((2 : ℝ) ^ (-13 : ℝ)) * (k : ℝ)) * N := by ring

/-- Performs the complete endpoint-constant interpolation calculation for
`prop:dyadic-l2-decay`, formalized by `dyadicL2Smoothing`. -/
theorem aux_dyadicL2_interpolation_numeric_with_endpoint_constant
    (S N C : ℝ) (k : ℕ) (hS : 2 ≤ S) (hN : 0 ≤ N)
    (hC0 : 0 ≤ C) (hC : C ≤ 4 * S) :
    (((2 : ℝ) ^ 13 * S ^ (4 : ℕ) *
      (2 : ℝ) ^ (-((2 : ℝ) ^ (-11 : ℝ)) * (k : ℝ)) * N) ^ (1 / (4 : ℝ))) *
      ((C * N * (2 : ℝ) ^ 6) ^ (3 / (4 : ℝ))) ≤
      (2 : ℝ) ^ 10 * S ^ (2 : ℝ) *
        (2 : ℝ) ^ (-((2 : ℝ) ^ (-13 : ℝ)) * (k : ℝ)) * N := by
  have hCbound : C * N * (2 : ℝ) ^ 6 ≤ (2 : ℝ) ^ 8 * S * N := by
    calc
      C * N * (2 : ℝ) ^ 6 = C * (N * (2 : ℝ) ^ 6) := by ring
      _ ≤ (4 * S) * (N * (2 : ℝ) ^ 6) :=
        mul_le_mul_of_nonneg_right hC (mul_nonneg hN (by positivity))
      _ = (2 : ℝ) ^ 8 * S * N := by norm_num; ring
  have hbase0 : 0 ≤ C * N * (2 : ℝ) ^ 6 :=
    mul_nonneg (mul_nonneg hC0 hN) (by positivity)
  calc
    (((2 : ℝ) ^ 13 * S ^ (4 : ℕ) *
      (2 : ℝ) ^ (-((2 : ℝ) ^ (-11 : ℝ)) * (k : ℝ)) * N) ^ (1 / (4 : ℝ))) *
        ((C * N * (2 : ℝ) ^ 6) ^ (3 / (4 : ℝ))) ≤
      (((2 : ℝ) ^ 13 * S ^ (4 : ℕ) *
        (2 : ℝ) ^ (-((2 : ℝ) ^ (-11 : ℝ)) * (k : ℝ)) * N) ^ (1 / (4 : ℝ))) *
        (((2 : ℝ) ^ 8 * S * N) ^ (3 / (4 : ℝ))) := by
          apply mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hbase0 hCbound (by norm_num))
          positivity
    _ ≤ (2 : ℝ) ^ 10 * S ^ (2 : ℝ) *
          (2 : ℝ) ^ (-((2 : ℝ) ^ (-13 : ℝ)) * (k : ℝ)) * N :=
      aux_dyadicL2_interpolation_numeric S N k hS hN

/--
Let \(k\geq1\).  Define
\[
C_{\ref{prop:dyadic-l2-decay},\,K,\chi}
=2^{10}\mathcal S(A_0,A_1,A_2,J_\chi;\chi)^2,
\]
where the intervals are those of \(\label{def:main-interaction-data}\).  If
\(f_0\in L^\infty(\mathbb R)\) is supported in \(K=[a,b]\) and
\(f_1,g\in L^2(\mathbb R)\), then
\[
\mathcal I_\chi(f_0,f_1,Q_kg)
\leq C_{\ref{prop:dyadic-l2-decay},\,K,\chi}
2^{-2^{-13}k}\lVert f_0\rVert_\infty
\lVert f_1\rVert_2\lVert g\rVert_2.
\]
-/
theorem dyadicL2Smoothing
    (a b : ℝ) (χ : ℝ → ℝ) (hab : a ≤ b)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (k : ℕ) (hk : 1 ≤ k)
    (f₀ f₁ g : ℝ → ℂ)
    (hf₀_memLp : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁_memLp : MemLp f₁ (2 : ℝ≥0∞) volume)
    (hg_memLp : MemLp g (2 : ℝ≥0∞) volume)
    (hf₀_support : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f₀ x = 0) :
    trilinearFormAbs χ f₀ f₁ (Q k g) ≤
      C_dyadicL2Smoothing a b χ *
        (2 : ℝ) ^ (-((2 : ℝ) ^ (-13 : ℝ)) * (k : ℝ)) *
          (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
            (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal *
              (eLpNorm g (2 : ℝ≥0∞) volume).toReal := by
  let S : ℝ := sizeParameter ![
    aux_mainInteractionA0 a b,
    aux_mainInteractionA1 a b χ,
    aux_mainInteractionA2 a b χ,
    aux_mainInteractionJ χ] χ
  let N : ℝ := (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal
  have hStwo : 2 ≤ S := by
    simpa [S] using aux_two_le_sizeParameter_four
      (aux_mainInteractionA0 a b) (aux_mainInteractionA1 a b χ)
      (aux_mainInteractionA2 a b χ) (aux_mainInteractionJ χ) χ
  have hN0 : 0 ≤ N := by simp [N]
  have hχmem : MemLp χ (1 : ℝ≥0∞) volume :=
    hχ_smooth.continuous.memLp_of_hasCompactSupport hχ_compact
  have hχint : Integrable (fun t : ℝ ↦ (χ t : ℂ)) :=
    memLp_one_iff_integrable.mp hχmem.ofReal
  let T := aux_compactSimpleDyadicFormOf χ f₀ k hχint hf₀_memLp
  let A₀ : ℝ := C_dyadicLInfinityDecay a b χ *
    (2 : ℝ) ^ (-((2 : ℝ) ^ (-11 : ℝ)) * (k : ℝ)) * N
  let A₁ : ℝ := C_quadraticAveragingOperator χ * N * (2 : ℝ) ^ 6
  have hCquad0 : 0 ≤ C_quadraticAveragingOperator χ := by
    unfold C_quadraticAveragingOperator
    have hR : 0 ≤ supportRadius χ :=
      zero_le_one.trans (aux_u3_one_le_supportRadius χ hχ_compact)
    positivity
  have hCquad : C_quadraticAveragingOperator χ ≤ 4 * S := by
    simpa [S] using aux_quadraticEndpointConstant_le_mainInteraction_size a b χ hχ_compact
  have hA₀ : 0 ≤ A₀ := by
    dsimp [A₀, N]
    unfold C_dyadicLInfinityDecay
    positivity
  have hA₁ : 0 ≤ A₁ := by
    dsimp [A₁]
    positivity
  have hInfinity : ∀ f g : CompactSimple,
      ‖T f g‖ ≤ A₀ *
        (eLpNorm (f.1 : ℝ → ℂ) (∞ : ℝ≥0∞) volume).toReal *
          (eLpNorm (g.1 : ℝ → ℂ) (∞ : ℝ≥0∞) volume).toReal := by
    intro f g
    simpa [T, A₀, N] using
      aux_compactSimpleDyadicFormOf_infinity_bound a b χ hab hχ_smooth hχ_compact
        hχ_nonneg hχ_le_one k hk f₀ hχint hf₀_memLp hf₀_support f g
  have hThreeHalves : ∀ f g : CompactSimple,
      ‖T f g‖ ≤ A₁ *
        (eLpNorm (f.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal *
          (eLpNorm (g.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal := by
    intro f g
    simpa [T, A₁, N] using
      aux_compactSimpleDyadicFormOf_threeHalves_bound χ hχ_smooth hχ_compact
        hχ_nonneg hχ_le_one k f₀ hχint hf₀_memLp f g
  rcases specialBilinearInterpolation T A₀ A₁ hA₀ hA₁ hInfinity hThreeHalves with
    ⟨T₂, hagree, hT₂bound⟩
  rcases aux_compactSimple_sequence_approximation f₁ hf₁_memLp with ⟨F, hF⟩
  rcases aux_compactSimple_sequence_approximation g hg_memLp with ⟨G, hG⟩
  have hQg : MemLp (Q k g) (2 : ℝ≥0∞) volume := aux_Q_memLp_two k g hg_memLp
  have hstage : ∀ m : ℕ,
      T₂ (hf₁_memLp.toLp f₁) (compactSimpleToLpTwo (G m)) =
        trilinearForm χ f₀ f₁ (Q k ((G m).1 : ℝ → ℂ)) := by
    intro m
    have hTlim : Filter.Tendsto
        (fun n ↦ T₂ (compactSimpleToLpTwo (F n)) (compactSimpleToLpTwo (G m)))
        Filter.atTop (𝓝 (T₂ (hf₁_memLp.toLp f₁) (compactSimpleToLpTwo (G m)))) := by
      have hcont : Continuous (fun x : Lp (α := ℝ) ℂ 2 volume ↦
          T₂ x (compactSimpleToLpTwo (G m))) := by fun_prop
      exact (hcont.tendsto _).comp hF
    have hrawlim : Filter.Tendsto
        (fun n ↦ trilinearForm χ f₀ ((F n).1 : ℝ → ℂ)
          (Q k ((G m).1 : ℝ → ℂ))) Filter.atTop
        (𝓝 (trilinearForm χ f₀ f₁ (Q k ((G m).1 : ℝ → ℂ)))) := by
      exact aux_trilinearForm_tendsto_middle_l2 χ f₀
        (Q k ((G m).1 : ℝ → ℂ)) f₁
        (fun n ↦ ((F n).1 : ℝ → ℂ)) hχint hf₀_memLp
        (aux_Q_memLp_two k ((G m).1 : ℝ → ℂ) (compactSimpleMemLpTwo (G m)))
        (fun n ↦ compactSimpleMemLpTwo (F n)) hf₁_memLp
        (by simpa [compactSimpleToLpTwo] using hF)
    apply tendsto_nhds_unique_of_eventuallyEq hTlim hrawlim
    filter_upwards with n
    simpa [T, aux_compactSimpleDyadicFormOf, aux_compactSimpleDyadicForm] using
      hagree (F n) (G m)
  have hTouter : Filter.Tendsto
      (fun m ↦ T₂ (hf₁_memLp.toLp f₁) (compactSimpleToLpTwo (G m))) Filter.atTop
      (𝓝 (T₂ (hf₁_memLp.toLp f₁) (hg_memLp.toLp g))) := by
    have hcont : Continuous (fun x : Lp (α := ℝ) ℂ 2 volume ↦ T₂ (hf₁_memLp.toLp f₁) x) := by
      fun_prop
    exact (hcont.tendsto _).comp hG
  have hQconv := aux_Q_tendsto_l2 k (fun m ↦ ((G m).1 : ℝ → ℂ)) g
    (fun m ↦ compactSimpleMemLpTwo (G m)) hg_memLp
    (by simpa [compactSimpleToLpTwo] using hG)
  have hrawouter : Filter.Tendsto
      (fun m ↦ trilinearForm χ f₀ f₁ (Q k ((G m).1 : ℝ → ℂ))) Filter.atTop
      (𝓝 (trilinearForm χ f₀ f₁ (Q k g))) := by
    exact aux_trilinearForm_tendsto_last_l2 χ f₀ f₁ (Q k g)
      (fun m ↦ Q k ((G m).1 : ℝ → ℂ)) hχint hf₀_memLp hf₁_memLp
      (fun m ↦ aux_Q_memLp_two k ((G m).1 : ℝ → ℂ) (compactSimpleMemLpTwo (G m))) hQg
      (by simpa using hQconv)
  have hident : T₂ (hf₁_memLp.toLp f₁) (hg_memLp.toLp g) =
      trilinearForm χ f₀ f₁ (Q k g) := by
    apply tendsto_nhds_unique_of_eventuallyEq hTouter hrawouter
    filter_upwards with m
    exact hstage m
  have hinterp := hT₂bound (hf₁_memLp.toLp f₁) (hg_memLp.toLp g)
  have hraw : trilinearFormAbs χ f₀ f₁ (Q k g) ≤
      A₀ ^ (1 / (4 : ℝ)) * A₁ ^ (3 / (4 : ℝ)) *
        (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal *
          (eLpNorm g (2 : ℝ≥0∞) volume).toReal := by
    rw [hident] at hinterp
    simpa only [trilinearFormAbs, Lp.norm_toLp] using hinterp
  have hcoeff : A₀ ^ (1 / (4 : ℝ)) * A₁ ^ (3 / (4 : ℝ)) ≤
      (2 : ℝ) ^ 10 * S ^ (2 : ℝ) *
        (2 : ℝ) ^ (-((2 : ℝ) ^ (-13 : ℝ)) * (k : ℝ)) * N := by
    dsimp [A₀, A₁]
    simpa [C_dyadicLInfinityDecay, S] using
      aux_dyadicL2_interpolation_numeric_with_endpoint_constant S N
        (C_quadraticAveragingOperator χ) k hStwo hN0 hCquad0 hCquad
  calc
    trilinearFormAbs χ f₀ f₁ (Q k g) ≤
        A₀ ^ (1 / (4 : ℝ)) * A₁ ^ (3 / (4 : ℝ)) *
          (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal *
            (eLpNorm g (2 : ℝ≥0∞) volume).toReal := hraw
    _ ≤ ((2 : ℝ) ^ 10 * S ^ (2 : ℝ) *
        (2 : ℝ) ^ (-((2 : ℝ) ^ (-13 : ℝ)) * (k : ℝ)) * N) *
          (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal *
            (eLpNorm g (2 : ℝ≥0∞) volume).toReal := by
      gcongr
    _ = C_dyadicL2Smoothing a b χ *
        (2 : ℝ) ^ (-((2 : ℝ) ^ (-13 : ℝ)) * (k : ℝ)) *
          (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
            (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal *
              (eLpNorm g (2 : ℝ≥0∞) volume).toReal := by
      simp [C_dyadicL2Smoothing, S, N]

end Auto
