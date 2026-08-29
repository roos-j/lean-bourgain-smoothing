import BourgainSmoothing.Auto.ConventionsAndFoundationalDefinitions
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Explicit auxiliary cutoffs

Formalizations of the labeled definitions and estimates in the corresponding
section of `blueprint/blueprint.tex`.
-/

noncomputable section

namespace Auto

open MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology FourierTransform Convolution SchwartzMap

/--
The polynomial smooth step from \(\label{def:smooth-step}\):
\[
s(u)=0\quad(u\leq0),\qquad
s(u)=3u^2-2u^3\quad(0<u<1),\qquad
s(u)=1\quad(u\geq1).
\]
Then \(s\in C^1(\mathbb R)\cap W^{2,1}_{\mathrm{loc}}(\mathbb R)\).
-/
def smoothStep (u : ℝ) : ℝ :=
  if u ≤ 0 then 0 else if u < 1 then 3 * u ^ 2 - 2 * u ^ 3 else 1

/-- The first derivative model for the polynomial smooth step.  This is used
to prove the explicit norm identities in `smoothStepBounds` for
`\label{lem:smooth-step-bounds}`. -/
noncomputable def aux_smoothStepDerivative (u : ℝ) : ℝ :=
  Set.Ioo 0 1 |>.indicator (fun v ↦ 6 * v - 6 * v ^ 2) u

/-- The second derivative model for the polynomial smooth step.  It agrees
almost everywhere with `deriv (deriv smoothStep)` and is used by
`smoothStepBounds` for `\label{lem:smooth-step-bounds}`. -/
noncomputable def aux_smoothStepSecondDerivative (u : ℝ) : ℝ :=
  Set.Ioo 0 1 |>.indicator (fun v ↦ 6 - 12 * v) u

/-- On the polynomial transition interval, this is the ordinary derivative
of `smoothStep`.  It is an auxiliary local calculation for
`smoothStepBounds` and `\label{lem:smooth-step-bounds}`. -/
lemma aux_smoothStep_deriv_on_Ioo (u : ℝ) (hu_zero : 0 < u) (hu_one : u < 1) :
    deriv smoothStep u = 6 * u - 6 * u ^ 2 := by
  have h2 : HasDerivAt (fun v : ℝ ↦ v ^ 2) (2 * u) u := by
    simpa using
      (hasDerivAt_pow 2 u : HasDerivAt (fun v : ℝ ↦ v ^ 2) (2 * u ^ (2 - 1)) u)
  have h3 : HasDerivAt (fun v : ℝ ↦ v ^ 3) (3 * u ^ 2) u := by
    simpa using
      (hasDerivAt_pow 3 u : HasDerivAt (fun v : ℝ ↦ v ^ 3) (3 * u ^ (3 - 1)) u)
  have hpolynomial := h2.const_mul 3 |>.sub (h3.const_mul 2)
  have hderiv : HasDerivAt (fun v : ℝ ↦ 3 * v ^ 2 - 2 * v ^ 3)
      (6 * u - 6 * u ^ 2) u := by
    have hfun : (fun v : ℝ ↦ 3 * v ^ 2 - 2 * v ^ 3) =ᶠ[𝓝 u]
        ((fun v : ℝ ↦ 3 * v ^ 2) - fun v ↦ 2 * v ^ 3) :=
      Filter.Eventually.of_forall (fun _ ↦ rfl)
    exact (hpolynomial.congr_of_eventuallyEq hfun).congr_deriv (by ring)
  exact (hderiv.congr_of_eventuallyEq (by
    filter_upwards [lt_mem_nhds hu_zero, gt_mem_nhds hu_one] with v hv_zero hv_one
    simp [smoothStep, not_le.mpr hv_zero, hv_one])).deriv

/-- To the left of its transition interval, `smoothStep` has zero derivative.
This supports the a.e. derivative model used in `smoothStepBounds`. -/
lemma aux_smoothStep_deriv_lt_zero (u : ℝ) (hu : u < 0) : deriv smoothStep u = 0 := by
  exact ((hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq (by
    filter_upwards [gt_mem_nhds hu] with v hv
    simp [smoothStep, hv.le])).deriv

/-- To the right of its transition interval, `smoothStep` has zero derivative.
This supports the a.e. derivative model used in `smoothStepBounds`. -/
lemma aux_smoothStep_deriv_gt_one (u : ℝ) (hu : 1 < u) : deriv smoothStep u = 0 := by
  exact ((hasDerivAt_const u (1 : ℝ)).congr_of_eventuallyEq (by
    filter_upwards [lt_mem_nhds hu] with v hv
    have hv_zero : ¬ v ≤ 0 := by linarith
    have hv_one : ¬ v < 1 := by linarith
    simp [smoothStep, hv_zero, hv_one])).deriv

/-- Almost everywhere, the derivative of the polynomial smooth step is its
compactly supported polynomial derivative.  The omitted junction points have
Lebesgue measure zero.  This is an auxiliary fact for `smoothStepBounds`. -/
lemma aux_smoothStep_deriv_ae :
    deriv smoothStep =ᵐ[volume] aux_smoothStepDerivative := by
  have hzero : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have hone : ∀ᵐ u : ℝ ∂volume, u ≠ 1 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hzero, hone] with u hu_zero hu_one
  by_cases hleft : u ≤ 0
  · rw [aux_smoothStepDerivative, Set.indicator_of_notMem]
    · rcases hleft.eq_or_lt with rfl | hlt
      · contradiction
      · exact aux_smoothStep_deriv_lt_zero u hlt
    · simp [hleft]
  by_cases hright : u < 1
  · rw [aux_smoothStepDerivative,
      Set.indicator_of_mem (show u ∈ Set.Ioo 0 1 from ⟨lt_of_not_ge hleft, hright⟩)]
    exact aux_smoothStep_deriv_on_Ioo u (lt_of_not_ge hleft) hright
  · rw [aux_smoothStepDerivative, Set.indicator_of_notMem]
    · have hgt : 1 < u :=
        lt_of_le_of_ne (le_of_not_gt hright) (Ne.symm hu_one)
      exact aux_smoothStep_deriv_gt_one u hgt
    · simp [hright]

/-- On the polynomial transition interval, this is the ordinary derivative
of `deriv smoothStep`.  It is an auxiliary local calculation for
`smoothStepBounds` and `\label{lem:smooth-step-bounds}`. -/
lemma aux_smoothStep_secondDeriv_on_Ioo (u : ℝ) (hu_zero : 0 < u) (hu_one : u < 1) :
    deriv (deriv smoothStep) u = 6 - 12 * u := by
  have hpolynomial : HasDerivAt (fun v : ℝ ↦ 6 * v - 6 * v ^ 2) (6 - 12 * u) u := by
    have h1 : HasDerivAt (fun v : ℝ ↦ v) 1 u := hasDerivAt_id u
    have h2 : HasDerivAt (fun v : ℝ ↦ v ^ 2) (2 * u) u := by
      simpa using
        (hasDerivAt_pow 2 u : HasDerivAt (fun v : ℝ ↦ v ^ 2) (2 * u ^ (2 - 1)) u)
    have hderiv := h1.const_mul 6 |>.sub (h2.const_mul 6)
    have hfun : (fun v : ℝ ↦ 6 * v - 6 * v ^ 2) =ᶠ[𝓝 u]
        ((fun v : ℝ ↦ 6 * v) - fun v ↦ 6 * v ^ 2) :=
      Filter.Eventually.of_forall (fun _ ↦ rfl)
    exact (hderiv.congr_of_eventuallyEq hfun).congr_deriv (by ring)
  exact (hpolynomial.congr_of_eventuallyEq (by
    filter_upwards [lt_mem_nhds hu_zero, gt_mem_nhds hu_one] with v hv_zero hv_one
    exact aux_smoothStep_deriv_on_Ioo v hv_zero hv_one)).deriv

/-- Off the transition interval on the left, the second derivative model of
`smoothStep` vanishes.  This is an auxiliary local calculation for
`smoothStepBounds`. -/
lemma aux_smoothStep_secondDeriv_lt_zero (u : ℝ) (hu : u < 0) :
    deriv (deriv smoothStep) u = 0 := by
  exact ((hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq (by
    filter_upwards [gt_mem_nhds hu] with v hv
    exact aux_smoothStep_deriv_lt_zero v hv)).deriv

/-- Off the transition interval on the right, the second derivative model of
`smoothStep` vanishes.  This is an auxiliary local calculation for
`smoothStepBounds`. -/
lemma aux_smoothStep_secondDeriv_gt_one (u : ℝ) (hu : 1 < u) :
    deriv (deriv smoothStep) u = 0 := by
  exact ((hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq (by
    filter_upwards [lt_mem_nhds hu] with v hv
    exact aux_smoothStep_deriv_gt_one v hv)).deriv

/-- Almost everywhere, the second derivative of the polynomial smooth step is
its compactly supported piecewise polynomial model.  This is an auxiliary
fact for `smoothStepBounds` and `\label{lem:smooth-step-bounds}`. -/
lemma aux_smoothStep_secondDeriv_ae :
    deriv (deriv smoothStep) =ᵐ[volume] aux_smoothStepSecondDerivative := by
  have hzero : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have hone : ∀ᵐ u : ℝ ∂volume, u ≠ 1 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hzero, hone] with u hu_zero hu_one
  by_cases hleft : u ≤ 0
  · rw [aux_smoothStepSecondDerivative, Set.indicator_of_notMem]
    · rcases hleft.eq_or_lt with rfl | hlt
      · contradiction
      · exact aux_smoothStep_secondDeriv_lt_zero u hlt
    · simp [hleft]
  by_cases hright : u < 1
  · rw [aux_smoothStepSecondDerivative,
      Set.indicator_of_mem (show u ∈ Set.Ioo 0 1 from ⟨lt_of_not_ge hleft, hright⟩)]
    exact aux_smoothStep_secondDeriv_on_Ioo u (lt_of_not_ge hleft) hright
  · rw [aux_smoothStepSecondDerivative, Set.indicator_of_notMem]
    · have hgt : 1 < u :=
        lt_of_le_of_ne (le_of_not_gt hright) (Ne.symm hu_one)
      exact aux_smoothStep_secondDeriv_gt_one u hgt
    · simp [hright]

/-- The polynomial smooth step takes values in the unit interval.  This
pointwise auxiliary bound is used by `spatialCutoffBounds` and the explicit
dyadic cutoff arguments. -/
lemma aux_smoothStep_nonneg_le_one (u : ℝ) :
    0 ≤ smoothStep u ∧ smoothStep u ≤ 1 := by
  unfold smoothStep
  split_ifs with hu_zero hu_one
  · norm_num
  · have hu_pos : 0 < u := lt_of_not_ge hu_zero
    constructor
    · rw [show 3 * u ^ 2 - 2 * u ^ 3 = u ^ 2 * (3 - 2 * u) by ring]
      exact mul_nonneg (sq_nonneg u) (by linarith)
    · rw [← sub_nonneg]
      rw [show 1 - (3 * u ^ 2 - 2 * u ^ 3) = (1 - u) ^ 2 * (1 + 2 * u) by ring]
      exact mul_nonneg (sq_nonneg _) (by linarith)
  · norm_num

/-- The constant left branch of the polynomial smooth step.  This auxiliary
identity is used to locate the support of `spatialCutoff` in
`spatialCutoffBounds`. -/
lemma aux_smoothStep_eq_zero_of_nonpos {u : ℝ} (hu : u ≤ 0) : smoothStep u = 0 := by
  simp [smoothStep, hu]

/-- The constant right branch of the polynomial smooth step.  This auxiliary
identity is used by `spatialCutoffBounds` and the dyadic cutoff facts. -/
lemma aux_smoothStep_eq_one_of_one_le {u : ℝ} (hu : 1 ≤ u) : smoothStep u = 1 := by
  have hu_zero : ¬ u ≤ 0 := by linarith
  have hu_one : ¬ u < 1 := not_lt.mpr hu
  simp [smoothStep, hu_zero, hu_one]

/--
The derivative bounds in \(\label{lem:smooth-step-bounds}\):
\[
\lVert s'\rVert_1=1,\qquad
\lVert s''\rVert_1=3,\qquad
\lVert s'\rVert_2^2=\frac65<2.
\]
-/
theorem smoothStepBounds :
    eLpNorm (deriv smoothStep) (1 : ℝ≥0∞) volume = 1 ∧
      eLpNorm (deriv (deriv smoothStep)) (1 : ℝ≥0∞) volume = 3 ∧
      eLpNorm (deriv smoothStep) (2 : ℝ≥0∞) volume ^ 2 = (6 : ℝ≥0∞) / 5 ∧
      eLpNorm (deriv smoothStep) (2 : ℝ≥0∞) volume ^ 2 < 2 := by
  let g1 : ℝ → ℝ := (Set.Ioo 0 1).indicator (fun x : ℝ ↦ 6 * x - 6 * x ^ 2)
  let g2 : ℝ → ℝ := (Set.Ioo 0 1).indicator (fun x : ℝ ↦ 6 - 12 * x)
  let g1sq : ℝ → ℝ :=
    (Set.Ioo 0 1).indicator (fun x : ℝ ↦ (6 * x - 6 * x ^ 2) ^ 2)
  let g2abs : ℝ → ℝ :=
    (Set.Ioo 0 1).indicator (fun x : ℝ ↦ |6 - 12 * x|)
  have hg1 : aux_smoothStepDerivative = g1 := by rfl
  have hg2 : aux_smoothStepSecondDerivative = g2 := by rfl
  have hg1int : Integrable g1 volume := by
    apply (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).2
    apply (intervalIntegrable_iff.mp
      ((by
        fun_prop : Continuous (fun x : ℝ ↦ 6 * x - 6 * x ^ 2)).intervalIntegrable 0 1)).mono_set
    simpa using (Set.Ioo_subset_Ioc_self : Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioc 0 1)
  have hg1nonneg : ∀ x : ℝ, 0 ≤ g1 x := by
    intro x
    dsimp [g1]
    by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1
    · rw [Set.indicator_of_mem hx]
      have hmul : 0 ≤ x * (1 - x) :=
        mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le)
      nlinarith
    · simp [Set.indicator_of_notMem hx]
  have hg1norm : (fun x : ℝ ↦ ‖g1 x‖ₑ) = fun x ↦ ENNReal.ofReal (g1 x) := by
    funext x
    rw [← ofReal_norm, Real.norm_of_nonneg (hg1nonneg x)]
  have hg1real : ∫ x : ℝ, g1 x = 1 := by
    dsimp [g1]
    rw [MeasureTheory.integral_indicator measurableSet_Ioo]
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    rw [intervalIntegral.integral_sub]
    · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      norm_num [integral_pow]
    · exact (continuous_const.mul continuous_id).intervalIntegrable 0 1
    · exact (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 1
  have hg1sqint : Integrable g1sq volume := by
    apply (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).2
    apply (intervalIntegrable_iff.mp
      ((by fun_prop : Continuous (fun x : ℝ ↦ (6 * x - 6 * x ^ 2) ^ 2)).intervalIntegrable
        0 1)).mono_set
    simpa using (Set.Ioo_subset_Ioc_self : Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioc 0 1)
  have hg1sqnonneg : ∀ x : ℝ, 0 ≤ g1sq x := by
    intro x
    dsimp [g1sq]
    by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1
    · rw [Set.indicator_of_mem hx]
      exact sq_nonneg _
    · simp [Set.indicator_of_notMem hx]
  have hg1pow : (fun x : ℝ ↦ ‖g1 x‖ₑ ^ (2 : ℝ)) =
      fun x ↦ ENNReal.ofReal (g1sq x) := by
    funext x
    rw [← ofReal_norm, Real.norm_of_nonneg (hg1nonneg x)]
    rw [ENNReal.ofReal_rpow_of_nonneg (hg1nonneg x) (by norm_num)]
    rw [Real.rpow_two]
    dsimp [g1, g1sq]
    by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hg1sqreal : ∫ x : ℝ, g1sq x = (6 / 5 : ℝ) := by
    dsimp [g1sq]
    rw [MeasureTheory.integral_indicator measurableSet_Ioo]
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    have hpoly : (fun x : ℝ ↦ (6 * x - 6 * x ^ 2) ^ 2) =
        fun x ↦ 36 * x ^ 2 - 72 * x ^ 3 + 36 * x ^ 4 := by
      funext x
      ring
    rw [hpoly]
    rw [intervalIntegral.integral_add]
    · rw [intervalIntegral.integral_sub]
      · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
        norm_num [integral_pow]
      · exact (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 1
      · exact (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable 0 1
    · exact ((continuous_const.mul (continuous_id.pow 2)).sub
        (continuous_const.mul (continuous_id.pow 3))).intervalIntegrable 0 1
    · exact (continuous_const.mul (continuous_id.pow 4)).intervalIntegrable 0 1
  have hg2absint : Integrable g2abs volume := by
    apply (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).2
    apply (intervalIntegrable_iff.mp
      ((by fun_prop : Continuous (fun x : ℝ ↦ |6 - 12 * x|)).intervalIntegrable 0 1)).mono_set
    simpa using (Set.Ioo_subset_Ioc_self : Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioc 0 1)
  have hg2absnonneg : ∀ x : ℝ, 0 ≤ g2abs x := by
    intro x
    dsimp [g2abs]
    by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1
    · rw [Set.indicator_of_mem hx]
      exact abs_nonneg _
    · simp [Set.indicator_of_notMem hx]
  have hg2norm : (fun x : ℝ ↦ ‖g2 x‖ₑ) = fun x ↦ ENNReal.ofReal (g2abs x) := by
    funext x
    dsimp [g2, g2abs]
    by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, ← ofReal_norm, Real.norm_eq_abs]
    · simp [Set.indicator_of_notMem hx]
  have hg2absreal : ∫ x : ℝ, g2abs x = 3 := by
    dsimp [g2abs]
    rw [MeasureTheory.integral_indicator measurableSet_Ioo]
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    have hc : Continuous (fun x : ℝ ↦ |6 - 12 * x|) :=
      (continuous_const.sub (continuous_const.mul continuous_id)).abs
    have hleft : IntervalIntegrable (fun x : ℝ ↦ |6 - 12 * x|) volume 0 (1 / 2) :=
      hc.intervalIntegrable 0 (1 / 2)
    have hright : IntervalIntegrable (fun x : ℝ ↦ |6 - 12 * x|) volume (1 / 2) 1 :=
      hc.intervalIntegrable (1 / 2) 1
    have hleftcalc : (∫ x : ℝ in 0..(1 / 2), |6 - 12 * x|) =
        ∫ x : ℝ in 0..(1 / 2), (6 - 12 * x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      change |6 - 12 * x| = 6 - 12 * x
      have hnon : 0 ≤ 6 - 12 * x := by
        norm_num [Set.mem_uIcc] at hx
        linarith
      exact abs_of_nonneg hnon
    have hrightcalc : (∫ x : ℝ in (1 / 2)..1, |6 - 12 * x|) =
        ∫ x : ℝ in (1 / 2)..1, (12 * x - 6) := by
      apply intervalIntegral.integral_congr
      intro x hx
      change |6 - 12 * x| = 12 * x - 6
      have hnon : 6 - 12 * x ≤ 0 := by
        norm_num [Set.mem_uIcc] at hx
        linarith
      rw [abs_of_nonpos hnon]
      ring
    have hleftpoly : (∫ x : ℝ in 0..(1 / 2), (6 - 12 * x)) = (3 / 2 : ℝ) := by
      rw [intervalIntegral.integral_sub]
      · rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
        norm_num [integral_pow]
      · exact continuous_const.intervalIntegrable 0 (1 / 2)
      · exact (continuous_const.mul continuous_id).intervalIntegrable 0 (1 / 2)
    have hrightpoly : (∫ x : ℝ in (1 / 2)..1, (12 * x - 6)) = (3 / 2 : ℝ) := by
      rw [intervalIntegral.integral_sub]
      · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
        norm_num [integral_pow]
      · exact (continuous_const.mul continuous_id).intervalIntegrable (1 / 2) 1
      · exact continuous_const.intervalIntegrable (1 / 2) 1
    calc
      ∫ x : ℝ in 0..1, |6 - 12 * x| =
          (∫ x : ℝ in 0..(1 / 2), |6 - 12 * x|) +
            ∫ x : ℝ in (1 / 2)..1, |6 - 12 * x| :=
        (intervalIntegral.integral_add_adjacent_intervals hleft hright).symm
      _ = 3 := by rw [hleftcalc, hrightcalc, hleftpoly, hrightpoly]; norm_num
  have hfirst : eLpNorm (deriv smoothStep) (1 : ℝ≥0∞) volume = 1 := by
    calc
      eLpNorm (deriv smoothStep) (1 : ℝ≥0∞) volume =
          eLpNorm aux_smoothStepDerivative (1 : ℝ≥0∞) volume :=
        eLpNorm_congr_ae aux_smoothStep_deriv_ae
      _ = eLpNorm g1 (1 : ℝ≥0∞) volume := by rw [hg1]
      _ = ∫⁻ x : ℝ, ‖g1 x‖ₑ := eLpNorm_one_eq_lintegral_enorm
      _ = ∫⁻ x : ℝ, ENNReal.ofReal (g1 x) := by rw [hg1norm]
      _ = ENNReal.ofReal (∫ x : ℝ, g1 x) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg1int
          (ae_of_all _ hg1nonneg)).symm
      _ = 1 := by rw [hg1real]; norm_num
  have hsecond : eLpNorm (deriv (deriv smoothStep)) (1 : ℝ≥0∞) volume = 3 := by
    calc
      eLpNorm (deriv (deriv smoothStep)) (1 : ℝ≥0∞) volume =
          eLpNorm aux_smoothStepSecondDerivative (1 : ℝ≥0∞) volume :=
        eLpNorm_congr_ae aux_smoothStep_secondDeriv_ae
      _ = eLpNorm g2 (1 : ℝ≥0∞) volume := by rw [hg2]
      _ = ∫⁻ x : ℝ, ‖g2 x‖ₑ := eLpNorm_one_eq_lintegral_enorm
      _ = ∫⁻ x : ℝ, ENNReal.ofReal (g2abs x) := by rw [hg2norm]
      _ = ENNReal.ofReal (∫ x : ℝ, g2abs x) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg2absint
          (ae_of_all _ hg2absnonneg)).symm
      _ = 3 := by rw [hg2absreal]; norm_num
  have hthird : eLpNorm (deriv smoothStep) (2 : ℝ≥0∞) volume ^ 2 =
      (6 : ℝ≥0∞) / 5 := by
    calc
      eLpNorm (deriv smoothStep) (2 : ℝ≥0∞) volume ^ 2 =
          eLpNorm aux_smoothStepDerivative (2 : ℝ≥0∞) volume ^ 2 :=
        congrArg (fun z : ℝ≥0∞ ↦ z ^ (2 : ℕ))
          (eLpNorm_congr_ae aux_smoothStep_deriv_ae)
      _ = eLpNorm g1 (2 : ℝ≥0∞) volume ^ 2 := by rw [hg1]
      _ = ∫⁻ x : ℝ, ‖g1 x‖ₑ ^ (2 : ℝ) := by
        simpa using
          (eLpNorm_nnreal_pow_eq_lintegral (f := g1) (p := (2 : NNReal)) (by norm_num))
      _ = ∫⁻ x : ℝ, ENNReal.ofReal (g1sq x) := by rw [hg1pow]
      _ = ENNReal.ofReal (∫ x : ℝ, g1sq x) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg1sqint
          (ae_of_all _ hg1sqnonneg)).symm
      _ = (6 : ℝ≥0∞) / 5 := by
        rw [hg1sqreal, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 5)]
        norm_num
  refine ⟨hfirst, hsecond, hthird, ?_⟩
  rw [hthird]
  rw [ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  norm_num

/--
For the compact interval \(I=[a,b]\), the spatial cutoff from
\(\label{def:spatial-cutoff}\) is
\[
\rho_I(x)=s(x-a+1)s(b+1-x).
\]
-/
def spatialCutoff (a b : ℝ) (x : ℝ) : ℝ :=
  smoothStep (x - a + 1) * smoothStep (b + 1 - x)

/-- Pointwise range control for the spatial cutoff.  This is an auxiliary
fact for `spatialCutoffBounds` and `\label{lem:spatial-cutoff-bounds}`. -/
lemma aux_spatialCutoff_pointwise (a b x : ℝ) :
    0 ≤ spatialCutoff a b x ∧ spatialCutoff a b x ≤ 1 := by
  unfold spatialCutoff
  have hleft := aux_smoothStep_nonneg_le_one (x - a + 1)
  have hright := aux_smoothStep_nonneg_le_one (b + 1 - x)
  constructor
  · exact mul_nonneg hleft.1 hright.1
  · nlinarith [mul_nonneg (sub_nonneg.mpr hleft.2) hright.1]

/-- The spatial cutoff equals one on its defining compact interval.  This
is an auxiliary pointwise fact for `spatialCutoffBounds`. -/
lemma aux_spatialCutoff_one_on {a b x : ℝ} (hx : x ∈ Set.Icc a b) :
    spatialCutoff a b x = 1 := by
  unfold spatialCutoff
  rw [aux_smoothStep_eq_one_of_one_le (by linarith [hx.1]),
    aux_smoothStep_eq_one_of_one_le (by linarith [hx.2])]
  norm_num

/-- The topological support of the spatial cutoff is contained in the
one-neighborhood of its defining interval.  This is used in
`spatialCutoffBounds` for `\label{lem:spatial-cutoff-bounds}`. -/
lemma aux_spatialCutoff_tsupport {a b : ℝ} :
    tsupport (spatialCutoff a b) ⊆ Set.Icc (a - 1) (b + 1) := by
  change closure (Function.support (spatialCutoff a b)) ⊆ Set.Icc (a - 1) (b + 1)
  apply closure_minimal
  · intro x hx
    rw [Function.mem_support] at hx
    by_contra hxbounds
    have hxout : x < a - 1 ∨ b + 1 < x := by
      by_contra h
      push Not at h
      exact hxbounds ⟨h.1, h.2⟩
    rcases hxout with hleft | hright
    · apply hx
      rw [spatialCutoff, aux_smoothStep_eq_zero_of_nonpos (by linarith : x - a + 1 ≤ 0)]
      simp
    · apply hx
      rw [spatialCutoff, aux_smoothStep_eq_zero_of_nonpos (by linarith : b + 1 - x ≤ 0)]
      simp
  · exact isClosed_Icc

/-- Pointwise domination of the spatial cutoff by the indicator of its
support interval.  This supports the two direct norm bounds in
`spatialCutoffBounds`. -/
lemma aux_spatialCutoff_domination (a b x : ℝ) :
    ‖spatialCutoff a b x‖ ≤
      ‖(Set.Icc (a - 1) (b + 1)).indicator (fun _ : ℝ ↦ (1 : ℝ)) x‖ := by
  by_cases hx : x ∈ Set.Icc (a - 1) (b + 1)
  · rw [Set.indicator_of_mem hx, norm_one]
    rw [Real.norm_of_nonneg (aux_spatialCutoff_pointwise a b x).1]
    exact (aux_spatialCutoff_pointwise a b x).2
  · rw [Set.indicator_of_notMem hx, norm_zero]
    have hzero : spatialCutoff a b x = 0 := by
      by_contra hne
      exact hx (aux_spatialCutoff_tsupport (show x ∈ tsupport (spatialCutoff a b) by
        exact subset_tsupport _ hne))
    rw [hzero, norm_zero]

/-- The elementary `L¹` consequence of the pointwise support domination,
used in `spatialCutoffBounds` for `\label{lem:spatial-cutoff-bounds}`. -/
lemma aux_spatialCutoff_l1 {a b : ℝ} :
    eLpNorm (spatialCutoff a b) (1 : ℝ≥0∞) volume ≤ ENNReal.ofReal (b - a + 2) := by
  calc
    eLpNorm (spatialCutoff a b) (1 : ℝ≥0∞) volume ≤
        eLpNorm ((Set.Icc (a - 1) (b + 1)).indicator (fun _ : ℝ ↦ (1 : ℝ)))
          (1 : ℝ≥0∞) volume := eLpNorm_mono (aux_spatialCutoff_domination a b)
    _ = ENNReal.ofReal (b - a + 2) := by
      rw [eLpNorm_indicator_const measurableSet_Icc (by norm_num) (by norm_num)]
      have hvol : volume (Set.Icc (a - 1) (b + 1)) = ENNReal.ofReal (b - a + 2) := by
        rw [Real.volume_Icc]
        congr 1
        ring
      rw [hvol]
      norm_num

/-- The elementary `L²` consequence of the pointwise support domination,
used in `spatialCutoffBounds` for `\label{lem:spatial-cutoff-bounds}`. -/
lemma aux_spatialCutoff_l2 {a b : ℝ} (hab : a ≤ b) :
    eLpNorm (spatialCutoff a b) (2 : ℝ≥0∞) volume ≤
      ENNReal.ofReal (Real.sqrt (b - a + 2)) := by
  calc
    eLpNorm (spatialCutoff a b) (2 : ℝ≥0∞) volume ≤
        eLpNorm ((Set.Icc (a - 1) (b + 1)).indicator (fun _ : ℝ ↦ (1 : ℝ)))
          (2 : ℝ≥0∞) volume := eLpNorm_mono (aux_spatialCutoff_domination a b)
    _ = ENNReal.ofReal (Real.sqrt (b - a + 2)) := by
      rw [eLpNorm_indicator_const measurableSet_Icc (by norm_num) (by norm_num)]
      have hvol : volume (Set.Icc (a - 1) (b + 1)) = ENNReal.ofReal (b - a + 2) := by
        rw [Real.volume_Icc]
        congr 1
        ring
      rw [hvol]
      have hlen : 0 ≤ b - a + 2 := by linarith
      norm_num
      rw [ENNReal.ofReal_rpow_of_nonneg hlen]
      · rw [← Real.sqrt_eq_rpow]
      · norm_num

/-- Away from the two transition points, the polynomial smooth step is
differentiable.  This local fact is used for the product-rule proof of the
derivative estimates in `spatialCutoffBounds`. -/
lemma aux_smoothStep_differentiableAt_of_ne (u : ℝ) (hu_zero : u ≠ 0) (hu_one : u ≠ 1) :
    DifferentiableAt ℝ smoothStep u := by
  by_cases hleft : u < 0
  · exact ((hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq (by
      filter_upwards [gt_mem_nhds hleft] with v hv
      simp [smoothStep, hv.le])).differentiableAt
  by_cases hmid : u < 1
  · have hpos : 0 < u := lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hu_zero)
    have h2 : HasDerivAt (fun v : ℝ ↦ v ^ 2) (2 * u) u := by
      simpa using
        (hasDerivAt_pow 2 u : HasDerivAt (fun v : ℝ ↦ v ^ 2) (2 * u ^ (2 - 1)) u)
    have h3 : HasDerivAt (fun v : ℝ ↦ v ^ 3) (3 * u ^ 2) u := by
      simpa using
        (hasDerivAt_pow 3 u : HasDerivAt (fun v : ℝ ↦ v ^ 3) (3 * u ^ (3 - 1)) u)
    have hpolynomial := h2.const_mul 3 |>.sub (h3.const_mul 2)
    have hfun : smoothStep =ᶠ[𝓝 u] (fun v : ℝ ↦ 3 * v ^ 2 - 2 * v ^ 3) := by
      filter_upwards [lt_mem_nhds hpos, gt_mem_nhds hmid] with v hv_zero hv_one
      simp [smoothStep, not_le.mpr hv_zero, hv_one]
    exact hpolynomial.differentiableAt.congr_of_eventuallyEq hfun
  · have hright : 1 < u := lt_of_le_of_ne (le_of_not_gt hmid) (Ne.symm hu_one)
    exact ((hasDerivAt_const u (1 : ℝ)).congr_of_eventuallyEq (by
      filter_upwards [lt_mem_nhds hright] with v hv
      have hv_zero : ¬ v ≤ 0 := by linarith
      have hv_one : ¬ v < 1 := by linarith
      simp [smoothStep, hv_zero, hv_one])).differentiableAt

/-- Away from the two transition points, the derivative of the polynomial
smooth step is differentiable.  This is used by the second-derivative
product-rule calculation for `spatialCutoffBounds`. -/
lemma aux_derivSmoothStep_differentiableAt_of_ne (u : ℝ) (hu_zero : u ≠ 0) (hu_one : u ≠ 1) :
    DifferentiableAt ℝ (deriv smoothStep) u := by
  by_cases hleft : u < 0
  · exact ((hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq (by
      filter_upwards [gt_mem_nhds hleft] with v hv
      exact aux_smoothStep_deriv_lt_zero v hv)).differentiableAt
  by_cases hmid : u < 1
  · have hpos : 0 < u := lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hu_zero)
    have h1 : HasDerivAt (fun v : ℝ ↦ v) 1 u := hasDerivAt_id u
    have h2 : HasDerivAt (fun v : ℝ ↦ v ^ 2) (2 * u) u := by
      simpa using
        (hasDerivAt_pow 2 u : HasDerivAt (fun v : ℝ ↦ v ^ 2) (2 * u ^ (2 - 1)) u)
    have hpolynomial := h1.const_mul 6 |>.sub (h2.const_mul 6)
    have hfun : deriv smoothStep =ᶠ[𝓝 u] (fun v : ℝ ↦ 6 * v - 6 * v ^ 2) := by
      filter_upwards [lt_mem_nhds hpos, gt_mem_nhds hmid] with v hv_zero hv_one
      exact aux_smoothStep_deriv_on_Ioo v hv_zero hv_one
    exact hpolynomial.differentiableAt.congr_of_eventuallyEq hfun
  · have hright : 1 < u := lt_of_le_of_ne (le_of_not_gt hmid) (Ne.symm hu_one)
    exact ((hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq (by
      filter_upwards [lt_mem_nhds hright] with v hv
      exact aux_smoothStep_deriv_gt_one v hv)).differentiableAt

/-- Translation invariance of `eLpNorm`, in the raw-function form needed by
the spatial cutoff derivative estimates. -/
lemma aux_eLpNorm_translate (f : ℝ → ℝ) (hf : AEStronglyMeasurable f volume)
    (c : ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun x : ℝ ↦ f (x + c)) p volume = eLpNorm f p volume := by
  simpa only [Function.comp_def] using
    (eLpNorm_comp_measurePreserving (p := p) hf (measurePreserving_add_right volume c))

/-- Reflection followed by translation preserves `eLpNorm`.  This auxiliary
change-of-variables fact is used by `spatialCutoffBounds`. -/
lemma aux_eLpNorm_reflect_translate (f : ℝ → ℝ) (hf : AEStronglyMeasurable f volume)
    (c : ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun x : ℝ ↦ f (c - x)) p volume = eLpNorm f p volume := by
  have hmp : MeasurePreserving (fun x : ℝ ↦ c - x) volume volume := by
    convert (measurePreserving_add_left volume c).comp
      (Measure.measurePreserving_neg volume) using 1;
      simp [Function.comp_def, sub_eq_add_neg]
  simpa only [Function.comp_def] using (eLpNorm_comp_measurePreserving (p := p) hf hmp)

/-- Multiplication by a pointwise unit-bounded factor does not increase an
`eLpNorm`.  This auxiliary estimate is used in `spatialCutoffBounds`. -/
lemma aux_eLpNorm_mul_le_left (f g : ℝ → ℝ) (hg : ∀ x, ‖g x‖ ≤ 1)
    (p : ℝ≥0∞) : eLpNorm (f * g) p volume ≤ eLpNorm f p volume := by
  apply eLpNorm_mono
  intro x
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hg x)

/-- The symmetric form of `aux_eLpNorm_mul_le_left`, used by the spatial
cutoff derivative estimates. -/
lemma aux_eLpNorm_mul_le_right (f g : ℝ → ℝ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (p : ℝ≥0∞) : eLpNorm (f * g) p volume ≤ eLpNorm g p volume := by
  apply eLpNorm_mono
  intro x
  rw [Pi.mul_apply, norm_mul, mul_comm]
  exact mul_le_of_le_one_right (norm_nonneg _) (hf x)

/-- The polynomial smooth step is measurable.  This supplies the
measurability hypotheses in the norm estimates of `spatialCutoffBounds`. -/
lemma aux_smoothStep_aestronglyMeasurable : AEStronglyMeasurable smoothStep volume := by
  apply Measurable.aestronglyMeasurable
  unfold smoothStep
  apply Measurable.ite measurableSet_Iic measurable_const
  apply Measurable.ite measurableSet_Iio
  · exact (measurable_id.pow_const 2).const_mul 3 |>.sub
      ((measurable_id.pow_const 3).const_mul 2)
  · exact measurable_const

/-- The first product-rule formula for the spatial cutoff, valid away from
the finitely many transition points.  It is an auxiliary calculation for
`spatialCutoffBounds`. -/
lemma aux_deriv_spatial_at (a b x : ℝ)
    (hA : DifferentiableAt ℝ smoothStep (x - a + 1))
    (hB : DifferentiableAt ℝ smoothStep (b + 1 - x)) :
    deriv (spatialCutoff a b) x =
      deriv smoothStep (x - a + 1) * smoothStep (b + 1 - x) -
        smoothStep (x - a + 1) * deriv smoothStep (b + 1 - x) := by
  have hleftaff : HasDerivAt (fun y : ℝ ↦ y - a + 1) 1 x := by
    convert ((hasDerivAt_id' x).sub_const a).add_const 1 using 1
  have hrightaff : HasDerivAt (fun y : ℝ ↦ b + 1 - y) (-1) x := by
    convert (hasDerivAt_id' x).const_sub (b + 1) using 1
  have hleft : HasDerivAt (fun y : ℝ ↦ smoothStep (y - a + 1))
      (deriv smoothStep (x - a + 1)) x := by
    simpa [Function.comp_def] using (hA.hasDerivAt.comp x hleftaff)
  have hright : HasDerivAt (fun y : ℝ ↦ smoothStep (b + 1 - y))
      (-deriv smoothStep (b + 1 - x)) x := by
    simpa [Function.comp_def] using (hB.hasDerivAt.comp x hrightaff)
  change deriv ((fun y : ℝ ↦ smoothStep (y - a + 1)) *
    (fun y : ℝ ↦ smoothStep (b + 1 - y))) x = _
  simpa [sub_eq_add_neg] using (hleft.mul hright).deriv

/-- Almost every point stays away from all four shifted transition points of
the two factors in `spatialCutoff`.  This is used for a.e. product rules in
`spatialCutoffBounds`. -/
lemma aux_ae_shifted_away (a b : ℝ) : ∀ᵐ x : ℝ ∂volume,
    x - a + 1 ≠ 0 ∧ x - a + 1 ≠ 1 ∧ b + 1 - x ≠ 0 ∧ b + 1 - x ≠ 1 := by
  have ae_ne (c : ℝ) : ∀ᵐ x : ℝ ∂volume, x ≠ c := by
    rw [ae_iff]
    have hset : {x : ℝ | ¬ x ≠ c} = {c} := by ext x; simp
    rw [hset]
    exact measure_singleton _
  filter_upwards [ae_ne (a - 1), ae_ne a, ae_ne (b + 1), ae_ne b] with x h1 h2 h3 h4
  constructor
  · intro h
    apply h1
    linarith
  constructor
  · intro h
    apply h2
    linarith
  constructor
  · intro h
    apply h3
    linarith
  · intro h
    apply h4
    linarith

/-- Almost-everywhere first product-rule formula for the spatial cutoff.
This auxiliary identity is used to establish the first derivative bound in
`spatialCutoffBounds`. -/
lemma aux_deriv_spatial_ae (a b : ℝ) :
    deriv (spatialCutoff a b) =ᵐ[volume]
      fun x ↦ deriv smoothStep (x - a + 1) * smoothStep (b + 1 - x) -
        smoothStep (x - a + 1) * deriv smoothStep (b + 1 - x) := by
  filter_upwards [aux_ae_shifted_away a b] with x hx
  exact aux_deriv_spatial_at a b x
    (aux_smoothStep_differentiableAt_of_ne _ hx.1 hx.2.1)
    (aux_smoothStep_differentiableAt_of_ne _ hx.2.2.1 hx.2.2.2)

/-- The first derivative `L¹` estimate for the spatial cutoff, reduced to
the explicit smooth-step derivative norm in `smoothStepBounds`. -/
lemma aux_spatial_deriv_L1
    (hnorm : eLpNorm (deriv smoothStep) (1 : ℝ≥0∞) volume = 1)
    (a b : ℝ) :
    eLpNorm (deriv (spatialCutoff a b)) (1 : ℝ≥0∞) volume ≤ 2 := by
  have hDmeas : AEStronglyMeasurable (deriv smoothStep) volume :=
    aestronglyMeasurable_deriv smoothStep volume
  have hSmeas : AEStronglyMeasurable smoothStep volume := aux_smoothStep_aestronglyMeasurable
  have hAmeas : AEStronglyMeasurable (fun x : ℝ ↦ smoothStep (x - a + 1)) volume := by
    have hshift : (fun x : ℝ ↦ smoothStep (x - a + 1)) =
        (fun x : ℝ ↦ smoothStep (x + (1 - a))) := by ext x; congr 1; ring
    rw [hshift]
    exact hSmeas.comp_measurePreserving (measurePreserving_add_right volume (1 - a))
  have hBmeas : AEStronglyMeasurable (fun x : ℝ ↦ smoothStep (b + 1 - x)) volume := by
    have hmp : MeasurePreserving (fun x : ℝ ↦ b + 1 - x) volume volume := by
      convert (measurePreserving_add_left volume (b + 1)).comp
        (Measure.measurePreserving_neg volume) using 1; simp [Function.comp_def, sub_eq_add_neg]
    simpa [Function.comp_def] using hSmeas.comp_measurePreserving hmp
  have hDAmeas : AEStronglyMeasurable (fun x : ℝ ↦ deriv smoothStep (x - a + 1)) volume := by
    have hshift : (fun x : ℝ ↦ deriv smoothStep (x - a + 1)) =
        (fun x : ℝ ↦ deriv smoothStep (x + (1 - a))) := by ext x; congr 1; ring
    rw [hshift]
    exact hDmeas.comp_measurePreserving (measurePreserving_add_right volume (1 - a))
  have hDBmeas : AEStronglyMeasurable (fun x : ℝ ↦ deriv smoothStep (b + 1 - x)) volume := by
    have hmp : MeasurePreserving (fun x : ℝ ↦ b + 1 - x) volume volume := by
      convert (measurePreserving_add_left volume (b + 1)).comp
        (Measure.measurePreserving_neg volume) using 1; simp [Function.comp_def, sub_eq_add_neg]
    simpa [Function.comp_def] using hDmeas.comp_measurePreserving hmp
  rw [eLpNorm_congr_ae (aux_deriv_spatial_ae a b)]
  calc
    eLpNorm (fun x : ℝ ↦ deriv smoothStep (x - a + 1) * smoothStep (b + 1 - x) -
        smoothStep (x - a + 1) * deriv smoothStep (b + 1 - x)) 1 volume
      ≤ eLpNorm ((fun x : ℝ ↦ deriv smoothStep (x - a + 1)) *
          (fun x ↦ smoothStep (b + 1 - x))) 1 volume +
        eLpNorm ((fun x : ℝ ↦ smoothStep (x - a + 1)) *
          (fun x ↦ deriv smoothStep (b + 1 - x))) 1 volume :=
      eLpNorm_sub_le (hDAmeas.mul hBmeas) (hAmeas.mul hDBmeas) (by norm_num)
    _ ≤ eLpNorm (fun x : ℝ ↦ deriv smoothStep (x - a + 1)) 1 volume +
        eLpNorm (fun x : ℝ ↦ deriv smoothStep (b + 1 - x)) 1 volume := by
      gcongr
      · apply aux_eLpNorm_mul_le_left
        intro x
        rw [Real.norm_of_nonneg (aux_smoothStep_nonneg_le_one _).1]
        exact (aux_smoothStep_nonneg_le_one _).2
      · apply aux_eLpNorm_mul_le_right
        intro x
        rw [Real.norm_of_nonneg (aux_smoothStep_nonneg_le_one _).1]
        exact (aux_smoothStep_nonneg_le_one _).2
    _ = 2 := by
      have hshift : (fun x : ℝ ↦ deriv smoothStep (x - a + 1)) =
          (fun x : ℝ ↦ deriv smoothStep (x + (1 - a))) := by ext x; congr 1; ring
      rw [hshift, aux_eLpNorm_translate _ hDmeas (1 - a) 1,
        aux_eLpNorm_reflect_translate _ hDmeas (b + 1) 1, hnorm]
      norm_num

/-- The second product-rule formula for the spatial cutoff, away from its
four shifted transition points.  This auxiliary calculation is used by
`spatialCutoffBounds`. -/
lemma aux_deriv2_spatial_at (a b x : ℝ)
    (hA_zero : x - a + 1 ≠ 0) (hA_one : x - a + 1 ≠ 1)
    (hB_zero : b + 1 - x ≠ 0) (hB_one : b + 1 - x ≠ 1) :
    deriv (deriv (spatialCutoff a b)) x =
      deriv (deriv smoothStep) (x - a + 1) * smoothStep (b + 1 - x) -
        2 * deriv smoothStep (x - a + 1) * deriv smoothStep (b + 1 - x) +
        smoothStep (x - a + 1) * deriv (deriv smoothStep) (b + 1 - x) := by
  have hA : DifferentiableAt ℝ smoothStep (x - a + 1) :=
    aux_smoothStep_differentiableAt_of_ne _ hA_zero hA_one
  have hB : DifferentiableAt ℝ smoothStep (b + 1 - x) :=
    aux_smoothStep_differentiableAt_of_ne _ hB_zero hB_one
  have hDA : DifferentiableAt ℝ (deriv smoothStep) (x - a + 1) :=
    aux_derivSmoothStep_differentiableAt_of_ne _ hA_zero hA_one
  have hDB : DifferentiableAt ℝ (deriv smoothStep) (b + 1 - x) :=
    aux_derivSmoothStep_differentiableAt_of_ne _ hB_zero hB_one
  have hxA_zero : x ≠ a - 1 := by
    intro h
    apply hA_zero
    linarith
  have hxA_one : x ≠ a := by
    intro h
    apply hA_one
    linarith
  have hxB_zero : x ≠ b + 1 := by
    intro h
    apply hB_zero
    linarith
  have hxB_one : x ≠ b := by
    intro h
    apply hB_one
    linarith
  have hfirst : deriv (spatialCutoff a b) =ᶠ[𝓝 x]
      fun y ↦ deriv smoothStep (y - a + 1) * smoothStep (b + 1 - y) -
        smoothStep (y - a + 1) * deriv smoothStep (b + 1 - y) := by
    filter_upwards [show ∀ᶠ y : ℝ in 𝓝 x, y ≠ a - 1 from isOpen_ne.mem_nhds hxA_zero,
      show ∀ᶠ y : ℝ in 𝓝 x, y ≠ a from isOpen_ne.mem_nhds hxA_one,
      show ∀ᶠ y : ℝ in 𝓝 x, y ≠ b + 1 from isOpen_ne.mem_nhds hxB_zero,
      show ∀ᶠ y : ℝ in 𝓝 x, y ≠ b from isOpen_ne.mem_nhds hxB_one] with
        y hyA_zero hyA_one hyB_zero hyB_one
    apply aux_deriv_spatial_at a b y
    · apply aux_smoothStep_differentiableAt_of_ne
      · intro h
        apply hyA_zero
        linarith
      · intro h
        apply hyA_one
        linarith
    · apply aux_smoothStep_differentiableAt_of_ne
      · intro h
        apply hyB_zero
        linarith
      · intro h
        apply hyB_one
        linarith
  have hleftaff : HasDerivAt (fun y : ℝ ↦ y - a + 1) 1 x := by
    convert ((hasDerivAt_id' x).sub_const a).add_const 1 using 1
  have hrightaff : HasDerivAt (fun y : ℝ ↦ b + 1 - y) (-1) x := by
    convert (hasDerivAt_id' x).const_sub (b + 1) using 1
  have hS_A : HasDerivAt (fun y : ℝ ↦ smoothStep (y - a + 1))
      (deriv smoothStep (x - a + 1)) x := by
    simpa [Function.comp_def] using (hA.hasDerivAt.comp x hleftaff)
  have hS_B : HasDerivAt (fun y : ℝ ↦ smoothStep (b + 1 - y))
      (-deriv smoothStep (b + 1 - x)) x := by
    simpa [Function.comp_def] using (hB.hasDerivAt.comp x hrightaff)
  have hD_A : HasDerivAt (fun y : ℝ ↦ deriv smoothStep (y - a + 1))
      (deriv (deriv smoothStep) (x - a + 1)) x := by
    simpa [Function.comp_def] using (hDA.hasDerivAt.comp x hleftaff)
  have hD_B : HasDerivAt (fun y : ℝ ↦ deriv smoothStep (b + 1 - y))
      (-deriv (deriv smoothStep) (b + 1 - x)) x := by
    simpa [Function.comp_def] using (hDB.hasDerivAt.comp x hrightaff)
  have hderiv := ((hD_A.mul hS_B).sub (hS_A.mul hD_B)).congr_of_eventuallyEq hfirst
  convert hderiv.deriv using 1; ring

/-- Almost-everywhere second product-rule formula for the spatial cutoff.
This is an auxiliary identity for the final derivative estimate in
`spatialCutoffBounds`. -/
lemma aux_deriv2_spatial_ae (a b : ℝ) :
    deriv (deriv (spatialCutoff a b)) =ᵐ[volume]
      fun x ↦ deriv (deriv smoothStep) (x - a + 1) * smoothStep (b + 1 - x) -
        2 * deriv smoothStep (x - a + 1) * deriv smoothStep (b + 1 - x) +
        smoothStep (x - a + 1) * deriv (deriv smoothStep) (b + 1 - x) := by
  filter_upwards [aux_ae_shifted_away a b] with x hx
  exact aux_deriv2_spatial_at a b x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2

/-- The `L¹` bound for the second spatial cutoff derivative.  It combines the
two `L¹` smooth-step second derivative terms with the mixed `L²` term, and is
used by `spatialCutoffBounds` for `\label{lem:spatial-cutoff-bounds}`. -/
lemma aux_spatial_deriv2_L1
    (hnorm_second : eLpNorm (deriv (deriv smoothStep)) (1 : ℝ≥0∞) volume = 3)
    (hnorm_first_sq : eLpNorm (deriv smoothStep) (2 : ℝ≥0∞) volume ^ 2 =
      (6 : ℝ≥0∞) / 5)
    (a b : ℝ)
    (hformula : deriv (deriv (spatialCutoff a b)) =ᵐ[volume]
      fun x ↦ deriv (deriv smoothStep) (x - a + 1) * smoothStep (b + 1 - x) -
        2 * deriv smoothStep (x - a + 1) * deriv smoothStep (b + 1 - x) +
        smoothStep (x - a + 1) * deriv (deriv smoothStep) (b + 1 - x)) :
    eLpNorm (deriv (deriv (spatialCutoff a b))) (1 : ℝ≥0∞) volume ≤ 2 ^ 4 := by
  have hDmeas : AEStronglyMeasurable (deriv smoothStep) volume :=
    aestronglyMeasurable_deriv smoothStep volume
  have hEmeas : AEStronglyMeasurable (deriv (deriv smoothStep)) volume :=
    aestronglyMeasurable_deriv (deriv smoothStep) volume
  have hSmeas : AEStronglyMeasurable smoothStep volume := aux_smoothStep_aestronglyMeasurable
  have hAmeas : AEStronglyMeasurable (fun x : ℝ ↦ smoothStep (x - a + 1)) volume := by
    have hshift : (fun x : ℝ ↦ smoothStep (x - a + 1)) =
        (fun x : ℝ ↦ smoothStep (x + (1 - a))) := by ext x; congr 1; ring
    rw [hshift]
    exact hSmeas.comp_measurePreserving (measurePreserving_add_right volume (1 - a))
  have hBmeas : AEStronglyMeasurable (fun x : ℝ ↦ smoothStep (b + 1 - x)) volume := by
    have hmp : MeasurePreserving (fun x : ℝ ↦ b + 1 - x) volume volume := by
      convert (measurePreserving_add_left volume (b + 1)).comp
        (Measure.measurePreserving_neg volume) using 1; simp [Function.comp_def, sub_eq_add_neg]
    simpa [Function.comp_def] using hSmeas.comp_measurePreserving hmp
  have hDAmeas : AEStronglyMeasurable (fun x : ℝ ↦ deriv smoothStep (x - a + 1)) volume := by
    have hshift : (fun x : ℝ ↦ deriv smoothStep (x - a + 1)) =
        (fun x : ℝ ↦ deriv smoothStep (x + (1 - a))) := by ext x; congr 1; ring
    rw [hshift]
    exact hDmeas.comp_measurePreserving (measurePreserving_add_right volume (1 - a))
  have hDBmeas : AEStronglyMeasurable (fun x : ℝ ↦ deriv smoothStep (b + 1 - x)) volume := by
    have hmp : MeasurePreserving (fun x : ℝ ↦ b + 1 - x) volume volume := by
      convert (measurePreserving_add_left volume (b + 1)).comp
        (Measure.measurePreserving_neg volume) using 1; simp [Function.comp_def, sub_eq_add_neg]
    simpa [Function.comp_def] using hDmeas.comp_measurePreserving hmp
  have hEAmeas :
      AEStronglyMeasurable (fun x : ℝ ↦ deriv (deriv smoothStep) (x - a + 1)) volume := by
    have hshift : (fun x : ℝ ↦ deriv (deriv smoothStep) (x - a + 1)) =
        (fun x : ℝ ↦ deriv (deriv smoothStep) (x + (1 - a))) := by ext x; congr 1; ring
    rw [hshift]
    exact hEmeas.comp_measurePreserving (measurePreserving_add_right volume (1 - a))
  have hEBmeas :
      AEStronglyMeasurable (fun x : ℝ ↦ deriv (deriv smoothStep) (b + 1 - x)) volume := by
    have hmp : MeasurePreserving (fun x : ℝ ↦ b + 1 - x) volume volume := by
      convert (measurePreserving_add_left volume (b + 1)).comp
        (Measure.measurePreserving_neg volume) using 1; simp [Function.comp_def, sub_eq_add_neg]
    simpa [Function.comp_def] using hEmeas.comp_measurePreserving hmp
  rw [eLpNorm_congr_ae hformula]
  have hF : eLpNorm ((fun x : ℝ ↦ deriv (deriv smoothStep) (x - a + 1)) *
        (fun x ↦ smoothStep (b + 1 - x))) 1 volume ≤ 3 := by
    calc
      _ ≤ eLpNorm (fun x : ℝ ↦ deriv (deriv smoothStep) (x - a + 1)) 1 volume := by
        apply aux_eLpNorm_mul_le_left
        intro x
        rw [Real.norm_of_nonneg (aux_smoothStep_nonneg_le_one _).1]
        exact (aux_smoothStep_nonneg_le_one _).2
      _ = 3 := by
        have hshift : (fun x : ℝ ↦ deriv (deriv smoothStep) (x - a + 1)) =
            (fun x : ℝ ↦ deriv (deriv smoothStep) (x + (1 - a))) := by ext x; congr 1; ring
        rw [hshift, aux_eLpNorm_translate _ hEmeas (1 - a) 1, hnorm_second]
  have hH : eLpNorm ((fun x : ℝ ↦ smoothStep (x - a + 1)) *
        (fun x ↦ deriv (deriv smoothStep) (b + 1 - x))) 1 volume ≤ 3 := by
    calc
      _ ≤ eLpNorm (fun x : ℝ ↦ deriv (deriv smoothStep) (b + 1 - x)) 1 volume := by
        apply aux_eLpNorm_mul_le_right
        intro x
        rw [Real.norm_of_nonneg (aux_smoothStep_nonneg_le_one _).1]
        exact (aux_smoothStep_nonneg_le_one _).2
      _ = 3 := by
        rw [aux_eLpNorm_reflect_translate _ hEmeas (b + 1) 1, hnorm_second]
  have hG : eLpNorm ((fun x : ℝ ↦ deriv smoothStep (x - a + 1)) *
        (fun x ↦ deriv smoothStep (b + 1 - x))) 1 volume ≤ (6 : ℝ≥0∞) / 5 := by
    calc
      _ ≤ (1 : ℝ≥0∞) * eLpNorm (fun x : ℝ ↦ deriv smoothStep (x - a + 1)) 2 volume *
          eLpNorm (fun x : ℝ ↦ deriv smoothStep (b + 1 - x)) 2 volume := by
        apply eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hDAmeas hDBmeas (· * ·) 1
        filter_upwards with x
        simp
      _ = eLpNorm (deriv smoothStep) 2 volume ^ 2 := by
        have hshift : (fun x : ℝ ↦ deriv smoothStep (x - a + 1)) =
            (fun x : ℝ ↦ deriv smoothStep (x + (1 - a))) := by ext x; congr 1; ring
        rw [hshift, aux_eLpNorm_translate _ hDmeas (1 - a) 2,
          aux_eLpNorm_reflect_translate _ hDmeas (b + 1) 2]
        simp [pow_two]
      _ = _ := hnorm_first_sq
  calc
    eLpNorm (fun x : ℝ ↦ deriv (deriv smoothStep) (x - a + 1) * smoothStep (b + 1 - x) -
        2 * deriv smoothStep (x - a + 1) * deriv smoothStep (b + 1 - x) +
        smoothStep (x - a + 1) * deriv (deriv smoothStep) (b + 1 - x)) 1 volume
      = eLpNorm (((fun x : ℝ ↦ deriv (deriv smoothStep) (x - a + 1)) *
          (fun x ↦ smoothStep (b + 1 - x))) -
          (2 : ℝ) • ((fun x : ℝ ↦ deriv smoothStep (x - a + 1)) *
            (fun x ↦ deriv smoothStep (b + 1 - x))) +
          ((fun x : ℝ ↦ smoothStep (x - a + 1)) *
            (fun x ↦ deriv (deriv smoothStep) (b + 1 - x)))) 1 volume := by
        congr 3
        ext x
        simp [smul_eq_mul]
        ring
    _ ≤ eLpNorm (((fun x : ℝ ↦ deriv (deriv smoothStep) (x - a + 1)) *
          (fun x ↦ smoothStep (b + 1 - x))) -
          (2 : ℝ) • ((fun x : ℝ ↦ deriv smoothStep (x - a + 1)) *
            (fun x ↦ deriv smoothStep (b + 1 - x)))) 1 volume +
        eLpNorm ((fun x : ℝ ↦ smoothStep (x - a + 1)) *
            (fun x ↦ deriv (deriv smoothStep) (b + 1 - x))) 1 volume := by
        apply eLpNorm_add_le
        · exact (hEAmeas.mul hBmeas).sub ((hDAmeas.mul hDBmeas).const_smul _)
        · exact hAmeas.mul hEBmeas
        · norm_num
    _ ≤ (eLpNorm ((fun x : ℝ ↦ deriv (deriv smoothStep) (x - a + 1)) *
          (fun x ↦ smoothStep (b + 1 - x))) 1 volume +
          eLpNorm ((2 : ℝ) • ((fun x : ℝ ↦ deriv smoothStep (x - a + 1)) *
            (fun x ↦ deriv smoothStep (b + 1 - x)))) 1 volume) + 3 := by
        exact add_le_add
          (eLpNorm_sub_le (hEAmeas.mul hBmeas)
            ((hDAmeas.mul hDBmeas).const_smul _) (by norm_num)) hH
    _ ≤ (3 + 2 * ((6 : ℝ≥0∞) / 5)) + 3 := by
        apply add_le_add ?_ (le_refl _)
        apply add_le_add hF ?_
        rw [eLpNorm_const_smul]
        rw [show ‖(2 : ℝ)‖ₑ = (2 : ℝ≥0∞) by
          rw [← ofReal_norm, Real.norm_of_nonneg (by norm_num)]
          norm_num]
        exact mul_le_mul_of_nonneg_left hG (by norm_num)
    _ ≤ 2 ^ 4 := by
      have hfrac : (6 : ℝ≥0∞) / 5 ≤ 2 := by
        rw [ENNReal.div_le_iff_le_mul (by norm_num) (by norm_num)]
        norm_num
      calc
        (3 + 2 * ((6 : ℝ≥0∞) / 5)) + 3 ≤ (3 + 2 * 2) + 3 := by gcongr
        _ ≤ 2 ^ 4 := by norm_num

/--
The bounds for the spatial cutoff in \(\label{lem:spatial-cutoff-bounds}\):
\[
0\leq\rho_I\leq1,\quad \rho_I=1\text{ on }I,\quad
\operatorname{supp}\rho_I\subset I+[-1,1],
\]
\[
\lVert\rho_I\rVert_1\leq |I|+2,\quad
\lVert\rho_I\rVert_2\leq(|I|+2)^{1/2},\quad
\lVert\rho_I'\rVert_1\leq2,\quad
\lVert\rho_I''\rVert_1\leq2^4.
\]
-/
theorem spatialCutoffBounds {a b : ℝ} (hab : a ≤ b) :
    (∀ x, 0 ≤ spatialCutoff a b x ∧ spatialCutoff a b x ≤ 1) ∧
      (∀ x ∈ Set.Icc a b, spatialCutoff a b x = 1) ∧
      tsupport (spatialCutoff a b) ⊆ Set.Icc (a - 1) (b + 1) ∧
      eLpNorm (spatialCutoff a b) (1 : ℝ≥0∞) volume ≤ ENNReal.ofReal (b - a + 2) ∧
      eLpNorm (spatialCutoff a b) (2 : ℝ≥0∞) volume ≤
        ENNReal.ofReal (Real.sqrt (b - a + 2)) ∧
      eLpNorm (deriv (spatialCutoff a b)) (1 : ℝ≥0∞) volume ≤ 2 ∧
      eLpNorm (deriv (deriv (spatialCutoff a b))) (1 : ℝ≥0∞) volume ≤ 2 ^ 4 := by
  rcases smoothStepBounds with ⟨hfirst, hsecond, hthird, _⟩
  exact ⟨aux_spatialCutoff_pointwise a b,
    fun x hx ↦ aux_spatialCutoff_one_on hx,
    aux_spatialCutoff_tsupport,
    aux_spatialCutoff_l1,
    aux_spatialCutoff_l2 hab,
    aux_spatial_deriv_L1 hfirst a b,
    aux_spatial_deriv2_L1 hsecond hthird a b (aux_deriv2_spatial_ae a b)⟩

/--
The even low-frequency cutoff \(\eta\) in \(\label{def:dyadic-cutoffs}\):
\[
\eta(\xi)=s(2-|\xi|).
\]
-/
def lowFrequencyCutoff (ξ : ℝ) : ℝ :=
  smoothStep (2 - |ξ|)

/--
The cutoff \(\varphi\) in \(\label{def:dyadic-cutoffs}\):
\[
\varphi(\xi)=\eta(\xi)-\eta(2\xi).
\]
-/
def dyadicCutoff (ξ : ℝ) : ℝ :=
  lowFrequencyCutoff ξ - lowFrequencyCutoff (2 * ξ)

/--
The annular cutoff \(q\) in \(\label{def:dyadic-cutoffs}\):
\[
q(\xi)=\eta(\xi/2)-\eta(4\xi).
\]
-/
def annularCutoff (ξ : ℝ) : ℝ :=
  lowFrequencyCutoff (ξ / 2) - lowFrequencyCutoff (4 * ξ)

/--
Helper for \(\label{def:dyadic-cutoffs}\), used by
`dyadicReconstructionAndMultiplierBounds`: the annular cutoff is one on the
stated middle annulus.
-/
theorem aux_annularCutoff_one_on {ξ : ℝ}
    (hξ_lower : 1 / 2 ≤ |ξ|) (hξ_upper : |ξ| ≤ 2) :
    annularCutoff ξ = 1 := by
  have hone : lowFrequencyCutoff (ξ / 2) = 1 := by
    have hz : |ξ / 2| ≤ 1 := by
      rw [abs_div]
      norm_num
      linarith
    have hu0 : ¬ 2 - |ξ / 2| ≤ 0 := by linarith
    have hu1 : ¬ 2 - |ξ / 2| < 1 := by linarith
    unfold lowFrequencyCutoff smoothStep
    rw [ite_eq_right hu0, ite_eq_right hu1]
  have hzero : lowFrequencyCutoff (4 * ξ) = 0 := by
    have hz : 2 ≤ |4 * ξ| := by
      rw [abs_mul]
      norm_num
      linarith
    have hu : 2 - |4 * ξ| ≤ 0 := by linarith
    unfold lowFrequencyCutoff smoothStep
    rw [ite_eq_left hu]
  simp [annularCutoff, hone, hzero]

/--
Helper for \(\label{def:dyadic-cutoffs}\), used by
`dyadicReconstructionAndMultiplierBounds`: the annular cutoff vanishes
outside its stated support.
-/
theorem aux_annularCutoff_eq_zero_of_outside {ξ : ℝ}
    (hξ : |ξ| ≤ 1 / 4 ∨ 4 ≤ |ξ|) :
    annularCutoff ξ = 0 := by
  rcases hξ with hξ | hξ
  · have hone₁ : lowFrequencyCutoff (ξ / 2) = 1 := by
      have hz : |ξ / 2| ≤ 1 := by
        rw [abs_div]
        norm_num
        linarith
      have hu0 : ¬ 2 - |ξ / 2| ≤ 0 := by linarith
      have hu1 : ¬ 2 - |ξ / 2| < 1 := by linarith
      unfold lowFrequencyCutoff smoothStep
      rw [ite_eq_right hu0, ite_eq_right hu1]
    have hone₂ : lowFrequencyCutoff (4 * ξ) = 1 := by
      have hz : |4 * ξ| ≤ 1 := by
        rw [abs_mul]
        norm_num
        linarith
      have hu0 : ¬ 2 - |4 * ξ| ≤ 0 := by linarith
      have hu1 : ¬ 2 - |4 * ξ| < 1 := by linarith
      unfold lowFrequencyCutoff smoothStep
      rw [ite_eq_right hu0, ite_eq_right hu1]
    simp [annularCutoff, hone₁, hone₂]
  · have hzero₁ : lowFrequencyCutoff (ξ / 2) = 0 := by
      have hz : 2 ≤ |ξ / 2| := by
        rw [abs_div]
        norm_num
        linarith
      have hu : 2 - |ξ / 2| ≤ 0 := by linarith
      unfold lowFrequencyCutoff smoothStep
      rw [ite_eq_left hu]
    have hzero₂ : lowFrequencyCutoff (4 * ξ) = 0 := by
      have hz : 2 ≤ |4 * ξ| := by
        rw [abs_mul]
        norm_num
        linarith
      have hu : 2 - |4 * ξ| ≤ 0 := by linarith
      unfold lowFrequencyCutoff smoothStep
      rw [ite_eq_left hu]
    simp [annularCutoff, hzero₁, hzero₂]

/-- The low-frequency cutoff is one on the unit interval.  This auxiliary
cutoff calculation is used in `dyadicReconstructionAndMultiplierBounds` for
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_lowFrequencyCutoff_eq_one_of_abs_le_one {ξ : ℝ} (hξ : |ξ| ≤ 1) :
    lowFrequencyCutoff ξ = 1 := by
  unfold lowFrequencyCutoff
  apply aux_smoothStep_eq_one_of_one_le
  linarith

/-- The low-frequency cutoff vanishes outside the radius-two interval.  This
auxiliary cutoff calculation is used in
`dyadicReconstructionAndMultiplierBounds` for
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_lowFrequencyCutoff_eq_zero_of_two_le_abs {ξ : ℝ} (hξ : 2 ≤ |ξ|) :
    lowFrequencyCutoff ξ = 0 := by
  unfold lowFrequencyCutoff
  apply aux_smoothStep_eq_zero_of_nonpos
  linarith

/-- The dyadic cutoff vanishes outside its fixed annulus.  This is an
auxiliary support calculation for `dyadicReconstructionAndMultiplierBounds`
and \(\label{lem:dyadic-reconstruction}\). -/
lemma aux_dyadicCutoff_eq_zero_of_outside {ξ : ℝ}
    (hξ : |ξ| ≤ 1 / 2 ∨ 2 ≤ |ξ|) : dyadicCutoff ξ = 0 := by
  rcases hξ with hξ | hξ
  · have hη₁ : lowFrequencyCutoff ξ = 1 :=
      aux_lowFrequencyCutoff_eq_one_of_abs_le_one (by linarith)
    have hη₂ : lowFrequencyCutoff (2 * ξ) = 1 :=
      aux_lowFrequencyCutoff_eq_one_of_abs_le_one (by
        rw [abs_mul]
        norm_num
        linarith)
    simp [dyadicCutoff, hη₁, hη₂]
  · have hη₁ : lowFrequencyCutoff ξ = 0 :=
      aux_lowFrequencyCutoff_eq_zero_of_two_le_abs hξ
    have hη₂ : lowFrequencyCutoff (2 * ξ) = 0 :=
      aux_lowFrequencyCutoff_eq_zero_of_two_le_abs (by
        rw [abs_mul]
        norm_num
        linarith)
    simp [dyadicCutoff, hη₁, hη₂]

/-- The annular cutoff is identically one wherever the dyadic cutoff can be
nonzero.  This auxiliary multiplier identity is used in
`dyadicReconstructionAndMultiplierBounds` for
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_annularCutoff_mul_dyadicCutoff (ξ : ℝ) :
    (annularCutoff ξ : ℂ) * (dyadicCutoff ξ : ℂ) = dyadicCutoff ξ := by
  by_cases hφ : dyadicCutoff ξ = 0
  · simp [hφ]
  have hout : ¬ (|ξ| ≤ 1 / 2 ∨ 2 ≤ |ξ|) := by
    intro hout
    exact hφ (aux_dyadicCutoff_eq_zero_of_outside hout)
  have hlower : 1 / 2 ≤ |ξ| :=
    (lt_of_not_ge (not_or.mp hout).1).le
  have hupper : |ξ| ≤ 2 :=
    (lt_of_not_ge (not_or.mp hout).2).le
  have hq : annularCutoff ξ = 1 := aux_annularCutoff_one_on hlower hupper
  simp [hq]

/-- The finite dyadic partition telescopes to the low-frequency cutoff at
the smallest scale.  This is an auxiliary identity for
`dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_dyadic_telescoping (N : ℕ) (ξ : ℝ) :
    lowFrequencyCutoff ξ +
        ∑ k ∈ Finset.range N, dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) =
      lowFrequencyCutoff (ξ / (2 : ℝ) ^ N) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ih]
      unfold dyadicCutoff
      have hpow : (2 : ℝ) ^ (N + 1) = 2 * (2 : ℝ) ^ N := by
        rw [pow_succ]
        ring
      rw [show 2 * (ξ / (2 : ℝ) ^ (N + 1)) = ξ / (2 : ℝ) ^ N by
        rw [hpow]
        field_simp]
      ring

/-- A nonzero dyadic multiplier at scale \(k\) lies in the asserted dyadic
frequency annulus.  This is the elementary support calculation used in
`dyadicReconstructionAndMultiplierBounds` for
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_scaled_dyadicCutoff_support {k : ℕ} (hk : 1 ≤ k) {ξ : ℝ}
    (hξ : dyadicCutoff (ξ / (2 : ℝ) ^ k) ≠ 0) :
    (2 : ℝ) ^ (k - 1) ≤ |ξ| ∧ |ξ| ≤ (2 : ℝ) ^ (k + 1) := by
  have hout : ¬ (|ξ / (2 : ℝ) ^ k| ≤ 1 / 2 ∨ 2 ≤ |ξ / (2 : ℝ) ^ k|) := by
    intro hout
    exact hξ (aux_dyadicCutoff_eq_zero_of_outside hout)
  have hlower : 1 / 2 ≤ |ξ / (2 : ℝ) ^ k| :=
    (lt_of_not_ge (not_or.mp hout).1).le
  have hupper : |ξ / (2 : ℝ) ^ k| ≤ 2 :=
    (lt_of_not_ge (not_or.mp hout).2).le
  have hpow : 0 < (2 : ℝ) ^ k := by positivity
  have habs : |ξ / (2 : ℝ) ^ k| = |ξ| / (2 : ℝ) ^ k := by
    rw [abs_div, abs_of_nonneg (le_of_lt hpow)]
  constructor
  · rw [habs] at hlower
    have hlowmult : (1 / 2 : ℝ) * (2 : ℝ) ^ k ≤ |ξ| :=
      (le_div_iff₀ hpow).mp hlower
    calc
      (2 : ℝ) ^ (k - 1) = (1 / 2 : ℝ) * (2 : ℝ) ^ k := by
        field_simp
        rw [← pow_succ]
        have hindex : k - 1 + 1 = k := Nat.sub_add_cancel hk
        rw [hindex]
      _ ≤ |ξ| := hlowmult
  · rw [habs] at hupper
    have huppmult : |ξ| ≤ 2 * (2 : ℝ) ^ k := (div_le_iff₀ hpow).mp hupper
    calc
      |ξ| ≤ 2 * (2 : ℝ) ^ k := huppmult
      _ = (2 : ℝ) ^ (k + 1) := by
        rw [pow_succ]
        ring

/--
The raw convolution used for the dyadic maps in \(\label{def:dyadic-cutoffs}\).
It is written directly as a map of functions so that the dyadic operators also
apply to bounded inputs, as they do in the manuscript.
-/
noncomputable def aux_convolution (κ f : ℝ → ℂ) : ℝ → ℂ :=
  fun x ↦ ∫ t : ℝ, κ t * f (x - t)

/-- Rewrites the project's raw convolution as Mathlib's multiplication
convolution.  This auxiliary bridge is used in
`dyadicReconstructionAndMultiplierBounds` for
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_convolution_eq_measureTheory_convolution (κ f : ℝ → ℂ) :
    aux_convolution κ f = κ ⋆[ContinuousLinearMap.mul ℂ ℂ] f := rfl

/-- An `L¹` kernel gives an `L∞` bound for raw convolution from any a.e.
enorm bound on its right input.  This supplies the endpoint of the
multiplier estimate in `dyadicReconstructionAndMultiplierBounds` for
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_eLpNorm_aux_convolution_top_le_of_ae_enorm_bound
    (κ f : ℝ → ℂ) (hκ : Integrable κ volume) (C : ℝ≥0∞)
    (hf : ∀ᵐ y : ℝ ∂volume, ‖f y‖ₑ ≤ C) :
    eLpNorm (aux_convolution κ f) ∞ volume ≤ eLpNorm κ 1 volume * C := by
  rw [eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  filter_upwards with x
  have hfx : ∀ᵐ t : ℝ ∂volume, ‖f (x - t)‖ₑ ≤ C := by
    exact (volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae hf
  calc
    ‖aux_convolution κ f x‖ₑ = ‖∫ t : ℝ, κ t * f (x - t)‖ₑ := rfl
    _ ≤ ∫⁻ t : ℝ, ‖κ t * f (x - t)‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ t : ℝ, ‖κ t‖ₑ * ‖f (x - t)‖ₑ := by simp only [enorm_mul]
    _ ≤ ∫⁻ t : ℝ, ‖κ t‖ₑ * C := by
      apply lintegral_mono_ae
      filter_upwards [hfx] with t ht
      exact mul_le_mul_of_nonneg_left ht bot_le
    _ = (∫⁻ t : ℝ, ‖κ t‖ₑ) * C :=
      lintegral_mul_const'' C ((hκ.aestronglyMeasurable).enorm)
    _ = eLpNorm κ 1 volume * C := by rw [eLpNorm_one_eq_lintegral_enorm]

/-- The raw `L¹ * L∞ → L∞` convolution inequality used by
`dyadicReconstructionAndMultiplierBounds` for
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_eLpNorm_aux_convolution_top_le
    (κ f : ℝ → ℂ) (hκ : Integrable κ volume) :
    eLpNorm (aux_convolution κ f) ∞ volume ≤
      eLpNorm κ 1 volume * eLpNorm f ∞ volume := by
  exact aux_eLpNorm_aux_convolution_top_le_of_ae_enorm_bound κ f hκ
    (eLpNorm f ∞ volume)
    (enorm_ae_le_eLpNormEssSup f volume)

/-- A numerical `L¹` bound on a kernel yields the corresponding raw
`L∞` convolution inequality for
`dyadicReconstructionAndMultiplierBounds`. -/
lemma aux_eLpNorm_aux_convolution_top_le_of_eLpNorm_one_le
    (κ f : ℝ → ℂ) (hκ : Integrable κ volume) (C : ℝ≥0∞)
    (hκnorm : eLpNorm κ 1 volume ≤ C) :
    eLpNorm (aux_convolution κ f) ∞ volume ≤ C * eLpNorm f ∞ volume := by
  calc
    eLpNorm (aux_convolution κ f) ∞ volume ≤
        eLpNorm κ 1 volume * eLpNorm f ∞ volume :=
      aux_eLpNorm_aux_convolution_top_le κ f hκ
    _ ≤ C * eLpNorm f ∞ volume := mul_le_mul_left hκnorm _

/-- Raw convolution is insensitive to a.e. changes of either input.  This
is equality of the raw functions, as needed to use bounded representatives
in `dyadicReconstructionAndMultiplierBounds`. -/
lemma aux_convolution_congr_ae
    (κ κ' f f' : ℝ → ℂ) (hκ : κ =ᵐ[volume] κ') (hf : f =ᵐ[volume] f') :
    aux_convolution κ f = aux_convolution κ' f' := by
  rw [aux_convolution_eq_measureTheory_convolution,
    aux_convolution_eq_measureTheory_convolution]
  exact convolution_congr (ContinuousLinearMap.mul ℂ ℂ) hκ hf

/-- Raw convolution is insensitive to an a.e. change of its right input.
This specialization supports the endpoint estimate in
`dyadicReconstructionAndMultiplierBounds`. -/
lemma aux_convolution_congr_ae_right
    (κ f g : ℝ → ℂ) (hfg : f =ᵐ[volume] g) :
    aux_convolution κ f = aux_convolution κ g :=
  aux_convolution_congr_ae κ κ f g Filter.EventuallyEq.rfl hfg

/-- Two square-integrable functions have a pointwise-defined raw convolution.
This supplies the Fubini hypotheses used in
`dyadicReconstructionAndMultiplierBounds` for
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_convolutionExistsAt_of_memLp_two {f g : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (x : ℝ) :
    ConvolutionExistsAt f g x (ContinuousLinearMap.mul ℂ ℂ) volume := by
  rw [convolutionExistsAt_iff_integrable_swap]
  have hfx : MemLp (f ∘ fun t : ℝ ↦ x - t) 2 volume :=
    hf.comp_measurePreserving (volume.measurePreserving_sub_left x)
  change Integrable ((f ∘ fun t : ℝ ↦ x - t) * g) volume
  exact hfx.integrable_mul hg

/--
The scaled inverse-Fourier kernel for a multiplier `m`.  This is the kernel
whose Fourier multiplier is \(m(2^{-k}\cdot)\), and is used by `P` and `Q`
for \(\label{def:dyadic-cutoffs}\).
-/
noncomputable def aux_scaledInverseFourierKernel (m : ℝ → ℂ) (k : ℕ) : ℝ → ℂ :=
  fun x ↦ ((2 : ℝ) ^ k : ℂ) * inverseFourierTransform m ((2 : ℝ) ^ k * x)

/--
The dyadic multiplier \(P_k\) from \(\label{def:dyadic-cutoffs}\), in its
kernel form:
\[
P_0f=\check\eta*f,\qquad
P_kf=2^k\check\varphi(2^k\cdot)*f\quad(k\geq1).
\]
Whenever Fourier transforms are defined, this is equivalently
\(\widehat{P_0f}=\eta\widehat f\) and
\(\widehat{P_kf}(\xi)=\varphi(2^{-k}\xi)\widehat f(\xi)\).
-/
noncomputable def P (k : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  if k = 0 then
    aux_convolution (inverseFourierTransform fun ξ ↦ (lowFrequencyCutoff ξ : ℂ)) f
  else
    aux_convolution
      (aux_scaledInverseFourierKernel (fun ξ ↦ (dyadicCutoff ξ : ℂ)) k) f

/--
The dyadic multiplier \(Q_k\) from \(\label{def:dyadic-cutoffs}\), in its
kernel form:
\[
Q_kf=2^k\check q(2^k\cdot)*f.
\]
For \(k\geq1\), this is equivalently
\(\widehat{Q_kf}(\xi)=q(2^{-k}\xi)\widehat f(\xi)\).  The kernel form is
defined for all raw functions, including the bounded inputs used later in the
manuscript.
-/
noncomputable def Q (k : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  aux_convolution
    (aux_scaledInverseFourierKernel (fun ξ ↦ (annularCutoff ξ : ℂ)) k) f

/-- The scaled annular multiplier fixes the scaled dyadic multiplier.  This
Fourier-side algebra is used in `dyadicReconstructionAndMultiplierBounds`
for \(\label{lem:dyadic-reconstruction}\). -/
lemma aux_scaled_annularCutoff_mul_dyadicCutoff (k : ℕ) (ξ : ℝ) :
    (annularCutoff (ξ / (2 : ℝ) ^ k) : ℂ) *
        (dyadicCutoff (ξ / (2 : ℝ) ^ k) : ℂ) =
      dyadicCutoff (ξ / (2 : ℝ) ^ k) :=
  aux_annularCutoff_mul_dyadicCutoff (ξ / (2 : ℝ) ^ k)

/-- An a.e. Fourier multiplier identity gives the desired a.e. dyadic support.
This packages the elementary cutoff calculation for
`dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_ae_dyadic_support_of_fourier_multiplier {f : ℝ → ℂ} {k : ℕ}
    (hk : 1 ≤ k)
    (hfourier : aux_l2Fourier (P k f) =ᵐ[volume]
      fun ξ ↦ (dyadicCutoff (ξ / (2 : ℝ) ^ k) : ℂ) * aux_l2Fourier f ξ) :
    ∀ᵐ ξ ∂volume, aux_l2Fourier (P k f) ξ ≠ 0 →
      (2 : ℝ) ^ (k - 1) ≤ |ξ| ∧ |ξ| ≤ (2 : ℝ) ^ (k + 1) := by
  filter_upwards [hfourier] with ξ hξ
  intro hnonzero
  have hcut : dyadicCutoff (ξ / (2 : ℝ) ^ k) ≠ 0 := by
    intro hzero
    apply hnonzero
    rw [hξ, hzero]
    simp
  exact aux_scaled_dyadicCutoff_support hk hcut

/--
The multiplier
\[
m(\xi)=\frac{q(\xi)}{(2\pi i\xi)^2}
\]
used to prove \(\label{lem:dyadic-kernel-bounds}\).  This is an auxiliary
definition for `dyadicKernelBounds`.
-/
def aux_dyadicKernelMultiplier (ξ : ℝ) : ℂ :=
  (annularCutoff ξ : ℂ) /
    ((((2 * Real.pi : ℝ) : ℂ) * Complex.I * (ξ : ℂ)) ^ 2)

/-- The explicit constant in \(\label{lem:dyadic-kernel-bounds}\), used by
`dyadicKernelBounds`. -/
def C_dyadicKernelBounds : ℝ := 2 ^ 10

/-- The clamped coordinate used to make the continuity of the piecewise
polynomial cutoff explicit.  It is an auxiliary construction for
`dyadicKernelBounds` and \(\label{lem:dyadic-kernel-bounds}\). -/
noncomputable def aux_clampUnitInterval (u : ℝ) : ℝ := max 0 (min u 1)

/-- The clamp in `aux_clampUnitInterval` is continuous.  This auxiliary fact
is used in the Fourier-kernel proof for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_continuous_clampUnitInterval : Continuous aux_clampUnitInterval := by
  unfold aux_clampUnitInterval
  exact continuous_const.max (continuous_id.min continuous_const)

/-- An algebraic form of `smoothStep` through the continuous clamp.  It is
used to establish compact support and integrability in `dyadicKernelBounds`
for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_smoothStep_eq_clampUnitInterval (u : ℝ) :
    smoothStep u = 3 * aux_clampUnitInterval u ^ 2 - 2 * aux_clampUnitInterval u ^ 3 := by
  unfold smoothStep aux_clampUnitInterval
  split_ifs with hu0 hu1
  · have hmin : min u 1 = u := min_eq_left (by linarith)
    rw [hmin, max_eq_left (by linarith)]
    norm_num
  · rw [min_eq_left (by linarith), max_eq_right (by linarith)]
  · rw [min_eq_right (by linarith), max_eq_right (by norm_num)]
    norm_num

/-- Continuity of the polynomial smooth step, used by the interval
integration arguments for `dyadicKernelBounds` in
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_continuous_smoothStep : Continuous smoothStep := by
  rw [show smoothStep = fun u : ℝ ↦
      3 * aux_clampUnitInterval u ^ 2 - 2 * aux_clampUnitInterval u ^ 3 by
    ext u
    exact aux_smoothStep_eq_clampUnitInterval u]
  exact (continuous_const.mul (aux_continuous_clampUnitInterval.pow 2)).sub
    (continuous_const.mul (aux_continuous_clampUnitInterval.pow 3))

/-- An algebraic form of the first-derivative model from `smoothStepBounds`.
It supplies a continuous representative for the piecewise integration by
parts in `dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_smoothStepDerivative_eq_clampUnitInterval (u : ℝ) :
    aux_smoothStepDerivative u =
      6 * aux_clampUnitInterval u * (1 - aux_clampUnitInterval u) := by
  unfold aux_smoothStepDerivative aux_clampUnitInterval
  by_cases hu0 : u ≤ 0
  · rw [Set.indicator_of_notMem]
    · rw [min_eq_left (by linarith), max_eq_left (by linarith)]
      norm_num
    · simp [hu0]
  by_cases hu1 : u < 1
  · rw [Set.indicator_of_mem]
    · rw [min_eq_left hu1.le, max_eq_right (by linarith)]
      ring
    · exact ⟨lt_of_not_ge hu0, hu1⟩
  · rw [Set.indicator_of_notMem]
    · rw [min_eq_right (le_of_not_gt hu1), max_eq_right (by norm_num)]
      norm_num
    · simp [hu1]

/-- The first-derivative model is continuous.  This is needed for the second
piecewise integration by parts in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_continuous_smoothStepDerivative : Continuous aux_smoothStepDerivative := by
  rw [show aux_smoothStepDerivative = fun u : ℝ ↦
      6 * aux_clampUnitInterval u * (1 - aux_clampUnitInterval u) by
    ext u
    exact aux_smoothStepDerivative_eq_clampUnitInterval u]
  exact ((continuous_const.mul aux_continuous_clampUnitInterval).mul
    (continuous_const.sub aux_continuous_clampUnitInterval))

/-- Continuity of the low-frequency cutoff, used to make its compact support
available to `dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_continuous_lowFrequencyCutoff : Continuous lowFrequencyCutoff := by
  unfold lowFrequencyCutoff
  apply aux_continuous_smoothStep.comp
  exact continuous_const.sub continuous_abs

/-- Continuity of the annular cutoff used by `dyadicKernelBounds` in
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_continuous_annularCutoff : Continuous annularCutoff := by
  unfold annularCutoff
  have hdiv : Continuous (fun ξ : ℝ ↦ ξ / 2) := by
    have h : Continuous (fun ξ : ℝ ↦ ξ * (1 / 2 : ℝ)) :=
      continuous_id.mul continuous_const
    convert h using 1
    ext ξ
    ring
  exact (aux_continuous_lowFrequencyCutoff.comp hdiv).sub
      (aux_continuous_lowFrequencyCutoff.comp
        (continuous_const.mul continuous_id))

/-- The annular cutoff is uniformly bounded by one.  This is the local
Fourier-integral bound used in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_annularCutoff_norm_le_one (ξ : ℝ) : ‖annularCutoff ξ‖ ≤ 1 := by
  rw [annularCutoff, Real.norm_eq_abs]
  change |smoothStep (2 - |ξ / 2|) - smoothStep (2 - |4 * ξ|)| ≤ 1
  have hleft := aux_smoothStep_nonneg_le_one (2 - |ξ / 2|)
  have hright := aux_smoothStep_nonneg_le_one (2 - |4 * ξ|)
  rw [abs_le]
  constructor <;> linarith

/-- The support cut used to convert the annular cutoff to a compactly
supported integrand in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_annularCutoff_eq_zero_of_not_mem (ξ : ℝ)
    (hξ : ξ ∉ Set.Icc (-4 : ℝ) 4) : annularCutoff ξ = 0 := by
  apply aux_annularCutoff_eq_zero_of_outside
  right
  by_cases hleft : ξ < -4
  · rw [abs_of_neg (by linarith)]
    linarith
  · have hright : 4 < ξ := by
      by_contra hright
      apply hξ
      constructor <;> linarith
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- Compact support of the annular cutoff, an auxiliary integrability input
for `dyadicKernelBounds` in \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_annularCutoff_hasCompactSupport : HasCompactSupport annularCutoff := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-4 : ℝ) 4))
  intro ξ hξ
  exact aux_annularCutoff_eq_zero_of_not_mem ξ hξ

/-- Integrability of the complex-valued annular cutoff.  This supplies the
basic Fourier-integral estimate for `dyadicKernelBounds` in
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_annularCutoff_integrable :
    Integrable (fun ξ ↦ (annularCutoff ξ : ℂ)) volume := by
  have hsupport : HasCompactSupport (fun ξ ↦ (annularCutoff ξ : ℂ)) := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-4 : ℝ) 4))
    intro ξ hξ
    simp [aux_annularCutoff_eq_zero_of_not_mem ξ hξ]
  exact
    (Complex.continuous_ofReal.comp aux_continuous_annularCutoff).integrable_of_hasCompactSupport
    hsupport

/-- The oscillatory phase in the inverse Fourier integral.  This auxiliary
notation isolates the two integrations by parts used in `dyadicKernelBounds`
for \(\label{lem:dyadic-kernel-bounds}\). -/
noncomputable def aux_dyadicFourierPhase (x ξ : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I)

/-- A primitive of the Fourier phase away from the frequency origin.  It is
used by `aux_interval_fourier_ibp` for
\(\label{lem:dyadic-kernel-bounds}\). -/
noncomputable def aux_dyadicFourierPhasePrimitive (x ξ : ℝ) : ℂ :=
  aux_dyadicFourierPhase x ξ / (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- A second primitive of the Fourier phase.  It is the antiderivative of
`aux_dyadicFourierPhasePrimitive` used for the second integration by parts in
`dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
noncomputable def aux_dyadicFourierPhaseSecondPrimitive (x ξ : ℝ) : ℂ :=
  aux_dyadicFourierPhasePrimitive x ξ / (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- The phase primitive differentiates to the phase when `x` is nonzero.
This is the elementary oscillatory calculation used in both integrations by
parts for `dyadicKernelBounds` and \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_hasDerivAt_dyadicFourierPhasePrimitive (x ξ : ℝ) (hx : x ≠ 0) :
    HasDerivAt (aux_dyadicFourierPhasePrimitive x) (aux_dyadicFourierPhase x ξ) ξ := by
  let c : ℂ := ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I
  have hc : c ≠ 0 := by
    dsimp [c]
    apply mul_ne_zero
    · exact_mod_cast mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hx
    · exact Complex.I_ne_zero
  have hlin : HasDerivAt (fun t : ℝ ↦ (t : ℂ) * c) c ξ := by
    have hsmul : HasDerivAt (fun t : ℝ ↦ t • c) c ξ := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id ξ).smul_const c
    convert hsmul using 1
    ext t
    simp
  have hphase0 := hlin.cexp
  have hphase_eq : (fun t : ℝ ↦ Complex.exp ((t : ℂ) * c)) = aux_dyadicFourierPhase x := by
    funext t
    dsimp [c, aux_dyadicFourierPhase]
    push_cast
    congr 1
    ring
  have hphase : HasDerivAt (aux_dyadicFourierPhase x)
      (aux_dyadicFourierPhase x ξ * c) ξ := by
    rw [← hphase_eq]
    exact hphase0
  have hdiv := hphase.div_const c
  have hprim_eq : (fun t : ℝ ↦ aux_dyadicFourierPhase x t / c) =
      aux_dyadicFourierPhasePrimitive x := by
    funext t
    dsimp [aux_dyadicFourierPhasePrimitive, c]
  rw [← hprim_eq]
  simpa [hc] using hdiv

/-- Continuity of the phase primitive.  The zero-frequency branch is harmless
and the nonzero branch follows from its derivative calculation; this supports
the interval integrations for `dyadicKernelBounds` in
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_continuous_dyadicFourierPhasePrimitive (x : ℝ) :
    Continuous (aux_dyadicFourierPhasePrimitive x) := by
  by_cases hx : x = 0
  · subst x
    rw [show aux_dyadicFourierPhasePrimitive 0 = fun _ : ℝ ↦ 0 by
      ext ξ
      simp [aux_dyadicFourierPhasePrimitive]]
    exact continuous_const
  · exact continuous_iff_continuousAt.2 fun ξ ↦
      (aux_hasDerivAt_dyadicFourierPhasePrimitive x ξ hx).continuousAt

/-- The second phase primitive differentiates to the first primitive away
from zero.  This is the second oscillatory calculation in
`dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_hasDerivAt_dyadicFourierPhaseSecondPrimitive (x ξ : ℝ) (hx : x ≠ 0) :
    HasDerivAt (aux_dyadicFourierPhaseSecondPrimitive x)
      (aux_dyadicFourierPhasePrimitive x ξ) ξ := by
  let c : ℂ := ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I
  have hc : c ≠ 0 := by
    dsimp [c]
    apply mul_ne_zero
    · exact_mod_cast mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hx
    · exact Complex.I_ne_zero
  have hprim_eq : (fun t : ℝ ↦ aux_dyadicFourierPhase x t / c) =
      aux_dyadicFourierPhasePrimitive x := by
    funext t
    dsimp [aux_dyadicFourierPhasePrimitive, c]
  change HasDerivAt (fun t : ℝ ↦ aux_dyadicFourierPhasePrimitive x t / c)
    (aux_dyadicFourierPhasePrimitive x ξ) ξ
  have hdiv := (aux_hasDerivAt_dyadicFourierPhasePrimitive x ξ hx).div_const c
  rw [← hprim_eq]
  exact hdiv

/-- Continuity of the second phase primitive, needed for the second interval
integration by parts in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_continuous_dyadicFourierPhaseSecondPrimitive (x : ℝ) :
    Continuous (aux_dyadicFourierPhaseSecondPrimitive x) := by
  by_cases hx : x = 0
  · subst x
    rw [show aux_dyadicFourierPhaseSecondPrimitive 0 = fun _ : ℝ ↦ 0 by
      ext ξ
      simp [aux_dyadicFourierPhaseSecondPrimitive, aux_dyadicFourierPhasePrimitive]]
    exact continuous_const
  · exact continuous_iff_continuousAt.2 fun ξ ↦
      (aux_hasDerivAt_dyadicFourierPhaseSecondPrimitive x ξ hx).continuousAt

/-- Continuity of the oscillatory phase used in
`aux_interval_fourier_ibp` for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_continuous_dyadicFourierPhase (x : ℝ) : Continuous (aux_dyadicFourierPhase x) := by
  unfold aux_dyadicFourierPhase
  fun_prop

/-- A reusable integration-by-parts identity for a real compact interval and
the inverse-Fourier phase.  It is the basic interval step in the proof of
`dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_interval_fourier_ibp {a b x : ℝ} (hx : x ≠ 0)
    {u u' : ℝ → ℝ} (hu : ContinuousOn u (Set.uIcc a b))
    (huu' : ∀ t ∈ Set.Ioo (min a b) (max a b), HasDerivAt u (u' t) t)
    (hu' : IntervalIntegrable u' volume a b) :
    (∫ t in a..b, aux_dyadicFourierPhase x t * (u t : ℂ)) =
      (u b : ℂ) * aux_dyadicFourierPhasePrimitive x b -
        (u a : ℂ) * aux_dyadicFourierPhasePrimitive x a -
        ∫ t in a..b, (u' t : ℂ) * aux_dyadicFourierPhasePrimitive x t := by
  have hU : ContinuousOn (fun t : ℝ ↦ (u t : ℂ)) (Set.uIcc a b) := by
    intro t ht
    simpa [Function.comp_def] using
      (Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt (hu t ht))
  have hV : ContinuousOn (aux_dyadicFourierPhasePrimitive x) (Set.uIcc a b) :=
    (aux_continuous_dyadicFourierPhasePrimitive x).continuousOn
  have hUderiv : ∀ t ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt (fun t : ℝ ↦ (u t : ℂ)) (u' t : ℂ) t := by
    intro t ht
    have h := (huu' t ht).smul_const (1 : ℂ)
    simpa using h
  have hVderiv : ∀ t ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt (aux_dyadicFourierPhasePrimitive x) (aux_dyadicFourierPhase x t) t := by
    intro t _
    exact aux_hasDerivAt_dyadicFourierPhasePrimitive x t hx
  have hU' : IntervalIntegrable (fun t : ℝ ↦ (u' t : ℂ)) volume a b := by
    constructor
    · exact hu'.1.ofReal
    · exact hu'.2.ofReal
  have hV' : IntervalIntegrable (aux_dyadicFourierPhase x) volume a b :=
    (aux_continuous_dyadicFourierPhase x).intervalIntegrable a b
  simpa [mul_comm] using
    (intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hU hV hUderiv hVderiv
      hU' hV')

/-- The second integration-by-parts identity for the inverse-Fourier phase.
It applies the second phase primitive to the derivative pieces in
`dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_interval_fourier_ibp_second {a b x : ℝ} (hx : x ≠ 0)
    {u u' : ℝ → ℝ} (hu : ContinuousOn u (Set.uIcc a b))
    (huu' : ∀ t ∈ Set.Ioo (min a b) (max a b), HasDerivAt u (u' t) t)
    (hu' : IntervalIntegrable u' volume a b) :
    (∫ t in a..b, aux_dyadicFourierPhasePrimitive x t * (u t : ℂ)) =
      (u b : ℂ) * aux_dyadicFourierPhaseSecondPrimitive x b -
        (u a : ℂ) * aux_dyadicFourierPhaseSecondPrimitive x a -
        ∫ t in a..b, (u' t : ℂ) * aux_dyadicFourierPhaseSecondPrimitive x t := by
  have hU : ContinuousOn (fun t : ℝ ↦ (u t : ℂ)) (Set.uIcc a b) := by
    intro t ht
    simpa [Function.comp_def] using
      (Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt (hu t ht))
  have hV : ContinuousOn (aux_dyadicFourierPhaseSecondPrimitive x) (Set.uIcc a b) :=
    (aux_continuous_dyadicFourierPhaseSecondPrimitive x).continuousOn
  have hUderiv : ∀ t ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt (fun t : ℝ ↦ (u t : ℂ)) (u' t : ℂ) t := by
    intro t ht
    have h := (huu' t ht).smul_const (1 : ℂ)
    simpa using h
  have hVderiv : ∀ t ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt (aux_dyadicFourierPhaseSecondPrimitive x)
        (aux_dyadicFourierPhasePrimitive x t) t := by
    intro t _
    exact aux_hasDerivAt_dyadicFourierPhaseSecondPrimitive x t hx
  have hU' : IntervalIntegrable (fun t : ℝ ↦ (u' t : ℂ)) volume a b := by
    constructor
    · exact hu'.1.ofReal
    · exact hu'.2.ofReal
  have hV' : IntervalIntegrable (aux_dyadicFourierPhasePrimitive x) volume a b :=
    (aux_continuous_dyadicFourierPhasePrimitive x).intervalIntegrable a b
  simpa [mul_comm] using
    (intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hU hV hUderiv hVderiv
      hU' hV')

/-- The elementary real affine derivative used to describe each transition
piece of the annular cutoff in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_hasDerivAt_affine (a b ξ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ a + b * t) b ξ := by
  have h := (hasDerivAt_const ξ a).add ((hasDerivAt_id ξ).const_mul b)
  have heq : (fun t : ℝ ↦ a + b * t) =ᶠ[𝓝 ξ]
      ((fun _ : ℝ ↦ a) + fun y : ℝ ↦ b * y) :=
    Filter.Eventually.of_forall fun t ↦ rfl
  exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)

/-- Continuity of the real affine transition coordinates used in
`dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_continuous_affine (a b : ℝ) : Continuous (fun t : ℝ ↦ a + b * t) := by
  exact continuous_const.add (continuous_const.mul continuous_id)

/-- A generic compact transition piece for the four nonconstant portions of
the annular cutoff.  It is used only as proof infrastructure for
`dyadicKernelBounds` and \(\label{lem:dyadic-kernel-bounds}\). -/
noncomputable def aux_dyadicTransition (c e a b ξ : ℝ) : ℝ :=
  c + e * smoothStep (a + b * ξ)

/-- The first derivative model for `aux_dyadicTransition`, used in the first
and second integrations by parts for `dyadicKernelBounds` in
\(\label{lem:dyadic-kernel-bounds}\). -/
noncomputable def aux_dyadicTransitionDeriv (e a b ξ : ℝ) : ℝ :=
  e * b * aux_smoothStepDerivative (a + b * ξ)

/-- The polynomial second derivative on the open transition interval.  This
is the integrable model used in the final decay estimate of
`dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
noncomputable def aux_dyadicTransitionSecondDeriv (e a b ξ : ℝ) : ℝ :=
  e * b ^ 2 * (6 - 12 * (a + b * ξ))

/-- Continuity of a generic annular-cutoff transition, used by the interval
integrations in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_continuous_dyadicTransition (c e a b : ℝ) :
    Continuous (aux_dyadicTransition c e a b) := by
  unfold aux_dyadicTransition
  exact continuous_const.add
    (continuous_const.mul (aux_continuous_smoothStep.comp (aux_continuous_affine a b)))

/-- Continuity of the first-derivative transition model used in the second
integration by parts for `dyadicKernelBounds` in
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_continuous_dyadicTransitionDeriv (e a b : ℝ) :
    Continuous (aux_dyadicTransitionDeriv e a b) := by
  unfold aux_dyadicTransitionDeriv
  have hcomp : Continuous (fun ξ : ℝ ↦ aux_smoothStepDerivative (a + b * ξ)) := by
    simpa [Function.comp_def] using
      aux_continuous_smoothStepDerivative.comp (aux_continuous_affine a b)
  have hmul : Continuous (fun ξ : ℝ ↦ b * aux_smoothStepDerivative (a + b * ξ)) :=
    continuous_const.mul hcomp
  have hfinal : Continuous (fun ξ : ℝ ↦
      e * (b * aux_smoothStepDerivative (a + b * ξ))) :=
    continuous_const.mul hmul
  convert hfinal using 1
  ext ξ
  ring

/-- Continuity of the polynomial second-derivative model used to bound the
Fourier tail in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_continuous_dyadicTransitionSecondDeriv (e a b : ℝ) :
    Continuous (aux_dyadicTransitionSecondDeriv e a b) := by
  unfold aux_dyadicTransitionSecondDeriv
  fun_prop

/-- The derivative calculation on a transition interval.  It is the local
calculus input to the first integration by parts in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_hasDerivAt_dyadicTransition (c e a b ξ : ℝ)
    (hlow : 0 < a + b * ξ) (hhigh : a + b * ξ < 1) :
    HasDerivAt (aux_dyadicTransition c e a b)
      (aux_dyadicTransitionDeriv e a b ξ) ξ := by
  have hu0 : a + b * ξ ≠ 0 := ne_of_gt hlow
  have hu1 : a + b * ξ ≠ 1 := ne_of_lt hhigh
  have hstep := (aux_smoothStep_differentiableAt_of_ne (a + b * ξ) hu0 hu1).hasDerivAt
  have hcomp := hstep.comp ξ (aux_hasDerivAt_affine a b ξ)
  have hsum := (hasDerivAt_const ξ c).add (hcomp.const_mul e)
  have heq : aux_dyadicTransition c e a b =ᶠ[𝓝 ξ]
      ((fun _ : ℝ ↦ c) + fun t : ℝ ↦ e *
        (smoothStep ∘ fun y : ℝ ↦ a + b * y) t) :=
    Filter.Eventually.of_forall fun _ ↦ rfl
  exact (hsum.congr_of_eventuallyEq heq).congr_deriv (by
    have hderiv : deriv smoothStep (a + b * ξ) =
        aux_smoothStepDerivative (a + b * ξ) := by
      have hmem : a + b * ξ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hlow, hhigh⟩
      rw [aux_smoothStep_deriv_on_Ioo _ hlow hhigh,
        aux_smoothStepDerivative,
        Set.indicator_of_mem hmem]
    rw [hderiv]
    unfold aux_dyadicTransitionDeriv
    ring)

/-- The second local derivative calculation on a transition interval.  It
drives the second integration by parts in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_hasDerivAt_dyadicTransitionDeriv (e a b ξ : ℝ)
    (hlow : 0 < a + b * ξ) (hhigh : a + b * ξ < 1) :
    HasDerivAt (aux_dyadicTransitionDeriv e a b)
      (aux_dyadicTransitionSecondDeriv e a b ξ) ξ := by
  have hu0 : a + b * ξ ≠ 0 := ne_of_gt hlow
  have hu1 : a + b * ξ ≠ 1 := ne_of_lt hhigh
  have hstep := (aux_derivSmoothStep_differentiableAt_of_ne
    (a + b * ξ) hu0 hu1).hasDerivAt
  have hcomp := (hstep.comp ξ (aux_hasDerivAt_affine a b ξ)).const_mul (e * b)
  have hcont : ContinuousAt (fun t : ℝ ↦ a + b * t) ξ :=
    (aux_continuous_affine a b).continuousAt
  have hmem : a + b * ξ ∈ Set.Ioo 0 1 := ⟨hlow, hhigh⟩
  have hneigh : ∀ᶠ t : ℝ in 𝓝 ξ, a + b * t ∈ Set.Ioo 0 1 := by
    change (fun t : ℝ ↦ a + b * t) ⁻¹' Set.Ioo 0 1 ∈ 𝓝 ξ
    exact hcont.preimage_mem_nhds (isOpen_Ioo.mem_nhds hmem)
  have heq : aux_dyadicTransitionDeriv e a b =ᶠ[𝓝 ξ]
      ((fun t : ℝ ↦ e * b *
        (deriv smoothStep ∘ fun y : ℝ ↦ a + b * y) t)) := by
    filter_upwards [hneigh] with t ht
    have hderiv : deriv smoothStep (a + b * t) =
        aux_smoothStepDerivative (a + b * t) := by
      rw [aux_smoothStep_deriv_on_Ioo _ ht.1 ht.2,
        aux_smoothStepDerivative, Set.indicator_of_mem ht]
    simp only [aux_dyadicTransitionDeriv, Function.comp_apply]
    rw [hderiv]
  exact (hcomp.congr_of_eventuallyEq heq).congr_deriv (by
    rw [aux_smoothStep_secondDeriv_on_Ioo _ hlow hhigh]
    unfold aux_dyadicTransitionSecondDeriv
    ring)

/-- The outer negative transition of the annular cutoff, expressed using the
generic transition model for `dyadicKernelBounds` in
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_annularCutoff_eq_negOuter_transition {ξ : ℝ} (_hξa : -4 ≤ ξ) (hξb : ξ ≤ -2) :
    annularCutoff ξ = aux_dyadicTransition 0 1 2 (1 / 2 : ℝ) ξ := by
  unfold annularCutoff lowFrequencyCutoff aux_dyadicTransition
  rw [abs_of_nonpos (by linarith : ξ / 2 ≤ 0),
    abs_of_nonpos (by linarith : 4 * ξ ≤ 0)]
  have hfirst : 2 - -(ξ / 2) = 2 + (1 / 2 : ℝ) * ξ := by ring
  have hsecond : 2 - -(4 * ξ) = 2 + 4 * ξ := by ring
  rw [hfirst, hsecond, aux_smoothStep_eq_zero_of_nonpos (by linarith : 2 + 4 * ξ ≤ 0)]
  ring

/-- The inner negative transition of the annular cutoff, expressed using the
generic transition model for `dyadicKernelBounds` in
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_annularCutoff_eq_negInner_transition {ξ : ℝ} (hξa : -1 / 2 ≤ ξ)
    (hξb : ξ ≤ -1 / 4) :
    annularCutoff ξ = aux_dyadicTransition 1 (-1) 2 4 ξ := by
  unfold annularCutoff lowFrequencyCutoff aux_dyadicTransition
  rw [abs_of_nonpos (by linarith : ξ / 2 ≤ 0),
    abs_of_nonpos (by linarith : 4 * ξ ≤ 0)]
  have hfirst : 2 - -(ξ / 2) = 2 + ξ / 2 := by ring
  have hsecond : 2 - -(4 * ξ) = 2 + 4 * ξ := by ring
  rw [hfirst, hsecond, aux_smoothStep_eq_one_of_one_le (by linarith : 1 ≤ 2 + ξ / 2)]
  ring

/-- The inner positive transition of the annular cutoff, expressed using the
generic transition model for `dyadicKernelBounds` in
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_annularCutoff_eq_posInner_transition {ξ : ℝ} (hξa : 1 / 4 ≤ ξ)
    (hξb : ξ ≤ 1 / 2) :
    annularCutoff ξ = aux_dyadicTransition 1 (-1) 2 (-4) ξ := by
  unfold annularCutoff lowFrequencyCutoff aux_dyadicTransition
  rw [abs_of_nonneg (by linarith : 0 ≤ ξ / 2),
    abs_of_nonneg (by linarith : 0 ≤ 4 * ξ)]
  have hfirst : 2 - ξ / 2 = 2 + (1 / 2 : ℝ) * (-ξ) := by ring
  have hsecond : 2 - 4 * ξ = 2 + (-4 : ℝ) * ξ := by ring
  rw [hfirst, hsecond,
    aux_smoothStep_eq_one_of_one_le (by linarith : 1 ≤ 2 + (1 / 2 : ℝ) * (-ξ))]
  ring

/-- The outer positive transition of the annular cutoff, expressed using the
generic transition model for `dyadicKernelBounds` in
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_annularCutoff_eq_posOuter_transition {ξ : ℝ} (hξa : 2 ≤ ξ) (_hξb : ξ ≤ 4) :
    annularCutoff ξ = aux_dyadicTransition 0 1 2 (-1 / 2 : ℝ) ξ := by
  unfold annularCutoff lowFrequencyCutoff aux_dyadicTransition
  rw [abs_of_nonneg (by linarith : 0 ≤ ξ / 2),
    abs_of_nonneg (by linarith : 0 ≤ 4 * ξ)]
  have hfirst : 2 - ξ / 2 = 2 + (-1 / 2 : ℝ) * ξ := by ring
  rw [hfirst, aux_smoothStep_eq_zero_of_nonpos (by linarith : 2 - 4 * ξ ≤ 0)]
  ring

/-- The negative plateau of the annular cutoff, used to cancel the first
integration-by-parts boundary terms in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_annularCutoff_eq_one_negMiddle {ξ : ℝ} (hξa : -2 ≤ ξ) (hξb : ξ ≤ -1 / 2) :
    annularCutoff ξ = 1 := by
  unfold annularCutoff lowFrequencyCutoff
  rw [abs_of_nonpos (by linarith : ξ / 2 ≤ 0),
    abs_of_nonpos (by linarith : 4 * ξ ≤ 0)]
  have hfirst : 2 - -(ξ / 2) = 2 + ξ / 2 := by ring
  have hsecond : 2 - -(4 * ξ) = 2 + 4 * ξ := by ring
  rw [hfirst, hsecond,
    aux_smoothStep_eq_one_of_one_le (by linarith : 1 ≤ 2 + ξ / 2),
    aux_smoothStep_eq_zero_of_nonpos (by linarith : 2 + 4 * ξ ≤ 0)]
  norm_num

/-- The positive plateau of the annular cutoff, used to cancel the first
integration-by-parts boundary terms in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_annularCutoff_eq_one_posMiddle {ξ : ℝ} (hξa : 1 / 2 ≤ ξ) (hξb : ξ ≤ 2) :
    annularCutoff ξ = 1 := by
  unfold annularCutoff lowFrequencyCutoff
  rw [abs_of_nonneg (by linarith : 0 ≤ ξ / 2),
    abs_of_nonneg (by linarith : 0 ≤ 4 * ξ)]
  rw [aux_smoothStep_eq_one_of_one_le (by linarith : 1 ≤ 2 - ξ / 2),
    aux_smoothStep_eq_zero_of_nonpos (by linarith : 2 - 4 * ξ ≤ 0)]
  norm_num

/-- The central zero region of the annular cutoff, used in the interval
decomposition for `dyadicKernelBounds` in
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_annularCutoff_eq_zero_middle {ξ : ℝ} (hξa : -1 / 4 ≤ ξ) (hξb : ξ ≤ 1 / 4) :
    annularCutoff ξ = 0 := by
  apply aux_annularCutoff_eq_zero_of_outside
  left
  rw [abs_le]
  constructor <;> linarith

/-- The Fourier phase has unit norm.  This is used to estimate the second
integration-by-parts remainder in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_norm_dyadicFourierPhase (x ξ : ℝ) : ‖aux_dyadicFourierPhase x ξ‖ = 1 := by
  unfold aux_dyadicFourierPhase
  rw [Complex.norm_exp]
  simp

/-- Away from the unit frequency interval, the second Fourier phase primitive
has norm at most `1 / 16`.  This explicit decay factor is used in
`dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_norm_dyadicFourierPhaseSecondPrimitive_le (x ξ : ℝ) (hx : 1 ≤ |x|) :
    ‖aux_dyadicFourierPhaseSecondPrimitive x ξ‖ ≤ 1 / 16 := by
  let c : ℂ := ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I
  have hc : ‖c‖ = |2 * Real.pi * x| := by
    dsimp [c]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  have hr : 4 ≤ ‖c‖ := by
    rw [hc, abs_mul, abs_mul, abs_of_nonneg (by norm_num),
      abs_of_nonneg Real.pi_pos.le]
    calc
      4 = 2 * 2 * 1 := by norm_num
      _ ≤ 2 * Real.pi * |x| := by gcongr; exact Real.two_le_pi
  have hpos : 0 < ‖c‖ := lt_of_lt_of_le (by norm_num) hr
  have hphase : ‖aux_dyadicFourierPhase x ξ‖ = 1 := aux_norm_dyadicFourierPhase x ξ
  change ‖aux_dyadicFourierPhase x ξ / c / c‖ ≤ 1 / 16
  rw [norm_div, norm_div, hphase]
  calc
    1 / ‖c‖ / ‖c‖ ≤ 1 / 4 / 4 := by gcongr
    _ = 1 / 16 := by norm_num

/-- The quantitative `|x|⁻²` bound for the second Fourier phase primitive.
It converts the four compact transition remainders into an integrable tail in
`dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_norm_dyadicFourierPhaseSecondPrimitive_decay (x ξ : ℝ) (hx : x ≠ 0) :
    ‖aux_dyadicFourierPhaseSecondPrimitive x ξ‖ ≤ 1 / (16 * x ^ 2) := by
  let c : ℂ := ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I
  have hc : ‖c‖ = |2 * Real.pi * x| := by
    dsimp [c]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  have hxabs : 0 < |x| := abs_pos.mpr hx
  have hc' : ‖c‖ = 2 * Real.pi * |x| := by
    calc
      ‖c‖ = |2 * Real.pi * x| := hc
      _ = |2 * Real.pi| * |x| := by rw [abs_mul]
      _ = 2 * Real.pi * |x| := by
        rw [abs_mul, abs_of_nonneg (by norm_num), abs_of_nonneg Real.pi_pos.le]
  have hr : 4 * |x| ≤ ‖c‖ := by
    rw [hc']
    calc
      4 * |x| = 2 * 2 * |x| := by ring
      _ ≤ 2 * Real.pi * |x| := by gcongr; exact Real.two_le_pi
  have hpos : 0 < ‖c‖ := lt_of_lt_of_le (by positivity) hr
  have hphase : ‖aux_dyadicFourierPhase x ξ‖ = 1 := aux_norm_dyadicFourierPhase x ξ
  change ‖aux_dyadicFourierPhase x ξ / c / c‖ ≤ 1 / (16 * x ^ 2)
  rw [norm_div, norm_div, hphase]
  calc
    1 / ‖c‖ / ‖c‖ ≤ 1 / (4 * |x|) / (4 * |x|) := by gcongr
    _ = 1 / (16 * x ^ 2) := by
      have hsq : |x| ^ 2 = x ^ 2 := sq_abs x
      field_simp [hxabs.ne']
      nlinarith [hsq]

/-- A uniform second-derivative remainder estimate for a cubic transition.
This is the local `|x|⁻²` estimate used to control each of the four annular
transition intervals in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_transition_remainder_bound {l r x e a b K : ℝ} (hx : x ≠ 0)
    (harg : ∀ t ∈ Set.uIoc l r, 0 ≤ a + b * t ∧ a + b * t ≤ 1)
    (hK : |e| * b ^ 2 * 6 ≤ K) :
    ‖∫ t in l..r, (aux_dyadicTransitionSecondDeriv e a b t : ℂ) *
        aux_dyadicFourierPhaseSecondPrimitive x t‖ ≤
      (K / (16 * x ^ 2)) * |r - l| := by
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hden : 0 ≤ 1 / (16 * x ^ 2) := by positivity
  have hK0 : 0 ≤ K := by
    have : 0 ≤ |e| * b ^ 2 * 6 := by positivity
    linarith
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t ht
  have htarg := harg t ht
  have hpoly : |6 - 12 * (a + b * t)| ≤ 6 := by
    rw [abs_le]
    constructor <;> linarith
  have hsecond : ‖(aux_dyadicTransitionSecondDeriv e a b t : ℂ)‖ ≤ K := by
    rw [Complex.norm_real, Real.norm_eq_abs, aux_dyadicTransitionSecondDeriv,
      abs_mul, abs_mul, abs_of_nonneg (sq_nonneg b)]
    calc
      |e| * b ^ 2 * |6 - 12 * (a + b * t)| ≤ |e| * b ^ 2 * 6 := by gcongr
      _ ≤ K := hK
  rw [norm_mul]
  calc
    ‖(aux_dyadicTransitionSecondDeriv e a b t : ℂ)‖ *
        ‖aux_dyadicFourierPhaseSecondPrimitive x t‖ ≤
        K * (1 / (16 * x ^ 2)) := by
          gcongr
          exact aux_norm_dyadicFourierPhaseSecondPrimitive_decay x t hx
    _ = K / (16 * x ^ 2) := by ring

/-- Continuity of the annular Fourier integrand, used to split the compact
frequency integral in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_annularFourierIntegrand_continuous (x : ℝ) :
    Continuous (fun ξ : ℝ ↦ aux_dyadicFourierPhase x ξ * (annularCutoff ξ : ℂ)) := by
  exact (aux_continuous_dyadicFourierPhase x).mul
    (Complex.continuous_ofReal.comp aux_continuous_annularCutoff)

/-- Restricts the annular Fourier integral to its compact support for
`dyadicKernelBounds` and \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_annularFourier_integral_eq_interval (x : ℝ) :
    (∫ ξ : ℝ, aux_dyadicFourierPhase x ξ * (annularCutoff ξ : ℂ)) =
      ∫ ξ in (-4 : ℝ)..4, aux_dyadicFourierPhase x ξ * (annularCutoff ξ : ℂ) := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro ξ hξ
  rw [Function.mem_support] at hξ
  constructor
  · by_contra h
    have hle : ξ ≤ -4 := le_of_not_gt h
    have hq : annularCutoff ξ = 0 := by
      apply aux_annularCutoff_eq_zero_of_outside
      right
      rw [abs_of_nonpos (by linarith : ξ ≤ 0)]
      linarith
    apply hξ
    simp [hq]
  · by_contra h
    have hgt : 4 < ξ := lt_of_not_ge h
    have hq : annularCutoff ξ = 0 := by
      apply aux_annularCutoff_eq_zero_of_outside
      right
      rw [abs_of_nonneg (by linarith : 0 ≤ ξ)]
      linarith
    apply hξ
    simp [hq]

/-- The seven-interval decomposition of the annular Fourier integral used in
the two integrations by parts for `dyadicKernelBounds` and
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_annularFourier_integral_seven_parts (x : ℝ) :
    (∫ ξ in (-4 : ℝ)..4, aux_dyadicFourierPhase x ξ * (annularCutoff ξ : ℂ)) =
      (∫ ξ in (-4 : ℝ)..(-2), aux_dyadicFourierPhase x ξ * (annularCutoff ξ : ℂ)) +
      (∫ ξ in (-2 : ℝ)..(-1 / 2), aux_dyadicFourierPhase x ξ * (annularCutoff ξ : ℂ)) +
      (∫ ξ in (-1 / 2 : ℝ)..(-1 / 4), aux_dyadicFourierPhase x ξ * (annularCutoff ξ : ℂ)) +
      (∫ ξ in (-1 / 4 : ℝ)..(1 / 4), aux_dyadicFourierPhase x ξ * (annularCutoff ξ : ℂ)) +
      (∫ ξ in (1 / 4 : ℝ)..(1 / 2), aux_dyadicFourierPhase x ξ * (annularCutoff ξ : ℂ)) +
      (∫ ξ in (1 / 2 : ℝ)..2, aux_dyadicFourierPhase x ξ * (annularCutoff ξ : ℂ)) +
      (∫ ξ in (2 : ℝ)..4, aux_dyadicFourierPhase x ξ * (annularCutoff ξ : ℂ)) := by
  let g : ℝ → ℂ := fun ξ ↦ aux_dyadicFourierPhase x ξ * (annularCutoff ξ : ℂ)
  have hg : Continuous g := aux_annularFourierIntegrand_continuous x
  have hi (a b : ℝ) : IntervalIntegrable g volume a b := hg.intervalIntegrable a b
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hi (-4 : ℝ) (-2)) (hi (-2 : ℝ) (-1 / 2))
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hi (-4 : ℝ) (-1 / 2)) (hi (-1 / 2 : ℝ) (-1 / 4))
  have h3 := intervalIntegral.integral_add_adjacent_intervals
    (hi (-4 : ℝ) (-1 / 4)) (hi (-1 / 4 : ℝ) (1 / 4))
  have h4 := intervalIntegral.integral_add_adjacent_intervals
    (hi (-4 : ℝ) (1 / 4)) (hi (1 / 4 : ℝ) (1 / 2))
  have h5 := intervalIntegral.integral_add_adjacent_intervals
    (hi (-4 : ℝ) (1 / 2)) (hi (1 / 2 : ℝ) 2)
  have h6 := intervalIntegral.integral_add_adjacent_intervals
    (hi (-4 : ℝ) 2) (hi (2 : ℝ) 4)
  change (∫ ξ in (-4 : ℝ)..4, g ξ) = _
  rw [← h6, ← h5, ← h4, ← h3, ← h2, ← h1]

/-- Two integrations by parts for one cubic transition.  This keeps the
boundary cancellations in `dyadicKernelBounds` explicit. -/
lemma aux_transition_fourier_ibp_twice {l r x c e a b : ℝ} (hx : x ≠ 0)
    (harg : ∀ t ∈ Set.Ioo (min l r) (max l r),
      0 < a + b * t ∧ a + b * t < 1)
    (hl : a + b * l = 0 ∨ a + b * l = 1)
    (hr : a + b * r = 0 ∨ a + b * r = 1) :
    (∫ t in l..r, aux_dyadicFourierPhase x t *
        (aux_dyadicTransition c e a b t : ℂ)) =
      (aux_dyadicTransition c e a b r : ℂ) * aux_dyadicFourierPhasePrimitive x r -
        (aux_dyadicTransition c e a b l : ℂ) * aux_dyadicFourierPhasePrimitive x l +
      ∫ t in l..r, (aux_dyadicTransitionSecondDeriv e a b t : ℂ) *
        aux_dyadicFourierPhaseSecondPrimitive x t := by
  have hcont : ContinuousOn (aux_dyadicTransition c e a b) (Set.uIcc l r) :=
    (aux_continuous_dyadicTransition c e a b).continuousOn
  have hderiv : ∀ t ∈ Set.Ioo (min l r) (max l r),
      HasDerivAt (aux_dyadicTransition c e a b)
        (aux_dyadicTransitionDeriv e a b t) t := by
    intro t ht
    exact aux_hasDerivAt_dyadicTransition c e a b t (harg t ht).1 (harg t ht).2
  have hderiv_int : IntervalIntegrable (aux_dyadicTransitionDeriv e a b)
      volume l r := (aux_continuous_dyadicTransitionDeriv e a b).intervalIntegrable l r
  have hfirst := aux_interval_fourier_ibp hx hcont hderiv hderiv_int
  have hderiv_cont : ContinuousOn (aux_dyadicTransitionDeriv e a b) (Set.uIcc l r) :=
    (aux_continuous_dyadicTransitionDeriv e a b).continuousOn
  have hsecond_deriv : ∀ t ∈ Set.Ioo (min l r) (max l r),
      HasDerivAt (aux_dyadicTransitionDeriv e a b)
        (aux_dyadicTransitionSecondDeriv e a b t) t := by
    intro t ht
    exact aux_hasDerivAt_dyadicTransitionDeriv e a b t (harg t ht).1 (harg t ht).2
  have hsecond_int : IntervalIntegrable (aux_dyadicTransitionSecondDeriv e a b)
      volume l r :=
    (aux_continuous_dyadicTransitionSecondDeriv e a b).intervalIntegrable l r
  have hsecond := aux_interval_fourier_ibp_second hx hderiv_cont hsecond_deriv hsecond_int
  have hdl : aux_dyadicTransitionDeriv e a b l = 0 := by
    unfold aux_dyadicTransitionDeriv aux_smoothStepDerivative
    rcases hl with hl | hl
    · rw [hl]
      simp
    · rw [hl]
      simp
  have hdr : aux_dyadicTransitionDeriv e a b r = 0 := by
    unfold aux_dyadicTransitionDeriv aux_smoothStepDerivative
    rcases hr with hr | hr
    · rw [hr]
      simp
    · rw [hr]
      simp
  rw [hdl, hdr] at hsecond
  norm_num at hsecond
  have hsecond' :
      (∫ t in l..r, (aux_dyadicTransitionDeriv e a b t : ℂ) *
        aux_dyadicFourierPhasePrimitive x t) =
        -∫ t in l..r, (aux_dyadicTransitionSecondDeriv e a b t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t := by
    simpa only [mul_comm] using hsecond
  rw [hfirst, hsecond']
  ring

/-- The twice-integrated negative outer transition of the annular cutoff,
used in `dyadicKernelBounds`. -/
lemma aux_annularFourier_negOuter_ibp (x : ℝ) (hx : x ≠ 0) :
    (∫ t in (-4 : ℝ)..(-2), aux_dyadicFourierPhase x t *
        (annularCutoff t : ℂ)) =
      (annularCutoff (-2) : ℂ) * aux_dyadicFourierPhasePrimitive x (-2) -
        (annularCutoff (-4) : ℂ) * aux_dyadicFourierPhasePrimitive x (-4) +
      ∫ t in (-4 : ℝ)..(-2),
        (aux_dyadicTransitionSecondDeriv 1 2 (1 / 2 : ℝ) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t := by
  have htrans := aux_transition_fourier_ibp_twice (l := (-4 : ℝ)) (r := (-2 : ℝ))
    (x := x) (c := 0) (e := 1) (a := 2) (b := (1 / 2 : ℝ)) hx (by
      intro t ht
      have ht' : -4 < t ∧ t < -2 := by
        norm_num [min_eq_left, max_eq_right] at ht
        exact ht
      constructor <;> linarith) (by norm_num) (by norm_num)
  rw [intervalIntegral.integral_congr (fun t ht ↦ by
    have ht' : -4 ≤ t ∧ t ≤ -2 := by
      rw [Set.uIcc_of_le (by norm_num : (-4 : ℝ) ≤ -2)] at ht
      exact ht
    rw [aux_annularCutoff_eq_negOuter_transition ht'.1 ht'.2])]
  rw [aux_annularCutoff_eq_negOuter_transition (by norm_num) (by norm_num),
    aux_annularCutoff_eq_negOuter_transition (by norm_num) (by norm_num)]
  exact htrans

/-- The twice-integrated negative inner transition of the annular cutoff,
used in `dyadicKernelBounds`. -/
lemma aux_annularFourier_negInner_ibp (x : ℝ) (hx : x ≠ 0) :
    (∫ t in (-1 / 2 : ℝ)..(-1 / 4), aux_dyadicFourierPhase x t *
        (annularCutoff t : ℂ)) =
      (annularCutoff (-1 / 4) : ℂ) * aux_dyadicFourierPhasePrimitive x (-1 / 4) -
        (annularCutoff (-1 / 2) : ℂ) * aux_dyadicFourierPhasePrimitive x (-1 / 2) +
      ∫ t in (-1 / 2 : ℝ)..(-1 / 4),
        (aux_dyadicTransitionSecondDeriv (-1) 2 (4 : ℝ) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t := by
  have htrans := aux_transition_fourier_ibp_twice (l := (-1 / 2 : ℝ)) (r := (-1 / 4 : ℝ))
    (x := x) (c := 1) (e := -1) (a := 2) (b := (4 : ℝ)) hx (by
      intro t ht
      have ht' : -1 / 2 < t ∧ t < -1 / 4 := by
        norm_num [min_eq_left, max_eq_right] at ht
        constructor <;> linarith [ht.1, ht.2]
      constructor <;> linarith) (by norm_num) (by norm_num)
  rw [intervalIntegral.integral_congr (fun t ht ↦ by
    have ht' : -1 / 2 ≤ t ∧ t ≤ -1 / 4 := by
      rw [Set.uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ -1 / 4)] at ht
      exact ht
    rw [aux_annularCutoff_eq_negInner_transition ht'.1 ht'.2])]
  rw [aux_annularCutoff_eq_negInner_transition (by norm_num) (by norm_num),
    aux_annularCutoff_eq_negInner_transition (by norm_num) (by norm_num)]
  exact htrans

/-- The twice-integrated positive inner transition of the annular cutoff,
used in `dyadicKernelBounds`. -/
lemma aux_annularFourier_posInner_ibp (x : ℝ) (hx : x ≠ 0) :
    (∫ t in (1 / 4 : ℝ)..(1 / 2), aux_dyadicFourierPhase x t *
        (annularCutoff t : ℂ)) =
      (annularCutoff (1 / 2) : ℂ) * aux_dyadicFourierPhasePrimitive x (1 / 2) -
        (annularCutoff (1 / 4) : ℂ) * aux_dyadicFourierPhasePrimitive x (1 / 4) +
      ∫ t in (1 / 4 : ℝ)..(1 / 2),
        (aux_dyadicTransitionSecondDeriv (-1) 2 (-4 : ℝ) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t := by
  have htrans := aux_transition_fourier_ibp_twice (l := (1 / 4 : ℝ)) (r := (1 / 2 : ℝ))
    (x := x) (c := 1) (e := -1) (a := 2) (b := (-4 : ℝ)) hx (by
      intro t ht
      have ht' : 1 / 4 < t ∧ t < 1 / 2 := by
        norm_num [min_eq_left, max_eq_right] at ht
        exact ht
      constructor <;> linarith) (by norm_num) (by norm_num)
  rw [intervalIntegral.integral_congr (fun t ht ↦ by
    have ht' : 1 / 4 ≤ t ∧ t ≤ 1 / 2 := by
      rw [Set.uIcc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)] at ht
      exact ht
    rw [aux_annularCutoff_eq_posInner_transition ht'.1 ht'.2])]
  rw [aux_annularCutoff_eq_posInner_transition (by norm_num) (by norm_num),
    aux_annularCutoff_eq_posInner_transition (by norm_num) (by norm_num)]
  exact htrans

/-- The twice-integrated positive outer transition of the annular cutoff,
used in `dyadicKernelBounds`. -/
lemma aux_annularFourier_posOuter_ibp (x : ℝ) (hx : x ≠ 0) :
    (∫ t in (2 : ℝ)..4, aux_dyadicFourierPhase x t *
        (annularCutoff t : ℂ)) =
      (annularCutoff 4 : ℂ) * aux_dyadicFourierPhasePrimitive x 4 -
        (annularCutoff 2 : ℂ) * aux_dyadicFourierPhasePrimitive x 2 +
      ∫ t in (2 : ℝ)..4,
        (aux_dyadicTransitionSecondDeriv 1 2 (-1 / 2 : ℝ) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t := by
  have htrans := aux_transition_fourier_ibp_twice (l := (2 : ℝ)) (r := (4 : ℝ))
    (x := x) (c := 0) (e := 1) (a := 2) (b := (-1 / 2 : ℝ)) hx (by
      intro t ht
      have ht' : 2 < t ∧ t < 4 := by
        norm_num [min_eq_left, max_eq_right] at ht
        exact ht
      constructor <;> linarith) (by norm_num) (by norm_num)
  rw [intervalIntegral.integral_congr (fun t ht ↦ by
    have ht' : 2 ≤ t ∧ t ≤ 4 := by
      rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at ht
      exact ht
    rw [aux_annularCutoff_eq_posOuter_transition ht'.1 ht'.2])]
  rw [aux_annularCutoff_eq_posOuter_transition (by norm_num) (by norm_num),
    aux_annularCutoff_eq_posOuter_transition (by norm_num) (by norm_num)]
  exact htrans

/-- The first integration by parts on the negative plateau of the annular
cutoff, used in `dyadicKernelBounds`. -/
lemma aux_annularFourier_negPlateau_ibp (x : ℝ) (hx : x ≠ 0) :
    (∫ t in (-2 : ℝ)..(-1 / 2), aux_dyadicFourierPhase x t *
        (annularCutoff t : ℂ)) =
      (annularCutoff (-1 / 2) : ℂ) * aux_dyadicFourierPhasePrimitive x (-1 / 2) -
        (annularCutoff (-2) : ℂ) * aux_dyadicFourierPhasePrimitive x (-2) := by
  have h := aux_interval_fourier_ibp (a := (-2 : ℝ)) (b := (-1 / 2 : ℝ)) (x := x)
    (u := fun _ : ℝ ↦ 1) (u' := fun _ : ℝ ↦ 0) hx (by fun_prop) (by
      intro t _
      simpa using hasDerivAt_const t (1 : ℝ)) (by
        exact (continuous_const : Continuous fun _ : ℝ ↦ (0 : ℝ)).intervalIntegrable _ _)
  norm_num at h
  rw [intervalIntegral.integral_congr (fun t ht ↦ by
    have ht' : -2 ≤ t ∧ t ≤ -1 / 2 := by
      rw [Set.uIcc_of_le (by norm_num : (-2 : ℝ) ≤ -1 / 2)] at ht
      exact ht
    rw [aux_annularCutoff_eq_one_negMiddle ht'.1 ht'.2])]
  rw [aux_annularCutoff_eq_one_negMiddle (by norm_num) (by norm_num),
    aux_annularCutoff_eq_one_negMiddle (by norm_num) (by norm_num)]
  convert h using 1 <;> norm_num

/-- The first integration by parts on the positive plateau of the annular
cutoff, used in `dyadicKernelBounds`. -/
lemma aux_annularFourier_posPlateau_ibp (x : ℝ) (hx : x ≠ 0) :
    (∫ t in (1 / 2 : ℝ)..2, aux_dyadicFourierPhase x t *
        (annularCutoff t : ℂ)) =
      (annularCutoff 2 : ℂ) * aux_dyadicFourierPhasePrimitive x 2 -
        (annularCutoff (1 / 2) : ℂ) * aux_dyadicFourierPhasePrimitive x (1 / 2) := by
  have h := aux_interval_fourier_ibp (a := (1 / 2 : ℝ)) (b := (2 : ℝ)) (x := x)
    (u := fun _ : ℝ ↦ 1) (u' := fun _ : ℝ ↦ 0) hx (by fun_prop) (by
      intro t _
      simpa using hasDerivAt_const t (1 : ℝ)) (by
        exact (continuous_const : Continuous fun _ : ℝ ↦ (0 : ℝ)).intervalIntegrable _ _)
  norm_num at h
  rw [intervalIntegral.integral_congr (fun t ht ↦ by
    have ht' : 1 / 2 ≤ t ∧ t ≤ 2 := by
      rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at ht
      exact ht
    rw [aux_annularCutoff_eq_one_posMiddle ht'.1 ht'.2])]
  rw [aux_annularCutoff_eq_one_posMiddle (by norm_num) (by norm_num),
    aux_annularCutoff_eq_one_posMiddle (by norm_num) (by norm_num)]
  simpa using h

/-- The central annular-cutoff interval contributes zero to the Fourier
integral in `dyadicKernelBounds`. -/
lemma aux_annularFourier_middle_zero_integral (x : ℝ) :
    (∫ t in (-1 / 4 : ℝ)..(1 / 4), aux_dyadicFourierPhase x t *
        (annularCutoff t : ℂ)) = 0 := by
  rw [intervalIntegral.integral_congr (fun t ht ↦ by
    have ht' : -1 / 4 ≤ t ∧ t ≤ 1 / 4 := by
      rw [Set.uIcc_of_le (by norm_num : (-1 / 4 : ℝ) ≤ 1 / 4)] at ht
      exact ht
    rw [aux_annularCutoff_eq_zero_middle ht'.1 ht'.2])]
  simp

/-- The annular Fourier integral after its boundary terms have cancelled.
Only the four second-derivative remainders remain, as needed for
`dyadicKernelBounds`. -/
lemma aux_annularFourier_tail_representation (x : ℝ) (hx : x ≠ 0) :
    (∫ ξ : ℝ, aux_dyadicFourierPhase x ξ * (annularCutoff ξ : ℂ)) =
      (∫ t in (-4 : ℝ)..(-2),
        (aux_dyadicTransitionSecondDeriv 1 2 (1 / 2 : ℝ) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      (∫ t in (-1 / 2 : ℝ)..(-1 / 4),
        (aux_dyadicTransitionSecondDeriv (-1) 2 (4 : ℝ) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      (∫ t in (1 / 4 : ℝ)..(1 / 2),
        (aux_dyadicTransitionSecondDeriv (-1) 2 (-4 : ℝ) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      ∫ t in (2 : ℝ)..4,
        (aux_dyadicTransitionSecondDeriv 1 2 (-1 / 2 : ℝ) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t := by
  rw [aux_annularFourier_integral_eq_interval, aux_annularFourier_integral_seven_parts]
  rw [aux_annularFourier_negOuter_ibp x hx, aux_annularFourier_negPlateau_ibp x hx,
    aux_annularFourier_negInner_ibp x hx, aux_annularFourier_middle_zero_integral x,
    aux_annularFourier_posInner_ibp x hx, aux_annularFourier_posPlateau_ibp x hx,
    aux_annularFourier_posOuter_ibp x hx]
  have hnegOuter : annularCutoff (-4 : ℝ) = 0 :=
    aux_annularCutoff_eq_zero_of_outside (Or.inr (by norm_num))
  have hnegInner : annularCutoff (-1 / 4 : ℝ) = 0 :=
    aux_annularCutoff_eq_zero_of_outside (Or.inl (by norm_num))
  have hposInner : annularCutoff (1 / 4 : ℝ) = 0 :=
    aux_annularCutoff_eq_zero_of_outside (Or.inl (by norm_num))
  have hposOuter : annularCutoff (4 : ℝ) = 0 :=
    aux_annularCutoff_eq_zero_of_outside (Or.inr (by norm_num))
  rw [hnegOuter, hnegInner, hposInner, hposOuter]
  simp; ring

/-- The `|x|⁻²` tail estimate for the inverse Fourier kernel of the annular
cutoff, used in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_annularFourier_tail_norm (x : ℝ) (hx : x ≠ 0) :
    ‖∫ ξ : ℝ, aux_dyadicFourierPhase x ξ * (annularCutoff ξ : ℂ)‖ ≤ 4 / x ^ 2 := by
  rw [aux_annularFourier_tail_representation x hx]
  have houterNeg := aux_transition_remainder_bound
    (l := (-4 : ℝ)) (r := (-2 : ℝ)) (x := x) (e := 1) (a := 2) (b := (1 / 2 : ℝ))
    (K := 3 / 2) hx (by
      intro t ht
      have ht' : -4 < t ∧ t ≤ -2 := by
        rw [Set.uIoc_of_le (by norm_num : (-4 : ℝ) ≤ -2)] at ht
        exact ht
      constructor <;> linarith) (by norm_num)
  have hinnerNeg := aux_transition_remainder_bound
    (l := (-1 / 2 : ℝ)) (r := (-1 / 4 : ℝ)) (x := x) (e := -1) (a := 2) (b := (4 : ℝ))
    (K := 96) hx (by
      intro t ht
      have ht' : -1 / 2 < t ∧ t ≤ -1 / 4 := by
        rw [Set.uIoc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ -1 / 4)] at ht
        exact ht
      constructor <;> linarith) (by norm_num)
  have hinnerPos := aux_transition_remainder_bound
    (l := (1 / 4 : ℝ)) (r := (1 / 2 : ℝ)) (x := x) (e := -1) (a := 2) (b := (-4 : ℝ))
    (K := 96) hx (by
      intro t ht
      have ht' : 1 / 4 < t ∧ t ≤ 1 / 2 := by
        rw [Set.uIoc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)] at ht
        exact ht
      constructor <;> linarith) (by norm_num)
  have houterPos := aux_transition_remainder_bound
    (l := (2 : ℝ)) (r := (4 : ℝ)) (x := x) (e := 1) (a := 2) (b := (-1 / 2 : ℝ))
    (K := 3 / 2) hx (by
      intro t ht
      have ht' : 2 < t ∧ t ≤ 4 := by
        rw [Set.uIoc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at ht
        exact ht
      constructor <;> linarith) (by norm_num)
  calc
    ‖(∫ t in (-4 : ℝ)..(-2),
        (aux_dyadicTransitionSecondDeriv 1 2 (1 / 2 : ℝ) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      (∫ t in (-1 / 2 : ℝ)..(-1 / 4),
        (aux_dyadicTransitionSecondDeriv (-1) 2 (4 : ℝ) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      (∫ t in (1 / 4 : ℝ)..(1 / 2),
        (aux_dyadicTransitionSecondDeriv (-1) 2 (-4 : ℝ) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      ∫ t in (2 : ℝ)..4,
        (aux_dyadicTransitionSecondDeriv 1 2 (-1 / 2 : ℝ) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t‖ ≤
        ‖∫ t in (-4 : ℝ)..(-2),
          (aux_dyadicTransitionSecondDeriv 1 2 (1 / 2 : ℝ) t : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x t‖ +
        ‖∫ t in (-1 / 2 : ℝ)..(-1 / 4),
          (aux_dyadicTransitionSecondDeriv (-1) 2 (4 : ℝ) t : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x t‖ +
        ‖∫ t in (1 / 4 : ℝ)..(1 / 2),
          (aux_dyadicTransitionSecondDeriv (-1) 2 (-4 : ℝ) t : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x t‖ +
        ‖∫ t in (2 : ℝ)..4,
          (aux_dyadicTransitionSecondDeriv 1 2 (-1 / 2 : ℝ) t : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x t‖ := by
      exact norm_add_le_of_le
        (norm_add_le_of_le (norm_add_le _ _) le_rfl) le_rfl
    _ ≤ (3 / 2 / (16 * x ^ 2)) * |(-2 : ℝ) - (-4)| +
        (96 / (16 * x ^ 2)) * |(-1 / 4 : ℝ) - (-1 / 2)| +
        (96 / (16 * x ^ 2)) * |(1 / 2 : ℝ) - (1 / 4)| +
        (3 / 2 / (16 * x ^ 2)) * |(4 : ℝ) - 2| := by
      gcongr
    _ ≤ 4 / x ^ 2 := by
      have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
      have hsum :
          (3 / 2 / (16 * x ^ 2)) * |(-2 : ℝ) - (-4)| +
            (96 / (16 * x ^ 2)) * |(-1 / 4 : ℝ) - (-1 / 2)| +
            (96 / (16 * x ^ 2)) * |(1 / 2 : ℝ) - (1 / 4)| +
            (3 / 2 / (16 * x ^ 2)) * |(4 : ℝ) - 2| =
              (27 / 8 : ℝ) / x ^ 2 := by
        rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ -2 - -4),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ -1 / 4 - -1 / 2),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2 - 1 / 4),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4 - 2)]
        field_simp [hx2.ne']
        ring
      rw [hsum]
      apply (div_le_div_iff_of_pos_right hx2).2
      norm_num

/-- The inverse Fourier transform of the annular cutoff in its explicit
oscillatory-integral form, used by `dyadicKernelBounds`. -/
lemma aux_inverseFourierTransform_annular_eq_phase (x : ℝ) :
    inverseFourierTransform (fun ξ ↦ (annularCutoff ξ : ℂ)) x =
      ∫ ξ : ℝ, aux_dyadicFourierPhase x ξ * (annularCutoff ξ : ℂ) := by
  rw [inverseFourierTransform, Real.fourierInv_eq']
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  congr 3
  rw [Real.inner_apply]
  push_cast
  ring

/-- The pointwise `|x|⁻²` bound for the annular inverse Fourier kernel,
used to integrate its tail in `dyadicKernelBounds`. -/
lemma aux_annular_inverseFourier_tail_bound (x : ℝ) (hx : x ≠ 0) :
    ‖inverseFourierTransform (fun ξ ↦ (annularCutoff ξ : ℂ)) x‖ ≤ 4 / x ^ 2 := by
  rw [aux_inverseFourierTransform_annular_eq_phase]
  exact aux_annularFourier_tail_norm x hx

/-- A compact-support estimate for the `L¹` norm of the annular cutoff,
used for the local kernel bound in `dyadicKernelBounds`. -/
lemma aux_annularCutoff_norm_integral_le_eight :
    (∫ ξ : ℝ, ‖(annularCutoff ξ : ℂ)‖) ≤ 8 := by
  let s : Set ℝ := Set.Icc (-4 : ℝ) 4
  have hs : MeasurableSet s := measurableSet_Icc
  let h : ℝ → ℝ := s.indicator (fun _ ↦ (1 : ℝ))
  have hqint : Integrable (fun ξ : ℝ ↦ ‖(annularCutoff ξ : ℂ)‖) volume :=
    aux_annularCutoff_integrable.norm
  have hsfinite : volume s ≠ ∞ := by
    simp [s, Real.volume_Icc]
  have hint : Integrable h volume := by
    exact (integrableOn_const hsfinite).integrable_indicator hs
  have hpoint : (fun ξ : ℝ ↦ ‖(annularCutoff ξ : ℂ)‖) ≤ h := by
    intro ξ
    by_cases hξ : ξ ∈ s
    · rw [show h ξ = 1 by simp [h, hξ]]
      simpa only [Complex.norm_real] using aux_annularCutoff_norm_le_one ξ
    · rw [show h ξ = 0 by simp [h, hξ]]
      change ‖(annularCutoff ξ : ℂ)‖ ≤ 0
      simp [aux_annularCutoff_eq_zero_of_not_mem ξ hξ]
  calc
    (∫ ξ : ℝ, ‖(annularCutoff ξ : ℂ)‖) ≤ ∫ ξ : ℝ, h ξ :=
      integral_mono hqint hint hpoint
    _ = volume.real s := by
      change (∫ ξ : ℝ, s.indicator (fun _ ↦ (1 : ℝ)) ξ) = volume.real s
      simpa only [smul_eq_mul, mul_one] using
        (integral_indicator_const (μ := volume) (1 : ℝ) hs)
    _ = 8 := by
      rw [show s = Set.Icc (-4 : ℝ) 4 by rfl,
        Real.volume_real_Icc_of_le (by norm_num)]
      norm_num

/-- A uniform bound for the annular inverse Fourier kernel, used on the
bounded spatial region in `dyadicKernelBounds`. -/
lemma aux_annular_inverseFourier_uniform_bound (x : ℝ) :
    ‖inverseFourierTransform (fun ξ ↦ (annularCutoff ξ : ℂ)) x‖ ≤ 8 := by
  change ‖VectorFourier.fourierIntegral 𝐞 volume (-(innerₗ ℝ))
      (fun ξ : ℝ ↦ (annularCutoff ξ : ℂ)) x‖ ≤ 8
  calc
    ‖VectorFourier.fourierIntegral 𝐞 volume (-(innerₗ ℝ))
        (fun ξ : ℝ ↦ (annularCutoff ξ : ℂ)) x‖ ≤
        ∫ ξ : ℝ, ‖(annularCutoff ξ : ℂ)‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (-(innerₗ ℝ)) _ x
    _ ≤ 8 := aux_annularCutoff_norm_integral_le_eight

/-- The exact `L¹` norm of the rational majorant used to integrate an
inverse-Fourier kernel in `dyadicKernelBounds`. -/
lemma aux_annular_kernel_majorant_eLpNorm :
    eLpNorm (fun x : ℝ ↦ (16 : ℝ) / (1 + x ^ 2)) (1 : ℝ≥0∞) volume =
      ENNReal.ofReal (16 * Real.pi) := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  have hnonneg : ∀ x : ℝ, 0 ≤ (16 : ℝ) / (1 + x ^ 2) := by
    intro x
    positivity
  have hfun : (fun x : ℝ ↦ ‖((16 : ℝ) / (1 + x ^ 2))‖ₑ) =
      fun x ↦ ENNReal.ofReal ((16 : ℝ) / (1 + x ^ 2)) := by
    funext x
    rw [← ofReal_norm]
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]
  rw [hfun]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · have hreal : (∫ x : ℝ, (16 : ℝ) / (1 + x ^ 2)) = 16 * Real.pi := by
      calc
        (∫ x : ℝ, (16 : ℝ) / (1 + x ^ 2)) =
            ∫ x : ℝ, (16 : ℝ) * (1 + x ^ 2)⁻¹ := by
              apply integral_congr_ae
              filter_upwards with x
              rw [div_eq_mul_inv]
        _ = 16 * ∫ x : ℝ, (1 + x ^ 2)⁻¹ := by
              rw [MeasureTheory.integral_const_mul]
        _ = 16 * Real.pi := by rw [integral_univ_inv_one_add_sq]
    rw [hreal]
  · exact (integrable_inv_one_add_sq.const_mul 16)
  · exact ae_of_all _ hnonneg

/-- The numerical bound for the rational majorant in
`dyadicKernelBounds`. -/
lemma aux_annular_kernel_majorant_eLpNorm_le :
    eLpNorm (fun x : ℝ ↦ (16 : ℝ) / (1 + x ^ 2)) (1 : ℝ≥0∞) volume ≤
      (2 ^ 6 : ℝ≥0∞) := by
  rw [aux_annular_kernel_majorant_eLpNorm]
  norm_num only [Nat.reducePow]
  have hreal : 16 * Real.pi ≤ (64 : ℝ) := by
    nlinarith [Real.pi_le_four]
  simpa using ENNReal.ofReal_le_ofReal hreal

/-- Converts a local bound and a `|x|⁻²` tail bound into the explicit `L¹`
kernel estimate used for the annular cutoff in `dyadicKernelBounds`. -/
lemma aux_eLpNorm_le_of_local_tail {F : ℝ → ℂ}
    (hlocal : ∀ x : ℝ, ‖F x‖ ≤ 8)
    (htail : ∀ x : ℝ, x ≠ 0 → ‖F x‖ ≤ 4 / x ^ 2) :
    eLpNorm F (1 : ℝ≥0∞) volume ≤ (2 ^ 6 : ℝ≥0∞) := by
  have hpoint : ∀ x : ℝ, ‖F x‖ ≤ 16 / (1 + x ^ 2) := by
    intro x
    by_cases hx : |x| ≤ 1
    · calc
        ‖F x‖ ≤ 8 := hlocal x
        _ ≤ 16 / (1 + x ^ 2) := by
          have hsq : x ^ 2 ≤ 1 := by
            rw [← sq_abs x]
            nlinarith [abs_nonneg x]
          have hpos : 0 < 1 + x ^ 2 := by positivity
          rw [le_div_iff₀ hpos]
          nlinarith
    · have hx' : 1 ≤ |x| := le_of_not_ge hx
      have hx0 : x ≠ 0 := by
        intro hzero
        have : ¬ (1 : ℝ) ≤ 0 := by norm_num
        exact this (by simpa [hzero] using hx')
      calc
        ‖F x‖ ≤ 4 / x ^ 2 := htail x hx0
        _ ≤ 16 / (1 + x ^ 2) := by
          have hsq : 1 ≤ x ^ 2 := by
            rw [← sq_abs x]
            nlinarith [abs_nonneg x]
          have hpos : 0 < x ^ 2 := sq_pos_of_ne_zero hx0
          have hpos' : 0 < 1 + x ^ 2 := by positivity
          rw [div_le_div_iff₀ hpos hpos']
          nlinarith
  calc
    eLpNorm F (1 : ℝ≥0∞) volume ≤
        eLpNorm (fun x : ℝ ↦ (16 : ℝ) / (1 + x ^ 2)) (1 : ℝ≥0∞) volume :=
      eLpNorm_mono (by
        intro x
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hpoint x)
    _ ≤ 2 ^ 6 := aux_annular_kernel_majorant_eLpNorm_le

/-- The real reciprocal factor in the dyadic multiplier.  It exposes the
removable zero-frequency singularity in `dyadicKernelBounds`. -/
noncomputable def aux_dyadicKernelReciprocal (ξ : ℝ) : ℝ :=
  -((2 * Real.pi) ^ 2)⁻¹ * (ξ⁻¹) ^ 2

/-- The first derivative model for `aux_dyadicKernelReciprocal`, used in the
two integrations by parts for `dyadicKernelBounds`. -/
noncomputable def aux_dyadicKernelReciprocalDeriv (ξ : ℝ) : ℝ :=
  2 * ((2 * Real.pi) ^ 2)⁻¹ * (ξ⁻¹) ^ 3

/-- The second derivative model for `aux_dyadicKernelReciprocal`, used to
bound multiplier Fourier remainders in `dyadicKernelBounds`. -/
noncomputable def aux_dyadicKernelReciprocalSecondDeriv (ξ : ℝ) : ℝ :=
  -6 * ((2 * Real.pi) ^ 2)⁻¹ * (ξ⁻¹) ^ 4

/-- The reciprocal-weighted cubic transition used for the multiplier kernel
in `dyadicKernelBounds`. -/
noncomputable def aux_dyadicTransitionMultiplier (c e a b ξ : ℝ) : ℝ :=
  aux_dyadicTransition c e a b ξ * aux_dyadicKernelReciprocal ξ

/-- The first derivative model for a reciprocal-weighted cubic transition,
used in `dyadicKernelBounds`. -/
noncomputable def aux_dyadicTransitionMultiplierDeriv (c e a b ξ : ℝ) : ℝ :=
  aux_dyadicTransitionDeriv e a b ξ * aux_dyadicKernelReciprocal ξ +
    aux_dyadicTransition c e a b ξ * aux_dyadicKernelReciprocalDeriv ξ

/-- The second derivative model for a reciprocal-weighted cubic transition,
used for multiplier tail estimates in `dyadicKernelBounds`. -/
noncomputable def aux_dyadicTransitionMultiplierSecondDeriv (c e a b ξ : ℝ) : ℝ :=
  (aux_dyadicTransitionSecondDeriv e a b ξ * aux_dyadicKernelReciprocal ξ +
      aux_dyadicTransitionDeriv e a b ξ * aux_dyadicKernelReciprocalDeriv ξ) +
    (aux_dyadicTransitionDeriv e a b ξ * aux_dyadicKernelReciprocalDeriv ξ +
      aux_dyadicTransition c e a b ξ * aux_dyadicKernelReciprocalSecondDeriv ξ)

/-- Identifies the complex multiplier with its real reciprocal-weighted
form away from zero for `dyadicKernelBounds`. -/
lemma aux_dyadicKernelMultiplier_eq_scalar (ξ : ℝ) (_hξ : ξ ≠ 0) :
    aux_dyadicKernelMultiplier ξ =
      ((annularCutoff ξ * aux_dyadicKernelReciprocal ξ : ℝ) : ℂ) := by
  unfold aux_dyadicKernelMultiplier aux_dyadicKernelReciprocal
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp
  simp only [Complex.I_sq]
  ring

/-- Differentiates the reciprocal factor away from zero for
`dyadicKernelBounds`. -/
lemma aux_dyadicKernelReciprocal_hasDerivAt (ξ : ℝ) (hξ : ξ ≠ 0) :
    HasDerivAt aux_dyadicKernelReciprocal
      (2 * ((2 * Real.pi) ^ 2)⁻¹ * (ξ⁻¹) ^ 3) ξ := by
  unfold aux_dyadicKernelReciprocal
  have hinv : HasDerivAt (fun t : ℝ ↦ t⁻¹) (-(ξ ^ 2)⁻¹) ξ := hasDerivAt_inv hξ
  have hsq := hinv.pow 2
  have h := hsq.const_mul (-((2 * Real.pi) ^ 2)⁻¹)
  have hfun : (fun y : ℝ ↦ -((2 * Real.pi) ^ 2)⁻¹ * y⁻¹ ^ 2) =ᶠ[𝓝 ξ]
      (fun y ↦ -((2 * Real.pi) ^ 2)⁻¹ * ((fun t : ℝ ↦ t⁻¹) ^ 2) y) :=
    Filter.Eventually.of_forall (fun _ ↦ rfl)
  apply (h.congr_of_eventuallyEq hfun).congr_deriv
  field_simp [hξ]
  norm_num
  field_simp [hξ]

/-- Differentiates the first reciprocal derivative away from zero for
`dyadicKernelBounds`. -/
lemma aux_dyadicKernelReciprocalDeriv_hasDerivAt (ξ : ℝ) (hξ : ξ ≠ 0) :
    HasDerivAt (fun t ↦ 2 * ((2 * Real.pi) ^ 2)⁻¹ * (t⁻¹) ^ 3)
      (-6 * ((2 * Real.pi) ^ 2)⁻¹ * (ξ⁻¹) ^ 4) ξ := by
  have hinv : HasDerivAt (fun t : ℝ ↦ t⁻¹) (-(ξ ^ 2)⁻¹) ξ := hasDerivAt_inv hξ
  have hpow := hinv.pow 3
  have h := hpow.const_mul (2 * ((2 * Real.pi) ^ 2)⁻¹)
  have hfun : (fun y : ℝ ↦ 2 * ((2 * Real.pi) ^ 2)⁻¹ * y⁻¹ ^ 3) =ᶠ[𝓝 ξ]
      (fun y ↦ 2 * ((2 * Real.pi) ^ 2)⁻¹ * ((fun t : ℝ ↦ t⁻¹) ^ 3) y) :=
    Filter.Eventually.of_forall (fun _ ↦ rfl)
  apply (h.congr_of_eventuallyEq hfun).congr_deriv
  field_simp [hξ]
  norm_num
  field_simp [hξ]

/-- The derivative identity for a reciprocal-weighted transition, used in
the multiplier integration by parts in `dyadicKernelBounds`. -/
lemma aux_dyadicTransitionMultiplier_hasDerivAt (c e a b ξ : ℝ)
    (harg_low : 0 < a + b * ξ) (harg_high : a + b * ξ < 1) (hξ : ξ ≠ 0) :
    HasDerivAt (aux_dyadicTransitionMultiplier c e a b)
      (aux_dyadicTransitionMultiplierDeriv c e a b ξ) ξ := by
  have hT := aux_hasDerivAt_dyadicTransition c e a b ξ harg_low harg_high
  have hR := aux_dyadicKernelReciprocal_hasDerivAt ξ hξ
  change HasDerivAt
    (fun t : ℝ ↦ aux_dyadicTransition c e a b t * aux_dyadicKernelReciprocal t)
    (aux_dyadicTransitionDeriv e a b ξ * aux_dyadicKernelReciprocal ξ +
      aux_dyadicTransition c e a b ξ * (2 * ((2 * Real.pi) ^ 2)⁻¹ * (ξ⁻¹) ^ 3)) ξ
  exact hT.mul hR

/-- The second derivative identity for a reciprocal-weighted transition,
used in the tail estimate of `dyadicKernelBounds`. -/
lemma aux_dyadicTransitionMultiplierDeriv_hasDerivAt (c e a b ξ : ℝ)
    (harg_low : 0 < a + b * ξ) (harg_high : a + b * ξ < 1) (hξ : ξ ≠ 0) :
    HasDerivAt (aux_dyadicTransitionMultiplierDeriv c e a b)
      (aux_dyadicTransitionMultiplierSecondDeriv c e a b ξ) ξ := by
  have hT := aux_hasDerivAt_dyadicTransition c e a b ξ harg_low harg_high
  have hT' := aux_hasDerivAt_dyadicTransitionDeriv e a b ξ harg_low harg_high
  have hR := aux_dyadicKernelReciprocal_hasDerivAt ξ hξ
  have hR' := aux_dyadicKernelReciprocalDeriv_hasDerivAt ξ hξ
  change HasDerivAt
    (fun t : ℝ ↦
      aux_dyadicTransitionDeriv e a b t * aux_dyadicKernelReciprocal t +
        aux_dyadicTransition c e a b t * (2 * ((2 * Real.pi) ^ 2)⁻¹ * (t⁻¹) ^ 3))
    ((aux_dyadicTransitionSecondDeriv e a b ξ * aux_dyadicKernelReciprocal ξ +
        aux_dyadicTransitionDeriv e a b ξ *
          (2 * ((2 * Real.pi) ^ 2)⁻¹ * (ξ⁻¹) ^ 3)) +
      (aux_dyadicTransitionDeriv e a b ξ *
          (2 * ((2 * Real.pi) ^ 2)⁻¹ * (ξ⁻¹) ^ 3) +
        aux_dyadicTransition c e a b ξ *
          (-6 * ((2 * Real.pi) ^ 2)⁻¹ * (ξ⁻¹) ^ 4))) ξ
  exact (hT'.mul hR).add (hT.mul hR')

/-- A reciprocal bound away from the central annulus, used for the multiplier
kernel estimate in `dyadicKernelBounds`. -/
lemma aux_inv_abs_le_four {ξ : ℝ} (hξ : (1 / 4 : ℝ) ≤ |ξ|) :
    |ξ|⁻¹ ≤ 4 := by
  calc
    |ξ|⁻¹ ≤ (1 / 4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hξ
    _ = 4 := by norm_num

/-- A numerical reciprocal-factor estimate from the lower bound for π,
used in `dyadicKernelBounds`. -/
lemma aux_dyadicKernelReciprocal_constant_le_sixteenth :
    ((2 * Real.pi) ^ 2)⁻¹ ≤ (1 / 16 : ℝ) := by
  have hbase : 4 ≤ 2 * Real.pi := by nlinarith [Real.two_le_pi]
  have hsquare : 16 ≤ (2 * Real.pi) ^ 2 := by nlinarith
  calc
    ((2 * Real.pi) ^ 2)⁻¹ ≤ (16 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hsquare
    _ = 1 / 16 := by norm_num

/-- The reciprocal factor is at most one on the support of the dyadic
multiplier, used in `dyadicKernelBounds`. -/
lemma aux_dyadicKernelReciprocal_abs_le_one {ξ : ℝ} (hξ : (1 / 4 : ℝ) ≤ |ξ|) :
    |aux_dyadicKernelReciprocal ξ| ≤ 1 := by
  have hC := aux_dyadicKernelReciprocal_constant_le_sixteenth
  have hinv := aux_inv_abs_le_four hξ
  rw [aux_dyadicKernelReciprocal, abs_mul, abs_neg, abs_inv, abs_pow,
    abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi), abs_pow, abs_inv]
  calc
    ((2 * Real.pi) ^ 2)⁻¹ * (|ξ|⁻¹) ^ 2 ≤ (1 / 16 : ℝ) * 4 ^ 2 := by gcongr
    _ = 1 := by norm_num

/-- The first reciprocal derivative is uniformly bounded on the dyadic
multiplier support, used in `dyadicKernelBounds`. -/
lemma aux_dyadicKernelReciprocalDeriv_abs_le_eight {ξ : ℝ}
    (hξ : (1 / 4 : ℝ) ≤ |ξ|) :
    |aux_dyadicKernelReciprocalDeriv ξ| ≤ 8 := by
  have hC := aux_dyadicKernelReciprocal_constant_le_sixteenth
  have hinv := aux_inv_abs_le_four hξ
  rw [aux_dyadicKernelReciprocalDeriv, abs_mul, abs_mul, abs_of_nonneg (by norm_num),
    abs_inv, abs_pow, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi), abs_pow, abs_inv]
  calc
    2 * ((2 * Real.pi) ^ 2)⁻¹ * (|ξ|⁻¹) ^ 3 ≤
        2 * (1 / 16 : ℝ) * 4 ^ 3 := by gcongr
    _ = 8 := by norm_num

/-- The second reciprocal derivative is uniformly bounded on the dyadic
multiplier support, used in `dyadicKernelBounds`. -/
lemma aux_dyadicKernelReciprocalSecondDeriv_abs_le_ninetysix {ξ : ℝ}
    (hξ : (1 / 4 : ℝ) ≤ |ξ|) :
    |aux_dyadicKernelReciprocalSecondDeriv ξ| ≤ 96 := by
  have hC := aux_dyadicKernelReciprocal_constant_le_sixteenth
  have hinv := aux_inv_abs_le_four hξ
  rw [aux_dyadicKernelReciprocalSecondDeriv, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (by norm_num), abs_inv, abs_pow,
    abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi), abs_pow, abs_inv]
  calc
    6 * ((2 * Real.pi) ^ 2)⁻¹ * (|ξ|⁻¹) ^ 4 ≤
        6 * (1 / 16 : ℝ) * 4 ^ 4 := by gcongr
    _ = 96 := by norm_num

/-- A crude but explicit bound for a reciprocal-weighted transition's second
derivative, used in the multiplier tail estimate of `dyadicKernelBounds`. -/
lemma aux_dyadicTransitionMultiplierSecondDeriv_abs_le_1024 {c e a b ξ : ℝ}
    (hfreq : (1 / 4 : ℝ) ≤ |ξ|)
    (hT : |aux_dyadicTransition c e a b ξ| ≤ 1)
    (hT' : |aux_dyadicTransitionDeriv e a b ξ| ≤ 24)
    (hT'' : |aux_dyadicTransitionSecondDeriv e a b ξ| ≤ 96) :
    |aux_dyadicTransitionMultiplierSecondDeriv c e a b ξ| ≤ 1024 := by
  have hR := aux_dyadicKernelReciprocal_abs_le_one hfreq
  have hR' := aux_dyadicKernelReciprocalDeriv_abs_le_eight hfreq
  have hR'' := aux_dyadicKernelReciprocalSecondDeriv_abs_le_ninetysix hfreq
  rw [aux_dyadicTransitionMultiplierSecondDeriv]
  calc
    |(aux_dyadicTransitionSecondDeriv e a b ξ * aux_dyadicKernelReciprocal ξ +
        aux_dyadicTransitionDeriv e a b ξ * aux_dyadicKernelReciprocalDeriv ξ) +
      (aux_dyadicTransitionDeriv e a b ξ * aux_dyadicKernelReciprocalDeriv ξ +
        aux_dyadicTransition c e a b ξ * aux_dyadicKernelReciprocalSecondDeriv ξ)| ≤
        |aux_dyadicTransitionSecondDeriv e a b ξ * aux_dyadicKernelReciprocal ξ| +
          |aux_dyadicTransitionDeriv e a b ξ * aux_dyadicKernelReciprocalDeriv ξ| +
            (|aux_dyadicTransitionDeriv e a b ξ * aux_dyadicKernelReciprocalDeriv ξ| +
              |aux_dyadicTransition c e a b ξ * aux_dyadicKernelReciprocalSecondDeriv ξ|) := by
        calc
          _ ≤ |aux_dyadicTransitionSecondDeriv e a b ξ * aux_dyadicKernelReciprocal ξ +
              aux_dyadicTransitionDeriv e a b ξ * aux_dyadicKernelReciprocalDeriv ξ| +
              |aux_dyadicTransitionDeriv e a b ξ * aux_dyadicKernelReciprocalDeriv ξ +
                aux_dyadicTransition c e a b ξ * aux_dyadicKernelReciprocalSecondDeriv ξ| :=
              abs_add_le _ _
          _ ≤ _ := by gcongr <;> exact abs_add_le _ _
    _ ≤ 96 * 1 + 24 * 8 + (24 * 8 + 1 * 96) := by
      simp only [abs_mul]
      gcongr
    _ ≤ 1024 := by norm_num

/-- A global derivative bound for the smooth-step derivative, used in the
multiplier transition estimate of `dyadicKernelBounds`. -/
lemma aux_smoothStepDerivative_abs_le_six (u : ℝ) :
    |aux_smoothStepDerivative u| ≤ 6 := by
  rw [aux_smoothStepDerivative_eq_clampUnitInterval]
  let z : ℝ := aux_clampUnitInterval u
  have hz0 : 0 ≤ z := by exact le_max_left _ _
  have hz1 : z ≤ 1 := by exact max_le (by norm_num) (min_le_right _ _)
  have hprod0 : 0 ≤ z * (1 - z) := mul_nonneg hz0 (sub_nonneg.mpr hz1)
  have hprod : z * (1 - z) ≤ 1 := by nlinarith
  change |6 * z * (1 - z)| ≤ 6
  rw [abs_of_nonneg (by nlinarith)]
  nlinarith

/-- A crude first derivative bound for a cubic transition, used in
`dyadicKernelBounds`. -/
lemma aux_dyadicTransitionDeriv_abs_le_24 {e a b ξ : ℝ}
    (he : |e| ≤ 1) (hb : |b| ≤ 4) :
    |aux_dyadicTransitionDeriv e a b ξ| ≤ 24 := by
  rw [aux_dyadicTransitionDeriv, abs_mul, abs_mul]
  calc
    |e| * |b| * |aux_smoothStepDerivative (a + b * ξ)| ≤ 1 * 4 * 6 := by
      gcongr
      exact aux_smoothStepDerivative_abs_le_six _
    _ = 24 := by norm_num

/-- A crude second derivative bound for a cubic transition, used in
`dyadicKernelBounds`. -/
lemma aux_dyadicTransitionSecondDeriv_abs_le_96 {e a b ξ : ℝ}
    (he : |e| ≤ 1) (hb : |b| ≤ 4)
    (hu : 0 ≤ a + b * ξ ∧ a + b * ξ ≤ 1) :
    |aux_dyadicTransitionSecondDeriv e a b ξ| ≤ 96 := by
  have hpoly : |6 - 12 * (a + b * ξ)| ≤ 6 := by
    rw [abs_le]
    constructor <;> linarith
  rw [aux_dyadicTransitionSecondDeriv, abs_mul, abs_mul, abs_pow]
  calc
    |e| * |b| ^ 2 * |6 - 12 * (a + b * ξ)| ≤ 1 * 4 ^ 2 * 6 := by
      gcongr
    _ = 96 := by norm_num

/-- Identifies the multiplier on its negative outer transition for
`dyadicKernelBounds`. -/
lemma aux_dyadicKernelMultiplier_eq_negOuter_transition {ξ : ℝ} (hξa : -4 ≤ ξ)
    (hξb : ξ ≤ -2) :
    aux_dyadicKernelMultiplier ξ =
      (aux_dyadicTransitionMultiplier 0 1 2 (1 / 2 : ℝ) ξ : ℂ) := by
  rw [aux_dyadicKernelMultiplier_eq_scalar ξ (by linarith),
    aux_annularCutoff_eq_negOuter_transition hξa hξb]
  rfl

/-- Identifies the multiplier on its negative inner transition for
`dyadicKernelBounds`. -/
lemma aux_dyadicKernelMultiplier_eq_negInner_transition {ξ : ℝ} (hξa : -1 / 2 ≤ ξ)
    (hξb : ξ ≤ -1 / 4) :
    aux_dyadicKernelMultiplier ξ =
      (aux_dyadicTransitionMultiplier 1 (-1) 2 4 ξ : ℂ) := by
  rw [aux_dyadicKernelMultiplier_eq_scalar ξ (by linarith),
    aux_annularCutoff_eq_negInner_transition hξa hξb]
  rfl

/-- Identifies the multiplier on its positive inner transition for
`dyadicKernelBounds`. -/
lemma aux_dyadicKernelMultiplier_eq_posInner_transition {ξ : ℝ} (hξa : 1 / 4 ≤ ξ)
    (hξb : ξ ≤ 1 / 2) :
    aux_dyadicKernelMultiplier ξ =
      (aux_dyadicTransitionMultiplier 1 (-1) 2 (-4) ξ : ℂ) := by
  rw [aux_dyadicKernelMultiplier_eq_scalar ξ (by linarith),
    aux_annularCutoff_eq_posInner_transition hξa hξb]
  rfl

/-- Identifies the multiplier on its positive outer transition for
`dyadicKernelBounds`. -/
lemma aux_dyadicKernelMultiplier_eq_posOuter_transition {ξ : ℝ} (hξa : 2 ≤ ξ)
    (hξb : ξ ≤ 4) :
    aux_dyadicKernelMultiplier ξ =
      (aux_dyadicTransitionMultiplier 0 1 2 (-1 / 2 : ℝ) ξ : ℂ) := by
  rw [aux_dyadicKernelMultiplier_eq_scalar ξ (by linarith),
    aux_annularCutoff_eq_posOuter_transition hξa hξb]
  rfl

/-- Identifies the multiplier on the negative annular plateau for
`dyadicKernelBounds`. -/
lemma aux_dyadicKernelMultiplier_eq_negMiddle {ξ : ℝ} (hξa : -2 ≤ ξ) (hξb : ξ ≤ -1 / 2) :
    aux_dyadicKernelMultiplier ξ = (aux_dyadicKernelReciprocal ξ : ℂ) := by
  rw [aux_dyadicKernelMultiplier_eq_scalar ξ (by linarith),
    aux_annularCutoff_eq_one_negMiddle hξa hξb]
  norm_num

/-- Identifies the multiplier on the positive annular plateau for
`dyadicKernelBounds`. -/
lemma aux_dyadicKernelMultiplier_eq_posMiddle {ξ : ℝ} (hξa : 1 / 2 ≤ ξ) (hξb : ξ ≤ 2) :
    aux_dyadicKernelMultiplier ξ = (aux_dyadicKernelReciprocal ξ : ℂ) := by
  rw [aux_dyadicKernelMultiplier_eq_scalar ξ (by linarith),
    aux_annularCutoff_eq_one_posMiddle hξa hξb]
  norm_num

/-- The multiplier vanishes on the central zero interval of the annular
cutoff, used in `dyadicKernelBounds`. -/
lemma aux_dyadicKernelMultiplier_eq_zero_middle {ξ : ℝ} (hξa : -1 / 4 ≤ ξ)
    (hξb : ξ ≤ 1 / 4) :
    aux_dyadicKernelMultiplier ξ = 0 := by
  unfold aux_dyadicKernelMultiplier
  rw [aux_annularCutoff_eq_zero_middle hξa hξb]
  simp

/-- The second derivative of the negative outer multiplier transition has a
uniform explicit bound for `dyadicKernelBounds`. -/
lemma aux_negOuter_multiplier_second_abs_le_1024 {ξ : ℝ}
    (hξa : -4 ≤ ξ) (hξb : ξ ≤ -2) :
    |aux_dyadicTransitionMultiplierSecondDeriv 0 1 2 (1 / 2 : ℝ) ξ| ≤ 1024 := by
  have hfreq : (1 / 4 : ℝ) ≤ |ξ| := by
    rw [abs_of_neg (by linarith)]
    linarith
  have hT : |aux_dyadicTransition 0 1 2 (1 / 2 : ℝ) ξ| ≤ 1 := by
    rw [← aux_annularCutoff_eq_negOuter_transition hξa hξb]
    exact aux_annularCutoff_norm_le_one ξ
  refine aux_dyadicTransitionMultiplierSecondDeriv_abs_le_1024 hfreq hT ?_ ?_
  · exact aux_dyadicTransitionDeriv_abs_le_24 (by norm_num) (by norm_num)
  · apply aux_dyadicTransitionSecondDeriv_abs_le_96 (by norm_num) (by norm_num)
    constructor <;> linarith

/-- The second derivative of the negative inner multiplier transition has a
uniform explicit bound for `dyadicKernelBounds`. -/
lemma aux_negInner_multiplier_second_abs_le_1024 {ξ : ℝ}
    (hξa : -1 / 2 ≤ ξ) (hξb : ξ ≤ -1 / 4) :
    |aux_dyadicTransitionMultiplierSecondDeriv 1 (-1) 2 4 ξ| ≤ 1024 := by
  have hfreq : (1 / 4 : ℝ) ≤ |ξ| := by
    rw [abs_of_neg (by linarith)]
    linarith
  have hT : |aux_dyadicTransition 1 (-1) 2 4 ξ| ≤ 1 := by
    rw [← aux_annularCutoff_eq_negInner_transition hξa hξb]
    exact aux_annularCutoff_norm_le_one ξ
  refine aux_dyadicTransitionMultiplierSecondDeriv_abs_le_1024 hfreq hT ?_ ?_
  · exact aux_dyadicTransitionDeriv_abs_le_24 (by norm_num) (by norm_num)
  · apply aux_dyadicTransitionSecondDeriv_abs_le_96 (by norm_num) (by norm_num)
    constructor <;> linarith

/-- The second derivative of the positive inner multiplier transition has a
uniform explicit bound for `dyadicKernelBounds`. -/
lemma aux_posInner_multiplier_second_abs_le_1024 {ξ : ℝ}
    (hξa : 1 / 4 ≤ ξ) (hξb : ξ ≤ 1 / 2) :
    |aux_dyadicTransitionMultiplierSecondDeriv 1 (-1) 2 (-4) ξ| ≤ 1024 := by
  have hfreq : (1 / 4 : ℝ) ≤ |ξ| := by
    rw [abs_of_nonneg (by linarith)]
    exact hξa
  have hT : |aux_dyadicTransition 1 (-1) 2 (-4) ξ| ≤ 1 := by
    rw [← aux_annularCutoff_eq_posInner_transition hξa hξb]
    exact aux_annularCutoff_norm_le_one ξ
  refine aux_dyadicTransitionMultiplierSecondDeriv_abs_le_1024 hfreq hT ?_ ?_
  · exact aux_dyadicTransitionDeriv_abs_le_24 (by norm_num) (by norm_num)
  · apply aux_dyadicTransitionSecondDeriv_abs_le_96 (by norm_num) (by norm_num)
    constructor <;> linarith

/-- The second derivative of the positive outer multiplier transition has a
uniform explicit bound for `dyadicKernelBounds`. -/
lemma aux_posOuter_multiplier_second_abs_le_1024 {ξ : ℝ}
    (hξa : 2 ≤ ξ) (hξb : ξ ≤ 4) :
    |aux_dyadicTransitionMultiplierSecondDeriv 0 1 2 (-1 / 2 : ℝ) ξ| ≤ 1024 := by
  have hfreq : (1 / 4 : ℝ) ≤ |ξ| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hT : |aux_dyadicTransition 0 1 2 (-1 / 2 : ℝ) ξ| ≤ 1 := by
    rw [← aux_annularCutoff_eq_posOuter_transition hξa hξb]
    exact aux_annularCutoff_norm_le_one ξ
  refine aux_dyadicTransitionMultiplierSecondDeriv_abs_le_1024 hfreq hT ?_ ?_
  · exact aux_dyadicTransitionDeriv_abs_le_24 (by norm_num) (by norm_num)
  · apply aux_dyadicTransitionSecondDeriv_abs_le_96 (by norm_num) (by norm_num)
    constructor <;> linarith

/-- Continuity of the reciprocal factor on a set avoiding zero, used in the
multiplier integration by parts for `dyadicKernelBounds`. -/
lemma aux_continuousOn_dyadicKernelReciprocal {s : Set ℝ}
    (hs : ∀ ξ ∈ s, ξ ≠ 0) : ContinuousOn aux_dyadicKernelReciprocal s := by
  intro ξ hξ
  exact (aux_dyadicKernelReciprocal_hasDerivAt ξ (hs ξ hξ)).continuousAt.continuousWithinAt

/-- Continuity of the first reciprocal derivative away from zero, used in
`dyadicKernelBounds`. -/
lemma aux_continuousOn_dyadicKernelReciprocalDeriv {s : Set ℝ}
    (hs : ∀ ξ ∈ s, ξ ≠ 0) : ContinuousOn aux_dyadicKernelReciprocalDeriv s := by
  intro ξ hξ
  exact (aux_dyadicKernelReciprocalDeriv_hasDerivAt ξ (hs ξ hξ)).continuousAt.continuousWithinAt

/-- Continuity of the second reciprocal derivative away from zero, used in
`dyadicKernelBounds`. -/
lemma aux_continuousOn_dyadicKernelReciprocalSecondDeriv {s : Set ℝ}
    (hs : ∀ ξ ∈ s, ξ ≠ 0) : ContinuousOn aux_dyadicKernelReciprocalSecondDeriv s := by
  intro ξ hξ
  unfold aux_dyadicKernelReciprocalSecondDeriv
  have hinv : ContinuousAt (fun t : ℝ ↦ t⁻¹) ξ :=
    continuousAt_id.inv₀ (hs ξ hξ)
  exact (continuousAt_const.mul (hinv.pow 4)).continuousWithinAt

/-- Continuity of a reciprocal-weighted transition away from zero, used in
`dyadicKernelBounds`. -/
lemma aux_continuousOn_dyadicTransitionMultiplier {c e a b : ℝ} {s : Set ℝ}
    (hs : ∀ ξ ∈ s, ξ ≠ 0) : ContinuousOn (aux_dyadicTransitionMultiplier c e a b) s := by
  unfold aux_dyadicTransitionMultiplier
  exact (aux_continuous_dyadicTransition c e a b).continuousOn.mul
    (aux_continuousOn_dyadicKernelReciprocal hs)

/-- Continuity of the first derivative of a reciprocal-weighted transition,
used in `dyadicKernelBounds`. -/
lemma aux_continuousOn_dyadicTransitionMultiplierDeriv {c e a b : ℝ} {s : Set ℝ}
    (hs : ∀ ξ ∈ s, ξ ≠ 0) :
    ContinuousOn (aux_dyadicTransitionMultiplierDeriv c e a b) s := by
  unfold aux_dyadicTransitionMultiplierDeriv
  exact ((aux_continuous_dyadicTransitionDeriv e a b).continuousOn.mul
      (aux_continuousOn_dyadicKernelReciprocal hs)).add
    ((aux_continuous_dyadicTransition c e a b).continuousOn.mul
      (aux_continuousOn_dyadicKernelReciprocalDeriv hs))

/-- Continuity of the second derivative of a reciprocal-weighted transition,
used in `dyadicKernelBounds`. -/
lemma aux_continuousOn_dyadicTransitionMultiplierSecondDeriv {c e a b : ℝ} {s : Set ℝ}
    (hs : ∀ ξ ∈ s, ξ ≠ 0) :
    ContinuousOn (aux_dyadicTransitionMultiplierSecondDeriv c e a b) s := by
  unfold aux_dyadicTransitionMultiplierSecondDeriv
  exact (((aux_continuous_dyadicTransitionSecondDeriv e a b).continuousOn.mul
      (aux_continuousOn_dyadicKernelReciprocal hs)).add
    ((aux_continuous_dyadicTransitionDeriv e a b).continuousOn.mul
      (aux_continuousOn_dyadicKernelReciprocalDeriv hs))).add
    (((aux_continuous_dyadicTransitionDeriv e a b).continuousOn.mul
      (aux_continuousOn_dyadicKernelReciprocalDeriv hs)).add
    ((aux_continuous_dyadicTransition c e a b).continuousOn.mul
      (aux_continuousOn_dyadicKernelReciprocalSecondDeriv hs)))

/-- Two integrations by parts for a reciprocal-weighted transition.  Its
explicit endpoint terms are assembled in `dyadicKernelBounds`. -/
lemma aux_transitionMultiplier_double_ibp {l r x c e a b : ℝ} (hx : x ≠ 0)
    (hzero : ∀ t ∈ Set.uIcc l r, t ≠ 0)
    (harg : ∀ t ∈ Set.Ioo (min l r) (max l r),
      0 < a + b * t ∧ a + b * t < 1) :
    (∫ t in l..r, aux_dyadicFourierPhase x t *
        (aux_dyadicTransitionMultiplier c e a b t : ℂ)) =
      (aux_dyadicTransitionMultiplier c e a b r : ℂ) * aux_dyadicFourierPhasePrimitive x r -
        (aux_dyadicTransitionMultiplier c e a b l : ℂ) * aux_dyadicFourierPhasePrimitive x l -
        ((aux_dyadicTransitionMultiplierDeriv c e a b r : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x r -
          (aux_dyadicTransitionMultiplierDeriv c e a b l : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x l -
          ∫ t in l..r, (aux_dyadicTransitionMultiplierSecondDeriv c e a b t : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x t) := by
  have hcont : ContinuousOn (aux_dyadicTransitionMultiplier c e a b) (Set.uIcc l r) :=
    aux_continuousOn_dyadicTransitionMultiplier hzero
  have hcont' : ContinuousOn (aux_dyadicTransitionMultiplierDeriv c e a b) (Set.uIcc l r) :=
    aux_continuousOn_dyadicTransitionMultiplierDeriv hzero
  have hcont'' : ContinuousOn (aux_dyadicTransitionMultiplierSecondDeriv c e a b)
      (Set.uIcc l r) :=
    aux_continuousOn_dyadicTransitionMultiplierSecondDeriv hzero
  have hderiv : ∀ t ∈ Set.Ioo (min l r) (max l r),
      HasDerivAt (aux_dyadicTransitionMultiplier c e a b)
        (aux_dyadicTransitionMultiplierDeriv c e a b t) t := by
    intro t ht
    apply aux_dyadicTransitionMultiplier_hasDerivAt
    · exact (harg t ht).1
    · exact (harg t ht).2
    · apply hzero t
      exact ⟨ht.1.le, ht.2.le⟩
  have hderiv' : ∀ t ∈ Set.Ioo (min l r) (max l r),
      HasDerivAt (aux_dyadicTransitionMultiplierDeriv c e a b)
        (aux_dyadicTransitionMultiplierSecondDeriv c e a b t) t := by
    intro t ht
    apply aux_dyadicTransitionMultiplierDeriv_hasDerivAt
    · exact (harg t ht).1
    · exact (harg t ht).2
    · apply hzero t
      exact ⟨ht.1.le, ht.2.le⟩
  have hfirst := aux_interval_fourier_ibp (a := l) (b := r) (x := x) hx hcont hderiv
    hcont'.intervalIntegrable
  have hsecond := aux_interval_fourier_ibp_second (a := l) (b := r) (x := x) hx hcont' hderiv'
    hcont''.intervalIntegrable
  rw [hfirst]
  have hswap :
      (∫ t in l..r, (aux_dyadicTransitionMultiplierDeriv c e a b t : ℂ) *
        aux_dyadicFourierPhasePrimitive x t) =
      ∫ t in l..r, aux_dyadicFourierPhasePrimitive x t *
        (aux_dyadicTransitionMultiplierDeriv c e a b t : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hswap, hsecond]

/-- A generic second-primitive remainder estimate used to bound reciprocal
multiplier pieces in `dyadicKernelBounds`. -/
lemma aux_fourier_remainder_bound {l r x K : ℝ} {u : ℝ → ℝ} (hx : x ≠ 0)
    (hK0 : 0 ≤ K) (hK : ∀ t ∈ Set.uIoc l r, |u t| ≤ K) :
    ‖∫ t in l..r, (u t : ℂ) * aux_dyadicFourierPhaseSecondPrimitive x t‖ ≤
      (K / (16 * x ^ 2)) * |r - l| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |u t| * ‖aux_dyadicFourierPhaseSecondPrimitive x t‖ ≤
        K * (1 / (16 * x ^ 2)) := by
      exact mul_le_mul (hK t ht)
        (aux_norm_dyadicFourierPhaseSecondPrimitive_decay x t hx) (norm_nonneg _) hK0
    _ = K / (16 * x ^ 2) := by ring

/-- The reciprocal multiplier is pointwise dominated by the annular cutoff.
This auxiliary estimate is used to prove `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_dyadicKernelMultiplier_norm_le_annular (ξ : ℝ) :
    ‖aux_dyadicKernelMultiplier ξ‖ ≤ ‖(annularCutoff ξ : ℂ)‖ := by
  by_cases hsmall : |ξ| ≤ 1 / 4
  · have hq := aux_annularCutoff_eq_zero_of_outside (Or.inl hsmall)
    simp [aux_dyadicKernelMultiplier, hq]
  · have hfreq : (1 / 4 : ℝ) ≤ |ξ| := le_of_not_ge hsmall
    have hξ : ξ ≠ 0 := by
      intro hzero
      norm_num [hzero] at hfreq
    rw [aux_dyadicKernelMultiplier_eq_scalar ξ hξ,
      Complex.norm_real, Real.norm_eq_abs, abs_mul]
    calc
      |annularCutoff ξ| * |aux_dyadicKernelReciprocal ξ| ≤ |annularCutoff ξ| * 1 := by
        gcongr
        exact aux_dyadicKernelReciprocal_abs_le_one hfreq
      _ = ‖(annularCutoff ξ : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, mul_one]

/-- Measurability of the multiplier used in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_measurable_dyadicKernelMultiplier : Measurable aux_dyadicKernelMultiplier := by
  have hq : Measurable (fun ξ : ℝ ↦ (annularCutoff ξ : ℂ)) :=
    (Complex.continuous_ofReal.comp aux_continuous_annularCutoff).measurable
  have hden : Measurable (fun ξ : ℝ ↦
      ((((2 * Real.pi : ℝ) : ℂ) * Complex.I * (ξ : ℂ)) ^ 2)) := by
    fun_prop
  exact hq.div hden

/-- Integrability of the reciprocal annular multiplier, used in
`dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_dyadicKernelMultiplier_integrable : Integrable aux_dyadicKernelMultiplier volume := by
  apply aux_annularCutoff_integrable.norm.mono'
  · exact aux_measurable_dyadicKernelMultiplier.aestronglyMeasurable
  · filter_upwards with ξ
    exact aux_dyadicKernelMultiplier_norm_le_annular ξ

/-- Integrability of the oscillatory multiplier integrand used in
`dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_dyadicKernelMultiplier_phase_integrable (x : ℝ) :
    Integrable (fun ξ : ℝ ↦ aux_dyadicFourierPhase x ξ * aux_dyadicKernelMultiplier ξ)
      volume := by
  apply aux_dyadicKernelMultiplier_integrable.norm.mono'
  · exact ((aux_continuous_dyadicFourierPhase x).aestronglyMeasurable).mul
      aux_measurable_dyadicKernelMultiplier.aestronglyMeasurable
  · filter_upwards with ξ
    rw [norm_mul, aux_norm_dyadicFourierPhase]
    simp

/-- The reciprocal multiplier vanishes off the fixed annular interval.  This
is an auxiliary support fact for `dyadicKernelBounds` and
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_dyadicKernelMultiplier_eq_zero_of_not_mem (ξ : ℝ)
    (hξ : ξ ∉ Set.Icc (-4 : ℝ) 4) : aux_dyadicKernelMultiplier ξ = 0 := by
  unfold aux_dyadicKernelMultiplier
  rw [aux_annularCutoff_eq_zero_of_not_mem ξ hξ]
  simp

/-- Replaces the global multiplier Fourier integral with its compact annular
interval in the proof of `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_dyadicKernelMultiplier_phase_global_eq_interval (x : ℝ) :
    (∫ ξ : ℝ, aux_dyadicFourierPhase x ξ * aux_dyadicKernelMultiplier ξ) =
      ∫ ξ in (-4 : ℝ)..4, aux_dyadicFourierPhase x ξ * aux_dyadicKernelMultiplier ξ := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro ξ hξ
  rw [Function.mem_support] at hξ
  constructor
  · by_contra h
    have hle : ξ ≤ -4 := le_of_not_gt h
    have hzero : aux_dyadicKernelMultiplier ξ = 0 := by
      unfold aux_dyadicKernelMultiplier
      rw [aux_annularCutoff_eq_zero_of_outside (Or.inr (by
        rw [abs_of_nonpos (by linarith : ξ ≤ 0)]
        linarith))]
      simp
    apply hξ
    simp [hzero]
  · by_contra h
    have hgt : 4 < ξ := lt_of_not_ge h
    have hzero : aux_dyadicKernelMultiplier ξ = 0 := by
      unfold aux_dyadicKernelMultiplier
      rw [aux_annularCutoff_eq_zero_of_outside (Or.inr (by
        rw [abs_of_nonneg (by linarith : 0 ≤ ξ)]
        linarith))]
      simp
    apply hξ
    simp [hzero]

/-- Splits the compact multiplier Fourier integral into its four transition,
two plateau, and central zero intervals for `dyadicKernelBounds` and
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_dyadicKernelMultiplier_phase_seven_parts (x : ℝ) :
    (∫ ξ in (-4 : ℝ)..4, aux_dyadicFourierPhase x ξ * aux_dyadicKernelMultiplier ξ) =
      (∫ ξ in (-4 : ℝ)..(-2), aux_dyadicFourierPhase x ξ * aux_dyadicKernelMultiplier ξ) +
      (∫ ξ in (-2 : ℝ)..(-1 / 2),
        aux_dyadicFourierPhase x ξ * aux_dyadicKernelMultiplier ξ) +
      (∫ ξ in (-1 / 2 : ℝ)..(-1 / 4),
        aux_dyadicFourierPhase x ξ * aux_dyadicKernelMultiplier ξ) +
      (∫ ξ in (-1 / 4 : ℝ)..(1 / 4),
        aux_dyadicFourierPhase x ξ * aux_dyadicKernelMultiplier ξ) +
      (∫ ξ in (1 / 4 : ℝ)..(1 / 2),
        aux_dyadicFourierPhase x ξ * aux_dyadicKernelMultiplier ξ) +
      (∫ ξ in (1 / 2 : ℝ)..2, aux_dyadicFourierPhase x ξ * aux_dyadicKernelMultiplier ξ) +
      (∫ ξ in (2 : ℝ)..4, aux_dyadicFourierPhase x ξ * aux_dyadicKernelMultiplier ξ) := by
  let g : ℝ → ℂ := fun ξ ↦ aux_dyadicFourierPhase x ξ * aux_dyadicKernelMultiplier ξ
  have hg : Integrable g volume := aux_dyadicKernelMultiplier_phase_integrable x
  have hi (a b : ℝ) : IntervalIntegrable g volume a b := hg.intervalIntegrable
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hi (-4 : ℝ) (-2)) (hi (-2 : ℝ) (-1 / 2))
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hi (-4 : ℝ) (-1 / 2)) (hi (-1 / 2 : ℝ) (-1 / 4))
  have h3 := intervalIntegral.integral_add_adjacent_intervals
    (hi (-4 : ℝ) (-1 / 4)) (hi (-1 / 4 : ℝ) (1 / 4))
  have h4 := intervalIntegral.integral_add_adjacent_intervals
    (hi (-4 : ℝ) (1 / 4)) (hi (1 / 4 : ℝ) (1 / 2))
  have h5 := intervalIntegral.integral_add_adjacent_intervals
    (hi (-4 : ℝ) (1 / 2)) (hi (1 / 2 : ℝ) 2)
  have h6 := intervalIntegral.integral_add_adjacent_intervals
    (hi (-4 : ℝ) 2) (hi (2 : ℝ) 4)
  change (∫ ξ in (-4 : ℝ)..4, g ξ) = _
  rw [← h6, ← h5, ← h4, ← h3, ← h2, ← h1]

/-- Two integrations by parts for the reciprocal factor on an interval away
from zero, used in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_dyadicKernelReciprocal_double_ibp {l r x : ℝ} (hx : x ≠ 0)
    (hzero : ∀ t ∈ Set.uIcc l r, t ≠ 0) :
    (∫ t in l..r, aux_dyadicFourierPhase x t *
        (aux_dyadicKernelReciprocal t : ℂ)) =
      (aux_dyadicKernelReciprocal r : ℂ) * aux_dyadicFourierPhasePrimitive x r -
        (aux_dyadicKernelReciprocal l : ℂ) * aux_dyadicFourierPhasePrimitive x l -
        ((aux_dyadicKernelReciprocalDeriv r : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x r -
          (aux_dyadicKernelReciprocalDeriv l : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x l -
          ∫ t in l..r, (aux_dyadicKernelReciprocalSecondDeriv t : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x t) := by
  have hcont : ContinuousOn aux_dyadicKernelReciprocal (Set.uIcc l r) :=
    aux_continuousOn_dyadicKernelReciprocal hzero
  have hcont' : ContinuousOn aux_dyadicKernelReciprocalDeriv (Set.uIcc l r) :=
    aux_continuousOn_dyadicKernelReciprocalDeriv hzero
  have hcont'' : ContinuousOn aux_dyadicKernelReciprocalSecondDeriv (Set.uIcc l r) :=
    aux_continuousOn_dyadicKernelReciprocalSecondDeriv hzero
  have hderiv : ∀ t ∈ Set.Ioo (min l r) (max l r),
      HasDerivAt aux_dyadicKernelReciprocal (aux_dyadicKernelReciprocalDeriv t) t := by
    intro t ht
    simpa [aux_dyadicKernelReciprocalDeriv] using
      aux_dyadicKernelReciprocal_hasDerivAt t (hzero t ⟨ht.1.le, ht.2.le⟩)
  have hderiv' : ∀ t ∈ Set.Ioo (min l r) (max l r),
      HasDerivAt aux_dyadicKernelReciprocalDeriv
        (aux_dyadicKernelReciprocalSecondDeriv t) t := by
    intro t ht
    have ht0 : t ≠ 0 := hzero t ⟨ht.1.le, ht.2.le⟩
    change HasDerivAt (fun z : ℝ ↦ 2 * ((2 * Real.pi) ^ 2)⁻¹ * (z⁻¹) ^ 3)
      (-6 * ((2 * Real.pi) ^ 2)⁻¹ * (t⁻¹) ^ 4) t
    exact aux_dyadicKernelReciprocalDeriv_hasDerivAt t ht0
  have hfirst := aux_interval_fourier_ibp (a := l) (b := r) (x := x) hx hcont hderiv
    hcont'.intervalIntegrable
  have hsecond := aux_interval_fourier_ibp_second (a := l) (b := r) (x := x) hx hcont' hderiv'
    hcont''.intervalIntegrable
  rw [hfirst]
  have hswap :
      (∫ t in l..r, (aux_dyadicKernelReciprocalDeriv t : ℂ) *
        aux_dyadicFourierPhasePrimitive x t) =
      ∫ t in l..r, aux_dyadicFourierPhasePrimitive x t *
        (aux_dyadicKernelReciprocalDeriv t : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hswap, hsecond]

/-- The negative reciprocal plateau has the standard double-integration by
parts form used in `dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_dyadicKernelMultiplier_neg_plateau_ibp (x : ℝ) (hx : x ≠ 0) :
    (∫ t in (-2 : ℝ)..(-1 / 2), aux_dyadicFourierPhase x t *
        aux_dyadicKernelMultiplier t) =
      (aux_dyadicKernelMultiplier (-1 / 2)) * aux_dyadicFourierPhasePrimitive x (-1 / 2) -
        (aux_dyadicKernelMultiplier (-2)) * aux_dyadicFourierPhasePrimitive x (-2) -
        ((aux_dyadicKernelReciprocalDeriv (-1 / 2) : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x (-1 / 2) -
          (aux_dyadicKernelReciprocalDeriv (-2) : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x (-2) -
          ∫ t in (-2 : ℝ)..(-1 / 2), (aux_dyadicKernelReciprocalSecondDeriv t : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x t) := by
  have h := aux_dyadicKernelReciprocal_double_ibp (l := (-2 : ℝ)) (r := (-1 / 2 : ℝ))
    (x := x) hx (by
    intro t ht
    have ht' : -2 ≤ t ∧ t ≤ -1 / 2 := by
      rw [Set.uIcc_of_le (by norm_num : (-2 : ℝ) ≤ -1 / 2)] at ht
      exact ht
    linarith)
  rw [intervalIntegral.integral_congr (fun t ht ↦ by
    have ht' : -2 ≤ t ∧ t ≤ -1 / 2 := by
      rw [Set.uIcc_of_le (by norm_num : (-2 : ℝ) ≤ -1 / 2)] at ht
      exact ht
    rw [aux_dyadicKernelMultiplier_eq_negMiddle ht'.1 ht'.2])]
  rw [aux_dyadicKernelMultiplier_eq_negMiddle (by norm_num) (by norm_num),
    aux_dyadicKernelMultiplier_eq_negMiddle (by norm_num) (by norm_num)]
  exact h

/-- The positive reciprocal plateau has the standard double-integration by
parts form used in `dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_dyadicKernelMultiplier_pos_plateau_ibp (x : ℝ) (hx : x ≠ 0) :
    (∫ t in (1 / 2 : ℝ)..2, aux_dyadicFourierPhase x t *
        aux_dyadicKernelMultiplier t) =
      (aux_dyadicKernelMultiplier 2) * aux_dyadicFourierPhasePrimitive x 2 -
        (aux_dyadicKernelMultiplier (1 / 2)) * aux_dyadicFourierPhasePrimitive x (1 / 2) -
        ((aux_dyadicKernelReciprocalDeriv 2 : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x 2 -
          (aux_dyadicKernelReciprocalDeriv (1 / 2) : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x (1 / 2) -
          ∫ t in (1 / 2 : ℝ)..2, (aux_dyadicKernelReciprocalSecondDeriv t : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x t) := by
  have h := aux_dyadicKernelReciprocal_double_ibp (l := (1 / 2 : ℝ)) (r := (2 : ℝ))
    (x := x) hx (by
    intro t ht
    have ht' : 1 / 2 ≤ t ∧ t ≤ 2 := by
      rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at ht
      exact ht
    linarith)
  rw [intervalIntegral.integral_congr (fun t ht ↦ by
    have ht' : 1 / 2 ≤ t ∧ t ≤ 2 := by
      rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at ht
      exact ht
    rw [aux_dyadicKernelMultiplier_eq_posMiddle ht'.1 ht'.2])]
  rw [aux_dyadicKernelMultiplier_eq_posMiddle (by norm_num) (by norm_num),
    aux_dyadicKernelMultiplier_eq_posMiddle (by norm_num) (by norm_num)]
  exact h

/-- The central multiplier interval vanishes in the proof of
`dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_dyadicKernelMultiplier_middle_zero_integral (x : ℝ) :
    (∫ t in (-1 / 4 : ℝ)..(1 / 4), aux_dyadicFourierPhase x t *
        aux_dyadicKernelMultiplier t) = 0 := by
  rw [intervalIntegral.integral_congr (fun t ht ↦ by
    have ht' : -1 / 4 ≤ t ∧ t ≤ 1 / 4 := by
      rw [Set.uIcc_of_le (by norm_num : (-1 / 4 : ℝ) ≤ 1 / 4)] at ht
      exact ht
    rw [aux_dyadicKernelMultiplier_eq_zero_middle ht'.1 ht'.2])]
  simp

/-- The negative outer multiplier transition has the standard double-
integration-by-parts form used in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_dyadicKernelMultiplier_negOuter_ibp (x : ℝ) (hx : x ≠ 0) :
    (∫ t in (-4 : ℝ)..(-2), aux_dyadicFourierPhase x t *
        aux_dyadicKernelMultiplier t) =
      aux_dyadicKernelMultiplier (-2) * aux_dyadicFourierPhasePrimitive x (-2) -
        aux_dyadicKernelMultiplier (-4) * aux_dyadicFourierPhasePrimitive x (-4) -
        ((aux_dyadicKernelReciprocalDeriv (-2) : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x (-2) -
          0 - ∫ t in (-4 : ℝ)..(-2),
            (aux_dyadicTransitionMultiplierSecondDeriv 0 1 2 (1 / 2 : ℝ) t : ℂ) *
              aux_dyadicFourierPhaseSecondPrimitive x t) := by
  have h := aux_transitionMultiplier_double_ibp (l := (-4 : ℝ)) (r := (-2 : ℝ))
    (x := x) (c := 0) (e := 1) (a := 2) (b := (1 / 2 : ℝ)) hx (by
      intro t ht
      have ht' : -4 ≤ t ∧ t ≤ -2 := by
        rw [Set.uIcc_of_le (by norm_num : (-4 : ℝ) ≤ -2)] at ht
        exact ht
      linarith) (by
      intro t ht
      have ht' : -4 < t ∧ t < -2 := by
        norm_num [min_eq_left, max_eq_right] at ht
        exact ht
      constructor <;> linarith)
  rw [intervalIntegral.integral_congr (fun t ht ↦ by
    have ht' : -4 ≤ t ∧ t ≤ -2 := by
      rw [Set.uIcc_of_le (by norm_num : (-4 : ℝ) ≤ -2)] at ht
      exact ht
    rw [aux_dyadicKernelMultiplier_eq_negOuter_transition ht'.1 ht'.2])]
  rw [aux_dyadicKernelMultiplier_eq_negOuter_transition (by norm_num) (by norm_num),
    aux_dyadicKernelMultiplier_eq_negOuter_transition (by norm_num) (by norm_num)]
  convert h using 1;
    norm_num [aux_dyadicTransitionMultiplierDeriv, aux_dyadicTransition,
      aux_dyadicTransitionDeriv, aux_smoothStepDerivative, smoothStep]

/-- The negative inner multiplier transition has the standard double-
integration-by-parts form used in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_dyadicKernelMultiplier_negInner_ibp (x : ℝ) (hx : x ≠ 0) :
    (∫ t in (-1 / 2 : ℝ)..(-1 / 4), aux_dyadicFourierPhase x t *
        aux_dyadicKernelMultiplier t) =
      aux_dyadicKernelMultiplier (-1 / 4) * aux_dyadicFourierPhasePrimitive x (-1 / 4) -
        aux_dyadicKernelMultiplier (-1 / 2) * aux_dyadicFourierPhasePrimitive x (-1 / 2) -
        (0 - (aux_dyadicKernelReciprocalDeriv (-1 / 2) : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x (-1 / 2) -
          ∫ t in (-1 / 2 : ℝ)..(-1 / 4),
            (aux_dyadicTransitionMultiplierSecondDeriv 1 (-1) 2 (4 : ℝ) t : ℂ) *
              aux_dyadicFourierPhaseSecondPrimitive x t) := by
  have h := aux_transitionMultiplier_double_ibp (l := (-1 / 2 : ℝ)) (r := (-1 / 4 : ℝ))
    (x := x) (c := 1) (e := -1) (a := 2) (b := (4 : ℝ)) hx (by
      intro t ht
      have ht' : -1 / 2 ≤ t ∧ t ≤ -1 / 4 := by
        rw [Set.uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ -1 / 4)] at ht
        exact ht
      linarith) (by
      intro t ht
      have ht' : -1 / 2 < t ∧ t < -1 / 4 := by
        norm_num [min_eq_left, max_eq_right] at ht
        constructor <;> linarith [ht.1, ht.2]
      constructor <;> linarith)
  rw [intervalIntegral.integral_congr (fun t ht ↦ by
    have ht' : -1 / 2 ≤ t ∧ t ≤ -1 / 4 := by
      rw [Set.uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ -1 / 4)] at ht
      exact ht
    rw [aux_dyadicKernelMultiplier_eq_negInner_transition ht'.1 ht'.2])]
  rw [aux_dyadicKernelMultiplier_eq_negInner_transition (by norm_num) (by norm_num),
    aux_dyadicKernelMultiplier_eq_negInner_transition (by norm_num) (by norm_num)]
  convert h using 1;
    norm_num [aux_dyadicTransitionMultiplierDeriv, aux_dyadicTransition,
      aux_dyadicTransitionDeriv, aux_smoothStepDerivative, smoothStep]

/-- The positive inner multiplier transition has the standard double-
integration-by-parts form used in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_dyadicKernelMultiplier_posInner_ibp (x : ℝ) (hx : x ≠ 0) :
    (∫ t in (1 / 4 : ℝ)..(1 / 2), aux_dyadicFourierPhase x t *
        aux_dyadicKernelMultiplier t) =
      aux_dyadicKernelMultiplier (1 / 2) * aux_dyadicFourierPhasePrimitive x (1 / 2) -
        aux_dyadicKernelMultiplier (1 / 4) * aux_dyadicFourierPhasePrimitive x (1 / 4) -
        ((aux_dyadicKernelReciprocalDeriv (1 / 2) : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x (1 / 2) - 0 -
          ∫ t in (1 / 4 : ℝ)..(1 / 2),
            (aux_dyadicTransitionMultiplierSecondDeriv 1 (-1) 2 (-4 : ℝ) t : ℂ) *
              aux_dyadicFourierPhaseSecondPrimitive x t) := by
  have h := aux_transitionMultiplier_double_ibp (l := (1 / 4 : ℝ)) (r := (1 / 2 : ℝ))
    (x := x) (c := 1) (e := -1) (a := 2) (b := (-4 : ℝ)) hx (by
      intro t ht
      have ht' : 1 / 4 ≤ t ∧ t ≤ 1 / 2 := by
        rw [Set.uIcc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)] at ht
        exact ht
      linarith) (by
      intro t ht
      have ht' : 1 / 4 < t ∧ t < 1 / 2 := by
        norm_num [min_eq_left, max_eq_right] at ht
        exact ht
      constructor <;> linarith)
  rw [intervalIntegral.integral_congr (fun t ht ↦ by
    have ht' : 1 / 4 ≤ t ∧ t ≤ 1 / 2 := by
      rw [Set.uIcc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)] at ht
      exact ht
    rw [aux_dyadicKernelMultiplier_eq_posInner_transition ht'.1 ht'.2])]
  rw [aux_dyadicKernelMultiplier_eq_posInner_transition (by norm_num) (by norm_num),
    aux_dyadicKernelMultiplier_eq_posInner_transition (by norm_num) (by norm_num)]
  convert h using 1;
    norm_num [aux_dyadicTransitionMultiplierDeriv, aux_dyadicTransition,
      aux_dyadicTransitionDeriv, aux_smoothStepDerivative, smoothStep]

/-- The positive outer multiplier transition has the standard double-
integration-by-parts form used in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_dyadicKernelMultiplier_posOuter_ibp (x : ℝ) (hx : x ≠ 0) :
    (∫ t in (2 : ℝ)..4, aux_dyadicFourierPhase x t *
        aux_dyadicKernelMultiplier t) =
      aux_dyadicKernelMultiplier 4 * aux_dyadicFourierPhasePrimitive x 4 -
        aux_dyadicKernelMultiplier 2 * aux_dyadicFourierPhasePrimitive x 2 -
        (0 - (aux_dyadicKernelReciprocalDeriv 2 : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x 2 -
          ∫ t in (2 : ℝ)..4,
            (aux_dyadicTransitionMultiplierSecondDeriv 0 1 2 (-1 / 2 : ℝ) t : ℂ) *
              aux_dyadicFourierPhaseSecondPrimitive x t) := by
  have h := aux_transitionMultiplier_double_ibp (l := (2 : ℝ)) (r := (4 : ℝ))
    (x := x) (c := 0) (e := 1) (a := 2) (b := (-1 / 2 : ℝ)) hx (by
      intro t ht
      have ht' : 2 ≤ t ∧ t ≤ 4 := by
        rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at ht
        exact ht
      linarith) (by
      intro t ht
      have ht' : 2 < t ∧ t < 4 := by
        norm_num [min_eq_left, max_eq_right] at ht
        exact ht
      constructor <;> linarith)
  rw [intervalIntegral.integral_congr (fun t ht ↦ by
    have ht' : 2 ≤ t ∧ t ≤ 4 := by
      rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at ht
      exact ht
    rw [aux_dyadicKernelMultiplier_eq_posOuter_transition ht'.1 ht'.2])]
  rw [aux_dyadicKernelMultiplier_eq_posOuter_transition (by norm_num) (by norm_num),
    aux_dyadicKernelMultiplier_eq_posOuter_transition (by norm_num) (by norm_num)]
  convert h using 1;
    norm_num [aux_dyadicTransitionMultiplierDeriv, aux_dyadicTransition,
      aux_dyadicTransitionDeriv, aux_smoothStepDerivative, smoothStep]

/-- The multiplier Fourier integral is a sum of six second-derivative
remainders, used in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_dyadicKernelMultiplier_tail_representation (x : ℝ) (hx : x ≠ 0) :
    (∫ ξ : ℝ, aux_dyadicFourierPhase x ξ * aux_dyadicKernelMultiplier ξ) =
      (∫ t in (-4 : ℝ)..(-2),
        (aux_dyadicTransitionMultiplierSecondDeriv 0 1 2 (1 / 2 : ℝ) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      (∫ t in (-2 : ℝ)..(-1 / 2),
        (aux_dyadicKernelReciprocalSecondDeriv t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      (∫ t in (-1 / 2 : ℝ)..(-1 / 4),
        (aux_dyadicTransitionMultiplierSecondDeriv 1 (-1) 2 (4 : ℝ) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      (∫ t in (1 / 4 : ℝ)..(1 / 2),
        (aux_dyadicTransitionMultiplierSecondDeriv 1 (-1) 2 (-4 : ℝ) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      (∫ t in (1 / 2 : ℝ)..2,
        (aux_dyadicKernelReciprocalSecondDeriv t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      ∫ t in (2 : ℝ)..4,
        (aux_dyadicTransitionMultiplierSecondDeriv 0 1 2 (-1 / 2 : ℝ) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t := by
  rw [aux_dyadicKernelMultiplier_phase_global_eq_interval,
    aux_dyadicKernelMultiplier_phase_seven_parts]
  rw [aux_dyadicKernelMultiplier_negOuter_ibp x hx,
    aux_dyadicKernelMultiplier_neg_plateau_ibp x hx,
    aux_dyadicKernelMultiplier_negInner_ibp x hx,
    aux_dyadicKernelMultiplier_middle_zero_integral x,
    aux_dyadicKernelMultiplier_posInner_ibp x hx,
    aux_dyadicKernelMultiplier_pos_plateau_ibp x hx,
    aux_dyadicKernelMultiplier_posOuter_ibp x hx]
  have hnegOuter : aux_dyadicKernelMultiplier (-4 : ℝ) = 0 := by
    unfold aux_dyadicKernelMultiplier
    rw [aux_annularCutoff_eq_zero_of_outside (Or.inr (by norm_num))]
    simp
  have hposOuter : aux_dyadicKernelMultiplier (4 : ℝ) = 0 := by
    unfold aux_dyadicKernelMultiplier
    rw [aux_annularCutoff_eq_zero_of_outside (Or.inr (by norm_num))]
    simp
  have hnegInner : aux_dyadicKernelMultiplier (-1 / 4 : ℝ) = 0 :=
    aux_dyadicKernelMultiplier_eq_zero_middle (by norm_num) (by norm_num)
  have hposInner : aux_dyadicKernelMultiplier (1 / 4 : ℝ) = 0 :=
    aux_dyadicKernelMultiplier_eq_zero_middle (by norm_num) (by norm_num)
  rw [hnegOuter, hposOuter, hnegInner, hposInner]
  simp; ring

/-- A \(512/|x|^2\) tail estimate for the reciprocal multiplier Fourier
integral, used in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_dyadicKernelMultiplier_fourier_tail_norm (x : ℝ) (hx : x ≠ 0) :
    ‖∫ ξ : ℝ,
      aux_dyadicFourierPhase x ξ * aux_dyadicKernelMultiplier ξ‖ ≤ 512 / x ^ 2 := by
  rw [aux_dyadicKernelMultiplier_tail_representation x hx]
  have houterNeg := aux_fourier_remainder_bound
    (u := fun t : ℝ ↦ aux_dyadicTransitionMultiplierSecondDeriv 0 1 2 (1 / 2 : ℝ) t)
    (l := (-4 : ℝ)) (r := (-2 : ℝ)) (x := x) (K := 1024) hx (by norm_num) (by
      intro t ht
      have ht' : -4 < t ∧ t ≤ -2 := by
        rw [Set.uIoc_of_le (by norm_num : (-4 : ℝ) ≤ -2)] at ht
        exact ht
      exact aux_negOuter_multiplier_second_abs_le_1024 ht'.1.le ht'.2)
  have hplateauNeg := aux_fourier_remainder_bound
    (u := aux_dyadicKernelReciprocalSecondDeriv)
    (l := (-2 : ℝ)) (r := (-1 / 2 : ℝ)) (x := x) (K := 1024) hx (by norm_num) (by
      intro t ht
      have ht' : -2 < t ∧ t ≤ -1 / 2 := by
        rw [Set.uIoc_of_le (by norm_num : (-2 : ℝ) ≤ -1 / 2)] at ht
        exact ht
      have hfreq : (1 / 4 : ℝ) ≤ |t| := by
        rw [abs_of_neg (by linarith)]
        linarith
      exact (aux_dyadicKernelReciprocalSecondDeriv_abs_le_ninetysix hfreq).trans (by norm_num))
  have hinnerNeg := aux_fourier_remainder_bound
    (u := fun t : ℝ ↦ aux_dyadicTransitionMultiplierSecondDeriv 1 (-1) 2 (4 : ℝ) t)
    (l := (-1 / 2 : ℝ)) (r := (-1 / 4 : ℝ)) (x := x) (K := 1024) hx (by norm_num) (by
      intro t ht
      have ht' : -1 / 2 < t ∧ t ≤ -1 / 4 := by
        rw [Set.uIoc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ -1 / 4)] at ht
        exact ht
      exact aux_negInner_multiplier_second_abs_le_1024 ht'.1.le ht'.2)
  have hinnerPos := aux_fourier_remainder_bound
    (u := fun t : ℝ ↦ aux_dyadicTransitionMultiplierSecondDeriv 1 (-1) 2 (-4 : ℝ) t)
    (l := (1 / 4 : ℝ)) (r := (1 / 2 : ℝ)) (x := x) (K := 1024) hx (by norm_num) (by
      intro t ht
      have ht' : 1 / 4 < t ∧ t ≤ 1 / 2 := by
        rw [Set.uIoc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)] at ht
        exact ht
      exact aux_posInner_multiplier_second_abs_le_1024 ht'.1.le ht'.2)
  have hplateauPos := aux_fourier_remainder_bound
    (u := aux_dyadicKernelReciprocalSecondDeriv)
    (l := (1 / 2 : ℝ)) (r := (2 : ℝ)) (x := x) (K := 1024) hx (by norm_num) (by
      intro t ht
      have ht' : 1 / 2 < t ∧ t ≤ 2 := by
        rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at ht
        exact ht
      have hfreq : (1 / 4 : ℝ) ≤ |t| := by
        rw [abs_of_nonneg (by linarith)]
        linarith
      exact (aux_dyadicKernelReciprocalSecondDeriv_abs_le_ninetysix hfreq).trans (by norm_num))
  have houterPos := aux_fourier_remainder_bound
    (u := fun t : ℝ ↦ aux_dyadicTransitionMultiplierSecondDeriv 0 1 2 (-1 / 2 : ℝ) t)
    (l := (2 : ℝ)) (r := (4 : ℝ)) (x := x) (K := 1024) hx (by norm_num) (by
      intro t ht
      have ht' : 2 < t ∧ t ≤ 4 := by
        rw [Set.uIoc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at ht
        exact ht
      exact aux_posOuter_multiplier_second_abs_le_1024 ht'.1.le ht'.2)
  calc
    ‖(∫ t in (-4 : ℝ)..(-2),
        (aux_dyadicTransitionMultiplierSecondDeriv 0 1 2 (1 / 2 : ℝ) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      (∫ t in (-2 : ℝ)..(-1 / 2),
        (aux_dyadicKernelReciprocalSecondDeriv t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      (∫ t in (-1 / 2 : ℝ)..(-1 / 4),
        (aux_dyadicTransitionMultiplierSecondDeriv 1 (-1) 2 (4 : ℝ) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      (∫ t in (1 / 4 : ℝ)..(1 / 2),
        (aux_dyadicTransitionMultiplierSecondDeriv 1 (-1) 2 (-4 : ℝ) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      (∫ t in (1 / 2 : ℝ)..2,
        (aux_dyadicKernelReciprocalSecondDeriv t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      ∫ t in (2 : ℝ)..4,
        (aux_dyadicTransitionMultiplierSecondDeriv 0 1 2 (-1 / 2 : ℝ) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t‖ ≤
        ‖∫ t in (-4 : ℝ)..(-2),
          (aux_dyadicTransitionMultiplierSecondDeriv 0 1 2 (1 / 2 : ℝ) t : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x t‖ +
        ‖∫ t in (-2 : ℝ)..(-1 / 2),
          (aux_dyadicKernelReciprocalSecondDeriv t : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x t‖ +
        ‖∫ t in (-1 / 2 : ℝ)..(-1 / 4),
          (aux_dyadicTransitionMultiplierSecondDeriv 1 (-1) 2 (4 : ℝ) t : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x t‖ +
        ‖∫ t in (1 / 4 : ℝ)..(1 / 2),
          (aux_dyadicTransitionMultiplierSecondDeriv 1 (-1) 2 (-4 : ℝ) t : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x t‖ +
        ‖∫ t in (1 / 2 : ℝ)..2,
          (aux_dyadicKernelReciprocalSecondDeriv t : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x t‖ +
        ‖∫ t in (2 : ℝ)..4,
          (aux_dyadicTransitionMultiplierSecondDeriv 0 1 2 (-1 / 2 : ℝ) t : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x t‖ := by
      exact norm_add_le_of_le
        (norm_add_le_of_le
          (norm_add_le_of_le
            (norm_add_le_of_le (norm_add_le _ _) le_rfl) le_rfl) le_rfl) le_rfl
    _ ≤ (1024 / (16 * x ^ 2)) * |(-2 : ℝ) - (-4)| +
        (1024 / (16 * x ^ 2)) * |(-1 / 2 : ℝ) - (-2)| +
        (1024 / (16 * x ^ 2)) * |(-1 / 4 : ℝ) - (-1 / 2)| +
        (1024 / (16 * x ^ 2)) * |(1 / 2 : ℝ) - (1 / 4)| +
        (1024 / (16 * x ^ 2)) * |(2 : ℝ) - (1 / 2)| +
        (1024 / (16 * x ^ 2)) * |(4 : ℝ) - 2| := by
      gcongr
    _ ≤ 512 / x ^ 2 := by
      have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
      have hsum :
          (1024 / (16 * x ^ 2)) * |(-2 : ℝ) - (-4)| +
            (1024 / (16 * x ^ 2)) * |(-1 / 2 : ℝ) - (-2)| +
            (1024 / (16 * x ^ 2)) * |(-1 / 4 : ℝ) - (-1 / 2)| +
            (1024 / (16 * x ^ 2)) * |(1 / 2 : ℝ) - (1 / 4)| +
            (1024 / (16 * x ^ 2)) * |(2 : ℝ) - (1 / 2)| +
            (1024 / (16 * x ^ 2)) * |(4 : ℝ) - 2| = 480 / x ^ 2 := by
        rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ -2 - -4),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ -1 / 2 - -2),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ -1 / 4 - -1 / 2),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2 - 1 / 4),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 - 1 / 2),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4 - 2)]
        field_simp [hx2.ne']
        ring
      rw [hsum]
      apply (div_le_div_iff_of_pos_right hx2).2
      norm_num

/-- An \(L^1\) bound for the reciprocal annular multiplier, used in
`dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_dyadicKernelMultiplier_norm_integral_le_eight :
    (∫ ξ : ℝ, ‖aux_dyadicKernelMultiplier ξ‖) ≤ 8 := by
  calc
    (∫ ξ : ℝ, ‖aux_dyadicKernelMultiplier ξ‖) ≤
        ∫ ξ : ℝ, ‖(annularCutoff ξ : ℂ)‖ :=
      integral_mono aux_dyadicKernelMultiplier_integrable.norm aux_annularCutoff_integrable.norm
        (fun ξ ↦ aux_dyadicKernelMultiplier_norm_le_annular ξ)
    _ ≤ 8 := aux_annularCutoff_norm_integral_le_eight

/-- A uniform pointwise inverse-Fourier bound for the reciprocal multiplier,
used in `dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_dyadicKernelMultiplier_inverse_uniform (x : ℝ) :
    ‖inverseFourierTransform aux_dyadicKernelMultiplier x‖ ≤ 8 := by
  change
    ‖VectorFourier.fourierIntegral 𝐞 volume (-(innerₗ ℝ))
      aux_dyadicKernelMultiplier x‖ ≤ 8
  calc
    ‖VectorFourier.fourierIntegral 𝐞 volume (-(innerₗ ℝ))
        aux_dyadicKernelMultiplier x‖ ≤
        ∫ ξ : ℝ, ‖aux_dyadicKernelMultiplier ξ‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (-(innerₗ ℝ)) _ x
    _ ≤ 8 := aux_dyadicKernelMultiplier_norm_integral_le_eight

/-- Identifies the inverse Fourier transform of the multiplier with the
oscillatory integral used in `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_inverse_dyadicKernelMultiplier_eq_phase (x : ℝ) :
    inverseFourierTransform aux_dyadicKernelMultiplier x =
      ∫ ξ : ℝ, aux_dyadicFourierPhase x ξ * aux_dyadicKernelMultiplier ξ := by
  rw [inverseFourierTransform, Real.fourierInv_eq']
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  congr 3
  rw [Real.inner_apply]
  push_cast
  ring

/-- Transfers the oscillatory tail bound to the inverse Fourier transform in
`dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_dyadicKernelMultiplier_inverse_tail (x : ℝ) (hx : x ≠ 0) :
    ‖inverseFourierTransform aux_dyadicKernelMultiplier x‖ ≤ 512 / x ^ 2 := by
  rw [aux_inverse_dyadicKernelMultiplier_eq_phase]
  exact aux_dyadicKernelMultiplier_fourier_tail_norm x hx

/-- An integrable real majorant combining the local and tail bounds in
`dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
noncomputable def aux_dyadicKernelMultiplierEnvelope (x : ℝ) : ℝ := 1024 / (64 + x ^ 2)

/-- Nonnegativity of the reciprocal-multiplier majorant used in
`dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_dyadicKernelMultiplierEnvelope_nonneg (x : ℝ) :
    0 ≤ aux_dyadicKernelMultiplierEnvelope x := by
  unfold aux_dyadicKernelMultiplierEnvelope
  positivity

/-- Expresses the reciprocal-multiplier majorant as a scaled Cauchy kernel
for `dyadicKernelBounds` and \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_dyadicKernelMultiplierEnvelope_eq_scaled_cauchy :
    aux_dyadicKernelMultiplierEnvelope =
      fun x : ℝ ↦ 16 * (1 + ((1 / 8 : ℝ) * x) ^ 2)⁻¹ := by
  ext x
  unfold aux_dyadicKernelMultiplierEnvelope
  field_simp
  ring

/-- Integrability of the reciprocal-multiplier majorant used in
`dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_dyadicKernelMultiplierEnvelope_integrable :
    Integrable aux_dyadicKernelMultiplierEnvelope volume := by
  rw [aux_dyadicKernelMultiplierEnvelope_eq_scaled_cauchy]
  exact (integrable_inv_one_add_mul_sq (by norm_num : (1 / 8 : ℝ) ≠ 0)).const_mul 16

/-- Computes the integral of the reciprocal-multiplier majorant for
`dyadicKernelBounds` and \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_dyadicKernelMultiplierEnvelope_integral :
    ∫ x : ℝ, aux_dyadicKernelMultiplierEnvelope x = 128 * Real.pi := by
  rw [aux_dyadicKernelMultiplierEnvelope_eq_scaled_cauchy,
    MeasureTheory.integral_const_mul, integral_univ_inv_one_add_mul_sq]
  field_simp
  ring

/-- Computes the \(L^1\) norm of the reciprocal-multiplier majorant used in
`dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_eLpNorm_dyadicKernelMultiplierEnvelope :
    eLpNorm aux_dyadicKernelMultiplierEnvelope (1 : ℝ≥0∞) volume =
      ENNReal.ofReal (128 * Real.pi) := by
  rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
  have henorm : (fun x : ℝ ↦ ‖aux_dyadicKernelMultiplierEnvelope x‖ₑ) =
      fun x ↦ ENNReal.ofReal (aux_dyadicKernelMultiplierEnvelope x) := by
    ext x
    rw [← ofReal_norm,
      Real.norm_of_nonneg (aux_dyadicKernelMultiplierEnvelope_nonneg x)]
  rw [henorm, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    aux_dyadicKernelMultiplierEnvelope_integrable
    (Filter.Eventually.of_forall aux_dyadicKernelMultiplierEnvelope_nonneg),
    aux_dyadicKernelMultiplierEnvelope_integral]

/-- The reciprocal-multiplier majorant has \(L^1\) norm at most \(1024\),
for `dyadicKernelBounds` and \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_eLpNorm_dyadicKernelMultiplierEnvelope_le_1024 :
    eLpNorm aux_dyadicKernelMultiplierEnvelope (1 : ℝ≥0∞) volume ≤ 1024 := by
  rw [aux_eLpNorm_dyadicKernelMultiplierEnvelope]
  rw [← ENNReal.ofReal_ofNat 1024]
  apply ENNReal.ofReal_le_ofReal
  calc
    128 * Real.pi ≤ 128 * 4 := by gcongr; exact Real.pi_le_four
    _ ≤ 1024 := by norm_num

/-- The uniform multiplier bound is dominated by the Cauchy majorant near the
origin in `dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_small_le_dyadicKernelMultiplierEnvelope {x : ℝ} (hx : |x| ≤ 8) :
    8 ≤ aux_dyadicKernelMultiplierEnvelope x := by
  have hx2 : x ^ 2 ≤ 64 := by
    rw [← sq_abs x]
    have hnonneg : 0 ≤ (8 - |x|) * (8 + |x|) :=
      mul_nonneg (sub_nonneg.mpr hx) (by positivity)
    nlinarith
  unfold aux_dyadicKernelMultiplierEnvelope
  apply (le_div_iff₀ (by positivity : 0 < 64 + x ^ 2)).2
  nlinarith

/-- The Fourier tail bound is dominated by the Cauchy majorant away from the
origin in `dyadicKernelBounds` for \(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_tail_le_dyadicKernelMultiplierEnvelope {x : ℝ} (hx : 8 ≤ |x|) :
    512 / x ^ 2 ≤ aux_dyadicKernelMultiplierEnvelope x := by
  have hx2 : 64 ≤ x ^ 2 := by
    rw [← sq_abs x]
    have hnonneg : 0 ≤ (|x| - 8) * (|x| + 8) :=
      mul_nonneg (sub_nonneg.mpr hx) (by positivity)
    nlinarith
  have hx20 : 0 < x ^ 2 := by nlinarith
  unfold aux_dyadicKernelMultiplierEnvelope
  apply (div_le_div_iff₀ hx20 (by positivity : 0 < 64 + x ^ 2)).2
  nlinarith

/-- Combines uniform and reciprocal-square tails into the explicit \(L^1\)
bound needed by `dyadicKernelBounds` for
\(\label{lem:dyadic-kernel-bounds}\). -/
lemma aux_eLpNorm_le_1024_of_uniform_and_tail {F : ℝ → ℂ}
    (huniform : ∀ x : ℝ, ‖F x‖ ≤ 8)
    (htail : ∀ x : ℝ, x ≠ 0 → ‖F x‖ ≤ 512 / x ^ 2) :
    eLpNorm F (1 : ℝ≥0∞) volume ≤ 1024 := by
  have hpoint : ∀ x : ℝ, ‖F x‖ ≤ aux_dyadicKernelMultiplierEnvelope x := by
    intro x
    by_cases hx : |x| ≤ 8
    · exact (huniform x).trans (aux_small_le_dyadicKernelMultiplierEnvelope hx)
    · have hxlarge : 8 ≤ |x| := le_of_lt (lt_of_not_ge hx)
      have hxne : x ≠ 0 := by
        intro hzero
        rw [hzero] at hxlarge
        norm_num at hxlarge
      exact (htail x hxne).trans (aux_tail_le_dyadicKernelMultiplierEnvelope hxlarge)
  calc
    eLpNorm F (1 : ℝ≥0∞) volume ≤
        eLpNorm aux_dyadicKernelMultiplierEnvelope (1 : ℝ≥0∞) volume :=
      eLpNorm_mono_real hpoint
    _ ≤ 1024 := aux_eLpNorm_dyadicKernelMultiplierEnvelope_le_1024

/--
The kernel bounds in \(\label{lem:dyadic-kernel-bounds}\):
\[
\lVert\check q\rVert_1\leq2^6,\qquad
\left\lVert\mathcal F^{-1}\!\left(\frac{q}{(2\pi i\,\cdot)^2}\right)
\right\rVert_1\leq C_{\mathrm{dyadic\text{-}kernel\text{-}bounds},q}.
\]
-/
theorem dyadicKernelBounds :
    eLpNorm (inverseFourierTransform fun ξ ↦ (annularCutoff ξ : ℂ))
        (1 : ℝ≥0∞) volume ≤ 2 ^ 6 ∧
      eLpNorm (inverseFourierTransform aux_dyadicKernelMultiplier)
        (1 : ℝ≥0∞) volume ≤ ENNReal.ofReal C_dyadicKernelBounds := by
  constructor
  · exact aux_eLpNorm_le_of_local_tail aux_annular_inverseFourier_uniform_bound
      aux_annular_inverseFourier_tail_bound
  · convert aux_eLpNorm_le_1024_of_uniform_and_tail
      aux_dyadicKernelMultiplier_inverse_uniform
      aux_dyadicKernelMultiplier_inverse_tail using 1;
      norm_num [C_dyadicKernelBounds]

/-- Continuity of the annular inverse-Fourier kernel.  This provides a
canonical representative for the convolution arguments in
`dyadicReconstructionAndMultiplierBounds` for
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_annularInverseFourierKernel_continuous :
    Continuous (inverseFourierTransform fun ξ : ℝ ↦ (annularCutoff ξ : ℂ)) := by
  let hmem : MemLp (fun ξ : ℝ ↦ (annularCutoff ξ : ℂ)) 1 volume :=
    memLp_one_iff_integrable.mpr aux_annularCutoff_integrable
  unfold inverseFourierTransform
  rw [← Real.Lp.fourierTransformInv_toLp hmem]
  exact (Real.Lp.fourierTransformInv hmem.toLp).continuous

/-- The annular inverse-Fourier kernel is in \(L^1\).  This auxiliary
integrability fact is used by `dyadicReconstructionAndMultiplierBounds` for
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_annularInverseFourierKernel_memLp_one :
    MemLp (inverseFourierTransform fun ξ : ℝ ↦ (annularCutoff ξ : ℂ)) 1 volume := by
  refine ⟨aux_annularInverseFourierKernel_continuous.aestronglyMeasurable, ?_⟩
  exact (aux_eLpNorm_le_of_local_tail aux_annular_inverseFourier_uniform_bound
    aux_annular_inverseFourier_tail_bound).trans_lt (by finiteness)

/-- The annular inverse-Fourier kernel is in \(L^2\).  Together with its
\(L^1\) bound, this supplies the raw convolution hypotheses in
`dyadicReconstructionAndMultiplierBounds` for
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_annularInverseFourierKernel_memLp_two :
    MemLp (inverseFourierTransform fun ξ : ℝ ↦ (annularCutoff ξ : ℂ)) 2 volume := by
  let K : ℝ → ℂ := inverseFourierTransform fun ξ : ℝ ↦ (annularCutoff ξ : ℂ)
  have hKmeas : AEStronglyMeasurable K volume :=
    aux_annularInverseFourierKernel_continuous.aestronglyMeasurable
  have hKint : Integrable K volume :=
    memLp_one_iff_integrable.mp aux_annularInverseFourierKernel_memLp_one
  have hmajor : Integrable (fun x : ℝ ↦ 8 * ‖K x‖) volume :=
    hKint.norm.const_mul 8
  have hsq : Integrable (fun x : ℝ ↦ ‖K x‖ ^ 2) volume :=
    hmajor.mono' (hKmeas.norm.pow 2) (Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖K x‖)]
      have hbound : ‖K x‖ ≤ 8 := aux_annular_inverseFourier_uniform_bound x
      nlinarith [norm_nonneg (K x)])
  apply (memLp_norm_iff hKmeas).mp
  exact (memLp_two_iff_integrable_sq hKmeas.norm).mpr hsq

/-- Every dyadic rescaling of the annular inverse-Fourier kernel is in
\(L^1\).  This is an auxiliary kernel fact for
`dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_scaledAnnularInverseFourierKernel_memLp_one (k : ℕ) :
    MemLp (aux_scaledInverseFourierKernel (fun ξ ↦ (annularCutoff ξ : ℂ)) k) 1 volume := by
  let a : ℝ := (2 : ℝ) ^ k
  let K : ℝ → ℂ := inverseFourierTransform fun ξ : ℝ ↦ (annularCutoff ξ : ℂ)
  have ha : a ≠ 0 := by
    dsimp [a]
    positivity
  have hK : Integrable K volume :=
    memLp_one_iff_integrable.mp aux_annularInverseFourierKernel_memLp_one
  have hcomp : Integrable (fun x : ℝ ↦ K (a * x)) volume :=
    hK.comp_mul_left' ha
  have hEq : aux_scaledInverseFourierKernel (fun ξ ↦ (annularCutoff ξ : ℂ)) k =
      fun x ↦ (a : ℂ) * K (a * x) := by
    ext x
    simp [aux_scaledInverseFourierKernel, a, K]
  rw [hEq]
  exact memLp_one_iff_integrable.mpr (hcomp.const_mul (a : ℂ))

/-- Dyadic spatial scaling preserves the `L¹` norm of the annular kernel.
This is the uniform kernel estimate used for the `Q_k` multiplier bound in
`dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_eLpNorm_scaledAnnularInverseFourierKernel_one (k : ℕ) :
    eLpNorm (aux_scaledInverseFourierKernel
      (fun ξ ↦ (annularCutoff ξ : ℂ)) k) (1 : ℝ≥0∞) volume =
      eLpNorm (inverseFourierTransform fun ξ ↦ (annularCutoff ξ : ℂ))
        (1 : ℝ≥0∞) volume := by
  let a : ℝ := (2 : ℝ) ^ k
  let K : ℝ → ℂ := inverseFourierTransform fun ξ ↦ (annularCutoff ξ : ℂ)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hK : Integrable K volume :=
    memLp_one_iff_integrable.mp aux_annularInverseFourierKernel_memLp_one
  have hscale : Integrable (fun x : ℝ ↦ a * ‖K (a * x)‖) volume := by
    have hcomp : Integrable (fun x : ℝ ↦ ‖K (a * x)‖) volume :=
      hK.norm.comp_mul_left' ha.ne'
    exact hcomp.const_mul a
  have hscale_nonneg : 0 ≤ᵐ[volume] fun x : ℝ ↦ a * ‖K (a * x)‖ :=
    Filter.Eventually.of_forall fun x ↦ mul_nonneg (le_of_lt ha) (norm_nonneg _)
  have hK_nonneg : 0 ≤ᵐ[volume] fun x : ℝ ↦ ‖K x‖ :=
    Filter.Eventually.of_forall fun x ↦ norm_nonneg _
  have hintegral : (∫ x : ℝ, a * ‖K (a * x)‖) = ∫ x : ℝ, ‖K x‖ := by
    calc
      (∫ x : ℝ, a * ‖K (a * x)‖) =
          a * ∫ x : ℝ, ‖K (a * x)‖ :=
        integral_const_mul a _
      _ = a * (|a⁻¹| • ∫ x : ℝ, ‖K x‖) := by
        congr 1
        exact Measure.integral_comp_mul_left (fun x : ℝ ↦ ‖K x‖) a
      _ = ∫ x : ℝ, ‖K x‖ := by
        rw [smul_eq_mul, abs_of_pos (inv_pos.mpr ha)]
        field_simp
  have hEq : aux_scaledInverseFourierKernel
      (fun ξ ↦ (annularCutoff ξ : ℂ)) k =
      fun x ↦ (a : ℂ) * K (a * x) := by
    ext x
    simp [aux_scaledInverseFourierKernel, a, K]
  rw [hEq, eLpNorm_one_eq_lintegral_enorm,
    show (fun x : ℝ ↦ ‖(a : ℂ) * K (a * x)‖ₑ) =
      fun x ↦ ENNReal.ofReal (a * ‖K (a * x)‖) by
        funext x
        rw [← ofReal_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos ha],
    ← ofReal_integral_eq_lintegral_ofReal hscale hscale_nonneg,
    hintegral]
  change ENNReal.ofReal (∫ x : ℝ, ‖K x‖) = eLpNorm K 1 volume
  rw [eLpNorm_one_eq_lintegral_enorm]
  calc
    ENNReal.ofReal (∫ x : ℝ, ‖K x‖) =
        ∫⁻ x : ℝ, ENNReal.ofReal ‖K x‖ :=
      ofReal_integral_eq_lintegral_ofReal hK.norm hK_nonneg
    _ = ∫⁻ x : ℝ, ‖K x‖ₑ := by
      apply lintegral_congr
      intro x
      exact ofReal_norm (K x)

/-- The scaled annular kernel retains the explicit `L¹` bound from
`dyadicKernelBounds`; this supplies the constant in
`dyadicReconstructionAndMultiplierBounds`. -/
lemma aux_eLpNorm_scaledAnnularInverseFourierKernel_one_le (k : ℕ) :
    eLpNorm (aux_scaledInverseFourierKernel
      (fun ξ ↦ (annularCutoff ξ : ℂ)) k) (1 : ℝ≥0∞) volume ≤ 2 ^ 6 := by
  rw [aux_eLpNorm_scaledAnnularInverseFourierKernel_one]
  exact dyadicKernelBounds.1

/-- Every dyadic rescaling of the annular inverse-Fourier kernel is in
\(L^2\).  This auxiliary fact makes the raw `Q` and `P` convolutions
pointwise-defined in `dyadicReconstructionAndMultiplierBounds` for
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_scaledAnnularInverseFourierKernel_memLp_two (k : ℕ) :
    MemLp (aux_scaledInverseFourierKernel (fun ξ ↦ (annularCutoff ξ : ℂ)) k) 2 volume := by
  let a : ℝ := (2 : ℝ) ^ k
  let K : ℝ → ℂ := inverseFourierTransform fun ξ : ℝ ↦ (annularCutoff ξ : ℂ)
  have ha : a ≠ 0 := by
    dsimp [a]
    positivity
  have hKmeas : AEStronglyMeasurable K volume :=
    aux_annularInverseFourierKernel_continuous.aestronglyMeasurable
  have hKsq : Integrable (fun x : ℝ ↦ ‖K x‖ ^ 2) volume := by
    have hKtwo := aux_annularInverseFourierKernel_memLp_two
    have hKnorm : MemLp (fun x : ℝ ↦ ‖K x‖) 2 volume :=
      (memLp_norm_iff hKmeas).mpr hKtwo
    exact (memLp_two_iff_integrable_sq hKmeas.norm).mp hKnorm
  have hcomp : Integrable (fun x : ℝ ↦ ‖K (a * x)‖ ^ 2) volume :=
    hKsq.comp_mul_left' ha
  have hmeas : AEStronglyMeasurable
      (aux_scaledInverseFourierKernel (fun ξ ↦ (annularCutoff ξ : ℂ)) k) volume := by
    have hcont : Continuous (fun x : ℝ ↦ K (a * x)) :=
      aux_annularInverseFourierKernel_continuous.comp (continuous_const.mul continuous_id)
    have hmeas' : AEStronglyMeasurable (fun x : ℝ ↦ (a : ℂ) * K (a * x)) volume :=
      hcont.aestronglyMeasurable.const_mul (a : ℂ)
    unfold aux_scaledInverseFourierKernel
    simpa [a, K] using hmeas'
  apply (memLp_norm_iff hmeas).mp
  rw [memLp_two_iff_integrable_sq]
  · have hsquares :
        (fun x : ℝ ↦ ‖aux_scaledInverseFourierKernel
          (fun ξ ↦ (annularCutoff ξ : ℂ)) k x‖ ^ 2) =
          fun x ↦ a ^ 2 * ‖K (a * x)‖ ^ 2 := by
      funext x
      unfold aux_scaledInverseFourierKernel
      dsimp only [a, K]
      rw [norm_mul, norm_pow, Complex.norm_real]
      norm_num
      ring
    rw [hsquares]
    exact hcomp.const_mul (a ^ 2)
  · exact hmeas.norm

/-- Integrability of the Fourier transform of the annular physical-space
kernel.  This is an auxiliary Fourier-inversion input for
`dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_fourier_annularInverseFourierKernel_integrable :
    Integrable (fun ξ : ℝ ↦ 𝓕 (fun t : ℝ ↦ (annularCutoff t : ℂ)) ξ) volume := by
  have hcheck : Integrable
      (inverseFourierTransform fun t : ℝ ↦ (annularCutoff t : ℂ)) volume :=
    memLp_one_iff_integrable.mp aux_annularInverseFourierKernel_memLp_one
  have hneg : Integrable
      ((inverseFourierTransform fun t : ℝ ↦ (annularCutoff t : ℂ)) ∘
        fun x : ℝ ↦ -x) volume :=
    ((Measure.measurePreserving_neg volume).integrable_comp hcheck.1).mpr hcheck
  convert hneg using 1
  ext x
  simpa [inverseFourierTransform] using
    (Real.fourierInv_eq_fourier_neg (fun t : ℝ ↦ (annularCutoff t : ℂ)) (-x)).symm

/-- Fourier inversion identifies the annular physical-space kernel with its
annular multiplier.  This is an auxiliary identity for
`dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_fourier_annularInverseFourierKernel_eq (ξ : ℝ) :
    𝓕 (inverseFourierTransform fun t : ℝ ↦ (annularCutoff t : ℂ)) ξ =
      (annularCutoff ξ : ℂ) := by
  have h := Continuous.fourier_fourierInv_eq
    (Complex.continuous_ofReal.comp aux_continuous_annularCutoff)
    aux_annularCutoff_integrable aux_fourier_annularInverseFourierKernel_integrable
  exact congrFun h ξ

/-- For an integrable input, raw convolution with the annular kernel has
the expected Fourier multiplier.  This supplies the dense-class calculation
used by `dyadicReconstructionAndMultiplierBounds` for
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_raw_annularConvolution_fourier_of_integrable
    {f : ℝ → ℂ} (hf : Integrable f volume) (ξ : ℝ) :
    𝓕 (aux_convolution
      (inverseFourierTransform fun t : ℝ ↦ (annularCutoff t : ℂ)) f) ξ =
      (annularCutoff ξ : ℂ) * 𝓕 f ξ := by
  rw [aux_convolution_eq_measureTheory_convolution]
  rw [Real.fourier_mul_convolution_eq
    (memLp_one_iff_integrable.mp aux_annularInverseFourierKernel_memLp_one) hf]
  rw [aux_fourier_annularInverseFourierKernel_eq]

/-- The inverse Fourier transform is self-adjoint against a Schwartz test
function and an integrable function.  This Fubini identity supplies the
`L²` Fourier bridge used in `dyadicReconstructionAndMultiplierBounds` for
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_integral_mul_inverseFourier (g : ℝ → ℂ) (hg : Integrable g volume)
    (φ : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ, φ x * (𝓕⁻ g) x) = ∫ ξ : ℝ, (𝓕⁻ φ) ξ * g ξ := by
  have hginv (x : ℝ) : (𝓕⁻ g) x = ∫ v : ℝ, 𝐞 (inner ℝ v x) • g v :=
    Real.fourierInv_eq g x
  have hprod : Integrable (fun z : ℝ × ℝ ↦
      φ z.1 * (𝐞 (inner ℝ z.2 z.1) • g z.2)) (volume.prod volume) := by
    have hbase : Integrable (fun z : ℝ × ℝ ↦ φ z.1 * g z.2)
        (volume.prod volume) :=
      Integrable.mul_prod (μ := volume) (ν := volume) φ.integrable hg
    refine hbase.norm.mono' ?_ (Filter.Eventually.of_forall fun z ↦ ?_)
    · have hphase : Continuous (fun z : ℝ × ℝ ↦ 𝐞 (inner ℝ z.2 z.1)) :=
        Real.continuous_fourierChar.comp (continuous_snd.inner continuous_fst)
      exact (φ.continuous.aestronglyMeasurable.comp_measurable measurable_fst).mul
        (hphase.aestronglyMeasurable.smul
          (hg.aestronglyMeasurable.comp_quasiMeasurePreserving
            Measure.quasiMeasurePreserving_snd))
    · simp only [norm_mul, Circle.norm_smul]
      exact le_rfl
  calc
    (∫ x : ℝ, φ x * (𝓕⁻ g) x) =
        ∫ x : ℝ, ∫ v : ℝ, φ x * (𝐞 (inner ℝ v x) • g v) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [hginv, integral_const_mul]
    _ = ∫ v : ℝ, ∫ x : ℝ, φ x * (𝐞 (inner ℝ v x) • g v) :=
      integral_integral_swap hprod
    _ = ∫ v : ℝ, (𝓕⁻ (φ : ℝ → ℂ)) v * g v := by
      apply integral_congr_ae
      filter_upwards with v
      rw [Real.fourierInv_eq]
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with x
      rw [real_inner_comm]
      simp only [Circle.smul_def]
      ring
    _ = ∫ ξ : ℝ, (𝓕⁻ φ) ξ * g ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [congrFun (SchwartzMap.fourierInv_coe φ) ξ]

/-- Embeds a raw inverse Fourier transform into tempered distributions.
This auxiliary compatibility statement is used to transfer a pointwise
Fourier-inversion calculation to the `aux_l2Fourier` representative in
`dyadicReconstructionAndMultiplierBounds`. -/
lemma aux_toTemperedDistribution_inverseFourier_eq
    (g h : ℝ → ℂ) (hg1 : Integrable g volume) (hg2 : MemLp g 2 volume)
    (hh2 : MemLp h 2 volume) (heq : h = 𝓕⁻ g) :
    (hh2.toLp h : 𝓢'(ℝ, ℂ)) = 𝓕⁻ (hg2.toLp g : 𝓢'(ℝ, ℂ)) := by
  ext φ
  rw [Lp.toTemperedDistribution_apply, TemperedDistribution.fourierInv_apply,
    Lp.toTemperedDistribution_apply]
  calc
    (∫ x : ℝ, φ x • (hh2.toLp h : ℝ → ℂ) x) = ∫ x : ℝ, φ x * h x := by
      apply integral_congr_ae
      filter_upwards [hh2.coeFn_toLp] with x hx
      simp [hx]
    _ = ∫ ξ : ℝ, ((𝓕⁻ φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ * g ξ := by
      rw [heq]
      exact aux_integral_mul_inverseFourier g hg1 φ
    _ = ∫ ξ : ℝ, ((𝓕⁻ φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ •
        (hg2.toLp g : ℝ → ℂ) ξ := by
      apply integral_congr_ae
      filter_upwards [hg2.coeFn_toLp] with ξ hξ
      simp [hξ]

/-- Plancherel agrees with a raw inverse-Fourier computation whenever both
the multiplier and its inverse transform are square-integrable.  This is a
reusable `L²` bridge for `dyadicReconstructionAndMultiplierBounds`. -/
lemma aux_l2Fourier_inverseFourier_eq
    (g h : ℝ → ℂ) (hg1 : Integrable g volume) (hg2 : MemLp g 2 volume)
    (hh2 : MemLp h 2 volume) (heq : h = 𝓕⁻ g) :
    Lp.fourierTransformₗᵢ ℝ ℂ (hh2.toLp h) = hg2.toLp g := by
  apply (LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume) (p := (2 : ℝ≥0∞))))
  calc
    Lp.toTemperedDistribution (Lp.fourierTransformₗᵢ ℝ ℂ (hh2.toLp h)) =
        𝓕 (Lp.toTemperedDistribution (hh2.toLp h)) :=
      (Lp.fourier_toTemperedDistribution_eq (hh2.toLp h)).symm
    _ = 𝓕 (𝓕⁻ (Lp.toTemperedDistribution (hg2.toLp g))) := by
      rw [aux_toTemperedDistribution_inverseFourier_eq g h hg1 hg2 hh2 heq]
    _ = Lp.toTemperedDistribution (hg2.toLp g) :=
      FourierTransform.fourier_fourierInv_eq _

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_continuous_dyadicCutoff : Continuous dyadicCutoff := by
  unfold dyadicCutoff
  exact aux_continuous_lowFrequencyCutoff.sub
    (aux_continuous_lowFrequencyCutoff.comp (continuous_const.mul continuous_id))

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_dyadicCutoff_integrable :
    Integrable (fun ξ : ℝ ↦ (dyadicCutoff ξ : ℂ)) volume := by
  have hsupport : HasCompactSupport (fun ξ : ℝ ↦ (dyadicCutoff ξ : ℂ)) := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-2 : ℝ) 2))
    intro ξ hξ
    have hout : 2 ≤ |ξ| := by
      by_cases hleft : ξ < -2
      · rw [abs_of_neg (by linarith)]
        linarith
      · have hright : 2 < ξ := by
          by_contra hright
          apply hξ
          constructor <;> linarith
        rw [abs_of_nonneg (by linarith)]
        linarith
    simp [aux_dyadicCutoff_eq_zero_of_outside (Or.inr hout)]
  exact (Complex.continuous_ofReal.comp aux_continuous_dyadicCutoff).integrable_of_hasCompactSupport
    hsupport

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_dyadicCutoff_eq_negOuter_transition {ξ : ℝ}
    (_hξa : -2 ≤ ξ) (hξb : ξ ≤ -1) :
    dyadicCutoff ξ = aux_dyadicTransition 0 1 2 1 ξ := by
  unfold dyadicCutoff lowFrequencyCutoff aux_dyadicTransition
  rw [abs_of_nonpos (by linarith : ξ ≤ 0),
    abs_of_nonpos (by linarith : 2 * ξ ≤ 0)]
  have harg : 2 - -ξ = 2 + ξ := by ring
  rw [harg, aux_smoothStep_eq_zero_of_nonpos (by linarith : 2 - -(2 * ξ) ≤ 0)]
  ring_nf

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_dyadicCutoff_eq_negInner_transition {ξ : ℝ}
    (hξa : -1 ≤ ξ) (hξb : ξ ≤ -1 / 2) :
    dyadicCutoff ξ = aux_dyadicTransition 1 (-1) 2 2 ξ := by
  unfold dyadicCutoff lowFrequencyCutoff aux_dyadicTransition
  rw [abs_of_nonpos (by linarith : ξ ≤ 0),
    abs_of_nonpos (by linarith : 2 * ξ ≤ 0)]
  have hfirst : 2 - -ξ = 2 + ξ := by ring
  have harg : 2 - -(2 * ξ) = 2 + 2 * ξ := by ring
  rw [hfirst, harg, aux_smoothStep_eq_one_of_one_le (by linarith : 1 ≤ 2 + ξ)]
  ring_nf

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_dyadicCutoff_eq_posInner_transition {ξ : ℝ}
    (hξa : 1 / 2 ≤ ξ) (hξb : ξ ≤ 1) :
    dyadicCutoff ξ = aux_dyadicTransition 1 (-1) 2 (-2) ξ := by
  unfold dyadicCutoff lowFrequencyCutoff aux_dyadicTransition
  rw [abs_of_nonneg (by linarith : 0 ≤ ξ),
    abs_of_nonneg (by linarith : 0 ≤ 2 * ξ)]
  rw [aux_smoothStep_eq_one_of_one_le (by linarith : 1 ≤ 2 - ξ)]
  ring_nf

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_dyadicCutoff_eq_posOuter_transition {ξ : ℝ}
    (hξa : 1 ≤ ξ) (_hξb : ξ ≤ 2) :
    dyadicCutoff ξ = aux_dyadicTransition 0 1 2 (-1) ξ := by
  unfold dyadicCutoff lowFrequencyCutoff aux_dyadicTransition
  rw [abs_of_nonneg (by linarith : 0 ≤ ξ),
    abs_of_nonneg (by linarith : 0 ≤ 2 * ξ)]
  rw [aux_smoothStep_eq_zero_of_nonpos (by linarith : 2 - 2 * ξ ≤ 0)]
  ring_nf

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_dyadicCutoff_eq_zero_middle {ξ : ℝ}
    (hξa : -1 / 2 ≤ ξ) (hξb : ξ ≤ 1 / 2) : dyadicCutoff ξ = 0 := by
  apply aux_dyadicCutoff_eq_zero_of_outside
  left
  rw [abs_le]
  constructor <;> linarith

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_dyadicFourierIntegrand_continuous (x : ℝ) :
    Continuous (fun ξ : ℝ ↦ aux_dyadicFourierPhase x ξ * (dyadicCutoff ξ : ℂ)) := by
  exact (aux_continuous_dyadicFourierPhase x).mul
    (Complex.continuous_ofReal.comp aux_continuous_dyadicCutoff)

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_dyadicFourier_integral_eq_interval (x : ℝ) :
    (∫ ξ : ℝ, aux_dyadicFourierPhase x ξ * (dyadicCutoff ξ : ℂ)) =
      ∫ ξ in (-2 : ℝ)..2, aux_dyadicFourierPhase x ξ * (dyadicCutoff ξ : ℂ) := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro ξ hξ
  rw [Function.mem_support] at hξ
  constructor
  · by_contra h
    have hle : ξ ≤ -2 := le_of_not_gt h
    have hphi : dyadicCutoff ξ = 0 :=
      aux_dyadicCutoff_eq_zero_of_outside (Or.inr (by
        rw [abs_of_nonpos (by linarith : ξ ≤ 0)]
        linarith))
    apply hξ
    simp [hphi]
  · by_contra h
    have hgt : 2 < ξ := lt_of_not_ge h
    have hphi : dyadicCutoff ξ = 0 :=
      aux_dyadicCutoff_eq_zero_of_outside (Or.inr (by
        rw [abs_of_nonneg (by linarith : 0 ≤ ξ)]
        linarith))
    apply hξ
    simp [hphi]

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_dyadicFourier_integral_five_parts (x : ℝ) :
    (∫ ξ in (-2 : ℝ)..2, aux_dyadicFourierPhase x ξ * (dyadicCutoff ξ : ℂ)) =
      (∫ ξ in (-2 : ℝ)..(-1), aux_dyadicFourierPhase x ξ * (dyadicCutoff ξ : ℂ)) +
      (∫ ξ in (-1 : ℝ)..(-1 / 2), aux_dyadicFourierPhase x ξ * (dyadicCutoff ξ : ℂ)) +
      (∫ ξ in (-1 / 2 : ℝ)..(1 / 2), aux_dyadicFourierPhase x ξ * (dyadicCutoff ξ : ℂ)) +
      (∫ ξ in (1 / 2 : ℝ)..1, aux_dyadicFourierPhase x ξ * (dyadicCutoff ξ : ℂ)) +
      ∫ ξ in (1 : ℝ)..2, aux_dyadicFourierPhase x ξ * (dyadicCutoff ξ : ℂ) := by
  let g : ℝ → ℂ := fun ξ ↦ aux_dyadicFourierPhase x ξ * (dyadicCutoff ξ : ℂ)
  have hg : Continuous g := aux_dyadicFourierIntegrand_continuous x
  have hi (a b : ℝ) : IntervalIntegrable g volume a b := hg.intervalIntegrable a b
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hi (-2 : ℝ) (-1)) (hi (-1 : ℝ) (-1 / 2))
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hi (-2 : ℝ) (-1 / 2)) (hi (-1 / 2 : ℝ) (1 / 2))
  have h3 := intervalIntegral.integral_add_adjacent_intervals
    (hi (-2 : ℝ) (1 / 2)) (hi (1 / 2 : ℝ) 1)
  have h4 := intervalIntegral.integral_add_adjacent_intervals
    (hi (-2 : ℝ) 1) (hi (1 : ℝ) 2)
  change (∫ ξ in (-2 : ℝ)..2, g ξ) = _
  rw [← h4, ← h3, ← h2, ← h1]

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_dyadicFourier_middle_zero_integral (x : ℝ) :
    (∫ t in (-1 / 2 : ℝ)..(1 / 2), aux_dyadicFourierPhase x t *
      (dyadicCutoff t : ℂ)) = 0 := by
  rw [intervalIntegral.integral_congr (fun t ht ↦ by
    have ht' : -1 / 2 ≤ t ∧ t ≤ 1 / 2 := by
      rw [Set.uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] at ht
      exact ht
    rw [aux_dyadicCutoff_eq_zero_middle ht'.1 ht'.2])]
  simp

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_dyadicFourier_negOuter_ibp (x : ℝ) (hx : x ≠ 0) :
    (∫ t in (-2 : ℝ)..(-1), aux_dyadicFourierPhase x t *
      (dyadicCutoff t : ℂ)) =
      (aux_dyadicTransition 0 1 2 1 (-1) : ℂ) * aux_dyadicFourierPhasePrimitive x (-1) -
        (aux_dyadicTransition 0 1 2 1 (-2) : ℂ) * aux_dyadicFourierPhasePrimitive x (-2) +
      ∫ t in (-2 : ℝ)..(-1), (aux_dyadicTransitionSecondDeriv 1 2 1 t : ℂ) *
        aux_dyadicFourierPhaseSecondPrimitive x t := by
  have htrans := aux_transition_fourier_ibp_twice (l := (-2 : ℝ)) (r := (-1 : ℝ))
    (x := x) (c := 0) (e := 1) (a := 2) (b := 1) hx (by
      intro t ht
      have ht' : -2 < t ∧ t < -1 := by
        norm_num [min_eq_left, max_eq_right] at ht
        exact ht
      constructor <;> linarith) (by norm_num) (by norm_num)
  rw [intervalIntegral.integral_congr (fun t ht ↦ by
    have ht' : -2 ≤ t ∧ t ≤ -1 := by
      rw [Set.uIcc_of_le (by norm_num : (-2 : ℝ) ≤ -1)] at ht
      exact ht
    rw [aux_dyadicCutoff_eq_negOuter_transition ht'.1 ht'.2])]
  exact htrans

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_dyadicFourier_negInner_ibp (x : ℝ) (hx : x ≠ 0) :
    (∫ t in (-1 : ℝ)..(-1 / 2), aux_dyadicFourierPhase x t *
      (dyadicCutoff t : ℂ)) =
      (aux_dyadicTransition 1 (-1) 2 2 (-1 / 2) : ℂ) *
          aux_dyadicFourierPhasePrimitive x (-1 / 2) -
        (aux_dyadicTransition 1 (-1) 2 2 (-1) : ℂ) *
          aux_dyadicFourierPhasePrimitive x (-1) +
      ∫ t in (-1 : ℝ)..(-1 / 2), (aux_dyadicTransitionSecondDeriv (-1) 2 2 t : ℂ) *
        aux_dyadicFourierPhaseSecondPrimitive x t := by
  have htrans := aux_transition_fourier_ibp_twice (l := (-1 : ℝ)) (r := (-1 / 2 : ℝ))
    (x := x) (c := 1) (e := -1) (a := 2) (b := 2) hx (by
      intro t ht
      have ht' : -1 < t ∧ t < -1 / 2 := by
        norm_num [min_eq_left, max_eq_right] at ht
        constructor <;> linarith [ht.1, ht.2]
      constructor <;> linarith) (by norm_num) (by norm_num)
  rw [intervalIntegral.integral_congr (fun t ht ↦ by
    have ht' : -1 ≤ t ∧ t ≤ -1 / 2 := by
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ -1 / 2)] at ht
      exact ht
    rw [aux_dyadicCutoff_eq_negInner_transition ht'.1 ht'.2])]
  exact htrans

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_dyadicFourier_posInner_ibp (x : ℝ) (hx : x ≠ 0) :
    (∫ t in (1 / 2 : ℝ)..1, aux_dyadicFourierPhase x t *
      (dyadicCutoff t : ℂ)) =
      (aux_dyadicTransition 1 (-1) 2 (-2) 1 : ℂ) * aux_dyadicFourierPhasePrimitive x 1 -
        (aux_dyadicTransition 1 (-1) 2 (-2) (1 / 2) : ℂ) *
          aux_dyadicFourierPhasePrimitive x (1 / 2) +
      ∫ t in (1 / 2 : ℝ)..1, (aux_dyadicTransitionSecondDeriv (-1) 2 (-2) t : ℂ) *
        aux_dyadicFourierPhaseSecondPrimitive x t := by
  have htrans := aux_transition_fourier_ibp_twice (l := (1 / 2 : ℝ)) (r := (1 : ℝ))
    (x := x) (c := 1) (e := -1) (a := 2) (b := -2) hx (by
      intro t ht
      have ht' : 1 / 2 < t ∧ t < 1 := by
        norm_num [min_eq_left, max_eq_right] at ht
        exact ht
      constructor <;> linarith) (by norm_num) (by norm_num)
  rw [intervalIntegral.integral_congr (fun t ht ↦ by
    have ht' : 1 / 2 ≤ t ∧ t ≤ 1 := by
      rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
      exact ht
    rw [aux_dyadicCutoff_eq_posInner_transition ht'.1 ht'.2])]
  exact htrans

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_dyadicFourier_posOuter_ibp (x : ℝ) (hx : x ≠ 0) :
    (∫ t in (1 : ℝ)..2, aux_dyadicFourierPhase x t *
      (dyadicCutoff t : ℂ)) =
      (aux_dyadicTransition 0 1 2 (-1) 2 : ℂ) * aux_dyadicFourierPhasePrimitive x 2 -
        (aux_dyadicTransition 0 1 2 (-1) 1 : ℂ) * aux_dyadicFourierPhasePrimitive x 1 +
      ∫ t in (1 : ℝ)..2, (aux_dyadicTransitionSecondDeriv 1 2 (-1) t : ℂ) *
        aux_dyadicFourierPhaseSecondPrimitive x t := by
  have htrans := aux_transition_fourier_ibp_twice (l := (1 : ℝ)) (r := (2 : ℝ))
    (x := x) (c := 0) (e := 1) (a := 2) (b := -1) hx (by
      intro t ht
      have ht' : 1 < t ∧ t < 2 := by
        norm_num [min_eq_left, max_eq_right] at ht
        exact ht
      constructor <;> linarith) (by norm_num) (by norm_num)
  rw [intervalIntegral.integral_congr (fun t ht ↦ by
    have ht' : 1 ≤ t ∧ t ≤ 2 := by
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
      exact ht
    rw [aux_dyadicCutoff_eq_posOuter_transition ht'.1 ht'.2])]
  exact htrans

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_dyadicFourier_tail_representation (x : ℝ) (hx : x ≠ 0) :
    (∫ ξ : ℝ, aux_dyadicFourierPhase x ξ * (dyadicCutoff ξ : ℂ)) =
      (∫ t in (-2 : ℝ)..(-1),
        (aux_dyadicTransitionSecondDeriv 1 2 1 t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      (∫ t in (-1 : ℝ)..(-1 / 2),
        (aux_dyadicTransitionSecondDeriv (-1) 2 2 t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      (∫ t in (1 / 2 : ℝ)..1,
        (aux_dyadicTransitionSecondDeriv (-1) 2 (-2) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      ∫ t in (1 : ℝ)..2,
        (aux_dyadicTransitionSecondDeriv 1 2 (-1) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t := by
  rw [aux_dyadicFourier_integral_eq_interval,
    aux_dyadicFourier_integral_five_parts]
  rw [aux_dyadicFourier_negOuter_ibp x hx,
    aux_dyadicFourier_negInner_ibp x hx,
    aux_dyadicFourier_middle_zero_integral x,
    aux_dyadicFourier_posInner_ibp x hx,
    aux_dyadicFourier_posOuter_ibp x hx]
  norm_num [aux_dyadicTransition, smoothStep]
  ring

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_dyadicFourier_tail_norm (x : ℝ) (hx : x ≠ 0) :
    ‖∫ ξ : ℝ, aux_dyadicFourierPhase x ξ * (dyadicCutoff ξ : ℂ)‖ ≤ 4 / x ^ 2 := by
  rw [aux_dyadicFourier_tail_representation x hx]
  have hnegOuter := aux_transition_remainder_bound
    (l := (-2 : ℝ)) (r := (-1 : ℝ)) (x := x) (e := 1) (a := 2) (b := (1 : ℝ))
    (K := 6) hx (by
      intro t ht
      have ht' : -2 < t ∧ t ≤ -1 := by
        rw [Set.uIoc_of_le (by norm_num : (-2 : ℝ) ≤ -1)] at ht
        exact ht
      constructor <;> linarith) (by norm_num)
  have hnegInner := aux_transition_remainder_bound
    (l := (-1 : ℝ)) (r := (-1 / 2 : ℝ)) (x := x) (e := -1) (a := 2) (b := (2 : ℝ))
    (K := 24) hx (by
      intro t ht
      have ht' : -1 < t ∧ t ≤ -1 / 2 := by
        rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ -1 / 2)] at ht
        constructor <;> linarith [ht.1, ht.2]
      constructor <;> linarith) (by norm_num)
  have hposInner := aux_transition_remainder_bound
    (l := (1 / 2 : ℝ)) (r := (1 : ℝ)) (x := x) (e := -1) (a := 2) (b := (-2 : ℝ))
    (K := 24) hx (by
      intro t ht
      have ht' : 1 / 2 < t ∧ t ≤ 1 := by
        rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
        exact ht
      constructor <;> linarith) (by norm_num)
  have hposOuter := aux_transition_remainder_bound
    (l := (1 : ℝ)) (r := (2 : ℝ)) (x := x) (e := 1) (a := 2) (b := (-1 : ℝ))
    (K := 6) hx (by
      intro t ht
      have ht' : 1 < t ∧ t ≤ 2 := by
        rw [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
        exact ht
      constructor <;> linarith) (by norm_num)
  calc
    ‖(∫ t in (-2 : ℝ)..(-1),
        (aux_dyadicTransitionSecondDeriv 1 2 1 t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      (∫ t in (-1 : ℝ)..(-1 / 2),
        (aux_dyadicTransitionSecondDeriv (-1) 2 2 t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      (∫ t in (1 / 2 : ℝ)..1,
        (aux_dyadicTransitionSecondDeriv (-1) 2 (-2) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      ∫ t in (1 : ℝ)..2,
        (aux_dyadicTransitionSecondDeriv 1 2 (-1) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t‖ ≤
        ‖∫ t in (-2 : ℝ)..(-1),
          (aux_dyadicTransitionSecondDeriv 1 2 1 t : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x t‖ +
        ‖∫ t in (-1 : ℝ)..(-1 / 2),
          (aux_dyadicTransitionSecondDeriv (-1) 2 2 t : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x t‖ +
        ‖∫ t in (1 / 2 : ℝ)..1,
          (aux_dyadicTransitionSecondDeriv (-1) 2 (-2) t : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x t‖ +
        ‖∫ t in (1 : ℝ)..2,
          (aux_dyadicTransitionSecondDeriv 1 2 (-1) t : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x t‖ := by
      exact norm_add_le_of_le
        (norm_add_le_of_le (norm_add_le _ _) le_rfl) le_rfl
    _ ≤ (6 / (16 * x ^ 2)) * |(-1 : ℝ) - (-2)| +
        (24 / (16 * x ^ 2)) * |(-1 / 2 : ℝ) - (-1)| +
        (24 / (16 * x ^ 2)) * |(1 : ℝ) - (1 / 2)| +
        (6 / (16 * x ^ 2)) * |(2 : ℝ) - 1| := by
      gcongr
    _ ≤ 4 / x ^ 2 := by
      have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
      have hsum :
          (6 / (16 * x ^ 2)) * |(-1 : ℝ) - (-2)| +
            (24 / (16 * x ^ 2)) * |(-1 / 2 : ℝ) - (-1)| +
            (24 / (16 * x ^ 2)) * |(1 : ℝ) - (1 / 2)| +
            (6 / (16 * x ^ 2)) * |(2 : ℝ) - 1| =
              (9 / 4 : ℝ) / x ^ 2 := by
        rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ -1 - -2),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ -1 / 2 - -1),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 - 1)]
        field_simp [hx2.ne']
        ring
      rw [hsum]
      apply (div_le_div_iff_of_pos_right hx2).2
      norm_num

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_inverseFourierTransform_dyadic_eq_phase (x : ℝ) :
    inverseFourierTransform (fun ξ ↦ (dyadicCutoff ξ : ℂ)) x =
      ∫ ξ : ℝ, aux_dyadicFourierPhase x ξ * (dyadicCutoff ξ : ℂ) := by
  rw [inverseFourierTransform, Real.fourierInv_eq']
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  congr 3
  rw [Real.inner_apply]
  push_cast
  ring

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_dyadic_inverseFourier_tail_bound (x : ℝ) (hx : x ≠ 0) :
    ‖inverseFourierTransform (fun ξ ↦ (dyadicCutoff ξ : ℂ)) x‖ ≤ 4 / x ^ 2 := by
  rw [aux_inverseFourierTransform_dyadic_eq_phase]
  exact aux_dyadicFourier_tail_norm x hx

lemma test_dyadicCutoff_norm_integral_le_eight :
    (∫ ξ : ℝ, ‖(dyadicCutoff ξ : ℂ)‖) ≤ 8 := by
  let s : Set ℝ := Set.Icc (-2 : ℝ) 2
  have hs : MeasurableSet s := measurableSet_Icc
  let h : ℝ → ℝ := s.indicator (fun _ ↦ (2 : ℝ))
  have hphiint : Integrable (fun ξ : ℝ ↦ ‖(dyadicCutoff ξ : ℂ)‖) volume :=
    aux_dyadicCutoff_integrable.norm
  have hsfinite : volume s ≠ ∞ := by
    simp [s, Real.volume_Icc]
  have hint : Integrable h volume := by
    exact (integrableOn_const hsfinite).integrable_indicator hs
  have hdom : (fun ξ : ℝ ↦ ‖(dyadicCutoff ξ : ℂ)‖) ≤ h := by
    intro ξ
    change ‖(dyadicCutoff ξ : ℂ)‖ ≤ h ξ
    by_cases hξ : ξ ∈ s
    · rw [show h ξ = 2 by simp [h, hξ]]
      rw [Complex.norm_real, Real.norm_eq_abs]
      change |lowFrequencyCutoff ξ - lowFrequencyCutoff (2 * ξ)| ≤ 2
      rw [lowFrequencyCutoff, lowFrequencyCutoff, abs_le]
      have hη := aux_smoothStep_nonneg_le_one (2 - |ξ|)
      have hη2 := aux_smoothStep_nonneg_le_one (2 - |2 * ξ|)
      constructor <;> linarith
    · rw [show h ξ = 0 by simp [h, hξ]]
      have hout : 2 ≤ |ξ| := by
        by_contra hnot
        apply hξ
        change ξ ∈ Set.Icc (-2 : ℝ) 2
        have hlt : |ξ| < 2 := lt_of_not_ge hnot
        rw [abs_lt] at hlt
        exact ⟨hlt.1.le, hlt.2.le⟩
      rw [aux_dyadicCutoff_eq_zero_of_outside (Or.inr hout)]
      simp
  calc
    (∫ ξ : ℝ, ‖(dyadicCutoff ξ : ℂ)‖) ≤ ∫ ξ : ℝ, h ξ :=
      integral_mono hphiint hint hdom
    _ = 8 := by
      change (∫ ξ : ℝ, s.indicator (fun _ ↦ (2 : ℝ)) ξ) = 8
      rw [integral_indicator_const (μ := volume) (2 : ℝ) hs]
      rw [show s = Set.Icc (-2 : ℝ) 2 by rfl,
        Real.volume_real_Icc_of_le (by norm_num)]
      norm_num

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_dyadic_inverseFourier_uniform_bound (x : ℝ) :
    ‖inverseFourierTransform (fun ξ ↦ (dyadicCutoff ξ : ℂ)) x‖ ≤ 8 := by
  change ‖VectorFourier.fourierIntegral 𝐞 volume (-(innerₗ ℝ))
      (fun ξ : ℝ ↦ (dyadicCutoff ξ : ℂ)) x‖ ≤ 8
  calc
    ‖VectorFourier.fourierIntegral 𝐞 volume (-(innerₗ ℝ))
        (fun ξ : ℝ ↦ (dyadicCutoff ξ : ℂ)) x‖ ≤
        ∫ ξ : ℝ, ‖(dyadicCutoff ξ : ℂ)‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (-(innerₗ ℝ)) _ x
    _ ≤ 8 := test_dyadicCutoff_norm_integral_le_eight

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_dyadicInverseFourierKernel_continuous :
    Continuous (inverseFourierTransform fun ξ : ℝ ↦ (dyadicCutoff ξ : ℂ)) := by
  let hmem : MemLp (fun ξ : ℝ ↦ (dyadicCutoff ξ : ℂ)) 1 volume :=
    memLp_one_iff_integrable.mpr aux_dyadicCutoff_integrable
  unfold inverseFourierTransform
  rw [← Real.Lp.fourierTransformInv_toLp hmem]
  exact (Real.Lp.fourierTransformInv hmem.toLp).continuous

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_dyadicInverseFourierKernel_memLp_one :
    MemLp (inverseFourierTransform fun ξ : ℝ ↦ (dyadicCutoff ξ : ℂ)) 1 volume := by
  refine ⟨aux_dyadicInverseFourierKernel_continuous.aestronglyMeasurable, ?_⟩
  exact (aux_eLpNorm_le_of_local_tail aux_dyadic_inverseFourier_uniform_bound
    aux_dyadic_inverseFourier_tail_bound).trans_lt (by norm_num)

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_dyadicInverseFourierKernel_memLp_two :
    MemLp (inverseFourierTransform fun ξ : ℝ ↦ (dyadicCutoff ξ : ℂ)) 2 volume := by
  let K : ℝ → ℂ := inverseFourierTransform fun ξ : ℝ ↦ (dyadicCutoff ξ : ℂ)
  have hKmeas : AEStronglyMeasurable K volume :=
    aux_dyadicInverseFourierKernel_continuous.aestronglyMeasurable
  have hKint : Integrable K volume :=
    memLp_one_iff_integrable.mp aux_dyadicInverseFourierKernel_memLp_one
  have hmajor : Integrable (fun x : ℝ ↦ 8 * ‖K x‖) volume :=
    hKint.norm.const_mul 8
  have hsq : Integrable (fun x : ℝ ↦ ‖K x‖ ^ 2) volume :=
    hmajor.mono' (hKmeas.norm.pow 2) (Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖K x‖)]
      have hbound : ‖K x‖ ≤ 8 := aux_dyadic_inverseFourier_uniform_bound x
      nlinarith [norm_nonneg (K x)])
  apply (memLp_norm_iff hKmeas).mp
  exact (memLp_two_iff_integrable_sq hKmeas.norm).mpr hsq

/- The (L^1) annular-kernel fact in integrable form, used below for
Fourier convolution in `dyadicReconstructionAndMultiplierBounds`. -/
/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_annularInverseFourierKernel_integrable :
    Integrable (inverseFourierTransform fun ξ : ℝ ↦ (annularCutoff ξ : ℂ)) volume :=
  memLp_one_iff_integrable.mp aux_annularInverseFourierKernel_memLp_one

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_dyadicInverseFourierKernel_integrable :
    Integrable (inverseFourierTransform fun ξ : ℝ ↦ (dyadicCutoff ξ : ℂ)) volume :=
  memLp_one_iff_integrable.mp aux_dyadicInverseFourierKernel_memLp_one

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_fourier_dyadicInverseFourierKernel_integrable :
    Integrable (fun ξ : ℝ ↦ 𝓕 (fun t : ℝ ↦ (dyadicCutoff t : ℂ)) ξ) volume := by
  have hcheck := aux_dyadicInverseFourierKernel_integrable
  have hneg : Integrable
      ((inverseFourierTransform fun t : ℝ ↦ (dyadicCutoff t : ℂ)) ∘
        fun x : ℝ ↦ -x) volume :=
    ((Measure.measurePreserving_neg volume).integrable_comp hcheck.1).mpr hcheck
  convert hneg using 1
  ext x
  simpa [inverseFourierTransform] using
    (Real.fourierInv_eq_fourier_neg (fun t : ℝ ↦ (dyadicCutoff t : ℂ)) (-x)).symm

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_fourier_dyadicInverseFourierKernel_eq (ξ : ℝ) :
    𝓕 (inverseFourierTransform fun t : ℝ ↦ (dyadicCutoff t : ℂ)) ξ =
      (dyadicCutoff ξ : ℂ) := by
  have h := Continuous.fourier_fourierInv_eq
    (Complex.continuous_ofReal.comp aux_continuous_dyadicCutoff)
    aux_dyadicCutoff_integrable aux_fourier_dyadicInverseFourierKernel_integrable
  exact congrFun h ξ

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_annular_dyadicInverseFourierKernel_convolution_fourier (ξ : ℝ) :
    𝓕 ((inverseFourierTransform fun t : ℝ ↦ (annularCutoff t : ℂ)) ⋆[
      ContinuousLinearMap.mul ℂ ℂ]
      (inverseFourierTransform fun t : ℝ ↦ (dyadicCutoff t : ℂ))) ξ =
      (dyadicCutoff ξ : ℂ) := by
  rw [Real.fourier_mul_convolution_eq
    aux_annularInverseFourierKernel_integrable aux_dyadicInverseFourierKernel_integrable]
  rw [aux_fourier_annularInverseFourierKernel_eq, aux_fourier_dyadicInverseFourierKernel_eq,
    aux_annularCutoff_mul_dyadicCutoff]

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_annular_dyadicInverseFourierKernel_convolution_eq :
    (inverseFourierTransform fun t : ℝ ↦ (annularCutoff t : ℂ)) ⋆[
      ContinuousLinearMap.mul ℂ ℂ]
      (inverseFourierTransform fun t : ℝ ↦ (dyadicCutoff t : ℂ)) =
    inverseFourierTransform fun t : ℝ ↦ (dyadicCutoff t : ℂ) := by
  let qK : ℝ → ℂ := inverseFourierTransform fun t : ℝ ↦ (annularCutoff t : ℂ)
  let φK : ℝ → ℂ := inverseFourierTransform fun t : ℝ ↦ (dyadicCutoff t : ℂ)
  have hqint : Integrable qK volume := aux_annularInverseFourierKernel_integrable
  have hφint : Integrable φK volume := aux_dyadicInverseFourierKernel_integrable
  have hconvint : Integrable (qK ⋆[ContinuousLinearMap.mul ℂ ℂ] φK) volume :=
    hqint.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hφint
  have hqbd : BddAbove (Set.range fun x : ℝ ↦ ‖qK x‖) := by
    refine ⟨8, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact aux_annular_inverseFourier_uniform_bound x
  have hcont : Continuous (qK ⋆[ContinuousLinearMap.mul ℂ ℂ] φK) :=
    hqbd.continuous_convolution_left_of_integrable (ContinuousLinearMap.mul ℂ ℂ)
      aux_annularInverseFourierKernel_continuous hφint
  have hfourier : 𝓕 (qK ⋆[ContinuousLinearMap.mul ℂ ℂ] φK) =
      fun ξ : ℝ ↦ (dyadicCutoff ξ : ℂ) := by
    ext ξ
    exact aux_annular_dyadicInverseFourierKernel_convolution_fourier ξ
  have hfourierInt : Integrable (𝓕 (qK ⋆[ContinuousLinearMap.mul ℂ ℂ] φK)) volume := by
    rw [hfourier]
    exact aux_dyadicCutoff_integrable
  have hinv := Continuous.fourierInv_fourier_eq hcont hconvint hfourierInt
  calc
    qK ⋆[ContinuousLinearMap.mul ℂ ℂ] φK =
      𝓕⁻ (𝓕 (qK ⋆[ContinuousLinearMap.mul ℂ ℂ] φK)) :=
      hinv.symm
    _ = 𝓕⁻ (fun ξ : ℝ ↦ (dyadicCutoff ξ : ℂ)) := by rw [hfourier]
    _ = φK := rfl

/- Dilation commutes exactly with raw convolution for positive scales. -/
/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
def aux_scaleKernel (a : ℝ) (h : ℝ → ℂ) : ℝ → ℂ :=
  fun x ↦ (a : ℂ) * h (a * x)

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_scaleKernel_convolution (a : ℝ) (ha : 0 < a) (q φ : ℝ → ℂ) :
    aux_scaleKernel a q ⋆[ContinuousLinearMap.mul ℂ ℂ] aux_scaleKernel a φ =
      aux_scaleKernel a (q ⋆[ContinuousLinearMap.mul ℂ ℂ] φ) := by
  ext x
  unfold aux_scaleKernel
  change (∫ t : ℝ, ((a : ℂ) * q (a * t)) * ((a : ℂ) * φ (a * (x - t)))) = _
  let g : ℝ → ℂ := fun u ↦ q u * φ (a * x - u)
  have hpoint (t : ℝ) :
      ((a : ℂ) * q (a * t)) * ((a : ℂ) * φ (a * (x - t))) =
        ((a : ℂ) ^ 2) * g (a * t) := by
    dsimp [g]
    rw [show a * (x - t) = a * x - a * t by ring]
    ring
  have hfun : (fun t : ℝ ↦ ((a : ℂ) * q (a * t)) * ((a : ℂ) * φ (a * (x - t)))) =
      (fun t ↦ ((a : ℂ) ^ 2) * g (a * t)) := by
    ext t
    exact hpoint t
  rw [hfun]
  rw [MeasureTheory.integral_const_mul]
  rw [Measure.integral_comp_mul_left g a]
  change ((a : ℂ) ^ 2) * (|a⁻¹| • ∫ y : ℝ, g y) =
    (a : ℂ) * ∫ t : ℝ, q t * φ (a * x - t)
  rw [show |a⁻¹| = a⁻¹ by rw [abs_of_pos (inv_pos.mpr ha)]]
  rw [Complex.real_smul, Complex.ofReal_inv]
  dsimp [g]
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  field_simp

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_scaled_annular_dyadicInverseFourierKernel_convolution_eq (k : ℕ) :
    (aux_scaledInverseFourierKernel (fun ξ ↦ (annularCutoff ξ : ℂ)) k) ⋆[
        ContinuousLinearMap.mul ℂ ℂ]
      (aux_scaledInverseFourierKernel (fun ξ ↦ (dyadicCutoff ξ : ℂ)) k) =
      aux_scaledInverseFourierKernel (fun ξ ↦ (dyadicCutoff ξ : ℂ)) k := by
  let a : ℝ := (2 : ℝ) ^ k
  let qK : ℝ → ℂ := inverseFourierTransform fun ξ ↦ (annularCutoff ξ : ℂ)
  let φK : ℝ → ℂ := inverseFourierTransform fun ξ ↦ (dyadicCutoff ξ : ℂ)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hq : aux_scaledInverseFourierKernel (fun ξ ↦ (annularCutoff ξ : ℂ)) k =
      aux_scaleKernel a qK := by
    ext x
    simp [aux_scaledInverseFourierKernel, aux_scaleKernel, a, qK]
  have hφ : aux_scaledInverseFourierKernel (fun ξ ↦ (dyadicCutoff ξ : ℂ)) k =
      aux_scaleKernel a φK := by
    ext x
    simp [aux_scaledInverseFourierKernel, aux_scaleKernel, a, φK]
  rw [hq, hφ, aux_scaleKernel_convolution a ha qK φK,
    aux_annular_dyadicInverseFourierKernel_convolution_eq]

/- Measurability of the positive (L^2\)-convolution majorant. -/
/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_norm_convolution_aestronglyMeasurable {b f : ℝ → ℂ}
    (hb : MemLp b 2 volume) (hf : MemLp f 2 volume) :
    AEStronglyMeasurable
      ((fun x : ℝ ↦ ‖b x‖) ⋆[ContinuousLinearMap.mul ℝ ℝ]
        fun x : ℝ ↦ ‖f x‖) volume := by
  unfold convolution
  exact
    ((hb.1.norm).convolution_integrand
      (ContinuousLinearMap.mul ℝ ℝ) hf.1.norm).integral_prod_right'

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_norm_convolution_nonneg {b f : ℝ → ℂ} (x : ℝ) :
    0 ≤ ((fun y : ℝ ↦ ‖b y‖) ⋆[ContinuousLinearMap.mul ℝ ℝ]
      fun y : ℝ ↦ ‖f y‖) x := by
  change 0 ≤ ∫ t : ℝ, ‖b t‖ * ‖f (x - t)‖
  exact integral_nonneg fun t ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)

/- The elementary (L^2\)-Cauchy bound for the positive convolution. -/
/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_norm_convolution_le_l2_product {b f : ℝ → ℂ}
    (hb : MemLp b 2 volume) (hf : MemLp f 2 volume) (x : ℝ) :
    ((fun y : ℝ ↦ ‖b y‖) ⋆[ContinuousLinearMap.mul ℝ ℝ]
      fun y : ℝ ↦ ‖f y‖) x ≤
      (∫ y : ℝ, ‖b y‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (∫ y : ℝ, ‖f y‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  have hfx : MemLp (f ∘ fun t : ℝ ↦ x - t) 2 volume :=
    hf.comp_measurePreserving (volume.measurePreserving_sub_left x)
  have hb' : MemLp b (ENNReal.ofReal (2 : ℝ)) volume := by
    norm_num
    exact hb
  have hfx' : MemLp (f ∘ fun t : ℝ ↦ x - t) (ENNReal.ofReal (2 : ℝ)) volume := by
    norm_num
    exact hfx
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    Real.HolderConjugate.two_two hb' hfx'
  change (∫ t : ℝ, ‖b t‖ * ‖f (x - t)‖) ≤ _
  calc
    (∫ t : ℝ, ‖b t‖ * ‖f (x - t)‖) ≤
        (∫ t : ℝ, ‖b t‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫ t : ℝ, ‖(f ∘ fun t : ℝ ↦ x - t) t‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
            simpa only [Function.comp_apply] using hholder
    _ = _ := by
      simp only [Function.comp_apply]
      rw [integral_sub_left_eq_self (fun y : ℝ ↦ ‖f y‖ ^ (2 : ℝ)) volume x]

/- The last Fubini condition in `convolution_assoc` follows from one
integrable left kernel and two (L^2\) factors. -/
/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_norm_left_convolutionExistsAt_of_memLp_one_two {a b f : ℝ → ℂ}
    (ha : MemLp a 1 volume) (hb : MemLp b 2 volume) (hf : MemLp f 2 volume)
    (x : ℝ) :
    ConvolutionExistsAt (fun y : ℝ ↦ ‖a y‖)
      ((fun y : ℝ ↦ ‖b y‖) ⋆[ContinuousLinearMap.mul ℝ ℝ]
        fun y : ℝ ↦ ‖f y‖) x (ContinuousLinearMap.mul ℝ ℝ) volume := by
  let h : ℝ → ℝ := (fun y : ℝ ↦ ‖b y‖) ⋆[ContinuousLinearMap.mul ℝ ℝ]
    fun y : ℝ ↦ ‖f y‖
  let C : ℝ :=
    (∫ y : ℝ, ‖b y‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
      (∫ y : ℝ, ‖f y‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
  have hhmeas : AEStronglyMeasurable h volume :=
    aux_norm_convolution_aestronglyMeasurable hb hf
  have hhbound (y : ℝ) : h y ≤ C :=
    aux_norm_convolution_le_l2_product hb hf y
  have hhnonneg (y : ℝ) : 0 ≤ h y := aux_norm_convolution_nonneg y
  have hCnonneg : 0 ≤ C := (hhnonneg 0).trans (hhbound 0)
  have hshift : AEStronglyMeasurable (h ∘ fun y : ℝ ↦ x - y) volume :=
    hhmeas.comp_measurePreserving (volume.measurePreserving_sub_left x)
  have hmeas : AEStronglyMeasurable (fun y : ℝ ↦ ‖a y‖ * h (x - y)) volume := by
    change AEStronglyMeasurable ((fun y : ℝ ↦ ‖a y‖) * (h ∘ fun y : ℝ ↦ x - y)) volume
    exact ha.1.norm.mul hshift
  change Integrable (fun y : ℝ ↦ ‖a y‖ * h (x - y)) volume
  have haint : Integrable a volume := memLp_one_iff_integrable.mp ha
  refine (haint.norm.const_mul C).mono' hmeas (Eventually.of_forall fun y ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · calc
      ‖a y‖ * h (x - y) ≤ ‖a y‖ * C :=
        mul_le_mul_of_nonneg_left (hhbound (x - y)) (norm_nonneg _)
      _ = C * ‖a y‖ := mul_comm _ _
  · exact mul_nonneg (norm_nonneg _) (hhnonneg _)

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_norm_convolutionExistsAt_of_memLp_two {b f : ℝ → ℂ}
    (hb : MemLp b 2 volume) (hf : MemLp f 2 volume) (x : ℝ) :
    ConvolutionExistsAt (fun y : ℝ ↦ ‖b y‖) (fun y : ℝ ↦ ‖f y‖) x
      (ContinuousLinearMap.mul ℝ ℝ) volume := by
  rw [convolutionExistsAt_iff_integrable_swap]
  have hbx : MemLp ((fun y : ℝ ↦ ‖b y‖) ∘ fun y : ℝ ↦ x - y) 2 volume :=
    (memLp_norm_iff hb.1).mpr hb |>.comp_measurePreserving
      (volume.measurePreserving_sub_left x)
  change Integrable (((fun y : ℝ ↦ ‖b y‖) ∘ fun y : ℝ ↦ x - y) *
    fun y : ℝ ↦ ‖f y‖) volume
  exact hbx.integrable_mul ((memLp_norm_iff hf.1).mpr hf)

/- A pointwise raw associativity statement adequate for (Q_k(P_kf)). -/
/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_convolution_assoc_of_memLp_one_two {a b f : ℝ → ℂ}
    (haone : MemLp a 1 volume)
    (hbone : MemLp b 1 volume) (hbtwo : MemLp b 2 volume)
    (hftwo : MemLp f 2 volume) (x : ℝ) :
    ((a ⋆[ContinuousLinearMap.mul ℂ ℂ] b) ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x =
      (a ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (b ⋆[ContinuousLinearMap.mul ℂ ℂ] f)) x := by
  have haint : Integrable a volume := memLp_one_iff_integrable.mp haone
  have hbint : Integrable b volume := memLp_one_iff_integrable.mp hbone
  exact convolution_assoc
    (ContinuousLinearMap.mul ℂ ℂ)
    (ContinuousLinearMap.mul ℂ ℂ)
    (ContinuousLinearMap.mul ℂ ℂ)
    (ContinuousLinearMap.mul ℂ ℂ)
    (fun u v w ↦ by
      change (u * v) * w = u * (v * w)
      ring)
    haone.1 hbone.1 hftwo.1
    (haint.ae_convolution_exists (ContinuousLinearMap.mul ℂ ℂ) hbint)
    (Filter.Eventually.of_forall fun y ↦
      aux_norm_convolutionExistsAt_of_memLp_two hbtwo hftwo y)
    (aux_norm_left_convolutionExistsAt_of_memLp_one_two haone hbtwo hftwo x)

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_scaledDyadicInverseFourierKernel_memLp_one (k : ℕ) :
    MemLp (aux_scaledInverseFourierKernel (fun ξ ↦ (dyadicCutoff ξ : ℂ)) k) 1 volume := by
  let a : ℝ := (2 : ℝ) ^ k
  let K : ℝ → ℂ := inverseFourierTransform fun ξ : ℝ ↦ (dyadicCutoff ξ : ℂ)
  have ha : a ≠ 0 := by
    dsimp [a]
    positivity
  have hK : Integrable K volume :=
    memLp_one_iff_integrable.mp aux_dyadicInverseFourierKernel_memLp_one
  have hcomp : Integrable (fun x : ℝ ↦ K (a * x)) volume :=
    hK.comp_mul_left' ha
  have hEq : aux_scaledInverseFourierKernel (fun ξ ↦ (dyadicCutoff ξ : ℂ)) k =
      fun x ↦ (a : ℂ) * K (a * x) := by
    ext x
    simp [aux_scaledInverseFourierKernel, a, K]
  rw [hEq]
  exact memLp_one_iff_integrable.mpr (hcomp.const_mul (a : ℂ))

/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_scaledDyadicInverseFourierKernel_memLp_two (k : ℕ) :
    MemLp (aux_scaledInverseFourierKernel (fun ξ ↦ (dyadicCutoff ξ : ℂ)) k) 2 volume := by
  let a : ℝ := (2 : ℝ) ^ k
  let K : ℝ → ℂ := inverseFourierTransform fun ξ : ℝ ↦ (dyadicCutoff ξ : ℂ)
  have ha : a ≠ 0 := by
    dsimp [a]
    positivity
  have hKmeas : AEStronglyMeasurable K volume :=
    aux_dyadicInverseFourierKernel_continuous.aestronglyMeasurable
  have hKsq : Integrable (fun x : ℝ ↦ ‖K x‖ ^ 2) volume := by
    have hKtwo := aux_dyadicInverseFourierKernel_memLp_two
    have hKnorm : MemLp (fun x : ℝ ↦ ‖K x‖) 2 volume :=
      (memLp_norm_iff hKmeas).mpr hKtwo
    exact (memLp_two_iff_integrable_sq hKmeas.norm).mp hKnorm
  have hcomp : Integrable (fun x : ℝ ↦ ‖K (a * x)‖ ^ 2) volume :=
    hKsq.comp_mul_left' ha
  have hmeas : AEStronglyMeasurable
      (aux_scaledInverseFourierKernel (fun ξ ↦ (dyadicCutoff ξ : ℂ)) k) volume := by
    have hcont : Continuous (fun x : ℝ ↦ K (a * x)) :=
      aux_dyadicInverseFourierKernel_continuous.comp (continuous_const.mul continuous_id)
    have hmeas' : AEStronglyMeasurable (fun x : ℝ ↦ (a : ℂ) * K (a * x)) volume :=
      hcont.aestronglyMeasurable.const_mul (a : ℂ)
    unfold aux_scaledInverseFourierKernel
    simpa [a, K] using hmeas'
  apply (memLp_norm_iff hmeas).mp
  rw [memLp_two_iff_integrable_sq]
  · have hsquares :
        (fun x : ℝ ↦ ‖aux_scaledInverseFourierKernel
          (fun ξ ↦ (dyadicCutoff ξ : ℂ)) k x‖ ^ 2) =
          fun x ↦ a ^ 2 * ‖K (a * x)‖ ^ 2 := by
      funext x
      unfold aux_scaledInverseFourierKernel
      dsimp only [a, K]
      rw [norm_mul, norm_pow, Complex.norm_real]
      norm_num
      ring
    rw [hsquares]
    exact hcomp.const_mul (a ^ 2)
  · exact hmeas.norm

/- The exact raw projection identity needed for the `Q(P f)` conjunct. -/
/-- An auxiliary fact used to prove `dyadicReconstructionAndMultiplierBounds` and
the manuscript result `\label{lem:dyadic-reconstruction}`. -/
lemma aux_Q_P_eq (f : ℝ → ℂ) (hf : MemLp f 2 volume) (k : ℕ) (hk : 1 ≤ k) :
    Q k (P k f) = P k f := by
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  let qK : ℝ → ℂ :=
    aux_scaledInverseFourierKernel (fun ξ ↦ (annularCutoff ξ : ℂ)) k
  let φK : ℝ → ℂ :=
    aux_scaledInverseFourierKernel (fun ξ ↦ (dyadicCutoff ξ : ℂ)) k
  have hqone : MemLp qK 1 volume := by
    simpa [qK] using aux_scaledAnnularInverseFourierKernel_memLp_one k
  have hφone : MemLp φK 1 volume := by
    simpa [φK] using aux_scaledDyadicInverseFourierKernel_memLp_one k
  have hφtwo : MemLp φK 2 volume := by
    simpa [φK] using aux_scaledDyadicInverseFourierKernel_memLp_two k
  have hkernel : qK ⋆[ContinuousLinearMap.mul ℂ ℂ] φK = φK := by
    simpa [qK, φK] using aux_scaled_annular_dyadicInverseFourierKernel_convolution_eq k
  have hassoc : qK ⋆[ContinuousLinearMap.mul ℂ ℂ]
      (φK ⋆[ContinuousLinearMap.mul ℂ ℂ] f) =
      (qK ⋆[ContinuousLinearMap.mul ℂ ℂ] φK) ⋆[ContinuousLinearMap.mul ℂ ℂ] f := by
    ext x
    exact (aux_convolution_assoc_of_memLp_one_two hqone hφone hφtwo hf x).symm
  unfold Q P
  rw [ite_eq_right hk0]
  change qK ⋆[ContinuousLinearMap.mul ℂ ℂ]
      (φK ⋆[ContinuousLinearMap.mul ℂ ℂ] f) =
    φK ⋆[ContinuousLinearMap.mul ℂ ℂ] f
  rw [hassoc, hkernel]

/-- The translation action on the `L²` quotient used to transfer convolution
to Fourier multipliers in `dyadicReconstructionAndMultiplierBounds` for
`\label{lem:dyadic-reconstruction}`. -/
noncomputable def aux_l2Translate (t : ℝ) (g : Lp (α := ℝ) ℂ 2 volume) :
    Lp (α := ℝ) ℂ 2 volume :=
  (DomAddAct.mk (-t) : ℝᵈᵃᵃ) +ᵥ g

/-- The Fourier phase associated with `aux_l2Translate`, used in the
`L²` multiplier calculation for `dyadicReconstructionAndMultiplierBounds`
and `\label{lem:dyadic-reconstruction}`. -/
noncomputable def aux_fourierPhase (t : ℝ) : ℝ → ℂ :=
  fun ξ ↦ (Real.fourierChar ((-t) * ξ) : ℂ)

/-- Continuity of the Fourier phase used in the `L²` convolution multiplier
bridge for `dyadicReconstructionAndMultiplierBounds` and
`\label{lem:dyadic-reconstruction}`. -/
lemma aux_continuous_fourierPhase (t : ℝ) : Continuous (aux_fourierPhase t) := by
  exact continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp (continuous_const.mul continuous_id))

/-- The Fourier phase has unit modulus.  This is used to realize it as an
`L∞` multiplier in `dyadicReconstructionAndMultiplierBounds` for
`\label{lem:dyadic-reconstruction}`. -/
lemma aux_norm_fourierPhase (t ξ : ℝ) : ‖aux_fourierPhase t ξ‖ = 1 := by
  exact Circle.norm_coe _

/-- The Fourier phase is an essentially bounded multiplier.  This auxiliary
fact supports the `L²` convolution multiplier calculation in
`dyadicReconstructionAndMultiplierBounds` for
`\label{lem:dyadic-reconstruction}`. -/
lemma aux_memLp_fourierPhase_top (t : ℝ) : MemLp (aux_fourierPhase t) ∞ volume := by
  refine memLp_top_of_bound (aux_continuous_fourierPhase t).aestronglyMeasurable 1 ?_
  exact Eventually.of_forall fun ξ ↦ (aux_norm_fourierPhase t ξ).le

/-- The `L∞` representative of the phase multiplier used in the `L²`
translation identity for `dyadicReconstructionAndMultiplierBounds` and
`\label{lem:dyadic-reconstruction}`. -/
noncomputable def aux_fourierPhaseLp (t : ℝ) : Lp (α := ℝ) ℂ ∞ volume :=
  (aux_memLp_fourierPhase_top t).toLp (aux_fourierPhase t)

/-- Identifies the chosen `L∞` phase representative almost everywhere.  This
supports the Fourier-side Bochner integral in
`dyadicReconstructionAndMultiplierBounds` for
`\label{lem:dyadic-reconstruction}`. -/
lemma aux_coe_fourierPhaseLp_ae (t : ℝ) :
    (aux_fourierPhaseLp t : ℝ → ℂ) =ᵐ[volume] aux_fourierPhase t :=
  (aux_memLp_fourierPhase_top t).coeFn_toLp

/-- Bounded multiplication by an `L∞` phase is a continuous linear map on
`L²`.  This lets the Schwartz-density argument prove the translation identity
needed by `dyadicReconstructionAndMultiplierBounds` for
`\label{lem:dyadic-reconstruction}`. -/
noncomputable def aux_l2PhaseMulCLM (phase : Lp (α := ℝ) ℂ ∞ volume) :
    Lp (α := ℝ) ℂ 2 volume →L[ℂ] Lp (α := ℝ) ℂ 2 volume := by
  letI : (∞ : ℝ≥0∞).HolderTriple 2 2 := ENNReal.HolderTriple.symm
  apply LinearMap.mkContinuous
    { toFun := fun g ↦ phase • g
      map_add' := fun g h ↦ Lp.add_smul phase g h
      map_smul' := fun c g ↦ by
        change phase • (c • g) = c • (phase • g)
        exact (Lp.smul_comm (p := ∞) (q := 2) (r := 2) c phase g).symm }
    ‖phase‖
  intro g
  exact Lp.norm_smul_le phase g

/-- Continuity of spatial translation on the `L²` quotient.  This is used in
the Fourier multiplier argument for `dyadicReconstructionAndMultiplierBounds`
and `\label{lem:dyadic-reconstruction}`. -/
lemma aux_continuous_l2Translate (t : ℝ) :
    Continuous (fun g : Lp (α := ℝ) ℂ 2 volume ↦ aux_l2Translate t g) := by
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  unfold aux_l2Translate
  exact (continuous_const : Continuous (fun _ : Lp (α := ℝ) ℂ 2 volume ↦
    (DomAddAct.mk (-t) : ℝᵈᵃᵃ))).vadd continuous_id

/-- The translated `L²` representative of a Schwartz function is its usual
translated Schwartz representative almost everywhere.  This connects the
Schwartz computation to `dyadicReconstructionAndMultiplierBounds` and
`\label{lem:dyadic-reconstruction}`. -/
lemma aux_coe_l2Translate_schwartz_ae (t : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    (aux_l2Translate t (φ.toLp 2 volume) : ℝ → ℂ) =ᵐ[volume]
      (φ.compSubConstCLM ℂ t : ℝ → ℂ) := by
  have hleft := DomAddAct.vadd_Lp_ae_eq
    (DomAddAct.mk (-t) : ℝᵈᵃᵃ) (φ.toLp 2 volume)
  have hφ : (φ.toLp 2 volume : ℝ → ℂ) =ᵐ[volume] φ := φ.coeFn_toLp 2 volume
  have hshift : MeasurePreserving (fun x : ℝ ↦ x - t) volume volume := by
    simpa [sub_eq_add_neg, add_comm] using measurePreserving_add_left volume (-t)
  unfold aux_l2Translate
  filter_upwards [hleft, hφ.comp_tendsto
    hshift.quasiMeasurePreserving.tendsto_ae] with x hx hφx
  have harg : DomAddAct.mk.symm (DomAddAct.mk (-t) : ℝᵈᵃᵃ) +ᵥ x = x - t := by
    change -t + x = x - t
    ring
  have hφx' : (φ.toLp 2 volume : ℝ → ℂ) (x - t) = φ (x - t) := by
    simpa only [Function.comp_apply] using hφx
  rw [hx, harg, hφx', SchwartzMap.compSubConstCLM_apply]

/-- Equality in `L²` between a translated Schwartz representative and the
corresponding translated Schwartz function.  This is an auxiliary density
step for `dyadicReconstructionAndMultiplierBounds` and
`\label{lem:dyadic-reconstruction}`. -/
lemma aux_l2Translate_schwartz_toLp (t : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    aux_l2Translate t (φ.toLp 2 volume) =
      (φ.compSubConstCLM ℂ t).toLp 2 volume := by
  apply Lp.ext (p := 2)
  filter_upwards [aux_coe_l2Translate_schwartz_ae t φ,
    (φ.compSubConstCLM ℂ t).coeFn_toLp 2 volume] with x hleft hright
  rw [hleft, hright]

/-- The elementary Fourier formula for translating a Schwartz function.  It
is the dense-class calculation behind the `L²` convolution multiplier in
`dyadicReconstructionAndMultiplierBounds` for
`\label{lem:dyadic-reconstruction}`. -/
lemma aux_raw_fourier_schwartz_l2Translate (t ξ : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    𝓕 (φ.compSubConstCLM ℂ t : ℝ → ℂ) ξ =
      aux_fourierPhase t ξ * 𝓕 (φ : ℝ → ℂ) ξ := by
  change 𝓕 (fun x : ℝ ↦ φ (x - t)) ξ = _
  change VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ)
    (φ ∘ fun x : ℝ ↦ x + -t) ξ = _
  rw [VectorFourier.fourierIntegral_comp_add_right]
  change (𝐞 ((innerₗ ℝ) (-t) ξ) : Circle) •
      VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) (φ : ℝ → ℂ) ξ =
    aux_fourierPhase t ξ *
      VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) (φ : ℝ → ℂ) ξ
  congr 1
  simp only [innerₗ_apply_apply, Real.inner_apply]

/-- Fourier transform converts spatial translation of any `L²` class to
multiplication by the corresponding unit phase.  This is the key `L²`
translation identity used to prove the multiplier and reconstruction claims
in `dyadicReconstructionAndMultiplierBounds` for
`\label{lem:dyadic-reconstruction}`. -/
lemma aux_l2Fourier_l2Translate (t : ℝ) (g : Lp (α := ℝ) ℂ 2 volume) :
    Lp.fourierTransformₗᵢ ℝ ℂ (aux_l2Translate t g) =
      aux_fourierPhaseLp t • Lp.fourierTransformₗᵢ ℝ ℂ g := by
  let : (∞ : ℝ≥0∞).HolderTriple 2 2 := ENNReal.HolderTriple.symm
  refine (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ)
    (p := 2) ENNReal.ofNat_ne_top).induction_on
      (p := fun u : Lp (α := ℝ) ℂ 2 volume ↦
        Lp.fourierTransformₗᵢ ℝ ℂ (aux_l2Translate t u) =
          aux_fourierPhaseLp t • Lp.fourierTransformₗᵢ ℝ ℂ u) g ?_ ?_
  · exact isClosed_eq
      ((Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp (aux_continuous_l2Translate t))
      ((aux_l2PhaseMulCLM (aux_fourierPhaseLp t)).continuous.comp
        (Lp.fourierTransformₗᵢ ℝ ℂ).continuous)
  · intro φ
    change Lp.fourierTransformₗᵢ ℝ ℂ (aux_l2Translate t (φ.toLp 2 volume)) =
      aux_fourierPhaseLp t • Lp.fourierTransformₗᵢ ℝ ℂ (φ.toLp 2 volume)
    have htranslate := aux_l2Translate_schwartz_toLp t φ
    rw [htranslate]
    change 𝓕 ((φ.compSubConstCLM ℂ t).toLp 2 volume) =
      aux_fourierPhaseLp t • 𝓕 (φ.toLp 2 volume)
    have hψ := SchwartzMap.toLp_fourier_eq (φ.compSubConstCLM ℂ t)
    have hφ := SchwartzMap.toLp_fourier_eq φ
    rw [hψ, hφ]
    apply Lp.ext (p := 2)
    filter_upwards [Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      (aux_fourierPhaseLp t) ((𝓕 φ).toLp 2 volume),
      aux_coe_fourierPhaseLp_ae t,
      (𝓕 (φ.compSubConstCLM ℂ t)).coeFn_toLp 2 volume,
      (𝓕 φ).coeFn_toLp 2 volume] with ξ hsmul hphase hleft hright
    rw [hleft, hsmul, Pi.smul_apply', hphase, hright]
    exact aux_raw_fourier_schwartz_l2Translate t ξ φ

/-- Scaling the inverse Fourier transform is used in
`dyadicReconstructionAndMultiplierBounds` to identify the frequency
multiplier of the scaled dyadic kernels. -/
lemma aux_scale_inverseFourier (a : ℝ) (ha : 0 < a) (m : ℝ → ℂ) :
    (fun x ↦ (a : ℂ) * inverseFourierTransform m (a * x)) =
      inverseFourierTransform (fun ξ ↦ m (ξ / a)) := by
  ext x
  simp only [inverseFourierTransform]
  change (a : ℂ) * 𝓕⁻ m (a * x) = 𝓕⁻ (fun ξ ↦ m (ξ / a)) x
  rw [Real.fourierInv_eq, Real.fourierInv_eq]
  let g : ℝ → ℂ := fun y ↦
    (𝐞 (inner ℝ (a * y) x) : Circle) • m y
  have hpoint (ξ : ℝ) :
      (𝐞 (inner ℝ ξ x) : Circle) • m (ξ / a) = g (a⁻¹ * ξ) := by
    dsimp [g]
    have hainv : a * (a⁻¹ * ξ) = ξ := by
      field_simp [ha.ne']
    rw [show ξ / a = a⁻¹ * ξ by field_simp [ha.ne'], hainv]
  rw [show (fun ξ : ℝ ↦ (𝐞 (inner ℝ ξ x) : Circle) • m (ξ / a)) =
      (fun ξ ↦ g (a⁻¹ * ξ)) by
        ext ξ
        exact hpoint ξ]
  rw [Measure.integral_comp_mul_left g a⁻¹]
  have habs : |(a⁻¹)⁻¹| = a := by
    rw [inv_inv, abs_of_pos ha]
  rw [habs, Complex.real_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  unfold g
  congr 2
  rw [Real.inner_apply, Real.inner_apply]
  ring

/-- The scaled inverse-Fourier kernel has the expected dilated multiplier;
this is the scaling step in `dyadicReconstructionAndMultiplierBounds`. -/
lemma aux_scaledInverseFourierKernel_eq_inverseFourier_scaled
    (m : ℝ → ℂ) (k : ℕ) :
    aux_scaledInverseFourierKernel m k =
      inverseFourierTransform (fun ξ ↦ m (ξ / (2 : ℝ) ^ k)) := by
  unfold aux_scaledInverseFourierKernel
  simpa only [Complex.ofReal_pow] using
    aux_scale_inverseFourier ((2 : ℝ) ^ k) (by positivity) m

/-- Translation is continuous as a curve in finite `Lᵖ`.  This is the
Bochner-integral input for the finite-exponent convolution estimate in
`dyadicReconstructionAndMultiplierBounds`. -/
lemma aux_continuous_lpTranslation {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    (f : Lp (α := ℝ) ℂ p volume) :
    Continuous (fun t : ℝ => DomAddAct.mk (-t) +ᵥ f) := by
  fun_prop

/-- The kernel-weighted finite-`Lᵖ` translation curve is a.e. strongly
measurable.  This supports the Bochner model of raw convolution. -/
lemma aux_weighted_lpTranslation_aestronglyMeasurable {p : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    (κ : ℝ → ℂ) (f : Lp (α := ℝ) ℂ p volume)
    (hκ : AEStronglyMeasurable κ volume) :
    AEStronglyMeasurable (fun t : ℝ => κ t • (DomAddAct.mk (-t) +ᵥ f)) volume := by
  exact continuous_smul.comp_aestronglyMeasurable₂ hκ
    (aux_continuous_lpTranslation f).aestronglyMeasurable

/-- An `L¹` kernel makes its finite-`Lᵖ` translation curve Bochner
integrable.  This supplies the Banach-valued integral behind Young's
inequality for the raw convolution. -/
lemma aux_weighted_lpTranslation_integrable {p : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (p ≠ ∞)] (κ : ℝ → ℂ) (f : Lp (α := ℝ) ℂ p volume)
    (hκ : Integrable κ volume) :
    Integrable (fun t : ℝ => κ t • (DomAddAct.mk (-t) +ᵥ f)) volume := by
  apply Integrable.mono' (hκ.norm.smul_const ‖f‖)
    (aux_weighted_lpTranslation_aestronglyMeasurable κ f hκ.aestronglyMeasurable)
  filter_upwards with t
  rw [norm_smul, DomAddAct.norm_vadd_Lp]
  simp only [smul_eq_mul]
  exact le_rfl

/-- The norm of the Bochner convolution model obeys the finite-`Lᵖ` Young
bound.  The raw-function bridge is proved below. -/
lemma aux_norm_integral_weighted_lpTranslation_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (p ≠ ∞)] (κ : ℝ → ℂ) (f : Lp (α := ℝ) ℂ p volume)
    (hκ : Integrable κ volume) :
    ‖∫ t : ℝ, κ t • (DomAddAct.mk (-t) +ᵥ f) ∂volume‖ ≤
      (eLpNorm κ 1 volume).toReal * ‖f‖ := by
  calc
    ‖∫ t : ℝ, κ t • (DomAddAct.mk (-t) +ᵥ f) ∂volume‖ ≤
        ∫ t : ℝ, ‖κ t • (DomAddAct.mk (-t) +ᵥ f)‖ ∂volume :=
      norm_integral_le_integral_norm _
    _ = ∫ t : ℝ, ‖κ t‖ * ‖f‖ ∂volume := by
      apply integral_congr_ae
      filter_upwards with t
      rw [norm_smul, DomAddAct.norm_vadd_Lp]
    _ = (∫ t : ℝ, ‖κ t‖ ∂volume) * ‖f‖ :=
      integral_mul_const ‖f‖ (fun t : ℝ => ‖κ t‖)
    _ = (eLpNorm κ 1 volume).toReal * ‖f‖ := by
      rw [integral_norm_eq_lintegral_enorm hκ.aestronglyMeasurable,
        ← eLpNorm_one_eq_lintegral_enorm]

/-- The Banach-valued Young bound expressed with the original function
representative and `eLpNorm`. -/
lemma aux_norm_integral_weighted_lpTranslation_le_eLpNorm {p : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (p ≠ ∞)] (κ f : ℝ → ℂ)
    (hκ : Integrable κ volume) (hf : MemLp f p volume) :
    ‖∫ t : ℝ, κ t • (DomAddAct.mk (-t) +ᵥ hf.toLp f) ∂volume‖ ≤
      (eLpNorm κ 1 volume).toReal * (eLpNorm f p volume).toReal := by
  simpa only [Lp.norm_toLp] using
    aux_norm_integral_weighted_lpTranslation_le κ (hf.toLp f) hκ

/-- The real-valued `Lᵖ` class represented by the pointwise norm of a
complex `Lᵖ` class.  It is used to test local integrability of convolution. -/
noncomputable def aux_normLp {p : ℝ≥0∞} (g : Lp (α := ℝ) ℂ p volume) :
    Lp (α := ℝ) ℝ p volume :=
  ((Lp.memLp g).norm).toLp fun x => ‖g x‖

/-- Taking the pointwise norm preserves the `Lᵖ` norm of the chosen class. -/
lemma aux_norm_aux_normLp {p : ℝ≥0∞} (g : Lp (α := ℝ) ℂ p volume) :
    ‖aux_normLp g‖ = ‖g‖ := by
  rw [aux_normLp, Lp.norm_toLp, eLpNorm_norm, Lp.norm_def]

/-- Pairing the norm class with a finite-measure indicator computes its local
`L¹` norm.  This makes the Fubini hypotheses for raw convolution explicit. -/
lemma aux_lpPairing_indicator_normLp_eq_setIntegral {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (s : Set ℝ) (hs : MeasurableSet s) (hμs : volume s ≠ ∞)
    (g : Lp (α := ℝ) ℂ p volume) :
    let q := ENNReal.conjExponent p
    letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
    ((ContinuousLinearMap.lpPairing volume q p (ContinuousLinearMap.mul ℝ ℝ))
      (indicatorConstLp q hs hμs (1 : ℝ))) (aux_normLp g) = ∫ x in s, ‖g x‖ := by
  dsimp only
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  rw [← integral_indicator hs]
  simp only [aux_normLp]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := ENNReal.conjExponent p)
    (hs := hs) (hμs := hμs) (c := (1 : ℝ)),
    MemLp.coeFn_toLp ((Lp.memLp g).norm)] with x hx hnorm
  rw [hx, hnorm]
  by_cases hxs : x ∈ s <;> simp [Set.indicator, hxs]

/-- A translate of an `Lᵖ` function has uniformly bounded local `L¹` norm on
every finite-measure set.  The bound is expressed through the Hölder pairing
with the set indicator. -/
lemma aux_local_L1_bound_lpTranslation {p : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (p ≠ ∞)] [Fact (1 ≤ ENNReal.conjExponent p)]
    (f : ℝ → ℂ) (hf : MemLp f p volume)
    (s : Set ℝ) (hs : MeasurableSet s) (hμs : volume s ≠ ∞) (t : ℝ) :
    ∫ x in s, ‖f (x - t)‖ ≤
      ‖(ContinuousLinearMap.lpPairing volume (ENNReal.conjExponent p) p
        (ContinuousLinearMap.mul ℝ ℝ))
        (indicatorConstLp (ENNReal.conjExponent p) hs hμs (1 : ℝ))‖ * ‖hf.toLp f‖ := by
  let g : Lp (α := ℝ) ℂ p volume := DomAddAct.mk (-t) +ᵥ hf.toLp f
  have hpairs :
      ((ContinuousLinearMap.lpPairing volume (ENNReal.conjExponent p) p
        (ContinuousLinearMap.mul ℝ ℝ))
        (indicatorConstLp (ENNReal.conjExponent p) hs hμs (1 : ℝ))) (aux_normLp g) =
        ∫ x in s, ‖g x‖ :=
    aux_lpPairing_indicator_normLp_eq_setIntegral s hs hμs g
  have htrans : (g : ℝ → ℂ) =ᵐ[volume] fun x ↦ f (x - t) := by
    have h0 := DomAddAct.vadd_Lp_ae_eq
      (DomAddAct.mk (-t) : ℝᵈᵃᵃ) hf.toLp
    have h1 : (g : ℝ → ℂ) =ᵐ[volume] fun x ↦ (hf.toLp : ℝ → ℂ) (x - t) := by
      simpa [g, sub_eq_add_neg, add_comm] using h0
    have hshift : MeasurePreserving (fun x : ℝ ↦ x - t) volume volume := by
      simpa [sub_eq_add_neg, add_comm] using measurePreserving_add_left volume (-t)
    exact h1.trans (hf.coeFn_toLp.comp_tendsto hshift.quasiMeasurePreserving.tendsto_ae)
  have hset : (∫ x in s, ‖f (x - t)‖) = ∫ x in s, ‖g x‖ := by
    apply setIntegral_congr_ae hs
    filter_upwards [htrans] with x hx hxs
    exact (congrArg norm hx).symm
  rw [hset, ← hpairs]
  calc
    ((ContinuousLinearMap.lpPairing volume (ENNReal.conjExponent p) p
        (ContinuousLinearMap.mul ℝ ℝ))
        (indicatorConstLp (ENNReal.conjExponent p) hs hμs (1 : ℝ))) (aux_normLp g) ≤
        ‖((ContinuousLinearMap.lpPairing volume (ENNReal.conjExponent p) p
          (ContinuousLinearMap.mul ℝ ℝ))
          (indicatorConstLp (ENNReal.conjExponent p) hs hμs (1 : ℝ))) (aux_normLp g)‖ :=
      le_abs_self _
    _ ≤ ‖(ContinuousLinearMap.lpPairing volume (ENNReal.conjExponent p) p
          (ContinuousLinearMap.mul ℝ ℝ))
          (indicatorConstLp (ENNReal.conjExponent p) hs hμs (1 : ℝ))‖ * ‖aux_normLp g‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖(ContinuousLinearMap.lpPairing volume (ENNReal.conjExponent p) p
          (ContinuousLinearMap.mul ℝ ℝ))
          (indicatorConstLp (ENNReal.conjExponent p) hs hμs (1 : ℝ))‖ * ‖hf.toLp f‖ := by
      rw [aux_norm_aux_normLp, DomAddAct.norm_vadd_Lp]

/-- The convolution integrand is integrable on a finite spatial set times the
kernel variable.  This is the local Fubini input for the raw Young inequality. -/
lemma aux_local_convolution_integrable_prod {p : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (p ≠ ∞)] (κ f : ℝ → ℂ) (hκ : Integrable κ volume)
    (hf : MemLp f p volume) (s : Set ℝ) (hs : MeasurableSet s)
    (hμs : volume s < ∞) :
    Integrable (fun z : ℝ × ℝ ↦ κ z.2 * f (z.1 - z.2))
      ((volume.restrict s).prod volume) := by
  let : Fact (1 ≤ ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p⟩
  let : IsFiniteMeasure (volume.restrict s) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hμs⟩
  have hF0 : AEStronglyMeasurable
      (fun z : ℝ × ℝ ↦ κ z.2 * f (z.1 - z.2)) (volume.prod volume) := by
    simpa using hκ.aestronglyMeasurable.convolution_integrand
      (ContinuousLinearMap.mul ℝ ℂ) hf.aestronglyMeasurable
  have hF : AEStronglyMeasurable
      (fun z : ℝ × ℝ ↦ κ z.2 * f (z.1 - z.2)) ((volume.restrict s).prod volume) := by
    have hprod_eq : ((volume : Measure ℝ).restrict s).prod (volume : Measure ℝ) =
        ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (s ×ˢ Set.univ) := by
      simpa using (Measure.prod_restrict (μ := (volume : Measure ℝ))
        (ν := (volume : Measure ℝ)) s Set.univ)
    rw [hprod_eq]
    exact hF0.restrict
  refine (integrable_prod_iff' hF).2 ⟨?_, ?_⟩
  · exact Eventually.of_forall fun t ↦ by
      have hshift : MeasurePreserving (fun x : ℝ ↦ x - t) volume volume := by
        simpa [sub_eq_add_neg, add_comm] using measurePreserving_add_left volume (-t)
      have hft : MemLp (f ∘ fun x : ℝ ↦ x - t) p volume :=
        hf.comp_measurePreserving hshift
      have hint : Integrable (f ∘ fun x : ℝ ↦ x - t) (volume.restrict s) :=
        (hft.restrict s).integrable Fact.out
      simpa [Function.comp_apply] using hint.const_mul (κ t)
  · let C : ℝ :=
      ‖(ContinuousLinearMap.lpPairing volume (ENNReal.conjExponent p) p
        (ContinuousLinearMap.mul ℝ ℝ))
        (indicatorConstLp (ENNReal.conjExponent p) hs hμs.ne (1 : ℝ))‖ * ‖hf.toLp f‖
    have hmeas : AEStronglyMeasurable
        (fun t : ℝ ↦ ∫ x in s, ‖κ t * f (x - t)‖) volume := by
      simpa using hF.prod_swap.norm.integral_prod_right'
    have hmajor : Integrable (fun t : ℝ ↦ ‖κ t‖ * C) volume :=
      hκ.norm.mul_const C
    refine hmajor.mono' hmeas (Eventually.of_forall fun t ↦ ?_)
    change ‖∫ x in s, ‖κ t * f (x - t)‖‖ ≤ ‖κ t‖ * C
    rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
    calc
      ∫ x in s, ‖κ t * f (x - t)‖ = ∫ x in s, ‖κ t‖ * ‖f (x - t)‖ := by
        congr 1
        funext x
        exact norm_mul _ _
      _ = ‖κ t‖ * ∫ x in s, ‖f (x - t)‖ := by
        exact integral_const_mul ‖κ t‖ (fun x : ℝ ↦ ‖f (x - t)‖)
      _ ≤ ‖κ t‖ * C := by
        exact mul_le_mul_of_nonneg_left
          (by simpa [C] using aux_local_L1_bound_lpTranslation f hf s hs hμs.ne t)
          (norm_nonneg _)

/-- Pairing a complex finite-`Lᵖ` class with a finite-measure indicator gives
its set integral.  This identifies the Bochner convolution model locally. -/
lemma aux_lpPairing_indicator_eq_setIntegral {p : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (1 ≤ ENNReal.conjExponent p)]
    (s : Set ℝ) (hs : MeasurableSet s) (hμs : volume s ≠ ∞)
    (g : Lp (α := ℝ) ℂ p volume) :
    ((ContinuousLinearMap.lpPairing volume (ENNReal.conjExponent p) p
      (ContinuousLinearMap.mul ℂ ℂ))
      (indicatorConstLp (ENNReal.conjExponent p) hs hμs (1 : ℂ))) g = ∫ x in s, g x := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := ENNReal.conjExponent p)
    (hs := hs) (hμs := hμs) (c := (1 : ℂ))] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [Set.indicator, hxs]

/-- The selected finite-`Lᵖ` translation representative agrees almost
everywhere with ordinary spatial translation. -/
lemma aux_coe_lpTranslation_ae {p : ℝ≥0∞}
    (f : ℝ → ℂ) (hf : MemLp f p volume) (t : ℝ) :
    ((DomAddAct.mk (-t) +ᵥ hf.toLp f : Lp (α := ℝ) ℂ p volume) : ℝ → ℂ) =ᵐ[volume]
      fun x ↦ f (x - t) := by
  have h0 := DomAddAct.vadd_Lp_ae_eq
    (DomAddAct.mk (-t) : ℝᵈᵃᵃ) hf.toLp
  have h1 :
      ((DomAddAct.mk (-t) +ᵥ hf.toLp f : Lp (α := ℝ) ℂ p volume) : ℝ → ℂ) =ᵐ[volume]
      fun x ↦ (hf.toLp : ℝ → ℂ) (x - t) := by
    simpa [sub_eq_add_neg, add_comm] using h0
  have hshift : MeasurePreserving (fun x : ℝ ↦ x - t) volume volume := by
    simpa [sub_eq_add_neg, add_comm] using measurePreserving_add_left volume (-t)
  exact h1.trans (hf.coeFn_toLp.comp_tendsto hshift.quasiMeasurePreserving.tendsto_ae)

/-- The indicator pairing of a translated `Lᵖ` class is its usual translated
set integral. -/
lemma aux_lpPairing_indicator_lpTranslation_eq_setIntegral {p : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ ENNReal.conjExponent p)]
    (f : ℝ → ℂ) (hf : MemLp f p volume)
    (s : Set ℝ) (hs : MeasurableSet s) (hμs : volume s ≠ ∞) (t : ℝ) :
    ((ContinuousLinearMap.lpPairing volume (ENNReal.conjExponent p) p
      (ContinuousLinearMap.mul ℂ ℂ))
      (indicatorConstLp (ENNReal.conjExponent p) hs hμs (1 : ℂ)))
      (DomAddAct.mk (-t) +ᵥ hf.toLp f) = ∫ x in s, f (x - t) := by
  rw [aux_lpPairing_indicator_eq_setIntegral s hs hμs]
  exact setIntegral_congr_ae hs
    ((aux_coe_lpTranslation_ae f hf t).mono fun _ hx _ ↦ hx)

/-- Raw convolution agrees almost everywhere with the Bochner integral of
kernel-weighted translations in finite `Lᵖ`.  This is the bridge from the
project's pointwise convolution definition to the Banach-space Young bound. -/
theorem aux_convolution_ae_eq_lpBochner {p : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    (κ f : ℝ → ℂ) (hκ : Integrable κ volume) (hf : MemLp f p volume) :
    (fun x ↦ aux_convolution κ f x) =ᵐ[volume]
      ((∫ t : ℝ, κ t • (DomAddAct.mk (-t) +ᵥ hf.toLp f) :
        Lp (α := ℝ) ℂ p volume) : ℝ → ℂ) := by
  let : Fact (1 ≤ ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p⟩
  let H : Lp (α := ℝ) ℂ p volume :=
    ∫ t : ℝ, κ t • (DomAddAct.mk (-t) +ᵥ hf.toLp f)
  have hB : Integrable (fun t : ℝ ↦ κ t •
      (DomAddAct.mk (-t) +ᵥ hf.toLp f : Lp (α := ℝ) ℂ p volume)) volume :=
    aux_weighted_lpTranslation_integrable κ (hf.toLp f) hκ
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s hs hμs
    have hF := aux_local_convolution_integrable_prod κ f hκ hf s hs hμs
    change Integrable (fun x : ℝ ↦ aux_convolution κ f x) (volume.restrict s)
    change Integrable (fun x : ℝ ↦ ∫ t : ℝ, κ t * f (x - t)) (volume.restrict s)
    exact hF.integral_prod_left
  · intro s hs hμs
    let : IsFiniteMeasure (volume.restrict s) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using hμs⟩
    change Integrable (H : ℝ → ℂ) (volume.restrict s)
    exact ((Lp.memLp H).restrict s).integrable Fact.out
  · intro s hs hμs
    have hF := aux_local_convolution_integrable_prod κ f hκ hf s hs hμs
    let L : Lp (α := ℝ) ℂ p volume →L[ℂ] ℂ :=
      (ContinuousLinearMap.lpPairing volume (ENNReal.conjExponent p) p
        (ContinuousLinearMap.mul ℂ ℂ))
        (indicatorConstLp (ENNReal.conjExponent p) hs hμs.ne (1 : ℂ))
    have hL_trans (t : ℝ) : L (DomAddAct.mk (-t) +ᵥ hf.toLp f) =
        ∫ x in s, f (x - t) := by
      exact aux_lpPairing_indicator_lpTranslation_eq_setIntegral f hf s hs hμs.ne t
    have hL_smul (t : ℝ) : L (κ t • (DomAddAct.mk (-t) +ᵥ hf.toLp f)) =
        ∫ x in s, κ t * f (x - t) := by
      calc
        L (κ t • (DomAddAct.mk (-t) +ᵥ hf.toLp f)) =
            κ t * L (DomAddAct.mk (-t) +ᵥ hf.toLp f) := L.map_smul _ _
        _ = κ t * ∫ x in s, f (x - t) := by rw [hL_trans]
        _ = ∫ x in s, κ t * f (x - t) :=
          (integral_const_mul (κ t) (fun x : ℝ ↦ f (x - t))).symm
    have hL_H : L H = ∫ x in s, H x := by
      exact aux_lpPairing_indicator_eq_setIntegral s hs hμs.ne H
    have hcomm := L.integral_comp_comm hB
    have hswap := integral_integral_swap
      (f := fun x : ℝ ↦ fun t : ℝ ↦ κ t * f (x - t)) hF
    change ∫ x in s, aux_convolution κ f x = ∫ x in s, H x
    change (∫ x in s, ∫ t : ℝ, κ t * f (x - t)) = ∫ x in s, H x
    calc
      ∫ x in s, ∫ t : ℝ, κ t * f (x - t) =
          ∫ t : ℝ, ∫ x in s, κ t * f (x - t) := hswap
      _ = ∫ t : ℝ, L (κ t • (DomAddAct.mk (-t) +ᵥ hf.toLp f)) := by
        exact integral_congr_ae (Eventually.of_forall fun t ↦ (hL_smul t).symm)
      _ = L (∫ t : ℝ, κ t • (DomAddAct.mk (-t) +ᵥ hf.toLp f)) := hcomm
      _ = L H := by rfl
      _ = ∫ x in s, H x := hL_H

/-- Raw convolution of an `L¹` kernel with a finite-`Lᵖ` function is itself
in `Lᵖ`.  This is the membership part of the finite Young inequality. -/
theorem aux_convolution_memLp_of_memLp_one {p : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    (κ f : ℝ → ℂ) (hκ : Integrable κ volume) (hf : MemLp f p volume) :
    MemLp (aux_convolution κ f) p volume := by
  let H : Lp (α := ℝ) ℂ p volume :=
    ∫ t : ℝ, κ t • (DomAddAct.mk (-t) +ᵥ hf.toLp f)
  have hbridge : (fun x ↦ aux_convolution κ f x) =ᵐ[volume] (H : ℝ → ℂ) := by
    simpa [H] using aux_convolution_ae_eq_lpBochner κ f hκ hf
  exact (Lp.memLp H).ae_eq hbridge.symm

/-- Finite-exponent Young inequality for the project's raw convolution,
expressed using an integrable `L¹` kernel. -/
theorem aux_eLpNorm_aux_convolution_le_of_integrable {p : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    (κ f : ℝ → ℂ) (hκ : Integrable κ volume) (hf : MemLp f p volume) :
    eLpNorm (aux_convolution κ f) p volume ≤
      eLpNorm κ 1 volume * eLpNorm f p volume := by
  let H : Lp (α := ℝ) ℂ p volume :=
    ∫ t : ℝ, κ t • (DomAddAct.mk (-t) +ᵥ hf.toLp f)
  have hbridge : (fun x ↦ aux_convolution κ f x) =ᵐ[volume] (H : ℝ → ℂ) := by
    simpa [H] using aux_convolution_ae_eq_lpBochner κ f hκ hf
  have hraw : MemLp (aux_convolution κ f) p volume :=
    aux_convolution_memLp_of_memLp_one κ f hκ hf
  have hκlp : MemLp κ 1 volume := memLp_one_iff_integrable.mpr hκ
  apply (ENNReal.toReal_le_toReal hraw.eLpNorm_ne_top
    (ENNReal.mul_ne_top hκlp.eLpNorm_ne_top hf.eLpNorm_ne_top)).mp
  calc
    (eLpNorm (aux_convolution κ f) p volume).toReal =
        (eLpNorm (H : ℝ → ℂ) p volume).toReal := by
      rw [eLpNorm_congr_ae hbridge]
    _ = ‖H‖ := (Lp.norm_def H).symm
    _ ≤ (eLpNorm κ 1 volume).toReal * (eLpNorm f p volume).toReal := by
      simpa [H] using aux_norm_integral_weighted_lpTranslation_le_eLpNorm κ f hκ hf
    _ = (eLpNorm κ 1 volume * eLpNorm f p volume).toReal := by
      rw [ENNReal.toReal_mul]

/-- Finite-exponent Young inequality for raw convolution with a kernel given
as an `L¹` function. -/
theorem aux_eLpNorm_aux_convolution_le_of_memLp_one {p : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    (κ f : ℝ → ℂ) (hκ : MemLp κ 1 volume) (hf : MemLp f p volume) :
    eLpNorm (aux_convolution κ f) p volume ≤
      eLpNorm κ 1 volume * eLpNorm f p volume :=
  aux_eLpNorm_aux_convolution_le_of_integrable κ f (memLp_one_iff_integrable.mp hκ) hf

/-- The `L²` indicator pairing used to identify the pointwise representative
of the phase Bochner integral in `dyadicReconstructionAndMultiplierBounds`
and `\label{lem:dyadic-reconstruction}`. -/
lemma aux_l2Pairing_indicator_eq_setIntegral (s : Set ℝ) (hs : MeasurableSet s)
    (hμs : volume s ≠ ∞) (g : Lp (α := ℝ) ℂ 2 volume) :
    ((ContinuousLinearMap.lpPairing volume 2 2 (ContinuousLinearMap.mul ℂ ℂ))
      (indicatorConstLp 2 hs hμs (1 : ℂ))) g = ∫ x in s, g x := by
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  rw [← integral_indicator hs]
  refine integral_congr_ae ?_
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs)
    (c := (1 : ℂ))] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [Set.indicator, hxs]

/-- Pairing a phase-modulated `L²` class with an indicator recovers the
corresponding raw set integral.  This is a Fubini input for
`dyadicReconstructionAndMultiplierBounds` and
`\label{lem:dyadic-reconstruction}`. -/
lemma aux_l2Pairing_indicator_phase_eq_setIntegral
    (s : Set ℝ) (hs : MeasurableSet s) (hμs : volume s ≠ ∞)
    (t : ℝ) (G : Lp (α := ℝ) ℂ 2 volume) :
    ((ContinuousLinearMap.lpPairing volume 2 2 (ContinuousLinearMap.mul ℂ ℂ))
      (indicatorConstLp 2 hs hμs (1 : ℂ)))
      (aux_fourierPhaseLp t • G) =
      ∫ ξ in s, aux_fourierPhase t ξ * G ξ := by
  let : (∞ : ℝ≥0∞).HolderTriple 2 2 := ENNReal.HolderTriple.symm
  rw [aux_l2Pairing_indicator_eq_setIntegral s hs hμs]
  apply setIntegral_congr_ae hs
  filter_upwards [Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      (aux_fourierPhaseLp t) G,
    aux_coe_fourierPhaseLp_ae t] with ξ hsmul hphase
  rw [hsmul, Pi.smul_apply', hphase]
  intro _
  simp only [smul_eq_mul]

/-- The phase convolution integrand is integrable on every finite frequency
set.  This supplies the local Fubini hypothesis in the Fourier multiplier
bridge for `dyadicReconstructionAndMultiplierBounds` and
`\label{lem:dyadic-reconstruction}`. -/
lemma aux_l2PhaseProduct_integrable_on
    (κ : ℝ → ℂ) (hκ : Integrable κ)
    (G : Lp (α := ℝ) ℂ 2 volume)
    (s : Set ℝ) (_hs : MeasurableSet s) (hμs : volume s < ∞) :
    Integrable (fun p : ℝ × ℝ ↦
      κ p.2 * aux_fourierPhase p.2 p.1 * G p.1)
      ((volume.restrict s).prod volume) := by
  let : IsFiniteMeasure (volume.restrict s) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hμs⟩
  have hG : Integrable (G : ℝ → ℂ) (volume.restrict s) :=
    ((Lp.memLp G).restrict s).integrable (by norm_num)
  have hbase : Integrable (fun p : ℝ × ℝ ↦ G p.1 * κ p.2)
      ((volume.restrict s).prod volume) :=
    Integrable.mul_prod (μ := volume.restrict s) (ν := volume) hG hκ
  have hphase : Continuous (fun p : ℝ × ℝ ↦ aux_fourierPhase p.2 p.1) := by
    exact continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp ((continuous_snd.neg).mul continuous_fst))
  refine hbase.mono ?_ (Eventually.of_forall fun p ↦ ?_)
  · convert hphase.aestronglyMeasurable.mul hbase.aestronglyMeasurable using 1
    ext p
    simp only [Pi.mul_apply]
    ring
  · rw [norm_mul, norm_mul, aux_norm_fourierPhase]
    rw [norm_mul, mul_one]
    exact le_of_eq (mul_comm _ _)

/-- The Fourier-side Bochner integral of phase-modulated `L²` functions.
This definition is used to turn convolution into multiplication in
`dyadicReconstructionAndMultiplierBounds` and
`\label{lem:dyadic-reconstruction}`. -/
noncomputable def aux_l2PhaseIntegral (κ : ℝ → ℂ) (G : Lp (α := ℝ) ℂ 2 volume) :
    Lp (α := ℝ) ℂ 2 volume :=
  ∫ t : ℝ, κ t • (aux_fourierPhaseLp t • G)

/-- The selected representative of the Fourier-side phase Bochner integral
is almost everywhere its raw iterated integral.  This is the local-Fubini
step for `dyadicReconstructionAndMultiplierBounds` and
`\label{lem:dyadic-reconstruction}`. -/
lemma aux_l2PhaseIntegral_ae_eq_raw
    (κ : ℝ → ℂ) (hκ : Integrable κ)
    (G : Lp (α := ℝ) ℂ 2 volume)
    (hB : Integrable (fun t : ℝ ↦ κ t • (aux_fourierPhaseLp t • G)) volume) :
    (aux_l2PhaseIntegral κ G : ℝ → ℂ) =ᵐ[volume]
      fun ξ ↦ ∫ t : ℝ, κ t * aux_fourierPhase t ξ * G ξ := by
  let H : Lp (α := ℝ) ℂ 2 volume := aux_l2PhaseIntegral κ G
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s hs hμs
    let : IsFiniteMeasure (volume.restrict s) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using hμs⟩
    change IntegrableOn (H : ℝ → ℂ) s volume
    exact ((Lp.memLp H).restrict s).integrable (by norm_num)
  · intro s hs hμs
    have hF := aux_l2PhaseProduct_integrable_on κ hκ G s hs hμs
    change IntegrableOn (fun ξ : ℝ ↦ ∫ t : ℝ,
      κ t * aux_fourierPhase t ξ * G ξ) s volume
    exact hF.integral_prod_left
  · intro s hs hμs
    have hF := aux_l2PhaseProduct_integrable_on κ hκ G s hs hμs
    let L : Lp (α := ℝ) ℂ 2 volume →L[ℂ] ℂ :=
      (ContinuousLinearMap.lpPairing volume 2 2 (ContinuousLinearMap.mul ℂ ℂ))
        (indicatorConstLp 2 hs hμs.ne (1 : ℂ))
    have hL_phase (t : ℝ) : L (aux_fourierPhaseLp t • G) =
        ∫ ξ in s, aux_fourierPhase t ξ * G ξ := by
      exact aux_l2Pairing_indicator_phase_eq_setIntegral s hs hμs.ne t G
    have hL_smul (t : ℝ) : L (κ t • (aux_fourierPhaseLp t • G)) =
        ∫ ξ in s, κ t * aux_fourierPhase t ξ * G ξ := by
      calc
        L (κ t • (aux_fourierPhaseLp t • G)) =
            κ t * L (aux_fourierPhaseLp t • G) := L.map_smul _ _
        _ = κ t * ∫ ξ in s, aux_fourierPhase t ξ * G ξ := by rw [hL_phase]
        _ = ∫ ξ in s, κ t * (aux_fourierPhase t ξ * G ξ) := by
          exact (integral_const_mul (κ t)
            (fun ξ : ℝ ↦ aux_fourierPhase t ξ * G ξ)).symm
        _ = ∫ ξ in s, κ t * aux_fourierPhase t ξ * G ξ := by
          congr 1
          funext ξ
          ring
    have hL_H : L H = ∫ ξ in s, H ξ :=
      aux_l2Pairing_indicator_eq_setIntegral s hs hμs.ne H
    have hcomm := L.integral_comp_comm hB
    have hswap := integral_integral_swap
      (f := fun ξ : ℝ ↦ fun t : ℝ ↦
        κ t * aux_fourierPhase t ξ * G ξ) hF
    change (∫ ξ in s, H ξ) = (∫ ξ in s, ∫ t : ℝ,
      κ t * aux_fourierPhase t ξ * G ξ)
    calc
      ∫ ξ in s, H ξ = L H := hL_H.symm
      _ = L (∫ t : ℝ, κ t • (aux_fourierPhaseLp t • G)) := by rfl
      _ = ∫ t : ℝ, L (κ t • (aux_fourierPhaseLp t • G)) := hcomm.symm
      _ = ∫ t : ℝ, ∫ ξ in s, κ t * aux_fourierPhase t ξ * G ξ := by
        exact integral_congr_ae (Eventually.of_forall fun t ↦ hL_smul t)
      _ = ∫ ξ in s, ∫ t : ℝ, κ t * aux_fourierPhase t ξ * G ξ := hswap.symm

/-- The raw iterated phase integral is multiplication by the raw Fourier
transform of the kernel.  This algebraic Fourier calculation feeds
`dyadicReconstructionAndMultiplierBounds` and
`\label{lem:dyadic-reconstruction}`. -/
lemma aux_raw_l2PhaseIntegral_eq_fourier_mul
    (κ : ℝ → ℂ) (G : Lp (α := ℝ) ℂ 2 volume) (ξ : ℝ) :
    (∫ t : ℝ, κ t * aux_fourierPhase t ξ * G ξ) =
      (𝓕 κ) ξ * G ξ := by
  rw [Real.fourier_eq]
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with t
  change κ t * (Real.fourierChar ((-t) * ξ) : ℂ) * G ξ =
    (𝐞 (-inner ℝ t ξ) : Circle) • κ t * G ξ
  rw [Circle.smul_def]
  have harg : -inner ℝ t ξ = (-t) * ξ := by
    simp only [Real.inner_apply]
    ring
  rw [harg]
  ring

/-- The Fourier-side phase Bochner integral is almost everywhere the raw
Fourier multiplier.  This is the frequency-side bridge for
`dyadicReconstructionAndMultiplierBounds` and
`\label{lem:dyadic-reconstruction}`. -/
lemma aux_l2PhaseIntegral_ae_eq_fourier_mul
    (κ : ℝ → ℂ) (hκ : Integrable κ)
    (G : Lp (α := ℝ) ℂ 2 volume)
    (hB : Integrable (fun t : ℝ ↦ κ t • (aux_fourierPhaseLp t • G)) volume) :
    (aux_l2PhaseIntegral κ G : ℝ → ℂ) =ᵐ[volume]
      fun ξ ↦ (𝓕 κ) ξ * G ξ := by
  filter_upwards [aux_l2PhaseIntegral_ae_eq_raw κ hκ G hB] with ξ hξ
  rw [hξ]
  exact aux_raw_l2PhaseIntegral_eq_fourier_mul κ G ξ

/-- The phase-modulated Fourier translation curve is integrable whenever
the corresponding spatial translation curve is integrable.  This transfers
the Bochner input for `dyadicReconstructionAndMultiplierBounds` and
`\label{lem:dyadic-reconstruction}`. -/
lemma aux_integrable_l2PhaseIntegral_of_l2Translate
    (κ : ℝ → ℂ) (g : Lp (α := ℝ) ℂ 2 volume)
    (hB : Integrable (fun t : ℝ ↦ κ t • aux_l2Translate t g) volume) :
    Integrable (fun t : ℝ ↦ κ t •
      (aux_fourierPhaseLp t • Lp.fourierTransformₗᵢ ℝ ℂ g)) volume := by
  let F := Lp.fourierTransformₗᵢ ℝ ℂ
  have hmap : Integrable (fun t : ℝ ↦
      (FourierTransform.fourierCLM ℂ (Lp (α := ℝ) ℂ 2 volume))
        (κ t • aux_l2Translate t g)) volume :=
    (FourierTransform.fourierCLM ℂ (Lp (α := ℝ) ℂ 2 volume)).integrable_comp hB
  change Integrable (fun t : ℝ ↦ F (κ t • aux_l2Translate t g)) volume at hmap
  apply hmap.congr
  filter_upwards with t
  calc
    F (κ t • aux_l2Translate t g) = κ t • F (aux_l2Translate t g) :=
      F.map_smul _ _
    _ = κ t • (aux_fourierPhaseLp t • F g) := by
      rw [aux_l2Fourier_l2Translate]

/-- Fourier transform of the `L²` Bochner convolution model is the expected
raw multiplier almost everywhere.  This combines the translation identity
with phase Fubini for `dyadicReconstructionAndMultiplierBounds` and
`\label{lem:dyadic-reconstruction}`. -/
lemma aux_fourier_l2Bochner_ae_eq_multiplier
    (κ : ℝ → ℂ) (hκ : Integrable κ)
    (g : Lp (α := ℝ) ℂ 2 volume)
    (hB : Integrable (fun t : ℝ ↦ κ t • aux_l2Translate t g) volume) :
    (Lp.fourierTransformₗᵢ ℝ ℂ
      (∫ t : ℝ, κ t • aux_l2Translate t g) : ℝ → ℂ) =ᵐ[volume]
      fun ξ ↦ (𝓕 κ) ξ * (Lp.fourierTransformₗᵢ ℝ ℂ g) ξ := by
  have hphase : Integrable (fun t : ℝ ↦ κ t •
      (aux_fourierPhaseLp t • Lp.fourierTransformₗᵢ ℝ ℂ g)) volume :=
    aux_integrable_l2PhaseIntegral_of_l2Translate κ g hB
  have hFourier : Lp.fourierTransformₗᵢ ℝ ℂ
      (∫ t : ℝ, κ t • aux_l2Translate t g) =
      aux_l2PhaseIntegral κ (Lp.fourierTransformₗᵢ ℝ ℂ g) := by
    change (FourierTransform.fourierCLM ℂ (Lp (α := ℝ) ℂ 2 volume))
        (∫ t : ℝ, κ t • aux_l2Translate t g) = _
    calc
      (FourierTransform.fourierCLM ℂ (Lp (α := ℝ) ℂ 2 volume))
          (∫ t : ℝ, κ t • aux_l2Translate t g) =
          ∫ t : ℝ, (FourierTransform.fourierCLM ℂ (Lp (α := ℝ) ℂ 2 volume))
            (κ t • aux_l2Translate t g) :=
        ((FourierTransform.fourierCLM ℂ (Lp (α := ℝ) ℂ 2 volume)).integral_comp_comm hB).symm
      _ = ∫ t : ℝ, κ t •
          (aux_fourierPhaseLp t • Lp.fourierTransformₗᵢ ℝ ℂ g) := by
        apply integral_congr_ae
        filter_upwards with t
        calc
          Lp.fourierTransformₗᵢ ℝ ℂ (κ t • aux_l2Translate t g) =
              κ t • Lp.fourierTransformₗᵢ ℝ ℂ (aux_l2Translate t g) :=
            (Lp.fourierTransformₗᵢ ℝ ℂ).map_smul _ _
          _ = κ t • (aux_fourierPhaseLp t •
              Lp.fourierTransformₗᵢ ℝ ℂ g) := by
            rw [aux_l2Fourier_l2Translate]
      _ = aux_l2PhaseIntegral κ (Lp.fourierTransformₗᵢ ℝ ℂ g) := rfl
  rw [hFourier]
  exact aux_l2PhaseIntegral_ae_eq_fourier_mul κ hκ
    (Lp.fourierTransformₗᵢ ℝ ℂ g) hphase

/-- Raw convolution by an integrable kernel has the expected `L²` Fourier
multiplier representative.  This joins the raw Young bridge to the Fourier
phase bridge for `dyadicReconstructionAndMultiplierBounds` and
`\label{lem:dyadic-reconstruction}`. -/
lemma aux_l2Fourier_aux_convolution_ae_eq_multiplier
    (κ f : ℝ → ℂ) (hκ : Integrable κ volume) (hf : MemLp f 2 volume) :
    aux_l2Fourier (aux_convolution κ f) =ᵐ[volume]
      fun ξ ↦ (𝓕 κ) ξ * aux_l2Fourier f ξ := by
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hconv : MemLp (aux_convolution κ f) 2 volume :=
    aux_convolution_memLp_of_memLp_one κ f hκ hf
  have hraw : (fun x ↦ aux_convolution κ f x) =ᵐ[volume]
      ((∫ t : ℝ, κ t • aux_l2Translate t (hf.toLp f) :
        Lp (α := ℝ) ℂ 2 volume) : ℝ → ℂ) := by
    simpa only [aux_l2Translate] using
      (aux_convolution_ae_eq_lpBochner (p := 2) κ f hκ hf)
  have hB : Integrable (fun t : ℝ ↦ κ t • aux_l2Translate t (hf.toLp f)) volume := by
    simpa only [aux_l2Translate] using
      (aux_weighted_lpTranslation_integrable (p := 2) κ (hf.toLp f) hκ)
  have htoLp : hconv.toLp (aux_convolution κ f) =
      ∫ t : ℝ, κ t • aux_l2Translate t (hf.toLp f) := by
    apply Lp.ext (p := 2)
    filter_upwards [hconv.coeFn_toLp, hraw] with x hleft hright
    rw [hleft, hright]
  rw [aux_l2Fourier, dite_eq_left hconv, aux_l2Fourier, dite_eq_left hf]
  change (Lp.fourierTransformₗᵢ ℝ ℂ
    (hconv.toLp (aux_convolution κ f)) : ℝ → ℂ) =ᵐ[volume]
      fun ξ ↦ (𝓕 κ) ξ * (Lp.fourierTransformₗᵢ ℝ ℂ (hf.toLp f)) ξ
  rw [htoLp]
  exact aux_fourier_l2Bochner_ae_eq_multiplier κ hκ (hf.toLp f) hB

/-- A dilation of an integrable Fourier kernel has its Fourier transform
dilated in the reciprocal frequency variable.  This is used in the
Fourier-support calculation of `dyadicReconstructionAndMultiplierBounds`
for `\label{lem:dyadic-reconstruction}`. -/
lemma aux_fourier_scaleKernel (a : ℝ) (ha : 0 < a) (h : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (aux_scaleKernel a h) ξ = 𝓕 h (ξ / a) := by
  unfold aux_scaleKernel
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  let g : ℝ → ℂ := fun y ↦ (𝐞 (-(y * (ξ / a))) : ℂ) * h y
  have hpoint (x : ℝ) :
      (𝐞 (-(x * ξ)) : Circle) • ((a : ℂ) * h (a * x)) =
        (a : ℂ) * g (a * x) := by
    have harg : -(a * x * (ξ / a)) = -(x * ξ) := by
      field_simp
    dsimp [g]
    rw [harg]
    simp only [Circle.smul_def]
    ring
  have hfun :
      (fun x : ℝ ↦ (𝐞 (-(x * ξ)) : Circle) • ((a : ℂ) * h (a * x))) =
        fun x ↦ (a : ℂ) * g (a * x) := by
    ext x
    exact hpoint x
  rw [hfun, MeasureTheory.integral_const_mul,
    Measure.integral_comp_mul_left g a]
  change (a : ℂ) * (|a⁻¹| • ∫ y : ℝ, g y) = ∫ y : ℝ, g y
  rw [show |a⁻¹| = a⁻¹ by rw [abs_of_pos (inv_pos.mpr ha)],
    Complex.real_smul, Complex.ofReal_inv]
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  field_simp

/-- The Fourier transform of the scaled dyadic inverse-Fourier kernel is
the corresponding scaled dyadic cutoff.  This exact kernel multiplier is
used by `dyadicReconstructionAndMultiplierBounds` for
`\label{lem:dyadic-reconstruction}`. -/
lemma aux_fourier_scaledDyadicInverseFourierKernel_eq (k : ℕ) (ξ : ℝ) :
    𝓕 (aux_scaledInverseFourierKernel (fun u ↦ (dyadicCutoff u : ℂ)) k) ξ =
      (dyadicCutoff (ξ / (2 : ℝ) ^ k) : ℂ) := by
  let a : ℝ := (2 : ℝ) ^ k
  let K : ℝ → ℂ := inverseFourierTransform fun u : ℝ ↦ (dyadicCutoff u : ℂ)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hscale :
      aux_scaledInverseFourierKernel (fun u ↦ (dyadicCutoff u : ℂ)) k =
        aux_scaleKernel a K := by
    funext x
    simp [aux_scaledInverseFourierKernel, aux_scaleKernel, a, K]
  rw [hscale, aux_fourier_scaleKernel a ha K ξ]
  simpa [a, K] using aux_fourier_dyadicInverseFourierKernel_eq (ξ / a)

/-- For positive dyadic index, the `L²` Fourier representative of `P k f`
is its scaled dyadic-cutoff multiplier.  This feeds the Fourier-support
conjunct of `dyadicReconstructionAndMultiplierBounds` for
`\label{lem:dyadic-reconstruction}`. -/
lemma aux_l2Fourier_P_ae_eq_multiplier (f : ℝ → ℂ) (hf : MemLp f 2 volume)
    (k : ℕ) (hk : 1 ≤ k) :
    aux_l2Fourier (P k f) =ᵐ[volume]
      fun ξ ↦ (dyadicCutoff (ξ / (2 : ℝ) ^ k) : ℂ) * aux_l2Fourier f ξ := by
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  let κ : ℝ → ℂ :=
    aux_scaledInverseFourierKernel (fun u ↦ (dyadicCutoff u : ℂ)) k
  have hκ : Integrable κ volume := by
    simpa [κ] using memLp_one_iff_integrable.mp
      (aux_scaledDyadicInverseFourierKernel_memLp_one k)
  have hmult := aux_l2Fourier_aux_convolution_ae_eq_multiplier κ f hκ hf
  unfold P
  rw [ite_eq_right hk0]
  change aux_l2Fourier (aux_convolution κ f) =ᵐ[volume] _
  filter_upwards [hmult] with ξ hξ
  rw [hξ, aux_fourier_scaledDyadicInverseFourierKernel_eq k ξ]

/-- The uniform `Lᵖ` estimate for the annular convolution operator.  This is
the multiplier-bound part of `dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_eLpNorm_Q_le (f : ℝ → ℂ) (hf : MemLp f 2 volume)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    eLpNorm (Q k f) p volume ≤ 2 ^ 6 * eLpNorm f p volume := by
  unfold Q
  let κ : ℝ → ℂ :=
    aux_scaledInverseFourierKernel (fun ξ ↦ (annularCutoff ξ : ℂ)) k
  change eLpNorm (aux_convolution κ f) p volume ≤ 2 ^ 6 * eLpNorm f p volume
  have hκlp : MemLp κ 1 volume := by
    simpa [κ] using aux_scaledAnnularInverseFourierKernel_memLp_one k
  have hκ : Integrable κ volume := memLp_one_iff_integrable.mp hκlp
  have hκnorm : eLpNorm κ 1 volume ≤ 2 ^ 6 := by
    simpa [κ] using aux_eLpNorm_scaledAnnularInverseFourierKernel_one_le k
  by_cases hp_top : p = ∞
  · subst p
    exact aux_eLpNorm_aux_convolution_top_le_of_eLpNorm_one_le κ f hκ (2 ^ 6) hκnorm
  · let : Fact (1 ≤ p) := ⟨hp⟩
    let : Fact (p ≠ ∞) := ⟨hp_top⟩
    by_cases hfp : MemLp f p volume
    · calc
        eLpNorm (aux_convolution κ f) p volume ≤
            eLpNorm κ 1 volume * eLpNorm f p volume :=
          aux_eLpNorm_aux_convolution_le_of_memLp_one κ f hκlp hfp
        _ ≤ 2 ^ 6 * eLpNorm f p volume :=
          mul_le_mul hκnorm le_rfl bot_le bot_le
    · have hnorm : eLpNorm f p volume = ∞ := by
        apply ENNReal.not_lt_top.mp
        intro hlt
        apply hfp
        exact ⟨hf.1, hlt⟩
      rw [hnorm]
      simp

/-- Compact support makes the low-frequency cutoff integrable; this is the
low-frequency input to `dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_lowFrequencyCutoff_integrable :
    Integrable (fun ξ ↦ (lowFrequencyCutoff ξ : ℂ)) volume := by
  have hsupport : HasCompactSupport (fun ξ ↦ (lowFrequencyCutoff ξ : ℂ)) := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-2 : ℝ) 2))
    intro ξ hξ
    have hout : 2 ≤ |ξ| := by
      by_contra hnot
      apply hξ
      rw [Set.mem_Icc]
      have habs : |ξ| < 2 := lt_of_not_ge hnot
      rw [abs_lt] at habs
      exact ⟨habs.1.le, habs.2.le⟩
    simp [aux_lowFrequencyCutoff_eq_zero_of_two_le_abs hout]
  have hcontinuous : Continuous (fun ξ : ℝ ↦ (lowFrequencyCutoff ξ : ℂ)) :=
    Complex.continuous_ofReal.comp aux_continuous_lowFrequencyCutoff
  exact hcontinuous.integrable_of_hasCompactSupport hsupport

/-- The negative transition of the low-frequency cutoff is a generic cubic
transition, for use in `dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_lowFrequencyCutoff_eq_neg_transition {ξ : ℝ} (_hξa : -2 ≤ ξ) (hξb : ξ ≤ -1) :
    lowFrequencyCutoff ξ = aux_dyadicTransition 0 1 2 1 ξ := by
  unfold lowFrequencyCutoff aux_dyadicTransition
  rw [abs_of_nonpos (by linarith : ξ ≤ 0)]
  ring_nf

/-- The positive transition of the low-frequency cutoff is a generic cubic
transition, for use in `dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_lowFrequencyCutoff_eq_pos_transition {ξ : ℝ} (hξa : 1 ≤ ξ) (_hξb : ξ ≤ 2) :
    lowFrequencyCutoff ξ = aux_dyadicTransition 0 1 2 (-1) ξ := by
  unfold lowFrequencyCutoff aux_dyadicTransition
  rw [abs_of_nonneg (by linarith : 0 ≤ ξ)]
  ring_nf

/-- The low-frequency cutoff is one on its central plateau.  This is used in
the low-kernel calculation for `dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_lowFrequencyCutoff_eq_one_middle {ξ : ℝ} (hξa : -1 ≤ ξ) (hξb : ξ ≤ 1) :
    lowFrequencyCutoff ξ = 1 := by
  exact aux_lowFrequencyCutoff_eq_one_of_abs_le_one (by
    rw [abs_le]
    exact ⟨hξa, hξb⟩)

/-- Restriction of the low-cutoff Fourier integral to its compact support,
used in `dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_lowFrequencyFourier_integral_eq_interval (x : ℝ) :
    (∫ ξ : ℝ, aux_dyadicFourierPhase x ξ * (lowFrequencyCutoff ξ : ℂ)) =
      ∫ ξ in (-2 : ℝ)..2, aux_dyadicFourierPhase x ξ * (lowFrequencyCutoff ξ : ℂ) := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro ξ hξ
  rw [Function.mem_support] at hξ
  constructor
  · by_contra h
    have hle : ξ ≤ -2 := le_of_not_gt h
    have hη : lowFrequencyCutoff ξ = 0 := by
      apply aux_lowFrequencyCutoff_eq_zero_of_two_le_abs
      rw [abs_of_nonpos (by linarith : ξ ≤ 0)]
      linarith
    apply hξ
    simp [hη]
  · by_contra h
    have hge : 2 ≤ ξ := le_of_lt (lt_of_not_ge h)
    have hη : lowFrequencyCutoff ξ = 0 := by
      apply aux_lowFrequencyCutoff_eq_zero_of_two_le_abs
      rw [abs_of_nonneg (by linarith : 0 ≤ ξ)]
      exact hge
    apply hξ
    simp [hη]

/-- Continuity of the low-cutoff Fourier integrand, used to split its
compact interval in `dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_lowFrequencyFourier_integrand_continuous (x : ℝ) :
    Continuous (fun ξ : ℝ ↦ aux_dyadicFourierPhase x ξ * (lowFrequencyCutoff ξ : ℂ)) := by
  exact (aux_continuous_dyadicFourierPhase x).mul
    (Complex.continuous_ofReal.comp aux_continuous_lowFrequencyCutoff)

/-- The compact low-cutoff Fourier integral splits into its two transitions
and plateau for `dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_lowFrequencyFourier_integral_three_parts (x : ℝ) :
    (∫ ξ in (-2 : ℝ)..2, aux_dyadicFourierPhase x ξ * (lowFrequencyCutoff ξ : ℂ)) =
      (∫ ξ in (-2 : ℝ)..(-1), aux_dyadicFourierPhase x ξ * (lowFrequencyCutoff ξ : ℂ)) +
      (∫ ξ in (-1 : ℝ)..1, aux_dyadicFourierPhase x ξ * (lowFrequencyCutoff ξ : ℂ)) +
      ∫ ξ in (1 : ℝ)..2, aux_dyadicFourierPhase x ξ * (lowFrequencyCutoff ξ : ℂ) := by
  let g : ℝ → ℂ := fun ξ ↦ aux_dyadicFourierPhase x ξ * (lowFrequencyCutoff ξ : ℂ)
  have hg : Continuous g := aux_lowFrequencyFourier_integrand_continuous x
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.intervalIntegrable (-2 : ℝ) (-1 : ℝ))
    (hg.intervalIntegrable (-1 : ℝ) (1 : ℝ))
  have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.intervalIntegrable (-2 : ℝ) (1 : ℝ))
    (hg.intervalIntegrable (1 : ℝ) (2 : ℝ))
  change (∫ ξ in (-2 : ℝ)..2, g ξ) = _
  rw [← h2, ← h1]

/-- Two integrations by parts on the negative low-cutoff transition, used in
`dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_lowFrequencyFourier_neg_ibp (x : ℝ) (hx : x ≠ 0) :
    (∫ t in (-2 : ℝ)..(-1), aux_dyadicFourierPhase x t * (lowFrequencyCutoff t : ℂ)) =
      (lowFrequencyCutoff (-1) : ℂ) * aux_dyadicFourierPhasePrimitive x (-1) -
        (lowFrequencyCutoff (-2) : ℂ) * aux_dyadicFourierPhasePrimitive x (-2) +
      ∫ t in (-2 : ℝ)..(-1),
        (aux_dyadicTransitionSecondDeriv 1 2 1 t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t := by
  have htrans := aux_transition_fourier_ibp_twice (l := (-2 : ℝ)) (r := (-1 : ℝ))
    (x := x) (c := 0) (e := 1) (a := 2) (b := (1 : ℝ)) hx (by
      intro t ht
      have ht' : -2 < t ∧ t < -1 := by
        norm_num [min_eq_left, max_eq_right] at ht
        exact ht
      constructor <;> linarith) (by norm_num) (by norm_num)
  rw [intervalIntegral.integral_congr (fun t ht ↦ by
    have ht' : -2 ≤ t ∧ t ≤ -1 := by
      rw [Set.uIcc_of_le (by norm_num : (-2 : ℝ) ≤ -1)] at ht
      exact ht
    rw [aux_lowFrequencyCutoff_eq_neg_transition ht'.1 ht'.2])]
  rw [aux_lowFrequencyCutoff_eq_neg_transition (by norm_num) (by norm_num),
    aux_lowFrequencyCutoff_eq_neg_transition (by norm_num) (by norm_num)]
  exact htrans

/-- Two integrations by parts on the positive low-cutoff transition, used in
`dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_lowFrequencyFourier_pos_ibp (x : ℝ) (hx : x ≠ 0) :
    (∫ t in (1 : ℝ)..2, aux_dyadicFourierPhase x t * (lowFrequencyCutoff t : ℂ)) =
      (lowFrequencyCutoff 2 : ℂ) * aux_dyadicFourierPhasePrimitive x 2 -
        (lowFrequencyCutoff 1 : ℂ) * aux_dyadicFourierPhasePrimitive x 1 +
      ∫ t in (1 : ℝ)..2,
        (aux_dyadicTransitionSecondDeriv 1 2 (-1) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t := by
  have htrans := aux_transition_fourier_ibp_twice (l := (1 : ℝ)) (r := (2 : ℝ))
    (x := x) (c := 0) (e := 1) (a := 2) (b := (-1 : ℝ)) hx (by
      intro t ht
      have ht' : 1 < t ∧ t < 2 := by
        norm_num [min_eq_left, max_eq_right] at ht
        exact ht
      constructor <;> linarith) (by norm_num) (by norm_num)
  rw [intervalIntegral.integral_congr (fun t ht ↦ by
    have ht' : 1 ≤ t ∧ t ≤ 2 := by
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
      exact ht
    rw [aux_lowFrequencyCutoff_eq_pos_transition ht'.1 ht'.2])]
  rw [aux_lowFrequencyCutoff_eq_pos_transition (by norm_num) (by norm_num),
    aux_lowFrequencyCutoff_eq_pos_transition (by norm_num) (by norm_num)]
  exact htrans

/-- Integration by parts on the central plateau of the low cutoff, used in
`dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_lowFrequencyFourier_middle_ibp (x : ℝ) (hx : x ≠ 0) :
    (∫ t in (-1 : ℝ)..1, aux_dyadicFourierPhase x t * (lowFrequencyCutoff t : ℂ)) =
      (lowFrequencyCutoff 1 : ℂ) * aux_dyadicFourierPhasePrimitive x 1 -
        (lowFrequencyCutoff (-1) : ℂ) * aux_dyadicFourierPhasePrimitive x (-1) := by
  have h := aux_interval_fourier_ibp (a := (-1 : ℝ)) (b := (1 : ℝ)) (x := x) hx
    (u := fun _ : ℝ ↦ (1 : ℝ)) (u' := fun _ : ℝ ↦ 0)
    (continuous_const.continuousOn) (by
      intro t ht
      simpa using (hasDerivAt_const t (1 : ℝ)))
    (continuous_const.intervalIntegrable (-1 : ℝ) 1)
  rw [intervalIntegral.integral_congr (fun t ht ↦ by
    have ht' : -1 ≤ t ∧ t ≤ 1 := by
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
      exact ht
    rw [aux_lowFrequencyCutoff_eq_one_middle ht'.1 ht'.2])]
  rw [aux_lowFrequencyCutoff_eq_one_middle (by norm_num) (by norm_num),
    aux_lowFrequencyCutoff_eq_one_middle (by norm_num) (by norm_num)]
  norm_num at h
  simpa using h

/-- Cancellation of the low-cutoff boundary terms leaves two second-order
remainders in `dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_lowFrequencyFourier_tail_representation (x : ℝ) (hx : x ≠ 0) :
    (∫ ξ : ℝ, aux_dyadicFourierPhase x ξ * (lowFrequencyCutoff ξ : ℂ)) =
      (∫ t in (-2 : ℝ)..(-1),
        (aux_dyadicTransitionSecondDeriv 1 2 1 t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      ∫ t in (1 : ℝ)..2,
        (aux_dyadicTransitionSecondDeriv 1 2 (-1) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t := by
  rw [aux_lowFrequencyFourier_integral_eq_interval,
    aux_lowFrequencyFourier_integral_three_parts,
    aux_lowFrequencyFourier_neg_ibp x hx,
    aux_lowFrequencyFourier_middle_ibp x hx,
    aux_lowFrequencyFourier_pos_ibp x hx]
  have hm2 : lowFrequencyCutoff (-2) = 0 :=
    aux_lowFrequencyCutoff_eq_zero_of_two_le_abs (by norm_num)
  have hm1 : lowFrequencyCutoff (-1) = 1 :=
    aux_lowFrequencyCutoff_eq_one_of_abs_le_one (by norm_num)
  have h1 : lowFrequencyCutoff 1 = 1 :=
    aux_lowFrequencyCutoff_eq_one_of_abs_le_one (by norm_num)
  have h2 : lowFrequencyCutoff 2 = 0 :=
    aux_lowFrequencyCutoff_eq_zero_of_two_le_abs (by norm_num)
  rw [hm2, hm1, h1, h2]
  norm_num
  ring

/-- The compact low-frequency multiplier has reciprocal-square Fourier tail,
used to make its inverse kernel integrable in
`dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_lowFrequencyFourier_tail_norm (x : ℝ) (hx : x ≠ 0) :
    ‖∫ ξ : ℝ, aux_dyadicFourierPhase x ξ * (lowFrequencyCutoff ξ : ℂ)‖ ≤
      512 / x ^ 2 := by
  rw [aux_lowFrequencyFourier_tail_representation x hx]
  have hneg := aux_transition_remainder_bound
    (l := (-2 : ℝ)) (r := (-1 : ℝ)) (x := x) (e := 1) (a := 2) (b := (1 : ℝ))
    (K := 1024) hx (by
      intro t ht
      have ht' : -2 < t ∧ t ≤ -1 := by
        rw [Set.uIoc_of_le (by norm_num : (-2 : ℝ) ≤ -1)] at ht
        exact ht
      constructor <;> linarith) (by norm_num)
  have hpos := aux_transition_remainder_bound
    (l := (1 : ℝ)) (r := (2 : ℝ)) (x := x) (e := 1) (a := 2) (b := (-1 : ℝ))
    (K := 1024) hx (by
      intro t ht
      have ht' : 1 < t ∧ t ≤ 2 := by
        rw [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
        exact ht
      constructor <;> linarith) (by norm_num)
  calc
    ‖(∫ t in (-2 : ℝ)..(-1),
        (aux_dyadicTransitionSecondDeriv 1 2 1 t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t) +
      ∫ t in (1 : ℝ)..2,
        (aux_dyadicTransitionSecondDeriv 1 2 (-1) t : ℂ) *
          aux_dyadicFourierPhaseSecondPrimitive x t‖ ≤
        ‖∫ t in (-2 : ℝ)..(-1),
          (aux_dyadicTransitionSecondDeriv 1 2 1 t : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x t‖ +
        ‖∫ t in (1 : ℝ)..2,
          (aux_dyadicTransitionSecondDeriv 1 2 (-1) t : ℂ) *
            aux_dyadicFourierPhaseSecondPrimitive x t‖ := norm_add_le _ _
    _ ≤ (1024 / (16 * x ^ 2)) * |(-1 : ℝ) - (-2)| +
        (1024 / (16 * x ^ 2)) * |(2 : ℝ) - 1| := by
      gcongr
    _ ≤ 512 / x ^ 2 := by
      have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ -1 - -2),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 - 1)]
      have hlen₁ : (-1 : ℝ) - (-2) = 1 := by norm_num
      have hlen₂ : (2 : ℝ) - 1 = 1 := by norm_num
      rw [hlen₁, hlen₂]
      calc
        (1024 / (16 * x ^ 2)) * 1 + (1024 / (16 * x ^ 2)) * 1 =
            128 / x ^ 2 := by
          field_simp [hx2.ne']
          ring
        _ ≤ 512 / x ^ 2 :=
          (div_le_div_iff_of_pos_right hx2).2 (by norm_num)

/-- A direct integral bound for the compact low-frequency multiplier, used
in the local kernel estimate of `dyadicReconstructionAndMultiplierBounds`
and \(\label{lem:dyadic-reconstruction}\). -/
lemma aux_lowFrequencyCutoff_norm_integral_le_four :
    (∫ ξ : ℝ, ‖(lowFrequencyCutoff ξ : ℂ)‖) ≤ 4 := by
  let s : Set ℝ := Set.Icc (-2 : ℝ) 2
  let h : ℝ → ℝ := s.indicator (fun _ ↦ (1 : ℝ))
  have hlowint : Integrable (fun ξ : ℝ ↦ ‖(lowFrequencyCutoff ξ : ℂ)‖) volume :=
    aux_lowFrequencyCutoff_integrable.norm
  have hsfinite : volume s ≠ ∞ := by
    simp [s, Real.volume_Icc]
  have hint : Integrable h volume := by
    exact (integrableOn_const hsfinite).integrable_indicator measurableSet_Icc
  have hdom : (fun ξ : ℝ ↦ ‖(lowFrequencyCutoff ξ : ℂ)‖) ≤ h := by
    intro ξ
    by_cases hξ : ξ ∈ s
    · rw [show h ξ = 1 by simp [h, hξ]]
      change ‖(lowFrequencyCutoff ξ : ℂ)‖ ≤ 1
      rw [Complex.norm_real, Real.norm_eq_abs, lowFrequencyCutoff,
        abs_of_nonneg (aux_smoothStep_nonneg_le_one _).1]
      exact (aux_smoothStep_nonneg_le_one _).2
    · rw [show h ξ = 0 by simp [h, hξ]]
      change ‖(lowFrequencyCutoff ξ : ℂ)‖ ≤ 0
      have hout : 2 ≤ |ξ| := by
        by_contra hnot
        apply hξ
        change ξ ∈ Set.Icc (-2 : ℝ) 2
        have hlt : |ξ| < 2 := lt_of_not_ge hnot
        rw [abs_lt] at hlt
        exact ⟨hlt.1.le, hlt.2.le⟩
      rw [aux_lowFrequencyCutoff_eq_zero_of_two_le_abs hout]
      simp
  calc
    (∫ ξ : ℝ, ‖(lowFrequencyCutoff ξ : ℂ)‖) ≤ ∫ ξ : ℝ, h ξ :=
      integral_mono hlowint hint hdom
    _ = 4 := by
      change (∫ ξ : ℝ, s.indicator (fun _ ↦ (1 : ℝ)) ξ) = 4
      rw [integral_indicator_const (μ := volume) (1 : ℝ) measurableSet_Icc]
      rw [Real.volume_real_Icc_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
      norm_num

/-- The inverse Fourier transform of the low cutoff has a uniform local
bound for `dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_lowFrequencyInverse_uniform (x : ℝ) :
    ‖inverseFourierTransform (fun ξ ↦ (lowFrequencyCutoff ξ : ℂ)) x‖ ≤ 8 := by
  change ‖VectorFourier.fourierIntegral 𝐞 volume (-(innerₗ ℝ))
      (fun ξ ↦ (lowFrequencyCutoff ξ : ℂ)) x‖ ≤ 8
  calc
    ‖VectorFourier.fourierIntegral 𝐞 volume (-(innerₗ ℝ))
        (fun ξ ↦ (lowFrequencyCutoff ξ : ℂ)) x‖ ≤
        ∫ ξ : ℝ, ‖(lowFrequencyCutoff ξ : ℂ)‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (-(innerₗ ℝ)) _ x
    _ ≤ 8 := (aux_lowFrequencyCutoff_norm_integral_le_four).trans (by norm_num)

/-- The inverse low-frequency kernel is its phase integral; this transfers
the decay estimate in `dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_lowFrequencyInverse_eq_phase (x : ℝ) :
    inverseFourierTransform (fun ξ ↦ (lowFrequencyCutoff ξ : ℂ)) x =
      ∫ ξ : ℝ, aux_dyadicFourierPhase x ξ * (lowFrequencyCutoff ξ : ℂ) := by
  rw [inverseFourierTransform, Real.fourierInv_eq']
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  congr 3
  rw [Real.inner_apply]
  push_cast
  ring

/-- The inverse low-frequency kernel has a reciprocal-square tail in
`dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_lowFrequencyInverse_tail (x : ℝ) (hx : x ≠ 0) :
    ‖inverseFourierTransform (fun ξ ↦ (lowFrequencyCutoff ξ : ℂ)) x‖ ≤ 512 / x ^ 2 := by
  rw [aux_lowFrequencyInverse_eq_phase]
  exact aux_lowFrequencyFourier_tail_norm x hx

/-- A continuous representative of the low-frequency inverse kernel, used
by `dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_lowFrequencyInverse_continuous :
    Continuous (inverseFourierTransform fun ξ : ℝ ↦ (lowFrequencyCutoff ξ : ℂ)) := by
  let hmem : MemLp (fun ξ : ℝ ↦ (lowFrequencyCutoff ξ : ℂ)) 1 volume :=
    memLp_one_iff_integrable.mpr aux_lowFrequencyCutoff_integrable
  unfold inverseFourierTransform
  rw [← Real.Lp.fourierTransformInv_toLp hmem]
  exact (Real.Lp.fourierTransformInv hmem.toLp).continuous

/-- The physical low-frequency inverse kernel is in `L¹`; this allows the
raw convolution model in `dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_lowFrequencyInverse_memLp_one :
    MemLp (inverseFourierTransform fun ξ : ℝ ↦ (lowFrequencyCutoff ξ : ℂ)) 1 volume := by
  refine ⟨aux_lowFrequencyInverse_continuous.aestronglyMeasurable, ?_⟩
  exact (aux_eLpNorm_le_1024_of_uniform_and_tail aux_lowFrequencyInverse_uniform
    aux_lowFrequencyInverse_tail).trans_lt (by finiteness)

/-- Integrability of the Fourier transform of the low inverse kernel, the
Fourier-inversion input for `dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_fourier_lowFrequencyInverse_integrable :
    Integrable
      (fun ξ : ℝ ↦ 𝓕 (fun t : ℝ ↦ (lowFrequencyCutoff t : ℂ)) ξ) volume := by
  have hcheck : Integrable
      (inverseFourierTransform fun t : ℝ ↦ (lowFrequencyCutoff t : ℂ)) volume :=
    memLp_one_iff_integrable.mp aux_lowFrequencyInverse_memLp_one
  have hneg : Integrable
      ((inverseFourierTransform fun t : ℝ ↦ (lowFrequencyCutoff t : ℂ)) ∘
        fun x : ℝ ↦ -x)
        volume :=
    ((Measure.measurePreserving_neg volume).integrable_comp hcheck.1).mpr hcheck
  convert hneg using 1
  ext x
  simpa [inverseFourierTransform] using
    (Real.fourierInv_eq_fourier_neg (fun t : ℝ ↦ (lowFrequencyCutoff t : ℂ)) (-x)).symm

/-- Fourier inversion for the low inverse kernel, used to identify `P 0` in
`dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_fourier_lowFrequencyInverse_eq (ξ : ℝ) :
    𝓕 (inverseFourierTransform fun t : ℝ ↦ (lowFrequencyCutoff t : ℂ)) ξ =
      (lowFrequencyCutoff ξ : ℂ) := by
  have h := Continuous.fourier_fourierInv_eq
    (Complex.continuous_ofReal.comp aux_continuous_lowFrequencyCutoff)
    aux_lowFrequencyCutoff_integrable aux_fourier_lowFrequencyInverse_integrable
  exact congrFun h ξ

/-- The `L²` Fourier representative of `P 0` is the low-frequency cutoff
multiplier, completing the low-index case for
`dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_l2Fourier_P_zero_ae_eq_multiplier (f : ℝ → ℂ) (hf : MemLp f 2 volume) :
    aux_l2Fourier (P 0 f) =ᵐ[volume]
      fun ξ ↦ (lowFrequencyCutoff ξ : ℂ) * aux_l2Fourier f ξ := by
  have hκ :
      Integrable (inverseFourierTransform fun ξ : ℝ ↦ (lowFrequencyCutoff ξ : ℂ)) volume :=
    memLp_one_iff_integrable.mp aux_lowFrequencyInverse_memLp_one
  have hmult := aux_l2Fourier_aux_convolution_ae_eq_multiplier
    (inverseFourierTransform fun ξ : ℝ ↦ (lowFrequencyCutoff ξ : ℂ)) f hκ hf
  unfold P
  rw [ite_eq_left rfl]
  filter_upwards [hmult] with ξ hξ
  rw [hξ, aux_fourier_lowFrequencyInverse_eq ξ]

/-- The low-index dyadic projection preserves `L²`; this is the membership
input for the reconstruction in `dyadicReconstructionAndMultiplierBounds`
and \(\label{lem:dyadic-reconstruction}\). -/
lemma aux_memLp_P_zero (f : ℝ → ℂ) (hf : MemLp f 2 volume) :
    MemLp (P 0 f) 2 volume := by
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hκ :
      Integrable (inverseFourierTransform fun ξ : ℝ ↦ (lowFrequencyCutoff ξ : ℂ)) volume :=
    memLp_one_iff_integrable.mp aux_lowFrequencyInverse_memLp_one
  unfold P
  rw [ite_eq_left rfl]
  exact aux_convolution_memLp_of_memLp_one _ _ hκ hf

/-- Every positive dyadic projection preserves `L²`; this is the membership
input for `dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_memLp_P_succ (f : ℝ → ℂ) (hf : MemLp f 2 volume) (k : ℕ) :
    MemLp (P (k + 1) f) 2 volume := by
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hκ : Integrable
      (aux_scaledInverseFourierKernel (fun ξ ↦ (dyadicCutoff ξ : ℂ)) (k + 1)) volume :=
    memLp_one_iff_integrable.mp (aux_scaledDyadicInverseFourierKernel_memLp_one (k + 1))
  unfold P
  rw [ite_eq_right (Nat.succ_ne_zero k)]
  exact aux_convolution_memLp_of_memLp_one _ _ hκ hf

/-- Plancherel preserves the `eLpNorm` of the chosen `aux_l2Fourier`
representative.  This transfers the finite reconstruction residual in
`dyadicReconstructionAndMultiplierBounds` to the Fourier side for
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_eLpNorm_aux_l2Fourier_eq (f : ℝ → ℂ) (hf : MemLp f 2 volume) :
    eLpNorm (aux_l2Fourier f) 2 volume = eLpNorm f 2 volume := by
  rw [aux_l2Fourier, dite_eq_left hf]
  calc
    eLpNorm (fun ξ ↦ (Lp.fourierTransformₗᵢ ℝ ℂ (hf.toLp f)) ξ) 2 volume =
        ‖Lp.fourierTransformₗᵢ ℝ ℂ (hf.toLp f)‖ₑ := (Lp.enorm_def _).symm
    _ = ‖hf.toLp f‖ₑ := (Lp.fourierTransformₗᵢ ℝ ℂ).enorm_map _
    _ = eLpNorm f 2 volume := Lp.enorm_toLp hf

/-- The chosen Plancherel representative is additive almost everywhere.
This is used to calculate the finite reconstruction residual in
`dyadicReconstructionAndMultiplierBounds` for
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_l2Fourier_add_ae {f g : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    aux_l2Fourier (f + g) =ᵐ[volume] aux_l2Fourier f + aux_l2Fourier g := by
  have hfg : MemLp (f + g) 2 volume := hf.add hg
  have htoLp : hfg.toLp (f + g) = hf.toLp f + hg.toLp g := by
    apply Lp.ext (p := 2)
    filter_upwards [hfg.coeFn_toLp, hf.coeFn_toLp, hg.coeFn_toLp,
      Lp.coeFn_add (hf.toLp f) (hg.toLp g)] with x hfgx hfx hgx hadd
    rw [hfgx, hadd]
    change f x + g x = (hf.toLp f : ℝ → ℂ) x + (hg.toLp g : ℝ → ℂ) x
    rw [hfx, hgx]
  rw [aux_l2Fourier, dite_eq_left hfg, aux_l2Fourier, dite_eq_left hf,
    aux_l2Fourier, dite_eq_left hg, htoLp]
  rw [map_add]
  exact Lp.coeFn_add _ _

/-- The chosen Plancherel representative respects subtraction almost
everywhere.  This handles the two subtractions in the reconstruction
residual of `dyadicReconstructionAndMultiplierBounds` for
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_l2Fourier_sub_ae {f g : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    aux_l2Fourier (f - g) =ᵐ[volume] aux_l2Fourier f - aux_l2Fourier g := by
  have hfg : MemLp (f - g) 2 volume := hf.sub hg
  have htoLp : hfg.toLp (f - g) = hf.toLp f - hg.toLp g := by
    apply Lp.ext (p := 2)
    filter_upwards [hfg.coeFn_toLp, hf.coeFn_toLp, hg.coeFn_toLp,
      Lp.coeFn_sub (hf.toLp f) (hg.toLp g)] with x hfgx hfx hgx hsub
    rw [hfgx, hsub]
    change f x - g x = (hf.toLp f : ℝ → ℂ) x - (hg.toLp g : ℝ → ℂ) x
    rw [hfx, hgx]
  rw [aux_l2Fourier, dite_eq_left hfg, aux_l2Fourier, dite_eq_left hf,
    aux_l2Fourier, dite_eq_left hg, htoLp]
  rw [map_sub]
  exact Lp.coeFn_sub _ _

/-- The chosen Plancherel representative commutes with finite sums almost
everywhere.  This packages the finite dyadic sum in
`dyadicReconstructionAndMultiplierBounds` for
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_l2Fourier_finset_sum_ae {ι : Type*} (s : Finset ι)
    (g : ι → ℝ → ℂ) (hg : ∀ i ∈ s, MemLp (g i) 2 volume) :
    aux_l2Fourier (fun x ↦ ∑ i ∈ s, g i x) =ᵐ[volume]
      fun ξ ↦ ∑ i ∈ s, aux_l2Fourier (g i) ξ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hzero : MemLp (fun _ : ℝ ↦ (0 : ℂ)) 2 volume := MemLp.zero
      have htoLp : hzero.toLp (fun _ : ℝ ↦ (0 : ℂ)) = 0 := by
        exact hzero.toLp_zero
      simp only [Finset.sum_empty]
      rw [aux_l2Fourier, dite_eq_left hzero, htoLp, map_zero]
      exact Lp.coeFn_zero ℂ 2 volume
  | @insert a s ha ih =>
      have hga : MemLp (g a) 2 volume := hg a (Finset.mem_insert_self _ _)
      have hgs : ∀ i ∈ s, MemLp (g i) 2 volume := by
        intro i hi
        exact hg i (Finset.mem_insert_of_mem hi)
      have hsum : MemLp (fun x ↦ ∑ i ∈ s, g i x) 2 volume :=
        memLp_finsetSum s hgs
      have hadd := aux_l2Fourier_add_ae hga hsum
      have hih := ih hgs
      filter_upwards [hadd, hih] with ξ h1 h2
      have hsum_insert : (fun x ↦ ∑ i ∈ insert a s, g i x) =
          g a + (fun x ↦ ∑ i ∈ s, g i x) := by
        funext x
        simp [Finset.sum_insert, ha]
      change aux_l2Fourier (fun x ↦ ∑ i ∈ insert a s, g i x) ξ =
        ∑ i ∈ insert a s, aux_l2Fourier (g i) ξ
      rw [hsum_insert, Finset.sum_insert ha]
      simpa [Pi.add_apply, h2] using h1

/-- The `L²` norm of a finite spatial residual equals the norm of its
finite Fourier residual.  It is the Plancherel reduction used in
`dyadicReconstructionAndMultiplierBounds` for
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_eLpNorm_residual_eq_fourier {ι : Type*} (s : Finset ι)
    (f g₀ : ℝ → ℂ) (g : ι → ℝ → ℂ)
    (hf : MemLp f 2 volume) (hg₀ : MemLp g₀ 2 volume)
    (hg : ∀ i ∈ s, MemLp (g i) 2 volume) :
    eLpNorm (fun x ↦ f x - g₀ x - ∑ i ∈ s, g i x) 2 volume =
      eLpNorm (fun ξ ↦ aux_l2Fourier f ξ - aux_l2Fourier g₀ ξ -
        ∑ i ∈ s, aux_l2Fourier (g i) ξ) 2 volume := by
  let G : ℝ → ℂ := fun x ↦ ∑ i ∈ s, g i x
  have hG : MemLp G 2 volume := memLp_finsetSum s hg
  have hfg : MemLp (f - g₀) 2 volume := hf.sub hg₀
  have hres : MemLp (f - g₀ - G) 2 volume := hfg.sub hG
  have hsum := aux_l2Fourier_finset_sum_ae s g hg
  have hfg_fourier := aux_l2Fourier_sub_ae hf hg₀
  have hres_fourier := aux_l2Fourier_sub_ae hfg hG
  have hfourier : aux_l2Fourier (f - g₀ - G) =ᵐ[volume]
      fun ξ ↦ aux_l2Fourier f ξ - aux_l2Fourier g₀ ξ -
        ∑ i ∈ s, aux_l2Fourier (g i) ξ := by
    filter_upwards [hres_fourier, hfg_fourier, hsum] with ξ hresξ hfgξ hsumξ
    rw [hresξ]
    change aux_l2Fourier (f - g₀) ξ - aux_l2Fourier G ξ = _
    rw [hfgξ]
    have hGξ : aux_l2Fourier G ξ = ∑ i ∈ s, aux_l2Fourier (g i) ξ := by
      simpa only [G] using hsumξ
    rw [hGξ]
    rfl
  change eLpNorm (f - g₀ - G) 2 volume = _
  calc
    eLpNorm (f - g₀ - G) 2 volume = eLpNorm (aux_l2Fourier (f - g₀ - G)) 2 volume :=
      (aux_eLpNorm_aux_l2Fourier_eq (f - g₀ - G) hres).symm
    _ = eLpNorm (fun ξ ↦ aux_l2Fourier f ξ - aux_l2Fourier g₀ ξ -
        ∑ i ∈ s, aux_l2Fourier (g i) ξ) 2 volume := eLpNorm_congr_ae hfourier

/-- The preceding Plancherel reduction specialized to the finite dyadic
reconstruction residual in `dyadicReconstructionAndMultiplierBounds` for
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_eLpNorm_dyadic_residual_eq_fourier (f : ℝ → ℂ)
    (hf : MemLp f 2 volume) (hPzero : MemLp (P 0 f) 2 volume)
    (hP : ∀ k : ℕ, MemLp (P (k + 1) f) 2 volume) (N : ℕ) :
    eLpNorm
        (fun x ↦ f x - P 0 f x - ∑ k ∈ Finset.range N, P (k + 1) f x)
        2 volume =
      eLpNorm
        (fun ξ ↦ aux_l2Fourier f ξ - aux_l2Fourier (P 0 f) ξ -
          ∑ k ∈ Finset.range N, aux_l2Fourier (P (k + 1) f) ξ)
        2 volume := by
  exact aux_eLpNorm_residual_eq_fourier (Finset.range N) f (P 0 f)
    (fun k ↦ P (k + 1) f) hf hPzero (fun k _ ↦ hP k)

/-- The Fourier representative of the finite dyadic reconstruction residual
is the high-frequency remainder multiplier.  This packages the telescoping
cutoff algebra for `dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_dyadic_residual_fourier_ae (f : ℝ → ℂ) (hf : MemLp f 2 volume) (N : ℕ) :
    (fun ξ ↦ aux_l2Fourier f ξ - aux_l2Fourier (P 0 f) ξ -
      ∑ k ∈ Finset.range N, aux_l2Fourier (P (k + 1) f) ξ) =ᵐ[volume]
      fun ξ ↦ (1 - (lowFrequencyCutoff (ξ / (2 : ℝ) ^ N) : ℂ)) * aux_l2Fourier f ξ := by
  have hzero := aux_l2Fourier_P_zero_ae_eq_multiplier f hf
  have hall : ∀ᵐ ξ ∂volume, ∀ k : ℕ,
      aux_l2Fourier (P (k + 1) f) ξ =
        (dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) : ℂ) * aux_l2Fourier f ξ := by
    rw [ae_all_iff]
    intro k
    exact aux_l2Fourier_P_ae_eq_multiplier f hf (k + 1) (by omega)
  filter_upwards [hzero, hall] with ξ hzeroξ hallξ
  have hsum : ∑ k ∈ Finset.range N, aux_l2Fourier (P (k + 1) f) ξ =
      ∑ k ∈ Finset.range N,
        (dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) : ℂ) * aux_l2Fourier f ξ := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hallξ k
  rw [hzeroξ, hsum, ← Finset.sum_mul]
  have htel : (lowFrequencyCutoff ξ : ℂ) +
      ∑ k ∈ Finset.range N, (dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) : ℂ) =
        (lowFrequencyCutoff (ξ / (2 : ℝ) ^ N) : ℂ) := by
    exact_mod_cast aux_dyadic_telescoping N ξ
  rw [show (1 : ℂ) = 1 by rfl]
  calc
    aux_l2Fourier f ξ - (lowFrequencyCutoff ξ : ℂ) * aux_l2Fourier f ξ -
        (∑ k ∈ Finset.range N, (dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) : ℂ)) *
          aux_l2Fourier f ξ =
        (1 - ((lowFrequencyCutoff ξ : ℂ) +
          ∑ k ∈ Finset.range N, (dyadicCutoff (ξ / (2 : ℝ) ^ (k + 1)) : ℂ))) *
          aux_l2Fourier f ξ := by ring
    _ = (1 - (lowFrequencyCutoff (ξ / (2 : ℝ) ^ N) : ℂ)) * aux_l2Fourier f ξ := by
      rw [htel]

/-- A bounded pointwise-vanishing multiplier sends a fixed `L²` function to
zero in `L²`.  This dominated-convergence bridge is used for the finite
reconstruction residual in `dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_tendsto_eLpNorm_mul_of_bounded_tends_zero
    (G : ℝ → ℂ) (hG : MemLp G 2 volume)
    (R : ℕ → ℝ → ℂ)
    (hRmem : ∀ N, MemLp (fun ξ ↦ R N ξ * G ξ) 2 volume)
    (hRbound : ∀ N ξ, ‖R N ξ‖ ≤ 2)
    (hRlim : ∀ ξ, Tendsto (fun N ↦ R N ξ) atTop (𝓝 0)) :
    Tendsto (fun N ↦ eLpNorm (fun ξ ↦ R N ξ * G ξ) 2 volume)
      atTop (𝓝 0) := by
  have hGmeas : AEStronglyMeasurable G volume := hG.aestronglyMeasurable
  have hGnorm : MemLp (fun ξ ↦ ‖G ξ‖) 2 volume :=
    (memLp_norm_iff hGmeas).mpr hG
  have hGsq : Integrable (fun ξ ↦ ‖G ξ‖ ^ (2 : ℕ)) volume :=
    (memLp_two_iff_integrable_sq hGmeas.norm).mp hGnorm
  have hbound : Integrable (fun ξ ↦ 4 * ‖G ξ‖ ^ (2 : ℕ)) volume :=
    hGsq.const_mul 4
  have hInt : Tendsto (fun N ↦ ∫ ξ : ℝ, ‖R N ξ * G ξ‖ ^ (2 : ℕ))
      atTop (𝓝 0) := by
    have hdom := tendsto_integral_of_dominated_convergence
      (μ := volume) (F := fun N ξ ↦ ‖R N ξ * G ξ‖ ^ (2 : ℕ))
      (f := fun _ : ℝ ↦ (0 : ℝ)) (fun ξ ↦ 4 * ‖G ξ‖ ^ (2 : ℕ))
      (fun N ↦ (hRmem N).aestronglyMeasurable.norm.pow 2) hbound ?_ ?_
    · simpa using hdom
    · intro N
      filter_upwards with ξ
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have hnorm : ‖R N ξ * G ξ‖ ≤ 2 * ‖G ξ‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hRbound N ξ) (norm_nonneg _)
      calc
        ‖R N ξ * G ξ‖ ^ 2 ≤ (2 * ‖G ξ‖) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm
        _ = 4 * ‖G ξ‖ ^ 2 := by ring
    · filter_upwards with ξ
      have hprod : Tendsto (fun N ↦ R N ξ * G ξ) atTop (𝓝 (0 : ℂ)) := by
        simpa using (hRlim ξ).mul tendsto_const_nhds
      have hnormlim : Tendsto (fun N ↦ ‖R N ξ * G ξ‖) atTop (𝓝 0) := by
        simpa [Function.comp_def] using (continuous_norm.tendsto (0 : ℂ)).comp hprod
      simpa using hnormlim.pow 2
  have hpow : Tendsto
      (fun N ↦ (∫ ξ : ℝ, ‖R N ξ * G ξ‖ ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹))
      atTop (𝓝 0) := by
    convert
      ((Real.continuous_rpow_const
        (by norm_num : 0 ≤ (2 : ℝ)⁻¹)).tendsto 0).comp hInt using 1 <;>
      simp [Function.comp_def, Real.zero_rpow]
  have henn : Tendsto
      (fun N ↦ ENNReal.ofReal
        ((∫ ξ : ℝ, ‖R N ξ * G ξ‖ ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹)))
      atTop (𝓝 0) := by
    convert (ENNReal.continuous_ofReal.tendsto 0).comp hpow using 1 <;>
      simp [Function.comp_def]
  refine henn.congr' ?_
  filter_upwards with N
  convert ((hRmem N).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top).symm using 1;
    norm_num [Real.rpow_two]

/-- The shrinking low-frequency remainder multiplier tends to zero against
every `L²` function.  This is the analytic convergence input for
`dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_tendsto_lowFrequencyResidual_multiplier
    (G : ℝ → ℂ) (hG : MemLp G 2 volume) :
    Tendsto (fun N : ℕ ↦
      eLpNorm (fun ξ ↦
        ((1 : ℂ) - (lowFrequencyCutoff (ξ / (2 : ℝ) ^ N) : ℂ)) * G ξ)
        2 volume) atTop (𝓝 0) := by
  let R : ℕ → ℝ → ℂ := fun N ξ ↦
    (1 : ℂ) - (lowFrequencyCutoff (ξ / (2 : ℝ) ^ N) : ℂ)
  have hRcont : ∀ N, Continuous (R N) := by
    intro N
    have hscale : Continuous (fun ξ : ℝ ↦ ξ / (2 : ℝ) ^ N) := by
      exact continuous_id.div_const _
    exact continuous_const.sub
      (Complex.continuous_ofReal.comp (aux_continuous_lowFrequencyCutoff.comp hscale))
  have hRbound : ∀ N ξ, ‖R N ξ‖ ≤ 2 := by
    intro N ξ
    have hηnonneg : 0 ≤ lowFrequencyCutoff (ξ / (2 : ℝ) ^ N) :=
      (aux_smoothStep_nonneg_le_one _).1
    have hηle : lowFrequencyCutoff (ξ / (2 : ℝ) ^ N) ≤ 1 :=
      (aux_smoothStep_nonneg_le_one _).2
    have hηnorm : ‖(lowFrequencyCutoff (ξ / (2 : ℝ) ^ N) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hηnonneg]
      exact hηle
    calc
      ‖R N ξ‖ ≤ ‖(1 : ℂ)‖ + ‖(lowFrequencyCutoff (ξ / (2 : ℝ) ^ N) : ℂ)‖ :=
        norm_sub_le _ _
      _ = 1 + ‖(lowFrequencyCutoff (ξ / (2 : ℝ) ^ N) : ℂ)‖ := by norm_num
      _ ≤ 1 + 1 := by gcongr
      _ = 2 := by norm_num
  have hRtop : ∀ N, MemLp (R N) ∞ volume := by
    intro N
    refine memLp_top_of_bound (hRcont N).aestronglyMeasurable 2 ?_
    filter_upwards with ξ
    exact hRbound N ξ
  have hRmem : ∀ N, MemLp (fun ξ ↦ R N ξ * G ξ) 2 volume := by
    intro N
    let : (∞ : ℝ≥0∞).HolderTriple 2 2 := ENNReal.HolderTriple.symm
    exact hG.mul (hRtop N)
  have hRlim : ∀ ξ, Tendsto (fun N ↦ R N ξ) atTop (𝓝 0) := by
    intro ξ
    have hpow : Tendsto (fun N : ℕ ↦ (2 : ℝ) ^ N) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [hpow.eventually_ge_atTop |ξ|] with N hN
    have hpowpos : 0 < (2 : ℝ) ^ N := by positivity
    have hdiv : |ξ / (2 : ℝ) ^ N| ≤ 1 := by
      rw [abs_div, abs_of_nonneg hpowpos.le]
      exact (div_le_one₀ hpowpos).mpr hN
    change (1 : ℂ) - (lowFrequencyCutoff (ξ / (2 : ℝ) ^ N) : ℂ) = 0
    rw [show lowFrequencyCutoff (ξ / (2 : ℝ) ^ N) = 1 by
      exact aux_lowFrequencyCutoff_eq_one_of_abs_le_one hdiv]
    simp
  exact aux_tendsto_eLpNorm_mul_of_bounded_tends_zero G hG R hRmem hRbound hRlim

/-- The finite dyadic reconstruction residual converges to zero in `L²`.
This joins the Plancherel/telescoping reduction with dominated convergence
for `dyadicReconstructionAndMultiplierBounds` and
\(\label{lem:dyadic-reconstruction}\). -/
lemma aux_tendsto_dyadic_reconstruction_residual
    (f : ℝ → ℂ) (hf : MemLp f 2 volume) :
    Tendsto
        (fun N : ℕ ↦
          eLpNorm
            (fun x ↦ f x - P 0 f x - ∑ k ∈ Finset.range N, P (k + 1) f x)
            2 volume)
        atTop (𝓝 0) := by
  have hPzero : MemLp (P 0 f) 2 volume := aux_memLp_P_zero f hf
  have hP : ∀ k : ℕ, MemLp (P (k + 1) f) 2 volume :=
    fun k ↦ aux_memLp_P_succ f hf k
  have hG : MemLp (aux_l2Fourier f) 2 volume := by
    rw [aux_l2Fourier, dite_eq_left hf]
    exact Lp.memLp _
  have hmult := aux_tendsto_lowFrequencyResidual_multiplier (aux_l2Fourier f) hG
  refine hmult.congr' ?_
  filter_upwards with N
  calc
    eLpNorm (fun ξ ↦
        ((1 : ℂ) - (lowFrequencyCutoff (ξ / (2 : ℝ) ^ N) : ℂ)) * aux_l2Fourier f ξ)
        2 volume =
        eLpNorm
          (fun ξ ↦ aux_l2Fourier f ξ - aux_l2Fourier (P 0 f) ξ -
            ∑ k ∈ Finset.range N, aux_l2Fourier (P (k + 1) f) ξ)
          2 volume := by
            symm
            exact eLpNorm_congr_ae (aux_dyadic_residual_fourier_ae f hf N)
    _ = eLpNorm
          (fun x ↦ f x - P 0 f x - ∑ k ∈ Finset.range N, P (k + 1) f x)
          2 volume :=
      (aux_eLpNorm_dyadic_residual_eq_fourier f hf hPzero hP N).symm

/--
The reconstruction, Fourier-support, and multiplier bounds in
\(\label{lem:dyadic-reconstruction}\):
\[
f=P_0f+\sum_{k=1}^\infty P_kf\quad\text{in }L^2(\mathbb R),
\]
\[
\operatorname{supp}\widehat{P_kf}\subset
\{\xi:2^{k-1}\leq|\xi|\leq2^{k+1}\},\qquad Q_kP_kf=P_kf,
\]
and, for \(1\leq p\leq\infty\),
\[
\lVert Q_kf\rVert_p\leq2^6\lVert f\rVert_p.
\]
-/
theorem dyadicReconstructionAndMultiplierBounds (f : ℝ → ℂ) (hf : MemLp f 2 volume) :
    Tendsto
        (fun N : ℕ ↦
          eLpNorm
            (fun x ↦ f x - P 0 f x - ∑ k ∈ Finset.range N, P (k + 1) f x)
            (2 : ℝ≥0∞) volume)
        atTop (𝓝 0) ∧
      (∀ k : ℕ, 1 ≤ k →
        ∀ᵐ ξ ∂volume, aux_l2Fourier (P k f) ξ ≠ 0 →
          (2 : ℝ) ^ (k - 1) ≤ |ξ| ∧ |ξ| ≤ (2 : ℝ) ^ (k + 1)) ∧
      (∀ k : ℕ, 1 ≤ k → Q k (P k f) = P k f) ∧
      ∀ (k : ℕ) (p : ℝ≥0∞), 1 ≤ k → 1 ≤ p →
        eLpNorm (Q k f) p volume ≤ 2 ^ 6 * eLpNorm f p volume := by
  refine ⟨aux_tendsto_dyadic_reconstruction_residual f hf, ?_, ?_, ?_⟩
  · intro k hk
    exact aux_ae_dyadic_support_of_fourier_multiplier hk
      (aux_l2Fourier_P_ae_eq_multiplier f hf k hk)
  · intro k hk
    exact aux_Q_P_eq f hf k hk
  · intro k p _ hp
    exact aux_eLpNorm_Q_le f hf k p hp

end Auto
