import BourgainSmoothing.Auto.DualDifferenceInterchange
import BourgainSmoothing.Auto.ExplicitAuxiliaryCutoffs
import BourgainSmoothing.VanDerCorput

/-!
# Quadratic oscillation and bilinear smoothing

Formalizations of the labeled estimates in the corresponding section of
`blueprint/blueprint.tex`.
-/

noncomputable section

open MeasureTheory Set FourierTransform
open scoped ENNReal Real FourierTransform

namespace Auto

/-- The constant in \(\label{lem:quadratic-oscillatory}\), used by
`quadraticOscillatoryIntegralEstimate`:
\[
C_{\ref{lem:quadratic-oscillatory},\,J,\chi}
:=
2^5\Ssize{J}{\chi}^{2}.
\]
-/
def C_quadraticOscillatoryIntegralEstimate (J : Set ℝ) (χ : ℝ → ℝ) : ℝ :=
  (2 : ℝ) ^ 5 * sizeParameter ![J] χ ^ 2

/-- Places the support of a compactly supported cutoff strictly inside its
support-radius interval. -/
lemma aux_quadratic_support_subset_Ioc_radius (χ : ℝ → ℝ)
    (hχ_compact : HasCompactSupport χ) :
    Function.support χ ⊆ Set.Ioc (-supportRadius χ) (supportRadius χ) := by
  classical
  by_cases hχ : χ = 0
  · simp [hχ]
  intro x hx
  have hxt : x ∈ tsupport χ := subset_tsupport χ hx
  have hmem : |x| ∈ Set.image (fun t : ℝ ↦ |t|) (tsupport χ) := ⟨x, hxt, rfl⟩
  have hbdd : BddAbove (Set.image (fun t : ℝ ↦ |t|) (tsupport χ)) :=
    hχ_compact.image continuous_abs |>.bddAbove
  have hle : |x| ≤ sSup (Set.image (fun t : ℝ ↦ |t|) (tsupport χ)) :=
    le_csSup hbdd hmem
  rw [show supportRadius χ =
      1 + sSup (Set.image (fun t : ℝ ↦ |t|) (tsupport χ)) by simp [supportRadius, hχ]]
  rw [Set.mem_Ioc]
  constructor <;> linarith [le_abs_self x, neg_le_abs x]

/-- Gives the strict support-radius containment needed to vanish at the interval endpoint. -/
lemma aux_quadratic_tsupport_subset_Ioo_radius (χ : ℝ → ℝ)
    (hχ_compact : HasCompactSupport χ) :
    tsupport χ ⊆ Set.Ioo (-supportRadius χ) (supportRadius χ) := by
  classical
  by_cases hχ : χ = 0
  · simp [hχ]
  intro x hx
  have hmem : |x| ∈ Set.image (fun t : ℝ ↦ |t|) (tsupport χ) := ⟨x, hx, rfl⟩
  have hbdd : BddAbove (Set.image (fun t : ℝ ↦ |t|) (tsupport χ)) :=
    hχ_compact.image continuous_abs |>.bddAbove
  have hle : |x| ≤ sSup (Set.image (fun t : ℝ ↦ |t|) (tsupport χ)) :=
    le_csSup hbdd hmem
  rw [show supportRadius χ =
      1 + sSup (Set.image (fun t : ℝ ↦ |t|) (tsupport χ)) by simp [supportRadius, hχ]]
  rw [Set.mem_Ioo]
  constructor <;> linarith [le_abs_self x, neg_le_abs x]

/-- The oscillatory factor does not enlarge the support of the cutoff. -/
lemma aux_quadratic_phase_support_subset (a b : ℝ) (χ : ℝ → ℝ) :
    Function.support (fun t : ℝ ↦ exponential (a * t + b * t ^ 2) * (χ t : ℂ)) ⊆
      Function.support χ := by
  intro t ht hzero
  simp [Function.mem_support, hzero] at ht

/-- Smoothness of the real quadratic phase used in the van der Corput applications. -/
lemma aux_quadratic_phase_smooth (a b : ℝ) :
    ContDiff ℝ ⊤ (fun t : ℝ ↦ 2 * Real.pi * (a * t + b * t ^ 2)) := by
  fun_prop

/-- Computes the ordinary first derivative of the quadratic phase. -/
lemma aux_quadratic_phase_deriv (a b t : ℝ) :
    deriv (fun x : ℝ ↦ 2 * Real.pi * (a * x + b * x ^ 2)) t =
      2 * Real.pi * (a + 2 * b * t) := by
  have hinner : HasDerivAt (fun x : ℝ ↦ a * x + b * x ^ 2) (a + 2 * b * t) t := by
    have hax : HasDerivAt (fun x : ℝ ↦ a * x) a t := by
      have hax0 := (hasDerivAt_const (x := t) (c := a)).mul (hasDerivAt_id t)
      change HasDerivAt (fun x : ℝ ↦ a * x) _ t at hax0
      simpa using hax0
    have hsq : HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * t) t := by
      have hsq0 := (hasDerivAt_id t).pow 2
      change HasDerivAt (fun x : ℝ ↦ x ^ 2) _ t at hsq0
      simpa using hsq0
    have hbx : HasDerivAt (fun x : ℝ ↦ b * x ^ 2) (b * (2 * t)) t := by
      have hbx0 := (hasDerivAt_const (x := t) (c := b)).mul hsq
      change HasDerivAt (fun x : ℝ ↦ b * x ^ 2) _ t at hbx0
      simpa using hbx0
    have hadd := hax.add hbx
    change HasDerivAt (fun x : ℝ ↦ a * x + b * x ^ 2) _ t at hadd
    convert hadd using 1; ring
  exact (hinner.const_mul (2 * Real.pi)).deriv

/-- Computes the derivative of the affine first derivative of the phase. -/
lemma aux_quadratic_phase_second_deriv (a b t : ℝ) :
    deriv (fun x : ℝ ↦ 2 * Real.pi * (a + 2 * b * x)) t =
      4 * Real.pi * b := by
  have hinner : HasDerivAt (fun x : ℝ ↦ a + 2 * b * x) (2 * b) t := by
    have hlin : HasDerivAt (fun x : ℝ ↦ (2 * b) * x) (2 * b) t := by
      have hlin0 := (hasDerivAt_id t).const_mul (2 * b)
      change HasDerivAt (fun x : ℝ ↦ (2 * b) * x) _ t at hlin0
      simpa using hlin0
    have hadd := (hasDerivAt_const (x := t) (c := a)).add hlin
    change HasDerivAt (fun x : ℝ ↦ a + 2 * b * x) _ t at hadd
    simpa using hadd
  have h := hinner.const_mul (2 * Real.pi)
  convert h.deriv using 1; ring

/-- Computes the second iterated ordinary derivative of the quadratic phase. -/
lemma aux_quadratic_phase_iteratedDeriv_two (a b t : ℝ) :
    iteratedDeriv 2 (fun x : ℝ ↦ 2 * Real.pi * (a * x + b * x ^ 2)) t =
      4 * Real.pi * b := by
  let f : ℝ → ℝ := fun x ↦ 2 * Real.pi * (a * x + b * x ^ 2)
  change iteratedDeriv 2 f t = _
  rw [iteratedDeriv_succ]
  rw [iteratedDeriv_one]
  rw [show deriv (fun x : ℝ ↦ 2 * Real.pi * (a * x + b * x ^ 2)) =
      fun x : ℝ ↦ 2 * Real.pi * (a + 2 * b * x) by
        funext x; exact aux_quadratic_phase_deriv a b x]
  exact aux_quadratic_phase_second_deriv a b t

/-- Computes the second derivative within any nondegenerate interval. -/
lemma aux_quadratic_phase_iteratedDerivWithin_two (a b u v t : ℝ) (huv : u ≠ v)
    (ht : t ∈ Set.uIcc u v) :
    iteratedDerivWithin 2 (fun x : ℝ ↦ 2 * Real.pi * (a * x + b * x ^ 2)) (Set.uIcc u v) t =
      4 * Real.pi * b := by
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc huv)
    ((aux_quadratic_phase_smooth a b).of_le (by norm_num)).contDiffAt ht]
  exact aux_quadratic_phase_iteratedDeriv_two a b t

/-- Computes the first derivative of the phase within a nondegenerate interval. -/
lemma aux_quadratic_phase_derivWithin (a b u v t : ℝ) (huv : u ≠ v)
    (ht : t ∈ Set.uIcc u v) :
    derivWithin (fun x : ℝ ↦ 2 * Real.pi * (a * x + b * x ^ 2)) (Set.uIcc u v) t =
      2 * Real.pi * (a + 2 * b * t) := by
  have hinner : HasDerivAt (fun x : ℝ ↦ a * x + b * x ^ 2) (a + 2 * b * t) t := by
    have hax : HasDerivAt (fun x : ℝ ↦ a * x) a t := by
      have hax0 := (hasDerivAt_const (x := t) (c := a)).mul (hasDerivAt_id t)
      change HasDerivAt (fun x : ℝ ↦ a * x) _ t at hax0
      simpa using hax0
    have hsq : HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * t) t := by
      have hsq0 := (hasDerivAt_id t).pow 2
      change HasDerivAt (fun x : ℝ ↦ x ^ 2) _ t at hsq0
      simpa using hsq0
    have hbx : HasDerivAt (fun x : ℝ ↦ b * x ^ 2) (b * (2 * t)) t := by
      have hbx0 := (hasDerivAt_const (x := t) (c := b)).mul hsq
      change HasDerivAt (fun x : ℝ ↦ b * x ^ 2) _ t at hbx0
      simpa using hbx0
    have hadd := hax.add hbx
    change HasDerivAt (fun x : ℝ ↦ a * x + b * x ^ 2) _ t at hadd
    convert hadd using 1; ring
  have h : HasDerivAt (fun x : ℝ ↦ 2 * Real.pi * (a * x + b * x ^ 2))
      (2 * Real.pi * (a + 2 * b * t)) t := by
    exact (hinner.const_mul (2 * Real.pi))
  exact h.hasDerivWithinAt.derivWithin (uniqueDiffOn_uIcc huv t ht)

/-- Relates the complexified cutoff derivative within the radius interval to its real derivative. -/
lemma aux_quadratic_ofReal_derivWithin_eq (χ : ℝ → ℝ) (hχ_smooth : ContDiff ℝ ⊤ χ)
    (r t : ℝ) (hr : 0 < r) (ht : t ∈ Set.uIcc (-r) r) :
    derivWithin (fun x : ℝ ↦ (χ x : ℂ)) (Set.uIcc (-r) r) t =
      ((deriv (𝕜 := ℝ) χ t : ℝ) : ℂ) := by
  have hderiv : HasDerivAt (fun x : ℝ ↦ (χ x : ℂ)) ((deriv (𝕜 := ℝ) χ t : ℝ) : ℂ) t := by
    exact ((hχ_smooth.differentiable (by norm_num) t).hasDerivAt).ofReal_comp
  exact hderiv.hasDerivWithinAt.derivWithin (uniqueDiffOn_uIcc (by linarith) t ht)

/-- Identifies the variation term in van der Corput with the cutoff's global
`L¹` derivative norm. -/
lemma aux_quadratic_deriv_norm_interval_eq_eLpNorm_one (χ : ℝ → ℝ)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ) :
    |∫ t in -supportRadius χ..supportRadius χ,
      ‖derivWithin (fun x : ℝ ↦ (χ x : ℂ))
        (Set.uIcc (-supportRadius χ) (supportRadius χ)) t‖| =
      (eLpNorm (deriv (𝕜 := ℝ) χ) (1 : ℝ≥0∞) volume).toReal := by
  let r : ℝ := supportRadius χ
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one (aux_u3_one_le_supportRadius χ hχ_compact)
  have htsupp : tsupport χ ⊆ Set.Ioc (-r) r := by
    simpa [r] using
      aux_quadratic_tsupport_subset_Ioo_radius χ hχ_compact |>.trans Set.Ioo_subset_Ioc_self
  have hder_supp : Function.support (fun t : ℝ ↦ |deriv (𝕜 := ℝ) χ t|) ⊆ Set.Ioc (-r) r := by
    intro t ht
    apply htsupp
    apply support_deriv_subset
    simpa [Function.mem_support] using ht
  have hdermem : MemLp (deriv (𝕜 := ℝ) χ) (1 : ℝ≥0∞) volume :=
    (hχ_smooth.continuous_deriv (by norm_num)).memLp_of_hasCompactSupport hχ_compact.deriv
  have hinterval :
      (∫ t in -r..r, ‖derivWithin (fun x : ℝ ↦ (χ x : ℂ)) (Set.uIcc (-r) r) t‖) =
        ∫ t in -r..r, |deriv (𝕜 := ℝ) χ t| := by
    apply intervalIntegral.integral_congr_ae_restrict
    apply ae_restrict_of_forall_mem measurableSet_uIoc
    intro t ht
    have htu : t ∈ Set.uIcc (-r) r := Set.uIoc_subset_uIcc ht
    change ‖derivWithin (fun x : ℝ ↦ (χ x : ℂ)) (Set.uIcc (-r) r) t‖ = _
    rw [aux_quadratic_ofReal_derivWithin_eq χ hχ_smooth r t hr htu]
    simp [Real.norm_eq_abs]
  have hglobal : (∫ t in -r..r, |deriv (𝕜 := ℝ) χ t|) =
      ∫ t : ℝ, |deriv (𝕜 := ℝ) χ t| :=
    intervalIntegral.integral_eq_integral_of_support_subset hder_supp
  have hnonneg : 0 ≤ ∫ t in -r..r, ‖derivWithin (fun x : ℝ ↦ (χ x : ℂ))
      (Set.uIcc (-r) r) t‖ := by
    rw [hinterval, hglobal]
    exact integral_nonneg fun _ ↦ abs_nonneg _
  rw [show -supportRadius χ = -r by rfl, show supportRadius χ = r by rfl,
    abs_of_nonneg hnonneg, hinterval, hglobal]
  calc
    ∫ t : ℝ, |deriv (𝕜 := ℝ) χ t| = ∫ t : ℝ, ‖deriv (𝕜 := ℝ) χ t‖ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [Real.norm_eq_abs]
    _ = lpNorm (deriv (𝕜 := ℝ) χ) 1 volume :=
      (lpNorm_one_eq_integral_norm hdermem.aestronglyMeasurable).symm
    _ = _ := (toReal_eLpNorm hdermem.aestronglyMeasurable).symm

/-- Applies second-order van der Corput to the quadratic phase for
`quadraticOscillatoryIntegralEstimate`. -/
lemma aux_quadratic_vdc_order_two (χ : ℝ → ℝ)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (a b : ℝ) (hb : b ≠ 0) :
    ‖∫ t : ℝ, exponential (a * t + b * t ^ 2) * (χ t : ℂ)‖ ≤
      8 * (2 * Real.pi * |b|) ^ (-(1 / 2 : ℝ)) *
        (eLpNorm (deriv (𝕜 := ℝ) χ) (1 : ℝ≥0∞) volume).toReal := by
  let r : ℝ := supportRadius χ
  let φ : ℝ → ℝ := fun t ↦ 2 * Real.pi * (a * t + b * t ^ 2)
  let ψ : ℝ → ℂ := fun t ↦ (χ t : ℂ)
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one (aux_u3_one_le_supportRadius χ hχ_compact)
  have hsupportχ : Function.support χ ⊆ Set.Ioc (-r) r := by
    simpa [r] using aux_quadratic_support_subset_Ioc_radius χ hχ_compact
  have hsupport : Function.support (fun t : ℝ ↦ Complex.exp (φ t * Complex.I) • ψ t) ⊆
      Set.Ioc (-r) r := by
    change Function.support (fun t : ℝ ↦ exponential (a * t + b * t ^ 2) * (χ t : ℂ)) ⊆ _
    exact (aux_quadratic_phase_support_subset a b χ).trans hsupportχ
  have hintegral : (∫ t in -r..r, Complex.exp (φ t * Complex.I) • ψ t) =
      ∫ t : ℝ, exponential (a * t + b * t ^ 2) * (χ t : ℂ) :=
    intervalIntegral.integral_eq_integral_of_support_subset hsupport
  have hφ : ContDiffOn ℝ 2 φ (Set.uIcc (-r) r) := by
    exact ((aux_quadratic_phase_smooth a b).of_le (by norm_num)).contDiffOn
  have hψ : ContDiffOn ℝ 1 ψ (Set.uIcc (-r) r) := by
    change ContDiffOn ℝ 1 (Complex.ofRealCLM ∘ χ) _
    exact (Complex.ofRealCLM.contDiff.comp hχ_smooth).of_le (by norm_num) |>.contDiffOn
  have hL : 0 < 2 * Real.pi * |b| := by positivity
  have hderiv : ∀ x ∈ Set.uIcc (-r) r,
      2 * Real.pi * |b| ≤ |iteratedDerivWithin 2 φ (Set.uIcc (-r) r) x| := by
    intro x hx
    change 2 * Real.pi * |b| ≤
      |iteratedDerivWithin 2 (fun t : ℝ ↦ 2 * Real.pi * (a * t + b * t ^ 2))
        (Set.uIcc (-r) r) x|
    rw [aux_quadratic_phase_iteratedDerivWithin_two a b (-r) r x (by linarith) hx]
    calc
      2 * Real.pi * |b| ≤ 4 * Real.pi * |b| := by
        nlinarith [mul_nonneg Real.pi_pos.le (abs_nonneg b)]
      _ = |4 * Real.pi * b| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
          abs_of_pos Real.pi_pos]
  have hvdc := Oscillatory.norm_integral_exp_mul_I_le_of_order_ge_two
    (a := -r) (b := r) (L := 2 * Real.pi * |b|) (φ := φ) (ψ := ψ)
    (k := 2) (by norm_num) hφ hψ hderiv hL
  have hχr : χ r = 0 := by
    by_contra hrzero
    have hmem : r ∈ Function.support χ := hrzero
    have hts : r ∈ tsupport χ := subset_tsupport χ hmem
    have hstrict := aux_quadratic_tsupport_subset_Ioo_radius χ hχ_compact hts
    have hrr : r < r := by simpa [r] using hstrict.2
    exact lt_irrefl _ hrr
  have hnormderiv := aux_quadratic_deriv_norm_interval_eq_eLpNorm_one χ hχ_smooth hχ_compact
  calc
    ‖∫ t : ℝ, exponential (a * t + b * t ^ 2) * (χ t : ℂ)‖ =
        ‖∫ t in -r..r, Complex.exp (φ t * Complex.I) • ψ t‖ := by
      rw [hintegral]
    _ ≤ Oscillatory.VanDerCorput.c 2 * (2 * Real.pi * |b|) ^ (-1 / (2 : ℝ)) *
        (‖ψ r‖ + |∫ t in -r..r, ‖derivWithin ψ (Set.uIcc (-r) r) t‖|) := hvdc
    _ = 8 * (2 * Real.pi * |b|) ^ (-(1 / 2 : ℝ)) *
        (eLpNorm (deriv (𝕜 := ℝ) χ) (1 : ℝ≥0∞) volume).toReal := by
      rw [show ψ r = 0 by simp [ψ, hχr], norm_zero, zero_add]
      rw [hnormderiv]
      norm_num [Oscillatory.VanDerCorput.c]

/-- Applies first-order van der Corput when the quadratic coefficient is nonnegative. -/
lemma aux_quadratic_vdc_order_one_nonneg_b (χ : ℝ → ℝ)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (a b : ℝ) (ha : a ≠ 0) (hb : 0 ≤ b)
    (hdom : 4 * supportRadius χ * |b| ≤ |a|) :
    ‖∫ t : ℝ, exponential (a * t + b * t ^ 2) * (χ t : ℂ)‖ ≤
      3 * (Real.pi * |a|)⁻¹ *
        (eLpNorm (deriv (𝕜 := ℝ) χ) (1 : ℝ≥0∞) volume).toReal := by
  let r : ℝ := supportRadius χ
  let φ : ℝ → ℝ := fun t ↦ 2 * Real.pi * (a * t + b * t ^ 2)
  let ψ : ℝ → ℂ := fun t ↦ (χ t : ℂ)
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one (aux_u3_one_le_supportRadius χ hχ_compact)
  have hsupportχ : Function.support χ ⊆ Set.Ioc (-r) r := by
    simpa [r] using aux_quadratic_support_subset_Ioc_radius χ hχ_compact
  have hsupport : Function.support (fun t : ℝ ↦ Complex.exp (φ t * Complex.I) • ψ t) ⊆
      Set.Ioc (-r) r := by
    change Function.support (fun t : ℝ ↦ exponential (a * t + b * t ^ 2) * (χ t : ℂ)) ⊆ _
    exact (aux_quadratic_phase_support_subset a b χ).trans hsupportχ
  have hintegral : (∫ t in -r..r, Complex.exp (φ t * Complex.I) • ψ t) =
      ∫ t : ℝ, exponential (a * t + b * t ^ 2) * (χ t : ℂ) :=
    intervalIntegral.integral_eq_integral_of_support_subset hsupport
  have hφ : ContDiffOn ℝ 2 φ (Set.uIcc (-r) r) := by
    exact ((aux_quadratic_phase_smooth a b).of_le (by norm_num)).contDiffOn
  have hψ : ContDiffOn ℝ 1 ψ (Set.uIcc (-r) r) := by
    change ContDiffOn ℝ 1 (Complex.ofRealCLM ∘ χ) _
    exact (Complex.ofRealCLM.contDiff.comp hχ_smooth).of_le (by norm_num) |>.contDiffOn
  have hL : 0 < Real.pi * |a| := by positivity
  have hderiv : ∀ x ∈ Set.uIcc (-r) r,
      Real.pi * |a| ≤ |derivWithin φ (Set.uIcc (-r) r) x| := by
    intro x hx
    have hx' : -r ≤ x ∧ x ≤ r := by
      rwa [Set.uIcc_of_le (by linarith)] at hx
    have hxabs : |x| ≤ r := abs_le.2 hx'
    have hterm : |2 * b * x| ≤ 2 * |b| * r := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left hxabs (by positivity)
    have htri : |a| ≤ |a + 2 * b * x| + |2 * b * x| := by
      calc
        |a| = |(a + 2 * b * x) + -(2 * b * x)| := by congr 1; ring
        _ ≤ _ := by simpa using abs_add_le (a + 2 * b * x) (-(2 * b * x))
    have hhalf : |a| / 2 ≤ |a + 2 * b * x| := by
      have hdom' : 2 * |b| * r ≤ |a| / 2 := by
        dsimp [r] at hdom ⊢
        nlinarith
      linarith
    change Real.pi * |a| ≤
      |derivWithin (fun t : ℝ ↦ 2 * Real.pi * (a * t + b * t ^ 2))
        (Set.uIcc (-r) r) x|
    rw [aux_quadratic_phase_derivWithin a b (-r) r x (by linarith) hx]
    calc
      Real.pi * |a| = 2 * Real.pi * (|a| / 2) := by ring
      _ ≤ 2 * Real.pi * |a + 2 * b * x| :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)
      _ = |2 * Real.pi * (a + 2 * b * x)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_pos Real.pi_pos]
  have hmono : MonotoneOn (derivWithin φ (Set.uIcc (-r) r)) (Set.uIcc (-r) r) := by
    intro x hx y hy hxy
    change derivWithin (fun t : ℝ ↦ 2 * Real.pi * (a * t + b * t ^ 2))
        (Set.uIcc (-r) r) x ≤
      derivWithin (fun t : ℝ ↦ 2 * Real.pi * (a * t + b * t ^ 2))
        (Set.uIcc (-r) r) y
    rw [aux_quadratic_phase_derivWithin a b (-r) r x (by linarith) hx,
      aux_quadratic_phase_derivWithin a b (-r) r y (by linarith) hy]
    have hlin : a + 2 * b * x ≤ a + 2 * b * y := by nlinarith
    exact mul_le_mul_of_nonneg_left hlin (by positivity)
  have hvdc := Oscillatory.norm_integral_exp_mul_I_le_of_order_one
    (a := -r) (b := r) (L := Real.pi * |a|) (φ := φ) (ψ := ψ)
    hφ hψ hderiv hmono hL
  have hχr : χ r = 0 := by
    by_contra hrzero
    have hmem : r ∈ Function.support χ := hrzero
    have hts : r ∈ tsupport χ := subset_tsupport χ hmem
    have hstrict := aux_quadratic_tsupport_subset_Ioo_radius χ hχ_compact hts
    have hrr : r < r := by simpa [r] using hstrict.2
    exact lt_irrefl _ hrr
  have hnormderiv := aux_quadratic_deriv_norm_interval_eq_eLpNorm_one χ hχ_smooth hχ_compact
  calc
    ‖∫ t : ℝ, exponential (a * t + b * t ^ 2) * (χ t : ℂ)‖ =
        ‖∫ t in -r..r, Complex.exp (φ t * Complex.I) • ψ t‖ := by
      rw [hintegral]
    _ ≤ Oscillatory.VanDerCorput.c 1 * (Real.pi * |a|)⁻¹ *
        (‖ψ r‖ + |∫ t in -r..r, ‖derivWithin ψ (Set.uIcc (-r) r) t‖|) := hvdc
    _ = 3 * (Real.pi * |a|)⁻¹ *
        (eLpNorm (deriv (𝕜 := ℝ) χ) (1 : ℝ≥0∞) volume).toReal := by
      rw [show ψ r = 0 by simp [ψ, hχr], norm_zero, zero_add]
      rw [hnormderiv]
      norm_num [Oscillatory.VanDerCorput.c]

/-- Transfers a quadratic oscillatory integral to the negated phase by complex conjugation. -/
lemma aux_quadratic_integral_neg_coeff_norm (χ : ℝ → ℝ) (a b : ℝ) :
    ‖∫ t : ℝ, exponential (a * t + b * t ^ 2) * (χ t : ℂ)‖ =
      ‖∫ t : ℝ, exponential ((-a) * t + (-b) * t ^ 2) * (χ t : ℂ)‖ := by
  let f : ℝ → ℂ := fun t ↦ exponential (a * t + b * t ^ 2) * (χ t : ℂ)
  let g : ℝ → ℂ := fun t ↦ exponential ((-a) * t + (-b) * t ^ 2) * (χ t : ℂ)
  have hpoint (t : ℝ) : starRingEnd ℂ (f t) = g t := by
    dsimp [f, g]
    rw [map_mul, aux_phase_star_exponential]
    rw [Complex.conj_ofReal]
    congr 1
    ring_nf
  have hconj : starRingEnd ℂ (∫ t : ℝ, f t) = ∫ t : ℝ, g t := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards with t
    exact hpoint t
  calc
    ‖∫ t : ℝ, exponential (a * t + b * t ^ 2) * (χ t : ℂ)‖ = ‖∫ t : ℝ, f t‖ := rfl
    _ = ‖starRingEnd ℂ (∫ t : ℝ, f t)‖ := (norm_star _).symm
    _ = ‖∫ t : ℝ, g t‖ := by rw [hconj]
    _ = _ := rfl

/-- Extends the first-order quadratic van der Corput bound to either sign of
the quadratic coefficient. -/
lemma aux_quadratic_vdc_order_one (χ : ℝ → ℝ)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (a b : ℝ) (ha : a ≠ 0)
    (hdom : 4 * supportRadius χ * |b| ≤ |a|) :
    ‖∫ t : ℝ, exponential (a * t + b * t ^ 2) * (χ t : ℂ)‖ ≤
      3 * (Real.pi * |a|)⁻¹ *
        (eLpNorm (deriv (𝕜 := ℝ) χ) (1 : ℝ≥0∞) volume).toReal := by
  rcases le_total 0 b with hb | hb
  · exact aux_quadratic_vdc_order_one_nonneg_b χ hχ_smooth hχ_compact a b ha hb hdom
  · have hminus : 0 ≤ -b := by linarith
    have hdomminus : 4 * supportRadius χ * |-b| ≤ |-a| := by
      simpa using hdom
    calc
      ‖∫ t : ℝ, exponential (a * t + b * t ^ 2) * (χ t : ℂ)‖ =
          ‖∫ t : ℝ, exponential ((-a) * t + (-b) * t ^ 2) * (χ t : ℂ)‖ :=
        aux_quadratic_integral_neg_coeff_norm χ a b
      _ ≤ 3 * (Real.pi * |-a|)⁻¹ *
          (eLpNorm (deriv (𝕜 := ℝ) χ) (1 : ℝ≥0∞) volume).toReal :=
        aux_quadratic_vdc_order_one_nonneg_b χ hχ_smooth hχ_compact (-a) (-b)
          (neg_ne_zero.mpr ha) hminus hdomminus
      _ = _ := by rw [abs_neg]

/-- Extracts the cutoff and support-radius bounds built into `sizeParameter`. -/
lemma aux_quadratic_size_properties (J : Set ℝ) (χ : ℝ → ℝ) :
    2 ≤ sizeParameter ![J] χ ∧
      0 ≤ sizeParameter ![J] χ ∧
      supportRadius χ ^ 2 ≤ sizeParameter ![J] χ ∧
      (eLpNorm χ (1 : ℝ≥0∞) volume).toReal ≤ sizeParameter ![J] χ ∧
      (eLpNorm (deriv (𝕜 := ℝ) χ) (1 : ℝ≥0∞) volume).toReal ≤ sizeParameter ![J] χ := by
  let T : ℝ := max (supportRadius χ ^ 2)
    (max (eLpNorm χ 1 volume).toReal
      (max (eLpNorm χ 2 volume).toReal
        (max (eLpNorm (deriv (𝕜 := ℝ) χ) 1 volume).toReal
          (eLpNorm (deriv (𝕜 := ℝ) χ) 2 volume).toReal)))
  have hT0 : 0 ≤ T := by
    dsimp [T]
    exact (sq_nonneg _).trans (le_max_left _ _)
  have hT : T ≤ sizeParameter ![J] χ := by
    change T ≤ 2 + max (sSup (Set.range fun i : Fin 1 ↦ intervalLength (![J] i))) T
    nlinarith [le_max_right (sSup (Set.range fun i : Fin 1 ↦ intervalLength (![J] i))) T]
  have hS2 : 2 ≤ sizeParameter ![J] χ := by
    change 2 ≤ 2 + max (sSup (Set.range fun i : Fin 1 ↦ intervalLength (![J] i))) T
    nlinarith [le_max_right (sSup (Set.range fun i : Fin 1 ↦ intervalLength (![J] i))) T]
  have hR : supportRadius χ ^ 2 ≤ T := le_max_left _ _
  have hχ1 : (eLpNorm χ (1 : ℝ≥0∞) volume).toReal ≤ T := by
    dsimp [T]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hd1 : (eLpNorm (deriv (𝕜 := ℝ) χ) (1 : ℝ≥0∞) volume).toReal ≤ T := by
    dsimp [T]
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  exact ⟨hS2, le_trans (by norm_num : (0 : ℝ) ≤ 2) hS2,
    hR.trans hT, hχ1.trans hT, hd1.trans hT⟩

/-- Supplies the low-frequency `L¹` bound used in `quadraticOscillatoryIntegralEstimate`. -/
lemma aux_quadratic_integral_trivial_bound (χ : ℝ → ℝ)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (a b : ℝ) :
    ‖∫ t : ℝ, exponential (a * t + b * t ^ 2) * (χ t : ℂ)‖ ≤
      (eLpNorm χ (1 : ℝ≥0∞) volume).toReal := by
  have hχmem : MemLp χ (1 : ℝ≥0∞) volume :=
    hχ_smooth.continuous.memLp_of_hasCompactSupport hχ_compact
  calc
    ‖∫ t : ℝ, exponential (a * t + b * t ^ 2) * (χ t : ℂ)‖ ≤
        ∫ t : ℝ, ‖exponential (a * t + b * t ^ 2) * (χ t : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ t : ℝ, χ t := by
      apply integral_congr_ae
      filter_upwards with t
      simp [aux_norm_exponential, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hχ_nonneg t)]
    _ = ∫ t : ℝ, ‖χ t‖ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [Real.norm_eq_abs, abs_of_nonneg (hχ_nonneg t)]
    _ = lpNorm χ 1 volume := (lpNorm_one_eq_integral_norm hχmem.aestronglyMeasurable).symm
    _ = _ := (toReal_eLpNorm hχmem.aestronglyMeasurable).symm

/-- Converts the second-order van der Corput bound into the stated explicit quadratic constant. -/
lemma aux_quadratic_b_case_numerical (S A B D : ℝ)
    (hS : 2 ≤ S) (hA : 1 < A) (hB : 0 < B)
    (hD : 0 ≤ D) (hDle : D ≤ S) (hAle : A ≤ 4 * S * B) :
    8 * (2 * Real.pi * B) ^ (-(1 / 2 : ℝ)) * D ≤
      32 * S ^ 2 * (1 + A) ^ (-(1 / 2 : ℝ)) := by
  have hSpos : 0 < S := by linarith
  have hBnonneg : 0 ≤ B := hB.le
  have hX : 0 < 2 * Real.pi * B := by positivity
  have hY : 0 < 1 + A := by linarith
  have hpi : 1 ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hcoeff : 8 * S ≤ 32 * S ^ 2 * Real.pi := by
    calc
      8 * S ≤ 16 * S ^ 2 := by nlinarith
      _ ≤ (16 * S ^ 2) * (2 * Real.pi) :=
        le_mul_of_one_le_right (by positivity) hpi
      _ = 32 * S ^ 2 * Real.pi := by ring
  have hbase : 1 + A ≤ (4 * S) ^ 2 * (2 * Real.pi * B) := by
    calc
      1 + A ≤ 2 * A := by linarith
      _ ≤ 8 * S * B := by nlinarith [hAle]
      _ ≤ 32 * S ^ 2 * Real.pi * B :=
        mul_le_mul_of_nonneg_right hcoeff hBnonneg
      _ = (4 * S) ^ 2 * (2 * Real.pi * B) := by ring
  have hsquare : (Real.sqrt (1 + A)) ^ 2 ≤
      (4 * S * Real.sqrt (2 * Real.pi * B)) ^ 2 := by
    rw [Real.sq_sqrt hY.le]
    calc
      1 + A ≤ (4 * S) ^ 2 * (2 * Real.pi * B) := hbase
      _ = (4 * S * Real.sqrt (2 * Real.pi * B)) ^ 2 := by
        conv_rhs => rw [mul_pow]
        rw [Real.sq_sqrt hX.le]
  have hsqrt : Real.sqrt (1 + A) ≤ 4 * S * Real.sqrt (2 * Real.pi * B) := by
    by_contra h
    have hgt : 4 * S * Real.sqrt (2 * Real.pi * B) < Real.sqrt (1 + A) :=
      lt_of_not_ge h
    have hright : 0 ≤ 4 * S * Real.sqrt (2 * Real.pi * B) := by positivity
    have hleft : 0 < Real.sqrt (1 + A) := Real.sqrt_pos.mpr hY
    have hprod : 0 < (Real.sqrt (1 + A) - 4 * S * Real.sqrt (2 * Real.pi * B)) *
        (Real.sqrt (1 + A) + 4 * S * Real.sqrt (2 * Real.pi * B)) :=
      mul_pos (sub_pos.mpr hgt) (add_pos_of_pos_of_nonneg hleft hright)
    nlinarith
  have hinv : 1 / Real.sqrt (2 * Real.pi * B) ≤
      (4 * S) / Real.sqrt (1 + A) := by
    apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hX) (Real.sqrt_pos.mpr hY)).mpr
    simpa [mul_comm] using hsqrt
  have hp : (2 * Real.pi * B) ^ (-(1 / 2 : ℝ)) =
      1 / Real.sqrt (2 * Real.pi * B) := by
    rw [Real.rpow_neg hX.le]
    rw [← Real.sqrt_eq_rpow]
    simp
  have hq : (1 + A) ^ (-(1 / 2 : ℝ)) =
      1 / Real.sqrt (1 + A) := by
    rw [Real.rpow_neg hY.le]
    rw [← Real.sqrt_eq_rpow]
    simp
  rw [hp, hq]
  calc
    8 * (1 / Real.sqrt (2 * Real.pi * B)) * D ≤
        8 * ((4 * S) / Real.sqrt (1 + A)) * S := by
      gcongr
    _ = 32 * S ^ 2 * (1 / Real.sqrt (1 + A)) := by ring

/-- Converts the first-order van der Corput bound into the stated explicit quadratic constant. -/
lemma aux_quadratic_a_case_numerical (S A D : ℝ)
    (hS : 2 ≤ S) (hA : 1 < A)
    (hD : 0 ≤ D) (hDle : D ≤ S) :
    3 * (Real.pi * A)⁻¹ * D ≤
      32 * S ^ 2 * (1 + A) ^ (-(1 / 2 : ℝ)) := by
  have hSpos : 0 < S := by linarith
  have hApos : 0 < A := by linarith
  have hY : 0 < 1 + A := by linarith
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hsquare : (Real.sqrt (1 + A)) ^ 2 ≤ (2 * A) ^ 2 := by
    rw [Real.sq_sqrt hY.le]
    nlinarith
  have hsqrt : Real.sqrt (1 + A) ≤ 2 * A := by
    by_contra h
    have hgt : 2 * A < Real.sqrt (1 + A) := lt_of_not_ge h
    have hright : 0 ≤ 2 * A := by positivity
    have hleft : 0 < Real.sqrt (1 + A) := Real.sqrt_pos.mpr hY
    have hprod : 0 < (Real.sqrt (1 + A) - 2 * A) *
        (Real.sqrt (1 + A) + 2 * A) :=
      mul_pos (sub_pos.mpr hgt) (add_pos_of_pos_of_nonneg hleft hright)
    nlinarith
  have hinv : A⁻¹ ≤ 2 / Real.sqrt (1 + A) := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hApos (Real.sqrt_pos.mpr hY)).mpr
    simpa [mul_comm] using hsqrt
  have hpiinv : (Real.pi * A)⁻¹ ≤ A⁻¹ := by
    apply (inv_le_inv₀ (mul_pos Real.pi_pos hApos) hApos).mpr
    calc
      A = 1 * A := by ring
      _ ≤ Real.pi * A := mul_le_mul_of_nonneg_right hpi hApos.le
  have hq : (1 + A) ^ (-(1 / 2 : ℝ)) =
      1 / Real.sqrt (1 + A) := by
    rw [Real.rpow_neg hY.le]
    rw [← Real.sqrt_eq_rpow]
    simp
  rw [hq]
  calc
    3 * (Real.pi * A)⁻¹ * D ≤ 3 * (2 / Real.sqrt (1 + A)) * S := by
      have hinv' : (Real.pi * A)⁻¹ ≤ 2 / Real.sqrt (1 + A) := hpiinv.trans hinv
      have hprod : (Real.pi * A)⁻¹ * D ≤ (2 / Real.sqrt (1 + A)) * S :=
        mul_le_mul hinv' hDle hD (by positivity)
      calc
        3 * (Real.pi * A)⁻¹ * D = 3 * ((Real.pi * A)⁻¹ * D) := by ring
        _ ≤ 3 * ((2 / Real.sqrt (1 + A)) * S) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = 3 * (2 / Real.sqrt (1 + A)) * S := by ring
    _ = (6 * S) * (1 / Real.sqrt (1 + A)) := by ring
    _ ≤ (32 * S ^ 2) * (1 / Real.sqrt (1 + A)) := by
      apply mul_le_mul_of_nonneg_right
      · nlinarith
      · positivity
    _ = 32 * S ^ 2 * (1 / Real.sqrt (1 + A)) := by ring

/-- Converts the trivial bound into the stated explicit constant at small frequency. -/
lemma aux_quadratic_small_case_numerical (S A D : ℝ)
    (hS : 2 ≤ S) (hA0 : 0 ≤ A) (hA : A ≤ 1)
    (_hD : 0 ≤ D) (hDle : D ≤ S) :
    D ≤ 32 * S ^ 2 * (1 + A) ^ (-(1 / 2 : ℝ)) := by
  have hSpos : 0 < S := by linarith
  have hYnonneg : 0 ≤ 1 + A := by linarith
  have hYpos : 0 < 1 + A := by linarith
  have hYle : 1 + A ≤ 2 := by linarith
  have hsqrt : Real.sqrt (1 + A) ≤ 2 := by
    have : Real.sqrt (1 + A) ≤ Real.sqrt (2 : ℝ) := Real.sqrt_le_sqrt hYle
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hrootpos : 0 < Real.sqrt (1 + A) := Real.sqrt_pos.mpr hYpos
  have hhalf : (1 / 2 : ℝ) ≤ 1 / Real.sqrt (1 + A) := by
    apply (div_le_div_iff₀ (by norm_num) hrootpos).mpr
    nlinarith
  have hq : (1 + A) ^ (-(1 / 2 : ℝ)) =
      1 / Real.sqrt (1 + A) := by
    rw [Real.rpow_neg hYnonneg]
    rw [← Real.sqrt_eq_rpow]
    simp
  rw [hq]
  calc
    D ≤ S := hDle
    _ ≤ 16 * S ^ 2 := by nlinarith
    _ = 32 * S ^ 2 * (1 / 2 : ℝ) := by ring
    _ ≤ 32 * S ^ 2 * (1 / Real.sqrt (1 + A)) :=
      mul_le_mul_of_nonneg_left hhalf (by positivity)

/--
Let \(J\) be a compact interval containing \(\supp\chi\). Define
\[
C_{\ref{lem:quadratic-oscillatory},\,J,\chi}
:=
2^5\Ssize{J}{\chi}^{2}.
\]
For every \(a,b\in\mathbb R\),
\[
\left|
\int_\mathbb R e(at+bt^2)\chi(t)\,dt
\right|
\leq
C_{\ref{lem:quadratic-oscillatory},\,J,\chi}
\bigl(1+\max\{|a|,|b|\}\bigr)^{-1/2}.
\]
-/
theorem quadraticOscillatoryIntegralEstimate
    (J : Set ℝ) (χ : ℝ → ℝ)
    (_hJ : ∃ jMinus jPlus : ℝ, jMinus ≤ jPlus ∧ J = Set.Icc jMinus jPlus)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (_hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (_hχ_support : tsupport χ ⊆ J) (a b : ℝ) :
    ‖∫ t : ℝ, exponential (a * t + b * t ^ 2) * (χ t : ℂ)‖ ≤
      C_quadraticOscillatoryIntegralEstimate J χ *
        (1 + max |a| |b|) ^ (-(1 / 2 : ℝ)) := by
  let S : ℝ := sizeParameter ![J] χ
  let A : ℝ := max |a| |b|
  let I : ℝ := ‖∫ t : ℝ, exponential (a * t + b * t ^ 2) * (χ t : ℂ)‖
  let D : ℝ := (eLpNorm (deriv (𝕜 := ℝ) χ) (1 : ℝ≥0∞) volume).toReal
  have hSdata := aux_quadratic_size_properties J χ
  have hS : 2 ≤ S := by simpa [S] using hSdata.1
  have hS0 : 0 ≤ S := by simpa [S] using hSdata.2.1
  have hR2 : supportRadius χ ^ 2 ≤ S := by simpa [S] using hSdata.2.2.1
  have hχ1 : (eLpNorm χ (1 : ℝ≥0∞) volume).toReal ≤ S := by
    simpa [S] using hSdata.2.2.2.1
  have hDle : D ≤ S := by simpa [D, S] using hSdata.2.2.2.2
  have hRone : 1 ≤ supportRadius χ := aux_u3_one_le_supportRadius χ hχ_compact
  have hRle : supportRadius χ ≤ S := by
    have hsquare : supportRadius χ ≤ supportRadius χ ^ 2 := by nlinarith
    exact hsquare.trans hR2
  have hI0 : 0 ≤ I := norm_nonneg _
  have hItriv : I ≤ S := by
    calc
      I ≤ (eLpNorm χ (1 : ℝ≥0∞) volume).toReal :=
        aux_quadratic_integral_trivial_bound χ hχ_smooth hχ_compact hχ_nonneg a b
      _ ≤ S := hχ1
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  change I ≤ C_quadraticOscillatoryIntegralEstimate J χ *
    (1 + max |a| |b|) ^ (-(1 / 2 : ℝ))
  rw [C_quadraticOscillatoryIntegralEstimate,
    show sizeParameter ![J] χ = S by rfl,
    show max |a| |b| = A by rfl]
  norm_num
  by_cases hAsmall : A ≤ 1
  · exact aux_quadratic_small_case_numerical S A I hS hA0 hAsmall hI0 hItriv
  have hA : 1 < A := lt_of_not_ge hAsmall
  by_cases hdom : 4 * supportRadius χ * |b| ≤ |a|
  · have hb_le_a : |b| ≤ |a| := by
      have hmul : |b| ≤ 4 * supportRadius χ * |b| := by
        have hcoef : 1 ≤ 4 * supportRadius χ := by nlinarith
        exact le_mul_of_one_le_left (abs_nonneg b) hcoef
      exact hmul.trans hdom
    have hAeq : A = |a| := by
      dsimp [A]
      exact max_eq_left hb_le_a
    have ha : a ≠ 0 := by
      intro ha
      have hzero : A = 0 := by
        rw [hAeq, ha]
        simp
      linarith
    have hfirst := aux_quadratic_vdc_order_one χ hχ_smooth hχ_compact a b ha hdom
    have hfirst' : I ≤ 3 * (Real.pi * |a|)⁻¹ * D := by
      simpa [I, D] using hfirst
    have hnum := aux_quadratic_a_case_numerical S |a| D hS
      (by simpa [hAeq] using hA) (by positivity) hDle
    calc
      I ≤ 3 * (Real.pi * |a|)⁻¹ * D := hfirst'
      _ ≤ 32 * S ^ 2 * (1 + |a|) ^ (-(1 / 2 : ℝ)) := hnum
      _ = 32 * S ^ 2 * (1 + A) ^ (-(1 / 2 : ℝ)) := by rw [hAeq]
  · have hdomlt : |a| < 4 * supportRadius χ * |b| := lt_of_not_ge hdom
    have hbpos : 0 < |b| := by
      by_contra hbzero
      have hbzero' : |b| = 0 := le_antisymm (le_of_not_gt hbzero) (abs_nonneg _)
      have : 4 * supportRadius χ * |b| ≤ |a| := by
        rw [hbzero']
        simp
      exact hdom this
    have hAle : A ≤ 4 * S * |b| := by
      dsimp [A]
      apply max_le
      · exact hdomlt.le.trans <| mul_le_mul_of_nonneg_right
          (by nlinarith [hRle]) (abs_nonneg b)
      · have hcoef : 1 ≤ 4 * S := by nlinarith
        exact le_mul_of_one_le_left (abs_nonneg b) hcoef
    have hsecond := aux_quadratic_vdc_order_two χ hχ_smooth hχ_compact a b
      (by
        intro hbzero
        simp [hbzero] at hbpos)
    have hsecond' : I ≤ 8 * (2 * Real.pi * |b|) ^ (-(1 / 2 : ℝ)) * D := by
      simpa [I, D] using hsecond
    exact hsecond'.trans (aux_quadratic_b_case_numerical S A |b| D hS hA hbpos
      (by positivity) hDle hAle)

/-- The constant in \(\label{prop:bilinear-sobolev}\), used by
`bilinearSobolevEstimates`:
\[
C_{\ref{prop:bilinear-sobolev},\,J,\chi}
:=
2^5\Ssize{J}{\chi}^{2}.
\]
-/
def C_bilinearSobolevEstimates (J : Set ℝ) (χ : ℝ → ℝ) : ℝ :=
  (2 : ℝ) ^ 5 * sizeParameter ![J] χ ^ 2

/-- The Bochner `L²` operator for the translation curves used in
`bilinearSobolevEstimates`. -/
noncomputable def aux_bilinear_shiftOperator
    (τ : ℝ → ℝ) (κ : ℝ → ℂ) (g : Lp (α := ℝ) ℂ 2 volume) :
    Lp (α := ℝ) ℂ 2 volume :=
  ∫ t : ℝ, κ t • aux_l2Translate (τ t) g

/-- A continuous translation curve is continuous as an `L²`-valued map; this
provides Bochner measurability for `bilinearSobolevEstimates`. -/
lemma aux_bilinear_continuous_shift_l2Translate
    (τ : ℝ → ℝ) (hτ : Continuous τ)
    (g : Lp (α := ℝ) ℂ 2 volume) :
    Continuous (fun t : ℝ ↦ aux_l2Translate (τ t) g) := by
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  exact (aux_continuous_lpTranslation g).comp hτ

/-- An integrable scalar kernel makes a continuous translated `L²` curve
Bochner integrable; used in `bilinearSobolevEstimates`. -/
lemma aux_bilinear_weighted_shift_l2Translate_integrable
    (τ : ℝ → ℝ) (hτ : Continuous τ)
    (κ : ℝ → ℂ) (g : Lp (α := ℝ) ℂ 2 volume)
    (hκ : Integrable κ volume) :
    Integrable (fun t : ℝ ↦ κ t • aux_l2Translate (τ t) g) volume := by
  apply Integrable.mono' (hκ.norm.smul_const ‖g‖)
    (continuous_smul.comp_aestronglyMeasurable₂ hκ.aestronglyMeasurable
      (aux_bilinear_continuous_shift_l2Translate τ hτ g).aestronglyMeasurable)
  filter_upwards with t
  unfold aux_l2Translate
  rw [norm_smul, DomAddAct.norm_vadd_Lp]
  simp only [smul_eq_mul]
  exact le_rfl

/-- Scalarizing the shifted Bochner operator gives its iterated `L²`
pairing.  This is the physical-side bridge for `bilinearSobolevEstimates`. -/
lemma aux_bilinear_inner_star_shiftOperator_eq_iterated
    (τ : ℝ → ℝ) (hτ : Continuous τ)
    (κ f g : ℝ → ℂ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hκ : Integrable κ volume) :
    inner ℂ (star (hg.toLp g))
      (aux_bilinear_shiftOperator τ κ (hf.toLp f)) =
      ∫ t : ℝ, ∫ y : ℝ, g y * (κ t * f (y - τ t)) := by
  let L : Lp (α := ℝ) ℂ 2 volume →L[ℂ] ℂ :=
    (innerSL ℂ) (star (hg.toLp g))
  have hB := aux_bilinear_weighted_shift_l2Translate_integrable τ hτ κ (hf.toLp f) hκ
  change L (∫ t : ℝ, κ t • aux_l2Translate (τ t) (hf.toLp f)) = _
  rw [← L.integral_comp_comm hB]
  apply integral_congr_ae
  filter_upwards with t
  change inner ℂ (star (hg.toLp g))
      (κ t • aux_l2Translate (τ t) (hf.toLp f)) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star (hg.toLp g), hg.coeFn_toLp,
    Lp.coeFn_smul (κ t) (aux_l2Translate (τ t) (hf.toLp f)),
    aux_coe_lpTranslation_ae f hf (τ t)] with y hstar hg' hsmul htrans
  rw [hstar, hsmul, Pi.smul_apply, show
    (aux_l2Translate (τ t) (hf.toLp f) : ℝ → ℂ) y =
      (DomAddAct.mk (-τ t) +ᵥ hf.toLp f : Lp (α := ℝ) ℂ 2 volume) y by rfl,
    htrans, RCLike.inner_apply]
  simp only [starRingEnd_apply, Pi.star_apply, star_star, smul_eq_mul]
  rw [hg']
  ring

/-- Fourier transform commutes with the shifted Bochner operator in the
proof of `bilinearSobolevEstimates`. -/
lemma aux_bilinear_fourier_shiftOperator_eq_phaseIntegral
    (τ : ℝ → ℝ) (hτ : Continuous τ)
    (κ : ℝ → ℂ) (g : Lp (α := ℝ) ℂ 2 volume)
    (hκ : Integrable κ volume) :
    Lp.fourierTransformₗᵢ ℝ ℂ (aux_bilinear_shiftOperator τ κ g) =
      ∫ t : ℝ, κ t •
        (aux_fourierPhaseLp (τ t) • Lp.fourierTransformₗᵢ ℝ ℂ g) := by
  have hB := aux_bilinear_weighted_shift_l2Translate_integrable τ hτ κ g hκ
  let F : Lp (α := ℝ) ℂ 2 volume →L[ℂ] Lp (α := ℝ) ℂ 2 volume :=
    FourierTransform.fourierCLM ℂ (Lp (α := ℝ) ℂ 2 volume)
  unfold aux_bilinear_shiftOperator
  change F (∫ t : ℝ, κ t • aux_l2Translate (τ t) g) = _
  calc
    F (∫ t : ℝ, κ t • aux_l2Translate (τ t) g) =
        ∫ t : ℝ, F (κ t • aux_l2Translate (τ t) g) :=
      (F.integral_comp_comm hB).symm
    _ = ∫ t : ℝ, κ t •
        (aux_fourierPhaseLp (τ t) • Lp.fourierTransformₗᵢ ℝ ℂ g) := by
      apply integral_congr_ae
      filter_upwards with t
      change Lp.fourierTransformₗᵢ ℝ ℂ
        (κ t • aux_l2Translate (τ t) g) = _
      rw [(Lp.fourierTransformₗᵢ ℝ ℂ).map_smul, aux_l2Fourier_l2Translate]

/-- The shift produced by the change of variables `y = x + t²` in the
first inequality of `bilinearSobolevEstimates`. -/
def aux_bilinear_branchOneShift (t : ℝ) : ℝ := t ^ 2 - t

/-- The scalar kernel produced by the first coordinate change in
`bilinearSobolevEstimates`. -/
def aux_bilinear_branchOneKernel (χ : ℝ → ℝ) (ξ : ℝ) : ℝ → ℂ :=
  fun t ↦ exponential (-ξ * t ^ 2) * (χ t : ℂ)

/-- The unimodular outer factor in the first inequality of
`bilinearSobolevEstimates`. -/
def aux_bilinear_branchOneModulation (ξ : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun y ↦ frequencyCharacter ξ y * f y

/-- The shift used in the second inequality of `bilinearSobolevEstimates`. -/
def aux_bilinear_branchTwoShift (t : ℝ) : ℝ := -t ^ 2

/-- The scalar kernel used in the second inequality of
`bilinearSobolevEstimates`. -/
def aux_bilinear_branchTwoKernel (χ : ℝ → ℝ) (ξ : ℝ) : ℝ → ℂ :=
  fun t ↦ exponential (ξ * t) * (χ t : ℂ)

/-- The unimodular outer factor in the second inequality of
`bilinearSobolevEstimates`. -/
def aux_bilinear_branchTwoModulation (ξ : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x ↦ frequencyCharacter ξ x * f x

/-- Continuity of the first shifted coordinate curve. -/
lemma aux_bilinear_continuous_branchOneShift : Continuous aux_bilinear_branchOneShift := by
  unfold aux_bilinear_branchOneShift
  fun_prop

/-- Continuity of the second shifted coordinate curve. -/
lemma aux_bilinear_continuous_branchTwoShift : Continuous aux_bilinear_branchTwoShift := by
  unfold aux_bilinear_branchTwoShift
  fun_prop

/-- The character addition formula used to identify the second physical
coordinate change in `bilinearSobolevEstimates`. -/
lemma aux_bilinear_frequencyCharacter_add (ξ x t : ℝ) :
    frequencyCharacter ξ (x + t) =
      frequencyCharacter ξ x * exponential (ξ * t) := by
  unfold frequencyCharacter
  rw [← aux_phase_exponential_add]
  congr 1
  ring

/-- The character identity used to identify the first physical coordinate
change in `bilinearSobolevEstimates`. -/
lemma aux_bilinear_frequencyCharacter_sub_sq (ξ y t : ℝ) :
    frequencyCharacter ξ (y - t ^ 2) =
      frequencyCharacter ξ y * exponential (-ξ * t ^ 2) := by
  unfold frequencyCharacter
  rw [← aux_phase_exponential_add]
  congr 1
  ring

/-- After `y = x + t²`, the first trilinear form is an `L²` pairing with
the branch-one shifted operator. -/
lemma aux_bilinear_trilinear_branchOne_eq_inner
    (χ : ℝ → ℝ) (ξ : ℝ) (f₁ f₂ : ℝ → ℂ)
    (hf₁ : MemLp f₁ 2 volume)
    (hmod : MemLp (aux_bilinear_branchOneModulation ξ f₂) 2 volume)
    (hκ : Integrable (aux_bilinear_branchOneKernel χ ξ) volume)
    (hjoint : Integrable (fun z : ℝ × ℝ ↦
      frequencyCharacter ξ z.1 * f₁ (z.1 + z.2) * f₂ (z.1 + z.2 ^ 2) *
        (χ z.2 : ℂ)) (volume.prod volume)) :
    trilinearForm χ (frequencyCharacter ξ) f₁ f₂ =
      inner ℂ (star (hmod.toLp (aux_bilinear_branchOneModulation ξ f₂)))
        (aux_bilinear_shiftOperator aux_bilinear_branchOneShift
          (aux_bilinear_branchOneKernel χ ξ) (hf₁.toLp f₁)) := by
  rw [aux_bilinear_inner_star_shiftOperator_eq_iterated aux_bilinear_branchOneShift
    aux_bilinear_continuous_branchOneShift (aux_bilinear_branchOneKernel χ ξ) f₁
    (aux_bilinear_branchOneModulation ξ f₂) hf₁ hmod hκ]
  unfold trilinearForm
  calc
    ∫ x : ℝ, ∫ t : ℝ,
        frequencyCharacter ξ x * f₁ (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ) =
        ∫ t : ℝ, ∫ x : ℝ,
          frequencyCharacter ξ x * f₁ (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ) :=
      integral_integral_swap hjoint
    _ = ∫ t : ℝ, ∫ y : ℝ,
        aux_bilinear_branchOneModulation ξ f₂ y *
          (aux_bilinear_branchOneKernel χ ξ t *
            f₁ (y - aux_bilinear_branchOneShift t)) := by
      apply integral_congr_ae
      filter_upwards with t
      let e : ℝ ≃ᵐ ℝ := MeasurableEquiv.addRight (t ^ 2)
      have he : MeasurePreserving (e : ℝ → ℝ) volume volume := by
        simpa [e] using measurePreserving_add_right volume (t ^ 2)
      calc
        ∫ x : ℝ,
            frequencyCharacter ξ x * f₁ (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ) =
            ∫ x : ℝ,
              aux_bilinear_branchOneModulation ξ f₂ (e x) *
                (aux_bilinear_branchOneKernel χ ξ t *
                  f₁ (e x - aux_bilinear_branchOneShift t)) := by
          apply integral_congr_ae
          filter_upwards with x
          have hphase : frequencyCharacter ξ x =
              frequencyCharacter ξ (x + t ^ 2) * exponential (-ξ * t ^ 2) := by
            convert aux_bilinear_frequencyCharacter_sub_sq ξ (x + t ^ 2) t using 1; ring_nf
          dsimp [e, aux_bilinear_branchOneModulation, aux_bilinear_branchOneKernel,
            aux_bilinear_branchOneShift]
          rw [hphase]
          ring_nf
        _ = ∫ y : ℝ,
            aux_bilinear_branchOneModulation ξ f₂ y *
              (aux_bilinear_branchOneKernel χ ξ t *
                f₁ (y - aux_bilinear_branchOneShift t)) :=
          he.integral_comp' (fun y : ℝ ↦
            aux_bilinear_branchOneModulation ξ f₂ y *
              (aux_bilinear_branchOneKernel χ ξ t *
                f₁ (y - aux_bilinear_branchOneShift t)))

/-- The second trilinear form is an `L²` pairing with the branch-two shifted
operator. -/
lemma aux_bilinear_trilinear_branchTwo_eq_inner
    (χ : ℝ → ℝ) (ξ : ℝ) (f₀ f₂ : ℝ → ℂ)
    (hf₂ : MemLp f₂ 2 volume)
    (hmod : MemLp (aux_bilinear_branchTwoModulation ξ f₀) 2 volume)
    (hκ : Integrable (aux_bilinear_branchTwoKernel χ ξ) volume)
    (hjoint : Integrable (fun z : ℝ × ℝ ↦
      f₀ z.1 * frequencyCharacter ξ (z.1 + z.2) * f₂ (z.1 + z.2 ^ 2) *
        (χ z.2 : ℂ)) (volume.prod volume)) :
    trilinearForm χ f₀ (frequencyCharacter ξ) f₂ =
      inner ℂ (star (hmod.toLp (aux_bilinear_branchTwoModulation ξ f₀)))
        (aux_bilinear_shiftOperator aux_bilinear_branchTwoShift
          (aux_bilinear_branchTwoKernel χ ξ) (hf₂.toLp f₂)) := by
  rw [aux_bilinear_inner_star_shiftOperator_eq_iterated aux_bilinear_branchTwoShift
    aux_bilinear_continuous_branchTwoShift (aux_bilinear_branchTwoKernel χ ξ) f₂
    (aux_bilinear_branchTwoModulation ξ f₀) hf₂ hmod hκ]
  unfold trilinearForm
  calc
    ∫ x : ℝ, ∫ t : ℝ,
        f₀ x * frequencyCharacter ξ (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ) =
        ∫ t : ℝ, ∫ x : ℝ,
          f₀ x * frequencyCharacter ξ (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ) :=
      integral_integral_swap hjoint
    _ = ∫ t : ℝ, ∫ x : ℝ,
        aux_bilinear_branchTwoModulation ξ f₀ x *
          (aux_bilinear_branchTwoKernel χ ξ t *
            f₂ (x - aux_bilinear_branchTwoShift t)) := by
      apply integral_congr_ae
      filter_upwards with t
      apply integral_congr_ae
      filter_upwards with x
      unfold aux_bilinear_branchTwoModulation aux_bilinear_branchTwoKernel
        aux_bilinear_branchTwoShift
      rw [aux_bilinear_frequencyCharacter_add]
      ring_nf

/-- An integrable time kernel times two `L²` factors along a continuous
translation curve is jointly integrable.  It supplies Fubini for
`bilinearSobolevEstimates`. -/
lemma aux_bilinear_integrable_weighted_shift_pair
    (τ : ℝ → ℝ) (hτ : Continuous τ)
    (κ f g : ℝ → ℂ) (hκ : Integrable κ volume)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun z : ℝ × ℝ ↦
      κ z.1 * (g z.2 * f (z.2 - τ z.1))) (volume.prod volume) := by
  let B : ℝ → ℝ → ℂ := fun t y ↦ g y * f (y - τ t)
  have htrans : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ f (z.2 - τ z.1))
      (volume.prod volume) := by
    change AEStronglyMeasurable (f ∘ fun z : ℝ × ℝ ↦ z.2 - τ z.1)
      (volume.prod volume)
    apply hf.aestronglyMeasurable.comp_quasiMeasurePreserving
    refine QuasiMeasurePreserving.prod_of_right (by fun_prop) ?_
    filter_upwards with t
    simpa only [sub_eq_add_neg] using
      (measurePreserving_add_right volume (-(τ t))).quasiMeasurePreserving
  have hg' : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ g z.2) (volume.prod volume) := by
    change AEStronglyMeasurable (g ∘ Prod.snd) (volume.prod volume)
    exact hg.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume))
  have hBmeas : AEStronglyMeasurable (Function.uncurry B) (volume.prod volume) := by
    exact hg'.mul htrans
  have hBint : ∀ t : ℝ, Integrable (B t) volume := by
    intro t
    have hft : MemLp (fun y : ℝ ↦ f (y - τ t)) 2 volume := by
      have h := hf.comp_measurePreserving
        (measurePreserving_add_right volume (-(τ t)))
      simpa only [Function.comp_def, sub_eq_add_neg] using h
    have hprod : MemLp (fun y : ℝ ↦ g y * f (y - τ t)) 1 volume := by
      exact hft.mul hg
    exact memLp_one_iff_integrable.mp hprod
  let C : ℝ :=
    (∫ y : ℝ, ‖g y‖ ^ 2) ^ (1 / (2 : ℝ)) *
      (∫ y : ℝ, ‖f y‖ ^ 2) ^ (1 / (2 : ℝ))
  have hBbound : ∀ t : ℝ, ∫ y : ℝ, ‖B t y‖ ≤ C := by
    intro t
    calc
      ∫ y : ℝ, ‖B t y‖ = ∫ y : ℝ, ‖g y‖ * ‖f (y - τ t)‖ := by
        apply integral_congr_ae
        filter_upwards with y
        rw [norm_mul]
      _ = ∫ y : ℝ, ‖g (1 * y + 0)‖ * ‖f (1 * y + -(τ t))‖ := by
        congr 1
        funext y
        congr 3 <;> ring
      _ ≤ C := by
        simpa only [C, inv_one, abs_one, one_mul] using
          (aux_gowersFourier_integral_norm_mul_comp_affine_le_scaled g f hg hf
            1 1 0 (-(τ t)) (by norm_num) (by norm_num))
  simpa only [B] using
    aux_gowersFourier_integrable_weighted_bilinear_of_section_bound κ hκ B hBmeas hBint C hBbound

/-- The required Fubini hypothesis for the first physical coordinate change
in `bilinearSobolevEstimates`. -/
lemma aux_bilinear_integrable_branchOne_joint
    (χ : ℝ → ℝ) (ξ : ℝ) (f₁ f₂ : ℝ → ℂ)
    (hf₁ : MemLp f₁ 2 volume)
    (hmod : MemLp (aux_bilinear_branchOneModulation ξ f₂) 2 volume)
    (hκ : Integrable (aux_bilinear_branchOneKernel χ ξ) volume) :
    Integrable (fun z : ℝ × ℝ ↦
      frequencyCharacter ξ z.1 * f₁ (z.1 + z.2) * f₂ (z.1 + z.2 ^ 2) *
        (χ z.2 : ℂ)) (volume.prod volume) := by
  let H : ℝ × ℝ → ℂ := fun z ↦
    aux_bilinear_branchOneKernel χ ξ z.2 *
      (aux_bilinear_branchOneModulation ξ f₂ z.1 *
        f₁ (z.1 - aux_bilinear_branchOneShift z.2))
  have hH : Integrable H (volume.prod volume) := by
    simpa only [H, Function.comp_def, Prod.fst_swap, Prod.snd_swap] using
      (aux_bilinear_integrable_weighted_shift_pair aux_bilinear_branchOneShift
        aux_bilinear_continuous_branchOneShift (aux_bilinear_branchOneKernel χ ξ) f₁
        (aux_bilinear_branchOneModulation ξ f₂) hκ hf₁ hmod).swap
  have hcomp : Integrable
      (H ∘ fun z : ℝ × ℝ ↦ (z.1 + z.2 ^ 2, z.2)) (volume.prod volume) := by
    rw [← memLp_one_iff_integrable] at hH ⊢
    exact hH.comp_measurePreserving aux_u3_measurePreserving_add_sq_prod
  have hEq : (fun z : ℝ × ℝ ↦
      frequencyCharacter ξ z.1 * f₁ (z.1 + z.2) * f₂ (z.1 + z.2 ^ 2) *
        (χ z.2 : ℂ)) =
      H ∘ fun z : ℝ × ℝ ↦ (z.1 + z.2 ^ 2, z.2) := by
    funext z
    rcases z with ⟨x, t⟩
    dsimp [H, Function.comp_def, aux_bilinear_branchOneKernel,
      aux_bilinear_branchOneModulation, aux_bilinear_branchOneShift]
    have hphase : frequencyCharacter ξ x =
        frequencyCharacter ξ (x + t ^ 2) * exponential (-ξ * t ^ 2) := by
      convert aux_bilinear_frequencyCharacter_sub_sq ξ (x + t ^ 2) t using 1; ring_nf
    rw [hphase]
    ring_nf
  rw [hEq]
  exact hcomp

/-- The required Fubini hypothesis for the second physical coordinate change
in `bilinearSobolevEstimates`. -/
lemma aux_bilinear_integrable_branchTwo_joint
    (χ : ℝ → ℝ) (ξ : ℝ) (f₀ f₂ : ℝ → ℂ)
    (hf₂ : MemLp f₂ 2 volume)
    (hmod : MemLp (aux_bilinear_branchTwoModulation ξ f₀) 2 volume)
    (hκ : Integrable (aux_bilinear_branchTwoKernel χ ξ) volume) :
    Integrable (fun z : ℝ × ℝ ↦
      f₀ z.1 * frequencyCharacter ξ (z.1 + z.2) * f₂ (z.1 + z.2 ^ 2) *
        (χ z.2 : ℂ)) (volume.prod volume) := by
  let H : ℝ × ℝ → ℂ := fun z ↦
    aux_bilinear_branchTwoKernel χ ξ z.2 *
      (aux_bilinear_branchTwoModulation ξ f₀ z.1 *
        f₂ (z.1 - aux_bilinear_branchTwoShift z.2))
  have hH : Integrable H (volume.prod volume) := by
    simpa only [H, Function.comp_def, Prod.fst_swap, Prod.snd_swap] using
      (aux_bilinear_integrable_weighted_shift_pair aux_bilinear_branchTwoShift
        aux_bilinear_continuous_branchTwoShift (aux_bilinear_branchTwoKernel χ ξ) f₂
        (aux_bilinear_branchTwoModulation ξ f₀) hκ hf₂ hmod).swap
  have hEq : (fun z : ℝ × ℝ ↦
      f₀ z.1 * frequencyCharacter ξ (z.1 + z.2) * f₂ (z.1 + z.2 ^ 2) *
        (χ z.2 : ℂ)) = H := by
    funext z
    rcases z with ⟨x, t⟩
    dsimp [H, aux_bilinear_branchTwoKernel, aux_bilinear_branchTwoModulation,
      aux_bilinear_branchTwoShift]
    rw [aux_bilinear_frequencyCharacter_add]
    ring_nf
  rw [hEq]
  exact hH

/-- The Fourier-side Bochner phase integral for an arbitrary continuous
translation curve in `bilinearSobolevEstimates`. -/
noncomputable def aux_bilinear_phaseIntegral
    (τ : ℝ → ℝ) (κ : ℝ → ℂ) (G : Lp (α := ℝ) ℂ 2 volume) :
    Lp (α := ℝ) ℂ 2 volume :=
  ∫ t : ℝ, κ t • (aux_fourierPhaseLp (τ t) • G)

/-- Local Fubini integrability for a nonlinear Fourier phase integral. -/
lemma aux_bilinear_phaseProduct_integrable_on
    (τ : ℝ → ℝ) (hτ : Continuous τ)
    (κ : ℝ → ℂ) (hκ : Integrable κ)
    (G : Lp (α := ℝ) ℂ 2 volume)
    (s : Set ℝ) (_hs : MeasurableSet s) (hμs : volume s < ∞) :
    Integrable (fun p : ℝ × ℝ ↦
      κ p.2 * aux_fourierPhase (τ p.2) p.1 * G p.1)
      ((volume.restrict s).prod volume) := by
  let : IsFiniteMeasure (volume.restrict s) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hμs⟩
  have hG : Integrable (G : ℝ → ℂ) (volume.restrict s) :=
    ((Lp.memLp G).restrict s).integrable (by norm_num)
  have hbase : Integrable (fun p : ℝ × ℝ ↦ G p.1 * κ p.2)
      ((volume.restrict s).prod volume) :=
    Integrable.mul_prod (μ := volume.restrict s) (ν := volume) hG hκ
  have hphase : Continuous (fun p : ℝ × ℝ ↦
      aux_fourierPhase (τ p.2) p.1) := by
    unfold aux_fourierPhase
    exact continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp
        ((hτ.comp continuous_snd).neg.mul continuous_fst))
  refine hbase.mono ?_ (Filter.Eventually.of_forall fun p ↦ ?_)
  · convert hphase.aestronglyMeasurable.mul hbase.aestronglyMeasurable using 1
    ext p
    simp only [Pi.mul_apply]
    ring
  · rw [norm_mul, norm_mul, aux_norm_fourierPhase]
    rw [norm_mul, mul_one]
    exact le_of_eq (mul_comm _ _)

/-- The selected representative of a nonlinear phase integral agrees almost
everywhere with its raw iterated integral. -/
lemma aux_bilinear_phaseIntegral_ae_eq_raw
    (τ : ℝ → ℝ) (hτ : Continuous τ)
    (κ : ℝ → ℂ) (hκ : Integrable κ)
    (G : Lp (α := ℝ) ℂ 2 volume)
    (hB : Integrable (fun t : ℝ ↦ κ t •
      (aux_fourierPhaseLp (τ t) • G)) volume) :
    (aux_bilinear_phaseIntegral τ κ G : ℝ → ℂ) =ᵐ[volume]
      fun η ↦ ∫ t : ℝ, κ t * aux_fourierPhase (τ t) η * G η := by
  let H : Lp (α := ℝ) ℂ 2 volume := aux_bilinear_phaseIntegral τ κ G
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s hs hμs
    let : IsFiniteMeasure (volume.restrict s) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using hμs⟩
    change IntegrableOn (H : ℝ → ℂ) s volume
    exact ((Lp.memLp H).restrict s).integrable (by norm_num)
  · intro s hs hμs
    have hF := aux_bilinear_phaseProduct_integrable_on τ hτ κ hκ G s hs hμs
    change IntegrableOn (fun η : ℝ ↦ ∫ t : ℝ,
      κ t * aux_fourierPhase (τ t) η * G η) s volume
    exact hF.integral_prod_left
  · intro s hs hμs
    have hF := aux_bilinear_phaseProduct_integrable_on τ hτ κ hκ G s hs hμs
    let L : Lp (α := ℝ) ℂ 2 volume →L[ℂ] ℂ :=
      (ContinuousLinearMap.lpPairing volume 2 2 (ContinuousLinearMap.mul ℂ ℂ))
        (indicatorConstLp 2 hs hμs.ne (1 : ℂ))
    have hL_phase (t : ℝ) : L (aux_fourierPhaseLp (τ t) • G) =
        ∫ η in s, aux_fourierPhase (τ t) η * G η := by
      exact aux_l2Pairing_indicator_phase_eq_setIntegral s hs hμs.ne (τ t) G
    have hL_smul (t : ℝ) : L (κ t • (aux_fourierPhaseLp (τ t) • G)) =
        ∫ η in s, κ t * aux_fourierPhase (τ t) η * G η := by
      calc
        L (κ t • (aux_fourierPhaseLp (τ t) • G)) =
            κ t * L (aux_fourierPhaseLp (τ t) • G) := L.map_smul _ _
        _ = κ t * ∫ η in s, aux_fourierPhase (τ t) η * G η := by rw [hL_phase]
        _ = ∫ η in s, κ t *
            (aux_fourierPhase (τ t) η * G η) := by
          exact (integral_const_mul (κ t)
            (fun η : ℝ ↦ aux_fourierPhase (τ t) η * G η)).symm
        _ = ∫ η in s, κ t * aux_fourierPhase (τ t) η * G η := by
          congr 1
          funext η
          ring
    have hL_H : L H = ∫ η in s, H η :=
      aux_l2Pairing_indicator_eq_setIntegral s hs hμs.ne H
    have hcomm := L.integral_comp_comm hB
    have hswap := integral_integral_swap
      (f := fun η : ℝ ↦ fun t : ℝ ↦
        κ t * aux_fourierPhase (τ t) η * G η) hF
    change (∫ η in s, H η) = (∫ η in s, ∫ t : ℝ,
      κ t * aux_fourierPhase (τ t) η * G η)
    calc
      ∫ η in s, H η = L H := hL_H.symm
      _ = L (∫ t : ℝ, κ t • (aux_fourierPhaseLp (τ t) • G)) := by rfl
      _ = ∫ t : ℝ, L (κ t • (aux_fourierPhaseLp (τ t) • G)) := hcomm.symm
      _ = ∫ t : ℝ, ∫ η in s,
          κ t * aux_fourierPhase (τ t) η * G η := by
        exact integral_congr_ae (Filter.Eventually.of_forall fun t ↦ hL_smul t)
      _ = ∫ η in s, ∫ t : ℝ,
          κ t * aux_fourierPhase (τ t) η * G η := hswap.symm

/-- Factoring the raw nonlinear phase integral isolates its scalar
multiplier. -/
lemma aux_bilinear_raw_phaseIntegral_eq_kernel_mul
    (τ : ℝ → ℝ) (κ : ℝ → ℂ) (G : Lp (α := ℝ) ℂ 2 volume) (η : ℝ) :
    (∫ t : ℝ, κ t * aux_fourierPhase (τ t) η * G η) =
      (∫ t : ℝ, κ t * aux_fourierPhase (τ t) η) * G η := by
  rw [← integral_mul_const]

/-- The nonlinear phase integral is almost everywhere its scalar multiplier
times the input Fourier representative. -/
lemma aux_bilinear_phaseIntegral_ae_eq_multiplier
    (τ : ℝ → ℝ) (hτ : Continuous τ)
    (κ : ℝ → ℂ) (hκ : Integrable κ)
    (G : Lp (α := ℝ) ℂ 2 volume)
    (hB : Integrable (fun t : ℝ ↦ κ t •
      (aux_fourierPhaseLp (τ t) • G)) volume) :
    (aux_bilinear_phaseIntegral τ κ G : ℝ → ℂ) =ᵐ[volume]
      fun η ↦ (∫ t : ℝ, κ t * aux_fourierPhase (τ t) η) * G η := by
  filter_upwards [aux_bilinear_phaseIntegral_ae_eq_raw τ hτ κ hκ G hB]
      with η hη
  rw [hη]
  exact aux_bilinear_raw_phaseIntegral_eq_kernel_mul τ κ G η

/-- Fourier transformation carries the spatial Bochner integrability input
to the nonlinear phase-integral input. -/
lemma aux_bilinear_phaseIntegral_integrable_of_l2Translate
    (τ : ℝ → ℝ) (κ : ℝ → ℂ) (G : Lp (α := ℝ) ℂ 2 volume)
    (hB : Integrable (fun t : ℝ ↦ κ t • aux_l2Translate (τ t) G) volume) :
    Integrable (fun t : ℝ ↦ κ t •
      (aux_fourierPhaseLp (τ t) • Lp.fourierTransformₗᵢ ℝ ℂ G)) volume := by
  let F := Lp.fourierTransformₗᵢ ℝ ℂ
  have hmap : Integrable (fun t : ℝ ↦
      (FourierTransform.fourierCLM ℂ (Lp (α := ℝ) ℂ 2 volume))
        (κ t • aux_l2Translate (τ t) G)) volume :=
    (FourierTransform.fourierCLM ℂ
      (Lp (α := ℝ) ℂ 2 volume)).integrable_comp hB
  change Integrable (fun t : ℝ ↦ F
    (κ t • aux_l2Translate (τ t) G)) volume at hmap
  apply hmap.congr
  filter_upwards with t
  calc
    F (κ t • aux_l2Translate (τ t) G) =
        κ t • F (aux_l2Translate (τ t) G) := F.map_smul _ _
    _ = κ t • (aux_fourierPhaseLp (τ t) • F G) := by
      rw [aux_l2Fourier_l2Translate]

/-- Fourier transform of the shifted Bochner operator has its nonlinear
scalar multiplier almost everywhere. -/
lemma aux_bilinear_fourier_shiftOperator_ae_eq_multiplier
    (τ : ℝ → ℝ) (hτ : Continuous τ)
    (κ : ℝ → ℂ) (hκ : Integrable κ)
    (G : Lp (α := ℝ) ℂ 2 volume) :
    (Lp.fourierTransformₗᵢ ℝ ℂ
      (aux_bilinear_shiftOperator τ κ G) : ℝ → ℂ) =ᵐ[volume]
      fun η ↦ (∫ t : ℝ, κ t * aux_fourierPhase (τ t) η) *
        (Lp.fourierTransformₗᵢ ℝ ℂ G) η := by
  have hB : Integrable (fun t : ℝ ↦ κ t • aux_l2Translate (τ t) G) volume :=
    aux_bilinear_weighted_shift_l2Translate_integrable τ hτ κ G hκ
  have hphase : Integrable (fun t : ℝ ↦ κ t •
      (aux_fourierPhaseLp (τ t) • Lp.fourierTransformₗᵢ ℝ ℂ G)) volume :=
    aux_bilinear_phaseIntegral_integrable_of_l2Translate τ κ G hB
  have hFourier : Lp.fourierTransformₗᵢ ℝ ℂ
      (aux_bilinear_shiftOperator τ κ G) =
      aux_bilinear_phaseIntegral τ κ (Lp.fourierTransformₗᵢ ℝ ℂ G) := by
    simpa only [aux_bilinear_phaseIntegral] using
      aux_bilinear_fourier_shiftOperator_eq_phaseIntegral τ hτ κ G hκ
  rw [hFourier]
  exact aux_bilinear_phaseIntegral_ae_eq_multiplier τ hτ κ hκ
    (Lp.fourierTransformₗᵢ ℝ ℂ G) hphase

/-- A compactly supported smooth cutoff multiplied by a continuous unit
phase is integrable; used for the two kernels in `bilinearSobolevEstimates`. -/
lemma aux_bilinear_phaseMul_integrable
    (p : ℝ → ℝ) (hp : Continuous p) (χ : ℝ → ℝ)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ) :
    Integrable (fun t ↦ exponential (p t) * (χ t : ℂ)) volume := by
  have hχmem : MemLp χ (1 : ℝ≥0∞) volume :=
    hχ_smooth.continuous.memLp_of_hasCompactSupport hχ_compact
  have hχint : Integrable (fun t : ℝ ↦ (χ t : ℂ)) volume :=
    memLp_one_iff_integrable.mp hχmem.ofReal
  have hphasecont : Continuous (fun t : ℝ ↦ exponential (p t)) := by
    unfold exponential
    fun_prop
  have hphase : AEStronglyMeasurable (fun t : ℝ ↦ exponential (p t)) volume :=
    hphasecont.aestronglyMeasurable
  have hmul := hχint.bdd_mul (c := 1) hphase
    (Filter.Eventually.of_forall fun t ↦ by rw [aux_norm_exponential])
  convert hmul using 1

/-- Multiplication by a frequency character preserves `L²`; this gives the
outer function in each Cauchy--Schwarz step for `bilinearSobolevEstimates`. -/
lemma aux_bilinear_frequencyCharacter_mul_memLp_two
    (ξ : ℝ) (f : ℝ → ℂ) (hf : MemLp f (2 : ℝ≥0∞) volume) :
    MemLp (fun x ↦ frequencyCharacter ξ x * f x) (2 : ℝ≥0∞) volume := by
  apply hf.mono
  · have hphase : AEStronglyMeasurable (frequencyCharacter ξ) volume := by
      unfold frequencyCharacter exponential
      fun_prop
    exact hphase.mul hf.aestronglyMeasurable
  · filter_upwards with x
    unfold frequencyCharacter
    rw [norm_mul, aux_norm_exponential]
    simp

/-- The `L²` norm is invariant under multiplication by a frequency
character. -/
lemma aux_bilinear_frequencyCharacter_mul_norm
    (ξ : ℝ) (f : ℝ → ℂ) (hf : MemLp f (2 : ℝ≥0∞) volume) :
    (eLpNorm (fun x ↦ frequencyCharacter ξ x * f x) (2 : ℝ≥0∞) volume).toReal =
      (eLpNorm f (2 : ℝ≥0∞) volume).toReal := by
  have hmod := aux_bilinear_frequencyCharacter_mul_memLp_two ξ f hf
  have heq : eLpNorm (fun x ↦ frequencyCharacter ξ x * f x)
      (2 : ℝ≥0∞) volume = eLpNorm f (2 : ℝ≥0∞) volume := by
    apply eLpNorm_congr_norm_ae
    filter_upwards with x
    unfold frequencyCharacter
    rw [norm_mul, aux_norm_exponential]
    ring
  rw [heq]

/-- The translated Fourier phase expressed using the manuscript's
`exponential` notation. -/
lemma aux_bilinear_fourierPhase_eq_exponential (s η : ℝ) :
    aux_fourierPhase s η = exponential ((-s) * η) := by
  unfold aux_fourierPhase exponential
  rw [Real.fourierChar_apply]

/-- The first branch's nonlinear Fourier kernel is the quadratic phase from
the first displayed estimate in `bilinearSobolevEstimates`. -/
lemma aux_bilinear_branchOne_phase_eq_quadratic
    (χ : ℝ → ℝ) (ξ η t : ℝ) :
    aux_bilinear_branchOneKernel χ ξ t *
      aux_fourierPhase (aux_bilinear_branchOneShift t) η =
      exponential (η * t - (η + ξ) * t ^ 2) * (χ t : ℂ) := by
  rw [aux_bilinear_branchOneKernel, aux_bilinear_fourierPhase_eq_exponential]
  rw [show exponential (-ξ * t ^ 2) * (χ t : ℂ) *
      exponential (-(aux_bilinear_branchOneShift t) * η) =
      (exponential (-ξ * t ^ 2) *
        exponential (-(aux_bilinear_branchOneShift t) * η)) * (χ t : ℂ) by ring]
  rw [← aux_phase_exponential_add]
  congr 2
  unfold aux_bilinear_branchOneShift
  ring

/-- The first shifted operator has its stated quadratic Fourier multiplier. -/
lemma aux_bilinear_fourier_branchOne_ae_eq_quadratic_multiplier
    (χ : ℝ → ℝ) (ξ : ℝ) (G : Lp (α := ℝ) ℂ 2 volume)
    (hκ : Integrable (aux_bilinear_branchOneKernel χ ξ)) :
    (Lp.fourierTransformₗᵢ ℝ ℂ
      (aux_bilinear_shiftOperator aux_bilinear_branchOneShift
        (aux_bilinear_branchOneKernel χ ξ) G) : ℝ → ℂ) =ᵐ[volume]
      fun η ↦ (∫ t : ℝ,
        exponential (η * t - (η + ξ) * t ^ 2) * (χ t : ℂ)) *
          (Lp.fourierTransformₗᵢ ℝ ℂ G) η := by
  filter_upwards [aux_bilinear_fourier_shiftOperator_ae_eq_multiplier
      aux_bilinear_branchOneShift aux_bilinear_continuous_branchOneShift
      (aux_bilinear_branchOneKernel χ ξ) hκ G] with η hη
  rw [hη]
  have hkernel :
      (∫ t : ℝ, aux_bilinear_branchOneKernel χ ξ t *
        aux_fourierPhase (aux_bilinear_branchOneShift t) η) =
        ∫ t : ℝ, exponential (η * t - (η + ξ) * t ^ 2) * (χ t : ℂ) := by
    apply integral_congr_ae
    filter_upwards with t
    exact aux_bilinear_branchOne_phase_eq_quadratic χ ξ η t
  rw [hkernel]

/-- The second branch's nonlinear Fourier kernel is the quadratic phase from
the second displayed estimate in `bilinearSobolevEstimates`. -/
lemma aux_bilinear_branchTwo_phase_eq_quadratic
    (χ : ℝ → ℝ) (ξ η t : ℝ) :
    aux_bilinear_branchTwoKernel χ ξ t *
      aux_fourierPhase (aux_bilinear_branchTwoShift t) η =
      exponential (ξ * t + η * t ^ 2) * (χ t : ℂ) := by
  rw [aux_bilinear_branchTwoKernel, aux_bilinear_fourierPhase_eq_exponential]
  rw [show exponential (ξ * t) * (χ t : ℂ) *
      exponential (-(aux_bilinear_branchTwoShift t) * η) =
      (exponential (ξ * t) * exponential (-(aux_bilinear_branchTwoShift t) * η)) *
        (χ t : ℂ) by ring]
  rw [← aux_phase_exponential_add]
  congr 2
  unfold aux_bilinear_branchTwoShift
  ring

/-- The second shifted operator has its stated quadratic Fourier multiplier. -/
lemma aux_bilinear_fourier_branchTwo_ae_eq_quadratic_multiplier
    (χ : ℝ → ℝ) (ξ : ℝ) (G : Lp (α := ℝ) ℂ 2 volume)
    (hκ : Integrable (aux_bilinear_branchTwoKernel χ ξ)) :
    (Lp.fourierTransformₗᵢ ℝ ℂ
      (aux_bilinear_shiftOperator aux_bilinear_branchTwoShift
        (aux_bilinear_branchTwoKernel χ ξ) G) : ℝ → ℂ) =ᵐ[volume]
      fun η ↦ (∫ t : ℝ,
        exponential (ξ * t + η * t ^ 2) * (χ t : ℂ)) *
          (Lp.fourierTransformₗᵢ ℝ ℂ G) η := by
  filter_upwards [aux_bilinear_fourier_shiftOperator_ae_eq_multiplier
      aux_bilinear_branchTwoShift aux_bilinear_continuous_branchTwoShift
      (aux_bilinear_branchTwoKernel χ ξ) hκ G] with η hη
  rw [hη]
  have hkernel :
      (∫ t : ℝ, aux_bilinear_branchTwoKernel χ ξ t *
        aux_fourierPhase (aux_bilinear_branchTwoShift t) η) =
        ∫ t : ℝ, exponential (ξ * t + η * t ^ 2) * (χ t : ℂ) := by
    apply integral_congr_ae
    filter_upwards with t
    exact aux_bilinear_branchTwo_phase_eq_quadratic χ ξ η t
  rw [hkernel]

/-- Quadratic oscillatory decay dominates the negative-half Japanese-bracket
weight on the quadratic coefficient. -/
lemma aux_bilinear_quadratic_decay_le_japanese (a b : ℝ) :
    (1 + max |a| |b|) ^ (-(1 / 2 : ℝ)) ≤
      japaneseBracket b ^ (-(1 / 2 : ℝ)) := by
  let M : ℝ := max |a| |b|
  have hM0 : 0 ≤ M := by
    dsimp [M]
    positivity
  have hbM : |b| ≤ M := by
    dsimp [M]
    exact le_max_right _ _
  have hbase : 0 < 1 + M := by linarith
  have hjap0 : 0 < japaneseBracket b := by
    dsimp [japaneseBracket]
    exact Real.sqrt_pos.2 (by positivity)
  have hjap : japaneseBracket b ≤ 1 + M := by
    rw [japaneseBracket]
    apply (Real.sqrt_le_iff).mpr
    constructor
    · linarith
    · have hsq : b ^ 2 ≤ M ^ 2 := by
        calc
          b ^ 2 = |b| ^ 2 := by rw [sq_abs]
          _ ≤ M ^ 2 := (sq_le_sq₀ (abs_nonneg b) hM0).mpr hbM
      have habsq : |b| ^ 2 ≤ M ^ 2 := by
        rw [sq_abs]
        exact hsq
      calc
        1 + |b| ^ 2 ≤ 1 + M ^ 2 := by gcongr
        _ ≤ (1 + M) ^ 2 := by nlinarith
  have hroot : Real.sqrt (japaneseBracket b) ≤ Real.sqrt (1 + M) :=
    Real.sqrt_le_sqrt hjap
  have hroot_left : 0 < Real.sqrt (1 + M) := Real.sqrt_pos.2 hbase
  have hroot_right : 0 < Real.sqrt (japaneseBracket b) :=
    Real.sqrt_pos.2 hjap0
  have hinv : (Real.sqrt (1 + M))⁻¹ ≤
      (Real.sqrt (japaneseBracket b))⁻¹ :=
    (inv_le_inv₀ hroot_left hroot_right).mpr hroot
  have hleft : (1 + M) ^ (-(1 / 2 : ℝ)) =
      (Real.sqrt (1 + M))⁻¹ := by
    rw [Real.rpow_neg hbase.le]
    rw [← Real.sqrt_eq_rpow]
  have hright : japaneseBracket b ^ (-(1 / 2 : ℝ)) =
      (Real.sqrt (japaneseBracket b))⁻¹ := by
    rw [Real.rpow_neg hjap0.le]
    rw [← Real.sqrt_eq_rpow]
  change (1 + M) ^ (-(1 / 2 : ℝ)) ≤ _
  rw [hleft, hright]
  exact hinv

/-- The quadratic estimate supplies the multiplier bound for the first
branch of `bilinearSobolevEstimates`. -/
lemma aux_bilinear_branchOne_multiplier_bound
    (J : Set ℝ) (χ : ℝ → ℝ)
    (hJ : ∃ jMinus jPlus : ℝ, jMinus ≤ jPlus ∧ J = Set.Icc jMinus jPlus)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (hχ_support : tsupport χ ⊆ J) (η ξ : ℝ) :
    ‖∫ t : ℝ, exponential (η * t - (η + ξ) * t ^ 2) * (χ t : ℂ)‖ ≤
      C_bilinearSobolevEstimates J χ *
        japaneseBracket η ^ (-(1 / 2 : ℝ)) := by
  have hquad := quadraticOscillatoryIntegralEstimate J χ hJ hχ_smooth hχ_compact
    hχ_nonneg hχ_le_one hχ_support η (-(η + ξ))
  have hfactor := aux_bilinear_quadratic_decay_le_japanese (-(η + ξ)) η
  have hconst0 : 0 ≤ C_quadraticOscillatoryIntegralEstimate J χ := by
    rw [C_quadraticOscillatoryIntegralEstimate]
    positivity
  have hfactor' :
      (1 + max |η| |-(η + ξ)|) ^ (-(1 / 2 : ℝ)) ≤
        japaneseBracket η ^ (-(1 / 2 : ℝ)) := by
    simpa only [max_comm] using hfactor
  calc
    ‖∫ t : ℝ, exponential (η * t - (η + ξ) * t ^ 2) * (χ t : ℂ)‖ =
        ‖∫ t : ℝ, exponential (η * t + (-(η + ξ)) * t ^ 2) * (χ t : ℂ)‖ := by
          congr 3
          funext t
          congr 2
          ring
    _ ≤ C_quadraticOscillatoryIntegralEstimate J χ *
        (1 + max |η| |-(η + ξ)|) ^ (-(1 / 2 : ℝ)) := hquad
    _ ≤ C_quadraticOscillatoryIntegralEstimate J χ *
        japaneseBracket η ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hfactor' hconst0
    _ = C_bilinearSobolevEstimates J χ *
        japaneseBracket η ^ (-(1 / 2 : ℝ)) := by rfl

/-- The quadratic estimate supplies the multiplier bound for the second
branch of `bilinearSobolevEstimates`. -/
lemma aux_bilinear_branchTwo_multiplier_bound
    (J : Set ℝ) (χ : ℝ → ℝ)
    (hJ : ∃ jMinus jPlus : ℝ, jMinus ≤ jPlus ∧ J = Set.Icc jMinus jPlus)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (hχ_support : tsupport χ ⊆ J) (ξ η : ℝ) :
    ‖∫ t : ℝ, exponential (ξ * t + η * t ^ 2) * (χ t : ℂ)‖ ≤
      C_bilinearSobolevEstimates J χ *
        japaneseBracket η ^ (-(1 / 2 : ℝ)) := by
  have hquad := quadraticOscillatoryIntegralEstimate J χ hJ hχ_smooth hχ_compact
    hχ_nonneg hχ_le_one hχ_support ξ η
  have hfactor := aux_bilinear_quadratic_decay_le_japanese ξ η
  have hconst0 : 0 ≤ C_quadraticOscillatoryIntegralEstimate J χ := by
    rw [C_quadraticOscillatoryIntegralEstimate]
    positivity
  calc
    ‖∫ t : ℝ, exponential (ξ * t + η * t ^ 2) * (χ t : ℂ)‖ ≤
        C_quadraticOscillatoryIntegralEstimate J χ *
          (1 + max |ξ| |η|) ^ (-(1 / 2 : ℝ)) := hquad
    _ ≤ C_quadraticOscillatoryIntegralEstimate J χ *
        japaneseBracket η ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hfactor hconst0
    _ = C_bilinearSobolevEstimates J χ *
        japaneseBracket η ^ (-(1 / 2 : ℝ)) := by rfl

/-- A pointwise quadratic multiplier bound yields the associated weighted
`L²` estimate. -/
lemma aux_bilinear_weighted_multiplier_eLpNorm_bound
    (m F : ℝ → ℂ) (C : ℝ) (_hC : 0 ≤ C)
    (hm : ∀ ζ : ℝ, ‖m ζ‖ ≤
      C * japaneseBracket ζ ^ (-(1 / 2 : ℝ))) :
    eLpNorm (fun ζ ↦ m ζ * F ζ) (2 : ℝ≥0∞) volume ≤
      ENNReal.ofReal C *
        eLpNorm (fun ζ ↦ (japaneseBracket ζ ^ (-(1 / 2 : ℝ))) • F ζ)
          (2 : ℝ≥0∞) volume := by
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
  filter_upwards with ζ
  rw [norm_mul]
  calc
    ‖m ζ‖ * ‖F ζ‖ ≤
        (C * japaneseBracket ζ ^ (-(1 / 2 : ℝ))) * ‖F ζ‖ :=
      mul_le_mul_of_nonneg_right (hm ζ) (norm_nonneg _)
    _ = C * ‖(japaneseBracket ζ ^ (-(1 / 2 : ℝ))) • F ζ‖ := by
      have hbracket : 0 ≤ japaneseBracket ζ := Real.sqrt_nonneg _
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hbracket _)]
      ring

/-- The real-valued version of the weighted multiplier inequality. -/
lemma aux_bilinear_weighted_multiplier_toReal_bound
    (m F : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ ζ : ℝ, ‖m ζ‖ ≤
      C * japaneseBracket ζ ^ (-(1 / 2 : ℝ)))
    (hFfinite : eLpNorm
      (fun ζ ↦ (japaneseBracket ζ ^ (-(1 / 2 : ℝ))) • F ζ)
      (2 : ℝ≥0∞) volume < ∞) :
    (eLpNorm (fun ζ ↦ m ζ * F ζ) (2 : ℝ≥0∞) volume).toReal ≤
      C * (eLpNorm
        (fun ζ ↦ (japaneseBracket ζ ^ (-(1 / 2 : ℝ))) • F ζ)
        (2 : ℝ≥0∞) volume).toReal := by
  have hbound := aux_bilinear_weighted_multiplier_eLpNorm_bound m F C hC hm
  have hright_ne : ENNReal.ofReal C * eLpNorm
      (fun ζ ↦ (japaneseBracket ζ ^ (-(1 / 2 : ℝ))) • F ζ)
      (2 : ℝ≥0∞) volume ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFfinite.ne
  have hreal := ENNReal.toReal_mono hright_ne hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at hreal
  exact hreal

/-- The negative-half Japanese-bracket multiplier preserves `L²`; this
ensures the Sobolev norm used by `bilinearSobolevEstimates` is finite. -/
lemma aux_bilinear_sobolev_weight_memLp_two
    (G : Lp (α := ℝ) ℂ 2 volume) :
    MemLp (fun ζ ↦ (japaneseBracket ζ ^ (-(1 / 2 : ℝ))) • G ζ)
      (2 : ℝ≥0∞) volume := by
  have hjap_cont : Continuous japaneseBracket := by
    unfold japaneseBracket
    fun_prop
  have hweight_cont : Continuous
      (fun ζ : ℝ ↦ japaneseBracket ζ ^ (-(1 / 2 : ℝ))) := by
    exact hjap_cont.rpow continuous_const (fun ζ ↦ Or.inl (by
      have hpos : 0 < japaneseBracket ζ := by
        unfold japaneseBracket
        exact Real.sqrt_pos.2 (by positivity)
      exact hpos.ne'))
  have hweight_bound : ∀ ζ : ℝ,
      ‖japaneseBracket ζ ^ (-(1 / 2 : ℝ))‖ ≤ 1 := by
    intro ζ
    have hjap_nonneg : 0 ≤ japaneseBracket ζ := by
      unfold japaneseBracket
      exact Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hjap_nonneg _)]
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · unfold japaneseBracket
      have harg : (1 : ℝ) ≤ 1 + |ζ| ^ 2 := by
        nlinarith [sq_nonneg |ζ|]
      simpa using (Real.sqrt_le_sqrt harg)
    · norm_num
  have hweight : MemLp (fun ζ : ℝ ↦ japaneseBracket ζ ^ (-(1 / 2 : ℝ)))
      (∞ : ℝ≥0∞) volume :=
    memLp_top_of_bound hweight_cont.aestronglyMeasurable 1
      (Filter.Eventually.of_forall hweight_bound)
  let : (∞ : ℝ≥0∞).HolderTriple 2 2 := ENNReal.HolderTriple.symm
  exact (Lp.memLp G).smul hweight

/-- Finiteness of the half-order Sobolev norm needed by the multiplier
bridge. -/
lemma aux_bilinear_sobolevNorm_half_lt_top
    (g : Lp (α := ℝ) ℂ 2 volume) :
    sobolevNorm (1 / 2 : ℝ) g < ∞ := by
  unfold sobolevNorm
  exact (aux_bilinear_sobolev_weight_memLp_two
    (Lp.fourierTransformₗᵢ ℝ ℂ g)).eLpNorm_lt_top

/-- An almost-everywhere Fourier multiplier formula together with the
quadratic pointwise bound gives the `L²` Sobolev operator estimate. -/
lemma aux_bilinear_l2_norm_of_fourier_multiplier_bound
    (T G : Lp (α := ℝ) ℂ 2 volume) (m : ℝ → ℂ) (C : ℝ)
    (hC : 0 ≤ C)
    (hm : ∀ ζ : ℝ, ‖m ζ‖ ≤
      C * japaneseBracket ζ ^ (-(1 / 2 : ℝ)))
    (hFourier : (Lp.fourierTransformₗᵢ ℝ ℂ T : ℝ → ℂ) =ᵐ[volume]
      fun ζ ↦ m ζ * (Lp.fourierTransformₗᵢ ℝ ℂ G) ζ) :
    ‖T‖ ≤ C * (sobolevNorm (1 / 2 : ℝ) G).toReal := by
  have hfinite : eLpNorm
      (fun ζ ↦ (japaneseBracket ζ ^ (-(1 / 2 : ℝ))) •
        (Lp.fourierTransformₗᵢ ℝ ℂ G) ζ)
      (2 : ℝ≥0∞) volume < ∞ := by
    simpa only [sobolevNorm] using aux_bilinear_sobolevNorm_half_lt_top G
  have hmult := aux_bilinear_weighted_multiplier_toReal_bound
    m (Lp.fourierTransformₗᵢ ℝ ℂ G) C hC hm hfinite
  have hnorm : ‖T‖ =
      (eLpNorm (Lp.fourierTransformₗᵢ ℝ ℂ T : ℝ → ℂ)
        (2 : ℝ≥0∞) volume).toReal := by
    calc
      ‖T‖ = ‖Lp.fourierTransformₗᵢ ℝ ℂ T‖ :=
        (Lp.fourierTransformₗᵢ ℝ ℂ).norm_map T |>.symm
      _ = _ := Lp.norm_def _
  calc
    ‖T‖ = (eLpNorm (Lp.fourierTransformₗᵢ ℝ ℂ T : ℝ → ℂ)
        (2 : ℝ≥0∞) volume).toReal := hnorm
    _ = (eLpNorm (fun ζ ↦ m ζ *
        (Lp.fourierTransformₗᵢ ℝ ℂ G) ζ) (2 : ℝ≥0∞) volume).toReal := by
      rw [eLpNorm_congr_ae hFourier]
    _ ≤ C * (eLpNorm
        (fun ζ ↦ (japaneseBracket ζ ^ (-(1 / 2 : ℝ))) •
          (Lp.fourierTransformₗᵢ ℝ ℂ G) ζ)
        (2 : ℝ≥0∞) volume).toReal := hmult
    _ = C * (sobolevNorm (1 / 2 : ℝ) G).toReal := by rfl

/-- The branch-one shifted operator satisfies the negative-half Sobolev
bound required in `bilinearSobolevEstimates`. -/
lemma aux_bilinear_branchOne_operator_sobolev_bound
    (J : Set ℝ) (χ : ℝ → ℝ)
    (hJ : ∃ jMinus jPlus : ℝ, jMinus ≤ jPlus ∧ J = Set.Icc jMinus jPlus)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (hχ_support : tsupport χ ⊆ J) (ξ : ℝ)
    (G : Lp (α := ℝ) ℂ 2 volume) :
    ‖aux_bilinear_shiftOperator aux_bilinear_branchOneShift
      (aux_bilinear_branchOneKernel χ ξ) G‖ ≤
      C_bilinearSobolevEstimates J χ *
        (sobolevNorm (1 / 2 : ℝ) G).toReal := by
  let T : Lp (α := ℝ) ℂ 2 volume :=
    aux_bilinear_shiftOperator aux_bilinear_branchOneShift
      (aux_bilinear_branchOneKernel χ ξ) G
  let m : ℝ → ℂ := fun η ↦ ∫ t : ℝ,
    exponential (η * t - (η + ξ) * t ^ 2) * (χ t : ℂ)
  have hκ : Integrable (aux_bilinear_branchOneKernel χ ξ) volume := by
    change Integrable (fun t : ℝ ↦ exponential (-ξ * t ^ 2) * (χ t : ℂ)) volume
    exact aux_bilinear_phaseMul_integrable (fun t : ℝ ↦ -ξ * t ^ 2) (by fun_prop)
      χ hχ_smooth hχ_compact
  have hC : 0 ≤ C_bilinearSobolevEstimates J χ := by
    rw [C_bilinearSobolevEstimates]
    positivity
  have hm : ∀ η : ℝ, ‖m η‖ ≤ C_bilinearSobolevEstimates J χ *
      japaneseBracket η ^ (-(1 / 2 : ℝ)) := by
    intro η
    exact aux_bilinear_branchOne_multiplier_bound J χ hJ hχ_smooth hχ_compact
      hχ_nonneg hχ_le_one hχ_support η ξ
  have hFourier : (Lp.fourierTransformₗᵢ ℝ ℂ T : ℝ → ℂ) =ᵐ[volume]
      fun η ↦ m η * (Lp.fourierTransformₗᵢ ℝ ℂ G) η := by
    simpa only [T, m] using
      aux_bilinear_fourier_branchOne_ae_eq_quadratic_multiplier χ ξ G hκ
  exact aux_bilinear_l2_norm_of_fourier_multiplier_bound T G m
    (C_bilinearSobolevEstimates J χ) hC hm hFourier

/-- The branch-two shifted operator satisfies the negative-half Sobolev
bound required in `bilinearSobolevEstimates`. -/
lemma aux_bilinear_branchTwo_operator_sobolev_bound
    (J : Set ℝ) (χ : ℝ → ℝ)
    (hJ : ∃ jMinus jPlus : ℝ, jMinus ≤ jPlus ∧ J = Set.Icc jMinus jPlus)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (hχ_support : tsupport χ ⊆ J) (ξ : ℝ)
    (G : Lp (α := ℝ) ℂ 2 volume) :
    ‖aux_bilinear_shiftOperator aux_bilinear_branchTwoShift
      (aux_bilinear_branchTwoKernel χ ξ) G‖ ≤
      C_bilinearSobolevEstimates J χ *
        (sobolevNorm (1 / 2 : ℝ) G).toReal := by
  let T : Lp (α := ℝ) ℂ 2 volume :=
    aux_bilinear_shiftOperator aux_bilinear_branchTwoShift
      (aux_bilinear_branchTwoKernel χ ξ) G
  let m : ℝ → ℂ := fun η ↦ ∫ t : ℝ,
    exponential (ξ * t + η * t ^ 2) * (χ t : ℂ)
  have hκ : Integrable (aux_bilinear_branchTwoKernel χ ξ) volume := by
    change Integrable (fun t : ℝ ↦ exponential (ξ * t) * (χ t : ℂ)) volume
    exact aux_bilinear_phaseMul_integrable (fun t : ℝ ↦ ξ * t) (by fun_prop)
      χ hχ_smooth hχ_compact
  have hC : 0 ≤ C_bilinearSobolevEstimates J χ := by
    rw [C_bilinearSobolevEstimates]
    positivity
  have hm : ∀ η : ℝ, ‖m η‖ ≤ C_bilinearSobolevEstimates J χ *
      japaneseBracket η ^ (-(1 / 2 : ℝ)) := by
    intro η
    exact aux_bilinear_branchTwo_multiplier_bound J χ hJ hχ_smooth hχ_compact
      hχ_nonneg hχ_le_one hχ_support ξ η
  have hFourier : (Lp.fourierTransformₗᵢ ℝ ℂ T : ℝ → ℂ) =ᵐ[volume]
      fun η ↦ m η * (Lp.fourierTransformₗᵢ ℝ ℂ G) η := by
    simpa only [T, m] using
      aux_bilinear_fourier_branchTwo_ae_eq_quadratic_multiplier χ ξ G hκ
  exact aux_bilinear_l2_norm_of_fourier_multiplier_bound T G m
    (C_bilinearSobolevEstimates J χ) hC hm hFourier

/-- The pointwise star operation on the selected complex `L²` quotient
representative is isometric.  This is the norm conversion in the final
Cauchy--Schwarz step of `bilinearSobolevEstimates`. -/
lemma aux_bilinear_norm_star_Lp (g : Lp (α := ℝ) ℂ 2 volume) :
    ‖star g‖ = ‖g‖ := by
  calc
    ‖star g‖ =
        (eLpNorm ((star g : Lp (α := ℝ) ℂ 2 volume) : ℝ → ℂ)
          (2 : ℝ≥0∞) volume).toReal := Lp.norm_def _
    _ = (eLpNorm (star (g : ℝ → ℂ)) (2 : ℝ≥0∞) volume).toReal := by
      exact congrArg ENNReal.toReal (eLpNorm_congr_ae (Lp.coeFn_star g))
    _ = (eLpNorm (g : ℝ → ℂ) (2 : ℝ≥0∞) volume).toReal := by
      rw [eLpNorm_star]
    _ = ‖g‖ := (Lp.norm_def _).symm

/-- The selected `L²` representative of a frequency-character modulation
has the same norm as the original raw function. -/
lemma aux_bilinear_frequencyCharacter_mul_toLp_norm
    (ξ : ℝ) (f : ℝ → ℂ) (hf : MemLp f (2 : ℝ≥0∞) volume)
    (hmod : MemLp (fun x ↦ frequencyCharacter ξ x * f x) (2 : ℝ≥0∞) volume) :
    ‖hmod.toLp (fun x ↦ frequencyCharacter ξ x * f x)‖ =
      (eLpNorm f (2 : ℝ≥0∞) volume).toReal := by
  rw [Lp.norm_toLp, aux_bilinear_frequencyCharacter_mul_norm ξ f hf]

/-- Cauchy--Schwarz in norm form for a trilinear form already identified
with an `L²` pairing. -/
lemma aux_bilinear_trilinearFormAbs_le_pairing_norm
    (χ : ℝ → ℝ) (a b c : ℝ → ℂ)
    (g T : Lp (α := ℝ) ℂ 2 volume)
    (hpair : trilinearForm χ a b c = inner ℂ (star g) T) :
    trilinearFormAbs χ a b c ≤ ‖g‖ * ‖T‖ := by
  unfold trilinearFormAbs
  rw [hpair]
  calc
    ‖inner ℂ (star g) T‖ ≤ ‖star g‖ * ‖T‖ := norm_inner_le_norm _ _
    _ = ‖g‖ * ‖T‖ := by rw [aux_bilinear_norm_star_Lp]

/--
Let \(J\) contain \(\supp\chi\). Define
\[
C_{\ref{prop:bilinear-sobolev},\,J,\chi}
:=
2^5\Ssize{J}{\chi}^{2}.
\]
For every \(\xi\in\mathbb R\) and every \(f_0,f_1,f_2\in L^2(\mathbb R)\),
\[
\Ichi(e_\xi,f_1,f_2)
\leq
C_{\ref{prop:bilinear-sobolev},\,J,\chi}
\hNorm{f_1}{-1/2}\lpNorm{f_2}2,
\]
\[
\Ichi(f_0,e_\xi,f_2)
\leq
C_{\ref{prop:bilinear-sobolev},\,J,\chi}
\lpNorm{f_0}2\hNorm{f_2}{-1/2}.
\]
-/
theorem bilinearSobolevEstimates
    (J : Set ℝ) (χ : ℝ → ℝ)
    (hJ : ∃ jMinus jPlus : ℝ, jMinus ≤ jPlus ∧ J = Set.Icc jMinus jPlus)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (hχ_support : tsupport χ ⊆ J)
    (ξ : ℝ) (f₀ f₁ f₂ : ℝ → ℂ)
    (hf₀ : MemLp f₀ 2 volume) (hf₁ : MemLp f₁ 2 volume) (hf₂ : MemLp f₂ 2 volume) :
    trilinearFormAbs χ (frequencyCharacter ξ) f₁ f₂ ≤
      C_bilinearSobolevEstimates J χ *
        (sobolevNorm (1 / 2 : ℝ) (hf₁.toLp f₁)).toReal *
          (eLpNorm f₂ (2 : ℝ≥0∞) volume).toReal ∧
    trilinearFormAbs χ f₀ (frequencyCharacter ξ) f₂ ≤
      C_bilinearSobolevEstimates J χ *
        (eLpNorm f₀ (2 : ℝ≥0∞) volume).toReal *
          (sobolevNorm (1 / 2 : ℝ) (hf₂.toLp f₂)).toReal := by
  constructor
  · have hmod : MemLp (aux_bilinear_branchOneModulation ξ f₂) 2 volume := by
      change MemLp (fun x ↦ frequencyCharacter ξ x * f₂ x) 2 volume
      exact aux_bilinear_frequencyCharacter_mul_memLp_two ξ f₂ hf₂
    have hκ : Integrable (aux_bilinear_branchOneKernel χ ξ) volume := by
      change Integrable (fun t : ℝ ↦ exponential (-ξ * t ^ 2) * (χ t : ℂ)) volume
      exact aux_bilinear_phaseMul_integrable (fun t : ℝ ↦ -ξ * t ^ 2) (by fun_prop)
        χ hχ_smooth hχ_compact
    have hjoint := aux_bilinear_integrable_branchOne_joint χ ξ f₁ f₂ hf₁ hmod hκ
    have hpair := aux_bilinear_trilinear_branchOne_eq_inner χ ξ f₁ f₂
      hf₁ hmod hκ hjoint
    have hT := aux_bilinear_branchOne_operator_sobolev_bound J χ hJ hχ_smooth
      hχ_compact hχ_nonneg hχ_le_one hχ_support ξ (hf₁.toLp f₁)
    have houter : ‖hmod.toLp (aux_bilinear_branchOneModulation ξ f₂)‖ =
        (eLpNorm f₂ (2 : ℝ≥0∞) volume).toReal := by
      change ‖hmod.toLp (fun x ↦ frequencyCharacter ξ x * f₂ x)‖ = _
      exact aux_bilinear_frequencyCharacter_mul_toLp_norm ξ f₂ hf₂ hmod
    calc
      trilinearFormAbs χ (frequencyCharacter ξ) f₁ f₂ ≤
          ‖hmod.toLp (aux_bilinear_branchOneModulation ξ f₂)‖ *
            ‖aux_bilinear_shiftOperator aux_bilinear_branchOneShift
              (aux_bilinear_branchOneKernel χ ξ) (hf₁.toLp f₁)‖ :=
        aux_bilinear_trilinearFormAbs_le_pairing_norm χ (frequencyCharacter ξ) f₁ f₂
          (hmod.toLp (aux_bilinear_branchOneModulation ξ f₂))
          (aux_bilinear_shiftOperator aux_bilinear_branchOneShift
            (aux_bilinear_branchOneKernel χ ξ) (hf₁.toLp f₁)) hpair
      _ ≤ ‖hmod.toLp (aux_bilinear_branchOneModulation ξ f₂)‖ *
          (C_bilinearSobolevEstimates J χ *
            (sobolevNorm (1 / 2 : ℝ) (hf₁.toLp f₁)).toReal) :=
        mul_le_mul_of_nonneg_left hT (norm_nonneg _)
      _ = C_bilinearSobolevEstimates J χ *
          (sobolevNorm (1 / 2 : ℝ) (hf₁.toLp f₁)).toReal *
            (eLpNorm f₂ (2 : ℝ≥0∞) volume).toReal := by
        rw [houter]
        ring
  · have hmod : MemLp (aux_bilinear_branchTwoModulation ξ f₀) 2 volume := by
      change MemLp (fun x ↦ frequencyCharacter ξ x * f₀ x) 2 volume
      exact aux_bilinear_frequencyCharacter_mul_memLp_two ξ f₀ hf₀
    have hκ : Integrable (aux_bilinear_branchTwoKernel χ ξ) volume := by
      change Integrable (fun t : ℝ ↦ exponential (ξ * t) * (χ t : ℂ)) volume
      exact aux_bilinear_phaseMul_integrable (fun t : ℝ ↦ ξ * t) (by fun_prop)
        χ hχ_smooth hχ_compact
    have hjoint := aux_bilinear_integrable_branchTwo_joint χ ξ f₀ f₂ hf₂ hmod hκ
    have hpair := aux_bilinear_trilinear_branchTwo_eq_inner χ ξ f₀ f₂
      hf₂ hmod hκ hjoint
    have hT := aux_bilinear_branchTwo_operator_sobolev_bound J χ hJ hχ_smooth
      hχ_compact hχ_nonneg hχ_le_one hχ_support ξ (hf₂.toLp f₂)
    have houter : ‖hmod.toLp (aux_bilinear_branchTwoModulation ξ f₀)‖ =
        (eLpNorm f₀ (2 : ℝ≥0∞) volume).toReal := by
      change ‖hmod.toLp (fun x ↦ frequencyCharacter ξ x * f₀ x)‖ = _
      exact aux_bilinear_frequencyCharacter_mul_toLp_norm ξ f₀ hf₀ hmod
    calc
      trilinearFormAbs χ f₀ (frequencyCharacter ξ) f₂ ≤
          ‖hmod.toLp (aux_bilinear_branchTwoModulation ξ f₀)‖ *
            ‖aux_bilinear_shiftOperator aux_bilinear_branchTwoShift
              (aux_bilinear_branchTwoKernel χ ξ) (hf₂.toLp f₂)‖ :=
        aux_bilinear_trilinearFormAbs_le_pairing_norm χ f₀ (frequencyCharacter ξ) f₂
          (hmod.toLp (aux_bilinear_branchTwoModulation ξ f₀))
          (aux_bilinear_shiftOperator aux_bilinear_branchTwoShift
            (aux_bilinear_branchTwoKernel χ ξ) (hf₂.toLp f₂)) hpair
      _ ≤ ‖hmod.toLp (aux_bilinear_branchTwoModulation ξ f₀)‖ *
          (C_bilinearSobolevEstimates J χ *
            (sobolevNorm (1 / 2 : ℝ) (hf₂.toLp f₂)).toReal) :=
        mul_le_mul_of_nonneg_left hT (norm_nonneg _)
      _ = C_bilinearSobolevEstimates J χ *
          (eLpNorm f₀ (2 : ℝ≥0∞) volume).toReal *
            (sobolevNorm (1 / 2 : ℝ) (hf₂.toLp f₂)).toReal := by
        rw [houter]
        ring

end Auto
