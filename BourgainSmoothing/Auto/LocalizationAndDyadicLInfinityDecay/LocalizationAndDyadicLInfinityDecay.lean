/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import BourgainSmoothing.Auto.DegreeLoweringAndNormalizedSmoothing.DegreeLoweringAndNormalizedSmoothing
import BourgainSmoothing.Auto.ExplicitAuxiliaryCutoffs.ExplicitAuxiliaryCutoffs

/-!
# Localization and dyadic \(L^\infty\) decay

Formalizations of the labeled definitions and estimates in the corresponding
section of `blueprint/blueprint.tex`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Real FourierTransform Topology

namespace Auto

/--
The raw tuple underlying `mainInteractionData`.  This auxiliary structure
keeps the source definition separate from the proof that its five entries
form an `AdmissibleSupportData`.
-/
structure aux_MainInteractionData where
  A₀ : Set ℝ
  A₁ : Set ℝ
  A₂ : Set ℝ
  J : Set ℝ
  χ : ℝ → ℝ

/-- The interval \(I_1\) used by `mainInteractionData`. -/
def aux_mainInteractionI1 (a b : ℝ) (χ : ℝ → ℝ) : Set ℝ :=
  Set.Icc (a - supportRadius χ) (b + supportRadius χ)

/-- The interval \(I_2\) used by `mainInteractionData`. -/
def aux_mainInteractionI2 (a b : ℝ) (χ : ℝ → ℝ) : Set ℝ :=
  Set.Icc a (b + supportRadius χ ^ 2)

/-- The interval \(J_\chi\) used by `mainInteractionData`. -/
def aux_mainInteractionJ (χ : ℝ → ℝ) : Set ℝ :=
  Set.Icc (-supportRadius χ) (supportRadius χ)

/-- The first spatial interval used by `mainInteractionData`. -/
def aux_mainInteractionA0 (a b : ℝ) : Set ℝ :=
  Set.Icc (a - 1) (b + 1)

/-- The second spatial interval used by `mainInteractionData`. -/
def aux_mainInteractionA1 (a b : ℝ) (χ : ℝ → ℝ) : Set ℝ :=
  Set.image2 (fun x y : ℝ ↦ x + y) (aux_mainInteractionI1 a b χ) (Set.Icc (-1) 1)

/-- The third spatial interval used by `mainInteractionData`. -/
def aux_mainInteractionA2 (a b : ℝ) (χ : ℝ → ℝ) : Set ℝ :=
  Set.image2 (fun x y : ℝ ↦ x + y) (aux_mainInteractionI2 a b χ) (Set.Icc (-1) 1)

/--
Let \(K=[a,b]\) and define
\[
J_\chi:=[-R_\chi,R_\chi],
\]
\[
I_1:=[a-R_\chi,b+R_\chi],
\qquad
I_2:=[a,b+R_\chi^2],
\]
\[
A_0:=[a-1,b+1],
\qquad
A_1:=I_1+[-1,1],
\qquad
A_2:=I_2+[-1,1].
\]
Write
\[
\mathfrak D_{K,\chi}:=(A_0,A_1,A_2,J_\chi,\chi).
\]
-/
def mainInteractionData (a b : ℝ) (χ : ℝ → ℝ) : aux_MainInteractionData where
  A₀ := aux_mainInteractionA0 a b
  A₁ := aux_mainInteractionA1 a b χ
  A₂ := aux_mainInteractionA2 a b χ
  J := aux_mainInteractionJ χ
  χ := χ

/--
The raw tuple associated with an admissible datum, used to express that
`mainInteractionData` is admissible in `mainInteractionDataAdmissible`.
-/
def aux_admissibleSupportDataToInteractionData
    (D : AdmissibleSupportData) : aux_MainInteractionData where
  A₀ := D.A₀
  A₁ := D.A₁
  A₂ := D.A₂
  J := D.J
  χ := D.χ

/--
The datum \(\mathfrak D_{K,\chi}\) from
\(\label{def:main-interaction-data}\) is admissible.
-/
theorem mainInteractionDataAdmissible
    (a b : ℝ) (χ : ℝ → ℝ) (hab : a ≤ b)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1) :
    ∃ D : AdmissibleSupportData,
      aux_admissibleSupportDataToInteractionData D = mainInteractionData a b χ := by
  let R : ℝ := supportRadius χ
  have hRone : 1 ≤ R := by
    simpa [R] using aux_u3_one_le_supportRadius χ hχ_compact
  have himage : ∀ p q r s : ℝ, p ≤ q → r ≤ s →
      Set.image2 (fun x y : ℝ ↦ x + y) (Set.Icc p q) (Set.Icc r s) =
        Set.Icc (p + r) (q + s) := by
    intro p q r s hpq hrs
    ext x
    constructor
    · rintro ⟨y, hy, z, hz, rfl⟩
      exact ⟨add_le_add hy.1 hz.1, add_le_add hy.2 hz.2⟩
    · intro hx
      rcases le_total x (p + s) with h | h
      · refine ⟨p, ⟨le_rfl, hpq⟩, x - p, ?_, by ring⟩
        constructor <;> linarith [hx.1]
      · refine ⟨x - s, ?_, s, ⟨hrs, le_rfl⟩, by ring⟩
        constructor <;> linarith [hx.2]
  have hA₀ : ∃ u v : ℝ, u < v ∧ aux_mainInteractionA0 a b = Set.Icc u v := by
    exact ⟨a - 1, b + 1, by linarith, rfl⟩
  have hA₁ : ∃ u v : ℝ, u < v ∧ aux_mainInteractionA1 a b χ = Set.Icc u v := by
    refine ⟨a - R - 1, b + R + 1, ?_, ?_⟩
    · linarith
    · rw [aux_mainInteractionA1, aux_mainInteractionI1]
      rw [himage (a - R) (b + R) (-1) 1 (by linarith) (by norm_num)]
      congr 1
  have hA₂ : ∃ u v : ℝ, u < v ∧ aux_mainInteractionA2 a b χ = Set.Icc u v := by
    refine ⟨a - 1, b + R ^ 2 + 1, ?_, ?_⟩
    · nlinarith [sq_nonneg R]
    · rw [aux_mainInteractionA2, aux_mainInteractionI2]
      rw [himage a (b + R ^ 2) (-1) 1 (by nlinarith [sq_nonneg R]) (by norm_num)]
      congr 1
  have hJ : ∃ u v : ℝ, u < v ∧ aux_mainInteractionJ χ = Set.Icc u v := by
    exact ⟨-R, R, by linarith, rfl⟩
  refine ⟨{
    A₀ := aux_mainInteractionA0 a b
    A₁ := aux_mainInteractionA1 a b χ
    A₂ := aux_mainInteractionA2 a b χ
    J := aux_mainInteractionJ χ
    χ := χ
    hA₀ := hA₀
    hA₁ := hA₁
    hA₂ := hA₂
    hJ := hJ
    hχ_smooth := hχ_smooth
    hχ_compact := hχ_compact
    hχ_nonneg := hχ_nonneg
    hχ_le_one := hχ_le_one
    hχ_support := ?_
    hA₀_add_J := ?_
  }, ?_⟩
  · intro t ht
    have ht' := aux_quadratic_tsupport_subset_Ioo_radius χ hχ_compact ht
    change t ∈ Set.Icc (-R) R
    exact ⟨le_of_lt ht'.1, le_of_lt ht'.2⟩
  · rw [aux_mainInteractionA0, aux_mainInteractionJ, aux_mainInteractionA1,
      aux_mainInteractionI1]
    rw [himage (a - 1) (b + 1) (-R) R (by linarith) (by linarith),
      himage (a - R) (b + R) (-1) 1 (by linarith) (by norm_num)]
    convert Set.Subset.rfl using 1 <;> ring
  · rfl

/--
If \(f_0\) is supported in \(K\), then
\[
\Lamchi(f_0,f_1,f_2)
=
\Lamchi(f_0,\rho_{I_1}f_1,\rho_{I_2}f_2).
\]
-/
theorem trilinearFormSpatialLocalization
    (a b : ℝ) (χ : ℝ → ℝ) (hab : a ≤ b)
    (hχ_compact : HasCompactSupport χ)
    (f₀ f₁ f₂ : ℝ → ℂ)
    (hf₀_support : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f₀ x = 0)
    (h_integrable : Integrable (fun p : ℝ × ℝ ↦
      f₀ p.1 * f₁ (p.1 + p.2) * f₂ (p.1 + p.2 ^ 2) * (χ p.2 : ℂ))) :
    trilinearForm χ f₀ f₁ f₂ =
      trilinearForm χ f₀
        (fun x ↦ (spatialCutoff (a - supportRadius χ) (b + supportRadius χ) x : ℂ) * f₁ x)
        (fun x ↦ (spatialCutoff a (b + supportRadius χ ^ 2) x : ℂ) * f₂ x) := by
  unfold trilinearForm
  apply integral_congr_ae
  filter_upwards [hf₀_support] with x hx
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro t
  by_cases hxK : x ∈ Set.Icc a b
  · by_cases hχt : χ t = 0
    · simp [hχt]
    · have ht_support : t ∈ Function.support χ := by
        rw [Function.mem_support]
        exact hχt
      have ht_radius : t ∈ Set.Ioc (-supportRadius χ) (supportRadius χ) :=
        aux_quadratic_support_subset_Ioc_radius χ hχ_compact ht_support
      have hrad : 0 ≤ supportRadius χ :=
        zero_le_one.trans (aux_u3_one_le_supportRadius χ hχ_compact)
      have hx1 : x + t ∈ Set.Icc (a - supportRadius χ) (b + supportRadius χ) := by
        rcases hxK with ⟨hxa, hxb⟩
        rcases ht_radius with ⟨htlo, hthi⟩
        constructor <;> linarith
      have hx2 : x + t ^ 2 ∈ Set.Icc a (b + supportRadius χ ^ 2) := by
        rcases hxK with ⟨hxa, hxb⟩
        rcases ht_radius with ⟨htlo, hthi⟩
        constructor
        · nlinarith [sq_nonneg t]
        · nlinarith
      have hcut1 : spatialCutoff (a - supportRadius χ) (b + supportRadius χ) (x + t) = 1 :=
        aux_spatialCutoff_one_on hx1
      have hcut2 : spatialCutoff a (b + supportRadius χ ^ 2) (x + t ^ 2) = 1 :=
        aux_spatialCutoff_one_on hx2
      simp [hcut1, hcut2]
  · have hxzero : f₀ x = 0 := hx hxK
    simp [hxzero]

/-- The explicit constant in \(\label{lem:localized-sobolev-decay}\), used
by `localizedNegativeSobolevDecay`:
\[
C_{\ref{lem:localized-sobolev-decay},\,I}
:=
2^{19}(2+\lvert I\rvert).
\]
-/
def C_localizedNegativeSobolevDecay (I : Set ℝ) : ℝ :=
  (2 : ℝ) ^ 19 * (2 + intervalLength I)

/--
Every dyadic rescaling of the reciprocal annular kernel has the same explicit
`L¹` bound.  This is the kernel input for the antiderivative used in
`localizedNegativeSobolevDecay`.
-/
lemma aux_scaledReciprocalKernel_l1 (k : ℕ) :
    eLpNorm (aux_scaledInverseFourierKernel aux_dyadicKernelMultiplier k)
      (1 : ℝ≥0∞) volume ≤ 2 ^ 10 := by
  let c : ℝ := (2 : ℝ) ^ k
  let K : ℝ → ℂ := inverseFourierTransform aux_dyadicKernelMultiplier
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hKcont : Continuous K := by
    let hmem : MemLp aux_dyadicKernelMultiplier 1 volume :=
      memLp_one_iff_integrable.mpr aux_dyadicKernelMultiplier_integrable
    unfold K inverseFourierTransform
    rw [← Real.Lp.fourierTransformInv_toLp hmem]
    exact (Real.Lp.fourierTransformInv hmem.toLp).continuous
  have hK : Integrable K volume := by
    apply memLp_one_iff_integrable.mp
    refine ⟨hKcont.aestronglyMeasurable, ?_⟩
    calc
      eLpNorm K 1 volume ≤ ENNReal.ofReal C_dyadicKernelBounds := by
        simpa [K] using dyadicKernelBounds.2
      _ < ∞ := ENNReal.ofReal_lt_top
  have hscale : Integrable (fun x : ℝ ↦ c * ‖K (c * x)‖) volume := by
    have hcomp : Integrable (fun x : ℝ ↦ ‖K (c * x)‖) volume :=
      hK.norm.comp_mul_left' hc.ne'
    exact hcomp.const_mul c
  have hscale_nonneg : 0 ≤ᵐ[volume] fun x : ℝ ↦ c * ‖K (c * x)‖ :=
    Filter.Eventually.of_forall fun x ↦ mul_nonneg hc.le (norm_nonneg _)
  have hK_nonneg : 0 ≤ᵐ[volume] fun x : ℝ ↦ ‖K x‖ :=
    Filter.Eventually.of_forall fun x ↦ norm_nonneg _
  have hintegral : (∫ x : ℝ, c * ‖K (c * x)‖) = ∫ x : ℝ, ‖K x‖ := by
    calc
      (∫ x : ℝ, c * ‖K (c * x)‖) =
          c * ∫ x : ℝ, ‖K (c * x)‖ :=
        integral_const_mul c _
      _ = c * (|c⁻¹| • ∫ x : ℝ, ‖K x‖) := by
        congr 1
        exact Measure.integral_comp_mul_left (fun x : ℝ ↦ ‖K x‖) c
      _ = ∫ x : ℝ, ‖K x‖ := by
        rw [smul_eq_mul, abs_of_pos (inv_pos.mpr hc)]
        field_simp
  have hEq : aux_scaledInverseFourierKernel aux_dyadicKernelMultiplier k =
      fun x ↦ (c : ℂ) * K (c * x) := by
    ext x
    simp [aux_scaledInverseFourierKernel, c, K]
  rw [hEq, eLpNorm_one_eq_lintegral_enorm,
    show (fun x : ℝ ↦ ‖(c : ℂ) * K (c * x)‖ₑ) =
      fun x ↦ ENNReal.ofReal (c * ‖K (c * x)‖) by
        funext x
        rw [← ofReal_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hc],
    ← ofReal_integral_eq_lintegral_ofReal hscale hscale_nonneg,
    hintegral]
  change ENNReal.ofReal (∫ x : ℝ, ‖K x‖) ≤ 2 ^ 10
  have hKnorm : eLpNorm K 1 volume = ENNReal.ofReal (∫ x : ℝ, ‖K x‖) := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    calc
      ∫⁻ x : ℝ, ‖K x‖ₑ = ∫⁻ x : ℝ, ENNReal.ofReal ‖K x‖ := by
        apply lintegral_congr
        intro x
        exact (ofReal_norm (K x)).symm
      _ = ENNReal.ofReal (∫ x : ℝ, ‖K x‖) :=
        (ofReal_integral_eq_lintegral_ofReal hK.norm hK_nonneg).symm
  calc
    ENNReal.ofReal (∫ x : ℝ, ‖K x‖) = eLpNorm K 1 volume := hKnorm.symm
    _ ≤ 2 ^ 10 := by
      simpa [K, C_dyadicKernelBounds] using dyadicKernelBounds.2

/--
After the (2^{-2k}) normalization that makes its second derivative the
annular dyadic kernel, the reciprocal kernel has the correspondingly scaled
`L¹` bound.  This is the size input after integration by parts in
`localizedNegativeSobolevDecay`.
-/
lemma aux_normalizedScaledReciprocalKernel_l1 (k : ℕ) :
    eLpNorm (fun x : ℝ ↦ ((((2 : ℝ) ^ k : ℂ) ^ 2)⁻¹) *
      aux_scaledInverseFourierKernel aux_dyadicKernelMultiplier k x)
      (1 : ℝ≥0∞) volume ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-2 * (k : ℝ))) * (2 : ℝ≥0∞) ^ 10 := by
  let c : ℂ := ((((2 : ℝ) ^ k : ℂ) ^ 2)⁻¹)
  have hbase := aux_scaledReciprocalKernel_l1 k
  calc
    eLpNorm (fun x : ℝ ↦ ((((2 : ℝ) ^ k : ℂ) ^ 2)⁻¹) *
        aux_scaledInverseFourierKernel aux_dyadicKernelMultiplier k x)
        (1 : ℝ≥0∞) volume =
        ENNReal.ofReal ‖c‖ *
          eLpNorm (aux_scaledInverseFourierKernel aux_dyadicKernelMultiplier k)
            (1 : ℝ≥0∞) volume := by
      change eLpNorm (fun x : ℝ ↦ c *
        aux_scaledInverseFourierKernel aux_dyadicKernelMultiplier k x) 1 volume = _
      rw [ofReal_norm]
      convert eLpNorm_const_smul c
        (aux_scaledInverseFourierKernel aux_dyadicKernelMultiplier k)
        (1 : ℝ≥0∞) volume using 1
      apply congrArg (fun f : ℝ → ℂ ↦ eLpNorm f 1 volume)
      funext x
      simp [Pi.smul_apply, smul_eq_mul]
    _ = ENNReal.ofReal ((2 : ℝ) ^ (-2 * (k : ℝ))) *
          eLpNorm (aux_scaledInverseFourierKernel aux_dyadicKernelMultiplier k)
            (1 : ℝ≥0∞) volume := by
      congr 2
      dsimp [c]
      rw [norm_inv, norm_pow]
      norm_num [Complex.norm_real, Real.norm_eq_abs]
      have hpow : (2 : ℝ) ^ k = (2 : ℝ) ^ (k : ℝ) :=
        (Real.rpow_natCast (2 : ℝ) k).symm
      rw [hpow]
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (k : ℝ)) 2]
      rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
      rw [← Real.rpow_neg (by positivity : 0 ≤ (2 : ℝ))]
      congr 1
      ring
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (-2 * (k : ℝ))) * (2 : ℝ≥0∞) ^ 10 :=
      by gcongr

/--
The normalized reciprocal kernel whose second derivative is the scaled
annular kernel.  This auxiliary test kernel is used to transfer derivatives
onto the spatial cutoff in `localizedNegativeSobolevDecay`.
-/
noncomputable def aux_normalizedScaledReciprocalKernel (k : ℕ) : ℝ → ℂ :=
  fun y ↦ ((((2 : ℝ) ^ k : ℂ) ^ 2)⁻¹) *
    aux_scaledInverseFourierKernel aux_dyadicKernelMultiplier k y

/--
The compact frequency support of the reciprocal multiplier supplies all
moments up to order two needed for its Fourier differentiation identity.
-/
lemma aux_dyadicKernelMultiplier_moment_integrable
    (n : ℕ) (hn : n ≤ 2) :
    Integrable (fun ξ : ℝ ↦ ξ ^ n • aux_dyadicKernelMultiplier ξ) volume := by
  apply (aux_dyadicKernelMultiplier_integrable.norm.const_mul 16).mono'
  · exact ((continuous_id.pow n).measurable.smul
      aux_measurable_dyadicKernelMultiplier).aestronglyMeasurable
  · filter_upwards with ξ
    by_cases hξ : ξ ∈ Set.Icc (-4 : ℝ) 4
    · rw [norm_smul, Real.norm_eq_abs, abs_pow]
      have habs : |ξ| ≤ 4 := by
        rcases hξ with ⟨hlo, hhi⟩
        exact abs_le.2 ⟨by linarith, hhi⟩
      have hpow : |ξ| ^ n ≤ (4 : ℝ) ^ n :=
        pow_le_pow_left₀ (abs_nonneg _) habs n
      have hfour : (4 : ℝ) ^ n ≤ 16 := by
        interval_cases n <;> norm_num at hn ⊢
      exact mul_le_mul_of_nonneg_right (hpow.trans hfour) (norm_nonneg _)
    · rw [aux_dyadicKernelMultiplier_eq_zero_of_not_mem ξ hξ]
      simp

/--
The reciprocal annular kernel is a second antiderivative of the annular
kernel.  This is the Fourier identity used to transfer two derivatives onto
the spatial cutoff in `localizedNegativeSobolevDecay`.
-/
lemma aux_inverseFourier_dyadicKernelMultiplier_deriv_two (x : ℝ) :
    deriv (deriv (inverseFourierTransform aux_dyadicKernelMultiplier)) x =
      inverseFourierTransform (fun ξ ↦ (annularCutoff ξ : ℂ)) x := by
  have hmoment : ∀ n : ℕ, (n : ℕ∞) ≤ (2 : ℕ∞) →
      Integrable (fun ξ : ℝ ↦ ξ ^ n • aux_dyadicKernelMultiplier ξ) volume := by
    intro n hn
    exact aux_dyadicKernelMultiplier_moment_integrable n (by exact_mod_cast hn)
  have hfourier := Real.iteratedDeriv_fourier
    (f := aux_dyadicKernelMultiplier) (N := (2 : ℕ∞)) hmoment
    (n := 2) (by norm_num)
  have hmult (ξ : ℝ) :
      (-2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) ^ 2 •
          aux_dyadicKernelMultiplier ξ =
        (annularCutoff ξ : ℂ) := by
    by_cases hξ : ξ = 0
    · subst ξ
      rw [aux_annularCutoff_eq_zero_middle (by norm_num) (by norm_num)]
      simp [aux_dyadicKernelMultiplier]
    · rw [smul_eq_mul]
      unfold aux_dyadicKernelMultiplier
      have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
      have hξ' : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ
      field_simp
      push_cast
      ring
  unfold inverseFourierTransform
  simp_rw [Real.fourierInv_eq_fourier_neg]
  change deriv (deriv (fun y : ℝ ↦ 𝓕 aux_dyadicKernelMultiplier (-y))) x =
    𝓕 (fun ξ : ℝ ↦ (annularCutoff ξ : ℂ)) (-x)
  calc
    deriv (deriv (fun y : ℝ ↦ 𝓕 aux_dyadicKernelMultiplier (-y))) x =
        iteratedDeriv 2 (fun y : ℝ ↦ 𝓕 aux_dyadicKernelMultiplier (-y)) x := by
      simp [iteratedDeriv_succ]
    _ = (-1) ^ 2 • iteratedDeriv 2 (𝓕 aux_dyadicKernelMultiplier) (-x) :=
      iteratedDeriv_comp_neg 2 (𝓕 aux_dyadicKernelMultiplier) x
    _ = ((-1 : ℝ) ^ 2) •
        𝓕 (fun ξ : ℝ ↦ (-2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) ^ 2 •
          aux_dyadicKernelMultiplier ξ) (-x) := by
      exact congrArg (fun H : ℝ → ℂ ↦ ((-1 : ℝ) ^ 2) • H (-x)) hfourier
    _ = 𝓕 (fun ξ : ℝ ↦ (annularCutoff ξ : ℂ)) (-x) := by
      have hmult' :
          (fun ξ : ℝ ↦ (-2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) ^ 2 •
              aux_dyadicKernelMultiplier ξ) =
            fun ξ : ℝ ↦ (annularCutoff ξ : ℂ) := by
        funext ξ
        exact hmult ξ
      rw [hmult']
      norm_num

/--
The reciprocal annular inverse-Fourier kernel is twice continuously
differentiable.  This regularity makes its scaled antiderivative kernel
available for the localization argument.
-/
lemma aux_inverseFourier_dyadicKernelMultiplier_contDiff :
    ContDiff ℝ 2 (inverseFourierTransform aux_dyadicKernelMultiplier) := by
  have hfourier : ContDiff ℝ 2 (𝓕 aux_dyadicKernelMultiplier) := by
    apply Real.contDiff_fourier (N := (2 : ℕ∞))
    intro n hn
    simpa only [norm_smul, Real.norm_eq_abs, abs_pow] using
      (aux_dyadicKernelMultiplier_moment_integrable n (by exact_mod_cast hn)).norm
  unfold inverseFourierTransform
  simp_rw [Real.fourierInv_eq_fourier_neg]
  simpa [Function.comp_def] using hfourier.comp (contDiff_neg)

/--
After normalizing the reciprocal dyadic kernel by (2^{-2k}), its second
derivative is exactly the dyadic annular kernel.  This is the scaled Fourier
identity used to move two derivatives onto the spatial cutoff in
`localizedNegativeSobolevDecay`.
-/
lemma aux_normalizedScaledInverseFourier_dyadicKernelMultiplier_deriv_two
    (k : ℕ) (x : ℝ) :
    deriv (deriv (fun y : ℝ ↦
      ((((2 : ℝ) ^ k : ℂ) ^ 2)⁻¹) *
        aux_scaledInverseFourierKernel aux_dyadicKernelMultiplier k y)) x =
      aux_scaledInverseFourierKernel (fun ξ ↦ (annularCutoff ξ : ℂ)) k x := by
  let s : ℝ := (2 : ℝ) ^ k
  let K : ℝ → ℂ := inverseFourierTransform aux_dyadicKernelMultiplier
  have hs : s ≠ 0 := by
    dsimp [s]
    positivity
  have hK : ContDiff ℝ 2 K := by
    simpa [K] using aux_inverseFourier_dyadicKernelMultiplier_contDiff
  have hKtwo : ∀ z : ℝ, deriv (deriv K) z =
      inverseFourierTransform (fun ξ ↦ (annularCutoff ξ : ℂ)) z := by
    intro z
    simpa [K] using aux_inverseFourier_dyadicKernelMultiplier_deriv_two z
  have hlinear : ContDiff ℝ 2 (fun y : ℝ ↦ s * y) := by
    change ContDiff ℝ 2 (fun y : ℝ ↦ s • y)
    exact contDiff_const_smul s
  have hscaled : ContDiff ℝ 2 (fun y : ℝ ↦ K (s * y)) := by
    simpa [Function.comp_def] using hK.comp hlinear
  have hscale := congrFun (iteratedDeriv_comp_const_smul (n := 2) hK s) x
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hfun :
      (fun y : ℝ ↦ ((((2 : ℝ) ^ k : ℂ) ^ 2)⁻¹) *
        aux_scaledInverseFourierKernel aux_dyadicKernelMultiplier k y) =
        fun y : ℝ ↦ ((s : ℂ)⁻¹) * K (s * y) := by
    funext y
    dsimp [s, K]
    unfold aux_scaledInverseFourierKernel
    field_simp
    push_cast
    ring
  rw [hfun]
  calc
    deriv (deriv (fun y : ℝ ↦ ((s : ℂ)⁻¹) * K (s * y))) x =
        iteratedDeriv 2 (fun y : ℝ ↦ ((s : ℂ)⁻¹) * K (s * y)) x := by
      simp [iteratedDeriv_succ]
    _ = (s : ℂ)⁻¹ • iteratedDeriv 2 (fun y : ℝ ↦ K (s * y)) x := by
      change iteratedDeriv 2 ((s : ℂ)⁻¹ • (fun y : ℝ ↦ K (s * y))) x = _
      rw [iteratedDeriv_const_smul (n := 2) hscaled.contDiffAt]
    _ = (s : ℂ)⁻¹ • (s ^ 2 • iteratedDeriv 2 K (s * x)) := by
      rw [hscale]
    _ = (s : ℂ)⁻¹ • (s ^ 2 • deriv (deriv K) (s * x)) := by
      simp [iteratedDeriv_succ]
    _ = (s : ℂ)⁻¹ •
        (s ^ 2 • inverseFourierTransform (fun ξ ↦ (annularCutoff ξ : ℂ)) (s * x)) := by
      rw [hKtwo]
    _ = (s : ℂ) * inverseFourierTransform (fun ξ ↦ (annularCutoff ξ : ℂ)) (s * x) := by
      rw [Complex.real_smul, smul_eq_mul]
      push_cast
      field_simp
    _ = aux_scaledInverseFourierKernel (fun ξ ↦ (annularCutoff ξ : ℂ)) k x := by
      simp [aux_scaledInverseFourierKernel, s]

/--
This finite-interval double integration-by-parts identity transfers two
derivatives from the normalized reciprocal kernel onto one polynomial piece
of the spatial cutoff.  The derivative hypotheses are only imposed in the
open interval, so the three pieces of `spatialCutoff` can be handled without
requiring a globally (C^2) cutoff in `localizedNegativeSobolevDecay`.
-/
lemma aux_intervalIntegral_mul_deriv_twice
    {r s : ℝ} {u u₁ u₂ v v₁ v₂ : ℝ → ℂ}
    (hu : ContinuousOn u (Set.uIcc r s))
    (hu₁ : ContinuousOn u₁ (Set.uIcc r s))
    (hv : ContinuousOn v (Set.uIcc r s))
    (hv₁ : ContinuousOn v₁ (Set.uIcc r s))
    (hdu : ∀ x ∈ Set.Ioo (min r s) (max r s), HasDerivAt u (u₁ x) x)
    (hdu₁ : ∀ x ∈ Set.Ioo (min r s) (max r s), HasDerivAt u₁ (u₂ x) x)
    (hdv : ∀ x ∈ Set.Ioo (min r s) (max r s), HasDerivAt v (v₁ x) x)
    (hdv₁ : ∀ x ∈ Set.Ioo (min r s) (max r s), HasDerivAt v₁ (v₂ x) x)
    (hu₁_int : IntervalIntegrable u₁ volume r s)
    (hu₂_int : IntervalIntegrable u₂ volume r s)
    (hv₁_int : IntervalIntegrable v₁ volume r s)
    (hv₂_int : IntervalIntegrable v₂ volume r s) :
    (∫ x in r..s, u₂ x * v x) =
      u₁ s * v s - u₁ r * v r - (u s * v₁ s - u r * v₁ r) +
        ∫ x in r..s, u x * v₂ x := by
  have hfirst := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hu₁ hv hdu₁ hdv hu₂_int hv₁_int
  have hsecond := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hu hv₁ hdu hdv₁ hu₁_int hv₂_int
  linear_combination hfirst - hsecond

/--
The normalized reciprocal kernel is twice continuously differentiable.  This
regularity supplies the ordinary derivatives used by
`aux_interval_dyadicKernel_transfer` in the localization proof.
-/
lemma aux_normalizedScaledReciprocalKernel_contDiff (k : ℕ) :
    ContDiff ℝ 2 (aux_normalizedScaledReciprocalKernel k) := by
  let s : ℝ := (2 : ℝ) ^ k
  let K : ℝ → ℂ := inverseFourierTransform aux_dyadicKernelMultiplier
  have hK : ContDiff ℝ 2 K := by
    simpa [K] using aux_inverseFourier_dyadicKernelMultiplier_contDiff
  have hlinear : ContDiff ℝ 2 (fun y : ℝ ↦ s * y) := by
    change ContDiff ℝ 2 (fun y : ℝ ↦ s • y)
    exact contDiff_const_smul s
  have hscaled : ContDiff ℝ 2 (fun y : ℝ ↦ K (s * y)) := by
    simpa [Function.comp_def] using hK.comp hlinear
  have hfun : aux_normalizedScaledReciprocalKernel k =
        fun y : ℝ ↦ ((s : ℂ)⁻¹) * K (s * y) := by
    funext y
    change
      (((((2 : ℝ) ^ k : ℂ) ^ 2)⁻¹) *
        aux_scaledInverseFourierKernel aux_dyadicKernelMultiplier k y) = _
    dsimp [s, K]
    unfold aux_scaledInverseFourierKernel
    have hs : (2 : ℝ) ^ k ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  rw [hfun]
  simpa [smul_eq_mul] using ((hscaled.const_smul ((s : ℂ)⁻¹)) :
    ContDiff ℝ 2 (fun y : ℝ ↦ ((s : ℂ)⁻¹) • K (s * y)))

/--
The normalized reciprocal kernel is in `L¹`, so it can be used as the
post-integration-by-parts convolution kernel in
`localizedNegativeSobolevDecay`.
-/
lemma aux_normalizedScaledReciprocalKernel_memLp_one (k : ℕ) :
    MemLp (aux_normalizedScaledReciprocalKernel k) (1 : ℝ≥0∞) volume := by
  refine ⟨(aux_normalizedScaledReciprocalKernel_contDiff k).continuous.aestronglyMeasurable,
    ?_⟩
  calc
    eLpNorm (aux_normalizedScaledReciprocalKernel k) 1 volume ≤
        ENNReal.ofReal ((2 : ℝ) ^ (-2 * (k : ℝ))) * (2 : ℝ≥0∞) ^ 10 :=
      aux_normalizedScaledReciprocalKernel_l1 k
    _ < ∞ := by finiteness

/--
On a finite interval, the second-derivative identity for the normalized
reciprocal kernel transfers both derivatives to an arbitrary twice
differentiable test function.  This is the interval-wise integration by
parts step for `localizedNegativeSobolevDecay`.
-/
lemma aux_interval_dyadicKernel_transfer
    (k : ℕ) {r s : ℝ} {v v₁ v₂ : ℝ → ℂ}
    (hv : ContinuousOn v (Set.uIcc r s))
    (hv₁ : ContinuousOn v₁ (Set.uIcc r s))
    (hdv : ∀ x ∈ Set.Ioo (min r s) (max r s), HasDerivAt v (v₁ x) x)
    (hdv₁ : ∀ x ∈ Set.Ioo (min r s) (max r s), HasDerivAt v₁ (v₂ x) x)
    (hv₁_int : IntervalIntegrable v₁ volume r s)
    (hv₂_int : IntervalIntegrable v₂ volume r s) :
    (∫ x in r..s,
      aux_scaledInverseFourierKernel (fun ξ ↦ (annularCutoff ξ : ℂ)) k x * v x) =
      deriv (aux_normalizedScaledReciprocalKernel k) s * v s -
      deriv (aux_normalizedScaledReciprocalKernel k) r * v r -
      (aux_normalizedScaledReciprocalKernel k s * v₁ s -
        aux_normalizedScaledReciprocalKernel k r * v₁ r) +
      ∫ x in r..s, aux_normalizedScaledReciprocalKernel k x * v₂ x := by
  let u : ℝ → ℂ := aux_normalizedScaledReciprocalKernel k
  have huC2 : ContDiff ℝ 2 u := by
    simpa [u] using aux_normalizedScaledReciprocalKernel_contDiff k
  have hu : ContinuousOn u (Set.uIcc r s) := huC2.continuous.continuousOn
  have hu₁ : ContinuousOn (deriv u) (Set.uIcc r s) :=
    (huC2.continuous_deriv (by norm_num)).continuousOn
  have hdu : ∀ x ∈ Set.Ioo (min r s) (max r s),
      HasDerivAt u (deriv u x) x := by
    intro x hx
    exact (huC2.contDiffAt.differentiableAt (by norm_num)).hasDerivAt
  have hdu₁ : ∀ x ∈ Set.Ioo (min r s) (max r s),
      HasDerivAt (deriv u) (deriv (deriv u) x) x := by
    intro x hx
    have hderiv : ContDiff ℝ 1 (deriv u) := by
      have huC2' : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) u := by
        norm_num
        exact huC2
      exact (contDiff_succ_iff_deriv.mp huC2').2.2
    exact (hderiv.contDiffAt.differentiableAt (by norm_num)).hasDerivAt
  have hu₁_int : IntervalIntegrable (deriv u) volume r s :=
    (huC2.continuous_deriv (by norm_num)).intervalIntegrable r s
  have hu₂_int : IntervalIntegrable (deriv (deriv u)) volume r s := by
    have hderiv : ContDiff ℝ 1 (deriv u) := by
      have huC2' : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) u := by
        norm_num
        exact huC2
      exact (contDiff_succ_iff_deriv.mp huC2').2.2
    exact (hderiv.continuous_deriv (by norm_num)).intervalIntegrable r s
  have hmain := aux_intervalIntegral_mul_deriv_twice hu hu₁ hv hv₁
    hdu hdu₁ hdv hdv₁ hu₁_int hu₂_int hv₁_int hv₂_int
  have htwo : deriv (deriv u) =
      aux_scaledInverseFourierKernel (fun ξ ↦ (annularCutoff ξ : ℂ)) k := by
    funext x
    dsimp [u, aux_normalizedScaledReciprocalKernel]
    exact aux_normalizedScaledInverseFourier_dyadicKernelMultiplier_deriv_two k x
  rw [htwo] at hmain
  simpa only [u] using hmain

/--
Fubini and the determinant-one shear rewrite a test pairing of raw
convolution as a pairing of the input with translated test functions.  This
is the testing bridge used to move the two reciprocal-kernel derivatives in
`localizedNegativeSobolevDecay`.
-/
lemma aux_integral_mul_aux_convolution_eq_sheared
    (κ g φ : ℝ → ℂ) (hκ : Integrable κ volume) (hφ : Integrable φ volume)
    (hg : AEStronglyMeasurable g volume) (C : ℝ)
    (hgbound : ∀ᵐ x : ℝ ∂volume, ‖g x‖ ≤ C) :
    (∫ x : ℝ, φ x * aux_convolution κ g x) =
      ∫ y : ℝ, g y * (∫ t : ℝ, κ t * φ (y + t)) := by
  let H : ℝ × ℝ → ℂ := fun z ↦ φ z.1 * (κ z.2 * g (z.1 - z.2))
  have hHmeas : AEStronglyMeasurable H (volume.prod volume) := by
    dsimp [H]
    refine hφ.1.comp_fst.mul (hκ.1.comp_snd.mul ?_)
    exact hg.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant volume volume)
  have hmajor : Integrable
      (fun z : ℝ × ℝ ↦ (C * ‖φ z.1‖) * ‖κ z.2‖) (volume.prod volume) := by
    exact (hφ.norm.const_mul C).mul_prod hκ.norm
  have hgbound_prod : ∀ᵐ z : ℝ × ℝ ∂(volume.prod volume),
      ‖g (z.1 - z.2)‖ ≤ C :=
    (quasiMeasurePreserving_sub_of_right_invariant volume volume).tendsto_ae hgbound
  have hH : Integrable H (volume.prod volume) := by
    apply hmajor.mono' hHmeas
    filter_upwards [hgbound_prod] with z hz
    dsimp [H]
    calc
      ‖φ z.1 * (κ z.2 * g (z.1 - z.2))‖ =
          ‖φ z.1‖ * ‖κ z.2‖ * ‖g (z.1 - z.2)‖ := by
        rw [norm_mul, norm_mul]
        ring
      _ ≤ ‖φ z.1‖ * ‖κ z.2‖ * C := by
        exact mul_le_mul_of_nonneg_left hz
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (C * ‖φ z.1‖) * ‖κ z.2‖ := by ring
  let T : ℝ × ℝ → ℝ × ℝ := fun z ↦ (z.1 + z.2, z.1)
  let e : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    (MeasurableEquiv.shearAddRight ℝ).trans MeasurableEquiv.prodComm
  have hT : MeasurePreserving T (volume.prod volume) (volume.prod volume) := by
    have h := (Measure.measurePreserving_swap :
      MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ)
        (volume.prod volume) (volume.prod volume)).comp
      (measurePreserving_prod_add volume volume)
    convert h using 1
    funext z
    rcases z with ⟨t, y⟩
    rfl
  have he : (e : ℝ × ℝ → ℝ × ℝ) = T := by
    funext z
    rcases z with ⟨t, y⟩
    rfl
  have hHT : Integrable (H ∘ T) (volume.prod volume) := by
    rw [← memLp_one_iff_integrable] at hH ⊢
    exact hH.comp_measurePreserving hT
  have hshear : (∫ z : ℝ × ℝ, H z) = ∫ z : ℝ × ℝ, H (T z) := by
    rw [← he]
    exact (hT.integral_comp e.measurableEmbedding H).symm
  calc
    (∫ x : ℝ, φ x * aux_convolution κ g x) =
        ∫ x : ℝ, ∫ t : ℝ, H (x, t) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [H, aux_convolution]
      rw [← integral_const_mul]
    _ = ∫ z : ℝ × ℝ, H z := integral_integral hH
    _ = ∫ z : ℝ × ℝ, H (T z) := hshear
    _ = ∫ t : ℝ, ∫ y : ℝ, H (T (t, y)) := integral_prod _ hHT
    _ = ∫ y : ℝ, ∫ t : ℝ, H (T (t, y)) := integral_integral_swap hHT
    _ = ∫ y : ℝ, g y * (∫ t : ℝ, κ t * φ (y + t)) := by
      apply integral_congr_ae
      filter_upwards with y
      have hcomm :
          (∫ t : ℝ, H (T (t, y))) =
            ∫ t : ℝ, g y * (κ t * φ (y + t)) := by
        apply integral_congr_ae
        filter_upwards with t
        dsimp [H, T]
        ring
      rw [hcomm, ← integral_const_mul]

/-- The Fourier phase used to test the localized dyadic convolution in
`localizedNegativeSobolevDecay`. -/
noncomputable def aux_localizedPhase (ξ : ℝ) : ℝ → ℂ :=
  fun x ↦ Complex.exp (((2 * Real.pi * (-(x * ξ)) : ℝ) : ℂ) * Complex.I)

/-- The first ordinary derivative of `aux_localizedPhase`, used in the
twofold interval integration by parts for `localizedNegativeSobolevDecay`. -/
noncomputable def aux_localizedPhaseDeriv (ξ : ℝ) : ℝ → ℂ :=
  fun x ↦ (-2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) *
    aux_localizedPhase ξ x

/-- The second ordinary derivative of `aux_localizedPhase`, used in the
twofold interval integration by parts for `localizedNegativeSobolevDecay`. -/
noncomputable def aux_localizedPhaseDerivTwo (ξ : ℝ) : ℝ → ℂ :=
  fun x ↦ (-2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) ^ 2 *
    aux_localizedPhase ξ x

/-- Supplies the first derivative required for the phase test in
`localizedNegativeSobolevDecay`. -/
lemma aux_localizedPhase_hasDerivAt (ξ x : ℝ) :
    HasDerivAt (aux_localizedPhase ξ) (aux_localizedPhaseDeriv ξ x) x := by
  have hmul : HasDerivAt (fun y : ℝ ↦ y * ξ) ξ x :=
    by simpa using (hasDerivAt_id x).mul_const ξ
  have hneg : HasDerivAt (fun y : ℝ ↦ -(y * ξ)) (-ξ) x := hmul.neg
  have harg : HasDerivAt (fun y : ℝ ↦ 2 * Real.pi * (-(y * ξ)))
      (2 * Real.pi * (-ξ)) x := hneg.const_mul (2 * Real.pi)
  have hargC : HasDerivAt
      (fun y : ℝ ↦ ((2 * Real.pi * (-(y * ξ)) : ℝ) : ℂ) * Complex.I)
      (((2 * Real.pi * (-ξ) : ℝ) : ℂ) * Complex.I) x :=
    harg.ofReal_comp.mul_const Complex.I
  have h := hargC.cexp
  change HasDerivAt
    (fun y : ℝ ↦ Complex.exp (((2 * Real.pi * (-(y * ξ)) : ℝ) : ℂ) * Complex.I))
    ((-2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) *
      Complex.exp (((2 * Real.pi * (-(x * ξ)) : ℝ) : ℂ) * Complex.I)) x
  convert h using 1
  push_cast
  ring

/-- Supplies the second derivative required for the phase test in
`localizedNegativeSobolevDecay`. -/
lemma aux_localizedPhaseDeriv_hasDerivAt (ξ x : ℝ) :
    HasDerivAt (aux_localizedPhaseDeriv ξ)
      (aux_localizedPhaseDerivTwo ξ x) x := by
  exact ((aux_localizedPhase_hasDerivAt ξ x).const_mul
    (-2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ))).congr_deriv (by
      simp only [aux_localizedPhaseDeriv, aux_localizedPhaseDerivTwo]
      ring)

/-- Continuity of the phase used to establish interval integrability in
`localizedNegativeSobolevDecay`. -/
lemma aux_localizedPhase_continuous (ξ : ℝ) :
    Continuous (aux_localizedPhase ξ) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (aux_localizedPhase_hasDerivAt ξ x).continuousAt

/-- Continuity of the first phase derivative used for interval integration
by parts in `localizedNegativeSobolevDecay`. -/
lemma aux_localizedPhaseDeriv_continuous (ξ : ℝ) :
    Continuous (aux_localizedPhaseDeriv ξ) := by
  exact continuous_const.mul (aux_localizedPhase_continuous ξ)

/-- Continuity of the second phase derivative used for interval integration
by parts in `localizedNegativeSobolevDecay`. -/
lemma aux_localizedPhaseDerivTwo_continuous (ξ : ℝ) :
    Continuous (aux_localizedPhaseDerivTwo ξ) := by
  exact continuous_const.mul (aux_localizedPhase_continuous ξ)

/-- Identifies the explicit phase with the Fourier character occurring in
the Fourier-testing step of `localizedNegativeSobolevDecay`. -/
lemma aux_localizedPhase_eq_fourierPhase (ξ x : ℝ) :
    aux_localizedPhase ξ x =
      (Real.fourierChar (-inner ℝ x ξ) : ℂ) := by
  rw [aux_localizedPhase, Real.fourierChar_apply]
  congr 1
  simp only [Real.inner_apply]

/-- The cubic left transition used to describe `spatialCutoff` piecewise in
the proof of `localizedNegativeSobolevDecay`. -/
def aux_leftSpatialCutoff (a : ℝ) : ℝ → ℝ :=
  fun x ↦ 3 * (x - a + 1) ^ 2 - 2 * (x - a + 1) ^ 3

/-- The first derivative of the left cubic transition used in
`localizedNegativeSobolevDecay`. -/
def aux_leftSpatialCutoffDeriv (a : ℝ) : ℝ → ℝ :=
  fun x ↦ 6 * (x - a + 1) - 6 * (x - a + 1) ^ 2

/-- The second derivative of the left cubic transition used in
`localizedNegativeSobolevDecay`. -/
def aux_leftSpatialCutoffDerivTwo (a : ℝ) : ℝ → ℝ :=
  fun x ↦ 6 - 12 * (x - a + 1)

/-- Verifies the first derivative of the left transition for the interval
transfer in `localizedNegativeSobolevDecay`. -/
lemma aux_leftSpatialCutoff_hasDerivAt (a x : ℝ) :
    HasDerivAt (aux_leftSpatialCutoff a) (aux_leftSpatialCutoffDeriv a x) x := by
  have hu : HasDerivAt (fun y : ℝ ↦ y - a + 1) 1 x := by
    simpa only [id_eq] using ((hasDerivAt_id x).sub_const a).add_const 1
  have h2 := hu.pow 2
  have h3 := hu.pow 3
  have h := (h2.const_mul 3).sub (h3.const_mul 2)
  have hfun : aux_leftSpatialCutoff a =ᶠ[𝓝 x]
      ((fun y : ℝ ↦ 3 * ((fun z : ℝ ↦ z - a + 1) ^ 2) y) -
        fun y ↦ 2 * ((fun z : ℝ ↦ z - a + 1) ^ 3) y) :=
    Filter.Eventually.of_forall fun y ↦ by
      simp only [aux_leftSpatialCutoff, Pi.pow_apply, Pi.sub_apply]
  apply (h.congr_of_eventuallyEq hfun).congr_deriv
  simp only [aux_leftSpatialCutoffDeriv]
  norm_num
  ring

/-- Verifies the second derivative of the left transition for the interval
transfer in `localizedNegativeSobolevDecay`. -/
lemma aux_leftSpatialCutoffDeriv_hasDerivAt (a x : ℝ) :
    HasDerivAt (aux_leftSpatialCutoffDeriv a)
      (aux_leftSpatialCutoffDerivTwo a x) x := by
  have hu : HasDerivAt (fun y : ℝ ↦ y - a + 1) 1 x := by
    simpa only [id_eq] using ((hasDerivAt_id x).sub_const a).add_const 1
  have h2 := hu.pow 2
  have h := (hu.const_mul 6).sub (h2.const_mul 6)
  have hfun : aux_leftSpatialCutoffDeriv a =ᶠ[𝓝 x]
      ((fun y : ℝ ↦ 6 * (y - a + 1)) -
        fun y ↦ 6 * ((fun z : ℝ ↦ z - a + 1) ^ 2) y) :=
    Filter.Eventually.of_forall fun y ↦ by
      simp only [aux_leftSpatialCutoffDeriv, Pi.pow_apply, Pi.sub_apply]
  apply (h.congr_of_eventuallyEq hfun).congr_deriv
  simp only [aux_leftSpatialCutoffDerivTwo]
  norm_num
  ring

/-- Continuity of the left cutoff transition used to make its pieces
interval-integrable in `localizedNegativeSobolevDecay`. -/
lemma aux_leftSpatialCutoff_continuous (a : ℝ) :
    Continuous (aux_leftSpatialCutoff a) := by
  exact continuous_const.mul ((continuous_id.sub continuous_const).add continuous_const |>.pow 2)
    |>.sub (continuous_const.mul
      ((continuous_id.sub continuous_const).add continuous_const |>.pow 3))

/-- Continuity of the first left-transition derivative used in
`localizedNegativeSobolevDecay`. -/
lemma aux_leftSpatialCutoffDeriv_continuous (a : ℝ) :
    Continuous (aux_leftSpatialCutoffDeriv a) := by
  exact continuous_const.mul ((continuous_id.sub continuous_const).add continuous_const)
    |>.sub (continuous_const.mul
      ((continuous_id.sub continuous_const).add continuous_const |>.pow 2))

/-- Continuity of the second left-transition derivative used in
`localizedNegativeSobolevDecay`. -/
lemma aux_leftSpatialCutoffDerivTwo_continuous (a : ℝ) :
    Continuous (aux_leftSpatialCutoffDerivTwo a) := by
  exact continuous_const.sub (continuous_const.mul
    ((continuous_id.sub continuous_const).add continuous_const))

/-- Identifies `spatialCutoff` with its cubic left transition on the left
boundary interval for `localizedNegativeSobolevDecay`. -/
lemma aux_spatialCutoff_eq_leftPiece (a b x : ℝ) (hab : a ≤ b)
    (hx : x ∈ Set.Icc (a - 1) a) :
    spatialCutoff a b x = aux_leftSpatialCutoff a x := by
  have hu0 : 0 ≤ x - a + 1 := by linarith [hx.1]
  have hu1 : x - a + 1 ≤ 1 := by linarith [hx.2]
  have hright : 1 ≤ b + 1 - x := by linarith [hx.2, hab]
  rw [spatialCutoff, aux_smoothStep_eq_one_of_one_le hright, mul_one]
  by_cases hzero : x - a + 1 ≤ 0
  · have hval : x - a + 1 = 0 := by linarith
    rw [aux_smoothStep_eq_zero_of_nonpos hzero]
    simp only [aux_leftSpatialCutoff, hval]
    norm_num
  by_cases hmid : x - a + 1 < 1
  · rw [show smoothStep (x - a + 1) =
        3 * (x - a + 1) ^ 2 - 2 * (x - a + 1) ^ 3 by
      simp [smoothStep, hzero, hmid], aux_leftSpatialCutoff]
  · have hone : 1 ≤ x - a + 1 := le_of_not_gt hmid
    have hval : x - a + 1 = 1 := by linarith
    rw [aux_smoothStep_eq_one_of_one_le hone]
    simp only [aux_leftSpatialCutoff, hval]
    norm_num

/-- The cubic right transition used to describe `spatialCutoff` piecewise in
the proof of `localizedNegativeSobolevDecay`. -/
def aux_rightSpatialCutoff (b : ℝ) : ℝ → ℝ :=
  fun x ↦ 3 * (b + 1 - x) ^ 2 - 2 * (b + 1 - x) ^ 3

/-- The first derivative of the right cubic transition used in
`localizedNegativeSobolevDecay`. -/
def aux_rightSpatialCutoffDeriv (b : ℝ) : ℝ → ℝ :=
  fun x ↦ -6 * (b + 1 - x) + 6 * (b + 1 - x) ^ 2

/-- The second derivative of the right cubic transition used in
`localizedNegativeSobolevDecay`. -/
def aux_rightSpatialCutoffDerivTwo (b : ℝ) : ℝ → ℝ :=
  fun x ↦ 6 - 12 * (b + 1 - x)

/-- Verifies the first derivative of the right transition for the interval
transfer in `localizedNegativeSobolevDecay`. -/
lemma aux_rightSpatialCutoff_hasDerivAt (b x : ℝ) :
    HasDerivAt (aux_rightSpatialCutoff b) (aux_rightSpatialCutoffDeriv b x) x := by
  have hu : HasDerivAt (fun y : ℝ ↦ b + 1 - y) (-1) x := by
    simpa only [id_eq] using (hasDerivAt_id x).const_sub (b + 1)
  have h2 := hu.pow 2
  have h3 := hu.pow 3
  have h := (h2.const_mul 3).sub (h3.const_mul 2)
  have hfun : aux_rightSpatialCutoff b =ᶠ[𝓝 x]
      ((fun y : ℝ ↦ 3 * ((fun z : ℝ ↦ b + 1 - z) ^ 2) y) -
        fun y ↦ 2 * ((fun z : ℝ ↦ b + 1 - z) ^ 3) y) :=
    Filter.Eventually.of_forall fun y ↦ by
      simp only [aux_rightSpatialCutoff, Pi.pow_apply, Pi.sub_apply]
  apply (h.congr_of_eventuallyEq hfun).congr_deriv
  simp only [aux_rightSpatialCutoffDeriv]
  norm_num
  ring

/-- Verifies the second derivative of the right transition for the interval
transfer in `localizedNegativeSobolevDecay`. -/
lemma aux_rightSpatialCutoffDeriv_hasDerivAt (b x : ℝ) :
    HasDerivAt (aux_rightSpatialCutoffDeriv b)
      (aux_rightSpatialCutoffDerivTwo b x) x := by
  have hu : HasDerivAt (fun y : ℝ ↦ b + 1 - y) (-1) x := by
    simpa only [id_eq] using (hasDerivAt_id x).const_sub (b + 1)
  have h2 := hu.pow 2
  have h := (hu.const_mul (-6)).add (h2.const_mul 6)
  have hfun : aux_rightSpatialCutoffDeriv b =ᶠ[𝓝 x]
      ((fun y : ℝ ↦ -6 * (b + 1 - y)) +
        fun y ↦ 6 * ((fun z : ℝ ↦ b + 1 - z) ^ 2) y) :=
    Filter.Eventually.of_forall fun y ↦ by
      simp only [aux_rightSpatialCutoffDeriv, Pi.pow_apply, Pi.add_apply]
  apply (h.congr_of_eventuallyEq hfun).congr_deriv
  simp only [aux_rightSpatialCutoffDerivTwo]
  norm_num
  ring

/-- Continuity of the right cutoff transition used to make its pieces
interval-integrable in `localizedNegativeSobolevDecay`. -/
lemma aux_rightSpatialCutoff_continuous (b : ℝ) :
    Continuous (aux_rightSpatialCutoff b) := by
  exact continuous_const.mul ((continuous_const.add continuous_const).sub continuous_id |>.pow 2)
    |>.sub (continuous_const.mul
      ((continuous_const.add continuous_const).sub continuous_id |>.pow 3))

/-- Continuity of the first right-transition derivative used in
`localizedNegativeSobolevDecay`. -/
lemma aux_rightSpatialCutoffDeriv_continuous (b : ℝ) :
    Continuous (aux_rightSpatialCutoffDeriv b) := by
  exact (continuous_const.mul ((continuous_const.add continuous_const).sub continuous_id))
    |>.add (continuous_const.mul
      ((continuous_const.add continuous_const).sub continuous_id |>.pow 2))

/-- Continuity of the second right-transition derivative used in
`localizedNegativeSobolevDecay`. -/
lemma aux_rightSpatialCutoffDerivTwo_continuous (b : ℝ) :
    Continuous (aux_rightSpatialCutoffDerivTwo b) := by
  exact continuous_const.sub (continuous_const.mul
    ((continuous_const.add continuous_const).sub continuous_id))

/-- Identifies `spatialCutoff` with its cubic right transition on the right
boundary interval for `localizedNegativeSobolevDecay`. -/
lemma aux_spatialCutoff_eq_rightPiece (a b x : ℝ) (hab : a ≤ b)
    (hx : x ∈ Set.Icc b (b + 1)) :
    spatialCutoff a b x = aux_rightSpatialCutoff b x := by
  have hu0 : 0 ≤ b + 1 - x := by linarith [hx.2]
  have hu1 : b + 1 - x ≤ 1 := by linarith [hx.1]
  have hleft : 1 ≤ x - a + 1 := by linarith [hx.1, hab]
  rw [spatialCutoff, aux_smoothStep_eq_one_of_one_le hleft, one_mul]
  by_cases hzero : b + 1 - x ≤ 0
  · have hval : b + 1 - x = 0 := by linarith
    rw [aux_smoothStep_eq_zero_of_nonpos hzero]
    simp only [aux_rightSpatialCutoff, hval]
    norm_num
  by_cases hmid : b + 1 - x < 1
  · rw [show smoothStep (b + 1 - x) =
        3 * (b + 1 - x) ^ 2 - 2 * (b + 1 - x) ^ 3 by
      simp [smoothStep, hzero, hmid], aux_rightSpatialCutoff]
  · have hone : 1 ≤ b + 1 - x := le_of_not_gt hmid
    have hval : b + 1 - x = 1 := by linarith
    rw [aux_smoothStep_eq_one_of_one_le hone]
    simp only [aux_rightSpatialCutoff, hval]
    norm_num

/-- The phase times the left cubic transition, used as the left test function
in the twofold integration by parts for `localizedNegativeSobolevDecay`. -/
noncomputable def aux_leftLocalizedTest (a ξ y : ℝ) : ℝ → ℂ :=
  fun t ↦ aux_localizedPhase ξ (y + t) *
    (aux_leftSpatialCutoff a (y + t) : ℂ)

/-- The first derivative of the left test function used in
`localizedNegativeSobolevDecay`. -/
noncomputable def aux_leftLocalizedTestDeriv (a ξ y : ℝ) : ℝ → ℂ :=
  fun t ↦ aux_localizedPhaseDeriv ξ (y + t) *
      (aux_leftSpatialCutoff a (y + t) : ℂ) +
    aux_localizedPhase ξ (y + t) *
      (aux_leftSpatialCutoffDeriv a (y + t) : ℂ)

/-- The second derivative of the left test function used in
`localizedNegativeSobolevDecay`. -/
noncomputable def aux_leftLocalizedTestDerivTwo (a ξ y : ℝ) : ℝ → ℂ :=
  fun t ↦ aux_localizedPhaseDerivTwo ξ (y + t) *
      (aux_leftSpatialCutoff a (y + t) : ℂ) +
    2 * aux_localizedPhaseDeriv ξ (y + t) *
      (aux_leftSpatialCutoffDeriv a (y + t) : ℂ) +
    aux_localizedPhase ξ (y + t) *
      (aux_leftSpatialCutoffDerivTwo a (y + t) : ℂ)

/-- Verifies the first derivative of the left test for the interval transfer
in `localizedNegativeSobolevDecay`. -/
lemma aux_leftLocalizedTest_hasDerivAt (a ξ y t : ℝ) :
    HasDerivAt (aux_leftLocalizedTest a ξ y)
      (aux_leftLocalizedTestDeriv a ξ y t) t := by
  have hp : HasDerivAt (fun z : ℝ ↦ aux_localizedPhase ξ (y + z))
      (aux_localizedPhaseDeriv ξ (y + t)) t :=
    (aux_localizedPhase_hasDerivAt ξ (y + t)).comp_const_add y t
  have hL : HasDerivAt (fun z : ℝ ↦
      (aux_leftSpatialCutoff a (y + z) : ℂ))
      (aux_leftSpatialCutoffDeriv a (y + t) : ℂ) t :=
    ((aux_leftSpatialCutoff_hasDerivAt a (y + t)).comp_const_add y t).ofReal_comp
  have h := hp.mul hL
  have hfun : aux_leftLocalizedTest a ξ y =ᶠ[𝓝 t]
      ((fun z : ℝ ↦ aux_localizedPhase ξ (y + z)) *
        fun z ↦ (aux_leftSpatialCutoff a (y + z) : ℂ)) :=
    Filter.Eventually.of_forall fun z ↦ by
      simp only [aux_leftLocalizedTest, Pi.mul_apply]
  exact h.congr_of_eventuallyEq hfun

/-- Verifies the second derivative of the left test for the interval transfer
in `localizedNegativeSobolevDecay`. -/
lemma aux_leftLocalizedTestDeriv_hasDerivAt (a ξ y t : ℝ) :
    HasDerivAt (aux_leftLocalizedTestDeriv a ξ y)
      (aux_leftLocalizedTestDerivTwo a ξ y t) t := by
  have hp : HasDerivAt (fun z : ℝ ↦ aux_localizedPhase ξ (y + z))
      (aux_localizedPhaseDeriv ξ (y + t)) t :=
    (aux_localizedPhase_hasDerivAt ξ (y + t)).comp_const_add y t
  have hp1 : HasDerivAt (fun z : ℝ ↦ aux_localizedPhaseDeriv ξ (y + z))
      (aux_localizedPhaseDerivTwo ξ (y + t)) t :=
    (aux_localizedPhaseDeriv_hasDerivAt ξ (y + t)).comp_const_add y t
  have hL : HasDerivAt (fun z : ℝ ↦
      (aux_leftSpatialCutoff a (y + z) : ℂ))
      (aux_leftSpatialCutoffDeriv a (y + t) : ℂ) t :=
    ((aux_leftSpatialCutoff_hasDerivAt a (y + t)).comp_const_add y t).ofReal_comp
  have hL1 : HasDerivAt (fun z : ℝ ↦
      (aux_leftSpatialCutoffDeriv a (y + z) : ℂ))
      (aux_leftSpatialCutoffDerivTwo a (y + t) : ℂ) t :=
    ((aux_leftSpatialCutoffDeriv_hasDerivAt a (y + t)).comp_const_add y t).ofReal_comp
  have h := (hp1.mul hL).add (hp.mul hL1)
  have hfun : aux_leftLocalizedTestDeriv a ξ y =ᶠ[𝓝 t]
      (((fun z : ℝ ↦ aux_localizedPhaseDeriv ξ (y + z)) *
          fun z ↦ (aux_leftSpatialCutoff a (y + z) : ℂ)) +
        (fun z ↦ aux_localizedPhase ξ (y + z)) *
          fun z ↦ (aux_leftSpatialCutoffDeriv a (y + z) : ℂ)) :=
    Filter.Eventually.of_forall fun z ↦ by
      simp only [aux_leftLocalizedTestDeriv, Pi.add_apply, Pi.mul_apply]
  apply (h.congr_of_eventuallyEq hfun).congr_deriv
  simp only [aux_leftLocalizedTestDerivTwo]
  ring

/-- Continuity of the left test function, used for finite-interval
integrability in `localizedNegativeSobolevDecay`. -/
lemma aux_leftLocalizedTest_continuous (a ξ y : ℝ) :
    Continuous (aux_leftLocalizedTest a ξ y) := by
  apply (aux_localizedPhase_continuous ξ).comp
    (continuous_const.add continuous_id) |>.mul
  exact Complex.continuous_ofReal.comp
    ((aux_leftSpatialCutoff_continuous a).comp
      (continuous_const.add continuous_id))

/-- Continuity of the first left-test derivative, used for finite-interval
integrability in `localizedNegativeSobolevDecay`. -/
lemma aux_leftLocalizedTestDeriv_continuous (a ξ y : ℝ) :
    Continuous (aux_leftLocalizedTestDeriv a ξ y) := by
  apply ((aux_localizedPhaseDeriv_continuous ξ).comp
    (continuous_const.add continuous_id)).mul
    (Complex.continuous_ofReal.comp
      ((aux_leftSpatialCutoff_continuous a).comp
        (continuous_const.add continuous_id))) |>.add
  exact ((aux_localizedPhase_continuous ξ).comp
    (continuous_const.add continuous_id)).mul
    (Complex.continuous_ofReal.comp
      ((aux_leftSpatialCutoffDeriv_continuous a).comp
        (continuous_const.add continuous_id)))

/-- Continuity of the second left-test derivative, used for finite-interval
integrability in `localizedNegativeSobolevDecay`. -/
lemma aux_leftLocalizedTestDerivTwo_continuous (a ξ y : ℝ) :
    Continuous (aux_leftLocalizedTestDerivTwo a ξ y) := by
  change Continuous (fun t : ℝ ↦
    aux_localizedPhaseDerivTwo ξ (y + t) *
        (aux_leftSpatialCutoff a (y + t) : ℂ) +
      2 * aux_localizedPhaseDeriv ξ (y + t) *
        (aux_leftSpatialCutoffDeriv a (y + t) : ℂ) +
      aux_localizedPhase ξ (y + t) *
        (aux_leftSpatialCutoffDerivTwo a (y + t) : ℂ))
  have hp : Continuous (fun t : ℝ ↦ aux_localizedPhase ξ (y + t)) :=
    (aux_localizedPhase_continuous ξ).comp (continuous_const.add continuous_id)
  have hp1 : Continuous (fun t : ℝ ↦ aux_localizedPhaseDeriv ξ (y + t)) :=
    (aux_localizedPhaseDeriv_continuous ξ).comp (continuous_const.add continuous_id)
  have hp2 : Continuous (fun t : ℝ ↦ aux_localizedPhaseDerivTwo ξ (y + t)) :=
    (aux_localizedPhaseDerivTwo_continuous ξ).comp (continuous_const.add continuous_id)
  have hL : Continuous (fun t : ℝ ↦ (aux_leftSpatialCutoff a (y + t) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((aux_leftSpatialCutoff_continuous a).comp (continuous_const.add continuous_id))
  have hL1 : Continuous (fun t : ℝ ↦ (aux_leftSpatialCutoffDeriv a (y + t) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((aux_leftSpatialCutoffDeriv_continuous a).comp (continuous_const.add continuous_id))
  have hL2 : Continuous (fun t : ℝ ↦ (aux_leftSpatialCutoffDerivTwo a (y + t) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((aux_leftSpatialCutoffDerivTwo_continuous a).comp (continuous_const.add continuous_id))
  exact ((hp2.mul hL).add ((continuous_const.mul hp1).mul hL1)).add (hp.mul hL2)

/-- The phase on the central constant piece of the spatial cutoff, used in
the three-piece transfer for `localizedNegativeSobolevDecay`. -/
noncomputable def aux_middleLocalizedTest (ξ y : ℝ) : ℝ → ℂ :=
  fun t ↦ aux_localizedPhase ξ (y + t)

/-- The first derivative of the central phase test used in
`localizedNegativeSobolevDecay`. -/
noncomputable def aux_middleLocalizedTestDeriv (ξ y : ℝ) : ℝ → ℂ :=
  fun t ↦ aux_localizedPhaseDeriv ξ (y + t)

/-- The second derivative of the central phase test used in
`localizedNegativeSobolevDecay`. -/
noncomputable def aux_middleLocalizedTestDerivTwo (ξ y : ℝ) : ℝ → ℂ :=
  fun t ↦ aux_localizedPhaseDerivTwo ξ (y + t)

/-- Verifies the derivative of the central phase test for the interval
transfer in `localizedNegativeSobolevDecay`. -/
lemma aux_middleLocalizedTest_hasDerivAt (ξ y t : ℝ) :
    HasDerivAt (aux_middleLocalizedTest ξ y)
      (aux_middleLocalizedTestDeriv ξ y t) t := by
  exact (aux_localizedPhase_hasDerivAt ξ (y + t)).comp_const_add y t

/-- Verifies the second derivative of the central phase test for the interval
transfer in `localizedNegativeSobolevDecay`. -/
lemma aux_middleLocalizedTestDeriv_hasDerivAt (ξ y t : ℝ) :
    HasDerivAt (aux_middleLocalizedTestDeriv ξ y)
      (aux_middleLocalizedTestDerivTwo ξ y t) t := by
  exact (aux_localizedPhaseDeriv_hasDerivAt ξ (y + t)).comp_const_add y t

/-- Continuity of the central phase test used for interval integrability in
`localizedNegativeSobolevDecay`. -/
lemma aux_middleLocalizedTest_continuous (ξ y : ℝ) :
    Continuous (aux_middleLocalizedTest ξ y) := by
  exact (aux_localizedPhase_continuous ξ).comp (continuous_const.add continuous_id)

/-- Continuity of the first central-test derivative used for interval
integrability in `localizedNegativeSobolevDecay`. -/
lemma aux_middleLocalizedTestDeriv_continuous (ξ y : ℝ) :
    Continuous (aux_middleLocalizedTestDeriv ξ y) := by
  exact (aux_localizedPhaseDeriv_continuous ξ).comp (continuous_const.add continuous_id)

/-- Continuity of the second central-test derivative used for interval
integrability in `localizedNegativeSobolevDecay`. -/
lemma aux_middleLocalizedTestDerivTwo_continuous (ξ y : ℝ) :
    Continuous (aux_middleLocalizedTestDerivTwo ξ y) := by
  exact (aux_localizedPhaseDerivTwo_continuous ξ).comp (continuous_const.add continuous_id)

/-- The phase times the right cubic transition, used as the right test
function in the twofold integration by parts for localizedNegativeSobolevDecay. -/
noncomputable def aux_rightLocalizedTest (b ξ y : ℝ) : ℝ → ℂ :=
  fun t ↦ aux_localizedPhase ξ (y + t) *
    (aux_rightSpatialCutoff b (y + t) : ℂ)

/-- The first derivative of the right test function used in
localizedNegativeSobolevDecay. -/
noncomputable def aux_rightLocalizedTestDeriv (b ξ y : ℝ) : ℝ → ℂ :=
  fun t ↦ aux_localizedPhaseDeriv ξ (y + t) *
      (aux_rightSpatialCutoff b (y + t) : ℂ) +
    aux_localizedPhase ξ (y + t) *
      (aux_rightSpatialCutoffDeriv b (y + t) : ℂ)

/-- The second derivative of the right test function used in
localizedNegativeSobolevDecay. -/
noncomputable def aux_rightLocalizedTestDerivTwo (b ξ y : ℝ) : ℝ → ℂ :=
  fun t ↦ aux_localizedPhaseDerivTwo ξ (y + t) *
      (aux_rightSpatialCutoff b (y + t) : ℂ) +
    2 * aux_localizedPhaseDeriv ξ (y + t) *
      (aux_rightSpatialCutoffDeriv b (y + t) : ℂ) +
    aux_localizedPhase ξ (y + t) *
      (aux_rightSpatialCutoffDerivTwo b (y + t) : ℂ)

/-- Verifies the first derivative of the right test for the interval transfer
in localizedNegativeSobolevDecay. -/
lemma aux_rightLocalizedTest_hasDerivAt (b ξ y t : ℝ) :
    HasDerivAt (aux_rightLocalizedTest b ξ y)
      (aux_rightLocalizedTestDeriv b ξ y t) t := by
  have hp : HasDerivAt (fun z : ℝ ↦ aux_localizedPhase ξ (y + z))
      (aux_localizedPhaseDeriv ξ (y + t)) t :=
    (aux_localizedPhase_hasDerivAt ξ (y + t)).comp_const_add y t
  have hR : HasDerivAt (fun z : ℝ ↦
      (aux_rightSpatialCutoff b (y + z) : ℂ))
      (aux_rightSpatialCutoffDeriv b (y + t) : ℂ) t :=
    ((aux_rightSpatialCutoff_hasDerivAt b (y + t)).comp_const_add y t).ofReal_comp
  have h := hp.mul hR
  have hfun : aux_rightLocalizedTest b ξ y =ᶠ[𝓝 t]
      ((fun z : ℝ ↦ aux_localizedPhase ξ (y + z)) *
        fun z ↦ (aux_rightSpatialCutoff b (y + z) : ℂ)) :=
    Filter.Eventually.of_forall fun z ↦ by
      simp only [aux_rightLocalizedTest, Pi.mul_apply]
  exact h.congr_of_eventuallyEq hfun

/-- Verifies the second derivative of the right test for the interval
transfer in localizedNegativeSobolevDecay. -/
lemma aux_rightLocalizedTestDeriv_hasDerivAt (b ξ y t : ℝ) :
    HasDerivAt (aux_rightLocalizedTestDeriv b ξ y)
      (aux_rightLocalizedTestDerivTwo b ξ y t) t := by
  have hp : HasDerivAt (fun z : ℝ ↦ aux_localizedPhase ξ (y + z))
      (aux_localizedPhaseDeriv ξ (y + t)) t :=
    (aux_localizedPhase_hasDerivAt ξ (y + t)).comp_const_add y t
  have hp1 : HasDerivAt (fun z : ℝ ↦ aux_localizedPhaseDeriv ξ (y + z))
      (aux_localizedPhaseDerivTwo ξ (y + t)) t :=
    (aux_localizedPhaseDeriv_hasDerivAt ξ (y + t)).comp_const_add y t
  have hR : HasDerivAt (fun z : ℝ ↦
      (aux_rightSpatialCutoff b (y + z) : ℂ))
      (aux_rightSpatialCutoffDeriv b (y + t) : ℂ) t :=
    ((aux_rightSpatialCutoff_hasDerivAt b (y + t)).comp_const_add y t).ofReal_comp
  have hR1 : HasDerivAt (fun z : ℝ ↦
      (aux_rightSpatialCutoffDeriv b (y + z) : ℂ))
      (aux_rightSpatialCutoffDerivTwo b (y + t) : ℂ) t :=
    ((aux_rightSpatialCutoffDeriv_hasDerivAt b (y + t)).comp_const_add y t).ofReal_comp
  have h := (hp1.mul hR).add (hp.mul hR1)
  have hfun : aux_rightLocalizedTestDeriv b ξ y =ᶠ[𝓝 t]
      (((fun z : ℝ ↦ aux_localizedPhaseDeriv ξ (y + z)) *
          fun z ↦ (aux_rightSpatialCutoff b (y + z) : ℂ)) +
        (fun z ↦ aux_localizedPhase ξ (y + z)) *
          fun z ↦ (aux_rightSpatialCutoffDeriv b (y + z) : ℂ)) :=
    Filter.Eventually.of_forall fun z ↦ by
      simp only [aux_rightLocalizedTestDeriv, Pi.add_apply, Pi.mul_apply]
  apply (h.congr_of_eventuallyEq hfun).congr_deriv
  simp only [aux_rightLocalizedTestDerivTwo]
  ring

/-- Continuity of the right test function, used for finite-interval
integrability in localizedNegativeSobolevDecay. -/
lemma aux_rightLocalizedTest_continuous (b ξ y : ℝ) :
    Continuous (aux_rightLocalizedTest b ξ y) := by
  apply (aux_localizedPhase_continuous ξ).comp
    (continuous_const.add continuous_id) |>.mul
  exact Complex.continuous_ofReal.comp
    ((aux_rightSpatialCutoff_continuous b).comp
      (continuous_const.add continuous_id))

/-- Continuity of the first right-test derivative, used for finite-interval
integrability in localizedNegativeSobolevDecay. -/
lemma aux_rightLocalizedTestDeriv_continuous (b ξ y : ℝ) :
    Continuous (aux_rightLocalizedTestDeriv b ξ y) := by
  apply ((aux_localizedPhaseDeriv_continuous ξ).comp
    (continuous_const.add continuous_id)).mul
    (Complex.continuous_ofReal.comp
      ((aux_rightSpatialCutoff_continuous b).comp
        (continuous_const.add continuous_id))) |>.add
  exact ((aux_localizedPhase_continuous ξ).comp
    (continuous_const.add continuous_id)).mul
    (Complex.continuous_ofReal.comp
      ((aux_rightSpatialCutoffDeriv_continuous b).comp
        (continuous_const.add continuous_id)))

/-- Continuity of the second right-test derivative, used for finite-interval
integrability in localizedNegativeSobolevDecay. -/
lemma aux_rightLocalizedTestDerivTwo_continuous (b ξ y : ℝ) :
    Continuous (aux_rightLocalizedTestDerivTwo b ξ y) := by
  change Continuous (fun t : ℝ ↦
    aux_localizedPhaseDerivTwo ξ (y + t) *
        (aux_rightSpatialCutoff b (y + t) : ℂ) +
      2 * aux_localizedPhaseDeriv ξ (y + t) *
        (aux_rightSpatialCutoffDeriv b (y + t) : ℂ) +
      aux_localizedPhase ξ (y + t) *
        (aux_rightSpatialCutoffDerivTwo b (y + t) : ℂ))
  have hp : Continuous (fun t : ℝ ↦ aux_localizedPhase ξ (y + t)) :=
    (aux_localizedPhase_continuous ξ).comp (continuous_const.add continuous_id)
  have hp1 : Continuous (fun t : ℝ ↦ aux_localizedPhaseDeriv ξ (y + t)) :=
    (aux_localizedPhaseDeriv_continuous ξ).comp (continuous_const.add continuous_id)
  have hp2 : Continuous (fun t : ℝ ↦ aux_localizedPhaseDerivTwo ξ (y + t)) :=
    (aux_localizedPhaseDerivTwo_continuous ξ).comp (continuous_const.add continuous_id)
  have hR : Continuous (fun t : ℝ ↦ (aux_rightSpatialCutoff b (y + t) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((aux_rightSpatialCutoff_continuous b).comp (continuous_const.add continuous_id))
  have hR1 : Continuous (fun t : ℝ ↦ (aux_rightSpatialCutoffDeriv b (y + t) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((aux_rightSpatialCutoffDeriv_continuous b).comp (continuous_const.add continuous_id))
  have hR2 : Continuous (fun t : ℝ ↦ (aux_rightSpatialCutoffDerivTwo b (y + t) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((aux_rightSpatialCutoffDerivTwo_continuous b).comp (continuous_const.add continuous_id))
  exact ((hp2.mul hR).add ((continuous_const.mul hp1).mul hR1)).add (hp.mul hR2)

/-- The outer left endpoint vanishes, eliminating a boundary term in the
three-piece transfer for localizedNegativeSobolevDecay. -/
lemma aux_leftLocalizedTest_outer (a ξ y : ℝ) :
    aux_leftLocalizedTest a ξ y (a - 1 - y) = 0 := by
  have harg : y + (a - 1 - y) = a - 1 := by ring
  rw [aux_leftLocalizedTest, harg]
  simp only [aux_leftSpatialCutoff]
  ring
  norm_num

/-- The first derivative vanishes at the outer left endpoint, eliminating its
boundary term in localizedNegativeSobolevDecay. -/
lemma aux_leftLocalizedTestDeriv_outer (a ξ y : ℝ) :
    aux_leftLocalizedTestDeriv a ξ y (a - 1 - y) = 0 := by
  have harg : y + (a - 1 - y) = a - 1 := by ring
  rw [aux_leftLocalizedTestDeriv, harg]
  simp only [aux_leftSpatialCutoff, aux_leftSpatialCutoffDeriv]
  ring
  norm_num

/-- The left transition and central test agree at their common endpoint in
the transfer for localizedNegativeSobolevDecay. -/
lemma aux_leftLocalizedTest_inner (a ξ y : ℝ) :
    aux_leftLocalizedTest a ξ y (a - y) = aux_localizedPhase ξ a := by
  have harg : y + (a - y) = a := by ring
  rw [aux_leftLocalizedTest, harg]
  simp only [aux_leftSpatialCutoff]
  ring
  norm_num

/-- The first derivatives of the left transition and central test agree at
their common endpoint in localizedNegativeSobolevDecay. -/
lemma aux_leftLocalizedTestDeriv_inner (a ξ y : ℝ) :
    aux_leftLocalizedTestDeriv a ξ y (a - y) = aux_localizedPhaseDeriv ξ a := by
  have harg : y + (a - y) = a := by ring
  rw [aux_leftLocalizedTestDeriv, harg]
  simp only [aux_leftSpatialCutoff, aux_leftSpatialCutoffDeriv]
  ring
  norm_num

/-- The central test takes the phase value at the left joining point in
localizedNegativeSobolevDecay. -/
lemma aux_middleLocalizedTest_left (a ξ y : ℝ) :
    aux_middleLocalizedTest ξ y (a - y) = aux_localizedPhase ξ a := by
  have harg : y + (a - y) = a := by ring
  simp only [aux_middleLocalizedTest, harg]

/-- The central-test derivative takes the phase derivative at the left
joining point in localizedNegativeSobolevDecay. -/
lemma aux_middleLocalizedTestDeriv_left (a ξ y : ℝ) :
    aux_middleLocalizedTestDeriv ξ y (a - y) = aux_localizedPhaseDeriv ξ a := by
  have harg : y + (a - y) = a := by ring
  simp only [aux_middleLocalizedTestDeriv, harg]

/-- The central test takes the phase value at the right joining point in
localizedNegativeSobolevDecay. -/
lemma aux_middleLocalizedTest_right (b ξ y : ℝ) :
    aux_middleLocalizedTest ξ y (b - y) = aux_localizedPhase ξ b := by
  have harg : y + (b - y) = b := by ring
  simp only [aux_middleLocalizedTest, harg]

/-- The central-test derivative takes the phase derivative at the right
joining point in localizedNegativeSobolevDecay. -/
lemma aux_middleLocalizedTestDeriv_right (b ξ y : ℝ) :
    aux_middleLocalizedTestDeriv ξ y (b - y) = aux_localizedPhaseDeriv ξ b := by
  have harg : y + (b - y) = b := by ring
  simp only [aux_middleLocalizedTestDeriv, harg]

/-- The central and right transition tests agree at their common endpoint in
the transfer for localizedNegativeSobolevDecay. -/
lemma aux_rightLocalizedTest_inner (b ξ y : ℝ) :
    aux_rightLocalizedTest b ξ y (b - y) = aux_localizedPhase ξ b := by
  have harg : y + (b - y) = b := by ring
  rw [aux_rightLocalizedTest, harg]
  simp only [aux_rightSpatialCutoff]
  ring
  norm_num

/-- The first derivatives of the central and right transition tests agree at
their common endpoint in localizedNegativeSobolevDecay. -/
lemma aux_rightLocalizedTestDeriv_inner (b ξ y : ℝ) :
    aux_rightLocalizedTestDeriv b ξ y (b - y) = aux_localizedPhaseDeriv ξ b := by
  have harg : y + (b - y) = b := by ring
  rw [aux_rightLocalizedTestDeriv, harg]
  simp only [aux_rightSpatialCutoff, aux_rightSpatialCutoffDeriv]
  ring
  norm_num

/-- The outer right endpoint vanishes, eliminating a boundary term in the
three-piece transfer for localizedNegativeSobolevDecay. -/
lemma aux_rightLocalizedTest_outer (b ξ y : ℝ) :
    aux_rightLocalizedTest b ξ y (b + 1 - y) = 0 := by
  have harg : y + (b + 1 - y) = b + 1 := by ring
  rw [aux_rightLocalizedTest, harg]
  simp only [aux_rightSpatialCutoff]
  ring
  norm_num

/-- The first derivative vanishes at the outer right endpoint, eliminating
its boundary term in localizedNegativeSobolevDecay. -/
lemma aux_rightLocalizedTestDeriv_outer (b ξ y : ℝ) :
    aux_rightLocalizedTestDeriv b ξ y (b + 1 - y) = 0 := by
  have harg : y + (b + 1 - y) = b + 1 := by ring
  rw [aux_rightLocalizedTestDeriv, harg]
  simp only [aux_rightSpatialCutoff, aux_rightSpatialCutoffDeriv]
  ring
  norm_num

/-- Summing the three interval transfers cancels every endpoint term and
leaves the reciprocal kernel against the piecewise second test derivative.
This is the integration-by-parts core of localizedNegativeSobolevDecay. -/
lemma aux_threePiece_dyadicKernel_transfer
    (a b : ℝ) (_hab : a ≤ b) (k : ℕ) (ξ y : ℝ) :
    (∫ t in (a - 1 - y)..(a - y),
      aux_scaledInverseFourierKernel (fun z ↦ (annularCutoff z : ℂ)) k t *
        aux_leftLocalizedTest a ξ y t) +
      (∫ t in (a - y)..(b - y),
        aux_scaledInverseFourierKernel (fun z ↦ (annularCutoff z : ℂ)) k t *
          aux_middleLocalizedTest ξ y t) +
      (∫ t in (b - y)..(b + 1 - y),
        aux_scaledInverseFourierKernel (fun z ↦ (annularCutoff z : ℂ)) k t *
          aux_rightLocalizedTest b ξ y t) =
      (∫ t in (a - 1 - y)..(a - y),
        aux_normalizedScaledReciprocalKernel k t *
          aux_leftLocalizedTestDerivTwo a ξ y t) +
      (∫ t in (a - y)..(b - y),
        aux_normalizedScaledReciprocalKernel k t *
          aux_middleLocalizedTestDerivTwo ξ y t) +
      (∫ t in (b - y)..(b + 1 - y),
        aux_normalizedScaledReciprocalKernel k t *
          aux_rightLocalizedTestDerivTwo b ξ y t) := by
  have hleft := aux_interval_dyadicKernel_transfer
    (r := a - 1 - y) (s := a - y) k
    (aux_leftLocalizedTest_continuous a ξ y).continuousOn
    (aux_leftLocalizedTestDeriv_continuous a ξ y).continuousOn
    (fun t _ ↦ aux_leftLocalizedTest_hasDerivAt a ξ y t)
    (fun t _ ↦ aux_leftLocalizedTestDeriv_hasDerivAt a ξ y t)
    ((aux_leftLocalizedTestDeriv_continuous a ξ y).intervalIntegrable _ _)
    ((aux_leftLocalizedTestDerivTwo_continuous a ξ y).intervalIntegrable _ _)
  have hmiddle := aux_interval_dyadicKernel_transfer
    (r := a - y) (s := b - y) k
    (aux_middleLocalizedTest_continuous ξ y).continuousOn
    (aux_middleLocalizedTestDeriv_continuous ξ y).continuousOn
    (fun t _ ↦ aux_middleLocalizedTest_hasDerivAt ξ y t)
    (fun t _ ↦ aux_middleLocalizedTestDeriv_hasDerivAt ξ y t)
    ((aux_middleLocalizedTestDeriv_continuous ξ y).intervalIntegrable _ _)
    ((aux_middleLocalizedTestDerivTwo_continuous ξ y).intervalIntegrable _ _)
  have hright := aux_interval_dyadicKernel_transfer
    (r := b - y) (s := b + 1 - y) k
    (aux_rightLocalizedTest_continuous b ξ y).continuousOn
    (aux_rightLocalizedTestDeriv_continuous b ξ y).continuousOn
    (fun t _ ↦ aux_rightLocalizedTest_hasDerivAt b ξ y t)
    (fun t _ ↦ aux_rightLocalizedTestDeriv_hasDerivAt b ξ y t)
    ((aux_rightLocalizedTestDeriv_continuous b ξ y).intervalIntegrable _ _)
    ((aux_rightLocalizedTestDerivTwo_continuous b ξ y).intervalIntegrable _ _)
  rw [hleft, hmiddle, hright,
    aux_leftLocalizedTest_outer, aux_leftLocalizedTestDeriv_outer,
    aux_leftLocalizedTest_inner, aux_leftLocalizedTestDeriv_inner,
    aux_middleLocalizedTest_left, aux_middleLocalizedTestDeriv_left,
    aux_middleLocalizedTest_right, aux_middleLocalizedTestDeriv_right,
    aux_rightLocalizedTest_inner, aux_rightLocalizedTestDeriv_inner,
    aux_rightLocalizedTest_outer, aux_rightLocalizedTestDeriv_outer]
  ring

/--
An interval integral with the shifted test arising from the shear identity
equals a whole-line integral against the correspondingly interval-supported
test function.  This identifies the three transferred pieces in
`localizedNegativeSobolevDecay` as translated convolutions.
-/
lemma aux_intervalIntegral_eq_indicator_add
    (r s y : ℝ) (hrs : r ≤ s) (κ D : ℝ → ℂ) :
    (∫ t in (r - y)..(s - y), κ t * D (y + t)) =
      ∫ t : ℝ, κ t * (Set.Ioc r s).indicator D (y + t) := by
  rw [intervalIntegral.integral_of_le (sub_le_sub_right hrs y)]
  calc
    (∫ t : ℝ in Set.Ioc (r - y) (s - y), κ t * D (y + t)) =
        ∫ t : ℝ, (Set.Ioc (r - y) (s - y)).indicator
          (fun t ↦ κ t * D (y + t)) t :=
      (integral_indicator measurableSet_Ioc).symm
    _ = ∫ t : ℝ, κ t * (Set.Ioc r s).indicator D (y + t) := by
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t ∈ Set.Ioc (r - y) (s - y)
      · have ht' : y + t ∈ Set.Ioc r s := by
          constructor <;> linarith [ht.1, ht.2]
        simp [ht, ht']
      · have ht' : y + t ∉ Set.Ioc r s := by
          intro hmem
          apply ht
          constructor <;> linarith [hmem.1, hmem.2]
        simp [ht, ht']

/--
An interval-supported function whose pointwise norm is bounded by `B` has
the corresponding `L¹` bound.  It controls the three second-test pieces in
`localizedNegativeSobolevDecay`.
-/
lemma aux_eLpNorm_indicator_Ioc_le_one
    (u v B : ℝ) (hB : 0 ≤ B) (f : ℝ → ℂ)
    (hbound : ∀ x ∈ Set.Ioc u v, ‖f x‖ ≤ B) :
    eLpNorm ((Set.Ioc u v).indicator f) (1 : ℝ≥0∞) volume ≤
      ENNReal.ofReal (B * (v - u)) := by
  calc
    eLpNorm ((Set.Ioc u v).indicator f) (1 : ℝ≥0∞) volume ≤
        ENNReal.ofReal B *
          eLpNorm ((Set.Ioc u v).indicator (fun _ : ℝ ↦ (1 : ℂ)))
            (1 : ℝ≥0∞) volume := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      filter_upwards with x
      by_cases hx : x ∈ Set.Ioc u v
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, norm_one]
        simpa using hbound x hx
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, norm_zero]
        positivity
    _ = ENNReal.ofReal B * ENNReal.ofReal (v - u) := by
      rw [eLpNorm_indicator_const measurableSet_Ioc (by norm_num) (by norm_num),
        Real.volume_Ioc]
      norm_num
    _ = ENNReal.ofReal (B * (v - u)) := by
      rw [ENNReal.ofReal_mul hB]

/--
A continuous function restricted to a finite interval is in `L¹`.  This
supplies the membership hypotheses for the three interval-supported tests
in `localizedNegativeSobolevDecay`.
-/
lemma aux_memLp_indicator_Ioc_one_of_continuous
    (u v : ℝ) (f : ℝ → ℂ) (hf : Continuous f)
    (B : ℝ) (hbound : ∀ x ∈ Set.Ioc u v, ‖f x‖ ≤ B) :
    MemLp ((Set.Ioc u v).indicator f) (1 : ℝ≥0∞) volume := by
  have hmeas : AEStronglyMeasurable ((Set.Ioc u v).indicator f) volume :=
    hf.aestronglyMeasurable.indicator measurableSet_Ioc
  have hsupp : ∀ᵐ x : ℝ ∂volume,
      x ∉ Set.Ioc u v → (Set.Ioc u v).indicator f x = 0 := by
    filter_upwards with x
    intro hx
    simp [hx]
  have hbounded : ∀ᵐ x : ℝ ∂volume,
      ‖(Set.Ioc u v).indicator f x‖ ≤ max B 0 := by
    filter_upwards with x
    by_cases hx : x ∈ Set.Ioc u v
    · rw [Set.indicator_of_mem hx]
      exact (hbound x hx).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact le_max_right _ _
  exact aux_memLp_of_ae_bound_of_ae_support _ hmeas (max B 0) hbounded
    (Set.Ioc u v) measurableSet_Ioc measure_Ioc_lt_top hsupp 1

/--
A uniformly bounded function supported on a finite interval has the sharp
interval-length `L¹` bound.  This is used for the combined second test in
`localizedNegativeSobolevDecay`.
-/
lemma aux_eLpNorm_le_one_of_bound_support_Ioc
    (u v B : ℝ) (hB : 0 ≤ B) (f : ℝ → ℂ)
    (hbound : ∀ x ∈ Set.Ioc u v, ‖f x‖ ≤ B)
    (hsupp : ∀ x : ℝ, x ∉ Set.Ioc u v → f x = 0) :
    eLpNorm f (1 : ℝ≥0∞) volume ≤ ENNReal.ofReal (B * (v - u)) := by
  calc
    eLpNorm f (1 : ℝ≥0∞) volume ≤
        ENNReal.ofReal B *
          eLpNorm ((Set.Ioc u v).indicator (fun _ : ℝ ↦ (1 : ℂ)))
            (1 : ℝ≥0∞) volume := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      filter_upwards with x
      by_cases hx : x ∈ Set.Ioc u v
      · rw [Set.indicator_of_mem hx, norm_one]
        simpa using hbound x hx
      · rw [Set.indicator_of_notMem hx, norm_zero, hsupp x hx, norm_zero]
        positivity
    _ = ENNReal.ofReal B * ENNReal.ofReal (v - u) := by
      rw [eLpNorm_indicator_const measurableSet_Ioc (by norm_num) (by norm_num),
        Real.volume_Ioc]
      norm_num
    _ = ENNReal.ofReal (B * (v - u)) := by
      rw [ENNReal.ofReal_mul hB]

/--
The bounded-support hypothesis used for the `L¹` norm estimate also gives
the `L¹` membership required by Young's inequality in
`localizedNegativeSobolevDecay`.
-/
lemma aux_memLp_one_of_bound_support_Ioc
    (u v B : ℝ) (hB : 0 ≤ B) (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f volume)
    (hbound : ∀ x ∈ Set.Ioc u v, ‖f x‖ ≤ B)
    (hsupp : ∀ x : ℝ, x ∉ Set.Ioc u v → f x = 0) :
    MemLp f (1 : ℝ≥0∞) volume := by
  have hboundAE : ∀ᵐ x : ℝ ∂volume, ‖f x‖ ≤ B := by
    filter_upwards with x
    by_cases hx : x ∈ Set.Ioc u v
    · exact hbound x hx
    · rw [hsupp x hx, norm_zero]
      exact hB
  have hsuppAE : ∀ᵐ x : ℝ ∂volume, x ∉ Set.Ioc u v → f x = 0 := by
    filter_upwards with x
    exact hsupp x
  exact aux_memLp_of_ae_bound_of_ae_support f hf B hboundAE
    (Set.Ioc u v) measurableSet_Ioc measure_Ioc_lt_top hsuppAE 1

/--
An integrable kernel times a uniformly bounded translated test is
integrable.  This justifies the finite additivity of the three transferred
integrals in `localizedNegativeSobolevDecay`.
-/
lemma aux_integrable_kernel_mul_translated_of_bound
    (κ F : ℝ → ℂ) (hκ : Integrable κ volume)
    (hF : AEStronglyMeasurable F volume) (B : ℝ)
    (hbound : ∀ x : ℝ, ‖F x‖ ≤ B) (y : ℝ) :
    Integrable (fun t : ℝ ↦ κ t * F (y + t)) volume := by
  have hshift : AEStronglyMeasurable (fun t : ℝ ↦ F (y + t)) volume := by
    simpa only [Function.comp_def] using hF.comp_quasiMeasurePreserving
      (measurePreserving_add_left volume y).quasiMeasurePreserving
  have h := hκ.bdd_mul hshift
    (Filter.Eventually.of_forall fun t ↦ hbound (y + t))
  simpa [mul_comm] using h

/--
The three translated convolutions associated with adjacent cutoff pieces
combine into the convolution against their sum.  The boundedness hypotheses
justify the two applications of integral additivity in
`localizedNegativeSobolevDecay`.
-/
lemma aux_addConvolution_three_eq_addConvolution_sum
    (κ f₁ f₂ f₃ : ℝ → ℂ) (y : ℝ) (hκ : Integrable κ volume)
    (hf₁ : AEStronglyMeasurable f₁ volume) (B₁ : ℝ)
    (hB₁ : ∀ x : ℝ, ‖f₁ x‖ ≤ B₁)
    (hf₂ : AEStronglyMeasurable f₂ volume) (B₂ : ℝ)
    (hB₂ : ∀ x : ℝ, ‖f₂ x‖ ≤ B₂)
    (hf₃ : AEStronglyMeasurable f₃ volume) (B₃ : ℝ)
    (hB₃ : ∀ x : ℝ, ‖f₃ x‖ ≤ B₃) :
    (∫ t : ℝ, κ t * f₁ (y + t)) +
        (∫ t : ℝ, κ t * f₂ (y + t)) +
        (∫ t : ℝ, κ t * f₃ (y + t)) =
      ∫ t : ℝ, κ t * ((f₁ + f₂ + f₃) (y + t)) := by
  have h₁ : Integrable (fun t : ℝ ↦ κ t * f₁ (y + t)) volume :=
    aux_integrable_kernel_mul_translated_of_bound κ f₁ hκ hf₁ B₁ hB₁ y
  have h₂ : Integrable (fun t : ℝ ↦ κ t * f₂ (y + t)) volume :=
    aux_integrable_kernel_mul_translated_of_bound κ f₂ hκ hf₂ B₂ hB₂ y
  have h₃ : Integrable (fun t : ℝ ↦ κ t * f₃ (y + t)) volume :=
    aux_integrable_kernel_mul_translated_of_bound κ f₃ hκ hf₃ B₃ hB₃ y
  have h₁₂ : Integrable (fun t : ℝ ↦
      κ t * f₁ (y + t) + κ t * f₂ (y + t)) volume :=
    h₁.add h₂
  calc
    (∫ t : ℝ, κ t * f₁ (y + t)) +
        (∫ t : ℝ, κ t * f₂ (y + t)) +
        (∫ t : ℝ, κ t * f₃ (y + t)) =
        (∫ t : ℝ, κ t * f₁ (y + t) + κ t * f₂ (y + t)) +
          (∫ t : ℝ, κ t * f₃ (y + t)) := by
      rw [integral_add h₁ h₂]
    _ = ∫ t : ℝ,
        (κ t * f₁ (y + t) + κ t * f₂ (y + t)) +
          κ t * f₃ (y + t) := by
      exact (integral_add h₁₂ h₃).symm
    _ = ∫ t : ℝ, κ t * ((f₁ + f₂ + f₃) (y + t)) := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [Pi.add_apply]
      ring

/--
The translated convolution form produced by the shear identity is the raw
convolution against the reflected kernel.  This lets
`localizedNegativeSobolevDecay` use the project's `L¹` convolution estimate.
-/
lemma aux_addConvolution_eq_reflected_aux_convolution
    (κ f : ℝ → ℂ) (y : ℝ) :
    (∫ t : ℝ, κ t * f (y + t)) =
      aux_convolution (fun t : ℝ ↦ κ (-t)) f y := by
  let H : ℝ → ℂ := fun t ↦ κ (-t) * f (y - t)
  have h := (Measure.measurePreserving_neg volume).integral_comp
    measurableEmbedding_neg H
  change (∫ t : ℝ, κ t * f (y + t)) =
    ∫ t : ℝ, κ (-t) * f (y - t)
  simpa [H] using h

/-- Reflection preserves the `L¹` norm needed for the kernel estimate in
`localizedNegativeSobolevDecay`. -/
lemma aux_eLpNorm_reflect_one (κ : ℝ → ℂ)
    (hκ : AEStronglyMeasurable κ volume) :
    eLpNorm (fun t : ℝ ↦ κ (-t)) (1 : ℝ≥0∞) volume =
      eLpNorm κ (1 : ℝ≥0∞) volume := by
  change eLpNorm (κ ∘ Neg.neg) 1 volume = eLpNorm κ 1 volume
  exact eLpNorm_comp_measurePreserving hκ (Measure.measurePreserving_neg volume)

/-- Reflection preserves `L¹` membership, as used when applying Young's
inequality to the post-shear translated convolution in
`localizedNegativeSobolevDecay`. -/
lemma aux_memLp_reflect_one (κ : ℝ → ℂ)
    (hκ : MemLp κ (1 : ℝ≥0∞) volume) :
    MemLp (fun t : ℝ ↦ κ (-t)) (1 : ℝ≥0∞) volume := by
  refine ⟨?_, ?_⟩
  · exact hκ.1.comp_quasiMeasurePreserving
      (Measure.measurePreserving_neg volume).quasiMeasurePreserving
  · rw [aux_eLpNorm_reflect_one κ hκ.1]
    exact hκ.2

/-- Young's inequality for the translated `y + t` convolution form arising
after the twofold integration by parts in `localizedNegativeSobolevDecay`. -/
lemma aux_eLpNorm_addConvolution_le_one
    (κ f : ℝ → ℂ) (hκ : MemLp κ (1 : ℝ≥0∞) volume)
    (hf : MemLp f (1 : ℝ≥0∞) volume) :
    eLpNorm (fun y : ℝ ↦ ∫ t : ℝ, κ t * f (y + t))
      (1 : ℝ≥0∞) volume ≤
      eLpNorm κ (1 : ℝ≥0∞) volume * eLpNorm f (1 : ℝ≥0∞) volume := by
  letI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hreflect : MemLp (fun t : ℝ ↦ κ (-t)) (1 : ℝ≥0∞) volume :=
    aux_memLp_reflect_one κ hκ
  calc
    eLpNorm (fun y : ℝ ↦ ∫ t : ℝ, κ t * f (y + t))
        (1 : ℝ≥0∞) volume =
        eLpNorm (aux_convolution (fun t : ℝ ↦ κ (-t)) f)
          (1 : ℝ≥0∞) volume := by
      congr with y
      exact aux_addConvolution_eq_reflected_aux_convolution κ f y
    _ ≤ eLpNorm (fun t : ℝ ↦ κ (-t)) (1 : ℝ≥0∞) volume *
          eLpNorm f (1 : ℝ≥0∞) volume :=
      aux_eLpNorm_aux_convolution_le_of_memLp_one
        (fun t : ℝ ↦ κ (-t)) f hreflect hf
    _ = eLpNorm κ (1 : ℝ≥0∞) volume * eLpNorm f (1 : ℝ≥0∞) volume := by
      rw [aux_eLpNorm_reflect_one κ hκ.1]

/--
The translated convolution form occurring after the three-piece transfer is
itself in `L¹` whenever both factors are in `L¹`.  This supplies the pairing
membership hypothesis in `localizedNegativeSobolevDecay`.
-/
lemma aux_memLp_addConvolution_one
    (κ f : ℝ → ℂ) (hκ : MemLp κ (1 : ℝ≥0∞) volume)
    (hf : MemLp f (1 : ℝ≥0∞) volume) :
    MemLp (fun y : ℝ ↦ ∫ t : ℝ, κ t * f (y + t))
      (1 : ℝ≥0∞) volume := by
  letI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hreflect : MemLp (fun t : ℝ ↦ κ (-t)) (1 : ℝ≥0∞) volume :=
    aux_memLp_reflect_one κ hκ
  have hraw : MemLp (aux_convolution (fun t : ℝ ↦ κ (-t)) f)
      (1 : ℝ≥0∞) volume :=
    aux_convolution_memLp_of_memLp_one _ _
      (memLp_one_iff_integrable.mp hreflect) hf
  have heq : (fun y : ℝ ↦ ∫ t : ℝ, κ t * f (y + t)) =
      aux_convolution (fun t : ℝ ↦ κ (-t)) f := by
    funext y
    exact aux_addConvolution_eq_reflected_aux_convolution κ f y
  rw [heq]
  exact hraw

/-- The Fourier phase appearing in the localized low-frequency estimate has
unit norm. -/
lemma aux_localizedPhase_norm (ξ x : ℝ) :
    ‖aux_localizedPhase ξ x‖ = 1 := by
  rw [aux_localizedPhase]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The first derivative of the localized Fourier phase has its elementary
frequency-size norm. -/
lemma aux_localizedPhaseDeriv_norm (ξ x : ℝ) :
    ‖aux_localizedPhaseDeriv ξ x‖ = 2 * Real.pi * |ξ| := by
  rw [aux_localizedPhaseDeriv, norm_mul, aux_localizedPhase_norm, mul_one]
  norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- The second derivative of the localized Fourier phase has quadratic
frequency size. -/
lemma aux_localizedPhaseDerivTwo_norm (ξ x : ℝ) :
    ‖aux_localizedPhaseDerivTwo ξ x‖ = (2 * Real.pi * |ξ|) ^ 2 := by
  rw [aux_localizedPhaseDerivTwo, norm_mul, aux_localizedPhase_norm, mul_one,
    norm_pow, norm_mul]
  norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- Bounds for the left cubic transition and its first two derivatives on
its transition interval. -/
lemma aux_leftSpatialCutoff_bounds (a x : ℝ)
    (hx : x ∈ Set.Icc (a - 1) a) :
    ‖(aux_leftSpatialCutoff a x : ℂ)‖ ≤ 1 ∧
      ‖(aux_leftSpatialCutoffDeriv a x : ℂ)‖ ≤ 2 ∧
      ‖(aux_leftSpatialCutoffDerivTwo a x : ℂ)‖ ≤ 6 := by
  let u : ℝ := x - a + 1
  have hu0 : 0 ≤ u := by dsimp [u]; linarith [hx.1]
  have hu1 : u ≤ 1 := by dsimp [u]; linarith [hx.2]
  have hL0 : 0 ≤ 3 * u ^ 2 - 2 * u ^ 3 := by
    have : 0 ≤ u ^ 2 * (3 - 2 * u) :=
      mul_nonneg (sq_nonneg u) (by linarith)
    nlinarith
  have hL1 : 3 * u ^ 2 - 2 * u ^ 3 ≤ 1 := by
    have : 0 ≤ (1 - u) ^ 2 * (1 + 2 * u) :=
      mul_nonneg (sq_nonneg (1 - u)) (by linarith)
    nlinarith
  have hD0 : 0 ≤ 6 * u - 6 * u ^ 2 := by
    have : 0 ≤ 6 * u * (1 - u) :=
      mul_nonneg (mul_nonneg (by norm_num) hu0) (by linarith)
    nlinarith
  have hD1 : 6 * u - 6 * u ^ 2 ≤ 2 := by
    nlinarith [sq_nonneg (u - 1 / 2)]
  have hE : |6 - 12 * u| ≤ 6 := by
    rw [abs_le]
    constructor <;> linarith
  constructor
  · rw [Complex.norm_real, Real.norm_eq_abs, aux_leftSpatialCutoff]
    change |3 * u ^ 2 - 2 * u ^ 3| ≤ 1
    rw [abs_of_nonneg hL0]
    exact hL1
  constructor
  · rw [Complex.norm_real, Real.norm_eq_abs, aux_leftSpatialCutoffDeriv]
    change |6 * u - 6 * u ^ 2| ≤ 2
    rw [abs_of_nonneg hD0]
    exact hD1
  · rw [Complex.norm_real, Real.norm_eq_abs, aux_leftSpatialCutoffDerivTwo]
    change |6 - 12 * u| ≤ 6
    exact hE

/-- Bounds for the right cubic transition and its first two derivatives on
its transition interval. -/
lemma aux_rightSpatialCutoff_bounds (b x : ℝ)
    (hx : x ∈ Set.Icc b (b + 1)) :
    ‖(aux_rightSpatialCutoff b x : ℂ)‖ ≤ 1 ∧
      ‖(aux_rightSpatialCutoffDeriv b x : ℂ)‖ ≤ 2 ∧
      ‖(aux_rightSpatialCutoffDerivTwo b x : ℂ)‖ ≤ 6 := by
  let u : ℝ := b + 1 - x
  have hu0 : 0 ≤ u := by dsimp [u]; linarith [hx.2]
  have hu1 : u ≤ 1 := by dsimp [u]; linarith [hx.1]
  have hL0 : 0 ≤ 3 * u ^ 2 - 2 * u ^ 3 := by
    have : 0 ≤ u ^ 2 * (3 - 2 * u) :=
      mul_nonneg (sq_nonneg u) (by linarith)
    nlinarith
  have hL1 : 3 * u ^ 2 - 2 * u ^ 3 ≤ 1 := by
    have : 0 ≤ (1 - u) ^ 2 * (1 + 2 * u) :=
      mul_nonneg (sq_nonneg (1 - u)) (by linarith)
    nlinarith
  have hD0 : -6 * u + 6 * u ^ 2 ≤ 0 := by
    have : 0 ≤ 6 * u * (1 - u) :=
      mul_nonneg (mul_nonneg (by norm_num) hu0) (by linarith)
    nlinarith
  have hD1 : -2 ≤ -6 * u + 6 * u ^ 2 := by
    nlinarith [sq_nonneg (u - 1 / 2)]
  have hE : |6 - 12 * u| ≤ 6 := by
    rw [abs_le]
    constructor <;> linarith
  constructor
  · rw [Complex.norm_real, Real.norm_eq_abs, aux_rightSpatialCutoff]
    change |3 * u ^ 2 - 2 * u ^ 3| ≤ 1
    rw [abs_of_nonneg hL0]
    exact hL1
  constructor
  · rw [Complex.norm_real, Real.norm_eq_abs, aux_rightSpatialCutoffDeriv]
    change |-6 * u + 6 * u ^ 2| ≤ 2
    rw [abs_le]
    constructor <;> linarith
  · rw [Complex.norm_real, Real.norm_eq_abs, aux_rightSpatialCutoffDerivTwo]
    change |6 - 12 * u| ≤ 6
    exact hE

/-- On the low-frequency interval, the first phase derivative is bounded by
eight times the frequency radius. -/
lemma aux_localizedPhaseDeriv_le (ξ x R : ℝ)
    (hξ : |ξ| ≤ R) :
    ‖aux_localizedPhaseDeriv ξ x‖ ≤ 8 * R := by
  rw [aux_localizedPhaseDeriv_norm]
  calc
    2 * Real.pi * |ξ| ≤ 2 * 4 * R := by
      gcongr
      exact Real.pi_le_four
    _ = 8 * R := by ring

/-- On the low-frequency interval, the second phase derivative is bounded
by sixty-four times the squared frequency radius. -/
lemma aux_localizedPhaseDerivTwo_le (ξ x R : ℝ)
    (hξ : |ξ| ≤ R) (_hR : 0 ≤ R) :
    ‖aux_localizedPhaseDerivTwo ξ x‖ ≤ 64 * R ^ 2 := by
  rw [aux_localizedPhaseDerivTwo_norm]
  have hbase : 2 * Real.pi * |ξ| ≤ 8 * R := by
    rw [← aux_localizedPhaseDeriv_norm ξ x]
    exact aux_localizedPhaseDeriv_le ξ x R hξ
  have hbase0 : 0 ≤ 2 * Real.pi * |ξ| := by positivity
  calc
    (2 * Real.pi * |ξ|) ^ 2 ≤ (8 * R) ^ 2 :=
      pow_le_pow_left₀ hbase0 hbase 2
    _ = 64 * R ^ 2 := by ring

/-- The second derivative transferred to the left transition piece. -/
noncomputable def aux_leftSecondTest (a ξ : ℝ) : ℝ → ℂ :=
  fun x ↦ aux_localizedPhaseDerivTwo ξ x *
      (aux_leftSpatialCutoff a x : ℂ) +
    2 * aux_localizedPhaseDeriv ξ x *
      (aux_leftSpatialCutoffDeriv a x : ℂ) +
    aux_localizedPhase ξ x *
      (aux_leftSpatialCutoffDerivTwo a x : ℂ)

/-- The second derivative transferred to the central constant piece. -/
noncomputable def aux_middleSecondTest (ξ : ℝ) : ℝ → ℂ :=
  aux_localizedPhaseDerivTwo ξ

/-- The second derivative transferred to the right transition piece. -/
noncomputable def aux_rightSecondTest (b ξ : ℝ) : ℝ → ℂ :=
  fun x ↦ aux_localizedPhaseDerivTwo ξ x *
      (aux_rightSpatialCutoff b x : ℂ) +
    2 * aux_localizedPhaseDeriv ξ x *
      (aux_rightSpatialCutoffDeriv b x : ℂ) +
    aux_localizedPhase ξ x *
      (aux_rightSpatialCutoffDerivTwo b x : ℂ)

/-- The global interval-supported second test produced by the three-piece
integration-by-parts transfer. -/
noncomputable def aux_localizedSecondTest (a b ξ : ℝ) : ℝ → ℂ :=
  (Set.Ioc (a - 1) a).indicator (aux_leftSecondTest a ξ) +
    (Set.Ioc a b).indicator (aux_middleSecondTest ξ) +
    (Set.Ioc b (b + 1)).indicator (aux_rightSecondTest b ξ)

/-- Each left transferred second derivative is controlled by `2^7 R²` on
the transition interval. -/
lemma aux_leftSecondTest_le (a ξ x R : ℝ)
    (hx : x ∈ Set.Icc (a - 1) a) (hξ : |ξ| ≤ R) (hR : 1 ≤ R) :
    ‖aux_leftSecondTest a ξ x‖ ≤ (2 : ℝ) ^ 7 * R ^ 2 := by
  rcases aux_leftSpatialCutoff_bounds a x hx with ⟨hL, hL1, hL2⟩
  have hp : ‖aux_localizedPhase ξ x‖ ≤ 1 := by
    rw [aux_localizedPhase_norm]
  have hp1 : ‖aux_localizedPhaseDeriv ξ x‖ ≤ 8 * R :=
    aux_localizedPhaseDeriv_le ξ x R hξ
  have hp2 : ‖aux_localizedPhaseDerivTwo ξ x‖ ≤ 64 * R ^ 2 :=
    aux_localizedPhaseDerivTwo_le ξ x R hξ (by linarith)
  have hRsq : R ≤ R ^ 2 := by nlinarith
  have hone : 1 ≤ R ^ 2 := by nlinarith
  have htwo : ‖(2 : ℂ)‖ ≤ 2 := by norm_num
  rw [aux_leftSecondTest]
  calc
    ‖aux_localizedPhaseDerivTwo ξ x * (aux_leftSpatialCutoff a x : ℂ) +
        2 * aux_localizedPhaseDeriv ξ x *
          (aux_leftSpatialCutoffDeriv a x : ℂ) +
        aux_localizedPhase ξ x * (aux_leftSpatialCutoffDerivTwo a x : ℂ)‖ ≤
        ‖aux_localizedPhaseDerivTwo ξ x * (aux_leftSpatialCutoff a x : ℂ)‖ +
          ‖2 * aux_localizedPhaseDeriv ξ x *
            (aux_leftSpatialCutoffDeriv a x : ℂ)‖ +
          ‖aux_localizedPhase ξ x * (aux_leftSpatialCutoffDerivTwo a x : ℂ)‖ := by
      calc
        ‖(aux_localizedPhaseDerivTwo ξ x * (aux_leftSpatialCutoff a x : ℂ) +
            2 * aux_localizedPhaseDeriv ξ x *
              (aux_leftSpatialCutoffDeriv a x : ℂ)) +
            aux_localizedPhase ξ x *
              (aux_leftSpatialCutoffDerivTwo a x : ℂ)‖ ≤
            ‖aux_localizedPhaseDerivTwo ξ x * (aux_leftSpatialCutoff a x : ℂ) +
              2 * aux_localizedPhaseDeriv ξ x *
                (aux_leftSpatialCutoffDeriv a x : ℂ)‖ +
              ‖aux_localizedPhase ξ x *
                (aux_leftSpatialCutoffDerivTwo a x : ℂ)‖ := norm_add_le _ _
        _ ≤ _ := by gcongr; exact norm_add_le _ _
    _ ≤ (64 * R ^ 2) * 1 + (2 * (8 * R)) * 2 + 1 * 6 := by
      simp only [norm_mul]
      gcongr
    _ ≤ (2 : ℝ) ^ 7 * R ^ 2 := by
      norm_num
      nlinarith

/-- Each central transferred second derivative is controlled by `2^7 R²` on
the low-frequency interval. -/
lemma aux_middleSecondTest_le (ξ x R : ℝ)
    (hξ : |ξ| ≤ R) (hR : 1 ≤ R) :
    ‖aux_middleSecondTest ξ x‖ ≤ (2 : ℝ) ^ 7 * R ^ 2 := by
  rw [aux_middleSecondTest]
  calc
    ‖aux_localizedPhaseDerivTwo ξ x‖ ≤ 64 * R ^ 2 :=
      aux_localizedPhaseDerivTwo_le ξ x R hξ (by linarith)
    _ ≤ (2 : ℝ) ^ 7 * R ^ 2 := by
      norm_num
      exact mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg R)

/-- Each right transferred second derivative is controlled by `2^7 R²` on
the transition interval. -/
lemma aux_rightSecondTest_le (b ξ x R : ℝ)
    (hx : x ∈ Set.Icc b (b + 1)) (hξ : |ξ| ≤ R) (hR : 1 ≤ R) :
    ‖aux_rightSecondTest b ξ x‖ ≤ (2 : ℝ) ^ 7 * R ^ 2 := by
  rcases aux_rightSpatialCutoff_bounds b x hx with ⟨hL, hL1, hL2⟩
  have hp : ‖aux_localizedPhase ξ x‖ ≤ 1 := by
    rw [aux_localizedPhase_norm]
  have hp1 : ‖aux_localizedPhaseDeriv ξ x‖ ≤ 8 * R :=
    aux_localizedPhaseDeriv_le ξ x R hξ
  have hp2 : ‖aux_localizedPhaseDerivTwo ξ x‖ ≤ 64 * R ^ 2 :=
    aux_localizedPhaseDerivTwo_le ξ x R hξ (by linarith)
  have hRsq : R ≤ R ^ 2 := by nlinarith
  have hone : 1 ≤ R ^ 2 := by nlinarith
  have htwo : ‖(2 : ℂ)‖ ≤ 2 := by norm_num
  rw [aux_rightSecondTest]
  calc
    ‖aux_localizedPhaseDerivTwo ξ x * (aux_rightSpatialCutoff b x : ℂ) +
        2 * aux_localizedPhaseDeriv ξ x *
          (aux_rightSpatialCutoffDeriv b x : ℂ) +
        aux_localizedPhase ξ x * (aux_rightSpatialCutoffDerivTwo b x : ℂ)‖ ≤
        ‖aux_localizedPhaseDerivTwo ξ x * (aux_rightSpatialCutoff b x : ℂ)‖ +
          ‖2 * aux_localizedPhaseDeriv ξ x *
            (aux_rightSpatialCutoffDeriv b x : ℂ)‖ +
          ‖aux_localizedPhase ξ x * (aux_rightSpatialCutoffDerivTwo b x : ℂ)‖ := by
      calc
        ‖(aux_localizedPhaseDerivTwo ξ x * (aux_rightSpatialCutoff b x : ℂ) +
            2 * aux_localizedPhaseDeriv ξ x *
              (aux_rightSpatialCutoffDeriv b x : ℂ)) +
            aux_localizedPhase ξ x *
              (aux_rightSpatialCutoffDerivTwo b x : ℂ)‖ ≤
            ‖aux_localizedPhaseDerivTwo ξ x * (aux_rightSpatialCutoff b x : ℂ) +
              2 * aux_localizedPhaseDeriv ξ x *
                (aux_rightSpatialCutoffDeriv b x : ℂ)‖ +
              ‖aux_localizedPhase ξ x *
                (aux_rightSpatialCutoffDerivTwo b x : ℂ)‖ := norm_add_le _ _
        _ ≤ _ := by gcongr; exact norm_add_le _ _
    _ ≤ (64 * R ^ 2) * 1 + (2 * (8 * R)) * 2 + 1 * 6 := by
      simp only [norm_mul]
      gcongr
    _ ≤ (2 : ℝ) ^ 7 * R ^ 2 := by
      norm_num
      nlinarith

/-- The three interval-supported second-test functions are jointly dominated
by `2^7 R²` on the support of the spatial cutoff. -/
lemma aux_localizedSecondTest_domination (a b ξ R x : ℝ) (hab : a ≤ b)
    (hξ : |ξ| ≤ R) (hR : 1 ≤ R) :
    ‖aux_localizedSecondTest a b ξ x‖ ≤
      ‖(Set.Icc (a - 1) (b + 1)).indicator
        (fun _ : ℝ ↦ ((2 : ℝ) ^ 7 * R ^ 2 : ℂ)) x‖ := by
  by_cases hxI : x ∈ Set.Icc (a - 1) (b + 1)
  · rcases hxI with ⟨hxlo, hxhi⟩
    have hxI' : x ∈ Set.Icc (a - 1) (b + 1) := ⟨hxlo, hxhi⟩
    have hB0 : 0 ≤ (2 : ℝ) ^ 7 * R ^ 2 := by positivity
    rw [Set.indicator_of_mem hxI']
    norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB0]
    by_cases hxleft : x ≤ a
    · by_cases hxouter : x = a - 1
      · have hleft : x ∉ Set.Ioc (a - 1) a := by
          rintro ⟨hstrict, _⟩
          rw [hxouter] at hstrict
          exact lt_irrefl _ hstrict
        have hmiddle : x ∉ Set.Ioc a b := by
          rintro ⟨hstrict, _⟩
          exact (not_lt_of_ge hxleft) hstrict
        have hright : x ∉ Set.Ioc b (b + 1) := by
          rintro ⟨hstrict, _⟩
          exact (not_lt_of_ge (hxleft.trans hab)) hstrict
        simp [aux_localizedSecondTest, hleft, hmiddle, hright]
        positivity
      · have hxlo' : a - 1 < x := lt_of_le_of_ne hxlo (Ne.symm hxouter)
        have hleft : x ∈ Set.Ioc (a - 1) a := ⟨hxlo', hxleft⟩
        have hmiddle : x ∉ Set.Ioc a b := by
          rintro ⟨hstrict, _⟩
          exact (not_lt_of_ge hxleft) hstrict
        have hright : x ∉ Set.Ioc b (b + 1) := by
          rintro ⟨hstrict, _⟩
          exact (not_lt_of_ge (hxleft.trans hab)) hstrict
        simp only [aux_localizedSecondTest, Pi.add_apply]
        rw [Set.indicator_of_mem hleft,
          Set.indicator_of_notMem hmiddle, Set.indicator_of_notMem hright]
        simp only [add_zero]
        have hbound := aux_leftSecondTest_le a ξ x R
          ⟨le_of_lt hxlo', hxleft⟩ hξ hR
        norm_num at hbound ⊢
        exact hbound
    · have hxa : a < x := lt_of_not_ge hxleft
      by_cases hxmiddle : x ≤ b
      · have hleft : x ∉ Set.Ioc (a - 1) a := by
          rintro ⟨_, hle⟩
          exact (not_le_of_gt hxa) hle
        have hmiddle : x ∈ Set.Ioc a b := ⟨hxa, hxmiddle⟩
        have hright : x ∉ Set.Ioc b (b + 1) := by
          rintro ⟨hstrict, _⟩
          exact (not_lt_of_ge hxmiddle) hstrict
        simp only [aux_localizedSecondTest, Pi.add_apply]
        rw [Set.indicator_of_notMem hleft,
          Set.indicator_of_mem hmiddle, Set.indicator_of_notMem hright]
        simp only [zero_add, add_zero]
        have hbound := aux_middleSecondTest_le ξ x R hξ hR
        norm_num at hbound ⊢
        exact hbound
      · have hxb : b < x := lt_of_not_ge hxmiddle
        have hleft : x ∉ Set.Ioc (a - 1) a := by
          rintro ⟨_, hle⟩
          exact (not_le_of_gt hxa) hle
        have hmiddle : x ∉ Set.Ioc a b := by
          rintro ⟨_, hle⟩
          exact (not_le_of_gt hxb) hle
        have hright : x ∈ Set.Ioc b (b + 1) := ⟨hxb, hxhi⟩
        simp only [aux_localizedSecondTest, Pi.add_apply]
        rw [Set.indicator_of_notMem hleft,
          Set.indicator_of_notMem hmiddle, Set.indicator_of_mem hright]
        simp only [zero_add]
        have hbound := aux_rightSecondTest_le b ξ x R ⟨le_of_lt hxb, hxhi⟩ hξ hR
        norm_num at hbound ⊢
        exact hbound
  · have hleft : x ∉ Set.Ioc (a - 1) a := by
      intro hx
      apply hxI
      exact ⟨le_of_lt hx.1, le_trans hx.2 (le_trans hab (by linarith))⟩
    have hmiddle : x ∉ Set.Ioc a b := by
      intro hx
      apply hxI
      exact ⟨le_trans (by linarith : a - 1 ≤ a) (le_of_lt hx.1),
        le_trans hx.2 (by linarith : b ≤ b + 1)⟩
    have hright : x ∉ Set.Ioc b (b + 1) := by
      intro hx
      apply hxI
      exact ⟨le_trans (le_trans (by linarith : a - 1 ≤ a) hab) (le_of_lt hx.1), hx.2⟩
    simp only [aux_localizedSecondTest, Pi.add_apply]
    rw [Set.indicator_of_notMem hleft,
      Set.indicator_of_notMem hmiddle, Set.indicator_of_notMem hright,
      Set.indicator_of_notMem hxI]
    norm_num

/-- Continuity of the left transferred second test. -/
lemma aux_leftSecondTest_continuous (a ξ : ℝ) :
    Continuous (aux_leftSecondTest a ξ) := by
  change Continuous (fun x : ℝ ↦
    aux_localizedPhaseDerivTwo ξ x * (aux_leftSpatialCutoff a x : ℂ) +
      2 * aux_localizedPhaseDeriv ξ x *
        (aux_leftSpatialCutoffDeriv a x : ℂ) +
      aux_localizedPhase ξ x * (aux_leftSpatialCutoffDerivTwo a x : ℂ))
  have hp : Continuous (aux_localizedPhase ξ) := aux_localizedPhase_continuous ξ
  have hp1 : Continuous (aux_localizedPhaseDeriv ξ) := aux_localizedPhaseDeriv_continuous ξ
  have hp2 : Continuous (aux_localizedPhaseDerivTwo ξ) :=
    aux_localizedPhaseDerivTwo_continuous ξ
  have hL : Continuous (fun x : ℝ ↦ (aux_leftSpatialCutoff a x : ℂ)) :=
    Complex.continuous_ofReal.comp (aux_leftSpatialCutoff_continuous a)
  have hL1 : Continuous (fun x : ℝ ↦ (aux_leftSpatialCutoffDeriv a x : ℂ)) :=
    Complex.continuous_ofReal.comp (aux_leftSpatialCutoffDeriv_continuous a)
  have hL2 : Continuous (fun x : ℝ ↦ (aux_leftSpatialCutoffDerivTwo a x : ℂ)) :=
    Complex.continuous_ofReal.comp (aux_leftSpatialCutoffDerivTwo_continuous a)
  exact ((hp2.mul hL).add ((continuous_const.mul hp1).mul hL1)).add (hp.mul hL2)

/-- Continuity of the right transferred second test. -/
lemma aux_rightSecondTest_continuous (b ξ : ℝ) :
    Continuous (aux_rightSecondTest b ξ) := by
  change Continuous (fun x : ℝ ↦
    aux_localizedPhaseDerivTwo ξ x * (aux_rightSpatialCutoff b x : ℂ) +
      2 * aux_localizedPhaseDeriv ξ x *
        (aux_rightSpatialCutoffDeriv b x : ℂ) +
      aux_localizedPhase ξ x * (aux_rightSpatialCutoffDerivTwo b x : ℂ))
  have hp : Continuous (aux_localizedPhase ξ) := aux_localizedPhase_continuous ξ
  have hp1 : Continuous (aux_localizedPhaseDeriv ξ) := aux_localizedPhaseDeriv_continuous ξ
  have hp2 : Continuous (aux_localizedPhaseDerivTwo ξ) :=
    aux_localizedPhaseDerivTwo_continuous ξ
  have hL : Continuous (fun x : ℝ ↦ (aux_rightSpatialCutoff b x : ℂ)) :=
    Complex.continuous_ofReal.comp (aux_rightSpatialCutoff_continuous b)
  have hL1 : Continuous (fun x : ℝ ↦ (aux_rightSpatialCutoffDeriv b x : ℂ)) :=
    Complex.continuous_ofReal.comp (aux_rightSpatialCutoffDeriv_continuous b)
  have hL2 : Continuous (fun x : ℝ ↦ (aux_rightSpatialCutoffDerivTwo b x : ℂ)) :=
    Complex.continuous_ofReal.comp (aux_rightSpatialCutoffDerivTwo_continuous b)
  exact ((hp2.mul hL).add ((continuous_const.mul hp1).mul hL1)).add (hp.mul hL2)

/-- Measurability of the global interval-supported second test. -/
lemma aux_localizedSecondTest_aestronglyMeasurable (a b ξ : ℝ) :
    AEStronglyMeasurable (aux_localizedSecondTest a b ξ) volume := by
  unfold aux_localizedSecondTest
  have hleft : AEStronglyMeasurable
      ((Set.Ioc (a - 1) a).indicator (aux_leftSecondTest a ξ)) volume :=
    (aux_leftSecondTest_continuous a ξ).aestronglyMeasurable.indicator measurableSet_Ioc
  have hmiddle : AEStronglyMeasurable
      ((Set.Ioc a b).indicator (aux_localizedPhaseDerivTwo ξ)) volume :=
    (aux_localizedPhaseDerivTwo_continuous ξ).aestronglyMeasurable.indicator measurableSet_Ioc
  have hright : AEStronglyMeasurable
      ((Set.Ioc b (b + 1)).indicator (aux_rightSecondTest b ξ)) volume :=
    (aux_rightSecondTest_continuous b ξ).aestronglyMeasurable.indicator measurableSet_Ioc
  simpa [aux_middleSecondTest] using (hleft.add hmiddle).add hright

/-- The global second test vanishes outside the union of the three transfer
intervals. -/
lemma aux_localizedSecondTest_support (a b ξ x : ℝ) (hab : a ≤ b)
    (hx : x ∉ Set.Ioc (a - 1) (b + 1)) :
    aux_localizedSecondTest a b ξ x = 0 := by
  have hleft : x ∉ Set.Ioc (a - 1) a := by
    intro h
    apply hx
    exact ⟨h.1, le_trans h.2 (le_trans hab (by linarith))⟩
  have hmiddle : x ∉ Set.Ioc a b := by
    intro h
    apply hx
    exact ⟨lt_of_le_of_lt (by linarith : a - 1 ≤ a) h.1,
      le_trans h.2 (by linarith)⟩
  have hright : x ∉ Set.Ioc b (b + 1) := by
    intro h
    apply hx
    exact ⟨lt_of_le_of_lt (by linarith [hab] : a - 1 ≤ b) h.1, h.2⟩
  simp [aux_localizedSecondTest, hleft, hmiddle, hright]

/-- The global second test has the sharp `L¹` bound needed after the
three-piece integration-by-parts transfer. -/
lemma aux_localizedSecondTest_l1 (a b ξ R : ℝ) (hab : a ≤ b)
    (hξ : |ξ| ≤ R) (hR : 1 ≤ R) :
    eLpNorm (aux_localizedSecondTest a b ξ) (1 : ℝ≥0∞) volume ≤
      ENNReal.ofReal ((2 : ℝ) ^ 7 * R ^ 2 * (b - a + 2)) := by
  let B : ℝ := 128 * R ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbound : ∀ x ∈ Set.Ioc (a - 1) (b + 1),
      ‖aux_localizedSecondTest a b ξ x‖ ≤ B := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (a - 1) (b + 1) := ⟨le_of_lt hx.1, hx.2⟩
    have hdom := aux_localizedSecondTest_domination a b ξ R x hab hξ hR
    rw [Set.indicator_of_mem hxIcc] at hdom
    norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB] at hdom
    exact hdom
  have hsupp : ∀ x : ℝ, x ∉ Set.Ioc (a - 1) (b + 1) →
      aux_localizedSecondTest a b ξ x = 0 := by
    intro x hx
    exact aux_localizedSecondTest_support a b ξ x hab hx
  have hraw := aux_eLpNorm_le_one_of_bound_support_Ioc
    (a - 1) (b + 1) B hB (aux_localizedSecondTest a b ξ) hbound hsupp
  calc
    eLpNorm (aux_localizedSecondTest a b ξ) (1 : ℝ≥0∞) volume ≤
        ENNReal.ofReal (B * ((b + 1) - (a - 1))) := hraw
    _ = ENNReal.ofReal ((2 : ℝ) ^ 7 * R ^ 2 * (b - a + 2)) := by
      have htwo : (2 : ℝ) ^ 7 = 128 := by norm_num
      rw [htwo]
      congr 1
      dsimp [B]
      ring

/-- The global second test is an `L¹` function. -/
lemma aux_localizedSecondTest_memLp_one (a b ξ R : ℝ) (hab : a ≤ b)
    (hξ : |ξ| ≤ R) (hR : 1 ≤ R) :
    MemLp (aux_localizedSecondTest a b ξ) (1 : ℝ≥0∞) volume := by
  let B : ℝ := 128 * R ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbound : ∀ x ∈ Set.Ioc (a - 1) (b + 1),
      ‖aux_localizedSecondTest a b ξ x‖ ≤ B := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (a - 1) (b + 1) := ⟨le_of_lt hx.1, hx.2⟩
    have hdom := aux_localizedSecondTest_domination a b ξ R x hab hξ hR
    rw [Set.indicator_of_mem hxIcc] at hdom
    norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB] at hdom
    exact hdom
  apply aux_memLp_one_of_bound_support_Ioc (a - 1) (b + 1) B hB
    (aux_localizedSecondTest a b ξ)
  · exact aux_localizedSecondTest_aestronglyMeasurable a b ξ
  · exact hbound
  · intro x hx
    exact aux_localizedSecondTest_support a b ξ x hab hx

/--
Combining Young's inequality with the reciprocal-kernel estimate gives the
exact `L¹` size needed after the three-piece transfer in
`localizedNegativeSobolevDecay`.
-/
lemma aux_localizedSecondTest_addConvolution_l1
    (a b R : ℝ) (k : ℕ) (hR : R = (2 : ℝ) ^ ((k : ℝ) / 2))
    (F : ℝ → ℂ) (hF_memLp : MemLp F (1 : ℝ≥0∞) volume)
    (hF : eLpNorm F (1 : ℝ≥0∞) volume ≤
      ENNReal.ofReal ((2 : ℝ) ^ 7 * R ^ 2 * (b - a + 2))) :
    eLpNorm (fun y : ℝ ↦ ∫ t : ℝ,
        aux_normalizedScaledReciprocalKernel k t * F (y + t))
      (1 : ℝ≥0∞) volume ≤
      ENNReal.ofReal ((2 : ℝ) ^ 17 * (b - a + 2) *
        (2 : ℝ) ^ (-(k : ℝ))) := by
  calc
    eLpNorm (fun y : ℝ ↦ ∫ t : ℝ,
        aux_normalizedScaledReciprocalKernel k t * F (y + t))
        (1 : ℝ≥0∞) volume ≤
        eLpNorm (aux_normalizedScaledReciprocalKernel k) (1 : ℝ≥0∞) volume *
          eLpNorm F (1 : ℝ≥0∞) volume :=
      aux_eLpNorm_addConvolution_le_one _ _
        (aux_normalizedScaledReciprocalKernel_memLp_one k) hF_memLp
    _ ≤ (ENNReal.ofReal ((2 : ℝ) ^ (-2 * (k : ℝ))) * (2 : ℝ≥0∞) ^ 10) *
          ENNReal.ofReal ((2 : ℝ) ^ 7 * R ^ 2 * (b - a + 2)) := by
      gcongr
      exact aux_normalizedScaledReciprocalKernel_l1 k
    _ = ENNReal.ofReal ((2 : ℝ) ^ 17 * (b - a + 2) *
        (2 : ℝ) ^ (-(k : ℝ))) := by
      rw [show (2 : ℝ≥0∞) ^ 10 = ENNReal.ofReal ((2 : ℝ) ^ 10) by norm_num,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ (-2 * (k : ℝ))),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤
          (2 : ℝ) ^ (-2 * (k : ℝ)) * (2 : ℝ) ^ 10)]
      congr 1
      rw [hR, ← Real.rpow_natCast ((2 : ℝ) ^ ((k : ℝ) / 2)) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring_nf
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      have hexp : -((k : ℝ) * 2) + (k : ℝ) = -(k : ℝ) := by ring
      rw [hexp]
      ring

/-- An integrable function supported in one interval splits into its three
adjacent interval integrals.  This is the spatial partition used before the
three-piece integration-by-parts transfer in `localizedNegativeSobolevDecay`.
-/
lemma aux_integral_eq_three_intervalIntegral
    (A B C D : ℝ) (F : ℝ → ℂ) (hF : Integrable F volume)
    (hsupp : Function.support F ⊆ Set.Ioc A D) :
    (∫ t : ℝ, F t) =
      (∫ t in A..B, F t) + (∫ t in B..C, F t) + (∫ t in C..D, F t) := by
  have hABi : IntervalIntegrable F volume A B := hF.intervalIntegrable
  have hBCi : IntervalIntegrable F volume B C := hF.intervalIntegrable
  have hCDi : IntervalIntegrable F volume C D := hF.intervalIntegrable
  have hACi : IntervalIntegrable F volume A C := hF.intervalIntegrable
  have hAC :
      (∫ t in A..B, F t) + (∫ t in B..C, F t) = ∫ t in A..C, F t :=
    intervalIntegral.integral_add_adjacent_intervals hABi hBCi
  have hAD :
      (∫ t in A..C, F t) + (∫ t in C..D, F t) = ∫ t in A..D, F t :=
    intervalIntegral.integral_add_adjacent_intervals hACi hCDi
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupp, ← hAD, ← hAC]

/-- The Fourier transform of a compactly localized raw convolution rewrites,
by the determinant-one shear, as a translated test pairing with the input.
This is the Fubini entry point for `localizedNegativeSobolevDecay`.
-/
lemma aux_localizedFourier_eq_sheared
    (a b : ℝ) (κ g : ℝ → ℂ) (ξ C : ℝ)
    (hκ : Integrable κ volume) (hg : AEStronglyMeasurable g volume)
    (hgbound : ∀ᵐ x : ℝ ∂volume, ‖g x‖ ≤ C) :
    𝓕 (fun x : ℝ ↦ (spatialCutoff a b x : ℂ) * aux_convolution κ g x) ξ =
      ∫ y : ℝ, g y * (∫ t : ℝ, κ t *
        (aux_localizedPhase ξ (y + t) * (spatialCutoff a b (y + t) : ℂ))) := by
  let φ : ℝ → ℂ := fun x ↦
    aux_localizedPhase ξ x * (spatialCutoff a b x : ℂ)
  have hcutcont : Continuous (spatialCutoff a b) := by
    unfold spatialCutoff
    exact (aux_continuous_smoothStep.comp
      ((continuous_id.sub continuous_const).add continuous_const)).mul
      (aux_continuous_smoothStep.comp
        ((continuous_const.add continuous_const).sub continuous_id))
  have hφcont : Continuous φ := by
    dsimp [φ]
    exact (aux_localizedPhase_continuous ξ).mul
      (Complex.continuous_ofReal.comp hcutcont)
  have hφ : Integrable φ volume := by
    apply hφcont.integrable_of_hasCompactSupport
    apply HasCompactSupport.intro
      (isCompact_Icc : IsCompact (Set.Icc (a - 1) (b + 1)))
    intro x hx
    have hx' : x < a - 1 ∨ b + 1 < x := by
      by_contra h
      push_neg at h
      exact hx ⟨h.1, h.2⟩
    have hzero : spatialCutoff a b x = 0 := by
      rcases hx' with hleft | hright
      · rw [spatialCutoff,
          aux_smoothStep_eq_zero_of_nonpos (by linarith : x - a + 1 ≤ 0)]
        simp
      · rw [spatialCutoff,
          aux_smoothStep_eq_zero_of_nonpos (by linarith : b + 1 - x ≤ 0)]
        simp
    simp [φ, hzero]
  have hshear := aux_integral_mul_aux_convolution_eq_sheared κ g φ
    hκ hφ hg C hgbound
  calc
    𝓕 (fun x : ℝ ↦ (spatialCutoff a b x : ℂ) * aux_convolution κ g x) ξ =
        ∫ x : ℝ, φ x * aux_convolution κ g x := by
      rw [Real.fourier_eq]
      apply integral_congr_ae
      filter_upwards with x
      change (Real.fourierChar (-inner ℝ x ξ) : ℂ) *
          ((spatialCutoff a b x : ℂ) * aux_convolution κ g x) =
        φ x * aux_convolution κ g x
      rw [← aux_localizedPhase_eq_fourierPhase]
      dsimp [φ]
      ring
    _ = ∫ y : ℝ, g y * (∫ t : ℝ, κ t * φ (y + t)) := hshear
    _ = ∫ y : ℝ, g y * (∫ t : ℝ, κ t *
        (aux_localizedPhase ξ (y + t) * (spatialCutoff a b (y + t) : ℂ))) := by
      rfl

/-- The sheared localized phase-cutoff test partitions exactly into its left
cubic transition, central phase, and right cubic transition. -/
lemma aux_inner_eq_three_localizedPieces
    (a b : ℝ) (hab : a ≤ b) (κ : ℝ → ℂ) (ξ y : ℝ)
    (hκ : Integrable κ volume) :
    (∫ t : ℝ, κ t *
        (aux_localizedPhase ξ (y + t) * (spatialCutoff a b (y + t) : ℂ))) =
      (∫ t in (a - 1 - y)..(a - y), κ t * aux_leftLocalizedTest a ξ y t) +
        (∫ t in (a - y)..(b - y), κ t * aux_middleLocalizedTest ξ y t) +
          (∫ t in (b - y)..(b + 1 - y), κ t * aux_rightLocalizedTest b ξ y t) := by
  have hcutcont : Continuous (spatialCutoff a b) := by
    unfold spatialCutoff
    exact (aux_continuous_smoothStep.comp
      ((continuous_id.sub continuous_const).add continuous_const)).mul
      (aux_continuous_smoothStep.comp
        ((continuous_const.add continuous_const).sub continuous_id))
  have hphasecutcont : Continuous (fun x : ℝ ↦
      aux_localizedPhase ξ x * (spatialCutoff a b x : ℂ)) :=
    (aux_localizedPhase_continuous ξ).mul
      (Complex.continuous_ofReal.comp hcutcont)
  have hphasecutnorm : ∀ x : ℝ,
      ‖aux_localizedPhase ξ x * (spatialCutoff a b x : ℂ)‖ ≤ 1 := by
    intro x
    have hphase : ‖aux_localizedPhase ξ x‖ = 1 := by
      rw [aux_localizedPhase]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [norm_mul, hphase]
    simp only [one_mul, Complex.norm_real]
    exact (abs_of_nonneg (aux_spatialCutoff_pointwise a b x).1).trans_le
      (aux_spatialCutoff_pointwise a b x).2
  have hinner : Integrable (fun t : ℝ ↦ κ t *
      (aux_localizedPhase ξ (y + t) * (spatialCutoff a b (y + t) : ℂ))) volume := by
    let ψ : ℝ → ℂ := fun t ↦
      aux_localizedPhase ξ (y + t) * (spatialCutoff a b (y + t) : ℂ)
    change Integrable (fun t : ℝ ↦ κ t * ψ t) volume
    have hψmeas : AEStronglyMeasurable ψ volume :=
      (hphasecutcont.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    apply hκ.norm.mono' (hκ.1.mul hψmeas)
    filter_upwards with t
    change ‖κ t * ψ t‖ ≤ ‖κ t‖
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hphasecutnorm (y + t))
  have hsupp : Function.support (fun t : ℝ ↦ κ t *
      (aux_localizedPhase ξ (y + t) * (spatialCutoff a b (y + t) : ℂ))) ⊆
      Set.Ioc (a - 1 - y) (b + 1 - y) := by
    intro t ht
    rw [Function.mem_support] at ht
    have hcut_ne : spatialCutoff a b (y + t) ≠ 0 := by
      intro hzero
      apply ht
      simp [hzero]
    have hmem : y + t ∈ Set.Icc (a - 1) (b + 1) :=
      aux_spatialCutoff_tsupport (subset_tsupport _ hcut_ne)
    constructor
    · have hne : a - 1 ≠ y + t := by
        intro heq
        apply hcut_ne
        rw [← heq, spatialCutoff,
          aux_smoothStep_eq_zero_of_nonpos
            (by norm_num : (a - 1) - a + 1 ≤ 0)]
        simp
      apply lt_of_le_of_ne
      · linarith [hmem.1]
      · intro heq
        apply hne
        linarith
    · linarith [hmem.2]
  have hpartition := aux_integral_eq_three_intervalIntegral
    (a - 1 - y) (a - y) (b - y) (b + 1 - y)
    (fun t : ℝ ↦ κ t *
      (aux_localizedPhase ξ (y + t) * (spatialCutoff a b (y + t) : ℂ))) hinner hsupp
  rw [hpartition]
  have hleft :
      (∫ t in (a - 1 - y)..(a - y), κ t *
        (aux_localizedPhase ξ (y + t) * (spatialCutoff a b (y + t) : ℂ))) =
        ∫ t in (a - 1 - y)..(a - y), κ t * aux_leftLocalizedTest a ξ y t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (a - 1 - y) (a - y) := by
      simpa only [Set.uIcc_of_le (by linarith : a - 1 - y ≤ a - y)] using ht
    have hcut : spatialCutoff a b (y + t) = aux_leftSpatialCutoff a (y + t) :=
      aux_spatialCutoff_eq_leftPiece a b (y + t) hab (by
        constructor <;> linarith [ht'.1, ht'.2])
    change κ t * (aux_localizedPhase ξ (y + t) *
      (spatialCutoff a b (y + t) : ℂ)) = κ t * aux_leftLocalizedTest a ξ y t
    rw [hcut]
    rfl
  have hmiddle :
      (∫ t in (a - y)..(b - y), κ t *
        (aux_localizedPhase ξ (y + t) * (spatialCutoff a b (y + t) : ℂ))) =
        ∫ t in (a - y)..(b - y), κ t * aux_middleLocalizedTest ξ y t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (a - y) (b - y) := by
      simpa only [Set.uIcc_of_le (by linarith : a - y ≤ b - y)] using ht
    have hcut : spatialCutoff a b (y + t) = 1 :=
      aux_spatialCutoff_one_on (by
        constructor <;> linarith [ht'.1, ht'.2])
    change κ t * (aux_localizedPhase ξ (y + t) *
      (spatialCutoff a b (y + t) : ℂ)) = κ t * aux_middleLocalizedTest ξ y t
    rw [hcut]
    simp [aux_middleLocalizedTest]
  have hright :
      (∫ t in (b - y)..(b + 1 - y), κ t *
        (aux_localizedPhase ξ (y + t) * (spatialCutoff a b (y + t) : ℂ))) =
        ∫ t in (b - y)..(b + 1 - y), κ t * aux_rightLocalizedTest b ξ y t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (b - y) (b + 1 - y) := by
      simpa only [Set.uIcc_of_le (by linarith : b - y ≤ b + 1 - y)] using ht
    have hcut : spatialCutoff a b (y + t) = aux_rightSpatialCutoff b (y + t) :=
      aux_spatialCutoff_eq_rightPiece a b (y + t) hab (by
        constructor <;> linarith [ht'.1, ht'.2])
    change κ t * (aux_localizedPhase ξ (y + t) *
      (spatialCutoff a b (y + t) : ℂ)) = κ t * aux_rightLocalizedTest b ξ y t
    rw [hcut]
    rfl
  rw [hleft, hmiddle, hright]

/-- Applying the three-piece transfer and converting each resulting interval
to an indicator-supported whole-line integral yields the three components of
`aux_localizedSecondTest`. -/
lemma aux_inner_eq_transferred_indicatorPieces
    (a b : ℝ) (hab : a ≤ b) (k : ℕ) (ξ y : ℝ) :
    (∫ t : ℝ,
      aux_scaledInverseFourierKernel (fun z ↦ (annularCutoff z : ℂ)) k t *
        (aux_localizedPhase ξ (y + t) * (spatialCutoff a b (y + t) : ℂ))) =
      (∫ t : ℝ, aux_normalizedScaledReciprocalKernel k t *
        (Set.Ioc (a - 1) a).indicator (aux_leftSecondTest a ξ) (y + t)) +
        (∫ t : ℝ, aux_normalizedScaledReciprocalKernel k t *
          (Set.Ioc a b).indicator (aux_middleSecondTest ξ) (y + t)) +
          (∫ t : ℝ, aux_normalizedScaledReciprocalKernel k t *
            (Set.Ioc b (b + 1)).indicator (aux_rightSecondTest b ξ) (y + t)) := by
  have hκ : Integrable
      (aux_scaledInverseFourierKernel (fun z ↦ (annularCutoff z : ℂ)) k) volume :=
    memLp_one_iff_integrable.mp (aux_scaledAnnularInverseFourierKernel_memLp_one k)
  have hpieces := aux_inner_eq_three_localizedPieces a b hab
    (aux_scaledInverseFourierKernel (fun z ↦ (annularCutoff z : ℂ)) k) ξ y hκ
  have htransfer := aux_threePiece_dyadicKernel_transfer a b hab k ξ y
  have hafter :
      (∫ t : ℝ,
        aux_scaledInverseFourierKernel (fun z ↦ (annularCutoff z : ℂ)) k t *
          (aux_localizedPhase ξ (y + t) * (spatialCutoff a b (y + t) : ℂ))) =
        (∫ t in (a - 1 - y)..(a - y),
          aux_normalizedScaledReciprocalKernel k t *
            aux_leftLocalizedTestDerivTwo a ξ y t) +
          (∫ t in (a - y)..(b - y),
            aux_normalizedScaledReciprocalKernel k t *
              aux_middleLocalizedTestDerivTwo ξ y t) +
            (∫ t in (b - y)..(b + 1 - y),
              aux_normalizedScaledReciprocalKernel k t *
                aux_rightLocalizedTestDerivTwo b ξ y t) := by
    rw [hpieces, htransfer]
  rw [hafter]
  have hleft := aux_intervalIntegral_eq_indicator_add
    (a - 1) a y (by linarith) (aux_normalizedScaledReciprocalKernel k)
    (aux_leftSecondTest a ξ)
  have hmiddle := aux_intervalIntegral_eq_indicator_add
    a b y hab (aux_normalizedScaledReciprocalKernel k)
    (aux_middleSecondTest ξ)
  have hright := aux_intervalIntegral_eq_indicator_add
    b (b + 1) y (by linarith) (aux_normalizedScaledReciprocalKernel k)
    (aux_rightSecondTest b ξ)
  rw [show (∫ t in (a - 1 - y)..(a - y),
      aux_normalizedScaledReciprocalKernel k t *
        aux_leftLocalizedTestDerivTwo a ξ y t) =
      ∫ t : ℝ, aux_normalizedScaledReciprocalKernel k t *
        (Set.Ioc (a - 1) a).indicator (aux_leftSecondTest a ξ) (y + t) by
      simpa [aux_leftLocalizedTestDerivTwo, aux_leftSecondTest] using hleft]
  rw [show (∫ t in (a - y)..(b - y),
      aux_normalizedScaledReciprocalKernel k t *
        aux_middleLocalizedTestDerivTwo ξ y t) =
      ∫ t : ℝ, aux_normalizedScaledReciprocalKernel k t *
        (Set.Ioc a b).indicator (aux_middleSecondTest ξ) (y + t) by
      simpa [aux_middleLocalizedTestDerivTwo, aux_middleSecondTest] using hmiddle]
  rw [show (∫ t in (b - y)..(b + 1 - y),
      aux_normalizedScaledReciprocalKernel k t *
        aux_rightLocalizedTestDerivTwo b ξ y t) =
      ∫ t : ℝ, aux_normalizedScaledReciprocalKernel k t *
        (Set.Ioc b (b + 1)).indicator (aux_rightSecondTest b ξ) (y + t) by
      simpa [aux_rightLocalizedTestDerivTwo, aux_rightSecondTest] using hright]

/-- The Fourier transform of the localized dyadic term is a pairing against
one translated convolution with the global interval-supported transferred
second test.  This is the Fourier-rewrite input for
`localizedNegativeSobolevDecay`. -/
lemma aux_localizedFourier_eq_globalSecondTest
    (a b : ℝ) (hab : a ≤ b) (k : ℕ) (g : ℝ → ℂ) (ξ : ℝ)
    (hg : MemLp g (∞ : ℝ≥0∞) volume) :
    𝓕 (fun x : ℝ ↦ (spatialCutoff a b x : ℂ) * Q k g x) ξ =
      ∫ y : ℝ, g y * (∫ t : ℝ,
        aux_normalizedScaledReciprocalKernel k t *
          aux_localizedSecondTest a b ξ (y + t)) := by
  let R : ℝ := max 1 |ξ|
  have hR : 1 ≤ R := by
    dsimp [R]
    exact le_max_left _ _
  have hξ : |ξ| ≤ R := by
    dsimp [R]
    exact le_max_right _ _
  let B : ℝ := (2 : ℝ) ^ 7 * R ^ 2
  let fL : ℝ → ℂ := (Set.Ioc (a - 1) a).indicator (aux_leftSecondTest a ξ)
  let fM : ℝ → ℂ := (Set.Ioc a b).indicator (aux_middleSecondTest ξ)
  let fR : ℝ → ℂ := (Set.Ioc b (b + 1)).indicator (aux_rightSecondTest b ξ)
  have hfL : AEStronglyMeasurable fL volume := by
    simpa [fL] using
      (aux_leftSecondTest_continuous a ξ).aestronglyMeasurable.indicator measurableSet_Ioc
  have hfM : AEStronglyMeasurable fM volume := by
    simpa [fM, aux_middleSecondTest] using
      (aux_localizedPhaseDerivTwo_continuous ξ).aestronglyMeasurable.indicator measurableSet_Ioc
  have hfR : AEStronglyMeasurable fR volume := by
    simpa [fR] using
      (aux_rightSecondTest_continuous b ξ).aestronglyMeasurable.indicator measurableSet_Ioc
  have hBL : ∀ x : ℝ, ‖fL x‖ ≤ B := by
    intro x
    change ‖(Set.Ioc (a - 1) a).indicator (aux_leftSecondTest a ξ) x‖ ≤
      (2 : ℝ) ^ 7 * R ^ 2
    by_cases hx : x ∈ Set.Ioc (a - 1) a
    · rw [Set.indicator_of_mem hx]
      exact aux_leftSecondTest_le a ξ x R
        ⟨le_of_lt hx.1, hx.2⟩ hξ hR
    · rw [Set.indicator_of_notMem hx, norm_zero]
      positivity
  have hBM : ∀ x : ℝ, ‖fM x‖ ≤ B := by
    intro x
    change ‖(Set.Ioc a b).indicator (aux_middleSecondTest ξ) x‖ ≤
      (2 : ℝ) ^ 7 * R ^ 2
    by_cases hx : x ∈ Set.Ioc a b
    · rw [Set.indicator_of_mem hx]
      exact aux_middleSecondTest_le ξ x R hξ hR
    · rw [Set.indicator_of_notMem hx, norm_zero]
      positivity
  have hBR : ∀ x : ℝ, ‖fR x‖ ≤ B := by
    intro x
    change ‖(Set.Ioc b (b + 1)).indicator (aux_rightSecondTest b ξ) x‖ ≤
      (2 : ℝ) ^ 7 * R ^ 2
    by_cases hx : x ∈ Set.Ioc b (b + 1)
    · rw [Set.indicator_of_mem hx]
      exact aux_rightSecondTest_le b ξ x R
        ⟨le_of_lt hx.1, hx.2⟩ hξ hR
    · rw [Set.indicator_of_notMem hx, norm_zero]
      positivity
  have hκdy : Integrable
      (aux_scaledInverseFourierKernel (fun z ↦ (annularCutoff z : ℂ)) k) volume :=
    memLp_one_iff_integrable.mp (aux_scaledAnnularInverseFourierKernel_memLp_one k)
  have hκrec : Integrable (aux_normalizedScaledReciprocalKernel k) volume :=
    memLp_one_iff_integrable.mp (aux_normalizedScaledReciprocalKernel_memLp_one k)
  have hsum (y : ℝ) :
      (∫ t : ℝ, aux_normalizedScaledReciprocalKernel k t * fL (y + t)) +
          (∫ t : ℝ, aux_normalizedScaledReciprocalKernel k t * fM (y + t)) +
          (∫ t : ℝ, aux_normalizedScaledReciprocalKernel k t * fR (y + t)) =
        ∫ t : ℝ, aux_normalizedScaledReciprocalKernel k t *
          ((fL + fM + fR) (y + t)) :=
    aux_addConvolution_three_eq_addConvolution_sum
      (aux_normalizedScaledReciprocalKernel k) fL fM fR y hκrec
      hfL B hBL hfM B hBM hfR B hBR
  have hshear := aux_localizedFourier_eq_sheared a b
    (aux_scaledInverseFourierKernel (fun z ↦ (annularCutoff z : ℂ)) k) g ξ
    (eLpNorm g (∞ : ℝ≥0∞) volume).toReal hκdy hg.1
    (aux_homogeneous_ae_norm_le_toReal g hg)
  rw [Q]
  calc
    𝓕 (fun x : ℝ ↦ (spatialCutoff a b x : ℂ) *
        aux_convolution
          (aux_scaledInverseFourierKernel (fun z ↦ (annularCutoff z : ℂ)) k) g x) ξ =
        ∫ y : ℝ, g y * (∫ t : ℝ,
          aux_scaledInverseFourierKernel (fun z ↦ (annularCutoff z : ℂ)) k t *
            (aux_localizedPhase ξ (y + t) *
              (spatialCutoff a b (y + t) : ℂ))) := hshear
    _ = ∫ y : ℝ, g y * (∫ t : ℝ,
        aux_normalizedScaledReciprocalKernel k t *
          aux_localizedSecondTest a b ξ (y + t)) := by
      apply integral_congr_ae
      filter_upwards with y
      apply congrArg (fun z : ℂ ↦ g y * z)
      calc
        (∫ t : ℝ,
          aux_scaledInverseFourierKernel (fun z ↦ (annularCutoff z : ℂ)) k t *
            (aux_localizedPhase ξ (y + t) *
              (spatialCutoff a b (y + t) : ℂ))) =
            (∫ t : ℝ, aux_normalizedScaledReciprocalKernel k t *
              (Set.Ioc (a - 1) a).indicator (aux_leftSecondTest a ξ) (y + t)) +
              (∫ t : ℝ, aux_normalizedScaledReciprocalKernel k t *
                (Set.Ioc a b).indicator (aux_middleSecondTest ξ) (y + t)) +
                (∫ t : ℝ, aux_normalizedScaledReciprocalKernel k t *
                  (Set.Ioc b (b + 1)).indicator (aux_rightSecondTest b ξ) (y + t)) :=
          aux_inner_eq_transferred_indicatorPieces a b hab k ξ y
        _ = ∫ t : ℝ, aux_normalizedScaledReciprocalKernel k t *
            aux_localizedSecondTest a b ξ (y + t) := by
          simpa [fL, fM, fR, aux_localizedSecondTest] using hsum y

/--
Pairing an `L∞` input with an `L¹` function is controlled by the product of
their raw norms.  This is used after the integration-by-parts transfer in
`localizedNegativeSobolevDecay`.
-/
lemma aux_norm_integral_mul_le_top_one
    (g ψ : ℝ → ℂ) (hg : MemLp g (∞ : ℝ≥0∞) volume)
    (hψ : MemLp ψ (1 : ℝ≥0∞) volume) :
    ‖∫ x : ℝ, g x * ψ x‖ ≤
      (eLpNorm g (∞ : ℝ≥0∞) volume).toReal *
        (eLpNorm ψ (1 : ℝ≥0∞) volume).toReal := by
  let G : ℝ := (eLpNorm g (∞ : ℝ≥0∞) volume).toReal
  have hGtop : eLpNorm g (∞ : ℝ≥0∞) volume ≠ ∞ := hg.eLpNorm_ne_top
  have hgbound : ∀ᵐ x : ℝ ∂volume, ‖g x‖ ≤ G := by
    filter_upwards [enorm_ae_le_eLpNormEssSup g volume] with x hx
    apply (ENNReal.ofReal_le_iff_le_toReal hGtop).mp
    simpa only [ofReal_norm, eLpNorm_exponent_top] using hx
  have hψint : Integrable ψ volume := memLp_one_iff_integrable.mp hψ
  have hprodmeas : AEStronglyMeasurable (fun x : ℝ ↦ g x * ψ x) volume :=
    hg.1.mul hψ.1
  have hprod : Integrable (fun x : ℝ ↦ g x * ψ x) volume := by
    apply (hψint.norm.const_mul G).mono' hprodmeas
    filter_upwards [hgbound] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  have hmajor : Integrable (fun x : ℝ ↦ G * ‖ψ x‖) volume := by
    simpa [smul_eq_mul] using hψint.norm.const_mul G
  calc
    ‖∫ x : ℝ, g x * ψ x‖ ≤ ∫ x : ℝ, ‖g x * ψ x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, G * ‖ψ x‖ := by
      apply integral_mono_ae hprod.norm hmajor
      filter_upwards [hgbound] with x hx
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ = G * ∫ x : ℝ, ‖ψ x‖ := integral_const_mul G _
    _ = (eLpNorm g (∞ : ℝ≥0∞) volume).toReal *
        (eLpNorm ψ (1 : ℝ≥0∞) volume).toReal := by
      rw [integral_norm_eq_lintegral_enorm hψ.1,
        ← eLpNorm_one_eq_lintegral_enorm]

/--
An explicit `L¹` norm bound can be inserted directly into the `L∞`--`L¹`
pairing estimate.  This is the final scalar step in the low-frequency part
of `localizedNegativeSobolevDecay`.
-/
lemma aux_norm_integral_mul_le_top_one_of_eLpNorm_bound
    (g ψ : ℝ → ℂ) (hg : MemLp g (∞ : ℝ≥0∞) volume)
    (hψ : MemLp ψ (1 : ℝ≥0∞) volume) (B : ℝ) (hB : 0 ≤ B)
    (hψB : eLpNorm ψ (1 : ℝ≥0∞) volume ≤ ENNReal.ofReal B) :
    ‖∫ x : ℝ, g x * ψ x‖ ≤
      (eLpNorm g (∞ : ℝ≥0∞) volume).toReal * B := by
  calc
    ‖∫ x : ℝ, g x * ψ x‖ ≤
        (eLpNorm g (∞ : ℝ≥0∞) volume).toReal *
          (eLpNorm ψ (1 : ℝ≥0∞) volume).toReal :=
      aux_norm_integral_mul_le_top_one g ψ hg hψ
    _ ≤ (eLpNorm g (∞ : ℝ≥0∞) volume).toReal *
          (ENNReal.ofReal B).toReal := by
      exact mul_le_mul_of_nonneg_left
        (ENNReal.toReal_mono ENNReal.ofReal_ne_top hψB) (ENNReal.toReal_nonneg)
    _ = (eLpNorm g (∞ : ℝ≥0∞) volume).toReal * B := by
      rw [ENNReal.toReal_ofReal hB]

/-- Once the Fourier-testing and three-piece transfer identify the localized
Fourier transform with the aggregate second test, Young's inequality gives
the exact low-frequency pointwise decay. -/
lemma aux_localizedNegativeSobolev_lowFrequency_pointwise_of_transfer
    (a b : ℝ) (hab : a ≤ b) (k : ℕ) (_hk : 1 ≤ k)
    (g : ℝ → ℂ) (hg : MemLp g (∞ : ℝ≥0∞) volume)
    (ξ : ℝ) (hξ : ξ ∈ Set.Icc
      (-(2 : ℝ) ^ ((k : ℝ) / 2)) ((2 : ℝ) ^ ((k : ℝ) / 2)))
    (htransfer :
      𝓕 (fun x : ℝ ↦ (spatialCutoff a b x : ℂ) * Q k g x) ξ =
        ∫ y : ℝ, g y * (∫ t : ℝ,
          aux_normalizedScaledReciprocalKernel k t *
            aux_localizedSecondTest a b ξ (y + t))) :
    ‖𝓕 (fun x : ℝ ↦ (spatialCutoff a b x : ℂ) * Q k g x) ξ‖ ≤
      (2 : ℝ) ^ 17 * (b - a + 2) * (2 : ℝ) ^ (-(k : ℝ)) *
        (eLpNorm g (∞ : ℝ≥0∞) volume).toReal := by
  let R : ℝ := (2 : ℝ) ^ ((k : ℝ) / 2)
  have hR : R = (2 : ℝ) ^ ((k : ℝ) / 2) := rfl
  have hRone : 1 ≤ R := by
    rw [hR]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hξabs : |ξ| ≤ R := by
    rw [hR]
    exact abs_le.mpr hξ
  have hFmem : MemLp (aux_localizedSecondTest a b ξ) (1 : ℝ≥0∞) volume :=
    aux_localizedSecondTest_memLp_one a b ξ R hab hξabs hRone
  have hFl1 : eLpNorm (aux_localizedSecondTest a b ξ) (1 : ℝ≥0∞) volume ≤
      ENNReal.ofReal ((2 : ℝ) ^ 7 * R ^ 2 * (b - a + 2)) :=
    aux_localizedSecondTest_l1 a b ξ R hab hξabs hRone
  let ψ : ℝ → ℂ := fun y ↦ ∫ t : ℝ,
    aux_normalizedScaledReciprocalKernel k t * aux_localizedSecondTest a b ξ (y + t)
  have hψ : MemLp ψ (1 : ℝ≥0∞) volume := by
    simpa [ψ] using aux_memLp_addConvolution_one
      (aux_normalizedScaledReciprocalKernel k) (aux_localizedSecondTest a b ξ)
      (aux_normalizedScaledReciprocalKernel_memLp_one k) hFmem
  have hψl1 : eLpNorm ψ (1 : ℝ≥0∞) volume ≤
      ENNReal.ofReal ((2 : ℝ) ^ 17 * (b - a + 2) *
        (2 : ℝ) ^ (-(k : ℝ))) := by
    simpa [ψ] using aux_localizedSecondTest_addConvolution_l1 a b R k hR
      (aux_localizedSecondTest a b ξ) hFmem hFl1
  have hB : 0 ≤ (2 : ℝ) ^ 17 * (b - a + 2) * (2 : ℝ) ^ (-(k : ℝ)) := by
    have : 0 ≤ b - a + 2 := by linarith
    positivity
  calc
    ‖𝓕 (fun x : ℝ ↦ (spatialCutoff a b x : ℂ) * Q k g x) ξ‖ =
        ‖∫ y : ℝ, g y * ψ y‖ := by
      rw [htransfer]
    _ ≤ (eLpNorm g (∞ : ℝ≥0∞) volume).toReal *
        ((2 : ℝ) ^ 17 * (b - a + 2) * (2 : ℝ) ^ (-(k : ℝ))) :=
      aux_norm_integral_mul_le_top_one_of_eLpNorm_bound g ψ hg hψ _ hB hψl1
    _ = (2 : ℝ) ^ 17 * (b - a + 2) * (2 : ℝ) ^ (-(k : ℝ)) *
        (eLpNorm g (∞ : ℝ≥0∞) volume).toReal := by ring

/-- The localized dyadic Fourier transform has the required pointwise bound
on the low-frequency region.  This is the `hpoint` input for
`aux_localizedNegativeSobolev_from_low_high_exact`. -/
lemma aux_localizedNegativeSobolev_lowFrequency_pointwise
    (a b : ℝ) (hab : a ≤ b) (k : ℕ) (hk : 1 ≤ k)
    (g : ℝ → ℂ) (hg : MemLp g (∞ : ℝ≥0∞) volume) :
    ∀ ξ ∈ aux_sobolevDifference_lowFrequency
        ((2 : ℝ) ^ ((k : ℝ) / 2)),
      ‖𝓕 (fun x : ℝ ↦ (spatialCutoff a b x : ℂ) * Q k g x) ξ‖ ≤
        (2 : ℝ) ^ 17 * (b - a + 2) * (2 : ℝ) ^ (-(k : ℝ)) *
          (eLpNorm g (∞ : ℝ≥0∞) volume).toReal := by
  intro ξ hξ
  change ξ ∈ Set.Icc (-(2 : ℝ) ^ ((k : ℝ) / 2))
    ((2 : ℝ) ^ ((k : ℝ) / 2)) at hξ
  exact aux_localizedNegativeSobolev_lowFrequency_pointwise_of_transfer
    a b hab k hk g hg ξ hξ
    (aux_localizedFourier_eq_globalSecondTest a b hab k g ξ hg)

/--
A uniform bound for a raw Fourier transform on a symmetric low-frequency
interval controls the corresponding squared Fourier energy.  This is the
energy-conversion step used in `localizedNegativeSobolevDecay`.
-/
lemma aux_lowFrequency_energy_le_of_norm_le
    (R B : ℝ) (F : ℝ → ℂ)
    (hF : ∀ ξ ∈ Set.Icc (-R) R, ‖F ξ‖ ≤ B) :
    (∫⁻ ξ : ℝ in aux_sobolevDifference_lowFrequency R,
      ‖F ξ‖ₑ ^ (2 : ℝ)) ≤
      ENNReal.ofReal (2 * R) * (ENNReal.ofReal B) ^ (2 : ℝ) := by
  change (∫⁻ ξ : ℝ in Set.Icc (-R) R, ‖F ξ‖ₑ ^ (2 : ℝ)) ≤ _
  have hmeas : Measurable (fun _ : ℝ ↦ (ENNReal.ofReal B) ^ (2 : ℝ)) :=
    measurable_const
  calc
    (∫⁻ ξ : ℝ in Set.Icc (-R) R, ‖F ξ‖ₑ ^ (2 : ℝ)) ≤
        ∫⁻ ξ : ℝ in Set.Icc (-R) R, (ENNReal.ofReal B) ^ (2 : ℝ) := by
      exact MeasureTheory.setLIntegral_mono hmeas (fun ξ hξ ↦
        ENNReal.rpow_le_rpow (by
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hF ξ hξ)) (by norm_num))
    _ = ENNReal.ofReal (2 * R) * (ENNReal.ofReal B) ^ (2 : ℝ) := by
      rw [MeasureTheory.lintegral_const]
      simp only [Measure.restrict_apply_univ, Real.volume_Icc]
      rw [mul_comm]
      congr 1
      congr 1
      ring

/--
The explicit scalar comparison which combines the low- and high-frequency
energy coefficients in `localizedNegativeSobolevDecay`.
-/
lemma aux_localizedNegativeSobolev_energy_coefficient_bound
    (d : ℝ) (hd : 2 ≤ d) (k : ℕ) :
    (2 * (2 : ℝ) ^ ((k : ℝ) / 2)) *
        ((2 : ℝ) ^ 17 * d * (2 : ℝ) ^ (-(k : ℝ))) ^ (2 : ℕ) +
      (2 : ℝ) ^ (-(k : ℝ) / 2) *
        ((2 : ℝ) ^ 6 * Real.sqrt d) ^ (2 : ℕ) ≤
      ((2 : ℝ) ^ 19 * d * (2 : ℝ) ^ (-(k : ℝ) / 4)) ^ (2 : ℕ) := by
  let x : ℝ := (2 : ℝ) ^ (-(k : ℝ) / 4)
  have hx0 : 0 < x := by
    dsimp [x]
    positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · norm_num
    · have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
  have hxpow : x ^ (6 : ℕ) ≤ x ^ (2 : ℕ) := by
    calc
      x ^ (6 : ℕ) = x ^ (2 : ℕ) * x ^ (4 : ℕ) := by ring
      _ ≤ x ^ (2 : ℕ) * 1 := by
        gcongr
        exact pow_le_one₀ hx0.le hx1
      _ = x ^ (2 : ℕ) := mul_one _
  have hscale :
      (2 : ℝ) ^ ((k : ℝ) / 2) * ((2 : ℝ) ^ (-(k : ℝ))) ^ (2 : ℕ) =
        x ^ (6 : ℕ) := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hlowid :
      (2 * (2 : ℝ) ^ ((k : ℝ) / 2)) *
          ((2 : ℝ) ^ 17 * d * (2 : ℝ) ^ (-(k : ℝ))) ^ (2 : ℕ) =
        (2 : ℝ) ^ 35 * d ^ (2 : ℕ) * x ^ (6 : ℕ) := by
    calc
      (2 * (2 : ℝ) ^ ((k : ℝ) / 2)) *
          ((2 : ℝ) ^ 17 * d * (2 : ℝ) ^ (-(k : ℝ))) ^ (2 : ℕ) =
          (2 * ((2 : ℝ) ^ 17) ^ (2 : ℕ)) * d ^ (2 : ℕ) *
            ((2 : ℝ) ^ ((k : ℝ) / 2) * ((2 : ℝ) ^ (-(k : ℝ))) ^ (2 : ℕ)) := by
        ring
      _ = (2 : ℝ) ^ 35 * d ^ (2 : ℕ) * x ^ (6 : ℕ) := by
        rw [hscale]
        norm_num
  have hhighid :
      (2 : ℝ) ^ (-(k : ℝ) / 2) *
          ((2 : ℝ) ^ 6 * Real.sqrt d) ^ (2 : ℕ) =
        (2 : ℝ) ^ 12 * d * x ^ (2 : ℕ) := by
    have hd0 : 0 ≤ d := by linarith
    rw [show (2 : ℝ) ^ (-(k : ℝ) / 2) = x ^ (2 : ℕ) by
      dsimp [x]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring]
    calc
      x ^ (2 : ℕ) * ((2 : ℝ) ^ 6 * Real.sqrt d) ^ (2 : ℕ) =
          x ^ (2 : ℕ) * ((2 : ℝ) ^ 6) ^ (2 : ℕ) * (Real.sqrt d) ^ (2 : ℕ) := by
        ring
      _ = (2 : ℝ) ^ 12 * d * x ^ (2 : ℕ) := by
        rw [show (Real.sqrt d) ^ (2 : ℕ) = d by rw [Real.sq_sqrt hd0]]
        norm_num
        ring
  have htargetid :
      ((2 : ℝ) ^ 19 * d * (2 : ℝ) ^ (-(k : ℝ) / 4)) ^ (2 : ℕ) =
        (2 : ℝ) ^ 38 * d ^ (2 : ℕ) * x ^ (2 : ℕ) := by
    calc
      ((2 : ℝ) ^ 19 * d * (2 : ℝ) ^ (-(k : ℝ) / 4)) ^ (2 : ℕ) =
          ((2 : ℝ) ^ 19) ^ (2 : ℕ) * d ^ (2 : ℕ) *
            ((2 : ℝ) ^ (-(k : ℝ) / 4)) ^ (2 : ℕ) := by ring
      _ = (2 : ℝ) ^ 38 * d ^ (2 : ℕ) * x ^ (2 : ℕ) := by
        rw [show ((2 : ℝ) ^ 19) ^ (2 : ℕ) = (2 : ℝ) ^ 38 by norm_num]
  rw [hlowid, hhighid, htargetid]
  have hcoeff0 : 0 ≤ (2 : ℝ) ^ 35 * d ^ (2 : ℕ) := by positivity
  have hlowbound :
      (2 : ℝ) ^ 35 * d ^ (2 : ℕ) * x ^ (6 : ℕ) ≤
        (2 : ℝ) ^ 37 * d ^ (2 : ℕ) * x ^ (2 : ℕ) := by
    have h35_37 : (2 : ℝ) ^ 35 ≤ (2 : ℝ) ^ 37 := by norm_num
    calc
      (2 : ℝ) ^ 35 * d ^ (2 : ℕ) * x ^ (6 : ℕ) ≤
          (2 : ℝ) ^ 35 * d ^ (2 : ℕ) * x ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hxpow hcoeff0
      _ ≤ (2 : ℝ) ^ 37 * d ^ (2 : ℕ) * x ^ (2 : ℕ) := by
        calc
          (2 : ℝ) ^ 35 * d ^ (2 : ℕ) * x ^ (2 : ℕ) =
              (2 : ℝ) ^ 35 * (d ^ (2 : ℕ) * x ^ (2 : ℕ)) := by ring
          _ ≤ (2 : ℝ) ^ 37 * (d ^ (2 : ℕ) * x ^ (2 : ℕ)) :=
            mul_le_mul_of_nonneg_right h35_37 (by positivity)
          _ = (2 : ℝ) ^ 37 * d ^ (2 : ℕ) * x ^ (2 : ℕ) := by ring
  have hcoeffhigh : (2 : ℝ) ^ 12 * d ≤ (2 : ℝ) ^ 37 * d ^ (2 : ℕ) := by
    have hd0 : 0 ≤ d := by linarith
    nlinarith [sq_nonneg (d - 2)]
  have hhighbound :
      (2 : ℝ) ^ 12 * d * x ^ (2 : ℕ) ≤
        (2 : ℝ) ^ 37 * d ^ (2 : ℕ) * x ^ (2 : ℕ) := by
    exact mul_le_mul_of_nonneg_right hcoeffhigh (by positivity)
  calc
    (2 : ℝ) ^ 35 * d ^ (2 : ℕ) * x ^ (6 : ℕ) +
        (2 : ℝ) ^ 12 * d * x ^ (2 : ℕ) ≤
        (2 : ℝ) ^ 37 * d ^ (2 : ℕ) * x ^ (2 : ℕ) +
          (2 : ℝ) ^ 37 * d ^ (2 : ℕ) * x ^ (2 : ℕ) :=
      add_le_add hlowbound hhighbound
    _ = (2 : ℝ) ^ 38 * d ^ (2 : ℕ) * x ^ (2 : ℕ) := by
      norm_num
      ring

/--
This packages the low/high-frequency energy comparison for
`localizedNegativeSobolevDecay` into the required negative-Sobolev norm
bound.
-/
lemma aux_localizedNegativeSobolev_aggregate_energy
    (d : ℝ) (hd : 2 ≤ d) (k : ℕ) (G X L H : ℝ≥0∞) (hGtop : G ≠ ∞)
    (henergy : X ^ (2 : ℝ) ≤ L + H)
    (hlow : L ≤
      ENNReal.ofReal (2 * (2 : ℝ) ^ ((k : ℝ) / 2)) *
        (ENNReal.ofReal ((2 : ℝ) ^ 17 * d * (2 : ℝ) ^ (-(k : ℝ)) * G.toReal)) ^
          (2 : ℝ))
    (hhigh : H ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-(k : ℝ) / 2)) *
        (((2 : ℝ≥0∞) ^ 6 * G * ENNReal.ofReal (Real.sqrt d)) ^ (2 : ℝ))) :
    X ≤ ENNReal.ofReal ((2 : ℝ) ^ 19 * d * (2 : ℝ) ^ (-(k : ℝ) / 4)) * G := by
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  have hG : ENNReal.ofReal G.toReal = G := ENNReal.ofReal_toReal hGtop
  let A : ℝ := (2 : ℝ) ^ 17 * d * (2 : ℝ) ^ (-(k : ℝ))
  let R : ℝ := (2 : ℝ) ^ ((k : ℝ) / 2)
  let T : ℝ := (2 : ℝ) ^ (-(k : ℝ) / 4)
  let G0 : ℝ := G.toReal
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hR0 : 0 ≤ R := by
    dsimp [R]
    positivity
  have hT0 : 0 ≤ T := by
    dsimp [T]
    positivity
  have hG00 : 0 ≤ G0 := by
    dsimp [G0]
    positivity
  have hRinv : R ^ (-1 : ℝ) = (2 : ℝ) ^ (-(k : ℝ) / 2) := by
    dsimp [R]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hlowid :
      ENNReal.ofReal (2 * R) * (ENNReal.ofReal (A * G0)) ^ (2 : ℝ) =
        ENNReal.ofReal ((2 * R) * (A * G0) ^ (2 : ℕ)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hA0 hG00) (by norm_num),
      Real.rpow_two, ← ENNReal.ofReal_mul (by positivity)]
  have hhighid :
      ENNReal.ofReal (R ^ (-1 : ℝ)) *
        (((2 : ℝ≥0∞) ^ 6 * G * ENNReal.ofReal (Real.sqrt d)) ^ (2 : ℝ)) =
        ENNReal.ofReal (R ^ (-1 : ℝ) *
          ((2 : ℝ) ^ 6 * G0 * Real.sqrt d) ^ (2 : ℕ)) := by
    rw [← hG]
    norm_num
    change ENNReal.ofReal (R ^ (-1 : ℝ)) *
        ((64 : ℝ≥0∞) * ENNReal.ofReal G0 * ENNReal.ofReal (Real.sqrt d)) ^ (2 : ℕ) = _
    rw [show (64 : ℝ≥0∞) = ENNReal.ofReal (64 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 64 * G0),
      ← ENNReal.ofReal_pow (by positivity : 0 ≤ 64 * G0 * Real.sqrt d) 2,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ R ^ (-1 : ℝ))]
  have htargetid :
      (ENNReal.ofReal ((2 : ℝ) ^ 19 * d * T) * G) ^ (2 : ℝ) =
        ENNReal.ofReal (((2 : ℝ) ^ 19 * d * T * G0) ^ (2 : ℕ)) := by
    rw [← hG]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ 19 * d * T),
      ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ 19 * d * T * G0)
        (by norm_num),
      Real.rpow_two]
  have hscalar :
      (2 * R) * (A * G0) ^ (2 : ℕ) +
          R ^ (-1 : ℝ) * ((2 : ℝ) ^ 6 * G0 * Real.sqrt d) ^ (2 : ℕ) ≤
        ((2 : ℝ) ^ 19 * d * T * G0) ^ (2 : ℕ) := by
    have hbase := mul_le_mul_of_nonneg_right
      (aux_localizedNegativeSobolev_energy_coefficient_bound d hd k) (sq_nonneg G0)
    calc
      (2 * R) * (A * G0) ^ (2 : ℕ) +
          R ^ (-1 : ℝ) * ((2 : ℝ) ^ 6 * G0 * Real.sqrt d) ^ (2 : ℕ) =
          ((2 * (2 : ℝ) ^ ((k : ℝ) / 2)) *
              ((2 : ℝ) ^ 17 * d * (2 : ℝ) ^ (-(k : ℝ))) ^ (2 : ℕ) +
            (2 : ℝ) ^ (-(k : ℝ) / 2) *
              ((2 : ℝ) ^ 6 * Real.sqrt d) ^ (2 : ℕ)) * G0 ^ (2 : ℕ) := by
        rw [hRinv]
        dsimp [A, R]
        ring
      _ ≤ ((2 : ℝ) ^ 19 * d * (2 : ℝ) ^ (-(k : ℝ) / 4)) ^ (2 : ℕ) *
          G0 ^ (2 : ℕ) := hbase
      _ = ((2 : ℝ) ^ 19 * d * T * G0) ^ (2 : ℕ) := by
        dsimp [T]
        ring
  calc
    X ^ (2 : ℝ) ≤ L + H := henergy
    _ ≤ ENNReal.ofReal (2 * R) * (ENNReal.ofReal (A * G0)) ^ (2 : ℝ) +
          ENNReal.ofReal (R ^ (-1 : ℝ)) *
            (((2 : ℝ≥0∞) ^ 6 * G * ENNReal.ofReal (Real.sqrt d)) ^ (2 : ℝ)) :=
      add_le_add hlow (by simpa only [hRinv] using hhigh)
    _ = ENNReal.ofReal ((2 * R) * (A * G0) ^ (2 : ℕ) +
          R ^ (-1 : ℝ) * ((2 : ℝ) ^ 6 * G0 * Real.sqrt d) ^ (2 : ℕ)) := by
      rw [hlowid, hhighid, ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (((2 : ℝ) ^ 19 * d * T * G0) ^ (2 : ℕ)) :=
      ENNReal.ofReal_le_ofReal hscalar
    _ = (ENNReal.ofReal ((2 : ℝ) ^ 19 * d * T) * G) ^ (2 : ℝ) := htargetid.symm

/--
The localized Sobolev conclusion follows from its low-frequency pointwise
Fourier estimate and its high-frequency Plancherel estimate.  This combines
the two analytic parts of `localizedNegativeSobolevDecay`.
-/
lemma aux_localizedNegativeSobolev_from_low_high
    (a b : ℝ) (hab : a ≤ b) (k : ℕ) (h : ℝ → ℂ) (G : ℝ≥0∞)
    (hGtop : G ≠ ∞)
    (h1 : MemLp h (1 : ℝ≥0∞) volume)
    (h2 : MemLp h (2 : ℝ≥0∞) volume)
    (hpoint : ∀ ξ ∈ aux_sobolevDifference_lowFrequency
        ((2 : ℝ) ^ ((k : ℝ) / 2)),
      ‖𝓕 h ξ‖ ≤
        (2 : ℝ) ^ 17 * (b - a + 2) * (2 : ℝ) ^ (-(k : ℝ)) * G.toReal)
    (hhigh :
      (∫⁻ ξ : ℝ in aux_sobolevDifference_highFrequency
          ((2 : ℝ) ^ ((k : ℝ) / 2)),
        ‖(japaneseBracket ξ ^ (-(1 / 2 : ℝ))) •
          (Lp.fourierTransformₗᵢ ℝ ℂ h2.toLp) ξ‖ₑ ^ (2 : ℝ)) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (-(k : ℝ) / 2)) *
          (((2 : ℝ≥0∞) ^ 6 * G *
            ENNReal.ofReal (Real.sqrt (b - a + 2))) ^ (2 : ℝ))) :
    aux_sobolevNormRaw (1 / 2 : ℝ) h ≤
      ENNReal.ofReal ((2 : ℝ) ^ 19 * (b - a + 2) *
        (2 : ℝ) ^ (-(k : ℝ) / 4)) * G := by
  let R : ℝ := (2 : ℝ) ^ ((k : ℝ) / 2)
  let d : ℝ := b - a + 2
  let L : ℝ≥0∞ :=
    ∫⁻ ξ : ℝ in aux_sobolevDifference_lowFrequency R, ‖𝓕 h ξ‖ₑ ^ (2 : ℝ)
  let H : ℝ≥0∞ :=
    ∫⁻ ξ : ℝ in aux_sobolevDifference_highFrequency R,
      ‖(japaneseBracket ξ ^ (-(1 / 2 : ℝ))) •
        (Lp.fourierTransformₗᵢ ℝ ℂ h2.toLp) ξ‖ₑ ^ (2 : ℝ)
  have hd : 2 ≤ d := by
    dsimp [d]
    linarith
  have hlow : L ≤ ENNReal.ofReal (2 * R) *
      (ENNReal.ofReal ((2 : ℝ) ^ 17 * d * (2 : ℝ) ^ (-(k : ℝ)) * G.toReal)) ^
        (2 : ℝ) := by
    apply aux_lowFrequency_energy_le_of_norm_le R
      ((2 : ℝ) ^ 17 * d * ((2 : ℝ) ^ (-(k : ℝ))) * G.toReal)
    intro ξ hξ
    have hξ' : ξ ∈ aux_sobolevDifference_lowFrequency R := by
      simpa [aux_sobolevDifference_lowFrequency] using hξ
    simpa [R, d, aux_sobolevDifference_lowFrequency] using
      hpoint ξ (by simpa [R] using hξ')
  have henergy : aux_sobolevNormRaw (1 / 2 : ℝ) h ^ (2 : ℝ) ≤ L + H := by
    simpa [L, H] using
      (aux_sobolevDifference_sobolevNormRaw_high_low_split_le
        (1 / 2 : ℝ) R (by norm_num) h h1 h2)
  apply aux_localizedNegativeSobolev_aggregate_energy d hd k G
    (aux_sobolevNormRaw (1 / 2 : ℝ) h) L H hGtop henergy hlow
  simpa [H, R, d] using hhigh

/--
The exact source-facing right-hand side of `localizedNegativeSobolevDecay`
is the interval-length form of `aux_localizedNegativeSobolev_from_low_high`.
-/
lemma aux_localizedNegativeSobolev_from_low_high_exact
    (a b : ℝ) (hab : a ≤ b) (k : ℕ) (h : ℝ → ℂ) (G : ℝ≥0∞)
    (hGtop : G ≠ ∞)
    (h1 : MemLp h (1 : ℝ≥0∞) volume)
    (h2 : MemLp h (2 : ℝ≥0∞) volume)
    (hpoint : ∀ ξ ∈ aux_sobolevDifference_lowFrequency
        ((2 : ℝ) ^ ((k : ℝ) / 2)),
      ‖𝓕 h ξ‖ ≤
        (2 : ℝ) ^ 17 * (b - a + 2) * (2 : ℝ) ^ (-(k : ℝ)) * G.toReal)
    (hhigh :
      (∫⁻ ξ : ℝ in aux_sobolevDifference_highFrequency
          ((2 : ℝ) ^ ((k : ℝ) / 2)),
        ‖(japaneseBracket ξ ^ (-(1 / 2 : ℝ))) •
          (Lp.fourierTransformₗᵢ ℝ ℂ h2.toLp) ξ‖ₑ ^ (2 : ℝ)) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (-(k : ℝ) / 2)) *
          (((2 : ℝ≥0∞) ^ 6 * G *
            ENNReal.ofReal (Real.sqrt (b - a + 2))) ^ (2 : ℝ))) :
    aux_sobolevNormRaw (1 / 2 : ℝ) h ≤
      ENNReal.ofReal
          (C_localizedNegativeSobolevDecay (Set.Icc a b) *
            (2 : ℝ) ^ (-(k : ℝ) / 4)) * G := by
  have hmain := aux_localizedNegativeSobolev_from_low_high
    a b hab k h G hGtop h1 h2 hpoint hhigh
  have hlength : intervalLength (Set.Icc a b) = b - a := by
    simp [intervalLength, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rw [C_localizedNegativeSobolevDecay, hlength]
  have hshape :
      (2 : ℝ) ^ 19 * (b - a + 2) * (2 : ℝ) ^ (-(k : ℝ) / 4) =
        (2 : ℝ) ^ 19 * (2 + (b - a)) * (2 : ℝ) ^ (-(k : ℝ) / 4) := by
    ring
  rw [← hshape]
  exact hmain

/--
The localized dyadic input belongs to `L¹ ∩ L²`, and its high-frequency
negative-Sobolev energy at radius `2 ^ (k / 2)` has the endpoint decay used
by `aux_localizedNegativeSobolev_from_low_high_exact`.
-/
lemma aux_localizedNegativeSobolev_highFrequency
    (a b : ℝ) (hab : a ≤ b) (k : ℕ) (g : ℝ → ℂ)
    (hg_memLp : MemLp g (∞ : ℝ≥0∞) volume) :
    ∃ (_h1 : MemLp (fun x ↦ (spatialCutoff a b x : ℂ) * Q k g x)
          (1 : ℝ≥0∞) volume)
      (h2 : MemLp (fun x ↦ (spatialCutoff a b x : ℂ) * Q k g x)
          (2 : ℝ≥0∞) volume),
      (∫⁻ ξ : ℝ in aux_sobolevDifference_highFrequency
          ((2 : ℝ) ^ ((k : ℝ) / 2)),
        ‖(japaneseBracket ξ ^ (-(1 / 2 : ℝ))) •
          (Lp.fourierTransformₗᵢ ℝ ℂ h2.toLp) ξ‖ₑ ^ (2 : ℝ)) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (-(k : ℝ) / 2)) *
          (((2 : ℝ≥0∞) ^ 6 * eLpNorm g (∞ : ℝ≥0∞) volume *
            ENNReal.ofReal (Real.sqrt (b - a + 2))) ^ (2 : ℝ)) := by
  let κ : ℝ → ℂ :=
    aux_scaledInverseFourierKernel (fun ξ ↦ (annularCutoff ξ : ℂ)) k
  have hκlp : MemLp κ 1 volume := by
    simpa [κ] using aux_scaledAnnularInverseFourierKernel_memLp_one k
  have hκ : Integrable κ volume := memLp_one_iff_integrable.mp hκlp
  have hκnorm : eLpNorm κ 1 volume ≤ 2 ^ 6 := by
    simpa [κ] using aux_eLpNorm_scaledAnnularInverseFourierKernel_one_le k
  have hQbound : eLpNorm (Q k g) (∞ : ℝ≥0∞) volume ≤
      (2 : ℝ≥0∞) ^ 6 * eLpNorm g (∞ : ℝ≥0∞) volume := by
    change eLpNorm (aux_convolution κ g) (∞ : ℝ≥0∞) volume ≤ _
    exact aux_eLpNorm_aux_convolution_top_le_of_eLpNorm_one_le κ g hκ (2 ^ 6) hκnorm
  have hQmeas : AEStronglyMeasurable (Q k g) volume := by
    change AEStronglyMeasurable (aux_convolution κ g) volume
    change AEStronglyMeasurable (fun x : ℝ ↦ ∫ t : ℝ, κ t * g (x - t)) volume
    exact (hκlp.aestronglyMeasurable.convolution_integrand
      (ContinuousLinearMap.mul ℂ ℂ) hg_memLp.aestronglyMeasurable).integral_prod_right'
  have hQtop : (2 : ℝ≥0∞) ^ 6 * eLpNorm g (∞ : ℝ≥0∞) volume ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · norm_num
    · exact hg_memLp.eLpNorm_ne_top
  have hQmem : MemLp (Q k g) (∞ : ℝ≥0∞) volume := by
    refine memLp_top_of_bound hQmeas
      ((2 : ℝ≥0∞) ^ 6 * eLpNorm g (∞ : ℝ≥0∞) volume).toReal ?_
    filter_upwards [enorm_ae_le_eLpNormEssSup (Q k g) volume] with x hx
    have hx' : ENNReal.ofReal ‖Q k g x‖ ≤
        (2 : ℝ≥0∞) ^ 6 * eLpNorm g (∞ : ℝ≥0∞) volume := by
      rw [ofReal_norm]
      exact hx.trans hQbound
    exact (ENNReal.ofReal_le_iff_le_toReal hQtop).mp hx'
  have hQreal : (eLpNorm (Q k g) (∞ : ℝ≥0∞) volume).toReal ≤
      ((2 : ℝ≥0∞) ^ 6 * eLpNorm g (∞ : ℝ≥0∞) volume).toReal :=
    ENNReal.toReal_mono hQtop hQbound
  let h : ℝ → ℂ := fun x ↦ (spatialCutoff a b x : ℂ) * Q k g x
  have hcutmeas : AEStronglyMeasurable
      (fun x : ℝ ↦ (spatialCutoff a b x : ℂ)) volume := by
    apply (Complex.continuous_ofReal.comp ?_).aestronglyMeasurable
    unfold spatialCutoff
    exact (aux_continuous_smoothStep.comp (by fun_prop)).mul
      (aux_continuous_smoothStep.comp (by fun_prop))
  have hmeas : AEStronglyMeasurable h volume := hcutmeas.mul hQmeas
  have hbound : ∀ᵐ x ∂volume, ‖h x‖ ≤
      ((2 : ℝ≥0∞) ^ 6 * eLpNorm g (∞ : ℝ≥0∞) volume).toReal := by
    filter_upwards [aux_homogeneous_ae_norm_le_toReal (Q k g) hQmem] with x hx
    change ‖(spatialCutoff a b x : ℂ) * Q k g x‖ ≤ _
    rw [norm_mul]
    have hcut : ‖(spatialCutoff a b x : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (aux_spatialCutoff_pointwise _ _ _).1]
      exact (aux_spatialCutoff_pointwise _ _ _).2
    calc
      ‖(spatialCutoff a b x : ℂ)‖ * ‖Q k g x‖ ≤ 1 * ‖Q k g x‖ :=
        mul_le_mul_of_nonneg_right hcut (norm_nonneg _)
      _ ≤ _ := by simpa using hx.trans hQreal
  have hsupp : ∀ᵐ x ∂volume, x ∉ Set.Icc (a - 1) (b + 1) → h x = 0 := by
    filter_upwards with x hx
    have hcut : spatialCutoff a b x = 0 := by
      by_contra hne
      apply hx
      exact aux_spatialCutoff_tsupport (subset_tsupport _ hne)
    simp [h, hcut]
  have hIcompact : IsCompact (Set.Icc (a - 1) (b + 1)) := isCompact_Icc
  have h1 : MemLp h (1 : ℝ≥0∞) volume :=
    aux_memLp_of_ae_bound_of_ae_support h hmeas
      ((2 : ℝ≥0∞) ^ 6 * eLpNorm g (∞ : ℝ≥0∞) volume).toReal hbound
      (Set.Icc (a - 1) (b + 1)) measurableSet_Icc hIcompact.measure_lt_top hsupp 1
  have h2 : MemLp h (2 : ℝ≥0∞) volume :=
    aux_memLp_of_ae_bound_of_ae_support h hmeas
      ((2 : ℝ≥0∞) ^ 6 * eLpNorm g (∞ : ℝ≥0∞) volume).toReal hbound
      (Set.Icc (a - 1) (b + 1)) measurableSet_Icc hIcompact.measure_lt_top hsupp 2
  have hindicator : eLpNorm ((Set.Icc (a - 1) (b + 1)).indicator
      (fun _ : ℝ ↦ (1 : ℝ))) (2 : ℝ≥0∞) volume =
      ENNReal.ofReal (Real.sqrt (b - a + 2)) := by
    rw [eLpNorm_indicator_const measurableSet_Icc (by norm_num) (by norm_num)]
    have hvol : volume (Set.Icc (a - 1) (b + 1)) =
        ENNReal.ofReal (b - a + 2) := by
      rw [Real.volume_Icc]
      congr 1
      ring
    rw [hvol]
    have hlen : 0 ≤ b - a + 2 := by linarith
    norm_num
    rw [ENNReal.ofReal_rpow_of_nonneg hlen]
    · rw [← Real.sqrt_eq_rpow]
    · norm_num
  have hh2bound : eLpNorm h (2 : ℝ≥0∞) volume ≤
      ENNReal.ofReal (((2 : ℝ≥0∞) ^ 6 * eLpNorm g (∞ : ℝ≥0∞) volume).toReal) *
        ENNReal.ofReal (Real.sqrt (b - a + 2)) := by
    calc
      eLpNorm h (2 : ℝ≥0∞) volume ≤
          ENNReal.ofReal
              (((2 : ℝ≥0∞) ^ 6 * eLpNorm g (∞ : ℝ≥0∞) volume).toReal) *
            eLpNorm ((Set.Icc (a - 1) (b + 1)).indicator
              (fun _ : ℝ ↦ (1 : ℝ))) (2 : ℝ≥0∞) volume := by
        apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        filter_upwards [hbound, hsupp] with x hx hxs
        by_cases hxI : x ∈ Set.Icc (a - 1) (b + 1)
        · rw [Set.indicator_of_mem hxI, norm_one]
          simpa using hx
        · rw [Set.indicator_of_notMem hxI, norm_zero, hxs hxI, norm_zero]
          positivity
      _ = _ := by rw [hindicator]
  have hh2energy : (eLpNorm h (2 : ℝ≥0∞) volume) ^ (2 : ℝ) ≤
      (ENNReal.ofReal
          (((2 : ℝ≥0∞) ^ 6 * eLpNorm g (∞ : ℝ≥0∞) volume).toReal) *
        ENNReal.ofReal (Real.sqrt (b - a + 2))) ^ (2 : ℝ) :=
    ENNReal.rpow_le_rpow hh2bound (by norm_num)
  have hRpos : 0 < (2 : ℝ) ^ ((k : ℝ) / 2) := by
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hhigh := aux_sobolevDifference_highFrequency_sobolev_set_energy_le
    (1 / 2 : ℝ) ((2 : ℝ) ^ ((k : ℝ) / 2)) (by norm_num) hRpos h2.toLp
  have hLpeq : eLpNorm (h2.toLp : ℝ → ℂ) (2 : ℝ≥0∞) volume =
      eLpNorm h (2 : ℝ≥0∞) volume :=
    eLpNorm_congr_ae h2.coeFn_toLp
  have hhigh' :
      (∫⁻ ξ : ℝ in aux_sobolevDifference_highFrequency
          ((2 : ℝ) ^ ((k : ℝ) / 2)),
        ‖(japaneseBracket ξ ^ (-(1 / 2 : ℝ))) •
          (Lp.fourierTransformₗᵢ ℝ ℂ h2.toLp) ξ‖ₑ ^ (2 : ℝ)) ≤
        ENNReal.ofReal (((2 : ℝ) ^ ((k : ℝ) / 2)) ^ (-1 : ℝ)) *
          (eLpNorm h (2 : ℝ≥0∞) volume) ^ (2 : ℝ) := by
    calc
      _ ≤ ENNReal.ofReal (((2 : ℝ) ^ ((k : ℝ) / 2)) ^
          (-2 * (1 / 2 : ℝ))) *
          (eLpNorm (h2.toLp : ℝ → ℂ) (2 : ℝ≥0∞) volume) ^ (2 : ℝ) := hhigh
      _ = _ := by
        rw [hLpeq]
        congr 2
        norm_num
  have hRdecay : ((2 : ℝ) ^ ((k : ℝ) / 2)) ^ (-1 : ℝ) =
      (2 : ℝ) ^ (-(k : ℝ) / 2) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hM : ENNReal.ofReal
      (((2 : ℝ≥0∞) ^ 6 * eLpNorm g (∞ : ℝ≥0∞) volume).toReal) =
      (2 : ℝ≥0∞) ^ 6 * eLpNorm g (∞ : ℝ≥0∞) volume :=
    ENNReal.ofReal_toReal hQtop
  refine ⟨?_, ?_, ?_⟩
  · simpa [h] using h1
  · simpa [h] using h2
  · simpa only [hRdecay, hM] using
      hhigh'.trans (mul_le_mul_right hh2energy _)

/--
Let \(I\) be a compact interval, \(k\geq1\), and \(g\in L^\infty(\R)\).  Define
\[
C_{\ref{lem:localized-sobolev-decay},\,I}
:=
2^{19}(2+\lvert I\rvert).
\]
Then
\[
\hNorm{\rho_IQ_kg}{-1/2}
\leq
C_{\ref{lem:localized-sobolev-decay},\,I}
2^{-k/4}\lpNorm g\infty.
\]
-/
theorem localizedNegativeSobolevDecay
    (a b : ℝ) (hab : a ≤ b) (k : ℕ) (hk : 1 ≤ k)
    (g : ℝ → ℂ) (hg_memLp : MemLp g (∞ : ℝ≥0∞) volume) :
    aux_sobolevNormRaw (1 / 2 : ℝ)
        (fun x ↦ (spatialCutoff a b x : ℂ) * Q k g x) ≤
      ENNReal.ofReal
          (C_localizedNegativeSobolevDecay (Set.Icc a b) *
            (2 : ℝ) ^ (-(k : ℝ) / 4)) *
        eLpNorm g (∞ : ℝ≥0∞) volume := by
  rcases aux_localizedNegativeSobolev_highFrequency a b hab k g hg_memLp with
    ⟨h1, h2, hhigh⟩
  exact aux_localizedNegativeSobolev_from_low_high_exact
    a b hab k (fun x ↦ (spatialCutoff a b x : ℂ) * Q k g x)
    (eLpNorm g (∞ : ℝ≥0∞) volume) hg_memLp.eLpNorm_ne_top h1 h2
    (aux_localizedNegativeSobolev_lowFrequency_pointwise a b hab k hk g hg_memLp) hhigh

/-- The explicit constant in \(\label{prop:dyadic-linfty-decay}\), used by
`dyadicLInfinityDecay`:
\[
C_{\ref{prop:dyadic-linfty-decay},\,K,\chi}
:=
2^{13}\Ssize{A_0,A_1,A_2,J_\chi}{\chi}^{4},
\]
where the intervals are those of \(\label{def:main-interaction-data}\).
-/
def C_dyadicLInfinityDecay (a b : ℝ) (χ : ℝ → ℝ) : ℝ :=
  (2 : ℝ) ^ 13 *
    sizeParameter ![
      aux_mainInteractionA0 a b,
      aux_mainInteractionA1 a b χ,
      aux_mainInteractionA2 a b χ,
      aux_mainInteractionJ χ] χ ^ 4

/--
The final real-variable exponent arithmetic for `dyadicLInfinityDecay`.
It absorbs the normalized-smoothing exponents and the localized
negative-Sobolev gain into the stated dyadic decay.
-/
lemma aux_dyadicLInfinityDecay_numeric (S b₀ b₁ bg : ℝ) (k : ℕ) (hS : 1 ≤ S)
    (hb₀ : 0 ≤ b₀) (hb₁ : 0 ≤ b₁) (hbg : 0 < bg) :
    (2 : ℝ) ^ 6 * S ^ 3 * b₀ * b₁ *
        (((2 : ℝ) ^ 6 * bg) ^ (319 / (320 : ℝ))) *
          (((2 : ℝ) ^ 19 * S * (2 : ℝ) ^ (-(k : ℝ) / 4) * bg) ^
            (1 / (320 : ℝ))) ≤
      (2 : ℝ) ^ 13 * S ^ 4 *
        (2 : ℝ) ^ (-((2 : ℝ) ^ (-11 : ℝ)) * (k : ℝ)) * b₀ * b₁ * bg := by
  have hpow6 : ((2 : ℝ) ^ 6) ^ (319 / (320 : ℝ)) ≤ (2 : ℝ) ^ 6 := by
    have hpow : ((2 : ℝ) ^ 6) ^ (319 / (320 : ℝ)) =
        (2 : ℝ) ^ ((6 : ℝ) * (319 / (320 : ℝ))) := by
      rw [← Real.rpow_natCast]
      exact (Real.rpow_mul (by norm_num) 6 (319 / (320 : ℝ))).symm
    rw [hpow]
    have hle := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ))
      (y := (6 : ℝ) * (319 / (320 : ℝ))) (z := 6)
      (by norm_num) (by norm_num)
    simpa [Real.rpow_natCast] using hle
  have hpow19S : ((2 : ℝ) ^ 19 * S) ^ (1 / (320 : ℝ)) ≤ 2 * S := by
    rw [Real.mul_rpow (by positivity) (by linarith)]
    calc
      ((2 : ℝ) ^ 19) ^ (1 / (320 : ℝ)) * S ^ (1 / (320 : ℝ)) ≤
          2 * S ^ (1 / (320 : ℝ)) := by
        apply mul_le_mul
        · have hpow : ((2 : ℝ) ^ 19) ^ (1 / (320 : ℝ)) =
              (2 : ℝ) ^ ((19 : ℝ) * (1 / (320 : ℝ))) := by
            rw [← Real.rpow_natCast]
            exact (Real.rpow_mul (by norm_num) 19 (1 / (320 : ℝ))).symm
          rw [hpow]
          have hle := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ))
            (y := (19 : ℝ) * (1 / (320 : ℝ))) (z := 1)
            (by norm_num) (by norm_num)
          simpa using hle
        · exact le_rfl
        · positivity
        · positivity
      _ ≤ 2 * S := by
        gcongr
        have hle := Real.rpow_le_rpow_of_exponent_le (x := S)
          (y := 1 / (320 : ℝ)) (z := 1) hS (by norm_num)
        simpa using hle
  have hdecay : ((2 : ℝ) ^ (-(k : ℝ) / 4)) ^ (1 / (320 : ℝ)) ≤
      (2 : ℝ) ^ (-((2 : ℝ) ^ (-11 : ℝ)) * (k : ℝ)) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have htwo : (2 : ℝ) ^ (-11 : ℝ) = 1 / 2048 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [htwo]
    nlinarith
  have hfirst : (((2 : ℝ) ^ 6 * bg) ^ (319 / (320 : ℝ))) =
      ((2 : ℝ) ^ 6) ^ (319 / (320 : ℝ)) * bg ^ (319 / (320 : ℝ)) := by
    rw [Real.mul_rpow (by positivity) (le_of_lt hbg)]
  have hsecond : (((2 : ℝ) ^ 19 * S * (2 : ℝ) ^ (-(k : ℝ) / 4) * bg) ^
      (1 / (320 : ℝ))) =
      ((2 : ℝ) ^ 19 * S) ^ (1 / (320 : ℝ)) *
        ((2 : ℝ) ^ (-(k : ℝ) / 4)) ^ (1 / (320 : ℝ)) *
          bg ^ (1 / (320 : ℝ)) := by
    rw [show (2 : ℝ) ^ 19 * S * (2 : ℝ) ^ (-(k : ℝ) / 4) * bg =
        (((2 : ℝ) ^ 19 * S) * (2 : ℝ) ^ (-(k : ℝ) / 4)) * bg by ring,
      Real.mul_rpow (mul_nonneg (by positivity) (by positivity)) (le_of_lt hbg),
      Real.mul_rpow (by positivity) (by positivity)]
  calc
    (2 : ℝ) ^ 6 * S ^ 3 * b₀ * b₁ *
        (((2 : ℝ) ^ 6 * bg) ^ (319 / (320 : ℝ))) *
          (((2 : ℝ) ^ 19 * S * (2 : ℝ) ^ (-(k : ℝ) / 4) * bg) ^
            (1 / (320 : ℝ))) =
      (2 : ℝ) ^ 6 * S ^ 3 * b₀ * b₁ *
        (((2 : ℝ) ^ 6) ^ (319 / (320 : ℝ)) * bg ^ (319 / (320 : ℝ))) *
          (((2 : ℝ) ^ 19 * S) ^ (1 / (320 : ℝ)) *
            ((2 : ℝ) ^ (-(k : ℝ) / 4)) ^ (1 / (320 : ℝ)) *
            bg ^ (1 / (320 : ℝ))) := by rw [hfirst, hsecond]
    _ ≤ (2 : ℝ) ^ 6 * S ^ 3 * b₀ * b₁ *
        ((2 : ℝ) ^ 6 * bg ^ (319 / (320 : ℝ))) *
          ((2 * S) * (2 : ℝ) ^ (-((2 : ℝ) ^ (-11 : ℝ)) * (k : ℝ)) *
            bg ^ (1 / (320 : ℝ))) := by
        gcongr
    _ = (2 : ℝ) ^ 13 * S ^ 4 *
        (2 : ℝ) ^ (-((2 : ℝ) ^ (-11 : ℝ)) * (k : ℝ)) * b₀ * b₁ *
          (bg ^ (319 / (320 : ℝ)) * bg ^ (1 / (320 : ℝ))) := by ring
    _ = (2 : ℝ) ^ 13 * S ^ 4 *
        (2 : ℝ) ^ (-((2 : ℝ) ^ (-11 : ℝ)) * (k : ℝ)) * b₀ * b₁ * bg := by
        rw [← Real.rpow_add hbg]
        norm_num

/--
Let \(k\geq1\).  Define
\[
C_{\ref{prop:dyadic-linfty-decay},\,K,\chi}
:=
2^{13}\Ssize{A_0,A_1,A_2,J_\chi}{\chi}^{4},
\]
where the intervals are those of \(\label{def:main-interaction-data}\).  If
\(f_0\) is supported in \(K\) and \(f_0,f_1,g\in L^\infty(\R)\), then
\[
\Ichi(f_0,f_1,Q_kg)
\leq
C_{\ref{prop:dyadic-linfty-decay},\,K,\chi}
2^{-2^{-11}k}
\lpNorm{f_0}\infty\lpNorm{f_1}\infty\lpNorm g\infty.
\]
-/
theorem dyadicLInfinityDecay
    (a b : ℝ) (χ : ℝ → ℝ) (hab : a ≤ b)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (k : ℕ) (hk : 1 ≤ k)
    (f₀ f₁ g : ℝ → ℂ)
    (hf₀_memLp : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁_memLp : MemLp f₁ (∞ : ℝ≥0∞) volume)
    (hg_memLp : MemLp g (∞ : ℝ≥0∞) volume)
    (hf₀_support : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f₀ x = 0) :
    trilinearFormAbs χ f₀ f₁ (Q k g) ≤
      C_dyadicLInfinityDecay a b χ *
        (2 : ℝ) ^ (-((2 : ℝ) ^ (-11 : ℝ)) * (k : ℝ)) *
          (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
            (eLpNorm f₁ (∞ : ℝ≥0∞) volume).toReal *
              (eLpNorm g (∞ : ℝ≥0∞) volume).toReal := by
  let κ : ℝ → ℂ :=
    aux_scaledInverseFourierKernel (fun ξ ↦ (annularCutoff ξ : ℂ)) k
  have hκlp : MemLp κ 1 volume := by
    simpa [κ] using aux_scaledAnnularInverseFourierKernel_memLp_one k
  have hκ : Integrable κ volume := memLp_one_iff_integrable.mp hκlp
  have hκnorm : eLpNorm κ 1 volume ≤ 2 ^ 6 := by
    simpa [κ] using aux_eLpNorm_scaledAnnularInverseFourierKernel_one_le k
  have hQbound : eLpNorm (Q k g) (∞ : ℝ≥0∞) volume ≤
      (2 : ℝ≥0∞) ^ 6 * eLpNorm g (∞ : ℝ≥0∞) volume := by
    change eLpNorm (aux_convolution κ g) (∞ : ℝ≥0∞) volume ≤ _
    exact aux_eLpNorm_aux_convolution_top_le_of_eLpNorm_one_le κ g hκ (2 ^ 6) hκnorm
  have hQmeas : AEStronglyMeasurable (Q k g) volume := by
    change AEStronglyMeasurable (aux_convolution κ g) volume
    change AEStronglyMeasurable (fun x : ℝ ↦ ∫ t : ℝ, κ t * g (x - t)) volume
    exact (hκlp.aestronglyMeasurable.convolution_integrand
      (ContinuousLinearMap.mul ℂ ℂ) hg_memLp.aestronglyMeasurable).integral_prod_right'
  have hQtop : (2 : ℝ≥0∞) ^ 6 * eLpNorm g (∞ : ℝ≥0∞) volume ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · norm_num
    · exact hg_memLp.eLpNorm_ne_top
  have hQmem : MemLp (Q k g) (∞ : ℝ≥0∞) volume := by
    refine memLp_top_of_bound hQmeas
      ((2 : ℝ≥0∞) ^ 6 * eLpNorm g (∞ : ℝ≥0∞) volume).toReal ?_
    filter_upwards [enorm_ae_le_eLpNormEssSup (Q k g) volume] with x hx
    have hx' : ENNReal.ofReal ‖Q k g x‖ ≤
        (2 : ℝ≥0∞) ^ 6 * eLpNorm g (∞ : ℝ≥0∞) volume := by
      rw [ofReal_norm]
      exact hx.trans hQbound
    exact (ENNReal.ofReal_le_iff_le_toReal hQtop).mp hx'
  let F₁ : ℝ → ℂ := fun x ↦
    (spatialCutoff (a - supportRadius χ) (b + supportRadius χ) x : ℂ) * f₁ x
  let F₂ : ℝ → ℂ := fun x ↦
    (spatialCutoff a (b + supportRadius χ ^ 2) x : ℂ) * Q k g x
  have hcut_cont : ∀ u v : ℝ, Continuous (fun x : ℝ ↦ (spatialCutoff u v x : ℂ)) := by
    intro u v
    apply Complex.continuous_ofReal.comp
    unfold spatialCutoff
    apply (aux_continuous_smoothStep.comp ?_).mul
      (aux_continuous_smoothStep.comp ?_)
    · fun_prop
    · fun_prop
  have hF₁_memLp : MemLp F₁ (∞ : ℝ≥0∞) volume := by
    refine memLp_top_of_bound
      ((hcut_cont _ _).aestronglyMeasurable.mul hf₁_memLp.aestronglyMeasurable)
      (eLpNorm f₁ (∞ : ℝ≥0∞) volume).toReal ?_
    filter_upwards [aux_homogeneous_ae_norm_le_toReal f₁ hf₁_memLp] with x hx
    change ‖(spatialCutoff (a - supportRadius χ) (b + supportRadius χ) x : ℂ) * f₁ x‖ ≤ _
    rw [norm_mul]
    have hcut : ‖(spatialCutoff (a - supportRadius χ) (b + supportRadius χ) x : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (aux_spatialCutoff_pointwise _ _ _).1]
      exact (aux_spatialCutoff_pointwise _ _ _).2
    calc
      ‖(spatialCutoff (a - supportRadius χ) (b + supportRadius χ) x : ℂ)‖ * ‖f₁ x‖ ≤
          1 * ‖f₁ x‖ := mul_le_mul_of_nonneg_right hcut (norm_nonneg _)
      _ ≤ (eLpNorm f₁ (∞ : ℝ≥0∞) volume).toReal := by simpa using hx
  have hF₂_memLp : MemLp F₂ (∞ : ℝ≥0∞) volume := by
    refine memLp_top_of_bound
      ((hcut_cont _ _).aestronglyMeasurable.mul hQmem.aestronglyMeasurable)
      (eLpNorm (Q k g) (∞ : ℝ≥0∞) volume).toReal ?_
    filter_upwards [aux_homogeneous_ae_norm_le_toReal (Q k g) hQmem] with x hx
    change ‖(spatialCutoff a (b + supportRadius χ ^ 2) x : ℂ) * Q k g x‖ ≤ _
    rw [norm_mul]
    have hcut : ‖(spatialCutoff a (b + supportRadius χ ^ 2) x : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (aux_spatialCutoff_pointwise _ _ _).1]
      exact (aux_spatialCutoff_pointwise _ _ _).2
    calc
      ‖(spatialCutoff a (b + supportRadius χ ^ 2) x : ℂ)‖ * ‖Q k g x‖ ≤
          1 * ‖Q k g x‖ := mul_le_mul_of_nonneg_right hcut (norm_nonneg _)
      _ ≤ (eLpNorm (Q k g) (∞ : ℝ≥0∞) volume).toReal := by simpa using hx
  have hF₁bound : eLpNorm F₁ (∞ : ℝ≥0∞) volume ≤ eLpNorm f₁ (∞ : ℝ≥0∞) volume := by
    apply eLpNorm_mono_ae
    filter_upwards with x
    change ‖(spatialCutoff (a - supportRadius χ) (b + supportRadius χ) x : ℂ) * f₁ x‖ ≤ ‖f₁ x‖
    rw [norm_mul]
    have hcut : ‖(spatialCutoff (a - supportRadius χ) (b + supportRadius χ) x : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (aux_spatialCutoff_pointwise _ _ _).1]
      exact (aux_spatialCutoff_pointwise _ _ _).2
    calc
      ‖(spatialCutoff (a - supportRadius χ) (b + supportRadius χ) x : ℂ)‖ * ‖f₁ x‖ ≤
          1 * ‖f₁ x‖ := mul_le_mul_of_nonneg_right hcut (norm_nonneg _)
      _ = ‖f₁ x‖ := by ring
  have hF₂bound : eLpNorm F₂ (∞ : ℝ≥0∞) volume ≤
      (2 : ℝ≥0∞) ^ 6 * eLpNorm g (∞ : ℝ≥0∞) volume := by
    calc
      eLpNorm F₂ (∞ : ℝ≥0∞) volume ≤ eLpNorm (Q k g) (∞ : ℝ≥0∞) volume := by
        apply eLpNorm_mono_ae
        filter_upwards with x
        change ‖(spatialCutoff a (b + supportRadius χ ^ 2) x : ℂ) * Q k g x‖ ≤ ‖Q k g x‖
        rw [norm_mul]
        have hcut : ‖(spatialCutoff a (b + supportRadius χ ^ 2) x : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (aux_spatialCutoff_pointwise _ _ _).1]
          exact (aux_spatialCutoff_pointwise _ _ _).2
        calc
          ‖(spatialCutoff a (b + supportRadius χ ^ 2) x : ℂ)‖ * ‖Q k g x‖ ≤
              1 * ‖Q k g x‖ := mul_le_mul_of_nonneg_right hcut (norm_nonneg _)
          _ = ‖Q k g x‖ := by ring
      _ ≤ _ := hQbound
  rcases mainInteractionDataAdmissible a b χ hab hχ_smooth hχ_compact hχ_nonneg hχ_le_one
    with ⟨D, hD⟩
  have hDχ : D.χ = χ := congrArg aux_MainInteractionData.χ hD
  have hDA0 : D.A₀ = aux_mainInteractionA0 a b := congrArg aux_MainInteractionData.A₀ hD
  have hDA1 : D.A₁ = aux_mainInteractionA1 a b χ := congrArg aux_MainInteractionData.A₁ hD
  have hDA2 : D.A₂ = aux_mainInteractionA2 a b χ := congrArg aux_MainInteractionData.A₂ hD
  have hDJ : D.J = aux_mainInteractionJ χ := congrArg aux_MainInteractionData.J hD
  have hF₀support : ∀ᵐ x ∂volume, x ∉ D.A₀ → f₀ x = 0 := by
    rw [hDA0, aux_mainInteractionA0]
    filter_upwards [hf₀_support] with x hx hnot
    apply hx
    intro hxK
    apply hnot
    constructor <;> linarith [hxK.1, hxK.2]
  let R : ℝ := supportRadius χ
  have himage : ∀ p q r s : ℝ, p ≤ q → r ≤ s →
      Set.image2 (fun x y : ℝ ↦ x + y) (Set.Icc p q) (Set.Icc r s) =
        Set.Icc (p + r) (q + s) := by
    intro p q r s hpq hrs
    ext x
    constructor
    · rintro ⟨y, hy, z, hz, rfl⟩
      exact ⟨add_le_add hy.1 hz.1, add_le_add hy.2 hz.2⟩
    · intro hx
      rcases le_total x (p + s) with h | h
      · refine ⟨p, ⟨le_rfl, hpq⟩, x - p, ?_, by ring⟩
        constructor <;> linarith [hx.1]
      · refine ⟨x - s, ?_, s, ⟨hrs, le_rfl⟩, by ring⟩
        constructor <;> linarith [hx.2]
  have hR0 : 0 ≤ R := by
    exact zero_le_one.trans (by simpa [R] using aux_u3_one_le_supportRadius χ hχ_compact)
  have hA1 : aux_mainInteractionA1 a b χ = Set.Icc (a - R - 1) (b + R + 1) := by
    rw [aux_mainInteractionA1, aux_mainInteractionI1]
    rw [himage (a - R) (b + R) (-1) 1 (by linarith) (by norm_num)]
    congr 1
  have hA2 : aux_mainInteractionA2 a b χ = Set.Icc (a - 1) (b + R ^ 2 + 1) := by
    rw [aux_mainInteractionA2, aux_mainInteractionI2]
    rw [himage a (b + R ^ 2) (-1) 1 (by nlinarith [sq_nonneg R]) (by norm_num)]
    congr 1
  have hF₁support : ∀ᵐ x ∂volume, x ∉ D.A₁ → F₁ x = 0 := by
    rw [hDA1, hA1]
    filter_upwards with x hx
    have hcut : spatialCutoff (a - R) (b + R) x = 0 := by
      by_contra hne
      apply hx
      exact aux_spatialCutoff_tsupport (subset_tsupport _ hne)
    simp [F₁, R, hcut]
  have hF₂support : ∀ᵐ x ∂volume, x ∉ D.A₂ → F₂ x = 0 := by
    rw [hDA2, hA2]
    filter_upwards with x hx
    have hcut : spatialCutoff a (b + R ^ 2) x = 0 := by
      by_contra hne
      apply hx
      exact aux_spatialCutoff_tsupport (subset_tsupport _ hne)
    simp [F₂, R, hcut]
  have hhom := homogeneousNormalizedSmoothing D f₀ F₁ F₂
    hf₀_memLp hF₁_memLp hF₂_memLp hF₀support hF₁support hF₂support
  have hH := localizedNegativeSobolevDecay a (b + supportRadius χ ^ 2)
    (by nlinarith [sq_nonneg (supportRadius χ)]) k hk g hg_memLp
  have hlocal : trilinearFormAbs χ f₀ f₁ (Q k g) = trilinearFormAbs D.χ f₀ F₁ F₂ := by
    unfold trilinearFormAbs trilinearForm
    rw [hDχ]
    apply congrArg norm
    apply integral_congr_ae
    filter_upwards [hf₀_support] with x hx
    apply integral_congr_ae
    refine Filter.Eventually.of_forall ?_
    intro t
    by_cases hxK : x ∈ Set.Icc a b
    · by_cases hχt : χ t = 0
      · simp [F₁, F₂, hχt]
      · have ht_support : t ∈ Function.support χ := by
          rw [Function.mem_support]
          exact hχt
        have ht_radius : t ∈ Set.Ioc (-supportRadius χ) (supportRadius χ) :=
          aux_quadratic_support_subset_Ioc_radius χ hχ_compact ht_support
        have hrad : 0 ≤ supportRadius χ :=
          zero_le_one.trans (aux_u3_one_le_supportRadius χ hχ_compact)
        have hx1 : x + t ∈ Set.Icc (a - supportRadius χ) (b + supportRadius χ) := by
          rcases hxK with ⟨hxa, hxb⟩
          rcases ht_radius with ⟨htlo, hthi⟩
          constructor <;> linarith
        have hx2 : x + t ^ 2 ∈ Set.Icc a (b + supportRadius χ ^ 2) := by
          rcases hxK with ⟨hxa, hxb⟩
          rcases ht_radius with ⟨htlo, hthi⟩
          constructor
          · nlinarith [sq_nonneg t]
          · nlinarith
        have hcut1 : spatialCutoff (a - supportRadius χ) (b + supportRadius χ) (x + t) = 1 :=
          aux_spatialCutoff_one_on hx1
        have hcut2 : spatialCutoff a (b + supportRadius χ ^ 2) (x + t ^ 2) = 1 :=
          aux_spatialCutoff_one_on hx2
        simp [F₁, F₂, hcut1, hcut2]
    · have hxzero : f₀ x = 0 := hx hxK
      simp [F₁, F₂, hxzero]
  rw [hDχ, hDA0, hDA1, hDA2, hDJ] at hhom
  let S : ℝ := sizeParameter ![
    aux_mainInteractionA0 a b,
    aux_mainInteractionA1 a b χ,
    aux_mainInteractionA2 a b χ,
    aux_mainInteractionJ χ] χ
  have hStwo : 2 ≤ S := by
    simpa [S] using aux_two_le_sizeParameter_four
      (aux_mainInteractionA0 a b) (aux_mainInteractionA1 a b χ)
      (aux_mainInteractionA2 a b χ) (aux_mainInteractionJ χ) χ
  have hSone : 1 ≤ S := by linarith
  have hlen : 2 + intervalLength (Set.Icc a (b + supportRadius χ ^ 2)) ≤ S := by
    have h := aux_intervalLength_le_sizeParameter_four
      (aux_mainInteractionA0 a b) (aux_mainInteractionA1 a b χ)
      (aux_mainInteractionA2 a b χ) (aux_mainInteractionJ χ) χ (2 : Fin 4)
    have hab' : a ≤ b + supportRadius χ ^ 2 := by
      nlinarith [sq_nonneg (supportRadius χ)]
    have hadd := intervalAdd a (b + supportRadius χ ^ 2) (-1) 1 hab' (by norm_num)
    rw [aux_mainInteractionA2, aux_mainInteractionI2] at h
    change intervalLength (Set.image2 (fun x y : ℝ ↦ x + y)
      (Set.Icc a (b + supportRadius χ ^ 2)) (Set.Icc (-1 : ℝ) 1)) ≤
      sizeParameter ![
        aux_mainInteractionA0 a b,
        aux_mainInteractionA1 a b χ,
        Set.image2 (fun x y : ℝ ↦ x + y)
          (Set.Icc a (b + supportRadius χ ^ 2)) (Set.Icc (-1 : ℝ) 1),
        aux_mainInteractionJ χ] χ at h
    change 2 + intervalLength (Set.Icc a (b + supportRadius χ ^ 2)) ≤
      sizeParameter ![
        aux_mainInteractionA0 a b,
        aux_mainInteractionA1 a b χ,
        Set.image2 (fun x y : ℝ ↦ x + y)
          (Set.Icc a (b + supportRadius χ ^ 2)) (Set.Icc (-1 : ℝ) 1),
        aux_mainInteractionJ χ] χ
    have hI : intervalLength (Set.Icc a (b + supportRadius χ ^ 2)) =
        b + supportRadius χ ^ 2 - a := by
      simp [intervalLength, Real.volume_Icc, sub_nonneg.mpr hab']
    change intervalLength (Set.image2 (fun x y : ℝ ↦ x + y)
      (Set.Icc a (b + supportRadius χ ^ 2)) (Set.Icc (-1 : ℝ) 1)) =
        intervalLength (Set.Icc a (b + supportRadius χ ^ 2)) +
          intervalLength (Set.Icc (-1 : ℝ) 1) at hadd
    have hunit : intervalLength (Set.Icc (-1 : ℝ) 1) = 2 := by
      norm_num [intervalLength, Real.volume_Icc]
    rw [hI, hunit] at hadd
    rw [hI]
    linarith [h, hadd]
  let δ : ℝ := (2 : ℝ) ^ (-(k : ℝ) / 4)
  have hδpos : 0 < δ := by
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hH' : aux_sobolevNormRaw (1 / 2 : ℝ) F₂ ≤
      ENNReal.ofReal
          (C_localizedNegativeSobolevDecay (Set.Icc a (b + supportRadius χ ^ 2)) * δ) *
        eLpNorm g (∞ : ℝ≥0∞) volume := by
    simpa [F₂, δ] using hH
  have hHbound : aux_sobolevNormRaw (1 / 2 : ℝ) F₂ ≤
      ENNReal.ofReal ((2 : ℝ) ^ 19 * S * δ) *
        eLpNorm g (∞ : ℝ≥0∞) volume := by
    have hcoeff : C_localizedNegativeSobolevDecay
        (Set.Icc a (b + supportRadius χ ^ 2)) * δ ≤ (2 : ℝ) ^ 19 * S * δ := by
      unfold C_localizedNegativeSobolevDecay
      calc
        ((2 : ℝ) ^ 19 * (2 + intervalLength (Set.Icc a (b + supportRadius χ ^ 2))) * δ) ≤
            ((2 : ℝ) ^ 19 * S) * δ := by
          gcongr
        _ = (2 : ℝ) ^ 19 * S * δ := by ring
    exact hH'.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hcoeff) _)
  have hHtop : aux_sobolevNormRaw (1 / 2 : ℝ) F₂ ≠ ∞ := by
    apply ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg_memLp.eLpNorm_ne_top)
    exact hHbound
  have hS0 : 0 ≤ S := le_trans (by norm_num) hSone
  have hCeq : C_normalizedNonlinearSmoothing
      (aux_mainInteractionA0 a b) (aux_mainInteractionA1 a b χ)
      (aux_mainInteractionA2 a b χ) (aux_mainInteractionJ χ) χ =
      (2 : ℝ) ^ 6 * S ^ 3 := by
    simp [C_normalizedNonlinearSmoothing, S]
  rw [hCeq] at hhom
  have hC0 : 0 ≤ (2 : ℝ) ^ 6 * S ^ 3 := by
    exact mul_nonneg (by positivity) (pow_nonneg hS0 _)
  have hT0 : 0 ≤ trilinearFormAbs χ f₀ F₁ F₂ := by
    exact norm_nonneg _
  have hB0top : eLpNorm f₀ (∞ : ℝ≥0∞) volume ≠ ∞ :=
    hf₀_memLp.eLpNorm_ne_top
  have hB1top : eLpNorm F₁ (∞ : ℝ≥0∞) volume ≠ ∞ :=
    hF₁_memLp.eLpNorm_ne_top
  have hB2top : eLpNorm F₂ (∞ : ℝ≥0∞) volume ≠ ∞ :=
    hF₂_memLp.eLpNorm_ne_top
  have hRtop : ENNReal.ofReal ((2 : ℝ) ^ 6 * S ^ 3) *
      eLpNorm f₀ (∞ : ℝ≥0∞) volume * eLpNorm F₁ (∞ : ℝ≥0∞) volume *
        eLpNorm F₂ (∞ : ℝ≥0∞) volume ^ (319 / (320 : ℝ)) *
          aux_sobolevNormRaw (1 / 2 : ℝ) F₂ ^ (1 / (320 : ℝ)) ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top
          · exact ENNReal.ofReal_ne_top
          · exact hB0top
        · exact hB1top
      · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hB2top
    · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hHtop
  have hreal : trilinearFormAbs χ f₀ F₁ F₂ ≤
      (2 : ℝ) ^ 6 * S ^ 3 *
        (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
          (eLpNorm F₁ (∞ : ℝ≥0∞) volume).toReal *
            (eLpNorm F₂ (∞ : ℝ≥0∞) volume).toReal ^ (319 / (320 : ℝ)) *
              (aux_sobolevNormRaw (1 / 2 : ℝ) F₂).toReal ^ (1 / (320 : ℝ)) := by
    have h := ENNReal.toReal_mono hRtop hhom
    simpa only [ENNReal.toReal_ofReal hT0, ENNReal.toReal_ofReal hC0,
      ENNReal.toReal_mul, ← ENNReal.toReal_rpow] using h
  have hF₁real : (eLpNorm F₁ (∞ : ℝ≥0∞) volume).toReal ≤
      (eLpNorm f₁ (∞ : ℝ≥0∞) volume).toReal := by
    exact ENNReal.toReal_mono hf₁_memLp.eLpNorm_ne_top hF₁bound
  have hF₂real : (eLpNorm F₂ (∞ : ℝ≥0∞) volume).toReal ≤
      (2 : ℝ) ^ 6 * (eLpNorm g (∞ : ℝ≥0∞) volume).toReal := by
    have h := ENNReal.toReal_mono hQtop hF₂bound
    norm_num [ENNReal.toReal_mul] at h ⊢
    exact h
  have hcoeff0 : 0 ≤ (2 : ℝ) ^ 19 * S * δ := by
    exact mul_nonneg (mul_nonneg (by positivity) hS0) (le_of_lt hδpos)
  have hHreal : (aux_sobolevNormRaw (1 / 2 : ℝ) F₂).toReal ≤
      (2 : ℝ) ^ 19 * S * δ *
        (eLpNorm g (∞ : ℝ≥0∞) volume).toReal := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg_memLp.eLpNorm_ne_top) hHbound
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcoeff0] using h
  rw [hlocal, hDχ]
  by_cases hbgzero : (eLpNorm g (∞ : ℝ≥0∞) volume).toReal = 0
  · have hBgzero : eLpNorm g (∞ : ℝ≥0∞) volume = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).mp hbgzero with h | h
      · exact h
      · exact (hg_memLp.eLpNorm_ne_top h).elim
    have hB₂zero : eLpNorm F₂ (∞ : ℝ≥0∞) volume = 0 := by
      exact bot_unique (hF₂bound.trans (by simp [hBgzero]))
    have hformzero : trilinearFormAbs χ f₀ F₁ F₂ = 0 := by
      have hzero : ENNReal.ofReal (trilinearFormAbs χ f₀ F₁ F₂) = 0 := by
        apply bot_unique
        calc
          ENNReal.ofReal (trilinearFormAbs χ f₀ F₁ F₂) ≤
              ENNReal.ofReal ((2 : ℝ) ^ 6 * S ^ 3) *
                eLpNorm f₀ (∞ : ℝ≥0∞) volume * eLpNorm F₁ (∞ : ℝ≥0∞) volume *
                  eLpNorm F₂ (∞ : ℝ≥0∞) volume ^ (319 / (320 : ℝ)) *
                    aux_sobolevNormRaw (1 / 2 : ℝ) F₂ ^ (1 / (320 : ℝ)) := hhom
          _ = 0 := by simp [hB₂zero]
      exact le_antisymm (ENNReal.ofReal_eq_zero.mp hzero) hT0
    rw [hformzero, hbgzero]
    norm_num
  · have hbgpos : 0 < (eLpNorm g (∞ : ℝ≥0∞) volume).toReal :=
      lt_of_le_of_ne (ENNReal.toReal_nonneg) (Ne.symm hbgzero)
    have hF₂pow : (eLpNorm F₂ (∞ : ℝ≥0∞) volume).toReal ^
        (319 / (320 : ℝ)) ≤
        ((2 : ℝ) ^ 6 * (eLpNorm g (∞ : ℝ≥0∞) volume).toReal) ^
          (319 / (320 : ℝ)) :=
      Real.rpow_le_rpow ENNReal.toReal_nonneg hF₂real (by norm_num)
    have hHpow : (aux_sobolevNormRaw (1 / 2 : ℝ) F₂).toReal ^
        (1 / (320 : ℝ)) ≤
        ((2 : ℝ) ^ 19 * S * δ *
          (eLpNorm g (∞ : ℝ≥0∞) volume).toReal) ^ (1 / (320 : ℝ)) :=
      Real.rpow_le_rpow ENNReal.toReal_nonneg hHreal (by norm_num)
    have hmain : trilinearFormAbs χ f₀ F₁ F₂ ≤
        (2 : ℝ) ^ 6 * S ^ 3 *
          (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
            (eLpNorm f₁ (∞ : ℝ≥0∞) volume).toReal *
              (((2 : ℝ) ^ 6 * (eLpNorm g (∞ : ℝ≥0∞) volume).toReal) ^
                (319 / (320 : ℝ))) *
                (((2 : ℝ) ^ 19 * S * δ *
                  (eLpNorm g (∞ : ℝ≥0∞) volume).toReal) ^ (1 / (320 : ℝ))) := by
      calc
        trilinearFormAbs χ f₀ F₁ F₂ ≤
            (2 : ℝ) ^ 6 * S ^ 3 *
              (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
                (eLpNorm F₁ (∞ : ℝ≥0∞) volume).toReal *
                  (eLpNorm F₂ (∞ : ℝ≥0∞) volume).toReal ^ (319 / (320 : ℝ)) *
                    (aux_sobolevNormRaw (1 / 2 : ℝ) F₂).toReal ^ (1 / (320 : ℝ)) := hreal
        _ ≤ _ := by gcongr
    have hnumeric :
        (2 : ℝ) ^ 6 * S ^ 3 *
          (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
            (eLpNorm f₁ (∞ : ℝ≥0∞) volume).toReal *
              (((2 : ℝ) ^ 6 * (eLpNorm g (∞ : ℝ≥0∞) volume).toReal) ^
                (319 / (320 : ℝ))) *
                (((2 : ℝ) ^ 19 * S * δ *
                  (eLpNorm g (∞ : ℝ≥0∞) volume).toReal) ^ (1 / (320 : ℝ))) ≤
          (2 : ℝ) ^ 13 * S ^ 4 *
            (2 : ℝ) ^ (-((2 : ℝ) ^ (-11 : ℝ)) * (k : ℝ)) *
              (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
                (eLpNorm f₁ (∞ : ℝ≥0∞) volume).toReal *
                  (eLpNorm g (∞ : ℝ≥0∞) volume).toReal := by
      simpa [δ] using aux_dyadicLInfinityDecay_numeric S
        (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal
        (eLpNorm f₁ (∞ : ℝ≥0∞) volume).toReal
        (eLpNorm g (∞ : ℝ≥0∞) volume).toReal k hSone
        ENNReal.toReal_nonneg ENNReal.toReal_nonneg hbgpos
    calc
      trilinearFormAbs χ f₀ F₁ F₂ ≤ _ := hmain
      _ ≤ _ := hnumeric
      _ = C_dyadicLInfinityDecay a b χ *
          (2 : ℝ) ^ (-((2 : ℝ) ^ (-11 : ℝ)) * (k : ℝ)) *
            (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
              (eLpNorm f₁ (∞ : ℝ≥0∞) volume).toReal *
                (eLpNorm g (∞ : ℝ≥0∞) volume).toReal := by
          simp [C_dyadicLInfinityDecay, S]

end Auto
