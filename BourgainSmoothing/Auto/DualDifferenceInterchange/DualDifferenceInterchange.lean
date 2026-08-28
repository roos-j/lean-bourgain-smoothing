/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import BourgainSmoothing.Auto.GowersDifferencingAndU3Control.GowersDifferencingAndU3Control

/-!
# Dual difference interchange

Formalizations of the labeled estimates in the corresponding section of
`blueprint/blueprint.tex`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Real FourierTransform

namespace Auto

/-- For \(\label{lem:measurable-linearization}\), this upgrades the essential
supremum bound of a continuous function to a pointwise bound. It is used by
`measurableFourierSupremumLinearization`. -/
lemma aux_continuous_norm_le_eLpNorm_toReal
    (f : ℝ → ℂ) (hf : Continuous f)
    (hfin : eLpNorm f (∞ : ℝ≥0∞) volume < ∞) (x : ℝ) :
    ‖f x‖ ≤ (eLpNorm f (∞ : ℝ≥0∞) volume).toReal := by
  by_contra hx
  have hlt : (eLpNorm f (∞ : ℝ≥0∞) volume).toReal < ‖f x‖ := lt_of_not_ge hx
  let M : ℝ≥0∞ := eLpNorm f (∞ : ℝ≥0∞) volume
  have hMfin : M ≠ ∞ := by
    dsimp [M]
    exact hfin.ne
  let U : Set ℝ := {y | M.toReal < ‖f y‖}
  have hUopen : IsOpen U := by
    exact isOpen_Ioi.preimage hf.norm
  have hxU : x ∈ U := by
    exact hlt
  have hUsub : U ⊆ {y | eLpNormEssSup f volume < ‖f y‖ₑ} := by
    intro y hy
    change M.toReal < ‖f y‖ at hy
    have hM : M = eLpNormEssSup f volume := by
      dsimp [M]
      exact eLpNorm_exponent_top
    rw [← hM]
    change M < ‖f y‖ₑ
    have hypos : 0 < ‖f y‖ := by
      have hMnonneg : 0 ≤ M.toReal := ENNReal.toReal_nonneg
      linarith
    have hy' : ENNReal.ofReal M.toReal < ENNReal.ofReal ‖f y‖ :=
      (ENNReal.ofReal_lt_ofReal_iff hypos).mpr hy
    simpa only [ENNReal.ofReal_toReal hMfin, ofReal_norm] using hy'
  have hUzero : volume U = 0 := by
    apply measure_mono_null hUsub
    exact meas_eLpNormEssSup_lt
  exact (hUopen.measure_pos volume ⟨x, hxU⟩).ne' hUzero

/-- For \(\label{lem:measurable-linearization}\), this identifies the finite
Fourier \(L^\infty\)-norm with rational-frequency samples. It is used by
`measurableFourierSupremumLinearization`. -/
lemma aux_linf_eq_iSup_dense
    (q : ℕ → ℝ) (hq : DenseRange q)
    (f : ℝ → ℂ) (hf : Continuous f)
    (hfin : eLpNorm f (∞ : ℝ≥0∞) volume < ∞) :
    (eLpNorm f (∞ : ℝ≥0∞) volume).toReal = ⨆ m : ℕ, ‖f (q m)‖ := by
  let M : ℝ := (eLpNorm f (∞ : ℝ≥0∞) volume).toReal
  let F : ℝ → ℝ := fun x ↦ ‖f x‖
  have hpoint : ∀ x : ℝ, F x ≤ M := by
    intro x
    exact aux_continuous_norm_le_eLpNorm_toReal f hf hfin x
  have hFcont : Continuous F := hf.norm
  have hFbdd : BddAbove (Set.range F) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hpoint x
  have hqbdd : BddAbove (Set.range fun m : ℕ ↦ F (q m)) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨m, rfl⟩
    exact hpoint _
  have hM_le_full : M ≤ ⨆ x : ℝ, F x := by
    have hbound : eLpNorm f (∞ : ℝ≥0∞) volume ≤
        ENNReal.ofReal (⨆ x : ℝ, F x) := by
      rw [eLpNorm_exponent_top]
      apply eLpNormEssSup_le_of_ae_bound
      filter_upwards with x
      exact le_ciSup hFbdd x
    dsimp [M]
    have hsup0 : 0 ≤ ⨆ x : ℝ, F x := by
      exact (norm_nonneg _).trans (le_ciSup hFbdd 0)
    simpa [ENNReal.toReal_ofReal hsup0] using
      (ENNReal.toReal_mono (by simp) hbound)
  have hsub_le : (⨆ z : Set.range q, F z) ≤ ⨆ m : ℕ, F (q m) := by
    apply ciSup_le
    intro z
    rcases z.property with ⟨m, hm⟩
    simpa [hm] using le_ciSup hqbdd m
  have hdense : (⨆ z : Set.range q, F z) = ⨆ x : ℝ, F x :=
    hq.ciSup hFcont hFbdd
  apply le_antisymm
  · calc
      M ≤ ⨆ x : ℝ, F x := hM_le_full
      _ = ⨆ z : Set.range q, F z := hdense.symm
      _ ≤ ⨆ m : ℕ, F (q m) := hsub_le
  · exact ciSup_le fun m ↦ hpoint _

/-- For \(\label{lem:measurable-linearization}\), this supplies measurable
Fourier evaluation for a jointly measurable family. It is used by
`measurableFourierSupremumLinearization`. -/
lemma aux_fourier_evaluation_measurable
    (g : ℝ → ℝ → ℂ) (hg : Measurable (Function.uncurry g)) (r : ℝ) :
    Measurable (fun h : ℝ ↦ 𝓕 (g h) r) := by
  have hphase : Measurable (fun z : ℝ × ℝ ↦
      (𝐞 (-inner ℝ z.2 r) : ℂ)) := by
    fun_prop
  have hprod : StronglyMeasurable (fun z : ℝ × ℝ ↦
      (𝐞 (-inner ℝ z.2 r) : ℂ) • g z.1 z.2) :=
    hphase.stronglyMeasurable.smul hg.stronglyMeasurable
  have hformula : (fun h : ℝ ↦ 𝓕 (g h) r) =
      fun h : ℝ ↦ ∫ x : ℝ, (𝐞 (-inner ℝ x r) : ℂ) • g h x := by
    funext h
    exact Real.fourier_eq (g h) r
  rw [hformula]
  exact hprod.integral_prod_right'.measurable

/-- For \(\label{thm:dual-difference-interchange}\), this supplies
measurable Fourier evaluation at a measurable variable frequency.  It is
used by `dualDifferenceInterchange`. -/
lemma aux_fourier_evaluation_measurable_comp
    (g : ℝ → ℝ → ℂ) (hg : Measurable (Function.uncurry g))
    (φ : ℝ → ℝ) (hφ : Measurable φ) :
    Measurable (fun h : ℝ ↦ 𝓕 (g h) (φ h)) := by
  have hphase : Measurable (fun z : ℝ × ℝ ↦
      (𝐞 (-inner ℝ z.2 (φ z.1)) : ℂ)) := by
    fun_prop
  have hprod : StronglyMeasurable (fun z : ℝ × ℝ ↦
      (𝐞 (-inner ℝ z.2 (φ z.1)) : ℂ) • g z.1 z.2) :=
    hphase.stronglyMeasurable.smul hg.stronglyMeasurable
  have hformula : (fun h : ℝ ↦ 𝓕 (g h) (φ h)) =
      fun h : ℝ ↦ ∫ x : ℝ, (𝐞 (-inner ℝ x (φ h)) : ℂ) • g h x := by
    funext h
    exact Real.fourier_eq (g h) (φ h)
  rw [hformula]
  exact hprod.integral_prod_right'.measurable

/--
Let $(g_h)_{h\in\R}$ be a jointly measurable family of $L^1$ functions, each
supported in a fixed compact interval. Suppose
\[
\int_\R\lpNorm{\FT{g_h}}\infty\dd h<\infty.
\]
For every $n\geq1$, there exists a measurable $\phi_n:\R\to\R$ such that
\[
\int_\R|\FT{g_h}(\phi_n(h))|\dd h
\geq
\int_\R\lpNorm{\FT{g_h}}\infty\dd h-\frac1n.
\]
-/
theorem measurableFourierSupremumLinearization
    (A : Set ℝ) (hA : ∃ a b : ℝ, a ≤ b ∧ A = Set.Icc a b)
    (g : ℝ → ℝ → ℂ)
    (hg_measurable : Measurable (Function.uncurry g))
    (hg_integrable : ∀ h : ℝ, Integrable (g h))
    (hg_support : ∀ h : ℝ, ∀ᵐ x ∂volume, x ∉ A → g h x = 0)
    (hg_fourier_integrable :
      Integrable (fun h : ℝ ↦ (eLpNorm (𝓕 (g h)) (∞ : ℝ≥0∞) volume).toReal))
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ φ : ℝ → ℝ, Measurable φ ∧
      ∫ h : ℝ, ‖𝓕 (g h) (φ h)‖ ≥
        (∫ h : ℝ, (eLpNorm (𝓕 (g h)) (∞ : ℝ≥0∞) volume).toReal) - 1 / (n : ℝ) := by
  classical
  obtain ⟨qrat, hqrat⟩ := exists_surjective_nat ℚ
  let q : ℕ → ℝ := fun m ↦ (qrat m : ℝ)
  have hq : DenseRange q := by
    have hrange : Set.range q = Set.range ((↑) : ℚ → ℝ) := by
      apply Set.Subset.antisymm
      · rintro x ⟨m, rfl⟩
        exact ⟨qrat m, rfl⟩
      · rintro x ⟨r, rfl⟩
        rcases hqrat r with ⟨m, hm⟩
        exact ⟨m, by simp [q, hm]⟩
    change Dense (Set.range q)
    rw [hrange]
    exact Rat.denseRange_cast
  let s : ℝ → ℝ := fun h ↦
    (eLpNorm (𝓕 (g h)) (∞ : ℝ≥0∞) volume).toReal
  let v : ℕ → ℝ → ℝ := fun m h ↦ ‖𝓕 (g h) (q m)‖
  have hfourierCont : ∀ h : ℝ, Continuous (𝓕 (g h)) := by
    intro h
    exact VectorFourier.fourierIntegral_continuous (e := 𝐞) (μ := volume)
      (L := innerₗ ℝ) Real.continuous_fourierChar (by fun_prop) (hg_integrable h)
  have hfourierFin : ∀ h : ℝ, eLpNorm (𝓕 (g h)) (∞ : ℝ≥0∞) volume < ∞ := by
    intro h
    exact (aux_eLpNorm_fourier_le_integral_norm (g h)).trans_lt ENNReal.ofReal_lt_top
  have hv_meas : ∀ m : ℕ, Measurable (v m) := by
    intro m
    dsimp [v]
    exact (aux_fourier_evaluation_measurable g hg_measurable (q m)).norm
  have hs_eq : ∀ h : ℝ, s h = ⨆ m : ℕ, v m h := by
    intro h
    dsimp [s, v]
    exact aux_linf_eq_iSup_dense q hq (𝓕 (g h))
      (hfourierCont h) (hfourierFin h)
  have hs_meas : Measurable s := by
    have hsup : Measurable (fun h : ℝ ↦ ⨆ m : ℕ, v m h) := Measurable.iSup hv_meas
    convert hsup using 1
    funext h
    exact hs_eq h
  let δ : ℝ → ℝ := fun h ↦
    (1 / (n : ℝ) * π⁻¹) * (1 + h ^ (2 : ℕ))⁻¹
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hδ_pos : ∀ h : ℝ, 0 < δ h := by
    intro h
    dsimp [δ]
    positivity
  have hδ_meas : Measurable δ := by
    dsimp [δ]
    fun_prop
  have hδ_int : Integrable δ volume := by
    dsimp [δ]
    exact integrable_inv_one_add_sq.const_mul _
  have hδ_integral : ∫ h : ℝ, δ h = 1 / (n : ℝ) := by
    dsimp [δ]
    rw [integral_const_mul, integral_univ_inv_one_add_sq]
    field_simp [Real.pi_ne_zero, hn_pos.ne']
  have hchoice : ∀ h : ℝ, ∃ m : ℕ, s h - δ h ≤ v m h := by
    intro h
    by_contra hnone
    push Not at hnone
    have hsup : (⨆ m : ℕ, v m h) ≤ s h - δ h :=
      ciSup_le fun m ↦ (hnone m).le
    rw [← hs_eq h] at hsup
    linarith [hδ_pos h]
  have hP_meas : ∀ m : ℕ, MeasurableSet {h : ℝ | s h - δ h ≤ v m h} := by
    intro m
    exact measurableSet_le (hs_meas.sub hδ_meas) (hv_meas m)
  let k : ℝ → ℕ := fun h ↦ Nat.find (hchoice h)
  have hkset : ∀ m : ℕ, MeasurableSet {h : ℝ | k h = m} := by
    intro m
    have heq : {h : ℝ | k h = m} =
        {h : ℝ | s h - δ h ≤ v m h ∧ ∀ r < m, ¬ s h - δ h ≤ v r h} := by
      ext h
      change Nat.find (hchoice h) = m ↔ _
      exact Nat.find_eq_iff (hchoice h)
    rw [heq]
    refine (hP_meas m).inter ?_
    change MeasurableSet {h : ℝ | ∀ r < m, ¬ (s h - δ h ≤ v r h)}
    have hinter :
        {h : ℝ | ∀ r < m, ¬ (s h - δ h ≤ v r h)} =
          ⋂ r ∈ Set.Iio m, {h : ℝ | ¬ (s h - δ h ≤ v r h)} := by
      ext h
      simp
    rw [hinter]
    exact MeasurableSet.biInter (Set.to_countable _) fun r _ ↦ (hP_meas r).compl
  have hk_meas : Measurable k := by
    apply measurable_to_nat
    intro h
    change MeasurableSet {x : ℝ | k x = k h}
    exact hkset (k h)
  let φ : ℝ → ℝ := fun h ↦ q (k h)
  have hφ_meas : Measurable φ := by
    dsimp [φ]
    change Measurable (q ∘ k)
    exact measurable_from_nat.comp hk_meas
  let selected : ℝ → ℝ := fun h ↦ ‖𝓕 (g h) (φ h)‖
  have hselected_meas : Measurable selected := by
    have hjoint : Measurable (fun z : ℕ × ℝ ↦ v z.1 z.2) :=
      measurable_from_prod_countable_right fun m ↦ hv_meas m
    simpa [selected, φ, v, Function.comp_def] using
      hjoint.comp (hk_meas.prodMk measurable_id)
  have hselected_le : ∀ h : ℝ, selected h ≤ s h := by
    intro h
    dsimp [selected, φ, s]
    exact aux_continuous_norm_le_eLpNorm_toReal (𝓕 (g h))
      (hfourierCont h) (hfourierFin h) (q (k h))
  have hselected_int : Integrable selected volume := by
    apply hg_fourier_integrable.mono' hselected_meas.aestronglyMeasurable
    filter_upwards with h
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hselected_le h
  have hpointwise : ∀ h : ℝ, s h ≤ selected h + δ h := by
    intro h
    have hfound : s h - δ h ≤ v (k h) h := Nat.find_spec (hchoice h)
    change s h - δ h ≤ selected h at hfound
    linarith
  have hint : ∫ h : ℝ, s h ≤ ∫ h : ℝ, selected h + δ h :=
    integral_mono hg_fourier_integrable (hselected_int.add hδ_int) hpointwise
  rw [integral_add hselected_int hδ_int, hδ_integral] at hint
  refine ⟨φ, hφ_meas, ?_⟩
  have hfinal : (∫ h : ℝ, s h) - 1 / (n : ℝ) ≤ ∫ h : ℝ, selected h :=
    (sub_le_iff_le_add).mpr (by simpa [add_comm] using hint)
  simpa only [selected, s] using hfinal

/-- For \(\label{thm:dual-difference-interchange}\), this is the measurable
unimodular-or-zero phase used to remove an absolute value in
`dualDifferenceInterchange`. -/
lemma aux_phase_measurable (z : ℝ → ℂ) (hz : Measurable z) :
    Measurable (fun h : ℝ ↦ if z h = 0 then 0 else star (z h) / (‖z h‖ : ℂ)) := by
  have hzero : MeasurableSet {h : ℝ | z h = 0} := measurableSet_eq_fun hz measurable_const
  have hstar : Measurable (fun h : ℝ ↦ star (z h)) := continuous_star.measurable.comp hz
  have hnorm : Measurable (fun h : ℝ ↦ (‖z h‖ : ℂ)) := Complex.measurable_ofReal.comp hz.norm
  exact Measurable.ite hzero measurable_const (hstar.div hnorm)

/-- For \(\label{thm:dual-difference-interchange}\), this is the pointwise
phase identity used to remove the selected Fourier absolute value in
`dualDifferenceInterchange`. -/
lemma aux_mul_phase_eq_norm (z : ℂ) :
    z * (if z = 0 then 0 else star z / (‖z‖ : ℂ)) = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [if_neg hz]
    calc
      z * (star z / (‖z‖ : ℂ)) = (z * star z) / (‖z‖ : ℂ) := by ring
      _ = (‖z‖ : ℂ) ^ (2 : ℕ) / (‖z‖ : ℂ) := by
        change z * (starRingEnd ℂ z) / (‖z‖ : ℂ) = _
        rw [RCLike.mul_conj]
        rfl
      _ = (‖z‖ : ℂ) := by field_simp [norm_ne_zero_iff.mpr hz]

/-- For \(\label{thm:dual-difference-interchange}\), this integrates the
pointwise phase identity used by `dualDifferenceInterchange`. -/
lemma aux_phase_integral_eq (z : ℝ → ℂ) :
    ∫ h : ℝ, z h * (if z h = 0 then 0 else star (z h) / (‖z h‖ : ℂ)) =
      ∫ h : ℝ, (‖z h‖ : ℂ) := by
  apply integral_congr_ae
  filter_upwards with h
  exact aux_mul_phase_eq_norm (z h)

/-- For \(\label{thm:dual-difference-interchange}\), this turns the phase
pairing into the integral of the selected Fourier absolute values.  It is
used by `dualDifferenceInterchange`. -/
lemma aux_norm_phase_integral_eq_integral_norm (z : ℝ → ℂ) :
    ‖∫ h : ℝ, z h * (if z h = 0 then 0 else star (z h) / (‖z h‖ : ℂ))‖ =
      ∫ h : ℝ, ‖z h‖ := by
  let I : ℝ := ∫ h : ℝ, ‖z h‖
  have hcast : (∫ h : ℝ, (‖z h‖ : ℂ)) = (I : ℂ) :=
    integral_ofReal (f := fun h : ℝ ↦ ‖z h‖)
  calc
    ‖∫ h : ℝ, z h * (if z h = 0 then 0 else star (z h) / (‖z h‖ : ℂ))‖ =
        ‖∫ h : ℝ, (‖z h‖ : ℂ)‖ := congrArg norm (aux_phase_integral_eq z)
    _ = ‖(I : ℂ)‖ := congrArg norm hcast
    _ = I := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (integral_nonneg fun h ↦ norm_nonneg (z h))
    _ = ∫ h : ℝ, ‖z h‖ := rfl

/-- For \(\label{thm:dual-difference-interchange}\), this bounds the
phase factor used by `dualDifferenceInterchange`. -/
lemma aux_norm_phase_le_one (z : ℂ) :
    ‖if z = 0 then 0 else star z / (‖z‖ : ℂ)‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [if_neg hz, norm_div, norm_star, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
    field_simp [norm_ne_zero_iff.mpr hz]
    exact le_rfl

/-- For \(\label{thm:dual-difference-interchange}\), this rewrites a raw
Fourier value at a negative frequency as the positive exponential integral
used by `dualDifferenceInterchange`. -/
lemma aux_fourier_neg_eq_exponential_integral (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 f (-ξ) = ∫ x : ℝ, f x * exponential (x * ξ) := by
  rw [Real.fourier_real_eq]
  apply integral_congr_ae
  filter_upwards with x
  rw [Circle.smul_def, Real.fourierChar_apply]
  simp only [mul_neg, neg_neg]
  simp [exponential]
  ring

/-- The compactly supported space--time kernel underlying
\(\label{thm:dual-difference-interchange}\).  It is auxiliary bookkeeping
for `dualDifferenceInterchange`. -/
def aux_dualKernel (Ft : ℝ → ℝ → ℂ) (χ : ℝ → ℝ) : ℝ → ℝ → ℂ :=
  fun x t ↦ Ft t x * (χ t : ℂ)

/-- For \(\label{thm:dual-difference-interchange}\), this establishes the
measurability, one-bound, and compact product support of `aux_dualKernel`.
It is used by `dualDifferenceInterchange`. -/
lemma aux_dualKernel_properties
    (A J : Set ℝ) (hAmeas : MeasurableSet A)
    (Ft : ℝ → ℝ → ℂ)
    (hFt_measurable : Measurable (Function.uncurry Ft))
    (hFt_one_bounded : ∀ t : ℝ, ∀ᵐ x ∂volume, ‖Ft t x‖ ≤ 1)
    (hFt_support : ∀ t : ℝ, ∀ᵐ x ∂volume, x ∉ A → Ft t x = 0)
    (χ : ℝ → ℝ)
    (hχ_measurable : Measurable χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t)
    (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (hχ_support : ∀ᵐ t ∂volume, t ∉ J → χ t = 0) :
    StronglyMeasurable (Function.uncurry (aux_dualKernel Ft χ)) ∧
      (∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖aux_dualKernel Ft χ z.1 z.2‖ ≤ 1) ∧
      (∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
        z ∉ A ×ˢ J → aux_dualKernel Ft χ z.1 z.2 = 0) := by
  have hQmeas : Measurable (Function.uncurry (aux_dualKernel Ft χ)) := by
    change Measurable (fun z : ℝ × ℝ ↦ Ft z.2 z.1 * (χ z.2 : ℂ))
    exact (hFt_measurable.comp measurable_swap).mul
      (Complex.continuous_ofReal.measurable.comp (hχ_measurable.comp measurable_snd))
  have hset : MeasurableSet {z : ℝ × ℝ | ‖Ft z.1 z.2‖ ≤ 1} :=
    measurableSet_le hFt_measurable.norm measurable_const
  have hboundOrig : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖Ft z.1 z.2‖ ≤ 1 := by
    rw [Measure.ae_prod_iff_ae_ae hset]
    exact Filter.Eventually.of_forall hFt_one_bounded
  have hbound : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      ‖aux_dualKernel Ft χ z.1 z.2‖ ≤ 1 := by
    have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hboundOrig
    filter_upwards [hswap] with z hz
    change ‖Ft z.2 z.1 * (χ z.2 : ℂ)‖ ≤ 1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ_nonneg _)]
    calc
      ‖Ft z.2 z.1‖ * χ z.2 ≤ 1 * 1 :=
        mul_le_mul hz (hχ_le_one _) (hχ_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hsuppSet : MeasurableSet {z : ℝ × ℝ | z.2 ∉ A → Ft z.1 z.2 = 0} := by
    exact (hAmeas.compl.preimage measurable_snd).imp
      ((measurableSet_singleton (0 : ℂ)).preimage hFt_measurable)
  have hsuppOrig : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z.2 ∉ A → Ft z.1 z.2 = 0 := by
    rw [Measure.ae_prod_iff_ae_ae hsuppSet]
    exact Filter.Eventually.of_forall hFt_support
  have hFtsupport : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z.1 ∉ A → aux_dualKernel Ft χ z.1 z.2 = 0 := by
    have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hsuppOrig
    filter_upwards [hswap] with z hz hx
    change Ft z.2 z.1 * (χ z.2 : ℂ) = 0
    apply mul_eq_zero_of_left
    simpa [Prod.swap] using hz hx
  have hχprod : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z.2 ∉ J → χ z.2 = 0 := by
    exact Measure.quasiMeasurePreserving_snd.ae hχ_support
  have hsupp : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∉ A ×ˢ J → aux_dualKernel Ft χ z.1 z.2 = 0 := by
    filter_upwards [hFtsupport, hχprod] with z hzF hzχ hzoutside
    by_cases hx : z.1 ∈ A
    · by_cases ht : z.2 ∈ J
      · exact False.elim (hzoutside ⟨hx, ht⟩)
      · change Ft z.2 z.1 * (χ z.2 : ℂ) = 0
        simp [hzχ ht]
    · exact hzF hx
  exact ⟨hQmeas.stronglyMeasurable, hbound, hsupp⟩

/-- For \(\label{thm:dual-difference-interchange}\), this records all
basic properties of a one-bounded compactly supported time integral.  It is
used to construct the averaged function in `dualDifferenceInterchange`. -/
lemma aux_timeIntegral_properties_compactSupport
    (X J : Set ℝ) (hX : IsCompact X) (hJ : IsCompact J) (Q : ℝ → ℝ → ℂ)
    (hQmeas : StronglyMeasurable (Function.uncurry Q))
    (hQbound : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖Q z.1 z.2‖ ≤ 1)
    (hQsupport : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∉ X ×ˢ J → Q z.1 z.2 = 0) :
    Measurable (fun x : ℝ ↦ ∫ t : ℝ, Q x t) ∧
      (∀ᵐ x : ℝ ∂volume, ‖∫ t : ℝ, Q x t‖ ≤ volume.real J) ∧
      (∀ᵐ x : ℝ ∂volume, x ∉ X → (∫ t : ℝ, Q x t) = 0) ∧
      MemLp (fun x : ℝ ↦ ∫ t : ℝ, Q x t) (1 : ℝ≥0∞) volume ∧
      MemLp (fun x : ℝ ↦ ∫ t : ℝ, Q x t) (2 : ℝ≥0∞) volume := by
  let T : Set (ℝ × ℝ) := X ×ˢ J
  have hTmeas : MeasurableSet T := hX.isClosed.measurableSet.prod hJ.isClosed.measurableSet
  have hTfinite : (volume.prod volume) T < ∞ := (hX.prod hJ).measure_lt_top
  have hQmem : MemLp (Function.uncurry Q) 1 (volume.prod volume) :=
    aux_memLp_of_ae_bound_of_ae_support _ hQmeas.aestronglyMeasurable 1 hQbound T hTmeas
      hTfinite hQsupport 1
  have hQint : Integrable (Function.uncurry Q) (volume.prod volume) :=
    memLp_one_iff_integrable.mp hQmem
  have hsections : ∀ᵐ x : ℝ ∂volume, Integrable (Q x) volume := hQint.prod_right_ae
  have hboundSections : ∀ᵐ x : ℝ ∂volume, ∀ᵐ t : ℝ ∂volume, ‖Q x t‖ ≤ 1 :=
    Measure.ae_ae_of_ae_prod hQbound
  have hsuppSections : ∀ᵐ x : ℝ ∂volume, ∀ᵐ t : ℝ ∂volume,
      (x, t) ∉ T → Q x t = 0 := Measure.ae_ae_of_ae_prod hQsupport
  have hJmeas : MeasurableSet J := hJ.isClosed.measurableSet
  have hJfinite : volume J < ∞ := hJ.measure_lt_top
  have hJint : Integrable (J.indicator (1 : ℝ → ℝ)) volume := by
    rw [← memLp_one_iff_integrable]
    exact memLp_indicator_const 1 hJmeas 1 (Or.inr hJfinite.ne)
  have hHmeas : StronglyMeasurable (fun x : ℝ ↦ ∫ t : ℝ, Q x t) :=
    hQmeas.integral_prod_right'
  have hHbound : ∀ᵐ x : ℝ ∂volume,
      ‖∫ t : ℝ, Q x t‖ ≤ (volume J).toReal := by
    filter_upwards [hsections, hboundSections, hsuppSections] with x hxint hxbound hxsupport
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
    filter_upwards [hsuppSections] with x hxsupport
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
  refine ⟨hHmeas.measurable, hHbound, hHsupport, ?_, ?_⟩
  · exact aux_memLp_of_ae_bound_of_ae_support _ hHmeas.aestronglyMeasurable
      (volume J).toReal hHbound X hXmeas hXfinite hHsupport 1
  · exact aux_memLp_of_ae_bound_of_ae_support _ hHmeas.aestronglyMeasurable
      (volume J).toReal hHbound X hXmeas hXfinite hHsupport 2

/-- For \(\label{thm:dual-difference-interchange}\), this packages the
measurability, support, and `L¹ ∩ L²` properties of the averaged function.
It is used by `dualDifferenceInterchange`. -/
lemma aux_dual_average_properties
    (A J : Set ℝ) (hAcompact : IsCompact A) (hJcompact : IsCompact J)
    (Ft : ℝ → ℝ → ℂ)
    (hFt_measurable : Measurable (Function.uncurry Ft))
    (hFt_one_bounded : ∀ t : ℝ, ∀ᵐ x ∂volume, ‖Ft t x‖ ≤ 1)
    (hFt_support : ∀ t : ℝ, ∀ᵐ x ∂volume, x ∉ A → Ft t x = 0)
    (χ : ℝ → ℝ)
    (hχ_measurable : Measurable χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t)
    (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (hχ_support : ∀ᵐ t ∂volume, t ∉ J → χ t = 0) :
    Measurable (fun x : ℝ ↦ ∫ t : ℝ, Ft t x * (χ t : ℂ)) ∧
      (∀ᵐ x : ℝ ∂volume, ‖∫ t : ℝ, Ft t x * (χ t : ℂ)‖ ≤ volume.real J) ∧
      (∀ᵐ x : ℝ ∂volume, x ∉ A → (∫ t : ℝ, Ft t x * (χ t : ℂ)) = 0) ∧
      MemLp (fun x : ℝ ↦ ∫ t : ℝ, Ft t x * (χ t : ℂ)) (1 : ℝ≥0∞) volume ∧
      MemLp (fun x : ℝ ↦ ∫ t : ℝ, Ft t x * (χ t : ℂ)) (2 : ℝ≥0∞) volume := by
  obtain ⟨hKmeas, hKbound, hKsupport⟩ :=
    aux_dualKernel_properties A J hAcompact.isClosed.measurableSet Ft hFt_measurable
      hFt_one_bounded hFt_support χ hχ_measurable hχ_nonneg hχ_le_one hχ_support
  simpa only [aux_dualKernel] using
    aux_timeIntegral_properties_compactSupport A J hAcompact hJcompact (aux_dualKernel Ft χ)
      hKmeas hKbound hKsupport

/-- For \(\label{thm:dual-difference-interchange}\), this supplies joint
measurability, `L¹` sections, and fixed spatial support for differences of
the averaged function.  It is used by `dualDifferenceInterchange`. -/
lemma aux_dual_difference_data
    (A : Set ℝ) (F : ℝ → ℂ) (hFmeas : Measurable F)
    (hFtwo : MemLp F (2 : ℝ≥0∞) volume)
    (hFsupp : ∀ᵐ x : ℝ ∂volume, x ∉ A → F x = 0) :
    Measurable (Function.uncurry fun h x : ℝ ↦ multiplicativeDifference h F x) ∧
      (∀ h : ℝ, Integrable (multiplicativeDifference h F) volume) ∧
      (∀ h : ℝ, ∀ᵐ x : ℝ ∂volume, x ∉ A → multiplicativeDifference h F x = 0) := by
  have hjoint : Measurable (Function.uncurry fun h x : ℝ ↦
      multiplicativeDifference h F x) := by
    have hleft : Measurable (fun z : ℝ × ℝ ↦ F z.2) := hFmeas.comp measurable_snd
    have hright : Measurable (fun z : ℝ × ℝ ↦ F (z.2 + z.1)) :=
      hFmeas.comp (measurable_snd.add measurable_fst)
    exact hleft.mul (Complex.continuous_conj.measurable.comp hright)
  have hint : ∀ h : ℝ, Integrable (multiplicativeDifference h F) volume := by
    intro h
    have hshift : MemLp (fun x : ℝ ↦ F (x + h)) (2 : ℝ≥0∞) volume := by
      simpa only [Function.comp_def] using
        hFtwo.comp_measurePreserving (measurePreserving_add_right volume h)
    have hprod : MemLp (fun x : ℝ ↦ starRingEnd ℂ (F (x + h)) * F x)
        (1 : ℝ≥0∞) volume := hFtwo.mul' (p := (2 : ℝ≥0∞))
          (r := (1 : ℝ≥0∞)) hshift.star
    rw [← memLp_one_iff_integrable]
    convert hprod using 1
    ext x
    exact mul_comm _ _
  have hsupp : ∀ h : ℝ, ∀ᵐ x : ℝ ∂volume,
      x ∉ A → multiplicativeDifference h F x = 0 := by
    intro h
    filter_upwards [hFsupp] with x hx
    intro hxA
    simp [multiplicativeDifference, hx hxA]
  exact ⟨hjoint, hint, hsupp⟩

/-- For \(\label{thm:dual-difference-interchange}\), this proves
integrability of the `L¹` norm of all multiplicative differences.  It is
used to control the Fourier-supremum profile in `dualDifferenceInterchange`. -/
lemma aux_dual_difference_norm_integrable
    (f : ℝ → ℂ) (hf : Integrable f volume) :
    Integrable (fun h : ℝ ↦ ∫ x : ℝ, ‖multiplicativeDifference h f x‖) volume := by
  have hfstar : Integrable (fun x : ℝ ↦ starRingEnd ℂ (f x)) volume := by
    change Integrable (star f) volume
    rw [← memLp_one_iff_integrable] at hf ⊢
    exact hf.star
  let K : ℝ × ℝ → ℂ := fun z ↦ f z.1 * starRingEnd ℂ (f z.2)
  have hK : Integrable K (volume.prod volume) := by
    simpa only [K] using hf.mul_prod hfstar
  have hKshear : Integrable (fun z : ℝ × ℝ ↦
      f z.1 * starRingEnd ℂ (f (z.1 + z.2))) (volume.prod volume) := by
    change Integrable (K ∘ fun z : ℝ × ℝ ↦ (z.1, z.1 + z.2)) (volume.prod volume)
    rw [← memLp_one_iff_integrable] at hK ⊢
    exact hK.comp_measurePreserving (measurePreserving_prod_add volume volume)
  have hR : Integrable (fun z : ℝ × ℝ ↦
      f z.2 * starRingEnd ℂ (f (z.2 + z.1))) (volume.prod volume) := by
    simpa [Function.comp_def, Prod.swap] using hKshear.swap
  have hRnorm : Integrable (fun z : ℝ × ℝ ↦
      ‖multiplicativeDifference z.1 f z.2‖) (volume.prod volume) := by
    convert hR.norm using 1 <;> ext z <;> simp [multiplicativeDifference]
  exact hRnorm.integral_prod_left

/-- For \(\label{thm:dual-difference-interchange}\), this supplies
measurability of a Fourier `L^∞` profile for a jointly measurable `L¹`
family.  It is used by `dualDifferenceInterchange`. -/
lemma aux_fourier_linf_profile_measurable
    (g : ℝ → ℝ → ℂ) (hg_measurable : Measurable (Function.uncurry g))
    (hg_integrable : ∀ h : ℝ, Integrable (g h) volume) :
    Measurable (fun h : ℝ ↦
      (eLpNorm (𝓕 (g h)) (∞ : ℝ≥0∞) volume).toReal) := by
  classical
  obtain ⟨qrat, hqrat⟩ := exists_surjective_nat ℚ
  let q : ℕ → ℝ := fun m ↦ (qrat m : ℝ)
  have hq : DenseRange q := by
    have hrange : Set.range q = Set.range ((↑) : ℚ → ℝ) := by
      apply Set.Subset.antisymm
      · rintro x ⟨m, rfl⟩
        exact ⟨qrat m, rfl⟩
      · rintro x ⟨r, rfl⟩
        rcases hqrat r with ⟨m, hm⟩
        exact ⟨m, by simp [q, hm]⟩
    change Dense (Set.range q)
    rw [hrange]
    exact Rat.denseRange_cast
  let s : ℝ → ℝ := fun h ↦
    (eLpNorm (𝓕 (g h)) (∞ : ℝ≥0∞) volume).toReal
  let v : ℕ → ℝ → ℝ := fun m h ↦ ‖𝓕 (g h) (q m)‖
  have hfourierCont : ∀ h : ℝ, Continuous (𝓕 (g h)) := by
    intro h
    exact VectorFourier.fourierIntegral_continuous (e := 𝐞) (μ := volume)
      (L := innerₗ ℝ) Real.continuous_fourierChar (by fun_prop) (hg_integrable h)
  have hfourierFin : ∀ h : ℝ, eLpNorm (𝓕 (g h)) (∞ : ℝ≥0∞) volume < ∞ := by
    intro h
    exact (aux_eLpNorm_fourier_le_integral_norm (g h)).trans_lt ENNReal.ofReal_lt_top
  have hv_meas : ∀ m : ℕ, Measurable (v m) := by
    intro m
    dsimp [v]
    exact (aux_fourier_evaluation_measurable g hg_measurable (q m)).norm
  have hs_eq : ∀ h : ℝ, s h = ⨆ m : ℕ, v m h := by
    intro h
    dsimp [s, v]
    exact aux_linf_eq_iSup_dense q hq (𝓕 (g h))
      (hfourierCont h) (hfourierFin h)
  have hsup : Measurable (fun h : ℝ ↦ ⨆ m : ℕ, v m h) := Measurable.iSup hv_meas
  convert hsup using 1
  funext h
  exact hs_eq h

/-- For \(\label{thm:dual-difference-interchange}\), this proves
integrability of the Fourier `L^∞` profile of the averaged function.  It is
used by `dualDifferenceInterchange`. -/
lemma aux_dual_fourier_linf_profile_integrable
    (F : ℝ → ℂ) (hFmeas : Measurable F)
    (hFone : MemLp F (1 : ℝ≥0∞) volume)
    (hFtwo : MemLp F (2 : ℝ≥0∞) volume) :
    Integrable (fun h : ℝ ↦
      (eLpNorm (𝓕 (multiplicativeDifference h F)) (∞ : ℝ≥0∞) volume).toReal)
      volume := by
  rcases aux_dual_difference_data Set.univ F hFmeas hFtwo
    (Filter.Eventually.of_forall fun x hx ↦ (hx (Set.mem_univ x)).elim)
      with ⟨hjoint, hint, _⟩
  have hsmeas : Measurable (fun h : ℝ ↦
      (eLpNorm (𝓕 (multiplicativeDifference h F)) (∞ : ℝ≥0∞) volume).toReal) :=
    aux_fourier_linf_profile_measurable _ hjoint hint
  have hHint : Integrable (fun h : ℝ ↦ ∫ x : ℝ,
      ‖multiplicativeDifference h F x‖) volume :=
    aux_dual_difference_norm_integrable F (memLp_one_iff_integrable.mp hFone)
  apply hHint.mono' hsmeas.aestronglyMeasurable
  filter_upwards with h
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  have hraw := aux_eLpNorm_fourier_le_integral_norm (multiplicativeDifference h F)
  have hnonneg : 0 ≤ ∫ x : ℝ, ‖multiplicativeDifference h F x‖ :=
    integral_nonneg fun x ↦ norm_nonneg _
  simpa [ENNReal.toReal_ofReal hnonneg] using
    (ENNReal.toReal_mono (by simp) hraw)

/-- For \(\label{thm:dual-difference-interchange}\), this converts the
integrable real Fourier-supremum profile into the squared `u³` quantity.
It is used by `dualDifferenceInterchange`. -/
lemma aux_dual_u3_square_from_real_integral
    (f : ℝ → ℂ)
    (hs : Integrable (fun h : ℝ ↦
      (eLpNorm (𝓕 (multiplicativeDifference h f)) ∞ volume).toReal) volume)
    (hfin : ∀ h : ℝ,
      eLpNorm (𝓕 (multiplicativeDifference h f)) ∞ volume < ∞) :
    ENNReal.ofReal (∫ h : ℝ,
      (eLpNorm (𝓕 (multiplicativeDifference h f)) ∞ volume).toReal) =
      (uNorm 3 f) ^ (2 : ℝ) := by
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hs]
  · calc
      ∫⁻ h : ℝ, ENNReal.ofReal
          (eLpNorm (𝓕 (multiplicativeDifference h f)) ∞ volume).toReal =
          ∫⁻ h : ℝ, eLpNorm (𝓕 (multiplicativeDifference h f)) ∞ volume := by
            apply lintegral_congr
            intro h
            exact ENNReal.ofReal_toReal (hfin h).ne
      _ = (uNorm 3 f) ^ (2 : ℝ) := (aux_uNorm_three_sq_real_parameter f).symm
  · filter_upwards with h
    exact ENNReal.toReal_nonneg

/-- For \(\label{thm:dual-difference-interchange}\), this is the
autocorrelation identity for a kernel with pair-valued outer variable.  It
is used by `dualDifferenceInterchange`. -/
lemma aux_autocorrelation_integral_ae_prod
    (F : (ℝ × ℝ) → ℝ → ℂ)
    (hF : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, Integrable (F z) volume)
    (hR : Integrable
      (Function.uncurry fun p : (ℝ × ℝ) × ℝ ↦ fun t : ℝ ↦
        F p.1 t * starRingEnd ℂ (F p.1 (t + p.2)))
      ((volume.prod volume).prod volume)) :
    ∫ z : ℝ × ℝ, (↑(‖∫ t : ℝ, F z t‖ ^ (2 : ℕ)) : ℂ) =
      ∫ h : ℝ, ∫ z : ℝ × ℝ, ∫ t : ℝ,
        F z t * starRingEnd ℂ (F z (t + h)) := by
  let R : (ℝ × ℝ) × ℝ → ℝ → ℂ := fun p t ↦
    F p.1 t * starRingEnd ℂ (F p.1 (t + p.2))
  have hD : Integrable (fun p : (ℝ × ℝ) × ℝ ↦ ∫ t : ℝ, R p t)
      ((volume.prod volume).prod volume) := by
    exact hR.integral_prod_left
  calc
    ∫ z : ℝ × ℝ, (↑(‖∫ t : ℝ, F z t‖ ^ (2 : ℕ)) : ℂ) =
        ∫ z : ℝ × ℝ, ∫ h : ℝ, ∫ t : ℝ,
          F z t * starRingEnd ℂ (F z (t + h)) := by
      apply integral_congr_ae
      filter_upwards [hF] with z hz
      exact aux_single_autocorrelation_integral (F z) hz
    _ = ∫ h : ℝ, ∫ z : ℝ × ℝ, ∫ t : ℝ,
        F z t * starRingEnd ℂ (F z (t + h)) := by
      simpa only [R] using (integral_integral_swap hD)

/-- For \(\label{thm:dual-difference-interchange}\), this takes norms in
the pair-indexed autocorrelation identity used by `dualDifferenceInterchange`. -/
lemma aux_integral_norm_sq_le_autocorrelation_prod
    (H : ℝ × ℝ → ℂ) (D : ℝ → ℂ)
    (hH : MemLp H 2 (volume.prod volume))
    (hEq : ∫ z : ℝ × ℝ, (↑(‖H z‖ ^ (2 : ℕ)) : ℂ) = ∫ h : ℝ, D h) :
    ∫ z : ℝ × ℝ, ‖H z‖ ^ (2 : ℕ) ≤ ∫ h : ℝ, ‖D h‖ := by
  have hHsq : Integrable (fun z : ℝ × ℝ ↦ ‖H z‖ ^ (2 : ℕ)) (volume.prod volume) :=
    hH.integrable_norm_pow (by norm_num)
  have hnonneg : 0 ≤ ∫ z : ℝ × ℝ, ‖H z‖ ^ (2 : ℕ) :=
    integral_nonneg fun z ↦ sq_nonneg ‖H z‖
  calc
    ∫ z : ℝ × ℝ, ‖H z‖ ^ (2 : ℕ) =
        ‖(↑(∫ z : ℝ × ℝ, ‖H z‖ ^ (2 : ℕ)) : ℂ)‖ := by
      exact ((RCLike.norm_ofReal (∫ z : ℝ × ℝ, ‖H z‖ ^ (2 : ℕ))).trans
        (abs_of_nonneg hnonneg)).symm
    _ = ‖∫ z : ℝ × ℝ, (↑(‖H z‖ ^ (2 : ℕ)) : ℂ)‖ := by
      congr 1
      exact (integral_ofReal (f := fun z : ℝ × ℝ ↦ ‖H z‖ ^ (2 : ℕ))).symm
    _ = ‖∫ h : ℝ, D h‖ := congrArg norm hEq
    _ ≤ ∫ h : ℝ, ‖D h‖ := norm_integral_le_integral_norm _

/-- For \(\label{thm:dual-difference-interchange}\), this is the
pair-indexed compact autocorrelation bound used after Cauchy--Schwarz in
`dualDifferenceInterchange`. -/
lemma aux_square_timeIntegral_le_autocorrelation_prod
    (F : (ℝ × ℝ) → ℝ → ℂ)
    (hF : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, Integrable (F z) volume)
    (hH : MemLp (fun z : ℝ × ℝ ↦ ∫ t : ℝ, F z t) 2 (volume.prod volume))
    (hR : Integrable
      (Function.uncurry fun p : (ℝ × ℝ) × ℝ ↦ fun t : ℝ ↦
        F p.1 t * starRingEnd ℂ (F p.1 (t + p.2)))
      ((volume.prod volume).prod volume)) :
    ∫ z : ℝ × ℝ, ‖∫ t : ℝ, F z t‖ ^ (2 : ℕ) ≤
      ∫ h : ℝ, ‖∫ z : ℝ × ℝ, ∫ t : ℝ,
        F z t * starRingEnd ℂ (F z (t + h))‖ := by
  exact aux_integral_norm_sq_le_autocorrelation_prod _ _ hH
    (aux_autocorrelation_integral_ae_prod F hF hR)

/-- The pair-indexed kernel used in the Cauchy--Schwarz/autocorrelation part
of \(\label{thm:dual-difference-interchange}\).  It is auxiliary
bookkeeping for `dualDifferenceInterchange`. -/
def aux_dualP (Ft : ℝ → ℝ → ℂ) (χ ψ : ℝ → ℝ) (u : ℝ → ℂ)
    (z : ℝ × ℝ) (h : ℝ) : ℂ :=
  ((Real.sqrt (χ z.2) : ℝ) : ℂ) * starRingEnd ℂ (Ft z.2 (z.1 + h)) *
    exponential (z.1 * ψ h) * u h

/-- For \(\label{thm:dual-difference-interchange}\), this pulls the
space--time input along the affine coordinate in `aux_dualP`. -/
lemma aux_dualP_qmp_time_space_shift :
    Measure.QuasiMeasurePreserving
      (fun z : (ℝ × ℝ) × ℝ ↦ (z.1.2, z.1.1 + z.2))
      ((volume.prod volume).prod volume) (volume.prod volume) := by
  let assoc : ((ℝ × ℝ) × ℝ) → ℝ × (ℝ × ℝ) := MeasurableEquiv.prodAssoc
  have hassoc : MeasurePreserving assoc
      ((volume.prod volume).prod volume) (volume.prod (volume.prod volume)) :=
    measurePreserving_prodAssoc volume volume volume
  have hswap : MeasurePreserving (Prod.swap : ℝ × (ℝ × ℝ) → (ℝ × ℝ) × ℝ)
      (volume.prod (volume.prod volume)) ((volume.prod volume).prod volume) :=
    Measure.measurePreserving_swap
  have hperm : MeasurePreserving
      (fun z : (ℝ × ℝ) × ℝ ↦ Prod.swap (assoc z))
      ((volume.prod volume).prod volume) ((volume.prod volume).prod volume) :=
    hswap.comp hassoc
  have hqmp := aux_autocorrelation_qmp_shifted.comp hperm.quasiMeasurePreserving
  convert hqmp using 1
  rfl

/-- For \(\label{thm:dual-difference-interchange}\), this proves joint
measurability of the Cauchy--Schwarz kernel `aux_dualP`. -/
lemma aux_dualP_measurable
    (Ft : ℝ → ℝ → ℂ) (χ ψ : ℝ → ℝ) (u : ℝ → ℂ)
    (hFt : Measurable (Function.uncurry Ft)) (hχ : Measurable χ)
    (hψ : Measurable ψ) (hu : Measurable u) :
    Measurable (Function.uncurry (aux_dualP Ft χ ψ u)) := by
  have hFt' : Measurable (fun p : (ℝ × ℝ) × ℝ ↦
      Ft p.1.2 (p.1.1 + p.2)) := by
    have hmap : Measurable (fun p : (ℝ × ℝ) × ℝ ↦
        (p.1.2, p.1.1 + p.2)) := by fun_prop
    exact hFt.comp hmap
  have hχ' : Measurable (fun p : (ℝ × ℝ) × ℝ ↦
      ((Real.sqrt (χ p.1.2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp ((hχ.comp (by fun_prop)).sqrt)
  have hFtstar : Measurable (fun p : (ℝ × ℝ) × ℝ ↦
      starRingEnd ℂ (Ft p.1.2 (p.1.1 + p.2))) :=
    Complex.continuous_conj.measurable.comp hFt'
  have hexp : Measurable (fun p : (ℝ × ℝ) × ℝ ↦
      exponential (p.1.1 * ψ p.2)) := by
    unfold exponential
    fun_prop
  change Measurable (fun p : (ℝ × ℝ) × ℝ ↦
    ((Real.sqrt (χ p.1.2) : ℝ) : ℂ) *
      starRingEnd ℂ (Ft p.1.2 (p.1.1 + p.2)) *
      exponential (p.1.1 * ψ p.2) * u p.2)
  fun_prop

/-- For \(\label{thm:dual-difference-interchange}\), this proves the
almost-everywhere one-bound of the Cauchy--Schwarz kernel
`aux_dualP`. -/
lemma aux_dualP_ae_one_bounded
    (Ft : ℝ → ℝ → ℂ) (χ ψ : ℝ → ℝ) (u : ℝ → ℂ)
    (hFtmeas : Measurable (Function.uncurry Ft))
    (hFt : ∀ t : ℝ, ∀ᵐ x ∂volume, ‖Ft t x‖ ≤ 1)
    (hχone : ∀ t : ℝ, χ t ≤ 1)
    (hu : ∀ h : ℝ, ‖u h‖ ≤ 1) :
    ∀ᵐ p : (ℝ × ℝ) × ℝ ∂((volume.prod volume).prod volume),
      ‖aux_dualP Ft χ ψ u p.1 p.2‖ ≤ 1 := by
  have hFt' : ∀ᵐ p : (ℝ × ℝ) × ℝ ∂((volume.prod volume).prod volume),
      ‖Ft p.1.2 (p.1.1 + p.2)‖ ≤ 1 := by
    have hprod : ∀ᵐ z : ℝ × ℝ ∂(volume.prod volume), ‖Ft z.1 z.2‖ ≤ 1 := by
      have hset : MeasurableSet {z : ℝ × ℝ | ‖Ft z.1 z.2‖ ≤ 1} :=
        measurableSet_le hFtmeas.norm measurable_const
      apply (Measure.ae_prod_iff_ae_ae hset).mpr
      filter_upwards with t
      exact hFt t
    exact aux_dualP_qmp_time_space_shift.ae hprod
  filter_upwards [hFt'] with p hp
  rw [aux_dualP, norm_mul, norm_mul, norm_mul]
  have hsqrt : ‖((Real.sqrt (χ p.1.2) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.mpr (hχone _)
  have hexp : ‖exponential (p.1.1 * ψ p.2)‖ = 1 := by
    unfold exponential
    rw [Complex.norm_exp]
    norm_num
  have hstar : ‖starRingEnd ℂ (Ft p.1.2 (p.1.1 + p.2))‖ =
      ‖Ft p.1.2 (p.1.1 + p.2)‖ := Complex.norm_conj _
  calc
    ‖((Real.sqrt (χ p.1.2) : ℝ) : ℂ)‖ *
        ‖starRingEnd ℂ (Ft p.1.2 (p.1.1 + p.2))‖ *
        ‖exponential (p.1.1 * ψ p.2)‖ * ‖u p.2‖ =
        ‖((Real.sqrt (χ p.1.2) : ℝ) : ℂ)‖ *
          ‖Ft p.1.2 (p.1.1 + p.2)‖ * 1 * ‖u p.2‖ := by rw [hstar, hexp]
    _ ≤ 1 * 1 * 1 * 1 := by
      gcongr
      exact hu _
    _ = 1 := by norm_num

/-- For \(\label{thm:dual-difference-interchange}\), this gives the
compact product support of `aux_dualP` from the supports of the input,
cutoff, and phase. -/
lemma aux_dualP_ae_zero_outside
    (A J D : Set ℝ) (Ft : ℝ → ℝ → ℂ) (χ ψ : ℝ → ℝ) (u : ℝ → ℂ)
    (hAmeas : MeasurableSet A)
    (hFtmeas : Measurable (Function.uncurry Ft))
    (hFtsupport : ∀ t : ℝ, ∀ᵐ x ∂volume, x ∉ A → Ft t x = 0)
    (hχsupport : ∀ᵐ t ∂volume, t ∉ J → χ t = 0)
    (husupport : ∀ h : ℝ, h ∉ D → u h = 0) :
    ∀ᵐ p : (ℝ × ℝ) × ℝ ∂((volume.prod volume).prod volume),
      p ∉ (Set.image2 (fun a d : ℝ ↦ a - d) A D ×ˢ J) ×ˢ D →
        aux_dualP Ft χ ψ u p.1 p.2 = 0 := by
  have hFtprod : ∀ᵐ z : ℝ × ℝ ∂(volume.prod volume),
      z.2 ∉ A → Ft z.1 z.2 = 0 := by
    have hset : MeasurableSet {z : ℝ × ℝ | z.2 ∉ A → Ft z.1 z.2 = 0} := by
      have heq : {z : ℝ × ℝ | z.2 ∉ A → Ft z.1 z.2 = 0} =
          (Prod.snd ⁻¹' A) ∪ ((Function.uncurry Ft) ⁻¹' ({0} : Set ℂ)) := by
        ext z
        constructor
        · intro hz
          by_cases hzA : z.2 ∈ A
          · exact Or.inl hzA
          · exact Or.inr (hz hzA)
        · rintro (hzA | hz0) hznot
          · exact (hznot hzA).elim
          · exact hz0
      rw [heq]
      exact (hAmeas.preimage measurable_snd).union
        ((measurableSet_singleton (0 : ℂ)).preimage hFtmeas)
    apply (Measure.ae_prod_iff_ae_ae hset).mpr
    filter_upwards with t
    exact hFtsupport t
  have hFt' : ∀ᵐ p : (ℝ × ℝ) × ℝ ∂((volume.prod volume).prod volume),
      p.1.1 + p.2 ∉ A → Ft p.1.2 (p.1.1 + p.2) = 0 :=
    aux_dualP_qmp_time_space_shift.ae hFtprod
  have htqmp : Measure.QuasiMeasurePreserving
      (fun p : (ℝ × ℝ) × ℝ ↦ p.1.2)
      ((volume.prod volume).prod volume) volume := by
    exact Measure.quasiMeasurePreserving_snd.comp
      (Measure.quasiMeasurePreserving_fst (μ := volume.prod volume) (ν := volume))
  have hχ' : ∀ᵐ p : (ℝ × ℝ) × ℝ ∂((volume.prod volume).prod volume),
      p.1.2 ∉ J → χ p.1.2 = 0 := htqmp.ae hχsupport
  filter_upwards [hFt', hχ'] with p hpFt hpχ
  intro hpbox
  by_cases hhD : p.2 ∈ D
  · by_cases htJ : p.1.2 ∈ J
    · have hx : p.1.1 ∉ Set.image2 (fun a d : ℝ ↦ a - d) A D := by
        intro hx
        exact hpbox ⟨⟨hx, htJ⟩, hhD⟩
      have hnotA : p.1.1 + p.2 ∉ A := by
        intro hA
        apply hx
        exact ⟨p.1.1 + p.2, hA, p.2, hhD, by ring⟩
      simp [aux_dualP, hpFt hnotA]
    · simp [aux_dualP, hpχ htJ]
  · simp [aux_dualP, husupport p.2 hhD]

/-- For \(\label{thm:dual-difference-interchange}\), this gives integrable
time sections and an `L²` time integral for a bounded kernel with a compact
pair-valued outer support.  It is used by `dualDifferenceInterchange`. -/
lemma aux_pair_timeIntegral_memLp_compactSupport
    (Z : Set (ℝ × ℝ)) (D : Set ℝ) (hZ : IsCompact Z) (hD : IsCompact D)
    (P : (ℝ × ℝ) → ℝ → ℂ)
    (hPmeas : AEStronglyMeasurable (Function.uncurry P)
      ((volume.prod volume).prod volume))
    (hPbound : ∀ᵐ p : (ℝ × ℝ) × ℝ ∂((volume.prod volume).prod volume),
      ‖P p.1 p.2‖ ≤ 1)
    (hPsupport : ∀ᵐ p : (ℝ × ℝ) × ℝ ∂((volume.prod volume).prod volume),
      p ∉ Z ×ˢ D → P p.1 p.2 = 0) :
    (∀ᵐ z : ℝ × ℝ ∂volume.prod volume, Integrable (P z) volume) ∧
      MemLp (fun z : ℝ × ℝ ↦ ∫ h : ℝ, P z h) 2 (volume.prod volume) := by
  let T : Set ((ℝ × ℝ) × ℝ) := Z ×ˢ D
  have hTmeas : MeasurableSet T := hZ.isClosed.measurableSet.prod hD.isClosed.measurableSet
  have hTfinite : ((volume.prod volume).prod volume) T < ∞ := (hZ.prod hD).measure_lt_top
  have hPmem : MemLp (Function.uncurry P) 1 ((volume.prod volume).prod volume) :=
    aux_memLp_of_ae_bound_of_ae_support _ hPmeas 1 hPbound T hTmeas hTfinite hPsupport 1
  have hPint : Integrable (Function.uncurry P) ((volume.prod volume).prod volume) :=
    memLp_one_iff_integrable.mp hPmem
  have hsections : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, Integrable (P z) volume :=
    hPint.prod_right_ae
  have hboundSections : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      ∀ᵐ h : ℝ ∂volume, ‖P z h‖ ≤ 1 := Measure.ae_ae_of_ae_prod hPbound
  have hsuppSections : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      ∀ᵐ h : ℝ ∂volume, (z, h) ∉ T → P z h = 0 :=
    Measure.ae_ae_of_ae_prod hPsupport
  have hDmeas : MeasurableSet D := hD.isClosed.measurableSet
  have hDfinite : volume D < ∞ := hD.measure_lt_top
  have hDint : Integrable (D.indicator (1 : ℝ → ℝ)) volume := by
    rw [← memLp_one_iff_integrable]
    exact memLp_indicator_const 1 hDmeas 1 (Or.inr hDfinite.ne)
  have hHmeas : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ ∫ h : ℝ, P z h)
      (volume.prod volume) := hPmeas.integral_prod_right'
  have hHbound : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      ‖∫ h : ℝ, P z h‖ ≤ (volume D).toReal := by
    filter_upwards [hsections, hboundSections, hsuppSections] with z hzint hzbound hzsupport
    calc
      ‖∫ h : ℝ, P z h‖ ≤ ∫ h : ℝ, ‖P z h‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ h : ℝ, D.indicator (1 : ℝ → ℝ) h := by
        apply integral_mono_ae hzint.norm hDint
        filter_upwards [hzbound, hzsupport] with h hhbound hhsupport
        by_cases hh : h ∈ D
        · simp [hh, hhbound]
        · have hnotT : (z, h) ∉ T := by
            intro hmem
            change z ∈ Z ∧ h ∈ D at hmem
            exact hh hmem.2
          simp [hh, hhsupport hnotT]
      _ = (volume D).toReal := by
        simpa only [Measure.real] using (integral_indicator_one (μ := volume) hDmeas)
  have hHsupport : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∉ Z → (∫ h : ℝ, P z h) = 0 := by
    filter_upwards [hsuppSections] with z hzsupport
    intro hz
    rw [← integral_zero]
    apply integral_congr_ae
    filter_upwards [hzsupport] with h hhsupport
    have hnotT : (z, h) ∉ T := by
      intro hmem
      change z ∈ Z ∧ h ∈ D at hmem
      exact hz hmem.1
    exact hhsupport hnotT
  have hZmeas : MeasurableSet Z := hZ.isClosed.measurableSet
  have hZfinite : (volume.prod volume) Z < ∞ := hZ.measure_lt_top
  refine ⟨hsections, ?_⟩
  exact aux_memLp_of_ae_bound_of_ae_support _ hHmeas (volume D).toReal hHbound
    Z hZmeas hZfinite hHsupport 2

/-- The pair-valued outer measure used in the compact autocorrelation
bookkeeping for \(\label{thm:dual-difference-interchange}\). -/
abbrev aux_dualPairMeasure : Measure (ℝ × ℝ) := volume.prod volume

/-- For \(\label{thm:dual-difference-interchange}\), this is the first
projection used to control an unshifted pair-kernel correlation. -/
lemma aux_dual_qmp_pright_unshifted :
    Measure.QuasiMeasurePreserving
      (fun p : (ℝ × ℝ) × (ℝ × ℝ) ↦ (p.1, p.2.1))
      (aux_dualPairMeasure.prod (volume.prod volume)) (aux_dualPairMeasure.prod volume) := by
  have h := MeasureTheory.QuasiMeasurePreserving.prodMap
    (Measure.QuasiMeasurePreserving.id (α := ℝ × ℝ) aux_dualPairMeasure)
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ)))
  convert h using 1
  rfl

/-- For \(\label{thm:dual-difference-interchange}\), this is the second
projection used to control an unshifted pair-kernel correlation. -/
lemma aux_dual_qmp_pright_second :
    Measure.QuasiMeasurePreserving
      (fun p : (ℝ × ℝ) × (ℝ × ℝ) ↦ (p.1, p.2.2))
      (aux_dualPairMeasure.prod (volume.prod volume)) (aux_dualPairMeasure.prod volume) := by
  have h := MeasureTheory.QuasiMeasurePreserving.prodMap
    (Measure.QuasiMeasurePreserving.id (α := ℝ × ℝ) aux_dualPairMeasure)
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ)))
  convert h using 1
  rfl

/-- For \(\label{thm:dual-difference-interchange}\), this pulls the
unshifted time coordinate through the four-variable correlation measure. -/
lemma aux_dual_qmp_pleft_unshifted :
    Measure.QuasiMeasurePreserving
      (fun p : ((ℝ × ℝ) × ℝ) × ℝ ↦ (p.1.1, p.1.2))
      ((aux_dualPairMeasure.prod volume).prod volume) (aux_dualPairMeasure.prod volume) := by
  have hprod := MeasureTheory.QuasiMeasurePreserving.prodMap
    (Measure.QuasiMeasurePreserving.id (α := ℝ × ℝ) aux_dualPairMeasure)
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ)))
  have h := hprod.comp
    (measurePreserving_prodAssoc aux_dualPairMeasure volume volume).quasiMeasurePreserving
  convert h using 1
  rfl

/-- For \(\label{thm:dual-difference-interchange}\), this pulls the
shifted time coordinate through the four-variable correlation measure. -/
lemma aux_dual_qmp_pleft_shifted :
    Measure.QuasiMeasurePreserving
      (fun p : ((ℝ × ℝ) × ℝ) × ℝ ↦ (p.1.1, p.1.2 + p.2))
      ((aux_dualPairMeasure.prod volume).prod volume) (aux_dualPairMeasure.prod volume) := by
  have hadd : Measure.QuasiMeasurePreserving (fun q : ℝ × ℝ ↦ q.1 + q.2)
      (volume.prod volume) volume := by
    simpa using (quasiMeasurePreserving_add volume volume)
  have h := MeasureTheory.QuasiMeasurePreserving.prodMap
    (Measure.QuasiMeasurePreserving.id (α := ℝ × ℝ) aux_dualPairMeasure) hadd
  have h' := h.comp
    (measurePreserving_prodAssoc aux_dualPairMeasure volume volume).quasiMeasurePreserving
  convert h' using 1
  rfl

/-- For \(\label{thm:dual-difference-interchange}\), this produces the
section and shifted-correlation integrability needed to autocorrelate a
bounded pair-indexed compact kernel.  It is used by
`dualDifferenceInterchange`. -/
lemma aux_autocorrelation_product_sections_and_integrable
    (Z : Set (ℝ × ℝ)) (D : Set ℝ) (hZ : IsCompact Z) (hD : IsCompact D)
    (P : (ℝ × ℝ) → ℝ → ℂ)
    (hPmeas : Measurable (Function.uncurry P))
    (hPbound : ∀ᵐ q : (ℝ × ℝ) × ℝ ∂(aux_dualPairMeasure.prod volume), ‖P q.1 q.2‖ ≤ 1)
    (hPsupp : ∀ᵐ q : (ℝ × ℝ) × ℝ ∂(aux_dualPairMeasure.prod volume),
      q ∉ Z ×ˢ D → P q.1 q.2 = 0) :
    (∀ᵐ z : ℝ × ℝ ∂aux_dualPairMeasure, Integrable
      (Function.uncurry (fun h r : ℝ ↦ P z h * starRingEnd ℂ (P z r)))
      (volume.prod volume)) ∧
    Integrable
      (Function.uncurry fun p : ((ℝ × ℝ) × ℝ) ↦ fun r : ℝ ↦
        P p.1 p.2 * starRingEnd ℂ (P p.1 (p.2 + r)))
      ((aux_dualPairMeasure.prod volume).prod volume) := by
  let G : (ℝ × ℝ) × (ℝ × ℝ) → ℂ := fun p ↦
    P p.1 p.2.1 * starRingEnd ℂ (P p.1 p.2.2)
  have hGmeas : Measurable G := by
    have hleftmap : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) ↦ (p.1, p.2.1)) := by
      fun_prop
    have hrightmap : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) ↦ (p.1, p.2.2)) := by
      fun_prop
    have hleft : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) ↦ P p.1 p.2.1) :=
      hPmeas.comp hleftmap
    have hright : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) ↦ P p.1 p.2.2) :=
      hPmeas.comp hrightmap
    exact hleft.mul (Complex.continuous_conj.measurable.comp hright)
  have hGbound : ∀ᵐ p : (ℝ × ℝ) × (ℝ × ℝ) ∂
      (aux_dualPairMeasure.prod (volume.prod volume)), ‖G p‖ ≤ 1 := by
    filter_upwards [aux_dual_qmp_pright_unshifted.ae hPbound,
      aux_dual_qmp_pright_second.ae hPbound] with p hp₁ hp₂
    rw [show G p = P p.1 p.2.1 * starRingEnd ℂ (P p.1 p.2.2) by rfl,
      norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg (P p.1 p.2.1), norm_nonneg (P p.1 p.2.2)]
  let SG : Set ((ℝ × ℝ) × (ℝ × ℝ)) := Z ×ˢ (D ×ˢ D)
  have hSGcompact : IsCompact SG := by
    dsimp only [SG]
    exact hZ.prod (hD.prod hD)
  have hGsupp : ∀ᵐ p : (ℝ × ℝ) × (ℝ × ℝ) ∂
      (aux_dualPairMeasure.prod (volume.prod volume)), p ∉ SG → G p = 0 := by
    filter_upwards [aux_dual_qmp_pright_unshifted.ae hPsupp,
      aux_dual_qmp_pright_second.ae hPsupp] with p hp₁ hp₂
    intro hpSG
    by_cases hleft : (p.1, p.2.1) ∈ Z ×ˢ D
    · by_cases hright : (p.1, p.2.2) ∈ Z ×ˢ D
      · apply False.elim
        apply hpSG
        change p.1 ∈ Z ∧ p.2.1 ∈ D ∧ p.2.2 ∈ D
        exact ⟨hleft.1, hleft.2, hright.2⟩
      · simp [G, hp₂ hright]
    · simp [G, hp₁ hleft]
  have hGint : Integrable G (aux_dualPairMeasure.prod (volume.prod volume)) := by
    rw [← memLp_one_iff_integrable]
    exact aux_memLp_of_ae_bound_of_ae_support G hGmeas.aestronglyMeasurable 1 hGbound SG
      hSGcompact.isClosed.measurableSet hSGcompact.measure_lt_top hGsupp 1
  have hRmeas : Measurable
      (Function.uncurry fun p : ((ℝ × ℝ) × ℝ) ↦ fun r : ℝ ↦
        P p.1 p.2 * starRingEnd ℂ (P p.1 (p.2 + r))) := by
    have hleftmap : Measurable (fun p : ((ℝ × ℝ) × ℝ) × ℝ ↦ (p.1.1, p.1.2)) := by
      fun_prop
    have hrightmap : Measurable (fun p : ((ℝ × ℝ) × ℝ) × ℝ ↦
        (p.1.1, p.1.2 + p.2)) := by
      fun_prop
    have hleft : Measurable (fun p : ((ℝ × ℝ) × ℝ) × ℝ ↦ P p.1.1 p.1.2) :=
      hPmeas.comp hleftmap
    have hright : Measurable (fun p : ((ℝ × ℝ) × ℝ) × ℝ ↦
        P p.1.1 (p.1.2 + p.2)) := hPmeas.comp hrightmap
    exact hleft.mul (Complex.continuous_conj.measurable.comp hright)
  have hRbound : ∀ᵐ p : ((ℝ × ℝ) × ℝ) × ℝ ∂
      ((aux_dualPairMeasure.prod volume).prod volume),
      ‖P p.1.1 p.1.2 * starRingEnd ℂ (P p.1.1 (p.1.2 + p.2))‖ ≤ 1 := by
    filter_upwards [aux_dual_qmp_pleft_unshifted.ae hPbound,
      aux_dual_qmp_pleft_shifted.ae hPbound] with p hp₁ hp₂
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg (P p.1.1 p.1.2), norm_nonneg (P p.1.1 (p.1.2 + p.2))]
  let DD : Set ℝ := Set.image2 (fun d₁ d₂ : ℝ ↦ d₁ - d₂) D D
  let SR : Set (((ℝ × ℝ) × ℝ) × ℝ) := (Z ×ˢ D) ×ˢ DD
  have hDDcompact : IsCompact DD := by
    dsimp only [DD]
    exact aux_isCompact_image2_sub D hD
  have hSRcompact : IsCompact SR := by
    dsimp only [SR]
    exact (hZ.prod hD).prod hDDcompact
  have hRsupp : ∀ᵐ p : ((ℝ × ℝ) × ℝ) × ℝ ∂
      ((aux_dualPairMeasure.prod volume).prod volume), p ∉ SR →
        P p.1.1 p.1.2 * starRingEnd ℂ (P p.1.1 (p.1.2 + p.2)) = 0 := by
    filter_upwards [aux_dual_qmp_pleft_unshifted.ae hPsupp,
      aux_dual_qmp_pleft_shifted.ae hPsupp] with p hp₁ hp₂
    intro hpSR
    by_cases hleft : (p.1.1, p.1.2) ∈ Z ×ˢ D
    · by_cases hright : (p.1.1, p.1.2 + p.2) ∈ Z ×ˢ D
      · apply False.elim
        apply hpSR
        dsimp only [SR]
        refine ⟨hleft, ?_⟩
        exact ⟨p.1.2 + p.2, hright.2, p.1.2, hleft.2, by ring⟩
      · simp [hp₂ hright]
    · simp [hp₁ hleft]
  have hRint : Integrable
      (Function.uncurry fun p : ((ℝ × ℝ) × ℝ) ↦ fun r : ℝ ↦
        P p.1 p.2 * starRingEnd ℂ (P p.1 (p.2 + r)))
      ((aux_dualPairMeasure.prod volume).prod volume) := by
    rw [← memLp_one_iff_integrable]
    exact aux_memLp_of_ae_bound_of_ae_support _ hRmeas.aestronglyMeasurable 1 hRbound SR
      hSRcompact.isClosed.measurableSet hSRcompact.measure_lt_top hRsupp 1
  exact ⟨hGint.prod_right_ae, hRint⟩

/-- For \(\label{thm:dual-difference-interchange}\), this discharges all
Fubini integrability conditions for the autocorrelation of `aux_dualP`.
It is used by `dualDifferenceInterchange`. -/
lemma aux_dualP_autocorrelation_conditions
    (A J D : Set ℝ) (hA : IsCompact A) (hJ : IsCompact J) (hD : IsCompact D)
    (Ft : ℝ → ℝ → ℂ) (χ ψ : ℝ → ℝ) (u : ℝ → ℂ)
    (hFtmeas : Measurable (Function.uncurry Ft))
    (hFtbound : ∀ t : ℝ, ∀ᵐ x ∂volume, ‖Ft t x‖ ≤ 1)
    (hFtsupport : ∀ t : ℝ, ∀ᵐ x ∂volume, x ∉ A → Ft t x = 0)
    (hχmeas : Measurable χ) (hχone : ∀ t : ℝ, χ t ≤ 1)
    (hχsupport : ∀ᵐ t ∂volume, t ∉ J → χ t = 0)
    (hψmeas : Measurable ψ) (humeas : Measurable u)
    (hubound : ∀ h : ℝ, ‖u h‖ ≤ 1)
    (husupport : ∀ h : ℝ, h ∉ D → u h = 0) :
    (∀ᵐ z : ℝ × ℝ ∂(volume.prod volume), Integrable
      (Function.uncurry (fun h r : ℝ ↦
        aux_dualP Ft χ ψ u z h * starRingEnd ℂ (aux_dualP Ft χ ψ u z r)))
      (volume.prod volume)) ∧
    Integrable
      (Function.uncurry fun p : ((ℝ × ℝ) × ℝ) ↦ fun r : ℝ ↦
        aux_dualP Ft χ ψ u p.1 p.2 *
          starRingEnd ℂ (aux_dualP Ft χ ψ u p.1 (p.2 + r)))
      (((volume.prod volume).prod volume).prod volume) := by
  let X : Set ℝ := Set.image2 (fun a d : ℝ ↦ a - d) A D
  let Z : Set (ℝ × ℝ) := X ×ˢ J
  have hX : IsCompact X := by
    dsimp only [X]
    rw [← Set.image_prod]
    exact (hA.prod hD).image (continuous_fst.sub continuous_snd)
  have hZ : IsCompact Z := hX.prod hJ
  apply aux_autocorrelation_product_sections_and_integrable Z D hZ hD (aux_dualP Ft χ ψ u)
  · exact aux_dualP_measurable Ft χ ψ u hFtmeas hχmeas hψmeas humeas
  · exact aux_dualP_ae_one_bounded Ft χ ψ u hFtmeas hFtbound hχone hubound
  · simpa only [Z, X] using aux_dualP_ae_zero_outside A J D Ft χ ψ u
      hA.isClosed.measurableSet hFtmeas hFtsupport hχsupport husupport

/-- For \(\label{thm:dual-difference-interchange}\), this pulls the base
time coordinate through the shift-first four-variable correlation measure. -/
lemma aux_dual_qmp_shift_first_base :
    Measure.QuasiMeasurePreserving
      (fun p : ((ℝ × ℝ) × ℝ) × ℝ ↦ (p.1.1, p.2))
      ((aux_dualPairMeasure.prod volume).prod volume) (aux_dualPairMeasure.prod volume) := by
  have hprod := MeasureTheory.QuasiMeasurePreserving.prodMap
    (Measure.QuasiMeasurePreserving.id (α := ℝ × ℝ) aux_dualPairMeasure)
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ)))
  have h := hprod.comp
    (measurePreserving_prodAssoc aux_dualPairMeasure volume volume).quasiMeasurePreserving
  convert h using 1
  rfl

/-- For \(\label{thm:dual-difference-interchange}\), this pulls the shifted
time coordinate through the shift-first four-variable correlation measure. -/
lemma aux_dual_qmp_shift_first_shifted :
    Measure.QuasiMeasurePreserving
      (fun p : ((ℝ × ℝ) × ℝ) × ℝ ↦ (p.1.1, p.2 + p.1.2))
      ((aux_dualPairMeasure.prod volume).prod volume) (aux_dualPairMeasure.prod volume) := by
  have hadd : Measure.QuasiMeasurePreserving (fun q : ℝ × ℝ ↦ q.1 + q.2)
      (volume.prod volume) volume := by
    simpa using (quasiMeasurePreserving_add volume volume)
  have hprod := MeasureTheory.QuasiMeasurePreserving.prodMap
    (Measure.QuasiMeasurePreserving.id (α := ℝ × ℝ) aux_dualPairMeasure) hadd
  have h := hprod.comp
    (measurePreserving_prodAssoc aux_dualPairMeasure volume volume).quasiMeasurePreserving
  have hbase : Measure.QuasiMeasurePreserving
      (fun p : ((ℝ × ℝ) × ℝ) × ℝ ↦ (p.1.1, p.1.2 + p.2))
      ((aux_dualPairMeasure.prod volume).prod volume) (aux_dualPairMeasure.prod volume) := by
    convert h using 1
    rfl
  convert hbase using 1
  ext p <;> simp [add_comm]

/-- For \(\label{thm:dual-difference-interchange}\), compact support and a
one-bound make the shift-first autocorrelation kernel integrable. -/
lemma aux_autocorrelation_product_integrable_shift_first
    (Z : Set (ℝ × ℝ)) (D : Set ℝ) (hZ : IsCompact Z) (hD : IsCompact D)
    (P : (ℝ × ℝ) → ℝ → ℂ)
    (hPmeas : Measurable (Function.uncurry P))
    (hPbound : ∀ᵐ q : (ℝ × ℝ) × ℝ ∂(aux_dualPairMeasure.prod volume), ‖P q.1 q.2‖ ≤ 1)
    (hPsupp : ∀ᵐ q : (ℝ × ℝ) × ℝ ∂(aux_dualPairMeasure.prod volume),
      q ∉ Z ×ˢ D → P q.1 q.2 = 0) :
    Integrable
      (Function.uncurry fun p : ((ℝ × ℝ) × ℝ) ↦ fun t : ℝ ↦
        P p.1 t * starRingEnd ℂ (P p.1 (t + p.2)))
      ((aux_dualPairMeasure.prod volume).prod volume) := by
  have hRmeas : Measurable
      (Function.uncurry fun p : ((ℝ × ℝ) × ℝ) ↦ fun t : ℝ ↦
        P p.1 t * starRingEnd ℂ (P p.1 (t + p.2))) := by
    have hleftmap : Measurable (fun p : ((ℝ × ℝ) × ℝ) × ℝ ↦ (p.1.1, p.2)) := by
      fun_prop
    have hrightmap : Measurable (fun p : ((ℝ × ℝ) × ℝ) × ℝ ↦
        (p.1.1, p.2 + p.1.2)) := by
      fun_prop
    have hleft : Measurable (fun p : ((ℝ × ℝ) × ℝ) × ℝ ↦ P p.1.1 p.2) :=
      hPmeas.comp hleftmap
    have hright : Measurable (fun p : ((ℝ × ℝ) × ℝ) × ℝ ↦
        P p.1.1 (p.2 + p.1.2)) := hPmeas.comp hrightmap
    change Measurable (fun p : ((ℝ × ℝ) × ℝ) × ℝ ↦
      P p.1.1 p.2 * starRingEnd ℂ (P p.1.1 (p.2 + p.1.2)))
    exact hleft.mul (Complex.continuous_conj.measurable.comp hright)
  have hRbound : ∀ᵐ p : ((ℝ × ℝ) × ℝ) × ℝ ∂
      ((aux_dualPairMeasure.prod volume).prod volume),
      ‖P p.1.1 p.2 * starRingEnd ℂ (P p.1.1 (p.2 + p.1.2))‖ ≤ 1 := by
    filter_upwards [aux_dual_qmp_shift_first_base.ae hPbound,
      aux_dual_qmp_shift_first_shifted.ae hPbound] with p hp₁ hp₂
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg (P p.1.1 p.2), norm_nonneg (P p.1.1 (p.2 + p.1.2))]
  let DD : Set ℝ := Set.image2 (fun d₁ d₂ : ℝ ↦ d₁ - d₂) D D
  let S : Set (((ℝ × ℝ) × ℝ) × ℝ) := (Z ×ˢ DD) ×ˢ D
  have hDD : IsCompact DD := by
    dsimp only [DD]
    exact aux_isCompact_image2_sub D hD
  have hS : IsCompact S := by
    dsimp only [S]
    exact (hZ.prod hDD).prod hD
  have hRsupp : ∀ᵐ p : ((ℝ × ℝ) × ℝ) × ℝ ∂
      ((aux_dualPairMeasure.prod volume).prod volume), p ∉ S →
        P p.1.1 p.2 * starRingEnd ℂ (P p.1.1 (p.2 + p.1.2)) = 0 := by
    filter_upwards [aux_dual_qmp_shift_first_base.ae hPsupp,
      aux_dual_qmp_shift_first_shifted.ae hPsupp] with p hp₁ hp₂
    intro hpS
    by_cases hleft : (p.1.1, p.2) ∈ Z ×ˢ D
    · by_cases hright : (p.1.1, p.2 + p.1.2) ∈ Z ×ˢ D
      · apply False.elim
        apply hpS
        dsimp only [S]
        refine ⟨?_, hleft.2⟩
        refine ⟨hleft.1, ?_⟩
        exact ⟨p.2 + p.1.2, hright.2, p.2, hleft.2, by ring⟩
      · simp [hp₂ hright]
    · simp [hp₁ hleft]
  change Integrable (fun p : ((ℝ × ℝ) × ℝ) × ℝ ↦
    P p.1.1 p.2 * starRingEnd ℂ (P p.1.1 (p.2 + p.1.2)))
    ((aux_dualPairMeasure.prod volume).prod volume)
  rw [← memLp_one_iff_integrable]
  exact aux_memLp_of_ae_bound_of_ae_support _ hRmeas.aestronglyMeasurable 1 hRbound S
    hS.isClosed.measurableSet hS.measure_lt_top hRsupp 1

/-- For \(\label{thm:dual-difference-interchange}\), this specializes the
shift-first autocorrelation integrability to the kernel `aux_dualP`. -/
lemma aux_dualP_autocorrelation_integrable_shift_first
    (A J D : Set ℝ) (hA : IsCompact A) (hJ : IsCompact J) (hD : IsCompact D)
    (Ft : ℝ → ℝ → ℂ) (χ ψ : ℝ → ℝ) (u : ℝ → ℂ)
    (hFtmeas : Measurable (Function.uncurry Ft))
    (hFtbound : ∀ t : ℝ, ∀ᵐ x ∂volume, ‖Ft t x‖ ≤ 1)
    (hFtsupport : ∀ t : ℝ, ∀ᵐ x ∂volume, x ∉ A → Ft t x = 0)
    (hχmeas : Measurable χ) (hχone : ∀ t : ℝ, χ t ≤ 1)
    (hχsupport : ∀ᵐ t ∂volume, t ∉ J → χ t = 0)
    (hψmeas : Measurable ψ) (humeas : Measurable u)
    (hubound : ∀ h : ℝ, ‖u h‖ ≤ 1)
    (husupport : ∀ h : ℝ, h ∉ D → u h = 0) :
    Integrable
      (Function.uncurry fun p : ((ℝ × ℝ) × ℝ) ↦ fun t : ℝ ↦
        aux_dualP Ft χ ψ u p.1 t *
          starRingEnd ℂ (aux_dualP Ft χ ψ u p.1 (t + p.2)))
      (((volume.prod volume).prod volume).prod volume) := by
  let X : Set ℝ := Set.image2 (fun a d : ℝ ↦ a - d) A D
  let Z : Set (ℝ × ℝ) := X ×ˢ J
  have hX : IsCompact X := by
    dsimp only [X]
    rw [← Set.image_prod]
    exact (hA.prod hD).image (continuous_fst.sub continuous_snd)
  have hZ : IsCompact Z := hX.prod hJ
  apply aux_autocorrelation_product_integrable_shift_first Z D hZ hD (aux_dualP Ft χ ψ u)
  · exact aux_dualP_measurable Ft χ ψ u hFtmeas hχmeas hψmeas humeas
  · exact aux_dualP_ae_one_bounded Ft χ ψ u hFtmeas hFtbound hχone hubound
  · simpa only [Z, X] using aux_dualP_ae_zero_outside A J D Ft χ ψ u
      hA.isClosed.measurableSet hFtmeas hFtsupport hχsupport husupport

/-- For \(\label{thm:dual-difference-interchange}\), this is the additive
law for the oscillatory phase. -/
lemma aux_phase_exponential_add (a b : ℝ) :
    exponential (a + b) = exponential a * exponential b := by
  unfold exponential
  rw [show (((2 * π * (a + b) : ℝ) : ℂ) * Complex.I) =
      ((2 * π * a : ℝ) : ℂ) * Complex.I +
        ((2 * π * b : ℝ) : ℂ) * Complex.I by
      push_cast
      ring]
  exact Complex.exp_add _ _

/-- For \(\label{thm:dual-difference-interchange}\), this conjugates the
oscillatory phase. -/
lemma aux_phase_star_exponential (a : ℝ) :
    starRingEnd ℂ (exponential a) = exponential (-a) := by
  unfold exponential
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- For \(\label{thm:dual-difference-interchange}\), this is the pointwise
post-autocorrelation factorization of `aux_dualP`. -/
lemma aux_dualP_autocorrelation_pointwise
    (Ft : ℝ → ℝ → ℂ) (χ ψ : ℝ → ℝ) (u : ℝ → ℂ)
    (hχ : ∀ t : ℝ, 0 ≤ χ t) (x t s r : ℝ) :
    aux_dualP Ft χ ψ u (x, t) s *
        starRingEnd ℂ (aux_dualP Ft χ ψ u (x, t) (s + r)) =
      (u s * starRingEnd ℂ (u (s + r)) *
        exponential (s * (ψ (s + r) - ψ s))) *
      starRingEnd ℂ
        (multiplicativeDifference r (Ft t) (x + s) *
          exponential ((x + s) * (ψ (s + r) - ψ s)) * (χ t : ℂ)) := by
  have hsqrt : ((Real.sqrt (χ t) : ℝ) : ℂ) * ((Real.sqrt (χ t) : ℝ) : ℂ) =
      (χ t : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (hχ t)
  rw [aux_dualP, aux_dualP]
  simp only [map_mul, aux_phase_star_exponential]
  have hphase :
      exponential (x * ψ s) * exponential (-(x * ψ (s + r))) =
        exponential (s * (ψ (s + r) - ψ s)) *
          exponential (-((x + s) * (ψ (s + r) - ψ s))) := by
    rw [← aux_phase_exponential_add, ← aux_phase_exponential_add]
    congr 1
    ring
  simp [Complex.star_def, multiplicativeDifference]
  calc
    _ =
        (((Real.sqrt (χ t) : ℝ) : ℂ) * ((Real.sqrt (χ t) : ℝ) : ℂ)) *
          (starRingEnd ℂ (Ft t (x + s)) * Ft t (x + (s + r))) *
          (exponential (x * ψ s) * exponential (-(x * ψ (s + r)))) *
          (u s * starRingEnd ℂ (u (s + r))) := by ring
    _ =
        (χ t : ℂ) *
          (starRingEnd ℂ (Ft t (x + s)) * Ft t (x + (s + r))) *
          (exponential (s * (ψ (s + r) - ψ s)) *
            exponential (-((x + s) * (ψ (s + r) - ψ s)))) *
          (u s * starRingEnd ℂ (u (s + r))) := by rw [hsqrt, hphase]
    _ = _ := by ring

/-- For \(\label{thm:dual-difference-interchange}\), this shows that a
multiplicative difference vanishes off the compact difference set.  It is
used to compactly support the selected phase in `dualDifferenceInterchange`. -/
lemma aux_difference_zero_off_difference
    (A : Set ℝ) (f : ℝ → ℂ)
    (hf_support : ∀ᵐ x ∂volume, x ∉ A → f x = 0)
    (h : ℝ) (hh : h ∉ Set.image2 (fun s t : ℝ ↦ s - t) A A) :
    multiplicativeDifference h f =ᵐ[volume] 0 := by
  have hshift_support : ∀ᵐ x ∂volume, x + h ∉ A → f (x + h) = 0 := by
    exact (measurePreserving_add_right volume h).quasiMeasurePreserving.ae hf_support
  filter_upwards [hf_support, hshift_support] with x hx hxshift
  dsimp [multiplicativeDifference]
  by_cases hxin : x ∈ A
  · by_cases hxhin : x + h ∈ A
    · exfalso
      apply hh
      exact ⟨x + h, hxhin, x, hxin, by ring⟩
    · simp [hxshift hxhin]
  · simp [hx hxin]

/-- For \(\label{thm:dual-difference-interchange}\), this is the Fourier
form of `aux_difference_zero_off_difference`, used to support the selected
phase in `dualDifferenceInterchange`. -/
lemma aux_fourier_difference_zero_off_difference
    (A : Set ℝ) (f : ℝ → ℂ)
    (hf_support : ∀ᵐ x ∂volume, x ∉ A → f x = 0)
    (h ξ : ℝ) (hh : h ∉ Set.image2 (fun s t : ℝ ↦ s - t) A A) :
    𝓕 (multiplicativeDifference h f) ξ = 0 := by
  have hzero := aux_difference_zero_off_difference A f hf_support h hh
  calc
    𝓕 (multiplicativeDifference h f) ξ = 𝓕 (0 : ℝ → ℂ) ξ :=
      Real.fourier_congr_ae hzero ξ
    _ = 0 := by
      rw [Real.fourier_eq]
      simp

/-- For \(\label{thm:dual-difference-interchange}\), this is the unit-norm
property of the exponential phase used in `dualDifferenceInterchange`. -/
lemma aux_norm_exponential (x : ℝ) : ‖exponential x‖ = 1 := by
  rw [exponential]
  exact Complex.norm_exp_ofReal_mul_I _

/-- For \(\label{thm:dual-difference-interchange}\), this proves compact
support integrability of the triple kernel occurring before the first
Cauchy--Schwarz step in `dualDifferenceInterchange`. -/
lemma aux_selector_phase_kernel_integrable
    (A J D : Set ℝ) (hA : IsCompact A) (hJ : IsCompact J) (hD : IsCompact D)
    (F : ℝ → ℂ) (Ft : ℝ → ℝ → ℂ) (χ : ℝ → ℝ)
    (φ : ℝ → ℝ) (u : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hFmeas : StronglyMeasurable F) (hFtmeas : Measurable (Function.uncurry Ft))
    (hχmeas : Measurable χ) (hφmeas : Measurable φ) (humeas : Measurable u)
    (hFbound : ∀ᵐ x : ℝ ∂volume, ‖F x‖ ≤ C)
    (hFsupp : ∀ᵐ x : ℝ ∂volume, x ∉ A → F x = 0)
    (hFtbound : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖Ft z.1 z.2‖ ≤ 1)
    (hχnonneg : ∀ t : ℝ, 0 ≤ χ t) (hχle : ∀ t : ℝ, χ t ≤ 1)
    (hχsupp : ∀ᵐ t : ℝ ∂volume, t ∉ J → χ t = 0)
    (hubound : ∀ᵐ h : ℝ ∂volume, ‖u h‖ ≤ 1)
    (husupp : ∀ᵐ h : ℝ ∂volume, h ∉ D → u h = 0) :
    Integrable
      (fun p : (ℝ × ℝ) × ℝ ↦
        F p.1.1 * (χ p.1.2 : ℂ) *
          (starRingEnd ℂ (Ft p.1.2 (p.1.1 + p.2)) *
            exponential (p.1.1 * φ p.2) * u p.2))
      ((volume.prod volume).prod volume) := by
  let K : (ℝ × ℝ) × ℝ → ℂ := fun p ↦
    F p.1.1 * (χ p.1.2 : ℂ) *
      (starRingEnd ℂ (Ft p.1.2 (p.1.1 + p.2)) *
        exponential (p.1.1 * φ p.2) * u p.2)
  have hF' : Measurable (fun p : (ℝ × ℝ) × ℝ ↦ F p.1.1) :=
    hFmeas.measurable.comp (measurable_fst.comp measurable_fst)
  have hχ' : Measurable (fun p : (ℝ × ℝ) × ℝ ↦ (χ p.1.2 : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      (hχmeas.comp (measurable_snd.comp measurable_fst))
  have hFt' : Measurable (fun p : (ℝ × ℝ) × ℝ ↦ Ft p.1.2 (p.1.1 + p.2)) :=
    hFtmeas.comp ((measurable_snd.comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_fst).add measurable_snd))
  have hphase : Measurable (fun p : (ℝ × ℝ) × ℝ ↦
      exponential (p.1.1 * φ p.2)) := by
    unfold exponential
    fun_prop
  have hu' : Measurable (fun p : (ℝ × ℝ) × ℝ ↦ u p.2) := humeas.comp measurable_snd
  have hKmeas : AEStronglyMeasurable K ((volume.prod volume).prod volume) := by
    dsimp [K]
    exact ((hF'.mul hχ').mul
      ((continuous_star.measurable.comp hFt').mul hphase |>.mul hu')).aestronglyMeasurable
  have hproj_xt : Measure.QuasiMeasurePreserving
      (fun p : (ℝ × ℝ) × ℝ ↦ p.1)
      ((volume.prod volume).prod volume) (volume.prod volume) :=
    Measure.quasiMeasurePreserving_fst
  have hproj_x : Measure.QuasiMeasurePreserving
      (fun p : (ℝ × ℝ) × ℝ ↦ p.1.1)
      ((volume.prod volume).prod volume) volume :=
    (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).comp hproj_xt
  have hproj_t : Measure.QuasiMeasurePreserving
      (fun p : (ℝ × ℝ) × ℝ ↦ p.1.2)
      ((volume.prod volume).prod volume) volume :=
    (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume)).comp hproj_xt
  have hproj_h : Measure.QuasiMeasurePreserving
      (fun p : (ℝ × ℝ) × ℝ ↦ p.2)
      ((volume.prod volume).prod volume) volume :=
    Measure.quasiMeasurePreserving_snd
  have hFbound' : ∀ᵐ p : (ℝ × ℝ) × ℝ ∂(volume.prod volume).prod volume,
      ‖F p.1.1‖ ≤ C := hproj_x.ae hFbound
  have hFtbound' : ∀ᵐ p : (ℝ × ℝ) × ℝ ∂(volume.prod volume).prod volume,
      ‖Ft p.1.2 (p.1.1 + p.2)‖ ≤ 1 :=
    aux_dualP_qmp_time_space_shift.ae hFtbound
  have hubound' : ∀ᵐ p : (ℝ × ℝ) × ℝ ∂(volume.prod volume).prod volume,
      ‖u p.2‖ ≤ 1 := hproj_h.ae hubound
  have hKbound : ∀ᵐ p : (ℝ × ℝ) × ℝ ∂(volume.prod volume).prod volume,
      ‖K p‖ ≤ C := by
    filter_upwards [hFbound', hFtbound', hubound'] with p hpF hpFt hpu
    dsimp [K]
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    change ‖F p.1.1‖ * ‖(χ p.1.2 : ℂ)‖ *
      (‖star (Ft p.1.2 (p.1.1 + p.2))‖ * ‖exponential (p.1.1 * φ p.2)‖ *
        ‖u p.2‖) ≤ C
    rw [norm_star, aux_norm_exponential]
    have hχnorm : ‖(χ p.1.2 : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχnonneg _)]
      exact hχle _
    calc
      ‖F p.1.1‖ * ‖(χ p.1.2 : ℂ)‖ *
          (‖Ft p.1.2 (p.1.1 + p.2)‖ * 1 * ‖u p.2‖) ≤
          C * 1 * (1 * 1 * 1) := by gcongr
      _ = C := by ring
  have hFsupp' : ∀ᵐ p : (ℝ × ℝ) × ℝ ∂(volume.prod volume).prod volume,
      p.1.1 ∉ A → F p.1.1 = 0 := hproj_x.ae hFsupp
  have hχsupp' : ∀ᵐ p : (ℝ × ℝ) × ℝ ∂(volume.prod volume).prod volume,
      p.1.2 ∉ J → χ p.1.2 = 0 := hproj_t.ae hχsupp
  have husupp' : ∀ᵐ p : (ℝ × ℝ) × ℝ ∂(volume.prod volume).prod volume,
      p.2 ∉ D → u p.2 = 0 := hproj_h.ae husupp
  let S : Set ((ℝ × ℝ) × ℝ) := (A ×ˢ J) ×ˢ D
  have hScompact : IsCompact S := by
    dsimp [S]
    exact (hA.prod hJ).prod hD
  have hSsupport : ∀ᵐ p : (ℝ × ℝ) × ℝ ∂(volume.prod volume).prod volume,
      p ∉ S → K p = 0 := by
    filter_upwards [hFsupp', hχsupp', husupp'] with p hpF hpχ hpu
    intro hp
    by_cases hx : p.1.1 ∈ A
    · by_cases ht : p.1.2 ∈ J
      · by_cases hh : p.2 ∈ D
        · exfalso
          apply hp
          change p.1 ∈ A ×ˢ J ∧ p.2 ∈ D
          exact ⟨⟨hx, ht⟩, hh⟩
        · simp [K, hpu hh]
      · simp [K, hpχ ht]
    · simp [K, hpF hx]
  have hmem : MemLp K 1 ((volume.prod volume).prod volume) :=
    aux_memLp_of_ae_bound_of_ae_support K hKmeas C hKbound S
      hScompact.isClosed.measurableSet hScompact.measure_lt_top hSsupport 1
  change Integrable K ((volume.prod volume).prod volume)
  exact memLp_one_iff_integrable.mp hmem

/-- For \(\label{thm:dual-difference-interchange}\), this Fubini identity
rewrites the selected Fourier phase pairing as the pair-indexed
Cauchy--Schwarz pairing used by `dualDifferenceInterchange`. -/
lemma aux_selector_phase_pairing_fubini
    (F : ℝ → ℂ) (Ft : ℝ → ℝ → ℂ) (χ : ℝ → ℝ)
    (φ : ℝ → ℝ) (u : ℝ → ℂ)
    (hF : ∀ x : ℝ, F x = ∫ t : ℝ, Ft t x * (χ t : ℂ))
    (hR : Integrable
      (fun p : (ℝ × ℝ) × ℝ ↦
        F p.1.1 * (χ p.1.2 : ℂ) *
          (starRingEnd ℂ (Ft p.1.2 (p.1.1 + p.2)) *
            exponential (p.1.1 * φ p.2) * u p.2))
      ((volume.prod volume).prod volume)) :
    (∫ h : ℝ,
      (∫ x : ℝ,
        multiplicativeDifference h F x * exponential (x * φ h)) * u h) =
      ∫ x : ℝ, ∫ t : ℝ, ∫ h : ℝ,
        F x * (χ t : ℂ) *
          (starRingEnd ℂ (Ft t (x + h)) * exponential (x * φ h) * u h) := by
  let R : ℝ → ℝ → ℝ → ℂ := fun x t h ↦
    F x * (χ t : ℂ) *
      (starRingEnd ℂ (Ft t (x + h)) * exponential (x * φ h) * u h)
  calc
    (∫ h : ℝ,
      (∫ x : ℝ,
        multiplicativeDifference h F x * exponential (x * φ h)) * u h) =
        ∫ h : ℝ, ∫ x : ℝ, ∫ t : ℝ, R x t h := by
      apply integral_congr_ae
      filter_upwards with h
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with x
      dsimp [multiplicativeDifference]
      calc
        F x * starRingEnd ℂ (F (x + h)) * exponential (x * φ h) * u h =
            F x * starRingEnd ℂ (∫ t : ℝ, Ft t (x + h) * (χ t : ℂ)) *
              exponential (x * φ h) * u h := by rw [hF (x + h)]
        _ = F x * (∫ t : ℝ, starRingEnd ℂ (Ft t (x + h) * (χ t : ℂ))) *
              exponential (x * φ h) * u h := by rw [← integral_conj]
        _ = (∫ t : ℝ, F x * starRingEnd ℂ (Ft t (x + h) * (χ t : ℂ))) *
              exponential (x * φ h) * u h := by rw [integral_const_mul]
        _ = (∫ t : ℝ, F x * starRingEnd ℂ (Ft t (x + h) * (χ t : ℂ))) *
              (exponential (x * φ h) * u h) := by ring
        _ = (∫ t : ℝ, F x * starRingEnd ℂ (Ft t (x + h) * (χ t : ℂ)) *
              (exponential (x * φ h) * u h)) := by rw [integral_mul_const]
        _ = ∫ t : ℝ, R x t h := by
          apply integral_congr_ae
          filter_upwards with t
          dsimp [R]
          rw [map_mul]
          simp only [Complex.conj_ofReal]
          ring
    _ = ∫ x : ℝ, ∫ t : ℝ, ∫ h : ℝ, R x t h := by
      simpa only [R] using (aux_triple_integral_swap R hR).symm

/-- For \(\label{thm:dual-difference-interchange}\), this is the
measure-space form of the squared Cauchy--Schwarz estimate used by
`dualDifferenceInterchange`. -/
lemma aux_dual_outer_cauchy_sq_of_energy_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f u : α → ℂ) (hf : MemLp f (2 : ℝ≥0∞) μ)
    (hu : MemLp u (2 : ℝ≥0∞) μ) (B : ℝ)
    (hB : (∫ x : α, ‖f x‖ ^ (2 : ℝ) ∂μ) ≤ B) :
    ‖∫ x : α, f x * u x ∂μ‖ ^ (2 : ℕ) ≤
      B * (∫ x : α, ‖u x‖ ^ (2 : ℝ) ∂μ) := by
  let F : ℝ := ∫ x : α, ‖f x‖ ^ (2 : ℝ) ∂μ
  let U : ℝ := ∫ x : α, ‖u x‖ ^ (2 : ℝ) ∂μ
  have hF0 : 0 ≤ F := integral_nonneg (fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)
  have hU0 : 0 ≤ U := integral_nonneg (fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)
  have hB0 : 0 ≤ B := hF0.trans hB
  have hFroot : F ^ (1 / (2 : ℝ)) ≤ B ^ (1 / (2 : ℝ)) :=
    Real.rpow_le_rpow hF0 hB (by norm_num)
  have hroot0 : 0 ≤ B ^ (1 / (2 : ℝ)) * U ^ (1 / (2 : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hU0 _)
  have hTbound : ‖∫ x : α, f x * u x ∂μ‖ ≤
      B ^ (1 / (2 : ℝ)) * U ^ (1 / (2 : ℝ)) := by
    calc
      ‖∫ x : α, f x * u x ∂μ‖ ≤ F ^ (1 / (2 : ℝ)) * U ^ (1 / (2 : ℝ)) := by
        have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by norm_num; exact hf
        have hu' : MemLp u (ENNReal.ofReal (2 : ℝ)) μ := by norm_num; exact hu
        calc
          ‖∫ x : α, f x * u x ∂μ‖ ≤ ∫ x : α, ‖f x * u x‖ ∂μ :=
            norm_integral_le_integral_norm _
          _ = ∫ x : α, ‖f x‖ * ‖u x‖ ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            rw [norm_mul]
          _ ≤ F ^ (1 / (2 : ℝ)) * U ^ (1 / (2 : ℝ)) := by
            simpa only [F, U] using
              integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hf' hu'
      _ ≤ B ^ (1 / (2 : ℝ)) * U ^ (1 / (2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hFroot (Real.rpow_nonneg hU0 _)
  calc
    ‖∫ x : α, f x * u x ∂μ‖ ^ (2 : ℕ) ≤
        (B ^ (1 / (2 : ℝ)) * U ^ (1 / (2 : ℝ))) ^ (2 : ℕ) :=
      (sq_le_sq₀ (norm_nonneg _) hroot0).mpr hTbound
    _ = B * U := by
      rw [mul_pow]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hB0]
      norm_num
      rw [← Real.rpow_natCast, ← Real.rpow_mul hU0]
      norm_num
    _ = B * (∫ x : α, ‖u x‖ ^ (2 : ℝ) ∂μ) := by rfl

/-- For \(\label{thm:dual-difference-interchange}\), this bounds the energy
of a bounded function by its finite support measure. -/
lemma aux_energy_le_measure_mul_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (S : Set α)
    (hS : MeasurableSet S) (hSfinite : μ S ≠ ∞)
    (f : α → ℂ) (hf : MemLp f (2 : ℝ≥0∞) μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ C)
    (hzero : ∀ᵐ x ∂μ, x ∉ S → f x = 0) :
    (∫ x : α, ‖f x‖ ^ (2 : ℝ) ∂μ) ≤ C ^ (2 : ℕ) * μ.real S := by
  have hfint : Integrable (fun x : α ↦ ‖f x‖ ^ (2 : ℝ)) μ := by
    convert hf.integrable_norm_rpow (by norm_num) (by norm_num) using 1
    norm_num
  have hind : Integrable (S.indicator (fun _ : α ↦ C ^ (2 : ℕ))) μ := by
    rw [integrable_indicator_iff hS]
    exact integrableOn_const hSfinite
  calc
    (∫ x : α, ‖f x‖ ^ (2 : ℝ) ∂μ) ≤
        ∫ x : α, S.indicator (fun _ : α ↦ C ^ (2 : ℕ)) x ∂μ := by
      apply integral_mono_ae hfint hind
      filter_upwards [hbound, hzero] with x hxbound hxzero
      by_cases hxS : x ∈ S
      · rw [Set.indicator_of_mem hxS, Real.rpow_two]
        nlinarith [norm_nonneg (f x)]
      · rw [Set.indicator_of_notMem hxS]
        simp [hxzero hxS]
    _ = C ^ (2 : ℕ) * μ.real S := by
      rw [integral_indicator_const _ hS]
      simp [smul_eq_mul, mul_comm]

/-- For \(\label{thm:dual-difference-interchange}\), this places the
square-root-cutoff outer factor in `L²` and bounds its energy. -/
lemma aux_weighted_average_factor_memLp_energy
    (A J : Set ℝ) (hA : IsCompact A) (hJ : IsCompact J)
    (F : ℝ → ℂ) (χ : ℝ → ℝ)
    (hFmeas : Measurable F)
    (hFbound : ∀ᵐ x : ℝ ∂volume, ‖F x‖ ≤ volume.real J)
    (hFsupp : ∀ᵐ x : ℝ ∂volume, x ∉ A → F x = 0)
    (hχmeas : Measurable χ) (hχone : ∀ t : ℝ, χ t ≤ 1)
    (hχsupport : ∀ᵐ t ∂volume, t ∉ J → χ t = 0) :
    MemLp (fun z : ℝ × ℝ ↦ F z.1 * ((Real.sqrt (χ z.2) : ℝ) : ℂ))
      (2 : ℝ≥0∞) (volume.prod volume) ∧
    (∫ z : ℝ × ℝ,
      ‖F z.1 * ((Real.sqrt (χ z.2) : ℝ) : ℂ)‖ ^ (2 : ℝ)
        ∂(volume.prod volume)) ≤
      volume.real A * (volume.real J) ^ (3 : ℕ) := by
  let W : ℝ × ℝ → ℂ := fun z ↦ F z.1 * ((Real.sqrt (χ z.2) : ℝ) : ℂ)
  have hWmeas : AEStronglyMeasurable W (volume.prod volume) := by
    have hleft : Measurable (fun z : ℝ × ℝ ↦ F z.1) := hFmeas.comp measurable_fst
    have hright : Measurable (fun z : ℝ × ℝ ↦
        ((Real.sqrt (χ z.2) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp ((hχmeas.comp measurable_snd).sqrt)
    exact (hleft.mul hright).aestronglyMeasurable
  have hWbound : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖W z‖ ≤ volume.real J := by
    have hFbound' : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
        ‖F z.1‖ ≤ volume.real J :=
      Measure.quasiMeasurePreserving_fst.ae hFbound
    filter_upwards [hFbound'] with z hz
    have hsqrt : ‖((Real.sqrt (χ z.2) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_one.mpr (hχone _)
    change ‖F z.1 * ((Real.sqrt (χ z.2) : ℝ) : ℂ)‖ ≤ volume.real J
    calc
      ‖F z.1 * ((Real.sqrt (χ z.2) : ℝ) : ℂ)‖ =
          ‖F z.1‖ * ‖((Real.sqrt (χ z.2) : ℝ) : ℂ)‖ := norm_mul _ _
      _ ≤ ‖F z.1‖ * 1 := mul_le_mul_of_nonneg_left hsqrt (norm_nonneg _)
      _ ≤ volume.real J * 1 := mul_le_mul_of_nonneg_right hz (by norm_num)
      _ = volume.real J := by ring
  have hWsupport : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∉ A ×ˢ J → W z = 0 := by
    have hF' : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
        z.1 ∉ A → F z.1 = 0 :=
      Measure.quasiMeasurePreserving_fst.ae hFsupp
    have hχ' : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
        z.2 ∉ J → χ z.2 = 0 :=
      Measure.quasiMeasurePreserving_snd.ae hχsupport
    filter_upwards [hF', hχ'] with z hzF hzχ hzout
    by_cases hx : z.1 ∈ A
    · by_cases ht : z.2 ∈ J
      · exact False.elim (hzout ⟨hx, ht⟩)
      · simp [W, hzχ ht]
    · simp [W, hzF hx]
  have hWmem : MemLp W (2 : ℝ≥0∞) (volume.prod volume) :=
    aux_memLp_of_ae_bound_of_ae_support W hWmeas (volume.real J) hWbound
      (A ×ˢ J) (hA.isClosed.measurableSet.prod hJ.isClosed.measurableSet)
      (hA.prod hJ).measure_lt_top hWsupport 2
  refine ⟨?_, ?_⟩
  · simpa only [W] using hWmem
  · have henergy := aux_energy_le_measure_mul_sq (volume.prod volume) (A ×ˢ J)
      (hA.isClosed.measurableSet.prod hJ.isClosed.measurableSet)
      (hA.prod hJ).measure_lt_top.ne W hWmem (volume.real J)
      MeasureTheory.measureReal_nonneg hWbound hWsupport
    have hbox : (volume.prod volume).real (A ×ˢ J) =
        volume.real A * volume.real J := by
      simp only [measureReal_prod_prod]
    calc
      (∫ z : ℝ × ℝ, ‖F z.1 * ((Real.sqrt (χ z.2) : ℝ) : ℂ)‖ ^ (2 : ℝ)
          ∂(volume.prod volume)) =
          ∫ z : ℝ × ℝ, ‖W z‖ ^ (2 : ℝ) ∂(volume.prod volume) := by rfl
      _ ≤ (volume.real J) ^ (2 : ℕ) * (volume.prod volume).real (A ×ˢ J) := henergy
      _ = volume.real A * (volume.real J) ^ (3 : ℕ) := by rw [hbox]; ring

/-- For \(\label{thm:dual-difference-interchange}\), this is the outer
Cauchy--Schwarz estimate after splitting the cutoff into square roots. -/
lemma aux_first_physical_cauchy_sq
    (A J : Set ℝ) (hA : IsCompact A) (hJ : IsCompact J)
    (F : ℝ → ℂ) (χ : ℝ → ℝ) (H : ℝ × ℝ → ℂ)
    (hFmeas : Measurable F)
    (hFbound : ∀ᵐ x : ℝ ∂volume, ‖F x‖ ≤ volume.real J)
    (hFsupp : ∀ᵐ x : ℝ ∂volume, x ∉ A → F x = 0)
    (hχmeas : Measurable χ) (hχone : ∀ t : ℝ, χ t ≤ 1)
    (hχsupport : ∀ᵐ t ∂volume, t ∉ J → χ t = 0)
    (hH : MemLp H (2 : ℝ≥0∞) (volume.prod volume)) :
    ‖∫ z : ℝ × ℝ,
      (F z.1 * ((Real.sqrt (χ z.2) : ℝ) : ℂ)) * H z
        ∂(volume.prod volume)‖ ^ (2 : ℕ) ≤
      volume.real A * (volume.real J) ^ (3 : ℕ) *
        ∫ z : ℝ × ℝ, ‖H z‖ ^ (2 : ℝ) ∂(volume.prod volume) := by
  obtain ⟨hW, henergy⟩ := aux_weighted_average_factor_memLp_energy A J hA hJ F χ
    hFmeas hFbound hFsupp hχmeas hχone hχsupport
  exact aux_dual_outer_cauchy_sq_of_energy_bound (volume.prod volume)
    (fun z : ℝ × ℝ ↦ F z.1 * ((Real.sqrt (χ z.2) : ℝ) : ℂ)) H hW hH
    (volume.real A * (volume.real J) ^ (3 : ℕ)) henergy

/-- For \(\label{thm:dual-difference-interchange}\), this identifies the
square-root-cutoff Cauchy--Schwarz factors with the original triple kernel. -/
lemma aux_sqrt_weighted_dualP_pointwise
    (F : ℝ → ℂ) (Ft : ℝ → ℝ → ℂ) (χ φ : ℝ → ℝ) (u : ℝ → ℂ)
    (hχnonneg : ∀ t : ℝ, 0 ≤ χ t) (x t h : ℝ) :
    (F x * ((Real.sqrt (χ t) : ℝ) : ℂ)) * aux_dualP Ft χ φ u (x, t) h =
      F x * (χ t : ℂ) *
        (starRingEnd ℂ (Ft t (x + h)) * exponential (x * φ h) * u h) := by
  have hsquare : ((Real.sqrt (χ t) : ℝ) : ℂ) *
      ((Real.sqrt (χ t) : ℝ) : ℂ) = (χ t : ℂ) := by
    rw [← Complex.ofReal_mul]
    exact_mod_cast Real.mul_self_sqrt (hχnonneg t)
  simp only [aux_dualP]
  calc
    F x * ((Real.sqrt (χ t) : ℝ) : ℂ) *
        (((Real.sqrt (χ t) : ℝ) : ℂ) * starRingEnd ℂ (Ft t (x + h)) *
          exponential (x * φ h) * u h) =
        F x * (((Real.sqrt (χ t) : ℝ) : ℂ) * ((Real.sqrt (χ t) : ℝ) : ℂ)) *
          (starRingEnd ℂ (Ft t (x + h)) * exponential (x * φ h) * u h) := by ring
    _ = F x * (χ t : ℂ) *
          (starRingEnd ℂ (Ft t (x + h)) * exponential (x * φ h) * u h) := by
      rw [hsquare]

/-- For \(\label{thm:dual-difference-interchange}\), this rewrites the
selected Fourier pairing in the square-root-cutoff form used for Cauchy--Schwarz. -/
lemma aux_selector_pairing_eq_sqrt_pairing
    (F : ℝ → ℂ) (Ft : ℝ → ℝ → ℂ) (χ φ : ℝ → ℝ) (u : ℝ → ℂ)
    (hF : ∀ x : ℝ, F x = ∫ t : ℝ, Ft t x * (χ t : ℂ))
    (hχnonneg : ∀ t : ℝ, 0 ≤ χ t)
    (hR : Integrable
      (fun p : (ℝ × ℝ) × ℝ ↦
        F p.1.1 * (χ p.1.2 : ℂ) *
          (starRingEnd ℂ (Ft p.1.2 (p.1.1 + p.2)) *
            exponential (p.1.1 * φ p.2) * u p.2))
      ((volume.prod volume).prod volume)) :
    (∫ h : ℝ,
      (∫ x : ℝ, multiplicativeDifference h F x * exponential (x * φ h)) * u h) =
      ∫ z : ℝ × ℝ,
        (F z.1 * ((Real.sqrt (χ z.2) : ℝ) : ℂ)) *
          (∫ h : ℝ, aux_dualP Ft χ φ u z h) ∂(volume.prod volume) := by
  let R : ℝ → ℝ → ℝ → ℂ := fun x t h ↦
    F x * (χ t : ℂ) *
      (starRingEnd ℂ (Ft t (x + h)) * exponential (x * φ h) * u h)
  let W : ℝ × ℝ → ℂ := fun z ↦ F z.1 * ((Real.sqrt (χ z.2) : ℝ) : ℂ)
  let P : (ℝ × ℝ) → ℝ → ℂ := aux_dualP Ft χ φ u
  have hR' : Integrable (Function.uncurry (fun z : ℝ × ℝ ↦ fun h : ℝ ↦
      W z * P z h)) ((volume.prod volume).prod volume) := by
    have heq : (Function.uncurry (fun z : ℝ × ℝ ↦ fun h : ℝ ↦ W z * P z h)) =
        (fun p : (ℝ × ℝ) × ℝ ↦
          F p.1.1 * (χ p.1.2 : ℂ) *
            (starRingEnd ℂ (Ft p.1.2 (p.1.1 + p.2)) *
              exponential (p.1.1 * φ p.2) * u p.2)) := by
      funext p
      rcases p with ⟨⟨x, t⟩, h⟩
      dsimp only [W, P]
      change (F x * ((Real.sqrt (χ t) : ℝ) : ℂ)) * aux_dualP Ft χ φ u (x, t) h =
        F x * (χ t : ℂ) *
          (starRingEnd ℂ (Ft t (x + h)) * exponential (x * φ h) * u h)
      exact aux_sqrt_weighted_dualP_pointwise F Ft χ φ u hχnonneg x t h
    rw [heq]
    exact hR
  have hQ : Integrable (fun z : ℝ × ℝ ↦ ∫ h : ℝ, R z.1 z.2 h)
      (volume.prod volume) := by
    simpa only [R] using hR.integral_prod_left
  calc
    (∫ h : ℝ,
      (∫ x : ℝ, multiplicativeDifference h F x * exponential (x * φ h)) * u h) =
        ∫ x : ℝ, ∫ t : ℝ, ∫ h : ℝ, R x t h := by
          simpa only [R] using aux_selector_phase_pairing_fubini F Ft χ φ u hF hR
    _ = ∫ z : ℝ × ℝ, ∫ h : ℝ, R z.1 z.2 h ∂volume ∂(volume.prod volume) := by
      simpa only using (integral_prod (fun z : ℝ × ℝ ↦ ∫ h : ℝ, R z.1 z.2 h) hQ).symm
    _ = ∫ z : ℝ × ℝ, ∫ h : ℝ, W z * P z h ∂volume ∂(volume.prod volume) := by
      apply integral_congr_ae
      filter_upwards with z
      apply integral_congr_ae
      filter_upwards with h
      rcases z with ⟨x, t⟩
      exact (aux_sqrt_weighted_dualP_pointwise F Ft χ φ u hχnonneg x t h).symm
    _ = ∫ z : ℝ × ℝ, W z * (∫ h : ℝ, P z h) ∂(volume.prod volume) := by
      apply integral_congr_ae
      filter_upwards [hR'.prod_right_ae] with z hz
      rw [integral_const_mul]
    _ = ∫ z : ℝ × ℝ,
        (F z.1 * ((Real.sqrt (χ z.2) : ℝ) : ℂ)) *
          (∫ h : ℝ, aux_dualP Ft χ φ u z h) ∂(volume.prod volume) := by
      rfl

/-- For \(\label{thm:dual-difference-interchange}\), this is the first
physical Cauchy--Schwarz estimate for the selected phase. -/
lemma aux_first_physical_cauchy_sq_with_dualP
    (A J : Set ℝ) (hA : IsCompact A) (hJ : IsCompact J)
    (F : ℝ → ℂ) (Ft : ℝ → ℝ → ℂ) (χ φ : ℝ → ℝ) (u : ℝ → ℂ)
    (hFmeas : Measurable F)
    (hFbound : ∀ᵐ x : ℝ ∂volume, ‖F x‖ ≤ volume.real J)
    (hFsupp : ∀ᵐ x : ℝ ∂volume, x ∉ A → F x = 0)
    (hχmeas : Measurable χ) (hχnonneg : ∀ t : ℝ, 0 ≤ χ t)
    (hχone : ∀ t : ℝ, χ t ≤ 1)
    (hχsupport : ∀ᵐ t ∂volume, t ∉ J → χ t = 0)
    (hF : ∀ x : ℝ, F x = ∫ t : ℝ, Ft t x * (χ t : ℂ))
    (hR : Integrable
      (fun p : (ℝ × ℝ) × ℝ ↦
        F p.1.1 * (χ p.1.2 : ℂ) *
          (starRingEnd ℂ (Ft p.1.2 (p.1.1 + p.2)) *
            exponential (p.1.1 * φ p.2) * u p.2))
      ((volume.prod volume).prod volume))
    (hH : MemLp (fun z : ℝ × ℝ ↦ ∫ h : ℝ, aux_dualP Ft χ φ u z h)
      (2 : ℝ≥0∞) (volume.prod volume)) :
    ‖∫ h : ℝ,
      (∫ x : ℝ, multiplicativeDifference h F x * exponential (x * φ h)) * u h‖ ^ (2 : ℕ) ≤
      volume.real A * (volume.real J) ^ (3 : ℕ) *
        ∫ z : ℝ × ℝ, ‖∫ h : ℝ, aux_dualP Ft χ φ u z h‖ ^ (2 : ℝ)
          ∂(volume.prod volume) := by
  have hpair := aux_selector_pairing_eq_sqrt_pairing F Ft χ φ u hF hχnonneg hR
  have hcauchy := aux_first_physical_cauchy_sq A J hA hJ F χ
    (fun z : ℝ × ℝ ↦ ∫ h : ℝ, aux_dualP Ft χ φ u z h)
    hFmeas hFbound hFsupp hχmeas hχone hχsupport hH
  rw [← hpair] at hcauchy
  exact hcauchy

/-- For \(\label{thm:dual-difference-interchange}\), this is the exact
fixed-base change of variables from an autocorrelation of `aux_dualP` to the
target difference integral. -/
lemma aux_dualP_autocorrelation_target_integral
    (Ft : ℝ → ℝ → ℂ) (χ ψ : ℝ → ℝ) (u : ℝ → ℂ)
    (hχ : ∀ t : ℝ, 0 ≤ χ t) (s r : ℝ) :
    (∫ x : ℝ, ∫ t : ℝ,
      aux_dualP Ft χ ψ u (x, t) s *
        starRingEnd ℂ (aux_dualP Ft χ ψ u (x, t) (s + r))) =
      (u s * starRingEnd ℂ (u (s + r)) *
        exponential (s * (ψ (s + r) - ψ s))) *
      starRingEnd ℂ (∫ x : ℝ, ∫ t : ℝ,
        multiplicativeDifference r (Ft t) x *
          exponential (x * (ψ (s + r) - ψ s)) * (χ t : ℂ)) := by
  let c : ℂ := u s * starRingEnd ℂ (u (s + r)) *
    exponential (s * (ψ (s + r) - ψ s))
  let R : ℝ → ℝ → ℂ := fun x t ↦
    multiplicativeDifference r (Ft t) x *
      exponential (x * (ψ (s + r) - ψ s)) * (χ t : ℂ)
  calc
    (∫ x : ℝ, ∫ t : ℝ,
      aux_dualP Ft χ ψ u (x, t) s *
        starRingEnd ℂ (aux_dualP Ft χ ψ u (x, t) (s + r))) =
        ∫ x : ℝ, ∫ t : ℝ, c * starRingEnd ℂ (R (x + s) t) := by
      apply integral_congr_ae
      filter_upwards with x
      apply integral_congr_ae
      filter_upwards with t
      simpa only [c, R] using
        aux_dualP_autocorrelation_pointwise Ft χ ψ u hχ x t s r
    _ = ∫ x : ℝ, c * ∫ t : ℝ, starRingEnd ℂ (R (x + s) t) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [integral_const_mul]
    _ = c * ∫ x : ℝ, ∫ t : ℝ, starRingEnd ℂ (R (x + s) t) := by
      rw [integral_const_mul]
    _ = c * ∫ x : ℝ, starRingEnd ℂ (∫ t : ℝ, R (x + s) t) := by
      apply congrArg (fun q : ℂ ↦ c * q)
      apply integral_congr_ae
      filter_upwards with x
      rw [integral_conj]
    _ = c * starRingEnd ℂ (∫ x : ℝ, ∫ t : ℝ, R (x + s) t) := by
      rw [← integral_conj]
    _ = c * starRingEnd ℂ (∫ x : ℝ, ∫ t : ℝ, R x t) := by
      rw [integral_add_right_eq_self (fun x : ℝ ↦ ∫ t : ℝ, R x t) s]
    _ = _ := by rfl

/- For \(\label{thm:dual-difference-interchange}\), Fubini and the triangle
inequality turn a fixed-fibre factorization into an outer integral norm bound. -/
/-- For thm:dual-difference-interchange, this proves measurability, a uniform
bound, and integrability of a compactly base-restricted target fibre. -/
lemma aux_target_indicator_properties
    (A J D : Set ℝ) (hA : IsCompact A) (hJ : IsCompact J) (hD : IsCompact D)
    (Ft : ℝ → ℝ → ℂ) (χ ψ : ℝ → ℝ)
    (hFtmeas : Measurable (Function.uncurry Ft))
    (hFtbound : ∀ t : ℝ, ∀ᵐ x : ℝ ∂volume, ‖Ft t x‖ ≤ 1)
    (hFtsupport : ∀ t : ℝ, ∀ᵐ x : ℝ ∂volume, x ∉ A → Ft t x = 0)
    (hχmeas : Measurable χ) (hχnonneg : ∀ t : ℝ, 0 ≤ χ t)
    (hχone : ∀ t : ℝ, χ t ≤ 1)
    (hχsupport : ∀ᵐ t : ℝ ∂volume, t ∉ J → χ t = 0)
    (hψmeas : Measurable ψ) (r : ℝ) :
    Measurable (D.indicator (fun s : ℝ ↦
      ∫ x : ℝ, ∫ t : ℝ,
        multiplicativeDifference r (Ft t) x *
          exponential (x * (ψ (s + r) - ψ s)) * (χ t : ℂ))) ∧
    (∀ s : ℝ, ‖D.indicator (fun s : ℝ ↦
      ∫ x : ℝ, ∫ t : ℝ,
        multiplicativeDifference r (Ft t) x *
          exponential (x * (ψ (s + r) - ψ s)) * (χ t : ℂ)) s‖ ≤
      volume.real A * volume.real J) ∧
    Integrable (D.indicator (fun s : ℝ ↦
      ∫ x : ℝ, ∫ t : ℝ,
        multiplicativeDifference r (Ft t) x *
          exponential (x * (ψ (s + r) - ψ s)) * (χ t : ℂ))) volume := by
  let R : ℝ → ℝ → ℝ → ℂ := fun s x t ↦
    multiplicativeDifference r (Ft t) x *
      exponential (x * (ψ (s + r) - ψ s)) * (χ t : ℂ)
  let T : ℝ → ℂ := fun s ↦ ∫ x : ℝ, ∫ t : ℝ, R s x t
  have hQ := aux_dualKernel_properties A J hA.isClosed.measurableSet Ft hFtmeas
    hFtbound hFtsupport χ hχmeas hχnonneg hχone hχsupport
  rcases hQ with ⟨hQmeas, hQbound, hQsupport⟩
  have hshiftSet : MeasurableSet {z : ℝ × ℝ | ‖Ft z.1 (z.2 + r)‖ ≤ 1} := by
    exact measurableSet_le
      (hFtmeas.comp (measurable_fst.prodMk (measurable_snd.add measurable_const))).norm
      measurable_const
  have hshiftTx : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      ‖Ft z.1 (z.2 + r)‖ ≤ 1 := by
    rw [Measure.ae_prod_iff_ae_ae hshiftSet]
    filter_upwards with t
    simpa using (measurePreserving_add_right volume r).quasiMeasurePreserving.ae (hFtbound t)
  have hshiftbound : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      ‖Ft z.2 (z.1 + r)‖ ≤ 1 := by
    simpa [Function.comp_def] using
      Measure.measurePreserving_swap.quasiMeasurePreserving.ae hshiftTx
  have hQbound' : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      ‖aux_dualKernel Ft χ z.1 z.2‖ ≤ 1 := hQbound
  have hQsupport' : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∉ A ×ˢ J → aux_dualKernel Ft χ z.1 z.2 = 0 := hQsupport
  have hRmeas : Measurable
      (Function.uncurry fun sx : ℝ × ℝ ↦ fun t : ℝ ↦ R sx.1 sx.2 t) := by
    have hbase : Measurable (fun p : (ℝ × ℝ) × ℝ ↦ Ft p.2 p.1.2) :=
      hFtmeas.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    have hshift : Measurable (fun p : (ℝ × ℝ) × ℝ ↦ Ft p.2 (p.1.2 + r)) :=
      hFtmeas.comp (measurable_snd.prodMk
        ((measurable_snd.comp measurable_fst).add measurable_const))
    have hphase : Measurable (fun p : (ℝ × ℝ) × ℝ ↦
        exponential (p.1.2 * (ψ (p.1.1 + r) - ψ p.1.1))) := by
      unfold exponential
      fun_prop
    have hchi : Measurable (fun p : (ℝ × ℝ) × ℝ ↦ (χ p.2 : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (hχmeas.comp measurable_snd)
    change Measurable (fun p : (ℝ × ℝ) × ℝ ↦
      (Ft p.2 p.1.2 * starRingEnd ℂ (Ft p.2 (p.1.2 + r))) *
        exponential (p.1.2 * (ψ (p.1.1 + r) - ψ p.1.1)) * (χ p.2 : ℂ))
    exact ((hbase.mul (Complex.continuous_conj.measurable.comp hshift)).mul hphase).mul hchi
  have hTmeas : StronglyMeasurable T := by
    exact hRmeas.stronglyMeasurable.integral_prod_right'.integral_prod_right'
  have hboxmeas : MeasurableSet (A ×ˢ J) :=
    hA.isClosed.measurableSet.prod hJ.isClosed.measurableSet
  have hboxfinite : (volume.prod volume) (A ×ˢ J) < ∞ := (hA.prod hJ).measure_lt_top
  have hboxint : Integrable ((A ×ˢ J).indicator (1 : ℝ × ℝ → ℝ))
      (volume.prod volume) := by
    rw [← memLp_one_iff_integrable]
    exact memLp_indicator_const 1 hboxmeas 1 (Or.inr hboxfinite.ne)
  have hRbound (s : ℝ) : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      ‖R s z.1 z.2‖ ≤ 1 := by
    filter_upwards [hshiftbound, hQbound'] with z hzshift hzQ
    change ‖(Ft z.2 z.1 * starRingEnd ℂ (Ft z.2 (z.1 + r))) *
      exponential (z.1 * (ψ (s + r) - ψ s)) * (χ z.2 : ℂ)‖ ≤ 1
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, aux_norm_exponential]
    have hq : ‖Ft z.2 z.1‖ * ‖(χ z.2 : ℂ)‖ ≤ 1 := by
      simpa only [aux_dualKernel, norm_mul] using hzQ
    calc
      ‖Ft z.2 z.1‖ * ‖Ft z.2 (z.1 + r)‖ * 1 * ‖(χ z.2 : ℂ)‖ =
          ‖Ft z.2 (z.1 + r)‖ * (‖Ft z.2 z.1‖ * ‖(χ z.2 : ℂ)‖) := by ring
      _ ≤ 1 * 1 := mul_le_mul hzshift hq
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
      _ = 1 := by norm_num
  have hRsupport (s : ℝ) : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∉ A ×ˢ J → R s z.1 z.2 = 0 := by
    filter_upwards [hQsupport'] with z hzQ
    intro hz
    change (Ft z.2 z.1 * starRingEnd ℂ (Ft z.2 (z.1 + r))) *
      exponential (z.1 * (ψ (s + r) - ψ s)) * (χ z.2 : ℂ) = 0
    have hzero : Ft z.2 z.1 * (χ z.2 : ℂ) = 0 := by
      simpa only [aux_dualKernel] using hzQ hz
    calc
      (Ft z.2 z.1 * starRingEnd ℂ (Ft z.2 (z.1 + r))) *
          exponential (z.1 * (ψ (s + r) - ψ s)) * (χ z.2 : ℂ) =
          (Ft z.2 z.1 * (χ z.2 : ℂ)) *
            (starRingEnd ℂ (Ft z.2 (z.1 + r)) *
              exponential (z.1 * (ψ (s + r) - ψ s))) := by ring
      _ = 0 := by rw [hzero, zero_mul]
  have hRint (s : ℝ) : Integrable (fun z : ℝ × ℝ ↦ R s z.1 z.2)
      (volume.prod volume) := by
    rw [← memLp_one_iff_integrable]
    apply aux_memLp_of_ae_bound_of_ae_support _
      ((hRmeas.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).aestronglyMeasurable)
      1 (hRbound s) (A ×ˢ J) hboxmeas hboxfinite (hRsupport s) 1
  have hTbound (s : ℝ) : ‖T s‖ ≤ volume.real A * volume.real J := by
    calc
      ‖T s‖ = ‖∫ z : ℝ × ℝ, R s z.1 z.2 ∂volume.prod volume‖ := by
        exact congrArg norm (integral_prod (fun z : ℝ × ℝ ↦ R s z.1 z.2) (hRint s)).symm
      _ ≤ ∫ z : ℝ × ℝ, ‖R s z.1 z.2‖ ∂volume.prod volume :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ z : ℝ × ℝ, (A ×ˢ J).indicator (1 : ℝ × ℝ → ℝ) z
          ∂volume.prod volume := by
        apply integral_mono_ae (hRint s).norm hboxint
        filter_upwards [hRbound s, hRsupport s] with z hzbound hzsupport
        by_cases hz : z ∈ A ×ˢ J
        · simp [hz, hzbound]
        · simp [hz, hzsupport hz]
      _ = volume.real A * volume.real J := by
        have hprod : (volume.prod volume).real (A ×ˢ J) =
            volume.real A * volume.real J := by
          simp only [measureReal_prod_prod]
        calc
          (∫ z : ℝ × ℝ, (A ×ˢ J).indicator (1 : ℝ × ℝ → ℝ) z
              ∂volume.prod volume) = (volume.prod volume).real (A ×ˢ J) := by
                simpa only [Measure.real] using
                  (integral_indicator_one (μ := volume.prod volume) hboxmeas)
          _ = volume.real A * volume.real J := hprod
  have hVindmeas : Measurable (D.indicator T) :=
    hTmeas.measurable.indicator hD.isClosed.measurableSet
  have hVindbound : ∀ s : ℝ, ‖D.indicator T s‖ ≤ volume.real A * volume.real J := by
    intro s
    by_cases hs : s ∈ D
    · simpa [hs] using hTbound s
    · calc
        ‖D.indicator T s‖ = 0 := by simp [hs]
        _ ≤ volume.real A * volume.real J :=
          mul_nonneg MeasureTheory.measureReal_nonneg MeasureTheory.measureReal_nonneg
  have hVindsupp : ∀ᵐ s : ℝ ∂volume, s ∉ D → D.indicator T s = 0 := by
    filter_upwards with s hs
    simp [hs]
  have hVindint : Integrable (D.indicator T) volume := by
    rw [← memLp_one_iff_integrable]
    exact aux_memLp_of_ae_bound_of_ae_support _ hVindmeas.aestronglyMeasurable
      (volume.real A * volume.real J) (Filter.Eventually.of_forall hVindbound)
      D hD.isClosed.measurableSet hD.measure_lt_top hVindsupp 1
  refine ⟨?_, ?_, ?_⟩
  · simpa only [T, R] using hVindmeas
  · simpa only [T, R] using hVindbound
  · simpa only [T, R] using hVindint

/-- For thm:dual-difference-interchange, this gives joint integrability of
the base-restricted target and its compact support in the difference variable. -/
lemma aux_target_indicator_joint_integrable
    (A J D : Set ℝ) (hA : IsCompact A) (hJ : IsCompact J) (hD : IsCompact D)
    (Ft : ℝ → ℝ → ℂ) (χ ψ : ℝ → ℝ)
    (hFtmeas : Measurable (Function.uncurry Ft))
    (hFtbound : ∀ t : ℝ, ∀ᵐ x : ℝ ∂volume, ‖Ft t x‖ ≤ 1)
    (hFtsupport : ∀ t : ℝ, ∀ᵐ x : ℝ ∂volume, x ∉ A → Ft t x = 0)
    (hχmeas : Measurable χ) (hχnonneg : ∀ t : ℝ, 0 ≤ χ t)
    (hχone : ∀ t : ℝ, χ t ≤ 1)
    (hχsupport : ∀ᵐ t : ℝ ∂volume, t ∉ J → χ t = 0)
    (hψmeas : Measurable ψ) :
    Measurable (Function.uncurry fun r s : ℝ ↦ D.indicator (fun s : ℝ ↦
      ∫ x : ℝ, ∫ t : ℝ,
        multiplicativeDifference r (Ft t) x *
          exponential (x * (ψ (s + r) - ψ s)) * (χ t : ℂ)) s) ∧
    (∀ r s : ℝ, ‖D.indicator (fun s : ℝ ↦
      ∫ x : ℝ, ∫ t : ℝ,
        multiplicativeDifference r (Ft t) x *
          exponential (x * (ψ (s + r) - ψ s)) * (χ t : ℂ)) s‖ ≤
      volume.real A * volume.real J) ∧
    Integrable (Function.uncurry fun r s : ℝ ↦ D.indicator (fun s : ℝ ↦
      ∫ x : ℝ, ∫ t : ℝ,
        multiplicativeDifference r (Ft t) x *
          exponential (x * (ψ (s + r) - ψ s)) * (χ t : ℂ)) s)
      (volume.prod volume) ∧
    (∀ᵐ p : ℝ × ℝ ∂volume.prod volume,
      p.2 ∉ D → D.indicator (fun s : ℝ ↦
        ∫ x : ℝ, ∫ t : ℝ,
          multiplicativeDifference p.1 (Ft t) x *
            exponential (x * (ψ (s + p.1) - ψ s)) * (χ t : ℂ)) p.2 = 0) := by
  let Raw : ℝ → ℝ → ℂ := fun r s ↦
    ∫ x : ℝ, ∫ t : ℝ,
      multiplicativeDifference r (Ft t) x *
        exponential (x * (ψ (s + r) - ψ s)) * (χ t : ℂ)
  let U : ℝ × ℝ → ℂ := (Prod.snd ⁻¹' D).indicator (Function.uncurry Raw)
  have hKernelMeas : Measurable
      (Function.uncurry fun rsx : (ℝ × ℝ) × ℝ ↦ fun t : ℝ ↦
        multiplicativeDifference rsx.1.1 (Ft t) rsx.2 *
          exponential (rsx.2 * (ψ (rsx.1.2 + rsx.1.1) - ψ rsx.1.2)) * (χ t : ℂ)) := by
    have hbase : Measurable (fun p : ((ℝ × ℝ) × ℝ) × ℝ ↦ Ft p.2 p.1.2) :=
      hFtmeas.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    have hshift : Measurable (fun p : ((ℝ × ℝ) × ℝ) × ℝ ↦
        Ft p.2 (p.1.2 + p.1.1.1)) :=
      hFtmeas.comp (measurable_snd.prodMk
        ((measurable_snd.comp measurable_fst).add
          (measurable_fst.comp (measurable_fst.comp measurable_fst))))
    have hphase : Measurable (fun p : ((ℝ × ℝ) × ℝ) × ℝ ↦
        exponential (p.1.2 * (ψ (p.1.1.2 + p.1.1.1) - ψ p.1.1.2))) := by
      unfold exponential
      fun_prop
    have hchi : Measurable (fun p : ((ℝ × ℝ) × ℝ) × ℝ ↦ (χ p.2 : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (hχmeas.comp measurable_snd)
    change Measurable (fun p : ((ℝ × ℝ) × ℝ) × ℝ ↦
      (Ft p.2 p.1.2 * starRingEnd ℂ (Ft p.2 (p.1.2 + p.1.1.1))) *
        exponential (p.1.2 * (ψ (p.1.1.2 + p.1.1.1) - ψ p.1.1.2)) * (χ p.2 : ℂ))
    exact ((hbase.mul (Complex.continuous_conj.measurable.comp hshift)).mul hphase).mul hchi
  have hRawMeas : StronglyMeasurable (Function.uncurry Raw) := by
    exact hKernelMeas.stronglyMeasurable.integral_prod_right'.integral_prod_right'
  have hUmeas : Measurable U := by
    exact hRawMeas.measurable.indicator
      (hD.isClosed.measurableSet.preimage measurable_snd)
  have hU_apply (r s : ℝ) : U (r, s) = D.indicator (Raw r) s := by
    by_cases hs : s ∈ D <;> simp [U, hs]
  have hUbound : ∀ p : ℝ × ℝ, ‖U p‖ ≤ volume.real A * volume.real J := by
    intro p
    obtain ⟨_, hbound, _⟩ := aux_target_indicator_properties A J D hA hJ hD Ft χ ψ
      hFtmeas hFtbound hFtsupport hχmeas hχnonneg hχone hχsupport hψmeas p.1
    rw [hU_apply p.1 p.2]
    simpa only [Raw] using hbound p.2
  let E : Set ℝ := Set.image2 (fun a b : ℝ ↦ a - b) A A
  have hEcompact : IsCompact E := by
    dsimp only [E]
    exact aux_isCompact_image2_sub A hA
  have hRawzero (r s : ℝ) (hr : r ∉ E) : Raw r s = 0 := by
    have hdiffMeas : Measurable (fun q : ℝ × ℝ ↦
        multiplicativeDifference r (Ft q.1) q.2) := by
      change Measurable (fun q : ℝ × ℝ ↦
        Ft q.1 q.2 * starRingEnd ℂ (Ft q.1 (q.2 + r)))
      exact hFtmeas.mul (Complex.continuous_conj.measurable.comp
        (hFtmeas.comp (measurable_fst.prodMk (measurable_snd.add measurable_const))))
    have hdiffSet : MeasurableSet {q : ℝ × ℝ |
        multiplicativeDifference r (Ft q.1) q.2 = 0} :=
      (measurableSet_singleton (0 : ℂ)).preimage hdiffMeas
    have hdiffTx : ∀ᵐ q : ℝ × ℝ ∂volume.prod volume,
        multiplicativeDifference r (Ft q.1) q.2 = 0 := by
      rw [Measure.ae_prod_iff_ae_ae hdiffSet]
      filter_upwards with t
      exact aux_difference_zero_off_difference A (Ft t) (hFtsupport t) r hr
    have hdiffXt : ∀ᵐ q : ℝ × ℝ ∂volume.prod volume,
        multiplicativeDifference r (Ft q.2) q.1 = 0 := by
      simpa [Function.comp_def] using
        Measure.measurePreserving_swap.quasiMeasurePreserving.ae hdiffTx
    change (∫ x : ℝ, ∫ t : ℝ,
      multiplicativeDifference r (Ft t) x *
        exponential (x * (ψ (s + r) - ψ s)) * (χ t : ℂ)) = 0
    rw [← integral_zero]
    apply integral_congr_ae
    filter_upwards [Measure.ae_ae_of_ae_prod hdiffXt] with x hx
    rw [← integral_zero]
    apply integral_congr_ae
    filter_upwards [hx] with t ht
    simp [ht]
  have hUsupport : ∀ᵐ p : ℝ × ℝ ∂volume.prod volume,
      p ∉ E ×ˢ D → U p = 0 := by
    filter_upwards with p hp
    by_cases hr : p.1 ∈ E
    · have hs : p.2 ∉ D := by
        intro hs
        exact hp ⟨hr, hs⟩
      simp [U, hs]
    · by_cases hs : p.2 ∈ D
      · rw [hU_apply p.1 p.2]
        simp [hs, hRawzero p.1 p.2 hr]
      · simp [U, hs]
  have hUint : Integrable U (volume.prod volume) := by
    rw [← memLp_one_iff_integrable]
    exact aux_memLp_of_ae_bound_of_ae_support U hUmeas.aestronglyMeasurable
      (volume.real A * volume.real J) (Filter.Eventually.of_forall hUbound)
      (E ×ˢ D) (hEcompact.isClosed.measurableSet.prod hD.isClosed.measurableSet)
      (hEcompact.prod hD).measure_lt_top hUsupport 1
  have hUsupportD : ∀ᵐ p : ℝ × ℝ ∂volume.prod volume,
      p.2 ∉ D → U p = 0 := by
    filter_upwards with p hp
    simp [U, hp]
  have htarget : Function.uncurry (fun r s : ℝ ↦ D.indicator (Raw r) s) = U := by
    funext p
    exact (hU_apply p.1 p.2).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Measurable (Function.uncurry fun r s : ℝ ↦ D.indicator (Raw r) s)
    rw [htarget]
    simpa only [Raw] using hUmeas
  · intro r s
    change ‖D.indicator (Raw r) s‖ ≤ volume.real A * volume.real J
    rw [← hU_apply r s]
    exact hUbound (r, s)
  · change Integrable (Function.uncurry fun r s : ℝ ↦ D.indicator (Raw r) s)
      (volume.prod volume)
    rw [htarget]
    exact hUint
  · filter_upwards [hUsupportD] with p hp hnot
    change D.indicator (Raw p.1) p.2 = 0
    rw [← hU_apply p.1 p.2]
    exact hp hnot

/-- For thm:dual-difference-interchange, this makes the base-time profile
integrable on its support and swaps the two target integrations. -/
lemma aux_base_target_integrableOn_and_swap
    (D : Set ℝ) (hD : MeasurableSet D) (T : ℝ → ℝ → ℂ)
    (hTD : Integrable
      (Function.uncurry fun r : ℝ ↦ fun s : ℝ ↦ D.indicator (T r) s)
      (volume.prod volume)) :
    IntegrableOn (fun s : ℝ ↦ ∫ r : ℝ, ‖T r s‖) D volume ∧
      (∫ r : ℝ, ∫ s : ℝ in D, ‖T r s‖) =
        ∫ s : ℝ in D, ∫ r : ℝ, ‖T r s‖ := by
  let Q : ℝ → ℝ := fun s ↦ ∫ r : ℝ, ‖T r s‖
  have hnorm : Integrable
      (Function.uncurry fun r : ℝ ↦ fun s : ℝ ↦ ‖D.indicator (T r) s‖)
      (volume.prod volume) := by
    change Integrable (fun p : ℝ × ℝ ↦ ‖D.indicator (T p.1) p.2‖)
      (volume.prod volume)
    exact hTD.norm
  have hswap : Integrable
      (Function.uncurry fun s : ℝ ↦ fun r : ℝ ↦ ‖D.indicator (T r) s‖)
      (volume.prod volume) := by
    convert hnorm.swap using 1
    ext p
    rfl
  have hsections : Integrable
      (fun s : ℝ ↦ ∫ r : ℝ, ‖D.indicator (T r) s‖) volume :=
    hswap.integral_prod_left
  have heq : (fun s : ℝ ↦ ∫ r : ℝ, ‖D.indicator (T r) s‖) =
      D.indicator Q := by
    funext s
    by_cases hs : s ∈ D <;> simp [Q, hs]
  have hQ : IntegrableOn Q D volume := by
    rw [heq, integrable_indicator_iff hD] at hsections
    exact hsections
  refine ⟨?_, ?_⟩
  · simpa only [Q] using hQ
  · have hind : ∀ r : ℝ,
        (∫ s : ℝ in D, ‖T r s‖) =
          ∫ s : ℝ, ‖D.indicator (T r) s‖ := by
      intro r
      calc
        (∫ s : ℝ in D, ‖T r s‖) =
            ∫ s : ℝ, D.indicator (fun s : ℝ ↦ ‖T r s‖) s :=
              (integral_indicator hD).symm
        _ = ∫ s : ℝ, ‖D.indicator (T r) s‖ := by
          apply integral_congr_ae
          filter_upwards with s
          by_cases hs : s ∈ D <;> simp [Set.indicator, hs]
    calc
      (∫ r : ℝ, ∫ s : ℝ in D, ‖T r s‖) =
          ∫ r : ℝ, ∫ s : ℝ, ‖D.indicator (T r) s‖ := by
            apply integral_congr_ae
            filter_upwards with r
            exact hind r
      _ = ∫ s : ℝ, ∫ r : ℝ, ‖D.indicator (T r) s‖ :=
        integral_integral_swap hnorm
      _ = ∫ s : ℝ in D, ∫ r : ℝ, ‖T r s‖ := by
        rw [heq, integral_indicator hD]

/-- For thm:dual-difference-interchange, Fubini and the triangle inequality
turn a fixed-fibre factorization into an outer integral norm bound. -/
lemma aux_norm_integral_integral_le_integral_norm_of_fiber_identity
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    (K : α → ℝ → ℂ) (c T : ℝ → ℂ)
    (hK : Integrable (Function.uncurry K) (μ.prod volume))
    (hT : Integrable T volume)
    (hc : ∀ᵐ s : ℝ ∂volume, ‖c s‖ ≤ 1)
    (hidentity : ∀ᵐ s : ℝ ∂volume,
      (∫ z : α, K z s ∂μ) = c s * starRingEnd ℂ (T s)) :
    ‖∫ z : α, ∫ s : ℝ, K z s ∂volume ∂μ‖ ≤
      ∫ s : ℝ, ‖T s‖ := by
  have hfib : Integrable (fun s : ℝ ↦ ∫ z : α, K z s ∂μ) volume := by
    convert hK.swap.integral_prod_left using 1
    ext s
    congr 1
  calc
    ‖∫ z : α, ∫ s : ℝ, K z s ∂volume ∂μ‖ =
        ‖∫ s : ℝ, ∫ z : α, K z s ∂μ‖ := by
          rw [integral_integral_swap hK]
    _ ≤ ∫ s : ℝ, ‖∫ z : α, K z s ∂μ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ s : ℝ, ‖T s‖ := by
      apply integral_mono_ae hfib.norm hT.norm
      filter_upwards [hc, hidentity] with s hs hident
      rw [hident, norm_mul, starRingEnd_apply, norm_star]
      simpa [mul_comm] using mul_le_of_le_one_right (norm_nonneg (T s)) hs

/-- For \(\label{thm:dual-difference-interchange}\), this combines the
autocorrelation identity with fibrewise Fubini and the triangle inequality.
It is used by `dualDifferenceInterchange`. -/
lemma aux_square_timeIntegral_le_target_doubleIntegral
    (P : (ℝ × ℝ) → ℝ → ℂ) (c T : ℝ → ℝ → ℂ)
    (hsections : ∀ᵐ z : ℝ × ℝ ∂aux_dualPairMeasure, Integrable (P z) volume)
    (hH : MemLp (fun z : ℝ × ℝ ↦ ∫ s : ℝ, P z s) 2 aux_dualPairMeasure)
    (hshift : Integrable
      (Function.uncurry fun p : ((ℝ × ℝ) × ℝ) ↦ fun s : ℝ ↦
        P p.1 s * starRingEnd ℂ (P p.1 (s + p.2)))
      ((aux_dualPairMeasure.prod volume).prod volume))
    (hbase : Integrable
      (Function.uncurry fun p : ((ℝ × ℝ) × ℝ) ↦ fun r : ℝ ↦
        P p.1 p.2 * starRingEnd ℂ (P p.1 (p.2 + r)))
      ((aux_dualPairMeasure.prod volume).prod volume))
    (hT : Integrable (Function.uncurry T) (volume.prod volume))
    (hc : ∀ᵐ r : ℝ ∂volume, ∀ᵐ s : ℝ ∂volume, ‖c r s‖ ≤ 1)
    (hidentity : ∀ᵐ r : ℝ ∂volume, ∀ᵐ s : ℝ ∂volume,
      (∫ z : ℝ × ℝ, P z s * starRingEnd ℂ (P z (s + r)) ∂aux_dualPairMeasure) =
        c r s * starRingEnd ℂ (T r s)) :
    ∫ z : ℝ × ℝ, ‖∫ s : ℝ, P z s‖ ^ (2 : ℕ) ∂aux_dualPairMeasure ≤
      ∫ r : ℝ, ∫ s : ℝ, ‖T r s‖ := by
  have hinitial := aux_square_timeIntegral_le_autocorrelation_prod P hsections hH hshift
  have houter : Integrable
      (fun r : ℝ ↦ ∫ p : (ℝ × ℝ) × ℝ,
        P p.1 p.2 * starRingEnd ℂ (P p.1 (p.2 + r)) ∂(aux_dualPairMeasure.prod volume))
      volume := by
    convert hbase.swap.integral_prod_left using 1
    ext r
    congr 1
  have houter' : Integrable
      (fun r : ℝ ↦ ∫ z : ℝ × ℝ, ∫ s : ℝ,
        P z s * starRingEnd ℂ (P z (s + r)) ∂volume ∂aux_dualPairMeasure) volume := by
    apply houter.congr
    filter_upwards [hbase.prod_left_ae] with r hr
    simpa only using (integral_prod
      (fun p : (ℝ × ℝ) × ℝ ↦
        P p.1 p.2 * starRingEnd ℂ (P p.1 (p.2 + r))) hr)
  have hTouter : Integrable (fun r : ℝ ↦ ∫ s : ℝ, ‖T r s‖) volume := by
    simpa only [Function.uncurry] using hT.norm.integral_prod_left
  have hpoint : ∀ᵐ r : ℝ ∂volume,
      ‖∫ z : ℝ × ℝ, ∫ s : ℝ,
        P z s * starRingEnd ℂ (P z (s + r)) ∂volume ∂aux_dualPairMeasure‖ ≤
        ∫ s : ℝ, ‖T r s‖ := by
    filter_upwards [hbase.prod_left_ae, hT.prod_right_ae, hc, hidentity]
      with r hr hTr hcr hident
    exact aux_norm_integral_integral_le_integral_norm_of_fiber_identity aux_dualPairMeasure
      (fun z s ↦ P z s * starRingEnd ℂ (P z (s + r))) (c r) (T r)
      hr hTr hcr hident
  calc
    ∫ z : ℝ × ℝ, ‖∫ s : ℝ, P z s‖ ^ (2 : ℕ) ∂aux_dualPairMeasure ≤
        ∫ r : ℝ, ‖∫ z : ℝ × ℝ, ∫ s : ℝ,
          P z s * starRingEnd ℂ (P z (s + r)) ∂volume ∂aux_dualPairMeasure‖ := hinitial
    _ ≤ ∫ r : ℝ, ∫ s : ℝ, ‖T r s‖ :=
      integral_mono_ae houter'.norm hTouter hpoint

/-- For \(\label{thm:dual-difference-interchange}\), this restricts a
fixed-fibre factorization to the support of its coefficient. It is used by
`aux_square_timeIntegral_le_target_doubleIntegralOnCoeff`. -/
lemma aux_norm_integral_integral_le_integralOn_norm_of_fiber_identity
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    (D : Set ℝ) (hD : MeasurableSet D)
    (K : α → ℝ → ℂ) (c T : ℝ → ℂ)
    (hK : Integrable (Function.uncurry K) (μ.prod volume))
    (hTD : Integrable (D.indicator T) volume)
    (hc : ∀ᵐ s : ℝ ∂volume, ‖c s‖ ≤ 1)
    (hcsupport : ∀ᵐ s : ℝ ∂volume, s ∉ D → c s = 0)
    (hidentity : ∀ᵐ s : ℝ ∂volume,
      (∫ z : α, K z s ∂μ) = c s * starRingEnd ℂ (T s)) :
    ‖∫ z : α, ∫ s : ℝ, K z s ∂volume ∂μ‖ ≤
      ∫ s : ℝ in D, ‖T s‖ := by
  have hfib : Integrable (fun s : ℝ ↦ ∫ z : α, K z s ∂μ) volume := by
    convert hK.swap.integral_prod_left using 1
    ext s
    congr 1
  have hindicator :
      (∫ s : ℝ, ‖D.indicator T s‖) = ∫ s : ℝ in D, ‖T s‖ := by
    calc
      (∫ s : ℝ, ‖D.indicator T s‖) =
          ∫ s : ℝ, D.indicator (fun s : ℝ ↦ ‖T s‖) s := by
            apply integral_congr_ae
            filter_upwards with s
            by_cases hsD : s ∈ D <;> simp [Set.indicator, hsD]
      _ = ∫ s : ℝ in D, ‖T s‖ := integral_indicator hD
  calc
    ‖∫ z : α, ∫ s : ℝ, K z s ∂volume ∂μ‖ =
        ‖∫ s : ℝ, ∫ z : α, K z s ∂μ‖ := by
          rw [integral_integral_swap hK]
    _ ≤ ∫ s : ℝ, ‖∫ z : α, K z s ∂μ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ s : ℝ, ‖D.indicator T s‖ := by
      apply integral_mono_ae hfib.norm hTD.norm
      filter_upwards [hc, hcsupport, hidentity] with s hs hssupport hident
      by_cases hsD : s ∈ D
      · rw [hident, norm_mul, starRingEnd_apply, norm_star]
        simpa [Set.indicator, hsD, mul_comm] using
          mul_le_of_le_one_right (norm_nonneg (T s)) hs
      · rw [hssupport hsD] at hident
        simp [Set.indicator, hsD, hident]
    _ = ∫ s : ℝ in D, ‖T s‖ := hindicator

/-- For \(\label{thm:dual-difference-interchange}\), this combines the
autocorrelation estimate with a coefficient-supported base-time restriction.
It is used by `dualDifferenceInterchange`. -/
lemma aux_square_timeIntegral_le_target_doubleIntegralOnCoeff
    (D : Set ℝ) (hD : MeasurableSet D)
    (P : (ℝ × ℝ) → ℝ → ℂ) (c T : ℝ → ℝ → ℂ)
    (hsections : ∀ᵐ z : ℝ × ℝ ∂aux_dualPairMeasure, Integrable (P z) volume)
    (hH : MemLp (fun z : ℝ × ℝ ↦ ∫ s : ℝ, P z s) 2 aux_dualPairMeasure)
    (hshift : Integrable
      (Function.uncurry fun p : ((ℝ × ℝ) × ℝ) ↦ fun s : ℝ ↦
        P p.1 s * starRingEnd ℂ (P p.1 (s + p.2)))
      ((aux_dualPairMeasure.prod volume).prod volume))
    (hbase : Integrable
      (Function.uncurry fun p : ((ℝ × ℝ) × ℝ) ↦ fun r : ℝ ↦
        P p.1 p.2 * starRingEnd ℂ (P p.1 (p.2 + r)))
      ((aux_dualPairMeasure.prod volume).prod volume))
    (hTD : Integrable
      (Function.uncurry fun r : ℝ ↦ fun s : ℝ ↦ D.indicator (T r) s)
      (volume.prod volume))
    (hc : ∀ᵐ r : ℝ ∂volume, ∀ᵐ s : ℝ ∂volume, ‖c r s‖ ≤ 1)
    (hcsupport : ∀ᵐ r : ℝ ∂volume, ∀ᵐ s : ℝ ∂volume,
      s ∉ D → c r s = 0)
    (hidentity : ∀ᵐ r : ℝ ∂volume, ∀ᵐ s : ℝ ∂volume,
      (∫ z : ℝ × ℝ, P z s * starRingEnd ℂ (P z (s + r)) ∂aux_dualPairMeasure) =
        c r s * starRingEnd ℂ (T r s)) :
    ∫ z : ℝ × ℝ, ‖∫ s : ℝ, P z s‖ ^ (2 : ℕ) ∂aux_dualPairMeasure ≤
      ∫ r : ℝ, ∫ s : ℝ in D, ‖T r s‖ := by
  have hinitial := aux_square_timeIntegral_le_autocorrelation_prod P hsections hH hshift
  have houter : Integrable
      (fun r : ℝ ↦ ∫ p : (ℝ × ℝ) × ℝ,
        P p.1 p.2 * starRingEnd ℂ (P p.1 (p.2 + r)) ∂(aux_dualPairMeasure.prod volume)) volume := by
    convert hbase.swap.integral_prod_left using 1
    ext r
    congr 1
  have houter' : Integrable
      (fun r : ℝ ↦ ∫ z : ℝ × ℝ, ∫ s : ℝ,
        P z s * starRingEnd ℂ (P z (s + r)) ∂volume ∂aux_dualPairMeasure) volume := by
    apply houter.congr
    filter_upwards [hbase.prod_left_ae] with r hr
    simpa only using (integral_prod
      (fun p : (ℝ × ℝ) × ℝ ↦
        P p.1 p.2 * starRingEnd ℂ (P p.1 (p.2 + r))) hr)
  have hTDouter : Integrable
      (fun r : ℝ ↦ ∫ s : ℝ, ‖D.indicator (T r) s‖) volume := by
    simpa only [Function.uncurry] using hTD.norm.integral_prod_left
  have hpoint : ∀ᵐ r : ℝ ∂volume,
      ‖∫ z : ℝ × ℝ, ∫ s : ℝ,
        P z s * starRingEnd ℂ (P z (s + r)) ∂volume ∂aux_dualPairMeasure‖ ≤
        ∫ s : ℝ in D, ‖T r s‖ := by
    filter_upwards [hbase.prod_left_ae, hTD.prod_right_ae, hc, hcsupport, hidentity]
      with r hr hTDr hcr hcsup hident
    exact aux_norm_integral_integral_le_integralOn_norm_of_fiber_identity aux_dualPairMeasure D hD
      (fun z s ↦ P z s * starRingEnd ℂ (P z (s + r))) (c r) (T r)
      hr hTDr hcr hcsup hident
  have hinner : ∀ᵐ r : ℝ ∂volume,
      (∫ s : ℝ, ‖D.indicator (T r) s‖) = ∫ s : ℝ in D, ‖T r s‖ := by
    filter_upwards with r
    calc
      (∫ s : ℝ, ‖D.indicator (T r) s‖) =
          ∫ s : ℝ, D.indicator (fun s : ℝ ↦ ‖T r s‖) s := by
            apply integral_congr_ae
            filter_upwards with s
            by_cases hsD : s ∈ D <;> simp [Set.indicator, hsD]
      _ = ∫ s : ℝ in D, ‖T r s‖ := integral_indicator hD
  have hpoint' : ∀ᵐ r : ℝ ∂volume,
      ‖∫ z : ℝ × ℝ, ∫ s : ℝ,
        P z s * starRingEnd ℂ (P z (s + r)) ∂volume ∂aux_dualPairMeasure‖ ≤
        ∫ s : ℝ, ‖D.indicator (T r) s‖ := by
    filter_upwards [hpoint, hinner] with r hr hri
    rw [hri]
    exact hr
  calc
    ∫ z : ℝ × ℝ, ‖∫ s : ℝ, P z s‖ ^ (2 : ℕ) ∂aux_dualPairMeasure ≤
        ∫ r : ℝ, ‖∫ z : ℝ × ℝ, ∫ s : ℝ,
          P z s * starRingEnd ℂ (P z (s + r)) ∂volume ∂aux_dualPairMeasure‖ := hinitial
    _ ≤ ∫ r : ℝ, ∫ s : ℝ, ‖D.indicator (T r) s‖ :=
      integral_mono_ae houter'.norm hTDouter hpoint'
    _ = ∫ r : ℝ, ∫ s : ℝ in D, ‖T r s‖ := integral_congr_ae hinner

/-- For \(\label{thm:dual-difference-interchange}\), this bounds the
scalar factor in the fixed-base autocorrelation identity. -/
lemma aux_dualP_autocorrelation_coefficient_bound
    (ψ : ℝ → ℝ) (u : ℝ → ℂ) (hubound : ∀ h : ℝ, ‖u h‖ ≤ 1) (r s : ℝ) :
    ‖u s * starRingEnd ℂ (u (s + r)) *
      exponential (s * (ψ (s + r) - ψ s))‖ ≤ 1 := by
  calc
    ‖u s * starRingEnd ℂ (u (s + r)) *
        exponential (s * (ψ (s + r) - ψ s))‖ =
        ‖u s‖ * ‖u (s + r)‖ * 1 := by
          rw [norm_mul, norm_mul, Complex.norm_conj, aux_norm_exponential]
    _ ≤ 1 * 1 * 1 := by gcongr <;> apply hubound
    _ = 1 := by norm_num

/-- For \(\label{thm:dual-difference-interchange}\), this records that the
fixed-base autocorrelation scalar vanishes off the selector support. -/
lemma aux_dualP_autocorrelation_coefficient_zero_off
    (D : Set ℝ) (ψ : ℝ → ℝ) (u : ℝ → ℂ)
    (husupport : ∀ h : ℝ, h ∉ D → u h = 0) (r s : ℝ) (hs : s ∉ D) :
    u s * starRingEnd ℂ (u (s + r)) *
      exponential (s * (ψ (s + r) - ψ s)) = 0 := by
  simp [husupport s hs]

/-- For \(\label{thm:dual-difference-interchange}\), this supplies the
almost-everywhere coefficient bound for the autocorrelation reduction. -/
lemma aux_dualP_autocorrelation_coefficient_ae_bound
    (ψ : ℝ → ℝ) (u : ℝ → ℂ) (hubound : ∀ h : ℝ, ‖u h‖ ≤ 1) :
    ∀ᵐ r : ℝ ∂volume, ∀ᵐ s : ℝ ∂volume,
      ‖u s * starRingEnd ℂ (u (s + r)) *
        exponential (s * (ψ (s + r) - ψ s))‖ ≤ 1 := by
  filter_upwards with r
  filter_upwards with s
  exact aux_dualP_autocorrelation_coefficient_bound ψ u hubound r s

/-- For \(\label{thm:dual-difference-interchange}\), this supplies the
almost-everywhere selector-support condition for the autocorrelation reduction. -/
lemma aux_dualP_autocorrelation_coefficient_ae_zero_off
    (D : Set ℝ) (ψ : ℝ → ℝ) (u : ℝ → ℂ)
    (husupport : ∀ h : ℝ, h ∉ D → u h = 0) :
    ∀ᵐ r : ℝ ∂volume, ∀ᵐ s : ℝ ∂volume, s ∉ D →
      u s * starRingEnd ℂ (u (s + r)) *
        exponential (s * (ψ (s + r) - ψ s)) = 0 := by
  filter_upwards with r
  filter_upwards with s
  exact aux_dualP_autocorrelation_coefficient_zero_off D ψ u husupport r s

/-- For thm:dual-difference-interchange, this specializes the
coefficient-supported autocorrelation bridge to the dual kernel. -/
lemma aux_dualP_square_timeIntegral_le_target_doubleIntegralOn
    (D : Set ℝ) (hD : MeasurableSet D)
    (Ft : ℝ → ℝ → ℂ) (χ ψ : ℝ → ℝ) (u : ℝ → ℂ)
    (hχ : ∀ t : ℝ, 0 ≤ χ t)
    (hubound : ∀ h : ℝ, ‖u h‖ ≤ 1)
    (husupport : ∀ h : ℝ, h ∉ D → u h = 0)
    (hsections : ∀ᵐ z : ℝ × ℝ ∂aux_dualPairMeasure,
      Integrable (aux_dualP Ft χ ψ u z) volume)
    (hH : MemLp (fun z : ℝ × ℝ ↦ ∫ s : ℝ, aux_dualP Ft χ ψ u z s)
      2 aux_dualPairMeasure)
    (hshift : Integrable
      (Function.uncurry fun p : ((ℝ × ℝ) × ℝ) ↦ fun s : ℝ ↦
        aux_dualP Ft χ ψ u p.1 s *
          starRingEnd ℂ (aux_dualP Ft χ ψ u p.1 (s + p.2)))
      ((aux_dualPairMeasure.prod volume).prod volume))
    (hbase : Integrable
      (Function.uncurry fun p : ((ℝ × ℝ) × ℝ) ↦ fun r : ℝ ↦
        aux_dualP Ft χ ψ u p.1 p.2 *
          starRingEnd ℂ (aux_dualP Ft χ ψ u p.1 (p.2 + r)))
      ((aux_dualPairMeasure.prod volume).prod volume))
    (hTD : Integrable
      (Function.uncurry fun r : ℝ ↦ fun s : ℝ ↦ D.indicator (fun s : ℝ ↦
        ∫ x : ℝ, ∫ t : ℝ,
          multiplicativeDifference r (Ft t) x *
            exponential (x * (ψ (s + r) - ψ s)) * (χ t : ℂ)) s)
      (volume.prod volume)) :
    ∫ z : ℝ × ℝ, ‖∫ s : ℝ, aux_dualP Ft χ ψ u z s‖ ^ (2 : ℕ)
      ∂aux_dualPairMeasure ≤
      ∫ r : ℝ, ∫ s : ℝ in D, ‖∫ x : ℝ, ∫ t : ℝ,
        multiplicativeDifference r (Ft t) x *
          exponential (x * (ψ (s + r) - ψ s)) * (χ t : ℂ)‖ := by
  let c : ℝ → ℝ → ℂ := fun r s ↦
    u s * starRingEnd ℂ (u (s + r)) *
      exponential (s * (ψ (s + r) - ψ s))
  let T : ℝ → ℝ → ℂ := fun r s ↦ ∫ x : ℝ, ∫ t : ℝ,
    multiplicativeDifference r (Ft t) x *
      exponential (x * (ψ (s + r) - ψ s)) * (χ t : ℂ)
  have hc : ∀ᵐ r : ℝ ∂volume, ∀ᵐ s : ℝ ∂volume, ‖c r s‖ ≤ 1 := by
    filter_upwards with r
    filter_upwards with s
    dsimp only [c]
    exact aux_dualP_autocorrelation_coefficient_bound ψ u hubound r s
  have hcsupport : ∀ᵐ r : ℝ ∂volume, ∀ᵐ s : ℝ ∂volume,
      s ∉ D → c r s = 0 := by
    filter_upwards with r
    filter_upwards with s
    intro hs
    exact aux_dualP_autocorrelation_coefficient_zero_off D ψ u husupport r s hs
  have hbaseSections : ∀ᵐ r : ℝ ∂volume, ∀ᵐ s : ℝ ∂volume,
      Integrable (fun z : ℝ × ℝ ↦
        aux_dualP Ft χ ψ u z s *
          starRingEnd ℂ (aux_dualP Ft χ ψ u z (s + r)))
        aux_dualPairMeasure := by
    filter_upwards [hbase.prod_left_ae] with r hr
    exact hr.prod_left_ae
  have hidentity : ∀ᵐ r : ℝ ∂volume, ∀ᵐ s : ℝ ∂volume,
      (∫ z : ℝ × ℝ,
        aux_dualP Ft χ ψ u z s *
          starRingEnd ℂ (aux_dualP Ft χ ψ u z (s + r))
          ∂aux_dualPairMeasure) = c r s * starRingEnd ℂ (T r s) := by
    filter_upwards [hbaseSections] with r hr
    filter_upwards [hr] with s hrs
    calc
      (∫ z : ℝ × ℝ,
        aux_dualP Ft χ ψ u z s *
          starRingEnd ℂ (aux_dualP Ft χ ψ u z (s + r))
          ∂aux_dualPairMeasure) =
          ∫ x : ℝ, ∫ t : ℝ,
            aux_dualP Ft χ ψ u (x, t) s *
              starRingEnd ℂ (aux_dualP Ft χ ψ u (x, t) (s + r)) := by
                simpa only using (integral_prod
                  (fun z : ℝ × ℝ ↦
                    aux_dualP Ft χ ψ u z s *
                      starRingEnd ℂ (aux_dualP Ft χ ψ u z (s + r))) hrs)
      _ = c r s * starRingEnd ℂ (T r s) := by
        simpa only [c, T] using
          aux_dualP_autocorrelation_target_integral Ft χ ψ u hχ s r
  exact aux_square_timeIntegral_le_target_doubleIntegralOnCoeff D hD
    (aux_dualP Ft χ ψ u) c T hsections hH hshift hbase
    (by simpa only [T] using hTD) hc hcsupport hidentity

/-- For \(\label{thm:dual-difference-interchange}\), this selects a point
of a positive interval whose value dominates the interval average. -/
lemma aux_exists_Icc_two_measure_mul_ge_of_le_setIntegral
    (a b : ℝ) (hab : a < b) (Q : ℝ → ℝ)
    (hQ : IntegrableOn Q (Set.Icc a b) volume)
    (hQnonneg : ∀ x ∈ Set.Icc a b, 0 ≤ Q x)
    (B : ℝ) (hB : B ≤ ∫ x : ℝ in Set.Icc a b, Q x) :
    ∃ x ∈ Set.Icc a b,
      B ≤ 2 * volume.real (Set.Icc a b) * Q x := by
  have hDpos : 0 < volume.real (Set.Icc a b) := by
    rw [Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
    exact sub_pos.mpr hab
  have hDfinite : volume (Set.Icc a b) ≠ ∞ := by
    exact (measure_Icc_lt_top).ne
  have hDnonzero : volume (Set.Icc a b) ≠ 0 := by
    intro hzero
    apply (ne_of_gt hDpos)
    simp only [Measure.real, hzero, ENNReal.toReal_zero]
  obtain ⟨x, hx, hmean⟩ := exists_setAverage_le hDnonzero hDfinite hQ
  have hdiv : B / volume.real (Set.Icc a b) ≤ Q x := by
    calc
      B / volume.real (Set.Icc a b) ≤
          (∫ x : ℝ in Set.Icc a b, Q x) / volume.real (Set.Icc a b) :=
        div_le_div_of_nonneg_right hB hDpos.le
      _ = ⨍ x : ℝ in Set.Icc a b, Q x := by
        rw [setAverage_eq]
        simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
      _ ≤ Q x := hmean
  have hfirst : B ≤ volume.real (Set.Icc a b) * Q x := by
    calc
      B = volume.real (Set.Icc a b) * (B / volume.real (Set.Icc a b)) := by field_simp
      _ ≤ volume.real (Set.Icc a b) * Q x :=
        mul_le_mul_of_nonneg_left hdiv hDpos.le
  refine ⟨x, hx, ?_⟩
  have hnonneg : 0 ≤ volume.real (Set.Icc a b) * Q x :=
    mul_nonneg hDpos.le (hQnonneg x hx)
  nlinarith

/-- For \(\label{thm:dual-difference-interchange}\), this selects a point
whose value dominates the average over an arbitrary positive finite-measure
set. It is used by `dualDifferenceInterchange` for a difference interval. -/
lemma aux_exists_measure_mul_ge_of_le_setIntegral
    (D : Set ℝ) (hDpos : 0 < volume.real D) (hDfinite : volume D ≠ ∞)
    (Q : ℝ → ℝ) (hQ : IntegrableOn Q D volume) (B : ℝ)
    (hB : B ≤ ∫ h : ℝ in D, Q h) :
    ∃ h ∈ D, B ≤ volume.real D * Q h := by
  have hDnonzero : volume D ≠ 0 := by
    intro hzero
    apply (ne_of_gt hDpos)
    simp only [Measure.real, hzero, ENNReal.toReal_zero]
  obtain ⟨h, hhD, hmean⟩ := exists_setAverage_le hDnonzero hDfinite hQ
  have hdiv : B / volume.real D ≤ Q h := by
    calc
      B / volume.real D ≤ (∫ h : ℝ in D, Q h) / volume.real D :=
        div_le_div_of_nonneg_right hB hDpos.le
      _ = ⨍ h : ℝ in D, Q h := by
        rw [setAverage_eq]
        simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
      _ ≤ Q h := hmean
  refine ⟨h, hhD, ?_⟩
  calc
    B = volume.real D * (B / volume.real D) := by
      field_simp
    _ ≤ volume.real D * Q h := mul_le_mul_of_nonneg_left hdiv hDpos.le

/-- For \(\label{thm:dual-difference-interchange}\), this removes a square
from the `uNorm` parameter after a real-valued square estimate. -/
lemma aux_ennreal_le_of_u_sq_eq_ofReal
    (U : ℝ≥0∞) (E R : ℝ)
    (hU : U ^ (2 : ℝ) = ENNReal.ofReal E)
    (hR : 0 ≤ R)
    (hER : E ≤ R ^ (2 : ℕ)) :
    U ≤ ENNReal.ofReal R := by
  apply aux_gowers_ennreal_le_of_sq_le
  have hUnat : U ^ (2 : ℕ) = ENNReal.ofReal E := by
    rw [← ENNReal.rpow_natCast U 2]
    simpa using hU
  rw [hUnat, ← ENNReal.ofReal_pow hR 2]
  exact ENNReal.ofReal_le_ofReal hER

/-- For \(\label{thm:dual-difference-interchange}\), this performs the
real coefficient calculation at the end of `dualDifferenceInterchange`. -/
lemma aux_real_dual_difference_coefficient
    (E S a j Q : ℝ)
    (hE0 : 0 ≤ E) (hS : 2 ≤ S)
    (ha0 : 0 ≤ a) (haS : a ≤ S)
    (hj0 : 0 ≤ j) (hjS : j ≤ S)
    (hQ0 : 0 ≤ Q)
    (hEsq : E ^ (2 : ℕ) ≤ 8 * a ^ (2 : ℕ) * j ^ (3 : ℕ) * Q) :
    E ≤ (2 * S ^ (2 : ℕ) * Q ^ (1 / (4 : ℝ))) ^ (2 : ℕ) := by
  have hS0 : 0 ≤ S := by linarith
  have hS1 : 1 ≤ S := by linarith
  have ha2 : a ^ (2 : ℕ) ≤ S ^ (2 : ℕ) :=
    pow_le_pow_left₀ ha0 haS 2
  have hj3 : j ^ (3 : ℕ) ≤ S ^ (3 : ℕ) :=
    pow_le_pow_left₀ hj0 hjS 3
  have hprod : a ^ (2 : ℕ) * j ^ (3 : ℕ) ≤
      S ^ (2 : ℕ) * S ^ (3 : ℕ) :=
    mul_le_mul ha2 hj3 (pow_nonneg hj0 _) (pow_nonneg hS0 _)
  have hcoeff : 8 * a ^ (2 : ℕ) * j ^ (3 : ℕ) ≤ 16 * S ^ (8 : ℕ) := by
    calc
      8 * a ^ (2 : ℕ) * j ^ (3 : ℕ) =
          8 * (a ^ (2 : ℕ) * j ^ (3 : ℕ)) := by ring
      _ ≤ 8 * (S ^ (2 : ℕ) * S ^ (3 : ℕ)) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = 8 * S ^ (5 : ℕ) := by ring
      _ ≤ 8 * S ^ (8 : ℕ) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hS1 (by norm_num)) (by norm_num)
      _ ≤ 16 * S ^ (8 : ℕ) :=
        mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hS0 _)
  have hcoeffQ : 8 * a ^ (2 : ℕ) * j ^ (3 : ℕ) * Q ≤
      16 * S ^ (8 : ℕ) * Q :=
    mul_le_mul_of_nonneg_right hcoeff hQ0
  have hQfour : (Q ^ (1 / (4 : ℝ))) ^ (4 : ℕ) = Q := by
    rw [← Real.rpow_natCast (Q ^ (1 / (4 : ℝ))) 4]
    rw [← Real.rpow_mul hQ0]
    norm_num
  let R : ℝ := 2 * S ^ (2 : ℕ) * Q ^ (1 / (4 : ℝ))
  have hRfour : R ^ (4 : ℕ) = 16 * S ^ (8 : ℕ) * Q := by
    dsimp [R]
    calc
      (2 * S ^ (2 : ℕ) * Q ^ (1 / (4 : ℝ))) ^ (4 : ℕ) =
          16 * S ^ (8 : ℕ) * (Q ^ (1 / (4 : ℝ))) ^ (4 : ℕ) := by ring
      _ = 16 * S ^ (8 : ℕ) * Q := by rw [hQfour]
  have hERfour : E ^ (2 : ℕ) ≤ R ^ (4 : ℕ) :=
    hEsq.trans (hcoeffQ.trans_eq hRfour.symm)
  have hR2 : 0 ≤ R ^ (2 : ℕ) := sq_nonneg R
  have hER2 : E ≤ R ^ (2 : ℕ) := by
    apply (sq_le_sq₀ hE0 hR2).mp
    calc
      E ^ (2 : ℕ) ≤ R ^ (4 : ℕ) := hERfour
      _ = (R ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
  simpa only [R] using hER2

/-- For \(\label{thm:dual-difference-interchange}\), this is the ENNReal
form of the endgame coefficient estimate. -/
lemma aux_ennreal_dual_difference_coefficient
    (U : ℝ≥0∞) (E S a j Q : ℝ)
    (hU : U ^ (2 : ℝ) = ENNReal.ofReal E)
    (hE0 : 0 ≤ E) (hS : 2 ≤ S)
    (ha0 : 0 ≤ a) (haS : a ≤ S)
    (hj0 : 0 ≤ j) (hjS : j ≤ S)
    (hQ0 : 0 ≤ Q)
    (hEsq : E ^ (2 : ℕ) ≤ 8 * a ^ (2 : ℕ) * j ^ (3 : ℕ) * Q) :
    U ≤ ENNReal.ofReal (2 * S ^ (2 : ℕ) * Q ^ (1 / (4 : ℝ))) := by
  apply aux_ennreal_le_of_u_sq_eq_ofReal U E
  · exact hU
  · have hS0 : 0 ≤ S := by linarith
    positivity
  · exact aux_real_dual_difference_coefficient E S a j Q
      hE0 hS ha0 haS hj0 hjS hQ0 hEsq

/-- For \(\label{thm:dual-difference-interchange}\), this assembles the
selector, Cauchy--Schwarz, and averaging square bounds. -/
lemma aux_dual_difference_square_assembly
    (E L a j B Q : ℝ)
    (hE0 : 0 ≤ E) (ha0 : 0 ≤ a) (hj0 : 0 ≤ j)
    (hEL : E ≤ 2 * L)
    (hLsq : L ^ (2 : ℕ) ≤ a * j ^ (3 : ℕ) * B)
    (hB : B ≤ 2 * a * Q) :
    E ^ (2 : ℕ) ≤ 8 * a ^ (2 : ℕ) * j ^ (3 : ℕ) * Q := by
  have h2L0 : 0 ≤ 2 * L := hE0.trans hEL
  have hELsq : E ^ (2 : ℕ) ≤ (2 * L) ^ (2 : ℕ) :=
    (sq_le_sq₀ hE0 h2L0).mpr hEL
  have haj0 : 0 ≤ a * j ^ (3 : ℕ) :=
    mul_nonneg ha0 (pow_nonneg hj0 _)
  calc
    E ^ (2 : ℕ) ≤ (2 * L) ^ (2 : ℕ) := hELsq
    _ = 4 * L ^ (2 : ℕ) := by ring
    _ ≤ 4 * (a * j ^ (3 : ℕ) * B) :=
      mul_le_mul_of_nonneg_left hLsq (by norm_num)
    _ ≤ 4 * (a * j ^ (3 : ℕ) * (2 * a * Q)) := by
      gcongr
    _ = 8 * a ^ (2 : ℕ) * j ^ (3 : ℕ) * Q := by ring

/-- For \(\label{thm:dual-difference-interchange}\), this is the full
numeric endgame of `dualDifferenceInterchange`. -/
lemma aux_ennreal_dual_difference_numerical_assembly
    (U : ℝ≥0∞) (E L S a j B Q : ℝ)
    (hU : U ^ (2 : ℝ) = ENNReal.ofReal E)
    (hE0 : 0 ≤ E) (hS : 2 ≤ S)
    (ha0 : 0 ≤ a) (haS : a ≤ S)
    (hj0 : 0 ≤ j) (hjS : j ≤ S)
    (hQ0 : 0 ≤ Q)
    (hEL : E ≤ 2 * L)
    (hLsq : L ^ (2 : ℕ) ≤ a * j ^ (3 : ℕ) * B)
    (hB : B ≤ 2 * a * Q) :
    U ≤ ENNReal.ofReal (2 * S ^ (2 : ℕ) * Q ^ (1 / (4 : ℝ))) := by
  apply aux_ennreal_dual_difference_coefficient U E S a j Q hU hE0 hS
    ha0 haS hj0 hjS hQ0
  exact aux_dual_difference_square_assembly E L a j B Q hE0 ha0 hj0 hEL hLsq hB

/-- For \(\label{thm:dual-difference-interchange}\), these are the size
parameter bounds used in the numeric endgame. -/
lemma aux_dual_difference_size_bounds
    (A J : Set ℝ) (χ : ℝ → ℝ) :
    2 ≤ sizeParameter ![A, J] χ ∧
      0 ≤ volume.real A ∧ volume.real A ≤ sizeParameter ![A, J] χ ∧
      0 ≤ volume.real J ∧ volume.real J ≤ sizeParameter ![A, J] χ := by
  have hA := aux_intervalLength_le_sizeParameter_two A J χ 0
  have hJ := aux_intervalLength_le_sizeParameter_two A J χ 1
  norm_num [intervalLength] at hA hJ
  refine ⟨?_, MeasureTheory.measureReal_nonneg, hA,
    MeasureTheory.measureReal_nonneg, hJ⟩
  unfold sizeParameter
  exact le_add_of_nonneg_right (by positivity)

/-- The constant in \(\label{thm:dual-difference-interchange}\), used by
`dualDifferenceInterchange`:
\[
C_{\ref{thm:dual-difference-interchange},\,A,J,\chi}
:=
2\Ssize{A,J}{\chi}^{2}.
\]
-/
def C_dualDifferenceInterchange (A J : Set ℝ) (χ : ℝ → ℝ) : ℝ :=
  2 * sizeParameter ![A, J] χ ^ 2

/--
Let $A,J$ be positive-length compact intervals. Let $(F_t)_{t\in\R}$ be a
jointly measurable family of $1$-bounded functions, each supported in $A$.
Let $\chi$ be nonnegative, $1$-bounded, and supported in $J$. Define
\[
F(x):=\int_\R F_t(x)\chi(t)\dd t.
\]
Define
\[
C_{\ref{thm:dual-difference-interchange},\,A,J,\chi}
:=
2\Ssize{A,J}{\chi}^{2}.
\]
Then there exists a measurable map $\Phi:\R\to\R$ such that
\[
\uNorm F3
\leq
C_{\ref{thm:dual-difference-interchange},\,A,J,\chi}
\left(
\int_\R
\left|
\iint\Delta_hF_t(x)e(x\Phi(h))\chi(t)\dd t\dd x
\right|
\dd h
\right)^{1/4}.
\]
-/
theorem dualDifferenceInterchange
    (A J : Set ℝ)
    (hA : ∃ a b : ℝ, a < b ∧ A = Set.Icc a b)
    (hJ : ∃ a b : ℝ, a < b ∧ J = Set.Icc a b)
    (Ft : ℝ → ℝ → ℂ)
    (hFt_measurable : Measurable (Function.uncurry Ft))
    (hFt_one_bounded : ∀ t : ℝ, ∀ᵐ x ∂volume, ‖Ft t x‖ ≤ 1)
    (hFt_support : ∀ t : ℝ, ∀ᵐ x ∂volume, x ∉ A → Ft t x = 0)
    (χ : ℝ → ℝ)
    (hχ_measurable : Measurable χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t)
    (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (hχ_support : ∀ᵐ t ∂volume, t ∉ J → χ t = 0) :
    ∃ Φ : ℝ → ℝ, Measurable Φ ∧
      uNorm 3 (fun x : ℝ ↦ ∫ t : ℝ, Ft t x * (χ t : ℂ)) ≤
        ENNReal.ofReal
          (C_dualDifferenceInterchange A J χ *
            (∫ h : ℝ, ‖∫ x : ℝ, ∫ t : ℝ,
              multiplicativeDifference h (Ft t) x * exponential (x * Φ h) * (χ t : ℂ)‖) ^
              (1 / (4 : ℝ))) := by
  rcases hA with ⟨a, b, hab, rfl⟩
  rcases hJ with ⟨c, d, hcd, rfl⟩
  let A : Set ℝ := Set.Icc a b
  let J : Set ℝ := Set.Icc c d
  let F : ℝ → ℂ := fun x ↦ ∫ t : ℝ, Ft t x * (χ t : ℂ)
  let D : Set ℝ := Set.image2 (fun s t : ℝ ↦ s - t) A A
  have hAcompact : IsCompact A := isCompact_Icc
  have hJcompact : IsCompact J := isCompact_Icc
  have hDcompact : IsCompact D := by
    dsimp [D]
    exact aux_isCompact_image2_sub A hAcompact
  obtain ⟨hFmeas, hFbound, hFsupp, hFone, hFtwo⟩ :=
    aux_dual_average_properties A J hAcompact hJcompact Ft hFt_measurable hFt_one_bounded
      hFt_support χ hχ_measurable hχ_nonneg hχ_le_one hχ_support
  have hs : Integrable (fun h : ℝ ↦
      (eLpNorm (𝓕 (multiplicativeDifference h F)) (∞ : ℝ≥0∞) volume).toReal)
      volume := aux_dual_fourier_linf_profile_integrable F hFmeas hFone hFtwo
  have hfin : ∀ h : ℝ,
      eLpNorm (𝓕 (multiplicativeDifference h F)) (∞ : ℝ≥0∞) volume < ∞ := by
    intro h
    exact (aux_eLpNorm_fourier_le_integral_norm (multiplicativeDifference h F)).trans_lt
      ENNReal.ofReal_lt_top
  let E : ℝ := ∫ h : ℝ,
    (eLpNorm (𝓕 (multiplicativeDifference h F)) (∞ : ℝ≥0∞) volume).toReal
  have hU : (uNorm 3 F) ^ (2 : ℝ) = ENNReal.ofReal E := by
    symm
    exact aux_dual_u3_square_from_real_integral F hs hfin
  have hE0 : 0 ≤ E := by
    dsimp [E]
    exact integral_nonneg fun h ↦ ENNReal.toReal_nonneg
  by_cases hEzero : E = 0
  · refine ⟨0, measurable_const, ?_⟩
    have hUzero : uNorm 3 F = 0 := by
      apply (ENNReal.rpow_eq_zero_iff_of_pos (by norm_num : (0 : ℝ) < 2)).mp
      rw [hU, hEzero]
      simp
    rw [hUzero]
    exact bot_le
  have hEpos : 0 < E := lt_of_le_of_ne hE0 (Ne.symm hEzero)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < E / 2 by linarith)
  let N : ℕ := n + 1
  have hN : 1 ≤ N := by
    dsimp [N]
    omega
  have hNerr : 1 / (N : ℝ) < E / 2 := by
    simpa [N, Nat.cast_add, Nat.cast_one] using hn
  obtain ⟨hDiffMeas, hDiffInt, hDiffSupp⟩ :=
    aux_dual_difference_data A F hFmeas hFtwo hFsupp
  have hAinterval : ∃ p q : ℝ, p ≤ q ∧ A = Set.Icc p q := by
    refine ⟨a, b, hab.le, ?_⟩
    rfl
  obtain ⟨φ, hφmeas, hlin⟩ := measurableFourierSupremumLinearization A hAinterval
    (fun h x ↦ multiplicativeDifference h F x) hDiffMeas hDiffInt hDiffSupp hs N hN
  let ψ : ℝ → ℝ := fun h ↦ -φ h
  have hψmeas : Measurable ψ := measurable_neg.comp hφmeas
  let z : ℝ → ℂ := fun h ↦ ∫ x : ℝ,
    multiplicativeDifference h F x * exponential (x * ψ h)
  have hzFourier : ∀ h : ℝ, z h = 𝓕 (multiplicativeDifference h F) (φ h) := by
    intro h
    dsimp [z, ψ]
    rw [← aux_fourier_neg_eq_exponential_integral]
    simp
  have hzmeas : Measurable z := by
    have hfour := aux_fourier_evaluation_measurable_comp
      (fun h x ↦ multiplicativeDifference h F x) hDiffMeas φ hφmeas
    have hformula : z = fun h : ℝ ↦ 𝓕 (multiplicativeDifference h F) (φ h) := by
      funext h
      exact hzFourier h
    rw [hformula]
    exact hfour
  let L : ℝ := ∫ h : ℝ, ‖z h‖
  have hEL : E ≤ 2 * L := by
    have hlin' : E - 1 / (N : ℝ) ≤ L := by
      simpa [E, L, hzFourier] using hlin
    have hhalf : 1 / (N : ℝ) ≤ E / 2 := hNerr.le
    linarith
  let u : ℝ → ℂ := fun h ↦
    if z h = 0 then 0 else star (z h) / (‖z h‖ : ℂ)
  have humeas : Measurable u := by
    simpa only [u] using aux_phase_measurable z hzmeas
  have hubound : ∀ h : ℝ, ‖u h‖ ≤ 1 := by
    intro h
    simpa only [u] using aux_norm_phase_le_one (z h)
  have husupport : ∀ h : ℝ, h ∉ D → u h = 0 := by
    intro h hh
    have hz0 : z h = 0 := by
      rw [hzFourier h]
      exact aux_fourier_difference_zero_off_difference A F hFsupp h (φ h) hh
    simp [u, hz0]
  have hFtjoint : ∀ᵐ q : ℝ × ℝ ∂volume.prod volume, ‖Ft q.1 q.2‖ ≤ 1 := by
    have hset : MeasurableSet {q : ℝ × ℝ | ‖Ft q.1 q.2‖ ≤ 1} :=
      measurableSet_le hFt_measurable.norm measurable_const
    rw [Measure.ae_prod_iff_ae_ae hset]
    exact Filter.Eventually.of_forall hFt_one_bounded
  have hRtriple := aux_selector_phase_kernel_integrable A J D hAcompact hJcompact hDcompact
    F Ft χ ψ u (volume.real J) MeasureTheory.measureReal_nonneg
    hFmeas.stronglyMeasurable hFt_measurable hχ_measurable hψmeas humeas
    hFbound hFsupp hFtjoint hχ_nonneg hχ_le_one hχ_support
    (Filter.Eventually.of_forall hubound) (Filter.Eventually.of_forall husupport)
  let X : Set ℝ := Set.image2 (fun a d : ℝ ↦ a - d) A D
  let Z : Set (ℝ × ℝ) := X ×ˢ J
  have hXcompact : IsCompact X := by
    dsimp only [X]
    rw [← Set.image_prod]
    exact (hAcompact.prod hDcompact).image (continuous_fst.sub continuous_snd)
  have hZcompact : IsCompact Z := hXcompact.prod hJcompact
  have hPmeas : AEStronglyMeasurable (Function.uncurry (aux_dualP Ft χ ψ u))
      ((volume.prod volume).prod volume) :=
    (aux_dualP_measurable Ft χ ψ u hFt_measurable hχ_measurable hψmeas humeas).aestronglyMeasurable
  have hPbound : ∀ᵐ q : (ℝ × ℝ) × ℝ ∂((volume.prod volume).prod volume),
      ‖aux_dualP Ft χ ψ u q.1 q.2‖ ≤ 1 :=
    aux_dualP_ae_one_bounded Ft χ ψ u hFt_measurable hFt_one_bounded hχ_le_one hubound
  have hPsupp : ∀ᵐ q : (ℝ × ℝ) × ℝ ∂((volume.prod volume).prod volume),
      q ∉ Z ×ˢ D → aux_dualP Ft χ ψ u q.1 q.2 = 0 := by
    simpa only [Z, X] using aux_dualP_ae_zero_outside A J D Ft χ ψ u
      hAcompact.isClosed.measurableSet hFt_measurable hFt_support hχ_support husupport
  obtain ⟨hPsections, hH⟩ := aux_pair_timeIntegral_memLp_compactSupport Z D hZcompact hDcompact
    (aux_dualP Ft χ ψ u) hPmeas hPbound hPsupp
  have hfirst := aux_first_physical_cauchy_sq_with_dualP A J hAcompact hJcompact
    F Ft χ ψ u hFmeas hFbound hFsupp hχ_measurable hχ_nonneg hχ_le_one hχ_support
    (by intro x; rfl) hRtriple hH
  have hphaseL : ‖∫ h : ℝ, z h * u h‖ = L := by
    simpa only [L, u] using aux_norm_phase_integral_eq_integral_norm z
  have hfirst' : L ^ (2 : ℕ) ≤
      volume.real A * (volume.real J) ^ (3 : ℕ) *
        ∫ z : ℝ × ℝ, ‖∫ h : ℝ, aux_dualP Ft χ ψ u z h‖ ^ (2 : ℝ)
          ∂(volume.prod volume) := by
    rw [← hphaseL]
    simpa only [z] using hfirst
  let B : ℝ := ∫ z : ℝ × ℝ, ‖∫ h : ℝ, aux_dualP Ft χ ψ u z h‖ ^ (2 : ℝ)
    ∂(volume.prod volume)
  have hLsq : L ^ (2 : ℕ) ≤ volume.real A * (volume.real J) ^ (3 : ℕ) * B := by
    simpa only [B] using hfirst'
  have hRshift := aux_dualP_autocorrelation_integrable_shift_first A J D
    hAcompact hJcompact hDcompact Ft χ ψ u hFt_measurable hFt_one_bounded hFt_support
    hχ_measurable hχ_le_one hχ_support hψmeas humeas hubound husupport
  obtain ⟨_, hRbase⟩ := aux_dualP_autocorrelation_conditions A J D
    hAcompact hJcompact hDcompact Ft χ ψ u hFt_measurable hFt_one_bounded hFt_support
    hχ_measurable hχ_le_one hχ_support hψmeas humeas hubound husupport
  obtain ⟨_, _, hTD, _⟩ := aux_target_indicator_joint_integrable A J D
    hAcompact hJcompact hDcompact Ft χ ψ hFt_measurable hFt_one_bounded hFt_support
    hχ_measurable hχ_nonneg hχ_le_one hχ_support hψmeas
  let T : ℝ → ℝ → ℂ := fun r s ↦ ∫ x : ℝ, ∫ t : ℝ,
    multiplicativeDifference r (Ft t) x *
      exponential (x * (ψ (s + r) - ψ s)) * (χ t : ℂ)
  have hTD' : Integrable (Function.uncurry fun r : ℝ ↦ fun s : ℝ ↦
      D.indicator (T r) s) (volume.prod volume) := by
    simpa only [T] using hTD
  have hBraw : B ≤ ∫ r : ℝ, ∫ s : ℝ in D, ‖T r s‖ := by
    have hbridge := aux_dualP_square_timeIntegral_le_target_doubleIntegralOn D
      hDcompact.isClosed.measurableSet Ft χ ψ u hχ_nonneg hubound husupport
      hPsections hH hRshift hRbase hTD'
    dsimp [B]
    simpa only [T, Real.rpow_two] using hbridge
  let Q : ℝ → ℝ := fun s ↦ ∫ r : ℝ, ‖T r s‖
  obtain ⟨hQint, hdouble⟩ := aux_base_target_integrableOn_and_swap D
    hDcompact.isClosed.measurableSet T hTD'
  have hBavg : B ≤ ∫ s : ℝ in D, Q s := hBraw.trans_eq hdouble
  have hDmeasure : volume.real D = 2 * volume.real A := by
    dsimp only [D, A]
    exact aux_u3_difference_set_measure_Icc a b hab.le
  have hApos : 0 < volume.real A := by
    dsimp only [A]
    rw [Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
    exact sub_pos.mpr hab
  have hDpos : 0 < volume.real D := by
    rw [hDmeasure]
    positivity
  have hDfinite : volume D ≠ ∞ := hDcompact.measure_lt_top.ne
  obtain ⟨s₀, hs₀D, hselect⟩ := aux_exists_measure_mul_ge_of_le_setIntegral
    D hDpos hDfinite Q hQint B hBavg
  have hBselect : B ≤ 2 * volume.real A * Q s₀ := by
    rw [hDmeasure] at hselect
    exact hselect
  let Φ : ℝ → ℝ := fun r ↦ ψ (r + s₀) - ψ s₀
  have hΦmeas : Measurable Φ := by
    dsimp only [Φ]
    exact (hψmeas.comp (measurable_id.add measurable_const)).sub measurable_const
  have hQfinal : Q s₀ = ∫ r : ℝ, ‖∫ x : ℝ, ∫ t : ℝ,
      multiplicativeDifference r (Ft t) x * exponential (x * Φ r) * (χ t : ℂ)‖ := by
    simp only [Q, T, Φ, add_comm]
  obtain ⟨hSge, ha0, haS, hj0, hjS⟩ := aux_dual_difference_size_bounds A J χ
  have hQ0 : 0 ≤ Q s₀ := by
    dsimp only [Q]
    exact integral_nonneg fun r ↦ norm_nonneg _
  have hfinal := aux_ennreal_dual_difference_numerical_assembly
    (uNorm 3 F) E L (sizeParameter ![A, J] χ) (volume.real A) (volume.real J) B (Q s₀)
    hU hE0 hSge ha0 haS hj0 hjS hQ0 hEL hLsq hBselect
  refine ⟨Φ, hΦmeas, ?_⟩
  change uNorm 3 F ≤ ENNReal.ofReal
    (C_dualDifferenceInterchange A J χ *
      (∫ h : ℝ, ‖∫ x : ℝ, ∫ t : ℝ,
        multiplicativeDifference h (Ft t) x * exponential (x * Φ h) * (χ t : ℂ)‖) ^
        (1 / (4 : ℝ)))
  rw [hQfinal] at hfinal
  simpa only [C_dualDifferenceInterchange] using hfinal

end Auto
