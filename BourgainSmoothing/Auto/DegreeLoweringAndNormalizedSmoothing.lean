import BourgainSmoothing.Auto.SobolevNormsOfMultiplicativeDifferences

/-!
# Degree lowering and normalized smoothing

Formalizations of the labeled estimates in the corresponding section of
`blueprint/blueprint.tex`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Real FourierTransform

namespace Auto

/--
An admissible support datum is a tuple
\[
\mathfrak D=(A_0,A_1,A_2,J,\chi)
\]
where \(A_0,A_1,A_2,J\) are positive-length compact intervals,
\(\supp\chi\subset J\), and
\[
A_0+J\subset A_1.
\]
Write \(\ell_i=\lvert A_i\rvert\), \(\ell_J=\lvert J\rvert\), and
\[
A_F:=A_1-J.
\]

The regularity and bounds on `χ` record the standing-cutoff convention of the
manuscript.
-/
structure AdmissibleSupportData where
  A₀ : Set ℝ
  A₁ : Set ℝ
  A₂ : Set ℝ
  J : Set ℝ
  χ : ℝ → ℝ
  hA₀ : ∃ a b : ℝ, a < b ∧ A₀ = Set.Icc a b
  hA₁ : ∃ a b : ℝ, a < b ∧ A₁ = Set.Icc a b
  hA₂ : ∃ a b : ℝ, a < b ∧ A₂ = Set.Icc a b
  hJ : ∃ a b : ℝ, a < b ∧ J = Set.Icc a b
  hχ_smooth : ContDiff ℝ ⊤ χ
  hχ_compact : HasCompactSupport χ
  hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t
  hχ_le_one : ∀ t : ℝ, χ t ≤ 1
  hχ_support : tsupport χ ⊆ J
  hA₀_add_J : Set.image2 (fun x t : ℝ ↦ x + t) A₀ J ⊆ A₁

/-- The displayed interval \(A_F=A_1-J\) in \(\label{def:admissible-data}\).

This auxiliary set is used by `firstDualization` and `u2Control`.
-/
def aux_firstDualInterval (D : AdmissibleSupportData) : Set ℝ :=
  Set.image2 (fun y t : ℝ ↦ y - t) D.A₁ D.J

/-- The function \(F_0\) appearing in \(\label{lem:first-dualization}\).

This raw map is separated from `firstDualization` so that its support and
Cauchy--Schwarz conclusions can be stated together.
-/
def aux_firstDualFunction (χ : ℝ → ℝ) (f₁ f₂ : ℝ → ℂ) : ℝ → ℂ :=
  fun x ↦ ∫ t : ℝ,
    starRingEnd ℂ (f₁ (x + t) * f₂ (x + t ^ 2)) * (χ t : ℂ)

/-- The un-conjugated time kernel used to express the first dual function in
`firstDualization`. -/
def aux_firstDualKernel (χ : ℝ → ℝ) (f₁ f₂ : ℝ → ℂ) : ℝ → ℝ → ℂ :=
  fun x t ↦ f₁ (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ)

/-- The first-dual spatial interval is compact, which supplies the finite
measure localization in `firstDualization`. -/
lemma aux_firstDualInterval_compact (D : AdmissibleSupportData) :
    IsCompact (aux_firstDualInterval D) := by
  rcases D.hA₁ with ⟨a, b, hab, hA⟩
  rcases D.hJ with ⟨p, q, hpq, hJ⟩
  rw [aux_firstDualInterval, hA, hJ, ← Set.image_prod]
  exact (isCompact_Icc.prod isCompact_Icc).image (continuous_fst.sub continuous_snd)

/-- Computes the difference image of two closed real intervals; this supplies
the interval data needed to use the first-dual support in `u2Control`. -/
lemma aux_image2_sub_Icc (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) :
    Set.image2 (fun y t : ℝ ↦ y - t) (Set.Icc a b) (Set.Icc c d) =
      Set.Icc (a - d) (b - c) := by
  ext x
  constructor
  · rintro ⟨y, hy, t, ht, rfl⟩
    exact ⟨sub_le_sub hy.1 ht.2, sub_le_sub hy.2 ht.1⟩
  · intro hx
    rcases le_total x (a - c) with h | h
    · refine ⟨a, ⟨le_rfl, hab⟩, a - x, ?_, by ring⟩
      constructor <;> linarith [hx.1]
    · refine ⟨x + c, ?_, c, ⟨le_rfl, hcd⟩, by ring⟩
      constructor <;> linarith [hx.2]

/-- The first-dual spatial range is a positive-length compact interval. -/
lemma aux_firstDualInterval_interval (D : AdmissibleSupportData) :
    ∃ p q : ℝ, p < q ∧ aux_firstDualInterval D = Set.Icc p q := by
  rcases D.hA₁ with ⟨a, b, hab, hA₁⟩
  rcases D.hJ with ⟨c, d, hcd, hJ⟩
  refine ⟨a - d, b - c, ?_, ?_⟩
  · linarith
  · rw [aux_firstDualInterval, hA₁, hJ]
    exact aux_image2_sub_Icc a b c d hab.le hcd.le

/-- The first-dual kernel is jointly almost-everywhere strongly measurable. -/
lemma aux_firstDualKernel_aestronglyMeasurable
    (D : AdmissibleSupportData) (f₁ f₂ : ℝ → ℂ)
    (hf₁ : AEStronglyMeasurable f₁ volume)
    (hf₂ : AEStronglyMeasurable f₂ volume) :
    AEStronglyMeasurable (Function.uncurry (aux_firstDualKernel D.χ f₁ f₂))
      (volume.prod volume) := by
  have h₁ : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ f₁ (z.1 + z.2))
      (volume.prod volume) := by
    change AEStronglyMeasurable (f₁ ∘ fun z : ℝ × ℝ ↦ z.1 + z.2)
      (volume.prod volume)
    have h := hf₁.comp_quasiMeasurePreserving (aux_quasiMeasurePreserving_affine 1)
    simpa only [Function.comp_apply, one_mul] using h
  have h₂ : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ f₂ (z.1 + z.2 ^ 2))
      (volume.prod volume) :=
    hf₂.comp_quasiMeasurePreserving aux_u3_qmp_add_sq
  have hχ : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ (D.χ z.2 : ℂ))
      (volume.prod volume) :=
    (Complex.continuous_ofReal.comp
      (D.hχ_smooth.continuous.comp continuous_snd)).aestronglyMeasurable
  exact h₁.mul h₂ |>.mul hχ

/-- The compact first-dual kernel inherits the manuscript's one-bound. -/
lemma aux_firstDualKernel_ae_one_bounded
    (D : AdmissibleSupportData) (f₁ f₂ : ℝ → ℂ)
    (hf₁ : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₂ : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1) :
    ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      ‖aux_firstDualKernel D.χ f₁ f₂ z.1 z.2‖ ≤ 1 := by
  have h₁' : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      ‖f₁ (z.1 + 1 * z.2)‖ ≤ 1 :=
    (aux_quasiMeasurePreserving_affine 1).tendsto_ae hf₁
  have h₁ : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖f₁ (z.1 + z.2)‖ ≤ 1 := by
    simpa only [one_mul] using h₁'
  have h₂ : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖f₂ (z.1 + z.2 ^ 2)‖ ≤ 1 :=
    aux_u3_qmp_add_sq.tendsto_ae hf₂
  filter_upwards [h₁, h₂] with z hz₁ hz₂
  rw [aux_firstDualKernel, norm_mul, norm_mul]
  have hχ : ‖(D.χ z.2 : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (D.hχ_nonneg _)]
    exact D.hχ_le_one _
  calc
    ‖f₁ (z.1 + z.2)‖ * ‖f₂ (z.1 + z.2 ^ 2)‖ * ‖(D.χ z.2 : ℂ)‖ ≤
        1 * 1 * 1 := by gcongr
    _ = 1 := by norm_num

/-- The first-dual kernel vanishes almost everywhere outside its compact
spatial/time box. -/
lemma aux_firstDualKernel_ae_zero_outside
    (D : AdmissibleSupportData) (f₁ f₂ : ℝ → ℂ)
    (hf₁support : ∀ᵐ x ∂volume, x ∉ D.A₁ → f₁ x = 0) :
    ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∉ aux_firstDualInterval D ×ˢ D.J →
        aux_firstDualKernel D.χ f₁ f₂ z.1 z.2 = 0 := by
  have h₁' : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z.1 + 1 * z.2 ∉ D.A₁ → f₁ (z.1 + 1 * z.2) = 0 :=
    (aux_quasiMeasurePreserving_affine 1).tendsto_ae hf₁support
  have h₁ : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z.1 + z.2 ∉ D.A₁ → f₁ (z.1 + z.2) = 0 := by
    simpa only [one_mul] using h₁'
  filter_upwards [h₁] with z hz₁ hz
  by_cases ht : z.2 ∈ D.J
  · have hx : z.1 ∉ aux_firstDualInterval D := by
      intro hx
      exact hz ⟨hx, ht⟩
    have hnotA : z.1 + z.2 ∉ D.A₁ := by
      intro hy
      apply hx
      exact ⟨z.1 + z.2, hy, z.2, ht, by ring⟩
    simp [aux_firstDualKernel, hz₁ hnotA]
  · have hnot : z.2 ∉ tsupport D.χ := fun hts => ht (D.hχ_support hts)
    have hzero : D.χ z.2 = 0 := image_eq_zero_of_notMem_tsupport hnot
    simp [aux_firstDualKernel, hzero]

/-- The raw first-dual function is the conjugate of the un-conjugated kernel
section integral. -/
lemma aux_firstDualFunction_eq_star_kernelIntegral
    (χ : ℝ → ℝ) (f₁ f₂ : ℝ → ℂ) (x : ℝ) :
    aux_firstDualFunction χ f₁ f₂ x =
      starRingEnd ℂ (∫ t : ℝ, aux_firstDualKernel χ f₁ f₂ x t) := by
  rw [aux_firstDualFunction, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  simp only [aux_firstDualKernel, map_mul]
  simp

/-- The first dual function is square-integrable and supported almost
everywhere on its first-dual interval. -/
lemma aux_firstDualFunction_memLp_and_support
    (D : AdmissibleSupportData) (f₁ f₂ : ℝ → ℂ)
    (hf₁meas : AEStronglyMeasurable f₁ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₁bound : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₁support : ∀ᵐ x ∂volume, x ∉ D.A₁ → f₁ x = 0) :
    (∀ᵐ x ∂volume, x ∉ aux_firstDualInterval D →
      aux_firstDualFunction D.χ f₁ f₂ x = 0) ∧
      MemLp (aux_firstDualFunction D.χ f₁ f₂) (2 : ℝ≥0∞) volume := by
  let Q := aux_firstDualKernel D.χ f₁ f₂
  let X := aux_firstDualInterval D
  have hXcompact : IsCompact X := by
    exact aux_firstDualInterval_compact D
  have hQmeas : AEStronglyMeasurable (Function.uncurry Q)
      (volume.prod volume) := by
    exact aux_firstDualKernel_aestronglyMeasurable D f₁ f₂ hf₁meas hf₂meas
  have hQbound : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖Q z.1 z.2‖ ≤ 1 := by
    exact aux_firstDualKernel_ae_one_bounded D f₁ f₂ hf₁bound hf₂bound
  have hQsupport : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∉ X ×ˢ D.J → Q z.1 z.2 = 0 := by
    exact aux_firstDualKernel_ae_zero_outside D f₁ f₂ hf₁support
  have hTmeas : MeasurableSet (X ×ˢ D.J) :=
    hXcompact.isClosed.measurableSet.prod (by
      rcases D.hJ with ⟨a, b, hab, hJ⟩
      rw [hJ]
      exact measurableSet_Icc)
  have hTfinite : (volume.prod volume) (X ×ˢ D.J) < ∞ := by
    have hJcompact : IsCompact D.J := by
      rcases D.hJ with ⟨a, b, hab, hJ⟩
      rw [hJ]
      exact isCompact_Icc
    exact (hXcompact.prod hJcompact).measure_lt_top
  have hQmem : MemLp (Function.uncurry Q) 1 (volume.prod volume) :=
    aux_memLp_of_ae_bound_of_ae_support _ hQmeas 1 hQbound (X ×ˢ D.J)
      hTmeas hTfinite hQsupport 1
  have hQint : Integrable (Function.uncurry Q) (volume.prod volume) :=
    memLp_one_iff_integrable.mp hQmem
  have hsuppSections : ∀ᵐ x : ℝ ∂volume, ∀ᵐ t : ℝ ∂volume,
      (x, t) ∉ X ×ˢ D.J → Q x t = 0 :=
    Measure.ae_ae_of_ae_prod hQsupport
  have hrawSupport : ∀ᵐ x : ℝ ∂volume, x ∉ X → (∫ t : ℝ, Q x t) = 0 := by
    filter_upwards [hsuppSections] with x hx
    intro hnot
    rw [← integral_zero]
    apply integral_congr_ae
    filter_upwards [hx] with t ht
    apply ht
    intro hmem
    exact hnot hmem.1
  have hrawLp : MemLp (fun x : ℝ ↦ ∫ t : ℝ, Q x t) (2 : ℝ≥0∞) volume := by
    rcases D.hJ with ⟨a, b, hab, hJ⟩
    have hJcompact : IsCompact D.J := by
      rw [hJ]
      exact isCompact_Icc
    exact (aux_timeIntegral_memLp_compactSupport X D.J hXcompact hJcompact Q
      hQmeas hQbound hQsupport).2
  have hstarSupport : ∀ᵐ x : ℝ ∂volume, x ∉ X →
      starRingEnd ℂ (∫ t : ℝ, Q x t) = 0 := by
    filter_upwards [hrawSupport] with x hx hnot
    simp [hx hnot]
  have hstarLp : MemLp (fun x : ℝ ↦ starRingEnd ℂ (∫ t : ℝ, Q x t))
      (2 : ℝ≥0∞) volume := by
    exact hrawLp.star
  constructor
  · filter_upwards [hstarSupport] with x hx hnot
    rw [aux_firstDualFunction_eq_star_kernelIntegral]
    exact hx hnot
  · rw [show aux_firstDualFunction D.χ f₁ f₂ =
        fun x : ℝ ↦ starRingEnd ℂ (∫ t : ℝ, Q x t) by
      funext x
      exact aux_firstDualFunction_eq_star_kernelIntegral D.χ f₁ f₂ x]
    exact hstarLp

/-- The first dual function is almost everywhere bounded by the length of
the cutoff interval.  This is the normalization bound used in `u2Control`. -/
lemma aux_firstDualFunction_ae_bound
    (D : AdmissibleSupportData) (f₁ f₂ : ℝ → ℂ)
    (hf₁meas : AEStronglyMeasurable f₁ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₁bound : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₁support : ∀ᵐ x ∂volume, x ∉ D.A₁ → f₁ x = 0) :
    ∀ᵐ x ∂volume, ‖aux_firstDualFunction D.χ f₁ f₂ x‖ ≤ volume.real D.J := by
  let Q := aux_firstDualKernel D.χ f₁ f₂
  let X := aux_firstDualInterval D
  have hXcompact : IsCompact X := aux_firstDualInterval_compact D
  have hJcompact : IsCompact D.J := by
    rcases D.hJ with ⟨a, b, hab, hJ⟩
    rw [hJ]
    exact isCompact_Icc
  have hQmeas : AEStronglyMeasurable (Function.uncurry Q)
      (volume.prod volume) :=
    aux_firstDualKernel_aestronglyMeasurable D f₁ f₂ hf₁meas hf₂meas
  have hQbound : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖Q z.1 z.2‖ ≤ 1 :=
    aux_firstDualKernel_ae_one_bounded D f₁ f₂ hf₁bound hf₂bound
  have hQsupport : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∉ X ×ˢ D.J → Q z.1 z.2 = 0 :=
    aux_firstDualKernel_ae_zero_outside D f₁ f₂ hf₁support
  have hTmeas : MeasurableSet (X ×ˢ D.J) :=
    hXcompact.isClosed.measurableSet.prod hJcompact.isClosed.measurableSet
  have hTfinite : (volume.prod volume) (X ×ˢ D.J) < ∞ :=
    (hXcompact.prod hJcompact).measure_lt_top
  have hQmem : MemLp (Function.uncurry Q) 1 (volume.prod volume) :=
    aux_memLp_of_ae_bound_of_ae_support _ hQmeas 1 hQbound (X ×ˢ D.J)
      hTmeas hTfinite hQsupport 1
  have hQint : Integrable (Function.uncurry Q) (volume.prod volume) :=
    memLp_one_iff_integrable.mp hQmem
  have hsections : ∀ᵐ x : ℝ ∂volume, Integrable (Q x) volume :=
    hQint.prod_right_ae
  have hboundsections : ∀ᵐ x : ℝ ∂volume, ∀ᵐ t : ℝ ∂volume, ‖Q x t‖ ≤ 1 :=
    Measure.ae_ae_of_ae_prod hQbound
  have hsupportsections : ∀ᵐ x : ℝ ∂volume, ∀ᵐ t : ℝ ∂volume,
      (x, t) ∉ X ×ˢ D.J → Q x t = 0 :=
    Measure.ae_ae_of_ae_prod hQsupport
  have hJmeas : MeasurableSet D.J := hJcompact.isClosed.measurableSet
  have hJfinite : volume D.J < ∞ := hJcompact.measure_lt_top
  have hJint : Integrable (D.J.indicator (1 : ℝ → ℝ)) volume := by
    rw [← memLp_one_iff_integrable]
    exact memLp_indicator_const 1 hJmeas 1 (Or.inr hJfinite.ne)
  have hraw : ∀ᵐ x : ℝ ∂volume, ‖∫ t : ℝ, Q x t‖ ≤ volume.real D.J := by
    filter_upwards [hsections, hboundsections, hsupportsections] with x hxint hxbound hxsupport
    calc
      ‖∫ t : ℝ, Q x t‖ ≤ ∫ t : ℝ, ‖Q x t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, D.J.indicator (1 : ℝ → ℝ) t := by
        apply integral_mono_ae hxint.norm hJint
        filter_upwards [hxbound, hxsupport] with t htbound htsupport
        by_cases ht : t ∈ D.J
        · simp [ht, htbound]
        · have hnotT : (x, t) ∉ X ×ˢ D.J := by
            intro hmem
            change x ∈ X ∧ t ∈ D.J at hmem
            exact ht hmem.2
          simp [ht, htsupport hnotT]
      _ = volume.real D.J := by
        simpa only [Measure.real] using (integral_indicator_one (μ := volume) hJmeas)
  filter_upwards [hraw] with x hx
  rw [aux_firstDualFunction_eq_star_kernelIntegral]
  simpa [Q] using hx

/-- Each interval length entering the four-set size parameter is bounded by
that size parameter.  This is the constant bookkeeping for `u2Control`. -/
lemma aux_intervalLength_le_sizeParameter_four
    (A₀ A₁ A₂ J : Set ℝ) (χ : ℝ → ℝ) (i : Fin 4) :
    intervalLength (![A₀, A₁, A₂, J] i) ≤ sizeParameter ![A₀, A₁, A₂, J] χ := by
  let v : Fin 4 → ℝ := fun k ↦ intervalLength (![A₀, A₁, A₂, J] k)
  have hbdd : BddAbove (Set.range v) := by
    refine ⟨max (intervalLength A₀)
      (max (intervalLength A₁) (max (intervalLength A₂) (intervalLength J))), ?_⟩
    rintro x ⟨k, rfl⟩
    fin_cases k <;> simp [v, le_max_iff]
  have hmem : intervalLength (![A₀, A₁, A₂, J] i) ∈ Set.range v := ⟨i, by simp [v]⟩
  have hsup : intervalLength (![A₀, A₁, A₂, J] i) ≤ sSup (Set.range v) :=
    le_csSup hbdd hmem
  let r : ℝ := max (supportRadius χ ^ 2)
    (max (eLpNorm χ 1 volume).toReal
      (max (eLpNorm χ 2 volume).toReal
        (max (eLpNorm (deriv χ) 1 volume).toReal
          (eLpNorm (deriv χ) 2 volume).toReal)))
  have hmax : sSup (Set.range v) ≤ max (sSup (Set.range v)) r := le_max_left _ _
  change intervalLength (![A₀, A₁, A₂, J] i) ≤ 2 + max (sSup (Set.range v)) r
  linarith

/-- The four-set size parameter is at least two. -/
lemma aux_two_le_sizeParameter_four (A₀ A₁ A₂ J : Set ℝ) (χ : ℝ → ℝ) :
    2 ≤ sizeParameter ![A₀, A₁, A₂, J] χ := by
  unfold sizeParameter
  exact le_add_of_nonneg_right (by positivity)

/-- The original trilinear form is the outer pairing with the conjugate of
the first dual function. -/
lemma aux_firstDualization_trilinear_eq_pairing
    (χ : ℝ → ℝ) (f₀ f₁ f₂ : ℝ → ℂ) :
    trilinearForm χ f₀ f₁ f₂ =
      ∫ x : ℝ, f₀ x * starRingEnd ℂ (aux_firstDualFunction χ f₁ f₂ x) := by
  unfold trilinearForm
  apply integral_congr_ae
  filter_upwards with x
  calc
    (∫ t : ℝ, f₀ x * f₁ (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ)) =
        ∫ t : ℝ, f₀ x * aux_firstDualKernel χ f₁ f₂ x t := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [aux_firstDualKernel]
      ring
    _ = f₀ x * ∫ t : ℝ, aux_firstDualKernel χ f₁ f₂ x t :=
      integral_const_mul _ _
    _ = f₀ x * starRingEnd ℂ (aux_firstDualFunction χ f₁ f₂ x) := by
      rw [aux_firstDualFunction_eq_star_kernelIntegral]
      simp

/-- The second trilinear form in `firstDualization` is exactly the
nonnegative `L²` energy of the first dual function. -/
lemma aux_firstDualization_dual_trilinearAbs_eq_energy
    (χ : ℝ → ℝ) (f₁ f₂ : ℝ → ℂ) :
    trilinearFormAbs χ (aux_firstDualFunction χ f₁ f₂) f₁ f₂ =
      ∫ x : ℝ, ‖aux_firstDualFunction χ f₁ f₂ x‖ ^ (2 : ℝ) := by
  unfold trilinearFormAbs trilinearForm
  have hpair : (∫ x : ℝ, ∫ t : ℝ,
      aux_firstDualFunction χ f₁ f₂ x * f₁ (x + t) * f₂ (x + t ^ 2) *
        (χ t : ℂ)) =
      ∫ x : ℝ, aux_firstDualFunction χ f₁ f₂ x *
        starRingEnd ℂ (aux_firstDualFunction χ f₁ f₂ x) := by
    apply integral_congr_ae
    filter_upwards with x
    calc
      (∫ t : ℝ, aux_firstDualFunction χ f₁ f₂ x * f₁ (x + t) * f₂ (x + t ^ 2) *
          (χ t : ℂ)) =
          ∫ t : ℝ, aux_firstDualFunction χ f₁ f₂ x *
            aux_firstDualKernel χ f₁ f₂ x t := by
        apply integral_congr_ae
        filter_upwards with t
        simp only [aux_firstDualKernel]
        ring
      _ = aux_firstDualFunction χ f₁ f₂ x *
          ∫ t : ℝ, aux_firstDualKernel χ f₁ f₂ x t :=
        integral_const_mul _ _
      _ = aux_firstDualFunction χ f₁ f₂ x *
          starRingEnd ℂ (aux_firstDualFunction χ f₁ f₂ x) := by
        rw [aux_firstDualFunction_eq_star_kernelIntegral]
        simp
  rw [hpair]
  calc
    ‖∫ x : ℝ, aux_firstDualFunction χ f₁ f₂ x *
        starRingEnd ℂ (aux_firstDualFunction χ f₁ f₂ x)‖ =
        ‖∫ x : ℝ,
          ((‖aux_firstDualFunction χ f₁ f₂ x‖ ^ (2 : ℝ) : ℝ) : ℂ)‖ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      rw [RCLike.mul_conj]
      norm_num [Real.rpow_two]
    _ = ∫ x : ℝ, ‖aux_firstDualFunction χ f₁ f₂ x‖ ^ (2 : ℝ) := by
      have hcast : (∫ x : ℝ,
          ((‖aux_firstDualFunction χ f₁ f₂ x‖ ^ (2 : ℝ) : ℝ) : ℂ)) =
          ((∫ x : ℝ, ‖aux_firstDualFunction χ f₁ f₂ x‖ ^ (2 : ℝ) : ℝ) : ℂ) :=
        integral_ofReal
      rw [hcast, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)]

/-- The Cauchy--Schwarz estimate for the first dualization after the compact
kernel properties have supplied its square-integrable dual input. -/
lemma aux_firstDualization_cauchy_bound
    (D : AdmissibleSupportData) (f₀ f₁ f₂ : ℝ → ℂ)
    (hf₀meas : AEStronglyMeasurable f₀ volume)
    (hf₁meas : AEStronglyMeasurable f₁ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₀bound : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₁bound : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₀support : ∀ᵐ x ∂volume, x ∉ D.A₀ → f₀ x = 0)
    (hf₁support : ∀ᵐ x ∂volume, x ∉ D.A₁ → f₁ x = 0) :
    trilinearFormAbs D.χ f₀ f₁ f₂ ≤
      intervalLength D.A₀ ^ (1 / (2 : ℝ)) *
        trilinearFormAbs D.χ (aux_firstDualFunction D.χ f₁ f₂) f₁ f₂ ^
          (1 / (2 : ℝ)) := by
  have hA₀compact : IsCompact D.A₀ := by
    rcases D.hA₀ with ⟨a, b, hab, hA⟩
    rw [hA]
    exact isCompact_Icc
  have hA₀meas : MeasurableSet D.A₀ := hA₀compact.isClosed.measurableSet
  have hf₀Lp : MemLp f₀ (2 : ℝ≥0∞) volume :=
    aux_memLp_of_ae_bound_of_ae_support f₀ hf₀meas 1 hf₀bound D.A₀ hA₀meas
      hA₀compact.measure_lt_top hf₀support 2
  have henergy₀ : (∫ x : ℝ, ‖f₀ x‖ ^ (2 : ℝ)) ≤ volume.real D.A₀ :=
    aux_energy_le_measure D.A₀ hA₀meas hA₀compact.measure_lt_top.ne f₀ hf₀Lp
      hf₀bound hf₀support
  have hFdata := aux_firstDualFunction_memLp_and_support D f₁ f₂
    hf₁meas hf₂meas hf₁bound hf₂bound hf₁support
  have hF₂ : MemLp (aux_firstDualFunction D.χ f₁ f₂) (2 : ℝ≥0∞) volume :=
    hFdata.2
  have houter := aux_outer_cauchy f₀
    (fun x : ℝ ↦ starRingEnd ℂ (aux_firstDualFunction D.χ f₁ f₂ x))
    hf₀Lp hF₂.star
  have hE₀nonneg : 0 ≤ ∫ x : ℝ, ‖f₀ x‖ ^ (2 : ℝ) :=
    integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _
  have hE₀pow : (∫ x : ℝ, ‖f₀ x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤
      (volume.real D.A₀) ^ (1 / (2 : ℝ)) :=
    Real.rpow_le_rpow hE₀nonneg henergy₀ (by norm_num)
  have hFenergyNonneg : 0 ≤ ∫ x : ℝ,
      ‖aux_firstDualFunction D.χ f₁ f₂ x‖ ^ (2 : ℝ) :=
    integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _
  calc
    trilinearFormAbs D.χ f₀ f₁ f₂ =
        ‖∫ x : ℝ, f₀ x * starRingEnd ℂ (aux_firstDualFunction D.χ f₁ f₂ x)‖ := by
      unfold trilinearFormAbs
      rw [aux_firstDualization_trilinear_eq_pairing]
    _ ≤ (∫ x : ℝ, ‖f₀ x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (∫ x : ℝ, ‖aux_firstDualFunction D.χ f₁ f₂ x‖ ^ (2 : ℝ)) ^
          (1 / (2 : ℝ)) := by
      simpa [RCLike.star_def] using houter
    _ ≤ (volume.real D.A₀) ^ (1 / (2 : ℝ)) *
        (∫ x : ℝ, ‖aux_firstDualFunction D.χ f₁ f₂ x‖ ^ (2 : ℝ)) ^
          (1 / (2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hE₀pow
        (Real.rpow_nonneg hFenergyNonneg _)
    _ = intervalLength D.A₀ ^ (1 / (2 : ℝ)) *
        trilinearFormAbs D.χ (aux_firstDualFunction D.χ f₁ f₂) f₁ f₂ ^
          (1 / (2 : ℝ)) := by
      rw [aux_firstDualization_dual_trilinearAbs_eq_energy]
      rfl

/--
Let \(\mathfrak D\) be admissible and let \(f_0,f_1,f_2\) be \(1\)-bounded
with \(f_i\) supported in \(A_i\). Define
\[
F_0(x):=\int_\R\overline{f_1(x+t)f_2(x+t^2)}\chi(t)\dd t.
\]
Then \(F_0\) is supported in \(A_F\) and
\[
\Ichi(f_0,f_1,f_2)
\leq
\ell_0^{1/2}\Ichi(F_0,f_1,f_2)^{1/2}.
\]
-/
theorem firstDualization
    (D : AdmissibleSupportData) (f₀ f₁ f₂ : ℝ → ℂ)
    (hf₀_measurable : AEStronglyMeasurable f₀ volume)
    (hf₁_measurable : AEStronglyMeasurable f₁ volume)
    (hf₂_measurable : AEStronglyMeasurable f₂ volume)
    (hf₀_one_bounded : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₁_one_bounded : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₂_one_bounded : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₀_support : ∀ᵐ x ∂volume, x ∉ D.A₀ → f₀ x = 0)
    (hf₁_support : ∀ᵐ x ∂volume, x ∉ D.A₁ → f₁ x = 0)
    (_hf₂_support : ∀ᵐ x ∂volume, x ∉ D.A₂ → f₂ x = 0) :
    (∀ᵐ x ∂volume, x ∉ aux_firstDualInterval D →
      aux_firstDualFunction D.χ f₁ f₂ x = 0) ∧
      trilinearFormAbs D.χ f₀ f₁ f₂ ≤
        intervalLength D.A₀ ^ (1 / (2 : ℝ)) *
          trilinearFormAbs D.χ (aux_firstDualFunction D.χ f₁ f₂) f₁ f₂ ^
            (1 / (2 : ℝ)) := by
  constructor
  · exact (aux_firstDualFunction_memLp_and_support D f₁ f₂ hf₁_measurable
      hf₂_measurable hf₁_one_bounded hf₂_one_bounded hf₁_support).1
  · exact aux_firstDualization_cauchy_bound D f₀ f₁ f₂ hf₀_measurable
      hf₁_measurable hf₂_measurable hf₀_one_bounded hf₁_one_bounded hf₂_one_bounded
      hf₀_support hf₁_support

/-- The `u²` quantity is invariant under equality almost everywhere; this
removes the measurable representatives used internally in `u2Control`. -/
lemma aux_u2_uNorm_two_congr_ae (f g : ℝ → ℂ) (hfg : f =ᵐ[volume] g) :
    uNorm 2 f = uNorm 2 g := by
  change eLpNorm (𝓕 f) ∞ volume = eLpNorm (𝓕 g) ∞ volume
  apply eLpNorm_congr_ae
  filter_upwards with ξ
  exact Real.fourier_congr_ae hfg ξ

/-- The canonical measurable representative has the same `u²` quantity as
the original AE-measurable function, for the end of `u2Control`. -/
lemma aux_u2_uNorm_two_mk_eq (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f volume) :
    uNorm 2 (AEStronglyMeasurable.mk f hf) = uNorm 2 f := by
  exact (aux_u2_uNorm_two_congr_ae f (AEStronglyMeasurable.mk f hf)
    hf.ae_eq_mk).symm

/-- Measurability of the canonical representative used in the first-dual
family for `u2Control`. -/
lemma aux_u2_mk_measurable (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f volume) :
    Measurable (AEStronglyMeasurable.mk f hf) := hf.measurable_mk

/-- A canonical measurable representative preserves an almost-everywhere
unit bound needed in the `u2Control` interchange and bilinear steps. -/
lemma aux_u2_mk_ae_one_bounded (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1) :
    ∀ᵐ x ∂volume, ‖AEStronglyMeasurable.mk f hf x‖ ≤ 1 := by
  filter_upwards [hf.ae_eq_mk, hbound] with x hx hbound
  rw [← hx]
  exact hbound

/-- A canonical measurable representative preserves an almost-everywhere
support condition needed in the `u2Control` bilinear step. -/
lemma aux_u2_mk_ae_zero_outside (A : Set ℝ) (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f volume)
    (hsupport : ∀ᵐ x ∂volume, x ∉ A → f x = 0) :
    ∀ᵐ x ∂volume, x ∉ A → AEStronglyMeasurable.mk f hf x = 0 := by
  filter_upwards [hf.ae_eq_mk, hsupport] with x hx hsupport
  intro hnot
  rw [← hx]
  exact hsupport hnot

/-- The `s = 1` Sobolev-difference estimate applied to a canonical measurable
representative, with its `u²` term returned to the original function for the
post-interchange argument in `u2Control`. -/
lemma aux_u2_sobolevDifferenceEstimateS1_mk
    (A : Set ℝ) (hA : ∃ a b : ℝ, a < b ∧ A = Set.Icc a b)
    (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hsupport : ∀ᵐ x ∂volume, x ∉ A → f x = 0) :
    (∫⁻ h : ℝ,
      aux_sobolevNormRaw (1 / 2 : ℝ)
        (multiplicativeDifference h (AEStronglyMeasurable.mk f hf)) ^ (2 : ℝ)) ≤
      ENNReal.ofReal (C_sobolevDifferenceEstimate 1 A) *
        uNorm 2 f ^ (1 / (2 : ℝ)) := by
  have hmain := sobolevDifferenceEstimateS1 A hA
    (AEStronglyMeasurable.mk f hf)
    (hf.measurable_mk.aestronglyMeasurable)
    (aux_u2_mk_ae_one_bounded f hf hbound)
    (aux_u2_mk_ae_zero_outside A f hf hsupport)
  rw [aux_u2_uNorm_two_mk_eq] at hmain
  exact hmain

/-- Compact interval support and the unit bound put the canonical measurable
representative in `L²`, as required in the final Cauchy--Schwarz step of
`u2Control`. -/
lemma aux_u2_mk_memLp_two
    (A : Set ℝ) (hA : ∃ a b : ℝ, a < b ∧ A = Set.Icc a b)
    (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hsupport : ∀ᵐ x ∂volume, x ∉ A → f x = 0) :
    MemLp (AEStronglyMeasurable.mk f hf) (2 : ℝ≥0∞) volume := by
  rcases hA with ⟨a, b, hab, rfl⟩
  exact aux_memLp_of_ae_bound_of_ae_support _
    hf.measurable_mk.aestronglyMeasurable 1
    (aux_u2_mk_ae_one_bounded f hf hbound) (Set.Icc a b)
    measurableSet_Icc isCompact_Icc.measure_lt_top
    (aux_u2_mk_ae_zero_outside (Set.Icc a b) f hf hsupport) 2

/-- The `L²` multiplicative-difference estimate applies unchanged to a
canonical representative in the post-bilinear step of `u2Control`. -/
lemma aux_u2_differenceL2_mk
    (A : Set ℝ) (hA : ∃ a b : ℝ, a < b ∧ A = Set.Icc a b)
    (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hsupport : ∀ᵐ x ∂volume, x ∉ A → f x = 0) :
    (∫⁻ h : ℝ,
      eLpNorm (multiplicativeDifference h (AEStronglyMeasurable.mk f hf))
        (2 : ℝ≥0∞) volume ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤
      ENNReal.ofReal (intervalLength A) := by
  have hmem := aux_u2_mk_memLp_two A hA f hf hbound hsupport
  exact (differenceL2Identity _ hmem).2 A
    (by rcases hA with ⟨a, b, hab, hA⟩; exact ⟨a, b, hab.le, hA⟩)
    (aux_u2_mk_ae_zero_outside A f hf hsupport)
    (aux_u2_mk_ae_one_bounded f hf hbound)

/-- The time-indexed conjugated product used to apply the dual-difference
interchange theorem inside `u2Control`. -/
def aux_u2Family (D : AdmissibleSupportData) (f₁ f₂ : ℝ → ℂ) :
    ℝ → ℝ → ℂ := by
  classical
  exact fun t x ↦ ({z : ℝ × ℝ | z.1 ∈ D.J}.indicator
    (fun z ↦ starRingEnd ℂ (f₁ (z.2 + z.1) * f₂ (z.2 + z.1 ^ 2)))) (t, x)

/-- Measurable inputs give a jointly measurable `aux_u2Family`; this is the
joint measurability hypothesis in the interchange step of `u2Control`. -/
lemma aux_u2Family_measurable (D : AdmissibleSupportData) (f₁ f₂ : ℝ → ℂ)
    (hf₁ : Measurable f₁) (hf₂ : Measurable f₂) :
    Measurable (Function.uncurry (aux_u2Family D f₁ f₂)) := by
  have hJmeas : MeasurableSet D.J := by
    rcases D.hJ with ⟨a, b, hab, hJ⟩
    rw [hJ]
    exact measurableSet_Icc
  have h₁ : Measurable (fun z : ℝ × ℝ ↦ f₁ (z.2 + z.1)) :=
    hf₁.comp (continuous_snd.add continuous_fst).measurable
  have h₂ : Measurable (fun z : ℝ × ℝ ↦ f₂ (z.2 + z.1 ^ 2)) :=
    hf₂.comp (continuous_snd.add (continuous_fst.pow 2)).measurable
  have hstar : Measurable (fun z : ℝ × ℝ ↦
      starRingEnd ℂ (f₁ (z.2 + z.1) * f₂ (z.2 + z.1 ^ 2))) :=
    continuous_star.measurable.comp (h₁.mul h₂)
  have hset : MeasurableSet {z : ℝ × ℝ | z.1 ∈ D.J} :=
    hJmeas.preimage measurable_fst
  change Measurable ({z : ℝ × ℝ | z.1 ∈ D.J}.indicator
    (fun z ↦ starRingEnd ℂ (f₁ (z.2 + z.1) * f₂ (z.2 + z.1 ^ 2))))
  exact hstar.indicator hset

/-- The first-dual family inherits the fibrewise unit bound needed by
`dualDifferenceInterchange` in the proof of `u2Control`. -/
lemma aux_u2Family_ae_one_bounded (D : AdmissibleSupportData) (f₁ f₂ : ℝ → ℂ)
    (hf₁ : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₂ : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1) :
    ∀ t : ℝ, ∀ᵐ x ∂volume, ‖aux_u2Family D f₁ f₂ t x‖ ≤ 1 := by
  intro t
  by_cases ht : t ∈ D.J
  · have h₁ : ∀ᵐ x : ℝ ∂volume, ‖f₁ (x + t)‖ ≤ 1 := by
      exact (measurePreserving_add_right volume t).quasiMeasurePreserving.tendsto_ae hf₁
    have h₂ : ∀ᵐ x : ℝ ∂volume, ‖f₂ (x + t ^ 2)‖ ≤ 1 := by
      exact (measurePreserving_add_right volume (t ^ 2)).quasiMeasurePreserving.tendsto_ae hf₂
    filter_upwards [h₁, h₂] with x hx₁ hx₂
    have hpair : (t, x) ∈ {z : ℝ × ℝ | z.1 ∈ D.J} := ht
    rw [aux_u2Family, Set.indicator_of_mem hpair, starRingEnd_apply,
      norm_star, norm_mul]
    nlinarith [norm_nonneg (f₁ (x + t)), norm_nonneg (f₂ (x + t ^ 2))]
  · filter_upwards with x
    simp [aux_u2Family, ht]

/-- Every fibre of the first-dual family is supported in the first-dual
interval; this supplies the support hypothesis for `dualDifferenceInterchange`
in `u2Control`. -/
lemma aux_u2Family_ae_zero_outside (D : AdmissibleSupportData)
    (f₁ f₂ : ℝ → ℂ)
    (hf₁ : ∀ᵐ x ∂volume, x ∉ D.A₁ → f₁ x = 0) :
    ∀ t : ℝ, ∀ᵐ x ∂volume, x ∉ aux_firstDualInterval D →
      aux_u2Family D f₁ f₂ t x = 0 := by
  intro t
  by_cases ht : t ∈ D.J
  · have h₁ : ∀ᵐ x : ℝ ∂volume, x + t ∉ D.A₁ → f₁ (x + t) = 0 := by
      exact (measurePreserving_add_right volume t).quasiMeasurePreserving.tendsto_ae hf₁
    filter_upwards [h₁] with x hx hnot
    have hnotA : x + t ∉ D.A₁ := by
      intro hmem
      apply hnot
      exact ⟨x + t, hmem, t, ht, by ring⟩
    simp [aux_u2Family, ht, hx hnotA]
  · filter_upwards with x
    simp [aux_u2Family, ht]

/-- Measurable representatives of the AE-measurable inputs supply all the
family hypotheses for the interchange step in `u2Control`. -/
lemma aux_u2Family_mk_data (D : AdmissibleSupportData) (f₁ f₂ : ℝ → ℂ)
    (hf₁meas : AEStronglyMeasurable f₁ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₁bound : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₁support : ∀ᵐ x ∂volume, x ∉ D.A₁ → f₁ x = 0) :
    let g₁ := AEStronglyMeasurable.mk f₁ hf₁meas
    let g₂ := AEStronglyMeasurable.mk f₂ hf₂meas
    Measurable (Function.uncurry (aux_u2Family D g₁ g₂)) ∧
      (∀ t : ℝ, ∀ᵐ x ∂volume, ‖aux_u2Family D g₁ g₂ t x‖ ≤ 1) ∧
      (∀ t : ℝ, ∀ᵐ x ∂volume, x ∉ aux_firstDualInterval D →
        aux_u2Family D g₁ g₂ t x = 0) := by
  dsimp
  have hg₁meas : Measurable (AEStronglyMeasurable.mk f₁ hf₁meas) :=
    hf₁meas.measurable_mk
  have hg₂meas : Measurable (AEStronglyMeasurable.mk f₂ hf₂meas) :=
    hf₂meas.measurable_mk
  have hg₁bound : ∀ᵐ x ∂volume, ‖AEStronglyMeasurable.mk f₁ hf₁meas x‖ ≤ 1 := by
    filter_upwards [hf₁meas.ae_eq_mk, hf₁bound] with x hx hbound
    rw [← hx]
    exact hbound
  have hg₂bound : ∀ᵐ x ∂volume, ‖AEStronglyMeasurable.mk f₂ hf₂meas x‖ ≤ 1 := by
    filter_upwards [hf₂meas.ae_eq_mk, hf₂bound] with x hx hbound
    rw [← hx]
    exact hbound
  have hg₁support : ∀ᵐ x ∂volume,
      x ∉ D.A₁ → AEStronglyMeasurable.mk f₁ hf₁meas x = 0 := by
    filter_upwards [hf₁meas.ae_eq_mk, hf₁support] with x hx hsupport
    intro hnot
    rw [← hx]
    exact hsupport hnot
  exact ⟨aux_u2Family_measurable D _ _ hg₁meas hg₂meas,
    aux_u2Family_ae_one_bounded D _ _ hg₁bound hg₂bound,
    aux_u2Family_ae_zero_outside D _ _ hg₁support⟩

/-- Inserting the time-support indicator in `aux_u2Family` does not alter
its cutoff-weighted average; this identifies that average with the first dual
function in `u2Control`. -/
lemma aux_u2Family_average_eq_firstDualFunction
    (D : AdmissibleSupportData) (f₁ f₂ : ℝ → ℂ) (x : ℝ) :
    (∫ t : ℝ, aux_u2Family D f₁ f₂ t x * (D.χ t : ℂ)) =
      aux_firstDualFunction D.χ f₁ f₂ x := by
  rw [aux_firstDualFunction]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ D.J
  · have hpair : (t, x) ∈ {z : ℝ × ℝ | z.1 ∈ D.J} := ht
    rw [aux_u2Family, Set.indicator_of_mem hpair]
  · have hnot : t ∉ tsupport D.χ := fun hts ↦ ht (D.hχ_support hts)
    have hzero : D.χ t = 0 := image_eq_zero_of_notMem_tsupport hnot
    have hpair : (t, x) ∉ {z : ℝ × ℝ | z.1 ∈ D.J} := ht
    rw [aux_u2Family, Set.indicator_of_notMem hpair]
    simp [hzero]

/-- A multiplicative difference of `aux_u2Family` is the conjugated product
of the two corresponding differences, the algebraic bridge for the bilinear
estimate in `u2Control`. -/
lemma aux_u2Family_difference_pointwise
    (D : AdmissibleSupportData) (f₁ f₂ : ℝ → ℂ) (h t x : ℝ) :
    (by
      classical
      exact multiplicativeDifference h (aux_u2Family D f₁ f₂ t) x =
        if t ∈ D.J then
          starRingEnd ℂ
            (multiplicativeDifference h f₁ (x + t) *
              multiplicativeDifference h f₂ (x + t ^ 2)) else 0) := by
  classical
  by_cases ht : t ∈ D.J
  · have hpair₀ : (t, x) ∈ {z : ℝ × ℝ | z.1 ∈ D.J} := ht
    have hpair₁ : (t, x + h) ∈ {z : ℝ × ℝ | z.1 ∈ D.J} := ht
    rw [multiplicativeDifference, aux_u2Family, aux_u2Family,
      Set.indicator_of_mem hpair₀, Set.indicator_of_mem hpair₁, ite_eq_left ht]
    rw [show starRingEnd ℂ
        (multiplicativeDifference h f₁ (x + t) *
          multiplicativeDifference h f₂ (x + t ^ 2)) =
        starRingEnd ℂ (multiplicativeDifference h f₁ (x + t)) *
          starRingEnd ℂ (multiplicativeDifference h f₂ (x + t ^ 2)) by
      exact map_mul _ _ _]
    have hstar_mul (a b : ℂ) : star (a * b) = star a * star b := by
      rw [← starRingEnd_apply, map_mul, starRingEnd_apply, starRingEnd_apply]
    simp only [multiplicativeDifference, starRingEnd_apply, star_star]
    rw [hstar_mul (f₁ (x + t)) (f₂ (x + t ^ 2)),
      hstar_mul (f₁ (x + t)) (star (f₁ (x + t + h))),
      hstar_mul (f₂ (x + t ^ 2)) (star (f₂ (x + t ^ 2 + h)))]
    simp only [star_star]
    ring_nf
  · have hpair₀ : (t, x) ∉ {z : ℝ × ℝ | z.1 ∈ D.J} := ht
    rw [multiplicativeDifference, aux_u2Family,
      Set.indicator_of_notMem hpair₀, ite_eq_right ht]
    simp

/-- The dual-difference target of `aux_u2Family` is the conjugate of the
frequency-character trilinear form to which `bilinearSobolevEstimates` applies
in `u2Control`. -/
lemma aux_u2Family_difference_target_eq_star_trilinear
    (D : AdmissibleSupportData) (f₁ f₂ : ℝ → ℂ) (h ξ : ℝ) :
    (∫ x : ℝ, ∫ t : ℝ,
      multiplicativeDifference h (aux_u2Family D f₁ f₂ t) x *
        exponential (x * ξ) * (D.χ t : ℂ)) =
      starRingEnd ℂ
        (trilinearForm D.χ (frequencyCharacter (-ξ))
          (multiplicativeDifference h f₁) (multiplicativeDifference h f₂)) := by
  unfold trilinearForm
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  have hphase : exponential (x * ξ) =
      starRingEnd ℂ (frequencyCharacter (-ξ) x) := by
    rw [frequencyCharacter, aux_phase_star_exponential]
    congr 1
    ring
  rw [aux_u2Family_difference_pointwise]
  classical
  by_cases ht : t ∈ D.J
  · rw [ite_eq_left ht]
    have hstar_mul (a b : ℂ) : starRingEnd ℂ (a * b) =
        starRingEnd ℂ a * starRingEnd ℂ b := by
      exact map_mul _ _ _
    rw [hstar_mul]
    rw [map_mul, map_mul, map_mul]
    rw [hphase]
    simp only [Complex.conj_ofReal]
    ring
  · have hnot : t ∉ tsupport D.χ := fun hts ↦ ht (D.hχ_support hts)
    have hzero : D.χ t = 0 := image_eq_zero_of_notMem_tsupport hnot
    rw [ite_eq_right ht]
    simp [hzero]

/-- Norm form of the first-dual difference target identity, used to put the
interchange output into the exact form required by `bilinearSobolevEstimates`
in `u2Control`. -/
lemma aux_u2Family_difference_target_norm_eq_trilinearAbs
    (D : AdmissibleSupportData) (f₁ f₂ : ℝ → ℂ) (h ξ : ℝ) :
    ‖∫ x : ℝ, ∫ t : ℝ,
      multiplicativeDifference h (aux_u2Family D f₁ f₂ t) x *
        exponential (x * ξ) * (D.χ t : ℂ)‖ =
      trilinearFormAbs D.χ (frequencyCharacter (-ξ))
        (multiplicativeDifference h f₁) (multiplicativeDifference h f₂) := by
  rw [aux_u2Family_difference_target_eq_star_trilinear, starRingEnd_apply, norm_star]
  rfl

/-- The first-dual function is unchanged almost everywhere by replacing its
inputs with almost-everywhere equal representatives; this removes the
representatives introduced for `u2Control`. -/
lemma aux_firstDualFunction_congr_ae
    (χ : ℝ → ℝ) (f₁ g₁ f₂ g₂ : ℝ → ℂ)
    (h₁ : f₁ =ᵐ[volume] g₁) (h₂ : f₂ =ᵐ[volume] g₂) :
    aux_firstDualFunction χ f₁ f₂ =ᵐ[volume]
      aux_firstDualFunction χ g₁ g₂ := by
  have h₁' : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      f₁ (z.1 + 1 * z.2) = g₁ (z.1 + 1 * z.2) :=
    (aux_quasiMeasurePreserving_affine 1).tendsto_ae h₁
  have h₁'' : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      f₁ (z.1 + z.2) = g₁ (z.1 + z.2) := by
    simpa only [one_mul] using h₁'
  have h₂' : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      f₂ (z.1 + z.2 ^ 2) = g₂ (z.1 + z.2 ^ 2) :=
    aux_u3_qmp_add_sq.tendsto_ae h₂
  have hkernel : Function.uncurry (aux_firstDualKernel χ f₁ f₂) =ᵐ[volume.prod volume]
      Function.uncurry (aux_firstDualKernel χ g₁ g₂) := by
    filter_upwards [h₁'', h₂'] with z hz₁ hz₂
    change aux_firstDualKernel χ f₁ f₂ z.1 z.2 = aux_firstDualKernel χ g₁ g₂ z.1 z.2
    simp only [aux_firstDualKernel, hz₁, hz₂]
  have hsections : ∀ᵐ x : ℝ ∂volume, ∀ᵐ t : ℝ ∂volume,
      aux_firstDualKernel χ f₁ f₂ x t = aux_firstDualKernel χ g₁ g₂ x t :=
    Measure.ae_ae_of_ae_prod hkernel
  filter_upwards [hsections] with x hx
  rw [aux_firstDualFunction_eq_star_kernelIntegral,
    aux_firstDualFunction_eq_star_kernelIntegral]
  congr 1
  apply integral_congr_ae
  filter_upwards [hx] with t ht
  exact ht

/-- The averaged measurable representative family agrees almost everywhere
with the original first-dual function, as needed by `u2Control`. -/
lemma aux_u2Family_mk_average_ae_eq_firstDualFunction
    (D : AdmissibleSupportData) (f₁ f₂ : ℝ → ℂ)
    (hf₁meas : AEStronglyMeasurable f₁ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume) :
    (fun x : ℝ ↦ ∫ t : ℝ,
      aux_u2Family D (AEStronglyMeasurable.mk f₁ hf₁meas)
        (AEStronglyMeasurable.mk f₂ hf₂meas) t x * (D.χ t : ℂ)) =ᵐ[volume]
      aux_firstDualFunction D.χ f₁ f₂ := by
  have hcongr := aux_firstDualFunction_congr_ae D.χ f₁
    (AEStronglyMeasurable.mk f₁ hf₁meas) f₂
    (AEStronglyMeasurable.mk f₂ hf₂meas)
    hf₁meas.ae_eq_mk hf₂meas.ae_eq_mk
  filter_upwards [hcongr.symm] with x hx
  rw [aux_u2Family_average_eq_firstDualFunction]
  exact hx

/-- The representative-family average has the same `u³` seminorm as the
first-dual function, allowing the interchange bound to be used in `u2Control`. -/
lemma aux_u2Family_mk_average_uNorm_three_eq_firstDualFunction
    (D : AdmissibleSupportData) (f₁ f₂ : ℝ → ℂ)
    (hf₁meas : AEStronglyMeasurable f₁ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume) :
    uNorm 3 (fun x : ℝ ↦ ∫ t : ℝ,
      aux_u2Family D (AEStronglyMeasurable.mk f₁ hf₁meas)
        (AEStronglyMeasurable.mk f₂ hf₂meas) t x * (D.χ t : ℂ)) =
      uNorm 3 (aux_firstDualFunction D.χ f₁ f₂) := by
  exact aux_u3_uNorm_three_congr_ae _ _
    (aux_u2Family_mk_average_ae_eq_firstDualFunction D f₁ f₂ hf₁meas hf₂meas)

/-- `dualDifferenceInterchange` specialized to the first-dual family, with
its left side identified with the original first-dual function for use in
`u2Control`. -/
lemma aux_u2_dualDifferenceInterchange_firstDual
    (D : AdmissibleSupportData) (f₁ f₂ : ℝ → ℂ)
    (hf₁meas : AEStronglyMeasurable f₁ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₁bound : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₁support : ∀ᵐ x ∂volume, x ∉ D.A₁ → f₁ x = 0) :
    ∃ Φ : ℝ → ℝ, Measurable Φ ∧
      uNorm 3 (aux_firstDualFunction D.χ f₁ f₂) ≤
        ENNReal.ofReal
          (C_dualDifferenceInterchange (aux_firstDualInterval D) D.J D.χ *
            (∫ h : ℝ, ‖∫ x : ℝ, ∫ t : ℝ,
              multiplicativeDifference h
                  (aux_u2Family D (AEStronglyMeasurable.mk f₁ hf₁meas)
                    (AEStronglyMeasurable.mk f₂ hf₂meas) t) x *
                exponential (x * Φ h) * (D.χ t : ℂ)‖) ^ (1 / (4 : ℝ))) := by
  obtain ⟨hFtmeas, hFtbound, hFtsupport⟩ := aux_u2Family_mk_data D f₁ f₂
    hf₁meas hf₂meas hf₁bound hf₂bound hf₁support
  have hχmeas : Measurable D.χ := D.hχ_smooth.continuous.measurable
  have hχsupport : ∀ᵐ t : ℝ ∂volume, t ∉ D.J → D.χ t = 0 :=
    Filter.Eventually.of_forall fun t ht ↦
      image_eq_zero_of_notMem_tsupport (fun hts ↦ ht (D.hχ_support hts))
  obtain ⟨Φ, hΦmeas, hDDI⟩ := dualDifferenceInterchange
    (aux_firstDualInterval D) D.J (aux_firstDualInterval_interval D) D.hJ
    (aux_u2Family D (AEStronglyMeasurable.mk f₁ hf₁meas)
      (AEStronglyMeasurable.mk f₂ hf₂meas)) hFtmeas hFtbound hFtsupport
    D.χ hχmeas D.hχ_nonneg D.hχ_le_one hχsupport
  refine ⟨Φ, hΦmeas, ?_⟩
  rw [aux_u2Family_mk_average_uNorm_three_eq_firstDualFunction] at hDDI
  exact hDDI

/-- The specialized dual-difference estimate rewritten in terms of the
frequency-character trilinear forms to which `bilinearSobolevEstimates`
applies in `u2Control`. -/
lemma aux_u2_dualDifferenceInterchange_firstDual_trilinear
    (D : AdmissibleSupportData) (f₁ f₂ : ℝ → ℂ)
    (hf₁meas : AEStronglyMeasurable f₁ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₁bound : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₁support : ∀ᵐ x ∂volume, x ∉ D.A₁ → f₁ x = 0) :
    ∃ Φ : ℝ → ℝ, Measurable Φ ∧
      uNorm 3 (aux_firstDualFunction D.χ f₁ f₂) ≤
        ENNReal.ofReal
          (C_dualDifferenceInterchange (aux_firstDualInterval D) D.J D.χ *
            (∫ h : ℝ,
              trilinearFormAbs D.χ (frequencyCharacter (-Φ h))
                (multiplicativeDifference h (AEStronglyMeasurable.mk f₁ hf₁meas))
                (multiplicativeDifference h (AEStronglyMeasurable.mk f₂ hf₂meas))) ^
              (1 / (4 : ℝ))) := by
  obtain ⟨Φ, hΦmeas, hDDI⟩ := aux_u2_dualDifferenceInterchange_firstDual D f₁ f₂
    hf₁meas hf₂meas hf₁bound hf₂bound hf₁support
  have htarget :
      (∫ h : ℝ, ‖∫ x : ℝ, ∫ t : ℝ,
        multiplicativeDifference h
            (aux_u2Family D (AEStronglyMeasurable.mk f₁ hf₁meas)
              (AEStronglyMeasurable.mk f₂ hf₂meas) t) x *
          exponential (x * Φ h) * (D.χ t : ℂ)‖) =
        ∫ h : ℝ,
          trilinearFormAbs D.χ (frequencyCharacter (-Φ h))
            (multiplicativeDifference h (AEStronglyMeasurable.mk f₁ hf₁meas))
            (multiplicativeDifference h (AEStronglyMeasurable.mk f₂ hf₂meas)) := by
    apply integral_congr_ae
    filter_upwards with h
    exact aux_u2Family_difference_target_norm_eq_trilinearAbs D
      (AEStronglyMeasurable.mk f₁ hf₁meas) (AEStronglyMeasurable.mk f₂ hf₂meas)
      h (Φ h)
  refine ⟨Φ, hΦmeas, ?_⟩
  rw [htarget] at hDDI
  exact hDDI

/-- Compact support and boundedness put each first multiplicative difference
in `L²`; this prepares the pointwise bilinear bound in `u2Control`. -/
lemma aux_u2_multiplicativeDifference_memLp_two
    (a b : ℝ) (f : ℝ → ℂ)
    (hfmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hsupp : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f x = 0)
    (h : ℝ) :
    MemLp (multiplicativeDifference h f) (2 : ℝ≥0∞) volume := by
  have hmem := aux_sobolevDifference_iteratedDifference_memLp_Icc 1
    (fun _ : Fin 1 ↦ h) a b f hfmeas hbound hsupp 2
  simpa [iteratedMultiplicativeDifference] using hmem

/-- The first multiplicative differences used in the Sobolev profile are
also in `L¹`, allowing its raw Fourier-energy description in `u2Control`. -/
lemma aux_u2_multiplicativeDifference_memLp_one
    (a b : ℝ) (f : ℝ → ℂ)
    (hfmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hsupp : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f x = 0)
    (h : ℝ) :
    MemLp (multiplicativeDifference h f) (1 : ℝ≥0∞) volume := by
  have hmem := aux_sobolevDifference_iteratedDifference_memLp_Icc 1
    (fun _ : Fin 1 ↦ h) a b f hfmeas hbound hsupp 1
  simpa [iteratedMultiplicativeDifference] using hmem

/-- The raw half-Sobolev profile of a first difference is finite under the
bounded interval support hypotheses of `u2Control`. -/
lemma aux_u2_multiplicativeDifference_sobolevRaw_half_lt_top
    (a b : ℝ) (f : ℝ → ℂ)
    (hfmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hsupp : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f x = 0)
    (h : ℝ) :
    aux_sobolevNormRaw (1 / 2 : ℝ) (multiplicativeDifference h f) < ∞ := by
  let hd := aux_u2_multiplicativeDifference_memLp_two a b f hfmeas hbound hsupp h
  rw [aux_sobolevDifference_sobolevNormRaw_eq_sobolevNorm _ _ hd]
  exact aux_bilinear_sobolevNorm_half_lt_top hd.toLp

/-- The first bilinear Sobolev estimate expressed in the raw Sobolev wrapper
that appears after dual-difference interchange in `u2Control`. -/
lemma aux_u2_direct_trilinear_bilinear_bound
    (D : AdmissibleSupportData) (f₁ f₂ : ℝ → ℂ)
    (hf₁meas : AEStronglyMeasurable f₁ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₁bound : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₁support : ∀ᵐ x ∂volume, x ∉ D.A₁ → f₁ x = 0)
    (hf₂support : ∀ᵐ x ∂volume, x ∉ D.A₂ → f₂ x = 0)
    (h ξ : ℝ) :
    trilinearFormAbs D.χ (frequencyCharacter (-ξ))
      (multiplicativeDifference h f₁) (multiplicativeDifference h f₂) ≤
      C_bilinearSobolevEstimates D.J D.χ *
        (aux_sobolevNormRaw (1 / 2 : ℝ)
          (multiplicativeDifference h f₁)).toReal *
        (eLpNorm (multiplicativeDifference h f₂) 2 volume).toReal := by
  rcases D.hA₁ with ⟨a₁, b₁, ha₁b₁, hA₁⟩
  rcases D.hA₂ with ⟨a₂, b₂, ha₂b₂, hA₂⟩
  have hd₁ : MemLp (multiplicativeDifference h f₁) (2 : ℝ≥0∞) volume := by
    rw [hA₁] at hf₁support
    exact aux_u2_multiplicativeDifference_memLp_two a₁ b₁ f₁
      hf₁meas hf₁bound hf₁support h
  have hd₂ : MemLp (multiplicativeDifference h f₂) (2 : ℝ≥0∞) volume := by
    rw [hA₂] at hf₂support
    exact aux_u2_multiplicativeDifference_memLp_two a₂ b₂ f₂
      hf₂meas hf₂bound hf₂support h
  have hzero : MemLp (fun _ : ℝ ↦ (0 : ℂ)) (2 : ℝ≥0∞) volume := by
    exact MemLp.zero
  have hbil := (bilinearSobolevEstimates D.J D.χ
    (by rcases D.hJ with ⟨a, b, hab, hJ⟩; exact ⟨a, b, hab.le, hJ⟩)
    D.hχ_smooth D.hχ_compact D.hχ_nonneg D.hχ_le_one D.hχ_support (-ξ)
    (fun _ : ℝ ↦ (0 : ℂ)) (multiplicativeDifference h f₁)
    (multiplicativeDifference h f₂) hzero hd₁ hd₂).1
  rw [aux_sobolevDifference_sobolevNormRaw_eq_sobolevNorm _ _ hd₁]
  exact hbil

/-- Passing a nonnegative real integral to its `ENNReal` form is bounded by
the corresponding lower integral; this lets `u2Control` use Hölder. -/
lemma aux_u2_ofReal_integral_le_lintegral_ofReal_of_nonneg
    (g : ℝ → ℝ) (hg : ∀ x, 0 ≤ g x) :
    ENNReal.ofReal (∫ x : ℝ, g x) ≤ ∫⁻ x : ℝ, ENNReal.ofReal (g x) := by
  by_cases hgintegrable : Integrable g volume
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgintegrable
      (Filter.Eventually.of_forall hg)]
  · rw [MeasureTheory.integral_undef hgintegrable]
    simp

/-- A finite real bilinear bound can be lifted to an `ENNReal` bound, for
use beneath the lower integral in the proof of `u2Control`. -/
lemma aux_u2_ofReal_bilinear_bound
    (C r : ℝ) (A B : ℝ≥0∞)
    (hC : 0 ≤ C) (hA : A < ∞) (hB : B < ∞)
    (hr : r ≤ C * A.toReal * B.toReal) :
    ENNReal.ofReal r ≤ ENNReal.ofReal C * A * B := by
  calc
    ENNReal.ofReal r ≤ ENNReal.ofReal (C * A.toReal * B.toReal) :=
      ENNReal.ofReal_le_ofReal hr
    _ = ENNReal.ofReal C * A * B := by
      calc
        ENNReal.ofReal (C * A.toReal * B.toReal) =
            ENNReal.ofReal (C * A.toReal) * ENNReal.ofReal B.toReal :=
          ENNReal.ofReal_mul (mul_nonneg hC ENNReal.toReal_nonneg)
        _ = (ENNReal.ofReal C * ENNReal.ofReal A.toReal) * ENNReal.ofReal B.toReal := by
          rw [ENNReal.ofReal_mul hC]
        _ = ENNReal.ofReal C * A * B := by
          rw [ENNReal.ofReal_toReal hA.ne, ENNReal.ofReal_toReal hB.ne]

/-- Cauchy--Schwarz for the two nonnegative profiles arising in the
post-interchange estimate of `u2Control`. -/
lemma aux_u2_lintegral_product_cauchy
    (A B : ℝ → ℝ≥0∞)
    (hA : AEMeasurable A volume) (hB : AEMeasurable B volume) :
    (∫⁻ h : ℝ, A h * B h) ≤
      (∫⁻ h : ℝ, A h ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (∫⁻ h : ℝ, B h ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  exact ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hA hB

/-- The `L²` norm profile of first differences is almost everywhere
measurable, enabling Cauchy--Schwarz in `u2Control`. -/
lemma aux_u2_multiplicativeDifference_eLpNorm_two_aemeasurable
    (a b : ℝ) (f : ℝ → ℂ)
    (hfmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hsupp : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f x = 0) :
    AEMeasurable (fun h : ℝ ↦
      eLpNorm (multiplicativeDifference h f) 2 volume) volume := by
  let e : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.piUnique _
  have he : MeasurePreserving e volume volume := volume_preserving_piUnique _
  have hsqFin := aux_sobolevDifference_iteratedDifference_l2_energy_aemeasurable 1
    (Set.Icc a b) f hfmeas hbound hsupp
  have heinv : MeasurePreserving e.symm volume volume := he.symm e
  have hsqComp := hsqFin.comp_quasiMeasurePreserving heinv.quasiMeasurePreserving
  have hsq : AEMeasurable (fun h : ℝ ↦
      eLpNorm (multiplicativeDifference h f) 2 volume ^ (2 : ℝ)) volume := by
    convert hsqComp using 1
    funext h
    simp [e, iteratedMultiplicativeDifference]
  have hroot : AEMeasurable (fun h : ℝ ↦
      (eLpNorm (multiplicativeDifference h f) 2 volume ^ (2 : ℝ)) ^
        (1 / (2 : ℝ))) volume :=
    AEMeasurable.comp_aemeasurable
      (ENNReal.continuous_rpow_const (y := (1 / (2 : ℝ))).aemeasurable) hsq
  convert hroot using 1
  funext h
  rw [← ENNReal.rpow_mul]
  norm_num

/-- The raw half-Sobolev profile of first differences is almost everywhere
measurable, completing the hypotheses for integrated Cauchy--Schwarz in
`u2Control`. -/
lemma aux_u2_multiplicativeDifference_sobolevRaw_half_aemeasurable
    (a b : ℝ) (f : ℝ → ℂ)
    (hfmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hsupp : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f x = 0) :
    AEMeasurable (fun h : ℝ ↦
      aux_sobolevNormRaw (1 / 2 : ℝ) (multiplicativeDifference h f)) volume := by
  have hjap : Continuous japaneseBracket := by
    unfold japaneseBracket
    fun_prop
  have hweightCont : Continuous (fun ξ : ℝ ↦
      japaneseBracket ξ ^ (-(1 / (2 : ℝ)))) := by
    apply hjap.rpow continuous_const
    intro ξ
    left
    unfold japaneseBracket
    exact ne_of_gt (Real.sqrt_pos.2 (by nlinarith [sq_nonneg |ξ|]))
  have hweight : AEStronglyMeasurable (fun z : ℝ × ℝ ↦
      ((japaneseBracket z.2 ^ (-(1 / (2 : ℝ))) : ℝ) : ℂ))
      (volume.prod volume) :=
    (Complex.continuous_ofReal.comp (hweightCont.comp continuous_snd)).aestronglyMeasurable
  have hjoint := aux_sobolevDifference_joint_aestronglyMeasurable_fourier_difference f hfmeas
  have henergyJoint : AEMeasurable (fun z : ℝ × ℝ ↦
      ‖((japaneseBracket z.2 ^ (-(1 / (2 : ℝ))) : ℝ) : ℂ) •
        𝓕 (multiplicativeDifference z.1 f) z.2‖ₑ ^ (2 : ℕ))
      (volume.prod volume) :=
    (hweight.smul hjoint).enorm.pow measurable_const.aemeasurable
  have henergy := henergyJoint.lintegral_prod_right'
  have hsq : AEMeasurable (fun h : ℝ ↦
      aux_sobolevNormRaw (1 / 2 : ℝ) (multiplicativeDifference h f) ^ (2 : ℝ))
      volume := by
    apply henergy.congr
    filter_upwards with h
    symm
    exact aux_sobolevDifference_sobolevNormRaw_sq_eq_raw_fourier_energy
      (1 / 2 : ℝ) (multiplicativeDifference h f)
      (aux_u2_multiplicativeDifference_memLp_one a b f hfmeas hbound hsupp h)
      (aux_u2_multiplicativeDifference_memLp_two a b f hfmeas hbound hsupp h)
  have hroot : AEMeasurable (fun h : ℝ ↦
      (aux_sobolevNormRaw (1 / 2 : ℝ) (multiplicativeDifference h f) ^ (2 : ℝ)) ^
        (1 / (2 : ℝ))) volume :=
    AEMeasurable.comp_aemeasurable
      (ENNReal.continuous_rpow_const (y := (1 / (2 : ℝ))).aemeasurable) hsq
  convert hroot using 1
  funext h
  rw [← ENNReal.rpow_mul]
  norm_num

/-- The parameter-integrated bilinear estimate preceding the final size
bookkeeping in `u2Control`. -/
lemma aux_u2_direct_trilinear_Q_bound
    (D : AdmissibleSupportData) (f₁ f₂ : ℝ → ℂ)
    (hf₁meas : AEStronglyMeasurable f₁ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₁bound : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₁support : ∀ᵐ x ∂volume, x ∉ D.A₁ → f₁ x = 0)
    (hf₂support : ∀ᵐ x ∂volume, x ∉ D.A₂ → f₂ x = 0)
    (φ : ℝ → ℝ)
    (hSobMeas : AEMeasurable
      (fun h : ℝ ↦ aux_sobolevNormRaw (1 / 2 : ℝ)
        (multiplicativeDifference h f₁)) volume)
    (hL2Meas : AEMeasurable
      (fun h : ℝ ↦ eLpNorm (multiplicativeDifference h f₂) 2 volume) volume) :
    ENNReal.ofReal (∫ h : ℝ,
      trilinearFormAbs D.χ (frequencyCharacter (-φ h))
        (multiplicativeDifference h f₁) (multiplicativeDifference h f₂)) ≤
      ENNReal.ofReal (C_bilinearSobolevEstimates D.J D.χ) *
        (ENNReal.ofReal (C_sobolevDifferenceEstimate 1 D.A₁) *
          uNorm 2 f₁ ^ (1 / (2 : ℝ))) ^ (1 / (2 : ℝ)) *
        ENNReal.ofReal (intervalLength D.A₂) := by
  let A : ℝ → ℝ≥0∞ := fun h ↦ aux_sobolevNormRaw (1 / 2 : ℝ)
    (multiplicativeDifference h f₁)
  let B : ℝ → ℝ≥0∞ := fun h ↦ eLpNorm (multiplicativeDifference h f₂) 2 volume
  let R : ℝ → ℝ := fun h ↦
    trilinearFormAbs D.χ (frequencyCharacter (-φ h))
      (multiplicativeDifference h f₁) (multiplicativeDifference h f₂)
  have hCnonneg : 0 ≤ C_bilinearSobolevEstimates D.J D.χ := by
    unfold C_bilinearSobolevEstimates
    positivity
  rcases D.hA₁ with ⟨a₁, b₁, ha₁b₁, hA₁⟩
  rcases D.hA₂ with ⟨a₂, b₂, ha₂b₂, hA₂⟩
  have hAfinite : ∀ h : ℝ, A h < ∞ := by
    intro h
    dsimp [A]
    rw [hA₁] at hf₁support
    exact aux_u2_multiplicativeDifference_sobolevRaw_half_lt_top a₁ b₁ f₁
      hf₁meas hf₁bound hf₁support h
  have hBfinite : ∀ h : ℝ, B h < ∞ := by
    intro h
    dsimp [B]
    rw [hA₂] at hf₂support
    exact (aux_u2_multiplicativeDifference_memLp_two a₂ b₂ f₂
      hf₂meas hf₂bound hf₂support h).eLpNorm_lt_top
  have hpoint : ∀ h : ℝ,
      ENNReal.ofReal (R h) ≤ ENNReal.ofReal (C_bilinearSobolevEstimates D.J D.χ) *
        A h * B h := by
    intro h
    apply aux_u2_ofReal_bilinear_bound
    · exact hCnonneg
    · exact hAfinite h
    · exact hBfinite h
    · dsimp [R, A, B]
      exact aux_u2_direct_trilinear_bilinear_bound D f₁ f₂
        hf₁meas hf₂meas hf₁bound hf₂bound hf₁support hf₂support h (φ h)
  have hS1 : (∫⁻ h : ℝ, A h ^ (2 : ℝ)) ≤
      ENNReal.ofReal (C_sobolevDifferenceEstimate 1 D.A₁) *
        uNorm 2 f₁ ^ (1 / (2 : ℝ)) := by
    simpa [A] using sobolevDifferenceEstimateS1 D.A₁ D.hA₁ f₁
      hf₁meas hf₁bound hf₁support
  have hf₂Lp : MemLp f₂ (2 : ℝ≥0∞) volume := by
    rw [hA₂] at hf₂support
    exact aux_memLp_of_ae_bound_of_ae_support f₂ hf₂meas 1 hf₂bound
      (Set.Icc a₂ b₂) measurableSet_Icc isCompact_Icc.measure_lt_top hf₂support 2
  have hL2 : (∫⁻ h : ℝ, B h ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤
      ENNReal.ofReal (intervalLength D.A₂) := by
    dsimp [B]
    exact (differenceL2Identity f₂ hf₂Lp).2 D.A₂
      ⟨a₂, b₂, ha₂b₂.le, hA₂⟩ hf₂support hf₂bound
  have hCauchy := aux_u2_lintegral_product_cauchy A B
    (by simpa [A] using hSobMeas) (by simpa [B] using hL2Meas)
  calc
    ENNReal.ofReal (∫ h : ℝ, R h) ≤ ∫⁻ h : ℝ, ENNReal.ofReal (R h) :=
      aux_u2_ofReal_integral_le_lintegral_ofReal_of_nonneg R (fun h ↦ norm_nonneg _)
    _ ≤ ∫⁻ h : ℝ, ENNReal.ofReal (C_bilinearSobolevEstimates D.J D.χ) * A h * B h := by
      apply MeasureTheory.lintegral_mono
      intro h
      exact hpoint h
    _ = ∫⁻ h : ℝ, ENNReal.ofReal (C_bilinearSobolevEstimates D.J D.χ) *
        (A h * B h) := by
      apply MeasureTheory.lintegral_congr
      intro h
      ring
    _ = ENNReal.ofReal (C_bilinearSobolevEstimates D.J D.χ) *
        (∫⁻ h : ℝ, A h * B h) := by
      rw [← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (C_bilinearSobolevEstimates D.J D.χ) *
        ((∫⁻ h : ℝ, A h ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫⁻ h : ℝ, B h ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hCauchy bot_le
    _ ≤ ENNReal.ofReal (C_bilinearSobolevEstimates D.J D.χ) *
        ((ENNReal.ofReal (C_sobolevDifferenceEstimate 1 D.A₁) *
          uNorm 2 f₁ ^ (1 / (2 : ℝ))) ^ (1 / (2 : ℝ)) *
          (∫⁻ h : ℝ, B h ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) := by
      apply mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow hS1 (by positivity)) bot_le) bot_le
    _ ≤ ENNReal.ofReal (C_bilinearSobolevEstimates D.J D.χ) *
        (ENNReal.ofReal (C_sobolevDifferenceEstimate 1 D.A₁) *
          uNorm 2 f₁ ^ (1 / (2 : ℝ))) ^ (1 / (2 : ℝ)) *
        ENNReal.ofReal (intervalLength D.A₂) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL2 bot_le) bot_le

/-- Turnkey parameter-integrated bilinear estimate for the exact quantity
arising after first dual-difference interchange in `u2Control`. -/
lemma aux_u2_direct_trilinear_Q_bound_turnkey
    (D : AdmissibleSupportData) (f₁ f₂ : ℝ → ℂ)
    (hf₁meas : AEStronglyMeasurable f₁ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₁bound : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₁support : ∀ᵐ x ∂volume, x ∉ D.A₁ → f₁ x = 0)
    (hf₂support : ∀ᵐ x ∂volume, x ∉ D.A₂ → f₂ x = 0)
    (φ : ℝ → ℝ) :
    ENNReal.ofReal (∫ h : ℝ,
      trilinearFormAbs D.χ (frequencyCharacter (-φ h))
        (multiplicativeDifference h f₁) (multiplicativeDifference h f₂)) ≤
      ENNReal.ofReal (C_bilinearSobolevEstimates D.J D.χ) *
        (ENNReal.ofReal (C_sobolevDifferenceEstimate 1 D.A₁) *
          uNorm 2 f₁ ^ (1 / (2 : ℝ))) ^ (1 / (2 : ℝ)) *
        ENNReal.ofReal (intervalLength D.A₂) := by
  rcases D.hA₁ with ⟨a₁, b₁, ha₁b₁, hA₁⟩
  rcases D.hA₂ with ⟨a₂, b₂, ha₂b₂, hA₂⟩
  have hsupp₁ : ∀ᵐ x ∂volume, x ∉ Set.Icc a₁ b₁ → f₁ x = 0 := by
    simpa [hA₁] using hf₁support
  have hsupp₂ : ∀ᵐ x ∂volume, x ∉ Set.Icc a₂ b₂ → f₂ x = 0 := by
    simpa [hA₂] using hf₂support
  exact aux_u2_direct_trilinear_Q_bound D f₁ f₂
    hf₁meas hf₂meas hf₁bound hf₂bound hf₁support hf₂support φ
    (aux_u2_multiplicativeDifference_sobolevRaw_half_aemeasurable a₁ b₁ f₁
      hf₁meas hf₁bound hsupp₁)
    (aux_u2_multiplicativeDifference_eLpNorm_two_aemeasurable a₂ b₂ f₂
      hf₂meas hf₂bound hsupp₂)

/-- The turnkey parameter-integrated bilinear estimate specialized to the
measurable representatives used by
`aux_u2_dualDifferenceInterchange_firstDual_trilinear`. -/
lemma aux_u2_direct_trilinear_Q_bound_mk
    (D : AdmissibleSupportData) (f₁ f₂ : ℝ → ℂ)
    (hf₁meas : AEStronglyMeasurable f₁ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₁bound : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₁support : ∀ᵐ x ∂volume, x ∉ D.A₁ → f₁ x = 0)
    (hf₂support : ∀ᵐ x ∂volume, x ∉ D.A₂ → f₂ x = 0)
    (φ : ℝ → ℝ) :
    ENNReal.ofReal (∫ h : ℝ,
      trilinearFormAbs D.χ (frequencyCharacter (-φ h))
        (multiplicativeDifference h (AEStronglyMeasurable.mk f₁ hf₁meas))
        (multiplicativeDifference h (AEStronglyMeasurable.mk f₂ hf₂meas))) ≤
      ENNReal.ofReal (C_bilinearSobolevEstimates D.J D.χ) *
        (ENNReal.ofReal (C_sobolevDifferenceEstimate 1 D.A₁) *
          uNorm 2 f₁ ^ (1 / (2 : ℝ))) ^ (1 / (2 : ℝ)) *
        ENNReal.ofReal (intervalLength D.A₂) := by
  have h := aux_u2_direct_trilinear_Q_bound_turnkey D
    (AEStronglyMeasurable.mk f₁ hf₁meas) (AEStronglyMeasurable.mk f₂ hf₂meas)
    hf₁meas.stronglyMeasurable_mk.aestronglyMeasurable
    hf₂meas.stronglyMeasurable_mk.aestronglyMeasurable
    (aux_u2_mk_ae_one_bounded f₁ hf₁meas hf₁bound)
    (aux_u2_mk_ae_one_bounded f₂ hf₂meas hf₂bound)
    (aux_u2_mk_ae_zero_outside D.A₁ f₁ hf₁meas hf₁support)
    (aux_u2_mk_ae_zero_outside D.A₂ f₂ hf₂meas hf₂support) φ
  rw [aux_u2_uNorm_two_mk_eq f₁ hf₁meas] at h
  exact h

/-- Scalar homogeneity of the `u³` quantity.  Unlike the legacy general
invariance theorem, this specialized form needs no finiteness premise. -/
lemma aux_u2_uNorm_three_smul (a : ℂ) (f : ℝ → ℂ) :
    uNorm 3 (a • f) = ENNReal.ofReal ‖a‖ * uNorm 3 f := by
  simp only [uNorm, show 3 ≠ 2 by norm_num, ite_false,
    show 2 < 3 by norm_num, ite_true]
  rw [show (3 : ℕ) - 2 = 1 by norm_num]
  norm_num
  change
    (∫⁻ h : Fin 1 → ℝ,
      eLpNormEssSup (𝓕 (iteratedMultiplicativeDifference 1 h (a • f))) volume) ^
        (1 / (2 : ℝ)) =
      ‖a‖ₑ *
        (∫⁻ h : Fin 1 → ℝ,
          eLpNormEssSup (𝓕 (iteratedMultiplicativeDifference 1 h f)) volume) ^
          (1 / (2 : ℝ))
  have hpoint (h : Fin 1 → ℝ) :
      eLpNormEssSup (𝓕 (iteratedMultiplicativeDifference 1 h (a • f))) volume =
        ‖a‖ₑ ^ (2 : ℕ) *
          eLpNormEssSup (𝓕 (iteratedMultiplicativeDifference 1 h f)) volume := by
    simpa [Nat.zero_add, ← ofReal_norm] using
      aux_fourier_linf_iterated_smul_succ 0 h a f
  simp_rw [hpoint]
  rw [lintegral_const_mul' _ _ (by simp)]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  have hroot : (‖a‖ₑ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) = ‖a‖ₑ := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [hroot]

/-- Scalar homogeneity of the physical trilinear absolute form in its first
factor. -/
lemma aux_u2_trilinearFormAbs_smul_first
    (χ : ℝ → ℝ) (a : ℂ) (f₀ f₁ f₂ : ℝ → ℂ) :
    trilinearFormAbs χ (a • f₀) f₁ f₂ = ‖a‖ * trilinearFormAbs χ f₀ f₁ f₂ := by
  unfold trilinearFormAbs trilinearForm
  have hraw : (∫ x : ℝ, ∫ t : ℝ,
      (a • f₀) x * f₁ (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ)) =
        a * ∫ x : ℝ, ∫ t : ℝ,
          f₀ x * f₁ (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hraw, norm_mul]

/-- Each interval component is bounded by the nonconstant part of a
four-set size parameter. -/
lemma aux_u2_intervalLength_le_sizeParameter_four_sub_two
    (A₀ A₁ A₂ J : Set ℝ) (χ : ℝ → ℝ) (i : Fin 4) :
    intervalLength (![A₀, A₁, A₂, J] i) ≤
      sizeParameter ![A₀, A₁, A₂, J] χ - 2 := by
  let v : Fin 4 → ℝ := fun k ↦ intervalLength (![A₀, A₁, A₂, J] k)
  have hbdd : BddAbove (Set.range v) := by
    refine ⟨max (intervalLength A₀)
      (max (intervalLength A₁) (max (intervalLength A₂) (intervalLength J))), ?_⟩
    rintro x ⟨k, rfl⟩
    fin_cases k <;> simp [v, le_max_iff]
  have hmem : intervalLength (![A₀, A₁, A₂, J] i) ∈ Set.range v :=
    ⟨i, by simp [v]⟩
  have hsup : intervalLength (![A₀, A₁, A₂, J] i) ≤ sSup (Set.range v) :=
    le_csSup hbdd hmem
  let r : ℝ := max (supportRadius χ ^ 2)
    (max (eLpNorm χ 1 volume).toReal
      (max (eLpNorm χ 2 volume).toReal
        (max (eLpNorm (deriv χ) 1 volume).toReal
          (eLpNorm (deriv χ) 2 volume).toReal)))
  have hmax : sSup (Set.range v) ≤ max (sSup (Set.range v)) r := le_max_left _ _
  change intervalLength (![A₀, A₁, A₂, J] i) ≤
    2 + max (sSup (Set.range v)) r - 2
  linarith

/-- Enlarging the first spatial interval from `A₁` to `A₁-J` enlarges the
three-set size parameter by at most a factor of two. -/
lemma aux_u2_firstDual_three_size_le_two_four_size (D : AdmissibleSupportData) :
    sizeParameter ![aux_firstDualInterval D, D.A₂, D.J] D.χ ≤
      2 * sizeParameter ![D.A₀, D.A₁, D.A₂, D.J] D.χ := by
  let S : ℝ := sizeParameter ![D.A₀, D.A₁, D.A₂, D.J] D.χ
  let v₃ : Fin 3 → ℝ := fun k ↦ intervalLength (![aux_firstDualInterval D, D.A₂, D.J] k)
  let r : ℝ := max (supportRadius D.χ ^ 2)
    (max (eLpNorm D.χ 1 volume).toReal
      (max (eLpNorm D.χ 2 volume).toReal
        (max (eLpNorm (deriv D.χ) 1 volume).toReal
          (eLpNorm (deriv D.χ) 2 volume).toReal)))
  have hS : 2 ≤ S := by
    simpa [S] using aux_two_le_sizeParameter_four D.A₀ D.A₁ D.A₂ D.J D.χ
  have hA₁ : intervalLength D.A₁ ≤ S - 2 := by
    simpa [S] using aux_u2_intervalLength_le_sizeParameter_four_sub_two
      D.A₀ D.A₁ D.A₂ D.J D.χ 1
  have hA₂ : intervalLength D.A₂ ≤ S - 2 := by
    simpa [S] using aux_u2_intervalLength_le_sizeParameter_four_sub_two
      D.A₀ D.A₁ D.A₂ D.J D.χ 2
  have hJ : intervalLength D.J ≤ S - 2 := by
    simpa [S] using aux_u2_intervalLength_le_sizeParameter_four_sub_two
      D.A₀ D.A₁ D.A₂ D.J D.χ 3
  have hAF : intervalLength (aux_firstDualInterval D) ≤ 2 * S - 4 := by
    rcases D.hA₁ with ⟨a, b, hab, hA₁eq⟩
    rcases D.hJ with ⟨c, d, hcd, hJeq⟩
    calc
      intervalLength (aux_firstDualInterval D) =
          intervalLength D.A₁ + intervalLength D.J := by
        rw [aux_firstDualInterval, hA₁eq, hJeq]
        exact intervalSub a b c d hab.le hcd.le
      _ ≤ (S - 2) + (S - 2) := add_le_add hA₁ hJ
      _ = 2 * S - 4 := by ring
  have hr : r ≤ S - 2 := by
    change r ≤ 2 + max (sSup (Set.range fun i : Fin 4 ↦
      intervalLength (![D.A₀, D.A₁, D.A₂, D.J] i))) r - 2
    have := le_max_right (sSup (Set.range fun i : Fin 4 ↦
      intervalLength (![D.A₀, D.A₁, D.A₂, D.J] i))) r
    linarith
  have hsup : sSup (Set.range v₃) ≤ 2 * S - 4 := by
    apply csSup_le
    · exact ⟨v₃ 0, ⟨0, rfl⟩⟩
    rintro x ⟨i, rfl⟩
    fin_cases i
    · simpa [v₃] using hAF
    · have : intervalLength D.A₂ ≤ 2 * S - 4 := by linarith
      simpa [v₃] using this
    · have : intervalLength D.J ≤ 2 * S - 4 := by linarith
      simpa [v₃] using this
  change 2 + max (sSup (Set.range v₃)) r ≤ 2 * S
  have hmax : max (sSup (Set.range v₃)) r ≤ 2 * S - 2 := by
    apply max_le
    · linarith
    · linarith
  linarith

/-- The two-set size parameter needed by the later dual-difference step is
also at most twice the global four-set size parameter. -/
lemma aux_u2_firstDual_two_size_le_two_four_size (D : AdmissibleSupportData) :
    sizeParameter ![aux_firstDualInterval D, D.J] D.χ ≤
      2 * sizeParameter ![D.A₀, D.A₁, D.A₂, D.J] D.χ := by
  let S : ℝ := sizeParameter ![D.A₀, D.A₁, D.A₂, D.J] D.χ
  let v₂ : Fin 2 → ℝ := fun k ↦ intervalLength (![aux_firstDualInterval D, D.J] k)
  let r : ℝ := max (supportRadius D.χ ^ 2)
    (max (eLpNorm D.χ 1 volume).toReal
      (max (eLpNorm D.χ 2 volume).toReal
        (max (eLpNorm (deriv D.χ) 1 volume).toReal
          (eLpNorm (deriv D.χ) 2 volume).toReal)))
  have hS : 2 ≤ S := by
    simpa [S] using aux_two_le_sizeParameter_four D.A₀ D.A₁ D.A₂ D.J D.χ
  have hA₁ : intervalLength D.A₁ ≤ S - 2 := by
    simpa [S] using aux_u2_intervalLength_le_sizeParameter_four_sub_two
      D.A₀ D.A₁ D.A₂ D.J D.χ 1
  have hJ : intervalLength D.J ≤ S - 2 := by
    simpa [S] using aux_u2_intervalLength_le_sizeParameter_four_sub_two
      D.A₀ D.A₁ D.A₂ D.J D.χ 3
  have hAF : intervalLength (aux_firstDualInterval D) ≤ 2 * S - 4 := by
    rcases D.hA₁ with ⟨a, b, hab, hA₁eq⟩
    rcases D.hJ with ⟨c, d, hcd, hJeq⟩
    calc
      intervalLength (aux_firstDualInterval D) =
          intervalLength D.A₁ + intervalLength D.J := by
        rw [aux_firstDualInterval, hA₁eq, hJeq]
        exact intervalSub a b c d hab.le hcd.le
      _ ≤ (S - 2) + (S - 2) := add_le_add hA₁ hJ
      _ = 2 * S - 4 := by ring
  have hr : r ≤ S - 2 := by
    change r ≤ 2 + max (sSup (Set.range fun i : Fin 4 ↦
      intervalLength (![D.A₀, D.A₁, D.A₂, D.J] i))) r - 2
    have := le_max_right (sSup (Set.range fun i : Fin 4 ↦
      intervalLength (![D.A₀, D.A₁, D.A₂, D.J] i))) r
    linarith
  have hsup : sSup (Set.range v₂) ≤ 2 * S - 4 := by
    apply csSup_le
    · exact ⟨v₂ 0, ⟨0, rfl⟩⟩
    rintro x ⟨i, rfl⟩
    fin_cases i
    · simpa [v₂] using hAF
    · have : intervalLength D.J ≤ 2 * S - 4 := by linarith
      simpa [v₂] using this
  change 2 + max (sSup (Set.range v₂)) r ≤ 2 * S
  have hmax : max (sSup (Set.range v₂)) r ≤ 2 * S - 2 := by
    apply max_le
    · linarith
    · linarith
  linarith

/-- Exact ENNReal algebra for the normalization `F ↦ S⁻¹F` in the first
dual/U³ step. -/
lemma aux_u2_firstDual_u3_normalization_rpow
    (S C U : ℝ≥0∞) (hSzero : S ≠ 0) (hStop : S ≠ ∞) :
    (S * (C * (S⁻¹ * U) ^ (1 / (5 : ℝ)))) ^ (1 / (2 : ℝ)) =
      S ^ (2 / (5 : ℝ)) * C ^ (1 / (2 : ℝ)) * U ^ (1 / (10 : ℝ)) := by
  calc
    (S * (C * (S⁻¹ * U) ^ (1 / (5 : ℝ)))) ^ (1 / (2 : ℝ)) =
        (S * C * (S⁻¹ * U) ^ (1 / (5 : ℝ))) ^ (1 / (2 : ℝ)) := by
      congr 1
      ring
    _ = S ^ (1 / (2 : ℝ)) * C ^ (1 / (2 : ℝ)) *
        ((S⁻¹ * U) ^ (1 / (5 : ℝ))) ^ (1 / (2 : ℝ)) := by
      rw [show S * C * (S⁻¹ * U) ^ (1 / (5 : ℝ)) =
          (S * C) * (S⁻¹ * U) ^ (1 / (5 : ℝ)) by ring,
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    _ = S ^ (1 / (2 : ℝ)) * C ^ (1 / (2 : ℝ)) *
        ((S⁻¹) ^ (1 / (5 : ℝ)) * U ^ (1 / (5 : ℝ))) ^ (1 / (2 : ℝ)) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    _ = S ^ (1 / (2 : ℝ)) * C ^ (1 / (2 : ℝ)) *
        (S⁻¹) ^ (1 / (10 : ℝ)) * U ^ (1 / (10 : ℝ)) := by
      have hSinv : ((S⁻¹) ^ (1 / (5 : ℝ))) ^ (1 / (2 : ℝ)) =
          (S⁻¹) ^ (1 / (10 : ℝ)) := by
        rw [← ENNReal.rpow_mul]
        congr 1
        ring
      have hU : (U ^ (1 / (5 : ℝ))) ^ (1 / (2 : ℝ)) =
          U ^ (1 / (10 : ℝ)) := by
        rw [← ENNReal.rpow_mul]
        congr 1
        ring
      rw [show ((S⁻¹) ^ (1 / (5 : ℝ)) * U ^ (1 / (5 : ℝ))) ^
          (1 / (2 : ℝ)) =
          ((S⁻¹) ^ (1 / (5 : ℝ))) ^ (1 / (2 : ℝ)) *
            (U ^ (1 / (5 : ℝ))) ^ (1 / (2 : ℝ)) by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)],
        hSinv, hU]
      ring
    _ = S ^ (1 / (2 : ℝ)) * C ^ (1 / (2 : ℝ)) *
        S ^ (-(1 / (10 : ℝ))) * U ^ (1 / (10 : ℝ)) := by
      rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg]
    _ = S ^ (2 / (5 : ℝ)) * C ^ (1 / (2 : ℝ)) * U ^ (1 / (10 : ℝ)) := by
      have hS : S ^ (1 / (2 : ℝ)) * S ^ (-(1 / (10 : ℝ))) =
          S ^ (2 / (5 : ℝ)) := by
        rw [← ENNReal.rpow_add _ _ hSzero hStop]
        congr 1
        ring
      rw [show S ^ (1 / (2 : ℝ)) * C ^ (1 / (2 : ℝ)) *
          S ^ (-(1 / (10 : ℝ))) * U ^ (1 / (10 : ℝ)) =
          (S ^ (1 / (2 : ℝ)) * S ^ (-(1 / (10 : ℝ)))) *
            C ^ (1 / (2 : ℝ)) * U ^ (1 / (10 : ℝ)) by ring, hS]

/-- The first-dual/Cauchy--Schwarz step followed by `u3Control`, with the
first-dual function normalized by the global four-set size parameter.  This
keeps the normalized `u³` factor explicit for later constant bookkeeping. -/
lemma aux_u2_firstDual_u3_scaled_chain
    (D : AdmissibleSupportData) (f₀ f₁ f₂ : ℝ → ℂ)
    (hf₀meas : AEStronglyMeasurable f₀ volume)
    (hf₁meas : AEStronglyMeasurable f₁ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₀bound : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₁bound : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₀support : ∀ᵐ x ∂volume, x ∉ D.A₀ → f₀ x = 0)
    (hf₁support : ∀ᵐ x ∂volume, x ∉ D.A₁ → f₁ x = 0)
    (hf₂support : ∀ᵐ x ∂volume, x ∉ D.A₂ → f₂ x = 0) :
    let F := aux_firstDualFunction D.χ f₁ f₂
    let S := sizeParameter ![D.A₀, D.A₁, D.A₂, D.J] D.χ
    let G : ℝ → ℂ := ((S : ℂ)⁻¹) • F
    ENNReal.ofReal (trilinearFormAbs D.χ f₀ f₁ f₂) ≤
      ENNReal.ofReal (intervalLength D.A₀) ^ (1 / (2 : ℝ)) *
        (ENNReal.ofReal S *
          (ENNReal.ofReal (C_u3Control (aux_firstDualInterval D) D.A₂ D.J D.χ) *
            uNorm 3 G ^ (1 / (5 : ℝ)))) ^ (1 / (2 : ℝ)) := by
  dsimp only
  let F : ℝ → ℂ := aux_firstDualFunction D.χ f₁ f₂
  let S : ℝ := sizeParameter ![D.A₀, D.A₁, D.A₂, D.J] D.χ
  let G : ℝ → ℂ := ((S : ℂ)⁻¹) • F
  have hS : 2 ≤ S := by
    simpa [S] using aux_two_le_sizeParameter_four D.A₀ D.A₁ D.A₂ D.J D.χ
  have hS0 : 0 ≤ S := by linarith
  have hSpos : 0 < S := by linarith
  have hFdata := aux_firstDualFunction_memLp_and_support D f₁ f₂
    hf₁meas hf₂meas hf₁bound hf₂bound hf₁support
  have hFmeas : AEStronglyMeasurable F volume := by
    simpa [F] using hFdata.2.aestronglyMeasurable
  have hFsupport : ∀ᵐ x ∂volume, x ∉ aux_firstDualInterval D → F x = 0 := by
    simpa [F] using hFdata.1
  have hFboundJ := aux_firstDualFunction_ae_bound D f₁ f₂
    hf₁meas hf₂meas hf₁bound hf₂bound hf₁support
  have hJle : volume.real D.J ≤ S := by
    change intervalLength D.J ≤ S
    simpa [S] using aux_intervalLength_le_sizeParameter_four
      D.A₀ D.A₁ D.A₂ D.J D.χ 3
  have hFbound : ∀ᵐ x ∂volume, ‖F x‖ ≤ S := by
    filter_upwards [hFboundJ] with x hx
    exact hx.trans hJle
  have hGmeas : AEStronglyMeasurable G volume := by
    exact hFmeas.const_smul _
  have hGbound : ∀ᵐ x ∂volume, ‖G x‖ ≤ 1 := by
    filter_upwards [hFbound] with x hx
    change ‖((S : ℂ)⁻¹) • F x‖ ≤ 1
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hS0]
    exact (inv_mul_le_iff₀ hSpos).mpr (by simpa using hx)
  have hGsupport : ∀ᵐ x ∂volume, x ∉ aux_firstDualInterval D → G x = 0 := by
    filter_upwards [hFsupport] with x hx hnot
    simp [G, hx hnot]
  have hAF : ∃ a b : ℝ, a < b ∧ aux_firstDualInterval D = Set.Icc a b :=
    aux_firstDualInterval_interval D
  have hu3 := u3Control (aux_firstDualInterval D) D.A₂ D.J D.χ
    hAF D.hA₂ D.hJ D.hχ_smooth D.hχ_compact D.hχ_nonneg D.hχ_le_one D.hχ_support
    G f₁ f₂ (by
      intro i
      fin_cases i
      · simpa using hGmeas
      · simpa using hf₁meas
      · simpa using hf₂meas)
    (by
      intro i
      fin_cases i
      · simpa using hGbound
      · simpa using hf₁bound
      · simpa using hf₂bound)
    hGsupport hf₂support
  have hFG : (S : ℂ) • G = F := by
    ext x
    simp only [G, smul_smul, Pi.smul_apply]
    rw [mul_inv_cancel₀]
    · simp
    · exact_mod_cast hSpos.ne'
  have hTscale : trilinearFormAbs D.χ F f₁ f₂ =
      S * trilinearFormAbs D.χ G f₁ f₂ := by
    rw [← hFG, aux_u2_trilinearFormAbs_smul_first]
    rw [Complex.norm_real, Real.norm_of_nonneg hS0]
  have hTF : ENNReal.ofReal (trilinearFormAbs D.χ F f₁ f₂) ≤
      ENNReal.ofReal S *
        (ENNReal.ofReal (C_u3Control (aux_firstDualInterval D) D.A₂ D.J D.χ) *
          uNorm 3 G ^ (1 / (5 : ℝ))) := by
    rw [hTscale, ENNReal.ofReal_mul hS0]
    gcongr
  have hfirst := (firstDualization D f₀ f₁ f₂ hf₀meas hf₁meas hf₂meas
    hf₀bound hf₁bound hf₂bound hf₀support hf₁support hf₂support).2
  have hfirstENN : ENNReal.ofReal (trilinearFormAbs D.χ f₀ f₁ f₂) ≤
      ENNReal.ofReal (intervalLength D.A₀) ^ (1 / (2 : ℝ)) *
        ENNReal.ofReal (trilinearFormAbs D.χ F f₁ f₂) ^ (1 / (2 : ℝ)) := by
    calc
      ENNReal.ofReal (trilinearFormAbs D.χ f₀ f₁ f₂) ≤
          ENNReal.ofReal (intervalLength D.A₀ ^ (1 / (2 : ℝ)) *
            trilinearFormAbs D.χ F f₁ f₂ ^ (1 / (2 : ℝ))) :=
        ENNReal.ofReal_le_ofReal (by simpa [F] using hfirst)
      _ = ENNReal.ofReal (intervalLength D.A₀) ^ (1 / (2 : ℝ)) *
          ENNReal.ofReal (trilinearFormAbs D.χ F f₁ f₂) ^ (1 / (2 : ℝ)) := by
        have hA₀nonneg : 0 ≤ intervalLength D.A₀ := ENNReal.toReal_nonneg
        have hTnonneg : 0 ≤ trilinearFormAbs D.χ F f₁ f₂ := norm_nonneg _
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hA₀nonneg _),
          ENNReal.ofReal_rpow_of_nonneg hA₀nonneg (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hTnonneg (by norm_num)]
  calc
    ENNReal.ofReal (trilinearFormAbs D.χ f₀ f₁ f₂) ≤
        ENNReal.ofReal (intervalLength D.A₀) ^ (1 / (2 : ℝ)) *
          ENNReal.ofReal (trilinearFormAbs D.χ F f₁ f₂) ^ (1 / (2 : ℝ)) := hfirstENN
    _ ≤ ENNReal.ofReal (intervalLength D.A₀) ^ (1 / (2 : ℝ)) *
        (ENNReal.ofReal S *
          (ENNReal.ofReal (C_u3Control (aux_firstDualInterval D) D.A₂ D.J D.χ) *
            uNorm 3 G ^ (1 / (5 : ℝ)))) ^ (1 / (2 : ℝ)) := by
      gcongr

/-- The first-dual/U³ portion of `u2Control`, with the normalized first-dual
function eliminated and all size constants reduced to the global four-set
size parameter. -/
lemma aux_u2_firstDual_u3_chain
    (D : AdmissibleSupportData) (f₀ f₁ f₂ : ℝ → ℂ)
    (hf₀meas : AEStronglyMeasurable f₀ volume)
    (hf₁meas : AEStronglyMeasurable f₁ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₀bound : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₁bound : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₀support : ∀ᵐ x ∂volume, x ∉ D.A₀ → f₀ x = 0)
    (hf₁support : ∀ᵐ x ∂volume, x ∉ D.A₁ → f₁ x = 0)
    (hf₂support : ∀ᵐ x ∂volume, x ∉ D.A₂ → f₂ x = 0) :
    let F := aux_firstDualFunction D.χ f₁ f₂
    let S := ENNReal.ofReal (sizeParameter ![D.A₀, D.A₁, D.A₂, D.J] D.χ)
    ENNReal.ofReal (trilinearFormAbs D.χ f₀ f₁ f₂) ≤
      S ^ (1 / (2 : ℝ)) * S ^ (2 / (5 : ℝ)) *
        ((128 : ℝ≥0∞) * S ^ (3 : ℝ)) ^ (1 / (2 : ℝ)) *
          uNorm 3 F ^ (1 / (10 : ℝ)) := by
  dsimp only
  let F : ℝ → ℂ := aux_firstDualFunction D.χ f₁ f₂
  let s : ℝ := sizeParameter ![D.A₀, D.A₁, D.A₂, D.J] D.χ
  let S : ℝ≥0∞ := ENNReal.ofReal s
  let G : ℝ → ℂ := ((s : ℂ)⁻¹) • F
  have hs : 2 ≤ s := by
    simpa [s] using aux_two_le_sizeParameter_four D.A₀ D.A₁ D.A₂ D.J D.χ
  have hs0 : 0 ≤ s := by linarith
  have hspos : 0 < s := by linarith
  have hSzero : S ≠ 0 := by
    exact ne_of_gt (by simpa [S] using (ENNReal.ofReal_pos.mpr hspos))
  have hStop : S ≠ ∞ := by
    exact ENNReal.ofReal_ne_top
  have hscaled : ENNReal.ofReal (trilinearFormAbs D.χ f₀ f₁ f₂) ≤
      ENNReal.ofReal (intervalLength D.A₀) ^ (1 / (2 : ℝ)) *
        (S *
          (ENNReal.ofReal (C_u3Control (aux_firstDualInterval D) D.A₂ D.J D.χ) *
            uNorm 3 G ^ (1 / (5 : ℝ)))) ^ (1 / (2 : ℝ)) := by
    simpa [F, s, S, G] using aux_u2_firstDual_u3_scaled_chain D f₀ f₁ f₂
      hf₀meas hf₁meas hf₂meas hf₀bound hf₁bound hf₂bound
      hf₀support hf₁support hf₂support
  have hUscale : uNorm 3 G = S⁻¹ * uNorm 3 F := by
    change uNorm 3 (((s : ℂ)⁻¹) • F) = S⁻¹ * uNorm 3 F
    rw [aux_u2_uNorm_three_smul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hs0, ENNReal.ofReal_inv_of_pos hspos]
  have hA₀ : ENNReal.ofReal (intervalLength D.A₀) ≤ S := by
    apply ENNReal.ofReal_le_ofReal
    simpa [s] using aux_intervalLength_le_sizeParameter_four
      D.A₀ D.A₁ D.A₂ D.J D.χ 0
  have hA₀root : ENNReal.ofReal (intervalLength D.A₀) ^ (1 / (2 : ℝ)) ≤
      S ^ (1 / (2 : ℝ)) :=
    ENNReal.rpow_le_rpow hA₀ (by norm_num)
  let T : ℝ := sizeParameter ![aux_firstDualInterval D, D.A₂, D.J] D.χ
  have hT : T ≤ 2 * s := by
    simpa [T, s] using aux_u2_firstDual_three_size_le_two_four_size D
  have hT0 : 0 ≤ T := by
    dsimp [T, sizeParameter]
    positivity
  have hC : C_u3Control (aux_firstDualInterval D) D.A₂ D.J D.χ ≤ 128 * s ^ (3 : ℕ) := by
    unfold C_u3Control
    calc
      (2 : ℝ) ^ 4 * T ^ 3 ≤ (2 : ℝ) ^ 4 * (2 * s) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT0 hT 3) (by positivity)
      _ = 128 * s ^ 3 := by ring
  have hCENN : ENNReal.ofReal (C_u3Control (aux_firstDualInterval D) D.A₂ D.J D.χ) ≤
      (128 : ℝ≥0∞) * S ^ (3 : ℝ) := by
    calc
      ENNReal.ofReal (C_u3Control (aux_firstDualInterval D) D.A₂ D.J D.χ) ≤
          ENNReal.ofReal (128 * s ^ (3 : ℕ)) := ENNReal.ofReal_le_ofReal hC
      _ = (128 : ℝ≥0∞) * S ^ (3 : ℝ) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hs0]
        norm_num [S, ENNReal.rpow_natCast]
  have hCroot : ENNReal.ofReal (C_u3Control (aux_firstDualInterval D) D.A₂ D.J D.χ) ^
      (1 / (2 : ℝ)) ≤ ((128 : ℝ≥0∞) * S ^ (3 : ℝ)) ^ (1 / (2 : ℝ)) :=
    ENNReal.rpow_le_rpow hCENN (by norm_num)
  have hnormalized :
      (S *
        (ENNReal.ofReal (C_u3Control (aux_firstDualInterval D) D.A₂ D.J D.χ) *
          uNorm 3 G ^ (1 / (5 : ℝ)))) ^ (1 / (2 : ℝ)) =
        S ^ (2 / (5 : ℝ)) *
          ENNReal.ofReal (C_u3Control (aux_firstDualInterval D) D.A₂ D.J D.χ) ^
            (1 / (2 : ℝ)) * uNorm 3 F ^ (1 / (10 : ℝ)) := by
    rw [hUscale]
    exact aux_u2_firstDual_u3_normalization_rpow S
      (ENNReal.ofReal (C_u3Control (aux_firstDualInterval D) D.A₂ D.J D.χ))
      (uNorm 3 F) hSzero hStop
  calc
    ENNReal.ofReal (trilinearFormAbs D.χ f₀ f₁ f₂) ≤
        ENNReal.ofReal (intervalLength D.A₀) ^ (1 / (2 : ℝ)) *
          (S *
            (ENNReal.ofReal (C_u3Control (aux_firstDualInterval D) D.A₂ D.J D.χ) *
              uNorm 3 G ^ (1 / (5 : ℝ)))) ^ (1 / (2 : ℝ)) := hscaled
    _ = ENNReal.ofReal (intervalLength D.A₀) ^ (1 / (2 : ℝ)) *
        (S ^ (2 / (5 : ℝ)) *
          ENNReal.ofReal (C_u3Control (aux_firstDualInterval D) D.A₂ D.J D.χ) ^
            (1 / (2 : ℝ)) * uNorm 3 F ^ (1 / (10 : ℝ))) := by rw [hnormalized]
    _ ≤ S ^ (1 / (2 : ℝ)) * S ^ (2 / (5 : ℝ)) *
        ((128 : ℝ≥0∞) * S ^ (3 : ℝ)) ^ (1 / (2 : ℝ)) *
          uNorm 3 F ^ (1 / (10 : ℝ)) := by
      have hprod :
          ENNReal.ofReal (intervalLength D.A₀) ^ (1 / (2 : ℝ)) *
            ENNReal.ofReal (C_u3Control (aux_firstDualInterval D) D.A₂ D.J D.χ) ^
              (1 / (2 : ℝ)) ≤
            S ^ (1 / (2 : ℝ)) * ((128 : ℝ≥0∞) * S ^ (3 : ℝ)) ^
              (1 / (2 : ℝ)) :=
        mul_le_mul hA₀root hCroot bot_le bot_le
      calc
        ENNReal.ofReal (intervalLength D.A₀) ^ (1 / (2 : ℝ)) *
            (S ^ (2 / (5 : ℝ)) *
              ENNReal.ofReal (C_u3Control (aux_firstDualInterval D) D.A₂ D.J D.χ) ^
                (1 / (2 : ℝ)) * uNorm 3 F ^ (1 / (10 : ℝ))) =
            (ENNReal.ofReal (intervalLength D.A₀) ^ (1 / (2 : ℝ)) *
              ENNReal.ofReal (C_u3Control (aux_firstDualInterval D) D.A₂ D.J D.χ) ^
                (1 / (2 : ℝ))) *
              (S ^ (2 / (5 : ℝ)) * uNorm 3 F ^ (1 / (10 : ℝ))) := by ring
        _ ≤ (S ^ (1 / (2 : ℝ)) * ((128 : ℝ≥0∞) * S ^ (3 : ℝ)) ^
              (1 / (2 : ℝ))) *
              (S ^ (2 / (5 : ℝ)) * uNorm 3 F ^ (1 / (10 : ℝ))) :=
          mul_le_mul_of_nonneg_right hprod bot_le
        _ = S ^ (1 / (2 : ℝ)) * S ^ (2 / (5 : ℝ)) *
            ((128 : ℝ≥0∞) * S ^ (3 : ℝ)) ^ (1 / (2 : ℝ)) *
              uNorm 3 F ^ (1 / (10 : ℝ)) := by ring

/-- The purely numerical post-bilinear endgame.  It converts the generic
quarter-root Cauchy--Schwarz bound into the displayed `128 * S^4` bound,
independently of the analytic source of that bound. -/
lemma aux_u2_post_bilinear_numerical
    (Q Cb Cs L S : ℝ) (U : ℝ≥0∞)
    (hS : 2 ≤ S)
    (hCb : Cb ≤ 32 * S ^ (2 : ℕ))
    (hCs : Cs ≤ 16 * S ^ (2 : ℕ))
    (hL : L ≤ S)
    (hQ : ENNReal.ofReal Q ≤ ENNReal.ofReal Cb *
      (ENNReal.ofReal Cs * U ^ (1 / (2 : ℝ))) ^ (1 / (2 : ℝ)) *
        ENNReal.ofReal L) :
    ENNReal.ofReal Q ≤ ENNReal.ofReal (128 * S ^ (4 : ℕ)) *
      U ^ (1 / (4 : ℝ)) := by
  have hS0 : 0 ≤ S := by linarith
  have hS1 : 1 ≤ S := by linarith
  have hCbENN : ENNReal.ofReal Cb ≤ ENNReal.ofReal (32 * S ^ (2 : ℕ)) :=
    ENNReal.ofReal_le_ofReal hCb
  have hCsENN : ENNReal.ofReal Cs ≤ ENNReal.ofReal (16 * S ^ (2 : ℕ)) :=
    ENNReal.ofReal_le_ofReal hCs
  have hLENN : ENNReal.ofReal L ≤ ENNReal.ofReal S :=
    ENNReal.ofReal_le_ofReal hL
  have hrootCs : (ENNReal.ofReal (16 * S ^ (2 : ℕ))) ^ (1 / (2 : ℝ)) =
      ENNReal.ofReal (4 * S) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ 16 * S ^ (2 : ℕ))
      (by norm_num : 0 ≤ 1 / (2 : ℝ))]
    congr 1
    rw [show 16 * S ^ (2 : ℕ) = (4 * S) ^ (2 : ℕ) by ring,
      ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 4 * S)]
    norm_num
  have hmiddle :
      (ENNReal.ofReal Cs * U ^ (1 / (2 : ℝ))) ^ (1 / (2 : ℝ)) ≤
        ENNReal.ofReal (4 * S) * U ^ (1 / (4 : ℝ)) := by
    calc
      (ENNReal.ofReal Cs * U ^ (1 / (2 : ℝ))) ^ (1 / (2 : ℝ)) ≤
          (ENNReal.ofReal (16 * S ^ (2 : ℕ)) * U ^ (1 / (2 : ℝ))) ^
            (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow (mul_le_mul_of_nonneg_right hCsENN (by positivity))
          (by norm_num)
      _ = (ENNReal.ofReal (16 * S ^ (2 : ℕ))) ^ (1 / (2 : ℝ)) *
          (U ^ (1 / (2 : ℝ))) ^ (1 / (2 : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      _ = ENNReal.ofReal (4 * S) * U ^ (1 / (4 : ℝ)) := by
        rw [hrootCs, ← ENNReal.rpow_mul]
        norm_num
  calc
    ENNReal.ofReal Q ≤ ENNReal.ofReal Cb *
        (ENNReal.ofReal Cs * U ^ (1 / (2 : ℝ))) ^ (1 / (2 : ℝ)) *
          ENNReal.ofReal L := hQ
    _ ≤ ENNReal.ofReal (32 * S ^ (2 : ℕ)) *
        (ENNReal.ofReal (4 * S) * U ^ (1 / (4 : ℝ))) *
          ENNReal.ofReal S := by
      gcongr
    _ = ENNReal.ofReal (128 * S ^ (4 : ℕ)) * U ^ (1 / (4 : ℝ)) := by
      have hcoeff : ENNReal.ofReal (32 * S ^ (2 : ℕ)) *
          ENNReal.ofReal (4 * S) * ENNReal.ofReal S =
          ENNReal.ofReal (128 * S ^ (4 : ℕ)) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 32 * S ^ (2 : ℕ)),
          ← ENNReal.ofReal_mul
            (by positivity : 0 ≤ (32 * S ^ (2 : ℕ)) * (4 * S))]
        congr 1
        ring
      calc
        ENNReal.ofReal (32 * S ^ (2 : ℕ)) *
            (ENNReal.ofReal (4 * S) * U ^ (1 / (4 : ℝ))) *
            ENNReal.ofReal S =
            (ENNReal.ofReal (32 * S ^ (2 : ℕ)) *
              ENNReal.ofReal (4 * S) * ENNReal.ofReal S) *
              U ^ (1 / (4 : ℝ)) := by ring
        _ = _ := by rw [hcoeff]

/-- Discarding interval entries can only decrease the size parameter.  This
special case compares the singleton cutoff parameter to the four-set one in
`u2Control`. -/
lemma aux_u2_sizeParameter_singleton_le_four
    (A₀ A₁ A₂ J : Set ℝ) (χ : ℝ → ℝ) :
    sizeParameter ![J] χ ≤ sizeParameter ![A₀, A₁, A₂, J] χ := by
  have hbd : BddAbove (Set.range fun i : Fin 4 ↦
      intervalLength (![A₀, A₁, A₂, J] i)) :=
    Set.finite_range _ |>.bddAbove
  have hmem : intervalLength J ∈ Set.range fun i : Fin 4 ↦
      intervalLength (![A₀, A₁, A₂, J] i) := ⟨3, by simp⟩
  have hJle : intervalLength J ≤ sSup (Set.range fun i : Fin 4 ↦
      intervalLength (![A₀, A₁, A₂, J] i)) := le_csSup hbd hmem
  have hsingle : sSup (Set.range fun i : Fin 1 ↦ intervalLength (![J] i)) =
      intervalLength J := by
    have hrange : Set.range (fun i : Fin 1 ↦ intervalLength (![J] i)) =
        {intervalLength J} := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i
        simp
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        exact ⟨0, by simp [hx]⟩
    rw [hrange, csSup_singleton]
  unfold sizeParameter
  rw [hsingle]
  exact add_le_add (le_refl 2) (max_le_max hJle le_rfl)

/-- Specialization of `aux_u2_post_bilinear_numerical` to the constants and
four-set size parameter in `u2Control`. -/
lemma aux_u2_post_bilinear_size_upgrade
    (D : AdmissibleSupportData) (Q : ℝ) (U : ℝ≥0∞)
    (hQ : ENNReal.ofReal Q ≤
      ENNReal.ofReal (C_bilinearSobolevEstimates D.J D.χ) *
        (ENNReal.ofReal (C_sobolevDifferenceEstimate 1 D.A₁) *
          U ^ (1 / (2 : ℝ))) ^ (1 / (2 : ℝ)) *
        ENNReal.ofReal (intervalLength D.A₂)) :
    ENNReal.ofReal Q ≤
      ENNReal.ofReal (128 * sizeParameter ![D.A₀, D.A₁, D.A₂, D.J] D.χ ^ (4 : ℕ)) *
        U ^ (1 / (4 : ℝ)) := by
  let S : ℝ := sizeParameter ![D.A₀, D.A₁, D.A₂, D.J] D.χ
  have hS : 2 ≤ S := by
    exact aux_two_le_sizeParameter_four D.A₀ D.A₁ D.A₂ D.J D.χ
  have hS1 : 1 ≤ S := by linarith
  have hsizeJ : sizeParameter ![D.J] D.χ ≤ S := by
    exact aux_u2_sizeParameter_singleton_le_four D.A₀ D.A₁ D.A₂ D.J D.χ
  have hsizeJ0 : 0 ≤ sizeParameter ![D.J] D.χ := by
    unfold sizeParameter
    positivity
  have hCb : C_bilinearSobolevEstimates D.J D.χ ≤ 32 * S ^ (2 : ℕ) := by
    unfold C_bilinearSobolevEstimates
    norm_num
    gcongr
  have hlen₁ : intervalLength D.A₁ ≤ S := by
    simpa [S] using aux_intervalLength_le_sizeParameter_four D.A₀ D.A₁ D.A₂ D.J D.χ 1
  have hlen₂ : intervalLength D.A₂ ≤ S := by
    simpa [S] using aux_intervalLength_le_sizeParameter_four D.A₀ D.A₁ D.A₂ D.J D.χ 2
  have hCs : C_sobolevDifferenceEstimate 1 D.A₁ ≤ 16 * S ^ (2 : ℕ) := by
    rw [C_sobolevDifferenceEstimate]
    norm_num
    have hlen₁0 : 0 ≤ intervalLength D.A₁ := ENNReal.toReal_nonneg
    have hlin : 1 + intervalLength D.A₁ ≤ 2 * S := by linarith
    calc
      4 * (1 + intervalLength D.A₁) ^ (2 : ℕ) ≤ 4 * (2 * S) ^ (2 : ℕ) := by
        gcongr
      _ = 16 * S ^ (2 : ℕ) := by ring
  have hfinal := aux_u2_post_bilinear_numerical Q
    (C_bilinearSobolevEstimates D.J D.χ)
    (C_sobolevDifferenceEstimate 1 D.A₁) (intervalLength D.A₂) S U
    hS hCb hCs hlen₂ hQ
  simpa [S] using hfinal


/-- Numerical endgame for `u2Control` after the intended analytic chain has
been reduced to the displayed first-dual / `u³` / interchange / bilinear
estimate.  Here `S` is the global size parameter and `U` is `uNorm 2 f₁`.

The hypothesis has the following factors, in order: the `A₀` support root,
the cutoff normalization, the square root of `u3Control`, the one-tenth
power of `dualDifferenceInterchange`, and the one-quarter-power bilinear
and difference estimate. -/
lemma aux_u2_numerical_endgame
    (I S U : ℝ≥0∞) (hS : 2 ≤ S)
    (hchain : I ≤
      S ^ (1 / (2 : ℝ)) * S ^ (2 / (5 : ℝ)) *
        (((128 : ℝ≥0∞) * S ^ (3 : ℝ)) ^ (1 / (2 : ℝ))) *
          (((8 : ℝ≥0∞) * S ^ (2 : ℝ) *
            (((128 : ℝ≥0∞) * S ^ (4 : ℝ) * U ^ (1 / (4 : ℝ))) ^
              (1 / (4 : ℝ)))) ^ (1 / (10 : ℝ)))) :
    I ≤ (64 : ℝ≥0∞) * S ^ (3 : ℝ) * U ^ (1 / (160 : ℝ)) := by
  by_cases hUzero : U = 0
  · subst U
    simpa using hchain
  by_cases hStop : S = ∞
  · subst S
    simp [hUzero]
  have hSone : 1 ≤ S := by
    exact le_trans (by norm_num) hS
  have hSzero : S ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hS)
  have hSfin : S ≠ ∞ := hStop
  have hC3 : ((128 : ℝ≥0∞) * S ^ (3 : ℝ)) ^ (1 / (2 : ℝ)) =
      (128 : ℝ≥0∞) ^ (1 / (2 : ℝ)) * S ^ (3 / (2 : ℝ)) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
    congr 1
    ring_nf
  have hQroot : ((128 : ℝ≥0∞) * S ^ (4 : ℝ) * U ^ (1 / (4 : ℝ))) ^
      (1 / (4 : ℝ)) =
      (128 : ℝ≥0∞) ^ (1 / (4 : ℝ)) * S * U ^ (1 / (16 : ℝ)) := by
    rw [show (128 : ℝ≥0∞) * S ^ (4 : ℝ) * U ^ (1 / (4 : ℝ)) =
        ((128 : ℝ≥0∞) * S ^ (4 : ℝ)) * U ^ (1 / (4 : ℝ)) by ring,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    rw [show (4 : ℝ) * (1 / 4 : ℝ) = 1 by norm_num,
      show (1 / 4 : ℝ) * (1 / 4 : ℝ) = 1 / 16 by ring,
      ENNReal.rpow_one]
  have hDual : ((8 : ℝ≥0∞) * S ^ (2 : ℝ) *
      (((128 : ℝ≥0∞) * S ^ (4 : ℝ) * U ^ (1 / (4 : ℝ))) ^
        (1 / (4 : ℝ)))) ^ (1 / (10 : ℝ)) =
      (8 : ℝ≥0∞) ^ (1 / (10 : ℝ)) *
        (128 : ℝ≥0∞) ^ (1 / (40 : ℝ)) * S ^ (3 / (10 : ℝ)) *
          U ^ (1 / (160 : ℝ)) := by
    rw [hQroot]
    calc
      ((8 : ℝ≥0∞) * S ^ (2 : ℝ) *
          ((128 : ℝ≥0∞) ^ (1 / (4 : ℝ)) * S * U ^ (1 / (16 : ℝ)))) ^
          (1 / (10 : ℝ)) =
          (((8 : ℝ≥0∞) * (128 : ℝ≥0∞) ^ (1 / (4 : ℝ))) *
            (S ^ (2 : ℝ) * S) * U ^ (1 / (16 : ℝ))) ^ (1 / (10 : ℝ)) := by
        congr 1
        ring
      _ = ((8 : ℝ≥0∞) * (128 : ℝ≥0∞) ^ (1 / (4 : ℝ))) ^ (1 / (10 : ℝ)) *
          (S ^ (2 : ℝ) * S) ^ (1 / (10 : ℝ)) *
            (U ^ (1 / (16 : ℝ))) ^ (1 / (10 : ℝ)) := by
        rw [show ((8 : ℝ≥0∞) * (128 : ℝ≥0∞) ^ (1 / (4 : ℝ))) *
            (S ^ (2 : ℝ) * S) * U ^ (1 / (16 : ℝ)) =
            (((8 : ℝ≥0∞) * (128 : ℝ≥0∞) ^ (1 / (4 : ℝ))) *
              (S ^ (2 : ℝ) * S)) * U ^ (1 / (16 : ℝ)) by ring,
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      _ = (8 : ℝ≥0∞) ^ (1 / (10 : ℝ)) *
          (128 : ℝ≥0∞) ^ (1 / (40 : ℝ)) * S ^ (3 / (10 : ℝ)) *
            U ^ (1 / (160 : ℝ)) := by
        have h128 : ((128 : ℝ≥0∞) ^ (1 / (4 : ℝ))) ^ (1 / (10 : ℝ)) =
            (128 : ℝ≥0∞) ^ (1 / (40 : ℝ)) := by
          rw [← ENNReal.rpow_mul]
          congr 1
          ring
        have hS : (S ^ (2 : ℝ) * S) ^ (1 / (10 : ℝ)) =
            S ^ (3 / (10 : ℝ)) := by
          calc
            (S ^ (2 : ℝ) * S) ^ (1 / (10 : ℝ)) =
                (S ^ ((2 : ℝ) + 1)) ^ (1 / (10 : ℝ)) := by
              congr 1
              rw [ENNReal.rpow_add _ _ hSzero hSfin, ENNReal.rpow_one]
            _ = S ^ (3 / (10 : ℝ)) := by
              rw [← ENNReal.rpow_mul]
              congr 1
              ring
        have hU : (U ^ (1 / (16 : ℝ))) ^ (1 / (10 : ℝ)) =
            U ^ (1 / (160 : ℝ)) := by
          rw [← ENNReal.rpow_mul]
          congr 1
          ring
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), h128, hS, hU]
  apply hchain.trans
  rw [hC3, hDual]
  have h128half : (128 : ℝ≥0∞) ^ (1 / (2 : ℝ)) ≤ 16 := by
    calc
      (128 : ℝ≥0∞) ^ (1 / (2 : ℝ)) ≤
          ((2 : ℝ≥0∞) ^ (7 : ℕ)) ^ (1 / (2 : ℝ)) := by
        apply ENNReal.rpow_le_rpow
        · norm_num
        · norm_num
      _ = (2 : ℝ≥0∞) ^ (7 / (2 : ℝ)) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        congr 1
        ring
      _ ≤ (2 : ℝ≥0∞) ^ (4 : ℝ) := by
        apply ENNReal.rpow_le_rpow_of_exponent_le
        · norm_num
        · norm_num
      _ = 16 := by
        norm_num [← ENNReal.rpow_natCast]
  have h8 : (8 : ℝ≥0∞) ^ (1 / (10 : ℝ)) ≤ 2 := by
    calc
      (8 : ℝ≥0∞) ^ (1 / (10 : ℝ)) ≤
          ((2 : ℝ≥0∞) ^ (3 : ℕ)) ^ (1 / (10 : ℝ)) := by
        apply ENNReal.rpow_le_rpow
        · norm_num
        · norm_num
      _ = (2 : ℝ≥0∞) ^ (3 / (10 : ℝ)) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        congr 1
        ring
      _ ≤ (2 : ℝ≥0∞) ^ (1 : ℝ) := by
        apply ENNReal.rpow_le_rpow_of_exponent_le
        · norm_num
        · norm_num
      _ = 2 := by norm_num
  have h128small : (128 : ℝ≥0∞) ^ (1 / (40 : ℝ)) ≤ 2 := by
    calc
      (128 : ℝ≥0∞) ^ (1 / (40 : ℝ)) ≤
          ((2 : ℝ≥0∞) ^ (7 : ℕ)) ^ (1 / (40 : ℝ)) := by
        apply ENNReal.rpow_le_rpow
        · norm_num
        · norm_num
      _ = (2 : ℝ≥0∞) ^ (7 / (40 : ℝ)) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        congr 1
        ring
      _ ≤ (2 : ℝ≥0∞) ^ (1 : ℝ) := by
        apply ENNReal.rpow_le_rpow_of_exponent_le
        · norm_num
        · norm_num
      _ = 2 := by norm_num
  have hcoeff : (128 : ℝ≥0∞) ^ (1 / (2 : ℝ)) *
      (8 : ℝ≥0∞) ^ (1 / (10 : ℝ)) *
        (128 : ℝ≥0∞) ^ (1 / (40 : ℝ)) ≤ 64 := by
    calc
      (128 : ℝ≥0∞) ^ (1 / (2 : ℝ)) *
          (8 : ℝ≥0∞) ^ (1 / (10 : ℝ)) *
            (128 : ℝ≥0∞) ^ (1 / (40 : ℝ)) ≤ 16 * 2 * 2 := by
          gcongr
      _ = 64 := by norm_num
  have hSpow : S ^ (1 / (2 : ℝ)) * S ^ (2 / (5 : ℝ)) *
      S ^ (3 / (2 : ℝ)) * S ^ (3 / (10 : ℝ)) =
        S ^ (27 / (10 : ℝ)) := by
    rw [← ENNReal.rpow_add _ _ hSzero hSfin,
      ← ENNReal.rpow_add _ _ hSzero hSfin,
      ← ENNReal.rpow_add _ _ hSzero hSfin]
    congr 1
    ring
  have hSpow_le : S ^ (1 / (2 : ℝ)) * S ^ (2 / (5 : ℝ)) *
      S ^ (3 / (2 : ℝ)) * S ^ (3 / (10 : ℝ)) ≤ S ^ (3 : ℝ) := by
    rw [hSpow]
    exact ENNReal.rpow_le_rpow_of_exponent_le hSone (by norm_num)
  calc
    S ^ (1 / (2 : ℝ)) * S ^ (2 / (5 : ℝ)) *
        ((128 : ℝ≥0∞) ^ (1 / (2 : ℝ)) * S ^ (3 / (2 : ℝ))) *
          ((8 : ℝ≥0∞) ^ (1 / (10 : ℝ)) *
            (128 : ℝ≥0∞) ^ (1 / (40 : ℝ)) * S ^ (3 / (10 : ℝ)) *
              U ^ (1 / (160 : ℝ))) =
        ((128 : ℝ≥0∞) ^ (1 / (2 : ℝ)) *
          (8 : ℝ≥0∞) ^ (1 / (10 : ℝ)) *
            (128 : ℝ≥0∞) ^ (1 / (40 : ℝ))) *
          (S ^ (1 / (2 : ℝ)) * S ^ (2 / (5 : ℝ)) *
            S ^ (3 / (2 : ℝ)) * S ^ (3 / (10 : ℝ))) *
              U ^ (1 / (160 : ℝ)) := by ring
    _ ≤ 64 * S ^ (3 : ℝ) * U ^ (1 / (160 : ℝ)) := by
      gcongr



/-- Combines the real-valued u3 and post-bilinear bounds after passing them
through ENNReal.ofReal and taking the required roots. -/
lemma aux_u2_u3_ennreal_glue
    (U₃ U S : ℝ≥0∞) (C Q : ℝ)
    (hC0 : 0 ≤ C) (hQ0 : 0 ≤ Q)
    (hU₃ : U₃ ≤ ENNReal.ofReal (C * Q ^ (1 / (4 : ℝ))))
    (hC : ENNReal.ofReal C ≤ (8 : ℝ≥0∞) * S ^ (2 : ℝ))
    (hQ : ENNReal.ofReal Q ≤
      (128 : ℝ≥0∞) * S ^ (4 : ℝ) * U ^ (1 / (4 : ℝ))) :
    U₃ ^ (1 / (10 : ℝ)) ≤
      ((8 : ℝ≥0∞) * S ^ (2 : ℝ) *
        ((128 : ℝ≥0∞) * S ^ (4 : ℝ) * U ^ (1 / (4 : ℝ))) ^
          (1 / (4 : ℝ))) ^ (1 / (10 : ℝ)) := by
  have hQroot : (ENNReal.ofReal Q) ^ (1 / (4 : ℝ)) ≤
      ((128 : ℝ≥0∞) * S ^ (4 : ℝ) * U ^ (1 / (4 : ℝ))) ^
        (1 / (4 : ℝ)) :=
    ENNReal.rpow_le_rpow hQ (by positivity)
  have hprod : ENNReal.ofReal C * (ENNReal.ofReal Q) ^ (1 / (4 : ℝ)) ≤
      ((8 : ℝ≥0∞) * S ^ (2 : ℝ)) *
        ((128 : ℝ≥0∞) * S ^ (4 : ℝ) * U ^ (1 / (4 : ℝ))) ^
          (1 / (4 : ℝ)) := by
    gcongr
  have hbase : ENNReal.ofReal (C * Q ^ (1 / (4 : ℝ))) ≤
      (8 : ℝ≥0∞) * S ^ (2 : ℝ) *
        ((128 : ℝ≥0∞) * S ^ (4 : ℝ) * U ^ (1 / (4 : ℝ))) ^
          (1 / (4 : ℝ)) := by
    calc
      ENNReal.ofReal (C * Q ^ (1 / (4 : ℝ))) =
          ENNReal.ofReal C * ENNReal.ofReal (Q ^ (1 / (4 : ℝ))) :=
        ENNReal.ofReal_mul hC0
      _ = ENNReal.ofReal C * (ENNReal.ofReal Q) ^ (1 / (4 : ℝ)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hQ0 (by positivity)]
      _ ≤ _ := by
        simpa only [mul_assoc] using hprod
  exact ENNReal.rpow_le_rpow (hU₃.trans hbase) (by positivity)

/-- The constant in \(\label{thm:u2-control}\), used by u2Control:
\[
C_{\ref{thm:u2-control},\,A_0,A_1,A_2,J,\chi}
:=
2^6\Ssize{A_0,A_1,A_2,J}{\chi}^{3}.
\]
-/
def C_u2Control (A₀ A₁ A₂ J : Set ℝ) (χ : ℝ → ℝ) : ℝ :=
  (2 : ℝ) ^ 6 * sizeParameter ![A₀, A₁, A₂, J] χ ^ 3

/--
Let \(\mathfrak D=(A_0,A_1,A_2,J,\chi)\) be admissible. Define
\[
C_{\ref{thm:u2-control},\,A_0,A_1,A_2,J,\chi}
:=
2^6\Ssize{A_0,A_1,A_2,J}{\chi}^{3}.
\]
If \(f_0,f_1,f_2\) are \(1\)-bounded and supported in
\(A_0,A_1,A_2\), respectively, then
\[
\Ichi(f_0,f_1,f_2)
\leq
C_{\ref{thm:u2-control},\,A_0,A_1,A_2,J,\chi}
\uNorm{f_1}2^{1/160}.
\]
-/
theorem u2Control
    (D : AdmissibleSupportData) (f₀ f₁ f₂ : ℝ → ℂ)
    (hf₀_measurable : AEStronglyMeasurable f₀ volume)
    (hf₁_measurable : AEStronglyMeasurable f₁ volume)
    (hf₂_measurable : AEStronglyMeasurable f₂ volume)
    (hf₀_one_bounded : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₁_one_bounded : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₂_one_bounded : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₀_support : ∀ᵐ x ∂volume, x ∉ D.A₀ → f₀ x = 0)
    (hf₁_support : ∀ᵐ x ∂volume, x ∉ D.A₁ → f₁ x = 0)
    (hf₂_support : ∀ᵐ x ∂volume, x ∉ D.A₂ → f₂ x = 0) :
    ENNReal.ofReal (trilinearFormAbs D.χ f₀ f₁ f₂) ≤
      ENNReal.ofReal (C_u2Control D.A₀ D.A₁ D.A₂ D.J D.χ) *
        uNorm 2 f₁ ^ (1 / (160 : ℝ)) := by
  let s : ℝ := sizeParameter ![D.A₀, D.A₁, D.A₂, D.J] D.χ
  let S : ℝ≥0∞ := ENNReal.ofReal s
  let F : ℝ → ℂ := aux_firstDualFunction D.χ f₁ f₂
  let U : ℝ≥0∞ := uNorm 2 f₁
  have hs : 2 ≤ s := by
    simpa [s] using aux_two_le_sizeParameter_four D.A₀ D.A₁ D.A₂ D.J D.χ
  have hs0 : 0 ≤ s := by linarith
  have hspos : 0 < s := by linarith
  have hS : (2 : ℝ≥0∞) ≤ S := by
    simpa [S] using ENNReal.ofReal_le_ofReal hs
  have hfirst := aux_u2_firstDual_u3_chain D f₀ f₁ f₂
    hf₀_measurable hf₁_measurable hf₂_measurable
    hf₀_one_bounded hf₁_one_bounded hf₂_one_bounded
    hf₀_support hf₁_support hf₂_support
  obtain ⟨Φ, _, hDDI⟩ :=
    aux_u2_dualDifferenceInterchange_firstDual_trilinear D f₁ f₂
      hf₁_measurable hf₂_measurable hf₁_one_bounded hf₂_one_bounded hf₁_support
  let Q : ℝ := ∫ h : ℝ,
    trilinearFormAbs D.χ (frequencyCharacter (-Φ h))
      (multiplicativeDifference h (AEStronglyMeasurable.mk f₁ hf₁_measurable))
      (multiplicativeDifference h (AEStronglyMeasurable.mk f₂ hf₂_measurable))
  let C : ℝ := C_dualDifferenceInterchange (aux_firstDualInterval D) D.J D.χ
  have hQraw := aux_u2_direct_trilinear_Q_bound_mk D f₁ f₂
    hf₁_measurable hf₂_measurable hf₁_one_bounded hf₂_one_bounded
    hf₁_support hf₂_support Φ
  have hQsizeRaw := aux_u2_post_bilinear_size_upgrade D Q U (by
    simpa [Q, U] using hQraw)
  have hQENN : ENNReal.ofReal Q ≤
      (128 : ℝ≥0∞) * S ^ (4 : ℝ) * U ^ (1 / (4 : ℝ)) := by
    calc
      ENNReal.ofReal Q ≤ ENNReal.ofReal (128 * s ^ (4 : ℕ)) * U ^ (1 / (4 : ℝ)) := by
        simpa [s, U] using hQsizeRaw
      _ = (128 : ℝ≥0∞) * S ^ (4 : ℝ) * U ^ (1 / (4 : ℝ)) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hs0]
        norm_num [S, ENNReal.rpow_natCast]
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    exact integral_nonneg fun h ↦ norm_nonneg _
  have hC0 : 0 ≤ C := by
    dsimp [C, C_dualDifferenceInterchange]
    positivity
  have hCsizeReal : C ≤ 8 * s ^ (2 : ℕ) := by
    let T : ℝ := sizeParameter ![aux_firstDualInterval D, D.J] D.χ
    have hT : T ≤ 2 * s := by
      simpa [T, s] using aux_u2_firstDual_two_size_le_two_four_size D
    have hT0 : 0 ≤ T := by
      dsimp [T, sizeParameter]
      positivity
    change 2 * T ^ 2 ≤ 8 * s ^ 2
    calc
      2 * T ^ 2 ≤ 2 * (2 * s) ^ 2 := by
        gcongr
      _ = 8 * s ^ 2 := by ring
  have hCENN : ENNReal.ofReal C ≤ (8 : ℝ≥0∞) * S ^ (2 : ℝ) := by
    calc
      ENNReal.ofReal C ≤ ENNReal.ofReal (8 * s ^ (2 : ℕ)) :=
        ENNReal.ofReal_le_ofReal hCsizeReal
      _ = (8 : ℝ≥0∞) * S ^ (2 : ℝ) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hs0]
        norm_num [S, ENNReal.rpow_natCast]
  have hU3 : uNorm 3 F ≤ ENNReal.ofReal (C * Q ^ (1 / (4 : ℝ))) := by
    simpa [F, C, Q] using hDDI
  have hglue := aux_u2_u3_ennreal_glue (uNorm 3 F) U S C Q hC0 hQ0 hU3 hCENN hQENN
  have hfirst' : ENNReal.ofReal (trilinearFormAbs D.χ f₀ f₁ f₂) ≤
      S ^ (1 / (2 : ℝ)) * S ^ (2 / (5 : ℝ)) *
        ((128 : ℝ≥0∞) * S ^ (3 : ℝ)) ^ (1 / (2 : ℝ)) *
          uNorm 3 F ^ (1 / (10 : ℝ)) := by
    simpa [F, S, s] using hfirst
  have hnum := aux_u2_numerical_endgame
    (ENNReal.ofReal (trilinearFormAbs D.χ f₀ f₁ f₂)) S U hS
    (hfirst'.trans (mul_le_mul_of_nonneg_left hglue bot_le))
  have hfinalCoef : ENNReal.ofReal (C_u2Control D.A₀ D.A₁ D.A₂ D.J D.χ) =
      (64 : ℝ≥0∞) * S ^ (3 : ℝ) := by
    unfold C_u2Control
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hs0]
    norm_num [S, ENNReal.rpow_natCast]
  calc
    ENNReal.ofReal (trilinearFormAbs D.χ f₀ f₁ f₂) ≤
        (64 : ℝ≥0∞) * S ^ (3 : ℝ) * U ^ (1 / (160 : ℝ)) := hnum
    _ = ENNReal.ofReal (C_u2Control D.A₀ D.A₁ D.A₂ D.J D.χ) *
        uNorm 2 f₁ ^ (1 / (160 : ℝ)) := by
      rw [← hfinalCoef]

/-- The function \(F_1\) appearing in \(\label{lem:second-dualization}\).

This raw map is separated from `secondDualization` so that its support and
Cauchy--Schwarz conclusions can be stated together.
-/
def aux_secondDualFunction (χ : ℝ → ℝ) (f₀ f₂ : ℝ → ℂ) : ℝ → ℂ :=
  fun x ↦ ∫ t : ℝ,
    starRingEnd ℂ (f₀ (x - t) * f₂ (x - t + t ^ 2)) * (χ t : ℂ)

/-- The un-conjugated compact time kernel whose integral represents the
second dual function in `secondDualization`. -/
def aux_secondDualKernel (χ : ℝ → ℝ) (f₀ f₂ : ℝ → ℂ) : ℝ → ℝ → ℂ :=
  fun x t ↦ f₀ (x - t) * f₂ (x - t + t ^ 2) * (χ t : ℂ)

/-- The nonlinear coordinate in the second-dual kernel preserves null sets;
this supplies its joint measurability in `secondDualization`. -/
lemma aux_secondDual_qmp_sub_add_sq :
    Measure.QuasiMeasurePreserving (fun z : ℝ × ℝ ↦ z.1 - z.2 + z.2 ^ 2)
      (volume.prod volume) volume := by
  refine QuasiMeasurePreserving.prod_of_left (by fun_prop)
    (Filter.Eventually.of_forall fun t ↦ ?_)
  convert (measurePreserving_add_right volume (-t + t ^ 2)).quasiMeasurePreserving using 1
  funext x
  ring

/-- Joint almost-everywhere strong measurability of the compact kernel used
to form the second dual function in `secondDualization`. -/
lemma aux_secondDualKernel_aestronglyMeasurable
    (D : AdmissibleSupportData) (f₀ f₂ : ℝ → ℂ)
    (hf₀ : AEStronglyMeasurable f₀ volume)
    (hf₂ : AEStronglyMeasurable f₂ volume) :
    AEStronglyMeasurable (Function.uncurry (aux_secondDualKernel D.χ f₀ f₂))
      (volume.prod volume) := by
  have h₀ : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ f₀ (z.1 - z.2))
      (volume.prod volume) := by
    have h := hf₀.comp_quasiMeasurePreserving (aux_quasiMeasurePreserving_affine (-1))
    convert h using 1
    ext z
    simp only [Function.comp_apply]
    ring_nf
  have h₂ : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ f₂ (z.1 - z.2 + z.2 ^ 2))
      (volume.prod volume) := by
    change AEStronglyMeasurable (f₂ ∘ fun z : ℝ × ℝ ↦ z.1 - z.2 + z.2 ^ 2)
      (volume.prod volume)
    exact hf₂.comp_quasiMeasurePreserving aux_secondDual_qmp_sub_add_sq
  have hχ : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ (D.χ z.2 : ℂ))
      (volume.prod volume) :=
    (Complex.continuous_ofReal.comp
      (D.hχ_smooth.continuous.comp continuous_snd)).aestronglyMeasurable
  exact h₀.mul h₂ |>.mul hχ

/-- The one-bounded input hypotheses make the second-dual time kernel
one-bounded almost everywhere. -/
lemma aux_secondDualKernel_ae_one_bounded
    (D : AdmissibleSupportData) (f₀ f₂ : ℝ → ℂ)
    (hf₀ : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₂ : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1) :
    ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      ‖aux_secondDualKernel D.χ f₀ f₂ z.1 z.2‖ ≤ 1 := by
  have h₀' : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      ‖f₀ (z.1 + (-1 : ℝ) * z.2)‖ ≤ 1 :=
    (aux_quasiMeasurePreserving_affine (-1)).tendsto_ae hf₀
  have h₀ : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖f₀ (z.1 - z.2)‖ ≤ 1 := by
    filter_upwards [h₀'] with z hz
    convert hz using 1
    ring_nf
  have h₂ : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      ‖f₂ (z.1 - z.2 + z.2 ^ 2)‖ ≤ 1 :=
    aux_secondDual_qmp_sub_add_sq.tendsto_ae hf₂
  filter_upwards [h₀, h₂] with z hz₀ hz₂
  rw [aux_secondDualKernel, norm_mul, norm_mul]
  have hχ : ‖(D.χ z.2 : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (D.hχ_nonneg _)]
    exact D.hχ_le_one _
  calc
    ‖f₀ (z.1 - z.2)‖ * ‖f₂ (z.1 - z.2 + z.2 ^ 2)‖ * ‖(D.χ z.2 : ℂ)‖ ≤
        1 * 1 * 1 := by gcongr
    _ = 1 := by norm_num

/-- The second-dual time kernel is zero almost everywhere away from the
compact box `A₁ × J`; this uses the admissible inclusion `A₀ + J ⊆ A₁`. -/
lemma aux_secondDualKernel_ae_zero_outside
    (D : AdmissibleSupportData) (f₀ f₂ : ℝ → ℂ)
    (hf₀support : ∀ᵐ x ∂volume, x ∉ D.A₀ → f₀ x = 0) :
    ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∉ D.A₁ ×ˢ D.J → aux_secondDualKernel D.χ f₀ f₂ z.1 z.2 = 0 := by
  have h₀' : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z.1 + (-1 : ℝ) * z.2 ∉ D.A₀ → f₀ (z.1 + (-1 : ℝ) * z.2) = 0 :=
    (aux_quasiMeasurePreserving_affine (-1)).tendsto_ae hf₀support
  have h₀ : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z.1 - z.2 ∉ D.A₀ → f₀ (z.1 - z.2) = 0 := by
    filter_upwards [h₀'] with z hz
    convert hz using 1 <;> ring_nf
  filter_upwards [h₀] with z hz₀ hz
  by_cases ht : z.2 ∈ D.J
  · have hx : z.1 ∉ D.A₁ := by
      intro hx
      exact hz ⟨hx, ht⟩
    have hnotA : z.1 - z.2 ∉ D.A₀ := by
      intro hy
      apply hx
      exact D.hA₀_add_J ⟨z.1 - z.2, hy, z.2, ht, by ring⟩
    simp [aux_secondDualKernel, hz₀ hnotA]
  · have hnot : z.2 ∉ tsupport D.χ := fun hts => ht (D.hχ_support hts)
    have hzero : D.χ z.2 = 0 := image_eq_zero_of_notMem_tsupport hnot
    simp [aux_secondDualKernel, hzero]

/-- The raw second dual function is the conjugate of the un-conjugated
second-dual kernel integral. -/
lemma aux_secondDualFunction_eq_star_kernelIntegral
    (χ : ℝ → ℝ) (f₀ f₂ : ℝ → ℂ) (x : ℝ) :
    aux_secondDualFunction χ f₀ f₂ x =
      starRingEnd ℂ (∫ t : ℝ, aux_secondDualKernel χ f₀ f₂ x t) := by
  rw [aux_secondDualFunction, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  simp only [aux_secondDualKernel, map_mul, Complex.conj_ofReal]

/-- The second dual function is square-integrable and supported almost
everywhere on `A₁`, as needed for the Cauchy--Schwarz step in
`secondDualization`. -/
lemma aux_secondDualFunction_memLp_and_support
    (D : AdmissibleSupportData) (f₀ f₂ : ℝ → ℂ)
    (hf₀meas : AEStronglyMeasurable f₀ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₀bound : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₀support : ∀ᵐ x ∂volume, x ∉ D.A₀ → f₀ x = 0) :
    (∀ᵐ x ∂volume, x ∉ D.A₁ → aux_secondDualFunction D.χ f₀ f₂ x = 0) ∧
      MemLp (aux_secondDualFunction D.χ f₀ f₂) (2 : ℝ≥0∞) volume := by
  let Q := aux_secondDualKernel D.χ f₀ f₂
  let X := D.A₁
  have hXcompact : IsCompact X := by
    rcases D.hA₁ with ⟨a, b, hab, hA₁⟩
    simpa [X, hA₁] using isCompact_Icc
  have hQmeas : AEStronglyMeasurable (Function.uncurry Q)
      (volume.prod volume) := by
    exact aux_secondDualKernel_aestronglyMeasurable D f₀ f₂ hf₀meas hf₂meas
  have hQbound : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖Q z.1 z.2‖ ≤ 1 := by
    exact aux_secondDualKernel_ae_one_bounded D f₀ f₂ hf₀bound hf₂bound
  have hQsupport : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∉ X ×ˢ D.J → Q z.1 z.2 = 0 := by
    exact aux_secondDualKernel_ae_zero_outside D f₀ f₂ hf₀support
  have hTmeas : MeasurableSet (X ×ˢ D.J) :=
    hXcompact.isClosed.measurableSet.prod (by
      rcases D.hJ with ⟨a, b, hab, hJ⟩
      rw [hJ]
      exact measurableSet_Icc)
  have hTfinite : (volume.prod volume) (X ×ˢ D.J) < ∞ := by
    have hJcompact : IsCompact D.J := by
      rcases D.hJ with ⟨a, b, hab, hJ⟩
      rw [hJ]
      exact isCompact_Icc
    exact (hXcompact.prod hJcompact).measure_lt_top
  have hQmem : MemLp (Function.uncurry Q) 1 (volume.prod volume) :=
    aux_memLp_of_ae_bound_of_ae_support _ hQmeas 1 hQbound (X ×ˢ D.J)
      hTmeas hTfinite hQsupport 1
  have hQint : Integrable (Function.uncurry Q) (volume.prod volume) :=
    memLp_one_iff_integrable.mp hQmem
  have hsuppSections : ∀ᵐ x : ℝ ∂volume, ∀ᵐ t : ℝ ∂volume,
      (x, t) ∉ X ×ˢ D.J → Q x t = 0 :=
    Measure.ae_ae_of_ae_prod hQsupport
  have hrawSupport : ∀ᵐ x : ℝ ∂volume, x ∉ X → (∫ t : ℝ, Q x t) = 0 := by
    filter_upwards [hsuppSections] with x hx
    intro hnot
    rw [← integral_zero]
    apply integral_congr_ae
    filter_upwards [hx] with t ht
    apply ht
    intro hmem
    exact hnot hmem.1
  have hrawLp : MemLp (fun x : ℝ ↦ ∫ t : ℝ, Q x t) (2 : ℝ≥0∞) volume := by
    rcases D.hJ with ⟨a, b, hab, hJ⟩
    have hJcompact : IsCompact D.J := by
      rw [hJ]
      exact isCompact_Icc
    exact (aux_timeIntegral_memLp_compactSupport X D.J hXcompact hJcompact Q
      hQmeas hQbound hQsupport).2
  have hstarSupport : ∀ᵐ x : ℝ ∂volume, x ∉ X →
      starRingEnd ℂ (∫ t : ℝ, Q x t) = 0 := by
    filter_upwards [hrawSupport] with x hx hnot
    simp [hx hnot]
  have hstarLp : MemLp (fun x : ℝ ↦ starRingEnd ℂ (∫ t : ℝ, Q x t))
      (2 : ℝ≥0∞) volume := by
    exact hrawLp.star
  constructor
  · filter_upwards [hstarSupport] with x hx hnot
    rw [aux_secondDualFunction_eq_star_kernelIntegral]
    exact hx hnot
  · rw [show aux_secondDualFunction D.χ f₀ f₂ =
        fun x : ℝ ↦ starRingEnd ℂ (∫ t : ℝ, Q x t) by
      funext x
      exact aux_secondDualFunction_eq_star_kernelIntegral D.χ f₀ f₂ x]
    exact hstarLp

/-- The second dual function is almost everywhere bounded by the length of
the cutoff interval.  This makes its re-entry into the trilinear form
integrable in `secondDualization`. -/
lemma aux_secondDualFunction_ae_bound
    (D : AdmissibleSupportData) (f₀ f₂ : ℝ → ℂ)
    (hf₀meas : AEStronglyMeasurable f₀ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₀bound : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₀support : ∀ᵐ x ∂volume, x ∉ D.A₀ → f₀ x = 0) :
    ∀ᵐ x ∂volume, ‖aux_secondDualFunction D.χ f₀ f₂ x‖ ≤ volume.real D.J := by
  let Q := aux_secondDualKernel D.χ f₀ f₂
  let X := D.A₁
  have hXcompact : IsCompact X := by
    rcases D.hA₁ with ⟨a, b, hab, hA₁⟩
    simpa [X, hA₁] using isCompact_Icc
  have hJcompact : IsCompact D.J := by
    rcases D.hJ with ⟨a, b, hab, hJ⟩
    rw [hJ]
    exact isCompact_Icc
  have hQmeas : AEStronglyMeasurable (Function.uncurry Q)
      (volume.prod volume) :=
    aux_secondDualKernel_aestronglyMeasurable D f₀ f₂ hf₀meas hf₂meas
  have hQbound : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖Q z.1 z.2‖ ≤ 1 :=
    aux_secondDualKernel_ae_one_bounded D f₀ f₂ hf₀bound hf₂bound
  have hQsupport : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∉ X ×ˢ D.J → Q z.1 z.2 = 0 :=
    aux_secondDualKernel_ae_zero_outside D f₀ f₂ hf₀support
  have hTmeas : MeasurableSet (X ×ˢ D.J) :=
    hXcompact.isClosed.measurableSet.prod hJcompact.isClosed.measurableSet
  have hTfinite : (volume.prod volume) (X ×ˢ D.J) < ∞ :=
    (hXcompact.prod hJcompact).measure_lt_top
  have hQmem : MemLp (Function.uncurry Q) 1 (volume.prod volume) :=
    aux_memLp_of_ae_bound_of_ae_support _ hQmeas 1 hQbound (X ×ˢ D.J)
      hTmeas hTfinite hQsupport 1
  have hQint : Integrable (Function.uncurry Q) (volume.prod volume) :=
    memLp_one_iff_integrable.mp hQmem
  have hsections : ∀ᵐ x : ℝ ∂volume, Integrable (Q x) volume :=
    hQint.prod_right_ae
  have hboundsections : ∀ᵐ x : ℝ ∂volume, ∀ᵐ t : ℝ ∂volume, ‖Q x t‖ ≤ 1 :=
    Measure.ae_ae_of_ae_prod hQbound
  have hsupportsections : ∀ᵐ x : ℝ ∂volume, ∀ᵐ t : ℝ ∂volume,
      (x, t) ∉ X ×ˢ D.J → Q x t = 0 :=
    Measure.ae_ae_of_ae_prod hQsupport
  have hJmeas : MeasurableSet D.J := hJcompact.isClosed.measurableSet
  have hJfinite : volume D.J < ∞ := hJcompact.measure_lt_top
  have hJint : Integrable (D.J.indicator (1 : ℝ → ℝ)) volume := by
    rw [← memLp_one_iff_integrable]
    exact memLp_indicator_const 1 hJmeas 1 (Or.inr hJfinite.ne)
  have hraw : ∀ᵐ x : ℝ ∂volume, ‖∫ t : ℝ, Q x t‖ ≤ volume.real D.J := by
    filter_upwards [hsections, hboundsections, hsupportsections] with x hxint hxbound hxsupport
    calc
      ‖∫ t : ℝ, Q x t‖ ≤ ∫ t : ℝ, ‖Q x t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, D.J.indicator (1 : ℝ → ℝ) t := by
        apply integral_mono_ae hxint.norm hJint
        filter_upwards [hxbound, hxsupport] with t htbound htsupport
        by_cases ht : t ∈ D.J
        · simp [ht, htbound]
        · have hnotT : (x, t) ∉ X ×ˢ D.J := by
            intro hmem
            change x ∈ X ∧ t ∈ D.J at hmem
            exact ht hmem.2
          simp [ht, htsupport hnotT]
      _ = volume.real D.J := by
        simpa only [Measure.real] using (integral_indicator_one (μ := volume) hJmeas)
  filter_upwards [hraw] with x hx
  rw [aux_secondDualFunction_eq_star_kernelIntegral]
  simpa [Q] using hx

/-- An almost-everywhere compact-box support statement for a trilinear
integrand.  This is the integrability bookkeeping used by
`secondDualization` after its linear shear. -/
lemma aux_secondDualization_trilinearIntegrand_ae_zero_outside
    (A J : Set ℝ) (f₀ f₁ f₂ : ℝ → ℂ) (χ : ℝ → ℝ)
    (hf₀ : ∀ᵐ x ∂volume, x ∉ A → f₀ x = 0) (hχ : tsupport χ ⊆ J) :
    ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∉ A ×ˢ J → aux_u3_trilinearIntegrand f₀ f₁ f₂ χ z = 0 := by
  have houter : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z.1 ∉ A → f₀ z.1 = 0 := by
    exact (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).tendsto_ae hf₀
  filter_upwards [houter] with z hz
  intro hnot
  by_cases hx : z.1 ∈ A
  · have ht : z.2 ∉ J := by
      intro ht
      exact hnot ⟨hx, ht⟩
    have hts : z.2 ∉ tsupport χ := fun hts ↦ ht (hχ hts)
    have hχzero : χ z.2 = 0 := image_eq_zero_of_notMem_tsupport hts
    simp [aux_u3_trilinearIntegrand, hχzero]
  · simp [aux_u3_trilinearIntegrand, hz hx]

/-- A compact trilinear kernel is integrable when its middle factor has a
finite almost-everywhere bound.  The two instances below allow the second
dual function to be inserted into the form in `secondDualization`. -/
lemma aux_secondDualization_trilinearIntegrand_integrable_middle_bound
    (A J : Set ℝ) (hA : IsCompact A) (hJ : IsCompact J)
    (f₀ f₁ f₂ : ℝ → ℂ) (χ : ℝ → ℝ) (B : ℝ)
    (hf₀meas : AEStronglyMeasurable f₀ volume)
    (hf₁meas : AEStronglyMeasurable f₁ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₀bound : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₁bound : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ B)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hB : 0 ≤ B)
    (hf₀support : ∀ᵐ x ∂volume, x ∉ A → f₀ x = 0)
    (hχcont : Continuous χ) (hχ₀ : ∀ t : ℝ, 0 ≤ χ t)
    (hχ₁ : ∀ t : ℝ, χ t ≤ 1) (hχsupport : tsupport χ ⊆ J) :
    Integrable (aux_u3_trilinearIntegrand f₀ f₁ f₂ χ) (volume.prod volume) := by
  rw [← memLp_one_iff_integrable]
  apply aux_memLp_of_ae_bound_of_ae_support
    (aux_u3_trilinearIntegrand f₀ f₁ f₂ χ)
    (aux_u3_trilinearIntegrand_aestronglyMeasurable f₀ f₁ f₂ χ
      hf₀meas hf₁meas hf₂meas hχcont)
    B ?_ (A ×ˢ J) (hA.isClosed.measurableSet.prod hJ.isClosed.measurableSet)
    (hA.prod hJ).measure_lt_top
    (aux_secondDualization_trilinearIntegrand_ae_zero_outside A J f₀ f₁ f₂ χ hf₀support
      hχsupport) 1
  have h0 : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖f₀ z.1‖ ≤ 1 := by
    exact (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).tendsto_ae hf₀bound
  have h1' : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖f₁ (z.1 + 1 * z.2)‖ ≤ B := by
    exact (aux_quasiMeasurePreserving_affine 1).tendsto_ae hf₁bound
  have h1 : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖f₁ (z.1 + z.2)‖ ≤ B := by
    simpa only [one_mul] using h1'
  have h2 : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖f₂ (z.1 + z.2 ^ 2)‖ ≤ 1 := by
    exact aux_u3_qmp_add_sq.tendsto_ae hf₂bound
  filter_upwards [h0, h1, h2] with z hz0 hz1 hz2
  change ‖f₀ z.1‖ ≤ 1 at hz0
  change ‖f₁ (z.1 + z.2)‖ ≤ B at hz1
  change ‖f₂ (z.1 + z.2 ^ 2)‖ ≤ 1 at hz2
  rw [aux_u3_trilinearIntegrand, norm_mul, norm_mul, norm_mul]
  have hχnorm : ‖(χ z.2 : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ₀ _)]
    exact hχ₁ _
  calc
    ‖f₀ z.1‖ * ‖f₁ (z.1 + z.2)‖ * ‖f₂ (z.1 + z.2 ^ 2)‖ * ‖(χ z.2 : ℂ)‖ ≤
        1 * B * 1 * 1 := by gcongr
    _ = B := by ring

/-- The determinant-one shear `y = x + t` rewrites the original trilinear
form as the pairing with the conjugate second-dual function. -/
lemma aux_secondDualization_trilinear_eq_pairing
    (χ : ℝ → ℝ) (f₀ f₁ f₂ : ℝ → ℂ)
    (hP : Integrable (Function.uncurry fun x t : ℝ ↦
      f₀ x * f₁ (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ))
      (volume.prod volume)) :
    trilinearForm χ f₀ f₁ f₂ =
      ∫ y : ℝ, f₁ y * starRingEnd ℂ (aux_secondDualFunction χ f₀ f₂ y) := by
  let P : ℝ → ℝ → ℂ := fun x t ↦
    f₀ x * f₁ (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ)
  have hshear : (∫ y : ℝ, ∫ t : ℝ, P (y - t) t) =
      ∫ x : ℝ, ∫ t : ℝ, P x t := by
    simpa only [P, one_mul] using (aux_integral_shear_sub_mul P (by
      simpa only [P] using hP) 1)
  calc
    trilinearForm χ f₀ f₁ f₂ = ∫ x : ℝ, ∫ t : ℝ, P x t := by rfl
    _ = ∫ y : ℝ, ∫ t : ℝ, P (y - t) t := hshear.symm
    _ = ∫ y : ℝ, f₁ y * starRingEnd ℂ (aux_secondDualFunction χ f₀ f₂ y) := by
      apply integral_congr_ae
      filter_upwards with y
      calc
        (∫ t : ℝ, P (y - t) t) =
            ∫ t : ℝ, f₁ y *
              (f₀ (y - t) * f₂ (y - t + t ^ 2) * (χ t : ℂ)) := by
          apply integral_congr_ae
          filter_upwards with t
          simp only [P]
          ring_nf
        _ = f₁ y * ∫ t : ℝ,
            f₀ (y - t) * f₂ (y - t + t ^ 2) * (χ t : ℂ) :=
          integral_const_mul _ _
        _ = f₁ y * starRingEnd ℂ (aux_secondDualFunction χ f₀ f₂ y) := by
          rw [aux_secondDualFunction_eq_star_kernelIntegral]
          simp [aux_secondDualKernel]

/-- The second trilinear form occurring after Cauchy--Schwarz is exactly the
nonnegative `L²` energy of the second-dual function. -/
lemma aux_secondDualization_dual_trilinearAbs_eq_energy
    (χ : ℝ → ℝ) (f₀ f₂ : ℝ → ℂ)
    (hP : Integrable (Function.uncurry fun x t : ℝ ↦
      f₀ x * aux_secondDualFunction χ f₀ f₂ (x + t) * f₂ (x + t ^ 2) *
        (χ t : ℂ)) (volume.prod volume)) :
    trilinearFormAbs χ f₀ (aux_secondDualFunction χ f₀ f₂) f₂ =
      ∫ x : ℝ, ‖aux_secondDualFunction χ f₀ f₂ x‖ ^ (2 : ℝ) := by
  unfold trilinearFormAbs
  rw [aux_secondDualization_trilinear_eq_pairing χ f₀
    (aux_secondDualFunction χ f₀ f₂) f₂ hP]
  calc
    ‖∫ x : ℝ, aux_secondDualFunction χ f₀ f₂ x *
        starRingEnd ℂ (aux_secondDualFunction χ f₀ f₂ x)‖ =
        ‖∫ x : ℝ,
          ((‖aux_secondDualFunction χ f₀ f₂ x‖ ^ (2 : ℝ) : ℝ) : ℂ)‖ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      rw [RCLike.mul_conj]
      norm_num [Real.rpow_two]
    _ = ∫ x : ℝ, ‖aux_secondDualFunction χ f₀ f₂ x‖ ^ (2 : ℝ) := by
      have hcast : (∫ x : ℝ,
          ((‖aux_secondDualFunction χ f₀ f₂ x‖ ^ (2 : ℝ) : ℝ) : ℂ)) =
          ((∫ x : ℝ, ‖aux_secondDualFunction χ f₀ f₂ x‖ ^ (2 : ℝ) : ℝ) : ℂ) :=
        integral_ofReal
      rw [hcast, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)]

/-- The Cauchy--Schwarz conclusion of `secondDualization`, once compact
integrability of the original and second-dual trilinear kernels is supplied. -/
lemma aux_secondDualization_cauchy_bound
    (D : AdmissibleSupportData) (f₀ f₁ f₂ : ℝ → ℂ)
    (hf₁meas : AEStronglyMeasurable f₁ volume)
    (hf₁bound : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₁support : ∀ᵐ x ∂volume, x ∉ D.A₁ → f₁ x = 0)
    (hF₂ : MemLp (aux_secondDualFunction D.χ f₀ f₂) (2 : ℝ≥0∞) volume)
    (hP : Integrable (Function.uncurry fun x t : ℝ ↦
      f₀ x * f₁ (x + t) * f₂ (x + t ^ 2) * (D.χ t : ℂ))
      (volume.prod volume))
    (hPdual : Integrable (Function.uncurry fun x t : ℝ ↦
      f₀ x * aux_secondDualFunction D.χ f₀ f₂ (x + t) * f₂ (x + t ^ 2) *
        (D.χ t : ℂ)) (volume.prod volume)) :
    trilinearFormAbs D.χ f₀ f₁ f₂ ≤
      intervalLength D.A₁ ^ (1 / (2 : ℝ)) *
        trilinearFormAbs D.χ f₀ (aux_secondDualFunction D.χ f₀ f₂) f₂ ^
          (1 / (2 : ℝ)) := by
  have hA₁compact : IsCompact D.A₁ := by
    rcases D.hA₁ with ⟨a, b, hab, hA⟩
    rw [hA]
    exact isCompact_Icc
  have hA₁meas : MeasurableSet D.A₁ := hA₁compact.isClosed.measurableSet
  have hf₁Lp : MemLp f₁ (2 : ℝ≥0∞) volume :=
    aux_memLp_of_ae_bound_of_ae_support f₁ hf₁meas 1 hf₁bound D.A₁ hA₁meas
      hA₁compact.measure_lt_top hf₁support 2
  have henergy₁ : (∫ x : ℝ, ‖f₁ x‖ ^ (2 : ℝ)) ≤ volume.real D.A₁ :=
    aux_energy_le_measure D.A₁ hA₁meas hA₁compact.measure_lt_top.ne f₁ hf₁Lp
      hf₁bound hf₁support
  have houter := aux_outer_cauchy f₁
    (fun x : ℝ ↦ starRingEnd ℂ (aux_secondDualFunction D.χ f₀ f₂ x))
    hf₁Lp hF₂.star
  have hE₁nonneg : 0 ≤ ∫ x : ℝ, ‖f₁ x‖ ^ (2 : ℝ) :=
    integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _
  have hE₁pow : (∫ x : ℝ, ‖f₁ x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤
      (volume.real D.A₁) ^ (1 / (2 : ℝ)) :=
    Real.rpow_le_rpow hE₁nonneg henergy₁ (by norm_num)
  have hFenergyNonneg : 0 ≤ ∫ x : ℝ,
      ‖aux_secondDualFunction D.χ f₀ f₂ x‖ ^ (2 : ℝ) :=
    integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _
  calc
    trilinearFormAbs D.χ f₀ f₁ f₂ =
        ‖∫ x : ℝ, f₁ x * starRingEnd ℂ (aux_secondDualFunction D.χ f₀ f₂ x)‖ := by
      unfold trilinearFormAbs
      rw [aux_secondDualization_trilinear_eq_pairing D.χ f₀ f₁ f₂ hP]
    _ ≤ (∫ x : ℝ, ‖f₁ x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (∫ x : ℝ, ‖aux_secondDualFunction D.χ f₀ f₂ x‖ ^ (2 : ℝ)) ^
          (1 / (2 : ℝ)) := by
      simpa [RCLike.star_def] using houter
    _ ≤ (volume.real D.A₁) ^ (1 / (2 : ℝ)) *
        (∫ x : ℝ, ‖aux_secondDualFunction D.χ f₀ f₂ x‖ ^ (2 : ℝ)) ^
          (1 / (2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hE₁pow
        (Real.rpow_nonneg hFenergyNonneg _)
    _ = intervalLength D.A₁ ^ (1 / (2 : ℝ)) *
        trilinearFormAbs D.χ f₀ (aux_secondDualFunction D.χ f₀ f₂) f₂ ^
          (1 / (2 : ℝ)) := by
      rw [aux_secondDualization_dual_trilinearAbs_eq_energy D.χ f₀ f₂ hPdual]
      rfl

/--
Let \(\mathfrak D\) be admissible and let \(f_0,f_1,f_2\) be \(1\)-bounded
with \(f_i\) supported in \(A_i\). Define
\[
F_1(x):=\int_\R\overline{f_0(x-t)f_2(x-t+t^2)}\chi(t)\dd t.
\]
Then \(F_1\) is supported in \(A_1\) and
\[
\Ichi(f_0,f_1,f_2)
\leq
\ell_1^{1/2}\Ichi(f_0,F_1,f_2)^{1/2}.
\]
-/
theorem secondDualization
    (D : AdmissibleSupportData) (f₀ f₁ f₂ : ℝ → ℂ)
    (hf₀_measurable : AEStronglyMeasurable f₀ volume)
    (hf₁_measurable : AEStronglyMeasurable f₁ volume)
    (hf₂_measurable : AEStronglyMeasurable f₂ volume)
    (hf₀_one_bounded : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₁_one_bounded : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₂_one_bounded : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₀_support : ∀ᵐ x ∂volume, x ∉ D.A₀ → f₀ x = 0)
    (hf₁_support : ∀ᵐ x ∂volume, x ∉ D.A₁ → f₁ x = 0)
    (_hf₂_support : ∀ᵐ x ∂volume, x ∉ D.A₂ → f₂ x = 0) :
    (∀ᵐ x ∂volume, x ∉ D.A₁ → aux_secondDualFunction D.χ f₀ f₂ x = 0) ∧
      trilinearFormAbs D.χ f₀ f₁ f₂ ≤
        intervalLength D.A₁ ^ (1 / (2 : ℝ)) *
          trilinearFormAbs D.χ f₀ (aux_secondDualFunction D.χ f₀ f₂) f₂ ^
            (1 / (2 : ℝ)) := by
  have hFdata := aux_secondDualFunction_memLp_and_support D f₀ f₂
    hf₀_measurable hf₂_measurable hf₀_one_bounded hf₂_one_bounded hf₀_support
  constructor
  · exact hFdata.1
  · have hA₀compact : IsCompact D.A₀ := by
      rcases D.hA₀ with ⟨a, b, hab, hA₀⟩
      rw [hA₀]
      exact isCompact_Icc
    have hJcompact : IsCompact D.J := by
      rcases D.hJ with ⟨a, b, hab, hJ⟩
      rw [hJ]
      exact isCompact_Icc
    have hP : Integrable (Function.uncurry fun x t : ℝ ↦
        f₀ x * f₁ (x + t) * f₂ (x + t ^ 2) * (D.χ t : ℂ))
        (volume.prod volume) := by
      change Integrable (aux_u3_trilinearIntegrand f₀ f₁ f₂ D.χ)
        (volume.prod volume)
      exact aux_secondDualization_trilinearIntegrand_integrable_middle_bound D.A₀ D.J
        hA₀compact hJcompact f₀ f₁ f₂ D.χ 1
        hf₀_measurable hf₁_measurable hf₂_measurable
        hf₀_one_bounded hf₁_one_bounded hf₂_one_bounded (by norm_num)
        hf₀_support D.hχ_smooth.continuous D.hχ_nonneg D.hχ_le_one D.hχ_support
    have hFbound : ∀ᵐ x ∂volume,
        ‖aux_secondDualFunction D.χ f₀ f₂ x‖ ≤ volume.real D.J :=
      aux_secondDualFunction_ae_bound D f₀ f₂ hf₀_measurable hf₂_measurable
        hf₀_one_bounded hf₂_one_bounded hf₀_support
    have hPdual : Integrable (Function.uncurry fun x t : ℝ ↦
        f₀ x * aux_secondDualFunction D.χ f₀ f₂ (x + t) * f₂ (x + t ^ 2) *
          (D.χ t : ℂ)) (volume.prod volume) := by
      change Integrable
        (aux_u3_trilinearIntegrand f₀ (aux_secondDualFunction D.χ f₀ f₂) f₂ D.χ)
          (volume.prod volume)
      exact aux_secondDualization_trilinearIntegrand_integrable_middle_bound D.A₀ D.J
        hA₀compact hJcompact f₀ (aux_secondDualFunction D.χ f₀ f₂) f₂ D.χ
        (volume.real D.J)
        hf₀_measurable hFdata.2.aestronglyMeasurable hf₂_measurable
        hf₀_one_bounded hFbound hf₂_one_bounded ENNReal.toReal_nonneg
        hf₀_support D.hχ_smooth.continuous D.hχ_nonneg D.hχ_le_one D.hχ_support
    exact aux_secondDualization_cauchy_bound D f₀ f₁ f₂ hf₁_measurable
      hf₁_one_bounded hf₁_support hFdata.2 hP hPdual

/-- The Fourier transform of the second-dual function is the conjugate of
the corresponding frequency-character trilinear form.  This identifies the
`u²` quantity used by `normalizedNonlinearSmoothing`. -/
lemma aux_normalized_secondDual_fourier_eq
    (χ : ℝ → ℝ) (f₀ f₂ : ℝ → ℂ) (ξ : ℝ)
    (hP : Integrable (Function.uncurry fun x t : ℝ ↦
      f₀ x * frequencyCharacter ξ (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ))
      (volume.prod volume)) :
    𝓕 (aux_secondDualFunction χ f₀ f₂) ξ =
      starRingEnd ℂ (trilinearForm χ f₀ (frequencyCharacter ξ) f₂) := by
  rw [aux_secondDualization_trilinear_eq_pairing χ f₀ (frequencyCharacter ξ) f₂ hP]
  rw [← integral_conj]
  rw [Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards with x
  have hphase : (𝐞 (-inner ℝ x ξ) : ℂ) =
      starRingEnd ℂ (frequencyCharacter ξ x) := by
    rw [frequencyCharacter, aux_phase_star_exponential]
    congr 1
  rw [Circle.smul_def, hphase]
  rw [map_mul]
  simp only [starRingEnd_apply, star_star]
  ring

/-- A one-bounded function supported on the first interval has its `L²`
norm bounded by the square root of that interval's length; this is used in
the Fourier estimate for `normalizedNonlinearSmoothing`. -/
lemma aux_normalized_l2_toReal_le_length_half
    (D : AdmissibleSupportData) (f₀ : ℝ → ℂ)
    (hf₀meas : AEStronglyMeasurable f₀ volume)
    (hf₀bound : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₀support : ∀ᵐ x ∂volume, x ∉ D.A₀ → f₀ x = 0) :
    (eLpNorm f₀ (2 : ℝ≥0∞) volume).toReal ≤
      intervalLength D.A₀ ^ (1 / (2 : ℝ)) := by
  have hA₀compact : IsCompact D.A₀ := by
    rcases D.hA₀ with ⟨a, b, hab, hA⟩
    rw [hA]
    exact isCompact_Icc
  have hf₀Lp : MemLp f₀ (2 : ℝ≥0∞) volume :=
    aux_memLp_of_ae_bound_of_ae_support f₀ hf₀meas 1 hf₀bound D.A₀
      hA₀compact.isClosed.measurableSet hA₀compact.measure_lt_top hf₀support 2
  have henergy : (∫ x : ℝ, ‖f₀ x‖ ^ (2 : ℝ)) ≤ volume.real D.A₀ :=
    aux_energy_le_measure D.A₀ hA₀compact.isClosed.measurableSet
      hA₀compact.measure_lt_top.ne f₀ hf₀Lp hf₀bound hf₀support
  rw [measureReal_def] at henergy
  rw [hf₀Lp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg
    (integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _) _)]
  simp only [ENNReal.toReal_ofNat]
  simpa [intervalLength, one_div] using
    (Real.rpow_le_rpow
      (integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)
      henergy (by norm_num : 0 ≤ (2 : ℝ)⁻¹))

/-- The bilinear Sobolev estimate bounds each Fourier value of the
second-dual function.  This is the analytic Fourier step in
`normalizedNonlinearSmoothing`. -/
lemma aux_normalized_secondDual_fourier_pointwise_bound
    (D : AdmissibleSupportData) (f₀ f₂ : ℝ → ℂ)
    (hf₀meas : AEStronglyMeasurable f₀ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₀bound : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₀support : ∀ᵐ x ∂volume, x ∉ D.A₀ → f₀ x = 0)
    (hf₂support : ∀ᵐ x ∂volume, x ∉ D.A₂ → f₂ x = 0)
    (ξ : ℝ) :
    ‖𝓕 (aux_secondDualFunction D.χ f₀ f₂) ξ‖ ≤
      C_bilinearSobolevEstimates D.J D.χ *
        intervalLength D.A₀ ^ (1 / (2 : ℝ)) *
          (aux_sobolevNormRaw (1 / 2 : ℝ) f₂).toReal := by
  have hA₀compact : IsCompact D.A₀ := by
    rcases D.hA₀ with ⟨a, b, hab, hA⟩
    rw [hA]
    exact isCompact_Icc
  have hJcompact : IsCompact D.J := by
    rcases D.hJ with ⟨a, b, hab, hJ⟩
    rw [hJ]
    exact isCompact_Icc
  have hf₀Lp : MemLp f₀ (2 : ℝ≥0∞) volume :=
    aux_memLp_of_ae_bound_of_ae_support f₀ hf₀meas 1 hf₀bound D.A₀
      hA₀compact.isClosed.measurableSet hA₀compact.measure_lt_top hf₀support 2
  have hf₂Lp : MemLp f₂ (2 : ℝ≥0∞) volume := by
    rcases D.hA₂ with ⟨a, b, hab, hA⟩
    rw [hA] at hf₂support
    exact aux_memLp_of_ae_bound_of_ae_support f₂ hf₂meas 1 hf₂bound (Set.Icc a b)
      measurableSet_Icc isCompact_Icc.measure_lt_top hf₂support 2
  have hP : Integrable (Function.uncurry fun x t : ℝ ↦
      f₀ x * frequencyCharacter ξ (x + t) * f₂ (x + t ^ 2) * (D.χ t : ℂ))
      (volume.prod volume) := by
    change Integrable (aux_u3_trilinearIntegrand f₀ (frequencyCharacter ξ) f₂ D.χ)
      (volume.prod volume)
    apply aux_secondDualization_trilinearIntegrand_integrable_middle_bound D.A₀ D.J
      hA₀compact hJcompact f₀ (frequencyCharacter ξ) f₂ D.χ 1
    · exact hf₀meas
    · have hcont : Continuous (frequencyCharacter ξ) := by
        unfold frequencyCharacter exponential
        fun_prop
      exact hcont.aestronglyMeasurable
    · exact hf₂meas
    · exact hf₀bound
    · filter_upwards with x
      simp [frequencyCharacter, aux_norm_exponential]
    · exact hf₂bound
    · norm_num
    · exact hf₀support
    · exact D.hχ_smooth.continuous
    · exact D.hχ_nonneg
    · exact D.hχ_le_one
    · exact D.hχ_support
  have hfourier := aux_normalized_secondDual_fourier_eq D.χ f₀ f₂ ξ hP
  have hbil := (bilinearSobolevEstimates D.J D.χ
    (by rcases D.hJ with ⟨a, b, hab, hJ⟩; exact ⟨a, b, hab.le, hJ⟩)
    D.hχ_smooth D.hχ_compact D.hχ_nonneg D.hχ_le_one D.hχ_support ξ
    f₀ (fun _ : ℝ ↦ (0 : ℂ)) f₂ hf₀Lp
    (by exact MemLp.zero) hf₂Lp).2
  have hL2 := aux_normalized_l2_toReal_le_length_half D f₀ hf₀meas hf₀bound hf₀support
  have hC : 0 ≤ C_bilinearSobolevEstimates D.J D.χ := by
    unfold C_bilinearSobolevEstimates
    positivity
  have hraw : aux_sobolevNormRaw (1 / 2 : ℝ) f₂ =
      sobolevNorm (1 / 2 : ℝ) hf₂Lp.toLp :=
    aux_sobolevDifference_sobolevNormRaw_eq_sobolevNorm _ _ hf₂Lp
  calc
    ‖𝓕 (aux_secondDualFunction D.χ f₀ f₂) ξ‖ =
        trilinearFormAbs D.χ f₀ (frequencyCharacter ξ) f₂ := by
      rw [hfourier, starRingEnd_apply, norm_star]
      rfl
    _ ≤ C_bilinearSobolevEstimates D.J D.χ *
        (eLpNorm f₀ (2 : ℝ≥0∞) volume).toReal *
          (sobolevNorm (1 / 2 : ℝ) hf₂Lp.toLp).toReal := hbil
    _ ≤ C_bilinearSobolevEstimates D.J D.χ *
        intervalLength D.A₀ ^ (1 / (2 : ℝ)) *
          (sobolevNorm (1 / 2 : ℝ) hf₂Lp.toLp).toReal :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hL2 hC) ENNReal.toReal_nonneg
    _ = C_bilinearSobolevEstimates D.J D.χ *
        intervalLength D.A₀ ^ (1 / (2 : ℝ)) *
          (aux_sobolevNormRaw (1 / 2 : ℝ) f₂).toReal := by rw [hraw]

/-- The `u²` norm of the second-dual function is first bounded with a real
Sobolev factor.  The following lemma converts that pointwise Fourier bound
to an essential-supremum bound for `normalizedNonlinearSmoothing`. -/
lemma aux_normalized_secondDual_uNorm_two_bound_toReal
    (D : AdmissibleSupportData) (f₀ f₂ : ℝ → ℂ)
    (hf₀meas : AEStronglyMeasurable f₀ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₀bound : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₀support : ∀ᵐ x ∂volume, x ∉ D.A₀ → f₀ x = 0)
    (hf₂support : ∀ᵐ x ∂volume, x ∉ D.A₂ → f₂ x = 0) :
    uNorm 2 (aux_secondDualFunction D.χ f₀ f₂) ≤
      ENNReal.ofReal
        (C_bilinearSobolevEstimates D.J D.χ *
          intervalLength D.A₀ ^ (1 / (2 : ℝ)) *
            (aux_sobolevNormRaw (1 / 2 : ℝ) f₂).toReal) := by
  rw [uNorm, ite_eq_left rfl, eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards with ξ
  exact aux_normalized_secondDual_fourier_pointwise_bound D f₀ f₂ hf₀meas hf₂meas
    hf₀bound hf₂bound hf₀support hf₂support ξ

/-- The Fourier/bilinear control of the second-dual `u²` norm in the
`ENNReal` form used by `normalizedNonlinearSmoothing`. -/
lemma aux_normalized_secondDual_uNorm_two_bound
    (D : AdmissibleSupportData) (f₀ f₂ : ℝ → ℂ)
    (hf₀meas : AEStronglyMeasurable f₀ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₀bound : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₀support : ∀ᵐ x ∂volume, x ∉ D.A₀ → f₀ x = 0)
    (hf₂support : ∀ᵐ x ∂volume, x ∉ D.A₂ → f₂ x = 0) :
    uNorm 2 (aux_secondDualFunction D.χ f₀ f₂) ≤
      ENNReal.ofReal (C_bilinearSobolevEstimates D.J D.χ) *
        ENNReal.ofReal (intervalLength D.A₀) ^ (1 / (2 : ℝ)) *
          aux_sobolevNormRaw (1 / 2 : ℝ) f₂ := by
  have hmain := aux_normalized_secondDual_uNorm_two_bound_toReal D f₀ f₂ hf₀meas hf₂meas
    hf₀bound hf₂bound hf₀support hf₂support
  have hf₂Lp : MemLp f₂ (2 : ℝ≥0∞) volume := by
    rcases D.hA₂ with ⟨a, b, hab, hA⟩
    rw [hA] at hf₂support
    exact aux_memLp_of_ae_bound_of_ae_support f₂ hf₂meas 1 hf₂bound (Set.Icc a b)
      measurableSet_Icc isCompact_Icc.measure_lt_top hf₂support 2
  have hraw : aux_sobolevNormRaw (1 / 2 : ℝ) f₂ =
      sobolevNorm (1 / 2 : ℝ) hf₂Lp.toLp :=
    aux_sobolevDifference_sobolevNormRaw_eq_sobolevNorm _ _ hf₂Lp
  have hrawTop : aux_sobolevNormRaw (1 / 2 : ℝ) f₂ < ∞ := by
    rw [hraw]
    exact aux_bilinear_sobolevNorm_half_lt_top hf₂Lp.toLp
  have hC : 0 ≤ C_bilinearSobolevEstimates D.J D.χ := by
    unfold C_bilinearSobolevEstimates
    positivity
  have hL : 0 ≤ intervalLength D.A₀ := by
    unfold intervalLength
    exact ENNReal.toReal_nonneg
  calc
    uNorm 2 (aux_secondDualFunction D.χ f₀ f₂) ≤
        ENNReal.ofReal
          (C_bilinearSobolevEstimates D.J D.χ *
            intervalLength D.A₀ ^ (1 / (2 : ℝ)) *
              (aux_sobolevNormRaw (1 / 2 : ℝ) f₂).toReal) := hmain
    _ = ENNReal.ofReal (C_bilinearSobolevEstimates D.J D.χ) *
        ENNReal.ofReal (intervalLength D.A₀) ^ (1 / (2 : ℝ)) *
          aux_sobolevNormRaw (1 / 2 : ℝ) f₂ := by
      rw [ENNReal.ofReal_mul (mul_nonneg hC (Real.rpow_nonneg hL _)),
        ENNReal.ofReal_mul hC, ← ENNReal.ofReal_rpow_of_nonneg hL (by norm_num),
        ENNReal.ofReal_toReal hrawTop.ne]

/-- Scalar homogeneity of the trilinear absolute form in its middle factor.
This is used only to normalize and then recover the second-dual input in
`normalizedNonlinearSmoothing`. -/
lemma aux_normalized_trilinearFormAbs_smul_middle
    (χ : ℝ → ℝ) (a : ℂ) (f₀ f₁ f₂ : ℝ → ℂ) :
    trilinearFormAbs χ f₀ (a • f₁) f₂ =
      ‖a‖ * trilinearFormAbs χ f₀ f₁ f₂ := by
  unfold trilinearFormAbs trilinearForm
  have hraw : (∫ x : ℝ, ∫ t : ℝ,
      f₀ x * (a • f₁) (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ)) =
        a * ∫ x : ℝ, ∫ t : ℝ,
          f₀ x * f₁ (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hraw, norm_mul]

/-- Dividing the second-dual function by the global size parameter makes it
one-bounded, so that `u2Control` can be applied in
`normalizedNonlinearSmoothing`. -/
lemma aux_normalized_secondDual_scaled_one_bounded
    (D : AdmissibleSupportData) (f₀ f₂ : ℝ → ℂ)
    (hf₀meas : AEStronglyMeasurable f₀ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₀bound : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₀support : ∀ᵐ x ∂volume, x ∉ D.A₀ → f₀ x = 0) :
    let s : ℝ := sizeParameter ![D.A₀, D.A₁, D.A₂, D.J] D.χ
    ∀ᵐ x ∂volume,
      ‖((s : ℂ)⁻¹ • aux_secondDualFunction D.χ f₀ f₂) x‖ ≤ 1 := by
  dsimp
  let s : ℝ := sizeParameter ![D.A₀, D.A₁, D.A₂, D.J] D.χ
  have hs : 2 ≤ s := by
    simpa [s] using aux_two_le_sizeParameter_four D.A₀ D.A₁ D.A₂ D.J D.χ
  have hspos : 0 < s := by linarith
  have hJ : volume.real D.J ≤ s := by
    simpa [s, intervalLength, Measure.real] using
      aux_intervalLength_le_sizeParameter_four D.A₀ D.A₁ D.A₂ D.J D.χ (3 : Fin 4)
  have hF := aux_secondDualFunction_ae_bound D f₀ f₂
    hf₀meas hf₂meas hf₀bound hf₂bound hf₀support
  filter_upwards [hF] with x hx
  change ‖(s : ℂ)⁻¹ * aux_secondDualFunction D.χ f₀ f₂ x‖ ≤ 1
  rw [norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hspos]
  calc
    s⁻¹ * ‖aux_secondDualFunction D.χ f₀ f₂ x‖ =
        ‖aux_secondDualFunction D.χ f₀ f₂ x‖ / s := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ 1 := (div_le_iff₀ hspos).mpr (by simpa using hx.trans hJ)

/-- Recovering the middle factor after normalization by a positive scalar.
This is an algebraic step for `normalizedNonlinearSmoothing`. -/
lemma aux_normalized_recover_scaled_middle
    (χ : ℝ → ℝ) (s : ℝ) (hs : 0 < s) (f₀ f₁ f₂ : ℝ → ℂ) :
    s * trilinearFormAbs χ f₀ ((s : ℂ)⁻¹ • f₁) f₂ =
      trilinearFormAbs χ f₀ f₁ f₂ := by
  rw [aux_normalized_trilinearFormAbs_smul_middle]
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  field_simp

/-- The `ENNReal` form of recovering the middle factor after normalization.
It lets `normalizedNonlinearSmoothing` combine `u2Control` with the second
dualization inequality. -/
lemma aux_normalized_ofReal_recover_scaled_middle
    (χ : ℝ → ℝ) (s : ℝ) (hs : 0 < s) (f₀ f₁ f₂ : ℝ → ℂ) :
    ENNReal.ofReal s *
        ENNReal.ofReal (trilinearFormAbs χ f₀ ((s : ℂ)⁻¹ • f₁) f₂) =
      ENNReal.ofReal (trilinearFormAbs χ f₀ f₁ f₂) := by
  rw [← ENNReal.ofReal_mul hs.le]
  exact congrArg ENNReal.ofReal
    (aux_normalized_recover_scaled_middle χ s hs f₀ f₁ f₂)

/-- Scalar homogeneity of `u²`, stated without a finiteness hypothesis for
the normalization step in `normalizedNonlinearSmoothing`. -/
lemma aux_normalized_uNorm_two_smul (a : ℂ) (f : ℝ → ℂ) :
    uNorm 2 (a • f) = ENNReal.ofReal ‖a‖ * uNorm 2 f := by
  simp only [uNorm]
  rw [aux_fourier_smul, eLpNorm_const_smul]
  simp

/-- Exponent bookkeeping when undoing the global normalization of the
second-dual input in `normalizedNonlinearSmoothing`. -/
lemma aux_normalized_scale_u2_power
    (S U : ℝ≥0∞) (hS : 2 ≤ S) (hStop : S ≠ ∞) :
    S * (S⁻¹ * U) ^ (1 / (160 : ℝ)) =
      S ^ (159 / (160 : ℝ)) * U ^ (1 / (160 : ℝ)) := by
  have hS0 : S ≠ 0 := by
    apply ne_of_gt
    exact lt_of_lt_of_le (by norm_num) hS
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg]
  calc
    S * (S ^ (-(1 / (160 : ℝ))) * U ^ (1 / (160 : ℝ))) =
        (S ^ (1 : ℝ) * S ^ (-(1 / (160 : ℝ)))) * U ^ (1 / (160 : ℝ)) := by
      rw [← mul_assoc]
      rw [ENNReal.rpow_one]
    _ = S ^ ((1 : ℝ) + -(1 / (160 : ℝ))) * U ^ (1 / (160 : ℝ)) := by
      rw [← ENNReal.rpow_add _ _ hS0 hStop]
    _ = S ^ (159 / (160 : ℝ)) * U ^ (1 / (160 : ℝ)) := by norm_num

/-- Applying `u2Control` to the globally normalized second-dual function.
The `u²` estimate supplied as `hU` is inserted only afterwards, which keeps
the degree-lowering and Fourier steps separated for
`normalizedNonlinearSmoothing`. -/
lemma aux_normalized_secondDual_u2_scaled_bound
    (D : AdmissibleSupportData) (f₀ f₂ : ℝ → ℂ)
    (hf₀meas : AEStronglyMeasurable f₀ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₀bound : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₀support : ∀ᵐ x ∂volume, x ∉ D.A₀ → f₀ x = 0)
    (hf₂support : ∀ᵐ x ∂volume, x ∉ D.A₂ → f₂ x = 0)
    (U : ℝ≥0∞)
    (hU : uNorm 2 (aux_secondDualFunction D.χ f₀ f₂) ≤ U) :
    let s : ℝ := sizeParameter ![D.A₀, D.A₁, D.A₂, D.J] D.χ
    let S : ℝ≥0∞ := ENNReal.ofReal s
    ENNReal.ofReal (trilinearFormAbs D.χ f₀
        (aux_secondDualFunction D.χ f₀ f₂) f₂) ≤
      ((64 : ℝ≥0∞) * S ^ (3 : ℝ)) * S ^ (159 / (160 : ℝ)) *
        U ^ (1 / (160 : ℝ)) := by
  dsimp
  let s : ℝ := sizeParameter ![D.A₀, D.A₁, D.A₂, D.J] D.χ
  let S : ℝ≥0∞ := ENNReal.ofReal s
  let F : ℝ → ℂ := aux_secondDualFunction D.χ f₀ f₂
  let G : ℝ → ℂ := ((s : ℂ)⁻¹) • F
  have hs : 2 ≤ s := by
    simpa [s] using aux_two_le_sizeParameter_four D.A₀ D.A₁ D.A₂ D.J D.χ
  have hspos : 0 < s := by linarith
  have hS : (2 : ℝ≥0∞) ≤ S := by
    simpa [S] using ENNReal.ofReal_le_ofReal hs
  have hStop : S ≠ ∞ := by exact ENNReal.ofReal_ne_top
  have hFdata := aux_secondDualFunction_memLp_and_support D f₀ f₂
    hf₀meas hf₂meas hf₀bound hf₂bound hf₀support
  have hGmeas : AEStronglyMeasurable G volume := by
    exact hFdata.2.aestronglyMeasurable.const_smul _
  have hGone : ∀ᵐ x ∂volume, ‖G x‖ ≤ 1 := by
    simpa [G, F, s] using aux_normalized_secondDual_scaled_one_bounded D f₀ f₂
      hf₀meas hf₂meas hf₀bound hf₂bound hf₀support
  have hGsupport : ∀ᵐ x ∂volume, x ∉ D.A₁ → G x = 0 := by
    filter_upwards [hFdata.1] with x hx hnot
    simp [G, F, hx hnot]
  have hu2 := u2Control D f₀ G f₂ hf₀meas hGmeas hf₂meas
    hf₀bound hGone hf₂bound hf₀support hGsupport hf₂support
  have hGnorm : uNorm 2 G = S⁻¹ * uNorm 2 F := by
    dsimp [G]
    rw [aux_normalized_uNorm_two_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hspos, ENNReal.ofReal_inv_of_pos hspos]
  have hu2' : ENNReal.ofReal (trilinearFormAbs D.χ f₀ G f₂) ≤
      ENNReal.ofReal (C_u2Control D.A₀ D.A₁ D.A₂ D.J D.χ) *
        (S⁻¹ * U) ^ (1 / (160 : ℝ)) := by
    calc
      ENNReal.ofReal (trilinearFormAbs D.χ f₀ G f₂) ≤
          ENNReal.ofReal (C_u2Control D.A₀ D.A₁ D.A₂ D.J D.χ) *
            (S⁻¹ * uNorm 2 F) ^ (1 / (160 : ℝ)) := by
        simpa [hGnorm] using hu2
      _ ≤ ENNReal.ofReal (C_u2Control D.A₀ D.A₁ D.A₂ D.J D.χ) *
            (S⁻¹ * U) ^ (1 / (160 : ℝ)) := by gcongr
  have hrecover : S * ENNReal.ofReal (trilinearFormAbs D.χ f₀ G f₂) =
      ENNReal.ofReal (trilinearFormAbs D.χ f₀ F f₂) := by
    simpa [S, G, F, s] using
      aux_normalized_ofReal_recover_scaled_middle D.χ s hspos f₀ F f₂
  have hC : ENNReal.ofReal (C_u2Control D.A₀ D.A₁ D.A₂ D.J D.χ) =
      (64 : ℝ≥0∞) * S ^ (3 : ℝ) := by
    unfold C_u2Control
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (le_of_lt hspos)]
    norm_num [S, ENNReal.rpow_natCast]
  calc
    ENNReal.ofReal (trilinearFormAbs D.χ f₀ F f₂) =
        S * ENNReal.ofReal (trilinearFormAbs D.χ f₀ G f₂) := hrecover.symm
    _ ≤ S * (ENNReal.ofReal (C_u2Control D.A₀ D.A₁ D.A₂ D.J D.χ) *
          (S⁻¹ * U) ^ (1 / (160 : ℝ))) := by gcongr
    _ = ((64 : ℝ≥0∞) * S ^ (3 : ℝ)) * S ^ (159 / (160 : ℝ)) *
          U ^ (1 / (160 : ℝ)) := by
      rw [show S * (ENNReal.ofReal (C_u2Control D.A₀ D.A₁ D.A₂ D.J D.χ) *
          (S⁻¹ * U) ^ (1 / (160 : ℝ))) =
          ENNReal.ofReal (C_u2Control D.A₀ D.A₁ D.A₂ D.J D.χ) *
            (S * (S⁻¹ * U) ^ (1 / (160 : ℝ))) by ring,
        hC, aux_normalized_scale_u2_power S U hS hStop]
      ring

/-- Square-root bookkeeping for the normalized `u²` estimate, ready for
the Cauchy--Schwarz conclusion of `secondDualization`. -/
lemma aux_normalized_secondDual_u2_scaled_root (S U : ℝ≥0∞) :
    (((64 : ℝ≥0∞) * S ^ (3 : ℝ)) * S ^ (159 / (160 : ℝ)) *
      U ^ (1 / (160 : ℝ))) ^ (1 / (2 : ℝ)) =
      S ^ (159 / (320 : ℝ)) * ((64 : ℝ≥0∞) * S ^ (3 : ℝ)) ^
        (1 / (2 : ℝ)) * U ^ (1 / (320 : ℝ)) := by
  rw [show ((64 : ℝ≥0∞) * S ^ (3 : ℝ)) * S ^ (159 / (160 : ℝ)) *
      U ^ (1 / (160 : ℝ)) =
      (((64 : ℝ≥0∞) * S ^ (3 : ℝ)) * S ^ (159 / (160 : ℝ))) *
        U ^ (1 / (160 : ℝ)) by ring,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  congr 1 <;> ring_nf

/-- This combines `secondDualization` with the normalized `u²` estimate.
The Fourier-side `u²` bound remains an explicit hypothesis so it can be
proved and size-reduced separately for `normalizedNonlinearSmoothing`. -/
lemma aux_normalized_chain_from_fourier
    (D : AdmissibleSupportData) (f₀ f₁ f₂ : ℝ → ℂ)
    (hf₀meas : AEStronglyMeasurable f₀ volume)
    (hf₁meas : AEStronglyMeasurable f₁ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₀bound : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₁bound : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₀support : ∀ᵐ x ∂volume, x ∉ D.A₀ → f₀ x = 0)
    (hf₁support : ∀ᵐ x ∂volume, x ∉ D.A₁ → f₁ x = 0)
    (hf₂support : ∀ᵐ x ∂volume, x ∉ D.A₂ → f₂ x = 0)
    (hFourier :
      let s : ℝ := sizeParameter ![D.A₀, D.A₁, D.A₂, D.J] D.χ
      let S : ℝ≥0∞ := ENNReal.ofReal s
      uNorm 2 (aux_secondDualFunction D.χ f₀ f₂) ≤
        (32 : ℝ≥0∞) * S ^ (3 : ℝ) * aux_sobolevNormRaw (1 / 2 : ℝ) f₂) :
    let s : ℝ := sizeParameter ![D.A₀, D.A₁, D.A₂, D.J] D.χ
    let S : ℝ≥0∞ := ENNReal.ofReal s
    let H : ℝ≥0∞ := aux_sobolevNormRaw (1 / 2 : ℝ) f₂
    ENNReal.ofReal (trilinearFormAbs D.χ f₀ f₁ f₂) ≤
      S ^ (1 / (2 : ℝ)) * S ^ (159 / (320 : ℝ)) *
        (((64 : ℝ≥0∞) * S ^ (3 : ℝ)) ^ (1 / (2 : ℝ))) *
          ((32 : ℝ≥0∞) * S ^ (3 : ℝ) * H) ^ (1 / (320 : ℝ)) := by
  dsimp
  let s : ℝ := sizeParameter ![D.A₀, D.A₁, D.A₂, D.J] D.χ
  let S : ℝ≥0∞ := ENNReal.ofReal s
  let H : ℝ≥0∞ := aux_sobolevNormRaw (1 / 2 : ℝ) f₂
  let F : ℝ → ℂ := aux_secondDualFunction D.χ f₀ f₂
  have hs : 2 ≤ s := by
    simpa [s] using aux_two_le_sizeParameter_four D.A₀ D.A₁ D.A₂ D.J D.χ
  have hS : (2 : ℝ≥0∞) ≤ S := by
    simpa [S] using ENNReal.ofReal_le_ofReal hs
  have hA₁ : intervalLength D.A₁ ≤ s := by
    simpa [s] using aux_intervalLength_le_sizeParameter_four
      D.A₀ D.A₁ D.A₂ D.J D.χ (1 : Fin 4)
  have hA₁ENN : ENNReal.ofReal (intervalLength D.A₁) ≤ S := by
    simpa [S] using ENNReal.ofReal_le_ofReal hA₁
  have hA₁root : ENNReal.ofReal (intervalLength D.A₁) ^ (1 / (2 : ℝ)) ≤
      S ^ (1 / (2 : ℝ)) :=
    ENNReal.rpow_le_rpow hA₁ENN (by positivity)
  have hsecond := secondDualization D f₀ f₁ f₂
    hf₀meas hf₁meas hf₂meas hf₀bound hf₁bound hf₂bound
    hf₀support hf₁support hf₂support
  have hsecondENN : ENNReal.ofReal (trilinearFormAbs D.χ f₀ f₁ f₂) ≤
      ENNReal.ofReal (intervalLength D.A₁) ^ (1 / (2 : ℝ)) *
        ENNReal.ofReal (trilinearFormAbs D.χ f₀ F f₂) ^ (1 / (2 : ℝ)) := by
    calc
      ENNReal.ofReal (trilinearFormAbs D.χ f₀ f₁ f₂) ≤
          ENNReal.ofReal (intervalLength D.A₁ ^ (1 / (2 : ℝ)) *
            trilinearFormAbs D.χ f₀ F f₂ ^ (1 / (2 : ℝ))) :=
        ENNReal.ofReal_le_ofReal (by simpa [F] using hsecond.2)
      _ = ENNReal.ofReal (intervalLength D.A₁) ^ (1 / (2 : ℝ)) *
          ENNReal.ofReal (trilinearFormAbs D.χ f₀ F f₂) ^ (1 / (2 : ℝ)) := by
        have hlen0 : 0 ≤ intervalLength D.A₁ := ENNReal.toReal_nonneg
        have hform0 : 0 ≤ trilinearFormAbs D.χ f₀ F f₂ := norm_nonneg _
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hlen0 _),
          ← ENNReal.ofReal_rpow_of_nonneg hlen0 (by positivity),
          ← ENNReal.ofReal_rpow_of_nonneg hform0 (by positivity)]
  have hF := aux_normalized_secondDual_u2_scaled_bound D f₀ f₂
    hf₀meas hf₂meas hf₀bound hf₂bound hf₀support hf₂support
    ((32 : ℝ≥0∞) * S ^ (3 : ℝ) * H) (by simpa [s, S, H] using hFourier)
  have hFroot : ENNReal.ofReal (trilinearFormAbs D.χ f₀ F f₂) ^
      (1 / (2 : ℝ)) ≤
      (((64 : ℝ≥0∞) * S ^ (3 : ℝ)) * S ^ (159 / (160 : ℝ)) *
        ((32 : ℝ≥0∞) * S ^ (3 : ℝ) * H) ^ (1 / (160 : ℝ))) ^
          (1 / (2 : ℝ)) := by
    apply ENNReal.rpow_le_rpow
    · simpa [F, s, S, H] using hF
    · positivity
  calc
    ENNReal.ofReal (trilinearFormAbs D.χ f₀ f₁ f₂) ≤
        ENNReal.ofReal (intervalLength D.A₁) ^ (1 / (2 : ℝ)) *
          ENNReal.ofReal (trilinearFormAbs D.χ f₀ F f₂) ^ (1 / (2 : ℝ)) := hsecondENN
    _ ≤ ENNReal.ofReal (intervalLength D.A₁) ^ (1 / (2 : ℝ)) *
        ((((64 : ℝ≥0∞) * S ^ (3 : ℝ)) * S ^ (159 / (160 : ℝ)) *
          ((32 : ℝ≥0∞) * S ^ (3 : ℝ) * H) ^ (1 / (160 : ℝ))) ^
            (1 / (2 : ℝ))) := by
      gcongr
    _ = ENNReal.ofReal (intervalLength D.A₁) ^ (1 / (2 : ℝ)) *
        (S ^ (159 / (320 : ℝ)) * ((64 : ℝ≥0∞) * S ^ (3 : ℝ)) ^
          (1 / (2 : ℝ)) * ((32 : ℝ≥0∞) * S ^ (3 : ℝ) * H) ^
            (1 / (320 : ℝ))) := by
      rw [aux_normalized_secondDual_u2_scaled_root]
    _ ≤ S ^ (1 / (2 : ℝ)) *
        (S ^ (159 / (320 : ℝ)) * ((64 : ℝ≥0∞) * S ^ (3 : ℝ)) ^
          (1 / (2 : ℝ)) * ((32 : ℝ≥0∞) * S ^ (3 : ℝ) * H) ^
            (1 / (320 : ℝ))) := by
      gcongr
    _ = S ^ (1 / (2 : ℝ)) * S ^ (159 / (320 : ℝ)) *
        (((64 : ℝ≥0∞) * S ^ (3 : ℝ)) ^ (1 / (2 : ℝ))) *
          ((32 : ℝ≥0∞) * S ^ (3 : ℝ) * H) ^ (1 / (320 : ℝ)) := by ring

/-- A safe global-size version of the Fourier estimate for the second-dual
`u²` norm.  It is the Fourier input consumed by
`aux_normalized_chain_from_fourier`. -/
lemma aux_normalized_secondDual_uNorm_two_size_bound
    (D : AdmissibleSupportData) (f₀ f₂ : ℝ → ℂ)
    (hf₀meas : AEStronglyMeasurable f₀ volume)
    (hf₂meas : AEStronglyMeasurable f₂ volume)
    (hf₀bound : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₂bound : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₀support : ∀ᵐ x ∂volume, x ∉ D.A₀ → f₀ x = 0)
    (hf₂support : ∀ᵐ x ∂volume, x ∉ D.A₂ → f₂ x = 0) :
    let s : ℝ := sizeParameter ![D.A₀, D.A₁, D.A₂, D.J] D.χ
    let S : ℝ≥0∞ := ENNReal.ofReal s
    uNorm 2 (aux_secondDualFunction D.χ f₀ f₂) ≤
      (32 : ℝ≥0∞) * S ^ (3 : ℝ) * aux_sobolevNormRaw (1 / 2 : ℝ) f₂ := by
  dsimp
  let s : ℝ := sizeParameter ![D.A₀, D.A₁, D.A₂, D.J] D.χ
  let S : ℝ≥0∞ := ENNReal.ofReal s
  have hs : 2 ≤ s := by
    simpa [s] using aux_two_le_sizeParameter_four D.A₀ D.A₁ D.A₂ D.J D.χ
  have hspos : 0 < s := by linarith
  have hS : (2 : ℝ≥0∞) ≤ S := by
    simpa [S] using ENNReal.ofReal_le_ofReal hs
  have hSone : (1 : ℝ≥0∞) ≤ S := le_trans (by norm_num) hS
  have hSzero : S ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hS)
  have hsizeJ : sizeParameter ![D.J] D.χ ≤ s := by
    simpa [s] using aux_u2_sizeParameter_singleton_le_four
      D.A₀ D.A₁ D.A₂ D.J D.χ
  have hsizeJ0 : 0 ≤ sizeParameter ![D.J] D.χ := by
    unfold sizeParameter
    positivity
  have hCb : C_bilinearSobolevEstimates D.J D.χ ≤ 32 * s ^ (2 : ℕ) := by
    unfold C_bilinearSobolevEstimates
    norm_num
    gcongr
  have hCbENN : ENNReal.ofReal (C_bilinearSobolevEstimates D.J D.χ) ≤
      (32 : ℝ≥0∞) * S ^ (2 : ℝ) := by
    calc
      ENNReal.ofReal (C_bilinearSobolevEstimates D.J D.χ) ≤
          ENNReal.ofReal (32 * s ^ (2 : ℕ)) := ENNReal.ofReal_le_ofReal hCb
      _ = (32 : ℝ≥0∞) * S ^ (2 : ℝ) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (le_of_lt hspos)]
        norm_num [S, ENNReal.rpow_natCast]
  have hA₀ : intervalLength D.A₀ ≤ s := by
    simpa [s] using aux_intervalLength_le_sizeParameter_four
      D.A₀ D.A₁ D.A₂ D.J D.χ (0 : Fin 4)
  have hA₀ENN : ENNReal.ofReal (intervalLength D.A₀) ≤ S := by
    simpa [S] using ENNReal.ofReal_le_ofReal hA₀
  have hA₀root : ENNReal.ofReal (intervalLength D.A₀) ^ (1 / (2 : ℝ)) ≤ S := by
    calc
      ENNReal.ofReal (intervalLength D.A₀) ^ (1 / (2 : ℝ)) ≤
          S ^ (1 / (2 : ℝ)) := ENNReal.rpow_le_rpow hA₀ENN (by positivity)
      _ ≤ S ^ (1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le hSone (by norm_num)
      _ = S := ENNReal.rpow_one S
  have hraw := aux_normalized_secondDual_uNorm_two_bound D f₀ f₂
    hf₀meas hf₂meas hf₀bound hf₂bound hf₀support hf₂support
  calc
    uNorm 2 (aux_secondDualFunction D.χ f₀ f₂) ≤
        ENNReal.ofReal (C_bilinearSobolevEstimates D.J D.χ) *
          ENNReal.ofReal (intervalLength D.A₀) ^ (1 / (2 : ℝ)) *
            aux_sobolevNormRaw (1 / 2 : ℝ) f₂ := hraw
    _ ≤ ((32 : ℝ≥0∞) * S ^ (2 : ℝ)) * S *
          aux_sobolevNormRaw (1 / 2 : ℝ) f₂ := by
      gcongr
    _ = (32 : ℝ≥0∞) * S ^ (3 : ℝ) *
          aux_sobolevNormRaw (1 / 2 : ℝ) f₂ := by
      have hpow : S ^ (2 : ℝ) * S = S ^ (3 : ℝ) := by
        calc
          S ^ (2 : ℝ) * S = S ^ (2 : ℝ) * S ^ (1 : ℝ) := by
            rw [ENNReal.rpow_one]
          _ = S ^ ((2 : ℝ) + 1) :=
            (ENNReal.rpow_add _ _ hSzero ENNReal.ofReal_ne_top).symm
          _ = S ^ (3 : ℝ) := by norm_num
      calc
        (32 : ℝ≥0∞) * S ^ (2 : ℝ) * S *
            aux_sobolevNormRaw (1 / 2 : ℝ) f₂ =
            32 * (S ^ (2 : ℝ) * S) * aux_sobolevNormRaw (1 / 2 : ℝ) f₂ := by ring
        _ = _ := by rw [hpow]

/-- Numerical endgame for `normalizedNonlinearSmoothing` after the
second-dual, `u²`, and Fourier estimates have been assembled. -/
lemma aux_normalized_numerical_endgame_S3
    (I S H : ℝ≥0∞) (hS : 2 ≤ S)
    (hchain : I ≤
      S ^ (1 / (2 : ℝ)) * S ^ (159 / (320 : ℝ)) *
        (((64 : ℝ≥0∞) * S ^ (3 : ℝ)) ^ (1 / (2 : ℝ))) *
          (((32 : ℝ≥0∞) * S ^ (3 : ℝ) * H) ^ (1 / (320 : ℝ)))) :
    I ≤ (64 : ℝ≥0∞) * S ^ (3 : ℝ) * H ^ (1 / (320 : ℝ)) := by
  by_cases hHzero : H = 0
  · subst H
    simpa using hchain
  by_cases hStop : S = ∞
  · subst S
    simp [hHzero]
  have hSone : 1 ≤ S := by
    exact le_trans (by norm_num) hS
  have hSzero : S ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hS)
  have hSfin : S ≠ ∞ := hStop
  have hC64 : ((64 : ℝ≥0∞) * S ^ (3 : ℝ)) ^ (1 / (2 : ℝ)) =
      (64 : ℝ≥0∞) ^ (1 / (2 : ℝ)) * S ^ (3 / (2 : ℝ)) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
    congr 1
    ring_nf
  have hBH : ((32 : ℝ≥0∞) * S ^ (3 : ℝ) * H) ^ (1 / (320 : ℝ)) =
      (32 : ℝ≥0∞) ^ (1 / (320 : ℝ)) * S ^ (3 / (320 : ℝ)) *
        H ^ (1 / (320 : ℝ)) := by
    rw [show (32 : ℝ≥0∞) * S ^ (3 : ℝ) * H =
        ((32 : ℝ≥0∞) * S ^ (3 : ℝ)) * H by ring,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ← ENNReal.rpow_mul]
    rw [show (3 : ℝ) * (1 / 320 : ℝ) = 3 / 320 by ring]
  apply hchain.trans
  rw [hC64, hBH]
  have h64half : (64 : ℝ≥0∞) ^ (1 / (2 : ℝ)) ≤ 8 := by
    calc
      (64 : ℝ≥0∞) ^ (1 / (2 : ℝ)) ≤
          ((2 : ℝ≥0∞) ^ (6 : ℕ)) ^ (1 / (2 : ℝ)) := by
        apply ENNReal.rpow_le_rpow
        · norm_num
        · norm_num
      _ = (2 : ℝ≥0∞) ^ (3 : ℝ) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        congr 1
        ring
      _ = 8 := by norm_num [← ENNReal.rpow_natCast]
  have h32small : (32 : ℝ≥0∞) ^ (1 / (320 : ℝ)) ≤ 2 := by
    calc
      (32 : ℝ≥0∞) ^ (1 / (320 : ℝ)) ≤
          ((2 : ℝ≥0∞) ^ (5 : ℕ)) ^ (1 / (320 : ℝ)) := by
        apply ENNReal.rpow_le_rpow
        · norm_num
        · norm_num
      _ = (2 : ℝ≥0∞) ^ (5 / (320 : ℝ)) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        congr 1
        ring
      _ ≤ (2 : ℝ≥0∞) ^ (1 : ℝ) := by
        apply ENNReal.rpow_le_rpow_of_exponent_le
        · norm_num
        · norm_num
      _ = 2 := by norm_num
  have hcoeff : (64 : ℝ≥0∞) ^ (1 / (2 : ℝ)) *
      (32 : ℝ≥0∞) ^ (1 / (320 : ℝ)) ≤ 16 := by
    calc
      (64 : ℝ≥0∞) ^ (1 / (2 : ℝ)) *
          (32 : ℝ≥0∞) ^ (1 / (320 : ℝ)) ≤ 8 * 2 := by
        gcongr
      _ = 16 := by norm_num
  have hSpow : S ^ (1 / (2 : ℝ)) * S ^ (159 / (320 : ℝ)) *
      S ^ (3 / (2 : ℝ)) * S ^ (3 / (320 : ℝ)) =
        S ^ (802 / (320 : ℝ)) := by
    rw [← ENNReal.rpow_add _ _ hSzero hSfin,
      ← ENNReal.rpow_add _ _ hSzero hSfin,
      ← ENNReal.rpow_add _ _ hSzero hSfin]
    congr 1
    ring
  have hSpow_le : S ^ (1 / (2 : ℝ)) * S ^ (159 / (320 : ℝ)) *
      S ^ (3 / (2 : ℝ)) * S ^ (3 / (320 : ℝ)) ≤ S ^ (3 : ℝ) := by
    rw [hSpow]
    apply ENNReal.rpow_le_rpow_of_exponent_le hSone
    norm_num
  calc
    S ^ (1 / (2 : ℝ)) * S ^ (159 / (320 : ℝ)) *
        ((64 : ℝ≥0∞) ^ (1 / (2 : ℝ)) * S ^ (3 / (2 : ℝ))) *
          ((32 : ℝ≥0∞) ^ (1 / (320 : ℝ)) * S ^ (3 / (320 : ℝ)) *
            H ^ (1 / (320 : ℝ))) =
        ((64 : ℝ≥0∞) ^ (1 / (2 : ℝ)) *
          (32 : ℝ≥0∞) ^ (1 / (320 : ℝ))) *
          (S ^ (1 / (2 : ℝ)) * S ^ (159 / (320 : ℝ)) *
            S ^ (3 / (2 : ℝ)) * S ^ (3 / (320 : ℝ))) *
            H ^ (1 / (320 : ℝ)) := by ring
    _ ≤ 64 * S ^ (3 : ℝ) * H ^ (1 / (320 : ℝ)) := by
      calc
        ((64 : ℝ≥0∞) ^ (1 / (2 : ℝ)) *
            (32 : ℝ≥0∞) ^ (1 / (320 : ℝ))) *
            (S ^ (1 / (2 : ℝ)) * S ^ (159 / (320 : ℝ)) *
              S ^ (3 / (2 : ℝ)) * S ^ (3 / (320 : ℝ))) *
              H ^ (1 / (320 : ℝ)) ≤
            16 * S ^ (3 : ℝ) * H ^ (1 / (320 : ℝ)) := by
          gcongr
        _ ≤ 64 * S ^ (3 : ℝ) * H ^ (1 / (320 : ℝ)) := by
          gcongr; norm_num

/-- The constant in \(\label{thm:normalized-smoothing}\), used by
`normalizedNonlinearSmoothing`:
\[
C_{\ref{thm:normalized-smoothing},\,A_0,A_1,A_2,J,\chi}
:=
2^6\Ssize{A_0,A_1,A_2,J}{\chi}^{3}.
\]
-/
def C_normalizedNonlinearSmoothing (A₀ A₁ A₂ J : Set ℝ) (χ : ℝ → ℝ) : ℝ :=
  (2 : ℝ) ^ 6 * sizeParameter ![A₀, A₁, A₂, J] χ ^ 3

/--
Let \(\mathfrak D=(A_0,A_1,A_2,J,\chi)\) be admissible. Define
\[
C_{\ref{thm:normalized-smoothing},\,A_0,A_1,A_2,J,\chi}
:=
2^6\Ssize{A_0,A_1,A_2,J}{\chi}^{3}.
\]
If \(f_0,f_1,f_2\) are \(1\)-bounded and supported in
\(A_0,A_1,A_2\), respectively, then
\[
\Ichi(f_0,f_1,f_2)
\leq
C_{\ref{thm:normalized-smoothing},\,A_0,A_1,A_2,J,\chi}
\hNorm{f_2}{-1/2}^{1/320}.
\]
-/
theorem normalizedNonlinearSmoothing
    (D : AdmissibleSupportData) (f₀ f₁ f₂ : ℝ → ℂ)
    (hf₀_measurable : AEStronglyMeasurable f₀ volume)
    (hf₁_measurable : AEStronglyMeasurable f₁ volume)
    (hf₂_measurable : AEStronglyMeasurable f₂ volume)
    (hf₀_one_bounded : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ 1)
    (hf₁_one_bounded : ∀ᵐ x ∂volume, ‖f₁ x‖ ≤ 1)
    (hf₂_one_bounded : ∀ᵐ x ∂volume, ‖f₂ x‖ ≤ 1)
    (hf₀_support : ∀ᵐ x ∂volume, x ∉ D.A₀ → f₀ x = 0)
    (hf₁_support : ∀ᵐ x ∂volume, x ∉ D.A₁ → f₁ x = 0)
    (hf₂_support : ∀ᵐ x ∂volume, x ∉ D.A₂ → f₂ x = 0) :
    ENNReal.ofReal (trilinearFormAbs D.χ f₀ f₁ f₂) ≤
      ENNReal.ofReal (C_normalizedNonlinearSmoothing D.A₀ D.A₁ D.A₂ D.J D.χ) *
        aux_sobolevNormRaw (1 / 2 : ℝ) f₂ ^ (1 / (320 : ℝ)) := by
  let s : ℝ := sizeParameter ![D.A₀, D.A₁, D.A₂, D.J] D.χ
  let S : ℝ≥0∞ := ENNReal.ofReal s
  let H : ℝ≥0∞ := aux_sobolevNormRaw (1 / 2 : ℝ) f₂
  have hs : 2 ≤ s := by
    simpa [s] using aux_two_le_sizeParameter_four D.A₀ D.A₁ D.A₂ D.J D.χ
  have hspos : 0 < s := by linarith
  have hS : (2 : ℝ≥0∞) ≤ S := by
    simpa [S] using ENNReal.ofReal_le_ofReal hs
  have hFourier := aux_normalized_secondDual_uNorm_two_size_bound D f₀ f₂
    hf₀_measurable hf₂_measurable hf₀_one_bounded hf₂_one_bounded
    hf₀_support hf₂_support
  have hchain := aux_normalized_chain_from_fourier D f₀ f₁ f₂
    hf₀_measurable hf₁_measurable hf₂_measurable
    hf₀_one_bounded hf₁_one_bounded hf₂_one_bounded
    hf₀_support hf₁_support hf₂_support
    (by simpa [s, S, H] using hFourier)
  have hnum := aux_normalized_numerical_endgame_S3
    (ENNReal.ofReal (trilinearFormAbs D.χ f₀ f₁ f₂)) S H hS
    (by simpa [s, S, H] using hchain)
  have hC : ENNReal.ofReal
      (C_normalizedNonlinearSmoothing D.A₀ D.A₁ D.A₂ D.J D.χ) =
      (64 : ℝ≥0∞) * S ^ (3 : ℝ) := by
    unfold C_normalizedNonlinearSmoothing
    rw [ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_pow (le_of_lt hspos)]
    norm_num [s, S, ENNReal.rpow_natCast]
  calc
    ENNReal.ofReal (trilinearFormAbs D.χ f₀ f₁ f₂) ≤
        (64 : ℝ≥0∞) * S ^ (3 : ℝ) * H ^ (1 / (320 : ℝ)) := hnum
    _ = ENNReal.ofReal (C_normalizedNonlinearSmoothing D.A₀ D.A₁ D.A₂ D.J D.χ) *
        aux_sobolevNormRaw (1 / 2 : ℝ) f₂ ^ (1 / (320 : ℝ)) := by
      rw [← hC]

/-- A finite `L∞` norm bounds the function almost everywhere in ordinary norm. -/
lemma aux_homogeneous_ae_norm_le_toReal
    (f : ℝ → ℂ) (hf : MemLp f (∞ : ℝ≥0∞) volume) :
    ∀ᵐ x : ℝ ∂volume, ‖f x‖ ≤ (eLpNorm f (∞ : ℝ≥0∞) volume).toReal := by
  have htop : eLpNorm f (∞ : ℝ≥0∞) volume ≠ ∞ := hf.eLpNorm_ne_top
  have hbound : ∀ᵐ x : ℝ ∂volume, ‖f x‖ₑ ≤ eLpNorm f (∞ : ℝ≥0∞) volume := by
    simpa only [eLpNorm_exponent_top] using
      (MeasureTheory.ae_le_eLpNormEssSup (f := f) (μ := volume))
  filter_upwards [hbound] with x hx
  have hx' : ENNReal.ofReal ‖f x‖ ≤ eLpNorm f (∞ : ℝ≥0∞) volume := by
    simpa only [ofReal_norm] using hx
  have hx'' := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top htop).mpr hx'
  simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using hx''

/-- Normalization by a positive finite `L∞` norm produces a one-bounded input. -/
lemma aux_homogeneous_normalized_one_bounded
    (f : ℝ → ℂ) (hf : MemLp f (∞ : ℝ≥0∞) volume)
    (hzero : eLpNorm f (∞ : ℝ≥0∞) volume ≠ 0) :
    ∀ᵐ x : ℝ ∂volume,
      ‖(((eLpNorm f (∞ : ℝ≥0∞) volume).toReal)⁻¹ : ℂ) • f x‖ ≤ 1 := by
  let B : ℝ≥0∞ := eLpNorm f (∞ : ℝ≥0∞) volume
  let b : ℝ := B.toReal
  have hBtop : B ≠ ∞ := by
    exact hf.eLpNorm_ne_top
  have hbpos : 0 < b := by
    exact ENNReal.toReal_pos hzero hBtop
  have hbound := aux_homogeneous_ae_norm_le_toReal f hf
  change ∀ᵐ x : ℝ ∂volume, ‖(b⁻¹ : ℂ) • f x‖ ≤ 1
  filter_upwards [hbound] with x hx
  rw [smul_eq_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hbpos]
  rw [← div_eq_inv_mul, div_le_iff₀ hbpos]
  simpa [B, b] using hx

/-- If any input is zero almost everywhere, the trilinear absolute form vanishes. -/
lemma aux_homogeneous_trilinearFormAbs_eq_zero_of_ae_zero
    (χ : ℝ → ℝ) (f₀ f₁ f₂ : ℝ → ℂ)
    (hzero : f₀ =ᵐ[volume] 0 ∨ f₁ =ᵐ[volume] 0 ∨ f₂ =ᵐ[volume] 0) :
    trilinearFormAbs χ f₀ f₁ f₂ = 0 := by
  have hkernel : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      aux_u3_trilinearIntegrand f₀ f₁ f₂ χ z = 0 := by
    rcases hzero with h₀ | hrest
    · have h₀' : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, f₀ z.1 = 0 :=
        (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).tendsto_ae h₀
      filter_upwards [h₀'] with z hz
      simp [aux_u3_trilinearIntegrand, hz]
    · rcases hrest with h₁ | h₂
      · have h₁' : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
            f₁ (z.1 + 1 * z.2) = 0 :=
          (aux_quasiMeasurePreserving_affine 1).tendsto_ae h₁
        have h₁'' : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
            f₁ (z.1 + z.2) = 0 := by
          simpa only [one_mul] using h₁'
        filter_upwards [h₁''] with z hz
        simp [aux_u3_trilinearIntegrand, hz]
      · have h₂' : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
            f₂ (z.1 + z.2 ^ 2) = 0 := aux_u3_qmp_add_sq.tendsto_ae h₂
        filter_upwards [h₂'] with z hz
        simp [aux_u3_trilinearIntegrand, hz]
  have hsections : ∀ᵐ x : ℝ ∂volume, ∀ᵐ t : ℝ ∂volume,
      aux_u3_trilinearIntegrand f₀ f₁ f₂ χ (x, t) = 0 :=
    Measure.ae_ae_of_ae_prod hkernel
  unfold trilinearFormAbs trilinearForm
  apply norm_eq_zero.mpr
  apply integral_eq_zero_of_ae
  filter_upwards [hsections] with x hx
  apply integral_eq_zero_of_ae
  filter_upwards [hx] with t ht
  simpa [aux_u3_trilinearIntegrand] using ht

/-- Scalar homogeneity of the trilinear absolute form in the last factor. -/
lemma aux_homogeneous_trilinearFormAbs_smul_last
    (χ : ℝ → ℝ) (a : ℂ) (f₀ f₁ f₂ : ℝ → ℂ) :
    trilinearFormAbs χ f₀ f₁ (a • f₂) =
      ‖a‖ * trilinearFormAbs χ f₀ f₁ f₂ := by
  unfold trilinearFormAbs trilinearForm
  have hraw : (∫ x : ℝ, ∫ t : ℝ,
      f₀ x * f₁ (x + t) * (a • f₂) (x + t ^ 2) * (χ t : ℂ)) =
        a * ∫ x : ℝ, ∫ t : ℝ,
          f₀ x * f₁ (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hraw, norm_mul]

/-- Scalar homogeneity of the trilinear absolute form in all three inputs. -/
lemma aux_homogeneous_trilinearFormAbs_smul_all
    (χ : ℝ → ℝ) (a₀ a₁ a₂ : ℂ) (f₀ f₁ f₂ : ℝ → ℂ) :
    trilinearFormAbs χ (a₀ • f₀) (a₁ • f₁) (a₂ • f₂) =
      ‖a₀‖ * ‖a₁‖ * ‖a₂‖ * trilinearFormAbs χ f₀ f₁ f₂ := by
  rw [aux_u2_trilinearFormAbs_smul_first,
    aux_normalized_trilinearFormAbs_smul_middle,
    aux_homogeneous_trilinearFormAbs_smul_last]
  ring

/-- The raw Sobolev quantity is homogeneous under a scalar when its input is `L²`. -/
lemma aux_homogeneous_sobolevNormRaw_smul
    (σ : ℝ) (a : ℂ) (f : ℝ → ℂ) (hf : MemLp f (2 : ℝ≥0∞) volume) :
    aux_sobolevNormRaw σ (a • f) =
      ENNReal.ofReal ‖a‖ * aux_sobolevNormRaw σ f := by
  rw [aux_sobolevDifference_sobolevNormRaw_eq_sobolevNorm σ (a • f)
      (hf.const_smul a),
    aux_sobolevDifference_sobolevNormRaw_eq_sobolevNorm σ f hf]
  let G : Lp (α := ℝ) ℂ 2 volume := (hf.const_smul a).toLp (a • f)
  let F : Lp (α := ℝ) ℂ 2 volume := hf.toLp f
  have hGF : G = a • F := MemLp.toLp_const_smul a hf
  change sobolevNorm σ G = ENNReal.ofReal ‖a‖ * sobolevNorm σ F
  unfold sobolevNorm
  let FF : Lp (α := ℝ) ℂ 2 volume := Lp.fourierTransformₗᵢ ℝ ℂ F
  have hFourier : Lp.fourierTransformₗᵢ ℝ ℂ G = a • FF := by
    rw [hGF]
    exact ContinuousLinearEquiv.map_smul _ _ _
  rw [hFourier]
  have hF : (↑↑(a • FF) : ℝ → ℂ) =ᵐ[volume] a • (↑↑FF : ℝ → ℂ) :=
    Lp.coeFn_smul a FF
  have heq :
      (fun ξ : ℝ ↦ (japaneseBracket ξ ^ (-σ)) • (a • FF) ξ) =ᵐ[volume]
        a • (fun ξ : ℝ ↦ (japaneseBracket ξ ^ (-σ)) • FF ξ) := by
    filter_upwards [hF] with ξ hξ
    change (japaneseBracket ξ ^ (-σ)) • (a • FF) ξ =
      a • ((japaneseBracket ξ ^ (-σ)) • FF ξ)
    rw [hξ]
    change ((japaneseBracket ξ ^ (-σ) : ℝ) : ℂ) * (a * FF ξ) =
      a * (((japaneseBracket ξ ^ (-σ) : ℝ) : ℂ) * FF ξ)
    ring
  rw [eLpNorm_congr_ae heq, eLpNorm_const_smul]
  simp [FF, ← ofReal_norm]

/-- Algebraic Sobolev exponent bookkeeping for homogeneous normalization. -/
lemma aux_homogeneous_sobolev_power
    (B H : ℝ≥0∞) (hBzero : B ≠ 0) (hBtop : B ≠ ∞) :
    B * H ^ (1 / (320 : ℝ)) =
      B ^ (319 / (320 : ℝ)) * (B * H) ^ (1 / (320 : ℝ)) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ 1 / (320 : ℝ))]
  rw [← mul_assoc]
  have hpow : B ^ (319 / (320 : ℝ)) * B ^ (1 / (320 : ℝ)) = B := by
    rw [← ENNReal.rpow_add _ _ hBzero hBtop]
    norm_num
  rw [hpow]

/--
Under the support assumptions of \(\cref{thm:normalized-smoothing}\), bounded
inputs satisfy
\[
\Ichi(f_0,f_1,f_2)
\leq
C_{\ref{thm:normalized-smoothing},\,A_0,A_1,A_2,J,\chi}
\lpNorm{f_0}\infty\lpNorm{f_1}\infty
\lpNorm{f_2}\infty^{319/320}
\hNorm{f_2}{-1/2}^{1/320}.
\]
-/
theorem homogeneousNormalizedSmoothing
    (D : AdmissibleSupportData) (f₀ f₁ f₂ : ℝ → ℂ)
    (hf₀_memLp : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁_memLp : MemLp f₁ (∞ : ℝ≥0∞) volume)
    (hf₂_memLp : MemLp f₂ (∞ : ℝ≥0∞) volume)
    (hf₀_support : ∀ᵐ x ∂volume, x ∉ D.A₀ → f₀ x = 0)
    (hf₁_support : ∀ᵐ x ∂volume, x ∉ D.A₁ → f₁ x = 0)
    (hf₂_support : ∀ᵐ x ∂volume, x ∉ D.A₂ → f₂ x = 0) :
    ENNReal.ofReal (trilinearFormAbs D.χ f₀ f₁ f₂) ≤
      ENNReal.ofReal (C_normalizedNonlinearSmoothing D.A₀ D.A₁ D.A₂ D.J D.χ) *
        eLpNorm f₀ (∞ : ℝ≥0∞) volume *
          eLpNorm f₁ (∞ : ℝ≥0∞) volume *
            eLpNorm f₂ (∞ : ℝ≥0∞) volume ^ (319 / (320 : ℝ)) *
              aux_sobolevNormRaw (1 / 2 : ℝ) f₂ ^ (1 / (320 : ℝ)) := by
  let B₀ : ℝ≥0∞ := eLpNorm f₀ (∞ : ℝ≥0∞) volume
  let B₁ : ℝ≥0∞ := eLpNorm f₁ (∞ : ℝ≥0∞) volume
  let B₂ : ℝ≥0∞ := eLpNorm f₂ (∞ : ℝ≥0∞) volume
  by_cases hB₀ : B₀ = 0
  · have hz : f₀ =ᵐ[volume] 0 := by
      exact (eLpNorm_eq_zero_iff (p := (∞ : ℝ≥0∞))
        hf₀_memLp.aestronglyMeasurable (by simp)).mp (by simpa [B₀] using hB₀)
    have hI := aux_homogeneous_trilinearFormAbs_eq_zero_of_ae_zero
      D.χ f₀ f₁ f₂ (Or.inl hz)
    rw [hI]
    simp [B₀, hB₀]
  by_cases hB₁ : B₁ = 0
  · have hz : f₁ =ᵐ[volume] 0 := by
      exact (eLpNorm_eq_zero_iff (p := (∞ : ℝ≥0∞))
        hf₁_memLp.aestronglyMeasurable (by simp)).mp (by simpa [B₁] using hB₁)
    have hI := aux_homogeneous_trilinearFormAbs_eq_zero_of_ae_zero
      D.χ f₀ f₁ f₂ (Or.inr (Or.inl hz))
    rw [hI]
    simp [B₁, hB₁]
  by_cases hB₂ : B₂ = 0
  · have hz : f₂ =ᵐ[volume] 0 := by
      exact (eLpNorm_eq_zero_iff (p := (∞ : ℝ≥0∞))
        hf₂_memLp.aestronglyMeasurable (by simp)).mp (by simpa [B₂] using hB₂)
    have hI := aux_homogeneous_trilinearFormAbs_eq_zero_of_ae_zero
      D.χ f₀ f₁ f₂ (Or.inr (Or.inr hz))
    rw [hI]
    simp [B₂, hB₂]
  have hB₀top : B₀ ≠ ∞ := by simpa [B₀] using hf₀_memLp.eLpNorm_ne_top
  have hB₁top : B₁ ≠ ∞ := by simpa [B₁] using hf₁_memLp.eLpNorm_ne_top
  have hB₂top : B₂ ≠ ∞ := by simpa [B₂] using hf₂_memLp.eLpNorm_ne_top
  let b₀ : ℝ := B₀.toReal
  let b₁ : ℝ := B₁.toReal
  let b₂ : ℝ := B₂.toReal
  have hb₀pos : 0 < b₀ := ENNReal.toReal_pos hB₀ hB₀top
  have hb₁pos : 0 < b₁ := ENNReal.toReal_pos hB₁ hB₁top
  have hb₂pos : 0 < b₂ := ENNReal.toReal_pos hB₂ hB₂top
  let g₀ : ℝ → ℂ := ((b₀⁻¹ : ℝ) : ℂ) • f₀
  let g₁ : ℝ → ℂ := ((b₁⁻¹ : ℝ) : ℂ) • f₁
  let g₂ : ℝ → ℂ := ((b₂⁻¹ : ℝ) : ℂ) • f₂
  have hg₀meas : AEStronglyMeasurable g₀ volume := by
    exact hf₀_memLp.aestronglyMeasurable.const_smul _
  have hg₁meas : AEStronglyMeasurable g₁ volume := by
    exact hf₁_memLp.aestronglyMeasurable.const_smul _
  have hg₂meas : AEStronglyMeasurable g₂ volume := by
    exact hf₂_memLp.aestronglyMeasurable.const_smul _
  have hg₀bound : ∀ᵐ x ∂volume, ‖g₀ x‖ ≤ 1 := by
    simpa [g₀, b₀, B₀] using
      aux_homogeneous_normalized_one_bounded f₀ hf₀_memLp (by simpa [B₀] using hB₀)
  have hg₁bound : ∀ᵐ x ∂volume, ‖g₁ x‖ ≤ 1 := by
    simpa [g₁, b₁, B₁] using
      aux_homogeneous_normalized_one_bounded f₁ hf₁_memLp (by simpa [B₁] using hB₁)
  have hg₂bound : ∀ᵐ x ∂volume, ‖g₂ x‖ ≤ 1 := by
    simpa [g₂, b₂, B₂] using
      aux_homogeneous_normalized_one_bounded f₂ hf₂_memLp (by simpa [B₂] using hB₂)
  have hg₀support : ∀ᵐ x ∂volume, x ∉ D.A₀ → g₀ x = 0 := by
    filter_upwards [hf₀_support] with x hx hxin
    simp [g₀, hx hxin]
  have hg₁support : ∀ᵐ x ∂volume, x ∉ D.A₁ → g₁ x = 0 := by
    filter_upwards [hf₁_support] with x hx hxin
    simp [g₁, hx hxin]
  have hg₂support : ∀ᵐ x ∂volume, x ∉ D.A₂ → g₂ x = 0 := by
    filter_upwards [hf₂_support] with x hx hxin
    simp [g₂, hx hxin]
  have hnorm := normalizedNonlinearSmoothing D g₀ g₁ g₂
    hg₀meas hg₁meas hg₂meas hg₀bound hg₁bound hg₂bound
    hg₀support hg₁support hg₂support
  have hrec₀ : (b₀ : ℂ) • g₀ = f₀ := by
    funext x
    simp [g₀, hb₀pos.ne']
  have hrec₁ : (b₁ : ℂ) • g₁ = f₁ := by
    funext x
    simp [g₁, hb₁pos.ne']
  have hrec₂ : (b₂ : ℂ) • g₂ = f₂ := by
    funext x
    simp [g₂, hb₂pos.ne']
  have hA₂compact : IsCompact D.A₂ := by
    rcases D.hA₂ with ⟨a, b, hab, hA₂⟩
    rw [hA₂]
    exact isCompact_Icc
  have hg₂Lp : MemLp g₂ (2 : ℝ≥0∞) volume :=
    aux_memLp_of_ae_bound_of_ae_support g₂ hg₂meas 1 hg₂bound D.A₂
      hA₂compact.isClosed.measurableSet hA₂compact.measure_lt_top hg₂support 2
  have hH : aux_sobolevNormRaw (1 / 2 : ℝ) f₂ =
      B₂ * aux_sobolevNormRaw (1 / 2 : ℝ) g₂ := by
    calc
      aux_sobolevNormRaw (1 / 2 : ℝ) f₂ =
          aux_sobolevNormRaw (1 / 2 : ℝ) ((b₂ : ℂ) • g₂) := by rw [hrec₂]
      _ = ENNReal.ofReal ‖(b₂ : ℂ)‖ *
          aux_sobolevNormRaw (1 / 2 : ℝ) g₂ :=
        aux_homogeneous_sobolevNormRaw_smul _ _ _ hg₂Lp
      _ = B₂ * aux_sobolevNormRaw (1 / 2 : ℝ) g₂ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb₂pos,
          ENNReal.ofReal_toReal hB₂top]
  have hIreal : trilinearFormAbs D.χ f₀ f₁ f₂ =
      b₀ * b₁ * b₂ * trilinearFormAbs D.χ g₀ g₁ g₂ := by
    rw [← hrec₀, ← hrec₁, ← hrec₂,
      aux_homogeneous_trilinearFormAbs_smul_all]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hb₀pos, abs_of_pos hb₁pos, abs_of_pos hb₂pos]
  have hB₀real : ENNReal.ofReal b₀ = B₀ := ENNReal.ofReal_toReal hB₀top
  have hB₁real : ENNReal.ofReal b₁ = B₁ := ENNReal.ofReal_toReal hB₁top
  have hB₂real : ENNReal.ofReal b₂ = B₂ := ENNReal.ofReal_toReal hB₂top
  have hI : ENNReal.ofReal (trilinearFormAbs D.χ f₀ f₁ f₂) =
      B₀ * B₁ * B₂ * ENNReal.ofReal (trilinearFormAbs D.χ g₀ g₁ g₂) := by
    rw [hIreal,
      ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (le_of_lt hb₀pos)
        (le_of_lt hb₁pos)) (le_of_lt hb₂pos)),
      ENNReal.ofReal_mul (mul_nonneg (le_of_lt hb₀pos) (le_of_lt hb₁pos)),
      ENNReal.ofReal_mul (le_of_lt hb₀pos), hB₀real, hB₁real, hB₂real]
  have hpower := aux_homogeneous_sobolev_power B₂
    (aux_sobolevNormRaw (1 / 2 : ℝ) g₂) hB₂ hB₂top
  calc
    ENNReal.ofReal (trilinearFormAbs D.χ f₀ f₁ f₂) =
        B₀ * B₁ * B₂ * ENNReal.ofReal (trilinearFormAbs D.χ g₀ g₁ g₂) := hI
    _ ≤ B₀ * B₁ * B₂ *
        (ENNReal.ofReal (C_normalizedNonlinearSmoothing D.A₀ D.A₁ D.A₂ D.J D.χ) *
          aux_sobolevNormRaw (1 / 2 : ℝ) g₂ ^ (1 / (320 : ℝ))) :=
      by
        calc
          B₀ * B₁ * B₂ * ENNReal.ofReal (trilinearFormAbs D.χ g₀ g₁ g₂) =
              ENNReal.ofReal (trilinearFormAbs D.χ g₀ g₁ g₂) *
                (B₀ * B₁ * B₂) := by
              ring
          _ ≤ (ENNReal.ofReal (C_normalizedNonlinearSmoothing D.A₀ D.A₁ D.A₂ D.J D.χ) *
              aux_sobolevNormRaw (1 / 2 : ℝ) g₂ ^ (1 / (320 : ℝ))) * (B₀ * B₁ * B₂) :=
            mul_le_mul_left hnorm _
          _ = B₀ * B₁ * B₂ *
              (ENNReal.ofReal (C_normalizedNonlinearSmoothing D.A₀ D.A₁ D.A₂ D.J D.χ) *
                aux_sobolevNormRaw (1 / 2 : ℝ) g₂ ^ (1 / (320 : ℝ))) := by ring
    _ = ENNReal.ofReal (C_normalizedNonlinearSmoothing D.A₀ D.A₁ D.A₂ D.J D.χ) *
        B₀ * B₁ *
          (B₂ * aux_sobolevNormRaw (1 / 2 : ℝ) g₂ ^ (1 / (320 : ℝ))) := by
      ring
    _ = ENNReal.ofReal (C_normalizedNonlinearSmoothing D.A₀ D.A₁ D.A₂ D.J D.χ) *
        B₀ * B₁ *
          (B₂ ^ (319 / (320 : ℝ)) *
            (B₂ * aux_sobolevNormRaw (1 / 2 : ℝ) g₂) ^ (1 / (320 : ℝ))) := by
      rw [hpower]
    _ = ENNReal.ofReal (C_normalizedNonlinearSmoothing D.A₀ D.A₁ D.A₂ D.J D.χ) *
        B₀ * B₁ * B₂ ^ (319 / (320 : ℝ)) *
          aux_sobolevNormRaw (1 / 2 : ℝ) f₂ ^ (1 / (320 : ℝ)) := by
      rw [← hH]
      ring
    _ = ENNReal.ofReal (C_normalizedNonlinearSmoothing D.A₀ D.A₁ D.A₂ D.J D.χ) *
        eLpNorm f₀ (∞ : ℝ≥0∞) volume *
          eLpNorm f₁ (∞ : ℝ≥0∞) volume *
            eLpNorm f₂ (∞ : ℝ≥0∞) volume ^ (319 / (320 : ℝ)) *
              aux_sobolevNormRaw (1 / 2 : ℝ) f₂ ^ (1 / (320 : ℝ)) := by
      rfl

end Auto
