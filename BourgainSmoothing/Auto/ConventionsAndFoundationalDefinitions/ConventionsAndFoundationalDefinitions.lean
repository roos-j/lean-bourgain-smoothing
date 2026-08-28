/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Conventions and foundational definitions

Formalizations of the labeled definitions and elementary lemmas in the
corresponding section of `blueprint/blueprint.tex`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Real FourierTransform

namespace Auto

/--
If `A = [a₋, a₊]` is a compact interval, then its length is
\[
|A| = a₊ - a₋.
\]
-/
def intervalLength (A : Set ℝ) : ℝ :=
  (volume A).toReal

/--
For compact intervals `A, B`,
\[
A+B:=\{a+b:a\in A,\ b\in B\},
\qquad
|A+B|=|A|+|B|.
\]
-/
theorem intervalAdd (aMinus aPlus bMinus bPlus : ℝ) (ha : aMinus ≤ aPlus)
    (hb : bMinus ≤ bPlus) :
    intervalLength (Set.image2 (fun a b : ℝ ↦ a + b)
      (Set.Icc aMinus aPlus) (Set.Icc bMinus bPlus)) =
      intervalLength (Set.Icc aMinus aPlus) + intervalLength (Set.Icc bMinus bPlus) := by
  have himage : Set.image2 (fun a b : ℝ ↦ a + b)
      (Set.Icc aMinus aPlus) (Set.Icc bMinus bPlus) =
      Set.Icc (aMinus + bMinus) (aPlus + bPlus) := by
    ext x
    constructor
    · rintro ⟨y, hy, z, hz, rfl⟩
      exact ⟨add_le_add hy.1 hz.1, add_le_add hy.2 hz.2⟩
    · intro hx
      rcases le_total x (aMinus + bPlus) with h | h
      · refine ⟨aMinus, ⟨le_rfl, ha⟩, x - aMinus, ?_, by ring⟩
        constructor <;> linarith [hx.1]
      · refine ⟨x - bPlus, ?_, bPlus, ⟨hb, le_rfl⟩, by ring⟩
        constructor <;> linarith [hx.2]
  rw [himage]
  simp only [intervalLength, Real.volume_Icc, ENNReal.toReal_ofReal,
    sub_nonneg.mpr ha, sub_nonneg.mpr hb,
    sub_nonneg.mpr (add_le_add ha hb)]
  ring

/--
For compact intervals `A, B`,
\[
A-B:=\{a-b:a\in A,\ b\in B\},
\qquad
|A-B|=|A|+|B|.
\]
-/
theorem intervalSub (aMinus aPlus bMinus bPlus : ℝ) (ha : aMinus ≤ aPlus)
    (hb : bMinus ≤ bPlus) :
    intervalLength (Set.image2 (fun a b : ℝ ↦ a - b)
      (Set.Icc aMinus aPlus) (Set.Icc bMinus bPlus)) =
      intervalLength (Set.Icc aMinus aPlus) + intervalLength (Set.Icc bMinus bPlus) := by
  have himage : Set.image2 (fun a b : ℝ ↦ a - b)
      (Set.Icc aMinus aPlus) (Set.Icc bMinus bPlus) =
      Set.Icc (aMinus - bPlus) (aPlus - bMinus) := by
    ext x
    constructor
    · rintro ⟨y, hy, z, hz, rfl⟩
      exact ⟨sub_le_sub hy.1 hz.2, sub_le_sub hy.2 hz.1⟩
    · intro hx
      rcases le_total x (aMinus - bMinus) with h | h
      · refine ⟨aMinus, ⟨le_rfl, ha⟩, aMinus - x, ?_, by ring⟩
        constructor <;> linarith [hx.1]
      · refine ⟨x + bMinus, ?_, bMinus, ⟨le_rfl, hb⟩, by ring⟩
        constructor <;> linarith [hx.2]
  rw [himage]
  simp only [intervalLength, Real.volume_Icc, ENNReal.toReal_ofReal,
    sub_nonneg.mpr ha, sub_nonneg.mpr hb,
    sub_nonneg.mpr (sub_le_sub ha hb)]
  ring

/--
For `x ∈ ℝ`,
\[
e(x):=e^{2\pi i x}.
\]
-/
def exponential (x : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

/--
For `x, ξ ∈ ℝ`,
\[
e_ξ(x):=e(ξx).
\]
-/
def frequencyCharacter (ξ : ℝ) : ℝ → ℂ :=
  fun x ↦ exponential (ξ * x)

/--
For `ξ ∈ ℝ`,
\[
\langle ξ\rangle:=(1+|ξ|^2)^{1/2}.
\]
-/
def japaneseBracket (ξ : ℝ) : ℝ :=
  Real.sqrt (1 + |ξ| ^ 2)

/--
For `g ∈ L¹(ℝ)`, define the inverse Fourier transform and check notation by
\[
\mathcal F^{-1}g(x):=\int_\mathbb R g(ξ)e(xξ)\,dξ,
\qquad
\check g:=\mathcal F^{-1}g.
\]
-/
def inverseFourierTransform (g : ℝ → ℂ) : ℝ → ℂ :=
  fun x ↦ 𝓕⁻ g x

/--
An `L²` Plancherel representative of the Fourier transform.

This auxiliary definition is used by the raw dyadic maps `P` and `Q` that
formalize `\label{def:dyadic-cutoffs}`.  It is deliberately not used to
define `sobolevNorm`; the latter takes an `Lp` input directly.  The zero
branch is outside `L²` and is excluded by the hypotheses of source-facing
results that use this representative.
-/
def aux_l2Fourier (f : ℝ → ℂ) : ℝ → ℂ := by
  classical
  exact if hf : MemLp f 2 volume then
    fun ξ ↦ (Lp.fourierTransformₗᵢ ℝ ℂ (hf.toLp f)) ξ
  else 0

/--
For `σ ≥ 0`,
\[
\|f\|_{H^{-σ}}^2
:=\int_\mathbb R |\widehat f(ξ)|^2\langle ξ\rangle^{-2σ}\,dξ.
\]
The Fourier transform on `L²` is its Plancherel extension.
-/
def sobolevNorm (σ : ℝ) (f : Lp (α := ℝ) ℂ 2 volume) : ℝ≥0∞ :=
  eLpNorm
    (fun ξ ↦ (japaneseBracket ξ ^ (-σ)) • (Lp.fourierTransformₗᵢ ℝ ℂ f) ξ) 2 volume

/--
For measurable `f : ℝ → ℂ` and `h ∈ ℝ`,
\[
\Delta_hf(x):=f(x)\overline{f(x+h)}.
\]
-/
def multiplicativeDifference (h : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x ↦ f x * starRingEnd ℂ (f (x + h))

/--
For `\mathbf h=(h₁,\ldots,h_s)∈\mathbb R^s`,
\[
\Delta_{\mathbf h}f:=\Delta_{h₁}\cdots\Delta_{h_s}f.
\]
-/
def iteratedMultiplicativeDifference :
    (s : ℕ) → (Fin s → ℝ) → (ℝ → ℂ) → ℝ → ℂ
  | 0, _, f => f
  | s + 1, h, f =>
      multiplicativeDifference (h 0)
        (iteratedMultiplicativeDifference s (fun i ↦ h i.succ) f)

/--
Whenever the right-hand side is finite, define
\[
\|f\|_{u^{s+2}}^{2^s}
:=\int_{\mathbb R^s}\|\widehat{\Delta_{\mathbf h}f}\|_\infty\,d\mathbf h.
\]
In particular,
\[
\|f\|_{u^2}=\|\widehat f\|_\infty,
\qquad
\|f\|_{u^3}^2=\int_\mathbb R
\|\widehat{\Delta_hf}\|_\infty\,dh.
\]
-/
def uNorm (r : ℕ) (f : ℝ → ℂ) : ℝ≥0∞ :=
  if r = 2 then
    eLpNorm (𝓕 f) ∞ volume
  else if 2 < r then
    (∫⁻ h : Fin (r - 2) → ℝ,
        eLpNorm
          (𝓕 (iteratedMultiplicativeDifference (r - 2) h f)) ∞ volume) ^
      (1 / ((2 : ℝ) ^ (r - 2)))
  else 0

/--
Whenever the integral is absolutely convergent, define
\[
\Lambda_χ(f₀,f₁,f₂):=
\iint_{\mathbb R^2}f₀(x)f₁(x+t)f₂(x+t^2)χ(t)\,dt\,dx.
\]
-/
def trilinearForm (χ : ℝ → ℝ) (f₀ f₁ f₂ : ℝ → ℂ) : ℂ :=
  ∫ x : ℝ, ∫ t : ℝ,
    f₀ x * f₁ (x + t) * f₂ (x + t ^ 2) * (χ t : ℂ)

/--
\[
\mathcal I_χ(f₀,f₁,f₂):=|\Lambda_χ(f₀,f₁,f₂)|.
\]
-/
def trilinearFormAbs (χ : ℝ → ℝ) (f₀ f₁ f₂ : ℝ → ℂ) : ℝ :=
  ‖trilinearForm χ f₀ f₁ f₂‖

/--
Let `A₁,\ldots,A_r` be compact intervals and let `ψ∈C_c^1(\mathbb R)`. Define
\[
R_ψ:=1+\sup\{|t|:t\in\operatorname{supp}ψ\},
\]
with supremum `0` when `ψ=0`.
-/
def supportRadius (ψ : ℝ → ℝ) : ℝ := by
  classical
  exact if hψ : ψ = 0 then 1
    else 1 + sSup (Set.image (fun t : ℝ ↦ |t|) (tsupport ψ))

/--
\[
\mathcal S(A₁,\ldots,A_r;ψ):=
2+\max\left\{
|A₁|,\ldots,|A_r|,R_ψ^2,
\|ψ\|_1,\|ψ\|_2,\|ψ'\|_1,\|ψ'\|_2
\right\}.
\]
This is a size parameter, not an inequality constant.
-/
def sizeParameter {r : ℕ} (A : Fin r → Set ℝ) (ψ : ℝ → ℝ) : ℝ :=
  2 + max (sSup (Set.range fun i ↦ intervalLength (A i)))
    (max (supportRadius ψ ^ 2)
      (max (eLpNorm ψ 1 volume).toReal
        (max (eLpNorm ψ 2 volume).toReal
          (max (eLpNorm (deriv ψ) 1 volume).toReal
            (eLpNorm (deriv ψ) 2 volume).toReal))))

/--
Auxiliary raw-Fourier homogeneity used to prove
`\label{lem:u-invariances}`.  It is stated for arbitrary functions because
the Bochner integral is homogeneous without an integrability hypothesis.
-/
lemma aux_fourier_smul (a : ℂ) (f : ℝ → ℂ) :
    𝓕 (a • f) = a • 𝓕 f := by
  exact VectorFourier.fourierIntegral_const_smul 𝐞 volume (innerₗ ℝ) f a

/--
Auxiliary raw-Fourier translation identity used to prove
`\label{lem:u-invariances}`.
-/
lemma aux_fourier_translate (y : ℝ) (f : ℝ → ℂ) :
    𝓕 (fun x ↦ f (x + y)) = fun ξ ↦ 𝐞 (y * ξ) • 𝓕 f ξ := by
  change VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) (fun x ↦ f (x + y)) =
    fun ξ ↦ 𝐞 (y * ξ) • VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) f ξ
  simpa [Function.comp_def, mul_comm] using
    (VectorFourier.fourierIntegral_comp_add_right 𝐞 volume (innerₗ ℝ) f y)

/--
Auxiliary raw-Fourier conjugation identity used to prove
`\label{lem:u-invariances}`.
-/
lemma aux_fourier_conj (g : ℝ → ℂ) :
    𝓕 (fun x ↦ starRingEnd ℂ (g x)) =
      fun ξ ↦ starRingEnd ℂ ((𝓕 g) (-ξ)) := by
  funext ξ
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  change (𝐞 (-inner ℝ x ξ) : ℂ) • star (g x) =
    star ((𝐞 (-inner ℝ x (-ξ)) : ℂ) • g x)
  rw [star_smul]
  congr 1
  have hphase : (𝐞 (-inner ℝ x ξ) : ℂ) =
      star (𝐞 (-inner ℝ x (-ξ)) : ℂ) := by
    change (𝐞 (-inner ℝ x ξ) : ℂ) =
      starRingEnd ℂ (𝐞 (-inner ℝ x (-ξ)) : ℂ)
    rw [← Circle.coe_inv_eq_conj (𝐞 (-inner ℝ x (-ξ)) : Circle)]
    rw [← AddChar.map_neg_eq_inv]
    congr 1
    simp
    rfl
  exact hphase

/--
Every raw Fourier integral is almost-everywhere strongly measurable: it is
continuous for integrable input and identically zero otherwise.  This permits
the reflection change of variables in `aux_fourier_linf_conj`.
-/
lemma aux_fourier_aestronglyMeasurable (g : ℝ → ℂ) :
    AEStronglyMeasurable (𝓕 g) volume := by
  by_cases hg : Integrable g volume
  · exact
      (VectorFourier.fourierIntegral_continuous (e := 𝐞) (μ := volume)
        (L := innerₗ ℝ) Real.continuous_fourierChar (by fun_prop) hg).aestronglyMeasurable
  · have hz : 𝓕 g = 0 := by
      funext ξ
      rw [Real.fourier_eq]
      exact integral_undef ((Real.fourierIntegral_convergent_iff ξ).not.mpr hg)
    rw [hz]
    exact aestronglyMeasurable_zero

/--
Translation does not change the `L^\infty` size of a raw Fourier transform.
This is an auxiliary step for `\label{lem:u-invariances}`.
-/
lemma aux_fourier_linf_translate (y : ℝ) (f : ℝ → ℂ) :
    eLpNorm (𝓕 (fun x ↦ f (x + y))) ∞ volume = eLpNorm (𝓕 f) ∞ volume := by
  rw [aux_fourier_translate]
  apply eLpNorm_congr_norm_ae
  filter_upwards with ξ
  simp

/--
Complex conjugation does not change the `L^\infty` size of a raw Fourier
transform.  This is an auxiliary step for `\label{lem:u-invariances}`.
-/
lemma aux_fourier_linf_conj (f : ℝ → ℂ) :
    eLpNorm (𝓕 (fun x ↦ starRingEnd ℂ (f x))) ∞ volume = eLpNorm (𝓕 f) ∞ volume := by
  rw [aux_fourier_conj]
  have hstar :
      eLpNorm (fun ξ ↦ starRingEnd ℂ ((𝓕 f) (-ξ))) ∞ volume =
        eLpNorm (fun ξ ↦ (𝓕 f) (-ξ)) ∞ volume := by
    apply eLpNorm_congr_norm_ae
    filter_upwards with ξ
    simp
  exact hstar.trans <| by
    simpa only [Function.comp_def] using
      (eLpNorm_comp_measurePreserving (p := ∞) (μ := volume) (ν := volume)
        (f := fun ξ : ℝ ↦ -ξ) (g := 𝓕 f) (aux_fourier_aestronglyMeasurable f)
        (Measure.measurePreserving_neg volume))

/--
The first multiplicative difference removes the phase of a complex scalar.
This is an auxiliary algebraic step for `\label{lem:u-invariances}`.
-/
lemma aux_multiplicativeDifference_smul (a : ℂ) (h : ℝ) (f : ℝ → ℂ) :
    multiplicativeDifference h (a • f) =
      (Complex.normSq a : ℂ) • multiplicativeDifference h f := by
  funext x
  simp only [multiplicativeDifference, Pi.smul_apply, smul_eq_mul, map_mul]
  calc
    a * f x * ((starRingEnd ℂ) a * (starRingEnd ℂ) (f (x + h))) =
        (a * (starRingEnd ℂ) a) * (f x * (starRingEnd ℂ) (f (x + h))) := by ring
    _ = _ := by rw [Complex.mul_conj]

/--
Multiplicative differences square a real scalar.  This supplies the induction
step for the scalar homogeneity of iterated differences.
-/
lemma aux_multiplicativeDifference_real_smul (c h : ℝ) (f : ℝ → ℂ) :
    multiplicativeDifference h ((c : ℂ) • f) =
      ((c ^ 2 : ℝ) : ℂ) • multiplicativeDifference h f := by
  funext x
  simp [multiplicativeDifference, mul_assoc]
  ring

/--
For a positive number of differences, scalar multiplication produces the
expected power of `Complex.normSq`.  This is an auxiliary lemma for
`\label{lem:u-invariances}`.
-/
lemma aux_iteratedMultiplicativeDifference_smul_succ :
    ∀ (s : ℕ) (h : Fin (s + 1) → ℝ) (a : ℂ) (f : ℝ → ℂ),
      iteratedMultiplicativeDifference (s + 1) h (a • f) =
        ((Complex.normSq a ^ (2 ^ s) : ℝ) : ℂ) •
          iteratedMultiplicativeDifference (s + 1) h f := by
  intro s
  induction s with
  | zero =>
      intro h a f
      simpa [iteratedMultiplicativeDifference] using
        aux_multiplicativeDifference_smul a (h 0) f
  | succ s ih =>
      intro h a f
      change multiplicativeDifference (h 0)
        (iteratedMultiplicativeDifference (s + 1) (fun i ↦ h i.succ) (a • f)) =
          ((Complex.normSq a ^ (2 ^ (s + 1)) : ℝ) : ℂ) •
            multiplicativeDifference (h 0)
              (iteratedMultiplicativeDifference (s + 1) (fun i ↦ h i.succ) f)
      rw [ih (fun i ↦ h i.succ) a f]
      rw [aux_multiplicativeDifference_real_smul]
      congr 1
      push_cast
      rw [← pow_mul]
      congr 1

/--
Iterated multiplicative differences commute with translation.  This is an
auxiliary algebraic step for `\label{lem:u-invariances}`.
-/
lemma aux_iteratedMultiplicativeDifference_translate :
    ∀ (s : ℕ) (h : Fin s → ℝ) (y : ℝ) (f : ℝ → ℂ),
      iteratedMultiplicativeDifference s h (fun x ↦ f (x + y)) =
        fun x ↦ iteratedMultiplicativeDifference s h f (x + y) := by
  intro s
  induction s with
  | zero =>
      intro h y f
      rfl
  | succ s ih =>
      intro h y f
      rw [iteratedMultiplicativeDifference, iteratedMultiplicativeDifference]
      rw [ih (fun i ↦ h i.succ) y f]
      funext x
      simp only [multiplicativeDifference]
      ring_nf

/--
Iterated multiplicative differences commute with complex conjugation.  This
is an auxiliary algebraic step for `\label{lem:u-invariances}`.
-/
lemma aux_iteratedMultiplicativeDifference_conj :
    ∀ (s : ℕ) (h : Fin s → ℝ) (f : ℝ → ℂ),
      iteratedMultiplicativeDifference s h (fun x ↦ starRingEnd ℂ (f x)) =
        fun x ↦ starRingEnd ℂ (iteratedMultiplicativeDifference s h f x) := by
  intro s
  induction s with
  | zero =>
      intro h f
      rfl
  | succ s ih =>
      intro h f
      rw [iteratedMultiplicativeDifference, iteratedMultiplicativeDifference]
      rw [ih (fun i ↦ h i.succ) f]
      funext x
      simp [multiplicativeDifference]

/--
The extended nonnegative norm of the scalar arising after `s + 1`
multiplicative differences.  This is the numerical normalization used by the
scalar part of `\label{lem:u-invariances}`.
-/
lemma aux_normSq_pow_enorm (a : ℂ) (s : ℕ) :
    (↑‖((Complex.normSq a ^ (2 ^ s) : ℝ) : ℂ)‖₊ : ℝ≥0∞) =
      (ENNReal.ofReal ‖a‖) ^ (2 ^ (s + 1)) := by
  rw [← enorm_eq_nnnorm, ← ofReal_norm]
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hnonneg : 0 ≤ Complex.normSq a ^ (2 ^ s) :=
    pow_nonneg (Complex.normSq_nonneg a) _
  rw [abs_of_nonneg hnonneg, ENNReal.ofReal_pow (Complex.normSq_nonneg a)]
  rw [Complex.normSq_eq_norm_sq, ENNReal.ofReal_pow (norm_nonneg a), ← pow_mul]
  congr 1
  ring

/--
The Fourier `L^∞` norm after a positive number of multiplicative differences
has the expected scalar factor.  This is an auxiliary step for
`\label{lem:u-invariances}`.
-/
lemma aux_fourier_linf_iterated_smul_succ (s : ℕ) (h : Fin (s + 1) → ℝ)
    (a : ℂ) (f : ℝ → ℂ) :
    eLpNorm (𝓕 (iteratedMultiplicativeDifference (s + 1) h (a • f))) ∞ volume =
      (ENNReal.ofReal ‖a‖) ^ (2 ^ (s + 1)) *
        eLpNorm (𝓕 (iteratedMultiplicativeDifference (s + 1) h f)) ∞ volume := by
  rw [aux_iteratedMultiplicativeDifference_smul_succ]
  rw [aux_fourier_smul]
  rw [eLpNorm_const_smul]
  rw [enorm_eq_nnnorm]
  rw [aux_normSq_pow_enorm]

/--
Let `r≥2`, `a∈\mathbb C`, `y∈\mathbb R`, and let `f` have finite `u^r`
quantity. Then
\[
\|af\|_{u^r}=|a|\|f\|_{u^r},
\qquad
\|x\mapsto f(x+y)\|_{u^r}=\|f\|_{u^r},
\qquad
\|\overline f\|_{u^r}=\|f\|_{u^r}.
\]
-/
theorem uNormInvariances (r : ℕ) (hr : 2 ≤ r) (a : ℂ) (y : ℝ) (f : ℝ → ℂ)
    (hf : uNorm r f ≠ ∞) :
    uNorm r (a • f) = ENNReal.ofReal ‖a‖ * uNorm r f ∧
      uNorm r (fun x ↦ f (x + y)) = uNorm r f ∧
        uNorm r (fun x ↦ starRingEnd ℂ (f x)) = uNorm r f := by
  clear hf
  rcases Nat.eq_or_lt_of_le hr with hr | hr
  · subst r
    constructor
    · simp only [uNorm]
      rw [aux_fourier_smul, eLpNorm_const_smul]
      simp
    constructor
    · simp only [uNorm]
      exact aux_fourier_linf_translate y f
    · simp only [uNorm]
      exact aux_fourier_linf_conj f
  have hr3 : 3 ≤ r := by omega
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' hr3
  have hs : s + 3 - 2 = s + 1 := by omega
  have hne : s + 3 ≠ 2 := by omega
  have hgt : 2 < s + 3 := by omega
  constructor
  · simp only [uNorm, if_neg hne, if_pos hgt]
    rw [hs]
    have hpoint (h : Fin (s + 1) → ℝ) :
        eLpNorm (𝓕 (iteratedMultiplicativeDifference (s + 1) h (a • f))) ∞ volume =
          (ENNReal.ofReal ‖a‖) ^ (2 ^ (s + 1) : ℕ) *
            eLpNorm (𝓕 (iteratedMultiplicativeDifference (s + 1) h f)) ∞ volume :=
      aux_fourier_linf_iterated_smul_succ s h a f
    simp_rw [hpoint]
    rw [lintegral_const_mul' _ _ (by simp)]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    have hroot : ((ENNReal.ofReal ‖a‖) ^ (2 ^ (s + 1) : ℕ)) ^
        (1 / ((2 : ℝ) ^ (s + 1))) = ENNReal.ofReal ‖a‖ := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      have hpow : ((2 ^ (s + 1) : ℕ) : ℝ) * (1 / ((2 : ℝ) ^ (s + 1))) = 1 := by
        norm_num [Nat.cast_pow]
      rw [hpow, ENNReal.rpow_one]
    rw [hroot]
  constructor
  · simp only [uNorm, if_neg hne, if_pos hgt]
    rw [hs]
    congr 1
    apply lintegral_congr
    intro h
    rw [aux_iteratedMultiplicativeDifference_translate (s + 1) h y f,
      aux_fourier_linf_translate]
  · simp only [uNorm, if_neg hne, if_pos hgt]
    rw [hs]
    congr 1
    apply lintegral_congr
    intro h
    rw [aux_iteratedMultiplicativeDifference_conj (s + 1) h f,
      aux_fourier_linf_conj]

/--
For every `f∈L^2(\mathbb R)`,
\[
\int_\mathbb R\|\Delta_hf\|_2^2\,dh=\|f\|_2^4.
\]
If `f` is `1`-bounded and supported in a compact interval `A`, then
\[
\left(\int_\mathbb R\|\Delta_hf\|_2^2\,dh\right)^{1/2}\leq|A|.
\]
-/
theorem differenceL2Identity (f : ℝ → ℂ) (hf : MemLp f 2 volume) :
    (∫⁻ h : ℝ, (eLpNorm (multiplicativeDifference h f) 2 volume) ^ (2 : ℝ)) =
        (eLpNorm f 2 volume) ^ (4 : ℝ) ∧
      ∀ A : Set ℝ, (∃ a b : ℝ, a ≤ b ∧ A = Set.Icc a b) →
        (∀ᵐ x ∂volume, x ∉ A → f x = 0) →
          (∀ᵐ x ∂volume, ‖f x‖ ≤ 1) →
            (∫⁻ h : ℝ, (eLpNorm (multiplicativeDifference h f) 2 volume) ^ (2 : ℝ)) ^
                (1 / (2 : ℝ)) ≤ ENNReal.ofReal (intervalLength A) := by
  let F : ℝ → ℝ≥0∞ := fun x ↦ ‖f x‖ₑ ^ (2 : ℝ)
  have hF : AEMeasurable F volume := by
    exact ENNReal.continuous_rpow_const.aemeasurable.comp_aemeasurable
      hf.aestronglyMeasurable.enorm
  have hnormSq : eLpNorm f 2 volume ^ (2 : ℝ) = ∫⁻ x, F x := by
    simpa [F] using
      (eLpNorm_nnreal_pow_eq_lintegral (f := f) (p := (2 : NNReal)) (by norm_num))
  have hinner (h : ℝ) :
      (eLpNorm (multiplicativeDifference h f) 2 volume) ^ (2 : ℝ) =
        ∫⁻ x, F x * F (x + h) := by
    simpa [F, multiplicativeDifference, enorm_mul,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)] using
      (eLpNorm_nnreal_pow_eq_lintegral (f := multiplicativeDifference h f)
        (p := (2 : NNReal)) (by norm_num))
  have hprod : AEMeasurable (Function.uncurry fun h x : ℝ ↦ F x * F (x + h))
      (volume.prod volume) := by
    have h1 : AEMeasurable (fun p : ℝ × ℝ ↦ F p.2) (volume.prod volume) := hF.comp_snd
    have h2 : AEMeasurable (fun p : ℝ × ℝ ↦ F (p.1 + p.2)) (volume.prod volume) := by
      simpa [Function.comp_def] using
        hF.comp_quasiMeasurePreserving (quasiMeasurePreserving_add volume volume)
    change AEMeasurable (fun p : ℝ × ℝ ↦ F p.2 * F (p.2 + p.1)) (volume.prod volume)
    convert h1.mul h2 using 1
    ext p
    simp [add_comm]
  have hidentity :
      (∫⁻ h : ℝ, (eLpNorm (multiplicativeDifference h f) 2 volume) ^ (2 : ℝ)) =
        (eLpNorm f 2 volume) ^ (4 : ℝ) := by
    calc
      ∫⁻ h : ℝ, (eLpNorm (multiplicativeDifference h f) 2 volume) ^ (2 : ℝ) =
          ∫⁻ h : ℝ, ∫⁻ x : ℝ, F x * F (x + h) := by simp_rw [hinner]
      _ = ∫⁻ x : ℝ, ∫⁻ h : ℝ, F x * F (x + h) := lintegral_lintegral_swap hprod
      _ = ∫⁻ x : ℝ, F x * ∫⁻ h : ℝ, F h := by
        apply lintegral_congr
        intro x
        have hshift : AEMeasurable (fun h : ℝ ↦ F (x + h)) volume := by
          simpa [Function.comp_def] using hF.comp_quasiMeasurePreserving
            (measurePreserving_add_left volume x).quasiMeasurePreserving
        have htranslate : (∫⁻ h : ℝ, F (x + h)) = ∫⁻ h : ℝ, F h :=
          lintegral_add_left_eq_self F x
        rw [lintegral_const_mul'' _ hshift, htranslate]
      _ = (∫⁻ x : ℝ, F x) * ∫⁻ h : ℝ, F h := lintegral_mul_const'' _ hF
      _ = (eLpNorm f 2 volume) ^ (4 : ℝ) := by
        rw [← hnormSq]
        norm_num [ENNReal.rpow_natCast, ← pow_add]
  refine ⟨hidentity, ?_⟩
  intro A hA hzero hbound
  rcases hA with ⟨a, b, hab, rfl⟩
  have hFle : F ≤ᵐ[volume] (Set.Icc a b).indicator (fun _ : ℝ ↦ (1 : ℝ≥0∞)) := by
    filter_upwards [hzero, hbound] with x hxzero hxbound
    by_cases hx : x ∈ Set.Icc a b
    · rw [Set.indicator_of_mem hx]
      have henorm : ‖f x‖ₑ ≤ 1 := by
        rw [← ofReal_norm, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hxbound
      exact ENNReal.rpow_le_one henorm (by norm_num)
    · rw [Set.indicator_of_notMem hx]
      simp [F, hxzero hx]
  have hroot :
      (∫⁻ h : ℝ, (eLpNorm (multiplicativeDifference h f) 2 volume) ^ (2 : ℝ)) ^
          (1 / (2 : ℝ)) = (eLpNorm f 2 volume) ^ (2 : ℝ) := by
    rw [hidentity, ← ENNReal.rpow_mul]
    norm_num
  calc
    (∫⁻ h : ℝ, (eLpNorm (multiplicativeDifference h f) 2 volume) ^ (2 : ℝ)) ^
          (1 / (2 : ℝ)) = (eLpNorm f 2 volume) ^ (2 : ℝ) := hroot
    _ = ∫⁻ x, F x := hnormSq
    _ ≤ ∫⁻ x, (Set.Icc a b).indicator (fun _ : ℝ ↦ (1 : ℝ≥0∞)) x :=
      lintegral_mono_ae hFle
    _ = ∫⁻ x in Set.Icc a b, (1 : ℝ≥0∞) := lintegral_indicator measurableSet_Icc _
    _ = volume (Set.Icc a b) := setLIntegral_one _
    _ = ENNReal.ofReal (intervalLength (Set.Icc a b)) := by
      simp only [intervalLength]
      rw [ENNReal.ofReal_toReal measure_Icc_lt_top.ne]

end Auto
