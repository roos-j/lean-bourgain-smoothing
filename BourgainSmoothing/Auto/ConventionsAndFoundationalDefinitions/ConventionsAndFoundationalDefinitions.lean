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
  sorry

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
  sorry

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
  sorry

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
  sorry

end Auto
