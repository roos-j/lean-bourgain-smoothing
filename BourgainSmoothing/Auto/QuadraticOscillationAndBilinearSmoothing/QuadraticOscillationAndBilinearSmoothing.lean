/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import BourgainSmoothing.Auto.DualDifferenceInterchange.DualDifferenceInterchange
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
    (hJ : ∃ jMinus jPlus : ℝ, jMinus ≤ jPlus ∧ J = Set.Icc jMinus jPlus)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (hχ_support : tsupport χ ⊆ J) (a b : ℝ) :
    ‖∫ t : ℝ, exponential (a * t + b * t ^ 2) * (χ t : ℂ)‖ ≤
      C_quadraticOscillatoryIntegralEstimate J χ *
        (1 + max |a| |b|) ^ (-(1 / 2 : ℝ)) := by
  sorry

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
  sorry

end Auto
