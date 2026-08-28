/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import BourgainSmoothing.Auto.ConventionsAndFoundationalDefinitions.ConventionsAndFoundationalDefinitions

/-!
# Introduction

Formalization of the labeled theorem in the introduction of
`blueprint/blueprint.tex`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Real FourierTransform

namespace Auto

/--
The unmaximized size expression in \(\label{thm:main}\).

This auxiliary definition records the exact sum occurring in the source
constant and is used by `C_bourgainTrilinearSmoothing` and
`bourgainTrilinearSmoothing`.
-/
def aux_mainSize (K : Set ℝ) (χ : ℝ → ℝ) : ℝ :=
  2 + intervalLength K + supportRadius χ ^ 2 +
    (eLpNorm χ 1 volume).toReal + (eLpNorm χ 2 volume).toReal +
      (eLpNorm (deriv χ) 1 volume).toReal +
        (eLpNorm (deriv χ) 2 volume).toReal

/--
The explicit constant in \(\label{thm:main}\), used by
`bourgainTrilinearSmoothing`:
\[
C_{\ref{thm:main},\,K,\chi}
:=
2^{23}
\left(
2+\lvert K\rvert+R_\chi^2
+\lVert\chi\rVert_1+\lVert\chi\rVert_2
+\lVert\chi'\rVert_1+\lVert\chi'\rVert_2
\right)^2.
\]
-/
def C_bourgainTrilinearSmoothing (K : Set ℝ) (χ : ℝ → ℝ) : ℝ :=
  (2 : ℝ) ^ 23 * aux_mainSize K χ ^ 2

/--
Let \(K\subset\mathbb R\) be a compact interval and let
\(\chi\in C_c^\infty(\mathbb R)\) satisfy \(0\leq\chi\leq1\).  Define
\[
R_\chi:=1+\sup\{|t|:t\in\operatorname{supp}\chi\},
\]
where the supremum is \(0\) when \(\chi=0\), and define
\[
C_{\ref{thm:main},\,K,\chi}
:=
2^{23}
\left(
2+\lvert K\rvert+R_\chi^2
+\lVert\chi\rVert_1+\lVert\chi\rVert_2
+\lVert\chi'\rVert_1+\lVert\chi'\rVert_2
\right)^2.
\]
Then, for every \(f_0\in L^\infty(\mathbb R)\) supported in \(K\) and every
\(f_1,f_2\in L^2(\mathbb R)\),
\[
\left|
\iint_{\mathbb R^2}
 f_0(x)f_1(x+t)f_2(x+t^2)\chi(t)
\,dt\,dx
\right|
\leq
C_{\ref{thm:main},\,K,\chi}
\lVert f_0\rVert_\infty\lVert f_1\rVert_2
\lVert f_2\rVert_{H^{-2^{-14}}}.
\]
-/
theorem bourgainTrilinearSmoothing
    (K : Set ℝ) (hK : ∃ a b : ℝ, a ≤ b ∧ K = Set.Icc a b)
    (χ : ℝ → ℝ)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (f₀ f₁ f₂ : ℝ → ℂ)
    (hf₀_memLp : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁_memLp : MemLp f₁ (2 : ℝ≥0∞) volume)
    (hf₂_memLp : MemLp f₂ (2 : ℝ≥0∞) volume)
    (hf₀_support : ∀ᵐ x ∂volume, x ∉ K → f₀ x = 0) :
    trilinearFormAbs χ f₀ f₁ f₂ ≤
      C_bourgainTrilinearSmoothing K χ *
        (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
          (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal *
            (sobolevNorm ((2 : ℝ) ^ (-14 : ℤ)) (hf₂_memLp.toLp f₂)).toReal := by
  sorry

end Auto
