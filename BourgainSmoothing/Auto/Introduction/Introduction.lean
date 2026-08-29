/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import BourgainSmoothing.Auto.DyadicSummationAndProofOfMainTheorem.DyadicSummationAndProofOfMainTheorem

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
  rcases hK with ⟨a, b, hab, rfl⟩
  have hχ_memLp : MemLp χ (1 : ℝ≥0∞) volume :=
    hχ_smooth.continuous.memLp_of_hasCompactSupport hχ_compact
  have hχ : Integrable (fun t : ℝ ↦ (χ t : ℂ)) :=
    memLp_one_iff_integrable.mp hχ_memLp.ofReal
  let S : ℝ := aux_mainSize (Set.Icc a b) χ
  let A : ℝ := (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal
  let B : ℝ := (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal
  let H : ℝ := (sobolevNorm aux_bourgainSmoothingExponent (hf₂_memLp.toLp f₂)).toReal
  have hS : 2 ≤ S := by
    simpa only [S] using aux_mainSize_two_le (Set.Icc a b) χ
  have hABH : 0 ≤ A * B * H := by
    dsimp only [A, B, H]
    positivity
  have hLow : trilinearFormAbs χ f₀ f₁ (P 0 f₂) ≤ 2 * S * A * B * H := by
    simpa only [S, A, B, H] using
      aux_main_low_frequency_bound (Set.Icc a b) χ f₀ f₁ f₂ hχ_memLp
        hf₀_memLp hf₁_memLp hf₂_memLp
  have hHigh : ∀ N : ℕ, ∑ k ∈ Finset.range N,
      trilinearFormAbs χ f₀ f₁ (P (k + 1) f₂) ≤
        (2 : ℝ) ^ 22 * S ^ 2 * A * B * H := by
    intro N
    simpa only [S, A, B, H] using
      aux_main_high_frequency_bound a b χ hab hχ_smooth hχ_compact hχ_nonneg hχ_le_one
        f₀ f₁ f₂ hf₀_memLp hf₁_memLp hf₂_memLp hf₀_support N
  have hmain := aux_main_from_dyadic_partial_bounds χ f₀ f₁ f₂ hχ
    hf₀_memLp hf₁_memLp hf₂_memLp S A B H hS hABH hLow hHigh
  simpa only [C_bourgainTrilinearSmoothing, S, A, B, H,
    aux_bourgainSmoothingExponent] using hmain

end Auto
