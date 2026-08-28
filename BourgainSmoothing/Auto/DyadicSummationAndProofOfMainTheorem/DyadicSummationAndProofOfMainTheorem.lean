/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import BourgainSmoothing.Auto.NondecayingEndpointAndInterpolation.NondecayingEndpointAndInterpolation
import BourgainSmoothing.Auto.Introduction.Introduction

/-!
# Dyadic summation and proof of the main theorem

Formalizations of the labeled auxiliary estimates in the corresponding
section of `blueprint/blueprint.tex`.  The introduction contains the statement
of the main theorem itself; this file supplies the four labeled estimates used
in its dyadic proof.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Real FourierTransform

namespace Auto

/--
If \(f_0\in L^\infty(\mathbb R)\) and \(f_1,f_2\in L^2(\mathbb R)\), then
\[
\mathcal I_\chi(f_0,f_1,f_2)
\leq
\lVert\chi\rVert_1\lVert f_0\rVert_\infty
\lVert f_1\rVert_2\lVert f_2\rVert_2.
\]
-/
theorem elementaryL2Endpoint
    (χ : ℝ → ℝ) (f₀ f₁ f₂ : ℝ → ℂ)
    (hχ_memLp : MemLp χ (1 : ℝ≥0∞) volume)
    (hf₀_memLp : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁_memLp : MemLp f₁ (2 : ℝ≥0∞) volume)
    (hf₂_memLp : MemLp f₂ (2 : ℝ≥0∞) volume) :
    trilinearFormAbs χ f₀ f₁ f₂ ≤
      (eLpNorm χ (1 : ℝ≥0∞) volume).toReal *
        (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
          (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal *
            (eLpNorm f₂ (2 : ℝ≥0∞) volume).toReal := by
  sorry

/--
Let \(0<\sigma\leq1\).  For every \(f\in L^2(\mathbb R)\),
\[
\lVert P_0f\rVert_2\leq5^{\sigma/2}\lVert f\rVert_{H^{-\sigma}},
\]
\[
\sum_{k=1}^\infty2^{-2\sigma k}\lVert P_kf\rVert_2^2
\leq3\cdot2^{3\sigma}\lVert f\rVert_{H^{-\sigma}}^2.
\]
-/
theorem weightedDyadicSquareEstimate
    (σ : ℝ) (hσ_pos : 0 < σ) (hσ_le_one : σ ≤ 1)
    (f : ℝ → ℂ) (hf_memLp : MemLp f (2 : ℝ≥0∞) volume) :
    (eLpNorm (P 0 f) (2 : ℝ≥0∞) volume).toReal ≤
      (5 : ℝ) ^ (σ / 2) * (sobolevNorm σ (hf_memLp.toLp f)).toReal ∧
      ∑' k : ℕ,
        (2 : ℝ) ^ (-2 * σ * ((k + 1 : ℕ) : ℝ)) *
          (eLpNorm (P (k + 1) f) (2 : ℝ≥0∞) volume).toReal ^ 2 ≤
        3 * (2 : ℝ) ^ (3 * σ) *
          (sobolevNorm σ (hf_memLp.toLp f)).toReal ^ 2 := by
  sorry

/--
The exponent \(\sigma_{\mathrm B}=2^{-14}\) in
\(\label{lem:geometric-summation}\), shared with the Sobolev exponent in
\(\label{thm:main}\).
-/
def aux_bourgainSmoothingExponent : ℝ :=
  (2 : ℝ) ^ (-14 : ℤ)

/--
Set \(\sigma_{\mathrm B}:=2^{-14}\).  Then
\[
\left(
\frac{3\cdot2^{3\sigma_{\mathrm B}}}
{2^{2\sigma_{\mathrm B}}-1}
\right)^{1/2}
\leq2^8.
\]
-/
theorem geometricSummationConstant :
    (3 * (2 : ℝ) ^ (3 * aux_bourgainSmoothingExponent) /
        ((2 : ℝ) ^ (2 * aux_bourgainSmoothingExponent) - 1)) ^
          (1 / (2 : ℝ)) ≤
      (2 : ℝ) ^ 8 := by
  sorry

/--
For \(K=[a,b]\), write
\[
\Sigma_{K,\chi}:=
2+|K|+R_\chi^2+\lVert\chi\rVert_1+\lVert\chi\rVert_2
+\lVert\chi'\rVert_1+\lVert\chi'\rVert_2.
\]
Then the interaction size from \(\label{def:main-interaction-data}\) obeys
\[
\mathcal S(A_0,A_1,A_2,J_\chi;\chi)
\leq2^2\Sigma_{K,\chi}.
\]
The right-hand side is `aux_mainSize (Set.Icc a b) χ`, the exact size
expression used by the main-theorem constant.
-/
theorem interactionSizeComparison
    (a b : ℝ) (χ : ℝ → ℝ) (hab : a ≤ b)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1) :
    sizeParameter ![
      aux_mainInteractionA0 a b,
      aux_mainInteractionA1 a b χ,
      aux_mainInteractionA2 a b χ,
      aux_mainInteractionJ χ] χ ≤
      (2 : ℝ) ^ 2 * aux_mainSize (Set.Icc a b) χ := by
  sorry

end Auto
