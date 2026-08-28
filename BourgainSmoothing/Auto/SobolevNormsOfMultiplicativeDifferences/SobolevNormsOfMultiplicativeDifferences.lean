/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import BourgainSmoothing.Auto.QuadraticOscillationAndBilinearSmoothing.QuadraticOscillationAndBilinearSmoothing

/-!
# Sobolev norms of multiplicative differences

Formalizations of the labeled estimates in the corresponding section of
`blueprint/blueprint.tex`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Real FourierTransform

namespace Auto

/--
The raw-function form of the `L²` Sobolev norm.

The foundational `sobolevNorm` takes an `Lp` representative so that its Fourier
transform is the Plancherel extension.  This wrapper supplies that representative
when it exists, and is zero otherwise.  In the source-facing estimates below,
the bounded compact-support hypotheses prove that the nonzero branch applies.
-/
def aux_sobolevNormRaw (σ : ℝ) (g : ℝ → ℂ) : ℝ≥0∞ := by
  classical
  exact if hg : MemLp g 2 volume then sobolevNorm σ hg.toLp else 0

/--
For `s ≥ 1` and `σ > 0`, the exponent in
`\label{thm:sobolev-difference}` is
\[
\gamma_{s,\sigma}:=\frac{2^s\sigma}{1+2\sigma}.
\]
-/
def gammaSobolevDifference (s : ℕ) (σ : ℝ) : ℝ :=
  (2 : ℝ) ^ s * σ / (1 + 2 * σ)

/-- The constant in `\(\label{thm:sobolev-difference}\)`, used by
`sobolevDifferenceEstimate`:
\[
C_{\ref{thm:sobolev-difference},\,s,A}
:=
2^{s+1}(1+|A|)^{s+1}.
\]
-/
def C_sobolevDifferenceEstimate (s : ℕ) (A : Set ℝ) : ℝ :=
  (2 : ℝ) ^ (s + 1) * (1 + intervalLength A) ^ (s + 1)

/--
Let `s ≥ 1`, `σ > 0`, and let `A` be a positive-length compact interval. Define
\[
\gamma_{s,\sigma}:=\frac{2^s\sigma}{1+2\sigma},
\qquad
C_{\ref{thm:sobolev-difference},\,s,A}
:=2^{s+1}(1+|A|)^{s+1}.
\]
If `f` is $1$-bounded and supported in `A`, then
\[
\int_{\mathbb R^s}\|\Delta_{\mathbf h}f\|_{H^{-\sigma}}^2
\,d\mathbf h
\leq
C_{\ref{thm:sobolev-difference},\,s,A}
\|f\|_{u^{s+1}}^{\gamma_{s,\sigma}}.
\]
-/
theorem sobolevDifferenceEstimate
    (s : ℕ) (hs : 1 ≤ s) (σ : ℝ) (hσ : 0 < σ)
    (A : Set ℝ) (hA : ∃ a b : ℝ, a < b ∧ A = Set.Icc a b)
    (f : ℝ → ℂ) (hf_measurable : AEStronglyMeasurable f volume)
    (hf_one_bounded : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hf_support : ∀ᵐ x ∂volume, x ∉ A → f x = 0) :
    (∫⁻ h : Fin s → ℝ,
      aux_sobolevNormRaw σ (iteratedMultiplicativeDifference s h f) ^ (2 : ℝ)) ≤
        ENNReal.ofReal (C_sobolevDifferenceEstimate s A) *
          uNorm (s + 1) f ^ gammaSobolevDifference s σ := by
  sorry

/--
Let `A` be a positive-length compact interval. If `f` is $1$-bounded and
supported in `A`, then
\[
\int_\mathbb R\|\Delta_h f\|_{H^{-1/2}}^2\,dh
\leq
C_{\ref{thm:sobolev-difference},\,1,A}\|f\|_{u^2}^{1/2}.
\]
-/
theorem sobolevDifferenceEstimateS1
    (A : Set ℝ) (hA : ∃ a b : ℝ, a < b ∧ A = Set.Icc a b)
    (f : ℝ → ℂ) (hf_measurable : AEStronglyMeasurable f volume)
    (hf_one_bounded : ∀ᵐ x ∂volume, ‖f x‖ ≤ 1)
    (hf_support : ∀ᵐ x ∂volume, x ∉ A → f x = 0) :
    (∫⁻ h : ℝ,
      aux_sobolevNormRaw (1 / 2 : ℝ) (multiplicativeDifference h f) ^ (2 : ℝ)) ≤
        ENNReal.ofReal (C_sobolevDifferenceEstimate 1 A) *
          uNorm 2 f ^ (1 / 2 : ℝ) := by
  sorry

end Auto
