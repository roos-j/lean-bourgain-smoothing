/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import BourgainSmoothing.Auto.ConventionsAndFoundationalDefinitions.ConventionsAndFoundationalDefinitions
import Mathlib.Analysis.Distribution.Sobolev

/-!
# Fourier estimates for products of cutoffs

Formalizations of the labeled estimates in the corresponding section of
`blueprint/blueprint.tex`.
-/

noncomputable section

open MeasureTheory FourierTransform TemperedDistribution
open scoped ENNReal Real FourierTransform LineDeriv

namespace Auto

/-- The right-hand-side coefficient in `\label{lem:fourier-l1-h1}`, used by
`fourierL1LeFromH1`. -/
noncomputable def C_fourierL1LeFromH1
    (g dg : Lp (α := ℝ) ℂ 2 volume) : ℝ :=
  Real.sqrt 2 * ‖g‖ +
    (Real.sqrt 2 / (2 * Real.pi)) * ‖dg‖

/--
If \(g\in H^1(\mathbb R)\), then
\[
\lVert\widehat g\rVert_1
\leq
\sqrt2\lVert g\rVert_2+
\frac{\sqrt2}{2\pi}\lVert g'\rVert_2.
\]
-/
theorem fourierL1LeFromH1
    (g dg : Lp (α := ℝ) ℂ 2 volume)
    (hg : MemSobolev (E := ℝ) 1 2 (Lp.toTemperedDistribution g))
    (hdg : ∂_{(1 : ℝ)} (Lp.toTemperedDistribution g) = Lp.toTemperedDistribution dg) :
    (eLpNorm (fun ξ : ℝ ↦ (Lp.fourierTransformₗᵢ ℝ ℂ g) ξ)
      (1 : ℝ≥0∞) volume).toReal ≤ C_fourierL1LeFromH1 g dg := by
  sorry

/-- The explicit constant in `\label{lem:product-cutoff-fourier}`, used by
`productCutoffFourierBounds`. -/
noncomputable def C_productCutoffFourierBounds (ψ : ℝ → ℝ) : ℝ :=
  Real.sqrt 2 * (eLpNorm ψ (2 : ℝ≥0∞) volume).toReal +
    (Real.sqrt 2 / Real.pi) * (eLpNorm (deriv ψ) (2 : ℝ≥0∞) volume).toReal

/--
Let \(\psi\in C_c^1(\mathbb R)\) satisfy \(0\leq\psi\leq1\). Define
\[
C_{\ref{lem:product-cutoff-fourier},\,\psi}
:=
\sqrt2\lVert\psi\rVert_2+\frac{\sqrt2}{\pi}\lVert\psi'\rVert_2.
\]
Then, for every \(u\in\mathbb R\),
\[
\left\lVert\mathcal F\{\psi(\cdot)\psi(\cdot+u)\}\right\rVert_1
\leq
C_{\ref{lem:product-cutoff-fourier},\,\psi}.
\]
-/
theorem productCutoffFourierBounds
    (ψ : ℝ → ℝ)
    (hψ_smooth : ContDiff ℝ 1 ψ) (hψ_compact : HasCompactSupport ψ)
    (hψ_nonneg : ∀ t : ℝ, 0 ≤ ψ t) (hψ_le_one : ∀ t : ℝ, ψ t ≤ 1) :
    ∀ u : ℝ,
      (eLpNorm
          (𝓕 (fun t : ℝ ↦ ((ψ t * ψ (t + u) : ℝ) : ℂ)))
          (1 : ℝ≥0∞) volume).toReal ≤
        C_productCutoffFourierBounds ψ := by
  sorry

/--
For \(\psi_h(t):=\chi(t)\chi(t+h)\), one has the uniform explicit bound
\[
C_{\ref{lem:product-cutoff-fourier},\,\psi_h}
\leq
\sqrt2\lVert\chi\rVert_2+\frac{2\sqrt2}{\pi}\lVert\chi'\rVert_2.
\]
-/
theorem productCutoffFourierBoundsChi
    (χ : ℝ → ℝ)
    (hχ_smooth : ContDiff ℝ 1 χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1) :
    ∀ h : ℝ,
      C_productCutoffFourierBounds (fun t : ℝ ↦ χ t * χ (t + h)) ≤
        Real.sqrt 2 * (eLpNorm χ (2 : ℝ≥0∞) volume).toReal +
          ((2 * Real.sqrt 2) / Real.pi) *
            (eLpNorm (deriv χ) (2 : ℝ≥0∞) volume).toReal := by
  sorry

end Auto
