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
        ∫ h : ℝ, (eLpNorm (𝓕 (g h)) (∞ : ℝ≥0∞) volume).toReal - 1 / (n : ℝ) := by
  sorry

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
  sorry

end Auto
