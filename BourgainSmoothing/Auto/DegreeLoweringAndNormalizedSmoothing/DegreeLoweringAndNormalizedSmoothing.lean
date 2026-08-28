/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import BourgainSmoothing.Auto.SobolevNormsOfMultiplicativeDifferences.SobolevNormsOfMultiplicativeDifferences

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
    (hf₂_support : ∀ᵐ x ∂volume, x ∉ D.A₂ → f₂ x = 0) :
    (∀ᵐ x ∂volume, x ∉ aux_firstDualInterval D →
      aux_firstDualFunction D.χ f₁ f₂ x = 0) ∧
      trilinearFormAbs D.χ f₀ f₁ f₂ ≤
        intervalLength D.A₀ ^ (1 / (2 : ℝ)) *
          trilinearFormAbs D.χ (aux_firstDualFunction D.χ f₁ f₂) f₁ f₂ ^
            (1 / (2 : ℝ)) := by
  sorry

/-- The constant in \(\label{thm:u2-control}\), used by `u2Control`:
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
  sorry

/-- The function \(F_1\) appearing in \(\label{lem:second-dualization}\).

This raw map is separated from `secondDualization` so that its support and
Cauchy--Schwarz conclusions can be stated together.
-/
def aux_secondDualFunction (χ : ℝ → ℝ) (f₀ f₂ : ℝ → ℂ) : ℝ → ℂ :=
  fun x ↦ ∫ t : ℝ,
    starRingEnd ℂ (f₀ (x - t) * f₂ (x - t + t ^ 2)) * (χ t : ℂ)

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
    (hf₂_support : ∀ᵐ x ∂volume, x ∉ D.A₂ → f₂ x = 0) :
    (∀ᵐ x ∂volume, x ∉ D.A₁ → aux_secondDualFunction D.χ f₀ f₂ x = 0) ∧
      trilinearFormAbs D.χ f₀ f₁ f₂ ≤
        intervalLength D.A₁ ^ (1 / (2 : ℝ)) *
          trilinearFormAbs D.χ f₀ (aux_secondDualFunction D.χ f₀ f₂) f₂ ^
            (1 / (2 : ℝ)) := by
  sorry

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
  sorry

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
  sorry

end Auto
