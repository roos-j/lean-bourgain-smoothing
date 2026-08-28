/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import BourgainSmoothing.Auto.FourierEstimatesForProductsOfCutoffs.FourierEstimatesForProductsOfCutoffs

/-!
# Gowers differencing and \(u^3\) control

Formalizations of the labeled estimates in the corresponding section of
`blueprint/blueprint.tex`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Real FourierTransform

namespace Auto

/-- The constant in \(\label{prop:gowers-differencing}\), used by
`gowersDifferencing`:
\[
C_{\ref{prop:gowers-differencing},\,A,J,\psi}
:=
2^2\Ssize{A,J}{\psi}^{2}.
\]
-/
def C_gowersDifferencing (A J : Set ℝ) (ψ : ℝ → ℝ) : ℝ :=
  (2 : ℝ) ^ 2 * sizeParameter ![A, J] ψ ^ 2

/--
Let $A,J$ be positive-length compact intervals. Let $\psi\in C_c^1(\R)$ satisfy
$0\leq\psi\leq1$ and $\supp\psi\subset J$. Let
$c_0=0,c_1,c_2,c_3\in\R$ satisfy
\[
0<\delta\leq\min_{0\leq i<j\leq3}|c_i-c_j|,
\]
\[
\max_{0\leq i<j\leq3}|c_i-c_j|\leq M,
\]
where $0<\delta\leq1$ and $M\geq1$. Let $g_0,g_1,g_2,g_3$ be $1$-bounded,
assume $g_0$ is supported in $A$, and assume $g_1$ is compactly supported. Define
\[
C_{\ref{prop:gowers-differencing},\,A,J,\psi}
:=
2^2\Ssize{A,J}{\psi}^{2}.
\]
Then
\[
\left|
\iint g_0(x)g_1(x+c_1t)g_2(x+c_2t)g_3(x+c_3t)\psi(t)
\dd t\dd x
\right|
\leq
C_{\ref{prop:gowers-differencing},\,A,J,\psi}
M\delta^{-3/2}\uNorm{g_1}3.
\]
-/
theorem gowersDifferencing
    (A J : Set ℝ) (ψ : ℝ → ℝ)
    (hA : ∃ a b : ℝ, a < b ∧ A = Set.Icc a b)
    (hJ : ∃ a b : ℝ, a < b ∧ J = Set.Icc a b)
    (hψ_smooth : ContDiff ℝ 1 ψ) (hψ_compact : HasCompactSupport ψ)
    (hψ_nonneg : ∀ t : ℝ, 0 ≤ ψ t) (hψ_le_one : ∀ t : ℝ, ψ t ≤ 1)
    (hψ_support : tsupport ψ ⊆ J)
    (δ M : ℝ) (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1) (hM_one : 1 ≤ M)
    (c : Fin 4 → ℝ) (hc_zero : c 0 = 0)
    (hc_separated : ∀ i j : Fin 4, i < j → δ ≤ |c i - c j|)
    (hc_bounded : ∀ i j : Fin 4, i < j → |c i - c j| ≤ M)
    (g : Fin 4 → ℝ → ℂ)
    (hg_measurable : ∀ i : Fin 4, AEStronglyMeasurable (g i) volume)
    (hg_one_bounded : ∀ i : Fin 4, ∀ᵐ x ∂volume, ‖g i x‖ ≤ 1)
    (hg_zero_support : ∀ᵐ x ∂volume, x ∉ A → g 0 x = 0)
    (hg_one_compact : HasCompactSupport (g 1)) :
    ENNReal.ofReal ‖∫ x : ℝ, ∫ t : ℝ,
        g 0 x * g 1 (x + c 1 * t) * g 2 (x + c 2 * t) * g 3 (x + c 3 * t) *
          (ψ t : ℂ)‖ ≤
      ENNReal.ofReal
          (C_gowersDifferencing A J ψ * M * δ ^ (-(3 / 2 : ℝ))) *
        uNorm 3 (g 1) := by
  sorry

/--
Let $E\subset\R$ be measurable and suppose $|E|\geq m$ with $0<m\leq1$. Then there
exists $h\in E$ such that the four numbers
\[
0,\quad -2h,\quad 1,\quad 1-2h
\]
are pairwise separated by at least $2^{-2}m$.
-/
theorem separationSelection
    (E : Set ℝ) (hE_measurable : MeasurableSet E)
    (m : ℝ) (hm_pos : 0 < m) (hm_le_one : m ≤ 1)
    (hE_measure : ENNReal.ofReal m ≤ volume E) :
    ∃ h ∈ E, ∀ i j : Fin 4, i ≠ j →
      m / 4 ≤
        |(![0, -2 * h, 1, 1 - 2 * h] i : ℝ) -
          (![0, -2 * h, 1, 1 - 2 * h] j : ℝ)| := by
  sorry

/-- The constant in \(\label{prop:u3-control}\), used by `u3Control`:
\[
C_{\ref{prop:u3-control},\,A,C,J,\chi}
:=
2^4\Ssize{A,C,J}{\chi}^{3}.
\]
-/
def C_u3Control (A C J : Set ℝ) (χ : ℝ → ℝ) : ℝ :=
  (2 : ℝ) ^ 4 * sizeParameter ![A, C, J] χ ^ 3

/--
Let $A,C,J$ be positive-length compact intervals. Let $\chi\in C_c^\infty(\R)$ satisfy
$0\leq\chi\leq1$ and $\supp\chi\subset J$. Define
\[
C_{\ref{prop:u3-control},\,A,C,J,\chi}
:=
2^4\Ssize{A,C,J}{\chi}^{3}.
\]
If $f_0,f_1,f_2$ are $1$-bounded, $f_0$ is supported in $A$, and $f_2$ is
supported in $C$, then
\[
\Ichi(f_0,f_1,f_2)
\leq
C_{\ref{prop:u3-control},\,A,C,J,\chi}
\uNorm{f_0}3^{1/5}.
\]
-/
theorem u3Control
    (A C J : Set ℝ) (χ : ℝ → ℝ)
    (hA : ∃ a b : ℝ, a < b ∧ A = Set.Icc a b)
    (hC : ∃ a b : ℝ, a < b ∧ C = Set.Icc a b)
    (hJ : ∃ a b : ℝ, a < b ∧ J = Set.Icc a b)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (hχ_support : tsupport χ ⊆ J)
    (f₀ f₁ f₂ : ℝ → ℂ)
    (hf_measurable : ∀ i : Fin 3, AEStronglyMeasurable (![f₀, f₁, f₂] i) volume)
    (hf_one_bounded : ∀ i : Fin 3, ∀ᵐ x ∂volume, ‖![f₀, f₁, f₂] i x‖ ≤ 1)
    (hf_zero_support : ∀ᵐ x ∂volume, x ∉ A → f₀ x = 0)
    (hf_two_support : ∀ᵐ x ∂volume, x ∉ C → f₂ x = 0) :
    ENNReal.ofReal (trilinearFormAbs χ f₀ f₁ f₂) ≤
      ENNReal.ofReal (C_u3Control A C J χ) * uNorm 3 f₀ ^ (1 / (5 : ℝ)) := by
  sorry

end Auto
