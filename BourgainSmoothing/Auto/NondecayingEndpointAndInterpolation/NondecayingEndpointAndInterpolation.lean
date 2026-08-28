/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import BourgainSmoothing.Auto.LocalizationAndDyadicLInfinityDecay.LocalizationAndDyadicLInfinityDecay
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# The nondecaying endpoint and interpolation

Formalizations of the labeled estimates in the corresponding section of
`blueprint/blueprint.tex`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Real FourierTransform

namespace Auto

/--
The quadratic averaging operator from \(\label{lem:quadratic-average}\):
\[
\mathcal A_\chi f(x)=\int_\mathbb R |f(x+t^2-t)|\chi(t)\,dt.
\]
-/
def quadraticAverage (χ : ℝ → ℝ) (f : ℝ → ℂ) : ℝ → ℝ :=
  fun x ↦ ∫ t : ℝ, ‖f (x + t ^ 2 - t)‖ * χ t

/-- The explicit constant in \(\label{lem:quadratic-average}\), used by
`quadraticAveragingOperator`:
\[
C_{\ref{lem:quadratic-average},\,\chi}
=2^2(1+R_\chi)^{1/3}.
\]
-/
noncomputable def C_quadraticAveragingOperator (χ : ℝ → ℝ) : ℝ :=
  (2 : ℝ) ^ 2 * (1 + supportRadius χ) ^ (1 / (3 : ℝ))

/--
Define
\[
\mathcal A_\chi f(x):=\int_\mathbb R|f(x+t^2-t)|\chi(t)\,dt,
\qquad
C_{\ref{lem:quadratic-average},\,\chi}:=2^2(1+R_\chi)^{1/3}.
\]
Then, for every \(f\in L^{3/2}(\mathbb R)\),
\[
\lVert\mathcal A_\chi f\rVert_3
\leq C_{\ref{lem:quadratic-average},\,\chi}\lVert f\rVert_{3/2}.
\]
-/
theorem quadraticAveragingOperator
    (χ : ℝ → ℝ)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (f : ℝ → ℂ) (hf : MemLp f (3 / 2 : ℝ≥0∞) volume) :
    (eLpNorm (quadraticAverage χ f) (3 : ℝ≥0∞) volume).toReal ≤
      C_quadraticAveragingOperator χ *
        (eLpNorm f (3 / 2 : ℝ≥0∞) volume).toReal := by
  sorry

/--
If \(f_0\in L^\infty(\mathbb R)\) and \(f_1,f_2\in L^{3/2}(\mathbb R)\), then
\[
\mathcal I_\chi(f_0,f_1,f_2)
\leq C_{\ref{lem:quadratic-average},\,\chi}
\lVert f_0\rVert_\infty
\lVert f_1\rVert_{3/2}
\lVert f_2\rVert_{3/2}.
\]
-/
theorem nondecayingLThreeHalvesEndpoint
    (χ : ℝ → ℝ)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (f₀ f₁ f₂ : ℝ → ℂ)
    (hf₀ : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁ : MemLp f₁ (3 / 2 : ℝ≥0∞) volume)
    (hf₂ : MemLp f₂ (3 / 2 : ℝ≥0∞) volume) :
    trilinearFormAbs χ f₀ f₁ f₂ ≤
      C_quadraticAveragingOperator χ *
        (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
          (eLpNorm f₁ (3 / 2 : ℝ≥0∞) volume).toReal *
            (eLpNorm f₂ (3 / 2 : ℝ≥0∞) volume).toReal := by
  sorry

/-- The submodule of bounded, compactly supported simple functions on
\(\mathbb R\).  A simple function is bounded because its range is finite; the
predicate records the compact-support condition in
\(\label{prop:special-interpolation}\). -/
def compactlySupportedSimpleSubmodule : Submodule ℂ (SimpleFunc ℝ ℂ) where
  carrier := {f | HasCompactSupport (f : ℝ → ℂ)}
  zero_mem' := by
    simpa using (HasCompactSupport.zero : HasCompactSupport (0 : ℝ → ℂ))
  add_mem' := by
    intro f g hf hg
    change HasCompactSupport ((f + g : SimpleFunc ℝ ℂ) : ℝ → ℂ)
    simpa only [SimpleFunc.coe_add, Pi.add_apply] using hf.add hg
  smul_mem' := by
    intro c f hf
    change HasCompactSupport ((c • f : SimpleFunc ℝ ℂ) : ℝ → ℂ)
    convert hf.smul_left (f := fun _ : ℝ ↦ c) using 1
    ext x
    change c * f x = (fun _ : ℝ ↦ c) x * f x
    rfl

/-- The source domain of `specialBilinearInterpolation`. -/
abbrev CompactSimple : Type := compactlySupportedSimpleSubmodule

/-- A compactly supported simple function is an `L²` function. -/
theorem compactSimpleMemLpTwo (f : CompactSimple) :
    MemLp (f.1 : ℝ → ℂ) (2 : ℝ≥0∞) volume := by
  obtain ⟨C, hC⟩ := (f.1.map (fun z : ℂ ↦ ‖z‖)).exists_forall_le
  refine f.2.memLp_of_bound f.1.aestronglyMeasurable C ?_
  exact Filter.Eventually.of_forall fun x ↦ by simpa using hC x

/-- The canonical embedding of source-domain functions into `L²`. -/
noncomputable def compactSimpleToLpTwo (f : CompactSimple) :
    Lp (α := ℝ) ℂ 2 volume :=
  (compactSimpleMemLpTwo f).toLp (f.1 : ℝ → ℂ)

/--
Let \(T\) be a complex bilinear form on bounded, compactly supported simple
functions.  Suppose
\[
|T(f,g)|\leq A_0\lVert f\rVert_\infty\lVert g\rVert_\infty,
\qquad
|T(f,g)|\leq A_1\lVert f\rVert_{3/2}\lVert g\rVert_{3/2},
\]
where \(A_0,A_1\geq0\).  Then \(T\) extends to
\(L^2(\mathbb R)\times L^2(\mathbb R)\) and
\[
|T(f,g)|\leq A_0^{1/4}A_1^{3/4}\lVert f\rVert_2\lVert g\rVert_2.
\]
-/
theorem specialBilinearInterpolation
    (T : CompactSimple →ₗ[ℂ] CompactSimple →ₗ[ℂ] ℂ)
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hInfinity : ∀ f g : CompactSimple,
      ‖T f g‖ ≤ A₀ *
        (eLpNorm (f.1 : ℝ → ℂ) (∞ : ℝ≥0∞) volume).toReal *
          (eLpNorm (g.1 : ℝ → ℂ) (∞ : ℝ≥0∞) volume).toReal)
    (hThreeHalves : ∀ f g : CompactSimple,
      ‖T f g‖ ≤ A₁ *
        (eLpNorm (f.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal *
          (eLpNorm (g.1 : ℝ → ℂ) (3 / 2 : ℝ≥0∞) volume).toReal) :
    ∃ T₂ : Lp (α := ℝ) ℂ 2 volume →L[ℂ]
        Lp (α := ℝ) ℂ 2 volume →L[ℂ] ℂ,
      (∀ f g : CompactSimple,
        T₂ (compactSimpleToLpTwo f) (compactSimpleToLpTwo g) = T f g) ∧
        ∀ f g : Lp (α := ℝ) ℂ 2 volume,
          ‖T₂ f g‖ ≤
            A₀ ^ (1 / (4 : ℝ)) * A₁ ^ (3 / (4 : ℝ)) * ‖f‖ * ‖g‖ := by
  sorry

/-- The explicit constant in \(\label{prop:dyadic-l2-decay}\), used by
`dyadicL2Smoothing`:
\[
C_{\ref{prop:dyadic-l2-decay},\,K,\chi}
=2^{10}\mathcal S(A_0,A_1,A_2,J_\chi;\chi)^2,
\]
where the intervals are those of \(\label{def:main-interaction-data}\). -/
def C_dyadicL2Smoothing (a b : ℝ) (χ : ℝ → ℝ) : ℝ :=
  (2 : ℝ) ^ 10 *
    sizeParameter ![
      aux_mainInteractionA0 a b,
      aux_mainInteractionA1 a b χ,
      aux_mainInteractionA2 a b χ,
      aux_mainInteractionJ χ] χ ^ 2

/--
Let \(k\geq1\).  Define
\[
C_{\ref{prop:dyadic-l2-decay},\,K,\chi}
=2^{10}\mathcal S(A_0,A_1,A_2,J_\chi;\chi)^2,
\]
where the intervals are those of \(\label{def:main-interaction-data}\).  If
\(f_0\in L^\infty(\mathbb R)\) is supported in \(K=[a,b]\) and
\(f_1,g\in L^2(\mathbb R)\), then
\[
\mathcal I_\chi(f_0,f_1,Q_kg)
\leq C_{\ref{prop:dyadic-l2-decay},\,K,\chi}
2^{-2^{-13}k}\lVert f_0\rVert_\infty
\lVert f_1\rVert_2\lVert g\rVert_2.
\]
-/
theorem dyadicL2Smoothing
    (a b : ℝ) (χ : ℝ → ℝ) (hab : a ≤ b)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (k : ℕ) (hk : 1 ≤ k)
    (f₀ f₁ g : ℝ → ℂ)
    (hf₀_memLp : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁_memLp : MemLp f₁ (2 : ℝ≥0∞) volume)
    (hg_memLp : MemLp g (2 : ℝ≥0∞) volume)
    (hf₀_support : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f₀ x = 0) :
    trilinearFormAbs χ f₀ f₁ (Q k g) ≤
      C_dyadicL2Smoothing a b χ *
        (2 : ℝ) ^ (-((2 : ℝ) ^ (-13 : ℝ)) * (k : ℝ)) *
          (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
            (eLpNorm f₁ (2 : ℝ≥0∞) volume).toReal *
              (eLpNorm g (2 : ℝ≥0∞) volume).toReal := by
  sorry

end Auto
