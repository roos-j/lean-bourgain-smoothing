/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import BourgainSmoothing.Auto.DegreeLoweringAndNormalizedSmoothing.DegreeLoweringAndNormalizedSmoothing
import BourgainSmoothing.Auto.ExplicitAuxiliaryCutoffs.ExplicitAuxiliaryCutoffs

/-!
# Localization and dyadic \(L^\infty\) decay

Formalizations of the labeled definitions and estimates in the corresponding
section of `blueprint/blueprint.tex`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Real FourierTransform

namespace Auto

/--
The raw tuple underlying `mainInteractionData`.  This auxiliary structure
keeps the source definition separate from the proof that its five entries
form an `AdmissibleSupportData`.
-/
structure aux_MainInteractionData where
  A₀ : Set ℝ
  A₁ : Set ℝ
  A₂ : Set ℝ
  J : Set ℝ
  χ : ℝ → ℝ

/-- The interval \(I_1\) used by `mainInteractionData`. -/
def aux_mainInteractionI1 (a b : ℝ) (χ : ℝ → ℝ) : Set ℝ :=
  Set.Icc (a - supportRadius χ) (b + supportRadius χ)

/-- The interval \(I_2\) used by `mainInteractionData`. -/
def aux_mainInteractionI2 (a b : ℝ) (χ : ℝ → ℝ) : Set ℝ :=
  Set.Icc a (b + supportRadius χ ^ 2)

/-- The interval \(J_\chi\) used by `mainInteractionData`. -/
def aux_mainInteractionJ (χ : ℝ → ℝ) : Set ℝ :=
  Set.Icc (-supportRadius χ) (supportRadius χ)

/-- The first spatial interval used by `mainInteractionData`. -/
def aux_mainInteractionA0 (a b : ℝ) : Set ℝ :=
  Set.Icc (a - 1) (b + 1)

/-- The second spatial interval used by `mainInteractionData`. -/
def aux_mainInteractionA1 (a b : ℝ) (χ : ℝ → ℝ) : Set ℝ :=
  Set.image2 (fun x y : ℝ ↦ x + y) (aux_mainInteractionI1 a b χ) (Set.Icc (-1) 1)

/-- The third spatial interval used by `mainInteractionData`. -/
def aux_mainInteractionA2 (a b : ℝ) (χ : ℝ → ℝ) : Set ℝ :=
  Set.image2 (fun x y : ℝ ↦ x + y) (aux_mainInteractionI2 a b χ) (Set.Icc (-1) 1)

/--
Let \(K=[a,b]\) and define
\[
J_\chi:=[-R_\chi,R_\chi],
\]
\[
I_1:=[a-R_\chi,b+R_\chi],
\qquad
I_2:=[a,b+R_\chi^2],
\]
\[
A_0:=[a-1,b+1],
\qquad
A_1:=I_1+[-1,1],
\qquad
A_2:=I_2+[-1,1].
\]
Write
\[
\mathfrak D_{K,\chi}:=(A_0,A_1,A_2,J_\chi,\chi).
\]
-/
def mainInteractionData (a b : ℝ) (χ : ℝ → ℝ) : aux_MainInteractionData where
  A₀ := aux_mainInteractionA0 a b
  A₁ := aux_mainInteractionA1 a b χ
  A₂ := aux_mainInteractionA2 a b χ
  J := aux_mainInteractionJ χ
  χ := χ

/--
The raw tuple associated with an admissible datum, used to express that
`mainInteractionData` is admissible in `mainInteractionDataAdmissible`.
-/
def aux_admissibleSupportDataToInteractionData
    (D : AdmissibleSupportData) : aux_MainInteractionData where
  A₀ := D.A₀
  A₁ := D.A₁
  A₂ := D.A₂
  J := D.J
  χ := D.χ

/--
The datum \(\mathfrak D_{K,\chi}\) from
\(\label{def:main-interaction-data}\) is admissible.
-/
theorem mainInteractionDataAdmissible
    (a b : ℝ) (χ : ℝ → ℝ) (hab : a ≤ b)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1) :
    ∃ D : AdmissibleSupportData,
      aux_admissibleSupportDataToInteractionData D = mainInteractionData a b χ := by
  sorry

/--
If \(f_0\) is supported in \(K\), then
\[
\Lamchi(f_0,f_1,f_2)
=
\Lamchi(f_0,\rho_{I_1}f_1,\rho_{I_2}f_2).
\]
-/
theorem trilinearFormSpatialLocalization
    (a b : ℝ) (χ : ℝ → ℝ) (hab : a ≤ b)
    (hχ_compact : HasCompactSupport χ)
    (f₀ f₁ f₂ : ℝ → ℂ)
    (hf₀_support : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f₀ x = 0)
    (h_integrable : Integrable (fun p : ℝ × ℝ ↦
      f₀ p.1 * f₁ (p.1 + p.2) * f₂ (p.1 + p.2 ^ 2) * (χ p.2 : ℂ))) :
    trilinearForm χ f₀ f₁ f₂ =
      trilinearForm χ f₀
        (fun x ↦ (spatialCutoff (a - supportRadius χ) (b + supportRadius χ) x : ℂ) * f₁ x)
        (fun x ↦ (spatialCutoff a (b + supportRadius χ ^ 2) x : ℂ) * f₂ x) := by
  sorry

/-- The explicit constant in \(\label{lem:localized-sobolev-decay}\), used
by `localizedNegativeSobolevDecay`:
\[
C_{\ref{lem:localized-sobolev-decay},\,I}
:=
2^{19}(2+\lvert I\rvert).
\]
-/
def C_localizedNegativeSobolevDecay (I : Set ℝ) : ℝ :=
  (2 : ℝ) ^ 19 * (2 + intervalLength I)

/--
Let \(I\) be a compact interval, \(k\geq1\), and \(g\in L^\infty(\R)\).  Define
\[
C_{\ref{lem:localized-sobolev-decay},\,I}
:=
2^{19}(2+\lvert I\rvert).
\]
Then
\[
\hNorm{\rho_IQ_kg}{-1/2}
\leq
C_{\ref{lem:localized-sobolev-decay},\,I}
2^{-k/4}\lpNorm g\infty.
\]
-/
theorem localizedNegativeSobolevDecay
    (a b : ℝ) (hab : a ≤ b) (k : ℕ) (hk : 1 ≤ k)
    (g : ℝ → ℂ) (hg_memLp : MemLp g (∞ : ℝ≥0∞) volume) :
    aux_sobolevNormRaw (1 / 2 : ℝ)
        (fun x ↦ (spatialCutoff a b x : ℂ) * Q k g x) ≤
      ENNReal.ofReal
          (C_localizedNegativeSobolevDecay (Set.Icc a b) *
            (2 : ℝ) ^ (-(k : ℝ) / 4)) *
        eLpNorm g (∞ : ℝ≥0∞) volume := by
  sorry

/-- The explicit constant in \(\label{prop:dyadic-linfty-decay}\), used by
`dyadicLInfinityDecay`:
\[
C_{\ref{prop:dyadic-linfty-decay},\,K,\chi}
:=
2^{13}\Ssize{A_0,A_1,A_2,J_\chi}{\chi}^{4},
\]
where the intervals are those of \(\label{def:main-interaction-data}\).
-/
def C_dyadicLInfinityDecay (a b : ℝ) (χ : ℝ → ℝ) : ℝ :=
  (2 : ℝ) ^ 13 *
    sizeParameter ![
      aux_mainInteractionA0 a b,
      aux_mainInteractionA1 a b χ,
      aux_mainInteractionA2 a b χ,
      aux_mainInteractionJ χ] χ ^ 4

/--
Let \(k\geq1\).  Define
\[
C_{\ref{prop:dyadic-linfty-decay},\,K,\chi}
:=
2^{13}\Ssize{A_0,A_1,A_2,J_\chi}{\chi}^{4},
\]
where the intervals are those of \(\label{def:main-interaction-data}\).  If
\(f_0\) is supported in \(K\) and \(f_0,f_1,g\in L^\infty(\R)\), then
\[
\Ichi(f_0,f_1,Q_kg)
\leq
C_{\ref{prop:dyadic-linfty-decay},\,K,\chi}
2^{-2^{-11}k}
\lpNorm{f_0}\infty\lpNorm{f_1}\infty\lpNorm g\infty.
\]
-/
theorem dyadicLInfinityDecay
    (a b : ℝ) (χ : ℝ → ℝ) (hab : a ≤ b)
    (hχ_smooth : ContDiff ℝ ⊤ χ) (hχ_compact : HasCompactSupport χ)
    (hχ_nonneg : ∀ t : ℝ, 0 ≤ χ t) (hχ_le_one : ∀ t : ℝ, χ t ≤ 1)
    (k : ℕ) (hk : 1 ≤ k)
    (f₀ f₁ g : ℝ → ℂ)
    (hf₀_memLp : MemLp f₀ (∞ : ℝ≥0∞) volume)
    (hf₁_memLp : MemLp f₁ (∞ : ℝ≥0∞) volume)
    (hg_memLp : MemLp g (∞ : ℝ≥0∞) volume)
    (hf₀_support : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f₀ x = 0) :
    trilinearFormAbs χ f₀ f₁ (Q k g) ≤
      C_dyadicLInfinityDecay a b χ *
        (2 : ℝ) ^ (-((2 : ℝ) ^ (-11 : ℝ)) * (k : ℝ)) *
          (eLpNorm f₀ (∞ : ℝ≥0∞) volume).toReal *
            (eLpNorm f₁ (∞ : ℝ≥0∞) volume).toReal *
              (eLpNorm g (∞ : ℝ≥0∞) volume).toReal := by
  sorry

end Auto
