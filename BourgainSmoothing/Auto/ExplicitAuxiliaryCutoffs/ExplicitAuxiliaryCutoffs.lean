/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import BourgainSmoothing.Auto.ConventionsAndFoundationalDefinitions.ConventionsAndFoundationalDefinitions

/-!
# Explicit auxiliary cutoffs

Formalizations of the labeled definitions and estimates in the corresponding
section of `blueprint/blueprint.tex`.
-/

noncomputable section

namespace Auto

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

/--
The polynomial smooth step from \(\label{def:smooth-step}\):
\[
s(u)=0\quad(u\leq0),\qquad
s(u)=3u^2-2u^3\quad(0<u<1),\qquad
s(u)=1\quad(u\geq1).
\]
Then \(s\in C^1(\mathbb R)\cap W^{2,1}_{\mathrm{loc}}(\mathbb R)\).
-/
def smoothStep (u : ℝ) : ℝ :=
  if u ≤ 0 then 0 else if u < 1 then 3 * u ^ 2 - 2 * u ^ 3 else 1

/--
The derivative bounds in \(\label{lem:smooth-step-bounds}\):
\[
\lVert s'\rVert_1=1,\qquad
\lVert s''\rVert_1=3,\qquad
\lVert s'\rVert_2^2=\frac65<2.
\]
-/
theorem smoothStepBounds :
    eLpNorm (deriv smoothStep) (1 : ℝ≥0∞) volume = 1 ∧
      eLpNorm (deriv (deriv smoothStep)) (1 : ℝ≥0∞) volume = 3 ∧
      eLpNorm (deriv smoothStep) (2 : ℝ≥0∞) volume ^ 2 = (6 : ℝ≥0∞) / 5 ∧
      eLpNorm (deriv smoothStep) (2 : ℝ≥0∞) volume ^ 2 < 2 := by
  sorry

/--
For the compact interval \(I=[a,b]\), the spatial cutoff from
\(\label{def:spatial-cutoff}\) is
\[
\rho_I(x)=s(x-a+1)s(b+1-x).
\]
-/
def spatialCutoff (a b : ℝ) (x : ℝ) : ℝ :=
  smoothStep (x - a + 1) * smoothStep (b + 1 - x)

/--
The bounds for the spatial cutoff in \(\label{lem:spatial-cutoff-bounds}\):
\[
0\leq\rho_I\leq1,\quad \rho_I=1\text{ on }I,\quad
\operatorname{supp}\rho_I\subset I+[-1,1],
\]
\[
\lVert\rho_I\rVert_1\leq |I|+2,\quad
\lVert\rho_I\rVert_2\leq(|I|+2)^{1/2},\quad
\lVert\rho_I'\rVert_1\leq2,\quad
\lVert\rho_I''\rVert_1\leq2^4.
\]
-/
theorem spatialCutoffBounds {a b : ℝ} (hab : a ≤ b) :
    (∀ x, 0 ≤ spatialCutoff a b x ∧ spatialCutoff a b x ≤ 1) ∧
      (∀ x ∈ Set.Icc a b, spatialCutoff a b x = 1) ∧
      tsupport (spatialCutoff a b) ⊆ Set.Icc (a - 1) (b + 1) ∧
      eLpNorm (spatialCutoff a b) (1 : ℝ≥0∞) volume ≤ ENNReal.ofReal (b - a + 2) ∧
      eLpNorm (spatialCutoff a b) (2 : ℝ≥0∞) volume ≤
        ENNReal.ofReal (Real.sqrt (b - a + 2)) ∧
      eLpNorm (deriv (spatialCutoff a b)) (1 : ℝ≥0∞) volume ≤ 2 ∧
      eLpNorm (deriv (deriv (spatialCutoff a b))) (1 : ℝ≥0∞) volume ≤ 2 ^ 4 := by
  sorry

/--
The even low-frequency cutoff \(\eta\) in \(\label{def:dyadic-cutoffs}\):
\[
\eta(\xi)=s(2-|\xi|).
\]
-/
def lowFrequencyCutoff (ξ : ℝ) : ℝ :=
  smoothStep (2 - |ξ|)

/--
The cutoff \(\varphi\) in \(\label{def:dyadic-cutoffs}\):
\[
\varphi(\xi)=\eta(\xi)-\eta(2\xi).
\]
-/
def dyadicCutoff (ξ : ℝ) : ℝ :=
  lowFrequencyCutoff ξ - lowFrequencyCutoff (2 * ξ)

/--
The annular cutoff \(q\) in \(\label{def:dyadic-cutoffs}\):
\[
q(\xi)=\eta(\xi/2)-\eta(4\xi).
\]
-/
def annularCutoff (ξ : ℝ) : ℝ :=
  lowFrequencyCutoff (ξ / 2) - lowFrequencyCutoff (4 * ξ)

/--
Helper for \(\label{def:dyadic-cutoffs}\), used by
`dyadicReconstructionAndMultiplierBounds`: the annular cutoff is one on the
stated middle annulus.
-/
theorem aux_annularCutoff_one_on {ξ : ℝ}
    (hξ_lower : 1 / 2 ≤ |ξ|) (hξ_upper : |ξ| ≤ 2) :
    annularCutoff ξ = 1 := by
  sorry

/--
Helper for \(\label{def:dyadic-cutoffs}\), used by
`dyadicReconstructionAndMultiplierBounds`: the annular cutoff vanishes
outside its stated support.
-/
theorem aux_annularCutoff_eq_zero_of_outside {ξ : ℝ}
    (hξ : |ξ| ≤ 1 / 4 ∨ 4 ≤ |ξ|) :
    annularCutoff ξ = 0 := by
  sorry

/--
The raw convolution used for the dyadic maps in \(\label{def:dyadic-cutoffs}\).
It is written directly as a map of functions so that the dyadic operators also
apply to bounded inputs, as they do in the manuscript.
-/
noncomputable def aux_convolution (κ f : ℝ → ℂ) : ℝ → ℂ :=
  fun x ↦ ∫ t : ℝ, κ t * f (x - t)

/--
The scaled inverse-Fourier kernel for a multiplier `m`.  This is the kernel
whose Fourier multiplier is \(m(2^{-k}\cdot)\), and is used by `P` and `Q`
for \(\label{def:dyadic-cutoffs}\).
-/
noncomputable def aux_scaledInverseFourierKernel (m : ℝ → ℂ) (k : ℕ) : ℝ → ℂ :=
  fun x ↦ ((2 : ℝ) ^ k : ℂ) * inverseFourierTransform m ((2 : ℝ) ^ k * x)

/--
The dyadic multiplier \(P_k\) from \(\label{def:dyadic-cutoffs}\), in its
kernel form:
\[
P_0f=\check\eta*f,\qquad
P_kf=2^k\check\varphi(2^k\cdot)*f\quad(k\geq1).
\]
Whenever Fourier transforms are defined, this is equivalently
\(\widehat{P_0f}=\eta\widehat f\) and
\(\widehat{P_kf}(\xi)=\varphi(2^{-k}\xi)\widehat f(\xi)\).
-/
noncomputable def P (k : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  if k = 0 then
    aux_convolution (inverseFourierTransform fun ξ ↦ (lowFrequencyCutoff ξ : ℂ)) f
  else
    aux_convolution
      (aux_scaledInverseFourierKernel (fun ξ ↦ (dyadicCutoff ξ : ℂ)) k) f

/--
The dyadic multiplier \(Q_k\) from \(\label{def:dyadic-cutoffs}\), in its
kernel form:
\[
Q_kf=2^k\check q(2^k\cdot)*f.
\]
For \(k\geq1\), this is equivalently
\(\widehat{Q_kf}(\xi)=q(2^{-k}\xi)\widehat f(\xi)\).  The kernel form is
defined for all raw functions, including the bounded inputs used later in the
manuscript.
-/
noncomputable def Q (k : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  aux_convolution
    (aux_scaledInverseFourierKernel (fun ξ ↦ (annularCutoff ξ : ℂ)) k) f

/--
The multiplier
\[
m(\xi)=\frac{q(\xi)}{(2\pi i\xi)^2}
\]
used to prove \(\label{lem:dyadic-kernel-bounds}\).  This is an auxiliary
definition for `dyadicKernelBounds`.
-/
def aux_dyadicKernelMultiplier (ξ : ℝ) : ℂ :=
  (annularCutoff ξ : ℂ) /
    ((((2 * Real.pi : ℝ) : ℂ) * Complex.I * (ξ : ℂ)) ^ 2)

/-- The explicit constant in \(\label{lem:dyadic-kernel-bounds}\), used by
`dyadicKernelBounds`. -/
def C_dyadicKernelBounds : ℝ := 2 ^ 10

/--
The kernel bounds in \(\label{lem:dyadic-kernel-bounds}\):
\[
\lVert\check q\rVert_1\leq2^6,\qquad
\left\lVert\mathcal F^{-1}\!\left(\frac{q}{(2\pi i\,\cdot)^2}\right)
\right\rVert_1\leq C_{\mathrm{dyadic\text{-}kernel\text{-}bounds},q}.
\]
-/
theorem dyadicKernelBounds :
    eLpNorm (inverseFourierTransform fun ξ ↦ (annularCutoff ξ : ℂ))
        (1 : ℝ≥0∞) volume ≤ 2 ^ 6 ∧
      eLpNorm (inverseFourierTransform aux_dyadicKernelMultiplier)
        (1 : ℝ≥0∞) volume ≤ ENNReal.ofReal C_dyadicKernelBounds := by
  sorry

/--
The reconstruction, Fourier-support, and multiplier bounds in
\(\label{lem:dyadic-reconstruction}\):
\[
f=P_0f+\sum_{k=1}^\infty P_kf\quad\text{in }L^2(\mathbb R),
\]
\[
\operatorname{supp}\widehat{P_kf}\subset
\{\xi:2^{k-1}\leq|\xi|\leq2^{k+1}\},\qquad Q_kP_kf=P_kf,
\]
and, for \(1\leq p\leq\infty\),
\[
\lVert Q_kf\rVert_p\leq2^6\lVert f\rVert_p.
\]
-/
theorem dyadicReconstructionAndMultiplierBounds (f : ℝ → ℂ) (hf : MemLp f 2 volume) :
    Tendsto
        (fun N : ℕ ↦
          eLpNorm
            (fun x ↦ f x - P 0 f x - ∑ k ∈ Finset.range N, P (k + 1) f x)
            (2 : ℝ≥0∞) volume)
        atTop (𝓝 0) ∧
      (∀ k : ℕ, 1 ≤ k →
        tsupport (aux_l2Fourier (P k f)) ⊆
          {ξ : ℝ | (2 : ℝ) ^ (k - 1) ≤ |ξ| ∧ |ξ| ≤ (2 : ℝ) ^ (k + 1)}) ∧
      (∀ k : ℕ, 1 ≤ k → Q k (P k f) = P k f) ∧
      ∀ (k : ℕ) (p : ℝ≥0∞), 1 ≤ k → 1 ≤ p →
        eLpNorm (Q k f) p volume ≤ 2 ^ 6 * eLpNorm f p volume := by
  sorry

end Auto
