# Formalization status

## Introduction

Lean file: BourgainSmoothing/Auto/Introduction/Introduction.lean

### Definitions

None.

### Theorems

\label{thm:main}: [Proof completed] (Lean: bourgainTrilinearSmoothing) (2026-08-28 18:16 PDT)

## Conventions and foundational definitions

Lean file: BourgainSmoothing/Auto/ConventionsAndFoundationalDefinitions/ConventionsAndFoundationalDefinitions.lean

### Definitions

\label{def:intervals}: [Completed] (Lean: intervalLength, intervalAdd, intervalSub) (2026-08-27 22:47 PDT)
\label{def:fourier-sobolev}: [Completed] (Lean: exponential, frequencyCharacter, japaneseBracket, inverseFourierTransform, sobolevNorm) (2026-08-27 20:45 PDT)
\label{def:uniformity}: [Completed] (Lean: multiplicativeDifference, iteratedMultiplicativeDifference, uNorm) (2026-08-27 20:45 PDT)
\label{def:trilinear-form}: [Completed] (Lean: trilinearForm, trilinearFormAbs) (2026-08-27 20:45 PDT)
\label{def:size-parameter}: [Completed] (Lean: supportRadius, sizeParameter) (2026-08-27 20:45 PDT)

### Theorems

\label{lem:u-invariances}: [Proof completed] (Lean: uNormInvariances) (2026-08-27 22:44 PDT)
\label{lem:difference-l2}: [Proof completed] (Lean: differenceL2Identity) (2026-08-27 22:45 PDT)

## Explicit auxiliary cutoffs

Lean file: BourgainSmoothing/Auto/ExplicitAuxiliaryCutoffs/ExplicitAuxiliaryCutoffs.lean

### Definitions

\label{def:smooth-step}: [Completed] (Lean: smoothStep) (2026-08-27 20:45 PDT)
\label{def:spatial-cutoff}: [Completed] (Lean: spatialCutoff) (2026-08-27 20:45 PDT)
\label{def:dyadic-cutoffs}: [Completed] (Lean: lowFrequencyCutoff, dyadicCutoff, annularCutoff, P, Q) (2026-08-27 20:45 PDT)

### Theorems

\label{lem:smooth-step-bounds}: [Proof completed] (Lean: smoothStepBounds) (2026-08-27 23:03 PDT)
\label{lem:spatial-cutoff-bounds}: [Proof completed] (Lean: spatialCutoffBounds) (2026-08-27 23:19 PDT)
\label{lem:dyadic-kernel-bounds}: [Proof completed] (Lean: dyadicKernelBounds) (2026-08-28 00:43 PDT)
\label{lem:dyadic-reconstruction}: [Proof completed] (Lean: dyadicReconstructionAndMultiplierBounds) (2026-08-28 02:24 PDT)

## Fourier estimates for products of cutoffs

Lean file: BourgainSmoothing/Auto/FourierEstimatesForProductsOfCutoffs/FourierEstimatesForProductsOfCutoffs.lean

### Definitions

None.

### Theorems

\label{lem:fourier-l1-h1}: [Proof completed] (Lean: fourierL1LeFromH1) (2026-08-28 03:10 PDT)
\label{lem:product-cutoff-fourier}: [Proof completed] (Lean: productCutoffFourierBounds, productCutoffFourierBoundsChi) (2026-08-28 03:31 PDT)

## Gowers differencing and u3 control

Lean file: BourgainSmoothing/Auto/GowersDifferencingAndU3Control/GowersDifferencingAndU3Control.lean

### Definitions

None.

### Theorems

\label{prop:gowers-differencing}: [Proof completed] (Lean: gowersDifferencing) (2026-08-28 05:18 PDT)
\label{lem:separation-selection}: [Proof completed] (Lean: separationSelection) (2026-08-28 05:22 PDT)
\label{prop:u3-control}: [Proof completed] (Lean: u3Control) (2026-08-28 06:20 PDT)

## Dual difference interchange

Lean file: BourgainSmoothing/Auto/DualDifferenceInterchange/DualDifferenceInterchange.lean

### Definitions

None.

### Theorems

\label{lem:measurable-linearization}: [Proof completed] (Lean: measurableFourierSupremumLinearization) (2026-08-28 06:37 PDT)
\label{thm:dual-difference-interchange}: [Proof completed] (Lean: dualDifferenceInterchange) (2026-08-28 07:52 PDT)

## Quadratic oscillation and bilinear smoothing

Lean file: BourgainSmoothing/Auto/QuadraticOscillationAndBilinearSmoothing/QuadraticOscillationAndBilinearSmoothing.lean

### Definitions

None.

### Theorems

\label{lem:quadratic-oscillatory}: [Proof completed] (Lean: quadraticOscillatoryIntegralEstimate) (2026-08-28 08:36 PDT)
\label{prop:bilinear-sobolev}: [Proof completed] (Lean: bilinearSobolevEstimates) (2026-08-28 09:19 PDT)

## Sobolev norms of multiplicative differences

Lean file: BourgainSmoothing/Auto/SobolevNormsOfMultiplicativeDifferences/SobolevNormsOfMultiplicativeDifferences.lean

### Definitions

None.

### Theorems

\label{thm:sobolev-difference}: [Proof completed] (Lean: sobolevDifferenceEstimate) (2026-08-28 10:25 PDT)
\label{cor:sobolev-difference-s1}: [Proof completed] (Lean: sobolevDifferenceEstimateS1) (2026-08-28 10:25 PDT)

## Degree lowering and normalized smoothing

Lean file: BourgainSmoothing/Auto/DegreeLoweringAndNormalizedSmoothing/DegreeLoweringAndNormalizedSmoothing.lean

### Definitions

\label{def:admissible-data}: [Completed] (Lean: AdmissibleSupportData) (2026-08-27 22:05 PDT)

### Theorems

\label{lem:first-dualization}: [Proof completed] (Lean: firstDualization) (2026-08-28 10:40 PDT)
\label{thm:u2-control}: [Proof completed] (Lean: u2Control) (2026-08-28 11:23 PDT)
\label{lem:second-dualization}: [Proof completed] (Lean: secondDualization) (2026-08-28 11:41 PDT)
\label{thm:normalized-smoothing}: [Proof completed] (Lean: normalizedNonlinearSmoothing) (2026-08-28 12:10 PDT)
\label{cor:homogeneous-normalized}: [Proof completed] (Lean: homogeneousNormalizedSmoothing) (2026-08-28 12:27 PDT)

## Localization and dyadic L-infinity decay

Lean file: BourgainSmoothing/Auto/LocalizationAndDyadicLInfinityDecay/LocalizationAndDyadicLInfinityDecay.lean

### Definitions

\label{def:main-interaction-data}: [Completed] (Lean: mainInteractionData) (2026-08-27 22:09 PDT)

### Theorems

\label{lem:main-interaction-admissible}: [Proof completed] (Lean: mainInteractionDataAdmissible) (2026-08-28 12:32 PDT)
\label{lem:trilinear-localization}: [Proof completed] (Lean: trilinearFormSpatialLocalization) (2026-08-28 12:33 PDT)
\label{lem:localized-sobolev-decay}: [Proof completed] (Lean: localizedNegativeSobolevDecay) (2026-08-28 14:13 PDT)
\label{prop:dyadic-linfty-decay}: [Proof completed] (Lean: dyadicLInfinityDecay) (2026-08-28 14:19 PDT)

## The nondecaying endpoint and interpolation

Lean file: BourgainSmoothing/Auto/NondecayingEndpointAndInterpolation/NondecayingEndpointAndInterpolation.lean

### Definitions

None.

### Theorems

\label{lem:quadratic-average}: [Proof completed] (Lean: quadraticAveragingOperator) (2026-08-28 15:30 PDT)
\label{cor:l32-endpoint}: [Proof completed] (Lean: nondecayingLThreeHalvesEndpoint) (2026-08-28 15:50 PDT)
\label{prop:special-interpolation}: [Proof completed] (Lean: specialBilinearInterpolation) (2026-08-28 16:36 PDT)
\label{prop:dyadic-l2-decay}: [Proof completed] (Lean: dyadicL2Smoothing) (2026-08-28 17:25 PDT)

## Dyadic summation and proof of the main theorem

Lean file: BourgainSmoothing/Auto/DyadicSummationAndProofOfMainTheorem/DyadicSummationAndProofOfMainTheorem.lean

### Definitions

None.

### Theorems

\label{lem:l2-endpoint}: [Proof completed] (Lean: elementaryL2Endpoint) (2026-08-28 17:26 PDT)
\label{lem:weighted-dyadic-square}: [Proof completed] (Lean: weightedDyadicSquareEstimate) (2026-08-28 18:05 PDT)
\label{lem:geometric-summation}: [Proof completed] (Lean: geometricSummationConstant) (2026-08-28 18:07 PDT)
\label{lem:interaction-size-comparison}: [Proof completed] (Lean: interactionSizeComparison) (2026-08-28 18:10 PDT)
