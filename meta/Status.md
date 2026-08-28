# Formalization status

## Introduction

Lean file: BourgainSmoothing/Auto/Introduction/Introduction.lean

### Definitions

None.

### Theorems

\label{thm:main}: [Statement completed] (Lean: bourgainTrilinearSmoothing) (2026-08-27 22:18 PDT)

## Conventions and foundational definitions

Lean file: BourgainSmoothing/Auto/ConventionsAndFoundationalDefinitions/ConventionsAndFoundationalDefinitions.lean

### Definitions

\label{def:intervals}: [Completed] (Lean: intervalLength, intervalAdd, intervalSub) (2026-08-27 20:45 PDT)
\label{def:fourier-sobolev}: [Completed] (Lean: exponential, frequencyCharacter, japaneseBracket, inverseFourierTransform, sobolevNorm) (2026-08-27 20:45 PDT)
\label{def:uniformity}: [Completed] (Lean: multiplicativeDifference, iteratedMultiplicativeDifference, uNorm) (2026-08-27 20:45 PDT)
\label{def:trilinear-form}: [Completed] (Lean: trilinearForm, trilinearFormAbs) (2026-08-27 20:45 PDT)
\label{def:size-parameter}: [Completed] (Lean: supportRadius, sizeParameter) (2026-08-27 20:45 PDT)

### Theorems

\label{lem:u-invariances}: [Statement completed] (Lean: uNormInvariances) (2026-08-27 20:45 PDT)
\label{lem:difference-l2}: [Statement completed] (Lean: differenceL2Identity) (2026-08-27 22:18 PDT)

## Explicit auxiliary cutoffs

Lean file: BourgainSmoothing/Auto/ExplicitAuxiliaryCutoffs/ExplicitAuxiliaryCutoffs.lean

### Definitions

\label{def:smooth-step}: [Completed] (Lean: smoothStep) (2026-08-27 20:45 PDT)
\label{def:spatial-cutoff}: [Completed] (Lean: spatialCutoff) (2026-08-27 20:45 PDT)
\label{def:dyadic-cutoffs}: [Completed] (Lean: lowFrequencyCutoff, dyadicCutoff, annularCutoff, P, Q) (2026-08-27 20:45 PDT)

### Theorems

\label{lem:smooth-step-bounds}: [Statement completed] (Lean: smoothStepBounds) (2026-08-27 20:45 PDT)
\label{lem:spatial-cutoff-bounds}: [Statement completed] (Lean: spatialCutoffBounds) (2026-08-27 20:45 PDT)
\label{lem:dyadic-kernel-bounds}: [Statement completed] (Lean: dyadicKernelBounds) (2026-08-27 20:45 PDT)
\label{lem:dyadic-reconstruction}: [Statement completed] (Lean: dyadicReconstructionAndMultiplierBounds) (2026-08-27 20:45 PDT)

## Fourier estimates for products of cutoffs

Lean file: BourgainSmoothing/Auto/FourierEstimatesForProductsOfCutoffs/FourierEstimatesForProductsOfCutoffs.lean

### Definitions

None.

### Theorems

\label{lem:fourier-l1-h1}: [Statement completed] (Lean: fourierL1LeFromH1) (2026-08-27 21:48 PDT)
\label{lem:product-cutoff-fourier}: [Statement completed] (Lean: productCutoffFourierBounds, productCutoffFourierBoundsChi) (2026-08-27 21:48 PDT)

## Gowers differencing and u3 control

Lean file: BourgainSmoothing/Auto/GowersDifferencingAndU3Control/GowersDifferencingAndU3Control.lean

### Definitions

None.

### Theorems

\label{prop:gowers-differencing}: [Statement completed] (Lean: gowersDifferencing) (2026-08-27 21:52 PDT)
\label{lem:separation-selection}: [Statement completed] (Lean: separationSelection) (2026-08-27 21:52 PDT)
\label{prop:u3-control}: [Statement completed] (Lean: u3Control) (2026-08-27 21:52 PDT)

## Dual difference interchange

Lean file: BourgainSmoothing/Auto/DualDifferenceInterchange/DualDifferenceInterchange.lean

### Definitions

None.

### Theorems

\label{lem:measurable-linearization}: [Statement completed] (Lean: measurableFourierSupremumLinearization) (2026-08-27 21:54 PDT)
\label{thm:dual-difference-interchange}: [Statement completed] (Lean: dualDifferenceInterchange) (2026-08-27 21:54 PDT)

## Quadratic oscillation and bilinear smoothing

Lean file: BourgainSmoothing/Auto/QuadraticOscillationAndBilinearSmoothing/QuadraticOscillationAndBilinearSmoothing.lean

### Definitions

None.

### Theorems

\label{lem:quadratic-oscillatory}: [Statement completed] (Lean: quadraticOscillatoryIntegralEstimate) (2026-08-27 21:58 PDT)
\label{prop:bilinear-sobolev}: [Statement completed] (Lean: bilinearSobolevEstimates) (2026-08-27 21:58 PDT)

## Sobolev norms of multiplicative differences

Lean file: BourgainSmoothing/Auto/SobolevNormsOfMultiplicativeDifferences/SobolevNormsOfMultiplicativeDifferences.lean

### Definitions

None.

### Theorems

\label{thm:sobolev-difference}: [Statement completed] (Lean: sobolevDifferenceEstimate) (2026-08-27 22:00 PDT)
\label{cor:sobolev-difference-s1}: [Statement completed] (Lean: sobolevDifferenceEstimateS1) (2026-08-27 22:00 PDT)

## Degree lowering and normalized smoothing

Lean file: BourgainSmoothing/Auto/DegreeLoweringAndNormalizedSmoothing/DegreeLoweringAndNormalizedSmoothing.lean

### Definitions

\label{def:admissible-data}: [Completed] (Lean: AdmissibleSupportData) (2026-08-27 22:05 PDT)

### Theorems

\label{lem:first-dualization}: [Statement completed] (Lean: firstDualization) (2026-08-27 22:05 PDT)
\label{thm:u2-control}: [Statement completed] (Lean: u2Control) (2026-08-27 22:05 PDT)
\label{lem:second-dualization}: [Statement completed] (Lean: secondDualization) (2026-08-27 22:05 PDT)
\label{thm:normalized-smoothing}: [Statement completed] (Lean: normalizedNonlinearSmoothing) (2026-08-27 22:05 PDT)
\label{cor:homogeneous-normalized}: [Statement completed] (Lean: homogeneousNormalizedSmoothing) (2026-08-27 22:05 PDT)

## Localization and dyadic L-infinity decay

Lean file: BourgainSmoothing/Auto/LocalizationAndDyadicLInfinityDecay/LocalizationAndDyadicLInfinityDecay.lean

### Definitions

\label{def:main-interaction-data}: [Completed] (Lean: mainInteractionData) (2026-08-27 22:09 PDT)

### Theorems

\label{lem:main-interaction-admissible}: [Statement completed] (Lean: mainInteractionDataAdmissible) (2026-08-27 22:09 PDT)
\label{lem:trilinear-localization}: [Statement completed] (Lean: trilinearFormSpatialLocalization) (2026-08-27 22:09 PDT)
\label{lem:localized-sobolev-decay}: [Statement completed] (Lean: localizedNegativeSobolevDecay) (2026-08-27 22:09 PDT)
\label{prop:dyadic-linfty-decay}: [Statement completed] (Lean: dyadicLInfinityDecay) (2026-08-27 22:09 PDT)

## The nondecaying endpoint and interpolation

Lean file: BourgainSmoothing/Auto/NondecayingEndpointAndInterpolation/NondecayingEndpointAndInterpolation.lean

### Definitions

None.

### Theorems

\label{lem:quadratic-average}: [Statement completed] (Lean: quadraticAveragingOperator) (2026-08-27 22:15 PDT)
\label{cor:l32-endpoint}: [Statement completed] (Lean: nondecayingLThreeHalvesEndpoint) (2026-08-27 22:15 PDT)
\label{prop:special-interpolation}: [Statement completed] (Lean: specialBilinearInterpolation) (2026-08-27 22:15 PDT)
\label{prop:dyadic-l2-decay}: [Statement completed] (Lean: dyadicL2Smoothing) (2026-08-27 22:15 PDT)

## Dyadic summation and proof of the main theorem

Lean file: BourgainSmoothing/Auto/DyadicSummationAndProofOfMainTheorem/DyadicSummationAndProofOfMainTheorem.lean

### Definitions

None.

### Theorems

\label{lem:l2-endpoint}: [Statement completed] (Lean: elementaryL2Endpoint) (2026-08-27 22:19 PDT)
\label{lem:weighted-dyadic-square}: [Statement completed] (Lean: weightedDyadicSquareEstimate) (2026-08-27 22:19 PDT)
\label{lem:geometric-summation}: [Statement completed] (Lean: geometricSummationConstant) (2026-08-27 22:19 PDT)
\label{lem:interaction-size-comparison}: [Statement completed] (Lean: interactionSizeComparison) (2026-08-27 22:19 PDT)
