# Lean metadata synchronization diagnostic

Date: 2026-08-28 18:10 PDT

## Inputs

- Blueprint: `blueprint/blueprint.tex`
- Status: `meta/Status.md`
- Updated label: `\label{lem:interaction-size-comparison}`
- Lean theorem: `interactionSizeComparison`

## Validation performed

- Confirmed that the blueprint label occurs exactly once.
- Confirmed that Status records the public Lean theorem name.
- Built `BourgainSmoothing.Auto.DyadicSummationAndProofOfMainTheorem.DyadicSummationAndProofOfMainTheorem`.
- Audited `Auto.interactionSizeComparison`; it depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- Searched the blueprint for label-adjacent `\lean{...}` and for `\leanok` metadata.

## Blocker

The blueprint contains neither `\lean{...}` declarations nor `\leanok` metadata, so there is no supported blueprint-side annotation to synchronize.  The project instructions prohibit inventing or hand-editing unsupported blueprint metadata.

## Action taken

Updated Status to mark the theorem proof completed.  The blueprint was intentionally left unchanged.
