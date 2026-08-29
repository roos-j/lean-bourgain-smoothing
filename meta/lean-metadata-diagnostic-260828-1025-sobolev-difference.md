# Lean metadata synchronization diagnostic

Date: 2026-08-28 10:25 PDT

## Inputs

- Blueprint: blueprint/blueprint.tex
- Status source: meta/Status.md
- Updated labels: thm:sobolev-difference, cor:sobolev-difference-s1

## Validation performed

- Confirmed that each updated label occurs exactly once in the canonical
  blueprint.
- Confirmed that the updated status entries name the corresponding public Lean
  theorems `sobolevDifferenceEstimate` and `sobolevDifferenceEstimateS1`.
- Searched the blueprint for label-adjacent `\lean{...}` / `\leanok` commands
  and for definitions of those macros.

## Blocker

The blueprint has neither label-adjacent Lean metadata commands nor definitions
for the required macros. The metadata workflow forbids adding global LaTeX
infrastructure or hand-editing neighboring source, and adding the commands
would leave the blueprint with undefined LaTeX macros.

## Action taken

`meta/Status.md` was updated to `Proof completed`. No change was made to
`blueprint/blueprint.tex`; metadata synchronization remains blocked until the
missing infrastructure is supplied.
