---
name: autoformalize
description: Continue this repository's Lean formalization of `blueprint/blueprint.tex`, with faithful manuscript mappings, status tracking, and proof completion. Use for blueprint-directed work, not generic Lean development.
---

# Autoformalize

Use this skill to continue or repair the formalization represented by this repository's blueprint. Chat instructions override this skill and `meta/Instructions.md`.

## Establish the current state

- Work from the repository root. Read `meta/Instructions.md`, `meta/Status.md` when present, the relevant part of `blueprint/blueprint.tex`, existing `BourgainSmoothing/Auto/` sources, and the relevant working-tree diff before editing. Resume existing work and avoid duplicating it. If `meta/Status.md` is absent, initialize it from the scoped manuscript labels in manuscript order before choosing the next `Todo` item.
- The instruction's relative `../Auto/` work area is this project's `BourgainSmoothing/Auto/`. Put formalization sources there, in the single flat namespace `Auto`. Do not edit other Lean source files, except for the required explicit imports of permanent Auto sources in the top-level module, currently `BourgainSmoothing.lean`.
- Keep the Introduction intentionally narrow: inside its section folder, define the twisted averages and state the main twisted theorem in `Introduction.lean`. Keep that theorem as `sorry`; it is an explicit exception and must never be marked proof-complete. If this explicit scope conflicts with the active blueprint, surface the discrepancy before substituting a different definition or theorem.

## Organize the formalization

- Translate manuscript *theorems*, *lemmas*, and *propositions* into Lean `theorem` declarations. Treat a labeled corollary that is in scope as a theorem as well. If a labeled convention or another environment cannot clearly be classified as an in-scope definition or result, surface that scope decision instead of silently omitting or inventing formal content.
- Create one CamelCase folder for each top-level manuscript section and no folders for subsections. Put each leaf sub(sub)section in one appropriately named CamelCase Lean file, omitting articles from its filename. When a section has no sub(sub)sections, treat the section itself as its leaf.
- Add each newly created, non-temporary Lean source as an explicit import in the top-level module. Use scratch files only for temporary work; do not import them and delete them when they are no longer needed.
- Work through subsections in manuscript order. First formalize all in-scope definitions and theorem statements; temporary `sorry` proofs are allowed during this phase. Then prove theorems in appearance order, advancing only after the preceding theorem or independent batch is complete.

## Preserve the manuscript's meaning

- Formalize only notions from the manuscript. Every labeled manuscript definition and result needs a corresponding public Lean definition or theorem; use clear source-based names and suffixes when one result legitimately splits into several claims.
- Stay close to the mathematical wording. Add assumptions only when Lean semantics require them, such as measurability or `MemLp`; do so conservatively. Prefer an existing mathlib concept, theorem, or notation when it already expresses the intended content.
- Define explicit estimate constants as `def C_<lean theorem name> := ...`, preserving recursively specified constants from the manuscript. Implement operators as raw maps between functions unless a linear operator is genuinely intended, state operator properties propositionally, and use `eLpNorm` for Lp norms where possible.
- Use auxiliary definitions or theorems only when they genuinely help. Prefix them with `aux_`; they are not manuscript entries and need docstrings explaining their role.
- Ignore LaTeX comments and author annotations. If a definitive mathematical error appears, correct the formalization and record the dated timestamp, `blueprint.tex` source line, and issue in `meta/ErrorReport.md`. Do the same for an unjustifiable displayed constant when a slightly weaker directly proved bound is used. Do not report routine omitted graduate-level details as errors, and do not delay later work for a sharper unused bound.

## Write source-facing documentation

- Give the Lean declaration that formalizes a source definition or theorem a docstring containing the copied LaTeX definition or statement only -- never its proof -- and reformat it to render correctly with doc-gen4.
- Do not place a theorem's statement in a related definition or constant docstring. Instead, name the manuscript label and point to the public Lean theorem.
- Make `aux_` docstrings state their purpose and, when relevant, reference the source label and public theorem rather than duplicating a source statement.

## Track progress and synchronize the blueprint

- Maintain `meta/Status.md` continuously. Organize entries by source section and subsection, give every heading a `Lean file: PATH HERE` line, and include every in-scope labeled source definition and theorem -- never `aux_` names.
- Use exactly `\label{manuscript label}: [Status] (Lean: lean name) (Date and time of update)` for each entry. When a source result justifiably maps to several public Lean declarations, use a comma-separated Lean-name list in that position. Definition statuses are only `Todo` and `Completed`; theorem statuses are only `Todo`, `Statement completed`, and `Proof completed`.
- Mark a theorem `Proof completed` only when it has a sorry-free proof using standard axioms. Fix status inconsistencies when found.
- Whenever any status entry changes, use `$update-lean-metadata` to synchronize the label-adjacent `\lean{...}` and `\leanok` commands in `blueprint/blueprint.tex`. Do not infer statuses from the existing LaTeX metadata. If that skill finds missing metadata infrastructure or ambiguous adjacency, respect its diagnostic rather than hand-editing LaTeX macros or neighboring labels. Retain the accurate Status update, report metadata synchronization as blocked, and do not claim the two files agree until the infrastructure is repaired.

## Finish each work unit

- Check the affected Lean modules and imports, leave no temporary artifacts, and ensure the status and blueprint metadata agree with the actual formalization unless `$update-lean-metadata` reported a blocker.
- Report the completed manuscript labels, current proof status, any retained sorries, error-report or constant discrepancy, and any metadata diagnostic or blocked synchronization.
