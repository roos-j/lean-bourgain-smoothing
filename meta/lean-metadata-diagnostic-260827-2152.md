# Lean metadata synchronization diagnostic

Date and time: 2026-08-27 21:52 PDT

## Inputs

- Blueprint: `blueprint/blueprint.tex`
- Status source: `meta/Status.md`

## Status update checked

- `prop:gowers-differencing` is now `Statement completed` as
  `gowersDifferencing`.
- `lem:separation-selection` is now `Statement completed` as
  `separationSelection`.
- `prop:u3-control` is now `Statement completed` as `u3Control`.

## Checks performed

- Re-read the changed entries and exact source labels in `meta/Status.md`.
- Confirmed that all 45 status labels still match exactly one scoped labeled
  environment in `blueprint/blueprint.tex`.
- Searched the selected blueprint for label-adjacent `\\lean{...}` and
  `\\leanok` commands and their macro definitions.

## Issue and action

The blueprint has no Lean-metadata command or macro infrastructure. Adding
the required `\\lean{...}` commands for the three non-`Todo` labels would create
undefined LaTeX commands.

No blueprint metadata was changed. Synchronization remains blocked until the
missing metadata infrastructure is supplied; the Status entries accurately
record the checked Lean declarations.
