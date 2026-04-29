-- FILE: Lean/Lehmer/Audit/README.lean
import Mathlib

/-
# Audit layer README

This file documents the role of the `Lehmer.Audit` namespace in the current
state of the development.

## Purpose

The audit layer does **not** add new arithmetic content to the proof.
Its purpose is to certify meta-level properties of the active Lean
development, in particular:

- which modules are normatively active in the current DAG;
- which taxonomic branches are explicitly present;
- which parts of the pipeline are already mathematically closed;
- which parts remain in a transition architecture.

The audit layer is therefore a **governance / coverage** layer, not a new
mathematical engine.

## Current audit files

### `Lehmer.Audit.DAGExhaustiveness`

This file certifies that the currently assembled active DAG is explicitly
accounted for.

Its job is to answer the question:

> "Are all normatively active modules of the current Lean development
> explicitly listed and covered?"

It is a certificate of **structural exhaustiveness of the active DAG**.

### `Lehmer.Audit.CaseAClosure`

This file certifies the local mathematical closure of Case A.

Its job is to answer the question:

> "Is mathematical Case A already closed in the current development?"

It exports the local audit theorem that no Lehmer composite can lie in
pipeline Case A.

### `Lehmer.Audit.CandidateCoverage`

This file certifies the current taxonomic coverage of the pipeline.

At the present transition stage:

- mathematical Case A is already closed locally;
- the exhaustive classification theorem still concerns the stable
  range-based split:
  - legacy small-pivot range,
  - Case C range,
  - intermediate range,
  - Case B range.

So `CandidateCoverage` currently certifies:

- exhaustiveness of the stable range taxonomy;
- handledness of the currently range-classified branches;
- presence of the active range branches;
- separate local closure of mathematical Case A;
- presence of all named global branches.

## Important architectural status

The current pipeline is in a **transition state**.

### What is already fully mathematical

- `Lehmer.Pivot.CaseAContradiction`
- `Lehmer.Pipeline.CaseABridge`
- `Lehmer.Audit.CaseAClosure`

These files certify that Case A is no longer merely a range condition:
it is a genuine mathematical contradiction branch.

### What is still range-based

The remaining global branches are still routed through the legacy pivot-range
taxonomy:

- small pivot range,
- Case C range,
- intermediate range,
- Case B range.

This means that current exhaustiveness in the audit layer is expressed at the
level of the stable range split, while Case A closure is recorded separately.

## What the audit layer currently certifies

At the current stage, the audit layer supports the following claims:

1. The active DAG is explicitly listed and covered.
2. The stable range taxonomy is exhaustive on Lehmer candidates.
3. Each named active range branch is present in the pipeline.
4. Mathematical Case A is already closed locally.
5. Every named global branch still has an explicit slot in the pipeline.

## What the audit layer does not currently claim

The audit layer does **not** yet claim that:

- the entire global pipeline taxonomy has been fully migrated to mathematical
  branch predicates for B / intermediate / C;
- all global branches are already closed by final branch-specific
  contradiction theorems;
- the final theorem of the whole development is already a purely mathematical
  case split with no remaining transition architecture.

Those stronger claims belong to a later stage of the refactor.

## Recommended reading order

For the current state of the project, the intended reading order is:

1. core mathematical files (`Basic/*`, `Pivot/*`);
2. local mathematical closure of Case A;
3. pipeline transition files;
4. audit files:
   - `DAGExhaustiveness`
   - `CaseAClosure`
   - `CandidateCoverage`

## Summary

The audit layer currently certifies that:

- the active Lean development is structurally accounted for;
- no active range branch is omitted;
- no Lehmer candidate is omitted from the current stable range taxonomy;
- Case A is already mathematically closed.

This is the correct audit reading of the present transition architecture.

-/
