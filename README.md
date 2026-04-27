# Pierre de Fermat in Lean

Formalisation in Lean 4 of a structured contradiction strategy around Lehmer candidates, with a clear separation between:

- the **main mathematical pipeline**
- the **audit / referee layer**
- the final top-level referee theorem `PierreDeFermat`

## Project structure

The repository is organized in two large layers.

### 1. Main mathematical layer

The core mathematical development lives under `Lean/Lehmer/...`.

This is where the actual objects, branch predicates, closure packages, and terminal contradictions are defined.

Main components:

- `Lehmer/Basic/...`  
  basic arithmetic and candidate infrastructure
- `Lehmer/Pivot/...`  
  pivot definitions and local pivot-side arguments
- `Lehmer/Pipeline/...`  
  global pipeline taxonomy and range split
- `Lehmer/CaseA/...`  
  Case A mathematics
- `Lehmer/CaseB/...`  
  Case B mathematics
- `Lehmer/CaseC/...`  
  Case C mathematics

This layer contains the mathematical proof objects that the audit layer later consumes.

### 2. Audit / referee layer

The verification layer lives under `Lean/Lehmer/Audit/...`.

Its role is not to redefine the mathematics, but to:

- expose the proof flow in a structured, inspectable way
- split local branches into explicit audit states
- package local closure arguments
- aggregate already-closed branches
- provide a final referee-style contradiction theorem

Typical audit files are split by local state and closure stage. For example in Case B:

- non-saturated state
- gate-pass state
- gate-fail state
- local closure aggregators
- top-level Case B closure aggregator

For Case C, the audit layer reconstructs the ingredients consumed by the terminal contradiction and packages them into a closure-facing interface.

## Main pipeline vs audit referee

A key design choice of this repository is the distinction between:

### Main pipeline

The main pipeline lives in the mathematical layer and provides the global classification machinery.

In particular:

- the global pivot taxonomy
- the branch predicates
- the range split used by the global argument

This is the mathematical backbone of the proof.

### Audit referee

The audit side replays the proof in a structured way and consumes the already-constructed closure results.

The final audit-facing global theorem is intentionally separated from the main pipeline theorem:

- the pipeline defines the branch structure
- the audit layer verifies that each relevant branch is closed
- the final referee theorem turns that branch closure into a contradiction statement

This makes the global proof easier to inspect, maintain, and refactor.

## Final theorem

The final top-level audit file is:

- `Lean/Lehmer/Audit/PierreDeFermat.lean`

Its role is to aggregate the globally closed branches and derive the final contradiction statement.

Conceptually:

1. the global pipeline classifies a Lehmer candidate into one of the global branches
2. each relevant branch has already been closed by the corresponding proof layer
3. the audit layer packages this into the final no-counterexample statement

So `PierreDeFermat.lean` should be read as a **referee / aggregator theorem**, not as the place where the branch mathematics is developed from scratch.

## Case B note

Case B is intentionally decomposed into several local audit states.

The important point is that `CaseBClosure.lean` is meant to remain thin:

- it should only aggregate the already-closed local Case B states
- it should not duplicate the mathematics of those states
- it should not reintroduce high-level proof machinery already handled downstream

In the current architecture, the three local Case B closures are:

- non-saturated
- gate-pass
- gate-fail

and the top-level Case B closure should simply consume them.

## Case C note

Case C has both:

- a mathematical terminal contradiction in the main layer
- an audit-facing reconstruction / closure layer

This means the project distinguishes carefully between:

- the mathematical terminal package (`Lehmer/CaseC/...`)
- the audit reconstruction and closure interface (`Lehmer/Audit/CaseC...`)

That separation is deliberate: the audit side acts as a referee-facing packaging of the already-proved Case C contradiction pipeline.

## Build

Standard build commands:

```powershell
lake build Lehmer.Audit.CaseAClosure
lake build Lehmer.Audit.NonSaturatedCaseBClosure
lake build Lehmer.Audit.CaseBGatePassClosure
lake build Lehmer.Audit.CaseBGateFailClosure
lake build Lehmer.Audit.CaseBClosure
lake build Lehmer.Audit.CaseCClosure
lake build Lehmer.Audit.PierreDeFermat
```

If a targeted build fails because some dependencies have not yet been built cleanly, run:

```powershell
lake build
```

On Windows PowerShell, if lake is not available on your PATH, use:

```powershell
& "$env:USERPROFILE\.elan\bin\lake.exe" build Lehmer.Audit.PierreDeFermat
```

## Design principles

This repository follows a few explicit principles:

- **thin aggregators**: top-level closure files should consume already-closed states, not redo local proofs
- **clear namespace separation**: avoid generic names in shared audit namespaces when branch-specific names are intended
- **mathematics first, audit second**: the audit layer packages and verifies the proof flow rather than replacing the main mathematics
- **refactor-friendly decomposition**: branch closures are split into small files to make local changes safer

## Status

This is an active formalization/refactor project.

In particular, the audit layer is organized so that:

- each local state closes independently
- aggregators remain minimal
- the final theorem `PierreDeFermat` acts as a clean referee-facing endpoint

## Repository goal

The goal of the project is not only to formalize the contradiction argument, but also to make the proof architecture readable:

- the **main layer** expresses the mathematics
- the **audit layer** expresses the verification flow
- the **final theorem** packages the global contradiction cleanly
