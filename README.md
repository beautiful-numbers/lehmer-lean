# Lean 4 Formalization and Referee Audit for a Proposed Proof of Lehmer’s Totient Conjecture

## Overview

This repository accompanies the paper:

Paper: https://zenodo.org/records/18911153

The paper is the normative human-readable mathematical proof. It states a proof-complete, unconditional proof of Lehmer’s totient conjecture: there is no composite integer `n` such that `φ(n) | (n - 1)`. It also contains the finite Case C exhaustion witness as part of the logical argument.

The Lean repository formalizes and audits the proof architecture associated with the paper. It contains two complementary Lean verification targets:

1. the main mathematical pipeline;
2. the standalone referee/audit layer.

The main mathematical pipeline formalizes the mathematical taxonomy, branch/range predicates, closure packages, terminal interfaces, and global contradiction flow.

The standalone referee/audit layer, including `PierreDeFermat.lean`, provides an additional Lean-checked audit of the proof architecture. Its role is to expose and verify the referee-facing assembly of the already specified branch/range closure obligations. It is an audit endpoint, not the name of the main mathematical theorem.

AXLE artifacts provide an additional external certificate trail for selected referee-layer statements.

## Formal verification status

The repository is intended to be checked as a Lean project.

The expected integrity checks are:

- full `lake build`;
- targeted build of the main entrypoint;
- targeted build of the standalone audit/referee endpoint;
- no `sorry` in the main Lean development;
- no `admit`;
- no new project axioms;
- no hidden external oracle;
- exported statements inspected with `#check`;
- axiom dependencies inspected with `#print axioms`;
- branch/range closure obligations traced to their corresponding Lean endpoints;
- AXLE certificates checked for the selected referee-layer artifacts.

The main pipeline target and the audit/referee target have different mathematical roles.

`GlobalSplit.lean` and `Pipeline.Main` belong to the main mathematical pipeline. They verify the range taxonomy, global split, branch/range interfaces, and terminal pipeline interfaces.

`PierreDeFermat.lean` belongs to the standalone audit/referee target. It verifies the referee-facing assembly from stated range-closure obligations to the no-counterexample conclusion, adding an additional Lean-checked layer of unconditional-exhaustiveness audit.

A clean build verifies the Lean statements that were encoded. A full audit also inspects the exact theorem statements, definitions, closure endpoints, and axiom output.

### Current verification outputs

The following checks were run successfully on the repository.

Full project build:

````powershell
lake build
````

Result:

````text
Build completed successfully (16806 jobs).
````

Standalone audit/referee endpoint build:

````powershell
lake build Lehmer.Audit.PierreDeFermat
````

Result:

````text
Build completed successfully (8341 jobs).
````

Verification file build:

````powershell
lake build Lehmer.Verify
````

Result:

````text
Build completed successfully (8409 jobs).
````

Placeholder and project-local axiom scan, excluding AXLE statement files:

````powershell
Get-ChildItem -Path .\Lean -Recurse -Filter *.lean | Where-Object { $_.FullName -notmatch "\\Audit-axle\\" } | Select-String -Pattern "\bsorry\b|\badmit\b|\baxiom\b"
````

Result:

````text
No matches.
````

`Lean/Lehmer/Audit-axle/.../*.statement.lean` files are excluded from this scan because they are AXLE statement/specification files. Their `sorry` placeholders are intentional: each statement file is paired with a corresponding proof file and checked by AXLE.

### Exported statement and axiom checks

The file `Lean/Lehmer/Verify.lean` records `#check` and `#print axioms` checks for the main exported pipeline endpoints and the standalone audit/referee endpoints.

Main / final pipeline endpoints:

````lean
#check Lehmer.Final.main_theorem_of_pipeline_closure
#print axioms Lehmer.Final.main_theorem_of_pipeline_closure

#check Lehmer.Final.no_LehmerComposite_of_pipeline_closure
#print axioms Lehmer.Final.no_LehmerComposite_of_pipeline_closure

#check Lehmer.Final.no_composite_Lehmer_of_pipeline_closure
#print axioms Lehmer.Final.no_composite_Lehmer_of_pipeline_closure

#check Lehmer.Final.LehmerComposite_implies_false_of_pipeline_closure
#print axioms Lehmer.Final.LehmerComposite_implies_false_of_pipeline_closure
````

Lean output:

````text
Lehmer.Final.main_theorem_of_pipeline_closure
  (hcloseSmallA : ∀ {n : ℕ}, Lehmer.Basic.LehmerComposite n → Lehmer.Pipeline.InSmallPivotRange n → False)
  (hcloseB : ∀ {n : ℕ}, Lehmer.Basic.LehmerComposite n → Lehmer.Pipeline.InCaseB n → False)
  (hcloseI : ∀ {n : ℕ}, Lehmer.Basic.LehmerComposite n → Lehmer.Pipeline.InIntermediate n → False)
  (hcloseC : ∀ {n : ℕ}, Lehmer.Basic.LehmerComposite n → Lehmer.Pipeline.InCaseC n → False) {n : ℕ} :
  Lehmer.Basic.LehmerComposite n → False

'Lehmer.Final.main_theorem_of_pipeline_closure' depends on axioms:
[propext, Classical.choice, Quot.sound]

Lehmer.Final.no_LehmerComposite_of_pipeline_closure
  (hcloseSmallA : ∀ {n : ℕ}, Lehmer.Basic.LehmerComposite n → Lehmer.Pipeline.InSmallPivotRange n → False)
  (hcloseB : ∀ {n : ℕ}, Lehmer.Basic.LehmerComposite n → Lehmer.Pipeline.InCaseB n → False)
  (hcloseI : ∀ {n : ℕ}, Lehmer.Basic.LehmerComposite n → Lehmer.Pipeline.InIntermediate n → False)
  (hcloseC : ∀ {n : ℕ}, Lehmer.Basic.LehmerComposite n → Lehmer.Pipeline.InCaseC n → False) {n : ℕ} :
  ¬Lehmer.Basic.LehmerComposite n

'Lehmer.Final.no_LehmerComposite_of_pipeline_closure' depends on axioms:
[propext, Classical.choice, Quot.sound]

Lehmer.Final.no_composite_Lehmer_of_pipeline_closure
  (hcloseSmallA : ∀ {n : ℕ}, Lehmer.Basic.LehmerComposite n → Lehmer.Pipeline.InSmallPivotRange n → False)
  (hcloseB : ∀ {n : ℕ}, Lehmer.Basic.LehmerComposite n → Lehmer.Pipeline.InCaseB n → False)
  (hcloseI : ∀ {n : ℕ}, Lehmer.Basic.LehmerComposite n → Lehmer.Pipeline.InIntermediate n → False)
  (hcloseC : ∀ {n : ℕ}, Lehmer.Basic.LehmerComposite n → Lehmer.Pipeline.InCaseC n → False) {n : ℕ} :
  ¬Lehmer.Basic.LehmerComposite n

'Lehmer.Final.no_composite_Lehmer_of_pipeline_closure' depends on axioms:
[propext, Classical.choice, Quot.sound]

Lehmer.Final.LehmerComposite_implies_false_of_pipeline_closure
  (hcloseSmallA : ∀ {n : ℕ}, Lehmer.Basic.LehmerComposite n → Lehmer.Pipeline.InSmallPivotRange n → False)
  (hcloseB : ∀ {n : ℕ}, Lehmer.Basic.LehmerComposite n → Lehmer.Pipeline.InCaseB n → False)
  (hcloseI : ∀ {n : ℕ}, Lehmer.Basic.LehmerComposite n → Lehmer.Pipeline.InIntermediate n → False)
  (hcloseC : ∀ {n : ℕ}, Lehmer.Basic.LehmerComposite n → Lehmer.Pipeline.InCaseC n → False) {n : ℕ} :
  Lehmer.Basic.LehmerComposite n → False

'Lehmer.Final.LehmerComposite_implies_false_of_pipeline_closure' depends on axioms:
[propext, Classical.choice, Quot.sound]
````

Standalone audit/referee endpoints:

````lean
#check Lehmer.Audit.pierreDeFermat_of_range_closures
#print axioms Lehmer.Audit.pierreDeFermat_of_range_closures

#check Lehmer.Audit.no_LehmerComposite_of_range_closures
#print axioms Lehmer.Audit.no_LehmerComposite_of_range_closures

#check Lehmer.Audit.no_counterexample_of_range_closures
#print axioms Lehmer.Audit.no_counterexample_of_range_closures
````

Lean output:

````text
Lehmer.Audit.pierreDeFermat_of_range_closures
  (hSmall : ∀ (n : ℕ), Lehmer.Pipeline.InSmallPivotRange n → False)
  (hCaseC : ∀ (n : ℕ), Lehmer.Pipeline.InCaseC n → False)
  (hIntermediate : ∀ (n : ℕ), Lehmer.Pipeline.InIntermediate n → False)
  (hCaseB : ∀ (n : ℕ), Lehmer.Pipeline.InCaseB n → False) :
  Lehmer.Audit.PierreDeFermatStatement

'Lehmer.Audit.pierreDeFermat_of_range_closures' depends on axioms:
[propext, Classical.choice, Quot.sound]

Lehmer.Audit.no_LehmerComposite_of_range_closures
  (hSmall : ∀ (n : ℕ), Lehmer.Pipeline.InSmallPivotRange n → False)
  (hCaseC : ∀ (n : ℕ), Lehmer.Pipeline.InCaseC n → False)
  (hIntermediate : ∀ (n : ℕ), Lehmer.Pipeline.InIntermediate n → False)
  (hCaseB : ∀ (n : ℕ), Lehmer.Pipeline.InCaseB n → False) (n : ℕ) :
  ¬Lehmer.Basic.LehmerComposite n

'Lehmer.Audit.no_LehmerComposite_of_range_closures' depends on axioms:
[propext, Classical.choice, Quot.sound]

Lehmer.Audit.no_counterexample_of_range_closures
  (hSmall : ∀ (n : ℕ), Lehmer.Pipeline.InSmallPivotRange n → False)
  (hCaseC : ∀ (n : ℕ), Lehmer.Pipeline.InCaseC n → False)
  (hIntermediate : ∀ (n : ℕ), Lehmer.Pipeline.InIntermediate n → False)
  (hCaseB : ∀ (n : ℕ), Lehmer.Pipeline.InCaseB n → False) :
  ¬∃ n, Lehmer.Basic.LehmerComposite n

'Lehmer.Audit.no_counterexample_of_range_closures' depends on axioms:
[propext, Classical.choice, Quot.sound]
````

The `#print axioms` outputs above show no `sorryAx` and no project-local axioms for the listed exported endpoints. Only the standard Lean/mathlib axioms `propext`, `Classical.choice`, and `Quot.sound` appear.

### Current verification outputs

The following checks were run successfully on the repository.

Full project build:

````powershell
lake build
````

Result:

````text
Build completed successfully (16806 jobs).
````

Standalone audit/referee endpoint build:

````powershell
lake build Lehmer.Audit.PierreDeFermat
````

Result:

````text
Build completed successfully (8341 jobs).
````

Placeholder and project-local axiom scan, excluding AXLE statement files:

````powershell
Get-ChildItem -Path .\Lean -Recurse -Filter *.lean | Where-Object { $_.FullName -notmatch "\\Audit-axle\\" } | Select-String -Pattern "\bsorry\b|\badmit\b|\baxiom\b"
````

Result:

````text
No matches.
````

`Lean/Lehmer/Audit-axle/.../*.statement.lean` files are excluded from this scan because they are AXLE statement/specification files. Their `sorry` placeholders are intentional: each statement file is paired with a corresponding proof file and checked by AXLE.

## Repository structure

The repository is organized around three complementary components:

1. the main mathematical development;
2. the audit/referee development;
3. the AXLE-certified audit artifacts.

The main mathematical development lives under `Lean/Lehmer/...`.

This is where the arithmetic objects, candidate predicates, pivot definitions, branch predicates, closure packages, bridge interfaces, and terminal contradictions are defined.

Main components include:

- `Lean/Lehmer/Basic/...` — basic arithmetic and Lehmer-candidate infrastructure;
- `Lean/Lehmer/Pivot/...` — pivot definitions and pivot-side arguments;
- `Lean/Lehmer/Pipeline/...` — global range taxonomy and terminal pipeline interfaces;
- `Lean/Lehmer/CaseB/...` — Case B mathematical layer;
- `Lean/Lehmer/CaseC/...` — Case C mathematical layer and package-based closure machinery.

The audit/referee development lives under `Lean/Lehmer/Audit/...`.

It is Lean code checked by Lean. It exposes the proof flow in a structured way, reconstructs audit-facing artifacts, packages local closure information, and provides referee-style assembly points.

The audit layer is intentionally heterogeneous: different branches have different proof shapes, so their audit interfaces have different forms.

The AXLE artifacts provide an additional external certificate trail for selected referee-layer statements.

## Current global taxonomy

The current Lean pipeline uses a range-based global split exported by:

`Lean/Lehmer/Pipeline/GlobalSplit.lean`

The four current range branches are:

- `InSmallPivotRange`
- `InCaseC`
- `InIntermediate`
- `InCaseB`

The key taxonomy theorems are:

- `global_range_split_exhaustive`
- `every_LehmerComposite_is_range_classified`
- `range_taxonomy_exhaustive`

These theorems express that every `LehmerComposite n` is routed into one of the four current range branches.

This is a range-based pipeline taxonomy. The paper’s mathematical case structure and the current Lean top-level range split should be read with this distinction in mind.

## Build success and proof granularity

A clean Lean build means that Lean has checked the statements that were encoded.

For large formalizations, the strength of the encoded statements matters. A development can build cleanly while some objects are only labels, wrappers, routing objects, or high-level interfaces. Such objects may be useful, but their audit value depends on the proof obligations carried by their types.

A proof-carrying or responsibility-carrying format makes the relevant obligation explicit in the type. For example, an “emptiness” object carries the proof that every admissible object in the relevant domain leads to contradiction. A finite-reduction object carries coverage and descent obligations.

This distinction is the motivation for the referee/audit layer. The goal is to check that the paper-to-Lean translation has not reduced mathematical responsibilities to weak structural labels. The referee layer therefore audits whether the global split, branch/range obligations, closure interfaces, reconstruction data, and final assembly are represented in Lean with the intended proof-carrying content.

In this sense, the referee layer adds a second Lean-checked audit of the unconditional exhaustiveness already present in the paper and formalized in the main Lean development.

## How to read `PierreDeFermat.lean`

`Lean/Lehmer/Audit/PierreDeFermat.lean` is a standalone referee/audit file.

Its purpose is to audit the paper-to-Lean translation at the level of proof responsibilities. It checks, through the corresponding Lean endpoints, that the branch/range closure results used by the paper are present, routed, and assembled in the formal development.

The file should be read as an audit endpoint: it checks that the formal proof architecture is complete at the level of branch results, routing, coverage, closure obligations, and final assembly.

The mathematical branch proofs and closure packages live at their corresponding main-pipeline or branch/range endpoints. `PierreDeFermat.lean` audits that these endpoints fit together according to the proof architecture described in the paper.

The file contributes an additional Lean-checked audit layer for unconditional exhaustiveness. It checks that the branch/range closure results, represented by their corresponding endpoints, assemble with the global range split into the no-counterexample conclusion.

The relevant audit statements in this file are:

- `PierreDeFermatStatement`
- `pierreDeFermat_pointwise_of_range_closures`
- `pierreDeFermat_of_range_closures`
- `no_LehmerComposite_of_range_closures`
- `no_counterexample_of_range_closures`

## Assembly obligations

`PierreDeFermat.lean` consumes the following range-closure obligations as its referee-facing assembly inputs:

| Assembly input | Range closure |
|---|---|
| `hSmall` | closure of `InSmallPivotRange` |
| `hCaseC` | closure of `InCaseC` |
| `hIntermediate` | closure of `InIntermediate` |
| `hCaseB` | closure of `InCaseB` |

These inputs belong to the audit assembly interface. The corresponding mathematical closure responsibilities live at the branch/range endpoints in the main Lean development and audit layer.

## Pipeline closure interface

The terminal pipeline interface is exposed in:

`Lean/Lehmer/Pipeline/Main.lean`

The important objects are:

- `PipelineHandled`
- `RangePipelineExhaustive`
- `pipeline_range_taxonomy_complete`
- `pipeline_closes_all_cases_by_range_assumptions`
- `pipeline_closes_completed_caseA_and_remaining_ranges`
- `PipelineBridgeData`
- `pipeline_closes_all_cases_from_bridge_data`
- `pipeline_closes_all_cases`

The repository exposes both bundled and unbundled terminal interfaces.

`PipelineBridgeData` is a bundled convenience interface.

The final theorem interface in `Lean/Lehmer/Final/MainTheorem.lean` uses the unbundled theorem `pipeline_closes_all_cases_by_range_assumptions` directly. In that file, `IntermediateBridgeData` and `CaseCBridgeData` are built locally from the corresponding intermediate and Case C closure endpoints, while the small-pivot and Case B closures are passed directly.

The audit target is the terminal interface actually used by the final theorem. The closure inputs consumed by that interface should be traced to their branch/range endpoints.

## Branch and range objectives

### Small pivot / Case A side

Relevant file:

`Lean/Lehmer/Pipeline/CaseABridge.lean`

Case A is directly closed at the pipeline level.

Important objects:

- `CaseAHandled`
- `CaseAClosed`
- `caseA_impossible`
- `caseA_closed`
- `caseA_bridge_terminal`
- `caseA_bridge_terminal_of_falls`

This branch is closed using the imported pivot-layer contradiction.

The current global pipeline also keeps a legacy range predicate `InSmallPivotRange`. The mathematical Case A predicate `InCaseA` and the current small-pivot range interface `InSmallPivotRange` have distinct roles in the current pipeline.

### Case B side

Relevant file:

`Lean/Lehmer/Pipeline/CaseBBridge.lean`

The Case B bridge records that a candidate in the global Case B range is routed to the Case B mathematical layer.

Important objects:

- `CaseBHandled`
- `caseB_bridge`
- `caseB_bridge_of_falls`
- `caseB_handled_implies_in_caseB`
- `caseB_handled_iff_in_caseB`

Case B is decomposed into local states and closure stages. The audit layer exposes these stages in a structured way.

Typical Case B audit stages include:

- non-saturated state;
- gate-pass state;
- gate-fail state;
- local closure routing;
- terminal bridge;
- global no-crossing / contradiction endpoint.

The Case B branch should be reviewed through the Case B branch pipeline and its closure endpoint.

### Intermediate range

Relevant file:

`Lean/Lehmer/Pipeline/IntermediateBridge.lean`

The intermediate range is closed through explicit bridge data.

Important objects:

- `IntermediateBridgeData`
- `IntermediateHandled`
- `intermediate_bridge_terminal`
- `intermediate_impossible_of_bridge`
- `not_inIntermediate_of_LehmerComposite_bridge`

The bridge data provides a terminal closure theorem for every Lehmer candidate in the intermediate range. In the current unbundled final interface, this bridge data can be built directly from the intermediate closure endpoint.

### Case C side

Relevant file:

`Lean/Lehmer/Pipeline/CaseCBridge.lean`

Case C is package-based. A Case C candidate is handled through the Case C package interface: the branch endpoint constructs or exposes a complete `CaseCMainPackage`.

Important objects:

- `CaseCHandled`
- `CaseCBridgeData`
- `caseC_bridge`
- `caseC_bridge_terminal`
- `caseC_impossible_of_bridge`
- `not_inCaseC_of_LehmerComposite_bridge`

The terminal Case C bridge closes the branch by extracting a `CaseCMainPackage` and applying its pointwise impossibility theorem.

Case C has both:

- a mathematical terminal package in `Lean/Lehmer/CaseC/...`;
- an audit-facing reconstruction / closure layer in `Lean/Lehmer/Audit/CaseC...`.

The audit side reconstructs the ingredients consumed by the terminal contradiction and packages them into a closure-facing interface.

## Main pipeline and audit referee

The main pipeline and the audit referee have distinct roles.

The main pipeline provides:

- pivot taxonomy;
- branch/range predicates;
- range split;
- bridge interfaces;
- terminal pipeline closure.

The audit referee provides:

- audit-facing reconstruction artifacts;
- local closure packaging;
- branch/state routing where appropriate;
- final referee-facing assembly statements;
- an additional Lean-checked audit of unconditional branch/range exhaustiveness.

The verification ecosystem should be read as follows:

- the paper gives the human-readable unconditional proof;
- the main Lean layer formalizes the mathematical objects, branch/range predicates, closure packages, and terminal interfaces;
- the audit layer checks and exposes the referee-facing verification flow;
- the AXLE artifacts certify selected referee-layer statements.

This separation makes the proof architecture inspectable while keeping the mathematical branch proofs at their corresponding endpoints.

## AXLE-certified audit artifacts

AXLE certificates provide an additional external audit trail for selected referee-layer artifacts.

They should be interpreted relative to branch/range objectives: which artifact is certified, what role it plays in the branch/range pipeline, and how it feeds a closure endpoint.

AXLE adds a machine-checkable certificate trail for selected formal artifacts. In this project, AXLE is used after the Lean referee layer: the paper is proof-complete, the main Lean development formalizes the proof architecture, the referee layer audits the main development from a second Lean-facing perspective, and AXLE certifies selected referee-layer artifacts.

## Build

Standard build commands include:

- `lake build`
- `lake build Lehmer.Pipeline.GlobalSplit`
- `lake build Lehmer.Pipeline.Main`
- `lake build Lehmer.Audit.CaseAClosure`
- `lake build Lehmer.Audit.NonSaturatedCaseBClosure`
- `lake build Lehmer.Audit.CaseBGatePassClosure`
- `lake build Lehmer.Audit.CaseBGateFailClosure`
- `lake build Lehmer.Audit.CaseBClosure`
- `lake build Lehmer.Audit.CaseCClosure`
- `lake build Lehmer.Audit.PierreDeFermat`

On Windows PowerShell, if `lake` is not available on your `PATH`, use:

`& "$env:USERPROFILE\.elan\bin\lake.exe" build Lehmer.Audit.PierreDeFermat`

A targeted build checks the selected module and its dependencies. A full repository check should use:

`lake build`

A meaningful Lean review should also inspect the exact exported statements and run axiom checks on the relevant endpoints.

## Review procedure

A reliable review should:

1. Read the paper’s proof claim and global split.
2. Build the main Lean project.
3. Verify that the main Lean development has no `sorry`, no `admit`, and no new project axioms.
4. Identify the current Lean range taxonomy in `GlobalSplit.lean`.
5. Identify the terminal interface actually used.
6. Follow the branch/range endpoints.
7. Check how small pivot, Case B, intermediate, and Case C closures feed the relevant terminal interfaces.
8. Build the standalone audit/referee target `Lehmer.Audit.PierreDeFermat`.
9. Check how the consumed range closures feed the referee-facing audit assembly.
10. Run `#check` and `#print axioms` on the relevant exported endpoints.
11. Compare the Lean definitions with the paper definitions.
12. Check AXLE certificates relative to the artifacts they certify.

## Design principles

This repository follows these design principles:

- proof obligations live at the appropriate branch/range endpoint;
- assembly files expose final logical flow;
- bridge files are read according to their interface role;
- audit files make proof flow inspectable while remaining Lean-checked;
- branch decompositions remain explicit enough to distinguish structural interfaces from proof-carrying artifacts;
- paper, main Lean development, referee layer, AXLE artifacts, and assembly endpoints are distinct but connected parts of the same verification ecosystem.

## Repository goal

The goal of the project is to provide a proof-complete paper, a Lean formalization of the proof architecture, a standalone Lean referee/audit layer, and AXLE-certified audit artifacts.

In this organization:

- the paper gives the human-readable unconditional proof;
- the main Lean layer expresses the mathematical objects, branch predicates, packages, terminal interfaces, and global split;
- the audit layer expresses the referee-facing verification flow and adds a second Lean-checked audit of unconditional exhaustiveness;
- AXLE certifies selected referee-layer artifacts;
- the assembly files expose how global classification and branch/range closures yield the no-counterexample conclusion.
