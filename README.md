# Lean 4 Formalization and Referee Audit for a Proposed Proof of Lehmer’s Totient Conjecture

## Overview

This repository accompanies the paper:

Paper: https://zenodo.org/records/18911153

The paper is the normative human-readable mathematical proof. It states a proof-complete, unconditional proof of Lehmer’s totient conjecture: there is no composite integer `n` such that `φ(n) | (n - 1)`. It also contains the finite Case C exhaustion witness as part of the logical argument.

The Lean repository is the formalization and audit counterpart of that proof. The main Lean development formalizes the mathematical pipeline and its unconditional global split/closure structure. The audit/referee layer then checks that proof architecture from a second, referee-facing perspective and adds an additional Lean-checked audit of unconditional exhaustiveness.

The referee layer has also been certified through AXLE artifacts for selected audit-facing statements.

This repository should be reviewed as a formal Lean development with multiple verification targets, not by opening one final-facing assembly file and treating it as if it were supposed to contain every local branch proof internally.

## Formal verification status

The repository is intended to be checked as a Lean project, not only read as prose.

The expected integrity checks are:

- full `lake build`;
- no `sorry` in the main Lean development;
- no `admit`;
- no new project axioms;
- no hidden external oracle;
- exported statements inspected with `#check`;
- axiom dependencies inspected with `#print axioms`;
- branch/range closure obligations traced to their corresponding Lean endpoints;
- AXLE certificates checked for the selected referee-layer artifacts.

The main pipeline target and the audit/referee target should not be conflated. `GlobalSplit.lean` / `Pipeline.Main` belong to the main mathematical pipeline and verify the range taxonomy, global split, and terminal closure interfaces. `PierreDeFermat.lean` is a standalone audit/referee target: it checks the referee-facing final assembly from the stated range-closure obligations to the no-counterexample conclusion.

A clean build is necessary but not the whole audit: the exact theorem statements, definitions, closure endpoints, and axiom output must also be inspected.

The central Lean integrity question is not whether `PierreDeFermat.lean` alone contains every branch proof internally. It is whether the branch/range closure obligations consumed by the final assembly are discharged by the corresponding Lean endpoints, without `sorry`, `admit`, or new axioms.

## Repository structure

The repository is organized around three complementary components:

1. the main mathematical development;
2. the audit / referee development;
3. the AXLE-certified audit artifacts.

The main mathematical development lives under `Lean/Lehmer/...`.

This is where the arithmetic objects, candidate predicates, pivot definitions, branch predicates, closure packages, bridge interfaces, and terminal contradictions are defined.

Main components include:

- `Lean/Lehmer/Basic/...` — basic arithmetic and Lehmer-candidate infrastructure;
- `Lean/Lehmer/Pivot/...` — pivot definitions and pivot-side arguments;
- `Lean/Lehmer/Pipeline/...` — global range taxonomy and terminal pipeline interfaces;
- `Lean/Lehmer/CaseB/...` — Case B mathematical layer;
- `Lean/Lehmer/CaseC/...` — Case C mathematical layer and package-based closure machinery.

The audit / referee development lives under `Lean/Lehmer/Audit/...`.

Its role is not to replace the mathematical layer or Lean’s kernel. It is Lean code checked by Lean. It exposes the proof flow in a structured way, reconstructs audit-facing artifacts, packages local closure information, and provides final referee-style assembly points.

The audit layer is intentionally heterogeneous: different branches have different proof shapes, so their audit interfaces are different.

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

This is a range-based pipeline taxonomy. It should not be confused with a simplified A/B/C-only description of the paper. In particular, the current Lean top-level range split has four branches.

## Why a clean Lean build is not the whole audit

A clean Lean build means that Lean has checked the statements that were encoded. It does not, by itself, say that the encoded statements have the right granularity for the intended mathematical responsibility.

This is a central audit issue in large formalizations.

One can write a Lean development that builds without `sorry`, without `admit`, and without new axioms, while still proving only weak structural statements. For example, a file may define labels, wrappers, routing objects, or high-level interfaces that compile perfectly, but do not themselves carry the mathematical obligations suggested by their names.

In such a weak format, an object may say “emptiness”, “exclusion”, “closure”, or “finite reduction” without its type requiring the corresponding proof obligation. Lean will correctly verify the object, because the object only claimed to be a label or wrapper.

A stronger proof-carrying or responsibility-carrying format makes the obligation explicit in the type. For example, an “emptiness” object should not merely be tagged as emptiness; it should carry a proof that every admissible object in the relevant domain leads to contradiction. A finite-reduction object should not merely list children; it should carry coverage and descent obligations.

Both formats can build cleanly. They do not have the same audit value.

This is the “backbone theorem” failure mode. It is not a claim that Lean’s kernel is unsound. Lean checks exactly what is stated. The risk is that the statements are too coarse, too weak, or too interface-like to certify the intended mathematical responsibility.

The audit/referee layer exists precisely to make this distinction visible. It separates mere structural assembly from proof-carrying or responsibility-carrying artifacts, and it provides an additional Lean-checked audit of the unconditional exhaustiveness already present in the paper and formalized in the main Lean development.

The point is not to avoid checking closure obligations. The point is to check them at their actual branch/range endpoints, not by stopping at the final assembly file.

## How to read `PierreDeFermat.lean`

The distinction above is essential for reading the top-level audit file correctly.

`Lean/Lehmer/Audit/PierreDeFermat.lean` is a final assembly / audit file. Reading it alone shows the shape of the final global assembly:

range classification + range closures → no Lehmer composite.

This is not a defect by itself. It is the declared role of this file.

`PierreDeFermat.lean` is not meant to contain every branch proof internally. It identifies the closure obligations that are discharged by the branch/range pipelines and checks the final referee-facing assembly.

However, the fact that it is an assembly file is also not, by itself, the complete audit. This is where the granularity issue matters.

Because Lean can verify both weak interfaces and strong proof-carrying objects, the correct question is not simply whether `PierreDeFermat.lean` has inputs. The correct question is whether the inputs it consumes correspond downstream to sufficiently granular, proof-carrying, or responsibility-carrying closure artifacts.

Therefore, observing that `PierreDeFermat.lean` is an aggregator neither proves nor refutes the formalization. It identifies the final audit assembly point. A complete review traces each consumed closure obligation to its branch/range endpoint and checks the granularity of the proof data there.

The relevant endpoint statements in this file are:

- `PierreDeFermatStatement`
- `pierreDeFermat_pointwise_of_range_closures`
- `pierreDeFermat_of_range_closures`
- `no_LehmerComposite_of_range_closures`
- `no_counterexample_of_range_closures`

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

Therefore, the audit target is the terminal interface actually used by the final theorem. A reviewer should trace the closure inputs consumed by that interface to their branch/range endpoints.

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

This branch is not merely routed. It is closed using the imported pivot-layer contradiction.

The current global pipeline also keeps a legacy range predicate `InSmallPivotRange`. When reviewing the top-level range closure, distinguish the mathematical Case A predicate `InCaseA` from the current small-pivot range interface `InSmallPivotRange`.

### Case B side

Relevant file:

`Lean/Lehmer/Pipeline/CaseBBridge.lean`

The Case B bridge does not itself carry the mathematical proof. It records that a candidate in the global Case B range is routed to the Case B mathematical layer.

Important objects:

- `CaseBHandled`
- `caseB_bridge`
- `caseB_bridge_of_falls`
- `caseB_handled_implies_in_caseB`
- `caseB_handled_iff_in_caseB`

Case B is intentionally decomposed into local states and closure stages. The audit layer exposes these stages rather than duplicating the entire Case B mathematics in the bridge file.

Typical Case B audit stages include:

- non-saturated state;
- gate-pass state;
- gate-fail state;
- local closure routing;
- terminal bridge;
- global no-crossing / contradiction endpoint.

Do not conclude that Case B is missing merely because `CaseBBridge.lean` only routes. That file is a routing bridge. The Case B proof must be reviewed through the Case B branch pipeline and its closure endpoint, not from `CaseBBridge.lean` alone.

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

This separation is deliberate. The audit side reconstructs the ingredients consumed by the terminal contradiction and packages them into a closure-facing interface.

The audit question is not whether `CaseCBridge.lean` itself proves the entire finite exhaustion. The audit question is where the `CaseCMainPackage` is constructed or exposed, and whether that package carries the closure data required by the Case C endpoint.

## Main pipeline and audit referee

A key design choice of this repository is the distinction between the main pipeline and the audit referee.

The main pipeline provides the global classification machinery:

- pivot taxonomy;
- branch/range predicates;
- range split;
- bridge interfaces;
- terminal pipeline closure.

The audit referee exposes the proof flow in a structured way:

- it reconstructs audit-facing artifacts;
- it packages local closure arguments;
- it records branch/state routing where appropriate;
- it exposes final assembly statements;
- it provides a second Lean-checked audit of the unconditional branch/range exhaustiveness formalized by the main development.

The final audit-facing global theorem is intentionally separated from local branch mathematics:

- the paper gives the human-readable unconditional proof;
- the main Lean layer formalizes the mathematical objects, branch/range predicates, closure packages, and terminal interfaces;
- the audit layer checks and exposes the referee-facing verification flow;
- the AXLE artifacts certify selected referee-layer statements;
- the final referee theorem turns the global range split and closure obligations into a no-counterexample statement.

This separation is meant to make the proof architecture inspectable and to avoid hiding proof obligations inside a single opaque final file.

## AXLE-certified audit artifacts

AXLE certificates provide an additional external audit trail for selected referee-layer artifacts.

They should be interpreted relative to branch/range objectives: which artifact is certified, what role it plays in the branch/range pipeline, and how it feeds a closure endpoint.

AXLE does not replace the paper, Lean’s kernel, the main Lean formalization, or human mathematical review. It adds another machine-checkable audit trail for selected formal artifacts.

In this project, AXLE is used after the Lean referee layer: the paper is proof-complete, the main Lean development formalizes the proof architecture, the referee layer audits the main development from a second Lean-facing perspective, and AXLE certifies selected referee-layer artifacts.

## Do not review local artifacts in isolation

Some files expose local artifacts such as routing objects, traces, classifications, bridge data, reconstruction pieces, residual states, package components, or certificate components.

These local artifacts are nodes in a branch or range pipeline. They are not all intended to independently prove the whole theorem.

A review that opens one local file, observes that it only constructs a routing object, an existential artifact, or a bridge wrapper, and concludes that the proof is incomplete is not following the repository architecture.

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

A meaningful Lean review should also inspect the exact final statements and run axiom checks on the relevant exported theorems.

## Review procedure

A reliable review should:

1. Read the paper’s proof claim and global split.
2. Build the main Lean project.
3. Verify that the main Lean development has no `sorry`, no `admit`, and no new project axioms.
4. Identify the current Lean range taxonomy in `GlobalSplit.lean`.
5. Identify the terminal interface actually used.
6. Follow the branch/range objectives, not isolated files.
7. Check how small pivot, Case B, intermediate, and Case C closures feed the relevant terminal interfaces.
8. Build the standalone audit/referee target `Lehmer.Audit.PierreDeFermat`.
9. Check how the consumed range closures feed `PierreDeFermat.lean`.
10. Run `#check` and `#print axioms` on the relevant exported endpoints.
11. Compare the Lean definitions with the paper definitions.
12. Check AXLE certificates relative to the artifacts they certify.

If these steps have not been performed, the correct conclusion is:

“I have not audited enough of the paper, Lean development, referee layer, and AXLE artifacts to confirm or refute the claim.”

The following conclusion is not justified from partial inspection:

“The proof is conditional, incomplete, or merely a skeleton.”

## Design principles

This repository follows these design principles:

- proof obligations should live at the appropriate branch/range endpoint;
- assembly files should expose final logical flow rather than duplicate local mathematics;
- bridge files should be read according to their interface role;
- audit files should make proof flow inspectable without replacing Lean’s kernel;
- branch decompositions should remain explicit enough to prevent weak skeletons from being mistaken for proof-carrying artifacts;
- paper, main Lean development, referee layer, AXLE artifacts, and final assembly endpoints should be read as distinct but connected parts of the same verification ecosystem.

## Repository goal

The goal of the project is to provide a proof-complete paper, a Lean formalization of the proof architecture, a standalone Lean referee/audit layer, and AXLE-certified audit artifacts.

In this organization:

- the paper gives the human-readable unconditional proof;
- the main Lean layer expresses the mathematical objects, branch predicates, packages, terminal interfaces, and global split;
- the audit layer expresses the referee-facing verification flow and adds a second Lean-checked audit of unconditional exhaustiveness;
- AXLE certifies selected referee-layer artifacts;
- the final assembly files expose how global classification and branch/range closures yield the no-counterexample conclusion.
