/-
This audit layer is a standalone Lean referee target.

It does not replace the main mathematical pipeline. Its role is to expose and
check the referee-facing assembly and audit artifacts built from the current
branch/range closure architecture.

The main proof architecture is provided by the paper and the main Lean
development. The audit layer adds an additional Lean-checked exhaustiveness
audit over selected proof-flow artifacts.
-/
