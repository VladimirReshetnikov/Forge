# Uncompiled Lean specimens

No Lean/Lake executable was available for this study. These files are explicitly **uncompiled**. They contain no reflected certificate checker and no implemented `forge` tactic.

`CoreComposition.lean` illustrates the logical witness and postcondition-composition rules. `SourceExamples.lean` gives hand-written proofs of the corner and critical-pair consequences, importing Mathlib. They clarify target statements and do not replace the requested future source-to-certificate bridge.

To test them in an existing compatible Lean/Mathlib project, run `lake env lean` with the path to the specimen, using that project's environment. The reviewed Forge baseline names Lean v4.34.0 and Mathlib `1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`; this package does not claim to have built at those pins.
