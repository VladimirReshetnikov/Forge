# Preserved first failure: CHSH source self-adjointness

The first experiment run stopped while constructing the CHSH worked receipt.
The initial target was `8 - S*S`, where
`S = A*(B+C) + D*(B-C)` and the cross-pair commutation relations were premises.
As an unreduced free-word polynomial, `S` is not syntactically self-adjoint.
The operator producer's syntactic entrance gate returned no certificate.

Investigation found that the proposed positive-square identity reduced to zero
modulo the supplied relation span. The failure was therefore at the entrance
contract, not a failed exact linear solve. The fix retained the self-adjointness
gate: the operator target became `8 - star(S)*S`, while a separate equality
receipt proves `S = star(S)` under the cross-commutations.

The final version also generates the ray dictionary from recognized involution
and cross-commutation relations, rather than supplying the three factors by hand.
A regression test retains the original syntactic boundary, and a separate test
runs the repaired example under all 24 atom renamings.

`results/initial-failure.log` is the actual failed initial run. Its line numbers
refer to that initial source version, not the final edited file. The current
experiment command is expected to pass; it does not intentionally replay the
old failure. This note prevents the retained historical log from being confused
with a current test failure.
