# Acceptance ledger

| Item | Status | Evidence / remaining gate |
|---|---|---|
| Four exact algorithm implementations | Executed | `prototype/`; recorded deterministic run |
| Constant and polynomial multiplier packets | Python checked | 51 and 14 stored certificates |
| Finite covers and concrete counterexample trees | Python checked | 136 certificates; independent closure oracle |
| Symbolic integer projection | Python checked | 221 certificates; 3,400 concrete differential valuations |
| Unit tests | Passed | 21 methods; 19 explicit certificate mutations |
| Search-free replay | Passed | `verify.py` disables search entry points |
| Python implementation formal verification | Not done | Shared representation and assembler are documented |
| Mathematical format soundness | Proved in article | Induction, coefficient identities, guarded CRT |
| Lean specimens | NOT_RUN | No Lean executable; `lean/status.json` |
| Source reification and native checker integration | Designed only | Complete checked source theorems required |
| Original Leant indexing query | Not attempted here | Fold/List specimen is not a substitute |
| Simultaneous two-universe query | Not attempted here | Remains a separate target |
| Comparison with grind or other tactics | Not run | Requires a matched Lean benchmark |

Empty invariant packets are valid preservation certificates but not certified
maximality results and not refutations of the user's goal. Finite-algebra negative
certificates apply to the exact input algebra; an abstract bad state is not a
source counterexample without a checked concretization.
