# Sources and scope of review

Repository reads used the GitHub connector. Public documentation and primary academic sources were checked online in September 2026. This is a scoped capability review, not a whole-repository audit or build reproduction. No external source code or third-party paper is redistributed in this bundle.

## Forge baseline

Pinned commit: `58ea206bd7ad501b930add568151217bcc7f82a2`.

- [README](https://github.com/VladimirReshetnikov/Forge/blob/58ea206bd7ad501b930add568151217bcc7f82a2/README.md): layout, rounds, capabilities, and evidence qualifications.
- [STATUS](https://github.com/VladimirReshetnikov/Forge/blob/58ea206bd7ad501b930add568151217bcc7f82a2/docs/STATUS.md): executed, uncompiled, and designed-only boundaries.
- [Closure chapter](https://github.com/VladimirReshetnikov/Forge/blob/58ea206bd7ad501b930add568151217bcc7f82a2/article/sections/06-closure.tex): existing all-word matrix/ideal closure and finite certificates, used to distinguish this number-quantifier lane.
- [Boolean/external chapter](https://github.com/VladimirReshetnikov/Forge/blob/58ea206bd7ad501b930add568151217bcc7f82a2/article/sections/11-boolean-and-external.tex): existing proof-producing difference logic, higher-order and external-engine contracts.

The reviewed repository already records compiled core-only Lean files. Do not reinterpret this extension's `Lean NOT_RUN` as a statement that nothing in Forge has ever compiled. The repository status still says no installed `forge` tactic or verified reflected certificate layer is delivered.

## Companion repositories

- [Leant](https://github.com/VladimirReshetnikov/Leant): main README, source-checked synthesis and scope limitations.
- [Djex](https://github.com/VladimirReshetnikov/Djex): main README, source-owned typed graphs and bounded higher-rank search.

Branch references observed during review: Leant `6bf05ad78c467989e68290f2d08bbed40802d485`; Djex `e8778f4ebd63e1f9b9b410fa4de8d14a8a04c9e5`. READMEs were retrieved from the main-branch interface; these references do not establish a frozen compatible multi-repository build.

## Primary mathematical and software references

- Pierre Wolper and Bernard Boigelot, “An Automata-Theoretic Approach to Presburger Arithmetic Constraints,” SAS 1995, LNCS 983, 21–32. [Author archive](https://orbi.uliege.be/handle/2268/74877), [DOI](https://doi.org/10.1007/3-540-60360-3_30).
- Hamoon Mousavi, *Automatic Theorem Proving in Walnut*, 2016, revised 2021. [arXiv:1603.06017](https://arxiv.org/abs/1603.06017).
- Jeffrey Shallit, [Walnut project and documentation index](https://cs.uwaterloo.ca/~shallit/walnut.html). Walnut was not run in the delivered experiments.
- Zhaobo (Aeacus) Sheng, *Formally Verifying Automata for Trusted Decision Procedures*, Carnegie Mellon University master's thesis, May 2025. [Primary PDF](https://www.andrew.cmu.edu/user/avigad/Students/sheng_ms.pdf).
- [Aeacu2/Automata](https://github.com/Aeacu2/Automata), pinned inspected commit `8b5fb2dd7e4f32e17f6c4dd43f2d8980649ebc42`: README, `lean-toolchain`, `Automata/Projection.lean` (including `project_iff`), and `Automata/Addition.lean`. Projection handles leading-zero conventions distinct from this bundle's LSBF zero suffixes. The toolchain file pins Lean 4.23.0. This dependency was not compiled here; absence of an atomic theorem in the inspected addition file is not a claim about every other file in that repository.
- Mathlib [DFA documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/DFA.html) and [NFA documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/NFA.html): semantic API, finite-state qualifications, and determinization correctness. These rolling docs require a fresh compatibility check against the chosen pinned Lean/Mathlib environment before implementation.

## Claim boundaries

The classical automata method, least choice via ordering, language closure operations, and padding correction are not claimed as new mathematical discoveries. The delivered contribution is an executable, certificate-producing arithmetic and witness lane proposed for the reviewed Forge architecture. Original code and experiments are in `prototype/` and `results/`; the Lean port remains a design with specific acceptance gates.
