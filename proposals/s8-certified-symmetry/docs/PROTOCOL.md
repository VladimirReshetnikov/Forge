# Certificate protocol and caller obligations

All generator arrays act on 0,...,n-1. Composition `mul(a,b)` applies b first. Coloring and exponent-vector action moves the value at coordinate i to coordinate g[i]. Problem objects are authoritative caller inputs, not claims supplied by certificates.

## Chain v1

Problem: `{"degree":n,"generators":[permutation_array,...]}`.

Certificate fields are exactly `format`, `word_dag`, `strong`, `levels`, `order`, with format `forge.symmetry.chain.v1`.

DAG operators: `["id"]`, `["gen",original_index]`, `["inv",earlier_index]`, `["mul",earlier_a,earlier_b]`. All strong roots are evaluated from the original generators. Nonidentity original generators must occur in the strong list; the list is distinct and contains no identity.

The complete base is 0,...,n-1. Each orbit tree begins `[level,null,null]`. Other rows are `[point,earlier_parent,signed_strong_index]`; signed indices are one-based, with negative indices denoting inverses. The checker reconstructs transversals, checks prefix fixing, all orbit closure edges, and all Schreier residues. The order must be the exact product of orbit sizes. No partial-base format is implemented.

## Canonical v1

The problem coloring is an external array of nonnegative integer colors. The certificate has `format`, `best`, `transporter`, `cover`. Its format is `forge.symmetry.canonical.v1`. A cover node is `["cut"]` or `["split",children]`. Child cosets are derived from the checked chain, in its table order. Every child must be present. The point-orbit lower bound is recomputed independently. The transporter must be a member of the original group and send the source to `best`.

## Family v1 and canonical-family v1

`{"format":"forge.symmetry.family.v1","family":"S"}` requires order n!. Family A requires n>=2, exact order n!/2, and even original generators. A family image certificate has format `forge.symmetry.canonical-family.v1` and fields `family`, `best`, `transporter`. Its least-image rule is checked separately from reachability.

## Burnside v1

Fields: `format`, `order`, `inventory`, with format `forge.symmetry.burnside.v1`. Each inventory row is `[sorted_cycle_lengths,positive_count]`. Fixed points contribute length-one cycles. The checker enumerates the group's unique normal forms, not the producer's Cayley-graph search, and compares the complete inventory. Unrestricted colors and fixed binary weight are implemented. General constraint-preserving coloring counts are not.

## Reynolds v1

External polynomial terms are strictly sorted rows `[exponent_vector,nonzero_integer_numerator,positive_denominator]`, with fractions in lowest terms. A certificate has `format`, `orbits`, `output`, format `forge.symmetry.reynolds.v1`.

Each orbit is a tree whose root `[exponent_vector,null,null]` must occur in the source support. Nonroot rows use an earlier parent and a **zero-based original generator index**, not the signed strong-generator convention of chain trees. Exponents are exact nonnegative integers. All points are distinct, components are disjoint, all generator images remain in the component, and every original support monomial is covered. Output coefficients must be the source coefficient sum on the component divided by its cardinality. Zero output terms are omitted. The different edge-label conventions are intentional and validated per format.

## Outcomes and implementation limits

`InvalidCertificate` rejects malformed or mathematically insufficient data. `CheckLimit` and producer `SearchLimit` mean unknown due to a resource bound. The producer's input-degree ceiling is 256 while the checker's default is 128; default accepted end-to-end degree is therefore at most 128. Default word-node cap is 200,000; Schreier work cap is 5,000,000; general explicit enumeration cap is 100,000; image cover cap is 200,000; monomial cap is 100,000. Individual experiments may select tighter bounds.

JSON mathematical numbers must be integers; rationals use integer pairs. Duplicate keys, JSON floats, and NaN are rejected by `load_json`. Timing diagnostics are separate and may contain floats. This is research software, not a hardened hostile-input parser. The caller should additionally cap input bit lengths, total memory, elapsed time, and recursive nesting before production exposure.

A Python `VerifiedChain` is not an unforgeable authority. Only a future Lean soundness theorem applied to the original source obligation can close a Lean goal. The monomial-orbit theorem needs validated generator bijections, not a group-order proof; the present API reuses the checked-chain object for convenience.
