"""Standalone certificate checker; imports no search code or third-party library.

This is ordinary Python, NOT a formally verified checker or a Lean proof.
Malformed input raises InvalidCertificate; resource refusal raises CheckLimit.
The caller supplies the problem independently of the certificate.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from collections import Counter, deque
from itertools import product
from math import factorial, comb
import json
from pathlib import Path
from typing import Any, Iterator

class InvalidCertificate(ValueError):
    pass

class CheckLimit(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise InvalidCertificate(message)


def integer(value: Any, *, lower: int = 0, upper: int | None = None) -> int:
    require(type(value) is int, "integer required (Booleans and floats are forbidden)")
    require(value >= lower and (upper is None or value <= upper), "integer out of bounds")
    return value


def shape(value: Any, keys: set[str]) -> None:
    require(type(value) is dict and set(value) == keys, "unexpected object schema")


def sequence(value: Any, maximum: int) -> list[Any]:
    require(type(value) is list, "list required")
    if len(value) > maximum:
        raise CheckLimit("list length budget exceeded")
    return value


def load_json(path: str | Path, max_bytes: int = 16_000_000) -> Any:
    """Reject duplicate keys, non-finite constants, JSON floats, and huge files."""
    path = Path(path)
    if path.stat().st_size > max_bytes:
        raise CheckLimit("JSON byte budget exceeded")
    def pairs(entries: list[tuple[str, Any]]) -> dict[str, Any]:
        result = {}
        for key, value in entries:
            require(key not in result, "duplicate JSON object key")
            result[key] = value
        return result
    def forbidden(_: str) -> None:
        raise InvalidCertificate("non-integer JSON number")
    try:
        return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=pairs,
                          parse_float=forbidden, parse_constant=forbidden)
    except (json.JSONDecodeError, UnicodeError, RecursionError) as exc:
        raise InvalidCertificate("malformed or excessively nested JSON") from exc


def _permutation(raw: Any, n: int) -> tuple[int, ...]:
    sequence(raw, n)
    require(len(raw) == n, "wrong permutation degree")
    seen = [False] * n
    for value in raw:
        integer(value, upper=n - 1)
        require(not seen[value], "duplicate permutation image")
        seen[value] = True
    return tuple(raw)


# Intentionally different implementation from producer.mul / producer.inv.
def _compose(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    output = []
    for position in range(len(a)):
        output.append(a[b[position]])
    return tuple(output)


def _inverse(p: tuple[int, ...]) -> tuple[int, ...]:
    inverse_map = {target: source for source, target in enumerate(p)}
    return tuple(inverse_map[target] for target in range(len(p)))


def _act(p: tuple[int, ...], source: tuple[int, ...]) -> tuple[int, ...]:
    result = [0] * len(p)
    for old, new in enumerate(p):
        result[new] = source[old]
    return tuple(result)


@dataclass
class VerifiedChain:
    """A Python result object, not an unforgeable authority or a Lean proof."""
    degree: int
    generators: tuple[tuple[int, ...], ...]
    strong: tuple[tuple[int, ...], ...]
    tables: tuple[dict[int, tuple[int, ...]], ...]
    order: int
    schreier_checks: int
    _inverse_tables: tuple[dict[int, tuple[int, ...]], ...] = field(repr=False)

    def sift(self, raw: list[int] | tuple[int, ...], start: int = 0) -> tuple[bool, int, tuple[int, ...]]:
        p = _permutation(list(raw), self.degree)
        integer(start, upper=self.degree)
        for level in range(start, self.degree):
            image = p[level]
            if image not in self.tables[level]:
                return False, level, p
            p = _compose(self._inverse_tables[level][image], p)
        return p == tuple(range(self.degree)), self.degree, p

    def contains(self, p: list[int] | tuple[int, ...]) -> bool:
        return self.sift(p)[0]

    def normal_forms(self, max_order: int = 100_000) -> Iterator[tuple[int, ...]]:
        if self.order > max_order:
            raise CheckLimit("normal-form enumeration budget exceeded")
        identity = tuple(range(self.degree))
        for factors in product(*(list(t.values()) for t in self.tables)):
            value = identity
            for factor in factors:
                value = _compose(value, factor)
            yield value


def verify_chain(problem: Any, certificate: Any, *, max_degree: int = 128,
                 max_words: int = 200_000, max_checks: int = 5_000_000) -> VerifiedChain:
    shape(problem, {"degree", "generators"})
    n = integer(problem["degree"])
    if n > max_degree:
        raise CheckLimit("degree budget exceeded")
    generators = tuple(_permutation(g, n) for g in sequence(problem["generators"], 1024))
    identity = tuple(range(n))
    shape(certificate, {"format", "word_dag", "strong", "levels", "order"})
    require(certificate["format"] == "forge.symmetry.chain.v1", "unsupported certificate format")
    raw_nodes = sequence(certificate["word_dag"], max_words)
    require(bool(raw_nodes) and raw_nodes[0] == ["id"], "identity DAG root missing")
    values = []
    for k, node in enumerate(raw_nodes):
        sequence(node, 3)
        require(bool(node) and type(node[0]) is str, "invalid DAG operator")
        op = node[0]
        if op == "id":
            require(len(node) == 1, "identity node arity")
            value = identity
        elif op == "gen":
            require(len(node) == 2, "generator node arity")
            index = integer(node[1], upper=len(generators) - 1)
            value = generators[index]
        elif op == "inv":
            require(len(node) == 2, "inverse node arity")
            index = integer(node[1], upper=k - 1)
            value = _inverse(values[index])
        elif op == "mul":
            require(len(node) == 3, "product node arity")
            a = integer(node[1], upper=k - 1)
            b = integer(node[2], upper=k - 1)
            value = _compose(values[a], values[b])
        else:
            raise InvalidCertificate("unknown DAG operator")
        values.append(value)
    strong = tuple(values[integer(k, upper=len(values) - 1)]
                   for k in sequence(certificate["strong"], 4096))
    require(identity not in strong and len(set(strong)) == len(strong),
            "strong generators must be distinct and nonidentity")
    require(all(g == identity or g in strong for g in generators),
            "an original generator is missing from the strong list")
    signed: dict[int, tuple[int, ...]] = {}
    for j, g in enumerate(strong):
        signed[j + 1], signed[-j - 1] = g, _inverse(g)
    levels = sequence(certificate["levels"], n)
    require(len(levels) == n, "the complete base is required")
    tables = []
    for level, edges in enumerate(levels):
        sequence(edges, n - level)
        require(bool(edges), "orbit tree is empty")
        sequence(edges[0], 3)
        require(len(edges[0]) == 3, "orbit root arity")
        require(integer(edges[0][0], upper=n - 1) == level and
                edges[0][1] is None and edges[0][2] is None,
                "orbit root must be the base point")
        points = [level]
        transversals = [identity]
        table = {level: identity}
        for j, edge in enumerate(edges[1:], 1):
            sequence(edge, 3)
            require(len(edge) == 3, "orbit edge arity")
            point = integer(edge[0], upper=n - 1)
            parent = integer(edge[1], upper=j - 1)
            label = integer(edge[2], lower=-len(strong), upper=len(strong))
            require(label != 0, "zero signed-generator label")
            s = signed[label]
            require(all(s[k] == k for k in range(level)), "edge generator moves an earlier base point")
            require(point not in table, "duplicate orbit point")
            transversal = _compose(s, transversals[parent])
            require(transversal[level] == point, "orbit edge has a wrong image")
            require(all(transversal[k] == k for k in range(level)), "transversal leaves stabilizer")
            points.append(point)
            transversals.append(transversal)
            table[point] = transversal
        tables.append(table)
    inverse_tables = tuple({x: _inverse(p) for x, p in t.items()} for t in tables)
    order = 1
    for table in tables:
        order *= len(table)
    require(integer(certificate["order"], lower=1) == order, "wrong order product")
    result = VerifiedChain(n, generators, strong, tuple(tables), order, 0, inverse_tables)

    # EVERY Schreier edge is covered, not a supplied subset or a random sample.
    for level in range(n):
        allowed = set(s for s in signed.values() if all(s[k] == k for k in range(level)))
        for s in allowed:
            for x, tx in tables[level].items():
                result.schreier_checks += 1
                if result.schreier_checks > max_checks:
                    raise CheckLimit("Schreier verification budget exhausted")
                y = s[x]
                require(y in tables[level], "orbit is not closed under a strong generator")
                residual = _compose(inverse_tables[level][y], _compose(s, tx))
                require(result.sift(residual, level + 1)[0], "a Schreier generator does not sift to identity")
    return result


def _orbit_minima(chain: VerifiedChain, source: tuple[int, ...]) -> list[tuple[int, ...]]:
    """Independent graph traversal, not the producer's union-find algorithm."""
    rows = []
    for level in range(chain.degree + 1):
        allowed = [g for g in chain.strong if all(g[k] == k for k in range(level))]
        remaining = set(range(chain.degree))
        row = [0] * chain.degree
        while remaining:
            start = min(remaining)
            orbit = {start}
            queue = deque([start])
            while queue:
                x = queue.popleft()
                for g in allowed:
                    y = g[x]
                    if y not in orbit:
                        orbit.add(y)
                        queue.append(y)
            low = min(source[x] for x in orbit)
            for x in orbit:
                row[x] = low
            remaining.difference_update(orbit)
        rows.append(tuple(row))
    return rows


def verify_canonical(chain: VerifiedChain, colors: Any, certificate: Any,
                     *, max_nodes: int = 200_000) -> dict[str, Any]:
    sequence(colors, chain.degree)
    require(len(colors) == chain.degree, "wrong source coloring degree")
    source = tuple(integer(x) for x in colors)
    shape(certificate, {"format", "best", "transporter", "cover"})
    require(certificate["format"] == "forge.symmetry.canonical.v1", "wrong canonical format")
    sequence(certificate["best"], chain.degree)
    require(len(certificate["best"]) == chain.degree, "wrong best-image degree")
    best = tuple(integer(x) for x in certificate["best"])
    transporter = _permutation(certificate["transporter"], chain.degree)
    require(chain.contains(transporter), "transporter is outside the original generated group")
    require(_act(transporter, source) == best, "transporter does not produce the claimed image")
    minima = _orbit_minima(chain, source)
    pending = [(0, tuple(range(chain.degree)), certificate["cover"])]
    seen = cuts = 0
    while pending:
        level, prefix, tree = pending.pop()
        seen += 1
        if seen > max_nodes:
            raise CheckLimit("coset-cover node budget exceeded")
        sequence(tree, 2)
        if tree == ["cut"]:
            require(_act(prefix, minima[level]) >= best, "unsound coset pruning bound")
            cuts += 1
        else:
            require(len(tree) == 2 and tree[0] == "split", "unknown coset-cover node")
            require(level < chain.degree, "split past the complete base")
            children = sequence(tree[1], len(chain.tables[level]))
            require(len(children) == len(chain.tables[level]), "incomplete coset cover")
            for transversal, child in zip(chain.tables[level].values(), children):
                pending.append((level + 1, _compose(prefix, transversal), child))
    return {"best": list(best), "nodes": seen, "cuts": cuts}


@dataclass(frozen=True)
class VerifiedInventory:
    degree: int
    order: int
    inventory: tuple[tuple[tuple[int, ...], int], ...]

    def count_colors(self, q: int) -> int:
        integer(q)
        total = sum(count * q ** len(lengths) for lengths, count in self.inventory)
        require(total % self.order == 0, "Burnside numerator not divisible by group order")
        return total // self.order

    def count_binary_weight(self, weight: int) -> int:
        integer(weight)
        if weight > self.degree:
            return 0
        numerator = 0
        for lengths, count in self.inventory:
            coefficients = [1] + [0] * weight
            for length in lengths:
                for j in range(weight, length - 1, -1):
                    coefficients[j] += coefficients[j - length]
            numerator += count * coefficients[weight]
        require(numerator % self.order == 0, "weighted numerator not divisible")
        return numerator // self.order

    def polynomial_numerator(self) -> list[list[int]]:
        result: Counter[int] = Counter()
        for lengths, count in self.inventory:
            result[len(lengths)] += count
        return [[power, value] for power, value in sorted(result.items())]


def verify_burnside(chain: VerifiedChain, certificate: Any, *, max_order: int = 100_000) -> VerifiedInventory:
    shape(certificate, {"format", "order", "inventory"})
    require(certificate["format"] == "forge.symmetry.burnside.v1", "wrong Burnside format")
    require(integer(certificate["order"], lower=1) == chain.order, "wrong census denominator")
    supplied = []
    for row in sequence(certificate["inventory"], max_order):
        sequence(row, 2)
        require(len(row) == 2, "cycle inventory row arity")
        lengths = tuple(integer(x, lower=1, upper=chain.degree) for x in sequence(row[0], chain.degree))
        require(tuple(sorted(lengths)) == lengths and sum(lengths) == chain.degree, "invalid cycle partition")
        count = integer(row[1], lower=1, upper=chain.order)
        supplied.append((lengths, count))
    require(supplied == sorted(supplied) and len({x for x, _ in supplied}) == len(supplied),
            "cycle inventory must be canonical")
    require(sum(count for _, count in supplied) == chain.order, "incomplete cycle inventory")
    actual: Counter[tuple[int, ...]] = Counter()
    # Producer enumerates by BFS; checker enumerates unique stabilizer digits.
    for g in chain.normal_forms(max_order):
        visited = [False] * chain.degree
        lengths = []
        for start in range(chain.degree):
            if visited[start]:
                continue
            point, length = start, 0
            while not visited[point]:
                visited[point] = True
                length += 1
                point = g[point]
            require(point == start, "malformed cycle traversal")
            lengths.append(length)
        actual[tuple(sorted(lengths))] += 1
    require(supplied == sorted(actual.items()), "cycle census disagrees with exact group normal forms")
    return VerifiedInventory(chain.degree, chain.order, tuple(supplied))


@dataclass(frozen=True)
class VerifiedFamily:
    degree: int
    family: str

    def count_colors(self, q: int) -> int:
        integer(q)
        n = self.degree
        if n == 0:
            return 1
        multisets = comb(q + n - 1, n) if q else 0
        if self.family == "S":
            return multisets
        return multisets + (comb(q, n) if q >= n else 0)


def verify_family(chain: VerifiedChain, certificate: Any) -> VerifiedFamily:
    shape(certificate, {"format", "family"})
    require(certificate["format"] == "forge.symmetry.family.v1", "wrong family format")
    family = certificate["family"]
    if family == "S":
        require(chain.order == factorial(chain.degree), "group is not the full symmetric group")
    elif family == "A":
        require(chain.degree >= 2, "alternating count formula requires degree at least two")
        require(2 * chain.order == factorial(chain.degree), "wrong alternating group order")
        for g in chain.generators:
            inversions = sum(g[i] > g[j] for i in range(chain.degree) for j in range(i + 1, chain.degree))
            require(inversions % 2 == 0, "an input generator is odd")
    else:
        raise InvalidCertificate("unsupported symbolic counting family")
    return VerifiedFamily(chain.degree, family)


def verify_cnf_symmetry(chain: VerifiedChain, clauses: Any, weights: Any = None) -> bool:
    """A deliberately narrow syntactic automorphism gate for concrete CNF.

    This is NOT the proposed Lean Expr reifier.  It accepts only unsigned
    variable permutations, retaining literal polarity and objective weights.
    """
    def normalize(raw: Any) -> tuple[tuple[int, ...], ...]:
        output = set()
        for clause in sequence(raw, 100_000):
            literals = []
            for literal in sequence(clause, 2 * chain.degree):
                integer(literal, lower=-chain.degree, upper=chain.degree)
                require(literal != 0, "CNF variables are one-based")
                literals.append(literal)
            output.add(tuple(sorted(set(literals))))
        return tuple(sorted(output))
    original = normalize(clauses)
    if weights is not None:
        sequence(weights, chain.degree)
        require(len(weights) == chain.degree, "wrong objective dimension")
        require(all(type(w) is int for w in weights), "objective weights must be exact integers")
    for g in chain.generators:
        renamed = [[(1 if literal > 0 else -1) * (g[abs(literal) - 1] + 1)
                    for literal in clause] for clause in original]
        require(normalize(renamed) == original, "generator does not preserve the CNF")
        if weights is not None:
            require(all(weights[i] == weights[g[i]] for i in range(chain.degree)),
                    "generator does not preserve the objective")
    return True


def verify_canonical_family(chain: VerifiedChain, colors: Any, certificate: Any) -> dict[str, Any]:
    shape(certificate, {"format", "family", "best", "transporter"})
    require(certificate["format"] == "forge.symmetry.canonical-family.v1", "wrong family-image format")
    family = verify_family(chain, {"format": "forge.symmetry.family.v1", "family": certificate["family"]})
    sequence(colors, chain.degree)
    require(len(colors) == chain.degree, "wrong source-coloring degree")
    source = tuple(integer(c) for c in colors)
    expected = sorted(source)
    # With repeated colors an odd stabilizer allows either transporter parity.
    # With distinct colors the least wrong-parity image swaps the last two.
    if family.family == "A" and len(set(source)) == chain.degree:
        parity = sum(source[i] > source[j] for i in range(chain.degree) for j in range(i + 1, chain.degree)) % 2
        if parity:
            expected[-2], expected[-1] = expected[-1], expected[-2]
    sequence(certificate["best"], chain.degree)
    require(len(certificate["best"]) == chain.degree, "wrong claimed-image degree")
    best = [integer(x) for x in certificate["best"]]
    require(best == expected, "family shortcut claims the wrong minimum")
    transporter = _permutation(certificate["transporter"], chain.degree)
    require(chain.contains(transporter), "family transporter is outside the generated group")
    require(list(_act(transporter, source)) == best, "family transporter has the wrong image")
    return {"best": best, "family": family.family}
