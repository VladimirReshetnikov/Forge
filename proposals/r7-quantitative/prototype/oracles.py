"""Small independent test oracles; never used to admit a certificate."""
from fractions import Fraction as Q
from itertools import combinations


def determinant(a):
    n = len(a)
    if n == 0:
        return Q(1)
    if n == 1:
        return a[0][0]
    return sum(((-1)**j)*a[0][j]*determinant([r[:j]+r[j+1:] for r in a[1:]])
               for j in range(n))


def reach_vertices(problem):
    """Enumerate vertices of the bounded supersolution polytope, via Cramer.

    Independent of policy enumeration and of the producer's Gaussian solver.
    Intended for at most three non-target states.
    """
    actions = [[[Q(x) for x in r] for r in ch] for ch in problem['actions']]
    targets = set(problem['target'])
    active = [s for s in range(len(actions)) if s not in targets]
    d, constraints = len(active), []  # a.x >= b
    for i, s in enumerate(active):
        unit = [Q(i == j) for j in range(d)]
        constraints += [(unit, Q(0)), ([-x for x in unit], Q(-1))]
        for row in actions[s]:
            constraints.append(([Q(s == t)-row[t] for t in active],
                                sum(row[t] for t in targets)))
    best = None
    for chosen in combinations(constraints, d):
        a, b = [x[0] for x in chosen], [x[1] for x in chosen]
        det = determinant(a)
        if not det:
            continue
        v = []
        for j in range(d):
            replaced = [r[:j]+[b[i]]+r[j+1:] for i, r in enumerate(a)]
            v.append(determinant(replaced)/det)
        if all(sum(x*y for x, y in zip(row, v)) >= bound for row, bound in constraints):
            if best is None or sum(v) < sum(best):
                best = v
    if best is None:
        raise ArithmeticError('supersolution polytope unexpectedly empty')
    out = [Q(s in targets) for s in range(len(actions))]
    for s, v in zip(active, best):
        out[s] = v
    return out


def integer_transport(left_counts, right_counts, cost, allowed):
    """Enumerate integer contingency tables; return exact cost / total mass.

    Integral marginal capacities have an integral optimum. The tiny oracle
    explores tables rather than residual graphs or dual potentials.
    """
    n, m, allowed = len(left_counts), len(right_counts), set(allowed)
    best = None
    def visit(k, rows, cols, value):
        nonlocal best
        if k == n*m:
            if not any(rows) and not any(cols) and (best is None or value < best):
                best = value
            return
        i, j = divmod(k, m)
        maximum = min(rows[i], cols[j]) if (i, j) in allowed else 0
        values = [rows[i]] if j == m-1 else range(maximum+1)
        for x in values:
            if x > maximum:
                continue
            rr, cc = list(rows), list(cols)
            rr[i] -= x
            cc[j] -= x
            if j == m-1 and rr[i]:
                continue
            visit(k+1, rr, cc, value+x*Q(cost[i][j]))
    visit(0, list(left_counts), list(right_counts), Q(0))
    return None if best is None else best/sum(left_counts)


def bisim_partition(problem):
    """Disjoint-union probability-to-block partition refinement (no couplings)."""
    p, q = problem['left'], problem['right']
    n, m = len(p), len(q)
    rows = [[Q(x) for x in r]+[Q(0)]*m for r in p]
    rows += [[Q(0)]*n+[Q(x) for x in r] for r in q]
    labels = problem['obs_left']+problem['obs_right']
    def classify(keys):
        seen, result = {}, []
        for key in keys:
            if key not in seen:
                seen[key] = len(seen)
            result.append(seen[key])
        return result
    blocks = classify(labels)
    while True:
        keys = [(blocks[s], tuple(sum(rows[s][t] for t in range(n+m) if blocks[t] == b)
                  for b in range(max(blocks)+1))) for s in range(n+m)]
        new = classify(keys)
        if new == blocks:
            break
        blocks = new
    i, j = problem['start']
    return blocks[i] == blocks[n+j]


def poly_value(v, n):
    return sum(Q(a)*Q(n)**k for k, a in enumerate(v))


def stopped_cost_check(problem, cert, start=3, horizon=10):
    """Explicit finite path-distribution evolution and telescoping identity."""
    mass, total = {start: Q(1)}, Q(0)
    jumps, probs = problem['jumps'], list(map(Q, problem['probabilities']))
    original = poly_value(cert['potential'], start)
    for _ in range(horizon):
        total += sum(p*poly_value(problem['cost'], s) for s, p in mass.items() if s > 0)
        new = {}
        for s, p in mass.items():
            if s == 0:
                new[0] = new.get(0, Q(0))+p
            else:
                for j, probability in zip(jumps, probs):
                    new[s+j] = new.get(s+j, Q(0))+p*probability
        mass = new
        if total > original:
            return False
        remainder = sum(p*poly_value(cert['potential'], s) for s, p in mass.items())
        if total+remainder != original:
            return False
    return True


def total_variation(p, q):
    return sum(abs(Q(x)-Q(y)) for x, y in zip(p, q))/2


def trace_law(kernel, labels, start, observations):
    """Explicit observation-prefix distribution; used only on tiny test chains."""
    if observations < 1:
        return {(): Q(1)}
    current={(start,(labels[start],)):Q(1)}
    for _ in range(observations-1):
        new={}
        for (s,word),mass in current.items():
            for t,prob in enumerate(kernel[s]):
                if Q(prob):
                    key=(t,word+(labels[t],))
                    new[key]=new.get(key,Q(0))+mass*Q(prob)
        current=new
    out={}
    for (s,word),mass in current.items():out[word]=out.get(word,Q(0))+mass
    return out
