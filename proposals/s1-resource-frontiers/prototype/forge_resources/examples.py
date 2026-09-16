"""Small, inspectable examples; these are not industrial benchmarks."""
from typing import Any


def problem(d: int, transitions: list[tuple[str, list[int], list[int]]],
            targets: list[list[int]]) -> dict[str, Any]:
    return {"kind": "pt-net-coverability", "dimension": d,
            "transitions": [{"name": n, "consume": c, "produce": p} for n, c, p in transitions],
            "targets": targets}


MUTEX = problem(3, [("enter", [1, 1, 0], [0, 0, 1]),
                    ("leave", [0, 0, 1], [1, 1, 0])], [[0, 0, 2]])
BROKEN_MUTEX = problem(3, [("enter_without_permit", [1, 0, 0], [0, 0, 1]),
                           ("leave", [0, 0, 1], [1, 1, 0])], [[0, 0, 2]])
UNBOUNDED_SAFE = problem(2, [("grow_output", [1, 0], [1, 1])], [[2, 0]])
EVEN_GROWTH = problem(1, [("add_two", [0], [2])], [[1]])
DEPLETION = problem(2, [("spend", [2, 0], [1, 1])], [[0, 1]])
STUTTER = problem(1, [("idle", [1], [1])], [[2]])
NO_TRANSITIONS = problem(2, [], [[2, 1], [1, 2]])

NAMED = {"mutex": MUTEX, "broken_mutex": BROKEN_MUTEX,
         "unbounded_safe": UNBOUNDED_SAFE, "even_growth": EVEN_GROWTH,
         "depletion": DEPLETION, "stutter": STUTTER, "no_transitions": NO_TRANSITIONS}
