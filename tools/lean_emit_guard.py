"""The boundary between certificate DATA and generated Lean CODE.

WHY THIS EXISTS. Every exporter in this repository reads a JSON bundle and
writes a Lean file. Four of them interpolated the bundle's record id --
untrusted data -- directly into a Lean doc comment. An id containing `-/`
closes the comment, and whatever follows is compiled as Lean. An adversarial
review reproduced a generated corpus that compiles cleanly and proves
`(1 : Int) = 2` from an injected `axiom injected_ax : False`, and the same attack
was then reproduced on tools/export_lean_cone.py.

The Lean checkers themselves were never at fault: every real corpus theorem
still depended only on propext and Quot.sound. But a generated file that
declares `axiom ... : False` poisons everything that imports it, and Gate 2 of
the design names "mutation rejection AT THE DATA BOUNDARY" as an exit
criterion. A certificate may be wrong and be rejected; it must never be able to
become code.

TWO DEFENCES, deliberately redundant.

  validate_ids   Record ids must be plain identifiers. Anything else is refused
                 BEFORE emission, as are empty ids and ids that collide after
                 sanitisation (`a-b` and `a_b` both become `a_b`).

  audit          After emission, the generated text is scanned for anything a
                 certificate corpus has no business containing: `axiom`,
                 `sorry`, `admit`, `native_decide`, `unsafe`, `implemented_by`,
                 `extern`, `ofReduceBool`, `opaque`, `macro`, `elab`, `syntax`,
                 `run_cmd`, `#eval`, `initialize`. Comments are stripped first,
                 with a depth counter because Lean block comments nest, so a
                 docstring that merely MENTIONS `native_decide` is not a hit --
                 the same lesson as this repository's sorry scanner, which once
                 flagged a file for the sentence denying it had any.

Either defence alone would have stopped the reproduced attack. The audit also
catches injection routes nobody has thought of yet, which is the point of
having it.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_lean import strip_lean_comments  # noqa: E402

IDENT = re.compile(r"^[A-Za-z][A-Za-z0-9_]*$")

FORBIDDEN = [
    "axiom", "sorry", "admit", "native_decide", "unsafe", "implemented_by",
    "extern", "ofReduceBool", "opaque", "macro", "macro_rules", "elab",
    "elab_rules", "syntax", "run_cmd", "run_tac", "#eval", "initialize",
    "builtin_initialize", "debug.skipKernelTC",
]
FORBIDDEN_RE = re.compile(r"(?<![A-Za-z0-9_.'])(" + "|".join(
    re.escape(w) for w in FORBIDDEN) + r")(?![A-Za-z0-9_'])")


class UnsafeEmission(ValueError):
    """Raised instead of writing a Lean file that could contain injected code."""


def validate_ids(ids, what: str = "record id") -> None:
    """Refuse ids that are not plain identifiers, or that collide."""
    seen: dict[str, str] = {}
    for raw in ids:
        if not isinstance(raw, str) or not raw:
            raise UnsafeEmission("%s must be a non-empty string, got %r" % (what, raw))
        if not IDENT.match(raw):
            raise UnsafeEmission(
                "%s %r is not a plain identifier ([A-Za-z][A-Za-z0-9_]*). It is "
                "interpolated into generated Lean, so it is refused rather than "
                "escaped." % (what, raw))
        if raw in seen:
            raise UnsafeEmission("duplicate %s %r" % (what, raw))
        seen[raw] = raw


def validate_label(value: str, allowed, what: str) -> None:
    """For strings that are not ids but still reach generated text (families)."""
    if value not in allowed:
        raise UnsafeEmission("%s %r is not one of %s" % (what, value, sorted(allowed)))


def audit(text: str, source: str = "generated Lean") -> None:
    """Refuse generated Lean that contains anything a certificate corpus must not."""
    code = strip_lean_comments(text)
    hits = sorted({m.group(1) for m in FORBIDDEN_RE.finditer(code)})
    if hits:
        raise UnsafeEmission(
            "%s contains forbidden construct(s) %s outside comments; refusing to "
            "write it. A certificate corpus declares data and proves theorems by "
            "`decide` and ordinary tactics, and nothing else." % (source, hits))


def write_checked(path: Path, text: str) -> None:
    """Audit, then write. The only way the exporters should emit Lean."""
    audit(text, str(path))
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
