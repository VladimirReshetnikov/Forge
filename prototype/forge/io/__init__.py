"""Serialisation boundary: hardened decoding and Lean source emission.

NOTE ON LAYOUT: the requested target layout placed this package at the top level
as `io/`. That is impossible in CPython -- `io` is imported during interpreter
bootstrap, so `sys.modules['io']` is always the standard library module and a
top-level `io` package can never be imported (`import io.decode` fails with
"'io' is not a package"). It therefore lives at `forge/io/`, which is importable
as `forge.io.decode` / `forge.io.lean` and shadows nothing.
"""
from . import decode  # noqa: F401

__all__ = ['decode', 'lean']
