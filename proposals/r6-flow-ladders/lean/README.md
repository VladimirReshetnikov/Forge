# Lean acceptance targets — NOT COMPILED

`FlowTargets.lean` supplies ten named proposition definitions for a future
implementation. It does not prove them, invoke Forge, or contain a checker.
The file was not compiled in this environment; no Lean compiler was available.

A real acceptance run must import the eventual implementation and prove the
original propositions through its source-bound certificate adapter. Merely
compiling these definitions would still not constitute certificate acceptance.

Concrete candidate Mathlib imports and theorem names are documented in the
article's Lean implementation section. They were inspected in current API docs,
not compiled against Forge's exact pin. The first required general theorem is
the scalar integrating-factor rule; the first end-to-end goal should be
`symmetric`, with its four-step rational certificate.
