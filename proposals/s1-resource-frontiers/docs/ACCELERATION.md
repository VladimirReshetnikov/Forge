# Exact productive-transition acceleration

Implemented option: `frontier(problem, accelerate=True)` or CLI `--accelerate`.
A transition qualifies when its production is componentwise >= consumption.
For target b, let r=consume and e=produce-consume. For positive e_i, choose H
large enough that b_i-H*e_i <= r_i; set H>=1. The predecessor plateau is r_i
when e_i>0 and max(r_i,b_i) when e_i=0. Use this one candidate instead of the
single-step predecessor, with a `repeat(step(t),H)` positive witness.

Why this preserves the exact result: the candidate is a genuine predecessor by
H repetitions and dominates (is <=) the ordinary one-step predecessor. At final
replay, the UNCHANGED checker checks closure against every ORIGINAL primitive
transition, plus the enabled repeated witness. The accelerator is not trusted.

Only single productive transitions are accelerated in this implementation. The
article proves a more general finite star-predecessor bound for an arbitrary
fixed macro; automatic macro discovery and that wider compiler are design work.

Executed ablation: 24 small productive nets have identical plain/accelerated
frontiers, with 396 versus 171 total candidate checks. At targets 10^4, 10^6,
and 10^100, the add-one net exhausts a 100-candidate plain budget but succeeds
with 2 accelerated candidates and a 3-node certificate. This is a comparison
between two modes of THIS Python prototype, not against any Lean tactic.
See results/acceleration-summary.json and acceleration-costs.json.
