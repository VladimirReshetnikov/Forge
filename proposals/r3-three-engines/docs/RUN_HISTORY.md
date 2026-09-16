# Execution notes

The final deterministic suite was run with seed 20260915 under Python 3.13.5, using only standard-library packages (`python -S`). The recorded final outcome is in `results/run.log` and `results/summary.json`.

During development the complete suite passed before additional analytic bound/coverage mutation cases were added. The expanded suite then passed with 180/81/81 rejected mutations. The final files are the authoritative recorded suite; the earlier shorter mutation run is not a separate benchmark.

Automatic jet discovery was added as an overlapping search profile for the four existing jet goals. Its source problems and checked results are preserved in `results/jet-discovery.json`; orders 2/2/2/3 were found. Independent replay with search imports blocked passed for both the main certificate file and this separate profile.

The named unit suite passed. Optional mpmath point sanity checks passed and remain outside certificate acceptance.

No failed full algorithmic suite run was reclassified as accepted. An initial PDF build encountered a TeX package load-order collision (`openbox`); the package ordering was repaired before the final render. That formatting issue has no bearing on algorithmic evidence.

No Lean compilation, GAP run, Arb run, Leant run, Djex run, or head-to-head Lean tactic evaluation was performed.
