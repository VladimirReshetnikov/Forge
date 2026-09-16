# Run history

## First named-example run: diagnostic failure

The initial reporting dictionary was built as:

    {'basis': basis_states, 'queries': queries, **search_stats}

The statistics also contained a key named `basis`, with the numeric basis size.
It overwrote the intended list. The following exact-basis assertion therefore
compared an integer against a list and failed. The generated semaphore
certificate already contained `[0,2,0]`, `[1,1,1]`, `[2,0,2]`.

The repair nested the statistics under `search_stats`. The original traceback
and run output remain in `results/failed-runs/01-*`. These are diagnostic
records, not acceptance receipts. The original failed script is not claimed
to be a separately preserved full source snapshot; this paragraph records the
specific one-line representation repair.

## Successful eager run

All named examples, local tests, complete finite execution oracles, 32 rejection
controls, four cutoff controls and 190 independent region replays completed.
The full suite was rerun after introducing the new direct-cover receipt type.
`results/run.log` and `results/summary.json` record that final run.

## Successful separation run

Both producers returned identical bases on the same 190 inputs. Three additional
constructed covered dense-preimage fixtures completed in the separation engine;
the eager engine returned unknown at its explicit 100,000-point grid limit.
Five additional direct-cover mutations were rejected. All 193 certificates
replayed in a fresh process that denied producer imports and disabled site
packages. Records are in `results/separation/`.

## CLI smoke checks

The separation CLI successfully searched and independently replayed the semaphore
model; output explicitly stated `lean_kernel_checked: false`. The stand-alone
checker accepted the stored dense-8 direct-cover certificate without search.

## Article build and inspection

The article was compiled with pdfLaTeX. An early layout pass found overlong
revision hashes and API names; breakable paths fixed them. The final build has
no overfull-box or unresolved-reference warnings. All pages were rendered to a
contact sheet and representative mathematical, tabular and bibliography pages
were inspected at reading resolution. Build intermediates and font files are
not part of the archive.
