"""Finite bases for infinite state spaces: the fourth round's antichain workers.

PROVENANCE
  orders        s1 + s3 + s4   Dickson and Higman orders, the antichain, the
                               predecessor formula --- each written once, where
                               the three proposals each wrote their own
  nets          s1 + s3 + s4   place/transition nets, finite-control counter
                               systems, matrix-update systems, lossy FIFO
  summaries     s1             compressed-run algebra and a hash-consed run DAG
  search        s1 + s3 + s4   one backward loop, four predecessor rules
  certificates  s1 + s3 + s4   every checker, no search code

WHAT THE MERGE REMOVED. Four of the fourth round's nine proposals do backward-
antichain coverability, the largest single-subject cluster in the collection.
They share one well-quasi-order argument, one antichain, one predecessor
formula and one saturation loop; between them they wrote each of those four
things three or four times. Here each appears once, and what differs --- the
model languages and their predecessor rules --- is what the code still spells
out separately.

Three of those proposals also independently computed the SAME three-element
mutual-exclusion antichain, verified identical under a coordinate bijection.
It appears once, in the tests, and is labelled as one result.

NOT MERGED HERE, and deliberately:

  s2's irrational least fixed points of probabilistic polynomial systems are
  not a well-structured transition system at all; they share the word
  "coverability" with s1 and nothing else. Run them from proposals/s2.

  s3's equality-register transducers owe their finiteness to the Bell numbers
  rather than to any well-quasi-order, which is worth keeping distinct rather
  than filing under Dickson's lemma. Run them from proposals/s3.

  s4's separation receipts over the full lossy-FIFO language need the producer's
  region search; only the checker is here. Run the search from proposals/s4.

Everything in this subpackage is standard library only, search included, so all
of it runs under `python -S`. certificates.py imports neither search.py nor
summaries.py, which is checkable by inspection and is checked by the tests.
"""
from . import orders, nets, summaries, search, certificates  # noqa: F401

__all__ = ['orders', 'nets', 'summaries', 'search', 'certificates']
