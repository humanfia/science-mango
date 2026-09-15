# Stage 6 results — faithful occurrence-tag packing

All seven frozen targets passed Lean acceptance and combined compilation. Total accepted individual lemmas through stage 6: 37.

For each tuple, the tag counts earlier occurrences of the same residue. The packed exponents are injective even when residue coordinates repeat. Their image has cardinality w, each exponent is less than w*T, and the designated initial zero remains an anchor. Reduction of each exponent modulo T returns its original residue.

The anchor and tag-bound nodes needed two attempts; the other five passed on their first attempts. Full candidate and compiler histories are retained.

Polynomial quotient congruence and integration with CRT repair are separate next steps; no claim about the full M5 count or arithmetic algorithm is made by this batch.

[Assembled proof](experiment/AcceptedExperiment.lean), [acceptance receipt](experiment/result.json), [status DAG](experiment/GRAPH.md).
