# Stage44 results

All four prefix-partition targets passed the final frozen-target checks and combined assembly. Empty-prefix count equals total cardinality; at terminal length the count is one precisely for membership in the valid-word set; before terminal length, the counts of all next-letter branches sum to the parent count. The unique-next-letter prefix lemma supports the partition proof.

The initial run accepted two targets. Explicit finite-filter extensional equality repaired two decidability-instance mismatches; the terminal proof additionally identifies the singleton filter. The final replay retained the two accepted drafts and rechecked both repairs, each in one attempt. Original statements and count definition are unchanged. Initial failures, checked repairs and historical retrieval provenance are retained.

This is a semantic helper, not the definition of an arithmetic oracle. Actual C/A recovery must identify the original conditional formulas with this helper; stages46/47 carry that obligation.

[Accepted assembly](experiment/AcceptedExperiment.lean), [receipt](experiment/result.json), [DAG](experiment/GRAPH.md).
