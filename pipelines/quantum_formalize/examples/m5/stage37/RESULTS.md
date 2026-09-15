# Stage37 results

All four residue-recovery targets and combined assembly passed. The recursive algorithm scans residues in order, preserves positive completion count under the partition identity, and returns a valid terminal assignment under the terminal-count specification. It performs at most m*T candidate tests; m=2*(w-1) gives the original bound. Attempts: pick_bound 1, pick_positive 1, recover_success 3, recover_valid 1.

Actual conditional-A partition and terminal specifications still need to instantiate this generic theorem.

[Accepted assembly](experiment/AcceptedExperiment.lean), [receipt](experiment/result.json), [DAG](experiment/GRAPH.md).
