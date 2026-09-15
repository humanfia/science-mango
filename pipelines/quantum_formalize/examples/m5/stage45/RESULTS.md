All four finite period-search targets accepted; combined assembly, unchanged environment and experiment passed.

The search explicitly takes the smallest N in the finite interval 1..2^natDegree F satisfying F dividing M_N. Under the original monic and constant-one assumptions, the candidate set is nonempty, the returned value belongs to it, and finiteSearch F equals signaturePeriod F. For F=1, finiteSearch returns1.

This validates the original bounded arithmetic period-search step; it does not impose a generated-runtime/codegen or efficiency goal. Repeated factors remain allowed.

Attempts: {"candidate_nonempty": 1, "finite_search_member": 1, "finite_search_eq_period": 1, "finite_search_one": 1}
