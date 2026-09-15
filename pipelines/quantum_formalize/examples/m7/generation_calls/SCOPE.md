# Original generation-call accounting

Pending canonical compact_core and normal compilation/acceptance. The planned measured program performs the same actual arithmetic evaluations and returns the same emission/output records. Its projection must be proved equal to the frozen production program. It explicitly counts both child calls and charges each cached root exactly once at the call that consumes it. The initial root is computed once to obtain fuel. Orbit-count calls are charged by the actual current stored-base cardinality for each residual evaluation.

The intended original bounds are H+1 root evaluations, 2mH child evaluations and at most finalBases.card * (1+H(2m+1)) factorized orbit-count evaluations. Full generation correctness must separately prove finalBases.card=H and that these H records are the complete distinct structural classes. These call counts do not by themselves prove the full per-call arithmetic cost, cache-bit bound, replay, or final M7 theorem.
