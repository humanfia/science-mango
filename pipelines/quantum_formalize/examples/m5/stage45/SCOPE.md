# Stage45 finite period search

The original proof describes computing the period by finite ring arithmetic. The accepted period law and quotient-cardinality bound give a direct bounded arithmetic search: inspect the positive integers from1 through2^natDegree F, retain those satisfying F dividing M_N, and return the smallest.

The candidate set and finiteSearch definition explicitly express that finite procedure. The theorems show its candidate set is nonempty under the original monic/constant-one assumptions, its output is a valid candidate, and its output equals signaturePeriod F. The constant polynomial F=1 returns1. Repeated factors are retained; no irreducibility or squarefreeness assumption appears.

This connects the original finite arithmetic period step to the mathematical period definition. It adds no generated-code execution test, runtime implementation requirement, efficient complexity bound, or stronger numerical bound. The use of noncomputable Lean definitions records classical decidability without claiming a separately extracted executable implementation.
