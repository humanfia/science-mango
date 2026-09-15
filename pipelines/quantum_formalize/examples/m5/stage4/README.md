# Stage 4: quotient cardinality and the original period bound

Two draft targets address the finite-ring estimate in section 5. They do not extend the M5 theorem strength: its proof uses E ≤ 2^H and does not need E < 2^H. Both statements include F = 1. The first theorem is valid for every monic binary polynomial, including those whose constant coefficient is not one; the second retains the original M5 signature assumptions.

The pinned Mathlib route is AdjoinRoot.powerBasisAux' hF followed by Basis.equivFun.toEquiv, giving an equivalence with Fin F.natDegree → ZMod 2. Nat.card_congr and standard finite function-space cardinalities give exactly 2^degree. Once stage 3 provides Finite (AdjoinRoot F), orderOf_le_card and this identity bound signaturePeriod directly. Nilpotents and repeated factors are retained throughout; no field structure on the quotient is used.

Dependency integration is now complete through M5Cardinality, which imports M5QuotientFinite. That module contains the actual accepted stage-3 declaration, with no axiom or unverified stub. DEPENDENCY_IMPORT.json records verification of accepted=true, the artifact payload digest, candidate/frozen-target source hashes, both compiled .olean hashes, and agreement of the promoted proof body and explicit statement with those compiled sources. The receipt is archived as quotient_finite.receipt.json. The pre-import graph is preserved as graph.before_dependency_import.json; the two target statements are unchanged. The period bound depends on the new cardinality node plus this imported accepted theorem.

The original source's executable-period algorithm/refinement remains a separate open obligation. Neither cardinality nor the bound marks the complete M5 theorem as formalized. The 28-node full roadmap remains in the parent graph.


The independent runnable project is /home/jing/m5-lean-cardinality-formalization, with its own build directory and shared pinned package cache. The stage-3 project sources are untouched.
