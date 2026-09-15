# Final original-M5 root

`M5.Final.OriginalM5Spec w F` is one fixed proposition over the actual existing definitions. It contains the arithmetic core, concrete physical recovery, and concrete residue recovery for the w≥2 branch. The only public hypotheses are positive weight, monic F and F(0)=1.

The core includes finite period search, exact/nonnegative order counts and positivity/zero certificates, lower orders, the weight-one boundary, normalization correspondence, global A criterion, bounded same-support progression, actual finite first birth with its membership/minimality certificates, and arbitrary later exceptions. The recovery fields call `M5.PhysicalRecovery.recoverWord` and `M5.ArithmeticResidueRecovery.recover`, using their actual conditional arithmetic oracles; no free count-oracle parameter appears.

The physical recovery wrapper assumes positive C, not F dividing M_N. It derives that divisibility from C's existing guard before applying stage46, then converts decoded range-subset/cardinality/anchor/gcd/signature properties into `PhysicalOrder.realizes`. The residue wrapper keeps the actual returned list, exact tail length and candidate-test bound. Its two blocks have implicit anchored zero and preserve repeated entries; no extra tuple representation or sorting requirement is introduced.

Stage46 and stage47 proof imports remain explicit DAG gates. Their definitions are present for exact type checking, but their correctness theorems are not assumed. The root-local `M5ConditionalResidueCountAccepted` adapter initially imports definitions only while stage42/47 closure is pending. It provides no theorem or axiom. Accepted proof closure must replace this adapter and resolve the gate before final proof execution.

The Core nodes can run independently while these gates remain. Passing Core is not passing OriginalM5Spec. Conversely, once the actual OriginalM5Spec proof and root audit pass, a component controller's hardcoded `m5_formalized=false` is not a rejection. See ROOT_ACCEPTANCE.md and the final_scope contract.

The final scope does not add runtime/codegen, efficiency, distance, inherited intersections, sorting, H-reindexing or equivalence-class classification. Finite arithmetic definitions and the actual finite-recovery correctness fields express the original terminating workflow.
