# M5 stage 2: fixed-support lift and bounded progression

Eight frozen conditional targets advance section 5 of the reviewed M5 proof. They reuse the nine accepted stage-1 theorems through the compiled M5StageOne module.

The polynomial branch proves characteristic-two cyclic modulus identities, divisibility at multiples, progression congruence and preservation of all common divisors of a,b,M_N. Quantification over every polynomial divisor retains repeated-factor information. It does not yet assert the fully assembled M5 theorem or prove that a feasible support pair exists.

The arithmetic branch proves that a positive-step progression meets [L,L+E), then combines that with the prior cutoff and birth-bound lemmas. Its hypotheses on E remain explicit; the finite-ring period bound is still a separate obligation.

Run the existing formalize-dag command with graph.json in this directory, the matching project sources in lean/, concurrency 16 and the same gpt-6-astra / medium settings. The 28 full-M5 roadmap obligations remain planned. Final receipts will distinguish this experiment's accepted statements from those broader obligations.
