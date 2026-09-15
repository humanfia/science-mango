# Stage 6: literal packing of repeated residues

This experiment follows the first paragraph of reviewed M5 section 5. For each tuple index i, its tag counts earlier indices with the same residue; its exponent is r(i) + tag(i)*T. The support is the finite image of these exponents. No distinctness assumption is imposed on the input tuple.

Seven targets establish the tag bound and strict growth among matching residues, preservation modulo T, injectivity of the packed exponents, exact support cardinality w, the exponent bound < w*T, and the zero anchor. The anchor uses index 0 with an explicit proof w>0 and assumes only that this designated residue has value zero. Thus the first occurrence of zero is the designated anchor, while later zero residues remain separate occurrences.

The initial independent nodes are tag_lt_weight, equal_residue_tag_strict, packed_value_mod and packed_support_anchor. packed_value_injective waits for the strict-tag and modular lemmas; cardinality waits for injectivity; range waits for the tag bound. The external runtime may retain concurrency cap 16, with four useful initial tasks here.

This experiment imports only definitions and Mathlib, not any unverified theorem or prior proof stub. It does not yet establish equality of binary residue polynomials after packing; that requires a subsequent finite-sum congruence lemma and must retain characteristic-two cancellations. Connectivity-repair integration and the complete M5 theorem are also separate obligations.

The isolated project is /home/jing/m5-lean-packing-formalization. No active earlier-stage project sources are modified. PREFLIGHT.json records statement checks only, not proof acceptance.
