# Stage 8: support polynomials and the packing residue bridge

The original section 5 asserts that the packed support polynomial reduces to the tuple residue polynomial modulo M_T, including every binary cancellation. This experiment represents that statement by equality under AdjoinRoot.mk (cyclicModulus T), the full polynomial quotient map. AdjoinRoot.mk_eq_mk identifies this equality with divisibility of the difference by M_T; no root-set or squarefree interpretation is used.

The definitions sum X^e over the support Finset and sum X^(r_i) over every tuple index separately. The latter must not be replaced by the image set of residues: repeated entries can cancel in characteristic two. The final theorem admits these cancellations and even zero tuple polynomials.

The six targets are the constant coefficient indicator, anchored nonzeroness, the bounded degree lemma, a sum-over-image identity given packed-value injectivity, quotient periodicity of monomials, and the final packing bridge. The degree bound explicitly assumes K>0 so that the zero polynomial's natDegree=0 causes no false claim. The quotient periodicity and bridge are valid even for T=0 (an inhabited positive-length residue tuple then cannot exist), so no unnecessary nontriviality assumption is added.

The final bridge now imports verified accepted stage6 M5.Packing.packed_value_injective through M5PackingInjective, together with its actual ancestors equal_residue_tag_strict and packed_value_mod. All three acceptance receipts, artifact digests, candidate/frozen-target source and compiled hashes, axiom lists, actual proof bodies and parent-embedded ancestor declarations were checked. DEPENDENCY_IMPORT.json and dependency_receipts record that provenance. No proof was substituted. The original graph and preflight are archived with the before_dependency_import suffix; all six target statements are unchanged. The modular predecessor is included because the accepted injectivity proof uses it; the new quotient bridge itself reduces packed exponents directly.

The independent project is /home/jing/m5-lean-support-polynomial-formalization. Build and statement preflight do not mean proof acceptance; PREFLIGHT.json records the exact status. No full-M5 completion claim is made.


Context compatibility repair: all spec.context values are empty, as required by the DAG runner. GraphPreflight.lean is generated directly from the six exact graph statements and their imports, with no extra open commands. Lean accepted all six. The mathematical statements and 28 planned roadmap nodes are unchanged; previous context-bearing graph/preflight revisions are archived with before_empty_context suffixes.
