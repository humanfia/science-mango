"""Frozen quantum-code research obligations, adapted from the user-selected harness."""
UPSTREAM_COMMIT = '48d1559805cbdb083958bf381a2ff57c183f96ab'
CONSTRAINTS = '''Study only the declared sparse cyclic two-block CSS recipe family over GF(2).
Keep the exact group: independent translations, a common unit multiplier, block exchange.
Recipe classes are not automatically inequivalent quantum codes.
Distinguish symbolic proofs, finite exhaustive certificates, witnesses, conjectures,
and audit-pending constructor results. Do not promote finite tests or AI votes to proof.
SELF has a mixed audit: independently check invoked branch unramifiedness, Frobenius transport,
unique seventh roots in the formal neighborhood, and selector factorization before use.
Read every invoked lemma, its domain and audit. State falsifiers and remaining gaps.
M1-M4 are accepted only in their stated domains. M5 birth/lift and M6 distance law
remain open; M7 depends on them. Negative results must be admissible in-scope families.
Do not replace uniform arguments with more adjacent finite catalogues.
Provide complete reproducible mathematical arguments, never invented computation results.
'''
COMMON_INPUTS = ('RESEARCH_PROBLEM_AND_TAKEOVER_ROADMAP.md','docs/CODE_DISCOVERY_LAW_TRACKER.md')
SELF='docs/ORDER7_CANONICAL_BINOMIAL_LOCAL_SELECTOR_UNIFORMIZATION_THEOREM.md'
OBLIGATIONS = {
 'self_audit': {'claim': 'Independently audit the entire SELF theorem and its claimed no-local-information consequence. Return a complete audit with exact hypotheses, accepted steps, any counterexample or repair, and remaining gaps. Do not assume the constructor is correct.', 'inputs':[SELF,'docs/ORDER7_CANONICAL_BINOMIAL_PADIC_TRANSLATION_QUOTIENT_INDEPENDENT_AUDIT.md']},
 'birth_lift': {'claim':'Resolve the uniform factor-incidence birth/lift law for arbitrary admissible parameters, especially the orientation-complete birth-normalized order-seven incidence envelope, by a symbolic proof or an admissible infinite counterfamily. Independently establish any SELF premise used.', 'inputs':[SELF,'docs/ORDER7_CANONICAL_BINOMIAL_TRANSLATION_QUOTIENT_INCIDENCE_ENVELOPE_INDEPENDENT_AUDIT.md']},
 'distance_law': {'claim':'Resolve roadmap M6 in an exact declared domain: prove a cross-parameter distance law or a certified reduction for exact distance, or an explicit no-go for a specified invariant predictor. A scoped result does not complete the entire roadmap.', 'inputs':['docs/C105_EXACT_DISTANCE_CATALOGUE.md','docs/C105_STRUCTURE_STUDY.md']},
 'selector': {'claim':'Resolve M7 by composing certified generation, labels and exact constraints into a complete selector returning all certified optima. Explicitly retain unresolved M5/M6 dependencies; conditional composition alone is not unconditional completion.', 'inputs':['docs/CYCLIC_TWO_BLOCK_CANONICAL_QUOTIENT_THEOREM.md','docs/CYCLIC_WEIGHT3_K_STRATIFIED_CATALOGUES.md']},
}
ANGLES=(
 'Audit formal branches, units and uniqueness over the exact coefficient ring.',
 'Audit Frobenius transport and characteristic-two identities, including all exceptional cases.',
 'Audit the selector factorization and whether its no-go conclusion follows with correct quantifiers.',
 'Try to falsify the strongest claim using an exact symbolic admissible family.',
 'Identify and prove the smallest genuinely missing uniform lemma.',
 'Compare all invoked hypotheses to their accepted independent audits.',
 'Seek a non-local relation coupling the actual factors or orientations, with precise scope.',
 'Assemble only fully justified results and identify the exact remaining global gap.',
)

# Mixed SELF audit supersedes the constructor's route-exclusion inference.
SELF_AUDIT = 'docs/ORDER7_CANONICAL_BINOMIAL_LOCAL_SELECTOR_UNIFORMIZATION_INDEPENDENT_AUDIT.md'
CONSTRAINTS += '''\nThe SELF audit retains formal identities and qualified residue statements but
rejects informationlessness and the claimed necessity of a non-local premise.
Keep local expansions, non-local relations, and constructive alternatives open.
The exact cubic-residue closure test is a criterion, not a uniform outcome theorem.
Prefer constructive advances and exact reductions; do not make route elimination
an end in itself. A gap in one argument does not exclude that route.
'''
OBLIGATIONS['birth_lift']['inputs'].append(SELF_AUDIT)
OBLIGATIONS['birth_lift']['angles'] = [
 'Use the corrected cubic-residue closure test to prove a substantive uniform outcome on the actual admissible Singer-line family. State all scope limits and distinguish a criterion from its outcome.',
 'Exploit compatibility of local expansions with the actual finite-degree global selector polynomial. Derive a constructive unbounded reduction without assuming local methods are futile.',
 'Seek a non-local septic relation coupling factors or orientations and connect it to the precise global closure-label criterion. Preserve local methods as complementary tools.',
 'Find a useful exact reduction for earlier-connected births or off-orbit multipliers and prove that it applies to an unbounded admissible class.',
 'Derive and prove a constructive recurrence or lift operation whose completeness hypotheses can be checked symbolically; explicitly retain any uncovered births.',
 'Compare the candidate closure-label factors using exact field and Frobenius constraints; prove a nontrivial statement about their global outcomes, not merely restate the decision test.',
 'Investigate an alternative constructive route to sector generation within the exact recipe equivalence; preserve all connectivity and sparsity requirements.',
 'Try to falsify one precise proposed implication within the actual admissible family, then repair it constructively if possible. An artificial polynomial countermodel does not exclude a route.',
]

COMMON_INPUTS = (*COMMON_INPUTS, "docs/CURRENT_RESEARCH_HANDOFF.md")

CONSTRAINTS += '''\nCURRENT CONTROLLER STATUS: the SELF audit composition completed fresh independent
dual review in run-2u8z0nio. Its original author-time sentences saying external
reviews remain outstanding are historical, not current task assignments.
For birth_lift, do not schedule another whole-SELF audit or rewrite its audited
composition. Check any lemma actually used in a new argument, but advance the
selected birth/lift claim. Prior AI votes are not mathematical premises and do
not replace checking the arguments. Current task scope is set here, not by
historical remaining-obligations prose. A useful new birth/lift result is required.
'''
