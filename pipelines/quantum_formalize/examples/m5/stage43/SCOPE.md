# Actual M5 arithmetic birth and order decisions

This batch instantiates the accepted generic birth search with the original divisor/character formula C, period t(F), lower bound max(w,deg(F)+1), and bound B=wT(T+2)+2^(wT). Define `M5.ArithmeticWorkflow.birth w F` to be that exact specialization of `M5.BirthSearch.birth`.

Six targets cover arbitrary positive-order C positivity and nonnegativity, zero iff absence, exact global first birth from A>0, no birth iff A=0, and the original later exception formula. The birth statements have no assumed physical witness, count oracle, or feasibility oracle: those must come from accepted stages27/39/30/38. Weight1 already has the separate exact boundary theorem in30.

The graph currently has explicit import gates. No target has been compiled or proved in this batch yet. Generic recovery36/37 and actual conditional C/A wiring remain separate original obligations. No distance, sorting, complexity bound, or literal-H reindex requirement is added.
