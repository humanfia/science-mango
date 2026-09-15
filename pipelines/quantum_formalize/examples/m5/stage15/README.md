# Stage 15: ordered tuple character-power identity

Reviewed M5 section 2 counts ordered length-k choices with repetition. Here the alphabet is Fin n and a tuple is a function Fin k → Fin n. Its vector sum uses every position; the count filters this full function space by equality with z. No injectivity, support-set interpretation or distinctness condition is imposed.

Five exact targets establish the zero-vector character, the character of a tuple sum as a product, the sum of tuple characters as the k-th power of the alphabet sum, an orthogonality count, and the final integer power-count identity. The final expression equals 2^D times the tuple count, so no rational division is introduced. The source's R(P,T,d,k,z) specialization still requires representing polynomial residues as binary vectors and identifying its alphabet; that is not silently marked complete.

All statements admit n=0, k=0 and D=0. There is one empty tuple at k=0, with vector sum zero and character product one. For the empty alphabet this agrees with the conventional 0^0=1 in Lean's natural exponentiation; positive-length tuples over the empty alphabet are absent.

The project /home/jing/m5-lean-tuple-character-formalization copies every imported M5 module verbatim from the immutable /home/jing/m5-lean-integrated52-formalization snapshot, with matching hashes recorded in IMPORT_PROVENANCE.json. The actual proof dependencies used here are M5.Character.character_add and M5.Character.character_orthogonality; the shared BinaryVector/value definitions are unchanged. No proof substitutions or new proofs are supplied during preparation. The full accepted module is imported to keep its dependency graph intact.

The independent ready nodes are value_zero and tuple_character_count. character_tuple_sum waits for value_zero, tuple_character_power waits for character_tuple_sum, and the final identity waits for the power and count identities. Contexts are empty, the runtime DAG loader is checked, and GraphPreflight.lean is generated directly from the graph's exact imports/statements.
