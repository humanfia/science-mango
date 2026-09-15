# M6 transfer route and original resource obligations

The frozen original PROOF sections 3 and 6 require indexed cyclic inputs, both labelled edges even at R=0, exact ordered trace propagation, and the indexed-array bit-model bounds. No resource clause is discarded.

The first seven targets establish shift coordinates, canonical periodic memory, forced memory of every closed walk, bijectivity of labels, arbitrary layer-weight sums, exact indexed walk cardinality, and output convolution. Internal cycles use ZMod N; physical outputs will use Fin (2*N), matching M6.Pinned.Vector and the character module through the standard Fin N / ZMod N equivalence. A closed walk retains both memory and labels, so the empty-memory case still has 2^N indexed inputs.

Next, define a labelled edge matrix by summing over both bits with the prescribed successor. Define a concrete two-layer state-array recurrence for each initial state. Prove its state entries equal weighted paths and its diagonal sum equals the trace of the ordered product, hence the indexed-input sum already proved. Instantiate arbitrary layer weights with the boundary and character factors supplied by the other modules. Memory output is the finite coefficient convolution; no squarefree or odd-order premise appears.

The resource API will use the same actual recurrence with indexed coefficient arrays through degree 2*N. It must establish these facts, rather than assume an abstract efficient oracle:

- Each start has N layers, 2*(2^R) labelled transitions per layer, 2*N+1 coefficient slots and at most three edge coefficients. A loop counter records these nested loops, including zero slots; propagation uses two reusable layers.
- Degree bounds make truncation exact. Edge coefficient l1 norm at most four gives per-start accumulated absolute contribution at depth i at most 8^i; summing starts gives at most 2^R*8^N. Signed coefficient width can therefore be bounded by R+3*N+2.
- Index widths are bounded from the actual array dimensions. Under R<N, both coefficient and address widths are O(N). Charging those widths to the loop counter gives trace bit work O(N^3*4^R) and storage O(N^2*2^R).
- A constant number of traces plus conservative polynomial Euclid/preprocessing costs gives distance work O(N^3*4^R). The at-most-2*N additional pin queries supplied by recovery give witness work O(N^4*4^R).

The final statements should provide uniform explicit constants or their equivalent big-O theorems. The indexed-array cost model is mathematical, not a timing theorem for Python dictionaries or Lean code generation. Fixed-span asymptotic advantage over 4^N scanning remains part of the original M6 scope and will be connected after these actual resource bounds.
