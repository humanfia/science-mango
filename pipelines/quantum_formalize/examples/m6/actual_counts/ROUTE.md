# Actual physical input normalization

This batch connects the accepted quotient-ring boundary fibers to the actual coefficient-defined physical maps. For polynomials `a,b` of degree below positive `N`, the block coefficients are exactly `Coordinates.coefficients N a` and `Coordinates.coefficients N b`. The signature exponent `f` retains the full gcd with `x^N+1`, including repeated factors.

The first chain transports the actual boundary equality through the accepted encoding bijection and convolution identity into equality of quotient-ring boundary outputs. The accepted algebraic fiber theorem then gives `2^f` inputs per actual boundary output. The weight-preserving involution and flattening are bijections, so the actual dual-boundary map has the same fibers.

A reusable finite-image weighted-sum lemma handles the subtype/image bookkeeping once. Applying it to each actual map gives its weighted input sum as `C(2^f)` times the sum over its actual finite image. The image of the boundary map is `Spaces.boundaryWords`; the image of the dual-boundary map is the actual binary subspace `Spaces.D`. Taking weight 1, together with the actual input cardinality `2^N`, proves `2^f * |D| = 2^N`.

The final boundary formula uses the shared pinned monomial and enumerator. The final signed-input formula uses the actual dual-boundary outputs in the product of pinned character factors. The accepted pinned MacWilliams identity and the proved input normalization yield exactly `C(2^N)` times the actual cycle enumerator. These final conclusions contain no free oracle-correctness, fiber-size or cardinality premise; those quantities are proved for the actual maps.

The definitions and ten exact targets typecheck. The planned dependency closure contains 53 accepted declarations from coordinates, polynomial boundary fibers, flattening, spaces, character orthogonality, pinned MacWilliams, and generic normalization. Promotion must verify the exact archived proofs and the actual project must compile and audit them before launch. Trace construction, cyclic-walk identities, exact division and the final algorithm remain separately owned integration work.
