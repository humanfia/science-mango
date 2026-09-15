# Actual substitution and full signature tau

The concrete `equiv u` uses the already proved actual quotient substitution as its forward function and the actual `u⁻¹` substitution as its inverse. There is no free automorphism argument. The predecessor closure consists of 27 individually verified declarations, with source, frozen-target, receipt, payload and original compiled hashes checked before copying.

The original source uses `gcd(M, sigma_u(F))`, with sigma represented in the quotient by the reduced polynomial. `sourceTau` therefore keeps that ordering and uses `substituted u F %ₘ M`; `tau` separately names `gcd(substituted u F, M)`. The graph explicitly proves the reduced representative has the actual substitution image and proves `sourceTau = tau`. These are equivalence proofs, not an unannounced algorithm change.

The two base goals establish binary monicity and the monic modulus. Gcd canonicality gives monic divisors and validates swapping the two gcd arguments over GF(2). Independent actual ideal mapping identifies principal tau with the image of principal F under the concrete substitution. The reduced-source equivalence and monic-divisor uniqueness then give the actual identity, composition and inverse laws.

All targets retain positive N, including N=1, and allow the nonreduced even-N quotient with all repeated factors. No squarefree or faithful-action hypothesis is introduced. Degree invariance is owned by the separate quotient-degree batch. The actual recipe/affine polynomial signature bridge waits for its own accepted predecessor; neither result is assumed in this batch.

Both the repository source and original takeover source PROOF.md hash to `8ad32a3432f4b7fd3ad15aa4467e0f01255ce593ac9e474b1af38c9424addf19`. This is an intermediate original-M7 interface, not a claim that the complete M7 selector is formalized.
