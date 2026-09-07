import Family8Grounding.Family8PaperFullCanonicalGroundingV200
import Family8Grounding.Family8PaperEq45SelectedOccurrenceBundleV3
import Family8Grounding.Family8PlankFrostmanCopyLossAlgebraV2
import Family8Grounding.Family8Prop51SelectedOccurrenceAmbientMassRatioV1

/-!
# Family 8 full canonical grounding checkpoint V201

The selected-occurrence interface for Equation (45) now uses the honest thick
parameter

`M = max 1 (27 * comparisonConstant ^ 3 * Delta * (b / a))`.

The corresponding Family 6 thickened-plank control is derived from an owner
map, unique ownership, and an actual owner-fibre maximal-concentration bound;
the fixed comparison loss remains visible for later scalar absorption.

The mixed Frostman factor's copy-loss algebra is also explicit.  Given a
reconstruction loss `L <= M` and retained copy count `J <= CF / M`, it bounds
`L * J ^ (1 - beta / 2)` by
`CF ^ (1 - beta / 2) * M ^ (beta / 2)`.  This is scalar algebra, not a
geometric copy producer.

Finally, the Proposition 5.1 source restriction uses the literal normalized
ambient-mass quotient

`max 1 (containedMassOn F active K / containedMassOn F selected K)`.

It yields the selected Frostman property once the selected ambient mass is
nonzero; positivity itself remains a geometric input.

Still open are an occurrence-specific producer of the owner, unique-owner,
and local-`Delta` data for the current greedy selected family, and an
`M`-aware selector/copy construction connecting that selection to the honest
thick parameter.  This checkpoint does not claim either seam is closed.
-/
