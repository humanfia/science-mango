# Prover result: `problem_phyx_mini_0649.lean`

## Status

Complete. Both proof placeholders were closed without changing either
declaration signature.

## Proofs

- `maximum_pulse_rate_is_half_bandwidth`: combined the hypotheses
  `B * Delta-t = 1`, `R * T = 1`, and `T = 2 * Delta-t`. The first relation
  proves `Delta-t` is nonzero, allowing cancellation and yielding `2 * R = B`.
- `problem_phyx_mini_0649`: used the `Dimensionful` scaling property and
  `UnitChoices.dimScale_of_inv_eq_swap` to prove that the inverse-second
  readout is `1000` times the inverse-millisecond readout. Thus `200 kHz`
  is `200000 Hz`; the half-bandwidth lemma gives `100000 pulses/s`, which
  unfolds to displayed answer choice C.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0649.lean`: passed.
- `lake build`: passed.
- Source scan: no `sorry`, `admit`, `axiom`, `native_decide`, or `sorryAx`.
- `lean_verify` found no suspicious source patterns; both declarations depend
  only on the standard imported axioms `propext`, `Classical.choice`, and
  `Quot.sound`.
- `git diff --check`: passed.

## Blueprint

The lemma and target theorem are proof-complete and ready for deterministic
`\leanok` synchronization. Per prover permissions, the blueprint chapter was
not edited directly.

## Redraft needed

None.
