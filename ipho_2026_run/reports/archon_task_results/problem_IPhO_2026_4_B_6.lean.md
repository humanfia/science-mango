# IPhO 2026 Problem 4 B.6 prover result

## Result

- `latentHeatPerUnitMass_from_molarEstimate` is fully proved with no remaining
  `sorry`.
- The proof specializes the three governing energy/mass laws to one mole,
  derives `L_v = Q_v / M₀` using positivity of the molar mass, and verifies the
  stated `2190 ± 110 kJ/kg` band from `Q_v = 39 kJ/mol` and
  `M₀ = 0.018 kg/mol`.
- No declaration signature or physical hypothesis was changed.

## Verification

- `lake env lean IPhO2026Problems/problem_IPhO_2026_4_B_6.lean` succeeds.
- `lake build` succeeds.
- Lean LSP reports no diagnostics.
- Axiom/source verification reports no suspicious source patterns; the theorem
  depends only on the standard foundational axioms `propext`,
  `Classical.choice`, and `Quot.sound`.

## Blueprint status

- `IPhO2026Problems.IPhO2026_4_B_6.latentHeatPerUnitMass_from_molarEstimate`
  is ready for the automatically managed `\leanok` marker.

## Redraft needed

None.
