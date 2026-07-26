# Autoformalization result: `problem_phyx_mini_0208.lean`

## Assumption/target split

### Governing laws

- A resonant normal mode has a nonzero physical displacement amplitude, a positive inverse-length wave number, and a positive physical wavelength.
- In every selected length unit, its spatial displacement profile is
  `A * Real.sin (k * x)`.
- The fixed endpoint is a displacement node.
- The endpoint carried by the frictionless sliding ring has zero spatial derivative, expressing the free-end/antinode boundary condition.
- Wave number and wavelength satisfy the standard defining relation `k * λ = 2 * π`.

These assumptions are the fields of `SatisfiesFixedFreeStandingWaveLaws`; none contains a mode number or the requested odd-quarter-wave formula.

### Previous-part results

- None.  The source report records no previous parts.

### Figure/data readouts

- The physical span labeled `ℓ` is `FixedFreeStringSetup.vibratingSpan`.
- The endpoints are explicitly labeled `StringEndpoint.fixedEnd` and `StringEndpoint.freeEnd`.
- The fixed end is at axial coordinate zero and the free end is at the coordinate `ℓ`, in every selected length unit.
- The fixed end uses a fixed anchor.
- The free end is attached to a ring on a vertical pole, and the ring/pole contact is frictionless.
- The span is positive.

These facts are separated into `MatchesPrimaryFigure` and `HasPhysicalStringGeometry`.

### Current target conclusions

- `fixedFree_phase_quantization`: the phase `k * ℓ` is an odd positive multiple `(2 n - 1) * π / 2`.
- `resonantWavelengths_iff`: a physical wavelength is resonant exactly when, for some positive natural `n`, every unit readout satisfies
  `λ = 4 * ℓ / (2 * n - 1)`.

## Goal-faithfulness audit

The target wavelength formula occurs only in the conclusion of `resonantWavelengths_iff`.  It is absent from `FixedFreeStringSetup`, `MatchesPrimaryFigure`, `HasPhysicalStringGeometry`, `StandingWaveMode`, `SatisfiesFixedFreeStandingWaveLaws`, and `IsResonantWavelength`.  The odd-half-phase relation likewise occurs only as the conclusion of the intermediate quantization lemma.  `IsResonantWavelength` is defined by existence of a nontrivial sinusoidal mode obeying the two physical boundary conditions and `k λ = 2π`; it does not unfold to the requested answer.

The theorem characterizes the entire resonant spectrum with `n > 0`, matching the conventional indexing `n = 1, 2, ...`.  It does not select answer D by definition or assume a wavelength readout from the answer choices.

## Declarations created and blueprint correspondence

- `LengthQuantity`, `WaveNumberQuantity`, `lengthReadout`, and `waveNumberReadout`: dimension-preserving physical quantities and scalar unit readouts.
- `StringEndpoint`, `EndpointSupport`, `PoleOrientation`, and `RingPoleContact`: endpoint and figure roles.
- `FixedFreeStringSetup`, `MatchesPrimaryFigure`, and `HasPhysicalStringGeometry`: apparatus, figure data, and nondegeneracy.
- `StandingWaveMode`, `SatisfiesFixedFreeStandingWaveLaws`, and `IsResonantWavelength`: local standing-wave witness and physical-law interface.
- `fixedFree_phase_quantization`: derived intermediate result.
- `resonantWavelengths_iff`: formalizes blueprint label `thm:physics:phyx_mini_0208:target` and answer D's formula.

The blueprint file was not edited because the task's explicit write-permission section allows edits only to the assigned Lean file and this result file.  A later blueprint-maintenance pass should add `\leanok` to `thm:physics:phyx_mini_0208:target`.

## LeanExplore queries/candidates actually used

All searches used package filters `Mathlib` and `Physlib`.

- Query `standing waves on a string fixed end free end resonant wavelength boundary conditions` found `ClassicalMechanics.WaveEquation` as the only relevant physics candidate.
- Query `wave equation fixed boundary Neumann boundary eigenvalues` again found `ClassicalMechanics.WaveEquation`, but no fixed--free string spectrum or mixed-boundary eigenmode API.
- Queries `UnitExp length dimensions physical quantity`, `PhysLean SI length quantity wavelength`, `WithDim physical quantity carrying a specified dimension`, and `WithDim Dimension.L𝓭 real length` found `Dimension`, `Dimension.L𝓭`, `Dimensionful`, `WithDim`, and related unit-scaling declarations.
- Query `HasDerivAt derivative of a real function at a point` found `HasDerivAt`.
- Queries `Real.sin real sine function derivative` and `Real.sin` found `Real.sin`, `Real.hasDerivAt_sin`, and related derivative declarations.

Source and module information was fetched for the candidates used in the statements: `HasDerivAt`, `Real.sin`, `WithDim`, `Dimension.L𝓭`, `Dimension`, and `Dimensionful`.  Source/module information was also fetched for the near-miss `ClassicalMechanics.WaveEquation` to assess compatibility.

## PhysLean/Mathlib names grounded

- PhysLean: `Dimensionful`, `WithDim`, `Dimension`, `Dimension.L𝓭`, `UnitChoices`, `UnitChoices.SI`, and `LengthUnit`.
- Mathlib: `HasDerivAt`, `Real.sin`, and `Real.pi`.

## Local abstractions introduced

- `FixedFreeStringSetup` preserves the physical span as a unit-independent length and records the actual endpoint/support geometry rather than replacing the apparatus by scalars.
- `StandingWaveMode` retains dimensionful amplitude and inverse-length wave number.  Its real function is explicitly named a unit-indexed scalar displacement readout, which is appropriate for differentiation with `HasDerivAt`.
- `SatisfiesFixedFreeStandingWaveLaws` is the smallest local interface found that expresses the nontrivial harmonic profile, Dirichlet fixed-end condition, Neumann free-end condition, and wavelength/wave-number law needed by the statement.
- `IsResonantWavelength` uses mode existence rather than defining resonance by the final closed formula.

## Grounding gaps

- No Mathlib/PhysLean declaration for a one-dimensional string with one fixed and one free endpoint, its standing modes, or its resonant wavelength spectrum was found.
- `ClassicalMechanics.WaveEquation` is a useful near match, but its signature is a time-dependent vector-valued field on `Space d`; it supplies neither endpoint boundary conditions nor a fixed--free spectral theorem.  Using it directly would still require a local scalar-mode and boundary abstraction, so the formalization states the separated sinusoidal normal-mode law directly.
- The requested `.archon/AGENTS.md` role file was absent.  The complete available `.archon/prover-modes/physics-formalize.md` instructions and the target entry in `.archon/PROGRESS.md` were used instead.
- The assigned Lean file did not previously exist, so there were no file-specific `/- USER: ... -/` hints to apply.

## Verification

- `archon-lean-lsp` diagnostics: only the two expected `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0208.lean`: exit code 0, with the same two expected warnings.
