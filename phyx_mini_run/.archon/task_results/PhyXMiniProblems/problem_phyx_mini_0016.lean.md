# Autoformalization result: `problem_phyx_mini_0016.lean`

## Assumption/target split

### Governing laws

- `PrismOpticsLaws.refractiveIndicesPositive` requires positive,
  dimensionless refractive-index readouts for ambient air and the prism.
- `PrismOpticsLaws.prismDenserThanAmbient` records the material ordering needed
  for prism-to-air critical incidence.
- `IsInterfaceAngle` restricts every incidence, refraction, and reflection
  readout to `[0, π / 2]` radians, measured from the relevant surface normal.
- `SatisfiesSnellLawAtSurfaceOne` states Snell's law for entry from ambient air
  into the prism.
- `SatisfiesCriticalAngleLawAtSurfaceTwo` states Snell's law at the critical
  limit, where the transmitted ambient ray is at `π / 2` from the normal.
- `SatisfiesReflectionLawAtSurfaceTwo` states equality of incidence and
  reflection angles at Surface 2.
- `SatisfiesPrismRayGeometry` states that the internal Surface 1 refraction
  angle plus the Surface 2 incidence angle equals the angle between the two
  surface normals, hence the displayed prism interior angle.

### Previous-part results

- None. The source report has an empty `previous_parts` list, and the target has
  no dependency supplied by an earlier subquestion.

### Figure/data readouts

- `TriangularPrismSetup.isIsosceles`, supplied as `h_isosceles`, records that
  the pictured prism is isosceles.
- `PrismFigureReadouts.surfacesOneTwoAngle` records the displayed `60.0°`
  angle at which Surface 1 and Surface 2 meet.
- `PrismFigureReadouts.criticalIncidenceAngle` records the displayed `42.0°`
  angle between the incoming internal ray and the Surface 2 normal.
- `PrismFigureReadouts.reflectedAngle` records the second displayed `42.0°`
  angle between the reflected ray and that normal.
- `IncidenceAnswerChoice` and `answerAngleDegrees` retain all four printed
  candidates: A `11.5°`, B `27.5°`, C `42.5°`, and D `19.5°`.

### Current target conclusions

- `incidenceAngleSurfaceOne_eq_answerChoiceC` concludes that the requested
  external incidence angle `θ₁` is `degreesToRadians 42.5`, i.e. the recorded
  answer choice C.

## Goal-faithfulness audit

The target equality for `θ₁` occurs only in the conclusion of
`incidenceAngleSurfaceOne_eq_answerChoiceC`. It is absent from
`TriangularPrismSetup`, `PrismRayPath`, `PrismOpticsLaws`, and
`PrismFigureReadouts`. The Surface 1 Snell relation mentions `θ₁` only as the
unknown incidence angle in a general governing equation; it does not assume
the requested numerical answer. `degreesToRadians` merely fixes units, and no
definition makes the substantive target true by unfolding. No physical claim
was replaced by `True`, a reflexive equality, or a transparent scalar alias.

The recorded answer is retained honestly even though it conflicts with the
other source data; the conflict was not hidden by weakening or modifying any
law or figure readout. Consequently the theorem remains a by-`sorry` target for
this autoformalization stage and should not be reported as proved.

## Declarations created

- `degreesToRadians`: explicit degree-to-radian conversion.
- `OpticalRegion`: ambient-air and prism-material physical roles.
- `PrismSurface`: the figure labels Surface 1 and Surface 2.
- `TriangularPrismSetup`: refractive-index function, surface interior angle,
  and isosceles-shape proposition.
- `PrismRayPath`: the four normal-relative angular readouts along the pictured
  incident, refracted, and reflected ray path.
- `IsInterfaceAngle`: physical range of interface-angle readouts.
- `SatisfiesSnellLawAtSurfaceOne`: Surface 1 entry law.
- `SatisfiesCriticalAngleLawAtSurfaceTwo`: Surface 2 critical-angle law.
- `SatisfiesReflectionLawAtSurfaceTwo`: Surface 2 reflection law.
- `SatisfiesPrismRayGeometry`: relation imposed by the triangular prism
  cross-section and the straight internal ray.
- `PrismOpticsLaws`: grouped governing laws and admissibility conditions.
- `PrismFigureReadouts`: the `60°`, `42°`, and `42°` labels read from the image.
- `IncidenceAnswerChoice` and `answerAngleDegrees`: all displayed choices.
- `incidenceAngleSurfaceOne_eq_answerChoiceC`: formalization of blueprint label
  `thm:physics:phyx_mini_0016:target`.

## LeanExplore queries/candidates actually used

- Query `Snell's law refraction critical angle geometrical optics`, packages
  `Mathlib` and `Physlib`: no optical Snell-law declaration was returned.
  `EuclideanGeometry.law_sin` and its angle-at-point variants were near misses
  about triangle geometry, not laws of refraction.
- Query `critical angle total internal reflection`, the same packages: returned
  affine/subspace reflection and Euclidean angle declarations, but no optical
  critical-angle API.
- Query `Real.arcsin Real.sin`, the same packages: reviewed
  `Real.arcsin_eq_of_sin_eq` and related inverse-sine lemmas as candidates for
  a later proof or consistency analysis; no arcsine lemma is required in the
  statement-only stage.
- Query `angle between vectors Euclidean geometry`, the same packages:
  reviewed `InnerProductGeometry.angle` and `EuclideanGeometry.angle`. They are
  unnecessary for the scalar normal-relative readouts already supplied by this
  fixed 2D figure.
- Query `Real.sin`, the same packages: selected `Real.sin` (declaration id
  `128819`). Its source, module (`Mathlib.Analysis.Complex.Trigonometric`), and
  docstring were fetched before use.
- Queries `Real.pi_pos` and `Real.pi_nonneg`, the same packages: confirmed the
  standard Mathlib `Real.pi` namespace and positivity support for later angle
  reasoning; these lemmas are not needed in the by-`sorry` statement.

## PhysLean/Mathlib names grounded

- Mathlib: `Real.sin`, `Real.pi`, and `Set.Icc`.
- No PhysLean optical object or law was found that matched Snell's law,
  refractive indices, or critical incidence.

## Local abstractions introduced

- `OpticalRegion` and `PrismSurface` preserve medium and interface identities
  instead of collapsing either physical primitive to a real scalar.
- `TriangularPrismSetup` separates the physical prism/material data from the
  path readouts and gives refractive index its correct dimensionless role.
- `PrismRayPath` is a multi-field measurement record whose values are explicitly
  radian readouts; it is not a scalar alias for a physical ray.
- The four optics/geometry predicates state independently reusable governing
  laws. They were introduced because LeanExplore found no matching PhysLean
  API, and none contains the current target answer.
- `PrismFigureReadouts` separates direct image evidence from governing laws and
  from the requested conclusion.

## Grounding gaps and redraft request

- Mathlib/PhysLean currently exposed no matching API for optical media,
  refractive index, Snell's law, or critical incidence, so faithful local
  abstractions were necessary.
- The blueprint contains `% archon:physics` but no informal derivation beyond
  the instruction to autoformalize. The figure was therefore used as the
  primary evidence, as its caption requests.
- The requested `.archon/AGENTS.md` and initial assigned Lean file were absent;
  `.archon/prover-modes/physics-formalize.md`, `PROGRESS.md`, the source report,
  blueprint, and image supplied the available role and problem context. There
  were no file-specific `/- USER: ... -/` comments to apply.
- The `archon` executable was not available on `PATH`, so the optional DAG query
  could not be run. The source report independently confirms no previous parts.
- **Redraft requested:** the figure and governing laws imply choice B, not the
  recorded choice C. The internal Surface 1 angle is `60° - 42° = 18°`.
  Critical incidence gives `n_prism sin 42° = n_air`, while Surface 1 Snell's
  law gives `n_air sin θ₁ = n_prism sin 18°`. Hence
  `sin θ₁ = sin 18° / sin 42°`, and the acute solution is approximately
  `27.5045°`, matching choice B (`27.5°`). The target conclusion `42.5°` is
  therefore not derivable from the modeled source assumptions and should be
  corrected upstream before the proof stage.

## Verification and blueprint synchronization

- `archon-lean-lsp` diagnostics report only the expected `declaration uses
  sorry` warning.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0016.lean` exits
  successfully with that same single expected warning.
- The blueprint theorem is ready for a statement-level `\leanok` marker once
  its recorded answer is reviewed. The chapter was not edited because this task
  explicitly permits writes only to the assigned Lean file and this result
  file.
