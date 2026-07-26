# Autoformalization result: `problem_phyx_mini_0036.lean`

This is the genuine post-formalization audit for Archon iteration 003.  The
review-gate reason was missing evidence only.  Inspection of the revised Lean
file, source report, primary image, and blueprint found no semantic defect, so
the physical declaration was preserved as required by the final retry
protocol.

## Assumption/target split

### Governing laws

- `SatisfiesLawOfReflection diagram` states the general optical reflection law
  `thetaR diagram = thetaA diagram`.  It does not mention `60 degrees`.
- `SatisfiesSnellLaw diagram` states
  `n_water * sin (thetaA) = n_glass * sin (thetaB)` using the scalar `.val`
  readouts of dimensionless `WithDim` refractive indices.  It does not contain
  the solved arcsine expression or answer B.
- `HasPhysicalOpticalParameters diagram` states positivity of each refractive
  index and places the three unsigned normal angles in `[0, pi/2]`, selecting
  the physical principal branch without assigning an outgoing angle.

### Previous-part results

- None.  The source report has `previous_parts: []`.

### Figure/data readouts

- `WaterGlassInterfaceDiagram` contains the common incidence point, an
  oriented interface normal and tangent, the three propagation vectors, and a
  dimensionless refractive index for each medium.
- `MatchesWaterGlassFigure diagram` records unit direction vectors, a unit
  perpendicular normal/tangent frame, and the depicted half-plane/rightward
  propagation relations.
- Its only numerical physics readouts are the source values
  `n_a(water) = 133/100`, `n_b(glass) = 38/25`, and
  `thetaA = degreesToRadians 60`.  Neither outgoing angle is a field.
- `AnswerChoice.angleDegrees` transcribes A--D and `recordedAnswerChoice`
  retains B as dataset metadata.  The latter is not a theorem premise.

### Current target conclusions

- `thetaR diagram = degreesToRadians 60`.
- `thetaB diagram` equals the principal-branch arcsine expression obtained by
  solving Snell's law.
- `thetaB diagram` is within half of `0.1 degree` of `49.3 degrees`, expressed
  by `MatchesAnswerToNearestTenth (thetaB diagram) .B`.

## Goal-faithfulness audit

No current conclusion is smuggled into a hypothesis, structure field, law
predicate, or local definition.  The reflected-angle result must combine the
independent incident-angle readout with the general reflection law.  The
refracted-angle result must solve the unspecialized Snell equation and use the
principal-branch conditions.  The numeric B match is absent from every theorem
premise and requires a later analytic/numeric proof.  `recordedAnswerChoice`
is isolated source metadata and does not make the theorem true by unfolding.

The result is substantive: it is neither `True`, a reflexive equality, nor an
unrelated scalar tautology.  The theorem body remains exactly the expected
autoformalization stub `by sorry`.

## Source/law/answer audit

- The primary image shows water (`a`) above glass (`b`), an incident ray
  travelling down/right, a reflected ray travelling up/right, and a refracted
  ray travelling down/right.  The displayed normal points upward, with
  `theta_a`, `theta_r`, and `theta_b` measured from the appropriate side of
  that normal.  The vector signs and angle definitions reproduce this.
- The image directly supplies `theta_a = 60 degrees`, `n_a = 1.33`, and
  `n_b = 1.52`; the formalization records these as exact decimal readouts.
- The auxiliary caption incorrectly says "water-air boundary" and calls
  `theta_r` a refraction angle.  The primary image and problem statement show
  a water--glass interface and a reflected water ray, which the Lean model
  follows.
- The law of reflection supports the separate `60 degree` reflected direction.
  Snell's law gives
  `arcsin ((1.33 / 1.52) * sin 60 degrees)`, approximately `49.3 degrees`, so
  recorded answer B is consistent with the refracted direction.

## Declarations and blueprint labels

- `OpticalMedium` —
  `def:physics:phyx-mini-0036:phyxminiproblems-problemphyxmini0036-opticalmedium`.
- `InterfaceRay` —
  `def:physics:phyx-mini-0036:phyxminiproblems-problemphyxmini0036-interfaceray`.
- `InterfaceRay.medium` —
  `def:physics:phyx-mini-0036:phyxminiproblems-problemphyxmini0036-interfaceray-medium`.
- `degreesToRadians` —
  `def:physics:phyx-mini-0036:phyxminiproblems-problemphyxmini0036-degreestoradians`.
- `WaterGlassInterfaceDiagram` —
  `def:physics:phyx-mini-0036:phyxminiproblems-problemphyxmini0036-waterglassinterfacediagram`.
- `thetaA`, `thetaR`, and `thetaB` — respectively
  `def:physics:phyx-mini-0036:phyxminiproblems-problemphyxmini0036-thetaa`,
  `def:physics:phyx-mini-0036:phyxminiproblems-problemphyxmini0036-thetar`, and
  `def:physics:phyx-mini-0036:phyxminiproblems-problemphyxmini0036-thetab`.
- `MatchesWaterGlassFigure` —
  `def:physics:phyx-mini-0036:phyxminiproblems-problemphyxmini0036-matcheswaterglassfigure`.
- `HasPhysicalOpticalParameters` —
  `def:physics:phyx-mini-0036:phyxminiproblems-problemphyxmini0036-hasphysicalopticalparameters`.
- `SatisfiesLawOfReflection` —
  `def:physics:phyx-mini-0036:phyxminiproblems-problemphyxmini0036-satisfieslawofreflection`.
- `SatisfiesSnellLaw` —
  `def:physics:phyx-mini-0036:phyxminiproblems-problemphyxmini0036-satisfiessnelllaw`.
- `AnswerChoice` and `AnswerChoice.angleDegrees` — respectively
  `def:physics:phyx-mini-0036:phyxminiproblems-problemphyxmini0036-answerchoice`
  and
  `def:physics:phyx-mini-0036:phyxminiproblems-problemphyxmini0036-answerchoice-angledegrees`.
- `recordedAnswerChoice` —
  `def:physics:phyx-mini-0036:phyxminiproblems-problemphyxmini0036-recordedanswerchoice`.
- `MatchesAnswerToNearestTenth` —
  `def:physics:phyx-mini-0036:phyxminiproblems-problemphyxmini0036-matchesanswertonearesttenth`.
- `reflectedAndRefractedDirections` —
  `thm:physics:phyx_mini_0036:target`.

No public helper was added or removed during this evidence-only retry.

## LeanExplore queries/candidates actually used

Every search passed `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `Snell's law refraction refractive index geometrical
  optics` returned unrelated `PolynomialLaw` declarations, the Euclidean law
  of sines, and affine `EuclideanGeometry.reflection`; none states either
  geometrical-optics interface law.
- Natural-language query `angle between two vectors in a real inner product
  space` returned `InnerProductGeometry.angle` and its supporting lemmas.  The
  exact definition is used for all three figure angle readouts.
- Natural-language query `dimensionless physical quantity with units` returned
  Physlib's dimension framework, including `Dimension`, but no refractive-index
  object.
- Likely-name query `WithDim` returned the exact `WithDim` structure from
  `Physlib.Units.WithDim.Basic`; it is used for dimensionless refractive
  indices.
- Likely-name query `refractiveIndex` returned only unrelated declarations,
  confirming that a dedicated library optical-index type was not found.
- Likely-name queries `Dimension`, `Real.sin Real.arcsin`, and `Real.sin`
  returned the exact used declarations `Dimension`, `Real.arcsin`, and
  `Real.sin`.

Source, module, and docstring were fetched only for the used candidates:
`WithDim` (LeanExplore id 394425), `InnerProductGeometry.angle` (228174),
`Dimension` (394292), `Real.arcsin` (147535), and `Real.sin` (128819).

## Physlib/Mathlib names grounded

- Physlib `WithDim` is the dimension-tagged structure with a scalar `val`
  projection, from `Physlib.Units.WithDim.Basic`.
- Physlib `Dimension` is the five-exponent physical dimension structure, from
  `Physlib.Units.Dimension`; its multiplicative identity denotes the
  dimensionless index used by `WithDim (1 : Dimension) Real`.
- Mathlib `InnerProductGeometry.angle`, from
  `Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic`, is the undirected real
  angle between two vectors and is used by `thetaA`, `thetaR`, and `thetaB`.
- Mathlib `Real.sin` and principal-range `Real.arcsin` ground Snell's equation
  and its solved target expression.
- The compiled file also uses standard Mathlib `EuclideanSpace`, `inner`,
  norms, `Real.pi`, and `Set.Icc`.

## Local abstractions introduced

- `OpticalMedium` and `InterfaceRay` preserve the distinct labelled media and
  physical ray roles instead of erasing them into scalar aliases.
- `WaterGlassInterfaceDiagram` preserves the planar geometry with actual
  two-dimensional propagation, normal, and tangent vectors.  Its refractive
  indices use Physlib dimension tags.
- `MatchesWaterGlassFigure` separates source/figure readouts from governing
  laws and conclusions.
- `SatisfiesLawOfReflection` and `SatisfiesSnellLaw` are the smallest faithful
  local law predicates.  Direct inspection of
  `.lake/packages/PhysLean/Physlib/Optics/Basic.lean` shows that the module is
  explicitly a placeholder and contains no optics declarations.
- `AnswerChoice` and `MatchesAnswerToNearestTenth` preserve the source's
  multiple-choice metadata and stated display precision without assuming the
  selected answer.

## Grounding gaps and redraft requests

- No Mathlib/Physlib Snell-law declaration, physical law-of-reflection
  declaration, or dedicated refractive-index object was found.  The local law
  predicates and dimension-tagged index field fill those gaps faithfully.
- No redraft is requested: the rejection was evidence-only and the physical
  audit found the current declaration source-supported and goal-faithful.
- `.archon/AGENTS.md` is absent in this checkout.  The available role file
  `.archon/prover-modes/physics-formalize.md` was read and followed instead.
- `archon` is not available on `PATH`, so the optional read-only DAG queries
  could not be executed.
- The theorem is ready for `\leanok`, but explicit write permissions prohibit
  editing the blueprint chapter; the coordinator should synchronize the marker.

## Verification

- `archon-lean-lsp` reported exactly one expected warning:
  `declaration uses sorry` at the target theorem, with no failed dependencies.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0036.lean` exited with code
  0 and emitted only the same expected `sorry` warning.
