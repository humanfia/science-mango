# Autoformalization result: `problem_phyx_mini_0005.lean`

The chapter contains `% archon:physics`, so the `physics-formalize` discipline
was applied. The final-review gate identifies only missing post-formalization
evidence, not a semantic defect. Accordingly, the revised Lean model and its
public target declaration were retained unchanged.

The requested `.archon/AGENTS.md` is absent from this checkout. The complete
role instructions supplied with the task and
`.archon/prover-modes/physics-formalize.md` were used instead. The assigned
Lean file contains no file-specific `/- USER: ... -/` comment.

## Assumption/target split

### Governing laws

- `SnellLawAtFluidAirInterface n θ_air θ_fluid` states Snell's law for a ray
  leaving the fluid into air of refractive index one:
  `n * Real.sin θ_fluid = Real.sin θ_air`. The angle arguments are explicitly
  named real-valued radian readouts measured from the horizontal surface
  normal, while `n` is a dimensionless scalar refractive-index readout.
- The acute-angle conditions in `EmptyContainerFarEdgeSightline` and
  `CoinCenterVisibleAtSameViewingAngle` select the physical nongrazing branch
  shown by the diagram. They do not determine the refractive index or assert
  invisibility.

### Previous-part results

- None. The source report records `previous_parts: []`, and the theorem assumes
  no earlier numerical or optical conclusion.

### Figure/data readouts and setup relations

- `ContainerGeometry.height` is the figure's vertical length `h`, from the
  bottom to the surface/rim, and `ContainerGeometry.width` is the full bottom
  width `d`. Both are genuine PhysLean dimensionful length quantities, with
  positive SI readouts.
- `siLengthValue` is the explicitly named scalar projection of such a length
  in the SI chart. It is not a scalar replacement for the physical length.
- `EmptyContainerFarEdgeSightline geometry θ_air` records the primary-image
  geometry of the straight empty-container ray: it passes through the near top
  rim and reaches the opposite bottom edge, so
  `tan θ_air = d / h`.
- `CoinCenterVisibleAtSameViewingAngle geometry n θ_air` describes, rather
  than assumes, the event whose impossibility is requested. A witness
  `θ_fluid` must be acute, must have the midpoint slope
  `tan θ_fluid = (d / 2) / h`, and must obey Snell's law at the fluid-air
  surface while retaining the same external viewing angle `θ_air`.
- The primary image `phyx_data/test_image/5.png` was inspected directly. It
  shows the eye to the left, the ray through the near upper rim to the far
  bottom edge, the full bottom width labelled `d`, the vertical height labelled
  `h`, and the coin centered on the bottom. This supports the full-width and
  half-width slopes used in Lean. The auxiliary caption's description of `d`
  as a distance to the entry point is less precise than the image; the model
  follows the primary image.

### Current target conclusions

Only `refractiveIndex_gt_two_makes_coinCenter_invisible` concludes that, for a
dimensionless fluid refractive-index readout satisfying `2 < n`, every positive
container geometry and every acute external angle satisfying the empty
far-edge sightline fail to satisfy `CoinCenterVisibleAtSameViewingAngle`.
This is the sufficient range represented by recorded answer choice C.

## Goal-faithfulness audit

The current conclusion, `¬ CoinCenterVisibleAtSameViewingAngle ...`, occurs
only on the conclusion side of the theorem. Neither `ContainerGeometry`,
`SnellLawAtFluidAirInterface`, nor `EmptyContainerFarEdgeSightline` contains an
invisibility claim. `CoinCenterVisibleAtSameViewingAngle` is a substantive,
generic visibility predicate requiring an existential physical ray; it does
not unfold to false and it contains no `n > 2` threshold.

The hypothesis `2 < fluidRefractiveIndex` is the candidate range whose physical
consequence the theorem must establish; it is not itself the requested
invisibility conclusion. No premise states a bound on a sine ratio, the
decisive geometric inequality, or the negation of visibility. A future proof
must combine the two independent tangent relations, acute-angle information,
and Snell's law to rule out the ray.

Physical lengths were not collapsed to reals: they use
`Dimensionful (WithDim Dimension.L𝓭 ℝ)`. Only the named SI coordinate
projection, dimensionless index, and radian angle readouts use `ℝ`, as allowed
for measured scalar components and dimensionless ratios.

## Source/law/answer audit

- **Source:** The source report and primary image supply positive dimensions
  `h,d`, an empty ray spanning `d` horizontally over `h` vertically, a coin at
  the bottom midpoint, and use of the same external viewing angle after
  filling. There are no previous parts.
- **Law:** Refraction is not printed as an equation in the source, so the
  standard fluid-to-air Snell relation is exposed as the separately named
  governing-law predicate `SnellLawAtFluidAirInterface`. It is not the target
  threshold formula.
- **Answer:** The dataset records choice C, `n > 2`. Lean states the supported
  implication from that range to universal invisibility. The recorded answer
  is mentioned only in documentation and is not introduced as metadata or a
  premise that could prove the theorem automatically.

## Declarations and blueprint correspondence

- `siLengthValue` —
  `def:physics:phyx-mini-0005:phyxminiproblems-problemphyxmini0005-silengthvalue`
- `ContainerGeometry` —
  `def:physics:phyx-mini-0005:phyxminiproblems-problemphyxmini0005-containergeometry`
- `SnellLawAtFluidAirInterface` —
  `def:physics:phyx-mini-0005:phyxminiproblems-problemphyxmini0005-snelllawatfluidairinterface`
- `EmptyContainerFarEdgeSightline` —
  `def:physics:phyx-mini-0005:phyxminiproblems-problemphyxmini0005-emptycontainerfaredgesightline`
- `CoinCenterVisibleAtSameViewingAngle` —
  `def:physics:phyx-mini-0005:phyxminiproblems-problemphyxmini0005-coincentervisibleatsameviewingangle`
- `refractiveIndex_gt_two_makes_coinCenter_invisible` —
  `thm:physics:phyx_mini_0005:target`

The helper declarations are all direct physical dependencies of the single
target; no isolated public helper or artificial dependency edge was added.

## LeanExplore queries/candidates actually used

Every search passed `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `dimensionful physical length evaluated in SI units
  as a real scalar` returned `Dimensionful` and `UnitChoices.SI`, which are
  used. Related scaling/action results were unnecessary.
- Likely-name query `Dimensionful WithDim UnitChoices.SI length` again selected
  `Dimensionful` and `UnitChoices.SI`; `CarriesDimension.toDimensionful` and
  example/scaling declarations were not needed.
- Likely-name queries `WithDim physical dimension carrier` and
  `Dimension.L𝓭 base dimension length` grounded the dimension-tagged carrier
  and selected `Dimension.L𝓭`. The returned `WithDim.ext`, order, cast, and
  arithmetic lemmas are proof-stage utilities and are not used in the
  declaration statements.
- Natural-language query `Snell law refractive index sine incident refracted
  angles` found `Real.Angle` sine facts and Euclidean triangle laws of sines,
  but no compatible optical-interface Snell-law declaration. Those near misses
  do not represent refraction between indexed media, so the local predicate was
  retained.
- Natural-language query `real sine tangent angle radians acute interval`
  identified the real trigonometric API, including
  `Real.tan_eq_sin_div_cos`. The file uses the underlying `Real.sin` and
  `Real.tan` functions directly; quotient-valued `Real.Angle` was not adopted
  because the blueprint model explicitly uses measured radian readouts with
  acute branch restrictions.

Source/module details were fetched for the candidates adopted in the physical
quantity model:

- `Dimensionful` (id 394284), from `Physlib.Units.Basic`, is a subtype of
  unit-choice-indexed representations satisfying the relevant dimension law.
- `UnitChoices.SI` (id 394270), from `Physlib.Units.Basic`, fixes metres,
  seconds, kilograms, coulombs, and kelvin as the SI base-unit choices.
- `Dimension.L𝓭` (id 394324), from `Physlib.Units.Dimension`, is the length
  dimension.

The language server additionally confirmed the exact signatures and module
origins of `WithDim`, `Dimensionful`, `Dimension.L𝓭`, `UnitChoices.SI`, and
`Real.sin` in the assigned file.

## PhysLean/Mathlib names grounded

- PhysLean/Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`,
  `UnitChoices`, and `UnitChoices.SI`.
- Mathlib: `Real.sin`, `Real.tan`, `Real.pi`, and `Set.Ioo`.

## Local abstractions introduced

- `ContainerGeometry` is the smallest shared structure that retains the two
  distinct, positive dimensionful figure lengths and their roles.
- `siLengthValue` is a fixed-unit coordinate projection needed to compare the
  physical lengths with scalar trigonometric readouts.
- `SnellLawAtFluidAirInterface` faithfully supplies the absent governing law
  for a fluid-to-air surface, with air index one, without encoding the desired
  `n > 2` invisibility result.
- `EmptyContainerFarEdgeSightline` separates the full-width figure readout from
  optical physics.
- `CoinCenterVisibleAtSameViewingAngle` preserves the existential refracted
  ray, half-width midpoint geometry, acute branch, and same external angle. It
  is the event negated by the target, not an assumption of that negation.

## Grounding gaps and redraft requests

- Package-filtered LeanExplore searches found no compatible Snell-law,
  refractive-index, or optical-interface API. Direct inspection of
  `Physlib.Optics.Basic` confirms that the optics directory is currently an
  explicit placeholder. The local Snell predicate is therefore necessary and
  is not a missing-infrastructure excuse for weakening the statement.
- `.archon/AGENTS.md` is absent, as noted above.
- The optional `archon dag-query` navigation could not be run because the
  `archon` executable is not on `PATH` in this runtime. The source report
  independently establishes that there are no previous-part dependencies.
- The blueprint was not edited to add `\leanok` because the task's explicit
  write permissions permit edits only to the assigned Lean file and this task
  result and expressly prohibit blueprint edits. A plan/review agent with
  blueprint permission should mark the target environment after accepting the
  formalization.

## Verification

- `archon-lean-lsp` reports no errors or failed dependencies and exactly one
  expected `declaration uses sorry` warning, on the target theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0005.lean` exited with code
  zero and emitted only the same expected `sorry` warning.
