# Autoformalization result: `problem_phyx_mini_0625.lean`

## Assumption/target split

### Governing laws

- `MatchesWeaklyBoundSimpleCubicScenario.eachBulkAtomHasSixNeighbors` states the bulk simple-cubic coordination law as `SimpleGraph.IsRegularOfDegree 6`.
- `MatchesWeaklyBoundSimpleCubicScenario.fusionEnergyBreaksBonds` records the stated melting mechanism: fusion energy is deposited in breaking lattice bonds.
- `SatisfiesFusionBondBreakingLaw.fusionEnergyBalance` is the general one-mole energy-accounting law. It relates latent heat to the actual edge count, atoms per mole, and energy per bond; it does not assume three bonds per atom or a numerical latent heat.
- The use of `SimpleGraph` preserves that the physical bond relation is loopless and undirected, so the Mathlib handshaking law counts the two endpoints of each bond.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Figure/data readouts

- `MatchesWeaklyBoundSimpleCubicScenario` records monatomic composition, simple-cubic lattice kind, weak binding, and coordination number six.
- `MatchesSuppliedCubicLatticeFigure` records the primary raster evidence: uniformly spaced yellow spherical sites arranged in three-dimensional cubic layers, joined by black straight nearest-neighbor segments, with no text labels or other objects.
- `HasStatedBondAndMoleCalibrations.bindingEnergyReadout` records `3.4 × 10⁻³ eV` as `34 / 10000` at an explicit electron-volt readout boundary.
- `HasStatedBondAndMoleCalibrations.avogadroReadout` records the exact atom count per mole, `6.02214076 × 10²³`.
- `displayedLatentHeatInJoulesPerMole` records choices A–D as 960, 970, 990, and 980 J/mol. `recordedAnswer` is separate source metadata and is not a theorem premise.

### Current target conclusions

- `bulkBondCount_eq_three_mul_atomCount`: the number of undirected bulk bonds is three times the atom count.
- `latentHeat_eq_three_bonds_per_atom`: the molar latent heat readout is `3 * atomsPerMole * bindingEnergyPerBond` in coherent SI units.
- `problem_phyx_mini_0625`: the physical latent heat is within `5 J/mol` of `980 J/mol`, and D is the unique closest displayed choice.

## Goal-faithfulness audit

The `980 J/mol` estimate, the `< 5` error statement, unique closeness of D, the three-bonds-per-atom equality, and the derived molar-energy formula occur only as conclusions of lemmas/theorems. None is a premise field, governing-law field, or local definition.

The fusion-energy balance is a genuine conservation/accounting assumption involving the graph's independent edge count. It deliberately retains the factor `Fintype.card Atom` on the latent-heat side, so deriving three bonds per atom from six-regularity remains necessary. `HasPhysicalCubicSolidParameters.latentHeatPositive` constrains only the sign of the independent latent-heat quantity, not its requested value. The answer-key definition `recordedAnswer` is not referenced by the target theorem.

The qualitative figure hypothesis is included to preserve the supplied image evidence, but contains no numerical energy or answer-choice claim. The target is an estimate rather than a false exact equality: the calibrated calculation is approximately `984.4 J/mol`, making 980 the nearest displayed value.

## Declarations created and blueprint labels

- Physical quantity/readout layer: `MolarEnergyScale`, `energyInJoules`, `electronVoltInJoules`, and `energyInElectronVolts`.
- Physical and figure vocabularies: `SolidComposition`, `LatticeKind`, `BindingRegime`, `FusionEnergyDestination`, `FigureArrangement`, `SiteGlyph`, `FigureColor`, `BondStroke`, and `CubicLatticeFigure`.
- Setup and premises: `MonatomicCubicSolidSetup`, `MatchesWeaklyBoundSimpleCubicScenario`, `MatchesSuppliedCubicLatticeFigure`, `HasStatedBondAndMoleCalibrations`, `HasPhysicalCubicSolidParameters`, and `SatisfiesFusionBondBreakingLaw`.
- Derived statements: `bulkBondCount_eq_three_mul_atomCount` and `latentHeat_eq_three_bonds_per_atom`.
- Answer and target layer: `AnswerChoice`, `displayedLatentHeatInJoulesPerMole`, `recordedAnswer`, `IsUniqueClosestDisplayedChoice`, and `problem_phyx_mini_0625`.
- Blueprint label `thm:physics:phyx_mini_0625:target` corresponds to `PhyXMiniProblems.ProblemPhyXMini0625.problem_phyx_mini_0625`. The statement is ready for the project marker-sync/review process. The blueprint was not edited because prover write permissions explicitly restrict it to read-only.

## LeanExplore queries/candidates actually used

All searches used `packages: ["Mathlib", "Physlib"]`.

- Query `physical quantity with SI dimensions and units energy joule electron volt` found `DimEnergy`, `DimEnergy.electronVolt`, `UnitChoices.SI`, `Dimension`, and `IsDimensionallyCorrect`.
- Query `electron volt conversion joule` found `DimEnergy.electronVolt`, `DimEnergy.joule`, and `DimEnergy`.
- Query `Avogadro constant particles per mole` found no matching Avogadro declaration; near misses included `Constants.kB` and statistical-mechanics particle-count declarations.
- Query `latent heat of fusion molar energy` found `DimEnergy` and heat-capacity/internal-energy declarations, but no latent-heat or molar-energy quantity.
- Query `SimpleGraph regular degree edge count handshaking lemma` found `SimpleGraph.sum_degrees_eq_twice_card_edges`, `SimpleGraph.IsRegularOfDegree`, and `SimpleGraph.IsRegularOfDegree.degree_eq`.
- Source/module details were fetched for `DimEnergy`, `DimEnergy.joule`, `DimEnergy.electronVolt`, `UnitChoices.SI`, `SimpleGraph.sum_degrees_eq_twice_card_edges`, `SimpleGraph.IsRegularOfDegree`, and `SimpleGraph.IsRegularOfDegree.degree_eq`.

## PhysLean/Mathlib names grounded

- Physlib: `DimEnergy`, `DimEnergy.electronVolt`, and `UnitChoices.SI` from the dimensionful-units API. `DimEnergy.electronVolt` supplies the exact `1.602176634 × 10⁻¹⁹ J` calibration.
- Mathlib: `SimpleGraph`, `SimpleGraph.edgeFinset`, `SimpleGraph.IsRegularOfDegree`, and the intended bond-count foundation `SimpleGraph.sum_degrees_eq_twice_card_edges`.
- Core/Mathlib scalar and finite infrastructure: `Fintype`, `Fintype.card`, `DecidableRel`, real absolute value, and finite answer labels.

## Local abstractions introduced

- `MolarEnergyScale` is an abstract carrier plus a J/mol readout. It preserves molar energy as a physical quantity rather than identifying it with `ℝ`; the scalar appears only as an explicitly unit-tagged measurement.
- `MonatomicCubicSolidSetup` keeps lattice graph, dimensionful per-bond energy, atoms-per-mole count, independent latent heat, melting mechanism, and figure evidence distinct.
- Small inductive vocabularies and `CubicLatticeFigure` preserve the named physical regimes and image-derived labels without encoding any numerical conclusion.
- Premise structures separate the physical scenario, primary-image evidence, numerical calibrations, parameter positivity, and the governing energy law.

## Grounding gaps

- LeanExplore found no Avogadro-constant declaration in the requested packages. The exact scalar is therefore introduced only as a calibrated particles-per-mole readout.
- Physlib's available `DimEnergy` uses the MLT dimension system and does not provide an amount-of-substance dimension, molar-energy type, or latent-heat-of-fusion API. `MolarEnergyScale` supplies the smallest abstract interface needed to retain that physical role.
- No library ontology was found for this raster's qualitative site glyphs, colors, or cubic-layer presentation, so these are represented by local finite inductive types.
- The requested `.archon/AGENTS.md` was absent in this workspace. The prover-role rules were consistent with the archived project role document, and the explicit current-turn permissions were followed.

## Verification

- `archon-lean-lsp` elaborated the file successfully.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0625.lean` exited successfully.
- Diagnostics contain exactly three expected `declaration uses sorry` warnings, for the two derived lemmas and the main target theorem, with no errors or failed dependencies.
