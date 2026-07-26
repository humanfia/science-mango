# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0519.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0519.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:518ed8f570f93ff17de13b485a259daec5ffb907bd69e0efab55ee439f408b6c
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Length Quantity`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `length In Nanometers`
- `LengthUnit.nanometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of nanometers (10⁻⁹ of a meter).
- `LengthUnit.femtometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of femtometers (10⁻¹⁵ of a meter).
- `LengthUnit.picometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of picometers (10⁻¹² of a meter).

### Query: `energy In Electron Volts`
- `DimEnergy.electronVolt` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 electron volt, 1.602176634×10−19 J.
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..

### Query: `planck Times Light In Electron Volt Nanometers`
- `LightProfinite` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | `LightProfinite` is the category of second countable profinite spaces.
- `DimEnergy.electronVolt` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 electron volt, 1.602176634×10−19 J.
- `Constants.ℏ` | module `Physlib.QuantumMechanics.PlanckConstant` | package PhysLean | The value of the reduced Planck's constant in units of J.s.

### Query: `Atomic Level`
- `IsAtomic` | module `Mathlib.Order.Atoms` | package Mathlib | A lattice is atomic iff every element other than `⊥` has an atom below it.
- `OrderedFinpartition.atomic` | module `Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno` | package Mathlib | The ordered finpartition of `Fin n` into singletons.
- `isAtomic_iff` | module `Mathlib.Order.Atoms` | package Mathlib | **Existence of Atoms in Nontrivial Atomic Orders.** In a nontrivial partially ordered set with a least element $\bot$, if the order is atomic, then there exists at least one atom.

### Query: `principal Quantum Number`
- `Filter.principal` | module `Mathlib.Order.Filter.Defs` | package Mathlib | The principal filter of `s` is the collection of all supersets of `s`.
- `NumberField.AdeleRing.principalSubgroup` | module `Mathlib.NumberTheory.NumberField.AdeleRing` | package Mathlib | The subgroup of principal adeles `(x)ᵥ` where `x ∈ K`.
- `Nat.nth_prime_zero_eq_two` | module `Mathlib.Data.Nat.Prime.Nth` | package Mathlib | **The First Prime Number.** The $0$-indexed $n$-th prime number is $2$.

### Query: `Atomic Energy Level Diagram`
- `Mathlib.Tactic.Widget.StringDiagram.AtomNode` | module `Mathlib.Tactic.Widget.StringDiagram` | package Mathlib | Nodes for 2-morphisms in a string diagram.
- `IsAtomic` | module `Mathlib.Order.Atoms` | package Mathlib | A lattice is atomic iff every element other than `⊥` has an atom below it.
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..

### Query: `One Electron Atom Experiment`
- `IsAtom` | module `Mathlib.Order.Atoms` | package Mathlib | An atom of an `OrderBot` is an element with no other element between it and `⊥`, which is not `⊥`.
- `DimEnergy.electronVolt` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 electron volt, 1.602176634×10−19 J.
- `IsPredArchimedean.findAtom` | module `Mathlib.Order.SuccPred.Tree` | package Mathlib | The unique atom less than an element in an `OrderBot` with archimedean predecessor.

### Query: `Matches One Electron Atom Scenario`
- `IsAtom` | module `Mathlib.Order.Atoms` | package Mathlib | An atom of an `OrderBot` is an element with no other element between it and `⊥`, which is not `⊥`.
- `DimEnergy.electronVolt` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 electron volt, 1.602176634×10−19 J.
- `RegularExpression.matches'` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | `matches' P` provides a language which contains all strings that `P` matches. Not named `matches` since that is a reserved word.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.nanometers` (PhysLean)
- `LengthUnit.femtometers` (PhysLean)
- `LengthUnit.picometers` (PhysLean)
- `DimEnergy.electronVolt` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `DimEnergy` (PhysLean)
- `LightProfinite` (Mathlib)
- `DimEnergy.electronVolt` (PhysLean)
- `Constants.ℏ` (PhysLean)
- `IsAtomic` (Mathlib)
- `OrderedFinpartition.atomic` (Mathlib)
- `isAtomic_iff` (Mathlib)
- `Filter.principal` (Mathlib)
- `NumberField.AdeleRing.principalSubgroup` (Mathlib)
- `Nat.nth_prime_zero_eq_two` (Mathlib)
- `Mathlib.Tactic.Widget.StringDiagram.AtomNode` (Mathlib)
- `IsAtomic` (Mathlib)
- `DimEnergy` (PhysLean)
- `IsAtom` (Mathlib)
- `DimEnergy.electronVolt` (PhysLean)
- `IsPredArchimedean.findAtom` (Mathlib)
- `IsAtom` (Mathlib)
- `DimEnergy.electronVolt` (PhysLean)
- `RegularExpression.matches'` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0519.AtomicEnergyLevelDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0519.AtomicLevel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0519.HasPhysicalAtomicSpectrum`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0519.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0519.MatchesIonizationEnergyMeasurement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0519.MatchesOneElectronAtomScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0519.MatchesSuppliedEnergyLevelDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0519.OneElectronAtomExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0519.RoundsToNearestWholeNanometer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0519.SatisfiesAtomicPhotonLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
