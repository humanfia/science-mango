# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0644.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0644.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:c45e6592977661c3b536b0cabf41dd215bbfdcb9394aab92d14786c0aa5699b8
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `energy In Joules`
- `Finset.mulEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The multiplicative energy `Eₘ[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. The notation `Eₘ[s, t]` is available in scope `C...
- `Finset.addEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The additive energy `E[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`. The notation `E[s, t]` is available in scope `Combinato...
- `DimEnergy.joule` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 joule, J.

### Query: `energy In Electron Volts`
- `DimEnergy.electronVolt` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 electron volt, 1.602176634×10−19 J.
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..

### Query: `Atomic Species`
- `IsAtomic` | module `Mathlib.Order.Atoms` | package Mathlib | A lattice is atomic iff every element other than `⊥` has an atom below it.
- `TensorSpecies.Tensor` | module `Physlib.Relativity.Tensors.Basic` | package PhysLean | The tensors associated with a list of indices of a given color `c : Fin n → C`.
- `OrderedFinpartition.atomic` | module `Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno` | package Mathlib | The ordered finpartition of `Fin n` into singletons.

### Query: `Atomic Energy Level`
- `IsAtomic` | module `Mathlib.Order.Atoms` | package Mathlib | A lattice is atomic iff every element other than `⊥` has an atom below it.
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..
- `Finpartition.energy` | module `Mathlib.Combinatorics.SimpleGraph.Regularity.Energy` | package Mathlib | The energy of a partition, also known as index. Auxiliary quantity for Szemerédi's regularity lemma.

### Query: `Energy Level Line Style`
- `Mathlib.Linter.linter.style.longLine` | module `Mathlib.Tactic.Linter.Style` | package Mathlib | The "longLine" linter emits a warning on lines longer than `linter.style.longLine.maxLineLength` (which defaults to 100) characters. We allow lines containing URLs to be longer, though.
- `Mathlib.Explode.Status.reg` | module `Mathlib.Tactic.Explode.Datatypes` | package Mathlib | `Entry.depth` * `│`
- `Mathlib.Linter.linter.style.emptyLine` | module `Mathlib.Tactic.Linter.EmptyLine` | package Mathlib | The "emptyLine" linter emits a warning on empty lines inside a command, but outside of a doc-string/module-doc. The linter is only active when there are no other warnings, so as to not add noise when developing incomp...

### Query: `Energy Level Line Color`
- `Combinatorics.Line.ColorFocused` | module `Mathlib.Combinatorics.HalesJewett` | package Mathlib | The type of collections of lines such that - each line is only one color except possibly at its endpoint - the lines all have the same endpoint - the colors of the lines are distinct. Used in the proof `exists_mono_in...
- `Combinatorics.Line.AlmostMono` | module `Mathlib.Combinatorics.HalesJewett` | package Mathlib | The type of lines that are only one color except possibly at their endpoints.
- `Combinatorics.Line.instInhabitedColorFocused` | module `Mathlib.Combinatorics.HalesJewett` | package Mathlib | **Existence of a Color-Focused Collection.** For any coloring function $C$ that maps lines (represented as functions from an index set $\iota$ to $\alpha \cup \{\text{none}\}$) to a set of colors $\kappa$, the type of...

### Query: `Atomic Energy Level Figure`
- `IsAtomic` | module `Mathlib.Order.Atoms` | package Mathlib | A lattice is atomic iff every element other than `⊥` has an atom below it.
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..
- `Mathlib.Tactic.Widget.StringDiagram.AtomNode` | module `Mathlib.Tactic.Widget.StringDiagram` | package Mathlib | Nodes for 2-morphisms in a string diagram.

### Query: `Element XIonization Setup`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `FTheory.SU5.Quanta.isViable_of_mem_viableElems` | module `Physlib.StringTheory.FTheory.SU5.Quanta.IsViable` | package PhysLean | **Viability of Elements in the Viable Set.** Any quantum configuration $x$ belonging to the set of viable elements is phenomenologically viable.
- `IsCompactElement` | module `Mathlib.Order.CompactlyGenerated.Basic` | package Mathlib | An element `k` is compact if any directed set with `LUB` (least upper bound) above `k` has already got above `k` at some point in the set. Such an element is also called "finite" or "S-compact".

### Query: `Matches Element XScenario`
- `commutatorElement` | module `Mathlib.Algebra.Group.Commutator` | package Mathlib | The commutator of two elements `g₁` and `g₂`. This is a scoped instance in the `commutatorElement` namespace to avoid clashing with other brackets.
- `RegularExpression.matches'` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | `matches' P` provides a language which contains all strings that `P` matches. Not named `matches` since that is a reserved word.
- `CKMMatrix.us_element` | module `Physlib.Particles.FlavorPhysics.CKMMatrix.Basic` | package PhysLean | The `us`th element of the CKM matrix.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Finset.mulEnergy` (Mathlib)
- `Finset.addEnergy` (Mathlib)
- `DimEnergy.joule` (PhysLean)
- `DimEnergy.electronVolt` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `DimEnergy` (PhysLean)
- `IsAtomic` (Mathlib)
- `TensorSpecies.Tensor` (PhysLean)
- `OrderedFinpartition.atomic` (Mathlib)
- `IsAtomic` (Mathlib)
- `DimEnergy` (PhysLean)
- `Finpartition.energy` (Mathlib)
- `Mathlib.Linter.linter.style.longLine` (Mathlib)
- `Mathlib.Explode.Status.reg` (Mathlib)
- `Mathlib.Linter.linter.style.emptyLine` (Mathlib)
- `Combinatorics.Line.ColorFocused` (Mathlib)
- `Combinatorics.Line.AlmostMono` (Mathlib)
- `Combinatorics.Line.instInhabitedColorFocused` (Mathlib)
- `IsAtomic` (Mathlib)
- `DimEnergy` (PhysLean)
- `Mathlib.Tactic.Widget.StringDiagram.AtomNode` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `FTheory.SU5.Quanta.isViable_of_mem_viableElems` (PhysLean)
- `IsCompactElement` (Mathlib)
- `commutatorElement` (Mathlib)
- `RegularExpression.matches'` (Mathlib)
- `CKMMatrix.us_element` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0644.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0644.AtomicEnergyLevel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0644.AtomicEnergyLevelFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0644.AtomicSpecies`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0644.ElementXIonizationSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0644.EnergyLevelLineColor`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0644.EnergyLevelLineStyle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0644.HasPhysicalElementXParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0644.IsUniqueMatchingIonizationEnergyChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0644.MatchesDisplayedIonizationEnergy`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0644.MatchesElementXScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0644.MatchesSuppliedEnergyLevelFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0644.SatisfiesGroundStateIonizationLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
