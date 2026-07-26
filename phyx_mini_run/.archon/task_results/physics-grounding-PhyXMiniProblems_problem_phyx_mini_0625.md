# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0625.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0625.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:cbd20040422b2b6213ffcccc780c0767238de4aa0a4902661c70a1b1555d4132
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Molar Energy Scale`
- `Polynomial.scaleRoots` | module `Mathlib.RingTheory.Polynomial.ScaleRoots` | package Mathlib | `scaleRoots p s` is a polynomial with root `r * s` for each root `r` of `p`.
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..
- `ONote.scale` | module `Mathlib.SetTheory.Ordinal.Notation` | package Mathlib | `scale x o` is the ordinal notation for `ω ^ x * o`.

### Query: `energy In Joules`
- `Finset.mulEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The multiplicative energy `Eₘ[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. The notation `Eₘ[s, t]` is available in scope `C...
- `Finset.addEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The additive energy `E[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`. The notation `E[s, t]` is available in scope `Combinato...
- `DimEnergy.joule` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 joule, J.

### Query: `electron Volt In Joules`
- `DimEnergy.electronVolt` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 electron volt, 1.602176634×10−19 J.
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `«term∫_In_.._,_∂_»` | module `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic` | package Mathlib | The interval integral `∫ x in a..b, f x ∂μ` is defined as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`. If `a ≤ b`, then it equals `∫ x in Ioc a b, f x ∂μ`, otherwise it equals `-∫ x in Ioc b a, f x ∂μ`.

### Query: `energy In Electron Volts`
- `DimEnergy.electronVolt` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 electron volt, 1.602176634×10−19 J.
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..

### Query: `Solid Composition`
- `Composition.length` | module `Mathlib.Combinatorics.Enumerative.Composition` | package Mathlib | The length of a composition, i.e., the number of blocks in the composition.
- `LatticeOrderedAddCommGroup.IsSolid` | module `Mathlib.Algebra.Order.Group.Unbundled.Abs` | package Mathlib | A set `s` in a lattice ordered group is *solid* if for all `x ∈ s` and all `y ∈ α` such that `|y| ≤ |x|`, then `y ∈ s`.
- `dual_solid` | module `Mathlib.Analysis.Normed.Order.Lattice` | package Mathlib | **Monotonicity of the Norm with Respect to Infima with Negations.** In a lattice-ordered normed additive commutative group with a solid norm, for any two elements $a$ and $b$, if the infimum of $b$ and its negation is...

### Query: `Lattice Kind`
- `CompleteLattice` | module `Mathlib.Order.CompleteLattice.Defs` | package Mathlib | A complete lattice is a bounded lattice which has suprema and infima for every subset.
- `Lattice` | module `Mathlib.Order.Lattice` | package Mathlib | A lattice is a join-semilattice which is also a meet-semilattice.
- `Lat` | module `Mathlib.Order.Category.Lat` | package Mathlib | The category of lattices.

### Query: `Binding Regime`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Mathlib.Tactic.UnfoldBoundary.registerUnfoldBoundaryExt` | module `Mathlib.Tactic.Translate.UnfoldBoundary` | package Mathlib | Register a new `UnfoldBoundaryExt`.
- `BigOperators.processBigOpBinder` | module `Mathlib.Algebra.BigOperators.Group.Finset.Defs` | package Mathlib | Collects additional binder/Finset pairs for the given `bigOpBinder`. Note: this is not extensible at the moment, unlike the usual `bigOpBinder` expansions.

### Query: `Fusion Energy Destination`
- `Finpartition.energy` | module `Mathlib.Combinatorics.SimpleGraph.Regularity.Energy` | package Mathlib | The energy of a partition, also known as index. Auxiliary quantity for Szemerédi's regularity lemma.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..

### Query: `Figure Arrangement`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `ACCSystemCharges.Charges` | module `Physlib.QFT.AnomalyCancellation.Basic` | package PhysLean | The charges as functions from `Fin χ.numberCharges → ℚ`.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Polynomial.scaleRoots` (Mathlib)
- `DimEnergy` (PhysLean)
- `ONote.scale` (Mathlib)
- `Finset.mulEnergy` (Mathlib)
- `Finset.addEnergy` (Mathlib)
- `DimEnergy.joule` (PhysLean)
- `DimEnergy.electronVolt` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `«term∫_In_.._,_∂_»` (Mathlib)
- `DimEnergy.electronVolt` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `DimEnergy` (PhysLean)
- `Composition.length` (Mathlib)
- `LatticeOrderedAddCommGroup.IsSolid` (Mathlib)
- `dual_solid` (Mathlib)
- `CompleteLattice` (Mathlib)
- `Lattice` (Mathlib)
- `Lat` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Mathlib.Tactic.UnfoldBoundary.registerUnfoldBoundaryExt` (Mathlib)
- `BigOperators.processBigOpBinder` (Mathlib)
- `Finpartition.energy` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `DimEnergy` (PhysLean)
- `εNFA.εClosure` (Mathlib)
- `ACCSystemCharges.Charges` (PhysLean)
- `εNFA.IsPath` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0625.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0625.BindingRegime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0625.BondStroke`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0625.CubicLatticeFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0625.FigureArrangement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0625.FigureColor`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0625.FusionEnergyDestination`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0625.HasPhysicalCubicSolidParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0625.HasStatedBondAndMoleCalibrations`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0625.IsUniqueClosestDisplayedChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0625.LatticeKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0625.MatchesSuppliedCubicLatticeFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0625.MatchesWeaklyBoundSimpleCubicScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0625.MolarEnergyScale`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0625.MonatomicCubicSolidSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0625.SatisfiesFusionBondBreakingLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0625.SiteGlyph`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0625.SolidComposition`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
