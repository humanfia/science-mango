# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_2_B_3.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_B_3.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:99dd5ff17e054a514ba5305c82e1bd2f9004c606e3ea318096e8ed1d6d5583e7
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `PhysicalLength`
- `CanonicalEnsemble.physicalProbability` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The dimensionless physical probability density. This is is the probability density w.r.t. the measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the probability density `ρ_ph...
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `Dimension.L𝓭_length` | module `Physlib.Units.Dimension` | package PhysLean | **Length Dimension Component.** The length component of the fundamental physical dimension for length is equal to 1.

### Query: `OpticalPower`
- `PowerSeries` | module `Mathlib.RingTheory.PowerSeries.Basic` | package Mathlib | Formal power series over a coefficient type `R`
- `TensorPower` | module `Mathlib.LinearAlgebra.TensorPower.Basic` | package Mathlib | Homogeneous tensor powers $M^{\otimes n}$. `⨂[R]^n M` is a shorthand for `⨂[R] (i : Fin n), M`.
- `PowerBasis` | module `Mathlib.RingTheory.PowerBasis` | package Mathlib | `pb : PowerBasis R S` states that `1, pb.gen, ..., pb.gen ^ (pb.dim - 1)` is a basis for the `R`-algebra `S` (viewed as `R`-module). This is a structure, not a class, since the same algebra can have many power bases....

### Query: `centimeterUnits`
- `Units` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | Units of a `Monoid`, bundled version. Notation: `αˣ`. An element of a `Monoid` is a unit if it has a two-sided inverse. This version bundles the inverse element so that it can be computed. For a predicate see `IsUnit`.
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `Units.exists0` | module `Mathlib.Algebra.GroupWithZero.Units.Basic` | package Mathlib | In a group with zero, an existential over a unit can be rewritten in terms of `Units.mk0`.

### Query: `lengthInMeters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `lengthInCentimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `powerInSI`
- `UnitChoices.dimScale_SIPrimed_SI` | module `Physlib.Units.Basic` | package PhysLean | **Scaling Factor between Prime-Scaled SI and Standard SI Units.** For any physical dimension $d$, the scaling factor from the prime-scaled SI unit system to the standard SI unit system is given by the product of the f...
- `PowerSeries` | module `Mathlib.RingTheory.PowerSeries.Basic` | package Mathlib | Formal power series over a coefficient type `R`
- `DimArea.hectare_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **Value of a Hectare in SI Units.** In the SI unit system, the value of one hectare is exactly $10,000$.

### Query: `HalfCylindricalMirror`
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `UpperHalfPlane` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Basic` | package Mathlib | The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace
- `HomotopicalAlgebra.Precylinder.symm` | module `Mathlib.AlgebraicTopology.ModelCategory.Cylinder` | package Mathlib | The precylinder object obtained by switching the two inclusions.

### Query: `FullyAbsorbingCylinder`
- `Filter.absorbing` | module `Mathlib.Topology.Bornology.Absorbs` | package Mathlib | The filter of sets that absorb `u`.
- `CategoryTheory.Functor.FullyFaithful` | module `Mathlib.CategoryTheory.Functor.FullyFaithful` | package Mathlib | Structure containing the data of inverse map `(F.obj X ⟶ F.obj Y) ⟶ (X ⟶ Y)` of `F.map` in order to express that `F` is a fully faithful functor.
- `HomotopicalAlgebra.Precylinder.i` | module `Mathlib.AlgebraicTopology.ModelCategory.Cylinder` | package Mathlib | the map from the coproduct of two copies of `A` to `P.I`, when `P` is a cylinder object for `A`. `P` shall be a *good* cylinder object when this morphism is a cofibration.

### Query: `SunlightBeam`
- `ConvexCone.Blunt.salient` | module `Mathlib.Geometry.Convex.Cone.Basic` | package Mathlib | A blunt cone (one not containing `0`) is always salient.
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.

### Query: `Figure2fSetup`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Mathlib.Notation3.setupLCtx` | module `Mathlib.Util.Notation3` | package Mathlib | Adds all the names in `boundNames` to the local context with types that are fresh metavariables. This is used for example when initializing `p` in `(scoped p => ...)` when elaborating `...`.
- `Mathlib.Explode.entriesToMessageData` | module `Mathlib.Tactic.Explode.Pretty` | package Mathlib | Given all `Entries`, return the entire Fitch table.

## Grounded Mathlib/PhysLean names

- `CanonicalEnsemble.physicalProbability` (PhysLean)
- `Dimension` (PhysLean)
- `Dimension.L𝓭_length` (PhysLean)
- `PowerSeries` (Mathlib)
- `TensorPower` (Mathlib)
- `PowerBasis` (Mathlib)
- `Units` (Mathlib)
- `LengthUnit.centimeters` (PhysLean)
- `Units.exists0` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `UnitChoices.dimScale_SIPrimed_SI` (PhysLean)
- `PowerSeries` (Mathlib)
- `DimArea.hectare_in_SI` (PhysLean)
- `Polynomial.mirror` (Mathlib)
- `UpperHalfPlane` (Mathlib)
- `HomotopicalAlgebra.Precylinder.symm` (Mathlib)
- `Filter.absorbing` (Mathlib)
- `CategoryTheory.Functor.FullyFaithful` (Mathlib)
- `HomotopicalAlgebra.Precylinder.i` (Mathlib)
- `ConvexCone.Blunt.salient` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Mathlib.Notation3.setupLCtx` (Mathlib)
- `Mathlib.Explode.entriesToMessageData` (Mathlib)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_2_B_3.Figure2fSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_3.FullyAbsorbingCylinder`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_3.HalfCylindricalMirror`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_3.OpticalPower`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_3.PhysicalLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_3.SunlightBeam`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
