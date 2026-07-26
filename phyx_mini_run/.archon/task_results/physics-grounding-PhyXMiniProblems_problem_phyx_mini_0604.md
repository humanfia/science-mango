# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0604.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0604.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:82b0cf50e7832b7c6cf68f1c3f41e13764187c92614b8ab7a80396ccab762866
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `derivative at a point`
- `Polynomial.derivative` | module `Mathlib.Algebra.Polynomial.Derivative` | package Mathlib | `derivative p` is the formal derivative of the polynomial `p`
- `bernsteinPolynomial.iterate_derivative_at_1` | module `Mathlib.RingTheory.Polynomial.Bernstein` | package Mathlib | **The $(n-\nu)$-th Derivative of a Bernstein Polynomial at 1.** For a commutative ring $R$ and natural numbers $\nu \leq n$, the $(n-\nu)$-th iterative derivative of the Bernstein polynomial $B_{\nu, n}(X)$ evaluated...
- `derivWithin_zero_of_not_accPt` | module `Mathlib.Analysis.Calculus.Deriv.Basic` | package Mathlib | **Derivative at an Isolated Point.** If a point $x$ is not an accumulation point of a set $s$, then the derivative of any function $f$ within $s$ at $x$ is zero.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Cartesian Axis`
- `CategoryTheory.CartesianMonoidalCategory.lift` | module `Mathlib.CategoryTheory.Monoidal.Cartesian.Basic` | package Mathlib | Constructs a morphism to the product given its two components.
- `RigidBody.intermediate_axis_instability` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | Rotations about the largest and smallest principal axes are stable under small perturbations; rotation about the intermediate axis is unstable (tennis-racket effect).
- `«term_×ˢ_»` | module `Mathlib.Data.SProd` | package Mathlib | The Cartesian product `s ×ˢ t` is the set of `(a, b)` such that `a ∈ s` and `b ∈ t`.

### Query: `Axis Orientation`
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `Orientation.finOrthonormalBasis_orientation` | module `Mathlib.Analysis.InnerProductSpace.Orientation` | package Mathlib | `Orientation.finOrthonormalBasis` gives a basis with the required orientation.
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.

### Query: `Nearest Neighbor Direction`
- `MeasureTheory.SimpleFunc.nearestPt` | module `Mathlib.MeasureTheory.Function.SimpleFuncDense` | package Mathlib | `nearestPt e N x` is the nearest point to `x` among the points `e 0`, ..., `e N`. If more than one point are at the same distance from `x`, then `nearestPt e N x` returns the point with the least possible index.
- `nhdsWithin` | module `Mathlib.Topology.Defs.Filter` | package Mathlib | The "neighborhood within" filter. Elements of `𝓝[s] x` are sets containing the intersection of `s` and a neighborhood of `x`.
- `FTheory.SU5.CodimensionOneConfig.nearestNeighbor` | module `Physlib.StringTheory.FTheory.SU5.Charges.OfRationalSection` | package PhysLean | `σ₀` and `σ₁` intersect the nearest neighbor `ℙ¹`s of the `I₅` Kodaira fiber. This is sometimes denoted `I₅^{(0|1)}`

### Query: `nearest Neighbor Direction card`
- `FTheory.SU5.CodimensionOneConfig.nearestNeighbor` | module `Physlib.StringTheory.FTheory.SU5.Charges.OfRationalSection` | package PhysLean | `σ₀` and `σ₁` intersect the nearest neighbor `ℙ¹`s of the `I₅` Kodaira fiber. This is sometimes denoted `I₅^{(0|1)}`
- `nhds` | module `Mathlib.Topology.Defs.Filter` | package Mathlib | A set is called a neighborhood of `x` if it contains an open set around `x`. The set of all neighborhoods of `x` forms a filter, the neighborhood filter at `x`, is here defined as the infimum over the principal filter...
- `nhdsWithin` | module `Mathlib.Topology.Defs.Filter` | package Mathlib | The "neighborhood within" filter. Elements of `𝓝[s] x` are sets containing the intersection of `s` and a neighborhood of `x`.

### Query: `Crystal Geometry`
- `AlgebraicGeometry.Scheme` | module `Mathlib.AlgebraicGeometry.Scheme` | package Mathlib | We define `Scheme` as an `X : LocallyRingedSpace`, along with a proof that every point has an open neighbourhood `U` so that the restriction of `X` to `U` is isomorphic, as a locally ringed space, to `Spec.toLocallyRi...
- `AlgebraicGeometry.Spec` | module `Mathlib.AlgebraicGeometry.Scheme` | package Mathlib | The spectrum of a commutative ring, as a scheme. The notation `Spec(R)` for `(R : Type*) [CommRing R]` to mean `Spec (CommRingCat.of R)` is enabled in the scope `SpecOfNotation`. Please do not use it within Mathlib, b...
- `RootPairing.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed` | module `Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas` | package Mathlib | **Possible Values of Cartan Integers in a Reduced Root System.** For a reduced crystallographic root pairing, the pair of Cartan integers $( \langle \alpha_i, \alpha_j^\vee \rangle, \langle \alpha_j, \alpha_i^\vee \ra...

### Query: `Einstein Crystal Model`
- `FirstOrder.Language.Theory.Model` | module `Mathlib.ModelTheory.Semantics` | package Mathlib | A model of a theory is a structure in which every sentence is realized as true.
- `RootPairing.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed'` | module `Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas` | package Mathlib | **Possible Values of Cartan Integers for Reduced Root Pairings.** In a reduced crystallographic root pairing, if two roots $\alpha_i$ and $\alpha_j$ are such that $\alpha_i \neq \alpha_j$ and $\alpha_i \neq -\alpha_j$...
- `WittVector.isocrystal_classification` | module `Mathlib.RingTheory.WittVector.Isocrystal` | package Mathlib | A one-dimensional isocrystal over an algebraically closed field admits an isomorphism to one of the standard (indexed by `m : ℤ`) one-dimensional isocrystals.

### Query: `einstein Temperature`
- `Temperature.ofβ` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | The temperature associated with a given inverse temperature `β`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Temperature` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | The type `Temperature` represents the temperature in a given (but arbitrary) set of units (preserving zero). It currently wraps `ℝ≥0`, i.e., absolute temperature in nonnegative reals.

### Query: `heat Capacity Per Atom`
- `IsAtom` | module `Mathlib.Order.Atoms` | package Mathlib | An atom of an `OrderBot` is an element with no other element between it and `⊥`, which is not `⊥`.
- `CanonicalEnsemble.heatCapacity` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | The heat capacity (at constant volume) C_V = ∂U/∂T (as a derivWithin on T > 0).
- `CanonicalEnsemble.heatCapacity_eq_deriv_meanEnergyBeta` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | Relates C_V = dU/dT to dU/dβ. C_V = dU/dβ * (-1/(kB T²)).

## Grounded Mathlib/PhysLean names

- `Polynomial.derivative` (Mathlib)
- `bernsteinPolynomial.iterate_derivative_at_1` (Mathlib)
- `derivWithin_zero_of_not_accPt` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `CategoryTheory.CartesianMonoidalCategory.lift` (Mathlib)
- `RigidBody.intermediate_axis_instability` (PhysLean)
- `«term_×ˢ_»` (Mathlib)
- `Orientation.oangle` (Mathlib)
- `Orientation.finOrthonormalBasis_orientation` (Mathlib)
- `RigidBody.parallel_axis_theorem` (PhysLean)
- `MeasureTheory.SimpleFunc.nearestPt` (Mathlib)
- `nhdsWithin` (Mathlib)
- `FTheory.SU5.CodimensionOneConfig.nearestNeighbor` (PhysLean)
- `FTheory.SU5.CodimensionOneConfig.nearestNeighbor` (PhysLean)
- `nhds` (Mathlib)
- `nhdsWithin` (Mathlib)
- `AlgebraicGeometry.Scheme` (Mathlib)
- `AlgebraicGeometry.Spec` (Mathlib)
- `RootPairing.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed` (Mathlib)
- `FirstOrder.Language.Theory.Model` (Mathlib)
- `RootPairing.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed'` (Mathlib)
- `WittVector.isocrystal_classification` (Mathlib)
- `Temperature.ofβ` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Temperature` (PhysLean)
- `IsAtom` (Mathlib)
- `CanonicalEnsemble.heatCapacity` (PhysLean)
- `CanonicalEnsemble.heatCapacity_eq_deriv_meanEnergyBeta` (PhysLean)

## Local abstractions introduced

- `PhyXMini0604.AxisOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0604.CartesianAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0604.CrystalGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0604.EinsteinCrystalModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0604.FigureMarker`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0604.NearestNeighborDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0604.SpecificHeatCurve`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0604.SpecificHeatFigureReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
