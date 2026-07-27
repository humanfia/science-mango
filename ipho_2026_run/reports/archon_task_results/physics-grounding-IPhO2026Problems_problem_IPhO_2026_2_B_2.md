# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_2_B_2.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_B_2.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:183ba6a338a1480c7dfa29d13ede99ccbccf893495ff5cefd4491584a632d38a
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `LengthQuantity`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `powerDimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `PowerSeries` | module `Mathlib.RingTheory.PowerSeries.Basic` | package Mathlib | Formal power series over a coefficient type `R`
- `Dimension.instPowRat` | module `Physlib.Units.Dimension` | package PhysLean | **Rational Power of a Physical Dimension.** For any physical dimension $d$ and any rational number $n$, the power $d^n$ is defined as the dimension whose fundamental components—length, time, mass, charge, and temperat...

### Query: `PowerQuantity`
- `PowerSeries` | module `Mathlib.RingTheory.PowerSeries.Basic` | package Mathlib | Formal power series over a coefficient type `R`
- `TensorPower` | module `Mathlib.LinearAlgebra.TensorPower.Basic` | package Mathlib | Homogeneous tensor powers $M^{\otimes n}$. `⨂[R]^n M` is a shorthand for `⨂[R] (i : Fin n), M`.
- `PowerBasis` | module `Mathlib.RingTheory.PowerBasis` | package Mathlib | `pb : PowerBasis R S` states that `1, pb.gen, ..., pb.gen ^ (pb.dim - 1)` is a basis for the `R`-algebra `S` (viewed as `R`-module). This is a structure, not a class, since the same algebra can have many power bases....

### Query: `irradianceDimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `ringKrullDim` | module `Mathlib.RingTheory.KrullDimension.Basic` | package Mathlib | The ring-theoretic Krull dimension is the Krull dimension of its spectrum ordered by inclusion.
- `DimEnergy.joule` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 joule, J.

### Query: `IrradianceQuantity`
- `DimEnergy.kilowattHour` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 kilowatt-hours, (3,600,000 J).
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `Ideal.inertiaDeg` | module `Mathlib.RingTheory.RamificationInertia.Inertia` | package Mathlib | Given a prime ideal `q` of an `R`-algebra `S`, the inertia degree of `q` over `R` is defined to be the degree of the residue field of `q` over the residue field of its preimage `p` in `R`. When `q` is not prime, we us...

### Query: `Figure2fGeometry`
- `AlgebraicGeometry.AlgebraicCycle` | module `Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic` | package Mathlib | Algebraic cycle on a scheme `X` with coefficients in a type `Z` is just a function from `X` to `Z` with locally finite support (see the module docstring for more details). Note: currently this is an abbrev to save som...
- `AlgebraicGeometry.Scheme` | module `Mathlib.AlgebraicGeometry.Scheme` | package Mathlib | We define `Scheme` as an `X : LocallyRingedSpace`, along with a proof that every point has an open neighbourhood `U` so that the restriction of `X` to `U` is isomorphic, as a locally ringed space, to `Spec.toLocallyRi...
- `EuclideanGeometry.Concyclic` | module `Mathlib.Geometry.Euclidean.Sphere.Basic` | package Mathlib | A set of points is concyclic if it is cospherical and coplanar. (Most results are stated directly in terms of `Cospherical` instead of using `Concyclic`.)

### Query: `OpticalModel`
- `Manifold.Elab.FindModelResult` | module `Mathlib.Geometry.Manifold.Notation` | package Mathlib | Information about a model with corners found through `findModelInner`. It includes the model with corners found, and, if this model is the trivial model with corners on a normed space, information about that normed sp...
- `modelWithCornersSelf` | module `Mathlib.Geometry.Manifold.IsManifold.Basic` | package Mathlib | A vector space is a model with corners, denoted as `𝓘(𝕜, E)` within the `Manifold` namespace.
- `ModelPi` | module `Mathlib.Geometry.Manifold.ChartedSpace` | package Mathlib | Same thing as `∀ i, H i`. We introduce it for technical reasons, see note [Manifold type tags].

### Query: `HasFigure2fPlacement`
- `HasSum` | module `Mathlib.Topology.Algebra.InfiniteSum.Defs` | package Mathlib | `HasSum f a L` means that the (potentially infinite) sum of the `f b` for `b : β` converges to `a` along the SummationFilter `L`. By default `L` is the `unconditional` one, corresponding to the limit of all finite set...
- `HasAdjoint.adjoint` | module `Physlib.Mathematics.InnerProductSpace.Adjoint` | package PhysLean | **Uniqueness of the Adjoint Operator.** If a map $f: E \to F$ between inner product spaces over a field $\mathbb{k}$ has an adjoint $f'$, then the formally defined adjoint operator $f^*$ is equal to $f'$.
- `CategoryTheory.Limits.BinaryFan.map_snd` | module `Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts` | package Mathlib | **Functorial Image of a Binary Fan Projection.** Given a functor $F$ and a binary fan $s$ over objects $X$ and $Y$, the second projection of the image of $s$ under $F$ is equal to the image of the second projection of...

### Query: `HasUniformParallelSunlight`
- `uniformity` | module `Mathlib.Topology.UniformSpace.Defs` | package Mathlib | The uniformity is a filter on α × α (inferred from an ambient uniform space structure on α).
- `Computation.parallel` | module `Mathlib.Data.Seq.Parallel` | package Mathlib | Parallel computation of an infinite stream of computations, taking the first result
- `UniformEquiv.comap_eq` | module `Mathlib.Topology.UniformSpace.Equiv` | package Mathlib | **Uniformity of a Uniform Isomorphism.** For any uniform isomorphism $h$ between two uniform spaces $\alpha$ and $\beta$, the uniform structure on $\alpha$ is equal to the uniform structure induced from $\beta$ by $h$.

### Query: `IsFullyAbsorbing`
- `CategoryTheory.Functor.FullyFaithful` | module `Mathlib.CategoryTheory.Functor.FullyFaithful` | package Mathlib | Structure containing the data of inverse map `(F.obj X ⟶ F.obj Y) ⟶ (X ⟶ Y)` of `F.map` in order to express that `F` is a fully faithful functor.
- `Filter.mem_absorbing` | module `Mathlib.Topology.Bornology.Absorbs` | package Mathlib | **Membership in the Absorbing Filter.** A set $s$ belongs to the filter of sets that absorb $u$ if and only if $s$ absorbs $u$.
- `Filter.absorbing` | module `Mathlib.Topology.Bornology.Absorbs` | package Mathlib | The filter of sets that absorb `u`.

## Grounded Mathlib/PhysLean names

- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `Dimension` (PhysLean)
- `PowerSeries` (Mathlib)
- `Dimension.instPowRat` (PhysLean)
- `PowerSeries` (Mathlib)
- `TensorPower` (Mathlib)
- `PowerBasis` (Mathlib)
- `Dimension` (PhysLean)
- `ringKrullDim` (Mathlib)
- `DimEnergy.joule` (PhysLean)
- `DimEnergy.kilowattHour` (PhysLean)
- `εNFA.εClosure` (Mathlib)
- `Ideal.inertiaDeg` (Mathlib)
- `AlgebraicGeometry.AlgebraicCycle` (Mathlib)
- `AlgebraicGeometry.Scheme` (Mathlib)
- `EuclideanGeometry.Concyclic` (Mathlib)
- `Manifold.Elab.FindModelResult` (Mathlib)
- `modelWithCornersSelf` (Mathlib)
- `ModelPi` (Mathlib)
- `HasSum` (Mathlib)
- `HasAdjoint.adjoint` (PhysLean)
- `CategoryTheory.Limits.BinaryFan.map_snd` (Mathlib)
- `uniformity` (Mathlib)
- `Computation.parallel` (Mathlib)
- `UniformEquiv.comap_eq` (Mathlib)
- `CategoryTheory.Functor.FullyFaithful` (Mathlib)
- `Filter.mem_absorbing` (Mathlib)
- `Filter.absorbing` (Mathlib)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_2_B_2.Figure2fGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_2.HasFigure2fPlacement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_2.HasPartB1RadiusRelation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_2.HasUniformParallelSunlight`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_2.IrradianceQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_2.IsFullyAbsorbing`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_2.IsLargestRelevantIncidenceAngle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_2.IsSingleReflectionRegime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_2.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_2.OpticalModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_2.PowerQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_2.SatisfiesProjectedAperturePowerLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
