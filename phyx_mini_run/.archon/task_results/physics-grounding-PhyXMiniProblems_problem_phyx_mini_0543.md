# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0543.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0543.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:8d048ab95a8b40af461b98c7a4eb9c79c8770f5e5559413f5398b4905a2e7975
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `EuclideanSpace vector components`
- `EuclideanSpace` | module `Mathlib.Analysis.InnerProductSpace.PiL2` | package Mathlib | The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional space use `EuclideanSpace 𝕜 (Fin n)`. For the case when `n = Fin _`, there is `!₂[x, y, ...]` notation for building element...
- `Space.fderiv_space_components` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | **Components of the Fréchet Derivative of a Vector-Valued Function.** For a differentiable function $f$ mapping from a normed space $M$ to the space of $d$-dimensional vectors $\mathbb{R}^d$, the $\mu$-th component of...
- `Lorentz.ContrMod.toSpace` | module `Physlib.Relativity.Tensors.RealTensor.Vector.Pre.Modules` | package PhysLean | The underlying space part of a `ContrMod` formed by removing the first element. A better name for this might be `tail`.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Spin Half State`
- `spinGroup` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | `spinGroup Q` is defined as the infimum of `pinGroup Q` and `CliffordAlgebra.even Q`. See `mem_iff`.
- `UpperHalfPlane` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Basic` | package Mathlib | The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace
- `spinGroup.involute_eq` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | If x is in `spinGroup Q`, then `involute x` is equal to x.

### Query: `spin ZBasis`
- `spinGroup` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | `spinGroup Q` is defined as the infimum of `pinGroup Q` and `CliffordAlgebra.even Q`. See `mem_iff`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `RootPairing.Base.toWeightBasisInt` | module `Mathlib.LinearAlgebra.RootSystem.Base` | package Mathlib | A base for a root system gives a `ℤ`-basis for the `ℤ`-span of the roots.

### Query: `spin ZUp State`
- `spinGroup` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | `spinGroup Q` is defined as the infimum of `pinGroup Q` and `CliffordAlgebra.even Q`. See `mem_iff`.
- `spinGroup.toUnits` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | The elements in `spinGroup Q` embed into (CliffordAlgebra Q)ˣ.
- `spinGroup.coe_star` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | **Star Operation on the Spin Group.** For any element $x$ in the spin group of a quadratic form $Q$, the star operation applied to $x$ within the spin group is equal to the star operation applied to $x$ when viewed as...

### Query: `spin ZDown State`
- `spinGroup` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | `spinGroup Q` is defined as the infimum of `pinGroup Q` and `CliffordAlgebra.even Q`. See `mem_iff`.
- `spinGroup.toUnits` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | The elements in `spinGroup Q` embed into (CliffordAlgebra Q)ˣ.
- `complexLorentzTensor.Color.downR` | module `Physlib.Relativity.Tensors.ComplexTensor.Basic` | package PhysLean | The color associated with dual-Right handed fermions.

### Query: `spin XUp State`
- `spinGroup` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | `spinGroup Q` is defined as the infimum of `pinGroup Q` and `CliffordAlgebra.even Q`. See `mem_iff`.
- `PNat.XgcdType.flip_x` | module `Mathlib.Data.PNat.Xgcd` | package Mathlib | **Symmetry of the $x$ and $y$ components under flipping.** For any state in the extended Euclidean algorithm, the $x$ component of the flipped state is equal to the $y$ component of the original state.
- `spinGroup.toUnits` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | The elements in `spinGroup Q` embed into (CliffordAlgebra Q)ˣ.

### Query: `spin XDown State`
- `spinGroup` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | `spinGroup Q` is defined as the infimum of `pinGroup Q` and `CliffordAlgebra.even Q`. See `mem_iff`.
- `PNat.XgcdType.flip_isReduced` | module `Mathlib.Data.PNat.Xgcd` | package Mathlib | **Invariance of Reduced States under Flipping.** A state in the extended Euclidean algorithm is reduced if and only if its flipped state is also reduced.
- `spinGroup.toUnits` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | The elements in `spinGroup Q` embed into (CliffordAlgebra Q)ˣ.

### Query: `z Direction`
- `AffineSubspace.direction` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of an affine subspace is the submodule spanned by the pairwise differences of points. (Except in the case of an empty affine subspace, where the direction is the zero submodule, every vector in the direc...
- `Space.Direction` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Notion of direction where `unit` returns a unit vector in the direction specified.
- `direction_affineSpan` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of the affine span is the `vectorSpan`.

### Query: `Spin Axis`
- `spinGroup.star_mem_iff` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | An element is in `spinGroup Q` if and only if `star x` is in `spinGroup Q`. See `star_mem` for only one direction.
- `Orientation.rotation` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation` | package Mathlib | A rotation by the oriented angle `θ`.
- `spinGroup` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | `spinGroup Q` is defined as the infimum of `pinGroup Q` and `CliffordAlgebra.even Q`. See `mem_iff`.

## Grounded Mathlib/PhysLean names

- `EuclideanSpace` (Mathlib)
- `Space.fderiv_space_components` (PhysLean)
- `Lorentz.ContrMod.toSpace` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `spinGroup` (Mathlib)
- `UpperHalfPlane` (Mathlib)
- `spinGroup.involute_eq` (Mathlib)
- `spinGroup` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `RootPairing.Base.toWeightBasisInt` (Mathlib)
- `spinGroup` (Mathlib)
- `spinGroup.toUnits` (Mathlib)
- `spinGroup.coe_star` (Mathlib)
- `spinGroup` (Mathlib)
- `spinGroup.toUnits` (Mathlib)
- `complexLorentzTensor.Color.downR` (PhysLean)
- `spinGroup` (Mathlib)
- `PNat.XgcdType.flip_x` (Mathlib)
- `spinGroup.toUnits` (Mathlib)
- `spinGroup` (Mathlib)
- `PNat.XgcdType.flip_isReduced` (Mathlib)
- `spinGroup.toUnits` (Mathlib)
- `AffineSubspace.direction` (Mathlib)
- `Space.Direction` (PhysLean)
- `direction_affineSpan` (Mathlib)
- `spinGroup.star_mem_iff` (Mathlib)
- `Orientation.rotation` (Mathlib)
- `spinGroup` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0543.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0543.FigureBranchPosition`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0543.HasPhysicalSpinPrecessionParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0543.IsUniformAppliedFieldAlongZ`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0543.MatchesSpinHalfPreparation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0543.MatchesSuppliedSpinPrecessionFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0543.SatisfiesBornRuleForXSpinMeasurement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0543.SatisfiesZeemanHamiltonian`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0543.SpinAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0543.SpinHalfState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0543.SpinOutcome`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0543.SpinPrecessionExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0543.SpinPrecessionFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
