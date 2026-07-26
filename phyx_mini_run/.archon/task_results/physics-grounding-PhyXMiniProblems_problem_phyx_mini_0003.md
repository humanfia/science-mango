# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0003.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0003.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:1ea72a52c9e69fad0b09d0a2fdc8ef1ef7a69ca8380e9d98cc9f664a9610e48a
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Real.sqrt square root`
- `Real.sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | The square root of a real number. This returns 0 for negative inputs. This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`.
- `Real.coe_sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Square Root of Nonnegative Reals.** For any nonnegative real number $x$, the real-valued square root of $x$ is equal to the square root of $x$ computed in the nonnegative real numbers and then cast to a real number.
- `Real.sqrt_lt'` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Strict Monotonicity of the Square Root.** For any real number $x$ and any positive real number $y$, the square root of $x$ is strictly less than $y$ if and only if $x$ is strictly less than $y^2$.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Dim Length`
- `Order.LTSeries.length_le_krullDim` | module `Mathlib.Order.KrullDimension` | package Mathlib | **Length of a Strictly Increasing Sequence and Krull Dimension.** For any strictly increasing sequence in a preorder, its length is less than or equal to the Krull dimension of that preorder.
- `Dimension.L𝓭_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass component of the length dimension.** The mass dimension component of the length dimension $L_d$ is equal to $0$.
- `Order.krullDim_eq_iSup_length` | module `Mathlib.Order.KrullDimension` | package Mathlib | A definition of krullDim for nonempty `α` that avoids `WithBot`

### Query: `Dim Time`
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `dim` | module `Physlib.Units.Basic` | package PhysLean | **Alias** of `HasDim.d`. --- The dimension associated with a type `M`.
- `Dimension.T𝓭_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass component of the time dimension.** The mass dimension component of the time dimension $T_d$ is equal to zero.

### Query: `Dim Speed Real`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `Real` | module `Mathlib.Data.Real.Basic` | package Mathlib | The type `ℝ` of real numbers constructed as equivalence classes of Cauchy sequences of rational numbers.
- `DimSpeed.speedOfLight` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensionful speed of light corresponding to 299792458 meters per second.

### Query: `Parallel Glass Slab Experiment`
- `Computation.parallel` | module `Mathlib.Data.Seq.Parallel` | package Mathlib | Parallel computation of an infinite stream of computations, taking the first result
- `CategoryTheory.Limits.parallelPair` | module `Mathlib.CategoryTheory.Limits.Shapes.Equalizers` | package Mathlib | `parallelPair f g` is the diagram in `C` consisting of the two morphisms `f` and `g` with common domain and codomain.
- `Computation.mem_parallel` | module `Mathlib.Data.Seq.Parallel` | package Mathlib | **Membership in a Parallel Computation.** Let $S$ be a weak sequence of computations. If every computation in $S$ that terminates is guaranteed to result in the value $a$, then for any specific computation $c$ in the...

### Query: `Parallel Glass Slab Governing Laws`
- `Computation.parallel` | module `Mathlib.Data.Seq.Parallel` | package Mathlib | Parallel computation of an infinite stream of computations, taking the first result
- `CategoryTheory.Limits.parallelPair` | module `Mathlib.CategoryTheory.Limits.Shapes.Equalizers` | package Mathlib | `parallelPair f g` is the diagram in `C` consisting of the two morphisms `f` and `g` with common domain and codomain.
- `Matrix.GeneralLinearGroup.isParabolic_conj_iff` | module `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo` | package Mathlib | **Invariance of Parabolicity under Conjugation in $GL_2(R)$.** An element $h$ of the general linear group $GL_2(R)$ is parabolic if and only if its conjugate $ghg^{-1}$ is parabolic for any $g \in GL_2(R)$.

### Query: `Parallel Glass Slab Figure Readouts`
- `CategoryTheory.Limits.parallelPair.parallelPairObj_one` | module `Mathlib.CategoryTheory.Limits.Shapes.Equalizers` | package Mathlib | **The Object Assignment of the Parallel Pair Diagram at Index One.** In the diagram of a parallel pair defined by objects $X$ and $Y$, the object corresponding to the index $1$ is $Y$.
- `CategoryTheory.Limits.parallelPair` | module `Mathlib.CategoryTheory.Limits.Shapes.Equalizers` | package Mathlib | `parallelPair f g` is the diagram in `C` consisting of the two morphisms `f` and `g` with common domain and codomain.
- `Computation.parallel` | module `Mathlib.Data.Seq.Parallel` | package Mathlib | Parallel computation of an infinite stream of computations, taking the first result

### Query: `transit Time is answer C`
- `Polynomial.C` | module `Mathlib.Algebra.Polynomial.Basic` | package Mathlib | `C a` is the constant polynomial `a`. `C` is provided as a ring homomorphism.
- `TimeTransMan.toTime` | module `Physlib.SpaceAndTime.Time.TimeTransMan` | package PhysLean | With a choice of zero `zero : TimeTransMan` and a choice of units `x : TimeUnit`, `toTime` is the homeomorphism between the type `TimeTransMan` and `Time`.
- `StateTransition.EvalsToInTime.trans` | module `Mathlib.Computability.StateTransition` | package Mathlib | Transitivity of `EvalsToInTime` in the sum of the numbers of steps.

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Order.LTSeries.length_le_krullDim` (Mathlib)
- `Dimension.L𝓭_mass` (PhysLean)
- `Order.krullDim_eq_iSup_length` (Mathlib)
- `dimH` (Mathlib)
- `dim` (PhysLean)
- `Dimension.T𝓭_mass` (PhysLean)
- `DimSpeed` (PhysLean)
- `Real` (Mathlib)
- `DimSpeed.speedOfLight` (PhysLean)
- `Computation.parallel` (Mathlib)
- `CategoryTheory.Limits.parallelPair` (Mathlib)
- `Computation.mem_parallel` (Mathlib)
- `Computation.parallel` (Mathlib)
- `CategoryTheory.Limits.parallelPair` (Mathlib)
- `Matrix.GeneralLinearGroup.isParabolic_conj_iff` (Mathlib)
- `CategoryTheory.Limits.parallelPair.parallelPairObj_one` (Mathlib)
- `CategoryTheory.Limits.parallelPair` (Mathlib)
- `Computation.parallel` (Mathlib)
- `Polynomial.C` (Mathlib)
- `TimeTransMan.toTime` (PhysLean)
- `StateTransition.EvalsToInTime.trans` (Mathlib)

## Local abstractions introduced

- `PhyXMini0003.DimLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0003.DimSpeedReal`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0003.DimTime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0003.ParallelGlassSlabExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0003.ParallelGlassSlabFigureReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0003.ParallelGlassSlabGoverningLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
