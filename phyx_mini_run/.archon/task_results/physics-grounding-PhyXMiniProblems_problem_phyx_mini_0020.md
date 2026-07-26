# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0020.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0020.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:bf599a44ae2276b038303ad575546aae19a54af804081ee89a6aaed9aa57e046
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Real.sqrt square root`
- `Real.sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | The square root of a real number. This returns 0 for negative inputs. This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`.
- `Real.coe_sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Square Root of Nonnegative Reals.** For any nonnegative real number $x$, the real-valued square root of $x$ is equal to the square root of $x$ computed in the nonnegative real numbers and then cast to a real number.
- `Real.sqrt_lt'` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Strict Monotonicity of the Square Root.** For any real number $x$ and any positive real number $y$, the square root of $x$ is strictly less than $y$ if and only if $x$ is strictly less than $y^2$.

### Query: `EuclideanSpace vector components`
- `EuclideanSpace` | module `Mathlib.Analysis.InnerProductSpace.PiL2` | package Mathlib | The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional space use `EuclideanSpace 𝕜 (Fin n)`. For the case when `n = Fin _`, there is `!₂[x, y, ...]` notation for building element...
- `Space.fderiv_space_components` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | **Components of the Fréchet Derivative of a Vector-Valued Function.** For a differentiable function $f$ mapping from a normed space $M$ to the space of $d$-dimensional vectors $\mathbb{R}^d$, the $\mu$-th component of...
- `Lorentz.ContrMod.toSpace` | module `Physlib.Relativity.Tensors.RealTensor.Vector.Pre.Modules` | package PhysLean | The underlying space part of a `ContrMod` formed by removing the first element. A better name for this might be `tail`.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Plane`
- `UpperHalfPlane` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Basic` | package Mathlib | The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace
- `Complex.slitPlane` | module `Mathlib.Analysis.Complex.Basic` | package Mathlib | The *slit plane* is the complex plane with the closed negative real axis removed.
- `MSSMACC.planeY₃B₃` | module `Physlib.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.OrthogY3B3.PlaneWithY3B3` | package PhysLean | The plane of linear solutions spanned by `Y₃`, `B₃` and `R`, a point orthogonal to `Y₃` and `B₃`.

### Query: `si Length Value`
- `UnitChoices.SI_length` | module `Physlib.Units.Basic` | package PhysLean | **SI Length Unit.** In the International System of Units (SI), the fundamental unit of length is defined to be the meter.
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `Light Ray`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `Module.Ray.linearEquiv_smul_eq_map` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | The action via `LinearEquiv.apply_distribMulAction` corresponds to `Module.Ray.map`.
- `Module.Ray` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | A ray (equivalence class of nonzero vectors with common positive multiples) in a module.

### Query: `Passes Through`
- `Mathlib.TacticAnalysis.runPasses` | module `Mathlib.Tactic.TacticAnalysis` | package Mathlib | Run the tactic analysis passes from `configs` on the tactic sequences in `stx`, using `trees` to get the infotrees.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Function.FactorsThrough` | module `Mathlib.Logic.Function.Basic` | package Mathlib | g factors through f : `f a = f b → g a = g b`

### Query: `right Semicircle`
- `RightCancelSemigroup` | module `Mathlib.Algebra.Group.Defs` | package Mathlib | A `RightCancelSemigroup` is a semigroup such that `a * b = c * b` implies `a = c`.
- `IsRightRegular` | module `Mathlib.Algebra.Regular.Defs` | package Mathlib | A right-regular element is an element `c` such that multiplication on the right by `c` is injective.
- `sdiff_sdiff_right` | module `Mathlib.Order.BooleanAlgebra.Basic` | package Mathlib | **Relative Complement of a Relative Complement.** For any elements $x, y,$ and $z$ in a generalized Boolean algebra (or a distributive lattice with a relative complement), the relative complement of $y \setminus z$ in...

### Query: `Cylinder Mirror Experiment`
- `HomotopicalAlgebra.Cylinder.symm` | module `Mathlib.AlgebraicTopology.ModelCategory.Cylinder` | package Mathlib | The cylinder object obtained by switching the two inclusions.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`

### Query: `Snell Law At Interface`
- `ProbabilityTheory.HasGaussianLaw` | module `Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def` | package Mathlib | The predicate `HasGaussianLaw X P` means that under the measure `P`, `X` has a Gaussian distribution.
- `InnerProductGeometry.sin_angle_mul_norm_eq_sin_angle_mul_norm` | module `Mathlib.Geometry.Euclidean.Triangle` | package Mathlib | **Law of sines** (sine rule), vector angle form.
- `EuclideanGeometry.law_sin` | module `Mathlib.Geometry.Euclidean.Triangle` | package Mathlib | **Alias** of `EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist`. --- **Law of sines** (sine rule), angle-at-point form.

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `EuclideanSpace` (Mathlib)
- `Space.fderiv_space_components` (PhysLean)
- `Lorentz.ContrMod.toSpace` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `UpperHalfPlane` (Mathlib)
- `Complex.slitPlane` (Mathlib)
- `MSSMACC.planeY₃B₃` (PhysLean)
- `UnitChoices.SI_length` (PhysLean)
- `LengthUnit` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `SameRay` (Mathlib)
- `Module.Ray.linearEquiv_smul_eq_map` (Mathlib)
- `Module.Ray` (Mathlib)
- `Mathlib.TacticAnalysis.runPasses` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Function.FactorsThrough` (Mathlib)
- `RightCancelSemigroup` (Mathlib)
- `IsRightRegular` (Mathlib)
- `sdiff_sdiff_right` (Mathlib)
- `HomotopicalAlgebra.Cylinder.symm` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `ProbabilityTheory.HasGaussianLaw` (Mathlib)
- `InnerProductGeometry.sin_angle_mul_norm_eq_sin_angle_mul_norm` (Mathlib)
- `EuclideanGeometry.law_sin` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0020.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0020.CylinderFigureReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0020.CylinderMirrorExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0020.GeometricalOpticsLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0020.LightRay`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0020.LightRay.PassesThrough`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0020.Plane`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0020.RoundsToNearestHundredth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0020.SnellLawAtInterface`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0020.SpecularReflectionAtMirror`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
