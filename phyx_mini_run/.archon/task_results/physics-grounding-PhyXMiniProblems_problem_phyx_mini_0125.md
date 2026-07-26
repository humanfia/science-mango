# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0125.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0125.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:a4a84409d5c7f7357fdaab6842d7f93f6072c23f289821d536d312454bb6b72b
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

### Query: `length Value In`
- `LengthUnit.val_ne_zero` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | **Non-zero Length Unit.** For any length unit, its associated numerical value is non-zero.
- `LengthUnit.instInhabited` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | **Default Length Unit.** The type of length units is inhabited, with a default value defined as the positive real number $1$.
- `Computation.length_pure` | module `Mathlib.Data.Seq.Computation` | package Mathlib | **Length of a Pure Computation.** The length of a pure computation of a value $a$ is equal to $0$.

### Query: `meters Value`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `AbsoluteValue` | module `Mathlib.Algebra.Order.AbsoluteValue.Basic` | package Mathlib | `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`: the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle inequality.
- `DimArea.squareMeter_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **Value of a Square Meter in SI Units.** In the International System of Units (SI), the magnitude of one square meter is exactly equal to one.

### Query: `millimeters Value`
- `LengthUnit.millimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of millimeters (10⁻³ of a meter).
- `AbsoluteValue` | module `Mathlib.Algebra.Order.AbsoluteValue.Basic` | package Mathlib | `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`: the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle inequality.
- `DimPressure.millimeterOfMercury` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 millimeter of mercury (133.322387415 pascals).

### Query: `nanometers Value`
- `LengthUnit.nanometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of nanometers (10⁻⁹ of a meter).
- `AbsoluteValue` | module `Mathlib.Algebra.Order.AbsoluteValue.Basic` | package Mathlib | `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`: the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle inequality.
- `spectralValue` | module `Mathlib.Analysis.Normed.Unbundled.SpectralNorm` | package Mathlib | The spectral value of a polynomial in `R[X]`, where `R` is a seminormed ring. One motivation for the spectral value: if the norm on `R` is nonarchimedean, and if a monic polynomial splits into linear factors, then its...

### Query: `Slit Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Complex.slitPlane` | module `Mathlib.Analysis.Complex.Basic` | package Mathlib | The *slit plane* is the complex plane with the closed negative real axis removed.
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.

### Query: `Bright Fringe Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `WriterT.mkLabel'` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Lifting Labels to the Writer Monad Transformer.** Given a monoid $\omega$, a label for a computation in a monad $m$ that accepts a pair $(a, w) \in \alpha \times \omega$ can be transformed into a label for a computa...

### Query: `order`
- `orderOf` | module `Mathlib.GroupTheory.OrderOfElement` | package Mathlib | `orderOf x` is the order of the element `x`, i.e. the `n ≥ 1`, s.t. `x ^ n = 1` if it exists. Otherwise, i.e. if `x` is of infinite order, then `orderOf x` is `0` by convention.
- `OrderHom` | module `Mathlib.Order.Hom.Basic` | package Mathlib | Bundled monotone (aka, increasing) function
- `Mathlib.Tactic.Order.OrderType` | module `Mathlib.Tactic.Order.Preprocessing` | package Mathlib | Supported order types: linear, partial, and preorder.

### Query: `Slit Arrangement`
- `Complex.slitPlane` | module `Mathlib.Analysis.Complex.Basic` | package Mathlib | The *slit plane* is the complex plane with the closed negative real axis removed.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Complex.slitPlane_eq_union` | module `Mathlib.Analysis.Complex.Basic` | package Mathlib | **Characterization of the Slit Plane.** The slit plane is the set of complex numbers $z$ such that either the real part of $z$ is strictly positive or the imaginary part of $z$ is non-zero.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.val_ne_zero` (PhysLean)
- `LengthUnit.instInhabited` (PhysLean)
- `Computation.length_pure` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `AbsoluteValue` (Mathlib)
- `DimArea.squareMeter_in_SI` (PhysLean)
- `LengthUnit.millimeters` (PhysLean)
- `AbsoluteValue` (Mathlib)
- `DimPressure.millimeterOfMercury` (PhysLean)
- `LengthUnit.nanometers` (PhysLean)
- `AbsoluteValue` (Mathlib)
- `spectralValue` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Complex.slitPlane` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `WriterT.mkLabel'` (Mathlib)
- `orderOf` (Mathlib)
- `OrderHom` (Mathlib)
- `Mathlib.Tactic.Order.OrderType` (Mathlib)
- `Complex.slitPlane` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Complex.slitPlane_eq_union` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0125.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0125.BrightFringeLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0125.DoubleSlitExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0125.HasDepictedLayout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0125.HasDistantInPhaseIllumination`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0125.HasPhysicalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0125.HasStatedReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0125.IncidentWavefrontRegime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0125.IsNearestDisplayedChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0125.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0125.SatisfiesConstructiveBrightFringeLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0125.SatisfiesStraightLineScreenGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0125.ScreenOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0125.SlitArrangement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0125.SlitLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
