# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0077.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0077.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:27fcfcee9bffe24158be2e308ec8329a916fc8d2dd9478bd8a302c6e28405106
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Gauss law divergence electric field`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Electromagnetism.ElectricField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The electric field is a map from `d`+1 dimensional spacetime to the vector space `ℝ^d`.
- `Space.distDiv_inv_pow_eq_dim` | module `Physlib.SpaceAndTime.Space.Norm.Basic` | package PhysLean | The distributional divergence of the radial field `x ↦ ‖x‖ ^ (-d) • x` (i.e. `x / ‖x‖ ^ d`) equals `d * volume (Metric.ball 0 1)` — the surface area of the unit sphere `S^{d-1}` — times the Dirac delta at the origin....

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Length Magnitude`
- `List.Vector.length` | module `Mathlib.Data.Vector.Defs` | package Mathlib | The length of a vector.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.

### Query: `length In Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `Figure Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `WriterT.mkLabel'` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Lifting Labels to the Writer Monad Transformer.** Given a monoid $\omega$, a label for a computation in a monad $m$ that accepts a pair $(a, w) \in \alpha \times \omega$ can be transformed into a label for a computa...

### Query: `Lens Kind`
- `YoungDiagram.rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | List of row lengths of a Young diagram
- `YoungDiagram.rowLens_sorted` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | **Descending Order of Row Lengths in a Young Diagram.** For any Young diagram, the sequence of its row lengths is sorted in descending order.
- `YoungDiagram.get_rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | **Row Length Consistency.** For a Young diagram $\mu$, the $i$-th element of the list of row lengths $\mu.\text{rowLens}$ is equal to the length of the $i$-th row $\mu.\text{rowLen } i$, provided that $i$ is a valid i...

### Query: `Mirror Kind`
- `Polynomial.mirror_eq_iff` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Mirror Symmetry of Polynomials.** For any two polynomials $p$ and $q$, the mirror of $p$ is equal to $q$ if and only if $p$ is equal to the mirror of $q$.
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `Polynomial.mirror_mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Involution of the Mirror Polynomial.** For any polynomial $p$, applying the mirror operation twice results in the original polynomial $p$.

### Query: `Arrow Orientation`
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `Orientation` | module `Mathlib.LinearAlgebra.Orientation` | package Mathlib | An orientation of a module, intended to be used when `ι` is a `Fintype` with the same cardinality as a basis.
- `Quiver.reverse_reverse` | module `Mathlib.Combinatorics.Quiver.Symmetric` | package Mathlib | **Involutive Property of Arrow Reversal.** In a quiver equipped with an involutive reversal, reversing the reverse of an arrow $f$ from vertex $a$ to vertex $b$ yields the original arrow $f$.

### Query: `Optical Approximation`
- `bernsteinApproximation` | module `Mathlib.Analysis.SpecialFunctions.Bernstein` | package Mathlib | The `n`-th approximation of a continuous function on `[0,1]` by Bernstein polynomials, given by `∑ k, bernstein n k x • f (k/n)`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `bernsteinApproximation_uniform` | module `Mathlib.Analysis.SpecialFunctions.Bernstein` | package Mathlib | The Bernstein approximations ``` ∑ k : Fin (n+1), f (k/n : ℝ) * n.choose k * x^k * (1-x)^(n-k) ``` for a continuous function `f : C([0,1], ℝ)` converge uniformly to `f` as `n` tends to infinity. This is the proof give...

### Query: `Object Arrow`
- `CategoryTheory.Arrow` | module `Mathlib.CategoryTheory.Comma.Arrow` | package Mathlib | The arrow category of `T` has as objects all morphisms in `T` and as morphisms commutative squares in `T`.
- `CategoryTheory.Arrow.mk_hom` | module `Mathlib.CategoryTheory.Comma.Arrow` | package Mathlib | **The Arrow Object Constructor.** Given an object $T$ in a category, any morphism $f : X \to Y$ between objects $X$ and $Y$ in $T$ defines an object in the arrow category of $T$, where the domain (left) of the arrow i...
- `CategoryTheory.SmallObject.propArrow` | module `Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument` | package Mathlib | The class of morphisms in `Arrow C` which on the left side are pushouts of coproducts of morphisms in `I`, and which are isomorphisms on the right side.

## Grounded Mathlib/PhysLean names

- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.ElectricField` (PhysLean)
- `Space.distDiv_inv_pow_eq_dim` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `List.Vector.length` (Mathlib)
- `Computation.length` (Mathlib)
- `LengthUnit` (PhysLean)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `WriterT.mkLabel'` (Mathlib)
- `YoungDiagram.rowLens` (Mathlib)
- `YoungDiagram.rowLens_sorted` (Mathlib)
- `YoungDiagram.get_rowLens` (Mathlib)
- `Polynomial.mirror_eq_iff` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `Polynomial.mirror_mirror` (Mathlib)
- `Orientation.oangle` (Mathlib)
- `Orientation` (Mathlib)
- `Quiver.reverse_reverse` (Mathlib)
- `bernsteinApproximation` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `bernsteinApproximation_uniform` (Mathlib)
- `CategoryTheory.Arrow` (Mathlib)
- `CategoryTheory.Arrow.mk_hom` (Mathlib)
- `CategoryTheory.SmallObject.propArrow` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0077.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0077.ArrowOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0077.FigureLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0077.FinalImage`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0077.HasPhysicalLengthMagnitudes`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0077.LengthMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0077.LensKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0077.LensMirrorRoundTrip`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0077.MatchesDisplayedImageHeight`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0077.MatchesFigureReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0077.MirrorKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0077.ObjectArrow`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0077.OpticalApproximation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0077.ParaxialRay`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0077.SatisfiesParaxialRoundTripImagingLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0077.SphericalMirror`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0077.ThinLens`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
