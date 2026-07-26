# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0043.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0043.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:4cc42c322d12905544f84433af05f6b8a09375ddc216d4ffda0fba3c2ec148cd
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Signed Length`
- `MeasureTheory.SignedMeasure` | module `Mathlib.MeasureTheory.VectorMeasure.Basic` | package Mathlib | A `SignedMeasure` is an `ℝ`-vector measure.
- `signedDist` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | The signed distance between two points `p` and `q`, in the direction of a reference vector `v`. It is the size of `q - p` in the direction of `v`. In the degenerate case `v = 0`, it returns `0`. TODO: once we have a t...
- `signedDist_neg` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | **Negation of the Reference Vector in Signed Distance.** The signed distance from a point $p$ to a point $q$ with respect to the negation of a reference vector $v$ is equal to the negative of the signed distance from...

### Query: `Length Magnitude`
- `List.Vector.length` | module `Mathlib.Data.Vector.Defs` | package Mathlib | The length of a vector.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.

### Query: `signed Length In Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.chains` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a chain (20.1168 meters)

### Query: `length Magnitude In Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `LengthUnit.kilometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of kilometers (10³ meters).

### Query: `Lens Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `YoungDiagram.rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | List of row lengths of a Young diagram
- `YoungDiagram.get_rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | **Row Length Consistency.** For a Young diagram $\mu$, the $i$-th element of the list of row lengths $\mu.\text{rowLens}$ is equal to the length of the $i$-th row $\mu.\text{rowLen } i$, provided that $i$ is a valid i...

### Query: `Lens Kind`
- `YoungDiagram.rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | List of row lengths of a Young diagram
- `YoungDiagram.rowLens_sorted` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | **Descending Order of Row Lengths in a Young Diagram.** For any Young diagram, the sequence of its row lengths is sorted in descending order.
- `YoungDiagram.get_rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | **Row Length Consistency.** For a Young diagram $\mu$, the $i$-th element of the list of row lengths $\mu.\text{rowLens}$ is equal to the length of the $i$-th row $\mu.\text{rowLen } i$, provided that $i$ is a valid i...

### Query: `Image Point Label`
- `IsGenericPoint.image` | module `Mathlib.Topology.Sober` | package Mathlib | **Image of a Generic Point.** If $x$ is a generic point of a subset $S$ of a topological space, and $f$ is a continuous map to another topological space, then $f(x)$ is a generic point of the closure of the image $f(S)$.
- `Set.image` | module `Mathlib.Data.Set.Defs` | package Mathlib | The image of `s : Set α` by `f : α → β`, written `f '' s`, is the set of `b : β` such that `f a = b` for some `a ∈ s`.
- `OnePoint.compl_image_coe` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | **Complement of an Image in the One-Point Compactification.** For any subset $s$ of a space $X$, the complement of the image of $s$ under the canonical embedding into the one-point compactification of $X$ is equal to...

### Query: `Figure Point Label`
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`
- `Equiv.pointReflection` | module `Mathlib.Algebra.Torsor.Defs` | package Mathlib | Point reflection in `x` as a permutation.

### Query: `Principal Ray Label`
- `Ordinal.IsPrincipal` | module `Mathlib.SetTheory.Ordinal.Principal` | package Mathlib | An ordinal `o` is said to be principal (or indecomposable) under an operation when `Iio o` is closed under that operation. For simplicity, we break usual convention and regard `0` as principal.
- `PrincipalSeg.ofElement_top` | module `Mathlib.Order.InitialSeg` | package Mathlib | **Principal Segment Element and Top.** For any binary relation $r$ on a set $\alpha$ and any element $a \in \alpha$, the principal segment from the subrelation $\{x \mid r(x, a)\}$ to $r$ is defined such that its prin...
- `RayVector` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Nonzero vectors, as used to define rays. This type depends on an unused argument `R` so that `RayVector.Setoid` can be an instance.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `MeasureTheory.SignedMeasure` (Mathlib)
- `signedDist` (Mathlib)
- `signedDist_neg` (Mathlib)
- `List.Vector.length` (Mathlib)
- `Computation.length` (Mathlib)
- `LengthUnit` (PhysLean)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.chains` (PhysLean)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `LengthUnit.kilometers` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `YoungDiagram.rowLens` (Mathlib)
- `YoungDiagram.get_rowLens` (Mathlib)
- `YoungDiagram.rowLens` (Mathlib)
- `YoungDiagram.rowLens_sorted` (Mathlib)
- `YoungDiagram.get_rowLens` (Mathlib)
- `IsGenericPoint.image` (Mathlib)
- `Set.image` (Mathlib)
- `OnePoint.compl_image_coe` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `OnePoint` (Mathlib)
- `Equiv.pointReflection` (Mathlib)
- `Ordinal.IsPrincipal` (Mathlib)
- `PrincipalSeg.ofElement_top` (Mathlib)
- `RayVector` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0043.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0043.FigurePointLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0043.HasPhysicalConfiguration`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0043.ImageOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0043.ImagePointLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0043.LengthMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0043.LensKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0043.LensLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0043.MatchesFigureGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0043.MatchesRayDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0043.MatchesSourceReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0043.PrincipalRayLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0043.PrincipalRayRole`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0043.SatisfiesThinLensEquationAt`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0043.SatisfiesTransverseMagnificationAt`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0043.SignedLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0043.ThinLens`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0043.TwoConvergingLensSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
