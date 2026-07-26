# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0083.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0083.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:664c125ed4ffafb3d8cd63ea994ba4c78278eca52da26a4bb616f70b64745544
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Dim Length`
- `Order.LTSeries.length_le_krullDim` | module `Mathlib.Order.KrullDimension` | package Mathlib | **Length of a Strictly Increasing Sequence and Krull Dimension.** For any strictly increasing sequence in a preorder, its length is less than or equal to the Krull dimension of that preorder.
- `Dimension.L𝓭_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass component of the length dimension.** The mass dimension component of the length dimension $L_d$ is equal to $0$.
- `Order.krullDim_eq_iSup_length` | module `Mathlib.Order.KrullDimension` | package Mathlib | A definition of krullDim for nonempty `α` that avoids `WithBot`

### Query: `length Value In`
- `LengthUnit.val_ne_zero` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | **Non-zero Length Unit.** For any length unit, its associated numerical value is non-zero.
- `LengthUnit.instInhabited` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | **Default Length Unit.** The type of length units is inhabited, with a default value defined as the positive real number $1$.
- `Computation.length_pure` | module `Mathlib.Data.Seq.Computation` | package Mathlib | **Length of a Pure Computation.** The length of a pure computation of a value $a$ is equal to $0$.

### Query: `meters Value`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `AbsoluteValue` | module `Mathlib.Algebra.Order.AbsoluteValue.Basic` | package Mathlib | `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`: the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle inequality.
- `DimArea.squareMeter_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **Value of a Square Meter in SI Units.** In the International System of Units (SI), the magnitude of one square meter is exactly equal to one.

### Query: `nanometers Value`
- `LengthUnit.nanometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of nanometers (10⁻⁹ of a meter).
- `AbsoluteValue` | module `Mathlib.Algebra.Order.AbsoluteValue.Basic` | package Mathlib | `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`: the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle inequality.
- `spectralValue` | module `Mathlib.Analysis.Normed.Unbundled.SpectralNorm` | package Mathlib | The spectral value of a polynomial in `R[X]`, where `R` is a seminormed ring. One motivation for the spectral value: if the norm on `R` is nonarchimedean, and if a monic polynomial splits into linear factors, then its...

### Query: `micrometers Value`
- `LengthUnit.micrometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of micrometers (10⁻⁶ of a meter).
- `AbsoluteValue` | module `Mathlib.Algebra.Order.AbsoluteValue.Basic` | package Mathlib | `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`: the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle inequality.
- `LengthUnit.millimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of millimeters (10⁻³ of a meter).

### Query: `Single Slit Experiment`
- `Complex.slitPlane` | module `Mathlib.Analysis.Complex.Basic` | package Mathlib | The *slit plane* is the complex plane with the closed negative real axis removed.
- `Pi.single` | module `Mathlib.Algebra.Notation.Pi.Basic` | package Mathlib | The function supported at `i`, with value `x` there, and `0` elsewhere.
- `Sat.Fmla.one` | module `Mathlib.Tactic.Sat.FromLRAT` | package Mathlib | A single clause as a formula.

### Query: `Alpha Versus Sine Theta Graph`
- `Asymptotics.IsTheta` | module `Mathlib.Analysis.Asymptotics.Defs` | package Mathlib | We say that `f` is `Θ(g)` along a filter `l` (notation: `f =Θ[l] g`) if `f =O[l] g` and `g =O[l] f`.
- `Real.Angle.sign` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | The sign of a `Real.Angle` is `0` if the angle is `0` or `π`, `1` if the angle is strictly between `0` and `π` and `-1` is the angle is strictly between `-π` and `0`. It is defined as the sign of the sine of the angle.
- `sineTerm` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent` | package Mathlib | The main term in the infinite product for sine.

### Query: `Satisfies Single Slit Phase Law`
- `Complex.slitPlane` | module `Mathlib.Analysis.Complex.Basic` | package Mathlib | The *slit plane* is the complex plane with the closed negative real axis removed.
- `Sat.Fmla.one` | module `Mathlib.Tactic.Sat.FromLRAT` | package Mathlib | A single clause as a formula.
- `CategoryTheory.Presieve.FamilyOfElements.compatible_singleton_iff` | module `Mathlib.CategoryTheory.Sites.IsSheafFor` | package Mathlib | **Compatibility of a Family on a Singleton Presieve.** A family of elements $x$ for the singleton presieve $\{f\}$ (where $f: X \to Y$) is compatible if and only if for every pair of morphisms $p_1, p_2: Z \to X$ such...

### Query: `Has Stated Wavelength And Graph Readouts`
- `RingHom.HasEqualizers.and` | module `Mathlib.RingTheory.RingHomProperties` | package Mathlib | **Intersection of Properties with Equalizers.** If two properties of ring homomorphisms, $P$ and $Q$, are both stable under taking equalizers, then their conjunction (the property that a homomorphism satisfies both $P...
- `Turing.TM1to1.supportsStmt_read` | module `Mathlib.Computability.TuringMachine.PostTuringMachine` | package Mathlib | **Support of the Read Statement.** A finite set of labels $S$ supports a `read` statement if, for every possible symbol $a$ that can be read from the tape, the set $S$ supports the statement $f(a)$ that is executed af...
- `Graph.IsLink.eq_and_eq_or_eq_and_eq` | module `Mathlib.Combinatorics.Graph.Basic` | package Mathlib | **Uniqueness of Edge Endpoints.** If an edge $e$ in a multigraph connects a pair of vertices $x$ and $y$, and the same edge $e$ also connects a pair of vertices $x'$ and $y'$, then the set of endpoints $\{x, y\}$ must...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Order.LTSeries.length_le_krullDim` (Mathlib)
- `Dimension.L𝓭_mass` (PhysLean)
- `Order.krullDim_eq_iSup_length` (Mathlib)
- `LengthUnit.val_ne_zero` (PhysLean)
- `LengthUnit.instInhabited` (PhysLean)
- `Computation.length_pure` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `AbsoluteValue` (Mathlib)
- `DimArea.squareMeter_in_SI` (PhysLean)
- `LengthUnit.nanometers` (PhysLean)
- `AbsoluteValue` (Mathlib)
- `spectralValue` (Mathlib)
- `LengthUnit.micrometers` (PhysLean)
- `AbsoluteValue` (Mathlib)
- `LengthUnit.millimeters` (PhysLean)
- `Complex.slitPlane` (Mathlib)
- `Pi.single` (Mathlib)
- `Sat.Fmla.one` (Mathlib)
- `Asymptotics.IsTheta` (Mathlib)
- `Real.Angle.sign` (Mathlib)
- `sineTerm` (Mathlib)
- `Complex.slitPlane` (Mathlib)
- `Sat.Fmla.one` (Mathlib)
- `CategoryTheory.Presieve.FamilyOfElements.compatible_singleton_iff` (Mathlib)
- `RingHom.HasEqualizers.and` (Mathlib)
- `Turing.TM1to1.supportsStmt_read` (Mathlib)
- `Graph.IsLink.eq_and_eq_or_eq_and_eq` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0083.AlphaVersusSineThetaGraph`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0083.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0083.DimLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0083.HasStatedWavelengthAndGraphReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0083.SatisfiesSingleSlitPhaseLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0083.SingleSlitExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
