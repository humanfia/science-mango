# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0116.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0116.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:092da7ae1e246b8e9fc700c19613e07f1c2667a9ad271d16f4dbdf903f65b7ba
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

### Query: `nanometers Value`
- `LengthUnit.nanometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of nanometers (10⁻⁹ of a meter).
- `AbsoluteValue` | module `Mathlib.Algebra.Order.AbsoluteValue.Basic` | package Mathlib | `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`: the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle inequality.
- `spectralValue` | module `Mathlib.Analysis.Normed.Unbundled.SpectralNorm` | package Mathlib | The spectral value of a polynomial in `R[X]`, where `R` is a seminormed ring. One motivation for the spectral value: if the norm on `R` is nonarchimedean, and if a monic polynomial splits into linear factors, then its...

### Query: `micrometers Value`
- `LengthUnit.micrometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of micrometers (10⁻⁶ of a meter).
- `AbsoluteValue` | module `Mathlib.Algebra.Order.AbsoluteValue.Basic` | package Mathlib | `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`: the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle inequality.
- `LengthUnit.millimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of millimeters (10⁻³ of a meter).

### Query: `length From Readout`
- `Computation.length_pure` | module `Mathlib.Data.Seq.Computation` | package Mathlib | **Length of a Pure Computation.** The length of a pure computation of a value $a$ is equal to $0$.
- `Computation.Results.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | **Length of a Resulting Computation.** If a terminating computation $s$ results in a value $a$ in exactly $n$ steps, then the length of the computation $s$ is equal to $n$.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation

### Query: `length In Micrometers`
- `LengthUnit.micrometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of micrometers (10⁻⁶ of a meter).
- `LengthUnit.picometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of picometers (10⁻¹² of a meter).
- `LengthUnit.millimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of millimeters (10⁻³ of a meter).

### Query: `Reflected Branch`
- `Physlib.FourTree.instReprBranch` | module `Physlib.Mathematics.DataStructures.FourTree.Basic` | package PhysLean | **Representation of a Branch.** For types $\alpha_2$, $\alpha_3$, and $\alpha_4$ that support string representation, a branch is represented as a string consisting of the prefix "branch", followed by the string repres...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Physlib.FourTree.Branch` | module `Physlib.Mathematics.DataStructures.FourTree.Basic` | package PhysLean | A branch has the data of a term of type `α2` and a multiset of type `Twig α3 α4`.

### Query: `Surface Feature`
- `MeasureTheory.OuterMeasure.map_top_of_surjective` | module `Mathlib.MeasureTheory.OuterMeasure.Operations` | package Mathlib | **Pushforward of the Maximal Outer Measure under a Surjective Function.** If $f: \alpha \to \beta$ is a surjective function, then the pushforward of the maximal outer measure on $\alpha$ is the maximal outer measure o...
- `CategoryTheory.Functor.essSurj_of_surj` | module `Mathlib.CategoryTheory.EssentialImage` | package Mathlib | **Essential Surjectivity from Surjectivity on Objects.** If a functor is surjective on objects, then it is essentially surjective.
- `ωCPO.omegaCompletePartialOrderEqualizer` | module `Mathlib.Order.Category.OmegaCompletePartialOrder` | package Mathlib | **$\omega$-Complete Partial Order on Equalizers.** Given two $\omega$-complete partial orders $\alpha$ and $\beta$ and two continuous functions $f, g: \alpha \to \beta$, the equalizer $\{ a \in \alpha \mid f(a) = g(a)...

### Query: `Optical Medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

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
- `LengthUnit.nanometers` (PhysLean)
- `AbsoluteValue` (Mathlib)
- `spectralValue` (Mathlib)
- `LengthUnit.micrometers` (PhysLean)
- `AbsoluteValue` (Mathlib)
- `LengthUnit.millimeters` (PhysLean)
- `Computation.length_pure` (Mathlib)
- `Computation.Results.length` (Mathlib)
- `Computation.length` (Mathlib)
- `LengthUnit.micrometers` (PhysLean)
- `LengthUnit.picometers` (PhysLean)
- `LengthUnit.millimeters` (PhysLean)
- `Physlib.FourTree.instReprBranch` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Physlib.FourTree.Branch` (PhysLean)
- `MeasureTheory.OuterMeasure.map_top_of_surjective` (Mathlib)
- `CategoryTheory.Functor.essSurj_of_surj` (Mathlib)
- `ωCPO.omegaCompletePartialOrderEqualizer` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `HahnSeries.single` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0116.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0116.BeamDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0116.CompactDiscInterferenceSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0116.DestructivePitDepths`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0116.HasPhysicalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0116.IsLeastDestructivePitDepth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0116.IsUniquelyClosestAnswer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0116.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0116.MatchesProblemAndFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0116.OpticalMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0116.ReflectedBranch`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0116.ReflectingLayer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0116.SatisfiesNormalIncidenceInterferenceLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0116.SurfaceFeature`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
