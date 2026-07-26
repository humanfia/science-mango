# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0121.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0121.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:f74e1b103cf92ee0c6c6d65ff83ec763675c2fdf8654074128fc85f1d806b36b
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

### Query: `milliradians Value`
- `spectralValue` | module `Mathlib.Analysis.Normed.Unbundled.SpectralNorm` | package Mathlib | The spectral value of a polynomial in `R[X]`, where `R` is a seminormed ring. One motivation for the spectral value: if the norm on `R` is nonarchimedean, and if a monic polynomial splits into linear factors, then its...
- `Real.Angle.toReal` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | Convert a `Real.Angle` to a real number in the interval `Ioc (-π) π`.
- `LengthUnit.millimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of millimeters (10⁻³ of a meter).

### Query: `Source Label`
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `WriterT.mkLabel` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Writer Monad Transformer Label Mapping.** Given a type $\omega$ with an empty collection element, a continuation label for computations in a monad $m$ that accepts a pair $(a, w) \in \alpha \times \omega$ can be tra...
- `Mathlib.Tactic.Monoidal.srcExpr` | module `Mathlib.Tactic.CategoryTheory.Monoidal.Datatypes` | package Mathlib | The domain of a morphism.

### Query: `Source Role`
- `Mathlib.Tactic.Monoidal.srcExpr` | module `Mathlib.Tactic.CategoryTheory.Monoidal.Datatypes` | package Mathlib | The domain of a morphism.
- `Mathlib.Tactic.Bicategory.srcExpr` | module `Mathlib.Tactic.CategoryTheory.Bicategory.Datatypes` | package Mathlib | The domain of a morphism.
- `CategoryTheory.Arrow.leftFunc` | module `Mathlib.CategoryTheory.Comma.Arrow` | package Mathlib | The functor sending an arrow to its source.

### Query: `role`
- `Set.range` | module `Mathlib.Data.Set.Operations` | package Mathlib | Range of a function. This function is more flexible than `f '' univ`, as the image requires that the domain is in Type and not an arbitrary Sort.
- `FieldSpecification.crAnFieldOpToCreateAnnihilate` | module `Physlib.QFT.PerturbationTheory.FieldSpecification.CrAnFieldOp` | package PhysLean | For a field specification `𝓕`, `𝓕.crAnFieldOpToCreateAnnihilate` is the map from `𝓕.CrAnFieldOp` to `CreateAnnihilate` taking `φ` to `create` if - `φ` corresponds to an incoming asymptotic field operator or the creati...
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

### Query: `Screen Point`
- `CategoryTheory.GrothendieckTopology.Point` | module `Mathlib.CategoryTheory.Sites.Point.Basic` | package Mathlib | Given `J` a Grothendieck topology on a category `C`, a point of the site `(C, J)` consists of a functor `fiber : C ⥤ Type w` such that the category `fiber.Elements` is initially small (which allows defining the fiber...
- `OnePoint.infty` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The point at infinity
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`

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
- `spectralValue` (Mathlib)
- `Real.Angle.toReal` (Mathlib)
- `LengthUnit.millimeters` (PhysLean)
- `MonadCont.Label` (Mathlib)
- `WriterT.mkLabel` (Mathlib)
- `Mathlib.Tactic.Monoidal.srcExpr` (Mathlib)
- `Mathlib.Tactic.Monoidal.srcExpr` (Mathlib)
- `Mathlib.Tactic.Bicategory.srcExpr` (Mathlib)
- `CategoryTheory.Arrow.leftFunc` (Mathlib)
- `Set.range` (Mathlib)
- `FieldSpecification.crAnFieldOpToCreateAnnihilate` (PhysLean)
- `HahnSeries.single` (Mathlib)
- `CategoryTheory.GrothendieckTopology.Point` (Mathlib)
- `OnePoint.infty` (Mathlib)
- `OnePoint` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0121.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0121.DimLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0121.FresnelBiprismInterferometer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0121.HasPhysicalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0121.HasStatedProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0121.MatchesDisplayedPrecision`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0121.OpticalMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0121.SatisfiesControlledAdjacentFringeLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0121.SatisfiesControlledThinBiprismImageLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0121.ScreenPoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0121.SourceLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0121.SourceRole`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
