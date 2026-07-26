# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0087.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0087.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:00ba44d5f3d5eca22a5c25316ef97fe9c46489dd7f43188dfa0a57759fd34634
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

### Query: `nanometers Value`
- `LengthUnit.nanometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of nanometers (10⁻⁹ of a meter).
- `AbsoluteValue` | module `Mathlib.Algebra.Order.AbsoluteValue.Basic` | package Mathlib | `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`: the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle inequality.
- `spectralValue` | module `Mathlib.Analysis.Normed.Unbundled.SpectralNorm` | package Mathlib | The spectral value of a polynomial in `R[X]`, where `R` is a seminormed ring. One motivation for the spectral value: if the norm on `R` is nonarchimedean, and if a monic polynomial splits into linear factors, then its...

### Query: `Source Label`
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `WriterT.mkLabel` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Writer Monad Transformer Label Mapping.** Given a type $\omega$ with an empty collection element, a continuation label for computations in a monad $m$ that accepts a pair $(a, w) \in \alpha \times \omega$ can be tra...
- `Mathlib.Tactic.Monoidal.srcExpr` | module `Mathlib.Tactic.CategoryTheory.Monoidal.Datatypes` | package Mathlib | The domain of a morphism.

### Query: `Observation Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `WriterT.mkLabel'` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Lifting Labels to the Writer Monad Transformer.** Given a monoid $\omega$, a label for a computation in a monad $m$ that accepts a pair $(a, w) \in \alpha \times \omega$ can be transformed into a label for a computa...

### Query: `Isotropic Point Source`
- `stereographic'_source` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Domain of the Stereographic Projection.** For an $(n+1)$-dimensional real inner product space $E$ and a point $v$ on the unit sphere in $E$, the domain (source) of the stereographic projection from the sphere with p...
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`
- `Pointed.Iso.mk_hom_toFun` | module `Mathlib.CategoryTheory.Category.Pointed` | package Mathlib | **Isomorphism Construction for Pointed Types.** Given two pointed types $\alpha$ and $\beta$, an isomorphism between them can be constructed from an equivalence of their underlying types $e: \alpha \simeq \beta$, prov...

### Query: `Two Point Source Setup`
- `TwoPointing.TwoP` | module `Mathlib.CategoryTheory.Category.TwoP` | package Mathlib | **Alias** of `TwoP.of`. --- Turns a two-pointing into a two-pointed type.
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`
- `Equiv.pointReflection` | module `Mathlib.Algebra.Torsor.Defs` | package Mathlib | Point reflection in `x` as a permutation.

### Query: `x Coordinate`
- `Polynomial.X` | module `Mathlib.Algebra.Polynomial.Basic` | package Mathlib | `X` is the polynomial variable (aka indeterminate).
- `LipschitzWith.coordinate` | module `Mathlib.Analysis.Normed.Lp.lpSpace` | package Mathlib | **Lipschitz Continuity of Functions into $L^\infty$.** A function $f$ from a pseudometric space into the space of bounded sequences $\ell^\infty(\iota, \mathbb{R})$ is Lipschitz continuous with constant $K$ if and onl...
- `WeierstrassCurve.Affine.Point.xRep_zero` | module `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point` | package Mathlib | **Projective Representative of the Zero Point's x-coordinate.** The projective representative of the $x$-coordinate for the zero point on an affine Weierstrass curve is given by the vector $[1, 0]$.

### Query: `y Coordinate`
- `WeierstrassCurve.Jacobian.negY` | module `Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula` | package Mathlib | The `Y`-coordinate of a representative of `-P` for a Jacobian point representative `P` on a Weierstrass curve.
- `WeierstrassCurve.Projective.negY` | module `Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula` | package Mathlib | The `Y`-coordinate of a representative of `-P` for a projective point representative `P` on a Weierstrass curve.
- `Pell.Solution₁.y` | module `Mathlib.NumberTheory.Pell` | package Mathlib | The `y` component of a solution to the Pell equation `x^2 - d*y^2 = 1`

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
- `LengthUnit.nanometers` (PhysLean)
- `AbsoluteValue` (Mathlib)
- `spectralValue` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `WriterT.mkLabel` (Mathlib)
- `Mathlib.Tactic.Monoidal.srcExpr` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `WriterT.mkLabel'` (Mathlib)
- `stereographic'_source` (Mathlib)
- `OnePoint` (Mathlib)
- `Pointed.Iso.mk_hom_toFun` (Mathlib)
- `TwoPointing.TwoP` (Mathlib)
- `OnePoint` (Mathlib)
- `Equiv.pointReflection` (Mathlib)
- `Polynomial.X` (Mathlib)
- `LipschitzWith.coordinate` (Mathlib)
- `WeierstrassCurve.Affine.Point.xRep_zero` (Mathlib)
- `WeierstrassCurve.Jacobian.negY` (Mathlib)
- `WeierstrassCurve.Projective.negY` (Mathlib)
- `Pell.Solution₁.y` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0087.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0087.DimLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0087.HasStatedFigureReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0087.HasStatedPhaseCalibrationAtP1`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0087.IsotropicPointSource`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0087.ObservationLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0087.SatisfiesIsotropicPhasePropagation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0087.SourceLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0087.TwoPointSourceSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
