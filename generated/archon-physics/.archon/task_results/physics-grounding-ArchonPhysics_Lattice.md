# Physics LeanExplore Grounding Log

- Target Lean file: `ArchonPhysics/Lattice.lean`
- Blueprint chapter: `blueprint/src/chapters/ArchonPhysics_Lattice.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:3c427e5e70768af74d9c2494c721703af938d413a7d3c320030880bddce4ac47
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Real.sqrt square root`
- `Real.sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | The square root of a real number. This returns 0 for negative inputs. This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`.
- `Real.coe_sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Square Root of Nonnegative Reals.** For any nonnegative real number $x$, the real-valued square root of $x$ is equal to the square root of $x$ computed in the nonnegative real numbers and then cast to a real number.
- `Real.sqrt_lt'` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Strict Monotonicity of the Square Root.** For any real number $x$ and any positive real number $y$, the square root of $x$ is strictly less than $y$ if and only if $x$ is strictly less than $y^2$.

### Query: `Mass projection`
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.
- `Submodule.starProjection` | module `Mathlib.Analysis.InnerProductSpace.Projection.Basic` | package Mathlib | The orthogonal projection onto a subspace as a map from the full space to itself, as opposed to `Submodule.orthogonalProjectionOnto`, which maps into the subtype. This version is important as it satisfies `IsStarProje...
- `IsMprojection` | module `Mathlib.Analysis.Normed.Module.MStructure` | package Mathlib | A projection on a normed space `X` is said to be an M-projection if, for all `x` in `X`, $\|x\| = max(\|P x\|,\|(1 - P) x\|)$. Note that we write `P • x` instead of `P x` for reasons described in the module docstring.

### Query: `Mass positivity`
- `Mathlib.Meta.Positivity.PositivityExt` | module `Mathlib.Tactic.Positivity.Core` | package Mathlib | An extension for `positivity`.
- `positivity` | module `Mathlib.Tactic.Positivity.Core` | package Mathlib | A definition of type `PositivityExt` tagged `@[positivity t]` extends the `positivity` tactic. The term (with underscores) `t` indicates which expressions this extension accepts. An extension will be given an expressi...
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.

### Query: `Locked mass constructor`
- `Finset.centerMass` | module `Mathlib.Analysis.Convex.Combination` | package Mathlib | Center of mass of a finite collection of points with prescribed weights. Note that we require neither `0 ≤ w i` nor `∑ w = 1`.
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.
- `Mathlib.Tactic.constructorMatching` | module `Mathlib.Tactic.CasesM` | package Mathlib | Core tactic for `constructorm`. Calls `constructor` on all subgoals for which `matcher ldecl.type` returns true. * `recursive`: if true, it calls itself repeatedly on the resulting subgoals * `throwOnNoMatch`: if true...

### Query: `Site`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `AlgebraicGeometry.Scheme.AffineZariskiSite` | module `Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski` | package Mathlib | `X.AffineZariskiSite` is the small affine Zariski site of `X`, whose elements are affine open sets of `X`, and whose arrows are basic open sets `D(f) ⟶ U` for any `f : Γ(X, U)`. Note that this differs from the definit...
- `CategoryTheory.hasSheafifyEssentiallySmallSite` | module `Mathlib.CategoryTheory.Sites.Equivalence` | package Mathlib | **Existence of Sheafification for Essentially Small Sites.** If a category $C$ equipped with a Grothendieck topology $J$ is essentially small, then the category of sheaves on $(C, J)$ with values in a category $A$ adm...

### Query: `Configuration`
- `Configuration.Dual` | module `Mathlib.Combinatorics.Configuration` | package Mathlib | A type synonym.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Turing.ToPartrec.Cfg.ret` | module `Mathlib.Computability.TuringMachine.Config` | package Mathlib | **Return Configuration.** A machine configuration representing a state that is about to pass a list of natural numbers to a specified continuation.

### Query: `site Configuration spec`
- `Configuration.Dual` | module `Mathlib.Combinatorics.Configuration` | package Mathlib | A type synonym.
- `AlgebraicGeometry.Spec` | module `Mathlib.AlgebraicGeometry.Scheme` | package Mathlib | The spectrum of a commutative ring, as a scheme. The notation `Spec(R)` for `(R : Type*) [CommRing R]` to mean `Spec (CommRingCat.of R)` is enabled in the scope `SpecOfNotation`. Please do not use it within Mathlib, b...
- `Configuration.Nondegenerate` | module `Mathlib.Combinatorics.Configuration` | package Mathlib | A configuration is nondegenerate if: 1) there does not exist a line that passes through all of the points, 2) there does not exist a point that is on all of the lines, 3) there is at most one line through any two poin...

### Query: `Positive Mass Config`
- `Finset.centerMass` | module `Mathlib.Analysis.Convex.Combination` | package Mathlib | Center of mass of a finite collection of points with prescribed weights. Note that we require neither `0 ≤ w i` nor `∑ w = 1`.
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.
- `QuantumMechanics.SpaceDQuantumSystem.m_pos` | module `Physlib.QuantumMechanics.SpaceDQuantumSystem` | package PhysLean | **Positivity of Mass.** In a $d$-dimensional quantum system, the mass parameter $m$ is strictly positive.

### Query: `mass`
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Finset.centerMass` | module `Mathlib.Analysis.Convex.Combination` | package Mathlib | Center of mass of a finite collection of points with prescribed weights. Note that we require neither `0 ≤ w i` nor `∑ w = 1`.

### Query: `mass pos`
- `MassUnit.val_pos` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | **Positivity of Mass Unit Values.** For any mass unit, its underlying numerical value is strictly greater than zero.
- `Finset.centerMass` | module `Mathlib.Analysis.Convex.Combination` | package Mathlib | Center of mass of a finite collection of points with prescribed weights. Note that we require neither `0 ≤ w i` nor `∑ w = 1`.
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `MassUnit` (PhysLean)
- `Submodule.starProjection` (Mathlib)
- `IsMprojection` (Mathlib)
- `Mathlib.Meta.Positivity.PositivityExt` (Mathlib)
- `positivity` (Mathlib)
- `MassUnit` (PhysLean)
- `Finset.centerMass` (Mathlib)
- `MassUnit` (PhysLean)
- `Mathlib.Tactic.constructorMatching` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `AlgebraicGeometry.Scheme.AffineZariskiSite` (Mathlib)
- `CategoryTheory.hasSheafifyEssentiallySmallSite` (Mathlib)
- `Configuration.Dual` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Turing.ToPartrec.Cfg.ret` (Mathlib)
- `Configuration.Dual` (Mathlib)
- `AlgebraicGeometry.Spec` (Mathlib)
- `Configuration.Nondegenerate` (Mathlib)
- `Finset.centerMass` (Mathlib)
- `MassUnit` (PhysLean)
- `QuantumMechanics.SpaceDQuantumSystem.m_pos` (PhysLean)
- `MassUnit` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Finset.centerMass` (Mathlib)
- `MassUnit.val_pos` (PhysLean)
- `Finset.centerMass` (Mathlib)
- `MassUnit` (PhysLean)

## Local abstractions introduced

- `ArchonPhysics.Lattice.Configuration`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `ArchonPhysics.Lattice.PositiveMassConfig`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `ArchonPhysics.Lattice.Site`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
