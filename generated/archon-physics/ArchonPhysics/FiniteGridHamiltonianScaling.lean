import ArchonPhysics.HamiltonianScaling

/-!
# Finite-graph and finite-grid Hamiltonian scaling

The existing lattice foundation is one-dimensional: periodic sites are
`ZMod N`, and a separate module treats an open chain.  This module supplies a
dimension-independent finite-edge formulation.  The scaling proof uses only
finiteness of the vertex and directed-edge sets, so it applies to every
finite graph after choosing one orientation for each odd-degree bond.

For convenience, finite undirected edges are `Sym2 V`, while the Hamiltonian
uses directed representatives `V × V`; orientation matters for odd degree.
Uniform open and periodic grids in arbitrary dimension, and explicit 2D/3D
aliases and scaling endpoints, are provided below.

The release-version 2D/3D numerical setup uses fixed boundary conditions.
The open boxes below delete crossing bonds, so they describe free/open scalar
boundaries rather than pinned or Dirichlet data. The generic finite-edge
theorem is a scalar nearest-neighbour specialization and homogeneity template.
Vector displacements, tensor couplings, and pinned boundary terms require
their own homogeneous adapters. Periodic multidimensional grids are also a
conditional algebraic extension; their positive-coordinate orientation is
exposed only for side length at least three. No numerical claim is made for
either extension. The degree-three endpoint records cubic-leading low-energy
scaling, not stability of a pure cubic potential.
-/

namespace ArchonPhysics.FiniteGridHamiltonianScaling

open ArchonPhysics.HamiltonianScaling

noncomputable section

/-! ## Generic finite directed-edge Hamiltonian -/

/-- An unordered finite bond set.  A cubic interaction additionally requires
an orientation before evaluation. -/
abbrev FiniteUndirectedEdges (V : Type*) := Finset (Sym2 V)

/-- A finite set of oriented bonds.  This is the minimal data used by the
Hamiltonian and also permits directed finite graphs. -/
abbrev FiniteDirectedEdges (V : Type*) := Finset (V × V)

/-- A strictly positive mass at every vertex of an arbitrary finite graph. -/
structure PositiveMassProfile (V : Type*) where
  mass : V → Real
  mass_pos : ∀ v, 0 < mass v

/-- The oriented bond displacement `q(head) - q(tail)`. -/
def edgeDifference {V : Type*} (q : V → Real) (edge : V × V) : Real :=
  q edge.2 - q edge.1

/-- Pointwise amplitude rescaling by `sqrt epsilon`. -/
def rescaleField {V : Type*} (epsilon : Real) (q : V → Real) : V → Real :=
  fun v ↦ Real.sqrt epsilon * q v

/-- The coupling remaining after extracting the common energy scale. -/
def graphEffectiveCoupling (lambda epsilon : Real) (degree : Nat) : Real :=
  lambda * Real.rpow epsilon (((degree : Real) - 2) / 2)

/-- Nearest-neighbour polynomial Hamiltonian on a finite directed edge set.
For an undirected graph, `edges` contains one chosen orientation per bond. -/
def finiteEdgeHamiltonian {V : Type*} [Fintype V]
    (edges : FiniteDirectedEdges V) (mass : PositiveMassProfile V)
    (degree : Nat) (lambda : Real) (p q : V → Real) : Real :=
  (∑ v, p v ^ 2 / (2 * mass.mass v)) +
    ∑ edge ∈ edges,
      (edgeDifference q edge ^ 2 / 2 +
        (lambda / (degree : Real)) * edgeDifference q edge ^ degree)

/-- Bond differences are homogeneous of degree one under amplitude
rescaling. -/
theorem edgeDifference_rescale {V : Type*} (epsilon : Real)
    (q : V → Real) (edge : V × V) :
    edgeDifference (rescaleField epsilon q) edge =
      Real.sqrt epsilon * edgeDifference q edge := by
  simp only [edgeDifference, rescaleField]
  ring

/-- Every finite directed-edge Hamiltonian obeys the exact energy-amplitude
scaling `H_lambda(sqrt epsilon p, sqrt epsilon q) = epsilon H_g(p,q)` with
`g = lambda * epsilon^((degree - 2)/2)`. -/
theorem finiteEdgeHamiltonian_rescale {V : Type*} [Fintype V]
    (edges : FiniteDirectedEdges V) (mass : PositiveMassProfile V)
    (degree : Nat) (_hdegree : 3 ≤ degree)
    (lambda epsilon : Real) (hepsilon : 0 < epsilon)
    (p q : V → Real) :
    finiteEdgeHamiltonian edges mass degree lambda
        (rescaleField epsilon p) (rescaleField epsilon q) =
      epsilon * finiteEdgeHamiltonian edges mass degree
        (graphEffectiveCoupling lambda epsilon degree) p q := by
  have hsqrt_sq : Real.sqrt epsilon ^ 2 = epsilon :=
    Real.sq_sqrt hepsilon.le
  have hsqrt_pow : Real.sqrt epsilon ^ degree =
      epsilon * Real.rpow epsilon (((degree : Real) - 2) / 2) := by
    calc
      Real.sqrt epsilon ^ degree =
          (Real.rpow epsilon (1 / 2)) ^ degree :=
        congrArg (fun x : Real ↦ x ^ degree) (Real.sqrt_eq_rpow epsilon)
      _ = (Real.rpow epsilon (1 / 2)) ^ (degree : Real) :=
        (Real.rpow_natCast _ degree).symm
      _ = Real.rpow epsilon ((1 / 2) * (degree : Real)) :=
        (Real.rpow_mul hepsilon.le _ _).symm
      _ = Real.rpow epsilon
          (1 + (((degree : Real) - 2) / 2)) := by
        congr 1
        ring
      _ = Real.rpow epsilon 1 *
          Real.rpow epsilon (((degree : Real) - 2) / 2) :=
        Real.rpow_add hepsilon _ _
      _ = epsilon * Real.rpow epsilon
          (((degree : Real) - 2) / 2) := by
        norm_num
  unfold finiteEdgeHamiltonian
  rw [mul_add]
  apply congrArg₂ (fun x y : Real ↦ x + y)
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _hv
    change (Real.sqrt epsilon * p v) ^ 2 /
        (2 * mass.mass v) =
      epsilon * (p v ^ 2 / (2 * mass.mass v))
    rw [mul_pow, hsqrt_sq]
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro edge _hedge
    rw [edgeDifference_rescale]
    simp only [mul_pow]
    rw [hsqrt_sq, hsqrt_pow]
    unfold graphEffectiveCoupling
    ring

/-- The graph coupling is definitionally the established lattice effective
coupling. -/
theorem graphEffectiveCoupling_eq_effectiveCoupling
    (lambda epsilon : Real) (degree : Nat) :
    graphEffectiveCoupling lambda epsilon degree =
      effectiveCoupling lambda epsilon degree := by
  rfl

/-- Cubic coupling after the amplitude rescaling. -/
theorem graphEffectiveCoupling_cubic (lambda epsilon : Real) :
    graphEffectiveCoupling lambda epsilon 3 =
      lambda * Real.sqrt epsilon := by
  unfold graphEffectiveCoupling
  norm_num [Real.sqrt_eq_rpow]

/-- The cubic inverse-square scale is exactly
`lambda^{-2} epsilon^{-1}`. -/
theorem graphEffectiveCoupling_cubic_inv_sq
    (lambda epsilon : Real) (hepsilon : 0 < epsilon)
    (hlambda : lambda ≠ 0) :
    (graphEffectiveCoupling lambda epsilon 3)⁻¹ ^ 2 =
      lambda⁻¹ ^ 2 * epsilon⁻¹ := by
  simpa [graphEffectiveCoupling_eq_effectiveCoupling] using
    (effectiveCoupling_inv_sq lambda epsilon 3 (by norm_num)
      hepsilon hlambda)


/-- Quartic coupling after the amplitude rescaling. -/
theorem graphEffectiveCoupling_quartic (lambda epsilon : Real) :
    graphEffectiveCoupling lambda epsilon 4 = lambda * epsilon := by
  unfold graphEffectiveCoupling
  norm_num

/-- The quartic inverse-square scale is exactly
`lambda^{-2} epsilon^{-2}`. -/
theorem graphEffectiveCoupling_quartic_inv_sq
    (lambda epsilon : Real) :
    (graphEffectiveCoupling lambda epsilon 4)⁻¹ ^ 2 =
      lambda⁻¹ ^ 2 * epsilon⁻¹ ^ 2 := by
  rw [graphEffectiveCoupling_quartic, mul_inv_rev, mul_pow]
  ring
/-! ## Uniform finite grids -/

/-- Sites of the `dimension`-dimensional open box with uniform side length
`side`. -/
abbrev OpenGridSite (dimension side : Nat) := Fin dimension → Fin side

/-- Sites of the `dimension`-dimensional periodic torus with uniform side
length `side`. -/
abbrev PeriodicGridSite (dimension side : Nat) := Fin dimension → Fin side

/-- Positive-coordinate nearest-neighbour adjacency in an open box. -/
def OpenGridForwardAdjacent {dimension side : Nat}
    (x y : OpenGridSite dimension side) : Prop :=
  ∃ axis : Fin dimension,
    (y axis).val = (x axis).val + 1 ∧
      ∀ other, other ≠ axis → y other = x other

/-- Positive-coordinate nearest-neighbour adjacency on a periodic torus. -/
def PeriodicGridForwardAdjacent {dimension side : Nat}
    (x y : PeriodicGridSite dimension side) : Prop :=
  ∃ axis : Fin dimension,
    (y axis).val = ((x axis).val + 1) % side ∧
      ∀ other, other ≠ axis → y other = x other

/-- The canonical positive-coordinate orientation of open-grid bonds. -/
def openGridDirectedEdges (dimension side : Nat) :
    FiniteDirectedEdges (OpenGridSite dimension side) := by
  classical
  exact Finset.univ.filter fun edge ↦
    OpenGridForwardAdjacent edge.1 edge.2

/-- The canonical positive-coordinate orientation of periodic-grid bonds. -/
def periodicGridDirectedEdges (dimension side : Nat)
    (_hside : 3 ≤ side) :
    FiniteDirectedEdges (PeriodicGridSite dimension side) := by
  classical
  exact Finset.univ.filter fun edge ↦
    PeriodicGridForwardAdjacent edge.1 edge.2

/-- Two-dimensional open-grid sites. -/
abbrev OpenGrid2Site (side : Nat) := OpenGridSite 2 side

/-- Three-dimensional open-grid sites. -/
abbrev OpenGrid3Site (side : Nat) := OpenGridSite 3 side

/-- Two-dimensional periodic-grid sites. -/
abbrev PeriodicGrid2Site (side : Nat) := PeriodicGridSite 2 side

/-- Three-dimensional periodic-grid sites. -/
abbrev PeriodicGrid3Site (side : Nat) := PeriodicGridSite 3 side

/-- Two-dimensional open-grid directed bonds. -/
def openGrid2DirectedEdges (side : Nat) :
    FiniteDirectedEdges (OpenGrid2Site side) :=
  openGridDirectedEdges 2 side

/-- Three-dimensional open-grid directed bonds. -/
def openGrid3DirectedEdges (side : Nat) :
    FiniteDirectedEdges (OpenGrid3Site side) :=
  openGridDirectedEdges 3 side

/-- Two-dimensional periodic-grid directed bonds. -/
def periodicGrid2DirectedEdges (side : Nat) (hside : 3 ≤ side) :
    FiniteDirectedEdges (PeriodicGrid2Site side) :=
  periodicGridDirectedEdges 2 side hside

/-- Three-dimensional periodic-grid directed bonds. -/
def periodicGrid3DirectedEdges (side : Nat) (hside : 3 ≤ side) :
    FiniteDirectedEdges (PeriodicGrid3Site side) :=
  periodicGridDirectedEdges 3 side hside

/-! The following four theorems are explicit 2D/3D open/periodic endpoints;
their proofs are direct specializations of the finite-edge theorem. -/

theorem openGrid2Hamiltonian_rescale (side : Nat)
    (mass : PositiveMassProfile (OpenGrid2Site side))
    (degree : Nat) (hdegree : 3 ≤ degree)
    (lambda epsilon : Real) (hepsilon : 0 < epsilon)
    (p q : OpenGrid2Site side → Real) :
    finiteEdgeHamiltonian (openGrid2DirectedEdges side) mass degree lambda
        (rescaleField epsilon p) (rescaleField epsilon q) =
      epsilon * finiteEdgeHamiltonian (openGrid2DirectedEdges side) mass
        degree (graphEffectiveCoupling lambda epsilon degree) p q := by
  exact finiteEdgeHamiltonian_rescale _ _ degree hdegree lambda epsilon
    hepsilon p q

theorem openGrid3Hamiltonian_rescale (side : Nat)
    (mass : PositiveMassProfile (OpenGrid3Site side))
    (degree : Nat) (hdegree : 3 ≤ degree)
    (lambda epsilon : Real) (hepsilon : 0 < epsilon)
    (p q : OpenGrid3Site side → Real) :
    finiteEdgeHamiltonian (openGrid3DirectedEdges side) mass degree lambda
        (rescaleField epsilon p) (rescaleField epsilon q) =
      epsilon * finiteEdgeHamiltonian (openGrid3DirectedEdges side) mass
        degree (graphEffectiveCoupling lambda epsilon degree) p q := by
  exact finiteEdgeHamiltonian_rescale _ _ degree hdegree lambda epsilon
    hepsilon p q

theorem periodicGrid2Hamiltonian_rescale (side : Nat)
    (hside : 3 ≤ side)
    (mass : PositiveMassProfile (PeriodicGrid2Site side))
    (degree : Nat) (hdegree : 3 ≤ degree)
    (lambda epsilon : Real) (hepsilon : 0 < epsilon)
    (p q : PeriodicGrid2Site side → Real) :
    finiteEdgeHamiltonian (periodicGrid2DirectedEdges side hside) mass degree lambda
        (rescaleField epsilon p) (rescaleField epsilon q) =
      epsilon * finiteEdgeHamiltonian (periodicGrid2DirectedEdges side hside) mass
        degree (graphEffectiveCoupling lambda epsilon degree) p q := by
  exact finiteEdgeHamiltonian_rescale _ _ degree hdegree lambda epsilon
    hepsilon p q

theorem periodicGrid3Hamiltonian_rescale (side : Nat)
    (hside : 3 ≤ side)
    (mass : PositiveMassProfile (PeriodicGrid3Site side))
    (degree : Nat) (hdegree : 3 ≤ degree)
    (lambda epsilon : Real) (hepsilon : 0 < epsilon)
    (p q : PeriodicGrid3Site side → Real) :
    finiteEdgeHamiltonian (periodicGrid3DirectedEdges side hside) mass degree lambda
        (rescaleField epsilon p) (rescaleField epsilon q) =
      epsilon * finiteEdgeHamiltonian (periodicGrid3DirectedEdges side hside) mass
        degree (graphEffectiveCoupling lambda epsilon degree) p q := by
  exact finiteEdgeHamiltonian_rescale _ _ degree hdegree lambda epsilon
    hepsilon p q

end

end ArchonPhysics.FiniteGridHamiltonianScaling
