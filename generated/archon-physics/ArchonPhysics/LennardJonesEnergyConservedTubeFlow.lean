import ArchonPhysics.LennardJonesHamiltonianDuhamel
import ArchonPhysics.LennardJonesThermodynamicThreshold

/-!
# Energy-conserved invariant tubes for exact Lennard--Jones trajectories

This module closes the finite-volume collision/tube condition needed by the
exact Lennard--Jones modal Duhamel formula.  On the open set of configurations
with positive physical bond lengths, the autonomous Physlib Hamilton
equations and the verified LJ gradient formula imply, by the chain rule, that
the exact Hamiltonian has derivative zero.  A clopen continuation argument
then combines this local conservation law with the one-bond energy barrier:
an initially tubular trajectory whose initial *total* energy lies below the
barrier remains in the tube for every real time.

The threshold is a total-energy threshold, equivalently an energy-density
threshold of order `1 / N`; it is not uniform at positive energy density in
the thermodynamic limit.  The theorem constructs neither a trajectory nor a
kinetic limit, and it uses no random-phase or thermalization hypothesis.
-/

namespace ArchonPhysics.LennardJonesEnergyConservedTubeFlow

open Set
open Time
open InnerProductSpace
open ArchonPhysics
open ArchonPhysics.BondPotentialHamiltonianPhyslib
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ConcreteHamiltonGradients
open ArchonPhysics.LennardJonesHamiltonianDuhamel
open ArchonPhysics.LennardJonesPotential
open ArchonPhysics.LennardJonesThermodynamicThreshold
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.PhaseRenormalization

noncomputable section

/-- One physical bond displacement along the canonically real-reparametrized
Physlib trajectory. -/
def realBondDisplacement {N : Nat} [NeZero N]
    (q : Time → HilbertConfiguration N) (i : Lattice.Site N) :
    Real → Real :=
  fun tau => Lattice.forwardDifference
    (asConfiguration (realReparametrize q tau)) i

/-- One actual physical bond length `r₀ + Δqᵢ` along the trajectory. -/
def realBondLength {N : Nat} [NeZero N]
    (r₀ : Real) (q : Time → HilbertConfiguration N)
    (i : Lattice.Site N) : Real → Real :=
  fun tau => r₀ + realBondDisplacement q i tau

/-- Exact LJ Hamiltonian along the canonically real-reparametrized Physlib
trajectory. -/
def realLennardJonesEnergy {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (p q : Time → HilbertConfiguration N) : Real → Real :=
  fun tau => periodicRandomMassHamiltonian m depth r₀
    (asConfiguration (realReparametrize p tau))
    (asConfiguration (realReparametrize q tau))

/-- Times at which every physical bond length is positive. -/
def admissibleTimeSet {N : Nat} [NeZero N]
    (r₀ : Real) (q : Time → HilbertConfiguration N) : Set Real :=
  {tau | AdmissibleConfiguration r₀
    (asConfiguration (realReparametrize q tau))}

/-- Times at which every displacement lies in the open relative tube. -/
def relativeTubeTimeSet {N : Nat} [NeZero N]
    (r₀ rho : Real) (q : Time → HilbertConfiguration N) : Set Real :=
  {tau | UniformRelativeTube r₀ rho
    (asConfiguration (realReparametrize q tau))}

/-- Closed version of the uniform relative tube. -/
def ClosedUniformRelativeTube {N : Nat}
    (r₀ rho : Real) (q : Lattice.Configuration N) : Prop :=
  ∀ i : Lattice.Site N,
    |Lattice.forwardDifference q i| ≤ rho * r₀

/-- Times at which every displacement lies in the closed relative tube. -/
def closedRelativeTubeTimeSet {N : Nat} [NeZero N]
    (r₀ rho : Real) (q : Time → HilbertConfiguration N) : Set Real :=
  {tau | ClosedUniformRelativeTube r₀ rho
    (asConfiguration (realReparametrize q tau))}

/-- A differentiable Physlib path gives a continuous real-time bond
displacement. -/
theorem continuous_realBondDisplacement
    {N : Nat} [NeZero N]
    (q : Time → HilbertConfiguration N) (hq : Differentiable Real q)
    (i : Lattice.Site N) :
    Continuous (realBondDisplacement q i) := by
  unfold realBondDisplacement
  simpa only [Function.comp_apply, bondFunctional_apply] using
    (bondFunctional i).continuous.comp'
      (continuous_realReparametrize q hq)

/-- Actual bond length is continuous along a differentiable Physlib path. -/
theorem continuous_realBondLength
    {N : Nat} [NeZero N]
    (r₀ : Real) (q : Time → HilbertConfiguration N)
    (hq : Differentiable Real q) (i : Lattice.Site N) :
    Continuous (realBondLength r₀ q i) := by
  unfold realBondLength
  exact continuous_const.add (continuous_realBondDisplacement q hq i)

/-- The positive-bond time set is open. -/
theorem isOpen_admissibleTimeSet
    {N : Nat} [NeZero N]
    (r₀ : Real) (q : Time → HilbertConfiguration N)
    (hq : Differentiable Real q) :
    IsOpen (admissibleTimeSet r₀ q) := by
  rw [show admissibleTimeSet r₀ q =
      ⋂ i : Lattice.Site N, {tau | 0 < realBondLength r₀ q i tau} by
    ext tau
    simp [admissibleTimeSet, AdmissibleConfiguration,
      BondAdmissible, Admissible, realBondLength, realBondDisplacement]]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (continuous_realBondLength r₀ q hq i)

/-- The open uniform-tube time set is open. -/
theorem isOpen_relativeTubeTimeSet
    {N : Nat} [NeZero N]
    (r₀ rho : Real) (q : Time → HilbertConfiguration N)
    (hq : Differentiable Real q) :
    IsOpen (relativeTubeTimeSet r₀ rho q) := by
  rw [show relativeTubeTimeSet r₀ rho q =
      ⋂ i : Lattice.Site N,
        {tau | |realBondDisplacement q i tau| < rho * r₀} by
    ext tau
    simp [relativeTubeTimeSet, UniformRelativeTube, InRelativeTube,
      realBondDisplacement]]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt (continuous_realBondDisplacement q hq i).abs continuous_const

/-- The closed uniform-tube time set is closed. -/
theorem isClosed_closedRelativeTubeTimeSet
    {N : Nat} [NeZero N]
    (r₀ rho : Real) (q : Time → HilbertConfiguration N)
    (hq : Differentiable Real q) :
    IsClosed (closedRelativeTubeTimeSet r₀ rho q) := by
  rw [show closedRelativeTubeTimeSet r₀ rho q =
      ⋂ i : Lattice.Site N,
        {tau | |realBondDisplacement q i tau| ≤ rho * r₀} by
    ext tau
    simp [closedRelativeTubeTimeSet, ClosedUniformRelativeTube,
      realBondDisplacement]]
  exact isClosed_iInter fun i =>
    isClosed_le (continuous_realBondDisplacement q hq i).abs continuous_const

/-- An open relative tube of radius strictly below one consists of positive
physical bonds. -/
theorem admissibleConfiguration_of_uniformRelativeTube
    {N : Nat} {r₀ rho : Real} (hr₀ : 0 < r₀) (hrho : rho < 1)
    {q : Lattice.Configuration N} (hq : UniformRelativeTube r₀ rho q) :
    AdmissibleConfiguration r₀ q := by
  intro i
  have habs := hq i
  change |Lattice.forwardDifference q i| < rho * r₀ at habs
  have hlower := neg_abs_le (Lattice.forwardDifference q i)
  have hradius : rho * r₀ < r₀ := by nlinarith
  change 0 < r₀ + Lattice.forwardDifference q i
  linarith

/-- The closed relative tube is still strictly positive when its radius is
strictly below one. -/
theorem admissibleConfiguration_of_closedUniformRelativeTube
    {N : Nat} {r₀ rho : Real} (hr₀ : 0 < r₀) (hrho : rho < 1)
    {q : Lattice.Configuration N} (hq : ClosedUniformRelativeTube r₀ rho q) :
    AdmissibleConfiguration r₀ q := by
  intro i
  have habs := hq i
  have hlower := neg_abs_le (Lattice.forwardDifference q i)
  have hradius : rho * r₀ < r₀ := by nlinarith
  change 0 < r₀ + Lattice.forwardDifference q i
  linarith

/-- On the positive-bond region, the autonomous Physlib LJ Hamilton equations
force the exact Hamiltonian derivative to vanish.  Energy conservation is
derived here; it is not supplied as a certificate field. -/
theorem hasDerivAt_realLennardJonesEnergy_zero_of_admissible
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m
      (bondPotential depth r₀) p q)
    {tau : Real}
    (hadmissible : tau ∈ admissibleTimeSet r₀ q) :
    HasDerivAt (realLennardJonesEnergy m depth r₀ p q) 0 tau := by
  let t : Time := Time.toRealCLE.symm tau
  have hnonsingular : LennardJonesBondsNonsingular r₀ (q t) := by
    intro i
    exact (hadmissible i).ne
  have hAbstract :=
    (satisfiesHamiltonEquations_iff m (bondPotential depth r₀) p q).mp
      hHamilton
  have hqDeriv := hasDerivAt_comp_toRealCLE_symm q tau (hq t)
  rw [hAbstract.1 t,
    gradient_hamiltonian_momentum m (bondPotential depth r₀)] at hqDeriv
  have hpDeriv := hasDerivAt_comp_toRealCLE_symm p tau (hp t)
  rw [hAbstract.2 t,
    gradient_hamiltonian_position m (bondPotential depth r₀)
      (lennardJonesDerivative depth r₀) t (p t) (q t)
      (hasDerivAt_lennardJones_bonds depth r₀ (q t) hnonsingular)] at hpDeriv
  have hkin :=
    (hasGradientAt_kineticEnergy m (p t)).hasFDerivAt
      |>.comp_hasDerivAt tau hpDeriv
  have hpot :=
    (hasGradientAt_periodicPotentialEnergy
      (bondPotential depth r₀) (lennardJonesDerivative depth r₀) (q t)
      (hasDerivAt_lennardJones_bonds depth r₀ (q t) hnonsingular)).hasFDerivAt
      |>.comp_hasDerivAt tau hqDeriv
  have hsum := hkin.add hpot
  simpa [realLennardJonesEnergy, periodicRandomMassHamiltonian,
    Function.comp_def, InnerProductSpace.toDual_apply_apply,
    real_inner_comm] using! hsum

/-- On every convex real-time interval contained in the positive-bond region,
the exact LJ Hamiltonian agrees at any two times. -/
theorem realLennardJonesEnergy_eq_of_convex_admissible
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m
      (bondPotential depth r₀) p q)
    {s : Set Real} (hs : Convex Real s)
    (hsafe : s ⊆ admissibleTimeSet r₀ q)
    {u v : Real} (hu : u ∈ s) (hv : v ∈ s) :
    realLennardJonesEnergy m depth r₀ p q u =
      realLennardJonesEnergy m depth r₀ p q v := by
  have hzero : ∀ t ∈ s,
      HasDerivWithinAt (realLennardJonesEnergy m depth r₀ p q) 0 s t := by
    intro t ht
    exact (hasDerivAt_realLennardJonesEnergy_zero_of_admissible
      m depth r₀ p q hp hq hHamilton (hsafe ht)).hasDerivWithinAt
  have hbound := hs.norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := 0) hzero (fun _ _ => by simp) hu hv
  have hrev : realLennardJonesEnergy m depth r₀ p q v =
      realLennardJonesEnergy m depth r₀ p q u := by
    simpa only [norm_zero, zero_mul, norm_le_zero_iff, sub_eq_zero]
      using hbound
  exact hrev.symm

end

/-- On the positive-bond region, every inverse image of an arbitrary energy
set is relatively open.  This is the local-constancy form of autonomous
Hamiltonian conservation used by the continuation argument below. -/
theorem isOpen_admissibleTimeSet_inter_energy_preimage
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m
      (bondPotential depth r₀) p q)
    (target : Set Real) :
    IsOpen (admissibleTimeSet r₀ q ∩
      realLennardJonesEnergy m depth r₀ p q ⁻¹' target) := by
  apply (isOpen_admissibleTimeSet r₀ q hq).isOpen_inter_preimage_of_deriv_eq_zero
  · intro tau htau
    exact (hasDerivAt_realLennardJonesEnergy_zero_of_admissible
      m depth r₀ p q hp hq hHamilton htau).differentiableAt
        |>.differentiableWithinAt
  · intro tau htau
    exact (hasDerivAt_realLennardJonesEnergy_zero_of_admissible
      m depth r₀ p q hp hq hHamilton htau).deriv

/-- Every strict relative tube is contained in its closed counterpart. -/
theorem closedUniformRelativeTube_of_uniformRelativeTube
    {N : Nat} {r₀ rho : Real} {q : Lattice.Configuration N}
    (hq : UniformRelativeTube r₀ rho q) :
    ClosedUniformRelativeTube r₀ rho q := by
  intro i
  exact (hq i).le

/-- Time-set form of strict-tube containment in the closed tube. -/
theorem relativeTubeTimeSet_subset_closedRelativeTubeTimeSet
    {N : Nat} [NeZero N] (r₀ rho : Real)
    (q : Time → HilbertConfiguration N) :
    relativeTubeTimeSet r₀ rho q ⊆ closedRelativeTubeTimeSet r₀ rho q := by
  intro tau htau
  exact closedUniformRelativeTube_of_uniformRelativeTube htau

/-- A relative tube of radius below one lies in the positive-bond time set. -/
theorem relativeTubeTimeSet_subset_admissibleTimeSet
    {N : Nat} [NeZero N] {r₀ rho : Real}
    (hr₀ : 0 < r₀) (hrho : rho < 1)
    (q : Time → HilbertConfiguration N) :
    relativeTubeTimeSet r₀ rho q ⊆ admissibleTimeSet r₀ q := by
  intro tau htau
  exact admissibleConfiguration_of_uniformRelativeTube hr₀ hrho htau

/-- Times that are simultaneously in the strict tube and on the initial exact
LJ energy level. -/
def energyConservedRelativeTubeTimeSet {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ rho : Real)
    (p q : Time → HilbertConfiguration N) : Set Real :=
  relativeTubeTimeSet r₀ rho q ∩
    realLennardJonesEnergy m depth r₀ p q ⁻¹'
      {realLennardJonesEnergy m depth r₀ p q 0}

/-- The strict-tube/initial-energy time set is open. -/
theorem isOpen_energyConservedRelativeTubeTimeSet
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ rho : Real)
    (p q : Time → HilbertConfiguration N)
    (hr₀ : 0 < r₀) (hrho : rho < 1)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m
      (bondPotential depth r₀) p q) :
    IsOpen (energyConservedRelativeTubeTimeSet m depth r₀ rho p q) := by
  rw [show energyConservedRelativeTubeTimeSet m depth r₀ rho p q =
      relativeTubeTimeSet r₀ rho q ∩
        (admissibleTimeSet r₀ q ∩
          realLennardJonesEnergy m depth r₀ p q ⁻¹'
            {realLennardJonesEnergy m depth r₀ p q 0}) by
    ext tau
    constructor
    · intro htau
      exact ⟨htau.1,
        relativeTubeTimeSet_subset_admissibleTimeSet hr₀ hrho q htau.1,
        htau.2⟩
    · intro htau
      exact ⟨htau.1, htau.2.2⟩]
  exact (isOpen_relativeTubeTimeSet r₀ rho q hq).inter
    (isOpen_admissibleTimeSet_inter_energy_preimage
      m depth r₀ p q hp hq hHamilton
        {realLennardJonesEnergy m depth r₀ p q 0})

/-- Below the one-bond total-energy barrier, the strict-tube/initial-energy
time set is also closed.  The proof uses the closed tube only as a boundary
set; closed-tube membership and `rho < 1` imply positive physical bonds, so
the static LJ barrier theorem applies there. -/
theorem isClosed_energyConservedRelativeTubeTimeSet_of_energy_lt_barrier
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ rho : Real)
    (p q : Time → HilbertConfiguration N)
    (hdepth : 0 ≤ depth) (hr₀ : 0 < r₀)
    (hrho : 0 ≤ rho) (hrhoOne : rho < 1)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m
      (bondPotential depth r₀) p q)
    (hinitialEnergy : realLennardJonesEnergy m depth r₀ p q 0 <
      relativeTubeBarrier depth rho) :
    IsClosed (energyConservedRelativeTubeTimeSet m depth r₀ rho p q) := by
  rw [← isOpen_compl_iff]
  rw [show (energyConservedRelativeTubeTimeSet m depth r₀ rho p q)ᶜ =
      (closedRelativeTubeTimeSet r₀ rho q)ᶜ ∪
        (admissibleTimeSet r₀ q ∩
          realLennardJonesEnergy m depth r₀ p q ⁻¹'
            ({realLennardJonesEnergy m depth r₀ p q 0} : Set Real)ᶜ) by
    ext tau
    constructor
    · intro hbad
      by_cases hclosed : tau ∈ closedRelativeTubeTimeSet r₀ rho q
      · have hsafe : tau ∈ admissibleTimeSet r₀ q :=
          admissibleConfiguration_of_closedUniformRelativeTube
            hr₀ hrhoOne hclosed
        by_cases henergy :
            realLennardJonesEnergy m depth r₀ p q tau =
              realLennardJonesEnergy m depth r₀ p q 0
        · exfalso
          apply hbad
          refine ⟨?_, ?_⟩
          · apply uniformRelativeTube_of_hamiltonian_lt_relativeTubeBarrier
              m hdepth hr₀ hrho
              (asConfiguration (realReparametrize p tau))
              (asConfiguration (realReparametrize q tau)) hsafe
            simpa [realLennardJonesEnergy] using
              henergy.trans_lt hinitialEnergy
          · exact henergy
        · right
          exact ⟨hsafe, by
            simp only [mem_preimage, mem_compl_iff, mem_singleton_iff]
            exact henergy⟩
      · exact Or.inl hclosed
    · intro hbad hgood
      rcases hbad with hnotclosed | henergyNe
      · exact hnotclosed
          (relativeTubeTimeSet_subset_closedRelativeTubeTimeSet
            r₀ rho q hgood.1)
      · exact henergyNe.2 hgood.2]
  exact (isClosed_closedRelativeTubeTimeSet r₀ rho q hq).isOpen_compl.union
    (isOpen_admissibleTimeSet_inter_energy_preimage
      m depth r₀ p q hp hq hHamilton
        ({realLennardJonesEnergy m depth r₀ p q 0} : Set Real)ᶜ)

/-- A differentiable exact LJ Hamilton trajectory that starts in the relative
tube and below its one-bond total-energy barrier stays in that tube at every
real-reparametrized time.  No separate conservation or collision-avoidance
certificate is assumed. -/
theorem uniformRelativeTube_all_real_of_initial_energy_lt_barrier
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ rho : Real)
    (p q : Time → HilbertConfiguration N)
    (hdepth : 0 ≤ depth) (hr₀ : 0 < r₀)
    (hrho : 0 ≤ rho) (hrhoOne : rho < 1)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m
      (bondPotential depth r₀) p q)
    (hinitialTube : UniformRelativeTube r₀ rho
      (asConfiguration (realReparametrize q 0)))
    (hinitialEnergy : realLennardJonesEnergy m depth r₀ p q 0 <
      relativeTubeBarrier depth rho) :
    ∀ tau : Real, UniformRelativeTube r₀ rho
      (asConfiguration (realReparametrize q tau)) := by
  have hopen := isOpen_energyConservedRelativeTubeTimeSet
    m depth r₀ rho p q hr₀ hrhoOne hp hq hHamilton
  have hclosed :=
    isClosed_energyConservedRelativeTubeTimeSet_of_energy_lt_barrier
      m depth r₀ rho p q hdepth hr₀ hrho hrhoOne hp hq hHamilton
        hinitialEnergy
  have hzero : 0 ∈ energyConservedRelativeTubeTimeSet
      m depth r₀ rho p q := by
    exact ⟨hinitialTube, by simp⟩
  have huniv : energyConservedRelativeTubeTimeSet
      m depth r₀ rho p q = Set.univ :=
    (show IsClopen (energyConservedRelativeTubeTimeSet
      m depth r₀ rho p q) from ⟨hclosed, hopen⟩).eq_univ ⟨0, hzero⟩
  intro tau
  have htau : tau ∈ energyConservedRelativeTubeTimeSet
      m depth r₀ rho p q := by
    rw [huniv]
    exact mem_univ tau
  exact htau.1

/-- Exact LJ energy conservation is a consequence of the autonomous
Hamilton equations and the invariant tube, not an input certificate. -/
theorem realLennardJonesEnergy_conserved_of_initial_energy_lt_barrier
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ rho : Real)
    (p q : Time → HilbertConfiguration N)
    (hdepth : 0 ≤ depth) (hr₀ : 0 < r₀)
    (hrho : 0 ≤ rho) (hrhoOne : rho < 1)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m
      (bondPotential depth r₀) p q)
    (hinitialTube : UniformRelativeTube r₀ rho
      (asConfiguration (realReparametrize q 0)))
    (hinitialEnergy : realLennardJonesEnergy m depth r₀ p q 0 <
      relativeTubeBarrier depth rho)
    (tau : Real) :
    realLennardJonesEnergy m depth r₀ p q tau =
      realLennardJonesEnergy m depth r₀ p q 0 := by
  apply realLennardJonesEnergy_eq_of_convex_admissible
    m depth r₀ p q hp hq hHamilton convex_univ
    (fun s _ => admissibleConfiguration_of_uniformRelativeTube hr₀ hrhoOne
      (uniformRelativeTube_all_real_of_initial_energy_lt_barrier
        m depth r₀ rho p q hdepth hr₀ hrho hrhoOne hp hq hHamilton
          hinitialTube hinitialEnergy s))
    (mem_univ tau) (mem_univ 0)

/-- Physlib-time form of the invariant-tube theorem. -/
theorem uniformRelativeTube_all_time_of_initial_energy_lt_barrier
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ rho : Real)
    (p q : Time → HilbertConfiguration N)
    (hdepth : 0 ≤ depth) (hr₀ : 0 < r₀)
    (hrho : 0 ≤ rho) (hrhoOne : rho < 1)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m
      (bondPotential depth r₀) p q)
    (hinitialTube : UniformRelativeTube r₀ rho
      (asConfiguration (q 0)))
    (hinitialEnergy : periodicRandomMassHamiltonian m depth r₀
      (asConfiguration (p 0)) (asConfiguration (q 0)) <
        relativeTubeBarrier depth rho) :
    ∀ t : Time, UniformRelativeTube r₀ rho (asConfiguration (q t)) := by
  have hreal := uniformRelativeTube_all_real_of_initial_energy_lt_barrier
    m depth r₀ rho p q hdepth hr₀ hrho hrhoOne hp hq hHamilton
    (by simpa [realReparametrize] using hinitialTube)
    (by simpa [realLennardJonesEnergy, realReparametrize] using hinitialEnergy)
  intro t
  simpa [realReparametrize] using hreal (Time.toRealCLE t)

/-- The invariant tube gives strict positivity of every physical bond at every
Physlib time. -/
theorem admissibleConfiguration_all_time_of_initial_energy_lt_barrier
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ rho : Real)
    (p q : Time → HilbertConfiguration N)
    (hdepth : 0 ≤ depth) (hr₀ : 0 < r₀)
    (hrho : 0 ≤ rho) (hrhoOne : rho < 1)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m
      (bondPotential depth r₀) p q)
    (hinitialTube : UniformRelativeTube r₀ rho (asConfiguration (q 0)))
    (hinitialEnergy : periodicRandomMassHamiltonian m depth r₀
      (asConfiguration (p 0)) (asConfiguration (q 0)) <
        relativeTubeBarrier depth rho) :
    ∀ t : Time, AdmissibleConfiguration r₀ (asConfiguration (q t)) := by
  intro t
  exact admissibleConfiguration_of_uniformRelativeTube hr₀ hrhoOne
    (uniformRelativeTube_all_time_of_initial_energy_lt_barrier
      m depth r₀ rho p q hdepth hr₀ hrho hrhoOne hp hq hHamilton
        hinitialTube hinitialEnergy t)


/-- The invariant tube automatically supplies the all-time nonzero-bond
hypothesis required by the exact LJ gradient and Duhamel theorems. -/
theorem lennardJonesBondsNonsingular_all_time_of_initial_energy_lt_barrier
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ rho : Real)
    (p q : Time → HilbertConfiguration N)
    (hdepth : 0 ≤ depth) (hr₀ : 0 < r₀)
    (hrho : 0 ≤ rho) (hrhoOne : rho < 1)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m
      (bondPotential depth r₀) p q)
    (hinitialTube : UniformRelativeTube r₀ rho (asConfiguration (q 0)))
    (hinitialEnergy : periodicRandomMassHamiltonian m depth r₀
      (asConfiguration (p 0)) (asConfiguration (q 0)) <
        relativeTubeBarrier depth rho) :
    ∀ t : Time, LennardJonesBondsNonsingular r₀ (q t) := by
  have htube := uniformRelativeTube_all_time_of_initial_energy_lt_barrier
    m depth r₀ rho p q hdepth hr₀ hrho hrhoOne hp hq hHamilton
      hinitialTube hinitialEnergy
  intro t
  have hadmissible := admissibleConfiguration_of_uniformRelativeTube
    hr₀ hrhoOne (htube t)
  intro i
  exact (hadmissible i).ne

/-- Physlib-time exact LJ Hamiltonian conservation derived from the equations
and low-energy invariant tube. -/
theorem periodicRandomMassHamiltonian_conserved_of_initial_energy_lt_barrier
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ rho : Real)
    (p q : Time → HilbertConfiguration N)
    (hdepth : 0 ≤ depth) (hr₀ : 0 < r₀)
    (hrho : 0 ≤ rho) (hrhoOne : rho < 1)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m
      (bondPotential depth r₀) p q)
    (hinitialTube : UniformRelativeTube r₀ rho (asConfiguration (q 0)))
    (hinitialEnergy : periodicRandomMassHamiltonian m depth r₀
      (asConfiguration (p 0)) (asConfiguration (q 0)) <
        relativeTubeBarrier depth rho)
    (t : Time) :
    periodicRandomMassHamiltonian m depth r₀
        (asConfiguration (p t)) (asConfiguration (q t)) =
      periodicRandomMassHamiltonian m depth r₀
        (asConfiguration (p 0)) (asConfiguration (q 0)) := by
  have hconserved :=
    realLennardJonesEnergy_conserved_of_initial_energy_lt_barrier
      m depth r₀ rho p q hdepth hr₀ hrho hrhoOne hp hq hHamilton
      (by simpa [realReparametrize] using hinitialTube)
      (by simpa [realLennardJonesEnergy, realReparametrize] using hinitialEnergy)
      (Time.toRealCLE t)
  simpa [realLennardJonesEnergy, realReparametrize] using hconserved

/-- Exact finite-time LJ modal Duhamel identity with nonsingularity and source
integrability discharged by the low-total-energy invariant tube.  Positivity
of the selected nonzero mode frequency remains the necessary oscillator
condition. -/
theorem interactionPicture_physlibMode_eq_initial_add_integral_of_energyTube
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ rho : Real)
    (k : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hdepth : 0 ≤ depth) (hr₀ : 0 < r₀)
    (hrho : 0 ≤ rho) (hrhoOne : rho < 1)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m
      (bondPotential depth r₀) p q)
    (hinitialTube : UniformRelativeTube r₀ rho (asConfiguration (q 0)))
    (hinitialEnergy : periodicRandomMassHamiltonian m depth r₀
      (asConfiguration (p 0)) (asConfiguration (q 0)) <
        relativeTubeBarrier depth rho)
    (homega : 0 < lennardJonesModeFrequency m depth r₀ k) (t : Real) :
    phaseRenormalize (lennardJonesModeFrequency m depth r₀ k * t)
        (physlibModeAmplitude m depth r₀ k p q t) =
      physlibModeAmplitude m depth r₀ k p q 0 +
        ∫ s in 0..t, physlibModeRotatedSource m depth r₀ k q s := by
  apply interactionPicture_physlibMode_eq_initial_add_integral_of_nonsingular
    m depth r₀ k p q hp hq hHamilton
    (lennardJonesBondsNonsingular_all_time_of_initial_energy_lt_barrier
      m depth r₀ rho p q hdepth hr₀ hrho hrhoOne hp hq hHamilton
        hinitialTube hinitialEnergy)
  · rw [harmonicStiffness_eq]
    positivity
  · exact homega

end ArchonPhysics.LennardJonesEnergyConservedTubeFlow
