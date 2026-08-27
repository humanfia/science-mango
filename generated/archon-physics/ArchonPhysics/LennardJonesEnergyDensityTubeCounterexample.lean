import ArchonPhysics.LennardJonesThermodynamicThreshold

/-!
# A thermodynamic energy-density counterexample to uniform LJ strain control

For a periodic chain of volume `n + 2`, put a displacement `-b` on every bond
except the bond crossing the periodic cut.  Telescoping forces the latter bond
to have displacement `(n + 1) b`.  Its Lennard--Jones energy is only `O(1)`,
so its contribution to the energy per site vanishes, although its strain
leaves every fixed relative tube.

This is a static counterexample.  It says that a positive mean energy-density
bound alone cannot provide a thermodynamic, all-bond Taylor tube; it makes no
claim about the time evolution or thermalization of the chain.
-/

namespace ArchonPhysics.LennardJonesEnergyDensityTubeCounterexample

open Filter
open scoped Topology
open LennardJonesPotential
open LennardJonesThermodynamicThreshold

noncomputable section

/-- A periodic configuration with one tensile defect.  Along the standard
representatives `0, ..., n + 1`, the configuration has slope `-b`. -/
def singleTensileDefectConfiguration (n : Nat) (b : Real) :
    Lattice.Configuration (n + 2) :=
  fun i => -(i.val : Real) * b

/-- Every non-cut bond has displacement `-b`, while the periodic cut has
displacement `(n + 1)b`. -/
theorem forwardDifference_singleTensileDefectConfiguration
    (n : Nat) (b : Real) (i : Lattice.Site (n + 2)) :
    Lattice.forwardDifference (singleTensileDefectConfiguration n b) i =
      if i.val + 1 < n + 2 then -b else (n + 1 : Nat) * b := by
  have hvolume : 1 < n + 2 := by omega
  have hone : (1 : ZMod (n + 2)).val = 1 := by
    simpa using
      (ZMod.val_natCast_of_lt (n := n + 2) (a := 1) hvolume)
  rw [Lattice.forwardDifference_apply]
  unfold singleTensileDefectConfiguration
  rw [ZMod.val_add, hone]
  have hival_lt : i.val < n + 2 := i.val_lt
  by_cases hnext : i.val + 1 < n + 2
  · rw [if_pos hnext, Nat.mod_eq_of_lt hnext]
    push_cast
    ring
  · rw [if_neg hnext]
    have hwrap : i.val + 1 = n + 2 := by omega
    have hilast : i.val = n + 1 := by omega
    rw [hwrap, Nat.mod_self]
    rw [hilast]
    push_cast
    ring

/-- `ZMod.finEquiv` preserves the canonical representative in every nonempty
volume. -/
theorem finEquiv_val {N : Nat} [NeZero N] (i : Fin N) :
    ((ZMod.finEquiv N).toEquiv i).val = i.val := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ N => rfl

/-- The exact potential energy is the energy of `n + 1` identical compressed
bonds plus that of the single tensile bond at the periodic cut. -/
theorem periodicPotentialEnergy_singleTensileDefectConfiguration
    (n : Nat) (depth r₀ b : Real) :
    periodicPotentialEnergy depth r₀
        (singleTensileDefectConfiguration n b) =
      (n + 1 : Nat) * bondPotential depth r₀ (-b) +
        bondPotential depth r₀ ((n + 1 : Nat) * b) := by
  unfold periodicPotentialEnergy
  rw [← (ZMod.finEquiv (n + 2)).sum_comp]
  rw [Fin.sum_univ_castSucc]
  have hprefix : ∀ i : Fin (n + 1),
      Lattice.forwardDifference
          (singleTensileDefectConfiguration n b)
          ((ZMod.finEquiv (n + 2)).toEquiv i.castSucc) = -b := by
    intro i
    rw [forwardDifference_singleTensileDefectConfiguration]
    rw [if_pos]
    rw [finEquiv_val]
    simp only [Fin.val_castSucc]
    omega
  have hlast :
      Lattice.forwardDifference
          (singleTensileDefectConfiguration n b)
          ((ZMod.finEquiv (n + 2)).toEquiv (Fin.last (n + 1))) =
        (n + 1 : Nat) * b := by
    rw [forwardDifference_singleTensileDefectConfiguration]
    rw [if_neg]
    rw [finEquiv_val]
    simp
  simp_rw [hprefix]
  rw [hlast]
  simp

/-- The periodic-cut bond is the unique tensile defect. -/
theorem forwardDifference_at_periodicCut (n : Nat) (b : Real) :
    Lattice.forwardDifference (singleTensileDefectConfiguration n b)
        ((ZMod.finEquiv (n + 2)).toEquiv (Fin.last (n + 1))) =
      (n + 1 : Nat) * b := by
  rw [forwardDifference_singleTensileDefectConfiguration, if_neg]
  · rw [finEquiv_val]
    simp

/-- If `0 < b < r₀`, every physical bond length in the defect
configuration is positive. -/
theorem singleTensileDefectConfiguration_admissible
    {r₀ b : Real} (hb : 0 < b) (hbr₀ : b < r₀)
    (n : Nat) :
    AdmissibleConfiguration r₀
      (singleTensileDefectConfiguration n b) := by
  intro i
  rw [BondAdmissible, Admissible]
  rw [forwardDifference_singleTensileDefectConfiguration]
  split_ifs
  · linarith
  · have hn : 0 ≤ ((n + 1 : Nat) : Real) := by positivity
    nlinarith

/-- Once the tensile defect reaches the tube boundary, the all-bond tube
condition fails. -/
theorem not_uniformRelativeTube_of_cut_large
    {r₀ ρ b : Real} (n : Nat)
    (hb : 0 ≤ b) (hlarge : ρ * r₀ ≤ (n + 1 : Nat) * b) :
    ¬ UniformRelativeTube r₀ ρ
      (singleTensileDefectConfiguration n b) := by
  intro htube
  have hcut := htube
    ((ZMod.finEquiv (n + 2)).toEquiv (Fin.last (n + 1)))
  rw [InRelativeTube, forwardDifference_at_periodicCut,
    abs_of_nonneg (mul_nonneg (by positivity) hb)] at hcut
  exact (not_lt_of_ge hlarge) hcut

/-- The energy of the increasingly stretched cut bond tends to the LJ
dissociation energy `depth`. -/
theorem tendsto_cutBondPotential
    {depth r₀ b : Real} (hb : 0 < b) :
    Tendsto
      (fun n : Nat => bondPotential depth r₀ ((n + 1 : Nat) * b))
      atTop (𝓝 depth) := by
  have hindexNat : Tendsto (fun n : Nat => n + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hindexReal :
      Tendsto (fun n : Nat => ((n + 1 : Nat) : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hindexNat
  have hx : Tendsto (fun n : Nat => ((n + 1 : Nat) : Real) * b)
      atTop atTop := hindexReal.atTop_mul_const hb
  have hden : Tendsto
      (fun n : Nat => r₀ + ((n + 1 : Nat) : Real) * b)
      atTop atTop := tendsto_const_nhds.add_atTop hx
  have hratio : Tendsto
      (fun n : Nat => r₀ / (r₀ + ((n + 1 : Nat) : Real) * b))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hden
  have hone : Tendsto (fun _ : Nat => (1 : Real)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hfactor : Tendsto
      (fun n : Nat => depth *
        ((r₀ / (r₀ + ((n + 1 : Nat) : Real) * b)) ^ 6 - 1) ^ 2)
      atTop (𝓝 (depth * ((0 : Real) ^ 6 - 1) ^ 2)) :=
    tendsto_const_nhds.mul (((hratio.pow 6).sub hone).pow 2)
  simpa [bondPotential, shiftedPotential_factor] using hfactor

/-- Potential energy per periodic site for the explicit one-defect family. -/
def defectPotentialEnergyDensity
    (n : Nat) (depth r₀ b : Real) : Real :=
  periodicPotentialEnergy depth r₀
      (singleTensileDefectConfiguration n b) / (n + 2 : Nat)

/-- Exact two-term formula for the defect potential-energy density. -/
theorem defectPotentialEnergyDensity_eq
    (n : Nat) (depth r₀ b : Real) :
    defectPotentialEnergyDensity n depth r₀ b =
      ((n + 1 : Nat) * bondPotential depth r₀ (-b) +
        bondPotential depth r₀ ((n + 1 : Nat) * b)) /
          (n + 2 : Nat) := by
  rw [defectPotentialEnergyDensity,
    periodicPotentialEnergy_singleTensileDefectConfiguration]

/-- In the thermodynamic limit, the unique tensile defect has zero density;
the limit is the energy of one of the repeated compressed bonds. -/
theorem tendsto_defectPotentialEnergyDensity
    {depth r₀ b : Real} (hb : 0 < b) :
    Tendsto (fun n : Nat => defectPotentialEnergyDensity n depth r₀ b)
      atTop (𝓝 (bondPotential depth r₀ (-b))) := by
  have hvolume : Tendsto (fun n : Nat => ((n + 2 : Nat) : Real))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hinv : Tendsto (fun n : Nat => (1 : Real) / (n + 2 : Nat))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop hvolume :
      Tendsto (fun n : Nat => (1 : Real) / ((n + 2 : Nat) : Real))
        atTop (𝓝 0))
  have hcoefficient : Tendsto
      (fun n : Nat => ((n + 1 : Nat) : Real) / (n + 2 : Nat))
      atTop (𝓝 1) := by
    convert (tendsto_const_nhds.sub hinv :
      Tendsto (fun n : Nat => (1 : Real) - 1 / (n + 2 : Nat))
        atTop (𝓝 (1 - 0))) using 1
    · funext n
      have hne : ((n + 2 : Nat) : Real) ≠ 0 := by positivity
      push_cast
      field_simp [hne]
      ring
    · norm_num
  have hcompressed : Tendsto
      (fun n : Nat =>
        (((n + 1 : Nat) : Real) / (n + 2 : Nat)) *
          bondPotential depth r₀ (-b))
      atTop (𝓝 (bondPotential depth r₀ (-b))) := by
    simpa using hcoefficient.mul tendsto_const_nhds
  have htensile : Tendsto
      (fun n : Nat =>
        bondPotential depth r₀ ((n + 1 : Nat) * b) / (n + 2 : Nat))
      atTop (𝓝 0) := by
    simpa using (tendsto_cutBondPotential hb).div_atTop hvolume
  have htarget : Tendsto
      (fun n : Nat =>
        (((n + 1 : Nat) : Real) / (n + 2 : Nat)) *
            bondPotential depth r₀ (-b) +
          bondPotential depth r₀ ((n + 1 : Nat) * b) / (n + 2 : Nat))
      atTop (𝓝 (bondPotential depth r₀ (-b))) := by
    simpa only [add_zero] using hcompressed.add htensile
  apply htarget.congr'
  filter_upwards with n
  rw [defectPotentialEnergyDensity_eq]
  have hne : ((n + 2 : Nat) : Real) ≠ 0 := by positivity
  push_cast
  field_simp [hne]

/-- Unit masses, used only to turn the static potential-energy construction
into a literal Hamiltonian-density counterexample. -/
def unitPositiveMassConfig (N : Nat) : Lattice.PositiveMassConfig N where
  mass := fun _ => 1
  mass_pos := fun _ => by norm_num

/-- The momentum-zero member of every finite-volume phase space. -/
def zeroMomentum (N : Nat) : Lattice.Configuration N := fun _ => 0

/-- At zero momentum and unit masses, the Hamiltonian density is exactly the
defect potential-energy density. -/
theorem periodicEnergyDensity_zeroMomentum_singleTensileDefect_eq
    (n : Nat) (depth r₀ b : Real) :
    periodicEnergyDensity (unitPositiveMassConfig (n + 2)) depth r₀
        (zeroMomentum (n + 2))
        (singleTensileDefectConfiguration n b) =
      defectPotentialEnergyDensity n depth r₀ b := by
  unfold periodicEnergyDensity periodicRandomMassHamiltonian
  unfold defectPotentialEnergyDensity zeroMomentum Lattice.kineticEnergy
  simp

/-- The same thermodynamic limit therefore holds for the literal LJ
Hamiltonian density at zero momentum. -/
theorem tendsto_defectHamiltonianEnergyDensity
    {depth r₀ b : Real} (hb : 0 < b) :
    Tendsto
      (fun n : Nat =>
        periodicEnergyDensity (unitPositiveMassConfig (n + 2)) depth r₀
          (zeroMomentum (n + 2))
          (singleTensileDefectConfiguration n b))
      atTop (𝓝 (bondPotential depth r₀ (-b))) := by
  apply (tendsto_defectPotentialEnergyDensity hb).congr'
  exact Eventually.of_forall fun n =>
    (periodicEnergyDensity_zeroMomentum_singleTensileDefect_eq
      n depth r₀ b).symm

/-- Every fixed tube is eventually violated because its cut strain grows
linearly in the volume. -/
theorem eventually_not_uniformRelativeTube
    {r₀ ρ b : Real} (hb : 0 < b) :
    ∀ᶠ n : Nat in atTop,
      ¬ UniformRelativeTube r₀ ρ
        (singleTensileDefectConfiguration n b) := by
  have hindexReal :
      Tendsto (fun n : Nat => ((n + 1 : Nat) : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hcut : Tendsto
      (fun n : Nat => ((n + 1 : Nat) : Real) * b) atTop atTop :=
    hindexReal.atTop_mul_const hb
  have hlarge : ∀ᶠ n : Nat in atTop,
      ρ * r₀ ≤ ((n + 1 : Nat) : Real) * b :=
    hcut.eventually (Ici_mem_atTop (ρ * r₀))
  filter_upwards [hlarge] with n hn
  exact not_uniformRelativeTube_of_cut_large n hb.le hn

/-- Continuity at the LJ equilibrium lets one choose a nonzero compression
whose repeated-bond energy lies below any prescribed positive density. -/
theorem exists_small_compression_bondPotential_lt
    {depth r₀ e : Real} (hr₀ : 0 < r₀) (he : 0 < e) :
    ∃ b : Real,
      0 < b ∧ b < r₀ ∧ bondPotential depth r₀ (-b) < e := by
  have hbond : BondAdmissible r₀ 0 := by
    simpa [BondAdmissible, Admissible] using hr₀
  have hnegative : ContinuousAt (fun b : Real => -b) 0 := by
    fun_prop
  have houter : ContinuousAt (bondPotential depth r₀) (-(0 : Real)) := by
    simpa only [neg_zero] using
      (hasDerivAt_bondPotential (depth := depth) hbond).continuousAt
  have hcontinuous : ContinuousAt
      (fun b : Real => bondPotential depth r₀ (-b)) 0 := by
    exact ContinuousAt.comp' (f := fun b : Real => -b)
      (g := bondPotential depth r₀) houter hnegative
  obtain ⟨δ, hδ, hclose⟩ :=
    (Metric.continuousAt_iff.mp hcontinuous) e he
  let b : Real := min (r₀ / 2) (δ / 2)
  have hb : 0 < b := by
    exact lt_min (by linarith) (by linarith)
  have hbr₀ : b < r₀ := by
    exact (min_le_left _ _).trans_lt (by linarith)
  have hbδ : b < δ := by
    exact (min_le_right _ _).trans_lt (by linarith)
  have hdist : dist b 0 < δ := by
    simpa [Real.dist_eq, abs_of_pos hb] using hbδ
  have hpotentialDistance := hclose hdist
  have habs : |bondPotential depth r₀ (-b)| < e := by
    simpa [Real.dist_eq, bondPotential_zero hr₀.ne'] using hpotentialDistance
  exact ⟨b, hb, hbr₀, (le_abs_self _).trans_lt habs⟩

/-- **Thermodynamic all-bond no-go.**  For every positive target energy
density and every fixed relative tube, there is a single fixed compression
`0 < b < r₀` such that, along the cofinal volumes `N = n + 2`, the
configuration is admissible and has Hamiltonian energy density below the
target, yet it is eventually outside the all-bond tube.

Thus no positive `N`-independent bound on mean LJ energy density can imply a
uniform Taylor tube without an additional sup-norm or probabilistic-tail
hypothesis. -/
theorem eventually_admissible_lowEnergyDensity_not_uniformRelativeTube
    {depth r₀ ρ e : Real} (hr₀ : 0 < r₀) (he : 0 < e) :
    ∃ b : Real,
      0 < b ∧ b < r₀ ∧
      Tendsto
        (fun n : Nat =>
          periodicEnergyDensity (unitPositiveMassConfig (n + 2)) depth r₀
            (zeroMomentum (n + 2))
            (singleTensileDefectConfiguration n b))
        atTop (𝓝 (bondPotential depth r₀ (-b))) ∧
      bondPotential depth r₀ (-b) < e ∧
      ∀ᶠ n : Nat in atTop,
        AdmissibleConfiguration r₀
            (singleTensileDefectConfiguration n b) ∧
          periodicEnergyDensity (unitPositiveMassConfig (n + 2)) depth r₀
              (zeroMomentum (n + 2))
              (singleTensileDefectConfiguration n b) < e ∧
          ¬ UniformRelativeTube r₀ ρ
              (singleTensileDefectConfiguration n b) := by
  obtain ⟨b, hb, hbr₀, hlimit_lt⟩ :=
    exists_small_compression_bondPotential_lt (depth := depth) (r₀ := r₀) (e := e) hr₀ he
  have hlimit := tendsto_defectHamiltonianEnergyDensity (depth := depth) (r₀ := r₀) hb
  have henergy : ∀ᶠ n : Nat in atTop,
      periodicEnergyDensity (unitPositiveMassConfig (n + 2)) depth r₀
          (zeroMomentum (n + 2))
          (singleTensileDefectConfiguration n b) < e :=
    hlimit.eventually (Iio_mem_nhds hlimit_lt)
  have htube := eventually_not_uniformRelativeTube (r₀ := r₀) (ρ := ρ) hb
  refine ⟨b, hb, hbr₀, hlimit, hlimit_lt, ?_⟩
  filter_upwards [henergy, htube] with n hnenergy hntube
  exact ⟨singleTensileDefectConfiguration_admissible hb hbr₀ n,
    hnenergy, hntube⟩

end

end ArchonPhysics.LennardJonesEnergyDensityTubeCounterexample
