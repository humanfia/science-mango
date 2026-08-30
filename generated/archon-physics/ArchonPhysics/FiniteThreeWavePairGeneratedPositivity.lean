import ArchonPhysics.FiniteThreeWaveGlobalStrictPositivity

/-!
# Pair-generated strict positivity for finite three-wave flows

For a quadratic three-wave collision, ordinary hypergraph connectivity and
positive total energy do not force instantaneous positivity: one populated
leg of a single connected triad is a stationary boundary state.  The correct
finite combinatorial condition is two-neighbour bootstrap reachability.  A
mode is activated when it belongs to a positive-rate triad whose other two,
pairwise-distinct legs are already active.

This module proves that every mode in the resulting finite closure is strictly
positive at every positive time.  It uses only the existing nonnegative global
flow, the explicit gain--loss estimate, and `g ≠ 0`.
-/

namespace ArchonPhysics.FiniteThreeWavePairGeneratedPositivity

open Set
open ArchonPhysics
open ArchonPhysics.ConditionalFiniteThreeWaveKineticFamily
open ArchonPhysics.FiniteThreeWaveCollisionNetwork
open ArchonPhysics.FiniteThreeWaveGlobalStrictPositivity
open ArchonPhysics.FiniteThreeWaveKineticGlobalFlow
open ArchonPhysics.FiniteThreeWaveStrictPositivity

noncomputable section

variable {Mode Triad : Type}
variable [Fintype Mode] [DecidableEq Mode] [Fintype Triad]

/-- The three legs of a collision are genuinely distinct. -/
def TriadPairwiseDistinct
    (network : Network Mode Triad) (a : Triad) : Prop :=
  network.mode₁ a ≠ network.mode₂ a /\
    network.mode₁ a ≠ network.mode₃ a /\
      network.mode₂ a ≠ network.mode₃ a

/-- A positive-rate collision generates `i` from two already active other
legs. -/
def PairGenerates
    (network : Network Mode Triad) (rate : Triad -> Real)
    (active : Set Mode) (i : Mode) : Prop :=
  exists a : Triad, 0 < rate a /\ TriadPairwiseDistinct network a /\
    ((i = network.mode₁ a /\ network.mode₂ a ∈ active /\
        network.mode₃ a ∈ active) \/
      (i = network.mode₂ a /\ network.mode₁ a ∈ active /\
        network.mode₃ a ∈ active) \/
      (i = network.mode₃ a /\ network.mode₁ a ∈ active /\
        network.mode₂ a ∈ active))

/-- Iterated two-neighbour closure of an initially active mode set. -/
def pairClosure
    (network : Network Mode Triad) (rate : Triad -> Real)
    (seed : Set Mode) : Nat -> Set Mode
  | 0 => seed
  | n + 1 => pairClosure network rate seed n ∪
      {i | PairGenerates network rate (pairClosure network rate seed n) i}

/-- Every mode is reached after finitely many two-neighbour activations from
the strictly positive initial support. -/
def PairGeneratedFromInitialSupport
    (network : Network Mode Triad) (rate : Triad -> Real)
    (actionZero : Mode -> Real) : Prop :=
  forall i, exists n,
    i ∈ pairClosure network rate {j | 0 < actionZero j} n

/-- A selected distinct triad contributes strictly inward at a zero leg when
its other two actions and its rate are strictly positive. -/
theorem triadContribution_pos_at_boundary_of_other_two_pos
    (network : Network Mode Triad) (rate : Triad -> Real)
    (action : Mode -> Real) (a : Triad) (i : Mode)
    (hrate : 0 < rate a) (hdistinct : TriadPairwiseDistinct network a)
    (hi : action i = 0)
    (hlegs :
      (i = network.mode₁ a /\ 0 < action (network.mode₂ a) /\
        0 < action (network.mode₃ a)) \/
      (i = network.mode₂ a /\ 0 < action (network.mode₁ a) /\
        0 < action (network.mode₃ a)) \/
      (i = network.mode₃ a /\ 0 < action (network.mode₁ a) /\
        0 < action (network.mode₂ a))) :
    0 < rate a * networkTriadFlux network action a *
      stoichiometricCoefficient network a i := by
  rcases hdistinct with ⟨h12, h13, h23⟩
  rcases hlegs with hleg | hleg | hleg
  · rcases hleg with ⟨rfl, h2, h3⟩
    simp [networkTriadFlux, ThreeWaveCollisionAlgebra.collisionFlux,
      stoichiometricCoefficient, hi, h12, h13]
    positivity
  · rcases hleg with ⟨rfl, h1, h3⟩
    simp [networkTriadFlux, ThreeWaveCollisionAlgebra.collisionFlux,
      stoichiometricCoefficient, hi, h12.symm, h23]
    positivity
  · rcases hleg with ⟨rfl, h1, h2⟩
    simp [networkTriadFlux, ThreeWaveCollisionAlgebra.collisionFlux,
      stoichiometricCoefficient, hi, h13.symm, h23.symm]
    positivity

/-- Pair generation makes the complete collision field strictly inward at a
vanishing generated coordinate. -/
theorem collisionVectorField_pos_at_boundary_of_pairGenerates
    (network : Network Mode Triad) (rate : Triad -> Real)
    (action : Mode -> Real) (i : Mode)
    (hrate : forall a, 0 <= rate a)
    (haction : forall j, 0 <= action j) (hi : action i = 0)
    (hgenerate : PairGenerates network rate {j | 0 < action j} i) :
    0 < collisionVectorField network rate action i := by
  rcases hgenerate with ⟨a, haRate, haDistinct, haLegs⟩
  unfold collisionVectorField
  apply Finset.sum_pos'
  · intro b _hb
    exact triadContribution_nonneg_at_boundary
      network rate action i b (hrate b) haction hi
  · refine ⟨a, Finset.mem_univ a, ?_⟩
    apply triadContribution_pos_at_boundary_of_other_two_pos
      network rate action a i haRate haDistinct hi
    rcases haLegs with hleg | hleg | hleg
    · exact Or.inl hleg
    · exact Or.inr (Or.inl hleg)
    · exact Or.inr (Or.inr hleg)

/-- Strict integrating-factor variant: a nonnegative initial coordinate
becomes positive at every positive time when the gain--loss derivative is
strictly positive throughout the open positive half-line. -/
theorem positive_for_posTime_of_hasDerivAt_add_rate_mul_pos
    (position velocity : Real -> Real) (rate : Real)
    (hinitial : 0 <= position 0)
    (hposition : forall t, 0 <= t -> HasDerivAt position (velocity t) t)
    (hloss : forall t, 0 < t ->
      0 < velocity t + rate * position t) :
    forall t, 0 < t -> 0 < position t := by
  let weighted : Real -> Real := fun t => Real.exp (rate * t) * position t
  have hweightedDeriv : forall t, 0 <= t -> HasDerivAt weighted
      (Real.exp (rate * t) * (velocity t + rate * position t)) t := by
    intro t ht
    have hexp : HasDerivAt (fun s => Real.exp (rate * s))
        (Real.exp (rate * t) * rate) t := by
      simpa only [Function.comp_def, mul_one] using
        (Real.hasDerivAt_exp (rate * t)).comp t
        ((hasDerivAt_id t).const_mul rate)
    change HasDerivAt
      (fun s => Real.exp (rate * s) * position s)
      (Real.exp (rate * t) * (velocity t + rate * position t)) t
    apply (hexp.mul (hposition t ht)).congr_deriv
    ring
  have hweightedStrict : StrictMonoOn weighted (Ici 0) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0)
    · intro t ht
      exact (hweightedDeriv t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hweightedDeriv t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      have htpos : 0 < t := by
        simpa only [interior_Ici, mem_Ioi] using ht
      exact mul_pos (Real.exp_pos _) (hloss t htpos)
  intro t ht
  have hmono : weighted 0 < weighted t :=
    hweightedStrict (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht.le) ht
  have hzeroNonnegative : 0 <= weighted 0 := by
    simpa only [weighted, mul_zero, Real.exp_zero, one_mul] using hinitial
  have hweightedPos : 0 < weighted t := hzeroNonnegative.trans_lt hmono
  exact pos_of_mul_pos_right hweightedPos (Real.exp_pos _).le

private def actionCeiling
    {model : FiniteCollisionModel Mode Triad} {g : Real}
    {actionZero : Mode -> Real}
    (_flow : GlobalForwardCertificate model g actionZero) : Real :=
  totalKineticEnergy model.frequency actionZero / model.omegaMin

private theorem actionCeiling_nonnegative
    {model : FiniteCollisionModel Mode Triad} {g : Real}
    {actionZero : Mode -> Real}
    (flow : GlobalForwardCertificate model g actionZero) :
    0 <= actionCeiling flow := by
  have hzero : forall i, 0 <= actionZero i := by
    intro i
    have hi := flow.nonnegative 0 le_rfl i
    rw [flow.initial] at hi
    exact hi
  exact div_nonneg
    (Finset.sum_nonneg fun i _ =>
      mul_nonneg
        (model.omegaMin_pos.le.trans (model.frequency_lower i))
        (hzero i))
    model.omegaMin_pos.le

private theorem trajectory_le_actionCeiling
    {model : FiniteCollisionModel Mode Triad} {g : Real}
    {actionZero : Mode -> Real}
    (flow : GlobalForwardCertificate model g actionZero)
    {t : Real} (ht : 0 <= t) (i : Mode) :
    flow.trajectory t i <= actionCeiling flow := by
  have hterm : model.frequency i * flow.trajectory t i <=
      ∑ j, model.frequency j * flow.trajectory t j := by
    exact Finset.single_le_sum
      (fun j _ => mul_nonneg
        (model.omegaMin_pos.le.trans (model.frequency_lower j))
        (flow.nonnegative t ht j))
      (Finset.mem_univ i)
  have hweighted : flow.trajectory t i * model.omegaMin <=
      totalKineticEnergy model.frequency actionZero := by
    calc
      flow.trajectory t i * model.omegaMin <=
          flow.trajectory t i * model.frequency i :=
        mul_le_mul_of_nonneg_left (model.frequency_lower i)
          (flow.nonnegative t ht i)
      _ = model.frequency i * flow.trajectory t i := by ring
      _ <= totalKineticEnergy model.frequency (flow.trajectory t) := by
        simpa only [totalKineticEnergy] using hterm
      _ = totalKineticEnergy model.frequency actionZero :=
        flow.energy_conserved t ht
  exact (le_div_iff₀ model.omegaMin_pos).2 hweighted

private def coordinateLossRate
    {model : FiniteCollisionModel Mode Triad} {g : Real}
    {actionZero : Mode -> Real}
    (flow : GlobalForwardCertificate model g actionZero) : Real :=
  g ^ 2 * (6 * actionCeiling flow * (∑ a, model.rate a))

private theorem coordinate_gainLoss_nonnegative
    {model : FiniteCollisionModel Mode Triad} {g : Real}
    {actionZero : Mode -> Real}
    (flow : GlobalForwardCertificate model g actionZero)
    {t : Real} (ht : 0 <= t) (i : Mode) :
    0 <= waveKineticVectorField model.collisionData g
        (flow.trajectory t) i +
      coordinateLossRate flow * flow.trajectory t i := by
  have hcollision := collisionVectorField_add_loss_nonnegative
    model.network model.rate (flow.trajectory t) (actionCeiling flow)
      (actionCeiling_nonnegative flow) model.rate_nonneg
      (flow.nonnegative t ht) (trajectory_le_actionCeiling flow ht) i
  have hscaled := mul_nonneg (sq_nonneg g) hcollision
  change 0 <=
    g ^ 2 * collisionVectorField model.network model.rate
        (flow.trajectory t) i +
      coordinateLossRate flow * flow.trajectory t i
  dsimp only [coordinateLossRate]
  nlinarith

/-- Positivity of one initially positive coordinate propagates independently
of the support of all other coordinates. -/
theorem GlobalForwardCertificate.coordinate_strictlyPositive_of_initial
    {model : FiniteCollisionModel Mode Triad} {g : Real}
    {actionZero : Mode -> Real}
    (flow : GlobalForwardCertificate model g actionZero)
    (i : Mode) (hi : 0 < actionZero i) :
    forall t, 0 <= t -> 0 < flow.trajectory t i := by
  apply positive_of_hasDerivAt_add_rate_mul_nonnegative
    (fun t => flow.trajectory t i)
    (fun t => waveKineticVectorField model.collisionData g
      (flow.trajectory t) i)
    (coordinateLossRate flow)
  · rw [flow.initial]
    exact hi
  · intro t ht
    exact hasDerivAt_pi.mp (flow.equation t ht) i
  · intro t ht
    exact coordinate_gainLoss_nonnegative flow ht i

/-- If the other two legs of some positive-rate distinct triad are positive
at every positive time, its selected leg is positive at every positive time,
even when it starts at zero. -/
theorem GlobalForwardCertificate.coordinate_strictlyPositive_for_posTime_of_pair
    {model : FiniteCollisionModel Mode Triad} {g : Real}
    {actionZero : Mode -> Real}
    (flow : GlobalForwardCertificate model g actionZero)
    (hg : g ≠ 0) (i : Mode)
    (hpair : forall t, 0 < t ->
      PairGenerates model.network model.rate
        {j | 0 < flow.trajectory t j} i) :
    forall t, 0 < t -> 0 < flow.trajectory t i := by
  apply positive_for_posTime_of_hasDerivAt_add_rate_mul_pos
    (fun t => flow.trajectory t i)
    (fun t => waveKineticVectorField model.collisionData g
      (flow.trajectory t) i)
    (coordinateLossRate flow + g ^ 2)
  · exact flow.nonnegative 0 le_rfl i
  · intro t ht
    exact hasDerivAt_pi.mp (flow.equation t ht) i
  · intro t ht
    have hbase := coordinate_gainLoss_nonnegative flow ht.le i
    have hiNonnegative := flow.nonnegative t ht.le i
    by_cases hiZero : flow.trajectory t i = 0
    · have hfield := collisionVectorField_pos_at_boundary_of_pairGenerates
        model.network model.rate (flow.trajectory t) i model.rate_nonneg
          (flow.nonnegative t ht.le) hiZero (hpair t ht)
      have hscaled := mul_pos (sq_pos_of_ne_zero hg) hfield
      change 0 <
        g ^ 2 * collisionVectorField model.network model.rate
            (flow.trajectory t) i +
          (coordinateLossRate flow + g ^ 2) * flow.trajectory t i
      rw [hiZero]
      simpa only [mul_zero, add_zero] using hscaled
    · have hiPositive : 0 < flow.trajectory t i :=
        lt_of_le_of_ne hiNonnegative (Ne.symm hiZero)
      have hextra : 0 < g ^ 2 * flow.trajectory t i :=
        mul_pos (sq_pos_of_ne_zero hg) hiPositive
      nlinarith

/-- Membership in the finite pair closure implies strict positivity at every
positive time. -/
theorem GlobalForwardCertificate.positive_for_posTime_of_mem_pairClosure
    {model : FiniteCollisionModel Mode Triad} {g : Real}
    {actionZero : Mode -> Real}
    (flow : GlobalForwardCertificate model g actionZero)
    (hg : g ≠ 0) (n : Nat) (i : Mode)
    (hi : i ∈ pairClosure model.network model.rate
      {j | 0 < actionZero j} n) :
    forall t, 0 < t -> 0 < flow.trajectory t i := by
  induction n generalizing i with
  | zero =>
      change 0 < actionZero i at hi
      intro t ht
      exact ArchonPhysics.FiniteThreeWavePairGeneratedPositivity.GlobalForwardCertificate.coordinate_strictlyPositive_of_initial flow i hi t ht.le
  | succ n inductionHypothesis =>
      change i ∈ pairClosure model.network model.rate
          {j | 0 < actionZero j} n ∪
        {j | PairGenerates model.network model.rate
          (pairClosure model.network model.rate
            {k | 0 < actionZero k} n) j} at hi
      rw [mem_union] at hi
      rcases hi with hi | hi
      · exact inductionHypothesis i hi
      · change PairGenerates model.network model.rate
          (pairClosure model.network model.rate
            {k | 0 < actionZero k} n) i at hi
        apply ArchonPhysics.FiniteThreeWavePairGeneratedPositivity.GlobalForwardCertificate.coordinate_strictlyPositive_for_posTime_of_pair flow hg i
        intro t ht
        rcases hi with ⟨a, haRate, haDistinct, haLegs⟩
        refine ⟨a, haRate, haDistinct, ?_⟩
        rcases haLegs with hleg | hleg | hleg
        · exact Or.inl ⟨hleg.1,
            inductionHypothesis _ hleg.2.1 t ht,
            inductionHypothesis _ hleg.2.2 t ht⟩
        · exact Or.inr (Or.inl ⟨hleg.1,
            inductionHypothesis _ hleg.2.1 t ht,
            inductionHypothesis _ hleg.2.2 t ht⟩)
        · exact Or.inr (Or.inr ⟨hleg.1,
            inductionHypothesis _ hleg.2.1 t ht,
            inductionHypothesis _ hleg.2.2 t ht⟩)

/-- Two-neighbour generation from the initial positive support makes the
whole finite trajectory strictly positive at every positive time. -/
theorem GlobalForwardCertificate.strictlyPositive_for_posTime_of_pairGenerated
    {model : FiniteCollisionModel Mode Triad} {g : Real}
    {actionZero : Mode -> Real}
    (flow : GlobalForwardCertificate model g actionZero)
    (hg : g ≠ 0)
    (hgenerated : PairGeneratedFromInitialSupport
      model.network model.rate actionZero) :
    forall t, 0 < t -> forall i, 0 < flow.trajectory t i := by
  intro t ht i
  obtain ⟨n, hi⟩ := hgenerated i
  exact ArchonPhysics.FiniteThreeWavePairGeneratedPositivity.GlobalForwardCertificate.positive_for_posTime_of_mem_pairClosure flow hg n i hi t ht

/-! ## Ordinary connectivity is not sufficient -/

/-- Every mode occurs in at least one collision triad.  This deliberately
weak ordinary connectivity notion is enough to state the obstruction. -/
def EveryModeIncident (network : Network Mode Triad) : Prop :=
  forall i, exists a,
    i = network.mode₁ a \/ i = network.mode₂ a \/ i = network.mode₃ a

def oneTriadNetwork : Network (Option Bool) Unit where
  mode₁ := fun _ => none
  mode₂ := fun _ => some false
  mode₃ := fun _ => some true

def oneTriadRate : Unit -> Real := fun _ => 1

def oneTriadFrequency : Option Bool -> Real
  | none => 2
  | some _ => 1

def oneSeedAction : Option Bool -> Real
  | none => 1
  | some _ => 0

/-- A connected positive-rate resonant triad can have positive total energy
and nevertheless support a stationary boundary state. -/
theorem ordinary_connectivity_and_positive_energy_do_not_force_positivity :
    EveryModeIncident oneTriadNetwork /\
      (forall a, 0 < oneTriadRate a) /\
      (forall a, oneTriadFrequency (oneTriadNetwork.mode₁ a) =
        oneTriadFrequency (oneTriadNetwork.mode₂ a) +
          oneTriadFrequency (oneTriadNetwork.mode₃ a)) /\
      0 < totalKineticEnergy oneTriadFrequency oneSeedAction /\
      collisionVectorField oneTriadNetwork oneTriadRate oneSeedAction = 0 /\
      ¬ (forall i, 0 < oneSeedAction i) := by
  constructor
  · intro i
    refine ⟨(), ?_⟩
    rcases i with _ | b
    · exact Or.inl rfl
    · rcases b with _ | _
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  constructor
  · intro a
    rcases a with ⟨⟩
    norm_num [oneTriadRate]
  constructor
  · intro a
    rcases a with ⟨⟩
    norm_num [oneTriadNetwork, oneTriadFrequency]
  constructor
  · norm_num [totalKineticEnergy, oneTriadFrequency, oneSeedAction]
  constructor
  · funext i
    simp [collisionVectorField, networkTriadFlux,
      ThreeWaveCollisionAlgebra.collisionFlux, stoichiometricCoefficient,
      oneTriadNetwork, oneTriadRate, oneSeedAction]
  · intro hall
    have := hall (some false)
    norm_num [oneSeedAction] at this

end

end ArchonPhysics.FiniteThreeWavePairGeneratedPositivity
