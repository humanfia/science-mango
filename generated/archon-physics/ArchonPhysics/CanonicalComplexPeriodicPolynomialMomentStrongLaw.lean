import ArchonPhysics.CenteredTranslatedWindowAverage
import ArchonPhysics.ComplexPeriodicPolynomialWindowRowSum
import ArchonPhysics.FiniteMassPolynomialAvoidance

/-!
# Canonical complex periodic polynomial moment strong law

The local observable is the sum over the common right endpoint of the three
complex polynomial window legs.  Its ordinary iid sliding-window strong law
is transferred first to cyclic windows using the explicit wrap estimate and
then, through the centered target-to-shift permutation and the exact periodic
row-sum theorem, to the complete periodic double sum per site of the first
finite iid restriction.

Only polynomial weighted-cycle matrices occur here; no simple-spectrum
hypothesis is needed.
-/

namespace ArchonPhysics.CanonicalComplexPeriodicPolynomialMomentStrongLaw

open ArchonPhysics
open ArchonPhysics.CenteredTranslatedWindowAverage
open ArchonPhysics.ComplexFiniteWindowIIDAllVolumeStrongLaw
open ArchonPhysics.ComplexPeriodicPolynomialWindowRowSum
open ArchonPhysics.ComplexPolynomialMarkedLegWindowStrongLaw
open ArchonPhysics.CyclicWindowPrefixComparison
open ArchonPhysics.PeriodicPolynomialWindowGeometricInterior
open ArchonPhysics.PeriodicPolynomialWindowReindex
open ArchonPhysics.PeriodicPolynomialWindowRowSum
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Fixed-window complex row observable: sum the three-leg product over one
right endpoint shared by all three legs. -/
def complexPolynomialRowWindowObservable
    (windowRadius : Nat)
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real)
    (x : Fin (2 * windowRadius + 1) → Real) : Complex :=
  ∑ b : Fin (2 * windowRadius + 1),
    complexThreeLegPolynomialWindowProduct
      cosineDegree sineDegree cosineCoefficient sineCoefficient
      (fun _ ↦ centeredWindowIndex windowRadius) (fun _ ↦ b) x

theorem continuous_complexPolynomialRowWindowObservable
    (windowRadius : Nat)
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real) :
    Continuous (complexPolynomialRowWindowObservable windowRadius
      cosineDegree sineDegree cosineCoefficient sineCoefficient) := by
  unfold complexPolynomialRowWindowObservable
  exact continuous_finsetSum Finset.univ (fun b _hb ↦
    continuous_complexThreeLegPolynomialWindowProduct
      cosineDegree sineDegree cosineCoefficient sineCoefficient
      (fun _ ↦ centeredWindowIndex windowRadius) (fun _ ↦ b))

theorem measurable_complexPolynomialRowWindowObservable
    (windowRadius : Nat)
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real) :
    Measurable (complexPolynomialRowWindowObservable windowRadius
      cosineDegree sineDegree cosineCoefficient sineCoefficient) :=
  (continuous_complexPolynomialRowWindowObservable windowRadius
    cosineDegree sineDegree cosineCoefficient sineCoefficient).measurable

theorem complexPolynomialRowWindowObservable_clipWindow
    (windowRadius : Nat)
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real)
    (x : Fin (2 * windowRadius + 1) → Real) :
    complexPolynomialRowWindowObservable windowRadius
        cosineDegree sineDegree cosineCoefficient sineCoefficient
        (PolynomialMarkedLegWindowStrongLaw.clipWindow x) =
      complexPolynomialRowWindowObservable windowRadius
        cosineDegree sineDegree cosineCoefficient sineCoefficient x := by
  unfold complexPolynomialRowWindowObservable
  apply Finset.sum_congr rfl
  intro b _hb
  exact complexThreeLegPolynomialWindowProduct_clipWindow
    cosineDegree sineDegree cosineCoefficient sineCoefficient
      (fun _ ↦ centeredWindowIndex windowRadius) (fun _ ↦ b) x

/-- Compactness of the frozen mass cube gives a single deterministic bound
for the complete local row observable. -/
theorem exists_uniformBound_complexPolynomialRowWindowObservable
    (windowRadius : Nat)
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real) :
    ∃ C : Real, ∀ x : Fin (2 * windowRadius + 1) → Real,
      ‖complexPolynomialRowWindowObservable windowRadius
        cosineDegree sineDegree cosineCoefficient sineCoefficient x‖ ≤ C := by
  let K : Set (Fin (2 * windowRadius + 1) → Real) :=
    Set.pi Set.univ (fun _ ↦ massSupport)
  have hK : IsCompact K :=
    isCompact_univ_pi (fun _ ↦ isCompact_Icc)
  let g : (Fin (2 * windowRadius + 1) → Real) → Real := fun x ↦
    ‖complexPolynomialRowWindowObservable windowRadius
      cosineDegree sineDegree cosineCoefficient sineCoefficient x‖
  have hg : Continuous g :=
    (continuous_complexPolynomialRowWindowObservable windowRadius
      cosineDegree sineDegree cosineCoefficient sineCoefficient).norm
  have hcompact : IsCompact (g '' K) := hK.image hg
  rcases hcompact.bddAbove with ⟨C, hC⟩
  refine ⟨C, fun x ↦ ?_⟩
  rw [← complexPolynomialRowWindowObservable_clipWindow windowRadius
    cosineDegree sineDegree cosineCoefficient sineCoefficient x]
  apply hC
  refine ⟨PolynomialMarkedLegWindowStrongLaw.clipWindow x, ?_, rfl⟩
  intro i _hi
  exact clippedMass_mem_support (x i)

/-- Ordinary all-volume strong law for the summed local row observable. -/
theorem complexPolynomialRowWindowObservable_allVolume_strongLaw_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (windowRadius : Nat)
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun N : Nat ↦ complexSpatialAverage ensemble
          (2 * windowRadius + 1)
          (complexPolynomialRowWindowObservable windowRadius
            cosineDegree sineDegree cosineCoefficient sineCoefficient)
          N omega)
        atTop
        (𝓝 (complexWindowMean ensemble (2 * windowRadius + 1)
          (complexPolynomialRowWindowObservable windowRadius
            cosineDegree sineDegree cosineCoefficient sineCoefficient))) := by
  obtain ⟨C, hC⟩ :=
    exists_uniformBound_complexPolynomialRowWindowObservable windowRadius
      cosineDegree sineDegree cosineCoefficient sineCoefficient
  exact complexSpatialAverage_allVolume_strongLaw_ae
    ensemble (2 * windowRadius + 1) (by omega)
    (complexPolynomialRowWindowObservable windowRadius
      cosineDegree sineDegree cosineCoefficient sineCoefficient)
    (measurable_complexPolynomialRowWindowObservable windowRadius
      cosineDegree sineDegree cosineCoefficient sineCoefficient)
    C (fun x _hx ↦ hC x)

/-- Cyclic all-volume strong law.  This invokes the deterministic
`2*C*W/N` wrap comparison rather than assuming cyclic convergence. -/
theorem complexPolynomialRowWindowObservable_cyclic_strongLaw_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (windowRadius : Nat)
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun N : Nat ↦ cyclicComplexWindowAverage ensemble N
          (2 * windowRadius + 1)
          (complexPolynomialRowWindowObservable windowRadius
            cosineDegree sineDegree cosineCoefficient sineCoefficient)
          omega)
        atTop
        (𝓝 (complexWindowMean ensemble (2 * windowRadius + 1)
          (complexPolynomialRowWindowObservable windowRadius
            cosineDegree sineDegree cosineCoefficient sineCoefficient))) := by
  obtain ⟨C, hC⟩ :=
    exists_uniformBound_complexPolynomialRowWindowObservable windowRadius
      cosineDegree sineDegree cosineCoefficient sineCoefficient
  filter_upwards
    [complexSpatialAverage_allVolume_strongLaw_ae
      ensemble (2 * windowRadius + 1) (by omega)
      (complexPolynomialRowWindowObservable windowRadius
        cosineDegree sineDegree cosineCoefficient sineCoefficient)
      (measurable_complexPolynomialRowWindowObservable windowRadius
        cosineDegree sineDegree cosineCoefficient sineCoefficient)
      C (fun x _hx ↦ hC x)] with omega homega
  exact tendsto_cyclicComplexWindowAverage_of_complexSpatialAverage
    ensemble (2 * windowRadius + 1)
    (complexPolynomialRowWindowObservable windowRadius
      cosineDegree sineDegree cosineCoefficient sineCoefficient)
    C (fun x _hx ↦ hC x) omega
    (complexWindowMean ensemble (2 * windowRadius + 1)
      (complexPolynomialRowWindowObservable windowRadius
        cosineDegree sineDegree cosineCoefficient sineCoefficient))
    homega

/-- Complete complex polynomial periodic double sum per site for one finite
mass vector. -/
def complexPeriodicPolynomialDoubleMomentPerSite
    {N : Nat} [NeZero N] (x : Fin N → Real)
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real) : Complex :=
  (∑ target : Fin N, ∑ l : Fin N, ∏ r : Fin 3,
    complexPeriodicPolynomialLeg x
      (cosineDegree r) (sineDegree r)
      (cosineCoefficient r) (sineCoefficient r) target l) / (N : Real)

/-- At every volume larger than the fixed window, the periodic double moment
of the first iid restriction is exactly the corresponding cyclic local-row
average. -/
theorem complexPeriodicPolynomialDoubleMomentPerSite_restrict_eq_cyclic
    (ensemble : IIDMassPhaseEnsemble Omega)
    {m windowRadius : Nat} [NeZero m] (omega : Omega)
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real)
    (hcosine : ∀ r, cosineDegree r + 1 ≤ windowRadius)
    (hsine : ∀ r, sineDegree r + 1 ≤ windowRadius) :
    complexPeriodicPolynomialDoubleMomentPerSite
        (ensemble.restrictMassFin
          (N := (2 * windowRadius + 1) + m) omega)
        cosineDegree sineDegree cosineCoefficient sineCoefficient =
      cyclicComplexWindowAverage ensemble
        ((2 * windowRadius + 1) + m) (2 * windowRadius + 1)
        (complexPolynomialRowWindowObservable windowRadius
          cosineDegree sineDegree cosineCoefficient sineCoefficient) omega := by
  let centerBig : Fin ((2 * windowRadius + 1) + m) :=
    Fin.castAdd m (centeredWindowIndex windowRadius)
  calc
    complexPeriodicPolynomialDoubleMomentPerSite
        (ensemble.restrictMassFin
          (N := (2 * windowRadius + 1) + m) omega)
        cosineDegree sineDegree cosineCoefficient sineCoefficient =
      (∑ target : Fin ((2 * windowRadius + 1) + m),
        complexPolynomialRowWindowObservable windowRadius
          cosineDegree sineDegree cosineCoefficient sineCoefficient
          (translatedMassWindow
            (ensemble.restrictMassFin
              (N := (2 * windowRadius + 1) + m) omega)
            (finCenteringShift centerBig target))) /
              (((2 * windowRadius + 1) + m : Nat) : Real) := by
        unfold complexPeriodicPolynomialDoubleMomentPerSite
        congr 1
        apply Finset.sum_congr rfl
        intro target _htarget
        simpa [complexPolynomialRowWindowObservable, centerBig] using
          complexThreeLegPeriodicPolynomialRowSum_eq_centeredWindowSum
            (ensemble.restrictMassFin
              (N := (2 * windowRadius + 1) + m) omega)
            target cosineDegree sineDegree
            cosineCoefficient sineCoefficient hcosine hsine
    _ = cyclicComplexWindowAverage ensemble
        ((2 * windowRadius + 1) + m) (2 * windowRadius + 1)
        (complexPolynomialRowWindowObservable windowRadius
          cosineDegree sineDegree cosineCoefficient sineCoefficient) omega := by
      change
        (∑ target : Fin ((2 * windowRadius + 1) + m),
          complexPolynomialRowWindowObservable windowRadius
            cosineDegree sineDegree cosineCoefficient sineCoefficient
            (translatedMassWindow
              (fun i : Fin ((2 * windowRadius + 1) + m) ↦
                ensemble.mass i.val omega)
              (finCenteringShift centerBig target))) /
            (((2 * windowRadius + 1) + m : Nat) : Real) = _
      exact centeredTranslatedWindowAverage_eq_cyclicComplexWindowAverage
        ensemble omega centerBig
        (complexPolynomialRowWindowObservable windowRadius
          cosineDegree sineDegree cosineCoefficient sineCoefficient)
/-- Canonical first-volume restriction along
`N = (2 * windowRadius + 1) + (m + 1)`. -/
def canonicalRestrictedComplexPeriodicPolynomialMoment
    (ensemble : IIDMassPhaseEnsemble Omega)
    (windowRadius : Nat)
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real)
    (m : Nat) (omega : Omega) : Complex :=
  complexPeriodicPolynomialDoubleMomentPerSite
    (ensemble.restrictMassFin
      (N := (2 * windowRadius + 1) + (m + 1)) omega)
    cosineDegree sineDegree cosineCoefficient sineCoefficient

theorem canonicalRestrictedComplexPeriodicPolynomialMoment_eq_cyclic
    (ensemble : IIDMassPhaseEnsemble Omega)
    (windowRadius : Nat)
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real)
    (hcosine : ∀ r, cosineDegree r + 1 ≤ windowRadius)
    (hsine : ∀ r, sineDegree r + 1 ≤ windowRadius)
    (m : Nat) (omega : Omega) :
    canonicalRestrictedComplexPeriodicPolynomialMoment ensemble windowRadius
        cosineDegree sineDegree cosineCoefficient sineCoefficient m omega =
      cyclicComplexWindowAverage ensemble
        ((2 * windowRadius + 1) + (m + 1)) (2 * windowRadius + 1)
        (complexPolynomialRowWindowObservable windowRadius
          cosineDegree sineDegree cosineCoefficient sineCoefficient) omega := by
  exact complexPeriodicPolynomialDoubleMomentPerSite_restrict_eq_cyclic
    ensemble omega cosineDegree sineDegree cosineCoefficient sineCoefficient
      hcosine hsine

/-- Almost-sure thermodynamic strong law for the complete fixed-polynomial
complex periodic double moment per site. -/
theorem canonicalRestrictedComplexPeriodicPolynomialMoment_strongLaw_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (windowRadius : Nat)
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real)
    (hcosine : ∀ r, cosineDegree r + 1 ≤ windowRadius)
    (hsine : ∀ r, sineDegree r + 1 ≤ windowRadius) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun m : Nat ↦
          canonicalRestrictedComplexPeriodicPolynomialMoment ensemble
            windowRadius cosineDegree sineDegree
            cosineCoefficient sineCoefficient m omega)
        atTop
        (𝓝 (complexWindowMean ensemble (2 * windowRadius + 1)
          (complexPolynomialRowWindowObservable windowRadius
            cosineDegree sineDegree cosineCoefficient sineCoefficient))) := by
  filter_upwards
    [complexPolynomialRowWindowObservable_cyclic_strongLaw_ae
      ensemble windowRadius cosineDegree sineDegree
        cosineCoefficient sineCoefficient] with omega homega
  have hvolume : Tendsto
      (fun m : Nat ↦ (2 * windowRadius + 1) + (m + 1)) atTop atTop := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Filter.tendsto_add_atTop_nat ((2 * windowRadius + 1) + 1))
  apply (homega.comp hvolume).congr'
  exact Eventually.of_forall fun m ↦
    (canonicalRestrictedComplexPeriodicPolynomialMoment_eq_cyclic
      ensemble windowRadius cosineDegree sineDegree
      cosineCoefficient sineCoefficient hcosine hsine m omega).symm

end
end ArchonPhysics.CanonicalComplexPeriodicPolynomialMomentStrongLaw
