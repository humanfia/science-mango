import ArchonPhysics.ActualEightSiteFullIIDEpsilonLevelSmallBall
import ArchonPhysics.RandomMassOrderedProjectorBridge

/-!
# Algebraic reduction of the actual full-eight irregular mass

This module removes three potential exceptional sectors without an added
scientific assumption: the boundary of the iid mass cube, repeated harmonic
eigenvalues, and nonpositivity of the three selected modes all have zero
mass or are impossible.

The remaining sector is the zero locus of the selected three-mass projector
minor, equivalently the selected partial Jacobian.  Existing adjugate and
polynomial-zero-set infrastructure proves that this sector is null once one
supplies a nonzero inverse-mass polynomial whose zero set contains it on the
physical simple-spectrum locus.  The existence of that elimination
polynomial is exposed as a structure field; it is not asserted here.
-/

open scoped ENNReal Matrix Topology

namespace ArchonPhysics.ActualEightSiteFullIIDIrregularMassPolynomialReduction

open ArchonPhysics
open ArchonPhysics.ActualEightSiteExactAllDistinctLinearSmallBall
open ArchonPhysics.ActualEightSiteExactDecayIVTBridge
open ArchonPhysics.ActualEightSiteFullIIDAugmentedSpectralChart
open ArchonPhysics.ActualEightSiteFullIIDCompactGoodLevelSmallBallReduction
open ArchonPhysics.ActualEightSiteFullIIDEpsilonLevelSmallBall
open ArchonPhysics.ActualEightSiteFullIIDGoodLevelLimitAudit
open ArchonPhysics.ActualEightSiteFullIIDLocalLinearSmallBallUpper
open ArchonPhysics.ActualEightSiteFullIIDPositiveWeightedNearResonancePatch
open ArchonPhysics.ActualEightSiteFullIIDRegularLocalSmallBallUpper
open ArchonPhysics.ActualThreeMassHellmannFeynmanJacobian
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.PathLaplacianResultant
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.RandomMassResultantBridge
open ArchonPhysics.RandomMassSimpleSpectrum
open ArchonPhysics.SingleMassRankOnePerturbation
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ThreeParameterProjectorWeightJacobian
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Filter MeasureTheory Set

noncomputable section

/-- A single iid mass coordinate lies in the open support interval almost
surely. -/
theorem massCoordinate_mem_openSupport_ae :
    ∀ᵐ mass ∂massCoordinateLaw, mass ∈ Ioo massLower massUpper := by
  have hlower : massCoordinateLaw ({massLower} : Set Real) = 0 :=
    massCoordinateLaw_absolutelyContinuous_volume (by simp)
  have hupper : massCoordinateLaw ({massUpper} : Set Real) = 0 :=
    massCoordinateLaw_absolutelyContinuous_volume (by simp)
  have hnotLower := measure_eq_zero_iff_ae_notMem.mp hlower
  have hnotUpper := measure_eq_zero_iff_ae_notMem.mp hupper
  filter_upwards [massCoordinate_mem_support_ae, hnotLower, hnotUpper]
    with mass hsupport hneLower hneUpper
  simp only [mem_singleton_iff] at hneLower hneUpper
  exact ⟨lt_of_le_of_ne hsupport.1 (Ne.symm hneLower),
    lt_of_le_of_ne hsupport.2 hneUpper⟩

/-- The genuine eightfold iid law lies in the open physical mass cube almost
surely. -/
theorem finiteMassLaw_eight_mem_fullEightMassSupportInterior_ae :
    ∀ᵐ x ∂(finiteMassLaw 8), x ∈ fullEightMassSupportInterior := by
  have hcoordinate : ∀ i : Fin 8,
      (Ioo massLower massUpper : Set Real) =ᵐ[massCoordinateLaw]
        (Set.univ : Set Real) := by
    intro i
    filter_upwards [massCoordinate_mem_openSupport_ae] with mass hmass
    exact propext ⟨fun _ => trivial, fun _ => hmass⟩
  have hpi :
      Set.univ.pi (fun _ : Fin 8 => Ioo massLower massUpper) =ᵐ[
        Measure.pi (fun _ : Fin 8 => massCoordinateLaw)]
      Set.univ.pi (fun _ : Fin 8 => (Set.univ : Set Real)) :=
    Measure.ae_eq_set_pi (fun i _hi => hcoordinate i)
  change ∀ᵐ x ∂Measure.pi (fun _ : Fin 8 => massCoordinateLaw),
    x ∈ fullEightMassSupportInterior
  filter_upwards [hpi] with x hx
  have hxpi :
      x ∈ Set.univ.pi (fun _ : Fin 8 => Ioo massLower massUpper) :=
    by
      change (Set.univ.pi (fun _ : Fin 8 =>
        Ioo massLower massUpper)) x
      exact Eq.mpr hx (fun i _hi => Set.mem_univ (x i))
  simpa [fullEightMassSupportInterior] using hxpi

/-- On the physical mass cube, the inverse-mass coordinates of the actual
eight-site configuration are the coordinatewise inverses of the raw iid
mass vector. -/
theorem inverseMassCoordinates_fullEightMassConfig
    {x : EightMassVector} (hx : ∀ i, x i ∈ massSupport) :
    inverseMassCoordinates (fullEightMassConfig x) =
      coordinatewiseInv x := by
  ext k
  simp only [coordinatewiseInv_apply]
  change (clippedMass (x k))⁻¹ = (x k)⁻¹
  rw [clippedMass_eq_self (hx k)]

/-- The actual full-eight harmonic spectrum is simple almost surely.  This
is a finite-law specialization of the already verified resultant argument,
not an additional random-spectrum assumption. -/
theorem finiteMassLaw_eight_simpleOrderedSpectrum_ae :
    ∀ᵐ x ∂(finiteMassLaw 8),
      SimpleOrderedSpectrum (fullEightHarmonic x) := by
  have hsupport : ∀ᵐ x ∂(finiteMassLaw 8),
      ∀ i, x i ∈ massSupport := by
    filter_upwards [finiteMassLaw_eight_mem_fullEightMassSupportInterior_ae]
      with x hx
    intro i
    exact ⟨(hx i).1.le, (hx i).2.le⟩
  have hpolynomial : ∀ᵐ x ∂(finiteMassLaw 8),
      MvPolynomial.eval (coordinatewiseInv x)
        (symbolicRepeatedRootCertificate (N := 8)) ≠ 0 := by
    have hnull := finiteMassLaw_zeroSet_eval_coordinatewiseInv
      (symbolicRepeatedRootCertificate (N := 8))
      (symbolicRepeatedRootCertificate_ne_zero (N := 8) (by norm_num))
    have hnot := measure_eq_zero_iff_ae_notMem.mp hnull
    filter_upwards [hnot] with x hx
    simpa using hx
  filter_upwards [hsupport, hpolynomial] with x hsupport hpolynomial
  apply simpleOrderedSpectrum_of_not_orderedPositiveDuplicate
  intro hduplicate
  have hrepeated :=
    repeatedPositiveHarmonic_of_orderedPositiveDuplicate
      (fullEightMassConfig x) hduplicate
  have hcertificate :=
    certificate_vanishes_of_repeatedPositiveHarmonic
      (fullEightMassConfig x) hrepeated
  rw [inverseMassCoordinates_fullEightMassConfig hsupport] at hcertificate
  exact hpolynomial hcertificate

/-- On the physical simple-spectrum locus, the selected partial-Jacobian
minor is nonzero exactly when the actual selected projector minor is nonzero.
-/
theorem actualEightSiteSelectedPartialJacobian_det_ne_zero_iff_projectorMinor
    {x : EightMassVector} (hx : x ∈ fullEightMassSupportInterior)
    (hsimple : SimpleOrderedSpectrum (fullEightHarmonic x)) :
    (actualEightSiteSelectedPartialJacobian x).det ≠ 0 ↔
      actualEightSiteSelectedProjectorMinor x ≠ 0 := by
  have htriple : (splitEightMass x).2 ∈ interior iidMassTripleSupport := by
    simpa [splitEightMass, splitEightMassLinearEquiv,
      actualEightSiteSelectedMassTriple] using
      actualEightSiteSelectedMassTriple_mem_interior hx
  have hharmonic :
      threeMassHarmonicHermitian (fullEightMassConfig x)
        (actualEightSiteSelectedSites 0)
        (actualEightSiteSelectedSites 1)
        (actualEightSiteSelectedSites 2) (splitEightMass x).2 =
        fullEightHarmonic x := by
    simpa [splitEightMass, splitEightMassLinearEquiv,
      actualEightSiteSelectedMassTriple] using
      threeMassHarmonic_actualEightSiteSelectedMassTriple hx
  have hpositive : ∀ r, 0 < orderedEigenvalue
      (threeMassHarmonicHermitian (fullEightMassConfig x)
        (actualEightSiteSelectedSites 0)
        (actualEightSiteSelectedSites 1)
        (actualEightSiteSelectedSites 2) (splitEightMass x).2)
      (actualEightSiteDecayModes r) := by
    intro r
    rw [hharmonic]
    exact Real.sqrt_pos.mp (actualEightSiteSelectedFrequency_pos x r)
  have hsimpleThree : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian (fullEightMassConfig x)
        (actualEightSiteSelectedSites 0)
        (actualEightSiteSelectedSites 1)
        (actualEightSiteSelectedSites 2) (splitEightMass x).2) := by
    rw [hharmonic]
    exact hsimple
  have hfactor :=
    actualThreeMassLiftedFrequencyJacobian_det_ne_zero_iff_projectorWeight
      (fullEightMassConfig x)
      (by decide : actualEightSiteSelectedSites 1 ≠
        actualEightSiteSelectedSites 0)
      (by decide : actualEightSiteSelectedSites 2 ≠
        actualEightSiteSelectedSites 0)
      (by decide : actualEightSiteSelectedSites 2 ≠
        actualEightSiteSelectedSites 1)
      actualEightSiteDecaySign actualEightSiteDecayModes htriple
      hsimpleThree hpositive
  have hprojector :
      actualThreeMassProjectorWeightMatrix (fullEightMassConfig x)
        (actualEightSiteSelectedSites 0)
        (actualEightSiteSelectedSites 1)
        (actualEightSiteSelectedSites 2)
        actualEightSiteDecayModes (splitEightMass x).2 =
      orderedProjectorWeightMatrix (fullEightDualHarmonic x)
        actualEightSiteDecayModes
        (fun s => cycleMassPerturbationVector
          (actualEightSiteSelectedSites s)) := by
    simpa [splitEightMass, splitEightMassLinearEquiv,
      actualEightSiteSelectedMassTriple] using
      actualThreeMassProjectorWeightMatrix_selected_eq hx
  rw [hprojector] at hfactor
  simpa [actualEightSiteSelectedPartialJacobian,
    actualEightSiteSelectedProjectorMinor] using hfactor

/-- The exact missing algebraic input.  A certificate consists of one
nonzero polynomial in the eight inverse raw masses whose zero set contains
the selected-projector singular locus on the physical simple-spectrum set.
Adjugate/resultant elimination is expected to produce such a polynomial,
but its existence is deliberately not postulated by this module. -/
structure FullEightSelectedProjectorMinorPolynomialCertificate where
  polynomial : MvPolynomial (Fin 8) Real
  polynomial_ne_zero : polynomial ≠ 0
  vanishes_of_projectorMinor_eq_zero :
    ∀ x : EightMassVector,
      x ∈ fullEightMassSupportInterior →
      SimpleOrderedSpectrum (fullEightHarmonic x) →
      actualEightSiteSelectedProjectorMinor x = 0 →
      MvPolynomial.eval (coordinatewiseInv x) polynomial = 0

/-- A genuine elimination certificate makes the selected regular locus
almost sure under the actual eightfold iid mass law. -/
theorem fullEightSelectedJacobianRegularSet_ae_of_polynomialCertificate
    (certificate : FullEightSelectedProjectorMinorPolynomialCertificate) :
    ∀ᵐ x ∂(finiteMassLaw 8),
      x ∈ fullEightSelectedJacobianRegularSet := by
  have hpolynomial : ∀ᵐ x ∂(finiteMassLaw 8),
      MvPolynomial.eval (coordinatewiseInv x) certificate.polynomial ≠ 0 := by
    have hnull := finiteMassLaw_zeroSet_eval_coordinatewiseInv
      certificate.polynomial certificate.polynomial_ne_zero
    have hnot := measure_eq_zero_iff_ae_notMem.mp hnull
    filter_upwards [hnot] with x hx
    simpa using hx
  filter_upwards [finiteMassLaw_eight_mem_fullEightMassSupportInterior_ae,
    finiteMassLaw_eight_simpleOrderedSpectrum_ae, hpolynomial]
      with x hinterior hsimple hpolynomial
  have hprojector : actualEightSiteSelectedProjectorMinor x ≠ 0 := by
    intro hzero
    exact hpolynomial
      (certificate.vanishes_of_projectorMinor_eq_zero
        x hinterior hsimple hzero)
  have hJacobian : (actualEightSiteSelectedPartialJacobian x).det ≠ 0 :=
    (actualEightSiteSelectedPartialJacobian_det_ne_zero_iff_projectorMinor
      hinterior hsimple).mpr hprojector
  exact ⟨hinterior, hsimple,
    (fun r => Real.sqrt_pos.mp (actualEightSiteSelectedFrequency_pos x r)),
    hJacobian⟩

/-- Conditional closure of the exact irregular mass. -/
theorem fullEightSelectedJacobianIrregularMass_eq_zero_of_polynomialCertificate
    (certificate : FullEightSelectedProjectorMinorPolynomialCertificate) :
    fullEightSelectedJacobianIrregularMass = 0 :=
  fullEightSelectedJacobianIrregularMass_eq_zero_iff_regular_ae.mpr
    (fullEightSelectedJacobianRegularSet_ae_of_polynomialCertificate
      certificate)

/-- Conditional epsilon-level small-ball theorem obtained from the
elimination certificate. -/
theorem exists_finiteLevelCoefficient_actualEightSite_fullIID_smallBallUpper_of_polynomialCertificate
    (certificate : FullEightSelectedProjectorMinorPolynomialCertificate)
    {epsilon : ENNReal} (hepsilon : 0 < epsilon) :
    ∃ n : Nat, ∃ coefficient : ENNReal,
      coefficient ≠ (∞ : ENNReal) ∧
      fullEightSelectedJacobianBadMass n < epsilon ∧
      ∀ delta : Real, 0 ≤ delta →
        (Measure.map selectedFirstEightMassEquiv (finiteMassLaw 8))
            {point |
              |selectedFirstActualEightSiteMismatch point| ≤ delta} ≤
          coefficient * ENNReal.ofReal (2 * delta) + epsilon := by
  exact
    exists_finiteLevelCoefficient_actualEightSite_fullIID_smallBallUpper_of_irregularMass_eq_zero
      (fullEightSelectedJacobianIrregularMass_eq_zero_of_polynomialCertificate
        certificate)
      hepsilon

end

end ArchonPhysics.ActualEightSiteFullIIDIrregularMassPolynomialReduction
