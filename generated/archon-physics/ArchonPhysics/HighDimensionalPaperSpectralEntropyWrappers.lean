import ArchonPhysics.HighDimensionalPaperSpectralEntropyScaling

/-!
# Explicit lattice-family wrappers for the 2024 all-mode criterion

These endpoints retain an arbitrary finite mode type.  The lattice tag fixes
the paper dimension and threshold metadata: hexagonal/FCC use 0.65, while
square/simple-cubic use 0.95.  All paper-matched wrappers require fixed
boundary conditions.  DOI: `10.1103/PhysRevLett.132.217102`.
-/

namespace ArchonPhysics.DimensionalPaperSpectralEntropyScaling

open Filter MeasureTheory Topology
open ArchonPhysics.HamiltonianScaling
open ArchonPhysics.ThermalizationTransfer

noncomputable section

section GeneralDegree

variable {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
  [IsProbabilityMeasure P]
variable (mu : Real) (sizeCutoff : Real -> Nat) (lower upper : Real)
variable (lambda : Real) (n : Nat) (s : AdmissibleJointLimit sizeCutoff)
variable (epsilon : Nat -> Real)

/-- Fixed-boundary hexagonal 2D, all-mode xi threshold 0.65, general degree. -/
theorem hexagonal2DFullModeXi_energyDensity_corollary
    (source : HighDimensionalModalEnergySource .hexagonal2D Omega)
    (hfixed : source.IsPaperMatched) (hmu : 0 <= mu ∧ mu < 1)
    (h : HighProbabilityG2Bounds P (source.equilibrationTime mu)
      sizeCutoff lower upper)
    (hn : 3 <= n) (hlambda : lambda ≠ 0)
    (hside : forall j, 0 < s.systemSize j)
    (hepsilon : forall j, 0 < epsilon j)
    (hcoupling : forall j,
      s.coupling j = effectiveCoupling lambda (epsilon j) n) :
    Tendsto
      (fun j => P (EnergyDensityThermalization.energyDensityWindowEvent
        (source.equilibrationTime mu) lower upper
        (s.systemSize j) lambda (epsilon j) n))
      atTop (nhds 1) :=
  highDimensionalFamilyXi_energyDensity_corollary P source hfixed mu hmu
    sizeCutoff lower upper h lambda n hn hlambda s hside epsilon hepsilon
      hcoupling

/-- Fixed-boundary square 2D, all-mode xi threshold 0.95, general degree. -/
theorem square2DFullModeXi_energyDensity_corollary
    (source : HighDimensionalModalEnergySource .square2D Omega)
    (hfixed : source.IsPaperMatched) (hmu : 0 <= mu ∧ mu < 1)
    (h : HighProbabilityG2Bounds P (source.equilibrationTime mu)
      sizeCutoff lower upper)
    (hn : 3 <= n) (hlambda : lambda ≠ 0)
    (hside : forall j, 0 < s.systemSize j)
    (hepsilon : forall j, 0 < epsilon j)
    (hcoupling : forall j,
      s.coupling j = effectiveCoupling lambda (epsilon j) n) :
    Tendsto
      (fun j => P (EnergyDensityThermalization.energyDensityWindowEvent
        (source.equilibrationTime mu) lower upper
        (s.systemSize j) lambda (epsilon j) n))
      atTop (nhds 1) :=
  highDimensionalFamilyXi_energyDensity_corollary P source hfixed mu hmu
    sizeCutoff lower upper h lambda n hn hlambda s hside epsilon hepsilon
      hcoupling

/-- Fixed-boundary FCC 3D, all-mode xi threshold 0.65, general degree. -/
theorem faceCenteredCubic3DFullModeXi_energyDensity_corollary
    (source : HighDimensionalModalEnergySource .faceCenteredCubic3D Omega)
    (hfixed : source.IsPaperMatched) (hmu : 0 <= mu ∧ mu < 1)
    (h : HighProbabilityG2Bounds P (source.equilibrationTime mu)
      sizeCutoff lower upper)
    (hn : 3 <= n) (hlambda : lambda ≠ 0)
    (hside : forall j, 0 < s.systemSize j)
    (hepsilon : forall j, 0 < epsilon j)
    (hcoupling : forall j,
      s.coupling j = effectiveCoupling lambda (epsilon j) n) :
    Tendsto
      (fun j => P (EnergyDensityThermalization.energyDensityWindowEvent
        (source.equilibrationTime mu) lower upper
        (s.systemSize j) lambda (epsilon j) n))
      atTop (nhds 1) :=
  highDimensionalFamilyXi_energyDensity_corollary P source hfixed mu hmu
    sizeCutoff lower upper h lambda n hn hlambda s hside epsilon hepsilon
      hcoupling

/-- Fixed-boundary simple-cubic 3D, all-mode xi threshold 0.95, general degree. -/
theorem simpleCubic3DFullModeXi_energyDensity_corollary
    (source : HighDimensionalModalEnergySource .simpleCubic3D Omega)
    (hfixed : source.IsPaperMatched) (hmu : 0 <= mu ∧ mu < 1)
    (h : HighProbabilityG2Bounds P (source.equilibrationTime mu)
      sizeCutoff lower upper)
    (hn : 3 <= n) (hlambda : lambda ≠ 0)
    (hside : forall j, 0 < s.systemSize j)
    (hepsilon : forall j, 0 < epsilon j)
    (hcoupling : forall j,
      s.coupling j = effectiveCoupling lambda (epsilon j) n) :
    Tendsto
      (fun j => P (EnergyDensityThermalization.energyDensityWindowEvent
        (source.equilibrationTime mu) lower upper
        (s.systemSize j) lambda (epsilon j) n))
      atTop (nhds 1) :=
  highDimensionalFamilyXi_energyDensity_corollary P source hfixed mu hmu
    sizeCutoff lower upper h lambda n hn hlambda s hside epsilon hepsilon
      hcoupling

end GeneralDegree

section CubicQuartic

variable {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
  [IsProbabilityMeasure P]
variable (mu : Real) (sizeCutoff : Real -> Nat) (lower upper lambda : Real)
variable (s : AdmissibleJointLimit sizeCutoff) (epsilon : Nat -> Real)

/-- Hexagonal 2D cubic-leading/Lennard-Jones endpoint, scale
`lambda^-2 epsilon^-1`. -/
theorem hexagonal2DFullModeXi_cubic_energyDensity_corollary
    (source : HighDimensionalModalEnergySource .hexagonal2D Omega)
    (hfixed : source.IsPaperMatched) (hmu : 0 <= mu ∧ mu < 1)
    (h : HighProbabilityG2Bounds P (source.equilibrationTime mu)
      sizeCutoff lower upper)
    (hlambda : lambda ≠ 0) (hside : forall j, 0 < s.systemSize j)
    (hepsilon : forall j, 0 < epsilon j)
    (hcoupling : forall j,
      s.coupling j = effectiveCoupling lambda (epsilon j) 3) :
    Tendsto
      (fun j => P (highDimensionalCubicWindowEvent
        (source.equilibrationTime mu) lower upper
        (s.systemSize j) lambda (epsilon j)))
      atTop (nhds 1) :=
  highDimensionalFamilyXi_cubic_energyDensity_corollary P source hfixed mu
    hmu sizeCutoff lower upper h lambda hlambda s hside epsilon hepsilon
      hcoupling

/-- Hexagonal 2D quartic endpoint, scale `lambda^-2 epsilon^-2`. -/
theorem hexagonal2DFullModeXi_quartic_energyDensity_corollary
    (source : HighDimensionalModalEnergySource .hexagonal2D Omega)
    (hfixed : source.IsPaperMatched) (hmu : 0 <= mu ∧ mu < 1)
    (h : HighProbabilityG2Bounds P (source.equilibrationTime mu)
      sizeCutoff lower upper)
    (hlambda : lambda ≠ 0) (hside : forall j, 0 < s.systemSize j)
    (hepsilon : forall j, 0 < epsilon j)
    (hcoupling : forall j,
      s.coupling j = effectiveCoupling lambda (epsilon j) 4) :
    Tendsto
      (fun j => P (highDimensionalQuarticWindowEvent
        (source.equilibrationTime mu) lower upper
        (s.systemSize j) lambda (epsilon j)))
      atTop (nhds 1) :=
  highDimensionalFamilyXi_quartic_energyDensity_corollary P source hfixed mu
    hmu sizeCutoff lower upper h lambda hlambda s hside epsilon hepsilon
      hcoupling

/-- Square 2D cubic-leading/Lennard-Jones endpoint, scale
`lambda^-2 epsilon^-1`. -/
theorem square2DFullModeXi_cubic_energyDensity_corollary
    (source : HighDimensionalModalEnergySource .square2D Omega)
    (hfixed : source.IsPaperMatched) (hmu : 0 <= mu ∧ mu < 1)
    (h : HighProbabilityG2Bounds P (source.equilibrationTime mu)
      sizeCutoff lower upper)
    (hlambda : lambda ≠ 0) (hside : forall j, 0 < s.systemSize j)
    (hepsilon : forall j, 0 < epsilon j)
    (hcoupling : forall j,
      s.coupling j = effectiveCoupling lambda (epsilon j) 3) :
    Tendsto
      (fun j => P (highDimensionalCubicWindowEvent
        (source.equilibrationTime mu) lower upper
        (s.systemSize j) lambda (epsilon j)))
      atTop (nhds 1) :=
  highDimensionalFamilyXi_cubic_energyDensity_corollary P source hfixed mu
    hmu sizeCutoff lower upper h lambda hlambda s hside epsilon hepsilon
      hcoupling

/-- Square 2D quartic endpoint, scale `lambda^-2 epsilon^-2`. -/
theorem square2DFullModeXi_quartic_energyDensity_corollary
    (source : HighDimensionalModalEnergySource .square2D Omega)
    (hfixed : source.IsPaperMatched) (hmu : 0 <= mu ∧ mu < 1)
    (h : HighProbabilityG2Bounds P (source.equilibrationTime mu)
      sizeCutoff lower upper)
    (hlambda : lambda ≠ 0) (hside : forall j, 0 < s.systemSize j)
    (hepsilon : forall j, 0 < epsilon j)
    (hcoupling : forall j,
      s.coupling j = effectiveCoupling lambda (epsilon j) 4) :
    Tendsto
      (fun j => P (highDimensionalQuarticWindowEvent
        (source.equilibrationTime mu) lower upper
        (s.systemSize j) lambda (epsilon j)))
      atTop (nhds 1) :=
  highDimensionalFamilyXi_quartic_energyDensity_corollary P source hfixed mu
    hmu sizeCutoff lower upper h lambda hlambda s hside epsilon hepsilon
      hcoupling

/-- FCC 3D cubic-leading/Lennard-Jones endpoint, scale
`lambda^-2 epsilon^-1`. -/
theorem faceCenteredCubic3DFullModeXi_cubic_energyDensity_corollary
    (source : HighDimensionalModalEnergySource .faceCenteredCubic3D Omega)
    (hfixed : source.IsPaperMatched) (hmu : 0 <= mu ∧ mu < 1)
    (h : HighProbabilityG2Bounds P (source.equilibrationTime mu)
      sizeCutoff lower upper)
    (hlambda : lambda ≠ 0) (hside : forall j, 0 < s.systemSize j)
    (hepsilon : forall j, 0 < epsilon j)
    (hcoupling : forall j,
      s.coupling j = effectiveCoupling lambda (epsilon j) 3) :
    Tendsto
      (fun j => P (highDimensionalCubicWindowEvent
        (source.equilibrationTime mu) lower upper
        (s.systemSize j) lambda (epsilon j)))
      atTop (nhds 1) :=
  highDimensionalFamilyXi_cubic_energyDensity_corollary P source hfixed mu
    hmu sizeCutoff lower upper h lambda hlambda s hside epsilon hepsilon
      hcoupling

/-- FCC 3D quartic endpoint, scale `lambda^-2 epsilon^-2`. -/
theorem faceCenteredCubic3DFullModeXi_quartic_energyDensity_corollary
    (source : HighDimensionalModalEnergySource .faceCenteredCubic3D Omega)
    (hfixed : source.IsPaperMatched) (hmu : 0 <= mu ∧ mu < 1)
    (h : HighProbabilityG2Bounds P (source.equilibrationTime mu)
      sizeCutoff lower upper)
    (hlambda : lambda ≠ 0) (hside : forall j, 0 < s.systemSize j)
    (hepsilon : forall j, 0 < epsilon j)
    (hcoupling : forall j,
      s.coupling j = effectiveCoupling lambda (epsilon j) 4) :
    Tendsto
      (fun j => P (highDimensionalQuarticWindowEvent
        (source.equilibrationTime mu) lower upper
        (s.systemSize j) lambda (epsilon j)))
      atTop (nhds 1) :=
  highDimensionalFamilyXi_quartic_energyDensity_corollary P source hfixed mu
    hmu sizeCutoff lower upper h lambda hlambda s hside epsilon hepsilon
      hcoupling

/-- Simple-cubic 3D cubic-leading/Lennard-Jones endpoint, scale
`lambda^-2 epsilon^-1`. -/
theorem simpleCubic3DFullModeXi_cubic_energyDensity_corollary
    (source : HighDimensionalModalEnergySource .simpleCubic3D Omega)
    (hfixed : source.IsPaperMatched) (hmu : 0 <= mu ∧ mu < 1)
    (h : HighProbabilityG2Bounds P (source.equilibrationTime mu)
      sizeCutoff lower upper)
    (hlambda : lambda ≠ 0) (hside : forall j, 0 < s.systemSize j)
    (hepsilon : forall j, 0 < epsilon j)
    (hcoupling : forall j,
      s.coupling j = effectiveCoupling lambda (epsilon j) 3) :
    Tendsto
      (fun j => P (highDimensionalCubicWindowEvent
        (source.equilibrationTime mu) lower upper
        (s.systemSize j) lambda (epsilon j)))
      atTop (nhds 1) :=
  highDimensionalFamilyXi_cubic_energyDensity_corollary P source hfixed mu
    hmu sizeCutoff lower upper h lambda hlambda s hside epsilon hepsilon
      hcoupling

/-- Simple-cubic 3D quartic endpoint, scale `lambda^-2 epsilon^-2`. -/
theorem simpleCubic3DFullModeXi_quartic_energyDensity_corollary
    (source : HighDimensionalModalEnergySource .simpleCubic3D Omega)
    (hfixed : source.IsPaperMatched) (hmu : 0 <= mu ∧ mu < 1)
    (h : HighProbabilityG2Bounds P (source.equilibrationTime mu)
      sizeCutoff lower upper)
    (hlambda : lambda ≠ 0) (hside : forall j, 0 < s.systemSize j)
    (hepsilon : forall j, 0 < epsilon j)
    (hcoupling : forall j,
      s.coupling j = effectiveCoupling lambda (epsilon j) 4) :
    Tendsto
      (fun j => P (highDimensionalQuarticWindowEvent
        (source.equilibrationTime mu) lower upper
        (s.systemSize j) lambda (epsilon j)))
      atTop (nhds 1) :=
  highDimensionalFamilyXi_quartic_energyDensity_corollary P source hfixed mu
    hmu sizeCutoff lower upper h lambda hlambda s hside epsilon hepsilon
      hcoupling

end CubicQuartic

end

end ArchonPhysics.DimensionalPaperSpectralEntropyScaling
