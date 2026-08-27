import ArchonPhysics.ActualThreeMassLiftedSpectralChart
import ArchonPhysics.FiniteMeasureVanishingErrorSmallBallWeakLimit
import ArchonPhysics.RepeatedParentChildMismatchSmallBall
import ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

/-!
# Mismatch small balls from an actual lifted density bound

The actual three-mass chart has coordinates
`((omega_child1, omega_child2), mismatch)`.  This file records the elementary
but essential coarea endpoint: if the good part of a lifted measure has a
three-dimensional Lebesgue density ceiling and its two child frequencies lie
in a common bounded band, then its mismatch marginal has a linear small-ball
bound.  An arbitrary bad part is retained as its exact unweighted mass.

For zero-atom questions this is the correct bad term: unlike finite-time
sinc-squared estimates, the raw mismatch marginal does not amplify the bad
set by a factor depending on time.

The final theorems also prove that the genuine random-mass harmonic chart has
the required child-frequency support `[0, sqrt 5]`, provided the frozen
environment has masses in the iid support.  No Jacobian nondegeneracy is
asserted here.  In particular, this module does not use the false pointwise
claim that every distinct-mode projector-weight minor is nonzero.
-/

namespace ArchonPhysics.ActualLiftedMismatchSmallBall

open ArchonPhysics
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.FiniteMeasureVanishingErrorSmallBallWeakLimit
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

local instance pairVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) :=
  Measure.prod.instIsAddHaarMeasure _ _

local instance tripleVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure MassTriple) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- The common square containing the two child frequencies. -/
def childFrequencySquare (ceiling : Real) : Set (Real × Real) :=
  Set.Icc 0 ceiling ×ˢ Set.Icc 0 ceiling

/-- The corresponding cylinder in lifted `(child pair, mismatch)` space. -/
def liftedChildFrequencyCylinder (ceiling : Real) : Set MassTriple :=
  childFrequencySquare ceiling ×ˢ Set.univ

/-- The bounded lifted slab over a symmetric mismatch window. -/
def liftedMismatchSlab (ceiling delta : Real) : Set MassTriple :=
  childFrequencySquare ceiling ×ˢ absoluteMismatchSublevel delta

theorem measurableSet_childFrequencySquare (ceiling : Real) :
    MeasurableSet (childFrequencySquare ceiling) :=
  measurableSet_Icc.prod measurableSet_Icc

theorem measurableSet_liftedChildFrequencyCylinder (ceiling : Real) :
    MeasurableSet (liftedChildFrequencyCylinder ceiling) :=
  (measurableSet_childFrequencySquare ceiling).prod MeasurableSet.univ

theorem measurableSet_liftedMismatchSlab (ceiling delta : Real) :
    MeasurableSet (liftedMismatchSlab ceiling delta) :=
  (measurableSet_childFrequencySquare ceiling).prod
    (measurableSet_absoluteMismatchSublevel delta)

theorem absoluteMismatchSublevel_eq_Icc (delta : Real) :
    absoluteMismatchSublevel delta = Set.Icc (-delta) delta := by
  ext x
  simp [absoluteMismatchSublevel, abs_le]

/-- Exact planar volume of the common child-frequency square. -/
theorem volume_childFrequencySquare (ceiling : Real) :
    (volume : Measure (Real × Real)) (childFrequencySquare ceiling) =
      ENNReal.ofReal ceiling * ENNReal.ofReal ceiling := by
  change ((volume : Measure Real).prod (volume : Measure Real))
      (Set.Icc 0 ceiling ×ˢ Set.Icc 0 ceiling) = _
  rw [Measure.prod_prod]
  simp only [Real.volume_Icc, sub_zero]

/-- Exact one-dimensional volume of a nonempty symmetric mismatch window. -/
theorem volume_absoluteMismatchSublevel
    (delta : Real) :
    (volume : Measure Real) (absoluteMismatchSublevel delta) =
      ENNReal.ofReal (2 * delta) := by
  rw [absoluteMismatchSublevel_eq_Icc]
  rw [Real.volume_Icc]
  congr 1
  ring

/-- Exact volume of the child-frequency/mismatch slab. -/
theorem volume_liftedMismatchSlab
    (ceiling : Real) {delta : Real} (_hdelta : 0 ≤ delta) :
    (volume : Measure MassTriple) (liftedMismatchSlab ceiling delta) =
      (ENNReal.ofReal ceiling * ENNReal.ofReal ceiling) *
        ENNReal.ofReal (2 * delta) := by
  change ((volume : Measure (Real × Real)).prod (volume : Measure Real))
      (childFrequencySquare ceiling ×ˢ absoluteMismatchSublevel delta) = _
  rw [Measure.prod_prod]
  rw [volume_childFrequencySquare,
    volume_absoluteMismatchSublevel delta]

/-- Projecting a bounded lifted density to the mismatch coordinate gives an
upper Lebesgue-density bound on every measurable target set. -/
theorem map_snd_apply_le_of_le_smul_volume_of_ae_mem_childCylinder
    (lifted : Measure MassTriple) (C : ENNReal) (ceiling : Real)
    (hdensity : lifted ≤ C • (volume : Measure MassTriple))
    (hchild : ∀ᵐ point ∂lifted,
      point ∈ liftedChildFrequencyCylinder ceiling)
    {target : Set Real} (htarget : MeasurableSet target) :
    Measure.map Prod.snd lifted target ≤
      C * (ENNReal.ofReal ceiling * ENNReal.ofReal ceiling) *
        (volume : Measure Real) target := by
  rw [Measure.map_apply measurable_snd htarget]
  have hrestrict :
      lifted.restrict (liftedChildFrequencyCylinder ceiling) = lifted :=
    Measure.restrict_eq_self_of_ae_mem hchild
  rw [← hrestrict,
    Measure.restrict_apply (htarget.preimage measurable_snd)]
  have hintersection :
      Prod.snd ⁻¹' target ∩ liftedChildFrequencyCylinder ceiling =
        childFrequencySquare ceiling ×ˢ target := by
    ext point
    simp [liftedChildFrequencyCylinder, and_comm]
  rw [hintersection]
  calc
    lifted (childFrequencySquare ceiling ×ˢ target) ≤
        (C • (volume : Measure MassTriple))
          (childFrequencySquare ceiling ×ˢ target) :=
      hdensity (childFrequencySquare ceiling ×ˢ target)
    _ = C * (volume : Measure MassTriple)
          (childFrequencySquare ceiling ×ˢ target) := by
      simp only [Measure.smul_apply, smul_eq_mul]
    _ = C * (ENNReal.ofReal ceiling * ENNReal.ofReal ceiling) *
          (volume : Measure Real) target := by
      change C * ((volume : Measure (Real × Real)).prod
        (volume : Measure Real))
          (childFrequencySquare ceiling ×ˢ target) = _
      rw [Measure.prod_prod, volume_childFrequencySquare]
      ring

/-- Arbitrary-target good/bad form.  This is the finite-volume approximate
L-infinity density estimate whose uniform version can pass to a weak
thermodynamic cluster. -/
theorem map_snd_good_add_bad_apply_le
    (goodLifted badLifted : Measure MassTriple)
    (C : ENNReal) (ceiling : Real)
    (hgoodDensity : goodLifted ≤ C • (volume : Measure MassTriple))
    (hgoodChild : ∀ᵐ point ∂goodLifted,
      point ∈ liftedChildFrequencyCylinder ceiling)
    {target : Set Real} (htarget : MeasurableSet target) :
    Measure.map Prod.snd (goodLifted + badLifted) target ≤
      C * (ENNReal.ofReal ceiling * ENNReal.ofReal ceiling) *
          (volume : Measure Real) target + badLifted Set.univ := by
  rw [Measure.map_add goodLifted badLifted measurable_snd,
    Measure.add_apply]
  exact add_le_add
    (map_snd_apply_le_of_le_smul_volume_of_ae_mem_childCylinder
      goodLifted C ceiling hgoodDensity hgoodChild htarget)
    (calc
      Measure.map Prod.snd badLifted target ≤
          Measure.map Prod.snd badLifted Set.univ :=
        measure_mono (subset_univ _)
      _ = badLifted Set.univ := by
        rw [Measure.map_apply measurable_snd MeasurableSet.univ]
        simp)

/-- A bounded three-dimensional lifted density has a linear mismatch
small-ball bound once the two child coordinates lie in a bounded square. -/
theorem map_snd_absoluteMismatchSublevel_le_of_le_smul_volume_of_ae_mem_childCylinder
    (lifted : Measure MassTriple) (C : ENNReal) (ceiling : Real)
    (hdensity : lifted ≤ C • (volume : Measure MassTriple))
    (hchild : ∀ᵐ point ∂lifted,
      point ∈ liftedChildFrequencyCylinder ceiling)
    {delta : Real} (hdelta : 0 ≤ delta) :
    Measure.map Prod.snd lifted (absoluteMismatchSublevel delta) ≤
      C * (ENNReal.ofReal ceiling * ENNReal.ofReal ceiling) *
        ENNReal.ofReal (2 * delta) := by
  have hwindow : MeasurableSet (absoluteMismatchSublevel delta) :=
    measurableSet_absoluteMismatchSublevel delta
  rw [Measure.map_apply measurable_snd hwindow]
  have hrestrict :
      lifted.restrict (liftedChildFrequencyCylinder ceiling) = lifted :=
    Measure.restrict_eq_self_of_ae_mem hchild
  rw [← hrestrict,
    Measure.restrict_apply (hwindow.preimage measurable_snd)]
  have hintersection :
      Prod.snd ⁻¹' absoluteMismatchSublevel delta ∩
          liftedChildFrequencyCylinder ceiling =
        liftedMismatchSlab ceiling delta := by
    ext point
    simp [liftedChildFrequencyCylinder, liftedMismatchSlab, and_comm]
  rw [hintersection]
  calc
    lifted (liftedMismatchSlab ceiling delta) ≤
        (C • (volume : Measure MassTriple))
          (liftedMismatchSlab ceiling delta) :=
      hdensity (liftedMismatchSlab ceiling delta)
    _ = C * (volume : Measure MassTriple)
          (liftedMismatchSlab ceiling delta) := by
      simp only [Measure.smul_apply, smul_eq_mul]
    _ = C * (ENNReal.ofReal ceiling * ENNReal.ofReal ceiling) *
          ENNReal.ofReal (2 * delta) := by
      rw [volume_liftedMismatchSlab ceiling hdelta]
      ring

/-- Good/bad form of the raw mismatch small-ball estimate.  The exceptional
contribution is bounded by the total mass of the bad lifted measure. -/
theorem map_snd_good_add_bad_absoluteMismatchSublevel_le
    (goodLifted badLifted : Measure MassTriple)
    (C : ENNReal) (ceiling : Real)
    (hgoodDensity : goodLifted ≤ C • (volume : Measure MassTriple))
    (hgoodChild : ∀ᵐ point ∂goodLifted,
      point ∈ liftedChildFrequencyCylinder ceiling)
    {delta : Real} (hdelta : 0 ≤ delta) :
    Measure.map Prod.snd (goodLifted + badLifted)
        (absoluteMismatchSublevel delta) ≤
      C * (ENNReal.ofReal ceiling * ENNReal.ofReal ceiling) *
          ENNReal.ofReal (2 * delta) + badLifted Set.univ := by
  have hwindow : MeasurableSet (absoluteMismatchSublevel delta) :=
    measurableSet_absoluteMismatchSublevel delta
  rw [Measure.map_add goodLifted badLifted measurable_snd,
    Measure.add_apply]
  exact add_le_add
    (map_snd_absoluteMismatchSublevel_le_of_le_smul_volume_of_ae_mem_childCylinder
      goodLifted C ceiling hgoodDensity hgoodChild hdelta)
    (calc
      Measure.map Prod.snd badLifted (absoluteMismatchSublevel delta) ≤
          Measure.map Prod.snd badLifted Set.univ :=
        measure_mono (subset_univ _)
      _ = badLifted Set.univ := by
        rw [Measure.map_apply measurable_snd MeasurableSet.univ]
        simp)

/-- Real-valued form used by finite-measure weak-limit small-ball theorems. -/
theorem map_snd_good_add_bad_absoluteMismatchSublevel_toReal_le
    (goodLifted badLifted : Measure MassTriple)
    (C : ENNReal) (hC : C ≠ ∞) (ceiling : Real) (hceiling : 0 ≤ ceiling)
    (hgoodDensity : goodLifted ≤ C • (volume : Measure MassTriple))
    (hgoodChild : ∀ᵐ point ∂goodLifted,
      point ∈ liftedChildFrequencyCylinder ceiling)
    (hbadFinite : badLifted Set.univ ≠ ∞)
    {delta : Real} (hdelta : 0 ≤ delta) :
    (Measure.map Prod.snd (goodLifted + badLifted)
        (absoluteMismatchSublevel delta)).toReal ≤
      (2 * C.toReal * ceiling ^ 2) * delta +
        (badLifted Set.univ).toReal := by
  have hENN := map_snd_good_add_bad_absoluteMismatchSublevel_le
    goodLifted badLifted C ceiling hgoodDensity hgoodChild hdelta
  have hregularFinite :
      C * (ENNReal.ofReal ceiling * ENNReal.ofReal ceiling) *
          ENNReal.ofReal (2 * delta) ≠ ∞ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hC
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))
      ENNReal.ofReal_ne_top
  have hupperFinite :
      C * (ENNReal.ofReal ceiling * ENNReal.ofReal ceiling) *
            ENNReal.ofReal (2 * delta) + badLifted Set.univ ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hregularFinite, hbadFinite⟩
  have hreal := ENNReal.toReal_mono hupperFinite hENN
  rw [ENNReal.toReal_add hregularFinite hbadFinite,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hceiling,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hdelta)] at hreal
  nlinarith

/-- Uniform lifted good densities plus a bad mass vanishing along the volume
sequence rule out a zero atom in every supplied finite-measure weak limit.
This is the exact nullity endpoint needed for the all-distinct decay sector:
the still model-specific input is a volume-uniform coarea constant and a
vanishing unweighted bad-source mass. -/
theorem finiteMeasure_singleton_zero_eq_zero_of_liftedGoodBadDensity
    (source : Nat → FiniteMeasure Real) (target : FiniteMeasure Real)
    (hlimit : Tendsto source atTop (nhds target))
    (goodLifted badLifted : Nat → Measure MassTriple)
    (C : ENNReal) (hC : C ≠ ∞)
    (ceiling : Real) (hceiling : 0 ≤ ceiling)
    (hdecompose : ∀ n,
      (source n : Measure Real) =
        Measure.map Prod.snd (goodLifted n + badLifted n))
    (hgoodDensity : ∀ n,
      goodLifted n ≤ C • (volume : Measure MassTriple))
    (hgoodChild : ∀ n, ∀ᵐ point ∂goodLifted n,
      point ∈ liftedChildFrequencyCylinder ceiling)
    (hbadFinite : ∀ n, badLifted n Set.univ ≠ ∞)
    (hbadTendsto : Tendsto
      (fun n => (badLifted n Set.univ).toReal) atTop (nhds 0)) :
    (target : Measure Real) ({0} : Set Real) = 0 := by
  refine
    finiteMeasure_singleton_zero_eq_zero_of_linearSmallBall_with_vanishingError
      source target hlimit (2 * C.toReal * ceiling ^ 2)
      (by positivity) (fun n => (badLifted n Set.univ).toReal)
      (fun _n => ENNReal.toReal_nonneg) hbadTendsto ?_
  intro n delta hdelta _hdeltaOne
  rw [hdecompose n]
  exact
    map_snd_good_add_bad_absoluteMismatchSublevel_toReal_le
      (goodLifted n) (badLifted n) C hC ceiling hceiling
      (hgoodDensity n) (hgoodChild n) (hbadFinite n) hdelta.le

/-- The three-mass replacement family inherits the lower iid mass bound from
the frozen environment and the clipping of the selected coordinates. -/
theorem massLower_le_threeMassSiteConfig_mass
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ site : Lattice.Site N) (triple : MassTriple) :
    massLower ≤
      (threeMassSiteConfig fixed site₀ site₁ site₂ triple).mass site := by
  unfold threeMassSiteConfig
  change massLower ≤
    (if site = site₀ then clippedMass triple.1.1
      else if site = site₁ then clippedMass triple.1.2
      else if site = site₂ then clippedMass triple.2
      else fixed.mass site)
  split_ifs
  · exact (clippedMass_mem_support triple.1.1).1
  · exact (clippedMass_mem_support triple.1.2).1
  · exact (clippedMass_mem_support triple.2).1
  · exact (hfixed site).1

/-- Every child frequency of the actual three-mass chart lies in the frozen
uniform band `[0, sqrt 5]`. -/
theorem actualThreeMassLiftedFrequencyChart_fst_mem_childFrequencySquare
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple) :
    (actualThreeMassLiftedFrequencyChart
      fixed site₀ site₁ site₂ sign modes triple).1 ∈
        childFrequencySquare (Real.sqrt 5) := by
  let mass := threeMassSiteConfig fixed site₀ site₁ site₂ triple
  have hmass : ∀ site, massLower ≤ mass.mass site := by
    intro site
    exact massLower_le_threeMassSiteConfig_mass
      fixed hfixed site₀ site₁ site₂ site triple
  have hupper (r : Fin 3) :
      orderedModeFrequency (harmonicHermitian mass) (modes r) ≤
        Real.sqrt 5 := by
    simpa [mass, threeMassHarmonicHermitian, massLower] using
      orderedModeFrequency_harmonic_le_sqrt_four_div_massLower
        mass massLower massLower_pos hmass (modes r)
  change
    (orderedModeFrequency (harmonicHermitian mass) (modes 1),
      orderedModeFrequency (harmonicHermitian mass) (modes 2)) ∈
        Set.Icc 0 (Real.sqrt 5) ×ˢ Set.Icc 0 (Real.sqrt 5)
  exact ⟨⟨Real.sqrt_nonneg _, hupper 1⟩,
    ⟨Real.sqrt_nonneg _, hupper 2⟩⟩

/-- Any pushforward through the actual chart is automatically supported in
the lifted child-frequency cylinder when the frozen environment lies in the
iid mass support. -/
theorem ae_map_actualThreeMassLiftedFrequencyChart_mem_childCylinder
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (source : Measure MassTriple) :
    ∀ᵐ point ∂Measure.map
        (actualThreeMassLiftedFrequencyChart
          fixed site₀ site₁ site₂ sign modes) source,
      point ∈ liftedChildFrequencyCylinder (Real.sqrt 5) := by
  apply (ae_map_iff
    (continuous_actualThreeMassLiftedFrequencyChart
      fixed site₀ site₁ site₂ sign modes).measurable.aemeasurable
    (measurableSet_liftedChildFrequencyCylinder (Real.sqrt 5))).2
  exact Filter.Eventually.of_forall fun triple =>
    ⟨actualThreeMassLiftedFrequencyChart_fst_mem_childFrequencySquare
      fixed hfixed site₀ site₁ site₂ sign modes triple, Set.mem_univ _⟩

theorem map_actualThreeMassLiftedFrequencyChart_univ
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (source : Measure MassTriple) :
    Measure.map
        (actualThreeMassLiftedFrequencyChart
          fixed site₀ site₁ site₂ sign modes) source Set.univ =
      source Set.univ := by
  rw [Measure.map_apply
    (continuous_actualThreeMassLiftedFrequencyChart
      fixed site₀ site₁ site₂ sign modes).measurable MeasurableSet.univ]
  simp

/-- The genuine three-mass chart satisfies an arbitrary-target approximate
mismatch density bound once its good pushforward has a coarea density
ceiling. The only exceptional term is the original bad source mass. -/
theorem actualThreeMassLifted_goodBad_mismatch_apply_le
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (goodSource badSource : Measure MassTriple)
    (C : ENNReal)
    (hgoodDensity :
      Measure.map
          (actualThreeMassLiftedFrequencyChart
            fixed site₀ site₁ site₂ sign modes) goodSource ≤
        C • (volume : Measure MassTriple))
    {target : Set Real} (htarget : MeasurableSet target) :
    Measure.map Prod.snd
        (Measure.map
          (actualThreeMassLiftedFrequencyChart
            fixed site₀ site₁ site₂ sign modes)
          (goodSource + badSource)) target ≤
      C * (ENNReal.ofReal (Real.sqrt 5) *
          ENNReal.ofReal (Real.sqrt 5)) *
        (volume : Measure Real) target + badSource Set.univ := by
  let chart := actualThreeMassLiftedFrequencyChart
    fixed site₀ site₁ site₂ sign modes
  have hchart : Measurable chart :=
    (continuous_actualThreeMassLiftedFrequencyChart
      fixed site₀ site₁ site₂ sign modes).measurable
  rw [Measure.map_add goodSource badSource hchart]
  have hmain :=
    map_snd_good_add_bad_apply_le
      (Measure.map chart goodSource) (Measure.map chart badSource)
      C (Real.sqrt 5) hgoodDensity
      (ae_map_actualThreeMassLiftedFrequencyChart_mem_childCylinder
        fixed hfixed site₀ site₁ site₂ sign modes goodSource)
      htarget
  rw [show Measure.map chart badSource Set.univ = badSource Set.univ by
    exact map_actualThreeMassLiftedFrequencyChart_univ
      fixed site₀ site₁ site₂ sign modes badSource] at hmain
  exact hmain

/-- Actual-chart specialization of the raw good/bad mismatch estimate.
The density hypothesis is precisely what an injective quantitative coarea
patch supplies. Its conclusion is already in the real-valued form consumed
by finite-measure weak-limit zero-atom theorems. -/
theorem actualThreeMassLifted_goodBad_mismatchSmallBall_toReal_le
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (goodSource badSource : Measure MassTriple)
    (C : ENNReal) (hC : C ≠ ∞)
    (hgoodDensity :
      Measure.map
          (actualThreeMassLiftedFrequencyChart
            fixed site₀ site₁ site₂ sign modes) goodSource ≤
        C • (volume : Measure MassTriple))
    (hbadFinite : badSource Set.univ ≠ ∞)
    {delta : Real} (hdelta : 0 ≤ delta) :
    (Measure.map Prod.snd
        (Measure.map
          (actualThreeMassLiftedFrequencyChart
            fixed site₀ site₁ site₂ sign modes)
          (goodSource + badSource))
        (absoluteMismatchSublevel delta)).toReal ≤
      (2 * C.toReal * (Real.sqrt 5) ^ 2) * delta +
        (badSource Set.univ).toReal := by
  let chart := actualThreeMassLiftedFrequencyChart
    fixed site₀ site₁ site₂ sign modes
  have hchart : Measurable chart :=
    (continuous_actualThreeMassLiftedFrequencyChart
      fixed site₀ site₁ site₂ sign modes).measurable
  have hbadMapFinite : Measure.map chart badSource Set.univ ≠ ∞ := by
    rw [show Measure.map chart badSource Set.univ = badSource Set.univ by
      exact map_actualThreeMassLiftedFrequencyChart_univ
        fixed site₀ site₁ site₂ sign modes badSource]
    exact hbadFinite
  rw [Measure.map_add goodSource badSource hchart]
  have hmain :=
    map_snd_good_add_bad_absoluteMismatchSublevel_toReal_le
      (Measure.map chart goodSource) (Measure.map chart badSource)
      C hC (Real.sqrt 5) (Real.sqrt_nonneg _) hgoodDensity
      (ae_map_actualThreeMassLiftedFrequencyChart_mem_childCylinder
        fixed hfixed site₀ site₁ site₂ sign modes goodSource)
      hbadMapFinite hdelta
  rw [show Measure.map chart badSource Set.univ = badSource Set.univ by
    exact map_actualThreeMassLiftedFrequencyChart_univ
      fixed site₀ site₁ site₂ sign modes badSource] at hmain
  exact hmain

end

end ArchonPhysics.ActualLiftedMismatchSmallBall
