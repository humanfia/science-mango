import Mathlib
import Physlib.SpaceAndTime.Space.Basic
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0239

/-!
# Locating an earthquake focus with P and S waves

The Earth is modeled locally by three-dimensional Euclidean coordinates whose
length unit is one kilometre.  The third coordinate is vertical, the local
surface is the plane with third coordinate zero, and underground points have
negative third coordinate.  This is the local flat-surface version of the
radial geometry shown in the supplied Earth cross-section.

Wave speeds are genuine unit-independent `DimSpeed` quantities from Physlib.
Coordinates, metric distances, and station timestamps are scalar readouts in
kilometres and seconds, respectively.  Thus the scalar fields below are
measurements of physical quantities rather than replacements for them.
-/

/-! ## Physical quantities and named-unit readouts -/

/-- Read a unit-independent speed in kilometres per second. -/
def speedInKilometersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed {UnitChoices.SI with
    length := LengthUnit.kilometers, time := TimeUnit.seconds}).val : ℝ)

/-- Distance in the local three-dimensional frame, read in kilometres. -/
def distanceInKilometers (p q : Space 3) : ℝ :=
  dist p q

/-- The vertical coordinate in the local frame, read in kilometres. -/
def verticalCoordinateInKilometers (p : Space 3) : ℝ :=
  p 2

/-- A point on the locally planar surface of the Earth. -/
def IsOnLocalEarthSurface (p : Space 3) : Prop :=
  verticalCoordinateInKilometers p = 0

/-- A possible focus lies strictly below the local surface. -/
def IsUnderground (p : Space 3) : Prop :=
  verticalCoordinateInKilometers p < 0

/-! ## Wave roles, figure labels, and station readings -/

/-- The two seismic-wave species detected at each station. -/
inductive SeismicWaveKind where
  | pWave
  | sWave
  deriving DecidableEq, Repr

/-- The displacement type associated with a seismic wave. -/
inductive WavePolarization where
  | longitudinal
  | transverse
  deriving DecidableEq, Repr

/-- The idealization of the material traversed by the waves. -/
inductive EarthMaterialModel where
  | uniform
  deriving DecidableEq, Repr

/-- The idealization of a seismic ray between the focus and a station. -/
inductive PropagationPathModel where
  | straightLine
  deriving DecidableEq, Repr

/-- The three locations explicitly labeled in the supplied bitmap. -/
inductive FigurePoint where
  | focus
  | epicenter
  | seismograph
  deriving DecidableEq, Repr

/-- A surface detector together with its P- and S-wave arrival timestamps. -/
structure DetectionStation where
  positionInKilometerCoordinates : Space 3
  pWaveArrivalTimeSeconds : ℝ
  sWaveArrivalTimeSeconds : ℝ

/-- Select the measured arrival timestamp belonging to a wave species. -/
def DetectionStation.arrivalTimeSeconds
    (station : DetectionStation) : SeismicWaveKind → ℝ
  | .pWave => station.pWaveArrivalTimeSeconds
  | .sWave => station.sWaveArrivalTimeSeconds

/-!
The complete earthquake-localization setup.  Stations are indexed by natural
numbers so that no answer count is built into their ambient type.  A designated
noncollinear triple will be selected separately by the placement assumptions;
that placement data does not say that the triple locates the focus.
-/
structure EarthquakeLocalizationSetup where
  focusPosition : Space 3
  epicenterPosition : Space 3
  originTimeSeconds : ℝ
  waveSpeed : SeismicWaveKind → DimSpeed
  wavePolarization : SeismicWaveKind → WavePolarization
  materialModel : EarthMaterialModel
  pathModel : SeismicWaveKind → ℕ → PropagationPathModel
  stations : ℕ → DetectionStation
  figurePosition : FigurePoint → Space 3
  figureDashedPathEndpoints : FigurePoint × FigurePoint

/-! ## Problem, figure, and governing-law assumptions -/

/--
The qualitative and numerical wave data stated in the prose.  The two real
equalities are calibrated readouts of physical `DimSpeed` values, in km/s.
-/
structure MatchesProblemWaveData
    (setup : EarthquakeLocalizationSetup) : Prop where
  pWaveIsLongitudinal :
    setup.wavePolarization .pWave = .longitudinal
  sWaveIsTransverse :
    setup.wavePolarization .sWave = .transverse
  materialIsUniform : setup.materialModel = .uniform
  pathsAreStraight :
    ∀ wave station, setup.pathModel wave station = .straightLine
  pWaveSpeedKilometersPerSecond :
    speedInKilometersPerSecond (setup.waveSpeed .pWave) = 8
  sWaveSpeedKilometersPerSecond :
    speedInKilometersPerSecond (setup.waveSpeed .sWave) = 5
  sWaveIsSlower :
    speedInKilometersPerSecond (setup.waveSpeed .sWave) <
      speedInKilometersPerSecond (setup.waveSpeed .pWave)

/--
Primary-image readouts.  The focus and epicenter have the same horizontal
coordinates, with the focus below the surface; the illustrated seismograph is
the first of the three candidate stations.  The dashed path joins the labeled
focus and seismograph, as in the bitmap.
-/
structure MatchesSuppliedEarthquakeFigure
    (setup : EarthquakeLocalizationSetup) : Prop where
  focusLabel : setup.figurePosition .focus = setup.focusPosition
  epicenterLabel : setup.figurePosition .epicenter = setup.epicenterPosition
  seismographLabel :
    setup.figurePosition .seismograph =
      (setup.stations 0).positionInKilometerCoordinates
  epicenterIsOnSurface : IsOnLocalEarthSurface setup.epicenterPosition
  focusIsUnderground : IsUnderground setup.focusPosition
  focusRadiallyBelowEpicenter :
    setup.focusPosition 0 = setup.epicenterPosition 0 ∧
      setup.focusPosition 1 = setup.epicenterPosition 1
  illustratedSeismographIsOnSurface :
    IsOnLocalEarthSurface (setup.figurePosition .seismograph)
  dashedPathRunsFromFocusToSeismograph :
    setup.figureDashedPathEndpoints = (.focus, .seismograph)

/--
Signed planar orientation of three surface stations.  Nonzero orientation is
the usual noncollinearity condition needed for three-dimensional
trilateration from a planar station array.
-/
def stationPlanarOrientation
    (a b c : DetectionStation) : ℝ :=
  (b.positionInKilometerCoordinates 0 -
      a.positionInKilometerCoordinates 0) *
      (c.positionInKilometerCoordinates 1 -
        a.positionInKilometerCoordinates 1) -
    (b.positionInKilometerCoordinates 1 -
      a.positionInKilometerCoordinates 1) *
      (c.positionInKilometerCoordinates 0 -
        a.positionInKilometerCoordinates 0)

/-- Nondegenerate placement data for the three available surface stations. -/
structure HasNondegenerateStationGeometry
    (setup : EarthquakeLocalizationSetup) : Prop where
  stationsAreOnSurface :
    ∀ i, IsOnLocalEarthSurface
      (setup.stations i).positionInKilometerCoordinates
  stationsAreNoncollinear :
    stationPlanarOrientation
      (setup.stations 0) (setup.stations 1) (setup.stations 2) ≠ 0

/-- The designated noncollinear triple of reference stations. -/
def referenceStationSet : Finset ℕ :=
  {0, 1, 2}

/-!
Constant-speed travel time along a straight ray: distance equals speed times
elapsed time.  This is the governing physical law for both wave species and
does not assert any localization or station-count conclusion.
-/
structure SatisfiesStraightUniformSeismicPropagation
    (setup : EarthquakeLocalizationSetup) : Prop where
  travelTimeLaw :
    ∀ (wave : SeismicWaveKind) (i : ℕ),
      distanceInKilometers setup.focusPosition
          (setup.stations i).positionInKilometerCoordinates =
        speedInKilometersPerSecond (setup.waveSpeed wave) *
          ((setup.stations i).arrivalTimeSeconds wave -
            setup.originTimeSeconds)

/-! ## Candidate compatibility and unambiguous localization -/

/-- A hypothetical underground source with an unknown origin timestamp. -/
structure CandidateFocus where
  position : Space 3
  originTimeSeconds : ℝ

/--
A candidate reproduces both P and S timestamps at every selected station
under the same straight, uniform, constant-speed propagation law.
-/
def CandidateFitsStationReadings
    (setup : EarthquakeLocalizationSetup)
    (candidate : CandidateFocus) (chosen : Finset ℕ) : Prop :=
  IsUnderground candidate.position ∧
    ∀ (i : ℕ), i ∈ chosen → ∀ wave : SeismicWaveKind,
      distanceInKilometers candidate.position
          (setup.stations i).positionInKilometerCoordinates =
        speedInKilometersPerSecond (setup.waveSpeed wave) *
          ((setup.stations i).arrivalTimeSeconds wave -
            candidate.originTimeSeconds)

/-- Every physically admissible source matching the selected readings is the actual focus. -/
def StationSetLocatesFocusUnambiguously
    (setup : EarthquakeLocalizationSetup)
    (chosen : Finset ℕ) : Prop :=
  ∀ candidate : CandidateFocus,
    CandidateFitsStationReadings setup candidate chosen →
      candidate.position = setup.focusPosition

/--
`n` is the minimum sufficient number of stations: some set of that size
locates the focus, and every locating set has at least that size.
-/
def IsMinimumDetectionStationCount
    (setup : EarthquakeLocalizationSetup) (n : ℕ) : Prop :=
  (∃ chosen : Finset ℕ,
      chosen.card = n ∧ StationSetLocatesFocusUnambiguously setup chosen) ∧
    ∀ chosen : Finset ℕ,
      StationSetLocatesFocusUnambiguously setup chosen → n ≤ chosen.card

/-! ## Derived localization facts -/

/--
At one station, the P--S arrival delay determines the focus distance because
the two speeds differ.  With the stated `8 km/s` and `5 km/s` speeds, the
conversion factor is `40/3 km` per second of delay.
-/
lemma p_s_delay_determines_focus_distance
    (setup : EarthquakeLocalizationSetup)
    (waveData : MatchesProblemWaveData setup)
    (laws : SatisfiesStraightUniformSeismicPropagation setup)
    (i : ℕ) :
    distanceInKilometers setup.focusPosition
        (setup.stations i).positionInKilometerCoordinates =
      (40 / 3 : ℝ) *
        ((setup.stations i).sWaveArrivalTimeSeconds -
          (setup.stations i).pWaveArrivalTimeSeconds) := by
  have hp := laws.travelTimeLaw .pWave i
  have hs := laws.travelTimeLaw .sWave i
  rw [waveData.pWaveSpeedKilometersPerSecond] at hp
  rw [waveData.sWaveSpeedKilometersPerSecond] at hs
  simp only [DetectionStation.arrivalTimeSeconds] at hp hs
  linarith

/-- Three noncollinear surface stations determine the underground focus uniquely. -/
lemma three_noncollinear_stations_locate_focus
    (setup : EarthquakeLocalizationSetup)
    (waveData : MatchesProblemWaveData setup)
    (figure : MatchesSuppliedEarthquakeFigure setup)
    (geometry : HasNondegenerateStationGeometry setup)
    (laws : SatisfiesStraightUniformSeismicPropagation setup) :
    StationSetLocatesFocusUnambiguously setup referenceStationSet := by
  intro candidate hcandidate
  rcases hcandidate with ⟨candidateUnderground, candidateFits⟩
  have equalDistance (i : ℕ) (hi : i ∈ referenceStationSet) :
      distanceInKilometers candidate.position
          (setup.stations i).positionInKilometerCoordinates =
        distanceInKilometers setup.focusPosition
          (setup.stations i).positionInKilometerCoordinates := by
    have candidateP := candidateFits i hi .pWave
    have candidateS := candidateFits i hi .sWave
    have actualP := laws.travelTimeLaw .pWave i
    have actualS := laws.travelTimeLaw .sWave i
    rw [waveData.pWaveSpeedKilometersPerSecond] at candidateP actualP
    rw [waveData.sWaveSpeedKilometersPerSecond] at candidateS actualS
    simp only [DetectionStation.arrivalTimeSeconds] at candidateP candidateS actualP actualS
    linarith
  have squareDistance {x y station : Space 3}
      (h : distanceInKilometers x station = distanceInKilometers y station) :
      (∑ j : Fin 3, (x j - station j) ^ 2) =
        ∑ j : Fin 3, (y j - station j) ^ 2 := by
    change dist x station = dist y station at h
    rw [Space.dist_eq, Space.dist_eq] at h
    have hx : 0 ≤ ∑ j : Fin 3, (x j - station j) ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    have hy : 0 ≤ ∑ j : Fin 3, (y j - station j) ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    have hsquared := congrArg (fun z : ℝ => z ^ 2) h
    rwa [Real.sq_sqrt hx, Real.sq_sqrt hy] at hsquared
  have hdist0 := squareDistance (equalDistance 0 (by simp [referenceStationSet]))
  have hdist1 := squareDistance (equalDistance 1 (by simp [referenceStationSet]))
  have hdist2 := squareDistance (equalDistance 2 (by simp [referenceStationSet]))
  have surface0 :
      (setup.stations 0).positionInKilometerCoordinates 2 = 0 := by
    simpa [IsOnLocalEarthSurface, verticalCoordinateInKilometers] using
      geometry.stationsAreOnSurface 0
  have surface1 :
      (setup.stations 1).positionInKilometerCoordinates 2 = 0 := by
    simpa [IsOnLocalEarthSurface, verticalCoordinateInKilometers] using
      geometry.stationsAreOnSurface 1
  have surface2 :
      (setup.stations 2).positionInKilometerCoordinates 2 = 0 := by
    simpa [IsOnLocalEarthSurface, verticalCoordinateInKilometers] using
      geometry.stationsAreOnSurface 2
  simp only [Fin.sum_univ_succ] at hdist0 hdist1 hdist2
  norm_num at hdist0 hdist1 hdist2
  rw [surface0] at hdist0
  rw [surface1] at hdist1
  rw [surface2] at hdist2
  norm_num at hdist0 hdist1 hdist2
  have horizontalEquation1 :
      ((setup.stations 1).positionInKilometerCoordinates 0 -
          (setup.stations 0).positionInKilometerCoordinates 0) *
          (candidate.position 0 - setup.focusPosition 0) +
        ((setup.stations 1).positionInKilometerCoordinates 1 -
          (setup.stations 0).positionInKilometerCoordinates 1) *
          (candidate.position 1 - setup.focusPosition 1) = 0 := by
    linear_combination (1 / 2 : ℝ) * hdist0 - (1 / 2 : ℝ) * hdist1
  have horizontalEquation2 :
      ((setup.stations 2).positionInKilometerCoordinates 0 -
          (setup.stations 0).positionInKilometerCoordinates 0) *
          (candidate.position 0 - setup.focusPosition 0) +
        ((setup.stations 2).positionInKilometerCoordinates 1 -
          (setup.stations 0).positionInKilometerCoordinates 1) *
          (candidate.position 1 - setup.focusPosition 1) = 0 := by
    linear_combination (1 / 2 : ℝ) * hdist0 - (1 / 2 : ℝ) * hdist2
  have horizontal0 :
      candidate.position 0 = setup.focusPosition 0 := by
    have hproduct :
        stationPlanarOrientation
              (setup.stations 0) (setup.stations 1) (setup.stations 2) *
            (candidate.position 0 - setup.focusPosition 0) = 0 := by
      unfold stationPlanarOrientation
      linear_combination
        ((setup.stations 2).positionInKilometerCoordinates 1 -
            (setup.stations 0).positionInKilometerCoordinates 1) *
              horizontalEquation1 -
          ((setup.stations 1).positionInKilometerCoordinates 1 -
            (setup.stations 0).positionInKilometerCoordinates 1) *
              horizontalEquation2
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp hproduct).resolve_left geometry.stationsAreNoncollinear)
  have horizontal1 :
      candidate.position 1 = setup.focusPosition 1 := by
    have hproduct :
        stationPlanarOrientation
              (setup.stations 0) (setup.stations 1) (setup.stations 2) *
            (candidate.position 1 - setup.focusPosition 1) = 0 := by
      unfold stationPlanarOrientation
      linear_combination
        ((setup.stations 1).positionInKilometerCoordinates 0 -
            (setup.stations 0).positionInKilometerCoordinates 0) *
              horizontalEquation2 -
          ((setup.stations 2).positionInKilometerCoordinates 0 -
            (setup.stations 0).positionInKilometerCoordinates 0) *
              horizontalEquation1
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp hproduct).resolve_left geometry.stationsAreNoncollinear)
  have vertical :
      candidate.position 2 = setup.focusPosition 2 := by
    rw [horizontal0, horizontal1] at hdist0
    have hsquares :
        candidate.position 2 ^ 2 = setup.focusPosition 2 ^ 2 := by
      nlinarith only [hdist0]
    have candidateNegative :
        candidate.position 2 < 0 := candidateUnderground
    have focusNegative :
        setup.focusPosition 2 < 0 := figure.focusIsUnderground
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsquares with hsame | hopposite
    · exact hsame
    · nlinarith only [candidateNegative, focusNegative, hopposite]
  apply Space.eq_of_apply
  intro j
  fin_cases j
  · exact horizontal0
  · exact horizontal1
  · exact vertical

/-- Any selection of fewer than three of the available stations leaves an ambiguity. -/
lemma fewer_than_three_stations_do_not_locate_focus
    (setup : EarthquakeLocalizationSetup)
    (waveData : MatchesProblemWaveData setup)
    (figure : MatchesSuppliedEarthquakeFigure setup)
    (geometry : HasNondegenerateStationGeometry setup)
    (laws : SatisfiesStraightUniformSeismicPropagation setup)
    (chosen : Finset ℕ)
    (hasFewerThanThree : chosen.card < 3) :
    ¬ StationSetLocatesFocusUnambiguously setup chosen := by
  intro locates
  have focusNegative : setup.focusPosition 2 < 0 :=
    figure.focusIsUnderground
  have stationSurface (i : ℕ) :
      (setup.stations i).positionInKilometerCoordinates 2 = 0 := by
    simpa [IsOnLocalEarthSurface, verticalCoordinateInKilometers] using
      geometry.stationsAreOnSurface i
  have oneStationAlternative (station focus : Space 3)
      (stationSurface : station 2 = 0) (focusNegative : focus 2 < 0) :
      ∃ alternative : Space 3,
        alternative 2 < 0 ∧ alternative ≠ focus ∧
          distanceInKilometers alternative station =
            distanceInKilometers focus station := by
    by_cases horizontalNonnegative : 0 ≤ focus 0 - station 0
    · let alternative : Space 3 :=
        ⟨![station 0 + (4 / 5 : ℝ) * (focus 0 - station 0) +
              (3 / 5 : ℝ) * focus 2,
            focus 1,
            -(3 / 5 : ℝ) * (focus 0 - station 0) +
              (4 / 5 : ℝ) * focus 2]⟩
      refine ⟨alternative, ?_, ?_, ?_⟩
      · change
          -(3 / 5 : ℝ) * (focus 0 - station 0) +
              (4 / 5 : ℝ) * focus 2 < 0
        linarith
      · intro alternativeEqualsFocus
        have horizontalEquality :=
          congrArg (fun point : Space 3 => point 0) alternativeEqualsFocus
        have verticalEquality :=
          congrArg (fun point : Space 3 => point 2) alternativeEqualsFocus
        change
          station 0 + (4 / 5 : ℝ) * (focus 0 - station 0) +
              (3 / 5 : ℝ) * focus 2 = focus 0 at horizontalEquality
        change
          -(3 / 5 : ℝ) * (focus 0 - station 0) +
              (4 / 5 : ℝ) * focus 2 = focus 2 at verticalEquality
        linarith
      · change dist alternative station = dist focus station
        rw [Space.dist_eq, Space.dist_eq]
        apply congrArg Real.sqrt
        simp only [Fin.sum_univ_succ]
        norm_num
        change
          (station 0 + (4 / 5 : ℝ) * (focus 0 - station 0) +
                  (3 / 5 : ℝ) * focus 2 - station 0) ^ 2 +
                ((focus 1 - station 1) ^ 2 +
                  (-(3 / 5 : ℝ) * (focus 0 - station 0) +
                      (4 / 5 : ℝ) * focus 2 - station 2) ^ 2) =
              (focus 0 - station 0) ^ 2 +
                ((focus 1 - station 1) ^ 2 +
                  (focus 2 - station 2) ^ 2)
        rw [stationSurface]
        ring
    · have horizontalNegative : focus 0 - station 0 < 0 :=
        lt_of_not_ge horizontalNonnegative
      let alternative : Space 3 :=
        ⟨![station 0 + (4 / 5 : ℝ) * (focus 0 - station 0) -
              (3 / 5 : ℝ) * focus 2,
            focus 1,
            (3 / 5 : ℝ) * (focus 0 - station 0) +
              (4 / 5 : ℝ) * focus 2]⟩
      refine ⟨alternative, ?_, ?_, ?_⟩
      · change
          (3 / 5 : ℝ) * (focus 0 - station 0) +
              (4 / 5 : ℝ) * focus 2 < 0
        linarith
      · intro alternativeEqualsFocus
        have horizontalEquality :=
          congrArg (fun point : Space 3 => point 0) alternativeEqualsFocus
        have verticalEquality :=
          congrArg (fun point : Space 3 => point 2) alternativeEqualsFocus
        change
          station 0 + (4 / 5 : ℝ) * (focus 0 - station 0) -
              (3 / 5 : ℝ) * focus 2 = focus 0 at horizontalEquality
        change
          (3 / 5 : ℝ) * (focus 0 - station 0) +
              (4 / 5 : ℝ) * focus 2 = focus 2 at verticalEquality
        linarith
      · change dist alternative station = dist focus station
        rw [Space.dist_eq, Space.dist_eq]
        apply congrArg Real.sqrt
        simp only [Fin.sum_univ_succ]
        norm_num
        change
          (station 0 + (4 / 5 : ℝ) * (focus 0 - station 0) -
                  (3 / 5 : ℝ) * focus 2 - station 0) ^ 2 +
                ((focus 1 - station 1) ^ 2 +
                  ((3 / 5 : ℝ) * (focus 0 - station 0) +
                      (4 / 5 : ℝ) * focus 2 - station 2) ^ 2) =
              (focus 0 - station 0) ^ 2 +
                ((focus 1 - station 1) ^ 2 +
                  (focus 2 - station 2) ^ 2)
        rw [stationSurface]
        ring
  have twoStationAlternative (stationA stationB focus : Space 3)
      (surfaceA : stationA 2 = 0) (surfaceB : stationB 2 = 0)
      (focusNegative : focus 2 < 0) :
      ∃ alternative : Space 3,
        alternative 2 < 0 ∧ alternative ≠ focus ∧
          distanceInKilometers alternative stationA =
            distanceInKilometers focus stationA ∧
          distanceInKilometers alternative stationB =
            distanceInKilometers focus stationB := by
    let directionSquare : ℝ :=
      (stationB 0 - stationA 0) ^ 2 +
        (stationB 1 - stationA 1) ^ 2
    by_cases coincidentHorizontally : directionSquare = 0
    · have horizontal0 : stationB 0 = stationA 0 := by
        have h0 : 0 ≤ (stationB 0 - stationA 0) ^ 2 := sq_nonneg _
        have h1 : 0 ≤ (stationB 1 - stationA 1) ^ 2 := sq_nonneg _
        dsimp [directionSquare] at coincidentHorizontally
        nlinarith
      have horizontal1 : stationB 1 = stationA 1 := by
        have h0 : 0 ≤ (stationB 0 - stationA 0) ^ 2 := sq_nonneg _
        have h1 : 0 ≤ (stationB 1 - stationA 1) ^ 2 := sq_nonneg _
        dsimp [directionSquare] at coincidentHorizontally
        nlinarith
      have stationsCoincide : stationB = stationA := by
        apply Space.eq_of_apply
        intro j
        fin_cases j
        · exact horizontal0
        · exact horizontal1
        · exact surfaceB.trans surfaceA.symm
      obtain ⟨alternative, alternativeNegative, alternativeNe, hdistance⟩ :=
        oneStationAlternative stationA focus surfaceA focusNegative
      refine ⟨alternative, alternativeNegative, alternativeNe, hdistance, ?_⟩
      simpa [stationsCoincide] using hdistance
    · let signedOffset : ℝ :=
        (stationB 0 - stationA 0) * (focus 1 - stationA 1) -
          (stationB 1 - stationA 1) * (focus 0 - stationA 0)
      by_cases offsetNonzero : signedOffset ≠ 0
      · let alternative : Space 3 :=
          ⟨![focus 0 +
                2 * signedOffset * (stationB 1 - stationA 1) /
                  directionSquare,
              focus 1 -
                2 * signedOffset * (stationB 0 - stationA 0) /
                  directionSquare,
              focus 2]⟩
        refine ⟨alternative, ?_, ?_, ?_, ?_⟩
        · change focus 2 < 0
          exact focusNegative
        · intro alternativeEqualsFocus
          have horizontalEquality0 :=
            congrArg (fun point : Space 3 => point 0) alternativeEqualsFocus
          have horizontalEquality1 :=
            congrArg (fun point : Space 3 => point 1) alternativeEqualsFocus
          change
            focus 0 +
                2 * signedOffset * (stationB 1 - stationA 1) /
                  directionSquare = focus 0 at horizontalEquality0
          change
            focus 1 -
                2 * signedOffset * (stationB 0 - stationA 0) /
                  directionSquare = focus 1 at horizontalEquality1
          have direction1Zero :
              signedOffset * (stationB 1 - stationA 1) = 0 := by
            field_simp [coincidentHorizontally] at horizontalEquality0
            linarith
          have direction0Zero :
              signedOffset * (stationB 0 - stationA 0) = 0 := by
            field_simp [coincidentHorizontally] at horizontalEquality1
            linarith
          have h1 : stationB 1 - stationA 1 = 0 :=
            (mul_eq_zero.mp direction1Zero).resolve_left offsetNonzero
          have h0 : stationB 0 - stationA 0 = 0 :=
            (mul_eq_zero.mp direction0Zero).resolve_left offsetNonzero
          apply coincidentHorizontally
          simp [directionSquare, h0, h1]
        · change dist alternative stationA = dist focus stationA
          rw [Space.dist_eq, Space.dist_eq]
          apply congrArg Real.sqrt
          simp only [Fin.sum_univ_succ]
          norm_num
          change
            (focus 0 +
                    2 * signedOffset * (stationB 1 - stationA 1) /
                      directionSquare - stationA 0) ^ 2 +
                  ((focus 1 -
                        2 * signedOffset * (stationB 0 - stationA 0) /
                          directionSquare - stationA 1) ^ 2 +
                    (focus 2 - stationA 2) ^ 2) =
                (focus 0 - stationA 0) ^ 2 +
                  ((focus 1 - stationA 1) ^ 2 +
                    (focus 2 - stationA 2) ^ 2)
          field_simp [coincidentHorizontally]
          dsimp [signedOffset, directionSquare]
          ring
        · change dist alternative stationB = dist focus stationB
          rw [Space.dist_eq, Space.dist_eq]
          apply congrArg Real.sqrt
          simp only [Fin.sum_univ_succ]
          norm_num
          change
            (focus 0 +
                    2 * signedOffset * (stationB 1 - stationA 1) /
                      directionSquare - stationB 0) ^ 2 +
                  ((focus 1 -
                        2 * signedOffset * (stationB 0 - stationA 0) /
                          directionSquare - stationB 1) ^ 2 +
                    (focus 2 - stationB 2) ^ 2) =
                (focus 0 - stationB 0) ^ 2 +
                  ((focus 1 - stationB 1) ^ 2 +
                    (focus 2 - stationB 2) ^ 2)
          field_simp [coincidentHorizontally]
          dsimp [signedOffset, directionSquare]
          ring
      · have offsetZero : signedOffset = 0 :=
          not_ne_iff.mp offsetNonzero
        have directionSquareNonnegative : 0 ≤ directionSquare := by
          dsimp [directionSquare]
          positivity
        have directionSquarePositive : 0 < directionSquare :=
          lt_of_le_of_ne directionSquareNonnegative
            (Ne.symm coincidentHorizontally)
        let directionLength : ℝ := √directionSquare
        have directionLengthPositive : 0 < directionLength := by
          simpa [directionLength] using
            Real.sqrt_pos.2 directionSquarePositive
        have directionLengthNe : directionLength ≠ 0 :=
          ne_of_gt directionLengthPositive
        have directionLengthSquare :
            directionLength ^ 2 = directionSquare := by
          simpa [directionLength] using
            Real.sq_sqrt directionSquareNonnegative
        let rotationScale : ℝ :=
          3 * focus 2 / (5 * directionLength)
        have rotationScaleSquare :
            rotationScale ^ 2 * directionSquare =
              (9 / 25 : ℝ) * focus 2 ^ 2 := by
          dsimp [rotationScale]
          field_simp [directionLengthNe]
          rw [directionLengthSquare]
          ring
        have orthogonalAtA :
            (focus 0 - stationA 0) *
                  (-rotationScale * (stationB 1 - stationA 1)) +
                (focus 1 - stationA 1) *
                  (rotationScale * (stationB 0 - stationA 0)) = 0 := by
          calc
            _ = rotationScale * signedOffset := by
              dsimp [signedOffset]
              ring
            _ = 0 := by rw [offsetZero]; ring
        have orthogonalAtB :
            (focus 0 - stationB 0) *
                  (-rotationScale * (stationB 1 - stationA 1)) +
                (focus 1 - stationB 1) *
                  (rotationScale * (stationB 0 - stationA 0)) = 0 := by
          calc
            _ = rotationScale * signedOffset := by
              dsimp [signedOffset]
              ring
            _ = 0 := by rw [offsetZero]; ring
        let alternative : Space 3 :=
          ⟨![focus 0 -
                rotationScale * (stationB 1 - stationA 1),
              focus 1 +
                rotationScale * (stationB 0 - stationA 0),
              (4 / 5 : ℝ) * focus 2]⟩
        refine ⟨alternative, ?_, ?_, ?_, ?_⟩
        · change (4 / 5 : ℝ) * focus 2 < 0
          linarith
        · intro alternativeEqualsFocus
          have verticalEquality :=
            congrArg (fun point : Space 3 => point 2) alternativeEqualsFocus
          change (4 / 5 : ℝ) * focus 2 = focus 2 at verticalEquality
          linarith
        · change dist alternative stationA = dist focus stationA
          rw [Space.dist_eq, Space.dist_eq]
          apply congrArg Real.sqrt
          simp only [Fin.sum_univ_succ]
          norm_num
          change
            (focus 0 -
                    rotationScale * (stationB 1 - stationA 1) -
                    stationA 0) ^ 2 +
                  ((focus 1 +
                        rotationScale * (stationB 0 - stationA 0) -
                        stationA 1) ^ 2 +
                    ((4 / 5 : ℝ) * focus 2 - stationA 2) ^ 2) =
                (focus 0 - stationA 0) ^ 2 +
                  ((focus 1 - stationA 1) ^ 2 +
                    (focus 2 - stationA 2) ^ 2)
          rw [surfaceA]
          calc
            _ = (focus 0 - stationA 0) ^ 2 +
                (focus 1 - stationA 1) ^ 2 +
                2 * ((focus 0 - stationA 0) *
                    (-rotationScale * (stationB 1 - stationA 1)) +
                  (focus 1 - stationA 1) *
                    (rotationScale * (stationB 0 - stationA 0))) +
                rotationScale ^ 2 * directionSquare +
                (16 / 25 : ℝ) * focus 2 ^ 2 := by
                  dsimp [directionSquare]
                  ring
            _ = _ := by
              rw [orthogonalAtA, rotationScaleSquare]
              ring
        · change dist alternative stationB = dist focus stationB
          rw [Space.dist_eq, Space.dist_eq]
          apply congrArg Real.sqrt
          simp only [Fin.sum_univ_succ]
          norm_num
          change
            (focus 0 -
                    rotationScale * (stationB 1 - stationA 1) -
                    stationB 0) ^ 2 +
                  ((focus 1 +
                        rotationScale * (stationB 0 - stationA 0) -
                        stationB 1) ^ 2 +
                    ((4 / 5 : ℝ) * focus 2 - stationB 2) ^ 2) =
                (focus 0 - stationB 0) ^ 2 +
                  ((focus 1 - stationB 1) ^ 2 +
                    (focus 2 - stationB 2) ^ 2)
          rw [surfaceB]
          calc
            _ = (focus 0 - stationB 0) ^ 2 +
                (focus 1 - stationB 1) ^ 2 +
                2 * ((focus 0 - stationB 0) *
                    (-rotationScale * (stationB 1 - stationA 1)) +
                  (focus 1 - stationB 1) *
                    (rotationScale * (stationB 0 - stationA 0))) +
                rotationScale ^ 2 * directionSquare +
                (16 / 25 : ℝ) * focus 2 ^ 2 := by
                  dsimp [directionSquare]
                  ring
            _ = _ := by
              rw [orthogonalAtB, rotationScaleSquare]
              ring
  have cardCases :
      chosen.card = 0 ∨ chosen.card = 1 ∨ chosen.card = 2 := by
    omega
  have alternativeExists :
      ∃ alternative : Space 3,
        IsUnderground alternative ∧
          alternative ≠ setup.focusPosition ∧
          ∀ i : ℕ, i ∈ chosen →
            distanceInKilometers alternative
                (setup.stations i).positionInKilometerCoordinates =
              distanceInKilometers setup.focusPosition
                (setup.stations i).positionInKilometerCoordinates := by
    rcases cardCases with cardZero | cardOne | cardTwo
    · have chosenEmpty : chosen = ∅ := Finset.card_eq_zero.mp cardZero
      obtain ⟨alternative, alternativeNegative, alternativeNe, _⟩ :=
        oneStationAlternative
          (setup.stations 0).positionInKilometerCoordinates
          setup.focusPosition (stationSurface 0) focusNegative
      refine ⟨alternative, alternativeNegative, alternativeNe, ?_⟩
      intro i hi
      simp [chosenEmpty] at hi
    · obtain ⟨i, chosenSingleton⟩ := Finset.card_eq_one.mp cardOne
      obtain ⟨alternative, alternativeNegative, alternativeNe, hdistance⟩ :=
        oneStationAlternative
          (setup.stations i).positionInKilometerCoordinates
          setup.focusPosition (stationSurface i) focusNegative
      refine ⟨alternative, alternativeNegative, alternativeNe, ?_⟩
      intro j hj
      have ji : j = i := by simpa [chosenSingleton] using hj
      subst j
      exact hdistance
    · obtain ⟨i, j, _, chosenPair⟩ := Finset.card_eq_two.mp cardTwo
      obtain ⟨alternative, alternativeNegative, alternativeNe,
          hdistanceI, hdistanceJ⟩ :=
        twoStationAlternative
          (setup.stations i).positionInKilometerCoordinates
          (setup.stations j).positionInKilometerCoordinates
          setup.focusPosition (stationSurface i) (stationSurface j)
          focusNegative
      refine ⟨alternative, alternativeNegative, alternativeNe, ?_⟩
      intro k hk
      have kCases : k = i ∨ k = j := by
        simpa [chosenPair] using hk
      rcases kCases with rfl | rfl
      · exact hdistanceI
      · exact hdistanceJ
  obtain ⟨alternative, alternativeUnderground, alternativeNe,
      alternativeDistances⟩ := alternativeExists
  let alternativeFocus : CandidateFocus :=
    { position := alternative
      originTimeSeconds := setup.originTimeSeconds }
  have alternativeFits :
      CandidateFitsStationReadings setup alternativeFocus chosen := by
    refine ⟨alternativeUnderground, ?_⟩
    intro i hi wave
    change
      distanceInKilometers alternative
          (setup.stations i).positionInKilometerCoordinates =
        speedInKilometersPerSecond (setup.waveSpeed wave) *
          ((setup.stations i).arrivalTimeSeconds wave -
            setup.originTimeSeconds)
    rw [alternativeDistances i hi]
    exact laws.travelTimeLaw wave i
  exact alternativeNe (locates alternativeFocus alternativeFits)

/-! ## Displayed choices and requested conclusion -/

/-- Labels printed beside the four candidate station counts. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Number of detection stations printed beside each answer label. -/
def displayedStationCount : AnswerChoice → ℕ
  | .A => 5
  | .B => 4
  | .C => 2
  | .D => 3

/-- The answer label recorded in the supplied dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A displayed choice agrees with a proposed minimum station count. -/
def MatchesStationCountChoice (count : ℕ) (choice : AnswerChoice) : Prop :=
  displayedStationCount choice = count

/-!
Exactly three suitably placed detection stations are necessary and sufficient
to locate the underground focus unambiguously.  This is recorded choice D.

This formalizes `thm:physics:phyx_mini_0239:target`.
-/
theorem problem_phyx_mini_0239
    (setup : EarthquakeLocalizationSetup)
    (waveData : MatchesProblemWaveData setup)
    (figure : MatchesSuppliedEarthquakeFigure setup)
    (geometry : HasNondegenerateStationGeometry setup)
    (laws : SatisfiesStraightUniformSeismicPropagation setup) :
    IsMinimumDetectionStationCount setup 3 ∧
      MatchesStationCountChoice 3 recordedDatasetAnswer := by
  constructor
  · constructor
    · refine ⟨referenceStationSet, ?_, ?_⟩
      · simp [referenceStationSet]
      · exact three_noncollinear_stations_locate_focus
          setup waveData figure geometry laws
    · intro chosen locates
      by_contra notEnough
      have hasFewerThanThree : chosen.card < 3 := by omega
      exact fewer_than_three_stations_do_not_locate_focus
        setup waveData figure geometry laws chosen hasFewerThanThree locates
  · rfl

end PhyXMiniProblems.ProblemPhyXMini0239
