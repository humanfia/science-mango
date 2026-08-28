import ArchonPhysics.FourWaveCollisionAlgebra

/-!
# Finite four-wave kinetic networks in weak form

After the nonresonant quadratic interaction of equal-mass alpha-FPUT is
removed, the thermodynamic-limit kinetic target is a `2 <-> 2` collision
equation.  This module assembles a supplied finite family of resonant
quartets into that equation in weak form.

The construction proves, channel by channel, conservation of wave action
and on-shell dispersion energy, nonnegative logarithmic entropy production,
and stationarity of every Rayleigh--Jeans profile.  The rates are explicit
inputs: identifying them with the squared effective alpha-FPUT vertex and
proving the microscopic joint limit are separate upstream obligations.
-/

namespace ArchonPhysics.FiniteFourWaveKineticNetwork

open ArchonPhysics.FourWaveCollisionAlgebra

noncomputable section

variable {Mode Channel : Type*} [Fintype Channel]

/-- Ordered incoming and outgoing pairs of one four-wave reaction. -/
structure FourWaveChannel (Mode : Type*) where
  incoming : Fin 2 -> Mode
  outgoing : Fin 2 -> Mode

/-- Collision flux evaluated on the four legs of a channel. -/
def channelFlux
    (channel : FourWaveChannel Mode) (action : Mode -> Real) : Real :=
  fourWaveCollisionFlux
    (action (channel.incoming 0))
    (action (channel.incoming 1))
    (action (channel.outgoing 0))
    (action (channel.outgoing 1))

/-- Signed balance of a linear observable across one channel. -/
def channelWeightMismatch
    (channel : FourWaveChannel Mode) (weight : Mode -> Real) : Real :=
  weight (channel.incoming 0) + weight (channel.incoming 1) -
    weight (channel.outgoing 0) - weight (channel.outgoing 1)

/-- Weak slope of a linear observable contributed by one channel. -/
def channelObservableSlope
    (channel : FourWaveChannel Mode) (rate : Real)
    (action weight : Mode -> Real) : Real :=
  rate * channelFlux channel action * channelWeightMismatch channel weight

/-- Total weak collision slope over a finite family of channels. -/
def finiteFourWaveObservableSlope
    (channels : Channel -> FourWaveChannel Mode) (rate : Channel -> Real)
    (action weight : Mode -> Real) : Real :=
  ∑ collision,
    channelObservableSlope (channels collision) (rate collision) action weight

/-- Total logarithmic entropy production over the finite channel family. -/
def finiteFourWaveEntropyProduction
    (channels : Channel -> FourWaveChannel Mode) (rate : Channel -> Real)
    (action : Mode -> Real) : Real :=
  ∑ collision,
    fourWaveEntropyProduction (rate collision)
      (action ((channels collision).incoming 0))
      (action ((channels collision).incoming 1))
      (action ((channels collision).outgoing 0))
      (action ((channels collision).outgoing 1))

@[simp] theorem channelWeightMismatch_one
    (channel : FourWaveChannel Mode) :
    channelWeightMismatch channel (fun _ => 1) = 0 := by
  simp [channelWeightMismatch]

/-- Every finite `2 <-> 2` network conserves total wave action in weak
form, independently of its rates. -/
theorem finiteFourWaveObservableSlope_one_eq_zero
    (channels : Channel -> FourWaveChannel Mode) (rate : Channel -> Real)
    (action : Mode -> Real) :
    finiteFourWaveObservableSlope channels rate action (fun _ => 1) = 0 := by
  simp [finiteFourWaveObservableSlope, channelObservableSlope]

/-- A quartet is on shell when its two incoming frequencies equal its two
outgoing frequencies. -/
def ChannelResonant
    (channel : FourWaveChannel Mode) (frequency : Mode -> Real) : Prop :=
  frequency (channel.incoming 0) + frequency (channel.incoming 1) =
    frequency (channel.outgoing 0) + frequency (channel.outgoing 1)

/-- A network of on-shell channels conserves total dispersion energy in
weak form. -/
theorem finiteFourWaveObservableSlope_frequency_eq_zero
    (channels : Channel -> FourWaveChannel Mode) (rate : Channel -> Real)
    (action frequency : Mode -> Real)
    (hresonant : ∀ collision, ChannelResonant (channels collision) frequency) :
    finiteFourWaveObservableSlope channels rate action frequency = 0 := by
  unfold finiteFourWaveObservableSlope
  apply Finset.sum_eq_zero
  intro collision _hcollision
  unfold channelObservableSlope channelWeightMismatch ChannelResonant at *
  rw [hresonant collision]
  ring

/-- Nonnegative rates and positive actions give nonnegative entropy
production for the whole finite network. -/
theorem finiteFourWaveEntropyProduction_nonneg
    (channels : Channel -> FourWaveChannel Mode) (rate : Channel -> Real)
    (action : Mode -> Real)
    (hrate : ∀ collision, 0 ≤ rate collision)
    (haction : ∀ mode, 0 < action mode) :
    0 ≤ finiteFourWaveEntropyProduction channels rate action := by
  unfold finiteFourWaveEntropyProduction
  apply Finset.sum_nonneg
  intro collision _hcollision
  exact fourWaveEntropyProduction_nonneg
    (hrate collision)
    (haction ((channels collision).incoming 0))
    (haction ((channels collision).incoming 1))
    (haction ((channels collision).outgoing 0))
    (haction ((channels collision).outgoing 1))

/-- A Rayleigh--Jeans action profile kills the flux of every on-shell
quartet. -/
theorem channelFlux_rayleighJeans_eq_zero
    (channel : FourWaveChannel Mode) (frequency : Mode -> Real)
    (chemical inverseTemperature : Real)
    (hresonant : ChannelResonant channel frequency) :
    channelFlux channel
      (fun mode => fourWaveRayleighJeansAction chemical inverseTemperature
        (frequency mode)) = 0 := by
  unfold channelFlux ChannelResonant at *
  exact fourWaveCollisionFlux_rayleighJeans_eq_zero
    chemical inverseTemperature
    (frequency (channel.incoming 0))
    (frequency (channel.incoming 1))
    (frequency (channel.outgoing 0))
    (frequency (channel.outgoing 1)) hresonant

/-- Consequently every weak observable has zero collision slope at a
Rayleigh--Jeans profile. -/
theorem finiteFourWaveObservableSlope_rayleighJeans_eq_zero
    (channels : Channel -> FourWaveChannel Mode) (rate : Channel -> Real)
    (frequency weight : Mode -> Real) (chemical inverseTemperature : Real)
    (hresonant : ∀ collision, ChannelResonant (channels collision) frequency) :
    finiteFourWaveObservableSlope channels rate
      (fun mode => fourWaveRayleighJeansAction chemical inverseTemperature
        (frequency mode)) weight = 0 := by
  unfold finiteFourWaveObservableSlope channelObservableSlope
  apply Finset.sum_eq_zero
  intro collision _hcollision
  rw [channelFlux_rayleighJeans_eq_zero
    (channels collision) frequency chemical inverseTemperature
      (hresonant collision)]
  ring

/-- Weak formulation of a finite four-wave kinetic trajectory. -/
def SolvesFiniteFourWaveKineticWeakly
    [Fintype Mode]
    (channels : Channel -> FourWaveChannel Mode) (rate : Channel -> Real)
    (trajectory : Real -> Mode -> Real) : Prop :=
  ∀ time weight,
    HasDerivAt
      (fun s => ∑ mode, weight mode * trajectory s mode)
      (finiteFourWaveObservableSlope channels rate (trajectory time) weight)
      time

/-- A time-independent Rayleigh--Jeans profile is an exact weak solution of
every resonant finite four-wave network. -/
theorem rayleighJeans_solvesFiniteFourWaveKineticWeakly
    [Fintype Mode]
    (channels : Channel -> FourWaveChannel Mode) (rate : Channel -> Real)
    (frequency : Mode -> Real) (chemical inverseTemperature : Real)
    (hresonant : ∀ collision, ChannelResonant (channels collision) frequency) :
    SolvesFiniteFourWaveKineticWeakly channels rate
      (fun _time mode =>
        fourWaveRayleighJeansAction chemical inverseTemperature
          (frequency mode)) := by
  intro time weight
  rw [finiteFourWaveObservableSlope_rayleighJeans_eq_zero
    channels rate frequency weight chemical inverseTemperature hresonant]
  simpa using (hasDerivAt_const time
    (∑ mode, weight mode *
      fourWaveRayleighJeansAction chemical inverseTemperature
        (frequency mode)))

/-- Every weak solution conserves total wave action infinitesimally. -/
theorem hasDerivAt_totalAction_zero_of_solvesWeakly
    [Fintype Mode]
    (channels : Channel -> FourWaveChannel Mode) (rate : Channel -> Real)
    (trajectory : Real -> Mode -> Real)
    (hsolve : SolvesFiniteFourWaveKineticWeakly channels rate trajectory)
    (time : Real) :
    HasDerivAt (fun s => ∑ mode, trajectory s mode) 0 time := by
  have h := hsolve time (fun _ => 1)
  rw [finiteFourWaveObservableSlope_one_eq_zero] at h
  simpa using h

/-- Every weak solution supported on resonant quartets conserves total
dispersion energy infinitesimally. -/
theorem hasDerivAt_totalEnergy_zero_of_solvesWeakly
    [Fintype Mode]
    (channels : Channel -> FourWaveChannel Mode) (rate : Channel -> Real)
    (trajectory : Real -> Mode -> Real) (frequency : Mode -> Real)
    (hsolve : SolvesFiniteFourWaveKineticWeakly channels rate trajectory)
    (hresonant : ∀ collision, ChannelResonant (channels collision) frequency)
    (time : Real) :
    HasDerivAt
      (fun s => ∑ mode, frequency mode * trajectory s mode) 0 time := by
  have h := hsolve time frequency
  rw [finiteFourWaveObservableSlope_frequency_eq_zero
    channels rate (trajectory time) frequency hresonant] at h
  exact h

end

end ArchonPhysics.FiniteFourWaveKineticNetwork
