import ArchonPhysics.SixWaveCollisionAlgebra

/-!
# Finite six-wave kinetic networks in weak form

This module assembles supplied resonant `3 <-> 3` channels into a finite
six-wave kinetic network.  The weak observable slope is the sum of the exact
single-channel slopes.  Action conservation, on-shell dispersion-energy
conservation, nonnegative logarithmic entropy production, and
Rayleigh--Jeans detailed balance then hold channel by channel.

The rates and channels are explicit inputs.  Therefore this module is the
target algebra for a Hamiltonian-to-kinetic limit, not a proof of that limit.
-/

namespace ArchonPhysics.FiniteSixWaveKineticNetwork

open ArchonPhysics.SixWaveCollisionAlgebra

noncomputable section

variable {Mode Channel : Type*} [Fintype Channel]

/-- Ordered incoming and outgoing triples of one six-wave reaction. -/
structure SixWaveChannel (Mode : Type*) where
  incoming : Fin 3 -> Mode
  outgoing : Fin 3 -> Mode

/-- Collision flux obtained by evaluating the action profile on the six
legs of a channel. -/
def channelFlux
    (channel : SixWaveChannel Mode) (action : Mode -> Real) : Real :=
  sixWaveCollisionFlux
    (action (channel.incoming 0))
    (action (channel.incoming 1))
    (action (channel.incoming 2))
    (action (channel.outgoing 0))
    (action (channel.outgoing 1))
    (action (channel.outgoing 2))

/-- Signed weight balance of a linear observable across one channel. -/
def channelWeightMismatch
    (channel : SixWaveChannel Mode) (weight : Mode -> Real) : Real :=
  weight (channel.incoming 0) + weight (channel.incoming 1) +
    weight (channel.incoming 2) - weight (channel.outgoing 0) -
    weight (channel.outgoing 1) - weight (channel.outgoing 2)

/-- Weak slope of a linear observable contributed by one channel. -/
def channelObservableSlope
    (channel : SixWaveChannel Mode) (rate : Real)
    (action weight : Mode -> Real) : Real :=
  rate * channelFlux channel action * channelWeightMismatch channel weight

/-- Total weak collision slope over a finite family of channels. -/
def finiteSixWaveObservableSlope
    (channels : Channel -> SixWaveChannel Mode) (rate : Channel -> Real)
    (action weight : Mode -> Real) : Real :=
  ∑ collision,
    channelObservableSlope (channels collision) (rate collision) action weight

/-- Total logarithmic entropy production over the finite channel family. -/
def finiteSixWaveEntropyProduction
    (channels : Channel -> SixWaveChannel Mode) (rate : Channel -> Real)
    (action : Mode -> Real) : Real :=
  ∑ collision,
    sixWaveEntropyProduction (rate collision)
      (action ((channels collision).incoming 0))
      (action ((channels collision).incoming 1))
      (action ((channels collision).incoming 2))
      (action ((channels collision).outgoing 0))
      (action ((channels collision).outgoing 1))
      (action ((channels collision).outgoing 2))

/-- Channelwise action balance. -/
@[simp] theorem channelWeightMismatch_one
    (channel : SixWaveChannel Mode) :
    channelWeightMismatch channel (fun _ => 1) = 0 := by
  simp [channelWeightMismatch]

/-- Every finite `3 <-> 3` network conserves total wave action in weak
form, independently of its rates. -/
theorem finiteSixWaveObservableSlope_one_eq_zero
    (channels : Channel -> SixWaveChannel Mode) (rate : Channel -> Real)
    (action : Mode -> Real) :
    finiteSixWaveObservableSlope channels rate action (fun _ => 1) = 0 := by
  simp [finiteSixWaveObservableSlope, channelObservableSlope]

/-- A dispersion is resonant on a channel when the three incoming
frequencies sum to the three outgoing frequencies. -/
def ChannelResonant
    (channel : SixWaveChannel Mode) (frequency : Mode -> Real) : Prop :=
  frequency (channel.incoming 0) + frequency (channel.incoming 1) +
      frequency (channel.incoming 2) =
    frequency (channel.outgoing 0) + frequency (channel.outgoing 1) +
      frequency (channel.outgoing 2)

/-- A network of on-shell channels conserves total dispersion energy in
weak form. -/
theorem finiteSixWaveObservableSlope_frequency_eq_zero
    (channels : Channel -> SixWaveChannel Mode) (rate : Channel -> Real)
    (action frequency : Mode -> Real)
    (hresonant : ∀ collision, ChannelResonant (channels collision) frequency) :
    finiteSixWaveObservableSlope channels rate action frequency = 0 := by
  unfold finiteSixWaveObservableSlope
  apply Finset.sum_eq_zero
  intro collision _hcollision
  unfold channelObservableSlope channelWeightMismatch ChannelResonant at *
  rw [hresonant collision]
  ring

/-- Nonnegative rates and positive actions give nonnegative entropy
production for the entire finite network. -/
theorem finiteSixWaveEntropyProduction_nonneg
    (channels : Channel -> SixWaveChannel Mode) (rate : Channel -> Real)
    (action : Mode -> Real)
    (hrate : ∀ collision, 0 ≤ rate collision)
    (haction : ∀ mode, 0 < action mode) :
    0 ≤ finiteSixWaveEntropyProduction channels rate action := by
  unfold finiteSixWaveEntropyProduction
  apply Finset.sum_nonneg
  intro collision _hcollision
  exact sixWaveEntropyProduction_nonneg
    (hrate collision)
    (haction ((channels collision).incoming 0))
    (haction ((channels collision).incoming 1))
    (haction ((channels collision).incoming 2))
    (haction ((channels collision).outgoing 0))
    (haction ((channels collision).outgoing 1))
    (haction ((channels collision).outgoing 2))

/-- A Rayleigh--Jeans action profile kills every flux in an on-shell finite
network. -/
theorem channelFlux_rayleighJeans_eq_zero
    (channel : SixWaveChannel Mode) (frequency : Mode -> Real)
    (chemical inverseTemperature : Real)
    (hresonant : ChannelResonant channel frequency) :
    channelFlux channel
      (fun mode => rayleighJeansAction chemical inverseTemperature
        (frequency mode)) = 0 := by
  unfold channelFlux ChannelResonant at *
  exact sixWaveCollisionFlux_rayleighJeans_eq_zero
    chemical inverseTemperature
    (frequency (channel.incoming 0))
    (frequency (channel.incoming 1))
    (frequency (channel.incoming 2))
    (frequency (channel.outgoing 0))
    (frequency (channel.outgoing 1))
    (frequency (channel.outgoing 2)) hresonant

/-- Consequently every linear observable has zero collision slope at the
Rayleigh--Jeans profile. -/
theorem finiteSixWaveObservableSlope_rayleighJeans_eq_zero
    (channels : Channel -> SixWaveChannel Mode) (rate : Channel -> Real)
    (frequency weight : Mode -> Real) (chemical inverseTemperature : Real)
    (hresonant : ∀ collision, ChannelResonant (channels collision) frequency) :
    finiteSixWaveObservableSlope channels rate
      (fun mode => rayleighJeansAction chemical inverseTemperature
        (frequency mode)) weight = 0 := by
  unfold finiteSixWaveObservableSlope channelObservableSlope
  apply Finset.sum_eq_zero
  intro collision _hcollision
  rw [channelFlux_rayleighJeans_eq_zero
    (channels collision) frequency chemical inverseTemperature
      (hresonant collision)]
  ring

/-- Weak formulation of a finite six-wave kinetic trajectory. -/
def SolvesFiniteSixWaveKineticWeakly
    [Fintype Mode]
    (channels : Channel -> SixWaveChannel Mode) (rate : Channel -> Real)
    (trajectory : Real -> Mode -> Real) : Prop :=
  ∀ time weight,
    HasDerivAt
      (fun s => ∑ mode, weight mode * trajectory s mode)
      (finiteSixWaveObservableSlope channels rate (trajectory time) weight)
      time

/-- The time-independent Rayleigh--Jeans profile is an exact weak solution
of every resonant finite six-wave network. -/
theorem rayleighJeans_solvesFiniteSixWaveKineticWeakly
    [Fintype Mode]
    (channels : Channel -> SixWaveChannel Mode) (rate : Channel -> Real)
    (frequency : Mode -> Real) (chemical inverseTemperature : Real)
    (hresonant : ∀ collision, ChannelResonant (channels collision) frequency) :
    SolvesFiniteSixWaveKineticWeakly channels rate
      (fun _time mode =>
        rayleighJeansAction chemical inverseTemperature (frequency mode)) := by
  intro time weight
  rw [finiteSixWaveObservableSlope_rayleighJeans_eq_zero
    channels rate frequency weight chemical inverseTemperature hresonant]
  simpa using (hasDerivAt_const time
    (∑ mode, weight mode *
      rayleighJeansAction chemical inverseTemperature (frequency mode)))

/-- Every weak solution conserves total wave action infinitesimally. -/
theorem hasDerivAt_totalAction_zero_of_solvesWeakly
    [Fintype Mode]
    (channels : Channel -> SixWaveChannel Mode) (rate : Channel -> Real)
    (trajectory : Real -> Mode -> Real)
    (hsolve : SolvesFiniteSixWaveKineticWeakly channels rate trajectory)
    (time : Real) :
    HasDerivAt (fun s => ∑ mode, trajectory s mode) 0 time := by
  have h := hsolve time (fun _ => 1)
  rw [finiteSixWaveObservableSlope_one_eq_zero] at h
  simpa using h

/-- Every weak solution supported on resonant channels conserves total
dispersion energy infinitesimally. -/
theorem hasDerivAt_totalEnergy_zero_of_solvesWeakly
    [Fintype Mode]
    (channels : Channel -> SixWaveChannel Mode) (rate : Channel -> Real)
    (trajectory : Real -> Mode -> Real) (frequency : Mode -> Real)
    (hsolve : SolvesFiniteSixWaveKineticWeakly channels rate trajectory)
    (hresonant : ∀ collision, ChannelResonant (channels collision) frequency)
    (time : Real) :
    HasDerivAt
      (fun s => ∑ mode, frequency mode * trajectory s mode) 0 time := by
  have h := hsolve time frequency
  rw [finiteSixWaveObservableSlope_frequency_eq_zero
    channels rate (trajectory time) frequency hresonant] at h
  exact h

end

end ArchonPhysics.FiniteSixWaveKineticNetwork
