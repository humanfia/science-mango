import ArchonPhysics.LennardJonesStoppedHigherRemainderProbability
import ArchonPhysics.MicroscopicErrorProbabilityUpgrade

/-!
# Project probability law for the higher Lennard--Jones remainder

The stopped-flow estimate for the force terms beyond the retained FPUT
`alpha-beta` jet is naturally real-valued.  This module converts its explicit
good-event certificate into the `ENNReal` convergence-in-probability interface
used by the project-level microscopic--kinetic reduction.

This is deliberately only an adapter for the higher Taylor remainder.  It
does not estimate the retained cubic/quartic dynamics, prove persistence of
the good tube, or identify a kinetic collision operator.
-/

namespace ArchonPhysics.LennardJonesHigherRemainderProbabilityUpgrade

open Filter MeasureTheory Set Topology
open ArchonPhysics
open ArchonPhysics.ThermalizationTransfer
open ArchonPhysics.LennardJonesStoppedHigherRemainderProbability
open ArchonPhysics.MicroscopicErrorProbabilityUpgrade

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The extended-nonnegative version of a nonnegative real microscopic error. -/
def ennrealError (error : Nat → Omega → Real) : Nat → Omega → ENNReal :=
  fun j omega ↦ ENNReal.ofReal (error j omega)

theorem measurable_ennrealError
    (error : Nat → Omega → Real)
    (herror : ∀ j, Measurable (error j)) :
    ∀ j, Measurable (ennrealError error j) := by
  intro j
  exact ENNReal.measurable_ofReal.comp (herror j)

/-- A vanishing real-valued good-event complement probability also vanishes
as an `ENNReal` measure. -/
theorem measure_goodEvent_compl_tendsto_zero
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    (goodEvent : Nat → Set Omega)
    (hreal : Tendsto
      (fun j ↦ probability.real (goodEvent j)ᶜ) atTop (nhds 0)) :
    Tendsto (fun j ↦ probability (goodEvent j)ᶜ) atTop (nhds 0) := by
  have hofReal := ENNReal.tendsto_ofReal hreal
  have hfun :
      (fun j ↦ ENNReal.ofReal (probability.real (goodEvent j)ᶜ)) =
        (fun j ↦ probability (goodEvent j)ᶜ) := by
    funext j
    exact ofReal_measureReal (by finiteness)
  rw [hfun, ENNReal.ofReal_zero] at hofReal
  exact hofReal

/-- The higher-remainder certificate supplies exactly the project's
zero-neighbourhood law after applying `ENNReal.ofReal` to the error. -/
theorem localUniformError_zero_law_of_certificate
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    (coupling : Nat → Real) (coefficient : Real)
    (error : Nat → Omega → Real)
    (certificate : VanishingGoodEventRemainderCertificate
      probability coupling coefficient error)
    (hcoupling : Tendsto coupling atTop (nhds 0)) :
    ∀ U : Set ENNReal, MeasurableSet U → U ∈ 𝓝 0 →
      Tendsto
        (fun j ↦ probability ((ennrealError error j) ⁻¹' U))
        atTop (nhds 1) := by
  apply localUniformError_zero_law_of_goodEvent_budget
    probability (ennrealError error)
      (measurable_ennrealError error certificate.error_measurable)
      certificate.goodEvent
      (fun j ↦ ENNReal.ofReal (coefficient * coupling j))
      (fun j ↦ probability (certificate.goodEvent j)ᶜ)
  · intro j omega homega
    exact ENNReal.ofReal_le_ofReal
      (certificate.error_le_on_good j omega homega)
  · have hscale : Tendsto (fun j ↦ coefficient * coupling j)
        atTop (nhds (coefficient * 0)) :=
      tendsto_const_nhds.mul hcoupling
    simpa using ENNReal.tendsto_ofReal hscale
  · intro j
    exact le_rfl
  · exact measure_goodEvent_compl_tendsto_zero probability
      certificate.goodEvent certificate.good_compl_probability_zero

/-- Bundled convergence-in-probability form of the higher LJ remainder
estimate. -/
theorem convergesInProbabilityTo_zero_of_certificate
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    (coupling : Nat → Real) (coefficient : Real)
    (error : Nat → Omega → Real)
    (certificate : VanishingGoodEventRemainderCertificate
      probability coupling coefficient error)
    (hcoupling : Tendsto coupling atTop (nhds 0)) :
    ConvergesInProbabilityTo probability (ennrealError error) 0 := by
  exact ⟨measurable_ennrealError error certificate.error_measurable,
    localUniformError_zero_law_of_certificate
      probability coupling coefficient error certificate hcoupling⟩
end

end ArchonPhysics.LennardJonesHigherRemainderProbabilityUpgrade
