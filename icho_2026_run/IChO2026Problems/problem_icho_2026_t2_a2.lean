import IChO2026Chem
import IChO2026Chem.Kinetics.BelousovZhabotinsky

/-!
# IChO 2026 T2-A2: stationary HBrO2 concentrations

This model uses the shared BZ numerical vocabulary in the units printed in the
problem.  In particular, concentrations are numerical values in `M` and the
calculation evaluates the shared mass-action readouts in `ℝ`.
-/

namespace IChO2026Problems.T2A2

open IChO2026Chem.Kinetics.BelousovZhabotinsky

/-- The requested stationary concentrations, labelled by the process in which
the species HBrO2 occurs. -/
structure HBrO2StationaryConcentrations where
  processA : MolarConcentration
  processB : MolarConcentration

/-- Kinetic constants and maintained reactant concentrations used in T2-A2.
The fields are readouts, rather than conclusions about HBrO2. -/
structure BZKineticData where
  parameters : KineticParameters
  state : State

/-- The independently supplied numerical kinetic data.  This predicate records
only problem inputs; neither stationary HBrO2 concentration is included. -/
def BZKineticData.matchesSuppliedData (data : BZKineticData) : Prop :=
  data.parameters.k1 = 10000 ∧
    data.parameters.k2 = 62000 ∧
    data.parameters.k3 = 40000000 ∧
    data.parameters.k4 = 2000000000 ∧
    data.parameters.k5 = 21 / 10 ∧
    data.state .bromate = 3 / 50 ∧
    data.state .proton = 4 / 5

/-- Adding the stationary equations for BrO2 radical and HBrO2 in Process A
gives the HBrO2 balance equation. -/
theorem processA_stationary_balance
    (data : BZKineticData)
    (xA radical ceIII : MolarConcentration)
    (hradical :
      2 * data.parameters.k1 * xA * data.state .bromate * data.state .proton -
          data.parameters.k2 * radical * ceIII * data.state .proton = 0)
    (hhbro2 :
      -data.parameters.k1 * xA * data.state .bromate * data.state .proton +
          data.parameters.k2 * radical * ceIII * data.state .proton -
            2 * data.parameters.k3 * xA ^ 2 = 0) :
    data.parameters.k1 * xA * data.state .bromate * data.state .proton -
      2 * data.parameters.k3 * xA ^ 2 = 0 := by
  linarith [hradical, hhbro2]

/-- A positive Process-A HBrO2 concentration satisfying the stationary balance
has the stated formula and, under the supplied data, the requested numerical
value in M. -/
theorem processA_hbro2_concentration
    (data : BZKineticData)
    (xA : MolarConcentration)
    (hxA : 0 < xA)
    (hk3 : 0 < data.parameters.k3)
    (hbalance :
      data.parameters.k1 * xA * data.state .bromate * data.state .proton -
        2 * data.parameters.k3 * xA ^ 2 = 0)
    (hdata : data.matchesSuppliedData) :
    xA = (data.parameters.k1 / (2 * data.parameters.k3)) * data.state .bromate *
        data.state .proton ∧
      xA = 6 / 1000000 := by
  have hxA0 : xA ≠ 0 := ne_of_gt hxA
  have hfactor :
      xA *
          (data.parameters.k1 * data.state .bromate * data.state .proton -
            2 * data.parameters.k3 * xA) = 0 := by
    calc
      xA *
          (data.parameters.k1 * data.state .bromate * data.state .proton -
            2 * data.parameters.k3 * xA) =
          data.parameters.k1 * xA * data.state .bromate * data.state .proton -
            2 * data.parameters.k3 * xA ^ 2 := by
            ring
      _ = 0 := hbalance
  have hinter :
      data.parameters.k1 * data.state .bromate * data.state .proton -
        2 * data.parameters.k3 * xA = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hxA0
  have hk3nonzero : 2 * data.parameters.k3 ≠ 0 := by positivity
  have hformula :
      xA = (data.parameters.k1 / (2 * data.parameters.k3)) * data.state .bromate *
        data.state .proton := by
    field_simp
    nlinarith [hinter]
  constructor
  · exact hformula
  · rcases hdata with ⟨hk1, _, hk3data, _, _, hbromate, hprotondata⟩
    rw [hformula, hk1, hk3data, hbromate, hprotondata]
    norm_num

/-- A positive-bromide Process-B stationary equation gives the stated HBrO2
formula and, under the supplied data, the requested numerical value in M. -/
theorem processB_hbro2_concentration
    (data : BZKineticData)
    (xB bromide : MolarConcentration)
    (hbromide : 0 < bromide)
    (hproton : 0 < data.state .proton)
    (hk4 : 0 < data.parameters.k4)
    (hstationary :
      -data.parameters.k4 * xB * bromide * data.state .proton +
          data.parameters.k5 * data.state .bromate * bromide * data.state .proton ^ 2 = 0)
    (hdata : data.matchesSuppliedData) :
    xB = (data.parameters.k5 / data.parameters.k4) * data.state .bromate *
        data.state .proton ∧
      xB = 504 / 10000000000000 := by
  have hprefix : bromide * data.state .proton ≠ 0 :=
    mul_ne_zero (ne_of_gt hbromide) (ne_of_gt hproton)
  have hfactor :
      (bromide * data.state .proton) *
          (-data.parameters.k4 * xB +
            data.parameters.k5 * data.state .bromate * data.state .proton) = 0 := by
    calc
      (bromide * data.state .proton) *
          (-data.parameters.k4 * xB +
            data.parameters.k5 * data.state .bromate * data.state .proton) =
          -data.parameters.k4 * xB * bromide * data.state .proton +
            data.parameters.k5 * data.state .bromate * bromide * data.state .proton ^ 2 := by
              ring
      _ = 0 := hstationary
  have hinter :
      -data.parameters.k4 * xB +
        data.parameters.k5 * data.state .bromate * data.state .proton = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hprefix
  have hk4nonzero : data.parameters.k4 ≠ 0 := ne_of_gt hk4
  have hformula :
      xB = (data.parameters.k5 / data.parameters.k4) * data.state .bromate *
        data.state .proton := by
    field_simp
    nlinarith [hinter]
  constructor
  · exact hformula
  · rcases hdata with ⟨_, _, _, hk4data, hk5data, hbromate, hprotondata⟩
    rw [hformula, hk4data, hk5data, hbromate, hprotondata]
    norm_num

/-- Under the respective steady-state equations and the positivity conditions
needed to eliminate their zero factors, the requested Process-A and Process-B
HBrO2 concentrations have the source values. -/
theorem steady_state_hbro2_concentrations
    (data : BZKineticData)
    (xA radical ceIII xB bromide : MolarConcentration)
    (hxA : 0 < xA)
    (hbromide : 0 < bromide)
    (hproton : 0 < data.state .proton)
    (hk3 : 0 < data.parameters.k3)
    (hk4 : 0 < data.parameters.k4)
    (hdata : data.matchesSuppliedData)
    (hradical :
      2 * data.parameters.k1 * xA * data.state .bromate * data.state .proton -
          data.parameters.k2 * radical * ceIII * data.state .proton = 0)
    (hprocessA :
      -data.parameters.k1 * xA * data.state .bromate * data.state .proton +
          data.parameters.k2 * radical * ceIII * data.state .proton -
            2 * data.parameters.k3 * xA ^ 2 = 0)
    (hprocessB :
      -data.parameters.k4 * xB * bromide * data.state .proton +
          data.parameters.k5 * data.state .bromate * bromide * data.state .proton ^ 2 = 0) :
    HBrO2StationaryConcentrations.mk xA xB =
      ⟨6 / 1000000, 504 / 10000000000000⟩ := by
  rcases processA_hbro2_concentration data xA hxA hk3
      (processA_stationary_balance data xA radical ceIII hradical hprocessA) hdata with
    ⟨_, hA⟩
  rcases processB_hbro2_concentration data xB bromide hbromide hproton hk4 hprocessB hdata with
    ⟨_, hB⟩
  cases hA
  cases hB
  rfl

end IChO2026Problems.T2A2
