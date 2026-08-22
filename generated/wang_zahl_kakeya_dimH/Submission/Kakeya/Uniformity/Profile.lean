import Submission.Kakeya.Uniformity.DyadicLevel

namespace Submission.Kakeya.Uniformity

/-!
# Multiscale profiles

A multiscale profile packages a finite family together with a finite set of
scales and one dyadic label for every family member at every scale.  The
`UniformOn` predicate records the exact constancy property later produced by
the multiscale pigeonhole argument.
-/

/-- Finite family data with one dyadic observable at each finite scale. -/
structure MultiscaleProfile (α : Type*) [DecidableEq α] where
  family : Finset α
  scales : Finset Nat
  label : Nat → α → DyadicLevel

/-- A subfamily is uniform on a set of scales when its dyadic label is
constant at each of those scales. -/
def MultiscaleProfile.UniformOn
    {α : Type*} [DecidableEq α] (profile : MultiscaleProfile α)
    (refined : Finset α) (scales : Finset Nat) : Prop :=
  ∀ r ∈ scales, ∃ level : DyadicLevel,
    ∀ x ∈ refined, profile.label r x = level

/-- The defining characterization of multiscale uniformity. -/
theorem MultiscaleProfile.uniformOn_iff
    {α : Type*} [DecidableEq α] (profile : MultiscaleProfile α)
    (refined : Finset α) (scales : Finset Nat) :
    profile.UniformOn refined scales ↔
      ∀ r ∈ scales, ∃ level : DyadicLevel,
        ∀ x ∈ refined, profile.label r x = level :=
  Iff.rfl

end Submission.Kakeya.Uniformity
