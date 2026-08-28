import ArchonPhysics.FiniteNestedNormalFormExtraction

/-!
# Consumer: effective higher-order FPUT interaction

This is the exact finite-diagram interface used after excluding nonzero
three-wave resonances in equal-mass periodic alpha-FPUT.  It extracts the
effective higher-order main interaction and its explicit normal-form
boundary from the nested quadratic Picard term.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.FiniteNestedNormalFormExtraction

noncomputable section

variable {Diagram : Type*} [Fintype Diagram]

theorem problem_finite_nested_normal_form_extraction
    (coefficient : Diagram -> Complex)
    (outerMismatch innerMismatch : Diagram -> Real)
    (time : Real)
    (hinner : ∀ diagram, innerMismatch diagram ≠ 0) :
    finiteNestedPicardSum coefficient outerMismatch innerMismatch time =
      finiteEffectiveInteractionSum coefficient outerMismatch innerMismatch time -
        finiteNormalFormBoundarySum coefficient outerMismatch innerMismatch time :=
  finiteNestedPicardSum_eq_effective_sub_boundary
    coefficient outerMismatch innerMismatch time hinner

theorem problem_finite_effective_interaction_resonant_split
    (coefficient : Diagram -> Complex)
    (outerMismatch innerMismatch : Diagram -> Real)
    (time : Real) :
    finiteEffectiveInteractionSum coefficient outerMismatch innerMismatch time =
      (∑ diagram,
        if outerMismatch diagram + innerMismatch diagram = 0 then
          coefficient diagram / (Complex.I * innerMismatch diagram) * time
        else 0) +
      (∑ diagram,
        if outerMismatch diagram + innerMismatch diagram ≠ 0 then
          coefficient diagram / (Complex.I * innerMismatch diagram) *
            ArchonPhysics.NonresonantOscillatoryGain.oscillatoryIntegral
              (outerMismatch diagram + innerMismatch diagram) time
        else 0) :=
  finiteEffectiveInteractionSum_eq_resonant_add_nonresonant
    coefficient outerMismatch innerMismatch time

#print axioms problem_finite_nested_normal_form_extraction
#print axioms problem_finite_effective_interaction_resonant_split

end

end ArchonPhysicsConsumers.Thermalization
