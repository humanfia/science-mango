# Recommendations

- `PhyXMiniProblems/problem_phyx_mini_0544.lean` — The contract conflates reflection and transmission: setup.reflectionCoefficient is assumed equal to (k₂/k₁)*(transmittedAmplitude/incidentAmplitude)^2, the transmitted-flux ratio, while the source asks for reflection.
- `PhyXMiniProblems/problem_phyx_mini_0546.lean` — One active `sorry` remains in `centered_rectangular_regularization_tends_to_dirac`; its nonzero-energy claim is false as stated because `ContinuousAt` at one point does not imply local a.e. strong measurability.
- `PhyXMiniProblems/problem_phyx_mini_0788.lean` — The final theorem has an active transitive sorryAx dependency through Physlib's @[sorryful] RigidBody.solidSphere_inertiaTensor, so the required zero-sorry/axiom gate does not pass even though the assigned file contains no local placeholder or custom axiom.
- `PhyXMiniProblems/problem_phyx_mini_0825.lean` — The proof invokes the imported @[sorryful] theorem RigidBody.solidSphere_inertiaTensor, so the target has an active transitive sorryAx dependency and fails the zero-sorry/axiom-laundering requirement.
- `PhyXMiniProblems/problem_phyx_mini_0869.lean` — The frozen numerical conclusions conflict with the encoded graph and governing law, and the file contains three active `sorry` gaps, including the target's false D-match conjunct.
