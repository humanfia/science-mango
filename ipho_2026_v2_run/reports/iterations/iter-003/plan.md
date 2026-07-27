# Iteration 003 prover plan

Bounded scope: exactly the 22 deterministically selected theory targets below, in the supplied order. All are new Proof Review attempts (`attempts = 0`); there are no retry, redraft, infrastructure-blocked, or exhausted targets. Preserve every theorem statement and physical hypothesis. The six user-skipped experimental targets remain out of scope.

1. **`IPhO2026Problems/problem_IPhO_2026_1_A_1.lean`** (6 placeholders)
   - Project the Figure 1a fields directly to prove the opening-area readout. For the critical balance, rewrite the hinge/contact forces to zero and then the contact-torque law; `linarith` should close the reduced balance.
   - Substitute the pressure, effective-weight, area, and lever-arm laws into that balance. Establish `sqrt 2 ≠ 0` and the required positive density/length factors, then use `field_simp` and `nlinarith`/`ring_nf` to isolate the side length.
   - Rewrite the density as `3ρ₀`, cancel positive `ρ₀`, and normalize to `Δh/(2*sqrt 2)`. Prove the decimal rounding bound by squaring rational bounds for `sqrt 2` under positivity, then assemble the requested final conjunction from the intermediate lemmas.

2. **`IPhO2026Problems/problem_IPhO_2026_1_B_1.lean`** (1 placeholder)
   - Unfold the turning-point energy readout and equate its values at the initial and outer turning points. Rewrite `μ = 4`, `r₀ = 100a₀`, and the Bohr-radius relation, clear only denominators proved nonzero from the law fields, and factor the resulting quadratic.
   - The two roots are the initial radius and `(1600/9)a₀`; use `r₀ < rmax` (and `a₀ > 0`) to reject the initial-radius root. Finish with `nlinarith` after the factorization.

3. **`IPhO2026Problems/problem_IPhO_2026_1_B_2.lean`** (5 placeholders)
   - For the conic-limit lemma, combine continuity of `cos` with the angle limit. Show that an unbounded positive radius forces `1-e*cos θ∞ = 0`; use the `[0,π]` branch and the injectivity/range characterization of `arccos` to select `θ∞ = arccos (1/e)`.
   - Normalize the source laws at `μ = 15/2` by `field_simp`/`ring_nf` to obtain `e = 7/2`, then reuse the conic lemma and simplify its reciprocal to `2/7`. Unfold the Figure 1b signed-angle definition to prove the `θ∞-π/2` conversion.
   - For the final sign and rounding certificate, rewrite `arccos x - π/2` as `-arcsin x`. Prove the required rational interval for `arcsin (2/7)` with a monotone Taylor bound (and standard rational bounds for `π`), then convert radians to degrees and discharge the rational endpoints with `norm_num`.

4. **`IPhO2026Problems/problem_IPhO_2026_1_C_1.lean`** (7 placeholders)
   - Expand the event definitions; eliminate the two momentum vectors with momentum conservation and use the norm/inner-product angle law to derive the scalar energy equation.
   - Prove the radial-energy lower bound by splitting at `θ < π/2`, completing the square in the momentum magnitude, and using the validity/nonnegativity fields. For the reverse direction of the kinematic iff, construct the collinear minimizing momenta on the forward branch and an arbitrarily close positive-momentum witness on the backscattering branch.
   - Analyze the resulting energy quadratic: prove discriminant nonnegativity, verify the displayed lower root, and show allowed positive frequencies are exactly at/above it (strictly above for the limiting backscatter case). Use that characterization to supply both the lower-bound and epsilon-witness clauses of `IsDissociationThreshold`, with `effectiveThresholdAngle` simplified in the two angle cases.

5. **`IPhO2026Problems/problem_IPhO_2026_1_C_2.lean`** (1 placeholder)
   - Unfold the requested eV readout, rewrite the previous-part lower-root equation and the three supplied readouts, and normalize the SI/eV/amu constants and `sin (π/6)`.
   - Isolate the remaining square root. Certify tight rational lower and upper bounds by comparing nonnegative squares; propagate them through the positive denominator to the `5e-14` rounding interval, closing the rational arithmetic with `norm_num`/`linarith`.

6. **`IPhO2026Problems/problem_IPhO_2026_2_A_1.lean`** (4 placeholders)
   - Solve the angular closure for the first-impact angle after proving `2N+1 ≠ 0`. Prove the complementary-angle identity with `field_simp` and `ring`.
   - Rewrite the sine form through that identity and `Real.sin_pi_div_two_sub` to obtain the cosine form.
   - Extract the limiting-ray witness from `laws.limiting_ray_geometry`; rewrite its projection by the solved angle, and return both official threshold formulas using the trigonometric bridge.

7. **`IPhO2026Problems/problem_IPhO_2026_2_B_1.lean`** (5 placeholders)
   - The tangency-elimination lemma is direct structure elimination. Unfold `LimitingTangentRay` to turn its signed-distance equation into the radius equality.
   - For the maximum ray, obtain the tangent witness, rewrite its canonical incidence point and reflected direction, and expand `cross2D`; simplify double-angle identities to the canonical limiting-radius formula.
   - Prove the two-term trigonometric formula by `simp` on the geometric definitions followed by `ring`. Identify the universal coefficients by applying the functional identity at angles that separate `sin θ` and `sin 2θ` (for example `π/2` then `π/4`), and finish the requested coefficient pair.

8. **`IPhO2026Problems/problem_IPhO_2026_2_B_2.lean`** (3 placeholders)
   - Rewrite the B.1 radius equation with `sin (2θ) = 2 sin θ cos θ` and factor it by `ring`.
   - Substitute both power balances and projected widths. Use positive irradiance, axial length, and baseline width to justify cancellation and prove the width-ratio lemma.
   - Replace the container radius with its factorization, establish the needed nonzero factors from the geometry/ray hypotheses, and use `field_simp` plus `ring` to reach `1/(1-cos θmax)`.

9. **`IPhO2026Problems/problem_IPhO_2026_2_B_3.lean`** (3 placeholders)
   - Insert the fivefold-power equation into the previous B.2 ratio, cancel the positive baseline power, and solve for `cos θmax = 4/5`.
   - From the nonnegative `[0,π/2]` branch and `sin²+cos²=1`, select `sin θmax = 3/5`. Substitute both values and the double-angle identity into the B.1 radius law to get `3/25 m`.
   - Normalize `3/25 = 12/100` and the metre-to-centimetre projection, then form the final conjunction by reusing the two lemmas.

10. **`IPhO2026Problems/problem_IPhO_2026_2_C_1.lean`** (4 placeholders)
    - Expand the vector specular-reflection equation with the Figure 2g hit point, radial normal, and selected down-left branch; simplify the double-angle components.
    - Derive the slope from the direction ratio, proving its denominator nonzero from the interaction branch, and rewrite the quotient as `cot (2θ)`.
    - Insert the length-valued hit coordinates into line incidence, use the slope result, and simplify the trigonometry to `R/(2 cos θ)`. The final theorem is the conjunction of these two readouts.

11. **`IPhO2026Problems/problem_IPhO_2026_2_C_2.lean`** (1 placeholder)
    - First derive eventual exact formulas for ray B's slope and SI intercept from the Figure 2g and reflection hypotheses.
    - On a neighborhood where the supplied sine/cosine denominators stay nonzero, prove the two scalar functions have bounded second derivatives. Apply the local second-order Taylor remainder theorem at `0` to `cot (2*(θ+Δθ))` and `R/(2*cos (θ+Δθ))`, simplify their values/derivatives, and transfer the resulting `IsBigO` facts through the eventual equalities.

12. **`IPhO2026Problems/problem_IPhO_2026_2_C_3.lean`** (6 placeholders)
    - Prove the impact point lies on the upper semicircle by expanding coordinates and using `sin²+cos²=1`. Establish the quoted C.2 `IsBigO` expansions via the same local second-derivative/Taylor argument.
    - Apply both reflected support-line laws to a neighboring intersection and subtract the affine equations. Solve for its coordinates while keeping the admissible-angle denominators nonzero.
    - Take `δ → 0` using the first-order expansions (or the corresponding derivative quotient limits), then simplify the limiting trigonometric expressions with `field_simp`, `ring`, and double-angle identities to `Xc = R sin³ θ` and `Yc = (R/2) cos θ (2-cos 2θ)`. Package the coordinate limits into the final theorem.

13. **`IPhO2026Problems/problem_IPhO_2026_2_C_4.lean`** (2 placeholders)
    - For fixed `θ ≠ 0`, use convergence of `|Δθ|` to zero with radius `|θ|` to prove the eventual smallness lemma.
    - Unfold the C.3 caustic readouts. Combine `sin θ ~ θ`, the second-order cosine expansion, and rpow product/power laws (using positive radius) to show `Xc ~ R θ³` and `Yc-R/2 ~ (3R/4)θ²`, hence the required punctured-neighborhood `2/3` power equivalence.
    - Discharge denominator nonzero and `Nat.Coprime 2 3` by computation, and normalize the coefficient to `(3/4) R^(1/3)`.

14. **`IPhO2026Problems/problem_IPhO_2026_3_A_1.lean`** (1 placeholder)
    - Unfold Ampère's law and the mean loop length. Rewrite the torus volume law `V = (2πR)A`, use positivity to justify the volume/loop-length cancellation, and isolate `H` with `field_simp` and `ring`.

15. **`IPhO2026Problems/problem_IPhO_2026_3_A_2.lean`** (2 placeholders)
    - Rewrite the flux-per-turn, linkage, Faraday, and source-work fields in sequence; `ring` gives `I N A dB`.
    - Substitute the locally recorded A.1 field relation `H = NIA/V`; use positive volume to clear the denominator and rearrange the intermediate result to `V H dB`.

16. **`IPhO2026Problems/problem_IPhO_2026_3_A_3.lean`** (4 placeholders)
    - Prove SI extensionality with the Physlib conversion/extensionality API, and prove the SI readout of `energyFromSI` by simplification of `CarriesDimension.toDimensionful`.
    - At the scalar SI level, rewrite `dB = μ₀(dH+dM)`, the A.2 source work, and the vacuum-core contribution. Subtract and use `ring` to obtain `μ₀ V H dM`.
    - Lift the scalar equality back to the dimensionful energy carrier with the SI extensionality lemma; keep the positive-into-system sign convention unchanged.

17. **`IPhO2026Problems/problem_IPhO_2026_3_B_1.lean`** (4 placeholders)
    - The constant-temperature field makes `dU/ds = C_M dT/ds = 0`. Differentiate the equation of state along the oriented linear field sweep to obtain the displayed constant magnetization rate.
    - Use the first-law sign convention to set heat rate to minus magnetic-work rate, then substitute the magnetization rate and the affine field strength.
    - Integrate the affine field over `[0,1]` (equivalently use the derivative of `H(s)^2/2`) and normalize `(Hf-Hi)(Hf+Hi)` to `Hf²-Hi²`, retaining the signed formula for either sweep orientation.

18. **`IPhO2026Problems/problem_IPhO_2026_3_B_2.lean`** (3 placeholders)
    - Expand the differential laws and use the product/quotient rules to derive the reduced adiabatic ODE.
    - Differentiate `T²/(λ+μ₀KH²)` on the process interval; positivity makes its denominator nonzero, and the ODE reduces the derivative to zero. Apply the derivative-zero-on-interval theorem to obtain the invariant.
    - Evaluate at endpoints, cross-multiply the positive scales, and use positive final temperature to select the positive square root. Subtract the initial temperature and normalize to the stated `ΔT` formula.

19. **`IPhO2026Problems/problem_IPhO_2026_3_C_2.lean`** (2 placeholders)
    - Rewrite the two isothermal heat laws and Carnot entropy balance, then eliminate field strength with the equation of state. Cancel only the explicitly positive common constants and use `ring` to obtain the magnetization-square balance.
    - Rearrange it to `M₁² = M₂²-M₃²+M₄²`; rewrite the radicand accordingly and use the nonnegative magnitude branch with `Real.sqrt_sq_eq_abs`/`abs_of_nonneg`.

20. **`IPhO2026Problems/problem_IPhO_2026_3_C_3.lean`** (1 placeholder)
    - Rewrite the supplied readouts through the torus mass/volume balance, equation of state, Carnot temperature pattern, previous C.2 relation, and isothermal heat law to bound `Qc` around `0.129 J`.
    - Insert that bound into the helium calorimetry equation. Use positivity of density, volume, and heat capacity to propagate the interval to the cooling magnitude and then to final temperature; finish the three rational rounding envelopes with `norm_num`/`linarith` and certified square-root bounds where needed.

21. **`IPhO2026Problems/problem_IPhO_2026_3_C_4.lean`** (2 placeholders)
    - Eliminate the hot/cold heat rates from the Carnot ratio, body heat balance, and refrigerator power balance. Positivity justifies denominator clearing and yields the instantaneous cooling equation.
    - Define the antiderivative along the temperature path corresponding to `Th*log T - T`; prove its derivative is the constant fixed by `P/C` using the cooling equation and trajectory positivity. Apply the fundamental theorem/derivative-zero interval lemma between the endpoint times, rewrite the endpoint temperatures, and rearrange to the stated logarithmic elapsed-time formula.

22. **`IPhO2026Problems/problem_IPhO_2026_3_C_5.lean`** (1 placeholder)
    - Unfold overall COP. Rewrite total cold heat as `C(T₀-T)`, total work as `P*t`, and substitute the local C.4 elapsed-time result.
    - Use strict cooling and positive heat capacity/power/temperatures to prove all canceled factors nonzero; `field_simp` followed by `ring` gives the reciprocal expression.

## Blueprint decision

No listed chapter is edited: the supplied excerpts contain no concrete source, statement, dimensional, branch, or strategy defect. The generic blueprint proof prose is superseded for this prover pass by the actionable routes above.
