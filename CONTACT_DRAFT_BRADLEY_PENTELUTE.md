# Contact draft for Professor Bradley L. Pentelute

**Subject:** A Lean 4 formalization based on the 2017 AFPS paper

Dear Professor Pentelute,

I am writing to share a recent formalization project based on your 2017 paper, “A Fully Automated Flow-Based Approach for Accelerated Peptide Synthesis.” We translated a carefully bounded set of claims from the paper and its supplementary information into a machine-checked Lean 4 library, named `AFPS2017`.

The current release contains 22 Lean modules organized into four verified areas: conditional solid-phase peptide sequence assembly; dimensioned flow, timing, step-yield, and throughput calculations; provenance-linked mass and signal observations; and scalar-composition results for the reported quantities. The project builds against pinned Lean, Mathlib, and Physlib versions with no `sorry`, `admit`, or project-defined axioms. Its verification record also reports complete source coverage, an independent sealed-holdout pass, and a standalone-extraction pass.

We have tried to preserve the scientific boundary of the original work. Experimental measurements are represented as source-addressed observations, while conclusions about successful coupling, molecular identity, purity, or reactor performance remain conditional on explicit assumptions. The formalization therefore checks the logical and numerical structure of selected claims without overstating what follows from the experimental record.

Two weeks ago, I had the opportunity to speak with one of your students about this effort, and the conversation was very helpful. I would be grateful for a chance to show you the result and hear your thoughts on its scientific fidelity and possible value. The repository is currently private and will not be made public without further discussion. Would you be available for a brief 20–30 minute conversation in the coming weeks?

Best regards,  
[Your name]
