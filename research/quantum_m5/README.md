# M5 proof and distance evidence

Current follow-up: [M6 proof, algorithm and final acceptance](../quantum_m6/README.md).

This snapshot accompanies the research and formalization harness in this repository.

- [Full reviewed M5 proof](research_checkpoints/period_residue_arithmetic_law_reviewed/PROOF.md)
- [Review and integration decision](research_checkpoints/period_residue_arithmetic_law_reviewed/integration-decision.json)
- [Accepted arithmetic scope](docs/M5_ARITHMETIC_COMPLETION_20260914.md)
- [Exact distance report](research_checkpoints/m5_distance_20260915/REPORT.md): 30 positive-k instances, 60 independently checked DRAT refutations; three k=0 instances have no logical distance.
- [Original problem and handoff](RESEARCH_PROBLEM_AND_TAKEOVER_ROADMAP.md)

The M5 result is a reviewed natural-language arithmetic proof. It has not yet been fully formalized in Lean. Distance certificates are separate computational evidence and are not part of the original M5 acceptance gate.

Source: ShuxiangCao/quantum_code_discovery_proof at e1a3c22da792bf5d02eed166cb38e9bc050f4710. SOURCE_MANIFEST.json preserves the exact hashes of imported files. Relative paths and commands from the distance report are interpreted from this directory (`cd research/quantum_m5`). Install its pinned requirements into a Python environment and use that Python for the scripts; the original local virtual environment is not included. DRAT replay requires a drat-trim executable.
