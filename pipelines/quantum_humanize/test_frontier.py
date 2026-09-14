"""Pure in-memory tests of untrusted frontier planning, never FPUT evidence.

All manifests, bounds, geometric descriptions and witnesses here are synthetic.
No files, research checkers, native agents or mathematical backends are run.
"""

import copy
from fractions import Fraction
import unittest
from unittest import mock

from pydantic import ValidationError

from pipelines.quantum_humanize import _frontier as frontier


OBLIGATION = "r3_b_remaining"
PLACEMENTS = [f"outer_{i}" for i in range(1, 4)] + [
    f"residual_{i}" for i in range(1, 10)
]
MANIFEST = {
    "head": "a" * 40,
    "files": [{"path": "thermalization-fixture.md", "sha256": "b" * 64, "bytes": 0}],
}


def _evidence():
    return {
        "path": "thermalization-fixture.md",
        "sha256": "b" * 64,
        "section": "Synthetic section: this is not a mathematical source.",
    }


def _power(parameter="delta", value="1"):
    return {"parameter": parameter, "value": value}


def _parameter(name="delta", *, shrinks=True):
    return {
        "name": name,
        "meaning": f"Synthetic geometric cutoff {name}; no geometric identity is proved.",
        "shrinks": shrinks,
    }


def _condition(name="cap", coefficients=None, rhs="1", *, strict=True):
    return {
        "id": name,
        "coefficients": [_power()] if coefficients is None else coefficients,
        "rhs": rhs,
        "strict": strict,
        "justification": "Synthetic declared exponent condition, not verified geometry.",
        "dependencies": [_evidence()],
    }


def _bound(**changes):
    value = {
        "time_power": "1",
        "log_power": "0",
        "cutoff_powers": [],
        "constant_policy": "uniform",
        "unknown_dependencies": [],
        "norm": "Synthetic L1 output norm retaining four labelled outputs.",
        "window_and_limits": "Synthetic endpoint or fixed positive window; N-first.",
        "hypothesis_conditions": [],
        "dependencies": [_evidence()],
    }
    value.update(changes)
    return value


def _cell(name="local", **changes):
    value = {
        "id": name,
        "placements": ["outer_1"],
        "source_labels": "Only the synthetic labelled source selector, not all sources.",
        "temporal_signs": "Synthetic declared signs; completeness is not proved.",
        "outputs": "All four synthetic original outputs retained.",
        "region": "A local synthetic momentum selector.",
        "boundary_and_overlap": "No geometric partition is verified by this fixture.",
        "localization": "Synthetic time-independent cutoff.",
        "status": "bounded",
        "bound": _bound(),
        "gap": "",
        "dependencies": [_evidence()],
    }
    value.update(changes)
    return value


def _fixture(**changes):
    value = {
        "obligation_id": OBLIGATION,
        "partition_argument": "Synthetic claim of a partition, not a checked identity.",
        "partition_dependencies": [_evidence()],
        "partition_gaps": [],
        "parameters": [],
        "conditions": [],
        "cells": [_cell()],
    }
    value.update(changes)
    return value


class FrontierTests(unittest.TestCase):
    def analyze(self, value=None, *, manifest=None, obligation=OBLIGATION):
        value = _fixture() if value is None else value
        model = frontier.Frontier.model_validate(value)
        return frontier.analyze_frontier(
            model, copy.deepcopy(MANIFEST if manifest is None else manifest), obligation
        )

    def assert_untrusted(self, report):
        self.assertIs(report["trusted_proof"], False)
        self.assertIs(report["coverage_complete"], False)
        self.assertIs(report["coverage"]["partition_verified"], False)
        self.assertIn("UNVERIFIED PLANNING ONLY", report["caution"])

    def assert_invalid(self, value, error, **analysis_options):
        with mock.patch.object(frontier, "solve_strict_system") as solve:
            report = self.analyze(value, **analysis_options)
        self.assertIn(error, report["validation_errors"])
        self.assertEqual(report["cutoffs"]["status"], "invalid")
        self.assertEqual(report["tasks"], [])
        self.assertNotIn("algebra", report["cutoffs"])
        solve.assert_not_called()
        self.assert_untrusted(report)
        return report

    def assert_feasible_witness(self, report):
        algebra = report["cutoffs"]["algebra"]
        self.assertEqual(algebra["status"], "feasible")
        witness = {key: Fraction(value) for key, value in algebra["witness"].items()}
        for row in report["cutoffs"]["rows"]:
            with self.subTest(row=row["id"]):
                lhs = sum(
                    (Fraction(value) * witness[key] for key, value in row["coefficients"].items()),
                    Fraction(0),
                )
                rhs = Fraction(row["rhs"])
                if row["strict"]:
                    self.assertLess(lhs, rhs)
                else:
                    self.assertLessEqual(lhs, rhs)
        for value in witness.values():
            self.assertGreaterEqual(value, 0)
        self.assert_untrusted(report)
        return witness

    def assert_tasks_locked(self, report):
        self.assertLessEqual(len(report["tasks"]), 8)
        for task in report["tasks"]:
            self.assertEqual(set(task), {
                "obligation_id", "objective", "success_criterion", "dependencies"
            })
            self.assertEqual(task["obligation_id"], OBLIGATION)
            self.assertTrue(task["objective"].startswith("UNVERIFIED RESEARCH TARGET: "))
            self.assertGreater(len(task["objective"]), 0)
            self.assertLessEqual(len(task["objective"]), 4000)
            self.assertGreater(len(task["success_criterion"]), 0)
            self.assertLessEqual(len(task["success_criterion"]), 2000)
            self.assertGreater(len(task["dependencies"]), 0)
            self.assertLessEqual(len(task["dependencies"]), 30)
            for dependency in task["dependencies"]:
                self.assertEqual(dependency, _evidence())

    def test_every_nested_schema_is_closed_and_requires_all_properties(self):
        stack = [frontier.Frontier.model_json_schema()]
        objects = 0
        while stack:
            node = stack.pop()
            if isinstance(node, dict):
                if node.get("type") == "object":
                    objects += 1
                    self.assertIs(node["additionalProperties"], False)
                    self.assertEqual(set(node["required"]), set(node["properties"]))
                stack.extend(node.values())
            elif isinstance(node, list):
                stack.extend(node)
        self.assertGreaterEqual(objects, 7)

    def test_missing_or_extra_fields_fail_at_every_model_level(self):
        samples = (
            (frontier.Evidence, _evidence()),
            (frontier.Power, _power()),
            (frontier.Parameter, _parameter()),
            (frontier.Condition, _condition()),
            (frontier.Bound, _bound()),
            (frontier.Cell, _cell()),
            (frontier.Frontier, _fixture()),
        )
        for model, sample in samples:
            for field in sample:
                with self.subTest(model=model.__name__, missing=field):
                    changed = copy.deepcopy(sample)
                    del changed[field]
                    with self.assertRaises(ValidationError):
                        model.model_validate(changed)
            with self.subTest(model=model.__name__, extra=True):
                changed = copy.deepcopy(sample)
                changed["trusted_proof"] = True
                with self.assertRaises(ValidationError):
                    model.model_validate(changed)

    def test_strict_types_do_not_coerce_untrusted_values(self):
        samples = (
            (frontier.Parameter, {**_parameter(), "shrinks": "true"}),
            (frontier.Parameter, {**_parameter(), "shrinks": 1}),
            (frontier.Power, _power(value=1)),
            (frontier.Bound, _bound(time_power=1.5)),
            (frontier.Condition, {**_condition(), "strict": "false"}),
            (frontier.Frontier, _fixture(obligation_id=17)),
            (frontier.Cell, _cell(placements=("outer_1",))),
        )
        for model, sample in samples:
            with self.subTest(model=model.__name__, sample=sample):
                with self.assertRaises(ValidationError):
                    model.model_validate(sample)

    def test_rational_fields_reject_executable_or_ambiguous_notation(self):
        for value in ("1/0", "+1", "01", "1.0", "1e2", "1/01", "1000000000", "delta+1"):
            with self.subTest(value=value):
                with self.assertRaises(ValidationError):
                    frontier.Bound.model_validate(_bound(time_power=value))
        for value in ("0", "-1", "3/4", "-7/3"):
            with self.subTest(valid=value):
                self.assertEqual(frontier.Power.model_validate(_power(value=value)).value, value)

    def test_null_bound_is_required_even_for_an_open_cell(self):
        cell = _cell(status="open", bound=None, gap="Synthetic missing estimate.")
        self.assertIsNone(frontier.Cell.model_validate(cell).bound)
        del cell["bound"]
        with self.assertRaises(ValidationError):
            frontier.Cell.model_validate(cell)

    def test_physical_cutoff_powers_have_the_correct_substitution_sign(self):
        value = _fixture(
            parameters=[_parameter()],
            conditions=[
                _condition("upper", [_power()], "3/4", strict=False),
                _condition("lower", [_power(value="-1")], "-3/4", strict=False),
            ],
            cells=[
                _cell("small_region", bound=_bound(
                    time_power="3", cutoff_powers=[_power(value="2")],
                    hypothesis_conditions=["upper", "lower"],
                )),
                _cell("quantified_loss", bound=_bound(
                    time_power="1", constant_policy="quantified",
                    cutoff_powers=[_power(value="-1")],
                )),
            ],
        )
        report = self.analyze(value)
        rows = {row["id"]: row for row in report["cutoffs"]["rows"]}
        self.assertEqual(rows["bound:small_region"]["coefficients"], {"delta": "-2"})
        self.assertEqual(rows["bound:small_region"]["rhs"], "-1")
        self.assertIs(rows["bound:small_region"]["strict"], True)
        self.assertEqual(rows["bound:quantified_loss"]["coefficients"], {"delta": "1"})
        self.assertEqual(rows["bound:quantified_loss"]["rhs"], "1")
        witness = self.assert_feasible_witness(report)
        self.assertEqual(witness["delta"], Fraction(3, 4))
        self.assertEqual(Fraction(3) - 2 * witness["delta"], Fraction(3, 2))
        self.assertEqual(Fraction(1) + witness["delta"], Fraction(7, 4))

    def test_unknown_fixed_cutoff_constant_stays_unknown_with_a_known_subsystem(self):
        value = _fixture(
            parameters=[_parameter()],
            conditions=[_condition("cap", rhs="3/4")],
            cells=[
                _cell("far", placements=PLACEMENTS, bound=_bound(
                    time_power="7/4", constant_policy="unknown",
                    unknown_dependencies=["Unquantified dependence of C_delta."],
                )),
                _cell("near", bound=_bound(time_power="3", cutoff_powers=[_power(value="2")])),
            ],
        )
        report = self.analyze(value)
        self.assertEqual(report["cutoffs"]["status"], "unknown")
        self.assertEqual(report["cutoffs"]["unknowns"], [{
            "cell": "far", "dependencies": ["Unquantified dependence of C_delta."]
        }])
        ids = {row["id"] for row in report["cutoffs"]["rows"]}
        self.assertIn("bound:near", ids)
        self.assertNotIn("bound:far", ids)
        witness = self.assert_feasible_witness(report)
        self.assertGreater(witness["delta"], Fraction(1, 2))
        self.assertLess(witness["delta"], Fraction(3, 4))
        self.assertEqual(len(report["tasks"]), 1)
        self.assertIn("Quantify constant", report["tasks"][0]["objective"])
        self.assert_tasks_locked(report)

    def test_unknown_policy_or_declared_unknown_loss_cannot_be_silently_uniform(self):
        for policy, losses in (("unknown", []), ("uniform", ["Unquantified derivative loss"])):
            with self.subTest(policy=policy, losses=losses):
                report = self.analyze(_fixture(cells=[_cell(
                    placements=PLACEMENTS,
                    bound=_bound(constant_policy=policy, unknown_dependencies=losses),
                )]))
                self.assertEqual(report["cutoffs"]["status"], "unknown")
                self.assertTrue(report["cutoffs"]["unknowns"][0]["dependencies"])
                self.assertNotIn("bound:local", {row["id"] for row in report["cutoffs"]["rows"]})
                self.assert_feasible_witness(report)
                self.assert_tasks_locked(report)

    def test_logarithmic_boundary_gains_are_not_certified_by_strict_power_solver(self):
        for log_power in ("0", "-1", "-10"):
            with self.subTest(log_power=log_power):
                report = self.analyze(_fixture(cells=[_cell(
                    placements=PLACEMENTS,
                    bound=_bound(time_power="2", log_power=log_power),
                )]))
                self.assertEqual(report["cutoffs"]["status"], "infeasible")
                self.assertIn("bound:local", report["cutoffs"]["algebra"]["conflict_ids"])
                self.assertIn("logarithmic boundary schedules", report["caution"])
                self.assert_untrusted(report)
        report = self.analyze(_fixture(cells=[_cell(bound=_bound(
            time_power="1999/1000", log_power="100"
        ))]))
        self.assert_feasible_witness(report)

    def test_mentioning_all_twelve_placements_does_not_certify_coverage(self):
        report = self.analyze(_fixture(cells=[_cell(placements=PLACEMENTS)]))
        self.assertEqual(report["coverage"]["unmentioned_placements"], [])
        self.assertEqual(report["coverage"]["bounded_cells"], ["local"])
        self.assertEqual(report["coverage"]["open_cells"], [])
        self.assertEqual(report["tasks"], [])
        self.assert_feasible_witness(report)
        self.assert_untrusted(report)

    def test_missing_placements_are_reported_against_the_full_original_universe(self):
        report = self.analyze()
        self.assertEqual(report["coverage"]["unmentioned_placements"], PLACEMENTS[1:])
        self.assertTrue(any("No cells yet listed for outer_2" in task["objective"]
                            for task in report["tasks"]))
        self.assertIn("residual_9", report["tasks"][0]["objective"])
        self.assert_untrusted(report)
        self.assert_tasks_locked(report)

    def test_open_cell_is_not_a_bound_and_produces_a_specific_research_target(self):
        report = self.analyze(_fixture(cells=[_cell(
            "unproved", placements=PLACEMENTS, status="open", bound=None,
            gap="Synthetic missing jump-region estimate.",
        )]))
        self.assertEqual(report["coverage"]["bounded_cells"], [])
        self.assertEqual(report["coverage"]["open_cells"], ["unproved"])
        self.assertEqual(report["cutoffs"]["rows"], [])
        self.assertEqual(len(report["tasks"]), 1)
        self.assertIn("Resolve cell unproved", report["tasks"][0]["objective"])
        self.assertIn("jump-region", report["tasks"][0]["objective"])
        self.assert_tasks_locked(report)
        self.assert_untrusted(report)

    def test_status_bound_mismatches_and_empty_open_gaps_do_not_dispatch(self):
        for cell, error in (
            (_cell(bound=None), "cell status/bound mismatch: local"),
            (_cell(status="open", gap="Missing estimate"), "cell status/bound mismatch: local"),
            (_cell(status="open", bound=None), "open cell lacks a concrete gap: local"),
        ):
            with self.subTest(cell=cell):
                self.assert_invalid(_fixture(cells=[cell]), error)

    def test_wrong_obligation_never_solves_or_dispatches(self):
        self.assert_invalid(_fixture(obligation_id="actual_kinetic"), "frontier obligation changed")

    def test_matching_but_unsupported_targets_never_solve_or_dispatch(self):
        for obligation in ("actual_kinetic", "synthetic_other_target"):
            with self.subTest(obligation=obligation):
                report = self.assert_invalid(
                    _fixture(obligation_id=obligation),
                    "T^2 cutoff planning is not supported for this obligation",
                    obligation=obligation,
                )
                self.assertNotIn("frontier obligation changed", report["validation_errors"])

    def test_unlocked_dependencies_are_rejected_at_every_reference_site(self):
        for site in ("partition", "condition", "cell", "bound"):
            for fault in ("path", "sha256"):
                with self.subTest(site=site, fault=fault):
                    value = _fixture(parameters=[_parameter()], conditions=[_condition()])
                    refs = {
                        "partition": value["partition_dependencies"],
                        "condition": value["conditions"][0]["dependencies"],
                        "cell": value["cells"][0]["dependencies"],
                        "bound": value["cells"][0]["bound"]["dependencies"],
                    }[site]
                    refs[0][fault] = "unlocked-fixture.md" if fault == "path" else "c" * 64
                    self.assert_invalid(value, "unlocked frontier dependency: " + refs[0]["path"])

    def test_unknown_parameters_are_rejected_in_conditions_and_bounds(self):
        for site in ("condition", "bound", "unknown_constant_bound"):
            with self.subTest(site=site):
                value = _fixture(parameters=[_parameter()])
                if site == "condition":
                    value["conditions"] = [_condition(coefficients=[_power("unlisted")])]
                else:
                    bound = value["cells"][0]["bound"]
                    bound["cutoff_powers"] = [_power("unlisted")]
                    if site == "unknown_constant_bound":
                        bound["constant_policy"] = "unknown"
                self.assert_invalid(value, "unknown coefficient parameter")

    def test_unknown_hypotheses_are_rejected_even_with_unknown_constants(self):
        for policy in ("uniform", "unknown"):
            with self.subTest(policy=policy):
                self.assert_invalid(_fixture(cells=[_cell(bound=_bound(
                    constant_policy=policy, hypothesis_conditions=["unlisted"]
                ))]), "unknown hypothesis condition in local")

    def test_duplicate_identifiers_do_not_dispatch(self):
        for kind in ("parameter", "condition", "cell", "coefficient_condition", "coefficient_bound", "placement"):
            with self.subTest(kind=kind):
                value = _fixture(parameters=[_parameter()], conditions=[_condition()])
                if kind == "parameter":
                    value["parameters"].append(_parameter())
                    error = "duplicate parameter"
                elif kind == "condition":
                    value["conditions"].append(_condition())
                    error = "duplicate condition"
                elif kind == "cell":
                    value["cells"].append(_cell())
                    error = "duplicate cell"
                elif kind == "coefficient_condition":
                    value["conditions"][0]["coefficients"] = [_power(), _power()]
                    error = "duplicate coefficient parameter"
                elif kind == "coefficient_bound":
                    value["cells"][0]["bound"]["cutoff_powers"] = [_power(), _power()]
                    error = "duplicate coefficient parameter"
                else:
                    value["cells"][0]["placements"] = ["outer_1", "outer_1"]
                    error = "duplicate placement within cell"
                self.assert_invalid(value, error)

    def test_unknown_original_placement_does_not_redefine_the_target_universe(self):
        self.assert_invalid(_fixture(cells=[_cell(placements=["outer_4"])]),
                            "unknown original placement in local")

    def test_joint_conditions_on_one_parameter_can_conflict(self):
        value = _fixture(parameters=[_parameter()], cells=[
            _cell("near", bound=_bound(time_power="3", cutoff_powers=[_power(value="2")])),
            _cell("far", bound=_bound(time_power="1", cutoff_powers=[_power(value="-2")])),
        ])
        report = self.analyze(value)
        self.assertEqual(report["cutoffs"]["status"], "infeasible")
        self.assertTrue({"bound:near", "bound:far"} <=
                        set(report["cutoffs"]["algebra"]["conflict_ids"]))
        self.assertIn("conflicting DECLARED", report["tasks"][0]["objective"])
        self.assertIn("bound:near: (-2)*a_delta < -1", report["tasks"][0]["objective"])
        self.assertIn("bound:far: (2)*a_delta < 1", report["tasks"][0]["objective"])
        self.assertIn("not a theorem", report["tasks"][0]["success_criterion"])
        self.assert_tasks_locked(report)
        self.assert_untrusted(report)

    def test_conflict_task_uses_actual_row_sources_not_unrelated_references(self):
        value = _fixture(parameters=[_parameter()], cells=[
            _cell("near", placements=PLACEMENTS, bound=_bound(
                time_power="3", cutoff_powers=[_power(value="2")]
            )),
            _cell("far", bound=_bound(time_power="1", cutoff_powers=[_power(value="-2")])),
            _cell("unrelated"),
        ])
        for cell in value["cells"]:
            cell["dependencies"][0]["section"] = "Synthetic cell " + cell["id"]
            cell["bound"]["dependencies"][0]["section"] = "Synthetic bound " + cell["id"]
        declared = {
            "status": "infeasible", "conflict_ids": ["bound:near", "bound:far"],
            "certificate": [],
        }
        with mock.patch.object(frontier, "solve_strict_system", return_value=declared):
            report = self.analyze(value)
        self.assertEqual(len(report["tasks"]), 1)
        refs = report["tasks"][0]["dependencies"]
        self.assertEqual({ref["section"] for ref in refs}, {
            "Synthetic bound near", "Synthetic cell near", "Synthetic bound far", "Synthetic cell far"
        })
        for ref in refs:
            self.assertEqual(ref["path"], _evidence()["path"])
            self.assertEqual(ref["sha256"], _evidence()["sha256"])
        self.assertNotIn("unrelated", report["tasks"][0]["objective"])
        self.assert_untrusted(report)

    def test_distinct_parameters_are_not_automatically_geometrically_identified(self):
        value = _fixture(parameters=[_parameter("delta"), _parameter("h")], cells=[
            _cell("near", placements=PLACEMENTS, bound=_bound(
                time_power="3", cutoff_powers=[_power("delta", "2")]
            )),
            _cell("far", bound=_bound(time_power="1", cutoff_powers=[_power("h", "-2")])),
        ], partition_gaps=["Synthetic delta and h regions have no established geometric overlap."])
        report = self.analyze(value)
        witness = self.assert_feasible_witness(report)
        self.assertGreater(witness["delta"], Fraction(1, 2))
        self.assertLess(witness["h"], Fraction(1, 2))
        self.assertNotEqual(witness["delta"], witness["h"])
        self.assertTrue(all(len(row["coefficients"]) <= 1 for row in report["cutoffs"]["rows"]))
        self.assertIn("no established geometric overlap", report["tasks"][0]["objective"])
        self.assert_untrusted(report)

    def test_shrinking_parameter_is_strictly_positive_but_fixed_zero_is_allowed(self):
        for shrinks, expected in ((True, "infeasible"), (False, "feasible")):
            with self.subTest(shrinks=shrinks):
                report = self.analyze(_fixture(
                    parameters=[_parameter(shrinks=shrinks)],
                    conditions=[_condition("zero", rhs="0", strict=False)],
                ))
                self.assertEqual(report["cutoffs"]["status"], expected)
                row = next(row for row in report["cutoffs"]["rows"] if row["id"] == "parameter:delta")
                self.assertEqual(row, {
                    "id": "parameter:delta", "coefficients": {"delta": "-1"},
                    "rhs": "0", "strict": shrinks,
                })
                if not shrinks:
                    self.assertEqual(self.assert_feasible_witness(report)["delta"], 0)

    def test_task_count_is_capped_and_every_dependency_is_locked_and_deduplicated(self):
        cells = [_cell(
            f"open_{i}", placements=PLACEMENTS, status="open", bound=None,
            gap="Synthetic missing estimate: " + "x" * 2900,
            region="Synthetic region: " + "y" * 2900,
            dependencies=[_evidence(), _evidence()],
        ) for i in range(16)]
        report = self.analyze(_fixture(cells=cells))
        self.assertEqual(len(report["tasks"]), 8)
        for i, task in enumerate(report["tasks"]):
            self.assertIn(f"Resolve cell open_{i}:", task["objective"])
            self.assertEqual(task["dependencies"], [_evidence()])
            self.assertEqual(len(task["objective"]), 4000)
        self.assert_tasks_locked(report)
        self.assert_untrusted(report)

    def test_solver_budget_unknown_is_preserved_without_fabricating_a_witness(self):
        unknown = {"status": "unknown", "reason": "Synthetic exact-elimination resource budget exhausted."}
        with mock.patch.object(frontier, "solve_strict_system", return_value=unknown) as solve:
            report = self.analyze(_fixture(cells=[_cell(placements=PLACEMENTS)]))
        solve.assert_called_once()
        self.assertEqual(report["cutoffs"]["status"], "unknown")
        self.assertEqual(report["cutoffs"]["algebra"], unknown)
        self.assertEqual(report["cutoffs"]["unknowns"], [])
        self.assertNotIn("witness", report["cutoffs"]["algebra"])
        self.assertEqual(report["tasks"], [])
        self.assert_untrusted(report)

    def test_unknown_constant_does_not_hide_a_conflict_in_the_known_subsystem(self):
        declared = {"status": "infeasible", "conflict_ids": ["bound:known"], "certificate": []}
        with mock.patch.object(frontier, "solve_strict_system", return_value=declared):
            report = self.analyze(_fixture(cells=[
                _cell("unknown", placements=PLACEMENTS, bound=_bound(
                    constant_policy="unknown", unknown_dependencies=["C_delta"],
                )),
                _cell("known", bound=_bound(time_power="2")),
            ]))
        self.assertEqual(report["cutoffs"]["status"], "unknown")
        self.assertEqual(report["cutoffs"]["algebra"]["status"], "infeasible")
        self.assertEqual(len(report["tasks"]), 2)
        self.assertIn("conflicting DECLARED", report["tasks"][0]["objective"])
        self.assertIn("Quantify constant", report["tasks"][1]["objective"])
        self.assert_tasks_locked(report)
        self.assert_untrusted(report)

    def test_analysis_does_not_mutate_the_frontier_or_manifest(self):
        value = _fixture(parameters=[_parameter()], conditions=[_condition()])
        model = frontier.Frontier.model_validate(value)
        manifest = copy.deepcopy(MANIFEST)
        model_before = model.model_dump()
        manifest_before = copy.deepcopy(manifest)
        frontier.analyze_frontier(model, manifest, OBLIGATION)
        self.assertEqual(model.model_dump(), model_before)
        self.assertEqual(manifest, manifest_before)


if __name__ == "__main__":
    unittest.main()

# Upstream fixture helpers; FPUT-specific scenarios are not adapted tests.
__test__ = False
