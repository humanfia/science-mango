"""Bounded exact rational feasibility; this does not certify any quantum-code premise.

Rows mean sum(coefficients[name] * name) < rhs when strict, and <= otherwise.
Fourier--Motzkin elimination preserves strictness by OR when combining rows
with positive multipliers. Every retained row carries its original-row
nonnegative combination. Witnesses and contradictions are independently
rechecked against the parsed original rows before they are returned.

Invalid inputs raise ValueError. Resource exhaustion returns unknown, never
infeasible. max_rows counts original rows plus every generated pair, including
rows subsequently deduplicated or discarded. It is not a live-row limit.
There are also fixed integer-size and arithmetic-operation limits.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import re


MAX_VARIABLES = 8
MAX_INPUT_ROWS = 128
MAX_NAME_CHARS = 128
MAX_RATIONAL_CHARS = 128
MAX_INPUT_INTEGER_BITS = 512
MAX_INTERMEDIATE_BITS = 4096
MAX_ROW_BUDGET = 16384
MAX_ARITHMETIC_OPERATIONS = 250000
_RATIONAL = re.compile(r"[+-]?[0-9]+(?:/[+-]?[0-9]+)?\Z")
_ZERO = Fraction(0)
_ONE = Fraction(1)


class _Limit(Exception):
    """A bounded calculation cannot make a definitive claim."""


class _Contradiction(Exception):
    def __init__(self, row: _Row):
        self.row = row


@dataclass(frozen=True)
class _Row:
    coefficients: tuple[Fraction, ...]
    rhs: Fraction
    strict: bool
    weights: dict[str, Fraction]


@dataclass
class _Budget:
    rows: int
    maximum: int
    operations: int = 0

    def reserve(self, count: int) -> None:
        if self.rows + count > self.maximum:
            raise _Limit("row generation budget exceeded")
        self.rows += count

    def checked(self, value: Fraction) -> Fraction:
        self.operations += 1
        if self.operations > MAX_ARITHMETIC_OPERATIONS:
            raise _Limit("arithmetic operation budget exceeded")
        if (value.numerator.bit_length() > MAX_INTERMEDIATE_BITS
                or value.denominator.bit_length() > MAX_INTERMEDIATE_BITS):
            raise _Limit("intermediate integer size limit exceeded")
        return value


def _name(value: object, label: str) -> str:
    if (not isinstance(value, str) or not value
            or len(value) > MAX_NAME_CHARS
            or any(ord(char) < 32 or ord(char) == 127 for char in value)):
        raise ValueError(f"{label} must be a nonempty bounded string")
    return value


def _rational(value: object) -> Fraction:
    if (not isinstance(value, str) or len(value) > MAX_RATIONAL_CHARS
            or _RATIONAL.fullmatch(value) is None):
        raise ValueError("rational values must be bounded integer/fraction strings")
    pieces = value.split("/")
    numerator = int(pieces[0])
    denominator = int(pieces[1]) if len(pieces) == 2 else 1
    if denominator == 0:
        raise ValueError("rational denominator cannot be zero")
    if (numerator.bit_length() > MAX_INPUT_INTEGER_BITS
            or denominator.bit_length() > MAX_INPUT_INTEGER_BITS):
        raise ValueError("input rational integer size limit exceeded")
    return Fraction(numerator, denominator)


def _parse(variables: list[str], rows: list[dict], max_rows: int
           ) -> tuple[list[str], list[_Row], list[str]]:
    if not isinstance(variables, list) or len(variables) > MAX_VARIABLES:
        raise ValueError(f"variables must be a list of at most {MAX_VARIABLES} names")
    names = [_name(name, "variable") for name in variables]
    if len(set(names)) != len(names):
        raise ValueError("duplicate variable name")
    if not isinstance(rows, list) or len(rows) > MAX_INPUT_ROWS:
        raise ValueError(f"rows must be a list of at most {MAX_INPUT_ROWS} rows")
    if type(max_rows) is not int or not 0 <= max_rows <= MAX_ROW_BUDGET:
        raise ValueError(f"max_rows must be an integer from 0 to {MAX_ROW_BUDGET}")
    allowed = set(names)
    identifiers = []
    parsed = []
    seen = set()
    for row in rows:
        if (not isinstance(row, dict)
                or set(row) != {"id", "coefficients", "rhs", "strict"}):
            raise ValueError("each row needs exactly id, coefficients, rhs, strict")
        identifier = _name(row["id"], "row id")
        if identifier in seen:
            raise ValueError("duplicate row id")
        seen.add(identifier)
        coefficients = row["coefficients"]
        if not isinstance(coefficients, dict):
            raise ValueError("coefficients must be a variable-to-rational dictionary")
        if any(not isinstance(name, str) or name not in allowed
               for name in coefficients):
            raise ValueError("unknown variable in coefficients")
        if type(row["strict"]) is not bool:
            raise ValueError("strict must be a bool")
        values = {name: _rational(value) for name, value in coefficients.items()}
        parsed.append(_Row(tuple(values.get(name, _ZERO) for name in names),
                           _rational(row["rhs"]), row["strict"], {identifier: _ONE}))
        identifiers.append(identifier)
    return names, parsed, identifiers


def _scale(row: _Row, multiplier: Fraction, budget: _Budget) -> _Row:
    if multiplier <= 0:
        raise _Limit("internal nonpositive elimination multiplier")
    if multiplier == 1:
        return row
    return _Row(
        tuple(budget.checked(value * multiplier) for value in row.coefficients),
        budget.checked(row.rhs * multiplier),
        row.strict,
        {key: budget.checked(value * multiplier) for key, value in row.weights.items()},
    )


def _combine(left: _Row, right: _Row, budget: _Budget) -> _Row:
    weights = dict(left.weights)
    for key, value in right.weights.items():
        weights[key] = budget.checked(weights.get(key, _ZERO) + value)
    return _Row(
        tuple(budget.checked(a + b) for a, b in zip(left.coefficients, right.coefficients)),
        budget.checked(left.rhs + right.rhs),
        left.strict or right.strict,
        weights,
    )


def _reduce(rows: list[_Row], budget: _Budget) -> list[_Row]:
    """Drop tautologies and dominated parallel rows, retaining valid provenance."""
    kept: dict[tuple[Fraction, ...], _Row] = {}
    for row in rows:
        pivot = next((value for value in row.coefficients if value), None)
        if pivot is None:
            if row.rhs < 0 or (row.rhs == 0 and row.strict):
                raise _Contradiction(row)
            continue
        row = _scale(row, budget.checked(_ONE / abs(pivot)), budget)
        old = kept.get(row.coefficients)
        if (old is None or row.rhs < old.rhs
                or (row.rhs == old.rhs and row.strict and not old.strict)):
            kept[row.coefficients] = row
    return list(kept.values())


def _dot(coefficients: tuple[Fraction, ...], values: dict[int, Fraction],
         budget: _Budget) -> Fraction:
    result = _ZERO
    for index, value in values.items():
        term = budget.checked(coefficients[index] * value)
        result = budget.checked(result + term)
    return result


def _witness(history: list[tuple[int, list[_Row]]], budget: _Budget
             ) -> dict[int, Fraction]:
    values: dict[int, Fraction] = {}
    for variable, rows in reversed(history):
        lower = upper = None
        lower_strict = upper_strict = False
        for row in rows:
            coefficient = row.coefficients[variable]
            if coefficient == 0:
                continue
            remainder = _dot(row.coefficients, values, budget)
            bound = budget.checked(budget.checked(row.rhs - remainder) / coefficient)
            if coefficient > 0:
                if upper is None or bound < upper:
                    upper, upper_strict = bound, row.strict
                elif bound == upper:
                    upper_strict = upper_strict or row.strict
            else:
                if lower is None or bound > lower:
                    lower, lower_strict = bound, row.strict
                elif bound == lower:
                    lower_strict = lower_strict or row.strict
        if lower is not None and upper is not None:
            if lower > upper or (lower == upper and (lower_strict or upper_strict)):
                raise _Limit("internal witness interval verification failed")
            values[variable] = budget.checked(budget.checked(lower + upper) / 2)
        elif lower is not None:
            values[variable] = budget.checked(lower + 1)
        elif upper is not None:
            values[variable] = budget.checked(upper - 1)
        else:
            values[variable] = _ZERO
    return values


def _feasible(names: list[str], original: list[_Row], identifiers: list[str],
              values: dict[int, Fraction], budget: _Budget) -> dict:
    slacks = []
    for identifier, row in zip(identifiers, original):
        slack = budget.checked(row.rhs - _dot(row.coefficients, values, budget))
        if slack < 0 or (row.strict and slack == 0):
            raise _Limit("internal original-row witness verification failed")
        slacks.append({"id": identifier, "slack": str(slack),
                       "strict": row.strict, "satisfied": True})
    return {
        "status": "feasible",
        "witness": {name: str(values[index]) for index, name in enumerate(names)},
        "slacks": slacks,
    }


def _infeasible(names: list[str], original: list[_Row], identifiers: list[str],
                row: _Row, budget: _Budget) -> dict:
    """Recompute the whole nonnegative combination from unmodified input rows."""
    originals = dict(zip(identifiers, original))
    lhs = [_ZERO] * len(names)
    rhs = _ZERO
    strict = False
    for identifier, weight in row.weights.items():
        if identifier not in originals or weight <= 0:
            raise _Limit("internal certificate weight verification failed")
        source = originals[identifier]
        for index, coefficient in enumerate(source.coefficients):
            term = budget.checked(weight * coefficient)
            lhs[index] = budget.checked(lhs[index] + term)
        rhs = budget.checked(rhs + budget.checked(weight * source.rhs))
        strict = strict or source.strict
    if (any(lhs) or not (rhs < 0 or (rhs == 0 and strict))
            or tuple(lhs) != row.coefficients or rhs != row.rhs or strict != row.strict):
        raise _Limit("internal original-row certificate verification failed")
    identifiers = sorted(row.weights)
    return {
        "status": "infeasible",
        "conflict_ids": identifiers,
        "certificate": {
            "weights": {identifier: str(row.weights[identifier]) for identifier in identifiers},
            "lhs": {name: str(value) for name, value in zip(names, lhs)},
            "rhs": str(rhs),
            "strict": strict,
        },
    }


def solve_strict_system(variables: list[str], rows: list[dict],
                        max_rows: int = 2048) -> dict:
    """Return a JSON-serializable feasible/infeasible/unknown result.

    Rational strings use only ASCII signed integers, optionally separated by
    one slash; decimals, exponents, floats, whitespace and zero denominators
    are rejected. Fraction strings in results are canonical (integers may
    therefore appear without "/1").

    feasible: witness maps variables to fractions; slacks lists every original
    row's exact rhs-minus-lhs with id, strict and satisfied=True.
    infeasible: certificate.weights maps conflict ids to positive rational
    multipliers. Their original-row combination has lhs zero and rhs negative,
    or rhs zero with at least one positively weighted strict row.
    unknown: reason describes an exhausted resource or failed internal check;
    it makes no assertion about mathematical feasibility.
    """
    names, original, identifiers = _parse(variables, rows, max_rows)
    budget = _Budget(0, max_rows)
    try:
        budget.reserve(len(original))
        try:
            ordered = [row for _, row in sorted(zip(identifiers, original))]
            current = _reduce(ordered, budget)
            remaining = set(range(len(names)))
            history = []
            while remaining:
                # Minimum fill, breaking ties by name rather than input order.
                def cost(variable: int) -> tuple[int, str]:
                    positive = sum(row.coefficients[variable] > 0 for row in current)
                    negative = sum(row.coefficients[variable] < 0 for row in current)
                    return positive * negative, names[variable]

                variable = min(remaining, key=cost)
                history.append((variable, current))
                positive = [row for row in current if row.coefficients[variable] > 0]
                negative = [row for row in current if row.coefficients[variable] < 0]
                following = [row for row in current if row.coefficients[variable] == 0]
                budget.reserve(len(positive) * len(negative))
                if positive and negative:
                    positive = [_scale(row, budget.checked(_ONE / row.coefficients[variable]),
                                       budget) for row in positive]
                    negative = [_scale(row, budget.checked(-_ONE / row.coefficients[variable]),
                                       budget) for row in negative]
                    for upper in positive:
                        for lower in negative:
                            following.append(_combine(upper, lower, budget))
                current = _reduce(following, budget)
                remaining.remove(variable)
        except _Contradiction as contradiction:
            return _infeasible(names, original, identifiers, contradiction.row, budget)
        values = _witness(history, budget)
        return _feasible(names, original, identifiers, values, budget)
    except _Limit as error:
        return {"status": "unknown", "reason": str(error)}
