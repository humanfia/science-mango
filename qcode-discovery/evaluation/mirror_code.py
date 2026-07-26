"""Mirror code construction (Khesin & Lu, arXiv:2603.05496).

Scope: this module is a baseline / reproducibility helper for codes
defined in arXiv:2603.05496 (used by ``tests/test_mirror_code.py`` and
``tests/benchmark_noncss.py`` to reproduce Table 1 of that paper, and
referenced in one PBB equivalence test).  Mirror codes are *not* used
in the production evolutionary search (Campaign 5 evolves general PBB
4-tuples, not mirror codes).

Mirror codes are a family of quantum LDPC stabilizer codes defined by
a finite abelian group G and two subsets A, B ⊆ G.  Each stabilizer
is labeled by a group element g ∈ G:

    S(g) = Z(Ag) · X(Bg^{-1})

where Ag = {a·g : a ∈ A} and Bg^{-1} = {b·g^{-1} : b ∈ B}.

Key properties:
- n = |G| physical qubits (one per group element)
- Check weight = |A| + |B| (typically 6 with |A|=|B|=3)
- All stabilizers are mixed X/Z -- inherently non-CSS
- Special cases can be equivalently CSS via Hadamard conjugation

For G = Z_{a1} × Z_{a2} × ... × Z_{ar} (abelian group as product of
cyclic groups), group elements are tuples and the group operation is
componentwise addition modulo the respective orders.

Usage::

    code = build_mirror_code((6, 12),
                              [(0,0), (1,0), (0,3)],   # A
                              [(0,0), (0,1), (2,0)])    # B
    print(code.num_qudits, code.dimension)  # 72, ...
"""

from __future__ import annotations

from functools import reduce
from operator import mul

import numpy as np
from qldpc.codes import QuditCode


def _element_to_index(element: tuple[int, ...], orders: tuple[int, ...]) -> int:
    """Map a group element tuple to a linear index.

    For G = Z_{a1} × Z_{a2} × ... × Z_{ar}, the element (e1, e2, ..., er)
    maps to index e1 * (a2*...*ar) + e2 * (a3*...*ar) + ... + er.
    """
    idx = 0
    stride = 1
    for i in range(len(orders) - 1, -1, -1):
        idx += (element[i] % orders[i]) * stride
        stride *= orders[i]
    return idx


def _group_add(a: tuple[int, ...], b: tuple[int, ...], orders: tuple[int, ...]) -> tuple[int, ...]:
    """Add two group elements componentwise modulo orders."""
    return tuple((ai + bi) % oi for ai, bi, oi in zip(a, b, orders))


def _group_inv(a: tuple[int, ...], orders: tuple[int, ...]) -> tuple[int, ...]:
    """Inverse of a group element: (a1, a2, ...) -> (o1-a1, o2-a2, ...)."""
    return tuple((oi - ai) % oi for ai, oi in zip(a, orders))


def _enumerate_group(orders: tuple[int, ...]) -> list[tuple[int, ...]]:
    """Enumerate all elements of G = Z_{a1} × ... × Z_{ar}."""
    if len(orders) == 0:
        return [()]
    elements = []
    sub = _enumerate_group(orders[1:])
    for i in range(orders[0]):
        for s in sub:
            elements.append((i,) + s)
    return elements


def build_mirror_code(
    group_orders: tuple[int, ...],
    A_elements: list[tuple[int, ...]],
    B_elements: list[tuple[int, ...]],
) -> QuditCode:
    """Construct a mirror code on abelian group G.

    Args:
        group_orders: Orders of cyclic group factors, e.g. (6, 12) for Z_6 × Z_12.
        A_elements: Subset A ⊆ G as list of tuples.
        B_elements: Subset B ⊆ G as list of tuples.

    Returns:
        Qubit stabilizer code (qldpc ``QuditCode``) with n = product(group_orders).

    Raises:
        ValueError: If elements are out of range or A/B are empty.
    """
    orders = tuple(group_orders)
    n = reduce(mul, orders, 1)

    if not A_elements:
        raise ValueError("A must be nonempty")
    if not B_elements:
        raise ValueError("B must be nonempty")

    # Validate elements
    for name, elems in [("A", A_elements), ("B", B_elements)]:
        for elem in elems:
            if len(elem) != len(orders):
                raise ValueError(
                    f"{name} element {elem} has wrong dimension "
                    f"(expected {len(orders)}, got {len(elem)})"
                )
            for i, (ei, oi) in enumerate(zip(elem, orders)):
                if not (0 <= ei < oi):
                    raise ValueError(
                        f"{name} element {elem}: component {i} = {ei} "
                        f"out of range [0, {oi})"
                    )

    # Enumerate group elements
    group = _enumerate_group(orders)
    assert len(group) == n

    # Build symplectic matrix: (n, 2n) where each row is [X-part | Z-part]
    # S(g) = Z(Ag) · X(Bg^{-1})
    #   X-part: 1s at positions {b + g^{-1} : b ∈ B}
    #   Z-part: 1s at positions {a + g : a ∈ A}
    symplectic = np.zeros((n, 2 * n), dtype=int)

    for row_idx, g in enumerate(group):
        g_inv = _group_inv(g, orders)

        # Z-part: positions in Ag = {a + g : a ∈ A}
        for a in A_elements:
            ag = _group_add(a, g, orders)
            col = _element_to_index(ag, orders)
            symplectic[row_idx, n + col] = 1  # Z-part

        # X-part: positions in Bg^{-1} = {b + g^{-1} : b ∈ B}
        for b in B_elements:
            bg_inv = _group_add(b, g_inv, orders)
            col = _element_to_index(bg_inv, orders)
            symplectic[row_idx, col] = 1  # X-part

    return QuditCode(symplectic % 2)


def get_mirror_params(code: QuditCode) -> tuple[int, int]:
    """Get (n, k) for a mirror code."""
    return code.num_qudits, code.dimension
