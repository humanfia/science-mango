"""Humanize-style long-horizon orchestration for qcode discovery.

OpenEvolve remains responsible for strategy evolution and MAP-Elites.  This
package adds the RLCR control plane: durable rounds, independent review,
expensive-verification promotion gates, and cross-round lessons.
"""

from .state import EliteArchive, RunStore, code_key

__all__ = ["EliteArchive", "RunStore", "code_key"]
