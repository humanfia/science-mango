"""Distance estimation for bivariate bicycle codes.

Provides three estimation strategies, listed from fastest to slowest:

1. **BP-OSD with OSD_0** (:func:`estimate_distance`) -- default fast estimator.
   Uses belief-propagation (product-sum) followed by ordered-statistics
   decoding at order 0.  Returns an upper bound on code distance by
   splitting random trials evenly between X and Z Pauli types and taking
   the minimum.  ~100-500 trials give a workable bound in seconds.

2. **BP-OSD with OSD-CS order 10** (:func:`estimate_distance_osd_cs`) --
   tighter bounds at ~2-5x the cost per trial.  OSD-CS (combination
   sweep) systematically searches order-*w* subsets of reliable bit
   positions after Gaussian elimination, finding lower-weight logical
   operators that OSD_0 misses.  Empirically tightens bounds on 7 of 9
   tested codes (4-12 point improvements on high-*k* codes).

3. **Exact distance** (:func:`compute_distance_exact`) -- brute-force
   enumeration via ``code.get_distance_exact()``.  Uses ``SIGALRM`` on
   Unix for timeout or ``multiprocessing`` on Windows.  Returns ``None``
   when called from non-main threads (qldpc objects are not picklable).

Important caveat: BP-OSD is **stochastic** -- the same code can yield
distance estimates ranging from 6 to 18 across independent batches
(observed on [[144,32,?]]).  For publication-quality claims, use the
multi-decoder soak test (``tests/soak_test.py``) with at least 150,000
total trials across three decoder configurations.

All distance values returned by this module are **upper bounds** and
should be reported as ``d <= X``, never ``d = X``.
"""

from __future__ import annotations

import multiprocessing
import signal
import threading
from contextlib import contextmanager
from qldpc.codes import CSSCode
from qldpc.objects import Pauli


def _safe_int(d, default=0) -> int:
    """Convert distance to int, returning default if NaN."""
    if d != d:  # NaN check
        return default
    return int(d)

_HAS_SIGALRM = hasattr(signal, "SIGALRM")


def _can_use_sigalrm() -> bool:
    """Check if SIGALRM is available and we're in the main thread."""
    return _HAS_SIGALRM and threading.current_thread() is threading.main_thread()


class DistanceTimeout(Exception):
    pass


@contextmanager
def timeout(seconds: int):
    """Context manager that raises DistanceTimeout after `seconds`.

    Uses SIGALRM on Unix. On platforms without it (Windows), falls back
    to running the block without a timeout -- use compute_distance_exact()
    which has its own multiprocessing-based timeout.
    """
    if not _can_use_sigalrm():
        yield
        return

    def handler(signum, frame):
        raise DistanceTimeout(f"Distance computation timed out after {seconds}s")

    old_handler = signal.signal(signal.SIGALRM, handler)
    signal.alarm(seconds)
    try:
        yield
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old_handler)


def estimate_distance(code: CSSCode, num_trials: int = 100) -> int:
    """Estimate code distance using decoder-based upper bound (BP-OSD).

    Calls get_distance_bound_with_decoder directly to bypass GAP/QDistRnd
    checks (which require interactive input when GAP is not installed).

    Args:
        code: A CSSCode (typically BBCode).
        num_trials: Number of randomized trials. More trials -> tighter bound.

    Returns:
        Upper bound on code distance.
    """
    if code.dimension == 0:
        return 0

    trials_x = num_trials // 2
    trials_z = (num_trials + 1) // 2
    d_x = code.get_distance_bound_with_decoder(
        Pauli.X, trials_x, bp_method="product_sum"
    )
    d_z = code.get_distance_bound_with_decoder(
        Pauli.Z, trials_z, bp_method="product_sum"
    )
    d = min(d_x, d_z)
    return _safe_int(d)


def estimate_distance_osd_cs(code: CSSCode, num_trials: int = 200) -> int:
    """Estimate distance using OSD-CS order 10 (tighter bounds than OSD_0).

    OSD-CS systematically searches order-w subsets of reliable bit positions
    after Gaussian elimination, finding lower-weight logical operators that
    OSD_0 misses. Empirically finds tighter bounds for 7 of 9 tested codes.

    ~2-5x slower per trial than OSD_0, so use fewer trials.
    """
    if code.dimension == 0:
        return 0

    trials_x = num_trials // 2
    trials_z = (num_trials + 1) // 2
    d_x = code.get_distance_bound_with_decoder(
        Pauli.X, trials_x,
        bp_method="product_sum", osd_method="osd_cs", osd_order=10,
    )
    d_z = code.get_distance_bound_with_decoder(
        Pauli.Z, trials_z,
        bp_method="product_sum", osd_method="osd_cs", osd_order=10,
    )
    d = min(d_x, d_z)
    return _safe_int(d)


def _exact_distance_worker(code: CSSCode, result_queue: multiprocessing.Queue):
    """Worker for multiprocessing-based exact distance with timeout."""
    try:
        d = code.get_distance_exact()
        result_queue.put(_safe_int(d) if d == d else None)
    except Exception:
        result_queue.put(None)


def compute_distance_exact(code: CSSCode, timeout_seconds: int = 300) -> int | None:
    """Compute exact code distance via brute-force.

    Uses SIGALRM on Unix for timeout. Falls back to multiprocessing on
    platforms without SIGALRM (Windows). Returns None (skips) when called
    from a non-main thread since qldpc objects can't be pickled for
    multiprocessing and SIGALRM isn't available.

    Args:
        code: A CSSCode (typically BBCode).
        timeout_seconds: Maximum time allowed (default 5 minutes).

    Returns:
        Exact distance, or None if computation timed out or unavailable.
    """
    if _can_use_sigalrm():
        try:
            with timeout(timeout_seconds):
                d = code.get_distance_exact()
                return _safe_int(d) or None
        except DistanceTimeout:
            return None

    if threading.current_thread() is not threading.main_thread():
        # Can't use SIGALRM or multiprocessing (qldpc objects aren't
        # picklable) from worker threads. Return None to keep the
        # BP-OSD estimate instead.
        return None

    # Fallback: multiprocessing-based timeout (main thread, no SIGALRM)
    queue: multiprocessing.Queue = multiprocessing.Queue()
    proc = multiprocessing.Process(
        target=_exact_distance_worker, args=(code, queue)
    )
    proc.start()
    proc.join(timeout=timeout_seconds)
    if proc.is_alive():
        proc.terminate()
        proc.join(timeout=5)
        return None
    return queue.get_nowait() if not queue.empty() else None
