#!/usr/bin/env python3
"""Independent finite reference for complete tied-placement reconstruction."""
import json
from pathlib import Path
import selector_complete as s


def validate():
    queries = 0
    duplicate_action_ties = False
    for N, w in ((1, 1), (3, 2), (4, 2), (4, 4), (5, 2), (5, 3)):
        for maximize in (False, True):
            winners, front, _ = s.select(N, w, maximize_distance=maximize)
            actions = list(s.optimal_actions(N, winners, maximize))
            actual = list(s.optimal_presentations(N, winners, maximize))
            expected = set()
            raw_winners, raw_front = s.brute_select(N, w, maximize_distance=maximize)
            assert front == raw_front
            for pair, points in raw_winners.items():
                distance = s.brute_label(N, pair)[1] if maximize else None
                for target in s.raw_orbit(N, pair):
                    costs = [min(x, N-x) for block in target for x in block]
                    point = (sum(costs), max(costs))
                    if maximize:
                        point = (-distance,) + point
                    if point in points:
                        expected.add((pair, target, point))
            assert set(actual) == expected, (N, w, maximize)
            assert len(actual) == len(set(actual)), (N, w, maximize)
            assert {(p, target, point) for p, action, target, point in actions} == expected
            for pair, action, target, point in actions:
                assert s.apply_action(N, pair, action) == target
                assert s.apply_action(N, pair, s.least_action(N, pair, target)) == target
            duplicate_action_ties |= len(actions) > len(actual)
            queries += 1
    assert duplicate_action_ties
    return dict(status='passed', all_placement_queries=queries,
                duplicate_action_ties_detected=duplicate_action_ties,
                scope='finite reconstruction validation; prototype query subset only')

if __name__ == '__main__':
    result = validate()
    Path(__file__).with_name('placement-verification.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))
