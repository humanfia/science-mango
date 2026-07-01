/** Cross-session target aggregation (mirrors cctest-dashboard aggregateTargets) */
import type { Milestone } from '../types';

export interface TargetHistory {
  file: string;
  theorem: string;
  status: string;
  sessions: string[];
  milestones: Milestone[];
  totalAttempts: number;
}

const STATUS_PRIORITY: Record<string, number> = {
  solved: 4, partial: 3, blocked: 2, failed_retry: 2, not_started: 1,
};

export function aggregateTargets(
  allMilestones: { sessionId: string; milestones: Milestone[] }[],
): TargetHistory[] {
  const map = new Map<string, TargetHistory>();

  for (const { sessionId, milestones } of allMilestones) {
    for (const m of milestones) {
      const file = m.target?.file || '?';
      const theorem = m.target?.theorem || '?';
      if (file === '?' && theorem === '?') continue;
      const key = `${file}::${theorem}`;

      if (!map.has(key)) {
        map.set(key, { file, theorem, status: m.status, sessions: [], milestones: [], totalAttempts: 0 });
      }
      const th = map.get(key)!;
      if ((STATUS_PRIORITY[m.status] || 0) > (STATUS_PRIORITY[th.status] || 0)) {
        th.status = m.status;
      }
      if (!th.sessions.includes(sessionId)) th.sessions.push(sessionId);
      th.milestones.push(m);
      th.totalAttempts += (m.attempts || []).length;
    }
  }

  return Array.from(map.values()).sort(
    (a, b) => a.file.localeCompare(b.file) || a.theorem.localeCompare(b.theorem),
  );
}
