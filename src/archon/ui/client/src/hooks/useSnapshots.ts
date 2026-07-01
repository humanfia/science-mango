import { useQuery } from '@tanstack/react-query';
import type { SnapshotProverSummary, FileSnapshotSummary, TimelineEntry, DiffResult } from '../types';

async function fetchJson<T>(url: string): Promise<T> {
  const res = await fetch(url);
  if (!res.ok) throw new Error(`API ${res.status}`);
  return res.json();
}

// --- Cross-iteration file-centric APIs ---

/** List all files that have snapshots, aggregated across iterations */
export function useSnapshotFiles() {
  return useQuery<FileSnapshotSummary[]>({
    queryKey: ['snapshotFiles'],
    queryFn: () => fetchJson('/api/snapshot-files'),
    refetchInterval: 10000,
  });
}

/** Get full timeline for a file across all iterations */
export function useFileTimeline(slug: string) {
  return useQuery<TimelineEntry[]>({
    queryKey: ['fileTimeline', slug],
    queryFn: () => fetchJson(`/api/snapshot-files/${slug}/timeline`),
    enabled: !!slug,
  });
}

/** Read a snapshot file content */
export function useSnapshotFileContent(slug: string, iteration: string, file: string) {
  return useQuery<{ name: string; iteration: string; content: string }>({
    queryKey: ['snapshotFileContent', slug, iteration, file],
    queryFn: () => fetchJson(`/api/snapshot-files/${slug}/${iteration}/${file}`),
    enabled: !!slug && !!iteration && !!file,
  });
}

// --- Per-iteration APIs (kept for other views) ---

export function useSnapshotProvers(iterationId: string) {
  return useQuery<SnapshotProverSummary[]>({
    queryKey: ['snapshotProvers', iterationId],
    queryFn: () => fetchJson(`/api/iterations/${iterationId}/snapshots`),
    enabled: !!iterationId,
    refetchInterval: 5000,
  });
}

export function useSnapshotDiffAll(iterationId: string, prover: string) {
  return useQuery<DiffResult[]>({
    queryKey: ['snapshotDiffAll', iterationId, prover],
    queryFn: () => fetchJson(`/api/iterations/${iterationId}/snapshots/${prover}/diff-all`),
    enabled: !!iterationId && !!prover,
  });
}
