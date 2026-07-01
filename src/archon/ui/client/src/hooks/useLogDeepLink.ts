import { useEffect, useMemo, useRef } from 'react';
import { useLocation, useSearchParams } from 'react-router-dom';
import type { LogsResponse } from '../types';

interface FromLocationState {
  from?: {
    pathname: string;
    search?: string;
  };
}

/**
 * Logs deep-link handling:
 * - consume iter/file/ts only once on initial load
 * - after that, user navigation owns selectedFile
 * - back-link comes from router state, not query params
 */
export function useLogDeepLink(logsData?: LogsResponse) {
  const [searchParams] = useSearchParams();
  const location = useLocation();
  const consumedRef = useRef(false);

  const target = useMemo(() => ({
    iter: searchParams.get('iter') || '',
    file: searchParams.get('file') || '',
    ts: searchParams.get('ts') || '',
  }), []);

  const backTarget = (location.state as FromLocationState | null)?.from || null;

  const resolveInitialSelectedFile = useMemo(() => {
    if (!logsData || consumedRef.current) return '';
    if (!target.iter || !target.file) return '';
    for (const g of logsData.groups) {
      if (g.id !== target.iter) continue;
      const match = g.files.find(f => f.name === `${target.file}.jsonl` || f.name === target.file);
      if (match) return match.path;
    }
    return '';
  }, [logsData, target]);

  useEffect(() => {
    if (resolveInitialSelectedFile) consumedRef.current = true;
  }, [resolveInitialSelectedFile]);

  return {
    initialSelectedFile: resolveInitialSelectedFile,
    initialHighlightTs: target.ts,
    backTarget,
  };
}
