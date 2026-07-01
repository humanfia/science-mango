export interface UnifiedDiffResult {
  diff: string;
  addedLines: number;
  removedLines: number;
}

type DiffOp =
  | { type: 'context'; line: string }
  | { type: 'remove'; line: string }
  | { type: 'add'; line: string };

const MATRIX_LIMIT = 2_000_000;

function splitLines(content: string): string[] {
  if (!content) return [];
  return content.split('\n');
}

function countPrefix(a: string[], b: string[]) {
  let i = 0;
  while (i < a.length && i < b.length && a[i] === b[i]) i += 1;
  return i;
}

function countSuffix(a: string[], b: string[], prefix: number) {
  let i = 0;
  while (
    i < a.length - prefix &&
    i < b.length - prefix &&
    a[a.length - 1 - i] === b[b.length - 1 - i]
  ) {
    i += 1;
  }
  return i;
}

function diffMiddle(oldLines: string[], newLines: string[]): DiffOp[] {
  const oldLen = oldLines.length;
  const newLen = newLines.length;

  if (oldLen === 0) return newLines.map(line => ({ type: 'add', line }));
  if (newLen === 0) return oldLines.map(line => ({ type: 'remove', line }));

  if (oldLen * newLen > MATRIX_LIMIT) {
    return [
      ...oldLines.map(line => ({ type: 'remove', line } as DiffOp)),
      ...newLines.map(line => ({ type: 'add', line } as DiffOp)),
    ];
  }

  const dp: number[][] = Array.from({ length: oldLen + 1 }, () => Array(newLen + 1).fill(0));
  for (let i = oldLen - 1; i >= 0; i -= 1) {
    for (let j = newLen - 1; j >= 0; j -= 1) {
      dp[i][j] = oldLines[i] === newLines[j]
        ? dp[i + 1][j + 1] + 1
        : Math.max(dp[i + 1][j], dp[i][j + 1]);
    }
  }

  const ops: DiffOp[] = [];
  let i = 0;
  let j = 0;
  while (i < oldLen && j < newLen) {
    if (oldLines[i] === newLines[j]) {
      ops.push({ type: 'context', line: oldLines[i] });
      i += 1;
      j += 1;
    } else if (dp[i + 1][j] >= dp[i][j + 1]) {
      ops.push({ type: 'remove', line: oldLines[i] });
      i += 1;
    } else {
      ops.push({ type: 'add', line: newLines[j] });
      j += 1;
    }
  }
  while (i < oldLen) {
    ops.push({ type: 'remove', line: oldLines[i] });
    i += 1;
  }
  while (j < newLen) {
    ops.push({ type: 'add', line: newLines[j] });
    j += 1;
  }
  return ops;
}

export function createUnifiedDiff(fromLabel: string, toLabel: string, oldContent: string, newContent: string): UnifiedDiffResult {
  if (oldContent === newContent) {
    return { diff: '', addedLines: 0, removedLines: 0 };
  }

  const oldLines = splitLines(oldContent);
  const newLines = splitLines(newContent);
  const prefix = countPrefix(oldLines, newLines);
  const suffix = countSuffix(oldLines, newLines, prefix);

  const prefixOps = oldLines.slice(0, prefix).map(line => ({ type: 'context', line } as DiffOp));
  const middleOps = diffMiddle(
    oldLines.slice(prefix, oldLines.length - suffix),
    newLines.slice(prefix, newLines.length - suffix),
  );
  const suffixOps = oldLines.slice(oldLines.length - suffix).map(line => ({ type: 'context', line } as DiffOp));
  const ops = [...prefixOps, ...middleOps, ...suffixOps];

  const addedLines = ops.filter(op => op.type === 'add').length;
  const removedLines = ops.filter(op => op.type === 'remove').length;
  const oldStart = oldLines.length > 0 ? 1 : 0;
  const newStart = newLines.length > 0 ? 1 : 0;
  const body = ops.map(op => `${op.type === 'context' ? ' ' : op.type === 'remove' ? '-' : '+'}${op.line}`).join('\n');
  const diff = [
    `--- ${fromLabel}`,
    `+++ ${toLabel}`,
    `@@ -${oldStart},${oldLines.length} +${newStart},${newLines.length} @@`,
    body,
  ].join('\n');

  return { diff, addedLines, removedLines };
}
