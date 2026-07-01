/**
 * ToolResultDetail — renders tool_result with error/warning highlighting
 *
 * Highlights Lean compilation errors (lines containing "error:" or "warning:")
 * and renders JSON-like payloads in a structured view.
 */
import JsonDetail from './JsonDetail';
import styles from './details.module.css';

interface Props {
  content: string;
  structuredJson?: boolean;
}

function classifyLine(line: string): 'error' | 'warning' | 'success' | 'normal' {
  const lower = line.toLowerCase();
  if (
    lower.includes('error:') ||
    lower.includes('tool_use_error') ||
    lower.includes('eacces') ||
    lower.includes('type mismatch') ||
    lower.includes('unknown identifier') ||
    lower.includes('unknown constant') ||
    lower.includes('unsolved goals')
  )
    return 'error';
  if (
    lower.includes('warning:') ||
    lower.includes("uses 'sorry'") ||
    /tactic '[^']+' failed/.test(lower)
  )
    return 'warning';
  if (lower.includes('successfully') || lower.includes('no errors'))
    return 'success';
  return 'normal';
}

function parseStructuredResult(content: string): unknown | null {
  const trimmed = content.trim();
  if (!trimmed) return null;
  if (!((trimmed.startsWith('{') && trimmed.endsWith('}')) || (trimmed.startsWith('[') && trimmed.endsWith(']')))) {
    return null;
  }
  try {
    return JSON.parse(trimmed);
  } catch {
    return null;
  }
}

function summarizeStructuredResult(data: unknown): { kind: string; size: string; tone: 'error' | 'warning' | 'success' | 'normal'; chips: string[] } {
  if (Array.isArray(data)) {
    return { kind: 'JSON array', size: `${data.length} items`, tone: 'normal', chips: [] };
  }

  if (data && typeof data === 'object') {
    const obj = data as Record<string, unknown>;
    const entries = Object.entries(obj);
    const chips: string[] = [];

    const keyOrder = ['status', 'success', 'error', 'message', 'count', 'path'];
    for (const key of keyOrder) {
      if (!(key in obj)) continue;
      const value = obj[key];
      if (typeof value === 'string' || typeof value === 'number' || typeof value === 'boolean') {
        const rendered = String(value);
        chips.push(`${key}: ${rendered.length > 48 ? rendered.slice(0, 48) + '…' : rendered}`);
      }
      if (chips.length >= 3) break;
    }

    let tone: 'error' | 'warning' | 'success' | 'normal' = 'normal';
    const errorValue = obj.error;
    const successValue = obj.success;
    const statusValue = typeof obj.status === 'string' ? obj.status.toLowerCase() : '';
    if ((typeof errorValue === 'string' && errorValue.trim()) || statusValue === 'error' || statusValue === 'failed' || successValue === false) {
      tone = 'error';
    } else if (statusValue === 'warning') {
      tone = 'warning';
    } else if (statusValue === 'ok' || statusValue === 'success' || successValue === true) {
      tone = 'success';
    }

    return { kind: 'JSON object', size: `${entries.length} fields`, tone, chips };
  }

  return { kind: 'JSON value', size: typeof data, tone: 'normal', chips: [] };
}

export default function ToolResultDetail({ content, structuredJson = true }: Props) {
  const structured = structuredJson ? parseStructuredResult(content) : null;

  if (structured !== null) {
    const summary = summarizeStructuredResult(structured);
    return (
      <div className={styles.container}>
        <div className={styles.header}>
          <span className={styles.icon}>
            {summary.tone === 'error' ? '❌' : summary.tone === 'warning' ? '⚠️' : '🧩'}
          </span>
          <span className={styles.label}>Structured result</span>
          <span className={styles.meta}>{summary.kind} · {summary.size}</span>
        </div>
        {summary.chips.length > 0 && (
          <div className={styles.summaryBar}>
            {summary.chips.map(chip => (
              <span key={chip} className={
                summary.tone === 'error' ? styles.summaryChipError :
                summary.tone === 'warning' ? styles.summaryChipWarning :
                summary.tone === 'success' ? styles.summaryChipSuccess :
                styles.summaryChip
              }>
                {chip}
              </span>
            ))}
          </div>
        )}
        <JsonDetail data={structured} bare />
      </div>
    );
  }

  const lines = content.split('\n');
  const hasError = lines.some(l => classifyLine(l) === 'error');

  return (
    <div className={styles.container}>
      <div className={styles.header}>
        <span className={styles.icon}>{hasError ? '❌' : '✅'}</span>
        <span className={styles.label}>Result</span>
        <span className={styles.meta}>{lines.length} lines</span>
      </div>
      <div className={styles.resultBlock}>
        {lines.map((line, i) => {
          const cls = classifyLine(line);
          return (
            <div key={i} className={
              cls === 'error' ? styles.resultError :
              cls === 'warning' ? styles.resultWarning :
              cls === 'success' ? styles.resultSuccess :
              styles.resultNormal
            }>
              {line || '\u00A0'}
            </div>
          );
        })}
      </div>
    </div>
  );
}
