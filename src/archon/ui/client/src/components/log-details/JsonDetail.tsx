/**
 * JsonDetail — fallback detail renderer for structured data
 *
 * Renders collapsible key-value pairs instead of raw JSON.
 */
import { useState } from 'react';
import styles from './details.module.css';

interface Props {
  data: unknown;
  bare?: boolean;
}

const MAX_DEPTH = 10;
const STRING_PREVIEW = 220;

function JsonNode({ label, value, depth = 0 }: { label?: string; value: unknown; depth?: number }) {
  const [open, setOpen] = useState(depth < 1);
  const [showFullString, setShowFullString] = useState(false);

  if (depth > MAX_DEPTH) {
    return (
      <div className={styles.jsonLeaf}>
        {label && <span className={styles.jsonKey}>{label}: </span>}
        <span className={styles.jsonNull}>…(depth limit)</span>
      </div>
    );
  }

  if (value === null || value === undefined) {
    return <span className={styles.jsonNull}>{label && <span className={styles.jsonKey}>{label}: </span>}null</span>;
  }

  if (typeof value === 'string') {
    const truncated = value.length > STRING_PREVIEW;
    const display = truncated && !showFullString ? value.slice(0, STRING_PREVIEW) + '…' : value;
    return (
      <div className={styles.jsonLeaf}>
        {label && <span className={styles.jsonKey}>{label}: </span>}
        <span className={styles.jsonString}>"{display}"</span>
        {truncated && (
          <button type="button" className={styles.inlineToggleBtn} onClick={() => setShowFullString(v => !v)}>
            {showFullString ? 'show less' : 'show more'}
          </button>
        )}
      </div>
    );
  }

  if (typeof value === 'number' || typeof value === 'boolean') {
    return (
      <div className={styles.jsonLeaf}>
        {label && <span className={styles.jsonKey}>{label}: </span>}
        <span className={styles.jsonPrimitive}>{String(value)}</span>
      </div>
    );
  }

  if (Array.isArray(value)) {
    return (
      <div className={styles.jsonNode} style={{ paddingLeft: depth > 0 ? 12 : 0 }}>
        <span className={styles.jsonToggle} onClick={() => setOpen(!open)}>
          {label && <span className={styles.jsonKey}>{label}: </span>}
          [{open ? '' : `${value.length} items`}
          <span className={styles.expandHint}>{open ? ' ▾' : ' ▸'}</span>
        </span>
        {open && value.map((item, i) => <JsonNode key={i} label={String(i)} value={item} depth={depth + 1} />)}
        {open && <span>]</span>}
      </div>
    );
  }

  if (typeof value === 'object') {
    const entries = Object.entries(value as Record<string, unknown>);
    return (
      <div className={styles.jsonNode} style={{ paddingLeft: depth > 0 ? 12 : 0 }}>
        <span className={styles.jsonToggle} onClick={() => setOpen(!open)}>
          {label && <span className={styles.jsonKey}>{label}: </span>}
          {'{'}{open ? '' : `${entries.length} fields`}
          <span className={styles.expandHint}>{open ? ' ▾' : ' ▸'}</span>
        </span>
        {open && entries.map(([k, v]) => <JsonNode key={k} label={k} value={v} depth={depth + 1} />)}
        {open && <span>{'}'}</span>}
      </div>
    );
  }

  return <span>{String(value)}</span>;
}

export default function JsonDetail({ data, bare = false }: Props) {
  const tree = (
    <div className={styles.jsonTree}>
      <JsonNode value={data} />
    </div>
  );

  if (bare) return tree;

  return (
    <div className={styles.container}>
      {tree}
    </div>
  );
}
