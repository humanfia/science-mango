/**
 * SnapshotDetail — renders code_snapshot event with step info + link to Diffs
 */
import { useNavigate } from 'react-router-dom';
import styles from './details.module.css';
import type { LogEntry } from '../../types';

interface Props {
  entry: LogEntry;
}

export default function SnapshotDetail({ entry }: Props) {
  const navigate = useNavigate();
  const step = entry.step ?? '?';
  const file = entry.file ?? '';
  const tool = entry.tool ?? 'Edit';
  const snapshotPath = entry.snapshot_path ?? '';
  const oldStr = entry.old_string ?? '';
  const newStr = entry.new_string ?? '';

  // Derive slug from file path for Diffs navigation
  const slug = file.replace(/\//g, '_').replace(/\.lean$/, '');

  const goToDiffs = () => {
    const params = new URLSearchParams({ file: slug, step: String(step) });
    navigate(`/diffs?${params.toString()}`);
  };

  return (
    <div className={styles.container}>
      <div className={styles.header}>
        <span className={styles.icon}>📸</span>
        <span className={styles.label}>Snapshot Step {step}</span>
        <span className={styles.path}>{file}</span>
      </div>
      <div className={styles.snapshotBody}>
        {oldStr && (
          <div className={styles.snapshotChange}>
            <span className={styles.changeRemove}>− {oldStr.length > 120 ? oldStr.slice(0, 120) + '…' : oldStr}</span>
          </div>
        )}
        {newStr && (
          <div className={styles.snapshotChange}>
            <span className={styles.changeAdd}>+ {newStr.length > 120 ? newStr.slice(0, 120) + '…' : newStr}</span>
          </div>
        )}
        <div className={styles.snapshotMeta}>
          <span>{tool} → {snapshotPath.split('/').pop()}</span>
          <button className={styles.linkBtn} onClick={goToDiffs}>View in Diffs →</button>
        </div>
      </div>
    </div>
  );
}
