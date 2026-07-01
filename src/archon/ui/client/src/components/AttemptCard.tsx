import { useState } from 'react';
import type { Attempt } from '../types';
import styles from './AttemptCard.module.css';

interface Props { att: Attempt; }

export default function AttemptCard({ att }: Props) {
  const [expanded, setExpanded] = useState(false);
  return (
    <div className={styles.attempt}>
      <div className={styles.header} onClick={() => setExpanded(!expanded)}>
        <span className={styles.num}>#{att.attempt}</span>
        <span className={styles.strategy}>{att.strategy || '—'}</span>
        <span className={`${styles.result} ${styles[`result_${att.result}`]}`}>{att.result}</span>
        <span className={styles.expandHint}>{expanded ? '▾' : '▸'}</span>
      </div>
      {expanded && (
        <div className={styles.body}>
          {att.code_tried && (
            <div className={styles.field}>
              <span className={styles.label}>Code:</span>
              <pre className={styles.codeBlock}>{att.code_tried}</pre>
            </div>
          )}
          {att.lean_error && (
            <div className={styles.field}>
              <span className={styles.labelError}>Lean error:</span>
              <pre className={styles.errorBlock}>{att.lean_error}</pre>
            </div>
          )}
          {att.goal_before && (
            <div className={styles.field}>
              <span className={styles.label}>Goal before:</span>
              <code className={styles.goalCode}>{att.goal_before}</code>
            </div>
          )}
          {att.goal_after && (
            <div className={styles.field}>
              <span className={styles.label}>Goal after:</span>
              <code className={styles.goalCode}>{att.goal_after}</code>
            </div>
          )}
          {att.insight && (
            <div className={styles.insight}>💡 {att.insight}</div>
          )}
        </div>
      )}
    </div>
  );
}
