import type { Milestone } from '../types';
import { STATUS_COLORS } from '../utils/constants';
import AttemptCard from './AttemptCard';
import styles from './MilestoneCard.module.css';

interface Props { milestone: Milestone; }

export default function MilestoneCard({ milestone: m }: Props) {
  return (
    <div className={styles.card} style={{ borderLeftColor: STATUS_COLORS[m.status] || 'var(--border)' }}>
      <div className={styles.header}>
        <code className={styles.file}>{m.target?.file || '?'}</code>
        <span className={styles.theorem}>{m.target?.theorem || '?'}</span>
        <span className={styles.badge} style={{ color: STATUS_COLORS[m.status] }}>{m.status}</span>
      </div>
      {m.findings?.blocker && (
        <div className={styles.blocker}>Blocker: {m.findings.blocker}</div>
      )}
      {m.findings?.key_lemmas_used && m.findings.key_lemmas_used.length > 0 && (
        <div className={styles.lemmas}>Lemmas: {m.findings.key_lemmas_used.join(', ')}</div>
      )}
      {m.attempts && m.attempts.length > 0 && (
        <div className={styles.attempts}>
          {m.attempts.map((att, i) => <AttemptCard key={i} att={att} />)}
        </div>
      )}
      {m.next_steps && (
        <div className={styles.nextSteps}>Next: {m.next_steps}</div>
      )}
    </div>
  );
}
