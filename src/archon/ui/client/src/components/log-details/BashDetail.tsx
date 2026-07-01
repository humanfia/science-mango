/**
 * BashDetail — renders Bash tool_call with styled command block
 */
import styles from './details.module.css';

interface Props {
  input: Record<string, unknown>;
}

export default function BashDetail({ input }: Props) {
  const command = String(input.command || '');
  const timeout = input.timeout_ms ? `${Math.round(Number(input.timeout_ms) / 1000)}s` : '';

  return (
    <div className={styles.container}>
      <div className={styles.header}>
        <span className={styles.icon}>$</span>
        <span className={styles.label}>Bash</span>
        {timeout && <span className={styles.meta}>timeout: {timeout}</span>}
      </div>
      <pre className={styles.bashBlock}>{command}</pre>
    </div>
  );
}
