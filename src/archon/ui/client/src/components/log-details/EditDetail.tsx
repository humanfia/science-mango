/**
 * EditDetail — renders Edit/Write tool_call details as a mini diff
 *
 * Shows file path + old_string → new_string with diff highlighting.
 * Reuses DiffView for consistency.
 */
import DiffView from '../DiffView';
import styles from './details.module.css';

interface Props {
  input: Record<string, unknown>;
  tool: string;
}

function buildMiniDiff(oldStr: string, newStr: string): string {
  const oldLines = oldStr ? oldStr.split('\n') : [];
  const newLines = newStr ? newStr.split('\n') : [];
  const oldCount = oldLines.length;
  const newCount = newLines.length;
  const oldStart = oldCount > 0 ? 1 : 0;
  const newStart = newCount > 0 ? 1 : 0;
  let result = `--- a/old\n+++ b/new\n@@ -${oldStart},${oldCount} +${newStart},${newCount} @@\n`;
  for (const line of oldLines) result += `-${line}\n`;
  for (const line of newLines) result += `+${line}\n`;
  return result;
}

export default function EditDetail({ input, tool }: Props) {
  const filePath = String(input.file_path || '');
  const oldString = String(input.old_string || '');
  const newString = String(input.new_string ?? (tool === 'Write' ? input.content ?? '' : ''));

  const isWrite = tool === 'Write';
  const fileName = filePath.split('/').slice(-2).join('/');

  if (isWrite) {
    // Write: show file content preview (no diff)
    const preview = newString.length > 2000 ? newString.slice(0, 2000) + '\n...(truncated)' : newString;
    return (
      <div className={styles.container}>
        <div className={styles.header}>
          <span className={styles.icon}>📝</span>
          <span className={styles.label}>Write</span>
          <span className={styles.path}>{fileName}</span>
        </div>
        <pre className={styles.codeBlock}>{preview}</pre>
      </div>
    );
  }

  // Edit: show diff
  if (!oldString && !newString) return null;

  const diff = buildMiniDiff(oldString, newString);
  const addedLines = newString.split('\n').length;
  const removedLines = oldString.split('\n').length;

  return (
    <div className={styles.container}>
      <div className={styles.header}>
        <span className={styles.icon}>✏️</span>
        <span className={styles.label}>Edit</span>
        <span className={styles.path}>{fileName}</span>
      </div>
      <DiffView
        diff={diff}
        addedLines={addedLines}
        removedLines={removedLines}
      />
    </div>
  );
}
