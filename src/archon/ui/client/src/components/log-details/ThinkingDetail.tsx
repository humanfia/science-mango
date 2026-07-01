/**
 * ThinkingDetail — renders thinking/text content as lightweight markdown.
 */
import MarkdownBlock from '../MarkdownBlock';
import styles from './details.module.css';

interface Props {
  content: string;
  event: string;
}

export default function ThinkingDetail({ content, event }: Props) {
  return (
    <div className={styles.container}>
      <div className={styles.header}>
        <span className={styles.icon}>{event === 'thinking' ? '💭' : '💬'}</span>
        <span className={styles.label}>{event === 'thinking' ? 'Thinking' : 'Response'}</span>
        <span className={styles.meta}>{content.length} chars</span>
      </div>
      <div className={styles.thinkingBlock}>
        <MarkdownBlock content={content} className={styles.thinkingMarkdown} />
      </div>
    </div>
  );
}
