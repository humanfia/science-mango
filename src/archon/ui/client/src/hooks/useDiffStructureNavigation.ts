import { useCallback, useState } from 'react';

export function useDiffStructureNavigation() {
  const [activeId, setActiveId] = useState<string>('');

  const jumpTo = useCallback((id: string) => {
    const el = document.getElementById(id);
    if (!el) return;
    setActiveId(id);
    el.scrollIntoView({ behavior: 'smooth', block: 'center' });
  }, []);

  return {
    activeId,
    setActiveId,
    jumpTo,
  };
}
