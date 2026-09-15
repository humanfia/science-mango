"""Render the actual scheduling graph and optional receipts as Mermaid."""
import argparse
import json
from pathlib import Path
from .dag_runner import load_graph


def render(graph_path, state_path=None):
    _, nodes = load_graph(graph_path)
    state = {} if state_path is None else json.loads(Path(state_path).read_text())['nodes']
    lines = ['flowchart TD']
    for node in nodes:
        status = state.get(node.id, {}).get('status', 'planned' if node.spec is None else 'pending')
        if status not in {'planned','pending','running','accepted','failed','blocked','cancelled'}:
            raise ValueError('unknown node status')
        lines.append(f'    {node.id}["{node.id}: {status}"]:::{status}')
        for dependency in node.dependencies:
            lines.append(f'    {dependency} --> {node.id}')
    lines.extend(['    classDef accepted fill:#dcfce7,stroke:#166534',
                  '    classDef running fill:#dbeafe,stroke:#1d4ed8',
                  '    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5',
                  '    classDef failed fill:#fee2e2,stroke:#991b1b',
                  '    classDef blocked fill:#ffedd5,stroke:#9a3412'])
    return '\n'.join(lines)+'\n'


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--graph',required=True,type=Path)
    parser.add_argument('--state',type=Path)
    args=parser.parse_args()
    print(render(args.graph,args.state),end='')
