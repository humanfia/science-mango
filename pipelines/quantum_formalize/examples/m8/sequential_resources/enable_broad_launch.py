from pathlib import Path

def enable_broad_launch(path):
 path=Path(path);s=path.read_text()
 if "broad_flow" in s:return
 before="argv=[str(Path(sys.executable).parent/'hmz')"
 snippet="""flow=P/'.humanize-formal-runs/broad_flow';flow.mkdir(exist_ok=True)
code=(repo/'pipelines/quantum_formalize/examples/m6/transfer/trace/replay_flow/__init__.py').read_text().replace('from pipelines.quantum_formalize.dag_runner import run_graph','from pipelines.quantum_formalize.dag_runner import run_graph\\nfrom pipelines.quantum_formalize.search import search_with_fallback').replace('timeout=config.compile_timeout)', 'timeout=config.compile_timeout, search=lambda queries: search_with_fallback(queries, fallback_queries=["algebra"]))')
(flow/'__init__.py').write_text(code)
"""
 assert before in s;s=s.replace(before,snippet+before).replace("str(repo/'pipelines/quantum_formalize_dag')", "str(flow)");path.write_text(s)
