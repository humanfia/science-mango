"""
Formalizer/stage3_alignment.py

这是语义对齐的“阶段三”控制器。
"""

import json
import re
from modules.llm_modules import LLMModules
from modules.data_structures import ConceptualGraph, ConceptNode, NodeStatus
from modules.knowledge_base import save_verified_nodes
from modules.knowledge_graph_manager import KnowledgeGraphManager

class SemanticAlignmentModule:
    """
    实现论文中的 Back-Translation 和 ASCC 流程。
    """

    def __init__(self):
        self.llm = LLMModules()
        print("[SemanticAlignmentModule] (阶段三) 已初始化。")

    def _normalize_node_name(self, name: str) -> str:
        """
        [关键修复] 与 Stage 2 保持完全一致的名称规范化逻辑。
        将多行、多空格压缩为单行单空格，并转小写。
        """
        return re.sub(r"\s+", " ", str(name)).strip().lower()

    def run(self,
            original_statement: str,
            synthesized_cache: dict[str, str],
            graph: ConceptualGraph,
            image_path: str = None) -> tuple[bool, dict]:
        """
        主方法：执行完整的语义对齐检查。
        返回 (is_consistent, report_dict)
        """
        print("[Aligner] 步骤 3.1: 正在运行“反向翻译”(Back-Translation)...")


        back_translated_segments = {}
        build_order = graph.get_build_order()


        for node in build_order:
            node_key = self._normalize_node_name(node.name)

            if node_key in synthesized_cache:
                code_chunk = synthesized_cache[node_key]
                print(f"  [Aligner] 正在反向翻译: '{node.name[:50]}...'")

                dep_nl_context = []
                for dep in node.dependencies:
                    dep_key = self._normalize_node_name(dep.name)
                    if dep_key in back_translated_segments:
                        dep_nl_context.append(
                            f"- {dep.name}: {back_translated_segments[dep_key]}"
                        )

                context_str = "\n".join(dep_nl_context)
                nl_description = self.llm.run_back_translation(
                    node_name=node.name,
                    code_chunk=code_chunk,
                    nl_context=context_str
                )
                back_translated_segments[node_key] = nl_description
            else:
                pass

        if not back_translated_segments:
            print("!! [Aligner] 警告: 没有生成任何反向翻译片段！(可能 Key 匹配依然失败)")
            return False, {"consistency_level": "level_3", "error": "No segments to merge"}

        print(f"  [Aligner] 正在合并 {len(back_translated_segments)} 个反向翻译片段...")
        merged_nl_description = self.llm.run_merge_back_translations(
            back_translated_segments
        )
        print(f"  [Aligner] 合并后的 NL (前200字符):\n{merged_nl_description[:200]}...")

        # 步骤 2: “自动语义一致性检查” (ASCC)
        print("\n[Aligner] 步骤 3.2: 正在运行“语义一致性检查”(ASCC)...")

        report_json_str = self.llm.run_semantic_check(
            original_nl=original_statement,
            back_translated_nl=merged_nl_description,
            image_path=image_path
        )

        try:
            text = report_json_str.strip()
            report = None

            match = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", text, re.DOTALL)
            if match:
                try:
                    report = json.loads(match.group(1))
                except json.JSONDecodeError:
                    pass

            if report is None:
                start_idx = text.find('{')
                end_idx = text.rfind('}')
                if start_idx != -1 and end_idx != -1:
                    try:
                        json_str = text[start_idx: end_idx + 1]
                        report = json.loads(json_str)
                    except json.JSONDecodeError:
                        pass
            if report is None:
                report = json.loads(text)

            consistency_level = report.get("consistency_level", "level_3")
            
            is_consistent = (consistency_level == "level_1" or consistency_level == "level_2")
            
            print(f"[Aligner] ASCC 检查完成。 语义一致性: {is_consistent}")
            
            if is_consistent:
                print(f"\n✅ [语义对齐] 成功：代码在语义上与原始问题一致 (Level: {report.get('consistency_level')})。")
                
                #print("[Aligner] 正在启动知识库保存流程...")
                #save_verified_nodes(synthesized_cache, graph)
                #KnowledgeGraphManager.save_subgraph(synthesized_cache, graph)
                
            else:
                 print(f"\n!! [语义对齐] 失败：检测到语义不一致 (Level: {report.get('consistency_level')})。")
                 print("   (失败的节点将不会被保存到知识库)")
            

            return is_consistent, report
            
        except json.JSONDecodeError as e:
            print(f"!! [Aligner] 严重错误: 无法解析 ASCC 模块的 JSON 响应。{e}")
            print(f"   原始响应:\n{report_json_str}")
            report = {
                "consistency_level": "level_3",
                "discrepancies": ["ASCC 模块返回了无效的 JSON。"],
                "recommendations": []
            }
            return False, report