"""
stage1_planner.py

实现了“阶段一：GoT 分解” (GoT Decomposition)。
- 包含“简单规划器”逻辑
"""

from collections import deque
from modules.data_structures import ConceptualGraph, NodeStatus, ConceptNode
from modules.llm_modules import ExpansionDecision, LLMModules
from modules.external_tools import LeanSearchClient
from modules.problem_contract import build_problem_contract
from modules.knowledge_base import load_knowledge_base
from modules.knowledge_graph_manager import KnowledgeGraphManager
import json
import logging
import config


class GoTPlanner:
    """
    实现阶段一 (GoT 分解) 的主循环。
    """

    def __init__(self):
        # 注入所有需要的模块
        self.llm = LLMModules()
        self.lean_search = LeanSearchClient()  # 初始化外部工具

        print("[GoTPlanner] 正在加载“已验证知识库”...")
        # 加载 KB (格式: {"key": {"code": "...", "deps": [...]}})
        #self.verified_kb = load_knowledge_base()
        self.verified_kb = {}
        print(f"[GoTPlanner] 已加载 {len(self.verified_kb)} 个已验证的节点。")

        print("GoTPlanner (阶段一) 已初始化。")

    def _reconstruct_graph_from_kb(self, root_name: str, subgraph_data: dict) -> ConceptualGraph:
        """
        辅助函数：将 KB 返回的字典数据重建为 ConceptualGraph 对象。
        """
        # 1. 初始化图对象
        graph = ConceptualGraph(root_name=root_name)

        # 2. 创建所有节点对象的映射表 (Key -> ConceptNode)
        #    这样我们才能在后续步骤中建立父子连接
        node_map = {}

        # 先创建所有节点实例
        for key, data in subgraph_data.items():
            # 使用保存时的原始名称 (Original Case)
            name = data.get("original_name", key)

            # 创建节点
            # 注意：这里 parent 暂时设为 None，后面连接时再补
            node = ConceptNode(name=name)

            # 关键：标记状态为 GROUNDED，且来源为 VerifiedKB
            # 这样 Stage 2 看到这个标记，就会去 synthesize_cache 或 KB 里找代码，而不会重新生成
            node.status = NodeStatus.GROUNDED
            node.grounded_definition = ["VerifiedKB"]

            node_map[key] = node

        # 3. 建立连线 (父 -> 子)
        for key, data in subgraph_data.items():
            if key not in node_map: continue

            current_node = node_map[key]
            deps = data.get("deps", [])

            for dep_key in deps:
                # 规范化依赖 key (防止大小写不一致)
                norm_dep_key = dep_key.strip().lower()

                if norm_dep_key in node_map:
                    child_node = node_map[norm_dep_key]

                    # 建立连接
                    current_node.dependencies.append(child_node)
                    child_node.parent = current_node
                else:
                    logging.warning(f"  [Reconstruct] 警告：节点 '{key}' 依赖 '{dep_key}'，但该依赖不在子图中。")

        # 4. 替换图的根节点
        # KB 加载是基于 key 匹配的，我们需要把图的 root 指向那个匹配到的节点
        root_key = root_name.strip().lower()
        if root_key in node_map:
            # 替换根节点
            graph.root = node_map[root_key]
            # 重建图的索引
            graph.nodes = {n.id: n for n in node_map.values()}
            graph._nodes_by_name = {n.name.lower().strip(): n for n in node_map.values()}
        else:
            logging.warning(f"  [Reconstruct] 警告：无法在加载的数据中找到根节点 '{root_name}'。将返回空图。")

        return graph

    def _log_dependency_graph(self, graph: ConceptualGraph):
        """
        [新增] 以树状结构漂亮地打印依赖图到日志和终端
        """
        logging.info("\n" + "=" * 40)
        logging.info("🌳 [Stage 1 Output] 概念依赖图构建完成")
        logging.info("=" * 40)

        def print_node(node, prefix="", is_last=True):
            # 符号美化
            connector = "└── " if is_last else "├── "

            # 状态图标
            status_icon = {
                NodeStatus.GROUNDED: "✅",  # 已接地
                NodeStatus.TO_SYNTHESIZE: "🛠️",  # 待合成
                NodeStatus.TO_EXPAND: "❓"
            }.get(node.status, "")

            grounding_info = ""
            if node.grounded_definition:
                # 只显示前几个字符，防止太长
                defs = str(node.grounded_definition)
                if len(defs) > 50: defs = defs[:47] + "..."
                grounding_info = f" -> {defs}"

            # 打印当前行
            logging.info(f"{prefix}{connector}{status_icon} {node.name}{grounding_info}")

            # 准备下一级的缩进
            new_prefix = prefix + ("    " if is_last else "│   ")

            children = node.dependencies
            count = len(children)
            for i, child in enumerate(children):
                print_node(child, new_prefix, i == count - 1)

        # 从根节点开始打印
        print_node(graph.root)
        logging.info("=" * 40 + "\n")

    def _run_expansion_decision(
        self,
        concept_name: str,
        image_path: str = None,
        problem_context: str = "",
    ) -> ExpansionDecision:
        if hasattr(self.llm, "run_expansion_decision"):
            try:
                return self.llm.run_expansion_decision(
                    concept_name,
                    image_path=image_path,
                    problem_context=problem_context,
                )
            except TypeError:
                return self.llm.run_expansion_decision(
                    concept_name, image_path=image_path
                )
        try:
            dependencies = self.llm.run_expansion_module(
                concept_name, image_path=image_path, problem_context=problem_context
            )
        except TypeError:
            dependencies = self.llm.run_expansion_module(
                concept_name, image_path=image_path
            )
        return ExpansionDecision(
            decision="EXPAND" if dependencies else "STOP_ATOMIC",
            dependencies=dependencies,
            reason="legacy expansion API",
        )

    def _node_depth(self, node: ConceptNode) -> int:
        depth = 0
        current = node.parent
        visited = set()
        while current and current.id not in visited:
            visited.add(current.id)
            depth += 1
            current = current.parent
        return depth

    def _is_physics_context_leaf(self, concept_name: str) -> bool:
        """Return true for diagram/setup context nodes that should not be split.

        These nodes preserve labels and apparatus semantics for Stage2, but
        splitting them into one node per switch, terminal, or supply creates a
        noisy graph and often causes Lean namespace collisions.
        """
        if getattr(config, "CURRENT_DOMAIN", "math") != "physics":
            return False
        normalized = concept_name.lower().strip()
        compact = normalized.replace("_", "").replace("-", "").replace(" ", "")
        leaf_markers = (
            "experimentsetupcontext",
            "setuplabels",
            "setupcontext",
            "diagramcontext",
            "apparatuscontext",
            "visualcontext",
            "contextlabels",
            "apparatuslabels",
            ".setup",
            ".context",
            ".labels",
        )
        if any(marker in compact or marker in normalized for marker in leaf_markers):
            return True
        return normalized.startswith("apparatus.")

    def _attach_dependency_names(
        self,
        graph: ConceptualGraph,
        parent: ConceptNode,
        dependency_names: list[str],
        queue: deque,
        queue_log: set[str],
        max_nodes: int | None = None,
    ) -> None:
        for name in dependency_names:
            name_key = name.lower().strip()
            if not name_key:
                continue

            if name_key == parent.name.lower().strip():
                logging.warning(f"🚫 [LoopGuard] 拦截自我引用: '{parent.name}'")
                continue

            existing_node = graph.find_node_by_name(name_key)

            if existing_node:
                if existing_node.id == parent.id:
                    continue

                def is_ancestor(ancestor_node, target_node):
                    stack = [ancestor_node]
                    visited = set()
                    while stack:
                        curr = stack.pop()
                        if curr.id == target_node.id:
                            return True
                        if curr.id in visited:
                            continue
                        visited.add(curr.id)
                        for dep in curr.dependencies:
                            stack.append(dep)
                    return False

                if is_ancestor(existing_node, parent):
                    logging.warning(
                        f"🛑 [LoopGuard] 拦截死循环依赖: '{parent.name}' -> '{existing_node.name}'"
                    )
                    continue

                if existing_node not in parent.dependencies:
                    parent.dependencies.append(existing_node)
                    logging.info(f"      🔗 [Link] 链接到已有节点: {existing_node.name}")
            else:
                if max_nodes is not None and len(graph.nodes) >= max_nodes:
                    logging.warning(
                        f"🛑 [Planner] 达到最大节点数限制 {max_nodes}，"
                        f"跳过新增依赖节点: {name}"
                    )
                    continue
                new_node = graph.add_node(name=name, parent=parent)
                if name_key not in queue_log:
                    queue.append(new_node)
                    queue_log.add(name_key)
                    logging.info(f"      + [New] 新增依赖节点: {name}")

    def run(self, informal_statement: str, image_path: str = None) -> ConceptualGraph:
        """
        主方法：执行完整的阶段一分解流程。
        """
        logging.info(f"--- [阶段一：GoT 分解] 开始 ---")

        final_problem_statement = informal_statement

        if image_path:
            logging.info(f"🖼️ [Multimodal] 检测到图片输入，正在执行‘图文融合’...")
            try:
                # 调用 LLM 将图片中的几何标记/数值融合进文本
                enhanced_text = self.llm.run_multimodal_synthesis(informal_statement, image_path)

                # 简单验证一下返回结果不为空
                if enhanced_text and len(enhanced_text.strip()) > 5:
                    logging.info(f"    原始题目: {informal_statement[:50]}...")
                    logging.info(f"    融合题目: {enhanced_text[:100]}...")
                    final_problem_statement = enhanced_text
                else:
                    logging.warning("⚠️ [Multimodal] 融合结果为空或过短，保留原题目。")

            except Exception as e:
                logging.warning(f"⚠️ [Multimodal] 图文融合模块出错 ({e})，将回退到原始文本。")

        # =========== [Step 1: 知识库查重] ===========
        # subgraph_data = KnowledgeGraphManager.load_dependency_tree(final_problem_statement)
        #
        # if subgraph_data:
        #     logging.info(f"🎉 [Planner] 命中完整知识图谱！找到 {len(subgraph_data)} 个节点。")
        #     logging.info(f"    正在重建依赖图并跳过分解步骤...")
        #     try:
        #         graph = self._reconstruct_graph_from_kb(final_problem_statement, subgraph_data)
        #         self._log_dependency_graph(graph)
        #         return graph
        #     except Exception as e:
        #         logging.error(f"!! [Planner] 重建图谱失败: {e}，转为常规分解流程。")

        graph = ConceptualGraph(root_name=final_problem_statement)
        queue = deque()
        queue_log = {graph.root.name.lower().strip()}
        max_nodes_limit = getattr(config, "PHYSICS_MAX_GRAPH_NODES", 50)
        max_depth_limit = getattr(config, "PHYSICS_MAX_GRAPH_DEPTH", 6)
        problem_context = build_problem_contract(final_problem_statement)

        logging.info(f"[Planner] 步骤 1: 优先分解根节点 '{graph.root.name}'...")
        graph.root.status = NodeStatus.TO_SYNTHESIZE

        # [消融实验] 跳过依赖图分解，直接以根节点作为完整图返回
        if config.ABLATION_NO_DECOMPOSE:
            logging.info("[Planner] ⚡ 消融模式：跳过依赖图分解，直接合成根节点。")
            self._log_dependency_graph(graph)
            return graph

        if max_depth_limit <= 0:
            root_expansion = ExpansionDecision(
                decision="STOP_ATOMIC",
                dependencies=[],
                reason="configured max graph depth reached at root",
            )
        else:
            root_expansion = self._run_expansion_decision(
                graph.root.name, image_path=None, problem_context=problem_context
            )  # 现在分解看不到图片
        dependency_names = root_expansion.dependencies

        logging.info(f"[Planner] 步骤 2: 将根节点的依赖项加入队列...")
        if root_expansion.failed:
            logging.warning(
                f"[Planner] 根节点分解失败或未知: {root_expansion.reason}"
            )
        elif root_expansion.is_atomic_stop:
                logging.warning("[Planner] 根节点被判定为 atomic，依赖图只有根节点。")
        self._attach_dependency_names(
            graph, graph.root, dependency_names, queue, queue_log, max_nodes_limit
        )

        # =========== [Step 3: BFS 循环处理] ===========
        logging.info("[Planner] 步骤 3: 开始 '广度优先' 分解与接地 *子节点*...")

        while queue:
            if len(graph.nodes) > max_nodes_limit:
                logging.warning("🛑 [Planner] 达到最大节点数限制，强制停止分解！")
                break
            current_node = queue.popleft()
            current_name_key = current_node.name.lower().strip()
            logging.info(f"[Planner] 正在处理: '{current_node.name}'")

            if self._is_physics_context_leaf(current_node.name):
                current_node.status = NodeStatus.TO_SYNTHESIZE
                logging.info(
                    f"[Planner] -> 🧱 CONTEXT_LEAF: '{current_node.name}' "
                    "保留为单个上下文节点，不拆成逐标签依赖。"
                )
                continue

            # 3.1 检查本地知识库
            if current_name_key in self.verified_kb:
                current_node.status = NodeStatus.GROUNDED
                current_node.grounded_definition = ["VerifiedKB"]
                logging.debug(f"[Planner] -> ✅ GROUNDED (来自本地知识库)")
                continue

            # 3.2 外部搜索 (LeanSearch)
            search_results = self.lean_search.search(current_node.name)

            logging.debug(f"  [Planner] 正在执行接地 (Text)...")

            # 3.3 LLM 接地判定
            grounding_result = self.llm.run_grounding_reasoner(
                concept_name=current_node.name,
                candidates=search_results,
                image_path=None  # 子节点通常是抽象概念，不需要看图
            )

            final_definitions = []
            if grounding_result.is_found and grounding_result.definitions:
                final_definitions = grounding_result.definitions

            # 3.4 处理接地成功
            if final_definitions:
                current_node.status = NodeStatus.GROUNDED
                current_node.grounded_definition = final_definitions
                chosen_def = final_definitions[0]

                matched_candidate = next((c for c in search_results if c.full_lean_name == chosen_def), None)

                if matched_candidate and matched_candidate.lean_type:
                    # 将 lean_type (statement_text) 存入节点
                    # Stage 2 将使用它来告诉模型具体的函数签名
                    current_node.grounding_info = {
                        "lean_type": matched_candidate.lean_type,
                        "description": matched_candidate.informal_description
                    }
                    logging.info(f"      [Info] Saved signature for {chosen_def}")

                logging.info(f"[Planner] -> ✅ GROUNDED (Matches: {final_definitions})")
                continue

            # 3.5 接地失败 -> 标记为待合成 -> 继续分解
            current_node.status = NodeStatus.TO_SYNTHESIZE
            logging.info(f"[Planner] -> 🛠️ TO_SYNTHESIZE (将进行分解...)")

            current_depth = self._node_depth(current_node)
            if current_depth >= max_depth_limit:
                logging.info(
                    f"[Planner] -> 🧱 MAX_DEPTH({max_depth_limit}): "
                    f"'{current_node.name}' 保留为待合成叶子。"
                )
                continue

            # 调用 LLM 分解子节点
            expansion = self._run_expansion_decision(
                current_node.name, image_path=None, problem_context=problem_context
            )
            if expansion.is_atomic_stop:
                logging.info(
                    f"[Planner] -> 🧱 STOP_ATOMIC: '{current_node.name}' 不再继续分解。"
                )
                continue
            if expansion.failed:
                logging.warning(
                    f"[Planner] -> ⚠️ EXPANSION_FAILED: '{current_node.name}' "
                    f"未能可靠分解 ({expansion.reason})，保留为待合成叶子。"
                )
                continue

            self._attach_dependency_names(
                graph, current_node, expansion.dependencies, queue, queue_log, max_nodes_limit
            )

        self._log_dependency_graph(graph)

        return graph


def print_graph_tree(node, indent=""):
    """辅助函数：漂亮地打印依赖图"""
    status_emoji = {
        NodeStatus.GROUNDED: "✅",
        NodeStatus.TO_SYNTHESIZE: "🛠️",
        NodeStatus.TO_EXPAND: "❓"
    }
    def_name = ""
    if node.grounded_definition == "VerifiedKB":
        def_name = " (as: VerifiedKB)"
    elif node.grounded_definition:
        def_name = f" (as: {node.grounded_definition})"

    print(f"{indent}{status_emoji.get(node.status, '❓')} {node.name}{def_name}")
    for dep in node.dependencies:
        print_graph_tree(dep, indent + "  ")


def demonstrate_stage1_to_stage2_interface(graph: ConceptualGraph):
    """
    演示为阶段二准备的接口 (.get_build_order())
    """
    print("\n--- [为阶段二准备的接口演示] ---")
    print("阶段二 (合成) 将按以下“自下而上”的顺序执行：")

    build_order = graph.get_build_order()

    for i, node in enumerate(build_order):
        print(f"  步骤 {i + 1}: ", end="")
        if node.status == NodeStatus.GROUNDED:
            if node.grounded_definition == "VerifiedKB":
                print(f"使用本地知识库 (KB) 定义 '{node.name}'")
            else:
                print(f"使用 Mathlib 定义 '{node.grounded_definition or node.name}'")
        elif node.status == NodeStatus.TO_SYNTHESIZE:
            print(f"**生成** '{node.name}' (依赖: {[dep.name for dep in node.dependencies]})")


if __name__ == "__main__":
    # 我们可以在这里运行测试
    print("=" * 40)
    print(" 运行示例 1：Koethe 猜想 ")
    print("=" * 40)

    planner = GoTPlanner()
    graph1 = planner.run(r"""Prove that if $H$ is a subgroup of $G$ of index $n$, then there is a normal subgroup $K$ of $G$ such that $K\leq H$ and $[G:K]\leq n!$""")

    print("\n[阶段一 最终输出：依赖图]")
    print_graph_tree(graph1.root)

    demonstrate_stage1_to_stage2_interface(graph1)
