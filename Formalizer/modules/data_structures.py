"""
modules/data_structures.py

定义项目的核心数据结构：
- NodeStatus (Enum)
- ConceptNode (Class)
- ConceptualGraph (Class)
"""

import uuid
import json
from enum import Enum, auto
from collections import deque


class NodeStatus(Enum):
    """
    定义一个概念节点在分解阶段的几种可能状态
    """
    TO_EXPAND = auto()  # 待处理
    GROUNDED = auto()  # ✅ 已接地：在 Mathlib 中找到
    TO_SYNTHESIZE = auto()  # 🛠️ 待合成：Mathlib 中未找到


class ConceptNode:
    """
    概念依赖图中的一个节点。
    """

    def __init__(self, name: str, parent=None):
        self.id = str(uuid.uuid4())
        self.name: str = name.strip()
        self.status: NodeStatus = NodeStatus.TO_EXPAND
        self.dependencies: list['ConceptNode'] = []
        self.parent: 'ConceptNode' | None = parent

        # 如果 status == GROUNDED，这里将存储 Mathlib 中的权威定义名称
        #self.grounded_definition: str | None = None
        self.grounded_definition: list[str] = []
        self.grounding_info: dict | None = None
        # (可选) 存储接地失败时的参考片段信息
        # self.reference_snippet: str | None = None
        # self.reference_info: dict | None = None # 或者存储更完整的 LeanSearchResult

    def __repr__(self):
        return f"Node(name='{self.name.strip()}', status={self.status.name})"

    def to_dict(self):
        return {
            "id": self.id,
            "name": self.name,
            "status": self.status.name,  # Enum 转字符串
            "parent_id": self.parent.id if self.parent else None,
            "dependency_ids": [dep.id for dep in self.dependencies],
            "grounded_definition": self.grounded_definition
        }


class ConceptualGraph:
    """
    “代理的工作记忆”，存储整个依赖图。
    这是 Stage 1 的最终输出，也是 Stage 2 的主要输入。
    """

    def __init__(self, root_name: str):
        self.root = ConceptNode(name=root_name)
        self.nodes: dict[str, ConceptNode] = {self.root.id: self.root}

        # 按名称索引所有节点，用于快速查找共享依赖
        self._nodes_by_name: dict[str, ConceptNode] = {
            self.root.name.lower().strip(): self.root
        }

    def add_node(self, name: str, parent: ConceptNode) -> ConceptNode:
        """在图中添加一个新节点作为某个节点的依赖项"""
        # ConceptNode 的 __init__ 会自动 strip() name
        new_node = ConceptNode(name=name, parent=parent)
        parent.dependencies.append(new_node)
        self.nodes[new_node.id] = new_node

        # 将新节点添加到名称索引中
        self._nodes_by_name[new_node.name.lower().strip()] = new_node

        return new_node

    def find_node_by_name(self, name: str) -> ConceptNode | None:
        """
        通过规范化（小写、去空格）的名称在图中查找一个 *已存在* 的节点。
        """
        return self._nodes_by_name.get(name.lower().strip())

    def get_build_order(self) -> list[ConceptNode]:
        """
        **为阶段二提供的核心接口**
        """
        build_order = []
        visited = set()

        def post_order_traverse(node: ConceptNode):
            if node.id in visited:
                return
            visited.add(node.id)

            # 先递归访问所有依赖项
            for dep in node.dependencies:
                post_order_traverse(dep)

            build_order.append(node)

        post_order_traverse(self.root)
        return build_order

    def to_json(self) -> str:
        """将图导出为 JSON 字符串"""
        data = {
            "root_id": self.root.id,
            "nodes": [node.to_dict() for node in self.nodes.values()]
        }
        return json.dumps(data, indent=2, ensure_ascii=False)

    @staticmethod
    def from_json(json_str: str) -> 'ConceptualGraph':
        data = json.loads(json_str)

        graph = ConceptualGraph("DUMMY")
        graph.nodes.clear()
        graph._nodes_by_name.clear()

        temp_nodes = {}  # id -> ConceptNode
        node_data_map = {}  # id -> dict data

        for n_data in data["nodes"]:
            nid = n_data["id"]
            name = n_data["name"]

            # 创建节点
            new_node = ConceptNode(name=name)
            new_node.id = nid  # 恢复原始 ID

            # 恢复状态
            if "status" in n_data:
                new_node.status = getattr(NodeStatus, n_data["status"])

            new_node.grounded_definition = n_data.get("grounded_definition", [])

            temp_nodes[nid] = new_node
            node_data_map[nid] = n_data

            # 注册到图
            graph.nodes[nid] = new_node
            graph._nodes_by_name[name.lower().strip()] = new_node

        # 3. 第二遍遍历：恢复连接关系 (Parent/Dependencies)
        for nid, node in temp_nodes.items():
            n_data = node_data_map[nid]

            # 恢复 Parent
            parent_id = n_data.get("parent_id")
            if parent_id and parent_id in temp_nodes:
                node.parent = temp_nodes[parent_id]

            # 恢复 Dependencies
            dep_ids = n_data.get("dependency_ids", [])
            for dep_id in dep_ids:
                if dep_id in temp_nodes:
                    node.dependencies.append(temp_nodes[dep_id])

        # 4. 设置 Root
        root_id = data.get("root_id")
        if root_id and root_id in temp_nodes:
            graph.root = temp_nodes[root_id]
        else:
            raise ValueError("Invalid Graph JSON: Root ID not found.")

        return graph