"""
Formalizer/modules/knowledge_graph_manager.py
"""

import json
import os
import threading
import logging
from typing import Dict, List, Optional

try:
    import config
    from modules.data_structures import ConceptualGraph
except ImportError:
    # 允许在单独测试时没有这些模块，但实际运行时会报错
    pass

GRAPH_DB_FILE = os.path.join(getattr(config, 'FORMALIZER_DIR', '.'), "knowledge_graph_v2.json")

_lock = threading.RLock()


def _normalize_key(name: str) -> str:
    """统一 Key 的格式：小写 + 去除首尾空格"""
    return str(name).strip().lower()


class KnowledgeGraphManager:
    """
    单例模式或静态工具类，管理图谱的 I/O
    """

    @staticmethod
    def _load_full_db() -> Dict[str, dict]:
        """内部方法：加载整个 JSON 数据库"""
        if not os.path.exists(GRAPH_DB_FILE):
            return {}
        try:
            with open(GRAPH_DB_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            return data if isinstance(data, dict) else {}
        except (IOError, json.JSONDecodeError) as e:
            logging.error(f"!! [KG Manager] 读取图谱文件失败: {e}")
            return {}

    @staticmethod
    def _save_full_db(data: Dict[str, dict]):
        """内部方法：保存整个 JSON 数据库"""
        try:
            with open(GRAPH_DB_FILE, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
        except IOError as e:
            logging.error(f"!! [KG Manager] 写入图谱文件失败: {e}")

    @classmethod
    def save_subgraph(cls, synthesized_cache: Dict[str, str], graph: ConceptualGraph):
        """
        [保存逻辑]
        将当前通过验证的图结构保存到数据库中。
        策略：
        1. 跳过 Root 节点（因为它包含具体数值，不可复用）。
        2. 保存所有中间节点的代码 + 依赖列表（作为指针）。
        """
        with _lock:
            logging.info(f"[KG Manager] 正在保存知识图谱片段...")

            db = cls._load_full_db()

            # 识别根节点 Key，用于过滤
            root_key = _normalize_key(graph.root.name)

            saved_count = 0

            for node_name, code in synthesized_cache.items():
                current_key = _normalize_key(node_name)

                # 1. 绝对不保存根节点
                if current_key == root_key:
                    continue

                # 2. 从 ConceptualGraph 中找回该节点的结构信息（为了获取 deps）
                # 注意：synthesized_cache 的 key 可能是规范化过的，也可能不是，需要尝试匹配
                graph_node = graph.find_node_by_name(node_name)
                if not graph_node:
                    # 尝试用 key 再找一次
                    graph_node = graph.find_node_by_name(current_key)

                if not graph_node:
                    logging.warning(f"  [KG Manager] 警告：无法在图中找到节点 '{node_name}' 的结构信息，跳过保存。")
                    continue

                # 3. 构建依赖指针列表
                # 只记录直接依赖的名称，不需要递归，因为加载时会递归
                dep_pointers = []
                for dep in graph_node.dependencies:
                    dep_pointers.append(_normalize_key(dep.name))

                # 4. 构造条目
                entry = {
                    "original_name": graph_node.name,  # 原始大小写名称
                    "code": code,  # Lean 代码
                    "deps": dep_pointers,  # 邻接表
                    "is_primitive": False  # 未来可扩展：是否为原语
                }

                db[current_key] = entry
                saved_count += 1

            cls._save_full_db(db)
            logging.info(f"[KG Manager] 保存完成。新增/更新了 {saved_count} 个通用节点。")

    @classmethod
    def load_dependency_tree(cls, concept_name: str) -> Dict[str, dict]:
        """
        [加载逻辑]
        给定一个概念名称（如 'RegularHexagon'），递归加载其所有依赖。
        返回一个子字典，包含重建该概念所需的所有节点。
        """
        with _lock:
            db = cls._load_full_db()
            start_key = _normalize_key(concept_name)

            if start_key not in db:
                return {}

            subgraph = {}
            visited = set()
            stack = [start_key]

            logging.info(f"[KG Manager] 正在递归查找 '{concept_name}' 的依赖树...")

            while stack:
                curr = stack.pop()
                if curr in visited:
                    continue
                visited.add(curr)

                if curr in db:
                    entry = db[curr]
                    subgraph[curr] = entry

                    # 将该节点的依赖加入栈中继续查找
                    for dep_key in entry.get("deps", []):
                        if dep_key not in visited:
                            stack.append(dep_key)
                else:
                    # 依赖项缺失（可能是 Mathlib 原语，或者尚未录入的节点）
                    # 可以在这里加日志，但为了不刷屏，暂忽略
                    pass

            logging.info(f"[KG Manager] -> 找到 {len(subgraph)} 个相关节点。")
            return subgraph


# 简单的测试代码
if __name__ == "__main__":
    # 模拟测试
    print("--- Testing KnowledgeGraphManager ---")

    # 1. 手动造一个假数据文件
    dummy_data = {
        "hexagon": {
            "original_name": "Hexagon",
            "code": "def Hexagon...",
            "deps": ["polygon", "point"]
        },
        "polygon": {
            "original_name": "Polygon",
            "code": "def Polygon...",
            "deps": ["point"]
        },
        "point": {
            "original_name": "Point",
            "code": "-- Primitive",
            "deps": []
        }
    }

    # 写入
    KnowledgeGraphManager._save_full_db(dummy_data)

    # 2. 测试递归读取
    result = KnowledgeGraphManager.load_dependency_tree("Hexagon")
    print(f"Result for 'Hexagon': {list(result.keys())}")
    assert "polygon" in result
    assert "point" in result

    print("Test Passed.")