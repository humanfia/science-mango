"""
Formalizer/modules/knowledge_base.py

管理一个持久化的 JSON 知识库，用于存储已验证的 Lean 代码片段。
V9 Hotfix：
- 修复了 save_verified_nodes -> load_knowledge_base 造成的重入锁死锁。
"""
import json
import os
import threading

# 导入配置和数据结构
try:
    import config
    # 我们需要 ConceptualGraph 来查找节点和依赖项
    from modules.data_structures import ConceptualGraph
except ImportError:
    print("错误：config.py 或 data_structures.py 未找到。")
    exit(1)

# 定义知识库文件的路径
KB_FILE_PATH = os.path.join(config.FORMALIZER_DIR, "verified_knowledge_base.json")

_lock = threading.RLock()

def save_verified_nodes(synthesized_cache: dict[str, str],
                        graph: ConceptualGraph):
    """
    将新验证通过的节点（代码块）合并到 JSON 知识库中。

    过滤逻辑:
    1. 跳过“根节点”(一次性产物)。
    2. 保存所有其他（非根）节点及其依赖项列表。
    """
    with _lock:
        print(f"\n[KnowledgeBase] 正在过滤并保存 {len(synthesized_cache)} 个已验证节点...", flush=True)

        existing_kb = load_knowledge_base()
        root_key = graph.root.name.lower().strip()

        new_items_count = 0
        updated_items_count = 0
        root_skipped = 0

        for node_key, code_chunk in synthesized_cache.items():

            # 1. 过滤根节点
            if node_key == root_key:
                root_skipped += 1
                continue


            # 2. 查找该节点的依赖项
            original_node = graph.find_node_by_name(node_key)
            if not original_node:
                print(f"!! [KnowledgeBase] 警告: 无法在图中找到节点 '{node_key}'，跳过保存。", flush=True)
                continue

            dep_keys = []
            for dep_node in original_node.dependencies:
                dep_keys.append(dep_node.name.lower().strip())

            # 3. 准备要保存的新条目
            kb_entry = {
                "code": code_chunk,
                "deps": dep_keys
            }

            if node_key not in existing_kb:
                new_items_count += 1
            else:
                updated_items_count += 1

            existing_kb[node_key] = kb_entry

        # 4. 写回文件
        try:
            with open(KB_FILE_PATH, "w", encoding="utf-8") as f:
                json.dump(existing_kb, f, indent=2, ensure_ascii=False)
            print(f"[KnowledgeBase] 保存成功。", flush=True)
            print(f"  > 跳过 {root_skipped} 个 (根节点)。", flush=True)
            print(f"  > 新增 {new_items_count} 个, 更新 {updated_items_count} 个 (非根节点)。", flush=True)
            print(f"  > 知识库总计 {len(existing_kb)} 个节点。", flush=True)
        except IOError as e:
            print(f"!! [KnowledgeBase] 写入 JSON 文件失败: {e}", flush=True)

def load_knowledge_base() -> dict[str, any]:
    """
    加载完整的 JSON 知识库。
    返回: dict[str, dict]  (例如: {"rhombus": {"code": "...", "deps": [...]}})
    """
    with _lock:
        if not os.path.exists(KB_FILE_PATH):
            return {}

        try:
            with open(KB_FILE_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
            if not isinstance(data, dict):
                print(f"!! [KnowledgeBase] 知识库文件格式错误 (不是字典)，将返回空库。", flush=True)
                return {}
            # 确保所有条目都是字典（防止旧格式冲突）
            valid_data = {k: v for k, v in data.items() if isinstance(v, dict)}
            if len(valid_data) != len(data):
                print(f"!! [KnowledgeBase] 警告: 知识库中检测到格式无效的条目，已过滤。", flush=True)
            return valid_data
        except json.JSONDecodeError as e:
            print(f"!! [KnowledgeBase] 解析 JSON 文件失败: {e}，将返回空库。", flush=True)
            return {}
        except IOError as e:
            print(f"!! [KnowledgeBase] 读取 JSON 文件失败: {e}，将返回空库。", flush=True)
            return {}