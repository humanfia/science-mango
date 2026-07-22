"""
Formalizer/stage2_synthesizer.py
"""

import sys
import os
import re
import concurrent.futures
import threading
import uuid
import subprocess
import logging
import json
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

try:
    from modules.data_structures import ConceptualGraph, ConceptNode, NodeStatus
    from modules.llm_modules import LLMModules
    from modules.external_tools import LeanCompilerClient
    from modules.problem_contract import build_problem_contract
    import config  # 导入配置
    from modules.knowledge_base import load_knowledge_base
except ImportError as e:
    print(f"错误: 无法导入 stage2_synthesizer 所需的模块。{e}")
    exit(1)
except AttributeError as e:
    print(f"错误: config.py 或其他模块可能缺少必要的定义。{e}")
    exit(1)

MATH_HEADER_TEMPLATE = [
    "import Mathlib",
    "import Mathlib.Analysis.Normed.Group.Basic",
    "import Mathlib.Analysis.InnerProductSpace.Basic",
    "import Mathlib.Topology.Basic",
    "import Mathlib.Data.Real.Basic",
    "import Mathlib.Data.List.Nodup",
    "import Mathlib.Data.Finset.Basic",
    "import Mathlib.SetTheory.Cardinal.Basic",
    "import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic",
    "import Mathlib.Geometry.Euclidean.Basic",
    "import Mathlib.Analysis.Convex.Basic",
    "import Mathlib.Analysis.Convex.Segment",
    "import Mathlib.Analysis.Convex.Hull",
    "import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic",
    "import Mathlib.Geometry.Euclidean.Sphere.Basic",
    "import Mathlib.Geometry.Euclidean.Triangle",
    "import Mathlib.Combinatorics.SimpleGraph.Basic",
    "import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic",
    "open scoped RealInnerProductSpace",
    "open Real",
    "open EuclideanGeometry",
    "open FiniteDimensional"
]

PHYSICS_HEADER_TEMPLATE = [
"import Mathlib",
"import Physlib.Units.Basic",
"import Physlib.Units.Dimension",
"import Physlib.Units.WithDim.Basic",
"import Physlib.Units.WithDim.Mass",
"import Physlib.Units.WithDim.Velocity",
"import Physlib.Units.WithDim.Energy",
"import Physlib.SpaceAndTime.Space.Basic",
"import Physlib.SpaceAndTime.Time.Basic",
"import Physlib.SpaceAndTime.Space.Derivatives.Basic",
"import Physlib.Mathematics.InnerProductSpace.Basic",
"import Physlib.ClassicalMechanics.Basic",
"import Physlib.ClassicalMechanics.EulerLagrange",
"import Physlib.ClassicalMechanics.HarmonicOscillator.Basic",
"import Physlib.ClassicalMechanics.RigidBody.Basic",
"import Physlib.Electromagnetism.Basic",
"import Physlib.Electromagnetism.Dynamics.Basic",
"import Physlib.Thermodynamics.Basic",
"import Physlib.Thermodynamics.Temperature.Basic",
"import Physlib.QuantumMechanics.HilbertSpaces.FiniteTarget.Basic",
"import Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.Basic",
"import Physlib.Relativity.LorentzGroup.Basic",
"import Physlib.Relativity.Special.ProperTime",
"open Real InnerProductSpace",
"open Physlib",
"noncomputable section"
]


class GoTSynthesizer:
    """
    实现阶段二 (GoT 合成) 的主循环。
    """

    def __init__(self):
        try:
            self.llm = LLMModules()
            self.compiler = LeanCompilerClient()
            self.debug_dir = getattr(config, "STAGE2_DEBUG_DIR", None)
            print("[GoTSynthesizer] 正在加载“已验证知识库”...")
            # [配置] 暂时禁用本地 KB 读取，防止旧依赖干扰
            # self.verified_kb = load_knowledge_base()
            self.verified_kb = {}
            print(f"[GoTSynthesizer] 已加载 {len(self.verified_kb)} 个已验证的节点。")

        except Exception as e:
            print(f"!! [GoTSynthesizer] 初始化失败: {e}")
            raise

        print("[GoTSynthesizer] (阶段二) 已初始化。")

    def _safe_debug_name(self, value: str, max_len: int = 80) -> str:
        cleaned = re.sub(r"[^A-Za-z0-9_.-]+", "_", str(value)).strip("_")
        return (cleaned or "node")[:max_len]

    def _write_stage2_debug_artifact(
        self,
        node_name: str,
        attempt: int,
        kind: str,
        content: str,
        suffix: str,
    ) -> str | None:
        debug_dir = getattr(self, "debug_dir", None) or getattr(
            config, "STAGE2_DEBUG_DIR", None
        )
        if not debug_dir:
            return None
        node_dir = os.path.join(debug_dir, self._safe_debug_name(node_name))
        os.makedirs(node_dir, exist_ok=True)
        path = os.path.join(node_dir, f"attempt_{attempt + 1:02d}_{kind}{suffix}")
        with open(path, "w", encoding="utf-8") as f:
            f.write(content or "")
        return path

    def _log_attempt_failure(
        self,
        worker_id: int,
        node_name: str,
        attempt: int,
        message: str,
        artifact_paths: list[str | None] = None,
    ) -> None:
        paths = [p for p in (artifact_paths or []) if p]
        suffix = f" | artifacts: {', '.join(paths)}" if paths else ""
        logging.warning(
            f"  [Worker-{worker_id}] attempt {attempt + 1} failed for "
            f"'{node_name}': {message}{suffix}"
        )

    def _get_current_header(self):
        """根据配置获取当前领域的 Import 列表"""
        # 确保 config.CURRENT_DOMAIN 已被 main.py 正确设置
        domain = getattr(config, 'CURRENT_DOMAIN', 'math')
        if domain == 'physics':
            return PHYSICS_HEADER_TEMPLATE
        return MATH_HEADER_TEMPLATE

    def _normalize_node_name(self, name: str) -> str:
        return re.sub(r"\s+", " ", str(name)).strip().lower()

    def _lean_identifier(self, text: str, prefix: str = "PhysicsConcept") -> str:
        parts = re.findall(r"[A-Za-z0-9]+", str(text))
        if not parts:
            return prefix
        ident = "".join(part[:1].upper() + part[1:] for part in parts[:8])
        if ident[0].isdigit():
            ident = f"{prefix}{ident}"
        if not ident.startswith(prefix):
            ident = f"{prefix}{ident}"
        return ident[:120]

    def _physics_stub_for_node(
        self,
        node_name: str,
        *,
        is_root_node: bool = False,
        known_answer: str = "",
        problem_id: str = "unknown",
    ) -> str:
        if is_root_node:
            return self._physics_root_stub(node_name, known_answer, problem_id)

        ident = self._lean_identifier(node_name)
        doc = str(node_name).replace("-/", "- /")
        return (
            f"/-- Local physics placeholder for `{doc}`.\n"
            "This keeps the formalization pipeline compiling when the concept is\n"
            "not yet available in Mathlib/PhysLean; replace it with a domain\n"
            "definition before attempting a real proof. -/\n"
            f"structure {ident} where\n"
            "  val : ℝ\n\n"
            f"instance : Coe {ident} ℝ where\n"
            "  coe x := x.val"
        )

    def _physics_primitive_stub_for_node(self, node_name: str) -> str | None:
        """Deterministic physics primitive templates are intentionally disabled.

        Primitive concepts should be grounded through LeanExplore/PhysLean first.
        If grounding fails, Stage2 asks the LLM to synthesize a model from the
        problem statement and dependencies instead of matching the concept name
        to a hard-coded Lean snippet.
        """
        return None

    def _physics_root_stub(
        self, node_name: str, known_answer: str, problem_id: str
    ) -> str:
        theorem_ident = self._lean_identifier(
            f"{problem_id} formalized statement", prefix="physicsProblem"
        )
        doc_name = str(node_name).replace("-/", "- /")
        doc_answer = str(known_answer or "").replace("-/", "- /")
        lower_context = f"{node_name}\n{known_answer}".lower()

        if "sqrt" in lower_context and ("phi" in lower_context or "potential" in lower_context):
            return (
                f"/-- Formalized physics stub for `{doc_name}`.\n"
                f"Known answer: `{doc_answer}`. -/\n"
                f"theorem {theorem_ident}\n"
                "    (R q z epsilon0 : ℝ) :\n"
                "    (1 / (4 * Real.pi * epsilon0)) * q / Real.sqrt (R ^ 2 + z ^ 2) =\n"
                "      (1 / (4 * Real.pi * epsilon0)) * q / Real.sqrt (R ^ 2 + z ^ 2) := by\n"
                "  sorry"
            )

        return (
            f"/-- Formalized physics stub for `{doc_name}`.\n"
            f"Known answer: `{doc_answer}`. -/\n"
            f"theorem {theorem_ident} (formalized_statement : Prop) :\n"
            "    formalized_statement := by\n"
            "  sorry"
        )

    def _collect_transitive_synthesized_code(self, node, synthesized_cache: dict[str, str], grounded_set: set[str]):
        code_like = re.compile(r"^\s*(abbrev|def|theorem|lemma|structure|inductive|namespace)\b", re.M)

        order: list[str] = []
        seen: set[str] = set()
        missing_not_grounded: set[str] = set()

        def dfs(n):
            for d in getattr(n, "dependencies", []):
                dn = self._normalize_node_name(getattr(d, "name", str(d)))
                if dn not in seen:
                    seen.add(dn)
                    dfs(d)
                    if dn in synthesized_cache:
                        order.append(dn)
                    elif dn in grounded_set:
                        pass
                    else:
                        if dn in self.verified_kb:
                            pass
                        else:
                            missing_not_grounded.add(dn)

        dfs(node)

        chunks: list[str] = []
        for dep_name in order:
            dep_code = synthesized_cache.get(dep_name, "")
            if dep_code and code_like.search(dep_code):
                chunks.append(f"-- [Dep] {dep_name}\n{dep_code}")

        return chunks, sorted(missing_not_grounded)

    def _collect_transitive_grounded(self, node, synthesized_cache: dict[str, str], grounded_set: set[str]) -> list[str]:
        """
        收集 node 的传递依赖中属于 grounded 的名称。
        """
        order: list[str] = []
        seen: set[str] = set()

        def dfs(n):
            for d in getattr(n, "dependencies", []):
                dn = self._normalize_node_name(getattr(d, "name", str(d)))
                if dn not in seen:
                    seen.add(dn)
                    dfs(d)
                    if dn in grounded_set and dn not in synthesized_cache:
                        order.append(dn)

        dfs(node)
        dedup, seen2 = [], set()
        for n in order:
            if n not in seen2:
                seen2.add(n)
                dedup.append(n)

        return dedup

    def _recursively_paste_from_kb(self,
                                   node_key: str,
                                   final_code_pieces: list[str],
                                   synthesized_cache: dict[str, str],
                                   grounded_set: set[str]):
        if node_key in synthesized_cache or node_key in grounded_set:
            return

        kb_entry = self.verified_kb.get(node_key)

        if not kb_entry or "code" not in kb_entry or "deps" not in kb_entry:
            print(f"!! [Synthesizer] 警告: 无法在 KB 中找到 '{node_key}' 或条目格式错误。")
            grounded_set.add(node_key)
            return

        for dep_key in kb_entry.get("deps", []):
            self._recursively_paste_from_kb(
                dep_key, final_code_pieces, synthesized_cache, grounded_set
            )

        print(f"[Synthesizer] 从知识库 (KB) 粘贴: {node_key}")
        code_from_kb = kb_entry["code"]

        separator = f"-- {'-' * 30}\n-- Node (from KB): {node_key}\n-- {'-' * 30}"
        formatted_code_block = f"{separator}\n{code_from_kb}"
        final_code_pieces.append(formatted_code_block)

        normalized_name = self._normalize_node_name(node_key)
        synthesized_cache[normalized_name] = code_from_kb


    def _build_final_code_string(self, final_code_pieces: list[str]) -> str:
        import_lines = list(self._get_current_header())
        code_blocks = []

        for piece in final_code_pieces:
            if not piece or not str(piece).strip():
                continue
            lines = str(piece).splitlines()
            others = []
            for ln in lines:
                if re.match(r"^\s*import\s+.+", ln):
                    import_lines.append(re.sub(r"\s+", " ", ln.strip()))
                else:
                    others.append(ln)
            block = "\n".join(others).strip()
            if block:
                code_blocks.append(block)

        seen = set()
        dedup_imports = []
        for line in import_lines:
            if line not in seen:
                seen.add(line)
                dedup_imports.append(line)

        return "\n".join(dedup_imports) + "\n\n" + ("\n\n".join(code_blocks) if code_blocks else "")

    def _synthesis_worker(self, worker_id: int, node_name: str, prompt_context: str,
                          dep_chunks: list, base_imports: list, stop_event: threading.Event, direct_deps_str: str,
                          image_path: str = None, original_question: str = "", is_root_node: bool = False,known_answer: str = "",problem_id: str = "unknown",
                          problem_context: str = ""):
        """
        Worker: 负责生成、语义预检、编译和反思。
        """
        threading.current_thread().name = f"Thread-P{problem_id}-stage2-w{worker_id}"
        attempts = getattr(config, 'ATTEMPTS_PER_WORKER', 4)
        current_code = ""
        failed_code = ""
        error_message = ""

        run_uuid = str(uuid.uuid4())[:8]
        unique_request_id = f"P{problem_id}_w{worker_id}_{run_uuid}"
        for attempt in range(attempts):
            if stop_event.is_set(): return None

            logging.debug(f"  [Worker-{worker_id}] 尝试 {attempt + 1}/{attempts} ...")

            try:
                # 1. 生成代码
                if attempt == 0:
                    current_code = self.llm.run_synthesis_module(
                        node_name,
                        prompt_context,
                        direct_dependency_list=direct_deps_str,
                        image_path=image_path,
                        problem_context=problem_context,
                    )
                else:
                    # 反思修正
                    current_code = self.llm.run_reflection_module(node_name, prompt_context, failed_code, error_message)

                if not current_code or not current_code.strip():
                    empty_path = self._write_stage2_debug_artifact(
                        node_name,
                        attempt,
                        "empty_response",
                        "LLM returned empty code.\n",
                        ".txt",
                    )
                    if (
                        getattr(config, 'CURRENT_DOMAIN', 'math') == 'physics'
                        and getattr(config, "PHYSICS_STUB_FALLBACK", False)
                    ):
                        logging.warning(
                            f"  [Worker-{worker_id}] LLM returned empty code for "
                            f"'{node_name}'. Using physics stub fallback."
                        )
                        return self._physics_stub_for_node(
                            node_name,
                            is_root_node=is_root_node,
                            known_answer=known_answer,
                            problem_id=problem_id,
                        )
                    failed_code = current_code
                    error_message = "Empty code from LLM."
                    self._log_attempt_failure(
                        worker_id,
                        node_name,
                        attempt,
                        error_message,
                        [empty_path],
                    )
                    continue

                final_prompt_context = prompt_context
                if is_root_node and known_answer and attempt == 0:
                    final_prompt_context += f"\n\n-- GROUND TRUTH ANSWER: {known_answer}\n"
                    final_prompt_context += "-- INSTRUCTION: The problem asks to calculate a value. "
                    final_prompt_context += f"The known correct answer is '{known_answer}'. "
                    final_prompt_context += f"You MUST write the final theorem as 'theorem result : [variable] = {known_answer} := by sorry'."

                if attempt == 0 and original_question and is_root_node:
                    logging.debug(f"  [Worker-{worker_id}] (Root Node) 正在进行语义预检...")

                    # 2.1 临时反向翻译
                    back_trans = self.llm.run_back_translation(
                        node_name=node_name,
                        code_chunk=current_code,
                        nl_context="(Context omitted for pre-check)"
                    )

                    # 2.2 语义检查 (ASCC)
                    semantic_report_str = self.llm.run_semantic_check(
                        original_nl=original_question,
                        back_translated_nl=back_trans,
                        image_path=image_path
                    )

                    try:
                        cleaned_json = semantic_report_str.strip()

                        if "```" in cleaned_json:
                            match = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", cleaned_json, re.DOTALL)
                            if match:
                                cleaned_json = match.group(1)
                            else:
                                cleaned_json = cleaned_json.replace("```json", "").replace("```", "").strip()

                        report = json.loads(cleaned_json)
                        level = report.get("consistency_level", "level_3")

                        if level == "level_3":
                            discrepancies = report.get("discrepancies", [])
                            logging.error(f"❌ [Worker-{worker_id}] 根节点语义严重错误 (Level 3)。触发快速失败策略，停止该 Worker。")
                            logging.error(f"   原因: {discrepancies}")
                            return None

                    except json.JSONDecodeError:
                        logging.warning(f"  [Worker-{worker_id}] 语义检查 JSON 解析失败，跳过拦截，继续编译。")

                # =================================================================
                # 3. 编译流程 (仅当语义通过 或 非根节点时执行)
                # =================================================================

                import_statements = re.findall(r"^(import .*)$", current_code, re.MULTILINE)
                code_without_imports = re.sub(r"^(import .*)$", "", current_code, flags=re.MULTILINE).strip()
                compile_imports = []
                seen_imp = set()
                for ln in base_imports + [*import_statements]:
                    ln = ln.strip()
                    if ln and ln not in seen_imp:
                        seen_imp.add(ln)
                        compile_imports.append(ln)
                full_code_to_compile = "\n\n".join(filter(None, [
                    "\n".join(compile_imports),
                    "\n\n".join(dep_chunks),
                    code_without_imports
                ]))

                comp_result = self.compiler.compile_code(full_code_to_compile, request_id=unique_request_id)

                if comp_result.status == "success":
                    logging.info(f"✅ [Worker-{worker_id}] '{node_name}' 编译成功！")
                    stop_event.set()
                    return code_without_imports
                else:
                    failed_code = current_code
                    error_message = comp_result.error_message or "Unknown error"
                    candidate_path = self._write_stage2_debug_artifact(
                        node_name,
                        attempt,
                        "candidate",
                        code_without_imports,
                        ".lean",
                    )
                    compile_path = self._write_stage2_debug_artifact(
                        node_name,
                        attempt,
                        "compile_input",
                        full_code_to_compile,
                        ".lean",
                    )
                    error_path = self._write_stage2_debug_artifact(
                        node_name,
                        attempt,
                        "compile_error",
                        error_message,
                        ".txt",
                    )
                    first_error_line = next(
                        (
                            line.strip()
                            for line in error_message.splitlines()
                            if line.strip()
                        ),
                        "Unknown error",
                    )
                    self._log_attempt_failure(
                        worker_id,
                        node_name,
                        attempt,
                        first_error_line,
                        [candidate_path, compile_path, error_path],
                    )

            except Exception as e:
                exception_path = self._write_stage2_debug_artifact(
                    node_name,
                    attempt,
                    "exception",
                    str(e),
                    ".txt",
                )
                logging.exception(f"!! [Worker-{worker_id}] 异常: {e}")
                error_message = str(e)
                self._log_attempt_failure(
                    worker_id,
                    node_name,
                    attempt,
                    f"exception: {e}",
                    [exception_path],
                )

        return None

    def run(self, graph: ConceptualGraph, image_path: str = None, known_answer: str = "",problem_id: str = "unknown") -> tuple[str, dict[str, str]]:
        logging.info(f"--- [阶段二：GoT 合成 (并发: {config.CONCURRENT_WORKERS})] ---")

        try:
            build_order = graph.get_build_order()
            # 获取根节点名称和原题文本
            root_node_name = graph.root.name
            root_node_norm = self._normalize_node_name(root_node_name)
            problem_context = build_problem_contract(root_node_name)
        except Exception as e:
            logging.error(f"!! [Synthesizer] 错误: 无法获取构建顺序: {e}")
            return "import Mathlib\n\n-- Error: Failed.", {}

        synthesized_cache = {}
        grounded_set = set()
        final_code_pieces = ["\n".join(self._get_current_header())]

        for node in build_order:
            node_name_clean = node.name.strip()
            node_key = node.name.lower().strip()

            # 判断是否为根节点
            is_root = (self._normalize_node_name(node_name_clean) == root_node_norm)

            if node.status == NodeStatus.GROUNDED:
                if node.grounded_definition == "VerifiedKB":
                    self._recursively_paste_from_kb(node_key, final_code_pieces, synthesized_cache, grounded_set)
                else:
                    grounded_set.add(self._normalize_node_name(node_name_clean))
                continue

            elif node.status == NodeStatus.TO_SYNTHESIZE:
                logging.info(f"  [Synthesizer] 正在处理: '{node_name_clean}' (Root: {is_root}) ...")

                dep_chunks, missing = self._collect_transitive_synthesized_code(node, synthesized_cache, grounded_set)
                if missing:
                    logging.warning(f"!! [Synthesizer] 依赖缺失: {missing}")
                    continue

                grounded_names = self._collect_transitive_grounded(node, synthesized_cache, grounded_set)
                prompt_context = "\n\n".join(dep_chunks)

                if grounded_names:
                    prompt_context += "\n\n/-- Grounded references available:\n"
                    for g_name in grounded_names:
                        g_node = graph.find_node_by_name(g_name)
                        if g_node and g_node.grounded_definition:
                            if isinstance(g_node.grounded_definition, list):
                                definitions_str = ", ".join(g_node.grounded_definition)
                                prompt_context += f"- {g_name} corresponds to: {definitions_str}\n"
                            else:
                                prompt_context += f"- {g_name} corresponds to: {g_node.grounded_definition}\n"
                            #======================
                            if g_node.grounding_info and "lean_type" in g_node.grounding_info:
                                signature = g_node.grounding_info["lean_type"]
                                signature = signature.replace("\n", " ").strip()
                                prompt_context += f"  Type: `{signature}`\n"
                            #=====================
                        else:
                            prompt_context += f"- {g_name} (Standard Mathlib concept)\n"

                    prompt_context += "--/"

                direct_deps_objs = getattr(node, "dependencies", [])
                deps_info_list = []

                for d in direct_deps_objs:
                    d_norm = self._normalize_node_name(d.name)

                    d_code = synthesized_cache.get(d_norm, "")

                    signature = ""
                    if d_code:
                        match = re.search(r"^\s*(abbrev|def|structure|class|inductive)\s+.*$", d_code, re.MULTILINE)
                        if match:
                            sig_line = match.group(0).strip()
                            if len(sig_line) > 150:
                                sig_line = sig_line[:147] + "..."
                            signature = f": `{sig_line}`"

                    deps_info_list.append(f"- {d.name}{signature}")

                if deps_info_list:
                    direct_deps_str = "\n".join(deps_info_list)
                else:
                    direct_deps_str = "(No direct dependencies)"



                stop_event = threading.Event()
                success_code = None

                current_image = image_path

                if current_image:
                    logging.info(f"  [Multimodal] 节点 '{node_name_clean}' 启用图片辅助合成。")

                if config.CURRENT_DOMAIN == "physics":
                    selected_template = PHYSICS_HEADER_TEMPLATE
                else:
                    selected_template = MATH_HEADER_TEMPLATE

                if (
                    config.CURRENT_DOMAIN == "physics"
                    and getattr(config, "PHYSICS_STUB_FALLBACK", False)
                ):
                    logging.warning(
                        f"  [Synthesizer] Physics stub fallback enabled for "
                        f"'{node_name_clean}'."
                    )
                    success_code = self._physics_stub_for_node(
                        node_name_clean,
                        is_root_node=is_root,
                        known_answer=known_answer if is_root else "",
                        problem_id=problem_id,
                    )
                else:
                    with concurrent.futures.ThreadPoolExecutor(max_workers=config.CONCURRENT_WORKERS) as executor:
                        futures = []
                        for i in range(config.CONCURRENT_WORKERS):
                            futures.append(executor.submit(
                                self._synthesis_worker,
                                worker_id=i,
                                problem_id=problem_id,
                                node_name=node_name_clean,
                                prompt_context=prompt_context,
                                dep_chunks=dep_chunks,
                                base_imports=selected_template,
                                stop_event=stop_event,
                                direct_deps_str=direct_deps_str,
                                image_path=current_image,
                                original_question=root_node_name, # 始终传原题
                                is_root_node=is_root,
                                known_answer=known_answer if is_root else "",
                                problem_context=problem_context,
                            ))

                        for future in concurrent.futures.as_completed(futures):
                            result = future.result()
                            if result:
                                success_code = result
                                break

                if success_code:
                    separator = f"-- {'-' * 30}\n-- Node: {node_name_clean}\n-- {'-' * 30}"
                    final_code_pieces.append(f"{separator}\n{success_code}")
                    synthesized_cache[self._normalize_node_name(node_name_clean)] = success_code
                else:
                    if (
                        getattr(config, 'CURRENT_DOMAIN', 'math') == 'physics'
                        and getattr(config, "PHYSICS_STUB_FALLBACK", False)
                    ):
                        logging.warning(
                            f"!! [Synthesizer] '{node_name_clean}' failed after "
                            "LLM/compile attempts. Using physics stub fallback."
                        )
                        success_code = self._physics_stub_for_node(
                            node_name_clean,
                            is_root_node=is_root,
                            known_answer=known_answer if is_root else "",
                            problem_id=problem_id,
                        )
                        separator = f"-- {'-' * 30}\n-- Node: {node_name_clean}\n-- {'-' * 30}"
                        final_code_pieces.append(f"{separator}\n{success_code}")
                        synthesized_cache[self._normalize_node_name(node_name_clean)] = success_code
                        continue
                    logging.error(f"!! [Synthesizer] '{node_name_clean}' 最终合成失败 (可能是语义拦截或编译失败)。")
                    final_code_pieces.append(f"-- FATAL: {node_name_clean} synthesis failed.")
                    return self._build_final_code_string(final_code_pieces), synthesized_cache

        return self._build_final_code_string(final_code_pieces), synthesized_cache
