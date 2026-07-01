"""
Formalizer/modules/llm_modules.py

封装所有 LLM 调用的逻辑。
- 从 config.py 加载配置
- 从 prompts/ 加载模板
- (真实) 调用 LLM API
- 包含清理 LLM 代码输出的逻辑
"""

import time
import ast # 用于安全地解析 LLM 返回的列表字符串
import re  # 用于清理代码块
from dataclasses import dataclass
import json
import os
import traceback
import logging
import base64
import mimetypes

# 导入配置
try:
    import config
except ImportError:
    print("错误：config.py 未找到。请确保它在 Formalizer/ 目录中。")
    exit(1)

try:
    from openai import OpenAI, APIConnectionError, RateLimitError, APIError, APIStatusError
    # 检查 API 密钥是否存在且非默认值
    if not config.LLM_API_KEY or config.LLM_API_KEY == "YOUR_API_KEY_HERE":
         print("!! 警告: LLM_API_KEY 未在 config.py 中正确设置。")
except ImportError:
    print("错误: 'openai' 库未安装。") #
    print("请运行 'pip install openai' 来安装它。")
    exit(1)
except Exception as e:
    print(f"!! [LLMModules] 初始化 OpenAI 客户端时出错: {e}")
    exit(1)


def _create_openai_client():
    """按当前 config 动态创建客户端，避免在模块导入时固化旧配置。"""
    print(f"[LLMModules] 正在初始化 真实 OpenAI 客户端...")
    print(f"[LLMModules] Base URL: {config.LLM_BASE_URL}")
    return OpenAI(
        api_key=config.LLM_API_KEY,
        base_url=config.LLM_BASE_URL,
        timeout=getattr(config, "LLM_TIMEOUT", 120),
    )


@dataclass
class GroundingResult:
    """封装接地推理器的输出""" #
    is_found: bool
    definitions: list[str] = None


@dataclass
class ExpansionDecision:
    """Structured result for deciding whether a concept should keep decomposing."""

    decision: str
    dependencies: list[str]
    reason: str = ""
    raw_response: str = ""

    @property
    def should_expand(self) -> bool:
        return self.decision == "EXPAND" and bool(self.dependencies)

    @property
    def is_atomic_stop(self) -> bool:
        return self.decision == "STOP_ATOMIC"

    @property
    def failed(self) -> bool:
        return self.decision == "FAILED_OR_UNKNOWN"


def _clean_llm_code_output(response: str, mode: str = "lean") -> str:
    """
    通用清洗函数。
    【重要】为了兼容旧代码逻辑，无论何种模式，此函数始终返回字符串 (str)。

    :return:
        - mode="lean": 清洗后的代码文本
        - mode="list": 列表的字符串表示，如 "['A', 'B']"
        - mode="json": JSON 字符串，如 "{...}"
    """
    if not response:
        if mode == "list": return "['NO_MATCH']"  # 返回列表字符串
        if mode == "json": return "{}"
        return ""

    cleaned = response.strip()

    # ==========================================================
    # 模式 A: List 清洗 (目标：返回 "['Item1', 'Item2']")
    # ==========================================================
    if mode == "list":
        upper_cleaned = cleaned.upper()

        # 1. 【入口拦截】拒绝词
        if "NO_MATCH" in upper_cleaned:
            return "['NO_MATCH']"
        if cleaned.lower() in ["none", "null", "no dependency", "no dependencies"]:
            return "['NO_MATCH']"

        final_item = None

        # 2. 【关键修复】优先提取 Markdown 代码块
        # 这能直接过滤掉外部的 [Extracted Context]: ... 废话
        # 只要找到了 ```...```，我们就只在里面找列表
        search_source = cleaned
        match_code = re.search(r"```(?:python|json)?\s*([\s\S]*?)\s*```", cleaned, re.DOTALL)
        if match_code:
            search_source = match_code.group(1).strip()

        # 3. 在锁定范围内寻找 [...]
        # 使用 candidates 列表尝试不同的提取策略
        candidates = []

        # 策略 A: 也就是 search_source 本身 (如果已经是干净的列表字符串)
        candidates.append(search_source)

        # 策略 B: 正则提取 [...]
        # (解决 search_source 里还有一些 print("...") 或其他杂音的情况)
        match_brackets = re.search(r"(\[.*\])", search_source, re.DOTALL)
        if match_brackets:
            candidates.append(match_brackets.group(1))

        # 尝试解析
        for text in candidates:
            try:
                res = ast.literal_eval(text)
                if isinstance(res, list):
                    # 找到了！且是一个列表
                    if len(res) > 0:
                        # 如果是多项列表，直接返回字符串
                        return str([str(x).strip() for x in res])
                    else:
                        # 这是一个空列表 []
                        return "[]"
            except:
                pass

            # 尝试 JSON 解析
            try:
                res = json.loads(text)
                if isinstance(res, list):
                    return str([str(x).strip() for x in res])
            except:
                pass

        # 4. 【兜底逻辑】(如果上面解析失败，处理单行/多行文本)
        # 只有当 search_source 确实找不到括号列表时才进这里

        # 4.1 单结果提取 (针对 xxx.xxx.xx)
        # 如果 search_source 很干净（没有换行，长度适中），直接当做单结果
        if "\n" not in search_source and len(search_source) < 100:
            # 清理行首可能的修饰符
            clean_single = re.sub(r"^[\d\-\*\.]+\s+", "", search_source).strip()
            if clean_single and "no " not in clean_single.lower():
                return str([clean_single])

        # 4.2 多行提取
        lines = search_source.split('\n')
        extracted = []
        for line in lines:
            line = line.strip()
            if not line: continue
            if line.lower().startswith(("here", "sure", "output", "extracted")): continue  # 过滤常见废话头

            clean_line = re.sub(r"^[\d\-\*\.]+\s+", "", line).strip()
            if clean_line.startswith('`') and clean_line.endswith('`'):
                clean_line = clean_line[1:-1]

            if clean_line and len(clean_line) < 80:
                extracted.append(clean_line)

        if extracted:
            return str(extracted)

        # 5. 实在没办法了，返回 NO_MATCH
        return "['NO_MATCH']"

    # ==========================================================
    # 模式 B: JSON 清洗 (目标：返回 "{...}")
    # ==========================================================
    elif mode == "json":
        # 只提取最外层的 {...}
        match = re.search(r"(\{.*\})", cleaned, re.DOTALL)
        if match:
            return match.group(1)  # 返回找到的 JSON 字符串

        # 如果找不到 {}，尝试原样返回（或者返回空字典字符串）
        # 这里原样返回，让下游的 json.loads 去报错或尝试解析
        return cleaned

    # ==========================================================
    # 模式 C: Lean 代码清洗 (返回 str)
    # ==========================================================
    else:  # mode == "lean"
        # 1. 提取 Markdown
        match_lean = re.search(r"```lean\s*([\s\S]*?)\s*```", cleaned, re.DOTALL)
        if match_lean:
            cleaned = match_lean.group(1).strip()
        else:
            match_python = re.search(r"```python\s*([\s\S]*?)\s*```", cleaned, re.DOTALL)
            if match_python:
                cleaned = match_python.group(1).strip()
            else:
                match_plain = re.search(r"```\s*([\s\S]*?)\s*```", cleaned, re.DOTALL)
                if match_plain:
                    cleaned = match_plain.group(1).strip()
                    if cleaned.startswith("python"): cleaned = cleaned[6:].strip()

        if cleaned.startswith('`') and cleaned.endswith('`'):
            cleaned = cleaned[1:-1]

        # 2. 截断逻辑 (应用之前讨论的 startswith 修复)
        stop_markers = ["-- [Dep]", "--[Dep]", "import Mathlib"]
        lines = cleaned.split('\n')
        valid_lines = []

        # 定义必须严格匹配的标记 (去除首尾空格后必须完全相等)
        # 这些通常是 Prompt 里用于分隔上下文的“栏杆”
        strict_stop_markers = [
            "-- [Dep]",
            "--[Dep]",
            "-- Dependency Context",
            "-- End of Dependency"
        ]

        for i, line in enumerate(lines):
            line_stripped = line.strip()
            should_cut = False


            if not should_cut:
                if line_stripped in strict_stop_markers:
                    logging.debug(f"  [Cleaner] 检测到分隔标记，截断: '{line_stripped}'")
                    should_cut = True

            if should_cut:
                break

            valid_lines.append(line)

        return "\n".join(valid_lines).strip()


_IMAGE_MAX_BYTES = 50 * 1024  # 50 KB，超过则压缩后再编码

def _encode_image(image_path: str) -> str:
    """读取图片，若超过 50KB 则自动缩放压缩，再转为 base64。"""
    if not image_path or not os.path.exists(image_path):
        return None
    try:
        raw = open(image_path, "rb").read()
        if len(raw) <= _IMAGE_MAX_BYTES:
            return base64.b64encode(raw).decode("utf-8")
        # 需要压缩：用 Pillow 缩放到宽度 ≤ 800px，再以 JPEG 质量 75 输出
        from PIL import Image as _PILImage
        import io as _io
        img = _PILImage.open(_io.BytesIO(raw)).convert("RGB")
        max_w = 800
        if img.width > max_w:
            ratio = max_w / img.width
            img = img.resize((max_w, int(img.height * ratio)), _PILImage.LANCZOS)
        buf = _io.BytesIO()
        quality = 75
        while quality >= 30:
            buf.seek(0); buf.truncate()
            img.save(buf, format="JPEG", quality=quality)
            if buf.tell() <= _IMAGE_MAX_BYTES:
                break
            quality -= 15
        logging.info(f"[ImageEncoder] 压缩 {os.path.basename(image_path)}: "
                     f"{len(raw)//1024}KB → {buf.tell()//1024}KB (quality={quality})")
        return base64.b64encode(buf.getvalue()).decode("utf-8")
    except Exception as e:
        logging.error(f"!! 无法读取图片 {image_path}: {e}")
        return None

class LLMModules:
    """
    封装所有 LLM 调用
    """
    def __init__(self):
        print(f"[LLMModules] 初始化...")
        print(f"[LLMModules] 模型: {config.LLM_MODEL_NAME}")
        self.client = _create_openai_client()

        # 1. 在初始化时加载所有 Prompt 模板
        try:
            self.grounding_prompt_template = self._smart_load(config.GROUNDING_PROMPT_FILE)
            self.expansion_prompt_template = self._smart_load(config.EXPANSION_PROMPT_FILE)
            self.synthesis_prompt_template = self._smart_load(config.SYNTHESIS_PROMPT_FILE)
            self.reflection_prompt_template = self._smart_load(config.REFLECTION_PROMPT_FILE)
            self.back_translation_prompt_template = self._smart_load(config.BACK_TRANSLATION_PROMPT_FILE)
            self.merge_back_translations_prompt_template = self._smart_load(config.MERGE_BACK_TRANSLATIONS_PROMPT_FILE)
            self.semantic_check_prompt_template = self._smart_load(config.SEMANTIC_CHECK_PROMPT_FILE)
            self.multimodal_synthesis_prompt_template = self._smart_load(config.MULTIMODAL_SYNTHESIS_PROMPT_FILE)

            print("[LLMModules] 所有 Prompt 模板加载成功。")
        except FileNotFoundError as e:
            print(f"错误: Prompt 文件未找到。{e}") #
            print(f"请确保 prompts/ 目录和 .txt 文件存在于 {config.FORMALIZER_DIR} 中。")
            exit(1)
        except AttributeError as e:
             print(f"错误: config.py 可能缺少 Prompt 文件路径定义。{e}")
             exit(1)

    def _smart_load(self, default_path: str) -> str:
        """
        智能加载函数：
        1. 检查 config.CURRENT_DOMAIN 是否为 physics
        2. 如果是，尝试寻找同名的 _physics.txt 文件
        3. 如果找到物理版，优先加载；否则回退加载 default_path
        """
        if not default_path: return ""

        final_path = default_path

        # 如果是物理模式，尝试构造物理版路径
        if config.CURRENT_DOMAIN == "physics":
            base, ext = os.path.splitext(default_path)
            physics_path = f"{base}_physics{ext}"

            if os.path.exists(physics_path):
                logging.info(f"  ✨ 命中物理 Prompt: {os.path.basename(physics_path)}")
                final_path = physics_path
            else:
                 logging.debug(f"  ⚠️ 未找到物理版 {os.path.basename(physics_path)}，回退到默认版。")

        try:
            with open(final_path, 'r', encoding='utf-8') as f:
                return f.read()
        except FileNotFoundError:
            print(f"!! 错误: 找不到 Prompt 文件: {final_path}")
            return ""
        except Exception as e:
            print(f"!! 读取 Prompt 出错: {e}")
            return ""


    def _call_llm_api(self, prompt: str, temperature: float = None, image_path: str = None) -> str:
        if temperature is None:
            temperature = getattr(config, 'LLM_TEMPERATURE_STRICT', 0.1)

        use_image = (image_path is not None)
        user_content = []
        user_content.append({"type": "text", "text": prompt})

        # 图片处理逻辑
        if use_image:
            base64_image = _encode_image(image_path)
            if base64_image:
                mime_type, _ = mimetypes.guess_type(image_path)
                if not mime_type: mime_type = "image/png"
                user_content.append({
                    "type": "image_url",
                    "image_url": {"url": f"data:{mime_type};base64,{base64_image}"}
                })

        # ================== 日志打印修复 ==================
        if use_image:
            # 多模态日志
            try:
                import json
                import copy
                log_payload = copy.deepcopy(user_content)
                for item in log_payload:
                    if item.get("type") == "image_url":
                        url = item["image_url"]["url"]
                        if "base64," in url:
                            header, data = url.split("base64,")
                            item["image_url"]["url"] = f"{header}base64,{data[:20]}...[TRUNCATED]"
                logging.debug(f"--- [LLM Request Payload (Multimodal)] ---\n{json.dumps(log_payload, ensure_ascii=False, indent=2)}")
            except: pass
        else:
            # 纯文本日志 (Grounding 走这里)
            logging.debug(f"--- [LLM Request Payload (Text)] ---\n{prompt}")
        # ==================================================

        final_content = user_content if use_image else prompt

        # 构建 API 参数
        api_kwargs = dict(
            messages=[
                {"role": "system", "content": "You are an AI assistant expert in Lean 4 and Mathlib."},
                {"role": "user", "content": final_content}
            ],
            model=config.LLM_MODEL_NAME,
        )
        # 官方推理模型 (o1/o3/gpt-5) 不支持 temperature
        if getattr(config, 'SUPPORTS_TEMPERATURE', True):
            api_kwargs["temperature"] = temperature

        max_retries = max(0, int(getattr(config, "LLM_MAX_RETRIES", 3)))
        retry_delay = max(0.0, float(getattr(config, "LLM_RETRY_DELAY", 2)))
        total_attempts = max_retries + 1

        for attempt in range(total_attempts):
            try:
                chat_completion = self.client.chat.completions.create(**api_kwargs)
                response = chat_completion.choices[0].message.content
                return response.strip() if response else ""
            except Exception as e:
                logging.error(
                    f"!! LLM API Error (attempt {attempt + 1}/{total_attempts}): {e}"
                )
                if attempt >= max_retries:
                    return ""
                if retry_delay > 0:
                    time.sleep(retry_delay * (2 ** attempt))

        return ""

    def run_multimodal_synthesis(self, original_text: str, image_path: str) -> str:
        """
        多模态预处理：将图片信息（标号、几何关系）融合进文本题目。
        """
        if not image_path:
            return original_text

        prompt = self.multimodal_synthesis_prompt_template.format(
            question=original_text
        )

        logging.debug(f"  [Multimodal Synthesis] 正在融合图片信息...")

        # 调用 LLM (带图片)
        response = self._call_llm_api(prompt, image_path=image_path)

        # 简单清理：有时候模型会罗嗦，我们尽量只取正文
        cleaned = response.strip()

        # 如果模型返回了被引号包围的内容，去掉引号
        if cleaned.startswith('"') and cleaned.endswith('"'):
            cleaned = cleaned[1:-1]

        return cleaned

    def run_grounding_reasoner(self, concept_name: str, candidates: list, image_path: str = None) -> GroundingResult:
        """
        [修改版] 使用结构化 Block 格式展示候选项，包含 Type 和 Desc。
        """
        # [优化] 只取前 15 个，防止爆 Token
        top_candidates = candidates[:15]

        candidates_formatted = []
        for i, c in enumerate(top_candidates):
            # 使用 ### 分隔符，增强视觉区分
            item_str = f"### [{i + 1}] Candidate: {c.full_lean_name}\n"

            # [新增] 显式展示 Type Signature
            if c.lean_type:
                # 截断过长的签名
                clean_type = c.lean_type[:300] + "..." if len(c.lean_type) > 300 else c.lean_type
                item_str += f"   Type: `{clean_type}`\n"

            # 展示描述
            desc = c.informal_description or '(No description)'
            if len(desc) > 200:
                desc = desc[:197] + "..."
            item_str += f"   Desc: {desc}"

            candidates_formatted.append(item_str)

        # 用换行符分隔各个 Block
        candidates_text = "\n\n".join(candidates_formatted)

        if not candidates_text:
            candidates_text = "(No search results found)"

        prompt = self.grounding_prompt_template.format(
            concept_name=concept_name,
            candidates_text=candidates_text
        )

        response = self._call_llm_api(prompt, image_path=image_path)
        cleaned_response = _clean_llm_code_output(response,mode="list")
        allowed_names = {c.full_lean_name for c in top_candidates if c.full_lean_name}

        def _pick_allowed_name(value: str) -> str | None:
            value = (value or "").strip().strip("`")
            if value in allowed_names:
                return value
            for name in allowed_names:
                if name in value:
                    return name
            return None

        if "NO_MATCH" in cleaned_response:
            return GroundingResult(is_found=False, definitions=[])

        try:
            content_to_parse = cleaned_response.replace("FOUND:", "").strip()

            if (content_to_parse.startswith("'") and content_to_parse.endswith("'")) or \
                    (content_to_parse.startswith('"') and content_to_parse.endswith('"')):
                content_to_parse = content_to_parse[1:-1]

            if content_to_parse.startswith("[") and content_to_parse.endswith("]"):
                parsed = ast.literal_eval(content_to_parse)
                if isinstance(parsed, list) and len(parsed) > 0:
                    # 强制只取第一个候选 Lean 名称，避免把解释文本写入 grounding。
                    for item in parsed:
                        matched = _pick_allowed_name(str(item))
                        if matched:
                            return GroundingResult(is_found=True, definitions=[matched])
                    return GroundingResult(is_found=False, definitions=[])

            final_name = content_to_parse.strip()
            matched = _pick_allowed_name(final_name)
            if matched:
                return GroundingResult(is_found=True, definitions=[matched])

        except Exception as e:
            logging.warning(f"  [LLM Reasoner] 解析错误: {e}")
            pass

        if "," in cleaned_response:
            first_def = cleaned_response.split(',')[0].strip()
            matched = _pick_allowed_name(first_def)
            if matched:
                return GroundingResult(is_found=True, definitions=[matched])

        if " " not in cleaned_response and len(cleaned_response) > 0:
            matched = _pick_allowed_name(cleaned_response)
            if matched:
                return GroundingResult(is_found=True, definitions=[matched])

        logging.warning(f"  [LLM Reasoner] 警告: 无法解析响应: '{cleaned_response}'")
        return GroundingResult(is_found=False, definitions=[])

    def _normalize_dependency_list(self, value) -> list[str]:
        if not isinstance(value, list):
            return []
        return [
            str(item).strip()
            for item in value
            if str(item).strip() and str(item).strip().upper() != "NO_MATCH"
        ]

    def _extract_json_object(self, response: str) -> dict | None:
        text = (response or "").strip()
        if not text:
            return None

        match = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", text, re.DOTALL)
        if match:
            text = match.group(1)
        elif "{" in text and "}" in text:
            text = text[text.find("{"): text.rfind("}") + 1]

        if not text.startswith("{"):
            return None

        try:
            parsed = json.loads(text)
            return parsed if isinstance(parsed, dict) else None
        except json.JSONDecodeError:
            return None

    def _parse_expansion_decision_response(
        self, response: str, concept_name: str
    ) -> ExpansionDecision:
        raw_response = response or ""
        if not raw_response.strip():
            return ExpansionDecision(
                decision="FAILED_OR_UNKNOWN",
                dependencies=[],
                reason="empty LLM response",
                raw_response=raw_response,
            )

        json_obj = self._extract_json_object(raw_response)
        if json_obj is not None:
            decision = str(json_obj.get("decision", "")).strip().upper()
            dependencies = self._normalize_dependency_list(
                json_obj.get("dependencies", [])
            )
            reason = str(json_obj.get("reason", "")).strip()

            if decision in {"STOP", "STOP_ATOMIC", "ATOMIC"}:
                return ExpansionDecision("STOP_ATOMIC", [], reason, raw_response)
            if decision == "EXPAND" and dependencies:
                return ExpansionDecision("EXPAND", dependencies, reason, raw_response)
            if decision in {"FAILED", "UNKNOWN", "FAILED_OR_UNKNOWN"}:
                return ExpansionDecision(
                    "FAILED_OR_UNKNOWN", [], reason or "model marked expansion unknown", raw_response
                )
            if dependencies:
                return ExpansionDecision("EXPAND", dependencies, reason, raw_response)
            return ExpansionDecision(
                "FAILED_OR_UNKNOWN",
                [],
                reason or "JSON expansion decision had no usable dependencies",
                raw_response,
            )

        cleaned_response = _clean_llm_code_output(raw_response, mode="list")
        if "NO_MATCH" in cleaned_response.upper():
            return ExpansionDecision(
                "FAILED_OR_UNKNOWN",
                [],
                "LLM did not return an expansion decision",
                raw_response,
            )

        try:
            parsed = ast.literal_eval(cleaned_response)
            if isinstance(parsed, list):
                dependencies = self._normalize_dependency_list(parsed)
                if dependencies:
                    return ExpansionDecision(
                        "EXPAND",
                        dependencies,
                        "legacy list expansion",
                        raw_response,
                    )
                return ExpansionDecision(
                    "STOP_ATOMIC",
                    [],
                    "legacy empty list atomic stop",
                    raw_response,
                )
        except (ValueError, SyntaxError) as e:
            logging.warning(f"!! LLM Expander 警告: 无法解析响应。错误: {e}")

        return ExpansionDecision(
            "FAILED_OR_UNKNOWN",
            [],
            f"could not parse expansion response for {concept_name}",
            raw_response,
        )

    def run_expansion_decision(
        self,
        concept_name: str,
        image_path: str = None,
        problem_context: str = "",
    ) -> ExpansionDecision:
        """
        LLM 扮演“分解器”角色，并显式返回继续/停止/失败判断。
        """
        prompt = self.expansion_prompt_template.format(
            concept_name=concept_name,
            problem_context=problem_context
            or "No explicit problem-level contract was provided.",
        )

        response = self._call_llm_api(prompt, image_path=image_path)
        return self._parse_expansion_decision_response(response, concept_name)

    def run_expansion_module(
        self,
        concept_name: str,
        image_path: str = None,
        problem_context: str = "",
    ) -> list[str]:
        """
        Backward-compatible list-only expansion API.
        """
        return self.run_expansion_decision(
            concept_name, image_path=image_path, problem_context=problem_context
        ).dependencies

    def run_synthesis_module(
        self,
        target_name: str,
        dependency_context: str,
        image_path: str = None,
        direct_dependency_list="",
        problem_context: str = "",
    ) -> str:
        prompt = self.synthesis_prompt_template.format(
            dependency_context=dependency_context,
            target_name=target_name,
            direct_dependency_list=direct_dependency_list,
            problem_context=problem_context
            or "No explicit problem-level contract was provided.",
        )
        logging.debug(f"  [Synthesizer] 生成 '{target_name}'...")

        creative_temp = getattr(config, 'LLM_TEMPERATURE_CREATIVE', 0.1)

        response = self._call_llm_api(prompt, temperature=creative_temp, image_path=image_path)

        return _clean_llm_code_output(response,mode="lean")

    def run_reflection_module(self, target_name: str, dependency_context: str, failed_code: str,
                              error_message: str) -> str:
        """
        LLM 扮演“代码修正器”角色。
        """
        cleaned_error = error_message.split("error:", 1)[-1].strip()
        max_error_len = 500
        if len(cleaned_error) > max_error_len:
            cleaned_error = cleaned_error[:max_error_len] + "\n... (错误信息过长已截断)"

        prompt = self.reflection_prompt_template.format(
            dependency_context=dependency_context,
            target_name=target_name,
            failed_code=failed_code,
            error_message=cleaned_error
        )

        logging.debug(f"  [LLM Reflector] 正在运行 Prompt (修正 '{target_name}')...")

        response = self._call_llm_api(prompt)
        cleaned_response = _clean_llm_code_output(response,mode="lean")

        return cleaned_response

    def run_back_translation(self, node_name: str, code_chunk: str, nl_context: str) -> str:
        if not nl_context:
            nl_context = "(无依赖项)"

        prompt = self.back_translation_prompt_template.format(
            node_name=node_name,
            code_chunk=code_chunk,
            nl_context=nl_context
        )
        response = self._call_llm_api(prompt)
        return response.strip()

    def run_merge_back_translations(self, segments: dict[str, str]) -> str:
        segments_text = "\n".join(
            f"--- 片段: {name} ---\n{description}\n"
            for name, description in segments.items()
        )

        prompt = self.merge_back_translations_prompt_template.format(
            segments_text=segments_text
        )
        response = self._call_llm_api(prompt)
        return response.strip()

    def run_semantic_check(self, original_nl: str, back_translated_nl: str, image_path: str = None) -> str:

        prompt = self.semantic_check_prompt_template.format(
            original_problem=original_nl,
            back_translated_problem=back_translated_nl
        )

        response = self._call_llm_api(prompt, image_path=image_path)

        cleaned_response = _clean_llm_code_output(response,mode="json")

        if not cleaned_response.startswith("{") or not cleaned_response.endswith("}"):
            logging.warning(f"!! [LLM ASCC] 警告: 响应不是 JSON。")
            logging.debug(f"   原始响应: {cleaned_response}")
            return """
            {
                "consistency_level": "level_3",
                "discrepancies": ["ASCC 模块返回了无效的 JSON 对象。"],
                "recommendations": []
            }
            """

        return cleaned_response
