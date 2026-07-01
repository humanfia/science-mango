"""
Formalizer/modules/external_tools.py

"""

import time
import uuid
import os
import subprocess
import json
import sys
import re
from dataclasses import dataclass
import threading
import requests
from requests.exceptions import RequestException, Timeout, HTTPError
import shutil

try:
    import config
except ImportError:
    print("错误：config.py 未找到。请确保它在 Formalizer/ 目录中。")
    exit(1)

# --- 阶段一：LeanSearch ---

@dataclass
class LeanSearchResult:
    """
    封装 LeanSearch 返回的单个结果。
    我们主要关心 Lean 名称和（如果有的话）非形式化描述。
    """
    full_lean_name: str
    informal_description: str | None
    lean_type: str | None = None

class LeanSearchClient:
    """
    封装 LeanSearch 检索功能。
    根据 config.USE_LOCAL_LEANSEARCH 决定是调用本地脚本还是 Web API。
    """
    _web_lock = threading.Lock()
    def __init__(self):
        self.num_results = str(config.LEANSEARCH_NUM_RESULTS)

        self.use_local = getattr(config, 'USE_LOCAL_LEANSEARCH', False)

        self.api_url = config.LEANSEARCH_API_URL
        self.timeout = config.LEANSEARCH_TIMEOUT
        self.max_retries = config.LEANSEARCH_MAX_RETRIES
        self.retry_delay = config.LEANSEARCH_RETRY_DELAY
        print(f"[LeanSearchClient] Web API 配置已加载: {self.api_url}")

        if self.use_local:
            self.local_script_path = getattr(config, 'LEANSEARCH_SCRIPT_PATH', '')
            self.local_cwd = getattr(config, 'LEANSEARCH_DIR', '')
            print(f"[LeanSearchClient] 本地脚本配置已加载 (混合模式开启)")
            print(f"  - 脚本: {self.local_script_path}")
            print(f"  - 工作目录: {self.local_cwd}")

    def _parse_search_output(self, output_content: str) -> list[LeanSearchResult]:
        results = []
        if not output_content or not output_content.strip():
            return results

        # 尝试 1: JSON 解析 (Web API 格式)
        try:
            stripped = output_content.strip()
            if stripped.startswith('[') or stripped.startswith('{'):
                data = json.loads(stripped)
                if isinstance(data, list) and len(data) > 0:
                    hits = data[0] if isinstance(data[0], list) else data
                    for hit in hits:
                        if isinstance(hit, dict):
                            res_data = hit.get("result", hit)

                            # 提取名字
                            name_val = res_data.get("name")
                            full_name = ".".join(name_val) if isinstance(name_val, list) else str(name_val)

                            # 提取描述
                            desc = res_data.get("informal_description")
                            if not (isinstance(desc, str) and desc.strip() and "[TRANSLATION_FAILED]" not in desc):
                                desc = res_data.get("docstring")
                            if isinstance(desc, str):
                                desc = " ".join(desc.split())  # 压缩空白，防止换行过多

                            # [新增] 提取代码签名
                            lean_type = res_data.get("type", "")
                            if lean_type:
                                lean_type = " ".join(lean_type.split())  # 压缩空白

                            results.append(LeanSearchResult(
                                full_lean_name=full_name,
                                informal_description=desc,
                                lean_type=lean_type  # <--- 存入
                            ))
                return results
        except json.JSONDecodeError:
            pass

            # 尝试 2: 文本解析 (本地格式)
        return self._parse_text_output(output_content)

    def _parse_text_output(self, text: str) -> list[LeanSearchResult]:
        results = []
        chunks = re.split(r'\n\d+:\n', '\n' + text)

        for chunk in chunks:
            if "Distance:" not in chunk:
                continue
            try:
                # 提取定义名称
                name_match = re.search(
                    r'(?:definition|theorem|def|lemma|structure|inductive|class|instance)\s+([^\s\(\{]+)', chunk)
                if not name_match:
                    continue
                full_name = name_match.group(1).strip()

                lean_type = None
                desc = None

                # [关键] 分离 Type 和 Description
                # 本地脚本输出通常包含 "Elaborated type:"
                if "Elaborated type:" in chunk:
                    parts = chunk.split("Elaborated type:", 1)
                    if len(parts) > 1:
                        content_block = parts[1].strip()
                        lines = content_block.split('\n')
                        if len(lines) > 0:
                            lean_type = lines[0].strip() # 第一行是 Type
                            if len(lines) > 1:
                                desc = " ".join(lines[1:]).strip() # 后面是描述

                results.append(LeanSearchResult(
                    full_lean_name=full_name,
                    informal_description=desc,
                    lean_type=lean_type  # <--- 独立存储
                ))
            except Exception:
                continue
        return results

    def _search_local(self, concept_name: str) -> list[LeanSearchResult]:
        """ [新增] 通过 subprocess 调用本地 search.py (带详细调试) """
        print(f"  [LeanSearch] (本地) 正在搜索: '{concept_name}'...")

        if not os.path.exists(self.local_script_path):
            print(f"!! [LeanSearch] 错误: 找不到脚本文件: {self.local_script_path}")
            return []

        # 构造命令
        command = [sys.executable, self.local_script_path, concept_name]

        try:
            # 执行命令
            process = subprocess.run(
                command,
                cwd=self.local_cwd,
                capture_output=True,
                text=True,
                encoding='utf-8',
                check=False
            )

            # --- [调试逻辑开始] ---
            # 1. 检查是否有标准错误输出 (stderr)
            if process.stderr:
                print(f"!! [LeanSearch] 脚本输出了错误信息 (stderr):")
                print(f"   {process.stderr.strip()}")

            # 2. 检查返回码
            if process.returncode != 0:
                print(f"!! [LeanSearch] 脚本执行失败，返回码: {process.returncode}")
                return []

            # 3. 检查标准输出是否为空
            output_text = process.stdout.strip()
            if not output_text:
                print(f"!! [LeanSearch] 警告: 脚本返回了空内容 (stdout is empty)。")
                return []
            # --- [调试逻辑结束] ---

            # 如果一切正常，解析输出
            return self._parse_search_output(output_text)

        except Exception as e:
            print(f"!! [LeanSearch] 本地调用发生异常: {e}")
            return []

    def _search_web(self, concept_name: str) -> list[LeanSearchResult]:
        """ [原有] 基于 Web API 的搜索逻辑 """
        print(f"  [LeanSearch] (Web) 正在搜索: '{concept_name}'...")
        payload = {"query": [concept_name], "num_results": self.num_results}
        headers = {'Content-Type': 'application/json'}

        with LeanSearchClient._web_lock:
            time.sleep(20.0)
            for attempt in range(self.max_retries + 1):
                try:
                    response = requests.post(
                        self.api_url, headers=headers, json=payload, timeout=self.timeout
                    )
                    response.raise_for_status()
                    return self._parse_search_output(response.text)
                except Exception as e:
                    print(f"!! [LeanSearch] API 请求失败 (尝试 {attempt + 1}): {e}")
                    if attempt < self.max_retries:
                        time.sleep(self.retry_delay* (2 ** attempt))
        return []

    def search(self, concept_name: str) -> list[LeanSearchResult]:
        all_results = []
        seen_names = set()

        web_results = self._search_web(concept_name)
        for res in web_results:
            if res.full_lean_name not in seen_names:
                seen_names.add(res.full_lean_name)
                all_results.append(res)

        if self.use_local:
            local_results = self._search_local(concept_name)
            for res in local_results:
                if res.full_lean_name not in seen_names:
                    seen_names.add(res.full_lean_name)
                    all_results.append(res)


        print(f"  [LeanSearch] '{concept_name}' 搜索完成。合计结果: {len(all_results)} (Web: {len(web_results)})")
        return all_results

@dataclass
class LeanCompilationResult:
    """封装 Lean 编译器的输出""" #
    status: str
    error_message: str | None = None

class LeanCompilerClient:
    """
    [cite_start]管理 Lean 编译子进程，实现“编译器在环”。
    使用 'lake env lean <file>'。
    **已实现**
    """
    def __init__(self, sandbox_path: str = config.LEAN_SANDBOX_PATH):
        self.sandbox_path = os.path.abspath(sandbox_path)
        self.temp_file_name_base = "Temp"
        self.src_dir = os.path.join(self.sandbox_path, "src")
        #self.temp_file_path = os.path.join(self.src_dir, self.temp_file_name)

        # 自动查找 lake 和 lean 可执行文件路径
        try:
            self.lake_executable = self._find_lake_executable()
            self.lean_executable = self._find_lean_executable()
        except FileNotFoundError as e:
            print(f"!! [LeanCompilerClient] 致命错误: {e}")
            # 如果找不到 lake 或 lean, 无法继续
            raise e

        # 检查沙盒有效性
        lakefile_path = os.path.join(self.sandbox_path, "lakefile.lean") #
        if not os.path.isdir(self.sandbox_path) or not os.path.isfile(lakefile_path):
             print(f"!! [LeanCompilerClient] 警告: Lean 沙盒路径无效或未找到 lakefile.lean。") #
             print(f"   路径: {self.sandbox_path}")
             # 在实际应用中，这里可能应该抛出更严重的错误

        print(f"[LeanCompilerClient] 初始化完成，指向沙盒: {self.sandbox_path}")
        print(f"[LeanCompilerClient] 使用 lake: {self.lake_executable}")
        print(f"[LeanCompilerClient] 使用 lean: {self.lean_executable}")

    def _find_lake_executable(self) -> str:
        """尝试找到 lake 可执行文件""" #
        # 1. 尝试直接调用 'lake' (如果它在 PATH 中)
        lake_path = shutil.which("lake")
        if lake_path:
            return lake_path
        # 2. 尝试从 elan toolchain 目录查找
        try:
            # 尝试直接获取当前活动的 toolchain bin 路径
            elan_bin_dir_process = subprocess.run(['elan', 'which', 'lake'], capture_output=True, text=True, check=True, encoding='utf-8')
            elan_lake_path = elan_bin_dir_process.stdout.strip()
            if os.path.exists(elan_lake_path):
                 return elan_lake_path
        except (FileNotFoundError, subprocess.CalledProcessError) as e:
             print(f"[LeanCompilerClient] 查找 elan lake 时出错: {e}")
             pass

        raise FileNotFoundError("无法自动找到 'lake' 可执行文件。请确保 Lean 和 Lake 已正确安装并通过 elan 管理。") #

    def _find_lean_executable(self) -> str:
        """尝试找到 lean 可执行文件""" #
        lean_path = shutil.which("lean")
        if lean_path:
            return lean_path
        # 尝试从 elan toolchain 目录查找
        try:
            # 尝试直接获取当前活动的 toolchain bin 路径
            elan_bin_dir_process = subprocess.run(['elan', 'which', 'lean'], capture_output=True, text=True, check=True, encoding='utf-8')
            elan_lean_path = elan_bin_dir_process.stdout.strip()
            if os.path.exists(elan_lean_path):
                 return elan_lean_path

            # 作为后备，尝试解析 lake env 获取 sysroot
            # 需要先找到 lake
            if hasattr(self, 'lake_executable') and self.lake_executable:
                env_process = subprocess.run([self.lake_executable, 'env'], cwd=self.sandbox_path, capture_output=True, text=True, check=True, encoding='utf-8')
                for line in env_process.stdout.splitlines():
                    if line.startswith("LEAN_SYSROOT="): #
                        sysroot = line.split("=", 1)[1].strip('"')
                        elan_lean = os.path.join(sysroot, "bin", "lean")
                        if os.path.exists(elan_lean):
                            return elan_lean
                        break # 找到 LEAN_SYSROOT 行就停止
            else:
                 print("[LeanCompilerClient] 警告: 未找到 lake 可执行文件，无法通过 lake env 推断 lean 路径。")

        except (FileNotFoundError, subprocess.CalledProcessError) as e:
             print(f"[LeanCompilerClient] 查找 elan lean 时出错: {e}")
             pass

        raise FileNotFoundError("无法自动找到 'lean' 可执行文件。请确保 Lean 已正确安装并通过 elan 管理。") #

    def compile_code(self, full_lean_code: str, request_id: str = None) -> LeanCompilationResult:
        """
        接收完整的 Lean 代码, 尝试在沙盒中用 'lean' 编译器直接编译它。
        使用 'lake env lean <file>'。

        :param full_lean_code: 要编译的完整 Lean 代码字符串
        :param request_id: (可选) 唯一请求标识符。如果提供，将生成 "Temp_{request_id}.lean"
                           以避免并发时的文件写入冲突。
        """

        # 1. 确定唯一的文件名，防止并发冲突
        if request_id:
            fname = f"{self.temp_file_name_base}_{request_id}.lean"
        else:
            fname = f"{self.temp_file_name_base}.lean"

        temp_file_path = os.path.join(self.src_dir, fname)

        # print(f"[LeanCompilerClient] 正在尝试编译代码 (File: {fname})...", flush=True)

        try:
            if not os.path.exists(self.src_dir):
                try:
                    os.makedirs(self.src_dir)
                except OSError as e:
                    return LeanCompilationResult(status="failure", error_message=f"无法创建 src 目录: {e}")

            with open(temp_file_path, "w", encoding="utf-8") as f:
                f.write(full_lean_code)

            # 注意：lake env lean 后面跟的是相对于沙盒根目录的路径
            relative_temp_path = os.path.join("src", fname)
            command = [self.lake_executable, "env", self.lean_executable, relative_temp_path]

            # 使用 subprocess.run 调用
            process = subprocess.run(
                command,
                cwd=self.sandbox_path,  # 在沙盒目录中运行
                capture_output=True,  # 捕获输出
                text=True,
                encoding='utf-8',
                check=False,
                timeout=120,
                stdin=subprocess.DEVNULL
            )

            # 4. 分析结果
            if process.returncode == 0:
                # 即使返回码为0，如果有 warning 也暂视为成功
                if process.stderr and "warning:" in process.stderr:
                    # print(f"[LeanCompilerClient] ({fname}) 编译警告:\n{process.stderr}")
                    return LeanCompilationResult(status="success")
                else:
                    return LeanCompilationResult(status="success")
            else:
                # print(f"!! [LeanCompilerClient] ({fname}) 编译失败 (Code: {process.returncode})")
                error_output = process.stderr if process.stderr else process.stdout

                # [关键] 传入当前文件名进行错误清洗，确保只提取当前线程的错误
                clean_error = self._clean_error_message(error_output, fname)
                return LeanCompilationResult(status="failure", error_message=clean_error)

        except FileNotFoundError:
            return LeanCompilationResult(status="failure", error_message="找不到 'lake' 或 'lean' 可执行文件。")
        except subprocess.TimeoutExpired:
            return LeanCompilationResult(status="failure", error_message="编译超时。")
        except Exception as e:
            return LeanCompilationResult(status="failure", error_message=f"意外错误: {e}")
        finally:
            # 5. 清理对应的临时文件
            if os.path.exists(temp_file_path):
                try:
                    os.remove(temp_file_path)
                except OSError:
                    pass

    def _clean_error_message(self, raw_error: str, current_filename: str) -> str:
        """
        (辅助方法) 尝试清理 Lean 编译器返回的错误信息。
        只保留与 current_filename 相关的错误行。
        """
        if not raw_error:
            return "未知编译错误"

        lines = raw_error.strip().split('\n')
        error_lines = []
        keep_line = False

        target_prefixes = (current_filename, os.path.join("src", current_filename))

        for line in lines:
            stripped_line = line.strip()

            # [关键过滤] 只保留属于当前文件的错误行
            # Lean 错误通常格式为: "src/Filename.lean:10:2: error: ..."
            if stripped_line.startswith(target_prefixes) and ".lean:" in stripped_line:
                keep_line = True

                # 过滤掉环境变量和工具链的无关输出
            if stripped_line.startswith(
                    ("ELAN=", "LAKE=", "LEAN=", "PATH=", "DYLD_LIBRARY_PATH=", "info:", "[", "Build", "Compiling",
                     "Linking", "trace:")):
                continue

            # 如果处于保留块中，或者是通用的 error/warning 标记
            if keep_line or "error:" in stripped_line or "warning:" in stripped_line:
                # 避免添加重复的空行
                if stripped_line or (error_lines and error_lines[-1].strip()):
                    error_lines.append(line)

        clean_error = "\n".join(error_lines).strip()

        # 如果清理后为空 (可能因为错误格式不标准)，返回原始错误的前几行作为兜底
        if not clean_error:
            filtered_raw_lines = [line for line in lines if not line.strip().startswith(
                ("ELAN=", "LAKE=", "LEAN=", "PATH=", "DYLD_LIBRARY_PATH="))]
            return "\n".join(filtered_raw_lines[:15]).strip()

        return "\n".join(line for line in clean_error.splitlines() if line.strip())
