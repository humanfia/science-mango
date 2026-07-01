# Formalizer/modules/external_tools.py

import os
import sys
import threading
import json
import logging
import asyncio
import shutil
import subprocess
import urllib.parse
import urllib.request
import time
from dataclasses import dataclass

try:
    import config
except ImportError:
    print("错误：config.py 未找到。")
    exit(1)

# ==============================================================================
# [依赖检查] 检查 lean-explore 库
# ==============================================================================
LEAN_EXPLORE_SDK_AVAILABLE = False
try:
    from lean_explore.api import ApiClient as LeanExploreWebClient
    from lean_explore.search import Service as LeanExploreLocalService

    LEAN_EXPLORE_SDK_AVAILABLE = True
except ImportError:
    pass


# ==============================================================================
# [数据结构]
# ==============================================================================
@dataclass
class LeanSearchResult:
    full_lean_name: str
    informal_description: str | None
    lean_type: str | None = None


class LeanSearchClient:
    """
    LeanExplore 客户端
    配置依赖: config.SEARCH_NUM_RESULTS, config.USE_LOCAL_SEARCH
    """

    _local_service = None
    _local_lock = threading.Lock()

    def __init__(self):
        self.num_results = getattr(config, 'SEARCH_NUM_RESULTS', 10)
        self.timeout = getattr(config, 'LEANSEARCH_TIMEOUT', 20)
        self.max_retries = getattr(config, 'LEANSEARCH_MAX_RETRIES', 3)
        self.retry_delay = getattr(config, 'LEANSEARCH_RETRY_DELAY', 10)

        self.api_key = getattr(config, 'LEANEXPLORE_API_KEY', None)
        self.search_packages = getattr(config, 'LEAN_SEARCH_PACKAGES', ["Mathlib"])

        # [修改] 使用新参数名 USE_LOCAL_SEARCH
        self.use_local = getattr(config, 'USE_LOCAL_SEARCH', False)

        mode_str = "LOCAL (Offline)" if self.use_local else "REMOTE (Web SDK)"
        logging.info(f"[LeanSearch] 模式: {mode_str} | Limit: {self.num_results}")

        if not LEAN_EXPLORE_SDK_AVAILABLE:
            logging.warning("!! 未检测到 'lean-explore' 库。请运行: pip install lean-explore")

    # ==========================================================================
    # 通用字段提取
    # ==========================================================================
    def _extract_fields(self, item) -> LeanSearchResult:
        full_name = getattr(item, "name", "Unknown") or "Unknown"

        desc = getattr(item, "informalization", None) or getattr(item, "docstring", None)
        desc = " ".join(desc.strip().split()) if desc else "(No description)"

        lean_type = getattr(item, "source_text", None)
        if lean_type:
            lean_type = " ".join(lean_type.split())

        return LeanSearchResult(full_lean_name=full_name, informal_description=desc, lean_type=lean_type)

    # ==========================================================================
    # 远程搜索 (Web SDK)
    # ==========================================================================
    async def _search_web_async(self, query: str):
        if not self.api_key:
            logging.error("!! [LeanExplore] 缺少 API Key。")
            return []

        # 初始化 SDK
        client = LeanExploreWebClient(api_key=self.api_key, timeout=self.timeout)
        try:
            # SDK 调用
            search_response = await client.search(
                query=query,
                limit=self.num_results,
                packages=self.search_packages
            )
            return search_response.results[:self.num_results]
        except Exception as e:
            logging.error(f"!! [LeanExplore] (Web) SDK调用失败: {e}")
            return self._search_web_http(query)

    def _search_web_http(self, query: str):
        params = urllib.parse.urlencode({
            "q": query,
            "limit": str(self.num_results),
            "packages": ",".join(self.search_packages),
        })
        url = f"https://www.leanexplore.com/api/v2/search?{params}"
        request = urllib.request.Request(
            url,
            headers={
                "Authorization": f"Bearer {self.api_key}",
                "x-api-key": self.api_key,
                "Accept": "application/json",
            },
        )
        max_retries = max(0, int(getattr(self, "max_retries", getattr(config, "LEANSEARCH_MAX_RETRIES", 3))))
        retry_delay = max(0.0, float(getattr(self, "retry_delay", getattr(config, "LEANSEARCH_RETRY_DELAY", 10))))
        total_attempts = max_retries + 1

        for attempt in range(total_attempts):
            try:
                with urllib.request.urlopen(request, timeout=self.timeout) as response:
                    data = json.loads(response.read().decode("utf-8"))
                break
            except Exception as e:
                logging.error(
                    f"!! [LeanExplore] (Web HTTP) 调用失败 "
                    f"(attempt {attempt + 1}/{total_attempts}): {e}"
                )
                if attempt >= max_retries:
                    return []
                if retry_delay > 0:
                    time.sleep(retry_delay * (2 ** attempt))

        results = []
        for item in data.get("results", [])[:self.num_results]:
            result = LeanSearchResult(
                full_lean_name=item.get("name", "Unknown") or "Unknown",
                informal_description=(
                    item.get("informalization")
                    or item.get("docstring")
                    or "(No description)"
                ),
                lean_type=item.get("source_text"),
            )
            results.append(result)
        logging.info(f"[LeanExplore] HTTP fallback returned {len(results)} result(s).")
        return results

    def _search_web(self, query: str) -> list[LeanSearchResult]:
        if not LEAN_EXPLORE_SDK_AVAILABLE: return []
        logging.debug(f"  [LeanExplore] (Remote) 搜索: '{query}'...")
        max_retries = max(0, int(getattr(self, "max_retries", getattr(config, "LEANSEARCH_MAX_RETRIES", 3))))
        retry_delay = max(0.0, float(getattr(self, "retry_delay", getattr(config, "LEANSEARCH_RETRY_DELAY", 10))))
        total_attempts = max_retries + 1

        for attempt in range(total_attempts):
            try:
                raw_results = asyncio.run(self._search_web_async(query))
                return [self._extract_fields(item) for item in raw_results]
            except Exception as e:
                logging.error(
                    f"!! [LeanExplore] (Remote) 运行时错误 "
                    f"(attempt {attempt + 1}/{total_attempts}): {e}"
                )
                if attempt >= max_retries:
                    return []
                if retry_delay > 0:
                    time.sleep(retry_delay * (2 ** attempt))

        return []

    # ==========================================================================
    # 本地搜索 (Local Service)
    # ==========================================================================
    def _ensure_local_service(self):
        if self._local_service is None and LEAN_EXPLORE_SDK_AVAILABLE:
            with self._local_lock:
                if self._local_service is None:
                    try:
                        logging.info("[LeanExplore] (Local) 加载索引...")
                        self._local_service = LeanExploreLocalService()
                        logging.info("[LeanExplore] 本地服务就绪。")
                    except Exception as e:
                        logging.error(f"!! [LeanExplore] 本地初始化失败: {e}")

    def _search_local(self, query: str) -> list[LeanSearchResult]:
        if not LEAN_EXPLORE_SDK_AVAILABLE: return []
        self._ensure_local_service()
        if not self._local_service: return []

        try:
            logging.debug(f"  [LeanExplore] (Local) 搜索: '{query}'...")
            response = self._local_service.search(
                query=query,
                limit=self.num_results,
                selected_packages=self.search_packages
            )
            return [self._extract_fields(item) for item in response.results]
        except Exception as e:
            logging.error(f"!! [LeanExplore] (Local) 搜索出错: {e}")
            return []

    # ==========================================================================
    # 主入口
    # ==========================================================================
    def search(self, concept_name: str) -> list[LeanSearchResult]:
        if self.use_local:
            return self._search_local(concept_name)
        else:
            return self._search_web(concept_name)


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
