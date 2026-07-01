"""
Formalizer/main.py
"""

import sys
import os
import json
import argparse
import traceback
import logging
import concurrent.futures
import threading
import time
from datetime import datetime

# 确保 'modules' 可以被导入
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

try:
    from stage1_planner import GoTPlanner
    from stage2_synthesizer import GoTSynthesizer
    from stage3_alignment import SemanticAlignmentModule
    from modules.data_structures import ConceptualGraph
    from modules.logger_setup import setup_global_logging, setup_task_logger, close_task_logger
    import config
except ImportError as e:
    print(f"错误: 无法导入必要的模块。{e}")
    exit(1)

_file_lock = threading.Lock()
_counter_lock = threading.Lock()

def save_individual_result(output_dir, index, code, status_report):
    """保存 Lean 代码和 json 报告"""
    lean_filename = os.path.join(output_dir, f"problem_{index}.lean")
    try:
        with open(lean_filename, "w", encoding="utf-8") as f:
            f.write(code)
    except IOError: pass

    meta_filename = os.path.join(output_dir, f"problem_{index}_report.json")
    try:
        with open(meta_filename, "w", encoding="utf-8") as f:
            json.dump(status_report, f, indent=2, ensure_ascii=False)
    except: pass


def process_single_problem(entry: dict, output_dir: str, image_root_dir: str = None) -> dict:
    idx = entry.get("index", "unknown")
    question = entry.get("question", "")
    category = entry.get("category", "Unknown")
    image_file = entry.get("image")
    ground_truth_answer = entry.get("answer", "")

    # 1. 开启任务日志
    task_log_file = os.path.join(output_dir, f"problem_{idx}.log")
    log_handler = setup_task_logger(task_log_file)

    # 2. 路径解析
    real_image_path = None
    if image_file and image_root_dir:
        potential_path = os.path.join(image_root_dir, image_file)
        if os.path.exists(potential_path):
            real_image_path = potential_path
            logging.debug(f"[Image] 发现关联图片: {real_image_path}")
        else:
            logging.warning(f"[Image] ⚠️ 图片文件未找到: {potential_path}")

    # [关键] 根据全局配置决定是否启用图片
    gen_image_path = real_image_path if config.USE_MULTIMODAL else None
    check_image_path = real_image_path

    logging.info(f"🚀 [Start] P{idx} ({category}) ...")

    # Debug 日志头
    logging.debug(f"{'='*60}")
    logging.debug(f" TASK: Problem {idx}")
    logging.debug(f" MULTIMODAL: {config.USE_MULTIMODAL}")
    logging.debug(f" IMAGE PATH: {real_image_path}")
    logging.debug(f"{'='*60}\n")

    result_summary = {
        "index": idx,
        "question": question,
        "status": "failed",
        "compilation_passed": False,
        "semantic_passed": False,
        "error": None,
        "consistency_level": "N/A",
        "generated_code": ""
    }
    stage2_debug_dir = os.path.join(output_dir, f"problem_{idx}_stage2_debug")
    result_summary["stage2_debug_dir"] = stage2_debug_dir

    try:
        # --- Stage 1 ---
        logging.debug(f"\n{'-'*20}\n 🧩 [Stage 1] Decomposition \n{'-'*20}")
        #planner = GoTPlanner()
        #graph = planner.run(question, image_path=gen_image_path)

        graph_checkpoint_path = os.path.join(output_dir, f"problem_{idx}_graph_checkpoint.json")

        graph = None

        if os.path.exists(graph_checkpoint_path):
            logging.info(f"📂 [Cache] 发现依赖图缓存: {os.path.basename(graph_checkpoint_path)}")
            try:
                with open(graph_checkpoint_path, "r", encoding="utf-8") as f:
                    json_str = f.read()

                graph = ConceptualGraph.from_json(json_str)
                logging.info(f"⏭️ [Skip] 成功加载依赖图，跳过 Stage 1 (Planner)！")
                logging.info(f"    根节点: {graph.root.name} | 节点数: {len(graph.nodes)}")

            except Exception as e:
                logging.warning(f"⚠️ [Cache] 加载缓存失败 ({e})，将重新运行 Stage 1。")
                graph = None

        if graph is None:
            logging.debug(f"\n{'-' * 20}\n 🧩 [Stage 1] Decomposition \n{'-' * 20}")
            try:
                planner = GoTPlanner()
                graph = planner.run(question, image_path=gen_image_path)

                with open(graph_checkpoint_path, "w", encoding="utf-8") as f:
                    f.write(graph.to_json())
                logging.info(f"💾 [Save] 依赖图已保存至: {os.path.basename(graph_checkpoint_path)}")

            except Exception as e:
                logging.error(f"Stage 1 失败: {e}")
                return result_summary  # 提前退出

        # --- Stage 2 ---
        logging.debug(f"\n{'-'*20}\n 🔨 [Stage 2] Synthesis & Verification \n{'-'*20}")
        synthesizer = GoTSynthesizer()
        synthesizer.debug_dir = stage2_debug_dir

        final_lean_code, synthesized_cache = synthesizer.run(
            graph,
            image_path=None,
            known_answer=ground_truth_answer,
            problem_id=idx
        )
        result_summary["generated_code"] = final_lean_code

        if "-- FATAL:" in final_lean_code:
            logging.warning(f"❌ [P{idx}] 阶段二合成失败。")
            result_summary["error"] = "Stage 2 Synthesis Failed"
            result_summary["compilation_passed"] = False
            logging.debug(f"Fatal Error Detail:\n{final_lean_code}")
            save_individual_result(output_dir, idx, final_lean_code, result_summary)
            return result_summary

        result_summary["compilation_passed"] = True

        # --- Stage 3 ---
        logging.debug(f"\n{'-'*20}\n ⚖️ [Stage 3] Semantic Alignment \n{'-'*20}")
        aligner = SemanticAlignmentModule()

        is_consistent, report = aligner.run(
            question,
            synthesized_cache,
            graph,
            image_path=check_image_path
        )

        consistency_level = report.get("consistency_level", "level_3")
        result_summary["consistency_level"] = consistency_level
        result_summary["ascc_report"] = report

        if is_consistent:
            result_summary["status"] = "success"
            result_summary["semantic_passed"] = True
            logging.info(f"✅ [Finish] P{idx} 完美通过！(Level: {consistency_level})")
        else:
            result_summary["status"] = "inconsistent"
            result_summary["semantic_passed"] = False
            logging.info(f"⚠️ [Finish] P{idx} 编译通过但语义不一致 (Level: {consistency_level})")

        save_individual_result(output_dir, idx, final_lean_code, result_summary)

    except Exception as e:
        err_msg = traceback.format_exc()
        logging.error(f"!! [P{idx}] 处理异常: {e}")
        logging.debug(f"详细堆栈:\n{err_msg}")
        result_summary["status"] = "error"
        result_summary["error"] = str(e)

    finally:
        close_task_logger(log_handler)

    return result_summary


def main():
    parser = argparse.ArgumentParser(description="Physics Auto-Formalizer")
    parser.add_argument("--input", type=str, default="data.jsonl", help="输入数据文件")
    parser.add_argument("--output_dir", type=str, default=None, help="指定输出目录")
    parser.add_argument("--limit", type=int, default=-1, help="仅运行前 N 个任务")
    parser.add_argument("--multimodal", action="store_true", help="开启多模态")
    parser.add_argument("--workers", type=int, default=1, help="并发处理的题目数量")
    parser.add_argument("--domain", type=str, default="math", choices=["math", "physics"])

    args = parser.parse_args()

    if args.multimodal:
        config.USE_MULTIMODAL = True

    config.CURRENT_DOMAIN = args.domain

    if config.CURRENT_DOMAIN == "physics":
        # 物理模式：必须包含 PhysLean，同时保留 Mathlib (因为物理依赖数学)
        config.LEAN_SEARCH_PACKAGES = ["Mathlib", "PhysLean"]
    else:
        # 数学模式：默认只搜 Mathlib
        config.LEAN_SEARCH_PACKAGES = ["Mathlib"]

    # 1. 目录设置
    if args.output_dir:
        run_output_dir = args.output_dir
    else:
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        run_output_dir = os.path.join(config.BASE_DIR, "batch_results", timestamp)

    os.makedirs(run_output_dir, exist_ok=True)

    setup_global_logging()
    logging.info(f"[BatchRunner] 输出目录: {run_output_dir}")
    if config.USE_MULTIMODAL:
        logging.info("[BatchRunner] 模式: 多模态 (Text + Image)")
    else:
        logging.info("[BatchRunner] 模式: 纯文本 (Text Only)")

    # 2. 读取数据
    if not os.path.exists(args.input):
        logging.error(f"错误: 找不到输入文件 {args.input}")
        return

    # 计算图片目录路径
    input_abs_path = os.path.abspath(args.input)
    input_dir = os.path.dirname(input_abs_path)
    image_search_path = os.path.join(input_dir, "image")

    if config.USE_MULTIMODAL:
        if os.path.isdir(image_search_path):
            logging.info(f"[BatchRunner] 图片目录已定位: {image_search_path}")
        else:
            logging.warning(f"[BatchRunner] ⚠️ 未找到图片目录: {image_search_path}，请检查路径！")

    all_tasks = []
    with open(args.input, "r", encoding="utf-8") as f:
        for line in f:
            if line.strip():
                try:
                    all_tasks.append(json.loads(line))
                except:
                    pass

    if args.limit > 0:
        all_tasks = all_tasks[:args.limit]

    summary_file = os.path.join(run_output_dir, "summary.jsonl")
    finished_indices = set()

    stats = {
        "compiled": 0,
        "semantic": 0
    }

    if os.path.exists(summary_file):
        logging.info(f"[Resume] 正在扫描 summary.jsonl (统计进度)...")
        try:
            with open(summary_file, "r", encoding="utf-8") as f:
                content = f.read()
            if "}{" in content:
                content = content.replace("}{", "}\n{")

            for line in content.splitlines():
                line = line.strip()
                if not line: continue
                try:
                    if line.startswith("{'") and line.endswith("'}"):
                        line = line.replace("'", '"')
                    d = json.loads(line)
                    idx = d.get("index")
                    if idx is not None:
                        finished_indices.add(str(idx))

                        if d.get("compilation_passed", False):
                            stats["compiled"] += 1
                        if d.get("semantic_passed", False):
                            stats["semantic"] += 1
                except:
                    pass
        except Exception as e:
            logging.error(f"⚠️ 读取 summary.jsonl 出错: {e}")

        logging.info(f"[Resume] 检测到 {len(finished_indices)} 个已完成任务。")
        logging.info(f"[Resume] 历史战绩 -> 🔨 编译: {stats['compiled']} | ✅ 通过: {stats['semantic']}")

    total_tasks = len(all_tasks)

    # 定义线程安全的处理逻辑
    def thread_safe_process(item):
        i, entry = item
        current_idx_str = str(entry.get("index"))

        threading.current_thread().name = f"Thread-P{current_idx_str}"

        # 1. 检查是否跳过
        if current_idx_str in finished_indices:
            return

        current_display_idx = i + 1

        try:
            # 2. 运行核心逻辑 (无锁)
            res = process_single_problem(entry, run_output_dir, image_search_path)

            # 3. 加锁写文件和更新统计
            with _file_lock:
                with open(summary_file, "a", encoding="utf-8") as f_out:
                    f_out.write(json.dumps(res, ensure_ascii=False) + "\n")
                    f_out.flush()

            with _counter_lock:
                if res["compilation_passed"]: stats["compiled"] += 1
                if res["semantic_passed"]: stats["semantic"] += 1

                # 实时打印进度
                logging.info(
                    f"📊 [Progress] P{current_idx_str} 完成 | 累计编译: {stats['compiled']} | 累计通过: {stats['semantic']}")
                logging.info("-" * 40)

        except Exception as e:
            logging.error(f"!! [Thread Error] P{current_idx_str}: {e}")

    # ==========================================
    # 启动并发执行
    # ==========================================

    # 准备任务列表
    tasks_to_run = list(enumerate(all_tasks))
    logging.info(f"🚀 启动并发模式: {args.workers} 个 Worker 正在待命...")

    try:
        # 使用线程池并发
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as executor:
            # 提交任务
            futures = [executor.submit(thread_safe_process, item) for item in tasks_to_run]

            # 等待所有任务完成
            for future in concurrent.futures.as_completed(futures):
                try:
                    future.result()  # 捕获任务内部抛出的异常
                except KeyboardInterrupt:
                    logging.warning("\n🛑 [User Exit] 用户触发中断，正在停止线程池...")
                    executor.shutdown(wait=False, cancel_futures=True)
                    break
                except Exception as e:
                    logging.error(f"Worker Exception: {e}")

    except KeyboardInterrupt:
        logging.warning("\n🛑 [User Exit] 主线程中断。")

    logging.info(f"🎉 运行结束。")


if __name__ == "__main__":
    main()
