"""
Formalizer/modules/logger_setup.py
"""
import logging
import sys
import threading

class ThreadLogFilter(logging.Filter):
    """
    日志过滤器：只允许来自特定问题线程及其子 worker 的日志通过。
    """
    def __init__(self, thread_name):
        super().__init__()
        self.thread_name = str(thread_name)
        self.thread_prefix = f"{self.thread_name}-"

    def filter(self, record):
        if self.thread_name == "MainThread":
            return True
        return (
            record.threadName == self.thread_name
            or record.threadName.startswith(self.thread_prefix)
        )

def setup_global_logging():
    """
    初始化全局日志：控制台输出
    """
    logger = logging.getLogger()
    logger.setLevel(logging.DEBUG)

    if logger.hasHandlers():
        logger.handlers.clear()

    # 屏蔽第三方库的噪音
    logging.getLogger("httpx").setLevel(logging.WARNING)
    logging.getLogger("httpcore").setLevel(logging.WARNING)
    logging.getLogger("openai").setLevel(logging.WARNING)
    logging.getLogger("urllib3").setLevel(logging.WARNING)

    # 1. 终端 Handler (保留，显示所有线程的 INFO)
    console_handler = logging.StreamHandler(sys.stdout)
    console_handler.setLevel(logging.INFO)
    console_formatter = logging.Formatter('%(message)s')
    console_handler.setFormatter(console_formatter)
    logger.addHandler(console_handler)

    return logger

def setup_task_logger(log_file_path):
    """
    [关键] 为当前任务挂载一个独立的文件日志 Handler。
    并利用 Filter 确保它只记录当前线程产生的日志。
    """
    # 1. 获取当前线程的名字
    # 在 main.py 中，我们需要确保每个 Worker 线程有唯一的名字
    current_thread_name = threading.current_thread().name

    logger = logging.getLogger()

    # 2. 创建文件 Handler
    file_handler = logging.FileHandler(log_file_path, mode='w', encoding='utf-8')
    file_handler.setLevel(logging.DEBUG) # 记录该线程的所有细节

    # 3. 格式化 (加上线程名以便调试)
    file_formatter = logging.Formatter(
        '%(asctime)s [%(levelname)s] [%(threadName)s] %(message)s',
        datefmt='%H:%M:%S'
    )
    file_handler.setFormatter(file_formatter)

    # 4. [核心] 添加过滤器
    # 告诉这个 Handler：只有标签为 current_thread_name 的日志才准写进来！
    thread_filter = ThreadLogFilter(current_thread_name)
    file_handler.addFilter(thread_filter)

    logger.addHandler(file_handler)
    return file_handler

def close_task_logger(handler):
    """
    任务结束，移除 Handler
    """
    if handler:
        logger = logging.getLogger()
        logger.removeHandler(handler)
        handler.close()
