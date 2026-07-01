# config.py
import os

# 项目根目录 (Formalizer/ 的父目录)
BASE_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
FORMALIZER_DIR = os.path.dirname(os.path.abspath(__file__))
# Lean 沙盒路径
LEAN_SANDBOX_PATH = os.path.join(BASE_DIR)

USE_LOCAL_SEARCH = False
#USE_LOCAL_LEANSEARCH = False
USE_MULTIMODAL = False

LEANEXPLORE_API_KEY = ""

LEAN_SEARCH_PACKAGES = ["Mathlib"]

LEANSEARCH_DIR = os.path.join(BASE_DIR, 'LeanSearch')

# search.py 脚本路径
LEANSEARCH_SCRIPT_PATH = os.path.join(LEANSEARCH_DIR, 'search.py')

# Prompt 路径
PROMPTS_DIR = os.path.join(os.path.dirname(__file__), 'prompts')
GROUNDING_PROMPT_FILE = os.path.join(PROMPTS_DIR, 'grounding_reasoner.txt')
EXPANSION_PROMPT_FILE = os.path.join(PROMPTS_DIR, 'expansion_module.txt')
SYNTHESIS_PROMPT_FILE = os.path.join(PROMPTS_DIR, 'synthesis_module.txt')
REFLECTION_PROMPT_FILE = os.path.join(PROMPTS_DIR, 'reflection_module.txt')
BACK_TRANSLATION_PROMPT_FILE = os.path.join(PROMPTS_DIR, 'back_translation.txt')
MERGE_BACK_TRANSLATIONS_PROMPT_FILE = os.path.join(PROMPTS_DIR, 'merge_back_translations.txt')
SEMANTIC_CHECK_PROMPT_FILE = os.path.join(PROMPTS_DIR, 'semantic_check.txt')
MULTIMODAL_SYNTHESIS_PROMPT_FILE = os.path.join(PROMPTS_DIR, 'multimodal_synthesis.txt')

LLM_API_KEY = ""

LLM_BASE_URL = ""

LLM_MODEL_NAME = ""
LLM_TIMEOUT = 120
LLM_MAX_RETRIES = 3
LLM_RETRY_DELAY = 2
PHYSICS_STUB_FALLBACK = False
PHYSICS_PRIMITIVE_STUBS = False
PHYSICS_MAX_GRAPH_NODES = 50
PHYSICS_MAX_GRAPH_DEPTH = 6
LLM_TEMPERATURE_STRICT = 0.1
LLM_TEMPERATURE_CREATIVE = 0.1

CONCURRENT_WORKERS = 1  # passk
ATTEMPTS_PER_WORKER = 16

LEANSEARCH_API_URL = "https://leansearch.net/search"
LEANSEARCH_NUM_RESULTS = 10
LEANSEARCH_TIMEOUT = 30
LEANSEARCH_MAX_RETRIES = 3 # 最多重试次数
LEANSEARCH_RETRY_DELAY = 10 # 基础重试延迟 (秒)


CURRENT_DOMAIN = "math"
