# qcode_exact_bridge — BB 码完整 `[[n,k,d]]` Lean 验证

该项目把 `ilp_catalog.json` 的 156 条 BB CSS 码转换成逐条 Lean 证书。
Python/SciPy 只负责寻找显式逻辑算符；Lean 重新构造校验矩阵并验证：

- 块长 `n = 2ℓm`；
- `k = n - rank(H_X) - rank(H_Z)`；
- X/Z 逻辑基完整、与校验对易且配对矩阵满秩；
- 存在权重不超过 `d` 的非平凡逻辑算符（上界）；
- 不存在权重小于 `d` 的非平凡逻辑算符（`bv_decide` 生成并检查 LRAT，下界）；
- 因而最终得到 `VerifiedParameters code k d`。

批处理使用追加式 `exact_witnesses.jsonl`、逐模块 `.olean` 和
`.exact-state/` 哈希标记断点续跑。`run_exact_batch.py` 会在 witness 搜索继续时，
以受控并发编译已经生成的 Lean 模块。

运行命令：

```bash
cd /root/proposal_for_physic/science-mango/qcode_lean_bridges
. /root/proposal_for_physic/science-mango/run_env.sh

/root/proposal_for_physic/qcode-discovery/.venv/bin/python run_exact_batch.py \
  --catalog /root/proposal_for_physic/qcode-discovery/results/ilp_catalog.json \
  --out qcode_exact_bridge \
  --seed-witnesses qcode_distance_bridge/distance_witnesses.jsonl \
  --jobs 4 \
  --memory-reserve-gib 16 --memory-per-job-gib 8 \
  --search-timeout 10800 --sat-timeout 10800
```

状态查看：

```bash
python3 exact_status.py qcode_exact_bridge
```

`generator.log`、`.exact-state/logs/*.log` 和 `.exact-state/*.exit` 保存失败详情。
所有生成证明要求 0 `sorry` / 0 `admit`。

## 加速与资源安全

- 距离下界只用一个封闭的 `simp only` 规则集展开具体矩阵，随后仍由
  `bv_decide` 生成并在 Lean 中检查 LRAT。代表性 `[[288,32,12]]` 文件从
  约 262 秒降至 16.6 秒（同一证明目标与求解器）。
- `--jobs` 是最大并发，不是强制并发。调度器读取 cgroup v2 的
  `memory.current`/`memory.max`，在达到预留线前自动暂停启动新 worker。
- `.olean` 先写入 `.exact-state/tmp/`，成功后原子替换；OOM、手动停止或
  编译失败不会把半成品当作缓存。
- SIGTERM/SIGINT 会同时终止 witness 生成器和全部 Lean 进程组，避免旧版
  流程出现孤儿 Lean 进程。

当前容器限制为 64 GiB 内存、16 核 CPU 配额。不要关闭内存门控后直接使用
16 个 Lean worker；在没有其他重负载流程时，建议最大并发 4。
