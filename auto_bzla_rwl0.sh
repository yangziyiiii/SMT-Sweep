#!/bin/bash

# 并发线程数
THREADS=32

# 工具与路径设置
BZLA_BIN=bitwuzla
BTOR2_BASE=/data/ziyi/SMT-Sweep/hls_btor
LOG_DIR=./bzla_v3_rwl0

# 创建日志目录（若不存在）
mkdir -p "$LOG_DIR"

# 定义每个任务的执行函数
run_task() {
    ID="$1"
    SMT2_FILE="${BTOR2_BASE}/example_${ID}/miter/miter.btor2.smt2"
    LOG_FILE="${LOG_DIR}/example_${ID}.log"

    if [[ -f "$SMT2_FILE" ]]; then
        echo "[RUN] example_${ID}: $BZLA_BIN -v 3 -rwl 0 $SMT2_FILE > $LOG_FILE"
        $BZLA_BIN -v 3 -rwl 0 "$SMT2_FILE" > "$LOG_FILE" 2>&1
        echo "[DONE] example_${ID}"
    else
        echo "[SKIP] example_${ID} - file not found: $SMT2_FILE"
        echo "[SKIP] miter.btor2.smt2 not found: $SMT2_FILE" > "$LOG_FILE"
    fi
}

# 导出函数及变量供 parallel 调用
export -f run_task
export BZLA_BIN
export BTOR2_BASE
export LOG_DIR

# 并行调度任务（example_1 到 example_500）
seq 1 500 | parallel -j "$THREADS" --halt soon,fail=1 run_task {}
