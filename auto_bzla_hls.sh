#!/bin/bash

# 并发线程数
THREADS=32

# 工具与路径设置
BZLA_BIN=./build/bzla_bmc
BTOR2_BASE=/data/ziyi/SMT-Sweep/hls_btor
LOG_DIR=./bzla_hls

# 创建日志目录（若不存在）
mkdir -p "$LOG_DIR"

# 定义每个任务的执行函数
run_task() {
    ID="$1"
    BTOR2_FILE="${BTOR2_BASE}/example_${ID}/miter/miter.btor2"
    LOG_FILE="${LOG_DIR}/example_${ID}.log"

    if [[ -f "$BTOR2_FILE" ]]; then
        echo "[RUN] example_${ID}: timeout 1800 $BZLA_BIN -f $BTOR2_FILE -i 10 -b 300 > $LOG_FILE"
        timeout 1800 "$BZLA_BIN" -f "$BTOR2_FILE" -i 10 -b 300 > "$LOG_FILE" 2>&1
        echo "[DONE] example_${ID}"
    else
        echo "[SKIP] example_${ID} - file not found: $BTOR2_FILE"
        echo "[SKIP] miter.btor2 not found: $BTOR2_FILE" > "$LOG_FILE"
    fi
}

# 导出函数及变量以供 parallel 使用
export -f run_task
export BZLA_BIN
export BTOR2_BASE
export LOG_DIR

# 并行调度任务
seq 1 500 | parallel -j "$THREADS" --halt soon,fail=1 run_task {}