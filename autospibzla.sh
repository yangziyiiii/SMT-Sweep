#!/bin/bash

# 并行度
NUM_PROCESSES=8
# 最大内存（单位 KB）：150GB
MAX_MEMORY_KB=$((150 * 1024 * 1024))

# 输入目录和输出目录
BTOR_DIR=../design/spi
OUT_DIR=../spi_experiments/bzla
mkdir -p "$OUT_DIR"
export OUT_DIR

# 可执行文件路径
BMC_BIN=./bmc
export BMC_BIN


# 获取当前用户 UID
MY_UID=$(id -u)

# 定义任务函数
run_bmc() {
    local file="$1"
    local bit="$2"

    local base=$(basename "$file" .btor2)
    local log_file="$OUT_DIR/${base}_b${bit}.log"

    echo "[RUN] $BMC_BIN -f $file -b $bit -i 200 > $log_file"
    "$BMC_BIN" -f "$file" -b "$bit" -i 200 > "$log_file" 2>&1
}

export -f run_bmc

# 定期监控内存，超出则终止
monitor_memory() {
    while true; do
        sleep 5
        total_kb=$(ps -u "$MY_UID" -o rss= | awk '{sum+=$1} END{print sum}')
        if [ "$total_kb" -gt "$MAX_MEMORY_KB" ]; then
            echo "[MONITOR] Memory exceeded 150GB. Killing all bmc processes..."
            pkill -u "$USER" -f "$BMC_BIN"
            kill $$
        fi
    done
}
monitor_memory &  # 后台运行

# 构建所有任务参数
TASKS=()
for file in "$BTOR_DIR"/*.btor2; do
    for bit in 7 8 9 10; do
        TASKS+=("$file $bit")
    done
done

# 使用 GNU Parallel 执行任务
printf "%s\n" "${TASKS[@]}" | parallel -j "$NUM_PROCESSES" --colsep ' ' run_bmc {1} {2}

# 停止后台内存监控
kill %1 2>/dev/null
