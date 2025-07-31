#!/bin/bash

# 输入文件目录
INPUT_DIR="/data/ziyi/SMT-Sweep/design/hls_benchmarks/benchmarks"

# 可执行程序
AIGUNROLL_BIN=~/data2/ziyi/aiger/aigunroll

# Depth 列表
DEPTHS=(30 100 300 500)

# 创建任务列表文件（临时）
TASK_FILE=$(mktemp)

# 遍历原始 .aig 文件（排除 *_bnd_*.aig）
for input_file in "$INPUT_DIR"/benchmark_*.aig; do
    if [[ "$input_file" == *_bnd_* ]]; then
        continue
    fi

    base_name=$(basename "$input_file" .aig)

    for depth in "${DEPTHS[@]}"; do
        output_file="${INPUT_DIR}/${base_name}_bnd_${depth}.aig"

        # 如果文件已存在，则跳过
        if [[ -f "$output_file" ]]; then
            echo "[SKIP] $output_file already exists" >&2
            continue
        fi

        # 写入任务命令
        echo "\"$AIGUNROLL_BIN\" -v $depth \"$input_file\" > \"$output_file\"" >> "$TASK_FILE"
    done
done

# 执行任务，最多并行 10 个
echo "[INFO] Launching parallel execution with 10 jobs..."
parallel -j 10 < "$TASK_FILE"

# 删除临时任务文件
rm -f "$TASK_FILE"
