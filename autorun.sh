#!/bin/bash

DESIGN_DIR="../design/ila"
BMC_EXEC="./bmc"
I_VALUE=200
OUT_DIR="./bmc_logs"

# 并发核数（你可以设置为 $(nproc) 或具体数字，如 8）
NUM_CORES=8
mkdir -p "$OUT_DIR"

# 构建命令任务列表
TASK_LIST_FILE="bmc_task_list.txt"
> "$TASK_LIST_FILE"  # 清空旧文件

for B in {11..15}; do
    for file in "$DESIGN_DIR"/*.btor2; do
        base=$(basename "$file" .btor2)
        log="$OUT_DIR/${base}_b${B}.txt"
        echo "$BMC_EXEC -f \"$file\" -b $B -i $I_VALUE > \"$log\" 2>&1" >> "$TASK_LIST_FILE"
    done
done

echo "Launching $(wc -l < "$TASK_LIST_FILE") tasks with $NUM_CORES parallel jobs..."
xargs -P "$NUM_CORES" -I{} bash -c {} < "$TASK_LIST_FILE"
