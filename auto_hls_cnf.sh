#!/bin/bash

# 输入目录
INPUT_DIR="/data/ziyi/SMT-Sweep/design/hls_benchmarks/benchmarks"

# 可执行程序路径
AIGTOCNF_BIN=~/data2/ziyi/aiger/aigtocnf

# 临时任务文件
TASK_FILE=$(mktemp)

# 遍历所有包含 _bnd_ 的 .aig 文件
find "$INPUT_DIR" -type f -name '*_bnd_*.aig' | while read -r aig_file; do
    cnf_file="${aig_file%.aig}.cnf"

    # 若 CNF 文件已存在，则跳过
    if [[ -f "$cnf_file" ]]; then
        echo "[SKIP] $cnf_file already exists" >&2
        continue
    fi

    # 生成转换命令
    echo "\"$AIGTOCNF_BIN\" \"$aig_file\" > \"$cnf_file\"" >> "$TASK_FILE"
done

# 并行执行转换任务，最多 10 个线程
echo "[INFO] Converting .aig to .cnf in parallel (10 jobs)..."
parallel -j 20 < "$TASK_FILE"

# 清理任务文件
rm -f "$TASK_FILE"
