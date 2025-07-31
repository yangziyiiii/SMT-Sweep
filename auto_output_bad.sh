#!/bin/bash

# 源路径
SRC_BASE="/data/ziyi/SMT-Sweep/design/benchmark_action_40_with_cb"
# 目标路径
DST_BASE="./hls_btor"

# 创建目标根目录（如果不存在）
mkdir -p "$DST_BASE"

# 遍历 example_1 到 example_20
for (( ID=1; ID<=500; ID++ )); do
    SRC_FILE="${SRC_BASE}/example_${ID}/miter.btor2"
    DST_DIR="${DST_BASE}/example_${ID}/miter"
    DST_FILE="${DST_DIR}/miter.btor2"

    if [[ -f "$DST_FILE" ]]; then
        echo "[SKIP] example_${ID} - already exists at $DST_FILE"
        continue
    fi

    if [[ -f "$SRC_FILE" ]]; then
        echo "[COPY] example_${ID}"

        # 创建目标路径
        mkdir -p "$DST_DIR"

        # 拷贝原始文件
        cp "$SRC_FILE" "$DST_FILE"

        # 替换 " output " → " bad "
        sed -i 's/\(\s\)output\(\s\)/\1bad\2/' "$DST_FILE"

        echo "[DONE] example_${ID} modified at $DST_FILE"
    else
        echo "[SKIP] example_${ID} - source file not found: $SRC_FILE"
    fi
done
