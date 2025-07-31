#!/bin/bash

LOG_DIR="/data/ziyi/SMT-Sweep/bzla_hls"

# 初始化计数器
lt_10=0
lt_20=0
lt_30=0
passed_count=0
total_files=0

# 初始化文件名列表
not_passed_files=()
ge_10s_files=()
ge_20s_files=()
ge_30s_files=()

# 遍历所有日志文件
for logfile in "$LOG_DIR"/*.log; do
    ((total_files++))

    # 提取 solving 行与 result 行
    solving_line=$(grep "\[Solving\]" "$logfile")
    result_line=$(grep "\[RESULT\]" "$logfile")

    filename=$(basename "$logfile")

    # 提取 solving 时间
    if [[ $solving_line =~ ([0-9]+\.[0-9]+) ]]; then
        solving_time=${BASH_REMATCH[1]}
        solving_sec=$(printf "%.2f" "$solving_time")

        if (( $(echo "$solving_sec < 10.0" | bc -l) )); then
            ((lt_10++))
        else
            ge_10s_files+=("$filename")
        fi

        if (( $(echo "$solving_sec < 20.0" | bc -l) )); then
            ((lt_20++))
        else
            ge_20s_files+=("$filename")
        fi

        if (( $(echo "$solving_sec < 30.0" | bc -l) )); then
            ((lt_30++))
        else
            ge_30s_files+=("$filename")
        fi
    fi

    # 检查是否 passed
    if echo "$result_line" | grep -q "passed"; then
        ((passed_count++))
    else
        not_passed_files+=("$filename")
    fi
done

# 输出摘要统计信息
echo "📊 Bzla HLS Log Summary:"
echo "Total log files processed     : $total_files"
echo "[Solving] < 10s               : $lt_10"
echo "[Solving] < 20s               : $lt_20"
echo "[Solving] < 30s               : $lt_30"
echo "[RESULT] Bound xxx passed     : $passed_count"
echo

# 输出未通过文件列表
if [[ ${#not_passed_files[@]} -gt 0 ]]; then
    echo "❌ Logs without 'passed':"
    for f in "${not_passed_files[@]}"; do
        echo "  $f"
    done
    echo
fi

# 输出耗时 ≥10s 的文件
if [[ ${#ge_10s_files[@]} -gt 0 ]]; then
    echo "⏱️ [Solving] ≥ 10s files:"
    for f in "${ge_10s_files[@]}"; do
        echo "  $f"
    done
    echo
fi

# 输出耗时 ≥20s 的文件
if [[ ${#ge_20s_files[@]} -gt 0 ]]; then
    echo "⏱️ [Solving] ≥ 20s files:"
    for f in "${ge_20s_files[@]}"; do
        echo "  $f"
    done
    echo
fi

# 输出耗时 ≥30s 的文件
if [[ ${#ge_30s_files[@]} -gt 0 ]]; then
    echo "⏱️ [Solving] ≥ 30s files:"
    for f in "${ge_30s_files[@]}"; do
        echo "  $f"
    done
    echo
fi
