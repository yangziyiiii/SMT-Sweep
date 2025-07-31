#!/bin/bash

BZLA_DIR="./bzla_hls"
SWEEPER_DIR="./sweeper_hls"
TMP_FILE="./compare_results.tmp"
> "$TMP_FILE"

total_improvement=0
total_ratio=0
matched_files=0

echo "[INFO] Comparing logs in: $BZLA_DIR vs $SWEEPER_DIR"

shopt -s nullglob  # 防止 *.log 展开为空时报错

for bzla_log in "$BZLA_DIR"/*.log; do
    filename=$(basename "$bzla_log")
    sweeper_log="${SWEEPER_DIR}/${filename}"

    if [[ ! -f "$sweeper_log" ]]; then
        echo "[SKIP] $filename - sweeper log not found"
        continue
    fi

    # 提取 bzla solving 时间
    bzla_solving=$(grep "\[Solving\]" "$bzla_log" | awk '{for(i=1;i<=NF;i++) if ($i ~ /^[0-9]+\.[0-9]+$/) {print $i; exit}}')
    # 提取 sweeper sweeping 的 UNSAT 总时间
    sweeper_solving=$(grep "Sweeping:" "$sweeper_log" | grep "\[UNSAT\]" | awk -F'[()]' '{print $2}' | awk '{print $1; exit}')

    if [[ -z $bzla_solving || -z $sweeper_solving ]]; then
        echo "[SKIP] $filename - failed to extract solving time"
        continue
    fi

    if [[ ! $bzla_solving =~ ^[0-9]+\.[0-9]+$ || ! $sweeper_solving =~ ^[0-9]+\.[0-9]+$ ]]; then
        echo "[SKIP] $filename - invalid number format"
        continue
    fi

    if (( $(echo "$bzla_solving == 0" | bc -l) )); then
        echo "[SKIP] $filename - bzla solving time is 0"
        continue
    fi

    # 计算对比指标
    diff_percent=$(echo "scale=4; (1 - $sweeper_solving / $bzla_solving) * 100" | bc)
    speed_ratio=$(echo "scale=4; $bzla_solving / $sweeper_solving" | bc)

    echo "$filename $bzla_solving $sweeper_solving $diff_percent $speed_ratio" >> "$TMP_FILE"

    total_improvement=$(echo "$total_improvement + $diff_percent" | bc)
    total_ratio=$(echo "$total_ratio + $speed_ratio" | bc)
    ((matched_files++))
done

# 输出总平均加速比例与倍数
if [[ $matched_files -eq 0 ]]; then
    echo "[ERROR] No matching files with valid solving time found."
    exit 1
fi

avg_improvement=$(echo "scale=2; $total_improvement / $matched_files" | bc)
avg_ratio=$(echo "scale=2; $total_ratio / $matched_files" | bc)

echo
echo "📊 Sweeper vs Bzla Summary:"
echo "Matched log files            : $matched_files"
echo "Average speedup              : $avg_improvement % faster on average"
echo "Average speed ratio          : ×$avg_ratio faster than Bzla"

echo
echo "🚀 Top 20 biggest improvements (Sweeper faster than Bzla):"
sort -k4 -nr "$TMP_FILE" | head -n 20 | awk '{printf "%-20s Bzla: %7ss  Sweeper: %7ss  Speedup: %+7.2f%%  Ratio: ×%.2f\n", $1, $2, $3, $4, $5}'

echo
echo "🐢 Top 20 smallest improvements (Sweeper slower or least faster):"
sort -k4 -n "$TMP_FILE" | head -n 20 | awk '{printf "%-20s Bzla: %7ss  Sweeper: %7ss  Speedup: %+7.2f%%  Ratio: ×%.2f\n", $1, $2, $3, $4, $5}'
