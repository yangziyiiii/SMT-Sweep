#!/bin/bash

# 用户配置
BTOR2_DIR="/data/ziyi/SMT-Sweep/design/hls_benchmarks/benchmarks/output_btor2"
BZLA_BIN="./build/bzla_bmc"
BZLA_BOUNDS=(30 100 300 500)

CNF_DIR="/data/ziyi/SMT-Sweep/design/hls_benchmarks/benchmarks"
KISSAT_BIN=~/data2/ziyi/kissat/build/kissat

LOG_FILE="bmc_kissat_log.csv"
TMP_LOG_DIR="./tmp_logs"
THREADS=16

mkdir -p "$TMP_LOG_DIR"

# 初始化主日志文件
echo "filename,bound,time_sec,result" > "$LOG_FILE"

# 注册中断/错误自动清理机制
cleanup() {
    echo "[CLEANUP] Killing child processes and cleaning temp logs..."
    pkill -u "$USER" -f "$BZLA_BIN"
    pkill -u "$USER" -f "$KISSAT_BIN"
    pkill -u "$USER" -f timeout
    pkill -u "$USER" -f '/usr/bin/time'
    rm -rf "$TMP_LOG_DIR"
    [[ -f "$BZLA_TASKS" ]] && rm -f "$BZLA_TASKS"
    [[ -f "$CNF_LIST" ]] && rm -f "$CNF_LIST"
    exit 1
}
trap cleanup SIGINT SIGTERM ERR

echo "[INFO] Phase 1: Running BMC with bzla..."

run_bzla() {
    btor2_file="$1"
    bound="$2"

    output=$(timeout 3600 "$BZLA_BIN" -f "$btor2_file" -i 10 -b "$bound" 2>/dev/null)
    retcode=$?

    if [[ $retcode -eq 124 ]]; then
        result="timeout"
        total_time=">3600"
    elif [[ $retcode -ne 0 ]]; then
        result="crash"
        total_time="N/A"
    else
        total_time=$(echo "$output" | grep "\[Total Execution\]" | grep -o '[0-9.]\+')
        result_line=$(echo "$output" | grep "\[RESULT\]")
        if echo "$result_line" | grep -q "passed"; then
            result="pass"
        elif echo "$result_line" | grep -q "Failed"; then
            result="fail"
        else
            result="unknown"
        fi
    fi

    filename=$(echo "$btor2_file" | awk -F'/' '{for(i=1;i<=NF;i++) if($i ~ /^example_[0-9]+$/) print $i}')
    echo "$filename,b=$bound,$total_time,$result" >> "$TMP_LOG_DIR/bzla.$(uuidgen).log"
}
export BZLA_BIN TMP_LOG_DIR
export -f run_bzla

# 收集 BTOR2 文件
BTOR2_FILES=()
for i in $(seq 1 20); do
    file="$BTOR2_DIR/example_${i}/miter/miter.btor2"
    [[ -f "$file" ]] && BTOR2_FILES+=("$file")
done

# 构造 BMC 任务列表
BZLA_TASKS=$(mktemp)
for file in "${BTOR2_FILES[@]}"; do
    for b in "${BZLA_BOUNDS[@]}"; do
        echo "run_bzla \"$file\" $b" >> "$BZLA_TASKS"
    done
done

# 执行并行 BMC
parallel -j "$THREADS" < "$BZLA_TASKS"
rm -f "$BZLA_TASKS"

echo "[INFO] Phase 2: Running kissat on filtered CNF files..."

run_kissat() {
    cnf_file="$1"
    filename=$(basename "$cnf_file")

    time_output=$(timeout 3600 /usr/bin/time -f "%e" "$KISSAT_BIN" "$cnf_file" 2>&1 >/dev/null | tail -n 1)
    if [[ $? -eq 124 ]]; then
        echo "$filename,kissat_time=>3600" >> "$TMP_LOG_DIR/kissat.$(uuidgen).log"
    else
        echo "$filename,kissat_time=$time_output" >> "$TMP_LOG_DIR/kissat.$(uuidgen).log"
    fi
}
export KISSAT_BIN TMP_LOG_DIR
export -f run_kissat

# 收集符合要求的 CNF 文件
CNF_LIST=$(mktemp)
find "$CNF_DIR" -type f -name '*_bnd_*.cnf' | while read -r cnf_file; do
    num=$(basename "$cnf_file" | sed -E 's/benchmark_[^_]+_[^_]+_([0-9]+)_bnd_.*/\1/')
    if [[ "$num" =~ ^[0-9]+$ && "$num" -ge 1 && "$num" -le 20 ]]; then
        echo "$cnf_file" >> "$CNF_LIST"
    fi
done

# 并行执行 kissat
parallel -j "$THREADS" run_kissat :::: "$CNF_LIST"
rm -f "$CNF_LIST"

echo "[INFO] Merging logs..."
cat "$TMP_LOG_DIR"/*.log >> "$LOG_FILE"
rm -rf "$TMP_LOG_DIR"

echo "[DONE] Log written to $LOG_FILE"
