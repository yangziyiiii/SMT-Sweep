#!/usr/bin/env bash
set -euo pipefail

# 并行度，可按机器配置调整
: "${MAX_JOBS:=4}"

# 结果根目录
OUT_ROOT="./hls_sec_experiment_300_hcec"
mkdir -p "$OUT_ROOT"/{abc,hybridcec,kissat,bzla,sweep}

# 路径与常量
ABC_BIN="$HOME/abc/abc"
HYBRIDCEC_BIN="$HOME/data2/ziyi/Hybrid-CEC/hybrid_cec"
KISSAT_BIN="$HOME/data2/ziyi/kissat/build/kissat"
BZLA_BIN="./build/bzla_bmc"
SWEEP_BIN="./build/bmc"

AIG_BASE="/data/ziyi/SMT-Sweep/design/hls_benchmarks/benchmarks"
BTOR2_BASE="/data/ziyi/SMT-Sweep/hls_experiment_benchmarks/hls_btor"

TIME_BIN="/usr/bin/time"
TIME_FMT="[time] real=%e user=%U sys=%S maxrss=%MKB"

# 仅运行以下 case
case_ids=(129 221 248 239 234 193 249 266 259 231 218)

# 需要运行的 bound
bounds=(300)

run_job() {
  local tool="$1"          # abc | hybridcec | kissat | bzla | sweep
  local logfile="$2"       # 输出日志文件路径
  shift 2
  local cmd=( "$@" )       # 实际执行的命令（数组）

  while (( $(jobs -rp | wc -l) >= MAX_JOBS )); do sleep 0.2; done

  {
    echo "========== $(date '+%F %T') =========="
    echo "[tool]   $tool"
    echo "[cmd]    ${cmd[*]}"
    echo "--------------------------------------"
    if ! $TIME_BIN -f "$TIME_FMT" timeout 3600 bash -lc "${cmd[*]}"; then
      status=$?
      if [[ $status -eq 124 ]]; then
        echo "[timeout] Command exceeded 3600s and was terminated."
      else
        echo "[error] Command exited with status $status"
      fi
    fi
    echo "======================================"
    echo
  } >> "$logfile" 2>&1 &
}

skip_or_run_if_exists() {
  local infile="$1"
  local log="$2"
  if [[ ! -f "$infile" ]]; then
    {
      echo "========== $(date '+%F %T') =========="
      echo "[skip]   input not found"
      echo "[input]  $infile"
      echo "======================================"
      echo
    } >> "$log"
    return 1   # 不存在则不运行
  fi
  return 0     # 存在则运行
}

# 主循环：仅遍历指定 case 列表
for case_id in "${case_ids[@]}"; do
  for b in "${bounds[@]}"; do
    # -------------------- abc --------------------
    aig_file="${AIG_BASE}/benchmark_20250728_141735_${case_id}_bnd_${b}.aig"
    # abc_log="${OUT_ROOT}/abc/${case_id}_bnd_${b}.log"
    # if skip_or_run_if_exists "$aig_file" "$abc_log"; then
    #   run_job "abc" "$abc_log" \
    #     "$ABC_BIN -c \"&r ${aig_file}; &cec -m\""
    # fi

    # -------------------- HybridCEC --------------------
    hybridcec_log="${OUT_ROOT}/hybridcec/${case_id}_bnd_${b}.log"
    if skip_or_run_if_exists "$aig_file" "$hybridcec_log"; then
      run_job "hybridcec" "$hybridcec_log" \
        "$HYBRIDCEC_BIN ${aig_file}"
    fi

    # -------------------- kissat（CNF） --------------------
    # cnf_file="${AIG_BASE}/benchmark_20250728_141735_${case_id}_bnd_${b}.cnf"
    # kissat_log="${OUT_ROOT}/kissat/${case_id}_bnd_${b}.log"
    # if skip_or_run_if_exists "$cnf_file" "$kissat_log"; then
    #   run_job "kissat" "$kissat_log" \
    #     "$KISSAT_BIN ${cnf_file}"
    # fi

    # -------------------- bzla（BTOR2，example_<case>） --------------------
    # btor2_file="${BTOR2_BASE}/example_${case_id}/miter/miter.btor2"
    # bzla_log="${OUT_ROOT}/bzla/${case_id}_bnd_${b}.log"
    # if skip_or_run_if_exists "$btor2_file" "$bzla_log"; then
    #   run_job "bzla" "$bzla_log" \
    #     "$BZLA_BIN -f ${btor2_file} -b ${b} -i 100"
    # fi

    # -------------------- sweep（BTOR2，example_<case>） --------------------
    # sweep_log="${OUT_ROOT}/sweep/${case_id}_bnd_${b}.log"
    # if skip_or_run_if_exists "$btor2_file" "$sweep_log"; then
    #   run_job "sweep" "$sweep_log" \
    #     "$SWEEP_BIN -f ${btor2_file} -b ${b} -i 100"
    # fi
  done
done

wait
echo "[INFO] All jobs finished."
