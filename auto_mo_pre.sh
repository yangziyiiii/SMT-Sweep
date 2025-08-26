#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
import sys
import csv
import time
import shlex
import signal
import pathlib
import traceback
import subprocess
from concurrent.futures import ThreadPoolExecutor, as_completed

# ================== 配置区（如需更改路径/参数可在此修改） ==================

WIDTHS = [5, 8, 10, 12, 16, 32]                # 需要处理的 bit-width 列表
TIMEOUT_SEC = 60 * 60                           # 每条命令超时：1 小时
MAX_MEM_BYTES = 100 * 1024**3                   # 100 GB 内存上限
N_WORKERS = 8                                   # 并发线程数

# 可执行文件路径
BIN_AIGAND = os.path.expanduser("~/data2/ziyi/aiger/aigand")
BIN_ABC    = os.path.expanduser("~/abc/abc")
BIN_HYB    = os.path.expanduser("~/data2/ziyi/Hybrid-CEC/hybrid_cec")
BIN_BITW   = "bitwuzla"                         # 假定在 PATH 中；如需绝对路径可改为 ~/.../bitwuzla

# 设计文件根目录
DIR_MUL = "/data/ziyi/SMT-Sweep/design/mul"

# 结果输出目录
OUT_DIR = pathlib.Path("experiment_motivation")

# ========================================================================


def ensure_out_dir():
    OUT_DIR.mkdir(parents=True, exist_ok=True)


def set_limits():
    """在子进程中设置资源限制与独立进程组，确保超时/终止能清理整个进程树。"""
    try:
        import resource
        # 限制虚拟内存（地址空间）
        resource.setrlimit(resource.RLIMIT_AS, (MAX_MEM_BYTES, MAX_MEM_BYTES))
    except Exception:
        # 某些平台/内核可能不支持，忽略但不中断
        pass
    # 让子进程成为新会话首进程，便于整体杀死进程组
    os.setsid()


def run_command(cmd_list, log_path, timeout_sec, env=None, cwd=None):
    """运行外部命令，记录用时与日志。返回 (status, elapsed_seconds)。"""
    start = time.monotonic()
    log_path = pathlib.Path(log_path)
    try:
        with log_path.open("wb") as logf:
            # 使用 Popen + communicate 以便自定义超时与进程组清理
            proc = subprocess.Popen(
                cmd_list,
                stdout=logf,
                stderr=subprocess.STDOUT,
                env=env,
                cwd=cwd,
                preexec_fn=set_limits  # 资源限制 + setsid
            )
            try:
                proc.wait(timeout=timeout_sec)
                ret = proc.returncode
                elapsed = time.monotonic() - start
                if ret == 0:
                    return ("ok", elapsed)
                else:
                    return (f"exit_{ret}", elapsed)
            except subprocess.TimeoutExpired:
                # 超时：杀掉整个进程组
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except Exception:
                    pass
                elapsed = time.monotonic() - start
                return ("timeout", elapsed)
    except FileNotFoundError as e:
        elapsed = time.monotonic() - start
        with log_path.open("ab") as logf:
            logf.write(f"\n[ERROR] File not found: {e}\n".encode("utf-8", "ignore"))
        return ("not_found", elapsed)
    except Exception as e:
        elapsed = time.monotonic() - start
        with log_path.open("ab") as logf:
            tb = traceback.format_exc()
            logf.write(f"\n[ERROR] Exception: {e}\n{tb}\n".encode("utf-8", "ignore"))
        return ("error", elapsed)


def file_exists(p):
    return pathlib.Path(p).exists()


def preprocess_one_output_aig(width):
    """运行 aigand: 输入 mul_fix_{w}.aig -> 输出 mul_fix_{w}_one_output.aig"""
    src = f"{DIR_MUL}/mul_fix_{width}.aig"
    dst = f"{DIR_MUL}/mul_fix_{width}_one_output.aig"
    log = OUT_DIR / f"prep_mul_fix_{width}.log"

    if not file_exists(src):
        # 记录缺失
        with open(log, "w", encoding="utf-8") as f:
            f.write(f"[WARN] Missing input AIG: {src}\n")
        return ("missing_input", 0.0, src, dst)

    # aigand 以 stdout 形式输出，模拟 shell 重定向 ">"
    start = time.monotonic()
    try:
        with open(dst, "wb") as out_f, open(log, "wb") as logf:
            proc = subprocess.Popen(
                [BIN_AIGAND, src],
                stdout=out_f,
                stderr=logf,
                preexec_fn=set_limits
            )
            try:
                proc.wait(timeout=TIMEOUT_SEC)
                ret = proc.returncode
                elapsed = time.monotonic() - start
                if ret == 0:
                    return ("ok", elapsed, src, dst)
                else:
                    return (f"exit_{ret}", elapsed, src, dst)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except Exception:
                    pass
                elapsed = time.monotonic() - start
                return ("timeout", elapsed, src, dst)
    except Exception as e:
        with open(log, "ab") as logf:
            tb = traceback.format_exc()
            logf.write(f"\n[ERROR] Exception: {e}\n{tb}\n".encode("utf-8", "ignore"))
        return ("error", 0.0, src, dst)


def build_jobs():
    """构造任务列表：每个 (task_name, width, cmd_list, log_path, env)。"""
    jobs = []
    # 先确保 one_output.aig 均已生成
    prep_results = []
    for w in WIDTHS:
        prep_results.append((w, preprocess_one_output_aig(w)))

    # 任务定义
    for w, (prep_status, _, src_aig, dst_aig) in prep_results:
        # 若 one_output 生成失败则跳过基于 AIG 的任务
        have_one_output = file_exists(dst_aig)

        # ---- (1) ABC: &cec -m ----
        if have_one_output:
            cmd_abc = [
                BIN_ABC, "-c",
                f"&r {dst_aig}; &cec -m"
            ]
            log_abc = OUT_DIR / f"abc_mul_fix_{w}.log"
            jobs.append(("abc", w, cmd_abc, log_abc, None))

        # ---- (2) KISSAT via ABC: &kissat ----
        if have_one_output:
            env_kissat = os.environ.copy()
            # 将 kissat 所在目录加入 PATH（供 ABC 的 &kissat 调用）
            env_kissat["PATH"] = env_kissat.get("PATH", "") + ":" + os.path.expanduser("~/data2/ziyi/kissat/build")
            cmd_kissat = [
                BIN_ABC, "-c",
                f"&r {dst_aig}; &kissat"
            ]
            log_kissat = OUT_DIR / f"kissat_mul_fix_{w}.log"
            jobs.append(("kissat", w, cmd_kissat, log_kissat, env_kissat))

        # ---- (3) Hybrid-CEC ----
        if have_one_output:
            cmd_hyb = [BIN_HYB, dst_aig]
            log_hyb = OUT_DIR / f"hybridcec_mul_fix_{w}.log"
            jobs.append(("hybridcec", w, cmd_hyb, log_hyb, None))

        # ---- (4) Bitwuzla (.btor2 优先, 否则 .btor) ----
        btor2 = f"{DIR_MUL}/mul_fix_{w}.btor2"
        btor  = f"{DIR_MUL}/mul_fix_{w}.btor"
        bitw_input = btor2 if file_exists(btor2) else (btor if file_exists(btor) else None)
        if bitw_input is not None:
            cmd_bitw = [BIN_BITW, bitw_input]
            log_bitw = OUT_DIR / f"bitwuzla_mul_fix_{w}.log"
            jobs.append(("bitwuzla", w, cmd_bitw, log_bitw, None))
        else:
            # 若 btor/btor2 均不存在，给出提示日志
            with open(OUT_DIR / f"bitwuzla_mul_fix_{w}.log", "w", encoding="utf-8") as f:
                f.write(f"[WARN] Missing BTOR/BTOR2 for width {w}: {btor2} / {btor}\n")

    return jobs


def main():
    ensure_out_dir()

    jobs = build_jobs()
    if not jobs:
        print("No runnable jobs were constructed. Please check input files.")
        return

    # 运行任务并收集结果
    results = []  # (task, width, status, elapsed)
    with ThreadPoolExecutor(max_workers=N_WORKERS) as ex:
        fut2job = {
            ex.submit(run_command, cmd, log, TIMEOUT_SEC, env, None): (task, width)
            for (task, width, cmd, log, env) in jobs
        }
        for fut in as_completed(fut2job):
            task, width = fut2job[fut]
            try:
                status, elapsed = fut.result()
            except Exception:
                status, elapsed = ("error", 0.0)
            results.append((task, width, status, elapsed))

    # 汇总为 {width: {task: (status, elapsed)}}
    summary = {}
    for task, width, status, elapsed in results:
        summary.setdefault(width, {})[task] = (status, elapsed)

    # 写出 CSV：列为 width + 四个任务用时（秒）+ 四个任务状态
    csv_path = OUT_DIR / "summary.csv"
    tasks = ["abc", "kissat", "hybridcec", "bitwuzla"]
    header = ["width"] + [f"{t}_time_s" for t in tasks] + [f"{t}_status" for t in tasks]

    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(header)
        for w in sorted(summary.keys()):
            row_times = []
            row_stats = []
            for t in tasks:
                if t in summary[w]:
                    st, el = summary[w][t]
                    row_times.append(f"{el:.3f}")
                    row_stats.append(st)
                else:
                    row_times.append("")
                    row_stats.append("skipped")
            writer.writerow([w] + row_times + row_stats)

    print(f"[DONE] Logs and summary written to: {OUT_DIR.resolve()}")
    print(f"       Summary CSV: {csv_path.resolve()}")


if __name__ == "__main__":
    main()
