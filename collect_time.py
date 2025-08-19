#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
import re
import csv
import argparse
from collections import defaultdict, OrderedDict
import matplotlib.pyplot as plt

# -----------------------------
# 正则表达式（精确匹配相应格式）
# -----------------------------
RE_ABC   = re.compile(r"Time\s*=\s*([0-9]*\.?[0-9]+)\s*sec")
RE_KISS  = re.compile(r"\[time\]\s*real\s*=\s*([0-9]*\.?[0-9]+)")
RE_SOLVE = re.compile(r"\[Solving\]\s*([0-9]*\.?[0-9]+)\s*s")
RE_PREP  = re.compile(r"\[Pre-processing\]\s*([0-9]*\.?[0-9]+)\s*s")

# 文件名严格匹配（仅 bnd=300）
RE_BND300_FILE = re.compile(r"^(\d+)_bnd_300\.log$")      # abc/kissat
RE_EXAMPLE_FILE = re.compile(r"^example_(\d+)\.log$")     # bzla/sweeper

def read_text(path):
    try:
        with open(path, "r", encoding="utf-8", errors="ignore") as f:
            return f.read()
    except Exception:
        return ""

def parse_abc_time(text):
    # 匹配 "Time = xxx sec"
    m = RE_ABC.search(text)
    return float(m.group(1)) if m else None

def parse_kissat_time(text):
    # 取最后一个 "[time] real="（更稳妥）
    matches = RE_KISS.findall(text)
    if matches:
        return float(matches[-1])
    return None

def parse_bzla_time(text):
    # 匹配 "[Solving] xxx s"（取最后一个）
    matches = RE_SOLVE.findall(text)
    if matches:
        return float(matches[-1])
    return None

def parse_sweeper_times(text):
    # "[Pre-processing] aaa s" 和 "[Solving] bbb s"
    prep = RE_PREP.findall(text)
    solv = RE_SOLVE.findall(text)
    a = float(prep[-1]) if prep else None
    b = float(solv[-1]) if solv else None
    return a, b

def collect_hls_sec(abc_dir, kissat_dir, case_lo, case_hi):
    """
    收集 abc/kissat 的 1_bnd_300.log .. 500_bnd_300.log
    返回 dict: tool -> {case -> time}
    """
    data = {"abc": {}, "kissat": {}}

    # abc
    if os.path.isdir(abc_dir):
        for fn in os.listdir(abc_dir):
            m = RE_BND300_FILE.match(fn)
            if not m:
                continue
            case = int(m.group(1))
            if case < case_lo or case > case_hi:
                continue
            path = os.path.join(abc_dir, fn)
            t = parse_abc_time(read_text(path))
            if t is not None:
                data["abc"][case] = t

    # kissat
    if os.path.isdir(kissat_dir):
        for fn in os.listdir(kissat_dir):
            m = RE_BND300_FILE.match(fn)
            if not m:
                continue
            case = int(m.group(1))
            if case < case_lo or case > case_hi:
                continue
            path = os.path.join(kissat_dir, fn)
            t = parse_kissat_time(read_text(path))
            if t is not None:
                data["kissat"][case] = t

    return data

def collect_hls_exp(bzla_dir, sweeper_dir, case_lo, case_hi):
    """
    收集 bzla/sweeper 的 example_1.log .. example_500.log
    返回：
      - bzla: {case -> time}
      - sweeper: {case -> bbb}
      - sweeper_total: {case -> a+b}
    """
    bzla = {}
    sweeper = {}
    sweeper_total = {}

    # bzla
    if os.path.isdir(bzla_dir):
        for fn in os.listdir(bzla_dir):
            m = RE_EXAMPLE_FILE.match(fn)
            if not m:
                continue
            case = int(m.group(1))
            if case < case_lo or case > case_hi:
                continue
            path = os.path.join(bzla_dir, fn)
            t = parse_bzla_time(read_text(path))
            if t is not None:
                bzla[case] = t

    # sweeper
    if os.path.isdir(sweeper_dir):
        for fn in os.listdir(sweeper_dir):
            m = RE_EXAMPLE_FILE.match(fn)
            if not m:
                continue
            case = int(m.group(1))
            if case < case_lo or case > case_hi:
                continue
            path = os.path.join(sweeper_dir, fn)
            a, b = parse_sweeper_times(read_text(path))
            if b is not None:
                sweeper[case] = b
            if a is not None and b is not None:
                sweeper_total[case] = a + b

    return bzla, sweeper, sweeper_total

def write_csv(csv_path, bound, series_dicts):
    """
    series_dicts: dict(tool_name -> {case -> time})
    统一写出：tool,case,bound,time_s
    """
    os.makedirs(os.path.dirname(csv_path) or ".", exist_ok=True)
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["tool", "case", "bound", "time_s"])
        for tool, mp in series_dicts.items():
            for case, t in sorted(mp.items()):
                w.writerow([tool, case, bound, f"{t:.6f}"])

def plot_pdf(pdf_path, case_lo, case_hi, series_dicts):
    """
    将五个序列画为一张折线图（一个 figure，无子图，不指定颜色）
    缺失的点不连线（仅绘制有数据的 case）
    """
    plt.figure(figsize=(10, 5))
    # 固定顺序以便图例稳定
    order = ["abc", "kissat", "bzla", "sweeper", "sweeper_total"]
    labels = {
        "abc": "ABC",
        "kissat": "Kissat",
        "bzla": "Bzla",
        "sweeper": "Sweeper (Solving only)",
        "sweeper_total": "Sweeper (Pre+Solving)",
    }
    for tool in order:
        mp = series_dicts.get(tool, {})
        if not mp:
            continue
        xs = sorted(mp.keys())
        ys = [mp[i] for i in xs]
        plt.plot(xs, ys, label=labels.get(tool, tool), marker="", linewidth=1.2)

    plt.xlabel("Case ID")
    plt.ylabel("Time (s)")
    plt.title("Runtime Comparison (bound=300)")
    plt.legend()
    plt.grid(True, linestyle="--", linewidth=0.5, alpha=0.6)
    plt.tight_layout()
    plt.savefig(pdf_path)
    plt.close()

def main():
    parser = argparse.ArgumentParser(description="统计并可视化五类运行时间（abc/kissat/bzla/sweeper/sweeper_total）")
    parser.add_argument("--bound", type=int, default=300, help="仅统计该 bound（默认 300）")
    parser.add_argument("--case_lo", type=int, default=1, help="起始 case（默认 1）")
    parser.add_argument("--case_hi", type=int, default=500, help="结束 case（默认 500）")
    parser.add_argument("--csv", type=str, default="runtime_results.csv", help="输出 CSV 路径（默认 runtime_results.csv）")
    parser.add_argument("--pdf", type=str, default="runtime_plot.pdf", help="输出 PDF 路径（默认 runtime_plot.pdf）")
    # 根路径（如路径变化可用参数覆盖）
    parser.add_argument("--hls_sec_root", type=str, default="/data/ziyi/SMT-Sweep/hls_sec_experiment",
                        help="abc/kissat 根目录")
    parser.add_argument("--hls_exp_root", type=str, default="/data/ziyi/SMT-Sweep/hls_experiment_benchmarks",
                        help="bzla_hls/sweeper_hls 根目录")

    args = parser.parse_args()

    # 路径
    abc_dir = os.path.join(args.hls_sec_root, "abc")
    kissat_dir = os.path.join(args.hls_sec_root, "kissat")
    bzla_dir = os.path.join(args.hls_exp_root, "bzla_hls")
    sweeper_dir = os.path.join(args.hls_exp_root, "sweeper_hls")

    # 1) hls_sec_experiment
    sec_data = collect_hls_sec(abc_dir, kissat_dir, args.case_lo, args.case_hi)
    # 2) hls_experiment_benchmarks
    bzla_map, sweep_map, sweep_total_map = collect_hls_exp(bzla_dir, sweeper_dir, args.case_lo, args.case_hi)

    # 汇总为五类
    series = {
        "abc": sec_data.get("abc", {}),
        "kissat": sec_data.get("kissat", {}),
        "bzla": bzla_map,
        "sweeper": sweep_map,
        "sweeper_total": sweep_total_map,
    }

    # 写 CSV
    write_csv(args.csv, args.bound, series)

    # 画 PDF 折线图
    plot_pdf(args.pdf, args.case_lo, args.case_hi, series)

    # 控制台提示
    found_counts = {k: len(v) for k, v in series.items()}
    print("[DONE] CSV 写入：", os.path.abspath(args.csv))
    print("[DONE] PDF 写入：", os.path.abspath(args.pdf))
    print("[INFO] 统计条目数：", found_counts)

if __name__ == "__main__":
    main()
