#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import argparse
import os
import re
import math
from typing import Optional, Dict

import matplotlib.pyplot as plt
import numpy as np

# ---------------------- 解析与提取 ----------------------

# 统一从日志中匹配: [Solving] <number> s   （大小写不敏感）
RE_SOLV = re.compile(r"\[Solving\]\s+([0-9]*\.?[0-9]+)\s*s", re.IGNORECASE)

def extract_time_from_log(path: str, take_last: bool = True) -> Optional[float]:
    """从日志中抽取 [Solving] xxx s；默认取最后一次出现。"""
    try:
        with open(path, "r", encoding="utf-8", errors="ignore") as f:
            text = f.read()
        matches = RE_SOLV.findall(text)
        if not matches:
            return None
        val = matches[-1] if take_last else matches[0]
        return float(val)
    except Exception:
        return None

# ---------------------- 主流程 ----------------------

def main():
    ap = argparse.ArgumentParser(
        description="Scatter: SMT-Sweep (x) vs Bitwuzla (y); optional right y-axis for a third tool."
    )
    ap.add_argument("--bzla_dir", default="./hls_experiment_benchmarks/bzla_hls",
                    help="Bitwuzla 日志目录")
    ap.add_argument("--sweeper_dir", default="./hls_experiment_benchmarks/sweeper_hls",
                    help="SMT-Sweep 日志目录")
    ap.add_argument("--third_dir", default="",
                    help="（可选）第三工具日志目录（如 ABC/Kissat），将绘制在右侧 y 轴")
    ap.add_argument("--third_label", default="ABC",
                    help="第三工具名称（右侧图例标签），默认 ABC")
    ap.add_argument("--out_pdf", default="smt_sweep_vs_bitwuzla.pdf",
                    help="输出 PDF 文件名")
    ap.add_argument("--topk", type=int, default=20,
                    help="终端打印条目数；<=0 打印全部")
    ap.add_argument("--first", action="store_true",
                    help="取日志中第一个 [Solving]（默认最后一个）")
    ap.add_argument("--linear", action="store_true",
                    help="使用线性坐标（默认 log–log）")
    args = ap.parse_args()

    take_last = not args.first

    # 收集（仅当两边都有同名 log 时纳入）
    records = []  # (name, bzla_t, sweep_t, diff_percent, ratio)
    total_bzla = total_sweep = 0.0

    for fn in sorted(os.listdir(args.sweeper_dir)):
        if not fn.endswith(".log"):
            continue
        sweep_path = os.path.join(args.sweeper_dir, fn)
        bzla_path  = os.path.join(args.bzla_dir, fn)
        if not os.path.isfile(bzla_path):
            continue

        sw_t = extract_time_from_log(sweep_path, take_last=take_last)
        bz_t = extract_time_from_log(bzla_path,  take_last=take_last)
        if sw_t is None or bz_t is None or sw_t <= 0 or bz_t <= 0:
            continue

        diff_percent = (1.0 - sw_t / bz_t) * 100.0  # 正数=SMT-Sweep 更快
        ratio = bz_t / sw_t

        records.append((fn, bz_t, sw_t, diff_percent, ratio))
        total_bzla  += bz_t
        total_sweep += sw_t

    if not records:
        print("[ERROR] No matching files with valid [Solving] time found.")
        return

    # 汇总
    avg_impr  = (1.0 - total_sweep / total_bzla) * 100.0
    avg_ratio =  total_bzla / total_sweep
    print("\nSMT-Sweep vs Bitwuzla Summary (ALL cases plotted):")
    print(f"Matched log files            : {len(records)}")
    print(f"Average speedup              : {avg_impr:.2f} % faster on average")
    print(f"Average speed ratio          : ×{avg_ratio:.2f}")

    k = len(records) if args.topk <= 0 else min(args.topk, len(records))
    print(f"\nTop {k} biggest improvements (SMT-Sweep faster):")
    for name, bz, sw, dp, r in sorted(records, key=lambda x: x[3], reverse=True)[:k]:
        print(f"{name:20s} Bitwuzla: {bz:7.3f}s  SMT-Sweep: {sw:7.3f}s  Speedup: {dp:+7.2f}%  Ratio: ×{r:.2f}")

    print(f"\nTop {k} smallest improvements (SMT-Sweep slower / equal):")
    for name, bz, sw, dp, r in sorted(records, key=lambda x: x[3])[:k]:
        print(f"{name:20s} Bitwuzla: {bz:7.3f}s  SMT-Sweep: {sw:7.3f}s  Speedup: {dp:+7.2f}%  Ratio: ×{r:.2f}")

    # ---------------------- 绘图 ----------------------
    plt.rcParams.update({
        "font.family": "Times New Roman",
        "font.size": 11,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    })

    # 交换坐标：x=SMT-Sweep, y=Bitwuzla
    xs = [sw for _, _, sw, _, _ in records]
    ys = [bz for _, bz, _, _, _ in records]

    # 分类：SMT-Sweep faster ⇔ x < y
    faster_x = [x for x, y in zip(xs, ys) if x < y]
    faster_y = [y for x, y in zip(xs, ys) if x < y]
    slower_x = [x for x, y in zip(xs, ys) if x >= y]
    slower_y = [y for x, y in zip(xs, ys) if x >= y]

    fig, ax = plt.subplots(figsize=(4.8, 4.2))

    # 统一范围
    mn = min(xs + ys)
    mx = max(xs + ys)
    lo = mn / 1.15 if mn > 0 else 1e-3
    hi = mx * 1.15

    # y=x 参考线（左 y 轴）
    if args.linear:
        xx = np.linspace(lo, hi, 200)
    else:
        xx = np.logspace(math.log10(lo), math.log10(hi), 200)
    ax.plot(xx, xx, color="black", linewidth=1.0, label="y = x (Bitwuzla = SMT-Sweep)")

    # 散点（左轴：Bitwuzla vs SMT-Sweep）
    s1 = ax.scatter(faster_x, faster_y, marker="x", linewidths=1.2,
                    color="#4C72B0", alpha=0.9, label="SMT-Sweep faster")
    s2 = ax.scatter(slower_x, slower_y, marker="x", linewidths=1.2,
                    color="#C44E52", alpha=0.9, label="SMT-Sweep slower / equal")

    if not args.linear:
        ax.set_xscale("log"); ax.set_yscale("log")
    ax.set_xlim(lo, hi); ax.set_ylim(lo, hi)

    ax.set_xlabel("SMT-Sweep runtime (s)")
    ax.set_ylabel("Bitwuzla runtime (s)")
    ax.grid(True, which="both", linestyle="--", linewidth=0.5, alpha=0.5)

    # ---------------------- （可选）右侧 y 轴：第三工具 ----------------------
    # 用同一 x（SMT-Sweep），右轴 y=第三工具；右轴与 x 轴使用相同范围/刻度 → 可绘制其自己的 y=x
    handles = [s1, s2]
    labels  = ["SMT-Sweep faster", "SMT-Sweep slower / equal"]

    if args.third_dir:
        # 读第三工具日志
        third_map: Dict[str, float] = {}
        for fn in sorted(os.listdir(args.third_dir)):
            if fn.endswith(".log"):
                t = extract_time_from_log(os.path.join(args.third_dir, fn), take_last=take_last)
                if t is not None and t > 0:
                    third_map[fn] = t

        # 对齐到已有 records 的文件名顺序
        names = [name for name, *_ in records]
        xs3 = []
        ys3 = []
        for name, x in zip(names, xs):
            if name in third_map:
                xs3.append(x)           # 同一 x：SMT-Sweep
                ys3.append(third_map[name])

        if xs3:
            ax2 = ax.twinx()
            if not args.linear:
                ax2.set_yscale("log")
            ax2.set_ylim(lo, hi)   # 让右轴与 x 轴共用数值范围，y=x 才有一致含义
            ax2.set_ylabel(f"{args.third_label} runtime (s)")

            # 第三工具的散点（右轴）
            s3 = ax2.scatter(xs3, ys3, marker="o", s=10,
                              facecolors="none", edgecolors="#55A868",
                              linewidths=1.0, alpha=0.9,
                              label=f"{args.third_label} vs SMT-Sweep")

            # 右轴也画一条 y=x 线（针对右轴的等价基准）
            ax2.plot(xx, xx, color="#55A868", linewidth=0.8, linestyle="--",
                     label=f"y = x ({args.third_label} = SMT-Sweep)")

            # 合并图例
            handles += [s3]
            labels  += [f"{args.third_label} vs SMT-Sweep"]

    lg = ax.legend(handles, labels, loc="upper left", frameon=False)

    plt.tight_layout()
    plt.savefig(args.out_pdf, dpi=400, bbox_inches="tight")
    print(f"\n[DONE] Scatter saved to {args.out_pdf}")

if __name__ == "__main__":
    main()
