#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import re
from pathlib import Path
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Patch
from matplotlib.lines import Line2D

# ---------------- Paths & Regex ----------------
DIR_HEUR = Path("/data/ziyi/SMT-Sweep/experiment_heur")
DIR_NOHR = Path("/data/ziyi/SMT-Sweep/experiment_no_heur")

# 例如：Sweeping: 2115, [UNSAT] 554 (8.977 s), [SAT] 1561 (4.509 s)
SWEEP_RE = re.compile(
    r"Sweeping:\s*(\d+),\s*\[UNSAT\]\s*(\d+)\s*\(([\d\.]+)\s*s\),\s*\[SAT\]\s*(\d+)\s*\(([\d\.]+)\s*s\)",
    re.IGNORECASE
)

# ---------------- Plot style ----------------
plt.rcParams.update({
    "font.family": "Times New Roman",
    "font.size": 11,
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
})

# 配色（论文风格，柱体一色）
C_BAR_HEUR  = "#d4a373"  # Heur 柱色（砖红）
C_BAR_NOHR  = "#8ecae6"  # No-Heur 柱色（浅蓝）
# 折线颜色
C_TIME_HEUR = "#264653"  # 深青
C_TIME_NOHR = "#7f4f24"  # 棕

# ---------------- Helpers ----------------
def numeric_key(name: str):
    vs = re.findall(r"\d+", name)
    return (int(vs[-1]) if vs else float("inf"), name.lower())

def parse_one(p: Path):
    try:
        text = p.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        text = p.read_text(errors="ignore")
    m = SWEEP_RE.search(text)
    if not m:
        return None
    total = int(m.group(1))
    u_cnt = int(m.group(2)); u_t = float(m.group(3))
    s_cnt = int(m.group(4)); s_t = float(m.group(5))
    return {
        "total_calls": total,
        "unsat_cnt": u_cnt, "unsat_time": u_t,
        "sat_cnt":   s_cnt, "sat_time":   s_t,
        "solver_calls": u_cnt + s_cnt,
        "total_time":   u_t + s_t,
    }

def collect(d: Path):
    data = {}
    if not d.exists(): return data
    for p in d.iterdir():
        if p.is_file():
            r = parse_one(p)
            if r: data[p.name] = r
    return data

# ---------------- Load & Align ----------------
heur = collect(DIR_HEUR)
nohr = collect(DIR_NOHR)
common = sorted(set(heur) & set(nohr), key=numeric_key)
if not common:
    raise SystemExit("[ERROR] 两目录无可对齐且可解析的同名日志。")

# 准备数组
x = np.arange(1, len(common) + 1)    # Benchmark 序号
H_unsat = np.array([heur[n]["unsat_cnt"]  for n in common], dtype=float)
H_sat   = np.array([heur[n]["sat_cnt"]    for n in common], dtype=float)
N_unsat = np.array([nohr[n]["unsat_cnt"]  for n in common], dtype=float)
N_sat   = np.array([nohr[n]["sat_cnt"]    for n in common], dtype=float)
T_heur  = np.array([heur[n]["total_time"] for n in common], dtype=float)
T_nohr  = np.array([nohr[n]["total_time"] for n in common], dtype=float)

# 找最大值的 index（solver call / total time）
max_solver_val = max(max(H_unsat + H_sat), max(N_unsat + N_sat))
max_time_val   = max(max(T_heur), max(T_nohr))

remove_idx = set()
remove_idx |= {i for i, v in enumerate(H_unsat + H_sat) if v == max_solver_val}
remove_idx |= {i for i, v in enumerate(N_unsat + N_sat) if v == max_solver_val}
remove_idx |= {i for i, v in enumerate(T_heur) if v == max_time_val}
remove_idx |= {i for i, v in enumerate(T_nohr) if v == max_time_val}

# 过滤数据
common = [name for i, name in enumerate(common) if i not in remove_idx]
H_unsat = np.array([heur[n]["unsat_cnt"]  for n in common], dtype=float)
H_sat   = np.array([heur[n]["sat_cnt"]    for n in common], dtype=float)
N_unsat = np.array([nohr[n]["unsat_cnt"]  for n in common], dtype=float)
N_sat   = np.array([nohr[n]["sat_cnt"]    for n in common], dtype=float)
T_heur  = np.array([heur[n]["total_time"] for n in common], dtype=float)
T_nohr  = np.array([nohr[n]["total_time"] for n in common], dtype=float)

# 总调用数（用于柱高）
S_heur = H_unsat + H_sat
S_nohr = N_unsat + N_sat

# 重设横坐标
x = np.arange(1, len(common) + 1)

# ---------------- Plot ----------------
fig, ax1 = plt.subplots(figsize=(6.0, 3.6))
ax2 = ax1.twinx()

bar_w = 0.7
edge_kwargs = dict(edgecolor="black", linewidth=0.4)

# 柱状图：完全重合——先画“较大”的，再画“较小”的，使重合部分呈现较小者颜色
alpha_bar = 0.5

for xi, sh, sn in zip(x, S_heur, S_nohr):
    if sh >= sn:
        ax1.bar(xi, sh, width=bar_w, color=C_BAR_HEUR, alpha=alpha_bar, **edge_kwargs)
        ax1.bar(xi, sn, width=bar_w, color=C_BAR_NOHR, alpha=alpha_bar, **edge_kwargs)
    else:
        ax1.bar(xi, sn, width=bar_w, color=C_BAR_NOHR, alpha=alpha_bar, **edge_kwargs)
        ax1.bar(xi, sh, width=bar_w, color=C_BAR_HEUR, alpha=alpha_bar, **edge_kwargs)
# 折线：Total Time
l1, = ax2.plot(x, T_heur, color=C_TIME_HEUR, marker="o", linewidth=1.2, label="Total Time (H)")
l2, = ax2.plot(x, T_nohr, color=C_TIME_NOHR, marker="s", linestyle="--", linewidth=1.2, label="Total Time (No-H)")

# 轴与网格
ax1.set_xlabel("Benchmark")
ax1.set_ylabel("Solver Call")
ax2.set_ylabel("Total Time (s)")

ax1.set_xlim(0.5, len(x) + 0.5)
# 去掉自动增加的最大值空白
ax1.set_ylim(0, max(np.max(S_heur), np.max(S_nohr)))
ax2.set_ylim(0, max(np.max(T_heur), np.max(T_nohr)))

ax1.grid(True, linestyle=":", linewidth=0.6, alpha=0.7)

# 图例（柱子的颜色与图中一致）
legend_handles = [
    Patch(facecolor=C_BAR_HEUR, edgecolor="black", alpha=alpha_bar, label="Solver Call (H)"),
    Patch(facecolor=C_BAR_NOHR, edgecolor="black", alpha=alpha_bar, label="Solver Call (No-H)"),
    Line2D([0], [0], color=C_TIME_HEUR, marker="o", linestyle="-", linewidth=1.2, label="Total Time (H)"),
    Line2D([0], [0], color=C_TIME_NOHR, marker="s", linestyle="--", linewidth=1.2, label="Total Time (No-H)"),
]
ax1.legend(handles=legend_handles, loc="upper left", frameon=False)

fig.tight_layout()
fig.savefig("heur.pdf", dpi=500, bbox_inches="tight")

print(f"[INFO] 基准数：{len(common)}")
print("[INFO] 已输出：heur.pdf")
