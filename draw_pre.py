import matplotlib.pyplot as plt
import numpy as np

# ================== Config =====================
plt.rcParams.update({
    'font.family': 'Times New Roman',
    'font.size': 11,
    'pdf.fonttype': 42,
    'ps.fonttype': 42,
})

bit_widths = [5, 8, 10, 12, 16, 32]
timeout = 3600

# 适合学术论文的高区分度配色（柔和 Set2 系列）
tool_colors = {
    'ABC':       "#1a93fc",  # 靛蓝
    'Kissat':    "#F7DC6F",  # 朱红
    'HybridCEC': "#66cd7f",  # 青翠
    'Bitwuzla':  "#E74C3C",  # 暖棕
}
tools = list(tool_colors.keys())

# 数据
runtime_data = {
    'ABC':       [0.09, 21.83, 324.11, 'timeout', 'timeout', 'timeout'],
    'Kissat':    [0.06, 4.75, 75.38, 1265.94, 'timeout', 2090.46],
    'HybridCEC': [0.13, 5.03, 156.89, 'timeout', 'timeout', 'timeout'],
    'Bitwuzla':  [0.01, 0.01, 0.01, 0.01, 0.01, 0.01],
}

# ================== Plot =====================
plt.figure(figsize=(6, 3.6))

x = np.arange(len(bit_widths))  # 类别型横坐标
bar_width = 0.18

for i, tool in enumerate(tools):
    # 将 'timeout' 转为数值
    y_vals = [timeout if t == 'timeout' else t for t in runtime_data[tool]]

    # 画柱子
    plt.bar(
        x + (i - len(tools)/2) * bar_width + bar_width/2,  # 偏移保证分组
        y_vals,
        width=bar_width,
        color=tool_colors[tool],
        label=tool,
        edgecolor='white',
        linewidth=0.6,
        alpha=0.5
    )

# ================== Timeout line =====================
plt.axhline(y=timeout, color='red', linestyle='--', linewidth=1)

# 在红线中间标注 "timeout"
plt.text(
    x[len(x)//2] - 0.8, 
    timeout * 0.97,
    "timeout",
    color='red',
    ha='center',
    va='bottom',
    fontsize=9
)

# ================== Axis & Legend =====================
plt.xlabel('Bit Width')
plt.ylabel('Runtime (s)')
plt.xticks(x, bit_widths)
plt.yscale('log')
plt.yticks([0.01, 0.1, 1, 10, 100, 1000, timeout])

# 图例放在左上角
plt.legend(loc='upper left', frameon=False)

plt.tight_layout()
plt.savefig('pre_experiments.pdf', dpi=500, bbox_inches='tight')
plt.show()
