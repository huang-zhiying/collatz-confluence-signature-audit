"""Generate fig0_trajectory27.png — 27 的 Collatz 轨线走势图（论文 §1.1 用）。"""
import os

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

plt.rcParams["font.sans-serif"] = ["SimHei"]
plt.rcParams["axes.unicode_minus"] = False


def T(x):
    return x // 2 if x % 2 == 0 else 3 * x + 1


x = 27
vals = [x]
while x != 1:
    x = T(x)
    vals.append(x)
steps = list(range(len(vals)))

fig, ax = plt.subplots(figsize=(7.2, 3.5))
ax.plot(steps, vals, color="#4C72B0", lw=1.5, zorder=2)
ax.scatter([0], [27], color="#4C72B0", s=20, zorder=3)
ax.scatter([77], [9232], color="#C44E52", s=30, zorder=3)

ax.annotate(
    "峰值 9232（第 77 步）",
    xy=(77, 9232), xytext=(44, 8250),
    fontsize=10.5, color="#C44E52",
    arrowprops=dict(arrowstyle="->", color="#C44E52", lw=1.0),
)
ax.annotate(
    "到 1（第 111 步）",
    xy=(111, 1), xytext=(86, 2500),
    fontsize=10.5, color="#4C72B0",
    arrowprops=dict(arrowstyle="->", color="#4C72B0", lw=1.0),
)
ax.text(2, 1500, "起点 27", fontsize=10, color="#4C72B0")

ax.set_xlabel("步数 n")
ax.set_ylabel("取值 $T^n(27)$")
ax.set_xlim(0, 115)
ax.set_ylim(0, 10000)
ax.grid(True, ls=":", lw=0.6, alpha=0.45)
for side in ("top", "right"):
    ax.spines[side].set_visible(False)
fig.tight_layout()

out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fig0_trajectory27.png")
fig.savefig(out, dpi=300)
print("WROTE", out, os.path.getsize(out))
