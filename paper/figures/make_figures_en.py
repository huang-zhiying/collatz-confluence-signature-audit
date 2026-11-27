"""
make_figures_en.py — English versions of the paper figures (300 dpi)

Same data, same random seed, same call order as make_figures.py, so all reported
numbers (886 unique values, n0, etc.) are reproduced exactly. Only the labels
are in English and the output goes to paper/figures/en/.
"""
import math
import os
import random
import statistics

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

plt.rcParams['axes.unicode_minus'] = False

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)))
random.seed(20260920)

DPI = 300


def T(x):
    return x // 2 if x % 2 == 0 else 3 * x + 1


def first_meeting_z(a, b, max_steps=50000):
    va = {a: 0}; vb = {b: 0}; ca, cb = a, b
    for tot in range(1, max_steps + 1):
        ca = T(ca)
        if ca in vb:
            return ca, tot + vb[ca]
        va[ca] = tot
        cb = T(cb)
        if cb in va:
            return cb, va[cb] + tot
        vb[cb] = tot
    return None, None


# ---------- fig 0: trajectory of 27 ----------
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
ax.annotate("peak 9232 (step 77)", xy=(77, 9232), xytext=(44, 8250),
            fontsize=10.5, color="#C44E52",
            arrowprops=dict(arrowstyle="->", color="#C44E52", lw=1.0))
ax.annotate("reaches 1 (step 111)", xy=(111, 1), xytext=(82, 2500),
            fontsize=10.5, color="#4C72B0",
            arrowprops=dict(arrowstyle="->", color="#4C72B0", lw=1.0))
ax.text(2, 1500, "start 27", fontsize=10, color="#4C72B0")
ax.set_xlabel("step n")
ax.set_ylabel("value $T^n(27)$")
ax.set_xlim(0, 115)
ax.set_ylim(0, 10000)
ax.grid(True, ls=":", lw=0.6, alpha=0.45)
for side in ("top", "right"):
    ax.spines[side].set_visible(False)
fig.tight_layout()
fig.savefig(os.path.join(OUT, 'fig0_trajectory27.png'), dpi=DPI)
plt.close(fig)
print("fig0 done")

# ---------- fig 1: distribution of z ----------
def sample_zs(k, n=80):
    zs = []
    for _ in range(n):
        a = random.randint(1 << (k - 1), (1 << k) - 1)
        b = random.randint(1 << (k - 1), (1 << k) - 1)
        z, _ = first_meeting_z(a, b)
        if z:
            zs.append(z)
    return zs


z20 = sample_zs(20)
z256 = sample_zs(256)

fig, axes = plt.subplots(1, 2, figsize=(10, 4))
for ax, data, title in ((axes[0], z20, 'k=20'), (axes[1], z256, 'k=256')):
    bl = [z.bit_length() for z in data]
    ax.hist(bl, bins=range(0, max(bl) + 2), color='#4C72B0', edgecolor='white')
    ax.set_title(f'Bit length of the meeting point z ({title})')
    ax.set_xlabel('bit length of z'); ax.set_ylabel('number of keys')
    ax.axvline(statistics.median(bl), color='red', ls='--',
               label=f'median {statistics.median(bl):.0f}')
    ax.legend()
fig.suptitle('Low-altitude confluence: larger starting values, still very low meeting points',
             fontsize=12)
fig.tight_layout()
fig.savefig(os.path.join(OUT, 'fig1_z_distribution.png'), dpi=DPI)
plt.close(fig)
print("fig1 done")

# ---------- fig 2: attack cost vs k ----------
data = {
    64:  [276, 674, 6515],
    128: [495, 4071, 115],
    256: [122, 308, 605],
}
fig, ax = plt.subplots(figsize=(7, 4.5))
for k, tries in data.items():
    ax.scatter([k] * len(tries), tries, s=60, color='#C44E52', zorder=3)
    ax.scatter([k], [statistics.median(tries)], marker='_', s=200, color='black',
               label=f'k={k} median {statistics.median(tries):.0f}' if k == 64 else None)
ax.set_yscale('log')
ax.set_xticks(sorted(data.keys()))
ax.set_xlabel('security parameter k (bit length of starting values)')
ax.set_ylabel('samples needed to hit (log scale)')
ax.set_title('Same-distribution sampling cost vs k: flat in k (9/9 instances broken)')
ax.grid(True, which='both', alpha=0.3)
ks = [64, 128, 256]
ax.plot(ks, [2 ** k for k in ks], ls='--', color='gray', label='$2^k$ exhaustively (reference)')
ax.legend()
fig.tight_layout()
fig.savefig(os.path.join(OUT, 'fig2_attack_cost.png'), dpi=DPI)
plt.close(fig)
print("fig2 done")

# ---------- fig 3: distribution of d (k=128) ----------
k = 128
lo, hi = 1 << (k - 1), 1 << k
a0 = random.randint(lo, hi - 1)
b0 = random.randint(lo, hi - 1)
_, n0 = first_meeting_z(a0, b0)
m = abs(a0 - b0)
ds = []
while len(ds) < 4000:
    a = random.randint(lo, hi - 1)
    for b in (a + m, a - m):
        if lo <= b < hi:
            _, d = first_meeting_z(a, b)
            if d:
                ds.append(d)
            break
uniq = len(set(ds))
h2e = math.log2(uniq)
fig, ax = plt.subplots(figsize=(8, 4.5))
ax.hist(ds, bins=80, color='#55A868', edgecolor='white')
ax.axvline(n0, color='red', ls='--', label=f'public key n = {n0}')
ax.set_xlabel("value of $d(a', a'+m)$")
ax.set_ylabel('sampled pairs')
ax.set_title(f'k=128: distribution of d --- {len(ds)} samples, only {uniq} distinct values '
             f'(entropy ~{h2e:.1f} bit)')
ax.legend()
fig.tight_layout()
fig.savefig(os.path.join(OUT, 'fig3_d_entropy.png'), dpi=DPI)
plt.close(fig)
print(f"fig3 done (unique {uniq}, log2 = {h2e:.2f})")

# ---------- fig 4: entropy vs k ----------
ks = [64, 128, 256, 512, 1024]
H2 = [8.61, 9.04, 9.59, 10.05, 10.55]
H2ci = [0.103, 0.156, 0.067, 0.098, 0.050]
Hinf = [7.22, 7.65, 8.07, 8.48, 8.89]
Hinfci = [0.103, 0.180, 0.083, 0.099, 0.075]
H1 = [8.97, 9.42, 9.95, 10.40, 10.87]
H1ci = [0.064, 0.098, 0.042, 0.063, 0.033]
fig, ax = plt.subplots(figsize=(7.5, 5))
ax.errorbar(ks, H1, yerr=H1ci, fmt='o-', color='#C44E52',
            label='Shannon entropy $H_1$ (mean of 20, 95% CI)')
ax.errorbar(ks, H2, yerr=H2ci, fmt='^-', color='#55A868',
            label='Rényi-2 entropy $H_2$ (mean of 20, 95% CI)')
ax.errorbar(ks, Hinf, yerr=Hinfci, fmt='s--', color='#4C72B0',
            label=r'min-entropy $H_\infty$ (mean of 20, 95% CI)')
ax.axhline(128, color='gray', ls=':', label='128-bit security target')
kx = [1024 * (2 ** j) for j in range(1, 13)]
hy = [10.87 + 0.475 * j for j in range(1, 13)]
ax.plot(kx, hy, color='#C44E52', alpha=0.4, ls='--',
        label='extrapolation (mean slope +0.475 bit/doubling)')
ax.set_xscale('log', base=2)
_n = (6, 9, 12, 15, 18, 21)
ax.set_xticks([2 ** n for n in _n])
ax.set_xticklabels([f'$2^{{{n}}}$' for n in _n])
ax.annotate('extrapolation', xy=(kx[-1], hy[-1]), xytext=(1.2e6, 10.3),
            fontsize=9, color='#C44E52', ha='center',
            arrowprops=dict(arrowstyle='->', color='#C44E52', alpha=0.7, lw=1.4))
ax.set_xlabel('security parameter k (bit length of starting values, log scale)')
ax.set_ylabel('entropy (bit)')
ax.set_title('Distance entropy vs k: five measured points (mean of 20) + mean-slope extrapolation\n'
             '(128 bits would need k ~ $2^{257}$; min-entropy convention ~ $2^{295}$)')
ax.legend(loc='upper left', fontsize=8)
ax.grid(True, alpha=0.3)
fig.tight_layout()
fig.savefig(os.path.join(OUT, 'fig4_entropy_vs_k.png'), dpi=DPI)
plt.close(fig)
print("fig4 done")
