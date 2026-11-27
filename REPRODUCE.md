# Reproducing the numbers in the paper

This repository holds the attack code, the measurement scripts, their outputs, and the
Lean development. The manuscript sources and PDFs are **not** included.

Every quantitative claim in the paper traces to a script and an output file below.
Scripts use the Python standard library only, except `paper/figures/make_figures.py`
(matplotlib). Seeds are fixed, so runs are deterministic up to timing fields.

## 1. Environment

| For | Need |
|---|---|
| attack and measurement scripts | Python ≥ 3.10 (CPython 3.13 / Windows 10 was the test bed) |
| `paper/figures/make_figures.py` | matplotlib, plus a CJK font (default `SimHei`) |
| `lean/core` | Lean 4.32.2 — `lean-toolchain` pins it, `elan` fetches it |
| `lean/guess` | Lean 4.32.2 **and** Mathlib (pinned in `lean/guess/lakefile.toml` and `lean/guess/lake-manifest.json`) |

## 2. Running everything

```
cd paper && python repro_run_all.py        # about 30 minutes; writes paper/repro_check_all.txt
```

The entropy re-measurement inside that runner is the fast setting ($k=64$, 20 repeats);
the full five-point results are the committed `paper/entropy_rep_{A,B,C}.csv`.

## 3. Claim map: paper statement → script → output → what to read

| Paper | Script | Output | What to read |
|---|---|---|---|
| 100 instances (five $k$), median 1 draw, 90th pct 12, max 89 | `attacks/round12_bitlen_cyclekill.py` | `attacks/round12_out.txt` | per-$k$ lines plus the summary line; seeds are `20261004+k`, 20 instances per $k$ |
| End-to-end forgery cost, $L=4/16/64/256$ | `attacks/round9_lamport_scaling.py` | `attacks/round9_out.txt` | 2,543 / 6,994 / 118,077 / 189,758 trajectory computations; $L=256$ in 28.2 s |
| Repetition statistics for the same runs | `attacks/round9b_repeat_stats.py`, `attacks/round9c_repeat_stats.py` | `attacks/round9b_out.txt`, `attacks/round9c_out.txt` | per-instance means and maxima |
| Table 1: entropy and $\hat U_k$ at five $k$ | `paper/entropy_replication.py` | `paper/entropy_rep_{A,B,C}.csv` | columns `k,rep,N,U,Hinf,H2,H1`; $k=64,128,256$ in A, 512 in B, 1024 in C; 20 repeats each; the paper quotes the means |
| Fig. 4 (entropy vs $k$) | `paper/figures/make_figures.py` | `paper/figures/fig4_entropy_vs_k.png` | regenerated from the CSVs above |
| Fig. 3 (distance entropy) | `paper/estimate_min_entropy.py`, `paper/estimate_min_entropy_large.py` | stdout, then `paper/figures/make_figures.py` | sample count, distinct distances, entropy estimate |
| Support counts vs $N$ (the saturation study) | `attacks/u_k_support.py` | `attacks/u_k_support.json` | at $k=64$ and $N=10^3\ldots1.6\times10^4$: 452 / 588 / 685 / 773 / 856 |
| Saturation at $k=64$ up to $N=2\times10^5$ | `attacks/u_k64_saturation.py` | `attacks/u_k64_saturation.json` | marginal 814 → 930 → 994 → 1,068 → 1,107; fixed-$m$ 963 / 965 / 965 at $N=5\times10^4$ |
| Three independent instances at $N=10^5$ | `attacks/u_k64_n100k.py` | `attacks/u_k64_n100k.json` | 1,011 / 1,032 / 1,023 (mean 1,022 against the withdrawn bound 1,024) |
| Meeting-height calibration grid | `attacks/round10_meeting_bound.py`, `attacks/analyze_round10.py` | `attacks/round10_out.txt` | per-$k$ grid of $\Pr[z\ge V]$, expected distinct count, tail supremum |
| Design-space exhaustion at $k=20$ | `attacks/round1_k20_full.py` | stdout | exhaustive enumeration over the design space |
| `thm:cyclekill` (step-count collapse) | `attacks/round1_h5_cyclekill.py`, `attacks/round12_bitlen_cyclekill.py` | `attacks/round12_out.txt` | no admissible $(s,t)$ survives the bit-length guard |
| Lemma 3 coverage and the Remark 1 retries | `paper/verify_rem_condition.py` | stdout | sum coverage over 2000 random pairs: 0 counterexamples; 30/30 instances satisfy `rem >= 0`; retries `min=1, max=1, mean=1.0` |
| Theorem 1 margin check | `attacks/verify_n6_margin.py` | `attacks/verify_n6_margin_out.txt` | the stated margin holds at the tested sizes |
| Audits of three published schemes | `attacks/round11_audit_{owf,pow,prng}.py` | stdout | each scheme broken as described in Appendix B |
| Distribution of $m=\lvert a-b\rvert$ | `paper/check_m_distribution.py` | `paper/m_distribution_check.csv`, `paper/m_range_check.csv` | KS comparison and quantised TV; extreme-interval probabilities for (C4) |
| Role coverage and $S_{\min}$ | `paper/verify_rem_condition.py` | stdout | mod-3 coverage lemma and the $S_{\min}$ condition |
| Unmeasured items | `paper/audit_nonmeasured.py` | stdout | half-compressed step counts, window frequencies |
| Lean, core layer | `lean/core/Collatz.lean` | `#print axioms` | 20 lines, no `sorryAx` |
| Lean, algebra layer | `lean/guess/Guess.lean` | `#print axioms` | 3 theorems, `[propext, Classical.choice, Quot.sound]` |
| Definition fidelity | `lean/core/DefCheck.lean` | stdout | five checks, each `true` |
| Figures 1–4 | `paper/figures/make_figures.py` | `paper/figures/*.png` | regenerated from committed data |

Figures 1 and 2 of the manuscript (architecture schematic and a worked trajectory example)
are drawings, not script output; they are not in this repository.

## 4. Integrity

Timing fields make byte-level MD5 unstable for a few outputs. Use the normaliser:

```
python normalize_outputs.py --check      # verifies the 11 txt/csv outputs numerically
python normalize_outputs.py --diff       # locates the first differing line (needs git)
```

`md5sums.txt` is the raw snapshot (timing fields included); `md5sums_numeric.txt` is the
normalised one.

## 5. Conventions that matter when comparing

- **Support counts are lower bounds.** $\hat U_k(N)$ counts the distinct values seen in
  $N$ samples; it is monotone in $N$ and was still rising at the largest $N$ tried
  (1,107 at $N=2\times10^5$, $k=64$). The paper reports these readings as lower bounds,
  so the attack cost it quotes is a lower bound too.
- **The growth bound on $U_k$ is an assumption, not a measurement.** The paper assumes
  $U_k\le C_2k^{\alpha}$ with $\alpha<1$ and withdraws the specific constants
  $(1/2,2^7)$: at $k=64$ the three-instance mean is 1,022 against the bound 1,024 — a
  margin of 0.2% that shrinks with $N$. Sampling can falsify such a bound, never confirm it.
- **Termination is measured, not proved.** The forgery algorithm's correctness (every
  output satisfies the verification predicate) is proved and machine-checked; that it
  returns for every $k$ within a bounded number of draws rests on measurement.

**Historical snapshots.** The authors' working repository keeps about ninety `tex/manuscript_v*_review.tex` snapshots. They predate the five-point protocol (added with `k=512`) and are kept only as version history; the numbers in this package and in the manuscript are those of `attacks/round12_out.txt`.

## 6. Not included

- Manuscript sources and PDFs (author's copy).
- Build products (`*.aux`, `*.log`, PDFs).
- The two schematic figures (1 and 2).
