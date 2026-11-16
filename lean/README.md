# Lean 4 形式化

本目录机器验证论文中**无条件**层的结果。稿件本身不在本仓库。

| 目录 | 内容 | 依赖 |
|---|---|---|
| `core/` | §2.4 四条命题、障碍一（§3.1）、定理 1 的正确性 | 无（仅 Lean 4.32.2，`lean-toolchain` 已钉版本） |
| `guess/` | 定理 3（猜测成本恒等式）的代数部分 | Mathlib，commit 见 `guess/lakefile.toml` |

## 验证方法

`core/` 零依赖：

```
cd core
lake build          # 或：lean Collatz.lean
```

预期：0 error、0 warning；19 行 `#print axioms`，每条的公理集为
`[propext, Quot.sound]` 或 `[propext, Classical.choice, Quot.sound]`。

`guess/` 需要联网获取 Mathlib（版本已钉）：

```
cd guess
lake exe cache get && lake build
```

预期：0 error；3 条 `#print axioms` 均为
`[propext, Classical.choice, Quot.sound]`，输出应逐字等于 `guess/AXIOMS.txt`。

## 核查要点

- **无 `sorry`**：`grep -rnE '\bsorry\b|\badmit\b|^axiom ' core guess` 应无匹配；
- **陈述对应**：每个目录的 `README.md` 有"论文命题 → Lean 名字"的对照表；
- **已知边界**：几何期望 `E[Geom(p)] = 1/p` 未形式化（论文只使用该期望给出的恒等式，
  不使用其推导）；`H_inf` 作为对数未形式化；全部条件性、实测性结论均不在形式化范围内。

## 说明

`guess/build.sh` 与 `guess/lake-verify.sh` 是作者机器上的离线辅助脚本
（借用本地已编译的 Mathlib）。正常验证请用 `lake exe cache get && lake build`。
