# JSP-000404 / Erdős 504 研究仓库

**状态：原题尚未解决，当前成果不具备完整申奖条件。**

本仓库由 Jackie1021 发起，使用 OpenAI Codex 协助研究、编程及验证。
数学背景、前人成果与 AI 协作方式见 [贡献说明](ATTRIBUTION.md)。

现有成果包括四中心方向模型中的两条容量界（覆盖所有整数 n≥3）、
一个容量为 10 的模型实例，以及原题完整结论的六项等价完成条件。
模型定理尚未与任意点数的真实平面配置完整连接。

当前核心目标是证明两组对所有 m≥2 成立的下界：

1. 任意 2^m+1 个互异平面点，都有角≥π(1−2/(2m+1))。
2. 任意 2^m+2^(m−2)+1 个互异平面点，都有角≥π(1−1/(m+1))。

两组全参数上界构造及 N=3、4 的基础情形也尚未接入完整证明。
公开提交研究代码不等于完成原题，不会自动取得完整成果的优先权。

编译使用 Lean 4.33.0 和锁定的 Mathlib 版本：

```sh
cd project
lake exe cache get Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine Mathlib.Analysis.InnerProductSpace.PiL2 Mathlib.Tactic
lake build
lake env lean Audit.lean
lake env lean FourCenterAudit.lean
lake env lean CompletionContract.lean
```

实验使用 Z3 时，Z3 仅用于探索；SAT/UNSAT 输出不能替代 Lean 证明。
没有向奖项官方提交新的申请。
