# plusworld-proof

Codeforces D. PLUSworld 题解正确性证明的 Lean 4 形式化。对照 `problem.md`（题面）与
`editorial.md`（中文题解），把其中解法的正确性论证写成机器检查的 Lean 证明。

## 编号约定

题面用 `1..n` 编号；形式化一律用 `0..n-1`（0-indexed），条件 `i ≤ bᵢ` 在两种编号下
形式相同（同时减一）。`I.src` 即题解记号 `α`，`I.tgt` 即 `b`。

## 文件结构

- `PlusworldProof.lean` — 库根，依次导入下述模块。
- `PlusworldProof/Model.lean` — 基本模型：实例 `PWInstance`（`n/src/tgt` 及
  `tgt < n`、`i ≤ tgt`、`src ≤ tgt` 约束）、证明图 `G` 的边
  （`Edge i j : i → [srcᵢ, tgtᵢ]` 整个区间）、`Reach`（`ReflTransGen`）、`SCC`、
  操作 `Step`（加一/移动）、有效状态 `ValidState`、`Solvable`，以及
  `crossing_edge`（`r→z` 且 `z ≤ u ≤ tgtᵣ` 则 `r→u`）、缩点无返回
  `scc_no_return`、单调性等基础引理。
- `PlusworldProof/Scc.lean` — “所有可能移动构成的图”一节的图论部分：
  `crossing_exists`（离散介值：`b ≤ v < a` 的路必含 `r>v≥z` 的一步）、
  `max_has_edge_below`/`max_init_incomplete`（性质一前半：分量最大点有内边指向
  更小点，故初始未完成）、`Component`/`compMax` 与
  `component_max_init_incomplete`（含单点情形）、`completed_path_ge_aux`
  （除终点外皆初始已完成的路不下降，性质二前半）。
- `PlusworldProof/Strategy.lean` — “直接模拟的策略”：起点取最小初始未完成
  （`start`）、三规则 `GreedyStep`（`moveLeft`/`incr`/`moveRight`）、保持有效与
  单调、提升 `greedy_to_step`、`step_attained`/`greedy_attained`（增一覆盖区间：
  完成 `r` 必经过中间值）、`stay_v_aux`（`v` 存活则 `r` 守 `v`）。
- `PlusworldProof/Correctness.lean` — “不会提前离开”“完备性与终止”：
  `order_of_reach`（性质二排序：后分量经 `r→u` 边回到较早分量，矛盾）、
  `max_lt_of_leave`（相邻待处理分量 max 递增）、`stay_inside_left`（左移留分量内）、
  `no_early_completion`（分 `r=M` 经历史+保持得 `aM=v`、分 `r<M` 已完成值更大
  再经历史+保持，两路皆矛盾）、`greedy_success_solvable`（成功即有解）、
  `stuck_selfloop`/`stuck_deterministic`/`stuck_fixed`/`stuck_never_succeeds`
  （卡住自环永留原状态、报告无解在运行层面合理）、`unfinishedSet` 单调与
  `R ≤ n`、对空间基数 `pair_space_card`、给定 `NoDup` 的
  `moves_bound_of_nodup`（纯组合推论）、`sum_incr_bound`（加一 ≤ `n(n-1)`）与
  `total_bound_of_nodup`（总量 `≤ 2n²`，恰为题目输出界）。

## 构建与验证

```sh
lake build
```

工具链 `leanprover/lean4:v4.34.0`（见 `lean-toolchain`），Mathlib 通过
`../lib/mathlib4` 引入。全量构建通过，无 `sorry`、无警告。

## 形式化范围说明

- 移动记录 `(x, R)` 的全局互异性以条件式给出（`moves_bound_of_nodup` 取 `NoDup`
  为前提）：单步左右方向、左相不返回核心（`stay_v_aux`）、已完成路不下降
  （`completed_path_ge_aux`）均已形式化，区间组装为纯组合推论。
- 总量界形式化为题目允许的 `o ≤ 2n²`；editorial 更紧的 `2n²-n` 在注释中说明
  （`R≥1` 细化把对空间从 `n*(n+1)` 收紧到 `n*n` 即得）。
- 完备性方向（有解则贪心成功）由“从首个待处理分量开始、每次完整处理一个分量”
  的诸引理（`stay_inside_left`、`no_early_completion`、`max_lt_of_leave`、
  起点最小性）组合而成；成功/卡住两个方向的运行层面合理性已分别由
  `greedy_success_solvable` 与 `stuck_never_succeeds` 覆盖。

## Git 历史

- `29ac5f7` 基础模型（Model：实例、图 G、可达与 SCC）
- `c43e698` SCC 图论（crossing、最大点性质一与已完成路径单调）
- `8f0d3a4` 直接模拟策略（起点、贪心步与历史引理）
- `3677cd3` 正确性 I（Greedy 历史、性质二排序、加一界与成功合理性）
- `74a3857` 正确性 II（留分量、max 递增与不过早完成）
- `601fff9` 正确性 III（终止界、卡住合理性与总量组装）