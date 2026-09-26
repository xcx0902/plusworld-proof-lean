-- Model.lean: PLUSworld 问题的基本模型
-- 对应 problem.md 的形式化以及 editorial.md 第一段的记号约定
--
-- 说明：题目使用 1..n 编号，本形式化使用 0..n-1（0-indexed）。
--  Correspondence: 题目编号 i (1-indexed) 对应本文件 i-1。
--  条件 i ≤ tgt_i 在两种编号下形式相同（同时减一）。
--  值域为 [0, n)，操作1要求 a_x + 1 < n（对应题目 a_p < n）。
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-- PLUSworld 实例：n, 初始数组 src, 目标数组 tgt，以及题目保证的基本约束。 -/
structure PWInstance where
  n : ℕ
  src : ℕ → ℕ
  tgt : ℕ → ℕ
  hsrc_lt : ∀ i : ℕ, i < n → src i < n
  htgt_lt : ∀ i : ℕ, i < n → tgt i < n
  htgt_ge : ∀ i : ℕ, i < n → i ≤ tgt i
  hsrc_le_tgt : ∀ i : ℕ, i < n → src i ≤ tgt i

namespace PWInstance

variable (I : PWInstance)

/-- 初始未完成位置：src_i < tgt_i（editorial 记号 α_i < b_i）。 -/
def InitIncomplete (i : ℕ) : Prop :=
  i < I.n ∧ I.src i < I.tgt i

/-- 当前数组 a 下的未完成位置：a_i < tgt_i。 -/
def Incomplete (a : ℕ → ℕ) (i : ℕ) : Prop :=
  i < I.n ∧ a i < I.tgt i

/-- 已完成位置：a_i = tgt_i（在 ValidState 下等价于 ¬Incomplete）。 -/
def Completed (a : ℕ → ℕ) (i : ℕ) : Prop :=
  i < I.n ∧ a i = I.tgt i

/-- 证明用图 G 的边：i 向整个区间 [src_i, tgt_i] 连边（editorial “所有可能移动构成的图”）。 -/
def Edge (i j : ℕ) : Prop :=
  i < I.n ∧ j < I.n ∧ I.src i ≤ j ∧ j ≤ I.tgt i

/-- 图中的可达关系。 -/
def Reach (i j : ℕ) : Prop :=
  Relation.ReflTransGen I.Edge i j

/-- 强连通：互相可达。缩点后为 DAG。 -/
def SCC (i j : ℕ) : Prop :=
  I.Reach i j ∧ I.Reach j i

/-- 有效状态：src ≤ a ≤ tgt（逐点，i < n 时）。 -/
def ValidState (a : ℕ → ℕ) : Prop :=
  ∀ i, i < I.n → I.src i ≤ a i ∧ a i ≤ I.tgt i

/-- Bessie 的两种操作对应的单步转移（problem.md 操作1/2）。 -/
inductive Step : (ℕ → ℕ) × ℕ → (ℕ → ℕ) × ℕ → Prop where
  | incr {a x} : x < I.n → a x + 1 < I.n → Step (a, x) (Function.update a x (a x + 1), x)
  | move {a x} : x < I.n → a x < I.n → Step (a, x) (a, a x)

/-- 可解性：存在起点与操作序列使最终数组等于 tgt。 -/
def Solvable : Prop :=
  ∃ start, start < I.n ∧ ∃ a' p',
    Relation.ReflTransGen I.Step (I.src, start) (a', p') ∧ ∀ i, i < I.n → a' i = I.tgt i

-- ===== 基础引理 =====

theorem edge_bounds {i j : ℕ} (h : I.Edge i j) : i < I.n ∧ j < I.n :=
  ⟨h.1, h.2.1⟩

theorem edge_mem {i j : ℕ} (h : I.Edge i j) : I.src i ≤ j ∧ j ≤ I.tgt i :=
  ⟨h.2.2.1, h.2.2.2⟩

/-- 目标边恒在图中：i → tgt_i（因 src_i ≤ tgt_i）。 -/
theorem edge_target (i : ℕ) (hi : i < I.n) : I.Edge i (I.tgt i) :=
  ⟨hi, I.htgt_lt i hi, I.hsrc_le_tgt i hi, le_rfl⟩

/-- editorial 核心算术事实：若 r → z 是边且 z ≤ u ≤ tgt_r，则 r → u 也是边。
    用于性质二的 crossing（含 r > u > z 蕴含 r → u）与“不会提前离开”一节。 -/
theorem crossing_edge {r z u : ℕ} (h : I.Edge r z)
    (hle1 : z ≤ u) (hle2 : u ≤ I.tgt r) : I.Edge r u := by
  obtain ⟨hr, _hz, hsrc, _hb⟩ := h
  have htgt_lt : I.tgt r < I.n := I.htgt_lt r hr
  have hu : u < I.n := lt_of_le_of_lt hle2 htgt_lt
  exact ⟨hr, hu, le_trans hsrc hle1, hle2⟩

/-- editorial 式 src_r ≤ z < u < r ≤ tgt_r 蕴含 r → u（性质二反设中的关键一步）。 -/
theorem crossing_edge_of_lt {r z u : ℕ} (h : I.Edge r z)
    (hzu : z < u) (hur : u < r) (hrb : r ≤ I.tgt r) : I.Edge r u := by
  apply I.crossing_edge h (le_of_lt hzu)
  exact le_trans (le_of_lt hur) hrb

/-- 初始已完成点在 G 中只有一条出边：指向 tgt_i（= src_i）。 -/
theorem completed_edge_unique {i j : ℕ} (_hi : i < I.n)
    (heq : I.src i = I.tgt i) (h : I.Edge i j) : j = I.tgt i := by
  obtain ⟨_, _, hsrc, htgt⟩ := h
  omega

/-- 初始已完成点的出边目标不小于自身（因 tgt_i ≥ i），故“经过已完成点编号不下降”。 -/
theorem completed_edge_ge {i j : ℕ} (hi : i < I.n)
    (heq : I.src i = I.tgt i) (h : I.Edge i j) : i ≤ j := by
  have hj := I.completed_edge_unique hi heq h
  rw [hj]
  exact I.htgt_ge i hi

/-- SCC 自反。 -/
theorem scc_refl (i : ℕ) : I.SCC i i :=
  ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

/-- SCC 对称。 -/
theorem scc_symm {i j : ℕ} (h : I.SCC i j) : I.SCC j i :=
  ⟨h.2, h.1⟩

/-- SCC 传递。 -/
theorem scc_trans {i j k : ℕ} (h1 : I.SCC i j) (h2 : I.SCC j k) : I.SCC i k :=
  ⟨Relation.ReflTransGen.trans h1.1 h2.1,
   Relation.ReflTransGen.trans h2.2 h1.2⟩

/-- 单边给出可达。 -/
theorem reach_of_edge {i j : ℕ} (h : I.Edge i j) : I.Reach i j :=
  Relation.ReflTransGen.single h

/-- 可达传递。 -/
theorem reach_trans {i j k : ℕ} (h1 : I.Reach i j) (h2 : I.Reach j k) : I.Reach i k :=
  Relation.ReflTransGen.trans h1 h2

/-- 缩点 DAG 性质：一旦沿边离开所在强连通分量，就再也不能回来
    （editorial：“一旦离开某个分量，就再也不能回来”）。 -/
theorem scc_no_return {x y z : ℕ} (hxy : I.SCC x y) (hyz : I.Edge y z)
    (hret : I.Reach z x) : I.SCC x z := by
  constructor
  · exact Relation.ReflTransGen.trans hxy.1 (Relation.ReflTransGen.single hyz)
  · exact hret

/-- 上述的逆否：若 z 与 x 不在同一分量，则从 y 出边到 z 后无法回到 x。 -/
theorem scc_no_return' {x y z : ℕ} (hxy : I.SCC x y) (hyz : I.Edge y z)
    (hneg : ¬ I.SCC x z) : ¬ I.Reach z x := by
  intro hret
  exact hneg (I.scc_no_return hxy hyz hret)

/-- ValidState 蕴含值域 < n。 -/
theorem valid_lt {a : ℕ → ℕ} (hv : I.ValidState a) {i : ℕ} (hi : i < I.n) :
    a i < I.n := by
  have ⟨_, hle⟩ := hv i hi
  exact lt_of_le_of_lt hle (I.htgt_lt i hi)

/-- 初始数组自身有效。 -/
theorem valid_init : I.ValidState I.src := fun i hi => ⟨le_rfl, I.hsrc_le_tgt i hi⟩

/-- 在 ValidState 下 Completed ↔ ¬Incomplete（i < n 时）。 -/
theorem completed_iff_not_incomplete {a : ℕ → ℕ} (hv : I.ValidState a)
    {i : ℕ} (hi : i < I.n) : I.Completed a i ↔ ¬ I.Incomplete a i := by
  constructor
  · rintro ⟨_, heq⟩ ⟨_, hlt⟩
    omega
  · intro h
    have ⟨_, hle⟩ := hv i hi
    have h_not_lt : ¬ a i < I.tgt i := fun hlt => h ⟨hi, hlt⟩
    constructor
    · exact hi
    · omega

/-- Step 单调：数组逐点不减（操作1加一，操作2不动）。 -/
theorem step_mono {s t : (ℕ → ℕ) × ℕ} (h : I.Step s t) :
    ∀ i, s.1 i ≤ t.1 i := by
  cases h with
  | @incr a x hx _ =>
    intro i
    by_cases heq : i = x
    · subst heq
      simp only
      rw [Function.update_self]
      omega
    · simp only
      rw [Function.update_of_ne heq]
  | @move a x =>
    intro i
    exact le_rfl

/-- 多步单调。 -/
theorem reach_mono {s t : (ℕ → ℕ) × ℕ}
    (h : Relation.ReflTransGen I.Step s t) : ∀ i, s.1 i ≤ t.1 i := by
  induction h with
  | refl => intro i; exact le_rfl
  | tail _ hstep ih =>
    intro i
    exact le_trans (ih i) (I.step_mono hstep i)

/-- Step 可达的位置始终 < n。 -/
theorem step_pos_lt {s t : (ℕ → ℕ) × ℕ}
    (h : Relation.ReflTransGen I.Step s t) (hs : s.2 < I.n) : t.2 < I.n := by
  induction h with
  | refl => exact hs
  | tail _ hstep ih =>
    cases hstep with
    | @incr a x hx _ => exact ih
    | @move a x _ hlt => exact hlt

end PWInstance
