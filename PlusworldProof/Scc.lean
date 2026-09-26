-- Scc.lean: 强连通分量与区间边性质
-- 对应 editorial.md “所有可能移动构成的图”一节的图论部分：
-- 缩点 DAG、无返回、crossing（r→z 蕴含 r→u）、最大点的性质一前半。
import PlusworldProof.Model

namespace PWInstance

variable (I : PWInstance)

/-- 可达目标仍在范围内：M < n 且 Reach M v 蕴含 v < n。 -/
theorem reach_target_lt {M v : ℕ} (hM : M < I.n) (h : I.Reach M v) : v < I.n := by
  induction h with
  | refl => exact hM
  | tail _ hEdge ih =>
    obtain ⟨_, hj, _, _⟩ := hEdge
    exact hj

/-- 阈值 crossing：从 a 到 b 的路（b ≤ v < a）必含一步 r→z 使 r > v ≥ z。
    editorial 性质二反设与“不会提前离开”一节共用的离散介值论证。 -/
theorem crossing_exists {a b v : ℕ} (hab : I.Reach a b)
    (hle1 : b ≤ v) (hle2 : v < a) :
    ∃ r z, I.Edge r z ∧ I.Reach a r ∧ I.Reach z b ∧ v < r ∧ z ≤ v := by
  induction hab using Relation.ReflTransGen.head_induction_on with
  | refl => omega
  | @head a2 c hEdge hTail ih =>
    by_cases hle : c ≤ v
    · exact ⟨a2, c, hEdge, Relation.ReflTransGen.refl, hTail, by omega, hle⟩
    · have hgt : v < c := by omega
      obtain ⟨r, z, hrEdge, hrReach, hzReach, hrgt, hzle⟩ := ih hgt
      exact ⟨r, z, hrEdge,
        Relation.ReflTransGen.trans (Relation.ReflTransGen.single hEdge) hrReach,
        hzReach, hrgt, hzle⟩

/-- 性质一前半的归纳辅助引理：将起点泛化，使 head 归纳的 motive 包含全部起点相关假设。 -/
theorem max_has_edge_below_aux {y a : ℕ} (hR : I.Reach a y) :
    a < I.n → I.Reach y a → y < a → (∀ z, I.SCC a z → z ≤ a) →
    ∃ z, z < a ∧ I.Edge a z := by
  induction hR using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro _ _ hlt _
    omega
  | @head a2 c hEdge hTail ih =>
    intro hM hBack hlt hmax
    have hc_lt : c < I.n := hEdge.2.1
    have hReach_a2c : I.Reach a2 c := Relation.ReflTransGen.single hEdge
    have hReach_c_a2 : I.Reach c a2 := Relation.ReflTransGen.trans hTail hBack
    have hscc_a2c : I.SCC a2 c := ⟨hReach_a2c, hReach_c_a2⟩
    have hc_le : c ≤ a2 := hmax c hscc_a2c
    by_cases h : c < a2
    · exact ⟨c, h, hEdge⟩
    · have heq : c = a2 := by omega
      subst heq
      exact ih hc_lt hBack hlt hmax

/-- 性质一前半（图论核心）：若 M 为其 SCC 的最大点，且 SCC 内含更小点 y，
    则 M 有一条指向更小区间的边，从而 src_M < M（结合 M ≤ tgt_M 得 M 初始未完成）。
    editorial：“M 必须能沿分量内部的路径到达更小的点，所以从 M 出发必有一条内部边指向更小的点”。 -/
theorem max_has_edge_below {M y : ℕ} (hM : M < I.n) (hscc : I.SCC M y) :
    y < M → (∀ z, I.SCC M z → z ≤ M) → ∃ z, z < M ∧ I.Edge M z := by
  intro hlt hmax
  exact I.max_has_edge_below_aux hscc.1 hM hscc.2 hlt hmax

/-- 由上直接得 M 初始未完成（src_M ≤ z < M ≤ tgt_M）。 -/
theorem max_init_incomplete {M y : ℕ} (hM : M < I.n) (hscc : I.SCC M y)
    (hlt : y < M) (hmax : ∀ z, I.SCC M z → z ≤ M) : I.InitIncomplete M := by
  obtain ⟨z, hzm, hEdge⟩ := I.max_has_edge_below hM hscc hlt hmax
  obtain ⟨_, _, hsrc_le, _⟩ := hEdge
  have hMle : M ≤ I.tgt M := I.htgt_ge M hM
  exact ⟨hM, by omega⟩

/-- 分量（Finset）：与 i 强连通且 < n 的点集。实际算法不必建图，仅为证明所用。 -/
noncomputable def Component (i : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range I.n).filter (fun j => I.SCC i j)

theorem mem_component_iff {i j : ℕ} : j ∈ I.Component i ↔ j < I.n ∧ I.SCC i j := by
  unfold Component
  simp only [Finset.mem_filter, Finset.mem_range]

theorem self_mem_component {i : ℕ} (hi : i < I.n) : i ∈ I.Component i :=
  (I.mem_component_iff).mpr ⟨hi, I.scc_refl i⟩

theorem component_nonempty {i : ℕ} (hi : i < I.n) : (I.Component i).Nonempty :=
  ⟨i, I.self_mem_component hi⟩

/-- 分量最大点（M = max C，editorial 记号）。 -/
noncomputable def compMax (i : ℕ) (hi : i < I.n) : ℕ :=
  (I.Component i).max' (I.component_nonempty hi)

theorem compMax_mem {i : ℕ} (hi : i < I.n) : I.compMax i hi ∈ I.Component i :=
  Finset.max'_mem _ _

theorem compMax_le {i : ℕ} (hi : i < I.n) {x : ℕ} (hx : x ∈ I.Component i) :
    x ≤ I.compMax i hi :=
  Finset.le_max' _ _ hx

theorem compMax_lt {i : ℕ} (hi : i < I.n) : I.compMax i hi < I.n := by
  have hmem := I.compMax_mem hi
  have hiff := (I.mem_component_iff).mp hmem
  exact hiff.1

theorem compMax_scc {i : ℕ} (hi : i < I.n) : I.SCC i (I.compMax i hi) := by
  have hmem := I.compMax_mem hi
  exact ((I.mem_component_iff).mp hmem).2

/-- 分量最大点的最大性：任何与 M 同分量的 z 皆 ≤ M。 -/
theorem compMax_is_max {i : ℕ} (hi : i < I.n) :
    ∀ z, I.SCC (I.compMax i hi) z → z ≤ I.compMax i hi := by
  intro z hz
  have hMi : I.SCC i (I.compMax i hi) := I.compMax_scc hi
  have hiz : I.SCC i z := I.scc_trans hMi hz
  have hz_lt : z < I.n := I.reach_target_lt hi hiz.1
  have hmem : z ∈ I.Component i := (I.mem_component_iff).mpr ⟨hz_lt, hiz⟩
  exact I.compMax_le hi hmem

/-- 性质一（含单点情形）：含初始未完成点的分量，其最大点 M 必初始未完成。
    editorial 性质一：“M 是初始未完成位置”。单点时由定义成立；
    非单点时由 max_init_incomplete（内部边指向更小点）得到。 -/
theorem component_max_init_incomplete {i : ℕ} (hi : i < I.n)
    {y : ℕ} (hy_mem : y ∈ I.Component i) (hy_inc : I.InitIncomplete y) :
    I.InitIncomplete (I.compMax i hi) := by
  have hy_scc : I.SCC i y := ((I.mem_component_iff).mp hy_mem).2
  have hM_scc : I.SCC i (I.compMax i hi) := I.compMax_scc hi
  have hMy : I.SCC (I.compMax i hi) y :=
    I.scc_trans (I.scc_symm hM_scc) hy_scc
  have hy_le : y ≤ I.compMax i hi := I.compMax_le hi hy_mem
  have hM_lt : I.compMax i hi < I.n := I.compMax_lt hi
  by_cases heq : y = I.compMax i hi
  · subst heq
    exact hy_inc
  · have hlt : y < I.compMax i hi := by omega
    exact I.max_init_incomplete hM_lt hMy hlt (I.compMax_is_max hi)

/-- 已完成路径单调：若 a 到 b 的路上除终点外皆初始已完成，则 a ≤ b。
    editorial 性质二前半：“在进入下一个待处理分量之前，经过的点都初始已完成，
    它们只有指向不小于自身的位置的边，所以编号不会下降”。 -/
theorem completed_path_ge_aux {b a : ℕ} (hab : I.Reach a b) :
    (∀ z, I.Reach a z → I.Reach z b → z ≠ b → I.src z = I.tgt z) → a ≤ b := by
  induction hab using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro _
    exact le_rfl
  | @head a2 c hEdge hTail ih =>
    intro hcomp
    by_cases heq : a2 = b
    · omega
    · have hsrc_eq : I.src a2 = I.tgt a2 := by
        apply hcomp a2 Relation.ReflTransGen.refl
        · exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hEdge) hTail
        · exact heq
      have ha2_lt : a2 < I.n := hEdge.1
      have hac : a2 ≤ c := I.completed_edge_ge ha2_lt hsrc_eq hEdge
      have hcomp_c : ∀ z, I.Reach c z → I.Reach z b → z ≠ b → I.src z = I.tgt z := by
        intro z hz1 hz2 hne
        apply hcomp z
        · exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hEdge) hz1
        · exact hz2
        · exact hne
      have hcb : c ≤ b := ih hcomp_c
      omega

end PWInstance
