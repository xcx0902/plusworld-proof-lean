-- Strategy.lean: 直接模拟策略的形式化
-- 对应 editorial.md “直接模拟的策略”一节：
-- 从最小编号初始未完成位置开始；未完成且 a_x<x 且 a_x 未完成则左移，
-- 未完成否则加一；已完成则沿最终边右移。全部完成成功，卡在自环则报告无解。
import PlusworldProof.Model
import PlusworldProof.Scc

namespace PWInstance

variable (I : PWInstance)

/-- 起点：最小初始未完成位置；若无则为 0（对应 editorial 无未完成时选 1，即 0-indexed 0）。 -/
noncomputable def start : ℕ :=
  open Classical in
  if h : ((Finset.range I.n).filter (fun i => I.src i < I.tgt i)).Nonempty then ((Finset.range I.n).filter (fun i => I.src i < I.tgt i)).min' h else 0

theorem start_mem_of_exists {i : ℕ} (hi : i < I.n) (hinc : I.src i < I.tgt i) :
    I.start < I.n ∧ I.src I.start < I.tgt I.start ∧ ∀ j, j < I.n → I.src j < I.tgt j → I.start ≤ j := by
  have hS : i ∈ (Finset.range I.n).filter (fun k => I.src k < I.tgt k) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hi, hinc⟩
  have hne : ((Finset.range I.n).filter (fun k => I.src k < I.tgt k)).Nonempty :=
    ⟨i, hS⟩
  have hstart : I.start = ((Finset.range I.n).filter (fun k => I.src k < I.tgt k)).min' hne := by
    unfold start
    simp [hne]
  rw [hstart]
  have hmem := Finset.min'_mem _ hne
  simp only [Finset.mem_filter, Finset.mem_range] at hmem
  constructor
  · exact hmem.1
  · constructor
    · exact hmem.2
    · intro j hj hjinc
      have hjS : j ∈ (Finset.range I.n).filter (fun k => I.src k < I.tgt k) := by
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨hj, hjinc⟩
      exact Finset.min'_le _ _ hjS

theorem start_lt_of_exists {i : ℕ} (hi : i < I.n) (hinc : I.src i < I.tgt i) :
    I.start < I.n :=
  (I.start_mem_of_exists hi hinc).1

theorem start_init_incomplete {i : ℕ} (hi : i < I.n) (hinc : I.src i < I.tgt i) :
    I.InitIncomplete I.start :=
  let h := I.start_mem_of_exists hi hinc
  ⟨h.1, h.2.1⟩

theorem start_le_of_exists {i j : ℕ} (hi : i < I.n) (hinc : I.src i < I.tgt i)
    (hj : j < I.n) (hjinc : I.src j < I.tgt j) : I.start ≤ j :=
  (I.start_mem_of_exists hi hinc).2.2 j hj hjinc

/-- 贪心单步：editorial 三条规则的直接形式化。 -/
inductive GreedyStep : (ℕ → ℕ) × ℕ → (ℕ → ℕ) × ℕ → Prop where
  | moveLeft {a x} : x < I.n → a x < I.tgt x → a x < x →
      a (a x) < I.tgt (a x) → GreedyStep (a, x) (a, a x)
  | incr {a x} : x < I.n → a x < I.tgt x → a x + 1 < I.n →
      ¬ (a x < x ∧ a (a x) < I.tgt (a x)) → GreedyStep (a, x) (Function.update a x (a x + 1), x)
  | moveRight {a x} : x < I.n → a x = I.tgt x → GreedyStep (a, x) (a, I.tgt x)

/-- 贪心步皆为合法操作步（从而可用 Step 的单调、历史等引理）。 -/
theorem greedy_is_step {s t : (ℕ → ℕ) × ℕ} (h : I.GreedyStep s t) : I.Step s t := by
  cases h with
  | @moveLeft a x hx _ hlt _ =>
    have hlt_n : a x < I.n := lt_trans hlt hx
    exact Step.move hx hlt_n
  | @incr a x hx _ hbnd _ =>
    exact Step.incr hx hbnd
  | @moveRight a x hx heq =>
    have hlt : a x < I.n := by
      rw [heq]
      exact I.htgt_lt x hx
    exact heq ▸ Step.move hx hlt

/-- 贪心保持有效状态（加一只在未完成时加一，移动不改数组）。 -/
theorem greedy_preserves_valid {s t : (ℕ → ℕ) × ℕ} (hv : I.ValidState s.1)
    (h : I.GreedyStep s t) : I.ValidState t.1 := by
  cases h with
  | @moveLeft a x =>
    simpa only using hv
  | @incr a x hx hinc _ _ =>
    dsimp only at hv ⊢
    intro i hi
    by_cases heq : i = x
    · subst heq
      have ⟨hsrc_le, _hle⟩ := hv i hi
      simp only [Function.update_self]
      constructor
      · omega
      · omega
    · simp only [Function.update_of_ne heq]
      exact hv i hi
  | @moveRight a x =>
    simpa only using hv

/-- 多步贪心保持有效。 -/
theorem greedy_reach_valid {s t : (ℕ → ℕ) × ℕ}
    (hv : I.ValidState s.1) (h : Relation.ReflTransGen I.GreedyStep s t) :
    I.ValidState t.1 := by
  induction h with
  | refl => exact hv
  | tail _ hstep ih =>
    exact I.greedy_preserves_valid ih hstep

/-- 贪心存在且唯一分支：有效状态下当前位置必有恰一规则适用（除自环停滞外仍有 moveRight 自环步）。 -/
theorem greedy_exists {a : ℕ → ℕ} {x : ℕ} (hv : I.ValidState a) (hx : x < I.n) :
    ∃ t, I.GreedyStep (a, x) t := by
  by_cases hinc : a x < I.tgt x
  · by_cases hleft : a x < x ∧ a (a x) < I.tgt (a x)
    · obtain ⟨hlt, hinc2⟩ := hleft
      exact ⟨(a, a x), GreedyStep.moveLeft hx hinc hlt hinc2⟩
    · have hbnd : a x + 1 < I.n := by
        have htgt := I.htgt_lt x hx
        omega
      exact ⟨(Function.update a x (a x + 1), x), GreedyStep.incr hx hinc hbnd hleft⟩
  · have heq : a x = I.tgt x := by
      have ⟨_, hle⟩ := hv x hx
      omega
    exact ⟨(a, I.tgt x), GreedyStep.moveRight hx heq⟩

/-- 贪心左移为图边：src_x ≤ a_x < tgt_x（有效状态 + 未完成），且 a_x < n。 -/
theorem moveLeft_is_edge {a : ℕ → ℕ} {x : ℕ} (hv : I.ValidState a) (hx : x < I.n)
    (hinc : a x < I.tgt x) (_hlt : a x < x) : I.Edge x (a x) := by
  have ⟨hsrc_le, _⟩ := hv x hx
  have ha_lt : a x < I.n := lt_trans _hlt hx
  exact ⟨hx, ha_lt, hsrc_le, le_of_lt hinc⟩

/-- 贪心右移即目标边（恒在图中）。 -/
theorem moveRight_is_edge {x : ℕ} (hx : x < I.n) : I.Edge x (I.tgt x) :=
  I.edge_target x hx

/-- 操作历史引理：若从 s 出发经合法步到达 t，且 r 处严格增加，
    则 s_r 与 t_r 之间任一值 U 都曾在位置 r 处取到（增一覆盖区间）。
    用于“不会过早完成最大点”：完成 r 必经过同分量更小未完成点 v，
    此时贪心本应左移而非加一，矛盾。 -/
theorem step_attained {s t : (ℕ → ℕ) × ℕ}
    (h : Relation.ReflTransGen I.Step s t) {r U : ℕ}
    (hsrc_le : s.1 r ≤ U) (hU_le : U ≤ t.1 r) (hlt : s.1 r < t.1 r) :
    ∃ a_mid : ℕ → ℕ,
      Relation.ReflTransGen I.Step s (a_mid, r) ∧
      Relation.ReflTransGen I.Step (a_mid, r) t ∧ a_mid r = U := by
  induction h with
  | refl =>
    exact False.elim (lt_irrefl _ hlt)
  | tail htail hstep ih =>
    cases hstep with
    | @incr a_prev x hx hbnd =>
      by_cases heq_r : r = x
      · subst heq_r
        -- 此时 r = x（x 已被 r 替换），当前 t = (update a_prev r (_+1), r)
        have hU_le2 : U ≤ a_prev r + 1 := by
          have h1 : U ≤ (Function.update a_prev r (a_prev r + 1)) r := hU_le
          rwa [Function.update_self] at h1
        have hlt2 : s.1 r < a_prev r + 1 := by
          have h1 : s.1 r < (Function.update a_prev r (a_prev r + 1)) r := hlt
          rwa [Function.update_self] at h1
        by_cases heq_U : U = a_prev r + 1
        · refine ⟨Function.update a_prev r (a_prev r + 1), ?_, Relation.ReflTransGen.refl, ?_⟩
          · exact Relation.ReflTransGen.trans htail (Relation.ReflTransGen.single (Step.incr hx hbnd))
          · rw [Function.update_self]
            exact heq_U.symm
        · have hU_le_m : U ≤ a_prev r := by omega
          by_cases hlt_m : s.1 r < a_prev r
          · obtain ⟨a_mid, h1, h2, h3⟩ := ih hU_le_m hlt_m
            refine ⟨a_mid, h1, ?_, h3⟩
            exact Relation.ReflTransGen.trans h2 (Relation.ReflTransGen.single (Step.incr hx hbnd))
          · have heq_Um : U = a_prev r := by omega
            refine ⟨a_prev, htail, Relation.ReflTransGen.single (Step.incr hx hbnd), heq_Um.symm⟩
      · have hUpd : (Function.update a_prev x (a_prev x + 1)) r = a_prev r :=
          Function.update_of_ne heq_r _ _
        have hU_le_m : U ≤ a_prev r := by
          have h1 : U ≤ (Function.update a_prev x (a_prev x + 1)) r := by
            simpa only using hU_le
          rwa [hUpd] at h1
        have hlt_m : s.1 r < a_prev r := by
          have h1 : s.1 r < (Function.update a_prev x (a_prev x + 1)) r := by
            simpa only using hlt
          rwa [hUpd] at h1
        obtain ⟨a_mid, h1, h2, h3⟩ := ih hU_le_m hlt_m
        refine ⟨a_mid, h1, ?_, h3⟩
        exact Relation.ReflTransGen.trans h2 (Relation.ReflTransGen.single (Step.incr hx hbnd))
    | @move a_prev x hx hlt2 =>
      have hU_le_m : U ≤ a_prev r := by simpa only using hU_le
      have hlt_m : s.1 r < a_prev r := by simpa only using hlt
      obtain ⟨a_mid, h1, h2, h3⟩ := ih hU_le_m hlt_m
      refine ⟨a_mid, h1, ?_, h3⟩
      exact Relation.ReflTransGen.trans h2 (Relation.ReflTransGen.single (Step.move hx hlt2))

/-- 贪心迹提升为合法步迹（逐单步映射）。 -/
theorem greedy_to_step {s t : (ℕ → ℕ) × ℕ}
    (h : Relation.ReflTransGen I.GreedyStep s t) :
    Relation.ReflTransGen I.Step s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail htail hstep ih =>
    exact Relation.ReflTransGen.trans ih (Relation.ReflTransGen.single (I.greedy_is_step hstep))

/-- 贪心单调（经提升由 Step 单调得到）。 -/
theorem greedy_mono {s t : (ℕ → ℕ) × ℕ}
    (h : Relation.ReflTransGen I.GreedyStep s t) (i : ℕ) : s.1 i ≤ t.1 i :=
  I.reach_mono (I.greedy_to_step h) i

/-- 左条件下贪心必为左移（数组不变）：incr 需 ¬left，右移需已完成，皆不可能。 -/
theorem greedy_must_moveLeft {a : ℕ → ℕ} {x : ℕ} {t : (ℕ → ℕ) × ℕ}
    (h : I.GreedyStep (a, x) t) (hinc : a x < I.tgt x)
    (hleft : a x < x ∧ a (a x) < I.tgt (a x)) : t.1 = a := by
  cases h with
  | moveLeft =>
    rfl
  | incr _ _ _ hnot =>
    exact False.elim (hnot hleft)
  | moveRight _ heq =>
    omega

/-- 不在 r 处时贪心不改变 r 分量（移动不动数组，加一加在别处）。 -/
theorem greedy_preserves_r_of_ne {a : ℕ → ℕ} {p0 r : ℕ} {t : (ℕ → ℕ) × ℕ}
    (h : I.GreedyStep (a, p0) t) (hne : p0 ≠ r) : t.1 r = a r := by
  cases h with
  | moveLeft =>
    rfl
  | incr =>
    show Function.update a p0 (a p0 + 1) r = a r
    rw [Function.update_of_ne (Ne.symm hne)]
  | moveRight =>
    rfl

/-- 保持引理（尾归纳版）：起点 r 取 v，终点 v 未完成，则终点 r 仍 v。
    证明对迹作 tail 归纳：末步若在 r 处则必左移（数组不变），否则不动 r；
    前缀由 IH 得 r=v（因前缀 v 经单步单调仍未完成），故终点 r=v。 -/
theorem stay_v_aux {v r : ℕ} (hlt : v < r) (hr_n : r < I.n)
    {s : (ℕ → ℕ) × ℕ} (ha0r : s.1 r = v)
    {t : (ℕ → ℕ) × ℕ} (h : Relation.ReflTransGen I.GreedyStep s t) :
    t.1 v < I.tgt v → t.1 r = v := by
  induction h with
  | refl =>
    intro _
    exact ha0r
  | @tail m t htail hstep ih =>
    intro hv_end
    have hmono_single : m.1 v ≤ t.1 v := by
      have h1 : Relation.ReflTransGen I.GreedyStep m t :=
        Relation.ReflTransGen.single hstep
      exact I.greedy_mono h1 v
    have hm_v_lt : m.1 v < I.tgt v := lt_of_le_of_lt hmono_single hv_end
    have hm_r_eq : m.1 r = v := ih hm_v_lt
    by_cases heq : m.2 = r
    · -- 在 r 处：左条件成立，必左移，数组不变
      have hr_le_tgt : r ≤ I.tgt r := I.htgt_ge r hr_n
      have hm_r_lt_tgt : m.1 r < I.tgt r := by
        rw [hm_r_eq]
        omega
      have hleft_r : m.1 r < r ∧ m.1 (m.1 r) < I.tgt (m.1 r) := by
        rw [hm_r_eq]
        exact ⟨hlt, hm_v_lt⟩
      have hm_eq : m = (m.1, r) := Prod.ext rfl heq
      have hstep2 : I.GreedyStep (m.1, r) t := by
        rw [← hm_eq]
        exact hstep
      have ht_eq : t.1 = m.1 := I.greedy_must_moveLeft hstep2 hm_r_lt_tgt hleft_r
      calc t.1 r = m.1 r := by rw [ht_eq]
        _ = v := hm_r_eq
    · have hpres : t.1 r = m.1 r := I.greedy_preserves_r_of_ne hstep heq
      rw [hpres, hm_r_eq]

end PWInstance
