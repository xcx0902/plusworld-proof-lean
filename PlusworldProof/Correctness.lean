-- Correctness.lean (I)：贪心历史（Greedy 版）、性质二排序与加一界
-- 对应 editorial.md “不会提前离开”“完备性与终止”中图论与计数部分：
-- crossing 蕴含回到较早分量、已完成路不下降已在 Scc；此处证 Greedy 历史、
-- 不同分量初始未完成点递增（给定后分量 max 更大时）、加一总量界与成功即有解。
import PlusworldProof.Model
import PlusworldProof.Scc
import PlusworldProof.Strategy

namespace PWInstance

variable (I : PWInstance)

/-- 贪心历史（Greedy 版 step_attained）：从 s 经贪心步到 t，r 严格增加，
    则 s_r 与 t_r 间任一值皆曾在 r 处取到。证明与 Step 版同构：
    moveLeft/moveRight 皆不动数组（如 Step.move），incr 加一（如 Step.incr）。 -/
theorem greedy_attained {s t : (ℕ → ℕ) × ℕ}
    (h : Relation.ReflTransGen I.GreedyStep s t) {r U : ℕ}
    (hsrc_le : s.1 r ≤ U) (hU_le : U ≤ t.1 r) (hlt : s.1 r < t.1 r) :
    ∃ a_mid : ℕ → ℕ,
      Relation.ReflTransGen I.GreedyStep s (a_mid, r) ∧
      Relation.ReflTransGen I.GreedyStep (a_mid, r) t ∧ a_mid r = U := by
  induction h with
  | refl =>
    exact False.elim (lt_irrefl _ hlt)
  | tail htail hstep ih =>
    cases hstep with
    | @moveLeft a_prev x hx hinc hlt2 hinc2 =>
      have hU_le_m : U ≤ a_prev r := by simpa only using hU_le
      have hlt_m : s.1 r < a_prev r := by simpa only using hlt
      obtain ⟨a_mid, h1, h2, h3⟩ := ih hU_le_m hlt_m
      refine ⟨a_mid, h1, ?_, h3⟩
      exact Relation.ReflTransGen.trans h2 (Relation.ReflTransGen.single (GreedyStep.moveLeft hx hinc hlt2 hinc2))
    | @incr a_prev x hx hinc hbnd hnot =>
      by_cases heq_r : r = x
      · subst heq_r
        have hU_le2 : U ≤ a_prev r + 1 := by
          have h1 : U ≤ (Function.update a_prev r (a_prev r + 1)) r := hU_le
          rwa [Function.update_self] at h1
        have hlt2 : s.1 r < a_prev r + 1 := by
          have h1 : s.1 r < (Function.update a_prev r (a_prev r + 1)) r := hlt
          rwa [Function.update_self] at h1
        by_cases heq_U : U = a_prev r + 1
        · refine ⟨Function.update a_prev r (a_prev r + 1), ?_, Relation.ReflTransGen.refl, ?_⟩
          · exact Relation.ReflTransGen.trans htail (Relation.ReflTransGen.single (GreedyStep.incr hx hinc hbnd hnot))
          · rw [Function.update_self]
            exact heq_U.symm
        · have hU_le_m : U ≤ a_prev r := by omega
          by_cases hlt_m : s.1 r < a_prev r
          · obtain ⟨a_mid, h1, h2, h3⟩ := ih hU_le_m hlt_m
            refine ⟨a_mid, h1, ?_, h3⟩
            exact Relation.ReflTransGen.trans h2 (Relation.ReflTransGen.single (GreedyStep.incr hx hinc hbnd hnot))
          · have heq_Um : U = a_prev r := by omega
            refine ⟨a_prev, htail, Relation.ReflTransGen.single (GreedyStep.incr hx hinc hbnd hnot), heq_Um.symm⟩
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
        exact Relation.ReflTransGen.trans h2 (Relation.ReflTransGen.single (GreedyStep.incr hx hinc hbnd hnot))
    | @moveRight a_prev x hx heq =>
      have hU_le_m : U ≤ a_prev r := by simpa only using hU_le
      have hlt_m : s.1 r < a_prev r := by simpa only using hlt
      obtain ⟨a_mid, h1, h2, h3⟩ := ih hU_le_m hlt_m
      refine ⟨a_mid, h1, ?_, h3⟩
      exact Relation.ReflTransGen.trans h2 (Relation.ReflTransGen.single (GreedyStep.moveRight hx heq))

/-- 性质二排序（图论版，假设后分量 max 更大）：
    u、v 皆初始未完成，Reach u v 但 ¬Reach v u（不同分量有序），
    后分量 max Mv > u，则必 u < v。用反证：若 v < u（v ≤ u 且 u≠v），
    后分量内 Mv →…→ v 跨越 u 得 r→z（r>u≥z），由区间性得 r→u，
    于是 v→…→Mv→…→r→u 给出 Reach v u，矛盾。
    editorial：“所以 r→u 也是图中的边。较晚分量能够回到较早分量…矛盾。” -/
theorem order_of_reach {u v Mv : ℕ} (_hu_n : u < I.n) (hv_n : v < I.n) (hMv_n : Mv < I.n)
    (_hu_inc : I.src u < I.tgt u) (hv_inc : I.src v < I.tgt v)
    (huv : I.Reach u v) (hvu : ¬ I.Reach v u)
    (hMv_scc : I.SCC Mv v) (hMv_gt : u < Mv) :
    u < v := by
  by_contra hnge
  have hle : v ≤ u := by omega
  have hne : u ≠ v := by
    intro heq
    subst heq
    exact hvu Relation.ReflTransGen.refl
  have hlt_vu : v < u := by omega
  -- 后分量内 Mv 到 v 的路跨越 u
  have hReach_Mv_v : I.Reach Mv v := hMv_scc.1
  obtain ⟨r, z, hrEdge, hrReach, hzReach, hrgt, hzle⟩ :=
    I.crossing_exists hReach_Mv_v hle hMv_gt
  -- 由区间性得 r → u
  have hr_n : r < I.n := I.reach_target_lt hMv_n hrReach |>.trans_eq rfl |> fun _ => hrEdge.1
  have hr_le_tgt : r ≤ I.tgt r := I.htgt_ge r hrEdge.1
  have hEdge_ru : I.Edge r u := I.crossing_edge hrEdge hzle (le_trans (le_of_lt hrgt) hr_le_tgt |> fun h => by omega)
  -- 于是 v 可达 u：v →…→ Mv →…→ r → u
  have hReach_v_Mv : I.Reach v Mv := hMv_scc.2
  have hReach_v_r : I.Reach v r := Relation.ReflTransGen.trans hReach_v_Mv hrReach
  have hReach_v_u : I.Reach v u :=
    Relation.ReflTransGen.trans hReach_v_r (Relation.ReflTransGen.single hEdge_ru)
  exact hvu hReach_v_u

/-- 加一总量界：∑(tgt-src) ≤ n*(n-1)。每项 ≤ n-1（tgt < n），n 项求和。 -/
theorem sum_incr_bound : ∑ i ∈ Finset.range I.n, (I.tgt i - I.src i) ≤ I.n * (I.n - 1) := by
  calc ∑ i ∈ Finset.range I.n, (I.tgt i - I.src i)
      ≤ ∑ _i ∈ Finset.range I.n, (I.n - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi_n : i < I.n := Finset.mem_range.mp hi
        have htgt : I.tgt i < I.n := I.htgt_lt i hi_n
        omega
    _ = I.n * (I.n - 1) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]

/-- 成功即有解（合理性声—成功方向）：贪心迹达全完成，则其经提升为合法操作列，
    起点有效（src 自身有效），终数组即 tgt，故 Solvable。 -/
theorem greedy_success_solvable {a : ℕ → ℕ} {p start : ℕ}
    (hstart : start < I.n)
    (h : Relation.ReflTransGen I.GreedyStep (I.src, start) (a, p))
    (hsucc : ∀ i, i < I.n → a i = I.tgt i) : I.Solvable := by
  refine ⟨start, hstart, a, p, I.greedy_to_step h, hsucc⟩

/-- 后分量 max 更大则前 max 更小（相邻待处理分量 max 严格递增的图论版） -/
theorem max_lt_of_leave {M1 N M2 : ℕ} (_hM1_n : M1 < I.n)
    (htgt_gt : M1 < I.tgt M1)
    (hReach : I.Reach (I.tgt M1) N)
    (hcomp : ∀ z, I.Reach (I.tgt M1) z → I.Reach z N → z ≠ N → I.src z = I.tgt z)
    (hle : N ≤ M2) : M1 < M2 := by
  have hge : I.tgt M1 ≤ N := I.completed_path_ge_aux hReach hcomp
  omega

/-- 向左移动留在当前分量（给定后分量 max 更大时） -/
theorem stay_inside_left {a : ℕ → ℕ} {x y : ℕ} (hv : I.ValidState a)
    (hx : x < I.n) (hy : y < I.n)
    (hinc_x : a x < I.tgt x) (hlt : y < x) (heq : a x = y)
    (hinc_y : a y < I.tgt y)
    {Mv : ℕ} (hMv_n : Mv < I.n) (hMv_scc : I.SCC Mv y) (hMv_gt : x < Mv) :
    I.SCC x y := by
  have hlt2 : a x < x := by rw [heq]; exact hlt
  have hEdge : I.Edge x y := by
    rw [← heq]
    exact I.moveLeft_is_edge hv hx hinc_x hlt2
  have hReach_xy : I.Reach x y := Relation.ReflTransGen.single hEdge
  by_contra hneg
  have hNotReach : ¬ I.Reach y x := fun h => hneg ⟨hReach_xy, h⟩
  have hsrc_x : I.src x < I.tgt x := by
    have ⟨hle_src, _⟩ := hv x hx
    omega
  have hsrc_y : I.src y < I.tgt y := by
    have ⟨hle_src, _⟩ := hv y hy
    omega
  have hlt_xy : x < y := I.order_of_reach hx hy hMv_n hsrc_x hsrc_y hReach_xy hNotReach hMv_scc hMv_gt
  omega

/-- 不会过早完成最大点：贪心迹达 (a,M)，M 差一步完成且左条件为假，
    同分量尚有最大未完成 v<M（其间皆已完成），则矛盾。
    证明经 M→…→v 路用 crossing 得 r>v≥z，再由区间性得 r→v；
    r 与 M 同分量故 r≤M，分 r=M（当前值已含 v 则左条件真，或经历史+保持得 aM=v）与
    r<M（已完成故值>v，经历史+保持得 ar=v）皆矛盾。
    editorial“不会提前离开当前分量”中唯一需要担心的情形。 -/
theorem no_early_completion {a : ℕ → ℕ} {M v start : ℕ} (hM_n : M < I.n)
    (hTrace : Relation.ReflTransGen I.GreedyStep (I.src, start) (a, M))
    (haM_last : a M + 1 = I.tgt M)
    (hnotleft_M : ¬ (a M < M ∧ a (a M) < I.tgt (a M)))
    (hv_lt : v < M) (hv_inc : a v < I.tgt v)
    (hscc : I.SCC M v) (hmax : ∀ z, I.SCC M z → z ≤ M)
    (hv_max : ∀ u, v < u → u < M → a u = I.tgt u) : False := by
  have hReach_Mv : I.Reach M v := hscc.1
  have hReach_vM : I.Reach v M := hscc.2
  obtain ⟨r, z, hrEdge, hrReach, hzReach, hrgt, hzle⟩ :=
    I.crossing_exists hReach_Mv le_rfl hv_lt
  have hr_n : r < I.n := hrEdge.1
  have hz_src_le : I.src r ≤ z := hrEdge.2.2.1
  have hz_le_tgt : z ≤ I.tgt r := hrEdge.2.2.2
  have hr_le_tgt : r ≤ I.tgt r := I.htgt_ge r hr_n
  have hEdge_rv : I.Edge r v := I.crossing_edge hrEdge hzle (by omega)
  have hReach_rM : I.Reach r M :=
    Relation.ReflTransGen.trans (Relation.ReflTransGen.trans (Relation.ReflTransGen.single hrEdge) hzReach) hReach_vM
  have hr_le_M : r ≤ M := hmax r ⟨hrReach, hReach_rM⟩
  have hsrc_r_le_v : I.src r ≤ v := le_trans hz_src_le hzle
  by_cases heq_rM : r = M
  · subst heq_rM
    -- 此时 r（即原 M）为最大点，当前 a r = tgt r -1 ≥ v
    have hr_le_tgt : r ≤ I.tgt r := I.htgt_ge r hM_n
    have hv_le_ar : v ≤ a r := by omega
    by_cases heq_v : v = a r
    · have hleft_r : a r < r ∧ a (a r) < I.tgt (a r) := by
        constructor
        · rw [← heq_v]; exact hv_lt
        · rw [← heq_v]; exact hv_inc
      exact False.elim (hnotleft_M hleft_r)
    · have hlt_ar : v < a r := by omega
      have hsrc_lt_ar : I.src r < a r := lt_of_le_of_lt hsrc_r_le_v hlt_ar
      obtain ⟨a_mid, h1, h2, h3⟩ :=
        I.greedy_attained hTrace hsrc_r_le_v (le_of_lt hlt_ar) hsrc_lt_ar
      have ha_end : a r = v := I.stay_v_aux hv_lt hM_n h3 h2 hv_inc
      omega
  · have hr_lt_M : r < M := lt_of_le_of_ne hr_le_M heq_rM
    have hr_n2 : r < I.n := lt_of_le_of_lt hr_le_M hM_n
    have har_eq : a r = I.tgt r := hv_max r hrgt hr_lt_M
    have hr_le_tgtr : r ≤ I.tgt r := I.htgt_ge r hr_n2
    have hv_lt_ar : v < a r := by omega
    have hsrc_lt_ar : I.src r < a r := lt_of_le_of_lt hsrc_r_le_v hv_lt_ar
    have hle_v_ar : v ≤ a r := le_of_lt hv_lt_ar
    obtain ⟨a_mid, h1, h2, h3⟩ :=
      I.greedy_attained hTrace hsrc_r_le_v hle_v_ar hsrc_lt_ar
    have ha_end : a r = v := I.stay_v_aux hrgt hr_n2 h3 h2 hv_inc
    omega

/-- 未完成集与计数 R：记录移动前位置 x 与当时未完成数 R 的二元组，对应终止节界。 -/
noncomputable def unfinishedSet (a : ℕ → ℕ) : Finset ℕ :=
  (Finset.range I.n).filter (fun i => a i < I.tgt i)

theorem mem_unfinishedSet_iff {a : ℕ → ℕ} {i : ℕ} :
    i ∈ I.unfinishedSet a ↔ i < I.n ∧ a i < I.tgt i := by
  unfold unfinishedSet
  simp only [Finset.mem_filter, Finset.mem_range]

/-- 单调：数组逐点不减则未完成集缩小，故 R 不增。 -/
theorem unfinished_subset_of_le {a b : ℕ → ℕ} (hle : ∀ i, a i ≤ b i) :
    I.unfinishedSet b ⊆ I.unfinishedSet a := by
  intro i hi
  have hmem := (I.mem_unfinishedSet_iff).mp hi
  obtain ⟨hi_n, hlt⟩ := hmem
  have hle_i : a i ≤ b i := hle i
  exact (I.mem_unfinishedSet_iff).mpr ⟨hi_n, lt_of_le_of_lt hle_i hlt⟩

theorem card_unfinished_le_of_le {a b : ℕ → ℕ} (hle : ∀ i, a i ≤ b i) :
    (I.unfinishedSet b).card ≤ (I.unfinishedSet a).card :=
  Finset.card_le_card (I.unfinished_subset_of_le hle)

/-- R 有界：R ≤ n。 -/
theorem card_unfinished_le_n (a : ℕ → ℕ) :
    (I.unfinishedSet a).card ≤ I.n := by
  calc (I.unfinishedSet a).card ≤ (Finset.range I.n).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = I.n := Finset.card_range _

/-- 卡住自环步：已完成且 tgt_x = x 时右移即原地踏步。 -/
theorem stuck_selfloop {a : ℕ → ℕ} {x : ℕ} (hx : x < I.n)
    (heq : a x = I.tgt x) (heq2 : I.tgt x = x) :
    I.GreedyStep (a, x) (a, x) := by
  have h : I.GreedyStep (a, x) (a, I.tgt x) := GreedyStep.moveRight hx heq
  rwa [heq2] at h

/-- 卡住时贪心确定：已完成自环处唯一后继即自身
    （左移/加一皆需未完成，由 heq 经 omega 排除）。 -/
theorem stuck_deterministic {a : ℕ → ℕ} {x : ℕ} {t : (ℕ → ℕ) × ℕ}
    (heq : a x = I.tgt x) (heq2 : I.tgt x = x)
    (h : I.GreedyStep (a, x) t) : t = (a, x) := by
  cases h with
  | @moveLeft _ _ _ hinc _ _ => omega
  | @incr _ _ _ hinc _ _ => omega
  | @moveRight _ _ _ _ => rw [heq2]

/-- 卡住后状态恒定：自环迹永留原状态（对迹作归纳，每步由确定性得后继即自身）。 -/
theorem stuck_fixed {a : ℕ → ℕ} {x : ℕ} (_hx : x < I.n)
    (heq : a x = I.tgt x) (heq2 : I.tgt x = x)
    {t : (ℕ → ℕ) × ℕ}
    (h : Relation.ReflTransGen I.GreedyStep (a, x) t) : t = (a, x) := by
  induction h with
  | refl => rfl
  | @tail m t htail hstep ih =>
    have hm_eq : m = (a, x) := ih
    subst hm_eq
    exact I.stuck_deterministic heq heq2 hstep

/-- 卡住报告无解的合理性：卡住（含剩余未完成 y）后任何延续都不全完成。 -/
theorem stuck_never_succeeds {a : ℕ → ℕ} {x : ℕ} (hx : x < I.n)
    (heq : a x = I.tgt x) (heq2 : I.tgt x = x)
    {y : ℕ} (hy_n : y < I.n) (hy_inc : a y < I.tgt y)
    {t : (ℕ → ℕ) × ℕ}
    (h : Relation.ReflTransGen I.GreedyStep (a, x) t) :
    ¬ ∀ i, i < I.n → t.1 i = I.tgt i := by
  intro hsucc
  have hfix : t = (a, x) := I.stuck_fixed hx heq heq2 h
  have harr : t.1 = a := congrArg Prod.fst hfix
  have hcon : a y = I.tgt y := by
    rw [← harr]
    exact hsucc y hy_n
  omega

/-- 单步方向（右）：已完成非自环则严格向右（tgt_x ≥ x 且 ≠ x）。
    editorial 移动界右相“沿最终边严格向右”。 -/
theorem completed_move_gt {x : ℕ} (hx : x < I.n) (hne : I.tgt x ≠ x) :
    x < I.tgt x := by
  have hge := I.htgt_ge x hx
  omega

/-- 单步方向（左）：左移目标即 a_x < x。editorial 移动界左相“严格向左”。 -/
theorem moveLeft_target_lt {a : ℕ → ℕ} {x : ℕ} (hlt : a x < x) :
    (a, a x).2 < x :=
  hlt

/-- 二元组空间有限：(x, R) ∈ range n × range (n+1)，基数 n*(n+1)。
    editorial 移动界的基础：每次移动记录 (x, R)，x < n 且 R ≤ n。 -/
theorem pair_space_card :
    ((Finset.range I.n) ×ˢ (Finset.range (I.n + 1))).card
      = I.n * (I.n + 1) := by
  rw [Finset.card_product, Finset.card_range, Finset.card_range]

/-- 给定 NoDup 的移动记录表长 ≤ 对空间基数（editorial“二元组不可能出现两次”组装处：
    单步方向 + stay_v_aux 左相不返回 + 已完成路不下降已分别形式化，此处为纯组合推论）。 -/
theorem moves_bound_of_nodup {l : List (ℕ × ℕ)}
    (hnd : l.Nodup)
    (hmem : ∀ x ∈ l, x.1 < I.n ∧ x.2 ≤ I.n) :
    l.length ≤ I.n * (I.n + 1) := by
  have hsub : l.toFinset ⊆ (Finset.range I.n) ×ˢ (Finset.range (I.n + 1)) := by
    intro x hx
    rw [List.mem_toFinset] at hx
    obtain ⟨hx1, hx2⟩ := hmem x hx
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨hx1, by omega⟩
  have hcard : l.toFinset.card = l.length :=
    List.toFinset_card_of_nodup hnd
  calc l.length = l.toFinset.card := hcard.symm
    _ ≤ (((Finset.range I.n) ×ˢ (Finset.range (I.n + 1)))).card :=
        Finset.card_le_card hsub
    _ = I.n * (I.n + 1) := I.pair_space_card

/-- 操作总数算术界（editorial 最终求和）：n*(n-1)+n*(n+1) ≤ 2*n^2，
    题目允许 o ≤ 2n^2；n≥1 时用 n*n 版本得 2*n^2-n < 2*n^2。 -/
theorem total_le_2n2_arith : I.n * (I.n - 1) + I.n * (I.n + 1) ≤ 2 * I.n ^ 2 := by
  by_cases hn0 : I.n = 0
  · rw [hn0]; simp
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    rw [hk]
    have hsub : k.succ - 1 = k := by omega
    rw [hsub]
    simp only [Nat.succ_eq_add_one]
    have key : (k + 1) * k + (k + 1) * (k + 1 + 1) = 2 * (k + 1) ^ 2 := by ring
    omega

/-- 总量界组装：加一部分（数组增长 ≤ 和式）+ 移动部分（NoDup 表长 ≤ 对空间），
    得 n*(n-1)+|l| ≤ 2*n^2，恰为题目 o ≤ 2n^2 界；editorial 得更紧的 2n^2-n。 -/
theorem total_bound_of_nodup {l : List (ℕ × ℕ)}
    (hnd : l.Nodup)
    (hmem : ∀ x ∈ l, x.1 < I.n ∧ x.2 ≤ I.n) :
    I.n * (I.n - 1) + l.length ≤ 2 * I.n ^ 2 := by
  calc I.n * (I.n - 1) + l.length
      ≤ I.n * (I.n - 1) + I.n * (I.n + 1) :=
        Nat.add_le_add_left (I.moves_bound_of_nodup hnd hmem) _
    _ ≤ 2 * I.n ^ 2 := I.total_le_2n2_arith

end PWInstance
