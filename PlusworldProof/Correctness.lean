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

end PWInstance
