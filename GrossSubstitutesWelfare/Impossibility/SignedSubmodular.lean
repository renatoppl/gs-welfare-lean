import GrossSubstitutesWelfare.Defs

set_option maxHeartbeats 4000000

/-!
# Appendix C: Proposition C.3 — Signed Submodular Impossibility (`prop:signed-sub`)

Formalizes Appendix C Proposition C.3 (`prop:signed-sub`, `[BIK07, Rubinstein16]`) of
*Gross Substitutes Welfare in Random Order*:
- Without the gross substitutes exchange axiom, submodularity alone admits no constant competitive
  ratio once values may be negative: on the explicit finite-valued disjoint-groups family on
  `n = k^(k + 1)` items (`k ≥ 2`), every randomized non-clairvoyant online algorithm obtains
  `E[f(A)] ≤ c · OPT(f) · log(log n) / log n` on some member `f` of the family.
-/

namespace GrossSubstitutesWelfare

open Classical MeasureTheory

noncomputable section

namespace SignedSubmodularInternal

/-- **Proposition C.3 (Signed submodular functions, `prop:signed-sub`)**:
There is an absolute constant `c > 0` such that for infinitely many `n`, there exists a finite
nonempty family of finite-valued submodular functions `f : 2^N → ℝ` with `f(∅) = 0` (and
`OPT(f) > 0`) such that every online selection algorithm has
`E[f(A)] ≤ c * OPT(f) * log(log n) / log n` on some `f` in the family. -/
def groupIdx (k : ℕ) (g : Fin (k ^ (k + 1))) : Fin (k ^ k) :=
  ((@finProdFinEquiv (k ^ k) k).symm g).1

def crossPairs (k : ℕ) (S : Finset (Fin (k ^ (k + 1)))) : ℕ :=
  ∑ x ∈ S, (S.filter (fun y => groupIdx k y ≠ groupIdx k x)).card

def groupSubmodFn (k : ℕ) (w : Fin (k ^ (k + 1)) → Bool)
    (S : Finset (Fin (k ^ (k + 1)))) : ℝ :=
  (∑ g ∈ S, if w g then (1 : ℝ) else 0) - 2 * (crossPairs k S : ℝ)

def firstHit {n : ℕ} (w : Fin n → Bool) (π : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) (t : Fin n) : Prop :=
  (π t ∈ S ∧ w (π t) = true) ∧ ∀ r : Fin n, r < t → ¬ (π r ∈ S ∧ w (π r) = true)

def laterSameGroup (k : ℕ) (w : Fin (k ^ (k + 1)) → Bool)
    (π : Equiv.Perm (Fin (k ^ (k + 1)))) (t : Fin (k ^ (k + 1))) : ℝ :=
  1 + ∑ s ∈ (Finset.univ : Finset (Fin (k ^ (k + 1)))).filter
    (fun s => t < s ∧ groupIdx k (π s) = groupIdx k (π t)),
    (if w (π s) then (1 : ℝ) else 0)

def upperScore (k : ℕ) (w : Fin (k ^ (k + 1)) → Bool)
    (π : Equiv.Perm (Fin (k ^ (k + 1)))) (S : Finset (Fin (k ^ (k + 1)))) : ℝ :=
  ∑ t : Fin (k ^ (k + 1)), if firstHit w π S t then laterSameGroup k w π t else 0

def bernProb (k : ℕ) (w : Fin (k ^ (k + 1)) → Bool) : ℝ :=
  ∏ g : Fin (k ^ (k + 1)), (if w g then 1 / (k : ℝ) else 1 - 1 / (k : ℝ))

def firstHitProb (k : ℕ) (alg : OnlineSelectionAlg (k ^ (k + 1)))
    (π : Equiv.Perm (Fin (k ^ (k + 1)))) (w : Fin (k ^ (k + 1)) → Bool)
    (t : Fin (k ^ (k + 1))) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin (k ^ (k + 1))))).filter (fun S => firstHit w π S t),
    alg.seedMeasure.real
      {ω | runDetSelection (alg.det ω) (fun T => ((groupSubmodFn k w T : ℝ) : WithBot ℝ)) π = S}

def arrivedList {n : ℕ} (π : Equiv.Perm (Fin n)) : (m : ℕ) → m ≤ n → List (Fin n)
  | 0, _ => []
  | m + 1, hm => arrivedList π m (Nat.le_of_succ_le hm) ++ [π ⟨m, hm⟩]

end SignedSubmodularInternal

section
open SignedSubmodularInternal

theorem prop_signed_submodular_impossibility :
    ∃ c : ℝ, 0 < c ∧
      ∀ N0 : ℕ, ∃ n : ℕ, N0 ≤ n ∧ 3 ≤ n ∧
        ∃ fam : List (Finset (Fin n) → ℝ),
          fam ≠ [] ∧
          (∀ f ∈ fam, IsSubmodularReal f ∧ 0 < optValReal f) ∧
          ∀ alg : OnlineSelectionAlg n,
            ∃ f ∈ fam,
              expectedSelectionValReal alg f ≤
                c * optValReal f * (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) :=
by
  refine ⟨8, by norm_num, ?_⟩
  intro N0
  let k : ℕ := max N0 4
  have hkN0 : N0 ≤ k := le_max_left N0 4
  have hk4 : 4 ≤ k := le_max_right N0 4
  have hk_pos : 0 < k := by omega
  have hk_real_ge4 : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk4
  have hk_real_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hk_real_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_real_pos
  have hk_le_pow : k ≤ k ^ (k + 1) := Nat.le_self_pow (by omega) k
  have hn_ge_N0 : N0 ≤ k ^ (k + 1) := le_trans hkN0 hk_le_pow
  have hn_ge3 : 3 ≤ k ^ (k + 1) := by omega
  have hn_pos : 0 < k ^ (k + 1) := by omega

  
  have h_log_ratio :
      4 / (k : ℝ) ≤
        8 * (Real.log (Real.log ((k ^ (k + 1) : ℕ) : ℝ)) /
          Real.log ((k ^ (k + 1) : ℕ) : ℝ)) := by
    have h_log2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have h_log4 : (1 : ℝ) ≤ Real.log 4 := by
      have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
      rw [h4, Real.log_pow]
      norm_num at h_log2 ⊢
      linarith
    have h_logk_ge1 : (1 : ℝ) ≤ Real.log (k : ℝ) :=
      le_trans h_log4 (Real.log_le_log (by norm_num) hk_real_ge4)
    have h_logk_pos : 0 < Real.log (k : ℝ) := by linarith
    have h_logn_eq :
        Real.log ((k ^ (k + 1) : ℕ) : ℝ) = ((k : ℝ) + 1) * Real.log (k : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one]
    have h_logn_gt_k : (k : ℝ) ≤ Real.log ((k ^ (k + 1) : ℕ) : ℝ) := by
      rw [h_logn_eq]
      nlinarith
    have h_logn_pos : 0 < Real.log ((k ^ (k + 1) : ℕ) : ℝ) :=
      lt_of_lt_of_le hk_real_pos h_logn_gt_k
    have h_loglogn : Real.log (k : ℝ) ≤ Real.log (Real.log ((k ^ (k + 1) : ℕ) : ℝ)) :=
      Real.log_le_log hk_real_pos h_logn_gt_k
    have h_logn_le : Real.log ((k ^ (k + 1) : ℕ) : ℝ) ≤ 2 * (k : ℝ) * Real.log (k : ℝ) := by
      rw [h_logn_eq]
      nlinarith
    rw [← mul_div_assoc, div_le_div_iff₀ hk_real_pos h_logn_pos]
    nlinarith

  
  have h_le_opt : ∀ (f : Finset (Fin (k ^ (k + 1))) → ℝ) (S : Finset (Fin (k ^ (k + 1)))),
      f S ≤ optValReal f := by
    intro f S
    let supVal :=
      (Finset.univ : Finset (Finset (Fin (k ^ (k + 1))))).sup (fun T => ((f T : ℝ) : WithBot ℝ))
    have h0 : ((f ∅ : ℝ) : WithBot ℝ) ≤ supVal :=
      Finset.le_sup (f := fun T => ((f T : ℝ) : WithBot ℝ)) (Finset.mem_univ ∅)
    have hne : supVal ≠ ⊥ := by
      intro hbot
      rw [hbot] at h0
      exact WithBot.coe_ne_bot (le_bot_iff.mp h0)
    obtain ⟨M, hM⟩ := WithBot.ne_bot_iff_exists.mp hne
    have hS : ((f S : ℝ) : WithBot ℝ) ≤ supVal :=
      Finset.le_sup (f := fun T => ((f T : ℝ) : WithBot ℝ)) (Finset.mem_univ S)
    rw [← hM] at hS
    have hopt : optValReal f = M := by
      unfold optValReal
      change supVal.unbotD 0 = M
      rw [← hM, WithBot.unbotD_coe]
    rw [hopt]
    exact WithBot.coe_le_coe.mp hS

  
  have h_submod : ∀ w : Fin (k ^ (k + 1)) → Bool, IsSubmodularReal (groupSubmodFn k w) := by
    intro w
    refine ⟨by simp [groupSubmodFn, crossPairs], ?_⟩
    have h_cp_insert : ∀ (R : Finset (Fin (k ^ (k + 1)))) (g : Fin (k ^ (k + 1))), g ∉ R →
        crossPairs k (insert g R) =
          crossPairs k R + 2 * (R.filter (fun y => groupIdx k y ≠ groupIdx k g)).card := by
      intro R g hg
      unfold crossPairs
      rw [Finset.sum_insert hg]
      have h_head : ((insert g R).filter (fun y => groupIdx k y ≠ groupIdx k g)) =
          R.filter (fun y => groupIdx k y ≠ groupIdx k g) := by
        rw [Finset.filter_insert]
        simp
      have h_tail : ∀ x ∈ R, ((insert g R).filter (fun y => groupIdx k y ≠ groupIdx k x)).card =
          (R.filter (fun y => groupIdx k y ≠ groupIdx k x)).card +
            (if groupIdx k x ≠ groupIdx k g then 1 else 0) := by
        intro x _
        rw [Finset.filter_insert]
        by_cases hgx : groupIdx k g ≠ groupIdx k x
        · have hxg : groupIdx k x ≠ groupIdx k g := Ne.symm hgx
          have hg_not : g ∉ R.filter (fun y => groupIdx k y ≠ groupIdx k x) := by simp [hg]
          simp [hgx, hxg, hg_not]
        · have hxg : ¬ (groupIdx k x ≠ groupIdx k g) := fun h => hgx (Ne.symm h)
          simp [hgx, hxg]
      rw [h_head, Finset.sum_congr rfl h_tail, Finset.sum_add_distrib, ← Finset.card_filter]
      omega
    intro Q R hQR g hgR
    have hgQ : g ∉ Q := fun h => hgR (hQR h)
    have h_card_le : (Q.filter (fun y => groupIdx k y ≠ groupIdx k g)).card ≤
        (R.filter (fun y => groupIdx k y ≠ groupIdx k g)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ hQR)
    have h_card_real : ((Q.filter (fun y => groupIdx k y ≠ groupIdx k g)).card : ℝ) ≤
        ((R.filter (fun y => groupIdx k y ≠ groupIdx k g)).card : ℝ) := by
      exact_mod_cast h_card_le
    unfold groupSubmodFn
    rw [Finset.sum_insert hgR, Finset.sum_insert hgQ, h_cp_insert R g hgR, h_cp_insert Q g hgQ]
    push_cast
    linarith

  have h_opt_nonneg : ∀ w : Fin (k ^ (k + 1)) → Bool, 0 ≤ optValReal (groupSubmodFn k w) := by
    intro w
    have h0 : groupSubmodFn k w ∅ = 0 := (h_submod w).1
    linarith [h_le_opt (groupSubmodFn k w) ∅]

  have h_opt_pos : ∀ w : Fin (k ^ (k + 1)) → Bool, (∃ g, w g = true) →
      0 < optValReal (groupSubmodFn k w) := by
    intro w ⟨g, hwg⟩
    have h1 : groupSubmodFn k w {g} = 1 := by
      unfold groupSubmodFn crossPairs
      rw [Finset.sum_singleton, Finset.sum_singleton]
      simp [hwg]
    linarith [h_le_opt (groupSubmodFn k w) {g}]

  have h_opt_full : ∀ (w : Fin (k ^ (k + 1)) → Bool) (a : Fin (k ^ k)),
      (∀ j : Fin k, w (@finProdFinEquiv (k ^ k) k (a, j)) = true) →
      (k : ℝ) ≤ optValReal (groupSubmodFn k w) := by
    intro w a hwa
    let emb : Fin k ↪ Fin (k ^ (k + 1)) :=
      ⟨fun j => @finProdFinEquiv (k ^ k) k (a, j),
        fun j₁ j₂ h => (Prod.mk.inj ((@finProdFinEquiv (k ^ k) k).injective h)).2⟩
    let Ga : Finset (Fin (k ^ (k + 1))) := Finset.univ.map emb
    have hGa_grp : ∀ x ∈ Ga, groupIdx k x = a := by
      intro x hx
      rcases Finset.mem_map.mp hx with ⟨j, _, rfl⟩
      simp [emb, groupIdx]
    have hGa_w : ∀ x ∈ Ga, w x = true := by
      intro x hx
      rcases Finset.mem_map.mp hx with ⟨j, _, rfl⟩
      exact hwa j
    have hGa_cp : crossPairs k Ga = 0 := by
      unfold crossPairs
      apply Finset.sum_eq_zero
      intro x hx
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro y hy
      simp [hGa_grp x hx, hGa_grp y hy]
    have hGa_sum : (∑ x ∈ Ga, if w x then (1 : ℝ) else 0) = (k : ℝ) := by
      have h_ones : ∀ x ∈ Ga, (if w x then (1 : ℝ) else 0) = 1 := by
        intro x hx
        simp [hGa_w x hx]
      rw [Finset.sum_congr rfl h_ones, Finset.sum_const, nsmul_eq_mul, mul_one]
      simp [Ga]
    have hGa_val : groupSubmodFn k w Ga = (k : ℝ) := by
      unfold groupSubmodFn
      rw [hGa_sum, hGa_cp]
      norm_num
    linarith [h_le_opt (groupSubmodFn k w) Ga]

  
  have h_later_nonneg : ∀ w π t, 0 ≤ laterSameGroup k w π t := by
    intro w π t
    unfold laterSameGroup
    have h_sum_nn : 0 ≤ ∑ s ∈ (Finset.univ : Finset (Fin (k ^ (k + 1)))).filter
        (fun s => t < s ∧ groupIdx k (π s) = groupIdx k (π t)),
        (if w (π s) then (1 : ℝ) else 0) := by
      apply Finset.sum_nonneg
      intro s _
      split_ifs <;> norm_num
    linarith

  have h_upper_nonneg : ∀ w π S, 0 ≤ upperScore k w π S := by
    intro w π S
    unfold upperScore
    apply Finset.sum_nonneg
    intro t _
    split_ifs
    · exact h_later_nonneg w π t
    · norm_num

  have h_pointwise : ∀ (w : Fin (k ^ (k + 1)) → Bool) (π : Equiv.Perm (Fin (k ^ (k + 1))))
      (S : Finset (Fin (k ^ (k + 1)))),
      groupSubmodFn k w S ≤ upperScore k w π S := by
    have h_multigroup_neg : ∀ (w : Fin (k ^ (k + 1)) → Bool) (S : Finset (Fin (k ^ (k + 1))))
        (x₀ y₀ : Fin (k ^ (k + 1))),
        x₀ ∈ S → y₀ ∈ S → groupIdx k x₀ ≠ groupIdx k y₀ → groupSubmodFn k w S ≤ 0 := by
      intro w S x₀ y₀ hx₀ hy₀ hxy
      have h_each : ∀ x ∈ S, 1 ≤ (S.filter (fun y => groupIdx k y ≠ groupIdx k x)).card := by
        intro x _
        by_cases hx : groupIdx k x₀ ≠ groupIdx k x
        · exact Finset.card_pos.mpr ⟨x₀, Finset.mem_filter.mpr ⟨hx₀, hx⟩⟩
        · have hx_eq : groupIdx k x₀ = groupIdx k x := not_ne_iff.mp hx
          have hy : groupIdx k y₀ ≠ groupIdx k x := fun h => hxy (hx_eq.trans h.symm)
          exact Finset.card_pos.mpr ⟨y₀, Finset.mem_filter.mpr ⟨hy₀, hy⟩⟩
      have h_cp_ge : S.card ≤ crossPairs k S := by
        unfold crossPairs
        calc S.card
          _ = ∑ _x ∈ S, 1 := by simp
          _ ≤ ∑ x ∈ S, (S.filter (fun y => groupIdx k y ≠ groupIdx k x)).card :=
              Finset.sum_le_sum h_each
      have h_cp_real : (S.card : ℝ) ≤ (crossPairs k S : ℝ) := by exact_mod_cast h_cp_ge
      have h_w_le : (∑ g ∈ S, if w g then (1 : ℝ) else 0) ≤ (S.card : ℝ) := by
        calc (∑ g ∈ S, if w g then (1 : ℝ) else 0)
          _ ≤ ∑ _g ∈ S, (1 : ℝ) := by
              apply Finset.sum_le_sum
              intro g _
              split_ifs <;> norm_num
          _ = (S.card : ℝ) := by simp
      unfold groupSubmodFn
      linarith

    intro w π S
    let H := (Finset.univ : Finset (Fin (k ^ (k + 1)))).filter (fun t => π t ∈ S ∧ w (π t) = true)
    by_cases hH : H.Nonempty
    · let t₀ := H.min' hH
      have ht₀_mem : t₀ ∈ H := Finset.min'_mem H hH
      have ht₀_S : π t₀ ∈ S := (Finset.mem_filter.mp ht₀_mem).2.1
      have ht₀_w : w (π t₀) = true := (Finset.mem_filter.mp ht₀_mem).2.2
      have h_fh_iff : ∀ t : Fin (k ^ (k + 1)), firstHit w π S t ↔ t = t₀ := by
        intro t
        constructor
        · rintro ⟨ht_in, ht_min⟩
          have htH : t ∈ H := Finset.mem_filter.mpr ⟨Finset.mem_univ t, ht_in⟩
          have h_le : t₀ ≤ t := Finset.min'_le H t htH
          have h_not_lt : ¬ (t₀ < t) := fun hlt => ht_min t₀ hlt ⟨ht₀_S, ht₀_w⟩
          exact le_antisymm (not_lt.mp h_not_lt) h_le
        · rintro rfl
          refine ⟨⟨ht₀_S, ht₀_w⟩, fun r hr h_in => ?_⟩
          have hrH : r ∈ H := Finset.mem_filter.mpr ⟨Finset.mem_univ r, h_in⟩
          exact not_lt_of_ge (Finset.min'_le H r hrH) hr
      have h_us_eq : upperScore k w π S = laterSameGroup k w π t₀ := by
        unfold upperScore
        simp [h_fh_iff]
      rw [h_us_eq]
      by_cases h_diff : ∃ y ∈ S, groupIdx k y ≠ groupIdx k (π t₀)
      · rcases h_diff with ⟨y, hyS, hy_ne⟩
        exact le_trans (h_multigroup_neg w S y (π t₀) hyS ht₀_S hy_ne) (h_later_nonneg w π t₀)
      · push_neg at h_diff
        have h_f_le_w : groupSubmodFn k w S ≤ ∑ g ∈ S, if w g then (1 : ℝ) else 0 := by
          unfold groupSubmodFn
          have : (0 : ℝ) ≤ (crossPairs k S : ℝ) := Nat.cast_nonneg _
          linarith
        have h_w_eq_card :
            (∑ g ∈ S, if w g then (1 : ℝ) else 0) = ((S.filter (fun g => w g = true)).card : ℝ) := by
          rw [Finset.card_filter, Nat.cast_sum]
          apply Finset.sum_congr rfl
          intro g _
          cases w g <;> simp
        have h_filter_eq_map : S.filter (fun g => w g = true) = H.map π.toEmbedding := by
          ext g
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
            Equiv.coe_toEmbedding, H]
          constructor
          · rintro ⟨hgS, hgw⟩
            exact ⟨π.symm g, ⟨by simpa using hgS, by simpa using hgw⟩, π.apply_symm_apply g⟩
          · rintro ⟨t, ⟨htS, htw⟩, rfl⟩
            exact ⟨htS, htw⟩
        have h_card_H : (S.filter (fun g => w g = true)).card = H.card := by
          rw [h_filter_eq_map, Finset.card_map]
        let L := (Finset.univ : Finset (Fin (k ^ (k + 1)))).filter
          (fun s => t₀ < s ∧ groupIdx k (π s) = groupIdx k (π t₀))
        let L' := L.filter (fun s => w (π s) = true)
        have h_sub : H ⊆ insert t₀ L' := by
          intro s hs
          rw [Finset.mem_insert]
          by_cases hst : s = t₀
          · exact Or.inl hst
          · right
            have hs_pair := (Finset.mem_filter.mp hs).2
            have h_le : t₀ ≤ s := Finset.min'_le H s hs
            have h_lt : t₀ < s := lt_of_le_of_ne h_le (Ne.symm hst)
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ s, h_lt, h_diff (π s) hs_pair.1⟩, hs_pair.2⟩
        have h_H_le : H.card ≤ L'.card + 1 :=
          le_trans (Finset.card_le_card h_sub) (Finset.card_insert_le t₀ L')
        have h_H_real : (H.card : ℝ) ≤ (L'.card : ℝ) + 1 := by exact_mod_cast h_H_le
        have h_later_eq : laterSameGroup k w π t₀ = 1 + (L'.card : ℝ) := by
          unfold laterSameGroup
          change 1 + (∑ s ∈ L, if w (π s) then (1 : ℝ) else 0) = 1 + (L'.card : ℝ)
          congr 1
          rw [Finset.card_filter, Nat.cast_sum]
          apply Finset.sum_congr rfl
          intro s _
          cases w (π s) <;> simp
        linarith [h_f_le_w, h_w_eq_card, congrArg (Nat.cast (R := ℝ)) h_card_H, h_H_real, h_later_eq]
    · have hH_empty : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
      have h_w_zero : (∑ g ∈ S, if w g then (1 : ℝ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro g hgS
        by_cases hwg : w g = true
        · exfalso
          have hmem : π.symm g ∈ H := by
            simp [H, hgS, hwg]
          rw [hH_empty] at hmem
          exact Finset.notMem_empty _ hmem
        · simp [hwg]
      have h_f_nonpos : groupSubmodFn k w S ≤ 0 := by
        unfold groupSubmodFn
        rw [h_w_zero]
        have : (0 : ℝ) ≤ (crossPairs k S : ℝ) := Nat.cast_nonneg _
        linarith
      exact le_trans h_f_nonpos (h_upper_nonneg w π S)

  
  let θ : Bool → ℝ := fun b => if b then 1 / (k : ℝ) else 1 - 1 / (k : ℝ)
  have h_inv_pos : 0 < 1 / (k : ℝ) := div_pos zero_lt_one hk_real_pos
  have h_inv_lt1 : 1 / (k : ℝ) < 1 := (div_lt_one hk_real_pos).mpr (by linarith)
  have h_theta_pos : ∀ b : Bool, 0 < θ b := by
    intro b
    cases b <;> dsimp [θ] <;> linarith
  have h_theta_sum : ∑ b : Bool, θ b = 1 := by
    rw [Fintype.sum_bool]
    dsimp [θ]
    ring
  have h_bern_pos : ∀ w : Fin (k ^ (k + 1)) → Bool, 0 < bernProb k w := by
    intro w
    unfold bernProb
    exact Finset.prod_pos (fun g _ => h_theta_pos (w g))
  have h_bern_sum : ∑ w : Fin (k ^ (k + 1)) → Bool, bernProb k w = 1 := by
    unfold bernProb
    change ∑ w : Fin (k ^ (k + 1)) → Bool, ∏ g : Fin (k ^ (k + 1)), θ (w g) = 1
    rw [← Fintype.prod_sum (fun (_ : Fin (k ^ (k + 1))) (b : Bool) => θ b)]
    exact Finset.prod_eq_one (fun _ _ => h_theta_sum)

  let E_full := (Finset.univ : Finset (Fin (k ^ (k + 1)) → Bool)).filter
    (fun w => ∃ a : Fin (k ^ k), ∀ j : Fin k, w (@finProdFinEquiv (k ^ k) k (a, j)) = true)
  have h_bern_full : (1 / 2 : ℝ) ≤ ∑ w ∈ E_full, bernProb k w := by
    let E_none := (Finset.univ : Finset (Fin (k ^ (k + 1)) → Bool)).filter
      (fun w => ¬ ∃ a : Fin (k ^ k), ∀ j : Fin k, w (@finProdFinEquiv (k ^ k) k (a, j)) = true)
    have h_part : (∑ w ∈ E_full, bernProb k w) + (∑ w ∈ E_none, bernProb k w) = 1 := by
      have h := Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset (Fin (k ^ (k + 1)) → Bool)))
        (p := fun w => ∃ a : Fin (k ^ k), ∀ j : Fin k, w (@finProdFinEquiv (k ^ k) k (a, j)) = true)
        (f := bernProb k)
      exact h.trans h_bern_sum
    let e : (Fin (k ^ (k + 1)) → Bool) ≃ (Fin (k ^ k) → Fin k → Bool) :=
      { toFun := fun w a j => w (@finProdFinEquiv (k ^ k) k (a, j))
        invFun := fun u g =>
          let p := (@finProdFinEquiv (k ^ k) k).symm g
          u p.1 p.2
        left_inv := fun w => funext fun g => by
          dsimp only
          rw [Prod.mk.eta, (@finProdFinEquiv (k ^ k) k).apply_symm_apply]
        right_inv := fun u => funext fun a => funext fun j => by
          dsimp only
          rw [(@finProdFinEquiv (k ^ k) k).symm_apply_apply] }
    let p_grp : (Fin k → Bool) → ℝ := fun v => ∏ j : Fin k, θ (v j)
    let v1 : Fin k → Bool := fun _ => true
    let φ : (Fin k → Bool) → ℝ := fun v => if v = v1 then 0 else p_grp v
    have h_pgrp_sum : ∑ v : Fin k → Bool, p_grp v = 1 := by
      dsimp [p_grp]
      rw [← Fintype.prod_sum (fun (_ : Fin k) (b : Bool) => θ b)]
      exact Finset.prod_eq_one (fun _ _ => h_theta_sum)
    have h_pgrp_v1 : p_grp v1 = (1 / (k : ℝ)) ^ k := by
      simp [p_grp, v1, θ]
    have h_phi_sum : ∑ v : Fin k → Bool, φ v = 1 - (1 / (k : ℝ)) ^ k := by
      have h1 := (Finset.add_sum_erase (Finset.univ : Finset (Fin k → Bool)) p_grp
        (Finset.mem_univ v1)).symm
      have h2 := (Finset.add_sum_erase (Finset.univ : Finset (Fin k → Bool)) φ
        (Finset.mem_univ v1)).symm
      have h_erase_eq : ∑ v ∈ (Finset.univ : Finset (Fin k → Bool)).erase v1, φ v =
          ∑ v ∈ (Finset.univ : Finset (Fin k → Bool)).erase v1, p_grp v := by
        apply Finset.sum_congr rfl
        intro v hv
        have hne : v ≠ v1 := Finset.ne_of_mem_erase hv
        simp [φ, hne]
      have h_phi_v1 : φ v1 = 0 := by simp [φ]
      linarith
    have h_bern_factor : ∀ u : Fin (k ^ k) → Fin k → Bool,
        bernProb k (e.symm u) = ∏ a : Fin (k ^ k), p_grp (u a) := by
      intro u
      unfold bernProb
      have h_pc : (∏ p : Fin (k ^ k) × Fin k, θ (e.symm u (@finProdFinEquiv (k ^ k) k p))) =
          ∏ g : Fin (k ^ (k + 1)), θ (e.symm u g) :=
        Equiv.prod_comp (@finProdFinEquiv (k ^ k) k) (fun g => θ (e.symm u g))
      change (∏ g : Fin (k ^ (k + 1)), θ (e.symm u g)) = ∏ a : Fin (k ^ k), p_grp (u a)
      rw [← h_pc, Fintype.prod_prod_type]
      apply Finset.prod_congr rfl
      intro a _
      apply Finset.prod_congr rfl
      intro j _
      change θ (e (e.symm u) a j) = θ (u a j)
      rw [e.apply_symm_apply]
    have h_none_eq : ∑ w ∈ E_none, bernProb k w = (1 - (1 / (k : ℝ)) ^ k) ^ (k ^ k) := by
      rw [Finset.sum_filter]
      rw [← Equiv.sum_comp e.symm]
      have h_term : ∀ u : Fin (k ^ k) → Fin k → Bool,
          (if ¬ ∃ a : Fin (k ^ k), ∀ j : Fin k, e.symm u (@finProdFinEquiv (k ^ k) k (a, j)) = true
            then bernProb k (e.symm u) else 0) = ∏ a : Fin (k ^ k), φ (u a) := by
        intro u
        have h_cond : (∃ a : Fin (k ^ k),
            ∀ j : Fin k, e.symm u (@finProdFinEquiv (k ^ k) k (a, j)) = true) ↔
            (∃ a : Fin (k ^ k), u a = v1) := by
          refine exists_congr (fun a => ?_)
          constructor
          · intro ha
            funext j
            change u a j = true
            rw [← ha j]
            change u a j = e (e.symm u) a j
            rw [e.apply_symm_apply]
          · intro ha j
            change e (e.symm u) a j = true
            rw [e.apply_symm_apply, ha]
        by_cases hu : ∃ a : Fin (k ^ k), u a = v1
        · have hex : ∃ a : Fin (k ^ k), ∀ j : Fin k,
              e.symm u (@finProdFinEquiv (k ^ k) k (a, j)) = true := h_cond.mpr hu
          rw [if_neg (not_not.mpr hex)]
          rcases hu with ⟨a₀, ha₀⟩
          symm
          exact Finset.prod_eq_zero (Finset.mem_univ a₀) (by simp [φ, ha₀])
        · have hnex : ¬ ∃ a : Fin (k ^ k), ∀ j : Fin k,
              e.symm u (@finProdFinEquiv (k ^ k) k (a, j)) = true := fun h => hu (h_cond.mp h)
          rw [if_pos hnex, h_bern_factor u]
          apply Finset.prod_congr rfl
          intro a _
          have hne : u a ≠ v1 := fun h => hu ⟨a, h⟩
          simp [φ, hne]
      rw [Finset.sum_congr rfl (fun u _ => h_term u)]
      rw [← Fintype.prod_sum (fun (_ : Fin (k ^ k)) (v : Fin k → Bool) => φ v)]
      simp [h_phi_sum]
    let p : ℝ := (1 / (k : ℝ)) ^ k
    let m : ℕ := k ^ k
    have hp_pos : 0 < p := pow_pos h_inv_pos k
    have hp_lt1 : p < 1 := pow_lt_one₀ (le_of_lt h_inv_pos) h_inv_lt1 (by omega)
    have h1mp_nn : 0 ≤ 1 - p := by linarith
    have h_prod_le1 : (1 - p) ^ m * (1 + p) ^ m ≤ 1 := by
      calc (1 - p) ^ m * (1 + p) ^ m
        _ = ((1 - p) * (1 + p)) ^ m := (mul_pow (1 - p) (1 + p) m).symm
        _ ≤ 1 ^ m := by
            apply pow_le_pow_left₀
            · exact mul_nonneg h1mp_nn (by linarith)
            · nlinarith [sq_nonneg p]
        _ = 1 := one_pow m
    have h_bern_ineq : (2 : ℝ) ≤ (1 + p) ^ m := by
      have hb := one_add_mul_le_pow (a := p) (by linarith) m
      have h_mp : (m : ℝ) * p = 1 := by
        calc (m : ℝ) * p
          _ = (k : ℝ) ^ k * (1 / (k : ℝ)) ^ k := by simp [m, p]
          _ = ((k : ℝ) * (1 / (k : ℝ))) ^ k := (mul_pow (k : ℝ) (1 / (k : ℝ)) k).symm
          _ = 1 ^ k := by rw [mul_one_div_cancel hk_real_ne]
          _ = 1 := one_pow k
      linarith
    have h_pow_nn : 0 ≤ (1 - p) ^ m := pow_nonneg h1mp_nn m
    have h_two_mul : 2 * (1 - p) ^ m ≤ (1 - p) ^ m * (1 + p) ^ m := by
      have := mul_le_mul_of_nonneg_left h_bern_ineq h_pow_nn
      linarith
    have h_le_half : (1 - p) ^ m ≤ 1 / 2 := by linarith
    change ∑ w ∈ E_none, bernProb k w = (1 - p) ^ m at h_none_eq
    linarith

  
  let nonzeroWeights : Finset (Fin (k ^ (k + 1)) → Bool) :=
    Finset.univ.filter (fun w => ∃ g : Fin (k ^ (k + 1)), w g = true)
  let fam : List (Finset (Fin (k ^ (k + 1))) → ℝ) :=
    nonzeroWeights.toList.map (groupSubmodFn k)
  have hw1_mem : (fun _ : Fin (k ^ (k + 1)) => true) ∈ nonzeroWeights := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨⟨0, hn_pos⟩, rfl⟩⟩
  have h_nzw_nonempty : nonzeroWeights.Nonempty := ⟨_, hw1_mem⟩
  have h_fam_ne : fam ≠ [] := by
    intro h_nil
    have h_mem : groupSubmodFn k (fun _ => true) ∈ fam :=
      List.mem_map.mpr ⟨_, Finset.mem_toList.mpr hw1_mem, rfl⟩
    rw [h_nil] at h_mem
    exact List.not_mem_nil h_mem
  have h_fam_props : ∀ f ∈ fam, IsSubmodularReal f ∧ 0 < optValReal f := by
    intro f hf
    rcases List.mem_map.mp hf with ⟨w, hw_list, rfl⟩
    have hw_mem : w ∈ nonzeroWeights := Finset.mem_toList.mp hw_list
    have hw_ex : ∃ g, w g = true := (Finset.mem_filter.mp hw_mem).2
    exact ⟨h_submod w, h_opt_pos w hw_ex⟩

  refine ⟨k ^ (k + 1), hn_ge_N0, hn_ge3, fam, h_fam_ne, h_fam_props, ?_⟩
  intro alg

  
  have hA1 : ∀ (d : DetSelectionAlg (k ^ (k + 1))) (v : ItemValuation (k ^ (k + 1)))
      (π : Equiv.Perm (Fin (k ^ (k + 1)))) (m : ℕ) (hm : m ≤ k ^ (k + 1)),
      (runDetSelectionSteps d v π m hm).1 = arrivedList π m hm := by
    intro d v π m
    induction m with
    | zero => intro hm; rfl
    | succ m ih =>
        intro hm
        unfold runDetSelectionSteps arrivedList
        dsimp only
        rw [ih (Nat.le_of_succ_le hm)]

  have hA2 : ∀ (π : Equiv.Perm (Fin (k ^ (k + 1)))) (m : ℕ) (hm : m ≤ k ^ (k + 1))
      (g : Fin (k ^ (k + 1))),
      g ∈ (arrivedList π m hm).toFinset → ∃ i : Fin (k ^ (k + 1)), i.1 < m ∧ π i = g := by
    intro π m
    induction m with
    | zero =>
        intro hm g hg
        simp [arrivedList] at hg
    | succ m ih =>
        intro hm g hg
        rw [List.mem_toFinset] at hg
        unfold arrivedList at hg
        rw [List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · obtain ⟨i, hi_lt, hi_eq⟩ := ih (Nat.le_of_succ_le hm) g (List.mem_toFinset.mpr hg)
          exact ⟨i, Nat.lt_succ_of_lt hi_lt, hi_eq⟩
        · exact ⟨⟨m, hm⟩, Nat.lt_succ_self m, rfl⟩

  have hB_meas : ∀ (v : ItemValuation (k ^ (k + 1))) (π : Equiv.Perm (Fin (k ^ (k + 1))))
      (m : ℕ) (hm : m ≤ k ^ (k + 1)) (C : Finset (Fin (k ^ (k + 1)))),
      MeasurableSet {ω : alg.Seed | (runDetSelectionSteps (alg.det ω) v π m hm).2 = C} := by
    intro v π m
    induction m with
    | zero =>
        intro hm C
        unfold runDetSelectionSteps
        dsimp only
        by_cases hC : (∅ : Finset (Fin (k ^ (k + 1)))) = C <;> simp [hC]
    | succ m ih =>
        intro hm C
        let hm' := Nat.le_of_succ_le hm
        let prev₀ := arrivedList π m hm'
        let x := π ⟨m, hm⟩
        let acc_m : alg.Seed → Finset (Fin (k ^ (k + 1))) :=
          fun ω => (runDetSelectionSteps (alg.det ω) v π m hm').2
        have h_set_eq : {ω : alg.Seed | (runDetSelectionSteps (alg.det ω) v π (m + 1) hm).2 = C} =
            ⋃ (B : Finset (Fin (k ^ (k + 1)))) (b : Bool),
              ({ω : alg.Seed | acc_m ω = B} ∩
                ({ω : alg.Seed | (alg.det ω).step prev₀ x B (fun ⟨T, _⟩ => v T) = b} ∩
                  {ω : alg.Seed | (if b then insert x B else B) = C})) := by
          ext ω
          have h_pair : runDetSelectionSteps (alg.det ω) v π m hm' = (prev₀, acc_m ω) :=
            Prod.ext (hA1 (alg.det ω) v π m hm') rfl
          have h_step : (runDetSelectionSteps (alg.det ω) v π (m + 1) hm).2 =
              if (alg.det ω).step prev₀ x (acc_m ω) (fun ⟨T, _⟩ => v T)
              then insert x (acc_m ω) else acc_m ω := by
            unfold runDetSelectionSteps
            rw [h_pair]
          simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, h_step]
          constructor
          · intro hC
            exact ⟨acc_m ω, (alg.det ω).step prev₀ x (acc_m ω) (fun ⟨T, _⟩ => v T), rfl, rfl, hC⟩
          · rintro ⟨B, b, rfl, h_dec, hC⟩
            rw [h_dec]
            exact hC
        rw [h_set_eq]
        apply MeasurableSet.iUnion
        intro B
        apply MeasurableSet.iUnion
        intro b
        have h_const : MeasurableSet {ω : alg.Seed | (if b then insert x B else B) = C} := by
          by_cases hP : (if b then insert x B else B) = C <;> simp [hP]
        exact (ih hm' B).inter
          ((alg.meas_step prev₀ x B (fun ⟨T, _⟩ => v T) b).inter h_const)

  have hC_loc : ∀ (d : DetSelectionAlg (k ^ (k + 1))) (v₁ v₂ : ItemValuation (k ^ (k + 1)))
      (π : Equiv.Perm (Fin (k ^ (k + 1)))) (m : ℕ) (hm : m ≤ k ^ (k + 1)),
      (∀ T : Finset (Fin (k ^ (k + 1))), T ⊆ (arrivedList π m hm).toFinset → v₁ T = v₂ T) →
      runDetSelectionSteps d v₁ π m hm = runDetSelectionSteps d v₂ π m hm := by
    intro d v₁ v₂ π m
    induction m with
    | zero => intro hm _; rfl
    | succ m ih =>
        intro hm h_agree
        let hm' := Nat.le_of_succ_le hm
        let prev₀ := arrivedList π m hm'
        let x := π ⟨m, hm⟩
        have h_sub_prev : prev₀.toFinset ⊆ (arrivedList π (m + 1) hm).toFinset := by
          intro g hg
          rw [List.mem_toFinset] at hg ⊢
          unfold arrivedList
          exact List.mem_append_left [x] hg
        have h_ih := ih hm' (fun T hT => h_agree T (Finset.Subset.trans hT h_sub_prev))
        let acc₀ := (runDetSelectionSteps d v₂ π m hm').2
        have hp2 : runDetSelectionSteps d v₂ π m hm' = (prev₀, acc₀) :=
          Prod.ext (hA1 d v₂ π m hm') rfl
        have hp1 : runDetSelectionSteps d v₁ π m hm' = (prev₀, acc₀) :=
          h_ih.trans hp2
        have h_oracles :
            (fun (⟨T, _⟩ : {T : Finset (Fin (k ^ (k + 1))) // T ⊆ insert x prev₀.toFinset}) => v₁ T) =
            (fun ⟨T, _⟩ => v₂ T) := by
          funext ⟨T, hT⟩
          apply h_agree T
          intro g hg
          have hg' := hT hg
          rw [Finset.mem_insert, List.mem_toFinset] at hg'
          rw [List.mem_toFinset]
          unfold arrivedList
          rw [List.mem_append, List.mem_singleton]
          exact hg'.symm
        unfold runDetSelectionSteps
        rw [hp1, hp2]
        dsimp only
        rw [h_oracles]

  have hD_pers : ∀ (d : DetSelectionAlg (k ^ (k + 1))) (v : ItemValuation (k ^ (k + 1)))
      (π : Equiv.Perm (Fin (k ^ (k + 1)))) (t r : Fin (k ^ (k + 1))),
      r ≤ t → ∀ (m : ℕ) (hm : m ≤ k ^ (k + 1)), t.1 + 1 ≤ m →
      (π r ∈ (runDetSelectionSteps d v π m hm).2 ↔
        π r ∈ (runDetSelectionSteps d v π (t.1 + 1) t.2).2) := by
    intro d v π t r hrt m
    induction m with
    | zero => intro hm htm; omega
    | succ m ih =>
        intro hm htm
        by_cases hmt : m = t.1
        · subst hmt
          rfl
        · have htm' : t.1 + 1 ≤ m := by omega
          let hm' := Nat.le_of_succ_le hm
          let prev₀ := arrivedList π m hm'
          let acc₀ := (runDetSelectionSteps d v π m hm').2
          have hp : runDetSelectionSteps d v π m hm' = (prev₀, acc₀) :=
            Prod.ext (hA1 d v π m hm') rfl
          have h_step : (runDetSelectionSteps d v π (m + 1) hm).2 =
              if d.step prev₀ (π ⟨m, hm⟩) acc₀ (fun ⟨T, _⟩ => v T)
              then insert (π ⟨m, hm⟩) acc₀ else acc₀ := by
            unfold runDetSelectionSteps
            rw [hp]
          have h_ne : π r ≠ π ⟨m, hm⟩ := by
            intro h_eq
            have h_fin := π.injective h_eq
            have h_val : r.1 = m := congrArg Fin.val h_fin
            have : r.1 ≤ t.1 := hrt
            omega
          have h_iff_one : π r ∈ (runDetSelectionSteps d v π (m + 1) hm).2 ↔ π r ∈ acc₀ := by
            rw [h_step]
            split_ifs
            · simp [h_ne]
            · rfl
          exact h_iff_one.trans (ih hm' htm')

  have h_fh_nonneg : ∀ π w t, 0 ≤ firstHitProb k alg π w t := by
    intro π w t
    unfold firstHitProb
    exact Finset.sum_nonneg (fun _ _ => MeasureTheory.measureReal_nonneg)

  have h_fh_sum_le1 : ∀ π w, ∑ t : Fin (k ^ (k + 1)), firstHitProb k alg π w t ≤ 1 := by
    intro π w
    let vw : ItemValuation (k ^ (k + 1)) := fun T => ((groupSubmodFn k w T : ℝ) : WithBot ℝ)
    let Ew : Finset (Fin (k ^ (k + 1))) → Set alg.Seed :=
      fun S => {ω | runDetSelection (alg.det ω) vw π = S}
    let Ft : Fin (k ^ (k + 1)) → Finset (Finset (Fin (k ^ (k + 1)))) :=
      fun t => Finset.univ.filter (fun S => firstHit w π S t)
    have hFt_disj :
        (↑(Finset.univ : Finset (Fin (k ^ (k + 1)))) : Set (Fin (k ^ (k + 1)))).PairwiseDisjoint Ft := by
      intro t₁ _ t₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro S hS1 hS2
      rw [Finset.mem_filter] at hS1 hS2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hS2.2.2 t₁ hlt hS1.2.1
      · exact hS1.2.2 t₂ hgt hS2.2.1
    have h_sum_le : ∑ t : Fin (k ^ (k + 1)), firstHitProb k alg π w t ≤
        ∑ S : Finset (Fin (k ^ (k + 1))), alg.seedMeasure.real (Ew S) := by
      change ∑ t ∈ Finset.univ, ∑ S ∈ Ft t, alg.seedMeasure.real (Ew S) ≤
        ∑ S ∈ Finset.univ, alg.seedMeasure.real (Ew S)
      rw [← Finset.sum_biUnion hFt_disj]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => MeasureTheory.measureReal_nonneg)
    have hEw_disj : Pairwise (Function.onFun Disjoint Ew) := by
      intro S₁ S₂ hne
      rw [Function.onFun, Set.disjoint_left]
      intro ω h1 h2
      exact hne (h1.symm.trans h2)
    have hEw_meas : ∀ S, MeasurableSet (Ew S) :=
      fun S => hB_meas vw π (k ^ (k + 1)) (le_refl _) S
    have hEw_sum : ∑ S : Finset (Fin (k ^ (k + 1))), alg.seedMeasure.real (Ew S) = 1 := by
      rw [← MeasureTheory.measureReal_iUnion_fintype hEw_disj hEw_meas]
      have h_univ : (⋃ S, Ew S) = Set.univ := by
        ext ω
        simp [Ew]
      rw [h_univ, MeasureTheory.probReal_univ]
    linarith

  have h_fh_indep : ∀ (π : Equiv.Perm (Fin (k ^ (k + 1)))) (t s : Fin (k ^ (k + 1))),
      t < s → ∀ (w : Fin (k ^ (k + 1)) → Bool) (b : Bool),
      firstHitProb k alg π (Function.update w (π s) b) t = firstHitProb k alg π w t := by
    have h_fh_set : ∀ (π : Equiv.Perm (Fin (k ^ (k + 1)))) (w₀ : Fin (k ^ (k + 1)) → Bool)
        (t : Fin (k ^ (k + 1))),
        firstHitProb k alg π w₀ t = alg.seedMeasure.real
          {ω | firstHit w₀ π (runDetSelection (alg.det ω)
            (fun T => ((groupSubmodFn k w₀ T : ℝ) : WithBot ℝ)) π) t} := by
      intro π w₀ t
      let vw₀ : ItemValuation (k ^ (k + 1)) := fun T => ((groupSubmodFn k w₀ T : ℝ) : WithBot ℝ)
      let Ew₀ : Finset (Fin (k ^ (k + 1))) → Set alg.Seed :=
        fun S => {ω | runDetSelection (alg.det ω) vw₀ π = S}
      let Ft₀ := (Finset.univ : Finset (Finset (Fin (k ^ (k + 1))))).filter (fun S => firstHit w₀ π S t)
      have h_disj : (↑Ft₀ : Set (Finset (Fin (k ^ (k + 1))))).PairwiseDisjoint Ew₀ := by
        intro S₁ _ S₂ _ hne
        rw [Function.onFun, Set.disjoint_left]
        intro ω h1 h2
        exact hne (h1.symm.trans h2)
      have h_meas : ∀ S ∈ Ft₀, MeasurableSet (Ew₀ S) :=
        fun S _ => hB_meas vw₀ π (k ^ (k + 1)) (le_refl _) S
      unfold firstHitProb
      change ∑ S ∈ Ft₀, alg.seedMeasure.real (Ew₀ S) = _
      rw [← MeasureTheory.measureReal_biUnion_finset h_disj h_meas]
      congr 1
      ext ω
      simp [Ew₀, Ft₀, vw₀]

    intro π t s hts w b
    let w' := Function.update w (π s) b
    rw [h_fh_set π w' t, h_fh_set π w t]
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq]
    let vw : ItemValuation (k ^ (k + 1)) := fun T => ((groupSubmodFn k w T : ℝ) : WithBot ℝ)
    let vw' : ItemValuation (k ^ (k + 1)) := fun T => ((groupSubmodFn k w' T : ℝ) : WithBot ℝ)
    have h_step_eq : runDetSelectionSteps (alg.det ω) vw' π (t.1 + 1) t.2 =
        runDetSelectionSteps (alg.det ω) vw π (t.1 + 1) t.2 := by
      apply hC_loc (alg.det ω) vw' vw π (t.1 + 1) t.2
      intro T hT
      have h_f_eq : groupSubmodFn k w' T = groupSubmodFn k w T := by
        unfold groupSubmodFn
        congr 1
        apply Finset.sum_congr rfl
        intro g hg
        obtain ⟨i, hi_lt, rfl⟩ := hA2 π (t.1 + 1) t.2 g (hT hg)
        have h_ne : π i ≠ π s := by
          intro h_eq
          have h_fin := π.injective h_eq
          have h_val : i.1 = s.1 := congrArg Fin.val h_fin
          have : t.1 < s.1 := hts
          omega
        simp [w', h_ne]
      simp [vw', vw, h_f_eq]
    have h_w_prefix : ∀ r : Fin (k ^ (k + 1)), r ≤ t → w' (π r) = w (π r) := by
      intro r hrt
      have h_ne : π r ≠ π s := by
        intro h_eq
        have h_fin := π.injective h_eq
        have h_val : r.1 = s.1 := congrArg Fin.val h_fin
        have : r.1 ≤ t.1 := hrt
        have : t.1 < s.1 := hts
        omega
      simp [w', h_ne]
    have h_mem_w' : ∀ r : Fin (k ^ (k + 1)), r ≤ t →
        (π r ∈ runDetSelection (alg.det ω) vw' π ↔
          π r ∈ (runDetSelectionSteps (alg.det ω) vw π (t.1 + 1) t.2).2) := by
      intro r hrt
      unfold runDetSelection
      rw [hD_pers (alg.det ω) vw' π t r hrt (k ^ (k + 1)) (le_refl _) t.2, h_step_eq]
    have h_mem_w : ∀ r : Fin (k ^ (k + 1)), r ≤ t →
        (π r ∈ runDetSelection (alg.det ω) vw π ↔
          π r ∈ (runDetSelectionSteps (alg.det ω) vw π (t.1 + 1) t.2).2) := by
      intro r hrt
      unfold runDetSelection
      exact hD_pers (alg.det ω) vw π t r hrt (k ^ (k + 1)) (le_refl _) t.2
    unfold firstHit
    constructor
    · rintro ⟨⟨htS, htw⟩, hmin⟩
      refine ⟨⟨(h_mem_w t (le_refl t)).mpr ((h_mem_w' t (le_refl t)).mp htS), ?_⟩, ?_⟩
      · rwa [h_w_prefix t (le_refl t)] at htw
      · intro r hrt ⟨hrS, hrw⟩
        apply hmin r hrt
        refine ⟨(h_mem_w' r (le_of_lt hrt)).mpr ((h_mem_w r (le_of_lt hrt)).mp hrS), ?_⟩
        rwa [h_w_prefix r (le_of_lt hrt)]
    · rintro ⟨⟨htS, htw⟩, hmin⟩
      refine ⟨⟨(h_mem_w' t (le_refl t)).mpr ((h_mem_w t (le_refl t)).mp htS), ?_⟩, ?_⟩
      · rwa [h_w_prefix t (le_refl t)]
      · intro r hrt ⟨hrS, hrw⟩
        apply hmin r hrt
        refine ⟨(h_mem_w r (le_of_lt hrt)).mpr ((h_mem_w' r (le_of_lt hrt)).mp hrS), ?_⟩
        rwa [h_w_prefix r (le_of_lt hrt)] at hrw

  
  have h_perm_bound : ∀ π : Equiv.Perm (Fin (k ^ (k + 1))),
      ∑ w : Fin (k ^ (k + 1)) → Bool,
        bernProb k w * (∑ t : Fin (k ^ (k + 1)), firstHitProb k alg π w t * laterSameGroup k w π t) ≤
        2 - 1 / (k : ℝ) := by
    intro π
    have h_swap_sum :
        ∑ w : Fin (k ^ (k + 1)) → Bool,
          bernProb k w * (∑ t : Fin (k ^ (k + 1)), firstHitProb k alg π w t * laterSameGroup k w π t) =
        ∑ t : Fin (k ^ (k + 1)), ∑ w : Fin (k ^ (k + 1)) → Bool,
          bernProb k w * (firstHitProb k alg π w t * laterSameGroup k w π t) := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    rw [h_swap_sum]
    have h_per_t : ∀ t : Fin (k ^ (k + 1)),
        ∑ w : Fin (k ^ (k + 1)) → Bool,
          bernProb k w * (firstHitProb k alg π w t * laterSameGroup k w π t) ≤
        (2 - 1 / (k : ℝ)) * (∑ w : Fin (k ^ (k + 1)) → Bool, bernProb k w * firstHitProb k alg π w t) := by
      intro t
      let Lt := (Finset.univ : Finset (Fin (k ^ (k + 1)))).filter
        (fun s => t < s ∧ groupIdx k (π s) = groupIdx k (π t))
      let Mt := ∑ w : Fin (k ^ (k + 1)) → Bool, bernProb k w * firstHitProb k alg π w t
      have hMt_nn : 0 ≤ Mt :=
        Finset.sum_nonneg (fun w _ => mul_nonneg (le_of_lt (h_bern_pos w)) (h_fh_nonneg π w t))
      have h_expand :
          ∑ w : Fin (k ^ (k + 1)) → Bool,
            bernProb k w * (firstHitProb k alg π w t * laterSameGroup k w π t) =
          Mt + ∑ s ∈ Lt, ∑ w : Fin (k ^ (k + 1)) → Bool,
            bernProb k w * firstHitProb k alg π w t * (if w (π s) then (1 : ℝ) else 0) := by
        have h1 : ∀ w : Fin (k ^ (k + 1)) → Bool,
            bernProb k w * (firstHitProb k alg π w t * laterSameGroup k w π t) =
            bernProb k w * firstHitProb k alg π w t +
              ∑ s ∈ Lt, bernProb k w * firstHitProb k alg π w t * (if w (π s) then (1 : ℝ) else 0) := by
          intro w
          unfold laterSameGroup
          change bernProb k w * (firstHitProb k alg π w t *
            (1 + ∑ s ∈ Lt, if w (π s) then (1 : ℝ) else 0)) = _
          rw [← mul_assoc, mul_add, mul_one, Finset.mul_sum]
        simp_rw [h1]
        rw [Finset.sum_add_distrib, Finset.sum_comm]
      have h_coord : ∀ s ∈ Lt,
          ∑ w : Fin (k ^ (k + 1)) → Bool,
            bernProb k w * firstHitProb k alg π w t * (if w (π s) then (1 : ℝ) else 0) =
          (1 / (k : ℝ)) * Mt := by
        intro s hs
        have hts : t < s := (Finset.mem_filter.mp hs).2.1
        let x := π s
        let swap_x : (Fin (k ^ (k + 1)) → Bool) ≃ (Fin (k ^ (k + 1)) → Bool) :=
          { toFun := fun w => Function.update w x (!w x)
            invFun := fun w => Function.update w x (!w x)
            left_inv := fun w => by
              ext g
              by_cases h : g = x
              · subst h; simp [Function.update]
              · simp [Function.update, h]
            right_inv := fun w => by
              ext g
              by_cases h : g = x
              · subst h; simp [Function.update]
              · simp [Function.update, h] }
        let f1 : (Fin (k ^ (k + 1)) → Bool) → ℝ :=
          fun w => bernProb k w * firstHitProb k alg π w t * (if w x then (1 : ℝ) else 0)
        let f2 : (Fin (k ^ (k + 1)) → Bool) → ℝ :=
          fun w => bernProb k w * firstHitProb k alg π w t
        have h_pair_id : ∀ w : Fin (k ^ (k + 1)) → Bool,
            f1 w + f1 (swap_x w) = (1 / (k : ℝ)) * (f2 w + f2 (swap_x w)) := by
          intro w
          dsimp only [f1, f2]
          let P := ∏ g ∈ (Finset.univ : Finset (Fin (k ^ (k + 1)))).erase x, θ (w g)
          have hbw : bernProb k w = θ (w x) * P := by
            unfold bernProb
            exact (Finset.mul_prod_erase Finset.univ (fun g => θ (w g)) (Finset.mem_univ x)).symm
          have hbs : bernProb k (swap_x w) = θ (!w x) * P := by
            unfold bernProb
            have h1 := (Finset.mul_prod_erase Finset.univ (fun g => θ (swap_x w g))
              (Finset.mem_univ x)).symm
            change bernProb k (swap_x w) = _ at h1
            unfold bernProb at h1
            rw [h1]
            have hx_val : swap_x w x = !w x := by simp [swap_x]
            have h_er : ∏ g ∈ (Finset.univ : Finset (Fin (k ^ (k + 1)))).erase x, θ (swap_x w g) = P := by
              apply Finset.prod_congr rfl
              intro g hg
              have hne : g ≠ x := Finset.ne_of_mem_erase hg
              simp [swap_x, hne]
            rw [hx_val, h_er]
          have hq_eq : firstHitProb k alg π (swap_x w) t = firstHitProb k alg π w t :=
            h_fh_indep π t s hts w (!w x)
          have hwx_swap : swap_x w x = !w x := by simp [swap_x]
          rw [hbw, hbs, hq_eq, hwx_swap]
          cases w x <;> dsimp [θ] <;> ring
        have h_sum2 := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin (k ^ (k + 1)) → Bool))) rfl
          (fun w _ => h_pair_id w)
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib] at h_sum2
        have hs1 : (∑ w : Fin (k ^ (k + 1)) → Bool, f1 (swap_x w)) = ∑ w, f1 w :=
          Equiv.sum_comp swap_x f1
        have hs2 : (∑ w : Fin (k ^ (k + 1)) → Bool, f2 (swap_x w)) = ∑ w, f2 w :=
          Equiv.sum_comp swap_x f2
        rw [hs1, hs2] at h_sum2
        change (∑ w : Fin (k ^ (k + 1)) → Bool, f1 w) = (1 / (k : ℝ)) * (∑ w : Fin (k ^ (k + 1)) → Bool, f2 w)
        linarith
      have h_Lt_card : Lt.card + 1 ≤ k := by
        let a := groupIdx k (π t)
        let emb : Fin k ↪ Fin (k ^ (k + 1)) :=
          ⟨fun j => @finProdFinEquiv (k ^ k) k (a, j),
            fun j₁ j₂ h => (Prod.mk.inj ((@finProdFinEquiv (k ^ k) k).injective h)).2⟩
        let Ga : Finset (Fin (k ^ (k + 1))) := Finset.univ.map emb
        have h_not_mem : π t ∉ Lt.map π.toEmbedding := by
          rw [Finset.mem_map]
          rintro ⟨s, hs, h_eq⟩
          have hst : s = t := π.injective h_eq
          have hlt : t < s := (Finset.mem_filter.mp hs).2.1
          exact absurd (hst ▸ hlt) (lt_irrefl t)
        have h_sub : insert (π t) (Lt.map π.toEmbedding) ⊆ Ga := by
          intro y hy
          rw [Finset.mem_insert, Finset.mem_map] at hy
          have hy_grp : groupIdx k y = a := by
            rcases hy with rfl | ⟨s, hs, rfl⟩
            · rfl
            · exact (Finset.mem_filter.mp hs).2.2
          rw [Finset.mem_map]
          let p := (@finProdFinEquiv (k ^ k) k).symm y
          refine ⟨p.2, Finset.mem_univ _, ?_⟩
          have hp1 : p.1 = a := hy_grp
          change @finProdFinEquiv (k ^ k) k (a, p.2) = y
          rw [← hp1]
          exact (@finProdFinEquiv (k ^ k) k).apply_symm_apply y
        have h_le_Ga : (insert (π t) (Lt.map π.toEmbedding)).card ≤ Ga.card :=
          Finset.card_le_card h_sub
        have hGa_card : Ga.card = k := by simp [Ga]
        rw [Finset.card_insert_of_notMem h_not_mem, Finset.card_map, hGa_card] at h_le_Ga
        exact h_le_Ga
      have h_Lt_real : (Lt.card : ℝ) ≤ (k : ℝ) - 1 := by
        have : (Lt.card : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast h_Lt_card
        linarith
      rw [h_expand, Finset.sum_congr rfl h_coord, Finset.sum_const, nsmul_eq_mul]
      have h_coeff : 1 + (Lt.card : ℝ) * (1 / (k : ℝ)) ≤ 2 - 1 / (k : ℝ) := by
        have h_mul := mul_le_mul_of_nonneg_right h_Lt_real (le_of_lt h_inv_pos)
        have h_cancel : ((k : ℝ) - 1) * (1 / (k : ℝ)) = 1 - 1 / (k : ℝ) := by
          rw [sub_mul, one_mul, mul_one_div_cancel hk_real_ne]
        linarith
      have h_lhs_eq : Mt + (Lt.card : ℝ) * ((1 / (k : ℝ)) * Mt) =
          (1 + (Lt.card : ℝ) * (1 / (k : ℝ))) * Mt := by ring
      rw [h_lhs_eq]
      exact mul_le_mul_of_nonneg_right h_coeff hMt_nn

    calc ∑ t : Fin (k ^ (k + 1)), ∑ w : Fin (k ^ (k + 1)) → Bool,
          bernProb k w * (firstHitProb k alg π w t * laterSameGroup k w π t)
      _ ≤ ∑ t : Fin (k ^ (k + 1)),
          (2 - 1 / (k : ℝ)) * (∑ w : Fin (k ^ (k + 1)) → Bool, bernProb k w * firstHitProb k alg π w t) :=
          Finset.sum_le_sum (fun t _ => h_per_t t)
      _ = (2 - 1 / (k : ℝ)) * ∑ w : Fin (k ^ (k + 1)) → Bool,
          bernProb k w * (∑ t : Fin (k ^ (k + 1)), firstHitProb k alg π w t) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro w _
          rw [← Finset.mul_sum]
      _ ≤ (2 - 1 / (k : ℝ)) * ∑ w : Fin (k ^ (k + 1)) → Bool, bernProb k w * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          apply Finset.sum_le_sum
          intro w _
          exact mul_le_mul_of_nonneg_left (h_fh_sum_le1 π w) (le_of_lt (h_bern_pos w))
      _ = 2 - 1 / (k : ℝ) := by
          simp [h_bern_sum]

  
  let B : (Fin (k ^ (k + 1)) → Bool) → ℝ := fun w =>
    (1 / (Nat.factorial (k ^ (k + 1)) : ℝ)) *
      ∑ π : Equiv.Perm (Fin (k ^ (k + 1))),
        ∑ t : Fin (k ^ (k + 1)), firstHitProb k alg π w t * laterSameGroup k w π t

  have h_fact_pos : 0 < (Nat.factorial (k ^ (k + 1)) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (k ^ (k + 1))
  have h_fact_ne : (Nat.factorial (k ^ (k + 1)) : ℝ) ≠ 0 := ne_of_gt h_fact_pos

  have h_alg_le_B : ∀ w : Fin (k ^ (k + 1)) → Bool,
      expectedSelectionValReal alg (groupSubmodFn k w) ≤ B w := by
    intro w
    let vw : ItemValuation (k ^ (k + 1)) := fun T => ((groupSubmodFn k w T : ℝ) : WithBot ℝ)
    unfold expectedSelectionValReal algSelectionProb
    have h_rearr :
        ∑ S : Finset (Fin (k ^ (k + 1))),
          ((1 / (Nat.factorial (k ^ (k + 1)) : ℝ)) *
            ∑ π : Equiv.Perm (Fin (k ^ (k + 1))),
              alg.seedMeasure.real {ω | runDetSelection (alg.det ω) vw π = S}) *
            groupSubmodFn k w S =
        (1 / (Nat.factorial (k ^ (k + 1)) : ℝ)) *
          ∑ π : Equiv.Perm (Fin (k ^ (k + 1))),
            ∑ S : Finset (Fin (k ^ (k + 1))),
              alg.seedMeasure.real {ω | runDetSelection (alg.det ω) vw π = S} *
                groupSubmodFn k w S := by
      simp_rw [mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
    change ∑ S : Finset (Fin (k ^ (k + 1))),
        ((1 / (Nat.factorial (k ^ (k + 1)) : ℝ)) *
          ∑ π : Equiv.Perm (Fin (k ^ (k + 1))),
            alg.seedMeasure.real {ω | runDetSelection (alg.det ω) vw π = S}) *
          groupSubmodFn k w S ≤ B w
    rw [h_rearr]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro π _
    calc ∑ S : Finset (Fin (k ^ (k + 1))),
          alg.seedMeasure.real {ω | runDetSelection (alg.det ω) vw π = S} * groupSubmodFn k w S
      _ ≤ ∑ S : Finset (Fin (k ^ (k + 1))),
          alg.seedMeasure.real {ω | runDetSelection (alg.det ω) vw π = S} * upperScore k w π S := by
          apply Finset.sum_le_sum
          intro S _
          exact mul_le_mul_of_nonneg_left (h_pointwise w π S) MeasureTheory.measureReal_nonneg
      _ = ∑ t : Fin (k ^ (k + 1)), firstHitProb k alg π w t * laterSameGroup k w π t := by
          unfold upperScore firstHitProb
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro t _
          rw [Finset.sum_filter, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro S _
          split_ifs <;> ring

  have hB_nn : ∀ w : Fin (k ^ (k + 1)) → Bool, 0 ≤ B w := by
    intro w
    dsimp [B]
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro π _
    apply Finset.sum_nonneg
    intro t _
    exact mul_nonneg (h_fh_nonneg π w t) (h_later_nonneg w π t)

  have h_sum_alg :
      ∑ w ∈ nonzeroWeights, bernProb k w * expectedSelectionValReal alg (groupSubmodFn k w) ≤
      2 - 1 / (k : ℝ) := by
    calc ∑ w ∈ nonzeroWeights, bernProb k w * expectedSelectionValReal alg (groupSubmodFn k w)
      _ ≤ ∑ w ∈ nonzeroWeights, bernProb k w * B w := by
          apply Finset.sum_le_sum
          intro w _
          exact mul_le_mul_of_nonneg_left (h_alg_le_B w) (le_of_lt (h_bern_pos w))
      _ ≤ ∑ w : Fin (k ^ (k + 1)) → Bool, bernProb k w * B w := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun w _ _ => mul_nonneg (le_of_lt (h_bern_pos w)) (hB_nn w))
      _ = (1 / (Nat.factorial (k ^ (k + 1)) : ℝ)) *
          ∑ π : Equiv.Perm (Fin (k ^ (k + 1))),
            ∑ w : Fin (k ^ (k + 1)) → Bool,
              bernProb k w * (∑ t : Fin (k ^ (k + 1)), firstHitProb k alg π w t * laterSameGroup k w π t) := by
          have h_Bw : ∀ w : Fin (k ^ (k + 1)) → Bool,
              bernProb k w * B w =
              (1 / (Nat.factorial (k ^ (k + 1)) : ℝ)) *
                ∑ π : Equiv.Perm (Fin (k ^ (k + 1))),
                  bernProb k w * (∑ t : Fin (k ^ (k + 1)), firstHitProb k alg π w t * laterSameGroup k w π t) := by
            intro w
            dsimp [B]
            rw [← mul_assoc, mul_comm (bernProb k w), mul_assoc, Finset.mul_sum]
          simp_rw [h_Bw]
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ (1 / (Nat.factorial (k ^ (k + 1)) : ℝ)) *
          ∑ _π : Equiv.Perm (Fin (k ^ (k + 1))), (2 - 1 / (k : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum (fun π _ => h_perm_bound π)
      _ = 2 - 1 / (k : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
          rw [← mul_assoc, one_div_mul_cancel h_fact_ne, one_mul]

  have h_Efull_sub : E_full ⊆ nonzeroWeights := by
    intro w hw
    rcases (Finset.mem_filter.mp hw).2 with ⟨a, ha⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ w,
      ⟨@finProdFinEquiv (k ^ k) k (a, ⟨0, hk_pos⟩), ha ⟨0, hk_pos⟩⟩⟩

  have h_sum_opt :
      (k : ℝ) / 2 ≤ ∑ w ∈ nonzeroWeights, bernProb k w * optValReal (groupSubmodFn k w) := by
    calc (k : ℝ) / 2
      _ = (1 / 2 : ℝ) * (k : ℝ) := by ring
      _ ≤ (∑ w ∈ E_full, bernProb k w) * (k : ℝ) :=
          mul_le_mul_of_nonneg_right h_bern_full (le_of_lt hk_real_pos)
      _ = ∑ w ∈ E_full, bernProb k w * (k : ℝ) := Finset.sum_mul _ _ _
      _ ≤ ∑ w ∈ E_full, bernProb k w * optValReal (groupSubmodFn k w) := by
          apply Finset.sum_le_sum
          intro w hw
          rcases (Finset.mem_filter.mp hw).2 with ⟨a, ha⟩
          exact mul_le_mul_of_nonneg_left (h_opt_full w a ha) (le_of_lt (h_bern_pos w))
      _ ≤ ∑ w ∈ nonzeroWeights, bernProb k w * optValReal (groupSubmodFn k w) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg h_Efull_sub
            (fun w _ _ => mul_nonneg (le_of_lt (h_bern_pos w)) (h_opt_nonneg w))

  by_contra! h_contra
  have h_strict_each : ∀ w ∈ nonzeroWeights,
      bernProb k w * ((4 / (k : ℝ)) * optValReal (groupSubmodFn k w)) <
        bernProb k w * expectedSelectionValReal alg (groupSubmodFn k w) := by
    intro w hw
    have hf_mem : groupSubmodFn k w ∈ fam :=
      List.mem_map.mpr ⟨w, Finset.mem_toList.mpr hw, rfl⟩
    have h_gt := h_contra (groupSubmodFn k w) hf_mem
    have h_opt_nn := h_opt_nonneg w
    have h_ratio_opt :
        (4 / (k : ℝ)) * optValReal (groupSubmodFn k w) ≤
        8 * optValReal (groupSubmodFn k w) *
          (Real.log (Real.log ((k ^ (k + 1) : ℕ) : ℝ)) /
            Real.log ((k ^ (k + 1) : ℕ) : ℝ)) := by
      have h_mul := mul_le_mul_of_nonneg_left h_log_ratio h_opt_nn
      linarith
    exact mul_lt_mul_of_pos_left (lt_of_le_of_lt h_ratio_opt h_gt) (h_bern_pos w)

  have h_sum_lt := Finset.sum_lt_sum_of_nonempty h_nzw_nonempty h_strict_each
  have h_lhs_factor :
      ∑ w ∈ nonzeroWeights, bernProb k w * ((4 / (k : ℝ)) * optValReal (groupSubmodFn k w)) =
      (4 / (k : ℝ)) * ∑ w ∈ nonzeroWeights, bernProb k w * optValReal (groupSubmodFn k w) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [h_lhs_factor] at h_sum_lt
  have h_two_le :
      (2 : ℝ) ≤ (4 / (k : ℝ)) * ∑ w ∈ nonzeroWeights, bernProb k w * optValReal (groupSubmodFn k w) := by
    have h_mul := mul_le_mul_of_nonneg_left h_sum_opt (by positivity : (0 : ℝ) ≤ 4 / (k : ℝ))
    have h_eq2 : (4 / (k : ℝ)) * ((k : ℝ) / 2) = 2 := by
      field_simp [hk_real_ne]
      ring
    linarith
  linarith

end

end


section NamedResults

/-- **Proposition C.3 (`prop:signed-sub`, Signed submodular functions, `[BIK07, Rubinstein16]`)**:
There exists an absolute constant `c > 0` such that for arbitrarily large `n` (`∀ N₀, ∃ n ≥ N₀`),
there is a finite nonempty family of finite-valued submodular functions `f : 2^N → ℝ` with
`f(∅) = 0` and `OPT(f) > 0` on which every online algorithm satisfies
`E[f(A)] ≤ c · OPT(f) · log(log n) / log n` on some `f` in the family. -/
theorem prop_C_3_signed_sub :
    ∃ c : ℝ, 0 < c ∧
      ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧ 4 ≤ n ∧
        ∃ fam : List (Finset (Fin n) → ℝ),
          fam ≠ [] ∧
          (∀ f ∈ fam, IsSubmodularReal f ∧ 0 < optValReal f) ∧
          ∀ alg : OnlineSelectionAlg n,
            ∃ f ∈ fam,
              expectedSelectionValReal alg f ≤
                c * optValReal f * (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) :=
by
  obtain ⟨c, hc, hmain⟩ := prop_signed_submodular_impossibility
  refine ⟨c, hc, fun N₀ => ?_⟩
  obtain ⟨n, hn1, _, fam, hfam⟩ := hmain (max N₀ 4)
  exact ⟨n, le_trans (le_max_left N₀ 4) hn1, le_trans (le_max_right N₀ 4) hn1, fam, hfam⟩

end NamedResults

end GrossSubstitutesWelfare
