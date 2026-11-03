import GrossSubstitutesWelfare.Defs
import GrossSubstitutesWelfare.Preliminaries.SafeSupportAndCutoff

set_option maxHeartbeats 4000000

/-!
# Section 2.1 & Section 4.1: Supremal Convolution, Disposal Envelopes & Canonical GS Examples

This file formalizes from first principles:
- **Section 2.1 (`[PaesLeme17]`)**: Non-closure of gross substitutes valuations under pointwise addition
  (`gs_not_closed_under_addition`).
- **Section 2.1 Example 2.4 (`ex:gs`, `[LLN06, Murota03]`)**: Matroid rank valuations
  (`ex_2_4_matroid_rank`), weighted matroid rank valuations (`ex_2_4_weighted_matroid_rank`),
  bipartite assignment valuations (`ex_2_4_assignment`), and discretely concave cardinality
  valuations (`ex_2_4_concave_cardinality_with_prices`), together with modular price shifts.
- **Section 4.1 (`[Murota03]`)**: Closure of gross substitutes valuations under supremal convolution
  `(u □ w)(S) = max_{T ⊆ S} [u(T) + w(S \ T)]` (`murota_gs_convolution`), proved from the exchange
  axiom without external discrete convex analysis dependencies.
- **Section 4.1 Lemma 4.2 (`lem:envelope`)**: Disposal envelope `v̄(S) = max_{T ⊆ S} v(T) = (v □ 0)(S)`
  is a finite-valued, nonnegative, nondecreasing gross substitutes valuation (hence submodular by
  `[GS99]`), and replacing valuations by their disposal envelopes preserves offline optimal welfare
  `OPT` (`lem_4_2_envelope`, `lem_4_2_envelope_optWelfare`).
-/

namespace GrossSubstitutesWelfare

open Classical

noncomputable section

namespace Internal

def unitDemandVal {n : ℕ} (A : Finset (Fin n)) : ItemValuation n :=
  fun S => if (S ∩ A).Nonempty then ((1 : ℝ) : WithBot ℝ) else ((0 : ℝ) : WithBot ℝ)

def lastSlotVal {n k : ℕ} (w : Fin n → Fin (k + 1) → ℝ) : ItemValuation n :=
  fun T => if T.card ≤ 1 then ((∑ g ∈ T, w g (Fin.last k) : ℝ) : WithBot ℝ) else ⊥

def pullbackVal {n m : ℕ} (e : Fin n ↪ Fin m) (V : ItemValuation m) : ItemValuation n :=
  fun S => V (S.map e)

def pairBase {N : ℕ} (a b : Fin N) (S : Finset (Fin N)) : Finset (Fin N) :=
  (S.erase a).erase b

def mergePair {N : ℕ} (a b : Fin N) (f : ItemValuation N) : ItemValuation N :=
  fun S =>
    if a ∈ S then max (f (insert a (pairBase a b S))) (f (insert b (pairBase a b S)))
    else f (pairBase a b S)

def convUlow {n : ℕ} (k : ℕ) (S : Finset (Fin (n + n))) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val < k ∧ Fin.castAdd n i ∈ S)

def convWlow {n : ℕ} (k : ℕ) (S : Finset (Fin (n + n))) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val < k ∧ Fin.natAdd n i ∈ S)

def convMhigh {n : ℕ} (k : ℕ) (S : Finset (Fin (n + n))) : Finset (Fin n) :=
  Finset.univ.filter (fun i => k ≤ i.val ∧ Fin.castAdd n i ∈ S)

def convStageVal {n : ℕ} (u w : ItemValuation n) (k : ℕ) : ItemValuation (n + n) :=
  fun S =>
    (convMhigh k S).powerset.sup (fun T =>
      u (convUlow k S ∪ T) + w (convWlow k S ∪ (convMhigh k S \ T)))

theorem thm_gs_convolution_and_examples :
    -- (1) Sums of GS valuations need not be GS
    (∃ v₁ v₂ : ItemValuation 3,
      IsFiniteValuation v₁ ∧ IsNonnegValuation v₁ ∧ IsGSValuation v₁ ∧
      IsFiniteValuation v₂ ∧ IsNonnegValuation v₂ ∧ IsGSValuation v₂ ∧
      ¬ IsGSValuation (fun S => v₁ S + v₂ S)) ∧
    -- (2) [GS99]: Every finite-valued GS valuation is submodular
    (∀ n (v : ItemValuation n),
      IsGSValuation v → IsFiniteValuation v → IsSubmodularReal (realVal v)) ∧
    -- (3) [Murota03]: Supremal convolution of GS valuations is GS
    (∀ n (u w : ItemValuation n),
      IsGSValuation u → IsGSValuation w → IsGSValuation (valConvolution u w)) ∧
    -- (4) Lemma 4.2 (lem:envelope): Disposal envelope is a finite, nonneg, monotone GS valuation
    (∀ n (v : ItemValuation n), IsGSValuation v →
      disposalEnvelopeVal v = valConvolution v (zeroVal n) ∧
      IsFiniteValuation (disposalEnvelopeVal v) ∧
      IsNonnegValuation (disposalEnvelopeVal v) ∧
      IsMonotoneValuation (disposalEnvelopeVal v) ∧
      IsGSValuation (disposalEnvelopeVal v) ∧
      IsSubmodularReal (disposalEnvelope v)) ∧
    (∀ n m (v : Fin m → ItemValuation n), (∀ i, IsGSValuation (v i)) →
      optWelfare (fun i => disposalEnvelopeVal (v i)) = optWelfare v) ∧
    -- (5) Example 2.4 (ex:gs): Rank, weighted rank, assignment, concave cardinality + modular shifts
    (∀ n (M : Matroid (Fin n)) (p : Fin n → ℝ),
      IsGSValuation (matroidRankVal M) ∧
      IsGSValuation (addModular (matroidRankVal M) (fun g => - p g))) ∧
    (∀ n (M : Matroid (Fin n)) (w p : Fin n → ℝ),
      IsGSValuation (weightedMatroidRankVal M w) ∧
      IsGSValuation (addModular (weightedMatroidRankVal M w) (fun g => - p g))) ∧
    (∀ n k (w : Fin n → Fin k → ℝ) (p : Fin n → ℝ),
      IsGSValuation (assignmentVal w) ∧
      IsGSValuation (addModular (assignmentVal w) (fun g => - p g))) ∧
    (∀ n (h : ℕ → ℝ) (p : Fin n → ℝ), h 0 = 0 →
      (∀ r : ℕ, h (r + 2) - h (r + 1) ≤ h (r + 1) - h r) →
      let vc : ItemValuation n := fun S => ((h S.card : ℝ) : WithBot ℝ)
      IsGSValuation vc ∧ IsGSValuation (addModular vc (fun g => - p g))) :=
by
  have h_wb_add_mono : ∀ {a₁ a₂ b₁ b₂ : WithBot ℝ}, a₁ ≤ b₁ → a₂ ≤ b₂ → a₁ + a₂ ≤ b₁ + b₂ := by
    intro a₁ a₂ b₁ b₂ h1 h2
    cases a₁ with
    | bot => simp
    | coe r₁ =>
      cases a₂ with
      | bot => simp
      | coe r₂ =>
        cases b₁ with
        | bot => exact absurd h1 (by simp)
        | coe s₁ =>
          cases b₂ with
          | bot => exact absurd h2 (by simp)
          | coe s₂ =>
            rw [WithBot.coe_le_coe] at h1 h2
            rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
            linarith

  
  have h_ud_fin : ∀ {n} (A : Finset (Fin n)), IsFiniteValuation (unitDemandVal A) := by
    intro n A S
    dsimp [unitDemandVal]
    split_ifs <;> exact WithBot.coe_ne_bot

  have h_ud_nn : ∀ {n} (A : Finset (Fin n)), IsNonnegValuation (unitDemandVal A) := by
    intro n A S
    dsimp [unitDemandVal]
    split_ifs <;> norm_num

  have h_ud_mono : ∀ {n} (A : Finset (Fin n)) {S T : Finset (Fin n)},
      S ⊆ T → unitDemandVal A S ≤ unitDemandVal A T := by
    intro n A S T hST
    dsimp [unitDemandVal]
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (h1.mono (Finset.inter_subset_inter_right hST)) h2
    · norm_num
    · exact le_rfl

  have h_ud_gs : ∀ {n} (A : Finset (Fin n)), IsGSValuation (unitDemandVal A) := by
    intro n A
    refine ⟨by simp [unitDemandVal], ?_⟩
    intro X Y _ _ x hx
    obtain ⟨hxX, hxY⟩ := Finset.mem_sdiff.mp hx
    by_cases hXA : (X ∩ A).Nonempty
    · by_cases hXeA : (X.erase x ∩ A).Nonempty
      · apply le_max_of_le_left
        have h1 : unitDemandVal A X = ((1 : ℝ) : WithBot ℝ) := if_pos hXA
        have h2 : unitDemandVal A (X.erase x) = ((1 : ℝ) : WithBot ℝ) := if_pos hXeA
        rw [h1, h2]
        exact h_wb_add_mono le_rfl (h_ud_mono A (Finset.subset_insert x Y))
      · obtain ⟨z, hz⟩ := hXA
        obtain ⟨hzX, hzA⟩ := Finset.mem_inter.mp hz
        have hzx : z = x := by
          by_contra hne
          exact hXeA ⟨z, Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr ⟨hne, hzX⟩, hzA⟩⟩
        subst hzx
        by_cases hYA : (Y ∩ A).Nonempty
        · obtain ⟨y, hy⟩ := hYA
          obtain ⟨hyY, hyA⟩ := Finset.mem_inter.mp hy
          have hyx : y ≠ z := fun h => hxY (h ▸ hyY)
          have hyX : y ∉ X := fun hm =>
            hXeA ⟨y, Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr ⟨hyx, hm⟩, hyA⟩⟩
          have hy_sdiff : y ∈ Y \ X := Finset.mem_sdiff.mpr ⟨hyY, hyX⟩
          apply le_max_of_le_right
          refine le_trans ?_ (Finset.le_sup (f := fun w =>
            unitDemandVal A (insert w (X.erase z)) + unitDemandVal A ((insert z Y).erase w)) hy_sdiff)
          dsimp only
          have h1 : unitDemandVal A X = ((1 : ℝ) : WithBot ℝ) := if_pos ⟨z, hz⟩
          have h2 : unitDemandVal A Y = ((1 : ℝ) : WithBot ℝ) := if_pos ⟨y, hy⟩
          have h3 : unitDemandVal A (insert y (X.erase z)) = ((1 : ℝ) : WithBot ℝ) :=
            if_pos ⟨y, Finset.mem_inter.mpr ⟨Finset.mem_insert_self y _, hyA⟩⟩
          have h4 : unitDemandVal A ((insert z Y).erase y) = ((1 : ℝ) : WithBot ℝ) :=
            if_pos ⟨z, Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr ⟨hyx.symm, Finset.mem_insert_self z Y⟩, hzA⟩⟩
          rw [h1, h2, h3, h4]
        · apply le_max_of_le_left
          have h1 : unitDemandVal A X = ((1 : ℝ) : WithBot ℝ) := if_pos ⟨z, hz⟩
          have h2 : unitDemandVal A Y = ((0 : ℝ) : WithBot ℝ) := if_neg hYA
          have h3 : unitDemandVal A (X.erase z) = ((0 : ℝ) : WithBot ℝ) := if_neg hXeA
          have h4 : unitDemandVal A (insert z Y) = ((1 : ℝ) : WithBot ℝ) :=
            if_pos ⟨z, Finset.mem_inter.mpr ⟨Finset.mem_insert_self z Y, hzA⟩⟩
          rw [h1, h2, h3, h4, ← WithBot.coe_add, ← WithBot.coe_add]
          norm_num
    · apply le_max_of_le_left
      have hXeA : ¬ (X.erase x ∩ A).Nonempty :=
        fun h => hXA (h.mono (Finset.inter_subset_inter_right (Finset.erase_subset x X)))
      have h1 : unitDemandVal A X = ((0 : ℝ) : WithBot ℝ) := if_neg hXA
      have h2 : unitDemandVal A (X.erase x) = ((0 : ℝ) : WithBot ℝ) := if_neg hXeA
      rw [h1, h2]
      exact h_wb_add_mono le_rfl (h_ud_mono A (Finset.subset_insert x Y))

  have h_part1 : ∃ v₁ v₂ : ItemValuation 3,
      IsFiniteValuation v₁ ∧ IsNonnegValuation v₁ ∧ IsGSValuation v₁ ∧
      IsFiniteValuation v₂ ∧ IsNonnegValuation v₂ ∧ IsGSValuation v₂ ∧
      ¬ IsGSValuation (fun S => v₁ S + v₂ S) := by
    let A1 : Finset (Fin 3) := {0, 2}
    let A2 : Finset (Fin 3) := {1, 2}
    let v1 := unitDemandVal A1
    let v2 := unitDemandVal A2
    refine ⟨v1, v2, h_ud_fin A1, h_ud_nn A1, h_ud_gs A1, h_ud_fin A2, h_ud_nn A2, h_ud_gs A2, ?_⟩
    intro hgs
    let X : Finset (Fin 3) := {0, 1}
    let Y : Finset (Fin 3) := {2}
    have hvX : v1 X + v2 X = ((2 : ℝ) : WithBot ℝ) := by
      have h1 : (X ∩ A1).Nonempty := ⟨0, by decide⟩
      have h2 : (X ∩ A2).Nonempty := ⟨1, by decide⟩
      simp only [v1, v2, unitDemandVal, if_pos h1, if_pos h2, ← WithBot.coe_add]
      norm_num
    have hvY : v1 Y + v2 Y = ((2 : ℝ) : WithBot ℝ) := by
      have h1 : (Y ∩ A1).Nonempty := ⟨2, by decide⟩
      have h2 : (Y ∩ A2).Nonempty := ⟨2, by decide⟩
      simp only [v1, v2, unitDemandVal, if_pos h1, if_pos h2, ← WithBot.coe_add]
      norm_num
    have hvXe : v1 (X.erase 0) + v2 (X.erase 0) = ((1 : ℝ) : WithBot ℝ) := by
      have h1 : ¬ (X.erase 0 ∩ A1).Nonempty := by decide
      have h2 : (X.erase 0 ∩ A2).Nonempty := ⟨1, by decide⟩
      simp only [v1, v2, unitDemandVal, if_neg h1, if_pos h2, ← WithBot.coe_add]
      norm_num
    have hvYi : v1 (insert 0 Y) + v2 (insert 0 Y) = ((2 : ℝ) : WithBot ℝ) := by
      have h1 : (insert 0 Y ∩ A1).Nonempty := ⟨0, by decide⟩
      have h2 : (insert 0 Y ∩ A2).Nonempty := ⟨2, by decide⟩
      simp only [v1, v2, unitDemandVal, if_pos h1, if_pos h2, ← WithBot.coe_add]
      norm_num
    have hsdiff : Y \ X = {2} := by decide
    have hvSw1 : v1 (insert 2 (X.erase 0)) + v2 (insert 2 (X.erase 0)) = ((2 : ℝ) : WithBot ℝ) := by
      have h1 : (insert 2 (X.erase 0) ∩ A1).Nonempty := ⟨2, by decide⟩
      have h2 : (insert 2 (X.erase 0) ∩ A2).Nonempty := ⟨2, by decide⟩
      simp only [v1, v2, unitDemandVal, if_pos h1, if_pos h2, ← WithBot.coe_add]
      norm_num
    have hvSw2 : v1 ((insert 0 Y).erase 2) + v2 ((insert 0 Y).erase 2) = ((1 : ℝ) : WithBot ℝ) := by
      have h1 : ((insert 0 Y).erase 2 ∩ A1).Nonempty := ⟨0, by decide⟩
      have h2 : ¬ ((insert 0 Y).erase 2 ∩ A2).Nonempty := by decide
      simp only [v1, v2, unitDemandVal, if_pos h1, if_neg h2, ← WithBot.coe_add]
      norm_num
    have h0_mem : (0 : Fin 3) ∈ X \ Y := by decide
    have hex := hgs.2 X Y (by dsimp; rw [hvX]; exact WithBot.coe_ne_bot)
      (by dsimp; rw [hvY]; exact WithBot.coe_ne_bot) 0 h0_mem
    dsimp only at hex
    have h22 : ((2 : ℝ) : WithBot ℝ) + ((2 : ℝ) : WithBot ℝ) = ((4 : ℝ) : WithBot ℝ) := by
      rw [← WithBot.coe_add]; norm_num
    have h12 : ((1 : ℝ) : WithBot ℝ) + ((2 : ℝ) : WithBot ℝ) = ((3 : ℝ) : WithBot ℝ) := by
      rw [← WithBot.coe_add]; norm_num
    have h21 : ((2 : ℝ) : WithBot ℝ) + ((1 : ℝ) : WithBot ℝ) = ((3 : ℝ) : WithBot ℝ) := by
      rw [← WithBot.coe_add]; norm_num
    rw [hvX, hvY, hvXe, hvYi, hsdiff, Finset.sup_singleton, hvSw1, hvSw2,
        h22, h12, h21, max_self, WithBot.coe_le_coe] at hex
    linarith

  have h_wb_add_zero : ∀ z : WithBot ℝ, z + ((0 : ℝ) : WithBot ℝ) = z := by
    intro z; cases z <;> simp

  
  have h_assign_coe : ∀ {n k : ℕ} (w : Fin n → Fin k → ℝ) (S : Finset (Fin n)),
      let Mset := (Finset.univ : Finset (Fin k → Option (Fin n))).filter (IsSlotMatchingOn S)
      Mset.Nonempty ∧
      assignmentVal w S = Mset.sup (fun f =>
        ((∑ j : Fin k, match f j with | none => (0 : ℝ) | some g => w g j : ℝ) : WithBot ℝ)) := by
    intro n k w S
    let Mset := (Finset.univ : Finset (Fin k → Option (Fin n))).filter (IsSlotMatchingOn S)
    let f0 : Fin k → Option (Fin n) := fun _ => none
    have hf0 : IsSlotMatchingOn S f0 := ⟨by simp [f0], by simp [f0]⟩
    have hf0_mem : f0 ∈ Mset := Finset.mem_filter.mpr ⟨Finset.mem_univ f0, hf0⟩
    have h0_le : ((0 : ℝ) : WithBot ℝ) ≤ Mset.sup (fun f =>
        ((∑ j : Fin k, match f j with | none => (0 : ℝ) | some g => w g j : ℝ) : WithBot ℝ)) := by
      have hval : ((∑ j : Fin k, match f0 j with | none => (0 : ℝ) | some g => w g j : ℝ) : WithBot ℝ) =
          ((0 : ℝ) : WithBot ℝ) := by simp [f0]
      rw [← hval]
      exact Finset.le_sup (f := fun f =>
        ((∑ j : Fin k, match f j with | none => (0 : ℝ) | some g => w g j : ℝ) : WithBot ℝ)) hf0_mem
    have hne_bot : Mset.sup (fun f =>
        ((∑ j : Fin k, match f j with | none => (0 : ℝ) | some g => w g j : ℝ) : WithBot ℝ)) ≠ ⊥ := by
      intro hb; rw [hb, le_bot_iff] at h0_le; exact WithBot.coe_ne_bot h0_le
    have h_unbot_eq : ∀ {z₁ z₂ : WithBot ℝ}, z₁ = z₂ → z₂ ≠ ⊥ → ((z₁.unbotD 0 : ℝ) : WithBot ℝ) = z₂ := by
      rintro _ _ rfl hz; obtain ⟨r', rfl⟩ := WithBot.ne_bot_iff_exists.mp hz; rfl
    refine ⟨⟨f0, hf0_mem⟩, ?_⟩
    unfold assignmentVal
    refine h_unbot_eq (Finset.sup_congr (by ext f; simp) (fun f _ => ?_)) hne_bot
    congr 1

  have h_assign_zero : ∀ n (w : Fin n → Fin 0 → ℝ), assignmentVal w = zeroVal n := by
    intro n w
    funext S
    obtain ⟨⟨f0, hf0_mem⟩, hcoe⟩ := h_assign_coe w S
    rw [hcoe]
    dsimp only [zeroVal]
    refine le_antisymm ?_ ?_
    · refine Finset.sup_le (fun f _ => ?_)
      simp
    · have hval : ((∑ j : Fin 0, match f0 j with | none => (0 : ℝ) | some g => w g j : ℝ) : WithBot ℝ) =
          ((0 : ℝ) : WithBot ℝ) := by simp
      rw [← hval]
      exact Finset.le_sup (f := fun f =>
        ((∑ j : Fin 0, match f j with | none => (0 : ℝ) | some g => w g j : ℝ) : WithBot ℝ)) hf0_mem

  have h_assign_step : ∀ n k (w : Fin n → Fin (k + 1) → ℝ),
      IsGSValuation (lastSlotVal w) ∧
      assignmentVal w = valConvolution (assignmentVal (fun g j => w g (Fin.castSucc j))) (lastSlotVal w) := by
    intro n k w
    refine ⟨?_, ?_⟩
    · refine ⟨by simp [lastSlotVal], ?_⟩
      intro X Y hX hY x hx
      obtain ⟨hxX, hxY⟩ := Finset.mem_sdiff.mp hx
      have hXc : X.card ≤ 1 := by
        by_contra h; simp [lastSlotVal, h] at hX
      have hYc : Y.card ≤ 1 := by
        by_contra h; simp [lastSlotVal, h] at hY
      have hX_eq : X = {x} := by
        ext z; simp only [Finset.mem_singleton]
        exact ⟨fun hz => Finset.card_le_one.mp hXc z hz x hxX, fun h => h ▸ hxX⟩
      by_cases hY_emp : Y = ∅
      · subst hY_emp
        apply le_max_of_le_left
        rw [hX_eq]
        simp [lastSlotVal]
      · obtain ⟨y, hyY⟩ := Finset.nonempty_iff_ne_empty.mpr hY_emp
        have hY_eq : Y = {y} := by
          ext z; simp only [Finset.mem_singleton]
          exact ⟨fun hz => Finset.card_le_one.mp hYc z hz y hyY, fun h => h ▸ hyY⟩
        have hyx : y ≠ x := fun h => hxY (h ▸ hyY)
        have hy_sdiff : y ∈ Y \ X := by rw [hX_eq, hY_eq]; simp [hyx]
        apply le_max_of_le_right
        refine le_trans ?_ (Finset.le_sup (f := fun z =>
          lastSlotVal w (insert z (X.erase x)) + lastSlotVal w ((insert x Y).erase z)) hy_sdiff)
        dsimp only
        have hs1 : insert y (X.erase x) = {y} := by rw [hX_eq]; simp
        have hs2 : (insert x Y).erase y = {x} := by
          rw [hY_eq]
          ext z; simp [Finset.mem_erase, Finset.mem_insert]
          by_cases hzx : z = x <;> simp_all
        rw [hs1, hs2, hX_eq, hY_eq]
        simp [lastSlotVal, ← WithBot.coe_add, add_comm]
    · let w_init : Fin n → Fin k → ℝ := fun g j => w g (Fin.castSucc j)
      funext S
      rw [(h_assign_coe w S).2]
      dsimp [valConvolution]
      refine le_antisymm ?_ ?_
      · refine Finset.sup_le (fun f hf_mem => ?_)
        have hf : IsSlotMatchingOn S f := (Finset.mem_filter.mp hf_mem).2
        let f_init : Fin k → Option (Fin n) := fun j => f (Fin.castSucc j)
        have h_sum_split : (∑ j : Fin (k + 1), match f j with | none => (0 : ℝ) | some g => w g j) =
            (∑ j : Fin k, match f_init j with | none => (0 : ℝ) | some g => w_init g j) +
            (match f (Fin.last k) with | none => (0 : ℝ) | some g => w g (Fin.last k)) := by
          rw [Fin.sum_univ_castSucc]
        cases hlast : f (Fin.last k) with
        | none =>
          have hf_init_S : IsSlotMatchingOn S f_init := by
            refine ⟨fun j g hj => hf.1 (Fin.castSucc j) g hj, fun j1 j2 g h1 h2 => ?_⟩
            exact Fin.castSucc_inj.mp (hf.2 (Fin.castSucc j1) (Fin.castSucc j2) g h1 h2)
          have hmem_init : f_init ∈ (Finset.univ : Finset (Fin k → Option (Fin n))).filter (IsSlotMatchingOn S) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf_init_S⟩
          have hS_pow : S ∈ S.powerset := Finset.mem_powerset.mpr Finset.Subset.rfl
          refine le_trans ?_ (Finset.le_sup (f := fun T => assignmentVal w_init T + lastSlotVal w (S \ T)) hS_pow)
          dsimp only
          rw [(h_assign_coe w_init S).2, Finset.sdiff_self]
          have h_u0 : lastSlotVal w ∅ = ((0 : ℝ) : WithBot ℝ) := by simp [lastSlotVal]
          rw [h_u0, h_wb_add_zero, h_sum_split, hlast, add_zero]
          exact Finset.le_sup (f := fun f' =>
            ((∑ j : Fin k, match f' j with | none => (0 : ℝ) | some g => w_init g j : ℝ) : WithBot ℝ)) hmem_init
        | some g =>
          have hgS : g ∈ S := hf.1 (Fin.last k) g hlast
          let T := S.erase g
          have hf_init_T : IsSlotMatchingOn T f_init := by
            refine ⟨fun j g' hj => ?_, fun j1 j2 g' h1 h2 => ?_⟩
            · have hg'S : g' ∈ S := hf.1 (Fin.castSucc j) g' hj
              have hne : g' ≠ g := by
                intro heq; subst heq
                exact Fin.castSucc_ne_last j (hf.2 (Fin.castSucc j) (Fin.last k) g' hj hlast)
              exact Finset.mem_erase.mpr ⟨hne, hg'S⟩
            · exact Fin.castSucc_inj.mp (hf.2 (Fin.castSucc j1) (Fin.castSucc j2) g' h1 h2)
          have hmem_init : f_init ∈ (Finset.univ : Finset (Fin k → Option (Fin n))).filter (IsSlotMatchingOn T) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf_init_T⟩
          have hT_pow : T ∈ S.powerset := Finset.mem_powerset.mpr (Finset.erase_subset g S)
          refine le_trans ?_ (Finset.le_sup (f := fun T' => assignmentVal w_init T' + lastSlotVal w (S \ T')) hT_pow)
          dsimp only
          have hsdiff_T : S \ T = {g} := by
            ext z; simp [T, Finset.mem_sdiff, Finset.mem_erase]
            by_cases hzg : z = g <;> simp_all
          rw [(h_assign_coe w_init T).2, hsdiff_T]
          have h_ug : lastSlotVal w {g} = ((w g (Fin.last k) : ℝ) : WithBot ℝ) := by
            simp [lastSlotVal]
          rw [h_ug, h_sum_split, hlast, WithBot.coe_add]
          have h_le_init := Finset.le_sup (f := fun f' =>
            ((∑ j : Fin k, match f' j with | none => (0 : ℝ) | some g => w_init g j : ℝ) : WithBot ℝ)) hmem_init
          exact h_wb_add_mono h_le_init le_rfl
      · refine Finset.sup_le (fun T hT_pow => ?_)
        have hTS : T ⊆ S := Finset.mem_powerset.mp hT_pow
        by_cases hcard : (S \ T).card ≤ 1
        · obtain ⟨hMne, hcoeT⟩ := h_assign_coe w_init T
          obtain ⟨f_init, hf_init_mem, hf_init_sup⟩ := Finset.exists_mem_eq_sup _ hMne
            (fun f' => ((∑ j : Fin k, match f' j with | none => (0 : ℝ) | some g => w_init g j : ℝ) : WithBot ℝ))
          have hf_init : IsSlotMatchingOn T f_init := (Finset.mem_filter.mp hf_init_mem).2
          rw [hcoeT, hf_init_sup]
          by_cases hemp : S \ T = ∅
          · rw [hemp]
            let f : Fin (k + 1) → Option (Fin n) := Fin.snoc f_init none
            have hf_S : IsSlotMatchingOn S f := by
              refine ⟨fun j g hj => ?_, fun j1 j2 g h1 h2 => ?_⟩
              · refine Fin.lastCases ?_ ?_ j hj
                · simp [f]
                · intro i hi; dsimp only [f] at hi; rw [Fin.snoc_castSucc] at hi; exact hTS (hf_init.1 i g hi)
              · refine Fin.lastCases ?_ ?_ j1 h1
                · simp [f]
                · intro i1 hi1
                  dsimp only [f] at hi1; rw [Fin.snoc_castSucc] at hi1
                  refine Fin.lastCases ?_ ?_ j2 h2
                  · simp [f]
                  · intro i2 hi2
                    dsimp only [f] at hi2; rw [Fin.snoc_castSucc] at hi2
                    exact congrArg Fin.castSucc (hf_init.2 i1 i2 g hi1 hi2)
            have hf_mem : f ∈ (Finset.univ : Finset (Fin (k + 1) → Option (Fin n))).filter (IsSlotMatchingOn S) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf_S⟩
            refine le_trans ?_ (Finset.le_sup (f := fun f' =>
              ((∑ j : Fin (k + 1), match f' j with | none => (0 : ℝ) | some g => w g j : ℝ) : WithBot ℝ)) hf_mem)
            dsimp only
            have h_u0 : lastSlotVal w ∅ = ((0 : ℝ) : WithBot ℝ) := by simp [lastSlotVal]
            rw [h_u0, ← WithBot.coe_add, WithBot.coe_le_coe, Fin.sum_univ_castSucc]
            simp [f, w_init]
          · obtain ⟨g, hg_mem⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
            have h_eq_g : S \ T = {g} := by
              ext z; simp only [Finset.mem_singleton]
              exact ⟨fun hz => Finset.card_le_one.mp hcard z hz g hg_mem, fun h => h ▸ hg_mem⟩
            obtain ⟨hgS, hgT⟩ := Finset.mem_sdiff.mp hg_mem
            rw [h_eq_g]
            let f : Fin (k + 1) → Option (Fin n) := Fin.snoc f_init (some g)
            have hf_S : IsSlotMatchingOn S f := by
              refine ⟨fun j g' hj => ?_, fun j1 j2 g' h1 h2 => ?_⟩
              · refine Fin.lastCases ?_ ?_ j hj
                · simp only [f, Fin.snoc_last, Option.some.injEq]
                  rintro rfl; exact hgS
                · intro i hi; dsimp only [f] at hi; rw [Fin.snoc_castSucc] at hi; exact hTS (hf_init.1 i g' hi)
              · refine Fin.lastCases ?_ ?_ j1 h1
                · simp only [f, Fin.snoc_last, Option.some.injEq]
                  rintro rfl
                  refine Fin.lastCases ?_ ?_ j2 h2
                  · intro _; rfl
                  · intro i2 hi2
                    dsimp only [f] at hi2; rw [Fin.snoc_castSucc] at hi2
                    exact absurd (hf_init.1 i2 g hi2) hgT
                · intro i1 hi1
                  dsimp only [f] at hi1; rw [Fin.snoc_castSucc] at hi1
                  refine Fin.lastCases ?_ ?_ j2 h2
                  · simp only [f, Fin.snoc_last, Option.some.injEq]
                    rintro rfl
                    exact absurd (hf_init.1 i1 g hi1) hgT
                  · intro i2 hi2
                    dsimp only [f] at hi2; rw [Fin.snoc_castSucc] at hi2
                    exact congrArg Fin.castSucc (hf_init.2 i1 i2 g' hi1 hi2)
            have hf_mem : f ∈ (Finset.univ : Finset (Fin (k + 1) → Option (Fin n))).filter (IsSlotMatchingOn S) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf_S⟩
            refine le_trans ?_ (Finset.le_sup (f := fun f' =>
              ((∑ j : Fin (k + 1), match f' j with | none => (0 : ℝ) | some g => w g j : ℝ) : WithBot ℝ)) hf_mem)
            dsimp only
            have h_ug : lastSlotVal w {g} = ((w g (Fin.last k) : ℝ) : WithBot ℝ) := by simp [lastSlotVal]
            rw [h_ug, ← WithBot.coe_add, WithBot.coe_le_coe, Fin.sum_univ_castSucc]
            simp [f, w_init]
        · have hbot : lastSlotVal w (S \ T) = ⊥ := by simp [lastSlotVal, hcard]
          rw [hbot, WithBot.add_bot]
          exact bot_le

  
  have h_wb_add_ne_bot : ∀ {a b : WithBot ℝ}, a ≠ ⊥ → b ≠ ⊥ → a + b ≠ ⊥ := by
    intro a b ha hb
    simp [WithBot.add_eq_bot, ha, hb]

  have h_gs_step : ∀ {N : ℕ} {f : ItemValuation N}, IsGSValuation f →
      ∀ {X Y : Finset (Fin N)} {x : Fin N},
        f X ≠ ⊥ → f Y ≠ ⊥ → x ∈ X \ Y →
          (f X + f Y ≤ f (X.erase x) + f (insert x Y)) ∨
          (∃ y ∈ Y \ X, f X + f Y ≤ f (insert y (X.erase x)) + f ((insert x Y).erase y)) := by
    intro N f hf X Y x hX hY hx
    have hex := hf.2 X Y hX hY x hx
    rw [le_max_iff] at hex
    rcases hex with htr | hsw
    · exact Or.inl htr
    · have hne : (Y \ X).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        rw [hemp, Finset.sup_empty, le_bot_iff] at hsw
        exact h_wb_add_ne_bot hX hY hsw
      obtain ⟨y, hy, hsup⟩ := Finset.exists_mem_eq_sup (Y \ X) hne
        (fun y => f (insert y (X.erase x)) + f ((insert x Y).erase y))
      rw [hsup] at hsw
      exact Or.inr ⟨y, hy, hsw⟩

  have h_pullback_gs : ∀ {n m : ℕ} (e : Fin n ↪ Fin m) (V : ItemValuation m),
      IsGSValuation V → IsGSValuation (pullbackVal e V) := by
    intro n m e V hV
    refine ⟨by simp [pullbackVal, hV.1], ?_⟩
    intro X Y hX hY x hx
    have hxX : x ∈ X := (Finset.mem_sdiff.mp hx).1
    have hxY : x ∉ Y := (Finset.mem_sdiff.mp hx).2
    have hex_mem : e x ∈ X.map e \ Y.map e := by
      simp [hxX, hxY]
    rcases h_gs_step hV hX hY hex_mem with htr | ⟨u, hu, hsw⟩
    · apply le_max_of_le_left
      dsimp [pullbackVal] at htr ⊢
      rwa [Finset.map_erase, Finset.map_insert]
    · obtain ⟨huY, huX⟩ := Finset.mem_sdiff.mp hu
      obtain ⟨y, hyY, rfl⟩ := Finset.mem_map.mp huY
      have hyX : y ∉ X := fun hm => huX (Finset.mem_map_of_mem e hm)
      have hy_sdiff : y ∈ Y \ X := Finset.mem_sdiff.mpr ⟨hyY, hyX⟩
      apply le_max_of_le_right
      refine le_trans ?_ (Finset.le_sup (f := fun z =>
        pullbackVal e V (insert z (X.erase x)) + pullbackVal e V ((insert x Y).erase z)) hy_sdiff)
      dsimp [pullbackVal] at hsw ⊢
      rwa [Finset.map_insert, Finset.map_erase, Finset.map_erase, Finset.map_insert]

  have h_mergePair_gs : ∀ {N : ℕ} (a b : Fin N), a ≠ b →
      ∀ (f : ItemValuation N), IsGSValuation f → IsGSValuation (mergePair a b f) := by
    intro N a b hab f hf
    let F := mergePair a b f
    have h_er_ins_ne : ∀ (S : Finset (Fin N)) {p q : Fin N},
        p ≠ q → (insert q S).erase p = insert q (S.erase p) := by
      intro S p q hpq; ext w; simp only [Finset.mem_erase, Finset.mem_insert]
      constructor
      · rintro ⟨hwp, rfl | hwS⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hwp, hwS⟩
      · rintro (rfl | ⟨hwp, hwS⟩)
        · exact ⟨hpq.symm, Or.inl rfl⟩
        · exact ⟨hwp, Or.inr hwS⟩
    have hbase_not_a : ∀ S, a ∉ pairBase a b S := fun S => by simp [pairBase]
    have hbase_not_b : ∀ S, b ∉ pairBase a b S := fun S => by simp [pairBase]
    have hbase_not_c : ∀ {c} (S), (c = a ∨ c = b) → c ∉ pairBase a b S := by
      rintro c S (rfl | rfl)
      · exact hbase_not_a S
      · exact hbase_not_b S
    have hbase_er_other : ∀ (S : Finset (Fin N)) {z : Fin N},
        z ≠ a → z ≠ b → (pairBase a b S).erase z = pairBase a b (S.erase z) := by
      intro S z _ _; ext w; simp only [pairBase, Finset.mem_erase]; tauto
    have hbase_ins_other : ∀ (S : Finset (Fin N)) {z : Fin N},
        z ≠ a → z ≠ b → insert z (pairBase a b S) = pairBase a b (insert z S) := by
      intro S z hza hzb; ext w; simp only [pairBase, Finset.mem_erase, Finset.mem_insert]
      constructor
      · rintro (rfl | ⟨hwb, hwa, hwS⟩)
        · exact ⟨hzb, hza, Or.inl rfl⟩
        · exact ⟨hwb, hwa, Or.inr hwS⟩
      · rintro ⟨hwb, hwa, rfl | hwS⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hwb, hwa, hwS⟩
    have hbase_er_a : ∀ S, pairBase a b (S.erase a) = pairBase a b S := by
      intro S; ext w; simp only [pairBase, Finset.mem_erase]; tauto
    have hbase_ins_a : ∀ S, pairBase a b (insert a S) = pairBase a b S := by
      intro S; ext w; simp only [pairBase, Finset.mem_erase, Finset.mem_insert]
      constructor
      · rintro ⟨hwb, hwa, rfl | hwS⟩
        · exact absurd rfl hwa
        · exact ⟨hwb, hwa, hwS⟩
      · rintro ⟨hwb, hwa, hwS⟩; exact ⟨hwb, hwa, Or.inr hwS⟩
    have hbase_er_b : ∀ S, pairBase a b (S.erase b) = pairBase a b S := by
      intro S; ext w; simp only [pairBase, Finset.mem_erase]; tauto
    have hbase_ins_b : ∀ S, pairBase a b (insert b S) = pairBase a b S := by
      intro S; ext w; simp only [pairBase, Finset.mem_erase, Finset.mem_insert]
      constructor
      · rintro ⟨hwb, hwa, rfl | hwS⟩
        · exact absurd rfl hwb
        · exact ⟨hwb, hwa, hwS⟩
      · rintro ⟨hwb, hwa, hwS⟩; exact ⟨hwb, hwa, Or.inr hwS⟩
    have hF_no_a : ∀ {S}, a ∉ S → f (pairBase a b S) = F S := fun {S} ha => by
      simp [F, mergePair, ha]
    have hF_ub : ∀ {S c}, a ∈ S → (c = a ∨ c = b) → f (insert c (pairBase a b S)) ≤ F S := by
      rintro S c ha (rfl | rfl) <;> simp [F, mergePair, ha]
    have hF_att : ∀ {S}, a ∈ S → ∃ c, (c = a ∨ c = b) ∧ f (insert c (pairBase a b S)) = F S := by
      intro S ha
      rcases max_choice (f (insert a (pairBase a b S))) (f (insert b (pairBase a b S))) with h | h
      · exact ⟨a, Or.inl rfl, by simp [F, mergePair, ha, h]⟩
      · exact ⟨b, Or.inr rfl, by simp [F, mergePair, ha, h]⟩
    have h_same_copy : ∀ {X Y : Finset (Fin N)} {x c : Fin N},
        F X ≠ ⊥ → F Y ≠ ⊥ → x ∈ X \ Y → x ≠ a → x ≠ b → a ∈ X → a ∈ Y →
        (c = a ∨ c = b) →
        f (insert c (pairBase a b X)) = F X →
        f (insert c (pairBase a b Y)) = F Y →
        F X + F Y ≤ max (F (X.erase x) + F (insert x Y))
          ((Y \ X).sup (fun y => F (insert y (X.erase x)) + F ((insert x Y).erase y))) := by
      intro X Y x c hFX hFY hx hxa hxb haX haY hc hXhat hYhat
      let Xhat := insert c (pairBase a b X)
      let Yhat := insert c (pairBase a b Y)
      have hxX : x ∈ X := (Finset.mem_sdiff.mp hx).1
      have hxY : x ∉ Y := (Finset.mem_sdiff.mp hx).2
      have hxc : x ≠ c := by rcases hc with rfl | rfl <;> assumption
      have hx_mem : x ∈ Xhat \ Yhat := by
        simp [Xhat, Yhat, pairBase, hxX, hxY, hxa, hxb, hxc]
      have hXh_ne : f Xhat ≠ ⊥ := by rw [hXhat]; exact hFX
      have hYh_ne : f Yhat ≠ ⊥ := by rw [hYhat]; exact hFY
      rcases h_gs_step hf hXh_ne hYh_ne hx_mem with htr | ⟨u, hu, hsw⟩
      · apply le_max_of_le_left
        rw [← hXhat, ← hYhat]
        refine htr.trans (h_wb_add_mono ?_ ?_)
        · dsimp only [Xhat]
          rw [h_er_ins_ne _ hxc, hbase_er_other X hxa hxb]
          exact hF_ub (Finset.mem_erase.mpr ⟨hxa.symm, haX⟩) hc
        · dsimp only [Yhat]
          rw [Finset.insert_comm, hbase_ins_other Y hxa hxb]
          exact hF_ub (Finset.mem_insert_of_mem haY) hc
      · obtain ⟨huY, huX⟩ := Finset.mem_sdiff.mp hu
        have huc : u ≠ c := fun h => huX (h ▸ Finset.mem_insert_self c _)
        have hu_baseY : u ∈ pairBase a b Y := by
          rcases Finset.mem_insert.mp huY with rfl | hm
          · exact absurd rfl huc
          · exact hm
        have hub : u ≠ b := (Finset.mem_erase.mp hu_baseY).1
        have hua : u ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hu_baseY).2).1
        have huY_orig : u ∈ Y := (Finset.mem_erase.mp (Finset.mem_erase.mp hu_baseY).2).2
        have huX_orig : u ∉ X := fun hm =>
          huX (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hub, Finset.mem_erase.mpr ⟨hua, hm⟩⟩))
        have hu_sdiff : u ∈ Y \ X := Finset.mem_sdiff.mpr ⟨huY_orig, huX_orig⟩
        apply le_max_of_le_right
        refine le_trans ?_ (Finset.le_sup (f := fun y => F (insert y (X.erase x)) + F ((insert x Y).erase y)) hu_sdiff)
        dsimp only
        rw [← hXhat, ← hYhat]
        refine hsw.trans (h_wb_add_mono ?_ ?_)
        · dsimp only [Xhat]
          rw [h_er_ins_ne _ hxc, Finset.insert_comm, hbase_er_other X hxa hxb,
              hbase_ins_other (X.erase x) hua hub]
          exact hF_ub (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxa.symm, haX⟩)) hc
        · dsimp only [Yhat]
          rw [Finset.insert_comm, h_er_ins_ne _ huc, hbase_ins_other Y hxa hxb,
              hbase_er_other (insert x Y) hua hub]
          exact hF_ub (Finset.mem_erase.mpr ⟨hua.symm, Finset.mem_insert_of_mem haY⟩) hc

    change IsGSValuation F
    refine ⟨by simp [F, mergePair, pairBase, hf.1], ?_⟩
    intro X Y hFX hFY x hx
    have hxX : x ∈ X := (Finset.mem_sdiff.mp hx).1
    have hxY : x ∉ Y := (Finset.mem_sdiff.mp hx).2
    by_cases hxb : x = b
    · subst hxb
      apply le_max_of_le_left
      have h1 : F (X.erase x) = F X := by
        have ha_iff : a ∈ X.erase x ↔ a ∈ X := by simp [hab]
        simp only [F, mergePair, ha_iff, hbase_er_b]
      have h2 : F (insert x Y) = F Y := by
        have ha_iff : a ∈ insert x Y ↔ a ∈ Y := by simp [hab]
        simp only [F, mergePair, ha_iff, hbase_ins_b]
      rw [h1, h2]
    · by_cases hxa : x = a
      · 
        subst hxa
        obtain ⟨c, hc, hXhat⟩ := hF_att hxX
        have hYhat := hF_no_a hxY
        let Xhat := insert c (pairBase x b X)
        let Yhat := pairBase x b Y
        have hc_mem : c ∈ Xhat \ Yhat :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self c _, hbase_not_c Y hc⟩
        have hXh_ne : f Xhat ≠ ⊥ := by rw [hXhat]; exact hFX
        have hYh_ne : f Yhat ≠ ⊥ := by rw [hYhat]; exact hFY
        rcases h_gs_step hf hXh_ne hYh_ne hc_mem with htr | ⟨u, hu, hsw⟩
        · apply le_max_of_le_left
          rw [← hXhat, ← hYhat]
          refine htr.trans (h_wb_add_mono ?_ ?_)
          · dsimp only [Xhat]
            rw [Finset.erase_insert (hbase_not_c X hc), ← hbase_er_a X, hF_no_a (Finset.notMem_erase x X)]
          · dsimp only [Yhat]
            rw [← hbase_ins_a Y]
            exact hF_ub (Finset.mem_insert_self x Y) hc
        · obtain ⟨huY, huX⟩ := Finset.mem_sdiff.mp hu
          have hub : u ≠ b := (Finset.mem_erase.mp huY).1
          have hux : u ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp huY).2).1
          have huY_orig : u ∈ Y := (Finset.mem_erase.mp (Finset.mem_erase.mp huY).2).2
          have huX_orig : u ∉ X := fun hm =>
            huX (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hub, Finset.mem_erase.mpr ⟨hux, hm⟩⟩))
          have hu_sdiff : u ∈ Y \ X := Finset.mem_sdiff.mpr ⟨huY_orig, huX_orig⟩
          have huc : u ≠ c := by rcases hc with rfl | rfl <;> assumption
          apply le_max_of_le_right
          refine le_trans ?_ (Finset.le_sup (f := fun y => F (insert y (X.erase x)) + F ((insert x Y).erase y)) hu_sdiff)
          dsimp only
          rw [← hXhat, ← hYhat]
          refine hsw.trans (h_wb_add_mono ?_ ?_)
          · dsimp only [Xhat]
            rw [Finset.erase_insert (hbase_not_c X hc), ← hbase_er_a X,
                hbase_ins_other (X.erase x) hux hub, hF_no_a (by simp [hux.symm])]
          · dsimp only [Yhat]
            rw [h_er_ins_ne _ huc, ← hbase_ins_a Y, hbase_er_other (insert x Y) hux hub]
            exact hF_ub (Finset.mem_erase.mpr ⟨hux.symm, Finset.mem_insert_self x Y⟩) hc
      · 
        have hxa_symm : a ≠ x := Ne.symm hxa
        by_cases haY : a ∈ Y
        · by_cases haX : a ∈ X
          · 
            obtain ⟨c, hc, hXhat⟩ := hF_att haX
            obtain ⟨c', hc', hYhat⟩ := hF_att haY
            by_cases hcc' : c = c'
            · subst hcc'
              exact h_same_copy hFX hFY hx hxa hxb haX haY hc hXhat hYhat
            · let Xhat := insert c (pairBase a b X)
              let Yhat := insert c' (pairBase a b Y)
              have hxc : x ≠ c := by rcases hc with rfl | rfl <;> assumption
              have hxc' : x ≠ c' := by rcases hc' with rfl | rfl <;> assumption
              have hx_mem : x ∈ Xhat \ Yhat := by
                simp [Xhat, Yhat, pairBase, hxX, hxY, hxa, hxb, hxc, hxc']
              have hXh_ne : f Xhat ≠ ⊥ := by rw [hXhat]; exact hFX
              have hYh_ne : f Yhat ≠ ⊥ := by rw [hYhat]; exact hFY
              rcases h_gs_step hf hXh_ne hYh_ne hx_mem with htr | ⟨u, hu, hsw⟩
              · apply le_max_of_le_left
                rw [← hXhat, ← hYhat]
                refine htr.trans (h_wb_add_mono ?_ ?_)
                · dsimp only [Xhat]
                  rw [h_er_ins_ne _ hxc, hbase_er_other X hxa hxb]
                  exact hF_ub (Finset.mem_erase.mpr ⟨hxa_symm, haX⟩) hc
                · dsimp only [Yhat]
                  rw [Finset.insert_comm, hbase_ins_other Y hxa hxb]
                  exact hF_ub (Finset.mem_insert_of_mem haY) hc'
              · obtain ⟨huY, huX⟩ := Finset.mem_sdiff.mp hu
                by_cases huc' : u = c'
                · 
                  subst huc'
                  let W1 := insert u (Xhat.erase x)
                  let W2 := (insert x Yhat).erase u
                  have hFW : F X + F Y ≤ f W1 + f W2 := by
                    rw [← hXhat, ← hYhat]; exact hsw
                  have hFX_Y_ne : F X + F Y ≠ ⊥ := h_wb_add_ne_bot hFX hFY
                  have hW_ne : f W1 + f W2 ≠ ⊥ := fun hb => hFX_Y_ne (le_bot_iff.mp (hb ▸ hFW))
                  have hW1_ne : f W1 ≠ ⊥ := fun hb => hW_ne (by simp [hb])
                  have hW2_ne : f W2 ≠ ⊥ := fun hb => hW_ne (by simp [hb])
                  have hW1_eq : W1 = insert u (insert c ((pairBase a b X).erase x)) := by
                    dsimp only [W1, Xhat]
                    rw [h_er_ins_ne _ hxc]
                  have hW2_eq : W2 = insert x (pairBase a b Y) := by
                    dsimp only [W2, Yhat]
                    rw [Finset.insert_comm, Finset.erase_insert (by simp [Ne.symm hxc', hbase_not_c Y hc'])]
                  have hc_W : c ∈ W1 \ W2 := by
                    rw [hW1_eq, hW2_eq]
                    exact Finset.mem_sdiff.mpr
                      ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self c _),
                       by simp [hxc.symm, hbase_not_c Y hc]⟩
                  have hc_not_bx : c ∉ (pairBase a b X).erase x :=
                    fun hm => hbase_not_c X hc (Finset.erase_subset x _ hm)
                  have hW1_er_c : W1.erase c = insert u ((pairBase a b X).erase x) := by
                    rw [hW1_eq, h_er_ins_ne _ hcc', Finset.erase_insert hc_not_bx]
                  rcases h_gs_step hf hW1_ne hW2_ne hc_W with htr2 | ⟨u2, hu2, hsw2⟩
                  · apply le_max_of_le_left
                    refine (hFW.trans htr2).trans (h_wb_add_mono ?_ ?_)
                    · rw [hW1_er_c, hbase_er_other X hxa hxb]
                      exact hF_ub (Finset.mem_erase.mpr ⟨hxa_symm, haX⟩) hc'
                    · rw [hW2_eq, hbase_ins_other Y hxa hxb]
                      exact hF_ub (Finset.mem_insert_of_mem haY) hc
                  · obtain ⟨hu2_W2, hu2_W1⟩ := Finset.mem_sdiff.mp hu2
                    rw [hW2_eq] at hu2_W2
                    rcases Finset.mem_insert.mp hu2_W2 with hu2_eq_x | hu2_baseY
                    · 
                      subst u2
                      have hx_baseX : x ∈ pairBase a b X :=
                        Finset.mem_erase.mpr ⟨hxb, Finset.mem_erase.mpr ⟨hxa, hxX⟩⟩
                      have hx_not_baseY : x ∉ pairBase a b Y :=
                        fun hm => hxY ((Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).2)
                      have heq1 : insert x (W1.erase c) = insert u (pairBase a b X) := by
                        rw [hW1_er_c, Finset.insert_comm, Finset.insert_erase hx_baseX]
                      have heq2 : (insert c W2).erase x = insert c (pairBase a b Y) := by
                        rw [hW2_eq, Finset.insert_comm, Finset.erase_insert (by simp [hxc, hx_not_baseY])]
                      rw [heq1, heq2] at hsw2
                      have h_sum_le : F X + F Y ≤ f (insert u (pairBase a b X)) + f (insert c (pairBase a b Y)) :=
                        hFW.trans hsw2
                      have h_ub1 : f (insert u (pairBase a b X)) ≤ F X := hF_ub haX hc'
                      have h_ub2 : f (insert c (pairBase a b Y)) ≤ F Y := hF_ub haY hc
                      have hXhat'_eq : f (insert u (pairBase a b X)) = F X := by
                        obtain ⟨rX, hrX⟩ := WithBot.ne_bot_iff_exists.mp hFX
                        obtain ⟨rY, hrY⟩ := WithBot.ne_bot_iff_exists.mp hFY
                        rw [← hrX, ← hrY, ← WithBot.coe_add] at h_sum_le
                        cases hf1 : f (insert u (pairBase a b X)) with
                        | bot => rw [hf1] at h_sum_le; exact absurd h_sum_le (by simp)
                        | coe s1 =>
                          cases hf2 : f (insert c (pairBase a b Y)) with
                          | bot => rw [hf2] at h_sum_le; exact absurd h_sum_le (by simp)
                          | coe s2 =>
                            rw [hf1, ← hrX, WithBot.coe_le_coe] at h_ub1
                            rw [hf2, ← hrY, WithBot.coe_le_coe] at h_ub2
                            rw [hf1, hf2, ← WithBot.coe_add, WithBot.coe_le_coe] at h_sum_le
                            rw [← hrX]
                            congr 1
                            linarith
                      exact h_same_copy hFX hFY hx hxa hxb haX haY hc' hXhat'_eq hYhat
                    · 
                      have hu2b : u2 ≠ b := (Finset.mem_erase.mp hu2_baseY).1
                      have hu2a : u2 ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hu2_baseY).2).1
                      have hu2Y_orig : u2 ∈ Y := (Finset.mem_erase.mp (Finset.mem_erase.mp hu2_baseY).2).2
                      have hu2x : u2 ≠ x := fun h => hxY (h ▸ hu2Y_orig)
                      have hu2c : u2 ≠ c := by rcases hc with rfl | rfl <;> assumption
                      have hu2X_orig : u2 ∉ X := by
                        intro hm
                        apply hu2_W1
                        rw [hW1_eq]
                        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                          (Finset.mem_erase.mpr ⟨hu2x, Finset.mem_erase.mpr ⟨hu2b, Finset.mem_erase.mpr ⟨hu2a, hm⟩⟩⟩))
                      have hu2_sdiff : u2 ∈ Y \ X := Finset.mem_sdiff.mpr ⟨hu2Y_orig, hu2X_orig⟩
                      apply le_max_of_le_right
                      refine le_trans ?_ (Finset.le_sup (f := fun y => F (insert y (X.erase x)) + F ((insert x Y).erase y)) hu2_sdiff)
                      dsimp only
                      refine (hFW.trans hsw2).trans (h_wb_add_mono ?_ ?_)
                      · rw [hW1_er_c, Finset.insert_comm, hbase_er_other X hxa hxb,
                            hbase_ins_other (X.erase x) hu2a hu2b]
                        exact hF_ub (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxa_symm, haX⟩)) hc'
                      · rw [hW2_eq, h_er_ins_ne _ hu2c, hbase_ins_other Y hxa hxb,
                            hbase_er_other (insert x Y) hu2a hu2b]
                        exact hF_ub (Finset.mem_erase.mpr ⟨hu2a.symm, Finset.mem_insert_of_mem haY⟩) hc
                · 
                  have hu_baseY : u ∈ pairBase a b Y := by
                    rcases Finset.mem_insert.mp huY with rfl | hm
                    · exact absurd rfl huc'
                    · exact hm
                  have hub : u ≠ b := (Finset.mem_erase.mp hu_baseY).1
                  have hua : u ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hu_baseY).2).1
                  have huY_orig : u ∈ Y := (Finset.mem_erase.mp (Finset.mem_erase.mp hu_baseY).2).2
                  have huX_orig : u ∉ X := fun hm =>
                    huX (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hub, Finset.mem_erase.mpr ⟨hua, hm⟩⟩))
                  have hu_sdiff : u ∈ Y \ X := Finset.mem_sdiff.mpr ⟨huY_orig, huX_orig⟩
                  apply le_max_of_le_right
                  refine le_trans ?_ (Finset.le_sup (f := fun y => F (insert y (X.erase x)) + F ((insert x Y).erase y)) hu_sdiff)
                  dsimp only
                  rw [← hXhat, ← hYhat]
                  refine hsw.trans (h_wb_add_mono ?_ ?_)
                  · dsimp only [Xhat]
                    rw [h_er_ins_ne _ hxc, Finset.insert_comm, hbase_er_other X hxa hxb,
                        hbase_ins_other (X.erase x) hua hub]
                    exact hF_ub (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxa_symm, haX⟩)) hc
                  · dsimp only [Yhat]
                    rw [Finset.insert_comm, h_er_ins_ne _ huc', hbase_ins_other Y hxa hxb,
                        hbase_er_other (insert x Y) hua hub]
                    exact hF_ub (Finset.mem_erase.mpr ⟨hua.symm, Finset.mem_insert_of_mem haY⟩) hc'
          · 
            have hXhat := hF_no_a haX
            obtain ⟨c, hc, hYhat⟩ := hF_att haY
            let Xhat := pairBase a b X
            let Yhat := insert c (pairBase a b Y)
            have hxc : x ≠ c := by rcases hc with rfl | rfl <;> assumption
            have hx_mem : x ∈ Xhat \ Yhat := by
              simp [Xhat, Yhat, pairBase, hxX, hxY, hxa, hxb, hxc]
            have hXh_ne : f Xhat ≠ ⊥ := by rw [hXhat]; exact hFX
            have hYh_ne : f Yhat ≠ ⊥ := by rw [hYhat]; exact hFY
            rcases h_gs_step hf hXh_ne hYh_ne hx_mem with htr | ⟨u, hu, hsw⟩
            · apply le_max_of_le_left
              rw [← hXhat, ← hYhat]
              refine htr.trans (h_wb_add_mono ?_ ?_)
              · dsimp only [Xhat]
                rw [hbase_er_other X hxa hxb, hF_no_a (fun hm => haX (Finset.erase_subset x X hm))]
              · dsimp only [Yhat]
                rw [Finset.insert_comm, hbase_ins_other Y hxa hxb]
                exact hF_ub (Finset.mem_insert_of_mem haY) hc
            · obtain ⟨huY, huX⟩ := Finset.mem_sdiff.mp hu
              by_cases huc : u = c
              · 
                subst huc
                have ha_sdiff : a ∈ Y \ X := Finset.mem_sdiff.mpr ⟨haY, haX⟩
                apply le_max_of_le_right
                refine le_trans ?_ (Finset.le_sup (f := fun y => F (insert y (X.erase x)) + F ((insert x Y).erase y)) ha_sdiff)
                dsimp only
                rw [← hXhat, ← hYhat]
                refine hsw.trans (h_wb_add_mono ?_ ?_)
                · dsimp only [Xhat]
                  rw [hbase_er_other X hxa hxb, ← hbase_ins_a (X.erase x)]
                  exact hF_ub (Finset.mem_insert_self a _) hc
                · dsimp only [Yhat]
                  rw [Finset.insert_comm, Finset.erase_insert (by simp [Ne.symm hxc, hbase_not_c Y hc]),
                      hbase_ins_other Y hxa hxb, ← hbase_er_a (insert x Y),
                      hF_no_a (Finset.notMem_erase a _)]
              · have hu_baseY : u ∈ pairBase a b Y := by
                  rcases Finset.mem_insert.mp huY with rfl | hm
                  · exact absurd rfl huc
                  · exact hm
                have hub : u ≠ b := (Finset.mem_erase.mp hu_baseY).1
                have hua : u ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hu_baseY).2).1
                have huY_orig : u ∈ Y := (Finset.mem_erase.mp (Finset.mem_erase.mp hu_baseY).2).2
                have huX_orig : u ∉ X := fun hm =>
                  huX (Finset.mem_erase.mpr ⟨hub, Finset.mem_erase.mpr ⟨hua, hm⟩⟩)
                have hu_sdiff : u ∈ Y \ X := Finset.mem_sdiff.mpr ⟨huY_orig, huX_orig⟩
                apply le_max_of_le_right
                refine le_trans ?_ (Finset.le_sup (f := fun y => F (insert y (X.erase x)) + F ((insert x Y).erase y)) hu_sdiff)
                dsimp only
                rw [← hXhat, ← hYhat]
                refine hsw.trans (h_wb_add_mono ?_ ?_)
                · dsimp only [Xhat]
                  rw [hbase_er_other X hxa hxb, hbase_ins_other (X.erase x) hua hub,
                      hF_no_a (by simp [hua.symm, haX])]
                · dsimp only [Yhat]
                  rw [Finset.insert_comm, h_er_ins_ne _ huc, hbase_ins_other Y hxa hxb,
                      hbase_er_other (insert x Y) hua hub]
                  exact hF_ub (Finset.mem_erase.mpr ⟨hua.symm, Finset.mem_insert_of_mem haY⟩) hc
        · 
          have hYhat := hF_no_a haY
          let Yhat := pairBase a b Y
          have hYh_ne : f Yhat ≠ ⊥ := by rw [hYhat]; exact hFY
          by_cases haX : a ∈ X
          · obtain ⟨c, hc, hXhat⟩ := hF_att haX
            let Xhat := insert c (pairBase a b X)
            have hxc : x ≠ c := by rcases hc with rfl | rfl <;> assumption
            have hx_mem : x ∈ Xhat \ Yhat := by
              simp [Xhat, Yhat, pairBase, hxX, hxY, hxa, hxb, hxc]
            have hXh_ne : f Xhat ≠ ⊥ := by rw [hXhat]; exact hFX
            rcases h_gs_step hf hXh_ne hYh_ne hx_mem with htr | ⟨u, hu, hsw⟩
            · apply le_max_of_le_left
              rw [← hXhat, ← hYhat]
              refine htr.trans (h_wb_add_mono ?_ ?_)
              · dsimp only [Xhat]
                rw [h_er_ins_ne _ hxc, hbase_er_other X hxa hxb]
                exact hF_ub (Finset.mem_erase.mpr ⟨hxa_symm, haX⟩) hc
              · dsimp only [Yhat]
                rw [hbase_ins_other Y hxa hxb, hF_no_a (by simp [hxa_symm, haY])]
            · obtain ⟨huY, huX⟩ := Finset.mem_sdiff.mp hu
              have hub : u ≠ b := (Finset.mem_erase.mp huY).1
              have hua : u ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp huY).2).1
              have huY_orig : u ∈ Y := (Finset.mem_erase.mp (Finset.mem_erase.mp huY).2).2
              have huX_orig : u ∉ X := fun hm =>
                huX (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hub, Finset.mem_erase.mpr ⟨hua, hm⟩⟩))
              have hu_sdiff : u ∈ Y \ X := Finset.mem_sdiff.mpr ⟨huY_orig, huX_orig⟩
              apply le_max_of_le_right
              refine le_trans ?_ (Finset.le_sup (f := fun y => F (insert y (X.erase x)) + F ((insert x Y).erase y)) hu_sdiff)
              dsimp only
              rw [← hXhat, ← hYhat]
              refine hsw.trans (h_wb_add_mono ?_ ?_)
              · dsimp only [Xhat]
                rw [h_er_ins_ne _ hxc, Finset.insert_comm, hbase_er_other X hxa hxb,
                    hbase_ins_other (X.erase x) hua hub]
                exact hF_ub (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxa_symm, haX⟩)) hc
              · dsimp only [Yhat]
                rw [hbase_ins_other Y hxa hxb, hbase_er_other (insert x Y) hua hub,
                    hF_no_a (fun hm => by simp [hxa_symm, haY] at hm)]
          · have hXhat := hF_no_a haX
            let Xhat := pairBase a b X
            have hx_mem : x ∈ Xhat \ Yhat := by
              simp [Xhat, Yhat, pairBase, hxX, hxY, hxa, hxb]
            have hXh_ne : f Xhat ≠ ⊥ := by rw [hXhat]; exact hFX
            rcases h_gs_step hf hXh_ne hYh_ne hx_mem with htr | ⟨u, hu, hsw⟩
            · apply le_max_of_le_left
              rw [← hXhat, ← hYhat]
              refine htr.trans (h_wb_add_mono ?_ ?_)
              · dsimp only [Xhat]
                rw [hbase_er_other X hxa hxb, hF_no_a (fun hm => haX (Finset.erase_subset x X hm))]
              · dsimp only [Yhat]
                rw [hbase_ins_other Y hxa hxb, hF_no_a (by simp [hxa_symm, haY])]
            · obtain ⟨huY, huX⟩ := Finset.mem_sdiff.mp hu
              have hub : u ≠ b := (Finset.mem_erase.mp huY).1
              have hua : u ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp huY).2).1
              have huY_orig : u ∈ Y := (Finset.mem_erase.mp (Finset.mem_erase.mp huY).2).2
              have huX_orig : u ∉ X := fun hm =>
                huX (Finset.mem_erase.mpr ⟨hub, Finset.mem_erase.mpr ⟨hua, hm⟩⟩)
              have hu_sdiff : u ∈ Y \ X := Finset.mem_sdiff.mpr ⟨huY_orig, huX_orig⟩
              apply le_max_of_le_right
              refine le_trans ?_ (Finset.le_sup (f := fun y => F (insert y (X.erase x)) + F ((insert x Y).erase y)) hu_sdiff)
              dsimp only
              rw [← hXhat, ← hYhat]
              refine hsw.trans (h_wb_add_mono ?_ ?_)
              · dsimp only [Xhat]
                rw [hbase_er_other X hxa hxb, hbase_ins_other (X.erase x) hua hub,
                    hF_no_a (by simp [hua.symm, haX])]
              · dsimp only [Yhat]
                rw [hbase_ins_other Y hxa hxb, hbase_er_other (insert x Y) hua hub,
                    hF_no_a (fun hm => by simp [hxa_symm, haY] at hm)]

  have h_conv : ∀ n (u w : ItemValuation n),
      IsGSValuation u → IsGSValuation w → IsGSValuation (valConvolution u w) := by
    intro n u w hu hw
    have h_stage_n_eq : ∀ S : Finset (Fin (n + n)),
        convStageVal u w n S = u (convUlow n S) + w (convWlow n S) := by
      intro S
      have hm_emp : convMhigh n S = ∅ := by
        ext i; simp [convMhigh]
      simp [convStageVal, hm_emp]

    have h_stage_n_gs : IsGSValuation (convStageVal u w n) := by
      refine ⟨?_, ?_⟩
      · rw [h_stage_n_eq]
        have h1 : convUlow n (∅ : Finset (Fin (n + n))) = ∅ := by ext i; simp [convUlow]
        have h2 : convWlow n (∅ : Finset (Fin (n + n))) = ∅ := by ext i; simp [convWlow]
        simp [h1, h2, hu.1, hw.1]
      · intro X Y hX hY x hx
        simp only [h_stage_n_eq] at hX hY ⊢
        have huX : u (convUlow n X) ≠ ⊥ := fun hb => hX (by simp [hb])
        have hwX : w (convWlow n X) ≠ ⊥ := fun hb => hX (by simp [hb])
        have huY : u (convUlow n Y) ≠ ⊥ := fun hb => hY (by simp [hb])
        have hwY : w (convWlow n Y) ≠ ⊥ := fun hb => hY (by simp [hb])
        obtain ⟨hxX, hxY⟩ := Finset.mem_sdiff.mp hx
        by_cases hlt : x.val < n
        · let ix : Fin n := ⟨x.val, hlt⟩
          have hx_eq : Fin.castAdd n ix = x := by ext; rfl
          have hix_mem : ix ∈ convUlow n X \ convUlow n Y := by
            rw [Finset.mem_sdiff]
            simp only [convUlow, Finset.mem_filter, Finset.mem_univ, true_and, hx_eq]
            exact ⟨⟨ix.isLt, hxX⟩, fun h => hxY h.2⟩
          have hw_er : convWlow n (X.erase x) = convWlow n X := by
            ext j; simp only [convWlow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
            constructor
            · rintro ⟨hj, _, hm⟩; exact ⟨hj, hm⟩
            · rintro ⟨hj, hm⟩; refine ⟨hj, ?_, hm⟩
              intro heq; have := congrArg Fin.val heq; simp [Fin.natAdd] at this; omega
          have hw_ins : convWlow n (insert x Y) = convWlow n Y := by
            ext j; simp only [convWlow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
            constructor
            · rintro ⟨hj, heq | hm⟩
              · have := congrArg Fin.val heq; simp [Fin.natAdd] at this; omega
              · exact ⟨hj, hm⟩
            · rintro ⟨hj, hm⟩; exact ⟨hj, Or.inr hm⟩
          have hu_er : convUlow n (X.erase x) = (convUlow n X).erase ix := by
            ext j; simp only [convUlow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
            constructor
            · rintro ⟨hj, hne, hm⟩
              refine ⟨fun hjx => hne (by subst hjx; exact hx_eq), hj, hm⟩
            · rintro ⟨hne, hj, hm⟩
              refine ⟨hj, fun heq => hne (Fin.castAdd_inj.mp (heq.trans hx_eq.symm)), hm⟩
          have hu_ins : convUlow n (insert x Y) = insert ix (convUlow n Y) := by
            ext j; simp only [convUlow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
            constructor
            · rintro ⟨hj, heq | hm⟩
              · exact Or.inl (Fin.castAdd_inj.mp (heq.trans hx_eq.symm))
              · exact Or.inr ⟨hj, hm⟩
            · rintro (rfl | ⟨hj, hm⟩)
              · exact ⟨hlt, Or.inl hx_eq⟩
              · exact ⟨hj, Or.inr hm⟩
          rcases h_gs_step hu huX huY hix_mem with htr | ⟨iy, hiy, hsw⟩
          · apply le_max_of_le_left
            rw [hu_er, hw_er, hu_ins, hw_ins]
            obtain ⟨ruX, hruX⟩ := WithBot.ne_bot_iff_exists.mp huX
            obtain ⟨rwX, hrwX⟩ := WithBot.ne_bot_iff_exists.mp hwX
            obtain ⟨ruY, hruY⟩ := WithBot.ne_bot_iff_exists.mp huY
            obtain ⟨rwY, hrwY⟩ := WithBot.ne_bot_iff_exists.mp hwY
            rw [← hruX, ← hruY, ← WithBot.coe_add] at htr
            cases hu1 : u ((convUlow n X).erase ix) with
            | bot => rw [hu1] at htr; exact absurd htr (by simp)
            | coe r1 =>
              cases hu2 : u (insert ix (convUlow n Y)) with
              | bot => rw [hu2] at htr; exact absurd htr (by simp)
              | coe r2 =>
                rw [hu1, hu2, ← WithBot.coe_add, WithBot.coe_le_coe] at htr
                rw [← hruX, ← hrwX, ← hruY, ← hrwY, ← WithBot.coe_add, ← WithBot.coe_add,
                    ← WithBot.coe_add, ← WithBot.coe_add, ← WithBot.coe_add, ← WithBot.coe_add,
                    WithBot.coe_le_coe]
                linarith
          · let y := Fin.castAdd n iy
            obtain ⟨hiyY, hiyX⟩ := Finset.mem_sdiff.mp hiy
            have hyY : y ∈ Y := (Finset.mem_filter.mp hiyY).2.2
            have hyX : y ∉ X := fun hm => hiyX (Finset.mem_filter.mpr ⟨Finset.mem_univ _, iy.isLt, hm⟩)
            have hy_sdiff : y ∈ Y \ X := Finset.mem_sdiff.mpr ⟨hyY, hyX⟩
            have hw_sw1 : convWlow n (insert y (X.erase x)) = convWlow n X := by
              rw [← hw_er]
              ext j; simp only [convWlow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
              constructor
              · rintro ⟨hj, heq | hm⟩
                · have := congrArg Fin.val heq; simp [y, Fin.castAdd, Fin.natAdd] at this; omega
                · exact ⟨hj, hm⟩
              · rintro ⟨hj, hm⟩; exact ⟨hj, Or.inr hm⟩
            have hw_sw2 : convWlow n ((insert x Y).erase y) = convWlow n Y := by
              rw [← hw_ins]
              ext j; simp only [convWlow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
              constructor
              · rintro ⟨hj, _, hm⟩; exact ⟨hj, hm⟩
              · rintro ⟨hj, hm⟩; refine ⟨hj, ?_, hm⟩
                intro heq; have := congrArg Fin.val heq; simp [y, Fin.castAdd, Fin.natAdd] at this; omega
            have hu_sw1 : convUlow n (insert y (X.erase x)) = insert iy ((convUlow n X).erase ix) := by
              rw [← hu_er]
              ext j; simp only [convUlow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
              constructor
              · rintro ⟨hj, heq | hm⟩
                · exact Or.inl (Fin.castAdd_inj.mp heq)
                · exact Or.inr ⟨hj, hm⟩
              · rintro (rfl | ⟨hj, hm⟩)
                · exact ⟨j.isLt, Or.inl rfl⟩
                · exact ⟨hj, Or.inr hm⟩
            have hu_sw2 : convUlow n ((insert x Y).erase y) = (insert ix (convUlow n Y)).erase iy := by
              rw [← hu_ins]
              ext j; simp only [convUlow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
              constructor
              · rintro ⟨hj, hne, hm⟩
                exact ⟨fun hjy => hne (by subst hjy; rfl), hj, hm⟩
              · rintro ⟨hne, hj, hm⟩
                exact ⟨hj, fun heq => hne (Fin.castAdd_inj.mp heq), hm⟩
            apply le_max_of_le_right
            refine le_trans ?_ (Finset.le_sup (f := fun z =>
              u (convUlow n (insert z (X.erase x))) + w (convWlow n (insert z (X.erase x))) +
              (u (convUlow n ((insert x Y).erase z)) + w (convWlow n ((insert x Y).erase z)))) hy_sdiff)
            dsimp only
            rw [hu_sw1, hw_sw1, hu_sw2, hw_sw2]
            obtain ⟨ruX, hruX⟩ := WithBot.ne_bot_iff_exists.mp huX
            obtain ⟨rwX, hrwX⟩ := WithBot.ne_bot_iff_exists.mp hwX
            obtain ⟨ruY, hruY⟩ := WithBot.ne_bot_iff_exists.mp huY
            obtain ⟨rwY, hrwY⟩ := WithBot.ne_bot_iff_exists.mp hwY
            rw [← hruX, ← hruY, ← WithBot.coe_add] at hsw
            cases hu1 : u (insert iy ((convUlow n X).erase ix)) with
            | bot => rw [hu1] at hsw; exact absurd hsw (by simp)
            | coe r1 =>
              cases hu2 : u ((insert ix (convUlow n Y)).erase iy) with
              | bot => rw [hu2] at hsw; exact absurd hsw (by simp)
              | coe r2 =>
                rw [hu1, hu2, ← WithBot.coe_add, WithBot.coe_le_coe] at hsw
                rw [← hruX, ← hrwX, ← hruY, ← hrwY, ← WithBot.coe_add, ← WithBot.coe_add,
                    ← WithBot.coe_add, ← WithBot.coe_add, ← WithBot.coe_add, ← WithBot.coe_add,
                    WithBot.coe_le_coe]
                linarith
        · 
          let ix : Fin n := ⟨x.val - n, by omega⟩
          have hx_eq : Fin.natAdd n ix = x := by ext; simp [Fin.natAdd, ix]; omega
          have hix_mem : ix ∈ convWlow n X \ convWlow n Y := by
            rw [Finset.mem_sdiff]
            simp only [convWlow, Finset.mem_filter, Finset.mem_univ, true_and, hx_eq]
            exact ⟨⟨ix.isLt, hxX⟩, fun h => hxY h.2⟩
          have hu_er : convUlow n (X.erase x) = convUlow n X := by
            ext j; simp only [convUlow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
            constructor
            · rintro ⟨hj, _, hm⟩; exact ⟨hj, hm⟩
            · rintro ⟨hj, hm⟩; refine ⟨hj, ?_, hm⟩
              intro heq; have := congrArg Fin.val heq; simp [Fin.castAdd] at this; omega
          have hu_ins : convUlow n (insert x Y) = convUlow n Y := by
            ext j; simp only [convUlow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
            constructor
            · rintro ⟨hj, heq | hm⟩
              · have := congrArg Fin.val heq; simp [Fin.castAdd] at this; omega
              · exact ⟨hj, hm⟩
            · rintro ⟨hj, hm⟩; exact ⟨hj, Or.inr hm⟩
          have hw_er : convWlow n (X.erase x) = (convWlow n X).erase ix := by
            ext j; simp only [convWlow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
            constructor
            · rintro ⟨hj, hne, hm⟩
              refine ⟨fun hjx => hne (by subst hjx; exact hx_eq), hj, hm⟩
            · rintro ⟨hne, hj, hm⟩
              refine ⟨hj, fun heq => hne ((Fin.natAdd_inj n).mp (heq.trans hx_eq.symm)), hm⟩
          have hw_ins : convWlow n (insert x Y) = insert ix (convWlow n Y) := by
            ext j; simp only [convWlow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
            constructor
            · rintro ⟨hj, heq | hm⟩
              · exact Or.inl ((Fin.natAdd_inj n).mp (heq.trans hx_eq.symm))
              · exact Or.inr ⟨hj, hm⟩
            · rintro (rfl | ⟨hj, hm⟩)
              · exact ⟨ix.isLt, Or.inl hx_eq⟩
              · exact ⟨hj, Or.inr hm⟩
          rcases h_gs_step hw hwX hwY hix_mem with htr | ⟨iy, hiy, hsw⟩
          · apply le_max_of_le_left
            rw [hu_er, hw_er, hu_ins, hw_ins]
            obtain ⟨ruX, hruX⟩ := WithBot.ne_bot_iff_exists.mp huX
            obtain ⟨rwX, hrwX⟩ := WithBot.ne_bot_iff_exists.mp hwX
            obtain ⟨ruY, hruY⟩ := WithBot.ne_bot_iff_exists.mp huY
            obtain ⟨rwY, hrwY⟩ := WithBot.ne_bot_iff_exists.mp hwY
            rw [← hrwX, ← hrwY, ← WithBot.coe_add] at htr
            cases hw1 : w ((convWlow n X).erase ix) with
            | bot => rw [hw1] at htr; exact absurd htr (by simp)
            | coe r1 =>
              cases hw2 : w (insert ix (convWlow n Y)) with
              | bot => rw [hw2] at htr; exact absurd htr (by simp)
              | coe r2 =>
                rw [hw1, hw2, ← WithBot.coe_add, WithBot.coe_le_coe] at htr
                rw [← hruX, ← hrwX, ← hruY, ← hrwY, ← WithBot.coe_add, ← WithBot.coe_add,
                    ← WithBot.coe_add, ← WithBot.coe_add, ← WithBot.coe_add, ← WithBot.coe_add,
                    WithBot.coe_le_coe]
                linarith
          · let y := Fin.natAdd n iy
            obtain ⟨hiyY, hiyX⟩ := Finset.mem_sdiff.mp hiy
            have hyY : y ∈ Y := (Finset.mem_filter.mp hiyY).2.2
            have hyX : y ∉ X := fun hm => hiyX (Finset.mem_filter.mpr ⟨Finset.mem_univ _, iy.isLt, hm⟩)
            have hy_sdiff : y ∈ Y \ X := Finset.mem_sdiff.mpr ⟨hyY, hyX⟩
            have hu_sw1 : convUlow n (insert y (X.erase x)) = convUlow n X := by
              rw [← hu_er]
              ext j; simp only [convUlow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
              constructor
              · rintro ⟨hj, heq | hm⟩
                · have := congrArg Fin.val heq; simp [y, Fin.castAdd] at this; omega
                · exact ⟨hj, hm⟩
              · rintro ⟨hj, hm⟩; exact ⟨hj, Or.inr hm⟩
            have hu_sw2 : convUlow n ((insert x Y).erase y) = convUlow n Y := by
              rw [← hu_ins]
              ext j; simp only [convUlow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
              constructor
              · rintro ⟨hj, _, hm⟩; exact ⟨hj, hm⟩
              · rintro ⟨hj, hm⟩; refine ⟨hj, ?_, hm⟩
                intro heq; have := congrArg Fin.val heq; simp [y, Fin.castAdd] at this; omega
            have hw_sw1 : convWlow n (insert y (X.erase x)) = insert iy ((convWlow n X).erase ix) := by
              rw [← hw_er]
              ext j; simp only [convWlow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
              constructor
              · rintro ⟨hj, heq | hm⟩
                · exact Or.inl ((Fin.natAdd_inj n).mp heq)
                · exact Or.inr ⟨hj, hm⟩
              · rintro (rfl | ⟨hj, hm⟩)
                · exact ⟨j.isLt, Or.inl rfl⟩
                · exact ⟨hj, Or.inr hm⟩
            have hw_sw2 : convWlow n ((insert x Y).erase y) = (insert ix (convWlow n Y)).erase iy := by
              rw [← hw_ins]
              ext j; simp only [convWlow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
              constructor
              · rintro ⟨hj, hne, hm⟩
                exact ⟨fun hjy => hne (by subst hjy; rfl), hj, hm⟩
              · rintro ⟨hne, hj, hm⟩
                exact ⟨hj, fun heq => hne ((Fin.natAdd_inj n).mp heq), hm⟩
            apply le_max_of_le_right
            refine le_trans ?_ (Finset.le_sup (f := fun z =>
              u (convUlow n (insert z (X.erase x))) + w (convWlow n (insert z (X.erase x))) +
              (u (convUlow n ((insert x Y).erase z)) + w (convWlow n ((insert x Y).erase z)))) hy_sdiff)
            dsimp only
            rw [hu_sw1, hw_sw1, hu_sw2, hw_sw2]
            obtain ⟨ruX, hruX⟩ := WithBot.ne_bot_iff_exists.mp huX
            obtain ⟨rwX, hrwX⟩ := WithBot.ne_bot_iff_exists.mp hwX
            obtain ⟨ruY, hruY⟩ := WithBot.ne_bot_iff_exists.mp huY
            obtain ⟨rwY, hrwY⟩ := WithBot.ne_bot_iff_exists.mp hwY
            rw [← hrwX, ← hrwY, ← WithBot.coe_add] at hsw
            cases hw1 : w (insert iy ((convWlow n X).erase ix)) with
            | bot => rw [hw1] at hsw; exact absurd hsw (by simp)
            | coe r1 =>
              cases hw2 : w ((insert ix (convWlow n Y)).erase iy) with
              | bot => rw [hw2] at hsw; exact absurd hsw (by simp)
              | coe r2 =>
                rw [hw1, hw2, ← WithBot.coe_add, WithBot.coe_le_coe] at hsw
                rw [← hruX, ← hrwX, ← hruY, ← hrwY, ← WithBot.coe_add, ← WithBot.coe_add,
                    ← WithBot.coe_add, ← WithBot.coe_add, ← WithBot.coe_add, ← WithBot.coe_add,
                    WithBot.coe_le_coe]
                linarith

    
    have h_stage_step : ∀ (k : ℕ) (hk : k < n),
        convStageVal u w k =
          mergePair (Fin.castAdd n ⟨k, hk⟩) (Fin.natAdd n ⟨k, hk⟩) (convStageVal u w (k + 1)) := by
      intro k hk
      let ik : Fin n := ⟨k, hk⟩
      let a := Fin.castAdd n ik
      let b := Fin.natAdd n ik
      have hab : a ≠ b := by
        intro h; have := congrArg Fin.val h; simp [a, b, ik] at this; omega
      have h_cast_ne_b : ∀ j : Fin n, Fin.castAdd n j ≠ b := by
        intro j h; have := congrArg Fin.val h; simp [b, ik, Fin.castAdd] at this; omega
      have h_nat_ne_a : ∀ j : Fin n, Fin.natAdd n j ≠ a := by
        intro j h; have := congrArg Fin.val h; simp [a, ik, Fin.natAdd] at this; omega
      funext S
      let S0 := pairBase a b S
      have h_U0 : convUlow (k + 1) S0 = convUlow k S := by
        ext j
        simp only [convUlow, S0, pairBase, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
        constructor
        · rintro ⟨hj, _, hnea, hm⟩
          have hjk : j.val ≠ k := fun h => hnea (congrArg (Fin.castAdd n) (Fin.ext h))
          exact ⟨by omega, hm⟩
        · rintro ⟨hj, hm⟩
          refine ⟨by omega, h_cast_ne_b j, ?_, hm⟩
          intro heq
          have hval := congrArg Fin.val (Fin.castAdd_inj.mp heq)
          dsimp [ik] at hval
          omega
      have h_W0 : convWlow (k + 1) S0 = convWlow k S := by
        ext j
        simp only [convWlow, S0, pairBase, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
        constructor
        · rintro ⟨hj, hneb, _, hm⟩
          have hjk : j.val ≠ k := fun h => hneb (congrArg (Fin.natAdd n) (Fin.ext h))
          exact ⟨by omega, hm⟩
        · rintro ⟨hj, hm⟩
          refine ⟨by omega, ?_, h_nat_ne_a j, hm⟩
          intro heq
          have hval := congrArg Fin.val ((Fin.natAdd_inj n).mp heq)
          dsimp [ik] at hval
          omega
      have h_M0 : convMhigh (k + 1) S0 = (convMhigh k S).erase ik := by
        ext j
        simp only [convMhigh, S0, pairBase, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
        constructor
        · rintro ⟨hj, _, _, hm⟩
          refine ⟨fun hjik => by subst hjik; dsimp [ik] at hj; omega, by omega, hm⟩
        · rintro ⟨hne, hj, hm⟩
          have hjk : j.val ≠ k := fun h => hne (Fin.ext h)
          exact ⟨by omega, h_cast_ne_b j, fun heq => hne (Fin.castAdd_inj.mp heq), hm⟩
      by_cases haS : a ∈ S
      · 
        dsimp only [mergePair]
        rw [if_pos haS]
        change _ = max (convStageVal u w (k + 1) (insert a S0)) (convStageVal u w (k + 1) (insert b S0))
        have hik_M : ik ∈ convMhigh k S := by
          simp only [convMhigh, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨le_rfl, haS⟩
        let M0 := (convMhigh k S).erase ik
        have hM_ins : convMhigh k S = insert ik M0 := (Finset.insert_erase hik_M).symm
        have h_Ua : convUlow (k + 1) (insert a S0) = insert ik (convUlow k S) := by
          rw [← h_U0]
          ext j; simp only [convUlow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · rintro ⟨hj, heq | hm⟩
            · exact Or.inl (Fin.castAdd_inj.mp heq)
            · exact Or.inr ⟨hj, hm⟩
          · rintro (rfl | ⟨hj, hm⟩)
            · exact ⟨by simp [ik], Or.inl rfl⟩
            · exact ⟨hj, Or.inr hm⟩
        have h_Wa : convWlow (k + 1) (insert a S0) = convWlow k S := by
          rw [← h_W0]
          ext j; simp only [convWlow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          exact ⟨fun ⟨hj, h⟩ => ⟨hj, h.resolve_left (h_nat_ne_a j)⟩, fun ⟨hj, hm⟩ => ⟨hj, Or.inr hm⟩⟩
        have h_Ma : convMhigh (k + 1) (insert a S0) = M0 := by
          dsimp only [M0]; rw [← h_M0]
          ext j; simp only [convMhigh, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · rintro ⟨hj, heq | hm⟩
            · have := Fin.castAdd_inj.mp heq; subst this; simp [ik] at hj
            · exact ⟨hj, hm⟩
          · rintro ⟨hj, hm⟩; exact ⟨hj, Or.inr hm⟩
        have h_Ub : convUlow (k + 1) (insert b S0) = convUlow k S := by
          rw [← h_U0]
          ext j; simp only [convUlow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          exact ⟨fun ⟨hj, h⟩ => ⟨hj, h.resolve_left (h_cast_ne_b j)⟩, fun ⟨hj, hm⟩ => ⟨hj, Or.inr hm⟩⟩
        have h_Wb : convWlow (k + 1) (insert b S0) = insert ik (convWlow k S) := by
          rw [← h_W0]
          ext j; simp only [convWlow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · rintro ⟨hj, heq | hm⟩
            · exact Or.inl ((Fin.natAdd_inj n).mp heq)
            · exact Or.inr ⟨hj, hm⟩
          · rintro (rfl | ⟨hj, hm⟩)
            · exact ⟨by simp [ik], Or.inl rfl⟩
            · exact ⟨hj, Or.inr hm⟩
        have h_Mb : convMhigh (k + 1) (insert b S0) = M0 := by
          dsimp only [M0]; rw [← h_M0]
          ext j; simp only [convMhigh, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          exact ⟨fun ⟨hj, h⟩ => ⟨hj, h.resolve_left (h_cast_ne_b j)⟩, fun ⟨hj, hm⟩ => ⟨hj, Or.inr hm⟩⟩
        dsimp only [convStageVal]
        rw [hM_ins, Finset.powerset_insert, Finset.sup_union, Finset.sup_image,
            h_Ua, h_Wa, h_Ma, h_Ub, h_Wb, h_Mb, max_comm]
        have hik_not_M0 : ik ∉ M0 := Finset.notMem_erase ik _
        have h_left : M0.powerset.sup (fun T =>
            u (convUlow k S ∪ T) + w (convWlow k S ∪ (insert ik M0 \ T))) =
          M0.powerset.sup (fun T =>
            u (convUlow k S ∪ T) + w (insert ik (convWlow k S) ∪ (M0 \ T))) := by
          refine Finset.sup_congr rfl (fun T hT => ?_)
          have hik_not_T : ik ∉ T := fun hm => hik_not_M0 (Finset.mem_powerset.mp hT hm)
          have hset : convWlow k S ∪ (insert ik M0 \ T) = insert ik (convWlow k S) ∪ (M0 \ T) := by
            ext z; simp [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert]
            by_cases hzik : z = ik <;> simp_all
          rw [hset]
        have h_right : M0.powerset.sup ((fun T =>
            u (convUlow k S ∪ T) + w (convWlow k S ∪ (insert ik M0 \ T))) ∘ insert ik) =
          M0.powerset.sup (fun T =>
            u (insert ik (convUlow k S) ∪ T) + w (convWlow k S ∪ (M0 \ T))) := by
          refine Finset.sup_congr rfl (fun T hT => ?_)
          dsimp only [Function.comp_apply]
          have hset1 : convUlow k S ∪ insert ik T = insert ik (convUlow k S) ∪ T := by
            ext z; simp [Finset.mem_union, Finset.mem_insert]
          have hset2 : insert ik M0 \ insert ik T = M0 \ T := by
            ext z; simp [Finset.mem_sdiff, Finset.mem_insert]
            by_cases hzik : z = ik <;> simp_all
          rw [hset1, hset2]
        rw [h_left, h_right]
      · 
        dsimp only [mergePair]
        rw [if_neg haS]
        change _ = convStageVal u w (k + 1) S0
        have hik_not : ik ∉ convMhigh k S := fun hm => haS (Finset.mem_filter.mp hm).2.2
        have hM_eq : convMhigh (k + 1) S0 = convMhigh k S := by
          rw [h_M0, Finset.erase_eq_of_notMem hik_not]
        dsimp only [convStageVal]
        rw [hM_eq, h_U0, h_W0]

    have h_stage_gs : ∀ d k : ℕ, k + d = n → IsGSValuation (convStageVal u w k) := by
      intro d
      induction d with
      | zero =>
        intro k hk
        obtain rfl : k = n := by omega
        exact h_stage_n_gs
      | succ d ih =>
        intro k hk
        have hlt : k < n := by omega
        have hstep := ih (k + 1) (by omega)
        have hab : Fin.castAdd n ⟨k, hlt⟩ ≠ Fin.natAdd n ⟨k, hlt⟩ := by
          intro h; have := congrArg Fin.val h; simp [Fin.castAdd, Fin.natAdd] at this; omega
        rw [h_stage_step k hlt]
        exact h_mergePair_gs _ _ hab _ hstep

    have h_conv_eq : valConvolution u w = pullbackVal (Fin.castAddEmb n) (convStageVal u w 0) := by
      funext S
      dsimp [valConvolution, pullbackVal, convStageVal]
      have hU : convUlow 0 (S.map (Fin.castAddEmb n)) = ∅ := by
        ext i; simp [convUlow]
      have hW : convWlow 0 (S.map (Fin.castAddEmb n)) = ∅ := by
        ext i; simp [convWlow]
      have hM : convMhigh 0 (S.map (Fin.castAddEmb n)) = S := by
        ext i
        simp only [convMhigh, Finset.mem_filter, Finset.mem_univ, true_and, Nat.zero_le, Finset.mem_map]
        exact ⟨fun ⟨a, ha, h⟩ => by
          have hval := congrArg Fin.val h
          have hai : a = i := Fin.ext hval
          exact hai ▸ ha, fun hi => ⟨i, hi, rfl⟩⟩
      rw [hU, hW, hM]
      refine Finset.sup_congr rfl (fun T _ => ?_)
      simp

    rw [h_conv_eq]
    exact h_pullback_gs (Fin.castAddEmb n) (convStageVal u w 0) (h_stage_gs n 0 (Nat.zero_add n))

  
  have coe_unbotD : ∀ {z : WithBot ℝ}, z ≠ ⊥ → ((z.unbotD 0 : ℝ) : WithBot ℝ) = z := by
    intro z hz
    obtain ⟨r, rfl⟩ := WithBot.ne_bot_iff_exists.mp hz
    rw [WithBot.unbotD_coe]

  have h_unbot_add : ∀ {a b : WithBot ℝ} {r : ℝ},
      ((r : ℝ) : WithBot ℝ) ≤ a + b →
        ∃ r1 r2 : ℝ, a = ((r1 : ℝ) : WithBot ℝ) ∧ b = ((r2 : ℝ) : WithBot ℝ) ∧ r ≤ r1 + r2 := by
    intro a b r hab
    cases a with
    | bot => simp at hab
    | coe r1 =>
      cases b with
      | bot => simp at hab
      | coe r2 =>
        refine ⟨r1, r2, rfl, rfl, ?_⟩
        rw [← WithBot.coe_add, WithBot.coe_le_coe] at hab
        exact hab

  have h_gs_cases : ∀ {n : ℕ} {v : ItemValuation n}, IsGSValuation v →
      ∀ {X Y : Finset (Fin n)} {rX rY : ℝ},
        v X = ((rX : ℝ) : WithBot ℝ) → v Y = ((rY : ℝ) : WithBot ℝ) →
        ∀ {x : Fin n}, x ∈ X \ Y →
          (∃ r1 r2 : ℝ,
            v (X.erase x) = ((r1 : ℝ) : WithBot ℝ) ∧
            v (insert x Y) = ((r2 : ℝ) : WithBot ℝ) ∧
            rX + rY ≤ r1 + r2) ∨
          (∃ y ∈ Y \ X, ∃ r1 r2 : ℝ,
            v (insert y (X.erase x)) = ((r1 : ℝ) : WithBot ℝ) ∧
            v ((insert x Y).erase y) = ((r2 : ℝ) : WithBot ℝ) ∧
            rX + rY ≤ r1 + r2) := by
    intro n v hv X Y rX rY hvX hvY x hx
    have hex := hv.2 X Y (by simp [hvX]) (by simp [hvY]) x hx
    rw [hvX, hvY, ← WithBot.coe_add, le_max_iff] at hex
    rcases hex with hT | hS
    · exact Or.inl (h_unbot_add hT)
    · have hne : (Y \ X).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        rw [hemp, Finset.sup_empty] at hS
        exact absurd hS (by simp)
      obtain ⟨y, hy, hsup⟩ := Finset.exists_mem_eq_sup (Y \ X) hne
        (fun y => v (insert y (X.erase x)) + v ((insert x Y).erase y))
      rw [hsup] at hS
      exact Or.inr ⟨y, hy, h_unbot_add hS⟩

  have h_build_transfer : ∀ {n : ℕ} (v : ItemValuation n) (X Y : Finset (Fin n)) (x : Fin n)
      {rX rY r1 r2 : ℝ},
      v X = ((rX : ℝ) : WithBot ℝ) → v Y = ((rY : ℝ) : WithBot ℝ) →
      v (X.erase x) = ((r1 : ℝ) : WithBot ℝ) → v (insert x Y) = ((r2 : ℝ) : WithBot ℝ) →
      rX + rY ≤ r1 + r2 →
      v X + v Y ≤
        max (v (X.erase x) + v (insert x Y))
            ((Y \ X).sup (fun y => v (insert y (X.erase x)) + v ((insert x Y).erase y))) := by
    intro n v X Y x rX rY r1 r2 hvX hvY h1 h2 hle
    apply le_max_of_le_left
    rw [hvX, hvY, h1, h2, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
    exact hle

  have h_build_swap : ∀ {n : ℕ} (v : ItemValuation n) (X Y : Finset (Fin n)) (x y : Fin n)
      {rX rY r1 r2 : ℝ},
      y ∈ Y \ X →
      v X = ((rX : ℝ) : WithBot ℝ) → v Y = ((rY : ℝ) : WithBot ℝ) →
      v (insert y (X.erase x)) = ((r1 : ℝ) : WithBot ℝ) →
      v ((insert x Y).erase y) = ((r2 : ℝ) : WithBot ℝ) →
      rX + rY ≤ r1 + r2 →
      v X + v Y ≤
        max (v (X.erase x) + v (insert x Y))
            ((Y \ X).sup (fun z => v (insert z (X.erase x)) + v ((insert x Y).erase z))) := by
    intro n v X Y x y rX rY r1 r2 hy hvX hvY h1 h2 hle
    apply le_max_of_le_right
    refine le_trans ?_ (Finset.le_sup (f := fun z => v (insert z (X.erase x)) + v ((insert x Y).erase z)) hy)
    dsimp only
    rw [hvX, hvY, h1, h2, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
    exact hle

  have h_mod_transfer : ∀ {n : ℕ} (a : Fin n → ℝ) {X Y : Finset (Fin n)} {x : Fin n},
      x ∈ X \ Y →
      (∑ g ∈ X.erase x, a g) + (∑ g ∈ insert x Y, a g) = (∑ g ∈ X, a g) + (∑ g ∈ Y, a g) := by
    intro n a X Y x hx
    have hxX : x ∈ X := (Finset.mem_sdiff.mp hx).1
    have hxY : x ∉ Y := (Finset.mem_sdiff.mp hx).2
    have h1 := Finset.sum_erase_add X a hxX
    have h2 := Finset.sum_insert hxY (f := a)
    linarith

  have h_mod_swap : ∀ {n : ℕ} (a : Fin n → ℝ) {X Y : Finset (Fin n)} {x y : Fin n},
      x ∈ X \ Y → y ∈ Y \ X →
      (∑ g ∈ insert y (X.erase x), a g) + (∑ g ∈ (insert x Y).erase y, a g) =
        (∑ g ∈ X, a g) + (∑ g ∈ Y, a g) := by
    intro n a X Y x y hx hy
    have hxX : x ∈ X := (Finset.mem_sdiff.mp hx).1
    have hxY : x ∉ Y := (Finset.mem_sdiff.mp hx).2
    have hyY : y ∈ Y := (Finset.mem_sdiff.mp hy).1
    have hyX : y ∉ X := (Finset.mem_sdiff.mp hy).2
    have hy_er : y ∉ X.erase x := fun hm => hyX (Finset.erase_subset x X hm)
    have hy_ins : y ∈ insert x Y := Finset.mem_insert_of_mem hyY
    have h1 := Finset.sum_erase_add X a hxX
    have h2 := Finset.sum_insert hy_er (f := a)
    have h3 := Finset.sum_erase_add (insert x Y) a hy_ins
    have h4 := Finset.sum_insert hxY (f := a)
    linarith

  have h_zero_gs : ∀ n, IsGSValuation (zeroVal n) := by
    intro n
    refine ⟨rfl, fun X Y _ _ x _ => ?_⟩
    apply le_max_of_le_left
    simp [zeroVal]

  have h_submod : ∀ n (v : ItemValuation n),
      IsGSValuation v → IsFiniteValuation v → IsSubmodularReal (realVal v) := by
    intro n v hv hfin
    refine ⟨by simp [realVal, hv.1], ?_⟩
    intro Q R hQR g hgR
    have hgQ : g ∉ Q := fun hg => hgR (hQR hg)
    have hg_mem : g ∈ insert g R \ Q := Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self g R, hgQ⟩
    have hex := hv.2 (insert g R) Q (hfin _) (hfin _) g hg_mem
    have hsdiff_emp : Q \ insert g R = ∅ :=
      Finset.sdiff_eq_empty_iff_subset.mpr (hQR.trans (Finset.subset_insert g R))
    rw [Finset.erase_insert hgR, hsdiff_emp, Finset.sup_empty, max_bot_right] at hex
    have hc1 := coe_unbotD (hfin (insert g R))
    have hc2 := coe_unbotD (hfin Q)
    have hc3 := coe_unbotD (hfin R)
    have hc4 := coe_unbotD (hfin (insert g Q))
    dsimp [realVal]
    rw [← hc1, ← hc2, ← hc3, ← hc4, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe] at hex
    linarith

  have h_addMod : ∀ n (v : ItemValuation n) (a : Fin n → ℝ),
      IsGSValuation v → IsGSValuation (addModular v a) := by
    intro n v a hv
    refine ⟨by simp [addModular, hv.1], ?_⟩
    intro X Y hX hY x hx
    cases hvX : v X with
    | bot => simp [addModular, hvX] at hX
    | coe rX =>
      cases hvY : v Y with
      | bot => simp [addModular, hvY] at hY
      | coe rY =>
        rcases h_gs_cases hv hvX hvY hx with ⟨r1, r2, h1, h2, hle⟩ | ⟨y, hy, r1, r2, h1, h2, hle⟩
        · refine h_build_transfer (addModular v a) X Y x
            (rX := rX + ∑ g ∈ X, a g) (rY := rY + ∑ g ∈ Y, a g)
            (r1 := r1 + ∑ g ∈ X.erase x, a g) (r2 := r2 + ∑ g ∈ insert x Y, a g)
            (by simp only [addModular, hvX, ← WithBot.coe_add])
            (by simp only [addModular, hvY, ← WithBot.coe_add])
            (by simp only [addModular, h1, ← WithBot.coe_add])
            (by simp only [addModular, h2, ← WithBot.coe_add]) ?_
          linarith [h_mod_transfer a hx]
        · refine h_build_swap (addModular v a) X Y x y hy
            (rX := rX + ∑ g ∈ X, a g) (rY := rY + ∑ g ∈ Y, a g)
            (r1 := r1 + ∑ g ∈ insert y (X.erase x), a g) (r2 := r2 + ∑ g ∈ (insert x Y).erase y, a g)
            (by simp only [addModular, hvX, ← WithBot.coe_add])
            (by simp only [addModular, hvY, ← WithBot.coe_add])
            (by simp only [addModular, h1, ← WithBot.coe_add])
            (by simp only [addModular, h2, ← WithBot.coe_add]) ?_
          linarith [h_mod_swap a hx hy]

  have env_spec : ∀ {n : ℕ} (v : ItemValuation n), IsGSValuation v →
      ∀ S : Finset (Fin n),
        disposalEnvelopeVal v S = S.powerset.sup v ∧
        (∀ T ⊆ S, v T ≤ disposalEnvelopeVal v S) ∧
        (∃ X ⊆ S, v X = disposalEnvelopeVal v S ∧ v X ≠ ⊥) := by
    intro n v hv S
    have h0_mem : (∅ : Finset (Fin n)) ∈ S.powerset := Finset.empty_mem_powerset S
    have h0_le : ((0 : ℝ) : WithBot ℝ) ≤ S.powerset.sup v := by
      rw [← hv.1]; exact Finset.le_sup h0_mem
    have hsup_ne : S.powerset.sup v ≠ ⊥ := by
      intro hb; rw [hb, le_bot_iff] at h0_le; exact WithBot.coe_ne_bot h0_le
    have h_coe : disposalEnvelopeVal v S = S.powerset.sup v := coe_unbotD hsup_ne
    have h_ub : ∀ T ⊆ S, v T ≤ disposalEnvelopeVal v S := by
      intro T hTS; rw [h_coe]; exact Finset.le_sup (Finset.mem_powerset.mpr hTS)
    obtain ⟨X, hX_mem, hX_eq⟩ := Finset.exists_mem_eq_sup S.powerset ⟨∅, h0_mem⟩ v
    have hX_val : v X = disposalEnvelopeVal v S := by rw [h_coe, hX_eq]
    have hX_ne : v X ≠ ⊥ := by rw [hX_val]; exact WithBot.coe_ne_bot
    exact ⟨h_coe, h_ub, ⟨X, Finset.mem_powerset.mp hX_mem, hX_val, hX_ne⟩⟩

  have h_env_basic : ∀ n (v : ItemValuation n), IsGSValuation v →
      disposalEnvelopeVal v = valConvolution v (zeroVal n) ∧
      IsFiniteValuation (disposalEnvelopeVal v) ∧
      IsNonnegValuation (disposalEnvelopeVal v) ∧
      IsMonotoneValuation (disposalEnvelopeVal v) := by
    intro n v hv
    refine ⟨?_, ?_, ?_, ?_⟩
    · funext S
      rw [(env_spec v hv S).1]
      dsimp [valConvolution, zeroVal]
      refine Finset.sup_congr rfl (fun T _ => ?_)
      cases v T <;> simp
    · intro S; exact WithBot.coe_ne_bot
    · intro S
      have h0 := (env_spec v hv S).2.1 ∅ (Finset.empty_subset S)
      rwa [hv.1] at h0
    · intro S T hST
      rw [(env_spec v hv S).1, (env_spec v hv T).1]
      exact Finset.sup_mono (Finset.powerset_mono.mpr hST)

  have h_optWelfare : ∀ n m (v : Fin m → ItemValuation n), (∀ i, IsGSValuation (v i)) →
      optWelfare (fun i => disposalEnvelopeVal (v i)) = optWelfare v := by
    intro n m v hv
    let w : Fin m → ItemValuation n := fun i => disposalEnvelopeVal (v i)
    let Aset := (Finset.univ : Finset (Fin m → Finset (Fin n))).filter (fun X => IsAllocOf Finset.univ X)
    suffices h_sup_eq : Aset.sup (allocWelfare w) = Aset.sup (allocWelfare v) by
      dsimp [optWelfare, optWelfareOn]
      exact congrArg (WithBot.unbotD 0) h_sup_eq
    refine le_antisymm ?_ ?_
    · refine Finset.sup_le (fun X hX => ?_)
      have hX_alloc : IsAllocOf Finset.univ X := (Finset.mem_filter.mp hX).2
      have h_ex : ∀ i : Fin m, ∃ Y ⊆ X i, v i Y = w i (X i) := by
        intro i
        obtain ⟨Y, hYX, hvY, _⟩ := (env_spec (v i) (hv i) (X i)).2.2
        exact ⟨Y, hYX, hvY⟩
      let Y : Fin m → Finset (Fin n) := fun i => Classical.choose (h_ex i)
      have hY_sub : ∀ i : Fin m, Y i ⊆ X i := fun i => (Classical.choose_spec (h_ex i)).1
      have hY_val : ∀ i : Fin m, v i (Y i) = w i (X i) := fun i => (Classical.choose_spec (h_ex i)).2
      have hY_alloc : IsAllocOf Finset.univ Y :=
        ⟨fun _ => Finset.subset_univ _,
         fun i j hij => Disjoint.mono (hY_sub i) (hY_sub j) (hX_alloc.2 i j hij)⟩
      have hY_mem : Y ∈ Aset := Finset.mem_filter.mpr ⟨Finset.mem_univ Y, hY_alloc⟩
      have h_eq_w : allocWelfare w X = allocWelfare v Y := by
        dsimp [allocWelfare]
        exact Finset.sum_congr rfl (fun i _ => (hY_val i).symm)
      rw [h_eq_w]
      exact Finset.le_sup hY_mem
    · refine Finset.sup_le (fun X hX => ?_)
      have h_le : allocWelfare v X ≤ allocWelfare w X := by
        dsimp [allocWelfare]
        exact Finset.sum_le_sum (fun i _ => (env_spec (v i) (hv i) (X i)).2.1 (X i) Finset.Subset.rfl)
      exact h_le.trans (Finset.le_sup hX)

  have h_matroid : ∀ n (M : Matroid (Fin n)) (w : Fin n → ℝ),
      IsGSValuation (weightedMatroidVal M w) ∧
      weightedMatroidRankVal M w = disposalEnvelopeVal (weightedMatroidVal M w) := by
    intro n M w
    refine ⟨?_, ?_⟩
    · have h_rep_aug : ∀ (d : ℕ) (A B : Finset (Fin n)),
          B.card - A.card = d →
          M.Indep (A : Set (Fin n)) → M.Indep (B : Set (Fin n)) → A.card ≤ B.card →
            ∃ K : Finset (Fin n),
              A ⊆ K ∧ K ⊆ A ∪ B ∧ M.Indep (K : Set (Fin n)) ∧ K.card = B.card := by
        intro d
        induction d with
        | zero =>
          intro A B hd hA _ hle
          exact ⟨A, Finset.Subset.refl A, Finset.subset_union_left, hA, by omega⟩
        | succ d ih =>
          intro A B hd hA hB hle
          have hlt : A.card < B.card := by omega
          have henc : (A : Set (Fin n)).encard < (B : Set (Fin n)).encard := by
            rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard]
            exact_mod_cast hlt
          obtain ⟨e, he, he_ind⟩ := hA.exists_insert_of_encard_lt hB henc
          have heB : e ∈ B := he.1
          have heA : e ∉ A := he.2
          have hA'_ind : M.Indep ((insert e A : Finset (Fin n)) : Set (Fin n)) := by
            simpa [Finset.coe_insert] using he_ind
          have hcardA' : (insert e A).card = A.card + 1 := Finset.card_insert_of_notMem heA
          obtain ⟨K, hAK, hKB, hKind, hKcard⟩ :=
            ih (insert e A) B (by omega) hA'_ind hB (by omega)
          refine ⟨K, (Finset.subset_insert e A).trans hAK, hKB.trans ?_, hKind, hKcard⟩
          intro z hz
          rcases Finset.mem_union.mp hz with hz1 | hz2
          · rcases Finset.mem_insert.mp hz1 with rfl | hzA
            · exact Finset.mem_union_right _ heB
            · exact Finset.mem_union_left _ hzA
          · exact Finset.mem_union_right _ hz2
      refine ⟨by simp [weightedMatroidVal, M.empty_indep], ?_⟩
      intro X Y hX hY x hx
      by_cases hIX : M.Indep (X : Set (Fin n))
      · by_cases hIY : M.Indep (Y : Set (Fin n))
        · have hxX : x ∈ X := (Finset.mem_sdiff.mp hx).1
          have hxY : x ∉ Y := (Finset.mem_sdiff.mp hx).2
          have hIX_er : M.Indep ((X.erase x : Finset (Fin n)) : Set (Fin n)) :=
            hIX.subset (Finset.coe_subset.mpr (Finset.erase_subset x X))
          by_cases hIY_ins : M.Indep ((insert x Y : Finset (Fin n)) : Set (Fin n))
          · refine h_build_transfer (weightedMatroidVal M w) X Y x
              (rX := ∑ g ∈ X, w g) (rY := ∑ g ∈ Y, w g)
              (r1 := ∑ g ∈ X.erase x, w g) (r2 := ∑ g ∈ insert x Y, w g)
              (by simp only [weightedMatroidVal, hIX, ↓reduceIte])
              (by simp only [weightedMatroidVal, hIY, ↓reduceIte])
              (by simp only [weightedMatroidVal, hIX_er, ↓reduceIte])
              (by simp only [weightedMatroidVal, hIY_ins, ↓reduceIte]) ?_
            linarith [h_mod_transfer w hx]
          · let Dset : Finset (Finset (Fin n)) :=
              (insert x Y).powerset.filter (fun D : Finset (Fin n) => ¬ M.Indep (D : Set (Fin n)))
            have hDne : Dset.Nonempty :=
              ⟨insert x Y, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _), hIY_ins⟩⟩
            obtain ⟨C, hCmem, hCmin⟩ := Finset.exists_min_image Dset Finset.card hDne
            have hCsub : C ⊆ insert x Y := Finset.mem_powerset.mp (Finset.mem_filter.mp hCmem).1
            have hCdep : ¬ M.Indep (C : Set (Fin n)) := (Finset.mem_filter.mp hCmem).2
            have hC_er_ind : ∀ z ∈ C, M.Indep ((C.erase z : Finset (Fin n)) : Set (Fin n)) := by
              intro z hz
              by_contra hdep
              have hz_sub : C.erase z ⊆ insert x Y := (Finset.erase_subset z C).trans hCsub
              have hz_mem : C.erase z ∈ Dset :=
                Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hz_sub, hdep⟩
              have hle := hCmin (C.erase z) hz_mem
              have hlt := Finset.card_erase_lt_of_mem hz
              omega
            have hxC : x ∈ C := by
              by_contra hxC
              have hCY : C ⊆ Y := fun z hz => by
                rcases Finset.mem_insert.mp (hCsub hz) with rfl | hzY
                · exact absurd hz hxC
                · exact hzY
              exact hCdep (hIY.subset (Finset.coe_subset.mpr hCY))
            have hSubA : ∀ y ∈ C.erase x,
                M.Indep (((insert x Y).erase y : Finset (Fin n)) : Set (Fin n)) := by
              intro y hy
              have hyC : y ∈ C := (Finset.mem_erase.mp hy).2
              have hy_ins : y ∈ insert x Y := hCsub hyC
              have hC_le : C.card ≤ Y.card + 1 := by
                have := Finset.card_le_card hCsub
                rw [Finset.card_insert_of_notMem hxY] at this
                exact this
              have hCy_le : (C.erase y).card ≤ Y.card := by
                have := Finset.card_erase_add_one hyC; omega
              obtain ⟨K, hCyK, hKsub, hKind, hKcard⟩ :=
                h_rep_aug (Y.card - (C.erase y).card) (C.erase y) Y rfl
                  (hC_er_ind y hyC) hIY hCy_le
              have hyK : y ∉ K := fun hm => by
                have hCK : C ⊆ K := by
                  rw [← Finset.insert_erase hyC]
                  exact Finset.insert_subset hm hCyK
                exact hCdep (hKind.subset (Finset.coe_subset.mpr hCK))
              have hK_ins : K ⊆ insert x Y :=
                hKsub.trans (Finset.union_subset ((Finset.erase_subset y C).trans hCsub) (Finset.subset_insert x Y))
              have hK_er : K ⊆ (insert x Y).erase y :=
                fun z hz => Finset.mem_erase.mpr ⟨fun hzy => hyK (hzy ▸ hz), hK_ins hz⟩
              have hcard_er : ((insert x Y).erase y).card ≤ K.card := by
                have h1 := Finset.card_erase_add_one hy_ins
                have h2 := Finset.card_insert_of_notMem hxY
                omega
              have hKeq : K = (insert x Y).erase y := Finset.eq_of_subset_of_card_le hK_er hcard_er
              exact hKeq ▸ hKind
            have hSubB : ∃ y ∈ C.erase x,
                y ∉ X ∧ M.Indep ((insert y (X.erase x) : Finset (Fin n)) : Set (Fin n)) := by
              have hCx_ind := hC_er_ind x hxC
              by_cases hlt : (X.erase x).card < (C.erase x).card
              · have henc : (X.erase x : Set (Fin n)).encard < (C.erase x : Set (Fin n)).encard := by
                  rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard]
                  exact_mod_cast hlt
                obtain ⟨y, hy, hy_ind⟩ := hIX_er.exists_insert_of_encard_lt hCx_ind henc
                have hyCx : y ∈ C.erase x := hy.1
                have hyXx : y ∉ X.erase x := hy.2
                have hyx : y ≠ x := (Finset.mem_erase.mp hyCx).1
                have hyX : y ∉ X := fun hm => hyXx (Finset.mem_erase.mpr ⟨hyx, hm⟩)
                exact ⟨y, hyCx, hyX, by simpa [Finset.coe_insert] using hy_ind⟩
              · have hCx_le : (C.erase x).card ≤ X.card := by
                  have := Finset.card_erase_add_one hxX; omega
                obtain ⟨K, hCxK, hKsub, hKind, hKcard⟩ :=
                  h_rep_aug (X.card - (C.erase x).card) (C.erase x) X rfl hCx_ind hIX hCx_le
                have hxK : x ∉ K := fun hm => by
                  have hCK : C ⊆ K := by
                    rw [← Finset.insert_erase hxC]
                    exact Finset.insert_subset hm hCxK
                  exact hCdep (hKind.subset (Finset.coe_subset.mpr hCK))
                have hltK : (X.erase x).card < K.card := by
                  have := Finset.card_erase_add_one hxX; omega
                have hencK : (X.erase x : Set (Fin n)).encard < (K : Set (Fin n)).encard := by
                  rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard]
                  exact_mod_cast hltK
                obtain ⟨y, hy, hy_ind⟩ := hIX_er.exists_insert_of_encard_lt hKind hencK
                have hyK : y ∈ K := hy.1
                have hyXx : y ∉ X.erase x := hy.2
                have hyx : y ≠ x := fun h => hxK (h ▸ hyK)
                have hyX : y ∉ X := fun hm => hyXx (Finset.mem_erase.mpr ⟨hyx, hm⟩)
                have hyCx : y ∈ C.erase x := by
                  rcases Finset.mem_union.mp (hKsub hyK) with h1 | h2
                  · exact h1
                  · exact absurd h2 hyX
                exact ⟨y, hyCx, hyX, by simpa [Finset.coe_insert] using hy_ind⟩
            obtain ⟨y, hyCx, hyX, hy_ind1⟩ := hSubB
            have hy_ind2 := hSubA y hyCx
            have hyY : y ∈ Y := by
              rcases Finset.mem_insert.mp (hCsub (Finset.mem_erase.mp hyCx).2) with rfl | hm
              · exact absurd rfl (Finset.mem_erase.mp hyCx).1
              · exact hm
            have hy_sdiff : y ∈ Y \ X := Finset.mem_sdiff.mpr ⟨hyY, hyX⟩
            refine h_build_swap (weightedMatroidVal M w) X Y x y hy_sdiff
              (rX := ∑ g ∈ X, w g) (rY := ∑ g ∈ Y, w g)
              (r1 := ∑ g ∈ insert y (X.erase x), w g) (r2 := ∑ g ∈ (insert x Y).erase y, w g)
              (by simp only [weightedMatroidVal, hIX, ↓reduceIte])
              (by simp only [weightedMatroidVal, hIY, ↓reduceIte])
              (by simp only [weightedMatroidVal, hy_ind1, ↓reduceIte])
              (by simp only [weightedMatroidVal, hy_ind2, ↓reduceIte]) ?_
            linarith [h_mod_swap w hx hy_sdiff]
        · simp [weightedMatroidVal, hIY] at hY
      · simp [weightedMatroidVal, hIX] at hX
    · funext S
      dsimp only [weightedMatroidRankVal, disposalEnvelopeVal, disposalEnvelope]
      congr 1
      congr 1
      refine le_antisymm ?_ ?_
      · refine Finset.sup_le (fun T hT => ?_)
        obtain ⟨hTS, hIT⟩ := Finset.mem_filter.mp hT
        simp at hTS
        obtain ⟨a, haS, rfl⟩ := hTS
        refine le_trans ?_ (Finset.le_sup (Finset.mem_powerset.mpr haS))
        simp [weightedMatroidVal, hIT]
      · refine Finset.sup_le (fun T hTS => ?_)
        by_cases hIT : M.Indep (T : Set (Fin n))
        · have hT_mem : (T : Set (Fin n)) ∈
              ((S.powerset : Finset (Set (Fin n))).filter (fun U : Set (Fin n) => M.Indep U)) := by
            simp [Finset.mem_powerset.mp hTS, hIT]
          refine le_trans ?_ (Finset.le_sup hT_mem)
          simp [weightedMatroidVal, hIT]
        · simp [weightedMatroidVal, hIT]

  have h_concave : ∀ n (h : ℕ → ℝ), h 0 = 0 →
      (∀ r : ℕ, h (r + 2) - h (r + 1) ≤ h (r + 1) - h r) →
      IsGSValuation (fun S : Finset (Fin n) => ((h S.card : ℝ) : WithBot ℝ)) := by
    intro n h h0 hconc
    have h_anti : ∀ a b : ℕ, a ≤ b → h (b + 1) - h b ≤ h (a + 1) - h a := by
      intro a b hab
      induction b with
      | zero =>
        obtain rfl : a = 0 := Nat.eq_zero_of_le_zero hab
        exact le_rfl
      | succ b ih =>
        rcases Nat.of_le_succ hab with hab' | rfl
        · linarith [hconc b, ih hab']
        · exact le_rfl
    let v : ItemValuation n := fun S => ((h S.card : ℝ) : WithBot ℝ)
    refine ⟨by simp [h0], ?_⟩
    intro X Y _ _ x hx
    have hxX : x ∈ X := (Finset.mem_sdiff.mp hx).1
    have hxY : x ∉ Y := (Finset.mem_sdiff.mp hx).2
    have hcardX : (X.erase x).card + 1 = X.card := Finset.card_erase_add_one hxX
    have hcardY : (insert x Y).card = Y.card + 1 := Finset.card_insert_of_notMem hxY
    by_cases hlt : Y.card < X.card
    · have hle : Y.card ≤ (X.erase x).card := by omega
      have hdiff := h_anti Y.card (X.erase x).card hle
      rw [hcardX, ← hcardY] at hdiff
      exact h_build_transfer v X Y x rfl rfl rfl rfl (by linarith)
    · have hne : (Y \ X).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        have hYX : Y ⊆ X := Finset.sdiff_eq_empty_iff_subset.mp hemp
        have hss : Y ⊂ X := Finset.ssubset_iff_subset_ne.mpr ⟨hYX, fun heq => hxY (heq ▸ hxX)⟩
        exact hlt (Finset.card_lt_card hss)
      obtain ⟨y, hy⟩ := hne
      have hyY : y ∈ Y := (Finset.mem_sdiff.mp hy).1
      have hyX : y ∉ X := (Finset.mem_sdiff.mp hy).2
      have hy_er : y ∉ X.erase x := fun hm => hyX (Finset.erase_subset x X hm)
      have hy_ins : y ∈ insert x Y := Finset.mem_insert_of_mem hyY
      have hc1 : (insert y (X.erase x)).card = X.card := by
        rw [Finset.card_insert_of_notMem hy_er, hcardX]
      have hc2 : ((insert x Y).erase y).card = Y.card := by
        have := Finset.card_erase_add_one hy_ins; omega
      refine h_build_swap v X Y x y hy rfl rfl ?_ ?_ le_rfl
      · simp [v, hc1]
      · simp [v, hc2]

  
  have h_part4 : ∀ n (v : ItemValuation n), IsGSValuation v →
      disposalEnvelopeVal v = valConvolution v (zeroVal n) ∧
      IsFiniteValuation (disposalEnvelopeVal v) ∧
      IsNonnegValuation (disposalEnvelopeVal v) ∧
      IsMonotoneValuation (disposalEnvelopeVal v) ∧
      IsGSValuation (disposalEnvelopeVal v) ∧
      IsSubmodularReal (disposalEnvelope v) := by
    intro n v hv
    obtain ⟨heq, hfin, hnn, hmono⟩ := h_env_basic n v hv
    have hgs_env : IsGSValuation (disposalEnvelopeVal v) := by
      rw [heq]
      exact h_conv n v (zeroVal n) hv (h_zero_gs n)
    have hreal_eq : realVal (disposalEnvelopeVal v) = disposalEnvelope v := by
      funext S
      dsimp [realVal, disposalEnvelopeVal]
    have hsub_env : IsSubmodularReal (disposalEnvelope v) := by
      rw [← hreal_eq]
      exact h_submod n (disposalEnvelopeVal v) hgs_env hfin
    exact ⟨heq, hfin, hnn, hmono, hgs_env, hsub_env⟩

  have h_part7 : ∀ n (M : Matroid (Fin n)) (w p : Fin n → ℝ),
      IsGSValuation (weightedMatroidRankVal M w) ∧
      IsGSValuation (addModular (weightedMatroidRankVal M w) (fun g => - p g)) := by
    intro n M w p
    obtain ⟨hm_gs, hm_eq⟩ := h_matroid n M w
    have hr_gs : IsGSValuation (weightedMatroidRankVal M w) := by
      rw [hm_eq]
      exact (h_part4 n (weightedMatroidVal M w) hm_gs).2.2.2.2.1
    exact ⟨hr_gs, h_addMod n (weightedMatroidRankVal M w) (fun g => - p g) hr_gs⟩

  have h_part6 : ∀ n (M : Matroid (Fin n)) (p : Fin n → ℝ),
      IsGSValuation (matroidRankVal M) ∧
      IsGSValuation (addModular (matroidRankVal M) (fun g => - p g)) := by
    intro n M p
    exact h_part7 n M (fun _ => 1) p

  have h_assign_gs : ∀ n k (w : Fin n → Fin k → ℝ), IsGSValuation (assignmentVal w) := by
    intro n k
    induction k with
    | zero =>
      intro w
      rw [h_assign_zero n w]
      exact h_zero_gs n
    | succ k ih =>
      intro w
      obtain ⟨hlast_gs, hstep_eq⟩ := h_assign_step n k w
      rw [hstep_eq]
      exact h_conv n _ _ (ih _) hlast_gs

  have h_part8 : ∀ n k (w : Fin n → Fin k → ℝ) (p : Fin n → ℝ),
      IsGSValuation (assignmentVal w) ∧
      IsGSValuation (addModular (assignmentVal w) (fun g => - p g)) := by
    intro n k w p
    have ha_gs := h_assign_gs n k w
    exact ⟨ha_gs, h_addMod n (assignmentVal w) (fun g => - p g) ha_gs⟩

  have h_part9 : ∀ n (h : ℕ → ℝ) (p : Fin n → ℝ), h 0 = 0 →
      (∀ r : ℕ, h (r + 2) - h (r + 1) ≤ h (r + 1) - h r) →
      let vc : ItemValuation n := fun S => ((h S.card : ℝ) : WithBot ℝ)
      IsGSValuation vc ∧ IsGSValuation (addModular vc (fun g => - p g)) := by
    intro n h p h0 hconc
    dsimp only
    have hvc_gs := h_concave n h h0 hconc
    exact ⟨hvc_gs, h_addMod n _ (fun g => - p g) hvc_gs⟩

  exact ⟨h_part1, h_submod, h_conv, h_part4, h_optWelfare, h_part6, h_part7, h_part8, h_part9⟩


end Internal

/-- **Section 2.1 (`sec:exchange`, `[PaesLeme17]`) — Sums of GS Valuations Need Not Be GS**:
There exist two finite-valued, nonnegative gross substitutes valuations on 3 items whose pointwise
sum violates the gross substitutes exchange axiom. -/
theorem gs_not_closed_under_addition :
    ∃ v₁ v₂ : ItemValuation 3,
      IsFiniteValuation v₁ ∧ IsNonnegValuation v₁ ∧ IsGSValuation v₁ ∧
      IsFiniteValuation v₂ ∧ IsNonnegValuation v₂ ∧ IsGSValuation v₂ ∧
      ¬ IsGSValuation (fun S => v₁ S + v₂ S) :=
  Internal.thm_gs_convolution_and_examples.1

/-- **Supremal Convolution Closure (`[Murota03]`, used in Lemma 4.2 `lem:envelope`)**:
For any two gross substitutes valuations `u` and `w` on `Fin n`, their supremal convolution
`(u □ w)(S) = max_{T ⊆ S} (u(T) + w(S \ T))` (`valConvolution u w`) is a gross substitutes valuation. -/
theorem murota_gs_convolution
    {n : ℕ} (u w : ItemValuation n)
    (hu : IsGSValuation u) (hw : IsGSValuation w) :
    IsGSValuation (valConvolution u w) :=
  Internal.thm_gs_convolution_and_examples.2.2.1 n u w hu hw

/-- **Lemma 4.2 (`lem:envelope`, Disposal envelope)**:
For any gross substitutes valuation `v`, its disposal envelope `v̄(S) = max_{T ⊆ S} v(T)` equals
`v □ 0` (`valConvolution v (zeroVal n)`) and is a finite-valued, nonnegative, nondecreasing gross
substitutes valuation, hence submodular on `2^N`. -/
theorem lem_4_2_envelope
    {n : ℕ} (v : ItemValuation n) (hv : IsGSValuation v) :
    disposalEnvelopeVal v = valConvolution v (zeroVal n) ∧
    IsFiniteValuation (disposalEnvelopeVal v) ∧
    IsNonnegValuation (disposalEnvelopeVal v) ∧
    IsMonotoneValuation (disposalEnvelopeVal v) ∧
    IsGSValuation (disposalEnvelopeVal v) ∧
    IsSubmodularReal (disposalEnvelope v) :=
  Internal.thm_gs_convolution_and_examples.2.2.2.1 n v hv

/-- **Lemma 4.2 (`lem:envelope`, Welfare benchmark invariance)**:
Replacing gross substitutes valuations `v_1, ..., v_m` by their disposal envelopes
`v̄_1, ..., v̄_m` preserves offline optimal welfare `OPT`. -/
theorem lem_4_2_envelope_optWelfare
    {n m : ℕ} (v : Fin m → ItemValuation n) (hv : ∀ i, IsGSValuation (v i)) :
    optWelfare (fun i => disposalEnvelopeVal (v i)) = optWelfare v :=
  Internal.thm_gs_convolution_and_examples.2.2.2.2.1 n m v hv

/-- **Example 2.4 (`ex:gs`) — Matroid Rank Valuations & Modular Price Shifts**:
For every matroid `M` on `Fin n` and price vector `p`, `matroidRankVal M` and
`S ↦ r_M(S) - ∑_{g ∈ S} p_g` are gross substitutes valuations. -/
theorem ex_2_4_matroid_rank
    {n : ℕ} (M : Matroid (Fin n)) (p : Fin n → ℝ) :
    IsGSValuation (matroidRankVal M) ∧
    IsGSValuation (addModular (matroidRankVal M) (fun g => - p g)) :=
  Internal.thm_gs_convolution_and_examples.2.2.2.2.2.1 n M p

/-- **Example 2.4 (`ex:gs`) — Weighted Matroid Rank Valuations & Modular Price Shifts**:
For every matroid `M` on `Fin n`, item weights `w`, and price vector `p`,
`weightedMatroidRankVal M w` and its price shift by `-p` are gross substitutes valuations. -/
theorem ex_2_4_weighted_matroid_rank
    {n : ℕ} (M : Matroid (Fin n)) (w p : Fin n → ℝ) :
    IsGSValuation (weightedMatroidRankVal M w) ∧
    IsGSValuation (addModular (weightedMatroidRankVal M w) (fun g => - p g)) :=
  Internal.thm_gs_convolution_and_examples.2.2.2.2.2.2.1 n M w p

/-- **Example 2.4 (`ex:gs`, `[LLN06, Murota03]`) — Bipartite Assignment Valuations & Price Shifts**:
For every item-slot weight matrix `w : Fin n → Fin k → ℝ` and price vector `p`,
`assignmentVal w` and its price shift by `-p` are gross substitutes valuations. -/
theorem ex_2_4_assignment
    {n k : ℕ} (w : Fin n → Fin k → ℝ) (p : Fin n → ℝ) :
    IsGSValuation (assignmentVal w) ∧
    IsGSValuation (addModular (assignmentVal w) (fun g => - p g)) :=
  Internal.thm_gs_convolution_and_examples.2.2.2.2.2.2.2.1 n k w p

/-- **Example 2.4 (`ex:gs`) — Discretely Concave Cardinality Valuations & Price Shifts**:
For any `h : ℕ → ℝ` with `h(0) = 0` and nonincreasing marginal increments, `S ↦ h(|S|)` and
`S ↦ h(|S|) - ∑_{g ∈ S} p_g` are gross substitutes valuations. -/
theorem ex_2_4_concave_cardinality_with_prices
    {n : ℕ} (h : ℕ → ℝ) (p : Fin n → ℝ) (h0 : h 0 = 0)
    (hconc : ∀ r : ℕ, h (r + 2) - h (r + 1) ≤ h (r + 1) - h r) :
    let vc : ItemValuation n := fun S => ((h S.card : ℝ) : WithBot ℝ)
    IsGSValuation vc ∧ IsGSValuation (addModular vc (fun g => - p g)) :=
  Internal.thm_gs_convolution_and_examples.2.2.2.2.2.2.2.2 n h p h0 hconc

end

end GrossSubstitutesWelfare
