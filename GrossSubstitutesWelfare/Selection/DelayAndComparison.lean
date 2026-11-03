import GrossSubstitutesWelfare.Defs
import GrossSubstitutesWelfare.Preliminaries.ExchangeAndDemand
import GrossSubstitutesWelfare.Selection.ClampAndPayment

set_option maxHeartbeats 4000000

/-!
# Appendix B.1 (Part 2): Moving One Timestamp (Two-Time Induction) & Comparison Inequality

This file formalizes Appendix B.1 Theorem B.5 (`thm:delay`) and Proposition B.1 (`prop:comparison`)
of *Gross Substitutes Welfare in Random Order*:
- `thm_B_5_delay_choice_rule` / `thm_B_5_delay` (**Theorem B.5**, `thm:delay`): Monotonicity of
  `τ̃ ↦ τ̃ μ̃(τ̃)` on `[1/e, t₀]` for all `1/e ≤ t₀ ≤ t ≤ 1` in the two-time generalized thought
  experiment (valid for any persistent, single-displacement choice rule `C`, and in particular
  `D_v`).
- `prop_B_1_comparison` (**Proposition B.1**, `prop:comparison`): Contraction comparison inequality
  `μ^v_{S, t}(A) ≥ (1 / (e t)) μ^{v / x}_{S, t}(A)`.
- `survivalAcceptProb_valid` (**Section 3.1 `eq:accept` & Appendix B.2 `eq:accept-mass`**):
  Acceptance probability bounds `0 ≤ α_x(A, S, t) ≤ 1` and exact transition mass identity
  `μ^v_{S, t}(A) α_x(A, S, t) = (1 / (e t)) μ^{v / x}_{S, t}(A)`.
-/

namespace GrossSubstitutesWelfare

open Classical MeasureTheory

noncomputable section

namespace DelayInternal

theorem thm_selection_two_time_delay_and_comparison :
    -- (1a) Theorem B.5 for any choice rule with persistence and single displacement
    (∀ (n : ℕ) (C : Finset (Fin n) → Finset (Fin n)) (t₀ t : ℝ)
        (S B : Finset (Fin n)) (β : Fin n → ℝ) (x : Fin n) (A : Finset (Fin n)),
      IsChoiceRule C → HasPersistence C → HasSingleDisplacement C →
      invE ≤ t₀ → t₀ ≤ t → t ≤ 1 →
      Disjoint S B → (∀ b ∈ B, invE ≤ β b ∧ β b ≤ t) → x ∉ S ∪ B → A ⊆ S →
        MonotoneOn (fun τ_tilde => τ_tilde * genMovingProb2 C t₀ t S B β x A τ_tilde)
          (Set.Icc invE t₀) ∧
        ∀ τ_tilde ∈ Set.Icc invE t₀,
          (1 / (Real.exp 1 * τ_tilde)) * genMovingProb2 C t₀ t S B β x A invE ≤
            genMovingProb2 C t₀ t S B β x A τ_tilde) ∧
    -- (1b) Theorem B.5 specialized directly to GS valuations v (D_v)
    (∀ (n : ℕ) (v : ItemValuation n) (t₀ t : ℝ)
        (S B : Finset (Fin n)) (β : Fin n → ℝ) (x : Fin n) (A : Finset (Fin n)),
      IsGSValuation v → invE ≤ t₀ → t₀ ≤ t → t ≤ 1 →
      Disjoint S B → (∀ b ∈ B, invE ≤ β b ∧ β b ≤ t) → x ∉ S ∪ B → A ⊆ S →
        MonotoneOn
          (fun τ_tilde => τ_tilde * genMovingProb2 (canonicalDemand v) t₀ t S B β x A τ_tilde)
          (Set.Icc invE t₀) ∧
        ∀ τ_tilde ∈ Set.Icc invE t₀,
          (1 / (Real.exp 1 * τ_tilde)) *
              genMovingProb2 (canonicalDemand v) t₀ t S B β x A invE ≤
            genMovingProb2 (canonicalDemand v) t₀ t S B β x A τ_tilde) ∧
    -- (2) Proposition B.1: Comparison inequality
    (∀ (n : ℕ) (v : ItemValuation n) (S : Finset (Fin n)) (x : Fin n) (t : ℝ)
        (A : Finset (Fin n)),
      IsGSValuation v → x ∉ S → x ∈ canonicalDemand v (insert x S) →
      invE ≤ t → t ≤ 1 →
        (1 / (Real.exp 1 * t)) * survivalLaw (contractVal v x) S t A ≤
          survivalLaw v S t A) ∧
    -- (3) Acceptance probability validity & exact transition mass identity
    (∀ (n : ℕ) (v : ItemValuation n) (S : Finset (Fin n)) (x : Fin n) (t : ℝ)
        (A : Finset (Fin n)),
      IsGSValuation v → x ∉ S → t ≤ 1 →
        (0 ≤ survivalAcceptProb v x A S t ∧ survivalAcceptProb v x A S t ≤ 1) ∧
        (invE < t → x ∈ canonicalDemand v (insert x S) →
          survivalLaw v S t A * survivalAcceptProb v x A S t =
            (1 / (Real.exp 1 * t)) * survivalLaw (contractVal v x) S t A)) :=
by
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

  have h_part4 : ∀ n (v : ItemValuation n) (x : Fin n),
      IsGSValuation v → v {x} ≠ ⊥ → IsGSValuation (contractVal v x) := by
    intro n v x hv hvx_ne
    cases hvx : v {x} with
    | bot => exact absurd hvx hvx_ne
    | coe vx =>
      have hcval : ∀ T : Finset (Fin n), x ∉ T →
          contractVal v x T = v (insert x T) + ((-vx : ℝ) : WithBot ℝ) := by
        intro T hxT; simp [contractVal, hxT, hvx]
      refine ⟨?_, ?_⟩
      · have h0 := hcval ∅ (Finset.notMem_empty x)
        have hins0 : (insert x ∅ : Finset (Fin n)) = {x} := rfl
        rw [hins0] at h0
        rw [h0, hvx, ← WithBot.coe_add]
        simp
      · intro X Y hX hY z hz
        by_cases hxX : x ∈ X
        · simp [contractVal, hxX] at hX
        · by_cases hxY : x ∈ Y
          · simp [contractVal, hxY] at hY
          · rw [hcval X hxX] at hX
            rw [hcval Y hxY] at hY
            cases hvX : v (insert x X) with
            | bot => simp [hvX] at hX
            | coe rX =>
              cases hvY : v (insert x Y) with
              | bot => simp [hvY] at hY
              | coe rY =>
                have hzX : z ∈ X := (Finset.mem_sdiff.mp hz).1
                have hzY : z ∉ Y := (Finset.mem_sdiff.mp hz).2
                have hzx : z ≠ x := fun h => hxX (h ▸ hzX)
                have hz' : z ∈ (insert x X) \ (insert x Y) := by
                  simp [Finset.mem_sdiff, hzX, hzY, hzx]
                rcases h_gs_cases hv hvX hvY hz' with
                  ⟨r1, r2, h1, h2, hle⟩ | ⟨y, hy, r1, r2, h1, h2, hle⟩
                · have hx1 : x ∉ X.erase z := fun hm => hxX (Finset.erase_subset z X hm)
                  have hx2 : x ∉ insert z Y := by simp [hxY, Ne.symm hzx]
                  have he1 : (insert x X).erase z = insert x (X.erase z) :=
                    Finset.erase_insert_of_ne (Ne.symm hzx)
                  have he2 : insert z (insert x Y) = insert x (insert z Y) :=
                    Finset.insert_comm z x Y
                  rw [he1] at h1; rw [he2] at h2
                  refine h_build_transfer (contractVal v x) X Y z
                    (rX := rX + -vx) (rY := rY + -vx) (r1 := r1 + -vx) (r2 := r2 + -vx)
                    ?_ ?_ ?_ ?_ (by linarith)
                  · rw [hcval X hxX, hvX, ← WithBot.coe_add]
                  · rw [hcval Y hxY, hvY, ← WithBot.coe_add]
                  · rw [hcval _ hx1, h1, ← WithBot.coe_add]
                  · rw [hcval _ hx2, h2, ← WithBot.coe_add]
                · have hyx : y ≠ x := fun h => (Finset.mem_sdiff.mp hy).2 (by simp [h])
                  have hyY : y ∈ Y := by
                    rcases Finset.mem_insert.mp (Finset.mem_sdiff.mp hy).1 with rfl | hm
                    · exact absurd rfl hyx
                    · exact hm
                  have hyX : y ∉ X := fun hm =>
                    (Finset.mem_sdiff.mp hy).2 (Finset.mem_insert_of_mem hm)
                  have hy_orig : y ∈ Y \ X := Finset.mem_sdiff.mpr ⟨hyY, hyX⟩
                  have hx1 : x ∉ insert y (X.erase z) := by
                    simp [Ne.symm hyx, show x ∉ X.erase z from fun hm => hxX (Finset.erase_subset z X hm)]
                  have hx2 : x ∉ (insert z Y).erase y := fun hm => by
                    have hm' := Finset.erase_subset y (insert z Y) hm
                    rcases Finset.mem_insert.mp hm' with rfl | hmY
                    · exact hzx rfl
                    · exact hxY hmY
                  have he1 : insert y ((insert x X).erase z) = insert x (insert y (X.erase z)) := by
                    rw [Finset.erase_insert_of_ne (Ne.symm hzx), Finset.insert_comm]
                  have he2 : (insert z (insert x Y)).erase y = insert x ((insert z Y).erase y) := by
                    rw [Finset.insert_comm z x Y, Finset.erase_insert_of_ne (Ne.symm hyx)]
                  rw [he1] at h1; rw [he2] at h2
                  refine h_build_swap (contractVal v x) X Y z y hy_orig
                    (rX := rX + -vx) (rY := rY + -vx) (r1 := r1 + -vx) (r2 := r2 + -vx)
                    ?_ ?_ ?_ ?_ (by linarith)
                  · rw [hcval X hxX, hvX, ← WithBot.coe_add]
                  · rw [hcval Y hxY, hvY, ← WithBot.coe_add]
                  · rw [hcval _ hx1, h1, ← WithBot.coe_add]
                  · rw [hcval _ hx2, h2, ← WithBot.coe_add]

  have h_hered : ∀ {n : ℕ} {v : ItemValuation n}, IsGSValuation v →
      ∀ {X Y : Finset (Fin n)}, v X ≠ ⊥ → Y ⊆ X → v Y ≠ ⊥ := by
    intro n v hv
    have h_del : ∀ {A : Finset (Fin n)} {x : Fin n}, v A ≠ ⊥ → x ∈ A → v (A.erase x) ≠ ⊥ := by
      intro A x hA hx
      cases hvA : v A with
      | bot => exact absurd hvA hA
      | coe rA =>
        have hx' : x ∈ A \ ∅ := by simp [hx]
        rcases h_gs_cases hv hvA hv.1 hx' with ⟨r1, _, h1, _, _⟩ | ⟨y, hy, _⟩
        · simp [h1]
        · simp at hy
    have h_ind : ∀ k : ℕ, ∀ X Y : Finset (Fin n),
        (X \ Y).card = k → v X ≠ ⊥ → Y ⊆ X → v Y ≠ ⊥ := by
      intro k
      induction k with
      | zero =>
        intro X Y hk hX hYX
        have hemp : X \ Y = ∅ := Finset.card_eq_zero.mp hk
        have hXY : X ⊆ Y := Finset.sdiff_eq_empty_iff_subset.mp hemp
        obtain rfl : X = Y := Finset.Subset.antisymm hXY hYX
        exact hX
      | succ k ih =>
        intro X Y hk hX hYX
        have hne : (X \ Y).Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨x, hx⟩ := hne
        have hxX : x ∈ X := (Finset.mem_sdiff.mp hx).1
        have hxY : x ∉ Y := (Finset.mem_sdiff.mp hx).2
        have hYX' : Y ⊆ X.erase x := fun z hz =>
          Finset.mem_erase.mpr ⟨fun hzx => hxY (hzx ▸ hz), hYX hz⟩
        have hsdiff : (X.erase x) \ Y = (X \ Y).erase x := by
          ext z; simp [Finset.mem_sdiff, Finset.mem_erase]; tauto
        have hk' : ((X.erase x) \ Y).card = k := by
          rw [hsdiff]
          have := Finset.card_erase_add_one hx
          omega
        exact ih (X.erase x) Y hk' (h_del hX hxX) hYX'
    intro X Y hX hYX
    exact h_ind (X \ Y).card X Y rfl hX hYX

  have h_geom : ∀ a b : ℕ, a ≤ b →
      ∑ k ∈ Finset.Ico a b, (1 / 2 : ℝ) ^ (k + 1) = (1 / 2 : ℝ) ^ a - (1 / 2 : ℝ) ^ b := by
    intro a b hab
    induction b with
    | zero =>
      obtain rfl : a = 0 := Nat.eq_zero_of_le_zero hab
      simp
    | succ b ih =>
      rcases Nat.of_le_succ hab with hab' | rfl
      · rw [Finset.sum_Ico_succ_top hab', ih hab']
        ring
      · simp

  have h_tail_lt : ∀ {n : ℕ} (S : Finset (Fin n)) (m : ℕ),
      m ≤ n → (∀ g ∈ S, m ≤ g.1) →
        ∑ g ∈ S, (1 / 2 : ℝ) ^ (g.1 + 1) < (1 / 2 : ℝ) ^ m := by
    intro n S m hmn hm
    have himg : ∑ g ∈ S, (1 / 2 : ℝ) ^ (g.1 + 1) =
        ∑ k ∈ S.image Fin.val, (1 / 2 : ℝ) ^ (k + 1) :=
      (Finset.sum_image (f := fun k => (1 / 2 : ℝ) ^ (k + 1))
        (fun a _ b _ h => Fin.ext h)).symm
    have hsub : S.image Fin.val ⊆ Finset.Ico m n := by
      intro k hk
      obtain ⟨g, hgS, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_Ico.mpr ⟨hm g hgS, g.2⟩
    have hle : ∑ k ∈ S.image Fin.val, (1 / 2 : ℝ) ^ (k + 1) ≤
        ∑ k ∈ Finset.Ico m n, (1 / 2 : ℝ) ^ (k + 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
    rw [h_geom m n hmn] at hle
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
    linarith

  have h_psi_inj : ∀ n : ℕ, Function.Injective (@psiWeight n) := by
    intro n X Y hXY
    have hsplit : ∀ A : Finset (Fin n),
        psiWeight A = (A.card : ℝ) + ∑ g ∈ A, (1 / 2 : ℝ) ^ (g.1 + 1) := by
      intro A
      simp [psiWeight, Finset.sum_add_distrib]
    have hX0 : 0 ≤ ∑ g ∈ X, (1 / 2 : ℝ) ^ (g.1 + 1) :=
      Finset.sum_nonneg (fun g _ => by positivity)
    have hY0 : 0 ≤ ∑ g ∈ Y, (1 / 2 : ℝ) ^ (g.1 + 1) :=
      Finset.sum_nonneg (fun g _ => by positivity)
    have hX1 : ∑ g ∈ X, (1 / 2 : ℝ) ^ (g.1 + 1) < 1 := by
      simpa using h_tail_lt X 0 (Nat.zero_le n) (fun g _ => Nat.zero_le g.1)
    have hY1 : ∑ g ∈ Y, (1 / 2 : ℝ) ^ (g.1 + 1) < 1 := by
      simpa using h_tail_lt Y 0 (Nat.zero_le n) (fun g _ => Nat.zero_le g.1)
    rw [hsplit X, hsplit Y] at hXY
    have hcard_eq : X.card = Y.card := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : (X.card : ℝ) + 1 ≤ (Y.card : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
        linarith
      · have hle : (Y.card : ℝ) + 1 ≤ (X.card : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
        linarith
    have hδ : ∑ g ∈ X, (1 / 2 : ℝ) ^ (g.1 + 1) = ∑ g ∈ Y, (1 / 2 : ℝ) ^ (g.1 + 1) := by
      rw [hcard_eq] at hXY; linarith
    have h_no_min : ∀ (A B : Finset (Fin n)),
        (∑ g ∈ A, (1 / 2 : ℝ) ^ (g.1 + 1)) = (∑ g ∈ B, (1 / 2 : ℝ) ^ (g.1 + 1)) →
        ∀ m₀ ∈ A \ B, (∀ g ∈ B \ A, m₀ < g) → False := by
      intro A B hAB m₀ hmA hmB
      have hA_un : (∑ g ∈ A \ B, (1 / 2 : ℝ) ^ (g.1 + 1)) +
          (∑ g ∈ A ∩ B, (1 / 2 : ℝ) ^ (g.1 + 1)) = ∑ g ∈ A, (1 / 2 : ℝ) ^ (g.1 + 1) := by
        rw [← Finset.sum_union (Finset.disjoint_sdiff_inter A B), Finset.sdiff_union_inter]
      have hB_un : (∑ g ∈ B \ A, (1 / 2 : ℝ) ^ (g.1 + 1)) +
          (∑ g ∈ A ∩ B, (1 / 2 : ℝ) ^ (g.1 + 1)) = ∑ g ∈ B, (1 / 2 : ℝ) ^ (g.1 + 1) := by
        rw [Finset.inter_comm A B, ← Finset.sum_union (Finset.disjoint_sdiff_inter B A),
          Finset.sdiff_union_inter]
      have hsdiff_eq : (∑ g ∈ A \ B, (1 / 2 : ℝ) ^ (g.1 + 1)) =
          (∑ g ∈ B \ A, (1 / 2 : ℝ) ^ (g.1 + 1)) := by linarith
      have hlow : (1 / 2 : ℝ) ^ (m₀.1 + 1) ≤ ∑ g ∈ A \ B, (1 / 2 : ℝ) ^ (g.1 + 1) :=
        Finset.single_le_sum (f := fun g : Fin n => (1 / 2 : ℝ) ^ (g.1 + 1))
          (fun g _ => by positivity) hmA
      have hup : ∑ g ∈ B \ A, (1 / 2 : ℝ) ^ (g.1 + 1) < (1 / 2 : ℝ) ^ (m₀.1 + 1) :=
        h_tail_lt (B \ A) (m₀.1 + 1) (Nat.succ_le_of_lt m₀.2)
          (fun g hg => Nat.succ_le_of_lt (Fin.lt_def.mp (hmB g hg)))
      linarith
    by_contra hne
    let D := (X \ Y) ∪ (Y \ X)
    have hDne : D.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      have h1 : X \ Y = ∅ := Finset.union_eq_empty.mp hemp |>.1
      have h2 : Y \ X = ∅ := Finset.union_eq_empty.mp hemp |>.2
      exact hne (Finset.Subset.antisymm
        (Finset.sdiff_eq_empty_iff_subset.mp h1)
        (Finset.sdiff_eq_empty_iff_subset.mp h2))
    let m₀ := D.min' hDne
    rcases Finset.mem_union.mp (Finset.min'_mem D hDne) with hmXY | hmYX
    · refine h_no_min X Y hδ m₀ hmXY (fun g hg => ?_)
      have hle : m₀ ≤ g := Finset.min'_le D g (Finset.mem_union_right _ hg)
      have hne_g : m₀ ≠ g := by
        intro h
        have hgY : g ∈ Y := (Finset.mem_sdiff.mp hg).1
        rw [← h] at hgY
        exact (Finset.mem_sdiff.mp hmXY).2 hgY
      exact lt_of_le_of_ne hle hne_g
    · refine h_no_min Y X hδ.symm m₀ hmYX (fun g hg => ?_)
      have hle : m₀ ≤ g := Finset.min'_le D g (Finset.mem_union_left _ hg)
      have hne_g : m₀ ≠ g := by
        intro h
        have hgX : g ∈ X := (Finset.mem_sdiff.mp hg).1
        rw [← h] at hgX
        exact (Finset.mem_sdiff.mp hmYX).2 hgX
      exact lt_of_le_of_ne hle hne_g

  have h_part9 : ∀ n (v : ItemValuation n) (T : Finset (Fin n)),
      v ∅ = ((0 : ℝ) : WithBot ℝ) →
        canonicalDemand v T ⊆ T ∧
        v (canonicalDemand v T) ≠ ⊥ ∧
        (∀ Y ⊆ T, demandKeyLe v Y (canonicalDemand v T)) ∧
        (∀ X ⊆ T, (∀ Y ⊆ T, demandKeyLe v Y X) → X = canonicalDemand v T) := by
    intro n v T hv0
    have h_refl : ∀ A : Finset (Fin n), demandKeyLe v A A :=
      fun A => Or.inr ⟨rfl, le_rfl⟩
    have h_trans : ∀ {A B C : Finset (Fin n)},
        demandKeyLe v A B → demandKeyLe v B C → demandKeyLe v A C := by
      intro A B C hAB hBC
      rcases hAB with hlt1 | ⟨heq1, hle1⟩
      · rcases hBC with hlt2 | ⟨heq2, _⟩
        · exact Or.inl (lt_trans hlt1 hlt2)
        · exact Or.inl (heq2 ▸ hlt1)
      · rcases hBC with hlt2 | ⟨heq2, hle2⟩
        · exact Or.inl (heq1.symm ▸ hlt2)
        · exact Or.inr ⟨heq1.trans heq2, le_trans hle1 hle2⟩
    have h_total : ∀ A B : Finset (Fin n), demandKeyLe v A B ∨ demandKeyLe v B A := by
      intro A B
      rcases lt_trichotomy (v A) (v B) with hlt | heq | hgt
      · exact Or.inl (Or.inl hlt)
      · rcases le_total (psiWeight A) (psiWeight B) with hle | hge
        · exact Or.inl (Or.inr ⟨heq, hle⟩)
        · exact Or.inr (Or.inr ⟨heq.symm, hge⟩)
      · exact Or.inr (Or.inl hgt)
    have h_antisymm : ∀ {A B : Finset (Fin n)},
        demandKeyLe v A B → demandKeyLe v B A → A = B := by
      intro A B hAB hBA
      rcases hAB with hlt1 | ⟨heq1, hle1⟩
      · rcases hBA with hlt2 | ⟨heq2, _⟩
        · exact absurd (lt_trans hlt1 hlt2) (lt_irrefl _)
        · exact absurd (heq2 ▸ hlt1) (lt_irrefl _)
      · rcases hBA with hlt2 | ⟨_, hle2⟩
        · exact absurd (heq1 ▸ hlt2) (lt_irrefl _)
        · exact h_psi_inj n (le_antisymm hle1 hle2)
    have h_fin_max : ∀ F : Finset (Finset (Fin n)), F.Nonempty →
        ∃ X ∈ F, ∀ Y ∈ F, demandKeyLe v Y X := by
      intro F
      induction F using Finset.induction_on with
      | empty => intro hne; simp at hne
      | @insert A F' hAF' ih =>
        intro _
        by_cases hF' : F'.Nonempty
        · obtain ⟨M, hMF', hMmax⟩ := ih hF'
          rcases h_total A M with hAM | hMA
          · refine ⟨M, Finset.mem_insert_of_mem hMF', fun Y hY => ?_⟩
            rcases Finset.mem_insert.mp hY with rfl | hYF'
            · exact hAM
            · exact hMmax Y hYF'
          · refine ⟨A, Finset.mem_insert_self A F', fun Y hY => ?_⟩
            rcases Finset.mem_insert.mp hY with rfl | hYF'
            · exact h_refl _
            · exact h_trans (hMmax Y hYF') hMA
        · rw [Finset.not_nonempty_iff_eq_empty] at hF'
          subst hF'
          refine ⟨A, Finset.mem_singleton_self A, fun Y hY => ?_⟩
          rw [Finset.mem_singleton.mp hY]
          exact h_refl A
    have hpow_ne : T.powerset.Nonempty := ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset T)⟩
    have hex : ∃ X ∈ T.powerset, ∀ Y ∈ T.powerset, demandKeyLe v Y X := h_fin_max T.powerset hpow_ne
    have hcd_eq : canonicalDemand v T = Classical.choose hex := dif_pos hex
    have hspec := Classical.choose_spec hex
    rw [← hcd_eq] at hspec
    have hsub : canonicalDemand v T ⊆ T := Finset.mem_powerset.mp hspec.1
    have hdom : ∀ Y ⊆ T, demandKeyLe v Y (canonicalDemand v T) :=
      fun Y hY => hspec.2 Y (Finset.mem_powerset.mpr hY)
    have hne_bot : v (canonicalDemand v T) ≠ ⊥ := by
      intro hbot
      have h0 := hdom ∅ (Finset.empty_subset T)
      dsimp only [demandKeyLe] at h0
      rw [hv0, hbot] at h0
      rcases h0 with hlt | ⟨heq, _⟩
      · exact absurd hlt (by simp)
      · exact absurd heq (by simp)
    have huniq : ∀ X ⊆ T, (∀ Y ⊆ T, demandKeyLe v Y X) → X = canonicalDemand v T := by
      intro X hXT hXdom
      exact h_antisymm (hdom X hXT) (hXdom (canonicalDemand v T) hsub)
    exact ⟨hsub, hne_bot, hdom, huniq⟩

  have h_part10 : ∀ n (v : ItemValuation n) (T : Finset (Fin n)) (x : Fin n),
      IsGSValuation v → x ∉ T →
        let X := canonicalDemand v T
        canonicalDemand v (insert x T) = X ∨
        canonicalDemand v (insert x T) = insert x X ∨
        ∃ f ∈ X, canonicalDemand v (insert x T) = insert x (X.erase f) := by
    intro n v T x hv hxT
    dsimp only
    let X := canonicalDemand v T
    let Y := canonicalDemand v (insert x T)
    obtain ⟨hXT, hvX_ne, hXdom, hXuniq⟩ := h_part9 n v T hv.1
    obtain ⟨hYT, hvY_ne, hYdom, _⟩ := h_part9 n v (insert x T) hv.1
    change Y = X ∨ Y = insert x X ∨ ∃ f ∈ X, Y = insert x (X.erase f)
    by_cases hxY : x ∈ Y
    · have hxX : x ∉ X := fun hm => hxT (hXT hm)
      cases hvY : v Y with
      | bot => exact absurd hvY hvY_ne
      | coe rY =>
        cases hvX : v X with
        | bot => exact absurd hvX hvX_ne
        | coe rX =>
          have h_opt_pair : ∀ (P Q : Finset (Fin n)) {rP rQ : ℝ},
              P ⊆ T → Q ⊆ insert x T →
              v P = ((rP : ℝ) : WithBot ℝ) → v Q = ((rQ : ℝ) : WithBot ℝ) →
              rY + rX ≤ rP + rQ →
              psiWeight P + psiWeight Q = psiWeight Y + psiWeight X →
              Y = Q := by
            intro P Q rP rQ hPT hQT hvP hvQ hr_sum hpsi_sum
            have hdP : demandKeyLe v P X := hXdom P hPT
            have hdQ : demandKeyLe v Q Y := hYdom Q hQT
            dsimp only [demandKeyLe] at hdP hdQ
            rw [hvP, hvX] at hdP
            rw [hvQ, hvY] at hdQ
            have hrPX : rP ≤ rX := by
              rcases hdP with hlt | ⟨heq, _⟩
              · exact le_of_lt (WithBot.coe_lt_coe.mp hlt)
              · exact le_of_eq (WithBot.coe_inj.mp heq)
            have hrQY : rQ ≤ rY := by
              rcases hdQ with hlt | ⟨heq, _⟩
              · exact le_of_lt (WithBot.coe_lt_coe.mp hlt)
              · exact le_of_eq (WithBot.coe_inj.mp heq)
            have hpsiP : psiWeight P ≤ psiWeight X := by
              rcases hdP with hlt | ⟨_, hle⟩
              · have := WithBot.coe_lt_coe.mp hlt; linarith
              · exact hle
            have hpsiQ : psiWeight Q ≤ psiWeight Y := by
              rcases hdQ with hlt | ⟨_, hle⟩
              · have := WithBot.coe_lt_coe.mp hlt; linarith
              · exact hle
            exact h_psi_inj n (by linarith)
          have hxYX : x ∈ Y \ X := Finset.mem_sdiff.mpr ⟨hxY, hxX⟩
          let wpsi : Fin n → ℝ := fun g => 1 + (1 / 2 : ℝ) ^ (g.1 + 1)
          rcases h_gs_cases hv hvY hvX hxYX with
            ⟨r1, r2, h1, h2, hle⟩ | ⟨f, hf, r1, r2, h1, h2, hle⟩
          · have hPT : Y.erase x ⊆ T := fun z hz => by
              rcases Finset.mem_insert.mp (hYT (Finset.erase_subset x Y hz)) with rfl | hzT
              · exact absurd rfl (Finset.mem_erase.mp hz).1
              · exact hzT
            have hQT : insert x X ⊆ insert x T := Finset.insert_subset_insert x hXT
            have hpsi_sum : psiWeight (Y.erase x) + psiWeight (insert x X) =
                psiWeight Y + psiWeight X := by
              have hp1 := Finset.sum_erase_add Y wpsi hxY
              have hp2 := Finset.sum_insert hxX (f := wpsi)
              dsimp only [psiWeight]
              linarith
            exact Or.inr (Or.inl (h_opt_pair (Y.erase x) (insert x X) hPT hQT h1 h2 hle hpsi_sum))
          · have hfX : f ∈ X := (Finset.mem_sdiff.mp hf).1
            have hfY : f ∉ Y := (Finset.mem_sdiff.mp hf).2
            have hfx : f ≠ x := fun h => hfY (h ▸ hxY)
            have hPT : insert f (Y.erase x) ⊆ T := by
              refine Finset.insert_subset (hXT hfX) (fun z hz => ?_)
              rcases Finset.mem_insert.mp (hYT (Finset.erase_subset x Y hz)) with rfl | hzT
              · exact absurd rfl (Finset.mem_erase.mp hz).1
              · exact hzT
            have hQeq : (insert x X).erase f = insert x (X.erase f) :=
              Finset.erase_insert_of_ne (Ne.symm hfx)
            rw [hQeq] at h2
            have hQT : insert x (X.erase f) ⊆ insert x T :=
              Finset.insert_subset_insert x ((Finset.erase_subset f X).trans hXT)
            have hf_er : f ∉ Y.erase x := fun hm => hfY (Finset.erase_subset x Y hm)
            have hx_er : x ∉ X.erase f := fun hm => hxX (Finset.erase_subset f X hm)
            have hpsi_sum : psiWeight (insert f (Y.erase x)) + psiWeight (insert x (X.erase f)) =
                psiWeight Y + psiWeight X := by
              have hp1 := Finset.sum_erase_add Y wpsi hxY
              have hp2 := Finset.sum_insert hf_er (f := wpsi)
              have hp3 := Finset.sum_erase_add X wpsi hfX
              have hp4 := Finset.sum_insert hx_er (f := wpsi)
              dsimp only [psiWeight]
              linarith
            exact Or.inr (Or.inr ⟨f, hfX,
              h_opt_pair (insert f (Y.erase x)) (insert x (X.erase f)) hPT hQT h1 h2 hle hpsi_sum⟩)
    · have hYT' : Y ⊆ T := fun z hz => by
        rcases Finset.mem_insert.mp (hYT hz) with rfl | hzT
        · exact absurd hz hxY
        · exact hzT
      exact Or.inl (hXuniq Y hYT' (fun Z hZT => hYdom Z (hZT.trans (Finset.subset_insert x T))))

  have h_part11 : ∀ n (v : ItemValuation n), IsGSValuation v →
      IsChoiceRule (canonicalDemand v) ∧
      HasPersistence (canonicalDemand v) ∧
      HasSingleDisplacement (canonicalDemand v) := by
    intro n v hv
    have hcr : IsChoiceRule (canonicalDemand v) :=
      fun T => (h_part9 n v T hv.1).1
    have hsd : HasSingleDisplacement (canonicalDemand v) := by
      intro T x hxT
      rcases h_part10 n v T x hv hxT with heq | heq | ⟨f, _, heq⟩
      · simp [heq]
      · have hsub : canonicalDemand v T \ insert x (canonicalDemand v T) = ∅ :=
          Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_insert x _)
        simp [heq, hsub]
      · rw [heq]
        have hsub : canonicalDemand v T \ insert x ((canonicalDemand v T).erase f) ⊆ {f} := by
          intro z hz
          have hz1 : z ∈ canonicalDemand v T := (Finset.mem_sdiff.mp hz).1
          have hz2 : z ∉ insert x ((canonicalDemand v T).erase f) := (Finset.mem_sdiff.mp hz).2
          rw [Finset.mem_singleton]
          by_contra hzf
          exact hz2 (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hzf, hz1⟩))
        exact (Finset.card_le_card hsub).trans (by simp)
    have hpers_ind : ∀ (k : ℕ) (T U : Finset (Fin n)),
        (U \ T).card = k → T ⊆ U → canonicalDemand v U ∩ T ⊆ canonicalDemand v T := by
      intro k
      induction k with
      | zero =>
        intro T U hk hTU
        have hUT : U ⊆ T := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hk)
        obtain rfl : T = U := Finset.Subset.antisymm hTU hUT
        exact Finset.inter_subset_left
      | succ k ih =>
        intro T U hk hTU
        obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < (U \ T).card)
        have hxU : x ∈ U := (Finset.mem_sdiff.mp hx).1
        have hxT : x ∉ T := (Finset.mem_sdiff.mp hx).2
        let U' := U.erase x
        have hxU' : x ∉ U' := Finset.notMem_erase x U
        have hUeq : insert x U' = U := Finset.insert_erase hxU
        have hTU' : T ⊆ U' := fun z hz =>
          Finset.mem_erase.mpr ⟨fun hzx => hxT (hzx ▸ hz), hTU hz⟩
        have hsdiff : U' \ T = (U \ T).erase x := by
          ext z; simp [U', Finset.mem_sdiff, Finset.mem_erase]; tauto
        have hk' : (U' \ T).card = k := by
          rw [hsdiff]; have := Finset.card_erase_add_one hx; omega
        have hex_sub : canonicalDemand v U ⊆ insert x (canonicalDemand v U') := by
          rw [← hUeq]
          rcases h_part10 n v U' x hv hxU' with heq | heq | ⟨f, _, heq⟩
          · rw [heq]; exact Finset.subset_insert x _
          · rw [heq]
          · rw [heq]; exact Finset.insert_subset_insert x (Finset.erase_subset f _)
        have hinter : canonicalDemand v U ∩ T ⊆ canonicalDemand v U' ∩ T := by
          intro z hz
          have hz1 : z ∈ insert x (canonicalDemand v U') := hex_sub (Finset.mem_inter.mp hz).1
          have hz2 : z ∈ T := (Finset.mem_inter.mp hz).2
          rcases Finset.mem_insert.mp hz1 with rfl | hzU'
          · exact absurd hz2 hxT
          · exact Finset.mem_inter.mpr ⟨hzU', hz2⟩
        exact hinter.trans (ih T U' hk' hTU')
    have hpers : HasPersistence (canonicalDemand v) :=
      fun T U hTU => hpers_ind (U \ T).card T U rfl hTU
    exact ⟨hcr, hpers, hsd⟩

  have h_part13 : ∀ n (v : ItemValuation n) (S : Finset (Fin n)) (x : Fin n),
      IsGSValuation v → x ∉ S → x ∈ canonicalDemand v (insert x S) →
        v {x} ≠ ⊥ ∧
        IsGSValuation (contractVal v x) ∧
        ∀ T ⊆ S, canonicalDemand (contractVal v x) T =
          (canonicalDemand v (insert x T)).erase x := by
    intro n v S x hv hxS hxD
    have hvD_ne : v (canonicalDemand v (insert x S)) ≠ ⊥ :=
      (h_part9 n v (insert x S) hv.1).2.1
    have hvx_ne : v {x} ≠ ⊥ :=
      h_hered hv hvD_ne (Finset.singleton_subset_iff.mpr hxD)
    have hcv_gs : IsGSValuation (contractVal v x) :=
      h_part4 n v x hv hvx_ne
    refine ⟨hvx_ne, hcv_gs, ?_⟩
    intro T hTS
    have hxT : x ∉ T := fun hm => hxS (hTS hm)
    have hpers := (h_part11 n v hv).2.1 (insert x T) (insert x S) (Finset.insert_subset_insert x hTS)
    have hxYstar : x ∈ canonicalDemand v (insert x T) :=
      hpers (Finset.mem_inter.mpr ⟨hxD, Finset.mem_insert_self x T⟩)
    let Ystar := canonicalDemand v (insert x T)
    let Zstar := Ystar.erase x
    obtain ⟨hYstar_sub, hvYstar_ne, hYstar_dom, _⟩ := h_part9 n v (insert x T) hv.1
    have hZstar_sub : Zstar ⊆ T := fun z hz => by
      rcases Finset.mem_insert.mp (hYstar_sub (Finset.erase_subset x Ystar hz)) with rfl | hzT
      · exact absurd rfl (Finset.mem_erase.mp hz).1
      · exact hzT
    have hxZstar : x ∉ Zstar := Finset.notMem_erase x Ystar
    have hinsZstar : insert x Zstar = Ystar := Finset.insert_erase hxYstar
    cases hvx : v {x} with
    | bot => exact absurd hvx hvx_ne
    | coe vx =>
      refine ((h_part9 n (contractVal v x) T hcv_gs.1).2.2.2 Zstar hZstar_sub (fun Z hZT => ?_)).symm
      have hxZ : x ∉ Z := fun hm => hxT (hZT hm)
      have hkey : demandKeyLe v (insert x Z) Ystar :=
        hYstar_dom (insert x Z) (Finset.insert_subset_insert x hZT)
      have hvYstar_ne' : v Ystar ≠ ⊥ := hvYstar_ne
      rw [← hinsZstar] at hkey hvYstar_ne'
      have hcZ : contractVal v x Z = v (insert x Z) + ((-vx : ℝ) : WithBot ℝ) := by
        simp [contractVal, hxZ, hvx]
      have hcZstar : contractVal v x Zstar = v (insert x Zstar) + ((-vx : ℝ) : WithBot ℝ) := by
        simp [contractVal, hxZstar, hvx]
      have hpsiZ : psiWeight (insert x Z) =
          (1 + (1 / 2 : ℝ) ^ (x.1 + 1)) + psiWeight Z :=
        Finset.sum_insert hxZ
      have hpsiZstar : psiWeight (insert x Zstar) =
          (1 + (1 / 2 : ℝ) ^ (x.1 + 1)) + psiWeight Zstar :=
        Finset.sum_insert hxZstar
      dsimp only [demandKeyLe] at hkey ⊢
      rcases hkey with hlt | ⟨heq, hle⟩
      · refine Or.inl ?_
        rw [hcZ, hcZstar]
        cases hvZstar : v (insert x Zstar) with
        | bot => exact absurd hvZstar hvYstar_ne'
        | coe rstar =>
          cases hvZ : v (insert x Z) with
          | bot => simp [← WithBot.coe_add]
          | coe r =>
            rw [hvZ, hvZstar, WithBot.coe_lt_coe] at hlt
            rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_lt_coe]
            linarith
      · refine Or.inr ⟨?_, ?_⟩
        · rw [hcZ, hcZstar, heq]
        · linarith

  clear h_unbot_add h_gs_cases h_build_transfer h_build_swap h_part4 h_hered h_geom h_tail_lt
    h_psi_inj h_part9 h_part10

  have h_invE_pos : 0 < invE := by
    unfold invE
    exact Real.exp_pos (-1)
  have h_exp_invE : Real.exp 1 * invE = 1 := by
    unfold invE
    rw [← Real.exp_add]
    norm_num
  have h_invE_eq : invE = (Real.exp 1)⁻¹ := by
    unfold invE
    exact Real.exp_neg 1
  have h_dt_bounds : ∀ {n : ℕ} (C : Finset (Fin n) → Finset (Fin n)) {t : ℝ},
      invE ≤ t → ∀ (S B : Finset (Fin n)) (τ β : Fin n → ℝ) (g : Fin n),
      invE ≤ deathTime C t S B τ β g ∧ deathTime C t S B τ β g ≤ t := by
    intro n C t ht S B τ β g
    let E : Set ℝ := {u : ℝ | invE ≤ u ∧ u ≤ t ∧ g ∉ C (presentSet S B τ β u)} ∪ {t}
    have htE : t ∈ E := Set.mem_union_right _ rfl
    have h_lo_E : ∀ u ∈ E, invE ≤ u := by
      rintro u (hu | hu)
      · exact hu.1
      · rw [Set.mem_singleton_iff.mp hu]
        exact ht
    have hBdd : BddBelow E := ⟨invE, h_lo_E⟩
    exact ⟨le_csInf ⟨t, htE⟩ h_lo_E, csInf_le hBdd htE⟩
  have h_ret_bounds : ∀ {n : ℕ} (C : Finset (Fin n) → Finset (Fin n)) {t : ℝ},
      invE ≤ t → t ≤ 1 →
      ∀ (S B : Finset (Fin n)) (τ β : Fin n → ℝ) (g : Fin n),
      0 ≤ retentionProb C t S B τ β g ∧ retentionProb C t S B τ β g ≤ 1 := by
    intro n C t ht_low ht_high S B τ β g
    unfold retentionProb
    split_ifs with hτ
    · obtain ⟨h_lo, h_hi⟩ := h_dt_bounds C ht_low S B τ β g
      have hexp1 : 1 ≤ Real.exp 1 * deathTime C t S B τ β g := by
        calc (1 : ℝ) = Real.exp 1 * invE := h_exp_invE.symm
          _ ≤ Real.exp 1 * deathTime C t S B τ β g :=
            mul_le_mul_of_nonneg_left h_lo (le_of_lt (Real.exp_pos 1))
      have hexp2 : Real.exp 1 * deathTime C t S B τ β g ≤ Real.exp 1 := by
        calc Real.exp 1 * deathTime C t S B τ β g ≤ Real.exp 1 * 1 :=
            mul_le_mul_of_nonneg_left (h_hi.trans ht_high) (le_of_lt (Real.exp_pos 1))
          _ = Real.exp 1 := mul_one _
      refine ⟨Real.log_nonneg hexp1, ?_⟩
      calc Real.log (Real.exp 1 * deathTime C t S B τ β g)
          ≤ Real.log (Real.exp 1) := Real.log_le_log (by linarith) hexp2
        _ = 1 := Real.log_exp 1
    · exact ⟨le_rfl, zero_le_one⟩
  have h_prod_bounds : ∀ {n : ℕ} (C : Finset (Fin n) → Finset (Fin n)) {t : ℝ},
      invE ≤ t → t ≤ 1 →
      ∀ (S B : Finset (Fin n)) (τ β : Fin n → ℝ) (A : Finset (Fin n)),
      0 ≤ retainProd C t S B τ β A ∧ retainProd C t S B τ β A ≤ 1 := by
    intro n C t ht_low ht_high S B τ β A
    unfold retainProd
    split_ifs with hAS
    · have h1_nn : 0 ≤ ∏ g ∈ A, retentionProb C t S B τ β g :=
        Finset.prod_nonneg (fun g _ => (h_ret_bounds C ht_low ht_high S B τ β g).1)

      have h1_le : ∏ g ∈ A, retentionProb C t S B τ β g ≤ 1 :=
        Finset.prod_le_one (fun g _ => (h_ret_bounds C ht_low ht_high S B τ β g).1)
          (fun g _ => (h_ret_bounds C ht_low ht_high S B τ β g).2)
      have h2_nn : 0 ≤ ∏ g ∈ S \ A, (1 - retentionProb C t S B τ β g) :=
        Finset.prod_nonneg (fun g _ => sub_nonneg.mpr (h_ret_bounds C ht_low ht_high S B τ β g).2)
      have h2_le : ∏ g ∈ S \ A, (1 - retentionProb C t S B τ β g) ≤ 1 :=
        Finset.prod_le_one (fun g _ => sub_nonneg.mpr (h_ret_bounds C ht_low ht_high S B τ β g).2)
          (fun g _ => sub_le_self 1 (h_ret_bounds C ht_low ht_high S B τ β g).1)
      exact ⟨mul_nonneg h1_nn h2_nn, mul_le_one₀ h1_le h2_nn h2_le⟩
    · exact ⟨le_rfl, zero_le_one⟩
  have h_dt_cand_eq : ∀ {n : ℕ} (C : Finset (Fin n) → Finset (Fin n)) {t : ℝ},
      invE ≤ t → ∀ (S B : Finset (Fin n)) (τ β : Fin n → ℝ) (g : Fin n),
      let Cand := Bool ⊕ {s // s ∈ S} ⊕ {b // b ∈ B}
      let candVal : Cand → ℝ := fun c => match c with
        | Sum.inl true => invE
        | Sum.inl false => t
        | Sum.inr (Sum.inl s) => τ s.1
        | Sum.inr (Sum.inr b) => β b.1
      let candEff : Cand → ℝ := fun c =>
        let u := candVal c
        if invE ≤ u ∧ u ≤ t ∧ g ∉ C (presentSet S B τ β u) then u else t
      deathTime C t S B τ β g =
        (Finset.univ : Finset Cand).inf' ⟨Sum.inl true, Finset.mem_univ _⟩ candEff := by
    intro n C t ht S B τ β g Cand candVal candEff
    let E : Set ℝ := {u : ℝ | invE ≤ u ∧ u ≤ t ∧ g ∉ C (presentSet S B τ β u)} ∪ {t}
    have htE : t ∈ E := Set.mem_union_right _ rfl
    have hBdd : BddBelow E := ⟨invE, by
      rintro u (hu | hu)
      · exact hu.1
      · rw [Set.mem_singleton_iff.mp hu]
        exact ht⟩
    have hne : (Finset.univ : Finset Cand).Nonempty := ⟨Sum.inl true, Finset.mem_univ _⟩
    apply le_antisymm
    · refine Finset.le_inf' hne candEff (fun c _ => csInf_le hBdd ?_)
      dsimp only [candEff]
      split_ifs with hc
      · exact Set.mem_union_left _ hc
      · exact htE
    · refine le_csInf ⟨t, htE⟩ (fun v hv => ?_)
      rcases hv with ⟨hv_lo, hv_hi, hv_not⟩ | hv_eq
      · let L := (Finset.univ : Finset Cand).filter (fun c => candVal c ≤ v)
        have hL_ne : L.Nonempty := ⟨Sum.inl true, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv_lo⟩⟩
        obtain ⟨c₀, hc₀L, hc₀_eq⟩ := Finset.exists_mem_eq_sup' hL_ne candVal
        let u₀ := L.sup' hL_ne candVal
        have hu₀_eq : candVal c₀ = u₀ := hc₀_eq.symm
        have h_true_L : (Sum.inl true : Cand) ∈ L :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv_lo⟩
        have hu₀_lo : invE ≤ u₀ := Finset.le_sup' candVal h_true_L
        have hu₀_v : u₀ ≤ v := by
          rw [← hu₀_eq]
          exact (Finset.mem_filter.mp hc₀L).2
        have h_pres : presentSet S B τ β u₀ = presentSet S B τ β v := by
          unfold presentSet
          congr 1
          · ext z
            simp only [Finset.mem_filter]
            refine ⟨fun ⟨hz, hle⟩ => ⟨hz, hle.trans hu₀_v⟩, fun ⟨hz, hle⟩ => ⟨hz, ?_⟩⟩
            have hcL : (Sum.inr (Sum.inl ⟨z, hz⟩) : Cand) ∈ L :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩
            exact Finset.le_sup' candVal hcL
          · ext z
            simp only [Finset.mem_filter]
            refine ⟨fun ⟨hz, hle⟩ => ⟨hz, hle.trans hu₀_v⟩, fun ⟨hz, hle⟩ => ⟨hz, ?_⟩⟩
            have hcL : (Sum.inr (Sum.inr ⟨z, hz⟩) : Cand) ∈ L :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩
            exact Finset.le_sup' candVal hcL
        have hc₀_eff : candEff c₀ = u₀ := by
          dsimp only [candEff]
          rw [hu₀_eq, h_pres]
          exact if_pos ⟨hu₀_lo, hu₀_v.trans hv_hi, hv_not⟩
        calc (Finset.univ : Finset Cand).inf' hne candEff
            ≤ candEff c₀ := Finset.inf'_le candEff (Finset.mem_univ c₀)
          _ = u₀ := hc₀_eff
          _ ≤ v := hu₀_v
      · rw [Set.mem_singleton_iff.mp hv_eq]
        have h_false : candEff (Sum.inl false) = t := by
          dsimp only [candEff, candVal]
          split_ifs <;> rfl
        calc (Finset.univ : Finset Cand).inf' hne candEff
            ≤ candEff (Sum.inl false) := Finset.inf'_le candEff (Finset.mem_univ (Sum.inl false))
          _ = t := h_false
  have h_dt_mem : ∀ {n : ℕ} (C : Finset (Fin n) → Finset (Fin n)) {t : ℝ},
      invE ≤ t → ∀ (S B : Finset (Fin n)) (τ β : Fin n → ℝ) (g : Fin n),
      deathTime C t S B τ β g ∈
        {u : ℝ | invE ≤ u ∧ u ≤ t ∧ g ∉ C (presentSet S B τ β u)} ∪ {t} := by
    intro n C t ht S B τ β g
    let Cand := Bool ⊕ {s // s ∈ S} ⊕ {b // b ∈ B}
    let candVal : Cand → ℝ := fun c => match c with
      | Sum.inl true => invE
      | Sum.inl false => t
      | Sum.inr (Sum.inl s) => τ s.1
      | Sum.inr (Sum.inr b) => β b.1
    let candEff : Cand → ℝ := fun c =>
      let u := candVal c
      if invE ≤ u ∧ u ≤ t ∧ g ∉ C (presentSet S B τ β u) then u else t
    have hne : (Finset.univ : Finset Cand).Nonempty := ⟨Sum.inl true, Finset.mem_univ _⟩
    obtain ⟨c, _, hc_eq⟩ := Finset.exists_mem_eq_inf' hne candEff
    have h_eq : deathTime C t S B τ β g = candEff c :=
      (h_dt_cand_eq C ht S B τ β g).trans hc_eq
    rw [h_eq]
    dsimp only [candEff]
    split_ifs with hc
    · exact Set.mem_union_left _ hc
    · exact Set.mem_union_right _ rfl
  have h_meas_inf : ∀ {Ω α : Type} [MeasurableSpace Ω] [DecidableEq α]
      (s : Finset α) (hs : s.Nonempty) (f : α → Ω → ℝ),
      (∀ c ∈ s, Measurable (f c)) → Measurable (fun ω => s.inf' hs (fun c => f c ω)) := by
    intro Ω α _ _ s hs f hf
    induction s using Finset.induction_on with
    | empty => exact (Finset.not_nonempty_empty hs).elim
    | insert a s has ih =>
      rcases s.eq_empty_or_nonempty with rfl | hne
      · simp only [Finset.insert_empty, Finset.inf'_singleton]
        exact hf a (Finset.mem_singleton_self a)
      · have h_eq : ∀ ω, (insert a s).inf' hs (fun c => f c ω) =
            (f a ω) ⊓ (s.inf' hne (fun c => f c ω)) := by
          intro ω
          exact Finset.inf'_insert hne (fun c => f c ω)
        simp_rw [h_eq]
        exact (hf a (Finset.mem_insert_self a s)).inf
          (ih hne (fun c hc => hf c (Finset.mem_insert_of_mem hc)))
  have h_meas_pres_eq : ∀ {n : ℕ} {Ω : Type} [MeasurableSpace Ω]
      (S B : Finset (Fin n)) (τ_fn β_fn : Ω → (Fin n → ℝ)) (u_fn : Ω → ℝ),
      Measurable τ_fn → Measurable β_fn → Measurable u_fn →
      ∀ U₀ : Finset (Fin n),
        MeasurableSet {ω : Ω | presentSet S B (τ_fn ω) (β_fn ω) (u_fn ω) = U₀} := by
    intro n Ω _ S B τ_fn β_fn u_fn hτ hβ hu U₀
    have h_mem : ∀ z : Fin n,
        MeasurableSet {ω : Ω | z ∈ presentSet S B (τ_fn ω) (β_fn ω) (u_fn ω)} := by
      intro z
      have heq_z : {ω : Ω | z ∈ presentSet S B (τ_fn ω) (β_fn ω) (u_fn ω)} =
          (if z ∈ S then {ω | τ_fn ω z ≤ u_fn ω} else ∅) ∪
          (if z ∈ B then {ω | β_fn ω z ≤ u_fn ω} else ∅) := by
        ext ω; simp [presentSet]
      rw [heq_z]
      refine MeasurableSet.union ?_ ?_
      · split_ifs
        · exact measurableSet_le ((measurable_pi_apply z).comp hτ) hu
        · exact MeasurableSet.empty
      · split_ifs
        · exact measurableSet_le ((measurable_pi_apply z).comp hβ) hu
        · exact MeasurableSet.empty
    have heq : {ω : Ω | presentSet S B (τ_fn ω) (β_fn ω) (u_fn ω) = U₀} =
        ⋂ z : Fin n,
          if z ∈ U₀ then {ω | z ∈ presentSet S B (τ_fn ω) (β_fn ω) (u_fn ω)}
          else {ω | z ∈ presentSet S B (τ_fn ω) (β_fn ω) (u_fn ω)}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      refine ⟨fun h z => by subst h; split_ifs with hz <;> simp [hz], fun hzU => ?_⟩
      ext z
      specialize hzU z
      by_cases hz : z ∈ U₀ <;> simp [hz] at hzU ⊢ <;> exact hzU
    rw [heq]
    refine MeasurableSet.iInter (fun z => ?_)
    split_ifs
    · exact h_mem z
    · exact (h_mem z).compl
  have h_meas_prod : ∀ {n : ℕ} {Ω : Type} [MeasurableSpace Ω]
      (C : Finset (Fin n) → Finset (Fin n)) {t : ℝ}, invE ≤ t →
      ∀ (S B A : Finset (Fin n)) (τ_fn β_fn : Ω → (Fin n → ℝ)),
      Measurable τ_fn → Measurable β_fn →
      (∀ g, Measurable (fun ω => retentionProb C t S B (τ_fn ω) (β_fn ω) g)) ∧
      Measurable (fun ω => retainProd C t S B (τ_fn ω) (β_fn ω) A) := by
    intro n Ω _ C t ht S B A τ_fn β_fn hτ hβ
    have h_meas_dt : ∀ g, Measurable (fun ω => deathTime C t S B (τ_fn ω) (β_fn ω) g) := by
      intro g
      let Cand := Bool ⊕ {s // s ∈ S} ⊕ {b // b ∈ B}
      let candVal : Cand → Ω → ℝ := fun c ω => match c with
        | Sum.inl true => invE
        | Sum.inl false => t
        | Sum.inr (Sum.inl s) => τ_fn ω s.1
        | Sum.inr (Sum.inr b) => β_fn ω b.1
      let candEff : Cand → Ω → ℝ := fun c ω =>
        let u := candVal c ω
        if invE ≤ u ∧ u ≤ t ∧ g ∉ C (presentSet S B (τ_fn ω) (β_fn ω) u) then u else t
      have h_eq : ∀ ω, deathTime C t S B (τ_fn ω) (β_fn ω) g =
          (Finset.univ : Finset Cand).inf' ⟨Sum.inl true, Finset.mem_univ _⟩ (fun c => candEff c ω) :=
        fun ω => h_dt_cand_eq C ht S B (τ_fn ω) (β_fn ω) g
      simp_rw [h_eq]
      refine h_meas_inf _ _ candEff (fun c _ => ?_)
      have hu : Measurable (candVal c) := by
        cases c with
        | inl b => cases b <;> exact measurable_const
        | inr sb =>
          cases sb with
          | inl s => exact (measurable_pi_apply s.1).comp hτ
          | inr b => exact (measurable_pi_apply b.1).comp hβ
      have h_notC : MeasurableSet
          {ω : Ω | g ∉ C (presentSet S B (τ_fn ω) (β_fn ω) (candVal c ω))} := by
        let badSets := (Finset.univ : Finset (Finset (Fin n))).filter (fun U => g ∉ C U)
        have heq_bad : {ω : Ω | g ∉ C (presentSet S B (τ_fn ω) (β_fn ω) (candVal c ω))} =
            ⋃ U ∈ badSets, {ω | presentSet S B (τ_fn ω) (β_fn ω) (candVal c ω) = U} := by
          ext ω
          simp [badSets]
        rw [heq_bad]
        exact Finset.measurableSet_biUnion _ (fun U _ => h_meas_pres_eq S B τ_fn β_fn (candVal c) hτ hβ hu U)
      have h_cond : MeasurableSet {ω : Ω | invE ≤ candVal c ω ∧ candVal c ω ≤ t ∧
          g ∉ C (presentSet S B (τ_fn ω) (β_fn ω) (candVal c ω))} :=
        (measurableSet_le measurable_const hu).inter
          ((measurableSet_le hu measurable_const).inter h_notC)
      exact Measurable.ite h_cond hu measurable_const
    have h_meas_ret : ∀ g, Measurable (fun ω => retentionProb C t S B (τ_fn ω) (β_fn ω) g) := by
      intro g
      unfold retentionProb
      refine Measurable.ite (measurableSet_le ((measurable_pi_apply g).comp hτ) measurable_const) ?_
        measurable_const
      exact Real.measurable_log.comp (measurable_const.mul (h_meas_dt g))
    refine ⟨h_meas_ret, ?_⟩
    unfold retainProd
    split_ifs with hAS
    · exact (Finset.measurable_prod A (fun g _ => h_meas_ret g)).mul
        (Finset.measurable_prod (S \ A) (fun g _ => measurable_const.sub (h_meas_ret g)))
    · exact measurable_const
  have h_unif1D_prob : ∀ {s : ℝ}, 0 < s →
      IsProbabilityMeasure ((ENNReal.ofReal s)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) s)) := by
    intro s hs
    rw [MeasureTheory.isProbabilityMeasure_iff]
    simp only [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul, Real.volume_Icc,
      sub_zero]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hs).ne' ENNReal.ofReal_ne_top
  have h_pres_update : ∀ {n : ℕ} (S B : Finset (Fin n)) {x : Fin n}, x ∉ B →
      ∀ (τ β : Fin n → ℝ) (u v : ℝ),
      presentSet S (insert x B) τ (Function.update β x u) v =
        if u ≤ v then insert x (presentSet S B τ β v) else presentSet S B τ β v := by
    intro n S B x hxB τ β u v
    ext z
    by_cases hzx : z = x
    · subst hzx
      by_cases huv : u ≤ v
      · simp [presentSet, huv]
      · simp [presentSet, huv, hxB]
    · by_cases huv : u ≤ v
      · simp [presentSet, huv, hzx]
      · simp [presentSet, huv, hzx]
  have h_pres_mono : ∀ {n : ℕ} (S B : Finset (Fin n)) (τ β : Fin n → ℝ) {v₁ v₂ : ℝ},
      v₁ ≤ v₂ → presentSet S B τ β v₁ ⊆ presentSet S B τ β v₂ := by
    intro n S B τ β v₁ v₂ hv z hz
    simp only [presentSet, Finset.mem_union, Finset.mem_filter] at hz ⊢
    rcases hz with ⟨hzS, hle⟩ | ⟨hzB, hle⟩
    · exact Or.inl ⟨hzS, hle.trans hv⟩
    · exact Or.inr ⟨hzB, hle.trans hv⟩

  have h_lip_retain : ∀ {n : ℕ} (C : Finset (Fin n) → Finset (Fin n)) {t : ℝ}
      (S B : Finset (Fin n)) (x : Fin n) (A : Finset (Fin n)) (τ β : Fin n → ℝ),
      HasPersistence C → invE ≤ t → t ≤ 1 → x ∉ S ∪ B → A ⊆ S →
      (∀ u₁ ∈ Set.Icc invE t, ∀ u₂ ∈ Set.Icc invE t,
        |retainProd C t S (insert x B) τ (Function.update β x u₁) A -
          retainProd C t S (insert x B) τ (Function.update β x u₂) A| ≤
          (((A.card : ℝ) + ((S \ A).card : ℝ)) * Real.exp 1) * |u₁ - u₂|) ∧
      ContinuousOn (fun u => u * retainProd C t S (insert x B) τ (Function.update β x u) A)
        (Set.Icc invE t) := by
    intro n C t S B x A τ β hP ht_low ht_high hxSB hA
    have hxB : x ∉ B := fun hb => hxSB (Finset.mem_union_right S hb)
    have h_clamp : ∀ g ∈ S, τ g ≤ invE → ∀ τ₁ τ₂ : ℝ, invE ≤ τ₁ → τ₁ < τ₂ → τ₂ ≤ t →
        let σ := fun u => deathTime C t S (insert x B) τ (Function.update β x u) g
        σ τ₁ ≤ σ τ₂ ∧ (σ τ₁ ≠ σ τ₂ → τ₁ ≤ σ τ₁ ∧ σ τ₂ ≤ τ₂) := by
      intro g hgS hg_early τ₁ τ₂ hτ₁_lo hτ₁₂ hτ₂_hi
      dsimp only
      let W : ℝ → ℝ → Finset (Fin n) :=
        fun u v => presentSet S (insert x B) τ (Function.update β x u) v
      let E : ℝ → Set ℝ := fun u => {v : ℝ | invE ≤ v ∧ v ≤ t ∧ g ∉ C (W u v)} ∪ {t}
      have hBdd : ∀ u, BddBelow (E u) := fun u => ⟨invE, by
        rintro v (hv | hv)
        · exact hv.1
        · rw [Set.mem_singleton_iff.mp hv]; exact ht_low⟩
      have hW_sub : ∀ v, W τ₂ v ⊆ W τ₁ v := by
        intro v
        dsimp only [W]
        rw [h_pres_update S B hxB τ β τ₂ v, h_pres_update S B hxB τ β τ₁ v]
        split_ifs with h2 h1 h1
        · exact subset_rfl
        · linarith
        · exact Finset.subset_insert x _
        · exact subset_rfl
      have hE_sub : E τ₂ ⊆ E τ₁ := by
        rintro v (⟨hv_lo, hv_hi, hv_not⟩ | hv_eq)
        · refine Set.mem_union_left _ ⟨hv_lo, hv_hi, ?_⟩
          intro hgC₁
          have hgW₂ : g ∈ W τ₂ v := by
            simp [W, presentSet, hgS, hg_early.trans hv_lo]
          exact hv_not (hP (W τ₂ v) (W τ₁ v) (hW_sub v) (Finset.mem_inter.mpr ⟨hgC₁, hgW₂⟩))
        · exact Set.mem_union_right _ hv_eq
      have h_le : deathTime C t S (insert x B) τ (Function.update β x τ₁) g ≤
          deathTime C t S (insert x B) τ (Function.update β x τ₂) g :=
        csInf_le_csInf (hBdd τ₁) ⟨t, Set.mem_union_right _ rfl⟩ hE_sub
      refine ⟨h_le, fun h_ne => ?_⟩
      let σ₁ := deathTime C t S (insert x B) τ (Function.update β x τ₁) g
      let σ₂ := deathTime C t S (insert x B) τ (Function.update β x τ₂) g
      have h_lt : σ₁ < σ₂ := lt_of_le_of_ne h_le h_ne
      have hσ₂_hi : σ₂ ≤ t := (h_dt_bounds C ht_low S (insert x B) τ _ g).2
      have hσ₁_lt_t : σ₁ < t := h_lt.trans_le hσ₂_hi
      have hσ₁_mem := h_dt_mem C ht_low S (insert x B) τ (Function.update β x τ₁) g
      rcases hσ₁_mem with ⟨hσ₁_lo, _, hσ₁_notC⟩ | hσ₁_eq_t
      · have h_low_clamp : τ₁ ≤ σ₁ := by
          by_contra h_lt_τ₁
          push_neg at h_lt_τ₁
          have hW_eq : W τ₂ σ₁ = W τ₁ σ₁ := by
            dsimp only [W]
            rw [h_pres_update S B hxB τ β τ₂ σ₁, h_pres_update S B hxB τ β τ₁ σ₁,
              if_neg (by linarith), if_neg (by linarith)]
          have h_mem₂ : σ₁ ∈ E τ₂ :=
            Set.mem_union_left _ ⟨hσ₁_lo, hσ₁_lt_t.le, by rwa [hW_eq]⟩
          exact not_lt_of_ge (csInf_le (hBdd τ₂) h_mem₂) h_lt
        have h_lt_τ₂ : σ₁ < τ₂ := by
          by_contra h_ge_τ₂
          push_neg at h_ge_τ₂
          have hW_eq : W τ₂ σ₁ = W τ₁ σ₁ := by
            dsimp only [W]
            rw [h_pres_update S B hxB τ β τ₂ σ₁, h_pres_update S B hxB τ β τ₁ σ₁,
              if_pos h_ge_τ₂, if_pos (by linarith)]
          have h_mem₂ : σ₁ ∈ E τ₂ :=
            Set.mem_union_left _ ⟨hσ₁_lo, hσ₁_lt_t.le, by rwa [hW_eq]⟩
          exact not_lt_of_ge (csInf_le (hBdd τ₂) h_mem₂) h_lt
        have hg_W₁ : g ∈ W τ₁ σ₁ := by
          have h_lo' : τ g ≤ σ₁ := hg_early.trans hσ₁_lo
          simp [W, presentSet, hgS, h_lo']
        have h_notC_τ₂ : g ∉ C (W τ₁ τ₂) := by
          intro hgC
          exact hσ₁_notC (hP (W τ₁ σ₁) (W τ₁ τ₂)
            (h_pres_mono S (insert x B) τ _ h_lt_τ₂.le) (Finset.mem_inter.mpr ⟨hgC, hg_W₁⟩))
        have hW_τ₂_eq : W τ₂ τ₂ = W τ₁ τ₂ := by
          dsimp only [W]
          rw [h_pres_update S B hxB τ β τ₂ τ₂, h_pres_update S B hxB τ β τ₁ τ₂,
            if_pos le_rfl, if_pos hτ₁₂.le]
        have h_mem_τ₂ : τ₂ ∈ E τ₂ :=
          Set.mem_union_left _ ⟨hτ₁_lo.trans hτ₁₂.le, hτ₂_hi, by rwa [hW_τ₂_eq]⟩
        exact ⟨h_low_clamp, csInf_le (hBdd τ₂) h_mem_τ₂⟩
      · exact (hσ₁_lt_t.ne (Set.mem_singleton_iff.mp hσ₁_eq_t)).elim
    have h_lip_σ : ∀ g ∈ S, τ g ≤ invE →
        LipschitzOnWith 1
          (fun u => deathTime C t S (insert x B) τ (Function.update β x u) g)
          (Set.Icc invE t) := by
      intro g hgS hg_early
      refine LipschitzOnWith.of_dist_le_mul (fun u₁ hu₁ u₂ hu₂ => ?_)
      simp only [NNReal.coe_one, one_mul, Real.dist_eq]
      let σ := fun u => deathTime C t S (insert x B) τ (Function.update β x u) g
      rcases lt_trichotomy u₁ u₂ with hlt | rfl | hgt
      · obtain ⟨hle, hcl⟩ := h_clamp g hgS hg_early u₁ u₂ hu₁.1 hlt hu₂.2
        by_cases hne : σ u₁ = σ u₂
        · simp [σ, hne]
        · obtain ⟨hc1, hc2⟩ := hcl hne
          rw [abs_of_nonpos (sub_nonpos.mpr hle), abs_of_nonpos (sub_nonpos.mpr hlt.le)]
          linarith
      · simp
      · obtain ⟨hle, hcl⟩ := h_clamp g hgS hg_early u₂ u₁ hu₂.1 hgt hu₁.2
        by_cases hne : σ u₂ = σ u₁
        · simp [σ, hne]
        · obtain ⟨hc1, hc2⟩ := hcl hne
          rw [abs_of_nonneg (sub_nonneg.mpr hle), abs_of_nonneg (sub_nonneg.mpr hgt.le)]
          linarith
    let I := Set.Icc invE t
    have h_log_lip : ∀ {y₁ y₂ : ℝ}, invE ≤ y₁ → invE ≤ y₂ →
        |Real.log (Real.exp 1 * y₁) - Real.log (Real.exp 1 * y₂)| ≤ Real.exp 1 * |y₁ - y₂| := by
      have h_aux : ∀ {a b : ℝ}, invE ≤ a → a ≤ b →
          |Real.log (Real.exp 1 * a) - Real.log (Real.exp 1 * b)| ≤ Real.exp 1 * |a - b| := by
        intro a b ha hab
        have ha_pos : 0 < a := h_invE_pos.trans_le ha
        have hb_pos : 0 < b := ha_pos.trans_le hab
        have hexp_pos : 0 < Real.exp 1 := Real.exp_pos 1
        have h_log_le : Real.log (Real.exp 1 * a) ≤ Real.log (Real.exp 1 * b) :=
          Real.log_le_log (mul_pos hexp_pos ha_pos) (mul_le_mul_of_nonneg_left hab hexp_pos.le)
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h_log_le),
          abs_sub_comm (a := a), abs_of_nonneg (sub_nonneg.mpr hab)]
        have h_diff : Real.log (Real.exp 1 * b) - Real.log (Real.exp 1 * a) = Real.log (b / a) := by
          rw [← Real.log_div (mul_pos hexp_pos hb_pos).ne' (mul_pos hexp_pos ha_pos).ne',
            mul_div_mul_left b a hexp_pos.ne']
        rw [h_diff]
        have h1 : Real.log (b / a) ≤ (b - a) / a := by
          calc Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb_pos ha_pos)
            _ = (b - a) / a := by field_simp
        have h2 : (b - a) / a ≤ (b - a) / invE :=
          div_le_div_of_nonneg_left (sub_nonneg.mpr hab) h_invE_pos ha
        have h3 : (b - a) / invE = Real.exp 1 * (b - a) := by
          rw [h_invE_eq, div_inv_eq_mul, mul_comm]
        linarith
      intro y₁ y₂ hy₁ hy₂
      rcases le_total y₁ y₂ with h12 | h21
      · exact h_aux hy₁ h12
      · rw [abs_sub_comm, abs_sub_comm y₁ y₂]
        exact h_aux hy₂ h21
    have h_mul_lip : ∀ {f₁ f₂ : ℝ → ℝ} {L₁ L₂ : ℝ},
        0 ≤ L₁ → 0 ≤ L₂ →
        (∀ u ∈ I, |f₁ u| ≤ 1) → (∀ u ∈ I, |f₂ u| ≤ 1) →
        (∀ u₁ ∈ I, ∀ u₂ ∈ I, |f₁ u₁ - f₁ u₂| ≤ L₁ * |u₁ - u₂|) →
        (∀ u₁ ∈ I, ∀ u₂ ∈ I, |f₂ u₁ - f₂ u₂| ≤ L₂ * |u₁ - u₂|) →
        (∀ u ∈ I, |f₁ u * f₂ u| ≤ 1) ∧
          (∀ u₁ ∈ I, ∀ u₂ ∈ I, |f₁ u₁ * f₂ u₁ - f₁ u₂ * f₂ u₂| ≤ (L₁ + L₂) * |u₁ - u₂|) := by
      intro f₁ f₂ L₁ L₂ hL₁ hL₂ hb₁ hb₂ hl₁ hl₂
      refine ⟨fun u hu => by rw [abs_mul]; exact mul_le_one₀ (hb₁ u hu) (abs_nonneg _) (hb₂ u hu),
        fun u₁ hu₁ u₂ hu₂ => ?_⟩
      calc |f₁ u₁ * f₂ u₁ - f₁ u₂ * f₂ u₂|
          = |(f₁ u₁ - f₁ u₂) * f₂ u₁ + f₁ u₂ * (f₂ u₁ - f₂ u₂)| := by ring_nf
        _ ≤ |(f₁ u₁ - f₁ u₂) * f₂ u₁| + |f₁ u₂ * (f₂ u₁ - f₂ u₂)| := abs_add_le _ _
        _ = |f₁ u₁ - f₁ u₂| * |f₂ u₁| + |f₁ u₂| * |f₂ u₁ - f₂ u₂| := by rw [abs_mul, abs_mul]
        _ ≤ (L₁ * |u₁ - u₂|) * 1 + 1 * (L₂ * |u₁ - u₂|) := by
            gcongr
            · exact hl₁ u₁ hu₁ u₂ hu₂
            · exact hb₂ u₁ hu₁
            · exact hb₁ u₂ hu₂
            · exact hl₂ u₁ hu₁ u₂ hu₂
        _ = (L₁ + L₂) * |u₁ - u₂| := by ring
    have h_finset_prod_lip : ∀ {α : Type} [DecidableEq α] (F : Finset α) (L : ℝ),
        0 ≤ L → ∀ (f : α → ℝ → ℝ),
        (∀ a ∈ F, (∀ u ∈ I, |f a u| ≤ 1) ∧
          (∀ u₁ ∈ I, ∀ u₂ ∈ I, |f a u₁ - f a u₂| ≤ L * |u₁ - u₂|)) →
        (∀ u ∈ I, |∏ a ∈ F, f a u| ≤ 1) ∧
          (∀ u₁ ∈ I, ∀ u₂ ∈ I,
            |(∏ a ∈ F, f a u₁) - (∏ a ∈ F, f a u₂)| ≤ ((F.card : ℝ) * L) * |u₁ - u₂|) := by
      intro α _ F L hL f hf
      induction F using Finset.induction_on with
      | empty =>
        refine ⟨fun _ _ => by simp, fun _ _ _ _ => by simp⟩
      | insert a s has ih =>
        obtain ⟨hba, hla⟩ := hf a (Finset.mem_insert_self a s)
        obtain ⟨hbs, hls⟩ := ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
        have hKs : 0 ≤ (s.card : ℝ) * L := mul_nonneg (Nat.cast_nonneg _) hL
        obtain ⟨hb_prod, hl_prod⟩ := h_mul_lip hL hKs hba hbs hla hls
        refine ⟨fun u hu => by simpa [Finset.prod_insert has] using hb_prod u hu,
          fun u₁ hu₁ u₂ hu₂ => ?_⟩
        have h_card : ((insert a s).card : ℝ) * L = L + (s.card : ℝ) * L := by
          rw [Finset.card_insert_of_notMem has]
          push_cast
          ring
        rw [h_card, Finset.prod_insert has, Finset.prod_insert has]
        exact hl_prod u₁ hu₁ u₂ hu₂
    have h_θ_lip : ∀ g ∈ S,
        (∀ u ∈ I, |retentionProb C t S (insert x B) τ (Function.update β x u) g| ≤ 1) ∧
        (∀ u₁ ∈ I, ∀ u₂ ∈ I,
          |retentionProb C t S (insert x B) τ (Function.update β x u₁) g -
            retentionProb C t S (insert x B) τ (Function.update β x u₂) g| ≤
            Real.exp 1 * |u₁ - u₂|) := by
      intro g hgS
      refine ⟨fun u _ => ?_, fun u₁ hu₁ u₂ hu₂ => ?_⟩
      · obtain ⟨h0, h1⟩ := h_ret_bounds C ht_low ht_high S (insert x B) τ (Function.update β x u) g
        rw [abs_of_nonneg h0]
        exact h1
      · unfold retentionProb
        split_ifs with hτ
        · have h_lip1 := h_lip_σ g hgS hτ
          have h_dist := h_lip1.dist_le_mul u₁ hu₁ u₂ hu₂
          simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h_dist
          have hlo1 := (h_dt_bounds C ht_low S (insert x B) τ (Function.update β x u₁) g).1
          have hlo2 := (h_dt_bounds C ht_low S (insert x B) τ (Function.update β x u₂) g).1
          exact (h_log_lip hlo1 hlo2).trans
            (mul_le_mul_of_nonneg_left h_dist (Real.exp_pos 1).le)
        · simp [mul_nonneg (Real.exp_pos 1).le (abs_nonneg _)]
    obtain ⟨hbA, hlA⟩ := h_finset_prod_lip A (Real.exp 1) (Real.exp_pos 1).le
      (fun g u => retentionProb C t S (insert x B) τ (Function.update β x u) g)
      (fun g hgA => h_θ_lip g (hA hgA))
    obtain ⟨hbSA, hlSA⟩ := h_finset_prod_lip (S \ A) (Real.exp 1) (Real.exp_pos 1).le
      (fun g u => 1 - retentionProb C t S (insert x B) τ (Function.update β x u) g)
      (fun g hgSA => by
        obtain ⟨_, hl⟩ := h_θ_lip g (Finset.mem_sdiff.mp hgSA).1
        refine ⟨fun u _ => ?_, fun u₁ hu₁ u₂ hu₂ => ?_⟩
        · obtain ⟨h0, h1⟩ :=
            h_ret_bounds C ht_low ht_high S (insert x B) τ (Function.update β x u) g
          rw [abs_of_nonneg (sub_nonneg.mpr h1)]
          linarith
        · have heq : (1 - retentionProb C t S (insert x B) τ (Function.update β x u₁) g) -
              (1 - retentionProb C t S (insert x B) τ (Function.update β x u₂) g) =
              -(retentionProb C t S (insert x B) τ (Function.update β x u₁) g -
                retentionProb C t S (insert x B) τ (Function.update β x u₂) g) := by ring
          rw [heq, abs_neg]
          exact hl u₁ hu₁ u₂ hu₂)
    have hKA_nn : 0 ≤ (A.card : ℝ) * Real.exp 1 := by positivity
    have hKSA_nn : 0 ≤ ((S \ A).card : ℝ) * Real.exp 1 := by positivity
    obtain ⟨hb_phi, hl_phi⟩ := h_mul_lip hKA_nn hKSA_nn hbA hbSA hlA hlSA
    have h_phi_lip_explicit : ∀ u₁ ∈ I, ∀ u₂ ∈ I,
        |retainProd C t S (insert x B) τ (Function.update β x u₁) A -
          retainProd C t S (insert x B) τ (Function.update β x u₂) A| ≤
          (((A.card : ℝ) + ((S \ A).card : ℝ)) * Real.exp 1) * |u₁ - u₂| := by
      intro u₁ hu₁ u₂ hu₂
      simp only [retainProd, if_pos hA]
      have h_eqK : ((A.card : ℝ) + ((S \ A).card : ℝ)) * Real.exp 1 =
          (A.card : ℝ) * Real.exp 1 + ((S \ A).card : ℝ) * Real.exp 1 := add_mul _ _ _
      rw [h_eqK]
      exact hl_phi u₁ hu₁ u₂ hu₂
    have hb_id : ∀ u ∈ I, |u| ≤ 1 := fun u hu => by
      rw [abs_of_nonneg (h_invE_pos.le.trans hu.1)]
      exact hu.2.trans ht_high
    have hl_id : ∀ u₁ ∈ I, ∀ u₂ ∈ I, |u₁ - u₂| ≤ 1 * |u₁ - u₂| := fun _ _ _ _ => by simp
    obtain ⟨_, hl_tot⟩ := h_mul_lip zero_le_one (add_nonneg hKA_nn hKSA_nn) hb_id hb_phi hl_id hl_phi
    have h_lip_uφ : LipschitzOnWith ⟨1 + ((A.card : ℝ) * Real.exp 1 + ((S \ A).card : ℝ) * Real.exp 1), by positivity⟩
        (fun u => u * retainProd C t S (insert x B) τ (Function.update β x u) A) I := by
      refine LipschitzOnWith.of_dist_le_mul (fun u₁ hu₁ u₂ hu₂ => ?_)
      simp only [NNReal.coe_mk, Real.dist_eq, retainProd, if_pos hA]
      exact hl_tot u₁ hu₁ u₂ hu₂
    exact ⟨h_phi_lip_explicit, h_lip_uφ.continuousOn⟩

  clear h_dt_bounds h_dt_cand_eq h_dt_mem h_meas_inf

  let moveDerivBranch : ∀ {n : ℕ}, (Finset (Fin n) → Finset (Fin n)) → ℝ →
      Finset (Fin n) → Finset (Fin n) → (Fin n → ℝ) → Fin n → Finset (Fin n) →
      Finset (Fin n) → (Fin n → ℝ) → ℝ → ℝ :=
    fun {n} C t S B β x A F₀ τ s =>
      let θ := fun g => retentionProb C t S (insert x B) τ (Function.update β x s) g
      let φ := retainProd C t S (insert x B) τ (Function.update β x s) A
      if F₀.card = 0 then
        φ
      else if h1 : F₀.card = 1 then
        let f := F₀.min' (Finset.card_pos.mp (by omega))
        if f ∈ A then
          φ + (∏ g ∈ A.erase f, θ g) * (∏ g ∈ S \ A, (1 - θ g))
        else
          -Real.log (Real.exp 1 * s) *
            ((∏ g ∈ A, θ g) * (∏ g ∈ S \ insert f A, (1 - θ g)))
      else 0

  let moveDeriv : ∀ {n : ℕ}, (Finset (Fin n) → Finset (Fin n)) → ℝ →
      Finset (Fin n) → Finset (Fin n) → (Fin n → ℝ) → Fin n → Finset (Fin n) →
      (Fin n → ℝ) → ℝ → ℝ :=
    fun {n} C t S B β x A τ s =>
      let U := presentSet S B τ β s
      let D := S.filter (fun g => τ g ≤ invE ∧ g ∈ C U \ C (insert x U))
      moveDerivBranch C t S B β x A D τ s

  have h_moveDeriv_meas : ∀ {n : ℕ} (C : Finset (Fin n) → Finset (Fin n)) {t : ℝ},
      invE ≤ t →
      ∀ (S B : Finset (Fin n)) (β : Fin n → ℝ) (x : Fin n) (A : Finset (Fin n)),
      Measurable (fun p : ℝ × (Fin n → ℝ) => moveDeriv C t S B β x A p.2 p.1) := by
    intro n C t ht_low S B β x A
    let β_upd : ℝ × (Fin n → ℝ) → (Fin n → ℝ) := fun p => Function.update β x p.1
    have h_meas_βupd : Measurable β_upd := by
      rw [measurable_pi_iff]
      intro z
      by_cases hzx : z = x
      · rw [hzx]; simpa [β_upd] using measurable_fst
      · simp [β_upd, Function.update_of_ne hzx]
    obtain ⟨h_meas_θ, h_meas_φ⟩ := h_meas_prod C ht_low S (insert x B) A Prod.snd β_upd
      measurable_snd h_meas_βupd
    have h_meas_branch : ∀ F₀ : Finset (Fin n),
        Measurable (fun p : ℝ × (Fin n → ℝ) => moveDerivBranch C t S B β x A F₀ p.2 p.1) := by
      intro F₀
      dsimp only [moveDerivBranch]
      split_ifs with h0 h1 hfA
      · exact h_meas_φ
      · exact h_meas_φ.add
          ((Finset.measurable_prod (A.erase _) (fun g _ => h_meas_θ g)).mul
            (Finset.measurable_prod (S \ A) (fun g _ => measurable_const.sub (h_meas_θ g))))
      · exact ((Real.measurable_log.comp (measurable_const.mul measurable_fst)).neg).mul
          ((Finset.measurable_prod A (fun g _ => h_meas_θ g)).mul
            (Finset.measurable_prod (S \ insert _ A) (fun g _ => measurable_const.sub (h_meas_θ g))))
      · exact measurable_const
    let D_fn : ℝ × (Fin n → ℝ) → Finset (Fin n) := fun p =>
      S.filter (fun g => p.2 g ≤ invE ∧
        g ∈ C (presentSet S B p.2 β p.1) \ C (insert x (presentSet S B p.2 β p.1)))
    have h_meas_memD : ∀ g : Fin n, MeasurableSet {p : ℝ × (Fin n → ℝ) | g ∈ D_fn p} := by
      intro g
      let dispSets := (Finset.univ : Finset (Finset (Fin n))).filter
        (fun U => g ∈ C U \ C (insert x U))
      have heq : {p : ℝ × (Fin n → ℝ) | g ∈ D_fn p} =
          (if g ∈ S then {p | p.2 g ≤ invE} else ∅) ∩
            ⋃ U ∈ dispSets, {p | presentSet S B p.2 β p.1 = U} := by
        ext p
        simp [D_fn, dispSets]
        tauto
      rw [heq]
      refine MeasurableSet.inter ?_ ?_
      · split_ifs
        · exact measurableSet_le ((measurable_pi_apply g).comp measurable_snd) measurable_const
        · exact MeasurableSet.empty
      · exact Finset.measurableSet_biUnion _ (fun U _ =>
          h_meas_pres_eq S B Prod.snd (fun _ => β) Prod.fst
            measurable_snd measurable_const measurable_fst U)
    have h_meas_eqD : ∀ F₀ : Finset (Fin n), MeasurableSet {p : ℝ × (Fin n → ℝ) | D_fn p = F₀} := by
      intro F₀
      have heq : {p : ℝ × (Fin n → ℝ) | D_fn p = F₀} =
          ⋂ g : Fin n,
            if g ∈ F₀ then {p | g ∈ D_fn p} else {p | g ∈ D_fn p}ᶜ := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
        refine ⟨fun h g => by subst h; split_ifs with hg <;> simp [hg], fun hgF => ?_⟩
        ext g
        specialize hgF g
        by_cases hg : g ∈ F₀ <;> simp [hg] at hgF ⊢ <;> exact hgF
      rw [heq]
      refine MeasurableSet.iInter (fun g => ?_)
      split_ifs
      · exact h_meas_memD g
      · exact (h_meas_memD g).compl
    have h_sum_eq : (fun p : ℝ × (Fin n → ℝ) => moveDeriv C t S B β x A p.2 p.1) =
        fun p => ∑ F₀ ∈ (Finset.univ : Finset (Finset (Fin n))),
          if D_fn p = F₀ then moveDerivBranch C t S B β x A F₀ p.2 p.1 else 0 := by
      ext p
      rw [Finset.sum_ite_eq (Finset.univ : Finset (Finset (Fin n))) (D_fn p)
        (fun F₀ => moveDerivBranch C t S B β x A F₀ p.2 p.1),
        if_pos (Finset.mem_univ (D_fn p))]
    rw [h_sum_eq]
    exact Finset.measurable_sum _ (fun F₀ _ =>
      Measurable.ite (h_meas_eqD F₀) (h_meas_branch F₀) measurable_const)

  have h_moveDeriv_bdd : ∀ {n : ℕ} (C : Finset (Fin n) → Finset (Fin n)) {t : ℝ},
      invE ≤ t → t ≤ 1 →
      ∀ (S B : Finset (Fin n)) (β : Fin n → ℝ) (x : Fin n) (A : Finset (Fin n))
        (τ : Fin n → ℝ) (s : ℝ),
      s ∈ Set.Icc invE t →
      |moveDeriv C t S B β x A τ s| ≤ 2 := by
    intro n C t ht_low ht_high S B β x A τ s hs
    dsimp only [moveDeriv, moveDerivBranch]
    have hφ_b := h_prod_bounds C ht_low ht_high S (insert x B) τ (Function.update β x s) A
    have h_sub_prod : ∀ P Q : Finset (Fin n),
        0 ≤ (∏ g ∈ P, retentionProb C t S (insert x B) τ (Function.update β x s) g) *
          (∏ g ∈ Q, (1 - retentionProb C t S (insert x B) τ (Function.update β x s) g)) ∧
        (∏ g ∈ P, retentionProb C t S (insert x B) τ (Function.update β x s) g) *
          (∏ g ∈ Q, (1 - retentionProb C t S (insert x B) τ (Function.update β x s) g)) ≤ 1 := by
      intro P Q
      let β' := Function.update β x s
      have h1_nn := Finset.prod_nonneg
        (s := P) (fun g _ => (h_ret_bounds C ht_low ht_high S (insert x B) τ β' g).1)
      have h1_le := Finset.prod_le_one
        (s := P) (fun g _ => (h_ret_bounds C ht_low ht_high S (insert x B) τ β' g).1)
        (fun g _ => (h_ret_bounds C ht_low ht_high S (insert x B) τ β' g).2)
      have h2_nn := Finset.prod_nonneg
        (s := Q) (fun g _ => sub_nonneg.mpr (h_ret_bounds C ht_low ht_high S (insert x B) τ β' g).2)
      have h2_le := Finset.prod_le_one
        (s := Q) (fun g _ => sub_nonneg.mpr (h_ret_bounds C ht_low ht_high S (insert x B) τ β' g).2)
        (fun g _ => sub_le_self 1 (h_ret_bounds C ht_low ht_high S (insert x B) τ β' g).1)
      exact ⟨mul_nonneg h1_nn h2_nn, mul_le_one₀ h1_le h2_nn h2_le⟩
    split_ifs with h0 h1 hfA
    · rw [abs_of_nonneg hφ_b.1]; linarith [hφ_b.2]
    · obtain ⟨hc0, hc1⟩ := h_sub_prod (A.erase _) (S \ A)
      rw [abs_of_nonneg (by linarith [hφ_b.1, hc0])]
      linarith [hφ_b.2, hc1]
    · obtain ⟨hc0, hc1⟩ := h_sub_prod A (S \ insert _ A)
      have hs_pos : 0 < s := h_invE_pos.trans_le hs.1
      have hlog_lo : 0 ≤ Real.log (Real.exp 1 * s) := by
        refine Real.log_nonneg ?_
        calc (1 : ℝ) = Real.exp 1 * invE := h_exp_invE.symm
          _ ≤ Real.exp 1 * s := mul_le_mul_of_nonneg_left hs.1 (Real.exp_pos 1).le
      have hlog_hi : Real.log (Real.exp 1 * s) ≤ 1 := by
        calc Real.log (Real.exp 1 * s)
            ≤ Real.log (Real.exp 1) := by
              refine Real.log_le_log (mul_pos (Real.exp_pos 1) hs_pos) ?_
              calc Real.exp 1 * s ≤ Real.exp 1 * 1 :=
                  mul_le_mul_of_nonneg_left (hs.2.trans ht_high) (Real.exp_pos 1).le
                _ = Real.exp 1 := mul_one _
          _ = 1 := Real.log_exp 1
      rw [abs_mul, abs_neg, abs_of_nonneg hlog_lo, abs_of_nonneg hc0]
      have hle1 : Real.log (Real.exp 1 * s) * _ ≤ 1 := mul_le_one₀ hlog_hi hc0 hc1
      linarith
    · norm_num

  have h_moveDeriv_hasDeriv : ∀ {n : ℕ} (C : Finset (Fin n) → Finset (Fin n)) {t τ_tilde : ℝ}
      (S B : Finset (Fin n)) (β : Fin n → ℝ) (x : Fin n) (A : Finset (Fin n)) (τ : Fin n → ℝ),
      HasPersistence C → HasSingleDisplacement C →
      invE < τ_tilde → τ_tilde < t →
      x ∉ S ∪ B → A ⊆ S →
      (∀ g ∈ S, τ g ≠ τ_tilde) → (∀ b ∈ B, β b ≠ τ_tilde) →
      HasDerivAt (fun u => u * retainProd C t S (insert x B) τ (Function.update β x u) A)
        (moveDeriv C t S B β x A τ τ_tilde) τ_tilde := by
    intro n C t τ_tilde S B β x A τ hP hSD h_low h_high hxSB hA hτ_ne hβ_ne
    let U := presentSet S B τ β τ_tilde
    let φ := fun u => retainProd C t S (insert x B) τ (Function.update β x u) A
    have ht_low : invE ≤ t := (h_low.trans h_high).le
    have hτ_pos : 0 < τ_tilde := h_invE_pos.trans h_low
    have hxB : x ∉ B := fun hb => hxSB (Finset.mem_union_right S hb)
    have hxU : x ∉ U := by
      intro hx_in
      simp only [U, presentSet, Finset.mem_union, Finset.mem_filter] at hx_in
      rcases hx_in with ⟨hxS, _⟩ | ⟨hxB', _⟩
      · exact hxSB (Finset.mem_union_left B hxS)
      · exact hxB hxB'
    let F_gap : Finset ℝ := insert (τ_tilde - invE) (insert (t - τ_tilde)
      (S.image (fun g => |τ g - τ_tilde|) ∪ B.image (fun b => |β b - τ_tilde|)))
    have hF_ne : F_gap.Nonempty := Finset.insert_nonempty _ _
    let δ : ℝ := F_gap.inf' hF_ne id
    have hδ_pos : 0 < δ := by
      rw [Finset.lt_inf'_iff]
      intro d hd
      dsimp only [id]
      simp only [F_gap, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hd
      rcases hd with rfl | rfl | ⟨⟨g, hgS, rfl⟩ | ⟨b, hbB, rfl⟩⟩
      · linarith
      · linarith
      · exact abs_pos.mpr (sub_ne_zero.mpr (hτ_ne g hgS))
      · exact abs_pos.mpr (sub_ne_zero.mpr (hβ_ne b hbB))
    have hδ_le_lo : δ ≤ τ_tilde - invE :=
      Finset.inf'_le id (Finset.mem_insert_self _ _)
    have hδ_le_hi : δ ≤ t - τ_tilde :=
      Finset.inf'_le id (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    let I_open : Set ℝ := Set.Ioo (τ_tilde - δ) (τ_tilde + δ)
    have hτ_mem_I : τ_tilde ∈ I_open := ⟨by linarith, by linarith⟩
    have hI_nhds : I_open ∈ nhds τ_tilde := Ioo_mem_nhds (by linarith) (by linarith)
    have hI_sub : ∀ v ∈ I_open, invE < v ∧ v < t := fun v hv =>
      ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hU_const : ∀ v ∈ I_open, presentSet S B τ β v = U := by
      intro v hv
      unfold U presentSet
      congr 1
      · ext g
        simp only [Finset.mem_filter]
        refine ⟨fun ⟨hgS, hle⟩ => ⟨hgS, ?_⟩, fun ⟨hgS, hle⟩ => ⟨hgS, ?_⟩⟩
        · have hδg : δ ≤ |τ g - τ_tilde| := Finset.inf'_le id
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hgS))))
          by_contra hgt
          push_neg at hgt
          rw [abs_of_pos (sub_pos.mpr hgt)] at hδg
          linarith [hv.2]
        · have hδg : δ ≤ |τ g - τ_tilde| := Finset.inf'_le id
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hgS))))
          have hlt : τ g < τ_tilde := lt_of_le_of_ne hle (hτ_ne g hgS)
          rw [abs_of_neg (sub_neg.mpr hlt)] at hδg
          linarith [hv.1]
      · ext b
        simp only [Finset.mem_filter]
        refine ⟨fun ⟨hbB, hle⟩ => ⟨hbB, ?_⟩, fun ⟨hbB, hle⟩ => ⟨hbB, ?_⟩⟩
        · have hδb : δ ≤ |β b - τ_tilde| := Finset.inf'_le id
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hbB))))
          by_contra hgt
          push_neg at hgt
          rw [abs_of_pos (sub_pos.mpr hgt)] at hδb
          linarith [hv.2]
        · have hδb : δ ≤ |β b - τ_tilde| := Finset.inf'_le id
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hbB))))
          have hlt : β b < τ_tilde := lt_of_le_of_ne hle (hβ_ne b hbB)
          rw [abs_of_neg (sub_neg.mpr hlt)] at hδb
          linarith [hv.1]
    let W : ℝ → ℝ → Finset (Fin n) :=
      fun u v => presentSet S (insert x B) τ (Function.update β x u) v
    have hW_out : ∀ u ∈ I_open, ∀ v, v ∉ I_open → W u v = W τ_tilde v := by
      intro u hu v hv_not
      dsimp only [W]
      rw [h_pres_update S B hxB τ β u v, h_pres_update S B hxB τ β τ_tilde v]
      have h_iff : u ≤ v ↔ τ_tilde ≤ v := by
        simp only [I_open, Set.mem_Ioo, not_and_or, not_lt] at hv_not
        rcases hv_not with hle | hge
        · constructor <;> intro h <;> linarith [hu.1, hu.2]
        · constructor <;> intro h <;> linarith [hu.1, hu.2]
      by_cases h : τ_tilde ≤ v
      · rw [if_pos (h_iff.mpr h), if_pos h]
      · rw [if_neg (mt h_iff.mp h), if_neg h]
    let θ : ℝ → Fin n → ℝ :=
      fun u g => retentionProb C t S (insert x B) τ (Function.update β x u) g
    let D : Finset (Fin n) :=
      S.filter (fun g => τ g ≤ invE ∧ g ∈ C U \ C (insert x U))
    have hθ_notD : ∀ g ∈ S, g ∉ D → ∀ u ∈ I_open, θ u g = θ τ_tilde g := by
      intro g hgS hgD u hu
      dsimp only [θ, retentionProb]
      split_ifs with hτ_early
      · congr 1
        congr 1
        have hgU : g ∈ U := by
          simp [U, presentSet, hgS, (hτ_early.trans_lt h_low).le]
        have hg_not_disp : g ∉ C U \ C (insert x U) := by
          intro hdisp
          exact hgD (Finset.mem_filter.mpr ⟨hgS, hτ_early, hdisp⟩)
        have h_pers_x : g ∈ C (insert x U) → g ∈ C U := fun hgx =>
          hP U (insert x U) (Finset.subset_insert x U) (Finset.mem_inter.mpr ⟨hgx, hgU⟩)
        unfold deathTime
        congr 1
        ext v
        by_cases hvI : v ∈ I_open
        · obtain ⟨hv_lo, hv_hi⟩ := hI_sub v hvI
          have hv_ne_t : v ≠ t := hv_hi.ne
          have hWu : W u v = if u ≤ v then insert x U else U := by
            dsimp only [W]
            rw [h_pres_update S B hxB τ β u v, hU_const v hvI]
          have hWt : W τ_tilde v = if τ_tilde ≤ v then insert x U else U := by
            dsimp only [W]
            rw [h_pres_update S B hxB τ β τ_tilde v, hU_const v hvI]
          by_cases hgCU : g ∈ C U
          · have hgCxU : g ∈ C (insert x U) := by
              by_contra hnot
              exact hg_not_disp (Finset.mem_sdiff.mpr ⟨hgCU, hnot⟩)
            have h1 : g ∈ C (W u v) := by rw [hWu]; split_ifs <;> assumption
            have h2 : g ∈ C (W τ_tilde v) := by rw [hWt]; split_ifs <;> assumption
            simp [W, hv_ne_t, h1, h2]
          · have hg_not_CxU : g ∉ C (insert x U) := mt h_pers_x hgCU
            have h1 : g ∉ C (W u v) := by rw [hWu]; split_ifs <;> assumption
            have h2 : g ∉ C (W τ_tilde v) := by rw [hWt]; split_ifs <;> assumption
            simp [W, hv_lo.le, hv_hi.le, h1, h2]
        · have hW_eq := hW_out u hu v hvI
          simp only [Set.mem_union, Set.mem_setOf_eq]
          rw [show presentSet S (insert x B) τ (Function.update β x u) v = W u v from rfl,
            show presentSet S (insert x B) τ (Function.update β x τ_tilde) v = W τ_tilde v from rfl,
            hW_eq]
      · rfl
    have hθ_inD : ∀ f ∈ D, ∀ u ∈ I_open, θ u f = Real.log (Real.exp 1 * u) := by
      intro f hfD u hu
      obtain ⟨hfS, hf_early, hf_disp⟩ := Finset.mem_filter.mp hfD
      obtain ⟨hfCU, hf_notCxU⟩ := Finset.mem_sdiff.mp hf_disp
      obtain ⟨hu_lo, hu_hi⟩ := hI_sub u hu
      dsimp only [θ, retentionProb]
      rw [if_pos hf_early]
      suffices h_dt_eq : deathTime C t S (insert x B) τ (Function.update β x u) f = u by
        rw [h_dt_eq]
      let Eu : Set ℝ := {v : ℝ | invE ≤ v ∧ v ≤ t ∧ f ∉ C (W u v)} ∪ {t}
      have hBdd : BddBelow Eu := ⟨invE, by
        rintro v (hv | hv)
        · exact hv.1
        · rw [Set.mem_singleton_iff.mp hv]; exact ht_low⟩
      apply le_antisymm
      · have hWuu : W u u = insert x U := by
          dsimp only [W]
          rw [h_pres_update S B hxB τ β u u, if_pos le_rfl, hU_const u hu]
        have hu_mem : u ∈ Eu :=
          Set.mem_union_left _ ⟨hu_lo.le, hu_hi.le, by rwa [hWuu]⟩
        exact csInf_le hBdd hu_mem
      · refine le_csInf ⟨t, Set.mem_union_right _ rfl⟩ (fun v hv => ?_)
        rcases hv with ⟨hv_lo, _, hv_notC⟩ | hv_eq
        · by_contra hlt
          push_neg at hlt
          have hWuv : W u v = presentSet S B τ β v := by
            dsimp only [W]
            rw [h_pres_update S B hxB τ β u v, if_neg (not_le_of_gt hlt)]
          have hsub : presentSet S B τ β v ⊆ U := by
            rw [← hU_const u hu]
            exact h_pres_mono S B τ β hlt.le
          have hf_mem_v : f ∈ presentSet S B τ β v := by
            simp [presentSet, hfS, hf_early.trans hv_lo]
          have hfC : f ∈ C (presentSet S B τ β v) :=
            hP (presentSet S B τ β v) U hsub (Finset.mem_inter.mpr ⟨hfCU, hf_mem_v⟩)
          rw [← hWuv] at hfC
          exact hv_notC hfC
        · rw [Set.mem_singleton_iff.mp hv_eq]
          exact hu_hi.le
    have hD_card : D.card ≤ 1 := by
      have hD_sub : D ⊆ C U \ C (insert x U) := fun g hg => (Finset.mem_filter.mp hg).2.2
      exact (Finset.card_le_card hD_sub).trans (hSD U x hxU)
    have h_log_deriv : HasDerivAt (fun u : ℝ => Real.log (Real.exp 1 * u)) (τ_tilde⁻¹) τ_tilde := by
      have h1 : HasDerivAt (fun u : ℝ => Real.exp 1 * u) (Real.exp 1 * 1) τ_tilde :=
        (hasDerivAt_id τ_tilde).const_mul (Real.exp 1)
      have hexp_ne : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
      have h2 := (Real.hasDerivAt_log (mul_ne_zero hexp_ne hτ_pos.ne')).comp τ_tilde h1
      have heq_d : (Real.exp 1 * τ_tilde)⁻¹ * (Real.exp 1 * 1) = τ_tilde⁻¹ := by
        field_simp
      rw [heq_d] at h2
      exact h2
    change HasDerivAt (fun u => u * φ u) (moveDerivBranch C t S B β x A D τ τ_tilde) τ_tilde
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hD_card with hD0 | hD1
    · have hD_emp : D = ∅ := Finset.card_eq_zero.mp hD0
      have hφ_eq : φ =ᶠ[nhds τ_tilde] (fun _ => φ τ_tilde) := by
        refine Filter.eventually_of_mem hI_nhds (fun u hu => ?_)
        dsimp only [φ, retainProd]
        rw [if_pos hA, if_pos hA]
        congr 1
        · refine Finset.prod_congr rfl (fun g hgA => hθ_notD g (hA hgA) ?_ u hu)
          rw [hD_emp]; exact Finset.notMem_empty g
        · refine Finset.prod_congr rfl (fun g hgSA => ?_)
          congr 1
          exact hθ_notD g (Finset.mem_sdiff.mp hgSA).1
            (by rw [hD_emp]; exact Finset.notMem_empty g) u hu
      have hd_φ : HasDerivAt φ 0 τ_tilde :=
        (hasDerivAt_const τ_tilde (φ τ_tilde)).congr_of_eventuallyEq hφ_eq
      have hd_uφ : HasDerivAt (fun u => u * φ u) (φ τ_tilde) τ_tilde := by
        simpa using (hasDerivAt_id τ_tilde).mul hd_φ
      dsimp only [moveDerivBranch]
      rw [if_pos hD0]
      exact hd_uφ
    · obtain ⟨f₀, hf₀_eq⟩ := Finset.card_eq_one.mp hD1
      have hf_min_eq : D.min' (Finset.card_pos.mp (by omega)) = f₀ := by
        have hm : D.min' (Finset.card_pos.mp (by omega)) ∈ D :=
          Finset.min'_mem D (Finset.card_pos.mp (by omega))
        generalize D.min' (Finset.card_pos.mp (by omega)) = m at hm ⊢
        rwa [hf₀_eq, Finset.mem_singleton] at hm
      have hf₀D : f₀ ∈ D := by rw [hf₀_eq]; exact Finset.mem_singleton_self f₀
      obtain ⟨hfS, _, _⟩ := Finset.mem_filter.mp hf₀D
      dsimp only [moveDerivBranch]
      rw [if_neg (by omega : ¬ D.card = 0), dif_pos hD1, hf_min_eq]
      by_cases hfA : f₀ ∈ A
      · rw [if_pos hfA]
        let c : ℝ := (∏ g ∈ A.erase f₀, θ τ_tilde g) * (∏ g ∈ S \ A, (1 - θ τ_tilde g))
        have hφ_on_I : ∀ u ∈ I_open, φ u = Real.log (Real.exp 1 * u) * c := by
          intro u hu
          dsimp only [φ, retainProd, c]
          rw [if_pos hA, ← Finset.mul_prod_erase A _ hfA, mul_assoc]
          congr 1
          · exact hθ_inD f₀ hf₀D u hu
          · congr 1
            · refine Finset.prod_congr rfl (fun g hg => ?_)
              obtain ⟨hg_ne, hgA⟩ := Finset.mem_erase.mp hg
              exact hθ_notD g (hA hgA) (by rw [hf₀_eq, Finset.mem_singleton]; exact hg_ne) u hu
            · refine Finset.prod_congr rfl (fun g hgSA => ?_)
              obtain ⟨hgS, hg_notA⟩ := Finset.mem_sdiff.mp hgSA
              have hg_ne : g ≠ f₀ := fun heq => hg_notA (heq ▸ hfA)
              congr 1
              exact hθ_notD g hgS (by rw [hf₀_eq, Finset.mem_singleton]; exact hg_ne) u hu
        have hd_φ : HasDerivAt φ (τ_tilde⁻¹ * c) τ_tilde :=
          (h_log_deriv.mul_const c).congr_of_eventuallyEq
            (Filter.eventually_of_mem hI_nhds hφ_on_I)
        have hd_uφ : HasDerivAt (fun u => u * φ u) (φ τ_tilde + c) τ_tilde := by
          have hd := (hasDerivAt_id τ_tilde).mul hd_φ
          have heq_val : 1 * φ τ_tilde + id τ_tilde * (τ_tilde⁻¹ * c) = φ τ_tilde + c := by
            dsimp only [id]
            have := hτ_pos.ne'
            field_simp
          exact heq_val ▸ hd
        exact hd_uφ
      · rw [if_neg hfA]
        have hfSA : f₀ ∈ S \ A := Finset.mem_sdiff.mpr ⟨hfS, hfA⟩
        let c_no : ℝ := (∏ g ∈ A, θ τ_tilde g) * (∏ g ∈ S \ insert f₀ A, (1 - θ τ_tilde g))
        have hsdiff_erase : (S \ A).erase f₀ = S \ insert f₀ A := by
          ext g
          simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
          tauto
        have hφ_on_I : ∀ u ∈ I_open, φ u = (1 - Real.log (Real.exp 1 * u)) * c_no := by
          intro u hu
          dsimp only [φ, retainProd, c_no]
          rw [if_pos hA, ← Finset.mul_prod_erase (S \ A) _ hfSA, hsdiff_erase]
          have h1_eq : (∏ g ∈ A, θ u g) = ∏ g ∈ A, θ τ_tilde g := by
            refine Finset.prod_congr rfl (fun g hgA => ?_)
            have hg_ne : g ≠ f₀ := fun heq => hfA (heq ▸ hgA)
            exact hθ_notD g (hA hgA) (by rw [hf₀_eq, Finset.mem_singleton]; exact hg_ne) u hu
          have h2_eq : (∏ g ∈ S \ insert f₀ A, (1 - θ u g)) =
              ∏ g ∈ S \ insert f₀ A, (1 - θ τ_tilde g) := by
            refine Finset.prod_congr rfl (fun g hg => ?_)
            obtain ⟨hgS, hg_not⟩ := Finset.mem_sdiff.mp hg
            have hg_ne : g ≠ f₀ := fun heq => hg_not (heq ▸ Finset.mem_insert_self f₀ A)
            rw [hθ_notD g hgS (by rw [hf₀_eq, Finset.mem_singleton]; exact hg_ne) u hu]
          have hf_eq_u : θ u f₀ = Real.log (Real.exp 1 * u) := hθ_inD f₀ hf₀D u hu
          change (∏ g ∈ A, θ u g) * ((1 - θ u f₀) * ∏ g ∈ S \ insert f₀ A, (1 - θ u g)) =
            (1 - Real.log (Real.exp 1 * u)) *
              ((∏ g ∈ A, θ τ_tilde g) * ∏ g ∈ S \ insert f₀ A, (1 - θ τ_tilde g))
          rw [h1_eq, h2_eq, hf_eq_u]
          ring
        have hd_one_sub : HasDerivAt (fun u : ℝ => 1 - Real.log (Real.exp 1 * u))
            (-τ_tilde⁻¹) τ_tilde := by
          simpa using (hasDerivAt_const τ_tilde (1 : ℝ)).sub h_log_deriv
        have hd_φ : HasDerivAt φ (-τ_tilde⁻¹ * c_no) τ_tilde :=
          (hd_one_sub.mul_const c_no).congr_of_eventuallyEq
            (Filter.eventually_of_mem hI_nhds hφ_on_I)
        have hd_uφ : HasDerivAt (fun u => u * φ u)
            (-Real.log (Real.exp 1 * τ_tilde) * c_no) τ_tilde := by
          have hd := (hasDerivAt_id τ_tilde).mul hd_φ
          have hφ_at_t := hφ_on_I τ_tilde hτ_mem_I
          have heq_val : 1 * φ τ_tilde + id τ_tilde * (-τ_tilde⁻¹ * c_no) =
              -Real.log (Real.exp 1 * τ_tilde) * c_no := by
            dsimp only [id]
            have := hτ_pos.ne'
            rw [hφ_at_t]
            field_simp
            ring
          exact heq_val ▸ hd
        exact hd_uφ

  have h_ftc_fubini2 : ∀ {n : ℕ} (C : Finset (Fin n) → Finset (Fin n)) {t₀ t u₁ u₂ : ℝ}
      (S B : Finset (Fin n)) (β : Fin n → ℝ) (x : Fin n) (A : Finset (Fin n)),
      HasPersistence C → HasSingleDisplacement C →
      invE ≤ t₀ → t₀ ≤ t → t ≤ 1 →
      x ∉ S ∪ B → A ⊆ S →
      u₁ ∈ Set.Icc invE t₀ → u₂ ∈ Set.Icc invE t₀ → u₁ < u₂ →
      (∀ s ∈ Set.Ioo u₁ u₂, 0 ≤ ∫ τ, moveDeriv C t S B β x A τ s ∂(unifCubeMeasure n t₀)) →
      u₁ * genMovingProb2 C t₀ t S B β x A u₁ ≤ u₂ * genMovingProb2 C t₀ t S B β x A u₂ := by
    intro n C t₀ t u₁ u₂ S B β x A hP hSD ht₀_low ht₀_t ht_high hxSB hA hu₁ hu₂ hu_lt h_nonneg
    have ht_low : invE ≤ t := ht₀_low.trans ht₀_t
    have ht₀_pos : 0 < t₀ := h_invE_pos.trans_le ht₀_low
    let μ₁ : Measure ℝ := (ENNReal.ofReal t₀)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) t₀)
    haveI : IsProbabilityMeasure μ₁ := h_unif1D_prob ht₀_pos
    let μ : Measure (Fin n → ℝ) := unifCubeMeasure n t₀
    haveI : IsProbabilityMeasure μ := by dsimp only [μ, unifCubeMeasure]; infer_instance
    have h_phi_int : ∀ u ∈ Set.Icc invE t₀,
        Integrable (fun τ => u * retainProd C t S (insert x B) τ (Function.update β x u) A) μ := by
      intro u hu
      have hm : Measurable (fun τ => u * retainProd C t S (insert x B) τ (Function.update β x u) A) :=
        measurable_const.mul (h_meas_prod C ht_low S (insert x B) A id
          (fun _ => Function.update β x u) measurable_id measurable_const).2
      refine Integrable.of_mem_Icc 0 1 hm.aemeasurable (Filter.Eventually.of_forall (fun τ => ?_))
      have hu_nn : 0 ≤ u := h_invE_pos.le.trans hu.1
      have hu_one : u ≤ 1 := (hu.2.trans ht₀_t).trans ht_high
      obtain ⟨hp0, hp1⟩ := h_prod_bounds C ht_low ht_high S (insert x B) τ (Function.update β x u) A
      exact ⟨mul_nonneg hu_nn hp0, mul_le_one₀ hu_one hp0 hp1⟩
    have h_diff_eq : u₂ * genMovingProb2 C t₀ t S B β x A u₂ - u₁ * genMovingProb2 C t₀ t S B β x A u₁ =
        ∫ τ, (∫ s in u₁..u₂, moveDeriv C t S B β x A τ s) ∂μ := by
      dsimp only [genMovingProb2, genSurvivalLaw2]
      change u₂ * (∫ τ, retainProd C t S (insert x B) τ (Function.update β x u₂) A ∂μ) -
          u₁ * (∫ τ, retainProd C t S (insert x B) τ (Function.update β x u₁) A ∂μ) = _
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_sub (h_phi_int u₂ hu₂) (h_phi_int u₁ hu₁)]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun τ => ?_))
      let F_τ : ℝ → ℝ := fun u => u * retainProd C t S (insert x B) τ (Function.update β x u) A
      let f'_τ : ℝ → ℝ := fun s => moveDeriv C t S B β x A τ s
      let E_bad : Finset ℝ := S.image τ ∪ B.image β
      have hI_sub : Set.Icc u₁ u₂ ⊆ Set.Icc invE t :=
        fun s hs => ⟨hu₁.1.trans hs.1, (hs.2.trans hu₂.2).trans ht₀_t⟩
      have hF_cont : ContinuousOn F_τ (Set.Icc u₁ u₂) :=
        (h_lip_retain C S B x A τ β hP ht_low ht_high hxSB hA).2.mono hI_sub
      have hf'_meas : Measurable f'_τ :=
        (h_moveDeriv_meas C ht_low S B β x A).comp (measurable_id.prodMk measurable_const)
      have hf'_int : IntervalIntegrable f'_τ volume u₁ u₂ := by
        have h_uIcc : IntegrableOn f'_τ (Set.uIcc u₁ u₂) volume := by
          rw [Set.uIcc_of_le hu_lt.le]
          refine Integrable.of_mem_Icc (-2) 2 hf'_meas.aemeasurable ?_
          rw [ae_restrict_iff' measurableSet_Icc]
          exact Filter.Eventually.of_forall (fun s hs =>
            abs_le.mp (h_moveDeriv_bdd C ht_low ht_high S B β x A τ s (hI_sub hs)))
        exact h_uIcc.intervalIntegrable
      have h_deriv : ∀ s ∈ Set.Ioo u₁ u₂ \ (E_bad : Set ℝ), HasDerivAt F_τ (f'_τ s) s := by
        intro s ⟨hs_ioo, hs_notE⟩
        have hs_lo : invE < s := lt_of_le_of_lt hu₁.1 hs_ioo.1
        have hs_hi : s < t := lt_of_lt_of_le hs_ioo.2 (hu₂.2.trans ht₀_t)
        have hτ_ne : ∀ g ∈ S, τ g ≠ s := by
          intro g hgS heq
          apply hs_notE
          rw [Finset.coe_union, Set.mem_union]
          exact Or.inl (Finset.mem_coe.mpr (heq ▸ Finset.mem_image_of_mem τ hgS))
        have hβ_ne : ∀ b ∈ B, β b ≠ s := by
          intro b hbB heq
          apply hs_notE
          rw [Finset.coe_union, Set.mem_union]
          exact Or.inr (Finset.mem_coe.mpr (heq ▸ Finset.mem_image_of_mem β hbB))
        exact h_moveDeriv_hasDeriv C S B β x A τ hP hSD hs_lo hs_hi hxSB hA hτ_ne hβ_ne
      exact (MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le F_τ f'_τ hu_lt.le
        E_bad.countable_toSet hF_cont h_deriv hf'_int).symm
    suffices h_ge : 0 ≤ u₂ * genMovingProb2 C t₀ t S B β x A u₂ - u₁ * genMovingProb2 C t₀ t S B β x A u₁ by
      linarith
    rw [h_diff_eq]
    let G : ℝ → (Fin n → ℝ) → ℝ := fun s τ => moveDeriv C t S B β x A τ s
    let μ_I : Measure ℝ := volume.restrict (Set.uIoc u₁ u₂)
    haveI : IsFiniteMeasure μ_I := by
      dsimp only [μ_I]
      rw [Set.uIoc_of_le hu_lt.le]
      infer_instance
    have h_int_prod : Integrable (Function.uncurry G) (μ_I.prod μ) := by
      refine Integrable.of_mem_Icc (-2) 2 (h_moveDeriv_meas C ht_low S B β x A).aemeasurable ?_
      have h_ae_I : ∀ᵐ s ∂μ_I, s ∈ Set.Icc invE t := by
        dsimp only [μ_I]
        rw [Set.uIoc_of_le hu_lt.le, ae_restrict_iff' measurableSet_Ioc]
        exact Filter.Eventually.of_forall (fun s hs => ⟨hu₁.1.trans hs.1.le, (hs.2.trans hu₂.2).trans ht₀_t⟩)
      have h_ae_prod : ∀ᵐ p ∂(μ_I.prod μ), p.1 ∈ Set.Icc invE t :=
        Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst h_ae_I
      filter_upwards [h_ae_prod] with p hp
      exact abs_le.mp (h_moveDeriv_bdd C ht_low ht_high S B β x A p.2 p.1 hp)
    have h_swap := intervalIntegral_integral_swap h_int_prod
    change 0 ≤ ∫ τ, (∫ s in u₁..u₂, G s τ) ∂μ
    rw [← h_swap, intervalIntegral.integral_of_le hu_lt.le]
    refine integral_nonneg_of_ae ?_
    change ∀ᵐ s ∂(volume.restrict (Set.Ioc u₁ u₂)), 0 ≤ ∫ τ, G s τ ∂μ
    rw [ae_restrict_iff' measurableSet_Ioc]
    have h_ne_u₂ : ∀ᵐ s ∂volume, s ≠ u₂ := by rw [ae_iff]; simp
    filter_upwards [h_ne_u₂] with s hs_ne hs_Ioc
    exact h_nonneg s ⟨hs_Ioc.1, lt_of_le_of_ne hs_Ioc.2 hs_ne⟩

  clear h_meas_pres_eq h_pres_update h_pres_mono h_moveDeriv_hasDeriv

  have h_rescale : ∀ (n : ℕ) {τ_tilde t : ℝ}, 0 < τ_tilde → τ_tilde < t →
      ∀ (Q : Finset (Fin n)) (H : (Fin n → ℝ) → ℝ),
      Measurable H → (∀ τ, |H τ| ≤ 2) →
      let ν := fun r => (ENNReal.ofReal r)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) r)
      let μ_mix := Measure.pi (fun i : Fin n => if i ∈ Q then ν τ_tilde else ν t)
      (∫ τ, (∏ g ∈ Q, if τ g ≤ τ_tilde then (1 : ℝ) else 0) * H τ ∂(unifCubeMeasure n t)) =
        (τ_tilde / t) ^ Q.card * ∫ τ, H τ ∂μ_mix := by
    intro n τ_tilde t h0 hlt Q H hH_meas hH_bdd
    let ν := fun r => (ENNReal.ofReal r)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) r)
    let μ_mix := fun P : Finset (Fin n) => Measure.pi (fun i : Fin n => if i ∈ P then ν τ_tilde else ν t)
    have ht_pos : 0 < t := h0.trans hlt
    haveI : IsProbabilityMeasure (ν τ_tilde) := h_unif1D_prob h0
    haveI : IsProbabilityMeasure (ν t) := h_unif1D_prob ht_pos
    have h_1d : ∀ (h : ℝ → ℝ),
        (∫ u, (if u ≤ τ_tilde then h u else 0) ∂(ν t)) =
          (τ_tilde / t) * ∫ u, h u ∂(ν τ_tilde) := by
      intro h
      have h_ind : (fun u => if u ≤ τ_tilde then h u else 0) = (Set.Iic τ_tilde).indicator h := by
        ext u; by_cases hu : u ≤ τ_tilde <;> simp [hu]
      have h_inter : Set.Iic τ_tilde ∩ Set.Icc (0 : ℝ) t = Set.Icc (0 : ℝ) τ_tilde := by
        ext u; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
        exact ⟨fun ⟨h1, h2, _⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, h2.trans hlt.le⟩⟩
      rw [h_ind, integral_smul_measure, integral_indicator measurableSet_Iic,
        Measure.restrict_restrict measurableSet_Iic, h_inter, integral_smul_measure,
        smul_eq_mul, smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_inv,
        ENNReal.toReal_ofReal ht_pos.le, ENNReal.toReal_ofReal h0.le]
      have h_ne : τ_tilde ≠ 0 := h0.ne'
      have ht_ne : t ≠ 0 := ht_pos.ne'
      field_simp
    have h_step : ∀ (P : Finset (Fin n)) (i₀ : Fin n), i₀ ∉ P →
        ∀ (G : (Fin n → ℝ) → ℝ), Measurable G → (∀ τ, |G τ| ≤ 2) →
        (∫ τ, (if τ i₀ ≤ τ_tilde then (1 : ℝ) else 0) * G τ ∂(μ_mix P)) =
          (τ_tilde / t) * ∫ τ, G τ ∂(μ_mix (insert i₀ P)) := by
      intro P i₀ hi₀ G hG_meas hG_bdd
      obtain ⟨pred, hpred⟩ : ∃ pred : Fin n → Prop, ∀ i, pred i ↔ i = i₀ :=
        ⟨fun i => i = i₀, fun _ => Iff.rfl⟩
      let i₀_sub : {i : Fin n // pred i} := ⟨i₀, (hpred i₀).mpr rfl⟩
      let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) pred
      let m₁ : {i : Fin n // pred i} → Measure ℝ :=
        fun i => if i.1 ∈ P then ν τ_tilde else ν t
      let m₂ : {i : Fin n // pred i} → Measure ℝ :=
        fun i => if i.1 ∈ insert i₀ P then ν τ_tilde else ν t
      let m_out : {i : Fin n // ¬ pred i} → Measure ℝ :=
        fun i => if i.1 ∈ P then ν τ_tilde else ν t
      have hm₁_eq : m₁ = fun _ => ν t := by
        funext ⟨i, hi⟩; dsimp only [m₁]; rw [(hpred i).mp hi]; simp [hi₀]
      have hm₂_eq : m₂ = fun _ => ν τ_tilde := by
        funext ⟨i, hi⟩; dsimp only [m₂]; rw [(hpred i).mp hi]; simp
      have hm_out_eq : (fun i : {i : Fin n // ¬ pred i} => if i.1 ∈ insert i₀ P then ν τ_tilde else ν t) = m_out := by
        funext ⟨i, hi⟩
        have hne : i ≠ i₀ := mt (hpred i).mpr hi
        simp [m_out, hne]
      haveI : IsProbabilityMeasure (Measure.pi m_out) := by
        haveI : ∀ i : {i : Fin n // ¬ pred i}, IsProbabilityMeasure (m_out i) := by
          intro i; dsimp only [m_out]; split_ifs <;> infer_instance
        infer_instance
      have h_mp₁ : MeasurePreserving e.symm ((Measure.pi (fun _ : {i // pred i} => ν t)).prod (Measure.pi m_out)) (μ_mix P) := by
        have h := (measurePreserving_piEquivPiSubtypeProd (fun i : Fin n => if i ∈ P then ν τ_tilde else ν t) pred).symm e
        simpa only [μ_mix, m₁, m_out, hm₁_eq] using h
      have h_mp₂ : MeasurePreserving e.symm ((Measure.pi (fun _ : {i // pred i} => ν τ_tilde)).prod (Measure.pi m_out)) (μ_mix (insert i₀ P)) := by
        have h := (measurePreserving_piEquivPiSubtypeProd (fun i : Fin n => if i ∈ insert i₀ P then ν τ_tilde else ν t) pred).symm e
        simpa only [μ_mix, m₂, hm₂_eq, hm_out_eq] using h
      have h_symm_eq : ∀ (x : {i // pred i} → ℝ) (z : {i // ¬ pred i} → ℝ),
          e.symm (x, z) = Function.update (e.symm (0, z)) i₀ (x i₀_sub) := by
        intro x z; ext j
        by_cases hj : j = i₀
        · rw [hj]
          have h1 : e.symm (x, z) i₀ = x i₀_sub :=
            (Equiv.piEquivPiSubtypeProd_symm_apply pred (fun _ : Fin n => ℝ) (x, z) i₀).trans
              (dif_pos ((hpred i₀).mpr rfl))
          rw [h1, Function.update_self]
        · have hnp : ¬ pred j := mt (hpred j).mp hj
          have h1 : e.symm (x, z) j = z ⟨j, hnp⟩ :=
            (Equiv.piEquivPiSubtypeProd_symm_apply pred (fun _ : Fin n => ℝ) (x, z) j).trans (dif_neg hnp)
          have h2 : e.symm (0, z) j = z ⟨j, hnp⟩ :=
            (Equiv.piEquivPiSubtypeProd_symm_apply pred (fun _ : Fin n => ℝ) (0, z) j).trans (dif_neg hnp)
          rw [h1, Function.update_of_ne hj, h2]
      let F₁ : (({i // pred i} → ℝ) × ({i // ¬ pred i} → ℝ)) → ℝ :=
        fun q => (if (e.symm q) i₀ ≤ τ_tilde then (1 : ℝ) else 0) * G (e.symm q)
      let F₂ : (({i // pred i} → ℝ) × ({i // ¬ pred i} → ℝ)) → ℝ :=
        fun q => G (e.symm q)
      have hF₁_meas : Measurable F₁ :=
        (Measurable.ite (measurableSet_le ((measurable_pi_apply i₀).comp e.symm.measurable) measurable_const)
          measurable_const measurable_const).mul (hG_meas.comp e.symm.measurable)
      have hF₂_meas : Measurable F₂ := hG_meas.comp e.symm.measurable
      have hF₁_int : Integrable F₁ ((Measure.pi (fun _ : {i // pred i} => ν t)).prod (Measure.pi m_out)) := by
        refine Integrable.of_mem_Icc (-2) 2 hF₁_meas.aemeasurable (Filter.Eventually.of_forall (fun q => ?_))
        refine abs_le.mp ?_
        dsimp only [F₁]; split_ifs <;> simp [hG_bdd (e.symm q)]
      have hF₂_int : Integrable F₂ ((Measure.pi (fun _ : {i // pred i} => ν τ_tilde)).prod (Measure.pi m_out)) :=
        Integrable.of_mem_Icc (-2) 2 hF₂_meas.aemeasurable
          (Filter.Eventually.of_forall (fun q => abs_le.mp (hG_bdd (e.symm q))))
      rw [← h_mp₁.integral_comp' (fun τ => (if τ i₀ ≤ τ_tilde then (1 : ℝ) else 0) * G τ),
        ← h_mp₂.integral_comp' G]
      change (∫ q, F₁ q ∂_) = (τ_tilde / t) * ∫ q, F₂ q ∂_
      rw [integral_prod_symm F₁ hF₁_int, integral_prod_symm F₂ hF₂_int, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      let gz : ℝ → ℝ := fun u => G (Function.update (e.symm (0, z)) i₀ u)
      have hgz_meas : Measurable gz := by
        refine hG_meas.comp (measurable_pi_iff.mpr (fun j => ?_))
        by_cases hj : j = i₀
        · rw [hj]; simpa using measurable_id
        · simp [Function.update_of_ne hj]
      have hgz_ite_meas : Measurable (fun u => if u ≤ τ_tilde then gz u else 0) :=
        Measurable.ite measurableSet_Iic hgz_meas measurable_const
      have h_mp_eval_t := measurePreserving_eval (fun _ : {i // pred i} => ν t) i₀_sub
      have h_mp_eval_τ := measurePreserving_eval (fun _ : {i // pred i} => ν τ_tilde) i₀_sub
      have h_eval_t : (∫ x, (if x i₀_sub ≤ τ_tilde then gz (x i₀_sub) else 0) ∂(Measure.pi (fun _ : {i // pred i} => ν t))) =
          ∫ u, (if u ≤ τ_tilde then gz u else 0) ∂(ν t) := by
        conv_rhs => rw [← h_mp_eval_t.map_eq]
        exact (integral_map h_mp_eval_t.measurable.aemeasurable hgz_ite_meas.aestronglyMeasurable).symm
      have h_eval_τ : (∫ x, gz (x i₀_sub) ∂(Measure.pi (fun _ : {i // pred i} => ν τ_tilde))) =
          ∫ u, gz u ∂(ν τ_tilde) := by
        conv_rhs => rw [← h_mp_eval_τ.map_eq]
        exact (integral_map h_mp_eval_τ.measurable.aemeasurable hgz_meas.aestronglyMeasurable).symm
      have h_lhs_eq : (fun x : {i // pred i} → ℝ => F₁ (x, z)) =
          (fun x => if x i₀_sub ≤ τ_tilde then gz (x i₀_sub) else 0) := by
        ext x; dsimp only [F₁, gz]; rw [h_symm_eq x z, Function.update_self]; split_ifs <;> ring
      have h_rhs_eq : (fun x : {i // pred i} → ℝ => F₂ (x, z)) = (fun x => gz (x i₀_sub)) := by
        ext x; dsimp only [F₂, gz]; rw [h_symm_eq x z]
      dsimp only
      rw [h_lhs_eq, h_rhs_eq, h_eval_t, h_eval_τ, h_1d gz]
    have h_mix_emp : μ_mix ∅ = unifCubeMeasure n t := by
      simp [μ_mix, unifCubeMeasure, ν]
    change (∫ τ, (∏ g ∈ Q, if τ g ≤ τ_tilde then (1 : ℝ) else 0) * H τ ∂(unifCubeMeasure n t)) =
      (τ_tilde / t) ^ Q.card * ∫ τ, H τ ∂(μ_mix Q)
    rw [← h_mix_emp]
    suffices h_ind : ∀ (R : Finset (Fin n)), Disjoint R (Q \ R) → R ⊆ Q →
        (∫ τ, (∏ g ∈ R, if τ g ≤ τ_tilde then (1 : ℝ) else 0) * H τ ∂(μ_mix (Q \ R))) =
          (τ_tilde / t) ^ R.card * ∫ τ, H τ ∂(μ_mix Q) by
      simpa using h_ind Q (by simp) subset_rfl
    intro R
    induction R using Finset.induction_on with
    | empty => intro _ _; simp
    | insert a s has ih =>
      intro _ hasQ
      have haQ : a ∈ Q := hasQ (Finset.mem_insert_self a s)
      have hsQ : s ⊆ Q := (Finset.subset_insert a s).trans hasQ
      have ha_not : a ∉ Q \ insert a s := fun hm => (Finset.mem_sdiff.mp hm).2 (Finset.mem_insert_self a s)
      have h_ins_eq : insert a (Q \ insert a s) = Q \ s := by
        ext z; simp only [Finset.mem_insert, Finset.mem_sdiff]
        refine ⟨?_, ?_⟩
        · rintro (rfl | ⟨hzQ, hzn⟩)
          · exact ⟨haQ, has⟩
          · exact ⟨hzQ, fun hzs => hzn (Or.inr hzs)⟩
        · rintro ⟨hzQ, hzs⟩
          by_cases hza : z = a
          · exact Or.inl hza
          · exact Or.inr ⟨hzQ, fun hz => hz.elim hza hzs⟩
      let Gs : (Fin n → ℝ) → ℝ := fun τ => (∏ g ∈ s, if τ g ≤ τ_tilde then (1 : ℝ) else 0) * H τ
      have hGs_meas : Measurable Gs :=
        (Finset.measurable_prod s (fun g _ =>
          Measurable.ite (measurableSet_le (measurable_pi_apply g) measurable_const)
            measurable_const measurable_const)).mul hH_meas
      have hGs_bdd : ∀ τ, |Gs τ| ≤ 2 := by
        intro τ; dsimp only [Gs]
        have hp0 : 0 ≤ ∏ g ∈ s, if τ g ≤ τ_tilde then (1 : ℝ) else 0 :=
          Finset.prod_nonneg (fun _ _ => by split_ifs <;> norm_num)
        have hp1 : (∏ g ∈ s, if τ g ≤ τ_tilde then (1 : ℝ) else 0) ≤ 1 :=
          Finset.prod_le_one (fun _ _ => by split_ifs <;> norm_num) (fun _ _ => by split_ifs <;> norm_num)
        rw [abs_mul, abs_of_nonneg hp0]
        calc (∏ g ∈ s, if τ g ≤ τ_tilde then (1 : ℝ) else 0) * |H τ|
            ≤ 1 * 2 := mul_le_mul hp1 (hH_bdd τ) (abs_nonneg _) zero_le_one
          _ = 2 := one_mul 2
      have h_rew : (fun τ => (∏ g ∈ insert a s, if τ g ≤ τ_tilde then (1 : ℝ) else 0) * H τ) =
          fun τ => (if τ a ≤ τ_tilde then (1 : ℝ) else 0) * Gs τ := by
        ext τ; simp [Gs, Finset.prod_insert has]
      rw [h_rew, h_step (Q \ insert a s) a ha_not Gs hGs_meas hGs_bdd, h_ins_eq,
        ih Finset.disjoint_sdiff hsQ, Finset.card_insert_of_notMem has, pow_succ']
      ring

  have h_decouple2 : ∀ (n : ℕ) {τ_tilde t : ℝ}, 0 < τ_tilde → τ_tilde < t →
      ∀ (Q : Finset (Fin n)) (f : Fin n), f ∈ Q →
      ∀ (I_late : (Fin n → ℝ) → ℝ) (Ψ : (Fin n → ℝ) × ℝ × (Fin n → ℝ) → ℝ),
      Measurable I_late →
      (∀ ω, 0 ≤ I_late ω ∧ I_late ω ≤ 1) →
      (∀ ω₁ ω₂ : Fin n → ℝ, (∀ i, i ∉ Q → ω₁ i = ω₂ i) → I_late ω₁ = I_late ω₂) →
      Measurable Ψ →
      (∀ p, |Ψ p| ≤ 1) →
      (∀ (τ₁ τ₂ : Fin n → ℝ) (u : ℝ) (ω : Fin n → ℝ),
        (∀ i ∈ Q.erase f, τ₁ i = τ₂ i) → Ψ (τ₁, u, ω) = Ψ (τ₂, u, ω)) →
      (∀ (τ' : Fin n → ℝ) (u : ℝ) (ω₁ ω₂ : Fin n → ℝ),
        (∀ i, i ∉ Q → ω₁ i = ω₂ i) → Ψ (τ', u, ω₁) = Ψ (τ', u, ω₂)) →
      (let ν := fun r => (ENNReal.ofReal r)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) r)
       ∀ ω : Fin n → ℝ, I_late ω ≠ 0 → (∀ i, i ∉ Q → 0 ≤ ω i ∧ ω i ≤ t) →
         0 ≤ ∫ u, (∫ τ', Ψ (τ', u, ω) ∂(unifCubeMeasure n τ_tilde)) ∂(ν τ_tilde)) →
      let ν := fun r => (ENNReal.ofReal r)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) r)
      let μ_mix := Measure.pi (fun i : Fin n => if i ∈ Q then ν τ_tilde else ν t)
      0 ≤ ∫ τ, I_late τ * Ψ (τ, τ f, τ) ∂μ_mix := by
    intro n τ_tilde t h0 hlt Q f hfQ I_late Ψ hI_meas hI_bounds hI_indep
      hΨ_meas hΨ_bdd hΨ_in hΨ_out h_1d_nonneg ν μ_mix
    let μ_τ : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => ν τ_tilde)
    have hμ_τ_eq : μ_τ = unifCubeMeasure n τ_tilde := rfl
    have ht_pos : 0 < t := h0.trans hlt
    haveI : IsProbabilityMeasure (ν τ_tilde) := h_unif1D_prob h0
    haveI : IsProbabilityMeasure (ν t) := h_unif1D_prob ht_pos
    haveI : IsProbabilityMeasure μ_τ := by dsimp only [μ_τ]; infer_instance
    haveI : IsProbabilityMeasure μ_mix := by
      haveI : ∀ i : Fin n, IsProbabilityMeasure (if i ∈ Q then ν τ_tilde else ν t) := by
        intro i; split_ifs <;> infer_instance
      dsimp only [μ_mix]; infer_instance
    let F : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p => I_late p.2 * Ψ (p.1, p.2 f, p.2)
    have hF_meas : Measurable F :=
      (hI_meas.comp measurable_snd).mul
        (hΨ_meas.comp (measurable_fst.prodMk
          (((measurable_pi_apply f).comp measurable_snd).prodMk measurable_snd)))
    have hF_bdd : ∀ p, |F p| ≤ 1 := by
      intro p; dsimp only [F]
      rw [abs_mul, abs_of_nonneg (hI_bounds p.2).1]
      exact mul_le_one₀ (hI_bounds p.2).2 (abs_nonneg _) (hΨ_bdd _)
    have h_step1 : (∫ τ, F (τ, τ) ∂μ_mix) = ∫ ω, (∫ τ', F (τ', ω) ∂μ_τ) ∂μ_mix := by
      obtain ⟨pred₁, hpred₁⟩ : ∃ pred₁ : Fin n → Prop, ∀ i, pred₁ i ↔ i ∈ Q.erase f :=
        ⟨fun i => i ∈ Q.erase f, fun _ => Iff.rfl⟩
      let e₁ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) pred₁
      let m_in : {i : Fin n // pred₁ i} → Measure ℝ := fun _ => ν τ_tilde
      let m_out_mix : {i : Fin n // ¬ pred₁ i} → Measure ℝ :=
        fun i => if i.1 ∈ Q then ν τ_tilde else ν t
      let m_out_τ : {i : Fin n // ¬ pred₁ i} → Measure ℝ := fun _ => ν τ_tilde
      have hm_in_eq : (fun i : {i : Fin n // pred₁ i} => if i.1 ∈ Q then ν τ_tilde else ν t) = m_in := by
        funext ⟨i, hi⟩
        have hiQ : i ∈ Q := Finset.erase_subset f Q ((hpred₁ i).mp hi)
        simp [m_in, hiQ]
      haveI : IsProbabilityMeasure (Measure.pi m_in) := by dsimp only [m_in]; infer_instance
      haveI : IsProbabilityMeasure (Measure.pi m_out_mix) := by
        haveI : ∀ i : {i // ¬ pred₁ i}, IsProbabilityMeasure (m_out_mix i) := by
          intro i; dsimp only [m_out_mix]; split_ifs <;> infer_instance
        infer_instance
      haveI : IsProbabilityMeasure (Measure.pi m_out_τ) := by dsimp only [m_out_τ]; infer_instance
      have h_mp_mix : MeasurePreserving e₁.symm ((Measure.pi m_in).prod (Measure.pi m_out_mix)) μ_mix := by
        have h := (measurePreserving_piEquivPiSubtypeProd (fun i : Fin n => if i ∈ Q then ν τ_tilde else ν t) pred₁).symm e₁
        simpa only [μ_mix, m_out_mix, hm_in_eq] using h
      have h_mp_τ : MeasurePreserving e₁.symm ((Measure.pi m_in).prod (Measure.pi m_out_τ)) μ_τ :=
        (measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => ν τ_tilde) pred₁).symm e₁
      let G₁ : (({i // pred₁ i} → ℝ) × ({i // ¬ pred₁ i} → ℝ)) → ℝ := fun q => F (e₁.symm q, e₁.symm q)
      have hG₁_meas : Measurable G₁ := hF_meas.comp (e₁.symm.measurable.prodMk e₁.symm.measurable)
      have hG₁_int : Integrable G₁ ((Measure.pi m_in).prod (Measure.pi m_out_mix)) :=
        Integrable.of_mem_Icc (-1) 1 hG₁_meas.aemeasurable
          (Filter.Eventually.of_forall (fun q => abs_le.mp (hF_bdd (e₁.symm q, e₁.symm q))))
      have h_symm_in : ∀ q (i : Fin n) (hi : pred₁ i), e₁.symm q i = q.1 ⟨i, hi⟩ :=
        fun q i hi => (Equiv.piEquivPiSubtypeProd_symm_apply pred₁ (fun _ : Fin n => ℝ) q i).trans (dif_pos hi)
      have h_symm_out : ∀ q (i : Fin n) (hi : ¬ pred₁ i), e₁.symm q i = q.2 ⟨i, hi⟩ :=
        fun q i hi => (Equiv.piEquivPiSubtypeProd_symm_apply pred₁ (fun _ : Fin n => ℝ) q i).trans (dif_neg hi)
      have h_indep₁ : ∀ x x' z z', F (e₁.symm (x, z), e₁.symm (x', z')) = G₁ (x, z') := by
        intro x x' z z'; dsimp only [F, G₁]
        have hout_eq : ∀ i, i ∉ Q → e₁.symm (x', z') i = e₁.symm (x, z') i := by
          intro i hiQ
          have hnp : ¬ pred₁ i := fun hp => hiQ (Finset.erase_subset f Q ((hpred₁ i).mp hp))
          rw [h_symm_out (x', z') i hnp, h_symm_out (x, z') i hnp]
        have hf_np : ¬ pred₁ f := fun hp => Finset.notMem_erase f Q ((hpred₁ f).mp hp)
        have hf_eq : e₁.symm (x', z') f = e₁.symm (x, z') f := by
          rw [h_symm_out (x', z') f hf_np, h_symm_out (x, z') f hf_np]
        have hin_eq : ∀ i ∈ Q.erase f, e₁.symm (x, z) i = e₁.symm (x, z') i := by
          intro i hi
          have hp : pred₁ i := (hpred₁ i).mpr hi
          rw [h_symm_in (x, z) i hp, h_symm_in (x, z') i hp]
        rw [hI_indep _ _ hout_eq, hf_eq, hΨ_in _ _ _ _ hin_eq, hΨ_out _ _ _ _ hout_eq]
      have h_lhs : (∫ τ, F (τ, τ) ∂μ_mix) = ∫ z', (∫ x, G₁ (x, z') ∂(Measure.pi m_in)) ∂(Measure.pi m_out_mix) := by
        rw [← h_mp_mix.integral_comp' (fun τ => F (τ, τ))]
        change (∫ q, G₁ q ∂_) = _
        exact integral_prod_symm G₁ hG₁_int
      have h_inner : ∀ x' z', (∫ τ', F (τ', e₁.symm (x', z')) ∂μ_τ) = ∫ x, G₁ (x, z') ∂(Measure.pi m_in) := by
        intro x' z'
        rw [← h_mp_τ.integral_comp' (fun τ' => F (τ', e₁.symm (x', z')))]
        have h_fn : (fun q => F (e₁.symm q, e₁.symm (x', z'))) = fun q => G₁ (q.1, z') :=
          funext (fun ⟨x, z⟩ => h_indep₁ x x' z z')
        rw [h_fn]
        have h_sl_meas : Measurable (fun q : ({i // pred₁ i} → ℝ) × ({i // ¬ pred₁ i} → ℝ) => G₁ (q.1, z')) :=
          hG₁_meas.comp (measurable_fst.prodMk measurable_const)
        have h_sl_int : Integrable (fun q => G₁ (q.1, z')) ((Measure.pi m_in).prod (Measure.pi m_out_τ)) :=
          Integrable.of_mem_Icc (-1) 1 h_sl_meas.aemeasurable
            (Filter.Eventually.of_forall (fun q => abs_le.mp (hF_bdd (e₁.symm (q.1, z'), e₁.symm (q.1, z')))))
        rw [integral_prod _ h_sl_int]; simp [integral_const]
      have h_rhs : (∫ ω, (∫ τ', F (τ', ω) ∂μ_τ) ∂μ_mix) =
          ∫ z', (∫ x, G₁ (x, z') ∂(Measure.pi m_in)) ∂(Measure.pi m_out_mix) := by
        rw [← h_mp_mix.integral_comp' (fun ω => ∫ τ', F (τ', ω) ∂μ_τ)]
        have h_fn2 : (fun q' => ∫ τ', F (τ', e₁.symm q') ∂μ_τ) = fun q' => ∫ x, G₁ (x, q'.2) ∂(Measure.pi m_in) :=
          funext (fun ⟨x', z'⟩ => h_inner x' z')
        rw [h_fn2]
        have h_z_int : Integrable (fun z' => ∫ x, G₁ (x, z') ∂(Measure.pi m_in)) (Measure.pi m_out_mix) :=
          hG₁_int.integral_prod_right
        rw [integral_prod_symm _ (h_z_int.comp_snd (Measure.pi m_in))]; simp [integral_const]
      rw [h_lhs, h_rhs]
    change 0 ≤ ∫ τ, F (τ, τ) ∂μ_mix
    rw [h_step1]
    obtain ⟨pred₂, hpred₂⟩ : ∃ pred₂ : Fin n → Prop, ∀ i, pred₂ i ↔ i = f :=
      ⟨fun i => i = f, fun _ => Iff.rfl⟩
    let f_sub : {i : Fin n // pred₂ i} := ⟨f, (hpred₂ f).mpr rfl⟩
    let e₂ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) pred₂
    let m₂_in : {i : Fin n // pred₂ i} → Measure ℝ := fun _ => ν τ_tilde
    let m₂_out : {i : Fin n // ¬ pred₂ i} → Measure ℝ :=
      fun i => if i.1 ∈ Q then ν τ_tilde else ν t
    have hm₂_in_eq : (fun i : {i : Fin n // pred₂ i} => if i.1 ∈ Q then ν τ_tilde else ν t) = m₂_in := by
      funext ⟨i, hi⟩; dsimp only [m₂_in]; rw [(hpred₂ i).mp hi]; simp [hfQ]
    haveI : IsProbabilityMeasure (Measure.pi m₂_in) := by dsimp only [m₂_in]; infer_instance
    haveI : IsProbabilityMeasure (Measure.pi m₂_out) := by
      haveI : ∀ i : {i // ¬ pred₂ i}, IsProbabilityMeasure (m₂_out i) := by
        intro i; dsimp only [m₂_out]; split_ifs <;> infer_instance
      infer_instance
    have h_mp₂ : MeasurePreserving e₂.symm ((Measure.pi m₂_in).prod (Measure.pi m₂_out)) μ_mix := by
      have h := (measurePreserving_piEquivPiSubtypeProd (fun i : Fin n => if i ∈ Q then ν τ_tilde else ν t) pred₂).symm e₂
      simpa only [μ_mix, m₂_out, hm₂_in_eq] using h
    let K_big : (({i // pred₂ i} → ℝ) × ({i // ¬ pred₂ i} → ℝ)) × (Fin n → ℝ) → ℝ :=
      fun p => F (p.2, e₂.symm p.1)
    have hK_big_meas : Measurable K_big :=
      hF_meas.comp (measurable_snd.prodMk (e₂.symm.measurable.comp measurable_fst))
    have hK_big_int : Integrable K_big (((Measure.pi m₂_in).prod (Measure.pi m₂_out)).prod μ_τ) :=
      Integrable.of_mem_Icc (-1) 1 hK_big_meas.aemeasurable
        (Filter.Eventually.of_forall (fun p => abs_le.mp (hF_bdd (p.2, e₂.symm p.1))))
    have hK_int : Integrable (fun q => ∫ τ', F (τ', e₂.symm q) ∂μ_τ) ((Measure.pi m₂_in).prod (Measure.pi m₂_out)) :=
      hK_big_int.integral_prod_left
    rw [← h_mp₂.integral_comp' (fun ω => ∫ τ', F (τ', ω) ∂μ_τ),
      integral_prod_symm _ hK_int]
    have h_ae_out : ∀ᵐ z ∂(Measure.pi m₂_out), ∀ i : Fin n, i ∉ Q →
        0 ≤ e₂.symm (0, z) i ∧ e₂.symm (0, z) i ≤ t := by
      rw [Filter.eventually_all]
      intro i
      by_cases hiQ : i ∈ Q
      · exact Filter.Eventually.of_forall (fun _ hnot => (hnot hiQ).elim)
      · have hnp : ¬ pred₂ i := fun hp => hiQ (((hpred₂ i).mp hp) ▸ hfQ)
        let j : {k : Fin n // ¬ pred₂ k} := ⟨i, hnp⟩
        have hm_j : m₂_out j = ν t := by simp [m₂_out, j, hiQ]
        have h_compl_zero : (ν t) (Set.Icc (0 : ℝ) t)ᶜ = 0 := by
          simp [ν, Measure.restrict_apply measurableSet_Icc.compl]
        have h_ae_1d : ∀ᵐ u ∂(m₂_out j), u ∈ Set.Icc (0 : ℝ) t := by rw [hm_j, ae_iff]; exact h_compl_zero
        have h_mp_j := measurePreserving_eval m₂_out j
        filter_upwards [h_mp_j.quasiMeasurePreserving.ae h_ae_1d] with z hz _
        have heq_z : e₂.symm (0, z) i = z j :=
          (Equiv.piEquivPiSubtypeProd_symm_apply pred₂ (fun _ : Fin n => ℝ) (0, z) i).trans (dif_neg hnp)
        rwa [heq_z]
    refine integral_nonneg_of_ae ?_
    change ∀ᵐ z ∂(Measure.pi m₂_out), 0 ≤ ∫ x, (∫ τ', F (τ', e₂.symm (x, z)) ∂μ_τ) ∂(Measure.pi m₂_in)
    filter_upwards [h_ae_out] with z hz
    let ω_z : Fin n → ℝ := e₂.symm (0, z)
    have h_out_ω : ∀ x : {i // pred₂ i} → ℝ, ∀ i, i ∉ Q → e₂.symm (x, z) i = ω_z i := by
      intro x i hiQ
      have hnp : ¬ pred₂ i := fun hp => hiQ (((hpred₂ i).mp hp) ▸ hfQ)
      have h1 := (Equiv.piEquivPiSubtypeProd_symm_apply pred₂ (fun _ : Fin n => ℝ) (x, z) i).trans (dif_neg hnp)
      have h2 := (Equiv.piEquivPiSubtypeProd_symm_apply pred₂ (fun _ : Fin n => ℝ) (0, z) i).trans (dif_neg hnp)
      exact h1.trans h2.symm
    have h_f_ω : ∀ x : {i // pred₂ i} → ℝ, e₂.symm (x, z) f = x f_sub :=
      fun x => (Equiv.piEquivPiSubtypeProd_symm_apply pred₂ (fun _ : Fin n => ℝ) (x, z) f).trans
        (dif_pos ((hpred₂ f).mpr rfl))
    have h_inner_eq : ∀ x : {i // pred₂ i} → ℝ,
        (∫ τ', F (τ', e₂.symm (x, z)) ∂μ_τ) =
          I_late ω_z * ∫ τ', Ψ (τ', x f_sub, ω_z) ∂μ_τ := by
      intro x
      have hfn : (fun τ' => F (τ', e₂.symm (x, z))) = fun τ' => I_late ω_z * Ψ (τ', x f_sub, ω_z) := by
        ext τ'; dsimp only [F]
        rw [hI_indep _ _ (h_out_ω x), h_f_ω x, hΨ_out _ _ _ _ (h_out_ω x)]
      rw [hfn, integral_const_mul]
    simp_rw [h_inner_eq]
    rw [integral_const_mul]
    by_cases hI0 : I_late ω_z = 0
    · rw [hI0, zero_mul]
    · refine mul_nonneg (hI_bounds ω_z).1 ?_
      let gu : ℝ → ℝ := fun u => ∫ τ', Ψ (τ', u, ω_z) ∂μ_τ
      have hgu_int : Integrable gu (ν τ_tilde) := by
        have h_prod_meas : Measurable (fun p : ℝ × (Fin n → ℝ) => Ψ (p.2, p.1, ω_z)) :=
          hΨ_meas.comp (measurable_snd.prodMk (measurable_fst.prodMk measurable_const))
        have h_prod_int : Integrable (fun p : ℝ × (Fin n → ℝ) => Ψ (p.2, p.1, ω_z)) ((ν τ_tilde).prod μ_τ) :=
          Integrable.of_mem_Icc (-1) 1 h_prod_meas.aemeasurable
            (Filter.Eventually.of_forall (fun p => abs_le.mp (hΨ_bdd _)))
        exact h_prod_int.integral_prod_left
      have h_mp_f : MeasurePreserving (Function.eval f_sub) (Measure.pi m₂_in) (ν τ_tilde) :=
        measurePreserving_eval (fun _ : {i // pred₂ i} => ν τ_tilde) f_sub
      have h_eval_f : (∫ x, gu (x f_sub) ∂(Measure.pi m₂_in)) = ∫ u, gu u ∂(ν τ_tilde) := by
        conv_rhs => rw [← h_mp_f.map_eq]
        exact (integral_map h_mp_f.measurable.aemeasurable
          (by rw [h_mp_f.map_eq]; exact hgu_int.aestronglyMeasurable)).symm
      change 0 ≤ ∫ x, gu (x f_sub) ∂(Measure.pi m₂_in)
      rw [h_eval_f]
      simpa only [gu, hμ_τ_eq] using h_1d_nonneg ω_z hI0 hz

  have h_pay_1d : ∀ {τ_tilde c : ℝ}, invE < τ_tilde →
      ∀ (γ : ℝ → ℝ), ContinuousOn γ (Set.Icc invE τ_tilde) →
      (∀ u ∈ Set.Icc invE τ_tilde, (Real.exp 1 * u)⁻¹ * c ≤ γ u) →
      let ν := (ENNReal.ofReal τ_tilde)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) τ_tilde)
      0 ≤ ∫ u, (if u ≤ invE then -Real.log (Real.exp 1 * τ_tilde) * c else γ u) ∂ν := by
    intro τ_tilde c h_low γ hγ_cont h_mono ν
    have hτ_pos : 0 < τ_tilde := h_invE_pos.trans h_low
    let g : ℝ → ℝ := fun u => if u ≤ invE then -Real.log (Real.exp 1 * τ_tilde) * c else γ u
    change 0 ≤ ∫ u, g u ∂ν
    rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hτ_pos.le]
    refine mul_nonneg (inv_nonneg.mpr hτ_pos.le) ?_
    have h_union : Set.Icc (0 : ℝ) τ_tilde = Set.Icc 0 invE ∪ Set.Ioc invE τ_tilde :=
      (Set.Icc_union_Ioc_eq_Icc h_invE_pos.le h_low.le).symm
    have h_disj : Disjoint (Set.Icc (0 : ℝ) invE) (Set.Ioc invE τ_tilde) :=
      Set.disjoint_left.mpr (fun _ h1 h2 => not_lt_of_ge h1.2 h2.1)
    have hg_eq1 : Set.EqOn g (fun _ => -Real.log (Real.exp 1 * τ_tilde) * c) (Set.Icc 0 invE) :=
      fun u hu => if_pos hu.2
    have hg_eq2 : Set.EqOn g γ (Set.Ioc invE τ_tilde) :=
      fun u hu => if_neg (not_le.mpr hu.1)
    have hint1 : IntegrableOn g (Set.Icc 0 invE) volume :=
      (integrableOn_const (hs := measure_Icc_lt_top.ne)).congr_fun hg_eq1.symm measurableSet_Icc
    have hint2 : IntegrableOn g (Set.Ioc invE τ_tilde) volume :=
      (hγ_cont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).congr_fun hg_eq2.symm measurableSet_Ioc
    rw [h_union, setIntegral_union h_disj measurableSet_Ioc hint1 hint2,
      setIntegral_congr_fun measurableSet_Icc hg_eq1,
      setIntegral_congr_fun measurableSet_Ioc hg_eq2,
      setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le h_invE_pos.le, sub_zero,
      ← intervalIntegral.integral_of_le h_low.le]
    let H_prim : ℝ → ℝ := fun u => invE * Real.log (Real.exp 1 * u) * c
    let H_deriv : ℝ → ℝ := fun u => (Real.exp 1 * u)⁻¹ * c
    have hH_cont : ContinuousOn H_prim (Set.Icc invE τ_tilde) := by
      refine ((continuousOn_const.mul ?_).mul continuousOn_const)
      refine ContinuousOn.log (continuousOn_const.mul continuousOn_id) (fun u hu => ?_)
      exact (mul_pos (Real.exp_pos 1) (h_invE_pos.trans_le hu.1)).ne'
    have hH_deriv_cont : ContinuousOn H_deriv (Set.Icc invE τ_tilde) := by
      refine (ContinuousOn.inv₀ (continuousOn_const.mul continuousOn_id) (fun u hu => ?_)).mul continuousOn_const
      exact (mul_pos (Real.exp_pos 1) (h_invE_pos.trans_le hu.1)).ne'
    have hH_hasDeriv : ∀ u ∈ Set.Ioo invE τ_tilde, HasDerivAt H_prim (H_deriv u) u := by
      intro u hu
      have hu_pos : 0 < u := h_invE_pos.trans hu.1
      have hexp_ne : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
      have h1 : HasDerivAt (fun x : ℝ => Real.exp 1 * x) (Real.exp 1 * 1) u :=
        (hasDerivAt_id u).const_mul (Real.exp 1)
      have h2 := (Real.hasDerivAt_log (mul_ne_zero hexp_ne hu_pos.ne')).comp u h1
      have h3 := (h2.const_mul invE).mul_const c
      have heq : invE * ((Real.exp 1 * u)⁻¹ * (Real.exp 1 * 1)) * c = (Real.exp 1 * u)⁻¹ * c := by
        rw [h_invE_eq]; have := hu_pos.ne'; field_simp
      dsimp only [H_deriv]; rw [← heq]; exact h3
    have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h_low.le hH_cont hH_hasDeriv
      (hH_deriv_cont.intervalIntegrable_of_Icc h_low.le)
    have hH_lo : H_prim invE = 0 := by
      dsimp only [H_prim]; rw [h_exp_invE, Real.log_one, mul_zero, zero_mul]
    rw [hH_lo, sub_zero] at h_ftc
    have h_cancel : invE * (-Real.log (Real.exp 1 * τ_tilde) * c) + ∫ u in invE..τ_tilde, γ u =
        (∫ u in invE..τ_tilde, γ u) - ∫ u in invE..τ_tilde, H_deriv u := by
      rw [h_ftc]; dsimp only [H_prim]; ring
    rw [h_cancel, ← intervalIntegral.integral_sub (hγ_cont.intervalIntegrable_of_Icc h_low.le)
      (hH_deriv_cont.intervalIntegrable_of_Icc h_low.le)]
    exact intervalIntegral.integral_nonneg h_low.le (fun u hu => sub_nonneg.mpr (h_mono u hu))

  have h_conj1a : ∀ (n : ℕ) (C : Finset (Fin n) → Finset (Fin n)) (t₀ t : ℝ)
      (S B : Finset (Fin n)) (β : Fin n → ℝ) (x : Fin n) (A : Finset (Fin n)),
      IsChoiceRule C → HasPersistence C → HasSingleDisplacement C →
      invE ≤ t₀ → t₀ ≤ t → t ≤ 1 →
      Disjoint S B → (∀ b ∈ B, invE ≤ β b ∧ β b ≤ t) → x ∉ S ∪ B → A ⊆ S →
        MonotoneOn (fun τ_tilde => τ_tilde * genMovingProb2 C t₀ t S B β x A τ_tilde)
          (Set.Icc invE t₀) ∧
        ∀ τ_tilde ∈ Set.Icc invE t₀,
          (1 / (Real.exp 1 * τ_tilde)) * genMovingProb2 C t₀ t S B β x A invE ≤
            genMovingProb2 C t₀ t S B β x A τ_tilde := by
    intro n C
    have h_ind_mono : ∀ (k : ℕ), ∀ (t₀ t : ℝ) (S B : Finset (Fin n)) (β : Fin n → ℝ)
        (x : Fin n) (A : Finset (Fin n)),
        S.card = k →
        IsChoiceRule C → HasPersistence C → HasSingleDisplacement C →
        invE ≤ t₀ → t₀ ≤ t → t ≤ 1 →
        Disjoint S B → (∀ b ∈ B, invE ≤ β b ∧ β b ≤ t) → x ∉ S ∪ B → A ⊆ S →
        MonotoneOn (fun τ_tilde => τ_tilde * genMovingProb2 C t₀ t S B β x A τ_tilde)
          (Set.Icc invE t₀) := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro t₀ t S B β x A hk hC hP hSD ht₀_low ht₀_t ht_high hDisj hβ hxSB hA
        have ht_low : invE ≤ t := ht₀_low.trans ht₀_t
        intro u₁ hu₁ u₂ hu₂ hu₁₂
        rcases eq_or_lt_of_le hu₁₂ with rfl | hu_lt
        · exact le_rfl
        · refine h_ftc_fubini2 C S B β x A hP hSD ht₀_low ht₀_t ht_high hxSB hA hu₁ hu₂ hu_lt (fun τ_tilde hτ_ioo => ?_)
          have h_low : invE < τ_tilde := lt_of_le_of_lt hu₁.1 hτ_ioo.1
          have h_high_t₀ : τ_tilde < t₀ := lt_of_lt_of_le hτ_ioo.2 hu₂.2
          have h_high : τ_tilde < t := lt_of_lt_of_le h_high_t₀ ht₀_t
          have hτ_pos : 0 < τ_tilde := h_invE_pos.trans h_low
          have ht₀_pos : 0 < t₀ := hτ_pos.trans h_high_t₀
          let μ_t₀ : Measure (Fin n → ℝ) := unifCubeMeasure n t₀
          haveI : IsProbabilityMeasure ((ENNReal.ofReal t₀)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) t₀)) :=
            h_unif1D_prob ht₀_pos
          haveI : IsProbabilityMeasure μ_t₀ := by dsimp only [μ_t₀, unifCubeMeasure]; infer_instance
          let cyl : Finset (Fin n) → (Fin n → ℝ) → ℝ := fun Q τ =>
            (∏ g ∈ Q, if τ g ≤ τ_tilde then (1 : ℝ) else 0) *
              (∏ g ∈ S \ Q, if τ_tilde < τ g then (1 : ℝ) else 0)
          have h_cyl_sum : ∀ τ : Fin n → ℝ, ∑ Q ∈ S.powerset, cyl Q τ = 1 := by
            intro τ
            have h1 : ∀ g ∈ S, (if τ g ≤ τ_tilde then (1 : ℝ) else 0) +
                (if τ_tilde < τ g then (1 : ℝ) else 0) = 1 := by
              intro g _
              by_cases h : τ g ≤ τ_tilde
              · simp [h, not_lt.mpr h]
              · simp [h, lt_of_not_ge h]
            calc ∑ Q ∈ S.powerset, cyl Q τ
                = ∏ g ∈ S, ((if τ g ≤ τ_tilde then (1 : ℝ) else 0) +
                    (if τ_tilde < τ g then (1 : ℝ) else 0)) :=
                  (Finset.prod_add (fun g => if τ g ≤ τ_tilde then (1 : ℝ) else 0)
                    (fun g => if τ_tilde < τ g then (1 : ℝ) else 0) S).symm
              _ = ∏ _g ∈ S, (1 : ℝ) := Finset.prod_congr rfl h1
              _ = 1 := Finset.prod_const_one
          have h_cyl_bounds : ∀ Q τ, 0 ≤ cyl Q τ ∧ cyl Q τ ≤ 1 := by
            intro Q τ; dsimp only [cyl]
            have h1_nn : 0 ≤ ∏ g ∈ Q, if τ g ≤ τ_tilde then (1 : ℝ) else 0 :=
              Finset.prod_nonneg (fun _ _ => by split_ifs <;> norm_num)
            have h1_le : (∏ g ∈ Q, if τ g ≤ τ_tilde then (1 : ℝ) else 0) ≤ 1 :=
              Finset.prod_le_one (fun _ _ => by split_ifs <;> norm_num) (fun _ _ => by split_ifs <;> norm_num)
            have h2_nn : 0 ≤ ∏ g ∈ S \ Q, if τ_tilde < τ g then (1 : ℝ) else 0 :=
              Finset.prod_nonneg (fun _ _ => by split_ifs <;> norm_num)
            have h2_le : (∏ g ∈ S \ Q, if τ_tilde < τ g then (1 : ℝ) else 0) ≤ 1 :=
              Finset.prod_le_one (fun _ _ => by split_ifs <;> norm_num) (fun _ _ => by split_ifs <;> norm_num)
            exact ⟨mul_nonneg h1_nn h2_nn, mul_le_one₀ h1_le h2_nn h2_le⟩
          have h_cyl_meas : ∀ Q, Measurable (cyl Q) := by
            intro Q; dsimp only [cyl]
            exact (Finset.measurable_prod Q (fun g _ =>
              Measurable.ite (measurableSet_le (measurable_pi_apply g) measurable_const)
                measurable_const measurable_const)).mul
              (Finset.measurable_prod (S \ Q) (fun g _ =>
                Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply g))
                  measurable_const measurable_const))
          have h_md_meas : Measurable (fun τ => moveDeriv C t S B β x A τ τ_tilde) :=
            (h_moveDeriv_meas C ht_low S B β x A).comp (measurable_const.prodMk measurable_id)
          have h_term_int : ∀ Q, Integrable (fun τ => cyl Q τ * moveDeriv C t S B β x A τ τ_tilde) μ_t₀ := by
            intro Q
            refine Integrable.of_mem_Icc (-2) 2 ((h_cyl_meas Q).mul h_md_meas).aemeasurable
              (Filter.Eventually.of_forall (fun τ => abs_le.mp ?_))
            rw [abs_mul, abs_of_nonneg (h_cyl_bounds Q τ).1]
            calc cyl Q τ * |moveDeriv C t S B β x A τ τ_tilde|
                ≤ 1 * 2 := mul_le_mul (h_cyl_bounds Q τ).2
                  (h_moveDeriv_bdd C ht_low ht_high S B β x A τ τ_tilde ⟨h_low.le, h_high.le⟩)
                  (abs_nonneg _) zero_le_one
              _ = 2 := one_mul 2
          have h_part_eq : (fun τ => moveDeriv C t S B β x A τ τ_tilde) =
              fun τ => ∑ Q ∈ S.powerset, cyl Q τ * moveDeriv C t S B β x A τ τ_tilde := by
            ext τ
            rw [← Finset.sum_mul, h_cyl_sum τ, one_mul]
          change 0 ≤ ∫ τ, moveDeriv C t S B β x A τ τ_tilde ∂μ_t₀
          rw [h_part_eq, integral_finset_sum _ (fun Q _ => h_term_int Q)]
          refine Finset.sum_nonneg (fun Q hQ_mem => ?_)
          have hQS : Q ⊆ S := Finset.mem_powerset.mp hQ_mem
          by_cases hAQ : A ⊆ Q
          · let U_Q : Finset (Fin n) := Q ∪ B.filter (fun b => β b ≤ τ_tilde)
            have hxUQ : x ∉ U_Q := by
              intro hx_in
              simp only [U_Q, Finset.mem_union, Finset.mem_filter] at hx_in
              rcases hx_in with hxQ | ⟨hxB', _⟩
              · exact hxSB (Finset.mem_union_left B (hQS hxQ))
              · exact hxSB (Finset.mem_union_right S hxB')
            have h_pres_UQ : ∀ τ : Fin n → ℝ,
                (∀ g ∈ Q, τ g ≤ τ_tilde) → (∀ g ∈ S \ Q, τ_tilde < τ g) →
                presentSet S B τ β τ_tilde = U_Q := by
              intro τ h_in h_out
              unfold presentSet U_Q
              congr 1
              ext g
              simp only [Finset.mem_filter]
              refine ⟨fun ⟨hgS, hle⟩ => ?_, fun hgQ => ⟨hQS hgQ, h_in g hgQ⟩⟩
              by_contra hg_notQ
              exact not_lt_of_ge hle (h_out g (Finset.mem_sdiff.mpr ⟨hgS, hg_notQ⟩))
            by_cases h_has_disp : ∃ f ∈ Q \ A, f ∈ C U_Q \ C (insert x U_Q)
            · obtain ⟨f, hfQA, hf_disp⟩ := h_has_disp
              have hfQ : f ∈ Q := (Finset.mem_sdiff.mp hfQA).1
              have hf_notA : f ∉ A := (Finset.mem_sdiff.mp hfQA).2
              have hfS : f ∈ S := hQS hfQ
              have hxS : x ∉ S := fun hs => hxSB (Finset.mem_union_left B hs)
              have hxB : x ∉ B := fun hb => hxSB (Finset.mem_union_right S hb)
              have hfx : f ≠ x := fun h => hxS (h ▸ hfS)
              have hfB : f ∉ B := Finset.disjoint_left.mp hDisj hfS
              have hA_er : A ⊆ Q.erase f := fun z hz =>
                Finset.mem_erase.mpr ⟨fun hzf => hf_notA (hzf ▸ hz), hAQ hz⟩
              let B_cont : Finset (Fin n) := insert x (B ∪ (S \ Q))
              let β_cont : (Fin n → ℝ) → (Fin n → ℝ) := fun ω =>
                Function.update (fun z => if z ∈ S \ Q then ω z else β z) x τ_tilde
              let I_late : (Fin n → ℝ) → ℝ :=
                fun ω => ∏ g ∈ S \ Q, if τ_tilde < ω g then (1 : ℝ) else 0
              let Ψ : (Fin n → ℝ) × ℝ × (Fin n → ℝ) → ℝ := fun p =>
                if p.2.1 ≤ invE then
                  -Real.log (Real.exp 1 * τ_tilde) *
                    retainProd C t (Q.erase f) (insert f B_cont) p.1
                      (Function.update (β_cont p.2.2) f invE) A
                else
                  retainProd C t (Q.erase f) (insert f B_cont) p.1
                    (Function.update (β_cont p.2.2) f p.2.1) A
              have h_pres_univ : ∀ (τ : Fin n → ℝ) (v : ℝ),
                  presentSet S (insert x B) τ (Function.update β x τ_tilde) v =
                    presentSet (Q.erase f) (insert f B_cont) τ (Function.update (β_cont τ) f (τ f)) v := by
                intro τ v; ext z
                by_cases hzf : z = f
                · rw [hzf]; simp [presentSet, hfS, hfx, hfB]
                · by_cases hzx : z = x
                  · rw [hzx]
                    have hx_not_er : x ∉ Q.erase f := fun hm => hxS (hQS (Finset.erase_subset f Q hm))
                    simp [presentSet, hxS, hx_not_er, Ne.symm hfx, B_cont, β_cont]
                  · by_cases hzQ : z ∈ Q
                    · have hzS : z ∈ S := hQS hzQ
                      have hzB : z ∉ B := Finset.disjoint_left.mp hDisj hzS
                      have hz_er : z ∈ Q.erase f := Finset.mem_erase.mpr ⟨hzf, hzQ⟩
                      have hz_not_Bc : z ∉ B_cont := by simp [B_cont, hzx, hzB, hzQ]
                      simp [presentSet, hzS, hzx, hzB, hz_er, hzf, hz_not_Bc]
                    · by_cases hzS : z ∈ S
                      · have hzB : z ∉ B := Finset.disjoint_left.mp hDisj hzS
                        have hz_not_er : z ∉ Q.erase f := fun hm => hzQ (Finset.erase_subset f Q hm)
                        have hzSQ : z ∈ S \ Q := Finset.mem_sdiff.mpr ⟨hzS, hzQ⟩
                        have hz_Bc : z ∈ B_cont := by simp [B_cont, hzSQ]
                        simp [presentSet, hzS, hzx, hzB, hz_not_er, hzf, hz_Bc, β_cont, hzQ]
                      · have hz_not_er : z ∉ Q.erase f := fun hm => hzS (hQS (Finset.erase_subset f Q hm))
                        by_cases hzB : z ∈ B
                        · have hz_Bc : z ∈ B_cont := by simp [B_cont, hzB]
                          simp [presentSet, hzS, hzx, hzB, hz_not_er, hzf, hz_Bc, β_cont]
                        · have hz_not_Bc : z ∉ B_cont := by simp [B_cont, hzx, hzB, hzS]
                          simp [presentSet, hzS, hzx, hzB, hz_not_er, hzf, hz_not_Bc]
              have h_ret_univ : ∀ (τ : Fin n → ℝ) (g : Fin n),
                  retentionProb C t S (insert x B) τ (Function.update β x τ_tilde) g =
                    retentionProb C t (Q.erase f) (insert f B_cont) τ (Function.update (β_cont τ) f (τ f)) g := by
                intro τ g; unfold retentionProb deathTime; simp_rw [h_pres_univ τ]
              have h_pt_Ψ : ∀ τ : Fin n → ℝ,
                  cyl Q τ * moveDeriv C t S B β x A τ τ_tilde =
                    (∏ g ∈ Q, if τ g ≤ τ_tilde then (1 : ℝ) else 0) *
                      (I_late τ * Ψ (τ, τ f, τ)) := by
                intro τ
                by_cases h_in : ∀ g ∈ Q, τ g ≤ τ_tilde
                · by_cases h_out : ∀ g ∈ S \ Q, τ_tilde < τ g
                  · have h_q1 : (∏ g ∈ Q, if τ g ≤ τ_tilde then (1 : ℝ) else 0) = 1 :=
                      Finset.prod_eq_one (fun g hg => if_pos (h_in g hg))
                    have h_i1 : I_late τ = 1 :=
                      Finset.prod_eq_one (fun g hg => if_pos (h_out g hg))
                    have h_c1 : cyl Q τ = 1 := by
                      change (∏ g ∈ Q, if τ g ≤ τ_tilde then (1 : ℝ) else 0) * I_late τ = 1
                      rw [h_q1, h_i1, mul_one]
                    rw [h_c1, h_q1, h_i1, one_mul, one_mul, one_mul]
                    have hU_eq := h_pres_UQ τ h_in h_out
                    let D := S.filter (fun g => τ g ≤ invE ∧
                      g ∈ C (presentSet S B τ β τ_tilde) \ C (insert x (presentSet S B τ β τ_tilde)))
                    have hD_sub_f : ∀ g ∈ D, g = f := by
                      intro g hgD
                      have hg_disp : g ∈ C U_Q \ C (insert x U_Q) := by
                        have h := (Finset.mem_filter.mp hgD).2.2
                        rwa [hU_eq] at h
                      exact Finset.card_le_one.mp (hSD U_Q x hxUQ) g hg_disp f hf_disp
                    change moveDerivBranch C t S B β x A D τ τ_tilde = Ψ (τ, τ f, τ)
                    by_cases hf_early : τ f ≤ invE
                    · have hD_eq : D = {f} := by
                        ext g
                        simp only [Finset.mem_singleton]
                        refine ⟨hD_sub_f g, fun hgf => ?_⟩
                        rw [hgf]
                        refine Finset.mem_filter.mpr ⟨hfS, hf_early, ?_⟩
                        rwa [hU_eq]
                      have hD_card1 : D.card = 1 := by rw [hD_eq]; simp
                      have hD_min : D.min' (Finset.card_pos.mp (by omega)) = f := by
                        have hm : D.min' (Finset.card_pos.mp (by omega)) ∈ D :=
                          Finset.min'_mem D (Finset.card_pos.mp (by omega))
                        generalize D.min' (Finset.card_pos.mp (by omega)) = m at hm ⊢
                        rwa [hD_eq, Finset.mem_singleton] at hm
                      dsimp only [moveDerivBranch, Ψ]
                      rw [if_neg (by omega : ¬ D.card = 0), dif_pos hD_card1, hD_min,
                        if_neg hf_notA, if_pos hf_early]
                      congr 1
                      have h_pres_invE : ∀ v : ℝ, invE ≤ v →
                          presentSet (Q.erase f) (insert f B_cont) τ (Function.update (β_cont τ) f (τ f)) v =
                            presentSet (Q.erase f) (insert f B_cont) τ (Function.update (β_cont τ) f invE) v := by
                        intro v hv
                        have hτf_v : τ f ≤ v := hf_early.trans hv
                        ext z
                        by_cases hzf : z = f
                        · rw [hzf]; simp [presentSet, hτf_v, hv]
                        · simp [presentSet, hzf]
                      have h_ret_invE : ∀ g : Fin n,
                          retentionProb C t S (insert x B) τ (Function.update β x τ_tilde) g =
                            retentionProb C t (Q.erase f) (insert f B_cont) τ (Function.update (β_cont τ) f invE) g := by
                        intro g
                        rw [h_ret_univ τ g]
                        unfold retentionProb
                        split_ifs with hg_e
                        · congr 1; congr 1; unfold deathTime; congr 1; congr 1; ext v
                          simp only [Set.mem_setOf_eq]
                          exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, by rwa [← h_pres_invE v h1]⟩,
                            fun ⟨h1, h2, h3⟩ => ⟨h1, h2, by rwa [h_pres_invE v h1]⟩⟩
                        · rfl
                      unfold retainProd
                      rw [if_pos hA_er]
                      congr 1
                      · exact Finset.prod_congr rfl (fun g _ => h_ret_invE g)
                      · have h_union : ((Q.erase f) \ A) ∪ (S \ Q) = S \ insert f A := by
                          ext z
                          simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
                          refine ⟨?_, ?_⟩
                          · rintro (⟨⟨hzf, hzQ⟩, hzA⟩ | ⟨hzS, hzQ⟩)
                            · exact ⟨hQS hzQ, fun h => h.elim hzf hzA⟩
                            · exact ⟨hzS, fun h => h.elim (fun hzf => hzQ (hzf ▸ hfQ)) (fun hzA => hzQ (hAQ hzA))⟩
                          · rintro ⟨hzS, hnot⟩
                            by_cases hzQ : z ∈ Q
                            · exact Or.inl ⟨⟨fun hzf => hnot (Or.inl hzf), hzQ⟩, fun hzA => hnot (Or.inr hzA)⟩
                            · exact Or.inr ⟨hzS, hzQ⟩
                        have h_disj_u : Disjoint ((Q.erase f) \ A) (S \ Q) := by
                          rw [Finset.disjoint_left]
                          exact fun z hz1 hz2 =>
                            (Finset.mem_sdiff.mp hz2).2 (Finset.mem_erase.mp (Finset.mem_sdiff.mp hz1).1).2
                        rw [← h_union, Finset.prod_union h_disj_u]
                        have h_one : (∏ g ∈ S \ Q, (1 - retentionProb C t S (insert x B) τ (Function.update β x τ_tilde) g)) = 1 := by
                          refine Finset.prod_eq_one (fun g hg => ?_)
                          have hgt : invE < τ g := h_low.trans (h_out g hg)
                          unfold retentionProb
                          rw [if_neg (not_le.mpr hgt), sub_zero]
                        rw [h_one, mul_one]
                        refine Finset.prod_congr rfl (fun g _ => ?_)
                        rw [h_ret_invE g]
                    · have hD_emp : D = ∅ := by
                        rw [Finset.eq_empty_iff_forall_notMem]
                        intro g hgD
                        have hgf := hD_sub_f g hgD
                        rw [hgf] at hgD
                        exact hf_early (Finset.mem_filter.mp hgD).2.1
                      have hD_card0 : D.card = 0 := by rw [hD_emp]; simp
                      dsimp only [moveDerivBranch, Ψ]
                      rw [if_pos hD_card0, if_neg hf_early]
                      unfold retainProd
                      rw [if_pos hA, if_pos hA_er]
                      congr 1
                      · exact Finset.prod_congr rfl (fun g _ => h_ret_univ τ g)
                      · have h_union : ((Q.erase f) \ A) ∪ (insert f (S \ Q)) = S \ A := by
                          ext z
                          simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
                          refine ⟨?_, ?_⟩
                          · rintro (⟨⟨hzf, hzQ⟩, hzA⟩ | (rfl | ⟨hzS, hzQ⟩))
                            · exact ⟨hQS hzQ, hzA⟩
                            · exact ⟨hfS, hf_notA⟩
                            · exact ⟨hzS, fun hzA => hzQ (hAQ hzA)⟩
                          · rintro ⟨hzS, hzA⟩
                            by_cases hzf : z = f
                            · exact Or.inr (Or.inl hzf)
                            · by_cases hzQ : z ∈ Q
                              · exact Or.inl ⟨⟨hzf, hzQ⟩, hzA⟩
                              · exact Or.inr (Or.inr ⟨hzS, hzQ⟩)
                        have h_disj_u : Disjoint ((Q.erase f) \ A) (insert f (S \ Q)) := by
                          rw [Finset.disjoint_left]
                          intro z hz1 hz2
                          obtain ⟨hzf, hzQ⟩ := Finset.mem_erase.mp (Finset.mem_sdiff.mp hz1).1
                          rcases Finset.mem_insert.mp hz2 with rfl | hzSQ
                          · exact hzf rfl
                          · exact (Finset.mem_sdiff.mp hzSQ).2 hzQ
                        rw [← h_union, Finset.prod_union h_disj_u]
                        have h_one : (∏ g ∈ insert f (S \ Q), (1 - retentionProb C t S (insert x B) τ (Function.update β x τ_tilde) g)) = 1 := by
                          refine Finset.prod_eq_one (fun g hg => ?_)
                          unfold retentionProb
                          rcases Finset.mem_insert.mp hg with rfl | hgSQ
                          · rw [if_neg hf_early, sub_zero]
                          · have hgt : invE < τ g := h_low.trans (h_out g hgSQ)
                            rw [if_neg (not_le.mpr hgt), sub_zero]
                        rw [h_one, mul_one]
                        refine Finset.prod_congr rfl (fun g _ => ?_)
                        rw [h_ret_univ τ g]
                  · push_neg at h_out
                    obtain ⟨g₀, hg₀, hle⟩ := h_out
                    have hi0 : I_late τ = 0 :=
                      Finset.prod_eq_zero hg₀ (if_neg (not_lt.mpr hle))
                    have hc0 : cyl Q τ = 0 := by
                      change (∏ g ∈ Q, if τ g ≤ τ_tilde then (1 : ℝ) else 0) * I_late τ = 0
                      rw [hi0, mul_zero]
                    rw [hc0, hi0, zero_mul, zero_mul, mul_zero]
                · push_neg at h_in
                  obtain ⟨g₀, hg₀, hgt⟩ := h_in
                  have hq0 : (∏ g ∈ Q, if τ g ≤ τ_tilde then (1 : ℝ) else 0) = 0 :=
                    Finset.prod_eq_zero hg₀ (if_neg (not_le.mpr hgt))
                  have hc0 : cyl Q τ = 0 := by dsimp only [cyl]; rw [hq0, zero_mul]
                  rw [hc0, hq0, zero_mul, zero_mul]
              simp_rw [h_pt_Ψ]
              have hI_meas : Measurable I_late :=
                Finset.measurable_prod (S \ Q) (fun g _ =>
                  Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply g))
                    measurable_const measurable_const)
              have hI_bounds : ∀ ω, 0 ≤ I_late ω ∧ I_late ω ≤ 1 := by
                intro ω; dsimp only [I_late]
                exact ⟨Finset.prod_nonneg (fun _ _ => by split_ifs <;> norm_num),
                  Finset.prod_le_one (fun _ _ => by split_ifs <;> norm_num) (fun _ _ => by split_ifs <;> norm_num)⟩
              have hI_indep : ∀ ω₁ ω₂ : Fin n → ℝ, (∀ i, i ∉ Q → ω₁ i = ω₂ i) → I_late ω₁ = I_late ω₂ := by
                intro ω₁ ω₂ h_eq; dsimp only [I_late]
                refine Finset.prod_congr rfl (fun g hg => ?_)
                rw [h_eq g (Finset.mem_sdiff.mp hg).2]
              have hΨ_meas : Measurable Ψ := by
                let β_fn1 : (Fin n → ℝ) × ℝ × (Fin n → ℝ) → (Fin n → ℝ) :=
                  fun p => Function.update (β_cont p.2.2) f invE
                let β_fn2 : (Fin n → ℝ) × ℝ × (Fin n → ℝ) → (Fin n → ℝ) :=
                  fun p => Function.update (β_cont p.2.2) f p.2.1
                have hm_β1 : Measurable β_fn1 := by
                  rw [measurable_pi_iff]; intro z
                  by_cases hzf : z = f
                  · rw [hzf]; simp [β_fn1]
                  · by_cases hzx : z = x
                    · rw [hzx]; simp [β_fn1, Ne.symm hfx, β_cont]
                    · have hfn : (fun p => β_fn1 p z) =
                          fun p => if z ∈ S \ Q then p.2.2 z else β z := by
                        ext p; dsimp only [β_fn1, β_cont]
                        rw [Function.update_of_ne hzf, Function.update_of_ne hzx]
                      rw [hfn]
                      by_cases hzSQ : z ∈ S \ Q
                      · simp only [if_pos hzSQ]
                        exact (measurable_pi_apply z).comp (measurable_snd.comp measurable_snd)
                      · simp only [if_neg hzSQ]
                        exact measurable_const
                have hm_β2 : Measurable β_fn2 := by
                  rw [measurable_pi_iff]; intro z
                  by_cases hzf : z = f
                  · rw [hzf]; simpa [β_fn2] using measurable_fst.comp measurable_snd
                  · by_cases hzx : z = x
                    · rw [hzx]; simp [β_fn2, Ne.symm hfx, β_cont]
                    · have hfn : (fun p => β_fn2 p z) =
                          fun p => if z ∈ S \ Q then p.2.2 z else β z := by
                        ext p; dsimp only [β_fn2, β_cont]
                        rw [Function.update_of_ne hzf, Function.update_of_ne hzx]
                      rw [hfn]
                      by_cases hzSQ : z ∈ S \ Q
                      · simp only [if_pos hzSQ]
                        exact (measurable_pi_apply z).comp (measurable_snd.comp measurable_snd)
                      · simp only [if_neg hzSQ]
                        exact measurable_const
                have hm1 := (h_meas_prod C ht_low (Q.erase f) (insert f B_cont) A Prod.fst β_fn1
                  measurable_fst hm_β1).2
                have hm2 := (h_meas_prod C ht_low (Q.erase f) (insert f B_cont) A Prod.fst β_fn2
                  measurable_fst hm_β2).2
                exact Measurable.ite
                  (measurableSet_le (measurable_fst.comp measurable_snd) measurable_const)
                  (measurable_const.mul hm1) hm2
              have hΨ_bdd : ∀ p, |Ψ p| ≤ 1 := by
                intro p; dsimp only [Ψ]
                split_ifs
                · obtain ⟨hp0, hp1⟩ := h_prod_bounds C ht_low ht_high (Q.erase f) (insert f B_cont)
                    p.1 (Function.update (β_cont p.2.2) f invE) A
                  have hlog_lo : 0 ≤ Real.log (Real.exp 1 * τ_tilde) := by
                    refine Real.log_nonneg ?_
                    calc (1 : ℝ) = Real.exp 1 * invE := h_exp_invE.symm
                      _ ≤ Real.exp 1 * τ_tilde := mul_le_mul_of_nonneg_left h_low.le (Real.exp_pos 1).le
                  have hlog_hi : Real.log (Real.exp 1 * τ_tilde) ≤ 1 := by
                    calc Real.log (Real.exp 1 * τ_tilde)
                        ≤ Real.log (Real.exp 1) := by
                          refine Real.log_le_log (mul_pos (Real.exp_pos 1) hτ_pos) ?_
                          calc Real.exp 1 * τ_tilde ≤ Real.exp 1 * 1 :=
                              mul_le_mul_of_nonneg_left (h_high.le.trans ht_high) (Real.exp_pos 1).le
                            _ = Real.exp 1 := mul_one _
                      _ = 1 := Real.log_exp 1
                  rw [abs_mul, abs_neg, abs_of_nonneg hlog_lo, abs_of_nonneg hp0]
                  exact mul_le_one₀ hlog_hi hp0 hp1
                · obtain ⟨hp0, hp1⟩ := h_prod_bounds C ht_low ht_high (Q.erase f) (insert f B_cont)
                    p.1 (Function.update (β_cont p.2.2) f p.2.1) A
                  rw [abs_of_nonneg hp0]; exact hp1
              have hΨ_in : ∀ (τ₁ τ₂ : Fin n → ℝ) (u : ℝ) (ω : Fin n → ℝ),
                  (∀ i ∈ Q.erase f, τ₁ i = τ₂ i) → Ψ (τ₁, u, ω) = Ψ (τ₂, u, ω) := by
                intro τ₁ τ₂ u ω h_eq
                have h_rp_eq : ∀ (β' : Fin n → ℝ),
                    retainProd C t (Q.erase f) (insert f B_cont) τ₁ β' A =
                      retainProd C t (Q.erase f) (insert f B_cont) τ₂ β' A := by
                  intro β'
                  have h_pr : ∀ v : ℝ,
                      presentSet (Q.erase f) (insert f B_cont) τ₁ β' v =
                        presentSet (Q.erase f) (insert f B_cont) τ₂ β' v := by
                    intro v; unfold presentSet; congr 1
                    refine Finset.filter_congr (fun g hg => ?_)
                    rw [h_eq g hg]
                  have h_rt : ∀ g ∈ Q.erase f,
                      retentionProb C t (Q.erase f) (insert f B_cont) τ₁ β' g =
                        retentionProb C t (Q.erase f) (insert f B_cont) τ₂ β' g := by
                    intro g hg; unfold retentionProb
                    rw [h_eq g hg]
                    split_ifs
                    · congr 1; congr 1; unfold deathTime; simp_rw [h_pr]
                    · rfl
                  unfold retainProd
                  rw [if_pos hA_er, if_pos hA_er]
                  congr 1
                  · exact Finset.prod_congr rfl (fun g hg => h_rt g (hA_er hg))
                  · refine Finset.prod_congr rfl (fun g hg => ?_)
                    rw [h_rt g (Finset.mem_sdiff.mp hg).1]
                dsimp only [Ψ]
                split_ifs
                · rw [h_rp_eq]
                · rw [h_rp_eq]
              have hΨ_out : ∀ (τ' : Fin n → ℝ) (u : ℝ) (ω₁ ω₂ : Fin n → ℝ),
                  (∀ i, i ∉ Q → ω₁ i = ω₂ i) → Ψ (τ', u, ω₁) = Ψ (τ', u, ω₂) := by
                intro τ' u ω₁ ω₂ h_eq
                have hβc : β_cont ω₁ = β_cont ω₂ := by
                  ext z; dsimp only [β_cont]
                  by_cases hzx : z = x
                  · rw [hzx]; simp
                  · simp only [Function.update_of_ne hzx]
                    split_ifs with hzSQ
                    · exact h_eq z (Finset.mem_sdiff.mp hzSQ).2
                    · rfl
                dsimp only [Ψ]; rw [hβc]
              have hH_meas : Measurable (fun τ => I_late τ * Ψ (τ, τ f, τ)) :=
                hI_meas.mul (hΨ_meas.comp (measurable_id.prodMk ((measurable_pi_apply f).prodMk measurable_id)))
              have hH_bdd : ∀ τ, |I_late τ * Ψ (τ, τ f, τ)| ≤ 2 := by
                intro τ
                rw [abs_mul, abs_of_nonneg (hI_bounds τ).1]
                have hle1 : I_late τ * |Ψ (τ, τ f, τ)| ≤ 1 :=
                  mul_le_one₀ (hI_bounds τ).2 (abs_nonneg _) (hΨ_bdd _)
                linarith
              change 0 ≤ ∫ τ, (∏ g ∈ Q, if τ g ≤ τ_tilde then (1 : ℝ) else 0) *
                (I_late τ * Ψ (τ, τ f, τ)) ∂(unifCubeMeasure n t₀)
              rw [h_rescale n hτ_pos h_high_t₀ Q _ hH_meas hH_bdd]
              refine mul_nonneg (pow_nonneg (div_nonneg hτ_pos.le ht₀_pos.le) _) ?_
              refine h_decouple2 n hτ_pos h_high_t₀ Q f hfQ I_late Ψ
                hI_meas hI_bounds hI_indep hΨ_meas hΨ_bdd hΨ_in hΨ_out (fun ω hI_ne hω_out => ?_)
              have h_ω_late : ∀ g ∈ S \ Q, τ_tilde < ω g := by
                intro g hg
                by_contra hnot
                apply hI_ne
                exact Finset.prod_eq_zero hg (if_neg hnot)
              have hDisj_sub : Disjoint (Q.erase f) B_cont := by
                rw [Finset.disjoint_left]
                intro z hz_er hz_Bc
                have hzQ : z ∈ Q := Finset.erase_subset f Q hz_er
                have hzS : z ∈ S := hQS hzQ
                simp only [B_cont, Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff] at hz_Bc
                rcases hz_Bc with rfl | (hzB | ⟨_, hz_notQ⟩)
                · exact hxS hzS
                · exact Finset.disjoint_left.mp hDisj hzS hzB
                · exact hz_notQ hzQ
              have hf_not_sub : f ∉ (Q.erase f) ∪ B_cont := by
                rw [Finset.mem_union, not_or]
                refine ⟨Finset.notMem_erase f Q, ?_⟩
                simp [B_cont, hfx, hfB, hfQ]
              have hβ_sub : ∀ b ∈ B_cont, invE ≤ β_cont ω b ∧ β_cont ω b ≤ t := by
                intro b hb
                dsimp only [β_cont]
                by_cases hbx : b = x
                · rw [hbx]; simp [h_low.le, h_high.le]
                · rw [Function.update_of_ne hbx]
                  simp only [B_cont, Finset.mem_insert, Finset.mem_union] at hb
                  rcases hb with rfl | (hbB | hbSQ)
                  · exact (hbx rfl).elim
                  · split_ifs with hSQ
                    · have hgt := h_ω_late b hSQ
                      exact ⟨(h_low.trans hgt).le, ((hω_out b (Finset.mem_sdiff.mp hSQ).2).2).trans ht₀_t⟩
                    · exact hβ b hbB
                  · rw [if_pos hbSQ]
                    have hgt := h_ω_late b hbSQ
                    exact ⟨(h_low.trans hgt).le, ((hω_out b (Finset.mem_sdiff.mp hbSQ).2).2).trans ht₀_t⟩
              let μ_τ : Measure (Fin n → ℝ) := unifCubeMeasure n τ_tilde
              haveI : IsProbabilityMeasure ((ENNReal.ofReal τ_tilde)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) τ_tilde)) :=
                h_unif1D_prob hτ_pos
              haveI : IsProbabilityMeasure μ_τ := by dsimp only [μ_τ, unifCubeMeasure]; infer_instance
              let γ_ω : ℝ → ℝ := fun u =>
                genMovingProb2 C τ_tilde t (Q.erase f) B_cont (β_cont ω) f A u
              let c_ω : ℝ := γ_ω invE
              have hγ_cont : ContinuousOn γ_ω (Set.Icc invE τ_tilde) := by
                let L : ℝ := (((A.card : ℝ) + (((Q.erase f) \ A).card : ℝ)) * Real.exp 1)
                have hL_nn : 0 ≤ L := by dsimp only [L]; positivity
                have h_int_u : ∀ u ∈ Set.Icc invE τ_tilde,
                    Integrable (fun τ' => retainProd C t (Q.erase f) (insert f B_cont) τ'
                      (Function.update (β_cont ω) f u) A) μ_τ := by
                  intro u _
                  have hm := (h_meas_prod C ht_low (Q.erase f) (insert f B_cont) A id
                    (fun _ => Function.update (β_cont ω) f u) measurable_id measurable_const).2
                  exact Integrable.of_mem_Icc 0 1 hm.aemeasurable
                    (Filter.Eventually.of_forall (fun τ' =>
                      h_prod_bounds C ht_low ht_high (Q.erase f) (insert f B_cont) τ' _ A))
                have h_lip_γ : LipschitzOnWith ⟨L, hL_nn⟩ γ_ω (Set.Icc invE τ_tilde) := by
                  refine LipschitzOnWith.of_dist_le_mul (fun v₁ hv₁ v₂ hv₂ => ?_)
                  simp only [NNReal.coe_mk, Real.dist_eq, γ_ω, genMovingProb2, genSurvivalLaw2]
                  change |(∫ τ', retainProd C t (Q.erase f) (insert f B_cont) τ'
                        (Function.update (β_cont ω) f v₁) A ∂μ_τ) -
                      (∫ τ', retainProd C t (Q.erase f) (insert f B_cont) τ'
                        (Function.update (β_cont ω) f v₂) A ∂μ_τ)| ≤ L * |v₁ - v₂|
                  rw [← integral_sub (h_int_u v₁ hv₁) (h_int_u v₂ hv₂)]
                  have hv₁_t : v₁ ∈ Set.Icc invE t := ⟨hv₁.1, hv₁.2.trans h_high.le⟩
                  have hv₂_t : v₂ ∈ Set.Icc invE t := ⟨hv₂.1, hv₂.2.trans h_high.le⟩
                  calc |∫ τ', (retainProd C t (Q.erase f) (insert f B_cont) τ' (Function.update (β_cont ω) f v₁) A -
                          retainProd C t (Q.erase f) (insert f B_cont) τ' (Function.update (β_cont ω) f v₂) A) ∂μ_τ|
                      ≤ ∫ τ', |retainProd C t (Q.erase f) (insert f B_cont) τ' (Function.update (β_cont ω) f v₁) A -
                          retainProd C t (Q.erase f) (insert f B_cont) τ' (Function.update (β_cont ω) f v₂) A| ∂μ_τ :=
                        abs_integral_le_integral_abs
                    _ ≤ ∫ _τ', (L * |v₁ - v₂|) ∂μ_τ := by
                        refine integral_mono ((h_int_u v₁ hv₁).sub (h_int_u v₂ hv₂)).abs (integrable_const _) ?_
                        intro τ'
                        exact (h_lip_retain C (Q.erase f) B_cont f A τ' (β_cont ω)
                          hP ht_low ht_high hf_not_sub hA_er).1 v₁ hv₁_t v₂ hv₂_t
                    _ = L * |v₁ - v₂| := by simp [integral_const]
                exact h_lip_γ.continuousOn
              have h_card_lt : (Q.erase f).card < k := by
                have h1 : (Q.erase f).card < Q.card := Finset.card_erase_lt_of_mem hfQ
                have h2 : Q.card ≤ S.card := Finset.card_le_card hQS
                omega
              have h_uγ_mono : MonotoneOn (fun u => u * γ_ω u) (Set.Icc invE τ_tilde) :=
                ih (Q.erase f).card h_card_lt τ_tilde t (Q.erase f) B_cont (β_cont ω) f A rfl
                  hC hP hSD h_low.le h_high.le ht_high hDisj_sub hβ_sub hf_not_sub hA_er
              have h_γ_lower : ∀ u ∈ Set.Icc invE τ_tilde, (Real.exp 1 * u)⁻¹ * c_ω ≤ γ_ω u := by
                intro u hu
                have h_le_uγ : invE * c_ω ≤ u * γ_ω u :=
                  h_uγ_mono ⟨le_rfl, h_low.le⟩ hu hu.1
                have hu_pos : 0 < u := h_invE_pos.trans_le hu.1
                have h_mul := mul_le_mul_of_nonneg_left h_le_uγ (inv_nonneg.mpr hu_pos.le)
                have h_lhs : u⁻¹ * (invE * c_ω) = (Real.exp 1 * u)⁻¹ * c_ω := by
                  rw [h_invE_eq]; have := hu_pos.ne'; field_simp
                have h_rhs : u⁻¹ * (u * γ_ω u) = γ_ω u := inv_mul_cancel_left₀ hu_pos.ne' (γ_ω u)
                rwa [h_lhs, h_rhs] at h_mul
              have h_inner_Ψ : ∀ u : ℝ,
                  (∫ τ', Ψ (τ', u, ω) ∂(unifCubeMeasure n τ_tilde)) =
                    if u ≤ invE then -Real.log (Real.exp 1 * τ_tilde) * c_ω else γ_ω u := by
                intro u
                dsimp only [Ψ]
                split_ifs with hu_le
                · dsimp only [c_ω, γ_ω, genMovingProb2, genSurvivalLaw2]
                  exact integral_const_mul (-Real.log (Real.exp 1 * τ_tilde)) _
                · rfl
              simp_rw [h_inner_Ψ]
              exact h_pay_1d h_low γ_ω hγ_cont h_γ_lower
            · push_neg at h_has_disp
              refine integral_nonneg (fun τ => ?_)
              dsimp only [Pi.zero_apply]
              by_cases h_in_out : (∀ g ∈ Q, τ g ≤ τ_tilde) ∧ (∀ g ∈ S \ Q, τ_tilde < τ g)
              · obtain ⟨h_in, h_out⟩ := h_in_out
                refine mul_nonneg (h_cyl_bounds Q τ).1 ?_
                have hU_eq := h_pres_UQ τ h_in h_out
                let D := S.filter (fun g => τ g ≤ invE ∧
                  g ∈ C (presentSet S B τ β τ_tilde) \ C (insert x (presentSet S B τ β τ_tilde)))
                have hD_card : D.card ≤ 1 := by
                  have hsub : D ⊆ C U_Q \ C (insert x U_Q) := by
                    intro g hg
                    have h := (Finset.mem_filter.mp hg).2.2
                    rwa [hU_eq] at h
                  exact (Finset.card_le_card hsub).trans (hSD U_Q x hxUQ)
                change 0 ≤ moveDerivBranch C t S B β x A D τ τ_tilde
                have hφ_nn := (h_prod_bounds C ht_low ht_high S (insert x B) τ
                  (Function.update β x τ_tilde) A).1
                rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hD_card with hD0 | hD1
                · dsimp only [moveDerivBranch]; rw [if_pos hD0]; exact hφ_nn
                · have hf_memD : D.min' (Finset.card_pos.mp (by omega)) ∈ D :=
                    Finset.min'_mem D (Finset.card_pos.mp (by omega))
                  obtain ⟨hfS, hf_early, hf_d⟩ := Finset.mem_filter.mp hf_memD
                  rw [hU_eq] at hf_d
                  have hfQ : D.min' (Finset.card_pos.mp (by omega)) ∈ Q := by
                    by_contra hnotQ
                    have hgt := h_out _ (Finset.mem_sdiff.mpr ⟨hfS, hnotQ⟩)
                    linarith [h_low]
                  have hfA : D.min' (Finset.card_pos.mp (by omega)) ∈ A := by
                    by_contra hnotA
                    exact h_has_disp _ (Finset.mem_sdiff.mpr ⟨hfQ, hnotA⟩) hf_d
                  dsimp only [moveDerivBranch]
                  rw [if_neg (by omega : ¬ D.card = 0), dif_pos hD1, if_pos hfA]
                  refine add_nonneg hφ_nn (mul_nonneg ?_ ?_)
                  · exact Finset.prod_nonneg (fun g _ =>
                      (h_ret_bounds C ht_low ht_high S (insert x B) τ
                        (Function.update β x τ_tilde) g).1)
                  · exact Finset.prod_nonneg (fun g _ =>
                      sub_nonneg.mpr (h_ret_bounds C ht_low ht_high S (insert x B) τ
                        (Function.update β x τ_tilde) g).2)
              · have hc0 : cyl Q τ = 0 := by
                  rw [not_and_or] at h_in_out
                  rcases h_in_out with h_not_in | h_not_out
                  · push_neg at h_not_in
                    obtain ⟨g₀, hg₀, hgt⟩ := h_not_in
                    have hq0 : (∏ g ∈ Q, if τ g ≤ τ_tilde then (1 : ℝ) else 0) = 0 :=
                      Finset.prod_eq_zero hg₀ (if_neg (not_le.mpr hgt))
                    dsimp only [cyl]; rw [hq0, zero_mul]
                  · push_neg at h_not_out
                    obtain ⟨g₀, hg₀, hle⟩ := h_not_out
                    have hi0 : (∏ g ∈ S \ Q, if τ_tilde < τ g then (1 : ℝ) else 0) = 0 :=
                      Finset.prod_eq_zero hg₀ (if_neg (not_lt.mpr hle))
                    dsimp only [cyl]; rw [hi0, mul_zero]
                rw [hc0, zero_mul]
          · obtain ⟨a₀, ha₀A, ha₀_notQ⟩ := Finset.not_subset.mp hAQ
            have ha₀SQ : a₀ ∈ S \ Q := Finset.mem_sdiff.mpr ⟨hA ha₀A, ha₀_notQ⟩
            have h_zero_fn : (fun τ => cyl Q τ * moveDeriv C t S B β x A τ τ_tilde) = fun _ => 0 := by
              ext τ
              by_cases h_gt : τ_tilde < τ a₀
              · have h_not_early : ¬ (τ a₀ ≤ invE) := not_le.mpr (h_low.trans h_gt)
                have hθ_a₀ : retentionProb C t S (insert x B) τ (Function.update β x τ_tilde) a₀ = 0 := by
                  unfold retentionProb; exact if_neg h_not_early
                have h_prodA_zero : (∏ g ∈ A, retentionProb C t S (insert x B) τ (Function.update β x τ_tilde) g) = 0 :=
                  Finset.prod_eq_zero ha₀A hθ_a₀
                have hφ_zero : retainProd C t S (insert x B) τ (Function.update β x τ_tilde) A = 0 := by
                  unfold retainProd; rw [if_pos hA, h_prodA_zero, zero_mul]
                have h_md_zero : moveDeriv C t S B β x A τ τ_tilde = 0 := by
                  let D := S.filter (fun g => τ g ≤ invE ∧
                    g ∈ C (presentSet S B τ β τ_tilde) \ C (insert x (presentSet S B τ β τ_tilde)))
                  change moveDerivBranch C t S B β x A D τ τ_tilde = 0
                  dsimp only [moveDerivBranch]
                  split_ifs with h0 h1 hfA
                  · exact hφ_zero
                  · have hD_pos : 0 < D.card := by omega
                    have hf_mem : D.min' (Finset.card_pos.mp hD_pos) ∈ D :=
                      Finset.min'_mem D (Finset.card_pos.mp hD_pos)
                    have hf_early : τ (D.min' (Finset.card_pos.mp hD_pos)) ≤ invE :=
                      (Finset.mem_filter.mp hf_mem).2.1
                    have ha₀_ne : a₀ ≠ D.min' (Finset.card_pos.mp hD_pos) :=
                      fun heq => h_not_early (heq ▸ hf_early)
                    have ha₀_er : a₀ ∈ A.erase (D.min' (Finset.card_pos.mp hD_pos)) :=
                      Finset.mem_erase.mpr ⟨ha₀_ne, ha₀A⟩
                    have h_er_zero : (∏ g ∈ A.erase (D.min' (Finset.card_pos.mp hD_pos)),
                        retentionProb C t S (insert x B) τ (Function.update β x τ_tilde) g) = 0 :=
                      Finset.prod_eq_zero ha₀_er hθ_a₀
                    rw [hφ_zero, h_er_zero, zero_mul, add_zero]
                  · rw [h_prodA_zero, zero_mul, mul_zero]
                  · rfl
                rw [h_md_zero, mul_zero]
              · have hi0 : (∏ g ∈ S \ Q, if τ_tilde < τ g then (1 : ℝ) else 0) = 0 :=
                  Finset.prod_eq_zero ha₀SQ (if_neg h_gt)
                have hc0 : cyl Q τ = 0 := by dsimp only [cyl]; rw [hi0, mul_zero]
                rw [hc0, zero_mul]
            rw [h_zero_fn, integral_zero]
    intro t₀ t S B β x A hC hP hSD ht₀_low ht₀_t ht_high hDisj hβ hxSB hA
    have h_mono := h_ind_mono S.card t₀ t S B β x A rfl hC hP hSD ht₀_low ht₀_t ht_high hDisj hβ hxSB hA
    refine ⟨h_mono, fun τ_tilde hτ => ?_⟩
    have h_le := h_mono ⟨le_rfl, ht₀_low⟩ hτ hτ.1
    have hτ_pos : 0 < τ_tilde := h_invE_pos.trans_le hτ.1
    have h_mul := mul_le_mul_of_nonneg_left h_le (inv_nonneg.mpr hτ_pos.le)
    have h_lhs : τ_tilde⁻¹ * (invE * genMovingProb2 C t₀ t S B β x A invE) =
        (1 / (Real.exp 1 * τ_tilde)) * genMovingProb2 C t₀ t S B β x A invE := by
      rw [h_invE_eq]; have := hτ_pos.ne'; field_simp
    have h_rhs : τ_tilde⁻¹ * (τ_tilde * genMovingProb2 C t₀ t S B β x A τ_tilde) =
        genMovingProb2 C t₀ t S B β x A τ_tilde :=
      inv_mul_cancel_left₀ hτ_pos.ne' _
    rwa [h_lhs, h_rhs] at h_mul

  clear h_meas_prod h_unif1D_prob h_lip_retain h_moveDeriv_meas h_moveDeriv_bdd h_ftc_fubini2
    h_rescale h_decouple2 h_pay_1d moveDeriv moveDerivBranch

  have h_conj1b : ∀ (n : ℕ) (v : ItemValuation n) (t₀ t : ℝ)
      (S B : Finset (Fin n)) (β : Fin n → ℝ) (x : Fin n) (A : Finset (Fin n)),
      IsGSValuation v → invE ≤ t₀ → t₀ ≤ t → t ≤ 1 →
      Disjoint S B → (∀ b ∈ B, invE ≤ β b ∧ β b ≤ t) → x ∉ S ∪ B → A ⊆ S →
        MonotoneOn
          (fun τ_tilde => τ_tilde * genMovingProb2 (canonicalDemand v) t₀ t S B β x A τ_tilde)
          (Set.Icc invE t₀) ∧
        ∀ τ_tilde ∈ Set.Icc invE t₀,
          (1 / (Real.exp 1 * τ_tilde)) *
              genMovingProb2 (canonicalDemand v) t₀ t S B β x A invE ≤
            genMovingProb2 (canonicalDemand v) t₀ t S B β x A τ_tilde := by
    intro n v t₀ t S B β x A hv ht₀_low ht₀_t ht_high hDisj hβ hxSB hA
    obtain ⟨hC, hP, hSD⟩ := h_part11 n v hv
    exact h_conj1a n (canonicalDemand v) t₀ t S B β x A hC hP hSD ht₀_low ht₀_t ht_high hDisj hβ hxSB hA

  have h_conj2 : ∀ (n : ℕ) (v : ItemValuation n) (S : Finset (Fin n)) (x : Fin n) (t : ℝ)
      (A : Finset (Fin n)),
      IsGSValuation v → x ∉ S → x ∈ canonicalDemand v (insert x S) →
      invE ≤ t → t ≤ 1 →
        (1 / (Real.exp 1 * t)) * survivalLaw (contractVal v x) S t A ≤
          survivalLaw v S t A := by
    intro n v S x t A hv hxS hxD ht_low ht_high
    by_cases hAS : A ⊆ S
    · obtain ⟨_, _, h_comm⟩ := h_part13 n v S x hv hxS hxD
      let C := canonicalDemand v
      let C' := canonicalDemand (contractVal v x)
      let β₀ : Fin n → ℝ := fun _ => t
      have hx_emp : x ∉ S ∪ ∅ := by simp [hxS]
      have h_vac : ∀ b ∈ (∅ : Finset (Fin n)), invE ≤ β₀ b ∧ β₀ b ≤ t := by simp
      have h_ineq := (h_conj1b n v t t S ∅ β₀ x A hv ht_low le_rfl ht_high
        (Finset.disjoint_empty_right S) h_vac hx_emp hAS).2 t ⟨ht_low, le_rfl⟩
      have h_end_t : genMovingProb2 C t t S ∅ β₀ x A t = survivalLaw v S t A := by
        dsimp only [genMovingProb2, survivalLaw, genSurvivalLaw, genSurvivalLaw2, C]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun τ => ?_))
        have hβ_eq : Function.update β₀ x t = β₀ := by
          ext z; by_cases hzx : z = x <;> simp [β₀, hzx]
        rw [hβ_eq]
        have h_dt_eq : ∀ g : Fin n,
            deathTime C t S (insert x ∅) τ β₀ g =
              deathTime C t S ∅ τ β₀ g := by
          intro g
          unfold deathTime
          refine congrArg sInf (Set.ext (fun u => ?_))
          by_cases hut : u = t
          · rw [hut]; simp
          · simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff, hut, or_false]
            by_cases h_le : u ≤ t
            · have h_lt : u < t := lt_of_le_of_ne h_le hut
              have h_pr : presentSet S (insert x ∅) τ β₀ u = presentSet S ∅ τ β₀ u := by
                ext z; simp [presentSet, β₀, not_le.mpr h_lt]
              rw [h_pr]
            · simp [h_le]
        change retainProd C t S (insert x ∅) τ β₀ A = retainProd C t S ∅ τ β₀ A
        unfold retainProd retentionProb
        simp_rw [h_dt_eq]
      have h_end_invE : genMovingProb2 C t t S ∅ β₀ x A invE = survivalLaw (contractVal v x) S t A := by
        dsimp only [genMovingProb2, survivalLaw, genSurvivalLaw, genSurvivalLaw2]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun τ => ?_))
        let β₁ := Function.update β₀ x invE
        have h_dt_eq : ∀ g ∈ S,
            deathTime C t S (insert x ∅) τ β₁ g =
              deathTime C' t S ∅ τ β₀ g := by
          intro g hgS
          have hgx : g ≠ x := fun h => hxS (h ▸ hgS)
          unfold deathTime
          refine congrArg sInf (congrArg (· ∪ {t}) (Set.ext (fun u => ?_)))
          simp only [Set.mem_setOf_eq]
          refine ⟨fun ⟨hu1, hu2, hnot⟩ => ⟨hu1, hu2, ?_⟩, fun ⟨hu1, hu2, hnot⟩ => ⟨hu1, hu2, ?_⟩⟩
          · have h_pr1 : presentSet S (insert x ∅) τ β₁ u = insert x (S.filter (fun z => τ z ≤ u)) := by
              ext z; by_cases hzx : z = x
              · rw [hzx]; simp [presentSet, β₁, hu1]
              · simp [presentSet, hzx]
            have h_pr0 : presentSet S ∅ τ β₀ u = S.filter (fun z => τ z ≤ u) := by
              ext z; simp [presentSet]
            rw [h_pr1] at hnot
            rw [h_pr0]
            have h_sub : S.filter (fun z => τ z ≤ u) ⊆ S := Finset.filter_subset _ S
            dsimp only [C, C'] at hnot ⊢
            rw [h_comm _ h_sub]
            exact fun hg_er => hnot (Finset.erase_subset x _ hg_er)
          · have h_pr1 : presentSet S (insert x ∅) τ β₁ u = insert x (S.filter (fun z => τ z ≤ u)) := by
              ext z; by_cases hzx : z = x
              · rw [hzx]; simp [presentSet, β₁, hu1]
              · simp [presentSet, hzx]
            have h_pr0 : presentSet S ∅ τ β₀ u = S.filter (fun z => τ z ≤ u) := by
              ext z; simp [presentSet]
            rw [h_pr0] at hnot
            rw [h_pr1]
            have h_sub : S.filter (fun z => τ z ≤ u) ⊆ S := Finset.filter_subset _ S
            intro hg_in
            apply hnot
            dsimp only [C, C'] at hg_in ⊢
            rw [h_comm _ h_sub]
            exact Finset.mem_erase.mpr ⟨hgx, hg_in⟩
        have h_rt_eq : ∀ g ∈ S,
            retentionProb C t S (insert x ∅) τ β₁ g =
              retentionProb C' t S ∅ τ β₀ g := by
          intro g hgS; unfold retentionProb; rw [h_dt_eq g hgS]
        change retainProd C t S (insert x ∅) τ β₁ A = retainProd C' t S ∅ τ β₀ A
        unfold retainProd
        rw [if_pos hAS, if_pos hAS]
        refine congrArg₂ (· * ·) ?_ ?_
        · exact Finset.prod_congr rfl (fun g hgA => h_rt_eq g (hAS hgA))
        · refine Finset.prod_congr rfl (fun g hgSA => ?_)
          rw [h_rt_eq g (Finset.mem_sdiff.mp hgSA).1]
      rwa [h_end_invE, h_end_t] at h_ineq
    · have h0_1 : survivalLaw (contractVal v x) S t A = 0 := by
        dsimp only [survivalLaw, genSurvivalLaw, genSurvivalLaw2]
        have hfn : (fun τ => retainProd (canonicalDemand (contractVal v x)) t S ∅ τ (fun _ => t) A) =
            fun _ => 0 := by ext τ; simp [retainProd, hAS]
        rw [hfn, integral_zero]
      have h0_2 : survivalLaw v S t A = 0 := by
        dsimp only [survivalLaw, genSurvivalLaw, genSurvivalLaw2]
        have hfn : (fun τ => retainProd (canonicalDemand v) t S ∅ τ (fun _ => t) A) =
            fun _ => 0 := by ext τ; simp [retainProd, hAS]
        rw [hfn, integral_zero]
      rw [h0_1, h0_2, mul_zero]

  have h_conj3 : ∀ (n : ℕ) (v : ItemValuation n) (S : Finset (Fin n)) (x : Fin n) (t : ℝ)
      (A : Finset (Fin n)),
      IsGSValuation v → x ∉ S → t ≤ 1 →
        (0 ≤ survivalAcceptProb v x A S t ∧ survivalAcceptProb v x A S t ≤ 1) ∧
        (invE < t → x ∈ canonicalDemand v (insert x S) →
          survivalLaw v S t A * survivalAcceptProb v x A S t =
            (1 / (Real.exp 1 * t)) * survivalLaw (contractVal v x) S t A) := by
    intro n v S x t A hv hxS ht_high
    have h_surv_nn : invE ≤ t → ∀ w : ItemValuation n, 0 ≤ survivalLaw w S t A := by
      intro ht_low w
      dsimp only [survivalLaw, genSurvivalLaw, genSurvivalLaw2]
      exact integral_nonneg (fun τ => (h_prod_bounds (canonicalDemand w) ht_low ht_high S ∅ τ (fun _ => t) A).1)
    have h_alg_le : ∀ a b c : ℝ, 0 ≤ c → 0 ≤ b → 0 < a → c * b ≤ a →
        0 ≤ c * (b / a) ∧ c * (b / a) ≤ 1 := by
      intro a b c hc hb ha hcb
      refine ⟨mul_nonneg hc (div_nonneg hb ha.le), ?_⟩
      rw [← mul_div_assoc]
      exact (div_le_one ha).mpr hcb
    have h_alg_eq : ∀ a b c : ℝ, a ≠ 0 → a * (c * (b / a)) = c * b := by
      intro a b c ha
      field_simp
    refine ⟨?_, ?_⟩
    · unfold survivalAcceptProb
      by_cases ht_le : t ≤ invE
      · rw [if_pos ht_le]
        exact ⟨le_rfl, zero_le_one⟩
      · rw [if_neg ht_le]
        by_cases hx_notD : x ∉ canonicalDemand v (insert x S)
        · rw [if_pos hx_notD]
          exact ⟨le_rfl, zero_le_one⟩
        · rw [if_neg hx_notD]
          by_cases h_zero : survivalLaw v S t A = 0
          · rw [if_pos h_zero]
            exact ⟨le_rfl, zero_le_one⟩
          · rw [if_neg h_zero]
            have ht_gt : invE < t := lt_of_not_ge ht_le
            have ht_low : invE ≤ t := ht_gt.le
            have ht_pos : 0 < t := h_invE_pos.trans ht_gt
            have hxD : x ∈ canonicalDemand v (insert x S) := Classical.not_not.mp hx_notD
            have h_num_nn : 0 ≤ survivalLaw (contractVal v x) S t A := h_surv_nn ht_low (contractVal v x)
            have h_den_nn : 0 ≤ survivalLaw v S t A := h_surv_nn ht_low v
            have h_den_pos : 0 < survivalLaw v S t A := lt_of_le_of_ne h_den_nn (Ne.symm h_zero)
            have h_comp := h_conj2 n v S x t A hv hxS hxD ht_low ht_high
            have h_pos_et : 0 < Real.exp 1 * t := mul_pos (Real.exp_pos 1) ht_pos
            exact h_alg_le (survivalLaw v S t A) (survivalLaw (contractVal v x) S t A)
              (1 / (Real.exp 1 * t)) (one_div_nonneg.mpr h_pos_et.le) h_num_nn h_den_pos h_comp
    · intro ht_gt hxD
      have ht_low : invE ≤ t := ht_gt.le
      have ht_pos : 0 < t := h_invE_pos.trans ht_gt
      have h_pos_et : 0 < Real.exp 1 * t := mul_pos (Real.exp_pos 1) ht_pos
      unfold survivalAcceptProb
      rw [if_neg (not_le.mpr ht_gt), if_neg (fun h => h hxD)]
      by_cases h_zero : survivalLaw v S t A = 0
      · rw [if_pos h_zero, h_zero, mul_zero]
        have h_comp := h_conj2 n v S x t A hv hxS hxD ht_low ht_high
        rw [h_zero] at h_comp
        have h_nn : 0 ≤ (1 / (Real.exp 1 * t)) * survivalLaw (contractVal v x) S t A :=
          mul_nonneg (one_div_nonneg.mpr h_pos_et.le) (h_surv_nn ht_low (contractVal v x))
        exact (le_antisymm h_comp h_nn).symm
      · rw [if_neg h_zero]
        exact h_alg_eq (survivalLaw v S t A) (survivalLaw (contractVal v x) S t A)
          (1 / (Real.exp 1 * t)) h_zero

  exact ⟨h_conj1a, h_conj1b, h_conj2, h_conj3⟩

end DelayInternal

/-- **Theorem B.5 (`thm:delay`) — Moving One Timestamp (General Choice Rules)**:
For any persistent, single-displacement choice rule `C`, times `1/e ≤ t₀ ≤ t ≤ 1`, disjoint `S, B`
with `β_b ∈ [1/e, t]`, `x ∉ S ∪ B`, and `A ⊆ S`, `τ̃ ↦ τ̃ μ̃(τ̃)` is nondecreasing on `[1/e, t₀]`,
so `μ̃(τ̃) ≥ (1 / (e τ̃)) μ̃(1/e)` for every `τ̃ ∈ [1/e, t₀]`. -/
theorem thm_B_5_delay_choice_rule
    {n : ℕ} (C : Finset (Fin n) → Finset (Fin n)) (t₀ t : ℝ)
    (S B : Finset (Fin n)) (β : Fin n → ℝ) (x : Fin n) (A : Finset (Fin n))
    (hC : IsChoiceRule C) (hP : HasPersistence C) (hSD : HasSingleDisplacement C)
    (ht₀ : invE ≤ t₀) (ht₀t : t₀ ≤ t) (ht1 : t ≤ 1)
    (hSB : Disjoint S B) (hβ : ∀ b ∈ B, invE ≤ β b ∧ β b ≤ t)
    (hx : x ∉ S ∪ B) (hAS : A ⊆ S) :
    MonotoneOn (fun τ_tilde => τ_tilde * genMovingProb2 C t₀ t S B β x A τ_tilde)
      (Set.Icc invE t₀) ∧
    ∀ τ_tilde ∈ Set.Icc invE t₀,
      (1 / (Real.exp 1 * τ_tilde)) * genMovingProb2 C t₀ t S B β x A invE ≤
        genMovingProb2 C t₀ t S B β x A τ_tilde :=
  DelayInternal.thm_selection_two_time_delay_and_comparison.1 n C t₀ t S B β x A
    hC hP hSD ht₀ ht₀t ht1 hSB hβ hx hAS

/-- **Theorem B.5 (`thm:delay`) — Moving One Timestamp for Gross Substitutes `D_v`**:
Specializes `thm_B_5_delay_choice_rule` to `D_v` (`canonicalDemand v`) for any GS valuation `v`. -/
theorem thm_B_5_delay
    {n : ℕ} (v : ItemValuation n) (t₀ t : ℝ)
    (S B : Finset (Fin n)) (β : Fin n → ℝ) (x : Fin n) (A : Finset (Fin n))
    (hv : IsGSValuation v)
    (ht₀ : invE ≤ t₀) (ht₀t : t₀ ≤ t) (ht1 : t ≤ 1)
    (hSB : Disjoint S B) (hβ : ∀ b ∈ B, invE ≤ β b ∧ β b ≤ t)
    (hx : x ∉ S ∪ B) (hAS : A ⊆ S) :
    MonotoneOn
      (fun τ_tilde => τ_tilde * genMovingProb2 (canonicalDemand v) t₀ t S B β x A τ_tilde)
      (Set.Icc invE t₀) ∧
    ∀ τ_tilde ∈ Set.Icc invE t₀,
      (1 / (Real.exp 1 * τ_tilde)) *
          genMovingProb2 (canonicalDemand v) t₀ t S B β x A invE ≤
        genMovingProb2 (canonicalDemand v) t₀ t S B β x A τ_tilde :=
  DelayInternal.thm_selection_two_time_delay_and_comparison.2.1 n v t₀ t S B β x A
    hv ht₀ ht₀t ht1 hSB hβ hx hAS

/-- **Proposition B.1 (`prop:comparison`) — Contraction Comparison Inequality**:
For any GS valuation `v`, `x ∉ S` with `x ∈ D_v(S + x)`, `t ∈ [1/e, 1]`, and `A ⊆ S`,
`μ^v_{S, t}(A) ≥ (1 / (e t)) μ^{v / x}_{S, t}(A)`. -/
theorem prop_B_1_comparison
    {n : ℕ} (v : ItemValuation n) (S : Finset (Fin n)) (x : Fin n) (t : ℝ)
    (A : Finset (Fin n))
    (hv : IsGSValuation v) (hxS : x ∉ S) (hxD : x ∈ canonicalDemand v (insert x S))
    (ht₀ : invE ≤ t) (ht1 : t ≤ 1) :
    (1 / (Real.exp 1 * t)) * survivalLaw (contractVal v x) S t A ≤
      survivalLaw v S t A :=
  DelayInternal.thm_selection_two_time_delay_and_comparison.2.2.1 n v S x t A
    hv hxS hxD ht₀ ht1

/-- **Section 3.1 (`eq:accept`) & Appendix B.2 (`eq:accept-mass`) — Survival Acceptance Validity**:
For any GS valuation `v`, `x ∉ S`, and `t ≤ 1`, `0 ≤ α_x(A, S, t) ≤ 1`, and whenever `t > 1/e` and
`x ∈ D_v(S + x)`, `μ^v_{S, t}(A) α_x(A, S, t) = (1 / (e t)) μ^{v / x}_{S, t}(A)`. -/
theorem survivalAcceptProb_valid
    {n : ℕ} (v : ItemValuation n) (S : Finset (Fin n)) (x : Fin n) (t : ℝ)
    (A : Finset (Fin n))
    (hv : IsGSValuation v) (hxS : x ∉ S) (ht1 : t ≤ 1) :
    (0 ≤ survivalAcceptProb v x A S t ∧ survivalAcceptProb v x A S t ≤ 1) ∧
    (invE < t → x ∈ canonicalDemand v (insert x S) →
      survivalLaw v S t A * survivalAcceptProb v x A S t =
        (1 / (Real.exp 1 * t)) * survivalLaw (contractVal v x) S t A) :=
  DelayInternal.thm_selection_two_time_delay_and_comparison.2.2.2 n v S x t A hv hxS ht1

end

end GrossSubstitutesWelfare
