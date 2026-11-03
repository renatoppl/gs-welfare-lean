import GrossSubstitutesWelfare.Defs

set_option maxHeartbeats 4000000

/-!
# Appendix C: Proposition C.2 (Two Items), Proposition C.4 (No Per-Pair Guarantee) & 1-Bidder Transfer

Formalizes Appendix C (`app:lower`) of *Gross Substitutes Welfare in Random Order*:
- **Single-bidder selection-to-welfare transfer (`rem_C_single_bidder_transfer`)**: Restricting any
  online welfare algorithm at `m = 1` (`Fin 1`) yields an `OnlineSelectionAlg` with identical
  expected value and offline optimum, so every selection impossibility bound applies verbatim to
  welfare;
- **Proposition C.2 (`prop:two-items`)**: On `n = 2` items, no online algorithm beats `1 / 2 + δ`
  across nonnegative GS valuations;
- **Proposition C.4 (`prop:contracts`)**: On `m = n` items and unit-demand (monotone nonnegative GS)
  bidders with a unique optimal allocation `X*`, some optimal pair `(i, g ∈ X*_i)` is realized with
  probability at most `H_m / m`.
-/

namespace GrossSubstitutesWelfare

open Classical MeasureTheory

noncomputable section

namespace ContractsAndTwoItemsInternal

/-- **Proposition C.4 (`prop:contracts`) & Proposition C.2 (`prop:two-items`)**:
1. **Proposition C.4 (No per-pair guarantee)**: For every `m ≥ 1` and every online welfare
   algorithm on `m` items and `m` bidders, there is an instance of `m` unit-demand (nonnegative,
   monotone GS) valuations with a unique optimal allocation `X*` in which some optimal `(item, bidder)`
   pair is realized with probability at most `H_m / m`.
2. **Proposition C.2 (Two items)**: For every `δ > 0`, there is a finite nonempty family of
   nonnegative GS valuations on `2` items (with `OPT(v) > 0`) such that every online selection
   algorithm obtains expected value at most `(1 / 2 + δ) OPT(v)` on some `v` in the family. -/
def unitDemandReal {n : ℕ} (w : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  (S.sup (fun g => ((w g : ℝ) : WithBot ℝ))).unbotD 0

def unitDemandOfWeights {n : ℕ} (w : Fin n → ℝ) : ItemValuation n :=
  fun S => ((unitDemandReal w S : ℝ) : WithBot ℝ)

def contractsWeight {m : ℕ} (x₀ : Fin m) (τ : Equiv.Perm (Fin m)) (i g : Fin m) : ℝ :=
  if g = x₀ then 1 else if i = τ g then 2 else 0

def contractsVal {m : ℕ} (x₀ : Fin m) (τ : Equiv.Perm (Fin m)) : Fin m → ItemValuation m :=
  fun i => unitDemandOfWeights (contractsWeight x₀ τ i)

def contractsOptAlloc {m : ℕ} (τ : Equiv.Perm (Fin m)) : Fin m → Finset (Fin m) :=
  fun i => {τ.symm i}

def prefixList {n : ℕ} (π : Equiv.Perm (Fin n)) : (r : ℕ) → r ≤ n → List (Fin n)
  | 0, _ => []
  | s + 1, hr => prefixList π s (Nat.le_of_succ_le hr) ++ [π ⟨s, hr⟩]

def twoItemVal (w₀ w₁ : ℝ) : ItemValuation 2 :=
  fun S =>
    if (0 : Fin 2) ∈ S then
      if (1 : Fin 2) ∈ S then ((0 : ℝ) : WithBot ℝ) else ((w₀ : ℝ) : WithBot ℝ)
    else
      if (1 : Fin 2) ∈ S then ((w₁ : ℝ) : WithBot ℝ) else ((0 : ℝ) : WithBot ℝ)

end ContractsAndTwoItemsInternal

section
open ContractsAndTwoItemsInternal

theorem thm_lower_contracts_and_two_items :
    -- (1) Proposition C.4: No per-pair guarantee
    (∀ (m : ℕ), 1 ≤ m → ∀ (alg : OnlineWelfareAlg m m),
      ∃ (v : Fin m → ItemValuation m) (Xstar : Fin m → Finset (Fin m)),
        (∀ i : Fin m,
          IsUnitDemandValuation (v i) ∧
          IsGSValuation (v i) ∧
          IsNonnegValuation (v i) ∧
          IsMonotoneValuation (v i)) ∧
        IsAllocOf Finset.univ Xstar ∧
        allocWelfare v Xstar = ((optWelfare v : ℝ) : WithBot ℝ) ∧
        (∀ Y : Fin m → Finset (Fin m),
          IsAllocOf Finset.univ Y →
          allocWelfare v Y = ((optWelfare v : ℝ) : WithBot ℝ) → Y = Xstar) ∧
        ∃ (i : Fin m) (g : Fin m), g ∈ Xstar i ∧
          (∑ A ∈ (Finset.univ : Finset (Fin m → Finset (Fin m))).filter (fun A => g ∈ A i),
            algWelfareProb alg v A) ≤ harmonicNum m / (m : ℝ)) ∧
    -- (2) Proposition C.2: Two-item 1/2 + δ upper bound for nonnegative GS valuations
    (∀ δ : ℝ, 0 < δ →
      ∃ fam : List (ItemValuation 2),
        fam ≠ [] ∧
        (∀ v ∈ fam, IsGSValuation v ∧ IsNonnegValuation v ∧ 0 < optVal v) ∧
        ∀ alg : OnlineSelectionAlg 2,
          ∃ v ∈ fam,
            expectedSelectionVal alg v ≤ (((1 / 2 + δ) * optVal v : ℝ) : WithBot ℝ)) :=
by
  refine ⟨?_, ?_⟩
  · 
    
    
    have hu_emp : ∀ {n : ℕ} (w : Fin n → ℝ), unitDemandReal w ∅ = 0 := by
      intro n w
      simp [unitDemandReal, Finset.sup_empty, WithBot.unbotD_bot]
    have hu_ins : ∀ {n : ℕ} (w : Fin n → ℝ), (∀ g, 0 ≤ w g) →
        ∀ (x : Fin n) (S : Finset (Fin n)),
          unitDemandReal w (insert x S) = max (w x) (unitDemandReal w S) := by
      intro n w hw x S
      rcases S.eq_empty_or_nonempty with rfl | ⟨g₀, hg₀⟩
      · rw [hu_emp, max_eq_left (hw x)]
        simp [unitDemandReal, Finset.sup_singleton, WithBot.unbotD_coe]
      · have hle : ((w g₀ : ℝ) : WithBot ℝ) ≤ S.sup (fun g => ((w g : ℝ) : WithBot ℝ)) :=
          Finset.le_sup (f := fun g => ((w g : ℝ) : WithBot ℝ)) hg₀
        cases hsup : S.sup (fun g => ((w g : ℝ) : WithBot ℝ)) with
        | bot =>
            rw [hsup] at hle
            exact absurd hle (by simp)
        | coe r =>
            unfold unitDemandReal
            rw [Finset.sup_insert, hsup, ← WithBot.coe_sup, WithBot.unbotD_coe, WithBot.unbotD_coe]
    have hu_nonneg : ∀ {n : ℕ} (w : Fin n → ℝ), (∀ g, 0 ≤ w g) →
        ∀ S : Finset (Fin n), 0 ≤ unitDemandReal w S := by
      intro n w hw S
      induction S using Finset.induction_on with
      | empty => rw [hu_emp]
      | @insert x S _ _ =>
          rw [hu_ins w hw x S]
          exact le_trans (hw x) (le_max_left _ _)
    have hu_mem_le : ∀ {n : ℕ} (w : Fin n → ℝ), (∀ g, 0 ≤ w g) →
        ∀ (S : Finset (Fin n)) (g : Fin n), g ∈ S → w g ≤ unitDemandReal w S := by
      intro n w hw S g hg
      have h := hu_ins w hw g S
      rw [Finset.insert_eq_of_mem hg] at h
      rw [h]
      exact le_max_left _ _
    have hu_bound : ∀ {n : ℕ} (w : Fin n → ℝ), (∀ g, 0 ≤ w g) →
        ∀ (S : Finset (Fin n)) (c : ℝ), 0 ≤ c → (∀ g ∈ S, w g ≤ c) → unitDemandReal w S ≤ c := by
      intro n w hw S c hc h
      induction S using Finset.induction_on with
      | empty => rw [hu_emp]; exact hc
      | @insert x S _ ih =>
          rw [hu_ins w hw x S]
          exact max_le (h x (Finset.mem_insert_self x S))
            (ih (fun g hg => h g (Finset.mem_insert_of_mem hg)))
    have hu_mono : ∀ {n : ℕ} (w : Fin n → ℝ), (∀ g, 0 ≤ w g) →
        ∀ S T : Finset (Fin n), S ⊆ T → unitDemandReal w S ≤ unitDemandReal w T := by
      intro n w hw S T hST
      exact hu_bound w hw S (unitDemandReal w T) (hu_nonneg w hw T)
        (fun g hg => hu_mem_le w hw T g (hST hg))
    have hu_attain : ∀ {n : ℕ} (w : Fin n → ℝ), (∀ g, 0 ≤ w g) →
        ∀ S : Finset (Fin n), S.Nonempty → ∃ g ∈ S, unitDemandReal w S = w g := by
      intro n w hw S
      induction S using Finset.induction_on with
      | empty =>
          intro hne
          exact absurd hne Finset.not_nonempty_empty
      | @insert x S _ ih =>
          intro _
          rcases S.eq_empty_or_nonempty with rfl | hne
          · refine ⟨x, Finset.mem_insert_self x ∅, ?_⟩
            rw [hu_ins w hw x ∅, hu_emp, max_eq_left (hw x)]
          · obtain ⟨g, hg, hval⟩ := ih hne
            rw [hu_ins w hw x S, hval]
            rcases le_total (w x) (w g) with hle | hle
            · exact ⟨g, Finset.mem_insert_of_mem hg, max_eq_right hle⟩
            · exact ⟨x, Finset.mem_insert_self x S, max_eq_left hle⟩
    have h_s1 : ∀ (n : ℕ) (w : Fin n → ℝ), (∀ g, 0 ≤ w g) →
        IsUnitDemandValuation (unitDemandOfWeights w) ∧
        IsGSValuation (unitDemandOfWeights w) ∧
        IsNonnegValuation (unitDemandOfWeights w) ∧
        IsMonotoneValuation (unitDemandOfWeights w) := by
      intro n w hw
      refine ⟨⟨w, hw, fun _ => rfl⟩, ?_, ?_, ?_⟩
      · refine ⟨by simp [unitDemandOfWeights, hu_emp], ?_⟩
        intro X Y _ _ x hx
        have hxX : x ∈ X := (Finset.mem_sdiff.mp hx).1
        have hxY : x ∉ Y := (Finset.mem_sdiff.mp hx).2
        have hX_eq : unitDemandReal w X = max (w x) (unitDemandReal w (X.erase x)) := by
          conv_lhs => rw [← Finset.insert_erase hxX]
          exact hu_ins w hw x (X.erase x)
        rcases le_or_gt (w x) (unitDemandReal w (X.erase x)) with hcase1 | hcase2
        · have huX : unitDemandReal w X = unitDemandReal w (X.erase x) := by
            rw [hX_eq, max_eq_right hcase1]
          have huY : unitDemandReal w Y ≤ unitDemandReal w (insert x Y) :=
            hu_mono w hw Y (insert x Y) (Finset.subset_insert x Y)
          refine le_trans ?_ (le_max_left _ _)
          dsimp only [unitDemandOfWeights]
          rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
          linarith
        · have huX : unitDemandReal w X = w x := by
            rw [hX_eq, max_eq_left (le_of_lt hcase2)]
          rcases le_or_gt (unitDemandReal w Y) (unitDemandReal w (X.erase x)) with hcase2a | hcase2b
          · have hwx_le : w x ≤ unitDemandReal w (insert x Y) :=
              hu_mem_le w hw (insert x Y) x (Finset.mem_insert_self x Y)
            refine le_trans ?_ (le_max_left _ _)
            dsimp only [unitDemandOfWeights]
            rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
            linarith
          · have hY_ne : Y.Nonempty := by
              rcases Y.eq_empty_or_nonempty with rfl | hne
              · exfalso
                have h0 := hu_nonneg w hw (X.erase x)
                rw [hu_emp] at hcase2b
                linarith
              · exact hne
            obtain ⟨y, hyY, huY_eq⟩ := hu_attain w hw Y hY_ne
            have hy_ne_x : y ≠ x := fun h => hxY (h ▸ hyY)
            have hy_not_X : y ∉ X := by
              intro hyX
              have hy_er : y ∈ X.erase x := Finset.mem_erase.mpr ⟨hy_ne_x, hyX⟩
              have hwy := hu_mem_le w hw (X.erase x) y hy_er
              linarith
            have hy_sdiff : y ∈ Y \ X := Finset.mem_sdiff.mpr ⟨hyY, hy_not_X⟩
            have h_sw1 : w y ≤ unitDemandReal w (insert y (X.erase x)) :=
              hu_mem_le w hw (insert y (X.erase x)) y (Finset.mem_insert_self y (X.erase x))
            have hx_mem_er : x ∈ (insert x Y).erase y :=
              Finset.mem_erase.mpr ⟨hy_ne_x.symm, Finset.mem_insert_self x Y⟩
            have h_sw2 : w x ≤ unitDemandReal w ((insert x Y).erase y) :=
              hu_mem_le w hw ((insert x Y).erase y) x hx_mem_er
            refine le_trans ?_ (le_max_right _ _)
            refine le_trans ?_ (Finset.le_sup (f := fun z =>
              unitDemandOfWeights w (insert z (X.erase x)) +
              unitDemandOfWeights w ((insert x Y).erase z)) hy_sdiff)
            dsimp only [unitDemandOfWeights]
            rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
            linarith
      · intro S
        dsimp only [unitDemandOfWeights]
        rw [WithBot.coe_le_coe]
        exact hu_nonneg w hw S
      · intro S T hST
        dsimp only [unitDemandOfWeights]
        rw [WithBot.coe_le_coe]
        exact hu_mono w hw S T hST
    have h_s2 : ∀ (m : ℕ) (x₀ : Fin m) (τ : Equiv.Perm (Fin m)),
        IsAllocOf Finset.univ (contractsOptAlloc τ) ∧
        allocWelfare (contractsVal x₀ τ) (contractsOptAlloc τ) =
          ((optWelfare (contractsVal x₀ τ) : ℝ) : WithBot ℝ) ∧
        ∀ Y : Fin m → Finset (Fin m),
          IsAllocOf Finset.univ Y →
          allocWelfare (contractsVal x₀ τ) Y =
            ((optWelfare (contractsVal x₀ τ) : ℝ) : WithBot ℝ) →
          Y = contractsOptAlloc τ := by
      intro m x₀ τ
      let v := contractsVal x₀ τ
      let Xstar := contractsOptAlloc τ
      have hw_nonneg : ∀ i g : Fin m, 0 ≤ contractsWeight x₀ τ i g := by
        intro i g
        unfold contractsWeight
        split_ifs <;> norm_num
      have hXstar_alloc : IsAllocOf Finset.univ Xstar := by
        refine ⟨fun _ => Finset.subset_univ _, ?_⟩
        intro i j hij
        dsimp only [Xstar, contractsOptAlloc]
        rw [Finset.disjoint_singleton]
        intro heq
        exact hij (τ.symm.injective heq)
      let c (i : Fin m) : ℝ := if i = τ x₀ then 1 else 2
      have hc_nonneg : ∀ i : Fin m, 0 ≤ c i := by
        intro i; dsimp only [c]; split_ifs <;> norm_num
      have hu_le_c : ∀ (i : Fin m) (S : Finset (Fin m)),
          unitDemandReal (contractsWeight x₀ τ i) S ≤ c i := by
        intro i S
        refine hu_bound (contractsWeight x₀ τ i) (hw_nonneg i) S (c i) (hc_nonneg i) ?_
        intro g _
        dsimp only [c, contractsWeight]
        by_cases hi : i = τ x₀
        · rw [if_pos hi]
          by_cases hg : g = x₀
          · rw [if_pos hg]
          · rw [if_neg hg]
            have hne : i ≠ τ g := fun heq => hg (τ.injective (heq.symm.trans hi))
            rw [if_neg hne]
            norm_num
        · rw [if_neg hi]
          split_ifs <;> norm_num
      have hu_Xstar_eq_c : ∀ i : Fin m,
          unitDemandReal (contractsWeight x₀ τ i) (Xstar i) = c i := by
        intro i
        dsimp only [Xstar, contractsOptAlloc]
        have hsing : ({τ.symm i} : Finset (Fin m)) = insert (τ.symm i) ∅ := rfl
        rw [hsing, hu_ins _ (hw_nonneg i), hu_emp, max_eq_left (hw_nonneg i (τ.symm i))]
        dsimp only [c, contractsWeight]
        by_cases hi : i = τ x₀
        · subst hi; simp
        · rw [if_neg hi]
          have hne : τ.symm i ≠ x₀ := by
            intro heq; apply hi; rw [← heq, Equiv.apply_symm_apply]
          rw [if_neg hne, Equiv.apply_symm_apply, if_pos rfl]
      have hu_eq_c_imp_mem : ∀ (i : Fin m) (S : Finset (Fin m)),
          unitDemandReal (contractsWeight x₀ τ i) S = c i → τ.symm i ∈ S := by
        intro i S heq
        by_contra hnot
        by_cases hi : i = τ x₀
        · have hx0_not : x₀ ∉ S := by subst hi; simpa using hnot
          have hle0 : unitDemandReal (contractsWeight x₀ τ i) S ≤ 0 := by
            refine hu_bound _ (hw_nonneg i) S 0 (le_refl 0) ?_
            intro g hg
            have hg_ne : g ≠ x₀ := fun h => hx0_not (h ▸ hg)
            have hne : i ≠ τ g := fun h => hg_ne (τ.injective (h.symm.trans hi))
            simp [contractsWeight, hg_ne, hne]
          have hci : c i = 1 := if_pos hi
          linarith
        · have hle1 : unitDemandReal (contractsWeight x₀ τ i) S ≤ 1 := by
            refine hu_bound _ (hw_nonneg i) S 1 (by norm_num) ?_
            intro g hg
            have hne : i ≠ τ g := by
              intro h; apply hnot; rw [h, Equiv.symm_apply_apply]; exact hg
            unfold contractsWeight
            by_cases hg0 : g = x₀
            · rw [if_pos hg0]
            · rw [if_neg hg0, if_neg hne]; norm_num
          have hci : c i = 2 := if_neg hi
          linarith
      have halloc_eq : ∀ Y : Fin m → Finset (Fin m),
          allocWelfare v Y =
            ((∑ i : Fin m, unitDemandReal (contractsWeight x₀ τ i) (Y i) : ℝ) : WithBot ℝ) := by
        intro Y
        unfold allocWelfare
        dsimp only [v, contractsVal, unitDemandOfWeights]
        exact (WithBot.coe_sum Finset.univ
          (fun i => unitDemandReal (contractsWeight x₀ τ i) (Y i))).symm
      let C : ℝ := ∑ i : Fin m, c i
      have halloc_Xstar : allocWelfare v Xstar = ((C : ℝ) : WithBot ℝ) := by
        rw [halloc_eq Xstar]
        congr 1
        exact Finset.sum_congr rfl (fun i _ => hu_Xstar_eq_c i)
      have hsup_opt :
          ((Finset.univ : Finset (Fin m → Finset (Fin m))).filter (fun X => IsAllocOf Finset.univ X)).sup
            (allocWelfare v) = ((C : ℝ) : WithBot ℝ) := by
        apply le_antisymm
        · apply Finset.sup_le
          intro Y _
          rw [halloc_eq Y, WithBot.coe_le_coe]
          exact Finset.sum_le_sum (fun i _ => hu_le_c i (Y i))
        · rw [← halloc_Xstar]
          exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ Xstar, hXstar_alloc⟩)
      have hopt_eq : optWelfare v = C := by
        unfold optWelfare optWelfareOn
        rw [hsup_opt, WithBot.unbotD_coe]
      refine ⟨hXstar_alloc, ?_, ?_⟩
      · rw [halloc_Xstar, hopt_eq]
      · intro Y hY_alloc hY_opt
        rw [halloc_eq Y, hopt_eq, WithBot.coe_inj] at hY_opt
        have h_all_eq : ∀ i ∈ (Finset.univ : Finset (Fin m)),
            unitDemandReal (contractsWeight x₀ τ i) (Y i) = c i :=
          (Finset.sum_eq_sum_iff_of_le (fun i _ => hu_le_c i (Y i))).mp hY_opt
        have h_mem_all : ∀ i : Fin m, τ.symm i ∈ Y i :=
          fun i => hu_eq_c_imp_mem i (Y i) (h_all_eq i (Finset.mem_univ i))
        funext i
        ext g
        dsimp only [Xstar, contractsOptAlloc]
        simp only [Finset.mem_singleton]
        constructor
        · intro hgY
          have hg_in_tau : g ∈ Y (τ g) := by
            have := h_mem_all (τ g)
            rwa [Equiv.symm_apply_apply] at this
          by_contra hne
          have hi_ne : i ≠ τ g := by
            intro heq; apply hne; rw [heq, Equiv.symm_apply_apply]
          exact Finset.disjoint_left.mp (hY_alloc.2 i (τ g) hi_ne) hgY hg_in_tau
        · rintro rfl
          exact h_mem_all i
    
    intro m hm alg
    let x₀ : Fin m := ⟨0, by omega⟩
    have h_prefix_eq : ∀ (d : DetWelfareAlg m m) (v : Fin m → ItemValuation m)
        (π : Equiv.Perm (Fin m)) (r : ℕ) (hr : r ≤ m),
        (runDetWelfareSteps d v π r hr).1 = prefixList π r hr := by
      intro d v π r
      induction r with
      | zero => intro _; rfl
      | succ s ih =>
          intro hr
          let hs := Nat.le_of_succ_le hr
          have ih_s := ih hs
          rcases hp : runDetWelfareSteps d v π s hs with ⟨prev, bundles⟩
          rw [hp] at ih_s; dsimp only at ih_s
          unfold runDetWelfareSteps prefixList
          rw [hp]; dsimp only; rw [ih_s]
    have h_prefix_mem : ∀ (π : Equiv.Perm (Fin m)) (r : ℕ) (hr : r ≤ m) (g : Fin m),
        g ∈ (prefixList π r hr).toFinset ↔ ∃ j : Fin m, j.1 < r ∧ π j = g := by
      intro π r
      induction r with
      | zero => intro _ g; simp [prefixList]
      | succ s ih =>
          intro hr g
          let hs := Nat.le_of_succ_le hr
          unfold prefixList
          rw [List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
              Finset.insert_empty, Finset.mem_union, Finset.mem_singleton, ih hs]
          constructor
          · rintro (⟨j, hj, hπj⟩ | rfl)
            · exact ⟨j, Nat.lt_succ_of_lt hj, hπj⟩
            · exact ⟨⟨s, hr⟩, Nat.lt_succ_self s, rfl⟩
          · rintro ⟨j, hj, hπj⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
            · left; exact ⟨j, hlt, hπj⟩
            · right; have hj_eq : j = ⟨s, hr⟩ := Fin.ext heq; rw [← hj_eq, hπj]
    have h_prefix_indep : ∀ (d : DetWelfareAlg m m) (v₁ v₂ : Fin m → ItemValuation m)
        (π : Equiv.Perm (Fin m)) (k : ℕ) (hk : k < m),
        (∀ (i : Fin m) (T : Finset (Fin m)),
          (∀ g ∈ T, ∃ j : Fin m, j.1 ≤ k ∧ π j = g) → v₁ i T = v₂ i T) →
        ∀ (r : ℕ) (hr : r ≤ m), r ≤ k + 1 →
          runDetWelfareSteps d v₁ π r hr = runDetWelfareSteps d v₂ π r hr := by
      intro d v₁ v₂ π k _ hv r
      induction r with
      | zero => intro _ _; rfl
      | succ s ih =>
          intro hr hrs
          have hs_le_k : s ≤ k := Nat.le_of_succ_le_succ hrs
          let hs := Nat.le_of_succ_le hr
          have heq_s := ih hs (Nat.le_trans hs_le_k (Nat.le_succ k))
          rcases hp2 : runDetWelfareSteps d v₂ π s hs with ⟨prev, bundles⟩
          have hp1 : runDetWelfareSteps d v₁ π s hs = (prev, bundles) := heq_s.trans hp2
          have hprev : prev = prefixList π s hs := by
            have := h_prefix_eq d v₂ π s hs; rw [hp2] at this; exact this
          unfold runDetWelfareSteps
          rw [hp1, hp2]; dsimp only
          have horc :
              (fun (i : Fin m) (sub : {T : Finset (Fin m) // T ⊆ insert (π ⟨s, hr⟩) prev.toFinset}) =>
                v₁ i sub.1) =
              (fun (i : Fin m) (sub : {T : Finset (Fin m) // T ⊆ insert (π ⟨s, hr⟩) prev.toFinset}) =>
                v₂ i sub.1) := by
            funext i ⟨T, hT⟩
            apply hv i T
            intro g hg
            have hg_ins := hT hg
            rw [hprev, Finset.mem_insert, h_prefix_mem] at hg_ins
            rcases hg_ins with rfl | ⟨j, hj, hπj⟩
            · exact ⟨⟨s, hr⟩, hs_le_k, rfl⟩
            · exact ⟨j, le_trans (le_of_lt hj) hs_le_k, hπj⟩
          rw [horc]
    have h_x0_before : ∀ (d : DetWelfareAlg m m) (v : Fin m → ItemValuation m)
        (π : Equiv.Perm (Fin m)) (r : ℕ) (hr : r ≤ m), r ≤ (π.symm x₀).1 →
        ∀ i : Fin m, x₀ ∉ (runDetWelfareSteps d v π r hr).2 i := by
      intro d v π r
      induction r with
      | zero => intro _ _ i; simp [runDetWelfareSteps]
      | succ s ih =>
          intro hr hrs i
          let hs := Nat.le_of_succ_le hr
          have ih_s := ih hs (le_of_lt hrs)
          have hπk : π ⟨(π.symm x₀).1, (π.symm x₀).2⟩ = x₀ := by
            have hfin : (⟨(π.symm x₀).1, (π.symm x₀).2⟩ : Fin m) = π.symm x₀ := Fin.ext rfl
            rw [hfin, Equiv.apply_symm_apply]
          have hx_ne : π ⟨s, hr⟩ ≠ x₀ := by
            intro heq; rw [← hπk] at heq; have := Fin.mk.inj (π.injective heq); omega
          rcases hp : runDetWelfareSteps d v π s hs with ⟨prev, bundles⟩
          have hb_not : ∀ i' : Fin m, x₀ ∉ bundles i' := by
            intro i'; have := ih_s i'; rwa [hp] at this
          unfold runDetWelfareSteps; rw [hp]; dsimp only
          cases d.step prev (π ⟨s, hr⟩) bundles (fun i' ⟨T, _⟩ => v i' T) with
          | none => exact hb_not i
          | some i₀ =>
              dsimp only
              by_cases hi : i = i₀
              · subst hi
                rw [Function.update_self, Finset.mem_insert]
                rintro (h1 | h2)
                · exact hx_ne h1.symm
                · exact hb_not i h2
              · rw [Function.update_of_ne hi]; exact hb_not i
    have h_x0_unique : ∀ (d : DetWelfareAlg m m) (v : Fin m → ItemValuation m)
        (π : Equiv.Perm (Fin m)) (i₁ i₂ : Fin m),
        x₀ ∈ (runDetWelfareSteps d v π ((π.symm x₀).1 + 1) (π.symm x₀).2).2 i₁ →
        x₀ ∈ (runDetWelfareSteps d v π ((π.symm x₀).1 + 1) (π.symm x₀).2).2 i₂ →
        i₁ = i₂ := by
      intro d v π i₁ i₂ h1 h2
      let k := (π.symm x₀).1
      let hk := (π.symm x₀).2
      let hk_le := le_of_lt hk
      have hb_k := h_x0_before d v π k hk_le (le_refl k)
      rcases hp : runDetWelfareSteps d v π k hk_le with ⟨prev, bundles⟩
      have hb_not : ∀ i' : Fin m, x₀ ∉ bundles i' := by
        intro i'; have := hb_k i'; rwa [hp] at this
      change x₀ ∈ (runDetWelfareSteps d v π (k + 1) hk).2 i₁ at h1
      change x₀ ∈ (runDetWelfareSteps d v π (k + 1) hk).2 i₂ at h2
      unfold runDetWelfareSteps at h1 h2; rw [hp] at h1 h2; dsimp only at h1 h2
      cases hdec : d.step prev (π ⟨k, hk⟩) bundles (fun i' ⟨T, _⟩ => v i' T) <;>
        rw [hdec] at h1 h2 <;> dsimp only at h1 h2
      · exact absurd h1 (hb_not i₁)
      · rename_i i₀
        have hi1 : i₁ = i₀ := by
          by_contra hne; rw [Function.update_of_ne hne] at h1; exact hb_not i₁ h1
        have hi2 : i₂ = i₀ := by
          by_contra hne; rw [Function.update_of_ne hne] at h2; exact hb_not i₂ h2
        exact hi1.trans hi2.symm
    have h_x0_after : ∀ (d : DetWelfareAlg m m) (v : Fin m → ItemValuation m)
        (π : Equiv.Perm (Fin m)) (r : ℕ) (hr : r ≤ m), (π.symm x₀).1 + 1 ≤ r →
        ∀ i : Fin m,
          x₀ ∈ (runDetWelfareSteps d v π r hr).2 i ↔
          x₀ ∈ (runDetWelfareSteps d v π ((π.symm x₀).1 + 1) (π.symm x₀).2).2 i := by
      intro d v π r
      induction r with
      | zero => intro _ hkr; omega
      | succ s ih =>
          intro hr hkr i
          rcases Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ hkr) with h_eq | h_lt
          · subst h_eq; rfl
          · let hs := Nat.le_of_succ_le hr
            have ih_s := ih hs h_lt i
            have hπk : π ⟨(π.symm x₀).1, (π.symm x₀).2⟩ = x₀ := by
              have hfin : (⟨(π.symm x₀).1, (π.symm x₀).2⟩ : Fin m) = π.symm x₀ := Fin.ext rfl
              rw [hfin, Equiv.apply_symm_apply]
            have hx_ne : π ⟨s, hr⟩ ≠ x₀ := by
              intro heq; rw [← hπk] at heq; have := Fin.mk.inj (π.injective heq); omega
            rcases hp : runDetWelfareSteps d v π s hs with ⟨prev, bundles⟩
            rw [hp] at ih_s; dsimp only at ih_s
            rw [← ih_s]; unfold runDetWelfareSteps; rw [hp]; dsimp only
            cases d.step prev (π ⟨s, hr⟩) bundles (fun i' ⟨T, _⟩ => v i' T) with
            | none => rfl
            | some i₀ =>
                dsimp only
                by_cases hi : i = i₀
                · subst hi
                  rw [Function.update_self, Finset.mem_insert]
                  exact ⟨fun h => h.resolve_left hx_ne.symm, Or.inr⟩
                · rw [Function.update_of_ne hi]
    have h_final_iff : ∀ (d : DetWelfareAlg m m) (v : Fin m → ItemValuation m)
        (π : Equiv.Perm (Fin m)) (i : Fin m),
        x₀ ∈ runDetWelfare d v π i ↔
        x₀ ∈ (runDetWelfareSteps d v π ((π.symm x₀).1 + 1) (π.symm x₀).2).2 i :=
      fun d v π i => h_x0_after d v π m (le_refl m) (π.symm x₀).2 i
    have h_meas_steps : ∀ (v : Fin m → ItemValuation m) (π : Equiv.Perm (Fin m))
        (r : ℕ) (hr : r ≤ m) (B : Fin m → Finset (Fin m)),
        MeasurableSet {ω : alg.Seed | (runDetWelfareSteps (alg.det ω) v π r hr).2 = B} := by
      intro v π r
      induction r with
      | zero =>
          intro hr B
          change MeasurableSet {ω : alg.Seed | (fun _ : Fin m => (∅ : Finset (Fin m))) = B}
          exact MeasurableSet.const _
      | succ s ih =>
          intro hr B
          let hs := Nat.le_of_succ_le hr
          let L := prefixList π s hs
          let x := π ⟨s, hr⟩
          let upd (B₀ : Fin m → Finset (Fin m)) (dec : Option (Fin m)) : Fin m → Finset (Fin m) :=
            match dec with
            | none => B₀
            | some i => Function.update B₀ i (insert x (B₀ i))
          have hset_eq :
              {ω : alg.Seed | (runDetWelfareSteps (alg.det ω) v π (s + 1) hr).2 = B} =
                ⋃ (B₀ : Fin m → Finset (Fin m)), ⋃ (dec : Option (Fin m)),
                  ({ω | (runDetWelfareSteps (alg.det ω) v π s hs).2 = B₀} ∩
                   ({ω | (alg.det ω).step L x B₀ (fun i ⟨T, _⟩ => v i T) = dec} ∩
                    {ω | upd B₀ dec = B})) := by
            ext ω
            simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
            constructor
            · intro hB
              let B₀ := (runDetWelfareSteps (alg.det ω) v π s hs).2
              have hp : runDetWelfareSteps (alg.det ω) v π s hs = (L, B₀) :=
                Prod.ext (h_prefix_eq (alg.det ω) v π s hs) rfl
              let dec := (alg.det ω).step L x B₀ (fun i ⟨T, _⟩ => v i T)
              refine ⟨B₀, dec, rfl, rfl, ?_⟩
              unfold runDetWelfareSteps at hB; rw [hp] at hB; exact hB
            · rintro ⟨B₀, dec, hB₀, hdec, hupd⟩
              have hp : runDetWelfareSteps (alg.det ω) v π s hs = (L, B₀) :=
                Prod.ext (h_prefix_eq (alg.det ω) v π s hs) hB₀
              unfold runDetWelfareSteps; rw [hp]; dsimp only; rw [hdec]; exact hupd
          rw [hset_eq]
          exact MeasurableSet.iUnion (fun B₀ => MeasurableSet.iUnion (fun dec =>
            (ih hs B₀).inter ((alg.meas_step L x B₀ _ dec).inter (MeasurableSet.const _))))
    have h_meas_mem : ∀ (v : Fin m → ItemValuation m) (π : Equiv.Perm (Fin m))
        (r : ℕ) (hr : r ≤ m) (i : Fin m),
        MeasurableSet {ω : alg.Seed | x₀ ∈ (runDetWelfareSteps (alg.det ω) v π r hr).2 i} := by
      intro v π r hr i
      have hset :
          {ω : alg.Seed | x₀ ∈ (runDetWelfareSteps (alg.det ω) v π r hr).2 i} =
            ⋃ (B : Fin m → Finset (Fin m)),
              ({ω | (runDetWelfareSteps (alg.det ω) v π r hr).2 = B} ∩ {ω | x₀ ∈ B i}) := by
        ext ω
        simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
        exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨_, h1, h2⟩ => h1 ▸ h2⟩
      rw [hset]
      exact MeasurableSet.iUnion (fun B => (h_meas_steps v π r hr B).inter (MeasurableSet.const _))
    let E_ev (π : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin m)) (y : Fin m) : Set alg.Seed :=
      {ω | x₀ ∈ (runDetWelfareSteps (alg.det ω) (contractsVal x₀ τ) π
        ((π.symm x₀).1 + 1) (π.symm x₀).2).2 (τ y)}
    let P_prob (τ : Equiv.Perm (Fin m)) : ℝ :=
      ∑ A ∈ (Finset.univ : Finset (Fin m → Finset (Fin m))).filter (fun A => x₀ ∈ A (τ x₀)),
        algWelfareProb alg (contractsVal x₀ τ) A
    have hP_eq : ∀ τ : Equiv.Perm (Fin m),
        P_prob τ = (1 / (Nat.factorial m : ℝ)) *
          ∑ π : Equiv.Perm (Fin m), alg.seedMeasure.real (E_ev π τ x₀) := by
      intro τ
      dsimp only [P_prob, algWelfareProb]
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl (fun π _ => ?_)
      let S_filt := (Finset.univ : Finset (Fin m → Finset (Fin m))).filter (fun A => x₀ ∈ A (τ x₀))
      have hdisj : (S_filt : Set (Fin m → Finset (Fin m))).PairwiseDisjoint
          (fun A => {ω : alg.Seed | runDetWelfare (alg.det ω) (contractsVal x₀ τ) π = A}) := by
        intro A₁ _ A₂ _ hne
        rw [Function.onFun, Set.disjoint_left]
        intro ω h1 h2; exact hne (h1.symm.trans h2)
      have hmeas : ∀ A ∈ S_filt,
          MeasurableSet {ω : alg.Seed | runDetWelfare (alg.det ω) (contractsVal x₀ τ) π = A} :=
        fun A _ => h_meas_steps (contractsVal x₀ τ) π m (le_refl m) A
      rw [← MeasureTheory.measureReal_biUnion_finset hdisj hmeas]
      congr 1
      ext ω
      simp only [S_filt, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq, E_ev]
      constructor
      · rintro ⟨A, hAx, hrun⟩
        rw [← hrun] at hAx
        exact (h_final_iff (alg.det ω) (contractsVal x₀ τ) π (τ x₀)).mp hAx
      · intro hmem
        exact ⟨runDetWelfare (alg.det ω) (contractsVal x₀ τ) π,
          (h_final_iff (alg.det ω) (contractsVal x₀ τ) π (τ x₀)).mpr hmem, rfl⟩
    have h_coset_bound : ∀ π : Equiv.Perm (Fin m),
        (∑ τ : Equiv.Perm (Fin m), alg.seedMeasure.real (E_ev π τ x₀)) ≤
          (Nat.factorial m : ℝ) / ((m - (π.symm x₀).1 : ℕ) : ℝ) := by
      intro π
      let k := (π.symm x₀).1
      have hk : k < m := (π.symm x₀).2
      let S_prev : Finset (Fin m) := (Finset.univ.filter (fun j : Fin m => j.1 < k)).image π
      have hS_card : S_prev.card = k := by
        dsimp only [S_prev]
        rw [Finset.card_image_of_injective _ π.injective]
        have hbij : (Finset.univ.filter (fun j : Fin m => j.1 < k)).card = (Finset.range k).card := by
          refine Finset.card_bij (fun (j : Fin m) _ => j.1) ?_ ?_ ?_
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            exact Finset.mem_range.mpr hj
          · intro j₁ _ j₂ _ heq; exact Fin.ext heq
          · intro r hr
            have hrk : r < k := Finset.mem_range.mp hr
            refine ⟨⟨r, lt_trans hrk hk⟩, ?_, rfl⟩
            simp [hrk]
        rw [hbij, Finset.card_range]
      have hx0_not_S : x₀ ∉ S_prev := by
        intro hmem
        dsimp only [S_prev] at hmem
        rw [Finset.mem_image] at hmem
        rcases hmem with ⟨j, hj_filt, hπj⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj_filt
        have hj_eq : j = π.symm x₀ := by
          apply π.injective; rw [hπj, Equiv.apply_symm_apply]
        rw [hj_eq] at hj_filt
        exact Nat.lt_irrefl k hj_filt
      let U_π : Finset (Fin m) := Finset.univ \ S_prev
      have hU_card : U_π.card = m - k := by
        have hunion : U_π ∪ S_prev = (Finset.univ : Finset (Fin m)) := by
          ext g; by_cases hg : g ∈ S_prev <;> simp [U_π, hg]
        have hdisj : Disjoint U_π S_prev :=
          Finset.disjoint_left.mpr (fun _ h1 h2 => (Finset.mem_sdiff.mp h1).2 h2)
        have hcard_u := Finset.card_union_of_disjoint hdisj
        rw [hunion, Finset.card_univ, Fintype.card_fin, hS_card] at hcard_u
        omega
      let H_π : Finset (Equiv.Perm (Fin m)) :=
        Finset.univ.filter (fun σ => ∀ g ∈ S_prev, σ g = g)
      have h1_in_H : (1 : Equiv.Perm (Fin m)) ∈ H_π := by simp [H_π]
      have hH_pos : (0 : ℝ) < (H_π.card : ℝ) :=
        Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨1, h1_in_H⟩)
      have hσ_in_U : ∀ σ ∈ H_π, σ x₀ ∈ U_π := by
        intro σ hσ
        simp only [H_π, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
        intro hmem
        have hfix : σ (σ x₀) = σ x₀ := hσ (σ x₀) hmem
        have hx_eq : σ x₀ = x₀ := σ.injective hfix
        rw [hx_eq] at hmem
        exact hx0_not_S hmem
      let F_fib (y : Fin m) : Finset (Equiv.Perm (Fin m)) :=
        H_π.filter (fun σ => σ x₀ = y)
      have hF_card_eq : ∀ y ∈ U_π, (F_fib y).card = (F_fib x₀).card := by
        intro y hy
        have hy_not_S : y ∉ S_prev := (Finset.mem_sdiff.mp hy).2
        let sw := Equiv.swap x₀ y
        refine Finset.card_bij (fun σ _ => sw * σ) ?_ ?_ ?_
        · intro σ hσ
          simp only [F_fib, H_π, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
          refine ⟨?_, ?_⟩
          · intro g hg
            have hgx : g ≠ x₀ := fun h => hx0_not_S (h ▸ hg)
            have hgy : g ≠ y := fun h => hy_not_S (h ▸ hg)
            rw [Equiv.Perm.mul_apply, hσ.1 g hg, Equiv.swap_apply_of_ne_of_ne hgx hgy]
          · rw [Equiv.Perm.mul_apply, hσ.2, Equiv.swap_apply_right]
        · intro σ₁ _ σ₂ _ heq
          exact (Equiv.mulLeft sw).injective heq
        · intro σ' hσ'
          simp only [F_fib, H_π, Finset.mem_filter, Finset.mem_univ, true_and] at hσ'
          refine ⟨sw * σ', ?_, ?_⟩
          · simp only [F_fib, H_π, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨?_, ?_⟩
            · intro g hg
              have hgx : g ≠ x₀ := fun h => hx0_not_S (h ▸ hg)
              have hgy : g ≠ y := fun h => hy_not_S (h ▸ hg)
              rw [Equiv.Perm.mul_apply, hσ'.1 g hg, Equiv.swap_apply_of_ne_of_ne hgx hgy]
            · rw [Equiv.Perm.mul_apply, hσ'.2, Equiv.swap_apply_left]
          · ext z; simp [sw]
      have hH_biUnion : H_π = U_π.biUnion F_fib := by
        ext σ
        simp only [Finset.mem_biUnion, F_fib, Finset.mem_filter]
        exact ⟨fun hσ => ⟨σ x₀, hσ_in_U σ hσ, hσ, rfl⟩, fun ⟨_, _, hσ, _⟩ => hσ⟩
      have hF_disj : (U_π : Set (Fin m)).PairwiseDisjoint F_fib := by
        intro y₁ _ y₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro σ h1 h2
        simp only [F_fib, Finset.mem_filter] at h1 h2
        exact hne (h1.2.symm.trans h2.2)
      have hH_card_rel : (H_π.card : ℝ) = ((m - k : ℕ) : ℝ) * ((F_fib x₀).card : ℝ) := by
        have hc : H_π.card = (m - k) * (F_fib x₀).card := by
          rw [hH_biUnion, Finset.card_biUnion hF_disj]
          calc
            ∑ y ∈ U_π, (F_fib y).card = ∑ _y ∈ U_π, (F_fib x₀).card :=
              Finset.sum_congr rfl (fun y hy => hF_card_eq y hy)
            _ = U_π.card * (F_fib x₀).card := by rw [Finset.sum_const, smul_eq_mul]
            _ = (m - k) * (F_fib x₀).card := by rw [hU_card]
        exact_mod_cast hc
      have hE_shift : ∀ (τ : Equiv.Perm (Fin m)) (σ : Equiv.Perm (Fin m)),
          σ ∈ H_π → E_ev π (τ * σ) x₀ = E_ev π τ (σ x₀) := by
        intro τ σ hσ
        simp only [H_π, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
        have hv_eq : ∀ (i : Fin m) (T : Finset (Fin m)),
            (∀ g ∈ T, ∃ j : Fin m, j.1 ≤ k ∧ π j = g) →
            contractsVal x₀ (τ * σ) i T = contractsVal x₀ τ i T := by
          intro i T hT
          dsimp only [contractsVal, unitDemandOfWeights, unitDemandReal]
          congr 2
          refine Finset.sup_congr rfl (fun g hg => ?_)
          congr 1
          dsimp only [contractsWeight]
          by_cases hgx : g = x₀
          · rw [if_pos hgx, if_pos hgx]
          · rw [if_neg hgx, if_neg hgx]
            obtain ⟨j, hjk, hπj⟩ := hT g hg
            have hj_lt : j.1 < k := by
              rcases Nat.eq_or_lt_of_le hjk with heq | hlt
              · exfalso; apply hgx
                have hj_eq : j = π.symm x₀ := Fin.ext heq
                rw [← hπj, hj_eq, Equiv.apply_symm_apply]
              · exact hlt
            have hgS : g ∈ S_prev :=
              Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj_lt⟩, hπj⟩
            rw [Equiv.Perm.mul_apply, hσ g hgS]
        ext ω
        simp only [E_ev, Set.mem_setOf_eq, Equiv.Perm.mul_apply]
        have hstep := h_prefix_indep (alg.det ω) (contractsVal x₀ (τ * σ)) (contractsVal x₀ τ)
          π k hk hv_eq (k + 1) hk (le_refl (k + 1))
        rw [hstep]
      have hE_sum_le_one : ∀ τ : Equiv.Perm (Fin m),
          (∑ y ∈ U_π, alg.seedMeasure.real (E_ev π τ y)) ≤ 1 := by
        intro τ
        have hdisj : (U_π : Set (Fin m)).PairwiseDisjoint (fun y => E_ev π τ y) := by
          intro y₁ _ y₂ _ hne
          rw [Function.onFun, Set.disjoint_left]
          intro ω h1 h2
          exact hne (τ.injective (h_x0_unique (alg.det ω) (contractsVal x₀ τ) π (τ y₁) (τ y₂) h1 h2))
        have hmeas : ∀ y ∈ U_π, MeasurableSet (E_ev π τ y) :=
          fun y _ => h_meas_mem (contractsVal x₀ τ) π (k + 1) hk (τ y)
        rw [← MeasureTheory.measureReal_biUnion_finset hdisj hmeas]
        exact (MeasureTheory.measureReal_mono (Set.subset_univ _)).trans
          (le_of_eq MeasureTheory.probReal_univ)
      have h_coset_tau : ∀ τ : Equiv.Perm (Fin m),
          (∑ σ ∈ H_π, alg.seedMeasure.real (E_ev π (τ * σ) x₀)) ≤ ((F_fib x₀).card : ℝ) := by
        intro τ
        calc
          ∑ σ ∈ H_π, alg.seedMeasure.real (E_ev π (τ * σ) x₀)
              = ∑ σ ∈ H_π, alg.seedMeasure.real (E_ev π τ (σ x₀)) :=
                Finset.sum_congr rfl (fun σ hσ => by rw [hE_shift τ σ hσ])
          _ = ∑ y ∈ U_π, ∑ σ ∈ F_fib y, alg.seedMeasure.real (E_ev π τ (σ x₀)) := by
                conv_lhs => rw [hH_biUnion]
                exact Finset.sum_biUnion hF_disj
          _ = ∑ y ∈ U_π, ((F_fib x₀).card : ℝ) * alg.seedMeasure.real (E_ev π τ y) := by
                refine Finset.sum_congr rfl (fun y hy => ?_)
                have hinner : ∀ σ ∈ F_fib y,
                    alg.seedMeasure.real (E_ev π τ (σ x₀)) = alg.seedMeasure.real (E_ev π τ y) :=
                  fun σ hσ => by rw [(Finset.mem_filter.mp hσ).2]
                rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul, hF_card_eq y hy]
          _ = ((F_fib x₀).card : ℝ) * ∑ y ∈ U_π, alg.seedMeasure.real (E_ev π τ y) := by
                rw [← Finset.mul_sum]
          _ ≤ ((F_fib x₀).card : ℝ) * 1 :=
                mul_le_mul_of_nonneg_left (hE_sum_le_one τ) (Nat.cast_nonneg _)
          _ = ((F_fib x₀).card : ℝ) := mul_one _
      have h_double :
          (H_π.card : ℝ) * (∑ τ : Equiv.Perm (Fin m), alg.seedMeasure.real (E_ev π τ x₀)) ≤
            (Nat.factorial m : ℝ) * ((F_fib x₀).card : ℝ) := by
        have h_lhs :
            (H_π.card : ℝ) * (∑ τ : Equiv.Perm (Fin m), alg.seedMeasure.real (E_ev π τ x₀)) =
              ∑ τ : Equiv.Perm (Fin m), ∑ σ ∈ H_π, alg.seedMeasure.real (E_ev π (τ * σ) x₀) := by
          rw [Finset.sum_comm]
          have h_each : ∀ σ ∈ H_π,
              (∑ τ : Equiv.Perm (Fin m), alg.seedMeasure.real (E_ev π (τ * σ) x₀)) =
                ∑ τ : Equiv.Perm (Fin m), alg.seedMeasure.real (E_ev π τ x₀) :=
            fun σ _ => Fintype.sum_equiv (Equiv.mulRight σ)
              (fun τ => alg.seedMeasure.real (E_ev π (τ * σ) x₀))
              (fun τ => alg.seedMeasure.real (E_ev π τ x₀))
              (fun _ => rfl)
          rw [Finset.sum_congr rfl h_each, Finset.sum_const, nsmul_eq_mul]
        rw [h_lhs]
        calc
          ∑ τ : Equiv.Perm (Fin m), ∑ σ ∈ H_π, alg.seedMeasure.real (E_ev π (τ * σ) x₀)
              ≤ ∑ _τ : Equiv.Perm (Fin m), ((F_fib x₀).card : ℝ) :=
                Finset.sum_le_sum (fun τ _ => h_coset_tau τ)
          _ = (Nat.factorial m : ℝ) * ((F_fib x₀).card : ℝ) := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
      have hmk_pos : (0 : ℝ) < ((m - k : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      rw [le_div_iff₀ hmk_pos]
      have h_mul := mul_le_mul_of_nonneg_left h_double (le_of_lt hmk_pos)
      have h_rhs_eq :
          ((m - k : ℕ) : ℝ) * ((Nat.factorial m : ℝ) * ((F_fib x₀).card : ℝ)) =
            (H_π.card : ℝ) * (Nat.factorial m : ℝ) := by
        rw [hH_card_rel]; ring
      have h_lhs_eq :
          ((m - k : ℕ) : ℝ) * ((H_π.card : ℝ) * ∑ τ : Equiv.Perm (Fin m), alg.seedMeasure.real (E_ev π τ x₀)) =
            (H_π.card : ℝ) * ((∑ τ : Equiv.Perm (Fin m), alg.seedMeasure.real (E_ev π τ x₀)) * ((m - k : ℕ) : ℝ)) := by
        ring
      rw [h_lhs_eq, h_rhs_eq] at h_mul
      exact le_of_mul_le_mul_left h_mul hH_pos
    let Q_fib (j : Fin m) : Finset (Equiv.Perm (Fin m)) :=
      Finset.univ.filter (fun π => π.symm x₀ = j)
    have hQ_card_eq : ∀ j : Fin m, (Q_fib j).card = (Q_fib x₀).card := by
      intro j
      let sw := Equiv.swap x₀ j
      refine Finset.card_bij (fun π _ => π * sw) ?_ ?_ ?_
      · intro π hπ
        simp only [Q_fib, Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
        apply (π * sw).injective
        rw [Equiv.apply_symm_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left, ← hπ,
            Equiv.apply_symm_apply]
      · intro π₁ _ π₂ _ heq
        exact (Equiv.mulRight sw).injective heq
      · intro π' hπ'
        simp only [Q_fib, Finset.mem_filter, Finset.mem_univ, true_and] at hπ'
        refine ⟨π' * sw, ?_, ?_⟩
        · simp only [Q_fib, Finset.mem_filter, Finset.mem_univ, true_and]
          have hπ'_app : π' x₀ = x₀ := by
            have := congrArg π' hπ'
            rw [Equiv.apply_symm_apply] at this
            exact this.symm
          apply (π' * sw).injective
          rw [Equiv.apply_symm_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_right, hπ'_app]
        · ext z; simp [sw]
    have hQ_biUnion : (Finset.univ : Finset (Equiv.Perm (Fin m))) = Finset.univ.biUnion Q_fib := by
      ext π; simp [Q_fib]
    have hQ_disj : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint Q_fib := by
      intro j₁ _ j₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro π h1 h2
      simp only [Q_fib, Finset.mem_filter] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
    have hQ_card_rel : (Nat.factorial m : ℝ) = (m : ℝ) * ((Q_fib x₀).card : ℝ) := by
      have hc : Nat.factorial m = m * (Q_fib x₀).card := by
        have h1 : (Finset.univ : Finset (Equiv.Perm (Fin m))).card = Nat.factorial m := by
          rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
        rw [← h1, hQ_biUnion, Finset.card_biUnion hQ_disj]
        calc
          ∑ j : Fin m, (Q_fib j).card = ∑ _j : Fin m, (Q_fib x₀).card :=
            Finset.sum_congr rfl (fun j _ => hQ_card_eq j)
          _ = m * (Q_fib x₀).card := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      exact_mod_cast hc
    have h_harm_bij : (∑ j : Fin m, (1 / ((m - j.1 : ℕ) : ℝ))) = harmonicNum m := by
      unfold harmonicNum
      refine Finset.sum_bij (fun (j : Fin m) _ => m - j.1) ?_ ?_ ?_ ?_
      · intro j _; dsimp only; have hj := j.2; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro j₁ _ j₂ _ heq; dsimp only at heq; have h1 := j₁.2; have h2 := j₂.2; exact Fin.ext (by omega)
      · intro r hr
        have hr_bounds := Finset.mem_Icc.mp hr
        refine ⟨⟨m - r, by omega⟩, Finset.mem_univ _, ?_⟩
        dsimp only; omega
      · intro _ _; rfl
    have h_sum_P :
        (∑ τ : Equiv.Perm (Fin m), P_prob τ) ≤
          ∑ _τ : Equiv.Perm (Fin m), (harmonicNum m / (m : ℝ)) := by
      have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
      have hm_fact_pos : (0 : ℝ) < (Nat.factorial m : ℝ) :=
        Nat.cast_pos.mpr (Nat.factorial_pos m)
      have h_lhs :
          ∑ τ : Equiv.Perm (Fin m), P_prob τ =
            (1 / (Nat.factorial m : ℝ)) *
              ∑ π : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m), alg.seedMeasure.real (E_ev π τ x₀) := by
        calc
          ∑ τ : Equiv.Perm (Fin m), P_prob τ
              = ∑ τ : Equiv.Perm (Fin m),
                  ((1 / (Nat.factorial m : ℝ)) *
                    ∑ π : Equiv.Perm (Fin m), alg.seedMeasure.real (E_ev π τ x₀)) :=
                Finset.sum_congr rfl (fun τ _ => hP_eq τ)
          _ = (1 / (Nat.factorial m : ℝ)) *
                ∑ τ : Equiv.Perm (Fin m), ∑ π : Equiv.Perm (Fin m), alg.seedMeasure.real (E_ev π τ x₀) := by
                rw [← Finset.mul_sum]
          _ = (1 / (Nat.factorial m : ℝ)) *
                ∑ π : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m), alg.seedMeasure.real (E_ev π τ x₀) := by
                rw [Finset.sum_comm]
      have h_pi_sum :
          (∑ π : Equiv.Perm (Fin m), (Nat.factorial m : ℝ) / ((m - (π.symm x₀).1 : ℕ) : ℝ)) =
            (Nat.factorial m : ℝ) * ((Q_fib x₀).card : ℝ) * harmonicNum m := by
        calc
          ∑ π : Equiv.Perm (Fin m), (Nat.factorial m : ℝ) / ((m - (π.symm x₀).1 : ℕ) : ℝ)
              = ∑ π ∈ Finset.univ.biUnion Q_fib,
                  (Nat.factorial m : ℝ) * (1 / ((m - (π.symm x₀).1 : ℕ) : ℝ)) := by
                rw [← hQ_biUnion]
                refine Finset.sum_congr rfl (fun _ _ => by ring)
          _ = ∑ j : Fin m, ∑ π ∈ Q_fib j,
                (Nat.factorial m : ℝ) * (1 / ((m - (π.symm x₀).1 : ℕ) : ℝ)) :=
                Finset.sum_biUnion hQ_disj
          _ = ∑ j : Fin m, ((Q_fib x₀).card : ℝ) *
                ((Nat.factorial m : ℝ) * (1 / ((m - j.1 : ℕ) : ℝ))) := by
                refine Finset.sum_congr rfl (fun j _ => ?_)
                have hinner : ∀ π ∈ Q_fib j,
                    (Nat.factorial m : ℝ) * (1 / ((m - (π.symm x₀).1 : ℕ) : ℝ)) =
                      (Nat.factorial m : ℝ) * (1 / ((m - j.1 : ℕ) : ℝ)) :=
                  fun π hπ => by rw [(Finset.mem_filter.mp hπ).2]
                rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul, hQ_card_eq j]
          _ = (Nat.factorial m : ℝ) * ((Q_fib x₀).card : ℝ) *
                ∑ j : Fin m, (1 / ((m - j.1 : ℕ) : ℝ)) := by
                calc
                  ∑ j : Fin m, ((Q_fib x₀).card : ℝ) *
                      ((Nat.factorial m : ℝ) * (1 / ((m - j.1 : ℕ) : ℝ)))
                      = ∑ j : Fin m, ((Nat.factorial m : ℝ) * ((Q_fib x₀).card : ℝ)) *
                          (1 / ((m - j.1 : ℕ) : ℝ)) :=
                        Finset.sum_congr rfl (fun _ _ => by ring)
                  _ = ((Nat.factorial m : ℝ) * ((Q_fib x₀).card : ℝ)) *
                        ∑ j : Fin m, (1 / ((m - j.1 : ℕ) : ℝ)) := by
                        rw [← Finset.mul_sum]
          _ = (Nat.factorial m : ℝ) * ((Q_fib x₀).card : ℝ) * harmonicNum m := by
                rw [h_harm_bij]
      have h_rhs :
          ∑ _τ : Equiv.Perm (Fin m), (harmonicNum m / (m : ℝ)) =
            (Nat.factorial m : ℝ) * (harmonicNum m / (m : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
      rw [h_lhs, h_rhs]
      calc
        (1 / (Nat.factorial m : ℝ)) *
            ∑ π : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m), alg.seedMeasure.real (E_ev π τ x₀)
            ≤ (1 / (Nat.factorial m : ℝ)) *
                ∑ π : Equiv.Perm (Fin m), (Nat.factorial m : ℝ) / ((m - (π.symm x₀).1 : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun π _ => h_coset_bound π)) (by positivity)
        _ = ((Q_fib x₀).card : ℝ) * harmonicNum m := by
              rw [h_pi_sum]
              have hne : (Nat.factorial m : ℝ) ≠ 0 := ne_of_gt hm_fact_pos
              calc
                (1 / (Nat.factorial m : ℝ)) *
                    ((Nat.factorial m : ℝ) * ((Q_fib x₀).card : ℝ) * harmonicNum m)
                    = ((1 / (Nat.factorial m : ℝ)) * (Nat.factorial m : ℝ)) *
                        (((Q_fib x₀).card : ℝ) * harmonicNum m) := by ring
                _ = 1 * (((Q_fib x₀).card : ℝ) * harmonicNum m) := by
                      rw [one_div_mul_cancel hne]
                _ = ((Q_fib x₀).card : ℝ) * harmonicNum m := one_mul _
        _ = (Nat.factorial m : ℝ) * (harmonicNum m / (m : ℝ)) := by
              rw [hQ_card_rel, div_eq_mul_inv]
              have hne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
              calc
                ((Q_fib x₀).card : ℝ) * harmonicNum m
                    = 1 * (((Q_fib x₀).card : ℝ) * harmonicNum m) := (one_mul _).symm
                _ = ((m : ℝ) * (m : ℝ)⁻¹) * (((Q_fib x₀).card : ℝ) * harmonicNum m) := by
                      rw [mul_inv_cancel₀ hne]
                _ = (m : ℝ) * ((Q_fib x₀).card : ℝ) * (harmonicNum m * (m : ℝ)⁻¹) := by ring
    have h_univ_ne : (Finset.univ : Finset (Equiv.Perm (Fin m))).Nonempty := ⟨1, Finset.mem_univ 1⟩
    obtain ⟨τ, _, hτ⟩ := Finset.exists_le_of_sum_le h_univ_ne h_sum_P
    obtain ⟨h_alloc, h_opt, h_uniq⟩ := h_s2 m x₀ τ
    refine ⟨contractsVal x₀ τ, contractsOptAlloc τ, ?_, h_alloc, h_opt, h_uniq, ?_⟩
    · intro i
      apply h_s1 m (contractsWeight x₀ τ i)
      intro g
      unfold contractsWeight
      split_ifs <;> norm_num
    · refine ⟨τ x₀, x₀, ?_, hτ⟩
      simp [contractsOptAlloc]
  · 
    
    
    have h_fin2_sets : ∀ S : Finset (Fin 2), S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {0, 1} := by
      intro S
      by_cases h0 : (0 : Fin 2) ∈ S <;> by_cases h1 : (1 : Fin 2) ∈ S
      · right; right; right; ext x; fin_cases x <;> simp [h0, h1]
      · right; left; ext x; fin_cases x <;> simp [h0, h1]
      · right; right; left; ext x; fin_cases x <;> simp [h0, h1]
      · left; ext x; fin_cases x <;> simp [h0, h1]
    have h_univ_sets : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by
      ext S
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      exact h_fin2_sets S
    have h_perm2 : ∀ π : Equiv.Perm (Fin 2), π = 1 ∨ π = Equiv.swap 0 1 := by
      intro π
      have hne : π 0 ≠ π 1 := fun h => absurd (π.injective h) (by decide)
      have hfin2 : ∀ z : Fin 2, z = 0 ∨ z = 1 := by decide
      rcases hfin2 (π 0) with hp0 | hp0 <;> rcases hfin2 (π 1) with hp1 | hp1
      · exact absurd (hp0.trans hp1.symm) hne
      · left; ext x; fin_cases x <;> simp [hp0, hp1]
      · right; ext x; fin_cases x <;> simp [hp0, hp1]
      · exact absurd (hp0.trans hp1.symm) hne
    have h_univ_perm : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by
      ext π
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      exact h_perm2 π
    have h_s4 : ∀ w₀ w₁ : ℝ, 0 < w₀ → 0 < w₁ →
        IsGSValuation (twoItemVal w₀ w₁) ∧
        IsNonnegValuation (twoItemVal w₀ w₁) ∧
        optVal (twoItemVal w₀ w₁) = max w₀ w₁ ∧
        0 < optVal (twoItemVal w₀ w₁) := by
      intro w₀ w₁ hw₀ hw₁
      have hv_emp : twoItemVal w₀ w₁ ∅ = ((0 : ℝ) : WithBot ℝ) := by simp [twoItemVal]
      have hv_0 : twoItemVal w₀ w₁ {0} = ((w₀ : ℝ) : WithBot ℝ) := by
        simp [twoItemVal, show (1 : Fin 2) ≠ 0 by decide]
      have hv_1 : twoItemVal w₀ w₁ {1} = ((w₁ : ℝ) : WithBot ℝ) := by
        simp [twoItemVal, show (0 : Fin 2) ≠ 1 by decide]
      have hv_01 : twoItemVal w₀ w₁ {0, 1} = ((0 : ℝ) : WithBot ℝ) := by simp [twoItemVal]
      have h_gs : IsGSValuation (twoItemVal w₀ w₁) := by
        refine ⟨hv_emp, ?_⟩
        intro X Y _ _ x hx
        rcases h_fin2_sets X with rfl | rfl | rfl | rfl <;>
        rcases h_fin2_sets Y with rfl | rfl | rfl | rfl <;>
        fin_cases x
        all_goals (try (exfalso; revert hx; decide))
        · have he : ({0} : Finset (Fin 2)).erase 0 = ∅ := by decide
          have hi : insert (0 : Fin 2) (∅ : Finset (Fin 2)) = {0} := by decide
          refine le_trans ?_ (le_max_left _ _)
          rw [Fin.zero_eta, he, hi, hv_0, hv_emp, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
          linarith
        · have hmem : (1 : Fin 2) ∈ ({1} : Finset (Fin 2)) \ {0} := by decide
          have hs1 : insert (1 : Fin 2) (({0} : Finset (Fin 2)).erase 0) = {1} := by decide
          have hs2 : (insert (0 : Fin 2) ({1} : Finset (Fin 2))).erase 1 = {0} := by decide
          refine le_trans ?_ (le_max_right _ _)
          refine le_trans ?_ (Finset.le_sup (f := fun y =>
            twoItemVal w₀ w₁ (insert y (({0} : Finset (Fin 2)).erase 0)) +
            twoItemVal w₀ w₁ ((insert (0 : Fin 2) ({1} : Finset (Fin 2))).erase y)) hmem)
          dsimp only
          rw [hs1, hs2, hv_0, hv_1, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
          linarith
        · have he : ({1} : Finset (Fin 2)).erase 1 = ∅ := by decide
          have hi : insert (1 : Fin 2) (∅ : Finset (Fin 2)) = {1} := by decide
          refine le_trans ?_ (le_max_left _ _)
          rw [Fin.mk_one, he, hi, hv_1, hv_emp, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
          linarith
        · have hmem : (0 : Fin 2) ∈ ({0} : Finset (Fin 2)) \ {1} := by decide
          have hs1 : insert (0 : Fin 2) (({1} : Finset (Fin 2)).erase 1) = {0} := by decide
          have hs2 : (insert (1 : Fin 2) ({0} : Finset (Fin 2))).erase 0 = {1} := by decide
          refine le_trans ?_ (le_max_right _ _)
          refine le_trans ?_ (Finset.le_sup (f := fun y =>
            twoItemVal w₀ w₁ (insert y (({1} : Finset (Fin 2)).erase 1)) +
            twoItemVal w₀ w₁ ((insert (1 : Fin 2) ({0} : Finset (Fin 2))).erase y)) hmem)
          dsimp only
          rw [hs1, hs2, hv_1, hv_0, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
          linarith
        · have he : ({0, 1} : Finset (Fin 2)).erase 0 = {1} := by decide
          have hi : insert (0 : Fin 2) (∅ : Finset (Fin 2)) = {0} := by decide
          refine le_trans ?_ (le_max_left _ _)
          rw [Fin.zero_eta, he, hi, hv_01, hv_emp, hv_1, hv_0, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
          linarith
        · have he : ({0, 1} : Finset (Fin 2)).erase 1 = {0} := by decide
          have hi : insert (1 : Fin 2) (∅ : Finset (Fin 2)) = {1} := by decide
          refine le_trans ?_ (le_max_left _ _)
          rw [Fin.mk_one, he, hi, hv_01, hv_emp, hv_0, hv_1, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
          linarith
        · have he : ({0, 1} : Finset (Fin 2)).erase 1 = {0} := by decide
          have hi : insert (1 : Fin 2) ({0} : Finset (Fin 2)) = {0, 1} := by decide
          refine le_trans ?_ (le_max_left _ _)
          rw [Fin.mk_one, he, hi, hv_01, hv_0, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
          linarith
        · have he : ({0, 1} : Finset (Fin 2)).erase 0 = {1} := by decide
          have hi : insert (0 : Fin 2) ({1} : Finset (Fin 2)) = {0, 1} := by decide
          refine le_trans ?_ (le_max_left _ _)
          rw [Fin.zero_eta, he, hi, hv_01, hv_1, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
          linarith
      have h_nonneg : IsNonnegValuation (twoItemVal w₀ w₁) := by
        intro S
        rcases h_fin2_sets S with rfl | rfl | rfl | rfl <;>
        simp only [hv_emp, hv_0, hv_1, hv_01, WithBot.coe_le_coe] <;> linarith
      have h_sup : (Finset.univ : Finset (Finset (Fin 2))).sup (twoItemVal w₀ w₁) =
          ((max w₀ w₁ : ℝ) : WithBot ℝ) := by
        apply le_antisymm
        · apply Finset.sup_le
          intro S _
          rcases h_fin2_sets S with rfl | rfl | rfl | rfl <;>
          simp only [hv_emp, hv_0, hv_1, hv_01, WithBot.coe_le_coe]
          · exact le_trans (le_of_lt hw₀) (le_max_left _ _)
          · exact le_max_left _ _
          · exact le_max_right _ _
          · exact le_trans (le_of_lt hw₀) (le_max_left _ _)
        · change ((w₀ ⊔ w₁ : ℝ) : WithBot ℝ) ≤ _
          rw [WithBot.coe_sup]
          apply sup_le
          · rw [← hv_0]; exact Finset.le_sup (Finset.mem_univ {0})
          · rw [← hv_1]; exact Finset.le_sup (Finset.mem_univ {1})
      have h_opt : optVal (twoItemVal w₀ w₁) = max w₀ w₁ := by
        unfold optVal
        rw [h_sup, WithBot.unbotD_coe]
      exact ⟨h_gs, h_nonneg, h_opt, h_opt.symm ▸ lt_of_lt_of_le hw₀ (le_max_left _ _)⟩
    have h_s5 : ∀ alg : OnlineSelectionAlg 2,
        ∃ q : ℝ → ℝ, (∀ w : ℝ, 0 ≤ q w ∧ q w ≤ 1) ∧
          ∀ w₀ w₁ : ℝ, 0 ≤ w₀ → 0 ≤ w₁ →
            ∃ E₁ E₂ : ℝ,
              expectedSelectionVal alg (twoItemVal w₀ w₁) = ((E₁ : ℝ) : WithBot ℝ) ∧
              expectedSelectionVal alg (twoItemVal w₁ w₀) = ((E₂ : ℝ) : WithBot ℝ) ∧
              E₁ + E₂ ≤ (1 + q w₀ - q w₁) * w₀ + (1 - q w₀ + q w₁) * w₁ := by
      intro alg
      let firstStepOracle (x : Fin 2) (w : ℝ) :
          {T : Finset (Fin 2) // T ⊆ insert x ([] : List (Fin 2)).toFinset} → WithBot ℝ :=
        fun ⟨T, _⟩ => if x ∈ T then ((w : ℝ) : WithBot ℝ) else ((0 : ℝ) : WithBot ℝ)
      let E_set (x : Fin 2) (w : ℝ) : Set alg.Seed :=
        {ω | (alg.det ω).step [] x ∅ (firstStepOracle x w) = true}
      let p (x : Fin 2) (w : ℝ) : ℝ := alg.seedMeasure.real (E_set x w)
      let q (w : ℝ) : ℝ := (p 0 w + p 1 w) / 2
      have hp_bounds : ∀ (x : Fin 2) (w : ℝ), 0 ≤ p x w ∧ p x w ≤ 1 := by
        intro x w
        refine ⟨MeasureTheory.measureReal_nonneg, ?_⟩
        exact le_trans (MeasureTheory.measureReal_mono (Set.subset_univ _))
          (le_of_eq MeasureTheory.probReal_univ)
      have hq_bounds : ∀ w : ℝ, 0 ≤ q w ∧ q w ≤ 1 := by
        intro w
        have h0 := hp_bounds 0 w
        have h1 := hp_bounds 1 w
        dsimp only [q]
        constructor <;> linarith
      have h_meas_E : ∀ (x : Fin 2) (w : ℝ), MeasurableSet (E_set x w) :=
        fun x w => alg.meas_step [] x ∅ (firstStepOracle x w) true
      have h_compl_E : ∀ (x : Fin 2) (w : ℝ), alg.seedMeasure.real (E_set x w)ᶜ = 1 - p x w := by
        intro x w
        rw [MeasureTheory.measureReal_compl (h_meas_E x w), MeasureTheory.probReal_univ]
      have h_single : ∀ w₀ w₁ : ℝ, 0 ≤ w₀ → 0 ≤ w₁ →
          ∃ E : ℝ,
            expectedSelectionVal alg (twoItemVal w₀ w₁) = ((E : ℝ) : WithBot ℝ) ∧
            E ≤ (1 / 2) * ((p 0 w₀ + (1 - p 1 w₁)) * w₀ + ((1 - p 0 w₀) + p 1 w₁) * w₁) := by
        intro w₀ w₁ hw₀ hw₁
        let v := twoItemVal w₀ w₁
        have hv_ne_bot : ∀ S : Finset (Fin 2), v S ≠ ⊥ := by
          intro S
          rcases h_fin2_sets S with rfl | rfl | rfl | rfl <;>
          simp [v, twoItemVal, show (1 : Fin 2) ≠ 0 by decide, show (0 : Fin 2) ≠ 1 by decide]
        have h_no_bot : ¬ ∃ S : Finset (Fin 2), 0 < algSelectionProb alg v S ∧ v S = ⊥ := by
          rintro ⟨S, _, hbot⟩
          exact hv_ne_bot S hbot
        let E := ∑ S : Finset (Fin 2), algSelectionProb alg v S * realVal v S
        refine ⟨E, ?_, ?_⟩
        · unfold expectedSelectionVal
          rw [if_neg h_no_bot]
        · have hr_emp : realVal v ∅ = 0 := by simp [realVal, v, twoItemVal]
          have hr_0 : realVal v {0} = w₀ := by
            simp [realVal, v, twoItemVal, show (1 : Fin 2) ≠ 0 by decide]
          have hr_1 : realVal v {1} = w₁ := by
            simp [realVal, v, twoItemVal, show (0 : Fin 2) ≠ 1 by decide]
          have hr_01 : realVal v {0, 1} = 0 := by simp [realVal, v, twoItemVal]
          have hE_eq : E = algSelectionProb alg v {0} * w₀ + algSelectionProb alg v {1} * w₁ := by
            dsimp only [E]
            rw [h_univ_sets]
            rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
                Finset.sum_insert (by decide), Finset.sum_singleton]
            rw [hr_emp, hr_0, hr_1, hr_01]
            ring
          have hprob_expand : ∀ S : Finset (Fin 2),
              algSelectionProb alg v S = (1 / 2) *
                (alg.seedMeasure.real {ω | runDetSelection (alg.det ω) v 1 = S} +
                 alg.seedMeasure.real {ω | runDetSelection (alg.det ω) v (Equiv.swap 0 1) = S}) := by
            intro S
            unfold algSelectionProb
            have hne_perm : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by
              intro h
              have := Equiv.Perm.ext_iff.mp h 0
              revert this; decide
            have hnot_mem : (1 : Equiv.Perm (Fin 2)) ∉ ({Equiv.swap 0 1} : Finset (Equiv.Perm (Fin 2))) := by
              simp only [Finset.mem_singleton]
              exact hne_perm
            rw [h_univ_perm, Finset.sum_insert hnot_mem, Finset.sum_singleton]
            norm_num
          have h_orc_0 : (fun ⟨T, _⟩ => v T : {T : Finset (Fin 2) // T ⊆ insert (0 : Fin 2) ([] : List (Fin 2)).toFinset} → WithBot ℝ) =
              firstStepOracle 0 w₀ := by
            funext ⟨T, hT⟩
            have h1not : (1 : Fin 2) ∉ T := fun h1 => by
              have := hT h1; revert this; decide
            simp [v, twoItemVal, firstStepOracle, h1not]
          have h_orc_1 : (fun ⟨T, _⟩ => v T : {T : Finset (Fin 2) // T ⊆ insert (1 : Fin 2) ([] : List (Fin 2)).toFinset} → WithBot ℝ) =
              firstStepOracle 1 w₁ := by
            funext ⟨T, hT⟩
            have h0not : (0 : Fin 2) ∉ T := fun h0 => by
              have := hT h0; revert this; decide
            simp [v, twoItemVal, firstStepOracle, h0not]
          have h_run_1 : ∀ d : DetSelectionAlg 2,
              runDetSelection d v 1 =
                (let acc1 : Finset (Fin 2) :=
                   if d.step [] 0 ∅ (fun ⟨T, _⟩ => v T) then insert 0 ∅ else ∅
                 if d.step [0] 1 acc1 (fun ⟨T, _⟩ => v T) then insert 1 acc1 else acc1) :=
            fun _ => rfl
          have h_run_sw : ∀ d : DetSelectionAlg 2,
              runDetSelection d v (Equiv.swap 0 1) =
                (let x0 : Fin 2 := (Equiv.swap 0 1) ⟨0, by decide⟩
                 let x1 : Fin 2 := (Equiv.swap 0 1) ⟨1, by decide⟩
                 let acc1 : Finset (Fin 2) :=
                   if d.step [] x0 ∅ (fun ⟨T, _⟩ => v T) then insert x0 ∅ else ∅
                 if d.step [x0] x1 acc1 (fun ⟨T, _⟩ => v T) then insert x1 acc1 else acc1) :=
            fun _ => rfl
          have hsw0 : (Equiv.swap (0 : Fin 2) 1) ⟨0, by decide⟩ = 1 := by decide
          have hsw1 : (Equiv.swap (0 : Fin 2) 1) ⟨1, by decide⟩ = 0 := by decide
          have h_sub_1_0 : {ω | runDetSelection (alg.det ω) v 1 = {0}} ⊆ E_set 0 w₀ := by
            intro ω hω
            change runDetSelection (alg.det ω) v 1 = {0} at hω
            rw [h_run_1] at hω; dsimp only at hω; rw [h_orc_0] at hω
            change (alg.det ω).step [] 0 ∅ (firstStepOracle 0 w₀) = true
            cases hdec1 : (alg.det ω).step [] 0 ∅ (firstStepOracle 0 w₀)
            · exfalso
              rw [hdec1] at hω
              simp only [Bool.false_eq_true, ↓reduceIte] at hω
              split_ifs at hω <;> (revert hω; decide)
            · rfl
          have h_sub_1_1 : {ω | runDetSelection (alg.det ω) v 1 = {1}} ⊆ (E_set 0 w₀)ᶜ := by
            intro ω hω hmem
            change runDetSelection (alg.det ω) v 1 = {1} at hω
            change (alg.det ω).step [] 0 ∅ (firstStepOracle 0 w₀) = true at hmem
            rw [h_run_1] at hω; dsimp only at hω; rw [h_orc_0, hmem] at hω
            simp only [↓reduceIte] at hω
            split_ifs at hω <;> (revert hω; decide)
          have h_sub_sw_1 : {ω | runDetSelection (alg.det ω) v (Equiv.swap 0 1) = {1}} ⊆ E_set 1 w₁ := by
            intro ω hω
            change runDetSelection (alg.det ω) v (Equiv.swap 0 1) = {1} at hω
            rw [h_run_sw] at hω; dsimp only at hω; rw [hsw0, hsw1, h_orc_1] at hω
            change (alg.det ω).step [] 1 ∅ (firstStepOracle 1 w₁) = true
            cases hdec1 : (alg.det ω).step [] 1 ∅ (firstStepOracle 1 w₁)
            · exfalso
              rw [hdec1] at hω
              simp only [Bool.false_eq_true, ↓reduceIte] at hω
              split_ifs at hω <;> (revert hω; decide)
            · rfl
          have h_sub_sw_0 : {ω | runDetSelection (alg.det ω) v (Equiv.swap 0 1) = {0}} ⊆ (E_set 1 w₁)ᶜ := by
            intro ω hω hmem
            change runDetSelection (alg.det ω) v (Equiv.swap 0 1) = {0} at hω
            change (alg.det ω).step [] 1 ∅ (firstStepOracle 1 w₁) = true at hmem
            rw [h_run_sw] at hω; dsimp only at hω; rw [hsw0, hsw1, h_orc_1, hmem] at hω
            simp only [↓reduceIte] at hω
            split_ifs at hω <;> (revert hω; decide)
          have hm_1_0 : alg.seedMeasure.real {ω | runDetSelection (alg.det ω) v 1 = {0}} ≤ p 0 w₀ :=
            MeasureTheory.measureReal_mono h_sub_1_0
          have hm_1_1 : alg.seedMeasure.real {ω | runDetSelection (alg.det ω) v 1 = {1}} ≤ 1 - p 0 w₀ :=
            (MeasureTheory.measureReal_mono h_sub_1_1).trans (le_of_eq (h_compl_E 0 w₀))
          have hm_sw_1 : alg.seedMeasure.real {ω | runDetSelection (alg.det ω) v (Equiv.swap 0 1) = {1}} ≤ p 1 w₁ :=
            MeasureTheory.measureReal_mono h_sub_sw_1
          have hm_sw_0 : alg.seedMeasure.real {ω | runDetSelection (alg.det ω) v (Equiv.swap 0 1) = {0}} ≤ 1 - p 1 w₁ :=
            (MeasureTheory.measureReal_mono h_sub_sw_0).trans (le_of_eq (h_compl_E 1 w₁))
          rw [hE_eq, hprob_expand {0}, hprob_expand {1}]
          nlinarith
      refine ⟨q, hq_bounds, ?_⟩
      intro w₀ w₁ hw₀ hw₁
      obtain ⟨E₁, hE₁_eq, hE₁_le⟩ := h_single w₀ w₁ hw₀ hw₁
      obtain ⟨E₂, hE₂_eq, hE₂_le⟩ := h_single w₁ w₀ hw₁ hw₀
      refine ⟨E₁, E₂, hE₁_eq, hE₂_eq, ?_⟩
      dsimp only [q]
      linarith
    intro δ hδ
    let K : ℕ := Nat.ceil (1 / δ) + 1
    let ϱ : ℝ := max 2 (1 / δ)
    have hK_pos : 1 ≤ K := by omega
    have hϱ_ge2 : (2 : ℝ) ≤ ϱ := le_max_left _ _
    have hϱ_gt1 : (1 : ℝ) < ϱ := by linarith
    have hϱ_pos : (0 : ℝ) < ϱ := by linarith
    have h_inv_ϱ : 1 / ϱ ≤ δ := by
      have h1 : 1 / δ ≤ ϱ := le_max_right _ _
      rw [div_le_iff₀ hϱ_pos]
      have h2 : 1 ≤ ϱ * δ := by
        have := mul_le_mul_of_nonneg_right h1 (le_of_lt hδ)
        rwa [one_div_mul_cancel (ne_of_gt hδ)] at this
      linarith
    have h_K_delta : 1 < δ * (K : ℝ) := by
      have hceil : 1 / δ ≤ (Nat.ceil (1 / δ) : ℝ) := Nat.le_ceil (1 / δ)
      have hK_lt : (Nat.ceil (1 / δ) : ℝ) < (K : ℝ) := by
        dsimp only [K]; push_cast; linarith
      have hlt : 1 / δ < (K : ℝ) := lt_of_le_of_lt hceil hK_lt
      have := mul_lt_mul_of_pos_left hlt hδ
      rwa [mul_one_div_cancel (ne_of_gt hδ)] at this
    let fam : List (ItemValuation 2) :=
      (List.range K).flatMap (fun k =>
        [twoItemVal (ϱ ^ (k + 1)) (ϱ ^ k), twoItemVal (ϱ ^ k) (ϱ ^ (k + 1))])
    refine ⟨fam, ?_, ?_, ?_⟩
    · intro h_emp
      have hmem : twoItemVal (ϱ ^ 1) (ϱ ^ 0) ∈ fam := by
        dsimp only [fam]
        rw [List.mem_flatMap]
        exact ⟨0, List.mem_range.mpr (by omega), by simp⟩
      rw [h_emp] at hmem
      simp at hmem
    · intro v hv
      dsimp only [fam] at hv
      rw [List.mem_flatMap] at hv
      rcases hv with ⟨k, _, hk_mem⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk_mem
      have hp1 : 0 < ϱ ^ (k + 1) := pow_pos hϱ_pos (k + 1)
      have hp0 : 0 < ϱ ^ k := pow_pos hϱ_pos k
      rcases hk_mem with rfl | rfl
      · obtain ⟨h1, h2, _, h4⟩ := h_s4 (ϱ ^ (k + 1)) (ϱ ^ k) hp1 hp0
        exact ⟨h1, h2, h4⟩
      · obtain ⟨h1, h2, _, h4⟩ := h_s4 (ϱ ^ k) (ϱ ^ (k + 1)) hp0 hp1
        exact ⟨h1, h2, h4⟩
    · intro alg
      obtain ⟨q, hq, hbound⟩ := h_s5 alg
      let a (k : ℕ) : ℝ :=
        ((1 + q (ϱ ^ (k + 1)) - q (ϱ ^ k)) * ϱ ^ (k + 1) +
         (1 - q (ϱ ^ (k + 1)) + q (ϱ ^ k)) * ϱ ^ k) / (2 * ϱ ^ (k + 1))
      have ha_eq : ∀ k : ℕ,
          a k = (1 / 2 + 1 / (2 * ϱ)) + (1 / 2) * (1 - 1 / ϱ) * (q (ϱ ^ (k + 1)) - q (ϱ ^ k)) := by
        intro k
        dsimp only [a]
        have hpow_ne : ϱ ^ k ≠ 0 := ne_of_gt (pow_pos hϱ_pos k)
        have hϱ_ne : ϱ ≠ 0 := ne_of_gt hϱ_pos
        rw [pow_succ]
        field_simp
        ring
      have h_sum_a : ∑ k ∈ Finset.range K, a k ≤ ∑ _k ∈ Finset.range K, (1 / 2 + δ) := by
        have h1 : ∑ k ∈ Finset.range K, a k =
            (K : ℝ) * (1 / 2 + 1 / (2 * ϱ)) + (1 / 2) * (1 - 1 / ϱ) * (q (ϱ ^ K) - q (ϱ ^ 0)) := by
          calc
            ∑ k ∈ Finset.range K, a k
                = ∑ k ∈ Finset.range K,
                    ((1 / 2 + 1 / (2 * ϱ)) + (1 / 2) * (1 - 1 / ϱ) * (q (ϱ ^ (k + 1)) - q (ϱ ^ k))) :=
                  Finset.sum_congr rfl (fun k _ => ha_eq k)
            _ = (∑ _k ∈ Finset.range K, (1 / 2 + 1 / (2 * ϱ))) +
                (1 / 2) * (1 - 1 / ϱ) * ∑ k ∈ Finset.range K, (q (ϱ ^ (k + 1)) - q (ϱ ^ k)) := by
                  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            _ = (K : ℝ) * (1 / 2 + 1 / (2 * ϱ)) + (1 / 2) * (1 - 1 / ϱ) * (q (ϱ ^ K) - q (ϱ ^ 0)) := by
                  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                      Finset.sum_range_sub (fun k => q (ϱ ^ k)) K]
        have h2 : ∑ _k ∈ Finset.range K, (1 / 2 + δ) = (K : ℝ) * (1 / 2 + δ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [h1, h2]
        have hqK : q (ϱ ^ K) ≤ 1 := (hq (ϱ ^ K)).2
        have hq0 : 0 ≤ q (ϱ ^ 0) := (hq (ϱ ^ 0)).1
        have h_coeff_nonneg : 0 ≤ (1 / 2) * (1 - 1 / ϱ) := by
          have : 1 / ϱ ≤ 1 := by rw [div_le_one hϱ_pos]; linarith
          linarith
        have h_coeff_le_half : (1 / 2) * (1 - 1 / ϱ) ≤ 1 / 2 := by
          have : 0 ≤ 1 / ϱ := by positivity
          linarith
        have h_term2 : (1 / 2) * (1 - 1 / ϱ) * (q (ϱ ^ K) - q (ϱ ^ 0)) ≤ 1 / 2 := by
          calc
            (1 / 2) * (1 - 1 / ϱ) * (q (ϱ ^ K) - q (ϱ ^ 0))
                ≤ (1 / 2) * (1 - 1 / ϱ) * 1 :=
                  mul_le_mul_of_nonneg_left (by linarith) h_coeff_nonneg
            _ ≤ 1 / 2 := by linarith
        have hK_nonneg : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
        have h_term1 : (K : ℝ) * (1 / 2 + 1 / (2 * ϱ)) ≤ (K : ℝ) * (1 / 2 + δ / 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hK_nonneg
          have : 1 / (2 * ϱ) = (1 / 2) * (1 / ϱ) := by ring
          linarith
        linarith
      have h_range_ne : (Finset.range K).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
      obtain ⟨k, hk_mem, hak⟩ := Finset.exists_le_of_sum_le h_range_ne h_sum_a
      have hk_lt : k < K := Finset.mem_range.mp hk_mem
      have hp1 : 0 < ϱ ^ (k + 1) := pow_pos hϱ_pos (k + 1)
      have hp0 : 0 < ϱ ^ k := pow_pos hϱ_pos k
      have h_unnorm :
          (1 + q (ϱ ^ (k + 1)) - q (ϱ ^ k)) * ϱ ^ (k + 1) +
          (1 - q (ϱ ^ (k + 1)) + q (ϱ ^ k)) * ϱ ^ k ≤
            2 * (1 / 2 + δ) * ϱ ^ (k + 1) := by
        have h2p : 0 < 2 * ϱ ^ (k + 1) := by linarith
        have := (div_le_iff₀ h2p).mp hak
        linarith
      obtain ⟨E₁, E₂, hE₁, hE₂, hsumE⟩ := hbound (ϱ ^ (k + 1)) (ϱ ^ k) (le_of_lt hp1) (le_of_lt hp0)
      have hE12 : E₁ + E₂ ≤ 2 * (1 / 2 + δ) * ϱ ^ (k + 1) := le_trans hsumE h_unnorm
      have hpow_le : ϱ ^ k ≤ ϱ ^ (k + 1) :=
        pow_le_pow_right₀ (le_of_lt hϱ_gt1) (Nat.le_succ k)
      have hopt1 : optVal (twoItemVal (ϱ ^ (k + 1)) (ϱ ^ k)) = ϱ ^ (k + 1) := by
        rw [(h_s4 (ϱ ^ (k + 1)) (ϱ ^ k) hp1 hp0).2.2.1, max_eq_left hpow_le]
      have hopt2 : optVal (twoItemVal (ϱ ^ k) (ϱ ^ (k + 1))) = ϱ ^ (k + 1) := by
        rw [(h_s4 (ϱ ^ k) (ϱ ^ (k + 1)) hp0 hp1).2.2.1, max_eq_right hpow_le]
      by_cases hE₁_case : E₁ ≤ (1 / 2 + δ) * ϱ ^ (k + 1)
      · refine ⟨twoItemVal (ϱ ^ (k + 1)) (ϱ ^ k), ?_, ?_⟩
        · dsimp only [fam]
          rw [List.mem_flatMap]
          exact ⟨k, List.mem_range.mpr hk_lt, by simp⟩
        · rw [hE₁, hopt1, WithBot.coe_le_coe]
          exact hE₁_case
      · have hE₂_case : E₂ ≤ (1 / 2 + δ) * ϱ ^ (k + 1) := by linarith
        refine ⟨twoItemVal (ϱ ^ k) (ϱ ^ (k + 1)), ?_, ?_⟩
        · dsimp only [fam]
          rw [List.mem_flatMap]
          exact ⟨k, List.mem_range.mpr hk_lt, by simp⟩
        · rw [hE₂, hopt2, WithBot.coe_le_coe]
          exact hE₂_case

end

end


section NamedResults

/-- **Proposition C.2 (`prop:two-items`, Two items)**:
For every `δ > 0`, there is a finite nonempty family of nonnegative GS valuations on two items such
that every randomized non-clairvoyant online algorithm achieves expected value at most
`(1 / 2 + δ) OPT(v)` on some `v` in the family. -/
theorem prop_C_2_two_items (δ : ℝ) (hδ : 0 < δ) :
    ∃ fam : List (ItemValuation 2),
      fam ≠ [] ∧
      (∀ v ∈ fam, IsGSValuation v ∧ IsNonnegValuation v ∧ 0 < optVal v) ∧
      ∀ alg : OnlineSelectionAlg 2,
        ∃ v ∈ fam,
          expectedSelectionVal alg v ≤ (((1 / 2 + δ) * optVal v : ℝ) : WithBot ℝ) :=
  thm_lower_contracts_and_two_items.2 δ hδ

/-- **Proposition C.4 (`prop:contracts`, No per-pair guarantee)**:
For every `m ≥ 1` and every randomized non-clairvoyant online welfare algorithm `alg` on `m` items
and `m` bidders, there is a unit-demand (nonnegative monotone GS) instance with a unique optimal
allocation `X*` in which some pair `(i, g)` with `g ∈ X*_i` is realized with probability at most
`H_m / m`. -/
theorem prop_C_4_contracts (m : ℕ) (hm : 1 ≤ m) (alg : OnlineWelfareAlg m m) :
    ∃ (v : Fin m → ItemValuation m) (Xstar : Fin m → Finset (Fin m)),
      (∀ i : Fin m,
        IsUnitDemandValuation (v i) ∧
        IsGSValuation (v i) ∧
        IsNonnegValuation (v i) ∧
        IsMonotoneValuation (v i)) ∧
      IsAllocOf Finset.univ Xstar ∧
      allocWelfare v Xstar = ((optWelfare v : ℝ) : WithBot ℝ) ∧
      (∀ Y : Fin m → Finset (Fin m),
        IsAllocOf Finset.univ Y →
        allocWelfare v Y = ((optWelfare v : ℝ) : WithBot ℝ) → Y = Xstar) ∧
      ∃ (i : Fin m) (g : Fin m), g ∈ Xstar i ∧
        (∑ A ∈ (Finset.univ : Finset (Fin m → Finset (Fin m))).filter (fun A => g ∈ A i),
          algWelfareProb alg v A) ≤ harmonicNum m / (m : ℝ) :=
  thm_lower_contracts_and_two_items.1 m hm alg

/-- Restrict a 1-bidder `OnlineWelfareAlg n 1` to an `OnlineSelectionAlg n` (Appendix C opening). -/
noncomputable def welfareAlgToSelectionAlg {n : ℕ} (alg : OnlineWelfareAlg n 1) :
    OnlineSelectionAlg n where
  Seed := alg.Seed
  measSeed := alg.measSeed
  seedMeasure := alg.seedMeasure
  isProb := alg.isProb
  det := fun ω =>
    { step := fun prev x accepted oracle =>
        ((alg.det ω).step prev x (fun _ => accepted) (fun _ => oracle)).isSome }
  meas_step := by
    intro prev x accepted oracle b
    cases b with
    | false =>
        have heq : {ω : alg.Seed |
            ((alg.det ω).step prev x (fun _ => accepted) (fun _ => oracle)).isSome = false} =
            {ω : alg.Seed | (alg.det ω).step prev x (fun _ => accepted) (fun _ => oracle) = none} := by
          ext ω
          simp
        rw [heq]
        exact alg.meas_step prev x (fun _ => accepted) (fun _ => oracle) none
    | true =>
        have heq : {ω : alg.Seed |
            ((alg.det ω).step prev x (fun _ => accepted) (fun _ => oracle)).isSome = true} =
            {ω : alg.Seed | (alg.det ω).step prev x (fun _ => accepted) (fun _ => oracle) = some 0} := by
          ext ω
          simp only [Set.mem_setOf_eq, Option.isSome_iff_exists]
          constructor
          · rintro ⟨i, hi⟩
            rw [Subsingleton.elim i 0] at hi
            exact hi
          · intro h
            exact ⟨0, h⟩
        rw [heq]
        exact alg.meas_step prev x (fun _ => accepted) (fun _ => oracle) (some 0)

/-- **Appendix C Opening Remark (`app:lower`, One-bidder selection bounds apply to welfare)**:
For `m = 1` bidder with valuation `v : ItemValuation n`, running any `alg : OnlineWelfareAlg n 1` on
`fun _ : Fin 1 => v` induces the exact same output law, expected value, and offline optimum as
`welfareAlgToSelectionAlg alg` on `v`. -/
theorem rem_C_single_bidder_transfer {n : ℕ} (alg : OnlineWelfareAlg n 1) (v : ItemValuation n) :
    let v1 : Fin 1 → ItemValuation n := fun _ => v
    (∀ S : Finset (Fin n),
      algSelectionProb (welfareAlgToSelectionAlg alg) v S = algWelfareProb alg v1 (fun _ => S)) ∧
    expectedSelectionVal (welfareAlgToSelectionAlg alg) v = expectedWelfareVal alg v1 ∧
    optVal v = optWelfare v1 := by
  intro v1
  have h_steps : ∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
      let stS := runDetSelectionSteps ((welfareAlgToSelectionAlg alg).det ω) v π k hk
      let stW := runDetWelfareSteps (alg.det ω) v1 π k hk
      stS.1 = stW.1 ∧ (fun _ : Fin 1 => stS.2) = stW.2 := by
    intro ω π k
    induction k with
    | zero =>
        intro hk
        simp [runDetSelectionSteps, runDetWelfareSteps]
    | succ k ih =>
        intro hk
        obtain ⟨h1, h2⟩ := ih (Nat.le_of_succ_le hk)
        dsimp only [runDetSelectionSteps, runDetWelfareSteps]
        have hstep_eq :
            ((welfareAlgToSelectionAlg alg).det ω).step
              (runDetSelectionSteps ((welfareAlgToSelectionAlg alg).det ω) v π k (Nat.le_of_succ_le hk)).1
              (π ⟨k, hk⟩)
              (runDetSelectionSteps ((welfareAlgToSelectionAlg alg).det ω) v π k (Nat.le_of_succ_le hk)).2
              (fun ⟨T, _⟩ => v T) =
            ((alg.det ω).step
              (runDetWelfareSteps (alg.det ω) v1 π k (Nat.le_of_succ_le hk)).1
              (π ⟨k, hk⟩)
              (runDetWelfareSteps (alg.det ω) v1 π k (Nat.le_of_succ_le hk)).2
              (fun i ⟨T, _⟩ => v1 i T)).isSome := by
          have hdep : ∀ (l₁ l₂ : List (Fin n))
              (b₁ b₂ : Fin 1 → Finset (Fin n)),
              l₁ = l₂ → b₁ = b₂ →
              ((alg.det ω).step l₁ (π ⟨k, hk⟩) b₁ (fun _ ⟨T, _⟩ => v T)).isSome =
              ((alg.det ω).step l₂ (π ⟨k, hk⟩) b₂ (fun i ⟨T, _⟩ => v1 i T)).isSome := by
            rintro l₁ _ b₁ _ rfl rfl
            rfl
          exact hdep _ _ _ _ h1 h2
        rw [hstep_eq, h1]
        refine ⟨rfl, ?_⟩
        cases hdec : (alg.det ω).step
            (runDetWelfareSteps (alg.det ω) v1 π k (Nat.le_of_succ_le hk)).1
            (π ⟨k, hk⟩)
            (runDetWelfareSteps (alg.det ω) v1 π k (Nat.le_of_succ_le hk)).2
            (fun i ⟨T, _⟩ => v1 i T) with
        | none =>
            simp [h2]
        | some i =>
            have hi : i = 0 := Subsingleton.elim i 0
            subst hi
            ext j
            have hj : j = 0 := Subsingleton.elim j 0
            subst hj
            have h20 := congr_fun h2 0
            simp [h20]
  have h_prob : ∀ S : Finset (Fin n),
      algSelectionProb (welfareAlgToSelectionAlg alg) v S = algWelfareProb alg v1 (fun _ => S) := by
    intro S
    simp only [algSelectionProb, algWelfareProb, runDetSelection, runDetWelfare]
    congr 1
    refine Finset.sum_congr rfl (fun π _ => ?_)
    have hmeas_eq :
        {ω : alg.Seed | (runDetSelectionSteps ((welfareAlgToSelectionAlg alg).det ω) v π n (le_refl n)).2 = S} =
        {ω : alg.Seed | (runDetWelfareSteps (alg.det ω) v1 π n (le_refl n)).2 = fun _ => S} := by
      ext ω
      obtain ⟨_, h2⟩ := h_steps ω π n (le_refl n)
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h
        rw [← h2, h]
      · intro h
        have h20 := congr_fun h2 0
        rw [h20]
        exact congr_fun h 0
    change (welfareAlgToSelectionAlg alg).seedMeasure.real
        {ω : alg.Seed | (runDetSelectionSteps ((welfareAlgToSelectionAlg alg).det ω) v π n (le_refl n)).2 = S} = _
    rw [hmeas_eq]
    rfl
  let e : Finset (Fin n) ≃ (Fin 1 → Finset (Fin n)) :=
    { toFun := fun S _ => S
      invFun := fun X => X 0
      left_inv := fun _ => rfl
      right_inv := fun X => by ext i; rw [Subsingleton.elim i 0] }
  refine ⟨h_prob, ?_, ?_⟩
  · simp only [expectedSelectionVal, expectedWelfareVal]
    have h_bot_iff : (∃ S, 0 < algSelectionProb (welfareAlgToSelectionAlg alg) v S ∧ v S = ⊥) ↔
        (∃ X, 0 < algWelfareProb alg v1 X ∧ allocWelfare v1 X = ⊥) := by
      constructor
      · rintro ⟨S, hpos, hbot⟩
        refine ⟨e S, ?_, ?_⟩
        · simpa [e, h_prob S] using hpos
        · simp [allocWelfare, v1, e, hbot]
      · rintro ⟨X, hpos, hbot⟩
        refine ⟨X 0, ?_, ?_⟩
        · have hX : (fun _ : Fin 1 => X 0) = X := e.right_inv X
          rw [h_prob (X 0), hX]
          exact hpos
        · simpa [allocWelfare, v1] using hbot
    by_cases hb : ∃ S, 0 < algSelectionProb (welfareAlgToSelectionAlg alg) v S ∧ v S = ⊥
    · rw [if_pos hb, if_pos (h_bot_iff.mp hb)]
    · rw [if_neg hb, if_neg (mt h_bot_iff.mpr hb)]
      congr 1
      refine Fintype.sum_equiv e _ _ (fun S => ?_)
      simp [e, h_prob S, allocWelfare, v1, realVal]
  · simp only [optVal, optWelfare, optWelfareOn]
    congr 1
    apply le_antisymm
    · refine Finset.sup_le (fun S _ => ?_)
      have hmem : e S ∈ (Finset.univ : Finset (Fin 1 → Finset (Fin n))).filter
          (fun X => IsAllocOf Finset.univ X) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsAllocOf, Finset.subset_univ,
          implies_true, IsPairwiseDisjoint]
        intro i j hij
        exact absurd (Subsingleton.elim i j) hij
      have hle := Finset.le_sup (f := allocWelfare v1) hmem
      simpa [allocWelfare, v1, e] using hle
    · refine Finset.sup_le (fun X _ => ?_)
      have hle := Finset.le_sup (f := v) (Finset.mem_univ (X 0))
      simpa [allocWelfare, v1] using hle

end NamedResults

end GrossSubstitutesWelfare
