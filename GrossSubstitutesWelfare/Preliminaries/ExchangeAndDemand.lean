import GrossSubstitutesWelfare.Defs

set_option maxHeartbeats 4000000

/-!
# Section 2.1, Section 2.2 & Appendix A: Closure, Matroids, Canonical Demands & Single Exchange

Formalizes Section 2.1, Section 2.2 (`sec:canonical`), and Appendix A (`app:prelim`) of
*Gross Substitutes Welfare in Random Order*:
- Closure of `IsGSValuation` under modular shifts, restrictions, dummy items, contractions, and
  positive scaling;
- **Example 2.4 (`ex:gs`, discretely concave cardinality case)**: `v(S) = h(|S|)` is GS;
- **Lemma 2.5 (`lem:domain`)**: `dom v` of a GS valuation is the independent-set family of a matroid;
- **Lemma 2.6 (`lem:matroid`)**: Weighted matroid valuations `weightedMatroidVal M w` are GS;
- **Section 2.2 (`sec:canonical`)**: Uniqueness, feasibility, and cardinality-first tie-breaking of
  canonical demands `D_v(T)`;
- **Lemma 2.7 (`lem:exchange`)**: Single exchange (`eq:single`), persistence (`eq:persistence`),
  and single displacement (`eq:displacement`);
- **Example 2.8 (`ex:assignment`)**: 4-item GS assignment valuation with no fixed priority order;
- **Lemma 2.9 (`lem:contract`)**: Contraction `v / x` commutes with canonical demand.
-/

namespace GrossSubstitutesWelfare

open Classical MeasureTheory

noncomputable section

theorem thm_gs_prelim_matroid_and_exchange :
    -- (1) Closure operations
    (∀ n (v : ItemValuation n) (a : Fin n → ℝ),
      IsGSValuation v → IsGSValuation (addModular v a)) ∧
    (∀ n (v : ItemValuation n) (N' : Finset (Fin n)),
      IsGSValuation v → IsGSValuation (restrictVal v N')) ∧
    (∀ n (v : ItemValuation n) (d : Fin n),
      IsGSValuation v → IsGSValuation (dummyItemVal v d)) ∧
    (∀ n (v : ItemValuation n) (x : Fin n),
      IsGSValuation v → v {x} ≠ ⊥ → IsGSValuation (contractVal v x)) ∧
    (∀ n (c : ℝ) (v : ItemValuation n),
      0 < c → IsGSValuation v → IsGSValuation (scaleVal c v)) ∧
    -- (2) Example 2.4: discretely concave cardinality valuation
    (∀ n (h : ℕ → ℝ), h 0 = 0 →
      (∀ k : ℕ, h (k + 2) - h (k + 1) ≤ h (k + 1) - h k) →
      IsGSValuation (fun S : Finset (Fin n) => ((h S.card : ℝ) : WithBot ℝ))) ∧
    -- (3) Lemma 2.5: Matroid domain
    (∀ n (v : ItemValuation n), IsGSValuation v →
      ∃ M : Matroid (Fin n), M.E = Set.univ ∧
        ∀ S : Finset (Fin n), M.Indep (S : Set (Fin n)) ↔ v S ≠ ⊥) ∧
    -- (4) Lemma 2.6: Weighted matroids
    (∀ n (M : Matroid (Fin n)) (w : Fin n → ℝ),
      IsGSValuation (weightedMatroidVal M w)) ∧
    -- (5) Canonical demand uniqueness and feasibility
    (∀ n (v : ItemValuation n) (T : Finset (Fin n)),
      v ∅ = ((0 : ℝ) : WithBot ℝ) →
        canonicalDemand v T ⊆ T ∧
        v (canonicalDemand v T) ≠ ⊥ ∧
        (∀ Y ⊆ T, demandKeyLe v Y (canonicalDemand v T)) ∧
        (∀ X ⊆ T, (∀ Y ⊆ T, demandKeyLe v Y X) → X = canonicalDemand v T)) ∧
    -- (6) Lemma 2.7: Single exchange, persistence & single displacement
    (∀ n (v : ItemValuation n) (T : Finset (Fin n)) (x : Fin n),
      IsGSValuation v → x ∉ T →
        let X := canonicalDemand v T
        canonicalDemand v (insert x T) = X ∨
        canonicalDemand v (insert x T) = insert x X ∨
        ∃ f ∈ X, canonicalDemand v (insert x T) = insert x (X.erase f)) ∧
    (∀ n (v : ItemValuation n), IsGSValuation v →
      IsChoiceRule (canonicalDemand v) ∧
      HasPersistence (canonicalDemand v) ∧
      HasSingleDisplacement (canonicalDemand v)) ∧
    -- (7) Example 2.8: No fixed priority order
    (∃ v : ItemValuation 4,
      IsGSValuation v ∧
      canonicalDemand v {(0 : Fin 4), 1} = {0, 1} ∧
      canonicalDemand v {(0 : Fin 4), 1, 3} = {0, 3} ∧
      canonicalDemand v {(2 : Fin 4), 3} = {2, 3} ∧
      canonicalDemand v {(2 : Fin 4), 3, 1} = {2, 1} ∧
      ¬ ∃ (M : Matroid (Fin 4)) (w : Fin 4 → ℝ),
        Function.Injective w ∧
        canonicalDemand (weightedMatroidVal M w) {(0 : Fin 4), 1} = {0, 1} ∧
        canonicalDemand (weightedMatroidVal M w) {(0 : Fin 4), 1, 3} = {0, 3} ∧
        canonicalDemand (weightedMatroidVal M w) {(2 : Fin 4), 3} = {2, 3} ∧
        canonicalDemand (weightedMatroidVal M w) {(2 : Fin 4), 3, 1} = {2, 1}) ∧
    -- (8) Lemma 2.9: Contraction commutes with canonical demand
    (∀ n (v : ItemValuation n) (S : Finset (Fin n)) (x : Fin n),
      IsGSValuation v → x ∉ S → x ∈ canonicalDemand v (insert x S) →
        v {x} ≠ ⊥ ∧
        IsGSValuation (contractVal v x) ∧
        ∀ T ⊆ S, canonicalDemand (contractVal v x) T =
          (canonicalDemand v (insert x T)).erase x) :=
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

  
  have h_part1 : ∀ n (v : ItemValuation n) (a : Fin n → ℝ),
      IsGSValuation v → IsGSValuation (addModular v a) := by
    intro n v a hv
    refine ⟨?_, ?_⟩
    · simp [addModular, hv.1]
    · intro X Y hX hY x hx
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

  
  have h_part2 : ∀ n (v : ItemValuation n) (N' : Finset (Fin n)),
      IsGSValuation v → IsGSValuation (restrictVal v N') := by
    intro n v N' hv
    refine ⟨by simp [restrictVal, hv.1], ?_⟩
    intro X Y hX hY x hx
    by_cases hXN : X ⊆ N'
    · by_cases hYN : Y ⊆ N'
      · simp only [restrictVal, hXN, hYN, ↓reduceIte] at hX hY
        cases hvX : v X with
        | bot => exact absurd hvX hX
        | coe rX =>
          cases hvY : v Y with
          | bot => exact absurd hvY hY
          | coe rY =>
            have hxX : x ∈ X := (Finset.mem_sdiff.mp hx).1
            rcases h_gs_cases hv hvX hvY hx with ⟨r1, r2, h1, h2, hle⟩ | ⟨y, hy, r1, r2, h1, h2, hle⟩
            · have hsub1 : X.erase x ⊆ N' := (Finset.erase_subset x X).trans hXN
              have hsub2 : insert x Y ⊆ N' := Finset.insert_subset (hXN hxX) hYN
              refine h_build_transfer (restrictVal v N') X Y x ?_ ?_ ?_ ?_ hle <;>
                simp [restrictVal, hXN, hYN, hsub1, hsub2, hvX, hvY, h1, h2]
            · have hyY : y ∈ Y := (Finset.mem_sdiff.mp hy).1
              have hsub1 : insert y (X.erase x) ⊆ N' :=
                Finset.insert_subset (hYN hyY) ((Finset.erase_subset x X).trans hXN)
              have hsub2 : (insert x Y).erase y ⊆ N' :=
                (Finset.erase_subset y _).trans (Finset.insert_subset (hXN hxX) hYN)
              refine h_build_swap (restrictVal v N') X Y x y hy ?_ ?_ ?_ ?_ hle <;>
                simp [restrictVal, hXN, hYN, hsub1, hsub2, hvX, hvY, h1, h2]
      · simp [restrictVal, hYN] at hY
    · simp [restrictVal, hXN] at hX

  
  have h_part3 : ∀ n (v : ItemValuation n) (d : Fin n),
      IsGSValuation v → IsGSValuation (dummyItemVal v d) := by
    intro n v d hv
    refine ⟨by simp [dummyItemVal, hv.1], ?_⟩
    intro X Y hX hY x hx
    cases hvX : v (X.erase d) with
    | bot => exact absurd hvX hX
    | coe rX =>
      cases hvY : v (Y.erase d) with
      | bot => exact absurd hvY hY
      | coe rY =>
        have hxX : x ∈ X := (Finset.mem_sdiff.mp hx).1
        have hxY : x ∉ Y := (Finset.mem_sdiff.mp hx).2
        by_cases hxd : x = d
        · subst hxd
          have he2 : (insert x Y).erase x = Y.erase x := by
            rw [Finset.erase_insert hxY, Finset.erase_eq_of_notMem hxY]
          refine h_build_transfer (dummyItemVal v x) X Y x hvX hvY ?_ ?_ le_rfl
          · simp [dummyItemVal, hvX]
          · simp [dummyItemVal, he2, hvY]
        · have hx' : x ∈ (X.erase d) \ (Y.erase d) := by
            simp [Finset.mem_sdiff, hxX, hxY, hxd]
          rcases h_gs_cases hv hvX hvY hx' with ⟨r1, r2, h1, h2, hle⟩ | ⟨y, hy, r1, r2, h1, h2, hle⟩
          · have he1 : (X.erase x).erase d = (X.erase d).erase x := Finset.erase_right_comm
            have he2 : (insert x Y).erase d = insert x (Y.erase d) := Finset.erase_insert_of_ne hxd
            refine h_build_transfer (dummyItemVal v d) X Y x hvX hvY ?_ ?_ hle
            · simp [dummyItemVal, he1, h1]
            · simp [dummyItemVal, he2, h2]
          · have hyd : y ≠ d := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hy).1).1
            have hyY : y ∈ Y := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hy).1).2
            have hyX : y ∉ X := fun hm => (Finset.mem_sdiff.mp hy).2 (Finset.mem_erase.mpr ⟨hyd, hm⟩)
            have hy_orig : y ∈ Y \ X := Finset.mem_sdiff.mpr ⟨hyY, hyX⟩
            have he1 : (insert y (X.erase x)).erase d = insert y ((X.erase d).erase x) := by
              rw [Finset.erase_insert_of_ne hyd, Finset.erase_right_comm]
            have he2 : ((insert x Y).erase y).erase d = (insert x (Y.erase d)).erase y := by
              rw [Finset.erase_right_comm, Finset.erase_insert_of_ne hxd]
            refine h_build_swap (dummyItemVal v d) X Y x y hy_orig hvX hvY ?_ ?_ hle
            · simp [dummyItemVal, he1, h1]
            · simp [dummyItemVal, he2, h2]

  
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

  
  have h_part5 : ∀ n (c : ℝ) (v : ItemValuation n),
      0 < c → IsGSValuation v → IsGSValuation (scaleVal c v) := by
    intro n c v hc hv
    refine ⟨by simp [scaleVal, hv.1], ?_⟩
    intro X Y hX hY x hx
    cases hvX : v X with
    | bot => simp [scaleVal, hvX] at hX
    | coe rX =>
      cases hvY : v Y with
      | bot => simp [scaleVal, hvY] at hY
      | coe rY =>
        rcases h_gs_cases hv hvX hvY hx with ⟨r1, r2, h1, h2, hle⟩ | ⟨y, hy, r1, r2, h1, h2, hle⟩
        · refine h_build_transfer (scaleVal c v) X Y x
            (rX := c * rX) (rY := c * rY) (r1 := c * r1) (r2 := c * r2)
            (by simp only [scaleVal, hvX]) (by simp only [scaleVal, hvY])
            (by simp only [scaleVal, h1]) (by simp only [scaleVal, h2]) ?_
          nlinarith
        · refine h_build_swap (scaleVal c v) X Y x y hy
            (rX := c * rX) (rY := c * rY) (r1 := c * r1) (r2 := c * r2)
            (by simp only [scaleVal, hvX]) (by simp only [scaleVal, hvY])
            (by simp only [scaleVal, h1]) (by simp only [scaleVal, h2]) ?_
          nlinarith

  
  have h_part6 : ∀ n (h : ℕ → ℝ), h 0 = 0 →
      (∀ k : ℕ, h (k + 2) - h (k + 1) ≤ h (k + 1) - h k) →
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
        · have hstep := hconc b
          have hprev := ih hab'
          linarith
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
        have hss : Y ⊂ X := Finset.ssubset_iff_subset_ne.mpr
          ⟨hYX, fun heq => hxY (heq ▸ hxX)⟩
        exact hlt (Finset.card_lt_card hss)
      obtain ⟨y, hy⟩ := hne
      have hyY : y ∈ Y := (Finset.mem_sdiff.mp hy).1
      have hyX : y ∉ X := (Finset.mem_sdiff.mp hy).2
      have hy_er : y ∉ X.erase x := fun hm => hyX (Finset.erase_subset x X hm)
      have hy_ins : y ∈ insert x Y := Finset.mem_insert_of_mem hyY
      have hc1 : (insert y (X.erase x)).card = X.card := by
        rw [Finset.card_insert_of_notMem hy_er, hcardX]
      have hc2 : ((insert x Y).erase y).card = Y.card := by
        have := Finset.card_erase_add_one hy_ins
        omega
      refine h_build_swap v X Y x y hy rfl rfl ?_ ?_ le_rfl
      · simp [v, hc1]
      · simp [v, hc2]

  
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

  
  have h_part7 : ∀ n (v : ItemValuation n), IsGSValuation v →
      ∃ M : Matroid (Fin n), M.E = Set.univ ∧
        ∀ S : Finset (Fin n), M.Indep (S : Set (Fin n)) ↔ v S ≠ ⊥ := by
    intro n v hv
    let Indep : Set (Fin n) → Prop := fun I => v I.toFinset ≠ ⊥
    have h_emp : Indep ∅ := by simp [Indep, hv.1]
    have h_sub : ∀ ⦃I J : Set (Fin n)⦄, Indep J → I ⊆ J → Indep I := by
      intro I J hJ hIJ
      exact h_hered hv hJ (Set.toFinset_subset_toFinset.mpr hIJ)
    have h_aug_fin : ∀ (I₀ : Finset (Fin n)), v I₀ ≠ ⊥ →
        ∀ (k : ℕ) (J₁ : Finset (Fin n)),
          (I₀ \ J₁).card = k → v J₁ ≠ ⊥ → J₁.card = I₀.card + 1 →
            ∃ y ∈ J₁ \ I₀, v (insert y I₀) ≠ ⊥ := by
      intro I₀ hI₀ k
      induction k with
      | zero =>
        intro J₁ hk hJ₁ hcard
        have hne : (J₁ \ I₀).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hemp
          have hle := Finset.card_le_card (Finset.sdiff_eq_empty_iff_subset.mp hemp)
          omega
        obtain ⟨x, hx⟩ := hne
        cases hvJ : v J₁ with
        | bot => exact absurd hvJ hJ₁
        | coe rJ =>
          cases hvI : v I₀ with
          | bot => exact absurd hvI hI₀
          | coe rI =>
            rcases h_gs_cases hv hvJ hvI hx with ⟨_, r2, _, h2, _⟩ | ⟨z, hz, _⟩
            · exact ⟨x, hx, by simp [h2]⟩
            · have hemp : I₀ \ J₁ = ∅ := Finset.card_eq_zero.mp hk
              rw [hemp] at hz; simp at hz
      | succ k ih =>
        intro J₁ hk hJ₁ hcard
        have hne : (J₁ \ I₀).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hemp
          have hle := Finset.card_le_card (Finset.sdiff_eq_empty_iff_subset.mp hemp)
          omega
        obtain ⟨x, hx⟩ := hne
        cases hvJ : v J₁ with
        | bot => exact absurd hvJ hJ₁
        | coe rJ =>
          cases hvI : v I₀ with
          | bot => exact absurd hvI hI₀
          | coe rI =>
            rcases h_gs_cases hv hvJ hvI hx with ⟨_, r2, _, h2, _⟩ | ⟨z, hz, r1, _, h1, _, _⟩
            · exact ⟨x, hx, by simp [h2]⟩
            · have hxJ : x ∈ J₁ := (Finset.mem_sdiff.mp hx).1
              have hxI : x ∉ I₀ := (Finset.mem_sdiff.mp hx).2
              have hzI : z ∈ I₀ := (Finset.mem_sdiff.mp hz).1
              have hzJ : z ∉ J₁ := (Finset.mem_sdiff.mp hz).2
              let J₁' : Finset (Fin n) := insert z (J₁.erase x)
              have hz_er : z ∉ J₁.erase x := fun hm => hzJ (Finset.erase_subset x J₁ hm)
              have hcard' : J₁'.card = I₀.card + 1 := by
                change (insert z (J₁.erase x)).card = I₀.card + 1
                rw [Finset.card_insert_of_notMem hz_er]
                have := Finset.card_erase_add_one hxJ
                omega
              have hsdiff' : I₀ \ J₁' = (I₀ \ J₁).erase z := by
                ext w
                simp only [J₁', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
                constructor
                · rintro ⟨hwI, hnot⟩
                  refine ⟨fun hwz => hnot (Or.inl hwz), hwI, fun hwJ => hnot (Or.inr ⟨?_, hwJ⟩)⟩
                  exact fun hwx => hxI (hwx ▸ hwI)
                · rintro ⟨hwz, hwI, hwJ⟩
                  exact ⟨hwI, fun h => h.elim hwz (fun h2 => hwJ h2.2)⟩
              have hk' : (I₀ \ J₁').card = k := by
                rw [hsdiff']
                have := Finset.card_erase_add_one hz
                omega
              obtain ⟨y, hy', hy_ins⟩ := ih J₁' hk' (by simp [J₁', h1]) hcard'
              have hyI : y ∉ I₀ := (Finset.mem_sdiff.mp hy').2
              have hyJ : y ∈ J₁ := by
                rcases Finset.mem_insert.mp (Finset.mem_sdiff.mp hy').1 with rfl | hm
                · exact absurd hzI hyI
                · exact Finset.erase_subset x J₁ hm
              exact ⟨y, Finset.mem_sdiff.mpr ⟨hyJ, hyI⟩, hy_ins⟩
    have h_aug : ∀ ⦃I J : Set (Fin n)⦄,
        Indep I → Indep J → I.encard < J.encard → ∃ e ∈ J, e ∉ I ∧ Indep (insert e I) := by
      intro I J hI hJ hlt
      let I₀ := I.toFinset
      let J₀ := J.toFinset
      have hI_eq : (I₀ : Set (Fin n)) = I := Set.coe_toFinset I
      have hJ_eq : (J₀ : Set (Fin n)) = J := Set.coe_toFinset J
      rw [← hI_eq, ← hJ_eq, Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard,
        Nat.cast_lt] at hlt
      obtain ⟨J₁, hJ₁_sub, hJ₁_card⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hlt)
      obtain ⟨e, he, he_ind⟩ := h_aug_fin I₀ hI (I₀ \ J₁).card J₁ rfl (h_hered hv hJ hJ₁_sub) hJ₁_card
      have heJ : e ∈ J := by
        rw [← hJ_eq]; exact Finset.mem_coe.mpr (hJ₁_sub (Finset.mem_sdiff.mp he).1)
      have heI : e ∉ I := by
        rw [← hI_eq]; simp [(Finset.mem_sdiff.mp he).2]
      have hto : (insert e I).toFinset = insert e I₀ := by simp [I₀]
      exact ⟨e, heJ, heI, by simpa [Indep, hto] using he_ind⟩
    have h_bdd : ∃ m : ℕ, ∀ I : Set (Fin n), Indep I → I.encard ≤ m := by
      refine ⟨n, fun I _ => ?_⟩
      rw [← Set.coe_toFinset I, Set.encard_coe_eq_coe_finsetCard]
      exact_mod_cast (Finset.card_le_univ I.toFinset).trans (by simp)
    have h_grd : ∀ I : Set (Fin n), Indep I → I ⊆ Set.univ := fun I _ => Set.subset_univ I
    let IM := IndepMatroid.ofBddAugment Set.univ Indep h_emp h_sub h_aug h_bdd h_grd
    refine ⟨IM.matroid, ?_, ?_⟩
    · rw [IndepMatroid.matroid_E, IndepMatroid.ofBddAugment_E]
    · intro S
      rw [IndepMatroid.matroid_Indep, IndepMatroid.ofBddAugment_indep]
      simp [Indep]

  
  have h_part8 : ∀ n (M : Matroid (Fin n)) (w : Fin n → ℝ),
      IsGSValuation (weightedMatroidVal M w) := by
    intro n M w
    have h_rep_aug : ∀ (d : ℕ) (A B : Finset (Fin n)),
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
    refine ⟨?_, ?_⟩
    · simp [weightedMatroidVal, M.empty_indep]
    · intro X Y hX hY x hx
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
              have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
              have hyC : y ∈ C := (Finset.mem_erase.mp hy).2
              have hy_ins : y ∈ insert x Y := hCsub hyC
              have hC_le : C.card ≤ Y.card + 1 := by
                have := Finset.card_le_card hCsub
                rw [Finset.card_insert_of_notMem hxY] at this
                exact this
              have hCy_le : (C.erase y).card ≤ Y.card := by
                have := Finset.card_erase_add_one hyC
                omega
              obtain ⟨K, hCyK, hKsub, hKind, hKcard⟩ :=
                h_rep_aug (Y.card - (C.erase y).card) (C.erase y) Y rfl
                  (hC_er_ind y hyC) hIY hCy_le
              have hyK : y ∉ K := fun hm => by
                have hCK : C ⊆ K := by
                  rw [← Finset.insert_erase hyC]
                  exact Finset.insert_subset hm hCyK
                exact hCdep (hKind.subset (Finset.coe_subset.mpr hCK))
              have hK_ins : K ⊆ insert x Y := by
                refine hKsub.trans (Finset.union_subset ((Finset.erase_subset y C).trans hCsub) ?_)
                exact Finset.subset_insert x Y
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

  
  have h_part12 : ∃ v : ItemValuation 4,
      IsGSValuation v ∧
      canonicalDemand v {(0 : Fin 4), 1} = {0, 1} ∧
      canonicalDemand v {(0 : Fin 4), 1, 3} = {0, 3} ∧
      canonicalDemand v {(2 : Fin 4), 3} = {2, 3} ∧
      canonicalDemand v {(2 : Fin 4), 3, 1} = {2, 1} ∧
      ¬ ∃ (M : Matroid (Fin 4)) (w : Fin 4 → ℝ),
        Function.Injective w ∧
        canonicalDemand (weightedMatroidVal M w) {(0 : Fin 4), 1} = {0, 1} ∧
        canonicalDemand (weightedMatroidVal M w) {(0 : Fin 4), 1, 3} = {0, 3} ∧
        canonicalDemand (weightedMatroidVal M w) {(2 : Fin 4), 3} = {2, 3} ∧
        canonicalDemand (weightedMatroidVal M w) {(2 : Fin 4), 3, 1} = {2, 1} := by
    let uZ : Finset (Fin 4) → WithBot ℤ := fun S =>
      if 2 < S.card then ⊥
      else if S = {0, 1} ∨ S = {2, 3} then ((-2 : ℤ) : WithBot ℤ)
      else ((0 : ℤ) : WithBot ℤ)
    let aZ : Fin 4 → ℤ := fun i => if i = 0 ∨ i = 2 then 4 else 3
    let vZ : Finset (Fin 4) → WithBot ℤ := fun S =>
      uZ S + ((∑ g ∈ S, aZ g : ℤ) : WithBot ℤ)
    have h_dec :
        uZ ∅ = ((0 : ℤ) : WithBot ℤ) ∧
        (∀ X Y : Finset (Fin 4), uZ X ≠ ⊥ → uZ Y ≠ ⊥ →
          ∀ x ∈ X \ Y,
            uZ X + uZ Y ≤
              max (uZ (X.erase x) + uZ (insert x Y))
                  ((Y \ X).sup (fun y => uZ (insert y (X.erase x)) + uZ ((insert x Y).erase y)))) ∧
        (vZ {0, 1} ≠ ⊥ ∧ ∀ Y : Finset (Fin 4), Y ⊆ {(0 : Fin 4), 1} →
          Y ≠ {0, 1} → vZ Y + ((1 : ℤ) : WithBot ℤ) ≤ vZ {0, 1}) ∧
        (vZ {0, 3} ≠ ⊥ ∧ ∀ Y : Finset (Fin 4), Y ⊆ {(0 : Fin 4), 1, 3} →
          Y ≠ {0, 3} → vZ Y + ((1 : ℤ) : WithBot ℤ) ≤ vZ {0, 3}) ∧
        (vZ {2, 3} ≠ ⊥ ∧ ∀ Y : Finset (Fin 4), Y ⊆ {(2 : Fin 4), 3} →
          Y ≠ {2, 3} → vZ Y + ((1 : ℤ) : WithBot ℤ) ≤ vZ {2, 3}) ∧
        (vZ {2, 1} ≠ ⊥ ∧ ∀ Y : Finset (Fin 4), Y ⊆ {(2 : Fin 4), 3, 1} →
          Y ≠ {2, 1} → vZ Y + ((1 : ℤ) : WithBot ℤ) ≤ vZ {2, 1}) := by
      decide
    let liftZ : (Finset (Fin 4) → WithBot ℤ) → ItemValuation 4 := fun f S =>
      match f S with
      | ⊥ => ⊥
      | (z : ℤ) => ((z : ℝ) : WithBot ℝ)
    have h_lift_le : ∀ (f : Finset (Fin 4) → WithBot ℤ) (A B C D : Finset (Fin 4)) (zA zB : ℤ),
        f A = ((zA : ℤ) : WithBot ℤ) → f B = ((zB : ℤ) : WithBot ℤ) →
        f A + f B ≤ f C + f D →
        liftZ f A + liftZ f B ≤ liftZ f C + liftZ f D := by
      intro f A B C D zA zB hA hB hle
      rw [hA, hB, ← WithBot.coe_add] at hle
      cases hC : f C with
      | bot => rw [hC] at hle; simp at hle
      | coe zC =>
        cases hD : f D with
        | bot => rw [hC, hD] at hle; simp at hle
        | coe zD =>
          rw [hC, hD, ← WithBot.coe_add, WithBot.coe_le_coe] at hle
          have hleR : (zA : ℝ) + (zB : ℝ) ≤ (zC : ℝ) + (zD : ℝ) := by exact_mod_cast hle
          simp only [liftZ, hA, hB, hC, hD, ← WithBot.coe_add, WithBot.coe_le_coe]
          exact hleR
    have hu_gs : IsGSValuation (liftZ uZ) := by
      refine ⟨by simp [liftZ, h_dec.1], ?_⟩
      intro X Y hX hY x hx
      cases huX : uZ X with
      | bot => simp [liftZ, huX] at hX
      | coe zX =>
        cases huY : uZ Y with
        | bot => simp [liftZ, huY] at hY
        | coe zY =>
          have hex := h_dec.2.1 X Y (by simp [huX]) (by simp [huY]) x hx
          rw [le_max_iff] at hex
          rcases hex with hT | hS
          · exact le_max_of_le_left (h_lift_le uZ X Y (X.erase x) (insert x Y) zX zY huX huY hT)
          · have hne : (Y \ X).Nonempty := by
              rw [Finset.nonempty_iff_ne_empty]
              intro hemp; rw [hemp, Finset.sup_empty, huX, huY, ← WithBot.coe_add] at hS
              exact absurd hS (by simp)
            obtain ⟨y, hy, hsup⟩ := Finset.exists_mem_eq_sup (Y \ X) hne
              (fun y => uZ (insert y (X.erase x)) + uZ ((insert x Y).erase y))
            rw [hsup] at hS
            apply le_max_of_le_right
            refine le_trans (h_lift_le uZ X Y (insert y (X.erase x)) ((insert x Y).erase y)
              zX zY huX huY hS) ?_
            exact Finset.le_sup
              (f := fun z => liftZ uZ (insert z (X.erase x)) + liftZ uZ ((insert x Y).erase z)) hy
    let aR : Fin 4 → ℝ := fun i => if i = 0 ∨ i = 2 then 4 else 3
    let v : ItemValuation 4 := addModular (liftZ uZ) aR
    have hv_gs : IsGSValuation v := h_part1 4 (liftZ uZ) aR hu_gs
    have ha_eq : ∀ g : Fin 4, aR g = (aZ g : ℝ) := by
      intro g; fin_cases g <;> simp [aR, aZ]
    have hv_eq : ∀ S : Finset (Fin 4), v S = liftZ vZ S := by
      intro S
      have hsum : ∑ g ∈ S, aR g = ((∑ g ∈ S, aZ g : ℤ) : ℝ) := by
        simp [ha_eq]
      cases huS : uZ S with
      | bot => simp [v, addModular, liftZ, vZ, huS]
      | coe z =>
        have hvZS : vZ S = ((z + ∑ g ∈ S, aZ g : ℤ) : WithBot ℤ) := by
          dsimp only [vZ]
          rw [huS, ← WithBot.coe_add]
        simp only [v, addModular, liftZ, huS, hvZS, hsum, ← WithBot.coe_add]
        push_cast
        rfl
    have h_menu_eq : ∀ (T Xstar : Finset (Fin 4)),
        Xstar ⊆ T → vZ Xstar ≠ ⊥ →
        (∀ Y : Finset (Fin 4), Y ⊆ T → Y ≠ Xstar → vZ Y + ((1 : ℤ) : WithBot ℤ) ≤ vZ Xstar) →
        canonicalDemand v T = Xstar := by
      intro T Xstar hsub hne_bot hstrict
      refine ((h_part9 4 v T hv_gs.1).2.2.2 Xstar hsub (fun Y hYT => ?_)).symm
      by_cases hYX : Y = Xstar
      · subst hYX; exact Or.inr ⟨rfl, le_rfl⟩
      · refine Or.inl ?_
        rw [hv_eq Y, hv_eq Xstar]
        have hltZ := hstrict Y hYT hYX
        cases hvX : vZ Xstar with
        | bot => exact absurd hvX hne_bot
        | coe zX =>
          cases hvY : vZ Y with
          | bot => simp [liftZ, hvY, hvX]
          | coe zY =>
            rw [hvY, hvX, ← WithBot.coe_add, WithBot.coe_le_coe] at hltZ
            have hltR : (zY : ℝ) < (zX : ℝ) := by exact_mod_cast (by omega : zY < zX)
            simp only [liftZ, hvY, hvX, WithBot.coe_lt_coe]
            exact hltR
    refine ⟨v, hv_gs,
      h_menu_eq {0, 1} {0, 1} (by decide) h_dec.2.2.1.1 h_dec.2.2.1.2,
      h_menu_eq {0, 1, 3} {0, 3} (by decide) h_dec.2.2.2.1.1 h_dec.2.2.2.1.2,
      h_menu_eq {2, 3} {2, 3} (by decide) h_dec.2.2.2.2.1.1 h_dec.2.2.2.2.1.2,
      h_menu_eq {2, 3, 1} {2, 1} (by decide) h_dec.2.2.2.2.2.1 h_dec.2.2.2.2.2.2, ?_⟩
    rintro ⟨M, w, hw_inj, hd1, hd2, hd3, hd4⟩
    let vM := weightedMatroidVal M w
    have hvM0 : vM ∅ = ((0 : ℝ) : WithBot ℝ) := by simp [vM, weightedMatroidVal, M.empty_indep]
    have h_wsum_le : ∀ {T A B : Finset (Fin 4)},
        canonicalDemand vM A = A → canonicalDemand vM T = B → A ⊆ T →
        ∑ g ∈ A, w g ≤ ∑ g ∈ B, w g := by
      intro T A B hA hB hAT
      have hAne : vM A ≠ ⊥ := by
        have := (h_part9 4 vM A hvM0).2.1; rwa [hA] at this
      have hBne : vM B ≠ ⊥ := by
        have := (h_part9 4 vM T hvM0).2.1; rwa [hB] at this
      have hkey : demandKeyLe vM A B := by
        have := (h_part9 4 vM T hvM0).2.2.1 A hAT; rwa [hB] at this
      by_cases hIA : M.Indep (A : Set (Fin 4))
      · by_cases hIB : M.Indep (B : Set (Fin 4))
        · simp only [demandKeyLe, vM, weightedMatroidVal, hIA, hIB, ↓reduceIte] at hkey
          rcases hkey with hlt | ⟨heq, _⟩
          · exact le_of_lt (WithBot.coe_lt_coe.mp hlt)
          · exact le_of_eq (WithBot.coe_inj.mp heq)
        · simp [vM, weightedMatroidVal, hIB] at hBne
      · simp [vM, weightedMatroidVal, hIA] at hAne
    have hle13 : ∑ g ∈ ({(0 : Fin 4), 1} : Finset (Fin 4)), w g ≤
        ∑ g ∈ ({(0 : Fin 4), 3} : Finset (Fin 4)), w g :=
      h_wsum_le hd1 hd2 (by decide)
    have hle31 : ∑ g ∈ ({(2 : Fin 4), 3} : Finset (Fin 4)), w g ≤
        ∑ g ∈ ({(2 : Fin 4), 1} : Finset (Fin 4)), w g :=
      h_wsum_le hd3 hd4 (by decide)
    simp only [Finset.sum_insert (by decide : (0 : Fin 4) ∉ ({1} : Finset (Fin 4))),
      Finset.sum_insert (by decide : (0 : Fin 4) ∉ ({3} : Finset (Fin 4))),
      Finset.sum_insert (by decide : (2 : Fin 4) ∉ ({3} : Finset (Fin 4))),
      Finset.sum_insert (by decide : (2 : Fin 4) ∉ ({1} : Finset (Fin 4))),
      Finset.sum_singleton] at hle13 hle31
    have hw13_eq : w 1 = w 3 := by linarith
    have h13_ne : (1 : Fin 4) ≠ 3 := by decide
    exact h13_ne (hw_inj hw13_eq)

  
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

  exact ⟨h_part1, h_part2, h_part3, h_part4, h_part5, h_part6, h_part7, h_part8,
    h_part9, h_part10, h_part11, h_part12, h_part13⟩

end


noncomputable section

/-- Adding a modular function `a(S) = ∑_{g ∈ S} a_g` preserves `IsGSValuation` (Section 2.1). -/
theorem gs_closure_add_modular {n : ℕ} (v : ItemValuation n) (a : Fin n → ℝ)
    (hv : IsGSValuation v) : IsGSValuation (addModular v a) :=
  thm_gs_prelim_matroid_and_exchange.1 n v a hv

/-- Restricting `v` to `2^{N'}` preserves `IsGSValuation` (Section 2.1). -/
theorem gs_closure_restrict {n : ℕ} (v : ItemValuation n) (N' : Finset (Fin n))
    (hv : IsGSValuation v) : IsGSValuation (restrictVal v N') :=
  thm_gs_prelim_matroid_and_exchange.2.1 n v N' hv

/-- Adding a dummy item `d` (`v'(S) = v(S - d)`) preserves `IsGSValuation` (Section 2.1). -/
theorem gs_closure_dummy_item {n : ℕ} (v : ItemValuation n) (d : Fin n)
    (hv : IsGSValuation v) : IsGSValuation (dummyItemVal v d) :=
  thm_gs_prelim_matroid_and_exchange.2.2.1 n v d hv

/-- Contracting `x` when `v({x}) > -∞` preserves `IsGSValuation` (`eq:contraction`, Section 2.1). -/
theorem gs_closure_contract {n : ℕ} (v : ItemValuation n) (x : Fin n)
    (hv : IsGSValuation v) (hx : v {x} ≠ ⊥) : IsGSValuation (contractVal v x) :=
  thm_gs_prelim_matroid_and_exchange.2.2.2.1 n v x hv hx

/-- Positive scaling `c · v` (`c > 0`) preserves `IsGSValuation` (Section 2.1). -/
theorem gs_closure_scale {n : ℕ} (c : ℝ) (v : ItemValuation n)
    (hc : 0 < c) (hv : IsGSValuation v) : IsGSValuation (scaleVal c v) :=
  thm_gs_prelim_matroid_and_exchange.2.2.2.2.1 n c v hc hv

/-- **Example 2.4 (`ex:gs`, discretely concave cardinality valuation)**:
If `h : ℕ → ℝ` has `h(0) = 0` and nonincreasing increments `h(k + 2) - h(k + 1) ≤ h(k + 1) - h(k)`,
then `v(S) = h(|S|)` satisfies `IsGSValuation`. -/
theorem ex_2_4_concave_cardinality {n : ℕ} (h : ℕ → ℝ) (h0 : h 0 = 0)
    (hconc : ∀ k : ℕ, h (k + 2) - h (k + 1) ≤ h (k + 1) - h k) :
    IsGSValuation (fun S : Finset (Fin n) => ((h S.card : ℝ) : WithBot ℝ)) :=
  thm_gs_prelim_matroid_and_exchange.2.2.2.2.2.1 n h h0 hconc

/-- **Lemma 2.5 (`lem:domain`, Matroid domain)**:
If `v` is a GS valuation on `Fin n`, then `dom v = {S | v(S) > -∞}` is the independent-set family
of a matroid on `Fin n` (proved from the exchange axiom in Appendix A). -/
theorem lem_2_5_domain {n : ℕ} (v : ItemValuation n) (hv : IsGSValuation v) :
    ∃ M : Matroid (Fin n), M.E = Set.univ ∧
      ∀ S : Finset (Fin n), M.Indep (S : Set (Fin n)) ↔ v S ≠ ⊥ :=
  thm_gs_prelim_matroid_and_exchange.2.2.2.2.2.2.1 n v hv

/-- **Lemma 2.6 (`lem:matroid`, Weighted matroids)**:
For any matroid `M` on `Fin n` and weight vector `w ∈ ℝ^N`, `weightedMatroidVal M w` satisfies
`IsGSValuation` (proved from the exchange axiom in Appendix A). -/
theorem lem_2_6_matroid {n : ℕ} (M : Matroid (Fin n)) (w : Fin n → ℝ) :
    IsGSValuation (weightedMatroidVal M w) :=
  thm_gs_prelim_matroid_and_exchange.2.2.2.2.2.2.2.1 n M w

/-- **Section 2.2 (`sec:canonical`, Canonical demand existence, feasibility, and uniqueness)**:
Whenever `v(∅) = 0`, `canonicalDemand v T` lies in `2^T ∩ dom v` and is the unique `(v, ψ)`-
lexicographic maximizer over subsets of `T`. -/
theorem canonical_demand_spec {n : ℕ} (v : ItemValuation n) (T : Finset (Fin n))
    (hv0 : v ∅ = ((0 : ℝ) : WithBot ℝ)) :
    canonicalDemand v T ⊆ T ∧
    v (canonicalDemand v T) ≠ ⊥ ∧
    (∀ Y ⊆ T, demandKeyLe v Y (canonicalDemand v T)) ∧
    (∀ X ⊆ T, (∀ Y ⊆ T, demandKeyLe v Y X) → X = canonicalDemand v T) :=
  thm_gs_prelim_matroid_and_exchange.2.2.2.2.2.2.2.2.1 n v T hv0

/-- Binary dyadic tie-breaker bound `∑_{g ∈ X} 2^{-(g+1)} < 1` and cardinality-first ordering of
`psiWeight` (`sec:canonical`): `ψ(X) < ψ(Y)` iff `|X| < |Y|` or (`|X| = |Y|` and
`∑_{g ∈ X} 2^{-(g+1)} < ∑_{g ∈ Y} 2^{-(g+1)}`). -/
theorem psiWeight_card_lex_iff {n : ℕ} (X Y : Finset (Fin n)) :
    psiWeight X < psiWeight Y ↔
      X.card < Y.card ∨
        (X.card = Y.card ∧
          (∑ g ∈ X, (1 / 2 : ℝ) ^ (g.1 + 1)) < (∑ g ∈ Y, (1 / 2 : ℝ) ^ (g.1 + 1))) := by
  have h_dyadic_lt_one : ∀ S : Finset (Fin n),
      0 ≤ (∑ g ∈ S, (1 / 2 : ℝ) ^ (g.1 + 1)) ∧ (∑ g ∈ S, (1 / 2 : ℝ) ^ (g.1 + 1)) < 1 := by
    intro S
    refine ⟨Finset.sum_nonneg (fun g _ => by positivity), ?_⟩
    have h_le_univ : (∑ g ∈ S, (1 / 2 : ℝ) ^ (g.1 + 1)) ≤
        ∑ g : Fin n, (1 / 2 : ℝ) ^ (g.1 + 1) :=
      Finset.sum_le_univ_sum_of_nonneg (fun g => by positivity)
    have h_range : (∑ g : Fin n, (1 / 2 : ℝ) ^ (g.1 + 1)) =
        ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ (k + 1) := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => (1 / 2 : ℝ) ^ (k + 1)) n]
    have h_geom : ∀ m : ℕ, (∑ k ∈ Finset.range m, (1 / 2 : ℝ) ^ (k + 1)) =
        1 - (1 / 2 : ℝ) ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        ring
    have h_pos : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
    linarith [h_geom n]
  have h_decomp : ∀ S : Finset (Fin n),
      psiWeight S = (S.card : ℝ) + ∑ g ∈ S, (1 / 2 : ℝ) ^ (g.1 + 1) := by
    intro S
    simp [psiWeight, Finset.sum_add_distrib]
  rw [h_decomp X, h_decomp Y]
  obtain ⟨hX0, hX1⟩ := h_dyadic_lt_one X
  obtain ⟨hY0, hY1⟩ := h_dyadic_lt_one Y
  constructor
  · intro hlt
    rcases lt_trichotomy X.card Y.card with hlt_c | heq_c | hgt_c
    · exact Or.inl hlt_c
    · right
      refine ⟨heq_c, ?_⟩
      have hc : (X.card : ℝ) = (Y.card : ℝ) := by exact_mod_cast heq_c
      linarith
    · exfalso
      have hc : (Y.card : ℝ) + 1 ≤ (X.card : ℝ) := by exact_mod_cast hgt_c
      linarith
  · rintro (hlt_c | ⟨heq_c, hlt_d⟩)
    · have hc : (X.card : ℝ) + 1 ≤ (Y.card : ℝ) := by exact_mod_cast hlt_c
      linarith
    · have hc : (X.card : ℝ) = (Y.card : ℝ) := by exact_mod_cast heq_c
      linarith

/-- **Lemma 2.7 (`lem:exchange`, Single exchange, `eq:single`)**:
For any GS valuation `v`, `T ⊆ N`, and `x ∉ T`, with `X = D_v(T)`,
`D_v(T + x) ∈ {X, X + x} ∪ {X + x - f : f ∈ X}`. -/
theorem lem_2_7_exchange {n : ℕ} (v : ItemValuation n) (T : Finset (Fin n)) (x : Fin n)
    (hv : IsGSValuation v) (hx : x ∉ T) :
    let X := canonicalDemand v T
    canonicalDemand v (insert x T) = X ∨
    canonicalDemand v (insert x T) = insert x X ∨
    ∃ f ∈ X, canonicalDemand v (insert x T) = insert x (X.erase f) :=
  thm_gs_prelim_matroid_and_exchange.2.2.2.2.2.2.2.2.2.1 n v T x hv hx

/-- **Lemma 2.7 (`eq:persistence`, Persistence of canonical demand)**:
For any GS valuation `v`, `D_v` is a choice rule (`D_v(T) ⊆ T`) satisfying persistence
(`T ⊆ U ⟹ D_v(U) ∩ T ⊆ D_v(T)`). -/
theorem lem_2_7_persistence {n : ℕ} (v : ItemValuation n) (hv : IsGSValuation v) :
    IsChoiceRule (canonicalDemand v) ∧ HasPersistence (canonicalDemand v) := by
  have h := thm_gs_prelim_matroid_and_exchange.2.2.2.2.2.2.2.2.2.2.1 n v hv
  exact ⟨h.1, h.2.1⟩

/-- **Lemma 2.7 (`eq:displacement`, Single displacement of canonical demand)**:
For any GS valuation `v` and `x ∉ T`, `|D_v(T) \ D_v(T + x)| ≤ 1`. -/
theorem lem_2_7_single_displacement {n : ℕ} (v : ItemValuation n) (hv : IsGSValuation v) :
    HasSingleDisplacement (canonicalDemand v) :=
  (thm_gs_prelim_matroid_and_exchange.2.2.2.2.2.2.2.2.2.2.1 n v hv).2.2

/-- **Example 2.8 (`ex:assignment`, No fixed priority)**:
A 4-item GS assignment valuation where item `3` (`b₂`) displaces `1` (`a₂`) from `{0, 1}` while
item `1` (`a₂`) displaces `3` (`b₂`) from `{2, 3}`, impossible in any weighted matroid with
distinct weights. -/
theorem ex_2_8_assignment :
    ∃ v : ItemValuation 4,
      IsGSValuation v ∧
      canonicalDemand v {(0 : Fin 4), 1} = {0, 1} ∧
      canonicalDemand v {(0 : Fin 4), 1, 3} = {0, 3} ∧
      canonicalDemand v {(2 : Fin 4), 3} = {2, 3} ∧
      canonicalDemand v {(2 : Fin 4), 3, 1} = {2, 1} ∧
      ¬ ∃ (M : Matroid (Fin 4)) (w : Fin 4 → ℝ),
        Function.Injective w ∧
        canonicalDemand (weightedMatroidVal M w) {(0 : Fin 4), 1} = {0, 1} ∧
        canonicalDemand (weightedMatroidVal M w) {(0 : Fin 4), 1, 3} = {0, 3} ∧
        canonicalDemand (weightedMatroidVal M w) {(2 : Fin 4), 3} = {2, 3} ∧
        canonicalDemand (weightedMatroidVal M w) {(2 : Fin 4), 3, 1} = {2, 1} :=
  thm_gs_prelim_matroid_and_exchange.2.2.2.2.2.2.2.2.2.2.2.1

/-- **Lemma 2.9 (`lem:contract`, Contraction and canonical demand)**:
If `v` is GS, `x ∉ S`, and `x ∈ D_v(S + x)`, then `v({x}) ≠ ⊥`, `v / x` is GS, and for every
`T ⊆ S`, `x ∈ D_v(T + x)` and `D_{v / x}(T) = D_v(T + x) - x`. -/
theorem lem_2_9_contract {n : ℕ} (v : ItemValuation n) (S : Finset (Fin n)) (x : Fin n)
    (hv : IsGSValuation v) (hxS : x ∉ S) (hxD : x ∈ canonicalDemand v (insert x S)) :
    v {x} ≠ ⊥ ∧
    IsGSValuation (contractVal v x) ∧
    ∀ T ⊆ S,
      x ∈ canonicalDemand v (insert x T) ∧
      canonicalDemand (contractVal v x) T = (canonicalDemand v (insert x T)).erase x := by
  obtain ⟨hvx, hgs, heq⟩ :=
    thm_gs_prelim_matroid_and_exchange.2.2.2.2.2.2.2.2.2.2.2.2 n v S x hv hxS hxD
  refine ⟨hvx, hgs, fun T hTS => ⟨?_, heq T hTS⟩⟩
  exact (lem_2_7_persistence v hv).2 (insert x T) (insert x S)
    (Finset.insert_subset_insert x hTS)
    (Finset.mem_inter.mpr ⟨hxD, Finset.mem_insert_self x T⟩)

end

end GrossSubstitutesWelfare
