import GrossSubstitutesWelfare.Defs

set_option maxHeartbeats 4000000

/-!
# Appendix C: Proposition C.1 — Secretary Embedding & Tightness of `1 / e` (`prop:secretary`)

Formalizes Appendix C Proposition C.1 (`prop:secretary`) of *Gross Substitutes Welfare in Random Order*,
including the self-contained finite-Ramsey Game of Googol / Dynkin construction
(`[Gnedin94, CDFS19, BHKKMO25, Dynkin63]`):
- For every `ε > 0`, there is a finite nonempty family of finite-valued GS valuations (each a
  positive multiple of a rank-one matroid rank function plus a modular function) on which every
  randomized non-clairvoyant online algorithm obtains expected value at most `(1 / e + ε) OPT(v)`
  on some member;
- The same `(1 / e + ε) OPT(v)` upper bound holds on a finite family of rank-one weighted matroid
  valuations taking values in `ℝ ∪ {-∞}`.
-/

namespace GrossSubstitutesWelfare

open Classical MeasureTheory

noncomputable section

namespace SecretaryEmbeddingInternal

/-- **Proposition C.1 (Secretary embedding, `prop:secretary`)**:
For every `ε > 0`, there is an item count `n ≥ 1` admitting:
1. A finite nonempty family of finite-valued GS valuations on `n` items, each of the form
   `κ min(|S|, 1) + ∑_{g ∈ S} a_g` (`κ > 0`, `OPT(v) > 0`), such that every online selection
   algorithm achieves expected value at most `(1 / e + ε) OPT(v)` on some member of the family; and
2. A finite nonempty family of rank-one weighted matroids `(M, w)` on `n` items (`OPT(v_M) > 0`)
   such that every online selection algorithm achieves expected value at most
   `(1 / e + ε) OPT(v_M)` on some member of the family. -/
def rankOneModularVal {n : ℕ} (κ : ℝ) (w : Fin n → ℝ) : ItemValuation n :=
  fun S => ((κ * (min S.card 1 : ℕ) + ∑ g ∈ S, (w g - κ) : ℝ) : WithBot ℝ)

theorem fin_ramsey_simultaneous (n : ℕ) (γ : ℕ → Type)
    [∀ k, Fintype (γ k)] [∀ k, Nonempty (γ k)] :
    ∃ N : ℕ, n ≤ N ∧
      ∀ c : (k : ℕ) → Finset (Fin N) → γ k,
        ∃ S : Finset (Fin N), S.card = n ∧
          ∀ k : ℕ, 1 ≤ k → k ≤ n →
            ∀ T₁ ∈ S.powersetCard k, ∀ T₂ ∈ S.powersetCard k, c k T₁ = c k T₂ :=
by
  have h_two_color : ∀ (k m₁ m₂ : ℕ), ∃ R : ℕ,
      ∀ (V : Finset ℕ), R ≤ V.card → ∀ (c : Finset ℕ → Bool),
        (∃ A : Finset ℕ, A ⊆ V ∧ A.card = m₁ ∧ ∀ e ∈ A.powersetCard k, c e = false) ∨
        (∃ B : Finset ℕ, B ⊆ V ∧ B.card = m₂ ∧ ∀ e ∈ B.powersetCard k, c e = true) := by
    intro k
    induction k with
    | zero =>
      intro m₁ m₂
      refine ⟨max m₁ m₂, ?_⟩
      intro V hV c
      cases hc0 : c ∅
      · left
        obtain ⟨A, hAV, hAcard⟩ := Finset.exists_subset_card_eq (le_trans (le_max_left m₁ m₂) hV)
        refine ⟨A, hAV, hAcard, ?_⟩
        intro e he
        rw [Finset.powersetCard_zero, Finset.mem_singleton] at he
        rw [he, hc0]
      · right
        obtain ⟨B, hBV, hBcard⟩ := Finset.exists_subset_card_eq (le_trans (le_max_right m₁ m₂) hV)
        refine ⟨B, hBV, hBcard, ?_⟩
        intro e he
        rw [Finset.powersetCard_zero, Finset.mem_singleton] at he
        rw [he, hc0]
    | succ k ih_k =>
      intro m₁
      induction m₁ with
      | zero =>
        intro m₂
        refine ⟨0, ?_⟩
        intro V _ c
        left
        refine ⟨∅, Finset.empty_subset V, Finset.card_empty, ?_⟩
        intro e he
        rw [Finset.mem_powersetCard] at he
        have he0 : e.card = 0 := Finset.card_eq_zero.mpr (Finset.subset_empty.mp he.1)
        omega
      | succ m₁ ih₁ =>
        intro m₂
        induction m₂ with
        | zero =>
          refine ⟨0, ?_⟩
          intro V _ c
          right
          refine ⟨∅, Finset.empty_subset V, Finset.card_empty, ?_⟩
          intro e he
          rw [Finset.mem_powersetCard] at he
          have he0 : e.card = 0 := Finset.card_eq_zero.mpr (Finset.subset_empty.mp he.1)
          omega
        | succ m₂ ih₂ =>
          obtain ⟨M₁, hM₁⟩ := ih₁ (m₂ + 1)
          obtain ⟨M₂, hM₂⟩ := ih₂
          obtain ⟨R₀, hR₀⟩ := ih_k M₁ M₂
          refine ⟨R₀ + 1, ?_⟩
          intro V hV c
          obtain ⟨v₀, hv₀⟩ := Finset.card_pos.mp (by omega : 0 < V.card)
          let V' : Finset ℕ := V.erase v₀
          have hV'_sub : V' ⊆ V := Finset.erase_subset v₀ V
          have hv₀_notMem : v₀ ∉ V' := Finset.notMem_erase v₀ V
          have hV'_card : R₀ ≤ V'.card := by
            have h_eq : V'.card = V.card - 1 := Finset.card_erase_of_mem hv₀
            omega
          rcases hR₀ V' hV'_card (fun f => c (insert v₀ f)) with
            ⟨W₁, hW₁_sub, hW₁_card, hW₁_col⟩ | ⟨W₂, hW₂_sub, hW₂_card, hW₂_col⟩
          · rcases hM₁ W₁ (by omega) c with
              ⟨A', hA'_sub, hA'_card, hA'_col⟩ | ⟨B, hB_sub, hB_card, hB_col⟩
            · left
              have hv₀_not_A' : v₀ ∉ A' := fun h => hv₀_notMem (hW₁_sub (hA'_sub h))
              refine ⟨insert v₀ A',
                Finset.insert_subset_iff.mpr ⟨hv₀, hA'_sub.trans (hW₁_sub.trans hV'_sub)⟩,
                by rw [Finset.card_insert_of_notMem hv₀_not_A', hA'_card], ?_⟩
              intro e he
              rw [Finset.powersetCard_succ_insert hv₀_not_A' k, Finset.mem_union] at he
              rcases he with he_old | he_new
              · exact hA'_col e he_old
              · rcases Finset.mem_image.mp he_new with ⟨f, hf, rfl⟩
                exact hW₁_col f (Finset.powersetCard_mono hA'_sub hf)
            · right
              exact ⟨B, hB_sub.trans (hW₁_sub.trans hV'_sub), hB_card, hB_col⟩
          · rcases hM₂ W₂ (by omega) c with
              ⟨A, hA_sub, hA_card, hA_col⟩ | ⟨B', hB'_sub, hB'_card, hB'_col⟩
            · left
              exact ⟨A, hA_sub.trans (hW₂_sub.trans hV'_sub), hA_card, hA_col⟩
            · right
              have hv₀_not_B' : v₀ ∉ B' := fun h => hv₀_notMem (hW₂_sub (hB'_sub h))
              refine ⟨insert v₀ B',
                Finset.insert_subset_iff.mpr ⟨hv₀, hB'_sub.trans (hW₂_sub.trans hV'_sub)⟩,
                by rw [Finset.card_insert_of_notMem hv₀_not_B', hB'_card], ?_⟩
              intro e he
              rw [Finset.powersetCard_succ_insert hv₀_not_B' k, Finset.mem_union] at he
              rcases he with he_old | he_new
              · exact hB'_col e he_old
              · rcases Finset.mem_image.mp he_new with ⟨f, hf, rfl⟩
                exact hW₂_col f (Finset.powersetCard_mono hB'_sub hf)

  have h_fin_color : ∀ (k C m : ℕ), ∃ R : ℕ, m ≤ R ∧
      ∀ (V : Finset ℕ), R ≤ V.card → ∀ (c : Finset ℕ → Fin (C + 1)),
        ∃ S : Finset ℕ, S ⊆ V ∧ S.card = m ∧
          ∀ T₁ ∈ S.powersetCard k, ∀ T₂ ∈ S.powersetCard k, c T₁ = c T₂ := by
    intro k C
    induction C with
    | zero =>
      intro m
      refine ⟨m, le_refl m, ?_⟩
      intro V hV c
      obtain ⟨S, hSV, hScard⟩ := Finset.exists_subset_card_eq hV
      exact ⟨S, hSV, hScard, fun T₁ _ T₂ _ => Fin.ext (by omega)⟩
    | succ C ih =>
      intro m
      obtain ⟨R', _, hR'⟩ := ih m
      obtain ⟨R₀, hR₀⟩ := h_two_color k m R'
      refine ⟨max m R₀, le_max_left m R₀, ?_⟩
      intro V hV c
      have hR₀_V : R₀ ≤ V.card := le_trans (le_max_right m R₀) hV
      rcases hR₀ V hR₀_V (fun e => decide (c e ≠ 0)) with
        ⟨A, hAV, hAcard, hAcol⟩ | ⟨B, hBV, hBcard, hBcol⟩
      · refine ⟨A, hAV, hAcard, ?_⟩
        intro T₁ hT₁ T₂ hT₂
        have h₁ : c T₁ = 0 := not_not.mp (decide_eq_false_iff_not.mp (hAcol T₁ hT₁))
        have h₂ : c T₂ = 0 := not_not.mp (decide_eq_false_iff_not.mp (hAcol T₂ hT₂))
        rw [h₁, h₂]
      · let c' : Finset ℕ → Fin (C + 1) := fun e =>
          if h : c e ≠ 0 then (c e).pred h else 0
        obtain ⟨S, hSB, hScard, hScol⟩ := hR' B (by omega) c'
        refine ⟨S, hSB.trans hBV, hScard, ?_⟩
        intro T₁ hT₁ T₂ hT₂
        have hT₁_B : T₁ ∈ B.powersetCard k := Finset.powersetCard_mono hSB hT₁
        have hT₂_B : T₂ ∈ B.powersetCard k := Finset.powersetCard_mono hSB hT₂
        have h₁ : c T₁ ≠ 0 := of_decide_eq_true (hBcol T₁ hT₁_B)
        have h₂ : c T₂ ≠ 0 := of_decide_eq_true (hBcol T₂ hT₂_B)
        have hc' : c' T₁ = c' T₂ := hScol T₁ hT₁ T₂ hT₂
        dsimp only [c'] at hc'
        rw [dif_pos h₁, dif_pos h₂] at hc'
        exact Fin.pred_inj.mp hc'

  have h_single : ∀ (k m : ℕ), ∃ R : ℕ, m ≤ R ∧
      ∀ (V : Finset ℕ), R ≤ V.card → ∀ (c : Finset ℕ → γ k),
        ∃ S : Finset ℕ, S ⊆ V ∧ S.card = m ∧
          ∀ T₁ ∈ S.powersetCard k, ∀ T₂ ∈ S.powersetCard k, c T₁ = c T₂ := by
    intro k m
    have hpos : 0 < Fintype.card (γ k) := Fintype.card_pos
    obtain ⟨C, hC⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hpos)
    let eγ : γ k ≃ Fin (C + 1) := (Fintype.equivFin (γ k)).trans (finCongr hC)
    obtain ⟨R, hmR, hR⟩ := h_fin_color k C m
    refine ⟨R, hmR, ?_⟩
    intro V hV c
    obtain ⟨S, hSV, hScard, hScol⟩ := hR V hV (fun T => eγ (c T))
    exact ⟨S, hSV, hScard, fun T₁ hT₁ T₂ hT₂ => eγ.injective (hScol T₁ hT₁ T₂ hT₂)⟩

  have h_sim_nat : ∀ (j m : ℕ), ∃ N : ℕ, m ≤ N ∧
      ∀ (V : Finset ℕ), N ≤ V.card → ∀ (c : (k : ℕ) → Finset ℕ → γ k),
        ∃ S : Finset ℕ, S ⊆ V ∧ S.card = m ∧
          ∀ k : ℕ, 1 ≤ k → k ≤ j →
            ∀ T₁ ∈ S.powersetCard k, ∀ T₂ ∈ S.powersetCard k, c k T₁ = c k T₂ := by
    intro j
    induction j with
    | zero =>
      intro m
      refine ⟨m, le_refl m, ?_⟩
      intro V hV _
      obtain ⟨S, hSV, hScard⟩ := Finset.exists_subset_card_eq hV
      exact ⟨S, hSV, hScard, fun k hk1 hk0 => by omega⟩
    | succ j ih =>
      intro m
      obtain ⟨R₁, hm_R₁, hR₁⟩ := h_single (j + 1) m
      obtain ⟨N, hR₁_N, hN⟩ := ih R₁
      refine ⟨N, le_trans hm_R₁ hR₁_N, ?_⟩
      intro V hV c
      obtain ⟨V₁, hV₁_sub, hV₁_card, hV₁_mono⟩ := hN V hV c
      obtain ⟨S, hS_sub, hS_card, hS_top⟩ := hR₁ V₁ (by omega) (c (j + 1))
      refine ⟨S, hS_sub.trans hV₁_sub, hS_card, ?_⟩
      intro k hk1 hk_le T₁ hT₁ T₂ hT₂
      rcases Nat.of_le_succ hk_le with hkj | rfl
      · exact hV₁_mono k hk1 hkj T₁ (Finset.powersetCard_mono hS_sub hT₁)
          T₂ (Finset.powersetCard_mono hS_sub hT₂)
      · exact hS_top T₁ hT₁ T₂ hT₂

  obtain ⟨N, hnN, hN⟩ := h_sim_nat n n
  refine ⟨N, hnN, ?_⟩
  intro c
  let V : Finset ℕ := (Finset.univ : Finset (Fin N)).map Fin.valEmbedding
  have hV_card : N ≤ V.card := by
    rw [Finset.card_map, Finset.card_fin]
  let toFin : Finset ℕ → Finset (Fin N) :=
    fun U => (Finset.univ : Finset (Fin N)).filter (fun x => x.1 ∈ U)
  have h_left : ∀ T : Finset (Fin N), toFin (T.map Fin.valEmbedding) = T := by
    intro T
    ext x
    simp only [toFin, Finset.mem_filter, Finset.mem_univ, Finset.mem_map,
      Fin.valEmbedding_apply, true_and]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hy_eq : y = x := Fin.ext hyx
      rwa [← hy_eq]
    · intro hx
      exact ⟨x, hx, rfl⟩
  have h_right : ∀ U : Finset ℕ, U ⊆ V → (toFin U).map Fin.valEmbedding = U := by
    intro U hUV
    ext a
    simp only [toFin, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
      Fin.valEmbedding_apply, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro ha
      rcases Finset.mem_map.mp (hUV ha) with ⟨x, _, hxa⟩
      rw [Fin.valEmbedding_apply] at hxa
      exact ⟨x, by rwa [hxa], hxa⟩
  obtain ⟨S_nat, hS_sub, hS_card, hS_mono⟩ := hN V hV_card (fun k U => c k (toFin U))
  let S : Finset (Fin N) := toFin S_nat
  have hS_map : S.map Fin.valEmbedding = S_nat := h_right S_nat hS_sub
  have hS_card_eq : S.card = n := by
    rw [← Finset.card_map Fin.valEmbedding, hS_map, hS_card]
  refine ⟨S, hS_card_eq, ?_⟩
  intro k hk1 hkn T₁ hT₁ T₂ hT₂
  have h_map_mem : ∀ {T : Finset (Fin N)}, T ∈ S.powersetCard k →
      T.map Fin.valEmbedding ∈ S_nat.powersetCard k := by
    intro T hT
    rw [Finset.mem_powersetCard] at hT ⊢
    refine ⟨?_, by rw [Finset.card_map, hT.2]⟩
    rw [← hS_map]
    exact Finset.map_subset_map.mpr hT.1
  have h_eq := hS_mono k hk1 hkn (T₁.map Fin.valEmbedding) (h_map_mem hT₁)
    (T₂.map Fin.valEmbedding) (h_map_mem hT₂)
  rw [h_left T₁, h_left T₂] at h_eq
  exact h_eq

theorem ordinal_secretary_bound (n : ℕ) (hn : 1 ≤ n)
    (q : Fin n → Equiv.Perm (Fin n) → ℝ)
    (hq_nonneg : ∀ (k : Fin n) (ρ : Equiv.Perm (Fin n)), 0 ≤ q k ρ)
    (hq_sum : ∀ ρ : Equiv.Perm (Fin n), ∑ k : Fin n, q k ρ ≤ 1)
    (hq_ord : ∀ (k : Fin n) (ρ₁ ρ₂ : Equiv.Perm (Fin n)),
      (∀ i j : Fin n, i ≤ k → j ≤ k → (ρ₁ i ≤ ρ₁ j ↔ ρ₂ i ≤ ρ₂ j)) →
      q k ρ₁ = q k ρ₂) :
    (1 / (Nat.factorial n : ℝ)) *
      ∑ ρ : Equiv.Perm (Fin n),
        ∑ k ∈ Finset.univ.filter (fun k : Fin n => (ρ k).1 = n - 1), q k ρ ≤
      invE + 1 / (n : ℝ) :=
by
  
  let β : Fin n → Type := fun j => Fin (j.1 + 1)
  let S_lt : Equiv.Perm (Fin n) → Fin n → Finset (Fin n) :=
    fun ρ k => (Finset.Iio k).filter (fun i => ρ i < ρ k)
  let f_rank : Equiv.Perm (Fin n) → ((j : Fin n) → β j) :=
    fun ρ k => ⟨(S_lt ρ k).card,
      Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans_eq (Fin.card_Iio k))⟩

  have hf_ord : ∀ (m : ℕ) (k : Fin n), k.1 = m → ∀ (ρ₁ ρ₂ : Equiv.Perm (Fin n)),
      (∀ j : Fin n, j ≤ k → f_rank ρ₁ j = f_rank ρ₂ j) →
      (∀ i j : Fin n, i ≤ k → j ≤ k → (ρ₁ i ≤ ρ₁ j ↔ ρ₂ i ≤ ρ₂ j)) := by
    intro m
    induction m with
    | zero =>
      intro k hk ρ₁ ρ₂ _ i j hi hj
      have hi0 : i.1 = 0 := by change i.1 ≤ k.1 at hi; omega
      have hj0 : j.1 = 0 := by change j.1 ≤ k.1 at hj; omega
      have hij : i = j := Fin.ext (by omega)
      subst hij
      simp
    | succ m ih =>
      intro k hk ρ₁ ρ₂ hf
      let k' : Fin n := ⟨m, by omega⟩
      have hk'_le : k' ≤ k := by change m ≤ k.1; omega
      have ih_k' : ∀ a b : Fin n, a < k → b < k → (ρ₁ a ≤ ρ₁ b ↔ ρ₂ a ≤ ρ₂ b) := by
        intro a b ha hb
        exact ih k' rfl ρ₁ ρ₂ (fun j hj => hf j (le_trans hj hk'_le)) a b
          (by change a.1 ≤ m; change a.1 < k.1 at ha; omega)
          (by change b.1 ≤ m; change b.1 < k.1 at hb; omega)
      have h_step_lt : ∀ (σ₁ σ₂ : Equiv.Perm (Fin n)),
          (∀ a b : Fin n, a < k → b < k → (σ₁ a ≤ σ₁ b ↔ σ₂ a ≤ σ₂ b)) →
          (S_lt σ₁ k).card = (S_lt σ₂ k).card →
          ∀ i : Fin n, i < k → σ₁ i < σ₁ k → σ₂ i < σ₂ k := by
        intro σ₁ σ₂ h_prev h_card i hi h1
        by_contra h2
        have h2_le : σ₂ k ≤ σ₂ i := not_lt.mp h2
        have h_sub : S_lt σ₂ k ⊆ S_lt σ₁ k := by
          intro a ha
          have ha' := Finset.mem_filter.mp ha
          have ha_lt : a < k := Finset.mem_Iio.mp ha'.1
          have ha2 : σ₂ a ≤ σ₂ i := le_of_lt (lt_of_lt_of_le ha'.2 h2_le)
          have ha1 : σ₁ a ≤ σ₁ i := (h_prev a i ha_lt hi).mpr ha2
          exact Finset.mem_filter.mpr ⟨ha'.1, lt_of_le_of_lt ha1 h1⟩
        have hi_mem1 : i ∈ S_lt σ₁ k :=
          Finset.mem_filter.mpr ⟨Finset.mem_Iio.mpr hi, h1⟩
        have hi_nmem2 : i ∉ S_lt σ₂ k := by
          intro hmem
          exact h2 (Finset.mem_filter.mp hmem).2
        have h_ssub : S_lt σ₂ k ⊂ S_lt σ₁ k :=
          Finset.ssubset_iff_subset_ne.mpr ⟨h_sub, fun heq => hi_nmem2 (heq ▸ hi_mem1)⟩
        have h_lt_card := Finset.card_lt_card h_ssub
        omega
      have h_card_k : (S_lt ρ₁ k).card = (S_lt ρ₂ k).card :=
        congrArg Fin.val (hf k le_rfl)
      have h_lt_k : ∀ x : Fin n, x < k → (ρ₁ x < ρ₁ k ↔ ρ₂ x < ρ₂ k) := fun x hx =>
        ⟨h_step_lt ρ₁ ρ₂ ih_k' h_card_k x hx,
         h_step_lt ρ₂ ρ₁ (fun a b ha hb => (ih_k' a b ha hb).symm) h_card_k.symm x hx⟩
      intro a b ha hb
      rcases lt_or_eq_of_le ha with ha_lt | ha_eq <;> rcases lt_or_eq_of_le hb with hb_lt | hb_eq
      · exact ih_k' a b ha_lt hb_lt
      · rw [hb_eq]
        have hne1 : ρ₁ a ≠ ρ₁ k := ρ₁.injective.ne (ne_of_lt ha_lt)
        have hne2 : ρ₂ a ≠ ρ₂ k := ρ₂.injective.ne (ne_of_lt ha_lt)
        rw [le_iff_lt_or_eq, le_iff_lt_or_eq]
        simp only [hne1, hne2, or_false]
        exact h_lt_k a ha_lt
      · rw [ha_eq, ← not_lt, ← not_lt]
        exact not_congr (h_lt_k b hb_lt)
      · rw [ha_eq, hb_eq]
        simp

  have hf_inj : Function.Injective f_rank := by
    intro ρ₁ ρ₂ h12
    let k_top : Fin n := ⟨n - 1, by omega⟩
    have h_all : ∀ i j : Fin n, ρ₁ i ≤ ρ₁ j ↔ ρ₂ i ≤ ρ₂ j := fun i j =>
      hf_ord (n - 1) k_top rfl ρ₁ ρ₂ (fun a _ => congrFun h12 a) i j
        (by change i.1 ≤ n - 1; omega) (by change j.1 ≤ n - 1; omega)
    let φ : Fin n ≃o Fin n :=
      { toEquiv := ρ₁.symm.trans ρ₂
        map_rel_iff' := by
          intro x y
          simp only [Equiv.trans_apply]
          rw [← h_all (ρ₁.symm x) (ρ₁.symm y)]
          simp }
    have hφ : φ = OrderIso.refl (Fin n) := Subsingleton.elim _ _
    apply Equiv.ext
    intro z
    have hz : φ (ρ₁ z) = (OrderIso.refl (Fin n)) (ρ₁ z) :=
      congrArg (fun g : Fin n ≃o Fin n => g (ρ₁ z)) hφ
    simpa [φ] using hz.symm

  have h_card_R : Fintype.card ((j : Fin n) → β j) = n.factorial := by
    rw [Fintype.card_pi]
    simp only [β, Fintype.card_fin]
    rw [Fin.prod_univ_eq_prod_range (fun m => m + 1) n, Finset.prod_range_add_one_eq_factorial]

  have h_card_perm : Fintype.card (Equiv.Perm (Fin n)) = Fintype.card ((j : Fin n) → β j) := by
    rw [Fintype.card_perm, Fintype.card_fin, h_card_R]

  let e : Equiv.Perm (Fin n) ≃ ((j : Fin n) → β j) :=
    Equiv.ofBijective f_rank ((Fintype.bijective_iff_injective_and_card f_rank).mpr ⟨hf_inj, h_card_perm⟩)

  have h_rec_iff : ∀ (ρ : Equiv.Perm (Fin n)) (j : Fin n),
      (e ρ j).1 = j.1 ↔ ∀ i : Fin n, i < j → ρ i < ρ j := by
    intro ρ j
    change (S_lt ρ j).card = j.1 ↔ ∀ i : Fin n, i < j → ρ i < ρ j
    constructor
    · intro hcard i hi
      have h_eq : S_lt ρ j = Finset.Iio j :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
          (by rw [Fin.card_Iio, hcard])
      have hmem : i ∈ S_lt ρ j := by rw [h_eq]; exact Finset.mem_Iio.mpr hi
      exact (Finset.mem_filter.mp hmem).2
    · intro hall
      have h_eq : S_lt ρ j = Finset.Iio j :=
        Finset.filter_eq_self.mpr (fun i hi => hall i (Finset.mem_Iio.mp hi))
      rw [h_eq, Fin.card_Iio]

  have he_max : ∀ (ρ : Equiv.Perm (Fin n)) (k : Fin n),
      (ρ k).1 = n - 1 ↔ ((e ρ k).1 = k.1 ∧ ∀ j : Fin n, k < j → (e ρ j).1 ≠ j.1) := by
    intro ρ k
    have h_max_iff : (ρ k).1 = n - 1 ↔ ∀ j : Fin n, ρ j ≤ ρ k := by
      constructor
      · intro hk j
        change (ρ j).1 ≤ (ρ k).1
        have := (ρ j).2
        omega
      · intro hall
        let j_top : Fin n := ⟨n - 1, by omega⟩
        have h1 : ρ (ρ.symm j_top) ≤ ρ k := hall (ρ.symm j_top)
        rw [Equiv.apply_symm_apply] at h1
        change n - 1 ≤ (ρ k).1 at h1
        have := (ρ k).2
        omega
    rw [h_max_iff]
    constructor
    · intro hall
      refine ⟨(h_rec_iff ρ k).mpr (fun i hi => ?_), fun j hj h_eq => ?_⟩
      · exact lt_of_le_of_ne (hall i) (ρ.injective.ne (ne_of_lt hi))
      · have h_lt : ρ k < ρ j := (h_rec_iff ρ j).mp h_eq k hj
        exact not_lt_of_ge (hall j) h_lt
    · rintro ⟨hk_rec, h_no_later⟩
      have h_strong : ∀ m : ℕ, ∀ j : Fin n, j.1 = m → ρ j ≤ ρ k := by
        intro m
        induction m using Nat.strong_induction_on with
        | h m ih =>
          intro j hjm
          rcases lt_trichotomy j k with hjk | rfl | hkj
          · exact le_of_lt ((h_rec_iff ρ k).mp hk_rec j hjk)
          · exact le_rfl
          · by_contra h_not_le
            have h_kj_lt : ρ k < ρ j := not_le.mp h_not_le
            apply h_no_later j hkj
            rw [h_rec_iff ρ j]
            intro i hij
            have hi_le : ρ i ≤ ρ k := ih i.1 (by change i.1 < j.1 at hij; omega) i rfl
            exact lt_of_le_of_lt hi_le h_kj_lt
      exact fun j => h_strong j.1 j rfl

  
  let Q : Fin n → ((j : Fin n) → β j) → ℝ := fun k r => q k (e.symm r)
  have hQ_nonneg : ∀ (k : Fin n) (r : (j : Fin n) → β j), 0 ≤ Q k r :=
    fun k r => hq_nonneg k (e.symm r)
  have hQ_sum : ∀ r : (j : Fin n) → β j, ∑ k : Fin n, Q k r ≤ 1 :=
    fun r => hq_sum (e.symm r)
  have hQ_prefix : ∀ (k : Fin n) (r₁ r₂ : (j : Fin n) → β j),
      (∀ j : Fin n, j ≤ k → r₁ j = r₂ j) → Q k r₁ = Q k r₂ := by
    intro k r₁ r₂ h_eq
    apply hq_ord k (e.symm r₁) (e.symm r₂)
    apply hf_ord k.1 k rfl (e.symm r₁) (e.symm r₂)
    intro j hj
    change e (e.symm r₁) j = e (e.symm r₂) j
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact h_eq j hj

  have h_sum_transfer :
      ∑ ρ : Equiv.Perm (Fin n),
        ∑ k ∈ Finset.univ.filter (fun k : Fin n => (ρ k).1 = n - 1), q k ρ =
      ∑ r : ((j : Fin n) → β j),
        ∑ k : Fin n, (if (r k).1 = k.1 ∧ (∀ j : Fin n, k < j → (r j).1 ≠ j.1) then Q k r else 0) := by
    rw [← Equiv.sum_comp e.symm]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have h1 := he_max (e.symm r) k
    rw [Equiv.apply_symm_apply] at h1
    by_cases hc : ((e.symm r) k).1 = n - 1
    · rw [if_pos hc, if_pos (h1.mp hc)]
    · rw [if_neg hc, if_neg (fun h' => hc (h1.mpr h'))]

  have sum_mul_of_lt_invariant : ∀ (j₀ : Fin n) (g : Fin (j₀.1 + 1) → ℝ)
      (F : ((j : Fin n) → β j) → ℝ),
      (∀ r₁ r₂ : (j : Fin n) → β j, (∀ i : Fin n, i < j₀ → r₁ i = r₂ i) → F r₁ = F r₂) →
      ((j₀.1 + 1 : ℕ) : ℝ) * ∑ r : ((j : Fin n) → β j), g (r j₀) * F r =
        (∑ x : Fin (j₀.1 + 1), g x) * (∑ r : ((j : Fin n) → β j), F r) := by
    intro j₀ g F hF
    let es := Equiv.piSplitAt j₀ β
    have h_symm_at : ∀ (x : Fin (j₀.1 + 1)) (rest : (i : {i : Fin n // i ≠ j₀}) → β i.1),
        (es.symm (x, rest)) j₀ = x := by
      intro x rest
      have h := es.apply_symm_apply (x, rest)
      rw [Equiv.piSplitAt_apply] at h
      exact congrArg Prod.fst h
    have h_symm_ne : ∀ (x : Fin (j₀.1 + 1)) (rest : (i : {i : Fin n // i ≠ j₀}) → β i.1)
        (i : Fin n) (hi : i ≠ j₀), (es.symm (x, rest)) i = rest ⟨i, hi⟩ := by
      intro x rest i hi
      have h := es.apply_symm_apply (x, rest)
      rw [Equiv.piSplitAt_apply] at h
      exact congrFun (congrArg Prod.snd h) ⟨i, hi⟩
    have hF_indep : ∀ (x : Fin (j₀.1 + 1)) (rest : (i : {i : Fin n // i ≠ j₀}) → β i.1),
        F (es.symm (x, rest)) = F (es.symm (0, rest)) := by
      intro x rest
      apply hF
      intro i hi
      rw [h_symm_ne x rest i (ne_of_lt hi), h_symm_ne 0 rest i (ne_of_lt hi)]
    have h_split : ∀ g' : Fin (j₀.1 + 1) → ℝ,
        ∑ r : ((j : Fin n) → β j), g' (r j₀) * F r =
          (∑ x : Fin (j₀.1 + 1), g' x) * ∑ rest, F (es.symm (0, rest)) := by
      intro g'
      rw [← Equiv.sum_comp es.symm, Fintype.sum_prod_type]
      simp_rw [h_symm_at, hF_indep, ← Finset.mul_sum, ← Finset.sum_mul]
      rfl
    have hg1 := h_split g
    have hg_one := h_split (fun _ => 1)
    simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] at hg_one
    calc ((j₀.1 + 1 : ℕ) : ℝ) * ∑ r : ((j : Fin n) → β j), g (r j₀) * F r
        = ((j₀.1 + 1 : ℕ) : ℝ) * ((∑ x : Fin (j₀.1 + 1), g x) * ∑ rest, F (es.symm (0, rest))) := by
          rw [hg1]
      _ = (∑ x : Fin (j₀.1 + 1), g x) * (((j₀.1 + 1 : ℕ) : ℝ) * ∑ rest, F (es.symm (0, rest))) := by
          ring
      _ = (∑ x : Fin (j₀.1 + 1), g x) * ∑ r : ((j : Fin n) → β j), F r := by
          rw [← hg_one]

  have h_fin_eq_sum : ∀ m : ℕ, ∑ x : Fin (m + 1), (if x.1 = m then (1 : ℝ) else 0) = 1 := by
    intro m
    let x_top : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
    have h_iff : ∀ x : Fin (m + 1), x.1 = m ↔ x = x_top := by
      intro x
      constructor
      · intro h
        exact Fin.ext h
      · rintro rfl
        rfl
    simp_rw [h_iff]
    simp

  have h_fin_ne_sum : ∀ m : ℕ, ∑ x : Fin (m + 1), (if x.1 ≠ m then (1 : ℝ) else 0) = (m : ℝ) := by
    intro m
    have h_pt : ∀ x : Fin (m + 1),
        (if x.1 ≠ m then (1 : ℝ) else 0) + (if x.1 = m then (1 : ℝ) else 0) = 1 := by
      intro x
      by_cases hx : x.1 = m <;> simp [hx]
    have h_tot : ∑ x : Fin (m + 1),
        ((if x.1 ≠ m then (1 : ℝ) else 0) + (if x.1 = m then (1 : ℝ) else 0)) = (m : ℝ) + 1 := by
      simp_rw [h_pt]
      simp [Nat.cast_add]
    rw [Finset.sum_add_distrib, h_fin_eq_sum m] at h_tot
    linarith

  
  let u_pay : (k : Fin n) → Fin (k.1 + 1) → ℝ :=
    fun k x => if x.1 = k.1 then ((k.1 + 1 : ℕ) : ℝ) / (n : ℝ) else 0

  have hn_pos : 0 < (n : ℝ) := by positivity
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos

  have h_cond_win : ∀ k : Fin n,
      ∑ r : ((j : Fin n) → β j),
        (if (r k).1 = k.1 ∧ (∀ j : Fin n, k < j → (r j).1 ≠ j.1) then Q k r else 0) =
      ∑ r : ((j : Fin n) → β j), u_pay k (r k) * Q k r := by
    intro k
    let H : ((j : Fin n) → β j) → ℝ := fun r => if (r k).1 = k.1 then Q k r else 0
    let W : ℕ → ((j : Fin n) → β j) → ℝ :=
      fun m r => if (∀ j : Fin n, k < j → j.1 < m → (r j).1 ≠ j.1) then H r else 0
    have h_inv : ∀ m : ℕ, k.1 + 1 ≤ m → m ≤ n →
        (m : ℝ) * ∑ r : ((j : Fin n) → β j), W m r =
          ((k.1 + 1 : ℕ) : ℝ) * ∑ r : ((j : Fin n) → β j), H r := by
      intro m hm_lo
      induction m, hm_lo using Nat.le_induction with
      | base =>
        intro _
        have hW_base : ∀ r : (j : Fin n) → β j, W (k.1 + 1) r = H r := by
          intro r
          dsimp [W]
          rw [if_pos]
          intro j hkj hjm
          change k.1 < j.1 at hkj
          omega
        simp_rw [hW_base]
      | succ m hm_lo ih =>
        intro hm_hi
        let jm : Fin n := ⟨m, hm_hi⟩
        have hk_lt_jm : k < jm := by change k.1 < m; omega
        have hW_step : ∀ r : (j : Fin n) → β j,
            W (m + 1) r = (if (r jm).1 ≠ m then (1 : ℝ) else 0) * W m r := by
          intro r
          dsimp [W]
          by_cases hjm_ne : (r jm).1 ≠ m
          · rw [if_pos hjm_ne, one_mul]
            have h_cond_iff :
                (∀ j : Fin n, k < j → j.1 < m + 1 → (r j).1 ≠ j.1) ↔
                (∀ j : Fin n, k < j → j.1 < m → (r j).1 ≠ j.1) := by
              constructor
              · intro h j hkj hjm
                exact h j hkj (by omega)
              · intro h j hkj hjm1
                rcases Nat.lt_succ_iff_lt_or_eq.mp hjm1 with hlt | heq
                · exact h j hkj hlt
                · have hj_eq : j = jm := Fin.ext heq
                  subst hj_eq
                  exact hjm_ne
            by_cases hc : ∀ j : Fin n, k < j → j.1 < m → (r j).1 ≠ j.1
            · rw [if_pos (h_cond_iff.mpr hc), if_pos hc]
            · rw [if_neg (fun h' => hc (h_cond_iff.mp h')), if_neg hc]
          · rw [if_neg hjm_ne, zero_mul, if_neg]
            intro hall
            exact hjm_ne (hall jm hk_lt_jm (Nat.lt_succ_self m))
        have hWm_indep : ∀ r₁ r₂ : (j : Fin n) → β j,
            (∀ i : Fin n, i < jm → r₁ i = r₂ i) → W m r₁ = W m r₂ := by
          intro r₁ r₂ h_eq
          have hH_eq : H r₁ = H r₂ := by
            dsimp [H]
            rw [h_eq k hk_lt_jm, hQ_prefix k r₁ r₂ (fun j hj => h_eq j (lt_of_le_of_lt hj hk_lt_jm))]
          have h_cond_eq :
              (∀ j : Fin n, k < j → j.1 < m → (r₁ j).1 ≠ j.1) ↔
              (∀ j : Fin n, k < j → j.1 < m → (r₂ j).1 ≠ j.1) := by
            refine forall_congr' (fun j => imp_congr_right (fun _ => imp_congr_right (fun hjm => ?_)))
            have hj_lt : j < jm := hjm
            rw [h_eq j hj_lt]
          dsimp [W]
          rw [hH_eq]
          by_cases hc : ∀ j : Fin n, k < j → j.1 < m → (r₂ j).1 ≠ j.1
          · rw [if_pos (h_cond_eq.mpr hc), if_pos hc]
          · rw [if_neg (fun h1 => hc (h_cond_eq.mp h1)), if_neg hc]
        calc ((m + 1 : ℕ) : ℝ) * ∑ r : ((j : Fin n) → β j), W (m + 1) r
            = ((jm.1 + 1 : ℕ) : ℝ) * ∑ r : ((j : Fin n) → β j),
                (if (r jm).1 ≠ m then (1 : ℝ) else 0) * W m r := by
              simp_rw [hW_step]
              rfl
          _ = (∑ x : Fin (jm.1 + 1), if x.1 ≠ m then (1 : ℝ) else 0) *
                ∑ r : ((j : Fin n) → β j), W m r :=
              sum_mul_of_lt_invariant jm
                (fun x : Fin (jm.1 + 1) => if x.1 ≠ m then (1 : ℝ) else 0) (W m) hWm_indep
          _ = (m : ℝ) * ∑ r : ((j : Fin n) → β j), W m r := by
              change (∑ x : Fin (m + 1), if x.1 ≠ m then (1 : ℝ) else 0) * _ = _
              rw [h_fin_ne_sum m]
          _ = ((k.1 + 1 : ℕ) : ℝ) * ∑ r : ((j : Fin n) → β j), H r := ih (by omega)
    have h_at_n := h_inv n k.2 le_rfl
    have hWn_eq : ∀ r : (j : Fin n) → β j,
        W n r = if (r k).1 = k.1 ∧ (∀ j : Fin n, k < j → (r j).1 ≠ j.1) then Q k r else 0 := by
      intro r
      dsimp [W, H]
      by_cases h1 : (r k).1 = k.1 <;> by_cases h2 : ∀ j : Fin n, k < j → (r j).1 ≠ j.1
      · have h2' : ∀ j : Fin n, k < j → j.1 < n → (r j).1 ≠ j.1 := fun j hkj _ => h2 j hkj
        rw [if_pos h2', if_pos h1, if_pos ⟨h1, h2⟩]
      · have h2' : ¬ (∀ j : Fin n, k < j → j.1 < n → (r j).1 ≠ j.1) :=
          fun hall => h2 (fun j hkj => hall j hkj j.2)
        rw [if_neg h2', if_neg (fun hc => h2 hc.2)]
      · simp [h1]
      · simp [h1]
    have hu_eq : ∀ r : (j : Fin n) → β j,
        u_pay k (r k) * Q k r = (((k.1 + 1 : ℕ) : ℝ) / (n : ℝ)) * H r := by
      intro r
      dsimp [u_pay, H]
      by_cases h1 : (r k).1 = k.1 <;> simp [h1, mul_comm]
    simp_rw [hWn_eq] at h_at_n
    simp_rw [hu_eq, ← Finset.mul_sum]
    apply mul_left_cancel₀ hn_ne
    rw [h_at_n]
    field_simp [hn_ne]

  
  let stepFn : ℕ → ℝ → ℝ := fun m prev =>
    (1 / (m : ℝ)) * max ((m : ℝ) / (n : ℝ)) prev + (((m : ℝ) - 1) / (m : ℝ)) * prev
  let aux : ℕ → ℝ := Nat.rec 0 (fun d prev => stepFn (n - d) prev)
  let V : ℕ → ℝ := fun m => aux (n + 1 - m)

  have hV_end : V (n + 1) = 0 := by
    dsimp [V, aux]
    rw [Nat.sub_self]
    rfl

  have hV_step : ∀ m : ℕ, 1 ≤ m → m ≤ n →
      V m = (1 / (m : ℝ)) * max ((m : ℝ) / (n : ℝ)) (V (m + 1)) +
        (((m : ℝ) - 1) / (m : ℝ)) * V (m + 1) := by
    intro m hm1 hmn
    let d : ℕ := n - m
    have hd1 : n + 1 - m = d + 1 := by omega
    have hd2 : n + 1 - (m + 1) = d := by omega
    have hd3 : n - d = m := by omega
    change aux (n + 1 - m) = stepFn m (aux (n + 1 - (m + 1)))
    rw [hd1, hd2]
    change stepFn (n - d) (aux d) = stepFn m (aux d)
    rw [hd3]

  have hV_nonneg : ∀ m : ℕ, 1 ≤ m → m ≤ n + 1 → 0 ≤ V m := by
    have h_aux : ∀ d : ℕ, d ≤ n → 0 ≤ V (n + 1 - d) := by
      intro d
      induction d with
      | zero =>
        intro _
        rw [Nat.sub_zero, hV_end]
      | succ d ih =>
        intro hd
        let m : ℕ := n - d
        have hm1 : 1 ≤ m := by omega
        have hmn : m ≤ n := by omega
        have heq1 : n + 1 - (d + 1) = m := by omega
        have heq2 : n + 1 - d = m + 1 := by omega
        rw [heq1, hV_step m hm1 hmn]
        have h_prev : 0 ≤ V (m + 1) := by rw [← heq2]; exact ih (by omega)
        have hm_pos : 0 < (m : ℝ) := by positivity
        have hm_ge1 : 0 ≤ (m : ℝ) - 1 := by
          have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
          linarith
        have h_max_nonneg : 0 ≤ max ((m : ℝ) / (n : ℝ)) (V (m + 1)) :=
          le_trans h_prev (le_max_right _ _)
        positivity
    intro m hm1 hmn1
    have h := h_aux (n + 1 - m) (by omega)
    have heq : n + 1 - (n + 1 - m) = m := by omega
    rwa [heq] at h

  let B : ℕ → ((j : Fin n) → β j) → ℝ :=
    fun m r => 1 - ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.1 < m), Q i r

  have hB_zero : ∀ r : (j : Fin n) → β j, B 0 r = 1 := by
    intro r
    dsimp [B]
    simp

  have hB_nonneg : ∀ (m : ℕ) (r : (j : Fin n) → β j), 0 ≤ B m r := by
    intro m r
    dsimp [B]
    have h_sub : ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.1 < m), Q i r ≤ ∑ i : Fin n, Q i r :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => hQ_nonneg i r)
    linarith [hQ_sum r]

  have hB_rec : ∀ (k : Fin n) (r : (j : Fin n) → β j), Q k r + B (k.1 + 1) r = B k.1 r := by
    intro k r
    dsimp [B]
    have h_filt : Finset.univ.filter (fun i : Fin n => i.1 < k.1 + 1) =
        insert k (Finset.univ.filter (fun i : Fin n => i.1 < k.1)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      rw [Fin.ext_iff]
      omega
    have hk_nmem : k ∉ Finset.univ.filter (fun i : Fin n => i.1 < k.1) := by simp
    rw [h_filt, Finset.sum_insert hk_nmem]
    ring

  have hB_indep : ∀ (k : Fin n) (r₁ r₂ : (j : Fin n) → β j),
      (∀ j : Fin n, j < k → r₁ j = r₂ j) → B k.1 r₁ = B k.1 r₂ := by
    intro k r₁ r₂ h_eq
    dsimp [B]
    congr 1
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi_lt : i < k := (Finset.mem_filter.mp hi).2
    exact hQ_prefix i r₁ r₂ (fun j hj => h_eq j (lt_of_le_of_lt hj hi_lt))

  have h_dp_step : ∀ k : Fin n,
      ∑ r : ((j : Fin n) → β j), u_pay k (r k) * Q k r ≤
        V (k.1 + 1) * (∑ r : ((j : Fin n) → β j), B k.1 r) -
          V (k.1 + 2) * (∑ r : ((j : Fin n) → β j), B (k.1 + 1) r) := by
    intro k
    let m : ℕ := k.1 + 1
    have hm1 : 1 ≤ m := by omega
    have hmn : m ≤ n := k.2
    have hm_pos : 0 < (m : ℝ) := by positivity
    have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
    have hVm1_nonneg : 0 ≤ V (m + 1) := hV_nonneg (m + 1) (by omega) (by omega)
    have h_pt : ∀ r : (j : Fin n) → β j,
        u_pay k (r k) * Q k r + V (m + 1) * B m r ≤
          max (u_pay k (r k)) (V (m + 1)) * B k.1 r := by
      intro r
      have h1 : u_pay k (r k) * Q k r ≤ max (u_pay k (r k)) (V (m + 1)) * Q k r :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (hQ_nonneg k r)
      have h2 : V (m + 1) * B m r ≤ max (u_pay k (r k)) (V (m + 1)) * B m r :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (hB_nonneg m r)
      calc u_pay k (r k) * Q k r + V (m + 1) * B m r
          ≤ max (u_pay k (r k)) (V (m + 1)) * Q k r + max (u_pay k (r k)) (V (m + 1)) * B m r :=
            add_le_add h1 h2
        _ = max (u_pay k (r k)) (V (m + 1)) * (Q k r + B m r) := by ring
        _ = max (u_pay k (r k)) (V (m + 1)) * B k.1 r := by rw [hB_rec k r]
    have h_sum_pt :
        (∑ r : ((j : Fin n) → β j), u_pay k (r k) * Q k r) +
          V (m + 1) * (∑ r : ((j : Fin n) → β j), B m r) ≤
        ∑ r : ((j : Fin n) → β j), max (u_pay k (r k)) (V (m + 1)) * B k.1 r := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun r _ => h_pt r)
    have h_fact := sum_mul_of_lt_invariant k (fun x : Fin (k.1 + 1) => max (u_pay k x) (V (m + 1)))
      (B k.1) (hB_indep k)
    have h_max_sum : ∑ x : Fin (k.1 + 1), max (u_pay k x) (V (m + 1)) = (m : ℝ) * V m := by
      have h_max_pt : ∀ x : Fin (k.1 + 1),
          max (u_pay k x) (V (m + 1)) =
            (if x.1 = k.1 then (1 : ℝ) else 0) * max ((m : ℝ) / (n : ℝ)) (V (m + 1)) +
              (if x.1 ≠ k.1 then (1 : ℝ) else 0) * V (m + 1) := by
        intro x
        dsimp [u_pay]
        by_cases hx : x.1 = k.1
        · simp [hx, m]
        · simp [hx, max_eq_right hVm1_nonneg]
      simp_rw [h_max_pt, Finset.sum_add_distrib, ← Finset.sum_mul, h_fin_eq_sum k.1, h_fin_ne_sum k.1]
      rw [hV_step m hm1 hmn]
      have hm_cast : (m : ℝ) = (k.1 : ℝ) + 1 := by simp [m, Nat.cast_add]
      field_simp [hm_ne]
      rw [hm_cast]
      ring
    rw [h_max_sum] at h_fact
    have h_rhs_eq :
        ∑ r : ((j : Fin n) → β j), max (u_pay k (r k)) (V (m + 1)) * B k.1 r =
          V m * ∑ r : ((j : Fin n) → β j), B k.1 r := by
      apply mul_left_cancel₀ hm_ne
      change ((k.1 + 1 : ℕ) : ℝ) * _ = ((k.1 + 1 : ℕ) : ℝ) * _
      rw [h_fact]
      ring
    rw [h_rhs_eq] at h_sum_pt
    change ∑ r, u_pay k (r k) * Q k r ≤ V m * (∑ r, B k.1 r) - V (m + 1) * (∑ r, B m r)
    linarith

  have h_fact_pos : 0 < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h_fact_ne : (Nat.factorial n : ℝ) ≠ 0 := ne_of_gt h_fact_pos

  have h_lhs_le_V1 :
      (1 / (Nat.factorial n : ℝ)) *
        ∑ ρ : Equiv.Perm (Fin n),
          ∑ k ∈ Finset.univ.filter (fun k : Fin n => (ρ k).1 = n - 1), q k ρ ≤ V 1 := by
    rw [h_sum_transfer, Finset.sum_comm]
    simp_rw [h_cond_win]
    let f_tel : ℕ → ℝ := fun t => V (t + 1) * (∑ r : ((j : Fin n) → β j), B t r)
    have h_sum_le :
        ∑ k : Fin n, ∑ r : ((j : Fin n) → β j), u_pay k (r k) * Q k r ≤
          (Nat.factorial n : ℝ) * V 1 := by
      calc ∑ k : Fin n, ∑ r : ((j : Fin n) → β j), u_pay k (r k) * Q k r
          ≤ ∑ k : Fin n, (f_tel k.1 - f_tel (k.1 + 1)) :=
            Finset.sum_le_sum (fun k _ => h_dp_step k)
        _ = ∑ t ∈ Finset.range n, (f_tel t - f_tel (t + 1)) :=
            Fin.sum_univ_eq_sum_range (fun t => f_tel t - f_tel (t + 1)) n
        _ = f_tel 0 - f_tel n := Finset.sum_range_sub' f_tel n
        _ = (Nat.factorial n : ℝ) * V 1 := by
            dsimp [f_tel]
            simp_rw [hB_zero]
            rw [hV_end, zero_mul, sub_zero, Finset.sum_const, Finset.card_univ, h_card_R,
              nsmul_eq_mul, mul_one, mul_comm]
    have h_mul := mul_le_mul_of_nonneg_left h_sum_le (by positivity : 0 ≤ 1 / (Nat.factorial n : ℝ))
    have h_cancel : (1 / (Nat.factorial n : ℝ)) * ((Nat.factorial n : ℝ) * V 1) = V 1 := by
      field_simp [h_fact_ne]
    linarith

  
  have hV_mono_step : ∀ m : ℕ, 1 ≤ m → m ≤ n → V (m + 1) ≤ V m := by
    intro m hm1 hmn
    have hm_pos : 0 < (m : ℝ) := by positivity
    have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
    have h_diff : V m - V (m + 1) =
        (1 / (m : ℝ)) * (max ((m : ℝ) / (n : ℝ)) (V (m + 1)) - V (m + 1)) := by
      rw [hV_step m hm1 hmn]
      field_simp [hm_ne]
      ring
    have h_max_ge : 0 ≤ max ((m : ℝ) / (n : ℝ)) (V (m + 1)) - V (m + 1) :=
      sub_nonneg.mpr (le_max_right _ _)
    have h_nonneg : 0 ≤ V m - V (m + 1) := by
      rw [h_diff]
      positivity
    linarith

  have hV_antitone : ∀ m₁ m₂ : ℕ, 1 ≤ m₁ → m₁ ≤ m₂ → m₂ ≤ n + 1 → V m₂ ≤ V m₁ := by
    intro m₁ m₂ hm₁ hm₁₂
    induction m₂, hm₁₂ using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ m₂ hm₁₂ ih =>
      intro hm₂_hi
      exact le_trans (hV_mono_step m₂ (by omega) (by omega)) (ih (by omega))

  let P_cut : ℕ → Prop := fun m => 1 ≤ m ∧ m ≤ n ∧ V (m + 1) ≤ (m : ℝ) / (n : ℝ)
  let dec_cut : DecidablePred P_cut := Classical.decPred P_cut
  have hex_cut : ∃ m : ℕ, P_cut m := by
    refine ⟨n, hn, le_rfl, ?_⟩
    rw [hV_end]
    positivity

  let m_star : ℕ := @Nat.find P_cut dec_cut hex_cut
  obtain ⟨hm_star_ge1, hm_star_le_n, hm_star_cut⟩ := @Nat.find_spec P_cut dec_cut hex_cut

  have hV_below : ∀ m : ℕ, 1 ≤ m → m < m_star → V m = V (m + 1) := by
    intro m hm1 hm_lt
    have hmn : m ≤ n := by omega
    have h_not : ¬ P_cut m := @Nat.find_min P_cut dec_cut hex_cut m hm_lt
    have h_not_le : ¬ (V (m + 1) ≤ (m : ℝ) / (n : ℝ)) := fun hle => h_not ⟨hm1, hmn, hle⟩
    have h_gt : (m : ℝ) / (n : ℝ) ≤ V (m + 1) := le_of_not_ge h_not_le
    have hm_ne : (m : ℝ) ≠ 0 := by positivity
    rw [hV_step m hm1 hmn, max_eq_right h_gt]
    field_simp [hm_ne]
    ring

  have hV1_eq_mstar : V 1 = V m_star := by
    have h_ind : ∀ t : ℕ, t < m_star → V 1 = V (t + 1) := by
      intro t
      induction t with
      | zero => intro _; rfl
      | succ t ih =>
        intro ht
        rw [ih (by omega), hV_below (t + 1) (by omega) ht]
    have h := h_ind (m_star - 1) (by omega)
    have heq : m_star - 1 + 1 = m_star := by omega
    rwa [heq] at h

  have hV_above : ∀ m : ℕ, m_star ≤ m → m ≤ n →
      V m = 1 / (n : ℝ) + (((m : ℝ) - 1) / (m : ℝ)) * V (m + 1) := by
    intro m hm_lo hmn
    have hm1 : 1 ≤ m := by omega
    have hm_ne : (m : ℝ) ≠ 0 := by positivity
    have h_le1 : V (m + 1) ≤ V (m_star + 1) :=
      hV_antitone (m_star + 1) (m + 1) (by omega) (by omega) (by omega)
    have h_le2 : (m_star : ℝ) / (n : ℝ) ≤ (m : ℝ) / (n : ℝ) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hn_pos)
      exact_mod_cast hm_lo
    have h_cut_m : V (m + 1) ≤ (m : ℝ) / (n : ℝ) := le_trans h_le1 (le_trans hm_star_cut h_le2)
    rw [hV_step m hm1 hmn, max_eq_left h_cut_m]
    congr 1
    field_simp [hm_ne, hn_ne]

  have h_invE_pos : 0 < invE := Real.exp_pos (-1)

  have hV1_bound : V 1 ≤ invE + 1 / (n : ℝ) := by
    by_cases hm_case : m_star = 1
    · have h1 := hV_above 1 (by omega) hn
      push_cast at h1
      have h1' : V 1 = 1 / (n : ℝ) := by rw [h1]; ring
      linarith
    · have hm2 : 2 ≤ m_star := by omega
      let s : ℕ := m_star - 1
      have hs1 : 1 ≤ s := by omega
      have hs_lt_n : s < n := by omega
      have hm_eq : m_star = s + 1 := by omega
      have hs_pos : 0 < (s : ℝ) := by positivity
      have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs_pos
      let g_harm : ℕ → ℝ := fun t => V (s + t + 1) / ((s + t : ℕ) : ℝ)
      have hg_diff : ∀ t ∈ Finset.range (n - s),
          g_harm t - g_harm (t + 1) = (1 / (n : ℝ)) * (1 / ((s + t : ℕ) : ℝ)) := by
        intro t ht
        have ht_lt : t < n - s := Finset.mem_range.mp ht
        let j : ℕ := s + t
        have hj1 : 1 ≤ j := by omega
        have hj_pos : 0 < (j : ℝ) := by positivity
        have hj_ne : (j : ℝ) ≠ 0 := ne_of_gt hj_pos
        have hj1_ne : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        have h_rec_j := hV_above (j + 1) (by omega) (by omega)
        have heq1 : s + (t + 1) + 1 = j + 2 := by omega
        have heq2 : s + (t + 1) = j + 1 := by omega
        dsimp [g_harm]
        rw [heq1, heq2]
        change V (j + 1) / (j : ℝ) - V (j + 2) / ((j + 1 : ℕ) : ℝ) =
          (1 / (n : ℝ)) * (1 / (j : ℝ))
        rw [h_rec_j]
        push_cast
        field_simp [hj_ne, hn_ne]
        ring
      have h_tel_harm :
          V 1 / (s : ℝ) =
            (1 / (n : ℝ)) * ∑ t ∈ Finset.range (n - s), (1 / ((s + t : ℕ) : ℝ)) := by
        have h1 : ∑ t ∈ Finset.range (n - s), (g_harm t - g_harm (t + 1)) =
            (1 / (n : ℝ)) * ∑ t ∈ Finset.range (n - s), (1 / ((s + t : ℕ) : ℝ)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl hg_diff
        rw [Finset.sum_range_sub' g_harm (n - s)] at h1
        have hg0 : g_harm 0 = V 1 / (s : ℝ) := by
          dsimp [g_harm]
          rw [Nat.add_zero, ← hm_eq, ← hV1_eq_mstar]
        have hgn : g_harm (n - s) = 0 := by
          dsimp [g_harm]
          have hsn : s + (n - s) = n := by omega
          rw [hsn, hV_end, zero_div]
        rw [hg0, hgn, sub_zero] at h1
        exact h1
      let K : ℕ := n - (s + 1)
      have hns_eq : n - s = K + 1 := by omega
      have h_peel :
          ∑ t ∈ Finset.range (n - s), (1 / ((s + t : ℕ) : ℝ)) =
            1 / (s : ℝ) + ∑ t ∈ Finset.range K, (1 / ((s + (t + 1) : ℕ) : ℝ)) := by
        rw [hns_eq, Finset.sum_range_succ']
        simp [add_comm]
      have h_log_term : ∀ t ∈ Finset.range K,
          1 / ((s + (t + 1) : ℕ) : ℝ) ≤
            Real.log ((s + (t + 1) : ℕ) : ℝ) - Real.log ((s + t : ℕ) : ℝ) := by
        intro t _
        let a : ℕ := s + t
        have ha_pos : 0 < (a : ℝ) := by positivity
        have ha1_pos : 0 < ((a + 1 : ℕ) : ℝ) := by positivity
        have h_log := Real.log_le_sub_one_of_pos (div_pos ha_pos ha1_pos)
        rw [Real.log_div (ne_of_gt ha_pos) (ne_of_gt ha1_pos)] at h_log
        have h_alg : (a : ℝ) / ((a + 1 : ℕ) : ℝ) - 1 = - (1 / ((a + 1 : ℕ) : ℝ)) := by
          push_cast
          field_simp [ne_of_gt ha1_pos]
          ring
        rw [h_alg] at h_log
        have heq : s + (t + 1) = a + 1 := by omega
        rw [heq]
        change 1 / ((a + 1 : ℕ) : ℝ) ≤ Real.log ((a + 1 : ℕ) : ℝ) - Real.log (a : ℝ)
        linarith
      have h_log_sum :
          ∑ t ∈ Finset.range K, (1 / ((s + (t + 1) : ℕ) : ℝ)) ≤
            Real.log ((n : ℝ) / (s : ℝ)) := by
        calc ∑ t ∈ Finset.range K, (1 / ((s + (t + 1) : ℕ) : ℝ))
            ≤ ∑ t ∈ Finset.range K,
                (Real.log ((s + (t + 1) : ℕ) : ℝ) - Real.log ((s + t : ℕ) : ℝ)) :=
              Finset.sum_le_sum h_log_term
          _ = Real.log ((s + K : ℕ) : ℝ) - Real.log ((s + 0 : ℕ) : ℝ) :=
              Finset.sum_range_sub (fun t => Real.log ((s + t : ℕ) : ℝ)) K
          _ ≤ Real.log (n : ℝ) - Real.log (s : ℝ) := by
              rw [Nat.add_zero]
              have hsK : s + K = n - 1 := by omega
              rw [hsK]
              have hn1_pos : 0 < ((n - 1 : ℕ) : ℝ) := by
                have : 1 ≤ n - 1 := by omega
                positivity
              have hn1_le : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : n - 1 ≤ n)
              linarith [Real.log_le_log hn1_pos hn1_le]
          _ = Real.log ((n : ℝ) / (s : ℝ)) :=
              (Real.log_div hn_ne hs_ne).symm
      have hV1_log : V 1 ≤ 1 / (n : ℝ) + ((s : ℝ) / (n : ℝ)) * Real.log ((n : ℝ) / (s : ℝ)) := by
        have hV1_eq : V 1 = ((s : ℝ) / (n : ℝ)) *
            (1 / (s : ℝ) + ∑ t ∈ Finset.range K, (1 / ((s + (t + 1) : ℕ) : ℝ))) := by
          have hmul := congrArg (fun z : ℝ => (s : ℝ) * z) h_tel_harm
          dsimp at hmul
          rw [h_peel] at hmul
          have h_lhs_c : (s : ℝ) * (V 1 / (s : ℝ)) = V 1 := mul_div_cancel₀ _ hs_ne
          rw [h_lhs_c] at hmul
          rw [hmul]
          ring
        rw [hV1_eq]
        have h_sn_pos : 0 ≤ (s : ℝ) / (n : ℝ) := by positivity
        have h_mul := mul_le_mul_of_nonneg_left (add_le_add_left h_log_sum (1 / (s : ℝ))) h_sn_pos
        have h_id : ((s : ℝ) / (n : ℝ)) * (1 / (s : ℝ) + Real.log ((n : ℝ) / (s : ℝ))) =
            1 / (n : ℝ) + ((s : ℝ) / (n : ℝ)) * Real.log ((n : ℝ) / (s : ℝ)) := by
          field_simp [hs_ne, hn_ne]
        linarith
      have h_e_bound : ((s : ℝ) / (n : ℝ)) * Real.log ((n : ℝ) / (s : ℝ)) ≤ invE := by
        have h_ns_pos : 0 < (n : ℝ) / (s : ℝ) := div_pos hn_pos hs_pos
        have h_prod_pos : 0 < invE * ((n : ℝ) / (s : ℝ)) := mul_pos h_invE_pos h_ns_pos
        have h_log := Real.log_le_sub_one_of_pos h_prod_pos
        rw [Real.log_mul (ne_of_gt h_invE_pos) (ne_of_gt h_ns_pos)] at h_log
        have h_log_invE : Real.log invE = -1 := Real.log_exp (-1)
        rw [h_log_invE] at h_log
        have h_le : Real.log ((n : ℝ) / (s : ℝ)) ≤ invE * ((n : ℝ) / (s : ℝ)) := by linarith
        have h_mul := mul_le_mul_of_nonneg_left h_le (by positivity : 0 ≤ (s : ℝ) / (n : ℝ))
        have h_id : ((s : ℝ) / (n : ℝ)) * (invE * ((n : ℝ) / (s : ℝ))) = invE := by
          field_simp [hs_ne, hn_ne]
        linarith
      linarith

  exact le_trans h_lhs_le_V1 hV1_bound

theorem rel_order_perm_factorization (m N : ℕ) (u₁ u₂ : Fin m → Fin N)
    (hu₁ : Function.Injective u₁) (hu₂ : Function.Injective u₂)
    (hrel : ∀ i j : Fin m, u₁ i ≤ u₁ j ↔ u₂ i ≤ u₂ j) :
    ∃ (hT₁ : (Finset.univ.image u₁).card = m)
      (hT₂ : (Finset.univ.image u₂).card = m)
      (τ : Equiv.Perm (Fin m)),
      (∀ i : Fin m, ((Finset.univ.image u₁).orderEmbOfFin hT₁) (τ i) = u₁ i) ∧
      (∀ i : Fin m, ((Finset.univ.image u₂).orderEmbOfFin hT₂) (τ i) = u₂ i) :=
by
  let T₁ : Finset (Fin N) := Finset.univ.image u₁
  let T₂ : Finset (Fin N) := Finset.univ.image u₂
  have hT₁ : T₁.card = m :=
    (Finset.card_image_of_injective Finset.univ hu₁).trans (Finset.card_fin m)
  have hT₂ : T₂.card = m :=
    (Finset.card_image_of_injective Finset.univ hu₂).trans (Finset.card_fin m)
  let u₁_sub : Fin m → ↥T₁ :=
    fun i => ⟨u₁ i, Finset.mem_image_of_mem u₁ (Finset.mem_univ i)⟩
  have hu₁_bij : Function.Bijective u₁_sub := by
    refine ⟨?_, ?_⟩
    · intro i j hij
      exact hu₁ (Subtype.ext_iff.mp hij)
    · rintro ⟨v, hv⟩
      rcases Finset.mem_image.mp hv with ⟨i, _, rfl⟩
      exact ⟨i, rfl⟩
  let eu₁ : Fin m ≃ ↥T₁ := Equiv.ofBijective u₁_sub hu₁_bij
  let iso₁ : Fin m ≃o ↥T₁ := T₁.orderIsoOfFin hT₁
  let τ : Equiv.Perm (Fin m) := eu₁.trans iso₁.symm.toEquiv
  have hτ₁ : ∀ i : Fin m, (T₁.orderEmbOfFin hT₁) (τ i) = u₁ i := by
    intro i
    rw [← Finset.coe_orderIsoOfFin_apply T₁ hT₁ (τ i)]
    change ↑(iso₁ (iso₁.symm (eu₁ i))) = u₁ i
    rw [iso₁.apply_symm_apply, Equiv.ofBijective_apply]
  have hrel_lt : ∀ i j : Fin m, u₁ i < u₁ j ↔ u₂ i < u₂ j := by
    intro i j
    rw [lt_iff_le_not_ge, lt_iff_le_not_ge, hrel i j, hrel j i]
  let f : Fin m → Fin N := fun a => u₂ (τ.symm a)
  have hf_mem : ∀ a : Fin m, f a ∈ T₂ :=
    fun a => Finset.mem_image_of_mem u₂ (Finset.mem_univ (τ.symm a))
  have hf_strict : StrictMono f := by
    intro a b hab
    have hτ_lt : τ (τ.symm a) < τ (τ.symm b) := by
      simpa only [Equiv.apply_symm_apply] using hab
    have he₁_lt : (T₁.orderEmbOfFin hT₁) (τ (τ.symm a)) < (T₁.orderEmbOfFin hT₁) (τ (τ.symm b)) :=
      (T₁.orderEmbOfFin hT₁).strictMono hτ_lt
    rw [hτ₁ (τ.symm a), hτ₁ (τ.symm b), hrel_lt] at he₁_lt
    exact he₁_lt
  have hf_eq : f = ⇑(T₂.orderEmbOfFin hT₂) :=
    Finset.orderEmbOfFin_unique hT₂ hf_mem hf_strict
  have hτ₂ : ∀ i : Fin m, (T₂.orderEmbOfFin hT₂) (τ i) = u₂ i := by
    intro i
    have h := congrFun hf_eq.symm (τ i)
    dsimp only [f] at h
    rw [Equiv.symm_apply_apply] at h
    exact h
  exact ⟨hT₁, hT₂, τ, hτ₁, hτ₂⟩

theorem online_alg_stopping_reduction (n : ℕ) (hn : 1 ≤ n)
    (valOf : (Fin n → ℝ) → ItemValuation n)
    (h_loc : ∀ (w₁ w₂ : Fin n → ℝ) (S : Finset (Fin n)),
      (∀ g ∈ S, w₁ g = w₂ g) → valOf w₁ S = valOf w₂ S)
    (alg : OnlineSelectionAlg n) :
    ∃ p : (m : ℕ) → (Fin m → ℝ) → ℝ,
      (∀ (m : ℕ) (z : Fin m → ℝ), 0 ≤ p m z ∧ p m z ≤ 1) ∧
      (∀ Z : Fin n → ℝ,
        ∑ k : Fin n,
          p (k.1 + 1) (fun i : Fin (k.1 + 1) => Z ⟨i.1, Nat.lt_of_lt_of_le i.2 k.2⟩) ≤ 1) ∧
      (∀ w₀ : Fin n → ℝ,
        (∀ j : Fin n, 0 ≤ w₀ j) →
        (∀ σ : Equiv.Perm (Fin n),
          realVal (valOf (w₀ ∘ σ)) ∅ ≤ 0 ∧
          (∀ g : Fin n, realVal (valOf (w₀ ∘ σ)) {g} ≤ w₀ (σ g)) ∧
          (∀ S : Finset (Fin n), 2 ≤ S.card → realVal (valOf (w₀ ∘ σ)) S ≤ 0)) →
        ∃ σ : Equiv.Perm (Fin n),
          expectedSelectionVal alg (valOf (w₀ ∘ σ)) ≤
            (((1 / (Nat.factorial n : ℝ)) *
              ∑ ρ : Equiv.Perm (Fin n),
                ∑ k : Fin n,
                  w₀ (ρ k) *
                    p (k.1 + 1)
                      (fun i : Fin (k.1 + 1) => w₀ (ρ ⟨i.1, Nat.lt_of_lt_of_le i.2 k.2⟩)) : ℝ) :
              WithBot ℝ)) :=
by
  have _ := hn
  
  let arrivalPrefix : Equiv.Perm (Fin n) → (j : ℕ) → j ≤ n → List (Fin n) :=
    fun π j hj => List.ofFn (fun i : Fin j => π ⟨i.1, Nat.lt_of_lt_of_le i.2 hj⟩)
  have h_fst_eq : ∀ (dalg : DetSelectionAlg n) (v : ItemValuation n) (π : Equiv.Perm (Fin n))
      (j : ℕ) (hj : j ≤ n),
      (runDetSelectionSteps dalg v π j hj).1 = arrivalPrefix π j hj := by
    intro dalg v π j
    induction j with
    | zero =>
      intro hj
      simp [runDetSelectionSteps, arrivalPrefix]
    | succ j ih =>
      intro hj
      have hj' : j ≤ n := Nat.le_of_succ_le hj
      have h1 : (runDetSelectionSteps dalg v π (j + 1) hj).1 =
          (runDetSelectionSteps dalg v π j hj').1 ++ [π ⟨j, hj⟩] := rfl
      rw [h1, ih hj']
      dsimp only [arrivalPrefix]
      rw [List.ofFn_succ', List.concat_eq_append]
      rfl

  have h_step_snd : ∀ (dalg : DetSelectionAlg n) (v : ItemValuation n) (π : Equiv.Perm (Fin n))
      (j : ℕ) (hj : j + 1 ≤ n),
      (runDetSelectionSteps dalg v π (j + 1) hj).2 =
        if dalg.step (arrivalPrefix π j (Nat.le_of_succ_le hj)) (π ⟨j, hj⟩)
            (runDetSelectionSteps dalg v π j (Nat.le_of_succ_le hj)).2 (fun ⟨T, _⟩ => v T)
        then insert (π ⟨j, hj⟩) (runDetSelectionSteps dalg v π j (Nat.le_of_succ_le hj)).2
        else (runDetSelectionSteps dalg v π j (Nat.le_of_succ_le hj)).2 := by
    intro dalg v π j hj
    let hj' : j ≤ n := Nat.le_of_succ_le hj
    let x := π ⟨j, hj⟩
    let acc := (runDetSelectionSteps dalg v π j hj').2
    have hdec : dalg.step (runDetSelectionSteps dalg v π j hj').1 x acc (fun ⟨T, _⟩ => v T) =
        dalg.step (arrivalPrefix π j hj') x acc (fun ⟨T, _⟩ => v T) :=
      congrArg (fun p : List (Fin n) => dalg.step p x acc (fun ⟨T, _⟩ => v T))
        (h_fst_eq dalg v π j hj')
    change (if dalg.step (runDetSelectionSteps dalg v π j hj').1 x acc (fun ⟨T, _⟩ => v T)
      then insert x acc else acc) = _
    rw [hdec]

  have h_mem_prefix : ∀ (π : Equiv.Perm (Fin n)) (j : ℕ) (hj : j ≤ n) (g : Fin n),
      g ∈ (arrivalPrefix π j hj).toFinset ↔ (π.symm g).1 < j := by
    intro π j hj g
    simp only [arrivalPrefix, List.mem_toFinset, List.mem_ofFn]
    constructor
    · rintro ⟨i, rfl⟩
      simp only [Equiv.symm_apply_apply]
      exact i.2
    · intro hlt
      refine ⟨⟨(π.symm g).1, hlt⟩, ?_⟩
      have hfin : (⟨(π.symm g).1, Nat.lt_of_lt_of_le hlt hj⟩ : Fin n) = π.symm g :=
        Fin.ext rfl
      rw [hfin, Equiv.apply_symm_apply]

  have h_acc_congr : ∀ (dalg : DetSelectionAlg n) (v : ItemValuation n) (π : Equiv.Perm (Fin n))
      (j₁ j₂ : ℕ) (h₁ : j₁ ≤ n) (h₂ : j₂ ≤ n),
      j₁ = j₂ → (runDetSelectionSteps dalg v π j₁ h₁).2 = (runDetSelectionSteps dalg v π j₂ h₂).2 := by
    rintro dalg v π j₁ _ h₁ h₂ rfl
    rfl

  
  have h_acc_lt : ∀ (dalg : DetSelectionAlg n) (v : ItemValuation n) (π : Equiv.Perm (Fin n))
      (j : ℕ) (hj : j ≤ n) (g : Fin n),
      g ∈ (runDetSelectionSteps dalg v π j hj).2 → (π.symm g).1 < j := by
    intro dalg v π j
    induction j with
    | zero =>
      intro hj g hg
      simp [runDetSelectionSteps] at hg
    | succ j ih =>
      intro hj g hg
      rw [h_step_snd dalg v π j hj] at hg
      split_ifs at hg
      · rcases Finset.mem_insert.mp hg with rfl | hg'
        · simp only [Equiv.symm_apply_apply]
          omega
        · have := ih (Nat.le_of_succ_le hj) g hg'
          omega
      · have := ih (Nat.le_of_succ_le hj) g hg
        omega

  have h_acc_mono : ∀ (dalg : DetSelectionAlg n) (v : ItemValuation n) (π : Equiv.Perm (Fin n))
      (j₁ j₂ : ℕ) (hj₁₂ : j₁ ≤ j₂) (hj₂ : j₂ ≤ n),
      (runDetSelectionSteps dalg v π j₁ (le_trans hj₁₂ hj₂)).2 ⊆
        (runDetSelectionSteps dalg v π j₂ hj₂).2 := by
    intro dalg v π j₁ j₂
    induction j₂ with
    | zero =>
      intro hj₁₂ hj₂
      have hj₁ : j₁ = 0 := by omega
      rw [h_acc_congr dalg v π j₁ 0 _ hj₂ hj₁]
    | succ m ih =>
      intro hj₁₂ hj₂
      by_cases h_eq : j₁ = m + 1
      · rw [h_acc_congr dalg v π j₁ (m + 1) _ hj₂ h_eq]
      · have hj₁m : j₁ ≤ m := by omega
        have hm : m ≤ n := Nat.le_of_succ_le hj₂
        have hsub1 : (runDetSelectionSteps dalg v π j₁ (le_trans hj₁₂ hj₂)).2 ⊆
            (runDetSelectionSteps dalg v π m hm).2 := by
          rw [h_acc_congr dalg v π j₁ j₁ (le_trans hj₁₂ hj₂) (le_trans hj₁m hm) rfl]
          exact ih hj₁m hm
        have hsub2 : (runDetSelectionSteps dalg v π m hm).2 ⊆
            (runDetSelectionSteps dalg v π (m + 1) hj₂).2 := by
          rw [h_step_snd dalg v π m hj₂]
          split_ifs
          · exact Finset.subset_insert _ _
          · exact fun _ h => h
        exact fun _ h => hsub2 (hsub1 h)

  have h_acc_persist : ∀ (dalg : DetSelectionAlg n) (v : ItemValuation n) (π : Equiv.Perm (Fin n))
      (g : Fin n) (j : ℕ) (hkj : (π.symm g).1 + 1 ≤ j) (hj : j ≤ n),
      g ∈ (runDetSelectionSteps dalg v π j hj).2 ↔
        g ∈ (runDetSelectionSteps dalg v π ((π.symm g).1 + 1) (π.symm g).2).2 := by
    intro dalg v π g j
    induction j with
    | zero =>
      intro hkj
      omega
    | succ m ih =>
      intro hkj hj
      by_cases h_eq : m + 1 = (π.symm g).1 + 1
      · rw [h_acc_congr dalg v π (m + 1) ((π.symm g).1 + 1) hj (π.symm g).2 h_eq]
      · have hkm : (π.symm g).1 + 1 ≤ m := by omega
        have hm : m ≤ n := Nat.le_of_succ_le hj
        have hne : g ≠ π ⟨m, hj⟩ := by
          intro h_eq_g
          have hsymm : π.symm g = ⟨m, hj⟩ := by
            rw [h_eq_g, Equiv.symm_apply_apply]
          have hval : (π.symm g).1 = m := congrArg Fin.val hsymm
          omega
        rw [h_step_snd dalg v π m hj]
        split_ifs
        · simp only [Finset.mem_insert, hne, false_or]
          exact ih hkm hm
        · exact ih hkm hm

  
  let DetFirstAccepts : DetSelectionAlg n → ItemValuation n → Equiv.Perm (Fin n) → Fin n → Prop :=
    fun dalg v π k =>
      (runDetSelectionSteps dalg v π k.1 (Nat.le_of_lt k.2)).2 = ∅ ∧
      (runDetSelectionSteps dalg v π (k.1 + 1) k.2).2 ≠ ∅

  have h_dfa_unique : ∀ (dalg : DetSelectionAlg n) (v : ItemValuation n) (π : Equiv.Perm (Fin n))
      (k₁ k₂ : Fin n),
      DetFirstAccepts dalg v π k₁ → DetFirstAccepts dalg v π k₂ → k₁ = k₂ := by
    intro dalg v π k₁ k₂ hk₁ hk₂
    by_contra hne
    have hne_val : k₁.1 ≠ k₂.1 := fun h => hne (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hne_val with hlt | hgt
    · have hle : k₁.1 + 1 ≤ k₂.1 := hlt
      have hsub := h_acc_mono dalg v π (k₁.1 + 1) k₂.1 hle (Nat.le_of_lt k₂.2)
      rw [h_acc_congr dalg v π (k₁.1 + 1) (k₁.1 + 1) _ k₁.2 rfl, hk₂.1] at hsub
      exact hk₁.2 (Finset.subset_empty.mp hsub)
    · have hle : k₂.1 + 1 ≤ k₁.1 := hgt
      have hsub := h_acc_mono dalg v π (k₂.1 + 1) k₁.1 hle (Nat.le_of_lt k₁.2)
      rw [h_acc_congr dalg v π (k₂.1 + 1) (k₂.1 + 1) _ k₂.2 rfl, hk₁.1] at hsub
      exact hk₂.2 (Finset.subset_empty.mp hsub)

  have h_singleton_imp_dfa : ∀ (dalg : DetSelectionAlg n) (v : ItemValuation n)
      (π : Equiv.Perm (Fin n)) (g : Fin n),
      runDetSelection dalg v π = {g} → DetFirstAccepts dalg v π (π.symm g) := by
    intro dalg v π g hrun
    refine ⟨?_, ?_⟩
    · apply Finset.eq_empty_of_forall_notMem
      intro y hy
      have hsub := h_acc_mono dalg v π (π.symm g).1 n (Nat.le_of_lt (π.symm g).2) (le_refl n)
      have hy_final : y ∈ runDetSelection dalg v π := hsub hy
      rw [hrun, Finset.mem_singleton] at hy_final
      subst hy_final
      have hlt := h_acc_lt dalg v π (π.symm y).1 (Nat.le_of_lt (π.symm y).2) y hy
      omega
    · intro hemp
      have hg_final : g ∈ (runDetSelectionSteps dalg v π n (le_refl n)).2 := by
        change g ∈ runDetSelection dalg v π
        rw [hrun]
        exact Finset.mem_singleton_self g
      have hg_acc := (h_acc_persist dalg v π g n (π.symm g).2 (le_refl n)).mp hg_final
      rw [hemp] at hg_acc
      simp at hg_acc

  have h_acc_loc : ∀ (dalg : DetSelectionAlg n) (v₁ v₂ : ItemValuation n)
      (π : Equiv.Perm (Fin n)) (m : ℕ) (hm : m ≤ n),
      (∀ S : Finset (Fin n), (∀ g ∈ S, (π.symm g).1 < m) → v₁ S = v₂ S) →
      ∀ (j : ℕ) (hj : j ≤ m),
        (runDetSelectionSteps dalg v₁ π j (le_trans hj hm)).2 =
          (runDetSelectionSteps dalg v₂ π j (le_trans hj hm)).2 := by
    intro dalg v₁ v₂ π m hm hv j
    induction j with
    | zero =>
      intro _
      rfl
    | succ j ih =>
      intro hj
      have hj' : j ≤ m := Nat.le_of_succ_le hj
      have hjn : j + 1 ≤ n := le_trans hj hm
      rw [h_step_snd dalg v₁ π j hjn, h_step_snd dalg v₂ π j hjn]
      have hacc_eq : (runDetSelectionSteps dalg v₁ π j (Nat.le_of_succ_le hjn)).2 =
          (runDetSelectionSteps dalg v₂ π j (Nat.le_of_succ_le hjn)).2 := by
        rw [h_acc_congr dalg v₁ π j j _ (le_trans hj' hm) rfl,
            h_acc_congr dalg v₂ π j j _ (le_trans hj' hm) rfl]
        exact ih hj'
      have horacle_eq :
          ((fun ⟨T, _⟩ => v₁ T) : {T : Finset (Fin n) //
              T ⊆ insert (π ⟨j, hjn⟩) (arrivalPrefix π j (Nat.le_of_succ_le hjn)).toFinset} →
            WithBot ℝ) =
          (fun ⟨T, _⟩ => v₂ T) := by
        funext ⟨T, hT⟩
        apply hv T
        intro g hg
        have hg' := hT hg
        rcases Finset.mem_insert.mp hg' with rfl | hg_pref
        · simp only [Equiv.symm_apply_apply]
          omega
        · have hlt := (h_mem_prefix π j (Nat.le_of_succ_le hjn) g).mp hg_pref
          omega
      rw [hacc_eq, horacle_eq]

  have h_dfa_loc : ∀ (dalg : DetSelectionAlg n) (v₁ v₂ : ItemValuation n)
      (π : Equiv.Perm (Fin n)) (k : Fin n),
      (∀ S : Finset (Fin n), (∀ g ∈ S, (π.symm g).1 < k.1 + 1) → v₁ S = v₂ S) →
      (DetFirstAccepts dalg v₁ π k ↔ DetFirstAccepts dalg v₂ π k) := by
    intro dalg v₁ v₂ π k hv
    have heq0 : (runDetSelectionSteps dalg v₁ π k.1 (Nat.le_of_lt k.2)).2 =
        (runDetSelectionSteps dalg v₂ π k.1 (Nat.le_of_lt k.2)).2 := by
      have := h_acc_loc dalg v₁ v₂ π (k.1 + 1) k.2 hv k.1 (Nat.le_succ k.1)
      simpa using this
    have heq1 : (runDetSelectionSteps dalg v₁ π (k.1 + 1) k.2).2 =
        (runDetSelectionSteps dalg v₂ π (k.1 + 1) k.2).2 := by
      have := h_acc_loc dalg v₁ v₂ π (k.1 + 1) k.2 hv (k.1 + 1) (le_refl _)
      simpa using this
    dsimp only [DetFirstAccepts]
    rw [heq0, heq1]

  
  have h_meas_acc : ∀ (v : ItemValuation n) (π : Equiv.Perm (Fin n))
      (j : ℕ) (hj : j ≤ n) (B : Finset (Fin n)),
      MeasurableSet {ω : alg.Seed | (runDetSelectionSteps (alg.det ω) v π j hj).2 = B} := by
    intro v π j
    induction j with
    | zero =>
      intro hj B
      by_cases hB : B = ∅
      · subst hB
        have h_univ : {ω : alg.Seed | (runDetSelectionSteps (alg.det ω) v π 0 hj).2 = ∅} =
            Set.univ := by
          ext ω
          simp [runDetSelectionSteps]
        rw [h_univ]
        exact MeasurableSet.univ
      · have h_emp : {ω : alg.Seed | (runDetSelectionSteps (alg.det ω) v π 0 hj).2 = B} = ∅ := by
          ext ω
          simp [runDetSelectionSteps, Ne.symm hB]
        rw [h_emp]
        exact MeasurableSet.empty
    | succ j ih =>
      intro hj B
      let hj' : j ≤ n := Nat.le_of_succ_le hj
      let prev := arrivalPrefix π j hj'
      let x := π ⟨j, hj⟩
      let oracle : {T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → WithBot ℝ :=
        fun ⟨T, _⟩ => v T
      let cand : Finset (Finset (Fin n) × Bool) :=
        Finset.univ.filter (fun q => (if q.2 then insert x q.1 else q.1) = B)
      have hset_eq :
          {ω : alg.Seed | (runDetSelectionSteps (alg.det ω) v π (j + 1) hj).2 = B} =
          ⋃ q ∈ cand,
            ({ω : alg.Seed | (runDetSelectionSteps (alg.det ω) v π j hj').2 = q.1} ∩
             {ω : alg.Seed | (alg.det ω).step prev x q.1 oracle = q.2}) := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, cand,
          Finset.mem_filter, Finset.mem_univ, true_and]
        rw [h_step_snd (alg.det ω) v π j hj]
        constructor
        · intro hB
          refine ⟨((runDetSelectionSteps (alg.det ω) v π j hj').2,
            (alg.det ω).step prev x (runDetSelectionSteps (alg.det ω) v π j hj').2 oracle),
            hB, rfl, rfl⟩
        · rintro ⟨⟨A, b⟩, hB, hA, hb⟩
          dsimp only at hB hA hb
          rw [hA]
          change (if (alg.det ω).step prev x A oracle then insert x A else A) = B
          rw [hb]
          exact hB
      rw [hset_eq]
      refine Finset.measurableSet_biUnion cand (fun q _ => ?_)
      exact (ih hj' q.1).inter (alg.meas_step prev x q.1 oracle q.2)

  have h_dfa_sum_le_one : ∀ (v : ItemValuation n) (π : Equiv.Perm (Fin n)),
      ∑ k : Fin n, alg.seedMeasure.real {ω : alg.Seed | DetFirstAccepts (alg.det ω) v π k} ≤ 1 := by
    intro v π
    let E : Fin n → Set alg.Seed := fun k => {ω : alg.Seed | DetFirstAccepts (alg.det ω) v π k}
    have hdisj : Pairwise (Function.onFun Disjoint E) := by
      intro k₁ k₂ hne
      rw [Function.onFun, Set.disjoint_left]
      intro ω h₁ h₂
      exact hne (h_dfa_unique (alg.det ω) v π k₁ k₂ h₁ h₂)
    have hmeas : ∀ k : Fin n, MeasurableSet (E k) := by
      intro k
      have hE : E k =
          {ω : alg.Seed | (runDetSelectionSteps (alg.det ω) v π k.1 (Nat.le_of_lt k.2)).2 = ∅} ∩
          ({ω : alg.Seed | (runDetSelectionSteps (alg.det ω) v π (k.1 + 1) k.2).2 = ∅})ᶜ := by
        ext ω
        simp [E, DetFirstAccepts]
      rw [hE]
      exact (h_meas_acc v π k.1 (Nat.le_of_lt k.2) ∅).inter
        (h_meas_acc v π (k.1 + 1) k.2 ∅).compl
    calc ∑ k : Fin n, alg.seedMeasure.real (E k)
        = alg.seedMeasure.real (⋃ k : Fin n, E k) :=
          (MeasureTheory.measureReal_iUnion_fintype hdisj hmeas).symm
      _ ≤ alg.seedMeasure.real Set.univ :=
          MeasureTheory.measureReal_mono (Set.subset_univ _)
      _ = 1 := MeasureTheory.probReal_univ

  
  have h_fact_pos : 0 < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h_fact_ne : (Nat.factorial n : ℝ) ≠ 0 := ne_of_gt h_fact_pos
  have h_card_perm : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) = (Nat.factorial n : ℝ) := by
    rw [Fintype.card_perm, Fintype.card_fin]

  have h_exp_le_sing : ∀ (v : ItemValuation n) (u : Fin n → ℝ),
      realVal v ∅ ≤ 0 →
      (∀ g : Fin n, realVal v {g} ≤ u g) →
      (∀ S : Finset (Fin n), 2 ≤ S.card → realVal v S ≤ 0) →
      expectedSelectionVal alg v ≤ ((∑ g : Fin n, algSelectionProb alg v {g} * u g : ℝ) : WithBot ℝ) := by
    intro v u h_emp h_sing h_multi
    have hprob_nonneg : ∀ S : Finset (Fin n), 0 ≤ algSelectionProb alg v S := by
      intro S
      unfold algSelectionProb
      apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg (fun π _ => MeasureTheory.measureReal_nonneg)
    unfold expectedSelectionVal
    split_ifs with hbot
    · exact bot_le
    · rw [WithBot.coe_le_coe]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun S : Finset (Fin n) => S.card = 1)]
      have h_not_one :
          ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => ¬ S.card = 1),
            algSelectionProb alg v S * realVal v S ≤ 0 := by
        apply Finset.sum_nonpos
        intro S hS
        have hcard_ne : S.card ≠ 1 := (Finset.mem_filter.mp hS).2
        have hrv_nonpos : realVal v S ≤ 0 := by
          by_cases h0 : S.card = 0
          · rw [Finset.card_eq_zero.mp h0]
            exact h_emp
          · exact h_multi S (by omega)
        exact mul_nonpos_of_nonneg_of_nonpos (hprob_nonneg S) hrv_nonpos
      have h_filter_one :
          Finset.univ.filter (fun S : Finset (Fin n) => S.card = 1) =
            (Finset.univ : Finset (Fin n)).image (fun g => ({g} : Finset (Fin n))) := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        rw [Finset.card_eq_one]
        constructor
        · rintro ⟨g, rfl⟩
          exact ⟨g, rfl⟩
        · rintro ⟨g, rfl⟩
          exact ⟨g, rfl⟩
      have h_one :
          ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = 1),
            algSelectionProb alg v S * realVal v S ≤
          ∑ g : Fin n, algSelectionProb alg v {g} * u g := by
        rw [h_filter_one, Finset.sum_image (fun _ _ _ _ h => Finset.singleton_injective h)]
        exact Finset.sum_le_sum (fun g _ =>
          mul_le_mul_of_nonneg_left (h_sing g) (hprob_nonneg {g}))
      linarith

  
  let prefixWeight : (m : ℕ) → (Fin m → ℝ) → Equiv.Perm (Fin n) → (Fin n → ℝ) :=
    fun m z π g => if h : (π.symm g).1 < m then z ⟨(π.symm g).1, h⟩ else 0

  let p : (m : ℕ) → (Fin m → ℝ) → ℝ :=
    fun m z =>
      if h : 1 ≤ m ∧ m ≤ n then
        (1 / (Nat.factorial n : ℝ)) *
          ∑ π : Equiv.Perm (Fin n),
            alg.seedMeasure.real
              {ω : alg.Seed | DetFirstAccepts (alg.det ω) (valOf (prefixWeight m z π)) π
                ⟨m - 1, by omega⟩}
      else 0

  have hp_eval : ∀ (Z : Fin n → ℝ) (k : Fin n),
      p (k.1 + 1) (fun i : Fin (k.1 + 1) => Z ⟨i.1, Nat.lt_of_lt_of_le i.2 k.2⟩) =
        (1 / (Nat.factorial n : ℝ)) *
          ∑ π : Equiv.Perm (Fin n),
            alg.seedMeasure.real
              {ω : alg.Seed | DetFirstAccepts (alg.det ω) (valOf (Z ∘ π.symm)) π k} := by
    intro Z k
    let zk : Fin (k.1 + 1) → ℝ := fun i => Z ⟨i.1, Nat.lt_of_lt_of_le i.2 k.2⟩
    have hk_cond : 1 ≤ k.1 + 1 ∧ k.1 + 1 ≤ n := ⟨by omega, k.2⟩
    dsimp only [p]
    rw [dif_pos hk_cond]
    congr 1
    apply Finset.sum_congr rfl
    intro π _
    have hk_fin : (⟨k.1 + 1 - 1, by omega⟩ : Fin n) = k := Fin.ext (Nat.add_sub_cancel k.1 1)
    rw [hk_fin]
    congr 1
    ext ω
    apply h_dfa_loc (alg.det ω) (valOf (prefixWeight (k.1 + 1) zk π)) (valOf (Z ∘ π.symm)) π k
    intro S hS
    apply h_loc
    intro g hg
    have hlt : (π.symm g).1 < k.1 + 1 := hS g hg
    dsimp only [prefixWeight, zk, Function.comp_apply]
    rw [dif_pos hlt]

  refine ⟨p, ?_, ?_, ?_⟩
  · 
    intro m z
    dsimp only [p]
    split_ifs with h
    · constructor
      · apply mul_nonneg (by positivity)
        exact Finset.sum_nonneg (fun π _ => MeasureTheory.measureReal_nonneg)
      · have hsum_le :
            ∑ π : Equiv.Perm (Fin n),
              alg.seedMeasure.real
                {ω : alg.Seed | DetFirstAccepts (alg.det ω) (valOf (prefixWeight m z π)) π
                  ⟨m - 1, by omega⟩} ≤ (Nat.factorial n : ℝ) := by
          calc ∑ π : Equiv.Perm (Fin n),
                alg.seedMeasure.real
                  {ω : alg.Seed | DetFirstAccepts (alg.det ω) (valOf (prefixWeight m z π)) π
                    ⟨m - 1, by omega⟩}
              ≤ ∑ _π : Equiv.Perm (Fin n), (1 : ℝ) := by
                apply Finset.sum_le_sum
                intro π _
                calc alg.seedMeasure.real _
                    ≤ alg.seedMeasure.real Set.univ :=
                      MeasureTheory.measureReal_mono (Set.subset_univ _)
                  _ = 1 := MeasureTheory.probReal_univ
            _ = (Nat.factorial n : ℝ) := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, h_card_perm, mul_one]
        calc (1 / (Nat.factorial n : ℝ)) * _
            ≤ (1 / (Nat.factorial n : ℝ)) * (Nat.factorial n : ℝ) :=
              mul_le_mul_of_nonneg_left hsum_le (by positivity)
          _ = 1 := one_div_mul_cancel h_fact_ne
    · exact ⟨le_refl 0, zero_le_one⟩

  · 
    intro Z
    have h_rw :
        ∑ k : Fin n, p (k.1 + 1) (fun i : Fin (k.1 + 1) => Z ⟨i.1, Nat.lt_of_lt_of_le i.2 k.2⟩) =
          (1 / (Nat.factorial n : ℝ)) *
            ∑ π : Equiv.Perm (Fin n),
              ∑ k : Fin n,
                alg.seedMeasure.real
                  {ω : alg.Seed | DetFirstAccepts (alg.det ω) (valOf (Z ∘ π.symm)) π k} := by
      calc ∑ k : Fin n,
              p (k.1 + 1) (fun i : Fin (k.1 + 1) => Z ⟨i.1, Nat.lt_of_lt_of_le i.2 k.2⟩)
          = ∑ k : Fin n,
              ((1 / (Nat.factorial n : ℝ)) *
                ∑ π : Equiv.Perm (Fin n),
                  alg.seedMeasure.real
                    {ω : alg.Seed | DetFirstAccepts (alg.det ω) (valOf (Z ∘ π.symm)) π k}) :=
            Finset.sum_congr rfl (fun k _ => hp_eval Z k)
        _ = (1 / (Nat.factorial n : ℝ)) *
              ∑ k : Fin n, ∑ π : Equiv.Perm (Fin n),
                alg.seedMeasure.real
                  {ω : alg.Seed | DetFirstAccepts (alg.det ω) (valOf (Z ∘ π.symm)) π k} := by
            rw [← Finset.mul_sum]
        _ = (1 / (Nat.factorial n : ℝ)) *
              ∑ π : Equiv.Perm (Fin n), ∑ k : Fin n,
                alg.seedMeasure.real
                  {ω : alg.Seed | DetFirstAccepts (alg.det ω) (valOf (Z ∘ π.symm)) π k} := by
            rw [Finset.sum_comm]
    rw [h_rw]
    have hsum_le :
        ∑ π : Equiv.Perm (Fin n), ∑ k : Fin n,
          alg.seedMeasure.real
            {ω : alg.Seed | DetFirstAccepts (alg.det ω) (valOf (Z ∘ π.symm)) π k} ≤
        (Nat.factorial n : ℝ) := by
      calc ∑ π : Equiv.Perm (Fin n), ∑ k : Fin n,
            alg.seedMeasure.real
              {ω : alg.Seed | DetFirstAccepts (alg.det ω) (valOf (Z ∘ π.symm)) π k}
          ≤ ∑ _π : Equiv.Perm (Fin n), (1 : ℝ) :=
            Finset.sum_le_sum (fun π _ => h_dfa_sum_le_one (valOf (Z ∘ π.symm)) π)
        _ = (Nat.factorial n : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, h_card_perm, mul_one]
    calc (1 / (Nat.factorial n : ℝ)) * _
        ≤ (1 / (Nat.factorial n : ℝ)) * (Nat.factorial n : ℝ) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = 1 := one_div_mul_cancel h_fact_ne

  · 
    intro w₀ hw₀ hval
    let RHS : ℝ :=
      (1 / (Nat.factorial n : ℝ)) *
        ∑ ρ : Equiv.Perm (Fin n),
          ∑ k : Fin n,
            w₀ (ρ k) *
              p (k.1 + 1)
                (fun i : Fin (k.1 + 1) => w₀ (ρ ⟨i.1, Nat.lt_of_lt_of_le i.2 k.2⟩))
    let B : Equiv.Perm (Fin n) → ℝ := fun σ =>
      (1 / (Nat.factorial n : ℝ)) *
        ∑ π : Equiv.Perm (Fin n),
          ∑ k : Fin n,
            w₀ (σ (π k)) *
              alg.seedMeasure.real
                {ω : alg.Seed | DetFirstAccepts (alg.det ω) (valOf (w₀ ∘ σ)) π k}

    have h_exp_le_B : ∀ σ : Equiv.Perm (Fin n),
        expectedSelectionVal alg (valOf (w₀ ∘ σ)) ≤ ((B σ : ℝ) : WithBot ℝ) := by
      intro σ
      obtain ⟨h0, h1, h2⟩ := hval σ
      have hstep1 := h_exp_le_sing (valOf (w₀ ∘ σ)) (w₀ ∘ σ) h0 h1 h2
      refine le_trans hstep1 (WithBot.coe_le_coe.mpr ?_)
      have h_sing_le :
          ∑ g : Fin n, algSelectionProb alg (valOf (w₀ ∘ σ)) {g} * (w₀ ∘ σ) g ≤ B σ := by
        calc ∑ g : Fin n, algSelectionProb alg (valOf (w₀ ∘ σ)) {g} * (w₀ ∘ σ) g
            = ∑ g : Fin n,
                ((1 / (Nat.factorial n : ℝ)) *
                  ∑ π : Equiv.Perm (Fin n),
                    alg.seedMeasure.real
                      {ω : alg.Seed | runDetSelection (alg.det ω) (valOf (w₀ ∘ σ)) π = {g}}) *
                w₀ (σ g) := rfl
          _ = (1 / (Nat.factorial n : ℝ)) *
                ∑ g : Fin n, ∑ π : Equiv.Perm (Fin n),
                  w₀ (σ g) *
                    alg.seedMeasure.real
                      {ω : alg.Seed | runDetSelection (alg.det ω) (valOf (w₀ ∘ σ)) π = {g}} := by
              simp only [Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl (fun g _ => Finset.sum_congr rfl (fun π _ => ?_))
              ring
          _ ≤ (1 / (Nat.factorial n : ℝ)) *
                ∑ g : Fin n, ∑ π : Equiv.Perm (Fin n),
                  w₀ (σ g) *
                    alg.seedMeasure.real
                      {ω : alg.Seed |
                        DetFirstAccepts (alg.det ω) (valOf (w₀ ∘ σ)) π (π.symm g)} := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              refine Finset.sum_le_sum (fun g _ => Finset.sum_le_sum (fun π _ => ?_))
              apply mul_le_mul_of_nonneg_left _ (hw₀ (σ g))
              exact MeasureTheory.measureReal_mono (fun ω hω =>
                h_singleton_imp_dfa (alg.det ω) (valOf (w₀ ∘ σ)) π g hω)
          _ = (1 / (Nat.factorial n : ℝ)) *
                ∑ π : Equiv.Perm (Fin n), ∑ g : Fin n,
                  w₀ (σ g) *
                    alg.seedMeasure.real
                      {ω : alg.Seed |
                        DetFirstAccepts (alg.det ω) (valOf (w₀ ∘ σ)) π (π.symm g)} := by
              rw [Finset.sum_comm]
          _ = B σ := by
              dsimp only [B]
              congr 1
              refine Finset.sum_congr rfl (fun π _ => ?_)
              rw [← Equiv.sum_comp π]
              refine Finset.sum_congr rfl (fun k _ => ?_)
              rw [Equiv.symm_apply_apply]
      exact h_sing_le

    have h_avg_eq :
        (1 / (Nat.factorial n : ℝ)) * ∑ σ : Equiv.Perm (Fin n), B σ = RHS := by
      have h_reidx : ∀ π : Equiv.Perm (Fin n),
          ∑ σ : Equiv.Perm (Fin n), ∑ k : Fin n,
            w₀ (σ (π k)) *
              alg.seedMeasure.real
                {ω : alg.Seed | DetFirstAccepts (alg.det ω) (valOf (w₀ ∘ σ)) π k} =
          ∑ ρ : Equiv.Perm (Fin n), ∑ k : Fin n,
            w₀ (ρ k) *
              alg.seedMeasure.real
                {ω : alg.Seed | DetFirstAccepts (alg.det ω) (valOf ((w₀ ∘ ρ) ∘ π.symm)) π k} := by
        intro π
        let φ : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) :=
          { toFun := fun ρ => π.symm.trans ρ
            invFun := fun σ => π.trans σ
            left_inv := fun ρ => by
              ext x
              simp
            right_inv := fun σ => by
              ext x
              simp }
        rw [← Equiv.sum_comp φ]
        refine Finset.sum_congr rfl (fun ρ _ => Finset.sum_congr rfl (fun k _ => ?_))
        have h1 : φ ρ (π k) = ρ k := by
          dsimp [φ]
          exact congrArg ρ (π.symm_apply_apply k)
        have h2 : w₀ ∘ φ ρ = (w₀ ∘ ρ) ∘ π.symm := by
          funext x
          rfl
        rw [h1, h2]
      calc (1 / (Nat.factorial n : ℝ)) * ∑ σ : Equiv.Perm (Fin n), B σ
          = (1 / (Nat.factorial n : ℝ)) *
              ((1 / (Nat.factorial n : ℝ)) *
                ∑ σ : Equiv.Perm (Fin n), ∑ π : Equiv.Perm (Fin n), ∑ k : Fin n,
                  w₀ (σ (π k)) *
                    alg.seedMeasure.real
                      {ω : alg.Seed | DetFirstAccepts (alg.det ω) (valOf (w₀ ∘ σ)) π k}) := by
            dsimp only [B]
            rw [← Finset.mul_sum]
        _ = (1 / (Nat.factorial n : ℝ)) *
              ((1 / (Nat.factorial n : ℝ)) *
                ∑ π : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin n), ∑ k : Fin n,
                  w₀ (σ (π k)) *
                    alg.seedMeasure.real
                      {ω : alg.Seed | DetFirstAccepts (alg.det ω) (valOf (w₀ ∘ σ)) π k}) := by
            rw [Finset.sum_comm]
        _ = (1 / (Nat.factorial n : ℝ)) *
              ((1 / (Nat.factorial n : ℝ)) *
                ∑ π : Equiv.Perm (Fin n), ∑ ρ : Equiv.Perm (Fin n), ∑ k : Fin n,
                  w₀ (ρ k) *
                    alg.seedMeasure.real
                      {ω : alg.Seed |
                        DetFirstAccepts (alg.det ω) (valOf ((w₀ ∘ ρ) ∘ π.symm)) π k}) := by
            congr 2
            exact Finset.sum_congr rfl (fun π _ => h_reidx π)
        _ = (1 / (Nat.factorial n : ℝ)) *
              ∑ ρ : Equiv.Perm (Fin n), ∑ k : Fin n,
                w₀ (ρ k) *
                  ((1 / (Nat.factorial n : ℝ)) *
                    ∑ π : Equiv.Perm (Fin n),
                      alg.seedMeasure.real
                        {ω : alg.Seed |
                          DetFirstAccepts (alg.det ω) (valOf ((w₀ ∘ ρ) ∘ π.symm)) π k}) := by
            congr 1
            rw [Finset.sum_comm, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun ρ _ => ?_)
            rw [Finset.sum_comm, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [← Finset.mul_sum, ← mul_assoc, mul_comm (1 / (Nat.factorial n : ℝ)) (w₀ (ρ k)),
              mul_assoc]
        _ = RHS := by
            dsimp only [RHS]
            congr 1
            refine Finset.sum_congr rfl (fun ρ _ => Finset.sum_congr rfl (fun k _ => ?_))
            rw [← hp_eval (w₀ ∘ ρ) k]
            rfl

    have h_sum_le :
        ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), B σ ≤
        ∑ _σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), RHS := by
      have h_rhs_sum :
          ∑ _σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), RHS =
            (Nat.factorial n : ℝ) * RHS := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, h_card_perm]
      rw [h_rhs_sum, ← h_avg_eq, ← mul_assoc, mul_one_div_cancel h_fact_ne, one_mul]

    obtain ⟨σ, _, hB_le⟩ :=
      Finset.exists_le_of_sum_le ⟨Equiv.refl (Fin n), Finset.mem_univ _⟩ h_sum_le
    refine ⟨σ, ?_⟩
    exact le_trans (h_exp_le_B σ) (WithBot.coe_le_coe.mpr hB_le)

theorem gs_rank_one_plus_modular_props (n : ℕ) (hn : 1 ≤ n)
    (W_max : ℝ) (hW : 1 ≤ W_max)
    (w : Fin n → ℝ) (hw : ∀ g : Fin n, 1 ≤ w g ∧ w g ≤ W_max) :
    (0 < 3 * W_max ∧
      IsGSValuation (rankOneModularVal (3 * W_max) w) ∧
      IsFiniteValuation (rankOneModularVal (3 * W_max) w)) ∧
    (∀ M_opt : ℝ, (∀ g : Fin n, w g ≤ M_opt) → (∃ g : Fin n, w g = M_opt) →
      optVal (rankOneModularVal (3 * W_max) w) = M_opt ∧
      0 < optVal (rankOneModularVal (3 * W_max) w)) ∧
    (realVal (rankOneModularVal (3 * W_max) w) ∅ = 0 ∧
      (∀ g : Fin n, realVal (rankOneModularVal (3 * W_max) w) {g} = w g) ∧
      (∀ S : Finset (Fin n), 2 ≤ S.card → realVal (rankOneModularVal (3 * W_max) w) S ≤ 0)) :=
by
  have _ := hn
  let κ : ℝ := 3 * W_max
  let a : Fin n → ℝ := fun g => w g - κ
  let f : Finset (Fin n) → ℝ := fun S => κ * (min S.card 1 : ℕ) + ∑ g ∈ S, a g
  let v : ItemValuation n := rankOneModularVal (3 * W_max) w
  have hv_eq : ∀ S : Finset (Fin n), v S = ((f S : ℝ) : WithBot ℝ) := fun _ => rfl
  have hκ_pos : 0 < 3 * W_max := by linarith
  have hκ_pos' : 0 < κ := hκ_pos
  have h_fin : IsFiniteValuation v := by
    intro S
    rw [hv_eq S]
    exact WithBot.coe_ne_bot
  have hreal_eq : ∀ S : Finset (Fin n), realVal v S = f S := by
    intro S
    unfold realVal
    rw [hv_eq S, WithBot.unbotD_coe]
  have hf_empty : f ∅ = 0 := by
    simp [f]
  have hv_empty : v ∅ = ((0 : ℝ) : WithBot ℝ) := by
    rw [hv_eq ∅, hf_empty]
  have hreal_empty : realVal v ∅ = 0 := by
    rw [hreal_eq ∅, hf_empty]
  have hf_sing : ∀ g : Fin n, f {g} = w g := by
    intro g
    simp [f, a]
  have hreal_sing : ∀ g : Fin n, realVal v {g} = w g := by
    intro g
    rw [hreal_eq {g}, hf_sing g]
  have hmin_of_mem : ∀ (S : Finset (Fin n)) (z : Fin n), z ∈ S → min S.card 1 = 1 := by
    intro S z hz
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨z, hz⟩
    omega
  have hf_multi : ∀ S : Finset (Fin n), 2 ≤ S.card → f S ≤ 0 := by
    intro S hS2
    have hmin : min S.card 1 = 1 := by omega
    have hsum : ∑ g ∈ S, a g ≤ (S.card : ℝ) * (-2 * W_max) := by
      calc ∑ g ∈ S, a g
          ≤ ∑ _g ∈ S, (-2 * W_max) := by
            apply Finset.sum_le_sum
            intro g _
            have hwg := (hw g).2
            dsimp [a, κ]
            linarith
        _ = (S.card : ℝ) * (-2 * W_max) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hcard_ge : (2 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hS2
    have h_prod : 4 * W_max ≤ 2 * (S.card : ℝ) * W_max := by nlinarith
    have h_f_def : f S = 3 * W_max + ∑ g ∈ S, a g := by
      dsimp [f, κ]
      rw [hmin]
      push_cast
      ring
    linarith
  have hreal_multi : ∀ S : Finset (Fin n), 2 ≤ S.card → realVal v S ≤ 0 := by
    intro S hS2
    rw [hreal_eq S]
    exact hf_multi S hS2
  have h_opt : ∀ M_opt : ℝ, (∀ g : Fin n, w g ≤ M_opt) → (∃ g : Fin n, w g = M_opt) →
      optVal v = M_opt ∧ 0 < optVal v := by
    intro M_opt h_le ⟨g₀, hg₀⟩
    have hM_ge1 : 1 ≤ M_opt := by
      have := (hw g₀).1
      linarith
    have hM_pos : 0 < M_opt := by linarith
    have h_sup_le : (Finset.univ : Finset (Finset (Fin n))).sup v ≤ ((M_opt : ℝ) : WithBot ℝ) := by
      apply Finset.sup_le
      intro S _
      rw [hv_eq S, WithBot.coe_le_coe]
      rcases Nat.lt_trichotomy S.card 1 with hlt | heq | hgt
      · have h0 : S.card = 0 := by omega
        rw [Finset.card_eq_zero.mp h0, hf_empty]
        linarith
      · rcases Finset.card_eq_one.mp heq with ⟨g, rfl⟩
        rw [hf_sing g]
        exact h_le g
      · have h2 : 2 ≤ S.card := by omega
        have := hf_multi S h2
        linarith
    have h_le_sup : ((M_opt : ℝ) : WithBot ℝ) ≤ (Finset.univ : Finset (Finset (Fin n))).sup v := by
      have h_eq_g₀ : v {g₀} = ((M_opt : ℝ) : WithBot ℝ) := by
        rw [hv_eq {g₀}, hf_sing g₀, hg₀]
      rw [← h_eq_g₀]
      exact Finset.le_sup (f := v) (Finset.mem_univ {g₀})
    have h_sup_eq : (Finset.univ : Finset (Finset (Fin n))).sup v = ((M_opt : ℝ) : WithBot ℝ) :=
      le_antisymm h_sup_le h_le_sup
    have h_opt_eq : optVal v = M_opt := by
      unfold optVal
      rw [h_sup_eq, WithBot.unbotD_coe]
    exact ⟨h_opt_eq, h_opt_eq.symm ▸ hM_pos⟩
  have h_gs : IsGSValuation v := by
    refine ⟨hv_empty, ?_⟩
    intro X Y _hX _hY x hxXY
    rcases Finset.mem_sdiff.mp hxXY with ⟨hxX, hxY⟩
    have h_add : ∀ A B : Finset (Fin n), v A + v B = ((f A + f B : ℝ) : WithBot ℝ) := by
      intro A B
      rw [hv_eq A, hv_eq B, ← WithBot.coe_add]
    have h_mod_tr : ∑ g ∈ X.erase x, a g + ∑ g ∈ insert x Y, a g = ∑ g ∈ X, a g + ∑ g ∈ Y, a g := by
      have h1 : a x + ∑ g ∈ X.erase x, a g = ∑ g ∈ X, a g := Finset.add_sum_erase X a hxX
      have h2 : ∑ g ∈ insert x Y, a g = a x + ∑ g ∈ Y, a g := Finset.sum_insert hxY
      linarith
    have hmin_X : min X.card 1 = 1 := hmin_of_mem X x hxX
    have hmin_insY : min (insert x Y).card 1 = 1 :=
      hmin_of_mem (insert x Y) x (Finset.mem_insert.mpr (Or.inl rfl))
    by_cases hYX : (Y \ X).Nonempty
    · obtain ⟨y, hy⟩ := hYX
      rcases Finset.mem_sdiff.mp hy with ⟨hyY, hyX⟩
      have hxy : x ≠ y := by
        intro h_eq
        apply hyX
        rw [← h_eq]
        exact hxX
      have hy_not_erase : y ∉ X.erase x := by
        intro hmem
        exact hyX (Finset.mem_erase.mp hmem).2
      have hy_mem_ins : y ∈ insert x Y := Finset.mem_insert.mpr (Or.inr hyY)
      have h_mod_sw : ∑ g ∈ insert y (X.erase x), a g + ∑ g ∈ (insert x Y).erase y, a g =
          ∑ g ∈ X, a g + ∑ g ∈ Y, a g := by
        have h1 : a x + ∑ g ∈ X.erase x, a g = ∑ g ∈ X, a g := Finset.add_sum_erase X a hxX
        have h2 : ∑ g ∈ insert x Y, a g = a x + ∑ g ∈ Y, a g := Finset.sum_insert hxY
        have h3 : ∑ g ∈ insert y (X.erase x), a g = a y + ∑ g ∈ X.erase x, a g :=
          Finset.sum_insert hy_not_erase
        have h4 : a y + ∑ g ∈ (insert x Y).erase y, a g = ∑ g ∈ insert x Y, a g :=
          Finset.add_sum_erase (insert x Y) a hy_mem_ins
        linarith
      have hmin_Y : min Y.card 1 = 1 := hmin_of_mem Y y hyY
      have hmin_sw1 : min (insert y (X.erase x)).card 1 = 1 :=
        hmin_of_mem (insert y (X.erase x)) y (Finset.mem_insert.mpr (Or.inl rfl))
      have hx_mem_sw2 : x ∈ (insert x Y).erase y :=
        Finset.mem_erase.mpr ⟨hxy, Finset.mem_insert.mpr (Or.inl rfl)⟩
      have hmin_sw2 : min ((insert x Y).erase y).card 1 = 1 :=
        hmin_of_mem ((insert x Y).erase y) x hx_mem_sw2
      have hf_sw : f X + f Y ≤ f (insert y (X.erase x)) + f ((insert x Y).erase y) := by
        dsimp only [f]
        rw [hmin_X, hmin_Y, hmin_sw1, hmin_sw2]
        push_cast
        linarith
      have hv_sw : v X + v Y ≤ v (insert y (X.erase x)) + v ((insert x Y).erase y) := by
        rw [h_add X Y, h_add (insert y (X.erase x)) ((insert x Y).erase y), WithBot.coe_le_coe]
        exact hf_sw
      have h_sup_sw : v (insert y (X.erase x)) + v ((insert x Y).erase y) ≤
          (Y \ X).sup (fun z => v (insert z (X.erase x)) + v ((insert x Y).erase z)) :=
        Finset.le_sup (f := fun z => v (insert z (X.erase x)) + v ((insert x Y).erase z)) hy
      exact le_max_of_le_right (le_trans hv_sw h_sup_sw)
    · have hYX_empty : Y \ X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hYX
      have h_sub : Y ⊆ X := Finset.sdiff_eq_empty_iff_subset.mp hYX_empty
      have hf_tr : f X + f Y ≤ f (X.erase x) + f (insert x Y) := by
        by_cases hY_ne : Y.Nonempty
        · obtain ⟨y, hyY⟩ := hY_ne
          have hyX : y ∈ X := h_sub hyY
          have hyx : y ≠ x := by
            intro h_eq
            apply hxY
            rw [← h_eq]
            exact hyY
          have hy_erase : y ∈ X.erase x := Finset.mem_erase.mpr ⟨hyx, hyX⟩
          have hmin_Y : min Y.card 1 = 1 := hmin_of_mem Y y hyY
          have hmin_erX : min (X.erase x).card 1 = 1 := hmin_of_mem (X.erase x) y hy_erase
          dsimp only [f]
          rw [hmin_X, hmin_Y, hmin_erX, hmin_insY]
          push_cast
          linarith
        · have hY_empty : Y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hY_ne
          have hmin_Y0 : min Y.card 1 = 0 := by rw [hY_empty]; simp
          have h_nonneg : (0 : ℝ) ≤ κ * ((min (X.erase x).card 1 : ℕ) : ℝ) := by positivity
          dsimp only [f]
          rw [hmin_X, hmin_Y0, hmin_insY]
          push_cast at h_nonneg ⊢
          linarith
      have hv_tr : v X + v Y ≤ v (X.erase x) + v (insert x Y) := by
        rw [h_add X Y, h_add (X.erase x) (insert x Y), WithBot.coe_le_coe]
        exact hf_tr
      exact le_max_of_le_left hv_tr
  exact ⟨⟨hκ_pos, h_gs, h_fin⟩, h_opt, ⟨hreal_empty, hreal_sing, hreal_multi⟩⟩

theorem rank_one_matroid_props (n : ℕ) (hn : 1 ≤ n) :
    ∃ M : Matroid (Fin n),
      (∀ S : Finset (Fin n), M.Indep (S : Set (Fin n)) ↔ S.card ≤ 1) ∧
      (∀ w : Fin n → ℝ, IsGSValuation (weightedMatroidVal M w)) ∧
      (∀ (w : Fin n → ℝ) (M_opt : ℝ),
        0 < M_opt → (∀ g : Fin n, w g ≤ M_opt) → (∃ g : Fin n, w g = M_opt) →
        optVal (weightedMatroidVal M w) = M_opt) ∧
      (∀ w : Fin n → ℝ,
        realVal (weightedMatroidVal M w) ∅ = 0 ∧
        (∀ g : Fin n, realVal (weightedMatroidVal M w) {g} = w g) ∧
        (∀ S : Finset (Fin n), 2 ≤ S.card → realVal (weightedMatroidVal M w) S ≤ 0)) ∧
      (∀ (w₁ w₂ : Fin n → ℝ) (S : Finset (Fin n)),
        (∀ g ∈ S, w₁ g = w₂ g) → weightedMatroidVal M w₁ S = weightedMatroidVal M w₂ S) :=
by
  let _ := hn
  let P : Set (Fin n) → Prop := fun I => I.encard ≤ 1
  have h_empty : P ∅ := by
    dsimp [P]
    rw [Set.encard_empty]
    exact zero_le 1
  have h_sub : ∀ ⦃I J : Set (Fin n)⦄, P J → I ⊆ J → P I := by
    intro I J hJ hIJ
    exact le_trans (Set.encard_le_encard hIJ) hJ
  have h_aug : ∀ ⦃I J : Set (Fin n)⦄, P I → P J → I.encard < J.encard →
      ∃ e ∈ J, e ∉ I ∧ P (insert e I) := by
    intro I J _ hJ hlt
    have hI_lt : I.encard < 1 := lt_of_lt_of_le hlt hJ
    have hI0 : I.encard = 0 := ENat.lt_one_iff_eq_zero.mp hI_lt
    have hI_emp : I = ∅ := Set.encard_eq_zero.mp hI0
    have hJ_pos : 0 < J.encard := by rwa [hI0] at hlt
    obtain ⟨e, heJ⟩ := Set.encard_pos.mp hJ_pos
    refine ⟨e, heJ, ?_, ?_⟩
    · rw [hI_emp]
      exact Set.notMem_empty e
    · dsimp [P]
      rw [hI_emp, ← Set.singleton_def, Set.encard_singleton]
  have h_bdd : ∃ k : ℕ, ∀ I : Set (Fin n), P I → I.encard ≤ (k : ℕ∞) := by
    refine ⟨1, fun I hI => ?_⟩
    rw [ENat.coe_one]
    exact hI
  have h_ground : ∀ I : Set (Fin n), P I → I ⊆ Set.univ := fun I _ => Set.subset_univ I
  let IM : IndepMatroid (Fin n) :=
    IndepMatroid.ofBddAugment Set.univ P h_empty h_sub h_aug h_bdd h_ground
  let M : Matroid (Fin n) := IM.matroid
  have hM_set_indep : ∀ I : Set (Fin n), M.Indep I ↔ I.encard ≤ 1 := by
    intro I
    have h1 : M.Indep I = IM.Indep I := IndepMatroid.matroid_Indep IM I
    have h2 : IM.Indep = P :=
      IndepMatroid.ofBddAugment_indep Set.univ P h_empty h_sub h_aug h_bdd h_ground
    rw [h1, h2]
  have hM_indep : ∀ S : Finset (Fin n), M.Indep (S : Set (Fin n)) ↔ S.card ≤ 1 := by
    intro S
    rw [hM_set_indep, Set.encard_coe_eq_coe_finsetCard, ← ENat.coe_one, Nat.cast_le]
  have h_val_empty : ∀ w : Fin n → ℝ, weightedMatroidVal M w ∅ = ((0 : ℝ) : WithBot ℝ) := by
    intro w
    have hind : M.Indep ((∅ : Finset (Fin n)) : Set (Fin n)) :=
      (hM_indep ∅).mpr (by simp)
    unfold weightedMatroidVal
    rw [if_pos hind]
    simp
  have h_val_sing : ∀ (w : Fin n → ℝ) (g : Fin n),
      weightedMatroidVal M w {g} = ((w g : ℝ) : WithBot ℝ) := by
    intro w g
    have hind : M.Indep (({g} : Finset (Fin n)) : Set (Fin n)) :=
      (hM_indep {g}).mpr (by simp)
    unfold weightedMatroidVal
    rw [if_pos hind]
    simp
  have h_val_dep : ∀ (w : Fin n → ℝ) (S : Finset (Fin n)),
      ¬ (S.card ≤ 1) → weightedMatroidVal M w S = ⊥ := by
    intro w S hS
    have hnot : ¬ M.Indep (S : Set (Fin n)) := fun h => hS ((hM_indep S).mp h)
    unfold weightedMatroidVal
    rw [if_neg hnot]
  have hM_gs : ∀ w : Fin n → ℝ, IsGSValuation (weightedMatroidVal M w) := by
    intro w
    refine ⟨h_val_empty w, ?_⟩
    intro X Y hX_ne hY_ne x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxX, hxY⟩
    have hX_le : X.card ≤ 1 := by
      by_contra hnot
      exact hX_ne (h_val_dep w X hnot)
    have hY_le : Y.card ≤ 1 := by
      by_contra hnot
      exact hY_ne (h_val_dep w Y hnot)
    have hX_eq : X = {x} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hxX, fun z hz => ?_⟩
      exact Finset.card_le_one.mp hX_le z hz x hxX
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hY_le with hY0 | hY1
    · have hY_eq : Y = ∅ := Finset.card_eq_zero.mp hY0
      have h_lhs : weightedMatroidVal M w X + weightedMatroidVal M w Y =
          weightedMatroidVal M w (X.erase x) + weightedMatroidVal M w (insert x Y) := by
        rw [hX_eq, hY_eq, Finset.erase_singleton, Finset.insert_empty,
          h_val_sing w x, h_val_empty w, ← WithBot.coe_add, ← WithBot.coe_add, add_comm]
      rw [h_lhs]
      exact le_max_left _ _
    · obtain ⟨y, hY_eq⟩ := Finset.card_eq_one.mp hY1
      have hxy : x ≠ y := by
        intro h_eq
        rw [h_eq, hY_eq] at hxY
        exact hxY (Finset.mem_singleton_self y)
      have hy_mem : y ∈ Y \ X := by
        rw [Finset.mem_sdiff, hY_eq, hX_eq]
        exact ⟨Finset.mem_singleton_self y, fun hyx => hxy (Finset.mem_singleton.mp hyx).symm⟩
      have h_swap_eq : weightedMatroidVal M w X + weightedMatroidVal M w Y =
          weightedMatroidVal M w (insert y (X.erase x)) +
            weightedMatroidVal M w ((insert x Y).erase y) := by
        rw [hX_eq, hY_eq, Finset.erase_singleton, Finset.insert_empty,
          Finset.erase_insert_of_ne hxy, Finset.erase_singleton, Finset.insert_empty,
          h_val_sing w x, h_val_sing w y, ← WithBot.coe_add, ← WithBot.coe_add, add_comm]
      have h_le_sup : weightedMatroidVal M w X + weightedMatroidVal M w Y ≤
          (Y \ X).sup (fun z => weightedMatroidVal M w (insert z (X.erase x)) +
            weightedMatroidVal M w ((insert x Y).erase z)) := by
        rw [h_swap_eq]
        exact Finset.le_sup (f := fun z => weightedMatroidVal M w (insert z (X.erase x)) +
          weightedMatroidVal M w ((insert x Y).erase z)) hy_mem
      exact le_trans h_le_sup (le_max_right _ _)
  have hM_opt : ∀ (w : Fin n → ℝ) (M_opt : ℝ),
      0 < M_opt → (∀ g : Fin n, w g ≤ M_opt) → (∃ g : Fin n, w g = M_opt) →
      optVal (weightedMatroidVal M w) = M_opt := by
    intro w M_opt hM_pos hw_le ⟨g₀, hg₀⟩
    have h_sup : (Finset.univ : Finset (Finset (Fin n))).sup (weightedMatroidVal M w) =
        ((M_opt : ℝ) : WithBot ℝ) := by
      apply le_antisymm
      · apply Finset.sup_le
        intro S _
        by_cases hS : S.card ≤ 1
        · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hS with hS0 | hS1
          · rw [Finset.card_eq_zero.mp hS0, h_val_empty w]
            exact WithBot.coe_le_coe.mpr (le_of_lt hM_pos)
          · obtain ⟨g, rfl⟩ := Finset.card_eq_one.mp hS1
            rw [h_val_sing w g]
            exact WithBot.coe_le_coe.mpr (hw_le g)
        · rw [h_val_dep w S hS]
          exact bot_le
      · have h_eq : weightedMatroidVal M w {g₀} = ((M_opt : ℝ) : WithBot ℝ) := by
          rw [h_val_sing w g₀, hg₀]
        rw [← h_eq]
        exact Finset.le_sup (f := weightedMatroidVal M w) (Finset.mem_univ {g₀})
    unfold optVal
    rw [h_sup]
    exact WithBot.unbotD_coe 0 M_opt
  have hM_real : ∀ w : Fin n → ℝ,
      realVal (weightedMatroidVal M w) ∅ = 0 ∧
      (∀ g : Fin n, realVal (weightedMatroidVal M w) {g} = w g) ∧
      (∀ S : Finset (Fin n), 2 ≤ S.card → realVal (weightedMatroidVal M w) S ≤ 0) := by
    intro w
    refine ⟨?_, ?_, ?_⟩
    · unfold realVal
      rw [h_val_empty w]
      exact WithBot.unbotD_coe 0 0
    · intro g
      unfold realVal
      rw [h_val_sing w g]
      exact WithBot.unbotD_coe 0 (w g)
    · intro S hS2
      have hS_not : ¬ (S.card ≤ 1) := by omega
      unfold realVal
      rw [h_val_dep w S hS_not, WithBot.unbotD_bot 0]
  have hM_loc : ∀ (w₁ w₂ : Fin n → ℝ) (S : Finset (Fin n)),
      (∀ g ∈ S, w₁ g = w₂ g) → weightedMatroidVal M w₁ S = weightedMatroidVal M w₂ S := by
    intro w₁ w₂ S h_eq
    unfold weightedMatroidVal
    split_ifs with _
    · rw [Finset.sum_congr rfl h_eq]
    · rfl
  exact ⟨M, hM_indep, hM_gs, hM_opt, hM_real, hM_loc⟩

end SecretaryEmbeddingInternal

section
open SecretaryEmbeddingInternal

theorem prop_secretary_embedding (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 1 ≤ n ∧
      (∃ fam : List (ItemValuation n),
        fam ≠ [] ∧
        (∀ v ∈ fam,
          IsGSValuation v ∧
          IsFiniteValuation v ∧
          0 < optVal v ∧
          ∃ (κ : ℝ) (a : Fin n → ℝ), 0 < κ ∧
            ∀ S : Finset (Fin n),
              v S = ((κ * (min S.card 1 : ℕ) + ∑ g ∈ S, a g : ℝ) : WithBot ℝ)) ∧
        (∀ alg : OnlineSelectionAlg n,
          ∃ v ∈ fam,
            expectedSelectionVal alg v ≤ (((invE + ε) * optVal v : ℝ) : WithBot ℝ))) ∧
      (∃ mfam : List (Matroid (Fin n) × (Fin n → ℝ)),
        mfam ≠ [] ∧
        (∀ mw ∈ mfam,
          (∀ S : Finset (Fin n), mw.1.Indep (S : Set (Fin n)) ↔ S.card ≤ 1) ∧
          IsGSValuation (weightedMatroidVal mw.1 mw.2) ∧
          0 < optVal (weightedMatroidVal mw.1 mw.2)) ∧
        (∀ alg : OnlineSelectionAlg n,
          ∃ mw ∈ mfam,
            expectedSelectionVal alg (weightedMatroidVal mw.1 mw.2) ≤
              (((invE + ε) * optVal (weightedMatroidVal mw.1 mw.2) : ℝ) : WithBot ℝ))) :=
by
  
  let K_ceil : ℕ := ⌈6 / ε⌉₊
  let n : ℕ := K_ceil + 2
  let M_grid : ℕ := K_ceil + 1
  let ϱ : ℝ := max 2 (3 / ε)
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hM_pos : 0 < (M_grid : ℝ) := by positivity
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hK_le : 6 / ε ≤ (K_ceil : ℝ) := Nat.le_ceil (6 / ε)
  have hM_ge : 6 / ε ≤ (M_grid : ℝ) := by
    have : (K_ceil : ℝ) ≤ (M_grid : ℝ) := by exact_mod_cast (by omega : K_ceil ≤ M_grid)
    linarith
  have hn_ge : 6 / ε ≤ (n : ℝ) := by
    have : (K_ceil : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : K_ceil ≤ n)
    linarith
  have h_inv_M : 1 / (M_grid : ℝ) ≤ ε / 6 := by
    rw [div_le_div_iff₀ hM_pos (by norm_num)]
    have h6 : 6 ≤ (M_grid : ℝ) * ε := (div_le_iff₀ hε).mp hM_ge
    linarith
  have h_inv_n : 1 / (n : ℝ) ≤ ε / 6 := by
    rw [div_le_div_iff₀ hn_pos (by norm_num)]
    have h6 : 6 ≤ (n : ℝ) * ε := (div_le_iff₀ hε).mp hn_ge
    linarith
  have hϱ2 : 2 ≤ ϱ := le_max_left 2 (3 / ε)
  have hϱ1 : 1 ≤ ϱ := by linarith
  have hϱ_pos : 0 < ϱ := by linarith
  have h_inv_ϱ : 1 / ϱ ≤ ε / 3 := by
    rw [div_le_div_iff₀ hϱ_pos (by norm_num)]
    have h3 : 3 ≤ ϱ * ε := (div_le_iff₀ hε).mp (le_max_right 2 (3 / ε))
    linarith

  
  let γ : ℕ → Type := fun k => Equiv.Perm (Fin k) → Fin (M_grid + 1)
  haveI hγ_nonempty : ∀ k, Nonempty (γ k) := fun _ => ⟨fun _ => 0⟩
  obtain ⟨N, hN_ge, hRamsey⟩ := fin_ramsey_simultaneous n γ
  have hN1 : 1 ≤ N := by omega
  let W_max : ℝ := ϱ ^ (N - 1)
  have hW_max : 1 ≤ W_max := one_le_pow₀ hϱ1

  have h_pow_bounds : ∀ x : Fin N, 1 ≤ ϱ ^ x.1 ∧ ϱ ^ x.1 ≤ W_max := by
    intro x
    exact ⟨one_le_pow₀ hϱ1, pow_le_pow_right₀ hϱ1 (by omega)⟩

  have h_pow_gap : ∀ a b : ℕ, a < b → ϱ ^ a ≤ (ε / 3) * ϱ ^ b := by
    intro a b hab
    have h1 : ϱ ^ (a + 1) ≤ ϱ ^ b := pow_le_pow_right₀ hϱ1 (by omega)
    rw [pow_succ] at h1
    have h2 : ϱ ^ a ≤ (1 / ϱ) * ϱ ^ b := by
      rw [one_div_mul_eq_div, le_div_iff₀ hϱ_pos]
      exact h1
    have h3 : 0 ≤ ϱ ^ b := pow_nonneg (le_of_lt hϱ_pos) b
    calc ϱ ^ a ≤ (1 / ϱ) * ϱ ^ b := h2
      _ ≤ (ε / 3) * ϱ ^ b := mul_le_mul_of_nonneg_right h_inv_ϱ h3

  
  let Idx : Type := {S : Finset (Fin N) // S.card = n} × Equiv.Perm (Fin n)
  obtain ⟨S₀, hS₀, _⟩ := hRamsey (fun _ _ _ => 0)
  let idx₀ : Idx := (⟨S₀, hS₀⟩, Equiv.refl (Fin n))

  let j_max : Fin n := ⟨n - 1, by omega⟩
  let M_opt_of : (S : Finset (Fin N)) → S.card = n → ℝ :=
    fun S hS => ϱ ^ ((S.orderEmbOfFin hS) j_max).1
  let w_of : Idx → (Fin n → ℝ) :=
    fun idx g => ϱ ^ ((idx.1.1.orderEmbOfFin idx.1.2) (idx.2 g)).1

  have hw_bounds : ∀ idx : Idx, ∀ g : Fin n, 1 ≤ w_of idx g ∧ w_of idx g ≤ W_max := by
    intro idx g
    exact h_pow_bounds ((idx.1.1.orderEmbOfFin idx.1.2) (idx.2 g))

  have hM_opt_pos : ∀ (S : Finset (Fin N)) (hS : S.card = n), 0 < M_opt_of S hS := by
    intro S hS
    have h1 := (h_pow_bounds ((S.orderEmbOfFin hS) j_max)).1
    linarith

  have hw_le_M_opt : ∀ idx : Idx, ∀ g : Fin n, w_of idx g ≤ M_opt_of idx.1.1 idx.1.2 := by
    intro idx g
    apply pow_le_pow_right₀ hϱ1
    have hle : idx.2 g ≤ j_max := by
      change (idx.2 g).1 ≤ n - 1
      omega
    exact (idx.1.1.orderEmbOfFin idx.1.2).monotone hle

  have hw_eq_M_opt : ∀ idx : Idx, ∃ g : Fin n, w_of idx g = M_opt_of idx.1.1 idx.1.2 := by
    intro idx
    refine ⟨idx.2.symm j_max, ?_⟩
    simp [w_of, M_opt_of]

  
  let bin : ℝ → Fin (M_grid + 1) :=
    fun x => ⟨min ⌊(M_grid : ℝ) * x⌋₊ M_grid, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

  have h_bin_close : ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
      bin x = bin y → x - y ≤ 1 / (M_grid : ℝ) := by
    intro x y hx0 hx1 hy0 hy1 hbin
    have hMx : (M_grid : ℝ) * x ≤ (M_grid : ℝ) := by nlinarith
    have hMy : (M_grid : ℝ) * y ≤ (M_grid : ℝ) := by nlinarith
    have hfx : ⌊(M_grid : ℝ) * x⌋₊ ≤ M_grid := Nat.floor_le_of_le hMx
    have hfy : ⌊(M_grid : ℝ) * y⌋₊ ≤ M_grid := Nat.floor_le_of_le hMy
    have hbin_val : (bin x).1 = (bin y).1 := congrArg Fin.val hbin
    dsimp [bin] at hbin_val
    rw [Nat.min_eq_left hfx, Nat.min_eq_left hfy] at hbin_val
    have hlt_x : (M_grid : ℝ) * x < (⌊(M_grid : ℝ) * x⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one ((M_grid : ℝ) * x)
    have hle_y : (⌊(M_grid : ℝ) * y⌋₊ : ℝ) ≤ (M_grid : ℝ) * y :=
      Nat.floor_le (by positivity)
    rw [hbin_val] at hlt_x
    have hdiff : (M_grid : ℝ) * (x - y) ≤ 1 := by linarith
    rw [le_div_iff₀' hM_pos]
    exact hdiff

  
  have h_unified : ∀ (valOf : (Fin n → ℝ) → ItemValuation n),
      (∀ (w₁ w₂ : Fin n → ℝ) (A : Finset (Fin n)),
        (∀ g ∈ A, w₁ g = w₂ g) → valOf w₁ A = valOf w₂ A) →
      (∀ w : Fin n → ℝ, (∀ g : Fin n, 1 ≤ w g ∧ w g ≤ W_max) →
        realVal (valOf w) ∅ ≤ 0 ∧
        (∀ g : Fin n, realVal (valOf w) {g} ≤ w g) ∧
        (∀ A : Finset (Fin n), 2 ≤ A.card → realVal (valOf w) A ≤ 0)) →
      ∀ alg : OnlineSelectionAlg n,
        ∃ idx : Idx,
          expectedSelectionVal alg (valOf (w_of idx)) ≤
            (((invE + ε) * M_opt_of idx.1.1 idx.1.2 : ℝ) : WithBot ℝ) := by
    intro valOf h_loc h_val alg
    obtain ⟨p, hp01, hp_sum, hp_red⟩ := online_alg_stopping_reduction n hn1 valOf h_loc alg
    let c : (k : ℕ) → Finset (Fin N) → γ k := fun k T =>
      if hT : T.card = k then
        fun τ => bin (p k (fun i : Fin k => ϱ ^ ((T.orderEmbOfFin hT) (τ i)).1))
      else
        fun _ => 0
    obtain ⟨S, hS, hS_mono⟩ := hRamsey c
    let e_S : Fin n ↪o Fin N := S.orderEmbOfFin hS
    let w₀ : Fin n → ℝ := fun j => ϱ ^ (e_S j).1
    have hw₀_nonneg : ∀ j : Fin n, 0 ≤ w₀ j := fun j =>
      le_trans zero_le_one (h_pow_bounds (e_S j)).1
    let p_pref : Fin n → Equiv.Perm (Fin n) → ℝ := fun k ρ' =>
      p (k.1 + 1) (fun i : Fin (k.1 + 1) => w₀ (ρ' ⟨i.1, Nat.lt_of_lt_of_le i.2 k.2⟩))
    let eqv : Fin n → Equiv.Perm (Fin n) → Finset (Equiv.Perm (Fin n)) := fun k ρ =>
      Finset.univ.filter (fun ρ' : Equiv.Perm (Fin n) =>
        ∀ i j : Fin n, i ≤ k → j ≤ k → (ρ' i ≤ ρ' j ↔ ρ i ≤ ρ j))
    have h_mem_eqv : ∀ (k : Fin n) (ρ : Equiv.Perm (Fin n)), ρ ∈ eqv k ρ := by
      intro k ρ
      simp [eqv]
    let q : Fin n → Equiv.Perm (Fin n) → ℝ := fun k ρ =>
      (eqv k ρ).inf' ⟨ρ, h_mem_eqv k ρ⟩ (p_pref k)

    have hq_nonneg : ∀ (k : Fin n) (ρ : Equiv.Perm (Fin n)), 0 ≤ q k ρ := by
      intro k ρ
      exact Finset.le_inf' _ _ (fun ρ' _ => (hp01 _ _).1)

    have hq_sum : ∀ ρ : Equiv.Perm (Fin n), ∑ k : Fin n, q k ρ ≤ 1 := by
      intro ρ
      calc ∑ k : Fin n, q k ρ
          ≤ ∑ k : Fin n, p_pref k ρ :=
            Finset.sum_le_sum (fun k _ => Finset.inf'_le (p_pref k) (h_mem_eqv k ρ))
        _ ≤ 1 := hp_sum (w₀ ∘ ρ)

    have h_inf_congr : ∀ (s₁ s₂ : Finset (Equiv.Perm (Fin n))) (hs : s₁ = s₂)
        (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty) (f : Equiv.Perm (Fin n) → ℝ),
        s₁.inf' h₁ f = s₂.inf' h₂ f := by
      intro s₁ s₂ hs h₁ h₂ f
      subst hs
      rfl

    have hq_ord : ∀ (k : Fin n) (ρ₁ ρ₂ : Equiv.Perm (Fin n)),
        (∀ i j : Fin n, i ≤ k → j ≤ k → (ρ₁ i ≤ ρ₁ j ↔ ρ₂ i ≤ ρ₂ j)) →
        q k ρ₁ = q k ρ₂ := by
      intro k ρ₁ ρ₂ h12
      apply h_inf_congr (eqv k ρ₁) (eqv k ρ₂)
      ext ρ'
      simp only [eqv, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h' i j hi hj
        exact (h' i j hi hj).trans (h12 i j hi hj)
      · intro h' i j hi hj
        exact (h' i j hi hj).trans (h12 i j hi hj).symm

    have h_ord_bound := ordinal_secretary_bound n hn1 q hq_nonneg hq_sum hq_ord

    have h_grid_gap : ∀ (k : Fin n) (ρ : Equiv.Perm (Fin n)),
        p_pref k ρ ≤ q k ρ + 1 / (M_grid : ℝ) := by
      intro k ρ
      obtain ⟨ρ', hρ'_mem, hq_eq⟩ := Finset.exists_mem_eq_inf' ⟨ρ, h_mem_eqv k ρ⟩ (p_pref k)
      have hρ'_rel : ∀ i j : Fin n, i ≤ k → j ≤ k → (ρ' i ≤ ρ' j ↔ ρ i ≤ ρ j) :=
        (Finset.mem_filter.mp hρ'_mem).2
      let m : ℕ := k.1 + 1
      let u₁ : Fin m → Fin N := fun i => e_S (ρ ⟨i.1, Nat.lt_of_lt_of_le i.2 k.2⟩)
      let u₂ : Fin m → Fin N := fun i => e_S (ρ' ⟨i.1, Nat.lt_of_lt_of_le i.2 k.2⟩)
      have hu₁ : Function.Injective u₁ := by
        intro i j hij
        have h1 : ρ ⟨i.1, _⟩ = ρ ⟨j.1, _⟩ := e_S.injective hij
        have h2 : (⟨i.1, Nat.lt_of_lt_of_le i.2 k.2⟩ : Fin n) = ⟨j.1, _⟩ := ρ.injective h1
        exact Fin.ext (congrArg (fun x : Fin n => x.1) h2)
      have hu₂ : Function.Injective u₂ := by
        intro i j hij
        have h1 : ρ' ⟨i.1, _⟩ = ρ' ⟨j.1, _⟩ := e_S.injective hij
        have h2 : (⟨i.1, Nat.lt_of_lt_of_le i.2 k.2⟩ : Fin n) = ⟨j.1, _⟩ := ρ'.injective h1
        exact Fin.ext (congrArg (fun x : Fin n => x.1) h2)
      have hrel_u : ∀ i j : Fin m, u₁ i ≤ u₁ j ↔ u₂ i ≤ u₂ j := by
        intro i j
        have hi : (⟨i.1, Nat.lt_of_lt_of_le i.2 k.2⟩ : Fin n) ≤ k := by
          change i.1 ≤ k.1
          omega
        have hj : (⟨j.1, Nat.lt_of_lt_of_le j.2 k.2⟩ : Fin n) ≤ k := by
          change j.1 ≤ k.1
          omega
        rw [e_S.le_iff_le, e_S.le_iff_le]
        exact (hρ'_rel _ _ hi hj).symm
      obtain ⟨hT₁, hT₂, τ, hτ₁, hτ₂⟩ := rel_order_perm_factorization m N u₁ u₂ hu₁ hu₂ hrel_u
      have hT₁_mem : Finset.univ.image u₁ ∈ S.powersetCard m := by
        rw [Finset.mem_powersetCard]
        refine ⟨?_, hT₁⟩
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
        exact Finset.orderEmbOfFin_mem S hS _
      have hT₂_mem : Finset.univ.image u₂ ∈ S.powersetCard m := by
        rw [Finset.mem_powersetCard]
        refine ⟨?_, hT₂⟩
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
        exact Finset.orderEmbOfFin_mem S hS _
      have hc_eq : c m (Finset.univ.image u₁) = c m (Finset.univ.image u₂) :=
        hS_mono m (by omega) (by omega) _ hT₁_mem _ hT₂_mem
      have hc_τ : c m (Finset.univ.image u₁) τ = c m (Finset.univ.image u₂) τ :=
        congrFun hc_eq τ
      dsimp only [c] at hc_τ
      rw [dif_pos hT₁, dif_pos hT₂] at hc_τ
      have hp₁_eq : (fun i : Fin m => ϱ ^ (((Finset.univ.image u₁).orderEmbOfFin hT₁) (τ i)).1) =
          (fun i : Fin m => w₀ (ρ ⟨i.1, Nat.lt_of_lt_of_le i.2 k.2⟩)) := by
        funext i
        rw [hτ₁ i]
      have hp₂_eq : (fun i : Fin m => ϱ ^ (((Finset.univ.image u₂).orderEmbOfFin hT₂) (τ i)).1) =
          (fun i : Fin m => w₀ (ρ' ⟨i.1, Nat.lt_of_lt_of_le i.2 k.2⟩)) := by
        funext i
        rw [hτ₂ i]
      rw [hp₁_eq, hp₂_eq] at hc_τ
      have h_diff := h_bin_close (p_pref k ρ) (p_pref k ρ')
        (hp01 _ _).1 (hp01 _ _).2 (hp01 _ _).1 (hp01 _ _).2 hc_τ
      linarith

    have h_per_ρ : ∀ ρ : Equiv.Perm (Fin n),
        ∑ k : Fin n, w₀ (ρ k) * p_pref k ρ ≤
          w₀ j_max * (∑ k ∈ Finset.univ.filter (fun k : Fin n => (ρ k).1 = n - 1), q k ρ) +
          w₀ j_max * (1 / (M_grid : ℝ)) +
          (ε / 3) * w₀ j_max := by
      intro ρ
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin n => (ρ k).1 = n - 1)]
      have h_win_set : Finset.univ.filter (fun k : Fin n => (ρ k).1 = n - 1) = {ρ.symm j_max} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hk
          have h1 : ρ k = j_max := Fin.ext hk
          exact (Equiv.eq_symm_apply ρ).mpr h1
        · rintro rfl
          simp [j_max]
      have h_win : ∑ k ∈ Finset.univ.filter (fun k : Fin n => (ρ k).1 = n - 1),
          w₀ (ρ k) * p_pref k ρ ≤
          w₀ j_max * (∑ k ∈ Finset.univ.filter (fun k : Fin n => (ρ k).1 = n - 1), q k ρ) +
          w₀ j_max * (1 / (M_grid : ℝ)) := by
        rw [h_win_set, Finset.sum_singleton, Finset.sum_singleton, Equiv.apply_symm_apply]
        have hg := h_grid_gap (ρ.symm j_max) ρ
        have hw_pos : 0 ≤ w₀ j_max := hw₀_nonneg j_max
        nlinarith
      have h_lose : ∑ k ∈ Finset.univ.filter (fun k : Fin n => ¬ (ρ k).1 = n - 1),
          w₀ (ρ k) * p_pref k ρ ≤ (ε / 3) * w₀ j_max := by
        calc ∑ k ∈ Finset.univ.filter (fun k : Fin n => ¬ (ρ k).1 = n - 1),
              w₀ (ρ k) * p_pref k ρ
            ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n => ¬ (ρ k).1 = n - 1),
              ((ε / 3) * w₀ j_max) * p_pref k ρ := by
              apply Finset.sum_le_sum
              intro k hk
              have hk_ne : (ρ k).1 ≠ n - 1 := (Finset.mem_filter.mp hk).2
              have hk_lt : ρ k < j_max := by
                change (ρ k).1 < n - 1
                have := (ρ k).2
                omega
              have he_lt : (e_S (ρ k)).1 < (e_S j_max).1 := e_S.lt_iff_lt.mpr hk_lt
              have hw_gap : w₀ (ρ k) ≤ (ε / 3) * w₀ j_max := h_pow_gap _ _ he_lt
              exact mul_le_mul_of_nonneg_right hw_gap (hp01 _ _).1
          _ = ((ε / 3) * w₀ j_max) *
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => ¬ (ρ k).1 = n - 1), p_pref k ρ := by
              rw [← Finset.mul_sum]
          _ ≤ ((ε / 3) * w₀ j_max) * 1 := by
              apply mul_le_mul_of_nonneg_left _ (by have := hw₀_nonneg j_max; positivity)
              calc ∑ k ∈ Finset.univ.filter (fun k : Fin n => ¬ (ρ k).1 = n - 1), p_pref k ρ
                  ≤ ∑ k : Fin n, p_pref k ρ :=
                    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                      (fun k _ _ => (hp01 _ _).1)
                _ ≤ 1 := hp_sum (w₀ ∘ ρ)
          _ = (ε / 3) * w₀ j_max := mul_one _
      linarith

    have h_card_perm : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) = (Nat.factorial n : ℝ) := by
      rw [Fintype.card_perm, Fintype.card_fin]
    have h_fact_pos : 0 < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n

    have h_avg_bound :
        (1 / (Nat.factorial n : ℝ)) *
          ∑ ρ : Equiv.Perm (Fin n), ∑ k : Fin n, w₀ (ρ k) * p_pref k ρ ≤
        (invE + ε) * M_opt_of S hS := by
      have h_sum_le :
          ∑ ρ : Equiv.Perm (Fin n), ∑ k : Fin n, w₀ (ρ k) * p_pref k ρ ≤
          w₀ j_max * (∑ ρ : Equiv.Perm (Fin n),
            ∑ k ∈ Finset.univ.filter (fun k : Fin n => (ρ k).1 = n - 1), q k ρ) +
          (Nat.factorial n : ℝ) * (w₀ j_max * (1 / (M_grid : ℝ)) + (ε / 3) * w₀ j_max) := by
        calc ∑ ρ : Equiv.Perm (Fin n), ∑ k : Fin n, w₀ (ρ k) * p_pref k ρ
            ≤ ∑ ρ : Equiv.Perm (Fin n),
                (w₀ j_max * (∑ k ∈ Finset.univ.filter (fun k : Fin n => (ρ k).1 = n - 1), q k ρ) +
                  (w₀ j_max * (1 / (M_grid : ℝ)) + (ε / 3) * w₀ j_max)) := by
              apply Finset.sum_le_sum
              intro ρ _
              have := h_per_ρ ρ
              linarith
          _ = w₀ j_max * (∑ ρ : Equiv.Perm (Fin n),
                ∑ k ∈ Finset.univ.filter (fun k : Fin n => (ρ k).1 = n - 1), q k ρ) +
              (Nat.factorial n : ℝ) * (w₀ j_max * (1 / (M_grid : ℝ)) + (ε / 3) * w₀ j_max) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
                nsmul_eq_mul, h_card_perm]
      have h1 : (1 / (Nat.factorial n : ℝ)) *
          ∑ ρ : Equiv.Perm (Fin n), ∑ k : Fin n, w₀ (ρ k) * p_pref k ρ ≤
          w₀ j_max * ((1 / (Nat.factorial n : ℝ)) * ∑ ρ : Equiv.Perm (Fin n),
            ∑ k ∈ Finset.univ.filter (fun k : Fin n => (ρ k).1 = n - 1), q k ρ) +
          w₀ j_max * (1 / (M_grid : ℝ)) + (ε / 3) * w₀ j_max := by
        have h_ne : (Nat.factorial n : ℝ) ≠ 0 := ne_of_gt h_fact_pos
        have h_mul := mul_le_mul_of_nonneg_left h_sum_le (by positivity : 0 ≤ 1 / (Nat.factorial n : ℝ))
        have h_id : (1 / (Nat.factorial n : ℝ)) *
            (w₀ j_max * (∑ ρ : Equiv.Perm (Fin n),
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => (ρ k).1 = n - 1), q k ρ) +
              (Nat.factorial n : ℝ) * (w₀ j_max * (1 / (M_grid : ℝ)) + (ε / 3) * w₀ j_max)) =
            w₀ j_max * ((1 / (Nat.factorial n : ℝ)) * ∑ ρ : Equiv.Perm (Fin n),
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => (ρ k).1 = n - 1), q k ρ) +
            w₀ j_max * (1 / (M_grid : ℝ)) + (ε / 3) * w₀ j_max := by
          field_simp [h_ne]
          ring
        linarith
      have hw_eq : w₀ j_max = M_opt_of S hS := rfl
      have hM_pos' : 0 < M_opt_of S hS := hM_opt_pos S hS
      rw [hw_eq] at h1
      nlinarith

    have h_val_σ : ∀ σ : Equiv.Perm (Fin n),
        realVal (valOf (w₀ ∘ σ)) ∅ ≤ 0 ∧
        (∀ g : Fin n, realVal (valOf (w₀ ∘ σ)) {g} ≤ w₀ (σ g)) ∧
        (∀ A : Finset (Fin n), 2 ≤ A.card → realVal (valOf (w₀ ∘ σ)) A ≤ 0) := by
      intro σ
      exact h_val (w_of (⟨S, hS⟩, σ)) (hw_bounds (⟨S, hS⟩, σ))

    obtain ⟨σ, hσ⟩ := hp_red w₀ hw₀_nonneg h_val_σ
    refine ⟨(⟨S, hS⟩, σ), ?_⟩
    exact le_trans hσ (WithBot.coe_le_coe.mpr h_avg_bound)

  
  refine ⟨n, hn1, ?_, ?_⟩
  · 
    let κ : ℝ := 3 * W_max
    let valOf_A : (Fin n → ℝ) → ItemValuation n := rankOneModularVal κ
    let fam : List (ItemValuation n) :=
      (Finset.univ : Finset Idx).toList.map (fun idx => valOf_A (w_of idx))
    refine ⟨fam, ?_, ?_, ?_⟩
    · intro h_nil
      have hmem : valOf_A (w_of idx₀) ∈ fam :=
        List.mem_map_of_mem (Finset.mem_toList.mpr (Finset.mem_univ idx₀))
      rw [h_nil] at hmem
      cases hmem
    · intro v hv
      rcases List.mem_map.mp hv with ⟨idx, _, rfl⟩
      have hgs := gs_rank_one_plus_modular_props n hn1 W_max hW_max (w_of idx) (hw_bounds idx)
      obtain ⟨hκ_gs, hopt, _⟩ := hgs
      obtain ⟨_, hopt_pos⟩ := hopt (M_opt_of idx.1.1 idx.1.2) (hw_le_M_opt idx) (hw_eq_M_opt idx)
      refine ⟨hκ_gs.2.1, hκ_gs.2.2, hopt_pos, κ, fun g => w_of idx g - κ, hκ_gs.1, ?_⟩
      intro A
      rfl
    · intro alg
      have h_loc_A : ∀ (w₁ w₂ : Fin n → ℝ) (A : Finset (Fin n)),
          (∀ g ∈ A, w₁ g = w₂ g) → valOf_A w₁ A = valOf_A w₂ A := by
        intro w₁ w₂ A h_eq
        dsimp [valOf_A, rankOneModularVal]
        congr 2
        exact Finset.sum_congr rfl (fun g hg => by rw [h_eq g hg])
      have h_val_A : ∀ w : Fin n → ℝ, (∀ g : Fin n, 1 ≤ w g ∧ w g ≤ W_max) →
          realVal (valOf_A w) ∅ ≤ 0 ∧
          (∀ g : Fin n, realVal (valOf_A w) {g} ≤ w g) ∧
          (∀ A : Finset (Fin n), 2 ≤ A.card → realVal (valOf_A w) A ≤ 0) := by
        intro w hw
        obtain ⟨_, _, hreal⟩ := gs_rank_one_plus_modular_props n hn1 W_max hW_max w hw
        exact ⟨le_of_eq hreal.1, fun g => le_of_eq (hreal.2.1 g), hreal.2.2⟩
      obtain ⟨idx, hidx⟩ := h_unified valOf_A h_loc_A h_val_A alg
      have hmem : valOf_A (w_of idx) ∈ fam :=
        List.mem_map_of_mem (Finset.mem_toList.mpr (Finset.mem_univ idx))
      obtain ⟨_, hopt, _⟩ :=
        gs_rank_one_plus_modular_props n hn1 W_max hW_max (w_of idx) (hw_bounds idx)
      obtain ⟨hopt_eq, _⟩ := hopt (M_opt_of idx.1.1 idx.1.2) (hw_le_M_opt idx) (hw_eq_M_opt idx)
      refine ⟨valOf_A (w_of idx), hmem, ?_⟩
      rw [hopt_eq]
      exact hidx
  · 
    obtain ⟨M, hM_indep, hM_gs, hM_opt, hM_real, hM_loc⟩ := rank_one_matroid_props n hn1
    let mfam : List (Matroid (Fin n) × (Fin n → ℝ)) :=
      (Finset.univ : Finset Idx).toList.map (fun idx => (M, w_of idx))
    refine ⟨mfam, ?_, ?_, ?_⟩
    · intro h_nil
      have hmem : (M, w_of idx₀) ∈ mfam :=
        List.mem_map_of_mem (Finset.mem_toList.mpr (Finset.mem_univ idx₀))
      rw [h_nil] at hmem
      cases hmem
    · intro mw hmw
      rcases List.mem_map.mp hmw with ⟨idx, _, rfl⟩
      have hopt_eq := hM_opt (w_of idx) (M_opt_of idx.1.1 idx.1.2)
        (hM_opt_pos idx.1.1 idx.1.2) (hw_le_M_opt idx) (hw_eq_M_opt idx)
      refine ⟨hM_indep, hM_gs (w_of idx), ?_⟩
      rw [hopt_eq]
      exact hM_opt_pos idx.1.1 idx.1.2
    · intro alg
      have h_val_B : ∀ w : Fin n → ℝ, (∀ g : Fin n, 1 ≤ w g ∧ w g ≤ W_max) →
          realVal (weightedMatroidVal M w) ∅ ≤ 0 ∧
          (∀ g : Fin n, realVal (weightedMatroidVal M w) {g} ≤ w g) ∧
          (∀ A : Finset (Fin n), 2 ≤ A.card → realVal (weightedMatroidVal M w) A ≤ 0) := by
        intro w _
        obtain ⟨h0, h1, h2⟩ := hM_real w
        exact ⟨le_of_eq h0, fun g => le_of_eq (h1 g), h2⟩
      obtain ⟨idx, hidx⟩ := h_unified (weightedMatroidVal M) hM_loc h_val_B alg
      have hmem : (M, w_of idx) ∈ mfam :=
        List.mem_map_of_mem (Finset.mem_toList.mpr (Finset.mem_univ idx))
      have hopt_eq := hM_opt (w_of idx) (M_opt_of idx.1.1 idx.1.2)
        (hM_opt_pos idx.1.1 idx.1.2) (hw_le_M_opt idx) (hw_eq_M_opt idx)
      refine ⟨(M, w_of idx), hmem, ?_⟩
      dsimp only
      rw [hopt_eq]
      exact hidx

end

end


section NamedResults

/-- **Proposition C.1 (`prop:secretary`, Secretary embedding, `[Gnedin94, CDFS19, BHKKMO25, Dynkin63]`)**:
For every `ε > 0`, there exist `n ≥ 1`, a finite nonempty family `fam` of finite-valued GS
valuations (each `κ · min{|S|, 1} + ∑_{g ∈ S} a_g` with `κ > 0`), and a finite nonempty family
`mfam` of rank-one weighted matroids, such that every randomized non-clairvoyant online algorithm
`alg : OnlineSelectionAlg n` achieves at most `(1 / e + ε) OPT` on some member of each family. -/
theorem prop_C_1_secretary (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 1 ≤ n ∧
      (∃ fam : List (ItemValuation n),
        fam ≠ [] ∧
        (∀ v ∈ fam,
          IsGSValuation v ∧
          IsFiniteValuation v ∧
          0 < optVal v ∧
          ∃ (κ : ℝ) (a : Fin n → ℝ), 0 < κ ∧
            ∀ S : Finset (Fin n),
              v S = ((κ * (min S.card 1 : ℕ) + ∑ g ∈ S, a g : ℝ) : WithBot ℝ)) ∧
        (∀ alg : OnlineSelectionAlg n,
          ∃ v ∈ fam,
            expectedSelectionVal alg v ≤ (((invE + ε) * optVal v : ℝ) : WithBot ℝ))) ∧
      (∃ mfam : List (Matroid (Fin n) × (Fin n → ℝ)),
        mfam ≠ [] ∧
        (∀ mw ∈ mfam,
          (∀ S : Finset (Fin n), mw.1.Indep (S : Set (Fin n)) ↔ S.card ≤ 1) ∧
          IsGSValuation (weightedMatroidVal mw.1 mw.2) ∧
          0 < optVal (weightedMatroidVal mw.1 mw.2)) ∧
        (∀ alg : OnlineSelectionAlg n,
          ∃ mw ∈ mfam,
            expectedSelectionVal alg (weightedMatroidVal mw.1 mw.2) ≤
              (((invE + ε) * optVal (weightedMatroidVal mw.1 mw.2) : ℝ) : WithBot ℝ))) :=
  prop_secretary_embedding ε hε

end NamedResults

end GrossSubstitutesWelfare
