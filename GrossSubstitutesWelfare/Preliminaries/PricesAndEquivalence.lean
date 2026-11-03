import GrossSubstitutesWelfare.Defs

set_option maxHeartbeats 4000000

/-!
# Section 2.1: Prices and the Exchange Axiom (Definitions 2.1–2.2 & Theorem 2.3)

Formalizes Section 2.1 (`sec:exchange`) of *Gross Substitutes Welfare in Random Order*:
- Nonemptiness and effective-domain membership of the Kelso–Crawford demand correspondence
  `𝒟(v, p)` (`priceDemand_nonempty`);
- **Theorem 2.3 (`thm:equivalence`, `[FY03, ST15]`)**: Equivalence of Kelso–Crawford gross
  substitutes via prices (`IsGSPrices`, Definition 2.1) and the $M^\natural$-concavity exchange
  axiom (`IsGSValuation`, Definition 2.2) for extended-real valuations `v : 2^N → ℝ ∪ {-∞}`.
-/

namespace GrossSubstitutesWelfare

open Classical MeasureTheory

noncomputable section

namespace PricesAndEquivalenceInternal

/-- **Theorem 2.3 (Prices and exchanges, `thm:equivalence`)**:
A valuation `v : 2^N → ℝ ∪ {-∞}` (with `v(∅) = 0`) satisfies Kelso–Crawford gross substitutes
(`IsGSPrices`) if and only if it satisfies the $M^\natural$-concavity exchange axiom
(`IsGSValuation`). -/
def HasHereditaryDom {n : ℕ} (v : ItemValuation n) : Prop :=
  ∀ A B : Finset (Fin n), A ⊆ B → v B ≠ ⊥ → v A ≠ ⊥

def HasSubmod2 {n : ℕ} (v : ItemValuation n) : Prop :=
  ∀ (S : Finset (Fin n)) (i j : Fin n),
    i ∉ S → j ∉ S → i ≠ j → v (insert i (insert j S)) ≠ ⊥ →
      v (insert i (insert j S)) + v S ≤ v (insert i S) + v (insert j S)

def HasRGP3 {n : ℕ} (v : ItemValuation n) : Prop :=
  ∀ (S : Finset (Fin n)) (i j k : Fin n),
    i ∉ S → j ∉ S → k ∉ S → i ≠ j → i ≠ k → j ≠ k →
    v (insert i (insert j S)) ≠ ⊥ → v (insert k S) ≠ ⊥ →
      v (insert i (insert j S)) + v (insert k S) ≤
        max (v (insert i S) + v (insert j (insert k S)))
            (v (insert j S) + v (insert i (insert k S)))

def liftedProj {n : ℕ} (A : Finset (Fin n ⊕ Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => Sum.inl i ∈ A)

def liftedVal {n : ℕ} (v : ItemValuation n) (A : Finset (Fin n ⊕ Fin n)) : WithBot ℝ :=
  v (liftedProj A)

def HasEquicardBaseExchange {n : ℕ} (ω : Finset (Fin n ⊕ Fin n) → WithBot ℝ) : Prop :=
  ∀ A B : Finset (Fin n ⊕ Fin n),
    A.card = n → B.card = n → ω A ≠ ⊥ → ω B ≠ ⊥ →
    ∀ s ∈ A \ B, ∃ u ∈ B \ A, ω (insert s (B.erase u)) ≠ ⊥

def HasGrassmannPlucker2 {n : ℕ} (ω : Finset (Fin n ⊕ Fin n) → WithBot ℝ) : Prop :=
  ∀ (I : Finset (Fin n ⊕ Fin n)) (x₁ x₂ y₁ y₂ : Fin n ⊕ Fin n),
    x₁ ∉ I → x₂ ∉ I → y₁ ∉ I → y₂ ∉ I →
    x₁ ≠ x₂ → x₁ ≠ y₁ → x₁ ≠ y₂ → x₂ ≠ y₁ → x₂ ≠ y₂ → y₁ ≠ y₂ →
    ω (insert x₁ (insert x₂ I)) ≠ ⊥ → ω (insert y₁ (insert y₂ I)) ≠ ⊥ →
      ω (insert x₁ (insert x₂ I)) + ω (insert y₁ (insert y₂ I)) ≤
        max (ω (insert x₁ (insert y₁ I)) + ω (insert x₂ (insert y₂ I)))
            (ω (insert x₁ (insert y₂ I)) + ω (insert x₂ (insert y₁ I)))

end PricesAndEquivalenceInternal

section
open PricesAndEquivalenceInternal

theorem thm_gs_prices_iff_exchange (n : ℕ) (v : ItemValuation n) :
    IsGSPrices v ↔ IsGSValuation v :=
by
  have h_s1 : IsGSValuation v → IsGSPrices v := by
    intro hv
    refine ⟨hv.1, ?_⟩
    have h_util_ne_bot : ∀ (q : Fin n → ℝ) (S : Finset (Fin n)),
        priceUtility v q S ≠ ⊥ ↔ v S ≠ ⊥ := by
      intro q S
      simp [priceUtility, WithBot.add_eq_bot]
    have h_demand_ne : ∀ (q : Fin n → ℝ), ∃ S, S ∈ priceDemand v q := by
      intro q
      obtain ⟨S, -, hS_max⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset (Fin n)))
        (priceUtility v q) ⟨∅, Finset.mem_univ ∅⟩
      refine ⟨S, ?_, fun T => hS_max T (Finset.mem_univ T)⟩
      have h0 : priceUtility v q ∅ = ((0 : ℝ) : WithBot ℝ) := by
        simp [priceUtility, hv.1]
      have hle : ((0 : ℝ) : WithBot ℝ) ≤ priceUtility v q S := by
        rw [← h0]; exact hS_max ∅ (Finset.mem_univ ∅)
      intro hbot
      rw [hbot] at hle
      exact absurd hle (not_le_of_gt (WithBot.bot_lt_coe 0))
    have h_step : ∀ (p : Fin n → ℝ) (x : Fin n) (c : ℝ), p x ≤ c →
        ∀ S ∈ priceDemand v p,
          ∃ S' ∈ priceDemand v (Function.update p x c), S.erase x ⊆ S' := by
      intro p x c hxc S hS
      let p' := Function.update p x c
      have hp_le : ∀ g, p g ≤ p' g := by
        intro g
        by_cases hgx : g = x
        · subst hgx; simp [p', hxc]
        · simp [p', hgx]
      have h_util_anti : ∀ T : Finset (Fin n), priceUtility v p' T ≤ priceUtility v p T := by
        intro T
        unfold priceUtility
        have hsum : ∑ g ∈ T, p g ≤ ∑ g ∈ T, p' g := Finset.sum_le_sum (fun g _ => hp_le g)
        have hneg : ((- ∑ g ∈ T, p' g : ℝ) : WithBot ℝ) ≤ ((- ∑ g ∈ T, p g : ℝ) : WithBot ℝ) :=
          WithBot.coe_le_coe.mpr (neg_le_neg hsum)
        exact add_le_add_right hneg (v T)
      by_cases hxS : x ∈ S
      · let D := (Finset.univ : Finset (Finset (Fin n))).filter (fun T => T ∈ priceDemand v p')
        have hD_ne : D.Nonempty := by
          obtain ⟨S₀, hS₀⟩ := h_demand_ne p'
          exact ⟨S₀, Finset.mem_filter.mpr ⟨Finset.mem_univ S₀, hS₀⟩⟩
        obtain ⟨S', hS'_memD, hS'_min⟩ :=
          Finset.exists_min_image D (fun T => (S \ T).card) hD_ne
        have hS' : S' ∈ priceDemand v p' := (Finset.mem_filter.mp hS'_memD).2
        refine ⟨S', hS', ?_⟩
        by_contra h_not_sub
        rw [Finset.subset_iff] at h_not_sub
        push_neg at h_not_sub
        obtain ⟨z, hz_er, hz_not_S'⟩ := h_not_sub
        have hzx : z ≠ x := (Finset.mem_erase.mp hz_er).1
        have hzS : z ∈ S := (Finset.mem_erase.mp hz_er).2
        have hz_sdiff : z ∈ S \ S' := Finset.mem_sdiff.mpr ⟨hzS, hz_not_S'⟩
        have hvS : v S ≠ ⊥ := (h_util_ne_bot p S).mp hS.1
        have hvS' : v S' ≠ ⊥ := (h_util_ne_bot p' S').mp hS'.1
        have hex := hv.2 S S' hvS hvS' z hz_sdiff
        obtain ⟨rS, hrS⟩ := WithBot.ne_bot_iff_exists.mp hvS
        obtain ⟨rS', hrS'⟩ := WithBot.ne_bot_iff_exists.mp hvS'
        have hpz : p' z = p z := Function.update_of_ne hzx c p
        rw [le_max_iff] at hex
        rcases hex with h_tr | h_sw
        · have h_lhs_ne : v S + v S' ≠ ⊥ := by
            rw [← hrS, ← hrS', ← WithBot.coe_add]; exact WithBot.coe_ne_bot
          have h_rhs_ne : v (S.erase z) + v (insert z S') ≠ ⊥ := by
            intro hbot; rw [hbot] at h_tr; exact h_lhs_ne (le_bot_iff.mp h_tr)
          have hv1 : v (S.erase z) ≠ ⊥ := fun hb => h_rhs_ne (by simp [hb])
          have hv2 : v (insert z S') ≠ ⊥ := fun hb => h_rhs_ne (by simp [hb])
          obtain ⟨r1, hr1⟩ := WithBot.ne_bot_iff_exists.mp hv1
          obtain ⟨r2, hr2⟩ := WithBot.ne_bot_iff_exists.mp hv2
          have h_val_le : rS + rS' ≤ r1 + r2 := by
            rw [← hrS, ← hrS', ← hr1, ← hr2, ← WithBot.coe_add, ← WithBot.coe_add,
                WithBot.coe_le_coe] at h_tr
            exact h_tr
          have h_opt_S : r1 - ∑ g ∈ S.erase z, p g ≤ rS - ∑ g ∈ S, p g := by
            have h := hS.2 (S.erase z)
            simp only [priceUtility, ← hr1, ← hrS, ← WithBot.coe_add, WithBot.coe_le_coe] at h
            linarith
          have hsum_S : ∑ g ∈ S.erase z, p g + p z = ∑ g ∈ S, p g :=
            Finset.sum_erase_add S p hzS
          have hsum_S' : ∑ g ∈ insert z S', p' g = p' z + ∑ g ∈ S', p' g :=
            Finset.sum_insert hz_not_S'
          have h_opt_S' : rS' - ∑ g ∈ S', p' g ≤ r2 - ∑ g ∈ insert z S', p' g := by
            linarith
          have h_ins_dem : insert z S' ∈ priceDemand v p' := by
            refine ⟨(h_util_ne_bot p' (insert z S')).mpr hv2, fun T => ?_⟩
            refine le_trans (hS'.2 T) ?_
            simp only [priceUtility, ← hrS', ← hr2, ← WithBot.coe_add, WithBot.coe_le_coe]
            linarith
          have h_ins_D : insert z S' ∈ D :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_ins_dem⟩
          have h_min_le := hS'_min (insert z S') h_ins_D
          have h_sdiff_eq : S \ insert z S' = (S \ S').erase z := by
            ext w; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
          rw [h_sdiff_eq] at h_min_le
          exact not_lt_of_ge h_min_le (Finset.card_erase_lt_of_mem hz_sdiff)
        · have h_lhs_ne : v S + v S' ≠ ⊥ := by
            rw [← hrS, ← hrS', ← WithBot.coe_add]; exact WithBot.coe_ne_bot
          have h_nonempty : (S' \ S).Nonempty := by
            by_contra h_emp
            rw [Finset.not_nonempty_iff_eq_empty] at h_emp
            rw [h_emp, Finset.sup_empty] at h_sw
            exact h_lhs_ne (le_bot_iff.mp h_sw)
          obtain ⟨y, hy_mem, hy_max⟩ := Finset.exists_max_image (S' \ S)
            (fun y => v (insert y (S.erase z)) + v ((insert z S').erase y)) h_nonempty
          have h_le_y : v S + v S' ≤ v (insert y (S.erase z)) + v ((insert z S').erase y) :=
            le_trans h_sw (Finset.sup_le fun y' hy' => hy_max y' hy')
          have hyS' : y ∈ S' := (Finset.mem_sdiff.mp hy_mem).1
          have hy_not_S : y ∉ S := (Finset.mem_sdiff.mp hy_mem).2
          have hyx : y ≠ x := fun h => hy_not_S (h ▸ hxS)
          have hpy : p' y = p y := Function.update_of_ne hyx c p
          have h_rhs_ne : v (insert y (S.erase z)) + v ((insert z S').erase y) ≠ ⊥ := by
            intro hbot; rw [hbot] at h_le_y; exact h_lhs_ne (le_bot_iff.mp h_le_y)
          have hv1 : v (insert y (S.erase z)) ≠ ⊥ := fun hb => h_rhs_ne (by simp [hb])
          have hv2 : v ((insert z S').erase y) ≠ ⊥ := fun hb => h_rhs_ne (by simp [hb])
          obtain ⟨r1, hr1⟩ := WithBot.ne_bot_iff_exists.mp hv1
          obtain ⟨r2, hr2⟩ := WithBot.ne_bot_iff_exists.mp hv2
          have h_val_le : rS + rS' ≤ r1 + r2 := by
            rw [← hrS, ← hrS', ← hr1, ← hr2, ← WithBot.coe_add, ← WithBot.coe_add,
                WithBot.coe_le_coe] at h_le_y
            exact h_le_y
          have hy_not_er : y ∉ S.erase z := fun hm => hy_not_S (Finset.mem_erase.mp hm).2
          have hy_ins : y ∈ insert z S' := Finset.mem_insert_of_mem hyS'
          have hsum_1 : ∑ g ∈ insert y (S.erase z), p g = p y + ∑ g ∈ S.erase z, p g :=
            Finset.sum_insert hy_not_er
          have hsum_S : ∑ g ∈ S.erase z, p g + p z = ∑ g ∈ S, p g :=
            Finset.sum_erase_add S p hzS
          have hsum_2 : ∑ g ∈ (insert z S').erase y, p' g + p' y = ∑ g ∈ insert z S', p' g :=
            Finset.sum_erase_add (insert z S') p' hy_ins
          have hsum_S' : ∑ g ∈ insert z S', p' g = p' z + ∑ g ∈ S', p' g :=
            Finset.sum_insert hz_not_S'
          have h_opt_S : r1 - ∑ g ∈ insert y (S.erase z), p g ≤ rS - ∑ g ∈ S, p g := by
            have h := hS.2 (insert y (S.erase z))
            simp only [priceUtility, ← hr1, ← hrS, ← WithBot.coe_add, WithBot.coe_le_coe] at h
            linarith
          have h_opt_S' : rS' - ∑ g ∈ S', p' g ≤ r2 - ∑ g ∈ (insert z S').erase y, p' g := by
            linarith
          let S'' := (insert z S').erase y
          have h_sw_dem : S'' ∈ priceDemand v p' := by
            refine ⟨(h_util_ne_bot p' S'').mpr hv2, fun T => ?_⟩
            refine le_trans (hS'.2 T) ?_
            simp only [S'', priceUtility, ← hrS', ← hr2, ← WithBot.coe_add, WithBot.coe_le_coe]
            linarith
          have h_sw_D : S'' ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_sw_dem⟩
          have h_min_le := hS'_min S'' h_sw_D
          have h_sdiff_eq : S \ S'' = (S \ S').erase z := by
            ext w
            simp only [S'', Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
            constructor
            · rintro ⟨hwS, hnot⟩
              have hwy : w ≠ y := fun h => hy_not_S (h ▸ hwS)
              exact ⟨fun hwz => hnot ⟨hwy, Or.inl hwz⟩, hwS, fun hwS' => hnot ⟨hwy, Or.inr hwS'⟩⟩
            · rintro ⟨hwz, hwS, hwS'⟩
              exact ⟨hwS, fun ⟨_, h⟩ => h.elim hwz hwS'⟩
          rw [h_sdiff_eq] at h_min_le
          exact not_lt_of_ge h_min_le (Finset.card_erase_lt_of_mem hz_sdiff)
      · refine ⟨S, ?_, Finset.erase_subset x S⟩
        have h_eq : priceUtility v p' S = priceUtility v p S := by
          unfold priceUtility
          congr 2
          congr 1
          refine Finset.sum_congr rfl (fun g hg => ?_)
          have hgx : g ≠ x := fun h => hxS (h ▸ hg)
          exact Function.update_of_ne hgx c p
        refine ⟨h_eq.symm ▸ hS.1, fun T => ?_⟩
        rw [h_eq]
        exact le_trans (h_util_anti T) (hS.2 T)
    suffices h_ind : ∀ (m : ℕ) (p p' : Fin n → ℝ),
        (Finset.univ.filter (fun g => p g < p' g)).card = m →
        (∀ g, p g ≤ p' g) →
        ∀ S ∈ priceDemand v p, ∃ S' ∈ priceDemand v p',
          S.filter (fun g => p g = p' g) ⊆ S' by
      intro p p' hle S hS
      exact h_ind _ p p' rfl hle S hS
    intro m
    induction m with
    | zero =>
      intro p p' hcard hle S hS
      have hp_eq : p = p' := by
        funext g
        have hnot : ¬ (p g < p' g) := by
          have hempty := Finset.card_eq_zero.mp hcard
          intro hlt
          have hmem : g ∈ Finset.univ.filter (fun g => p g < p' g) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ g, hlt⟩
          rw [hempty] at hmem
          exact Finset.notMem_empty g hmem
        exact le_antisymm (hle g) (not_lt.mp hnot)
      subst hp_eq
      exact ⟨S, hS, Finset.filter_subset _ S⟩
    | succ m ih =>
      intro p p' hcard hle S hS
      have hne : (Finset.univ.filter (fun g => p g < p' g)).Nonempty :=
        Finset.card_pos.mp (by omega)
      obtain ⟨x, hx_mem⟩ := hne
      have hx_lt : p x < p' x := (Finset.mem_filter.mp hx_mem).2
      let p₁ := Function.update p x (p' x)
      obtain ⟨S₁, hS₁_dem, hS₁_sub⟩ := h_step p x (p' x) (le_of_lt hx_lt) S hS
      have hle₁ : ∀ g, p₁ g ≤ p' g := by
        intro g
        by_cases hgx : g = x
        · subst hgx; simp [p₁]
        · simp [p₁, hgx, hle g]
      have hfilt_eq : Finset.univ.filter (fun g => p₁ g < p' g) =
          (Finset.univ.filter (fun g => p g < p' g)).erase x := by
        ext g
        by_cases hgx : g = x
        · subst hgx; simp [p₁]
        · simp [p₁, hgx]
      have hcard₁ : (Finset.univ.filter (fun g => p₁ g < p' g)).card = m := by
        rw [hfilt_eq, Finset.card_erase_of_mem hx_mem]
        omega
      obtain ⟨S', hS'_dem, hS'_sub⟩ := ih p₁ p' hcard₁ hle₁ S₁ hS₁_dem
      refine ⟨S', hS'_dem, fun g hg => hS'_sub ?_⟩
      have hgS : g ∈ S := (Finset.mem_filter.mp hg).1
      have hgp : p g = p' g := (Finset.mem_filter.mp hg).2
      have hgx : g ≠ x := by
        intro heq; subst heq; linarith
      refine Finset.mem_filter.mpr ⟨hS₁_sub (Finset.mem_erase.mpr ⟨hgx, hgS⟩), ?_⟩
      simp [p₁, hgx, hgp]

  have h_s2 : IsGSPrices v → HasHereditaryDom v ∧ HasSubmod2 v := by
    clear h_s1
    intro hp_gs
    obtain ⟨r, hr_coe⟩ : ∃ r : Finset (Fin n) → ℝ,
        ∀ T, v T ≠ ⊥ → ((r T : ℝ) : WithBot ℝ) = v T := by
      refine ⟨fun T => (v T).unbotD 0, fun T hT => ?_⟩
      obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.mp hT
      simp [← hx]
    have h_util_coe : ∀ (q : Fin n → ℝ) (T : Finset (Fin n)), v T ≠ ⊥ →
        priceUtility v q T = ((r T - ∑ g ∈ T, q g : ℝ) : WithBot ℝ) := by
      intro q T hT
      simp [priceUtility, ← hr_coe T hT, ← WithBot.coe_add, sub_eq_add_neg]
    have h_util_ne_bot : ∀ (q : Fin n → ℝ) (T : Finset (Fin n)),
        priceUtility v q T ≠ ⊥ ↔ v T ≠ ⊥ := by
      intro q T
      simp [priceUtility, WithBot.add_eq_bot]
    obtain ⟨C, hC_pos, hr_lt⟩ : ∃ C : ℝ, 0 < C ∧ ∀ T : Finset (Fin n), |r T| < C := by
      refine ⟨1 + ∑ T : Finset (Fin n), |r T|, ?_, fun T => ?_⟩
      · have hsum : 0 ≤ ∑ T : Finset (Fin n), |r T| :=
          Finset.sum_nonneg (fun _ _ => abs_nonneg _)
        linarith
      · have hle : |r T| ≤ ∑ S : Finset (Fin n), |r S| :=
          Finset.single_le_sum (fun S _ => abs_nonneg (r S)) (Finset.mem_univ T)
        linarith
    have hr_diff : ∀ T₁ T₂ : Finset (Fin n), -2 * C < r T₁ - r T₂ := by
      intro T₁ T₂
      have h1 := abs_lt.mp (hr_lt T₁)
      have h2 := abs_lt.mp (hr_lt T₂)
      linarith
    have h_split : ∀ (U V : Finset (Fin n)) (q : Fin n → ℝ),
        ∑ g ∈ U, q g = ∑ g ∈ U ∩ V, q g + ∑ g ∈ U \ V, q g := by
      intro U V q
      have hdisj : Disjoint (U ∩ V) (U \ V) :=
        Finset.disjoint_left.mpr (fun g hg1 hg2 =>
          (Finset.mem_sdiff.mp hg2).2 (Finset.mem_inter.mp hg1).2)
      rw [← Finset.sum_union hdisj]
      congr 1
      ext g; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
    have h_hered : HasHereditaryDom v := by
      intro A B hAB hvB
      let M : ℝ := 3 * C
      let M' : ℝ := ((n : ℝ) + 2) * M
      let p : Fin n → ℝ := fun g => if g ∈ B then -M else M
      let p' : Fin n → ℝ := fun g => if g ∈ A then -M else M'
      have h_sum_p : ∀ T : Finset (Fin n),
          ∑ g ∈ T, p g = -M * ((T ∩ B).card : ℝ) + M * ((T \ B).card : ℝ) := by
        intro T
        rw [h_split T B p]
        have h1 : ∑ g ∈ T ∩ B, p g = -M * ((T ∩ B).card : ℝ) := by
          have hc : ∀ g ∈ T ∩ B, p g = -M := fun g hg => if_pos (Finset.mem_inter.mp hg).2
          rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]; ring
        have h2 : ∑ g ∈ T \ B, p g = M * ((T \ B).card : ℝ) := by
          have hc : ∀ g ∈ T \ B, p g = M := fun g hg => if_neg (Finset.mem_sdiff.mp hg).2
          rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]; ring
        rw [h1, h2]
      have hB_dem : B ∈ priceDemand v p := by
        refine ⟨(h_util_ne_bot p B).mpr hvB, fun T => ?_⟩
        by_cases hvT : v T = ⊥
        · simp [priceUtility, hvT]
        · rw [h_util_coe p T hvT, h_util_coe p B hvB, WithBot.coe_le_coe]
          by_cases hTB : T = B
          · subst hTB; exact le_rfl
          · have h_card_B : (B.card : ℝ) = ((T ∩ B).card : ℝ) + ((B \ T).card : ℝ) := by
              have hc : B.card = (T ∩ B).card + (B \ T).card := by
                have h := Finset.card_sdiff_add_card_inter B T
                rw [Finset.inter_comm] at h; omega
              exact_mod_cast hc
            have h_sum_B : ∑ g ∈ B, p g = -M * (B.card : ℝ) := by
              rw [h_sum_p B, Finset.inter_self, Finset.sdiff_self, Finset.card_empty, Nat.cast_zero]
              ring
            have h_pos_sd : 1 ≤ (B \ T).card + (T \ B).card := by
              by_contra h0
              have hBT0 : (B \ T).card = 0 := by omega
              have hTB0 : (T \ B).card = 0 := by omega
              have h1 := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hBT0)
              have h2 := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hTB0)
              exact hTB (Finset.Subset.antisymm h2 h1)
            have h_pos_sd_r : (1 : ℝ) ≤ ((B \ T).card : ℝ) + ((T \ B).card : ℝ) := by
              exact_mod_cast h_pos_sd
            have h_m_ge : M ≤ M * (((B \ T).card : ℝ) + ((T \ B).card : ℝ)) := by
              nlinarith
            have hd := hr_diff B T
            rw [h_sum_p T, h_sum_B, h_card_B, mul_add]
            linarith
      have hp_le : ∀ g, p g ≤ p' g := by
        intro g
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        by_cases hgA : g ∈ A
        · have hgB : g ∈ B := hAB hgA
          simp [p, p', hgA, hgB]
        · by_cases hgB : g ∈ B
          · simp only [p, p', hgA, hgB, ↓reduceIte]; nlinarith
          · simp only [p, p', hgA, hgB, ↓reduceIte]; nlinarith
      obtain ⟨S', hS'_dem, hS'_sub⟩ := hp_gs.2 p p' hp_le B hB_dem
      have hAS' : A ⊆ S' := by
        intro g hgA
        refine hS'_sub (Finset.mem_filter.mpr ⟨hAB hgA, ?_⟩)
        simp [p, p', hgA, hAB hgA]
      have hvS' : v S' ≠ ⊥ := (h_util_ne_bot p' S').mp hS'_dem.1
      by_cases hS'A : S' = A
      · exact hS'A ▸ hvS'
      · exfalso
        have h_ssub : A ⊂ S' := ssubset_iff_subset_ne.mpr ⟨hAS', Ne.symm hS'A⟩
        obtain ⟨g₀, hg₀S', hg₀A⟩ := Finset.exists_of_ssubset h_ssub
        have h_sd_pos : 1 ≤ (S' \ A).card :=
          Finset.card_pos.mpr ⟨g₀, Finset.mem_sdiff.mpr ⟨hg₀S', hg₀A⟩⟩
        have h_sd_r : (1 : ℝ) ≤ ((S' \ A).card : ℝ) := by exact_mod_cast h_sd_pos
        have hA_le_n : A.card ≤ n := by
          simpa using Finset.card_le_univ A
        have hA_le_nr : (A.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hA_le_n
        have h_sum_S' : ∑ g ∈ S', p' g = -M * (A.card : ℝ) + M' * ((S' \ A).card : ℝ) := by
          rw [h_split S' A p', Finset.inter_eq_right.mpr hAS']
          have h1 : ∑ g ∈ A, p' g = -M * (A.card : ℝ) := by
            have hc : ∀ g ∈ A, p' g = -M := fun g hg => if_pos hg
            rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]; ring
          have h2 : ∑ g ∈ S' \ A, p' g = M' * ((S' \ A).card : ℝ) := by
            have hc : ∀ g ∈ S' \ A, p' g = M' := fun g hg => if_neg (Finset.mem_sdiff.mp hg).2
            rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]; ring
          rw [h1, h2]
        have h_emp_le := hS'_dem.2 ∅
        have h_emp_zero : priceUtility v p' ∅ = ((0 : ℝ) : WithBot ℝ) := by
          simp [priceUtility, hp_gs.1]
        rw [h_emp_zero, h_util_coe p' S' hvS', WithBot.coe_le_coe, h_sum_S'] at h_emp_le
        have hrS'_lt : r S' < C := (abs_lt.mp (hr_lt S')).2
        have hM_nonneg : 0 ≤ M := by dsimp [M]; linarith
        have hm1 : M * (A.card : ℝ) ≤ M * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hA_le_nr hM_nonneg
        have hM'_nonneg : 0 ≤ M' := by
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          dsimp [M']; nlinarith
        have hm2 : M' ≤ M' * ((S' \ A).card : ℝ) := by nlinarith
        have hm_diff : M' - M * (n : ℝ) = 2 * M := by dsimp [M']; ring
        linarith
    refine ⟨h_hered, ?_⟩
    intro S i j hiS hjS hij hvSij
    let Sij := insert i (insert j S)
    let Si := insert i S
    let Sj := insert j S
    have hvS : v S ≠ ⊥ := h_hered S Sij
      (Finset.Subset.trans (Finset.subset_insert j S) (Finset.subset_insert i Sj)) hvSij
    have hvSi : v Si ≠ ⊥ := h_hered Si Sij
      (Finset.insert_subset_insert i (Finset.subset_insert j S)) hvSij
    have hvSj : v Sj ≠ ⊥ := h_hered Sj Sij (Finset.subset_insert i Sj) hvSij
    let pi : ℝ := r Sij - r Sj
    let K : ℝ := 6 * C
    have hpi_gt : -2 * C < pi := hr_diff Sij Sj
    have hpi_lt : pi < 2 * C := by
      have := hr_diff Sj Sij; dsimp [pi]; linarith
    let p : Fin n → ℝ := fun g => if g ∈ Sj then -K else if g = i then pi else K
    have hi_not_Sj : i ∉ Sj := by simp [Sj, hij, hiS]
    have h_sum_p : ∀ T : Finset (Fin n),
        ∑ g ∈ T, p g = -K * ((T ∩ Sj).card : ℝ) + (if i ∈ T then pi else 0) +
          K * ((T \ Sij).card : ℝ) := by
      intro T
      rw [h_split T Sj p, h_split (T \ Sj) {i} p]
      have h1 : ∑ g ∈ T ∩ Sj, p g = -K * ((T ∩ Sj).card : ℝ) := by
        have hc : ∀ g ∈ T ∩ Sj, p g = -K := fun g hg => if_pos (Finset.mem_inter.mp hg).2
        rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]; ring
      have h2 : ∑ g ∈ (T \ Sj) ∩ {i}, p g = (if i ∈ T then pi else 0) := by
        by_cases hiT : i ∈ T
        · have heq : (T \ Sj) ∩ {i} = {i} := by
            ext g; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton]
            constructor
            · exact And.right
            · rintro rfl; exact ⟨⟨hiT, hi_not_Sj⟩, rfl⟩
          rw [heq, if_pos hiT, Finset.sum_singleton]
          simp [p, hi_not_Sj]
        · have heq : (T \ Sj) ∩ {i} = ∅ := by
            ext g; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton,
              Finset.notMem_empty, iff_false]
            rintro ⟨⟨hgT, _⟩, rfl⟩; exact hiT hgT
          rw [heq, if_neg hiT, Finset.sum_empty]
      have h3 : ∑ g ∈ (T \ Sj) \ {i}, p g = K * ((T \ Sij).card : ℝ) := by
        have heq : (T \ Sj) \ {i} = T \ Sij := by
          ext g; simp only [Sij, Sj, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
          clear hp_gs hr_coe h_util_coe h_util_ne_bot hr_lt hr_diff h_split h_hered
          tauto
        rw [heq]
        have hc : ∀ g ∈ T \ Sij, p g = K := by
          intro g hg
          have hnot : g ∉ Sij := (Finset.mem_sdiff.mp hg).2
          have hgSj : g ∉ Sj := fun hm => hnot (Finset.mem_insert_of_mem hm)
          have hgi : g ≠ i := fun he => hnot (he ▸ Finset.mem_insert_self i Sj)
          simp [p, hgSj, hgi]
        rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]; ring
      rw [h1, h2, h3, add_assoc]
    have hSij_dem : Sij ∈ priceDemand v p := by
      refine ⟨(h_util_ne_bot p Sij).mpr hvSij, fun T => ?_⟩
      by_cases hvT : v T = ⊥
      · simp [priceUtility, hvT]
      · rw [h_util_coe p T hvT, h_util_coe p Sij hvSij, WithBot.coe_le_coe]
        have h_sum_Sij : ∑ g ∈ Sij, p g = -K * (Sj.card : ℝ) + pi := by
          have h_inter : Sij ∩ Sj = Sj :=
            Finset.inter_eq_right.mpr (Finset.subset_insert i Sj)
          rw [h_sum_p Sij, h_inter, if_pos (Finset.mem_insert_self i Sj),
              Finset.sdiff_self, Finset.card_empty]
          ring
        by_cases h_loc : Sj ⊆ T ∧ T ⊆ Sij
        · by_cases hiT : i ∈ T
          · have hT_eq : T = Sij := by
              refine Finset.Subset.antisymm h_loc.2 ?_
              exact Finset.insert_subset hiT h_loc.1
            subst hT_eq; exact le_rfl
          · have hT_eq : T = Sj := by
              refine Finset.Subset.antisymm ?_ h_loc.1
              intro g hgT
              rcases Finset.mem_insert.mp (h_loc.2 hgT) with rfl | hgSj
              · exact absurd hgT hiT
              · exact hgSj
            subst hT_eq
            rw [h_sum_p Sj, Finset.inter_self, if_neg hi_not_Sj,
                Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_insert i Sj),
                Finset.card_empty, Nat.cast_zero, h_sum_Sij]
            dsimp [pi]; linarith
        · have h_sd_pos : 1 ≤ (Sj \ T).card + (T \ Sij).card := by
            by_contra h0
            have h1 : (Sj \ T).card = 0 := by omega
            have h2 : (T \ Sij).card = 0 := by omega
            exact h_loc ⟨Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp h1),
                         Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp h2)⟩
          have h_sd_r : (1 : ℝ) ≤ ((Sj \ T).card : ℝ) + ((T \ Sij).card : ℝ) := by
            exact_mod_cast h_sd_pos
          have h_card_Sj : (Sj.card : ℝ) = ((T ∩ Sj).card : ℝ) + ((Sj \ T).card : ℝ) := by
            have hc : Sj.card = (T ∩ Sj).card + (Sj \ T).card := by
              have h := Finset.card_sdiff_add_card_inter Sj T
              rw [Finset.inter_comm] at h; omega
            exact_mod_cast hc
          have h_if_gt : -2 * C < (if i ∈ T then pi else 0) := by
            split_ifs <;> linarith
          have hd := hr_diff Sj T
          have hK_ge : K ≤ K * (((Sj \ T).card : ℝ) + ((T \ Sij).card : ℝ)) := by nlinarith
          rw [h_sum_p T, h_sum_Sij, h_card_Sj, mul_add]
          dsimp [pi, K] at hK_ge ⊢
          linarith
    let p' := Function.update p j K
    have hp_le : ∀ g, p g ≤ p' g := by
      intro g
      by_cases hgj : g = j
      · subst hgj
        have hjSj : g ∈ Sj := Finset.mem_insert_self g S
        simp only [p, p', hjSj, Function.update_self, ↓reduceIte]; linarith
      · simp [p', hgj]
    obtain ⟨S', hS'_dem, hS'_sub⟩ := hp_gs.2 p p' hp_le Sij hSij_dem
    have hSi_sub_S' : Si ⊆ S' := by
      intro g hgSi
      have hgj : g ≠ j := by
        rcases Finset.mem_insert.mp hgSi with rfl | hgS
        · exact hij
        · exact fun h => hjS (h ▸ hgS)
      have hgSij : g ∈ Sij := by
        rcases Finset.mem_insert.mp hgSi with rfl | hgS
        · exact Finset.mem_insert_self g Sj
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hgS)
      exact hS'_sub (Finset.mem_filter.mpr ⟨hgSij, by simp [p', hgj]⟩)
    have hvS' : v S' ≠ ⊥ := (h_util_ne_bot p' S').mp hS'_dem.1
    have hS'_eq_Si : S' = Si := by
      by_contra hne
      have h_ssub : Si ⊂ S' := ssubset_iff_subset_ne.mpr ⟨hSi_sub_S', Ne.symm hne⟩
      obtain ⟨g₀, hg₀S', hg₀Si⟩ := Finset.exists_of_ssubset h_ssub
      have h_sd_pos : 1 ≤ (S' \ Si).card :=
        Finset.card_pos.mpr ⟨g₀, Finset.mem_sdiff.mpr ⟨hg₀S', hg₀Si⟩⟩
      have h_sd_r : (1 : ℝ) ≤ ((S' \ Si).card : ℝ) := by exact_mod_cast h_sd_pos
      have h_sum_S' : ∑ g ∈ S', p' g = ∑ g ∈ Si, p' g + K * ((S' \ Si).card : ℝ) := by
        rw [h_split S' Si p', Finset.inter_eq_right.mpr hSi_sub_S']
        congr 1
        have hc : ∀ g ∈ S' \ Si, p' g = K := by
          intro g hg
          have hgSi' : g ∉ Si := (Finset.mem_sdiff.mp hg).2
          by_cases hgj : g = j
          · subst hgj; simp [p']
          · have hgSj : g ∉ Sj := by
              intro hm
              rcases Finset.mem_insert.mp hm with h1 | h2
              · exact hgj h1
              · exact hgSi' (Finset.mem_insert_of_mem h2)
            have hgi : g ≠ i := fun h => hgSi' (h ▸ Finset.mem_insert_self i S)
            simp [p', p, hgj, hgSj, hgi]
        rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]; ring
      have h_opt := hS'_dem.2 Si
      rw [h_util_coe p' Si hvSi, h_util_coe p' S' hvS', WithBot.coe_le_coe, h_sum_S'] at h_opt
      have hd := hr_diff Si S'
      have hK_ge : K ≤ K * ((S' \ Si).card : ℝ) := by nlinarith
      dsimp [K] at hK_ge
      linarith
    have hSi_dem : Si ∈ priceDemand v p' := hS'_eq_Si ▸ hS'_dem
    have h_cmp := hSi_dem.2 S
    rw [h_util_coe p' S hvS, h_util_coe p' Si hvSi, WithBot.coe_le_coe] at h_cmp
    have h_sum_Si : ∑ g ∈ Si, p' g = pi + ∑ g ∈ S, p' g := by
      rw [Finset.sum_insert hiS]
      have hp'i : p' i = pi := by
        simp [p', p, hij, hi_not_Sj]
      rw [hp'i]
    rw [h_sum_Si] at h_cmp
    rw [← hr_coe Sij hvSij, ← hr_coe S hvS, ← hr_coe Si hvSi, ← hr_coe Sj hvSj,
        ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
    dsimp [pi] at h_cmp
    linarith

  have h_s3 : IsGSPrices v → HasHereditaryDom v → HasSubmod2 v → HasRGP3 v := by
    clear h_s1 h_s2
    intro hp_gs h_hered h_submod S i j k hiS hjS hkS hij hik hjk hvSij hvSk
    by_contra h_not_le
    push_neg at h_not_le
    let Sij := insert i (insert j S)
    let Sk := insert k S
    let Si := insert i S
    let Sj := insert j S
    let Sjk := insert j (insert k S)
    let Sik := insert i (insert k S)
    let Sijk := insert i (insert j (insert k S))
    have hvS : v S ≠ ⊥ := h_hered S Sk (Finset.subset_insert k S) hvSk
    have hvSi : v Si ≠ ⊥ := h_hered Si Sij
      (Finset.insert_subset_insert i (Finset.subset_insert j S)) hvSij
    have hvSj : v Sj ≠ ⊥ := h_hered Sj Sij (Finset.subset_insert i Sj) hvSij
    obtain ⟨r, hr_coe⟩ : ∃ r : Finset (Fin n) → ℝ,
        ∀ T, v T ≠ ⊥ → ((r T : ℝ) : WithBot ℝ) = v T := by
      refine ⟨fun T => (v T).unbotD 0, fun T hT => ?_⟩
      obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.mp hT
      simp [← hx]
    have h_util_coe : ∀ (q : Fin n → ℝ) (T : Finset (Fin n)), v T ≠ ⊥ →
        priceUtility v q T = ((r T - ∑ g ∈ T, q g : ℝ) : WithBot ℝ) := by
      intro q T hT
      simp [priceUtility, ← hr_coe T hT, ← WithBot.coe_add, sub_eq_add_neg]
    have h_util_ne_bot : ∀ (q : Fin n → ℝ) (T : Finset (Fin n)),
        priceUtility v q T ≠ ⊥ ↔ v T ≠ ⊥ := by
      intro q T
      simp [priceUtility, WithBot.add_eq_bot]
    let w : Finset (Fin n) → ℝ := fun T => r T - r S
    have h_lt1 : v Si + v Sjk < v Sij + v Sk := lt_of_le_of_lt (le_max_left _ _) h_not_le
    have h_lt2 : v Sj + v Sik < v Sij + v Sk := lt_of_le_of_lt (le_max_right _ _) h_not_le
    let δ₁ : ℝ := if v Sjk = ⊥ then 1 else w Sij + w Sk - w Si - w Sjk
    let δ₂ : ℝ := if v Sik = ⊥ then 1 else w Sij + w Sk - w Sj - w Sik
    have hδ₁_pos : 0 < δ₁ := by
      dsimp [δ₁]
      split_ifs with hb
      · norm_num
      · rw [← hr_coe Si hvSi, ← hr_coe Sjk hb, ← hr_coe Sij hvSij, ← hr_coe Sk hvSk,
            ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_lt_coe] at h_lt1
        dsimp [w]; linarith
    have hδ₂_pos : 0 < δ₂ := by
      dsimp [δ₂]
      split_ifs with hb
      · norm_num
      · rw [← hr_coe Sj hvSj, ← hr_coe Sik hb, ← hr_coe Sij hvSij, ← hr_coe Sk hvSk,
            ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_lt_coe] at h_lt2
        dsimp [w]; linarith
    obtain ⟨φ, hφ_pos, hφ_le1, hφ_le2⟩ : ∃ φ : ℝ, 0 < φ ∧ φ ≤ δ₁ ∧ φ ≤ δ₂ :=
      ⟨min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, min_le_left _ _, min_le_right _ _⟩
    let pi : ℝ := w Sij - w Sj - (1 / 2 : ℝ) * φ
    let pj : ℝ := w Sij - w Si - (1 / 2 : ℝ) * φ
    let pk : ℝ := w Sk + w Sij - w Si - w Sj - φ
    obtain ⟨B, hB_pos, hr_lt_B, h_loc_B⟩ :
        ∃ B : ℝ, 0 < B ∧ (∀ T : Finset (Fin n), |r T| < B) ∧ -B < -(|pi| + |pj| + |pk|) := by
      refine ⟨1 + |pi| + |pj| + |pk| + ∑ T : Finset (Fin n), |r T|, ?_, fun T => ?_, ?_⟩
      · have hsum : 0 ≤ ∑ T : Finset (Fin n), |r T| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
        have := abs_nonneg pi; have := abs_nonneg pj; have := abs_nonneg pk
        linarith
      · have hle : |r T| ≤ ∑ U : Finset (Fin n), |r U| :=
          Finset.single_le_sum (fun U _ => abs_nonneg (r U)) (Finset.mem_univ T)
        have := abs_nonneg pi; have := abs_nonneg pj; have := abs_nonneg pk
        linarith
      · have hsum : 0 ≤ ∑ U : Finset (Fin n), |r U| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
        linarith
    let M : ℝ := 6 * B
    let p : Fin n → ℝ := fun g =>
      if g ∈ S then -M else if g = i then pi else if g = j then pj else if g = k then pk else M
    have h_split : ∀ (U V : Finset (Fin n)) (q : Fin n → ℝ),
        ∑ g ∈ U, q g = ∑ g ∈ U ∩ V, q g + ∑ g ∈ U \ V, q g := by
      intro U V q
      have hdisj : Disjoint (U ∩ V) (U \ V) :=
        Finset.disjoint_left.mpr (fun g hg1 hg2 =>
          (Finset.mem_sdiff.mp hg2).2 (Finset.mem_inter.mp hg1).2)
      rw [← Finset.sum_union hdisj]
      congr 1
      ext g; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      clear hp_gs h_hered h_submod hr_coe h_util_coe h_util_ne_bot hr_lt_B
      tauto
    have h_sum_p : ∀ T : Finset (Fin n),
        ∑ g ∈ T, p g = -M * ((T ∩ S).card : ℝ) +
          (if i ∈ T then pi else 0) + (if j ∈ T then pj else 0) + (if k ∈ T then pk else 0) +
          M * ((T \ Sijk).card : ℝ) := by
      intro T
      rw [h_split T S p, h_split (T \ S) {i} p, h_split ((T \ S) \ {i}) {j} p,
          h_split (((T \ S) \ {i}) \ {j}) {k} p]
      have h1 : ∑ g ∈ T ∩ S, p g = -M * ((T ∩ S).card : ℝ) := by
        have hc : ∀ g ∈ T ∩ S, p g = -M := fun g hg => if_pos (Finset.mem_inter.mp hg).2
        rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]; ring
      have h_i : ∑ g ∈ (T \ S) ∩ {i}, p g = (if i ∈ T then pi else 0) := by
        by_cases hiT : i ∈ T
        · have heq : (T \ S) ∩ {i} = {i} := by
            ext g; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton]
            exact ⟨And.right, fun h => ⟨⟨h ▸ hiT, h ▸ hiS⟩, h⟩⟩
          rw [heq, if_pos hiT, Finset.sum_singleton]; simp [p, hiS]
        · have heq : (T \ S) ∩ {i} = ∅ := by
            ext g; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton,
              Finset.notMem_empty, iff_false]
            rintro ⟨⟨hgT, _⟩, rfl⟩; exact hiT hgT
          rw [heq, if_neg hiT, Finset.sum_empty]
      have h_j : ∑ g ∈ ((T \ S) \ {i}) ∩ {j}, p g = (if j ∈ T then pj else 0) := by
        by_cases hjT : j ∈ T
        · have heq : ((T \ S) \ {i}) ∩ {j} = {j} := by
            ext g; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton]
            exact ⟨And.right, fun h => ⟨⟨⟨h ▸ hjT, h ▸ hjS⟩, h ▸ hij.symm⟩, h⟩⟩
          rw [heq, if_pos hjT, Finset.sum_singleton]; simp [p, hjS, hij.symm]
        · have heq : ((T \ S) \ {i}) ∩ {j} = ∅ := by
            ext g; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton,
              Finset.notMem_empty, iff_false]
            rintro ⟨⟨⟨hgT, _⟩, _⟩, rfl⟩; exact hjT hgT
          rw [heq, if_neg hjT, Finset.sum_empty]
      have h_k : ∑ g ∈ (((T \ S) \ {i}) \ {j}) ∩ {k}, p g = (if k ∈ T then pk else 0) := by
        by_cases hkT : k ∈ T
        · have heq : (((T \ S) \ {i}) \ {j}) ∩ {k} = {k} := by
            ext g; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton]
            exact ⟨And.right,
              fun h => ⟨⟨⟨⟨h ▸ hkT, h ▸ hkS⟩, h ▸ hik.symm⟩, h ▸ hjk.symm⟩, h⟩⟩
          rw [heq, if_pos hkT, Finset.sum_singleton]; simp [p, hkS, hik.symm, hjk.symm]
        · have heq : (((T \ S) \ {i}) \ {j}) ∩ {k} = ∅ := by
            ext g; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton,
              Finset.notMem_empty, iff_false]
            rintro ⟨⟨⟨⟨hgT, _⟩, _⟩, _⟩, rfl⟩; exact hkT hgT
          rw [heq, if_neg hkT, Finset.sum_empty]
      have h_rem : ∑ g ∈ (((T \ S) \ {i}) \ {j}) \ {k}, p g = M * ((T \ Sijk).card : ℝ) := by
        have heq : (((T \ S) \ {i}) \ {j}) \ {k} = T \ Sijk := by
          ext g
          simp only [Sijk, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
          clear hp_gs h_hered h_submod hr_coe h_util_coe h_util_ne_bot hr_lt_B h_split h1 h_i h_j h_k
          tauto
        rw [heq]
        have hc : ∀ g ∈ T \ Sijk, p g = M := by
          intro g hg
          have hnot : g ∉ Sijk := (Finset.mem_sdiff.mp hg).2
          simp only [Sijk, Finset.mem_insert] at hnot
          push_neg at hnot
          simp [p, hnot.1, hnot.2.1, hnot.2.2.1, hnot.2.2.2]
        rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]; ring
      rw [h1, h_i, h_j, h_k, h_rem]; ring
    have h_sub_ij : r Sij + r S ≤ r Si + r Sj := by
      have hs := h_submod S i j hiS hjS hij hvSij
      rw [← hr_coe Sij hvSij, ← hr_coe S hvS, ← hr_coe Si hvSi, ← hr_coe Sj hvSj,
          ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe] at hs
      exact hs
    let u_star : ℝ := r S + M * (S.card : ℝ) + (w Si + w Sj - w Sij + φ)
    have hu_Sk : r Sk - ∑ g ∈ Sk, p g = u_star := by
      have h_inter : Sk ∩ S = S := Finset.inter_eq_right.mpr (Finset.subset_insert k S)
      have h_sd : Sk \ Sijk = ∅ := by
        rw [Finset.sdiff_eq_empty_iff_subset]
        exact Finset.Subset.trans (Finset.subset_insert j Sk) (Finset.subset_insert i Sjk)
      have hiSk : i ∉ Sk := by simp [Sk, hik, hiS]
      have hjSk : j ∉ Sk := by simp [Sk, hjk, hjS]
      have hkSk : k ∈ Sk := Finset.mem_insert_self k S
      rw [h_sum_p Sk, h_inter, h_sd, Finset.card_empty, Nat.cast_zero,
          if_neg hiSk, if_neg hjSk, if_pos hkSk]
      dsimp [u_star, pk, w]; ring
    have hu_Sij : r Sij - ∑ g ∈ Sij, p g = u_star := by
      have h_inter : Sij ∩ S = S := Finset.inter_eq_right.mpr
        (Finset.Subset.trans (Finset.subset_insert j S) (Finset.subset_insert i Sj))
      have h_sd : Sij \ Sijk = ∅ := by
        rw [Finset.sdiff_eq_empty_iff_subset]
        intro g hg
        simp only [Sij, Sijk, Finset.mem_insert] at hg ⊢
        rcases hg with rfl | rfl | hgS
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr hgS))
      have hiSij : i ∈ Sij := Finset.mem_insert_self i Sj
      have hjSij : j ∈ Sij := Finset.mem_insert_of_mem (Finset.mem_insert_self j S)
      have hkSij : k ∉ Sij := by simp [Sij, hik.symm, hjk.symm, hkS]
      rw [h_sum_p Sij, h_inter, h_sd, Finset.card_empty, Nat.cast_zero,
          if_pos hiSij, if_pos hjSij, if_neg hkSij]
      dsimp [u_star, pi, pj, w]; ring
    have h_strict_other : ∀ T : Finset (Fin n), v T ≠ ⊥ → T ≠ Sk → T ≠ Sij →
        r T - ∑ g ∈ T, p g < u_star := by
      intro T hvT hTSk hTSij
      by_cases h_loc : S ⊆ T ∧ T ⊆ Sijk
      · have h_inter : T ∩ S = S := Finset.inter_eq_right.mpr h_loc.1
        have h_sd : T \ Sijk = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr h_loc.2
        rw [h_sum_p T, h_inter, h_sd, Finset.card_empty, Nat.cast_zero, mul_zero, add_zero]
        by_cases hiT : i ∈ T <;> by_cases hjT : j ∈ T <;> by_cases hkT : k ∈ T
        · have hT_eq : T = Sijk := by
            ext g; have h1 := @h_loc.1 g; have h2 := @h_loc.2 g
            simp only [Sijk, Finset.mem_insert] at h2 ⊢
            constructor
            · exact h2
            · rintro (rfl | rfl | rfl | hgS)
              · exact hiT
              · exact hjT
              · exact hkT
              · exact h1 hgS
          subst hT_eq
          have hvSik : v Sik ≠ ⊥ := h_hered Sik Sijk (by
            intro g hg; simp only [Sik, Sijk, Finset.mem_insert] at hg ⊢
            rcases hg with rfl | rfl | hgS
            · exact Or.inl rfl
            · exact Or.inr (Or.inr (Or.inl rfl))
            · exact Or.inr (Or.inr (Or.inr hgS))) hvT
          have hvSjk : v Sjk ≠ ⊥ := h_hered Sjk Sijk
            (Finset.subset_insert i Sjk) hvT
          have h_sub_k : r Sijk + r Sk ≤ r Sik + r Sjk := by
            have hs := h_submod Sk i j (by simp [Sk, hik, hiS]) (by simp [Sk, hjk, hjS]) hij hvT
            rw [← hr_coe Sijk hvT, ← hr_coe Sk hvSk, ← hr_coe Sik hvSik, ← hr_coe Sjk hvSjk,
                ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe] at hs
            exact hs
          have hδ₁_eq : δ₁ = w Sij + w Sk - w Si - w Sjk := if_neg hvSjk
          have hδ₂_eq : δ₂ = w Sij + w Sk - w Sj - w Sik := if_neg hvSik
          simp only [hiT, hjT, hkT, ↓reduceIte]
          dsimp [u_star, pi, pj, pk, w] at hδ₁_eq hδ₂_eq ⊢
          linarith
        · exfalso; apply hTSij
          ext g; have h1 := @h_loc.1 g; have h2 := @h_loc.2 g
          simp only [Sij, Sijk, Finset.mem_insert] at h2 ⊢
          constructor
          · intro hgT
            rcases h2 hgT with rfl | rfl | rfl | hgS
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
            · exact absurd hgT hkT
            · exact Or.inr (Or.inr hgS)
          · rintro (rfl | rfl | hgS)
            · exact hiT
            · exact hjT
            · exact h1 hgS
        · have hT_eq : T = Sik := by
            ext g; have h1 := @h_loc.1 g; have h2 := @h_loc.2 g
            simp only [Sik, Sijk, Finset.mem_insert] at h2 ⊢
            constructor
            · intro hgT
              rcases h2 hgT with rfl | rfl | rfl | hgS
              · exact Or.inl rfl
              · exact absurd hgT hjT
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr hgS)
            · rintro (rfl | rfl | hgS)
              · exact hiT
              · exact hkT
              · exact h1 hgS
          subst hT_eq
          have hδ₂_eq : δ₂ = w Sij + w Sk - w Sj - w Sik := if_neg hvT
          simp only [hiT, hjT, hkT, ↓reduceIte]
          dsimp [u_star, pi, pk, w] at hδ₂_eq ⊢
          linarith
        · have hT_eq : T = Si := by
            ext g; have h1 := @h_loc.1 g; have h2 := @h_loc.2 g
            simp only [Si, Sijk, Finset.mem_insert] at h2 ⊢
            constructor
            · intro hgT
              rcases h2 hgT with rfl | rfl | rfl | hgS
              · exact Or.inl rfl
              · exact absurd hgT hjT
              · exact absurd hgT hkT
              · exact Or.inr hgS
            · rintro (rfl | hgS)
              · exact hiT
              · exact h1 hgS
          subst hT_eq
          simp only [hiT, hjT, hkT, ↓reduceIte]
          dsimp [u_star, pi, w]; linarith
        · have hT_eq : T = Sjk := by
            ext g; have h1 := @h_loc.1 g; have h2 := @h_loc.2 g
            simp only [Sjk, Sijk, Finset.mem_insert] at h2 ⊢
            constructor
            · intro hgT
              rcases h2 hgT with rfl | rfl | rfl | hgS
              · exact absurd hgT hiT
              · exact Or.inl rfl
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr hgS)
            · rintro (rfl | rfl | hgS)
              · exact hjT
              · exact hkT
              · exact h1 hgS
          subst hT_eq
          have hδ₁_eq : δ₁ = w Sij + w Sk - w Si - w Sjk := if_neg hvT
          simp only [hiT, hjT, hkT, ↓reduceIte]
          dsimp [u_star, pj, pk, w] at hδ₁_eq ⊢
          linarith
        · have hT_eq : T = Sj := by
            ext g; have h1 := @h_loc.1 g; have h2 := @h_loc.2 g
            simp only [Sj, Sijk, Finset.mem_insert] at h2 ⊢
            constructor
            · intro hgT
              rcases h2 hgT with rfl | rfl | rfl | hgS
              · exact absurd hgT hiT
              · exact Or.inl rfl
              · exact absurd hgT hkT
              · exact Or.inr hgS
            · rintro (rfl | hgS)
              · exact hjT
              · exact h1 hgS
          subst hT_eq
          simp only [hiT, hjT, hkT, ↓reduceIte]
          dsimp [u_star, pj, w]; linarith
        · exfalso; apply hTSk
          ext g; have h1 := @h_loc.1 g; have h2 := @h_loc.2 g
          simp only [Sk, Sijk, Finset.mem_insert] at h2 ⊢
          constructor
          · intro hgT
            rcases h2 hgT with rfl | rfl | rfl | hgS
            · exact absurd hgT hiT
            · exact absurd hgT hjT
            · exact Or.inl rfl
            · exact Or.inr hgS
          · rintro (rfl | hgS)
            · exact hkT
            · exact h1 hgS
        · have hT_eq : T = S := by
            ext g; have h1 := @h_loc.1 g; have h2 := @h_loc.2 g
            simp only [Sijk, Finset.mem_insert] at h2
            constructor
            · intro hgT
              rcases h2 hgT with rfl | rfl | rfl | hgS
              · exact absurd hgT hiT
              · exact absurd hgT hjT
              · exact absurd hgT hkT
              · exact hgS
            · exact h1
          subst hT_eq
          simp only [hiT, hjT, hkT, ↓reduceIte]
          dsimp [u_star, w]; linarith
      · have h_sd_pos : 1 ≤ (S \ T).card + (T \ Sijk).card := by
          by_contra h0
          have h1 : (S \ T).card = 0 := by omega
          have h2 : (T \ Sijk).card = 0 := by omega
          exact h_loc ⟨Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp h1),
                       Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp h2)⟩
        have h_sd_r : (1 : ℝ) ≤ ((S \ T).card : ℝ) + ((T \ Sijk).card : ℝ) := by
          exact_mod_cast h_sd_pos
        have h_card_S : (S.card : ℝ) = ((T ∩ S).card : ℝ) + ((S \ T).card : ℝ) := by
          have hc : S.card = (T ∩ S).card + (S \ T).card := by
            have h := Finset.card_sdiff_add_card_inter S T
            rw [Finset.inter_comm] at h; omega
          exact_mod_cast hc
        have hi_abs : -|pi| ≤ (if i ∈ T then pi else 0) := by
          split_ifs
          · exact neg_abs_le pi
          · exact neg_nonpos.mpr (abs_nonneg pi)
        have hj_abs : -|pj| ≤ (if j ∈ T then pj else 0) := by
          split_ifs
          · exact neg_abs_le pj
          · exact neg_nonpos.mpr (abs_nonneg pj)
        have hk_abs : -|pk| ≤ (if k ∈ T then pk else 0) := by
          split_ifs
          · exact neg_abs_le pk
          · exact neg_nonpos.mpr (abs_nonneg pk)
        have hrT_B := (abs_lt.mp (hr_lt_B T)).2
        have hrS_B := (abs_lt.mp (hr_lt_B S)).1
        have hM_ge : M ≤ M * (((S \ T).card : ℝ) + ((T \ Sijk).card : ℝ)) := by nlinarith
        rw [h_sum_p T]
        dsimp [u_star, M, w] at hM_ge ⊢
        rw [h_card_S, mul_add]
        linarith
    have hSij_dem : Sij ∈ priceDemand v p := by
      refine ⟨(h_util_ne_bot p Sij).mpr hvSij, fun T => ?_⟩
      by_cases hvT : v T = ⊥
      · simp [priceUtility, hvT]
      · rw [h_util_coe p T hvT, h_util_coe p Sij hvSij, WithBot.coe_le_coe, hu_Sij]
        by_cases hTSk : T = Sk
        · subst hTSk; rw [hu_Sk]
        · by_cases hTSij : T = Sij
          · subst hTSij; rw [hu_Sij]
          · exact le_of_lt (h_strict_other T hvT hTSk hTSij)
    let p' := Function.update p j (pj + φ)
    have hp_le : ∀ g, p g ≤ p' g := by
      intro g
      by_cases hgj : g = j
      · subst hgj
        have hpj_eq : p g = pj := by simp [p, hjS, hij.symm]
        simp [p', hpj_eq]; linarith
      · simp [p', hgj]
    have h_util_anti : ∀ T : Finset (Fin n), priceUtility v p' T ≤ priceUtility v p T := by
      intro T
      unfold priceUtility
      have hsum : ∑ g ∈ T, p g ≤ ∑ g ∈ T, p' g := Finset.sum_le_sum (fun g _ => hp_le g)
      have hneg : ((- ∑ g ∈ T, p' g : ℝ) : WithBot ℝ) ≤ ((- ∑ g ∈ T, p g : ℝ) : WithBot ℝ) :=
        WithBot.coe_le_coe.mpr (neg_le_neg hsum)
      exact add_le_add_right hneg (v T)
    obtain ⟨S', hS'_dem, hS'_sub⟩ := hp_gs.2 p p' hp_le Sij hSij_dem
    have hi_S' : i ∈ S' := by
      refine hS'_sub (Finset.mem_filter.mpr ⟨Finset.mem_insert_self i Sj, ?_⟩)
      simp [p', hij]
    have hu_p'_Sk : priceUtility v p' Sk = ((u_star : ℝ) : WithBot ℝ) := by
      have h_eq : priceUtility v p' Sk = priceUtility v p Sk := by
        unfold priceUtility
        congr 2; congr 1
        refine Finset.sum_congr rfl (fun g hg => ?_)
        have hgj : g ≠ j := by
          rcases Finset.mem_insert.mp hg with rfl | hgS
          · exact hjk.symm
          · exact fun h => hjS (h ▸ hgS)
        simp [p', hgj]
      rw [h_eq, h_util_coe p Sk hvSk, hu_Sk]
    have hS'_eq_Sk : S' = Sk := by
      by_contra hne
      have hvS' : v S' ≠ ⊥ := (h_util_ne_bot p' S').mp hS'_dem.1
      have h_le_Sk : priceUtility v p' Sk ≤ priceUtility v p' S' := hS'_dem.2 Sk
      rw [hu_p'_Sk] at h_le_Sk
      by_cases hS'Sij : S' = Sij
      · subst hS'Sij
        have hj_Sij : j ∈ Sij := Finset.mem_insert_of_mem (Finset.mem_insert_self j S)
        have h_sum_diff : ∑ g ∈ Sij, p' g = ∑ g ∈ Sij, p g + φ := by
          have h1 := Finset.sum_erase_add Sij p' hj_Sij
          have h2 := Finset.sum_erase_add Sij p hj_Sij
          have h_er_eq : ∑ g ∈ Sij.erase j, p' g = ∑ g ∈ Sij.erase j, p g := by
            refine Finset.sum_congr rfl (fun g hg => ?_)
            simp [p', (Finset.mem_erase.mp hg).1]
          have hpj_eq : p j = pj := by simp [p, hjS, hij.symm]
          have hp'j_eq : p' j = pj + φ := by simp [p']
          linarith
        rw [h_util_coe p' Sij hvSij, WithBot.coe_le_coe, h_sum_diff] at h_le_Sk
        linarith
      · have h_lt : priceUtility v p S' < ((u_star : ℝ) : WithBot ℝ) := by
          rw [h_util_coe p S' hvS', WithBot.coe_lt_coe]
          exact h_strict_other S' hvS' hne hS'Sij
        exact not_lt_of_ge (le_trans h_le_Sk (h_util_anti S')) h_lt
    rw [hS'_eq_Sk] at hi_S'
    rcases Finset.mem_insert.mp hi_S' with h1 | h2
    · exact hik h1
    · exact hiS h2

  have h_s4 : HasHereditaryDom v → HasRGP3 v → HasEquicardBaseExchange (liftedVal v) := by
    clear h_s1 h_s2 h_s3
    intro h_hered h_rgp
    have h_aug : ∀ (d : ℕ) (I J : Finset (Fin n)),
        (I \ J).card = d → v I ≠ ⊥ → v J ≠ ⊥ → I.card < J.card →
        ∃ e ∈ J \ I, v (insert e I) ≠ ⊥ := by
      intro d
      induction d with
      | zero =>
        intro I J hd hvI hvJ hlt
        have hIJ : I ⊆ J := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hd)
        obtain ⟨e, heJ, heI⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
        refine ⟨e, Finset.mem_sdiff.mpr ⟨heJ, heI⟩, ?_⟩
        exact h_hered (insert e I) J (Finset.insert_subset heJ hIJ) hvJ
      | succ d ih =>
        intro I J hd hvI hvJ hlt
        obtain ⟨a, ha_mem⟩ := Finset.card_pos.mp (by omega : 0 < (I \ J).card)
        have haI : a ∈ I := (Finset.mem_sdiff.mp ha_mem).1
        have haJ : a ∉ J := (Finset.mem_sdiff.mp ha_mem).2
        let S := I.erase a
        have hvS : v S ≠ ⊥ := h_hered S I (Finset.erase_subset a I) hvI
        have hS_sdiff : S \ J = (I \ J).erase a := by
          ext w; simp only [S, Finset.mem_sdiff, Finset.mem_erase]
          clear h_hered h_rgp ih
          tauto
        have hS_d : (S \ J).card = d := by
          rw [hS_sdiff, Finset.card_erase_of_mem ha_mem]; omega
        have hS_lt : S.card < J.card := lt_trans (Finset.card_erase_lt_of_mem haI) hlt
        obtain ⟨b₁, hb₁_mem, hvb₁⟩ := ih S J hS_d hvS hvJ hS_lt
        have hb₁J : b₁ ∈ J := (Finset.mem_sdiff.mp hb₁_mem).1
        have hb₁S : b₁ ∉ S := (Finset.mem_sdiff.mp hb₁_mem).2
        have hb₁a : b₁ ≠ a := fun h => haJ (h ▸ hb₁J)
        have hb₁I : b₁ ∉ I := fun h => hb₁S (Finset.mem_erase.mpr ⟨hb₁a, h⟩)
        let I₁ := insert b₁ S
        have hI₁_card : I₁.card = I.card := by
          rw [Finset.card_insert_of_notMem hb₁S, Finset.card_erase_add_one haI]
        have hI₁_sdiff : I₁ \ J = S \ J := by
          ext w
          simp only [I₁, Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hwS, hwJ⟩
            · exact absurd hb₁J hwJ
            · exact ⟨hwS, hwJ⟩
          · rintro ⟨hwS, hwJ⟩
            exact ⟨Or.inr hwS, hwJ⟩
        obtain ⟨b₂, hb₂_mem, hvb₂⟩ :=
          ih I₁ J (hI₁_sdiff.trans rfl ▸ hS_d) hvb₁ hvJ (hI₁_card ▸ hlt)
        have hb₂J : b₂ ∈ J := (Finset.mem_sdiff.mp hb₂_mem).1
        have hb₂I₁ : b₂ ∉ I₁ := (Finset.mem_sdiff.mp hb₂_mem).2
        have hb₂_ne_b₁ : b₂ ≠ b₁ := fun h => hb₂I₁ (h ▸ Finset.mem_insert_self b₁ S)
        have hb₂S : b₂ ∉ S := fun h => hb₂I₁ (Finset.mem_insert_of_mem h)
        have hb₂a : b₂ ≠ a := fun h => haJ (h ▸ hb₂J)
        have hb₂I : b₂ ∉ I := fun h => hb₂S (Finset.mem_erase.mpr ⟨hb₂a, h⟩)
        have hv_b1b2 : v (insert b₁ (insert b₂ S)) ≠ ⊥ := by
          simpa [I₁, Finset.insert_comm b₁ b₂ S] using hvb₂
        have h_ins_a : insert a S = I := Finset.insert_erase haI
        have hv_a : v (insert a S) ≠ ⊥ := h_ins_a.symm ▸ hvI
        have h_ineq := h_rgp S b₁ b₂ a hb₁S hb₂S (Finset.notMem_erase a I)
          hb₂_ne_b₁.symm hb₁a hb₂a hv_b1b2 hv_a
        have h_lhs_ne : v (insert b₁ (insert b₂ S)) + v (insert a S) ≠ ⊥ := by
          simp [WithBot.add_eq_bot, hv_b1b2, hv_a]
        rw [le_max_iff] at h_ineq
        rcases h_ineq with h1 | h2
        · have h_rhs_ne : v (insert b₁ S) + v (insert b₂ (insert a S)) ≠ ⊥ :=
            fun hb => h_lhs_ne (le_bot_iff.mp (hb ▸ h1))
          have hv_res : v (insert b₂ I) ≠ ⊥ := by
            rw [← h_ins_a]; exact fun hb => h_rhs_ne (by simp [hb])
          exact ⟨b₂, Finset.mem_sdiff.mpr ⟨hb₂J, hb₂I⟩, hv_res⟩
        · have h_rhs_ne : v (insert b₂ S) + v (insert b₁ (insert a S)) ≠ ⊥ :=
            fun hb => h_lhs_ne (le_bot_iff.mp (hb ▸ h2))
          have hv_res : v (insert b₁ I) ≠ ⊥ := by
            rw [← h_ins_a]; exact fun hb => h_rhs_ne (by simp [hb])
          exact ⟨b₁, Finset.mem_sdiff.mpr ⟨hb₁J, hb₁I⟩, hv_res⟩
    intro A B hA hB hvA hvB s hs
    have hBA_ne : (B \ A).Nonempty := by
      by_contra h_emp
      rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h_emp
      have hAB_eq : B = A := Finset.eq_of_subset_of_card_le h_emp (by omega)
      rw [hAB_eq] at hs
      exact (Finset.mem_sdiff.mp hs).2 (Finset.mem_sdiff.mp hs).1
    rcases s with x | d
    · by_cases hvYx : v (insert x (liftedProj B)) ≠ ⊥
      · obtain ⟨u, hu⟩ := hBA_ne
        refine ⟨u, hu, ?_⟩
        apply h_hered _ (insert x (liftedProj B)) _ hvYx
        intro i hi
        simp only [liftedProj, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_erase, Sum.inl.injEq] at hi ⊢
        exact hi.imp_right And.right
      · push_neg at hvYx
        let X₀ := liftedProj A
        let Y₀ := liftedProj B
        have hxX₀ : x ∈ X₀ := by
          simp [X₀, liftedProj, (Finset.mem_sdiff.mp hs).1]
        have hxY₀ : x ∉ Y₀ := by
          simp [Y₀, liftedProj, (Finset.mem_sdiff.mp hs).2]
        let base := insert x (X₀ ∩ Y₀)
        let F := (insert x Y₀).powerset.filter (fun Z => base ⊆ Z ∧ v Z ≠ ⊥)
        have hbase_mem : base ∈ F := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, Finset.Subset.refl _, ?_⟩
          · exact Finset.insert_subset (Finset.mem_insert_self x Y₀)
              (Finset.Subset.trans Finset.inter_subset_right (Finset.subset_insert x Y₀))
          · refine h_hered base X₀ ?_ hvA
            exact Finset.insert_subset hxX₀ Finset.inter_subset_left
        obtain ⟨Z, hZF, hZ_max⟩ := Finset.exists_max_image F Finset.card ⟨base, hbase_mem⟩
        have hZ_sub : Z ⊆ insert x Y₀ := Finset.mem_powerset.mp (Finset.mem_filter.mp hZF).1
        have hbase_Z : base ⊆ Z := (Finset.mem_filter.mp hZF).2.1
        have hvZ : v Z ≠ ⊥ := (Finset.mem_filter.mp hZF).2.2
        have hZ_ne : Z ≠ insert x Y₀ := fun heq => hvZ (heq.symm ▸ hvYx)
        have hZ_lt_ins : Z.card < (insert x Y₀).card :=
          Finset.card_lt_card (ssubset_iff_subset_ne.mpr ⟨hZ_sub, hZ_ne⟩)
        rw [Finset.card_insert_of_notMem hxY₀] at hZ_lt_ins
        have hZ_card : Z.card = Y₀.card := by
          by_contra hne
          have hlt : Z.card < Y₀.card := by omega
          obtain ⟨e, he_mem, hve⟩ := h_aug _ Z Y₀ rfl hvZ hvB hlt
          have heY₀ : e ∈ Y₀ := (Finset.mem_sdiff.mp he_mem).1
          have heZ : e ∉ Z := (Finset.mem_sdiff.mp he_mem).2
          have hins_F : insert e Z ∈ F := by
            refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_, hve⟩
            · exact Finset.insert_subset (Finset.mem_insert_of_mem heY₀) hZ_sub
            · exact Finset.Subset.trans hbase_Z (Finset.subset_insert e Z)
          have hle := hZ_max (insert e Z) hins_F
          rw [Finset.card_insert_of_notMem heZ] at hle
          omega
        have hsdiff_one : (insert x Y₀ \ Z).card = 1 := by
          rw [Finset.card_sdiff_of_subset hZ_sub, Finset.card_insert_of_notMem hxY₀, hZ_card]
          omega
        obtain ⟨y, hy_eq⟩ := Finset.card_eq_one.mp hsdiff_one
        have hy_sdiff : y ∈ insert x Y₀ \ Z := hy_eq ▸ Finset.mem_singleton_self y
        have hy_ins : y ∈ insert x Y₀ := (Finset.mem_sdiff.mp hy_sdiff).1
        have hyZ : y ∉ Z := (Finset.mem_sdiff.mp hy_sdiff).2
        have hxZ : x ∈ Z := hbase_Z (Finset.mem_insert_self x (X₀ ∩ Y₀))
        have hyx : y ≠ x := fun h => hyZ (h ▸ hxZ)
        have hyY₀ : y ∈ Y₀ := by
          rcases Finset.mem_insert.mp hy_ins with rfl | h
          · exact absurd rfl hyx
          · exact h
        have hyX₀ : y ∉ X₀ := by
          intro hX
          exact hyZ (hbase_Z (Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hX, hyY₀⟩)))
        have hu_mem : Sum.inl y ∈ B \ A := by
          simp only [Y₀, X₀, liftedProj, Finset.mem_filter, Finset.mem_univ, true_and] at hyY₀ hyX₀
          exact Finset.mem_sdiff.mpr ⟨hyY₀, hyX₀⟩
        refine ⟨Sum.inl y, hu_mem, ?_⟩
        have hproj_eq : liftedProj (insert (Sum.inl x) (B.erase (Sum.inl y))) = Z := by
          ext i
          simp only [liftedProj, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_erase]
          have hinl_eq : ∀ {a b : Fin n}, (Sum.inl a : Fin n ⊕ Fin n) = Sum.inl b ↔ a = b :=
            ⟨Sum.inl.inj, congrArg Sum.inl⟩
          simp only [hinl_eq]
          have hiY₀_iff : Sum.inl i ∈ B ↔ i ∈ Y₀ := by
            simp [Y₀, liftedProj]
          rw [hiY₀_iff]
          constructor
          · intro hi
            have hi_ins : i ∈ insert x Y₀ := by
              rcases hi with rfl | ⟨_, hY⟩
              · exact Finset.mem_insert_self i Y₀
              · exact Finset.mem_insert_of_mem hY
            have hiy : i ≠ y := by
              rcases hi with rfl | ⟨hne, _⟩
              · exact hyx.symm
              · exact fun h => hne (congrArg Sum.inl h)
            by_contra hiZ
            have hi_sd : i ∈ insert x Y₀ \ Z := Finset.mem_sdiff.mpr ⟨hi_ins, hiZ⟩
            rw [hy_eq, Finset.mem_singleton] at hi_sd
            exact hiy hi_sd
          · intro hiZ
            have hi_ins := hZ_sub hiZ
            have hiy : i ≠ y := fun h => hyZ (h ▸ hiZ)
            rcases Finset.mem_insert.mp hi_ins with rfl | hY
            · exact Or.inl rfl
            · exact Or.inr ⟨fun h => hiy (Sum.inl.inj h), hY⟩
        simpa [liftedVal, hproj_eq] using hvZ
    · obtain ⟨u, hu⟩ := hBA_ne
      refine ⟨u, hu, ?_⟩
      apply h_hered _ (liftedProj B) _ hvB
      intro i hi
      simp only [liftedProj, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_erase, reduceCtorEq, false_or] at hi ⊢
      exact hi.2

  have h_s5 : HasHereditaryDom v → HasSubmod2 v → HasRGP3 v →
      HasGrassmannPlucker2 (liftedVal v) := by
    clear h_s1 h_s2 h_s3 h_s4
    intro h_hered h_submod h_rgp
    have hproj_inl : ∀ (A : Finset (Fin n ⊕ Fin n)) (a : Fin n),
        liftedProj (insert (Sum.inl a) A) = insert a (liftedProj A) := by
      intro A a; ext i; simp [liftedProj]
    have hproj_inr : ∀ (A : Finset (Fin n ⊕ Fin n)) (d : Fin n),
        liftedProj (insert (Sum.inr d) A) = liftedProj A := by
      intro A d; ext i; simp [liftedProj]
    have hmem_inl : ∀ (A : Finset (Fin n ⊕ Fin n)) (a : Fin n),
        Sum.inl a ∉ A → a ∉ liftedProj A := by
      intro A a h; simp [liftedProj, h]
    have h_real4 : ∀ (I₀ : Finset (Fin n)) (a₁ a₂ b₁ b₂ : Fin n),
        a₁ ∉ I₀ → a₂ ∉ I₀ → b₁ ∉ I₀ → b₂ ∉ I₀ →
        a₁ ≠ a₂ → a₁ ≠ b₁ → a₁ ≠ b₂ → a₂ ≠ b₁ → a₂ ≠ b₂ → b₁ ≠ b₂ →
        v (insert a₁ (insert a₂ I₀)) ≠ ⊥ → v (insert b₁ (insert b₂ I₀)) ≠ ⊥ →
          v (insert a₁ (insert a₂ I₀)) + v (insert b₁ (insert b₂ I₀)) ≤
            max (v (insert a₁ (insert b₁ I₀)) + v (insert a₂ (insert b₂ I₀)))
                (v (insert a₁ (insert b₂ I₀)) + v (insert a₂ (insert b₁ I₀))) := by
      intro I₀ a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ ha₁a₂ ha₁b₁ ha₁b₂ ha₂b₁ ha₂b₂ hb₁b₂ hva hvb
      have hva₁ : v (insert a₁ I₀) ≠ ⊥ :=
        h_hered _ _ (Finset.insert_subset_insert a₁ (Finset.subset_insert a₂ I₀)) hva
      have hva₂ : v (insert a₂ I₀) ≠ ⊥ :=
        h_hered _ _ (Finset.subset_insert a₁ (insert a₂ I₀)) hva
      have hvb₁ : v (insert b₁ I₀) ≠ ⊥ :=
        h_hered _ _ (Finset.insert_subset_insert b₁ (Finset.subset_insert b₂ I₀)) hvb
      have hvb₂ : v (insert b₂ I₀) ≠ ⊥ :=
        h_hered _ _ (Finset.subset_insert b₁ (insert b₂ I₀)) hvb
      obtain ⟨r, hr_coe⟩ : ∃ r : Fin n → ℝ,
          ∀ q, v (insert q I₀) ≠ ⊥ → ((r q : ℝ) : WithBot ℝ) = v (insert q I₀) := by
        refine ⟨fun q => (v (insert q I₀)).unbotD 0, fun q hq => ?_⟩
        obtain ⟨rq, hrq⟩ := WithBot.ne_bot_iff_exists.mp hq
        simp [← hrq]
      let c : Fin n → Fin n → WithBot ℝ :=
        fun p q => v (insert p (insert q I₀)) + ((-(r p + r q) : ℝ) : WithBot ℝ)
      have c_symm : ∀ p q, c p q = c q p := by
        intro p q
        simp only [c, Finset.insert_comm p q I₀, add_comm (r p) (r q)]
      have c_ult : ∀ p q s,
          p ∉ I₀ → q ∉ I₀ → s ∉ I₀ → p ≠ q → p ≠ s → q ≠ s →
          v (insert p I₀) ≠ ⊥ → v (insert q I₀) ≠ ⊥ → v (insert s I₀) ≠ ⊥ →
          c p q ≤ max (c p s) (c s q) := by
        intro p q s hp hq hs hpq hps hqs hvp hvq hvs
        by_cases hpq_bot : v (insert p (insert q I₀)) = ⊥
        · simp [c, hpq_bot]
        · have hrgp := h_rgp I₀ p q s hp hq hs hpq hps hqs hpq_bot hvs
          obtain ⟨rpq, hrpq⟩ := WithBot.ne_bot_iff_exists.mp hpq_bot
          have h_lhs_ne : v (insert p (insert q I₀)) + v (insert s I₀) ≠ ⊥ := by
            simp [WithBot.add_eq_bot, hpq_bot, hvs]
          rw [le_max_iff] at hrgp ⊢
          rcases hrgp with h1 | h2
          · right
            have h_rhs_ne : v (insert p I₀) + v (insert q (insert s I₀)) ≠ ⊥ :=
              fun hb => h_lhs_ne (le_bot_iff.mp (hb ▸ h1))
            have hvqs : v (insert q (insert s I₀)) ≠ ⊥ := fun hb => h_rhs_ne (by simp [hb])
            obtain ⟨rqs, hrqs⟩ := WithBot.ne_bot_iff_exists.mp hvqs
            rw [← hr_coe p hvp, ← hr_coe s hvs, ← hrpq, ← hrqs,
                ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe] at h1
            have hsq : insert s (insert q I₀) = insert q (insert s I₀) := Finset.insert_comm s q I₀
            simp only [c, hsq, ← hrpq, ← hrqs, ← WithBot.coe_add, WithBot.coe_le_coe]
            linarith
          · left
            have h_rhs_ne : v (insert q I₀) + v (insert p (insert s I₀)) ≠ ⊥ :=
              fun hb => h_lhs_ne (le_bot_iff.mp (hb ▸ h2))
            have hvps : v (insert p (insert s I₀)) ≠ ⊥ := fun hb => h_rhs_ne (by simp [hb])
            obtain ⟨rps, hrps⟩ := WithBot.ne_bot_iff_exists.mp hvps
            rw [← hr_coe q hvq, ← hr_coe s hvs, ← hrpq, ← hrps,
                ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe] at h2
            simp only [c, ← hrpq, ← hrps, ← WithBot.coe_add, WithBot.coe_le_coe]
            linarith
      have c_branch : ∀ (p₁ p₂ : Fin n),
          p₁ ∉ I₀ → p₂ ∉ I₀ → p₁ ≠ p₂ → p₁ ≠ b₁ → p₁ ≠ b₂ → p₂ ≠ b₁ → p₂ ≠ b₂ →
          v (insert p₁ I₀) ≠ ⊥ → v (insert p₂ I₀) ≠ ⊥ →
          c p₂ b₁ ≤ c p₁ b₁ →
          c p₁ p₂ + c b₁ b₂ ≤ max (c p₁ b₁ + c p₂ b₂) (c p₁ b₂ + c p₂ b₁) := by
        intro p₁ p₂ hp₁ hp₂ hp₁p₂ hp₁b₁ hp₁b₂ hp₂b₁ hp₂b₂ hvp₁ hvp₂ hle
        have h_p12 : c p₁ p₂ ≤ c p₁ b₁ := by
          have hu := c_ult p₁ p₂ b₁ hp₁ hp₂ hb₁ hp₁p₂ hp₁b₁ hp₂b₁ hvp₁ hvp₂ hvb₁
          rw [c_symm b₁ p₂, max_eq_left hle] at hu
          exact hu
        have h_b12 := c_ult b₁ b₂ p₂ hb₁ hb₂ hp₂ hb₁b₂ hp₂b₁.symm hp₂b₂.symm hvb₁ hvb₂ hvp₂
        rw [c_symm b₁ p₂, le_max_iff] at h_b12
        rcases h_b12 with hb_le1 | hb_le2
        · by_cases h_p12_b2 : c p₁ p₂ ≤ c p₁ b₂
          · exact le_trans (add_le_add h_p12_b2 hb_le1) (le_max_right _ _)
          · have hu2 := c_ult p₁ p₂ b₂ hp₁ hp₂ hb₂ hp₁p₂ hp₁b₂ hp₂b₂ hvp₁ hvp₂ hvb₂
            rw [c_symm b₂ p₂, le_max_iff] at hu2
            have h_p12_p2b2 : c p₁ p₂ ≤ c p₂ b₂ := hu2.resolve_left h_p12_b2
            have h_sum := add_le_add h_p12_p2b2 (le_trans hb_le1 hle)
            rw [add_comm (c p₂ b₂) (c p₁ b₁)] at h_sum
            exact le_trans h_sum (le_max_left _ _)
        · exact le_trans (add_le_add h_p12 hb_le2) (le_max_left _ _)
      have hc_main : c a₁ a₂ + c b₁ b₂ ≤ max (c a₁ b₁ + c a₂ b₂) (c a₁ b₂ + c a₂ b₁) := by
        rcases le_total (c a₂ b₁) (c a₁ b₁) with hle | hle
        · exact c_branch a₁ a₂ ha₁ ha₂ ha₁a₂ ha₁b₁ ha₁b₂ ha₂b₁ ha₂b₂ hva₁ hva₂ hle
        · have h := c_branch a₂ a₁ ha₂ ha₁ ha₁a₂.symm ha₂b₁ ha₂b₂ ha₁b₁ ha₁b₂ hva₂ hva₁ hle
          rwa [c_symm a₂ a₁, add_comm (c a₂ b₁) (c a₁ b₂), add_comm (c a₂ b₂) (c a₁ b₁),
               max_comm] at h
      obtain ⟨raa, hraa⟩ := WithBot.ne_bot_iff_exists.mp hva
      obtain ⟨rbb, hrbb⟩ := WithBot.ne_bot_iff_exists.mp hvb
      have hc_lhs_ne : c a₁ a₂ + c b₁ b₂ ≠ ⊥ := by
        simp [c, ← hraa, ← hrbb, ← WithBot.coe_add]
      rw [le_max_iff] at hc_main ⊢
      rcases hc_main with h1 | h2
      · left
        have h_rhs_ne : c a₁ b₁ + c a₂ b₂ ≠ ⊥ := fun hb => hc_lhs_ne (le_bot_iff.mp (hb ▸ h1))
        have hv1 : v (insert a₁ (insert b₁ I₀)) ≠ ⊥ := fun hb => h_rhs_ne (by simp [c, hb])
        have hv2 : v (insert a₂ (insert b₂ I₀)) ≠ ⊥ := fun hb => h_rhs_ne (by simp [c, hb])
        obtain ⟨r1, hr1⟩ := WithBot.ne_bot_iff_exists.mp hv1
        obtain ⟨r2, hr2⟩ := WithBot.ne_bot_iff_exists.mp hv2
        simp only [c, ← hraa, ← hrbb, ← hr1, ← hr2, ← WithBot.coe_add, WithBot.coe_le_coe] at h1 ⊢
        linarith
      · right
        have h_rhs_ne : c a₁ b₂ + c a₂ b₁ ≠ ⊥ := fun hb => hc_lhs_ne (le_bot_iff.mp (hb ▸ h2))
        have hv1 : v (insert a₁ (insert b₂ I₀)) ≠ ⊥ := fun hb => h_rhs_ne (by simp [c, hb])
        have hv2 : v (insert a₂ (insert b₁ I₀)) ≠ ⊥ := fun hb => h_rhs_ne (by simp [c, hb])
        obtain ⟨r1, hr1⟩ := WithBot.ne_bot_iff_exists.mp hv1
        obtain ⟨r2, hr2⟩ := WithBot.ne_bot_iff_exists.mp hv2
        simp only [c, ← hraa, ← hrbb, ← hr1, ← hr2, ← WithBot.coe_add, WithBot.coe_le_coe] at h2 ⊢
        linarith
    have hinl_ne : ∀ {x y : Fin n}, (Sum.inl x : Fin n ⊕ Fin n) ≠ Sum.inl y → x ≠ y :=
      fun h heq => h (congrArg Sum.inl heq)
    intro I x₁ x₂ y₁ y₂ hx₁ hx₂ hy₁ hy₂ hx₁x₂ hx₁y₁ hx₁y₂ hx₂y₁ hx₂y₂ hy₁y₂ hvx hvy
    rcases x₁ with a₁ | d₁ <;> rcases x₂ with a₂ | d₂ <;>
      rcases y₁ with b₁ | e₁ <;> rcases y₂ with b₂ | e₂
    · simp only [liftedVal, hproj_inl] at hvx hvy ⊢
      exact h_real4 (liftedProj I) a₁ a₂ b₁ b₂
        (hmem_inl I a₁ hx₁) (hmem_inl I a₂ hx₂) (hmem_inl I b₁ hy₁) (hmem_inl I b₂ hy₂)
        (hinl_ne hx₁x₂) (hinl_ne hx₁y₁) (hinl_ne hx₁y₂)
        (hinl_ne hx₂y₁) (hinl_ne hx₂y₂) (hinl_ne hy₁y₂)
        hvx hvy
    · simp only [liftedVal, hproj_inl, hproj_inr] at hvx hvy ⊢
      have h := h_rgp (liftedProj I) a₁ a₂ b₁
        (hmem_inl I a₁ hx₁) (hmem_inl I a₂ hx₂) (hmem_inl I b₁ hy₁)
        (hinl_ne hx₁x₂) (hinl_ne hx₁y₁) (hinl_ne hx₂y₁) hvx hvy
      rwa [add_comm (v (insert a₂ (liftedProj I))), max_comm] at h
    · simp only [liftedVal, hproj_inl, hproj_inr] at hvx hvy ⊢
      have h := h_rgp (liftedProj I) a₁ a₂ b₂
        (hmem_inl I a₁ hx₁) (hmem_inl I a₂ hx₂) (hmem_inl I b₂ hy₂)
        (hinl_ne hx₁x₂) (hinl_ne hx₁y₂) (hinl_ne hx₂y₂) hvx hvy
      rwa [add_comm (v (insert a₂ (liftedProj I)))] at h
    · simp only [liftedVal, hproj_inl, hproj_inr] at hvx hvy ⊢
      exact le_trans (h_submod (liftedProj I) a₁ a₂ (hmem_inl I a₁ hx₁) (hmem_inl I a₂ hx₂)
        (hinl_ne hx₁x₂) hvx) (le_max_left _ _)
    · simp only [liftedVal, hproj_inl, hproj_inr] at hvx hvy ⊢
      have h := h_rgp (liftedProj I) b₁ b₂ a₁
        (hmem_inl I b₁ hy₁) (hmem_inl I b₂ hy₂) (hmem_inl I a₁ hx₁)
        (hinl_ne hy₁y₂) (hinl_ne hx₁y₁).symm (hinl_ne hx₁y₂).symm hvy hvx
      rwa [Finset.insert_comm b₂ a₁ (liftedProj I), Finset.insert_comm b₁ a₁ (liftedProj I),
           add_comm (v (insert b₁ (insert b₂ (liftedProj I)))),
           add_comm (v (insert b₁ (liftedProj I))),
           add_comm (v (insert b₂ (liftedProj I))), max_comm] at h
    · simp only [liftedVal, hproj_inl, hproj_inr]
      exact le_max_right _ _
    · simp only [liftedVal, hproj_inl, hproj_inr]
      exact le_max_left _ _
    · simp only [liftedVal, hproj_inl, hproj_inr]
      exact le_max_left _ _
    · simp only [liftedVal, hproj_inl, hproj_inr] at hvx hvy ⊢
      have h := h_rgp (liftedProj I) b₁ b₂ a₂
        (hmem_inl I b₁ hy₁) (hmem_inl I b₂ hy₂) (hmem_inl I a₂ hx₂)
        (hinl_ne hy₁y₂) (hinl_ne hx₂y₁).symm (hinl_ne hx₂y₂).symm hvy hvx
      rwa [Finset.insert_comm b₂ a₂ (liftedProj I), Finset.insert_comm b₁ a₂ (liftedProj I),
           add_comm (v (insert b₁ (insert b₂ (liftedProj I))))] at h
    · simp only [liftedVal, hproj_inl, hproj_inr]
      rw [add_comm]
      exact le_max_left _ _
    · simp only [liftedVal, hproj_inl, hproj_inr]
      rw [add_comm]
      exact le_max_right _ _
    · simp only [liftedVal, hproj_inl, hproj_inr]
      rw [add_comm]
      exact le_max_left _ _
    · simp only [liftedVal, hproj_inl, hproj_inr] at hvx hvy ⊢
      rw [add_comm]
      exact le_trans (h_submod (liftedProj I) b₁ b₂ (hmem_inl I b₁ hy₁) (hmem_inl I b₂ hy₂)
        (hinl_ne hy₁y₂) hvy) (le_max_left _ _)
    · simp only [liftedVal, hproj_inl, hproj_inr]
      exact le_max_right _ _
    · simp only [liftedVal, hproj_inl, hproj_inr]
      rw [add_comm (v (liftedProj I))]
      exact le_max_left _ _
    · simp only [liftedVal, hproj_inr]
      exact le_max_left _ _

  have h_s6 : ∀ (ω : Finset (Fin n ⊕ Fin n) → WithBot ℝ),
      HasEquicardBaseExchange ω → HasGrassmannPlucker2 ω →
      ∀ S T : Finset (Fin n ⊕ Fin n),
        S.card = n → T.card = n → ω S ≠ ⊥ → ω T ≠ ⊥ →
        ∀ s ∈ S \ T,
          ∃ t ∈ T \ S, ω S + ω T ≤ ω (insert t (S.erase s)) + ω ((insert s T).erase t) := by
    clear v h_s1 h_s2 h_s3 h_s4 h_s5
    intro ω h_base h_plucker S T hS_card hT_card hS_ne hT_ne s hs
    suffices h_ind : ∀ (k : ℕ) (S T : Finset (Fin n ⊕ Fin n)),
        (S \ T).card = k → S.card = n → T.card = n → ω S ≠ ⊥ → ω T ≠ ⊥ →
        ∀ s ∈ S \ T,
        ∃ t ∈ T \ S, ω S + ω T ≤ ω (insert t (S.erase s)) + ω ((insert s T).erase t) by
      exact h_ind (S \ T).card S T rfl hS_card hT_card hS_ne hT_ne s hs
    clear S T hS_card hT_card hS_ne hT_ne s hs
    intro k
    induction k with
    | zero =>
      intro S T hk _ _ _ _ s hs
      have hempty := Finset.card_eq_zero.mp hk
      rw [hempty] at hs
      exact absurd hs (Finset.notMem_empty s)
    | succ k ih =>
      intro S T hk hS_card hT_card hS_ne hT_ne s hs
      have hTS_card : (T \ S).card = k + 1 := by
        have h1 := Finset.card_sdiff_add_card_inter S T
        have h2 := Finset.card_sdiff_add_card_inter T S
        rw [Finset.inter_comm] at h2
        omega
      by_cases hk0 : k = 0
      · subst hk0
        obtain ⟨t, ht_eq⟩ := Finset.card_eq_one.mp hTS_card
        have ht_mem : t ∈ T \ S := ht_eq ▸ Finset.mem_singleton_self t
        obtain ⟨s', hs'_eq⟩ := Finset.card_eq_one.mp hk
        have hs_eq_s' : s = s' := Finset.mem_singleton.mp (hs'_eq ▸ hs)
        subst hs_eq_s'
        refine ⟨t, ht_mem, ?_⟩
        have h1 : insert t (S.erase s) = T := by
          ext x
          have hxS_iff : x ∈ S \ T ↔ x = s := by rw [hs'_eq, Finset.mem_singleton]
          have hxT_iff : x ∈ T \ S ↔ x = t := by rw [ht_eq, Finset.mem_singleton]
          clear h_base h_plucker ih hS_card hT_card hS_ne hT_ne hk hTS_card ht_mem hs'_eq ht_eq hs
          simp only [Finset.mem_sdiff] at hxS_iff hxT_iff
          simp only [Finset.mem_insert, Finset.mem_erase]
          by_cases hxT : x ∈ T <;> by_cases hxS : x ∈ S <;> tauto
        have h2 : (insert s T).erase t = S := by
          ext x
          have hxS_iff : x ∈ S \ T ↔ x = s := by rw [hs'_eq, Finset.mem_singleton]
          have hxT_iff : x ∈ T \ S ↔ x = t := by rw [ht_eq, Finset.mem_singleton]
          clear h_base h_plucker ih hS_card hT_card hS_ne hT_ne hk hTS_card ht_mem hs'_eq ht_eq hs h1
          simp only [Finset.mem_sdiff] at hxS_iff hxT_iff
          simp only [Finset.mem_erase, Finset.mem_insert]
          by_cases hxT : x ∈ T <;> by_cases hxS : x ∈ S <;> tauto
        rw [h1, h2, add_comm]
      · by_cases hk1 : k = 1
        · subst hk1
          have hS_er_one : ((S \ T).erase s).card = 1 := by
            rw [Finset.card_erase_of_mem hs]; omega
          obtain ⟨s_tilde, hs_tilde_eq⟩ := Finset.card_eq_one.mp hS_er_one
          have hs_tilde_mem : s_tilde ∈ (S \ T).erase s :=
            hs_tilde_eq ▸ Finset.mem_singleton_self s_tilde
          have hs_tilde_ne_s : s_tilde ≠ s := (Finset.mem_erase.mp hs_tilde_mem).1
          have hs_tilde_sd : s_tilde ∈ S \ T := (Finset.mem_erase.mp hs_tilde_mem).2
          obtain ⟨t₁, t₂, ht12_ne, ht_eq⟩ := Finset.card_eq_two.mp hTS_card
          have ht₁_mem : t₁ ∈ T \ S := by rw [ht_eq]; simp
          have ht₂_mem : t₂ ∈ T \ S := by rw [ht_eq]; simp
          let I := S ∩ T
          have hs_I : s ∉ I := fun h => (Finset.mem_sdiff.mp hs).2 (Finset.mem_inter.mp h).2
          have hst_I : s_tilde ∉ I :=
            fun h => (Finset.mem_sdiff.mp hs_tilde_sd).2 (Finset.mem_inter.mp h).2
          have ht₁_I : t₁ ∉ I := fun h => (Finset.mem_sdiff.mp ht₁_mem).2 (Finset.mem_inter.mp h).1
          have ht₂_I : t₂ ∉ I := fun h => (Finset.mem_sdiff.mp ht₂_mem).2 (Finset.mem_inter.mp h).1
          have hS_eq : insert s_tilde (insert s I) = S := by
            ext x
            have h_sd : x ∈ (S \ T).erase s ↔ x = s_tilde := by
              rw [hs_tilde_eq, Finset.mem_singleton]
            simp only [I, Finset.mem_insert, Finset.mem_inter, Finset.mem_erase,
              Finset.mem_sdiff] at h_sd hs ⊢
            clear h_base h_plucker ih hS_card hT_card hS_ne hT_ne hk hTS_card hk0 hS_er_one
              hs_tilde_eq hs_tilde_mem hs_tilde_ne_s hs_tilde_sd ht12_ne ht_eq ht₁_mem ht₂_mem
              hs_I hst_I ht₁_I ht₂_I I
            by_cases hxs : x = s
            · subst hxs; tauto
            · by_cases hxS : x ∈ S <;> by_cases hxT : x ∈ T <;> tauto
          have hT_eq : insert t₁ (insert t₂ I) = T := by
            ext x
            have h_sd : x ∈ T \ S ↔ x = t₁ ∨ x = t₂ := by
              rw [ht_eq]; simp
            simp only [I, Finset.mem_insert, Finset.mem_inter, Finset.mem_sdiff] at h_sd ⊢
            clear h_base h_plucker ih hS_card hT_card hS_ne hT_ne hk hTS_card hk0 hS_er_one
              hs_tilde_eq hs_tilde_mem hs_tilde_ne_s hs_tilde_sd ht12_ne ht_eq ht₁_mem ht₂_mem
              hs_I hst_I ht₁_I ht₂_I hS_eq hs I
            by_cases hxS : x ∈ S <;> by_cases hxT : x ∈ T <;> tauto
          have hst_t₁ : s_tilde ≠ t₁ :=
            fun h => (Finset.mem_sdiff.mp ht₁_mem).2 (h ▸ (Finset.mem_sdiff.mp hs_tilde_sd).1)
          have hst_t₂ : s_tilde ≠ t₂ :=
            fun h => (Finset.mem_sdiff.mp ht₂_mem).2 (h ▸ (Finset.mem_sdiff.mp hs_tilde_sd).1)
          have hs_t₁ : s ≠ t₁ :=
            fun h => (Finset.mem_sdiff.mp ht₁_mem).2 (h ▸ (Finset.mem_sdiff.mp hs).1)
          have hs_t₂ : s ≠ t₂ :=
            fun h => (Finset.mem_sdiff.mp ht₂_mem).2 (h ▸ (Finset.mem_sdiff.mp hs).1)
          have hpl := h_plucker I s_tilde s t₁ t₂ hst_I hs_I ht₁_I ht₂_I
            hs_tilde_ne_s hst_t₁ hst_t₂ hs_t₁ hs_t₂ ht12_ne
            (hS_eq.symm ▸ hS_ne) (hT_eq.symm ▸ hT_ne)
          rw [hS_eq, hT_eq, le_max_iff] at hpl
          have h_er_S : insert s_tilde I = S.erase s := by
            rw [← hS_eq, Finset.insert_comm s_tilde s I, Finset.erase_insert]
            simp [hs_I, hs_tilde_ne_s.symm]
          have h_er_T₁ : insert s (insert t₂ I) = (insert s T).erase t₁ := by
            rw [← hT_eq]
            ext x
            simp only [Finset.mem_insert, Finset.mem_erase]
            by_cases hxt₁ : x = t₁
            · subst hxt₁; simp [hs_t₁.symm, ht12_ne, ht₁_I]
            · simp [hxt₁]
          have h_er_T₂ : insert s (insert t₁ I) = (insert s T).erase t₂ := by
            rw [← hT_eq]
            ext x
            simp only [Finset.mem_insert, Finset.mem_erase]
            by_cases hxt₂ : x = t₂
            · subst hxt₂; simp [hs_t₂.symm, ht12_ne.symm, ht₂_I]
            · simp [hxt₂]
          rcases hpl with h1 | h2
          · refine ⟨t₁, ht₁_mem, ?_⟩
            rwa [Finset.insert_comm s_tilde t₁ I, h_er_S, h_er_T₁] at h1
          · refine ⟨t₂, ht₂_mem, ?_⟩
            rwa [Finset.insert_comm s_tilde t₂ I, h_er_S, h_er_T₂] at h2
        · have h_er_pos : 0 < ((S \ T).erase s).card := by
            rw [Finset.card_erase_of_mem hs]; omega
          obtain ⟨s_tilde, hs_tilde_er⟩ := Finset.card_pos.mp h_er_pos
          have hs_tilde_ne_s : s_tilde ≠ s := (Finset.mem_erase.mp hs_tilde_er).1
          have hs_tilde_sd : s_tilde ∈ S \ T := (Finset.mem_erase.mp hs_tilde_er).2
          have hs_tilde_S : s_tilde ∈ S := (Finset.mem_sdiff.mp hs_tilde_sd).1
          have hs_tilde_not_T : s_tilde ∉ T := (Finset.mem_sdiff.mp hs_tilde_sd).2
          have hs_S : s ∈ S := (Finset.mem_sdiff.mp hs).1
          have hs_not_T : s ∉ T := (Finset.mem_sdiff.mp hs).2
          let U := (T \ S).filter (fun u => ω (insert s_tilde (T.erase u)) ≠ ⊥)
          have hU_ne : U.Nonempty := by
            obtain ⟨u₀, hu₀_mem, hu₀_ne⟩ :=
              h_base S T hS_card hT_card hS_ne hT_ne s_tilde hs_tilde_sd
            exact ⟨u₀, Finset.mem_filter.mpr ⟨hu₀_mem, hu₀_ne⟩⟩
          let Φ : (Fin n ⊕ Fin n) → WithBot ℝ :=
            fun u => ω (insert s_tilde (T.erase u)) + ω (insert u (S.erase s))
          obtain ⟨t_tilde, ht_tilde_U, ht_tilde_max⟩ := Finset.exists_max_image U Φ hU_ne
          have ht_tilde_sd : t_tilde ∈ T \ S := (Finset.mem_filter.mp ht_tilde_U).1
          have ht_tilde_T : t_tilde ∈ T := (Finset.mem_sdiff.mp ht_tilde_sd).1
          have ht_tilde_not_S : t_tilde ∉ S := (Finset.mem_sdiff.mp ht_tilde_sd).2
          let T' := insert s_tilde (T.erase t_tilde)
          have hT'_ne : ω T' ≠ ⊥ := (Finset.mem_filter.mp ht_tilde_U).2
          have hT'_card : T'.card = n := by
            rw [Finset.card_insert_of_notMem
                  (fun hm => hs_tilde_not_T (Finset.mem_erase.mp hm).2),
                Finset.card_erase_add_one ht_tilde_T, hT_card]
          have hST'_eq : S \ T' = (S \ T).erase s_tilde := by
            ext x
            simp only [T', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
            constructor
            · rintro ⟨hxS, hnot⟩
              have hxt : x ≠ t_tilde := fun h => ht_tilde_not_S (h ▸ hxS)
              exact ⟨fun hxs => hnot (Or.inl hxs), hxS, fun hxT => hnot (Or.inr ⟨hxt, hxT⟩)⟩
            · rintro ⟨hxs, hxS, hxT⟩
              exact ⟨hxS, fun h => h.elim hxs (fun ⟨_, hT⟩ => hxT hT)⟩
          have hST'_card : (S \ T').card = k := by
            rw [hST'_eq, Finset.card_erase_of_mem hs_tilde_sd]; omega
          have hs_ST' : s ∈ S \ T' := by
            rw [hST'_eq]; exact Finset.mem_erase.mpr ⟨hs_tilde_ne_s.symm, hs⟩
          obtain ⟨t, ht_T'S, h_ih⟩ :=
            ih S T' hST'_card hS_card hT'_card hS_ne hT'_ne s hs_ST'
          have ht_er_sd : t ∈ (T \ S).erase t_tilde := by
            have ht_T' : t ∈ T' := (Finset.mem_sdiff.mp ht_T'S).1
            have ht_not_S : t ∉ S := (Finset.mem_sdiff.mp ht_T'S).2
            rcases Finset.mem_insert.mp ht_T' with rfl | ht_er
            · exact absurd hs_tilde_S ht_not_S
            · exact Finset.mem_erase.mpr
                ⟨(Finset.mem_erase.mp ht_er).1,
                 Finset.mem_sdiff.mpr ⟨(Finset.mem_erase.mp ht_er).2, ht_not_S⟩⟩
          have ht_ne_tt : t ≠ t_tilde := (Finset.mem_erase.mp ht_er_sd).1
          have ht_sd : t ∈ T \ S := (Finset.mem_erase.mp ht_er_sd).2
          have ht_T : t ∈ T := (Finset.mem_sdiff.mp ht_sd).1
          have ht_not_S : t ∉ S := (Finset.mem_sdiff.mp ht_sd).2
          let T'' := (insert s T').erase t
          have h_lhs1_ne : ω S + ω T' ≠ ⊥ := by simp [WithBot.add_eq_bot, hS_ne, hT'_ne]
          have h_rhs1_ne : ω (insert t (S.erase s)) + ω T'' ≠ ⊥ :=
            fun hb => h_lhs1_ne (le_bot_iff.mp (hb ▸ h_ih))
          have hSt_ne : ω (insert t (S.erase s)) ≠ ⊥ := fun hb => h_rhs1_ne (by simp [hb])
          have hT''_ne : ω T'' ≠ ⊥ := fun hb => h_rhs1_ne (by simp [hb])
          let J := (T.erase t).erase t_tilde
          have hs_J : s ∉ J :=
            fun hm => hs_not_T (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).2
          have hst_J : s_tilde ∉ J :=
            fun hm => hs_tilde_not_T (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).2
          have htt_J : t_tilde ∉ J := Finset.notMem_erase t_tilde (T.erase t)
          have ht_J : t ∉ J := fun hm => (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).1 rfl
          have hs_ne_t : s ≠ t := fun h => hs_not_T (h ▸ ht_T)
          have hs_ne_tt : s ≠ t_tilde := fun h => hs_not_T (h ▸ ht_tilde_T)
          have hst_ne_t : s_tilde ≠ t := fun h => hs_tilde_not_T (h ▸ ht_T)
          have hst_ne_tt : s_tilde ≠ t_tilde := fun h => hs_tilde_not_T (h ▸ ht_tilde_T)
          have hJ_ss : insert s (insert s_tilde J) = T'' := by
            ext x
            simp only [J, T'', T', Finset.mem_insert, Finset.mem_erase]
            by_cases hxt : x = t
            · subst hxt; simp [hs_ne_t.symm, hst_ne_t.symm]
            · simp [hxt]
          have hJ_tt : insert t_tilde (insert t J) = T := by
            ext x
            simp only [J, Finset.mem_insert, Finset.mem_erase]
            by_cases hxtt : x = t_tilde
            · subst hxtt; simp [ht_tilde_T]
            · by_cases hxt : x = t
              · subst hxt; simp [ht_T]
              · simp [hxtt, hxt]
          have hJ_s_tt : insert s (insert t_tilde J) = (insert s T).erase t := by
            ext x
            simp only [J, Finset.mem_insert, Finset.mem_erase]
            by_cases hxt : x = t
            · subst hxt; simp [hs_ne_t.symm, ht_ne_tt]
            · by_cases hxtt : x = t_tilde
              · subst hxtt; simp [ht_ne_tt.symm, ht_tilde_T]
              · simp [hxt, hxtt]
          have hJ_st_t : insert s_tilde (insert t J) = T' := by
            ext x
            simp only [J, T', Finset.mem_insert, Finset.mem_erase]
            by_cases hxtt : x = t_tilde
            · subst hxtt; simp [hst_ne_tt.symm, ht_ne_tt.symm]
            · by_cases hxt : x = t
              · subst hxt; simp [hxtt, ht_T]
              · simp [hxtt, hxt]
          have hJ_s_t : insert s (insert t J) = (insert s T).erase t_tilde := by
            ext x
            simp only [J, Finset.mem_insert, Finset.mem_erase]
            by_cases hxtt : x = t_tilde
            · subst hxtt; simp [hs_ne_tt.symm, ht_ne_tt.symm]
            · by_cases hxt : x = t
              · subst hxt; simp [hxtt, ht_T]
              · simp [hxtt, hxt]
          have hJ_st_tt : insert s_tilde (insert t_tilde J) = insert s_tilde (T.erase t) := by
            ext x
            simp only [J, Finset.mem_insert, Finset.mem_erase]
            by_cases hxtt : x = t_tilde
            · subst hxtt; simp [ht_ne_tt.symm, ht_tilde_T]
            · simp [hxtt]
          have hpl := h_plucker J s s_tilde t_tilde t hs_J hst_J htt_J ht_J
            hs_tilde_ne_s.symm hs_ne_tt hs_ne_t hst_ne_tt hst_ne_t ht_ne_tt.symm
            (hJ_ss.symm ▸ hT''_ne) (hJ_tt.symm ▸ hT_ne)
          rw [hJ_ss, hJ_tt, hJ_s_tt, hJ_st_t, hJ_s_t, hJ_st_tt, le_max_iff] at hpl
          have h_lhs2_ne : ω T'' + ω T ≠ ⊥ := by simp [WithBot.add_eq_bot, hT''_ne, hT_ne]
          obtain ⟨rS, hrS⟩ := WithBot.ne_bot_iff_exists.mp hS_ne
          obtain ⟨rT, hrT⟩ := WithBot.ne_bot_iff_exists.mp hT_ne
          obtain ⟨rT', hrT'⟩ := WithBot.ne_bot_iff_exists.mp hT'_ne
          obtain ⟨rT'', hrT''⟩ := WithBot.ne_bot_iff_exists.mp hT''_ne
          obtain ⟨rSt, hrSt⟩ := WithBot.ne_bot_iff_exists.mp hSt_ne
          have h1_real : rS + rT' ≤ rSt + rT'' := by
            have h := h_ih
            change ω S + ω T' ≤ ω (insert t (S.erase s)) + ω T'' at h
            rw [← hrS, ← hrT', ← hrSt, ← hrT'', ← WithBot.coe_add, ← WithBot.coe_add,
                WithBot.coe_le_coe] at h
            exact h
          clear h_base h_plucker ih
          rcases hpl with hA | hB
          · have h_rhsA_ne : ω ((insert s T).erase t) + ω T' ≠ ⊥ :=
              fun hb => h_lhs2_ne (le_bot_iff.mp (hb ▸ hA))
            have hTs_t_ne : ω ((insert s T).erase t) ≠ ⊥ := fun hb => h_rhsA_ne (by simp [hb])
            obtain ⟨rTs_t, hrTs_t⟩ := WithBot.ne_bot_iff_exists.mp hTs_t_ne
            have hA_real : rT'' + rT ≤ rTs_t + rT' := by
              rw [← hrT'', ← hrT, ← hrTs_t, ← hrT', ← WithBot.coe_add, ← WithBot.coe_add,
                  WithBot.coe_le_coe] at hA
              exact hA
            refine ⟨t, ht_sd, ?_⟩
            rw [← hrS, ← hrT, ← hrSt, ← hrTs_t, ← WithBot.coe_add, ← WithBot.coe_add,
                WithBot.coe_le_coe]
            linarith
          · have h_rhsB_ne : ω ((insert s T).erase t_tilde) + ω (insert s_tilde (T.erase t)) ≠ ⊥ :=
              fun hb => h_lhs2_ne (le_bot_iff.mp (hb ▸ hB))
            have hTs_tt_ne : ω ((insert s T).erase t_tilde) ≠ ⊥ :=
              fun hb => h_rhsB_ne (by simp [hb])
            have hTst_t_ne : ω (insert s_tilde (T.erase t)) ≠ ⊥ :=
              fun hb => h_rhsB_ne (by simp [hb])
            have ht_U : t ∈ U := Finset.mem_filter.mpr ⟨ht_sd, hTst_t_ne⟩
            have h_phi_le : Φ t ≤ Φ t_tilde := ht_tilde_max t ht_U
            have h_phi_t_ne : Φ t ≠ ⊥ := by
              simp [Φ, WithBot.add_eq_bot, hTst_t_ne, hSt_ne]
            have h_phi_tt_ne : Φ t_tilde ≠ ⊥ :=
              fun hb => h_phi_t_ne (le_bot_iff.mp (hb ▸ h_phi_le))
            have hStt_ne : ω (insert t_tilde (S.erase s)) ≠ ⊥ :=
              fun hb => h_phi_tt_ne (by simp [Φ, hb])
            obtain ⟨rTs_tt, hrTs_tt⟩ := WithBot.ne_bot_iff_exists.mp hTs_tt_ne
            obtain ⟨rTst_t, hrTst_t⟩ := WithBot.ne_bot_iff_exists.mp hTst_t_ne
            obtain ⟨rStt, hrStt⟩ := WithBot.ne_bot_iff_exists.mp hStt_ne
            have hB_real : rT'' + rT ≤ rTs_tt + rTst_t := by
              rw [← hrT'', ← hrT, ← hrTs_tt, ← hrTst_t, ← WithBot.coe_add, ← WithBot.coe_add,
                  WithBot.coe_le_coe] at hB
              exact hB
            have h3_real : rTst_t + rSt ≤ rT' + rStt := by
              change ω (insert s_tilde (T.erase t)) + ω (insert t (S.erase s)) ≤
                ω T' + ω (insert t_tilde (S.erase s)) at h_phi_le
              rw [← hrTst_t, ← hrSt, ← hrT', ← hrStt, ← WithBot.coe_add, ← WithBot.coe_add,
                  WithBot.coe_le_coe] at h_phi_le
              exact h_phi_le
            refine ⟨t_tilde, ht_tilde_sd, ?_⟩
            rw [← hrS, ← hrT, ← hrStt, ← hrTs_tt, ← WithBot.coe_add, ← WithBot.coe_add,
                WithBot.coe_le_coe]
            linarith

  refine ⟨fun hp_gs => ?_, h_s1⟩
  clear h_s1
  obtain ⟨h_hered, h_submod⟩ := h_s2 hp_gs
  have h_rgp : HasRGP3 v := h_s3 hp_gs h_hered h_submod
  have h_base : HasEquicardBaseExchange (liftedVal v) := h_s4 h_hered h_rgp
  have h_plucker : HasGrassmannPlucker2 (liftedVal v) := h_s5 h_hered h_submod h_rgp
  clear h_s2 h_s3 h_s4 h_s5 h_hered h_submod h_rgp
  refine ⟨hp_gs.1, fun X Y hvX hvY x hx_sdiff => ?_⟩
  clear hp_gs
  let liftSet : Finset (Fin n) → Finset (Fin n ⊕ Fin n) := fun Z =>
    Z.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
      (Finset.univ \ Z).map ⟨Sum.inr, Sum.inr_injective⟩
  have h_inl_mem : ∀ (Z : Finset (Fin n)) (i : Fin n),
      (Sum.inl i : Fin n ⊕ Fin n) ∈ liftSet Z ↔ i ∈ Z := by
    intro Z i
    simp [liftSet]
  have h_proj_lift : ∀ Z : Finset (Fin n), liftedProj (liftSet Z) = Z := by
    intro Z
    ext i
    simp [liftedProj, h_inl_mem]
  have h_val_lift : ∀ Z : Finset (Fin n), liftedVal v (liftSet Z) = v Z := by
    intro Z
    simp [liftedVal, h_proj_lift]
  have h_card_lift : ∀ Z : Finset (Fin n), (liftSet Z).card = n := by
    intro Z
    have hdisj : Disjoint (Z.map ⟨Sum.inl, Sum.inl_injective⟩)
        ((Finset.univ \ Z).map ⟨Sum.inr, Sum.inr_injective⟩) := by
      refine Finset.disjoint_left.mpr (fun w hw1 hw2 => ?_)
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hw1 hw2
      obtain ⟨a, _, rfl⟩ := hw1
      obtain ⟨b, _, hb⟩ := hw2
      cases hb
    dsimp [liftSet]
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map,
        Finset.card_sdiff_of_subset (Finset.subset_univ Z), Finset.card_univ, Fintype.card_fin]
    have hZ_le : Z.card ≤ n := by simpa using Finset.card_le_univ Z
    omega
  let S := liftSet X
  let T := liftSet Y
  have hS_ne : liftedVal v S ≠ ⊥ := by simpa [S, h_val_lift] using hvX
  have hT_ne : liftedVal v T ≠ ⊥ := by simpa [T, h_val_lift] using hvY
  have hxX : x ∈ X := (Finset.mem_sdiff.mp hx_sdiff).1
  have hxY : x ∉ Y := (Finset.mem_sdiff.mp hx_sdiff).2
  have hs_mem : (Sum.inl x : Fin n ⊕ Fin n) ∈ S \ T := by
    simp [S, T, h_inl_mem, hxX, hxY]
  obtain ⟨t, ht_mem, h_ex⟩ :=
    h_s6 (liftedVal v) h_base h_plucker S T (h_card_lift X) (h_card_lift Y)
      hS_ne hT_ne (Sum.inl x) hs_mem
  clear h_s6 h_base h_plucker
  rw [show liftedVal v S = v X from h_val_lift X,
      show liftedVal v T = v Y from h_val_lift Y] at h_ex
  have hinl_eq : ∀ {a b : Fin n}, (Sum.inl a : Fin n ⊕ Fin n) = Sum.inl b ↔ a = b :=
    ⟨Sum.inl.inj, congrArg Sum.inl⟩
  rcases t with y | d
  · have hy_mem : y ∈ Y \ X := by
      simpa [S, T, h_inl_mem] using ht_mem
    have hproj1 : liftedProj (insert (Sum.inl y) (S.erase (Sum.inl x))) =
        insert y (X.erase x) := by
      ext i
      simp [liftedProj, S, h_inl_mem, hinl_eq]
    have hproj2 : liftedProj ((insert (Sum.inl x) T).erase (Sum.inl y)) =
        (insert x Y).erase y := by
      ext i
      simp [liftedProj, T, h_inl_mem, hinl_eq]
    simp only [liftedVal, hproj1, hproj2] at h_ex
    have h_sup : v (insert y (X.erase x)) + v ((insert x Y).erase y) ≤
        (Y \ X).sup (fun y => v (insert y (X.erase x)) + v ((insert x Y).erase y)) :=
      Finset.le_sup (f := fun y => v (insert y (X.erase x)) + v ((insert x Y).erase y)) hy_mem
    exact le_trans h_ex (le_trans h_sup (le_max_right _ _))
  · have hproj1 : liftedProj (insert (Sum.inr d) (S.erase (Sum.inl x))) = X.erase x := by
      ext i
      simp [liftedProj, S, h_inl_mem, hinl_eq]
    have hproj2 : liftedProj ((insert (Sum.inl x) T).erase (Sum.inr d)) = insert x Y := by
      ext i
      simp [liftedProj, T, h_inl_mem, hinl_eq]
    simp only [liftedVal, hproj1, hproj2] at h_ex
    exact le_trans h_ex (le_max_left _ _)

end

end


section NamedResults

/-- For every valuation `v` with `v(∅) = 0` and every price vector `p ∈ ℝ^N`, the demand
correspondence `𝒟(v, p)` is nonempty and consists solely of bundles in `dom v` (Section 2.1). -/
theorem priceDemand_nonempty {n : ℕ} (v : ItemValuation n) (hv0 : v ∅ = ((0 : ℝ) : WithBot ℝ))
    (p : Fin n → ℝ) :
    (priceDemand v p).Nonempty ∧ ∀ S ∈ priceDemand v p, S ∈ valDom v := by
  constructor
  · obtain ⟨S, -, hS_max⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset (Fin n)))
      (priceUtility v p) ⟨∅, Finset.mem_univ ∅⟩
    refine ⟨S, ?_, fun T => hS_max T (Finset.mem_univ T)⟩
    have h0 : priceUtility v p ∅ = ((0 : ℝ) : WithBot ℝ) := by simp [priceUtility, hv0]
    have hle : ((0 : ℝ) : WithBot ℝ) ≤ priceUtility v p S := by
      rw [← h0]; exact hS_max ∅ (Finset.mem_univ ∅)
    intro hbot
    rw [hbot] at hle
    exact absurd hle (by simp)
  · intro S hS hbot
    exact hS.1 (by simp [priceUtility, hbot])

/-- **Theorem 2.3 (`thm:equivalence`, Prices and exchanges, `[FY03, ST15]`)**:
A valuation `v : 2^N → ℝ ∪ {-∞}` satisfies Kelso–Crawford gross substitutes (`IsGSPrices`,
Definition 2.1) if and only if it satisfies the $M^\natural$-concavity exchange axiom
(`IsGSValuation`, Definition 2.2). -/
theorem thm_2_3_equivalence {n : ℕ} (v : ItemValuation n) :
    IsGSPrices v ↔ IsGSValuation v :=
  thm_gs_prices_iff_exchange n v

end NamedResults

end GrossSubstitutesWelfare
