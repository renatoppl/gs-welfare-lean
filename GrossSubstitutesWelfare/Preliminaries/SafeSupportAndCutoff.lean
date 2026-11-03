import GrossSubstitutesWelfare.Defs

set_option maxHeartbeats 4000000

/-!
# Section 2.3, Section 4.1 (Base) & Appendix D: Safe Region, Additive Support, Sampling & Cutoffs

Formalizes Section 2.3 (`sec:value`), base envelope/prefix properties of Section 4.1, and
Appendix D (`app:cutoff`) of *Gross Substitutes Welfare in Random Order*:
- **Lemma 2.10 (`lem:safe`)**: Submodularity on `dom v` (`lem_2_10_safe_a`), finite-valued GS
  submodularity (`[GS99]`, `rem_2_10_finite_gs_submodular`), and monotonicity/nonnegativity on
  subsets of canonical demands (`lem_2_10_safe_b`);
- **Lemma 2.11 (`lem:support`)**: Additive nonnegative lower support `∑_{g ∈ Y} a_g ≤ v(Y)` on any
  `X ∈ dom v` with `v(X) = max_{Y ⊆ X} v(Y)`;
- **Corollary 2.12 (`cor:value`)**: Inclusion-to-value conversion under canonical-demand safety
  (plus `cor_2_12_value_subset` when `A ⊆ X`);
- **Example 2.13 (`ex:sampling`)**: Independent `1/e`-sampling destroys value on signed GS
  valuations (`n ≥ 6`);
- **Lemma 4.3 (`lem:prefix`)**: Random subsets with marginal probability `λ` preserve `λ · OPT`;
- **Lemma D.1 (`lem:cutoff`)**: Existence of a secretary cutoff `s ∈ {1, ..., n - 1}` with
  `c_n(s) ≥ 1 / e` for every `n ≥ 2`.
-/

namespace GrossSubstitutesWelfare

open Classical MeasureTheory

noncomputable section

theorem thm_gs_safe_support_envelopes_cutoff :
    -- (1a) Lemma 2.10(a): Submodularity on dom v
    (∀ n (v : ItemValuation n) (Q R : Finset (Fin n)) (g : Fin n),
      IsGSValuation v → Q ⊆ R → g ∉ R → v (insert g R) ≠ ⊥ →
        marginalVal v R g ≤ marginalVal v Q g) ∧
    -- (1b) Lemma 2.10(b): Monotonicity and nonnegativity inside canonical demands
    (∀ n (v : ItemValuation n) (T : Finset (Fin n)),
      IsGSValuation v →
        let X := canonicalDemand v T
        (∀ Y ⊆ X, v Y ≠ ⊥ ∧ 0 ≤ realVal v Y) ∧
        (∀ Y Z : Finset (Fin n), Y ⊆ Z → Z ⊆ X → v Y ≤ v Z)) ∧
    -- (2) Lemma 2.11: Additive lower support
    (∀ n (v : ItemValuation n) (X : Finset (Fin n)),
      IsGSValuation v → v X ≠ ⊥ → (∀ Y ⊆ X, v Y ≤ v X) →
        ∃ a : Fin n → ℝ,
          (∀ g ∈ X, 0 ≤ a g) ∧
          (∑ g ∈ X, a g) = realVal v X ∧
          (∀ Y ⊆ X, ((∑ g ∈ Y, a g : ℝ) : WithBot ℝ) ≤ v Y)) ∧
    -- (3) Corollary 2.12: From inclusion probabilities to expected value
    (∀ n (v : ItemValuation n) (X : Finset (Fin n))
        (p : Finset (Fin n) → ℝ) (ρ : ℝ),
      IsGSValuation v → v X ≠ ⊥ → (∀ Y ⊆ X, v Y ≤ v X) →
      (∀ A, 0 ≤ p A) → (∑ A : Finset (Fin n), p A) = 1 →
      (∀ A, 0 < p A → ∃ T : Finset (Fin n), A ⊆ canonicalDemand v T) →
      (∀ g ∈ X, ρ ≤ ∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => g ∈ A), p A) →
        (∀ A, 0 < p A → v A ≠ ⊥) ∧
        ρ * realVal v X ≤ ∑ A : Finset (Fin n), p A * realVal v A) ∧
    -- (4) Example 2.13: Independent 1/e sampling destroys value for n ≥ 6
    (∀ (n : ℕ) (hn : 6 ≤ n),
      let v : ItemValuation n :=
        fun S => (((2 * (min S.card 1 : ℕ) : ℝ) - (S.card : ℝ) : ℝ) : WithBot ℝ)
      let p : Finset (Fin n) → ℝ :=
        fun A => invE ^ A.card * (1 - invE) ^ (n - A.card)
      let g0 : Fin n := ⟨0, by omega⟩
      IsGSValuation v ∧
      optVal v = 1 ∧
      canonicalDemand v Finset.univ = {g0} ∧
      (∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => g0 ∈ A), p A) = invE ∧
      (∑ A : Finset (Fin n), p A * realVal v A) < 0) ∧
    -- (5) Lemma 4.2 (base properties): Disposal envelopes
    (∀ n (v : ItemValuation n), IsGSValuation v →
      disposalEnvelope v ∅ = 0 ∧
      (∀ S, 0 ≤ disposalEnvelope v S) ∧
      (∀ S T : Finset (Fin n), S ⊆ T → disposalEnvelope v S ≤ disposalEnvelope v T) ∧
      IsSubmodularReal (disposalEnvelope v)) ∧
    (∀ n m (v : Fin m → ItemValuation n), (∀ i, IsGSValuation (v i)) →
      optWelfare (fun i S => ((disposalEnvelope (v i) S : ℝ) : WithBot ℝ)) = optWelfare v) ∧
    -- (6) Lemma 4.3: Random subsets preserve proportional optimal welfare
    (∀ n m (v : Fin m → ItemValuation n) (p : Finset (Fin n) → ℝ) (lam : ℝ),
      (∀ i, IsGSValuation (v i)) →
      (∀ R, 0 ≤ p R) → (∑ R : Finset (Fin n), p R) = 1 →
      (∀ g : Fin n,
        (∑ R ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun R => g ∈ R), p R) = lam) →
        lam * optWelfare v ≤ ∑ R : Finset (Fin n), p R * optWelfareOn v R) ∧
    -- (7) Lemma D.1: Finite-n secretary cutoff achieves 1/e for all n ≥ 2
    (∀ n : ℕ, 2 ≤ n → ∃ s ∈ Finset.Ico 1 n, invE ≤ secretaryCutoffConst n s) :=
by
  have coe_unbotD : ∀ {z : WithBot ℝ}, z ≠ ⊥ → ((z.unbotD 0 : ℝ) : WithBot ℝ) = z := by
    intro z hz
    obtain ⟨r, rfl⟩ := WithBot.ne_bot_iff_exists.mp hz
    rw [WithBot.unbotD_coe]
  have coe_realVal : ∀ {n : ℕ} (v : ItemValuation n) (S : Finset (Fin n)),
      v S ≠ ⊥ → ((realVal v S : ℝ) : WithBot ℝ) = v S := by
    intro n v S hS
    exact coe_unbotD hS
  have dom_erase : ∀ {n : ℕ} {v : ItemValuation n}, IsGSValuation v →
      ∀ (X : Finset (Fin n)) (x : Fin n), v X ≠ ⊥ → x ∈ X → v (X.erase x) ≠ ⊥ := by
    intro n v hv X x hX hx
    have hv0 : v ∅ ≠ ⊥ := by rw [hv.1]; exact WithBot.coe_ne_bot
    have hx_sdiff : x ∈ X \ ∅ := by simp [hx]
    have hex := hv.2 X ∅ hX hv0 x hx_sdiff
    have hsdiff_emp : (∅ : Finset (Fin n)) \ X = ∅ := by simp
    rw [hsdiff_emp, Finset.sup_empty, max_bot_right] at hex
    have hlhs_ne : v X + v ∅ ≠ ⊥ := by
      rw [← coe_realVal v X hX, hv.1, ← WithBot.coe_add]
      exact WithBot.coe_ne_bot
    intro h_eq_bot
    rw [h_eq_bot, WithBot.bot_add, le_bot_iff] at hex
    exact hlhs_ne hex
  have dom_hereditary : ∀ {n : ℕ} {v : ItemValuation n}, IsGSValuation v →
      ∀ {X Y : Finset (Fin n)}, Y ⊆ X → v X ≠ ⊥ → v Y ≠ ⊥ := by
    intro n v hv X Y hYX hX
    have h_ind : ∀ (k : ℕ) (X : Finset (Fin n)), (X \ Y).card = k → Y ⊆ X → v X ≠ ⊥ → v Y ≠ ⊥ := by
      intro k
      induction k with
      | zero =>
        intro X hk hYX hX
        have hsub : X ⊆ Y := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hk)
        have hXY : Y = X := Finset.Subset.antisymm hYX hsub
        rwa [hXY]
      | succ k ih =>
        intro X hk hYX hX
        have hne : (X \ Y).Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨x, hx⟩ := hne
        obtain ⟨hxX, hxY⟩ := Finset.mem_sdiff.mp hx
        have hX' : v (X.erase x) ≠ ⊥ := dom_erase hv X x hX hxX
        have hYX' : Y ⊆ X.erase x := Finset.subset_erase.mpr ⟨hYX, hxY⟩
        have hsdiff : X.erase x \ Y = (X \ Y).erase x := by
          ext z; simp [and_assoc]
        have hk' : (X.erase x \ Y).card = k := by
          rw [hsdiff, Finset.card_erase_of_mem hx]
          omega
        exact ih (X.erase x) hk' hYX' hX'
    exact h_ind (X \ Y).card X rfl hYX hX
  have part_1a : ∀ n (v : ItemValuation n) (Q R : Finset (Fin n)) (g : Fin n),
      IsGSValuation v → Q ⊆ R → g ∉ R → v (insert g R) ≠ ⊥ →
        marginalVal v R g ≤ marginalVal v Q g := by
    intro n v Q R g hv hQR hgR hRg
    have hgQ : g ∉ Q := fun hg => hgR (hQR hg)
    have hR : v R ≠ ⊥ := dom_hereditary hv (Finset.subset_insert g R) hRg
    have hQg : v (insert g Q) ≠ ⊥ :=
      dom_hereditary hv (Finset.insert_subset_insert g hQR) hRg
    have hQ : v Q ≠ ⊥ := dom_hereditary hv (hQR.trans (Finset.subset_insert g R)) hRg
    have hg_mem : g ∈ insert g R \ Q := Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self g R, hgQ⟩
    have hex := hv.2 (insert g R) Q hRg hQ g hg_mem
    have hsdiff_empty : Q \ insert g R = ∅ :=
      Finset.sdiff_eq_empty_iff_subset.mpr (hQR.trans (Finset.subset_insert g R))
    rw [Finset.erase_insert hgR, hsdiff_empty, Finset.sup_empty, max_bot_right] at hex
    rw [← coe_realVal v (insert g R) hRg, ← coe_realVal v Q hQ,
        ← coe_realVal v R hR, ← coe_realVal v (insert g Q) hQg,
        ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe] at hex
    dsimp [marginalVal]
    linarith
  have part_1b : ∀ n (v : ItemValuation n) (T : Finset (Fin n)),
      IsGSValuation v →
        let X := canonicalDemand v T
        (∀ Y ⊆ X, v Y ≠ ⊥ ∧ 0 ≤ realVal v Y) ∧
        (∀ Y Z : Finset (Fin n), Y ⊆ Z → Z ⊆ X → v Y ≤ v Z) := by
    intro n v T hv
    dsimp only
    have hex : ∃ X₀ ∈ T.powerset, ∀ Y ∈ T.powerset, demandKeyLe v Y X₀ := by
      let f : Finset (Fin n) → WithBot ℝ ×ₗ ℝ := fun S => toLex (v S, psiWeight S)
      have hne : T.powerset.Nonempty := ⟨∅, Finset.empty_mem_powerset T⟩
      obtain ⟨X₀, hX₀_mem, hX₀_max⟩ := Finset.exists_max_image T.powerset f hne
      refine ⟨X₀, hX₀_mem, fun Y hY => ?_⟩
      have hle := hX₀_max Y hY
      rwa [Prod.Lex.toLex_le_toLex] at hle
    set X := canonicalDemand v T
    have hX_def : X = Classical.choose hex := dif_pos hex
    obtain ⟨hX_mem, hX_max⟩ := Classical.choose_spec hex
    rw [← hX_def] at hX_mem hX_max
    have hXT : X ⊆ T := Finset.mem_powerset.mp hX_mem
    have hX_v_max : ∀ Y ⊆ T, v Y ≤ v X := by
      intro Y hYT
      rcases hX_max Y (Finset.mem_powerset.mpr hYT) with hlt | ⟨heq, _⟩
      · exact le_of_lt hlt
      · exact le_of_eq heq
    have hX_ne_bot : v X ≠ ⊥ := by
      have h0 : v ∅ ≤ v X := hX_v_max ∅ (Finset.empty_subset T)
      rw [hv.1] at h0
      intro hbot
      rw [hbot, le_bot_iff] at h0
      exact WithBot.coe_ne_bot h0
    have hY_ne_bot : ∀ Y ⊆ X, v Y ≠ ⊥ := fun Y hYX => dom_hereditary hv hYX hX_ne_bot
    have h_erase_mono : ∀ Z ⊆ X, ∀ g ∈ Z, v (Z.erase g) ≤ v Z := by
      intro Z hZX g hgZ
      have hXg : g ∈ X := hZX hgZ
      have hsub : Finset.erase Z g ⊆ Finset.erase X g := by
        intro z hz
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hz).1, hZX (Finset.mem_erase.mp hz).2⟩
      have hg_not : g ∉ Finset.erase X g := Finset.notMem_erase g X
      have h_ins_X : insert g (Finset.erase X g) = X := Finset.insert_erase hXg
      have h_ins_Z : insert g (Finset.erase Z g) = Z := Finset.insert_erase hgZ
      have h_submod := part_1a n v (Finset.erase Z g) (Finset.erase X g) g hv hsub hg_not (by rwa [h_ins_X])
      have hXe_ne : v (Finset.erase X g) ≠ ⊥ := hY_ne_bot (Finset.erase X g) (Finset.erase_subset g X)
      have hXe_le : v (Finset.erase X g) ≤ v X := hX_v_max (Finset.erase X g) ((Finset.erase_subset g X).trans hXT)
      rw [← coe_realVal v (Finset.erase X g) hXe_ne, ← coe_realVal v X hX_ne_bot, WithBot.coe_le_coe] at hXe_le
      dsimp [marginalVal] at h_submod
      rw [h_ins_X, h_ins_Z] at h_submod
      have hZe_ne : v (Finset.erase Z g) ≠ ⊥ := hY_ne_bot (Finset.erase Z g) ((Finset.erase_subset g Z).trans hZX)
      have hZ_ne : v Z ≠ ⊥ := hY_ne_bot Z hZX
      rw [← coe_realVal v (Finset.erase Z g) hZe_ne, ← coe_realVal v Z hZ_ne, WithBot.coe_le_coe]
      linarith
    have h_mono : ∀ Y Z : Finset (Fin n), Y ⊆ Z → Z ⊆ X → v Y ≤ v Z := by
      intro Y Z hYZ hZX
      have h_ind : ∀ (k : ℕ) (Z : Finset (Fin n)), (Z \ Y).card = k → Y ⊆ Z → Z ⊆ X → v Y ≤ v Z := by
        intro k
        induction k with
        | zero =>
          intro Z hk hYZ _
          have hZY : Z ⊆ Y := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hk)
          rw [Finset.Subset.antisymm hYZ hZY]
        | succ k ih =>
          intro Z hk hYZ hZX
          have hne : (Z \ Y).Nonempty := Finset.card_pos.mp (by omega)
          obtain ⟨g, hg⟩ := hne
          obtain ⟨hgZ, hgY⟩ := Finset.mem_sdiff.mp hg
          have hYZe : Y ⊆ Finset.erase Z g := Finset.subset_erase.mpr ⟨hYZ, hgY⟩
          have hZeX : Finset.erase Z g ⊆ X := (Finset.erase_subset g Z).trans hZX
          have hsdiff : Finset.erase Z g \ Y = Finset.erase (Z \ Y) g := by
            ext z; simp [and_assoc]
          have hk' : (Finset.erase Z g \ Y).card = k := by
            rw [hsdiff, Finset.card_erase_of_mem hg]; omega
          exact (ih (Finset.erase Z g) hk' hYZe hZeX).trans (h_erase_mono Z hZX g hgZ)
      exact h_ind (Z \ Y).card Z rfl hYZ hZX
    refine ⟨fun Y hYX => ⟨hY_ne_bot Y hYX, ?_⟩, h_mono⟩
    have h0Y : v ∅ ≤ v Y := h_mono ∅ Y (Finset.empty_subset Y) hYX
    rw [hv.1, ← coe_realVal v Y (hY_ne_bot Y hYX), WithBot.coe_le_coe] at h0Y
    exact h0Y
  have part_2 : ∀ n (v : ItemValuation n) (X : Finset (Fin n)),
      IsGSValuation v → v X ≠ ⊥ → (∀ Y ⊆ X, v Y ≤ v X) →
        ∃ a : Fin n → ℝ,
          (∀ g ∈ X, 0 ≤ a g) ∧
          (∑ g ∈ X, a g) = realVal v X ∧
          (∀ Y ⊆ X, ((∑ g ∈ Y, a g : ℝ) : WithBot ℝ) ≤ v Y) := by
    intro n v X hv hX hXmax
    have h_tele : ∀ (k : ℕ) (Y : Finset (Fin n)), Y.card ≤ k →
        ∑ g ∈ Y, marginalVal v (Y.filter (fun h => h < g)) g = realVal v Y := by
      intro k
      induction k with
      | zero =>
        intro Y hk
        have hY : Y = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hk)
        subst hY
        simp [realVal, hv.1]
      | succ k ih =>
        intro Y hk
        rcases Y.eq_empty_or_nonempty with rfl | hYne
        · simp [realVal, hv.1]
        · let m := Y.max' hYne
          have hmY : m ∈ Y := Finset.max'_mem Y hYne
          let Y' := Finset.erase Y m
          have hY'_card : Y'.card ≤ k := by
            dsimp [Y']
            have hlt := Finset.card_erase_lt_of_mem hmY
            omega
          rw [← Finset.add_sum_erase Y _ hmY]
          have h_filt_m : Y.filter (fun h => h < m) = Y' := by
            ext y
            simp only [Finset.mem_filter, Y', Finset.mem_erase]
            constructor
            · rintro ⟨hyY, hylt⟩
              exact ⟨ne_of_lt hylt, hyY⟩
            · rintro ⟨hyne, hyY⟩
              exact ⟨hyY, lt_of_le_of_ne (Finset.le_max' Y y hyY) hyne⟩
          have h_ins_m : insert m Y' = Y := Finset.insert_erase hmY
          have h_term_m : marginalVal v (Y.filter (fun h => h < m)) m = realVal v Y - realVal v Y' := by
            dsimp [marginalVal]
            rw [h_filt_m, h_ins_m]
          have h_rest : ∑ g ∈ Y', marginalVal v (Y.filter (fun h => h < g)) g =
              ∑ g ∈ Y', marginalVal v (Y'.filter (fun h => h < g)) g := by
            refine Finset.sum_congr rfl (fun g hgY' => ?_)
            obtain ⟨hgne, hgY⟩ := Finset.mem_erase.mp hgY'
            have hglt : g < m := lt_of_le_of_ne (Finset.le_max' Y g hgY) hgne
            have h_filt_g : Y.filter (fun h => h < g) = Y'.filter (fun h => h < g) := by
              ext y
              simp only [Finset.mem_filter, Y', Finset.mem_erase]
              constructor
              · rintro ⟨hyY, hylt⟩
                exact ⟨⟨ne_of_lt (lt_trans hylt hglt), hyY⟩, hylt⟩
              · rintro ⟨⟨_, hyY⟩, hylt⟩
                exact ⟨hyY, hylt⟩
            rw [h_filt_g]
          rw [h_term_m, h_rest, ih Y' hY'_card]
          ring
    let a : Fin n → ℝ := fun g => marginalVal v (X.filter (fun h => h < g)) g
    refine ⟨a, ?_, h_tele X.card X le_rfl, ?_⟩
    · intro g hgX
      have hsub : X.filter (fun h => h < g) ⊆ Finset.erase X g := by
        intro h hh
        obtain ⟨hhX, hhlt⟩ := Finset.mem_filter.mp hh
        exact Finset.mem_erase.mpr ⟨ne_of_lt hhlt, hhX⟩
      have hg_not : g ∉ Finset.erase X g := Finset.notMem_erase g X
      have h_ins : insert g (Finset.erase X g) = X := Finset.insert_erase hgX
      have h_submod := part_1a n v (X.filter (fun h => h < g)) (Finset.erase X g) g hv hsub hg_not (by rwa [h_ins])
      have hXe_ne : v (Finset.erase X g) ≠ ⊥ := dom_hereditary hv (Finset.erase_subset g X) hX
      have hXe_le : v (Finset.erase X g) ≤ v X := hXmax (Finset.erase X g) (Finset.erase_subset g X)
      rw [← coe_realVal v (Finset.erase X g) hXe_ne, ← coe_realVal v X hX, WithBot.coe_le_coe] at hXe_le
      dsimp [a, marginalVal] at h_submod ⊢
      rw [h_ins] at h_submod
      linarith
    · intro Y hYX
      have hY_ne : v Y ≠ ⊥ := dom_hereditary hv hYX hX
      have h_le_real : ∑ g ∈ Y, a g ≤ realVal v Y := by
        calc
          ∑ g ∈ Y, a g ≤ ∑ g ∈ Y, marginalVal v (Y.filter (fun h => h < g)) g := by
            refine Finset.sum_le_sum (fun g hgY => ?_)
            have hsub : Y.filter (fun h => h < g) ⊆ X.filter (fun h => h < g) :=
              Finset.filter_subset_filter _ hYX
            have hg_not : g ∉ X.filter (fun h => h < g) := by simp
            have h_ins_sub : insert g (X.filter (fun h => h < g)) ⊆ X :=
              Finset.insert_subset_iff.mpr ⟨hYX hgY, Finset.filter_subset _ X⟩
            exact part_1a n v (Y.filter (fun h => h < g)) (X.filter (fun h => h < g)) g hv
              hsub hg_not (dom_hereditary hv h_ins_sub hX)
          _ = realVal v Y := h_tele Y.card Y le_rfl
      rw [← coe_realVal v Y hY_ne, WithBot.coe_le_coe]
      exact h_le_real
  have part_3 : ∀ n (v : ItemValuation n) (X : Finset (Fin n))
      (p : Finset (Fin n) → ℝ) (ρ : ℝ),
      IsGSValuation v → v X ≠ ⊥ → (∀ Y ⊆ X, v Y ≤ v X) →
      (∀ A, 0 ≤ p A) → (∑ A : Finset (Fin n), p A) = 1 →
      (∀ A, 0 < p A → ∃ T : Finset (Fin n), A ⊆ canonicalDemand v T) →
      (∀ g ∈ X, ρ ≤ ∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => g ∈ A), p A) →
        (∀ A, 0 < p A → v A ≠ ⊥) ∧
        ρ * realVal v X ≤ ∑ A : Finset (Fin n), p A * realVal v A := by
    intro n v X p ρ hv hX hXmax hp0 _ hsafe hinc
    have h_dom_A : ∀ A, 0 < p A → v A ≠ ⊥ := by
      intro A hpA
      obtain ⟨T, hAT⟩ := hsafe A hpA
      exact ((part_1b n v T hv).1 A hAT).1
    refine ⟨h_dom_A, ?_⟩
    obtain ⟨a, ha_nn, ha_sum, ha_low⟩ := part_2 n v X hv hX hXmax
    have h_ptwise : ∀ A : Finset (Fin n),
        p A * (∑ g ∈ X.filter (fun g => g ∈ A), a g) ≤ p A * realVal v A := by
      intro A
      rcases lt_or_eq_of_le (hp0 A) with hpA_pos | hpA_zero
      · obtain ⟨T, hAT⟩ := hsafe A hpA_pos
        have h_safe_T := part_1b n v T hv
        let Y_A := X.filter (fun g => g ∈ A)
        have hYA_X : Y_A ⊆ X := Finset.filter_subset _ X
        have hYA_A : Y_A ⊆ A := fun g hg => (Finset.mem_filter.mp hg).2
        have hA_ne : v A ≠ ⊥ := (h_safe_T.1 A hAT).1
        have hv_le : v Y_A ≤ v A := h_safe_T.2 Y_A A hYA_A hAT
        have ha_le : ((∑ g ∈ Y_A, a g : ℝ) : WithBot ℝ) ≤ v A :=
          (ha_low Y_A hYA_X).trans hv_le
        rw [← coe_realVal v A hA_ne, WithBot.coe_le_coe] at ha_le
        exact mul_le_mul_of_nonneg_left ha_le (le_of_lt hpA_pos)
      · rw [← hpA_zero, zero_mul, zero_mul]
    have h_sum_A : ∑ A : Finset (Fin n), p A * (∑ g ∈ X.filter (fun g => g ∈ A), a g) ≤
        ∑ A : Finset (Fin n), p A * realVal v A :=
      Finset.sum_le_sum (fun A _ => h_ptwise A)
    have h_swap : ∑ A : Finset (Fin n), p A * (∑ g ∈ X.filter (fun g => g ∈ A), a g) =
        ∑ g ∈ X, (∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => g ∈ A), p A) * a g := by
      calc
        ∑ A : Finset (Fin n), p A * (∑ g ∈ X.filter (fun g => g ∈ A), a g)
          = ∑ A : Finset (Fin n), ∑ g ∈ X, (if g ∈ A then p A * a g else 0) := by
            refine Finset.sum_congr rfl (fun A _ => ?_)
            rw [Finset.sum_filter, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun g _ => ?_)
            split_ifs <;> ring
        _ = ∑ g ∈ X, ∑ A : Finset (Fin n), (if g ∈ A then p A * a g else 0) := Finset.sum_comm
        _ = ∑ g ∈ X, (∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => g ∈ A), p A) * a g := by
            refine Finset.sum_congr rfl (fun g _ => ?_)
            rw [← Finset.sum_filter, Finset.sum_mul]
    have h_rho : ρ * realVal v X ≤
        ∑ g ∈ X, (∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => g ∈ A), p A) * a g := by
      rw [← ha_sum, Finset.mul_sum]
      refine Finset.sum_le_sum (fun g hgX => ?_)
      exact mul_le_mul_of_nonneg_right (hinc g hgX) (ha_nn g hgX)
    linarith
  have part_4 : ∀ (n : ℕ) (hn : 6 ≤ n),
      let v : ItemValuation n :=
        fun S => (((2 * (min S.card 1 : ℕ) : ℝ) - (S.card : ℝ) : ℝ) : WithBot ℝ)
      let p : Finset (Fin n) → ℝ :=
        fun A => invE ^ A.card * (1 - invE) ^ (n - A.card)
      let g0 : Fin n := ⟨0, by omega⟩
      IsGSValuation v ∧
      optVal v = 1 ∧
      canonicalDemand v Finset.univ = {g0} ∧
      (∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => g0 ∈ A), p A) = invE ∧
      (∑ A : Finset (Fin n), p A * realVal v A) < 0 := by
    intro n hn v p g0
    let h : ℕ → ℝ := fun k => (2 * (min k 1 : ℕ) : ℝ) - (k : ℝ)
    have hv_eq : ∀ S : Finset (Fin n), v S = ((h S.card : ℝ) : WithBot ℝ) := fun _ => rfl
    have h_realVal : ∀ S : Finset (Fin n), realVal v S = h S.card := by
      intro S; simp [realVal, hv_eq]
    have h_zero : h 0 = 0 := by norm_num [h]
    have h_one : h 1 = 1 := by norm_num [h]
    have h_ge_one : ∀ k : ℕ, 1 ≤ k → h k = 2 - (k : ℝ) := by
      intro k hk
      dsimp [h]
      rw [Nat.min_eq_right hk]
      norm_num
    have h_gs : IsGSValuation v := by
      refine ⟨by simp [hv_eq, h_zero], ?_⟩
      intro X Y _ _ x hx
      obtain ⟨hxX, hxY⟩ := Finset.mem_sdiff.mp hx
      have hX_pos : 1 ≤ X.card := Finset.card_pos.mpr ⟨x, hxX⟩
      have hXe_card : (Finset.erase X x).card = X.card - 1 := Finset.card_erase_of_mem hxX
      have hYx_card : (insert x Y).card = Y.card + 1 := Finset.card_insert_of_notMem hxY
      rcases Y.eq_empty_or_nonempty with rfl | hYne
      · refine le_trans ?_ (le_max_left _ _)
        rw [hv_eq, hv_eq, hv_eq, hv_eq, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
        simp only [Finset.card_empty, h_zero, add_zero, hXe_card, hYx_card, zero_add, h_one]
        rcases eq_or_lt_of_le hX_pos with hX1 | hX2
        · rw [← hX1, Nat.sub_self, h_zero, h_one]; norm_num
        · have h1 : 1 ≤ X.card - 1 := by omega
          rw [h_ge_one X.card hX_pos, h_ge_one (X.card - 1) h1]
          have hcast : ((X.card - 1 : ℕ) : ℝ) = (X.card : ℝ) - 1 := by
            simpa using (Nat.cast_sub hX_pos : ((X.card - 1 : ℕ) : ℝ) = _)
          linarith
      · have hY_pos : 1 ≤ Y.card := Finset.card_pos.mpr hYne
        rcases eq_or_lt_of_le hX_pos with hX1 | hX2
        · obtain ⟨y, hyY⟩ := hYne
          have hyX : y ∉ X := by
            intro hyX_mem
            have hXe_empty : Finset.erase X x = ∅ := Finset.card_eq_zero.mp (by omega)
            have hX_sing : X = {x} := by
              rw [← Finset.insert_erase hxX, hXe_empty]; rfl
            rw [hX_sing, Finset.mem_singleton] at hyX_mem
            exact hxY (hyX_mem ▸ hyY)
          have hy_sdiff : y ∈ Y \ X := Finset.mem_sdiff.mpr ⟨hyY, hyX⟩
          refine le_trans ?_ (le_max_right _ _)
          refine le_trans ?_ (Finset.le_sup (f := fun y => v (insert y (Finset.erase X x)) + v (Finset.erase (insert x Y) y)) hy_sdiff)
          dsimp only
          have hXe_empty : Finset.erase X x = ∅ := Finset.card_eq_zero.mp (by omega)
          have h_ins_y : (insert y (Finset.erase X x)).card = 1 := by rw [hXe_empty]; simp
          have hy_ins : y ∈ insert x Y := Finset.mem_insert_of_mem hyY
          have h_er_y : (Finset.erase (insert x Y) y).card = Y.card := by
            rw [Finset.card_erase_of_mem hy_ins, hYx_card]; omega
          rw [hv_eq, hv_eq, hv_eq, hv_eq, ← hX1, h_ins_y, h_er_y]
        · refine le_trans ?_ (le_max_left _ _)
          rw [hv_eq, hv_eq, hv_eq, hv_eq, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
          rw [hXe_card, hYx_card]
          have h1 : 1 ≤ X.card - 1 := by omega
          have h2 : 1 ≤ Y.card + 1 := by omega
          rw [h_ge_one X.card hX_pos, h_ge_one Y.card hY_pos,
              h_ge_one (X.card - 1) h1, h_ge_one (Y.card + 1) h2]
          have hcast1 : ((X.card - 1 : ℕ) : ℝ) = (X.card : ℝ) - 1 := by
            simpa using (Nat.cast_sub hX_pos : ((X.card - 1 : ℕ) : ℝ) = _)
          push_cast [hcast1]
          linarith
    have h_opt : optVal v = 1 := by
      have h_sup : (Finset.univ : Finset (Finset (Fin n))).sup v = ((1 : ℝ) : WithBot ℝ) := by
        refine le_antisymm ?_ ?_
        · refine Finset.sup_le (fun S _ => ?_)
          rw [hv_eq, WithBot.coe_le_coe]
          rcases Nat.eq_zero_or_pos S.card with hc0 | hcpos
          · rw [hc0, h_zero]; norm_num
          · rw [h_ge_one S.card hcpos]
            have : (1 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hcpos
            linarith
        · refine le_trans ?_ (Finset.le_sup (Finset.mem_univ ({g0} : Finset (Fin n))))
          rw [hv_eq, Finset.card_singleton, h_one]
      simp [optVal, h_sup]
    have h_cd : canonicalDemand v Finset.univ = {g0} := by
      have hv_g0 : v {g0} = ((1 : ℝ) : WithBot ℝ) := by rw [hv_eq, Finset.card_singleton, h_one]
      have hpsi_g0 : psiWeight ({g0} : Finset (Fin n)) = 3 / 2 := by
        simp [psiWeight, g0]
        norm_num
      have h_strict : ∀ Y : Finset (Fin n), Y ≠ {g0} →
          v Y < v {g0} ∨ (v Y = v {g0} ∧ psiWeight Y < psiWeight {g0}) := by
        intro Y hYne
        rcases Nat.eq_zero_or_pos Y.card with hc0 | hcpos
        · left
          rw [hv_eq, hc0, h_zero, hv_g0, WithBot.coe_lt_coe]
          norm_num
        · have hcpos1 : 1 ≤ Y.card := hcpos
          rcases eq_or_lt_of_le hcpos1 with hc1 | hc2
          · right
            obtain ⟨g, rfl⟩ := Finset.card_eq_one.mp hc1.symm
            have hg_ne : g ≠ g0 := fun h_eq => hYne (by rw [h_eq])
            have hg_val_pos : 1 ≤ g.1 := by
              by_contra h_zero_val
              apply hg_ne
              ext
              simp [g0]
              omega
            refine ⟨by rw [hv_eq, Finset.card_singleton, h_one, hv_g0], ?_⟩
            have hpsi_g : psiWeight ({g} : Finset (Fin n)) = 1 + (1 / 2 : ℝ) ^ (g.1 + 1) := by
              simp [psiWeight]
            have hpow : (1 / 2 : ℝ) ^ (g.1 + 1) ≤ (1 / 2 : ℝ) ^ 2 :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
            rw [hpsi_g, hpsi_g0]
            linarith [show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num]
          · left
            rw [hv_eq, h_ge_one Y.card hcpos1, hv_g0, WithBot.coe_lt_coe]
            have : (2 : ℝ) ≤ (Y.card : ℝ) := by exact_mod_cast hc2
            linarith
      have hex : ∃ X ∈ (Finset.univ : Finset (Fin n)).powerset,
          ∀ Y ∈ (Finset.univ : Finset (Fin n)).powerset, demandKeyLe v Y X := by
        refine ⟨{g0}, Finset.mem_powerset.mpr (Finset.subset_univ _), fun Y _ => ?_⟩
        by_cases hY : Y = {g0}
        · subst hY; exact Or.inr ⟨rfl, le_rfl⟩
        · rcases h_strict Y hY with hlt | ⟨heq, hpsi⟩
          · exact Or.inl hlt
          · exact Or.inr ⟨heq, le_of_lt hpsi⟩
      have hcd_def : canonicalDemand v Finset.univ = Classical.choose hex := dif_pos hex
      rw [hcd_def]
      obtain ⟨_, hmax⟩ := Classical.choose_spec hex
      have h_le := hmax {g0} (Finset.mem_powerset.mpr (Finset.subset_univ _))
      by_contra h_ne
      rcases h_strict (Classical.choose hex) h_ne with hlt | ⟨heq, hpsi⟩
      · rcases h_le with hlt' | ⟨heq', _⟩
        · exact lt_asymm hlt hlt'
        · rw [heq'] at hlt; exact lt_irrefl _ hlt
      · rcases h_le with hlt' | ⟨_, hpsi'⟩
        · rw [heq] at hlt'; exact lt_irrefl _ hlt'
        · exact not_lt_of_ge hpsi' hpsi
    have h_powerset_sum : ∀ S : Finset (Fin n),
        ∑ B ∈ S.powerset, invE ^ B.card * (1 - invE) ^ (S.card - B.card) = 1 := by
      intro S
      rw [Finset.sum_powerset]
      have h_inner : ∀ k ∈ Finset.range (S.card + 1),
          ∑ B ∈ Finset.powersetCard k S, invE ^ B.card * (1 - invE) ^ (S.card - B.card) =
            invE ^ k * (1 - invE) ^ (S.card - k) * (S.card.choose k : ℝ) := by
        intro k _
        have h_congr : ∑ B ∈ Finset.powersetCard k S, invE ^ B.card * (1 - invE) ^ (S.card - B.card) =
            ∑ _B ∈ Finset.powersetCard k S, invE ^ k * (1 - invE) ^ (S.card - k) := by
          refine Finset.sum_congr rfl (fun B hB => ?_)
          rw [(Finset.mem_powersetCard.mp hB).2]
        rw [h_congr, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, mul_comm]
      rw [Finset.sum_congr rfl h_inner, ← add_pow]
      ring
    have h_univ_sum : ∑ A : Finset (Fin n), p A = 1 := by
      have h_eq_pow : (Finset.univ : Finset (Finset (Fin n))) = (Finset.univ : Finset (Fin n)).powerset := by
        ext A; simp
      have h_card_univ : (Finset.univ : Finset (Fin n)).card = n := Finset.card_fin n
      calc
        ∑ A : Finset (Fin n), p A
          = ∑ A ∈ (Finset.univ : Finset (Fin n)).powerset,
              invE ^ A.card * (1 - invE) ^ ((Finset.univ : Finset (Fin n)).card - A.card) := by
            rw [← h_eq_pow, h_card_univ]
        _ = 1 := h_powerset_sum Finset.univ
    have h_marg : ∀ g : Fin n,
        ∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => g ∈ A), p A = invE := by
      intro g
      let Sg := Finset.erase (Finset.univ : Finset (Fin n)) g
      have hSg_card : Sg.card = n - 1 := by
        simp [Sg, Finset.card_erase_of_mem (Finset.mem_univ g)]
      have h_bij : ∑ B ∈ Sg.powerset, p (insert g B) =
          ∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => g ∈ A), p A := by
        refine Finset.sum_bij (fun B _ => insert g B) ?_ ?_ ?_ ?_
        · intro B _; simp
        · intro B₁ hB₁ B₂ hB₂ heq
          have hg₁ : g ∉ B₁ := fun hg => (Finset.notMem_erase g _) (Finset.mem_powerset.mp hB₁ hg)
          have hg₂ : g ∉ B₂ := fun hg => (Finset.notMem_erase g _) (Finset.mem_powerset.mp hB₂ hg)
          have := congrArg (fun S => Finset.erase S g) heq
          simpa [Finset.erase_insert hg₁, Finset.erase_insert hg₂] using this
        · intro A hA
          have hgA : g ∈ A := (Finset.mem_filter.mp hA).2
          refine ⟨Finset.erase A g, ?_, Finset.insert_erase hgA⟩
          rw [Finset.mem_powerset]
          intro x hx
          exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, Finset.mem_univ x⟩
        · intro B _; rfl
      rw [← h_bij]
      have h_factor : ∀ B ∈ Sg.powerset,
          p (insert g B) = invE * (invE ^ B.card * (1 - invE) ^ (Sg.card - B.card)) := by
        intro B hB
        have hB_sub : B ⊆ Sg := Finset.mem_powerset.mp hB
        have hgB : g ∉ B := fun hg => (Finset.notMem_erase g _) (hB_sub hg)
        have hB_le : B.card ≤ n - 1 := hSg_card ▸ Finset.card_le_card hB_sub
        have h_ins_c : (insert g B).card = B.card + 1 := Finset.card_insert_of_notMem hgB
        have h_sub_c : n - (B.card + 1) = Sg.card - B.card := by omega
        dsimp [p]
        rw [h_ins_c, h_sub_c, pow_succ]
        ring
      rw [Finset.sum_congr rfl h_factor, ← Finset.mul_sum, h_powerset_sum Sg, mul_one]
    have h_neg : ∑ A : Finset (Fin n), p A * realVal v A < 0 := by
      have h_invE_pos : 0 < invE := Real.exp_pos (-1)
      have h_invE_le_one : invE ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      have hp_nn : ∀ A : Finset (Fin n), 0 ≤ p A := by
        intro A; dsimp [p]
        exact mul_nonneg (pow_nonneg (le_of_lt h_invE_pos) _) (pow_nonneg (by linarith) _)
      have h_ub : ∑ A : Finset (Fin n), p A * realVal v A ≤
          ∑ A : Finset (Fin n), p A * (2 - (A.card : ℝ)) := by
        refine Finset.sum_le_sum (fun A _ => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (hp_nn A)
        rw [h_realVal]
        dsimp [h]
        have hm : (min A.card 1 : ℕ) ≤ 1 := Nat.min_le_right A.card 1
        have hmR : ((min A.card 1 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hm
        linarith
      have h_exp_card : ∑ A : Finset (Fin n), p A * (A.card : ℝ) = (n : ℝ) * invE := by
        calc
          ∑ A : Finset (Fin n), p A * (A.card : ℝ)
            = ∑ A : Finset (Fin n), ∑ g : Fin n, (if g ∈ A then p A else 0) := by
              refine Finset.sum_congr rfl (fun A _ => ?_)
              have hcard : (A.card : ℝ) = ∑ g : Fin n, (if g ∈ A then (1 : ℝ) else 0) := by
                rw [← Finset.sum_filter]
                have hA_filt : (Finset.univ : Finset (Fin n)).filter (fun g => g ∈ A) = A := by
                  ext g; simp
                rw [hA_filt]; simp
              rw [hcard, Finset.mul_sum]
              refine Finset.sum_congr rfl (fun g _ => ?_)
              split_ifs <;> ring
          _ = ∑ g : Fin n, ∑ A : Finset (Fin n), (if g ∈ A then p A else 0) := Finset.sum_comm
          _ = ∑ g : Fin n, ∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => g ∈ A), p A := by
              refine Finset.sum_congr rfl (fun g _ => ?_)
              rw [← Finset.sum_filter]
          _ = ∑ _g : Fin n, invE := Finset.sum_congr rfl (fun g _ => h_marg g)
          _ = (n : ℝ) * invE := by simp
      have h_lin : ∑ A : Finset (Fin n), p A * (2 - (A.card : ℝ)) = 2 - (n : ℝ) * invE := by
        have h_split : ∑ A : Finset (Fin n), p A * (2 - (A.card : ℝ)) =
            2 * (∑ A : Finset (Fin n), p A) - ∑ A : Finset (Fin n), p A * (A.card : ℝ) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun A _ => by ring)
        rw [h_split, h_univ_sum, h_exp_card]
        ring
      have h_e_lt_3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have h_prod : Real.exp 1 * invE = 1 := by
        dsimp [invE]
        rw [← Real.exp_add]
        norm_num
      have h_2_lt_6invE : 2 < 6 * invE := by
        have hmul : 2 * Real.exp 1 * invE < 6 * invE :=
          mul_lt_mul_of_pos_right (by linarith) h_invE_pos
        linarith [show 2 * Real.exp 1 * invE = 2 * (Real.exp 1 * invE) by ring]
      have hn_ge : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have h_6_le_n : 6 * invE ≤ (n : ℝ) * invE :=
        mul_le_mul_of_nonneg_right hn_ge (le_of_lt h_invE_pos)
      linarith
    exact ⟨h_gs, h_opt, h_cd, h_marg g0, h_neg⟩
  have env_spec : ∀ {n : ℕ} (v : ItemValuation n), IsGSValuation v →
      ∀ S : Finset (Fin n),
        ((disposalEnvelope v S : ℝ) : WithBot ℝ) = S.powerset.sup v ∧
        (∀ T ⊆ S, v T ≤ ((disposalEnvelope v S : ℝ) : WithBot ℝ)) ∧
        (∃ X ⊆ S, v X = ((disposalEnvelope v S : ℝ) : WithBot ℝ) ∧ v X ≠ ⊥) := by
    intro n v hv S
    have h0_mem : (∅ : Finset (Fin n)) ∈ S.powerset := Finset.empty_mem_powerset S
    have h0_le : ((0 : ℝ) : WithBot ℝ) ≤ S.powerset.sup v := by
      rw [← hv.1]
      exact Finset.le_sup h0_mem
    have hsup_ne : S.powerset.sup v ≠ ⊥ := by
      intro hbot
      rw [hbot, le_bot_iff] at h0_le
      exact WithBot.coe_ne_bot h0_le
    have h_coe : ((disposalEnvelope v S : ℝ) : WithBot ℝ) = S.powerset.sup v :=
      coe_unbotD hsup_ne
    have h_ub : ∀ T ⊆ S, v T ≤ ((disposalEnvelope v S : ℝ) : WithBot ℝ) := by
      intro T hTS
      rw [h_coe]
      exact Finset.le_sup (Finset.mem_powerset.mpr hTS)
    obtain ⟨X, hX_mem, hX_eq⟩ := Finset.exists_mem_eq_sup S.powerset ⟨∅, h0_mem⟩ v
    have hX_val : v X = ((disposalEnvelope v S : ℝ) : WithBot ℝ) := by
      rw [h_coe, hX_eq]
    have hX_ne : v X ≠ ⊥ := by
      rw [hX_val]
      exact WithBot.coe_ne_bot
    exact ⟨h_coe, h_ub, ⟨X, Finset.mem_powerset.mp hX_mem, hX_val, hX_ne⟩⟩
  have part_5a : ∀ n (v : ItemValuation n), IsGSValuation v →
      disposalEnvelope v ∅ = 0 ∧
      (∀ S, 0 ≤ disposalEnvelope v S) ∧
      (∀ S T : Finset (Fin n), S ⊆ T → disposalEnvelope v S ≤ disposalEnvelope v T) ∧
      IsSubmodularReal (disposalEnvelope v) := by
    intro n v hv
    have h_emp : disposalEnvelope v ∅ = 0 := by
      simp [disposalEnvelope, hv.1]
    have h_nn : ∀ S : Finset (Fin n), 0 ≤ disposalEnvelope v S := by
      intro S
      have h0 := (env_spec v hv S).2.1 ∅ (Finset.empty_subset S)
      rwa [hv.1, WithBot.coe_le_coe] at h0
    have h_mono : ∀ S T : Finset (Fin n), S ⊆ T → disposalEnvelope v S ≤ disposalEnvelope v T := by
      intro S T hST
      have hle : S.powerset.sup v ≤ T.powerset.sup v :=
        Finset.sup_mono (Finset.powerset_mono.mpr hST)
      rwa [← (env_spec v hv S).1, ← (env_spec v hv T).1, WithBot.coe_le_coe] at hle
    refine ⟨h_emp, h_nn, h_mono, ⟨h_emp, ?_⟩⟩
    intro Q R hQR g hgR
    obtain ⟨X, hXQ, hvX, hXne⟩ := (env_spec v hv Q).2.2
    obtain ⟨Y, hYRg, hvY, hYne⟩ := (env_spec v hv (insert g R)).2.2
    by_cases hgY : g ∈ Y
    · have hgX : g ∉ X := fun hg => hgR (hQR (hXQ hg))
      have hg_sdiff : g ∈ Y \ X := Finset.mem_sdiff.mpr ⟨hgY, hgX⟩
      have hex := hv.2 Y X hYne hXne g hg_sdiff
      have hYe_R : Finset.erase Y g ⊆ R := by
        intro z hz
        obtain ⟨hzne, hzY⟩ := Finset.mem_erase.mp hz
        rcases Finset.mem_insert.mp (hYRg hzY) with rfl | hzR
        · exact absurd rfl hzne
        · exact hzR
      have hgX_Qg : insert g X ⊆ insert g Q := Finset.insert_subset_insert g hXQ
      have h_br1 : v (Finset.erase Y g) + v (insert g X) ≤
          ((disposalEnvelope v R + disposalEnvelope v (insert g Q) : ℝ) : WithBot ℝ) := by
        rw [WithBot.coe_add]
        exact add_le_add ((env_spec v hv R).2.1 _ hYe_R) ((env_spec v hv (insert g Q)).2.1 _ hgX_Qg)
      have h_br2 : (X \ Y).sup (fun y => v (insert y (Finset.erase Y g)) + v (Finset.erase (insert g X) y)) ≤
          ((disposalEnvelope v R + disposalEnvelope v (insert g Q) : ℝ) : WithBot ℝ) := by
        refine Finset.sup_le (fun y hy => ?_)
        obtain ⟨hyX, _⟩ := Finset.mem_sdiff.mp hy
        have h1_sub : insert y (Finset.erase Y g) ⊆ R :=
          Finset.insert_subset_iff.mpr ⟨hQR (hXQ hyX), hYe_R⟩
        have h2_sub : Finset.erase (insert g X) y ⊆ insert g Q :=
          (Finset.erase_subset y (insert g X)).trans hgX_Qg
        rw [WithBot.coe_add]
        exact add_le_add ((env_spec v hv R).2.1 _ h1_sub) ((env_spec v hv (insert g Q)).2.1 _ h2_sub)
      have h_comb : v Y + v X ≤
          ((disposalEnvelope v R + disposalEnvelope v (insert g Q) : ℝ) : WithBot ℝ) :=
        hex.trans (max_le h_br1 h_br2)
      rw [hvY, hvX, ← WithBot.coe_add, WithBot.coe_le_coe] at h_comb
      linarith
    · have hYR : Y ⊆ R := by
        intro z hz
        rcases Finset.mem_insert.mp (hYRg hz) with rfl | hzR
        · exact absurd hz hgY
        · exact hzR
      have h1 : disposalEnvelope v (insert g R) ≤ disposalEnvelope v R := by
        have hle := (env_spec v hv R).2.1 Y hYR
        rwa [hvY, WithBot.coe_le_coe] at hle
      have h2 : disposalEnvelope v Q ≤ disposalEnvelope v (insert g Q) :=
        h_mono Q (insert g Q) (Finset.subset_insert g Q)
      linarith
  have part_5b : ∀ n m (v : Fin m → ItemValuation n), (∀ i, IsGSValuation (v i)) →
      optWelfare (fun i S => ((disposalEnvelope (v i) S : ℝ) : WithBot ℝ)) = optWelfare v := by
    intro n m v hv
    let w : Fin m → ItemValuation n := fun i S => ((disposalEnvelope (v i) S : ℝ) : WithBot ℝ)
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
      have hY_alloc : IsAllocOf Finset.univ Y := by
        refine ⟨fun i => Finset.subset_univ _, fun i j hij => ?_⟩
        exact Disjoint.mono (hY_sub i) (hY_sub j) (hX_alloc.2 i j hij)
      have hY_mem : Y ∈ Aset := Finset.mem_filter.mpr ⟨Finset.mem_univ Y, hY_alloc⟩
      have h_eq_w : allocWelfare w X = allocWelfare v Y := by
        dsimp [allocWelfare]
        exact Finset.sum_congr rfl (fun i _ => (hY_val i).symm)
      rw [h_eq_w]
      exact Finset.le_sup hY_mem
    · refine Finset.sup_le (fun X hX => ?_)
      have h_le : allocWelfare v X ≤ allocWelfare w X := by
        dsimp [allocWelfare]
        refine Finset.sum_le_sum (fun i _ => ?_)
        exact (env_spec (v i) (hv i) (X i)).2.1 (X i) Finset.Subset.rfl
      exact h_le.trans (Finset.le_sup hX)
  have part_6 : ∀ n m (v : Fin m → ItemValuation n) (p : Finset (Fin n) → ℝ) (lam : ℝ),
      (∀ i, IsGSValuation (v i)) →
      (∀ R, 0 ≤ p R) → (∑ R : Finset (Fin n), p R) = 1 →
      (∀ g : Fin n,
        (∑ R ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun R => g ∈ R), p R) = lam) →
        lam * optWelfare v ≤ ∑ R : Finset (Fin n), p R * optWelfareOn v R := by
    intro n m v p lam hv hp0 _ hlam
    have h_welf_spec : ∀ S : Finset (Fin n),
        let A_S := (Finset.univ : Finset (Fin m → Finset (Fin n))).filter (fun X => IsAllocOf S X)
        A_S.Nonempty ∧ ((optWelfareOn v S : ℝ) : WithBot ℝ) = A_S.sup (allocWelfare v) := by
      intro S
      let A_S := (Finset.univ : Finset (Fin m → Finset (Fin n))).filter (fun X => IsAllocOf S X)
      let X0 : Fin m → Finset (Fin n) := fun _ => ∅
      have hX0_alloc : IsAllocOf S X0 :=
        ⟨fun _ => Finset.empty_subset S, fun _ _ _ => Finset.disjoint_empty_left ∅⟩
      have hX0_mem : X0 ∈ A_S := Finset.mem_filter.mpr ⟨Finset.mem_univ X0, hX0_alloc⟩
      have hX0_val : allocWelfare v X0 = ((0 : ℝ) : WithBot ℝ) := by
        dsimp [allocWelfare, X0]
        have h_each : ∀ i : Fin m, v i ∅ = ((0 : ℝ) : WithBot ℝ) := fun i => (hv i).1
        rw [Finset.sum_congr rfl (fun i _ => h_each i)]
        simp [WithBot.coe_zero]
      have h0_le : ((0 : ℝ) : WithBot ℝ) ≤ A_S.sup (allocWelfare v) := by
        rw [← hX0_val]
        exact Finset.le_sup hX0_mem
      have hsup_ne : A_S.sup (allocWelfare v) ≠ ⊥ := by
        intro hbot
        rw [hbot, le_bot_iff] at h0_le
        exact WithBot.coe_ne_bot h0_le
      exact ⟨⟨X0, hX0_mem⟩, coe_unbotD hsup_ne⟩
    let A_univ := (Finset.univ : Finset (Fin m → Finset (Fin n))).filter (fun X => IsAllocOf Finset.univ X)
    obtain ⟨Xstar, hXstar_mem, hXstar_sup⟩ :=
      Finset.exists_mem_eq_sup A_univ (h_welf_spec Finset.univ).1 (allocWelfare v)
    have hXstar_alloc : IsAllocOf Finset.univ Xstar := (Finset.mem_filter.mp hXstar_mem).2
    have hXstar_val : allocWelfare v Xstar = ((optWelfare v : ℝ) : WithBot ℝ) := by
      dsimp [optWelfare]
      rw [(h_welf_spec Finset.univ).2, hXstar_sup]
    have hXi_ne : ∀ i : Fin m, v i (Xstar i) ≠ ⊥ := by
      intro i hbot
      have h_all_bot : allocWelfare v Xstar = ⊥ := by
        dsimp [allocWelfare]
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i), hbot, WithBot.bot_add]
      rw [hXstar_val] at h_all_bot
      exact WithBot.coe_ne_bot h_all_bot
    have h_opt_sum : optWelfare v = ∑ i : Fin m, realVal (v i) (Xstar i) := by
      have h_coe_eq : ((optWelfare v : ℝ) : WithBot ℝ) =
          ((∑ i : Fin m, realVal (v i) (Xstar i) : ℝ) : WithBot ℝ) := by
        rw [← hXstar_val, WithBot.coe_sum]
        dsimp [allocWelfare]
        exact Finset.sum_congr rfl (fun i _ => (coe_realVal (v i) (Xstar i) (hXi_ne i)).symm)
      exact le_antisymm (WithBot.coe_le_coe.mp (le_of_eq h_coe_eq))
        (WithBot.coe_le_coe.mp (le_of_eq h_coe_eq.symm))
    have hXi_max : ∀ (i : Fin m) (Y : Finset (Fin n)), Y ⊆ Xstar i → v i Y ≤ v i (Xstar i) := by
      intro i Y hYX
      have hY_ne : v i Y ≠ ⊥ := dom_hereditary (hv i) hYX (hXi_ne i)
      let X' : Fin m → Finset (Fin n) := Function.update Xstar i Y
      have hX'_sub : ∀ j : Fin m, X' j ⊆ Xstar j := by
        intro j
        by_cases hj : j = i
        · subst hj; simpa [X'] using hYX
        · simp [X', hj]
      have hX'_alloc : IsAllocOf Finset.univ X' :=
        ⟨fun _ => Finset.subset_univ _,
         fun j1 j2 hne => Disjoint.mono (hX'_sub j1) (hX'_sub j2) (hXstar_alloc.2 j1 j2 hne)⟩
      have hX'_mem : X' ∈ A_univ := Finset.mem_filter.mpr ⟨Finset.mem_univ X', hX'_alloc⟩
      have h_welf_le : allocWelfare v X' ≤ allocWelfare v Xstar := by
        rw [← hXstar_sup]
        exact Finset.le_sup hX'_mem
      have hX'_ne : ∀ j : Fin m, v j (X' j) ≠ ⊥ :=
        fun j => dom_hereditary (hv j) (hX'_sub j) (hXi_ne j)
      have h_lhs : allocWelfare v X' = ((∑ j : Fin m, realVal (v j) (X' j) : ℝ) : WithBot ℝ) := by
        rw [WithBot.coe_sum]; dsimp [allocWelfare]
        exact Finset.sum_congr rfl (fun j _ => (coe_realVal (v j) (X' j) (hX'_ne j)).symm)
      have h_rhs : allocWelfare v Xstar = ((∑ j : Fin m, realVal (v j) (Xstar j) : ℝ) : WithBot ℝ) := by
        rw [WithBot.coe_sum]; dsimp [allocWelfare]
        exact Finset.sum_congr rfl (fun j _ => (coe_realVal (v j) (Xstar j) (hXi_ne j)).symm)
      rw [h_lhs, h_rhs, WithBot.coe_le_coe] at h_welf_le
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)] at h_welf_le
      have h_rhs_split : ∑ j : Fin m, realVal (v j) (Xstar j) =
          realVal (v i) (Xstar i) + ∑ j ∈ Finset.erase Finset.univ i, realVal (v j) (Xstar j) :=
        (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)).symm
      rw [h_rhs_split] at h_welf_le
      have h_erase_eq : ∑ j ∈ Finset.erase Finset.univ i, realVal (v j) (X' j) =
          ∑ j ∈ Finset.erase Finset.univ i, realVal (v j) (Xstar j) := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have hjne : j ≠ i := (Finset.mem_erase.mp hj).1
        simp [X', hjne]
      have h_at_i : realVal (v i) (X' i) = realVal (v i) Y := by simp [X']
      rw [h_at_i, h_erase_eq] at h_welf_le
      rw [← coe_realVal (v i) Y hY_ne, ← coe_realVal (v i) (Xstar i) (hXi_ne i), WithBot.coe_le_coe]
      linarith
    have h_ex_a : ∀ i : Fin m, ∃ a : Fin n → ℝ,
        (∀ g ∈ Xstar i, 0 ≤ a g) ∧
        (∑ g ∈ Xstar i, a g) = realVal (v i) (Xstar i) ∧
        (∀ Y ⊆ Xstar i, ((∑ g ∈ Y, a g : ℝ) : WithBot ℝ) ≤ v i Y) :=
      fun i => part_2 n (v i) (Xstar i) (hv i) (hXi_ne i) (hXi_max i)
    let a : Fin m → Fin n → ℝ := fun i => Classical.choose (h_ex_a i)
    have ha_sum : ∀ i : Fin m, (∑ g ∈ Xstar i, a i g) = realVal (v i) (Xstar i) :=
      fun i => (Classical.choose_spec (h_ex_a i)).2.1
    have ha_low : ∀ (i : Fin m) (Y : Finset (Fin n)),
        Y ⊆ Xstar i → ((∑ g ∈ Y, a i g : ℝ) : WithBot ℝ) ≤ v i Y :=
      fun i => (Classical.choose_spec (h_ex_a i)).2.2
    have h_R_bound : ∀ R : Finset (Fin n),
        ∑ i : Fin m, ∑ g ∈ (Xstar i).filter (fun g => g ∈ R), a i g ≤ optWelfareOn v R := by
      intro R
      let XR : Fin m → Finset (Fin n) := fun i => (Xstar i).filter (fun g => g ∈ R)
      have hXR_R : ∀ i : Fin m, XR i ⊆ R := fun i g hg => (Finset.mem_filter.mp hg).2
      have hXR_X : ∀ i : Fin m, XR i ⊆ Xstar i := fun i => Finset.filter_subset _ (Xstar i)
      have hXR_alloc : IsAllocOf R XR :=
        ⟨hXR_R, fun i j hij => Disjoint.mono (hXR_X i) (hXR_X j) (hXstar_alloc.2 i j hij)⟩
      let A_R := (Finset.univ : Finset (Fin m → Finset (Fin n))).filter (fun X => IsAllocOf R X)
      have hXR_mem : XR ∈ A_R := Finset.mem_filter.mpr ⟨Finset.mem_univ XR, hXR_alloc⟩
      have h_coe_le : ((∑ i : Fin m, ∑ g ∈ XR i, a i g : ℝ) : WithBot ℝ) ≤
          ((optWelfareOn v R : ℝ) : WithBot ℝ) := by
        rw [WithBot.coe_sum, (h_welf_spec R).2]
        refine le_trans ?_ (Finset.le_sup hXR_mem)
        dsimp [allocWelfare]
        exact Finset.sum_le_sum (fun i _ => ha_low i (XR i) (hXR_X i))
      exact WithBot.coe_le_coe.mp h_coe_le
    have h_weighted : ∑ R : Finset (Fin n),
          p R * (∑ i : Fin m, ∑ g ∈ (Xstar i).filter (fun g => g ∈ R), a i g) ≤
        ∑ R : Finset (Fin n), p R * optWelfareOn v R :=
      Finset.sum_le_sum (fun R _ => mul_le_mul_of_nonneg_left (h_R_bound R) (hp0 R))
    have h_lhs_eval : ∑ R : Finset (Fin n),
          p R * (∑ i : Fin m, ∑ g ∈ (Xstar i).filter (fun g => g ∈ R), a i g) =
        lam * optWelfare v := by
      calc
        ∑ R : Finset (Fin n), p R * (∑ i : Fin m, ∑ g ∈ (Xstar i).filter (fun g => g ∈ R), a i g)
          = ∑ R : Finset (Fin n), ∑ i : Fin m, ∑ g ∈ Xstar i, (if g ∈ R then p R * a i g else 0) := by
            refine Finset.sum_congr rfl (fun R _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.sum_filter, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun g _ => ?_)
            split_ifs <;> ring
        _ = ∑ i : Fin m, ∑ R : Finset (Fin n), ∑ g ∈ Xstar i, (if g ∈ R then p R * a i g else 0) :=
            Finset.sum_comm
        _ = ∑ i : Fin m, ∑ g ∈ Xstar i, ∑ R : Finset (Fin n), (if g ∈ R then p R * a i g else 0) := by
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
        _ = ∑ i : Fin m, ∑ g ∈ Xstar i,
              (∑ R ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun R => g ∈ R), p R) * a i g := by
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun g _ => ?_))
            rw [← Finset.sum_filter, Finset.sum_mul]
        _ = ∑ i : Fin m, ∑ g ∈ Xstar i, lam * a i g := by
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun g _ => ?_))
            rw [hlam g]
        _ = lam * optWelfare v := by
            rw [h_opt_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [← Finset.mul_sum, ha_sum i]
    linarith
  have part_7 : ∀ n : ℕ, 2 ≤ n → ∃ s ∈ Finset.Ico 1 n, invE ≤ secretaryCutoffConst n s := by
    intro n hn2
    have h_invE_pos : 0 < invE := Real.exp_pos (-1)
    have h_exp_prod : Real.exp 1 * invE = 1 := by
      dsimp [invE]; rw [← Real.exp_add]; norm_num
    rcases eq_or_lt_of_le hn2 with rfl | hn3
    · refine ⟨1, by simp, ?_⟩
      have h_c21 : secretaryCutoffConst 2 1 = 1 / 2 := by
        dsimp [secretaryCutoffConst]
        rw [Nat.Ico_succ_singleton]
        norm_num
      rw [h_c21]
      have h2_le_e : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp 1
        linarith
      have hmul : 2 * invE ≤ Real.exp 1 * invE :=
        mul_le_mul_of_nonneg_right h2_le_e (le_of_lt h_invE_pos)
      linarith
    · have hn3' : 3 ≤ n := hn3
      have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
      let ζ : ℝ := (n : ℝ) * invE
      have hζ_pos : 0 < ζ := mul_pos hn_pos h_invE_pos
      let s0 : ℕ := ⌊ζ⌋₊
      have h_one_lt_ζ : 1 < ζ := by
        have he_lt_n : Real.exp 1 < (n : ℝ) := by
          have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3'
          linarith [Real.exp_one_lt_d9]
        have hmul : Real.exp 1 * invE < (n : ℝ) * invE :=
          mul_lt_mul_of_pos_right he_lt_n h_invE_pos
        dsimp [ζ]
        linarith
      have hs0_ge_1 : 1 ≤ s0 := Nat.le_floor (by exact_mod_cast le_of_lt h_one_lt_ζ)
      have hs0_lt_nm1 : s0 < n - 1 := by
        have h2_lt_e : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
        have h2invE : 2 * invE < 1 := by
          have hmul : 2 * invE < Real.exp 1 * invE :=
            mul_lt_mul_of_pos_right h2_lt_e h_invE_pos
          linarith
        have h2ζ : 2 * ζ < (n : ℝ) := by
          dsimp [ζ]
          have hmul : (n : ℝ) * (2 * invE) < (n : ℝ) * 1 :=
            mul_lt_mul_of_pos_left h2invE hn_pos
          linarith
        have hn_le : n ≤ 2 * (n - 1) := by omega
        have hn_leR : (n : ℝ) ≤ 2 * ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hn_le
        have hζ_lt : ζ < ((n - 1 : ℕ) : ℝ) := by linarith
        exact (Nat.floor_lt (le_of_lt hζ_pos)).mpr hζ_lt
      have hs0_lt_n : s0 < n := by omega
      have hs01_lt_n : s0 + 1 < n := by omega
      have hs0_mem : s0 ∈ Finset.Ico 1 n := Finset.mem_Ico.mpr ⟨hs0_ge_1, hs0_lt_n⟩
      have hs01_mem : s0 + 1 ∈ Finset.Ico 1 n := Finset.mem_Ico.mpr ⟨by omega, hs01_lt_n⟩
      let η : ℝ := ζ - (s0 : ℝ)
      have hη_nn : 0 ≤ η := by
        dsimp [η, s0]
        linarith [Nat.floor_le (le_of_lt hζ_pos)]
      have h1mη_pos : 0 < 1 - η := by
        dsimp [η, s0]
        linarith [Nat.lt_floor_add_one ζ]
      let H : ℝ := ∑ j ∈ Finset.Ico (s0 + 1) n, (1 / (j : ℝ))
      have h_split_sum : ∑ j ∈ Finset.Ico s0 n, (1 / (j : ℝ)) = 1 / (s0 : ℝ) + H :=
        Finset.sum_eq_sum_Ico_succ_bot hs0_lt_n (fun j => 1 / (j : ℝ))
      have hs0_posR : (0 : ℝ) < (s0 : ℝ) := by exact_mod_cast (show 0 < s0 by omega)
      have h_conv_id : (1 - η) * secretaryCutoffConst n s0 + η * secretaryCutoffConst n (s0 + 1) =
          ((s0 : ℝ) + 1 - ζ) / (n : ℝ) + (ζ / (n : ℝ)) * H := by
        dsimp [secretaryCutoffConst, η]
        rw [h_split_sum]
        change (1 - (ζ - (s0 : ℝ))) * (((s0 : ℝ) / (n : ℝ)) * (1 / (s0 : ℝ) + H)) +
            (ζ - (s0 : ℝ)) * ((((s0 + 1 : ℕ) : ℝ) / (n : ℝ)) * H) =
            ((s0 : ℝ) + 1 - ζ) / (n : ℝ) + (ζ / (n : ℝ)) * H
        rw [Nat.cast_add, Nat.cast_one]
        have hs0_ne : (s0 : ℝ) ≠ 0 := ne_of_gt hs0_posR
        have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
        field_simp
        ring
      have h_H_lb : Real.log (n : ℝ) - Real.log ((s0 : ℝ) + 1) ≤ H := by
        have h_term : ∀ j ∈ Finset.Ico (s0 + 1) n,
            Real.log (((j + 1 : ℕ) : ℝ)) - Real.log (j : ℝ) ≤ 1 / (j : ℝ) := by
          intro j hj
          have hj_ge : s0 + 1 ≤ j := (Finset.mem_Ico.mp hj).1
          have hj_pos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
          have hj1_pos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < j + 1 by omega)
          have h_div_pos : 0 < ((j + 1 : ℕ) : ℝ) / (j : ℝ) := div_pos hj1_pos hj_pos
          have hlog := Real.log_le_sub_one_of_pos h_div_pos
          rw [Real.log_div (ne_of_gt hj1_pos) (ne_of_gt hj_pos)] at hlog
          have h_alg : ((j + 1 : ℕ) : ℝ) / (j : ℝ) - 1 = 1 / (j : ℝ) := by
            rw [Nat.cast_add, Nat.cast_one]
            have hj_ne : (j : ℝ) ≠ 0 := ne_of_gt hj_pos
            field_simp
            ring
          linarith
        have h_sum := Finset.sum_le_sum h_term
        let f : ℕ → ℝ := fun k => Real.log (k : ℝ)
        have h_tele : ∑ j ∈ Finset.Ico (s0 + 1) n, (f (j + 1) - f j) = f n - f (s0 + 1) := by
          rw [Finset.sum_Ico_eq_sub (fun j => f (j + 1) - f j) (le_of_lt hs01_lt_n),
              Finset.sum_range_sub f n, Finset.sum_range_sub f (s0 + 1)]
          ring
        dsimp [f] at h_tele
        rw [Nat.cast_add, Nat.cast_one] at h_tele
        dsimp [H]
        linarith
      have h_frac_lb : invE * (Real.log ((s0 : ℝ) + 1) - Real.log ζ) ≤ ((s0 : ℝ) + 1 - ζ) / (n : ℝ) := by
        have hs01_pos : 0 < (s0 : ℝ) + 1 := by linarith
        have hlog := Real.log_le_sub_one_of_pos (div_pos hs01_pos hζ_pos)
        rw [Real.log_div (ne_of_gt hs01_pos) (ne_of_gt hζ_pos)] at hlog
        have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt h_invE_pos)
        have h_rhs_eq : invE * (((s0 : ℝ) + 1) / ζ - 1) = ((s0 : ℝ) + 1 - ζ) / (n : ℝ) := by
          dsimp [ζ]
          have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
          have hinv_ne : invE ≠ 0 := ne_of_gt h_invE_pos
          field_simp
        linarith
      have h_ζ_div_n : ζ / (n : ℝ) = invE := by
        dsimp [ζ]
        exact mul_div_cancel_left₀ invE (ne_of_gt hn_pos)
      have h_log_ζ : Real.log ζ = Real.log (n : ℝ) - 1 := by
        dsimp [ζ, invE]
        rw [Real.log_mul (ne_of_gt hn_pos) (ne_of_gt (Real.exp_pos (-1))), Real.log_exp]
        ring
      have h_comb_lb : invE ≤
          (1 - η) * secretaryCutoffConst n s0 + η * secretaryCutoffConst n (s0 + 1) := by
        have hH_scaled := mul_le_mul_of_nonneg_left h_H_lb (le_of_lt h_invE_pos)
        rw [h_conv_id, h_ζ_div_n]
        have h_cancel : invE * (Real.log ((s0 : ℝ) + 1) - Real.log ζ) +
            invE * (Real.log (n : ℝ) - Real.log ((s0 : ℝ) + 1)) = invE := by
          rw [h_log_ζ]; ring
        linarith
      by_contra h_none
      push_neg at h_none
      have hc0 : secretaryCutoffConst n s0 < invE := h_none s0 hs0_mem
      have hc1 : secretaryCutoffConst n (s0 + 1) < invE := h_none (s0 + 1) hs01_mem
      have hlt0 : (1 - η) * secretaryCutoffConst n s0 < (1 - η) * invE :=
        mul_lt_mul_of_pos_left hc0 h1mη_pos
      have hle1 : η * secretaryCutoffConst n (s0 + 1) ≤ η * invE :=
        mul_le_mul_of_nonneg_left (le_of_lt hc1) hη_nn
      linarith
  exact ⟨part_1a, part_1b, part_2, part_3, part_4, part_5a, part_5b, part_6, part_7⟩

end


noncomputable section

/-- **Lemma 2.10(a) (`lem:safe`a, Submodularity on `dom v`)**:
For any GS valuation `v`, if `Q ⊆ R`, `g ∉ R`, and `R + g ∈ dom v`, then `v(g | R) ≤ v(g | Q)`. -/
theorem lem_2_10_safe_a {n : ℕ} (v : ItemValuation n) (Q R : Finset (Fin n)) (g : Fin n)
    (hv : IsGSValuation v) (hQR : Q ⊆ R) (hgR : g ∉ R) (hdom : v (insert g R) ≠ ⊥) :
    marginalVal v R g ≤ marginalVal v Q g :=
  thm_gs_safe_support_envelopes_cutoff.1 n v Q R g hv hQR hgR hdom

/-- **Lemma 2.10(b) (`lem:safe`b, Safe region inside canonical demands)**:
For any GS valuation `v` and `T ⊆ N`, with `X = D_v(T)`, every `Y ⊆ X` lies in `dom v` with
`v(Y) ≥ 0`, and `v` is nondecreasing on `2^X`. -/
theorem lem_2_10_safe_b {n : ℕ} (v : ItemValuation n) (T : Finset (Fin n))
    (hv : IsGSValuation v) :
    let X := canonicalDemand v T
    (∀ Y ⊆ X, v Y ≠ ⊥ ∧ 0 ≤ realVal v Y) ∧
    (∀ Y Z : Finset (Fin n), Y ⊆ Z → Z ⊆ X → v Y ≤ v Z) :=
  thm_gs_safe_support_envelopes_cutoff.2.1 n v T hv

/-- **Lemma 2.10 (`lem:safe`, Combined safe region lemma)**. -/
theorem lem_2_10_safe {n : ℕ} (v : ItemValuation n) (hv : IsGSValuation v) :
    (∀ (Q R : Finset (Fin n)) (g : Fin n),
      Q ⊆ R → g ∉ R → v (insert g R) ≠ ⊥ → marginalVal v R g ≤ marginalVal v Q g) ∧
    (∀ T : Finset (Fin n),
      let X := canonicalDemand v T
      (∀ Y ⊆ X, v Y ≠ ⊥ ∧ 0 ≤ realVal v Y) ∧
      (∀ Y Z : Finset (Fin n), Y ⊆ Z → Z ⊆ X → v Y ≤ v Z)) :=
  ⟨fun Q R g => lem_2_10_safe_a v Q R g hv, fun T => lem_2_10_safe_b v T hv⟩

/-- **Section 2.3 Remark (`[GS99]`, Finite-valued GS valuations are submodular)**:
Every finite-valued GS valuation `v` (`dom v = 2^N`) is submodular on `2^N`. -/
theorem rem_2_10_finite_gs_submodular {n : ℕ} (v : ItemValuation n)
    (hv : IsGSValuation v) (hfin : IsFiniteValuation v) :
    IsSubmodularReal (realVal v) := by
  refine ⟨by simp [realVal, hv.1], ?_⟩
  intro Q R hQR g hgR
  exact lem_2_10_safe_a v Q R g hv hQR hgR (hfin (insert g R))

/-- **Lemma 2.11 (`lem:support`, Additive lower support)**:
If `v` is GS and `X ∈ dom v` satisfies `v(X) ≥ v(Y)` for all `Y ⊆ X`, then there exist nonnegative
weights `a_g ≥ 0` (`g ∈ X`) summing to `v(X)` such that `v(Y) ≥ ∑_{g ∈ Y} a_g` for all `Y ⊆ X`. -/
theorem lem_2_11_support {n : ℕ} (v : ItemValuation n) (X : Finset (Fin n))
    (hv : IsGSValuation v) (hXdom : v X ≠ ⊥) (hXmax : ∀ Y ⊆ X, v Y ≤ v X) :
    ∃ a : Fin n → ℝ,
      (∀ g ∈ X, 0 ≤ a g) ∧
      (∑ g ∈ X, a g) = realVal v X ∧
      (∀ Y ⊆ X, ((∑ g ∈ Y, a g : ℝ) : WithBot ℝ) ≤ v Y) :=
  thm_gs_safe_support_envelopes_cutoff.2.2.1 n v X hv hXdom hXmax

/-- **Corollary 2.12 (`cor:value`, From inclusion to value)**:
If `v` is GS, `X ∈ dom v` maximizes `v` over `2^X`, `A ~ p` almost surely lies in a canonical
demand `D_v(T)`, and `P[g ∈ A] ≥ ρ` for every `g ∈ X`, then `A ∈ dom v` almost surely and
`E[v(A)] ≥ ρ · v(X)`. -/
theorem cor_2_12_value {n : ℕ} (v : ItemValuation n) (X : Finset (Fin n))
    (p : Finset (Fin n) → ℝ) (ρ : ℝ)
    (hv : IsGSValuation v) (hXdom : v X ≠ ⊥) (hXmax : ∀ Y ⊆ X, v Y ≤ v X)
    (hp_nonneg : ∀ A, 0 ≤ p A) (hp_sum : (∑ A : Finset (Fin n), p A) = 1)
    (hp_safe : ∀ A, 0 < p A → ∃ T : Finset (Fin n), A ⊆ canonicalDemand v T)
    (hp_incl : ∀ g ∈ X,
      ρ ≤ ∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => g ∈ A), p A) :
    (∀ A, 0 < p A → v A ≠ ⊥) ∧
    ρ * realVal v X ≤ ∑ A : Finset (Fin n), p A * realVal v A :=
  thm_gs_safe_support_envelopes_cutoff.2.2.2.1 n v X p ρ
    hv hXdom hXmax hp_nonneg hp_sum hp_safe hp_incl

/-- **Section 2.3 Remark after Corollary 2.12**:
When `A ⊆ X` almost surely, the hypothesis `A ⊆ D_v(T)` can be dropped in Corollary 2.12. -/
theorem cor_2_12_value_subset {n : ℕ} (v : ItemValuation n) (X : Finset (Fin n))
    (p : Finset (Fin n) → ℝ) (ρ : ℝ)
    (hv : IsGSValuation v) (hXdom : v X ≠ ⊥) (hXmax : ∀ Y ⊆ X, v Y ≤ v X)
    (hp_nonneg : ∀ A, 0 ≤ p A)
    (hp_sub : ∀ A, 0 < p A → A ⊆ X)
    (hp_incl : ∀ g ∈ X,
      ρ ≤ ∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => g ∈ A), p A) :
    (∀ A, 0 < p A → v A ≠ ⊥) ∧
    ρ * realVal v X ≤ ∑ A : Finset (Fin n), p A * realVal v A := by
  obtain ⟨a, ha_nn, ha_sum, ha_low⟩ := lem_2_11_support v X hv hXdom hXmax
  have hdomA : ∀ A, 0 < p A → v A ≠ ⊥ := by
    intro A hA hbot
    have hlow := ha_low A (hp_sub A hA)
    rw [hbot, le_bot_iff] at hlow
    exact WithBot.coe_ne_bot hlow
  refine ⟨hdomA, ?_⟩
  have hpt : ∀ A : Finset (Fin n), p A * (∑ g ∈ A ∩ X, a g) ≤ p A * realVal v A := by
    intro A
    rcases eq_or_lt_of_le (hp_nonneg A) with hp0 | hp_pos
    · rw [← hp0]; simp
    · have hAX : A ∩ X = A := Finset.inter_eq_left.mpr (hp_sub A hp_pos)
      rw [hAX]
      have hlow := ha_low A (hp_sub A hp_pos)
      obtain ⟨r, hr⟩ := WithBot.ne_bot_iff_exists.mp (hdomA A hp_pos)
      rw [← hr, WithBot.coe_le_coe] at hlow
      unfold realVal
      rw [← hr, WithBot.unbotD_coe]
      exact mul_le_mul_of_nonneg_left hlow (le_of_lt hp_pos)
  have h_swap :
      (∑ g ∈ X, (∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => g ∈ A), p A) * a g) =
      ∑ A : Finset (Fin n), p A * (∑ g ∈ A ∩ X, a g) := by
    calc
      (∑ g ∈ X, (∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => g ∈ A), p A) * a g)
          = ∑ g ∈ X, ∑ A : Finset (Fin n), (if g ∈ A then p A * a g else 0) := by
            refine Finset.sum_congr rfl (fun g _ => ?_)
            rw [Finset.sum_mul, Finset.sum_filter]
      _ = ∑ A : Finset (Fin n), ∑ g ∈ X, (if g ∈ A then p A * a g else 0) := Finset.sum_comm
      _ = ∑ A : Finset (Fin n), p A * (∑ g ∈ A ∩ X, a g) := by
            refine Finset.sum_congr rfl (fun A _ => ?_)
            rw [Finset.mul_sum, ← Finset.sum_filter]
            refine Finset.sum_congr ?_ (fun _ _ => rfl)
            ext g
            simp [Finset.mem_inter, and_comm]
  calc
    ρ * realVal v X = ρ * (∑ g ∈ X, a g) := by rw [ha_sum]
    _ = ∑ g ∈ X, ρ * a g := by rw [Finset.mul_sum]
    _ ≤ ∑ g ∈ X, (∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => g ∈ A), p A) * a g :=
        Finset.sum_le_sum (fun g hg => mul_le_mul_of_nonneg_right (hp_incl g hg) (ha_nn g hg))
    _ = ∑ A : Finset (Fin n), p A * (∑ g ∈ A ∩ X, a g) := h_swap
    _ ≤ ∑ A : Finset (Fin n), p A * realVal v A :=
        Finset.sum_le_sum (fun A _ => hpt A)

/-- **Example 2.13 (`ex:sampling`, Random samples can destroy value)**:
For `n ≥ 6` and `v(S) = 2 min{|S|, 1} - |S|`, `v` is GS with `OPT(v) = 1` and `D_v(N) = {0}`,
and independent `1/e`-sampling includes item `0` with probability `1/e` yet has `E[v(A)] < 0`. -/
theorem ex_2_13_sampling (n : ℕ) (hn : 6 ≤ n) :
    let v : ItemValuation n :=
      fun S => (((2 * (min S.card 1 : ℕ) : ℝ) - (S.card : ℝ) : ℝ) : WithBot ℝ)
    let p : Finset (Fin n) → ℝ :=
      fun A => invE ^ A.card * (1 - invE) ^ (n - A.card)
    let g0 : Fin n := ⟨0, by omega⟩
    IsGSValuation v ∧
    optVal v = 1 ∧
    canonicalDemand v Finset.univ = {g0} ∧
    (∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => g0 ∈ A), p A) = invE ∧
    (∑ A : Finset (Fin n), p A * realVal v A) < 0 :=
  thm_gs_safe_support_envelopes_cutoff.2.2.2.2.1 n hn

/-- **Lemma 4.3 (`lem:prefix`, Random subsets)**:
If `v_1, ..., v_m` are GS valuations and `R ~ p` contains each item `g ∈ N` with marginal
probability `λ`, then `E[W(R)] ≥ λ · OPT`. -/
theorem lem_4_3_prefix {n m : ℕ} (v : Fin m → ItemValuation n)
    (p : Finset (Fin n) → ℝ) (lam : ℝ)
    (hv : ∀ i, IsGSValuation (v i))
    (hp_nonneg : ∀ R, 0 ≤ p R) (hp_sum : (∑ R : Finset (Fin n), p R) = 1)
    (hp_marg : ∀ g : Fin n,
      (∑ R ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun R => g ∈ R), p R) = lam) :
    lam * optWelfare v ≤ ∑ R : Finset (Fin n), p R * optWelfareOn v R :=
  thm_gs_safe_support_envelopes_cutoff.2.2.2.2.2.2.2.1 n m v p lam hv hp_nonneg hp_sum hp_marg

/-- **Lemma D.1 (`lem:cutoff`, Cutoffs)**:
For every `n ≥ 2`, there exists `s ∈ {1, ..., n - 1}` with `c_n(s) ≥ 1 / e`. -/
theorem lem_D_1_cutoff (n : ℕ) (hn : 2 ≤ n) :
    ∃ s ∈ Finset.Ico 1 n, invE ≤ secretaryCutoffConst n s :=
  thm_gs_safe_support_envelopes_cutoff.2.2.2.2.2.2.2.2 n hn

end

end GrossSubstitutesWelfare
