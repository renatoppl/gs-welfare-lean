import GrossSubstitutesWelfare.Defs
import GrossSubstitutesWelfare.Preliminaries.ExchangeAndDemand

set_option maxHeartbeats 4000000

/-!
# Section 3.2 & Appendix B.1 (Part 1): Two-Time Survival Law, Clamp, Local Move & Cost-and-Repayment

This file formalizes Section 3.2 (`sec:survival`) and Appendix B.1 Lemmas B.2 (`lem:clamp`),
B.3 (`lem:local-move`), and B.4 (`lem:payment`) of *Gross Substitutes Welfare in Random Order*.
-/

namespace GrossSubstitutesWelfare

open Classical MeasureTheory

noncomputable section

namespace Internal

theorem thm_selection_clamp_local_move_and_payment :
    -- (1) Thought experiment probability, support, t = 1/e base, and single-item retention
    (∀ (n : ℕ) (C : Finset (Fin n) → Finset (Fin n)) (t₀ t : ℝ)
        (S B : Finset (Fin n)) (β : Fin n → ℝ),
      IsChoiceRule C → HasPersistence C → invE ≤ t₀ → t₀ ≤ t → t ≤ 1 →
        (∀ τ A, 0 ≤ retainProd C t S B τ β A ∧ retainProd C t S B τ β A ≤ 1) ∧
        (∀ τ, (∑ A ∈ S.powerset, retainProd C t S B τ β A) = 1) ∧
        (∀ τ A, 0 < retainProd C t S B τ β A → A ⊆ C (presentSet S B τ β invE) ∩ S) ∧
        (∀ A, genSurvivalLaw2 C invE invE S B β A = (if A = ∅ then 1 else 0)) ∧
        (∀ g ∈ C S,
          (∑ A ∈ S.powerset.filter (fun A => g ∈ A), genSurvivalLaw C t S ∅ β A) =
            Real.log (Real.exp 1 * t) / (Real.exp 1 * t))) ∧
    -- (2) Lemma B.2 (lem:clamp): Clamp identity, displacement interval, disjointness & Lipschitzness
    (∀ (n : ℕ) (C : Finset (Fin n) → Finset (Fin n)) (t : ℝ)
        (S B : Finset (Fin n)) (x : Fin n) (A : Finset (Fin n)) (τ β : Fin n → ℝ),
      IsChoiceRule C → HasPersistence C → HasSingleDisplacement C →
      invE ≤ t → t ≤ 1 → Disjoint S B → x ∉ S ∪ B → A ⊆ S →
        let σ := fun g u => deathTime C t S (insert x B) τ (Function.update β x u) g
        (∀ g ∈ S, τ g ≤ invE →
          let a_g := σ g invE
          let b_g := σ g t
          invE ≤ a_g ∧ a_g ≤ b_g ∧ b_g ≤ t ∧
          (∀ τ_tilde ∈ Set.Icc invE t, σ g τ_tilde = min (max τ_tilde a_g) b_g) ∧
          (∀ τ_tilde ∈ Set.Ico invE t,
            let U := presentSet S B τ β τ_tilde
            g ∈ C U \ C (insert x U) ↔ a_g ≤ τ_tilde ∧ τ_tilde < b_g) ∧
          LipschitzOnWith 1 (σ g) (Set.Icc invE t)) ∧
        (∀ g₁ ∈ S, ∀ g₂ ∈ S, τ g₁ ≤ invE → τ g₂ ≤ invE → g₁ ≠ g₂ →
          Disjoint (Set.Ico (σ g₁ invE) (σ g₁ t)) (Set.Ico (σ g₂ invE) (σ g₂ t))) ∧
        (∃ K₀ : NNReal,
          LipschitzOnWith K₀
            (fun u => retainProd C t S (insert x B) τ (Function.update β x u) A)
            (Set.Icc invE t)) ∧
        (∃ K : NNReal,
          LipschitzOnWith K
            (fun u => u * retainProd C t S (insert x B) τ (Function.update β x u) A)
            (Set.Icc invE t))) ∧
    -- (3) Lemma B.3 (lem:local-move): Pointwise derivative formula and bound
    (∀ (n : ℕ) (C : Finset (Fin n) → Finset (Fin n)) (t τ_tilde : ℝ)
        (S B : Finset (Fin n)) (x : Fin n) (A : Finset (Fin n)) (τ β : Fin n → ℝ),
      IsChoiceRule C → HasPersistence C → HasSingleDisplacement C →
      invE < τ_tilde → τ_tilde < t → t ≤ 1 →
      Disjoint S B → x ∉ S ∪ B → A ⊆ S →
      (∀ g ∈ S, τ g ≠ τ_tilde) → (∀ b ∈ B, β b ≠ τ_tilde) →
        let U := presentSet S B τ β τ_tilde
        let φ := fun u => retainProd C t S (insert x B) τ (Function.update β x u) A
        let φ_no := fun f =>
          retainProdWithout C t S (insert x B) τ (Function.update β x τ_tilde) A f
        DifferentiableAt ℝ φ τ_tilde ∧
        DifferentiableAt ℝ (fun u => u * φ u) τ_tilde ∧
        |deriv (fun u => u * φ u) τ_tilde| ≤ 2 ∧
        (∀ f ∈ S \ A, τ f ≤ invE → f ∈ C U \ C (insert x U) →
          deriv (fun u => u * φ u) τ_tilde =
            - Real.log (Real.exp 1 * τ_tilde) * φ_no f) ∧
        ((¬ ∃ f ∈ S \ A, τ f ≤ invE ∧ f ∈ C U \ C (insert x U)) →
          φ τ_tilde ≤ deriv (fun u => u * φ u) τ_tilde) ∧
        ((¬ ∃ f ∈ S, τ f ≤ invE ∧ f ∈ C U \ C (insert x U)) →
          deriv (fun u => u * φ u) τ_tilde = φ τ_tilde) ∧
        (∀ f ∈ S, invE < τ f → f ∈ C U \ C (insert x U) →
          deriv (fun u => u * φ u) τ_tilde = φ τ_tilde)) ∧
    -- (4) Lemma B.4 (lem:payment): Cost-and-repayment integral identity
    (∀ (n : ℕ) (C : Finset (Fin n) → Finset (Fin n)) (t τ_tilde : ℝ)
        (S B : Finset (Fin n)) (x f : Fin n) (A : Finset (Fin n)) (β : Fin n → ℝ),
      IsChoiceRule C → HasPersistence C → HasSingleDisplacement C →
      invE < τ_tilde → τ_tilde < t → t ≤ 1 →
      Disjoint S B → (∀ b ∈ B, invE ≤ β b ∧ β b ≤ t ∧ β b ≠ τ_tilde) →
      x ∉ S ∪ B → A ⊆ S → f ∈ S \ A →
      C (S ∪ B.filter (fun b => β b ≤ τ_tilde)) \
        C (insert x (S ∪ B.filter (fun b => β b ≤ τ_tilde))) = {f} →
        let μ_f : ℝ → ℝ := fun u =>
          genMovingProb2 C τ_tilde t (S.erase f) (insert x B) (Function.update β x τ_tilde) f A u
        let dPhi : (Fin n → ℝ) → ℝ := fun τ =>
          deriv (fun u => u * retainProd C t S (insert x B) τ (Function.update β x u) A) τ_tilde
        (∫ τ, dPhi τ ∂(unifCubeMeasure n τ_tilde)) =
          (1 / τ_tilde) * (∫ τ_f in Set.Icc invE τ_tilde, μ_f τ_f) -
            (Real.log (Real.exp 1 * τ_tilde) / (Real.exp 1 * τ_tilde)) * μ_f invE ∧
        (∫ τ, dPhi τ ∂(unifCubeMeasure n τ_tilde)) =
          (1 / τ_tilde) * (∫ τ_f in Set.Icc invE τ_tilde,
            (μ_f τ_f - μ_f invE / (Real.exp 1 * τ_f)))) :=
by
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
      have h_set_pres : ∀ z : Fin n,
          MeasurableSet {ω : Ω | z ∈ presentSet S B (τ_fn ω) (β_fn ω) (candVal c ω)} := by
        intro z
        have heq_z : {ω : Ω | z ∈ presentSet S B (τ_fn ω) (β_fn ω) (candVal c ω)} =
            (if z ∈ S then {ω | τ_fn ω z ≤ candVal c ω} else ∅) ∪
            (if z ∈ B then {ω | β_fn ω z ≤ candVal c ω} else ∅) := by
          ext ω
          simp [presentSet]
        rw [heq_z]
        refine MeasurableSet.union ?_ ?_
        · split_ifs
          · exact measurableSet_le ((measurable_pi_apply z).comp hτ) hu
          · exact MeasurableSet.empty
        · split_ifs
          · exact measurableSet_le ((measurable_pi_apply z).comp hβ) hu
          · exact MeasurableSet.empty
      have h_notC : MeasurableSet
          {ω : Ω | g ∉ C (presentSet S B (τ_fn ω) (β_fn ω) (candVal c ω))} := by
        let badSets := (Finset.univ : Finset (Finset (Fin n))).filter (fun U => g ∉ C U)
        have heq_bad : {ω : Ω | g ∉ C (presentSet S B (τ_fn ω) (β_fn ω) (candVal c ω))} =
            ⋃ U ∈ badSets, ⋂ z : Fin n,
              if z ∈ U then {ω | z ∈ presentSet S B (τ_fn ω) (β_fn ω) (candVal c ω)}
              else {ω | z ∈ presentSet S B (τ_fn ω) (β_fn ω) (candVal c ω)}ᶜ := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, badSets, Finset.mem_filter,
            Finset.mem_univ, true_and]
          refine ⟨fun hg => ⟨presentSet S B (τ_fn ω) (β_fn ω) (candVal c ω), hg, fun z => ?_⟩, ?_⟩
          · split_ifs with hz <;> simp [hz]
          · rintro ⟨U, hgU, hzU⟩
            have hU_eq : presentSet S B (τ_fn ω) (β_fn ω) (candVal c ω) = U := by
              ext z
              specialize hzU z
              by_cases hz : z ∈ U <;> simp [hz] at hzU ⊢ <;> exact hzU
            rwa [hU_eq]
        rw [heq_bad]
        refine Finset.measurableSet_biUnion _ (fun U _ => MeasurableSet.iInter (fun z => ?_))
        split_ifs
        · exact h_set_pres z
        · exact (h_set_pres z).compl
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

  
  have h_clamp_core : ∀ {n : ℕ} (C : Finset (Fin n) → Finset (Fin n)) {t : ℝ}
      (S B : Finset (Fin n)) {x : Fin n} (τ β : Fin n → ℝ),
      HasPersistence C → invE ≤ t → x ∉ B →
      let σ := fun g u => deathTime C t S (insert x B) τ (Function.update β x u) g
      ∀ g ∈ S, τ g ≤ invE →
        let a_g := σ g invE
        let b_g := σ g t
        invE ≤ a_g ∧ a_g ≤ b_g ∧ b_g ≤ t ∧
        (∀ τ_tilde ∈ Set.Icc invE t, σ g τ_tilde = min (max τ_tilde a_g) b_g) ∧
        (∀ τ_tilde ∈ Set.Ico invE t,
          let U := presentSet S B τ β τ_tilde
          g ∈ C U \ C (insert x U) ↔ a_g ≤ τ_tilde ∧ τ_tilde < b_g) ∧
        LipschitzOnWith 1 (σ g) (Set.Icc invE t) := by
    intro n C t S B x τ β hP ht_low hxB σ g hgS hg_early
    dsimp only
    let a_g := σ g invE
    let b_g := σ g t
    let U_fn : ℝ → Finset (Fin n) := fun w => presentSet S B τ β w
    let J : Set ℝ := {w : ℝ | invE ≤ w ∧ w ≤ t ∧ g ∉ C (U_fn w)}
    let J_x : Set ℝ := {w : ℝ | invE ≤ w ∧ w ≤ t ∧ g ∉ C (insert x (U_fn w))}
    let E : ℝ → Set ℝ := fun u =>
      {w : ℝ | invE ≤ w ∧ w ≤ t ∧
        g ∉ C (presentSet S (insert x B) τ (Function.update β x u) w)} ∪ {t}
    have hBdd : ∀ u, BddBelow (E u) := fun u => ⟨invE, by
      rintro w (hw | hw)
      · exact hw.1
      · rw [Set.mem_singleton_iff.mp hw]; exact ht_low⟩
    have hE_invE : E invE = J_x ∪ {t} := by
      ext w
      simp only [E, J_x, U_fn, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
      refine or_congr_left ?_
      refine and_congr_right (fun hw_lo => and_congr_right (fun _ => ?_))
      rw [h_pres_update S B hxB τ β invE w, if_pos hw_lo]
    have hE_t : E t = J ∪ {t} := by
      ext w
      by_cases hwt : w = t
      · simp [E, J, hwt]
      · simp only [E, J, U_fn, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff, hwt, or_false]
        refine and_congr_right (fun _ => and_congr_right (fun hw_hi => ?_))
        have hw_lt : w < t := lt_of_le_of_ne hw_hi hwt
        rw [h_pres_update S B hxB τ β t w, if_neg (not_le_of_gt hw_lt)]
    have hJ_sub : J ⊆ J_x := by
      rintro w ⟨hw_lo, hw_hi, hnot⟩
      refine ⟨hw_lo, hw_hi, fun hgx => hnot ?_⟩
      have hgU : g ∈ U_fn w := by simp [U_fn, presentSet, hgS, hg_early.trans hw_lo]
      exact hP (U_fn w) (insert x (U_fn w)) (Finset.subset_insert x _)
        (Finset.mem_inter.mpr ⟨hgx, hgU⟩)
    have hJ_up : ∀ {w₁ w₂ : ℝ}, w₁ ∈ J → w₁ ≤ w₂ → w₂ ≤ t → w₂ ∈ J := by
      rintro w₁ w₂ ⟨hw₁_lo, _, hnot₁⟩ hw₁₂ hw₂_hi
      refine ⟨hw₁_lo.trans hw₁₂, hw₂_hi, fun hg₂ => hnot₁ ?_⟩
      have hgU₁ : g ∈ U_fn w₁ := by simp [U_fn, presentSet, hgS, hg_early.trans hw₁_lo]
      exact hP (U_fn w₁) (U_fn w₂) (h_pres_mono S B τ β hw₁₂)
        (Finset.mem_inter.mpr ⟨hg₂, hgU₁⟩)
    have hJx_up : ∀ {w₁ w₂ : ℝ}, w₁ ∈ J_x → w₁ ≤ w₂ → w₂ ≤ t → w₂ ∈ J_x := by
      rintro w₁ w₂ ⟨hw₁_lo, _, hnot₁⟩ hw₁₂ hw₂_hi
      refine ⟨hw₁_lo.trans hw₁₂, hw₂_hi, fun hg₂ => hnot₁ ?_⟩
      have hgU₁ : g ∈ insert x (U_fn w₁) :=
        Finset.mem_insert_of_mem (by simp [U_fn, presentSet, hgS, hg_early.trans hw₁_lo])
      exact hP (insert x (U_fn w₁)) (insert x (U_fn w₂))
        (Finset.insert_subset_insert x (h_pres_mono S B τ β hw₁₂))
        (Finset.mem_inter.mpr ⟨hg₂, hgU₁⟩)
    have ha_bounds := h_dt_bounds C ht_low S (insert x B) τ (Function.update β x invE) g
    have hb_bounds := h_dt_bounds C ht_low S (insert x B) τ (Function.update β x t) g
    have hab : a_g ≤ b_g := by
      have h_sub : E t ⊆ E invE := by
        rw [hE_t, hE_invE]
        exact Set.union_subset_union_left _ hJ_sub
      exact csInf_le_csInf (hBdd invE) ⟨t, Set.mem_union_right _ rfl⟩ h_sub
    have ha_mem : a_g ∈ J_x ∪ {t} := by
      have hm := h_dt_mem C ht_low S (insert x B) τ (Function.update β x invE) g
      change a_g ∈ E invE at hm
      rwa [hE_invE] at hm
    have hb_mem : b_g ∈ J ∪ {t} := by
      have hm := h_dt_mem C ht_low S (insert x B) τ (Function.update β x t) g
      change b_g ∈ E t at hm
      rwa [hE_t] at hm
    have hJ_Icc : J ∪ {t} = Set.Icc b_g t := by
      ext w
      refine ⟨fun hw => ?_, fun ⟨hbw, hwt⟩ => ?_⟩
      · have hwE : w ∈ E t := by rwa [hE_t]
        refine ⟨csInf_le (hBdd t) hwE, ?_⟩
        rcases hw with ⟨_, hwt, _⟩ | hwt
        · exact hwt
        · exact (Set.mem_singleton_iff.mp hwt).le
      · by_cases hwt_eq : w = t
        · exact Set.mem_union_right _ hwt_eq
        · have hbw_lt : b_g < t := hbw.trans_lt (lt_of_le_of_ne hwt hwt_eq)
          rcases hb_mem with hbJ | hbt
          · exact Set.mem_union_left _ (hJ_up hbJ hbw hwt)
          · exact (hbw_lt.ne (Set.mem_singleton_iff.mp hbt)).elim
    have hJx_Icc : J_x ∪ {t} = Set.Icc a_g t := by
      ext w
      refine ⟨fun hw => ?_, fun ⟨haw, hwt⟩ => ?_⟩
      · have hwE : w ∈ E invE := by rwa [hE_invE]
        refine ⟨csInf_le (hBdd invE) hwE, ?_⟩
        rcases hw with ⟨_, hwt, _⟩ | hwt
        · exact hwt
        · exact (Set.mem_singleton_iff.mp hwt).le
      · by_cases hwt_eq : w = t
        · exact Set.mem_union_right _ hwt_eq
        · have haw_lt : a_g < t := haw.trans_lt (lt_of_le_of_ne hwt hwt_eq)
          rcases ha_mem with haJx | hat
          · exact Set.mem_union_left _ (hJx_up haJx haw hwt)
          · exact (haw_lt.ne (Set.mem_singleton_iff.mp hat)).elim
    have h_clamp_eq : ∀ τ_tilde ∈ Set.Icc invE t, σ g τ_tilde = min (max τ_tilde a_g) b_g := by
      intro τ_tilde ⟨hτ_lo, hτ_hi⟩
      let m := min (max τ_tilde a_g) b_g
      have ha_le_m : a_g ≤ m := le_min (le_max_right τ_tilde a_g) hab
      have hm_le_t : m ≤ t := (min_le_right _ b_g).trans hb_bounds.2
      have hE_eq : E τ_tilde = Set.Icc m t := by
        ext w
        refine ⟨fun hw => ?_, fun ⟨hmw, hwt⟩ => ?_⟩
        · rcases hw with ⟨hw_lo, hw_hi, hnot⟩ | hwt
          · rw [h_pres_update S B hxB τ β τ_tilde w] at hnot
            by_cases hτw : τ_tilde ≤ w
            · rw [if_pos hτw] at hnot
              have hwJx : w ∈ J_x ∪ {t} := Set.mem_union_left _ ⟨hw_lo, hw_hi, hnot⟩
              rw [hJx_Icc] at hwJx
              exact ⟨(min_le_left _ _).trans (max_le hτw hwJx.1), hw_hi⟩
            · rw [if_neg hτw] at hnot
              have hwJ : w ∈ J ∪ {t} := Set.mem_union_left _ ⟨hw_lo, hw_hi, hnot⟩
              rw [hJ_Icc] at hwJ
              exact ⟨(min_le_right _ _).trans hwJ.1, hw_hi⟩
          · rw [Set.mem_singleton_iff.mp hwt]
            exact ⟨hm_le_t, le_rfl⟩
        · by_cases hwt_eq : w = t
          · exact Set.mem_union_right _ hwt_eq
          · by_cases hτw : τ_tilde ≤ w
            · have hw_Icc : w ∈ Set.Icc a_g t := ⟨ha_le_m.trans hmw, hwt⟩
              rw [← hJx_Icc] at hw_Icc
              rcases hw_Icc with ⟨hw_lo, hw_hi, hnot⟩ | h_eq
              · refine Set.mem_union_left _ ⟨hw_lo, hw_hi, ?_⟩
                rw [h_pres_update S B hxB τ β τ_tilde w, if_pos hτw]
                exact hnot
              · exact (hwt_eq h_eq).elim
            · have hw_lt_max : w < max τ_tilde a_g :=
                (lt_of_not_ge hτw).trans_le (le_max_left τ_tilde a_g)
              have hbw : b_g ≤ w := by
                rcases min_cases (max τ_tilde a_g) b_g with ⟨h_eq, _⟩ | ⟨h_eq, _⟩
                · dsimp only [m] at hmw; linarith
                · dsimp only [m] at hmw; linarith
              have hw_Icc : w ∈ Set.Icc b_g t := ⟨hbw, hwt⟩
              rw [← hJ_Icc] at hw_Icc
              rcases hw_Icc with ⟨hw_lo, hw_hi, hnot⟩ | h_eq
              · refine Set.mem_union_left _ ⟨hw_lo, hw_hi, ?_⟩
                rw [h_pres_update S B hxB τ β τ_tilde w, if_neg hτw]
                exact hnot
              · exact (hwt_eq h_eq).elim
      change sInf (E τ_tilde) = m
      rw [hE_eq]
      exact csInf_Icc hm_le_t
    have h_disp_iff : ∀ τ_tilde ∈ Set.Ico invE t,
        let U := presentSet S B τ β τ_tilde
        g ∈ C U \ C (insert x U) ↔ a_g ≤ τ_tilde ∧ τ_tilde < b_g := by
      intro τ_tilde ⟨hτ_lo, hτ_lt⟩
      dsimp only
      have hτ_hi : τ_tilde ≤ t := hτ_lt.le
      have hτ_ne : τ_tilde ≠ t := hτ_lt.ne
      have h_a_iff : g ∉ C (insert x (U_fn τ_tilde)) ↔ a_g ≤ τ_tilde := by
        calc g ∉ C (insert x (U_fn τ_tilde))
            ↔ τ_tilde ∈ J_x := ⟨fun h => ⟨hτ_lo, hτ_hi, h⟩, fun h => h.2.2⟩
          _ ↔ τ_tilde ∈ J_x ∪ {t} :=
              ⟨Set.mem_union_left _, fun h => h.elim id (fun ht => (hτ_ne ht).elim)⟩
          _ ↔ τ_tilde ∈ Set.Icc a_g t := by rw [hJx_Icc]
          _ ↔ a_g ≤ τ_tilde := ⟨fun h => h.1, fun h => ⟨h, hτ_hi⟩⟩
      have h_b_iff : g ∉ C (U_fn τ_tilde) ↔ b_g ≤ τ_tilde := by
        calc g ∉ C (U_fn τ_tilde)
            ↔ τ_tilde ∈ J := ⟨fun h => ⟨hτ_lo, hτ_hi, h⟩, fun h => h.2.2⟩
          _ ↔ τ_tilde ∈ J ∪ {t} :=
              ⟨Set.mem_union_left _, fun h => h.elim id (fun ht => (hτ_ne ht).elim)⟩
          _ ↔ τ_tilde ∈ Set.Icc b_g t := by rw [hJ_Icc]
          _ ↔ b_g ≤ τ_tilde := ⟨fun h => h.1, fun h => ⟨h, hτ_hi⟩⟩
      rw [Finset.mem_sdiff]
      refine ⟨fun ⟨hgU, hg_notx⟩ =>
        ⟨h_a_iff.mp hg_notx, lt_of_not_ge (fun hb_le => (h_b_iff.mpr hb_le) hgU)⟩,
        fun ⟨ha_le, hlt_b⟩ =>
          ⟨by_contra (fun hnot => not_lt_of_ge (h_b_iff.mp hnot) hlt_b), h_a_iff.mpr ha_le⟩⟩
    have h_lip : LipschitzOnWith 1 (σ g) (Set.Icc invE t) := by
      have h_cl_step : ∀ u₁ u₂ : ℝ, u₁ ≤ u₂ →
          |min (max u₁ a_g) b_g - min (max u₂ a_g) b_g| ≤ |u₁ - u₂| := by
        intro u₁ u₂ hu
        have h_mono : min (max u₁ a_g) b_g ≤ min (max u₂ a_g) b_g :=
          min_le_min_right b_g (max_le_max_right a_g hu)
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h_mono),
          abs_sub_comm u₁ u₂, abs_of_nonneg (sub_nonneg.mpr hu)]
        rcases max_cases u₁ a_g with ⟨h1_eq, h1_le⟩ | ⟨h1_eq, h1_lt⟩ <;>
          rcases max_cases u₂ a_g with ⟨h2_eq, h2_le⟩ | ⟨h2_eq, h2_lt⟩ <;>
          rcases min_cases (max u₁ a_g) b_g with ⟨m1_eq, m1_le⟩ | ⟨m1_eq, m1_lt⟩ <;>
          rcases min_cases (max u₂ a_g) b_g with ⟨m2_eq, m2_le⟩ | ⟨m2_eq, m2_lt⟩ <;>
          linarith
      refine LipschitzOnWith.of_dist_le_mul (fun u₁ hu₁ u₂ hu₂ => ?_)
      simp only [NNReal.coe_one, one_mul, Real.dist_eq]
      rw [h_clamp_eq u₁ hu₁, h_clamp_eq u₂ hu₂]
      rcases le_total u₁ u₂ with h12 | h21
      · exact h_cl_step u₁ u₂ h12
      · rw [abs_sub_comm, abs_sub_comm u₁ u₂]
        exact h_cl_step u₂ u₁ h21
    exact ⟨ha_bounds.1, hab, hb_bounds.2, h_clamp_eq, h_disp_iff, h_lip⟩

  have h_lip_retain : ∀ {n : ℕ} (C : Finset (Fin n) → Finset (Fin n)) {t : ℝ}
      (S B : Finset (Fin n)) {x : Fin n} (A : Finset (Fin n)) (τ β : Fin n → ℝ),
      HasPersistence C → invE ≤ t → t ≤ 1 → x ∉ B → A ⊆ S →
      let L₀ : ℝ := ((A.card : ℝ) + ((S \ A).card : ℝ)) * Real.exp 1
      (∀ u₁ ∈ Set.Icc invE t, ∀ u₂ ∈ Set.Icc invE t,
        |retainProd C t S (insert x B) τ (Function.update β x u₁) A -
          retainProd C t S (insert x B) τ (Function.update β x u₂) A| ≤ L₀ * |u₁ - u₂|) ∧
      (∀ u₁ ∈ Set.Icc invE t, ∀ u₂ ∈ Set.Icc invE t,
        |u₁ * retainProd C t S (insert x B) τ (Function.update β x u₁) A -
          u₂ * retainProd C t S (insert x B) τ (Function.update β x u₂) A| ≤
            (1 + L₀) * |u₁ - u₂|) := by
    intro n C t S B x A τ β hP ht_low ht_high hxB hA L₀
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
        (∀ u ∈ I, |f₁ u| ≤ 1) → (∀ u ∈ I, |f₂ u| ≤ 1) →
        (∀ u₁ ∈ I, ∀ u₂ ∈ I, |f₁ u₁ - f₁ u₂| ≤ L₁ * |u₁ - u₂|) →
        (∀ u₁ ∈ I, ∀ u₂ ∈ I, |f₂ u₁ - f₂ u₂| ≤ L₂ * |u₁ - u₂|) →
        (∀ u ∈ I, |f₁ u * f₂ u| ≤ 1) ∧
          (∀ u₁ ∈ I, ∀ u₂ ∈ I, |f₁ u₁ * f₂ u₁ - f₁ u₂ * f₂ u₂| ≤ (L₁ + L₂) * |u₁ - u₂|) := by
      intro f₁ f₂ L₁ L₂ hb₁ hb₂ hl₁ hl₂
      refine ⟨fun u hu => by rw [abs_mul]; exact mul_le_one₀ (hb₁ u hu) (abs_nonneg _) (hb₂ u hu),
        fun u₁ hu₁ u₂ hu₂ => ?_⟩
      calc |f₁ u₁ * f₂ u₁ - f₁ u₂ * f₂ u₂|
          = |(f₁ u₁ - f₁ u₂) * f₂ u₁ + f₁ u₂ * (f₂ u₁ - f₂ u₂)| := by ring_nf
        _ ≤ |(f₁ u₁ - f₁ u₂) * f₂ u₁| + |f₁ u₂ * (f₂ u₁ - f₂ u₂)| := abs_add_le _ _
        _ = |f₁ u₁ - f₁ u₂| * |f₂ u₁| + |f₁ u₂| * |f₂ u₁ - f₂ u₂| := by rw [abs_mul, abs_mul]
        _ ≤ (L₁ * |u₁ - u₂|) * 1 + 1 * (L₂ * |u₁ - u₂|) :=
            add_le_add
              (mul_le_mul (hl₁ u₁ hu₁ u₂ hu₂) (hb₂ u₁ hu₁) (abs_nonneg _)
                (le_trans (abs_nonneg _) (hl₁ u₁ hu₁ u₂ hu₂)))
              (mul_le_mul (hb₁ u₂ hu₂) (hl₂ u₁ hu₁ u₂ hu₂) (abs_nonneg _) zero_le_one)
        _ = (L₁ + L₂) * |u₁ - u₂| := by ring
    have h_finset_prod_lip : ∀ {α : Type} [DecidableEq α] (F : Finset α) (f : α → ℝ → ℝ) (L : ℝ),
        (∀ a ∈ F, (∀ u ∈ I, |f a u| ≤ 1) ∧
          ∀ u₁ ∈ I, ∀ u₂ ∈ I, |f a u₁ - f a u₂| ≤ L * |u₁ - u₂|) →
        (∀ u ∈ I, |∏ a ∈ F, f a u| ≤ 1) ∧
          ∀ u₁ ∈ I, ∀ u₂ ∈ I,
            |(∏ a ∈ F, f a u₁) - (∏ a ∈ F, f a u₂)| ≤ ((F.card : ℝ) * L) * |u₁ - u₂| := by
      intro α _ F f L hf
      induction F using Finset.induction_on with
      | empty =>
        refine ⟨fun _ _ => by simp, fun _ _ _ _ => by simp⟩
      | insert a s has ih =>
        obtain ⟨hba, hla⟩ := hf a (Finset.mem_insert_self a s)
        obtain ⟨hbs, hls⟩ := ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
        obtain ⟨hb_prod, hl_prod⟩ := h_mul_lip hba hbs hla hls
        refine ⟨fun u hu => by simpa [Finset.prod_insert has] using hb_prod u hu,
          fun u₁ hu₁ u₂ hu₂ => ?_⟩
        have hstep := hl_prod u₁ hu₁ u₂ hu₂
        simp only [Finset.prod_insert has]
        have hcard : (((insert a s).card : ℝ) * L) = L + (s.card : ℝ) * L := by
          rw [Finset.card_insert_of_notMem has]
          push_cast
          ring
        rw [hcard]
        exact hstep
    have h_θ_lip : ∀ g ∈ S,
        (∀ u ∈ I, |retentionProb C t S (insert x B) τ (Function.update β x u) g| ≤ 1) ∧
        ∀ u₁ ∈ I, ∀ u₂ ∈ I,
          |retentionProb C t S (insert x B) τ (Function.update β x u₁) g -
            retentionProb C t S (insert x B) τ (Function.update β x u₂) g| ≤
              Real.exp 1 * |u₁ - u₂| := by
      intro g hgS
      refine ⟨fun u _ => ?_, fun u₁ hu₁ u₂ hu₂ => ?_⟩
      · obtain ⟨h0, h1⟩ := h_ret_bounds C ht_low ht_high S (insert x B) τ (Function.update β x u) g
        rw [abs_of_nonneg h0]
        exact h1
      · unfold retentionProb
        split_ifs with hτ
        · have h_lip1 := (h_clamp_core C S B τ β hP ht_low hxB g hgS hτ).2.2.2.2.2
          have h_dist := h_lip1.dist_le_mul u₁ hu₁ u₂ hu₂
          simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h_dist
          have hlo1 := (h_dt_bounds C ht_low S (insert x B) τ (Function.update β x u₁) g).1
          have hlo2 := (h_dt_bounds C ht_low S (insert x B) τ (Function.update β x u₂) g).1
          exact (h_log_lip hlo1 hlo2).trans
            (mul_le_mul_of_nonneg_left h_dist (Real.exp_pos 1).le)
        · simp [mul_nonneg (Real.exp_pos 1).le (abs_nonneg _)]
    obtain ⟨hbA, hlA⟩ := h_finset_prod_lip A
      (fun g u => retentionProb C t S (insert x B) τ (Function.update β x u) g) (Real.exp 1)
      (fun g hgA => h_θ_lip g (hA hgA))
    obtain ⟨hbSA, hlSA⟩ := h_finset_prod_lip (S \ A)
      (fun g u => 1 - retentionProb C t S (insert x B) τ (Function.update β x u) g) (Real.exp 1)
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
    obtain ⟨hb_phi, hl_phi⟩ := h_mul_lip hbA hbSA hlA hlSA
    have hL₀_eq : (A.card : ℝ) * Real.exp 1 + ((S \ A).card : ℝ) * Real.exp 1 = L₀ := by
      dsimp only [L₀]; ring
    have hl_phi' : ∀ u₁ ∈ I, ∀ u₂ ∈ I,
        |retainProd C t S (insert x B) τ (Function.update β x u₁) A -
          retainProd C t S (insert x B) τ (Function.update β x u₂) A| ≤ L₀ * |u₁ - u₂| := by
      intro u₁ hu₁ u₂ hu₂
      simp only [retainProd, if_pos hA]
      rw [← hL₀_eq]
      exact hl_phi u₁ hu₁ u₂ hu₂
    have hb_phi' : ∀ u ∈ I, |retainProd C t S (insert x B) τ (Function.update β x u) A| ≤ 1 := by
      intro u hu
      simp only [retainProd, if_pos hA]
      exact hb_phi u hu
    have hb_id : ∀ u ∈ I, |u| ≤ 1 := fun u hu => by
      rw [abs_of_nonneg (h_invE_pos.le.trans hu.1)]
      exact hu.2.trans ht_high
    have hl_id : ∀ u₁ ∈ I, ∀ u₂ ∈ I, |u₁ - u₂| ≤ 1 * |u₁ - u₂| := fun _ _ _ _ => by simp
    obtain ⟨_, hl_tot⟩ := h_mul_lip hb_id hb_phi' hl_id hl_phi'
    exact ⟨hl_phi', hl_tot⟩

  
  have h_local_move : ∀ (n : ℕ) (C : Finset (Fin n) → Finset (Fin n)) (t τ_tilde : ℝ)
      (S B : Finset (Fin n)) (x : Fin n) (A : Finset (Fin n)) (τ β : Fin n → ℝ),
      IsChoiceRule C → HasPersistence C → HasSingleDisplacement C →
      invE < τ_tilde → τ_tilde < t → t ≤ 1 →
      Disjoint S B → x ∉ S ∪ B → A ⊆ S →
      (∀ g ∈ S, τ g ≠ τ_tilde) → (∀ b ∈ B, β b ≠ τ_tilde) →
        let U := presentSet S B τ β τ_tilde
        let φ := fun u => retainProd C t S (insert x B) τ (Function.update β x u) A
        let φ_no := fun f =>
          retainProdWithout C t S (insert x B) τ (Function.update β x τ_tilde) A f
        DifferentiableAt ℝ φ τ_tilde ∧
        DifferentiableAt ℝ (fun u => u * φ u) τ_tilde ∧
        |deriv (fun u => u * φ u) τ_tilde| ≤ 2 ∧
        (∀ f ∈ S \ A, τ f ≤ invE → f ∈ C U \ C (insert x U) →
          deriv (fun u => u * φ u) τ_tilde =
            - Real.log (Real.exp 1 * τ_tilde) * φ_no f) ∧
        ((¬ ∃ f ∈ S \ A, τ f ≤ invE ∧ f ∈ C U \ C (insert x U)) →
          φ τ_tilde ≤ deriv (fun u => u * φ u) τ_tilde) ∧
        ((¬ ∃ f ∈ S, τ f ≤ invE ∧ f ∈ C U \ C (insert x U)) →
          deriv (fun u => u * φ u) τ_tilde = φ τ_tilde) ∧
        (∀ f ∈ S, invE < τ f → f ∈ C U \ C (insert x U) →
          deriv (fun u => u * φ u) τ_tilde = φ τ_tilde) := by
    intro n C t τ_tilde S B x A τ β _ hP hSD h_low h_high ht_one _ hxSB hA hτ_ne hβ_ne
    dsimp only
    let U := presentSet S B τ β τ_tilde
    let φ := fun u => retainProd C t S (insert x B) τ (Function.update β x u) A
    let φ_no := fun f =>
      retainProdWithout C t S (insert x B) τ (Function.update β x τ_tilde) A f
    have ht_low : invE ≤ t := (h_low.trans h_high).le
    have hτ_pos : 0 < τ_tilde := h_invE_pos.trans h_low
    have hxB : x ∉ B := fun hb => hxSB (Finset.mem_union_right S hb)
    have hxU : x ∉ U := by
      intro hx_in
      simp only [U, presentSet, Finset.mem_union, Finset.mem_filter] at hx_in
      rcases hx_in with ⟨hxS, _⟩ | ⟨hxB', _⟩
      · exact hxSB (Finset.mem_union_left B hxS)
      · exact hxB hxB'
    have h_late_imp : ((¬ ∃ f ∈ S, τ f ≤ invE ∧ f ∈ C U \ C (insert x U)) →
        deriv (fun u => u * φ u) τ_tilde = φ τ_tilde) →
        (∀ f ∈ S, invE < τ f → f ∈ C U \ C (insert x U) →
          deriv (fun u => u * φ u) τ_tilde = φ τ_tilde) := by
      intro h_no_early f _ hf_late hf_disp
      refine h_no_early ?_
      rintro ⟨g, _, hg_early, hg_disp⟩
      have hgf : g = f := Finset.card_le_one.mp (hSD U x hxU) g hg_disp f hf_disp
      subst hgf
      exact not_lt_of_ge hg_early hf_late
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
            have h1 : g ∈ C (W u v) := by
              rw [hWu]; split_ifs <;> assumption
            have h2 : g ∈ C (W τ_tilde v) := by
              rw [hWt]; split_ifs <;> assumption
            simp [W, hv_ne_t, h1, h2]
          · have hg_not_CxU : g ∉ C (insert x U) := mt h_pers_x hgCU
            have h1 : g ∉ C (W u v) := by
              rw [hWu]; split_ifs <;> assumption
            have h2 : g ∉ C (W τ_tilde v) := by
              rw [hWt]; split_ifs <;> assumption
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
    have hφ_bounds : 0 ≤ φ τ_tilde ∧ φ τ_tilde ≤ 1 :=
      h_prod_bounds C ht_low ht_one S (insert x B) τ (Function.update β x τ_tilde) A
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
      have h_no_e : (¬ ∃ f ∈ S, τ f ≤ invE ∧ f ∈ C U \ C (insert x U)) →
          deriv (fun u => u * φ u) τ_tilde = φ τ_tilde := fun _ => hd_uφ.deriv
      refine ⟨hd_φ.differentiableAt, hd_uφ.differentiableAt, ?_, ?_, ?_, h_no_e, h_late_imp h_no_e⟩
      · rw [hd_uφ.deriv, abs_of_nonneg hφ_bounds.1]
        linarith [hφ_bounds.2]
      · intro f hfSA hf_early hf_disp
        have hfD : f ∈ D := Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hfSA).1, hf_early, hf_disp⟩
        rw [hD_emp] at hfD
        exact (Finset.notMem_empty f hfD).elim
      · intro _
        rw [hd_uφ.deriv]
    · obtain ⟨f, hf_eq⟩ := Finset.card_eq_one.mp hD1
      have hfD : f ∈ D := by rw [hf_eq]; exact Finset.mem_singleton_self f
      obtain ⟨hfS, hf_early, hf_disp⟩ := Finset.mem_filter.mp hfD
      by_cases hfA : f ∈ A
      · let c : ℝ := (∏ g ∈ A.erase f, θ τ_tilde g) * (∏ g ∈ S \ A, (1 - θ τ_tilde g))
        have hc_bounds : 0 ≤ c ∧ c ≤ 1 := by
          have h1_nn : 0 ≤ ∏ g ∈ A.erase f, θ τ_tilde g :=
            Finset.prod_nonneg (fun g _ => (h_ret_bounds C ht_low ht_one S (insert x B) τ _ g).1)
          have h1_le : ∏ g ∈ A.erase f, θ τ_tilde g ≤ 1 :=
            Finset.prod_le_one (fun g _ => (h_ret_bounds C ht_low ht_one S (insert x B) τ _ g).1)
              (fun g _ => (h_ret_bounds C ht_low ht_one S (insert x B) τ _ g).2)
          have h2_nn : 0 ≤ ∏ g ∈ S \ A, (1 - θ τ_tilde g) :=
            Finset.prod_nonneg (fun g _ =>
              sub_nonneg.mpr (h_ret_bounds C ht_low ht_one S (insert x B) τ _ g).2)
          have h2_le : ∏ g ∈ S \ A, (1 - θ τ_tilde g) ≤ 1 :=
            Finset.prod_le_one
              (fun g _ => sub_nonneg.mpr (h_ret_bounds C ht_low ht_one S (insert x B) τ _ g).2)
              (fun g _ => sub_le_self 1 (h_ret_bounds C ht_low ht_one S (insert x B) τ _ g).1)
          exact ⟨mul_nonneg h1_nn h2_nn, mul_le_one₀ h1_le h2_nn h2_le⟩
        have hφ_on_I : ∀ u ∈ I_open, φ u = Real.log (Real.exp 1 * u) * c := by
          intro u hu
          dsimp only [φ, retainProd, c]
          rw [if_pos hA, ← Finset.mul_prod_erase A _ hfA, mul_assoc]
          congr 1
          · exact hθ_inD f hfD u hu
          · congr 1
            · refine Finset.prod_congr rfl (fun g hg => ?_)
              obtain ⟨hg_ne, hgA⟩ := Finset.mem_erase.mp hg
              refine hθ_notD g (hA hgA) ?_ u hu
              rw [hf_eq, Finset.mem_singleton]
              exact hg_ne
            · refine Finset.prod_congr rfl (fun g hgSA => ?_)
              obtain ⟨hgS, hg_notA⟩ := Finset.mem_sdiff.mp hgSA
              have hg_ne : g ≠ f := fun heq => hg_notA (heq ▸ hfA)
              congr 1
              exact hθ_notD g hgS (by rw [hf_eq, Finset.mem_singleton]; exact hg_ne) u hu
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
        have h_no_e : (¬ ∃ f ∈ S, τ f ≤ invE ∧ f ∈ C U \ C (insert x U)) →
            deriv (fun u => u * φ u) τ_tilde = φ τ_tilde :=
          fun h_none => (h_none ⟨f, hfS, hf_early, hf_disp⟩).elim
        refine ⟨hd_φ.differentiableAt, hd_uφ.differentiableAt, ?_, ?_, ?_, h_no_e, h_late_imp h_no_e⟩
        · rw [hd_uφ.deriv, abs_of_nonneg (by linarith [hφ_bounds.1, hc_bounds.1])]
          linarith [hφ_bounds.2, hc_bounds.2]
        · intro f' hf'SA hf'_early hf'_disp
          have hf'D : f' ∈ D :=
            Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hf'SA).1, hf'_early, hf'_disp⟩
          rw [hf_eq, Finset.mem_singleton] at hf'D
          subst hf'D
          exact ((Finset.mem_sdiff.mp hf'SA).2 hfA).elim
        · intro _
          rw [hd_uφ.deriv]
          linarith [hc_bounds.1]
      · have hfSA : f ∈ S \ A := Finset.mem_sdiff.mpr ⟨hfS, hfA⟩
        have hc_bounds : 0 ≤ φ_no f ∧ φ_no f ≤ 1 := by
          dsimp only [φ_no, retainProdWithout]
          have h1_nn : 0 ≤ ∏ g ∈ A, θ τ_tilde g :=
            Finset.prod_nonneg (fun g _ => (h_ret_bounds C ht_low ht_one S (insert x B) τ _ g).1)
          have h1_le : ∏ g ∈ A, θ τ_tilde g ≤ 1 :=
            Finset.prod_le_one (fun g _ => (h_ret_bounds C ht_low ht_one S (insert x B) τ _ g).1)
              (fun g _ => (h_ret_bounds C ht_low ht_one S (insert x B) τ _ g).2)
          have h2_nn : 0 ≤ ∏ g ∈ S \ insert f A, (1 - θ τ_tilde g) :=
            Finset.prod_nonneg (fun g _ =>
              sub_nonneg.mpr (h_ret_bounds C ht_low ht_one S (insert x B) τ _ g).2)
          have h2_le : ∏ g ∈ S \ insert f A, (1 - θ τ_tilde g) ≤ 1 :=
            Finset.prod_le_one
              (fun g _ => sub_nonneg.mpr (h_ret_bounds C ht_low ht_one S (insert x B) τ _ g).2)
              (fun g _ => sub_le_self 1 (h_ret_bounds C ht_low ht_one S (insert x B) τ _ g).1)
          exact ⟨mul_nonneg h1_nn h2_nn, mul_le_one₀ h1_le h2_nn h2_le⟩
        have hsdiff_erase : (S \ A).erase f = S \ insert f A := by
          ext g
          simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
          tauto
        have hφ_on_I : ∀ u ∈ I_open, φ u = (1 - Real.log (Real.exp 1 * u)) * φ_no f := by
          intro u hu
          dsimp only [φ, retainProd, φ_no, retainProdWithout]
          rw [if_pos hA, ← Finset.mul_prod_erase (S \ A) _ hfSA, hsdiff_erase]
          have h1_eq : (∏ g ∈ A, θ u g) = ∏ g ∈ A, θ τ_tilde g := by
            refine Finset.prod_congr rfl (fun g hgA => ?_)
            have hg_ne : g ≠ f := fun heq => hfA (heq ▸ hgA)
            exact hθ_notD g (hA hgA) (by rw [hf_eq, Finset.mem_singleton]; exact hg_ne) u hu
          have h2_eq : (∏ g ∈ S \ insert f A, (1 - θ u g)) =
              ∏ g ∈ S \ insert f A, (1 - θ τ_tilde g) := by
            refine Finset.prod_congr rfl (fun g hg => ?_)
            obtain ⟨hgS, hg_not⟩ := Finset.mem_sdiff.mp hg
            have hg_ne : g ≠ f := fun heq => hg_not (heq ▸ Finset.mem_insert_self f A)
            rw [hθ_notD g hgS (by rw [hf_eq, Finset.mem_singleton]; exact hg_ne) u hu]
          have hf_eq_u : θ u f = Real.log (Real.exp 1 * u) := hθ_inD f hfD u hu
          change (∏ g ∈ A, θ u g) * ((1 - θ u f) * ∏ g ∈ S \ insert f A, (1 - θ u g)) =
            (1 - Real.log (Real.exp 1 * u)) *
              ((∏ g ∈ A, θ τ_tilde g) * ∏ g ∈ S \ insert f A, (1 - θ τ_tilde g))
          rw [h1_eq, h2_eq, hf_eq_u]
          ring
        have hd_one_sub : HasDerivAt (fun u : ℝ => 1 - Real.log (Real.exp 1 * u))
            (-τ_tilde⁻¹) τ_tilde := by
          simpa using (hasDerivAt_const τ_tilde (1 : ℝ)).sub h_log_deriv
        have hd_φ : HasDerivAt φ (-τ_tilde⁻¹ * φ_no f) τ_tilde :=
          (hd_one_sub.mul_const (φ_no f)).congr_of_eventuallyEq
            (Filter.eventually_of_mem hI_nhds hφ_on_I)
        have hd_uφ : HasDerivAt (fun u => u * φ u)
            (-Real.log (Real.exp 1 * τ_tilde) * φ_no f) τ_tilde := by
          have hd := (hasDerivAt_id τ_tilde).mul hd_φ
          have hφ_at_t := hφ_on_I τ_tilde hτ_mem_I
          have heq_val : 1 * φ τ_tilde + id τ_tilde * (-τ_tilde⁻¹ * φ_no f) =
              -Real.log (Real.exp 1 * τ_tilde) * φ_no f := by
            dsimp only [id]
            have := hτ_pos.ne'
            rw [hφ_at_t]
            field_simp
            ring
          exact heq_val ▸ hd
        have h_no_e : (¬ ∃ f ∈ S, τ f ≤ invE ∧ f ∈ C U \ C (insert x U)) →
            deriv (fun u => u * φ u) τ_tilde = φ τ_tilde :=
          fun h_none => (h_none ⟨f, hfS, hf_early, hf_disp⟩).elim
        refine ⟨hd_φ.differentiableAt, hd_uφ.differentiableAt, ?_, ?_, ?_, h_no_e, h_late_imp h_no_e⟩
        · rw [hd_uφ.deriv]
          have hlog_lo : 0 ≤ Real.log (Real.exp 1 * τ_tilde) := by
            refine Real.log_nonneg ?_
            calc (1 : ℝ) = Real.exp 1 * invE := h_exp_invE.symm
              _ ≤ Real.exp 1 * τ_tilde :=
                mul_le_mul_of_nonneg_left h_low.le (Real.exp_pos 1).le
          have hlog_hi : Real.log (Real.exp 1 * τ_tilde) ≤ 1 := by
            calc Real.log (Real.exp 1 * τ_tilde)
                ≤ Real.log (Real.exp 1) := by
                  refine Real.log_le_log (mul_pos (Real.exp_pos 1) hτ_pos) ?_
                  calc Real.exp 1 * τ_tilde ≤ Real.exp 1 * 1 :=
                      mul_le_mul_of_nonneg_left (h_high.le.trans ht_one) (Real.exp_pos 1).le
                    _ = Real.exp 1 := mul_one _
              _ = 1 := Real.log_exp 1
          rw [abs_mul, abs_neg, abs_of_nonneg hlog_lo, abs_of_nonneg hc_bounds.1]
          have hle1 : Real.log (Real.exp 1 * τ_tilde) * φ_no f ≤ 1 :=
            mul_le_one₀ hlog_hi hc_bounds.1 hc_bounds.2
          linarith
        · intro f' hf'SA hf'_early hf'_disp
          have hf'D : f' ∈ D :=
            Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hf'SA).1, hf'_early, hf'_disp⟩
          rw [hf_eq, Finset.mem_singleton] at hf'D
          subst hf'D
          exact hd_uφ.deriv
        · intro h_none
          exact (h_none ⟨f, hfSA, hf_early, hf_disp⟩).elim

  
  refine ⟨?_, ?_, h_local_move, ?_⟩
  · 
    intro n C t₀ t S B β hC hP ht₀_low ht₀_t ht_high
    have ht_low : invE ≤ t := ht₀_low.trans ht₀_t
    refine ⟨fun τ A => h_prod_bounds C ht_low ht_high S B τ β A, ?_, ?_, ?_, ?_⟩
    · intro τ
      have h_congr : ∑ A ∈ S.powerset, retainProd C t S B τ β A =
          ∑ A ∈ S.powerset,
            (∏ g ∈ A, retentionProb C t S B τ β g) *
              (∏ g ∈ S \ A, (1 - retentionProb C t S B τ β g)) := by
        refine Finset.sum_congr rfl (fun A hA => ?_)
        unfold retainProd
        rw [if_pos (Finset.mem_powerset.mp hA)]
      rw [h_congr, ← Finset.prod_add]
      simp
    · intro τ A hpos
      have hAS : A ⊆ S := by
        by_contra hnot
        unfold retainProd at hpos
        rw [if_neg hnot] at hpos
        exact lt_irrefl 0 hpos
      intro g hgA
      rw [Finset.mem_inter]
      refine ⟨?_, hAS hgA⟩
      have hθ_ne : retentionProb C t S B τ β g ≠ 0 := by
        intro hzero
        unfold retainProd at hpos
        rw [if_pos hAS, Finset.prod_eq_zero hgA hzero, zero_mul] at hpos
        exact lt_irrefl 0 hpos
      have hθ_pos : 0 < retentionProb C t S B τ β g :=
        lt_of_le_of_ne (h_ret_bounds C ht_low ht_high S B τ β g).1 hθ_ne.symm
      unfold retentionProb at hθ_pos
      split_ifs at hθ_pos with hτ_early
      · have h_dt_ne : deathTime C t S B τ β g ≠ invE := by
          intro heq
          rw [heq, h_exp_invE, Real.log_one] at hθ_pos
          exact lt_irrefl 0 hθ_pos
        have h_dt_gt : invE < deathTime C t S B τ β g :=
          lt_of_le_of_ne (h_dt_bounds C ht_low S B τ β g).1 h_dt_ne.symm
        by_contra hg_notC
        let E : Set ℝ := {u : ℝ | invE ≤ u ∧ u ≤ t ∧ g ∉ C (presentSet S B τ β u)} ∪ {t}
        have hBdd : BddBelow E := ⟨invE, by
          rintro u (hu | rfl)
          · exact hu.1
          · exact ht_low⟩
        have h_le : deathTime C t S B τ β g ≤ invE :=
          csInf_le hBdd (Set.mem_union_left _ ⟨le_rfl, ht_low, hg_notC⟩)
        exact not_lt_of_ge h_le h_dt_gt
      · exact (lt_irrefl 0 hθ_pos).elim
    · intro A
      haveI : IsProbabilityMeasure
          ((ENNReal.ofReal invE)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) invE)) :=
        h_unif1D_prob h_invE_pos
      haveI : IsProbabilityMeasure (unifCubeMeasure n invE) := by
        unfold unifCubeMeasure
        infer_instance
      have h_ret_zero : ∀ τ g, retentionProb C invE S B τ β g = 0 := by
        intro τ g
        unfold retentionProb
        split_ifs with hτ
        · obtain ⟨h1, h2⟩ := h_dt_bounds C le_rfl S B τ β g
          have heq : deathTime C invE S B τ β g = invE := le_antisymm h2 h1
          rw [heq, h_exp_invE, Real.log_one]
        · rfl
      have h_prod_const : ∀ τ, retainProd C invE S B τ β A = (if A = ∅ then 1 else 0) := by
        intro τ
        by_cases hA_emp : A = ∅
        · subst hA_emp
          simp [retainProd, h_ret_zero]
        · rw [if_neg hA_emp]
          unfold retainProd
          split_ifs with hAS
          · obtain ⟨g, hgA⟩ := Finset.nonempty_iff_ne_empty.mpr hA_emp
            rw [Finset.prod_eq_zero hgA (h_ret_zero τ g), zero_mul]
          · rfl
      unfold genSurvivalLaw2
      simp_rw [h_prod_const]
      rw [MeasureTheory.integral_const, probReal_univ, one_smul]
    · intro g hgCS
      have hgS : g ∈ S := hC S hgCS
      have ht_pos : 0 < t := h_invE_pos.trans_le ht_low
      let μ₁ : Measure ℝ := (ENNReal.ofReal t)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) t)
      haveI : IsProbabilityMeasure μ₁ := h_unif1D_prob ht_pos
      haveI : IsProbabilityMeasure (unifCubeMeasure n t) := by
        unfold unifCubeMeasure
        infer_instance
      have h_int : ∀ A : Finset (Fin n),
          Integrable (fun τ => retainProd C t S ∅ τ β A) (unifCubeMeasure n t) := by
        intro A
        have h_meas := (h_meas_prod C ht_low S ∅ A id (fun _ => β) measurable_id measurable_const).2
        exact MeasureTheory.Integrable.of_mem_Icc 0 1 h_meas.aemeasurable
          (Filter.Eventually.of_forall (fun τ => h_prod_bounds C ht_low ht_high S ∅ τ β A))
      unfold genSurvivalLaw genSurvivalLaw2
      rw [← MeasureTheory.integral_finset_sum _ (fun A _ => h_int A)]
      have h_sum_eq : ∀ τ,
          (∑ A ∈ S.powerset.filter (fun A => g ∈ A), retainProd C t S ∅ τ β A) =
            retentionProb C t S ∅ τ β g := by
        intro τ
        have h_filter_eq : S.powerset.filter (fun A => g ∈ A) =
            (S.erase g).powerset.image (insert g) := by
          ext A
          simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
          refine ⟨fun ⟨hAS, hgA⟩ => ⟨A.erase g, ?_, Finset.insert_erase hgA⟩, ?_⟩
          · exact Finset.erase_subset_erase g hAS
          · rintro ⟨A', hA', rfl⟩
            exact ⟨Finset.insert_subset_iff.mpr ⟨hgS, hA'.trans (Finset.erase_subset g S)⟩,
              Finset.mem_insert_self g A'⟩
        rw [h_filter_eq, Finset.sum_image]
        · have h_term : ∀ A' ∈ (S.erase g).powerset,
              retainProd C t S ∅ τ β (insert g A') =
                retentionProb C t S ∅ τ β g *
                  ((∏ x ∈ A', retentionProb C t S ∅ τ β x) *
                    (∏ x ∈ S.erase g \ A', (1 - retentionProb C t S ∅ τ β x))) := by
            intro A' hA'
            have hA'_sub : A' ⊆ S.erase g := Finset.mem_powerset.mp hA'
            have hg_not_A' : g ∉ A' := fun hg => (Finset.notMem_erase g S) (hA'_sub hg)
            have hins_sub : insert g A' ⊆ S :=
              Finset.insert_subset_iff.mpr ⟨hgS, hA'_sub.trans (Finset.erase_subset g S)⟩
            have hsdiff_eq : S \ insert g A' = S.erase g \ A' := by
              ext x
              simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
              tauto
            unfold retainProd
            rw [if_pos hins_sub, Finset.prod_insert hg_not_A', hsdiff_eq, mul_assoc]
          rw [Finset.sum_congr rfl h_term, ← Finset.mul_sum, ← Finset.prod_add]
          simp
        · intro A₁ hA₁ A₂ hA₂ heq
          have hg₁ : g ∉ A₁ := fun hg => (Finset.notMem_erase g S) (Finset.mem_powerset.mp hA₁ hg)
          have hg₂ : g ∉ A₂ := fun hg => (Finset.notMem_erase g S) (Finset.mem_powerset.mp hA₂ hg)
          have := congr_arg (fun X : Finset (Fin n) => X.erase g) heq
          simpa [Finset.erase_insert hg₁, Finset.erase_insert hg₂] using this
      simp_rw [h_sum_eq]
      have h_ret_g : ∀ τ : Fin n → ℝ,
          retentionProb C t S ∅ τ β g =
            ((Function.eval g) ⁻¹' Set.Iic invE).indicator
              (fun _ => Real.log (Real.exp 1 * t)) τ := by
        intro τ
        unfold retentionProb
        by_cases hτ : τ g ≤ invE
        · have hmem : τ ∈ (Function.eval g : (Fin n → ℝ) → ℝ) ⁻¹' Set.Iic invE := hτ
          rw [if_pos hτ, Set.indicator_of_mem hmem]
          have h_dt_t : deathTime C t S ∅ τ β g = t := by
            have h_set : {u : ℝ | invE ≤ u ∧ u ≤ t ∧ g ∉ C (presentSet S ∅ τ β u)} = ∅ := by
              ext u
              simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
              intro hu_lo _
              have hU_sub : presentSet S ∅ τ β u ⊆ S := by
                intro z hz
                simp [presentSet] at hz
                exact hz.1
              have hgU : g ∈ presentSet S ∅ τ β u := by
                simp [presentSet, hgS, hτ.trans hu_lo]
              exact hP (presentSet S ∅ τ β u) S hU_sub (Finset.mem_inter.mpr ⟨hgCS, hgU⟩)
            unfold deathTime
            rw [h_set, Set.empty_union, csInf_singleton]
          rw [h_dt_t]
        · have hnmem : τ ∉ (Function.eval g : (Fin n → ℝ) → ℝ) ⁻¹' Set.Iic invE := hτ
          rw [if_neg hτ, Set.indicator_of_notMem hnmem]
      simp_rw [h_ret_g]
      have hs_meas : MeasurableSet ((Function.eval g : (Fin n → ℝ) → ℝ) ⁻¹' Set.Iic invE) :=
        measurableSet_Iic.preimage (measurable_pi_apply g)
      rw [MeasureTheory.integral_indicator_const _ hs_meas, smul_eq_mul]
      have h_mp := MeasureTheory.measurePreserving_eval (fun _ : Fin n => μ₁) g
      have h_meas_eq : unifCubeMeasure n t ((Function.eval g) ⁻¹' Set.Iic invE) =
          μ₁ (Set.Iic invE) :=
        h_mp.measure_preimage measurableSet_Iic.nullMeasurableSet
      have h_inter : Set.Iic invE ∩ Set.Icc (0 : ℝ) t = Set.Icc 0 invE := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
        exact ⟨fun ⟨h1, h2, _⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, h2.trans ht_low⟩⟩
      have h_μ₁_val : μ₁ (Set.Iic invE) = (ENNReal.ofReal t)⁻¹ * ENNReal.ofReal invE := by
        simp only [μ₁, Measure.smul_apply, smul_eq_mul,
          Measure.restrict_apply measurableSet_Iic, h_inter, Real.volume_Icc, sub_zero]
      have h_real_val : (unifCubeMeasure n t).real ((Function.eval g) ⁻¹' Set.Iic invE) =
          invE / t := by
        rw [Measure.real, h_meas_eq, h_μ₁_val, ENNReal.toReal_mul, ENNReal.toReal_inv,
          ENNReal.toReal_ofReal ht_pos.le, ENNReal.toReal_ofReal h_invE_pos.le, div_eq_inv_mul]
      rw [h_real_val, h_invE_eq]
      have hexp_ne : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
      have ht_ne : t ≠ 0 := ht_pos.ne'
      field_simp

  · 
    intro n C t S B x A τ β _ hP hSD ht_low ht_high _ hxSB hA
    dsimp only
    have hxB : x ∉ B := fun hb => hxSB (Finset.mem_union_right S hb)
    have h_part1 := h_clamp_core C S B τ β hP ht_low hxB
    refine ⟨h_part1, ?_, ?_, ?_⟩
    · intro g₁ hg₁S g₂ hg₂S hg₁_e hg₂_e hne
      rw [Set.disjoint_left]
      intro τ_tilde h₁ h₂
      obtain ⟨h_inv_a₁, _, hb₁_t, _, hd₁, _⟩ := h_part1 g₁ hg₁S hg₁_e
      obtain ⟨_, _, _, _, hd₂, _⟩ := h_part1 g₂ hg₂S hg₂_e
      have hτ_ico : τ_tilde ∈ Set.Ico invE t :=
        ⟨h_inv_a₁.trans h₁.1, h₁.2.trans_le hb₁_t⟩
      have hg₁_disp := (hd₁ τ_tilde hτ_ico).mpr h₁
      have hg₂_disp := (hd₂ τ_tilde hτ_ico).mpr h₂
      let U := presentSet S B τ β τ_tilde
      have hxU : x ∉ U := by
        intro hx_in
        simp only [U, presentSet, Finset.mem_union, Finset.mem_filter] at hx_in
        rcases hx_in with ⟨hxS, _⟩ | ⟨hxB', _⟩
        · exact hxSB (Finset.mem_union_left B hxS)
        · exact hxB hxB'
      exact hne (Finset.card_le_one.mp (hSD U x hxU) g₁ hg₁_disp g₂ hg₂_disp)
    · let L₀ : ℝ := ((A.card : ℝ) + ((S \ A).card : ℝ)) * Real.exp 1
      have hL₀_nn : 0 ≤ L₀ := by dsimp only [L₀]; positivity
      obtain ⟨hl_phi, _⟩ := h_lip_retain C S B A τ β hP ht_low ht_high hxB hA
      refine ⟨⟨L₀, hL₀_nn⟩, LipschitzOnWith.of_dist_le_mul (fun u₁ hu₁ u₂ hu₂ => ?_)⟩
      simp only [NNReal.coe_mk, Real.dist_eq]
      exact hl_phi u₁ hu₁ u₂ hu₂
    · let L₀ : ℝ := ((A.card : ℝ) + ((S \ A).card : ℝ)) * Real.exp 1
      have hL_nn : 0 ≤ 1 + L₀ := by dsimp only [L₀]; positivity
      obtain ⟨_, hl_tot⟩ := h_lip_retain C S B A τ β hP ht_low ht_high hxB hA
      refine ⟨⟨1 + L₀, hL_nn⟩, LipschitzOnWith.of_dist_le_mul (fun u₁ hu₁ u₂ hu₂ => ?_)⟩
      simp only [NNReal.coe_mk, Real.dist_eq]
      exact hl_tot u₁ hu₁ u₂ hu₂

  · 
    intro n C t τ_tilde S B x f A β hC hP hSD h_low h_high ht_one hDisj hβ hxSB hA hfSA h_disp_f
    dsimp only
    let μ_f : ℝ → ℝ := fun u =>
      genMovingProb2 C τ_tilde t (S.erase f) (insert x B) (Function.update β x τ_tilde) f A u
    let dPhi : (Fin n → ℝ) → ℝ := fun τ =>
      deriv (fun u => u * retainProd C t S (insert x B) τ (Function.update β x u) A) τ_tilde
    have ht_low : invE ≤ t := (h_low.trans h_high).le
    have hτ_pos : 0 < τ_tilde := h_invE_pos.trans h_low
    have hfS : f ∈ S := (Finset.mem_sdiff.mp hfSA).1
    have hf_notA : f ∉ A := (Finset.mem_sdiff.mp hfSA).2
    have hA_er : A ⊆ S.erase f :=
      fun z hz => Finset.mem_erase.mpr ⟨fun hzf => hf_notA (hzf ▸ hz), hA hz⟩
    have hfB : f ∉ B := Finset.disjoint_left.mp hDisj hfS
    have hxS : x ∉ S := fun hs => hxSB (Finset.mem_union_left B hs)
    have hxB : x ∉ B := fun hb => hxSB (Finset.mem_union_right S hb)
    have hfx : f ≠ x := fun h => hxS (h ▸ hfS)
    have hf_not_insB : f ∉ insert x B := by simp [hfx, hfB]
    let β_x : Fin n → ℝ := Function.update β x τ_tilde
    let G : (Fin n → ℝ) → ℝ → ℝ := fun τ' u =>
      retainProd C t (S.erase f) (insert f (insert x B)) τ' (Function.update β_x f u) A
    let Ψ : (Fin n → ℝ) → ℝ := fun τ =>
      if τ f ≤ invE then - Real.log (Real.exp 1 * τ_tilde) * G τ invE else G τ (τ f)

    
    let ν : Measure ℝ := (ENNReal.ofReal τ_tilde)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) τ_tilde)
    haveI : IsProbabilityMeasure ν := h_unif1D_prob hτ_pos
    let μ_τ : Measure (Fin n → ℝ) := unifCubeMeasure n τ_tilde
    haveI : IsProbabilityMeasure μ_τ := by dsimp only [μ_τ, unifCubeMeasure]; infer_instance
    have h_ae_lt : ∀ᵐ τ ∂μ_τ, ∀ i : Fin n, 0 ≤ τ i ∧ τ i < τ_tilde := by
      rw [Filter.eventually_all]
      intro i
      have h_inter : (Set.Ico (0 : ℝ) τ_tilde)ᶜ ∩ Set.Icc (0 : ℝ) τ_tilde = {τ_tilde} := by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_Ico, Set.mem_Icc,
          Set.mem_singleton_iff, not_and, not_lt]
        exact ⟨fun ⟨hnot, h0, hle⟩ => le_antisymm hle (hnot h0),
          fun hy => ⟨fun _ => hy.ge, hτ_pos.le.trans_eq hy.symm, hy.le⟩⟩
      have h_compl_zero : ν (Set.Ico (0 : ℝ) τ_tilde)ᶜ = 0 := by
        simp [ν, Measure.restrict_apply measurableSet_Ico.compl, h_inter]
      have h_ae_1d : ∀ᵐ y ∂ν, y ∈ Set.Ico (0 : ℝ) τ_tilde := by
        rw [ae_iff]
        exact h_compl_zero
      have h_mp := MeasureTheory.measurePreserving_eval (fun _ : Fin n => ν) i
      exact h_mp.quasiMeasurePreserving.ae h_ae_1d

    
    have h_ae_eq : dPhi =ᵐ[μ_τ] Ψ := by
      filter_upwards [h_ae_lt] with τ hτ
      have hτ_ne : ∀ g ∈ S, τ g ≠ τ_tilde := fun g _ => (hτ g).2.ne
      have hβ_ne : ∀ b ∈ B, β b ≠ τ_tilde := fun b hb => (hβ b hb).2.2
      have hU_eq : presentSet S B τ β τ_tilde = S ∪ B.filter (fun b => β b ≤ τ_tilde) := by
        unfold presentSet
        rw [Finset.filter_true_of_mem (fun g _ => (hτ g).2.le)]
      have hf_disp : f ∈ C (presentSet S B τ β τ_tilde) \
          C (insert x (presentSet S B τ β τ_tilde)) := by
        rw [hU_eq, h_disp_f]
        exact Finset.mem_singleton_self f
      have hlm := h_local_move n C t τ_tilde S B x A τ β hC hP hSD
        h_low h_high ht_one hDisj hxSB hA hτ_ne hβ_ne
      by_cases hf_early : τ f ≤ invE
      · have hd_early := hlm.2.2.2.1 f hfSA hf_early hf_disp
        dsimp only [dPhi, Ψ]
        rw [hd_early, if_pos hf_early]
        congr 1
        have h_pres_er : ∀ w : ℝ, invE ≤ w →
            presentSet S (insert x B) τ β_x w =
              presentSet (S.erase f) (insert f (insert x B)) τ (Function.update β_x f invE) w := by
          intro w hw
          have hτf_w : τ f ≤ w := hf_early.trans hw
          ext z
          by_cases hzf : z = f
          · subst hzf
            simp [presentSet, hfS, hτf_w, hw]
          · simp [presentSet, hzf]
        have h_ret_er : ∀ g : Fin n,
            retentionProb C t S (insert x B) τ β_x g =
              retentionProb C t (S.erase f) (insert f (insert x B)) τ
                (Function.update β_x f invE) g := by
          intro g
          unfold retentionProb
          split_ifs with hg_e
          · congr 1; congr 1; unfold deathTime; congr 1; congr 1; ext w
            simp only [Set.mem_setOf_eq]
            exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, by rwa [← h_pres_er w h1]⟩,
              fun ⟨h1, h2, h3⟩ => ⟨h1, h2, by rwa [h_pres_er w h1]⟩⟩
          · rfl
        have hsdiff_eq : S \ insert f A = (S.erase f) \ A := by
          ext z
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
          tauto
        dsimp only [G, retainProd, retainProdWithout]
        rw [if_pos hA_er, hsdiff_eq]
        congr 1
        · exact Finset.prod_congr rfl (fun g _ => h_ret_er g)
        · refine Finset.prod_congr rfl (fun g _ => ?_)
          rw [h_ret_er g]
      · have hf_late : invE < τ f := lt_of_not_ge hf_early
        have hd_late := hlm.2.2.2.2.2.2 f hfS hf_late hf_disp
        dsimp only [dPhi, Ψ]
        rw [hd_late, if_neg hf_early]
        have h_pres_er : ∀ w : ℝ,
            presentSet S (insert x B) τ β_x w =
              presentSet (S.erase f) (insert f (insert x B)) τ
                (Function.update β_x f (τ f)) w := by
          intro w
          ext z
          by_cases hzf : z = f
          · subst hzf
            simp [presentSet, hfS, hf_not_insB]
          · simp [presentSet, hzf]
        have h_ret_er : ∀ g : Fin n,
            retentionProb C t S (insert x B) τ β_x g =
              retentionProb C t (S.erase f) (insert f (insert x B)) τ
                (Function.update β_x f (τ f)) g := by
          intro g
          unfold retentionProb
          split_ifs with hg_e
          · congr 1; congr 1; unfold deathTime; simp_rw [h_pres_er]
          · rfl
        have hsdiff_ins : S \ A = insert f ((S.erase f) \ A) := by
          ext z
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
          by_cases hzf : z = f
          · subst hzf; simp [hfS, hf_notA]
          · simp [hzf]
        have hf_not_erA : f ∉ (S.erase f) \ A :=
          fun hm => (Finset.notMem_erase f S) (Finset.mem_sdiff.mp hm).1
        have hθf_zero : retentionProb C t S (insert x B) τ β_x f = 0 := by
          unfold retentionProb; exact if_neg hf_early
        dsimp only [G, retainProd]
        rw [if_pos hA, if_pos hA_er, hsdiff_ins, Finset.prod_insert hf_not_erA,
          hθf_zero, sub_zero, one_mul]
        congr 1
        · exact Finset.prod_congr rfl (fun g _ => h_ret_er g)
        · refine Finset.prod_congr rfl (fun g _ => ?_)
          rw [h_ret_er g]

    
    have hG_meas : Measurable (fun p : (Fin n → ℝ) × ℝ => G p.1 p.2) := by
      have hm_β : Measurable (fun p : (Fin n → ℝ) × ℝ => Function.update β_x f p.2) := by
        rw [measurable_pi_iff]
        intro z
        by_cases hzf : z = f
        · subst hzf; simpa using measurable_snd
        · simp [Function.update_of_ne hzf, measurable_const]
      exact (h_meas_prod C ht_low (S.erase f) (insert f (insert x B)) A
        Prod.fst (fun p => Function.update β_x f p.2) measurable_fst hm_β).2
    have hG_bounds : ∀ (τ' : Fin n → ℝ) (u : ℝ), 0 ≤ G τ' u ∧ G τ' u ≤ 1 :=
      fun τ' u => h_prod_bounds C ht_low ht_one (S.erase f) (insert f (insert x B)) τ' _ A
    have hG_indep : ∀ (τ₁ τ₂ : Fin n → ℝ) (u : ℝ),
        (∀ i : Fin n, i ≠ f → τ₁ i = τ₂ i) → G τ₁ u = G τ₂ u := by
      intro τ₁ τ₂ u h_eq
      have h_pr : ∀ w : ℝ,
          presentSet (S.erase f) (insert f (insert x B)) τ₁ (Function.update β_x f u) w =
            presentSet (S.erase f) (insert f (insert x B)) τ₂ (Function.update β_x f u) w := by
        intro w; unfold presentSet; congr 1
        refine Finset.filter_congr (fun s hs => ?_)
        rw [h_eq s (Finset.ne_of_mem_erase hs)]
      have h_rt : ∀ g ∈ S.erase f,
          retentionProb C t (S.erase f) (insert f (insert x B)) τ₁ (Function.update β_x f u) g =
            retentionProb C t (S.erase f) (insert f (insert x B)) τ₂ (Function.update β_x f u) g := by
        intro g hg
        unfold retentionProb
        rw [h_eq g (Finset.ne_of_mem_erase hg)]
        split_ifs
        · congr 1; congr 1; unfold deathTime; simp_rw [h_pr]
        · rfl
      dsimp only [G, retainProd]
      rw [if_pos hA_er, if_pos hA_er]
      congr 1
      · exact Finset.prod_congr rfl (fun g hg => h_rt g (hA_er hg))
      · refine Finset.prod_congr rfl (fun g hg => ?_)
        rw [h_rt g (Finset.mem_sdiff.mp hg).1]
    have hμ_cont : ContinuousOn μ_f (Set.Icc invE τ_tilde) := by
      let L₀ : ℝ := ((A.card : ℝ) + (((S.erase f) \ A).card : ℝ)) * Real.exp 1
      have hL₀_nn : 0 ≤ L₀ := by dsimp only [L₀]; positivity
      have h_int_u : ∀ u : ℝ, Integrable (fun τ' => G τ' u) μ_τ := by
        intro u
        have hm : Measurable (fun τ' => G τ' u) :=
          hG_meas.comp (measurable_id.prodMk measurable_const)
        exact MeasureTheory.Integrable.of_mem_Icc 0 1 hm.aemeasurable
          (Filter.Eventually.of_forall (fun τ' => hG_bounds τ' u))
      have h_lip_μ : LipschitzOnWith ⟨L₀, hL₀_nn⟩ μ_f (Set.Icc invE τ_tilde) := by
        refine LipschitzOnWith.of_dist_le_mul (fun u₁ hu₁ u₂ hu₂ => ?_)
        simp only [NNReal.coe_mk, Real.dist_eq, μ_f, genMovingProb2, genSurvivalLaw2]
        change |(∫ τ', G τ' u₁ ∂μ_τ) - (∫ τ', G τ' u₂ ∂μ_τ)| ≤ L₀ * |u₁ - u₂|
        rw [← MeasureTheory.integral_sub (h_int_u u₁) (h_int_u u₂)]
        have hu₁_t : u₁ ∈ Set.Icc invE t := ⟨hu₁.1, hu₁.2.trans h_high.le⟩
        have hu₂_t : u₂ ∈ Set.Icc invE t := ⟨hu₂.1, hu₂.2.trans h_high.le⟩
        calc |∫ τ', (G τ' u₁ - G τ' u₂) ∂μ_τ|
            ≤ ∫ τ', |G τ' u₁ - G τ' u₂| ∂μ_τ := abs_integral_le_integral_abs
          _ ≤ ∫ _τ', (L₀ * |u₁ - u₂|) ∂μ_τ := by
              refine integral_mono ((h_int_u u₁).sub (h_int_u u₂)).abs (integrable_const _) ?_
              intro τ'
              exact (h_lip_retain C (S.erase f) (insert x B) A τ' β_x
                hP ht_low ht_one hf_not_insB hA_er).1 u₁ hu₁_t u₂ hu₂_t
          _ = L₀ * |u₁ - u₂| := by simp [MeasureTheory.integral_const]
      exact h_lip_μ.continuousOn

    
    obtain ⟨pred, hpred⟩ : ∃ pred : Fin n → Prop, ∀ i, pred i ↔ i = f :=
      ⟨fun i => i = f, fun _ => Iff.rfl⟩
    let f_sub : {i : Fin n // pred i} := ⟨f, (hpred f).mpr rfl⟩
    let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) pred
    let μ_in : Measure ({i : Fin n // pred i} → ℝ) := Measure.pi (fun _ => ν)
    let μ_out : Measure ({i : Fin n // ¬ pred i} → ℝ) := Measure.pi (fun _ => ν)
    haveI : IsProbabilityMeasure μ_in := by dsimp only [μ_in]; infer_instance
    haveI : IsProbabilityMeasure μ_out := by dsimp only [μ_out]; infer_instance
    have h_mp : MeasurePreserving e.symm (μ_in.prod μ_out) μ_τ :=
      (MeasureTheory.measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => ν) pred).symm e
    have h_symm_f : ∀ (x_in : {i // pred i} → ℝ) (z : {i // ¬ pred i} → ℝ),
        e.symm (x_in, z) f = x_in f_sub :=
      fun x_in z => (Equiv.piEquivPiSubtypeProd_symm_apply pred (fun _ : Fin n => ℝ) (x_in, z) f).trans
        (dif_pos ((hpred f).mpr rfl))
    have h_symm_out : ∀ (x₁ x₂ : {i // pred i} → ℝ) (z : {i // ¬ pred i} → ℝ) (i : Fin n),
        i ≠ f → e.symm (x₁, z) i = e.symm (x₂, z) i := by
      intro x₁ x₂ z i hif
      have hnp : ¬ pred i := mt (hpred i).mp hif
      have h1 := (Equiv.piEquivPiSubtypeProd_symm_apply pred (fun _ : Fin n => ℝ) (x₁, z) i).trans
        (dif_neg hnp)
      have h2 := (Equiv.piEquivPiSubtypeProd_symm_apply pred (fun _ : Fin n => ℝ) (x₂, z) i).trans
        (dif_neg hnp)
      exact h1.trans h2.symm
    have h_μf_out : ∀ u : ℝ, μ_f u = ∫ z, G (e.symm (0, z)) u ∂μ_out := by
      intro u
      change (∫ τ', G τ' u ∂μ_τ) = _
      rw [← h_mp.integral_comp' (fun τ' => G τ' u)]
      have h_fn : (fun q : ({i // pred i} → ℝ) × ({i // ¬ pred i} → ℝ) => G (e.symm q) u) =
          fun q => G (e.symm (0, q.2)) u :=
        funext (fun ⟨x_in, z⟩ => hG_indep _ _ u (h_symm_out x_in 0 z))
      rw [h_fn]
      have h_sl_meas : Measurable (fun q : ({i // pred i} → ℝ) × ({i // ¬ pred i} → ℝ) =>
          G (e.symm (0, q.2)) u) :=
        hG_meas.comp ((e.symm.measurable.comp (measurable_const.prodMk measurable_snd)).prodMk
          measurable_const)
      have h_sl_int : Integrable (fun q => G (e.symm (0, q.2)) u) (μ_in.prod μ_out) :=
        MeasureTheory.Integrable.of_mem_Icc 0 1 h_sl_meas.aemeasurable
          (Filter.Eventually.of_forall (fun q => hG_bounds _ u))
      rw [MeasureTheory.integral_prod _ h_sl_int]
      simp [MeasureTheory.integral_const]
    have hΨ_meas : Measurable Ψ := by
      refine Measurable.ite (measurableSet_le (measurable_pi_apply f) measurable_const) ?_ ?_
      · exact measurable_const.mul (hG_meas.comp (measurable_id.prodMk measurable_const))
      · exact hG_meas.comp (measurable_id.prodMk (measurable_pi_apply f))
    have hΨ_bdd : ∀ τ : Fin n → ℝ, |Ψ τ| ≤ 1 := by
      intro τ
      dsimp only [Ψ]
      split_ifs
      · obtain ⟨hg0, hg1⟩ := hG_bounds τ invE
        have hlog_lo : 0 ≤ Real.log (Real.exp 1 * τ_tilde) := by
          refine Real.log_nonneg ?_
          calc (1 : ℝ) = Real.exp 1 * invE := h_exp_invE.symm
            _ ≤ Real.exp 1 * τ_tilde := mul_le_mul_of_nonneg_left h_low.le (Real.exp_pos 1).le
        have hlog_hi : Real.log (Real.exp 1 * τ_tilde) ≤ 1 := by
          calc Real.log (Real.exp 1 * τ_tilde)
              ≤ Real.log (Real.exp 1) := by
                refine Real.log_le_log (mul_pos (Real.exp_pos 1) hτ_pos) ?_
                calc Real.exp 1 * τ_tilde ≤ Real.exp 1 * 1 :=
                    mul_le_mul_of_nonneg_left (h_high.le.trans ht_one) (Real.exp_pos 1).le
                  _ = Real.exp 1 := mul_one _
            _ = 1 := Real.log_exp 1
        rw [abs_mul, abs_neg, abs_of_nonneg hlog_lo, abs_of_nonneg hg0]
        exact mul_le_one₀ hlog_hi hg0 hg1
      · obtain ⟨hg0, hg1⟩ := hG_bounds τ (τ f)
        rw [abs_of_nonneg hg0]
        exact hg1
    let g1d : ℝ → ℝ := fun u =>
      if u ≤ invE then - Real.log (Real.exp 1 * τ_tilde) * μ_f invE else μ_f u
    have hg_eq1 : Set.EqOn g1d (fun _ => - Real.log (Real.exp 1 * τ_tilde) * μ_f invE)
        (Set.Icc 0 invE) := fun u hu => if_pos hu.2
    have hg_eq2 : Set.EqOn g1d μ_f (Set.Ioc invE τ_tilde) :=
      fun u hu => if_neg (not_le.mpr hu.1)
    have hint1 : IntegrableOn g1d (Set.Icc 0 invE) volume :=
      (integrableOn_const (hs := measure_Icc_lt_top.ne)).congr_fun hg_eq1.symm measurableSet_Icc
    have hint2 : IntegrableOn g1d (Set.Ioc invE τ_tilde) volume :=
      (hμ_cont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).congr_fun
        hg_eq2.symm measurableSet_Ioc
    have h_union : Set.Icc (0 : ℝ) τ_tilde = Set.Icc 0 invE ∪ Set.Ioc invE τ_tilde :=
      (Set.Icc_union_Ioc_eq_Icc h_invE_pos.le h_low.le).symm
    have hg1d_int_vol : IntegrableOn g1d (Set.Icc 0 τ_tilde) volume := by
      rw [h_union]
      exact hint1.union hint2
    have hg1d_int_ν : Integrable g1d ν :=
      hg1d_int_vol.integrable.smul_measure
        (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hτ_pos).ne')

    have h_fub : (∫ τ, dPhi τ ∂μ_τ) = ∫ u, g1d u ∂ν := by
      rw [MeasureTheory.integral_congr_ae h_ae_eq, ← h_mp.integral_comp' Ψ]
      have hΨ_comp_meas : Measurable (fun q => Ψ (e.symm q)) := hΨ_meas.comp e.symm.measurable
      have hΨ_comp_int : Integrable (fun q => Ψ (e.symm q)) (μ_in.prod μ_out) :=
        MeasureTheory.Integrable.of_mem_Icc (-1) 1 hΨ_comp_meas.aemeasurable
          (Filter.Eventually.of_forall (fun q => abs_le.mp (hΨ_bdd (e.symm q))))
      rw [MeasureTheory.integral_prod _ hΨ_comp_int]
      have h_inner : ∀ x_in : {i // pred i} → ℝ,
          (∫ z, Ψ (e.symm (x_in, z)) ∂μ_out) = g1d (x_in f_sub) := by
        intro x_in
        by_cases hx_le : x_in f_sub ≤ invE
        · have h_fn : (fun z => Ψ (e.symm (x_in, z))) =
              fun z => - Real.log (Real.exp 1 * τ_tilde) * G (e.symm (0, z)) invE := by
            ext z
            dsimp only [Ψ]
            rw [h_symm_f x_in z, if_pos hx_le, hG_indep _ _ invE (h_symm_out x_in 0 z)]
          rw [h_fn, integral_const_mul, ← h_μf_out invE]
          dsimp only [g1d]
          rw [if_pos hx_le]
        · have h_fn : (fun z => Ψ (e.symm (x_in, z))) =
              fun z => G (e.symm (0, z)) (x_in f_sub) := by
            ext z
            dsimp only [Ψ]
            rw [h_symm_f x_in z, if_neg hx_le, hG_indep _ _ (x_in f_sub) (h_symm_out x_in 0 z)]
          rw [h_fn, ← h_μf_out (x_in f_sub)]
          dsimp only [g1d]
          rw [if_neg hx_le]
      simp_rw [h_inner]
      have h_mp_f : MeasurePreserving (Function.eval f_sub) μ_in ν :=
        MeasureTheory.measurePreserving_eval (fun _ : {i // pred i} => ν) f_sub
      conv_rhs => rw [← h_mp_f.map_eq]
      exact (integral_map h_mp_f.measurable.aemeasurable
        (by rw [h_mp_f.map_eq]; exact hg1d_int_ν.aestronglyMeasurable)).symm

    
    have h_id1 : (∫ τ, dPhi τ ∂μ_τ) =
        (1 / τ_tilde) * (∫ τ_f in Set.Icc invE τ_tilde, μ_f τ_f) -
          (Real.log (Real.exp 1 * τ_tilde) / (Real.exp 1 * τ_tilde)) * μ_f invE := by
      have h_disj : Disjoint (Set.Icc (0 : ℝ) invE) (Set.Ioc invE τ_tilde) :=
        Set.disjoint_left.mpr (fun _ h1 h2 => not_lt_of_ge h1.2 h2.1)
      rw [h_fub]
      dsimp only [ν]
      rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv,
        ENNReal.toReal_ofReal hτ_pos.le, h_union,
        setIntegral_union h_disj measurableSet_Ioc hint1 hint2,
        setIntegral_congr_fun measurableSet_Icc hg_eq1,
        setIntegral_congr_fun measurableSet_Ioc hg_eq2,
        setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le h_invE_pos.le, sub_zero,
        ← MeasureTheory.integral_Icc_eq_integral_Ioc]
      rw [h_invE_eq]
      have hexp_ne : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
      have hτ_ne : τ_tilde ≠ 0 := hτ_pos.ne'
      field_simp
      ring

    
    have h_id2 : (∫ τ, dPhi τ ∂μ_τ) =
        (1 / τ_tilde) * (∫ τ_f in Set.Icc invE τ_tilde,
          (μ_f τ_f - μ_f invE / (Real.exp 1 * τ_f))) := by
      let H_prim : ℝ → ℝ := fun u => invE * Real.log (Real.exp 1 * u) * μ_f invE
      let H_deriv : ℝ → ℝ := fun u => μ_f invE / (Real.exp 1 * u)
      have hH_cont : ContinuousOn H_prim (Set.Icc invE τ_tilde) := by
        refine (continuousOn_const.mul ?_).mul continuousOn_const
        refine ContinuousOn.log (continuousOn_const.mul continuousOn_id) (fun u hu => ?_)
        exact (mul_pos (Real.exp_pos 1) (h_invE_pos.trans_le hu.1)).ne'
      have hH_deriv_cont : ContinuousOn H_deriv (Set.Icc invE τ_tilde) := by
        refine continuousOn_const.div (continuousOn_const.mul continuousOn_id) (fun u hu => ?_)
        exact (mul_pos (Real.exp_pos 1) (h_invE_pos.trans_le hu.1)).ne'
      have hH_hasDeriv : ∀ u ∈ Set.Ioo invE τ_tilde, HasDerivAt H_prim (H_deriv u) u := by
        intro u hu
        have hu_pos : 0 < u := h_invE_pos.trans hu.1
        have hexp_ne : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
        have h1 : HasDerivAt (fun y : ℝ => Real.exp 1 * y) (Real.exp 1 * 1) u :=
          (hasDerivAt_id u).const_mul (Real.exp 1)
        have h2 := (Real.hasDerivAt_log (mul_ne_zero hexp_ne hu_pos.ne')).comp u h1
        have h3 := (h2.const_mul invE).mul_const (μ_f invE)
        have heq : invE * ((Real.exp 1 * u)⁻¹ * (Real.exp 1 * 1)) * μ_f invE =
            μ_f invE / (Real.exp 1 * u) := by
          rw [h_invE_eq]; have := hu_pos.ne'; field_simp
        dsimp only [H_deriv]
        rw [← heq]
        exact h3
      have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h_low.le
        hH_cont hH_hasDeriv (hH_deriv_cont.intervalIntegrable_of_Icc h_low.le)
      have hH_lo : H_prim invE = 0 := by
        dsimp only [H_prim]
        rw [h_exp_invE, Real.log_one, mul_zero, zero_mul]
      rw [hH_lo, sub_zero, intervalIntegral.integral_of_le h_low.le,
        ← MeasureTheory.integral_Icc_eq_integral_Ioc] at h_ftc
      have h_sub_int := MeasureTheory.integral_sub
        (μ := volume.restrict (Set.Icc invE τ_tilde))
        hμ_cont.integrableOn_Icc hH_deriv_cont.integrableOn_Icc
      dsimp only [H_deriv] at h_sub_int h_ftc
      rw [h_id1, h_sub_int, h_ftc]
      dsimp only [H_prim]
      rw [h_invE_eq]
      have hexp_ne : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
      have hτ_ne : τ_tilde ≠ 0 := hτ_pos.ne'
      field_simp

    exact ⟨h_id1, h_id2⟩


end Internal

/-- **Section 3.2 (`sec:survival`) & Appendix B.1 (`sec:delay`) — Two-Time Survival Thought Experiment**:
For any persistent choice rule `C` and times `1/e ≤ t₀ ≤ t ≤ 1`:
1. `0 ≤ ϕ_τ(A) ≤ 1` and `∑_{A ⊆ S} ϕ_τ(A) = 1`;
2. `ϕ_τ(A) > 0 ⟹ A ⊆ C(U_{1/e}) ∩ S`;
3. `genSurvivalLaw2 C (1/e) (1/e) S B β A = [A = ∅]`;
4. for `g ∈ C(S)` at `t₀ = t, B = ∅`, `P[g ∈ R] = ln(e t) / (e t)`. -/
theorem genSurvivalLaw2_spec
    {n : ℕ} (C : Finset (Fin n) → Finset (Fin n)) (t₀ t : ℝ)
    (S B : Finset (Fin n)) (β : Fin n → ℝ)
    (hC : IsChoiceRule C) (hP : HasPersistence C)
    (ht₀ : invE ≤ t₀) (ht₀t : t₀ ≤ t) (ht1 : t ≤ 1) :
    (∀ τ A, 0 ≤ retainProd C t S B τ β A ∧ retainProd C t S B τ β A ≤ 1) ∧
    (∀ τ, (∑ A ∈ S.powerset, retainProd C t S B τ β A) = 1) ∧
    (∀ τ A, 0 < retainProd C t S B τ β A → A ⊆ C (presentSet S B τ β invE) ∩ S) ∧
    (∀ A, genSurvivalLaw2 C invE invE S B β A = (if A = ∅ then 1 else 0)) ∧
    (∀ g ∈ C S,
      (∑ A ∈ S.powerset.filter (fun A => g ∈ A), genSurvivalLaw C t S ∅ β A) =
        Real.log (Real.exp 1 * t) / (Real.exp 1 * t)) :=
  Internal.thm_selection_clamp_local_move_and_payment.1 n C t₀ t S B β hC hP ht₀ ht₀t ht1

/-- **Lemma B.2 (`lem:clamp`) — General Persistent Single-Displacement Choice Rules**:
Explicit clamp formula `σ_g(τ̃) = min (max τ̃ a_g) b_g`, displacement interval equivalence
`g ∈ C(U_{τ̃}) \ C(U_{τ̃} + x) ↔ a_g ≤ τ̃ < b_g` on `[1/e, t)`, disjointness of `[a_g, b_g)`
across distinct early items, `1`-Lipschitzness of `σ_g`, and Lipschitzness of `ϕ_τ` and
`τ̃ ↦ τ̃ ϕ_τ(τ̃)`. -/
theorem lem_B_2_clamp_choice_rule
    {n : ℕ} (C : Finset (Fin n) → Finset (Fin n)) (t : ℝ)
    (S B : Finset (Fin n)) (x : Fin n) (A : Finset (Fin n)) (τ β : Fin n → ℝ)
    (hC : IsChoiceRule C) (hP : HasPersistence C) (hSD : HasSingleDisplacement C)
    (ht₀ : invE ≤ t) (ht1 : t ≤ 1) (hSB : Disjoint S B) (hx : x ∉ S ∪ B) (hAS : A ⊆ S) :
    let σ := fun g u => deathTime C t S (insert x B) τ (Function.update β x u) g
    (∀ g ∈ S, τ g ≤ invE →
      let a_g := σ g invE
      let b_g := σ g t
      invE ≤ a_g ∧ a_g ≤ b_g ∧ b_g ≤ t ∧
      (∀ τ_tilde ∈ Set.Icc invE t, σ g τ_tilde = min (max τ_tilde a_g) b_g) ∧
      (∀ τ_tilde ∈ Set.Ico invE t,
        let U := presentSet S B τ β τ_tilde
        g ∈ C U \ C (insert x U) ↔ a_g ≤ τ_tilde ∧ τ_tilde < b_g) ∧
      LipschitzOnWith 1 (σ g) (Set.Icc invE t)) ∧
    (∀ g₁ ∈ S, ∀ g₂ ∈ S, τ g₁ ≤ invE → τ g₂ ≤ invE → g₁ ≠ g₂ →
      Disjoint (Set.Ico (σ g₁ invE) (σ g₁ t)) (Set.Ico (σ g₂ invE) (σ g₂ t))) ∧
    (∃ K₀ : NNReal,
      LipschitzOnWith K₀
        (fun u => retainProd C t S (insert x B) τ (Function.update β x u) A)
        (Set.Icc invE t)) ∧
    (∃ K : NNReal,
      LipschitzOnWith K
        (fun u => u * retainProd C t S (insert x B) τ (Function.update β x u) A)
        (Set.Icc invE t)) :=
  Internal.thm_selection_clamp_local_move_and_payment.2.1 n C t S B x A τ β
    hC hP hSD ht₀ ht1 hSB hx hAS

/-- **Lemma B.2 (`lem:clamp`) — Gross Substitutes Canonical Demands `D_v`**:
Specializes `lem_B_2_clamp_choice_rule` to `D_v` (`canonicalDemand v`) for any GS valuation `v`. -/
theorem lem_B_2_clamp
    {n : ℕ} (v : ItemValuation n) (t : ℝ)
    (S B : Finset (Fin n)) (x : Fin n) (A : Finset (Fin n)) (τ β : Fin n → ℝ)
    (hv : IsGSValuation v)
    (ht₀ : invE ≤ t) (ht1 : t ≤ 1) (hSB : Disjoint S B) (hx : x ∉ S ∪ B) (hAS : A ⊆ S) :
    let C := canonicalDemand v
    let σ := fun g u => deathTime C t S (insert x B) τ (Function.update β x u) g
    (∀ g ∈ S, τ g ≤ invE →
      let a_g := σ g invE
      let b_g := σ g t
      invE ≤ a_g ∧ a_g ≤ b_g ∧ b_g ≤ t ∧
      (∀ τ_tilde ∈ Set.Icc invE t, σ g τ_tilde = min (max τ_tilde a_g) b_g) ∧
      (∀ τ_tilde ∈ Set.Ico invE t,
        let U := presentSet S B τ β τ_tilde
        g ∈ C U \ C (insert x U) ↔ a_g ≤ τ_tilde ∧ τ_tilde < b_g) ∧
      LipschitzOnWith 1 (σ g) (Set.Icc invE t)) ∧
    (∀ g₁ ∈ S, ∀ g₂ ∈ S, τ g₁ ≤ invE → τ g₂ ≤ invE → g₁ ≠ g₂ →
      Disjoint (Set.Ico (σ g₁ invE) (σ g₁ t)) (Set.Ico (σ g₂ invE) (σ g₂ t))) ∧
    (∃ K₀ : NNReal,
      LipschitzOnWith K₀
        (fun u => retainProd C t S (insert x B) τ (Function.update β x u) A)
        (Set.Icc invE t)) ∧
    (∃ K : NNReal,
      LipschitzOnWith K
        (fun u => u * retainProd C t S (insert x B) τ (Function.update β x u) A)
        (Set.Icc invE t)) :=
  lem_B_2_clamp_choice_rule (canonicalDemand v) t S B x A τ β
    (lem_2_7_persistence v hv).1 (lem_2_7_persistence v hv).2 (lem_2_7_single_displacement v hv)
    ht₀ ht1 hSB hx hAS

/-- **Lemma B.3 (`lem:local-move`) — General Persistent Single-Displacement Choice Rules**:
Differentiability and exact derivative formula `(eq:pointwise)` for `(τ̃ ϕ_τ(τ̃))'` off timestamps. -/
theorem lem_B_3_local_move_choice_rule
    {n : ℕ} (C : Finset (Fin n) → Finset (Fin n)) (t τ_tilde : ℝ)
    (S B : Finset (Fin n)) (x : Fin n) (A : Finset (Fin n)) (τ β : Fin n → ℝ)
    (hC : IsChoiceRule C) (hP : HasPersistence C) (hSD : HasSingleDisplacement C)
    (hlo : invE < τ_tilde) (hhi : τ_tilde < t) (ht1 : t ≤ 1)
    (hSB : Disjoint S B) (hx : x ∉ S ∪ B) (hAS : A ⊆ S)
    (hτ : ∀ g ∈ S, τ g ≠ τ_tilde) (hβ : ∀ b ∈ B, β b ≠ τ_tilde) :
    let U := presentSet S B τ β τ_tilde
    let φ := fun u => retainProd C t S (insert x B) τ (Function.update β x u) A
    let φ_no := fun f =>
      retainProdWithout C t S (insert x B) τ (Function.update β x τ_tilde) A f
    DifferentiableAt ℝ φ τ_tilde ∧
    DifferentiableAt ℝ (fun u => u * φ u) τ_tilde ∧
    |deriv (fun u => u * φ u) τ_tilde| ≤ 2 ∧
    (∀ f ∈ S \ A, τ f ≤ invE → f ∈ C U \ C (insert x U) →
      deriv (fun u => u * φ u) τ_tilde =
        - Real.log (Real.exp 1 * τ_tilde) * φ_no f) ∧
    ((¬ ∃ f ∈ S \ A, τ f ≤ invE ∧ f ∈ C U \ C (insert x U)) →
      φ τ_tilde ≤ deriv (fun u => u * φ u) τ_tilde) ∧
    ((¬ ∃ f ∈ S, τ f ≤ invE ∧ f ∈ C U \ C (insert x U)) →
      deriv (fun u => u * φ u) τ_tilde = φ τ_tilde) ∧
    (∀ f ∈ S, invE < τ f → f ∈ C U \ C (insert x U) →
      deriv (fun u => u * φ u) τ_tilde = φ τ_tilde) :=
  Internal.thm_selection_clamp_local_move_and_payment.2.2.1 n C t τ_tilde S B x A τ β
    hC hP hSD hlo hhi ht1 hSB hx hAS hτ hβ

/-- **Lemma B.3 (`lem:local-move`) — Gross Substitutes Canonical Demands `D_v`**:
Specializes `lem_B_3_local_move_choice_rule` to `D_v` (`canonicalDemand v`). -/
theorem lem_B_3_local_move
    {n : ℕ} (v : ItemValuation n) (t τ_tilde : ℝ)
    (S B : Finset (Fin n)) (x : Fin n) (A : Finset (Fin n)) (τ β : Fin n → ℝ)
    (hv : IsGSValuation v)
    (hlo : invE < τ_tilde) (hhi : τ_tilde < t) (ht1 : t ≤ 1)
    (hSB : Disjoint S B) (hx : x ∉ S ∪ B) (hAS : A ⊆ S)
    (hτ : ∀ g ∈ S, τ g ≠ τ_tilde) (hβ : ∀ b ∈ B, β b ≠ τ_tilde) :
    let C := canonicalDemand v
    let U := presentSet S B τ β τ_tilde
    let φ := fun u => retainProd C t S (insert x B) τ (Function.update β x u) A
    let φ_no := fun f =>
      retainProdWithout C t S (insert x B) τ (Function.update β x τ_tilde) A f
    DifferentiableAt ℝ φ τ_tilde ∧
    DifferentiableAt ℝ (fun u => u * φ u) τ_tilde ∧
    |deriv (fun u => u * φ u) τ_tilde| ≤ 2 ∧
    (∀ f ∈ S \ A, τ f ≤ invE → f ∈ C U \ C (insert x U) →
      deriv (fun u => u * φ u) τ_tilde =
        - Real.log (Real.exp 1 * τ_tilde) * φ_no f) ∧
    ((¬ ∃ f ∈ S \ A, τ f ≤ invE ∧ f ∈ C U \ C (insert x U)) →
      φ τ_tilde ≤ deriv (fun u => u * φ u) τ_tilde) ∧
    ((¬ ∃ f ∈ S, τ f ≤ invE ∧ f ∈ C U \ C (insert x U)) →
      deriv (fun u => u * φ u) τ_tilde = φ τ_tilde) ∧
    (∀ f ∈ S, invE < τ f → f ∈ C U \ C (insert x U) →
      deriv (fun u => u * φ u) τ_tilde = φ τ_tilde) :=
  lem_B_3_local_move_choice_rule (canonicalDemand v) t τ_tilde S B x A τ β
    (lem_2_7_persistence v hv).1 (lem_2_7_persistence v hv).2 (lem_2_7_single_displacement v hv)
    hlo hhi ht1 hSB hx hAS hτ hβ

/-- **Lemma B.4 (`lem:payment`) — Cost and Repayment (General Choice Rules)**:
Integral identity `(eq:payment)` expressing `E[(τ̃ ϕ_τ(τ̃))']` under `Unif([0, τ̃])^S` in terms of
the smaller experiment `μ̃_f` on `[1/e, τ̃]`. -/
theorem lem_B_4_payment_choice_rule
    {n : ℕ} (C : Finset (Fin n) → Finset (Fin n)) (t τ_tilde : ℝ)
    (S B : Finset (Fin n)) (x f : Fin n) (A : Finset (Fin n)) (β : Fin n → ℝ)
    (hC : IsChoiceRule C) (hP : HasPersistence C) (hSD : HasSingleDisplacement C)
    (hlo : invE < τ_tilde) (hhi : τ_tilde < t) (ht1 : t ≤ 1)
    (hSB : Disjoint S B) (hβ : ∀ b ∈ B, invE ≤ β b ∧ β b ≤ t ∧ β b ≠ τ_tilde)
    (hx : x ∉ S ∪ B) (hAS : A ⊆ S) (hf : f ∈ S \ A)
    (hdisp : C (S ∪ B.filter (fun b => β b ≤ τ_tilde)) \
      C (insert x (S ∪ B.filter (fun b => β b ≤ τ_tilde))) = {f}) :
    let μ_f : ℝ → ℝ := fun u =>
      genMovingProb2 C τ_tilde t (S.erase f) (insert x B) (Function.update β x τ_tilde) f A u
    let dPhi : (Fin n → ℝ) → ℝ := fun τ =>
      deriv (fun u => u * retainProd C t S (insert x B) τ (Function.update β x u) A) τ_tilde
    (∫ τ, dPhi τ ∂(unifCubeMeasure n τ_tilde)) =
      (1 / τ_tilde) * (∫ τ_f in Set.Icc invE τ_tilde, μ_f τ_f) -
        (Real.log (Real.exp 1 * τ_tilde) / (Real.exp 1 * τ_tilde)) * μ_f invE ∧
    (∫ τ, dPhi τ ∂(unifCubeMeasure n τ_tilde)) =
      (1 / τ_tilde) * (∫ τ_f in Set.Icc invE τ_tilde,
        (μ_f τ_f - μ_f invE / (Real.exp 1 * τ_f))) :=
  Internal.thm_selection_clamp_local_move_and_payment.2.2.2 n C t τ_tilde S B x f A β
    hC hP hSD hlo hhi ht1 hSB hβ hx hAS hf hdisp

/-- **Lemma B.4 (`lem:payment`) — Cost and Repayment for Gross Substitutes `D_v`**:
Specializes `lem_B_4_payment_choice_rule` to `D_v` (`canonicalDemand v`). -/
theorem lem_B_4_payment
    {n : ℕ} (v : ItemValuation n) (t τ_tilde : ℝ)
    (S B : Finset (Fin n)) (x f : Fin n) (A : Finset (Fin n)) (β : Fin n → ℝ)
    (hv : IsGSValuation v)
    (hlo : invE < τ_tilde) (hhi : τ_tilde < t) (ht1 : t ≤ 1)
    (hSB : Disjoint S B) (hβ : ∀ b ∈ B, invE ≤ β b ∧ β b ≤ t ∧ β b ≠ τ_tilde)
    (hx : x ∉ S ∪ B) (hAS : A ⊆ S) (hf : f ∈ S \ A)
    (hdisp : canonicalDemand v (S ∪ B.filter (fun b => β b ≤ τ_tilde)) \
      canonicalDemand v (insert x (S ∪ B.filter (fun b => β b ≤ τ_tilde))) = {f}) :
    let C := canonicalDemand v
    let μ_f : ℝ → ℝ := fun u =>
      genMovingProb2 C τ_tilde t (S.erase f) (insert x B) (Function.update β x τ_tilde) f A u
    let dPhi : (Fin n → ℝ) → ℝ := fun τ =>
      deriv (fun u => u * retainProd C t S (insert x B) τ (Function.update β x u) A) τ_tilde
    (∫ τ, dPhi τ ∂(unifCubeMeasure n τ_tilde)) =
      (1 / τ_tilde) * (∫ τ_f in Set.Icc invE τ_tilde, μ_f τ_f) -
        (Real.log (Real.exp 1 * τ_tilde) / (Real.exp 1 * τ_tilde)) * μ_f invE ∧
    (∫ τ, dPhi τ ∂(unifCubeMeasure n τ_tilde)) =
      (1 / τ_tilde) * (∫ τ_f in Set.Icc invE τ_tilde,
        (μ_f τ_f - μ_f invE / (Real.exp 1 * τ_f))) :=
  lem_B_4_payment_choice_rule (canonicalDemand v) t τ_tilde S B x f A β
    (lem_2_7_persistence v hv).1 (lem_2_7_persistence v hv).2 (lem_2_7_single_displacement v hv)
    hlo hhi ht1 hSB hβ hx hAS hf hdisp

end

end GrossSubstitutesWelfare
