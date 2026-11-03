import GrossSubstitutesWelfare.Defs
import GrossSubstitutesWelfare.Preliminaries.ExchangeAndDemand
import GrossSubstitutesWelfare.Preliminaries.SafeSupportAndCutoff
import GrossSubstitutesWelfare.Selection.ClampAndPayment
import GrossSubstitutesWelfare.Selection.DelayAndComparison
import GrossSubstitutesWelfare.Selection.DistributionMatching

set_option maxHeartbeats 4000000
set_option linter.all false
set_option Elab.async true

/-!
# Section 1.1 Theorem A & Section 3 Theorem 3.1: `1 / e`-Competitive Online Selection

This file formalizes Theorem A (`thm:A`) and Theorem 3.1 (`thm:selection`) of *Gross Substitutes
Welfare in Random Order*: the non-clairvoyant survival algorithm accepts every item of the optimal
canonical demand `D_v(N)` with exact probability `1 / e`, maintains `A_k ⊆ D_v(T)` (hence feasible
with `v(Y) ≥ 0` for all `Y ⊆ A_k`) at every arrival step, and obtains `E[v(A)] ≥ OPT(v) / e`.
-/

namespace GrossSubstitutesWelfare

open Classical MeasureTheory

noncomputable section

namespace GSSelectionInternal

def clamp01 (u : ℝ) : ℝ := min 1 (max 0 u)

def sortedClampedList {n : ℕ} (rawTimes : Fin n → ℝ) : List (Fin n) :=
  (List.finRange n).mergeSort (fun a b => decide (clamp01 (rawTimes a) ≤ clamp01 (rawTimes b)))

def sortedClampedTime {n : ℕ} (rawTimes : Fin n → ℝ) (idx : Fin n) : ℝ :=
  clamp01 (rawTimes ((sortedClampedList rawTimes)[idx.1]'(by
    rw [sortedClampedList, List.length_mergeSort, List.length_finRange]
    exact idx.2)))

def localVal {n : ℕ} (prev : List (Fin n)) (x : Fin n)
    (oracle : {T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → WithBot ℝ) :
    ItemValuation n :=
  fun T => if h : T ⊆ insert x prev.toFinset then oracle ⟨T, h⟩ else ⊥

def gsOnlineSelectionStep {n : ℕ} (ω : (Fin n → ℝ) × (Fin n → ℝ))
    (prev : List (Fin n)) (x : Fin n) (accepted : Finset (Fin n))
    (oracle : {T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → WithBot ℝ) : Bool :=
  if hk : prev.length < n then
    let idx : Fin n := ⟨prev.length, hk⟩
    let t := sortedClampedTime ω.1 idx
    let v_loc := localVal prev x oracle
    let α := survivalAcceptProb v_loc x accepted prev.toFinset t
    decide (0 ≤ ω.2 idx ∧ ω.2 idx < α)
  else false

def gsDetAlg {n : ℕ} (ω : (Fin n → ℝ) × (Fin n → ℝ)) : DetSelectionAlg n :=
  { step := gsOnlineSelectionStep ω }


theorem survival_accept_bounds_and_support (n : ℕ) (v : ItemValuation n) (hv : IsGSValuation v) :
    (∀ (x : Fin n) (A S : Finset (Fin n)) (t : ℝ),
      x ∉ S → t ≤ 1 →
        0 ≤ survivalAcceptProb v x A S t ∧ survivalAcceptProb v x A S t ≤ 1) ∧
    (∀ (S A : Finset (Fin n)) (t : ℝ),
      invE ≤ t → t ≤ 1 →
        0 ≤ survivalLaw v S t A ∧
        (0 < survivalLaw v S t A → ∃ T ⊆ S, A ⊆ canonicalDemand v T)) ∧
    (∀ (T Y : Finset (Fin n)), Y ⊆ canonicalDemand v T → v Y ≠ ⊥ ∧ 0 ≤ realVal v Y) ∧
    (∀ (S : Finset (Fin n)) (x : Fin n),
      x ∉ S → x ∈ canonicalDemand v (insert x S) →
        IsGSValuation (contractVal v x) ∧
        ∀ T ⊆ S,
          x ∈ canonicalDemand v (insert x T) ∧
          canonicalDemand (contractVal v x) T = (canonicalDemand v (insert x T)).erase x) := by
  refine ⟨fun x A S t hxS ht1 => (survivalAcceptProb_valid v S x t A hv hxS ht1).1, ?_,
    fun T Y hY => (lem_2_10_safe_b v T hv).1 Y hY,
    fun S x hxS hxD => ⟨(lem_2_9_contract v S x hv hxS hxD).2.1,
      (lem_2_9_contract v S x hv hxS hxD).2.2⟩⟩
  intro S A t ht₀ ht1
  have hspec := genSurvivalLaw2_spec (canonicalDemand v) t t S ∅ (fun _ => t)
    (lem_2_7_persistence v hv).1 (lem_2_7_persistence v hv).2 ht₀ le_rfl ht1
  refine ⟨MeasureTheory.integral_nonneg (fun τ => (hspec.1 τ A).1), ?_⟩
  intro hpos
  obtain ⟨T, hTS, hAD, _⟩ := survival_pointwise_safe v S A t hv ht₀ ht1 hpos
  exact ⟨T, hTS, hAD⟩

theorem online_survival_law_eq_survival_law (n : ℕ) (v : ItemValuation n)
    (S : Finset (Fin n)) (hv : IsGSValuation v) :
    onlineSurvivalLaw v Finset.univ 1 S = survivalLaw v Finset.univ 1 S :=
  prop_B_6_matching v Finset.univ 1 S hv
    (by unfold invE; exact Real.exp_le_one_iff.mpr (by norm_num)) le_rfl

end GSSelectionInternal

section
open GSSelectionInternal

theorem thm_gs_selection (n : ℕ) :
    ∃ alg : OnlineSelectionAlg n,
      ∀ v : ItemValuation n, IsGSValuation v →
        (∀ (x : Fin n) (A S : Finset (Fin n)) (t : ℝ),
          x ∉ S → t ≤ 1 →
            0 ≤ survivalAcceptProb v x A S t ∧ survivalAcceptProb v x A S t ≤ 1) ∧
        (∀ S : Finset (Fin n), algSelectionProb alg v S = survivalLaw v Finset.univ 1 S) ∧
        (∀ g ∈ canonicalDemand v Finset.univ, algInclusionProb alg v g = invE) ∧
        (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
          let st := runDetSelectionSteps (alg.det ω) v π k hk
          ∃ T ⊆ st.1.toFinset,
            st.2 ⊆ canonicalDemand v T ∧
            v st.2 ≠ ⊥ ∧
            ∀ Y ⊆ st.2, v Y ≠ ⊥ ∧ 0 ≤ realVal v Y) ∧
        (((invE * optVal v : ℝ) : WithBot ℝ) ≤ expectedSelectionVal alg v) ∧
        (Finset.univ : Finset (Finset (Fin n))).card = 2 ^ n :=
by
 have gs_canonical_safe_and_contract : ∀ (n : ℕ) (v : ItemValuation n), IsGSValuation v →
       (∀ T : Finset (Fin n), canonicalDemand v T ⊆ T) ∧
       (∀ T U : Finset (Fin n), T ⊆ U → canonicalDemand v U ∩ T ⊆ canonicalDemand v T) ∧
       (∀ T Y : Finset (Fin n), Y ⊆ canonicalDemand v T → v Y ≠ ⊥ ∧ 0 ≤ realVal v Y) ∧
       (∀ (S : Finset (Fin n)) (x : Fin n),
         x ∉ S → x ∈ canonicalDemand v (insert x S) →
           IsGSValuation (contractVal v x) ∧
           ∀ T ⊆ S,
             x ∈ canonicalDemand v (insert x T) ∧
             canonicalDemand (contractVal v x) T = (canonicalDemand v (insert x T)).erase x) := by
   intro n v hv
   exact ⟨(lem_2_7_persistence v hv).1, (lem_2_7_persistence v hv).2,
     fun T Y hY => (lem_2_10_safe_b v T hv).1 Y hY,
     fun S x hxS hxD => ⟨(lem_2_9_contract v S x hv hxS hxD).2.1,
       (lem_2_9_contract v S x hv hxS hxD).2.2⟩⟩

 have H_surv : ∀ (w : ItemValuation n), IsGSValuation w →
     (∀ (x : Fin n) (A S : Finset (Fin n)) (t : ℝ),
       x ∉ S → t ≤ 1 →
         0 ≤ survivalAcceptProb w x A S t ∧ survivalAcceptProb w x A S t ≤ 1) ∧
     (∀ (S A : Finset (Fin n)) (t : ℝ),
       invE ≤ t → t ≤ 1 →
         0 ≤ survivalLaw w S t A ∧
         (0 < survivalLaw w S t A → ∃ T ⊆ S, A ⊆ canonicalDemand w T)) ∧
     (∀ (T Y : Finset (Fin n)), Y ⊆ canonicalDemand w T → w Y ≠ ⊥ ∧ 0 ≤ realVal w Y) ∧
     (∀ (S : Finset (Fin n)) (x : Fin n),
       x ∉ S → x ∈ canonicalDemand w (insert x S) →
         IsGSValuation (contractVal w x) ∧
         ∀ T ⊆ S,
           x ∈ canonicalDemand w (insert x T) ∧
           canonicalDemand (contractVal w x) T = (canonicalDemand w (insert x T)).erase x) :=
   fun w hw => survival_accept_bounds_and_support n w hw

 have h_s4 : ∃ alg : OnlineSelectionAlg n,
     ∀ v : ItemValuation n, IsGSValuation v →
       (∀ S : Finset (Fin n), algSelectionProb alg v S = onlineSurvivalLaw v Finset.univ 1 S) ∧
       (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
         let st := runDetSelectionSteps (alg.det ω) v π k hk
         ∃ T ⊆ st.1.toFinset,
           st.2 ⊆ canonicalDemand v T ∧
           v st.2 ≠ ⊥ ∧
           ∀ Y ⊆ st.2, v Y ≠ ⊥ ∧ 0 ≤ realVal v Y) := by
  have h_invE_pos : 0 < invE := by unfold invE; exact Real.exp_pos (-1)
  have h_clamp_bounds : ∀ u : ℝ, 0 ≤ clamp01 u ∧ clamp01 u ≤ 1 := fun u =>
    ⟨le_min zero_le_one (le_max_left 0 u), min_le_left 1 (max 0 u)⟩
  have h_clamp_id : ∀ {u : ℝ}, 0 ≤ u → u ≤ 1 → clamp01 u = u := by
    intro u h0 h1; unfold clamp01; rw [max_eq_right h0, min_eq_right h1]
  have h_clamp_meas : Measurable clamp01 :=
    measurable_const.min (measurable_const.max measurable_id)
  have h_t_bounds : ∀ (u : Fin n → ℝ) (idx : Fin n),
      0 ≤ sortedClampedTime u idx ∧ sortedClampedTime u idx ≤ 1 :=
    fun u idx => h_clamp_bounds _

  
  let ν₁ : Measure ℝ := (ENNReal.ofReal (1 : ℝ))⁻¹ • volume.restrict (Set.Icc (0 : ℝ) 1)
  have hν₁_eq : ν₁ = volume.restrict (Set.Icc (0 : ℝ) 1) := by simp [ν₁]
  have hν₁_prob : IsProbabilityMeasure ν₁ := by
    rw [MeasureTheory.isProbabilityMeasure_iff, hν₁_eq]
    simp [Real.volume_Icc]
  haveI : IsProbabilityMeasure ν₁ := hν₁_prob
  have h_cube_prob : ∀ {r : ℝ}, 0 < r → IsProbabilityMeasure (unifCubeMeasure n r) := by
    intro r hr
    unfold unifCubeMeasure
    have h1 : IsProbabilityMeasure
        ((ENNReal.ofReal r)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) r)) := by
      rw [MeasureTheory.isProbabilityMeasure_iff]
      simp only [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul, Real.volume_Icc,
        sub_zero]
      exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top
    haveI : ∀ _ : Fin n, IsProbabilityMeasure
        ((ENNReal.ofReal r)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) r)) := fun _ => h1
    exact Measure.pi.instIsProbabilityMeasure _
  let μ : Measure (Fin n → ℝ) := unifCubeMeasure n 1
  haveI : IsProbabilityMeasure μ := h_cube_prob zero_lt_one

  
  have h_t_meas : ∀ idx : Fin n, Measurable (fun rawTimes : Fin n → ℝ => sortedClampedTime rawTimes idx) := by
    intro idx
    let cmpOf : (Fin n → ℝ) → (Fin n → Fin n → Bool) :=
      fun rawTimes a b => decide (clamp01 (rawTimes a) ≤ clamp01 (rawTimes b))
    have h_eq : (fun rawTimes : Fin n → ℝ => sortedClampedTime rawTimes idx) =
        fun rawTimes => ∑ c ∈ (Finset.univ : Finset (Fin n → Fin n → Bool)),
          if cmpOf rawTimes = c then
            clamp01 (rawTimes ((((List.finRange n).mergeSort c)[idx.1]?).getD idx))
          else 0 := by
      ext rawTimes
      rw [Finset.sum_ite_eq Finset.univ (cmpOf rawTimes) _, if_pos (Finset.mem_univ _)]
      unfold sortedClampedTime sortedClampedList
      have hlen : idx.1 < ((List.finRange n).mergeSort (cmpOf rawTimes)).length := by
        rw [List.length_mergeSort, List.length_finRange]; exact idx.2
      change clamp01 (rawTimes (((List.finRange n).mergeSort (cmpOf rawTimes))[idx.1]'hlen)) = _
      rw [List.getElem?_eq_getElem hlen, Option.getD_some]
    rw [h_eq]
    refine Finset.measurable_sum Finset.univ (fun c _ => ?_)
    have h_set_c : MeasurableSet {rawTimes : Fin n → ℝ | cmpOf rawTimes = c} := by
      have h_iinter : {rawTimes : Fin n → ℝ | cmpOf rawTimes = c} =
          ⋂ a : Fin n, ⋂ b : Fin n,
            {rawTimes : Fin n → ℝ | decide (clamp01 (rawTimes a) ≤ clamp01 (rawTimes b)) = c a b} := by
        ext rawTimes; simp [cmpOf, funext_iff]
      rw [h_iinter]
      refine MeasurableSet.iInter (fun a => MeasurableSet.iInter (fun b => ?_))
      have ha : Measurable (fun rawTimes : Fin n → ℝ => clamp01 (rawTimes a)) :=
        h_clamp_meas.comp (measurable_pi_apply a)
      have hb : Measurable (fun rawTimes : Fin n → ℝ => clamp01 (rawTimes b)) :=
        h_clamp_meas.comp (measurable_pi_apply b)
      cases hcab : c a b
      · have hf : {rawTimes : Fin n → ℝ |
            decide (clamp01 (rawTimes a) ≤ clamp01 (rawTimes b)) = false} =
            {rawTimes : Fin n → ℝ | clamp01 (rawTimes a) ≤ clamp01 (rawTimes b)}ᶜ := by
          ext rawTimes; simp
        rw [hf]; exact (measurableSet_le ha hb).compl
      · have ht : {rawTimes : Fin n → ℝ |
            decide (clamp01 (rawTimes a) ≤ clamp01 (rawTimes b)) = true} =
            {rawTimes : Fin n → ℝ | clamp01 (rawTimes a) ≤ clamp01 (rawTimes b)} := by
          ext rawTimes; simp
        rw [ht]; exact measurableSet_le ha hb
    exact Measurable.ite h_set_c
      (h_clamp_meas.comp (measurable_pi_apply ((((List.finRange n).mergeSort c)[idx.1]?).getD idx)))
      measurable_const

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
            (f a ω) ⊓ (s.inf' hne (fun c => f c ω)) :=
          fun ω => Finset.inf'_insert hne (fun c => f c ω)
        simp_rw [h_eq]
        exact (hf a (Finset.mem_insert_self a s)).inf
          (ih hne (fun c hc => hf c (Finset.mem_insert_of_mem hc)))

  have h_dt_cand_eq : ∀ (C : Finset (Fin n) → Finset (Fin n)) {t : ℝ},
      invE ≤ t → ∀ (S : Finset (Fin n)) (τ β : Fin n → ℝ) (g : Fin n),
      let Cand := Bool ⊕ {z // z ∈ S}
      let candVal : Cand → ℝ := fun c => match c with
        | Sum.inl true => invE
        | Sum.inl false => t
        | Sum.inr z => τ z.1
      let candEff : Cand → ℝ := fun c =>
        let u := candVal c
        if invE ≤ u ∧ u ≤ t ∧ g ∉ C (presentSet S ∅ τ β u) then u else t
      deathTime C t S ∅ τ β g =
        (Finset.univ : Finset Cand).inf' ⟨Sum.inl true, Finset.mem_univ _⟩ candEff := by
    intro C t ht S τ β g Cand candVal candEff
    let E : Set ℝ := {u : ℝ | invE ≤ u ∧ u ≤ t ∧ g ∉ C (presentSet S ∅ τ β u)} ∪ {t}
    have htE : t ∈ E := Set.mem_union_right _ rfl
    have hBdd : BddBelow E := ⟨invE, by
      rintro u (hu | hu)
      · exact hu.1
      · rw [Set.mem_singleton_iff.mp hu]; exact ht⟩
    have hne : (Finset.univ : Finset Cand).Nonempty := ⟨Sum.inl true, Finset.mem_univ _⟩
    apply le_antisymm
    · refine Finset.le_inf' hne candEff (fun c _ => csInf_le hBdd ?_)
      dsimp only [candEff]; split_ifs with hc
      · exact Set.mem_union_left _ hc
      · exact htE
    · refine le_csInf ⟨t, htE⟩ (fun v hv => ?_)
      rcases hv with ⟨hv_lo, hv_hi, hv_not⟩ | hv_eq
      · let L := (Finset.univ : Finset Cand).filter (fun c => candVal c ≤ v)
        have h_true_L : (Sum.inl true : Cand) ∈ L :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv_lo⟩
        have hL_ne : L.Nonempty := ⟨Sum.inl true, h_true_L⟩
        obtain ⟨c₀, hc₀L, hc₀_eq⟩ := Finset.exists_mem_eq_sup' hL_ne candVal
        let u₀ := L.sup' hL_ne candVal
        have hu₀_eq : candVal c₀ = u₀ := hc₀_eq.symm
        have hu₀_lo : invE ≤ u₀ := Finset.le_sup' candVal h_true_L
        have hu₀_v : u₀ ≤ v := hu₀_eq ▸ (Finset.mem_filter.mp hc₀L).2
        have h_pres : presentSet S ∅ τ β u₀ = presentSet S ∅ τ β v := by
          ext z
          simp only [presentSet, Finset.mem_union, Finset.mem_filter, Finset.notMem_empty,
            false_and, or_false]
          refine ⟨fun ⟨hz, hle⟩ => ⟨hz, hle.trans hu₀_v⟩, fun ⟨hz, hle⟩ => ⟨hz, ?_⟩⟩
          have hcL : (Sum.inr ⟨z, hz⟩ : Cand) ∈ L :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩
          exact Finset.le_sup' candVal hcL
        have hc₀_eff : candEff c₀ = u₀ := by
          dsimp only [candEff]; rw [hu₀_eq, h_pres]
          exact if_pos ⟨hu₀_lo, hu₀_v.trans hv_hi, hv_not⟩
        calc (Finset.univ : Finset Cand).inf' hne candEff
            ≤ candEff c₀ := Finset.inf'_le candEff (Finset.mem_univ c₀)
          _ = u₀ := hc₀_eff
          _ ≤ v := hu₀_v
      · rw [Set.mem_singleton_iff.mp hv_eq]
        have h_false : candEff (Sum.inl false) = t := by
          dsimp only [candEff, candVal]; split_ifs <;> rfl
        calc (Finset.univ : Finset Cand).inf' hne candEff
            ≤ candEff (Sum.inl false) := Finset.inf'_le candEff (Finset.mem_univ (Sum.inl false))
          _ = t := h_false

  have h_F_meas : ∀ (w : ItemValuation n) (S B : Finset (Fin n)),
      Measurable (fun s : ℝ => if s ≤ invE then 0 else survivalLaw w S s B) := by
    intro w S B
    let C := canonicalDemand w
    let P := ℝ × (Fin n → ℝ)
    let s_fn : P → ℝ := fun p => max invE p.1
    let τ_fn : P → (Fin n → ℝ) := fun p i => p.1 * p.2 i
    let β_fn : P → (Fin n → ℝ) := fun p _ => s_fn p
    have hs_fn : Measurable s_fn := measurable_const.max measurable_fst
    have hτ_fn : Measurable τ_fn :=
      measurable_pi_iff.mpr (fun i => measurable_fst.mul ((measurable_pi_apply i).comp measurable_snd))
    have h_meas_dt : ∀ g : Fin n,
        Measurable (fun p : P => deathTime C (s_fn p) S ∅ (τ_fn p) (β_fn p) g) := by
      intro g
      let Cand := Bool ⊕ {z // z ∈ S}
      let candVal : Cand → P → ℝ := fun c p => match c with
        | Sum.inl true => invE
        | Sum.inl false => s_fn p
        | Sum.inr z => τ_fn p z.1
      let candEff : Cand → P → ℝ := fun c p =>
        let u := candVal c p
        if invE ≤ u ∧ u ≤ s_fn p ∧ g ∉ C (presentSet S ∅ (τ_fn p) (β_fn p) u) then u else s_fn p
      have h_eq : ∀ p : P, deathTime C (s_fn p) S ∅ (τ_fn p) (β_fn p) g =
          (Finset.univ : Finset Cand).inf' ⟨Sum.inl true, Finset.mem_univ _⟩ (fun c => candEff c p) :=
        fun p => h_dt_cand_eq C (le_max_left invE p.1) S (τ_fn p) (β_fn p) g
      simp_rw [h_eq]
      refine h_meas_inf _ _ candEff (fun c _ => ?_)
      have hu : Measurable (candVal c) := by
        cases c with
        | inl b => cases b
                   · exact hs_fn
                   · exact measurable_const
        | inr z => exact (measurable_pi_apply z.1).comp hτ_fn
      have h_set_pres : ∀ z : Fin n,
          MeasurableSet {p : P | z ∈ presentSet S ∅ (τ_fn p) (β_fn p) (candVal c p)} := by
        intro z
        have heq_z : {p : P | z ∈ presentSet S ∅ (τ_fn p) (β_fn p) (candVal c p)} =
            if z ∈ S then {p : P | τ_fn p z ≤ candVal c p} else ∅ := by
          ext p; simp [presentSet]
        rw [heq_z]; split_ifs
        · exact measurableSet_le ((measurable_pi_apply z).comp hτ_fn) hu
        · exact MeasurableSet.empty
      have h_notC : MeasurableSet
          {p : P | g ∉ C (presentSet S ∅ (τ_fn p) (β_fn p) (candVal c p))} := by
        let badSets := (Finset.univ : Finset (Finset (Fin n))).filter (fun U => g ∉ C U)
        have heq_bad : {p : P | g ∉ C (presentSet S ∅ (τ_fn p) (β_fn p) (candVal c p))} =
            ⋃ U ∈ badSets, ⋂ z : Fin n,
              if z ∈ U then {p : P | z ∈ presentSet S ∅ (τ_fn p) (β_fn p) (candVal c p)}
              else {p : P | z ∈ presentSet S ∅ (τ_fn p) (β_fn p) (candVal c p)}ᶜ := by
          ext p
          simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, badSets, Finset.mem_filter,
            Finset.mem_univ, true_and]
          refine ⟨fun hg => ⟨presentSet S ∅ (τ_fn p) (β_fn p) (candVal c p), hg, fun z => ?_⟩, ?_⟩
          · split_ifs with hz <;> simp [hz]
          · rintro ⟨U, hgU, hzU⟩
            have hU_eq : presentSet S ∅ (τ_fn p) (β_fn p) (candVal c p) = U := by
              ext z; specialize hzU z; by_cases hz : z ∈ U <;> simp [hz] at hzU ⊢ <;> exact hzU
            rwa [hU_eq]
        rw [heq_bad]
        refine Finset.measurableSet_biUnion _ (fun U _ => MeasurableSet.iInter (fun z => ?_))
        split_ifs
        · exact h_set_pres z
        · exact (h_set_pres z).compl
      have h_cond : MeasurableSet {p : P | invE ≤ candVal c p ∧ candVal c p ≤ s_fn p ∧
          g ∉ C (presentSet S ∅ (τ_fn p) (β_fn p) (candVal c p))} :=
        (measurableSet_le measurable_const hu).inter
          ((measurableSet_le hu hs_fn).inter h_notC)
      exact Measurable.ite h_cond hu hs_fn
    have h_meas_ret : ∀ g : Fin n,
        Measurable (fun p : P => retentionProb C (s_fn p) S ∅ (τ_fn p) (β_fn p) g) := by
      intro g; unfold retentionProb
      exact Measurable.ite (measurableSet_le ((measurable_pi_apply g).comp hτ_fn) measurable_const)
        (Real.measurable_log.comp (measurable_const.mul (h_meas_dt g))) measurable_const
    have h_meas_rp : Measurable (fun p : P => retainProd C (s_fn p) S ∅ (τ_fn p) (β_fn p) B) := by
      unfold retainProd; split_ifs with hBS
      · exact (Finset.measurable_prod B (fun g _ => h_meas_ret g)).mul
          (Finset.measurable_prod (S \ B) (fun g _ => measurable_const.sub (h_meas_ret g)))
      · exact measurable_const
    let Φ : P → ℝ := fun p =>
      if p.1 ≤ invE then 0 else retainProd C (s_fn p) S ∅ (τ_fn p) (β_fn p) B
    have hΦ_meas : Measurable Φ :=
      Measurable.ite (measurableSet_le measurable_fst measurable_const) measurable_const h_meas_rp
    have hH_meas : Measurable (fun s : ℝ => ∫ u, Φ (s, u) ∂μ) :=
      (hΦ_meas.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
    have h_eq_fn : (fun s : ℝ => if s ≤ invE then 0 else survivalLaw w S s B) =
        (fun s : ℝ => ∫ u, Φ (s, u) ∂μ) := by
      ext s
      by_cases hs : s ≤ invE
      · rw [if_pos hs]
        have h_zero : (fun u : Fin n → ℝ => Φ (s, u)) = fun _ => 0 := by
          ext u; dsimp only [Φ]; exact if_pos hs
        rw [h_zero, MeasureTheory.integral_zero]
      · rw [if_neg hs]
        have hs_gt : invE < s := lt_of_not_ge hs
        have hs_pos : 0 < s := h_invE_pos.trans hs_gt
        have hs_max : max invE s = s := max_eq_right hs_gt.le
        let μ_s : Measure ℝ := (ENNReal.ofReal s)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) s)
        let scale_s : ℝ → ℝ := fun x => s * x
        have h_sc_meas : Measurable scale_s := measurable_const_mul s
        haveI : IsProbabilityMeasure (ν₁.map scale_s) :=
          Measure.isProbabilityMeasure_map h_sc_meas.aemeasurable
        have h_1d : ν₁.map scale_s = μ_s := by
          have h_pre : scale_s ⁻¹' Set.Icc (0 : ℝ) s = Set.Icc (0 : ℝ) 1 := by
            ext x; simp only [Set.mem_preimage, Set.mem_Icc, scale_s]
            exact ⟨fun ⟨h1, h2⟩ => ⟨(mul_nonneg_iff_of_pos_left hs_pos).mp h1,
              (mul_le_iff_le_one_right hs_pos).mp h2⟩,
              fun ⟨h1, h2⟩ => ⟨mul_nonneg hs_pos.le h1, (mul_le_iff_le_one_right hs_pos).mpr h2⟩⟩
          rw [hν₁_eq, ← h_pre, ← Measure.restrict_map h_sc_meas measurableSet_Icc,
            Real.map_volume_mul_left hs_pos.ne', abs_of_pos (inv_pos.mpr hs_pos),
            ENNReal.ofReal_inv_of_pos hs_pos, Measure.restrict_smul]
        let Scale_s : (Fin n → ℝ) → (Fin n → ℝ) := fun u i => s * u i
        have h_Scale_meas : Measurable Scale_s :=
          measurable_pi_iff.mpr (fun i => measurable_const.mul (measurable_pi_apply i))
        have h_map_cube : μ.map Scale_s = unifCubeMeasure n s := by
          change (Measure.pi (fun _ : Fin n => ν₁)).map (fun u i => scale_s (u i)) =
            Measure.pi (fun _ : Fin n => μ_s)
          rw [Measure.pi_map_pi (fun _ => h_sc_meas.aemeasurable)]
          simp_rw [h_1d]
        let g_s : (Fin n → ℝ) → ℝ := fun τ => retainProd C s S ∅ τ (fun _ => s) B
        have h_gs_eq : ∀ τ : Fin n → ℝ, g_s τ = Φ (s, fun i => s⁻¹ * τ i) := by
          intro τ; dsimp only [g_s, Φ, s_fn, τ_fn, β_fn]; rw [if_neg hs, hs_max]
          have h_mul_inv : (fun i : Fin n => s * (s⁻¹ * τ i)) = τ := by
            ext i; exact mul_inv_cancel_left₀ hs_pos.ne' (τ i)
          rw [h_mul_inv]
        have hg_meas : Measurable g_s := by
          rw [funext h_gs_eq]
          exact hΦ_meas.comp (measurable_const.prodMk
            (measurable_pi_iff.mpr (fun i => measurable_const.mul (measurable_pi_apply i))))
        have h_gs_Scale : ∀ u : Fin n → ℝ, g_s (Scale_s u) = Φ (s, u) := by
          intro u; dsimp only [g_s, Scale_s, Φ, s_fn, τ_fn, β_fn]; rw [if_neg hs, hs_max]
        dsimp only [survivalLaw, genSurvivalLaw, genSurvivalLaw2]
        change (∫ τ, g_s τ ∂(unifCubeMeasure n s)) = ∫ u, Φ (s, u) ∂μ
        rw [← h_map_cube,
          MeasureTheory.integral_map h_Scale_meas.aemeasurable hg_meas.aestronglyMeasurable]
        simp_rw [h_gs_Scale]
    rwa [h_eq_fn]

  have h_α_meas : ∀ (w : ItemValuation n) (x : Fin n) (B S : Finset (Fin n)),
      Measurable (fun s : ℝ => survivalAcceptProb w x B S s) := by
    intro w x B S
    let F_v : ℝ → ℝ := fun s => if s ≤ invE then 0 else survivalLaw w S s B
    let F_vx : ℝ → ℝ := fun s => if s ≤ invE then 0 else survivalLaw (contractVal w x) S s B
    have hFv : Measurable F_v := h_F_meas w S B
    have hFvx : Measurable F_vx := h_F_meas (contractVal w x) S B
    have h_rew : (fun s : ℝ => survivalAcceptProb w x B S s) =
        fun s => if s ≤ invE then 0
          else if x ∉ canonicalDemand w (insert x S) then 0
          else if F_v s = 0 then 0
          else (1 / (Real.exp 1 * s)) * (F_vx s / F_v s) := by
      ext s; unfold survivalAcceptProb; by_cases hs : s ≤ invE <;> simp [hs, F_v, F_vx]
    rw [h_rew]
    by_cases hxD : x ∉ canonicalDemand w (insert x S)
    · have h_zero : (fun s : ℝ => if s ≤ invE then (0 : ℝ)
          else if x ∉ canonicalDemand w (insert x S) then 0
          else if F_v s = 0 then 0
          else (1 / (Real.exp 1 * s)) * (F_vx s / F_v s)) = fun _ => 0 := by
        ext s; simp [hxD]
      rw [h_zero]; exact measurable_const
    · simp_rw [if_neg hxD]
      refine Measurable.ite measurableSet_Iic measurable_const
        (Measurable.ite (measurableSet_eq_fun hFv measurable_const) measurable_const ?_)
      exact (measurable_const.div (measurable_const.mul measurable_id)).mul (hFvx.div hFv)

  
  have h_meas_step : ∀ (prev : List (Fin n)) (x : Fin n) (accepted : Finset (Fin n))
      (oracle : {T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → WithBot ℝ) (b : Bool),
      MeasurableSet {ω : (Fin n → ℝ) × (Fin n → ℝ) | (gsDetAlg ω).step prev x accepted oracle = b} := by
    intro prev x accepted oracle b
    change MeasurableSet {ω : (Fin n → ℝ) × (Fin n → ℝ) |
      gsOnlineSelectionStep ω prev x accepted oracle = b}
    unfold gsOnlineSelectionStep
    by_cases hk : prev.length < n
    · simp_rw [dif_pos hk]
      let idx : Fin n := ⟨prev.length, hk⟩
      let w := localVal prev x oracle
      let α_fn : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun ω =>
        survivalAcceptProb w x accepted prev.toFinset (sortedClampedTime ω.1 idx)
      let coin_fn : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun ω => ω.2 idx
      have hα_m : Measurable α_fn :=
        (h_α_meas w x accepted prev.toFinset).comp ((h_t_meas idx).comp measurable_fst)
      have hc_m : Measurable coin_fn := (measurable_pi_apply idx).comp measurable_snd
      have h_true_set : MeasurableSet {ω : (Fin n → ℝ) × (Fin n → ℝ) |
          0 ≤ coin_fn ω ∧ coin_fn ω < α_fn ω} :=
        (measurableSet_le measurable_const hc_m).inter (measurableSet_lt hc_m hα_m)
      cases b
      · have heq : {ω : (Fin n → ℝ) × (Fin n → ℝ) |
            decide (0 ≤ coin_fn ω ∧ coin_fn ω < α_fn ω) = false} =
            {ω : (Fin n → ℝ) × (Fin n → ℝ) | 0 ≤ coin_fn ω ∧ coin_fn ω < α_fn ω}ᶜ := by
          ext ω; simp
        change MeasurableSet {ω : (Fin n → ℝ) × (Fin n → ℝ) |
          decide (0 ≤ coin_fn ω ∧ coin_fn ω < α_fn ω) = false}
        rw [heq]; exact h_true_set.compl
      · have heq : {ω : (Fin n → ℝ) × (Fin n → ℝ) |
            decide (0 ≤ coin_fn ω ∧ coin_fn ω < α_fn ω) = true} =
            {ω : (Fin n → ℝ) × (Fin n → ℝ) | 0 ≤ coin_fn ω ∧ coin_fn ω < α_fn ω} := by
          ext ω; simp
        change MeasurableSet {ω : (Fin n → ℝ) × (Fin n → ℝ) |
          decide (0 ≤ coin_fn ω ∧ coin_fn ω < α_fn ω) = true}
        rwa [heq]
    · simp_rw [dif_neg hk]
      cases b
      · simp
      · simp

  
  have h_psi_inj : Function.Injective (@psiWeight n) := by
    have h_geom : ∀ a b : ℕ, a ≤ b →
        ∑ k ∈ Finset.Ico a b, (1 / 2 : ℝ) ^ (k + 1) = (1 / 2 : ℝ) ^ a - (1 / 2 : ℝ) ^ b := by
      intro a b hab
      induction b with
      | zero => obtain rfl : a = 0 := Nat.eq_zero_of_le_zero hab; simp
      | succ b ih =>
        rcases Nat.of_le_succ hab with hab' | rfl
        · rw [Finset.sum_Ico_succ_top hab', ih hab']; ring
        · simp
    have h_tail_lt : ∀ (S : Finset (Fin n)) (m : ℕ),
        m ≤ n → (∀ g ∈ S, m ≤ g.1) →
          ∑ g ∈ S, (1 / 2 : ℝ) ^ (g.1 + 1) < (1 / 2 : ℝ) ^ m := by
      intro S m hmn hm
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
    intro X Y hXY
    have hsplit : ∀ A : Finset (Fin n),
        psiWeight A = (A.card : ℝ) + ∑ g ∈ A, (1 / 2 : ℝ) ^ (g.1 + 1) := by
      intro A; simp [psiWeight, Finset.sum_add_distrib]
    have hX0 : 0 ≤ ∑ g ∈ X, (1 / 2 : ℝ) ^ (g.1 + 1) := Finset.sum_nonneg (fun g _ => by positivity)
    have hY0 : 0 ≤ ∑ g ∈ Y, (1 / 2 : ℝ) ^ (g.1 + 1) := Finset.sum_nonneg (fun g _ => by positivity)
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
      rw [Finset.nonempty_iff_ne_empty]; intro hemp
      exact hne (Finset.Subset.antisymm
        (Finset.sdiff_eq_empty_iff_subset.mp (Finset.union_eq_empty.mp hemp).1)
        (Finset.sdiff_eq_empty_iff_subset.mp (Finset.union_eq_empty.mp hemp).2))
    let m₀ := D.min' hDne
    rcases Finset.mem_union.mp (Finset.min'_mem D hDne) with hmXY | hmYX
    · refine h_no_min X Y hδ m₀ hmXY (fun g hg => lt_of_le_of_ne
        (Finset.min'_le D g (Finset.mem_union_right _ hg)) (fun h => ?_))
      have hgY : g ∈ Y := (Finset.mem_sdiff.mp hg).1
      rw [← h] at hgY; exact (Finset.mem_sdiff.mp hmXY).2 hgY
    · refine h_no_min Y X hδ.symm m₀ hmYX (fun g hg => lt_of_le_of_ne
        (Finset.min'_le D g (Finset.mem_union_left _ hg)) (fun h => ?_))
      have hgX : g ∈ X := (Finset.mem_sdiff.mp hg).1
      rw [← h] at hgX; exact (Finset.mem_sdiff.mp hmYX).2 hgX

  have h_cd_congr : ∀ (v₁ v₂ : ItemValuation n) (U : Finset (Fin n)),
      (∀ Z ⊆ U, v₁ Z = v₂ Z) → canonicalDemand v₁ U = canonicalDemand v₂ U := by
    intro v₁ v₂ U hv_eq
    have h_key : ∀ X ∈ U.powerset, ∀ Y ∈ U.powerset,
        demandKeyLe v₁ Y X ↔ demandKeyLe v₂ Y X := by
      intro X hX Y hY
      unfold demandKeyLe
      rw [hv_eq X (Finset.mem_powerset.mp hX), hv_eq Y (Finset.mem_powerset.mp hY)]
    unfold canonicalDemand
    by_cases h₁ : ∃ X ∈ U.powerset, ∀ Y ∈ U.powerset, demandKeyLe v₁ Y X
    · have h₂ : ∃ X ∈ U.powerset, ∀ Y ∈ U.powerset, demandKeyLe v₂ Y X := by
        obtain ⟨X, hXU, hmax⟩ := h₁
        exact ⟨X, hXU, fun Y hYU => (h_key X hXU Y hYU).mp (hmax Y hYU)⟩
      rw [dif_pos h₁, dif_pos h₂]
      obtain ⟨hX₁U, hmax₁⟩ := Classical.choose_spec h₁
      obtain ⟨hX₂U, hmax₂⟩ := Classical.choose_spec h₂
      have hk12 : demandKeyLe v₁ (Classical.choose h₂) (Classical.choose h₁) :=
        hmax₁ _ hX₂U
      have hk21 : demandKeyLe v₁ (Classical.choose h₁) (Classical.choose h₂) :=
        (h_key _ hX₂U _ hX₁U).mpr (hmax₂ _ hX₁U)
      rcases hk12 with hlt12 | ⟨heq12, hle12⟩
      · rcases hk21 with hlt21 | ⟨heq21, _⟩
        · exact (lt_asymm hlt12 hlt21).elim
        · exact (ne_of_lt hlt12 heq21.symm).elim
      · rcases hk21 with hlt21 | ⟨_, hle21⟩
        · exact (ne_of_lt hlt21 heq12.symm).elim
        · exact h_psi_inj (le_antisymm hle21 hle12)
    · have h₂ : ¬∃ X ∈ U.powerset, ∀ Y ∈ U.powerset, demandKeyLe v₂ Y X := by
        rintro ⟨X, hXU, hmax⟩
        exact h₁ ⟨X, hXU, fun Y hYU => (h_key X hXU Y hYU).mpr (hmax Y hYU)⟩
      rw [dif_neg h₁, dif_neg h₂]

  have h_surv_congr : ∀ (w₁ w₂ : ItemValuation n) (S A : Finset (Fin n)) (t : ℝ),
      (∀ U ⊆ S, canonicalDemand w₁ U = canonicalDemand w₂ U) →
        survivalLaw w₁ S t A = survivalLaw w₂ S t A := by
    intro w₁ w₂ S A t hcd
    unfold survivalLaw genSurvivalLaw genSurvivalLaw2
    refine congrArg (fun f : (Fin n → ℝ) → ℝ => ∫ τ, f τ ∂(unifCubeMeasure n t)) (funext fun τ => ?_)
    have h_dt : ∀ g : Fin n,
        deathTime (canonicalDemand w₁) t S ∅ τ (fun _ => t) g =
          deathTime (canonicalDemand w₂) t S ∅ τ (fun _ => t) g := by
      intro g; unfold deathTime
      have h_set : {u : ℝ | invE ≤ u ∧ u ≤ t ∧
          g ∉ canonicalDemand w₁ (presentSet S ∅ τ (fun _ => t) u)} =
          {u : ℝ | invE ≤ u ∧ u ≤ t ∧
          g ∉ canonicalDemand w₂ (presentSet S ∅ τ (fun _ => t) u)} := by
        ext u
        simp only [Set.mem_setOf_eq]
        have hsub : presentSet S ∅ τ (fun _ => t) u ⊆ S := by
          intro z hz; simp [presentSet] at hz; exact hz.1
        rw [hcd _ hsub]
      rw [h_set]
    have h_ret : ∀ g : Fin n,
        retentionProb (canonicalDemand w₁) t S ∅ τ (fun _ => t) g =
          retentionProb (canonicalDemand w₂) t S ∅ τ (fun _ => t) g := by
      intro g; unfold retentionProb; rw [h_dt g]
    unfold retainProd
    split_ifs with hAS
    · have hp1 : (∏ g ∈ A, retentionProb (canonicalDemand w₁) t S ∅ τ (fun _ => t) g) =
          (∏ g ∈ A, retentionProb (canonicalDemand w₂) t S ∅ τ (fun _ => t) g) :=
        Finset.prod_congr rfl (fun g _ => h_ret g)
      have hp2 : (∏ g ∈ S \ A, (1 - retentionProb (canonicalDemand w₁) t S ∅ τ (fun _ => t) g)) =
          (∏ g ∈ S \ A, (1 - retentionProb (canonicalDemand w₂) t S ∅ τ (fun _ => t) g)) :=
        Finset.prod_congr rfl (fun g _ => by rw [h_ret g])
      rw [hp1, hp2]
    · rfl

  have h_acc_local : ∀ (v : ItemValuation n) (prev : List (Fin n)) (x : Fin n)
      (acc : Finset (Fin n)) (t : ℝ)
      (oracle : {T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → WithBot ℝ),
      (∀ T h, oracle ⟨T, h⟩ = v T) →
      x ∉ prev.toFinset →
        survivalAcceptProb (localVal prev x oracle) x acc prev.toFinset t =
          survivalAcceptProb v x acc prev.toFinset t := by
    intro v prev x acc t oracle horacle hxS
    let S := prev.toFinset
    let v_loc := localVal prev x oracle
    have hv_eq : ∀ Z ⊆ insert x S, v_loc Z = v Z := by
      intro Z hZ; dsimp only [v_loc, localVal]; rw [dif_pos hZ]; exact horacle Z hZ
    have hcd_ins : canonicalDemand v_loc (insert x S) = canonicalDemand v (insert x S) :=
      h_cd_congr v_loc v (insert x S) hv_eq
    have h_sl : survivalLaw v_loc S t acc = survivalLaw v S t acc :=
      h_surv_congr v_loc v S acc t (fun U hUS =>
        h_cd_congr v_loc v U (fun Z hZU => hv_eq Z (hZU.trans (hUS.trans (Finset.subset_insert x S)))))
    have h_sl_cv : survivalLaw (contractVal v_loc x) S t acc =
        survivalLaw (contractVal v x) S t acc := by
      refine h_surv_congr (contractVal v_loc x) (contractVal v x) S acc t (fun U hUS =>
        h_cd_congr _ _ U (fun Z hZU => ?_))
      have hZS : Z ⊆ S := hZU.trans hUS
      have hxZ : x ∉ Z := fun hx => hxS (hZS hx)
      have hx_sub : ({x} : Finset (Fin n)) ⊆ insert x S :=
        Finset.singleton_subset_iff.mpr (Finset.mem_insert_self x S)
      have hinsZ : insert x Z ⊆ insert x S := Finset.insert_subset_insert x hZS
      unfold contractVal
      rw [if_neg hxZ, if_neg hxZ, hv_eq {x} hx_sub, hv_eq (insert x Z) hinsZ]
    unfold survivalAcceptProb
    change (if t ≤ invE then 0
      else if x ∉ canonicalDemand v_loc (insert x S) then 0
      else if survivalLaw v_loc S t acc = 0 then 0
      else (1 / (Real.exp 1 * t)) *
        (survivalLaw (contractVal v_loc x) S t acc / survivalLaw v_loc S t acc)) = _
    rw [hcd_ins, h_sl, h_sl_cv]

  
  have h_run_fst : ∀ (d : DetSelectionAlg n) (v : ItemValuation n) (π : Equiv.Perm (Fin n))
      (k : ℕ) (hk : k ≤ n),
      (runDetSelectionSteps d v π k hk).1 = (List.ofFn π).take k := by
    intro d v π k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have hlen : k < (List.ofFn π).length := by rw [List.length_ofFn]; exact hk
      change (runDetSelectionSteps d v π k (Nat.le_of_succ_le hk)).1 ++ [π ⟨k, hk⟩] =
        (List.ofFn π).take (k + 1)
      rw [ih (Nat.le_of_succ_le hk), List.take_add_one, List.getElem?_eq_getElem hlen,
        Option.toList_some, List.getElem_ofFn]

  have h_step_prev_eq : ∀ (d : DetSelectionAlg n) (v : ItemValuation n)
      (prev₁ prev₂ : List (Fin n)) (x : Fin n) (acc : Finset (Fin n)),
      prev₁ = prev₂ →
      d.step prev₁ x acc (fun ⟨T, _⟩ => v T) = d.step prev₂ x acc (fun ⟨T, _⟩ => v T) := by
    intro d v prev₁ prev₂ x acc h; subst h; rfl

  have h_run_snd_sub : ∀ (d : DetSelectionAlg n) (v : ItemValuation n) (π : Equiv.Perm (Fin n))
      (k : ℕ) (hk : k ≤ n),
      (runDetSelectionSteps d v π k hk).2 ⊆ (runDetSelectionSteps d v π k hk).1.toFinset := by
    intro d v π k
    induction k with
    | zero => intro _; simp [runDetSelectionSteps]
    | succ k ih =>
      intro hk
      let st := runDetSelectionSteps d v π k (Nat.le_of_succ_le hk)
      let x := π ⟨k, hk⟩
      have h_sub₀ : st.2 ⊆ (st.1 ++ [x]).toFinset :=
        (ih (Nat.le_of_succ_le hk)).trans (by
          intro z hz; dsimp only [st]; simp only [List.toFinset_append, Finset.mem_union]
          exact Or.inl hz)
      change (if d.step st.1 x st.2 (fun ⟨T, _⟩ => v T) then insert x st.2 else st.2) ⊆
        (st.1 ++ [x]).toFinset
      split_ifs
      · exact Finset.insert_subset_iff.mpr ⟨by simp, h_sub₀⟩
      · exact h_sub₀

  have h_not_in_take : ∀ (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k + 1 ≤ n),
      π ⟨k, hk⟩ ∉ ((List.ofFn π).take k).toFinset := by
    intro π k hk hmem
    rw [List.mem_toFinset] at hmem
    obtain ⟨i, hi_len, hi_eq⟩ := List.getElem_of_mem hmem
    have h_take_len : ((List.ofFn π).take k).length = k := by
      rw [List.length_take, List.length_ofFn]; omega
    have hi_lt_k : i < k := hi_len.trans_eq h_take_len
    have hi_lt_n : i < (List.ofFn π).length := by rw [List.length_ofFn]; omega
    rw [List.getElem_take, List.getElem_ofFn] at hi_eq
    have h_idx := π.injective hi_eq
    exact (ne_of_lt hi_lt_k) (congrArg Fin.val h_idx)

  
  have h_det_safe : ∀ (v : ItemValuation n), IsGSValuation v →
      ∀ (ω : (Fin n → ℝ) × (Fin n → ℝ)) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
        let st := runDetSelectionSteps (gsDetAlg ω) v π k hk
        ∃ T ⊆ st.1.toFinset,
          st.2 ⊆ canonicalDemand v T ∧
          v st.2 ≠ ⊥ ∧
          ∀ Y ⊆ st.2, v Y ≠ ⊥ ∧ 0 ≤ realVal v Y := by
    intro v hv ω π k hk
    obtain ⟨_, h_surv_v, h_safe_v, h_cont_v⟩ := H_surv v hv
    suffices h_ind : ∀ (m : ℕ) (hm : m ≤ n),
        let st := runDetSelectionSteps (gsDetAlg ω) v π m hm
        ∃ T ⊆ st.1.toFinset, st.2 ⊆ canonicalDemand v T by
      obtain ⟨T, hT1, hT2⟩ := h_ind k hk
      exact ⟨T, hT1, hT2, (h_safe_v T _ hT2).1, fun Y hY => h_safe_v T Y (hY.trans hT2)⟩
    intro m
    induction m with
    | zero =>
      intro hm; exact ⟨∅, Finset.empty_subset _, Finset.empty_subset _⟩
    | succ m ih =>
      intro hm
      let st := runDetSelectionSteps (gsDetAlg ω) v π m (Nat.le_of_succ_le hm)
      let x := π ⟨m, hm⟩
      obtain ⟨T₀, hT₀_sub, h_acc_sub⟩ := ih (Nat.le_of_succ_le hm)
      have h_st1 : st.1 = (List.ofFn π).take m := h_run_fst (gsDetAlg ω) v π m (Nat.le_of_succ_le hm)
      have h_len : st.1.length = m := by
        rw [h_st1, List.length_take, List.length_ofFn]; omega
      have h_lt_n : st.1.length < n := h_len.symm ▸ hm
      have hx_not_S : x ∉ st.1.toFinset := by
        rw [h_st1]; exact h_not_in_take π m hm
      have h_idx_eq : (⟨st.1.length, h_lt_n⟩ : Fin n) = ⟨m, hm⟩ := Fin.ext h_len
      let dec := (gsDetAlg ω).step st.1 x st.2 (fun ⟨T, _⟩ => v T)
      change ∃ T ⊆ (st.1 ++ [x]).toFinset,
        (if dec then insert x st.2 else st.2) ⊆ canonicalDemand v T
      by_cases hdec : dec = true
      · rw [if_pos hdec]
        have hdec_unfold : gsOnlineSelectionStep ω st.1 x st.2 (fun ⟨T, _⟩ => v T) = true := hdec
        unfold gsOnlineSelectionStep at hdec_unfold
        rw [dif_pos h_lt_n, h_idx_eq, decide_eq_true_eq,
          h_acc_local v st.1 x st.2 (sortedClampedTime ω.1 ⟨m, hm⟩) _ (fun _ _ => rfl) hx_not_S] at hdec_unfold
        let t := sortedClampedTime ω.1 ⟨m, hm⟩
        have ht_le1 : t ≤ 1 := (h_t_bounds ω.1 ⟨m, hm⟩).2
        have hα_pos : 0 < survivalAcceptProb v x st.2 st.1.toFinset t :=
          lt_of_le_of_lt hdec_unfold.1 hdec_unfold.2
        unfold survivalAcceptProb at hα_pos
        by_cases ht_inv : t ≤ invE
        · rw [if_pos ht_inv] at hα_pos; exact (lt_irrefl 0 hα_pos).elim
        · rw [if_neg ht_inv] at hα_pos
          have ht_gt : invE < t := lt_of_not_ge ht_inv
          have ht_pos : 0 < t := h_invE_pos.trans ht_gt
          by_cases hx_notD : x ∉ canonicalDemand v (insert x st.1.toFinset)
          · rw [if_pos hx_notD] at hα_pos; exact (lt_irrefl 0 hα_pos).elim
          · rw [if_neg hx_notD] at hα_pos
            have hxD : x ∈ canonicalDemand v (insert x st.1.toFinset) := not_not.mp hx_notD
            by_cases hden0 : survivalLaw v st.1.toFinset t st.2 = 0
            · rw [if_pos hden0] at hα_pos; exact (lt_irrefl 0 hα_pos).elim
            · rw [if_neg hden0] at hα_pos
              have hden_pos : 0 < survivalLaw v st.1.toFinset t st.2 :=
                lt_of_le_of_ne (h_surv_v st.1.toFinset st.2 t ht_gt.le ht_le1).1 (Ne.symm hden0)
              obtain ⟨hv_cv, h_comm⟩ := h_cont_v st.1.toFinset x hx_not_S hxD
              obtain ⟨_, h_surv_cv, _, _⟩ := H_surv (contractVal v x) hv_cv
              have hnum_nn : 0 ≤ survivalLaw (contractVal v x) st.1.toFinset t st.2 :=
                (h_surv_cv st.1.toFinset st.2 t ht_gt.le ht_le1).1
              have hnum_pos : 0 < survivalLaw (contractVal v x) st.1.toFinset t st.2 := by
                by_contra hle
                rw [le_antisymm (not_lt.mp hle) hnum_nn, zero_div, mul_zero] at hα_pos
                exact lt_irrefl 0 hα_pos
              obtain ⟨T', hT'S, h_st2_cv⟩ :=
                (h_surv_cv st.1.toFinset st.2 t ht_gt.le ht_le1).2 hnum_pos
              obtain ⟨hx_DT', h_er_eq⟩ := h_comm T' hT'S
              refine ⟨insert x T', ?_, ?_⟩
              · intro z hz
                simp only [List.toFinset_append, Finset.mem_union]
                rcases Finset.mem_insert.mp hz with rfl | hzT'
                · exact Or.inr (by simp)
                · exact Or.inl (hT'S hzT')
              · refine Finset.insert_subset_iff.mpr ⟨hx_DT', ?_⟩
                exact h_st2_cv.trans (h_er_eq.symm ▸ Finset.erase_subset x _)
      · rw [if_neg hdec]
        refine ⟨T₀, hT₀_sub.trans ?_, h_acc_sub⟩
        intro z hz; dsimp only [st]; simp only [List.toFinset_append, Finset.mem_union]; exact Or.inl hz

  
  have h_cyl_indep : ∀ (idx : Fin n) (E : Set (Fin n → ℝ)) (J : Set ℝ),
      MeasurableSet E →
      (∀ (c : Fin n → ℝ) (r : ℝ), Function.update c idx r ∈ E ↔ c ∈ E) →
      MeasurableSet J →
        μ.real (E ∩ {c : Fin n → ℝ | c idx ∈ J}) = μ.real E * ν₁.real J := by
    intro idx E J hE hE_upd hJ
    let p : Fin n → Prop := fun j => j = idx
    let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) p
    let μ_in : Measure ({j : Fin n // p j} → ℝ) := Measure.pi (fun _ => ν₁)
    let μ_out : Measure ({j : Fin n // ¬ p j} → ℝ) := Measure.pi (fun _ => ν₁)
    haveI : IsProbabilityMeasure μ_in := by dsimp only [μ_in]; infer_instance
    haveI : IsProbabilityMeasure μ_out := by dsimp only [μ_out]; infer_instance
    have h_mp : MeasurePreserving e μ (μ_in.prod μ_out) := by
      have h_ft : @Measure.pi (Subtype p) (fun _ => ℝ) (Subtype.fintype p) _ (fun _ => ν₁) = μ_in :=
        congrArg (fun ft => @Measure.pi (Subtype p) (fun _ => ℝ) ft _ (fun _ => ν₁)) (Subsingleton.elim _ _)
      rw [← h_ft]
      dsimp only [μ, unifCubeMeasure, μ_out]
      exact MeasureTheory.measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => ν₁) p
    let idx_sub : {j : Fin n // p j} := ⟨idx, rfl⟩
    let lift_y : ({j : Fin n // ¬ p j} → ℝ) → (Fin n → ℝ) :=
      fun y j => if hj : ¬ p j then y ⟨j, hj⟩ else 0
    have h_lift_meas : Measurable lift_y := by
      refine measurable_pi_iff.mpr (fun j => ?_)
      dsimp only [lift_y]
      by_cases hj : ¬ p j
      · simp_rw [dif_pos hj]; exact measurable_pi_apply (⟨j, hj⟩ : {k : Fin n // ¬ p k})
      · simp_rw [dif_neg hj]; exact measurable_const
    let A_set : Set ({j : Fin n // p j} → ℝ) := (Function.eval idx_sub) ⁻¹' J
    let B_set : Set ({j : Fin n // ¬ p j} → ℝ) := lift_y ⁻¹' E
    have hA_meas : MeasurableSet A_set := hJ.preimage (measurable_pi_apply idx_sub)
    have hB_meas : MeasurableSet B_set := hE.preimage h_lift_meas
    have h_upd_eq : ∀ c : Fin n → ℝ, Function.update (lift_y (e c).2) idx (c idx) = c := by
      intro c; ext j
      by_cases hj : j = idx
      · subst hj; simp
      · rw [Function.update_of_ne hj]
        dsimp only [lift_y]
        have hnp : ¬ p j := hj
        rw [dif_pos hnp]
        rfl
    have h_pre_E : e ⁻¹' (Set.univ ×ˢ B_set) = E := by
      ext c
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and, B_set]
      have h1 := hE_upd (lift_y (e c).2) (c idx)
      rw [h_upd_eq c] at h1
      exact h1.symm
    have h_pre_EJ : e ⁻¹' (A_set ×ˢ B_set) = E ∩ {c : Fin n → ℝ | c idx ∈ J} := by
      ext c
      simp only [Set.mem_preimage, Set.mem_prod, A_set, B_set, Set.mem_inter_iff, Set.mem_setOf_eq]
      have h1 := hE_upd (lift_y (e c).2) (c idx)
      rw [h_upd_eq c] at h1
      exact ⟨fun ⟨hA, hB⟩ => ⟨h1.mpr hB, hA⟩, fun ⟨hcE, hcJ⟩ => ⟨hcJ, h1.mp hcE⟩⟩
    have h_mE : μ E = μ_out B_set := by
      rw [← h_pre_E, h_mp.measure_preimage (MeasurableSet.univ.prod hB_meas).nullMeasurableSet,
        Measure.prod_prod, measure_univ, one_mul]
    have h_mA : μ_in A_set = ν₁ J :=
      (MeasureTheory.measurePreserving_eval (fun _ : {j : Fin n // p j} => ν₁) idx_sub).measure_preimage
        hJ.nullMeasurableSet
    have h_mEJ : μ (E ∩ {c : Fin n → ℝ | c idx ∈ J}) = ν₁ J * μ E := by
      rw [← h_pre_EJ, h_mp.measure_preimage (hA_meas.prod hB_meas).nullMeasurableSet,
        Measure.prod_prod, h_mA, h_mE]
    rw [MeasureTheory.measureReal_def, h_mEJ, ENNReal.toReal_mul,
      ← MeasureTheory.measureReal_def, ← MeasureTheory.measureReal_def, mul_comm]

  have h_ν₁_Ico : ∀ {α : ℝ}, 0 ≤ α → α ≤ 1 →
      ν₁.real {r : ℝ | 0 ≤ r ∧ r < α} = α ∧
      ν₁.real {r : ℝ | ¬(0 ≤ r ∧ r < α)} = 1 - α := by
    intro α h0 h1
    have h_eq_Ico : {r : ℝ | 0 ≤ r ∧ r < α} = Set.Ico 0 α := rfl
    have h_inter : Set.Ico 0 α ∩ Set.Icc (0 : ℝ) 1 = Set.Ico 0 α :=
      Set.inter_eq_left.mpr (fun r hr => ⟨hr.1, hr.2.le.trans h1⟩)
    have h_m : ν₁ (Set.Ico 0 α) = ENNReal.ofReal α := by
      rw [hν₁_eq, Measure.restrict_apply measurableSet_Ico, h_inter, Real.volume_Ico, sub_zero]
    have h_r1 : ν₁.real {r : ℝ | 0 ≤ r ∧ r < α} = α := by
      rw [h_eq_Ico, MeasureTheory.measureReal_def, h_m, ENNReal.toReal_ofReal h0]
    refine ⟨h_r1, ?_⟩
    have h_compl_eq : {r : ℝ | ¬(0 ≤ r ∧ r < α)} = (Set.Ico 0 α)ᶜ := rfl
    have h_mc : ν₁ (Set.Ico 0 α)ᶜ = 1 - ENNReal.ofReal α := by
      rw [measure_compl measurableSet_Ico (measure_ne_top ν₁ _), measure_univ, h_m]
    have h_le1 : ENNReal.ofReal α ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal h1
    rw [h_compl_eq, MeasureTheory.measureReal_def, h_mc,
      ENNReal.toReal_sub_of_le h_le1 ENNReal.one_ne_top, ENNReal.toReal_one,
      ENNReal.toReal_ofReal h0]

  have h_run_append : ∀ (v : ItemValuation n) (τ : Fin n → ℝ) (L : List (Fin n))
      (x : Fin n) (S₀ : Finset (Fin n)) (d : Finset (Fin n) → ℝ),
      survivalRunDistList v τ (L ++ [x]) S₀ d =
        survivalStepDist v (S₀ ∪ L.toFinset) x (τ x) (survivalRunDistList v τ L S₀ d) := by
    intro v τ L x
    induction L with
    | nil => intro S₀ d; simp [survivalRunDistList]
    | cons y ys ih =>
      intro S₀ d
      dsimp only [List.cons_append, survivalRunDistList]
      rw [ih (insert y S₀) (survivalStepDist v S₀ y (τ y) d)]
      have h_u : insert y S₀ ∪ ys.toFinset = S₀ ∪ (y :: ys).toFinset := by
        ext z; simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons]; tauto
      rw [h_u]

  let dist₀ : Finset (Fin n) → ℝ := fun B => if B = ∅ then 1 else 0

  have h_coin_marg : ∀ (v : ItemValuation n), IsGSValuation v →
      ∀ (u : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)),
        μ.real {coins : Fin n → ℝ | runDetSelection (gsDetAlg (u, coins)) v π = S} =
          survivalRunDistList v (fun g => sortedClampedTime u (π.symm g))
            (List.ofFn π) ∅ dist₀ S := by
    intro v hv u π S
    obtain ⟨h_acc_bdd, _, _, _⟩ := H_surv v hv
    let τ_π : Fin n → ℝ := fun g => sortedClampedTime u (π.symm g)
    have h_ind : ∀ (k : ℕ) (hk : k ≤ n),
        let A_k : (Fin n → ℝ) → Finset (Fin n) :=
          fun coins => (runDetSelectionSteps (gsDetAlg (u, coins)) v π k hk).2
        (∀ B : Finset (Fin n), MeasurableSet {coins : Fin n → ℝ | A_k coins = B}) ∧
        (∀ coins₁ coins₂ : Fin n → ℝ,
          (∀ j : Fin n, j.1 < k → coins₁ j = coins₂ j) → A_k coins₁ = A_k coins₂) ∧
        (∀ B : Finset (Fin n),
          μ.real {coins : Fin n → ℝ | A_k coins = B} =
            survivalRunDistList v τ_π ((List.ofFn π).take k) ∅ dist₀ B) := by
      intro k
      induction k with
      | zero =>
        intro hk
        refine ⟨?_, fun _ _ _ => rfl, ?_⟩
        · intro B
          change MeasurableSet {coins : Fin n → ℝ | (∅ : Finset (Fin n)) = B}
          by_cases hB : (∅ : Finset (Fin n)) = B
          · simp only [hB, Set.setOf_true]; exact MeasurableSet.univ
          · simp only [hB, Set.setOf_false]; exact MeasurableSet.empty
        · intro B
          dsimp only [List.take_zero, survivalRunDistList, dist₀]
          change μ.real {coins : Fin n → ℝ | (∅ : Finset (Fin n)) = B} = if B = ∅ then 1 else 0
          by_cases hB : B = ∅
          · subst hB; simp [MeasureTheory.measureReal_def]
          · have hne : (∅ : Finset (Fin n)) ≠ B := Ne.symm hB
            simp [hB, hne]
      | succ k ih =>
        intro hk
        obtain ⟨h_meas_k, h_dep_k, h_law_k⟩ := ih (Nat.le_of_succ_le hk)
        let A_k : (Fin n → ℝ) → Finset (Fin n) :=
          fun coins => (runDetSelectionSteps (gsDetAlg (u, coins)) v π k (Nat.le_of_succ_le hk)).2
        let L_k := (List.ofFn π).take k
        let S_k := L_k.toFinset
        let idx : Fin n := ⟨k, hk⟩
        let x := π idx
        have h_len_Lk : L_k.length = k := by
          dsimp only [L_k]; rw [List.length_take, List.length_ofFn]; omega
        have h_lt_Lk : L_k.length < n := h_len_Lk.symm ▸ hk
        have h_idx_Lk : (⟨L_k.length, h_lt_Lk⟩ : Fin n) = idx := Fin.ext h_len_Lk
        have hx_not_Sk : x ∉ S_k := h_not_in_take π k hk
        have hτx : τ_π x = sortedClampedTime u idx := by
          dsimp only [τ_π, x]; rw [π.symm_apply_apply]
        have hτx_le1 : τ_π x ≤ 1 := hτx ▸ (h_t_bounds u idx).2
        have h_step_eq : ∀ coins : Fin n → ℝ,
            (runDetSelectionSteps (gsDetAlg (u, coins)) v π (k + 1) hk).2 =
              if (0 ≤ coins idx ∧ coins idx < survivalAcceptProb v x (A_k coins) S_k (τ_π x))
              then insert x (A_k coins) else A_k coins := by
          intro coins
          have h_fst_eq : (runDetSelectionSteps (gsDetAlg (u, coins)) v π k (Nat.le_of_succ_le hk)).1 =
              L_k := h_run_fst (gsDetAlg (u, coins)) v π k (Nat.le_of_succ_le hk)
          have h_iff : ((gsDetAlg (u, coins)).step
              (runDetSelectionSteps (gsDetAlg (u, coins)) v π k (Nat.le_of_succ_le hk)).1
              x (A_k coins) (fun ⟨T, _⟩ => v T) = true) ↔
              (0 ≤ coins idx ∧ coins idx < survivalAcceptProb v x (A_k coins) S_k (τ_π x)) := by
            rw [h_step_prev_eq (gsDetAlg (u, coins)) v _ L_k x (A_k coins) h_fst_eq]
            dsimp only [gsDetAlg, gsOnlineSelectionStep]
            rw [dif_pos h_lt_Lk, h_idx_Lk, decide_eq_true_iff,
              h_acc_local v L_k x (A_k coins) (sortedClampedTime u idx) _ (fun _ _ => rfl) hx_not_Sk,
              ← hτx]
          change (if (gsDetAlg (u, coins)).step
              (runDetSelectionSteps (gsDetAlg (u, coins)) v π k (Nat.le_of_succ_le hk)).1
              x (A_k coins) (fun ⟨T, _⟩ => v T) = true
            then insert x (A_k coins) else A_k coins) = _
          by_cases hQ : 0 ≤ coins idx ∧ coins idx < survivalAcceptProb v x (A_k coins) S_k (τ_π x)
          · rw [if_pos (h_iff.mpr hQ), if_pos hQ]
          · rw [if_neg (mt h_iff.mp hQ), if_neg hQ]
        have h_Ak_sub : ∀ coins : Fin n → ℝ, A_k coins ⊆ S_k := by
          intro coins
          have h1 := h_run_snd_sub (gsDetAlg (u, coins)) v π k (Nat.le_of_succ_le hk)
          rwa [h_run_fst (gsDetAlg (u, coins)) v π k (Nat.le_of_succ_le hk)] at h1
        have h_Ak_not_x : ∀ coins : Fin n → ℝ, x ∉ A_k coins :=
          fun coins hx => hx_not_Sk (h_Ak_sub coins hx)
        have h_fib_eq : ∀ B : Finset (Fin n),
            {coins : Fin n → ℝ |
              (runDetSelectionSteps (gsDetAlg (u, coins)) v π (k + 1) hk).2 = B} =
              if x ∈ B then
                {coins | A_k coins = B.erase x} ∩
                  {coins | 0 ≤ coins idx ∧ coins idx < survivalAcceptProb v x (B.erase x) S_k (τ_π x)}
              else
                {coins | A_k coins = B} ∩
                  {coins | ¬(0 ≤ coins idx ∧ coins idx < survivalAcceptProb v x B S_k (τ_π x))} := by
          intro B; ext coins
          simp only [Set.mem_setOf_eq, h_step_eq coins]
          by_cases hxB : x ∈ B
          · rw [if_pos hxB]
            simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
            by_cases hc : 0 ≤ coins idx ∧ coins idx < survivalAcceptProb v x (A_k coins) S_k (τ_π x)
            · rw [if_pos hc]
              refine ⟨fun hins => ?_, fun ⟨her, hc'⟩ => ?_⟩
              · have her : A_k coins = B.erase x := by
                  rw [← hins, Finset.erase_insert (h_Ak_not_x coins)]
                exact ⟨her, her ▸ hc⟩
              · rw [her, Finset.insert_erase hxB]
            · rw [if_neg hc]
              refine ⟨fun hEq => (h_Ak_not_x coins (hEq ▸ hxB)).elim, fun ⟨her, hc'⟩ => ?_⟩
              exact (hc (her.symm ▸ hc')).elim
          · rw [if_neg hxB]
            simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
            by_cases hc : 0 ≤ coins idx ∧ coins idx < survivalAcceptProb v x (A_k coins) S_k (τ_π x)
            · rw [if_pos hc]
              refine ⟨fun hins => (hxB (hins ▸ Finset.mem_insert_self x _)).elim,
                fun ⟨hEq, hnc⟩ => (hnc (hEq ▸ hc)).elim⟩
            · rw [if_neg hc]
              exact ⟨fun hEq => ⟨hEq, hEq ▸ hc⟩, fun ⟨hEq, _⟩ => hEq⟩
        have h_upd_indep : ∀ W : Finset (Fin n), ∀ (c : Fin n → ℝ) (r : ℝ),
            Function.update c idx r ∈ {coins | A_k coins = W} ↔ c ∈ {coins | A_k coins = W} := by
          intro W c r
          simp only [Set.mem_setOf_eq]
          have heq : A_k (Function.update c idx r) = A_k c :=
            h_dep_k (Function.update c idx r) c (fun j hj =>
              Function.update_of_ne (Fin.ne_of_lt hj) r c)
          rw [heq]
        refine ⟨?_, ?_, ?_⟩
        · intro B
          rw [h_fib_eq B]
          split_ifs with hxB
          · exact (h_meas_k (B.erase x)).inter
              ((measurableSet_le measurable_const (measurable_pi_apply idx)).inter
                (measurableSet_lt (measurable_pi_apply idx) measurable_const))
          · exact (h_meas_k B).inter
              ((measurableSet_le measurable_const (measurable_pi_apply idx)).inter
                (measurableSet_lt (measurable_pi_apply idx) measurable_const)).compl
        · intro c₁ c₂ hc
          dsimp only
          rw [h_step_eq c₁, h_step_eq c₂]
          have hA : A_k c₁ = A_k c₂ := h_dep_k c₁ c₂ (fun j hj => hc j (Nat.lt_succ_of_lt hj))
          have h_idx : c₁ idx = c₂ idx := hc idx (Nat.lt_succ_self k)
          by_cases hcond : 0 ≤ c₂ idx ∧ c₂ idx < survivalAcceptProb v x (A_k c₂) S_k (τ_π x)
          · have hcond1 : 0 ≤ c₁ idx ∧ c₁ idx < survivalAcceptProb v x (A_k c₁) S_k (τ_π x) := by
              rwa [hA, h_idx]
            rw [if_pos hcond1, if_pos hcond, hA]
          · have hcond1 : ¬(0 ≤ c₁ idx ∧ c₁ idx < survivalAcceptProb v x (A_k c₁) S_k (τ_π x)) := by
              rwa [hA, h_idx]
            rw [if_neg hcond1, if_neg hcond, hA]
        · intro B
          have h_take_succ : (List.ofFn π).take (k + 1) = L_k ++ [x] := by
            have hlen : k < (List.ofFn π).length := by rw [List.length_ofFn]; exact hk
            dsimp only [L_k, x, idx]
            rw [List.take_add_one, List.getElem?_eq_getElem hlen, Option.toList_some,
              List.getElem_ofFn]
          rw [h_take_succ, h_run_append v τ_π L_k x ∅ dist₀, Finset.empty_union, h_fib_eq B]
          unfold survivalStepDist
          by_cases hxB : x ∈ B
          · rw [if_pos hxB, if_neg (not_not.mpr hxB), if_pos hxB, zero_add]
            let α' := survivalAcceptProb v x (B.erase x) S_k (τ_π x)
            obtain ⟨hα0, hα1⟩ := h_acc_bdd x (B.erase x) S_k (τ_π x) hx_not_Sk hτx_le1
            have hJ : MeasurableSet {r : ℝ | 0 ≤ r ∧ r < α'} := measurableSet_Ico
            have hcyl : μ.real ({coins | A_k coins = B.erase x} ∩ {coins | 0 ≤ coins idx ∧ coins idx < α'}) =
                μ.real {coins | A_k coins = B.erase x} * ν₁.real {r : ℝ | 0 ≤ r ∧ r < α'} :=
              h_cyl_indep idx {coins | A_k coins = B.erase x} {r : ℝ | 0 ≤ r ∧ r < α'}
                (h_meas_k (B.erase x)) (h_upd_indep (B.erase x)) hJ
            have hlaw_er : μ.real {coins | A_k coins = B.erase x} =
                survivalRunDistList v τ_π L_k ∅ dist₀ (B.erase x) := h_law_k (B.erase x)
            dsimp only [α', S_k, L_k, A_k] at hcyl hlaw_er ⊢
            rw [hcyl, hlaw_er, (h_ν₁_Ico hα0 hα1).1]
          · rw [if_neg hxB, if_pos hxB, if_neg hxB, add_zero]
            let α := survivalAcceptProb v x B S_k (τ_π x)
            obtain ⟨hα0, hα1⟩ := h_acc_bdd x B S_k (τ_π x) hx_not_Sk hτx_le1
            have hJ : MeasurableSet {r : ℝ | ¬(0 ≤ r ∧ r < α)} := measurableSet_Ico.compl
            have hcyl : μ.real ({coins | A_k coins = B} ∩ {coins | ¬(0 ≤ coins idx ∧ coins idx < α)}) =
                μ.real {coins | A_k coins = B} * ν₁.real {r : ℝ | ¬(0 ≤ r ∧ r < α)} :=
              h_cyl_indep idx {coins | A_k coins = B} {r : ℝ | ¬(0 ≤ r ∧ r < α)}
                (h_meas_k B) (h_upd_indep B) hJ
            have hlaw_B : μ.real {coins | A_k coins = B} =
                survivalRunDistList v τ_π L_k ∅ dist₀ B := h_law_k B
            dsimp only [α, S_k, L_k, A_k] at hcyl hlaw_B ⊢
            rw [hcyl, hlaw_B, (h_ν₁_Ico hα0 hα1).2]
    have h_n := (h_ind n (le_refl n)).2.2 S
    have h_take_n : (List.ofFn π).take n = List.ofFn π :=
      List.take_of_length_le (by rw [List.length_ofFn])
    rw [h_take_n] at h_n
    exact h_n

  
  have h_seed_meas : ∀ (v : ItemValuation n) (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)),
      MeasurableSet {ω : (Fin n → ℝ) × (Fin n → ℝ) | runDetSelection (gsDetAlg ω) v π = S} := by
    intro v π S
    have h_ind : ∀ (k : ℕ) (hk : k ≤ n) (B : Finset (Fin n)),
        MeasurableSet {ω : (Fin n → ℝ) × (Fin n → ℝ) | (runDetSelectionSteps (gsDetAlg ω) v π k hk).2 = B} := by
      intro k
      induction k with
      | zero =>
        intro hk B
        change MeasurableSet {ω : (Fin n → ℝ) × (Fin n → ℝ) | (∅ : Finset (Fin n)) = B}
        by_cases hB : (∅ : Finset (Fin n)) = B
        · simp only [hB, Set.setOf_true]; exact MeasurableSet.univ
        · simp only [hB, Set.setOf_false]; exact MeasurableSet.empty
      | succ k ih =>
        intro hk B
        let L_k := (List.ofFn π).take k
        let x := π ⟨k, hk⟩
        let oracle : {T : Finset (Fin n) // T ⊆ insert x L_k.toFinset} → WithBot ℝ :=
          fun ⟨T, _⟩ => v T
        have h_eq : {ω : (Fin n → ℝ) × (Fin n → ℝ) |
            (runDetSelectionSteps (gsDetAlg ω) v π (k + 1) hk).2 = B} =
            ⋃ A : Finset (Fin n),
              ((if insert x A = B then
                  {ω | (runDetSelectionSteps (gsDetAlg ω) v π k (Nat.le_of_succ_le hk)).2 = A} ∩
                    {ω | (gsDetAlg ω).step L_k x A oracle = true}
                else ∅) ∪
               (if A = B then
                  {ω | (runDetSelectionSteps (gsDetAlg ω) v π k (Nat.le_of_succ_le hk)).2 = A} ∩
                    {ω | (gsDetAlg ω).step L_k x A oracle = false}
                else ∅)) := by
          ext ω
          have h_fst : (runDetSelectionSteps (gsDetAlg ω) v π k (Nat.le_of_succ_le hk)).1 = L_k :=
            h_run_fst (gsDetAlg ω) v π k (Nat.le_of_succ_le hk)
          simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_union]
          let A₀ := (runDetSelectionSteps (gsDetAlg ω) v π k (Nat.le_of_succ_le hk)).2
          change (if (gsDetAlg ω).step
              (runDetSelectionSteps (gsDetAlg ω) v π k (Nat.le_of_succ_le hk)).1
              x A₀ (fun ⟨T, _⟩ => v T) = true
            then insert x A₀ else A₀) = B ↔ _
          have h_ite_eq : (if (gsDetAlg ω).step
              (runDetSelectionSteps (gsDetAlg ω) v π k (Nat.le_of_succ_le hk)).1
              x A₀ (fun ⟨T, _⟩ => v T) = true
            then insert x A₀ else A₀) =
            (if (gsDetAlg ω).step L_k x A₀ oracle = true
            then insert x A₀ else A₀) :=
            congrArg (fun b : Bool => if b = true then insert x A₀ else A₀)
              (h_step_prev_eq (gsDetAlg ω) v _ L_k x A₀ h_fst)
          rw [h_ite_eq]
          refine ⟨fun h => ⟨A₀, ?_⟩, ?_⟩
          · cases hdec : (gsDetAlg ω).step L_k x A₀ oracle
            · rw [hdec, if_neg Bool.false_ne_true] at h
              right; rw [if_pos h]; exact ⟨rfl, hdec⟩
            · rw [hdec, if_pos rfl] at h
              left; rw [if_pos h]; exact ⟨rfl, hdec⟩
          · rintro ⟨A, hA | hA⟩
            · split_ifs at hA with hins
              · obtain ⟨rfl, hdec⟩ := hA; rw [hdec, if_pos rfl]; exact hins
              · exact False.elim hA
            · split_ifs at hA with heq
              · obtain ⟨rfl, hdec⟩ := hA; rw [hdec, if_neg Bool.false_ne_true]; exact heq
              · exact False.elim hA
        rw [h_eq]
        refine MeasurableSet.iUnion (fun A => MeasurableSet.union ?_ ?_)
        · split_ifs
          · exact (ih (Nat.le_of_succ_le hk) A).inter (h_meas_step L_k x A oracle true)
          · exact MeasurableSet.empty
        · split_ifs
          · exact (ih (Nat.le_of_succ_le hk) A).inter (h_meas_step L_k x A oracle false)
          · exact MeasurableSet.empty
    exact h_ind n (le_refl n) S

  have h_fubini : ∀ (v : ItemValuation n), IsGSValuation v →
      ∀ (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)),
        (μ.prod μ).real {ω | runDetSelection (gsDetAlg ω) v π = S} =
          ∫ u, survivalRunDistList v (fun g => sortedClampedTime u (π.symm g))
            (List.ofFn π) ∅ dist₀ S ∂μ := by
    intro v hv π S
    let E_π := {ω : (Fin n → ℝ) × (Fin n → ℝ) | runDetSelection (gsDetAlg ω) v π = S}
    have hE_π : MeasurableSet E_π := h_seed_meas v π S
    have h_ind_int : Integrable (E_π.indicator (1 : ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ)) (μ.prod μ) := by
      refine MeasureTheory.Integrable.of_mem_Icc 0 1
        (measurable_const.indicator hE_π).aemeasurable
        (Filter.Eventually.of_forall (fun ω => ?_))
      by_cases hω : ω ∈ E_π <;> simp [hω]
    rw [← MeasureTheory.integral_indicator_one hE_π,
      MeasureTheory.integral_prod _ h_ind_int]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    dsimp only
    have h_slice_eq : (fun c : Fin n → ℝ =>
          E_π.indicator (1 : ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ) (u, c)) =
        (Prod.mk u ⁻¹' E_π).indicator (1 : (Fin n → ℝ) → ℝ) := rfl
    have h_slice_meas : MeasurableSet (Prod.mk u ⁻¹' E_π) :=
      hE_π.preimage measurable_prodMk_left
    rw [h_slice_eq, MeasureTheory.integral_indicator_one h_slice_meas]
    exact h_coin_marg v hv u π S

  
  let GoodCube : Set (Fin n → ℝ) :=
    {u | (∀ i : Fin n, 0 ≤ u i ∧ u i ≤ 1) ∧ Function.Injective u}
  let Simplex : Equiv.Perm (Fin n) → Set (Fin n → ℝ) :=
    fun σ => {u | (∀ i : Fin n, 0 ≤ u i ∧ u i ≤ 1) ∧ StrictMono (u ∘ σ)}

  have h_good_ae : ∀ᵐ u ∂μ, u ∈ GoodCube := by
    have h_sing : ∀ c : ℝ, ν₁ {c} = 0 := by
      intro c
      have h_le : volume.restrict (Set.Icc (0 : ℝ) 1) {c} ≤ volume {c} :=
        Measure.restrict_apply_le _ _
      rw [Real.volume_singleton, nonpos_iff_eq_zero] at h_le
      rw [hν₁_eq, h_le]
    have h_ae_icc : ∀ᵐ u ∂μ, ∀ i : Fin n, 0 ≤ u i ∧ u i ≤ 1 := by
      rw [Filter.eventually_all]; intro i
      have h_1d : ∀ᵐ r ∂ν₁, 0 ≤ r ∧ r ≤ 1 := by
        rw [ae_iff]
        have h_compl : {r : ℝ | ¬(0 ≤ r ∧ r ≤ 1)} = (Set.Icc (0 : ℝ) 1)ᶜ := rfl
        rw [h_compl, hν₁_eq, Measure.restrict_apply measurableSet_Icc.compl,
          Set.compl_inter_self, measure_empty]
      exact (MeasureTheory.measurePreserving_eval (fun _ : Fin n => ν₁) i).quasiMeasurePreserving.ae h_1d
    have h_ae_inj : ∀ᵐ u ∂μ, Function.Injective u := by
      have h_pair : ∀ i j : Fin n, ∀ᵐ u ∂μ, i ≠ j → u i ≠ u j := by
        intro i j
        by_cases hij : i = j
        · exact Filter.Eventually.of_forall (fun _ hne => (hne hij).elim)
        · suffices h_neq : ∀ᵐ u ∂μ, u i ≠ u j by exact h_neq.mono (fun _ h _ => h)
          rw [ae_iff]
          have h_set_eq : {u : Fin n → ℝ | ¬(u i ≠ u j)} = {u : Fin n → ℝ | u i = u j} := by
            ext u; simp
          rw [h_set_eq]
          let pred : Fin n → Prop := fun k => k = i
          let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) pred
          let μ_in : Measure ({k : Fin n // pred k} → ℝ) := Measure.pi (fun _ => ν₁)
          let μ_out : Measure ({k : Fin n // ¬ pred k} → ℝ) := Measure.pi (fun _ => ν₁)
          haveI : IsProbabilityMeasure μ_in := by dsimp only [μ_in]; infer_instance
          haveI : IsProbabilityMeasure μ_out := by dsimp only [μ_out]; infer_instance
          have h_mp : MeasurePreserving e μ (μ_in.prod μ_out) := by
            have h_ft : @Measure.pi (Subtype pred) (fun _ => ℝ) (Subtype.fintype pred) _ (fun _ => ν₁) = μ_in :=
              congrArg (fun ft => @Measure.pi (Subtype pred) (fun _ => ℝ) ft _ (fun _ => ν₁)) (Subsingleton.elim _ _)
            rw [← h_ft]
            dsimp only [μ, unifCubeMeasure, μ_out]
            exact MeasureTheory.measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => ν₁) pred
          let i_sub : {k : Fin n // pred k} := ⟨i, rfl⟩
          let j_sub : {k : Fin n // ¬ pred k} := ⟨j, Ne.symm hij⟩
          let E : Set (({k // pred k} → ℝ) × ({k // ¬ pred k} → ℝ)) :=
            {q | q.1 i_sub = q.2 j_sub}
          have hE_meas : MeasurableSet E :=
            measurableSet_eq_fun ((measurable_pi_apply i_sub).comp measurable_fst)
              ((measurable_pi_apply j_sub).comp measurable_snd)
          have h_pre : e ⁻¹' E = {u : Fin n → ℝ | u i = u j} := rfl
          rw [← h_pre, h_mp.measure_preimage hE_meas.nullMeasurableSet,
            MeasureTheory.Measure.prod_apply_symm hE_meas]
          have h_sec : ∀ y : {k // ¬ pred k} → ℝ, μ_in ((fun x => (x, y)) ⁻¹' E) = 0 := by
            intro y
            have h_pre_y : (fun x : {k // pred k} → ℝ => (x, y)) ⁻¹' E =
                (Function.eval i_sub : ({k // pred k} → ℝ) → ℝ) ⁻¹' ({y j_sub} : Set ℝ) := rfl
            rw [h_pre_y,
              (MeasureTheory.measurePreserving_eval (fun _ : {k // pred k} => ν₁) i_sub).measure_preimage
                (measurableSet_singleton (y j_sub)).nullMeasurableSet]
            exact h_sing (y j_sub)
          simp_rw [h_sec, MeasureTheory.lintegral_zero]
      have h_all : ∀ᵐ u ∂μ, ∀ i j : Fin n, i ≠ j → u i ≠ u j := by
        rw [Filter.eventually_all]; intro i; rw [Filter.eventually_all]; exact h_pair i
      exact h_all.mono (fun u hu i j hij => by by_contra hne; exact hu i j hne hij)
    exact h_ae_icc.and h_ae_inj

  have h_simplex_meas : ∀ σ : Equiv.Perm (Fin n), MeasurableSet (Simplex σ) := by
    intro σ
    have h_eq : Simplex σ =
        (⋂ i : Fin n, {u : Fin n → ℝ | 0 ≤ u i} ∩ {u : Fin n → ℝ | u i ≤ 1}) ∩
        (⋂ a : Fin n, ⋂ b : Fin n,
          if a < b then {u : Fin n → ℝ | u (σ a) < u (σ b)} else Set.univ) := by
      ext u
      simp only [Simplex, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, StrictMono,
        Function.comp_apply]
      refine ⟨fun ⟨h1, h2⟩ => ⟨h1, fun a b => ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, fun a b hab => ?_⟩⟩
      · split_ifs with hab
        · exact h2 hab
        · exact trivial
      · specialize h2 a b; rwa [if_pos hab] at h2
    rw [h_eq]
    refine (MeasurableSet.iInter (fun i =>
        (measurableSet_le measurable_const (measurable_pi_apply i)).inter
          (measurableSet_le (measurable_pi_apply i) measurable_const))).inter
      (MeasurableSet.iInter (fun a => MeasurableSet.iInter (fun b => ?_)))
    split_ifs
    · exact measurableSet_lt (measurable_pi_apply (σ a)) (measurable_pi_apply (σ b))
    · exact MeasurableSet.univ

  have h_simplex_disj : ∀ {σ₁ σ₂ : Equiv.Perm (Fin n)} {u : Fin n → ℝ},
      u ∈ Simplex σ₁ → u ∈ Simplex σ₂ → σ₁ = σ₂ := by
    intro σ₁ σ₂ u hu₁ hu₂
    let τ : Equiv.Perm (Fin n) := σ₁.trans σ₂.symm
    have hτ_sm : StrictMono τ := by
      intro a b hab
      have hlt : (u ∘ σ₂) (τ a) < (u ∘ σ₂) (τ b) := by
        dsimp only [τ, Function.comp_apply, Equiv.trans_apply]
        rw [σ₂.apply_symm_apply, σ₂.apply_symm_apply]
        exact hu₁.2 hab
      exact hu₂.2.lt_iff_lt.mp hlt
    have hτ_symm_sm : StrictMono τ.symm := by
      intro a b hab
      by_contra hnot
      have hle : τ.symm b ≤ τ.symm a := not_lt.mp hnot
      have hba : b ≤ a := by
        simpa [τ.apply_symm_apply] using hτ_sm.monotone hle
      exact not_lt_of_ge hba hab
    have h_ge_id : ∀ (f : Fin n → Fin n), StrictMono f → ∀ i : Fin n, i.1 ≤ (f i).1 := by
      intro f hf
      have h_nat : ∀ (m : ℕ) (hm : m < n), m ≤ (f ⟨m, hm⟩).1 := by
        intro m
        induction m with
        | zero => intro _; exact Nat.zero_le _
        | succ m ih =>
          intro hm
          have h1 := ih (Nat.lt_of_succ_lt hm)
          have h2 : (f ⟨m, Nat.lt_of_succ_lt hm⟩).1 < (f ⟨m + 1, hm⟩).1 :=
            Fin.lt_def.mp (hf (Fin.lt_def.mpr (Nat.lt_succ_self m)))
          omega
      exact fun i => h_nat i.1 i.2
    have hτ_id : ∀ i : Fin n, τ i = i := by
      intro i
      apply Fin.ext
      have h1 := h_ge_id τ hτ_sm i
      have h2 := h_ge_id τ.symm hτ_symm_sm (τ i)
      rw [τ.symm_apply_apply] at h2
      omega
    apply Equiv.ext
    intro i
    have hi := congrArg σ₂ (hτ_id i)
    dsimp only [τ, Equiv.trans_apply] at hi
    rwa [σ₂.apply_symm_apply] at hi

  have h_simplex_cover : ∀ {u : Fin n → ℝ}, u ∈ GoodCube →
      ∃ σ : Equiv.Perm (Fin n), u ∈ Simplex σ := by
    intro u ⟨hu_bdd, hu_inj⟩
    let r : Fin n → Fin n → Bool := fun a b => decide (u a ≤ u b)
    let L := (List.finRange n).mergeSort r
    have h_perm : L.Perm (List.finRange n) := List.mergeSort_perm (List.finRange n) r
    have h_len : L.length = n := h_perm.length_eq.trans List.length_finRange
    have h_nd : L.Nodup := h_perm.nodup_iff.mpr (List.nodup_finRange n)
    let f : Fin n → Fin n := fun i => L[i.1]'(i.2.trans_eq h_len.symm)
    have hf_inj : Function.Injective f := by
      intro i j hij
      apply Fin.ext
      exact (h_nd.getElem_inj_iff (hi := i.2.trans_eq h_len.symm)
        (hj := j.2.trans_eq h_len.symm)).mp hij
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj)
    have h_tot : ∀ a b : Fin n, (r a b || r b a) = true := by
      intro a b; simp only [r, Bool.or_eq_true, decide_eq_true_eq]; exact le_total (u a) (u b)
    have h_tr : ∀ a b c : Fin n, r a b = true → r b c = true → r a c = true := by
      intro a b c hab hbc; simp only [r, decide_eq_true_eq] at hab hbc ⊢; exact hab.trans hbc
    have h_pw : L.Pairwise (fun a b => r a b = true) :=
      List.pairwise_mergeSort h_tr h_tot (List.finRange n)
    refine ⟨σ, hu_bdd, fun i j hij => ?_⟩
    have hle : u (σ i) ≤ u (σ j) := by
      have hr := List.pairwise_iff_getElem.mp h_pw i.1 j.1
        (i.2.trans_eq h_len.symm) (j.2.trans_eq h_len.symm) (Fin.lt_def.mp hij)
      simpa only [r, decide_eq_true_eq] using hr
    have hne : u (σ i) ≠ u (σ j) := fun heq => (ne_of_lt hij) (σ.injective (hu_inj heq))
    exact lt_of_le_of_ne hle hne

  have h_simplex_sort_finRange : ∀ {σ : Equiv.Perm (Fin n)} {u : Fin n → ℝ},
      u ∈ Simplex σ → sortedClampedList u = List.ofFn σ := by
    intro σ u ⟨hu_bdd, hu_sm⟩
    have hu_inj : Function.Injective u := by
      intro a b hab
      have h_eq : (u ∘ σ) (σ.symm a) = (u ∘ σ) (σ.symm b) := by
        simp [Function.comp_apply, hab]
      exact σ.symm.injective (hu_sm.injective h_eq)
    have h_cmp_eq : (fun a b : Fin n => decide (clamp01 (u a) ≤ clamp01 (u b))) =
        (fun a b : Fin n => decide (u a ≤ u b)) := by
      ext a b
      rw [h_clamp_id (hu_bdd a).1 (hu_bdd a).2, h_clamp_id (hu_bdd b).1 (hu_bdd b).2]
    unfold sortedClampedList
    rw [h_cmp_eq]
    let r : Fin n → Fin n → Bool := fun a b => decide (u a ≤ u b)
    have h_perm1 : ((List.finRange n).mergeSort r).Perm (List.finRange n) :=
      List.mergeSort_perm (List.finRange n) r
    have h_perm2 : (List.ofFn σ).Perm (List.finRange n) :=
      (List.perm_ext_iff_of_nodup (List.nodup_ofFn.mpr σ.injective) (List.nodup_finRange n)).mpr
        (fun x => by simp [List.mem_ofFn, σ.surjective x])
    have h_perm : ((List.finRange n).mergeSort r).Perm (List.ofFn σ) :=
      h_perm1.trans h_perm2.symm
    have h_tot : ∀ a b : Fin n, (r a b || r b a) = true := by
      intro a b; simp only [r, Bool.or_eq_true, decide_eq_true_eq]; exact le_total (u a) (u b)
    have h_tr : ∀ a b c : Fin n, r a b = true → r b c = true → r a c = true := by
      intro a b c hab hbc; simp only [r, decide_eq_true_eq] at hab hbc ⊢; exact hab.trans hbc
    have h_pw1 : ((List.finRange n).mergeSort r).Pairwise (fun a b => r a b = true) :=
      List.pairwise_mergeSort h_tr h_tot (List.finRange n)
    have h_pw2 : (List.ofFn σ).Pairwise (fun a b => r a b = true) := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      rw [List.length_ofFn] at hi hj
      simp only [List.getElem_ofFn, r, decide_eq_true_eq]
      exact (hu_sm (Fin.lt_def.mpr hij)).le
    exact h_perm.eq_of_pairwise (fun a b _ _ hab hba => by
      simp only [r, decide_eq_true_eq] at hab hba
      exact hu_inj (le_antisymm hab hba)) h_pw1 h_pw2

  have h_simplex_sort_univ : ∀ {π : Equiv.Perm (Fin n)} {τ : Fin n → ℝ},
      τ ∈ Simplex π →
        ((Finset.univ : Finset (Fin n)).sort (· ≤ ·)).mergeSort
          (fun a b => decide (τ a ≤ τ b)) = List.ofFn π := by
    intro π τ ⟨_, hτ_sm⟩
    have hτ_inj : Function.Injective τ := by
      intro a b hab
      have h_eq : (τ ∘ π) (π.symm a) = (τ ∘ π) (π.symm b) := by
        simp [Function.comp_apply, hab]
      exact π.symm.injective (hτ_sm.injective h_eq)
    let r : Fin n → Fin n → Bool := fun a b => decide (τ a ≤ τ b)
    let L₀ := (Finset.univ : Finset (Fin n)).sort (· ≤ ·)
    have h_perm1 : (L₀.mergeSort r).Perm L₀ := List.mergeSort_perm L₀ r
    have h_nd0 : L₀.Nodup := (Finset.univ : Finset (Fin n)).sort_nodup (· ≤ ·)
    have h_perm2 : L₀.Perm (List.ofFn π) :=
      (List.perm_ext_iff_of_nodup h_nd0 (List.nodup_ofFn.mpr π.injective)).mpr
        (fun x => by simp [L₀, Finset.mem_sort, List.mem_ofFn, π.surjective x])
    have h_perm : (L₀.mergeSort r).Perm (List.ofFn π) := h_perm1.trans h_perm2
    have h_tot : ∀ a b : Fin n, (r a b || r b a) = true := by
      intro a b; simp only [r, Bool.or_eq_true, decide_eq_true_eq]; exact le_total (τ a) (τ b)
    have h_tr : ∀ a b c : Fin n, r a b = true → r b c = true → r a c = true := by
      intro a b c hab hbc; simp only [r, decide_eq_true_eq] at hab hbc ⊢; exact hab.trans hbc
    have h_pw1 : (L₀.mergeSort r).Pairwise (fun a b => r a b = true) :=
      List.pairwise_mergeSort h_tr h_tot L₀
    have h_pw2 : (List.ofFn π).Pairwise (fun a b => r a b = true) := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      rw [List.length_ofFn] at hi hj
      simp only [List.getElem_ofFn, r, decide_eq_true_eq]
      exact (hτ_sm (Fin.lt_def.mpr hij)).le
    exact h_perm.eq_of_pairwise (fun a b _ _ hab hba => by
      simp only [r, decide_eq_true_eq] at hab hba
      exact hτ_inj (le_antisymm hab hba)) h_pw1 h_pw2

  
  have h_run_meas_bdd : ∀ (v : ItemValuation n), IsGSValuation v →
      ∀ (L : List (Fin n)) (τ_fn : (Fin n → ℝ) → (Fin n → ℝ)),
        L.Nodup →
        Measurable τ_fn →
        (∀ u x, τ_fn u x ≤ 1) →
        ∀ B : Finset (Fin n),
          Measurable (fun u => survivalRunDistList v (τ_fn u) L ∅ dist₀ B) ∧
          (∀ u, 0 ≤ survivalRunDistList v (τ_fn u) L ∅ dist₀ B ∧
                survivalRunDistList v (τ_fn u) L ∅ dist₀ B ≤ 1) := by
    intro v hv L τ_fn hnd_L hτ_m hτ_le1
    obtain ⟨h_acc_bdd, _, _, _⟩ := H_surv v hv
    have h_gen : ∀ (M : List (Fin n)) (S₀ : Finset (Fin n))
        (d_fn : (Fin n → ℝ) → Finset (Fin n) → ℝ),
        M.Nodup → Disjoint M.toFinset S₀ →
        (∀ W, Measurable (fun u => d_fn u W)) →
        (∀ u W, ¬(W ⊆ S₀) → d_fn u W = 0) →
        (∀ u W, 0 ≤ d_fn u W) →
        (∀ u, (∑ W ∈ S₀.powerset, d_fn u W) = 1) →
        ∀ B : Finset (Fin n),
          Measurable (fun u => survivalRunDistList v (τ_fn u) M S₀ (d_fn u) B) ∧
          (∀ u, 0 ≤ survivalRunDistList v (τ_fn u) M S₀ (d_fn u) B ∧
                survivalRunDistList v (τ_fn u) M S₀ (d_fn u) B ≤ 1) := by
      intro M
      induction M with
      | nil =>
        intro S₀ d_fn _ _ hd_m hd_supp hd_nn hd_sum B
        dsimp only [survivalRunDistList]
        refine ⟨hd_m B, fun u => ⟨hd_nn u B, ?_⟩⟩
        by_cases hBS : B ⊆ S₀
        · calc d_fn u B ≤ ∑ C ∈ S₀.powerset, d_fn u C :=
                Finset.single_le_sum (fun C _ => hd_nn u C) (Finset.mem_powerset.mpr hBS)
            _ = 1 := hd_sum u
        · rw [hd_supp u B hBS]; exact zero_le_one
      | cons x xs ih =>
        intro S₀ d_fn hnd hdj hd_m hd_supp hd_nn hd_sum B
        obtain ⟨hx_xs, hnd_xs⟩ := List.nodup_cons.mp hnd
        have hxS : x ∉ S₀ := Finset.disjoint_left.mp hdj (by simp)
        have hdj_xs : Disjoint xs.toFinset (insert x S₀) := by
          rw [Finset.disjoint_left]; intro z hz hzin
          rcases Finset.mem_insert.mp hzin with rfl | hzS
          · exact hx_xs (List.mem_toFinset.mp hz)
          · exact Finset.disjoint_left.mp hdj (by simp [List.mem_toFinset.mp hz]) hzS
        let d₁_fn : (Fin n → ℝ) → Finset (Fin n) → ℝ :=
          fun u => survivalStepDist v S₀ x (τ_fn u x) (d_fn u)
        have hd₁_m : ∀ W, Measurable (fun u => d₁_fn u W) := by
          intro W
          dsimp only [d₁_fn, survivalStepDist]
          have h_tx : Measurable (fun u => τ_fn u x) := (measurable_pi_apply x).comp hτ_m
          refine Measurable.add ?_ ?_
          · by_cases hxW : x ∉ W
            · simp_rw [if_pos hxW]
              exact (hd_m W).mul (measurable_const.sub ((h_α_meas v x W S₀).comp h_tx))
            · simp_rw [if_neg hxW]; exact measurable_const
          · by_cases hxW : x ∈ W
            · simp_rw [if_pos hxW]
              exact (hd_m (W.erase x)).mul ((h_α_meas v x (W.erase x) S₀).comp h_tx)
            · simp_rw [if_neg hxW]; exact measurable_const
        have hd₁_supp : ∀ u W, ¬(W ⊆ insert x S₀) → d₁_fn u W = 0 := by
          intro u W hW
          dsimp only [d₁_fn, survivalStepDist]
          have hW_notS : ¬(W ⊆ S₀) := fun h => hW (h.trans (Finset.subset_insert x S₀))
          have h1 : (if x ∉ W then d_fn u W * (1 - survivalAcceptProb v x W S₀ (τ_fn u x)) else 0) = 0 := by
            by_cases hxW : x ∉ W
            · rw [if_pos hxW, hd_supp u W hW_notS, zero_mul]
            · rw [if_neg hxW]
          have h2 : (if x ∈ W then d_fn u (W.erase x) *
              survivalAcceptProb v x (W.erase x) S₀ (τ_fn u x) else 0) = 0 := by
            split_ifs with hxW
            · have her : ¬(W.erase x ⊆ S₀) := fun h =>
                hW (Finset.insert_erase hxW ▸ Finset.insert_subset_insert x h)
              rw [hd_supp u (W.erase x) her, zero_mul]
            · rfl
          rw [h1, h2, add_zero]
        have hd₁_nn : ∀ u W, 0 ≤ d₁_fn u W := by
          intro u W
          dsimp only [d₁_fn, survivalStepDist]
          refine add_nonneg ?_ ?_
          · by_cases hxW : x ∉ W
            · rw [if_pos hxW]
              exact mul_nonneg (hd_nn u W)
                (sub_nonneg.mpr (h_acc_bdd x W S₀ (τ_fn u x) hxS (hτ_le1 u x)).2)
            · rw [if_neg hxW]
          · split_ifs
            · exact mul_nonneg (hd_nn u (W.erase x))
                (h_acc_bdd x (W.erase x) S₀ (τ_fn u x) hxS (hτ_le1 u x)).1
            · exact le_rfl
        have hd₁_sum : ∀ u, (∑ W ∈ (insert x S₀).powerset, d₁_fn u W) = 1 := by
          intro u
          rw [Finset.powerset_insert]
          have h_disj_p : Disjoint S₀.powerset (S₀.powerset.image (insert x)) := by
            rw [Finset.disjoint_left]; intro W hW hWi
            obtain ⟨Z, _, rfl⟩ := Finset.mem_image.mp hWi
            exact hxS ((Finset.mem_powerset.mp hW) (Finset.mem_insert_self x Z))
          rw [Finset.sum_union h_disj_p]
          have h_out : (∑ W ∈ S₀.powerset, d₁_fn u W) =
              ∑ Z ∈ S₀.powerset, d_fn u Z * (1 - survivalAcceptProb v x Z S₀ (τ_fn u x)) := by
            refine Finset.sum_congr rfl (fun Z hZ => ?_)
            have hxZ : x ∉ Z := fun h => hxS ((Finset.mem_powerset.mp hZ) h)
            dsimp only [d₁_fn, survivalStepDist]
            rw [if_pos hxZ, if_neg hxZ, add_zero]
          have h_in : (∑ W ∈ S₀.powerset.image (insert x), d₁_fn u W) =
              ∑ Z ∈ S₀.powerset, d_fn u Z * survivalAcceptProb v x Z S₀ (τ_fn u x) := by
            rw [Finset.sum_image]
            · refine Finset.sum_congr rfl (fun Z hZ => ?_)
              have hxZ : x ∉ Z := fun h => hxS ((Finset.mem_powerset.mp hZ) h)
              have hx_ins : x ∈ insert x Z := Finset.mem_insert_self x Z
              dsimp only [d₁_fn, survivalStepDist]
              rw [if_neg (not_not.mpr hx_ins), if_pos hx_ins, Finset.erase_insert hxZ, zero_add]
            · intro Z₁ hZ₁ Z₂ hZ₂ heq
              have hx₁ : x ∉ Z₁ := fun h => hxS ((Finset.mem_powerset.mp hZ₁) h)
              have hx₂ : x ∉ Z₂ := fun h => hxS ((Finset.mem_powerset.mp hZ₂) h)
              have her := congrArg (fun X : Finset (Fin n) => X.erase x) heq
              simpa [Finset.erase_insert hx₁, Finset.erase_insert hx₂] using her
          rw [h_out, h_in, ← Finset.sum_add_distrib]
          have h_coll : (∑ Z ∈ S₀.powerset,
              (d_fn u Z * (1 - survivalAcceptProb v x Z S₀ (τ_fn u x)) +
               d_fn u Z * survivalAcceptProb v x Z S₀ (τ_fn u x))) =
              ∑ Z ∈ S₀.powerset, d_fn u Z :=
            Finset.sum_congr rfl (fun Z _ => by ring)
          rw [h_coll, hd_sum u]
        exact ih (insert x S₀) d₁_fn hnd_xs hdj_xs hd₁_m hd₁_supp hd₁_nn hd₁_sum B
    refine h_gen L ∅ (fun _ => dist₀) hnd_L (Finset.disjoint_empty_right _)
      (fun _ => measurable_const) ?_ ?_ ?_
    · intro _ W hW; simp only [Finset.subset_empty] at hW; exact if_neg hW
    · intro _ W; dsimp only [dist₀]; split_ifs <;> norm_num
    · intro _; simp [dist₀]

  
  refine ⟨{ Seed := (Fin n → ℝ) × (Fin n → ℝ)
            measSeed := inferInstance
            seedMeasure := μ.prod μ
            isProb := inferInstance
            det := gsDetAlg
            meas_step := h_meas_step }, fun v hv => ⟨?_, h_det_safe v hv⟩⟩
  intro S
  let clampVec : (Fin n → ℝ) → (Fin n → ℝ) := fun τ i => clamp01 (τ i)
  let onlineRun : (Fin n → ℝ) → ℝ := fun τ =>
    survivalRunDistList v τ
      (((Finset.univ : Finset (Fin n)).sort (· ≤ ·)).mergeSort (fun a b => decide (τ a ≤ τ b)))
      ∅ dist₀ S
  have h_clampVec_meas : Measurable clampVec :=
    measurable_pi_iff.mpr (fun i => h_clamp_meas.comp (measurable_pi_apply i))
  have h_clampVec_id : ∀ {τ : Fin n → ℝ}, (∀ i : Fin n, 0 ≤ τ i ∧ τ i ≤ 1) → clampVec τ = τ := by
    intro τ hτ; ext i; exact h_clamp_id (hτ i).1 (hτ i).2
  have h_onlineRun_cl_meas_bdd :
      Measurable (fun τ => onlineRun (clampVec τ)) ∧
      (∀ τ, 0 ≤ onlineRun (clampVec τ) ∧ onlineRun (clampVec τ) ≤ 1) := by
    let cmpOf : (Fin n → ℝ) → (Fin n → Fin n → Bool) :=
      fun τ a b => decide (clampVec τ a ≤ clampVec τ b)
    have h_sum_eq : (fun τ : Fin n → ℝ => onlineRun (clampVec τ)) =
        fun τ => ∑ c ∈ (Finset.univ : Finset (Fin n → Fin n → Bool)),
          if cmpOf τ = c then
            survivalRunDistList v (clampVec τ)
              (((Finset.univ : Finset (Fin n)).sort (· ≤ ·)).mergeSort c) ∅ dist₀ S
          else 0 := by
      ext τ
      rw [Finset.sum_ite_eq Finset.univ (cmpOf τ) _, if_pos (Finset.mem_univ _)]
    refine ⟨?_, ?_⟩
    · rw [h_sum_eq]
      refine Finset.measurable_sum Finset.univ (fun c _ => ?_)
      have h_set_c : MeasurableSet {τ : Fin n → ℝ | cmpOf τ = c} := by
        have h_iinter : {τ : Fin n → ℝ | cmpOf τ = c} =
            ⋂ a : Fin n, ⋂ b : Fin n,
              {τ : Fin n → ℝ | decide (clampVec τ a ≤ clampVec τ b) = c a b} := by
          ext τ; simp [cmpOf, funext_iff]
        rw [h_iinter]
        refine MeasurableSet.iInter (fun a => MeasurableSet.iInter (fun b => ?_))
        have ha : Measurable (fun τ : Fin n → ℝ => clampVec τ a) :=
          h_clamp_meas.comp (measurable_pi_apply a)
        have hb : Measurable (fun τ : Fin n → ℝ => clampVec τ b) :=
          h_clamp_meas.comp (measurable_pi_apply b)
        cases hcab : c a b
        · have hf : {τ : Fin n → ℝ | decide (clampVec τ a ≤ clampVec τ b) = false} =
              {τ : Fin n → ℝ | clampVec τ a ≤ clampVec τ b}ᶜ := by ext τ; simp
          rw [hf]; exact (measurableSet_le ha hb).compl
        · have ht : {τ : Fin n → ℝ | decide (clampVec τ a ≤ clampVec τ b) = true} =
              {τ : Fin n → ℝ | clampVec τ a ≤ clampVec τ b} := by ext τ; simp
          rw [ht]; exact measurableSet_le ha hb
      have h_nd_c : (((Finset.univ : Finset (Fin n)).sort (· ≤ ·)).mergeSort c).Nodup :=
        (List.mergeSort_perm _ c).nodup_iff.mpr ((Finset.univ : Finset (Fin n)).sort_nodup (· ≤ ·))
      exact Measurable.ite h_set_c
        (h_run_meas_bdd v hv _ clampVec h_nd_c h_clampVec_meas
          (fun u x => (h_clamp_bounds (u x)).2) S).1
        measurable_const
    · intro τ
      have h_nd_τ : (((Finset.univ : Finset (Fin n)).sort (· ≤ ·)).mergeSort
          (fun a b => decide (clampVec τ a ≤ clampVec τ b))).Nodup :=
        (List.mergeSort_perm _ _).nodup_iff.mpr ((Finset.univ : Finset (Fin n)).sort_nodup (· ≤ ·))
      exact (h_run_meas_bdd v hv _ clampVec h_nd_τ h_clampVec_meas
        (fun u x => (h_clamp_bounds (u x)).2) S).2 τ

  have h_onl_int : Integrable (fun τ => onlineRun (clampVec τ)) μ :=
    MeasureTheory.Integrable.of_mem_Icc 0 1 h_onlineRun_cl_meas_bdd.1.aemeasurable
      (Filter.Eventually.of_forall h_onlineRun_cl_meas_bdd.2)

  have h_pi_integral : ∀ π : Equiv.Perm (Fin n),
      (μ.prod μ).real {ω | runDetSelection (gsDetAlg ω) v π = S} =
        (Nat.factorial n : ℝ) *
          ∫ τ, (Simplex π).indicator (fun τ => onlineRun (clampVec τ)) τ ∂μ := by
    intro π
    rw [h_fubini v hv π S]
    let F_π : (Fin n → ℝ) → ℝ := fun u =>
      survivalRunDistList v (fun g => sortedClampedTime u (π.symm g))
        (List.ofFn π) ∅ dist₀ S
    have hF_meas_bdd := h_run_meas_bdd v hv (List.ofFn π)
      (fun u g => sortedClampedTime u (π.symm g))
      (List.nodup_ofFn.mpr π.injective)
      (measurable_pi_iff.mpr (fun g => h_t_meas (π.symm g)))
      (fun u g => (h_t_bounds u (π.symm g)).2) S
    have hF_int : Integrable F_π μ :=
      MeasureTheory.Integrable.of_mem_Icc 0 1 hF_meas_bdd.1.aemeasurable
        (Filter.Eventually.of_forall hF_meas_bdd.2)
    have h_ae_sum : F_π =ᵐ[μ] fun u =>
        ∑ σ : Equiv.Perm (Fin n), (Simplex σ).indicator F_π u := by
      refine h_good_ae.mono (fun u hu => ?_)
      obtain ⟨σ₀, hσ₀⟩ := h_simplex_cover hu
      dsimp only
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ σ₀),
        Set.indicator_of_mem hσ₀]
      have h_rest : (∑ σ ∈ Finset.univ.erase σ₀, (Simplex σ).indicator F_π u) = 0 :=
        Finset.sum_eq_zero (fun σ hσ => Set.indicator_of_notMem (fun huσ =>
          (Finset.mem_erase.mp hσ).1 (h_simplex_disj huσ hσ₀)) _)
      rw [h_rest, add_zero]
    have h_sum_int : (∫ u, F_π u ∂μ) =
        ∑ σ : Equiv.Perm (Fin n), ∫ u, (Simplex σ).indicator F_π u ∂μ := by
      rw [MeasureTheory.integral_congr_ae h_ae_sum,
        MeasureTheory.integral_finset_sum Finset.univ
          (fun σ _ => hF_int.indicator (h_simplex_meas σ))]
    have h_each_σ : ∀ σ : Equiv.Perm (Fin n),
        (∫ u, (Simplex σ).indicator F_π u ∂μ) =
          ∫ τ, (Simplex π).indicator (fun τ => onlineRun (clampVec τ)) τ ∂μ := by
      intro σ
      let ρ : Equiv.Perm (Fin n) := π.symm.trans σ
      let Φ_ρ : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
        (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) ρ).symm
      have h_Φ_apply : ∀ (u : Fin n → ℝ) (g : Fin n), Φ_ρ u g = u (ρ g) :=
        fun u g => Equiv.piCongrLeft_symm_apply (fun _ : Fin n => ℝ) ρ u g
      have h_mp : MeasurePreserving Φ_ρ μ μ := by
        dsimp only [μ, unifCubeMeasure, Φ_ρ]
        exact (MeasureTheory.measurePreserving_piCongrLeft (fun _ : Fin n => ν₁) ρ).symm
      have h_pt : ∀ u : Fin n → ℝ,
          (Simplex σ).indicator F_π u =
            (Simplex π).indicator (fun τ => onlineRun (clampVec τ)) (Φ_ρ u) := by
        intro u
        have h_mem_iff : u ∈ Simplex σ ↔ Φ_ρ u ∈ Simplex π := by
          simp only [Simplex, Set.mem_setOf_eq]
          have h_bdd_iff : (∀ i : Fin n, 0 ≤ u i ∧ u i ≤ 1) ↔
              (∀ g : Fin n, 0 ≤ Φ_ρ u g ∧ Φ_ρ u g ≤ 1) := by
            simp_rw [h_Φ_apply]
            exact ⟨fun h g => h (ρ g), fun h i => by simpa [ρ.apply_symm_apply] using h (ρ.symm i)⟩
          have h_comp_eq : (Φ_ρ u) ∘ π = u ∘ σ := by
            ext k; simp [Function.comp_apply, h_Φ_apply, ρ]
          rw [h_bdd_iff, h_comp_eq]
        by_cases hu : u ∈ Simplex σ
        · have hΦu : Φ_ρ u ∈ Simplex π := h_mem_iff.mp hu
          rw [Set.indicator_of_mem hu, Set.indicator_of_mem hΦu]
          have h_cl_Φ : clampVec (Φ_ρ u) = Φ_ρ u := h_clampVec_id hΦu.1
          have h_sort_u : sortedClampedList u = List.ofFn σ := h_simplex_sort_finRange hu
          have h_τ_eq : (fun g : Fin n => sortedClampedTime u (π.symm g)) = Φ_ρ u := by
            ext g
            unfold sortedClampedTime
            have hlen : (π.symm g).1 < (sortedClampedList u).length := by
              rw [sortedClampedList, List.length_mergeSort, List.length_finRange]
              exact (π.symm g).2
            have h_get : (sortedClampedList u)[(π.symm g).1]'hlen = σ (π.symm g) := by
              have hlen2 : (π.symm g).1 < (List.ofFn σ).length := by
                rw [List.length_ofFn]; exact (π.symm g).2
              have h_opt : (sortedClampedList u)[(π.symm g).1]? = (List.ofFn σ)[(π.symm g).1]? := by
                rw [h_sort_u]
              rw [List.getElem?_eq_getElem hlen, List.getElem?_eq_getElem hlen2,
                Option.some.injEq, List.getElem_ofFn] at h_opt
              exact h_opt
            change clamp01 (u ((sortedClampedList u)[(π.symm g).1]'hlen)) = Φ_ρ u g
            rw [h_get, h_clamp_id (hu.1 (σ (π.symm g))).1 (hu.1 (σ (π.symm g))).2, h_Φ_apply]
            rfl
          have h_ord_Φ := h_simplex_sort_univ hΦu
          dsimp only [F_π, onlineRun]
          rw [h_cl_Φ, h_τ_eq, h_ord_Φ]
        · have hΦu : Φ_ρ u ∉ Simplex π := fun h => hu (h_mem_iff.mpr h)
          rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hΦu]
      simp_rw [h_pt]
      have h_f_aesm : MeasureTheory.AEStronglyMeasurable
          ((Simplex π).indicator (fun τ => onlineRun (clampVec τ))) (Measure.map Φ_ρ μ) := by
        rw [h_mp.map_eq]
        exact (h_onl_int.indicator (h_simplex_meas π)).aestronglyMeasurable
      rw [← MeasureTheory.integral_map Φ_ρ.measurable.aemeasurable h_f_aesm, h_mp.map_eq]
    change (∫ u, F_π u ∂μ) = _
    rw [h_sum_int]
    simp_rw [h_each_σ]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

  dsimp only [algSelectionProb]
  simp_rw [h_pi_integral, ← Finset.mul_sum]
  have h_fac_ne : (Nat.factorial n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h_cancel : (1 / (Nat.factorial n : ℝ)) *
      ((Nat.factorial n : ℝ) *
        ∑ π : Equiv.Perm (Fin n),
          ∫ τ, (Simplex π).indicator (fun τ => onlineRun (clampVec τ)) τ ∂μ) =
      ∑ π : Equiv.Perm (Fin n),
        ∫ τ, (Simplex π).indicator (fun τ => onlineRun (clampVec τ)) τ ∂μ := by
    field_simp [h_fac_ne]
  rw [h_cancel, ← MeasureTheory.integral_finset_sum Finset.univ
    (fun π _ => h_onl_int.indicator (h_simplex_meas π))]
  unfold onlineSurvivalLaw
  refine MeasureTheory.integral_congr_ae (h_good_ae.mono (fun τ hτ => ?_))
  obtain ⟨π₀, hπ₀⟩ := h_simplex_cover hτ
  dsimp only
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ π₀),
    Set.indicator_of_mem hπ₀]
  have h_rest : (∑ π ∈ Finset.univ.erase π₀,
      (Simplex π).indicator (fun τ => onlineRun (clampVec τ)) τ) = 0 :=
    Finset.sum_eq_zero (fun π hπ => Set.indicator_of_notMem (fun hτπ =>
      (Finset.mem_erase.mp hπ).1 (h_simplex_disj hτπ hπ₀)) _)
  rw [h_rest, add_zero, h_clampVec_id hτ.1]

 have h_s5 : ∀ (v : ItemValuation n), IsGSValuation v →
     (∀ g ∈ canonicalDemand v Finset.univ,
       (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => g ∈ S),
         survivalLaw v Finset.univ 1 S) = invE) ∧
     (invE * optVal v ≤ ∑ S : Finset (Fin n), survivalLaw v Finset.univ 1 S * realVal v S) := by
  intro v hv
  have h_sub : ∀ T : Finset (Fin n), canonicalDemand v T ⊆ T :=
    (gs_canonical_safe_and_contract n v hv).1
  have h_pers : ∀ T U : Finset (Fin n), T ⊆ U → canonicalDemand v U ∩ T ⊆ canonicalDemand v T :=
    (gs_canonical_safe_and_contract n v hv).2.1
  have h_surv : ∀ S A : Finset (Fin n),
      0 ≤ survivalLaw v S 1 A ∧ (0 < survivalLaw v S 1 A → ∃ T ⊆ S, A ⊆ canonicalDemand v T) :=
    fun S A => (survival_accept_bounds_and_support n v hv).2.1 S A 1
      (by unfold invE; exact Real.exp_le_one_iff.mpr (by norm_num)) le_rfl
  have h_invE_pos : 0 < invE := by unfold invE; exact Real.exp_pos (-1)
  have h_invE_le_one : invE ≤ 1 := by unfold invE; exact Real.exp_le_one_iff.mpr (by norm_num)
  have h_exp_invE : Real.exp 1 * invE = 1 := by
    unfold invE; rw [← Real.exp_add]; norm_num
  let C := canonicalDemand v
  let β₁ : Fin n → ℝ := fun _ => 1
  have h_dt_bounds : ∀ (τ : Fin n → ℝ) (g : Fin n),
      invE ≤ deathTime C 1 Finset.univ ∅ τ β₁ g ∧ deathTime C 1 Finset.univ ∅ τ β₁ g ≤ 1 := by
    intro τ g
    let E : Set ℝ := {u : ℝ | invE ≤ u ∧ u ≤ 1 ∧ g ∉ C (presentSet Finset.univ ∅ τ β₁ u)} ∪ {1}
    have h1E : (1 : ℝ) ∈ E := Set.mem_union_right _ rfl
    have h_lo_E : ∀ u ∈ E, invE ≤ u := by
      rintro u (hu | hu)
      · exact hu.1
      · rw [Set.mem_singleton_iff.mp hu]; exact h_invE_le_one
    exact ⟨le_csInf ⟨1, h1E⟩ h_lo_E, csInf_le ⟨invE, h_lo_E⟩ h1E⟩
  have h_ret_bounds : ∀ (τ : Fin n → ℝ) (g : Fin n),
      0 ≤ retentionProb C 1 Finset.univ ∅ τ β₁ g ∧ retentionProb C 1 Finset.univ ∅ τ β₁ g ≤ 1 := by
    intro τ g
    unfold retentionProb
    split_ifs with hτ
    · obtain ⟨h_lo, h_hi⟩ := h_dt_bounds τ g
      have hexp1 : 1 ≤ Real.exp 1 * deathTime C 1 Finset.univ ∅ τ β₁ g := by
        calc (1 : ℝ) = Real.exp 1 * invE := h_exp_invE.symm
          _ ≤ Real.exp 1 * deathTime C 1 Finset.univ ∅ τ β₁ g :=
            mul_le_mul_of_nonneg_left h_lo (Real.exp_pos 1).le
      have hexp2 : Real.exp 1 * deathTime C 1 Finset.univ ∅ τ β₁ g ≤ Real.exp 1 := by
        calc Real.exp 1 * deathTime C 1 Finset.univ ∅ τ β₁ g ≤ Real.exp 1 * 1 :=
            mul_le_mul_of_nonneg_left h_hi (Real.exp_pos 1).le
          _ = Real.exp 1 := mul_one _
      refine ⟨Real.log_nonneg hexp1, ?_⟩
      calc Real.log (Real.exp 1 * deathTime C 1 Finset.univ ∅ τ β₁ g)
          ≤ Real.log (Real.exp 1) := Real.log_le_log (by linarith) hexp2
        _ = 1 := Real.log_exp 1
    · exact ⟨le_rfl, zero_le_one⟩
  have h_prod_bounds : ∀ (τ : Fin n → ℝ) (A : Finset (Fin n)),
      0 ≤ retainProd C 1 Finset.univ ∅ τ β₁ A ∧ retainProd C 1 Finset.univ ∅ τ β₁ A ≤ 1 := by
    intro τ A
    unfold retainProd
    rw [if_pos (Finset.subset_univ A)]
    have h1_nn : 0 ≤ ∏ g ∈ A, retentionProb C 1 Finset.univ ∅ τ β₁ g :=
      Finset.prod_nonneg (fun g _ => (h_ret_bounds τ g).1)
    have h1_le : ∏ g ∈ A, retentionProb C 1 Finset.univ ∅ τ β₁ g ≤ 1 :=
      Finset.prod_le_one (fun g _ => (h_ret_bounds τ g).1) (fun g _ => (h_ret_bounds τ g).2)
    have h2_nn : 0 ≤ ∏ g ∈ Finset.univ \ A, (1 - retentionProb C 1 Finset.univ ∅ τ β₁ g) :=
      Finset.prod_nonneg (fun g _ => sub_nonneg.mpr (h_ret_bounds τ g).2)
    have h2_le : ∏ g ∈ Finset.univ \ A, (1 - retentionProb C 1 Finset.univ ∅ τ β₁ g) ≤ 1 :=
      Finset.prod_le_one (fun g _ => sub_nonneg.mpr (h_ret_bounds τ g).2)
        (fun g _ => sub_le_self 1 (h_ret_bounds τ g).1)
    exact ⟨mul_nonneg h1_nn h2_nn, mul_le_one₀ h1_le h2_nn h2_le⟩
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
            (f a ω) ⊓ (s.inf' hne (fun c => f c ω)) :=
          fun ω => Finset.inf'_insert hne (fun c => f c ω)
        simp_rw [h_eq]
        exact (hf a (Finset.mem_insert_self a s)).inf
          (ih hne (fun c hc => hf c (Finset.mem_insert_of_mem hc)))
  have h_dt_cand_eq : ∀ (τ : Fin n → ℝ) (g : Fin n),
      let Cand := Bool ⊕ Fin n
      let candVal : Cand → ℝ := fun c => match c with
        | Sum.inl true => invE
        | Sum.inl false => 1
        | Sum.inr z => τ z
      let candEff : Cand → ℝ := fun c =>
        let u := candVal c
        if invE ≤ u ∧ u ≤ 1 ∧ g ∉ C (presentSet Finset.univ ∅ τ β₁ u) then u else 1
      deathTime C 1 Finset.univ ∅ τ β₁ g =
        (Finset.univ : Finset Cand).inf' ⟨Sum.inl true, Finset.mem_univ _⟩ candEff := by
    intro τ g Cand candVal candEff
    let E : Set ℝ := {u : ℝ | invE ≤ u ∧ u ≤ 1 ∧ g ∉ C (presentSet Finset.univ ∅ τ β₁ u)} ∪ {1}
    have h1E : (1 : ℝ) ∈ E := Set.mem_union_right _ rfl
    have hBdd : BddBelow E := ⟨invE, by
      rintro u (hu | hu)
      · exact hu.1
      · rw [Set.mem_singleton_iff.mp hu]; exact h_invE_le_one⟩
    have hne : (Finset.univ : Finset Cand).Nonempty := ⟨Sum.inl true, Finset.mem_univ _⟩
    apply le_antisymm
    · refine Finset.le_inf' hne candEff (fun c _ => csInf_le hBdd ?_)
      dsimp only [candEff]
      split_ifs with hc
      · exact Set.mem_union_left _ hc
      · exact h1E
    · refine le_csInf ⟨1, h1E⟩ (fun u hu => ?_)
      rcases hu with ⟨hu_lo, hu_hi, hu_not⟩ | hu_eq
      · let L := (Finset.univ : Finset Cand).filter (fun c => candVal c ≤ u)
        have h_true_L : (Sum.inl true : Cand) ∈ L :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu_lo⟩
        have hL_ne : L.Nonempty := ⟨Sum.inl true, h_true_L⟩
        obtain ⟨c₀, hc₀L, hc₀_eq⟩ := Finset.exists_mem_eq_sup' hL_ne candVal
        let u₀ := L.sup' hL_ne candVal
        have hu₀_eq : candVal c₀ = u₀ := hc₀_eq.symm
        have hu₀_lo : invE ≤ u₀ := Finset.le_sup' candVal h_true_L
        have hu₀_u : u₀ ≤ u := hu₀_eq ▸ (Finset.mem_filter.mp hc₀L).2
        have h_pres : presentSet Finset.univ ∅ τ β₁ u₀ = presentSet Finset.univ ∅ τ β₁ u := by
          ext z
          simp only [presentSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.notMem_empty, false_and, or_false]
          refine ⟨fun hle => hle.trans hu₀_u, fun hle => ?_⟩
          exact Finset.le_sup' (f := candVal)
            (Finset.mem_filter.mpr ⟨Finset.mem_univ (Sum.inr z), hle⟩)
        have hc₀_eff : candEff c₀ = u₀ := by
          dsimp only [candEff]
          rw [hu₀_eq, h_pres]
          exact if_pos ⟨hu₀_lo, hu₀_u.trans hu_hi, hu_not⟩
        calc (Finset.univ : Finset Cand).inf' hne candEff
            ≤ candEff c₀ := Finset.inf'_le candEff (Finset.mem_univ c₀)
          _ = u₀ := hc₀_eff
          _ ≤ u := hu₀_u
      · rw [Set.mem_singleton_iff.mp hu_eq]
        have h_false : candEff (Sum.inl false) = 1 := by
          dsimp only [candEff, candVal]; split_ifs <;> rfl
        calc (Finset.univ : Finset Cand).inf' hne candEff
            ≤ candEff (Sum.inl false) := Finset.inf'_le candEff (Finset.mem_univ (Sum.inl false))
          _ = 1 := h_false
  have h_meas_rp : ∀ A : Finset (Fin n),
      Measurable (fun τ : Fin n → ℝ => retainProd C 1 Finset.univ ∅ τ β₁ A) := by
    intro A
    have h_meas_dt : ∀ g : Fin n, Measurable (fun τ => deathTime C 1 Finset.univ ∅ τ β₁ g) := by
      intro g
      let Cand := Bool ⊕ Fin n
      let candVal : Cand → (Fin n → ℝ) → ℝ := fun c τ => match c with
        | Sum.inl true => invE
        | Sum.inl false => 1
        | Sum.inr z => τ z
      let candEff : Cand → (Fin n → ℝ) → ℝ := fun c τ =>
        let u := candVal c τ
        if invE ≤ u ∧ u ≤ 1 ∧ g ∉ C (presentSet Finset.univ ∅ τ β₁ u) then u else 1
      simp_rw [fun τ => h_dt_cand_eq τ g]
      refine h_meas_inf _ _ candEff (fun c _ => ?_)
      have hu : Measurable (candVal c) := by
        cases c with
        | inl b => cases b <;> exact measurable_const
        | inr z => exact measurable_pi_apply z
      have h_notC : MeasurableSet
          {τ : Fin n → ℝ | g ∉ C (presentSet Finset.univ ∅ τ β₁ (candVal c τ))} := by
        let badSets := (Finset.univ : Finset (Finset (Fin n))).filter (fun U => g ∉ C U)
        have heq_bad : {τ : Fin n → ℝ | g ∉ C (presentSet Finset.univ ∅ τ β₁ (candVal c τ))} =
            ⋃ U ∈ badSets, ⋂ z : Fin n,
              if z ∈ U then {τ | τ z ≤ candVal c τ} else {τ | τ z ≤ candVal c τ}ᶜ := by
          ext τ
          simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, badSets, Finset.mem_filter,
            Finset.mem_univ, true_and]
          refine ⟨fun hg => ⟨presentSet Finset.univ ∅ τ β₁ (candVal c τ), hg, fun z => ?_⟩, ?_⟩
          · by_cases hz : z ∈ presentSet Finset.univ ∅ τ β₁ (candVal c τ)
            · rw [if_pos hz]; simp [presentSet] at hz; exact hz
            · rw [if_neg hz]; intro hle
              simp only [Set.mem_setOf_eq] at hle
              exact hz (by simp [presentSet, hle])
          · rintro ⟨U, hgU, hzU⟩
            have hU_eq : presentSet Finset.univ ∅ τ β₁ (candVal c τ) = U := by
              ext z
              specialize hzU z
              by_cases hz : z ∈ U
              · rw [if_pos hz] at hzU
                simp only [Set.mem_setOf_eq] at hzU
                simp [presentSet, hz, hzU]
              · rw [if_neg hz] at hzU
                simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hzU
                simp [presentSet, hz, hzU]
            rwa [hU_eq]
        rw [heq_bad]
        refine Finset.measurableSet_biUnion _ (fun U _ => MeasurableSet.iInter (fun z => ?_))
        split_ifs
        · exact measurableSet_le (measurable_pi_apply z) hu
        · exact (measurableSet_le (measurable_pi_apply z) hu).compl
      have h_cond : MeasurableSet {τ : Fin n → ℝ | invE ≤ candVal c τ ∧ candVal c τ ≤ 1 ∧
          g ∉ C (presentSet Finset.univ ∅ τ β₁ (candVal c τ))} :=
        (measurableSet_le measurable_const hu).inter
          ((measurableSet_le hu measurable_const).inter h_notC)
      exact Measurable.ite h_cond hu measurable_const
    have h_meas_ret : ∀ g : Fin n,
        Measurable (fun τ => retentionProb C 1 Finset.univ ∅ τ β₁ g) := by
      intro g
      unfold retentionProb
      exact Measurable.ite (measurableSet_le (measurable_pi_apply g) measurable_const)
        (Real.measurable_log.comp (measurable_const.mul (h_meas_dt g))) measurable_const
    unfold retainProd
    simp_rw [if_pos (Finset.subset_univ A)]
    exact (Finset.measurable_prod A (fun g _ => h_meas_ret g)).mul
      (Finset.measurable_prod (Finset.univ \ A) (fun g _ => measurable_const.sub (h_meas_ret g)))
  let ν₁ : Measure ℝ := (ENNReal.ofReal (1 : ℝ))⁻¹ • volume.restrict (Set.Icc (0 : ℝ) 1)
  have hν₁_prob : IsProbabilityMeasure ν₁ := by
    rw [MeasureTheory.isProbabilityMeasure_iff]
    simp [ν₁, Real.volume_Icc]
  haveI : IsProbabilityMeasure ν₁ := hν₁_prob
  haveI : IsProbabilityMeasure (unifCubeMeasure n 1) := by
    unfold unifCubeMeasure; infer_instance
  have h_int : ∀ A : Finset (Fin n),
      Integrable (fun τ => retainProd C 1 Finset.univ ∅ τ β₁ A) (unifCubeMeasure n 1) := by
    intro A
    exact MeasureTheory.Integrable.of_mem_Icc 0 1 (h_meas_rp A).aemeasurable
      (Filter.Eventually.of_forall (fun τ => h_prod_bounds τ A))
  have h_incl : ∀ g ∈ canonicalDemand v Finset.univ,
      (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => g ∈ S),
        survivalLaw v Finset.univ 1 S) = invE := by
    intro g hgX
    change (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => g ∈ S),
        ∫ τ, retainProd C 1 Finset.univ ∅ τ β₁ S ∂(unifCubeMeasure n 1)) = invE
    rw [← MeasureTheory.integral_finset_sum _ (fun S _ => h_int S)]
    have h_sum_eq : ∀ τ : Fin n → ℝ,
        (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => g ∈ S),
          retainProd C 1 Finset.univ ∅ τ β₁ S) =
          retentionProb C 1 Finset.univ ∅ τ β₁ g := by
      intro τ
      have h_filt : (Finset.univ : Finset (Finset (Fin n))).filter (fun S => g ∈ S) =
          ((Finset.univ : Finset (Fin n)).erase g).powerset.image (insert g) := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
          Finset.mem_powerset]
        refine ⟨fun hgS => ⟨S.erase g, ?_, Finset.insert_erase hgS⟩, ?_⟩
        · intro x hx
          exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, Finset.mem_univ x⟩
        · rintro ⟨A', _, rfl⟩
          exact Finset.mem_insert_self g A'
      rw [h_filt, Finset.sum_image]
      · have h_term : ∀ A' ∈ ((Finset.univ : Finset (Fin n)).erase g).powerset,
            retainProd C 1 Finset.univ ∅ τ β₁ (insert g A') =
              retentionProb C 1 Finset.univ ∅ τ β₁ g *
                ((∏ x ∈ A', retentionProb C 1 Finset.univ ∅ τ β₁ x) *
                  (∏ x ∈ (Finset.univ : Finset (Fin n)).erase g \ A',
                    (1 - retentionProb C 1 Finset.univ ∅ τ β₁ x))) := by
          intro A' hA'
          have hA'_sub : A' ⊆ (Finset.univ : Finset (Fin n)).erase g := Finset.mem_powerset.mp hA'
          have hg_not_A' : g ∉ A' := fun hg => (Finset.notMem_erase g Finset.univ) (hA'_sub hg)
          have hsdiff_eq : (Finset.univ : Finset (Fin n)) \ insert g A' =
              (Finset.univ : Finset (Fin n)).erase g \ A' := by
            ext x; simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
              Finset.mem_erase, true_and]; tauto
          unfold retainProd
          rw [if_pos (Finset.subset_univ _), Finset.prod_insert hg_not_A', hsdiff_eq, mul_assoc]
        rw [Finset.sum_congr rfl h_term, ← Finset.mul_sum, ← Finset.prod_add]
        simp
      · intro A₁ hA₁ A₂ hA₂ heq
        have hg₁ : g ∉ A₁ := fun hg => (Finset.notMem_erase g Finset.univ) (Finset.mem_powerset.mp hA₁ hg)
        have hg₂ : g ∉ A₂ := fun hg => (Finset.notMem_erase g Finset.univ) (Finset.mem_powerset.mp hA₂ hg)
        have := congrArg (fun X : Finset (Fin n) => X.erase g) heq
        simpa [Finset.erase_insert hg₁, Finset.erase_insert hg₂] using this
    simp_rw [h_sum_eq]
    have h_ret_g : ∀ τ : Fin n → ℝ,
        retentionProb C 1 Finset.univ ∅ τ β₁ g =
          ((Function.eval g : (Fin n → ℝ) → ℝ) ⁻¹' Set.Iic invE).indicator (1 : (Fin n → ℝ) → ℝ) τ := by
      intro τ
      unfold retentionProb
      by_cases hτ : τ g ≤ invE
      · have hmem : τ ∈ (Function.eval g : (Fin n → ℝ) → ℝ) ⁻¹' Set.Iic invE := hτ
        rw [if_pos hτ, Set.indicator_of_mem hmem, Pi.one_apply]
        have h_dt_1 : deathTime C 1 Finset.univ ∅ τ β₁ g = 1 := by
          have h_set : {u : ℝ | invE ≤ u ∧ u ≤ 1 ∧
              g ∉ C (presentSet Finset.univ ∅ τ β₁ u)} = ∅ := by
            ext u
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
            intro hu_lo _
            have hgU : g ∈ presentSet Finset.univ ∅ τ β₁ u := by
              simp [presentSet, hτ.trans hu_lo]
            exact h_pers (presentSet Finset.univ ∅ τ β₁ u) Finset.univ (Finset.subset_univ _)
              (Finset.mem_inter.mpr ⟨hgX, hgU⟩)
          unfold deathTime
          rw [h_set, Set.empty_union, csInf_singleton]
        rw [h_dt_1, mul_one, Real.log_exp]
      · have hnmem : τ ∉ (Function.eval g : (Fin n → ℝ) → ℝ) ⁻¹' Set.Iic invE := hτ
        rw [if_neg hτ, Set.indicator_of_notMem hnmem]
    simp_rw [h_ret_g]
    have hs_meas : MeasurableSet ((Function.eval g : (Fin n → ℝ) → ℝ) ⁻¹' Set.Iic invE) :=
      measurableSet_Iic.preimage (measurable_pi_apply g)
    rw [MeasureTheory.integral_indicator_one hs_meas]
    have h_mp := MeasureTheory.measurePreserving_eval (fun _ : Fin n => ν₁) g
    have h_meas_eq : unifCubeMeasure n 1 ((Function.eval g) ⁻¹' Set.Iic invE) = ν₁ (Set.Iic invE) :=
      h_mp.measure_preimage measurableSet_Iic.nullMeasurableSet
    have h_inter : Set.Iic invE ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 invE := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      exact ⟨fun ⟨h1, h2, _⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, h2.trans h_invE_le_one⟩⟩
    have h_ν₁_val : ν₁ (Set.Iic invE) = ENNReal.ofReal invE := by
      simp [ν₁, Measure.restrict_apply measurableSet_Iic, h_inter, Real.volume_Icc]
    rw [MeasureTheory.measureReal_def, h_meas_eq, h_ν₁_val, ENNReal.toReal_ofReal h_invE_pos.le]

  
  have coe_realVal : ∀ S : Finset (Fin n), v S ≠ ⊥ → ((realVal v S : ℝ) : WithBot ℝ) = v S := by
    intro S hS
    obtain ⟨r, hr⟩ := WithBot.ne_bot_iff_exists.mp hS
    rw [realVal, ← hr, WithBot.unbotD_coe]
  have dom_erase : ∀ (X : Finset (Fin n)) (x : Fin n), v X ≠ ⊥ → x ∈ X → v (X.erase x) ≠ ⊥ := by
    intro X x hX hx
    have hv0 : v ∅ ≠ ⊥ := by rw [hv.1]; exact WithBot.coe_ne_bot
    have hex := hv.2 X ∅ hX hv0 x (by simp [hx])
    have hsdiff_emp : (∅ : Finset (Fin n)) \ X = ∅ := by simp
    rw [hsdiff_emp, Finset.sup_empty, max_bot_right] at hex
    have hlhs_ne : v X + v ∅ ≠ ⊥ := by
      rw [← coe_realVal X hX, hv.1, ← WithBot.coe_add]; exact WithBot.coe_ne_bot
    intro h_eq_bot
    rw [h_eq_bot, WithBot.bot_add, le_bot_iff] at hex
    exact hlhs_ne hex
  have dom_hereditary : ∀ {X Y : Finset (Fin n)}, Y ⊆ X → v X ≠ ⊥ → v Y ≠ ⊥ := by
    intro X Y hYX hX
    have h_ind : ∀ (k : ℕ) (Z : Finset (Fin n)), (Z \ Y).card = k → Y ⊆ Z → v Z ≠ ⊥ → v Y ≠ ⊥ := by
      intro k
      induction k with
      | zero =>
        intro Z hk hYZ hZ
        have hsub : Z ⊆ Y := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hk)
        rwa [Finset.Subset.antisymm hYZ hsub]
      | succ k ih =>
        intro Z hk hYZ hZ
        obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < (Z \ Y).card)
        obtain ⟨hxZ, hxY⟩ := Finset.mem_sdiff.mp hx
        have hsdiff : Z.erase x \ Y = (Z \ Y).erase x := by ext z; simp [and_assoc]
        exact ih (Z.erase x) (by rw [hsdiff, Finset.card_erase_of_mem hx]; omega)
          (Finset.subset_erase.mpr ⟨hYZ, hxY⟩) (dom_erase Z x hZ hxZ)
    exact h_ind (X \ Y).card X rfl hYX hX
  have submod : ∀ (Q R : Finset (Fin n)) (g : Fin n),
      Q ⊆ R → g ∉ R → v (insert g R) ≠ ⊥ → marginalVal v R g ≤ marginalVal v Q g := by
    intro Q R g hQR hgR hRg
    have hgQ : g ∉ Q := fun hg => hgR (hQR hg)
    have hR : v R ≠ ⊥ := dom_hereditary (Finset.subset_insert g R) hRg
    have hQg : v (insert g Q) ≠ ⊥ := dom_hereditary (Finset.insert_subset_insert g hQR) hRg
    have hQ : v Q ≠ ⊥ := dom_hereditary (hQR.trans (Finset.subset_insert g R)) hRg
    have hex := hv.2 (insert g R) Q hRg hQ g (Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self g R, hgQ⟩)
    have hsdiff_empty : Q \ insert g R = ∅ :=
      Finset.sdiff_eq_empty_iff_subset.mpr (hQR.trans (Finset.subset_insert g R))
    rw [Finset.erase_insert hgR, hsdiff_empty, Finset.sup_empty, max_bot_right,
      ← coe_realVal (insert g R) hRg, ← coe_realVal Q hQ,
      ← coe_realVal R hR, ← coe_realVal (insert g Q) hQg,
      ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe] at hex
    dsimp [marginalVal]; linarith
  have demand_props : ∀ T : Finset (Fin n),
      let X := canonicalDemand v T
      v X ≠ ⊥ ∧ (∀ Y ⊆ T, v Y ≤ v X) ∧ (∀ Y Z : Finset (Fin n), Y ⊆ Z → Z ⊆ X → v Y ≤ v Z) := by
    intro T
    dsimp only
    have hex : ∃ X₀ ∈ T.powerset, ∀ Y ∈ T.powerset, demandKeyLe v Y X₀ := by
      let f : Finset (Fin n) → WithBot ℝ ×ₗ ℝ := fun S => toLex (v S, psiWeight S)
      obtain ⟨X₀, hX₀_mem, hX₀_max⟩ :=
        Finset.exists_max_image T.powerset f ⟨∅, Finset.empty_mem_powerset T⟩
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
      intro hbot; rw [hbot, le_bot_iff] at h0; exact WithBot.coe_ne_bot h0
    have h_erase_mono : ∀ Z ⊆ X, ∀ g ∈ Z, v (Z.erase g) ≤ v Z := by
      intro Z hZX g hgZ
      have hXg : g ∈ X := hZX hgZ
      have hsub : Z.erase g ⊆ X.erase g := Finset.erase_subset_erase g hZX
      have hg_not : g ∉ X.erase g := Finset.notMem_erase g X
      have h_ins_X : insert g (X.erase g) = X := Finset.insert_erase hXg
      have h_ins_Z : insert g (Z.erase g) = Z := Finset.insert_erase hgZ
      have h_sm := submod (Z.erase g) (X.erase g) g hsub hg_not (by rwa [h_ins_X])
      have hXe_ne : v (X.erase g) ≠ ⊥ := dom_hereditary (Finset.erase_subset g X) hX_ne_bot
      have hXe_le : v (X.erase g) ≤ v X := hX_v_max (X.erase g) ((Finset.erase_subset g X).trans hXT)
      rw [← coe_realVal (X.erase g) hXe_ne, ← coe_realVal X hX_ne_bot, WithBot.coe_le_coe] at hXe_le
      dsimp [marginalVal] at h_sm
      rw [h_ins_X, h_ins_Z] at h_sm
      have hZe_ne : v (Z.erase g) ≠ ⊥ := dom_hereditary ((Finset.erase_subset g Z).trans hZX) hX_ne_bot
      have hZ_ne : v Z ≠ ⊥ := dom_hereditary hZX hX_ne_bot
      rw [← coe_realVal (Z.erase g) hZe_ne, ← coe_realVal Z hZ_ne, WithBot.coe_le_coe]
      linarith
    have h_mono : ∀ Y Z : Finset (Fin n), Y ⊆ Z → Z ⊆ X → v Y ≤ v Z := by
      intro Y Z hYZ hZX
      have h_ind : ∀ (k : ℕ) (W : Finset (Fin n)), (W \ Y).card = k → Y ⊆ W → W ⊆ X → v Y ≤ v W := by
        intro k
        induction k with
        | zero =>
          intro W hk hYW _
          rw [Finset.Subset.antisymm hYW (Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hk))]
        | succ k ih =>
          intro W hk hYW hWX
          obtain ⟨g, hg⟩ := Finset.card_pos.mp (by omega : 0 < (W \ Y).card)
          obtain ⟨hgW, hgY⟩ := Finset.mem_sdiff.mp hg
          have hsdiff : W.erase g \ Y = (W \ Y).erase g := by ext z; simp [and_assoc]
          exact (ih (W.erase g) (by rw [hsdiff, Finset.card_erase_of_mem hg]; omega)
            (Finset.subset_erase.mpr ⟨hYW, hgY⟩) ((Finset.erase_subset g W).trans hWX)).trans
            (h_erase_mono W hWX g hgW)
      exact h_ind (Z \ Y).card Z rfl hYZ hZX
    exact ⟨hX_ne_bot, hX_v_max, h_mono⟩
  let Xstar := canonicalDemand v Finset.univ
  obtain ⟨hX_ne, hX_max_all, _⟩ := demand_props Finset.univ
  have h_opt_eq : optVal v = realVal v Xstar := by
    have h_sup : (Finset.univ : Finset (Finset (Fin n))).sup v = v Xstar := by
      apply le_antisymm
      · exact Finset.sup_le (fun Y _ => hX_max_all Y (Finset.subset_univ Y))
      · exact Finset.le_sup (Finset.mem_univ Xstar)
    rw [optVal, h_sup, realVal]
  have h_tele : ∀ (k : ℕ) (Y : Finset (Fin n)), Y.card ≤ k →
      ∑ g ∈ Y, marginalVal v (Y.filter (fun h => h < g)) g = realVal v Y := by
    intro k
    induction k with
    | zero =>
      intro Y hk
      have hY : Y = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hk)
      subst hY; simp [realVal, hv.1]
    | succ k ih =>
      intro Y hk
      rcases Y.eq_empty_or_nonempty with rfl | hYne
      · simp [realVal, hv.1]
      · let m := Y.max' hYne
        have hmY : m ∈ Y := Finset.max'_mem Y hYne
        let Y' := Y.erase m
        have hY'_card : Y'.card ≤ k := by
          have hlt := Finset.card_erase_lt_of_mem hmY; dsimp only [Y']; omega
        rw [← Finset.add_sum_erase Y _ hmY]
        have h_filt_m : Y.filter (fun h => h < m) = Y' := by
          ext y; simp only [Finset.mem_filter, Y', Finset.mem_erase]
          exact ⟨fun ⟨hyY, hylt⟩ => ⟨ne_of_lt hylt, hyY⟩,
            fun ⟨hyne, hyY⟩ => ⟨hyY, lt_of_le_of_ne (Finset.le_max' Y y hyY) hyne⟩⟩
        have h_term_m : marginalVal v (Y.filter (fun h => h < m)) m = realVal v Y - realVal v Y' := by
          dsimp [marginalVal]; rw [h_filt_m, Finset.insert_erase hmY]
        have h_rest : ∑ g ∈ Y', marginalVal v (Y.filter (fun h => h < g)) g =
            ∑ g ∈ Y', marginalVal v (Y'.filter (fun h => h < g)) g := by
          refine Finset.sum_congr rfl (fun g hgY' => ?_)
          obtain ⟨hgne, hgY⟩ := Finset.mem_erase.mp hgY'
          have hglt : g < m := lt_of_le_of_ne (Finset.le_max' Y g hgY) hgne
          have h_filt_g : Y.filter (fun h => h < g) = Y'.filter (fun h => h < g) := by
            ext y; simp only [Finset.mem_filter, Y', Finset.mem_erase]
            exact ⟨fun ⟨hyY, hylt⟩ => ⟨⟨ne_of_lt (lt_trans hylt hglt), hyY⟩, hylt⟩,
              fun ⟨⟨_, hyY⟩, hylt⟩ => ⟨hyY, hylt⟩⟩
          rw [h_filt_g]
        rw [h_term_m, h_rest, ih Y' hY'_card]; ring
  let a : Fin n → ℝ := fun g => marginalVal v (Xstar.filter (fun h => h < g)) g
  have ha_sum : (∑ g ∈ Xstar, a g) = realVal v Xstar := h_tele Xstar.card Xstar le_rfl
  have ha_low : ∀ Y ⊆ Xstar, ∑ g ∈ Y, a g ≤ realVal v Y := by
    intro Y hYX
    calc ∑ g ∈ Y, a g
        ≤ ∑ g ∈ Y, marginalVal v (Y.filter (fun h => h < g)) g := by
          refine Finset.sum_le_sum (fun g hgY => ?_)
          have hsub : Y.filter (fun h => h < g) ⊆ Xstar.filter (fun h => h < g) :=
            Finset.filter_subset_filter _ hYX
          have hg_not : g ∉ Xstar.filter (fun h => h < g) := by simp
          have h_ins_sub : insert g (Xstar.filter (fun h => h < g)) ⊆ Xstar :=
            Finset.insert_subset_iff.mpr ⟨hYX hgY, Finset.filter_subset _ Xstar⟩
          exact submod (Y.filter (fun h => h < g)) (Xstar.filter (fun h => h < g)) g
            hsub hg_not (dom_hereditary h_ins_sub hX_ne)
      _ = realVal v Y := h_tele Y.card Y le_rfl
  let p : Finset (Fin n) → ℝ := fun S => survivalLaw v Finset.univ 1 S
  have h_ptwise : ∀ S : Finset (Fin n),
      p S * (∑ g ∈ Xstar.filter (fun g => g ∈ S), a g) ≤ p S * realVal v S := by
    intro S
    rcases lt_or_eq_of_le (h_surv Finset.univ S).1 with hp_pos | hp_zero
    · obtain ⟨T, _, hST⟩ := (h_surv Finset.univ S).2 hp_pos
      obtain ⟨hDT_ne, _, hDT_mono⟩ := demand_props T
      let Y_S := Xstar.filter (fun g => g ∈ S)
      have hYS_X : Y_S ⊆ Xstar := Finset.filter_subset _ Xstar
      have hYS_S : Y_S ⊆ S := fun g hg => (Finset.mem_filter.mp hg).2
      have hS_ne : v S ≠ ⊥ := dom_hereditary hST hDT_ne
      have hYS_ne : v Y_S ≠ ⊥ := dom_hereditary (hYS_S.trans hST) hDT_ne
      have hv_le : v Y_S ≤ v S := hDT_mono Y_S S hYS_S hST
      rw [← coe_realVal Y_S hYS_ne, ← coe_realVal S hS_ne, WithBot.coe_le_coe] at hv_le
      exact mul_le_mul_of_nonneg_left ((ha_low Y_S hYS_X).trans hv_le) hp_pos.le
    · dsimp only [p]; rw [← hp_zero, zero_mul, zero_mul]
  have h_sum_le : ∑ S : Finset (Fin n), p S * (∑ g ∈ Xstar.filter (fun g => g ∈ S), a g) ≤
      ∑ S : Finset (Fin n), p S * realVal v S :=
    Finset.sum_le_sum (fun S _ => h_ptwise S)
  have h_swap : ∑ S : Finset (Fin n), p S * (∑ g ∈ Xstar.filter (fun g => g ∈ S), a g) =
      invE * optVal v := by
    calc ∑ S : Finset (Fin n), p S * (∑ g ∈ Xstar.filter (fun g => g ∈ S), a g)
        = ∑ S : Finset (Fin n), ∑ g ∈ Xstar, (if g ∈ S then p S * a g else 0) := by
          refine Finset.sum_congr rfl (fun S _ => ?_)
          rw [Finset.sum_filter, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun g _ => by split_ifs <;> ring)
      _ = ∑ g ∈ Xstar, ∑ S : Finset (Fin n), (if g ∈ S then p S * a g else 0) := Finset.sum_comm
      _ = ∑ g ∈ Xstar,
            (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => g ∈ S), p S) * a g := by
          refine Finset.sum_congr rfl (fun g _ => ?_)
          rw [← Finset.sum_filter, Finset.sum_mul]
      _ = ∑ g ∈ Xstar, invE * a g :=
          Finset.sum_congr rfl (fun g hg => by rw [h_incl g hg])
      _ = invE * (∑ g ∈ Xstar, a g) := (Finset.mul_sum Xstar a invE).symm
      _ = invE * optVal v := by rw [ha_sum, h_opt_eq]
  exact ⟨h_incl, by linarith⟩

 obtain ⟨alg, halg⟩ := h_s4
 refine ⟨alg, fun v hv => ?_⟩
 have h_invE_le_1 : invE ≤ 1 := by unfold invE; exact Real.exp_le_one_iff.mpr (by norm_num)
 have h_law_eq : ∀ S : Finset (Fin n), algSelectionProb alg v S = survivalLaw v Finset.univ 1 S := by
   intro S
   rw [(halg v hv).1 S, online_survival_law_eq_survival_law n v S hv]
 refine ⟨(survival_accept_bounds_and_support n v hv).1, h_law_eq, ?_, (halg v hv).2, ?_, ?_⟩
 · intro g hg
   unfold algInclusionProb
   simp_rw [h_law_eq]
   exact (h_s5 v hv).1 g hg
 · unfold expectedSelectionVal
   have h_no_bot : ¬ ∃ S : Finset (Fin n), 0 < algSelectionProb alg v S ∧ v S = ⊥ := by
     rintro ⟨S, hpos, hbot⟩
     rw [h_law_eq S] at hpos
     obtain ⟨T, _, hST⟩ :=
       ((survival_accept_bounds_and_support n v hv).2.1 Finset.univ S 1 h_invE_le_1 le_rfl).2 hpos
     exact ((survival_accept_bounds_and_support n v hv).2.2.1 T S hST).1 hbot
   rw [if_neg h_no_bot, WithBot.coe_le_coe]
   simp_rw [h_law_eq]
   exact (h_s5 v hv).2
 · rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]


/-- **Theorem 3.1 (`thm:selection`, `1 / e`-Competitive Online Selection for Gross Substitutes)**:
For every `n`, the non-clairvoyant survival algorithm `alg : OnlineSelectionAlg n` satisfies for
every signed gross substitutes valuation `v`:
- acceptance probability validity `0 ≤ α_x(A, S, t) ≤ 1` and output law `μ^v_{N, 1}`;
- **(i)** `P[g ∈ A] = 1 / e` for every `g ∈ D_v(N)`;
- **(ii)** at every arrival step `k ≤ n`, `A_k ⊆ D_v(T)` for some subset `T` of arrived items, so
  `A_k ∈ dom v` and `v(Y) ≥ 0` for every `Y ⊆ A_k` (in particular `v(A_k) ≥ 0`);
- **(iii)** `E[v(A)] ≥ OPT(v) / e`. -/
theorem thm_3_1_selection (n : ℕ) :
    ∃ alg : OnlineSelectionAlg n,
      ∀ v : ItemValuation n, IsGSValuation v →
        (∀ (x : Fin n) (A S : Finset (Fin n)) (t : ℝ),
          x ∉ S → t ≤ 1 →
            0 ≤ survivalAcceptProb v x A S t ∧ survivalAcceptProb v x A S t ≤ 1) ∧
        (∀ S : Finset (Fin n), algSelectionProb alg v S = survivalLaw v Finset.univ 1 S) ∧
        (∀ g ∈ canonicalDemand v Finset.univ, algInclusionProb alg v g = invE) ∧
        (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
          let st := runDetSelectionSteps (alg.det ω) v π k hk
          ∃ T ⊆ st.1.toFinset,
            st.2 ⊆ canonicalDemand v T ∧
            v st.2 ≠ ⊥ ∧
            ∀ Y ⊆ st.2, v Y ≠ ⊥ ∧ 0 ≤ realVal v Y) ∧
        (((invE * optVal v : ℝ) : WithBot ℝ) ≤ expectedSelectionVal alg v) := by
  obtain ⟨alg, halg⟩ := thm_gs_selection n
  exact ⟨alg, fun v hv => ⟨(halg v hv).1, (halg v hv).2.1, (halg v hv).2.2.1,
    (halg v hv).2.2.2.1, (halg v hv).2.2.2.2.1⟩⟩

/-- **Theorem A (`thm:A`, Gross Substitutes Secretary / Single-Bidder Online Selection)**:
There exists a universal randomized non-clairvoyant online selection algorithm on `n` items that,
for every signed gross substitutes valuation `v : 2^N → ℝ ∪ {-∞}` with `v(∅) = 0`, keeps `v(A_k) ≥ 0`
at all times, selects each item of `D_v(N)` with exact probability `1 / e`, and achieves
`E[v(A)] ≥ OPT(v) / e`. -/
theorem thm_A (n : ℕ) :
    ∃ alg : OnlineSelectionAlg n,
      ∀ v : ItemValuation n, IsGSValuation v →
        (∀ g ∈ canonicalDemand v Finset.univ, algInclusionProb alg v g = invE) ∧
        (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
          let st := runDetSelectionSteps (alg.det ω) v π k hk
          v st.2 ≠ ⊥ ∧ ((0 : ℝ) : WithBot ℝ) ≤ v st.2) ∧
        (((invE * optVal v : ℝ) : WithBot ℝ) ≤ expectedSelectionVal alg v) := by
  obtain ⟨alg, halg⟩ := thm_3_1_selection n
  refine ⟨alg, fun v hv => ⟨(halg v hv).2.2.1, fun ω π k hk => ?_, (halg v hv).2.2.2.2⟩⟩
  obtain ⟨_, _, _, hne, hsub⟩ := (halg v hv).2.2.2.1 ω π k hk
  have hnn : 0 ≤ realVal v (runDetSelectionSteps (alg.det ω) v π k hk).2 :=
    (hsub _ Finset.Subset.rfl).2
  obtain ⟨r, hr⟩ := WithBot.ne_bot_iff_exists.mp hne
  dsimp only [realVal] at hnn
  rw [← hr, WithBot.unbotD_coe] at hnn
  exact ⟨hne, by rw [← hr, WithBot.coe_le_coe]; exact hnn⟩

end

end

end GrossSubstitutesWelfare
