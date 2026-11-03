import GrossSubstitutesWelfare.Defs
import GrossSubstitutesWelfare.Preliminaries.ExchangeAndDemand
import GrossSubstitutesWelfare.Preliminaries.SafeSupportAndCutoff
import GrossSubstitutesWelfare.Selection.ClampAndPayment
import GrossSubstitutesWelfare.Selection.DelayAndComparison

set_option maxHeartbeats 4000000

/-!
# Appendix B.2: Inclusion Recursion, Pointwise Safety & Distribution Matching

This file formalizes Appendix B.2 Proposition B.6 (`prop:matching`), Lemma B.7 (`lem:inclusion`),
and the pointwise canonical-demand support invariant of Appendix B.3 of *Gross Substitutes Welfare
in Random Order*.
-/

namespace GrossSubstitutesWelfare

open Classical MeasureTheory

noncomputable section

namespace InclusionAndMatchingInternal

theorem gs_canonical_safe_and_contract : ∀ (n : ℕ) (v : ItemValuation n), IsGSValuation v →
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

theorem survival_accept_validity_and_mass_eq : ∀ (n : ℕ) (v : ItemValuation n), IsGSValuation v →
      (∀ (S A : Finset (Fin n)) (t : ℝ),
        invE ≤ t → t ≤ 1 →
          0 ≤ survivalLaw v S t A ∧
          (0 < survivalLaw v S t A → ∃ T ⊆ S, A ⊆ canonicalDemand v T)) ∧
      (∀ (S A : Finset (Fin n)) (x : Fin n) (t : ℝ),
        x ∉ S → t ≤ 1 →
          0 ≤ survivalAcceptProb v x A S t ∧ survivalAcceptProb v x A S t ≤ 1) ∧
      (∀ (S A : Finset (Fin n)) (x : Fin n) (t : ℝ),
        x ∉ S → invE < t → t ≤ 1 → x ∈ canonicalDemand v (insert x S) →
          survivalLaw v S t A * survivalAcceptProb v x A S t =
            (1 / (Real.exp 1 * t)) * survivalLaw (contractVal v x) S t A) := by
  intro n v hv
  refine ⟨?_, ?_, ?_⟩
  · intro S A t ht₀ ht1
    have hspec := genSurvivalLaw2_spec (canonicalDemand v) t t S ∅ (fun _ => t)
      (lem_2_7_persistence v hv).1 (lem_2_7_persistence v hv).2 ht₀ le_rfl ht1
    have hnn : 0 ≤ survivalLaw v S t A :=
      MeasureTheory.integral_nonneg (fun τ => (hspec.1 τ A).1)
    refine ⟨hnn, fun hpos => ?_⟩
    have hex : ∃ τ : Fin n → ℝ, 0 < retainProd (canonicalDemand v) t S ∅ τ (fun _ => t) A := by
      by_contra hno
      push_neg at hno
      have hzero : (fun τ => retainProd (canonicalDemand v) t S ∅ τ (fun _ => t) A) =
          fun _ => 0 := by
        ext τ
        exact le_antisymm (hno τ) (hspec.1 τ A).1
      have hint0 : survivalLaw v S t A = 0 := by
        unfold survivalLaw genSurvivalLaw genSurvivalLaw2
        rw [hzero, MeasureTheory.integral_zero]
      exact (ne_of_gt hpos) hint0
    obtain ⟨τ, hτ_pos⟩ := hex
    have hA_sub := hspec.2.2.1 τ A hτ_pos
    refine ⟨presentSet S ∅ τ (fun _ => t) invE, ?_, fun g hg => (Finset.mem_inter.mp (hA_sub hg)).1⟩
    intro g hg
    simp [presentSet] at hg
    exact hg.1
  · intro S A x t hxS ht1
    exact (survivalAcceptProb_valid v S x t A hv hxS ht1).1
  · intro S A x t hxS ht_gt ht1 hxD
    exact (survivalAcceptProb_valid v S x t A hv hxS ht1).2 ht_gt hxD

theorem unif_cube_threshold_max_split : ∀ (n : ℕ) (Q : Finset (Fin n)) (M t : ℝ) (Ψ : (Fin n → ℝ) → ℝ),
      invE ≤ t →
      Measurable Ψ →
      (∀ τ, |Ψ τ| ≤ M) →
      (∀ τ₁ τ₂, (∀ q ∈ Q, τ₁ q = τ₂ q) → Ψ τ₁ = Ψ τ₂) →
        t ^ Q.card * ∫ τ, Ψ τ ∂(unifCubeMeasure n t) =
          Real.exp (-(Q.card : ℝ)) * ∫ τ, Ψ τ ∂(unifCubeMeasure n invE) +
          ∑ x ∈ Q,
            ∫ s in Set.Icc invE t,
              s ^ (Q.erase x).card *
                ∫ τ, Ψ (Function.update τ x s) ∂(unifCubeMeasure n s) :=
by
  have h_1d_prob : ∀ {c : ℝ}, 0 < c →
      IsProbabilityMeasure ((ENNReal.ofReal c)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) c)) := by
    intro c hc
    rw [MeasureTheory.isProbabilityMeasure_iff]
    simp only [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul, Real.volume_Icc, sub_zero]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top

  have h_rescale : ∀ (n : ℕ) (r : ℝ), 0 < r →
      IsProbabilityMeasure (unifCubeMeasure n r) ∧
      ∀ (Φ : (Fin n → ℝ) → ℝ),
        ∫ τ, Φ τ ∂(unifCubeMeasure n r) =
          ∫ ω, Φ (fun i => r * ω i) ∂(unifCubeMeasure n 1) := by
    intro n r hr
    haveI : IsProbabilityMeasure ((ENNReal.ofReal r)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) r)) :=
      h_1d_prob hr
    haveI : IsProbabilityMeasure ((ENNReal.ofReal (1 : ℝ))⁻¹ • volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      h_1d_prob zero_lt_one
    have h_prob : IsProbabilityMeasure (unifCubeMeasure n r) := by
      unfold unifCubeMeasure
      infer_instance
    refine ⟨h_prob, fun Φ => ?_⟩
    let ν : ℝ → Measure ℝ := fun c => (ENNReal.ofReal c)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) c)
    have h_mp_1d : MeasurePreserving (fun x : ℝ => r * x) (ν 1) (ν r) := by
      refine ⟨measurable_const_mul r, MeasureTheory.Measure.ext (fun E hE => ?_)⟩
      have hν1 : ν 1 = volume.restrict (Set.Icc (0 : ℝ) 1) := by
        simp [ν]
      rw [hν1, Measure.map_apply (measurable_const_mul r) hE,
        Measure.restrict_apply ((measurable_const_mul r) hE)]
      have h_pre : ((fun x : ℝ => r * x) ⁻¹' E) ∩ Set.Icc (0 : ℝ) 1 =
          (fun x : ℝ => r * x) ⁻¹' (E ∩ Set.Icc (0 : ℝ) r) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc]
        refine ⟨fun ⟨hxE, hx0, hx1⟩ => ⟨hxE, by nlinarith, by nlinarith⟩,
          fun ⟨hxE, hrx0, hrxr⟩ => ⟨hxE, by nlinarith, by nlinarith⟩⟩
      rw [h_pre, ← Measure.map_apply (measurable_const_mul r) (hE.inter measurableSet_Icc),
        Real.map_volume_mul_left hr.ne', abs_of_pos (inv_pos.mpr hr), ENNReal.ofReal_inv_of_pos hr]
      simp [ν, Measure.restrict_apply hE]
    let e_r : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
      { toFun := fun ω i => r * ω i
        invFun := fun τ i => r⁻¹ * τ i
        left_inv := fun ω => funext (fun i => inv_mul_cancel_left₀ hr.ne' (ω i))
        right_inv := fun τ => funext (fun i => mul_inv_cancel_left₀ hr.ne' (τ i))
        measurable_toFun := measurable_pi_iff.mpr (fun i => (measurable_const_mul r).comp (measurable_pi_apply i))
        measurable_invFun := measurable_pi_iff.mpr (fun i => (measurable_const_mul r⁻¹).comp (measurable_pi_apply i)) }
    have h_mp : MeasurePreserving e_r (unifCubeMeasure n 1) (unifCubeMeasure n r) := by
      unfold unifCubeMeasure
      exact MeasureTheory.measurePreserving_pi _ _ (fun _ => h_mp_1d)
    exact (h_mp.integral_comp' Φ).symm

  have h_upd_joint : ∀ (n : ℕ) (x : Fin n),
      Measurable (fun p : ℝ × (Fin n → ℝ) => Function.update p.2 x p.1) := by
    intro n x
    refine measurable_pi_iff.mpr (fun j => ?_)
    by_cases hj : j = x
    · subst hj
      have hfn : (fun p : ℝ × (Fin n → ℝ) => Function.update p.2 j p.1 j) = Prod.fst :=
        funext (fun p => Function.update_self j p.1 p.2)
      rw [hfn]
      exact measurable_fst
    · have hfn : (fun p : ℝ × (Fin n → ℝ) => Function.update p.2 x p.1 j) = fun p => p.2 j :=
        funext (fun p => Function.update_of_ne hj p.1 p.2)
      rw [hfn]
      exact (measurable_pi_apply j).comp measurable_snd

  have h_param : ∀ (Z : Type) [MeasurableSpace Z] (n : ℕ) (M : ℝ)
      (r_fn : Z → ℝ) (H : Z × (Fin n → ℝ) → ℝ),
      Measurable r_fn →
      Measurable H →
      (∀ p, |H p| ≤ M) →
        let J : Z → ℝ := fun z =>
          ∫ ω, H (z, fun i => r_fn z * ω i) ∂(unifCubeMeasure n 1)
        Measurable J ∧
        (∀ z, |J z| ≤ M) ∧
        (∀ z, 0 < r_fn z →
          ∫ τ, H (z, τ) ∂(unifCubeMeasure n (r_fn z)) = J z) := by
    intro Z _ n M r_fn H hr_fn hH hH_bdd J
    haveI : IsProbabilityMeasure (unifCubeMeasure n 1) := (h_rescale n 1 zero_lt_one).1
    have hφ : Measurable (fun p : Z × (Fin n → ℝ) => (p.1, fun i => r_fn p.1 * p.2 i)) := by
      refine measurable_fst.prodMk (measurable_pi_iff.mpr (fun i => ?_))
      exact (hr_fn.comp measurable_fst).mul ((measurable_pi_apply i).comp measurable_snd)
    have hJ_meas : Measurable J :=
      ((hH.comp hφ).stronglyMeasurable.integral_prod_right').measurable
    have hJ_bdd : ∀ z : Z, |J z| ≤ M := by
      intro z
      have h_norm := MeasureTheory.norm_integral_le_of_norm_le_const (μ := unifCubeMeasure n 1)
        (f := fun ω => H (z, fun i => r_fn z * ω i)) (C := M)
        (Filter.Eventually.of_forall (fun ω => by simpa [Real.norm_eq_abs] using hH_bdd _))
      simpa [J, Real.norm_eq_abs, MeasureTheory.probReal_univ] using h_norm
    have hJ_eq : ∀ z : Z, 0 < r_fn z →
        ∫ τ, H (z, τ) ∂(unifCubeMeasure n (r_fn z)) = J z := by
      intro z hz
      exact (h_rescale n (r_fn z) hz).2 (fun τ => H (z, τ))
    exact ⟨hJ_meas, hJ_bdd, hJ_eq⟩

  have h_slice : ∀ (n : ℕ) (a : Fin n) (M r : ℝ) (Φ : (Fin n → ℝ) → ℝ),
      0 < r →
      Measurable Φ →
      (∀ τ, |Φ τ| ≤ M) →
        r * ∫ τ, Φ τ ∂(unifCubeMeasure n r) =
          ∫ u in Set.Icc (0 : ℝ) r,
            ∫ τ, Φ (Function.update τ a u) ∂(unifCubeMeasure n r) := by
    intro n a M r Φ hr hΦ hΦ_bdd
    let ν : Measure ℝ := (ENNReal.ofReal r)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) r)
    haveI : IsProbabilityMeasure ν := h_1d_prob hr
    haveI : IsProbabilityMeasure (unifCubeMeasure n r) := (h_rescale n r hr).1
    obtain ⟨pred, hpred⟩ : ∃ pred : Fin n → Prop, ∀ i, pred i ↔ i = a :=
      ⟨fun i => i = a, fun _ => Iff.rfl⟩
    let a_sub : {i : Fin n // pred i} := ⟨a, (hpred a).mpr rfl⟩
    let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) pred
    suffices h_gen_sl : ∀ {μ_in : Measure ({i : Fin n // pred i} → ℝ)}
        {μ_out : Measure ({i : Fin n // ¬ pred i} → ℝ)},
        μ_in = Measure.pi (fun _ => ν) →
        MeasurePreserving e (unifCubeMeasure n r) (μ_in.prod μ_out) →
        IsProbabilityMeasure μ_in → IsProbabilityMeasure μ_out →
        r * ∫ τ, Φ τ ∂(unifCubeMeasure n r) =
          ∫ u in Set.Icc (0 : ℝ) r,
            ∫ τ, Φ (Function.update τ a u) ∂(unifCubeMeasure n r) by
      exact h_gen_sl rfl
        (MeasureTheory.measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => ν) pred)
        inferInstance inferInstance
    intro μ_in μ_out hμ_in_eq h_mp_fwd h_prob_in h_prob_out
    haveI : IsProbabilityMeasure μ_in := h_prob_in
    haveI : IsProbabilityMeasure μ_out := h_prob_out
    have h_mp : MeasurePreserving e.symm (μ_in.prod μ_out) (unifCubeMeasure n r) :=
      h_mp_fwd.symm e
    have h_symm_in : ∀ q (j : Fin n) (hj : pred j), e.symm q j = q.1 ⟨j, hj⟩ := by
      intro q j hj
      exact (Equiv.piEquivPiSubtypeProd_symm_apply pred (fun _ : Fin n => ℝ) q j).trans (dif_pos hj)
    have h_symm_out : ∀ q (j : Fin n) (hj : ¬ pred j), e.symm q j = q.2 ⟨j, hj⟩ := by
      intro q j hj
      exact (Equiv.piEquivPiSubtypeProd_symm_apply pred (fun _ : Fin n => ℝ) q j).trans (dif_neg hj)
    have h_id1 : ∀ (x : {i // pred i} → ℝ) (z : {i // ¬ pred i} → ℝ),
        e.symm (x, z) = Function.update (e.symm (0, z)) a (x a_sub) := by
      intro x z
      ext j
      by_cases hj : j = a
      · subst hj
        rw [h_symm_in (x, z) j ((hpred j).mpr rfl), Function.update_self]
      · have hnp : ¬ pred j := fun hp => hj ((hpred j).mp hp)
        rw [h_symm_out (x, z) j hnp, Function.update_of_ne hj, h_symm_out (0, z) j hnp]
    have h_id2 : ∀ (x' : {i // pred i} → ℝ) (z : {i // ¬ pred i} → ℝ) (u : ℝ),
        Function.update (e.symm (x', z)) a u = Function.update (e.symm (0, z)) a u := by
      intro x' z u
      ext j
      by_cases hj : j = a
      · subst hj
        rw [Function.update_self, Function.update_self]
      · have hnp : ¬ pred j := fun hp => hj ((hpred j).mp hp)
        rw [Function.update_of_ne hj, Function.update_of_ne hj,
          h_symm_out (x', z) j hnp, h_symm_out (0, z) j hnp]
    let g : ℝ → ℝ := fun u => ∫ τ, Φ (Function.update τ a u) ∂(unifCubeMeasure n r)
    have hg_meas : Measurable g :=
      ((hΦ.comp (h_upd_joint n a)).stronglyMeasurable.integral_prod_right').measurable
    have hg_eq : ∀ u : ℝ, g u = ∫ z, Φ (Function.update (e.symm (0, z)) a u) ∂μ_out := by
      intro u
      dsimp only [g]
      rw [← h_mp.integral_comp' (fun τ => Φ (Function.update τ a u))]
      have h_upd_u : Measurable (fun τ : Fin n → ℝ => Function.update τ a u) :=
        (h_upd_joint n a).comp (measurable_const.prodMk measurable_id)
      have h_int_u : Integrable (fun q => Φ (Function.update (e.symm q) a u)) (μ_in.prod μ_out) :=
        MeasureTheory.Integrable.of_mem_Icc (-M) M
          (hΦ.comp (h_upd_u.comp e.symm.measurable)).aemeasurable
          (Filter.Eventually.of_forall (fun q => abs_le.mp (hΦ_bdd _)))
      rw [MeasureTheory.integral_prod _ h_int_u]
      have h_const : (fun x : {i // pred i} → ℝ =>
          ∫ z, Φ (Function.update (e.symm (x, z)) a u) ∂μ_out) =
          fun _ => ∫ z, Φ (Function.update (e.symm (0, z)) a u) ∂μ_out := by
        ext x
        congr 1
        ext z
        rw [h_id2 x z u]
      rw [h_const]
      simp [MeasureTheory.integral_const]
    have h_outer : ∫ τ, Φ τ ∂(unifCubeMeasure n r) = ∫ x, g (x a_sub) ∂μ_in := by
      rw [← h_mp.integral_comp' Φ]
      have h_int : Integrable (fun q => Φ (e.symm q)) (μ_in.prod μ_out) :=
        MeasureTheory.Integrable.of_mem_Icc (-M) M
          (hΦ.comp e.symm.measurable).aemeasurable
          (Filter.Eventually.of_forall (fun q => abs_le.mp (hΦ_bdd _)))
      rw [MeasureTheory.integral_prod _ h_int]
      congr 1
      ext x
      rw [hg_eq (x a_sub)]
      congr 1
      ext z
      rw [← h_id1 x z]
    have h_eval : MeasurePreserving (fun x : {i // pred i} → ℝ => x a_sub) μ_in ν := by
      subst hμ_in_eq
      exact MeasureTheory.measurePreserving_eval (fun _ : {i // pred i} => ν) a_sub
    have h_map_in : ∫ x, g (x a_sub) ∂μ_in = ∫ u, g u ∂ν := by
      rw [← h_eval.map_eq]
      exact (MeasureTheory.integral_map h_eval.measurable.aemeasurable
        (by rw [h_eval.map_eq]; exact hg_meas.aestronglyMeasurable)).symm
    have h_ν_int : ∫ u, g u ∂ν = r⁻¹ * ∫ u in Set.Icc (0 : ℝ) r, g u := by
      dsimp only [ν]
      rw [MeasureTheory.integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv,
        ENNReal.toReal_ofReal hr.le]
    rw [h_outer, h_map_in, h_ν_int, mul_inv_cancel_left₀ hr.ne']

  have h_trap : ∀ (a₀ t K : ℝ) (g : ℝ × ℝ → ℝ),
      0 ≤ a₀ →
      a₀ ≤ t →
      Measurable g →
      (∀ u ∈ Set.Icc (0 : ℝ) t, ∀ s ∈ Set.Icc a₀ t, |g (u, s)| ≤ K) →
        IntegrableOn (fun u => ∫ s in Set.Icc a₀ t, g (u, s)) (Set.Icc (0 : ℝ) a₀) volume ∧
        IntegrableOn (fun u => ∫ s in Set.Icc u t, g (u, s)) (Set.Ioc a₀ t) volume ∧
        (∫ u in Set.Icc (0 : ℝ) a₀, ∫ s in Set.Icc a₀ t, g (u, s)) +
        (∫ u in Set.Ioc a₀ t, ∫ s in Set.Icc u t, g (u, s)) =
          ∫ s in Set.Icc a₀ t, ∫ u in Set.Icc (0 : ℝ) s, g (u, s) := by
    intro a₀ t K g ha₀ ht hg hg_bdd
    have ht0 : 0 ≤ t := ha₀.trans ht
    have hK0 : 0 ≤ K :=
      (abs_nonneg (g (0, a₀))).trans (hg_bdd 0 ⟨le_rfl, ht0⟩ a₀ ⟨le_rfl, ht⟩)
    let μ_U : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) t)
    let μ_S : Measure ℝ := volume.restrict (Set.Icc a₀ t)
    haveI : IsFiniteMeasure μ_U := ⟨by simp [μ_U]⟩
    haveI : IsFiniteMeasure μ_S := ⟨by simp [μ_S]⟩
    let G : ℝ × ℝ → ℝ := fun p => if p.1 ≤ p.2 then g p else 0
    have hG_meas : Measurable G :=
      Measurable.ite (measurableSet_le measurable_fst measurable_snd) hg measurable_const
    have hG_int : Integrable G (μ_U.prod μ_S) := by
      refine MeasureTheory.Integrable.of_mem_Icc (-K) K hG_meas.aemeasurable ?_
      rw [show μ_U.prod μ_S = (volume.prod volume).restrict (Set.Icc (0 : ℝ) t ×ˢ Set.Icc a₀ t) from
        MeasureTheory.Measure.prod_restrict _ _]
      rw [MeasureTheory.ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)]
      refine Filter.Eventually.of_forall (fun p hp => abs_le.mp ?_)
      dsimp only [G]
      split_ifs with hle
      · exact hg_bdd p.1 hp.1 p.2 hp.2
      · simpa using hK0
    let L : ℝ → ℝ := fun u => ∫ s in Set.Icc a₀ t, G (u, s)
    have hL_int : IntegrableOn L (Set.Icc (0 : ℝ) t) volume := hG_int.integral_prod_left
    have h_sub1 : Set.Icc (0 : ℝ) a₀ ⊆ Set.Icc (0 : ℝ) t := Set.Icc_subset_Icc_right ht
    have h_sub2 : Set.Ioc a₀ t ⊆ Set.Icc (0 : ℝ) t :=
      Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_left ha₀)
    have hL_int1 : IntegrableOn L (Set.Icc (0 : ℝ) a₀) volume := hL_int.mono_set h_sub1
    have hL_int2 : IntegrableOn L (Set.Ioc a₀ t) volume := hL_int.mono_set h_sub2
    have hL_eq1 : Set.EqOn (fun u => ∫ s in Set.Icc a₀ t, g (u, s)) L (Set.Icc (0 : ℝ) a₀) := by
      intro u hu
      dsimp only [L]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun s hs => ?_)
      dsimp only [G]
      rw [if_pos (hu.2.trans hs.1)]
    have hL_eq2 : Set.EqOn (fun u => ∫ s in Set.Icc u t, g (u, s)) L (Set.Ioc a₀ t) := by
      intro u hu
      dsimp only [L]
      have h_ind : (fun s : ℝ => G (u, s)) = (Set.Ici u).indicator (fun s => g (u, s)) := by
        ext s
        simp [G, Set.indicator, Set.mem_Ici]
      rw [h_ind, MeasureTheory.integral_indicator measurableSet_Ici,
        MeasureTheory.Measure.restrict_restrict measurableSet_Ici]
      have h_set : Set.Ici u ∩ Set.Icc a₀ t = Set.Icc u t := by
        ext s
        simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
        exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h2⟩ => ⟨h1, hu.1.le.trans h1, h2⟩⟩
      rw [h_set]
    have h_int1 : IntegrableOn (fun u => ∫ s in Set.Icc a₀ t, g (u, s)) (Set.Icc (0 : ℝ) a₀) volume :=
      hL_int1.congr_fun hL_eq1.symm measurableSet_Icc
    have h_int2 : IntegrableOn (fun u => ∫ s in Set.Icc u t, g (u, s)) (Set.Ioc a₀ t) volume :=
      hL_int2.congr_fun hL_eq2.symm measurableSet_Ioc
    refine ⟨h_int1, h_int2, ?_⟩
    have h_fub : ∫ u in Set.Icc (0 : ℝ) t, L u =
        ∫ s in Set.Icc a₀ t, ∫ u in Set.Icc (0 : ℝ) t, G (u, s) :=
      (MeasureTheory.integral_prod G hG_int).symm.trans (MeasureTheory.integral_prod_symm G hG_int)
    have h_disj : Disjoint (Set.Icc (0 : ℝ) a₀) (Set.Ioc a₀ t) :=
      Set.disjoint_left.mpr (fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1)
    have h_lhs : ∫ u in Set.Icc (0 : ℝ) t, L u =
        (∫ u in Set.Icc (0 : ℝ) a₀, ∫ s in Set.Icc a₀ t, g (u, s)) +
        (∫ u in Set.Ioc a₀ t, ∫ s in Set.Icc u t, g (u, s)) := by
      rw [← Set.Icc_union_Ioc_eq_Icc ha₀ ht,
        MeasureTheory.setIntegral_union h_disj measurableSet_Ioc hL_int1 hL_int2,
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc hL_eq1.symm,
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hL_eq2.symm]
    have h_rhs : (∫ s in Set.Icc a₀ t, ∫ u in Set.Icc (0 : ℝ) t, G (u, s)) =
        ∫ s in Set.Icc a₀ t, ∫ u in Set.Icc (0 : ℝ) s, g (u, s) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun s hs => ?_)
      have h_ind : (fun u : ℝ => G (u, s)) = (Set.Iic s).indicator (fun u => g (u, s)) := by
        ext u
        simp [G, Set.indicator, Set.mem_Iic]
      rw [h_ind, MeasureTheory.integral_indicator measurableSet_Iic,
        MeasureTheory.Measure.restrict_restrict measurableSet_Iic]
      have h_set : Set.Iic s ∩ Set.Icc (0 : ℝ) t = Set.Icc (0 : ℝ) s := by
        ext u
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
        exact ⟨fun ⟨h1, h2, _⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, h2.trans hs.2⟩⟩
      rw [h_set]
    rw [← h_lhs, h_fub, h_rhs]

  have h_gen : ∀ (n : ℕ) (M : ℝ) (R : Finset (Fin n)) (a₀ t : ℝ) (Ψ : (Fin n → ℝ) → ℝ),
      0 < a₀ →
      a₀ ≤ t →
      Measurable Ψ →
      (∀ τ, |Ψ τ| ≤ M) →
      (∀ τ₁ τ₂, (∀ q ∈ R, τ₁ q = τ₂ q) → Ψ τ₁ = Ψ τ₂) →
        t ^ R.card * ∫ τ, Ψ τ ∂(unifCubeMeasure n t) =
          a₀ ^ R.card * ∫ τ, Ψ τ ∂(unifCubeMeasure n a₀) +
          ∑ x ∈ R,
            ∫ s in Set.Icc a₀ t,
              s ^ (R.erase x).card *
                ∫ τ, Ψ (Function.update τ x s) ∂(unifCubeMeasure n s) := by
    intro n M R
    induction R using Finset.induction_on with
    | empty =>
      intro a₀ t Ψ ha₀ ht _ _ hΨ_loc
      have ht_pos : 0 < t := ha₀.trans_le ht
      haveI : IsProbabilityMeasure (unifCubeMeasure n t) := (h_rescale n t ht_pos).1
      haveI : IsProbabilityMeasure (unifCubeMeasure n a₀) := (h_rescale n a₀ ha₀).1
      have hΨ_const : Ψ = fun _ => Ψ 0 := by
        ext τ
        exact hΨ_loc τ 0 (fun q hq => (Finset.notMem_empty q hq).elim)
      rw [hΨ_const]
      simp [MeasureTheory.integral_const]
    | @insert a R haR ih =>
      intro a₀ t Ψ ha₀ ht hΨ_meas hΨ_bdd hΨ_loc
      have ht_pos : 0 < t := ha₀.trans_le ht
      have hM_nn : 0 ≤ M := (abs_nonneg (Ψ 0)).trans (hΨ_bdd 0)
      let Ψ_u : ℝ → (Fin n → ℝ) → ℝ := fun u τ => Ψ (Function.update τ a u)
      have hΨu_meas : ∀ u : ℝ, Measurable (Ψ_u u) :=
        fun u => hΨ_meas.comp ((h_upd_joint n a).comp (measurable_const.prodMk measurable_id))
      have hΨu_bdd : ∀ (u : ℝ) (τ : Fin n → ℝ), |Ψ_u u τ| ≤ M :=
        fun u τ => hΨ_bdd (Function.update τ a u)
      have hΨu_loc : ∀ (u : ℝ) (τ₁ τ₂ : Fin n → ℝ),
          (∀ q ∈ R, τ₁ q = τ₂ q) → Ψ_u u τ₁ = Ψ_u u τ₂ := by
        intro u τ₁ τ₂ hqR
        refine hΨ_loc _ _ (fun q hq => ?_)
        rcases Finset.mem_insert.mp hq with rfl | hq'
        · simp
        · have hqa : q ≠ a := fun h => haR (h ▸ hq')
          rw [Function.update_of_ne hqa, Function.update_of_ne hqa]
          exact hqR q hq'
      have h_int_on_Icc : ∀ {b c : ℝ} (B : ℝ) {f : ℝ → ℝ},
          Measurable f → (∀ u ∈ Set.Icc b c, |f u| ≤ B) →
          IntegrableOn f (Set.Icc b c) volume := by
        intro b c B f hf hf_bdd
        haveI : IsFiniteMeasure (volume.restrict (Set.Icc b c)) := ⟨by simp⟩
        refine MeasureTheory.Integrable.of_mem_Icc (-B) B hf.aemeasurable ?_
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
        exact Filter.Eventually.of_forall (fun u hu => abs_le.mp (hf_bdd u hu))
      let φ : ℝ → ℝ := fun u => t ^ R.card * ∫ τ, Ψ_u u τ ∂(unifCubeMeasure n t)
      have h_lhs_slice : t ^ (insert a R).card * ∫ τ, Ψ τ ∂(unifCubeMeasure n t) =
          ∫ u in Set.Icc (0 : ℝ) t, φ u := by
        rw [Finset.card_insert_of_notMem haR, pow_succ, mul_assoc,
          h_slice n a M t Ψ ht_pos hΨ_meas hΨ_bdd, ← MeasureTheory.integral_const_mul]
      obtain ⟨hJt_meas, hJt_bdd, hJt_eq⟩ :=
        h_param ℝ n M (fun _ : ℝ => t) (fun p => Ψ (Function.update p.2 a p.1))
          measurable_const (hΨ_meas.comp (h_upd_joint n a)) (fun p => hΨ_bdd _)
      have hφ_eq_J : φ = fun u => t ^ R.card * ∫ ω, Ψ (Function.update (fun i => t * ω i) a u) ∂(unifCubeMeasure n 1) := by
        ext u
        dsimp only [φ, Ψ_u]
        rw [hJt_eq u ht_pos]
      have hφ_meas : Measurable φ := by
        rw [hφ_eq_J]
        exact hJt_meas.const_mul (t ^ R.card)
      have hφ_bdd : ∀ u : ℝ, |φ u| ≤ t ^ R.card * M := by
        intro u
        rw [hφ_eq_J]
        dsimp only
        rw [abs_mul, abs_of_nonneg (pow_nonneg ht_pos.le R.card)]
        exact mul_le_mul_of_nonneg_left (hJt_bdd u) (pow_nonneg ht_pos.le R.card)
      have hφ_int_all : IntegrableOn φ (Set.Icc (0 : ℝ) t) volume :=
        h_int_on_Icc (t ^ R.card * M) hφ_meas (fun u _ => hφ_bdd u)
      have hφ_int1 : IntegrableOn φ (Set.Icc (0 : ℝ) a₀) volume :=
        hφ_int_all.mono_set (Set.Icc_subset_Icc_right ht)
      have hφ_int2 : IntegrableOn φ (Set.Ioc a₀ t) volume :=
        hφ_int_all.mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_left ha₀.le))
      have h_disj : Disjoint (Set.Icc (0 : ℝ) a₀) (Set.Ioc a₀ t) :=
        Set.disjoint_left.mpr (fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1)
      have h_lhs_split : ∫ u in Set.Icc (0 : ℝ) t, φ u =
          (∫ u in Set.Icc (0 : ℝ) a₀, φ u) + (∫ u in Set.Ioc a₀ t, φ u) := by
        rw [← Set.Icc_union_Ioc_eq_Icc ha₀.le ht,
          MeasureTheory.setIntegral_union h_disj measurableSet_Ioc hφ_int1 hφ_int2]
      let ψ₀ : ℝ → ℝ := fun u => a₀ ^ R.card * ∫ τ, Ψ_u u τ ∂(unifCubeMeasure n a₀)
      obtain ⟨hJa₀_meas, hJa₀_bdd, hJa₀_eq⟩ :=
        h_param ℝ n M (fun _ : ℝ => a₀) (fun p => Ψ (Function.update p.2 a p.1))
          measurable_const (hΨ_meas.comp (h_upd_joint n a)) (fun p => hΨ_bdd _)
      have hψ₀_eq_J : ψ₀ = fun u => a₀ ^ R.card * ∫ ω, Ψ (Function.update (fun i => a₀ * ω i) a u) ∂(unifCubeMeasure n 1) := by
        ext u
        dsimp only [ψ₀, Ψ_u]
        rw [hJa₀_eq u ha₀]
      have hψ₀_int : IntegrableOn ψ₀ (Set.Icc (0 : ℝ) a₀) volume := by
        refine h_int_on_Icc (a₀ ^ R.card * M) (by rw [hψ₀_eq_J]; exact hJa₀_meas.const_mul _) (fun u _ => ?_)
        rw [hψ₀_eq_J]
        dsimp only
        rw [abs_mul, abs_of_nonneg (pow_nonneg ha₀.le R.card)]
        exact mul_le_mul_of_nonneg_left (hJa₀_bdd u) (pow_nonneg ha₀.le R.card)
      have h_int_sum : ∀ (K_fin : Finset (Fin n)) {S_set : Set ℝ} (F : Fin n → ℝ → ℝ),
          (∀ x ∈ K_fin, IntegrableOn (F x) S_set volume) →
          IntegrableOn (fun u => ∑ x ∈ K_fin, F x u) S_set volume := by
        intro K_fin
        induction K_fin using Finset.induction_on with
        | empty =>
          intro S_set F _
          simp
        | @insert z T hzT ihT =>
          intro S_set F hF
          have h_eq_s : (fun u => ∑ x ∈ insert z T, F x u) =
              fun u => F z u + ∑ x ∈ T, F x u :=
            funext (fun u => Finset.sum_insert hzT)
          rw [h_eq_s]
          exact (hF z (Finset.mem_insert_self z T)).add
            (ihT F (fun x hx => hF x (Finset.mem_insert_of_mem hx)))
      obtain ⟨hJa_meas, hJa_bdd, hJa_eq⟩ :=
        h_param ℝ n M (fun u : ℝ => u) (fun p => Ψ (Function.update p.2 a p.1))
          measurable_id (hΨ_meas.comp (h_upd_joint n a)) (fun p => hΨ_bdd _)
      let h_a : ℝ → ℝ := fun u =>
        u ^ R.card * ∫ ω, Ψ (Function.update (fun i => u * ω i) a u) ∂(unifCubeMeasure n 1)
      have hha_int : IntegrableOn h_a (Set.Ioc a₀ t) volume := by
        have hha_all : IntegrableOn h_a (Set.Icc (0 : ℝ) t) volume := by
          refine h_int_on_Icc (t ^ R.card * M) ((measurable_id.pow_const R.card).mul hJa_meas) (fun u hu => ?_)
          dsimp only [h_a]
          rw [abs_mul, abs_of_nonneg (pow_nonneg hu.1 R.card)]
          exact mul_le_mul (pow_le_pow_left₀ hu.1 hu.2 R.card) (hJa_bdd u) (abs_nonneg _)
            (pow_nonneg ht_pos.le R.card)
        exact hha_all.mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_left ha₀.le))
      let g_tilde : Fin n → ℝ × ℝ → ℝ := fun x p =>
        p.2 ^ (R.erase x).card *
          ∫ ω, Ψ (Function.update (Function.update (fun i => p.2 * ω i) x p.2) a p.1)
            ∂(unifCubeMeasure n 1)
      have hg_props : ∀ x : Fin n,
          (∀ u s : ℝ, 0 < s →
            s ^ (R.erase x).card * ∫ τ, Ψ_u u (Function.update τ x s) ∂(unifCubeMeasure n s) =
              g_tilde x (u, s)) ∧
          IntegrableOn (fun u => ∫ s in Set.Icc a₀ t, g_tilde x (u, s)) (Set.Icc (0 : ℝ) a₀) volume ∧
          IntegrableOn (fun u => ∫ s in Set.Icc u t, g_tilde x (u, s)) (Set.Ioc a₀ t) volume ∧
          (∫ u in Set.Icc (0 : ℝ) a₀, ∫ s in Set.Icc a₀ t, g_tilde x (u, s)) +
          (∫ u in Set.Ioc a₀ t, ∫ s in Set.Icc u t, g_tilde x (u, s)) =
            ∫ s in Set.Icc a₀ t, ∫ u in Set.Icc (0 : ℝ) s, g_tilde x (u, s) := by
        intro x
        have h_dbl_meas : Measurable (fun q : (ℝ × ℝ) × (Fin n → ℝ) =>
            Ψ (Function.update (Function.update q.2 x q.1.2) a q.1.1)) :=
          hΨ_meas.comp ((h_upd_joint n a).comp
            ((measurable_fst.comp measurable_fst).prodMk
              ((h_upd_joint n x).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))))
        obtain ⟨hJx_meas, hJx_bdd, hJx_eq⟩ :=
          h_param (ℝ × ℝ) n M Prod.snd
            (fun q : (ℝ × ℝ) × (Fin n → ℝ) =>
              Ψ (Function.update (Function.update q.2 x q.1.2) a q.1.1))
            measurable_snd h_dbl_meas (fun _ => hΨ_bdd _)
        have hgx_meas : Measurable (g_tilde x) :=
          (measurable_snd.pow_const (R.erase x).card).mul hJx_meas
        have hgx_bdd : ∀ u ∈ Set.Icc (0 : ℝ) t, ∀ s ∈ Set.Icc a₀ t,
            |g_tilde x (u, s)| ≤ t ^ (R.erase x).card * M := by
          intro u _ s hs
          have hs0 : 0 ≤ s := ha₀.le.trans hs.1
          dsimp only [g_tilde]
          rw [abs_mul, abs_of_nonneg (pow_nonneg hs0 (R.erase x).card)]
          exact mul_le_mul (pow_le_pow_left₀ hs0 hs.2 (R.erase x).card) (hJx_bdd (u, s))
            (abs_nonneg _) (pow_nonneg ht_pos.le (R.erase x).card)
        obtain ⟨hi1, hi2, hsw⟩ :=
          h_trap a₀ t (t ^ (R.erase x).card * M) (g_tilde x) ha₀.le ht hgx_meas hgx_bdd
        refine ⟨fun u s hs => ?_, hi1, hi2, hsw⟩
        dsimp only [g_tilde, Ψ_u]
        have h_eq := hJx_eq (u, s) hs
        dsimp only at h_eq
        rw [h_eq]
      have h_part1 : ∫ u in Set.Icc (0 : ℝ) a₀, φ u =
          a₀ ^ (insert a R).card * ∫ τ, Ψ τ ∂(unifCubeMeasure n a₀) +
          ∑ x ∈ R, ∫ u in Set.Icc (0 : ℝ) a₀, ∫ s in Set.Icc a₀ t, g_tilde x (u, s) := by
        have h_congr1 : Set.EqOn φ
            (fun u => ψ₀ u + ∑ x ∈ R, ∫ s in Set.Icc a₀ t, g_tilde x (u, s))
            (Set.Icc (0 : ℝ) a₀) := by
          intro u _
          dsimp only [φ, ψ₀]
          rw [ih a₀ t (Ψ_u u) ha₀ ht (hΨu_meas u) (hΨu_bdd u) (hΨu_loc u)]
          congr 1
          refine Finset.sum_congr rfl (fun x _ => ?_)
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun s hs => ?_)
          exact (hg_props x).1 u s (ha₀.trans_le hs.1)
        have h_sum_int1 : IntegrableOn
            (fun u => ∑ x ∈ R, ∫ s in Set.Icc a₀ t, g_tilde x (u, s))
            (Set.Icc (0 : ℝ) a₀) volume :=
          h_int_sum R _ (fun x _ => (hg_props x).2.1)
        rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc h_congr1,
          MeasureTheory.integral_add hψ₀_int h_sum_int1,
          MeasureTheory.integral_finset_sum R (fun x _ => (hg_props x).2.1)]
        congr 1
        dsimp only [ψ₀, Ψ_u]
        rw [MeasureTheory.integral_const_mul,
          ← h_slice n a M a₀ Ψ ha₀ hΨ_meas hΨ_bdd,
          ← mul_assoc, ← pow_succ, Finset.card_insert_of_notMem haR]
      have h_part2 : ∫ u in Set.Ioc a₀ t, φ u =
          (∫ s in Set.Icc a₀ t,
            s ^ ((insert a R).erase a).card *
              ∫ τ, Ψ (Function.update τ a s) ∂(unifCubeMeasure n s)) +
          ∑ x ∈ R, ∫ u in Set.Ioc a₀ t, ∫ s in Set.Icc u t, g_tilde x (u, s) := by
        have h_congr2 : Set.EqOn φ
            (fun u => h_a u + ∑ x ∈ R, ∫ s in Set.Icc u t, g_tilde x (u, s))
            (Set.Ioc a₀ t) := by
          intro u hu
          have hu_pos : 0 < u := ha₀.trans hu.1
          dsimp only [φ]
          rw [ih u t (Ψ_u u) hu_pos hu.2 (hΨu_meas u) (hΨu_bdd u) (hΨu_loc u)]
          congr 1
          · have h_eq := hJa_eq u hu_pos
            dsimp only at h_eq
            dsimp only [h_a, Ψ_u]
            rw [h_eq]
          · refine Finset.sum_congr rfl (fun x _ => ?_)
            refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun s hs => ?_)
            exact (hg_props x).1 u s (hu_pos.trans_le hs.1)
        have h_sum_int2 : IntegrableOn
            (fun u => ∑ x ∈ R, ∫ s in Set.Icc u t, g_tilde x (u, s))
            (Set.Ioc a₀ t) volume :=
          h_int_sum R _ (fun x _ => (hg_props x).2.2.1)
        rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc h_congr2,
          MeasureTheory.integral_add hha_int h_sum_int2,
          MeasureTheory.integral_finset_sum R (fun x _ => (hg_props x).2.2.1)]
        congr 1
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, Finset.erase_insert haR]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
        have h_eq := hJa_eq s (ha₀.trans hs.1)
        dsimp only at h_eq
        dsimp only [h_a]
        rw [← h_eq]
      have h_merge : ∀ x ∈ R,
          (∫ u in Set.Icc (0 : ℝ) a₀, ∫ s in Set.Icc a₀ t, g_tilde x (u, s)) +
          (∫ u in Set.Ioc a₀ t, ∫ s in Set.Icc u t, g_tilde x (u, s)) =
          ∫ s in Set.Icc a₀ t,
            s ^ ((insert a R).erase x).card *
              ∫ τ, Ψ (Function.update τ x s) ∂(unifCubeMeasure n s) := by
        intro x hxR
        have hxa : x ≠ a := fun h => haR (h ▸ hxR)
        rw [(hg_props x).2.2.2]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun s hs => ?_)
        have hs_pos : 0 < s := ha₀.trans_le hs.1
        have h_inner_eq : Set.EqOn (fun u => g_tilde x (u, s))
            (fun u => s ^ (R.erase x).card *
              ∫ τ, Ψ (Function.update (Function.update τ a u) x s) ∂(unifCubeMeasure n s))
            (Set.Icc (0 : ℝ) s) := by
          intro u _
          dsimp only
          rw [← (hg_props x).1 u s hs_pos]
          dsimp only [Ψ_u]
          congr 2
          ext τ
          rw [Function.update_comm hxa s u τ]
        have hΦ_xs_meas : Measurable (fun τ' : Fin n → ℝ => Ψ (Function.update τ' x s)) :=
          hΨ_meas.comp ((h_upd_joint n x).comp (measurable_const.prodMk measurable_id))
        have h_card_er : ((insert a R).erase x).card = (R.erase x).card + 1 := by
          rw [Finset.erase_insert_of_ne hxa.symm,
            Finset.card_insert_of_notMem (fun h => haR (Finset.mem_erase.mp h).2)]
        rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc h_inner_eq,
          MeasureTheory.integral_const_mul,
          ← h_slice n a M s (fun τ' => Ψ (Function.update τ' x s)) hs_pos hΦ_xs_meas
            (fun τ' => hΨ_bdd _),
          ← mul_assoc, ← pow_succ, h_card_er]
      rw [h_lhs_slice, h_lhs_split, h_part1, h_part2]
      have h_rearr :
          (a₀ ^ (insert a R).card * ∫ τ, Ψ τ ∂(unifCubeMeasure n a₀) +
            ∑ x ∈ R, ∫ u in Set.Icc (0 : ℝ) a₀, ∫ s in Set.Icc a₀ t, g_tilde x (u, s)) +
          ((∫ s in Set.Icc a₀ t,
              s ^ ((insert a R).erase a).card *
                ∫ τ, Ψ (Function.update τ a s) ∂(unifCubeMeasure n s)) +
            ∑ x ∈ R, ∫ u in Set.Ioc a₀ t, ∫ s in Set.Icc u t, g_tilde x (u, s)) =
          a₀ ^ (insert a R).card * ∫ τ, Ψ τ ∂(unifCubeMeasure n a₀) +
          ((∫ s in Set.Icc a₀ t,
              s ^ ((insert a R).erase a).card *
                ∫ τ, Ψ (Function.update τ a s) ∂(unifCubeMeasure n s)) +
            ∑ x ∈ R,
              ((∫ u in Set.Icc (0 : ℝ) a₀, ∫ s in Set.Icc a₀ t, g_tilde x (u, s)) +
               (∫ u in Set.Ioc a₀ t, ∫ s in Set.Icc u t, g_tilde x (u, s)))) := by
        rw [Finset.sum_add_distrib]
        ring
      rw [h_rearr, Finset.sum_congr rfl h_merge, Finset.sum_insert haR]

  intro n Q M t Ψ ht1 hΨ_meas hΨ_bdd hΨ_loc
  have h_invE_pos : 0 < invE := by
    unfold invE
    exact Real.exp_pos (-1)
  have h_invE_pow : invE ^ Q.card = Real.exp (-(Q.card : ℝ)) := by
    unfold invE
    rw [← Real.exp_nat_mul]
    simp
  rw [h_gen n M Q invE t Ψ h_invE_pos ht1 hΨ_meas hΨ_bdd hΨ_loc, h_invE_pow]

theorem inclusion_mass_ftc_and_boundary : ∀ (n : ℕ) (v : ItemValuation n) (Q A : Finset (Fin n)) (t : ℝ),
      A ⊆ Q → invE ≤ t → t ≤ 1 →
      (∀ T ⊆ Q, canonicalDemand v Q ∩ T ⊆ canonicalDemand v T) →
      (∀ x ∈ A ∩ canonicalDemand v Q, ∀ T ⊆ Q.erase x,
        canonicalDemand (contractVal v x) T = (canonicalDemand v (insert x T)).erase x) →
        let s₀ : (Fin n → ℝ) → ℝ := fun τ =>
          (insert invE (Q.image (fun q => min 1 (τ q)))).max' (Finset.insert_nonempty _ _)
        let Ψ : (Fin n → ℝ) → ℝ := fun τ =>
          ∏ g ∈ A, retentionProb (canonicalDemand v) (s₀ τ) Q ∅ τ (fun _ => s₀ τ) g
        (Measurable Ψ ∧ (∀ τ, |Ψ τ| ≤ 1) ∧
          (∀ τ₁ τ₂, (∀ q ∈ Q, τ₁ q = τ₂ q) → Ψ τ₁ = Ψ τ₂)) ∧
        (inclusionMass v Q A t =
          t ^ Q.card * ∫ τ, Ψ τ ∂(unifCubeMeasure n t) +
          ∑ x ∈ A ∩ canonicalDemand v Q,
            ∫ s in Set.Icc invE t,
              (1 / (Real.exp 1 * s)) *
                inclusionMass (contractVal v x) (Q.erase x) (A.erase x) s) ∧
        ((∫ τ, Ψ τ ∂(unifCubeMeasure n invE)) = (if A = ∅ then 1 else 0) ∧
         (∀ x ∈ A, ∀ s : ℝ, invE < s → ∀ τ, Ψ (Function.update τ x s) = 0) ∧
         (∀ x ∈ Q \ A, ∀ s : ℝ, invE < s → s ≤ t →
           s ^ (Q.erase x).card * ∫ τ, Ψ (Function.update τ x s) ∂(unifCubeMeasure n s) =
             inclusionMass v (Q.erase x) A s)) :=
by
  intro n v Q A t hAQ ht1 ht2 h_persQ h_commQ s₀ Ψ
  have h_invE_pos : 0 < invE := by
    unfold invE
    exact Real.exp_pos (-1)
  have h_exp_invE : Real.exp 1 * invE = 1 := by
    unfold invE
    rw [← Real.exp_add]
    norm_num
  have h_invE_le_one : invE ≤ 1 := by
    unfold invE
    calc Real.exp (-1) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by norm_num)
      _ = 1 := Real.exp_zero
  have ht_pos : 0 < t := h_invE_pos.trans_le ht1
  have h_pres_empty : ∀ (S : Finset (Fin n)) (τ β : Fin n → ℝ) (u : ℝ),
      presentSet S ∅ τ β u = S.filter (fun q => τ q ≤ u) := by
    intro S τ β u
    simp [presentSet]
  have h_dt_bounds : ∀ (C : Finset (Fin n) → Finset (Fin n)) {r₀ : ℝ},
      invE ≤ r₀ → ∀ (S B : Finset (Fin n)) (τ β : Fin n → ℝ) (g : Fin n),
      invE ≤ deathTime C r₀ S B τ β g ∧ deathTime C r₀ S B τ β g ≤ r₀ := by
    intro C r₀ hr₀ S B τ β g
    let E : Set ℝ := {u : ℝ | invE ≤ u ∧ u ≤ r₀ ∧ g ∉ C (presentSet S B τ β u)} ∪ {r₀}
    have hrE : r₀ ∈ E := Set.mem_union_right _ rfl
    have h_lo_E : ∀ u ∈ E, invE ≤ u := by
      rintro u (hu | hu)
      · exact hu.1
      · rw [Set.mem_singleton_iff.mp hu]
        exact hr₀
    exact ⟨le_csInf ⟨r₀, hrE⟩ h_lo_E, csInf_le ⟨invE, h_lo_E⟩ hrE⟩
  have h_ret_bounds : ∀ (C : Finset (Fin n) → Finset (Fin n)) {r₀ : ℝ},
      invE ≤ r₀ → r₀ ≤ 1 →
      ∀ (S B : Finset (Fin n)) (τ β : Fin n → ℝ) (g : Fin n),
      0 ≤ retentionProb C r₀ S B τ β g ∧ retentionProb C r₀ S B τ β g ≤ 1 := by
    intro C r₀ hr_lo hr_hi S B τ β g
    unfold retentionProb
    split_ifs with hτ
    · obtain ⟨h_lo, h_hi⟩ := h_dt_bounds C hr_lo S B τ β g
      have hexp1 : 1 ≤ Real.exp 1 * deathTime C r₀ S B τ β g := by
        calc (1 : ℝ) = Real.exp 1 * invE := h_exp_invE.symm
          _ ≤ Real.exp 1 * deathTime C r₀ S B τ β g :=
            mul_le_mul_of_nonneg_left h_lo (Real.exp_pos 1).le
      have hexp2 : Real.exp 1 * deathTime C r₀ S B τ β g ≤ Real.exp 1 := by
        calc Real.exp 1 * deathTime C r₀ S B τ β g ≤ Real.exp 1 * 1 :=
            mul_le_mul_of_nonneg_left (h_hi.trans hr_hi) (Real.exp_pos 1).le
          _ = Real.exp 1 := mul_one _
      refine ⟨Real.log_nonneg hexp1, ?_⟩
      calc Real.log (Real.exp 1 * deathTime C r₀ S B τ β g)
          ≤ Real.log (Real.exp 1) := Real.log_le_log (by linarith) hexp2
        _ = 1 := Real.log_exp 1
    · exact ⟨le_rfl, zero_le_one⟩
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

  
  have h_s1_reg : ∀ (C : Finset (Fin n) → Finset (Fin n)) (P : Finset (Fin n))
      (r : (Fin n → ℝ) → ℝ),
      Measurable r →
      (∀ τ, invE ≤ r τ ∧ r τ ≤ 1) →
      (∀ τ₁ τ₂, (∀ q ∈ P, τ₁ q = τ₂ q) → r τ₁ = r τ₂) →
      (∀ g : Fin n, Measurable (fun τ => retentionProb C (r τ) P ∅ τ (fun _ => r τ) g)) ∧
      (∀ (g : Fin n) (τ : Fin n → ℝ),
        0 ≤ retentionProb C (r τ) P ∅ τ (fun _ => r τ) g ∧
        retentionProb C (r τ) P ∅ τ (fun _ => r τ) g ≤ 1) ∧
      (∀ g ∈ P, ∀ τ₁ τ₂ : Fin n → ℝ, (∀ q ∈ P, τ₁ q = τ₂ q) →
        retentionProb C (r τ₁) P ∅ τ₁ (fun _ => r τ₁) g =
          retentionProb C (r τ₂) P ∅ τ₂ (fun _ => r τ₂) g) := by
    intro C P r hr_meas hr_bdd hr_loc
    have h_meas_dt : ∀ g : Fin n,
        Measurable (fun τ => deathTime C (r τ) P ∅ τ (fun _ => r τ) g) := by
      intro g
      let Cand := Bool ⊕ {q // q ∈ P}
      let candVal : Cand → (Fin n → ℝ) → ℝ := fun c τ => match c with
        | Sum.inl true => invE
        | Sum.inl false => r τ
        | Sum.inr q => τ q.1
      let candEff : Cand → (Fin n → ℝ) → ℝ := fun c τ =>
        let u := candVal c τ
        if invE ≤ u ∧ u ≤ r τ ∧ g ∉ C (presentSet P ∅ τ (fun _ => r τ) u) then u else r τ
      have hne : (Finset.univ : Finset Cand).Nonempty := ⟨Sum.inl true, Finset.mem_univ _⟩
      have h_eq : ∀ τ, deathTime C (r τ) P ∅ τ (fun _ => r τ) g =
          (Finset.univ : Finset Cand).inf' hne (fun c => candEff c τ) := by
        intro τ
        let E : Set ℝ := {u : ℝ | invE ≤ u ∧ u ≤ r τ ∧ g ∉ C (presentSet P ∅ τ (fun _ => r τ) u)} ∪ {r τ}
        have hrE : r τ ∈ E := Set.mem_union_right _ rfl
        have hBdd : BddBelow E := ⟨invE, by
          rintro u (hu | hu)
          · exact hu.1
          · rw [Set.mem_singleton_iff.mp hu]
            exact (hr_bdd τ).1⟩
        apply le_antisymm
        · refine Finset.le_inf' hne (fun c => candEff c τ) (fun c _ => csInf_le hBdd ?_)
          dsimp only [candEff]
          split_ifs with hc
          · exact Set.mem_union_left _ hc
          · exact hrE
        · refine le_csInf ⟨r τ, hrE⟩ (fun u_val hu_val => ?_)
          rcases hu_val with ⟨hu_lo, hu_hi, hu_not⟩ | hu_eq
          · let L := (Finset.univ : Finset Cand).filter (fun c => candVal c τ ≤ u_val)
            have h_true_L : (Sum.inl true : Cand) ∈ L :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu_lo⟩
            have hL_ne : L.Nonempty := ⟨Sum.inl true, h_true_L⟩
            obtain ⟨c₀, hc₀L, hc₀_eq⟩ := Finset.exists_mem_eq_sup' hL_ne (fun c => candVal c τ)
            let u₀ := L.sup' hL_ne (fun c => candVal c τ)
            have hu₀_eq : candVal c₀ τ = u₀ := hc₀_eq.symm
            have hu₀_lo : invE ≤ u₀ := Finset.le_sup' (fun c => candVal c τ) h_true_L
            have hu₀_v : u₀ ≤ u_val := by
              rw [← hu₀_eq]
              exact (Finset.mem_filter.mp hc₀L).2
            have h_pres : presentSet P ∅ τ (fun _ => r τ) u₀ =
                presentSet P ∅ τ (fun _ => r τ) u_val := by
              rw [h_pres_empty, h_pres_empty]
              ext z
              simp only [Finset.mem_filter]
              refine ⟨fun ⟨hz, hle⟩ => ⟨hz, hle.trans hu₀_v⟩, fun ⟨hz, hle⟩ => ⟨hz, ?_⟩⟩
              have hcL : (Sum.inr ⟨z, hz⟩ : Cand) ∈ L :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩
              exact Finset.le_sup' (fun c => candVal c τ) hcL
            have hc₀_eff : candEff c₀ τ = u₀ := by
              dsimp only [candEff]
              rw [hu₀_eq, h_pres]
              exact if_pos ⟨hu₀_lo, hu₀_v.trans hu_hi, hu_not⟩
            calc (Finset.univ : Finset Cand).inf' hne (fun c => candEff c τ)
                ≤ candEff c₀ τ := Finset.inf'_le (fun c => candEff c τ) (Finset.mem_univ c₀)
              _ = u₀ := hc₀_eff
              _ ≤ u_val := hu₀_v
          · rw [Set.mem_singleton_iff.mp hu_eq]
            have h_false : candEff (Sum.inl false) τ = r τ := by
              dsimp only [candEff, candVal]
              split_ifs <;> rfl
            calc (Finset.univ : Finset Cand).inf' hne (fun c => candEff c τ)
                ≤ candEff (Sum.inl false) τ :=
                  Finset.inf'_le (fun c => candEff c τ) (Finset.mem_univ (Sum.inl false))
              _ = r τ := h_false
      simp_rw [h_eq]
      refine h_meas_inf _ _ candEff (fun c _ => ?_)
      have hu : Measurable (candVal c) := by
        rcases c with (_ | _) | q
        · exact hr_meas
        · exact measurable_const
        · exact measurable_pi_apply q.1
      have h_set_pres : ∀ z : Fin n,
          MeasurableSet {τ : Fin n → ℝ | z ∈ presentSet P ∅ τ (fun _ => r τ) (candVal c τ)} := by
        intro z
        have heq_z : {τ : Fin n → ℝ | z ∈ presentSet P ∅ τ (fun _ => r τ) (candVal c τ)} =
            if z ∈ P then {τ | τ z ≤ candVal c τ} else ∅ := by
          ext τ
          simp [presentSet]
        rw [heq_z]
        split_ifs
        · exact measurableSet_le (measurable_pi_apply z) hu
        · exact MeasurableSet.empty
      have h_notC : MeasurableSet
          {τ : Fin n → ℝ | g ∉ C (presentSet P ∅ τ (fun _ => r τ) (candVal c τ))} := by
        let badSets := (Finset.univ : Finset (Finset (Fin n))).filter (fun U => g ∉ C U)
        have heq_bad : {τ : Fin n → ℝ | g ∉ C (presentSet P ∅ τ (fun _ => r τ) (candVal c τ))} =
            ⋃ U ∈ badSets, ⋂ z : Fin n,
              if z ∈ U then {τ | z ∈ presentSet P ∅ τ (fun _ => r τ) (candVal c τ)}
              else {τ | z ∈ presentSet P ∅ τ (fun _ => r τ) (candVal c τ)}ᶜ := by
          ext τ
          simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, badSets, Finset.mem_filter,
            Finset.mem_univ, true_and]
          refine ⟨fun hg => ⟨presentSet P ∅ τ (fun _ => r τ) (candVal c τ), hg, fun z => ?_⟩, ?_⟩
          · split_ifs with hz <;> simp [hz]
          · rintro ⟨U, hgU, hzU⟩
            have hU_eq : presentSet P ∅ τ (fun _ => r τ) (candVal c τ) = U := by
              ext z
              specialize hzU z
              by_cases hz : z ∈ U <;> simp [hz] at hzU ⊢ <;> exact hzU
            rwa [hU_eq]
        rw [heq_bad]
        refine Finset.measurableSet_biUnion _ (fun U _ => MeasurableSet.iInter (fun z => ?_))
        split_ifs
        · exact h_set_pres z
        · exact (h_set_pres z).compl
      have h_cond : MeasurableSet {τ : Fin n → ℝ | invE ≤ candVal c τ ∧ candVal c τ ≤ r τ ∧
          g ∉ C (presentSet P ∅ τ (fun _ => r τ) (candVal c τ))} :=
        (measurableSet_le measurable_const hu).inter
          ((measurableSet_le hu hr_meas).inter h_notC)
      exact Measurable.ite h_cond hu hr_meas
    refine ⟨?_, ?_, ?_⟩
    · intro g
      unfold retentionProb
      exact Measurable.ite (measurableSet_le (measurable_pi_apply g) measurable_const)
        (Real.measurable_log.comp (measurable_const.mul (h_meas_dt g))) measurable_const
    · intro g τ
      exact h_ret_bounds C (hr_bdd τ).1 (hr_bdd τ).2 P ∅ τ (fun _ => r τ) g
    · intro g hgP τ₁ τ₂ hq
      have hr_eq : r τ₁ = r τ₂ := hr_loc τ₁ τ₂ hq
      have hτg : τ₁ g = τ₂ g := hq g hgP
      have h_pres_eq : ∀ u : ℝ,
          presentSet P ∅ τ₁ (fun _ => r τ₁) u = presentSet P ∅ τ₂ (fun _ => r τ₂) u := by
        intro u
        rw [h_pres_empty, h_pres_empty]
        exact Finset.filter_congr (fun q hqP => by rw [hq q hqP])
      unfold retentionProb deathTime
      simp_rw [hτg, h_pres_eq, hr_eq]

  
  let ν : ℝ → Measure ℝ :=
    fun r => (ENNReal.ofReal r)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) r)
  have h_ν_prob : ∀ {r : ℝ}, 0 < r → IsProbabilityMeasure (ν r) := by
    intro r hr
    rw [MeasureTheory.isProbabilityMeasure_iff]
    simp only [ν, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul, Real.volume_Icc,
      sub_zero]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top
  have h_cube_prob : ∀ {r : ℝ}, 0 < r → IsProbabilityMeasure (unifCubeMeasure n r) := by
    intro r hr
    haveI : IsProbabilityMeasure (ν r) := h_ν_prob hr
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin n => ν r))
    infer_instance
  have h_cube_ae : ∀ {r : ℝ}, 0 < r →
      ∀ᵐ τ ∂(unifCubeMeasure n r), ∀ i : Fin n, 0 ≤ τ i ∧ τ i ≤ r := by
    intro r hr
    haveI : IsProbabilityMeasure (ν r) := h_ν_prob hr
    have h1d : ∀ᵐ u ∂(ν r), 0 ≤ u ∧ u ≤ r := by
      rw [ae_iff]
      have hset : {u : ℝ | ¬(0 ≤ u ∧ u ≤ r)} = (Set.Icc (0 : ℝ) r)ᶜ := by
        ext u; simp [Set.mem_Icc]
      rw [hset]
      simp [ν, Measure.restrict_apply measurableSet_Icc.compl]
    unfold unifCubeMeasure
    exact Filter.eventually_all.mpr (fun i =>
      (MeasureTheory.measurePreserving_eval (fun _ : Fin n => ν r) i).quasiMeasurePreserving.ae h1d)

  
  have h_s1_incl : ∀ (w : ItemValuation n) (P B : Finset (Fin n)) (s : ℝ),
      B ⊆ P → invE ≤ s → s ≤ 1 →
        survivalInclProb w P B s =
          ∫ τ, (∏ g ∈ B, retentionProb (canonicalDemand w) s P ∅ τ (fun _ => s) g)
            ∂(unifCubeMeasure n s) := by
    intro w P B s hBP hs1 hs2
    have hs_pos : 0 < s := h_invE_pos.trans_le hs1
    haveI : IsProbabilityMeasure (unifCubeMeasure n s) := h_cube_prob hs_pos
    obtain ⟨h_ret_m, h_ret_b, _⟩ :=
      h_s1_reg (canonicalDemand w) P (fun _ => s) measurable_const
        (fun _ => ⟨hs1, hs2⟩) (fun _ _ _ => rfl)
    have h_int_R : ∀ R : Finset (Fin n),
        Integrable (fun τ => retainProd (canonicalDemand w) s P ∅ τ (fun _ => s) R)
          (unifCubeMeasure n s) := by
      intro R
      have hm : Measurable (fun τ => retainProd (canonicalDemand w) s P ∅ τ (fun _ => s) R) := by
        unfold retainProd
        split_ifs
        · exact (Finset.measurable_prod R (fun g _ => h_ret_m g)).mul
            (Finset.measurable_prod (P \ R) (fun g _ => measurable_const.sub (h_ret_m g)))
        · exact measurable_const
      refine MeasureTheory.Integrable.of_mem_Icc 0 1 hm.aemeasurable
        (Filter.Eventually.of_forall (fun τ => ?_))
      unfold retainProd
      split_ifs
      · have h1_nn : 0 ≤ ∏ g ∈ R, retentionProb (canonicalDemand w) s P ∅ τ (fun _ => s) g :=
          Finset.prod_nonneg (fun g _ => (h_ret_b g τ).1)
        have h1_le : ∏ g ∈ R, retentionProb (canonicalDemand w) s P ∅ τ (fun _ => s) g ≤ 1 :=
          Finset.prod_le_one (fun g _ => (h_ret_b g τ).1) (fun g _ => (h_ret_b g τ).2)
        have h2_nn : 0 ≤ ∏ g ∈ P \ R, (1 - retentionProb (canonicalDemand w) s P ∅ τ (fun _ => s) g) :=
          Finset.prod_nonneg (fun g _ => sub_nonneg.mpr (h_ret_b g τ).2)
        have h2_le : ∏ g ∈ P \ R, (1 - retentionProb (canonicalDemand w) s P ∅ τ (fun _ => s) g) ≤ 1 :=
          Finset.prod_le_one (fun g _ => sub_nonneg.mpr (h_ret_b g τ).2)
            (fun g _ => sub_le_self 1 (h_ret_b g τ).1)
        exact ⟨mul_nonneg h1_nn h2_nn, mul_le_one₀ h1_le h2_nn h2_le⟩
      · exact ⟨le_rfl, zero_le_one⟩
    unfold survivalInclProb survivalLaw genSurvivalLaw genSurvivalLaw2
    rw [← MeasureTheory.integral_finset_sum _ (fun R _ => h_int_R R)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun τ => ?_))
    dsimp only
    let θ : Fin n → ℝ := fun g => retentionProb (canonicalDemand w) s P ∅ τ (fun _ => s) g
    have h_bij :
        (∑ R ∈ P.powerset.filter (fun R => B ⊆ R),
          retainProd (canonicalDemand w) s P ∅ τ (fun _ => s) R) =
        ∑ W ∈ (P \ B).powerset,
          (∏ g ∈ B, θ g) * ((∏ g ∈ W, θ g) * (∏ g ∈ (P \ B) \ W, (1 - θ g))) := by
      refine (Finset.sum_bij (fun W _ => B ∪ W) ?_ ?_ ?_ ?_).symm
      · intro W hW
        have hWP : W ⊆ P \ B := Finset.mem_powerset.mp hW
        simp only [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.union_subset hBP (hWP.trans Finset.sdiff_subset), Finset.subset_union_left⟩
      · intro W₁ hW₁ W₂ hW₂ heq
        dsimp only at heq
        have hWP₁ : W₁ ⊆ P \ B := Finset.mem_powerset.mp hW₁
        have hWP₂ : W₂ ⊆ P \ B := Finset.mem_powerset.mp hW₂
        ext z
        constructor
        · intro hz
          have hbu : z ∈ B ∪ W₂ := heq ▸ Finset.mem_union_right B hz
          rcases Finset.mem_union.mp hbu with hzB | hzW₂
          · exact ((Finset.mem_sdiff.mp (hWP₁ hz)).2 hzB).elim
          · exact hzW₂
        · intro hz
          have hbu : z ∈ B ∪ W₁ := heq.symm ▸ Finset.mem_union_right B hz
          rcases Finset.mem_union.mp hbu with hzB | hzW₁
          · exact ((Finset.mem_sdiff.mp (hWP₂ hz)).2 hzB).elim
          · exact hzW₁
      · intro R hR
        obtain ⟨hRP_pow, hBR⟩ := Finset.mem_filter.mp hR
        have hRP : R ⊆ P := Finset.mem_powerset.mp hRP_pow
        exact ⟨R \ B, Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff hRP Finset.Subset.rfl),
          Finset.union_sdiff_of_subset hBR⟩
      · intro W hW
        have hWP : W ⊆ P \ B := Finset.mem_powerset.mp hW
        have hBU_sub : B ∪ W ⊆ P := Finset.union_subset hBP (hWP.trans Finset.sdiff_subset)
        have hdisj : Disjoint B W := disjoint_sdiff_self_right.mono_right hWP
        have hsdiff : P \ (B ∪ W) = (P \ B) \ W := by
          ext z; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
        unfold retainProd
        rw [if_pos hBU_sub, Finset.prod_union hdisj, hsdiff, mul_assoc]
    rw [h_bij, ← Finset.mul_sum]
    have h_collapse :
        (∑ W ∈ (P \ B).powerset, (∏ g ∈ W, θ g) * (∏ g ∈ (P \ B) \ W, (1 - θ g))) = 1 := by
      rw [← Finset.prod_add]
      exact Finset.prod_eq_one (fun g _ => by ring)
    rw [h_collapse, mul_one]

  
  have hs₀_meas : Measurable s₀ := by
    suffices h_gen : ∀ S : Finset (Fin n),
        Measurable (fun τ : Fin n → ℝ =>
          (insert invE (S.image (fun q => min 1 (τ q)))).max' (Finset.insert_nonempty _ _)) by
      exact h_gen Q
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have h_eq : (fun τ : Fin n → ℝ =>
          (insert invE ((∅ : Finset (Fin n)).image (fun q => min 1 (τ q)))).max'
            (Finset.insert_nonempty _ _)) = fun _ => invE := by
        ext τ
        simp [Finset.max'_singleton]
      rw [h_eq]
      exact measurable_const
    | insert a S' haS' ih =>
      have h_eq : ∀ τ : Fin n → ℝ,
          (insert invE ((insert a S').image (fun q => min 1 (τ q)))).max'
            (Finset.insert_nonempty _ _) =
          max (min 1 (τ a))
            ((insert invE (S'.image (fun q => min 1 (τ q)))).max'
              (Finset.insert_nonempty _ _)) := by
        intro τ
        apply le_antisymm
        · refine Finset.max'_le _ _ _ (fun y hy => ?_)
          simp only [Finset.image_insert, Finset.mem_insert] at hy
          rcases hy with rfl | rfl | hyS'
          · exact le_max_of_le_right (Finset.le_max' _ _ (Finset.mem_insert_self _ _))
          · exact le_max_left _ _
          · exact le_max_of_le_right (Finset.le_max' _ _ (Finset.mem_insert_of_mem hyS'))
        · refine max_le ?_ ?_
          · refine Finset.le_max' _ _ ?_
            simp [Finset.image_insert]
          · refine Finset.max'_le _ _ _ (fun y hy => Finset.le_max' _ _ ?_)
            simp only [Finset.mem_insert] at hy
            simp only [Finset.image_insert, Finset.mem_insert]
            rcases hy with rfl | hyS'
            · exact Or.inl rfl
            · exact Or.inr (Or.inr hyS')
      simp_rw [h_eq]
      exact (measurable_const.min (measurable_pi_apply a)).max ih
  have hs₀_bdd : ∀ τ : Fin n → ℝ, invE ≤ s₀ τ ∧ s₀ τ ≤ 1 := by
    intro τ
    refine ⟨Finset.le_max' _ invE (Finset.mem_insert_self _ _), ?_⟩
    refine Finset.max'_le _ _ _ (fun y hy => ?_)
    rcases Finset.mem_insert.mp hy with rfl | hy_img
    · exact h_invE_le_one
    · obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hy_img
      exact min_le_left 1 (τ q)
  have hs₀_loc : ∀ τ₁ τ₂ : Fin n → ℝ, (∀ q ∈ Q, τ₁ q = τ₂ q) → s₀ τ₁ = s₀ τ₂ := by
    intro τ₁ τ₂ hq
    have himg : Q.image (fun q => min 1 (τ₁ q)) = Q.image (fun q => min 1 (τ₂ q)) :=
      Finset.image_congr (fun q hqQ => by rw [hq q hqQ])
    dsimp only [s₀]
    simp_rw [himg]
  obtain ⟨h_ret_s₀_m, h_ret_s₀_b, h_ret_s₀_loc⟩ :=
    h_s1_reg (canonicalDemand v) Q s₀ hs₀_meas hs₀_bdd hs₀_loc
  have hΨ_meas : Measurable Ψ :=
    Finset.measurable_prod A (fun g _ => h_ret_s₀_m g)
  have hΨ_bdd : ∀ τ : Fin n → ℝ, |Ψ τ| ≤ 1 := by
    intro τ
    have hnn : 0 ≤ Ψ τ := Finset.prod_nonneg (fun g _ => (h_ret_s₀_b g τ).1)
    have hle : Ψ τ ≤ 1 :=
      Finset.prod_le_one (fun g _ => (h_ret_s₀_b g τ).1) (fun g _ => (h_ret_s₀_b g τ).2)
    rw [abs_of_nonneg hnn]
    exact hle
  have hΨ_loc : ∀ τ₁ τ₂ : Fin n → ℝ, (∀ q ∈ Q, τ₁ q = τ₂ q) → Ψ τ₁ = Ψ τ₂ := by
    intro τ₁ τ₂ hq
    exact Finset.prod_congr rfl (fun g hgA => h_ret_s₀_loc g (hAQ hgA) τ₁ τ₂ hq)
  have h_conj1 : Measurable Ψ ∧ (∀ τ, |Ψ τ| ≤ 1) ∧
      (∀ τ₁ τ₂, (∀ q ∈ Q, τ₁ q = τ₂ q) → Ψ τ₁ = Ψ τ₂) :=
    ⟨hΨ_meas, hΨ_bdd, hΨ_loc⟩

  
  let θ_surr : (Fin n → ℝ) → ℝ → Fin n → ℝ := fun τ s g =>
    if g ∈ canonicalDemand v Q then
      (if τ g ≤ invE then Real.log (Real.exp 1 * s) else 0)
    else
      retentionProb (canonicalDemand v) (s₀ τ) Q ∅ τ (fun _ => s₀ τ) g
  have h_s2 : ∀ τ : Fin n → ℝ, (∀ q ∈ Q, τ q ≤ t) →
      ((∏ g ∈ A, retentionProb (canonicalDemand v) t Q ∅ τ (fun _ => t) g) =
        Ψ τ +
        ∑ x ∈ A ∩ canonicalDemand v Q,
          ∫ s in Set.Icc invE t,
            (if s₀ τ ≤ s ∧ τ x ≤ invE then
              s⁻¹ * ∏ g ∈ A.erase x, θ_surr τ s g
            else 0)) ∧
      (∀ x ∈ A ∩ canonicalDemand v Q, ∀ s ∈ Set.Icc invE t,
        (if s₀ τ ≤ s ∧ τ x ≤ invE then
          s⁻¹ * ∏ g ∈ A.erase x, θ_surr τ s g
        else 0) =
          s⁻¹ * ((if τ x ≤ invE then (1 : ℝ) else 0) *
            (∏ q ∈ Q.erase x, if τ q ≤ s then (1 : ℝ) else 0) *
            (∏ g ∈ A.erase x,
              retentionProb (canonicalDemand (contractVal v x)) s (Q.erase x) ∅ τ (fun _ => s) g))) := by
    intro τ hτQ
    have hs₀_lo : invE ≤ s₀ τ := (hs₀_bdd τ).1
    have hs₀_hi : s₀ τ ≤ t := by
      refine Finset.max'_le _ _ _ (fun y hy => ?_)
      rcases Finset.mem_insert.mp hy with rfl | hy_img
      · exact ht1
      · obtain ⟨q, hqQ, rfl⟩ := Finset.mem_image.mp hy_img
        exact min_le_of_right_le (hτQ q hqQ)
    have hτ_le_s₀ : ∀ q ∈ Q, τ q ≤ s₀ τ := by
      intro q hqQ
      have hq1 : τ q ≤ 1 := (hτQ q hqQ).trans ht2
      have hmem : min 1 (τ q) ∈ insert invE (Q.image (fun q => min 1 (τ q))) :=
        Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hqQ)
      have hle : min 1 (τ q) ≤ s₀ τ := Finset.le_max' _ _ hmem
      rwa [min_eq_right hq1] at hle
    have hs₀_le_iff : ∀ s : ℝ, invE ≤ s → (s₀ τ ≤ s ↔ ∀ q ∈ Q, τ q ≤ s) := by
      intro s hs_invE
      refine ⟨fun hs q hqQ => (hτ_le_s₀ q hqQ).trans hs, fun hq => ?_⟩
      refine Finset.max'_le _ _ _ (fun y hy => ?_)
      rcases Finset.mem_insert.mp hy with rfl | hy_img
      · exact hs_invE
      · obtain ⟨q, hqQ, rfl⟩ := Finset.mem_image.mp hy_img
        exact min_le_of_right_le (hq q hqQ)
    have hU_s₀ : Q.filter (fun q => τ q ≤ s₀ τ) = Q := Finset.filter_true_of_mem hτ_le_s₀
    have h_surr_eq : ∀ s : ℝ, s₀ τ ≤ s → s ≤ t → ∀ g ∈ A,
        retentionProb (canonicalDemand v) s Q ∅ τ (fun _ => s) g = θ_surr τ s g := by
      intro s hs_lo hs_hi g hgA
      dsimp only [θ_surr]
      by_cases hgD : g ∈ canonicalDemand v Q
      · rw [if_pos hgD]
        unfold retentionProb
        by_cases hτg : τ g ≤ invE
        · rw [if_pos hτg, if_pos hτg]
          have hemp : {u : ℝ | invE ≤ u ∧ u ≤ s ∧
              g ∉ canonicalDemand v (presentSet Q ∅ τ (fun _ => s) u)} = ∅ := by
            ext u
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
            intro hu1 _ hnot
            rw [h_pres_empty] at hnot
            have hg_flt : g ∈ Q.filter (fun q => τ q ≤ u) :=
              Finset.mem_filter.mpr ⟨hAQ hgA, hτg.trans hu1⟩
            exact hnot (h_persQ _ (Finset.filter_subset _ Q)
              (Finset.mem_inter.mpr ⟨hgD, hg_flt⟩))
          have hdt : deathTime (canonicalDemand v) s Q ∅ τ (fun _ => s) g = s := by
            unfold deathTime
            rw [hemp, Set.empty_union, csInf_singleton]
          rw [hdt]
        · rw [if_neg hτg, if_neg hτg]
      · rw [if_neg hgD]
        have hdt : deathTime (canonicalDemand v) s Q ∅ τ (fun _ => s) g =
            deathTime (canonicalDemand v) (s₀ τ) Q ∅ τ (fun _ => s₀ τ) g := by
          unfold deathTime
          simp_rw [h_pres_empty]
          let E₁ : Set ℝ :=
            {u : ℝ | invE ≤ u ∧ u ≤ s ∧ g ∉ canonicalDemand v (Q.filter (fun q => τ q ≤ u))} ∪ {s}
          let E₀ : Set ℝ :=
            {u : ℝ | invE ≤ u ∧ u ≤ s₀ τ ∧ g ∉ canonicalDemand v (Q.filter (fun q => τ q ≤ u))} ∪ {s₀ τ}
          have hs₀_E₁ : s₀ τ ∈ E₁ :=
            Set.mem_union_left _ ⟨hs₀_lo, hs_lo, by rwa [hU_s₀]⟩
          have hs₀_E₀ : s₀ τ ∈ E₀ := Set.mem_union_right _ rfl
          have hBdd₁ : BddBelow E₁ := ⟨invE, by
            rintro u (hu | hu)
            · exact hu.1
            · rw [Set.mem_singleton_iff.mp hu]; exact hs₀_lo.trans hs_lo⟩
          have hBdd₀ : BddBelow E₀ := ⟨invE, by
            rintro u (hu | hu)
            · exact hu.1
            · rw [Set.mem_singleton_iff.mp hu]; exact hs₀_lo⟩
          change sInf E₁ = sInf E₀
          apply le_antisymm
          · refine csInf_le_csInf hBdd₁ ⟨s₀ τ, hs₀_E₀⟩ (fun u hu => ?_)
            rcases hu with ⟨h1, h2, h3⟩ | hu_eq
            · exact Set.mem_union_left _ ⟨h1, h2.trans hs_lo, h3⟩
            · rw [Set.mem_singleton_iff.mp hu_eq]; exact hs₀_E₁
          · refine le_csInf ⟨s, Set.mem_union_right _ rfl⟩ (fun u hu => ?_)
            by_cases h_le : s₀ τ ≤ u
            · exact (csInf_le hBdd₀ hs₀_E₀).trans h_le
            · have hu_lt : u < s₀ τ := lt_of_not_ge h_le
              rcases hu with ⟨h1, _, h3⟩ | hu_eq
              · exact csInf_le hBdd₀ (Set.mem_union_left _ ⟨h1, hu_lt.le, h3⟩)
              · exfalso
                rw [Set.mem_singleton_iff.mp hu_eq] at hu_lt
                exact not_lt_of_ge hs_lo hu_lt
        unfold retentionProb
        rw [hdt]
    refine ⟨?_, ?_⟩
    · let Φ : ℝ → ℝ := fun s => ∏ g ∈ A, θ_surr τ s g
      let dθ : ℝ → Fin n → ℝ := fun s g =>
        if g ∈ canonicalDemand v Q then (if τ g ≤ invE then s⁻¹ else 0) else 0
      let f_x : Fin n → ℝ → ℝ := fun x s =>
        if τ x ≤ invE then s⁻¹ * ∏ g ∈ A.erase x, θ_surr τ s g else 0
      have hdθ : ∀ {s : ℝ}, 0 < s → ∀ g : Fin n,
          HasDerivAt (fun u => θ_surr τ u g) (dθ s g) s := by
        intro s hs_pos g
        dsimp only [θ_surr, dθ]
        by_cases hgD : g ∈ canonicalDemand v Q
        · rw [if_pos hgD]
          simp_rw [if_pos hgD]
          by_cases hτg : τ g ≤ invE
          · rw [if_pos hτg]
            simp_rw [if_pos hτg]
            have hexp_ne : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
            have hs_ne : s ≠ 0 := hs_pos.ne'
            have hmul_ne : Real.exp 1 * s ≠ 0 := mul_ne_zero hexp_ne hs_ne
            have h1 : HasDerivAt (fun u : ℝ => Real.exp 1 * u) (Real.exp 1 * 1) s :=
              (hasDerivAt_id s).const_mul (Real.exp 1)
            have h2 : HasDerivAt (fun u : ℝ => Real.log (Real.exp 1 * u))
                ((Real.exp 1 * s)⁻¹ * (Real.exp 1 * 1)) s :=
              (Real.hasDerivAt_log hmul_ne).comp s h1
            have h_val : (Real.exp 1 * s)⁻¹ * (Real.exp 1 * 1) = s⁻¹ := by field_simp
            rwa [h_val] at h2
          · rw [if_neg hτg]
            simp_rw [if_neg hτg]
            exact hasDerivAt_const s (0 : ℝ)
        · rw [if_neg hgD]
          simp_rw [if_neg hgD]
          exact hasDerivAt_const s
            (retentionProb (canonicalDemand v) (s₀ τ) Q ∅ τ (fun _ => s₀ τ) g)
      have hΦ_deriv : ∀ {s : ℝ}, 0 < s →
          HasDerivAt Φ (∑ x ∈ A ∩ canonicalDemand v Q, f_x x s) s := by
        intro s hs_pos
        have hprod : HasDerivAt Φ (∑ x ∈ A, (∏ g ∈ A.erase x, θ_surr τ s g) • dθ s x) s :=
          HasDerivAt.fun_finset_prod (fun g _ => hdθ hs_pos g)
        have hsum_eq : (∑ x ∈ A, (∏ g ∈ A.erase x, θ_surr τ s g) • dθ s x) =
            ∑ x ∈ A ∩ canonicalDemand v Q, f_x x s := by
          let term : Fin n → ℝ := fun x => (∏ g ∈ A.erase x, θ_surr τ s g) • dθ s x
          have hpart : A \ canonicalDemand v Q ∪ (A ∩ canonicalDemand v Q) = A :=
            Finset.sdiff_union_inter A (canonicalDemand v Q)
          have hdisj : Disjoint (A \ canonicalDemand v Q) (A ∩ canonicalDemand v Q) :=
            Finset.disjoint_sdiff_inter A (canonicalDemand v Q)
          have hsplit : (∑ x ∈ A, term x) =
              (∑ x ∈ A \ canonicalDemand v Q, term x) +
              (∑ x ∈ A ∩ canonicalDemand v Q, term x) := by
            rw [← Finset.sum_union hdisj, hpart]
          change (∑ x ∈ A, term x) = _
          rw [hsplit]
          have h_zero : (∑ x ∈ A \ canonicalDemand v Q, term x) = 0 := by
            refine Finset.sum_eq_zero (fun x hx => ?_)
            have hxD : x ∉ canonicalDemand v Q := (Finset.mem_sdiff.mp hx).2
            dsimp only [term, dθ]
            rw [if_neg hxD, smul_zero]
          rw [h_zero, zero_add]
          refine Finset.sum_congr rfl (fun x hx => ?_)
          have hxD : x ∈ canonicalDemand v Q := (Finset.mem_inter.mp hx).2
          dsimp only [term, dθ, f_x]
          rw [if_pos hxD, smul_eq_mul]
          split_ifs <;> ring
        rwa [hsum_eq] at hprod
      have h_pos_on : ∀ {s : ℝ}, s ∈ Set.Icc (s₀ τ) t → 0 < s :=
        fun hs => h_invE_pos.trans_le (hs₀_lo.trans hs.1)
      have hΦ_cont : ContinuousOn Φ (Set.Icc (s₀ τ) t) :=
        fun s hs => (hΦ_deriv (h_pos_on hs)).continuousAt.continuousWithinAt
      have hf_cont : ∀ x : Fin n, ContinuousOn (f_x x) (Set.Icc (s₀ τ) t) := by
        intro x
        dsimp only [f_x]
        split_ifs with hτx
        · have h_inv_c : ContinuousOn (fun s : ℝ => s⁻¹) (Set.Icc (s₀ τ) t) :=
            continuousOn_inv₀.mono (fun s hs => (h_pos_on hs).ne')
          have h_prd_c : ContinuousOn (fun s : ℝ => ∏ g ∈ A.erase x, θ_surr τ s g)
              (Set.Icc (s₀ τ) t) :=
            continuousOn_finset_prod _ (fun g _ s hs =>
              (hdθ (h_pos_on hs) g).continuousAt.continuousWithinAt)
          exact h_inv_c.mul h_prd_c
        · exact continuousOn_const
      have hΦ'_cont : ContinuousOn (fun s => ∑ x ∈ A ∩ canonicalDemand v Q, f_x x s)
          (Set.Icc (s₀ τ) t) :=
        continuousOn_finset_sum _ (fun x _ => hf_cont x)
      have h_ftc : ∫ s in (s₀ τ)..t, (∑ x ∈ A ∩ canonicalDemand v Q, f_x x s) = Φ t - Φ (s₀ τ) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs₀_hi hΦ_cont
          (fun s hs => hΦ_deriv (h_pos_on ⟨hs.1.le, hs.2.le⟩))
          (hΦ'_cont.intervalIntegrable_of_Icc hs₀_hi)
      rw [intervalIntegral.integral_of_le hs₀_hi, ← MeasureTheory.integral_Icc_eq_integral_Ioc,
        MeasureTheory.integral_finset_sum _ (fun x _ => (hf_cont x).integrableOn_Icc)] at h_ftc
      have h_ind_sum :
          (∑ x ∈ A ∩ canonicalDemand v Q, ∫ s in Set.Icc (s₀ τ) t, f_x x s) =
          ∑ x ∈ A ∩ canonicalDemand v Q,
            ∫ s in Set.Icc invE t,
              (if s₀ τ ≤ s ∧ τ x ≤ invE then s⁻¹ * ∏ g ∈ A.erase x, θ_surr τ s g else 0) := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        have h_inter : Set.Icc invE t ∩ Set.Ici (s₀ τ) = Set.Icc (s₀ τ) t := by
          ext s
          simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]
          exact ⟨fun ⟨⟨_, h2⟩, h3⟩ => ⟨h3, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨hs₀_lo.trans h1, h2⟩, h1⟩⟩
        have h_ind_fn : (Set.Ici (s₀ τ)).indicator (f_x x) =
            fun s => if s₀ τ ≤ s ∧ τ x ≤ invE then s⁻¹ * ∏ g ∈ A.erase x, θ_surr τ s g else 0 := by
          ext s
          by_cases hs : s₀ τ ≤ s <;> by_cases hx : τ x ≤ invE <;>
            simp [Set.indicator, f_x, hs, hx]
        rw [← h_inter, ← MeasureTheory.setIntegral_indicator measurableSet_Ici, h_ind_fn]
      rw [h_ind_sum] at h_ftc
      have hΦ_t : Φ t = ∏ g ∈ A, retentionProb (canonicalDemand v) t Q ∅ τ (fun _ => t) g :=
        Finset.prod_congr rfl (fun g hgA => (h_surr_eq t hs₀_hi le_rfl g hgA).symm)
      have hΦ_s₀ : Φ (s₀ τ) = Ψ τ :=
        Finset.prod_congr rfl (fun g hgA => (h_surr_eq (s₀ τ) le_rfl hs₀_hi g hgA).symm)
      rw [hΦ_t, hΦ_s₀] at h_ftc
      linarith
    · intro x hxAD s hs_mem
      obtain ⟨hs1, hs2⟩ := hs_mem
      obtain ⟨hxA, _⟩ := Finset.mem_inter.mp hxAD
      have hxQ : x ∈ Q := hAQ hxA
      by_cases h_cond : s₀ τ ≤ s ∧ τ x ≤ invE
      · obtain ⟨hs₀_s, hτx⟩ := h_cond
        have hq_le : ∀ q ∈ Q.erase x, τ q ≤ s :=
          fun q hq => (hs₀_le_iff s hs1).mp hs₀_s q (Finset.erase_subset x Q hq)
        have h_prod_one : (∏ q ∈ Q.erase x, if τ q ≤ s then (1 : ℝ) else 0) = 1 :=
          Finset.prod_eq_one (fun q hq => if_pos (hq_le q hq))
        rw [if_pos ⟨hs₀_s, hτx⟩, if_pos hτx, h_prod_one, one_mul, one_mul]
        congr 1
        refine Finset.prod_congr rfl (fun g hg_er => ?_)
        obtain ⟨hg_ne, hgA⟩ := Finset.mem_erase.mp hg_er
        rw [← h_surr_eq s hs₀_s hs2 g hgA]
        unfold retentionProb
        split_ifs with hτg
        · have hdt_eq : deathTime (canonicalDemand v) s Q ∅ τ (fun _ => s) g =
              deathTime (canonicalDemand (contractVal v x)) s (Q.erase x) ∅ τ (fun _ => s) g := by
            unfold deathTime
            congr 1
            ext u
            by_cases hus : u = s
            · subst hus; simp
            · simp only [Set.mem_union, Set.mem_singleton_iff, hus, or_false, Set.mem_setOf_eq]
              have h_iff : ∀ hu1 : invE ≤ u,
                  (g ∈ canonicalDemand (contractVal v x)
                      (presentSet (Q.erase x) ∅ τ (fun _ => s) u) ↔
                    g ∈ canonicalDemand v (presentSet Q ∅ τ (fun _ => s) u)) := by
                intro hu1
                let T_u' := presentSet (Q.erase x) ∅ τ (fun _ => s) u
                have hT_sub : T_u' ⊆ Q.erase x := by
                  dsimp only [T_u']; rw [h_pres_empty]; exact Finset.filter_subset _ _
                have hpres_ins : presentSet Q ∅ τ (fun _ => s) u = insert x T_u' := by
                  dsimp only [T_u']
                  rw [h_pres_empty, h_pres_empty]
                  ext z
                  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
                  by_cases hzx : z = x
                  · subst hzx
                    exact ⟨fun _ => Or.inl rfl, fun _ => ⟨hxQ, hτx.trans hu1⟩⟩
                  · simp [hzx]
                rw [h_commQ x hxAD T_u' hT_sub, hpres_ins, Finset.mem_erase]
                exact and_iff_right hg_ne
              exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, mt (h_iff h1).mp h3⟩,
                fun ⟨h1, h2, h3⟩ => ⟨h1, h2, mt (h_iff h1).mpr h3⟩⟩
          rw [hdt_eq]
        · rfl
      · rw [if_neg h_cond]
        by_cases hτx : τ x ≤ invE
        · have hnot_s₀ : ¬(s₀ τ ≤ s) := fun hs₀ => h_cond ⟨hs₀, hτx⟩
          have hnot_all : ¬(∀ q ∈ Q, τ q ≤ s) := mt (hs₀_le_iff s hs1).mpr hnot_s₀
          push_neg at hnot_all
          obtain ⟨q, hqQ, hsq⟩ := hnot_all
          have hqx : q ≠ x := fun h => (not_lt_of_ge (hτx.trans hs1)) (h ▸ hsq)
          have hq_er : q ∈ Q.erase x := Finset.mem_erase.mpr ⟨hqx, hqQ⟩
          have h_prod_zero : (∏ q' ∈ Q.erase x, if τ q' ≤ s then (1 : ℝ) else 0) = 0 :=
            Finset.prod_eq_zero hq_er (if_neg (not_le_of_gt hsq))
          rw [h_prod_zero]
          ring
        · rw [if_neg hτx]
          ring

  
  have h_1d : ∀ {a b : ℝ}, 0 < a → a ≤ b → ∀ h : ℝ → ℝ,
      (∫ u, (if u ≤ a then h u else 0) ∂(ν b)) = (a / b) * ∫ u, h u ∂(ν a) := by
    intro a b ha hb h
    have hb_pos : 0 < b := ha.trans_le hb
    have h_ind : (fun u => if u ≤ a then h u else 0) = (Set.Iic a).indicator h := by
      ext u; by_cases hu : u ≤ a <;> simp [hu]
    have h_inter : Set.Iic a ∩ Set.Icc (0 : ℝ) b = Set.Icc (0 : ℝ) a := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      exact ⟨fun ⟨h1, h2, _⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, h2.trans hb⟩⟩
    dsimp only [ν]
    rw [h_ind, MeasureTheory.integral_smul_measure,
      MeasureTheory.integral_indicator measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Iic, h_inter,
      MeasureTheory.integral_smul_measure, smul_eq_mul, smul_eq_mul,
      ENNReal.toReal_inv, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal hb_pos.le, ENNReal.toReal_ofReal ha.le]
    have ha_ne : a ≠ 0 := ha.ne'
    have hb_ne : b ≠ 0 := hb_pos.ne'
    field_simp
  have h_coord_swap : ∀ (b : Fin n → ℝ), (∀ i, 0 < b i) →
      ∀ (i₀ : Fin n) (a : ℝ), 0 < a → a ≤ b i₀ →
      ∀ (G : (Fin n → ℝ) → ℝ), Measurable G → (∀ τ, |G τ| ≤ 1) →
        (∫ τ, (if τ i₀ ≤ a then (1 : ℝ) else 0) * G τ ∂(Measure.pi (fun i => ν (b i)))) =
          (a / b i₀) * ∫ τ, G τ ∂(Measure.pi (fun i => ν (Function.update b i₀ a i))) := by
    intro b hb i₀ a ha hab G hG_meas hG_bdd
    obtain ⟨pred, hpred⟩ : ∃ pred : Fin n → Prop, ∀ i, pred i ↔ i = i₀ :=
      ⟨fun i => i = i₀, fun _ => Iff.rfl⟩
    let i₀_sub : {i : Fin n // pred i} := ⟨i₀, (hpred i₀).mpr rfl⟩
    let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) pred
    haveI : IsProbabilityMeasure (ν (b i₀)) := h_ν_prob (hb i₀)
    haveI : IsProbabilityMeasure (ν a) := h_ν_prob ha
    haveI : ∀ i : Fin n, IsProbabilityMeasure (ν (b i)) := fun i => h_ν_prob (hb i)
    have hb_upd_pos : ∀ i : Fin n, 0 < Function.update b i₀ a i := by
      intro i
      by_cases hi : i = i₀
      · subst hi; rw [Function.update_self]; exact ha
      · rw [Function.update_of_ne hi]; exact hb i
    haveI : ∀ i : Fin n, IsProbabilityMeasure (ν (Function.update b i₀ a i)) :=
      fun i => h_ν_prob (hb_upd_pos i)
    let m_out : {i : Fin n // ¬ pred i} → Measure ℝ := fun i => ν (b i.1)
    haveI : ∀ i : {i : Fin n // ¬ pred i}, IsProbabilityMeasure (m_out i) :=
      fun i => h_ν_prob (hb i.1)
    haveI : IsProbabilityMeasure (Measure.pi m_out) := inferInstance
    have hm₁_eq : (fun i : {i : Fin n // pred i} => ν (b i.1)) = fun _ => ν (b i₀) := by
      funext i; dsimp only; rw [(hpred i.1).mp i.2]
    have hm₂_eq : (fun i : {i : Fin n // pred i} => ν (Function.update b i₀ a i.1)) =
        fun _ => ν a := by
      funext i; dsimp only; rw [(hpred i.1).mp i.2, Function.update_self]
    have hm_out_eq : (fun i : {i : Fin n // ¬ pred i} => ν (Function.update b i₀ a i.1)) =
        m_out := by
      funext i
      have hne : i.1 ≠ i₀ := mt (hpred i.1).mpr i.2
      dsimp only [m_out]
      rw [Function.update_of_ne hne]
    have h_mp₁ : MeasurePreserving e.symm
        ((Measure.pi (fun _ : {i // pred i} => ν (b i₀))).prod (Measure.pi m_out))
        (Measure.pi (fun i => ν (b i))) := by
      have h := (measurePreserving_piEquivPiSubtypeProd (fun i : Fin n => ν (b i)) pred).symm e
      simpa only [m_out, hm₁_eq] using h
    have h_mp₂ : MeasurePreserving e.symm
        ((Measure.pi (fun _ : {i // pred i} => ν a)).prod (Measure.pi m_out))
        (Measure.pi (fun i => ν (Function.update b i₀ a i))) := by
      have h := (measurePreserving_piEquivPiSubtypeProd
        (fun i : Fin n => ν (Function.update b i₀ a i)) pred).symm e
      simpa only [hm₂_eq, hm_out_eq] using h
    have h_symm_eq : ∀ (x_in : {i // pred i} → ℝ) (z : {i // ¬ pred i} → ℝ),
        e.symm (x_in, z) = Function.update (e.symm (0, z)) i₀ (x_in i₀_sub) := by
      intro x_in z; ext j
      by_cases hj : j = i₀
      · rw [hj]
        have h1 : e.symm (x_in, z) i₀ = x_in i₀_sub :=
          (Equiv.piEquivPiSubtypeProd_symm_apply pred (fun _ : Fin n => ℝ) (x_in, z) i₀).trans
            (dif_pos ((hpred i₀).mpr rfl))
        rw [h1, Function.update_self]
      · have hnp : ¬ pred j := mt (hpred j).mp hj
        have h1 : e.symm (x_in, z) j = z ⟨j, hnp⟩ :=
          (Equiv.piEquivPiSubtypeProd_symm_apply pred (fun _ : Fin n => ℝ) (x_in, z) j).trans
            (dif_neg hnp)
        have h2 : e.symm (0, z) j = z ⟨j, hnp⟩ :=
          (Equiv.piEquivPiSubtypeProd_symm_apply pred (fun _ : Fin n => ℝ) (0, z) j).trans
            (dif_neg hnp)
        rw [h1, Function.update_of_ne hj, h2]
    let F₁ : (({i // pred i} → ℝ) × ({i // ¬ pred i} → ℝ)) → ℝ :=
      fun q => (if (e.symm q) i₀ ≤ a then (1 : ℝ) else 0) * G (e.symm q)
    let F₂ : (({i // pred i} → ℝ) × ({i // ¬ pred i} → ℝ)) → ℝ :=
      fun q => G (e.symm q)
    have hF₁_meas : Measurable F₁ :=
      (Measurable.ite
        (measurableSet_le ((measurable_pi_apply i₀).comp e.symm.measurable) measurable_const)
        measurable_const measurable_const).mul (hG_meas.comp e.symm.measurable)
    have hF₂_meas : Measurable F₂ := hG_meas.comp e.symm.measurable
    have hF₁_int : Integrable F₁
        ((Measure.pi (fun _ : {i // pred i} => ν (b i₀))).prod (Measure.pi m_out)) := by
      refine Integrable.of_mem_Icc (-1) 1 hF₁_meas.aemeasurable
        (Filter.Eventually.of_forall (fun q => abs_le.mp ?_))
      dsimp only [F₁]; split_ifs <;> simp [hG_bdd (e.symm q)]
    have hF₂_int : Integrable F₂
        ((Measure.pi (fun _ : {i // pred i} => ν a)).prod (Measure.pi m_out)) :=
      Integrable.of_mem_Icc (-1) 1 hF₂_meas.aemeasurable
        (Filter.Eventually.of_forall (fun q => abs_le.mp (hG_bdd (e.symm q))))
    rw [← h_mp₁.integral_comp' (fun τ => (if τ i₀ ≤ a then (1 : ℝ) else 0) * G τ),
      ← h_mp₂.integral_comp' G]
    change (∫ q, F₁ q ∂_) = (a / b i₀) * ∫ q, F₂ q ∂_
    rw [MeasureTheory.integral_prod_symm F₁ hF₁_int,
      MeasureTheory.integral_prod_symm F₂ hF₂_int, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    let gz : ℝ → ℝ := fun u => G (Function.update (e.symm (0, z)) i₀ u)
    have hgz_meas : Measurable gz := by
      refine hG_meas.comp (measurable_pi_iff.mpr (fun j => ?_))
      by_cases hj : j = i₀
      · rw [hj]; simp only [Function.update_self]; exact measurable_id
      · simp only [Function.update_of_ne hj]; exact measurable_const
    have hgz_ite_meas : Measurable (fun u => if u ≤ a then gz u else 0) :=
      Measurable.ite measurableSet_Iic hgz_meas measurable_const
    have h_mp_eval_b := measurePreserving_eval (fun _ : {i // pred i} => ν (b i₀)) i₀_sub
    have h_mp_eval_a := measurePreserving_eval (fun _ : {i // pred i} => ν a) i₀_sub
    have h_eval_b :
        (∫ x_in, (if x_in i₀_sub ≤ a then gz (x_in i₀_sub) else 0)
          ∂(Measure.pi (fun _ : {i // pred i} => ν (b i₀)))) =
        ∫ u, (if u ≤ a then gz u else 0) ∂(ν (b i₀)) := by
      conv_rhs => rw [← h_mp_eval_b.map_eq]
      exact (MeasureTheory.integral_map h_mp_eval_b.measurable.aemeasurable
        hgz_ite_meas.aestronglyMeasurable).symm
    have h_eval_a :
        (∫ x_in, gz (x_in i₀_sub) ∂(Measure.pi (fun _ : {i // pred i} => ν a))) =
        ∫ u, gz u ∂(ν a) := by
      conv_rhs => rw [← h_mp_eval_a.map_eq]
      exact (MeasureTheory.integral_map h_mp_eval_a.measurable.aemeasurable
        hgz_meas.aestronglyMeasurable).symm
    have h_lhs_eq : (fun x_in : {i // pred i} → ℝ => F₁ (x_in, z)) =
        (fun x_in => if x_in i₀_sub ≤ a then gz (x_in i₀_sub) else 0) := by
      ext x_in; dsimp only [F₁, gz]; rw [h_symm_eq x_in z, Function.update_self]; split_ifs <;> ring
    have h_rhs_eq : (fun x_in : {i // pred i} → ℝ => F₂ (x_in, z)) =
        (fun x_in => gz (x_in i₀_sub)) := by
      ext x_in; dsimp only [F₂, gz]; rw [h_symm_eq x_in z]
    dsimp only
    rw [h_lhs_eq, h_rhs_eq, h_eval_b, h_eval_a, h_1d ha hab gz]
  have h_s3 : ∀ (P : Finset (Fin n)) (x : Fin n) (s : ℝ) (H : (Fin n → ℝ) → ℝ),
      x ∉ P → 0 < s → s ≤ t → Measurable H → (∀ τ, |H τ| ≤ 1) →
      (∀ τ₁ τ₂, (∀ q ∈ P, τ₁ q = τ₂ q) → H τ₁ = H τ₂) →
        ∫ τ, (if τ x ≤ invE then (1 : ℝ) else 0) *
            (∏ q ∈ P, if τ q ≤ s then (1 : ℝ) else 0) * H τ ∂(unifCubeMeasure n t) =
          (invE / t) * (s / t) ^ P.card * ∫ τ, H τ ∂(unifCubeMeasure n s) := by
    intro P x s H hxP hs_pos hs_le_t hH_meas hH_bdd hH_loc
    have h_iter : ∀ (S : Finset (Fin n)) (b : Fin n → ℝ),
        (∀ i, 0 < b i) → (∀ q ∈ S, b q = t) →
          (∫ τ, (∏ q ∈ S, if τ q ≤ s then (1 : ℝ) else 0) * H τ ∂(Measure.pi (fun i => ν (b i)))) =
            (s / t) ^ S.card *
              ∫ τ, H τ ∂(Measure.pi (fun i => ν (if i ∈ S then s else b i))) := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
        intro b _ _
        simp
      | insert q S' hqS' ih =>
        intro b hb hbS
        have hbq : b q = t := hbS q (Finset.mem_insert_self q S')
        let G : (Fin n → ℝ) → ℝ :=
          fun τ => (∏ z ∈ S', if τ z ≤ s then (1 : ℝ) else 0) * H τ
        have hG_meas : Measurable G :=
          (Finset.measurable_prod S' (fun z _ =>
            Measurable.ite (measurableSet_le (measurable_pi_apply z) measurable_const)
              measurable_const measurable_const)).mul hH_meas
        have hG_bdd : ∀ τ, |G τ| ≤ 1 := by
          intro τ; dsimp only [G]
          have hp0 : 0 ≤ ∏ z ∈ S', if τ z ≤ s then (1 : ℝ) else 0 :=
            Finset.prod_nonneg (fun _ _ => by split_ifs <;> norm_num)
          have hp1 : (∏ z ∈ S', if τ z ≤ s then (1 : ℝ) else 0) ≤ 1 :=
            Finset.prod_le_one (fun _ _ => by split_ifs <;> norm_num)
              (fun _ _ => by split_ifs <;> norm_num)
          rw [abs_mul, abs_of_nonneg hp0]
          exact mul_le_one₀ hp1 (abs_nonneg _) (hH_bdd τ)
        have h_rew : (fun τ => (∏ z ∈ insert q S', if τ z ≤ s then (1 : ℝ) else 0) * H τ) =
            fun τ => (if τ q ≤ s then (1 : ℝ) else 0) * G τ := by
          ext τ; dsimp only [G]; rw [Finset.prod_insert hqS', mul_assoc]
        have hb' : ∀ i, 0 < Function.update b q s i := by
          intro i
          by_cases hiq : i = q
          · subst hiq; rw [Function.update_self]; exact hs_pos
          · rw [Function.update_of_ne hiq]; exact hb i
        have hb'S' : ∀ z ∈ S', Function.update b q s z = t := by
          intro z hzS'
          have hzq : z ≠ q := fun h => hqS' (h ▸ hzS')
          rw [Function.update_of_ne hzq]
          exact hbS z (Finset.mem_insert_of_mem hzS')
        have h_upd_eq : (fun i => ν (if i ∈ S' then s else Function.update b q s i)) =
            fun i => ν (if i ∈ insert q S' then s else b i) := by
          funext i; congr 1
          by_cases hiS' : i ∈ S'
          · simp [hiS']
          · by_cases hiq : i = q
            · subst hiq; simp [hiS']
            · simp [hiS', hiq]
        rw [h_rew, h_coord_swap b hb q s hs_pos (hbq ▸ hs_le_t) G hG_meas hG_bdd, hbq,
          ih (Function.update b q s) hb' hb'S', h_upd_eq,
          Finset.card_insert_of_notMem hqS', pow_succ']
        ring
    let G₀ : (Fin n → ℝ) → ℝ := fun τ => (∏ q ∈ P, if τ q ≤ s then (1 : ℝ) else 0) * H τ
    have hG₀_meas : Measurable G₀ :=
      (Finset.measurable_prod P (fun q _ =>
        Measurable.ite (measurableSet_le (measurable_pi_apply q) measurable_const)
          measurable_const measurable_const)).mul hH_meas
    have hG₀_bdd : ∀ τ, |G₀ τ| ≤ 1 := by
      intro τ; dsimp only [G₀]
      have hp0 : 0 ≤ ∏ q ∈ P, if τ q ≤ s then (1 : ℝ) else 0 :=
        Finset.prod_nonneg (fun _ _ => by split_ifs <;> norm_num)
      have hp1 : (∏ q ∈ P, if τ q ≤ s then (1 : ℝ) else 0) ≤ 1 :=
        Finset.prod_le_one (fun _ _ => by split_ifs <;> norm_num)
          (fun _ _ => by split_ifs <;> norm_num)
      rw [abs_mul, abs_of_nonneg hp0]
      exact mul_le_one₀ hp1 (abs_nonneg _) (hH_bdd τ)
    have h_assoc : (fun τ => (if τ x ≤ invE then (1 : ℝ) else 0) *
        (∏ q ∈ P, if τ q ≤ s then (1 : ℝ) else 0) * H τ) =
        fun τ => (if τ x ≤ invE then (1 : ℝ) else 0) * G₀ τ := by
      ext τ; dsimp only [G₀]; ring
    let b₁ : Fin n → ℝ := Function.update (fun _ : Fin n => t) x invE
    have hb₁_pos : ∀ i, 0 < b₁ i := by
      intro i; dsimp only [b₁]
      by_cases hix : i = x
      · subst hix; rw [Function.update_self]; exact h_invE_pos
      · rw [Function.update_of_ne hix]; exact ht_pos
    have hb₁_P : ∀ q ∈ P, b₁ q = t := by
      intro q hqP
      have hqx : q ≠ x := fun h => hxP (h ▸ hqP)
      dsimp only [b₁]; rw [Function.update_of_ne hqx]
    have h_step_x :
        (∫ τ, (if τ x ≤ invE then (1 : ℝ) else 0) * G₀ τ ∂(unifCubeMeasure n t)) =
          (invE / t) * ∫ τ, G₀ τ ∂(Measure.pi (fun i => ν (b₁ i))) :=
      h_coord_swap (fun _ => t) (fun _ => ht_pos) x invE h_invE_pos ht1 G₀ hG₀_meas hG₀_bdd
    let c : Fin n → ℝ := fun i => if i ∈ P then s else b₁ i
    have hc_pos : ∀ i, 0 < c i := by
      intro i; dsimp only [c]; split_ifs
      · exact hs_pos
      · exact hb₁_pos i
    have h_marg : (∫ τ, H τ ∂(Measure.pi (fun i => ν (c i)))) =
        ∫ τ, H τ ∂(unifCubeMeasure n s) := by
      obtain ⟨pred, hpred⟩ : ∃ pred : Fin n → Prop, ∀ i, pred i ↔ i ∈ P :=
        ⟨fun i => i ∈ P, fun _ => Iff.rfl⟩
      let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) pred
      haveI : IsProbabilityMeasure (ν s) := h_ν_prob hs_pos
      haveI : ∀ i : Fin n, IsProbabilityMeasure (ν (c i)) := fun i => h_ν_prob (hc_pos i)
      let m_in : {i : Fin n // pred i} → Measure ℝ := fun _ => ν s
      let m_out₁ : {i : Fin n // ¬ pred i} → Measure ℝ := fun i => ν (c i.1)
      let m_out₂ : {i : Fin n // ¬ pred i} → Measure ℝ := fun _ => ν s
      haveI : IsProbabilityMeasure (Measure.pi m_in) := by dsimp only [m_in]; infer_instance
      haveI : ∀ i : {i : Fin n // ¬ pred i}, IsProbabilityMeasure (m_out₁ i) :=
        fun i => h_ν_prob (hc_pos i.1)
      haveI : IsProbabilityMeasure (Measure.pi m_out₁) := inferInstance
      haveI : IsProbabilityMeasure (Measure.pi m_out₂) := by dsimp only [m_out₂]; infer_instance
      have hm_in_eq : (fun i : {i : Fin n // pred i} => ν (c i.1)) = m_in := by
        funext i
        dsimp only [c, m_in]
        rw [if_pos ((hpred i.1).mp i.2)]
      have h_mp₁ : MeasurePreserving e.symm
          ((Measure.pi m_in).prod (Measure.pi m_out₁)) (Measure.pi (fun i => ν (c i))) := by
        have h := (measurePreserving_piEquivPiSubtypeProd (fun i : Fin n => ν (c i)) pred).symm e
        simpa only [m_out₁, hm_in_eq] using h
      have h_mp₂ : MeasurePreserving e.symm
          ((Measure.pi m_in).prod (Measure.pi m_out₂)) (unifCubeMeasure n s) := by
        unfold unifCubeMeasure
        exact (measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => ν s) pred).symm e
      have h_loc_eq : ∀ q : ({i // pred i} → ℝ) × ({i // ¬ pred i} → ℝ),
          H (e.symm q) = H (e.symm (q.1, 0)) := by
        intro ⟨y, z⟩
        refine hH_loc _ _ (fun i hiP => ?_)
        have hp : pred i := (hpred i).mpr hiP
        have h1 : e.symm (y, z) i = y ⟨i, hp⟩ :=
          (Equiv.piEquivPiSubtypeProd_symm_apply pred (fun _ : Fin n => ℝ) (y, z) i).trans
            (dif_pos hp)
        have h2 : e.symm (y, 0) i = y ⟨i, hp⟩ :=
          (Equiv.piEquivPiSubtypeProd_symm_apply pred (fun _ : Fin n => ℝ) (y, 0) i).trans
            (dif_pos hp)
        rw [h1, h2]
      let F₀ : ({i // pred i} → ℝ) × ({i // ¬ pred i} → ℝ) → ℝ := fun q => H (e.symm (q.1, 0))
      have hF₀_meas : Measurable F₀ :=
        hH_meas.comp (e.symm.measurable.comp (measurable_fst.prodMk measurable_const))
      have h_eval : ∀ (μ_out : Measure ({i // ¬ pred i} → ℝ)) [IsProbabilityMeasure μ_out],
          (∫ q, H (e.symm q) ∂((Measure.pi m_in).prod μ_out)) =
            ∫ y, H (e.symm (y, 0)) ∂(Measure.pi m_in) := by
        intro μ_out _
        have h_fn : (fun q => H (e.symm q)) = F₀ := funext h_loc_eq
        have hF₀_int : Integrable F₀ ((Measure.pi m_in).prod μ_out) :=
          Integrable.of_mem_Icc (-1) 1 hF₀_meas.aemeasurable
            (Filter.Eventually.of_forall (fun q => abs_le.mp (hH_bdd _)))
        rw [h_fn, MeasureTheory.integral_prod F₀ hF₀_int]
        simp [F₀, MeasureTheory.integral_const]
      rw [← h_mp₁.integral_comp' H, ← h_mp₂.integral_comp' H,
        h_eval (Measure.pi m_out₁), h_eval (Measure.pi m_out₂)]
    rw [h_assoc, h_step_x]
    dsimp only [G₀]
    rw [h_iter P b₁ hb₁_pos hb₁_P]
    change (invE / t) * ((s / t) ^ P.card * ∫ τ, H τ ∂(Measure.pi (fun i => ν (c i)))) = _
    rw [h_marg, mul_assoc]

  
  have h_conj2 : inclusionMass v Q A t =
      t ^ Q.card * ∫ τ, Ψ τ ∂(unifCubeMeasure n t) +
      ∑ x ∈ A ∩ canonicalDemand v Q,
        ∫ s in Set.Icc invE t,
          (1 / (Real.exp 1 * s)) *
            inclusionMass (contractVal v x) (Q.erase x) (A.erase x) s := by
    let μ_t := unifCubeMeasure n t
    let ν_I := volume.restrict (Set.Icc invE t)
    haveI : IsProbabilityMeasure μ_t := h_cube_prob ht_pos
    let K_x : Fin n → (Fin n → ℝ) × ℝ → ℝ := fun x p =>
      if invE ≤ p.2 ∧ p.2 ≤ t ∧ s₀ p.1 ≤ p.2 ∧ p.1 x ≤ invE then
        (p.2)⁻¹ * ∏ g ∈ A.erase x, θ_surr p.1 p.2 g
      else 0
    have hK_meas : ∀ x : Fin n, Measurable (K_x x) := by
      intro x
      have h_cond : MeasurableSet
          {p : (Fin n → ℝ) × ℝ | invE ≤ p.2 ∧ p.2 ≤ t ∧ s₀ p.1 ≤ p.2 ∧ p.1 x ≤ invE} :=
        (measurableSet_le measurable_const measurable_snd).inter
          ((measurableSet_le measurable_snd measurable_const).inter
            ((measurableSet_le (hs₀_meas.comp measurable_fst) measurable_snd).inter
              (measurableSet_le ((measurable_pi_apply x).comp measurable_fst) measurable_const)))
      have h_θ_meas : ∀ g : Fin n, Measurable (fun p : (Fin n → ℝ) × ℝ => θ_surr p.1 p.2 g) := by
        intro g
        dsimp only [θ_surr]
        split_ifs
        · exact Measurable.ite
            (measurableSet_le ((measurable_pi_apply g).comp measurable_fst) measurable_const)
            (Real.measurable_log.comp (measurable_const.mul measurable_snd))
            measurable_const
        · exact (h_ret_s₀_m g).comp measurable_fst
      exact Measurable.ite h_cond
        (measurable_snd.inv.mul (Finset.measurable_prod (A.erase x) (fun g _ => h_θ_meas g)))
        measurable_const
    have hK_bdd : ∀ (x : Fin n) (p : (Fin n → ℝ) × ℝ), 0 ≤ K_x x p ∧ K_x x p ≤ invE⁻¹ := by
      intro x p
      dsimp only [K_x]
      split_ifs with hc
      · obtain ⟨hp1, hp2, _, _⟩ := hc
        have hp_pos : 0 < p.2 := h_invE_pos.trans_le hp1
        have hp_le1 : p.2 ≤ 1 := hp2.trans ht2
        have h_inv_nn : 0 ≤ (p.2)⁻¹ := inv_nonneg.mpr hp_pos.le
        have h_inv_le : (p.2)⁻¹ ≤ invE⁻¹ := inv_anti₀ h_invE_pos hp1
        have h_θ_bdd : ∀ g : Fin n, 0 ≤ θ_surr p.1 p.2 g ∧ θ_surr p.1 p.2 g ≤ 1 := by
          intro g
          dsimp only [θ_surr]
          split_ifs with hgD hτg
          · have hexp1 : 1 ≤ Real.exp 1 * p.2 := by
              calc (1 : ℝ) = Real.exp 1 * invE := h_exp_invE.symm
                _ ≤ Real.exp 1 * p.2 := mul_le_mul_of_nonneg_left hp1 (Real.exp_pos 1).le
            have hexp2 : Real.exp 1 * p.2 ≤ Real.exp 1 := by
              calc Real.exp 1 * p.2 ≤ Real.exp 1 * 1 :=
                  mul_le_mul_of_nonneg_left hp_le1 (Real.exp_pos 1).le
                _ = Real.exp 1 := mul_one _
            refine ⟨Real.log_nonneg hexp1, ?_⟩
            calc Real.log (Real.exp 1 * p.2)
                ≤ Real.log (Real.exp 1) := Real.log_le_log (by linarith) hexp2
              _ = 1 := Real.log_exp 1
          · exact ⟨le_rfl, zero_le_one⟩
          · exact h_ret_s₀_b g p.1
        have h_prd_nn : 0 ≤ ∏ g ∈ A.erase x, θ_surr p.1 p.2 g :=
          Finset.prod_nonneg (fun g _ => (h_θ_bdd g).1)
        have h_prd_le : (∏ g ∈ A.erase x, θ_surr p.1 p.2 g) ≤ 1 :=
          Finset.prod_le_one (fun g _ => (h_θ_bdd g).1) (fun g _ => (h_θ_bdd g).2)
        refine ⟨mul_nonneg h_inv_nn h_prd_nn, ?_⟩
        calc (p.2)⁻¹ * (∏ g ∈ A.erase x, θ_surr p.1 p.2 g)
            ≤ invE⁻¹ * 1 := mul_le_mul h_inv_le h_prd_le h_prd_nn (inv_nonneg.mpr h_invE_pos.le)
          _ = invE⁻¹ := mul_one _
      · exact ⟨le_rfl, inv_nonneg.mpr h_invE_pos.le⟩
    have hK_int : ∀ x : Fin n, Integrable (K_x x) (μ_t.prod ν_I) := fun x =>
      MeasureTheory.Integrable.of_mem_Icc 0 (invE⁻¹) (hK_meas x).aemeasurable
        (Filter.Eventually.of_forall (hK_bdd x))
    have hΨ_int : Integrable Ψ μ_t :=
      MeasureTheory.Integrable.of_mem_Icc (-1) 1 hΨ_meas.aemeasurable
        (Filter.Eventually.of_forall (fun τ => abs_le.mp (hΨ_bdd τ)))
    have hK_left_int : ∀ x : Fin n, Integrable (fun τ => ∫ s, K_x x (τ, s) ∂ν_I) μ_t :=
      fun x => (hK_int x).integral_prod_left
    have hae_ftc :
        (fun τ => ∏ g ∈ A, retentionProb (canonicalDemand v) t Q ∅ τ (fun _ => t) g) =ᵐ[μ_t]
          fun τ => Ψ τ + ∑ x ∈ A ∩ canonicalDemand v Q, ∫ s, K_x x (τ, s) ∂ν_I := by
      filter_upwards [h_cube_ae ht_pos] with τ hτ
      rw [(h_s2 τ (fun q _ => (hτ q).2)).1]
      congr 1
      refine Finset.sum_congr rfl (fun x _ => ?_)
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun s hs => ?_)
      dsimp only [K_x]
      by_cases hc : s₀ τ ≤ s ∧ τ x ≤ invE
      · rw [if_pos hc, if_pos ⟨hs.1, hs.2, hc.1, hc.2⟩]
      · rw [if_neg hc, if_neg (fun h => hc h.2.2)]
    have h_incl_t : survivalInclProb v Q A t =
        (∫ τ, Ψ τ ∂μ_t) +
        ∑ x ∈ A ∩ canonicalDemand v Q, ∫ s in Set.Icc invE t, (∫ τ, K_x x (τ, s) ∂μ_t) := by
      rw [h_s1_incl v Q A t hAQ ht1 ht2]
      change (∫ τ, _ ∂μ_t) = _
      rw [MeasureTheory.integral_congr_ae hae_ftc,
        MeasureTheory.integral_add hΨ_int
          (MeasureTheory.integrable_finset_sum _ (fun x _ => hK_left_int x)),
        MeasureTheory.integral_finset_sum _ (fun x _ => hK_left_int x)]
      congr 1
      refine Finset.sum_congr rfl (fun x _ => ?_)
      exact ((MeasureTheory.integral_prod (K_x x) (hK_int x)).symm.trans
        (MeasureTheory.integral_prod_symm (K_x x) (hK_int x)))
    unfold inclusionMass
    rw [h_incl_t, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun x hxAD => ?_)
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun s hs => ?_)
    dsimp only
    obtain ⟨hxA, _⟩ := Finset.mem_inter.mp hxAD
    have hxQ : x ∈ Q := hAQ hxA
    have hx_not_er : x ∉ Q.erase x := Finset.notMem_erase x Q
    have hA_er_sub : A.erase x ⊆ Q.erase x := Finset.erase_subset_erase x hAQ
    have hs_pos : 0 < s := h_invE_pos.trans_le hs.1
    have hs_le1 : s ≤ 1 := hs.2.trans ht2
    let H_xs : (Fin n → ℝ) → ℝ := fun τ =>
      ∏ g ∈ A.erase x,
        retentionProb (canonicalDemand (contractVal v x)) s (Q.erase x) ∅ τ (fun _ => s) g
    obtain ⟨hH_m_g, hH_b_g, hH_loc_g⟩ :=
      h_s1_reg (canonicalDemand (contractVal v x)) (Q.erase x) (fun _ => s)
        measurable_const (fun _ => ⟨hs.1, hs_le1⟩) (fun _ _ _ => rfl)
    have hH_meas : Measurable H_xs := Finset.measurable_prod (A.erase x) (fun g _ => hH_m_g g)
    have hH_bdd : ∀ τ, |H_xs τ| ≤ 1 := by
      intro τ
      have h0 : 0 ≤ H_xs τ := Finset.prod_nonneg (fun g _ => (hH_b_g g τ).1)
      have h1 : H_xs τ ≤ 1 :=
        Finset.prod_le_one (fun g _ => (hH_b_g g τ).1) (fun g _ => (hH_b_g g τ).2)
      rw [abs_of_nonneg h0]; exact h1
    have hH_loc : ∀ τ₁ τ₂, (∀ q ∈ Q.erase x, τ₁ q = τ₂ q) → H_xs τ₁ = H_xs τ₂ :=
      fun τ₁ τ₂ hq => Finset.prod_congr rfl (fun g hg => hH_loc_g g (hA_er_sub hg) τ₁ τ₂ hq)
    have hae_K :
        (fun τ => K_x x (τ, s)) =ᵐ[μ_t]
          fun τ => s⁻¹ * ((if τ x ≤ invE then (1 : ℝ) else 0) *
            (∏ q ∈ Q.erase x, if τ q ≤ s then (1 : ℝ) else 0) * H_xs τ) := by
      filter_upwards [h_cube_ae ht_pos] with τ hτ
      have h2 := (h_s2 τ (fun q _ => (hτ q).2)).2 x hxAD s hs
      dsimp only [K_x, H_xs] at h2 ⊢
      have heq_if :
          (if invE ≤ s ∧ s ≤ t ∧ s₀ τ ≤ s ∧ τ x ≤ invE then
            s⁻¹ * ∏ g ∈ A.erase x, θ_surr τ s g else 0) =
          (if s₀ τ ≤ s ∧ τ x ≤ invE then
            s⁻¹ * ∏ g ∈ A.erase x, θ_surr τ s g else 0) := by
        by_cases hc : s₀ τ ≤ s ∧ τ x ≤ invE
        · rw [if_pos ⟨hs.1, hs.2, hc.1, hc.2⟩, if_pos hc]
        · rw [if_neg (fun h => hc h.2.2), if_neg hc]
      rw [heq_if, h2]
    rw [MeasureTheory.integral_congr_ae hae_K, MeasureTheory.integral_const_mul,
      h_s3 (Q.erase x) x s H_xs hx_not_er hs_pos hs.2 hH_meas hH_bdd hH_loc,
      ← h_s1_incl (contractVal v x) (Q.erase x) (A.erase x) s hA_er_sub hs.1 hs_le1]
    have hcard : Q.card = (Q.erase x).card + 1 := (Finset.card_erase_add_one hxQ).symm
    have hinvE_eq : invE = (Real.exp 1)⁻¹ := by
      unfold invE; rw [Real.exp_neg]
    have ht_ne : t ≠ 0 := ht_pos.ne'
    have hs_ne : s ≠ 0 := hs_pos.ne'
    have hexp_ne : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
    rw [hcard, pow_succ, div_pow, hinvE_eq]
    field_simp

  
  have h_conj3a : (∫ τ, Ψ τ ∂(unifCubeMeasure n invE)) = (if A = ∅ then 1 else 0) := by
    haveI : IsProbabilityMeasure (unifCubeMeasure n invE) := h_cube_prob h_invE_pos
    have h_pt : ∀ τ : Fin n → ℝ, (∀ q ∈ Q, τ q ≤ invE) → Ψ τ = (if A = ∅ then 1 else 0) := by
      intro τ hτQ
      have hs₀_eq : s₀ τ = invE := by
        apply le_antisymm
        · refine Finset.max'_le _ _ _ (fun y hy => ?_)
          rcases Finset.mem_insert.mp hy with rfl | hy_img
          · exact le_rfl
          · obtain ⟨q, hqQ, rfl⟩ := Finset.mem_image.mp hy_img
            exact min_le_of_right_le (hτQ q hqQ)
        · exact (hs₀_bdd τ).1
      by_cases hA : A = ∅
      · subst hA
        simp [Ψ]
      · rw [if_neg hA]
        obtain ⟨g, hgA⟩ := Finset.nonempty_iff_ne_empty.mpr hA
        refine Finset.prod_eq_zero hgA ?_
        rw [hs₀_eq]
        unfold retentionProb
        split_ifs with hτg
        · obtain ⟨h_lo, h_hi⟩ := h_dt_bounds (canonicalDemand v) le_rfl Q ∅ τ (fun _ => invE) g
          have hdt : deathTime (canonicalDemand v) invE Q ∅ τ (fun _ => invE) g = invE :=
            le_antisymm h_hi h_lo
          rw [hdt, h_exp_invE, Real.log_one]
        · rfl
    have hae : Ψ =ᵐ[unifCubeMeasure n invE] fun _ => (if A = ∅ then (1 : ℝ) else 0) := by
      filter_upwards [h_cube_ae h_invE_pos] with τ hτ
      exact h_pt τ (fun q _ => (hτ q).2)
    rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const,
      MeasureTheory.probReal_univ, one_smul]
  have h_conj3b : ∀ x ∈ A, ∀ s : ℝ, invE < s → ∀ τ : Fin n → ℝ,
      Ψ (Function.update τ x s) = 0 := by
    intro x hxA s hs τ
    refine Finset.prod_eq_zero hxA ?_
    unfold retentionProb
    rw [Function.update_self, if_neg (not_le_of_gt hs)]
  have h_conj3c : ∀ x ∈ Q \ A, ∀ s : ℝ, invE < s → s ≤ t →
      s ^ (Q.erase x).card * ∫ τ, Ψ (Function.update τ x s) ∂(unifCubeMeasure n s) =
        inclusionMass v (Q.erase x) A s := by
    intro x hxQA s hs_gt hs_le_t
    obtain ⟨hxQ, hx_notA⟩ := Finset.mem_sdiff.mp hxQA
    have hs_pos : 0 < s := h_invE_pos.trans hs_gt
    have hs_le1 : s ≤ 1 := hs_le_t.trans ht2
    have hA_er : A ⊆ Q.erase x := by
      intro g hgA
      exact Finset.mem_erase.mpr ⟨fun hgx => hx_notA (hgx ▸ hgA), hAQ hgA⟩
    have h_pt : ∀ τ : Fin n → ℝ, (∀ q ∈ Q.erase x, τ q ≤ s) →
        Ψ (Function.update τ x s) =
          ∏ g ∈ A, retentionProb (canonicalDemand v) s (Q.erase x) ∅ τ (fun _ => s) g := by
      intro τ hτ_er
      have hs₀_eq : s₀ (Function.update τ x s) = s := by
        apply le_antisymm
        · refine Finset.max'_le _ _ _ (fun y hy => ?_)
          rcases Finset.mem_insert.mp hy with rfl | hy_img
          · exact hs_gt.le
          · obtain ⟨q, hqQ, rfl⟩ := Finset.mem_image.mp hy_img
            by_cases hqx : q = x
            · subst hqx
              rw [Function.update_self, min_eq_right hs_le1]
            · rw [Function.update_of_ne hqx]
              exact min_le_of_right_le (hτ_er q (Finset.mem_erase.mpr ⟨hqx, hqQ⟩))
        · have hx_mem : min 1 (Function.update τ x s x) ∈
              insert invE (Q.image (fun q => min 1 (Function.update τ x s q))) :=
            Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hxQ)
          have hle : min 1 (Function.update τ x s x) ≤ s₀ (Function.update τ x s) :=
            Finset.le_max' _ _ hx_mem
          rwa [Function.update_self, min_eq_right hs_le1] at hle
      dsimp only [Ψ]
      rw [hs₀_eq]
      refine Finset.prod_congr rfl (fun g hgA => ?_)
      have hgx : g ≠ x := fun h => hx_notA (h ▸ hgA)
      have hdt_eq : deathTime (canonicalDemand v) s Q ∅ (Function.update τ x s) (fun _ => s) g =
          deathTime (canonicalDemand v) s (Q.erase x) ∅ τ (fun _ => s) g := by
        unfold deathTime
        congr 1
        ext u
        by_cases hus : u = s
        · subst hus
          simp
        · simp only [Set.mem_union, Set.mem_singleton_iff, hus, or_false, Set.mem_setOf_eq]
          have hpres : ∀ hu2 : u ≤ s,
              presentSet Q ∅ (Function.update τ x s) (fun _ => s) u =
                presentSet (Q.erase x) ∅ τ (fun _ => s) u := by
            intro hu2
            have hu_lt : u < s := lt_of_le_of_ne hu2 hus
            rw [h_pres_empty, h_pres_empty]
            ext z
            simp only [Finset.mem_filter, Finset.mem_erase]
            by_cases hzx : z = x
            · subst hzx
              rw [Function.update_self]
              simp [not_le_of_gt hu_lt]
            · rw [Function.update_of_ne hzx]
              simp [hzx]
          refine ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, ?_⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, ?_⟩⟩
          · rwa [← hpres h2]
          · rwa [hpres h2]
      unfold retentionProb
      rw [Function.update_of_ne hgx, hdt_eq]
    have hae : (fun τ => Ψ (Function.update τ x s)) =ᵐ[unifCubeMeasure n s]
        (fun τ => ∏ g ∈ A, retentionProb (canonicalDemand v) s (Q.erase x) ∅ τ (fun _ => s) g) := by
      filter_upwards [h_cube_ae hs_pos] with τ hτ
      exact h_pt τ (fun q _ => (hτ q).2)
    rw [MeasureTheory.integral_congr_ae hae, ← h_s1_incl v (Q.erase x) A s hA_er hs_gt.le hs_le1]
    rfl

  exact ⟨h_conj1, h_conj2, h_conj3a, h_conj3b, h_conj3c⟩

theorem online_dist_meas_and_last_arrival : ∀ (n : ℕ) (v : ItemValuation n),
      (∀ (S B : Finset (Fin n)) (x : Fin n) (s : ℝ),
        x ∉ S → s ≤ 1 →
          0 ≤ survivalAcceptProb v x B S s ∧ survivalAcceptProb v x B S s ≤ 1) →
        let clamp : (Fin n → ℝ) → (Fin n → ℝ) := fun τ i => min 1 (max 0 (τ i))
        let onlineRun : (Fin n → ℝ) → Finset (Fin n) → Finset (Fin n) → ℝ := fun τ Q R =>
          survivalRunDistList v τ
            ((Q.sort (· ≤ ·)).mergeSort (fun a b => decide (τ a ≤ τ b)))
            ∅ (fun B => if B = ∅ then 1 else 0) R
        (∀ Q : Finset (Fin n), ∀ t : ℝ, ∀ R : Finset (Fin n),
          ¬(R ⊆ Q) → onlineSurvivalLaw v Q t R = 0) ∧
        (∀ Q R : Finset (Fin n),
          Measurable (fun τ => onlineRun (clamp τ) Q R) ∧
          (∀ τ, 0 ≤ onlineRun (clamp τ) Q R ∧ onlineRun (clamp τ) Q R ≤ 1) ∧
          (∀ τ, (∑ B ∈ Q.powerset, onlineRun (clamp τ) Q B) = 1) ∧
          (∀ τ₁ τ₂, (∀ q ∈ Q, τ₁ q = τ₂ q) →
            onlineRun (clamp τ₁) Q R = onlineRun (clamp τ₂) Q R)) ∧
        (∀ (Q R : Finset (Fin n)) (t : ℝ),
          invE ≤ t → t ≤ 1 →
            ∫ τ, onlineRun (clamp τ) Q R ∂(unifCubeMeasure n t) =
              onlineSurvivalLaw v Q t R) ∧
        ((∀ Q R : Finset (Fin n),
            ∫ τ, onlineRun (clamp τ) Q R ∂(unifCubeMeasure n invE) =
              (if R = ∅ then 1 else 0)) ∧
         (∀ (Q R : Finset (Fin n)) (x : Fin n) (s : ℝ),
            x ∈ Q → invE < s → s ≤ 1 →
              ∫ τ, onlineRun (clamp (Function.update τ x s)) Q R ∂(unifCubeMeasure n s) =
                survivalStepDist v (Q.erase x) x s
                  (fun B => onlineSurvivalLaw v (Q.erase x) s B) R)) :=
by
  intro n v h_acc clamp onlineRun
  have h_invE_pos : 0 < invE := by
    unfold invE
    exact Real.exp_pos (-1)
  have h_invE_le_one : invE ≤ 1 := by
    unfold invE
    exact Real.exp_le_one_iff.mpr (by norm_num)
  have h_clamp_le_one : ∀ (τ : Fin n → ℝ) (i : Fin n), clamp τ i ≤ 1 :=
    fun τ i => min_le_left 1 (max 0 (τ i))
  have h_clamp_id : ∀ {τ : Fin n → ℝ}, (∀ i : Fin n, 0 ≤ τ i ∧ τ i ≤ 1) → clamp τ = τ := by
    intro τ hτ
    ext i
    dsimp only [clamp]
    rw [max_eq_right (hτ i).1, min_eq_right (hτ i).2]
  have h_clamp_coord_meas : ∀ i : Fin n, Measurable (fun τ : Fin n → ℝ => clamp τ i) :=
    fun i => measurable_const.min (measurable_const.max (measurable_pi_apply i))

  
  
  
  have h_s3 : ∀ {r : ℝ}, 0 < r →
      IsProbabilityMeasure (unifCubeMeasure n r) ∧
      (∀ᵐ τ ∂(unifCubeMeasure n r), (∀ i : Fin n, 0 ≤ τ i ∧ τ i < r) ∧ Function.Injective τ) := by
    intro r hr
    let μ_r : Measure ℝ := (ENNReal.ofReal r)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) r)
    have h_prob_1d : IsProbabilityMeasure μ_r := by
      rw [MeasureTheory.isProbabilityMeasure_iff]
      simp only [μ_r, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
        Real.volume_Icc, sub_zero]
      exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top
    haveI : IsProbabilityMeasure μ_r := h_prob_1d
    have h_prob : IsProbabilityMeasure (unifCubeMeasure n r) := by
      unfold unifCubeMeasure
      infer_instance
    refine ⟨h_prob, ?_⟩
    have h_sing : ∀ c : ℝ, μ_r {c} = 0 := by
      intro c
      have h_le : volume.restrict (Set.Icc (0 : ℝ) r) {c} ≤ volume {c} :=
        Measure.restrict_apply_le _ _
      rw [Real.volume_singleton, nonpos_iff_eq_zero] at h_le
      simp [μ_r, h_le]
    have h_ae_lt : ∀ᵐ τ ∂(unifCubeMeasure n r), ∀ i : Fin n, 0 ≤ τ i ∧ τ i < r := by
      rw [Filter.eventually_all]
      intro i
      have h_ae_1d : ∀ᵐ u ∂μ_r, 0 ≤ u ∧ u < r := by
        rw [ae_iff]
        have h_sub : {u : ℝ | ¬(0 ≤ u ∧ u < r)} ⊆ (Set.Icc (0 : ℝ) r)ᶜ ∪ {r} := by
          intro u hu
          by_cases h_icc : u ∈ Set.Icc (0 : ℝ) r
          · right
            rw [Set.mem_singleton_iff]
            exact le_antisymm h_icc.2 (not_lt.mp (fun hlt => hu ⟨h_icc.1, hlt⟩))
          · exact Or.inl h_icc
        refine measure_mono_null h_sub (measure_union_null ?_ (h_sing r))
        simp [μ_r, Measure.restrict_apply measurableSet_Icc.compl]
      exact (MeasureTheory.measurePreserving_eval (fun _ : Fin n => μ_r) i).quasiMeasurePreserving.ae
        h_ae_1d
    have h_ae_inj : ∀ᵐ τ ∂(unifCubeMeasure n r), Function.Injective τ := by
      have h_pair : ∀ i : Fin n, ∀ j : Fin n, ∀ᵐ τ ∂(unifCubeMeasure n r), i ≠ j → τ i ≠ τ j := by
        intro i j
        by_cases hij : i = j
        · exact Filter.Eventually.of_forall (fun _ hne => (hne hij).elim)
        · suffices h_neq : ∀ᵐ τ ∂(unifCubeMeasure n r), τ i ≠ τ j by
            exact h_neq.mono (fun _ h _ => h)
          rw [ae_iff]
          have h_set_eq : {τ : Fin n → ℝ | ¬(τ i ≠ τ j)} = {τ : Fin n → ℝ | τ i = τ j} := by
            ext τ; simp
          rw [h_set_eq]
          obtain ⟨pred, hpred⟩ : ∃ pred : Fin n → Prop, ∀ k, pred k ↔ k = i :=
            ⟨fun k => k = i, fun _ => Iff.rfl⟩
          let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) pred
          let μ_in : Measure ({k : Fin n // pred k} → ℝ) := Measure.pi (fun _ => μ_r)
          let μ_out : Measure ({k : Fin n // ¬ pred k} → ℝ) := Measure.pi (fun _ => μ_r)
          haveI : IsProbabilityMeasure μ_in := by dsimp only [μ_in]; infer_instance
          haveI : IsProbabilityMeasure μ_out := by dsimp only [μ_out]; infer_instance
          have h_mp : MeasurePreserving e (unifCubeMeasure n r) (μ_in.prod μ_out) :=
            MeasureTheory.measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => μ_r) pred
          let i_sub : {k : Fin n // pred k} := ⟨i, (hpred i).mpr rfl⟩
          have hj_np : ¬ pred j := mt (hpred j).mp (Ne.symm hij)
          let j_sub : {k : Fin n // ¬ pred k} := ⟨j, hj_np⟩
          let E : Set (({k // pred k} → ℝ) × ({k // ¬ pred k} → ℝ)) :=
            {q | q.1 i_sub = q.2 j_sub}
          have hE_meas : MeasurableSet E :=
            measurableSet_eq_fun ((measurable_pi_apply i_sub).comp measurable_fst)
              ((measurable_pi_apply j_sub).comp measurable_snd)
          have h_pre : e ⁻¹' E = {τ : Fin n → ℝ | τ i = τ j} := rfl
          rw [← h_pre, h_mp.measure_preimage hE_meas.nullMeasurableSet,
            MeasureTheory.Measure.prod_apply_symm hE_meas]
          have h_sec : ∀ y : {k // ¬ pred k} → ℝ,
              μ_in ((fun x => (x, y)) ⁻¹' E) = 0 := by
            intro y
            have h_pre_y : (fun x : {k // pred k} → ℝ => (x, y)) ⁻¹' E =
                (Function.eval i_sub : ({k // pred k} → ℝ) → ℝ) ⁻¹' ({y j_sub} : Set ℝ) := rfl
            rw [h_pre_y,
              (MeasureTheory.measurePreserving_eval (fun _ : {k // pred k} => μ_r) i_sub).measure_preimage
                (measurableSet_singleton (y j_sub)).nullMeasurableSet]
            exact h_sing (y j_sub)
          simp_rw [h_sec, MeasureTheory.lintegral_zero]
      have h_all : ∀ᵐ τ ∂(unifCubeMeasure n r), ∀ i j : Fin n, i ≠ j → τ i ≠ τ j := by
        rw [Filter.eventually_all]
        intro i
        rw [Filter.eventually_all]
        exact h_pair i
      refine h_all.mono (fun τ hτ i j hij_eq => ?_)
      by_contra hne
      exact hτ i j hne hij_eq
    exact h_ae_lt.and h_ae_inj

  
  
  
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
      dsimp only [candEff]
      split_ifs with hc
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
          ext p
          simp [presentSet]
        rw [heq_z]
        split_ifs
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
              ext z
              specialize hzU z
              by_cases hz : z ∈ U <;> simp [hz] at hzU ⊢ <;> exact hzU
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
      intro g
      unfold retentionProb
      exact Measurable.ite (measurableSet_le ((measurable_pi_apply g).comp hτ_fn) measurable_const)
        (Real.measurable_log.comp (measurable_const.mul (h_meas_dt g))) measurable_const
    have h_meas_rp : Measurable (fun p : P => retainProd C (s_fn p) S ∅ (τ_fn p) (β_fn p) B) := by
      unfold retainProd
      split_ifs with hBS
      · exact (Finset.measurable_prod B (fun g _ => h_meas_ret g)).mul
          (Finset.measurable_prod (S \ B) (fun g _ => measurable_const.sub (h_meas_ret g)))
      · exact measurable_const
    let Φ : P → ℝ := fun p =>
      if p.1 ≤ invE then 0 else retainProd C (s_fn p) S ∅ (τ_fn p) (β_fn p) B
    have hΦ_meas : Measurable Φ :=
      Measurable.ite (measurableSet_le measurable_fst measurable_const) measurable_const h_meas_rp
    let ν : Measure (Fin n → ℝ) := unifCubeMeasure n 1
    haveI : IsProbabilityMeasure ν := (h_s3 zero_lt_one).1
    have hH_meas : Measurable (fun s : ℝ => ∫ u, Φ (s, u) ∂ν) :=
      (hΦ_meas.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
    have h_eq_fn : (fun s : ℝ => if s ≤ invE then 0 else survivalLaw w S s B) =
        (fun s : ℝ => ∫ u, Φ (s, u) ∂ν) := by
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
        let μ₁ : Measure ℝ := (ENNReal.ofReal 1)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) 1)
        let μ_s : Measure ℝ := (ENNReal.ofReal s)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) s)
        let scale_s : ℝ → ℝ := fun x => s * x
        have h_sc_meas : Measurable scale_s := measurable_const_mul s
        have h_prob₁ : IsProbabilityMeasure μ₁ := by
          rw [MeasureTheory.isProbabilityMeasure_iff]
          simp [μ₁, Real.volume_Icc]
        haveI : IsProbabilityMeasure μ₁ := h_prob₁
        haveI : IsProbabilityMeasure (μ₁.map scale_s) :=
          Measure.isProbabilityMeasure_map h_sc_meas.aemeasurable
        have h_1d : μ₁.map scale_s = μ_s := by
          have hμ₁_eq : μ₁ = volume.restrict (Set.Icc (0 : ℝ) 1) := by simp [μ₁]
          have h_pre : scale_s ⁻¹' Set.Icc (0 : ℝ) s = Set.Icc (0 : ℝ) 1 := by
            ext x
            simp only [Set.mem_preimage, Set.mem_Icc, scale_s]
            exact ⟨fun ⟨h1, h2⟩ => ⟨(mul_nonneg_iff_of_pos_left hs_pos).mp h1,
              (mul_le_iff_le_one_right hs_pos).mp h2⟩,
              fun ⟨h1, h2⟩ => ⟨mul_nonneg hs_pos.le h1, (mul_le_iff_le_one_right hs_pos).mpr h2⟩⟩
          rw [hμ₁_eq, ← h_pre, ← Measure.restrict_map h_sc_meas measurableSet_Icc,
            Real.map_volume_mul_left hs_pos.ne', abs_of_pos (inv_pos.mpr hs_pos),
            ENNReal.ofReal_inv_of_pos hs_pos, Measure.restrict_smul]
        let Scale_s : (Fin n → ℝ) → (Fin n → ℝ) := fun u i => s * u i
        have h_Scale_meas : Measurable Scale_s :=
          measurable_pi_iff.mpr (fun i => measurable_const.mul (measurable_pi_apply i))
        have h_map_cube : ν.map Scale_s = unifCubeMeasure n s := by
          change (Measure.pi (fun _ : Fin n => μ₁)).map (fun u i => scale_s (u i)) =
            Measure.pi (fun _ : Fin n => μ_s)
          rw [Measure.pi_map_pi (fun _ => h_sc_meas.aemeasurable)]
          simp_rw [h_1d]
        let g_s : (Fin n → ℝ) → ℝ := fun τ => retainProd C s S ∅ τ (fun _ => s) B
        have h_gs_eq : ∀ τ : Fin n → ℝ, g_s τ = Φ (s, fun i => s⁻¹ * τ i) := by
          intro τ
          dsimp only [g_s, Φ, s_fn, τ_fn, β_fn]
          rw [if_neg hs, hs_max]
          have h_mul_inv : (fun i : Fin n => s * (s⁻¹ * τ i)) = τ := by
            ext i; exact mul_inv_cancel_left₀ hs_pos.ne' (τ i)
          rw [h_mul_inv]
        have hg_meas : Measurable g_s := by
          have h_inv_meas : Measurable (fun τ : Fin n → ℝ => ((s, fun i => s⁻¹ * τ i) : P)) :=
            measurable_const.prodMk
              (measurable_pi_iff.mpr (fun i => measurable_const.mul (measurable_pi_apply i)))
          rw [funext h_gs_eq]
          exact hΦ_meas.comp h_inv_meas
        have h_gs_Scale : ∀ u : Fin n → ℝ, g_s (Scale_s u) = Φ (s, u) := by
          intro u
          dsimp only [g_s, Scale_s, Φ, s_fn, τ_fn, β_fn]
          rw [if_neg hs, hs_max]
        dsimp only [survivalLaw, genSurvivalLaw, genSurvivalLaw2]
        change (∫ τ, g_s τ ∂(unifCubeMeasure n s)) = ∫ u, Φ (s, u) ∂ν
        rw [← h_map_cube,
          MeasureTheory.integral_map h_Scale_meas.aemeasurable hg_meas.aestronglyMeasurable]
        simp_rw [h_gs_Scale]
    rwa [h_eq_fn]

  have h_s1 : ∀ (S B : Finset (Fin n)) (x : Fin n),
      Measurable (fun s : ℝ => survivalAcceptProb v x B S s) := by
    intro S B x
    let F_v : ℝ → ℝ := fun s => if s ≤ invE then 0 else survivalLaw v S s B
    let F_vx : ℝ → ℝ := fun s => if s ≤ invE then 0 else survivalLaw (contractVal v x) S s B
    have hFv : Measurable F_v := h_F_meas v S B
    have hFvx : Measurable F_vx := h_F_meas (contractVal v x) S B
    have h_rew : (fun s : ℝ => survivalAcceptProb v x B S s) =
        fun s => if s ≤ invE then 0
          else if x ∉ canonicalDemand v (insert x S) then 0
          else if F_v s = 0 then 0
          else (1 / (Real.exp 1 * s)) * (F_vx s / F_v s) := by
      ext s
      unfold survivalAcceptProb
      by_cases hs : s ≤ invE
      · simp [hs]
      · simp [hs, F_v, F_vx]
    rw [h_rew]
    by_cases hxD : x ∉ canonicalDemand v (insert x S)
    · have h_zero : (fun s : ℝ => if s ≤ invE then (0 : ℝ)
          else if x ∉ canonicalDemand v (insert x S) then 0
          else if F_v s = 0 then 0
          else (1 / (Real.exp 1 * s)) * (F_vx s / F_v s)) = fun _ => 0 := by
        ext s; simp [hxD]
      rw [h_zero]
      exact measurable_const
    · simp_rw [if_neg hxD]
      refine Measurable.ite measurableSet_Iic measurable_const
        (Measurable.ite (measurableSet_eq_fun hFv measurable_const) measurable_const ?_)
      exact (measurable_const.div (measurable_const.mul measurable_id)).mul (hFvx.div hFv)

  
  
  
  have h_step_supp : ∀ (S : Finset (Fin n)) (x : Fin n) (s : ℝ) (dist : Finset (Fin n) → ℝ),
      (∀ B, ¬(B ⊆ S) → dist B = 0) →
        ∀ B, ¬(B ⊆ insert x S) → survivalStepDist v S x s dist B = 0 := by
    intro S x s dist hsupp B hB
    unfold survivalStepDist
    have hB_notS : ¬(B ⊆ S) := fun h => hB (h.trans (Finset.subset_insert x S))
    have h1 : (if x ∉ B then dist B * (1 - survivalAcceptProb v x B S s) else 0) = 0 := by
      by_cases hxB : x ∉ B
      · rw [if_pos hxB, hsupp B hB_notS, zero_mul]
      · rw [if_neg hxB]
    have h2 : (if x ∈ B then dist (B.erase x) * survivalAcceptProb v x (B.erase x) S s else 0) = 0 := by
      split_ifs with hxB
      · have h_er_notS : ¬(B.erase x ⊆ S) := by
          intro h_er
          apply hB
          rw [← Finset.insert_erase hxB]
          exact Finset.insert_subset_insert x h_er
        rw [hsupp (B.erase x) h_er_notS, zero_mul]
      · rfl
    rw [h1, h2, add_zero]

  have h_step_prob : ∀ (S : Finset (Fin n)) (x : Fin n) (s : ℝ) (dist : Finset (Fin n) → ℝ),
      x ∉ S → s ≤ 1 →
      (∀ B, ¬(B ⊆ S) → dist B = 0) →
      (∀ B, 0 ≤ dist B) →
      (∑ B ∈ S.powerset, dist B) = 1 →
        (∀ B, 0 ≤ survivalStepDist v S x s dist B ∧ survivalStepDist v S x s dist B ≤ 1) ∧
        (∑ B ∈ (insert x S).powerset, survivalStepDist v S x s dist B) = 1 := by
    intro S x s dist hxS hs hsupp hnn hsum
    let dist' := survivalStepDist v S x s dist
    have hnn' : ∀ B, 0 ≤ dist' B := by
      intro B
      dsimp only [dist', survivalStepDist]
      refine add_nonneg ?_ ?_
      · by_cases hxB : x ∉ B
        · rw [if_pos hxB]
          exact mul_nonneg (hnn B) (sub_nonneg.mpr (h_acc S B x s hxS hs).2)
        · rw [if_neg hxB]
      · split_ifs
        · exact mul_nonneg (hnn (B.erase x)) (h_acc S (B.erase x) x s hxS hs).1
        · exact le_rfl
    have hsum' : (∑ B ∈ (insert x S).powerset, dist' B) = 1 := by
      rw [Finset.powerset_insert]
      have h_disj : Disjoint S.powerset (S.powerset.image (insert x)) := by
        rw [Finset.disjoint_left]
        intro B hB hB_img
        obtain ⟨W, _, rfl⟩ := Finset.mem_image.mp hB_img
        exact hxS ((Finset.mem_powerset.mp hB) (Finset.mem_insert_self x W))
      rw [Finset.sum_union h_disj]
      have h_out : (∑ B ∈ S.powerset, dist' B) =
          ∑ W ∈ S.powerset, dist W * (1 - survivalAcceptProb v x W S s) := by
        refine Finset.sum_congr rfl (fun W hW => ?_)
        have hxW : x ∉ W := fun h => hxS ((Finset.mem_powerset.mp hW) h)
        dsimp only [dist', survivalStepDist]
        rw [if_pos hxW, if_neg hxW, add_zero]
      have h_in : (∑ B ∈ S.powerset.image (insert x), dist' B) =
          ∑ W ∈ S.powerset, dist W * survivalAcceptProb v x W S s := by
        rw [Finset.sum_image]
        · refine Finset.sum_congr rfl (fun W hW => ?_)
          have hxW : x ∉ W := fun h => hxS ((Finset.mem_powerset.mp hW) h)
          have hx_ins : x ∈ insert x W := Finset.mem_insert_self x W
          dsimp only [dist', survivalStepDist]
          rw [if_neg (not_not.mpr hx_ins), if_pos hx_ins, Finset.erase_insert hxW, zero_add]
        · intro W₁ hW₁ W₂ hW₂ heq
          have hx₁ : x ∉ W₁ := fun h => hxS ((Finset.mem_powerset.mp hW₁) h)
          have hx₂ : x ∉ W₂ := fun h => hxS ((Finset.mem_powerset.mp hW₂) h)
          have h_er := congrArg (fun X : Finset (Fin n) => X.erase x) heq
          simpa only [Finset.erase_insert hx₁, Finset.erase_insert hx₂] using h_er
      rw [h_out, h_in, ← Finset.sum_add_distrib]
      have h_coll : (∑ W ∈ S.powerset,
          (dist W * (1 - survivalAcceptProb v x W S s) +
            dist W * survivalAcceptProb v x W S s)) = ∑ W ∈ S.powerset, dist W :=
        Finset.sum_congr rfl (fun W _ => by ring)
      rw [h_coll, hsum]
    refine ⟨fun B => ⟨hnn' B, ?_⟩, hsum'⟩
    by_cases hB : B ⊆ insert x S
    · calc dist' B
          ≤ ∑ C ∈ (insert x S).powerset, dist' C :=
            Finset.single_le_sum (fun C _ => hnn' C) (Finset.mem_powerset.mpr hB)
        _ = 1 := hsum'
    · rw [h_step_supp S x s dist hsupp B hB]
      exact zero_le_one

  have h_step_invE : ∀ (S : Finset (Fin n)) (x : Fin n) (s : ℝ) (dist : Finset (Fin n) → ℝ),
      x ∉ S → s ≤ invE →
      (∀ B, ¬(B ⊆ S) → dist B = 0) →
        survivalStepDist v S x s dist = dist := by
    intro S x s dist hxS hs hsupp
    ext B
    have h_acc0 : ∀ W, survivalAcceptProb v x W S s = 0 := by
      intro W; unfold survivalAcceptProb; exact if_pos hs
    unfold survivalStepDist
    by_cases hxB : x ∈ B
    · have hB_notS : ¬(B ⊆ S) := fun h => hxS (h hxB)
      rw [if_neg (not_not.mpr hxB), if_pos hxB, h_acc0, mul_zero, add_zero, hsupp B hB_notS]
    · rw [if_pos hxB, if_neg hxB, h_acc0, sub_zero, mul_one, add_zero]

  have h_union_cons : ∀ (S : Finset (Fin n)) (x : Fin n) (xs : List (Fin n)),
      insert x S ∪ xs.toFinset = S ∪ (x :: xs).toFinset := by
    intro S x xs
    ext z
    simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons]
    tauto

  have h_run_supp : ∀ (τ : Fin n → ℝ) (L : List (Fin n)) (S : Finset (Fin n))
      (dist : Finset (Fin n) → ℝ),
      (∀ B, ¬(B ⊆ S) → dist B = 0) →
        ∀ B, ¬(B ⊆ S ∪ L.toFinset) → survivalRunDistList v τ L S dist B = 0 := by
    intro τ L
    induction L with
    | nil =>
      intro S dist hsupp B hB
      simpa using hsupp B (fun h => hB (by simpa using h))
    | cons x xs ih =>
      intro S dist hsupp B hB
      have hB' : ¬(B ⊆ insert x S ∪ xs.toFinset) := by rwa [h_union_cons]
      exact ih (insert x S) (survivalStepDist v S x (τ x) dist)
        (h_step_supp S x (τ x) dist hsupp) B hB'

  have h_run_prob : ∀ (τ : Fin n → ℝ) (L : List (Fin n)) (S : Finset (Fin n))
      (dist : Finset (Fin n) → ℝ),
      L.Nodup → Disjoint L.toFinset S → (∀ x ∈ L, τ x ≤ 1) →
      (∀ B, ¬(B ⊆ S) → dist B = 0) → (∀ B, 0 ≤ dist B) → (∑ B ∈ S.powerset, dist B) = 1 →
        (∀ B, 0 ≤ survivalRunDistList v τ L S dist B ∧ survivalRunDistList v τ L S dist B ≤ 1) ∧
        (∑ B ∈ (S ∪ L.toFinset).powerset, survivalRunDistList v τ L S dist B) = 1 := by
    intro τ L
    induction L with
    | nil =>
      intro S dist _ _ _ hsupp hnn hsum
      have h_u : S ∪ ([] : List (Fin n)).toFinset = S := by simp
      rw [h_u]
      dsimp only [survivalRunDistList]
      refine ⟨fun B => ⟨hnn B, ?_⟩, hsum⟩
      by_cases hBS : B ⊆ S
      · calc dist B ≤ ∑ C ∈ S.powerset, dist C :=
              Finset.single_le_sum (fun C _ => hnn C) (Finset.mem_powerset.mpr hBS)
          _ = 1 := hsum
      · rw [hsupp B hBS]; exact zero_le_one
    | cons x xs ih =>
      intro S dist hnd hdj hτL hsupp hnn hsum
      obtain ⟨hx_xs, hnd_xs⟩ := List.nodup_cons.mp hnd
      have hxS : x ∉ S := Finset.disjoint_left.mp hdj (by simp)
      have hdj_xs : Disjoint xs.toFinset (insert x S) := by
        rw [Finset.disjoint_left]
        intro z hz hzin
        rcases Finset.mem_insert.mp hzin with rfl | hzS
        · exact hx_xs (List.mem_toFinset.mp hz)
        · exact Finset.disjoint_left.mp hdj (by simp [List.mem_toFinset.mp hz]) hzS
      have hτx : τ x ≤ 1 := hτL x List.mem_cons_self
      have hτxs : ∀ z ∈ xs, τ z ≤ 1 := fun z hz => hτL z (List.mem_cons_of_mem x hz)
      have hsupp₁ := h_step_supp S x (τ x) dist hsupp
      obtain ⟨hbdd₁, hsum₁⟩ := h_step_prob S x (τ x) dist hxS hτx hsupp hnn hsum
      have h_res := ih (insert x S) (survivalStepDist v S x (τ x) dist)
        hnd_xs hdj_xs hτxs hsupp₁ (fun B => (hbdd₁ B).1) hsum₁
      rwa [h_union_cons] at h_res

  have h_run_invE : ∀ (τ : Fin n → ℝ) (L : List (Fin n)) (S : Finset (Fin n))
      (dist : Finset (Fin n) → ℝ),
      L.Nodup → Disjoint L.toFinset S → (∀ x ∈ L, τ x ≤ invE) →
      (∀ B, ¬(B ⊆ S) → dist B = 0) →
        survivalRunDistList v τ L S dist = dist := by
    intro τ L
    induction L with
    | nil => intros; rfl
    | cons x xs ih =>
      intro S dist hnd hdj hτL hsupp
      obtain ⟨hx_xs, hnd_xs⟩ := List.nodup_cons.mp hnd
      have hxS : x ∉ S := Finset.disjoint_left.mp hdj (by simp)
      have hdj_xs : Disjoint xs.toFinset (insert x S) := by
        rw [Finset.disjoint_left]
        intro z hz hzin
        rcases Finset.mem_insert.mp hzin with rfl | hzS
        · exact hx_xs (List.mem_toFinset.mp hz)
        · exact Finset.disjoint_left.mp hdj (by simp [List.mem_toFinset.mp hz]) hzS
      have hτx : τ x ≤ invE := hτL x List.mem_cons_self
      have hτxs : ∀ z ∈ xs, τ z ≤ invE := fun z hz => hτL z (List.mem_cons_of_mem x hz)
      have h_eq₁ : survivalStepDist v S x (τ x) dist = dist := h_step_invE S x (τ x) dist hxS hτx hsupp
      have hsupp₁ : ∀ B, ¬(B ⊆ insert x S) → dist B = 0 := by
        rw [← h_eq₁]; exact h_step_supp S x (τ x) dist hsupp
      change survivalRunDistList v τ xs (insert x S) (survivalStepDist v S x (τ x) dist) = dist
      rw [h_eq₁]
      exact ih (insert x S) dist hnd_xs hdj_xs hτxs hsupp₁

  have h_run_congr : ∀ (τ₁ τ₂ : Fin n → ℝ) (L : List (Fin n)) (S : Finset (Fin n))
      (dist : Finset (Fin n) → ℝ),
      (∀ x ∈ L, τ₁ x = τ₂ x) →
        survivalRunDistList v τ₁ L S dist = survivalRunDistList v τ₂ L S dist := by
    intro τ₁ τ₂ L
    induction L with
    | nil => intros; rfl
    | cons x xs ih =>
      intro S dist h_eq
      change survivalRunDistList v τ₁ xs (insert x S) (survivalStepDist v S x (τ₁ x) dist) =
        survivalRunDistList v τ₂ xs (insert x S) (survivalStepDist v S x (τ₂ x) dist)
      rw [h_eq x List.mem_cons_self]
      exact ih (insert x S) _ (fun z hz => h_eq z (List.mem_cons_of_mem x hz))

  have h_run_append : ∀ (τ : Fin n → ℝ) (L : List (Fin n)) (x : Fin n) (S : Finset (Fin n))
      (dist : Finset (Fin n) → ℝ),
      survivalRunDistList v τ (L ++ [x]) S dist =
        survivalStepDist v (S ∪ L.toFinset) x (τ x) (survivalRunDistList v τ L S dist) := by
    intro τ L x
    induction L with
    | nil =>
      intro S dist
      simp [survivalRunDistList]
    | cons y ys ih =>
      intro S dist
      change survivalRunDistList v τ (ys ++ [x]) (insert y S) (survivalStepDist v S y (τ y) dist) =
        survivalStepDist v (S ∪ (y :: ys).toFinset) x (τ x)
          (survivalRunDistList v τ ys (insert y S) (survivalStepDist v S y (τ y) dist))
      rw [ih (insert y S) (survivalStepDist v S y (τ y) dist), h_union_cons]

  have h_run_meas : ∀ (L : List (Fin n)) (S : Finset (Fin n))
      (dist : (Fin n → ℝ) → Finset (Fin n) → ℝ),
      (∀ B, Measurable (fun τ => dist τ B)) →
        ∀ B, Measurable (fun τ => survivalRunDistList v (clamp τ) L S (dist τ) B) := by
    intro L
    induction L with
    | nil => intro S dist h_meas B; exact h_meas B
    | cons x xs ih =>
      intro S dist h_meas B
      refine ih (insert x S) (fun τ => survivalStepDist v S x (clamp τ x) (dist τ)) (fun W => ?_) B
      unfold survivalStepDist
      refine Measurable.add ?_ ?_
      · by_cases hxW : x ∉ W
        · simp_rw [if_pos hxW]
          exact (h_meas W).mul (measurable_const.sub ((h_s1 S W x).comp (h_clamp_coord_meas x)))
        · simp_rw [if_neg hxW]
          exact measurable_const
      · split_ifs
        · exact (h_meas (W.erase x)).mul ((h_s1 S (W.erase x) x).comp (h_clamp_coord_meas x))
        · exact measurable_const

  
  let dist₀ : Finset (Fin n) → ℝ := fun B => if B = ∅ then 1 else 0
  have h_dist₀_supp : ∀ B : Finset (Fin n), ¬(B ⊆ ∅) → dist₀ B = 0 := by
    intro B hB
    have hne : B ≠ ∅ := by rintro rfl; exact hB (Finset.empty_subset ∅)
    exact if_neg hne
  have h_dist₀_nn : ∀ B : Finset (Fin n), 0 ≤ dist₀ B := by
    intro B; dsimp only [dist₀]; split_ifs <;> norm_num
  have h_dist₀_sum : (∑ B ∈ (∅ : Finset (Fin n)).powerset, dist₀ B) = 1 := by
    simp [dist₀]

  have h_list_props : ∀ (τ : Fin n → ℝ) (Q : Finset (Fin n)),
      let L := (Q.sort (· ≤ ·)).mergeSort (fun a b => decide (τ a ≤ τ b))
      L.Nodup ∧ L.toFinset = Q := by
    intro τ Q L
    have h_perm := List.mergeSort_perm (Q.sort (· ≤ ·)) (fun a b => decide (τ a ≤ τ b))
    refine ⟨h_perm.nodup_iff.mpr (Q.sort_nodup (· ≤ ·)), ?_⟩
    rw [List.toFinset_eq_of_perm _ _ h_perm]
    ext z
    simp

  have h_out_pt : ∀ (τ : Fin n → ℝ) (Q R : Finset (Fin n)), ¬(R ⊆ Q) → onlineRun τ Q R = 0 := by
    intro τ Q R hRQ
    obtain ⟨_, h_toF⟩ := h_list_props τ Q
    have hR_not : ¬(R ⊆ ∅ ∪ ((Q.sort (· ≤ ·)).mergeSort (fun a b => decide (τ a ≤ τ b))).toFinset) := by
      rwa [Finset.empty_union, h_toF]
    exact h_run_supp τ _ ∅ dist₀ h_dist₀_supp R hR_not

  have h_loc_pt : ∀ (τ₁ τ₂ : Fin n → ℝ) (Q R : Finset (Fin n)),
      (∀ q ∈ Q, τ₁ q = τ₂ q) → onlineRun τ₁ Q R = onlineRun τ₂ Q R := by
    intro τ₁ τ₂ Q R h_eq
    let r₁ : Fin n → Fin n → Bool := fun a b => decide (τ₁ a ≤ τ₁ b)
    let r₂ : Fin n → Fin n → Bool := fun a b => decide (τ₂ a ≤ τ₂ b)
    have h_ms_eq : (Q.sort (· ≤ ·)).mergeSort r₁ = (Q.sort (· ≤ ·)).mergeSort r₂ := by
      have hm := @List.map_mergeSort (Fin n) (Fin n) r₁ r₂ id (Q.sort (· ≤ ·))
      simpa only [List.map_id] using hm (fun a ha b hb => by
        have haQ : a ∈ Q := (Finset.mem_sort (· ≤ ·)).mp ha
        have hbQ : b ∈ Q := (Finset.mem_sort (· ≤ ·)).mp hb
        simp [r₁, r₂, h_eq a haQ, h_eq b hbQ])
    dsimp only [onlineRun]
    change survivalRunDistList v τ₁ ((Q.sort (· ≤ ·)).mergeSort r₁) ∅ dist₀ R =
      survivalRunDistList v τ₂ ((Q.sort (· ≤ ·)).mergeSort r₂) ∅ dist₀ R
    rw [h_ms_eq]
    have h_congr := h_run_congr τ₁ τ₂ ((Q.sort (· ≤ ·)).mergeSort r₂) ∅ dist₀ (fun z hz => by
      have hzQ : z ∈ Q := by
        rw [← (h_list_props τ₂ Q).2]
        exact List.mem_toFinset.mpr hz
      exact h_eq z hzQ)
    exact congrFun h_congr R

  have h_invE_pt : ∀ (τ : Fin n → ℝ) (Q R : Finset (Fin n)),
      (∀ q ∈ Q, τ q ≤ invE) → onlineRun τ Q R = (if R = ∅ then 1 else 0) := by
    intro τ Q R h_le
    obtain ⟨h_nd, h_toF⟩ := h_list_props τ Q
    have h_le_L : ∀ x ∈ (Q.sort (· ≤ ·)).mergeSort (fun a b => decide (τ a ≤ τ b)), τ x ≤ invE := by
      intro x hx
      apply h_le x
      rw [← h_toF]
      exact List.mem_toFinset.mpr hx
    have h_eq := h_run_invE τ _ ∅ dist₀ h_nd (Finset.disjoint_empty_right _) h_le_L h_dist₀_supp
    exact congrFun h_eq R

  have h_last_pt : ∀ (τ : Fin n → ℝ) (Q R : Finset (Fin n)) (x : Fin n) (s : ℝ),
      x ∈ Q → (∀ y ∈ Q.erase x, τ y < s) → Set.InjOn τ (Q.erase x) →
        onlineRun (Function.update τ x s) Q R =
          survivalStepDist v (Q.erase x) x s (fun B => onlineRun τ (Q.erase x) B) R := by
    intro τ Q R x s hx h_lt h_inj
    let τ' := Function.update τ x s
    let r₀ : Fin n → Fin n → Bool := fun a b => decide (τ a ≤ τ b)
    let r' : Fin n → Fin n → Bool := fun a b => decide (τ' a ≤ τ' b)
    have h_eq_er : ∀ y ∈ Q.erase x, τ' y = τ y :=
      fun y hy => Function.update_of_ne (Finset.ne_of_mem_erase hy) s τ
    have h_L0_eq : ((Q.erase x).sort (· ≤ ·)).mergeSort r' =
        ((Q.erase x).sort (· ≤ ·)).mergeSort r₀ := by
      have hm := @List.map_mergeSort (Fin n) (Fin n) r' r₀ id ((Q.erase x).sort (· ≤ ·))
      simpa only [List.map_id] using hm (fun a ha b hb => by
        have ha' : a ∈ Q.erase x := (Finset.mem_sort (· ≤ ·)).mp ha
        have hb' : b ∈ Q.erase x := (Finset.mem_sort (· ≤ ·)).mp hb
        simp [r', r₀, h_eq_er a ha', h_eq_er b hb'])
    let L₁ := (Q.sort (· ≤ ·)).mergeSort r'
    let L₀ := ((Q.erase x).sort (· ≤ ·)).mergeSort r'
    have h_mem_L1 : ∀ z, z ∈ L₁ ↔ z ∈ Q := fun z => by
      rw [(List.mergeSort_perm (Q.sort (· ≤ ·)) r').mem_iff, Finset.mem_sort]
    have h_mem_L0 : ∀ z, z ∈ L₀ ↔ z ∈ Q.erase x := fun z => by
      rw [(List.mergeSort_perm ((Q.erase x).sort (· ≤ ·)) r').mem_iff, Finset.mem_sort]
    have h_nd_L1 : L₁.Nodup :=
      (List.mergeSort_perm (Q.sort (· ≤ ·)) r').nodup_iff.mpr (Q.sort_nodup (· ≤ ·))
    have h_nd_L0 : L₀.Nodup :=
      (List.mergeSort_perm ((Q.erase x).sort (· ≤ ·)) r').nodup_iff.mpr ((Q.erase x).sort_nodup (· ≤ ·))
    have h_nd_rhs : (L₀ ++ [x]).Nodup := by
      rw [List.nodup_append]
      refine ⟨h_nd_L0, List.nodup_singleton x, fun a ha b hb hab => ?_⟩
      rw [List.mem_singleton] at hb
      rw [hb] at hab
      rw [hab] at ha
      exact Finset.notMem_erase x Q ((h_mem_L0 x).mp ha)
    have h_perm : L₁.Perm (L₀ ++ [x]) := by
      rw [List.perm_ext_iff_of_nodup h_nd_L1 h_nd_rhs]
      intro z
      rw [h_mem_L1, List.mem_append, h_mem_L0, List.mem_singleton]
      refine ⟨fun hzQ => ?_, ?_⟩
      · by_cases hzx : z = x
        · exact Or.inr hzx
        · exact Or.inl (Finset.mem_erase.mpr ⟨hzx, hzQ⟩)
      · rintro (hz_er | rfl)
        · exact Finset.erase_subset x Q hz_er
        · exact hx
    have h_trans : ∀ a b c : Fin n, r' a b = true → r' b c = true → r' a c = true := by
      intro a b c hab hbc
      simp only [r', decide_eq_true_eq] at hab hbc ⊢
      exact hab.trans hbc
    have h_tot : ∀ a b : Fin n, (r' a b || r' b a) = true := by
      intro a b
      simp only [r', Bool.or_eq_true, decide_eq_true_eq]
      exact le_total (τ' a) (τ' b)
    have h_pw_L1 : List.Pairwise (fun a b => r' a b = true) L₁ :=
      List.pairwise_mergeSort h_trans h_tot (Q.sort (· ≤ ·))
    have h_pw_rhs : List.Pairwise (fun a b => r' a b = true) (L₀ ++ [x]) := by
      rw [List.pairwise_append]
      refine ⟨List.pairwise_mergeSort h_trans h_tot ((Q.erase x).sort (· ≤ ·)),
        List.pairwise_singleton _ x, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb
      rw [hb]
      have ha_er : a ∈ Q.erase x := (h_mem_L0 a).mp ha
      simp only [r', decide_eq_true_eq]
      rw [h_eq_er a ha_er]
      dsimp only [τ']
      rw [Function.update_self]
      exact (h_lt a ha_er).le
    have h_inj' : Set.InjOn τ' Q := by
      intro a ha b hb heq
      by_cases hax : a = x
      · by_cases hbx : b = x
        · exact hax.trans hbx.symm
        · have hb_er : b ∈ Q.erase x := Finset.mem_erase.mpr ⟨hbx, hb⟩
          have h_lhs : τ' a = s := by rw [hax]; dsimp only [τ']; exact Function.update_self x s τ
          rw [h_lhs, h_eq_er b hb_er] at heq
          exact (ne_of_lt (h_lt b hb_er) heq.symm).elim
      · by_cases hbx : b = x
        · have ha_er : a ∈ Q.erase x := Finset.mem_erase.mpr ⟨hax, ha⟩
          have h_rhs : τ' b = s := by rw [hbx]; dsimp only [τ']; exact Function.update_self x s τ
          rw [h_eq_er a ha_er, h_rhs] at heq
          exact (ne_of_lt (h_lt a ha_er) heq).elim
        · have ha_er : a ∈ Q.erase x := Finset.mem_erase.mpr ⟨hax, ha⟩
          have hb_er : b ∈ Q.erase x := Finset.mem_erase.mpr ⟨hbx, hb⟩
          rw [h_eq_er a ha_er, h_eq_er b hb_er] at heq
          exact h_inj ha_er hb_er heq
    have h_L_append : L₁ = L₀ ++ [x] := by
      refine h_perm.eq_of_pairwise (fun a b ha hb hab hba => ?_) h_pw_L1 h_pw_rhs
      simp only [r', decide_eq_true_eq] at hab hba
      have haQ : a ∈ Q := (h_mem_L1 a).mp ha
      have hbQ : b ∈ Q := (h_mem_L1 b).mp ((h_perm.mem_iff).mpr hb)
      exact h_inj' haQ hbQ (le_antisymm hab hba)
    have h_L0_toF : L₀.toFinset = Q.erase x := (h_list_props τ' (Q.erase x)).2
    have h_run_er : (fun B => survivalRunDistList v τ' L₀ ∅ dist₀ B) =
        (fun B => onlineRun τ (Q.erase x) B) := by
      ext B
      change onlineRun τ' (Q.erase x) B = onlineRun τ (Q.erase x) B
      exact h_loc_pt τ' τ (Q.erase x) B h_eq_er
    change survivalRunDistList v τ' L₁ ∅ dist₀ R = _
    rw [h_L_append, h_run_append τ' L₀ x ∅ dist₀, Finset.empty_union, h_L0_toF]
    have h_tx : τ' x = s := Function.update_self x s τ
    rw [h_tx]
    change survivalStepDist v (Q.erase x) x s (fun B => survivalRunDistList v τ' L₀ ∅ dist₀ B) R = _
    rw [h_run_er]

  
  
  
  have h_conj1 : ∀ Q : Finset (Fin n), ∀ t : ℝ, ∀ R : Finset (Fin n),
      ¬(R ⊆ Q) → onlineSurvivalLaw v Q t R = 0 := by
    intro Q t R hRQ
    unfold onlineSurvivalLaw
    have h_zero : (fun τ : Fin n → ℝ => onlineRun τ Q R) = fun _ => 0 := by
      ext τ; exact h_out_pt τ Q R hRQ
    change (∫ τ, onlineRun τ Q R ∂(unifCubeMeasure n t)) = 0
    rw [h_zero, MeasureTheory.integral_zero]

  have h_conj2 : ∀ Q R : Finset (Fin n),
      Measurable (fun τ => onlineRun (clamp τ) Q R) ∧
      (∀ τ, 0 ≤ onlineRun (clamp τ) Q R ∧ onlineRun (clamp τ) Q R ≤ 1) ∧
      (∀ τ, (∑ B ∈ Q.powerset, onlineRun (clamp τ) Q B) = 1) ∧
      (∀ τ₁ τ₂, (∀ q ∈ Q, τ₁ q = τ₂ q) →
        onlineRun (clamp τ₁) Q R = onlineRun (clamp τ₂) Q R) := by
    intro Q R
    have h_meas_Q : Measurable (fun τ : Fin n → ℝ => onlineRun (clamp τ) Q R) := by
      let cmpOf : (Fin n → ℝ) → (Fin n → Fin n → Bool) :=
        fun τ a b => decide (clamp τ a ≤ clamp τ b)
      have h_sum_eq : (fun τ : Fin n → ℝ => onlineRun (clamp τ) Q R) =
          fun τ => ∑ c ∈ (Finset.univ : Finset (Fin n → Fin n → Bool)),
            if cmpOf τ = c then
              survivalRunDistList v (clamp τ) ((Q.sort (· ≤ ·)).mergeSort c) ∅ dist₀ R
            else 0 := by
        ext τ
        rw [Finset.sum_ite_eq Finset.univ (cmpOf τ)
          (fun c => survivalRunDistList v (clamp τ) ((Q.sort (· ≤ ·)).mergeSort c) ∅ dist₀ R),
          if_pos (Finset.mem_univ _)]
      rw [h_sum_eq]
      refine Finset.measurable_sum Finset.univ (fun c _ => ?_)
      have h_set_c : MeasurableSet {τ : Fin n → ℝ | cmpOf τ = c} := by
        have h_iinter : {τ : Fin n → ℝ | cmpOf τ = c} =
            ⋂ a : Fin n, ⋂ b : Fin n, {τ : Fin n → ℝ | decide (clamp τ a ≤ clamp τ b) = c a b} := by
          ext τ
          simp [cmpOf, funext_iff]
        rw [h_iinter]
        refine MeasurableSet.iInter (fun a => MeasurableSet.iInter (fun b => ?_))
        cases hcab : c a b
        · have h_f : {τ : Fin n → ℝ | decide (clamp τ a ≤ clamp τ b) = false} =
              {τ : Fin n → ℝ | clamp τ a ≤ clamp τ b}ᶜ := by
            ext τ; simp
          rw [h_f]
          exact (measurableSet_le (h_clamp_coord_meas a) (h_clamp_coord_meas b)).compl
        · have h_t : {τ : Fin n → ℝ | decide (clamp τ a ≤ clamp τ b) = true} =
              {τ : Fin n → ℝ | clamp τ a ≤ clamp τ b} := by
            ext τ; simp
          rw [h_t]
          exact measurableSet_le (h_clamp_coord_meas a) (h_clamp_coord_meas b)
      exact Measurable.ite h_set_c
        (h_run_meas ((Q.sort (· ≤ ·)).mergeSort c) ∅ (fun _ => dist₀) (fun _ => measurable_const) R)
        measurable_const
    have h_bdd_sum : ∀ τ : Fin n → ℝ,
        (0 ≤ onlineRun (clamp τ) Q R ∧ onlineRun (clamp τ) Q R ≤ 1) ∧
        (∑ B ∈ Q.powerset, onlineRun (clamp τ) Q B) = 1 := by
      intro τ
      obtain ⟨h_nd, h_toF⟩ := h_list_props (clamp τ) Q
      have h_le1 : ∀ x ∈ (Q.sort (· ≤ ·)).mergeSort (fun a b => decide (clamp τ a ≤ clamp τ b)),
          clamp τ x ≤ 1 := fun x _ => h_clamp_le_one τ x
      obtain ⟨hbdd, hsum⟩ := h_run_prob (clamp τ) _ ∅ dist₀ h_nd (Finset.disjoint_empty_right _)
        h_le1 h_dist₀_supp h_dist₀_nn h_dist₀_sum
      rw [Finset.empty_union, h_toF] at hsum
      exact ⟨hbdd R, hsum⟩
    refine ⟨h_meas_Q, fun τ => (h_bdd_sum τ).1, fun τ => (h_bdd_sum τ).2, ?_⟩
    intro τ₁ τ₂ hq
    exact h_loc_pt (clamp τ₁) (clamp τ₂) Q R (fun q hqQ => by dsimp only [clamp]; rw [hq q hqQ])

  have h_conj3 : ∀ (Q R : Finset (Fin n)) (t : ℝ),
      invE ≤ t → t ≤ 1 →
        ∫ τ, onlineRun (clamp τ) Q R ∂(unifCubeMeasure n t) =
          onlineSurvivalLaw v Q t R := by
    intro Q R t ht_lo ht_hi
    have ht_pos : 0 < t := h_invE_pos.trans_le ht_lo
    obtain ⟨_, h_ae⟩ := h_s3 ht_pos
    unfold onlineSurvivalLaw
    refine MeasureTheory.integral_congr_ae (h_ae.mono (fun τ hτ => ?_))
    change onlineRun (clamp τ) Q R = onlineRun τ Q R
    have h_cl : clamp τ = τ := h_clamp_id (fun i => ⟨(hτ.1 i).1, (hτ.1 i).2.le.trans ht_hi⟩)
    rw [h_cl]

  have h_conj4a : ∀ Q R : Finset (Fin n),
      ∫ τ, onlineRun (clamp τ) Q R ∂(unifCubeMeasure n invE) =
        (if R = ∅ then 1 else 0) := by
    intro Q R
    obtain ⟨h_prob, h_ae⟩ := h_s3 h_invE_pos
    haveI : IsProbabilityMeasure (unifCubeMeasure n invE) := h_prob
    have h_ae_eq : (fun τ => onlineRun (clamp τ) Q R) =ᵐ[unifCubeMeasure n invE]
        fun _ => (if R = ∅ then (1 : ℝ) else 0) := by
      refine h_ae.mono (fun τ hτ => ?_)
      dsimp only
      have h_cl : clamp τ = τ :=
        h_clamp_id (fun i => ⟨(hτ.1 i).1, (hτ.1 i).2.le.trans h_invE_le_one⟩)
      rw [h_cl]
      exact h_invE_pt τ Q R (fun q _ => (hτ.1 q).2.le)
    rw [MeasureTheory.integral_congr_ae h_ae_eq, MeasureTheory.integral_const,
      MeasureTheory.probReal_univ, one_smul]

  have h_conj4b : ∀ (Q R : Finset (Fin n)) (x : Fin n) (s : ℝ),
      x ∈ Q → invE < s → s ≤ 1 →
        ∫ τ, onlineRun (clamp (Function.update τ x s)) Q R ∂(unifCubeMeasure n s) =
          survivalStepDist v (Q.erase x) x s
            (fun B => onlineSurvivalLaw v (Q.erase x) s B) R := by
    intro Q R x s hx hs_gt hs_le
    have hs_pos : 0 < s := h_invE_pos.trans hs_gt
    obtain ⟨h_prob, h_ae⟩ := h_s3 hs_pos
    haveI : IsProbabilityMeasure (unifCubeMeasure n s) := h_prob
    let c₁ : ℝ := if x ∉ R then 1 - survivalAcceptProb v x R (Q.erase x) s else 0
    let c₂ : ℝ := if x ∈ R then survivalAcceptProb v x (R.erase x) (Q.erase x) s else 0
    have h_step_lin : ∀ d : Finset (Fin n) → ℝ,
        survivalStepDist v (Q.erase x) x s d R = d R * c₁ + d (R.erase x) * c₂ := by
      intro d
      dsimp only [survivalStepDist, c₁, c₂]
      split_ifs <;> ring
    have h_ae_eq : (fun τ => onlineRun (clamp (Function.update τ x s)) Q R) =ᵐ[unifCubeMeasure n s]
        fun τ => onlineRun (clamp τ) (Q.erase x) R * c₁ +
          onlineRun (clamp τ) (Q.erase x) (R.erase x) * c₂ := by
      refine h_ae.mono (fun τ ⟨h_lt_s, h_inj⟩ => ?_)
      dsimp only
      have h_cl_τ : clamp τ = τ :=
        h_clamp_id (fun i => ⟨(h_lt_s i).1, (h_lt_s i).2.le.trans hs_le⟩)
      have h_cl_upd : clamp (Function.update τ x s) = Function.update τ x s := by
        refine h_clamp_id (fun i => ?_)
        by_cases hix : i = x
        · rw [hix, Function.update_self]
          exact ⟨hs_pos.le, hs_le⟩
        · rw [Function.update_of_ne hix]
          exact ⟨(h_lt_s i).1, (h_lt_s i).2.le.trans hs_le⟩
      rw [h_cl_upd, h_cl_τ,
        h_last_pt τ Q R x s hx (fun y _ => (h_lt_s y).2) h_inj.injOn, h_step_lin]
    have h_int_B : ∀ B : Finset (Fin n),
        Integrable (fun τ => onlineRun (clamp τ) (Q.erase x) B) (unifCubeMeasure n s) := by
      intro B
      exact MeasureTheory.Integrable.of_mem_Icc 0 1 (h_conj2 (Q.erase x) B).1.aemeasurable
        (Filter.Eventually.of_forall (fun τ => (h_conj2 (Q.erase x) B).2.1 τ))
    rw [MeasureTheory.integral_congr_ae h_ae_eq,
      MeasureTheory.integral_add ((h_int_B R).mul_const c₁) ((h_int_B (R.erase x)).mul_const c₂),
      MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const,
      h_conj3 (Q.erase x) R s hs_gt.le hs_le,
      h_conj3 (Q.erase x) (R.erase x) s hs_gt.le hs_le,
      ← h_step_lin (fun B => onlineSurvivalLaw v (Q.erase x) s B)]

  exact ⟨h_conj1, h_conj2, h_conj3, h_conj4a, h_conj4b⟩

end InclusionAndMatchingInternal

section
open InclusionAndMatchingInternal

theorem thm_selection_inclusion_and_matching :
    -- (1) Section B.3: Pointwise safety of survivalLaw and online transitions
    (∀ (n : ℕ) (v : ItemValuation n) (S A : Finset (Fin n)) (t : ℝ),
      IsGSValuation v → invE ≤ t → t ≤ 1 → 0 < survivalLaw v S t A →
        ∃ T ⊆ S, A ⊆ canonicalDemand v T ∧ ∀ Y ⊆ A, v Y ≠ ⊥ ∧ 0 ≤ realVal v Y) ∧
    (∀ (n : ℕ) (v : ItemValuation n) (τ : Fin n → ℝ) (items : List (Fin n))
        (S₀ : Finset (Fin n)) (dist₀ : Finset (Fin n) → ℝ),
      IsGSValuation v → items.Nodup → Disjoint items.toFinset S₀ →
      (∀ x ∈ items, τ x ≤ 1) →
      (∀ B, 0 ≤ dist₀ B) →
      (∀ B, 0 < dist₀ B → ∃ T ⊆ S₀, B ⊆ canonicalDemand v T) →
        let dist' := survivalRunDistList v τ items S₀ dist₀
        (∀ B, 0 ≤ dist' B) ∧
        (∑ B : Finset (Fin n), dist' B) = (∑ B : Finset (Fin n), dist₀ B) ∧
        (∀ B, 0 < dist' B →
          ∃ T ⊆ S₀ ∪ items.toFinset,
            B ⊆ canonicalDemand v T ∧ ∀ Y ⊆ B, v Y ≠ ⊥ ∧ 0 ≤ realVal v Y)) ∧
    -- (2) Lemma B.7 (lem:inclusion): Inclusion recursion eq:recursion
    (∀ (n : ℕ) (v : ItemValuation n) (Q A : Finset (Fin n)) (t : ℝ),
      IsGSValuation v → A ⊆ Q → invE ≤ t → t ≤ 1 →
        inclusionMass v Q A t =
          Real.exp (-(Q.card : ℝ)) * (if A = ∅ then 1 else 0) +
          (∑ x ∈ Q \ A, ∫ s in Set.Icc invE t, inclusionMass v (Q.erase x) A s) +
          (∑ x ∈ A ∩ canonicalDemand v Q,
            ∫ s in Set.Icc invE t,
              (1 / (Real.exp 1 * s)) *
                inclusionMass (contractVal v x) (Q.erase x) (A.erase x) s)) ∧
    -- (3) Proposition B.6 (prop:matching): Distribution matching L_{Q, t} = μ^v_{Q, t}
    (∀ (n : ℕ) (v : ItemValuation n) (Q : Finset (Fin n)) (t : ℝ) (A : Finset (Fin n)),
      IsGSValuation v → invE ≤ t → t ≤ 1 →
        onlineSurvivalLaw v Q t A = survivalLaw v Q t A) :=
by
  have h_invE_pos : 0 < invE := by
    unfold invE
    exact Real.exp_pos (-1)

  have h_cube_prob : ∀ (n : ℕ) {r : ℝ}, 0 < r →
      IsProbabilityMeasure (unifCubeMeasure n r) := by
    intro n r hr
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

  
  have h_conj1a :
      ∀ (n : ℕ) (v : ItemValuation n) (S A : Finset (Fin n)) (t : ℝ),
        IsGSValuation v → invE ≤ t → t ≤ 1 → 0 < survivalLaw v S t A →
          ∃ T ⊆ S, A ⊆ canonicalDemand v T ∧ ∀ Y ⊆ A, v Y ≠ ⊥ ∧ 0 ≤ realVal v Y := by
    intro n v S A t hv ht1 ht2 hpos
    obtain ⟨_, _, h_safe, _⟩ := gs_canonical_safe_and_contract n v hv
    obtain ⟨h_surv, _, _⟩ := survival_accept_validity_and_mass_eq n v hv
    obtain ⟨T, hTS, hAD⟩ := (h_surv S A t ht1 ht2).2 hpos
    exact ⟨T, hTS, hAD, fun Y hYA => h_safe T Y (hYA.trans hAD)⟩

  
  have h_step_inv :
      ∀ (n : ℕ) (v : ItemValuation n) (S : Finset (Fin n)) (x : Fin n) (s : ℝ)
        (dist : Finset (Fin n) → ℝ),
        IsGSValuation v → x ∉ S → s ≤ 1 →
        (∀ B, 0 ≤ dist B) →
        (∀ B, 0 < dist B → ∃ T ⊆ S, B ⊆ canonicalDemand v T) →
          let dist₁ := survivalStepDist v S x s dist
          (∀ B, 0 ≤ dist₁ B) ∧
          (∑ B : Finset (Fin n), dist₁ B) = (∑ B : Finset (Fin n), dist B) ∧
          (∀ B, 0 < dist₁ B → ∃ T ⊆ insert x S, B ⊆ canonicalDemand v T) := by
    intro n v S x s dist hv hxS hs hnn hsupp
    obtain ⟨h_sub, _, _, h_cont⟩ := gs_canonical_safe_and_contract n v hv
    obtain ⟨h_surv, h_acc_bdd, _⟩ := survival_accept_validity_and_mass_eq n v hv
    let dist₁ := survivalStepDist v S x s dist
    have h_zero_in : ∀ B : Finset (Fin n), x ∈ B → dist B = 0 := by
      intro B hxB
      by_contra hne
      have hpos : 0 < dist B := lt_of_le_of_ne (hnn B) (Ne.symm hne)
      obtain ⟨T, hTS, hBD⟩ := hsupp B hpos
      exact hxS (hTS (h_sub T (hBD hxB)))
    have h_nn₁ : ∀ B : Finset (Fin n), 0 ≤ dist₁ B := by
      intro B
      dsimp only [dist₁, survivalStepDist]
      refine add_nonneg ?_ ?_
      · by_cases hxB : x ∈ B
        · rw [if_neg (not_not.mpr hxB)]
        · rw [if_pos hxB]
          exact mul_nonneg (hnn B) (sub_nonneg.mpr (h_acc_bdd S B x s hxS hs).2)
      · by_cases hxB : x ∈ B
        · rw [if_pos hxB]
          exact mul_nonneg (hnn (B.erase x)) (h_acc_bdd S (B.erase x) x s hxS hs).1
        · rw [if_neg hxB]
    have h_mass₁ : (∑ B : Finset (Fin n), dist₁ B) = ∑ B : Finset (Fin n), dist B := by
      let U : Finset (Finset (Fin n)) := Finset.univ
      let U_in := U.filter (fun B => x ∈ B)
      let U_out := U.filter (fun B => x ∉ B)
      have h_split₁ : (∑ B : Finset (Fin n), dist₁ B) =
          (∑ B ∈ U_in, dist₁ B) + (∑ B ∈ U_out, dist₁ B) :=
        (Finset.sum_filter_add_sum_filter_not U (fun B : Finset (Fin n) => x ∈ B) dist₁).symm
      have h_split₀ : (∑ B : Finset (Fin n), dist B) =
          (∑ B ∈ U_in, dist B) + (∑ B ∈ U_out, dist B) :=
        (Finset.sum_filter_add_sum_filter_not U (fun B : Finset (Fin n) => x ∈ B) dist).symm
      have h_sum_in : (∑ B ∈ U_in, dist₁ B) =
          ∑ W ∈ U_out, dist W * survivalAcceptProb v x W S s := by
        refine Finset.sum_bij (fun B _ => B.erase x) ?_ ?_ ?_ ?_
        · intro B hB
          simp only [U_out, U, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
            ne_eq, not_true_eq_false, false_and, not_false_eq_true]
        · intro B₁ hB₁ B₂ hB₂ heq
          dsimp only at heq
          have hx₁ : x ∈ B₁ := (Finset.mem_filter.mp hB₁).2
          have hx₂ : x ∈ B₂ := (Finset.mem_filter.mp hB₂).2
          rw [← Finset.insert_erase hx₁, ← Finset.insert_erase hx₂, heq]
        · intro W hW
          have hxW : x ∉ W := (Finset.mem_filter.mp hW).2
          refine ⟨insert x W, ?_, Finset.erase_insert hxW⟩
          simp only [U_in, U, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_insert_self]
        · intro B hB
          have hxB : x ∈ B := (Finset.mem_filter.mp hB).2
          dsimp only [dist₁, survivalStepDist]
          rw [if_neg (not_not.mpr hxB), if_pos hxB, zero_add]
      have h_sum_out : (∑ B ∈ U_out, dist₁ B) =
          ∑ W ∈ U_out, dist W * (1 - survivalAcceptProb v x W S s) := by
        refine Finset.sum_congr rfl (fun W hW => ?_)
        have hxW : x ∉ W := (Finset.mem_filter.mp hW).2
        dsimp only [dist₁, survivalStepDist]
        rw [if_pos hxW, if_neg hxW, add_zero]
      have h_zero_sum_in : (∑ B ∈ U_in, dist B) = 0 :=
        Finset.sum_eq_zero (fun B hB => h_zero_in B (Finset.mem_filter.mp hB).2)
      rw [h_split₁, h_sum_in, h_sum_out, ← Finset.sum_add_distrib, h_split₀, h_zero_sum_in,
        zero_add]
      refine Finset.sum_congr rfl (fun W _ => ?_)
      ring
    have h_supp₁ : ∀ B : Finset (Fin n), 0 < dist₁ B →
        ∃ T ⊆ insert x S, B ⊆ canonicalDemand v T := by
      intro B hpos
      dsimp only [dist₁, survivalStepDist] at hpos
      by_cases hxB : x ∈ B
      · rw [if_neg (not_not.mpr hxB), if_pos hxB, zero_add] at hpos
        let W := B.erase x
        have hposW : 0 < dist W * survivalAcceptProb v x W S s := hpos
        have h_acc_nn : 0 ≤ survivalAcceptProb v x W S s := (h_acc_bdd S W x s hxS hs).1
        have h_acc_pos : 0 < survivalAcceptProb v x W S s := by
          by_contra hle
          have heq : survivalAcceptProb v x W S s = 0 :=
            le_antisymm (not_lt.mp hle) h_acc_nn
          rw [heq, mul_zero] at hposW
          exact lt_irrefl 0 hposW
        unfold survivalAcceptProb at h_acc_pos
        by_cases hs_le : s ≤ invE
        · rw [if_pos hs_le] at h_acc_pos
          exact (lt_irrefl 0 h_acc_pos).elim
        · rw [if_neg hs_le] at h_acc_pos
          have hs_gt : invE < s := lt_of_not_ge hs_le
          have hs_pos : 0 < s := h_invE_pos.trans hs_gt
          by_cases hx_notD : x ∉ canonicalDemand v (insert x S)
          · rw [if_pos hx_notD] at h_acc_pos
            exact (lt_irrefl 0 h_acc_pos).elim
          · rw [if_neg hx_notD] at h_acc_pos
              
            have hxD : x ∈ canonicalDemand v (insert x S) := not_not.mp hx_notD
            by_cases h_den_zero : survivalLaw v S s W = 0
            · rw [if_pos h_den_zero] at h_acc_pos
              exact (lt_irrefl 0 h_acc_pos).elim
            · rw [if_neg h_den_zero] at h_acc_pos
              have h_den_nn : 0 ≤ survivalLaw v S s W := (h_surv S W s hs_gt.le hs).1
              have h_den_pos : 0 < survivalLaw v S s W :=
                lt_of_le_of_ne h_den_nn (Ne.symm h_den_zero)
              obtain ⟨hv_cont, h_comm⟩ := h_cont S x hxS hxD
              obtain ⟨h_surv_cont, _, _⟩ := survival_accept_validity_and_mass_eq n (contractVal v x) hv_cont
              have h_num_nn : 0 ≤ survivalLaw (contractVal v x) S s W :=
                (h_surv_cont S W s hs_gt.le hs).1
              have h_num_pos : 0 < survivalLaw (contractVal v x) S s W := by
                by_contra hle
                have heq : survivalLaw (contractVal v x) S s W = 0 :=
                  le_antisymm (not_lt.mp hle) h_num_nn
                rw [heq, zero_div, mul_zero] at h_acc_pos
                exact lt_irrefl 0 h_acc_pos
              obtain ⟨T₀, hT₀S, hWD⟩ := (h_surv_cont S W s hs_gt.le hs).2 h_num_pos
              obtain ⟨hxDT₀, h_eq_er⟩ := h_comm T₀ hT₀S
              refine ⟨insert x T₀, Finset.insert_subset_insert x hT₀S, ?_⟩
              rw [← Finset.insert_erase hxB]
              refine Finset.insert_subset_iff.mpr ⟨hxDT₀, ?_⟩
              exact hWD.trans (h_eq_er.symm ▸ Finset.erase_subset x _)
      · rw [if_pos hxB, if_neg hxB, add_zero] at hpos
        have h_one_sub_nn : 0 ≤ 1 - survivalAcceptProb v x B S s :=
          sub_nonneg.mpr (h_acc_bdd S B x s hxS hs).2
        have h_dist_pos : 0 < dist B := by
          by_contra hle
          have heq : dist B = 0 := le_antisymm (not_lt.mp hle) (hnn B)
          rw [heq, zero_mul] at hpos
          exact lt_irrefl 0 hpos
        obtain ⟨T, hTS, hBD⟩ := hsupp B h_dist_pos
        exact ⟨T, hTS.trans (Finset.subset_insert x S), hBD⟩
    exact ⟨h_nn₁, h_mass₁, h_supp₁⟩

  
  have h_conj1b :
      ∀ (n : ℕ) (v : ItemValuation n) (τ : Fin n → ℝ) (items : List (Fin n))
        (S₀ : Finset (Fin n)) (dist₀ : Finset (Fin n) → ℝ),
        IsGSValuation v → items.Nodup → Disjoint items.toFinset S₀ →
        (∀ x ∈ items, τ x ≤ 1) →
        (∀ B, 0 ≤ dist₀ B) →
        (∀ B, 0 < dist₀ B → ∃ T ⊆ S₀, B ⊆ canonicalDemand v T) →
          let dist' := survivalRunDistList v τ items S₀ dist₀
          (∀ B, 0 ≤ dist' B) ∧
          (∑ B : Finset (Fin n), dist' B) = (∑ B : Finset (Fin n), dist₀ B) ∧
          (∀ B, 0 < dist' B →
            ∃ T ⊆ S₀ ∪ items.toFinset,
              B ⊆ canonicalDemand v T ∧ ∀ Y ⊆ B, v Y ≠ ⊥ ∧ 0 ≤ realVal v Y) := by
    intro n v τ items S₀ dist₀ hv hnodup hdisj hτ hnn₀ hsupp₀
    obtain ⟨_, _, h_safe, _⟩ := gs_canonical_safe_and_contract n v hv
    have h_list :
        ∀ (L : List (Fin n)) (S : Finset (Fin n)) (dist : Finset (Fin n) → ℝ),
          L.Nodup → Disjoint L.toFinset S → (∀ x ∈ L, τ x ≤ 1) →
          (∀ B, 0 ≤ dist B) →
          (∀ B, 0 < dist B → ∃ T ⊆ S, B ⊆ canonicalDemand v T) →
            let dist' := survivalRunDistList v τ L S dist
            (∀ B, 0 ≤ dist' B) ∧
            (∑ B : Finset (Fin n), dist' B) = (∑ B : Finset (Fin n), dist B) ∧
            (∀ B, 0 < dist' B → ∃ T ⊆ S ∪ L.toFinset, B ⊆ canonicalDemand v T) := by
      intro L
      induction L with
      | nil =>
        intro S dist _ _ _ hnn hsupp
        refine ⟨hnn, rfl, fun B hpos => ?_⟩
        obtain ⟨T, hTS, hBD⟩ := hsupp B hpos
        refine ⟨T, ?_, hBD⟩
        simpa using hTS
      | cons x xs ih =>
        intro S dist hnd hdj hτL hnn hsupp
        obtain ⟨hx_xs, hnd_xs⟩ := List.nodup_cons.mp hnd
        have hx_in_L : x ∈ (x :: xs).toFinset := by simp
        have hxS : x ∉ S := Finset.disjoint_left.mp hdj hx_in_L
        have hdj_xs : Disjoint xs.toFinset (insert x S) := by
          rw [Finset.disjoint_left]
          intro z hz hzin
          rcases Finset.mem_insert.mp hzin with rfl | hzS
          · exact hx_xs (List.mem_toFinset.mp hz)
          · exact Finset.disjoint_left.mp hdj (by simp [List.mem_toFinset.mp hz]) hzS
        have hτx : τ x ≤ 1 := hτL x List.mem_cons_self
        have hτxs : ∀ z ∈ xs, τ z ≤ 1 :=
          fun z hz => hτL z (List.mem_cons_of_mem x hz)
        obtain ⟨hnn₁, hmass₁, hsupp₁⟩ :=
          h_step_inv n v S x (τ x) dist hv hxS hτx hnn hsupp
        obtain ⟨hnn', hmass', hsupp'⟩ :=
          ih (insert x S) (survivalStepDist v S x (τ x) dist) hnd_xs hdj_xs hτxs hnn₁ hsupp₁
        refine ⟨hnn', hmass'.trans hmass₁, fun B hpos => ?_⟩
        obtain ⟨T, hTsub, hBD⟩ := hsupp' B hpos
        refine ⟨T, hTsub.trans ?_, hBD⟩
        intro z hz
        simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons] at hz ⊢
        rcases hz with (rfl | hzS) | hzxs
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl hzS
        · exact Or.inr (Or.inr hzxs)
    obtain ⟨hnn', hmass', hsupp'⟩ := h_list items S₀ dist₀ hnodup hdisj hτ hnn₀ hsupp₀
    refine ⟨hnn', hmass', fun B hpos => ?_⟩
    obtain ⟨T, hTsub, hBD⟩ := hsupp' B hpos
    exact ⟨T, hTsub, hBD, fun Y hYB => h_safe T Y (hYB.trans hBD)⟩

  
  have h_conj2 :
      ∀ (n : ℕ) (v : ItemValuation n) (Q A : Finset (Fin n)) (t : ℝ),
        IsGSValuation v → A ⊆ Q → invE ≤ t → t ≤ 1 →
          inclusionMass v Q A t =
            Real.exp (-(Q.card : ℝ)) * (if A = ∅ then 1 else 0) +
            (∑ x ∈ Q \ A, ∫ s in Set.Icc invE t, inclusionMass v (Q.erase x) A s) +
            (∑ x ∈ A ∩ canonicalDemand v Q,
              ∫ s in Set.Icc invE t,
                (1 / (Real.exp 1 * s)) *
                  inclusionMass (contractVal v x) (Q.erase x) (A.erase x) s) := by
    intro n v Q A t hv hAQ ht1 ht2
    obtain ⟨_, h_pers, _, h_cont⟩ := gs_canonical_safe_and_contract n v hv
    have h_persQ : ∀ T ⊆ Q, canonicalDemand v Q ∩ T ⊆ canonicalDemand v T :=
      fun T hTQ => h_pers T Q hTQ
    have h_commQ : ∀ x ∈ A ∩ canonicalDemand v Q, ∀ T ⊆ Q.erase x,
        canonicalDemand (contractVal v x) T = (canonicalDemand v (insert x T)).erase x := by
      intro x hx T hT
      obtain ⟨hxA, hxD⟩ := Finset.mem_inter.mp hx
      have hxQ : x ∈ Q := hAQ hxA
      have hx_not_er : x ∉ Q.erase x := Finset.notMem_erase x Q
      have hins : insert x (Q.erase x) = Q := Finset.insert_erase hxQ
      rw [← hins] at hxD
      exact ((h_cont (Q.erase x) x hx_not_er hxD).2 T hT).2
    let s₀ : (Fin n → ℝ) → ℝ := fun τ =>
      (insert invE (Q.image (fun q => min 1 (τ q)))).max' (Finset.insert_nonempty _ _)
    let Ψ : (Fin n → ℝ) → ℝ := fun τ =>
      ∏ g ∈ A, retentionProb (canonicalDemand v) (s₀ τ) Q ∅ τ (fun _ => s₀ τ) g
    obtain ⟨⟨hΨ_meas, hΨ_bdd, hΨ_loc⟩, h_ftc, h_invE, h_inA, h_outA⟩ :=
      inclusion_mass_ftc_and_boundary n v Q A t hAQ ht1 ht2 h_persQ h_commQ
    have h_split :=
      unif_cube_threshold_max_split n Q 1 t Ψ ht1 hΨ_meas hΨ_bdd hΨ_loc
    have h_partQ : Q \ A ∪ A = Q := Finset.sdiff_union_of_subset hAQ
    have h_disjQ : Disjoint (Q \ A) A := disjoint_sdiff_self_left
    have h_sumQ :
        (∑ x ∈ Q,
          ∫ s in Set.Icc invE t,
            s ^ (Q.erase x).card *
              ∫ τ, Ψ (Function.update τ x s) ∂(unifCubeMeasure n s)) =
        (∑ x ∈ Q \ A, ∫ s in Set.Icc invE t, inclusionMass v (Q.erase x) A s) := by
      let f_slice0 : Fin n → ℝ := fun x =>
        ∫ s in Set.Icc invE t,
          s ^ (Q.erase x).card *
            ∫ τ, Ψ (Function.update τ x s) ∂(unifCubeMeasure n s)
      have h_u0 : (∑ x ∈ Q, f_slice0 x) =
          (∑ x ∈ Q \ A, f_slice0 x) + (∑ x ∈ A, f_slice0 x) := by
        rw [← Finset.sum_union h_disjQ, h_partQ]
      have h_sumA :
          (∑ x ∈ A, f_slice0 x) = 0 := by
        refine Finset.sum_eq_zero (fun x hxA => ?_)
        dsimp only [f_slice0]
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
        have h_congr :
            Set.EqOn
              (fun s : ℝ =>
                s ^ (Q.erase x).card *
                  ∫ τ, Ψ (Function.update τ x s) ∂(unifCubeMeasure n s))
              (fun _ => (0 : ℝ))
              (Set.Ioc invE t) := by
          intro s hs
          have hfn : (fun τ : Fin n → ℝ => Ψ (Function.update τ x s)) = fun _ => 0 := by
            ext τ
            exact h_inA x hxA s hs.1 τ
          dsimp only
          rw [hfn, MeasureTheory.integral_zero, mul_zero]
        rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc h_congr,
          MeasureTheory.integral_zero]
      have h_sumQA :
          (∑ x ∈ Q \ A, f_slice0 x) =
          (∑ x ∈ Q \ A, ∫ s in Set.Icc invE t, inclusionMass v (Q.erase x) A s) := by
        refine Finset.sum_congr rfl (fun x hxQA => ?_)
        dsimp only [f_slice0]
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
        exact h_outA x hxQA s hs.1 hs.2
      change (∑ x ∈ Q, f_slice0 x) = _
      rw [h_u0, h_sumQA, h_sumA, add_zero]
    change inclusionMass v Q A t = _
    rw [h_ftc]
    change t ^ Q.card * (∫ τ, Ψ τ ∂unifCubeMeasure n t) + _ = _
    rw [h_split, h_invE, h_sumQ]

  
  have h_conj3 :
      ∀ (n : ℕ) (v : ItemValuation n) (Q : Finset (Fin n)) (t : ℝ) (A : Finset (Fin n)),
        IsGSValuation v → invE ≤ t → t ≤ 1 →
          onlineSurvivalLaw v Q t A = survivalLaw v Q t A := by
    intro n v Q₀ t₀ A₀ hv ht₀1 ht₀2
    obtain ⟨_, h_acc_bdd, h_acc_mass⟩ := survival_accept_validity_and_mass_eq n v hv
    have h_acc_prem : ∀ (S B : Finset (Fin n)) (x : Fin n) (s : ℝ),
        x ∉ S → s ≤ 1 →
          0 ≤ survivalAcceptProb v x B S s ∧ survivalAcceptProb v x B S s ≤ 1 :=
      fun S B x s hxS hs => h_acc_bdd S B x s hxS hs
    obtain ⟨h5_out, h5_reg, h5_eq, h5_invE, h5_step⟩ :=
      online_dist_meas_and_last_arrival n v h_acc_prem
    let clamp : (Fin n → ℝ) → (Fin n → ℝ) := fun τ i => min 1 (max 0 (τ i))
    let onlineRun : (Fin n → ℝ) → Finset (Fin n) → Finset (Fin n) → ℝ := fun τ Q R =>
      survivalRunDistList v τ
        ((Q.sort (· ≤ ·)).mergeSort (fun a b => decide (τ a ≤ τ b)))
        ∅ (fun B => if B = ∅ then 1 else 0) R
    have h_ind :
        ∀ (k : ℕ) (Q : Finset (Fin n)), Q.card = k →
          ∀ (t : ℝ) (B : Finset (Fin n)), invE ≤ t → t ≤ 1 →
            onlineSurvivalLaw v Q t B = survivalLaw v Q t B := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro Q hk t B ht1 ht2
        by_cases hBQ : B ⊆ Q
        · have ht_pos : 0 < t := h_invE_pos.trans_le ht1
          have h_incl_eq :
              ∀ A : Finset (Fin n), A ⊆ Q →
                t ^ Q.card *
                  (∑ R ∈ Q.powerset.filter (fun R => A ⊆ R), onlineSurvivalLaw v Q t R) =
                inclusionMass v Q A t := by
            intro A hAQ
            let F_A := Q.powerset.filter (fun R => A ⊆ R)
            let Ψ_onl : (Fin n → ℝ) → ℝ := fun τ => ∑ R ∈ F_A, onlineRun (clamp τ) Q R
            have hΨ_meas : Measurable Ψ_onl :=
              Finset.measurable_sum F_A (fun R _ => (h5_reg Q R).1)
            have hΨ_bdd : ∀ τ : Fin n → ℝ, |Ψ_onl τ| ≤ 1 := by
              intro τ
              have h_nn : 0 ≤ Ψ_onl τ :=
                Finset.sum_nonneg (fun R _ => ((h5_reg Q R).2.1 τ).1)
              have h_le : Ψ_onl τ ≤ 1 := by
                calc Ψ_onl τ
                    ≤ ∑ R ∈ Q.powerset, onlineRun (clamp τ) Q R :=
                      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                        (fun R _ _ => ((h5_reg Q R).2.1 τ).1)
                  _ = 1 := (h5_reg Q ∅).2.2.1 τ
              rw [abs_of_nonneg h_nn]
              exact h_le
            have hΨ_loc : ∀ τ₁ τ₂ : Fin n → ℝ,
                (∀ q ∈ Q, τ₁ q = τ₂ q) → Ψ_onl τ₁ = Ψ_onl τ₂ :=
              fun τ₁ τ₂ hq => Finset.sum_congr rfl (fun R _ => (h5_reg Q R).2.2.2 τ₁ τ₂ hq)
            have h_int_run : ∀ {r : ℝ}, 0 < r → ∀ R : Finset (Fin n),
                Integrable (fun τ => onlineRun (clamp τ) Q R) (unifCubeMeasure n r) := by
              intro r hr R
              haveI := h_cube_prob n hr
              exact MeasureTheory.Integrable.of_mem_Icc 0 1 (h5_reg Q R).1.aemeasurable
                (Filter.Eventually.of_forall (fun τ => (h5_reg Q R).2.1 τ))
            have h_lhs_eq :
                (∑ R ∈ F_A, onlineSurvivalLaw v Q t R) =
                  ∫ τ, Ψ_onl τ ∂(unifCubeMeasure n t) := by
              have h1 : (∑ R ∈ F_A, onlineSurvivalLaw v Q t R) =
                  ∑ R ∈ F_A, ∫ τ, onlineRun (clamp τ) Q R ∂(unifCubeMeasure n t) :=
                Finset.sum_congr rfl (fun R _ => (h5_eq Q R t ht1 ht2).symm)
              rw [h1, ← MeasureTheory.integral_finset_sum F_A (fun R _ => h_int_run ht_pos R)]
            have h_split :=
              unif_cube_threshold_max_split n Q 1 t Ψ_onl ht1 hΨ_meas hΨ_bdd hΨ_loc
            have h_base :
                (∫ τ, Ψ_onl τ ∂(unifCubeMeasure n invE)) = (if A = ∅ then 1 else 0) := by
              dsimp only [Ψ_onl]
              rw [MeasureTheory.integral_finset_sum F_A (fun R _ => h_int_run h_invE_pos R)]
              have h_s : (∑ R ∈ F_A, ∫ τ, onlineRun (clamp τ) Q R ∂(unifCubeMeasure n invE)) =
                  ∑ R ∈ F_A, (if R = ∅ then (1 : ℝ) else 0) :=
                Finset.sum_congr rfl (fun R _ => h5_invE Q R)
              rw [h_s]
              by_cases hA_emp : A = ∅
              · subst hA_emp
                rw [if_pos rfl]
                have hemp_mem : (∅ : Finset (Fin n)) ∈ F_A := by
                  simp [F_A]
                rw [← Finset.add_sum_erase F_A _ hemp_mem, if_pos rfl]
                have h_rest : (∑ R ∈ F_A.erase ∅, (if R = ∅ then (1 : ℝ) else 0)) = 0 :=
                  Finset.sum_eq_zero (fun R hR => if_neg (Finset.mem_erase.mp hR).1)
                rw [h_rest, add_zero]
              · rw [if_neg hA_emp]
                refine Finset.sum_eq_zero (fun R hR => if_neg ?_)
                rintro rfl
                exact hA_emp (Finset.subset_empty.mp (Finset.mem_filter.mp hR).2)
            have h_slice :
                ∀ x ∈ Q, ∀ s : ℝ, invE < s → s ≤ t →
                  s ^ (Q.erase x).card *
                    (∫ τ, Ψ_onl (Function.update τ x s) ∂(unifCubeMeasure n s)) =
                  (if x ∈ Q \ A then inclusionMass v (Q.erase x) A s
                   else if x ∈ A ∩ canonicalDemand v Q then
                     (1 / (Real.exp 1 * s)) *
                       inclusionMass (contractVal v x) (Q.erase x) (A.erase x) s
                   else 0) := by
              intro x hxQ s hs_gt hs_let
              have hs_pos : 0 < s := h_invE_pos.trans hs_gt
              have hs_le1 : s ≤ 1 := hs_let.trans ht2
              have h_meas_upd : Measurable (fun τ : Fin n → ℝ => Function.update τ x s) := by
                refine measurable_pi_iff.mpr (fun i => ?_)
                by_cases hix : i = x
                · subst hix
                  have h_eq_fn : (fun τ : Fin n → ℝ => Function.update τ i s i) = fun _ => s := by
                    ext τ
                    exact Function.update_self i s τ
                  rw [h_eq_fn]
                  exact measurable_const
                · have h_eq_fn : (fun τ : Fin n → ℝ => Function.update τ x s i) = fun τ => τ i := by
                    ext τ
                    exact Function.update_of_ne hix s τ
                  rw [h_eq_fn]
                  exact measurable_pi_apply i
              have h_int_upd : ∀ R : Finset (Fin n),
                  Integrable (fun τ => onlineRun (clamp (Function.update τ x s)) Q R)
                    (unifCubeMeasure n s) := by
                intro R
                haveI := h_cube_prob n hs_pos
                have hm : Measurable (fun τ => onlineRun (clamp (Function.update τ x s)) Q R) :=
                  (h5_reg Q R).1.comp h_meas_upd
                exact MeasureTheory.Integrable.of_mem_Icc 0 1 hm.aemeasurable
                  (Filter.Eventually.of_forall (fun τ => (h5_reg Q R).2.1 (Function.update τ x s)))
              have h_int_sum :
                  (∫ τ, Ψ_onl (Function.update τ x s) ∂(unifCubeMeasure n s)) =
                    ∑ R ∈ F_A,
                      survivalStepDist v (Q.erase x) x s
                        (fun W => survivalLaw v (Q.erase x) s W) R := by
                dsimp only [Ψ_onl]
                rw [MeasureTheory.integral_finset_sum F_A (fun R _ => h_int_upd R)]
                refine Finset.sum_congr rfl (fun R _ => ?_)
                rw [h5_step Q R x s hxQ hs_gt hs_le1]
                have h_card_lt : (Q.erase x).card < k := by
                  rw [← hk]
                  exact Finset.card_erase_lt_of_mem hxQ
                have h_ih_eq :
                    (fun W => onlineSurvivalLaw v (Q.erase x) s W) =
                      (fun W => survivalLaw v (Q.erase x) s W) := by
                  ext W
                  exact ih (Q.erase x).card h_card_lt (Q.erase x) rfl s W hs_gt.le hs_le1
                rw [h_ih_eq]
              rw [h_int_sum]
              by_cases hxA : x ∈ A
              · have hx_not_QA : x ∉ Q \ A := fun h => (Finset.mem_sdiff.mp h).2 hxA
                rw [if_neg hx_not_QA]
                let G_Ax := (Q.erase x).powerset.filter (fun W => A.erase x ⊆ W)
                have h_bij_A :
                    (∑ R ∈ F_A,
                      survivalStepDist v (Q.erase x) x s
                        (fun W => survivalLaw v (Q.erase x) s W) R) =
                    ∑ W ∈ G_Ax,
                      survivalLaw v (Q.erase x) s W *
                        survivalAcceptProb v x W (Q.erase x) s := by
                  refine Finset.sum_bij (fun R _ => R.erase x) ?_ ?_ ?_ ?_
                  · intro R hR
                    obtain ⟨hRQ, hAR⟩ := Finset.mem_filter.mp hR
                    rw [Finset.mem_powerset] at hRQ
                    simp only [G_Ax, Finset.mem_filter, Finset.mem_powerset]
                    exact ⟨Finset.erase_subset_erase x hRQ, Finset.erase_subset_erase x hAR⟩
                  · intro R₁ hR₁ R₂ hR₂ heq
                    dsimp only at heq
                    have hx₁ : x ∈ R₁ := (Finset.mem_filter.mp hR₁).2 hxA
                    have hx₂ : x ∈ R₂ := (Finset.mem_filter.mp hR₂).2 hxA
                    rw [← Finset.insert_erase hx₁, ← Finset.insert_erase hx₂, heq]
                  · intro W hW
                    obtain ⟨hWQ, hAW⟩ := Finset.mem_filter.mp hW
                    rw [Finset.mem_powerset] at hWQ
                    have hxW : x ∉ W := fun h => Finset.notMem_erase x Q (hWQ h)
                    refine ⟨insert x W, ?_, Finset.erase_insert hxW⟩
                    simp only [F_A, Finset.mem_filter, Finset.mem_powerset]
                    refine ⟨Finset.insert_subset_iff.mpr ⟨hxQ, hWQ.trans (Finset.erase_subset x Q)⟩, ?_⟩
                    rw [← Finset.insert_erase hxA]
                    exact Finset.insert_subset_insert x hAW
                  · intro R hR
                    have hxR : x ∈ R := (Finset.mem_filter.mp hR).2 hxA
                    unfold survivalStepDist
                    rw [if_neg (not_not.mpr hxR), if_pos hxR, zero_add]
                rw [h_bij_A]
                have hinsQ : insert x (Q.erase x) = Q := Finset.insert_erase hxQ
                have hx_not_er : x ∉ Q.erase x := Finset.notMem_erase x Q
                by_cases hxD : x ∈ canonicalDemand v Q
                · have hxAD : x ∈ A ∩ canonicalDemand v Q := Finset.mem_inter.mpr ⟨hxA, hxD⟩
                  rw [if_pos hxAD]
                  have hxD' : x ∈ canonicalDemand v (insert x (Q.erase x)) := by rwa [hinsQ]
                  have h_terms :
                      (∑ W ∈ G_Ax,
                        survivalLaw v (Q.erase x) s W *
                          survivalAcceptProb v x W (Q.erase x) s) =
                      (1 / (Real.exp 1 * s)) *
                        survivalInclProb (contractVal v x) (Q.erase x) (A.erase x) s := by
                    unfold survivalInclProb
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl (fun W _ => ?_)
                    exact h_acc_mass (Q.erase x) W x s hx_not_er hs_gt hs_le1 hxD'
                  rw [h_terms]
                  unfold inclusionMass
                  ring
                · have hx_not_AD : x ∉ A ∩ canonicalDemand v Q :=
                    fun h => hxD (Finset.mem_inter.mp h).2
                  rw [if_neg hx_not_AD]
                  have h_zero_sum :
                      (∑ W ∈ G_Ax,
                        survivalLaw v (Q.erase x) s W *
                          survivalAcceptProb v x W (Q.erase x) s) = 0 := by
                    refine Finset.sum_eq_zero (fun W _ => ?_)
                    have h_acc0 : survivalAcceptProb v x W (Q.erase x) s = 0 := by
                      unfold survivalAcceptProb
                      rw [hinsQ]
                      by_cases h1 : s ≤ invE
                      · rw [if_pos h1]
                      · rw [if_neg h1, if_pos hxD]
                    rw [h_acc0, mul_zero]
                  rw [h_zero_sum, mul_zero]
              · have hxQA : x ∈ Q \ A := Finset.mem_sdiff.mpr ⟨hxQ, hxA⟩
                rw [if_pos hxQA]
                let G_A := (Q.erase x).powerset.filter (fun W => A ⊆ W)
                have h_split_FA :
                    (∑ R ∈ F_A,
                      survivalStepDist v (Q.erase x) x s
                        (fun W => survivalLaw v (Q.erase x) s W) R) =
                    (∑ R ∈ F_A.filter (fun R => x ∈ R),
                      survivalStepDist v (Q.erase x) x s
                        (fun W => survivalLaw v (Q.erase x) s W) R) +
                    (∑ R ∈ F_A.filter (fun R => x ∉ R),
                      survivalStepDist v (Q.erase x) x s
                        (fun W => survivalLaw v (Q.erase x) s W) R) :=
                  (Finset.sum_filter_add_sum_filter_not F_A (fun R => x ∈ R) _).symm
                have h_in_sum :
                    (∑ R ∈ F_A.filter (fun R => x ∈ R),
                      survivalStepDist v (Q.erase x) x s
                        (fun W => survivalLaw v (Q.erase x) s W) R) =
                    ∑ W ∈ G_A,
                      survivalLaw v (Q.erase x) s W *
                        survivalAcceptProb v x W (Q.erase x) s := by
                  refine Finset.sum_bij (fun R _ => R.erase x) ?_ ?_ ?_ ?_
                  · intro R hR
                    obtain ⟨hRFA, _⟩ := Finset.mem_filter.mp hR
                    obtain ⟨hRQ, hAR⟩ := Finset.mem_filter.mp hRFA
                    rw [Finset.mem_powerset] at hRQ
                    simp only [G_A, Finset.mem_filter, Finset.mem_powerset]
                    refine ⟨Finset.erase_subset_erase x hRQ, fun z hzA => ?_⟩
                    exact Finset.mem_erase.mpr ⟨fun hzx => hxA (hzx ▸ hzA), hAR hzA⟩
                  · intro R₁ hR₁ R₂ hR₂ heq
                    dsimp only at heq
                    have hx₁ : x ∈ R₁ := (Finset.mem_filter.mp hR₁).2
                    have hx₂ : x ∈ R₂ := (Finset.mem_filter.mp hR₂).2
                    rw [← Finset.insert_erase hx₁, ← Finset.insert_erase hx₂, heq]
                  · intro W hW
                    obtain ⟨hWQ, hAW⟩ := Finset.mem_filter.mp hW
                    rw [Finset.mem_powerset] at hWQ
                    have hxW : x ∉ W := fun h => Finset.notMem_erase x Q (hWQ h)
                    refine ⟨insert x W, ?_, Finset.erase_insert hxW⟩
                    simp only [F_A, Finset.mem_filter, Finset.mem_powerset]
                    refine ⟨⟨Finset.insert_subset_iff.mpr ⟨hxQ, hWQ.trans (Finset.erase_subset x Q)⟩,
                      hAW.trans (Finset.subset_insert x W)⟩, Finset.mem_insert_self x W⟩
                  · intro R hR
                    have hxR : x ∈ R := (Finset.mem_filter.mp hR).2
                    unfold survivalStepDist
                    rw [if_neg (not_not.mpr hxR), if_pos hxR, zero_add]
                have h_out_set : F_A.filter (fun R => x ∉ R) = G_A := by
                  ext R
                  simp only [F_A, G_A, Finset.mem_filter, Finset.mem_powerset]
                  refine ⟨fun ⟨⟨hRQ, hAR⟩, hxR⟩ => ⟨?_, hAR⟩,
                    fun ⟨hRQer, hAR⟩ => ⟨⟨hRQer.trans (Finset.erase_subset x Q), hAR⟩, ?_⟩⟩
                  · intro z hzR
                    exact Finset.mem_erase.mpr ⟨fun hzx => hxR (hzx ▸ hzR), hRQ hzR⟩
                  · exact fun hxR => Finset.notMem_erase x Q (hRQer hxR)
                have h_out_sum :
                    (∑ R ∈ F_A.filter (fun R => x ∉ R),
                      survivalStepDist v (Q.erase x) x s
                        (fun W => survivalLaw v (Q.erase x) s W) R) =
                    ∑ W ∈ G_A,
                      survivalLaw v (Q.erase x) s W *
                        (1 - survivalAcceptProb v x W (Q.erase x) s) := by
                  rw [h_out_set]
                  refine Finset.sum_congr rfl (fun W hW => ?_)
                  have hWQ : W ⊆ Q.erase x := Finset.mem_powerset.mp (Finset.mem_filter.mp hW).1
                  have hxW : x ∉ W := fun h => Finset.notMem_erase x Q (hWQ h)
                  unfold survivalStepDist
                  rw [if_pos hxW, if_neg hxW, add_zero]
                rw [h_split_FA, h_in_sum, h_out_sum, ← Finset.sum_add_distrib]
                have h_coll :
                    (∑ W ∈ G_A,
                      (survivalLaw v (Q.erase x) s W * survivalAcceptProb v x W (Q.erase x) s +
                       survivalLaw v (Q.erase x) s W * (1 - survivalAcceptProb v x W (Q.erase x) s))) =
                    survivalInclProb v (Q.erase x) A s := by
                  unfold survivalInclProb
                  refine Finset.sum_congr rfl (fun W _ => ?_)
                  ring
                rw [h_coll]
                rfl
            have h_sumQ :
                (∑ x ∈ Q,
                  ∫ s in Set.Icc invE t,
                    s ^ (Q.erase x).card *
                      ∫ τ, Ψ_onl (Function.update τ x s) ∂(unifCubeMeasure n s)) =
                (∑ x ∈ Q \ A, ∫ s in Set.Icc invE t, inclusionMass v (Q.erase x) A s) +
                (∑ x ∈ A ∩ canonicalDemand v Q,
                  ∫ s in Set.Icc invE t,
                    (1 / (Real.exp 1 * s)) *
                      inclusionMass (contractVal v x) (Q.erase x) (A.erase x) s) := by
              let f_slice : Fin n → ℝ := fun x =>
                ∫ s in Set.Icc invE t,
                  s ^ (Q.erase x).card *
                    ∫ τ, Ψ_onl (Function.update τ x s) ∂(unifCubeMeasure n s)
              have h_part1 : Q \ A ∪ A = Q := Finset.sdiff_union_of_subset hAQ
              have h_disj1 : Disjoint (Q \ A) A := disjoint_sdiff_self_left
              have h_u1 : (∑ x ∈ Q, f_slice x) =
                  (∑ x ∈ Q \ A, f_slice x) + (∑ x ∈ A, f_slice x) := by
                rw [← Finset.sum_union h_disj1, h_part1]
              have h_part2 : A \ canonicalDemand v Q ∪ (A ∩ canonicalDemand v Q) = A :=
                Finset.sdiff_union_inter A (canonicalDemand v Q)
              have h_disj2 : Disjoint (A \ canonicalDemand v Q) (A ∩ canonicalDemand v Q) :=
                Finset.disjoint_sdiff_inter A (canonicalDemand v Q)
              have h_u2 : (∑ x ∈ A, f_slice x) =
                  (∑ x ∈ A \ canonicalDemand v Q, f_slice x) +
                  (∑ x ∈ A ∩ canonicalDemand v Q, f_slice x) := by
                rw [← Finset.sum_union h_disj2, h_part2]
              have h_s1 :
                  (∑ x ∈ Q \ A, f_slice x) =
                  ∑ x ∈ Q \ A, ∫ s in Set.Icc invE t, inclusionMass v (Q.erase x) A s := by
                refine Finset.sum_congr rfl (fun x hxQA => ?_)
                have hxQ : x ∈ Q := (Finset.mem_sdiff.mp hxQA).1
                dsimp only [f_slice]
                rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
                  MeasureTheory.integral_Icc_eq_integral_Ioc]
                refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
                have hs_eq := h_slice x hxQ s hs.1 hs.2
                rw [if_pos hxQA] at hs_eq
                exact hs_eq
              have h_s2 :
                  (∑ x ∈ A \ canonicalDemand v Q, f_slice x) = 0 := by
                refine Finset.sum_eq_zero (fun x hx => ?_)
                obtain ⟨hxA, hx_notD⟩ := Finset.mem_sdiff.mp hx
                have hxQ : x ∈ Q := hAQ hxA
                have hx_notQA : x ∉ Q \ A := fun h => (Finset.mem_sdiff.mp h).2 hxA
                have hx_notAD : x ∉ A ∩ canonicalDemand v Q :=
                  fun h => hx_notD (Finset.mem_inter.mp h).2
                dsimp only [f_slice]
                rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
                have h_zero_on :
                    Set.EqOn
                      (fun s : ℝ =>
                        s ^ (Q.erase x).card *
                          ∫ τ, Ψ_onl (Function.update τ x s) ∂(unifCubeMeasure n s))
                      (fun _ => (0 : ℝ))
                      (Set.Ioc invE t) := by
                  intro s hs
                  have hs_eq := h_slice x hxQ s hs.1 hs.2
                  rw [if_neg hx_notQA, if_neg hx_notAD] at hs_eq
                  exact hs_eq
                rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc h_zero_on,
                  MeasureTheory.integral_zero]
              have h_s3 :
                  (∑ x ∈ A ∩ canonicalDemand v Q, f_slice x) =
                  ∑ x ∈ A ∩ canonicalDemand v Q,
                    ∫ s in Set.Icc invE t,
                      (1 / (Real.exp 1 * s)) *
                        inclusionMass (contractVal v x) (Q.erase x) (A.erase x) s := by
                refine Finset.sum_congr rfl (fun x hxAD => ?_)
                have hxA : x ∈ A := (Finset.mem_inter.mp hxAD).1
                have hxQ : x ∈ Q := hAQ hxA
                have hx_notQA : x ∉ Q \ A := fun h => (Finset.mem_sdiff.mp h).2 hxA
                dsimp only [f_slice]
                rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
                  MeasureTheory.integral_Icc_eq_integral_Ioc]
                refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
                have hs_eq := h_slice x hxQ s hs.1 hs.2
                rw [if_neg hx_notQA, if_pos hxAD] at hs_eq
                exact hs_eq
              change (∑ x ∈ Q, f_slice x) = _
              rw [h_u1, h_u2, h_s1, h_s2, h_s3, zero_add]
            rw [h_lhs_eq, h_split, h_base, h_sumQ, ← add_assoc, ← h_conj2 n v Q A t hv hAQ ht1 ht2]
          
          have h_sum_eq :
              ∀ A : Finset (Fin n), A ⊆ Q →
                (∑ R ∈ Q.powerset.filter (fun R => A ⊆ R), onlineSurvivalLaw v Q t R) =
                (∑ R ∈ Q.powerset.filter (fun R => A ⊆ R), survivalLaw v Q t R) := by
            intro A hAQ
            have h_pow_ne : t ^ Q.card ≠ 0 := (pow_pos ht_pos Q.card).ne'
            exact mul_left_cancel₀ h_pow_ne (h_incl_eq A hAQ)
          have h_inv :
              ∀ (d : ℕ) (C : Finset (Fin n)), C ⊆ Q → (Q \ C).card = d →
                onlineSurvivalLaw v Q t C = survivalLaw v Q t C := by
            intro d
            induction d using Nat.strong_induction_on with
            | _ d ih_d =>
              intro C hCQ hd
              let F_C := Q.powerset.filter (fun R => C ⊆ R)
              have hC_mem : C ∈ F_C :=
                Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hCQ, Finset.Subset.rfl⟩
              have h_eqC := h_sum_eq C hCQ
              rw [← Finset.add_sum_erase F_C _ hC_mem,
                ← Finset.add_sum_erase F_C _ hC_mem] at h_eqC
              have h_tail_eq :
                  (∑ R ∈ F_C.erase C, onlineSurvivalLaw v Q t R) =
                  (∑ R ∈ F_C.erase C, survivalLaw v Q t R) := by
                refine Finset.sum_congr rfl (fun R hR => ?_)
                obtain ⟨hRC_ne, hRFC⟩ := Finset.mem_erase.mp hR
                obtain ⟨hRQ_pow, hCR⟩ := Finset.mem_filter.mp hRFC
                have hRQ : R ⊆ Q := Finset.mem_powerset.mp hRQ_pow
                have h_ssub : Q \ R ⊂ Q \ C := by
                  rw [Finset.ssubset_iff_subset_ne]
                  refine ⟨Finset.sdiff_subset_sdiff Finset.Subset.rfl hCR, fun heq => hRC_ne ?_⟩
                  refine Finset.Subset.antisymm ?_ hCR
                  intro z hzR
                  by_contra hzC
                  have hzQC : z ∈ Q \ C := Finset.mem_sdiff.mpr ⟨hRQ hzR, hzC⟩
                  rw [← heq] at hzQC
                  exact (Finset.mem_sdiff.mp hzQC).2 hzR
                have h_lt : (Q \ R).card < d := by
                  rw [← hd]
                  exact Finset.card_lt_card h_ssub
                exact ih_d (Q \ R).card h_lt R hRQ rfl
              rw [h_tail_eq] at h_eqC
              exact add_right_cancel h_eqC
          exact h_inv (Q \ B).card B hBQ rfl
        · rw [h5_out Q t B hBQ]
          dsimp only [survivalLaw, genSurvivalLaw, genSurvivalLaw2]
          have h_zero_fn :
              (fun τ => retainProd (canonicalDemand v) t Q ∅ τ (fun _ => t) B) =
                fun _ => 0 := by
            ext τ
            unfold retainProd
            exact if_neg hBQ
          rw [h_zero_fn, MeasureTheory.integral_zero]
    exact h_ind Q₀.card Q₀ rfl t₀ A₀ ht₀1 ht₀2

  exact ⟨h_conj1a, h_conj1b, h_conj2, h_conj3⟩


/-- **Appendix B.3 (`sec:proof-selection`) — Pointwise Canonical-Demand Support of `survivalLaw`**:
Whenever `μ^v_{S, t}(A) > 0` (`t ∈ [1/e, 1]`), `A ⊆ D_v(T)` for some `T ⊆ S`, so `A` and all its
subsets belong to `dom v` with nonnegative values. -/
theorem survival_pointwise_safe
    {n : ℕ} (v : ItemValuation n) (S A : Finset (Fin n)) (t : ℝ)
    (hv : IsGSValuation v) (ht₀ : invE ≤ t) (ht1 : t ≤ 1)
    (hpos : 0 < survivalLaw v S t A) :
    ∃ T ⊆ S, A ⊆ canonicalDemand v T ∧ ∀ Y ⊆ A, v Y ≠ ⊥ ∧ 0 ≤ realVal v Y :=
  thm_selection_inclusion_and_matching.1 n v S A t hv ht₀ ht1 hpos

/-- **Lemma B.7 (`lem:inclusion`) — Inclusion Recursion (`eq:recursion`)**:
For any GS valuation `v`, `Q ⊆ N`, `A ⊆ Q`, and `t ∈ [1/e, 1]`, the unnormalized inclusion mass
`m^v_{Q, A}(t) = t^{|Q|} P_{R ~ μ^v_{Q, t}}[A ⊆ R]` satisfies
`m^v_{Q, A}(t) = e^{-|Q|} [A = ∅] + ∑_{x ∈ Q \ A} ∫_{1/e}^t m^v_{Q - x, A}(s) ds +
  ∑_{x ∈ A ∩ D_v(Q)} ∫_{1/e}^t (1 / (e s)) m^{v / x}_{Q - x, A - x}(s) ds`. -/
theorem lem_B_7_inclusion
    {n : ℕ} (v : ItemValuation n) (Q A : Finset (Fin n)) (t : ℝ)
    (hv : IsGSValuation v) (hAQ : A ⊆ Q) (ht₀ : invE ≤ t) (ht1 : t ≤ 1) :
    inclusionMass v Q A t =
      Real.exp (-(Q.card : ℝ)) * (if A = ∅ then 1 else 0) +
      (∑ x ∈ Q \ A, ∫ s in Set.Icc invE t, inclusionMass v (Q.erase x) A s) +
      (∑ x ∈ A ∩ canonicalDemand v Q,
        ∫ s in Set.Icc invE t,
          (1 / (Real.exp 1 * s)) *
            inclusionMass (contractVal v x) (Q.erase x) (A.erase x) s) :=
  thm_selection_inclusion_and_matching.2.2.1 n v Q A t hv hAQ ht₀ ht1

/-- **Proposition B.6 (`prop:matching`) — Distribution Matching**:
For every GS valuation `v`, subset `Q ⊆ N`, horizon `t ∈ [1/e, 1]`, and `A`, the online law
`L_{Q, t}` (`onlineSurvivalLaw v Q t`) equals the survival law `μ^v_{Q, t}` (`survivalLaw v Q t`). -/
theorem prop_B_6_matching
    {n : ℕ} (v : ItemValuation n) (Q : Finset (Fin n)) (t : ℝ) (A : Finset (Fin n))
    (hv : IsGSValuation v) (ht₀ : invE ≤ t) (ht1 : t ≤ 1) :
    onlineSurvivalLaw v Q t A = survivalLaw v Q t A :=
  thm_selection_inclusion_and_matching.2.2.2 n v Q t A hv ht₀ ht1

end

end

end GrossSubstitutesWelfare
