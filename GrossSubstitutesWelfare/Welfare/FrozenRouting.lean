import GrossSubstitutesWelfare.Defs
import GrossSubstitutesWelfare.Selection.GSSelection
import GrossSubstitutesWelfare.Welfare.EnvelopesAndBenchmarks

set_option maxHeartbeats 4000000
set_option linter.all false
set_option Elab.async true

/-!
# Section 1.1 Theorem B & Section 4 Theorem 4.1: `(3 - 2√2) / e`-Competitive Online Welfare

This file formalizes Theorem B (`thm:B`) and Section 4.2 Frozen Routing / Theorem 4.1
(`thm:welfare`) of *Gross Substitutes Welfare in Random Order*: frozen routing with bias
`λ = √2 - 1` achieves `E[∑_i v_i(A_i)] ≥ ((3 - 2√2) / e) OPT` across any number `m` of signed
gross substitutes bidders while maintaining `v_i(A_i) ≥ 0` for every bidder at every step.
-/

namespace GrossSubstitutesWelfare

open Classical MeasureTheory

noncomputable section

namespace FrozenRoutingInternal

def lam : ℝ := Real.sqrt 2 - 1

def bernProb (n : ℕ) (p : ℝ) (L : Finset (Fin n)) : ℝ :=
  p ^ L.card * (1 - p) ^ (n - L.card)

def K_sample {n : ℕ} (c : Fin n → ℝ) : Fin (n + 1) :=
  ⟨(Finset.univ.filter (fun j : Fin n => 0 ≤ c j ∧ c j < lam)).card,
    Nat.lt_succ_of_le ((Finset.card_le_univ _).trans_eq (Fintype.card_fin n))⟩

def bestBidderOpt {m : ℕ} (score : Fin m → ℝ) : Option (Fin m) :=
  if hm : (Finset.univ : Finset (Fin m)).Nonempty then
    let maxScore := (Finset.univ : Finset (Fin m)).sup' hm score
    let ties := (Finset.univ : Finset (Fin m)).filter (fun i => score i = maxScore)
    have hties : ties.Nonempty := by
      obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_mem_eq_sup' hm score
      exact ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, hmax.symm⟩⟩
    some (ties.min' hties)
  else
    none

def trainState {n m : ℕ} (F : Fin m → Finset (Fin n) → ℝ) (L : Finset (Fin n)) :
    ℕ → (Fin m → Finset (Fin n))
  | 0 => fun _ => ∅
  | t + 1 =>
      let B := trainState F L t
      if ht : t < n then
        let g : Fin n := ⟨t, ht⟩
        match bestBidderOpt (fun i : Fin m => F i (insert g (B i)) - F i (B i)) with
        | some i_star => if g ∈ L then Function.update B i_star (insert g (B i_star)) else B
        | none => B
      else B

def routeOpt {n m : ℕ} (F : Fin m → Finset (Fin n) → ℝ) (L : Finset (Fin n)) (g : Fin n) :
    Option (Fin m) :=
  let B := trainState F L g.1
  bestBidderOpt (fun i : Fin m => F i (insert g (B i)) - F i (B i))

def R_pool {n m : ℕ} (F : Fin m → Finset (Fin n) → ℝ) (L : Finset (Fin n)) (i : Fin m) :
    Finset (Fin n) :=
  (Finset.univ \ L).filter (fun g => routeOpt F L g = some i)

def poolVal {d n : ℕ} (v : ItemValuation n) (emb : Fin d ↪ Fin n) (R_i : Finset (Fin n)) :
    ItemValuation d :=
  fun T' => v ((T'.map emb) ∩ R_i)

def complEmb {n : ℕ} (L : Finset (Fin n)) (k : ℕ)
    (hcard : (Finset.univ \ L).card = n - k) : Fin (n - k) ↪ Fin n :=
  ((Finset.univ \ L).orderEmbOfFin hcard).toEmbedding

def invEmbOpt {d n : ℕ} (emb : Fin d ↪ Fin n) (y : Fin n) : Option (Fin d) :=
  if h : ∃ z : Fin d, emb z = y then some (Classical.choose h) else none

def replaySelectionSteps {d : ℕ}
    (alg : DetSelectionAlg d) (v_hat : ItemValuation d) (items : List (Fin d)) :
    (s : ℕ) → s ≤ items.length → List (Fin d) × Finset (Fin d)
  | 0, _ => ([], ∅)
  | s + 1, hs =>
      let ⟨prev, acc⟩ := replaySelectionSteps alg v_hat items s (Nat.le_of_succ_le hs)
      let y := items[s]'hs
      let dec := alg.step prev y acc (fun ⟨T, _⟩ => v_hat T)
      (prev ++ [y], if dec then insert y acc else acc)

abbrev FrozenSeed (n : ℕ) (selAlg : ∀ d : ℕ, OnlineSelectionAlg d) : Type :=
  (Fin n → ℝ) × ((k : Fin (n + 1)) → (selAlg (n - k.1)).Seed)

def frozenSeedMeasure (n : ℕ) (selAlg : ∀ d : ℕ, OnlineSelectionAlg d) :
    Measure (FrozenSeed n selAlg) :=
  (unifCubeMeasure n 1).prod (Measure.pi (fun k : Fin (n + 1) => (selAlg (n - k.1)).seedMeasure))

def frozenRoutingStep {n m : ℕ} (selAlg : ∀ d : ℕ, OnlineSelectionAlg d)
    (ω : FrozenSeed n selAlg) (prev : List (Fin n)) (x : Fin n)
    (_bundles : Fin m → Finset (Fin n))
    (oracle : Fin m → {T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → WithBot ℝ) :
    Option (Fin m) :=
  let k_fin : Fin (n + 1) := K_sample ω.1
  let k : ℕ := k_fin.1
  if hk_valid : k ≤ prev.length ∧ prev.length < n ∧ prev.Nodup ∧ x ∉ prev then
    let L : Finset (Fin n) := (prev.take k).toFinset
    have hL_nodup : (prev.take k).Nodup := hk_valid.2.2.1.take
    have hL_card : L.card = k := by
      rw [List.toFinset_card_of_nodup hL_nodup, List.length_take, min_eq_left hk_valid.1]
    have hcard : (Finset.univ \ L).card = n - k := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hL_card]
    let d : ℕ := n - k
    let emb : Fin d ↪ Fin n := complEmb L k hcard
    let v_loc : Fin m → ItemValuation n :=
      fun i T => if h : T ⊆ insert x prev.toFinset then oracle i ⟨T, h⟩ else ⊥
    let F_loc : Fin m → Finset (Fin n) → ℝ := fun i S => disposalEnvelope (v_loc i) S
    match routeOpt F_loc L x, invEmbOpt emb x with
    | some i_star, some x' =>
        let tail' : List (Fin d) := (prev.drop k).filterMap (invEmbOpt emb)
        let v_hat_loc : ItemValuation d :=
          poolVal (v_loc i_star) emb (R_pool F_loc L i_star)
        let acc' : Finset (Fin d) :=
          (replaySelectionSteps ((selAlg d).det (ω.2 k_fin)) v_hat_loc tail' tail'.length le_rfl).2
        let dec_b : Bool :=
          ((selAlg d).det (ω.2 k_fin)).step tail' x' acc' (fun ⟨T', _⟩ => v_hat_loc T')
        if dec_b then some i_star else none
    | _, _ => none
  else
    none

def frozenRoutingDet {n m : ℕ} (selAlg : ∀ d : ℕ, OnlineSelectionAlg d)
    (ω : FrozenSeed n selAlg) : DetWelfareAlg n m :=
  { step := frozenRoutingStep selAlg ω }


theorem exists_gs_selection_alg : ∀ d : ℕ,
      ∃ alg : OnlineSelectionAlg d,
        ∀ v : ItemValuation d, IsGSValuation v →
          (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin d)) (k : ℕ) (hk : k ≤ d),
            let st := runDetSelectionSteps (alg.det ω) v π k hk
            v st.2 ≠ ⊥ ∧ ((0 : ℝ) : WithBot ℝ) ≤ v st.2) ∧
          (((invE * optVal v : ℝ) : WithBot ℝ) ≤ expectedSelectionVal alg v) := by
  intro d
  obtain ⟨alg, halg⟩ := thm_A d
  exact ⟨alg, fun v hv => ⟨(halg v hv).2.1, (halg v hv).2.2⟩⟩

theorem gs_disposal_and_pool_val : ∀ (n : ℕ),
      (∀ (v : ItemValuation n), IsGSValuation v →
        disposalEnvelope v ∅ = 0 ∧
        (∀ S : Finset (Fin n), 0 ≤ disposalEnvelope v S) ∧
        (∀ S T : Finset (Fin n), S ⊆ T → disposalEnvelope v S ≤ disposalEnvelope v T) ∧
        IsSubmodularReal (disposalEnvelope v) ∧
        (∀ (d : ℕ) (emb : Fin d ↪ Fin n) (R_i : Finset (Fin n)),
          IsGSValuation (poolVal v emb R_i) ∧
          (R_i ⊆ Finset.univ.map emb → optVal (poolVal v emb R_i) = disposalEnvelope v R_i))) ∧
      (∀ (m : ℕ) (v_prof : Fin m → ItemValuation n),
        (∀ i : Fin m, IsGSValuation (v_prof i)) →
        ∃ X_star : Fin m → Finset (Fin n),
          IsAllocOf Finset.univ X_star ∧
          optWelfare v_prof = ∑ i : Fin m, disposalEnvelope (v_prof i) (X_star i)) :=
by
  have coe_unbotD : ∀ {z : WithBot ℝ}, z ≠ ⊥ → ((z.unbotD 0 : ℝ) : WithBot ℝ) = z := by
    intro z hz
    cases z with
    | bot => exact absurd rfl hz
    | coe r => simp [WithBot.unbotD_coe]
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
  intro n
  refine ⟨?_, ?_⟩
  · intro v hv
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
    have h_submod : IsSubmodularReal (disposalEnvelope v) := by
      refine ⟨h_emp, ?_⟩
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
    refine ⟨h_emp, h_nn, h_mono, h_submod, ?_⟩
    intro d emb R_i
    let φ : Finset (Fin d) → Finset (Fin n) := fun T' => (T'.map emb) ∩ R_i
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp [poolVal, hv.1]
    · intro X Y hX hY x hxXY
      obtain ⟨hxX, hxY⟩ := Finset.mem_sdiff.mp hxXY
      by_cases hxR : emb x ∈ R_i
      · have hxφ : emb x ∈ φ X \ φ Y := by
          simp only [φ, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_map, emb.injective.eq_iff]
          exact ⟨⟨⟨x, hxX, rfl⟩, hxR⟩, fun ⟨⟨z, hzY, hzeq⟩, _⟩ => hxY (hzeq ▸ hzY)⟩
        have hex := hv.2 (φ X) (φ Y) hX hY (emb x) hxφ
        rw [le_max_iff] at hex ⊢
        rcases hex with htr | hsw
        · left
          have he1 : (φ X).erase (emb x) = φ (X.erase x) := by
            ext g; simp only [φ, Finset.mem_erase, Finset.mem_inter, Finset.mem_map]
            constructor
            · rintro ⟨hne, ⟨z, hzX, rfl⟩, hgR⟩
              exact ⟨⟨z, ⟨fun hzx => hne (congrArg emb hzx), hzX⟩, rfl⟩, hgR⟩
            · rintro ⟨⟨z, ⟨hzx, hzX⟩, rfl⟩, hgR⟩
              exact ⟨emb.injective.ne hzx, ⟨z, hzX, rfl⟩, hgR⟩
          have he2 : insert (emb x) (φ Y) = φ (insert x Y) := by
            ext g; simp only [φ, Finset.mem_insert, Finset.mem_inter, Finset.mem_map]
            constructor
            · rintro (rfl | ⟨⟨z, hzY, rfl⟩, hgR⟩)
              · exact ⟨⟨x, Or.inl rfl, rfl⟩, hxR⟩
              · exact ⟨⟨z, Or.inr hzY, rfl⟩, hgR⟩
            · rintro ⟨⟨z, rfl | hzY, rfl⟩, hgR⟩
              · exact Or.inl rfl
              · exact Or.inr ⟨⟨z, hzY, rfl⟩, hgR⟩
          simpa only [poolVal, φ, he1, he2] using htr
        · right
          have hne_sum : v (φ X) + v (φ Y) ≠ ⊥ := by
            cases h1 : v (φ X) with
            | bot => exact absurd h1 hX
            | coe r1 =>
              cases h2 : v (φ Y) with
              | bot => exact absurd h2 hY
              | coe r2 => rw [← WithBot.coe_add]; exact WithBot.coe_ne_bot
          have hne_sdiff : (φ Y \ φ X).Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro hemp; rw [hemp, Finset.sup_empty, le_bot_iff] at hsw; exact hne_sum hsw
          obtain ⟨gy, hgy, hsup⟩ := Finset.exists_mem_eq_sup (φ Y \ φ X) hne_sdiff
            (fun y => v (insert y ((φ X).erase (emb x))) + v ((insert (emb x) (φ Y)).erase y))
          rw [hsup] at hsw
          obtain ⟨hgyY, hgyX⟩ := Finset.mem_sdiff.mp hgy
          have hgy_inter := Finset.mem_inter.mp hgyY
          obtain ⟨y, hyY, rfl⟩ := Finset.mem_map.mp hgy_inter.1
          have hyR : emb y ∈ R_i := hgy_inter.2
          have hy_notX : y ∉ X :=
            fun hyX => hgyX (Finset.mem_inter.mpr ⟨Finset.mem_map_of_mem emb hyX, hyR⟩)
          have hyYX : y ∈ Y \ X := Finset.mem_sdiff.mpr ⟨hyY, hy_notX⟩
          have hs1 : insert (emb y) ((φ X).erase (emb x)) = φ (insert y (X.erase x)) := by
            ext g; simp only [φ, Finset.mem_insert, Finset.mem_erase, Finset.mem_inter, Finset.mem_map]
            constructor
            · rintro (rfl | ⟨hne, ⟨z, hzX, rfl⟩, hgR⟩)
              · exact ⟨⟨y, Or.inl rfl, rfl⟩, hyR⟩
              · exact ⟨⟨z, Or.inr ⟨fun hzx => hne (congrArg emb hzx), hzX⟩, rfl⟩, hgR⟩
            · rintro ⟨⟨z, rfl | ⟨hzx, hzX⟩, rfl⟩, hgR⟩
              · exact Or.inl rfl
              · exact Or.inr ⟨emb.injective.ne hzx, ⟨z, hzX, rfl⟩, hgR⟩
          have hs2 : (insert (emb x) (φ Y)).erase (emb y) = φ ((insert x Y).erase y) := by
            ext g; simp only [φ, Finset.mem_erase, Finset.mem_insert, Finset.mem_inter, Finset.mem_map]
            constructor
            · rintro ⟨hne, (rfl | ⟨⟨z, hzY, rfl⟩, hgR⟩)⟩
              · exact ⟨⟨x, ⟨emb.injective.ne_iff.mp hne, Or.inl rfl⟩, rfl⟩, hxR⟩
              · exact ⟨⟨z, ⟨emb.injective.ne_iff.mp hne, Or.inr hzY⟩, rfl⟩, hgR⟩
            · rintro ⟨⟨z, ⟨hzy, rfl | hzY⟩, rfl⟩, hgR⟩
              · exact ⟨emb.injective.ne hzy, Or.inl rfl⟩
              · exact ⟨emb.injective.ne hzy, Or.inr ⟨⟨z, hzY, rfl⟩, hgR⟩⟩
          refine le_trans ?_ (Finset.le_sup (f := fun z => poolVal v emb R_i (insert z (X.erase x)) +
            poolVal v emb R_i ((insert x Y).erase z)) hyYX)
          simpa only [poolVal, φ, hs1, hs2] using hsw
      · apply le_max_of_le_left
        have he1 : φ (X.erase x) = φ X := by
          ext g; simp only [φ, Finset.mem_inter, Finset.mem_map, Finset.mem_erase]
          constructor
          · rintro ⟨⟨z, ⟨_, hzX⟩, rfl⟩, hgR⟩; exact ⟨⟨z, hzX, rfl⟩, hgR⟩
          · rintro ⟨⟨z, hzX, rfl⟩, hgR⟩
            exact ⟨⟨z, ⟨fun hzx => hxR (congrArg emb hzx ▸ hgR), hzX⟩, rfl⟩, hgR⟩
        have he2 : φ (insert x Y) = φ Y := by
          ext g; simp only [φ, Finset.mem_inter, Finset.mem_map, Finset.mem_insert]
          constructor
          · rintro ⟨⟨z, rfl | hzY, rfl⟩, hgR⟩
            · exact absurd hgR hxR
            · exact ⟨⟨z, hzY, rfl⟩, hgR⟩
          · rintro ⟨⟨z, hzY, rfl⟩, hgR⟩; exact ⟨⟨z, Or.inr hzY, rfl⟩, hgR⟩
        simp only [poolVal, φ, he1, he2, le_refl]
    · intro hR_sub
      have hsup : (Finset.univ : Finset (Finset (Fin d))).sup (poolVal v emb R_i) =
          R_i.powerset.sup v := by
        apply le_antisymm
        · refine Finset.sup_le (fun T' _ => ?_)
          have hmem : φ T' ∈ R_i.powerset := Finset.mem_powerset.mpr Finset.inter_subset_right
          exact Finset.le_sup (f := v) hmem
        · refine Finset.sup_le (fun U hU => ?_)
          have hUR : U ⊆ R_i := Finset.mem_powerset.mp hU
          let T' : Finset (Fin d) := Finset.univ.filter (fun z => emb z ∈ U)
          have hφT : φ T' = U := by
            ext g
            simp only [φ, T', Finset.mem_inter, Finset.mem_map, Finset.mem_filter,
              Finset.mem_univ, true_and]
            constructor
            · rintro ⟨⟨z, hzU, rfl⟩, _⟩; exact hzU
            · intro hgU
              obtain ⟨z, _, rfl⟩ := Finset.mem_map.mp (hR_sub (hUR hgU))
              exact ⟨⟨z, hgU, rfl⟩, hUR hgU⟩
          calc v U = poolVal v emb R_i T' := by simp [poolVal, φ, hφT]
            _ ≤ (Finset.univ : Finset (Finset (Fin d))).sup (poolVal v emb R_i) :=
                Finset.le_sup (Finset.mem_univ T')
      rw [optVal, disposalEnvelope, hsup]
  · intro m v_prof hv
    let Aset : Finset (Fin m → Finset (Fin n)) :=
      (Finset.univ : Finset (Fin m → Finset (Fin n))).filter (fun X => IsAllocOf Finset.univ X)
    let X0 : Fin m → Finset (Fin n) := fun _ => ∅
    have hX0_alloc : IsAllocOf Finset.univ X0 :=
      ⟨fun _ => Finset.empty_subset Finset.univ, fun _ _ _ => Finset.disjoint_empty_left ∅⟩
    have hA_ne : Aset.Nonempty :=
      ⟨X0, Finset.mem_filter.mpr ⟨Finset.mem_univ X0, hX0_alloc⟩⟩
    let w : Fin m → ItemValuation n :=
      fun i S => ((disposalEnvelope (v_prof i) S : ℝ) : WithBot ℝ)
    obtain ⟨X_star, hX_mem, hX_sup⟩ := Finset.exists_mem_eq_sup Aset hA_ne (allocWelfare w)
    have hX_alloc : IsAllocOf Finset.univ X_star := (Finset.mem_filter.mp hX_mem).2
    have h_w_coe : allocWelfare w X_star =
        ((∑ i : Fin m, disposalEnvelope (v_prof i) (X_star i) : ℝ) : WithBot ℝ) := by
      dsimp only [allocWelfare, w]
      exact (WithBot.coe_sum Finset.univ (fun i : Fin m => disposalEnvelope (v_prof i) (X_star i))).symm
    have h_sup_eq : Aset.sup (allocWelfare v_prof) = Aset.sup (allocWelfare w) := by
      refine le_antisymm ?_ ?_
      · refine Finset.sup_le (fun X hX => ?_)
        have h_le : allocWelfare v_prof X ≤ allocWelfare w X := by
          dsimp only [allocWelfare, w]
          refine Finset.sum_le_sum (fun i _ => ?_)
          exact (env_spec (v_prof i) (hv i) (X i)).2.1 (X i) Finset.Subset.rfl
        exact h_le.trans (Finset.le_sup hX)
      · rw [hX_sup]
        have h_ex : ∀ i : Fin m, ∃ Y_i ⊆ X_star i, v_prof i Y_i = w i (X_star i) := by
          intro i
          obtain ⟨Y_i, hYX, hvY, _⟩ := (env_spec (v_prof i) (hv i) (X_star i)).2.2
          exact ⟨Y_i, hYX, hvY⟩
        let Y : Fin m → Finset (Fin n) := fun i => Classical.choose (h_ex i)
        have hY_sub : ∀ i : Fin m, Y i ⊆ X_star i :=
          fun i => (Classical.choose_spec (h_ex i)).1
        have hY_val : ∀ i : Fin m, v_prof i (Y i) = w i (X_star i) :=
          fun i => (Classical.choose_spec (h_ex i)).2
        have hY_alloc : IsAllocOf Finset.univ Y := by
          refine ⟨fun i => Finset.subset_univ _, fun i j hij => ?_⟩
          exact Disjoint.mono (hY_sub i) (hY_sub j) (hX_alloc.2 i j hij)
        have hY_mem : Y ∈ Aset := Finset.mem_filter.mpr ⟨Finset.mem_univ Y, hY_alloc⟩
        have h_eq_w : allocWelfare w X_star = allocWelfare v_prof Y := by
          dsimp only [allocWelfare]
          exact Finset.sum_congr rfl (fun i _ => (hY_val i).symm)
        rw [h_eq_w]
        exact Finset.le_sup hY_mem
    have h_opt_coe : Aset.sup (allocWelfare v_prof) =
        ((∑ i : Fin m, disposalEnvelope (v_prof i) (X_star i) : ℝ) : WithBot ℝ) := by
      rw [h_sup_eq, hX_sup, h_w_coe]
    have h_opt : optWelfare v_prof = ∑ i : Fin m, disposalEnvelope (v_prof i) (X_star i) := by
      have h_unbot := congrArg (WithBot.unbotD 0) h_opt_coe
      simpa only [optWelfare, optWelfareOn, Aset, WithBot.unbotD_coe] using h_unbot
    exact ⟨X_star, hX_alloc, h_opt⟩

theorem bernoulli_routing_pool_bound : ∀ (n m : ℕ) (F : Fin m → Finset (Fin n) → ℝ) (X_star : Fin m → Finset (Fin n)),
      (∀ i : Fin m,
        (∀ S T : Finset (Fin n), S ⊆ T → F i S ≤ F i T) ∧
        IsSubmodularReal (F i)) →
      IsAllocOf Finset.univ X_star →
      (3 - 2 * Real.sqrt 2) * (∑ i : Fin m, F i (X_star i)) ≤
        ∑ L : Finset (Fin n), bernProb n lam L * (∑ i : Fin m, F i (R_pool F L i)) :=
by
  intro n m F X_star hF hX_alloc
  by_cases hm : (Finset.univ : Finset (Fin m)).Nonempty
  swap
  · have hempty : (Finset.univ : Finset (Fin m)) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hm
    simp [hempty]
  
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hlam_pos : 0 < lam := by
    have hgt1 : 1 < Real.sqrt 2 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    unfold lam; linarith
  have hlam_lt1 : lam < 1 := by
    have hlt2 : Real.sqrt 2 < 2 := by
      have h4 : (2 : ℝ) = Real.sqrt 4 := by norm_num
      rw [h4]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    unfold lam; linarith
  have hlam_alg : (1 - lam) * lam = (3 - 2 * Real.sqrt 2) * (1 + lam) := by
    unfold lam; nlinarith [hsq]
  have hbern_nonneg : ∀ L : Finset (Fin n), 0 ≤ bernProb n lam L := by
    intro L
    exact mul_nonneg (pow_nonneg hlam_pos.le _) (pow_nonneg (by linarith) _)
  have hbern_sum : ∑ L : Finset (Fin n), bernProb n lam L = 1 := by
    have hpow : ∀ S : Finset (Fin n),
        ∑ t ∈ S.powerset, lam ^ t.card * (1 - lam) ^ (S.card - t.card) = 1 := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.sum_powerset_insert ha, ← Finset.sum_add_distrib]
        have hcongr : ∑ t ∈ s.powerset,
            (lam ^ t.card * (1 - lam) ^ ((insert a s).card - t.card) +
             lam ^ (insert a t).card * (1 - lam) ^ ((insert a s).card - (insert a t).card)) =
            ∑ t ∈ s.powerset, lam ^ t.card * (1 - lam) ^ (s.card - t.card) := by
          refine Finset.sum_congr rfl (fun t ht => ?_)
          have hts : t ⊆ s := Finset.mem_powerset.mp ht
          have hat : a ∉ t := fun h => ha (hts h)
          have hle : t.card ≤ s.card := Finset.card_le_card hts
          rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hat]
          have hsub1 : s.card + 1 - t.card = (s.card - t.card) + 1 := by omega
          have hsub2 : s.card + 1 - (t.card + 1) = s.card - t.card := by omega
          rw [hsub1, hsub2, pow_succ, pow_succ]
          ring
        rw [hcongr, ih]
    have huniv := hpow Finset.univ
    rw [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at huniv
    exact huniv
  have hbern_coin : ∀ (g : Fin n) (H : Finset (Fin n) → ℝ),
      (∀ S : Finset (Fin n), g ∉ S → H (insert g S) = H S) →
      (∑ L : Finset (Fin n), bernProb n lam L * (if g ∈ L then H L else 0) =
        lam * ∑ L : Finset (Fin n), bernProb n lam L * H L) ∧
      (∑ L : Finset (Fin n), bernProb n lam L * (if g ∉ L then H L else 0) =
        (1 - lam) * ∑ L : Finset (Fin n), bernProb n lam L * H L) := by
    intro g H hH
    let U0 := (Finset.univ : Finset (Finset (Fin n))).filter (fun S => g ∉ S)
    let U1 := (Finset.univ : Finset (Finset (Fin n))).filter (fun L => g ∈ L)
    have hU_union : U0 ∪ U1 = Finset.univ := by
      ext L; simp only [U0, U1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
    have hU_disj : Disjoint U0 U1 := by
      rw [Finset.disjoint_filter]; intro L _ hg0 hg1; exact hg0 hg1
    have hU1_img : U1 = U0.image (insert g) := by
      ext L; simp only [U1, U0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      refine ⟨fun hgL => ⟨L.erase g, Finset.notMem_erase g L, Finset.insert_erase hgL⟩, ?_⟩
      rintro ⟨S, _, rfl⟩; exact Finset.mem_insert_self g S
    have hinj : Set.InjOn (insert g) (U0 : Set (Finset (Fin n))) := by
      intro S1 hS1 S2 hS2 heq
      have hg1 : g ∉ S1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hS1)).2
      have hg2 : g ∉ S2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hS2)).2
      have := congrArg (fun X => X.erase g) heq
      simpa [Finset.erase_insert hg1, Finset.erase_insert hg2] using this
    let w : Finset (Fin n) → ℝ := fun S => lam ^ S.card * (1 - lam) ^ (n - 1 - S.card)
    have hw_card : ∀ S ∈ U0, S.card + 1 ≤ n := by
      intro S hS
      have hgS : g ∉ S := (Finset.mem_filter.mp hS).2
      have hc := Finset.card_le_univ (insert g S)
      rw [Finset.card_insert_of_notMem hgS, Fintype.card_fin] at hc
      exact hc
    have hw1 : ∀ S ∈ U0, bernProb n lam (insert g S) = lam * w S := by
      intro S hS
      have hgS : g ∉ S := (Finset.mem_filter.mp hS).2
      have hc := hw_card S hS
      have hsub : n - (S.card + 1) = n - 1 - S.card := by omega
      simp only [bernProb, w, Finset.card_insert_of_notMem hgS, hsub, pow_succ']
      ring
    have hw0 : ∀ S ∈ U0, bernProb n lam S = (1 - lam) * w S := by
      intro S hS
      have hc := hw_card S hS
      have hsub : n - S.card = (n - 1 - S.card) + 1 := by omega
      simp only [bernProb, w, hsub, pow_succ']
      ring
    have hsum_all : (∑ L : Finset (Fin n), bernProb n lam L * H L) = ∑ S ∈ U0, w S * H S := by
      rw [← hU_union, Finset.sum_union hU_disj, hU1_img, Finset.sum_image hinj, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun S hS => ?_)
      have hgS : g ∉ S := (Finset.mem_filter.mp hS).2
      rw [hH S hgS, hw0 S hS, hw1 S hS]
      ring
    refine ⟨?_, ?_⟩
    · simp only [mul_ite, mul_zero, ← Finset.sum_filter]
      change ∑ L ∈ U1, bernProb n lam L * H L = _
      rw [hU1_img, Finset.sum_image hinj, hsum_all, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun S hS => ?_)
      rw [hH S (Finset.mem_filter.mp hS).2, hw1 S hS, mul_assoc]
    · simp only [mul_ite, mul_zero, ← Finset.sum_filter]
      change ∑ L ∈ U0, bernProb n lam L * H L = _
      rw [hsum_all, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun S hS => ?_)
      rw [hw0 S hS, mul_assoc]
  
  have h_best : ∀ score : Fin m → ℝ,
      ∃ i_star : Fin m, bestBidderOpt score = some i_star ∧ ∀ j : Fin m, score j ≤ score i_star := by
    intro score
    dsimp [bestBidderOpt]
    rw [dif_pos hm]
    refine ⟨_, rfl, fun j => ?_⟩
    have hties : ((Finset.univ : Finset (Fin m)).filter
        (fun i => score i = (Finset.univ : Finset (Fin m)).sup' hm score)).Nonempty := by
      obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_mem_eq_sup' hm score
      exact ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, hmax.symm⟩⟩
    have hmem := Finset.min'_mem _ hties
    rw [(Finset.mem_filter.mp hmem).2]
    exact Finset.le_sup' score (Finset.mem_univ j)
  let r : Finset (Fin n) → Fin n → Fin m := fun L g =>
    Classical.choose (h_best (fun i => F i (insert g (trainState F L g.1 i)) - F i (trainState F L g.1 i)))
  have hr_opt : ∀ (L : Finset (Fin n)) (g : Fin n), routeOpt F L g = some (r L g) := fun L g =>
    (Classical.choose_spec (h_best (fun i => F i (insert g (trainState F L g.1 i)) - F i (trainState F L g.1 i)))).1
  have hr_max : ∀ (L : Finset (Fin n)) (g : Fin n) (j : Fin m),
      F j (insert g (trainState F L g.1 j)) - F j (trainState F L g.1 j) ≤
        F (r L g) (insert g (trainState F L g.1 (r L g))) - F (r L g) (trainState F L g.1 (r L g)) :=
    fun L g =>
      (Classical.choose_spec (h_best (fun i => F i (insert g (trainState F L g.1 i)) - F i (trainState F L g.1 i)))).2
  have htrain_step : ∀ (L : Finset (Fin n)) (t : ℕ) (ht : t < n),
      let g : Fin n := ⟨t, ht⟩
      trainState F L (t + 1) =
        if g ∈ L then Function.update (trainState F L t) (r L g) (insert g (trainState F L t (r L g)))
        else trainState F L t := by
    intro L t ht
    dsimp only [trainState]
    rw [dif_pos ht]
    have hroute : bestBidderOpt (fun i : Fin m =>
        F i (insert ⟨t, ht⟩ (trainState F L t i)) - F i (trainState F L t i)) =
        some (r L ⟨t, ht⟩) := hr_opt L ⟨t, ht⟩
    rw [hroute]
  have htrain_congr : ∀ (t : ℕ) (L₁ L₂ : Finset (Fin n)),
      (∀ h : Fin n, h.1 < t → (h ∈ L₁ ↔ h ∈ L₂)) →
      trainState F L₁ t = trainState F L₂ t := by
    intro t
    induction t with
    | zero => intros; rfl
    | succ t ih =>
      intro L₁ L₂ hagree
      have hB : trainState F L₁ t = trainState F L₂ t :=
        ih L₁ L₂ (fun h hh => hagree h (Nat.lt_succ_of_lt hh))
      by_cases ht : t < n
      · rw [htrain_step L₁ t ht, htrain_step L₂ t ht]
        have hr_eq : r L₁ ⟨t, ht⟩ = r L₂ ⟨t, ht⟩ := by
          have hro : routeOpt F L₁ ⟨t, ht⟩ = routeOpt F L₂ ⟨t, ht⟩ := by
            dsimp [routeOpt]; rw [hB]
          exact Option.some.inj ((hr_opt L₁ ⟨t, ht⟩).symm.trans (hro.trans (hr_opt L₂ ⟨t, ht⟩)))
        have hmem : (⟨t, ht⟩ : Fin n) ∈ L₁ ↔ (⟨t, ht⟩ : Fin n) ∈ L₂ :=
          hagree ⟨t, ht⟩ (Nat.lt_succ_self t)
        rw [hB, hr_eq]
        by_cases hg : (⟨t, ht⟩ : Fin n) ∈ L₁
        · rw [if_pos hg, if_pos (hmem.mp hg)]
        · rw [if_neg hg, if_neg (fun h2 => hg (hmem.mpr h2))]
      · dsimp only [trainState]
        rw [dif_neg ht, dif_neg ht, hB]
  have hr_congr : ∀ (L₁ L₂ : Finset (Fin n)) (g : Fin n),
      (∀ h : Fin n, h.1 < g.1 → (h ∈ L₁ ↔ h ∈ L₂)) → r L₁ g = r L₂ g := by
    intro L₁ L₂ g hagree
    have hB := htrain_congr g.1 L₁ L₂ hagree
    have hro : routeOpt F L₁ g = routeOpt F L₂ g := by dsimp [routeOpt]; rw [hB]
    exact Option.some.inj ((hr_opt L₁ g).symm.trans (hro.trans (hr_opt L₂ g)))
  let prefFilter : Finset (Fin n) → Finset (Fin n) → ℕ → Fin m → Finset (Fin n) :=
    fun S L t i => S.filter (fun h : Fin n => h.1 < t ∧ r L h = i)
  have hpref_step : ∀ (S L : Finset (Fin n)) (t : ℕ) (ht : t < n),
      let g : Fin n := ⟨t, ht⟩
      prefFilter S L (t + 1) =
        if g ∈ S then Function.update (prefFilter S L t) (r L g) (insert g (prefFilter S L t (r L g)))
        else prefFilter S L t := by
    intro S L t ht
    let g : Fin n := ⟨t, ht⟩
    funext i
    ext h
    have hlt_iff : h.1 < t + 1 ↔ h.1 < t ∨ h = g := by
      rw [Nat.lt_succ_iff_lt_or_eq]
      refine or_congr_right ⟨fun heq => Fin.ext heq, fun heq => by subst heq; rfl⟩
    by_cases hgS : g ∈ S
    · rw [if_pos hgS]
      by_cases hi : i = r L g
      · subst hi
        rw [Function.update_self]
        simp only [prefFilter, Finset.mem_filter, Finset.mem_insert, hlt_iff]
        constructor
        · rintro ⟨hhS, hhlt | rfl, hhr⟩
          · exact Or.inr ⟨hhS, hhlt, hhr⟩
          · exact Or.inl rfl
        · rintro (rfl | ⟨hhS, hhlt, hhr⟩)
          · exact ⟨hgS, Or.inr rfl, rfl⟩
          · exact ⟨hhS, Or.inl hhlt, hhr⟩
      · rw [Function.update_of_ne hi]
        simp only [prefFilter, Finset.mem_filter, hlt_iff]
        constructor
        · rintro ⟨hhS, hhlt | rfl, hhr⟩
          · exact ⟨hhS, hhlt, hhr⟩
          · exact absurd hhr.symm hi
        · rintro ⟨hhS, hhlt, hhr⟩
          exact ⟨hhS, Or.inl hhlt, hhr⟩
    · rw [if_neg hgS]
      simp only [prefFilter, Finset.mem_filter, hlt_iff]
      constructor
      · rintro ⟨hhS, hhlt | rfl, hhr⟩
        · exact ⟨hhS, hhlt, hhr⟩
        · exact absurd hhS hgS
      · rintro ⟨hhS, hhlt, hhr⟩
        exact ⟨hhS, Or.inl hhlt, hhr⟩
  have htrain_eq_pref : ∀ (t : ℕ) (L : Finset (Fin n)), trainState F L t = prefFilter L L t := by
    intro t
    induction t with
    | zero =>
      intro L; funext i; ext h; simp [trainState, prefFilter]
    | succ t ih =>
      intro L
      by_cases ht : t < n
      · rw [htrain_step L t ht, hpref_step L L t ht, ih L]
      · dsimp only [trainState]
        rw [dif_neg ht, ih L]
        funext i; ext h
        simp only [prefFilter, Finset.mem_filter]
        have hh1 : h.1 < t := lt_of_lt_of_le h.isLt (Nat.le_of_not_lt ht)
        have hh2 : h.1 < t + 1 := Nat.lt_succ_of_lt hh1
        tauto
  have hpref_telescope : ∀ (S L : Finset (Fin n)),
      ∑ i : Fin m, F i (prefFilter S L n i) =
        ∑ g : Fin n,
          if g ∈ S then
            F (r L g) (insert g (prefFilter S L g.1 (r L g))) -
              F (r L g) (prefFilter S L g.1 (r L g))
          else 0 := by
    intro S L
    let Φ : ℕ → ℝ := fun t => ∑ i : Fin m, F i (prefFilter S L t i)
    have hΦ0 : Φ 0 = 0 := by
      dsimp only [Φ]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have hempty_i : prefFilter S L 0 i = ∅ := by ext h; simp [prefFilter]
      rw [hempty_i, (hF i).2.1]
    have hΦ_diff : ∀ (t : ℕ) (ht : t < n),
        let g : Fin n := ⟨t, ht⟩
        Φ (t + 1) - Φ t =
          if g ∈ S then
            F (r L g) (insert g (prefFilter S L g.1 (r L g))) -
              F (r L g) (prefFilter S L g.1 (r L g))
          else 0 := by
      intro t ht
      let g : Fin n := ⟨t, ht⟩
      dsimp only [Φ]
      rw [hpref_step S L t ht]
      by_cases hgS : g ∈ S
      · rw [if_pos hgS, if_pos hgS, ← Finset.sum_sub_distrib]
        rw [Finset.sum_eq_single (r L g) (fun i _ hi => by rw [Function.update_of_ne hi, sub_self])
          (fun hnot => absurd (Finset.mem_univ _) hnot)]
        rw [Function.update_self]
      · rw [if_neg hgS, if_neg hgS, sub_self]
    calc ∑ i : Fin m, F i (prefFilter S L n i)
        = Φ n - Φ 0 := by rw [hΦ0, sub_zero]
      _ = ∑ t ∈ Finset.range n, (Φ (t + 1) - Φ t) := (Finset.sum_range_sub Φ n).symm
      _ = ∑ t ∈ Finset.range n,
            if ht : t < n then
              (if (⟨t, ht⟩ : Fin n) ∈ S then
                F (r L ⟨t, ht⟩) (insert ⟨t, ht⟩ (prefFilter S L (⟨t, ht⟩ : Fin n).1 (r L ⟨t, ht⟩))) -
                  F (r L ⟨t, ht⟩) (prefFilter S L (⟨t, ht⟩ : Fin n).1 (r L ⟨t, ht⟩))
               else 0)
            else 0 := by
          refine Finset.sum_congr rfl (fun t ht_mem => ?_)
          have ht : t < n := Finset.mem_range.mp ht_mem
          rw [dif_pos ht]
          exact hΦ_diff t ht
      _ = ∑ g : Fin n,
            if g ∈ S then
              F (r L g) (insert g (prefFilter S L g.1 (r L g))) -
                F (r L g) (prefFilter S L g.1 (r L g))
            else 0 :=
          (Finset.sum_fin_eq_sum_range (fun g : Fin n =>
            if g ∈ S then
              F (r L g) (insert g (prefFilter S L g.1 (r L g))) -
                F (r L g) (prefFilter S L g.1 (r L g))
            else 0)).symm
  
  let d : Finset (Fin n) → Fin n → ℝ := fun L g =>
    F (r L g) (insert g (trainState F L g.1 (r L g))) - F (r L g) (trainState F L g.1 (r L g))
  let phiR : Finset (Fin n) → Fin n → ℝ := fun L g =>
    F (r L g) (insert g (prefFilter (Finset.univ \ L) L g.1 (r L g))) -
      F (r L g) (prefFilter (Finset.univ \ L) L g.1 (r L g))
  have hd_indep : ∀ (g : Fin n) (S : Finset (Fin n)), g ∉ S → d (insert g S) g = d S g := by
    intro g S _
    have hagree : ∀ h : Fin n, h.1 < g.1 → (h ∈ insert g S ↔ h ∈ S) := by
      intro h hh
      have hne : h ≠ g := fun heq => by subst heq; omega
      simp [hne]
    have hB := htrain_congr g.1 (insert g S) S hagree
    have hr_eq := hr_congr (insert g S) S g hagree
    dsimp only [d]
    rw [hB, hr_eq]
  have hphiR_indep : ∀ (g : Fin n) (S : Finset (Fin n)), g ∉ S → phiR (insert g S) g = phiR S g := by
    intro g S _
    have hagree : ∀ h : Fin n, h.1 < g.1 → (h ∈ insert g S ↔ h ∈ S) := by
      intro h hh
      have hne : h ≠ g := fun heq => by subst heq; omega
      simp [hne]
    have hr_eq := hr_congr (insert g S) S g hagree
    have hpref_eq : ∀ i : Fin m,
        prefFilter (Finset.univ \ insert g S) (insert g S) g.1 i =
          prefFilter (Finset.univ \ S) S g.1 i := by
      intro i; ext h
      simp only [prefFilter, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hnot, hhlt, hhr⟩
        have hmem_iff := hagree h hhlt
        have hr_h : r (insert g S) h = r S h :=
          hr_congr (insert g S) S h (fun u hu => hagree u (lt_trans hu hhlt))
        exact ⟨fun hS => hnot (hmem_iff.mpr hS), hhlt, hr_h ▸ hhr⟩
      · rintro ⟨hnot, hhlt, hhr⟩
        have hmem_iff := hagree h hhlt
        have hr_h : r (insert g S) h = r S h :=
          hr_congr (insert g S) S h (fun u hu => hagree u (lt_trans hu hhlt))
        exact ⟨fun hS => hnot (hmem_iff.mp hS), hhlt, hr_h.symm ▸ hhr⟩
    dsimp only [phiR]
    rw [hr_eq, hpref_eq]
  have hB_tele : ∀ L : Finset (Fin n),
      ∑ i : Fin m, F i (trainState F L n i) = ∑ g : Fin n, if g ∈ L then d L g else 0 := by
    intro L
    rw [htrain_eq_pref n L, hpref_telescope L L]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    dsimp only [d]
    rw [htrain_eq_pref g.1 L]
  have hR_tele : ∀ L : Finset (Fin n),
      ∑ i : Fin m, F i (R_pool F L i) = ∑ g : Fin n, if g ∉ L then phiR L g else 0 := by
    intro L
    have hR_eq : ∀ i : Fin m, R_pool F L i = prefFilter (Finset.univ \ L) L n i := by
      intro i; ext g
      simp only [R_pool, prefFilter, Finset.mem_filter, hr_opt L g, Option.some.injEq]
      exact ⟨fun ⟨hg1, hg2⟩ => ⟨hg1, g.isLt, hg2⟩, fun ⟨hg1, _, hg2⟩ => ⟨hg1, hg2⟩⟩
    simp_rw [hR_eq]
    rw [hpref_telescope (Finset.univ \ L) L]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    have hmem : g ∈ Finset.univ \ L ↔ g ∉ L := by simp
    by_cases hg : g ∉ L
    · rw [if_pos (hmem.mpr hg), if_pos hg]
    · rw [if_neg (fun h => hg (hmem.mp h)), if_neg hg]
  have hsubmod_union : ∀ (i : Fin m) (A U : Finset (Fin n)), Disjoint A U →
      F i (A ∪ U) - F i A ≤ ∑ g ∈ U, (F i (insert g A) - F i A) := by
    intro i A U
    induction U using Finset.induction_on with
    | empty => intro _; simp
    | insert a U' ha ih =>
      intro hdisj
      obtain ⟨haA, hdisj'⟩ := Finset.disjoint_insert_right.mp hdisj
      have haAU : a ∉ A ∪ U' := by simp [haA, ha]
      have hstep := (hF i).2.2 A (A ∪ U') Finset.subset_union_left a haAU
      have hih := ih hdisj'
      rw [Finset.union_insert, Finset.sum_insert ha]
      linarith
  have hd_nonneg : ∀ (L : Finset (Fin n)) (g : Fin n), 0 ≤ d L g := by
    intro L g
    exact sub_nonneg.mpr ((hF (r L g)).1 _ _ (Finset.subset_insert _ _))
  have h_greedy_bound : ∀ L : Finset (Fin n),
      ∑ i : Fin m, F i (X_star i) ≤
        (∑ i : Fin m, F i (trainState F L n i)) + ∑ g : Fin n, d L g := by
    intro L
    let B : Fin m → Finset (Fin n) := trainState F L n
    let U : Fin m → Finset (Fin n) := fun i => X_star i \ B i
    have hper_i : ∀ i : Fin m, F i (X_star i) ≤ F i (B i) + ∑ g ∈ U i, d L g := by
      intro i
      have hsub_union : X_star i ⊆ B i ∪ U i := by
        dsimp only [U]
        rw [Finset.union_sdiff_self_eq_union]
        exact Finset.subset_union_right
      have h1 : F i (X_star i) ≤ F i (B i ∪ U i) := (hF i).1 _ _ hsub_union
      have h2 : F i (B i ∪ U i) - F i (B i) ≤ ∑ g ∈ U i, (F i (insert g (B i)) - F i (B i)) :=
        hsubmod_union i (B i) (U i) Finset.disjoint_sdiff
      have h3 : ∑ g ∈ U i, (F i (insert g (B i)) - F i (B i)) ≤ ∑ g ∈ U i, d L g := by
        refine Finset.sum_le_sum (fun g hgU => ?_)
        have hgB : g ∉ B i := (Finset.mem_sdiff.mp hgU).2
        have hpref_sub : trainState F L g.1 i ⊆ B i := by
          dsimp only [B]
          rw [htrain_eq_pref g.1 L, htrain_eq_pref n L]
          intro h hh
          simp only [prefFilter, Finset.mem_filter] at hh ⊢
          exact ⟨hh.1, h.isLt, hh.2.2⟩
        have hdim := (hF i).2.2 (trainState F L g.1 i) (B i) hpref_sub g hgB
        exact le_trans hdim (hr_max L g i)
      linarith
    have hsum_i : ∑ i : Fin m, F i (X_star i) ≤
        (∑ i : Fin m, F i (B i)) + ∑ i : Fin m, ∑ g ∈ U i, d L g := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun i _ => hper_i i)
    have hU_disj : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint U := by
      intro i _ j _ hij
      exact Disjoint.mono Finset.sdiff_subset Finset.sdiff_subset (hX_alloc.2 i j hij)
    have hsum_U : ∑ i : Fin m, ∑ g ∈ U i, d L g ≤ ∑ g : Fin n, d L g := by
      rw [← Finset.sum_biUnion hU_disj]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun g _ _ => hd_nonneg L g)
    linarith
  have h_pool_dom : ∀ L : Finset (Fin n),
      ∑ i : Fin m, F i (trainState F L n i) ≤ ∑ g : Fin n, phiR L g := by
    intro L
    have hB_le_Z : ∑ i : Fin m, F i (trainState F L n i) ≤
        ∑ i : Fin m, F i (prefFilter Finset.univ L n i) := by
      rw [htrain_eq_pref n L]
      refine Finset.sum_le_sum (fun i _ => (hF i).1 _ _ ?_)
      intro h hh
      simp only [prefFilter, Finset.mem_filter] at hh ⊢
      exact ⟨Finset.mem_univ h, hh.2⟩
    have hZ_tele := hpref_telescope Finset.univ L
    have hZ_le_R : (∑ g : Fin n,
          if g ∈ (Finset.univ : Finset (Fin n)) then
            F (r L g) (insert g (prefFilter Finset.univ L g.1 (r L g))) -
              F (r L g) (prefFilter Finset.univ L g.1 (r L g))
          else 0) ≤ ∑ g : Fin n, phiR L g := by
      refine Finset.sum_le_sum (fun g _ => ?_)
      rw [if_pos (Finset.mem_univ g)]
      have hsub : prefFilter (Finset.univ \ L) L g.1 (r L g) ⊆
          prefFilter Finset.univ L g.1 (r L g) := by
        intro h hh
        simp only [prefFilter, Finset.mem_filter] at hh ⊢
        exact ⟨Finset.mem_univ h, hh.2⟩
      have hg_not : g ∉ prefFilter Finset.univ L g.1 (r L g) := by
        simp [prefFilter]
      exact (hF (r L g)).2.2 _ _ hsub g hg_not
    linarith
  
  let OPT : ℝ := ∑ i : Fin m, F i (X_star i)
  let EB : ℝ := ∑ L : Finset (Fin n), bernProb n lam L * (∑ i : Fin m, F i (trainState F L n i))
  let Ed : ℝ := ∑ L : Finset (Fin n), bernProb n lam L * (∑ g : Fin n, d L g)
  let ER : ℝ := ∑ L : Finset (Fin n), bernProb n lam L * (∑ i : Fin m, F i (R_pool F L i))
  let EpR : ℝ := ∑ L : Finset (Fin n), bernProb n lam L * (∑ g : Fin n, phiR L g)
  have hEB_eq : EB = lam * Ed := by
    calc EB
        = ∑ L : Finset (Fin n), ∑ g : Fin n, bernProb n lam L * (if g ∈ L then d L g else 0) := by
          dsimp only [EB]; simp_rw [hB_tele, Finset.mul_sum]
      _ = ∑ g : Fin n, ∑ L : Finset (Fin n), bernProb n lam L * (if g ∈ L then d L g else 0) :=
          Finset.sum_comm
      _ = ∑ g : Fin n, lam * (∑ L : Finset (Fin n), bernProb n lam L * d L g) := by
          refine Finset.sum_congr rfl (fun g _ => ?_)
          exact (hbern_coin g (fun L => d L g) (hd_indep g)).1
      _ = lam * ∑ g : Fin n, ∑ L : Finset (Fin n), bernProb n lam L * d L g :=
          (Finset.mul_sum _ _ _).symm
      _ = lam * ∑ L : Finset (Fin n), ∑ g : Fin n, bernProb n lam L * d L g := by
          rw [Finset.sum_comm]
      _ = lam * Ed := by
          dsimp only [Ed]; simp_rw [Finset.mul_sum]
  have hER_eq : ER = (1 - lam) * EpR := by
    calc ER
        = ∑ L : Finset (Fin n), ∑ g : Fin n, bernProb n lam L * (if g ∉ L then phiR L g else 0) := by
          dsimp only [ER]; simp_rw [hR_tele, Finset.mul_sum]
      _ = ∑ g : Fin n, ∑ L : Finset (Fin n), bernProb n lam L * (if g ∉ L then phiR L g else 0) :=
          Finset.sum_comm
      _ = ∑ g : Fin n, (1 - lam) * (∑ L : Finset (Fin n), bernProb n lam L * phiR L g) := by
          refine Finset.sum_congr rfl (fun g _ => ?_)
          exact (hbern_coin g (fun L => phiR L g) (hphiR_indep g)).2
      _ = (1 - lam) * ∑ g : Fin n, ∑ L : Finset (Fin n), bernProb n lam L * phiR L g :=
          (Finset.mul_sum _ _ _).symm
      _ = (1 - lam) * ∑ L : Finset (Fin n), ∑ g : Fin n, bernProb n lam L * phiR L g := by
          rw [Finset.sum_comm]
      _ = (1 - lam) * EpR := by
          dsimp only [EpR]; simp_rw [Finset.mul_sum]
  have hOPT_le : OPT ≤ EB + Ed := by
    calc OPT
        = (∑ L : Finset (Fin n), bernProb n lam L) * OPT := by rw [hbern_sum, one_mul]
      _ = ∑ L : Finset (Fin n), bernProb n lam L * OPT := Finset.sum_mul _ _ _
      _ ≤ ∑ L : Finset (Fin n),
            bernProb n lam L * ((∑ i : Fin m, F i (trainState F L n i)) + ∑ g : Fin n, d L g) := by
          refine Finset.sum_le_sum (fun L _ => ?_)
          exact mul_le_mul_of_nonneg_left (h_greedy_bound L) (hbern_nonneg L)
      _ = EB + Ed := by
          simp_rw [mul_add]
          exact Finset.sum_add_distrib
  have hEB_le_EpR : EB ≤ EpR := by
    dsimp only [EB, EpR]
    refine Finset.sum_le_sum (fun L _ => ?_)
    exact mul_le_mul_of_nonneg_left (h_pool_dom L) (hbern_nonneg L)
  have h1 : lam * OPT ≤ (1 + lam) * EB := by nlinarith [hOPT_le, hEB_eq, hlam_pos]
  have h2 : (1 - lam) * EB ≤ ER := by nlinarith [hEB_le_EpR, hER_eq, hlam_lt1]
  have h3 : (1 + lam) * ((3 - 2 * Real.sqrt 2) * OPT) ≤ (1 + lam) * ER := by
    calc (1 + lam) * ((3 - 2 * Real.sqrt 2) * OPT)
        = ((3 - 2 * Real.sqrt 2) * (1 + lam)) * OPT := by ring
      _ = ((1 - lam) * lam) * OPT := by rw [← hlam_alg]
      _ = (1 - lam) * (lam * OPT) := by ring
      _ ≤ (1 - lam) * ((1 + lam) * EB) := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = (1 + lam) * ((1 - lam) * EB) := by ring
      _ ≤ (1 + lam) * ER := mul_le_mul_of_nonneg_left h2 (by linarith)
  exact le_of_mul_le_mul_left h3 (by linarith)

theorem frozen_routing_trajectory_and_meas : ∀ (n m : ℕ) (selAlg : ∀ d : ℕ, OnlineSelectionAlg d),
      IsProbabilityMeasure (frozenSeedMeasure n selAlg) ∧
      (∀ (prev : List (Fin n)) (x : Fin n) (bundles : Fin m → Finset (Fin n))
        (oracle : Fin m → {T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → WithBot ℝ)
        (dec : Option (Fin m)),
        MeasurableSet {ω : FrozenSeed n selAlg |
          (frozenRoutingDet selAlg ω).step prev x bundles oracle = dec}) ∧
      (∀ (v : Fin m → ItemValuation n) (c : Fin n → ℝ)
        (η_fam : (k : Fin (n + 1)) → (selAlg (n - k.1)).Seed) (π : Equiv.Perm (Fin n)),
        let k_fin := K_sample c
        let k := k_fin.1
        let L := ((List.ofFn π).take k).toFinset
        let F := fun i => disposalEnvelope (v i)
        ∀ (hcard : (Finset.univ \ L).card = n - k) (π' : Equiv.Perm (Fin (n - k))),
          (∀ s : Fin (n - k), complEmb L k hcard (π' s) = π ⟨k + s.1, by omega⟩) →
          runDetWelfare (frozenRoutingDet selAlg (c, η_fam)) v π =
            fun i =>
              ((runDetSelection ((selAlg (n - k)).det (η_fam k_fin))
                (poolVal (v i) (complEmb L k hcard) (R_pool F L i)) π').map
                  (complEmb L k hcard)) ∩ R_pool F L i) ∧
      ((∀ (d : ℕ) (w : ItemValuation d), IsGSValuation w →
        ∀ (ω_s : (selAlg d).Seed) (π_s : Equiv.Perm (Fin d)) (s : ℕ) (hs : s ≤ d),
          let st := runDetSelectionSteps ((selAlg d).det ω_s) w π_s s hs
          w st.2 ≠ ⊥ ∧ ((0 : ℝ) : WithBot ℝ) ≤ w st.2) →
        ∀ (v : Fin m → ItemValuation n),
          (∀ i : Fin m, IsGSValuation (v i)) →
          (∀ (i : Fin m) (d : ℕ) (emb : Fin d ↪ Fin n) (R_i : Finset (Fin n)),
            IsGSValuation (poolVal (v i) emb R_i)) →
          ∀ (ω : FrozenSeed n selAlg) (π : Equiv.Perm (Fin n)) (t : ℕ) (ht : t ≤ n),
            let st := runDetWelfareSteps (frozenRoutingDet selAlg ω) v π t ht
            IsAllocOf st.1.toFinset st.2 ∧
            ∀ i : Fin m, v i (st.2 i) ≠ ⊥ ∧ ((0 : ℝ) : WithBot ℝ) ≤ v i (st.2 i)) :=
by
  intro n m selAlg
  
  have h_prob : IsProbabilityMeasure (frozenSeedMeasure n selAlg) := by
    let ν₁ : Measure ℝ := (ENNReal.ofReal (1 : ℝ))⁻¹ • volume.restrict (Set.Icc (0 : ℝ) 1)
    have hν₁ : IsProbabilityMeasure ν₁ := by
      rw [MeasureTheory.isProbabilityMeasure_iff]
      simp [ν₁, Real.volume_Icc]
    haveI : IsProbabilityMeasure ν₁ := hν₁
    haveI : IsProbabilityMeasure (unifCubeMeasure n 1) := by
      unfold unifCubeMeasure; infer_instance
    unfold frozenSeedMeasure
    infer_instance
  
  have h_K_meas : ∀ k_fin : Fin (n + 1), MeasurableSet {c : Fin n → ℝ | K_sample c = k_fin} := by
    intro k_fin
    have heq : {c : Fin n → ℝ | K_sample c = k_fin} =
        ⋃ J ∈ (Finset.univ : Finset (Fin n)).powersetCard k_fin.1,
          ⋂ j : Fin n,
            if j ∈ J then {c : Fin n → ℝ | c j ∈ Set.Ico (0 : ℝ) lam}
            else {c : Fin n → ℝ | c j ∈ Set.Ico (0 : ℝ) lam}ᶜ := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, Finset.mem_powersetCard,
        Finset.subset_univ, true_and, K_sample, Fin.ext_iff, Set.mem_Ico]
      constructor
      · intro hk
        refine ⟨Finset.univ.filter (fun j : Fin n => 0 ≤ c j ∧ c j < lam), hk, fun j => ?_⟩
        by_cases hj : 0 ≤ c j ∧ c j < lam <;> simp [hj]
      · rintro ⟨J, hJcard, hjJ⟩
        have hJeq : Finset.univ.filter (fun j : Fin n => 0 ≤ c j ∧ c j < lam) = J := by
          ext j; specialize hjJ j
          by_cases hj : j ∈ J
          · rw [if_pos hj] at hjJ
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, hj, iff_true]; exact hjJ
          · rw [if_neg hj] at hjJ
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, hj, iff_false]; exact hjJ
        rw [hJeq, hJcard]
    rw [heq]
    refine Finset.measurableSet_biUnion _ (fun J _ => MeasurableSet.iInter (fun j => ?_))
    split_ifs
    · exact measurableSet_Ico.preimage (measurable_pi_apply j)
    · exact (measurableSet_Ico.preimage (measurable_pi_apply j)).compl
  have h_replay_meas : ∀ (d : ℕ) (w : ItemValuation d) (items : List (Fin d))
      (s : ℕ) (hs : s ≤ items.length),
      (∀ η : (selAlg d).Seed,
        (replaySelectionSteps ((selAlg d).det η) w items s hs).1 = items.take s) ∧
      (∀ A : Finset (Fin d),
        MeasurableSet {η : (selAlg d).Seed |
          (replaySelectionSteps ((selAlg d).det η) w items s hs).2 = A}) := by
    intro d w items s
    induction s with
    | zero =>
      intro hs
      refine ⟨fun _ => by simp [replaySelectionSteps], fun A => ?_⟩
      by_cases hA : (∅ : Finset (Fin d)) = A
      · convert MeasurableSet.univ; ext η; simp [replaySelectionSteps, hA]
      · convert MeasurableSet.empty; ext η; simp [replaySelectionSteps, hA]
    | succ s ih =>
      intro hs
      obtain ⟨ih1, ih2⟩ := ih (Nat.le_of_succ_le hs)
      refine ⟨fun η => ?_, fun A => ?_⟩
      · simp only [replaySelectionSteps, ih1 η]
        rw [List.take_add_one, List.getElem?_eq_getElem hs, Option.toList_some]
      · let y := items[s]'hs
        let pairs := ((Finset.univ : Finset (Finset (Fin d) × Bool))).filter
          (fun p => (if p.2 then insert y p.1 else p.1) = A)
        have heq : {η : (selAlg d).Seed |
            (replaySelectionSteps ((selAlg d).det η) w items (s + 1) hs).2 = A} =
            ⋃ p ∈ pairs,
              ({η | (replaySelectionSteps ((selAlg d).det η) w items s (Nat.le_of_succ_le hs)).2 = p.1} ∩
               {η | ((selAlg d).det η).step (items.take s) y p.1 (fun ⟨T, _⟩ => w T) = p.2}) := by
          ext η
          simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, pairs,
            Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hA
            let acc0 := (replaySelectionSteps ((selAlg d).det η) w items s (Nat.le_of_succ_le hs)).2
            let b0 := ((selAlg d).det η).step (items.take s) y acc0 (fun ⟨T, _⟩ => w T)
            refine ⟨(acc0, b0), ?_, rfl, rfl⟩
            dsimp only [y, acc0, b0]
            rw [← ih1 η]
            exact hA
          · rintro ⟨⟨A0, b0⟩, hp, hacc, hb⟩
            dsimp only at hp
            dsimp only [replaySelectionSteps]
            rw [ih1 η, hacc, hb]
            exact hp
        rw [heq]
        exact Finset.measurableSet_biUnion _ (fun p _ =>
          (ih2 p.1).inter ((selAlg d).meas_step (items.take s) y p.1 (fun ⟨T, _⟩ => w T) p.2))
  
  have h_meas : ∀ (prev : List (Fin n)) (x : Fin n) (bundles : Fin m → Finset (Fin n))
      (oracle : Fin m → {T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → WithBot ℝ)
      (dec : Option (Fin m)),
      MeasurableSet {ω : FrozenSeed n selAlg |
        (frozenRoutingDet selAlg ω).step prev x bundles oracle = dec} := by
    intro prev x bundles oracle dec
    let stepAt : (k_fin : Fin (n + 1)) → (selAlg (n - k_fin.1)).Seed → Option (Fin m) :=
      fun k_fin η =>
        let k : ℕ := k_fin.1
        if hk_valid : k ≤ prev.length ∧ prev.length < n ∧ prev.Nodup ∧ x ∉ prev then
          let L : Finset (Fin n) := (prev.take k).toFinset
          have hL_nodup : (prev.take k).Nodup := hk_valid.2.2.1.take
          have hL_card : L.card = k := by
            rw [List.toFinset_card_of_nodup hL_nodup, List.length_take, min_eq_left hk_valid.1]
          have hcard : (Finset.univ \ L).card = n - k := by
            rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hL_card]
          let d : ℕ := n - k
          let emb : Fin d ↪ Fin n := complEmb L k hcard
          let v_loc : Fin m → ItemValuation n :=
            fun i T => if h : T ⊆ insert x prev.toFinset then oracle i ⟨T, h⟩ else ⊥
          let F_loc : Fin m → Finset (Fin n) → ℝ := fun i S => disposalEnvelope (v_loc i) S
          match routeOpt F_loc L x, invEmbOpt emb x with
          | some i_star, some x' =>
              let tail' : List (Fin d) := (prev.drop k).filterMap (invEmbOpt emb)
              let v_hat_loc : ItemValuation d :=
                poolVal (v_loc i_star) emb (R_pool F_loc L i_star)
              let acc' : Finset (Fin d) :=
                (replaySelectionSteps ((selAlg d).det η) v_hat_loc tail' tail'.length le_rfl).2
              let dec_b : Bool :=
                ((selAlg d).det η).step tail' x' acc' (fun ⟨T', _⟩ => v_hat_loc T')
              if dec_b then some i_star else none
          | _, _ => none
        else
          none
    have h_stepAt_eq : ∀ ω : FrozenSeed n selAlg,
        (frozenRoutingDet selAlg ω).step prev x bundles oracle =
          stepAt (K_sample ω.1) (ω.2 (K_sample ω.1)) := fun _ => rfl
    have h_stepAt_congr : ∀ (k₁ k₂ : Fin (n + 1))
        (η_fam : (k : Fin (n + 1)) → (selAlg (n - k.1)).Seed),
        k₁ = k₂ → stepAt k₁ (η_fam k₁) = stepAt k₂ (η_fam k₂) := by
      rintro k₁ _ η_fam rfl; rfl
    have h_union : {ω : FrozenSeed n selAlg |
        (frozenRoutingDet selAlg ω).step prev x bundles oracle = dec} =
        ⋃ k_fin : Fin (n + 1),
          ((Prod.fst ⁻¹' {c : Fin n → ℝ | K_sample c = k_fin}) ∩
           ((fun ω : FrozenSeed n selAlg => ω.2 k_fin) ⁻¹'
             {η : (selAlg (n - k_fin.1)).Seed | stepAt k_fin η = dec})) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
        h_stepAt_eq ω]
      constructor
      · intro hdec
        exact ⟨K_sample ω.1, rfl, hdec⟩
      · rintro ⟨k_fin, hk, hdec⟩
        rw [h_stepAt_congr (K_sample ω.1) k_fin ω.2 hk]
        exact hdec
    rw [h_union]
    refine MeasurableSet.iUnion (fun k_fin => ?_)
    refine ((h_K_meas k_fin).preimage measurable_fst).inter ?_
    have h_proj_meas : Measurable (fun ω : FrozenSeed n selAlg => ω.2 k_fin) :=
      (@measurable_pi_apply (Fin (n + 1)) (fun k => (selAlg (n - k.1)).Seed) _ k_fin).comp
        measurable_snd
    refine MeasurableSet.preimage ?_ h_proj_meas
    by_cases hk_valid : k_fin.1 ≤ prev.length ∧ prev.length < n ∧ prev.Nodup ∧ x ∉ prev
    · let k : ℕ := k_fin.1
      let L : Finset (Fin n) := (prev.take k).toFinset
      have hL_nodup : (prev.take k).Nodup := hk_valid.2.2.1.take
      have hL_card : L.card = k := by
        rw [List.toFinset_card_of_nodup hL_nodup, List.length_take, min_eq_left hk_valid.1]
      have hcard : (Finset.univ \ L).card = n - k := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hL_card]
      let d : ℕ := n - k
      let emb : Fin d ↪ Fin n := complEmb L k hcard
      let v_loc : Fin m → ItemValuation n :=
        fun i T => if h : T ⊆ insert x prev.toFinset then oracle i ⟨T, h⟩ else ⊥
      let F_loc : Fin m → Finset (Fin n) → ℝ := fun i S => disposalEnvelope (v_loc i) S
      have h_slice_eq : ∀ η : (selAlg d).Seed, stepAt k_fin η =
          (match routeOpt F_loc L x, invEmbOpt emb x with
           | some i_star, some x' =>
               let tail' : List (Fin d) := (prev.drop k).filterMap (invEmbOpt emb)
               let v_hat_loc : ItemValuation d :=
                 poolVal (v_loc i_star) emb (R_pool F_loc L i_star)
               let acc' : Finset (Fin d) :=
                 (replaySelectionSteps ((selAlg d).det η) v_hat_loc tail' tail'.length le_rfl).2
               let dec_b : Bool :=
                 ((selAlg d).det η).step tail' x' acc' (fun ⟨T', _⟩ => v_hat_loc T')
               if dec_b then some i_star else none
           | _, _ => none) := by
        intro η
        dsimp only [stepAt]
        rw [dif_pos hk_valid]
      simp only [h_slice_eq]
      cases h_ro : routeOpt F_loc L x with
      | none =>
        by_cases hdec : (none : Option (Fin m)) = dec
        · convert MeasurableSet.univ; ext η; simp [hdec]
        · convert MeasurableSet.empty; ext η; simp [hdec]
      | some i_star =>
        cases h_inv : invEmbOpt emb x with
        | none =>
          by_cases hdec : (none : Option (Fin m)) = dec
          · convert MeasurableSet.univ; ext η; simp [hdec]
          · convert MeasurableSet.empty; ext η; simp [hdec]
        | some x' =>
          let tail' : List (Fin d) := (prev.drop k).filterMap (invEmbOpt emb)
          let v_hat_loc : ItemValuation d :=
            poolVal (v_loc i_star) emb (R_pool F_loc L i_star)
          let b_set : Finset Bool :=
            (Finset.univ : Finset Bool).filter (fun b => (if b then some i_star else none) = dec)
          have h_decomp_eta : {η : (selAlg d).Seed |
              (if ((selAlg d).det η).step tail' x'
                (replaySelectionSteps ((selAlg d).det η) v_hat_loc tail' tail'.length le_rfl).2
                (fun ⟨T', _⟩ => v_hat_loc T') then some i_star else none) = dec} =
              ⋃ b ∈ b_set, ⋃ A : Finset (Fin d),
                ({η : (selAlg d).Seed |
                  (replaySelectionSteps ((selAlg d).det η) v_hat_loc tail' tail'.length le_rfl).2 = A} ∩
                 {η : (selAlg d).Seed |
                  ((selAlg d).det η).step tail' x' A (fun ⟨T', _⟩ => v_hat_loc T') = b}) := by
            ext η
            simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, b_set,
              Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro hdec
              exact ⟨_, hdec, _, rfl, rfl⟩
            · rintro ⟨b, hb, A, hA, hstep⟩
              rw [hA, hstep]
              exact hb
          dsimp only
          rw [h_decomp_eta]
          refine Finset.measurableSet_biUnion _ (fun b _ => MeasurableSet.iUnion (fun A => ?_))
          exact ((h_replay_meas d v_hat_loc tail' tail'.length le_rfl).2 A).inter
            ((selAlg d).meas_step tail' x' A (fun ⟨T', _⟩ => v_hat_loc T') b)
    · have h_slice_neg : ∀ η : (selAlg (n - k_fin.1)).Seed, stepAt k_fin η = none := by
        intro η; dsimp only [stepAt]; rw [dif_neg hk_valid]
      simp only [h_slice_neg]
      by_cases hdec : (none : Option (Fin m)) = dec
      · convert MeasurableSet.univ; ext η; simp [hdec]
      · convert MeasurableSet.empty; ext η; simp [hdec]
  
  have h_wsteps_fst : ∀ (alg_w : DetWelfareAlg n m) (v : Fin m → ItemValuation n)
      (π : Equiv.Perm (Fin n)) (t : ℕ) (ht : t ≤ n),
      (runDetWelfareSteps alg_w v π t ht).1 = (List.ofFn π).take t := by
    intro alg_w v π t
    induction t with
    | zero => intro _; simp [runDetWelfareSteps]
    | succ t ih =>
      intro ht
      simp only [runDetWelfareSteps, ih (Nat.le_of_succ_le ht)]
      have ht_len : t < (List.ofFn π).length := by simp [List.length_ofFn]; omega
      rw [List.take_add_one, List.getElem?_eq_getElem ht_len, Option.toList_some, List.getElem_ofFn]
  have h_ssteps_fst : ∀ {d : ℕ} (alg_s : DetSelectionAlg d) (w : ItemValuation d)
      (π_s : Equiv.Perm (Fin d)) (r : ℕ) (hr : r ≤ d),
      (runDetSelectionSteps alg_s w π_s r hr).1 = (List.ofFn π_s).take r := by
    intro d alg_s w π_s r
    induction r with
    | zero => intro _; simp [runDetSelectionSteps]
    | succ r ih =>
      intro hr
      simp only [runDetSelectionSteps, ih (Nat.le_of_succ_le hr)]
      have hr_len : r < (List.ofFn π_s).length := by simp [List.length_ofFn]; omega
      rw [List.take_add_one, List.getElem?_eq_getElem hr_len, Option.toList_some, List.getElem_ofFn]
  have h_invEmb_self : ∀ {d : ℕ} (emb : Fin d ↪ Fin n) (z : Fin d),
      invEmbOpt emb (emb z) = some z := by
    intro d emb z
    unfold invEmbOpt
    have hex : ∃ z' : Fin d, emb z' = emb z := ⟨z, rfl⟩
    rw [dif_pos hex]
    congr 1
    exact emb.injective (Classical.choose_spec hex)
  have h_wsteps_congr : ∀ (alg_w : DetWelfareAlg n m) (v : Fin m → ItemValuation n)
      (π : Equiv.Perm (Fin n)) (t₁ t₂ : ℕ) (ht₁ : t₁ ≤ n) (ht₂ : t₂ ≤ n),
      t₁ = t₂ → runDetWelfareSteps alg_w v π t₁ ht₁ = runDetWelfareSteps alg_w v π t₂ ht₂ := by
    rintro alg_w v π t₁ _ ht₁ ht₂ rfl; rfl
  have h_ssteps_congr : ∀ {d : ℕ} (alg_s : DetSelectionAlg d) (w : ItemValuation d)
      (π_s : Equiv.Perm (Fin d)) (r₁ r₂ : ℕ) (hr₁ : r₁ ≤ d) (hr₂ : r₂ ≤ d),
      r₁ = r₂ → runDetSelectionSteps alg_s w π_s r₁ hr₁ = runDetSelectionSteps alg_s w π_s r₂ hr₂ := by
    rintro d alg_s w π_s r₁ _ hr₁ hr₂ rfl; rfl
  have h_replay_self_congr : ∀ {d : ℕ} (alg_s : DetSelectionAlg d) (w : ItemValuation d)
      (l₁ l₂ : List (Fin d)), l₁ = l₂ →
      replaySelectionSteps alg_s w l₁ l₁.length le_rfl =
      replaySelectionSteps alg_s w l₂ l₂.length le_rfl := by
    rintro d alg_s w l₁ _ rfl; rfl
  have h_step_congr : ∀ {d : ℕ} (alg_s : DetSelectionAlg d)
      (l₁ l₂ : List (Fin d)) (y₁ y₂ : Fin d) (A₁ A₂ : Finset (Fin d)) (w₁ w₂ : ItemValuation d),
      l₁ = l₂ → y₁ = y₂ → A₁ = A₂ →
      (∀ T' : Finset (Fin d), T' ⊆ insert y₂ l₂.toFinset → w₁ T' = w₂ T') →
      alg_s.step l₁ y₁ A₁ (fun ⟨T', _⟩ => w₁ T') =
        alg_s.step l₂ y₂ A₂ (fun ⟨T', _⟩ => w₂ T') := by
    rintro d alg_s l₁ _ y₁ _ A₁ _ w₁ w₂ rfl rfl rfl hw
    congr 1
    funext ⟨T', hT'⟩
    exact hw T' hT'
  
  have h_env_agree : ∀ (v₁ v₂ : Fin m → ItemValuation n) (U : Finset (Fin n)),
      (∀ (i : Fin m) (T : Finset (Fin n)), T ⊆ U → v₁ i T = v₂ i T) →
      ∀ (i : Fin m) (S : Finset (Fin n)), S ⊆ U →
        disposalEnvelope (v₁ i) S = disposalEnvelope (v₂ i) S := by
    intro v₁ v₂ U hv i S hS
    unfold disposalEnvelope
    congr 1
    refine Finset.sup_congr rfl (fun T hT => ?_)
    exact hv i T ((Finset.mem_powerset.mp hT).trans hS)
  have h_train_agree : ∀ (v₁ v₂ : Fin m → ItemValuation n) (U L₀ : Finset (Fin n)),
      L₀ ⊆ U →
      (∀ (i : Fin m) (T : Finset (Fin n)), T ⊆ U → v₁ i T = v₂ i T) →
      let F₁ := fun i => disposalEnvelope (v₁ i)
      let F₂ := fun i => disposalEnvelope (v₂ i)
      ∀ u : ℕ, (∀ i : Fin m, trainState F₁ L₀ u i ⊆ L₀) ∧
        trainState F₁ L₀ u = trainState F₂ L₀ u := by
    intro v₁ v₂ U L₀ hL₀ hv F₁ F₂ u
    induction u with
    | zero =>
      exact ⟨fun _ => Finset.empty_subset _, rfl⟩
    | succ u ih =>
      obtain ⟨hsub, heq⟩ := ih
      dsimp only [trainState]
      by_cases hu : u < n
      · rw [dif_pos hu, dif_pos hu]
        let g : Fin n := ⟨u, hu⟩
        by_cases hg : g ∈ L₀
        · have hscore : (fun i : Fin m =>
              F₁ i (insert g (trainState F₁ L₀ u i)) - F₁ i (trainState F₁ L₀ u i)) =
              (fun i : Fin m =>
              F₂ i (insert g (trainState F₂ L₀ u i)) - F₂ i (trainState F₂ L₀ u i)) := by
            funext i
            have hBi : trainState F₂ L₀ u i ⊆ L₀ := heq ▸ hsub i
            rw [heq]
            have h1 := h_env_agree v₁ v₂ U hv i (insert g (trainState F₂ L₀ u i))
              (Finset.insert_subset_iff.mpr ⟨hL₀ hg, hBi.trans hL₀⟩)
            have h2 := h_env_agree v₁ v₂ U hv i (trainState F₂ L₀ u i) (hBi.trans hL₀)
            dsimp only [F₁, F₂]
            rw [h1, h2]
          refine ⟨?_, ?_⟩
          · intro i
            cases bestBidderOpt (fun j : Fin m =>
                F₁ j (insert g (trainState F₁ L₀ u j)) - F₁ j (trainState F₁ L₀ u j)) with
            | none => exact hsub i
            | some i_star =>
              dsimp only
              rw [if_pos (show (⟨u, hu⟩ : Fin n) ∈ L₀ from hg)]
              by_cases hi : i = i_star
              · subst hi
                rw [Function.update_self]
                exact Finset.insert_subset_iff.mpr ⟨hg, hsub i⟩
              · rw [Function.update_of_ne hi]
                exact hsub i
          · rw [hscore, heq]
        · have h_not_mem : ∀ (opt : Option (Fin m)) (B : Fin m → Finset (Fin n)),
              (match opt with
               | some i_star => if g ∈ L₀ then Function.update B i_star (insert g (B i_star)) else B
               | none => B) = B := by
            intro opt B
            cases opt with
            | none => rfl
            | some i_star => exact if_neg hg
          rw [h_not_mem, h_not_mem]
          exact ⟨hsub, heq⟩
      · rw [dif_neg hu, dif_neg hu]
        exact ⟨hsub, heq⟩
  have h_route_agree : ∀ (v₁ v₂ : Fin m → ItemValuation n) (U L₀ : Finset (Fin n)),
      L₀ ⊆ U →
      (∀ (i : Fin m) (T : Finset (Fin n)), T ⊆ U → v₁ i T = v₂ i T) →
      ∀ y : Fin n, y ∈ U →
        routeOpt (fun i => disposalEnvelope (v₁ i)) L₀ y =
          routeOpt (fun i => disposalEnvelope (v₂ i)) L₀ y := by
    intro v₁ v₂ U L₀ hL₀ hv y hy
    obtain ⟨hsub, heq⟩ := h_train_agree v₁ v₂ U L₀ hL₀ hv y.1
    unfold routeOpt
    dsimp only
    congr 1
    funext i
    have hBi : trainState (fun j => disposalEnvelope (v₂ j)) L₀ y.1 i ⊆ L₀ := heq ▸ hsub i
    rw [heq]
    rw [h_env_agree v₁ v₂ U hv i _ (Finset.insert_subset_iff.mpr ⟨hy, hBi.trans hL₀⟩),
        h_env_agree v₁ v₂ U hv i _ (hBi.trans hL₀)]
  have h_poolVal_agree : ∀ (v₁ v₂ : Fin m → ItemValuation n) (U L₀ : Finset (Fin n)),
      L₀ ⊆ U →
      (∀ (i : Fin m) (T : Finset (Fin n)), T ⊆ U → v₁ i T = v₂ i T) →
      ∀ {d : ℕ} (emb : Fin d ↪ Fin n) (i_star : Fin m) (T' : Finset (Fin d)),
        T'.map emb ⊆ U →
        poolVal (v₁ i_star) emb (R_pool (fun i => disposalEnvelope (v₁ i)) L₀ i_star) T' =
          poolVal (v₂ i_star) emb (R_pool (fun i => disposalEnvelope (v₂ i)) L₀ i_star) T' := by
    intro v₁ v₂ U L₀ hL₀ hv d emb i_star T' hT'
    unfold poolVal
    have h_inter_eq : (T'.map emb) ∩ R_pool (fun i => disposalEnvelope (v₁ i)) L₀ i_star =
        (T'.map emb) ∩ R_pool (fun i => disposalEnvelope (v₂ i)) L₀ i_star := by
      ext y
      simp only [Finset.mem_inter, R_pool, Finset.mem_filter]
      constructor
      · rintro ⟨hyT, hys, hro⟩
        exact ⟨hyT, hys, (h_route_agree v₁ v₂ U L₀ hL₀ hv y (hT' hyT)) ▸ hro⟩
      · rintro ⟨hyT, hys, hro⟩
        exact ⟨hyT, hys, (h_route_agree v₁ v₂ U L₀ hL₀ hv y (hT' hyT)).symm ▸ hro⟩
    rw [h_inter_eq]
    exact hv i_star _ (Finset.inter_subset_left.trans hT')
  
  have h_replay_eq_sel : ∀ {d : ℕ} (alg_s : DetSelectionAlg d) (w₁ w₂ : ItemValuation d)
      (π_s : Equiv.Perm (Fin d)) (s : ℕ) (hs : s < d),
      let tail'_0 := (List.ofFn π_s).take s
      (∀ T' : Finset (Fin d), T' ⊆ tail'_0.toFinset → w₁ T' = w₂ T') →
      ∀ (r : ℕ) (hr : r ≤ tail'_0.length) (hr_d : r ≤ d),
        replaySelectionSteps alg_s w₁ tail'_0 r hr =
          runDetSelectionSteps alg_s w₂ π_s r hr_d := by
    intro d alg_s w₁ w₂ π_s s hs tail'_0 hw r
    induction r with
    | zero =>
      intro _ _
      rfl
    | succ r ih =>
      intro hr hr_d
      have h_ih := ih (Nat.le_of_succ_le hr) (Nat.le_of_succ_le hr_d)
      have h_fst_r : (replaySelectionSteps alg_s w₁ tail'_0 r (Nat.le_of_succ_le hr)).1 =
          (List.ofFn π_s).take r := by
        rw [h_ih, h_ssteps_fst]
      have h_acc_r : (replaySelectionSteps alg_s w₁ tail'_0 r (Nat.le_of_succ_le hr)).2 =
          (runDetSelectionSteps alg_s w₂ π_s r (Nat.le_of_succ_le hr_d)).2 := by
        rw [h_ih]
      have hy : tail'_0[r]'hr = π_s ⟨r, hr_d⟩ := by
        simp [tail'_0, List.getElem_take, List.getElem_ofFn]
      dsimp only [replaySelectionSteps, runDetSelectionSteps]
      rw [h_fst_r, h_ssteps_fst, hy, h_acc_r]
      have h_ora_eq :
          (fun x : {T' : Finset (Fin d) //
              T' ⊆ insert (π_s ⟨r, hr_d⟩) ((List.ofFn π_s).take r).toFinset} => w₁ x.1) =
          (fun x => w₂ x.1) := by
        funext ⟨T', hT'⟩
        refine hw T' (fun z hz => ?_)
        rcases Finset.mem_insert.mp (hT' hz) with rfl | hz_prev
        · rw [← hy]
          exact List.mem_toFinset.mpr (List.getElem_mem hr)
        · have hr_le_s : r ≤ s := by
            have hlen : tail'_0.length = s := by
              simp [tail'_0, List.length_take, List.length_ofFn, Nat.le_of_lt hs]
            omega
          have h_sub_take : (List.ofFn π_s).take r = tail'_0.take r := by
            simp [tail'_0, List.take_take, min_eq_left hr_le_s]
          rw [h_sub_take] at hz_prev
          exact List.mem_toFinset.mpr (List.take_subset r tail'_0 (List.mem_toFinset.mp hz_prev))
      rw [h_ora_eq]
  
  have h_sample_empty : ∀ (v : Fin m → ItemValuation n) (c : Fin n → ℝ)
      (η_fam : (k : Fin (n + 1)) → (selAlg (n - k.1)).Seed) (π : Equiv.Perm (Fin n))
      (t : ℕ) (ht : t ≤ n),
      t ≤ (K_sample c).1 →
      (runDetWelfareSteps (frozenRoutingDet selAlg (c, η_fam)) v π t ht).2 = fun _ => ∅ := by
    intro v c η_fam π t
    induction t with
    | zero => intro _ _; rfl
    | succ t ih =>
      intro ht htk
      have ht' := Nat.le_of_succ_le ht
      have htk' := Nat.le_of_succ_le htk
      have h_prev : (runDetWelfareSteps (frozenRoutingDet selAlg (c, η_fam)) v π t ht').1 =
          (List.ofFn π).take t := h_wsteps_fst _ v π t ht'
      have h_bund : (runDetWelfareSteps (frozenRoutingDet selAlg (c, η_fam)) v π t ht').2 =
          fun _ => ∅ := ih ht' htk'
      have h_not_valid : ¬ ((K_sample c).1 ≤
          (runDetWelfareSteps (frozenRoutingDet selAlg (c, η_fam)) v π t ht').1.length ∧
          (runDetWelfareSteps (frozenRoutingDet selAlg (c, η_fam)) v π t ht').1.length < n ∧
          (runDetWelfareSteps (frozenRoutingDet selAlg (c, η_fam)) v π t ht').1.Nodup ∧
          π ⟨t, ht⟩ ∉ (runDetWelfareSteps (frozenRoutingDet selAlg (c, η_fam)) v π t ht').1) := by
        rw [h_prev]
        simp only [List.length_take, List.length_ofFn, min_eq_left ht']
        omega
      change (match frozenRoutingStep selAlg (c, η_fam)
          (runDetWelfareSteps (frozenRoutingDet selAlg (c, η_fam)) v π t ht').1
          (π ⟨t, ht⟩)
          (runDetWelfareSteps (frozenRoutingDet selAlg (c, η_fam)) v π t ht').2
          (fun i ⟨T, _⟩ => v i T) with
        | none => (runDetWelfareSteps (frozenRoutingDet selAlg (c, η_fam)) v π t ht').2
        | some i => _) = fun _ => ∅
      dsimp only [frozenRoutingStep]
      rw [dif_neg h_not_valid]
      exact h_bund
  have h_post_sample : ∀ (v : Fin m → ItemValuation n) (c : Fin n → ℝ)
      (η_fam : (k : Fin (n + 1)) → (selAlg (n - k.1)).Seed) (π : Equiv.Perm (Fin n)),
      let k_fin := K_sample c
      let k := k_fin.1
      let L := ((List.ofFn π).take k).toFinset
      let F := fun i => disposalEnvelope (v i)
      ∀ (hcard : (Finset.univ \ L).card = n - k) (π' : Equiv.Perm (Fin (n - k))),
        (∀ s : Fin (n - k), complEmb L k hcard (π' s) = π ⟨k + s.1, by omega⟩) →
        ∀ (s : ℕ) (hs : s ≤ n - k) (hks : k + s ≤ n),
          (runDetWelfareSteps (frozenRoutingDet selAlg (c, η_fam)) v π (k + s) hks).2 =
            fun i =>
              ((runDetSelectionSteps ((selAlg (n - k)).det (η_fam k_fin))
                (poolVal (v i) (complEmb L k hcard) (R_pool F L i)) π' s hs).2.map
                  (complEmb L k hcard)) ∩ R_pool F L i := by
    intro v c η_fam π k_fin k L F hcard π' hπ' s
    have h_emb_congr : ∀ (L₁ L₂ : Finset (Fin n)) (h₁ : (Finset.univ \ L₁).card = n - k)
        (h₂ : (Finset.univ \ L₂).card = n - k), L₁ = L₂ →
        complEmb L₁ k h₁ = complEmb L₂ k h₂ := by
      rintro L₁ _ h₁ h₂ rfl; rfl
    induction s with
    | zero =>
      intro hs hks
      have h0 := h_sample_empty v c η_fam π (k + 0) hks (le_refl k)
      rw [h0]
      funext i
      simp [runDetSelectionSteps]
    | succ s ih =>
      intro hs hks
      have hs' : s ≤ n - k := Nat.le_of_succ_le hs
      have hks' : k + s ≤ n := Nat.le_of_succ_le hks
      have h_ih := ih hs' hks'
      let d : ℕ := n - k
      let emb : Fin d ↪ Fin n := complEmb L k hcard
      let prev := (runDetWelfareSteps (frozenRoutingDet selAlg (c, η_fam)) v π (k + s) hks').1
      let bundles := (runDetWelfareSteps (frozenRoutingDet selAlg (c, η_fam)) v π (k + s) hks').2
      let x : Fin n := π ⟨k + s, hks⟩
      let x' : Fin d := π' ⟨s, hs⟩
      have hx_emb : emb x' = x := hπ' ⟨s, hs⟩
      have hprev_eq : prev = (List.ofFn π).take (k + s) := h_wsteps_fst _ v π (k + s) hks'
      have hprev_len : prev.length = k + s := by
        rw [hprev_eq, List.length_take, List.length_ofFn, min_eq_left hks']
      have hk_valid : k ≤ prev.length ∧ prev.length < n ∧ prev.Nodup ∧ x ∉ prev := by
        refine ⟨by omega, by omega, ?_, ?_⟩
        · rw [hprev_eq]
          exact (List.nodup_ofFn.mpr π.injective).take
        · rw [hprev_eq, List.mem_iff_getElem]
          rintro ⟨j, hj, hget⟩
          rw [List.length_take, List.length_ofFn, min_eq_left hks'] at hj
          rw [List.getElem_take, List.getElem_ofFn] at hget
          have hfin := π.injective hget
          have hj_eq : j = k + s := congrArg Fin.val hfin
          omega
      have hL_int : (prev.take k).toFinset = L := by
        rw [hprev_eq, List.take_take, min_eq_left (Nat.le_add_right k s)]
      have h_drop : prev.drop k = List.map emb ((List.ofFn π').take s) := by
        rw [hprev_eq]
        have hlen1 : (((List.ofFn π).take (k + s)).drop k).length = s := by
          simp [List.length_drop, List.length_take, List.length_ofFn, min_eq_left hks']
        have hlen2 : (List.map emb ((List.ofFn π').take s)).length = s := by
          simp [List.length_take, List.length_ofFn, min_eq_left hs']
        refine List.ext_getElem (hlen1.trans hlen2.symm) (fun j hj1 hj2 => ?_)
        rw [hlen1] at hj1
        simp only [List.getElem_drop, List.getElem_take, List.getElem_ofFn, List.getElem_map]
        exact (hπ' ⟨j, by omega⟩).symm
      have h_tail_eq : (prev.drop k).filterMap (invEmbOpt emb) = (List.ofFn π').take s := by
        rw [h_drop, List.filterMap_map]
        have hcomp : (invEmbOpt emb ∘ emb) = some := by
          funext z; exact h_invEmb_self emb z
        rw [hcomp, List.filterMap_some]
      have h_inv_x : invEmbOpt emb x = some x' := by
        rw [← hx_emb]; exact h_invEmb_self emb x'
      let U : Finset (Fin n) := insert x prev.toFinset
      let v_loc : Fin m → ItemValuation n :=
        fun i T => if h : T ⊆ insert x prev.toFinset then v i T else ⊥
      have hv_loc : ∀ (i : Fin m) (T : Finset (Fin n)), T ⊆ U → v_loc i T = v i T := by
        intro i T hT; exact dif_pos hT
      have hL_sub_U : L ⊆ U := by
        intro y hy
        refine Finset.mem_insert_of_mem ?_
        rw [← hL_int] at hy
        exact List.mem_toFinset.mpr (List.take_subset k prev (List.mem_toFinset.mp hy))
      have h_ro_x : routeOpt (fun i => disposalEnvelope (v_loc i)) L x = routeOpt F L x :=
        h_route_agree v_loc v U L hL_sub_U hv_loc x (Finset.mem_insert_self x prev.toFinset)
      change (match frozenRoutingStep selAlg (c, η_fam) prev x bundles (fun i ⟨T, _⟩ => v i T) with
        | none => bundles
        | some i => Function.update bundles i (insert x (bundles i))) = _
      have h_step_eval : frozenRoutingStep selAlg (c, η_fam) prev x bundles (fun i ⟨T, _⟩ => v i T) =
          (match routeOpt F L x with
           | some i_star =>
               let tail' : List (Fin d) := (prev.drop k).filterMap (invEmbOpt emb)
               let v_hat_loc : ItemValuation d :=
                 poolVal (v_loc i_star) emb (R_pool (fun i => disposalEnvelope (v_loc i)) L i_star)
               let acc' : Finset (Fin d) :=
                 (replaySelectionSteps ((selAlg d).det (η_fam k_fin)) v_hat_loc tail' tail'.length le_rfl).2
               let dec_b : Bool :=
                 ((selAlg d).det (η_fam k_fin)).step tail' x' acc' (fun ⟨T', _⟩ => v_hat_loc T')
               if dec_b then some i_star else none
           | none => none) := by
        dsimp only [frozenRoutingStep]
        rw [dif_pos hk_valid]
        have hemb_int : complEmb (prev.take k).toFinset k
            (by rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
              List.toFinset_card_of_nodup hk_valid.2.2.1.take, List.length_take, min_eq_left hk_valid.1]) =
            emb := h_emb_congr _ L _ hcard hL_int
        have h_eval_aux : ∀ (L_a : Finset (Fin n)) (emb_a : Fin d ↪ Fin n),
            L_a = L → emb_a = emb →
            (match routeOpt (fun i S => disposalEnvelope (v_loc i) S) L_a x, invEmbOpt emb_a x with
             | some i_star, some x'_int =>
                 let tail' : List (Fin d) := (prev.drop k).filterMap (invEmbOpt emb_a)
                 let v_hat_loc : ItemValuation d :=
                   poolVal (v_loc i_star) emb_a (R_pool (fun i => disposalEnvelope (v_loc i)) L_a i_star)
                 let acc' : Finset (Fin d) :=
                   (replaySelectionSteps ((selAlg d).det (η_fam k_fin)) v_hat_loc tail' tail'.length le_rfl).2
                 let dec_b : Bool :=
                   ((selAlg d).det (η_fam k_fin)).step tail' x'_int acc' (fun ⟨T', _⟩ => v_hat_loc T')
                 if dec_b then some i_star else none
             | _, _ => none) =
            (match routeOpt F L x with
             | some i_star =>
                 let tail' : List (Fin d) := (prev.drop k).filterMap (invEmbOpt emb)
                 let v_hat_loc : ItemValuation d :=
                   poolVal (v_loc i_star) emb (R_pool (fun i => disposalEnvelope (v_loc i)) L i_star)
                 let acc' : Finset (Fin d) :=
                   (replaySelectionSteps ((selAlg d).det (η_fam k_fin)) v_hat_loc tail' tail'.length le_rfl).2
                 let dec_b : Bool :=
                   ((selAlg d).det (η_fam k_fin)).step tail' x' acc' (fun ⟨T', _⟩ => v_hat_loc T')
                 if dec_b then some i_star else none
             | none => none) := by
          rintro _ _ rfl rfl
          rw [h_ro_x, h_inv_x]
          cases routeOpt F L x <;> rfl
        exact h_eval_aux _ _ hL_int hemb_int
      rw [h_step_eval]
      cases h_ro_val : routeOpt F L x with
      | none =>
        have hm_empty : ¬ (Finset.univ : Finset (Fin m)).Nonempty := by
          intro hm_ne
          unfold routeOpt bestBidderOpt at h_ro_val
          dsimp only at h_ro_val
          rw [dif_pos hm_ne] at h_ro_val
          simp at h_ro_val
        funext i
        exact False.elim (hm_empty ⟨i, Finset.mem_univ i⟩)
      | some i_star =>
        dsimp only
        let tail' : List (Fin d) := (prev.drop k).filterMap (invEmbOpt emb)
        let tail'_0 : List (Fin d) := (List.ofFn π').take s
        let v_hat_loc : ItemValuation d :=
          poolVal (v_loc i_star) emb (R_pool (fun i => disposalEnvelope (v_loc i)) L i_star)
        let w_star : ItemValuation d := poolVal (v i_star) emb (R_pool F L i_star)
        have h_map_sub_U : ∀ T' : Finset (Fin d), T' ⊆ insert x' tail'_0.toFinset → T'.map emb ⊆ U := by
          intro T' hT' y hy
          obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
          rcases Finset.mem_insert.mp (hT' hz) with rfl | hz_tail
          · rw [hx_emb]; exact Finset.mem_insert_self x prev.toFinset
          · refine Finset.mem_insert_of_mem ?_
            rw [hprev_eq]
            obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hz_tail)
            rw [List.length_take, List.length_ofFn, min_eq_left hs'] at hj
            rw [List.getElem_take, List.getElem_ofFn] at hget
            subst hget
            rw [hπ' ⟨j, by omega⟩]
            have hjk : k + j < ((List.ofFn π).take (k + s)).length := by
              rw [List.length_take, List.length_ofFn, min_eq_left hks']; omega
            have hmem_take : ((List.ofFn π).take (k + s))[k + j]'hjk ∈ (List.ofFn π).take (k + s) :=
              List.getElem_mem hjk
            simp only [List.getElem_take, List.getElem_ofFn] at hmem_take
            exact List.mem_toFinset.mpr hmem_take
        have hw_tail : ∀ T' : Finset (Fin d), T' ⊆ tail'_0.toFinset → v_hat_loc T' = w_star T' := by
          intro T' hT'
          exact h_poolVal_agree v_loc v U L hL_sub_U hv_loc emb i_star T'
            (h_map_sub_U T' (hT'.trans (Finset.subset_insert x' _)))
        have hw_ins : ∀ T' : Finset (Fin d), T' ⊆ insert x' tail'_0.toFinset → v_hat_loc T' = w_star T' := by
          intro T' hT'
          exact h_poolVal_agree v_loc v U L hL_sub_U hv_loc emb i_star T' (h_map_sub_U T' hT')
        have htail0_len : tail'_0.length = s := by
          simp [tail'_0, List.length_take, List.length_ofFn, min_eq_left hs']
        have h_acc_eq :
            (replaySelectionSteps ((selAlg d).det (η_fam k_fin)) v_hat_loc tail' tail'.length le_rfl).2 =
            (runDetSelectionSteps ((selAlg d).det (η_fam k_fin)) w_star π' s hs').2 := by
          have h1 := h_replay_self_congr ((selAlg d).det (η_fam k_fin)) v_hat_loc tail' tail'_0 h_tail_eq
          have h2 := h_replay_eq_sel ((selAlg d).det (η_fam k_fin)) v_hat_loc w_star π' s hs hw_tail
            tail'_0.length le_rfl (by omega)
          have h3 := h_ssteps_congr ((selAlg d).det (η_fam k_fin)) w_star π' tail'_0.length s
            (by omega) hs' htail0_len
          exact congrArg Prod.snd (h1.trans (h2.trans h3))
        have h_dec_b_eq :
            ((selAlg d).det (η_fam k_fin)).step tail' x'
              (replaySelectionSteps ((selAlg d).det (η_fam k_fin)) v_hat_loc tail' tail'.length le_rfl).2
              (fun ⟨T', _⟩ => v_hat_loc T') =
            ((selAlg d).det (η_fam k_fin)).step
              (runDetSelectionSteps ((selAlg d).det (η_fam k_fin)) w_star π' s hs').1
              x'
              (runDetSelectionSteps ((selAlg d).det (η_fam k_fin)) w_star π' s hs').2
              (fun ⟨T', _⟩ => w_star T') := by
          have h_fst_sel := h_ssteps_fst ((selAlg d).det (η_fam k_fin)) w_star π' s hs'
          refine h_step_congr ((selAlg d).det (η_fam k_fin)) _ _ _ _ _ _ v_hat_loc w_star
            (h_tail_eq.trans h_fst_sel.symm) rfl h_acc_eq (fun T' hT' => ?_)
          rw [h_fst_sel] at hT'
          exact hw_ins T' hT'
        have hx_sdiff : x ∈ Finset.univ \ L := by
          rw [← hx_emb]
          exact Finset.orderEmbOfFin_mem (Finset.univ \ L) hcard x'
        funext i
        by_cases hi : i = i_star
        · subst hi
          have hx_R : x ∈ R_pool F L i := Finset.mem_filter.mpr ⟨hx_sdiff, h_ro_val⟩
          change (match (if ((selAlg d).det (η_fam k_fin)).step tail' x'
                (replaySelectionSteps ((selAlg d).det (η_fam k_fin)) v_hat_loc tail' tail'.length le_rfl).2
                (fun ⟨T', _⟩ => v_hat_loc T') then some i else none) with
              | none => bundles
              | some j => Function.update bundles j (insert x (bundles j))) i = _
          rw [h_dec_b_eq]
          dsimp only [runDetSelectionSteps]
          change (match (if ((selAlg d).det (η_fam k_fin)).step
                (runDetSelectionSteps ((selAlg d).det (η_fam k_fin)) w_star π' s hs').1 x'
                (runDetSelectionSteps ((selAlg d).det (η_fam k_fin)) w_star π' s hs').2
                (fun ⟨T', _⟩ => w_star T') then some i else none) with
              | none => bundles
              | some j => Function.update bundles j (insert x (bundles j))) i =
            ((if ((selAlg d).det (η_fam k_fin)).step
                (runDetSelectionSteps ((selAlg d).det (η_fam k_fin)) w_star π' s hs').1 x'
                (runDetSelectionSteps ((selAlg d).det (η_fam k_fin)) w_star π' s hs').2
                (fun ⟨T', _⟩ => w_star T') then
                insert x' (runDetSelectionSteps ((selAlg d).det (η_fam k_fin)) w_star π' s hs').2
              else
                (runDetSelectionSteps ((selAlg d).det (η_fam k_fin)) w_star π' s hs').2).map emb) ∩
              R_pool F L i
          cases ((selAlg d).det (η_fam k_fin)).step
              (runDetSelectionSteps ((selAlg d).det (η_fam k_fin)) w_star π' s hs').1 x'
              (runDetSelectionSteps ((selAlg d).det (η_fam k_fin)) w_star π' s hs').2
              (fun ⟨T', _⟩ => w_star T') with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact congrFun h_ih i
          | true =>
            simp only [↓reduceIte, Function.update_self]
            dsimp only [bundles, emb, w_star, d]
            rw [h_ih, Finset.map_insert, show complEmb L k hcard x' = x from hx_emb,
              Finset.insert_inter_of_mem hx_R]
        · have hx_not_R : x ∉ R_pool F L i := by
            intro hxR
            have hro_i := (Finset.mem_filter.mp hxR).2
            rw [h_ro_val] at hro_i
            exact hi (Option.some.inj hro_i).symm
          have h_lhs_i : (match (if ((selAlg d).det (η_fam k_fin)).step tail' x'
                (replaySelectionSteps ((selAlg d).det (η_fam k_fin)) v_hat_loc tail' tail'.length le_rfl).2
                (fun ⟨T', _⟩ => v_hat_loc T') then some i_star else none) with
              | none => bundles
              | some j => Function.update bundles j (insert x (bundles j))) i = bundles i := by
            cases ((selAlg d).det (η_fam k_fin)).step tail' x'
                (replaySelectionSteps ((selAlg d).det (η_fam k_fin)) v_hat_loc tail' tail'.length le_rfl).2
                (fun ⟨T', _⟩ => v_hat_loc T') with
            | false => simp only [Bool.false_eq_true, ↓reduceIte]
            | true =>
              simp only [↓reduceIte]
              rw [Function.update_of_ne hi]
          rw [h_lhs_i]
          dsimp only [bundles, runDetSelectionSteps]
          rw [h_ih]
          let w_i := poolVal (v i) emb (R_pool F L i)
          cases ((selAlg d).det (η_fam k_fin)).step
              (runDetSelectionSteps ((selAlg d).det (η_fam k_fin)) w_i π' s hs').1 x'
              (runDetSelectionSteps ((selAlg d).det (η_fam k_fin)) w_i π' s hs').2
              (fun ⟨T', _⟩ => w_i T') with
          | false => simp only [Bool.false_eq_true, ↓reduceIte]
          | true =>
            simp only [↓reduceIte]
            rw [Finset.map_insert, show complEmb L k hcard x' = x from hx_emb]
            ext y
            simp only [Finset.mem_inter, Finset.mem_insert]
            constructor
            · rintro ⟨hy, hyR⟩
              exact ⟨Or.inr hy, hyR⟩
            · rintro ⟨rfl | hy, hyR⟩
              · exact False.elim (hx_not_R hyR)
              · exact ⟨hy, hyR⟩
  
  refine ⟨h_prob, h_meas, ?_, ?_⟩
  · 
    intro v c η_fam π k_fin k L F hcard π' hπ'
    have hk : k ≤ n := Nat.lt_succ_iff.mp k_fin.2
    have hkn : k + (n - k) = n := Nat.add_sub_of_le hk
    unfold runDetWelfare runDetSelection
    rw [← h_wsteps_congr (frozenRoutingDet selAlg (c, η_fam)) v π (k + (n - k)) n hkn.le (le_refl n) hkn]
    exact h_post_sample v c η_fam π hcard π' hπ' (n - k) (le_refl (n - k)) hkn.le
  · 
    intro h_sel_safe v hv h_pool_gs
    rintro ⟨c, η_fam⟩ π t ht
    let k_fin := K_sample c
    let k := k_fin.1
    have hk : k ≤ n := Nat.lt_succ_iff.mp k_fin.2
    by_cases htk : t ≤ k
    · 
      have h_fst := h_wsteps_fst (frozenRoutingDet selAlg (c, η_fam)) v π t ht
      have h_snd := h_sample_empty v c η_fam π t ht htk
      dsimp only
      rw [h_fst, h_snd]
      refine ⟨⟨fun _ => Finset.empty_subset _, fun _ _ _ => Finset.disjoint_empty_left _⟩, fun i => ?_⟩
      rw [(hv i).1]
      exact ⟨WithBot.coe_ne_bot, le_rfl⟩
    · 
      let s := t - k
      have hs : s ≤ n - k := by omega
      have hks : k + s ≤ n := by omega
      have ht_eq : t = k + s := by omega
      let L := ((List.ofFn π).take k).toFinset
      let F := fun i => disposalEnvelope (v i)
      
      have hL_nodup : ((List.ofFn π).take k).Nodup := (List.nodup_ofFn.mpr π.injective).take
      have hL_card : L.card = k := by
        rw [List.toFinset_card_of_nodup hL_nodup, List.length_take, List.length_ofFn, min_eq_left hk]
      have hcard : (Finset.univ \ L).card = n - k := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hL_card]
      let emb := complEmb L k hcard
      have h_in_range : ∀ r : Fin (n - k), ∃ z : Fin (n - k), emb z = π ⟨k + r.1, by omega⟩ := by
        intro r
        have h_mem_sdiff : π ⟨k + r.1, by omega⟩ ∈ (↑(Finset.univ \ L) : Set (Fin n)) := by
          simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and]
          intro hmemL
          obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hmemL)
          rw [List.length_take, List.length_ofFn, min_eq_left hk] at hj
          rw [List.getElem_take, List.getElem_ofFn] at hget
          have hj_eq : j = k + r.1 := congrArg Fin.val (π.injective hget)
          omega
        rw [← Finset.range_orderEmbOfFin (Finset.univ \ L) hcard] at h_mem_sdiff
        exact h_mem_sdiff
      let f : Fin (n - k) → Fin (n - k) := fun r => Classical.choose (h_in_range r)
      have hf : ∀ r : Fin (n - k), emb (f r) = π ⟨k + r.1, by omega⟩ :=
        fun r => Classical.choose_spec (h_in_range r)
      have hf_inj : Function.Injective f := by
        intro r₁ r₂ hfr
        have hemb_eq : emb (f r₁) = emb (f r₂) := congrArg emb hfr
        rw [hf r₁, hf r₂] at hemb_eq
        have hval := congrArg Fin.val (π.injective hemb_eq)
        dsimp only at hval
        exact Fin.ext (by omega)
      let π' : Equiv.Perm (Fin (n - k)) :=
        Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj)
      have hπ' : ∀ r : Fin (n - k), complEmb L k hcard (π' r) = π ⟨k + r.1, by omega⟩ :=
        fun r => hf r
      
      have h_sel_sub : ∀ {d : ℕ} (alg_d : DetSelectionAlg d) (w : ItemValuation d)
          (π_s : Equiv.Perm (Fin d)) (r : ℕ) (hr : r ≤ d),
          (runDetSelectionSteps alg_d w π_s r hr).2 ⊆ ((List.ofFn π_s).take r).toFinset := by
        intro d alg_d w π_s r
        induction r with
        | zero => intro _; simp [runDetSelectionSteps]
        | succ r ih =>
          intro hr
          have hr' := Nat.le_of_succ_le hr
          have h_sub_prev : ((List.ofFn π_s).take r).toFinset ⊆
              ((List.ofFn π_s).take (r + 1)).toFinset := by
            intro z hz
            have h_take : (List.ofFn π_s).take r = ((List.ofFn π_s).take (r + 1)).take r := by
              rw [List.take_take, min_eq_left (Nat.le_succ r)]
            rw [h_take] at hz
            exact List.mem_toFinset.mpr
              (List.take_subset r ((List.ofFn π_s).take (r + 1)) (List.mem_toFinset.mp hz))
          have h_mem_r : π_s ⟨r, hr⟩ ∈ ((List.ofFn π_s).take (r + 1)).toFinset := by
            have hr_len : r < ((List.ofFn π_s).take (r + 1)).length := by
              simp [List.length_take, List.length_ofFn, min_eq_left hr]
            have hm := List.getElem_mem hr_len
            simp only [List.getElem_take, List.getElem_ofFn] at hm
            exact List.mem_toFinset.mpr hm
          dsimp only [runDetSelectionSteps]
          split_ifs
          · exact Finset.insert_subset_iff.mpr ⟨h_mem_r, (ih hr').trans h_sub_prev⟩
          · exact (ih hr').trans h_sub_prev
      dsimp only
      rw [h_wsteps_congr (frozenRoutingDet selAlg (c, η_fam)) v π t (k + s) ht hks ht_eq,
          h_wsteps_fst (frozenRoutingDet selAlg (c, η_fam)) v π (k + s) hks,
          h_post_sample v c η_fam π hcard π' hπ' s hs hks]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · 
        intro i g hg
        have hg_map := (Finset.mem_inter.mp hg).1
        obtain ⟨z, hz_acc, rfl⟩ := Finset.mem_map.mp hg_map
        have hz_take := h_sel_sub _ _ π' s hs hz_acc
        obtain ⟨u, hu_len, hget⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hz_take)
        rw [List.length_take, List.length_ofFn, min_eq_left hs] at hu_len
        rw [List.getElem_take, List.getElem_ofFn] at hget
        subst hget
        rw [hπ' ⟨u, by omega⟩]
        have huk_len : k + u < ((List.ofFn π).take (k + s)).length := by
          rw [List.length_take, List.length_ofFn, min_eq_left hks]; omega
        have hm := List.getElem_mem huk_len
        simp only [List.getElem_take, List.getElem_ofFn] at hm
        exact List.mem_toFinset.mpr hm
      · 
        intro i j hij
        refine Finset.disjoint_left.mpr (fun g hgi hgj => ?_)
        have hri := (Finset.mem_filter.mp (Finset.mem_inter.mp hgi).2).2
        have hrj := (Finset.mem_filter.mp (Finset.mem_inter.mp hgj).2).2
        rw [hri] at hrj
        exact hij (Option.some.inj hrj)
      · 
        intro i
        exact h_sel_safe (n - k) (poolVal (v i) emb (R_pool F L i))
          (h_pool_gs i (n - k) emb (R_pool F L i)) (η_fam k_fin) π' s hs

theorem frozen_routing_expected_welfare_decomp : ∀ (n m : ℕ) (selAlg : ∀ d : ℕ, OnlineSelectionAlg d) (v : Fin m → ItemValuation n)
      (h_prob : IsProbabilityMeasure (frozenSeedMeasure n selAlg))
      (h_meas : ∀ (prev : List (Fin n)) (x : Fin n) (bundles : Fin m → Finset (Fin n))
        (oracle : Fin m → {T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → WithBot ℝ)
        (dec : Option (Fin m)),
        MeasurableSet {ω : FrozenSeed n selAlg |
          (frozenRoutingDet selAlg ω).step prev x bundles oracle = dec}),
      (∀ (d : ℕ) (w : ItemValuation d), IsGSValuation w →
        (∀ (ω_s : (selAlg d).Seed) (π_s : Equiv.Perm (Fin d)),
          w (runDetSelection ((selAlg d).det ω_s) w π_s) ≠ ⊥) ∧
        (((invE * optVal w : ℝ) : WithBot ℝ) ≤ expectedSelectionVal (selAlg d) w)) →
      (∀ i : Fin m, IsGSValuation (v i)) →
      (∀ (i : Fin m) (d : ℕ) (emb : Fin d ↪ Fin n) (R_i : Finset (Fin n)),
        R_i ⊆ Finset.univ.map emb →
          IsGSValuation (poolVal (v i) emb R_i) ∧
          optVal (poolVal (v i) emb R_i) = disposalEnvelope (v i) R_i) →
      (∀ (c : Fin n → ℝ) (η_fam : (k : Fin (n + 1)) → (selAlg (n - k.1)).Seed)
        (π : Equiv.Perm (Fin n)),
        let k_fin := K_sample c
        let k := k_fin.1
        let L := ((List.ofFn π).take k).toFinset
        let F := fun i => disposalEnvelope (v i)
        ∀ (hcard : (Finset.univ \ L).card = n - k) (π' : Equiv.Perm (Fin (n - k))),
          (∀ s : Fin (n - k), complEmb L k hcard (π' s) = π ⟨k + s.1, by omega⟩) →
          runDetWelfare (frozenRoutingDet selAlg (c, η_fam)) v π =
            fun i =>
              ((runDetSelection ((selAlg (n - k)).det (η_fam k_fin))
                (poolVal (v i) (complEmb L k hcard) (R_pool F L i)) π').map
                  (complEmb L k hcard)) ∩ R_pool F L i) →
      (∀ (ω : FrozenSeed n selAlg) (π : Equiv.Perm (Fin n)) (i : Fin m),
        v i (runDetWelfare (frozenRoutingDet selAlg ω) v π i) ≠ ⊥) →
      let alg : OnlineWelfareAlg n m :=
        { Seed := FrozenSeed n selAlg
          seedMeasure := frozenSeedMeasure n selAlg
          isProb := h_prob
          det := frozenRoutingDet selAlg
          meas_step := h_meas }
      let F := fun i => disposalEnvelope (v i)
      ((invE * (∑ L : Finset (Fin n), bernProb n lam L * (∑ i : Fin m, F i (R_pool F L i))) : ℝ) :
        WithBot ℝ) ≤ expectedWelfareVal alg v :=
by
  intro n m selAlg v h_prob h_meas h_sel _hv h_pool h_traj h_safe alg F
  haveI : IsProbabilityMeasure (frozenSeedMeasure n selAlg) := h_prob

  
  have h_sqrt2_ge : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have h_sqrt2_le : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  have hlam0 : 0 ≤ lam := by dsimp [lam]; linarith
  have hlam1 : lam ≤ 1 := by dsimp [lam]; linarith
  have h1lam0 : 0 ≤ 1 - lam := by linarith
  have h_bern_nonneg : ∀ L : Finset (Fin n), 0 ≤ bernProb n lam L := by
    intro L
    exact mul_nonneg (pow_nonneg hlam0 _) (pow_nonneg h1lam0 _)

  
  have h_coe_realVal : ∀ {d' : ℕ} (w : ItemValuation d') (S : Finset (Fin d')),
      w S ≠ ⊥ → ((realVal w S : ℝ) : WithBot ℝ) = w S := by
    intro d' w S hS
    obtain ⟨r, hr⟩ := WithBot.ne_bot_iff_exists.mp hS
    rw [realVal, ← hr]
    simp only [WithBot.unbotD_coe]

  have h_reach_unbot : ∀ (π : Equiv.Perm (Fin n)) (X : Fin m → Finset (Fin n)),
      (∃ ω : FrozenSeed n selAlg, runDetWelfare (frozenRoutingDet selAlg ω) v π = X) →
      allocWelfare v X ≠ ⊥ ∧
      (allocWelfare v X).unbotD 0 = ∑ i : Fin m, realVal (v i) (X i) := by
    rintro π X ⟨ω, rfl⟩
    have h_eq : allocWelfare v (runDetWelfare (frozenRoutingDet selAlg ω) v π) =
        ((∑ i : Fin m, realVal (v i) (runDetWelfare (frozenRoutingDet selAlg ω) v π i) : ℝ) :
          WithBot ℝ) := by
      unfold allocWelfare
      rw [WithBot.coe_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact (h_coe_realVal (v i) _ (h_safe ω π i)).symm
    rw [h_eq]
    exact ⟨WithBot.coe_ne_bot, by simp only [WithBot.unbotD_coe]⟩

  have h_no_bot : ¬ ∃ X : Fin m → Finset (Fin n),
      0 < algWelfareProb alg v X ∧ allocWelfare v X = ⊥ := by
    rintro ⟨X, hpos, hbot⟩
    have h_all_empty : ∀ π : Equiv.Perm (Fin n),
        {ω : alg.Seed | runDetWelfare (alg.det ω) v π = X} = ∅ := by
      intro π
      by_contra hne
      obtain ⟨ω, hω⟩ := Set.nonempty_iff_ne_empty.mpr hne
      exact (h_reach_unbot π X ⟨ω, hω⟩).1 hbot
    have hprob0 : algWelfareProb alg v X = 0 := by
      unfold algWelfareProb
      simp [h_all_empty]
    linarith

  have h_term_unbot : ∀ (π : Equiv.Perm (Fin n)) (X : Fin m → Finset (Fin n)),
      (frozenSeedMeasure n selAlg).real
        {ω : FrozenSeed n selAlg | runDetWelfare (frozenRoutingDet selAlg ω) v π = X} *
        (allocWelfare v X).unbotD 0 =
      (frozenSeedMeasure n selAlg).real
        {ω : FrozenSeed n selAlg | runDetWelfare (frozenRoutingDet selAlg ω) v π = X} *
        (∑ i : Fin m, realVal (v i) (X i)) := by
    intro π X
    by_cases hemp :
        {ω : FrozenSeed n selAlg | runDetWelfare (frozenRoutingDet selAlg ω) v π = X} = ∅
    · simp [hemp]
    · obtain ⟨ω, hω⟩ := Set.nonempty_iff_ne_empty.mpr hemp
      rw [(h_reach_unbot π X ⟨ω, hω⟩).2]

  unfold expectedWelfareVal
  rw [if_neg h_no_bot, WithBot.coe_le_coe]
  have h_rhs_expand :
      (∑ X : Fin m → Finset (Fin n), algWelfareProb alg v X * (allocWelfare v X).unbotD 0) =
      (1 / (Nat.factorial n : ℝ)) *
        ∑ π : Equiv.Perm (Fin n), ∑ X : Fin m → Finset (Fin n),
          (frozenSeedMeasure n selAlg).real
            {ω : FrozenSeed n selAlg | runDetWelfare (frozenRoutingDet selAlg ω) v π = X} *
            (∑ i : Fin m, realVal (v i) (X i)) := by
    unfold algWelfareProb
    dsimp only [alg]
    simp_rw [mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl (fun π _ => ?_)
    refine Finset.sum_congr rfl (fun X _ => h_term_unbot π X)
  rw [h_rhs_expand]

  
  have h_welf_fst : ∀ (det_a : DetWelfareAlg n m) (π : Equiv.Perm (Fin n)) (t : ℕ) (ht : t ≤ n),
      (runDetWelfareSteps det_a v π t ht).1 = (List.ofFn π).take t := by
    intro det_a π t
    induction t with
    | zero =>
      intro _
      simp [runDetWelfareSteps]
    | succ t ih =>
      intro ht
      have h1 : (runDetWelfareSteps det_a v π (t + 1) ht).1 =
          (runDetWelfareSteps det_a v π t (Nat.le_of_succ_le ht)).1 ++ [π ⟨t, ht⟩] := rfl
      have hlt : t < n := ht
      rw [h1, ih (Nat.le_of_succ_le ht), List.take_add_one, List.getElem?_ofFn, dif_pos hlt]
      rfl

  have h_welf_step_prev : ∀ (det_a : DetWelfareAlg n m) (p₁ p₂ : List (Fin n))
      (x : Fin n) (B₀ : Fin m → Finset (Fin n)),
      p₁ = p₂ →
      det_a.step p₁ x B₀ (fun i ⟨T, _⟩ => v i T) =
      det_a.step p₂ x B₀ (fun i ⟨T, _⟩ => v i T) := by
    rintro _ _ _ _ _ rfl
    rfl

  have h_meas_welf : ∀ (π : Equiv.Perm (Fin n)) (X : Fin m → Finset (Fin n)),
      MeasurableSet {ω : FrozenSeed n selAlg |
        runDetWelfare (frozenRoutingDet selAlg ω) v π = X} := by
    intro π X
    have h_ind : ∀ (t : ℕ) (ht : t ≤ n) (B : Fin m → Finset (Fin n)),
        MeasurableSet {ω : FrozenSeed n selAlg |
          (runDetWelfareSteps (frozenRoutingDet selAlg ω) v π t ht).2 = B} := by
      intro t
      induction t with
      | zero =>
        intro _ B
        change MeasurableSet {ω : FrozenSeed n selAlg | (fun _ : Fin m => (∅ : Finset (Fin n))) = B}
        by_cases hB : (fun _ : Fin m => (∅ : Finset (Fin n))) = B <;> simp [hB]
      | succ t ih =>
        intro ht B
        let L_t := (List.ofFn π).take t
        let x := π ⟨t, ht⟩
        let oracle : Fin m → {T : Finset (Fin n) // T ⊆ insert x L_t.toFinset} → WithBot ℝ :=
          fun i ⟨T, _⟩ => v i T
        let upd (B₀ : Fin m → Finset (Fin n)) (dec : Option (Fin m)) : Fin m → Finset (Fin n) :=
          match dec with
          | none => B₀
          | some i => Function.update B₀ i (insert x (B₀ i))
        have h_eq : {ω : FrozenSeed n selAlg |
            (runDetWelfareSteps (frozenRoutingDet selAlg ω) v π (t + 1) ht).2 = B} =
            ⋃ (B₀ : Fin m → Finset (Fin n)) (dec : Option (Fin m)),
              if upd B₀ dec = B then
                {ω | (runDetWelfareSteps (frozenRoutingDet selAlg ω) v π t (Nat.le_of_succ_le ht)).2 = B₀} ∩
                {ω | (frozenRoutingDet selAlg ω).step L_t x B₀ oracle = dec}
              else ∅ := by
          ext ω
          have h_fst := h_welf_fst (frozenRoutingDet selAlg ω) π t (Nat.le_of_succ_le ht)
          let B_cur := (runDetWelfareSteps (frozenRoutingDet selAlg ω) v π t (Nat.le_of_succ_le ht)).2
          have h_step_eq := h_welf_step_prev (frozenRoutingDet selAlg ω) _ L_t x B_cur h_fst
          simp only [Set.mem_setOf_eq, Set.mem_iUnion]
          change upd B_cur ((frozenRoutingDet selAlg ω).step
            (runDetWelfareSteps (frozenRoutingDet selAlg ω) v π t (Nat.le_of_succ_le ht)).1
            x B_cur (fun i ⟨T, _⟩ => v i T)) = B ↔ _
          rw [h_step_eq]
          refine ⟨fun h => ⟨B_cur, (frozenRoutingDet selAlg ω).step L_t x B_cur oracle, ?_⟩, ?_⟩
          · rw [if_pos h]; exact ⟨rfl, rfl⟩
          · rintro ⟨B₀, dec, hmem⟩
            split_ifs at hmem with hupd
            · obtain ⟨hB₀, hdec⟩ : B_cur = B₀ ∧
                  (frozenRoutingDet selAlg ω).step L_t x B₀ oracle = dec := hmem
              rw [hB₀, hdec]
              exact hupd
            · exact False.elim hmem
        rw [h_eq]
        refine MeasurableSet.iUnion (fun B₀ => MeasurableSet.iUnion (fun dec => ?_))
        split_ifs
        · exact (ih (Nat.le_of_succ_le ht) B₀).inter (h_meas L_t x B₀ oracle dec)
        · exact MeasurableSet.empty
    exact h_ind n (le_refl n) X

  have h_meas_sel : ∀ (d : ℕ) (alg_d : OnlineSelectionAlg d) (w : ItemValuation d)
      (π' : Equiv.Perm (Fin d)) (S' : Finset (Fin d)),
      MeasurableSet {η : alg_d.Seed | runDetSelection (alg_d.det η) w π' = S'} := by
    intro d alg_d w π' S'
    have h_sel_fst : ∀ (det_s : DetSelectionAlg d) (s : ℕ) (hs : s ≤ d),
        (runDetSelectionSteps det_s w π' s hs).1 = (List.ofFn π').take s := by
      intro det_s s
      induction s with
      | zero =>
        intro _
        simp [runDetSelectionSteps]
      | succ s ih =>
        intro hs
        have h1 : (runDetSelectionSteps det_s w π' (s + 1) hs).1 =
            (runDetSelectionSteps det_s w π' s (Nat.le_of_succ_le hs)).1 ++ [π' ⟨s, hs⟩] := rfl
        have hlt : s < d := hs
        rw [h1, ih (Nat.le_of_succ_le hs), List.take_add_one, List.getElem?_ofFn, dif_pos hlt]
        rfl
    have h_sel_step_prev : ∀ (det_s : DetSelectionAlg d) (p₁ p₂ : List (Fin d))
        (y : Fin d) (A₀ : Finset (Fin d)),
        p₁ = p₂ →
        det_s.step p₁ y A₀ (fun ⟨T, _⟩ => w T) =
        det_s.step p₂ y A₀ (fun ⟨T, _⟩ => w T) := by
      rintro _ _ _ _ _ rfl
      rfl
    have h_ind : ∀ (s : ℕ) (hs : s ≤ d) (A : Finset (Fin d)),
        MeasurableSet {η : alg_d.Seed |
          (runDetSelectionSteps (alg_d.det η) w π' s hs).2 = A} := by
      intro s
      induction s with
      | zero =>
        intro _ A
        change MeasurableSet {η : alg_d.Seed | (∅ : Finset (Fin d)) = A}
        by_cases hA : (∅ : Finset (Fin d)) = A <;> simp [hA]
      | succ s ih =>
        intro hs A
        let L_s := (List.ofFn π').take s
        let y := π' ⟨s, hs⟩
        let oracle : {T : Finset (Fin d) // T ⊆ insert y L_s.toFinset} → WithBot ℝ :=
          fun ⟨T, _⟩ => w T
        let upd (A₀ : Finset (Fin d)) (b : Bool) : Finset (Fin d) :=
          if b then insert y A₀ else A₀
        have h_eq : {η : alg_d.Seed |
            (runDetSelectionSteps (alg_d.det η) w π' (s + 1) hs).2 = A} =
            ⋃ (A₀ : Finset (Fin d)) (b : Bool),
              if upd A₀ b = A then
                {η | (runDetSelectionSteps (alg_d.det η) w π' s (Nat.le_of_succ_le hs)).2 = A₀} ∩
                {η | (alg_d.det η).step L_s y A₀ oracle = b}
              else ∅ := by
          ext η
          have h_fst := h_sel_fst (alg_d.det η) s (Nat.le_of_succ_le hs)
          let A_cur := (runDetSelectionSteps (alg_d.det η) w π' s (Nat.le_of_succ_le hs)).2
          have h_step_eq := h_sel_step_prev (alg_d.det η) _ L_s y A_cur h_fst
          simp only [Set.mem_setOf_eq, Set.mem_iUnion]
          change upd A_cur ((alg_d.det η).step
            (runDetSelectionSteps (alg_d.det η) w π' s (Nat.le_of_succ_le hs)).1
            y A_cur (fun ⟨T, _⟩ => w T)) = A ↔ _
          rw [h_step_eq]
          refine ⟨fun h => ⟨A_cur, (alg_d.det η).step L_s y A_cur oracle, ?_⟩, ?_⟩
          · rw [if_pos h]; exact ⟨rfl, rfl⟩
          · rintro ⟨A₀, b, hmem⟩
            split_ifs at hmem with hupd
            · obtain ⟨hA₀, hb⟩ : A_cur = A₀ ∧
                  (alg_d.det η).step L_s y A₀ oracle = b := hmem
              rw [hA₀, hb]
              exact hupd
            · exact False.elim hmem
        rw [h_eq]
        refine MeasurableSet.iUnion (fun A₀ => MeasurableSet.iUnion (fun b => ?_))
        split_ifs
        · exact (ih (Nat.le_of_succ_le hs) A₀).inter (alg_d.meas_step L_s y A₀ oracle b)
        · exact MeasurableSet.empty
    exact h_ind d (le_refl d) S'

  have h_slice_law : ∀ (k_fin : Fin (n + 1)),
      MeasurableSet {c : Fin n → ℝ | K_sample c = k_fin} ∧
      ∀ (E : Set ((selAlg (n - k_fin.1)).Seed)), MeasurableSet E →
        (frozenSeedMeasure n selAlg).real
          ({c : Fin n → ℝ | K_sample c = k_fin} ×ˢ
            {η_fam : (k : Fin (n + 1)) → (selAlg (n - k.1)).Seed | η_fam k_fin ∈ E}) =
        ((Nat.choose n k_fin.1 : ℝ) * lam ^ k_fin.1 * (1 - lam) ^ (n - k_fin.1)) *
          ((selAlg (n - k_fin.1)).seedMeasure).real E := by
    intro k_fin
    let ν₁ : Measure ℝ := (ENNReal.ofReal (1 : ℝ))⁻¹ • volume.restrict (Set.Icc (0 : ℝ) 1)
    have hν₁_prob : IsProbabilityMeasure ν₁ := by
      rw [MeasureTheory.isProbabilityMeasure_iff]
      simp [ν₁, Real.volume_Icc]
    haveI : IsProbabilityMeasure ν₁ := hν₁_prob
    haveI : IsProbabilityMeasure (unifCubeMeasure n 1) := by
      unfold unifCubeMeasure; infer_instance
    let I : Set ℝ := Set.Ico (0 : ℝ) lam
    have hI_inter : I ∩ Set.Icc (0 : ℝ) 1 = I := by
      ext x
      simp only [I, Set.mem_inter_iff, Set.mem_Ico, Set.mem_Icc]
      exact ⟨fun h => h.1, fun ⟨h0, hlt⟩ => ⟨⟨h0, hlt⟩, ⟨h0, hlt.le.trans hlam1⟩⟩⟩
    have hν₁_I : ν₁ I = ENNReal.ofReal lam := by
      simp [ν₁, I, Measure.restrict_apply measurableSet_Ico, hI_inter, Real.volume_Ico]
    have hν₁_Ic : ν₁ Iᶜ = ENNReal.ofReal (1 - lam) := by
      rw [prob_compl_eq_one_sub measurableSet_Ico, hν₁_I, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_sub 1 hlam0]
    let Rect (J : Finset (Fin n)) : Set (Fin n → ℝ) :=
      Set.univ.pi (fun j : Fin n => if j ∈ J then I else Iᶜ)
    have hRect_meas : ∀ J : Finset (Fin n), MeasurableSet (Rect J) := by
      intro J
      refine MeasurableSet.univ_pi (fun j => ?_)
      by_cases hj : j ∈ J <;> simp [hj, I, measurableSet_Ico, measurableSet_Ico.compl]
    have hRect_mem : ∀ (J : Finset (Fin n)) (c : Fin n → ℝ),
        c ∈ Rect J ↔ Finset.univ.filter (fun j : Fin n => 0 ≤ c j ∧ c j < lam) = J := by
      intro J c
      simp only [Rect, I, Set.mem_univ_pi, Finset.ext_iff, Finset.mem_filter, Finset.mem_univ,
        true_and]
      refine forall_congr' (fun j => ?_)
      by_cases hj : j ∈ J <;> simp [hj]
    have hK_eq_biUnion : {c : Fin n → ℝ | K_sample c = k_fin} =
        ⋃ J ∈ (Finset.univ : Finset (Fin n)).powersetCard k_fin.1, Rect J := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_powersetCard, Finset.subset_univ,
        true_and, hRect_mem, K_sample, Fin.ext_iff]
      exact ⟨fun h => ⟨_, h, rfl⟩, by rintro ⟨J, hcard_J, h_eq⟩; rw [h_eq]; exact hcard_J⟩
    have hK_meas : MeasurableSet {c : Fin n → ℝ | K_sample c = k_fin} := by
      rw [hK_eq_biUnion]
      exact Finset.measurableSet_biUnion _ (fun J _ => hRect_meas J)
    have hRect_real : ∀ J : Finset (Fin n),
        (unifCubeMeasure n 1).real (Rect J) = lam ^ J.card * (1 - lam) ^ (n - J.card) := by
      intro J
      have h_pi : unifCubeMeasure n 1 (Rect J) =
          ENNReal.ofReal (lam ^ J.card * (1 - lam) ^ (n - J.card)) := by
        unfold unifCubeMeasure
        rw [MeasureTheory.Measure.pi_pi]
        have h_prod_eq : (∏ j : Fin n,
            ((ENNReal.ofReal (1 : ℝ))⁻¹ • volume.restrict (Set.Icc (0 : ℝ) 1))
              (if j ∈ J then I else Iᶜ)) =
            ∏ j : Fin n, ENNReal.ofReal (if j ∈ J then lam else 1 - lam) := by
          refine Finset.prod_congr rfl (fun j _ => ?_)
          change ν₁ (if j ∈ J then I else Iᶜ) = _
          by_cases hj : j ∈ J <;> simp [hj, hν₁_I, hν₁_Ic]
        rw [h_prod_eq]
        rw [← ENNReal.ofReal_prod_of_nonneg
          (fun j _ => by by_cases hj : j ∈ J <;> simp [hj, hlam0, h1lam0])]
        congr 1
        rw [Finset.prod_ite]
        have hf1 : (Finset.univ : Finset (Fin n)).filter (fun x => x ∈ J) = J := by
          ext x; simp
        have hf2 : ((Finset.univ : Finset (Fin n)).filter (fun x => x ∉ J)).card = n - J.card := by
          have heq : (Finset.univ : Finset (Fin n)).filter (fun x => x ∉ J) = Finset.univ \ J := by
            ext x; simp
          rw [heq, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
        simp [hf1, hf2]
      rw [MeasureTheory.measureReal_def, h_pi,
        ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg hlam0 _) (pow_nonneg h1lam0 _))]
    have hRect_disj : Set.PairwiseDisjoint
        ((Finset.univ : Finset (Fin n)).powersetCard k_fin.1 : Set (Finset (Fin n))) Rect := by
      intro J₁ _ J₂ _ hne
      rw [Function.onFun, Set.disjoint_left]
      intro c hc₁ hc₂
      exact hne ((hRect_mem J₁ c).mp hc₁ ▸ (hRect_mem J₂ c).mp hc₂)
    have hK_real : (unifCubeMeasure n 1).real {c : Fin n → ℝ | K_sample c = k_fin} =
        (Nat.choose n k_fin.1 : ℝ) * lam ^ k_fin.1 * (1 - lam) ^ (n - k_fin.1) := by
      rw [hK_eq_biUnion, MeasureTheory.measureReal_biUnion_finset hRect_disj (fun J _ => hRect_meas J)]
      have h_congr : ∀ J ∈ (Finset.univ : Finset (Fin n)).powersetCard k_fin.1,
          (unifCubeMeasure n 1).real (Rect J) = lam ^ k_fin.1 * (1 - lam) ^ (n - k_fin.1) := by
        intro J hJ
        rw [hRect_real J, (Finset.mem_powersetCard.mp hJ).2]
      rw [Finset.sum_congr rfl h_congr, Finset.sum_const, Finset.card_powersetCard,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
    refine ⟨hK_meas, fun E hE => ?_⟩
    let μ_η := Measure.pi (fun k : Fin (n + 1) => (selAlg (n - k.1)).seedMeasure)
    haveI : IsProbabilityMeasure μ_η := inferInstance
    change ((unifCubeMeasure n 1).prod μ_η).real
      ({c : Fin n → ℝ | K_sample c = k_fin} ×ˢ ((Function.eval k_fin) ⁻¹' E)) = _
    rw [MeasureTheory.measureReal_prod_prod, hK_real]
    congr 1
    have h_mp := MeasureTheory.measurePreserving_eval
      (fun k : Fin (n + 1) => (selAlg (n - k.1)).seedMeasure) k_fin
    rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
      h_mp.measure_preimage hE.nullMeasurableSet]

  
  have h_perm_split : ∀ (k : ℕ) (hk : k ≤ n) (Φ : Equiv.Perm (Fin n) → ℝ)
      (Ψ : Finset (Fin n) → Equiv.Perm (Fin (n - k)) → ℝ),
      (∀ (π : Equiv.Perm (Fin n)),
        let L := ((List.ofFn π).take k).toFinset
        ∀ (hcard : (Finset.univ \ L).card = n - k) (π' : Equiv.Perm (Fin (n - k))),
          (∀ s : Fin (n - k), complEmb L k hcard (π' s) = π ⟨k + s.1, by omega⟩) →
          Φ π = Ψ L π') →
      (∑ π : Equiv.Perm (Fin n), Φ π) =
        (Nat.factorial k : ℝ) *
          ∑ L ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
            ∑ π' : Equiv.Perm (Fin (n - k)), Ψ L π' := by
    intro k hk Φ Ψ h_agree
    let S_k := (Finset.univ : Finset (Fin n)).powersetCard k
    let Dom_k := Σ (_ : {L : Finset (Fin n) // L ∈ S_k}),
      Equiv.Perm (Fin k) × Equiv.Perm (Fin (n - k))
    have hL_card : ∀ L_sub : {L : Finset (Fin n) // L ∈ S_k}, L_sub.1.card = k :=
      fun L_sub => (Finset.mem_powersetCard.mp L_sub.2).2
    have hcard_L : ∀ L_sub : {L : Finset (Fin n) // L ∈ S_k},
        (Finset.univ \ L_sub.1).card = n - k := by
      intro L_sub
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hL_card L_sub]
    let rawFn (u : Dom_k) (j : Fin n) : Fin n :=
      if hj : j.1 < k then
        (u.1.1.orderEmbOfFin (hL_card u.1)) (u.2.1 ⟨j.1, hj⟩)
      else
        complEmb u.1.1 k (hcard_L u.1) (u.2.2 ⟨j.1 - k, by omega⟩)
    have h_raw_inj : ∀ u : Dom_k, Function.Injective (rawFn u) := by
      intro u j₁ j₂ heq
      by_cases hj₁ : j₁.1 < k <;> by_cases hj₂ : j₂.1 < k
      · simp only [rawFn, dif_pos hj₁, dif_pos hj₂] at heq
        have h1 := u.2.1.injective ((u.1.1.orderEmbOfFin (hL_card u.1)).injective heq)
        exact Fin.ext (Fin.mk.inj h1)
      · simp only [rawFn, dif_pos hj₁, dif_neg hj₂] at heq
        have hm1 : (u.1.1.orderEmbOfFin (hL_card u.1)) (u.2.1 ⟨j₁.1, hj₁⟩) ∈ u.1.1 :=
          Finset.orderEmbOfFin_mem u.1.1 (hL_card u.1) _
        have hm2 : complEmb u.1.1 k (hcard_L u.1) (u.2.2 ⟨j₂.1 - k, by omega⟩) ∈
            Finset.univ \ u.1.1 :=
          Finset.orderEmbOfFin_mem (Finset.univ \ u.1.1) (hcard_L u.1) _
        rw [heq] at hm1
        exact False.elim ((Finset.mem_sdiff.mp hm2).2 hm1)
      · simp only [rawFn, dif_neg hj₁, dif_pos hj₂] at heq
        have hm1 : complEmb u.1.1 k (hcard_L u.1) (u.2.2 ⟨j₁.1 - k, by omega⟩) ∈
            Finset.univ \ u.1.1 :=
          Finset.orderEmbOfFin_mem (Finset.univ \ u.1.1) (hcard_L u.1) _
        have hm2 : (u.1.1.orderEmbOfFin (hL_card u.1)) (u.2.1 ⟨j₂.1, hj₂⟩) ∈ u.1.1 :=
          Finset.orderEmbOfFin_mem u.1.1 (hL_card u.1) _
        rw [← heq] at hm2
        exact False.elim ((Finset.mem_sdiff.mp hm1).2 hm2)
      · simp only [rawFn, dif_neg hj₁, dif_neg hj₂] at heq
        have h1 := u.2.2.injective ((complEmb u.1.1 k (hcard_L u.1)).injective heq)
        have h2 : j₁.1 - k = j₂.1 - k := congrArg Fin.val h1
        exact Fin.ext (by omega)
    let buildPerm (u : Dom_k) : Equiv.Perm (Fin n) :=
      Equiv.ofBijective (rawFn u) (Finite.injective_iff_bijective.mp (h_raw_inj u))
    have h_apply : ∀ (u : Dom_k) (j : Fin n), buildPerm u j = rawFn u j := fun _ _ => rfl
    have h_take : ∀ u : Dom_k, ((List.ofFn (buildPerm u)).take k).toFinset = u.1.1 := by
      intro u
      have h_sub : ((List.ofFn (buildPerm u)).take k).toFinset ⊆ u.1.1 := by
        intro x hx
        rw [List.mem_toFinset, List.mem_iff_getElem] at hx
        obtain ⟨idx, hidx, rfl⟩ := hx
        have hlen : ((List.ofFn (buildPerm u)).take k).length = k := by
          rw [List.length_take, List.length_ofFn, min_eq_left hk]
        have hidx_k : idx < k := hlen ▸ hidx
        have hidx_n : idx < n := Nat.lt_of_lt_of_le hidx_k hk
        rw [List.getElem_take, List.getElem_ofFn, h_apply]
        simp only [rawFn, dif_pos hidx_k]
        exact Finset.orderEmbOfFin_mem u.1.1 (hL_card u.1) _
      have h_nodup : ((List.ofFn (buildPerm u)).take k).Nodup :=
        (List.nodup_ofFn.mpr (buildPerm u).injective).take
      have h_card : (((List.ofFn (buildPerm u)).take k).toFinset).card = u.1.1.card := by
        rw [List.toFinset_card_of_nodup h_nodup, List.length_take, List.length_ofFn,
          min_eq_left hk, hL_card u.1]
      exact Finset.eq_of_subset_of_card_le h_sub h_card.ge
    have h_tail : ∀ (u : Dom_k) (s : Fin (n - k)),
        complEmb u.1.1 k (hcard_L u.1) (u.2.2 s) = buildPerm u ⟨k + s.1, by omega⟩ := by
      intro u s
      rw [h_apply]
      have hnot : ¬ (k + s.1 < k) := by omega
      simp only [rawFn, dif_neg hnot]
      have hfin : (⟨k + s.1 - k, by omega⟩ : Fin (n - k)) = s := by
        ext; dsimp; omega
      rw [hfin]
    have h_build_inj : Function.Injective buildPerm := by
      rintro ⟨L₁, σ₁, π'₁⟩ ⟨L₂, σ₂, π'₂⟩ heq
      have hL_val : L₁.1 = L₂.1 := by
        rw [← h_take ⟨L₁, σ₁, π'₁⟩, ← h_take ⟨L₂, σ₂, π'₂⟩, heq]
      have hL_eq : L₁ = L₂ := Subtype.ext hL_val
      subst hL_eq
      have hσ_eq : σ₁ = σ₂ := by
        ext a
        have ha_n : a.1 < n := Nat.lt_of_lt_of_le a.2 hk
        have hpt := Equiv.congr_fun heq ⟨a.1, ha_n⟩
        rw [h_apply, h_apply] at hpt
        simp only [rawFn, dif_pos a.2] at hpt
        exact congrArg Fin.val ((L₁.1.orderEmbOfFin (hL_card L₁)).injective hpt)
      have hπ'_eq : π'₁ = π'₂ := by
        ext s
        have hpt := Equiv.congr_fun heq ⟨k + s.1, by omega⟩
        rw [← h_tail ⟨L₁, σ₁, π'₁⟩ s, ← h_tail ⟨L₁, σ₂, π'₂⟩ s] at hpt
        exact congrArg Fin.val ((complEmb L₁.1 k (hcard_L L₁)).injective hpt)
      simp [hσ_eq, hπ'_eq]
    have h_card_dom : Fintype.card Dom_k = Fintype.card (Equiv.Perm (Fin n)) := by
      simp only [Dom_k, S_k, Fintype.card_sigma, Fintype.card_prod, Fintype.card_perm,
        Fintype.card_fin, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        Finset.card_powersetCard, smul_eq_mul, ← mul_assoc,
        Nat.choose_mul_factorial_mul_factorial hk]
    have h_bij : Function.Bijective buildPerm :=
      (Fintype.bijective_iff_injective_and_card buildPerm).mpr ⟨h_build_inj, h_card_dom⟩
    rw [← Fintype.sum_bijective buildPerm h_bij (fun u => Φ (buildPerm u)) Φ (fun _ => rfl)]
    have h_term : ∀ u : Dom_k, Φ (buildPerm u) = Ψ u.1.1 u.2.2 := by
      intro u
      have h_st := h_agree (buildPerm u)
      dsimp only at h_st
      rw [h_take u] at h_st
      exact h_st (hcard_L u.1) u.2.2 (h_tail u)
    simp_rw [h_term]
    rw [Fintype.sum_sigma]
    simp_rw [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    rw [← Finset.sum_coe_sort S_k]

  
  have h_pool_sel_bound : ∀ (d : ℕ) (emb : Fin d ↪ Fin n) (R : Fin m → Finset (Fin n)),
      (∀ i : Fin m, IsGSValuation (poolVal (v i) emb (R i)) ∧
        optVal (poolVal (v i) emb (R i)) = disposalEnvelope (v i) (R i)) →
      invE * (∑ i : Fin m, disposalEnvelope (v i) (R i)) ≤
        (1 / (Nat.factorial d : ℝ)) *
          ∑ π' : Equiv.Perm (Fin d), ∑ X : Fin m → Finset (Fin n),
            (selAlg d).seedMeasure.real
              {η : (selAlg d).Seed |
                (fun i =>
                  ((runDetSelection ((selAlg d).det η) (poolVal (v i) emb (R i)) π').map emb) ∩
                    R i) = X} *
              (∑ i : Fin m, realVal (v i) (X i)) := by
    intro d emb R hR_gs
    let alg_d := selAlg d
    let v_hat : Fin m → ItemValuation d := fun i => poolVal (v i) emb (R i)
    have h_fiber_pi : ∀ π' : Equiv.Perm (Fin d),
        (∑ X : Fin m → Finset (Fin n),
          alg_d.seedMeasure.real
            {η : alg_d.Seed |
              (fun i => ((runDetSelection (alg_d.det η) (v_hat i) π').map emb) ∩ R i) = X} *
            (∑ i : Fin m, realVal (v i) (X i))) =
        ∑ i : Fin m, ∑ S' : Finset (Fin d),
          alg_d.seedMeasure.real {η : alg_d.Seed | runDetSelection (alg_d.det η) (v_hat i) π' = S'} *
            realVal (v_hat i) S' := by
      intro π'
      let hatVec (η : alg_d.Seed) : Fin m → Finset (Fin d) :=
        fun i => runDetSelection (alg_d.det η) (v_hat i) π'
      let allocFromHat (S_vec : Fin m → Finset (Fin d)) : Fin m → Finset (Fin n) :=
        fun i => ((S_vec i).map emb) ∩ R i
      let G (S_vec : Fin m → Finset (Fin d)) : Set alg_d.Seed := {η | hatVec η = S_vec}
      have hG_meas : ∀ S_vec : Fin m → Finset (Fin d), MeasurableSet (G S_vec) := by
        intro S_vec
        have h_eq : G S_vec = ⋂ i : Fin m,
            {η : alg_d.Seed | runDetSelection (alg_d.det η) (v_hat i) π' = S_vec i} := by
          ext η; simp [G, hatVec, funext_iff]
        rw [h_eq]
        exact MeasurableSet.iInter (fun i => h_meas_sel d alg_d (v_hat i) π' (S_vec i))
      have hG_disj : ∀ (U_s : Finset (Fin m → Finset (Fin d))),
          Set.PairwiseDisjoint (U_s : Set (Fin m → Finset (Fin d))) G := by
        intro U_s S₁ _ S₂ _ hne
        rw [Function.onFun, Set.disjoint_left]
        intro η h₁ h₂
        exact hne (h₁.symm.trans h₂)
      have h_step1 :
          (∑ X : Fin m → Finset (Fin n),
            alg_d.seedMeasure.real {η : alg_d.Seed | allocFromHat (hatVec η) = X} *
              (∑ i : Fin m, realVal (v i) (X i))) =
          ∑ S_vec : Fin m → Finset (Fin d),
            alg_d.seedMeasure.real (G S_vec) * (∑ i : Fin m, realVal (v_hat i) (S_vec i)) := by
        have h_X_term : ∀ X : Fin m → Finset (Fin n),
            alg_d.seedMeasure.real {η : alg_d.Seed | allocFromHat (hatVec η) = X} *
              (∑ i : Fin m, realVal (v i) (X i)) =
            ∑ S_vec ∈ (Finset.univ : Finset (Fin m → Finset (Fin d))).filter
                (fun S_vec => allocFromHat S_vec = X),
              alg_d.seedMeasure.real (G S_vec) * (∑ i : Fin m, realVal (v_hat i) (S_vec i)) := by
          intro X
          have h_union : {η : alg_d.Seed | allocFromHat (hatVec η) = X} =
              ⋃ S_vec ∈ (Finset.univ : Finset (Fin m → Finset (Fin d))).filter
                (fun S_vec => allocFromHat S_vec = X), G S_vec := by
            ext η
            simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ,
              true_and, G]
            exact ⟨fun h => ⟨hatVec η, h, rfl⟩, by rintro ⟨S_vec, h_al, h_eq⟩; rw [h_eq, h_al]⟩
          rw [h_union,
            MeasureTheory.measureReal_biUnion_finset (hG_disj _) (fun S_vec _ => hG_meas S_vec),
            Finset.sum_mul]
          refine Finset.sum_congr rfl (fun S_vec hS => ?_)
          have h_alloc : allocFromHat S_vec = X := (Finset.mem_filter.mp hS).2
          rw [← h_alloc]
          rfl
        simp_rw [h_X_term]
        exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
      change (∑ X : Fin m → Finset (Fin n),
          alg_d.seedMeasure.real {η : alg_d.Seed | allocFromHat (hatVec η) = X} *
            (∑ i : Fin m, realVal (v i) (X i))) = _
      rw [h_step1]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_fiberwise_of_maps_to
        (g := fun S_vec : Fin m → Finset (Fin d) => S_vec i)
        (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl (fun S' _ => ?_)
      have h_inner : ∀ S_vec ∈ (Finset.univ : Finset (Fin m → Finset (Fin d))).filter
          (fun S_vec => S_vec i = S'),
          alg_d.seedMeasure.real (G S_vec) * realVal (v_hat i) (S_vec i) =
            alg_d.seedMeasure.real (G S_vec) * realVal (v_hat i) S' := by
        intro S_vec hS
        rw [(Finset.mem_filter.mp hS).2]
      rw [Finset.sum_congr rfl h_inner, ← Finset.sum_mul]
      congr 1
      have h_union_i :
          (⋃ S_vec ∈ (Finset.univ : Finset (Fin m → Finset (Fin d))).filter
            (fun S_vec => S_vec i = S'), G S_vec) =
          {η : alg_d.Seed | runDetSelection (alg_d.det η) (v_hat i) π' = S'} := by
        ext η
        simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
          G, hatVec]
        exact ⟨by rintro ⟨S_vec, h_si, h_eq⟩; rw [← h_si]; exact congrFun h_eq i,
          fun h => ⟨hatVec η, h, rfl⟩⟩
      rw [← h_union_i,
        MeasureTheory.measureReal_biUnion_finset (hG_disj _) (fun S_vec _ => hG_meas S_vec)]
    change invE * (∑ i : Fin m, disposalEnvelope (v i) (R i)) ≤
      (1 / (Nat.factorial d : ℝ)) *
        ∑ π' : Equiv.Perm (Fin d), ∑ X : Fin m → Finset (Fin n),
          alg_d.seedMeasure.real
            {η : alg_d.Seed |
              (fun i => ((runDetSelection (alg_d.det η) (v_hat i) π').map emb) ∩ R i) = X} *
            (∑ i : Fin m, realVal (v i) (X i))
    simp_rw [h_fiber_pi]
    have h_swap_pi :
        (1 / (Nat.factorial d : ℝ)) *
          (∑ π' : Equiv.Perm (Fin d), ∑ i : Fin m, ∑ S' : Finset (Fin d),
            alg_d.seedMeasure.real {η : alg_d.Seed | runDetSelection (alg_d.det η) (v_hat i) π' = S'} *
              realVal (v_hat i) S') =
        ∑ i : Fin m, ∑ S' : Finset (Fin d), algSelectionProb alg_d (v_hat i) S' * realVal (v_hat i) S' := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun S' _ => ?_)
      unfold algSelectionProb
      rw [← Finset.sum_mul, ← mul_assoc]
    rw [h_swap_pi, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    obtain ⟨h_gs_i, h_opt_i⟩ := hR_gs i
    obtain ⟨h_sel_safe_i, h_sel_val_i⟩ := h_sel d (v_hat i) h_gs_i
    have h_no_bot_i : ¬ ∃ S' : Finset (Fin d),
        0 < algSelectionProb alg_d (v_hat i) S' ∧ v_hat i S' = ⊥ := by
      rintro ⟨S', hpos, hbot⟩
      have h_emp : ∀ π' : Equiv.Perm (Fin d),
          {η : alg_d.Seed | runDetSelection (alg_d.det η) (v_hat i) π' = S'} = ∅ := by
        intro π'
        by_contra hne
        obtain ⟨η, hη⟩ := Set.nonempty_iff_ne_empty.mpr hne
        exact h_sel_safe_i η π' (hη.symm ▸ hbot)
      have hprob0 : algSelectionProb alg_d (v_hat i) S' = 0 := by
        unfold algSelectionProb
        simp [h_emp]
      linarith
    unfold expectedSelectionVal at h_sel_val_i
    rw [if_neg h_no_bot_i, WithBot.coe_le_coe, h_opt_i] at h_sel_val_i
    exact h_sel_val_i

  
  let U (k_fin : Fin (n + 1)) (π : Equiv.Perm (Fin n)) (X : Fin m → Finset (Fin n)) :
      Set (FrozenSeed n selAlg) :=
    {ω | K_sample ω.1 = k_fin ∧ runDetWelfare (frozenRoutingDet selAlg ω) v π = X}
  have hU_meas : ∀ k_fin π X, MeasurableSet (U k_fin π X) := by
    intro k_fin π X
    have h_eq : U k_fin π X =
        ({c : Fin n → ℝ | K_sample c = k_fin} ×ˢ Set.univ) ∩
        {ω : FrozenSeed n selAlg | runDetWelfare (frozenRoutingDet selAlg ω) v π = X} := by
      ext ⟨c, η_fam⟩; simp [U]
    rw [h_eq]
    exact ((h_slice_law k_fin).1.prod MeasurableSet.univ).inter (h_meas_welf π X)

  have h_part_seed : ∀ (π : Equiv.Perm (Fin n)) (X : Fin m → Finset (Fin n)),
      (frozenSeedMeasure n selAlg).real
        {ω : FrozenSeed n selAlg | runDetWelfare (frozenRoutingDet selAlg ω) v π = X} =
      ∑ k_fin : Fin (n + 1), (frozenSeedMeasure n selAlg).real (U k_fin π X) := by
    intro π X
    have h_union : {ω : FrozenSeed n selAlg | runDetWelfare (frozenRoutingDet selAlg ω) v π = X} =
        ⋃ k_fin : Fin (n + 1), U k_fin π X := by
      ext ω; simp [U]
    have h_disj : Pairwise (fun k₁ k₂ : Fin (n + 1) => Disjoint (U k₁ π X) (U k₂ π X)) := by
      intro k₁ k₂ hne
      rw [Set.disjoint_left]
      intro ω h₁ h₂
      exact hne (h₁.1.symm.trans h₂.1)
    rw [h_union, MeasureTheory.measureReal_iUnion_fintype h_disj (fun k_fin => hU_meas k_fin π X)]

  simp_rw [h_part_seed, Finset.sum_mul]
  have h_pull_k :
      (1 / (Nat.factorial n : ℝ)) *
        (∑ π : Equiv.Perm (Fin n), ∑ X : Fin m → Finset (Fin n), ∑ k_fin : Fin (n + 1),
          (frozenSeedMeasure n selAlg).real (U k_fin π X) * (∑ i : Fin m, realVal (v i) (X i))) =
      ∑ k_fin : Fin (n + 1), (1 / (Nat.factorial n : ℝ)) *
        (∑ π : Equiv.Perm (Fin n), ∑ X : Fin m → Finset (Fin n),
          (frozenSeedMeasure n selAlg).real (U k_fin π X) * (∑ i : Fin m, realVal (v i) (X i))) := by
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin m → Finset (Fin n))))
      (t := (Finset.univ : Finset (Fin (n + 1))))]
    rw [Finset.sum_comm, Finset.mul_sum]
  rw [h_pull_k]

  let E_set (k : ℕ) (L : Finset (Fin n)) (hcard : (Finset.univ \ L).card = n - k)
      (π' : Equiv.Perm (Fin (n - k))) (X : Fin m → Finset (Fin n)) :
      Set ((selAlg (n - k)).Seed) :=
    {η | (fun i =>
      ((runDetSelection ((selAlg (n - k)).det η)
        (poolVal (v i) (complEmb L k hcard) (R_pool F L i)) π').map
          (complEmb L k hcard)) ∩ R_pool F L i) = X}

  have hE_meas : ∀ (k : ℕ) (L : Finset (Fin n)) (hcard : (Finset.univ \ L).card = n - k)
      (π' : Equiv.Perm (Fin (n - k))) (X : Fin m → Finset (Fin n)),
      MeasurableSet (E_set k L hcard π' X) := by
    intro k L hcard π' X
    have h_eq : E_set k L hcard π' X =
        ⋃ (S_vec : Fin m → Finset (Fin (n - k))),
          if (fun i => ((S_vec i).map (complEmb L k hcard)) ∩ R_pool F L i) = X then
            ⋂ i : Fin m, {η : (selAlg (n - k)).Seed |
              runDetSelection ((selAlg (n - k)).det η)
                (poolVal (v i) (complEmb L k hcard) (R_pool F L i)) π' = S_vec i}
          else ∅ := by
      ext η
      simp only [E_set, Set.mem_setOf_eq, Set.mem_iUnion]
      refine ⟨fun h => ⟨fun i => runDetSelection ((selAlg (n - k)).det η)
          (poolVal (v i) (complEmb L k hcard) (R_pool F L i)) π', ?_⟩, ?_⟩
      · rw [if_pos h]
        exact Set.mem_iInter.mpr (fun _ => rfl)
      · rintro ⟨S_vec, hmem⟩
        split_ifs at hmem with hmap
        · rw [← hmap]
          funext i
          have hi : runDetSelection ((selAlg (n - k)).det η)
              (poolVal (v i) (complEmb L k hcard) (R_pool F L i)) π' = S_vec i :=
            Set.mem_iInter.mp hmem i
          rw [hi]
        · exact False.elim hmem
    rw [h_eq]
    refine MeasurableSet.iUnion (fun S_vec => ?_)
    split_ifs
    · exact MeasurableSet.iInter (fun i =>
        h_meas_sel (n - k) (selAlg (n - k))
          (poolVal (v i) (complEmb L k hcard) (R_pool F L i)) π' (S_vec i))
    · exact MeasurableSet.empty

  
  have h_slice_eq : ∀ (k₀ : Fin (n + 1)) (π : Equiv.Perm (Fin n)) (X : Fin m → Finset (Fin n))
      (hcard₀ : (Finset.univ \ ((List.ofFn π).take k₀.1).toFinset).card = n - k₀.1)
      (π'₀ : Equiv.Perm (Fin (n - k₀.1))),
      (∀ s : Fin (n - k₀.1),
        complEmb (((List.ofFn π).take k₀.1).toFinset) k₀.1 hcard₀ (π'₀ s) =
          π ⟨k₀.1 + s.1, by omega⟩) →
      U k₀ π X =
        {c : Fin n → ℝ | K_sample c = k₀} ×ˢ
          {η_fam : (k : Fin (n + 1)) → (selAlg (n - k.1)).Seed |
            η_fam k₀ ∈ E_set k₀.1 (((List.ofFn π).take k₀.1).toFinset) hcard₀ π'₀ X} := by
    intro k₀ π X hcard₀ π'₀ hπ'₀
    ext ⟨c, η_fam⟩
    simp only [U, E_set, Set.mem_setOf_eq, Set.mem_prod]
    refine and_congr_right (fun hk_c => ?_)
    subst hk_c
    rw [h_traj c η_fam π hcard₀ π'₀ hπ'₀]

  have h_each_k : ∀ k_fin : Fin (n + 1),
      (∑ L ∈ (Finset.univ : Finset (Fin n)).powersetCard k_fin.1,
        bernProb n lam L * (invE * (∑ i : Fin m, F i (R_pool F L i)))) ≤
      (1 / (Nat.factorial n : ℝ)) *
        (∑ π : Equiv.Perm (Fin n), ∑ X : Fin m → Finset (Fin n),
          (frozenSeedMeasure n selAlg).real (U k_fin π X) * (∑ i : Fin m, realVal (v i) (X i))) := by
    intro k_fin
    have hk : k_fin.1 ≤ n := Nat.lt_succ_iff.mp k_fin.2
    let c_prob : ℝ := (Nat.choose n k_fin.1 : ℝ) * lam ^ k_fin.1 * (1 - lam) ^ (n - k_fin.1)
    let Φ (π : Equiv.Perm (Fin n)) : ℝ :=
      ∑ X : Fin m → Finset (Fin n),
        (frozenSeedMeasure n selAlg).real (U k_fin π X) * (∑ i : Fin m, realVal (v i) (X i))
    let Ψ (L : Finset (Fin n)) (π' : Equiv.Perm (Fin (n - k_fin.1))) : ℝ :=
      if hcard : (Finset.univ \ L).card = n - k_fin.1 then
        c_prob * ∑ X : Fin m → Finset (Fin n),
          ((selAlg (n - k_fin.1)).seedMeasure).real (E_set k_fin.1 L hcard π' X) *
            (∑ i : Fin m, realVal (v i) (X i))
      else 0
    have h_agree : ∀ (π : Equiv.Perm (Fin n)),
        let L := ((List.ofFn π).take k_fin.1).toFinset
        ∀ (hcard : (Finset.univ \ L).card = n - k_fin.1)
          (π' : Equiv.Perm (Fin (n - k_fin.1))),
          (∀ s : Fin (n - k_fin.1),
            complEmb L k_fin.1 hcard (π' s) = π ⟨k_fin.1 + s.1, by omega⟩) →
          Φ π = Ψ L π' := by
      intro π L hcard π' hπ'
      dsimp only [Φ, Ψ]
      rw [dif_pos hcard, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun X _ => ?_)
      rw [h_slice_eq k_fin π X hcard π' hπ',
        (h_slice_law k_fin).2 (E_set k_fin.1 L hcard π' X) (hE_meas k_fin.1 L hcard π' X),
        mul_assoc]
    change _ ≤ (1 / (Nat.factorial n : ℝ)) * (∑ π : Equiv.Perm (Fin n), Φ π)
    rw [h_perm_split k_fin.1 hk Φ Ψ h_agree, ← mul_assoc, Finset.mul_sum]
    refine Finset.sum_le_sum (fun L hL => ?_)
    have hL_card : L.card = k_fin.1 := (Finset.mem_powersetCard.mp hL).2
    have hcard_L : (Finset.univ \ L).card = n - k_fin.1 := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hL_card]
    have hΨ_unfold : ∀ π' : Equiv.Perm (Fin (n - k_fin.1)),
        Ψ L π' = c_prob * ∑ X : Fin m → Finset (Fin n),
          ((selAlg (n - k_fin.1)).seedMeasure).real (E_set k_fin.1 L hcard_L π' X) *
            (∑ i : Fin m, realVal (v i) (X i)) := by
      intro π'
      dsimp only [Ψ]
      rw [dif_pos hcard_L]
    simp_rw [hΨ_unfold, ← Finset.mul_sum]
    have h_scalar :
        (1 / (Nat.factorial n : ℝ)) * (Nat.factorial k_fin.1 : ℝ) * c_prob =
        bernProb n lam L * (1 / (Nat.factorial (n - k_fin.1) : ℝ)) := by
      have h_nat : (Nat.choose n k_fin.1 * Nat.factorial k_fin.1) *
          Nat.factorial (n - k_fin.1) = Nat.factorial n :=
        Nat.choose_mul_factorial_mul_factorial hk
      have h_real : ((Nat.choose n k_fin.1 : ℝ) * (Nat.factorial k_fin.1 : ℝ)) *
          (Nat.factorial (n - k_fin.1) : ℝ) = (Nat.factorial n : ℝ) := by
        exact_mod_cast h_nat
      have hn_ne : (Nat.factorial n : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      have hd_ne : (Nat.factorial (n - k_fin.1) : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k_fin.1))
      dsimp only [c_prob, bernProb]
      rw [hL_card]
      field_simp [hn_ne, hd_ne]
      rw [← h_real]
      ring
    have h_reassoc :
        (1 / (Nat.factorial n : ℝ)) * (Nat.factorial k_fin.1 : ℝ) *
          (c_prob * ∑ π' : Equiv.Perm (Fin (n - k_fin.1)), ∑ X : Fin m → Finset (Fin n),
            ((selAlg (n - k_fin.1)).seedMeasure).real (E_set k_fin.1 L hcard_L π' X) *
              (∑ i : Fin m, realVal (v i) (X i))) =
        bernProb n lam L *
          ((1 / (Nat.factorial (n - k_fin.1) : ℝ)) *
            ∑ π' : Equiv.Perm (Fin (n - k_fin.1)), ∑ X : Fin m → Finset (Fin n),
              ((selAlg (n - k_fin.1)).seedMeasure).real (E_set k_fin.1 L hcard_L π' X) *
                (∑ i : Fin m, realVal (v i) (X i))) := by
      rw [← mul_assoc ((1 / (Nat.factorial n : ℝ)) * (Nat.factorial k_fin.1 : ℝ)) c_prob,
        h_scalar, mul_assoc]
    rw [h_reassoc]
    refine mul_le_mul_of_nonneg_left ?_ (h_bern_nonneg L)
    have h_map_compl :
        (Finset.univ : Finset (Fin (n - k_fin.1))).map (complEmb L k_fin.1 hcard_L) =
          Finset.univ \ L := by
      refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
      · obtain ⟨z, _, rfl⟩ := Finset.mem_map.mp hy
        exact Finset.orderEmbOfFin_mem (Finset.univ \ L) hcard_L z
      · rw [Finset.card_map, Finset.card_univ, Fintype.card_fin, hcard_L]
    have h_pool_L : ∀ i : Fin m,
        IsGSValuation (poolVal (v i) (complEmb L k_fin.1 hcard_L) (R_pool F L i)) ∧
        optVal (poolVal (v i) (complEmb L k_fin.1 hcard_L) (R_pool F L i)) =
          disposalEnvelope (v i) (R_pool F L i) := by
      intro i
      refine h_pool i (n - k_fin.1) (complEmb L k_fin.1 hcard_L) (R_pool F L i) ?_
      rw [h_map_compl]
      exact Finset.filter_subset _ _
    exact h_pool_sel_bound (n - k_fin.1) (complEmb L k_fin.1 hcard_L) (R_pool F L) h_pool_L

  
  let cardFin (L : Finset (Fin n)) : Fin (n + 1) :=
    ⟨L.card, Nat.lt_succ_of_le ((Finset.card_le_univ L).trans_eq (Fintype.card_fin n))⟩
  have h_collapse :
      invE * (∑ L : Finset (Fin n), bernProb n lam L * (∑ i : Fin m, F i (R_pool F L i))) =
      ∑ k_fin : Fin (n + 1),
        ∑ L ∈ (Finset.univ : Finset (Fin n)).powersetCard k_fin.1,
          bernProb n lam L * (invE * (∑ i : Fin m, F i (R_pool F L i))) := by
    rw [Finset.mul_sum]
    simp_rw [← mul_left_comm (bernProb n lam _)]
    rw [← Finset.sum_fiberwise_of_maps_to (g := cardFin) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl (fun k_fin _ => ?_)
    have h_pow_eq : (Finset.univ : Finset (Finset (Fin n))).filter (fun L => cardFin L = k_fin) =
        (Finset.univ : Finset (Fin n)).powersetCard k_fin.1 := by
      ext L
      simp [cardFin, Finset.mem_powersetCard, Fin.ext_iff]
    rw [h_pow_eq]
  rw [h_collapse]
  exact Finset.sum_le_sum (fun k_fin _ => h_each_k k_fin)

end FrozenRoutingInternal

section
open FrozenRoutingInternal

theorem thm_gs_welfare (n m : ℕ) :
    ∃ alg : OnlineWelfareAlg n m,
      ∀ v : Fin m → ItemValuation n, (∀ i : Fin m, IsGSValuation (v i)) →
        (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
          let st := runDetWelfareSteps (alg.det ω) v π k hk
          IsAllocOf st.1.toFinset st.2 ∧
          ∀ i : Fin m, ((0 : ℝ) : WithBot ℝ) ≤ v i (st.2 i)) ∧
        ((((3 - 2 * Real.sqrt 2) / Real.exp 1) * optWelfare v : ℝ) : WithBot ℝ) ≤
          expectedWelfareVal alg v :=
by
  let selAlg : ∀ d : ℕ, OnlineSelectionAlg d :=
    fun d => Classical.choose (exists_gs_selection_alg d)
  have h_sel_spec : ∀ (d : ℕ) (w : ItemValuation d), IsGSValuation w →
      (∀ (ω_s : (selAlg d).Seed) (π_s : Equiv.Perm (Fin d)) (s : ℕ) (hs : s ≤ d),
        let st := runDetSelectionSteps ((selAlg d).det ω_s) w π_s s hs
        w st.2 ≠ ⊥ ∧ ((0 : ℝ) : WithBot ℝ) ≤ w st.2) ∧
      (((invE * optVal w : ℝ) : WithBot ℝ) ≤ expectedSelectionVal (selAlg d) w) :=
    fun d => Classical.choose_spec (exists_gs_selection_alg d)
  obtain ⟨h_prob, h_meas, h_traj, h_safety⟩ := frozen_routing_trajectory_and_meas n m selAlg
  let alg : OnlineWelfareAlg n m :=
    { Seed := FrozenSeed n selAlg
      seedMeasure := frozenSeedMeasure n selAlg
      isProb := h_prob
      det := frozenRoutingDet selAlg
      meas_step := h_meas }
  refine ⟨alg, fun v hv => ?_⟩
  have h_env_all := gs_disposal_and_pool_val n
  have h_pool_gs : ∀ (i : Fin m) (d : ℕ) (emb : Fin d ↪ Fin n) (R_i : Finset (Fin n)),
      IsGSValuation (poolVal (v i) emb R_i) :=
    fun i d emb R_i => ((h_env_all.1 (v i) (hv i)).2.2.2.2 d emb R_i).1
  have h_pool_both : ∀ (i : Fin m) (d : ℕ) (emb : Fin d ↪ Fin n) (R_i : Finset (Fin n)),
      R_i ⊆ Finset.univ.map emb →
        IsGSValuation (poolVal (v i) emb R_i) ∧
        optVal (poolVal (v i) emb R_i) = disposalEnvelope (v i) R_i := by
    intro i d emb R_i hsub
    have hp := (h_env_all.1 (v i) (hv i)).2.2.2.2 d emb R_i
    exact ⟨hp.1, hp.2 hsub⟩
  have h_step_safe := h_safety (fun d w hw => (h_sel_spec d w hw).1) v hv h_pool_gs
  refine ⟨?_, ?_⟩
  · intro ω π k hk
    obtain ⟨h_alloc, h_val⟩ := h_step_safe ω π k hk
    exact ⟨h_alloc, fun i => (h_val i).2⟩
  · obtain ⟨X_star, hX_alloc, h_opt_eq⟩ := h_env_all.2 m v hv
    let F : Fin m → Finset (Fin n) → ℝ := fun i => disposalEnvelope (v i)
    have hF_props : ∀ i : Fin m,
        (∀ S T : Finset (Fin n), S ⊆ T → F i S ≤ F i T) ∧ IsSubmodularReal (F i) := by
      intro i
      have hi := h_env_all.1 (v i) (hv i)
      exact ⟨hi.2.2.1, hi.2.2.2.1⟩
    have h_bern := bernoulli_routing_pool_bound n m F X_star hF_props hX_alloc
    have h_invE_nonneg : 0 ≤ invE := (Real.exp_pos (-1)).le
    have h_lhs_le :
        ((3 - 2 * Real.sqrt 2) / Real.exp 1) * optWelfare v ≤
          invE * (∑ L : Finset (Fin n), bernProb n lam L * (∑ i : Fin m, F i (R_pool F L i))) := by
      have h_eq : ((3 - 2 * Real.sqrt 2) / Real.exp 1) * optWelfare v =
          invE * ((3 - 2 * Real.sqrt 2) * (∑ i : Fin m, F i (X_star i))) := by
        rw [h_opt_eq]
        dsimp only [F, invE]
        rw [Real.exp_neg, div_eq_mul_inv]
        ring
      rw [h_eq]
      exact mul_le_mul_of_nonneg_left h_bern h_invE_nonneg
    have h_sel_final : ∀ (d : ℕ) (w : ItemValuation d), IsGSValuation w →
        (∀ (ω_s : (selAlg d).Seed) (π_s : Equiv.Perm (Fin d)),
          w (runDetSelection ((selAlg d).det ω_s) w π_s) ≠ ⊥) ∧
        (((invE * optVal w : ℝ) : WithBot ℝ) ≤ expectedSelectionVal (selAlg d) w) := by
      intro d w hw
      refine ⟨fun ω_s π_s => ?_, (h_sel_spec d w hw).2⟩
      exact ((h_sel_spec d w hw).1 ω_s π_s d (le_refl d)).1
    have h_final_ne_bot : ∀ (ω : FrozenSeed n selAlg) (π : Equiv.Perm (Fin n)) (i : Fin m),
        v i (runDetWelfare (frozenRoutingDet selAlg ω) v π i) ≠ ⊥ :=
      fun ω π i => ((h_step_safe ω π n (le_refl n)).2 i).1
    have h_decomp := frozen_routing_expected_welfare_decomp n m selAlg v h_prob h_meas
      h_sel_final hv h_pool_both (h_traj v) h_final_ne_bot
    exact le_trans (WithBot.coe_le_coe.mpr h_lhs_le) h_decomp


/-- **Theorem 4.1 (`thm:welfare`, Frozen Routing for Signed Gross Substitutes Welfare)**:
For every `n, m`, frozen routing with coin bias `λ = √2 - 1` (`alg : OnlineWelfareAlg n m`)
maintains a valid allocation with `v_i(A_i) ≥ 0` for every bidder at every arrival step `k ≤ n`,
uses Lemma 4.2 (`lem_4_2_envelope` / `lem_4_2_envelope_optWelfare`) and Theorem A (`thm_A`), and
obtains `E[∑_{i=1}^m v_i(A_i)] ≥ ((3 - 2√2) / e) OPT`. -/
theorem thm_4_1_welfare (n m : ℕ) :
    ∃ alg : OnlineWelfareAlg n m,
      ∀ v : Fin m → ItemValuation n, (∀ i : Fin m, IsGSValuation (v i)) →
        optWelfare (fun i => disposalEnvelopeVal (v i)) = optWelfare v ∧
        (∀ i : Fin m, IsSubmodularReal (disposalEnvelope (v i))) ∧
        (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
          let st := runDetWelfareSteps (alg.det ω) v π k hk
          IsAllocOf st.1.toFinset st.2 ∧
          ∀ i : Fin m, ((0 : ℝ) : WithBot ℝ) ≤ v i (st.2 i)) ∧
        ((((3 - 2 * Real.sqrt 2) / Real.exp 1) * optWelfare v : ℝ) : WithBot ℝ) ≤
          expectedWelfareVal alg v := by
  obtain ⟨alg, halg⟩ := thm_gs_welfare n m
  refine ⟨alg, fun v hv => ⟨lem_4_2_envelope_optWelfare v hv,
    fun i => (lem_4_2_envelope (v i) (hv i)).2.2.2.2.2,
    (halg v hv).1, (halg v hv).2⟩⟩

/-- **Theorem B (`thm:B`, Main Multi-Bidder Welfare Theorem for Signed GS Valuations)**:
For any `n` items and `m` signed gross substitutes bidders `v_1, ..., v_m` arriving in uniformly
random order, there exists a universal non-clairvoyant online welfare algorithm keeping
`v_i(A_i) ≥ 0` for every bidder at every time and achieving
`E[∑_{i=1}^m v_i(A_i)] ≥ ((3 - 2√2) / e) OPT ≈ 0.0631 OPT`. -/
theorem thm_B (n m : ℕ) :
    ∃ alg : OnlineWelfareAlg n m,
      ∀ v : Fin m → ItemValuation n, (∀ i : Fin m, IsGSValuation (v i)) →
        (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
          let st := runDetWelfareSteps (alg.det ω) v π k hk
          IsAllocOf st.1.toFinset st.2 ∧
          ∀ i : Fin m, ((0 : ℝ) : WithBot ℝ) ≤ v i (st.2 i)) ∧
        ((((3 - 2 * Real.sqrt 2) / Real.exp 1) * optWelfare v : ℝ) : WithBot ℝ) ≤
          expectedWelfareVal alg v :=
  thm_gs_welfare n m

end

end

end GrossSubstitutesWelfare
