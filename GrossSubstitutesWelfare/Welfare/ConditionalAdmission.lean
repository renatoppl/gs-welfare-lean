import GrossSubstitutesWelfare.Defs
import GrossSubstitutesWelfare.Preliminaries.ExchangeAndDemand
import GrossSubstitutesWelfare.Preliminaries.SafeSupportAndCutoff

set_option maxHeartbeats 4000000

/-!
# Section 4.2 Remarks & Section 4.3: Conditional Admission, `[KRTV13]`, and Open Problem 1.1

This file formalizes:
- **Section 4.2 (`sec:routing`)**:
  - Non-submodular disposal envelope of a nonnegative submodular directed-cut valuation
    (`rem_4_2_directed_cut_envelope_not_submodular`).
  - *The price of freezing* (`rem_4_2_price_of_freezing`): exact pool value formula
    `(λ(1 - λ) + (1 - λ)^2 / n) OPT ≤ (1/4 + 1/n) OPT`, strictly below `OPT / e` for `n ≥ 9`.
- **Section 4.3 (`sec:towards`)**:
  - Canonical prefix-optimal allocations `gsPrefixOptAlloc` and proposal-map validity
    (`gsPrefixOptAlloc_spec`, `gsPrefixOptAlloc_proposal`).
  - **Theorem 4.5 (`thm:admission`)**: Running per-bidder conditional-admission modules in parallel
    achieves `c_n(s) OPT` expected welfare (`thm_4_5_admission`).
  - **`[KRTV13]` Unit-Demand Conditional Admission & Welfare**: First-accepted-offer module
    satisfies `HasConditionalAdmission` (`krtv_unit_demand_module`), yielding `1/e`-competitive
    online welfare for unit-demand bidders (`krtv_unit_demand_welfare`).
  - **Open Problem 1.1 (`q:welfare`) Reduction**: Universal conditional admission for gross
    substitutes valuations implies `1/e`-competitive online welfare for signed gross substitutes
    valuations across all `n, m` (`open_problem_1_1_reduction`).
-/

namespace GrossSubstitutesWelfare

open Classical MeasureTheory

noncomputable section

def frozenRouteStep {n m : ℕ} (hm : 0 < m)
    (v : Fin m → ItemValuation n) (L : Finset (Fin n))
    (state : (Fin m → Finset (Fin n)) × (Fin m → Finset (Fin n))) (g : Fin n) :
    (Fin m → Finset (Fin n)) × (Fin m → Finset (Fin n)) :=
  let B := state.1
  let R := state.2
  let marg : Fin m → ℝ := fun i =>
    disposalEnvelope (v i) (insert g (B i)) - disposalEnvelope (v i) (B i)
  let best := (Finset.univ : Finset (Fin m)).sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ marg
  let optBidders := (Finset.univ : Finset (Fin m)).filter (fun i => marg i = best)
  let i_star : Fin m :=
    if h : optBidders.Nonempty then optBidders.min' h else ⟨0, hm⟩
  if g ∈ L then
    (Function.update B i_star (insert g (B i_star)), R)
  else
    (B, Function.update R i_star (insert g (R i_star)))

/-- Final bidder pools `(R_1(L), ..., R_m(L))` produced by Frozen Routing's label-order pass. -/
def frozenRoutingPools {n m : ℕ} (hm : 0 < m)
    (v : Fin m → ItemValuation n) (L : Finset (Fin n)) : Fin m → Finset (Fin n) :=
  ((List.finRange n).foldl (frozenRouteStep hm v L) (fun _ => ∅, fun _ => ∅)).2

namespace Internal

/-- **Section 4.2 Counterexamples & Section 4.3 Conditional Admission (`def:admission`,
`thm:admission`, `[KRTV13]`, Open Problem 1.1 Reduction)**:
1. **Non-submodular disposal envelope of a nonnegative submodular valuation (`sec:routing`)**:
   Directed-cut valuation on 3 items (`a ↔ b, c → a`) is finite, nonnegative, and submodular, yet
   its disposal envelope violates submodularity.
2. **The price of freezing (`sec:routing`)**: On `n` items and `n` identical bidders with
   `v_i(S) = |S| - 3(|S| - 1)_+`, each `v_i` is GS, `OPT = n`, and for every coin bias `λ ∈ [0, 1]`
   the expected total envelope value of the frozen routing pools equals
   `(λ(1 - λ) + (1 - λ)^2 / n) OPT ≤ (1/4 + 1/n) OPT`, which is strictly below `OPT / e` for `n ≥ 9`.
3. **Prefix proposals (`gsPrefixOptAlloc`)**: For any GS profile `v_1, ..., v_m`, `X^S` is a valid
   allocation of `S` achieving `W(S)`, depends only on subsets of `S`, and defines a valid proposal
   map `IsProposalMap (v i) (fun S => X^S_i)` for every bidder `i` (with `|X^S_i| ≤ 1` when `v_i`
   is unit-demand).
4. **Theorem 4.5 (`thm:admission`)**: Running conditional-admission modules for `v_i` and
   `P_i(S) = X^S_i` side by side defines a valid non-clairvoyant `OnlineWelfareAlg n m` achieving
   `E[∑_i v_i(A_i)] ≥ c_n(s) OPT`.
5. **`[KRTV13]` Unit-demand conditional admission & welfare**: The first-accepted-offer module
   satisfies `HasConditionalAdmission` for any unit-demand valuation and `≤ 1`-item proposal map,
   yielding `c_n(s) OPT` (for `1 ≤ s < n`) and `OPT / e` across all `n, m` for unit-demand welfare.
6. **Open Problem 1.1 (`q:welfare`) reduction**: If every GS valuation and proposal map admits a
   module with conditional admission (uniformly or per `(v, P)`), then `1 / e`-competitive online
   welfare holds across all `n, m` for signed GS valuations. -/
theorem thm_welfare_counterexamples_and_admission :
    -- (1) Directed-cut nonnegative submodular valuation with non-submodular disposal envelope
    (∃ v : ItemValuation 3,
      IsFiniteValuation v ∧ IsNonnegValuation v ∧ IsSubmodularReal (realVal v) ∧
      disposalEnvelope v {0} = 1 ∧
      disposalEnvelope v {0, 1} = 1 ∧
      disposalEnvelope v {0, 2} = 1 ∧
      disposalEnvelope v {0, 1, 2} = 2 ∧
      ¬ IsSubmodularReal (disposalEnvelope v)) ∧
    -- (2) Price of freezing: exact pool value formula and < 1/e bound for n ≥ 9
    (∀ (n : ℕ) (hn : 1 ≤ n) (lam : ℝ), 0 ≤ lam → lam ≤ 1 →
      let v : Fin n → ItemValuation n := fun _ S =>
        (((S.card : ℝ) - 3 * ((S.card - 1 : ℕ) : ℝ) : ℝ) : WithBot ℝ)
      let bernProb : Finset (Fin n) → ℝ :=
        fun L => lam ^ L.card * (1 - lam) ^ (n - L.card)
      let poolVal : ℝ :=
        ∑ L : Finset (Fin n),
          bernProb L * (∑ i : Fin n, disposalEnvelope (v i) (frozenRoutingPools hn v L i))
      (∀ i : Fin n, IsGSValuation (v i)) ∧
      optWelfare v = (n : ℝ) ∧
      (∀ i S, disposalEnvelope (v i) S = (min S.card 1 : ℝ)) ∧
      poolVal = (lam * (1 - lam) + (1 - lam) ^ 2 / (n : ℝ)) * optWelfare v ∧
      poolVal ≤ (1 / 4 + 1 / (n : ℝ)) * optWelfare v ∧
      (9 ≤ n → poolVal < invE * optWelfare v)) ∧
    -- (3) Prefix-optimal proposals are valid proposal maps depending only on subsets of S
    (∀ {n m : ℕ} (v : Fin m → ItemValuation n),
      (∀ i, v i ∅ = ((0 : ℝ) : WithBot ℝ)) →
        (∀ S : Finset (Fin n),
          IsAllocOf S (gsPrefixOptAlloc v S) ∧
          allocWelfare v (gsPrefixOptAlloc v S) = ((optWelfareOn v S : ℝ) : WithBot ℝ) ∧
          (∀ v' : Fin m → ItemValuation n,
            (∀ i, ∀ T ⊆ S, v' i T = v i T) → gsPrefixOptAlloc v' S = gsPrefixOptAlloc v S)) ∧
        (∀ i : Fin m, IsProposalMap (v i) (fun S => gsPrefixOptAlloc v S i)) ∧
        (∀ i : Fin m, IsUnitDemandValuation (v i) →
          ∀ S : Finset (Fin n), (gsPrefixOptAlloc v S i).card ≤ 1)) ∧
    -- (4) Theorem 4.5 (thm:admission): Conditional admission implies c_n(s) OPT welfare
    (∀ {n m s : ℕ} (v : Fin m → ItemValuation n) (mod : Fin m → OnlineAdmissionModule n),
      1 ≤ s → s < n →
      (∀ i : Fin m, IsGSValuation (v i)) →
      (∀ i : Fin m, HasConditionalAdmission s (v i) (fun S => gsPrefixOptAlloc v S i) (mod i)) →
        ∃ alg : OnlineWelfareAlg n m,
          (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
            IsAllocOf (runDetWelfareSteps (alg.det ω) v π k hk).1.toFinset
              (runDetWelfareSteps (alg.det ω) v π k hk).2) ∧
          (((secretaryCutoffConst n s * optWelfare v : ℝ) : WithBot ℝ) ≤
            expectedWelfareVal alg v)) ∧
    -- (5) [KRTV13]: Unit-demand conditional admission module & 1/e unit-demand welfare
    (∀ (n s : ℕ), 1 ≤ s → s < n →
      ∃ mod : OnlineAdmissionModule n,
        ∀ (v : ItemValuation n) (P : Finset (Fin n) → Finset (Fin n)),
          IsUnitDemandValuation v → IsProposalMap v P → (∀ S, (P S).card ≤ 1) →
            HasConditionalAdmission s v P mod) ∧
    (∀ (n m : ℕ),
      ∃ alg : OnlineWelfareAlg n m,
        ∀ v : Fin m → ItemValuation n, (∀ i, IsUnitDemandValuation (v i)) →
          (((invE * optWelfare v : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg v)) ∧
    -- (6) Open Problem 1.1 reduction: Universal GS conditional admission ⟹ 1/e GS welfare
    ((∀ (n s : ℕ), 2 ≤ n → 1 ≤ s → s < n →
        ∃ mod : OnlineAdmissionModule n,
          ∀ (v : ItemValuation n) (P : Finset (Fin n) → Finset (Fin n)),
            IsGSValuation v → IsProposalMap v P → HasConditionalAdmission s v P mod) →
      ∀ (n m : ℕ),
        ∃ alg : OnlineWelfareAlg n m,
          ∀ v : Fin m → ItemValuation n, (∀ i, IsGSValuation (v i)) →
            (((invE * optWelfare v : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg v)) :=
by
  have h_s1 : ∃ v : ItemValuation 3,
      IsFiniteValuation v ∧ IsNonnegValuation v ∧ IsSubmodularReal (realVal v) ∧
      disposalEnvelope v {0} = 1 ∧
      disposalEnvelope v {0, 1} = 1 ∧
      disposalEnvelope v {0, 2} = 1 ∧
      disposalEnvelope v {0, 1, 2} = 2 ∧
      ¬ IsSubmodularReal (disposalEnvelope v) := by
    let phi : Fin 3 → Fin 3 → Finset (Fin 3) → ℝ :=
      fun u w S => if u ∈ S ∧ w ∉ S then 1 else 0
    let f : Finset (Fin 3) → ℝ := fun S => phi 0 1 S + phi 1 0 S + phi 2 0 S
    let v : ItemValuation 3 := fun S => ((f S : ℝ) : WithBot ℝ)
    have h_phi_nn : ∀ u w S, 0 ≤ phi u w S := by
      intro u w S; dsimp [phi]; split_ifs <;> norm_num
    have h_phi_le : ∀ u w S, phi u w S ≤ 1 := by
      intro u w S; dsimp [phi]; split_ifs <;> norm_num
    have h_phi_submod : ∀ u w : Fin 3, u ≠ w → IsSubmodularReal (phi u w) := by
      intro u w huw
      refine ⟨by simp [phi], fun Q R hQR g hgR => ?_⟩
      have hgQ : g ∉ Q := fun hg => hgR (hQR hg)
      by_cases hgu : g = u
      · subst hgu
        have h1 : phi g w R = 0 := by simp [phi, hgR]
        have h2 : phi g w Q = 0 := by simp [phi, hgQ]
        rw [h1, h2]
        by_cases hwQ : w ∈ Q
        · have hwR : w ∈ R := hQR hwQ
          have h3 : phi g w (insert g R) = 0 := by simp [phi, hwR]
          have h4 : phi g w (insert g Q) = 0 := by simp [phi, hwQ]
          linarith
        · have h4 : phi g w (insert g Q) = 1 := by simp [phi, hwQ, huw.symm]
          linarith [h_phi_le g w (insert g R)]
      · by_cases hgw : g = w
        · subst hgw
          have h1 : phi u g (insert g R) = 0 := by simp [phi]
          have h2 : phi u g (insert g Q) = 0 := by simp [phi]
          rw [h1, h2]
          by_cases huQ : u ∈ Q
          · have huR : u ∈ R := hQR huQ
            have h3 : phi u g R = 1 := by simp [phi, huR, hgR]
            have h4 : phi u g Q = 1 := by simp [phi, huQ, hgQ]
            linarith
          · have h4 : phi u g Q = 0 := by simp [phi, huQ]
            linarith [h_phi_nn u g R]
        · have h1 : phi u w (insert g R) = phi u w R := by
            dsimp [phi]
            simp [ Ne.symm hgu, Ne.symm hgw]
          have h2 : phi u w (insert g Q) = phi u w Q := by
            dsimp [phi]
            simp [Ne.symm hgu, Ne.symm hgw]
          linarith
    have h_f_submod : IsSubmodularReal f := by
      have s01 := h_phi_submod 0 1 (by decide)
      have s10 := h_phi_submod 1 0 (by decide)
      have s20 := h_phi_submod 2 0 (by decide)
      refine ⟨by dsimp [f]; linarith [s01.1, s10.1, s20.1], fun Q R hQR g hgR => ?_⟩
      dsimp [f]
      linarith [s01.2 Q R hQR g hgR, s10.2 Q R hQR g hgR, s20.2 Q R hQR g hgR]
    have h_rv : realVal v = f := by
      ext S; simp [realVal, v]
    have h_env_eq : ∀ (S : Finset (Fin 3)) (r : ℝ),
        (∃ T₀ ⊆ S, f T₀ = r) → (∀ T ⊆ S, f T ≤ r) → disposalEnvelope v S = r := by
      intro S r ⟨T₀, hT₀S, hfT₀⟩ h_ub
      have hsup : S.powerset.sup v = ((r : ℝ) : WithBot ℝ) := by
        refine le_antisymm (Finset.sup_le (fun T hT => ?_)) ?_
        · dsimp [v]
          exact WithBot.coe_le_coe.mpr (h_ub T (Finset.mem_powerset.mp hT))
        · refine le_trans ?_ (Finset.le_sup (f := v) (Finset.mem_powerset.mpr hT₀S))
          dsimp [v]
          rw [hfT₀]
      simp [disposalEnvelope, hsup]
    have hf_0 : f {0} = 1 := by
      dsimp [f, phi]
      norm_num
    have hf_12 : f {1, 2} = 2 := by
      dsimp [f, phi]
      norm_num
    have h_env0 : disposalEnvelope v {0} = 1 := by
      refine h_env_eq {0} 1 ⟨{0}, Finset.Subset.rfl, hf_0⟩ (fun T hT => ?_)
      have h1 : (1 : Fin 3) ∉ T := fun h => by
        have := hT h; simp at this
      have h2 : (2 : Fin 3) ∉ T := fun h => by
        have := hT h; simp at this
      have p1 : phi 1 0 T = 0 := by simp [phi, h1]
      have p2 : phi 2 0 T = 0 := by simp [phi, h2]
      dsimp [f]; linarith [h_phi_le 0 1 T]
    have h_env01 : disposalEnvelope v {0, 1} = 1 := by
      refine h_env_eq {0, 1} 1 ⟨{0}, by decide, hf_0⟩ (fun T hT => ?_)
      have h2 : (2 : Fin 3) ∉ T := fun h => by
        have := hT h; simp at this
      have p2 : phi 2 0 T = 0 := by simp [phi, h2]
      by_cases h0 : (0 : Fin 3) ∈ T
      · have p1 : phi 1 0 T = 0 := by simp [phi, h0]
        dsimp [f]; linarith [h_phi_le 0 1 T]
      · have p0 : phi 0 1 T = 0 := by simp [phi, h0]
        dsimp [f]; linarith [h_phi_le 1 0 T]
    have h_env02 : disposalEnvelope v {0, 2} = 1 := by
      refine h_env_eq {0, 2} 1 ⟨{0}, by decide, hf_0⟩ (fun T hT => ?_)
      have h1 : (1 : Fin 3) ∉ T := fun h => by
        have := hT h; simp at this
      have p1 : phi 1 0 T = 0 := by simp [phi, h1]
      by_cases h0 : (0 : Fin 3) ∈ T
      · have p2 : phi 2 0 T = 0 := by simp [phi, h0]
        dsimp [f]; linarith [h_phi_le 0 1 T]
      · have p0 : phi 0 1 T = 0 := by simp [phi, h0]
        dsimp [f]; linarith [h_phi_le 2 0 T]
    have h_env012 : disposalEnvelope v {0, 1, 2} = 2 := by
      refine h_env_eq {0, 1, 2} 2 ⟨{1, 2}, by decide, hf_12⟩ (fun T _ => ?_)
      by_cases h0 : (0 : Fin 3) ∈ T
      · have p1 : phi 1 0 T = 0 := by simp [phi, h0]
        have p2 : phi 2 0 T = 0 := by simp [phi, h0]
        dsimp [f]; linarith [h_phi_le 0 1 T]
      · have p0 : phi 0 1 T = 0 := by simp [phi, h0]
        dsimp [f]; linarith [h_phi_le 1 0 T, h_phi_le 2 0 T]
    refine ⟨v, fun S => WithBot.coe_ne_bot, fun S => ?_, h_rv ▸ h_f_submod,
            h_env0, h_env01, h_env02, h_env012, ?_⟩
    · dsimp [v, f]
      exact WithBot.coe_le_coe.mpr (by linarith [h_phi_nn 0 1 S, h_phi_nn 1 0 S, h_phi_nn 2 0 S])
    · intro hsub
      have h_ineq := hsub.2 {0} {0, 1} (by decide) 2 (by decide)
      have hins1 : (insert (2 : Fin 3) ({0, 1} : Finset (Fin 3))) = {0, 1, 2} := by decide
      have hins2 : (insert (2 : Fin 3) ({0} : Finset (Fin 3))) = {0, 2} := by decide
      rw [hins1, hins2, h_env012, h_env01, h_env02, h_env0] at h_ineq
      linarith
  have coe_unbotD : ∀ {z : WithBot ℝ}, z ≠ ⊥ → ((z.unbotD 0 : ℝ) : WithBot ℝ) = z := by
    intro z hz
    obtain ⟨r, rfl⟩ := WithBot.ne_bot_iff_exists.mp hz
    rw [WithBot.unbotD_coe]
  have coe_realVal : ∀ {n : ℕ} (v : ItemValuation n) (S : Finset (Fin n)),
      v S ≠ ⊥ → ((realVal v S : ℝ) : WithBot ℝ) = v S :=
    fun _ _ hS => coe_unbotD hS
  
  
  
  have h_allocCode_lt : ∀ {n m : ℕ} (X : Fin m → Finset (Fin n)),
      allocCode X < 2 ^ (n * m + 1) := by
    intro n m X
    have h_geom2 : ∀ k : ℕ, (∑ r ∈ Finset.range k, 2 ^ r) + 1 = 2 ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, pow_succ]
        omega
    have h_bundle_le : ∀ A : Finset (Fin n), ∑ g ∈ A, 2 ^ g.1 ≤ 2 ^ n - 1 := by
      intro A
      have h_sub : ∑ g ∈ A, 2 ^ g.1 ≤ ∑ g : Fin n, 2 ^ g.1 :=
        Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
      rw [Fin.sum_univ_eq_sum_range (fun r => 2 ^ r)] at h_sub
      have h2 := h_geom2 n
      omega
    let B : ℕ := 2 ^ n
    have hB_pos : 1 ≤ B := Nat.one_le_two_pow
    have h_geomB : ∀ k : ℕ, (∑ r ∈ Finset.range k, (B - 1) * B ^ r) + 1 = B ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, pow_succ]
        calc
          (∑ r ∈ Finset.range k, (B - 1) * B ^ r) + (B - 1) * B ^ k + 1
            = ((∑ r ∈ Finset.range k, (B - 1) * B ^ r) + 1) + (B - 1) * B ^ k := by omega
          _ = B ^ k + (B - 1) * B ^ k := by rw [ih]
          _ = (1 + (B - 1)) * B ^ k := by ring
          _ = B * B ^ k := by rw [Nat.add_sub_of_le hB_pos]
          _ = B ^ k * B := Nat.mul_comm _ _
    have h_code_le : allocCode X ≤ ∑ r ∈ Finset.range m, (B - 1) * B ^ r := by
      unfold allocCode
      calc
        ∑ i : Fin m, (∑ g ∈ X i, 2 ^ g.1) * B ^ i.1
          ≤ ∑ i : Fin m, (B - 1) * B ^ i.1 := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            exact Nat.mul_le_mul_right (B ^ i.1) (h_bundle_le (X i))
        _ = ∑ r ∈ Finset.range m, (B - 1) * B ^ r :=
            Fin.sum_univ_eq_sum_range (fun r => (B - 1) * B ^ r) m
    have h_code_lt_Bm : allocCode X < B ^ m := by
      have := h_geomB m
      omega
    have hBm_eq : B ^ m = 2 ^ (n * m) := (pow_mul 2 n m).symm
    have h_lt_next : 2 ^ (n * m) < 2 ^ (n * m + 1) := by
      rw [pow_succ]
      have : 1 ≤ 2 ^ (n * m) := Nat.one_le_two_pow
      omega
    omega
  have h_s3_main : ∀ {n m : ℕ} (v : Fin m → ItemValuation n),
      (∀ i, v i ∅ = ((0 : ℝ) : WithBot ℝ)) →
        (∀ S : Finset (Fin n),
          IsAllocOf S (gsPrefixOptAlloc v S) ∧
          allocWelfare v (gsPrefixOptAlloc v S) = ((optWelfareOn v S : ℝ) : WithBot ℝ) ∧
          (∀ v' : Fin m → ItemValuation n,
            (∀ i, ∀ T ⊆ S, v' i T = v i T) → gsPrefixOptAlloc v' S = gsPrefixOptAlloc v S)) ∧
        (∀ i : Fin m, IsProposalMap (v i) (fun S => gsPrefixOptAlloc v S i)) ∧
        (∀ i : Fin m, IsUnitDemandValuation (v i) →
          ∀ S : Finset (Fin n), (gsPrefixOptAlloc v S i).card ≤ 1) := by
    intro n m v hv0
    have h_spec : ∀ S : Finset (Fin n),
        let cand := (Finset.univ : Finset (Fin m → Finset (Fin n))).filter
          (fun X => IsAllocOf S X ∧ allocWelfare v X ≠ ⊥)
        let best := cand.sup (allocWelfare v)
        let optCand := cand.filter (fun X => allocWelfare v X = best)
        gsPrefixOptAlloc v S ∈ optCand ∧
        (∀ Y ∈ optCand, gsAllocTieKey (gsPrefixOptAlloc v S) ≤ gsAllocTieKey Y) ∧
        best = ((optWelfareOn v S : ℝ) : WithBot ℝ) := by
      intro S
      let cand := (Finset.univ : Finset (Fin m → Finset (Fin n))).filter
        (fun X => IsAllocOf S X ∧ allocWelfare v X ≠ ⊥)
      let best := cand.sup (allocWelfare v)
      let optCand := cand.filter (fun X => allocWelfare v X = best)
      let X0 : Fin m → Finset (Fin n) := fun _ => ∅
      have hX0_alloc : IsAllocOf S X0 :=
        ⟨fun _ => Finset.empty_subset S, fun _ _ _ => Finset.disjoint_empty_left ∅⟩
      have hX0_val : allocWelfare v X0 = ((0 : ℝ) : WithBot ℝ) := by
        unfold allocWelfare
        rw [Finset.sum_congr rfl (fun i _ => hv0 i)]
        simp
      have hX0_cand : X0 ∈ cand :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ X0, hX0_alloc, by rw [hX0_val]; exact WithBot.coe_ne_bot⟩
      obtain ⟨X1, hX1_cand, hX1_eq⟩ := Finset.exists_mem_eq_sup cand ⟨X0, hX0_cand⟩ (allocWelfare v)
      have hX1_opt : X1 ∈ optCand := Finset.mem_filter.mpr ⟨hX1_cand, hX1_eq.symm⟩
      obtain ⟨Xmin, hXmin_opt, hXmin_le⟩ :=
        Finset.exists_min_image optCand gsAllocTieKey ⟨X1, hX1_opt⟩
      have hex : ∃ X ∈ optCand, ∀ Y ∈ optCand, gsAllocTieKey X ≤ gsAllocTieKey Y :=
        ⟨Xmin, hXmin_opt, hXmin_le⟩
      have h_gs_eq : gsPrefixOptAlloc v S = Classical.choose hex := by
        dsimp [gsPrefixOptAlloc, cand, best, optCand]
        exact dif_pos hex
      obtain ⟨hch_mem, hch_min⟩ := Classical.choose_spec hex
      rw [← h_gs_eq] at hch_mem hch_min
      let A_S := (Finset.univ : Finset (Fin m → Finset (Fin n))).filter (fun X => IsAllocOf S X)
      have h_sup_eq : A_S.sup (allocWelfare v) = best := by
        refine le_antisymm (Finset.sup_le (fun X hX => ?_)) (Finset.sup_le (fun X hX => ?_))
        · by_cases hbot : allocWelfare v X = ⊥
          · rw [hbot]; exact bot_le
          · exact Finset.le_sup (f := allocWelfare v)
              (Finset.mem_filter.mpr ⟨Finset.mem_univ X, (Finset.mem_filter.mp hX).2, hbot⟩)
        · exact Finset.le_sup (f := allocWelfare v)
            (Finset.mem_filter.mpr ⟨Finset.mem_univ X, (Finset.mem_filter.mp hX).2.1⟩)
      have hbest_ne : best ≠ ⊥ := by
        dsimp [best]
        rw [hX1_eq]
        exact (Finset.mem_filter.mp hX1_cand).2.2
      have hbest_opt : best = ((optWelfareOn v S : ℝ) : WithBot ℝ) := by
        unfold optWelfareOn
        change best = (((A_S.sup (allocWelfare v)).unbotD 0 : ℝ) : WithBot ℝ)
        rw [h_sup_eq, coe_unbotD hbest_ne]
      exact ⟨hch_mem, hch_min, hbest_opt⟩
    have h_part1 : ∀ S : Finset (Fin n),
        IsAllocOf S (gsPrefixOptAlloc v S) ∧
        allocWelfare v (gsPrefixOptAlloc v S) = ((optWelfareOn v S : ℝ) : WithBot ℝ) ∧
        (∀ v' : Fin m → ItemValuation n,
          (∀ i, ∀ T ⊆ S, v' i T = v i T) → gsPrefixOptAlloc v' S = gsPrefixOptAlloc v S) := by
      intro S
      obtain ⟨hmem_opt, _, hbest_eq⟩ := h_spec S
      obtain ⟨hmem_cand, hw_best⟩ := Finset.mem_filter.mp hmem_opt
      obtain ⟨h_alloc, _⟩ := (Finset.mem_filter.mp hmem_cand).2
      refine ⟨h_alloc, hw_best.trans hbest_eq, fun v' hv' => ?_⟩
      let chooseOpt : Finset (Fin m → Finset (Fin n)) → (Fin m → Finset (Fin n)) :=
        fun O => if h : ∃ X ∈ O, ∀ Y ∈ O, gsAllocTieKey X ≤ gsAllocTieKey Y then
          Classical.choose h else fun _ => ∅
      have h_welf_eq : ∀ X : Fin m → Finset (Fin n), IsAllocOf S X →
          allocWelfare v' X = allocWelfare v X := by
        intro X hX
        unfold allocWelfare
        exact Finset.sum_congr rfl (fun i _ => hv' i (X i) (hX.1 i))
      let cand := (Finset.univ : Finset (Fin m → Finset (Fin n))).filter
        (fun X => IsAllocOf S X ∧ allocWelfare v X ≠ ⊥)
      let cand' := (Finset.univ : Finset (Fin m → Finset (Fin n))).filter
        (fun X => IsAllocOf S X ∧ allocWelfare v' X ≠ ⊥)
      have h_cand_eq : cand' = cand := by
        ext X
        simp only [cand, cand', Finset.mem_filter, Finset.mem_univ, true_and]
        exact and_congr_right (fun hX => by rw [h_welf_eq X hX])
      have h_best_eq' : cand'.sup (allocWelfare v') = cand.sup (allocWelfare v) := by
        refine Finset.sup_congr h_cand_eq (fun X hX => ?_)
        exact h_welf_eq X (Finset.mem_filter.mp hX).2.1
      let optCand := cand.filter (fun X => allocWelfare v X = cand.sup (allocWelfare v))
      let optCand' := cand'.filter (fun X => allocWelfare v' X = cand'.sup (allocWelfare v'))
      have h_optCand_eq : optCand' = optCand := by
        ext X
        have h1 : X ∈ optCand' ↔ X ∈ cand' ∧ allocWelfare v' X = cand'.sup (allocWelfare v') := Finset.mem_filter
        have h2 : X ∈ optCand ↔ X ∈ cand ∧ allocWelfare v X = cand.sup (allocWelfare v) := Finset.mem_filter
        rw [h1, h2, h_best_eq', h_cand_eq]
        exact and_congr_right (fun hX => by rw [h_welf_eq X (Finset.mem_filter.mp hX).2.1])
      change chooseOpt optCand' = chooseOpt optCand
      rw [h_optCand_eq]
    have h_bundle_ne_bot : ∀ (S : Finset (Fin n)) (j : Fin m),
        v j (gsPrefixOptAlloc v S j) ≠ ⊥ := by
      intro S j hbot
      obtain ⟨hmem_opt, _, _⟩ := h_spec S
      have hw_ne : allocWelfare v (gsPrefixOptAlloc v S) ≠ ⊥ :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hmem_opt).1).2.2
      have hw_bot : allocWelfare v (gsPrefixOptAlloc v S) = ⊥ := by
        unfold allocWelfare
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j), hbot, WithBot.bot_add]
      exact hw_ne hw_bot
    have h_part2 : ∀ i : Fin m, IsProposalMap (v i) (fun S => gsPrefixOptAlloc v S i) := by
      intro i S
      let XS := gsPrefixOptAlloc v S
      obtain ⟨hmem_opt, _, _⟩ := h_spec S
      obtain ⟨hmem_cand, hw_best⟩ := Finset.mem_filter.mp hmem_opt
      obtain ⟨hXS_alloc, _⟩ := (Finset.mem_filter.mp hmem_cand).2
      refine ⟨hXS_alloc.1 i, h_bundle_ne_bot S i, fun Y hYX => ?_⟩
      by_cases hYbot : v i Y = ⊥
      · rw [hYbot]; exact bot_le
      · let X' : Fin m → Finset (Fin n) := Function.update XS i Y
        have hX'_sub : ∀ j : Fin m, X' j ⊆ XS j := by
          intro j
          by_cases hj : j = i
          · subst hj; simpa [X'] using hYX
          · simp [X', hj]
        have hX'_alloc : IsAllocOf S X' :=
          ⟨fun j => (hX'_sub j).trans (hXS_alloc.1 j),
           fun j1 j2 hne => Disjoint.mono (hX'_sub j1) (hX'_sub j2) (hXS_alloc.2 j1 j2 hne)⟩
        have hX'_ne : ∀ j : Fin m, v j (X' j) ≠ ⊥ := by
          intro j
          by_cases hj : j = i
          · subst hj; simpa [X'] using hYbot
          · simpa [X', hj] using h_bundle_ne_bot S j
        have h_lhs : allocWelfare v X' = ((∑ j : Fin m, realVal (v j) (X' j) : ℝ) : WithBot ℝ) := by
          rw [WithBot.coe_sum]; unfold allocWelfare
          exact Finset.sum_congr rfl (fun j _ => (coe_realVal (v j) (X' j) (hX'_ne j)).symm)
        have h_rhs : allocWelfare v XS = ((∑ j : Fin m, realVal (v j) (XS j) : ℝ) : WithBot ℝ) := by
          rw [WithBot.coe_sum]; unfold allocWelfare
          exact Finset.sum_congr rfl (fun j _ => (coe_realVal (v j) (XS j) (h_bundle_ne_bot S j)).symm)
        let cand := (Finset.univ : Finset (Fin m → Finset (Fin n))).filter
          (fun X => IsAllocOf S X ∧ allocWelfare v X ≠ ⊥)
        have hX'_cand : X' ∈ cand := Finset.mem_filter.mpr
          ⟨Finset.mem_univ X', hX'_alloc, by rw [h_lhs]; exact WithBot.coe_ne_bot⟩
        have h_welf_le : allocWelfare v X' ≤ allocWelfare v XS := by
          rw [hw_best]
          exact Finset.le_sup (f := allocWelfare v) hX'_cand
        rw [h_lhs, h_rhs, WithBot.coe_le_coe] at h_welf_le
        have h_split1 := (Finset.add_sum_erase Finset.univ (fun j => realVal (v j) (X' j)) (Finset.mem_univ i)).symm
        have h_split2 := (Finset.add_sum_erase Finset.univ (fun j => realVal (v j) (XS j)) (Finset.mem_univ i)).symm
        rw [h_split1, h_split2] at h_welf_le
        have h_rest : ∑ j ∈ Finset.erase Finset.univ i, realVal (v j) (X' j) =
            ∑ j ∈ Finset.erase Finset.univ i, realVal (v j) (XS j) := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          simp [X', (Finset.mem_erase.mp hj).1]
        have h_at_i : realVal (v i) (X' i) = realVal (v i) Y := by simp [X']
        rw [h_at_i, h_rest] at h_welf_le
        rw [← coe_realVal (v i) Y hYbot, ← coe_realVal (v i) (XS i) (h_bundle_ne_bot S i), WithBot.coe_le_coe]
        linarith
    have h_part3 : ∀ i : Fin m, IsUnitDemandValuation (v i) →
        ∀ S : Finset (Fin n), (gsPrefixOptAlloc v S i).card ≤ 1 := by
      intro i hud S
      obtain ⟨w, _, hw_eq⟩ := hud
      let XS := gsPrefixOptAlloc v S
      by_contra h_gt
      have h_ge2 : 2 ≤ (XS i).card := by dsimp [XS]; omega
      have hne : (XS i).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨g_star, hg_mem, hg_sup⟩ :=
        Finset.exists_mem_eq_sup (XS i) hne (fun g => ((w g : ℝ) : WithBot ℝ))
      have hv_sing : v i {g_star} = v i (XS i) := by
        rw [hw_eq {g_star}, hw_eq (XS i), hg_sup]
        simp
      obtain ⟨hmem_opt, htie_min, _⟩ := h_spec S
      obtain ⟨hmem_cand, hw_best⟩ := Finset.mem_filter.mp hmem_opt
      obtain ⟨hXS_alloc, hXS_ne⟩ := (Finset.mem_filter.mp hmem_cand).2
      let Y : Fin m → Finset (Fin n) := Function.update XS i {g_star}
      have hY_sub : ∀ j : Fin m, Y j ⊆ XS j := by
        intro j
        by_cases hj : j = i
        · subst hj; simpa [Y] using Finset.singleton_subset_iff.mpr hg_mem
        · simp [Y, hj]
      have hY_alloc : IsAllocOf S Y :=
        ⟨fun j => (hY_sub j).trans (hXS_alloc.1 j),
         fun j1 j2 hne' => Disjoint.mono (hY_sub j1) (hY_sub j2) (hXS_alloc.2 j1 j2 hne')⟩
      have hY_welf : allocWelfare v Y = allocWelfare v XS := by
        unfold allocWelfare
        refine Finset.sum_congr rfl (fun j _ => ?_)
        by_cases hj : j = i
        · subst hj; simpa [Y] using hv_sing
        · simp [Y, hj]
      let cand := (Finset.univ : Finset (Fin m → Finset (Fin n))).filter
        (fun X => IsAllocOf S X ∧ allocWelfare v X ≠ ⊥)
      let optCand := cand.filter (fun X => allocWelfare v X = cand.sup (allocWelfare v))
      have hY_cand : Y ∈ cand :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ Y, hY_alloc, by rwa [hY_welf]⟩
      have hY_opt : Y ∈ optCand :=
        Finset.mem_filter.mpr ⟨hY_cand, hY_welf.trans hw_best⟩
      have h_tie_le : gsAllocTieKey XS ≤ gsAllocTieKey Y := htie_min Y hY_opt
      have h_card_lt : (∑ j : Fin m, (Y j).card) + 1 ≤ ∑ j : Fin m, (XS j).card := by
        have h1 := (Finset.add_sum_erase Finset.univ (fun j => (Y j).card) (Finset.mem_univ i)).symm
        have h2 := (Finset.add_sum_erase Finset.univ (fun j => (XS j).card) (Finset.mem_univ i)).symm
        have h_rest : ∑ j ∈ Finset.erase Finset.univ i, (Y j).card =
            ∑ j ∈ Finset.erase Finset.univ i, (XS j).card := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          simp [Y, (Finset.mem_erase.mp hj).1]
        have hYi : (Y i).card = 1 := by simp [Y]
        omega
      let K : ℕ := 2 ^ (n * m + 1)
      have h_mul_le : (∑ j : Fin m, (Y j).card) * K + K ≤ (∑ j : Fin m, (XS j).card) * K := by
        calc
          (∑ j : Fin m, (Y j).card) * K + K = ((∑ j : Fin m, (Y j).card) + 1) * K := by ring
          _ ≤ (∑ j : Fin m, (XS j).card) * K := Nat.mul_le_mul_right K h_card_lt
      have h_codeY : allocCode Y < K := h_allocCode_lt Y
      unfold gsAllocTieKey at h_tie_le
      change (∑ j : Fin m, (XS j).card) * K + allocCode XS ≤
        (∑ j : Fin m, (Y j).card) * K + allocCode Y at h_tie_le
      omega
    exact ⟨h_part1, h_part2, h_part3⟩
  have h_opt_nonneg : ∀ {n m : ℕ} (v : Fin m → ItemValuation n),
      (∀ i, v i ∅ = ((0 : ℝ) : WithBot ℝ)) → 0 ≤ optWelfare v := by
    intro n m v hv0
    let X0 : Fin m → Finset (Fin n) := fun _ => ∅
    have hX0_alloc : IsAllocOf Finset.univ X0 :=
      ⟨fun _ => Finset.empty_subset _, fun _ _ _ => Finset.disjoint_empty_left ∅⟩
    have hX0_val : allocWelfare v X0 = ((0 : ℝ) : WithBot ℝ) := by
      unfold allocWelfare
      rw [Finset.sum_congr rfl (fun i _ => hv0 i)]
      simp
    let A_univ := (Finset.univ : Finset (Fin m → Finset (Fin n))).filter (fun X => IsAllocOf Finset.univ X)
    have h0_le : ((0 : ℝ) : WithBot ℝ) ≤ A_univ.sup (allocWelfare v) := by
      rw [← hX0_val]
      exact Finset.le_sup (f := allocWelfare v) (Finset.mem_filter.mpr ⟨Finset.mem_univ X0, hX0_alloc⟩)
    have hsup_ne : A_univ.sup (allocWelfare v) ≠ ⊥ := by
      intro hb; rw [hb, le_bot_iff] at h0_le; exact WithBot.coe_ne_bot h0_le
    unfold optWelfare optWelfareOn
    change 0 ≤ (A_univ.sup (allocWelfare v)).unbotD 0
    rw [← WithBot.coe_le_coe, coe_unbotD hsup_ne]
    exact h0_le
  have h_ud_gs : ∀ {n : ℕ} (u : ItemValuation n), IsUnitDemandValuation u → IsGSValuation u := by
    intro n u hud
    obtain ⟨w, hw_nn, hu_eq⟩ := hud
    let uR : Finset (Fin n) → ℝ := fun S =>
      (S.sup (fun g => ((w g : ℝ) : WithBot ℝ))).unbotD 0
    have hu_coe : ∀ S : Finset (Fin n), u S = ((uR S : ℝ) : WithBot ℝ) := hu_eq
    have huR_empty : uR ∅ = 0 := by simp [uR]
    have huR_attain : ∀ S : Finset (Fin n), S.Nonempty →
        ∃ g ∈ S, uR S = w g ∧ ∀ h ∈ S, w h ≤ w g := by
      intro S hne
      obtain ⟨g, hgS, hgsup⟩ :=
        Finset.exists_mem_eq_sup S hne (fun h => ((w h : ℝ) : WithBot ℝ))
      refine ⟨g, hgS, ?_, fun h hhS => ?_⟩
      · dsimp [uR]; rw [hgsup, WithBot.unbotD_coe]
      · have hle : ((w h : ℝ) : WithBot ℝ) ≤ S.sup (fun z => ((w z : ℝ) : WithBot ℝ)) :=
          Finset.le_sup (f := fun z => ((w z : ℝ) : WithBot ℝ)) hhS
        rw [hgsup, WithBot.coe_le_coe] at hle
        exact hle
    have huR_nn : ∀ S : Finset (Fin n), 0 ≤ uR S := by
      intro S
      rcases S.eq_empty_or_nonempty with rfl | hne
      · rw [huR_empty]
      · obtain ⟨g, _, hval, _⟩ := huR_attain S hne
        rw [hval]; exact hw_nn g
    have huR_mem_le : ∀ (S : Finset (Fin n)) (g : Fin n), g ∈ S → w g ≤ uR S := by
      intro S g hgS
      obtain ⟨g_star, _, hval, hmax⟩ := huR_attain S ⟨g, hgS⟩
      rw [hval]; exact hmax g hgS
    have huR_mono : ∀ {A B : Finset (Fin n)}, A ⊆ B → uR A ≤ uR B := by
      intro A B hAB
      rcases A.eq_empty_or_nonempty with rfl | hne
      · rw [huR_empty]; exact huR_nn B
      · obtain ⟨g, hgA, hval, _⟩ := huR_attain A hne
        rw [hval]; exact huR_mem_le B g (hAB hgA)
    refine ⟨by rw [hu_coe ∅, huR_empty], fun X Y _ _ x hx => ?_⟩
    obtain ⟨hxX, hxY⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨x_star, hx_star_mem, hx_star_val, _⟩ := huR_attain X ⟨x, hxX⟩
    by_cases h_eq_x : x_star = x
    · subst h_eq_x
      rcases Y.eq_empty_or_nonempty with rfl | hYne
      · refine le_max_of_le_left ?_
        rw [hu_coe X, hu_coe ∅, hu_coe (X.erase x_star), hu_coe (insert x_star ∅),
            ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
        have h1 : 0 ≤ uR (X.erase x_star) := huR_nn _
        have h2 : w x_star ≤ uR (insert x_star ∅) :=
          huR_mem_le (insert x_star ∅) x_star (Finset.mem_insert_self _ _)
        linarith [hx_star_val, huR_empty]
      · obtain ⟨y_star, hy_star_mem, hy_star_val, _⟩ := huR_attain Y hYne
        by_cases hyX : y_star ∈ X
        · refine le_max_of_le_left ?_
          rw [hu_coe X, hu_coe Y, hu_coe (X.erase x_star), hu_coe (insert x_star Y),
              ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
          have hy_ne : y_star ≠ x_star := fun heq => hxY (heq ▸ hy_star_mem)
          have h1 : w y_star ≤ uR (X.erase x_star) :=
            huR_mem_le (X.erase x_star) y_star (Finset.mem_erase.mpr ⟨hy_ne, hyX⟩)
          have h2 : w x_star ≤ uR (insert x_star Y) :=
            huR_mem_le (insert x_star Y) x_star (Finset.mem_insert_self _ _)
          linarith [hx_star_val, hy_star_val]
        · refine le_max_of_le_right ?_
          have hy_sdiff : y_star ∈ Y \ X := Finset.mem_sdiff.mpr ⟨hy_star_mem, hyX⟩
          refine le_trans ?_
            (Finset.le_sup (f := fun y => u (insert y (X.erase x_star)) + u ((insert x_star Y).erase y)) hy_sdiff)
          dsimp only
          rw [hu_coe X, hu_coe Y, hu_coe (insert y_star (X.erase x_star)),
              hu_coe ((insert x_star Y).erase y_star),
              ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
          have h1 : w y_star ≤ uR (insert y_star (X.erase x_star)) :=
            huR_mem_le _ y_star (Finset.mem_insert_self _ _)
          have hx_ne_y : x_star ≠ y_star := fun heq => hxY (heq ▸ hy_star_mem)
          have h2 : w x_star ≤ uR ((insert x_star Y).erase y_star) :=
            huR_mem_le _ x_star (Finset.mem_erase.mpr ⟨hx_ne_y, Finset.mem_insert_self _ _⟩)
          linarith [hx_star_val, hy_star_val]
    · refine le_max_of_le_left ?_
      rw [hu_coe X, hu_coe Y, hu_coe (X.erase x), hu_coe (insert x Y),
          ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
      have h1 : w x_star ≤ uR (X.erase x) :=
        huR_mem_le (X.erase x) x_star (Finset.mem_erase.mpr ⟨h_eq_x, hx_star_mem⟩)
      have h2 : uR Y ≤ uR (insert x Y) := huR_mono (Finset.subset_insert x Y)
      linarith [hx_star_val]
  
  
  
  have dom_erase : ∀ {n : ℕ} {v : ItemValuation n}, IsGSValuation v →
      ∀ (X : Finset (Fin n)) (x : Fin n), v X ≠ ⊥ → x ∈ X → v (X.erase x) ≠ ⊥ := by
    intro n v hv X x hX hx
    have hv0 : v ∅ ≠ ⊥ := by rw [hv.1]; exact WithBot.coe_ne_bot
    have hex := hv.2 X ∅ hX hv0 x (by simp [hx])
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
        rwa [Finset.Subset.antisymm hYX hsub]
      | succ k ih =>
        intro X hk hYX hX
        obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < (X \ Y).card)
        obtain ⟨hxX, hxY⟩ := Finset.mem_sdiff.mp hx
        have hsdiff : X.erase x \ Y = (X \ Y).erase x := by ext z; simp [and_assoc]
        have hk' : (X.erase x \ Y).card = k := by rw [hsdiff, Finset.card_erase_of_mem hx]; omega
        exact ih (X.erase x) hk' (Finset.subset_erase.mpr ⟨hYX, hxY⟩) (dom_erase hv X x hX hxX)
    exact h_ind (X \ Y).card X rfl hYX hX
  have gs_submod : ∀ {n : ℕ} {v : ItemValuation n}, IsGSValuation v →
      ∀ (Q R : Finset (Fin n)) (g : Fin n), Q ⊆ R → g ∉ R → v (insert g R) ≠ ⊥ →
        realVal v (insert g R) - realVal v R ≤ realVal v (insert g Q) - realVal v Q := by
    intro n v hv Q R g hQR hgR hRg
    have hgQ : g ∉ Q := fun hg => hgR (hQR hg)
    have hR : v R ≠ ⊥ := dom_hereditary hv (Finset.subset_insert g R) hRg
    have hQg : v (insert g Q) ≠ ⊥ := dom_hereditary hv (Finset.insert_subset_insert g hQR) hRg
    have hQ : v Q ≠ ⊥ := dom_hereditary hv (hQR.trans (Finset.subset_insert g R)) hRg
    have hex := hv.2 (insert g R) Q hRg hQ g (Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self g R, hgQ⟩)
    have hsdiff_empty : Q \ insert g R = ∅ :=
      Finset.sdiff_eq_empty_iff_subset.mpr (hQR.trans (Finset.subset_insert g R))
    rw [Finset.erase_insert hgR, hsdiff_empty, Finset.sup_empty, max_bot_right] at hex
    rw [← coe_realVal v (insert g R) hRg, ← coe_realVal v Q hQ,
        ← coe_realVal v R hR, ← coe_realVal v (insert g Q) hQg,
        ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe] at hex
    linarith
  have gs_additive_support : ∀ {n : ℕ} (v : ItemValuation n) (X : Finset (Fin n)),
      IsGSValuation v → v X ≠ ⊥ →
        ∃ a : Fin n → ℝ,
          (∑ g ∈ X, a g) = realVal v X ∧
          (∀ Y ⊆ X, ((∑ g ∈ Y, a g : ℝ) : WithBot ℝ) ≤ v Y) := by
    intro n v X hv hX
    let marg : Finset (Fin n) → Fin n → ℝ :=
      fun S g => realVal v (insert g S) - realVal v S
    have h_tele : ∀ (k : ℕ) (Y : Finset (Fin n)), Y.card ≤ k →
        ∑ g ∈ Y, marg (Y.filter (fun h => h < g)) g = realVal v Y := by
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
          let Y' := Finset.erase Y m
          have hY'_card : Y'.card ≤ k := by
            dsimp [Y']
            have hlt := Finset.card_erase_lt_of_mem hmY
            omega
          rw [← Finset.add_sum_erase Y _ hmY]
          have h_filt_m : Y.filter (fun h => h < m) = Y' := by
            ext y; simp only [Finset.mem_filter, Y', Finset.mem_erase]
            exact ⟨fun ⟨hyY, hylt⟩ => ⟨ne_of_lt hylt, hyY⟩,
                   fun ⟨hyne, hyY⟩ => ⟨hyY, lt_of_le_of_ne (Finset.le_max' Y y hyY) hyne⟩⟩
          have h_term_m : marg (Y.filter (fun h => h < m)) m = realVal v Y - realVal v Y' := by
            dsimp [marg]; rw [h_filt_m, Finset.insert_erase hmY]
          have h_rest : ∑ g ∈ Y', marg (Y.filter (fun h => h < g)) g =
              ∑ g ∈ Y', marg (Y'.filter (fun h => h < g)) g := by
            refine Finset.sum_congr rfl (fun g hgY' => ?_)
            obtain ⟨hgne, hgY⟩ := Finset.mem_erase.mp hgY'
            have hglt : g < m := lt_of_le_of_ne (Finset.le_max' Y g hgY) hgne
            have h_filt_g : Y.filter (fun h => h < g) = Y'.filter (fun h => h < g) := by
              ext y; simp only [Finset.mem_filter, Y', Finset.mem_erase]
              exact ⟨fun ⟨hyY, hylt⟩ => ⟨⟨ne_of_lt (lt_trans hylt hglt), hyY⟩, hylt⟩,
                     fun ⟨⟨_, hyY⟩, hylt⟩ => ⟨hyY, hylt⟩⟩
            rw [h_filt_g]
          rw [h_term_m, h_rest, ih Y' hY'_card]
          ring
    let a : Fin n → ℝ := fun g => marg (X.filter (fun h => h < g)) g
    refine ⟨a, h_tele X.card X le_rfl, fun Y hYX => ?_⟩
    have hY_ne : v Y ≠ ⊥ := dom_hereditary hv hYX hX
    rw [← coe_realVal v Y hY_ne, WithBot.coe_le_coe]
    calc
      ∑ g ∈ Y, a g ≤ ∑ g ∈ Y, marg (Y.filter (fun h => h < g)) g := by
        refine Finset.sum_le_sum (fun g hgY => ?_)
        have hsub : Y.filter (fun h => h < g) ⊆ X.filter (fun h => h < g) :=
          Finset.filter_subset_filter _ hYX
        have hg_not : g ∉ X.filter (fun h => h < g) := by simp
        have h_ins_sub : insert g (X.filter (fun h => h < g)) ⊆ X :=
          Finset.insert_subset_iff.mpr ⟨hYX hgY, Finset.filter_subset _ X⟩
        exact gs_submod hv (Y.filter (fun h => h < g)) (X.filter (fun h => h < g)) g
          hsub hg_not (dom_hereditary hv h_ins_sub hX)
      _ = realVal v Y := h_tele Y.card Y le_rfl
  have h_s4_prefix : ∀ {n m : ℕ} (v : Fin m → ItemValuation n) (k : ℕ),
      k + 1 ≤ n → (∀ i : Fin m, IsGSValuation (v i)) →
        (((k + 1 : ℕ) : ℝ) / (n : ℝ)) * ((Nat.factorial n : ℝ) * optWelfare v) ≤
          ∑ π : Equiv.Perm (Fin n), optWelfareOn v (arrivalPrefixSet π (k + 1)) := by
    intro n m v k hk hv
    have hv0 : ∀ i : Fin m, v i ∅ = ((0 : ℝ) : WithBot ℝ) := fun i => (hv i).1
    obtain ⟨h_s3_1, h_s3_2, _⟩ := h_s3_main v hv0
    let Xstar := gsPrefixOptAlloc v Finset.univ
    have hXstar_alloc : IsAllocOf Finset.univ Xstar := (h_s3_1 Finset.univ).1
    have hXstar_welf : allocWelfare v Xstar = ((optWelfare v : ℝ) : WithBot ℝ) :=
      (h_s3_1 Finset.univ).2.1
    have hXi_ne : ∀ i : Fin m, v i (Xstar i) ≠ ⊥ := fun i => (h_s3_2 i Finset.univ).2.1
    have h_opt_sum : optWelfare v = ∑ i : Fin m, realVal (v i) (Xstar i) := by
      have h_coe : ((optWelfare v : ℝ) : WithBot ℝ) =
          ((∑ i : Fin m, realVal (v i) (Xstar i) : ℝ) : WithBot ℝ) := by
        rw [← hXstar_welf, WithBot.coe_sum]; unfold allocWelfare
        exact Finset.sum_congr rfl (fun i _ => (coe_realVal (v i) (Xstar i) (hXi_ne i)).symm)
      exact WithBot.coe_inj.mp h_coe
    have h_ex_a : ∀ i : Fin m, ∃ a : Fin n → ℝ,
        (∑ g ∈ Xstar i, a g) = realVal (v i) (Xstar i) ∧
        (∀ Y ⊆ Xstar i, ((∑ g ∈ Y, a g : ℝ) : WithBot ℝ) ≤ v i Y) :=
      fun i => gs_additive_support (v i) (Xstar i) (hv i) (hXi_ne i)
    let a : Fin m → Fin n → ℝ := fun i => Classical.choose (h_ex_a i)
    have ha_sum : ∀ i : Fin m, (∑ g ∈ Xstar i, a i g) = realVal (v i) (Xstar i) :=
      fun i => (Classical.choose_spec (h_ex_a i)).1
    have ha_low : ∀ (i : Fin m) (Y : Finset (Fin n)),
        Y ⊆ Xstar i → ((∑ g ∈ Y, a i g : ℝ) : WithBot ℝ) ≤ v i Y :=
      fun i => (Classical.choose_spec (h_ex_a i)).2
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
      have h_sup_opt : A_R.sup (allocWelfare v) = ((optWelfareOn v R : ℝ) : WithBot ℝ) := by
        have h_cand_welf := (h_s3_1 R).2.1
        have h_gs_alloc := (h_s3_1 R).1
        have h_le1 : ((optWelfareOn v R : ℝ) : WithBot ℝ) ≤ A_R.sup (allocWelfare v) := by
          rw [← h_cand_welf]
          exact Finset.le_sup (f := allocWelfare v) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_gs_alloc⟩)
        have hsup_ne : A_R.sup (allocWelfare v) ≠ ⊥ := by
          intro hb; rw [hb, le_bot_iff] at h_le1; exact WithBot.coe_ne_bot h_le1
        unfold optWelfareOn
        exact (coe_unbotD hsup_ne).symm
      rw [← WithBot.coe_le_coe, WithBot.coe_sum, ← h_sup_opt]
      refine le_trans ?_ (Finset.le_sup (f := allocWelfare v) hXR_mem)
      unfold allocWelfare
      exact Finset.sum_le_sum (fun i _ => ha_low i (XR i) (hXR_X i))
    have h_perm_count : ∀ g : Fin n,
        (((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
            (fun π => g ∈ arrivalPrefixSet π (k + 1))).card : ℝ) =
          (((k + 1 : ℕ) : ℝ) / (n : ℝ)) * (Nat.factorial n : ℝ) := by
      intro g
      let F : Fin n → Finset (Equiv.Perm (Fin n)) :=
        fun idx => (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => π idx = g)
      have hF_eq : ∀ idx₁ idx₂ : Fin n, (F idx₁).card = (F idx₂).card := by
        intro idx₁ idx₂
        refine Finset.card_bij (fun π _ => π * Equiv.swap idx₁ idx₂) ?_ ?_ ?_
        · intro π hπ
          dsimp only [F] at hπ ⊢
          rw [Finset.mem_filter] at hπ ⊢
          refine ⟨Finset.mem_univ _, ?_⟩
          change π (Equiv.swap idx₁ idx₂ idx₂) = g
          rw [Equiv.swap_apply_right]
          exact hπ.2
        · intro π₁ _ π₂ _ heq
          dsimp only at heq
          have := congrArg (fun σ => σ * Equiv.swap idx₁ idx₂) heq
          simpa [mul_assoc] using this
        · intro σ hσ
          have hσg : σ idx₂ = g := (Finset.mem_filter.mp hσ).2
          refine ⟨σ * Equiv.swap idx₁ idx₂, ?_, ?_⟩
          · rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_⟩
            change σ (Equiv.swap idx₁ idx₂ idx₁) = g
            rw [Equiv.swap_apply_left]
            exact hσg
          · dsimp only
            ext x
            simp
      have hF_disj : ∀ (S_idx : Finset (Fin n)),
          (S_idx : Set (Fin n)).PairwiseDisjoint F := by
        intro S_idx idx₁ _ idx₂ _ hne
        change Disjoint (F idx₁) (F idx₂)
        rw [Finset.disjoint_left]
        intro π h₁ h₂
        have hg₁ : π idx₁ = g := (Finset.mem_filter.mp h₁).2
        have hg₂ : π idx₂ = g := (Finset.mem_filter.mp h₂).2
        exact hne (π.injective (hg₁.trans hg₂.symm))
      let idx0 : Fin n := ⟨0, by omega⟩
      have h_univ_part : (Finset.univ : Finset (Equiv.Perm (Fin n))) =
          (Finset.univ : Finset (Fin n)).biUnion F := by
        ext π
        simp only [Finset.mem_univ, Finset.mem_biUnion, F, Finset.mem_filter, true_and]
        exact ⟨fun _ => ⟨π.symm g, by simp⟩, fun _ => trivial⟩
      have h_fact : n * (F idx0).card = Nat.factorial n := by
        have h1 : (Finset.univ : Finset (Equiv.Perm (Fin n))).card = Nat.factorial n := by
          rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
        rw [h_univ_part, Finset.card_biUnion (hF_disj Finset.univ)] at h1
        rw [Finset.sum_congr rfl (fun idx _ => hF_eq idx idx0), Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
        exact h1
      let prefIdx := (Finset.univ : Finset (Fin n)).filter (fun idx : Fin n => idx.1 < k + 1)
      have h_pref_part : (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
            (fun π => g ∈ arrivalPrefixSet π (k + 1)) =
          prefIdx.biUnion F := by
        ext π
        simp [arrivalPrefixSet, prefIdx, F]
      have h_prefIdx_card : prefIdx.card = k + 1 := by
        rw [← Finset.card_range (k + 1)]
        refine Finset.card_bij (fun (idx : Fin n) _ => idx.1) ?_ ?_ ?_
        · intro idx hidx
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hidx).2
        · intro idx₁ _ idx₂ _ heq
          exact Fin.ext heq
        · intro r hr
          have hr_lt : r < k + 1 := Finset.mem_range.mp hr
          refine ⟨⟨r, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr_lt⟩, rfl⟩
      have h_filt_card : ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
            (fun π => g ∈ arrivalPrefixSet π (k + 1))).card = (k + 1) * (F idx0).card := by
        rw [h_pref_part, Finset.card_biUnion (hF_disj prefIdx),
            Finset.sum_congr rfl (fun idx _ => hF_eq idx idx0),
            Finset.sum_const, h_prefIdx_card, smul_eq_mul]
      have h_factR : (n : ℝ) * ((F idx0).card : ℝ) = (Nat.factorial n : ℝ) := by
        exact_mod_cast h_fact
      have hn_ne : (n : ℝ) ≠ 0 := by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
        linarith
      rw [h_filt_card, Nat.cast_mul]
      calc
        ((k + 1 : ℕ) : ℝ) * ((F idx0).card : ℝ)
          = (((k + 1 : ℕ) : ℝ) / (n : ℝ)) * ((n : ℝ) * ((F idx0).card : ℝ)) := by
            rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel_left₀ hn_ne]
        _ = (((k + 1 : ℕ) : ℝ) / (n : ℝ)) * (Nat.factorial n : ℝ) := by rw [h_factR]
    have h_sum_le : ∑ π : Equiv.Perm (Fin n),
          (∑ i : Fin m, ∑ g ∈ (Xstar i).filter (fun g => g ∈ arrivalPrefixSet π (k + 1)), a i g) ≤
        ∑ π : Equiv.Perm (Fin n), optWelfareOn v (arrivalPrefixSet π (k + 1)) :=
      Finset.sum_le_sum (fun π _ => h_R_bound (arrivalPrefixSet π (k + 1)))
    have h_lhs_eval : ∑ π : Equiv.Perm (Fin n),
          (∑ i : Fin m, ∑ g ∈ (Xstar i).filter (fun g => g ∈ arrivalPrefixSet π (k + 1)), a i g) =
        (((k + 1 : ℕ) : ℝ) / (n : ℝ)) * ((Nat.factorial n : ℝ) * optWelfare v) := by
      calc
        ∑ π : Equiv.Perm (Fin n),
            (∑ i : Fin m, ∑ g ∈ (Xstar i).filter (fun g => g ∈ arrivalPrefixSet π (k + 1)), a i g)
          = ∑ i : Fin m, ∑ π : Equiv.Perm (Fin n),
              ∑ g ∈ Xstar i, (if g ∈ arrivalPrefixSet π (k + 1) then a i g else 0) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun π _ => ?_))
            rw [Finset.sum_filter]
        _ = ∑ i : Fin m, ∑ g ∈ Xstar i,
              ∑ π : Equiv.Perm (Fin n), (if g ∈ arrivalPrefixSet π (k + 1) then a i g else 0) := by
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
        _ = ∑ i : Fin m, ∑ g ∈ Xstar i,
              (((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
                (fun π => g ∈ arrivalPrefixSet π (k + 1))).card : ℝ) * a i g := by
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun g _ => ?_))
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        _ = ∑ i : Fin m, ∑ g ∈ Xstar i,
              ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) * (Nat.factorial n : ℝ)) * a i g := by
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun g _ => ?_))
            rw [h_perm_count g]
        _ = (((k + 1 : ℕ) : ℝ) / (n : ℝ)) * ((Nat.factorial n : ℝ) * optWelfare v) := by
            rw [h_opt_sum, Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [← Finset.mul_sum, ha_sum i]
            ring
    linarith
  have h_s4_cutoff : ∀ n : ℕ, 2 ≤ n → ∃ s : ℕ, 1 ≤ s ∧ s < n ∧ invE ≤ secretaryCutoffConst n s := by
    intro n hn2
    have h_invE_pos : 0 < invE := Real.exp_pos (-1)
    have h_exp_prod : Real.exp 1 * invE = 1 := by
      dsimp [invE]; rw [← Real.exp_add]; norm_num
    rcases eq_or_lt_of_le hn2 with rfl | hn3
    · refine ⟨1, le_rfl, by omega, ?_⟩
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
        dsimp [ζ]; linarith
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
      let η : ℝ := ζ - (s0 : ℝ)
      have hη_nn : 0 ≤ η := by dsimp [η, s0]; linarith [Nat.floor_le (le_of_lt hζ_pos)]
      have h1mη_pos : 0 < 1 - η := by dsimp [η, s0]; linarith [Nat.lt_floor_add_one ζ]
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
          have hlog := Real.log_le_sub_one_of_pos (div_pos hj1_pos hj_pos)
          rw [Real.log_div (ne_of_gt hj1_pos) (ne_of_gt hj_pos)] at hlog
          have h_alg : ((j + 1 : ℕ) : ℝ) / (j : ℝ) - 1 = 1 / (j : ℝ) := by
            rw [Nat.cast_add, Nat.cast_one]
            have hj_ne : (j : ℝ) ≠ 0 := ne_of_gt hj_pos
            field_simp; ring
          linarith
        have h_sum := Finset.sum_le_sum h_term
        let f : ℕ → ℝ := fun k => Real.log (k : ℝ)
        have h_tele : ∑ j ∈ Finset.Ico (s0 + 1) n, (f (j + 1) - f j) = f n - f (s0 + 1) := by
          rw [Finset.sum_Ico_eq_sub (fun j => f (j + 1) - f j) (le_of_lt hs01_lt_n),
              Finset.sum_range_sub f n, Finset.sum_range_sub f (s0 + 1)]
          ring
        dsimp [f] at h_tele
        rw [Nat.cast_add, Nat.cast_one] at h_tele
        dsimp [H]; linarith
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
        dsimp [ζ]; exact mul_div_cancel_left₀ invE (ne_of_gt hn_pos)
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
      have hc0 : secretaryCutoffConst n s0 < invE := h_none s0 hs0_ge_1 hs0_lt_n
      have hc1 : secretaryCutoffConst n (s0 + 1) < invE := h_none (s0 + 1) (by omega) hs01_lt_n
      have hlt0 : (1 - η) * secretaryCutoffConst n s0 < (1 - η) * invE :=
        mul_lt_mul_of_pos_left hc0 h1mη_pos
      have hle1 : η * secretaryCutoffConst n (s0 + 1) ≤ η * invE :=
        mul_le_mul_of_nonneg_left (le_of_lt hc1) hη_nn
      linarith
  have h_s4_small : ∀ (n m : ℕ), n ≤ 1 →
      ∃ alg : OnlineWelfareAlg n m,
        ∀ v : Fin m → ItemValuation n, (∀ i, IsGSValuation (v i)) →
          (((invE * optWelfare v : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg v) := by
    intro n m hn
    let detAlg : DetWelfareAlg n m :=
      { step := fun prev x _ oracle =>
          let hx_sub : ({x} : Finset (Fin n)) ⊆ insert x prev.toFinset :=
            Finset.singleton_subset_iff.mpr (Finset.mem_insert_self x _)
          let posB := (Finset.univ : Finset (Fin m)).filter
            (fun i => ((0 : ℝ) : WithBot ℝ) < oracle i ⟨{x}, hx_sub⟩)
          if _hne : posB.Nonempty then
            let best := posB.sup (fun i => oracle i ⟨{x}, hx_sub⟩)
            let ties := posB.filter (fun i => oracle i ⟨{x}, hx_sub⟩ = best)
            if ht : ties.Nonempty then some (ties.min' ht) else none
          else none }
    let alg : OnlineWelfareAlg n m :=
      { Seed := PUnit
        seedMeasure := MeasureTheory.Measure.dirac ()
        isProb := inferInstance
        det := fun _ => detAlg
        meas_step := fun prev x bundles oracle dec => by
          by_cases h : detAlg.step prev x bundles oracle = dec
          · have : {ω : PUnit | detAlg.step prev x bundles oracle = dec} = Set.univ := by
              ext _; simp [h]
            rw [this]; exact MeasurableSet.univ
          · have : {ω : PUnit | detAlg.step prev x bundles oracle = dec} = ∅ := by
              ext _; simp [h]
            rw [this]; exact MeasurableSet.empty }
    have h_punit_real : ∀ (P : Prop) [Decidable P],
        alg.seedMeasure.real {ω : alg.Seed | P} = if P then 1 else 0 := by
      intro P _
      by_cases hP : P
      · have hset : {ω : alg.Seed | P} = Set.univ := by ext _; simp [hP]
        rw [if_pos hP, hset]
        exact MeasureTheory.probReal_univ
      · have hset : {ω : alg.Seed | P} = ∅ := by ext _; simp [hP]
        rw [if_neg hP, hset]
        exact MeasureTheory.measureReal_empty
    refine ⟨alg, fun v hv => ?_⟩
    have hv0 : ∀ i : Fin m, v i ∅ = ((0 : ℝ) : WithBot ℝ) := fun i => (hv i).1
    have h_invE_le_one : invE ≤ 1 := by
      dsimp [invE]; exact Real.exp_le_one_iff.mpr (by norm_num)
    have h_opt_nn : 0 ≤ optWelfare v := h_opt_nonneg v hv0
    have h_invE_opt : invE * optWelfare v ≤ optWelfare v := by
      calc invE * optWelfare v ≤ 1 * optWelfare v := mul_le_mul_of_nonneg_right h_invE_le_one h_opt_nn
        _ = optWelfare v := one_mul _
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
    · 
      let X0 : Fin m → Finset (Fin 0) := fun _ => ∅
      have h_all_X : ∀ X : Fin m → Finset (Fin 0), X = X0 := by
        intro X; funext i; ext z; exact Fin.elim0 z
      have hX0_val : allocWelfare v X0 = ((0 : ℝ) : WithBot ℝ) := by
        unfold allocWelfare
        rw [Finset.sum_congr rfl (fun i _ => hv0 i)]; simp
      have h_no_bot : ¬ ∃ X : Fin m → Finset (Fin 0),
          0 < algWelfareProb alg v X ∧ allocWelfare v X = ⊥ := by
        rintro ⟨X, _, hbot⟩
        rw [h_all_X X, hX0_val] at hbot
        exact WithBot.coe_ne_bot hbot
      have h_opt_zero : optWelfare v = 0 := by
        have h_gs_welf := ((h_s3_main v hv0).1 Finset.univ).2.1
        rw [h_all_X (gsPrefixOptAlloc v Finset.univ), hX0_val] at h_gs_welf
        exact (WithBot.coe_inj.mp h_gs_welf).symm
      unfold expectedWelfareVal
      rw [if_neg h_no_bot, h_opt_zero, mul_zero, WithBot.coe_le_coe]
      have h_sum_zero : ∑ X : Fin m → Finset (Fin 0),
          algWelfareProb alg v X * (allocWelfare v X).unbotD 0 = 0 := by
        refine Finset.sum_eq_zero (fun X _ => ?_)
        rw [h_all_X X, hX0_val, WithBot.unbotD_coe, mul_zero]
      rw [h_sum_zero]
    · 
      let g0 : Fin 1 := ⟨0, Nat.zero_lt_one⟩
      have h_fin1 : ∀ z : Fin 1, z = g0 := fun z => Fin.ext (by omega)
      have h_perm_univ : (Finset.univ : Finset (Equiv.Perm (Fin 1))) = {1} := by
        ext π
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        ext z; omega
      let X_alg := runDetWelfare detAlg v 1
      have h_prob_eq : ∀ X : Fin m → Finset (Fin 1),
          algWelfareProb alg v X = if X_alg = X then 1 else 0 := by
        intro X
        unfold algWelfareProb
        have h_det_eq : ∀ π : Equiv.Perm (Fin 1),
            alg.seedMeasure.real {ω | runDetWelfare (alg.det ω) v π = X} =
              if runDetWelfare detAlg v π = X then 1 else 0 :=
          fun π => h_punit_real (runDetWelfare detAlg v π = X)
        rw [Finset.sum_congr rfl (fun π _ => h_det_eq π), h_perm_univ, Finset.sum_singleton]
        change (1 / (Nat.factorial 1 : ℝ)) * (if X_alg = X then 1 else 0) = _
        norm_num
      have h_X_alg_eq : X_alg = match detAlg.step [] g0 (fun _ => ∅) (fun i ⟨T, _⟩ => v i T) with
          | none => fun _ => ∅
          | some i => Function.update (fun _ => ∅) i {g0} := by
        change (runDetWelfareSteps detAlg v 1 1 (le_refl 1)).2 = _
        dsimp [runDetWelfareSteps]
        have hg0_zero : (0 : Fin 1) = g0 := rfl
        rw [hg0_zero]
        cases detAlg.step [] g0 (fun _ => ∅) (fun i ⟨T, _⟩ => v i T) <;> rfl
      have h_subset_g0 : ∀ S : Finset (Fin 1), S = ∅ ∨ S = {g0} := by
        intro S
        rcases S.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
        · exact Or.inl rfl
        · refine Or.inr (Finset.Subset.antisymm (fun y _ => ?_) ?_)
          · rw [h_fin1 y]; exact Finset.mem_singleton_self g0
          · rw [← h_fin1 z]; exact Finset.singleton_subset_iff.mpr hz
      have h_opt_ub : ∀ b : WithBot ℝ, ((0 : ℝ) : WithBot ℝ) ≤ b →
          (∀ i : Fin m, v i {g0} ≤ b) → ((optWelfare v : ℝ) : WithBot ℝ) ≤ b := by
        intro b hb0 hbi
        let XS := gsPrefixOptAlloc v Finset.univ
        obtain ⟨⟨_, hXS_disj⟩, hXS_welf, _⟩ := (h_s3_main v hv0).1 Finset.univ
        have hXS_welf' : allocWelfare v XS = ((optWelfareOn v Finset.univ : ℝ) : WithBot ℝ) := hXS_welf
        unfold optWelfare
        rw [← hXS_welf']
        by_cases hex : ∃ i0 : Fin m, XS i0 = {g0}
        · obtain ⟨i0, hi0⟩ := hex
          unfold allocWelfare
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0), hi0]
          have h_rest : ∑ j ∈ Finset.erase Finset.univ i0, v j (XS j) = ((0 : ℝ) : WithBot ℝ) := by
            have h_each : ∀ j ∈ Finset.erase Finset.univ i0, v j (XS j) = ((0 : ℝ) : WithBot ℝ) := by
              intro j hj
              have hjne : j ≠ i0 := (Finset.mem_erase.mp hj).1
              rcases h_subset_g0 (XS j) with hemp | hsing
              · rw [hemp, hv0 j]
              · exfalso
                have hdisj : Disjoint (XS j) (XS i0) := hXS_disj j i0 hjne
                rw [hsing, hi0, Finset.disjoint_singleton] at hdisj
                exact hdisj rfl
            rw [Finset.sum_congr rfl h_each]
            simp
          rw [h_rest, WithBot.coe_zero, add_zero]
          exact hbi i0
        · push_neg at hex
          have h_each : ∀ j : Fin m, v j (XS j) = ((0 : ℝ) : WithBot ℝ) := by
            intro j
            rcases h_subset_g0 (XS j) with hemp | hsing
            · rw [hemp, hv0 j]
            · exfalso; exact hex j hsing
          unfold allocWelfare
          rw [Finset.sum_congr rfl (fun j _ => h_each j)]
          simpa using hb0
      have h_X_alg_spec : allocWelfare v X_alg = ((optWelfare v : ℝ) : WithBot ℝ) := by
        let posB := (Finset.univ : Finset (Fin m)).filter
          (fun i => ((0 : ℝ) : WithBot ℝ) < v i {g0})
        by_cases hne : posB.Nonempty
        · let best := posB.sup (fun i => v i {g0})
          obtain ⟨i1, hi1_pos, hi1_eq⟩ := Finset.exists_mem_eq_sup posB hne (fun i => v i {g0})
          let ties := posB.filter (fun i => v i {g0} = best)
          have ht : ties.Nonempty := ⟨i1, Finset.mem_filter.mpr ⟨hi1_pos, hi1_eq.symm⟩⟩
          let i_star := ties.min' ht
          have hi_star_ties : i_star ∈ ties := Finset.min'_mem ties ht
          obtain ⟨hi_star_pos, hi_star_best⟩ := Finset.mem_filter.mp hi_star_ties
          have hi_star_gt0 : ((0 : ℝ) : WithBot ℝ) < v i_star {g0} :=
            (Finset.mem_filter.mp hi_star_pos).2
          have h_step_eq : detAlg.step [] g0 (fun _ => ∅) (fun i ⟨T, _⟩ => v i T) = some i_star := by
            dsimp [detAlg]
            change (if h1 : posB.Nonempty then
              if h2 : ties.Nonempty then some (ties.min' h2) else none else none) = some i_star
            rw [dif_pos hne, dif_pos ht]
          rw [h_X_alg_eq, h_step_eq]
          dsimp only
          have hw_alg : allocWelfare v (Function.update (fun _ => ∅) i_star {g0}) = v i_star {g0} := by
            unfold allocWelfare
            rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i_star)]
            have h_rest : ∑ j ∈ Finset.erase Finset.univ i_star,
                v j (Function.update (fun _ : Fin m => (∅ : Finset (Fin 1))) i_star {g0} j) = 0 := by
              refine Finset.sum_eq_zero (fun j hj => ?_)
              simp [(Finset.mem_erase.mp hj).1, hv0 j]
            simp [h_rest]
          rw [hw_alg]
          refine le_antisymm ?_ ?_
          · have h_alloc : IsAllocOf Finset.univ
                (Function.update (fun _ : Fin m => (∅ : Finset (Fin 1))) i_star {g0}) := by
              refine ⟨fun _ => Finset.subset_univ _, fun j1 j2 hne' => ?_⟩
              by_cases hj1 : j1 = i_star
              · subst hj1; simp [hne'.symm]
              · simp [hj1]
            let A_univ := (Finset.univ : Finset (Fin m → Finset (Fin 1))).filter
              (fun X => IsAllocOf Finset.univ X)
            have h_sup_opt : A_univ.sup (allocWelfare v) = ((optWelfare v : ℝ) : WithBot ℝ) := by
              have h_gs_welf := ((h_s3_main v hv0).1 Finset.univ).2.1
              have h_gs_alloc := ((h_s3_main v hv0).1 Finset.univ).1
              have hle : ((optWelfare v : ℝ) : WithBot ℝ) ≤ A_univ.sup (allocWelfare v) := by
                unfold optWelfare
                rw [← h_gs_welf]
                exact Finset.le_sup (f := allocWelfare v)
                  (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_gs_alloc⟩)
              have hsne : A_univ.sup (allocWelfare v) ≠ ⊥ := by
                intro hb; rw [hb, le_bot_iff] at hle; exact WithBot.coe_ne_bot hle
              unfold optWelfare optWelfareOn
              exact (coe_unbotD hsne).symm
            rw [← hw_alg, ← h_sup_opt]
            exact Finset.le_sup (f := allocWelfare v)
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_alloc⟩)
          · refine h_opt_ub (v i_star {g0}) (le_of_lt hi_star_gt0) (fun i => ?_)
            by_cases hi : ((0 : ℝ) : WithBot ℝ) < v i {g0}
            · rw [hi_star_best]
              exact Finset.le_sup (f := fun j => v j {g0}) (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
            · exact (le_of_not_gt hi).trans (le_of_lt hi_star_gt0)
        · have h_step_eq : detAlg.step [] g0 (fun _ => ∅) (fun i ⟨T, _⟩ => v i T) = none := by
            dsimp [detAlg]
            change (if h1 : posB.Nonempty then _ else none) = none
            rw [dif_neg hne]
          rw [h_X_alg_eq, h_step_eq]
          dsimp only
          have hw_alg : allocWelfare v (fun _ => ∅) = ((0 : ℝ) : WithBot ℝ) := by
            unfold allocWelfare
            rw [Finset.sum_congr rfl (fun j _ => hv0 j)]; simp
          rw [hw_alg]
          refine le_antisymm (WithBot.coe_le_coe.mpr h_opt_nn) ?_
          refine h_opt_ub ((0 : ℝ) : WithBot ℝ) le_rfl (fun i => ?_)
          have hnot : i ∉ posB := fun hmem => hne ⟨i, hmem⟩
          have hnot_lt : ¬ (((0 : ℝ) : WithBot ℝ) < v i {g0}) := by
            simpa [posB] using hnot
          exact le_of_not_gt hnot_lt
      have h_no_bot : ¬ ∃ X : Fin m → Finset (Fin 1),
          0 < algWelfareProb alg v X ∧ allocWelfare v X = ⊥ := by
        rintro ⟨X, hpos, hbot⟩
        rw [h_prob_eq X] at hpos
        by_cases hX : X_alg = X
        · subst hX
          rw [h_X_alg_spec] at hbot
          exact WithBot.coe_ne_bot hbot
        · rw [if_neg hX] at hpos; linarith
      unfold expectedWelfareVal
      rw [if_neg h_no_bot, WithBot.coe_le_coe]
      have h_sum_eval : ∑ X : Fin m → Finset (Fin 1),
          algWelfareProb alg v X * (allocWelfare v X).unbotD 0 = optWelfare v := by
        have h_term : ∀ X : Fin m → Finset (Fin 1),
            algWelfareProb alg v X * (allocWelfare v X).unbotD 0 =
              if X_alg = X then optWelfare v else 0 := by
          intro X
          rw [h_prob_eq X]
          by_cases hX : X_alg = X
          · subst hX
            rw [if_pos rfl, if_pos rfl, h_X_alg_spec, WithBot.unbotD_coe, one_mul]
          · rw [if_neg hX, if_neg hX, zero_mul]
        rw [Finset.sum_congr rfl (fun X _ => h_term X)]
        simp
      rw [h_sum_eval]
      exact h_invE_opt
  
  have h_pref_step : ∀ {n : ℕ} (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k + 1 ≤ n),
      insert (π ⟨k, hk⟩) (arrivalPrefixSet π k) = arrivalPrefixSet π (k + 1) := by
    intro n π k hk
    ext y
    simp only [Finset.mem_insert, arrivalPrefixSet, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro (rfl | ⟨idx, hlt, rfl⟩)
      · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, rfl⟩
      · exact ⟨idx, Nat.lt_succ_of_lt hlt, rfl⟩
    · rintro ⟨idx, hlt, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
      · exact Or.inr ⟨idx, hlt', rfl⟩
      · exact Or.inl (congrArg π (Fin.ext heq))
  have h_pref_notMem : ∀ {n : ℕ} (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k + 1 ≤ n),
      π ⟨k, hk⟩ ∉ arrivalPrefixSet π k := by
    intro n π k hk hmem
    simp only [arrivalPrefixSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hmem
    obtain ⟨idx, hlt, heq⟩ := hmem
    have hidx : idx = ⟨k, hk⟩ := π.injective heq
    have : idx.1 = k := congrArg Fin.val hidx
    omega
  have h_card_pref : ∀ {n : ℕ} (π : Equiv.Perm (Fin n)) (t : ℕ),
      t ≤ n → (arrivalPrefixSet π t).card = t := by
    intro n π t ht
    unfold arrivalPrefixSet
    have h_eq_card : ((Finset.univ : Finset (Fin n)).filter (fun idx => idx.1 < t)).card =
        (Finset.range t).card := by
      refine Finset.card_bij (fun (idx : Fin n) _ => idx.1) ?_ ?_ ?_
      · intro idx hidx
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hidx).2
      · intro idx₁ _ idx₂ _ heq
        exact Fin.ext heq
      · intro r hr
        have hr_lt : r < t := Finset.mem_range.mp hr
        exact ⟨⟨r, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr_lt⟩, rfl⟩
    rw [Finset.card_image_of_injective _ π.injective, h_eq_card, Finset.card_range]
  have h_swap_image : ∀ {n : ℕ} (S : Finset (Fin n)) (g₁ : Fin n), g₁ ∈ S →
      ∀ g₂ ∈ S, S.image (Equiv.swap g₁ g₂) = S := by
    intro n S g₁ hg₁ g₂ hg₂
    have hsub : S.image (Equiv.swap g₁ g₂) ⊆ S := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨x, hxS, rfl⟩
      by_cases hx1 : x = g₁
      · subst hx1; simpa using hg₂
      · by_cases hx2 : x = g₂
        · subst hx2; simpa using hg₁
        · rw [Equiv.swap_apply_of_ne_of_ne hx1 hx2]; exact hxS
    exact Finset.eq_of_subset_of_card_le hsub
      (by rw [Finset.card_image_of_injective _ (Equiv.swap g₁ g₂).injective])
  have h_adm_list_props : ∀ {n : ℕ} (d : DetAdmissionModule n) (u : ItemValuation n)
      (P : Finset (Fin n) → Finset (Fin n)) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
      (runDetAdmissionSteps d u P π k hk).1.length = k ∧
      (runDetAdmissionSteps d u P π k hk).1.toFinset = arrivalPrefixSet π k ∧
      (runDetAdmissionSteps d u P π k hk).2 ⊆ arrivalPrefixSet π k := by
    intro n d u P π k
    induction k with
    | zero =>
      intro hk
      simp [runDetAdmissionSteps, arrivalPrefixSet]
    | succ k ih =>
      intro hk
      obtain ⟨hlen, hfin, hsub⟩ := ih (Nat.le_of_succ_le hk)
      dsimp [runDetAdmissionSteps]
      refine ⟨by rw [List.length_append, hlen]; simp, ?_, ?_⟩
      · rw [List.toFinset_append, hfin, ← h_pref_step π k hk]
        ext y; simp [or_comm]
      · rw [← h_pref_step π k hk]
        split_ifs
        · exact Finset.insert_subset_insert (π ⟨k, hk⟩) hsub
        · exact hsub.trans (Finset.subset_insert _ _)
  
  
  
  have h_s5 : ∀ {n m s : ℕ} (mod : Fin m → OnlineAdmissionModule n),
      1 ≤ s → s < n →
      ∃ alg : OnlineWelfareAlg n m,
        ∀ v : Fin m → ItemValuation n,
          (∀ i : Fin m, IsGSValuation (v i)) →
          (∀ i : Fin m, HasConditionalAdmission s (v i) (fun S => gsPrefixOptAlloc v S i) (mod i)) →
            (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
              IsAllocOf (runDetWelfareSteps (alg.det ω) v π k hk).1.toFinset
                (runDetWelfareSteps (alg.det ω) v π k hk).2) ∧
            (((secretaryCutoffConst n s * optWelfare v : ℝ) : WithBot ℝ) ≤
              expectedWelfareVal alg v) := by
    intro n m s mod hs1 hsn
    let detAlg : (∀ i : Fin m, (mod i).Seed) → DetWelfareAlg n m := fun ω =>
      { step := fun prev x bundles oracle =>
          let U : Finset (Fin n) := insert x prev.toFinset
          let v_loc : Fin m → ItemValuation n :=
            fun j R => if hR : R ⊆ U then oracle j ⟨R, hR⟩ else ⊥
          let winners : Finset (Fin m) := (Finset.univ : Finset (Fin m)).filter
            (fun i => ((mod i).det (ω i)).step prev x (bundles i) (oracle i)
              (fun ⟨T, _⟩ => gsPrefixOptAlloc v_loc T i) = true)
          if hw : winners.Nonempty then some (winners.min' hw) else none }
    let alg : OnlineWelfareAlg n m :=
      { Seed := ∀ i : Fin m, (mod i).Seed
        seedMeasure := MeasureTheory.Measure.pi (fun i => (mod i).seedMeasure)
        isProb := inferInstance
        det := detAlg
        meas_step := fun prev x bundles oracle dec => by
          let U : Finset (Fin n) := insert x prev.toFinset
          let v_loc : Fin m → ItemValuation n :=
            fun j R => if hR : R ⊆ U then oracle j ⟨R, hR⟩ else ⊥
          let propO : ∀ i : Fin m, {T : Finset (Fin n) // T ⊆ U} → Finset (Fin n) :=
            fun i ⟨T, _⟩ => gsPrefixOptAlloc v_loc T i
          let E : Fin m → Bool → Set (∀ i : Fin m, (mod i).Seed) :=
            fun i b => (fun ω => ω i) ⁻¹'
              {η : (mod i).Seed | ((mod i).det η).step prev x (bundles i) (oracle i) (propO i) = b}
          have hE_meas : ∀ (i : Fin m) (b : Bool), MeasurableSet (E i b) :=
            fun i b => ((mod i).meas_step prev x (bundles i) (oracle i) (propO i) b).preimage
              (measurable_pi_apply i)
          cases dec with
          | none =>
            have h_eq : {ω : ∀ i : Fin m, (mod i).Seed | (detAlg ω).step prev x bundles oracle = none} =
                ⋂ i ∈ (Finset.univ : Finset (Fin m)), E i false := by
              ext ω
              simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_univ, forall_true_left, E,
                Set.mem_preimage, detAlg]
              let winners := (Finset.univ : Finset (Fin m)).filter
                (fun i => ((mod i).det (ω i)).step prev x (bundles i) (oracle i) (propO i) = true)
              change (if hw : winners.Nonempty then some (winners.min' hw) else none) = none ↔ _
              constructor
              · intro hnone i
                by_cases hw : winners.Nonempty
                · rw [dif_pos hw] at hnone; cases hnone
                · have hnot : i ∉ winners := fun hi => hw ⟨i, hi⟩
                  have hne_true : ¬ (((mod i).det (ω i)).step prev x (bundles i) (oracle i) (propO i) = true) := by
                    simpa [winners] using hnot
                  exact Bool.eq_false_iff.mpr hne_true
              · intro hall
                have hnot_ne : ¬ winners.Nonempty := by
                  rintro ⟨i, hi⟩
                  have htrue := (Finset.mem_filter.mp hi).2
                  rw [hall i] at htrue; cases htrue
                rw [dif_neg hnot_ne]
            rw [h_eq]
            exact Finset.measurableSet_biInter Finset.univ (fun i _ => hE_meas i false)
          | some i0 =>
            let ltSet := (Finset.univ : Finset (Fin m)).filter (fun j => j < i0)
            have h_eq : {ω : ∀ i : Fin m, (mod i).Seed | (detAlg ω).step prev x bundles oracle = some i0} =
                E i0 true ∩ (⋂ j ∈ ltSet, E j false) := by
              ext ω
              simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_filter,
                Finset.mem_univ, true_and, E, Set.mem_preimage, detAlg, ltSet]
              let winners := (Finset.univ : Finset (Fin m)).filter
                (fun i => ((mod i).det (ω i)).step prev x (bundles i) (oracle i) (propO i) = true)
              change (if hw : winners.Nonempty then some (winners.min' hw) else none) = some i0 ↔ _
              constructor
              · intro hsome
                by_cases hw : winners.Nonempty
                · rw [dif_pos hw] at hsome
                  have hmin : winners.min' hw = i0 := Option.some.inj hsome
                  have hi0_mem : i0 ∈ winners := hmin ▸ Finset.min'_mem winners hw
                  refine ⟨(Finset.mem_filter.mp hi0_mem).2, fun j hjlt => ?_⟩
                  cases hj_step : ((mod j).det (ω j)).step prev x (bundles j) (oracle j) (propO j)
                  · rfl
                  · exfalso
                    have hj_mem : j ∈ winners := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj_step⟩
                    have hle : i0 ≤ j := hmin ▸ Finset.min'_le winners j hj_mem
                    exact not_lt_of_ge hle hjlt
                · rw [dif_neg hw] at hsome; cases hsome
              · rintro ⟨hi0_true, hj_false⟩
                have hi0_mem : i0 ∈ winners := Finset.mem_filter.mpr ⟨Finset.mem_univ i0, hi0_true⟩
                have hw : winners.Nonempty := ⟨i0, hi0_mem⟩
                rw [dif_pos hw]
                congr 1
                refine le_antisymm (Finset.min'_le winners i0 hi0_mem) ?_
                by_contra hlt
                have hlt' : winners.min' hw < i0 := lt_of_not_ge hlt
                have hmem := Finset.min'_mem winners hw
                have htrue := (Finset.mem_filter.mp hmem).2
                rw [hj_false (winners.min' hw) hlt'] at htrue
                cases htrue
            rw [h_eq]
            exact (hE_meas i0 true).inter
              (Finset.measurableSet_biInter ltSet (fun j _ => hE_meas j false)) }
    refine ⟨alg, fun v hv hmod => ?_⟩
    have hv0 : ∀ i : Fin m, v i ∅ = ((0 : ℝ) : WithBot ℝ) := fun i => (hv i).1
    obtain ⟨h_s3_1, h_s3_2, _⟩ := h_s3_main v hv0
    let P_i : Fin m → Finset (Fin n) → Finset (Fin n) := fun i S => gsPrefixOptAlloc v S i
    
    have h_welf_alloc : ∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
        (runDetWelfareSteps (alg.det ω) v π k hk).1.toFinset = arrivalPrefixSet π k ∧
        IsAllocOf (runDetWelfareSteps (alg.det ω) v π k hk).1.toFinset
          (runDetWelfareSteps (alg.det ω) v π k hk).2 := by
      intro ω π k
      induction k with
      | zero =>
        intro hk
        refine ⟨by simp [runDetWelfareSteps, arrivalPrefixSet], ?_⟩
        exact ⟨fun _ => Finset.empty_subset _, fun _ _ _ => Finset.disjoint_empty_left ∅⟩
      | succ k ih =>
        intro hk
        obtain ⟨hfin, hsub, hdisj⟩ := ih (Nat.le_of_succ_le hk)
        let st := runDetWelfareSteps (alg.det ω) v π k (Nat.le_of_succ_le hk)
        let x := π ⟨k, hk⟩
        have hfin_next : (runDetWelfareSteps (alg.det ω) v π (k + 1) hk).1.toFinset =
            arrivalPrefixSet π (k + 1) := by
          dsimp [runDetWelfareSteps]
          rw [List.toFinset_append, hfin, ← h_pref_step π k hk]
          ext y; simp [or_comm]
        refine ⟨hfin_next, ?_⟩
        rw [hfin_next, ← h_pref_step π k hk]
        have hx_not_pref : x ∉ st.1.toFinset := by
          rw [hfin]; exact h_pref_notMem π k hk
        have hx_not_bundle : ∀ j : Fin m, x ∉ st.2 j :=
          fun j hmem => hx_not_pref (hsub j hmem)
        change IsAllocOf (insert x (arrivalPrefixSet π k))
          (match (alg.det ω).step st.1 x st.2 (fun i ⟨T, _⟩ => v i T) with
           | none => st.2
           | some i => Function.update st.2 i (insert x (st.2 i)))
        cases (alg.det ω).step st.1 x st.2 (fun i ⟨T, _⟩ => v i T) with
        | none =>
          exact ⟨fun j => (hsub j).trans (by rw [hfin]; exact Finset.subset_insert _ _), hdisj⟩
        | some i0 =>
          dsimp only
          refine ⟨fun j => ?_, fun j1 j2 hne => ?_⟩
          · by_cases hj : j = i0
            · subst hj
              rw [Function.update_self, ← hfin]
              exact Finset.insert_subset_insert x (hsub j)
            · rw [Function.update_of_ne hj, ← hfin]
              exact (hsub j).trans (Finset.subset_insert _ _)
          · by_cases hj1 : j1 = i0
            · subst hj1
              have hj2 : j2 ≠ j1 := hne.symm
              rw [Function.update_self, Function.update_of_ne hj2]
              exact Finset.disjoint_insert_left.mpr ⟨hx_not_bundle j2, hdisj j1 j2 hne⟩
            · rw [Function.update_of_ne hj1]
              by_cases hj2 : j2 = i0
              · subst hj2
                rw [Function.update_self]
                exact Finset.disjoint_insert_right.mpr ⟨hx_not_bundle j1, hdisj j1 j2 hne⟩
              · rw [Function.update_of_ne hj2]
                exact hdisj j1 j2 hne
    
    have h_adm_prev_eq : ∀ (d₁ d₂ : DetAdmissionModule n) (u₁ u₂ : ItemValuation n)
        (Q₁ Q₂ : Finset (Fin n) → Finset (Fin n)) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
        (runDetAdmissionSteps d₁ u₁ Q₁ π k hk).1 = (runDetAdmissionSteps d₂ u₂ Q₂ π k hk).1 := by
      intro d₁ d₂ u₁ u₂ Q₁ Q₂ π k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        dsimp [runDetAdmissionSteps]
        rw [ih (Nat.le_of_succ_le hk)]
    have h_coupling : ∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
        (∀ i : Fin m, (runDetWelfareSteps (alg.det ω) v π k hk).1 =
          (runDetAdmissionSteps ((mod i).det (ω i)) (v i) (P_i i) π k hk).1) ∧
        (∀ i : Fin m, (runDetWelfareSteps (alg.det ω) v π k hk).2 i =
          (runDetAdmissionSteps ((mod i).det (ω i)) (v i) (P_i i) π k hk).2) := by
      intro ω π k
      induction k with
      | zero =>
        intro hk
        exact ⟨fun _ => rfl, fun _ => rfl⟩
      | succ k ih =>
        intro hk
        have hk' := Nat.le_of_succ_le hk
        obtain ⟨ih_prev, ih_acc⟩ := ih hk'
        let st := runDetWelfareSteps (alg.det ω) v π k hk'
        let x := π ⟨k, hk⟩
        let U : Finset (Fin n) := insert x st.1.toFinset
        let v_loc : Fin m → ItemValuation n :=
          fun j R => if hR : R ⊆ U then v j R else ⊥
        have h_prop_eq : ∀ i : Fin m,
            (fun (T : {T : Finset (Fin n) // T ⊆ U}) => gsPrefixOptAlloc v_loc T.1 i) =
              (fun (T : {T : Finset (Fin n) // T ⊆ U}) => P_i i T.1) := by
          intro i
          funext ⟨T, hTU⟩
          have h_eq_alloc : gsPrefixOptAlloc v_loc T = gsPrefixOptAlloc v T :=
            (h_s3_1 T).2.2 v_loc (fun j R hRT => dif_pos (hRT.trans hTU))
          exact congrFun h_eq_alloc i
        let dec_i : Fin m → Bool := fun i =>
          let st_i := runDetAdmissionSteps ((mod i).det (ω i)) (v i) (P_i i) π k hk'
          ((mod i).det (ω i)).step st_i.1 x st_i.2 (fun ⟨T, _⟩ => v i T) (fun ⟨T, _⟩ => P_i i T)
        have h_step_i_eq : ∀ i : Fin m,
            ((mod i).det (ω i)).step st.1 x (st.2 i) (fun ⟨T, _⟩ => v i T)
              (fun ⟨T, _⟩ => gsPrefixOptAlloc v_loc T i) = dec_i i := by
          intro i
          rw [h_prop_eq i]
          dsimp [dec_i]
          rw [← ih_prev i, ← ih_acc i]
        have h_at_most_one : ∀ i₁ i₂ : Fin m, dec_i i₁ = true → dec_i i₂ = true → i₁ = i₂ := by
          intro i₁ i₂ h₁ h₂
          by_contra hne
          have hx_in : ∀ j : Fin m, dec_i j = true → x ∈ gsPrefixOptAlloc v U j := by
            intro j hj
            by_contra hx_not
            have hx_not' : x ∉ P_i j (insert x (runDetAdmissionSteps ((mod j).det (ω j)) (v j) (P_i j) π k hk').1.toFinset) := by
              rw [← ih_prev j]; exact hx_not
            have hfalse := (hmod j).1 (ω j) π k hk (Or.inr hx_not')
            change dec_i j = false at hfalse
            rw [hj] at hfalse; cases hfalse
          have hx₁ := hx_in i₁ h₁
          have hx₂ := hx_in i₂ h₂
          have hdisj := (h_s3_1 U).1.2 i₁ i₂ hne
          exact Finset.disjoint_left.mp hdisj hx₁ hx₂
        refine ⟨fun i => ?_, fun i => ?_⟩
        · dsimp [runDetWelfareSteps, runDetAdmissionSteps]
          rw [ih_prev i]
        · let winners := (Finset.univ : Finset (Fin m)).filter (fun j =>
            ((mod j).det (ω j)).step st.1 x (st.2 j) (fun ⟨T, _⟩ => v j T)
              (fun ⟨T, _⟩ => gsPrefixOptAlloc v_loc T j) = true)
          have h_win_eq : winners = (Finset.univ : Finset (Fin m)).filter (fun j => dec_i j = true) := by
            ext j; simp [winners, h_step_i_eq j]
          change (match (if hw : winners.Nonempty then some (winners.min' hw) else none) with
            | none => st.2
            | some j => Function.update st.2 j (insert x (st.2 j))) i =
            (if dec_i i then insert x (runDetAdmissionSteps ((mod i).det (ω i)) (v i) (P_i i) π k hk').2
             else (runDetAdmissionSteps ((mod i).det (ω i)) (v i) (P_i i) π k hk').2)
          by_cases hw : winners.Nonempty
          · rw [dif_pos hw]
            let i0 := winners.min' hw
            have hi0_mem : i0 ∈ winners := Finset.min'_mem winners hw
            have hi0_true : dec_i i0 = true := by
              rw [h_win_eq] at hi0_mem; exact (Finset.mem_filter.mp hi0_mem).2
            by_cases hi : i = i0
            · subst hi
              change Function.update st.2 i0 (insert x (st.2 i0)) i0 = _
              rw [Function.update_self, if_pos hi0_true, ih_acc i0]
            · change Function.update st.2 i0 (insert x (st.2 i0)) i = _
              rw [Function.update_of_ne hi]
              have hi_false : dec_i i = false := by
                cases h : dec_i i
                · rfl
                · exfalso; exact hi (h_at_most_one i i0 h hi0_true)
              rw [if_neg (by rw [hi_false]; decide), ih_acc i]
          · rw [dif_neg hw]
            have hi_false : dec_i i = false := by
              cases h : dec_i i
              · rfl
              · exfalso
                have hmem : i ∈ winners := by
                  rw [h_win_eq]
                  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩
                exact hw ⟨i, hmem⟩
            change st.2 i = _
            rw [if_neg (by rw [hi_false]; decide), ih_acc i]
    have h_coupling_final : ∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)),
        runDetWelfare (alg.det ω) v π =
          fun i => runDetAdmission ((mod i).det (ω i)) (v i) (P_i i) π := by
      intro ω π
      funext i
      exact (h_coupling ω π n (le_refl n)).2 i
    
    have h_meas_adm_steps : ∀ (i : Fin m) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n)
        (A : Finset (Fin n)),
        MeasurableSet {η : (mod i).Seed |
          (runDetAdmissionSteps ((mod i).det η) (v i) (P_i i) π k hk).2 = A} := by
      intro i π k
      induction k with
      | zero =>
        intro hk A
        by_cases hA : (∅ : Finset (Fin n)) = A
        · have : {η : (mod i).Seed |
            (runDetAdmissionSteps ((mod i).det η) (v i) (P_i i) π 0 hk).2 = A} = Set.univ := by
            ext _; simp [runDetAdmissionSteps, hA]
          rw [this]; exact MeasurableSet.univ
        · have : {η : (mod i).Seed |
            (runDetAdmissionSteps ((mod i).det η) (v i) (P_i i) π 0 hk).2 = A} = ∅ := by
            ext _; simp [runDetAdmissionSteps, hA]
          rw [this]; exact MeasurableSet.empty
      | succ k ih =>
        intro hk A
        have hk' := Nat.le_of_succ_le hk
        let d0 : DetAdmissionModule n := { step := fun _ _ _ _ _ => false }
        let prev_k := (runDetAdmissionSteps d0 (v i) (P_i i) π k hk').1
        let x := π ⟨k, hk⟩
        let valO : {T : Finset (Fin n) // T ⊆ insert x prev_k.toFinset} → WithBot ℝ :=
          fun ⟨T, _⟩ => v i T
        let propO : {T : Finset (Fin n) // T ⊆ insert x prev_k.toFinset} → Finset (Fin n) :=
          fun ⟨T, _⟩ => P_i i T
        have h_prev_const : ∀ η : (mod i).Seed,
            (runDetAdmissionSteps ((mod i).det η) (v i) (P_i i) π k hk').1 = prev_k :=
          fun η => h_adm_prev_eq ((mod i).det η) d0 (v i) (v i) (P_i i) (P_i i) π k hk'
        let G : Finset (Fin n) → Set (mod i).Seed := fun B =>
          {η | (runDetAdmissionSteps ((mod i).det η) (v i) (P_i i) π k hk').2 = B} ∩
          (({η | ((mod i).det η).step prev_k x B valO propO = true} ∩ {η | insert x B = A}) ∪
           ({η | ((mod i).det η).step prev_k x B valO propO = false} ∩ {η | B = A}))
        have h_eq : {η : (mod i).Seed |
            (runDetAdmissionSteps ((mod i).det η) (v i) (P_i i) π (k + 1) hk).2 = A} =
            ⋃ B ∈ (Finset.univ : Finset (Finset (Fin n))), G B := by
          ext η
          simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_univ, exists_true_left, G,
            Set.mem_inter_iff, Set.mem_union]
          let st := runDetAdmissionSteps ((mod i).det η) (v i) (P_i i) π k hk'
          let stepWith (L : List (Fin n)) : Bool :=
            ((mod i).det η).step L x st.2 (fun ⟨T, _⟩ => v i T) (fun ⟨T, _⟩ => P_i i T)
          have h_step_prev : stepWith st.1 = stepWith prev_k :=
            congrArg stepWith (h_prev_const η)
          change (if stepWith st.1 then insert x st.2 else st.2) = A ↔ _
          rw [h_step_prev]
          dsimp only [stepWith]
          constructor
          · intro hA
            refine ⟨st.2, rfl, ?_⟩
            cases hdec : ((mod i).det η).step prev_k x st.2 valO propO
            · rw [hdec] at hA; exact Or.inr ⟨rfl, hA⟩
            · rw [hdec] at hA; exact Or.inl ⟨rfl, hA⟩
          · rintro ⟨B, rfl, (⟨ht, hins⟩ | ⟨hf, heq⟩)⟩
            · rw [ht, if_pos rfl]; exact hins
            · rw [hf]; simpa using heq
        rw [h_eq]
        refine Finset.measurableSet_biUnion Finset.univ (fun B _ => ?_)
        have hm_const : ∀ Q : Prop, MeasurableSet {η : (mod i).Seed | Q} := by
          intro Q
          by_cases hQ : Q
          · convert MeasurableSet.univ; ext _; simp [hQ]
          · convert MeasurableSet.empty; ext _; simp [hQ]
        exact (ih hk' B).inter
          ((((mod i).meas_step prev_k x B valO propO true).inter (hm_const _)).union
           (((mod i).meas_step prev_k x B valO propO false).inter (hm_const _)))
    have h_meas_welf : ∀ (π : Equiv.Perm (Fin n)) (X : Fin m → Finset (Fin n)),
        MeasurableSet {ω : alg.Seed | runDetWelfare (alg.det ω) v π = X} := by
      intro π X
      have h_eq : {ω : alg.Seed | runDetWelfare (alg.det ω) v π = X} =
          ⋂ i ∈ (Finset.univ : Finset (Fin m)),
            (fun ω : alg.Seed => ω i) ⁻¹'
              {η : (mod i).Seed | runDetAdmission ((mod i).det η) (v i) (P_i i) π = X i} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_univ, forall_true_left,
          Set.mem_preimage, h_coupling_final ω π, funext_iff]
      rw [h_eq]
      exact Finset.measurableSet_biInter Finset.univ (fun i _ =>
        (h_meas_adm_steps i π n (le_refl n) (X i)).preimage (measurable_pi_apply i))
    
    have h_marginal_π : ∀ (i : Fin m) (π : Equiv.Perm (Fin n)) (A : Finset (Fin n)),
        (mod i).seedMeasure.real {η | runDetAdmission ((mod i).det η) (v i) (P_i i) π = A} =
          ∑ X ∈ (Finset.univ : Finset (Fin m → Finset (Fin n))).filter (fun X => X i = A),
            alg.seedMeasure.real {ω | runDetWelfare (alg.det ω) v π = X} := by
      intro i π A
      let S_i : Set (mod i).Seed := {η | runDetAdmission ((mod i).det η) (v i) (P_i i) π = A}
      have hS_i_meas : MeasurableSet S_i := h_meas_adm_steps i π n (le_refl n) A
      have hmp := MeasureTheory.measurePreserving_eval (fun j => (mod j).seedMeasure) i
      have h_pre_real : alg.seedMeasure.real ((fun ω : alg.Seed => ω i) ⁻¹' S_i) =
          (mod i).seedMeasure.real S_i :=
        congrArg ENNReal.toReal (hmp.measure_preimage hS_i_meas.nullMeasurableSet)
      let fib := (Finset.univ : Finset (Fin m → Finset (Fin n))).filter (fun X => X i = A)
      let F_X : (Fin m → Finset (Fin n)) → Set alg.Seed :=
        fun X => {ω | runDetWelfare (alg.det ω) v π = X}
      have h_union : ((fun ω : alg.Seed => ω i) ⁻¹' S_i) = ⋃ X ∈ fib, F_X X := by
        ext ω
        simp only [Set.mem_preimage, S_i, Set.mem_setOf_eq, Set.mem_iUnion, fib,
          Finset.mem_filter, Finset.mem_univ, true_and, F_X]
        constructor
        · intro hA
          refine ⟨runDetWelfare (alg.det ω) v π, ?_, rfl⟩
          rw [h_coupling_final ω π]; exact hA
        · rintro ⟨X, rfl, hX⟩
          rw [← hX, h_coupling_final ω π]
      have h_disj : (fib : Set (Fin m → Finset (Fin n))).PairwiseDisjoint F_X := by
        intro X₁ _ X₂ _ hne
        change Disjoint (F_X X₁) (F_X X₂)
        rw [Set.disjoint_left]
        intro ω h₁ h₂
        exact hne (h₁.symm.trans h₂)
      rw [← h_pre_real, h_union]
      exact measureReal_biUnion_finset h_disj (fun X _ => h_meas_welf π X)
    have h_marginal_prob : ∀ (i : Fin m) (A : Finset (Fin n)),
        algAdmissionProb (mod i) (v i) (P_i i) A =
          ∑ X ∈ (Finset.univ : Finset (Fin m → Finset (Fin n))).filter (fun X => X i = A),
            algWelfareProb alg v X := by
      intro i A
      unfold algAdmissionProb algWelfareProb
      rw [Finset.sum_congr rfl (fun π _ => h_marginal_π i π A), Finset.sum_comm, Finset.mul_sum]
    have h_welf_prob_nn : ∀ X : Fin m → Finset (Fin n), 0 ≤ algWelfareProb alg v X := by
      intro X
      unfold algWelfareProb
      refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun π _ => measureReal_nonneg))
    have h_pos_bundle_ne_bot : ∀ (X : Fin m → Finset (Fin n)),
        0 < algWelfareProb alg v X → ∀ i : Fin m, v i (X i) ≠ ⊥ := by
      intro X hpos i
      obtain ⟨_, _, _, _, h_safe_i, _⟩ := hmod i
      refine h_safe_i (X i) ?_
      rw [h_marginal_prob i (X i)]
      have hX_mem : X ∈ (Finset.univ : Finset (Fin m → Finset (Fin n))).filter (fun Y => Y i = X i) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ X, rfl⟩
      exact lt_of_lt_of_le hpos
        (Finset.single_le_sum (fun Y _ => h_welf_prob_nn Y) hX_mem)
    have h_no_welf_bot : ¬ ∃ X : Fin m → Finset (Fin n),
        0 < algWelfareProb alg v X ∧ allocWelfare v X = ⊥ := by
      rintro ⟨X, hpos, hbot⟩
      have h_all_ne := h_pos_bundle_ne_bot X hpos
      have h_coe : allocWelfare v X = ((∑ i : Fin m, realVal (v i) (X i) : ℝ) : WithBot ℝ) := by
        rw [WithBot.coe_sum]; unfold allocWelfare
        exact Finset.sum_congr rfl (fun i _ => (coe_realVal (v i) (X i) (h_all_ne i)).symm)
      rw [h_coe] at hbot
      exact WithBot.coe_ne_bot hbot
    have h_exp_welf_decomp : expectedWelfareVal alg v =
        ((∑ i : Fin m, ∑ A : Finset (Fin n),
          algAdmissionProb (mod i) (v i) (P_i i) A * realVal (v i) A : ℝ) : WithBot ℝ) := by
      unfold expectedWelfareVal
      rw [if_neg h_no_welf_bot]
      congr 1
      have h_term : ∀ X : Fin m → Finset (Fin n),
          algWelfareProb alg v X * (allocWelfare v X).unbotD 0 =
            ∑ i : Fin m, algWelfareProb alg v X * realVal (v i) (X i) := by
        intro X
        rcases eq_or_lt_of_le (h_welf_prob_nn X) with hzero | hpos
        · rw [← hzero]; simp
        · have h_all_ne := h_pos_bundle_ne_bot X hpos
          have h_coe : allocWelfare v X = ((∑ i : Fin m, realVal (v i) (X i) : ℝ) : WithBot ℝ) := by
            rw [WithBot.coe_sum]; unfold allocWelfare
            exact Finset.sum_congr rfl (fun i _ => (coe_realVal (v i) (X i) (h_all_ne i)).symm)
          rw [h_coe, WithBot.unbotD_coe, Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun X _ => h_term X), Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      calc
        ∑ X : Fin m → Finset (Fin n), algWelfareProb alg v X * realVal (v i) (X i)
          = ∑ X : Fin m → Finset (Fin n), ∑ A : Finset (Fin n),
              (if X i = A then algWelfareProb alg v X * realVal (v i) A else 0) := by
            refine Finset.sum_congr rfl (fun X _ => ?_)
            simp
        _ = ∑ A : Finset (Fin n), ∑ X : Fin m → Finset (Fin n),
              (if X i = A then algWelfareProb alg v X * realVal (v i) A else 0) := Finset.sum_comm
        _ = ∑ A : Finset (Fin n),
              ∑ X ∈ (Finset.univ : Finset (Fin m → Finset (Fin n))).filter (fun X => X i = A),
                algWelfareProb alg v X * realVal (v i) A := by
            refine Finset.sum_congr rfl (fun A _ => ?_)
            rw [Finset.sum_filter]
        _ = ∑ A : Finset (Fin n), algAdmissionProb (mod i) (v i) (P_i i) A * realVal (v i) A := by
            refine Finset.sum_congr rfl (fun A _ => ?_)
            rw [← Finset.sum_mul, ← h_marginal_prob i A]
    
    have h_ev_card : ∀ (k : ℕ) (hk : k + 1 ≤ n) (S : Finset (Fin n)) (g : Fin n),
        S.card = k + 1 → g ∈ S →
          let ev := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
            (fun π => arrivalPrefixSet π (k + 1) = S ∧ π ⟨k, hk⟩ = g)
          let evS := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
            (fun π => arrivalPrefixSet π (k + 1) = S)
          (k + 1) * ev.card = evS.card := by
      intro k hk S g hScard hgS ev evS
      let evOf : Fin n → Finset (Equiv.Perm (Fin n)) := fun g' =>
        (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun π => arrivalPrefixSet π (k + 1) = S ∧ π ⟨k, hk⟩ = g')
      have h_card_eq : ∀ g' ∈ S, (evOf g').card = ev.card := by
        intro g' hg'
        refine Finset.card_bij (fun π _ => Equiv.swap g' g * π) ?_ ?_ ?_
        · intro π hπ
          obtain ⟨hπS, hπg'⟩ := (Finset.mem_filter.mp hπ).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
          · have h_img : arrivalPrefixSet (Equiv.swap g' g * π) (k + 1) =
                (arrivalPrefixSet π (k + 1)).image (Equiv.swap g' g) := by
              unfold arrivalPrefixSet; rw [Finset.image_image]; rfl
            rw [h_img, hπS, h_swap_image S g' hg' g hgS]
          · change Equiv.swap g' g (π ⟨k, hk⟩) = g
            rw [hπg', Equiv.swap_apply_left]
        · intro π₁ _ π₂ _ heq
          exact mul_left_cancel heq
        · intro π hπ
          obtain ⟨hπS, hπg⟩ := (Finset.mem_filter.mp hπ).2
          refine ⟨Equiv.swap g' g * π, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
          · have h_img : arrivalPrefixSet (Equiv.swap g' g * π) (k + 1) =
                (arrivalPrefixSet π (k + 1)).image (Equiv.swap g' g) := by
              unfold arrivalPrefixSet; rw [Finset.image_image]; rfl
            rw [h_img, hπS, h_swap_image S g' hg' g hgS]
          · change Equiv.swap g' g (π ⟨k, hk⟩) = g'
            rw [hπg, Equiv.swap_apply_right]
          · dsimp only; ext x; simp
      have h_maps : Set.MapsTo (fun π : Equiv.Perm (Fin n) => π ⟨k, hk⟩) (↑evS) (↑S) := by
        intro π hπ
        have hπS : arrivalPrefixSet π (k + 1) = S := (Finset.mem_filter.mp hπ).2
        rw [Finset.mem_coe, ← hπS]
        exact Finset.mem_image.mpr ⟨⟨k, hk⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.lt_succ_self k⟩, rfl⟩
      rw [Finset.card_eq_sum_card_fiberwise h_maps]
      have h_filter_eq : ∀ g' ∈ S, evS.filter (fun π => π ⟨k, hk⟩ = g') = evOf g' := by
        intro g' _; ext π; simp [evS, evOf]
      exact (calc
        ∑ g' ∈ S, (evS.filter (fun π => π ⟨k, hk⟩ = g')).card
          = ∑ g' ∈ S, (evOf g').card :=
            Finset.sum_congr rfl (fun g' hg' => congrArg Finset.card (h_filter_eq g' hg'))
        _ = ∑ _ ∈ S, ev.card := Finset.sum_congr rfl h_card_eq
        _ = (k + 1) * ev.card := by rw [Finset.sum_const, smul_eq_mul, hScard]).symm
    let c_fn : Fin m → Finset (Fin n) → Fin n → ℝ :=
      fun i => Classical.choose (hmod i).2.2
    have hc_spec : ∀ i : Fin m,
        (∀ S : Finset (Fin n),
          (∀ g ∈ P_i i S, 0 ≤ c_fn i S g) ∧ (∑ g ∈ P_i i S, c_fn i S g) = realVal (v i) (P_i i S)) ∧
        (∀ S : Finset (Fin n), 0 < algAdmissionProb (mod i) (v i) (P_i i) S → v i S ≠ ⊥) ∧
        (((1 / (Nat.factorial n : ℝ)) *
          ∑ π : Equiv.Perm (Fin n), ∑ idx : Fin n,
            if s ≤ idx.1 then
              c_fn i (arrivalPrefixSet π (idx.1 + 1)) (π idx) *
                (mod i).seedMeasure.real {η | π idx ∈
                  (runDetAdmissionSteps ((mod i).det η) (v i) (P_i i) π (idx.1 + 1) idx.2).2}
            else 0 : ℝ) : WithBot ℝ) ≤ expectedAdmissionVal (mod i) (v i) (P_i i) :=
      fun i => Classical.choose_spec (hmod i).2.2
    let termAt : Fin m → ℕ → ℝ := fun i k =>
      if hk : k + 1 ≤ n then
        ∑ π : Equiv.Perm (Fin n),
          c_fn i (arrivalPrefixSet π (k + 1)) (π ⟨k, hk⟩) *
            (mod i).seedMeasure.real {η | π ⟨k, hk⟩ ∈
              (runDetAdmissionSteps ((mod i).det η) (v i) (P_i i) π (k + 1) hk).2}
      else 0
    have h_adm_val_lb : ∀ i : Fin m,
        (1 / (Nat.factorial n : ℝ)) * ∑ k ∈ Finset.Ico s n, termAt i k ≤
          ∑ A : Finset (Fin n), algAdmissionProb (mod i) (v i) (P_i i) A * realVal (v i) A := by
      intro i
      obtain ⟨_, h_safe_i, h_cred_le⟩ := hc_spec i
      have h_no_bot_i : ¬ ∃ A : Finset (Fin n),
          0 < algAdmissionProb (mod i) (v i) (P_i i) A ∧ v i A = ⊥ := by
        rintro ⟨A, hpos, hbot⟩
        exact h_safe_i A hpos hbot
      unfold expectedAdmissionVal at h_cred_le
      rw [if_neg h_no_bot_i, WithBot.coe_le_coe] at h_cred_le
      have h_idx_eq : (∑ π : Equiv.Perm (Fin n), ∑ idx : Fin n,
            if s ≤ idx.1 then
              c_fn i (arrivalPrefixSet π (idx.1 + 1)) (π idx) *
                (mod i).seedMeasure.real {η | π idx ∈
                  (runDetAdmissionSteps ((mod i).det η) (v i) (P_i i) π (idx.1 + 1) idx.2).2}
            else 0) = ∑ k ∈ Finset.Ico s n, termAt i k := by
        rw [Finset.sum_comm]
        have h_each_idx : ∀ idx : Fin n,
            (∑ π : Equiv.Perm (Fin n),
              if s ≤ idx.1 then
                c_fn i (arrivalPrefixSet π (idx.1 + 1)) (π idx) *
                  (mod i).seedMeasure.real {η | π idx ∈
                    (runDetAdmissionSteps ((mod i).det η) (v i) (P_i i) π (idx.1 + 1) idx.2).2}
              else 0) = if s ≤ idx.1 then termAt i idx.1 else 0 := by
          intro idx
          by_cases hs_idx : s ≤ idx.1
          · dsimp only [termAt]
            rw [if_pos hs_idx, dif_pos (show idx.1 + 1 ≤ n from idx.2)]
            exact Finset.sum_congr rfl (fun π _ => by simp [hs_idx])
          · simp [hs_idx]
        rw [Finset.sum_congr rfl (fun idx _ => h_each_idx idx),
            Fin.sum_univ_eq_sum_range (fun k => if s ≤ k then termAt i k else 0) n,
            ← Finset.sum_filter]
        have h_filt : (Finset.range n).filter (fun k => s ≤ k) = Finset.Ico s n := by
          ext k; simp [Finset.mem_Ico, Finset.mem_range, and_comm]
        rw [h_filt]
      rw [← h_idx_eq]
      exact h_cred_le
    have h_step_k_lb : ∀ k ∈ Finset.Ico s n,
        (((s : ℝ) / (n : ℝ)) * (1 / (k : ℝ))) * ((Nat.factorial n : ℝ) * optWelfare v) ≤
          ∑ i : Fin m, termAt i k := by
      intro k hk_mem
      obtain ⟨hsk, hkn⟩ := Finset.mem_Ico.mp hk_mem
      have hk : k + 1 ≤ n := hkn
      let powK := (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card = k + 1)
      let evS : Finset (Fin n) → Finset (Equiv.Perm (Fin n)) :=
        fun S => (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun π => arrivalPrefixSet π (k + 1) = S)
      have h_term_i_lb : ∀ i : Fin m,
          (((s : ℝ) / (k : ℝ)) * (1 / ((k + 1 : ℕ) : ℝ))) *
              ∑ S ∈ powK, ((evS S).card : ℝ) * realVal (v i) (P_i i S) ≤
            termAt i k := by
        intro i
        dsimp [termAt]
        rw [dif_pos hk]
        have h_zero_out : ∀ π : Equiv.Perm (Fin n),
            π ⟨k, hk⟩ ∉ P_i i (arrivalPrefixSet π (k + 1)) →
              (mod i).seedMeasure.real {η | π ⟨k, hk⟩ ∈
                (runDetAdmissionSteps ((mod i).det η) (v i) (P_i i) π (k + 1) hk).2} = 0 := by
          intro π hnot
          have hemp : {η : (mod i).Seed | π ⟨k, hk⟩ ∈
              (runDetAdmissionSteps ((mod i).det η) (v i) (P_i i) π (k + 1) hk).2} = ∅ := by
            ext η
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
            intro hmem
            let st := runDetAdmissionSteps ((mod i).det η) (v i) (P_i i) π k (Nat.le_of_succ_le hk)
            obtain ⟨_, hfin_k, hsub_k⟩ :=
              h_adm_list_props ((mod i).det η) (v i) (P_i i) π k (Nat.le_of_succ_le hk)
            have hnot' : π ⟨k, hk⟩ ∉ P_i i (insert (π ⟨k, hk⟩) st.1.toFinset) := by
              rw [hfin_k, h_pref_step π k hk]; exact hnot
            have hdec_f := (hmod i).1 η π k hk (Or.inr hnot')
            dsimp [runDetAdmissionSteps] at hmem
            change π ⟨k, hk⟩ ∈
              (if ((mod i).det η).step st.1 (π ⟨k, hk⟩) st.2 (fun ⟨T, _⟩ => v i T) (fun ⟨T, _⟩ => P_i i T)
               then insert (π ⟨k, hk⟩) st.2 else st.2) at hmem
            rw [hdec_f] at hmem
            simp only [Bool.false_eq_true, ↓reduceIte] at hmem
            exact h_pref_notMem π k hk (hsub_k hmem)
          rw [hemp]
          exact MeasureTheory.measureReal_empty
        have h_decomp_π : ∀ π : Equiv.Perm (Fin n),
            c_fn i (arrivalPrefixSet π (k + 1)) (π ⟨k, hk⟩) *
              (mod i).seedMeasure.real {η | π ⟨k, hk⟩ ∈
                (runDetAdmissionSteps ((mod i).det η) (v i) (P_i i) π (k + 1) hk).2} =
            ∑ S ∈ powK, ∑ g ∈ P_i i S,
              if arrivalPrefixSet π (k + 1) = S ∧ π ⟨k, hk⟩ = g then
                c_fn i S g * (mod i).seedMeasure.real {η | g ∈
                  (runDetAdmissionSteps ((mod i).det η) (v i) (P_i i) π (k + 1) hk).2}
              else 0 := by
          intro π
          let S0 := arrivalPrefixSet π (k + 1)
          let g0 := π ⟨k, hk⟩
          have hS0_mem : S0 ∈ powK :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ S0, h_card_pref π (k + 1) hk⟩
          have h_S_sum : (∑ S ∈ powK, ∑ g ∈ P_i i S,
              if S0 = S ∧ g0 = g then
                c_fn i S g * (mod i).seedMeasure.real {η | g ∈
                  (runDetAdmissionSteps ((mod i).det η) (v i) (P_i i) π (k + 1) hk).2}
              else 0) =
              ∑ g ∈ P_i i S0,
                if g0 = g then
                  c_fn i S0 g * (mod i).seedMeasure.real {η | g ∈
                    (runDetAdmissionSteps ((mod i).det η) (v i) (P_i i) π (k + 1) hk).2}
                else 0 := by
            rw [Finset.sum_eq_single S0]
            · refine Finset.sum_congr rfl (fun g _ => ?_)
              simp
            · intro S _ hne
              refine Finset.sum_eq_zero (fun g _ => ?_)
              simp [hne.symm]
            · intro hnot; exfalso; exact hnot hS0_mem
          rw [h_S_sum]
          by_cases hg0 : g0 ∈ P_i i S0
          · rw [Finset.sum_eq_single g0]
            · simp only [↓reduceIte]; rfl
            · intro g _ hne; simp [hne.symm]
            · intro hnot; exfalso; exact hnot hg0
          · have h_rhs0 : (∑ g ∈ P_i i S0,
                if g0 = g then
                  c_fn i S0 g * (mod i).seedMeasure.real {η | g ∈
                    (runDetAdmissionSteps ((mod i).det η) (v i) (P_i i) π (k + 1) hk).2}
                else 0) = 0 := by
              refine Finset.sum_eq_zero (fun g hg => ?_)
              have hne : g0 ≠ g := fun heq => hg0 (heq ▸ hg)
              simp [hne]
            rw [h_rhs0, h_zero_out π hg0, mul_zero]
        rw [Finset.sum_congr rfl (fun π _ => h_decomp_π π), Finset.sum_comm]
        have h_swap_inner : ∑ S ∈ powK, ∑ π : Equiv.Perm (Fin n), ∑ g ∈ P_i i S,
              (if arrivalPrefixSet π (k + 1) = S ∧ π ⟨k, hk⟩ = g then
                c_fn i S g * (mod i).seedMeasure.real {η | g ∈
                  (runDetAdmissionSteps ((mod i).det η) (v i) (P_i i) π (k + 1) hk).2}
               else 0) =
            ∑ S ∈ powK, ∑ g ∈ P_i i S, c_fn i S g *
              ∑ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
                  (fun π => arrivalPrefixSet π (k + 1) = S ∧ π ⟨k, hk⟩ = g),
                (mod i).seedMeasure.real {η | g ∈
                  (runDetAdmissionSteps ((mod i).det η) (v i) (P_i i) π (k + 1) hk).2} := by
          refine Finset.sum_congr rfl (fun S _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun g _ => ?_)
          rw [Finset.mul_sum, Finset.sum_filter]
        rw [h_swap_inner, Finset.mul_sum]
        refine Finset.sum_le_sum (fun S hS => ?_)
        have hScard : S.card = k + 1 := (Finset.mem_filter.mp hS).2
        obtain ⟨hc_nn, hc_sum⟩ := (hc_spec i).1 S
        have h_g_lb : ∀ g ∈ P_i i S,
            (((s : ℝ) / (k : ℝ)) * (1 / ((k + 1 : ℕ) : ℝ)) * ((evS S).card : ℝ)) * c_fn i S g ≤
              c_fn i S g *
                ∑ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
                    (fun π => arrivalPrefixSet π (k + 1) = S ∧ π ⟨k, hk⟩ = g),
                  (mod i).seedMeasure.real {η | g ∈
                    (runDetAdmissionSteps ((mod i).det η) (v i) (P_i i) π (k + 1) hk).2} := by
          intro g hgP
          have hgS : g ∈ S := (h_s3_2 i S).1 hgP
          let ev := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
            (fun π => arrivalPrefixSet π (k + 1) = S ∧ π ⟨k, hk⟩ = g)
          have h_cond_rate := (hmod i).2.1 k hk hsk S g hScard hgP
          have h_card_rel : ((k + 1 : ℕ) : ℝ) * (ev.card : ℝ) = ((evS S).card : ℝ) := by
            exact_mod_cast h_ev_card k hk S g hScard hgS
          have h_rate_eq : admitRate s (k + 1) * (ev.card : ℝ) =
              ((s : ℝ) / (k : ℝ)) * (1 / ((k + 1 : ℕ) : ℝ)) * ((evS S).card : ℝ) := by
            unfold admitRate
            have hk_sub : (k + 1 - 1 : ℕ) = k := Nat.add_sub_cancel k 1
            rw [hk_sub, ← h_card_rel]
            have hk1_ne : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
            field_simp
          rw [mul_comm _ (c_fn i S g), ← h_rate_eq]
          exact mul_le_mul_of_nonneg_left h_cond_rate (hc_nn g hgP)
        calc
          (((s : ℝ) / (k : ℝ)) * (1 / ((k + 1 : ℕ) : ℝ))) *
              (((evS S).card : ℝ) * realVal (v i) (P_i i S))
            = ∑ g ∈ P_i i S,
                (((s : ℝ) / (k : ℝ)) * (1 / ((k + 1 : ℕ) : ℝ)) * ((evS S).card : ℝ)) * c_fn i S g := by
              rw [← hc_sum, ← Finset.mul_sum]; ring
          _ ≤ ∑ g ∈ P_i i S, c_fn i S g *
                ∑ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
                    (fun π => arrivalPrefixSet π (k + 1) = S ∧ π ⟨k, hk⟩ = g),
                  (mod i).seedMeasure.real {η | g ∈
                    (runDetAdmissionSteps ((mod i).det η) (v i) (P_i i) π (k + 1) hk).2} :=
              Finset.sum_le_sum h_g_lb
      have h_sum_i := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h_term_i_lb i)
      have h_welf_S : ∀ S : Finset (Fin n),
          ∑ i : Fin m, realVal (v i) (P_i i S) = optWelfareOn v S := by
        intro S
        have h_coe : ((∑ i : Fin m, realVal (v i) (P_i i S) : ℝ) : WithBot ℝ) =
            ((optWelfareOn v S : ℝ) : WithBot ℝ) := by
          rw [← (h_s3_1 S).2.1, WithBot.coe_sum]; unfold allocWelfare
          exact Finset.sum_congr rfl (fun i _ => coe_realVal (v i) (P_i i S) (h_s3_2 i S).2.1)
        exact WithBot.coe_inj.mp h_coe
      have h_evS_sum : ∑ S ∈ powK, ((evS S).card : ℝ) * optWelfareOn v S =
          ∑ π : Equiv.Perm (Fin n), optWelfareOn v (arrivalPrefixSet π (k + 1)) := by
        calc
          ∑ S ∈ powK, ((evS S).card : ℝ) * optWelfareOn v S
            = ∑ S ∈ powK, ∑ π : Equiv.Perm (Fin n),
                (if arrivalPrefixSet π (k + 1) = S then optWelfareOn v S else 0) := by
              refine Finset.sum_congr rfl (fun S _ => ?_)
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          _ = ∑ π : Equiv.Perm (Fin n), ∑ S ∈ powK,
                (if arrivalPrefixSet π (k + 1) = S then optWelfareOn v S else 0) := Finset.sum_comm
          _ = ∑ π : Equiv.Perm (Fin n), optWelfareOn v (arrivalPrefixSet π (k + 1)) := by
              refine Finset.sum_congr rfl (fun π _ => ?_)
              have hmem : arrivalPrefixSet π (k + 1) ∈ powK :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_card_pref π (k + 1) hk⟩
              rw [Finset.sum_eq_single (arrivalPrefixSet π (k + 1))]
              · simp
              · intro S _ hne; simp [hne.symm]
              · intro hnot; exfalso; exact hnot hmem
      have h_lhs_collapse : ∑ i : Fin m,
            (((s : ℝ) / (k : ℝ)) * (1 / ((k + 1 : ℕ) : ℝ))) *
              ∑ S ∈ powK, ((evS S).card : ℝ) * realVal (v i) (P_i i S) =
          (((s : ℝ) / (k : ℝ)) * (1 / ((k + 1 : ℕ) : ℝ))) *
            ∑ π : Equiv.Perm (Fin n), optWelfareOn v (arrivalPrefixSet π (k + 1)) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        rw [← h_evS_sum]
        refine Finset.sum_congr rfl (fun S _ => ?_)
        rw [← Finset.mul_sum, h_welf_S S]
      have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
      have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have h_coeff_nn : 0 ≤ ((s : ℝ) / (k : ℝ)) * (1 / ((k + 1 : ℕ) : ℝ)) := by positivity
      have h_pref_scaled := mul_le_mul_of_nonneg_left (h_s4_prefix v k hk hv) h_coeff_nn
      have h_alg_id : (((s : ℝ) / (k : ℝ)) * (1 / ((k + 1 : ℕ) : ℝ))) *
            ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) * ((Nat.factorial n : ℝ) * optWelfare v)) =
          (((s : ℝ) / (n : ℝ)) * (1 / (k : ℝ))) * ((Nat.factorial n : ℝ) * optWelfare v) := by
        have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
        have hk1_ne : ((k + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hk1_pos
        have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
        field_simp
      linarith
    refine ⟨fun ω π k hk => (h_welf_alloc ω π k hk).2, ?_⟩
    rw [h_exp_welf_decomp, WithBot.coe_le_coe]
    have h_fact_pos : (0 : ℝ) < (Nat.factorial n : ℝ) := by
      exact_mod_cast Nat.factorial_pos n
    have h_fact_ne : (Nat.factorial n : ℝ) ≠ 0 := ne_of_gt h_fact_pos
    have h_sum_all := Finset.sum_le_sum h_step_k_lb
    have h_mul_fact := mul_le_mul_of_nonneg_left h_sum_all
      (show 0 ≤ (1 : ℝ) / (Nat.factorial n : ℝ) by positivity)
    have h_lhs_sec : (1 / (Nat.factorial n : ℝ)) *
          ∑ k ∈ Finset.Ico s n,
            (((s : ℝ) / (n : ℝ)) * (1 / (k : ℝ))) * ((Nat.factorial n : ℝ) * optWelfare v) =
        secretaryCutoffConst n s * optWelfare v := by
      unfold secretaryCutoffConst
      rw [← Finset.sum_mul, Finset.mul_sum]
      calc
        (1 / (Nat.factorial n : ℝ)) *
            ((∑ i ∈ Finset.Ico s n, (s : ℝ) / (n : ℝ) * (1 / (i : ℝ))) *
              ((Nat.factorial n : ℝ) * optWelfare v))
          = ((1 / (Nat.factorial n : ℝ)) * (Nat.factorial n : ℝ)) *
              ((∑ i ∈ Finset.Ico s n, (s : ℝ) / (n : ℝ) * (1 / (i : ℝ))) * optWelfare v) := by ring
        _ = (∑ i ∈ Finset.Ico s n, (s : ℝ) / (n : ℝ) * (1 / (i : ℝ))) * optWelfare v := by
            rw [one_div_mul_cancel h_fact_ne, one_mul]
    have h_rhs_adm : (1 / (Nat.factorial n : ℝ)) * ∑ k ∈ Finset.Ico s n, ∑ i : Fin m, termAt i k ≤
        ∑ i : Fin m, ∑ A : Finset (Fin n),
          algAdmissionProb (mod i) (v i) (P_i i) A * realVal (v i) A := by
      rw [Finset.sum_comm, Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => h_adm_val_lb i)
    linarith
  
  
  
  have h_s6 : ∀ (n s : ℕ), 1 ≤ s → s < n →
      ∃ mod : OnlineAdmissionModule n,
        ∀ (v : ItemValuation n) (P : Finset (Fin n) → Finset (Fin n)),
          IsUnitDemandValuation v → IsProposalMap v P → (∀ S, (P S).card ≤ 1) →
            HasConditionalAdmission s v P mod := by
    intro n s hs1 hsn
    let detMod : DetAdmissionModule n :=
      { step := fun prev x accepted _ propO =>
          decide (s ≤ prev.length ∧ accepted = ∅ ∧
            x ∈ propO ⟨insert x prev.toFinset, Finset.Subset.refl _⟩) }
    let mod : OnlineAdmissionModule n :=
      { Seed := PUnit
        seedMeasure := MeasureTheory.Measure.dirac ()
        isProb := inferInstance
        det := fun _ => detMod
        meas_step := fun prev x accepted valO propO b => by
          by_cases hb : detMod.step prev x accepted valO propO = b
          · have : {ω : PUnit | detMod.step prev x accepted valO propO = b} = Set.univ := by
              ext _; simp [hb]
            rw [this]; exact MeasurableSet.univ
          · have : {ω : PUnit | detMod.step prev x accepted valO propO = b} = ∅ := by
              ext _; simp [hb]
            rw [this]; exact MeasurableSet.empty }
    have h_punit_real : ∀ (Q : Prop) [Decidable Q],
        mod.seedMeasure.real {ω : mod.Seed | Q} = if Q then 1 else 0 := by
      intro Q _
      by_cases hQ : Q
      · have hset : {ω : mod.Seed | Q} = Set.univ := by ext _; simp [hQ]
        rw [if_pos hQ, hset]; exact MeasureTheory.probReal_univ
      · have hset : {ω : mod.Seed | Q} = ∅ := by ext _; simp [hQ]
        rw [if_neg hQ, hset]; exact MeasureTheory.measureReal_empty
    refine ⟨mod, fun v P hud hP hP_card => ?_⟩
    
    have h_traj : ∀ (π : Equiv.Perm (Fin n)) (t : ℕ) (ht : t ≤ n),
        ((runDetAdmissionSteps detMod v P π t ht).2 = ∅ ∧
          (∀ (r : ℕ) (hr : r + 1 ≤ t),
            (s ≤ r → π ⟨r, by omega⟩ ∉ P (arrivalPrefixSet π (r + 1))) ∧
            π ⟨r, by omega⟩ ∉ (runDetAdmissionSteps detMod v P π (r + 1) (by omega)).2)) ∨
        (∃ (r0 : ℕ) (hr0 : r0 + 1 ≤ t), s ≤ r0 ∧
          π ⟨r0, by omega⟩ ∈ P (arrivalPrefixSet π (r0 + 1)) ∧
          (runDetAdmissionSteps detMod v P π t ht).2 = {π ⟨r0, by omega⟩} ∧
          (∀ (r : ℕ) (hr : r + 1 ≤ t),
            π ⟨r, by omega⟩ ∈ (runDetAdmissionSteps detMod v P π (r + 1) (by omega)).2 ↔ r = r0)) := by
      intro π t
      induction t with
      | zero =>
        intro ht
        refine Or.inl ⟨rfl, fun r hr => ?_⟩
        omega
      | succ t ih =>
        intro ht
        have ht' := Nat.le_of_succ_le ht
        let st := runDetAdmissionSteps detMod v P π t ht'
        obtain ⟨hlen, hfin, _⟩ := h_adm_list_props detMod v P π t ht'
        have h_ins_pref : insert (π ⟨t, ht⟩) st.1.toFinset = arrivalPrefixSet π (t + 1) := by
          rw [hfin, h_pref_step π t ht]
        rcases ih ht' with ⟨hemp, hprev⟩ | ⟨r0, hr0, hsr0, hPr0, hsing, huniq⟩
        · 
          by_cases h_acc_now : s ≤ t ∧ π ⟨t, ht⟩ ∈ P (arrivalPrefixSet π (t + 1))
          · have hdec_t : detMod.step st.1 (π ⟨t, ht⟩) st.2 (fun ⟨T, _⟩ => v T) (fun ⟨T, _⟩ => P T) = true := by
              dsimp [detMod]
              rw [decide_eq_true_iff]
              exact ⟨hlen ▸ h_acc_now.1, hemp, h_ins_pref.symm ▸ h_acc_now.2⟩
            have h_acc_next : (runDetAdmissionSteps detMod v P π (t + 1) ht).2 = {π ⟨t, ht⟩} := by
              change (if detMod.step st.1 (π ⟨t, ht⟩) st.2 (fun ⟨T, _⟩ => v T) (fun ⟨T, _⟩ => P T)
                      then insert (π ⟨t, ht⟩) st.2 else st.2) = _
              rw [hdec_t, if_pos rfl, hemp]; simp
            refine Or.inr ⟨t, le_rfl, h_acc_now.1, h_acc_now.2, h_acc_next, fun r hr => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hr) with hlt | heq
            · have hr' : r + 1 ≤ t := by omega
              exact ⟨fun hm => False.elim ((hprev r hr').2 hm), fun he => by omega⟩
            · have hrt : r = t := by omega
              subst hrt
              rw [h_acc_next]
              simp
          · have hdec_f : detMod.step st.1 (π ⟨t, ht⟩) st.2 (fun ⟨T, _⟩ => v T) (fun ⟨T, _⟩ => P T) = false := by
              dsimp [detMod]
              rw [decide_eq_false_iff_not]
              rintro ⟨hs_len, _, hxP⟩
              exact h_acc_now ⟨hlen ▸ hs_len, h_ins_pref ▸ hxP⟩
            have h_acc_next : (runDetAdmissionSteps detMod v P π (t + 1) ht).2 = ∅ := by
              change (if detMod.step st.1 (π ⟨t, ht⟩) st.2 (fun ⟨T, _⟩ => v T) (fun ⟨T, _⟩ => P T)
                      then insert (π ⟨t, ht⟩) st.2 else st.2) = ∅
              rw [hdec_f]; simpa using hemp
            refine Or.inl ⟨h_acc_next, fun r hr => ?_⟩
            by_cases hrt : r = t
            · subst hrt
              rw [h_acc_next]
              exact ⟨fun hsr => fun hxP => h_acc_now ⟨hsr, hxP⟩, Finset.notMem_empty _⟩
            · exact hprev r (by omega)
        · 
          have hne_emp : st.2 ≠ ∅ := by
            dsimp [st]; rw [hsing]; exact Finset.singleton_ne_empty _
          have hdec_f : detMod.step st.1 (π ⟨t, ht⟩) st.2 (fun ⟨T, _⟩ => v T) (fun ⟨T, _⟩ => P T) = false := by
            dsimp [detMod]
            rw [decide_eq_false_iff_not]
            rintro ⟨_, h_emp, _⟩
            exact hne_emp h_emp
          have h_acc_next : (runDetAdmissionSteps detMod v P π (t + 1) ht).2 = {π ⟨r0, by omega⟩} := by
            change (if detMod.step st.1 (π ⟨t, ht⟩) st.2 (fun ⟨T, _⟩ => v T) (fun ⟨T, _⟩ => P T)
                    then insert (π ⟨t, ht⟩) st.2 else st.2) = _
            rw [hdec_f]; simpa using hsing
          refine Or.inr ⟨r0, by omega, hsr0, hPr0, h_acc_next, fun r hr => ?_⟩
          by_cases hrt : r = t
          · subst hrt
            rw [h_acc_next, Finset.mem_singleton]
            constructor
            · intro heq
              have hidx := π.injective heq
              have : r = r0 := congrArg Fin.val hidx
              omega
            · intro heq; omega
          · exact huniq r (by omega)
    
    have h_is_adm : IsAdmissionModuleFor s v P mod := by
      unfold IsAdmissionModuleFor
      intro _ π k hk
      dsimp only [mod]
      intro hcond
      obtain ⟨hlen, _, _⟩ := h_adm_list_props detMod v P π k (Nat.le_of_succ_le hk)
      let st := runDetAdmissionSteps detMod v P π k (Nat.le_of_succ_le hk)
      change decide (s ≤ st.1.length ∧ st.2 = ∅ ∧ π ⟨k, hk⟩ ∈ P (insert (π ⟨k, hk⟩) st.1.toFinset)) = false
      rw [decide_eq_false_iff_not]
      rintro ⟨hs_len, _, hxP⟩
      have hlen' : st.1.length = k := hlen
      rcases hcond with hlt | hnotP
      · omega
      · exact hnotP hxP
    
    have h_rate : ∀ (k : ℕ) (hk : k + 1 ≤ n), s ≤ k →
        ∀ (S : Finset (Fin n)) (g : Fin n),
          S.card = k + 1 → g ∈ P S →
            let ev := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
              (fun π => arrivalPrefixSet π (k + 1) = S ∧ π ⟨k, hk⟩ = g)
            admitRate s (k + 1) * (ev.card : ℝ) ≤
              ∑ π ∈ ev, mod.seedMeasure.real
                {ω | g ∈ (runDetAdmissionSteps (mod.det ω) v P π (k + 1) hk).2} := by
      intro k hk hsk S g hScard hgP
      
      have h_fwd_ind : ∀ (t : ℕ), s ≤ t → ∀ (ht : t ≤ n) (T : Finset (Fin n))
          (Ω : Finset (Equiv.Perm (Fin n))),
          T.card = t →
          (∀ x₁ ∈ T, ∀ x₂ ∈ T, ∀ π ∈ Ω, Equiv.swap x₁ x₂ * π ∈ Ω) →
            let allF := Ω.filter (fun π => arrivalPrefixSet π t = T)
            let goodF := allF.filter (fun π =>
              ∀ (r : ℕ) (hr : r < t), s ≤ r →
                π ⟨r, Nat.lt_of_lt_of_le hr ht⟩ ∉ P (arrivalPrefixSet π (r + 1)))
            s * allF.card ≤ t * goodF.card := by
        intro t
        induction t with
        | zero =>
          intro hst; omega
        | succ t ih =>
          intro hst1 ht1 T Ω hTcard hΩ_inv allF goodF
          rcases eq_or_lt_of_le hst1 with heq_s | hlt_s
          · 
            subst heq_s
            have h_eq_fg : goodF = allF := by
              ext π
              simp only [goodF, Finset.mem_filter, and_iff_left_iff_imp]
              intro _ r hr hsr; omega
            rw [h_eq_fg]
          · 
            have hst : s ≤ t := by omega
            have ht_le : t ≤ n := Nat.le_of_succ_le ht1
            have ht_pos : 0 < t := by omega
            let fibAll : Fin n → Finset (Equiv.Perm (Fin n)) := fun x =>
              (Ω.filter (fun π => π ⟨t, ht1⟩ = x)).filter (fun π => arrivalPrefixSet π t = T.erase x)
            let fibGood : Fin n → Finset (Equiv.Perm (Fin n)) := fun x =>
              (fibAll x).filter (fun π =>
                ∀ (r : ℕ) (hr : r < t), s ≤ r →
                  π ⟨r, Nat.lt_of_lt_of_le hr ht_le⟩ ∉ P (arrivalPrefixSet π (r + 1)))
            have h_fib_mem : ∀ x ∈ T, ∀ π : Equiv.Perm (Fin n),
                π ∈ fibAll x ↔ (π ∈ allF ∧ π ⟨t, ht1⟩ = x) := by
              intro x hxT π
              simp only [fibAll, allF, Finset.mem_filter]
              constructor
              · rintro ⟨⟨hπΩ, hπt⟩, hpref_t⟩
                refine ⟨⟨hπΩ, ?_⟩, hπt⟩
                rw [← h_pref_step π t ht1, hπt, hpref_t, Finset.insert_erase hxT]
              · rintro ⟨⟨hπΩ, hpref_t1⟩, hπt⟩
                refine ⟨⟨hπΩ, hπt⟩, ?_⟩
                have hnot := h_pref_notMem π t ht1
                have hins : insert x (arrivalPrefixSet π t) = T := by
                  rw [← hπt, h_pref_step π t ht1, hpref_t1]
                rw [← hins, Finset.erase_insert (hπt ▸ hnot)]
            have h_fib_eq : ∀ x₁ ∈ T, ∀ x₂ ∈ T, (fibAll x₁).card = (fibAll x₂).card := by
              intro x₁ hx₁ x₂ hx₂
              refine Finset.card_bij (fun π _ => Equiv.swap x₁ x₂ * π) ?_ ?_ ?_
              · intro π hπ
                obtain ⟨hπ_all, hπt⟩ := (h_fib_mem x₁ hx₁ π).mp hπ
                obtain ⟨hπΩ, hpref1⟩ := Finset.mem_filter.mp hπ_all
                refine (h_fib_mem x₂ hx₂ (Equiv.swap x₁ x₂ * π)).mpr
                  ⟨Finset.mem_filter.mpr ⟨hΩ_inv x₁ hx₁ x₂ hx₂ π hπΩ, ?_⟩, ?_⟩
                · have h_img : arrivalPrefixSet (Equiv.swap x₁ x₂ * π) (t + 1) =
                      (arrivalPrefixSet π (t + 1)).image (Equiv.swap x₁ x₂) := by
                    unfold arrivalPrefixSet; rw [Finset.image_image]; rfl
                  rw [h_img, hpref1, h_swap_image T x₁ hx₁ x₂ hx₂]
                · change Equiv.swap x₁ x₂ (π ⟨t, ht1⟩) = x₂
                  rw [hπt, Equiv.swap_apply_left]
              · intro π₁ _ π₂ _ heq
                exact mul_left_cancel heq
              · intro σ hσ
                obtain ⟨hσ_all, hσt⟩ := (h_fib_mem x₂ hx₂ σ).mp hσ
                obtain ⟨hσΩ, hpref2⟩ := Finset.mem_filter.mp hσ_all
                refine ⟨Equiv.swap x₁ x₂ * σ, ?_, by dsimp only; ext z; simp⟩
                refine (h_fib_mem x₁ hx₁ (Equiv.swap x₁ x₂ * σ)).mpr
                  ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
                · have hswap := hΩ_inv x₂ hx₂ x₁ hx₁ σ hσΩ
                  rwa [Equiv.swap_comm] at hswap
                · have h_img : arrivalPrefixSet (Equiv.swap x₁ x₂ * σ) (t + 1) =
                      (arrivalPrefixSet σ (t + 1)).image (Equiv.swap x₁ x₂) := by
                    unfold arrivalPrefixSet; rw [Finset.image_image]; rfl
                  rw [h_img, hpref2, h_swap_image T x₁ hx₁ x₂ hx₂]
                · change Equiv.swap x₁ x₂ (σ ⟨t, ht1⟩) = x₁
                  rw [hσt, Equiv.swap_apply_right]
            have h_all_part : allF = T.biUnion fibAll := by
              ext π
              simp only [Finset.mem_biUnion]
              constructor
              · intro hπ
                have hpref : arrivalPrefixSet π (t + 1) = T := (Finset.mem_filter.mp hπ).2
                have hxT : π ⟨t, ht1⟩ ∈ T := by
                  rw [← hpref]
                  exact Finset.mem_image.mpr ⟨⟨t, ht1⟩,
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.lt_succ_self t⟩, rfl⟩
                exact ⟨π ⟨t, ht1⟩, hxT, (h_fib_mem (π ⟨t, ht1⟩) hxT π).mpr ⟨hπ, rfl⟩⟩
              · rintro ⟨x, hxT, hπx⟩
                exact ((h_fib_mem x hxT π).mp hπx).1
            have h_fib_disj : ∀ (U_sub : Finset (Fin n)), U_sub ⊆ T →
                (U_sub : Set (Fin n)).PairwiseDisjoint fibAll := by
              intro U_sub hUT x₁ hx₁ x₂ hx₂ hne
              change Disjoint (fibAll x₁) (fibAll x₂)
              rw [Finset.disjoint_left]
              intro π h₁ h₂
              have ht₁ := ((h_fib_mem x₁ (hUT hx₁) π).mp h₁).2
              have ht₂ := ((h_fib_mem x₂ (hUT hx₂) π).mp h₂).2
              exact hne (ht₁.symm.trans ht₂)
            have h_fib_card_rel : ∀ x ∈ T, (t + 1) * (fibAll x).card = allF.card := by
              intro x hxT
              rw [h_all_part, Finset.card_biUnion (h_fib_disj T (Finset.Subset.refl T)),
                  Finset.sum_congr rfl (fun y hy => h_fib_eq y hy x hxT),
                  Finset.sum_const, hTcard, smul_eq_mul]
            have h_ih_x : ∀ x ∈ T, s * (fibAll x).card ≤ t * (fibGood x).card := by
              intro x hxT
              have hTe_card : (T.erase x).card = t := by
                rw [Finset.card_erase_of_mem hxT, hTcard]; omega
              have hΩx_inv : ∀ y₁ ∈ T.erase x, ∀ y₂ ∈ T.erase x,
                  ∀ π ∈ Ω.filter (fun π => π ⟨t, ht1⟩ = x),
                    Equiv.swap y₁ y₂ * π ∈ Ω.filter (fun π => π ⟨t, ht1⟩ = x) := by
                intro y₁ hy₁ y₂ hy₂ π hπ
                obtain ⟨hπΩ, hπt⟩ := Finset.mem_filter.mp hπ
                obtain ⟨hy₁_ne, hy₁T⟩ := Finset.mem_erase.mp hy₁
                obtain ⟨hy₂_ne, hy₂T⟩ := Finset.mem_erase.mp hy₂
                refine Finset.mem_filter.mpr ⟨hΩ_inv y₁ hy₁T y₂ hy₂T π hπΩ, ?_⟩
                change Equiv.swap y₁ y₂ (π ⟨t, ht1⟩) = x
                rw [hπt, Equiv.swap_apply_of_ne_of_ne hy₁_ne.symm hy₂_ne.symm]
              exact ih hst ht_le (T.erase x) (Ω.filter (fun π => π ⟨t, ht1⟩ = x)) hTe_card hΩx_inv
            let safeT := T \ P T
            have h_safeT_sub : safeT ⊆ T := Finset.sdiff_subset
            have h_safeT_card : t ≤ safeT.card := by
              have h_add := Finset.card_sdiff_add_card_inter T (P T)
              have h_int_le : (T ∩ P T).card ≤ 1 :=
                (Finset.card_le_card Finset.inter_subset_right).trans (hP_card T)
              dsimp [safeT]
              omega
            have h_good_sub : safeT.biUnion fibGood ⊆ goodF := by
              intro π hπ
              rcases Finset.mem_biUnion.mp hπ with ⟨x, hx_safe, hπ_fg⟩
              obtain ⟨hxT, hx_notP⟩ := Finset.mem_sdiff.mp hx_safe
              obtain ⟨hπ_fa, hπ_prev⟩ := Finset.mem_filter.mp hπ_fg
              obtain ⟨hπ_all, hπt⟩ := (h_fib_mem x hxT π).mp hπ_fa
              have hpref_T : arrivalPrefixSet π (t + 1) = T := (Finset.mem_filter.mp hπ_all).2
              refine Finset.mem_filter.mpr ⟨hπ_all, fun r hr hsr => ?_⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | rfl
              · exact hπ_prev r hlt hsr
              · rw [hpref_T]
                have hidx_eq : (⟨r, Nat.lt_of_lt_of_le hr ht1⟩ : Fin n) = ⟨r, ht1⟩ := rfl
                rw [hidx_eq, hπt]
                exact hx_notP
            have h_good_disj : (safeT : Set (Fin n)).PairwiseDisjoint fibGood := by
              intro x₁ hx₁ x₂ hx₂ hne
              change Disjoint (fibGood x₁) (fibGood x₂)
              exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
                (h_fib_disj safeT h_safeT_sub hx₁ hx₂ hne)
            have h_sum_good : ∑ x ∈ safeT, (fibGood x).card ≤ goodF.card := by
              rw [← Finset.card_biUnion h_good_disj]
              exact Finset.card_le_card h_good_sub
            have h_chain : t * (s * allF.card) ≤ t * ((t + 1) * goodF.card) := by
              calc
                t * (s * allF.card)
                  ≤ safeT.card * (s * allF.card) := Nat.mul_le_mul_right _ h_safeT_card
                _ = ∑ x ∈ safeT, s * ((t + 1) * (fibAll x).card) := by
                    rw [← smul_eq_mul, ← Finset.sum_const]
                    exact Finset.sum_congr rfl (fun x hx => by rw [h_fib_card_rel x (h_safeT_sub hx)])
                _ = (t + 1) * ∑ x ∈ safeT, s * (fibAll x).card := by
                    rw [Finset.mul_sum]
                    exact Finset.sum_congr rfl (fun x _ => by ring)
                _ ≤ (t + 1) * ∑ x ∈ safeT, t * (fibGood x).card :=
                    Nat.mul_le_mul_left (t + 1)
                      (Finset.sum_le_sum (fun x hx => h_ih_x x (h_safeT_sub hx)))
                _ = (t + 1) * (t * ∑ x ∈ safeT, (fibGood x).card) := by
                    rw [← Finset.mul_sum]
                _ ≤ (t + 1) * (t * goodF.card) :=
                    Nat.mul_le_mul_left (t + 1) (Nat.mul_le_mul_left t h_sum_good)
                _ = t * ((t + 1) * goodF.card) := by ring
            exact Nat.le_of_mul_le_mul_left h_chain ht_pos
      
      have hgS : g ∈ S := (hP S).1 hgP
      let T0 := S.erase g
      have hT0_card : T0.card = k := by
        dsimp [T0]; rw [Finset.card_erase_of_mem hgS, hScard]; omega
      let Ω0 := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => π ⟨k, hk⟩ = g)
      have hΩ0_inv : ∀ x₁ ∈ T0, ∀ x₂ ∈ T0, ∀ π ∈ Ω0, Equiv.swap x₁ x₂ * π ∈ Ω0 := by
        intro x₁ hx₁ x₂ hx₂ π hπ
        have hπg : π ⟨k, hk⟩ = g := (Finset.mem_filter.mp hπ).2
        have hx₁_ne : x₁ ≠ g := (Finset.mem_erase.mp hx₁).1
        have hx₂_ne : x₂ ≠ g := (Finset.mem_erase.mp hx₂).1
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        change Equiv.swap x₁ x₂ (π ⟨k, hk⟩) = g
        rw [hπg, Equiv.swap_apply_of_ne_of_ne hx₁_ne.symm hx₂_ne.symm]
      let allF := Ω0.filter (fun π => arrivalPrefixSet π k = T0)
      let goodF := allF.filter (fun π =>
        ∀ (r : ℕ) (hr : r < k), s ≤ r →
          π ⟨r, Nat.lt_of_lt_of_le hr (Nat.le_of_succ_le hk)⟩ ∉ P (arrivalPrefixSet π (r + 1)))
      have h_nat_bound := h_fwd_ind k hsk (Nat.le_of_succ_le hk) T0 Ω0 hT0_card hΩ0_inv
      let ev := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
        (fun π => arrivalPrefixSet π (k + 1) = S ∧ π ⟨k, hk⟩ = g)
      have h_allF_eq_ev : allF = ev := by
        ext π
        simp only [allF, Ω0, ev, Finset.mem_filter, Finset.mem_univ, true_and, T0]
        constructor
        · rintro ⟨hπg, hpref_k⟩
          refine ⟨?_, hπg⟩
          rw [← h_pref_step π k hk, hπg, hpref_k, Finset.insert_erase hgS]
        · rintro ⟨hpref_k1, hπg⟩
          refine ⟨hπg, ?_⟩
          have hnot := h_pref_notMem π k hk
          have hins : insert g (arrivalPrefixSet π k) = S := by
            rw [← hπg, h_pref_step π k hk, hpref_k1]
          rw [← hins, Finset.erase_insert (hπg ▸ hnot)]
      have h_good_admit : ∀ π ∈ goodF,
          g ∈ (runDetAdmissionSteps detMod v P π (k + 1) hk).2 := by
        intro π hπ
        obtain ⟨hπ_all, hπ_prev⟩ := Finset.mem_filter.mp hπ
        have hπ_ev : π ∈ ev := h_allF_eq_ev ▸ hπ_all
        obtain ⟨hpref_k1, hπg⟩ := (Finset.mem_filter.mp hπ_ev).2
        rcases h_traj π k (Nat.le_of_succ_le hk) with ⟨hemp, _⟩ | ⟨r0, hr0, hsr0, hPr0, _, _⟩
        · let st := runDetAdmissionSteps detMod v P π k (Nat.le_of_succ_le hk)
          obtain ⟨hlen, hfin, _⟩ := h_adm_list_props detMod v P π k (Nat.le_of_succ_le hk)
          have hdec_t : detMod.step st.1 (π ⟨k, hk⟩) st.2 (fun ⟨T, _⟩ => v T) (fun ⟨T, _⟩ => P T) = true := by
            dsimp [detMod]
            rw [decide_eq_true_iff]
            refine ⟨hlen ▸ hsk, hemp, ?_⟩
            rw [hfin, h_pref_step π k hk, hpref_k1, hπg]
            exact hgP
          change g ∈ (if detMod.step st.1 (π ⟨k, hk⟩) st.2 (fun ⟨T, _⟩ => v T) (fun ⟨T, _⟩ => P T)
                      then insert (π ⟨k, hk⟩) st.2 else st.2)
          rw [hdec_t, if_pos rfl, hπg]
          exact Finset.mem_insert_self g _
        · exfalso
          exact hπ_prev r0 (by omega) hsr0 hPr0
      have h_sum_lb : (goodF.card : ℝ) ≤
          ∑ π ∈ ev, mod.seedMeasure.real
            {ω | g ∈ (runDetAdmissionSteps (mod.det ω) v P π (k + 1) hk).2} := by
        have h_sub_ev : goodF ⊆ ev := by
          rw [← h_allF_eq_ev]; exact Finset.filter_subset _ _
        have h_nonneg : ∀ π ∈ ev, 0 ≤ mod.seedMeasure.real
            {ω | g ∈ (runDetAdmissionSteps (mod.det ω) v P π (k + 1) hk).2} :=
          fun _ _ => measureReal_nonneg
        calc
          (goodF.card : ℝ) = ∑ π ∈ goodF, (1 : ℝ) := by simp
          _ ≤ ∑ π ∈ goodF, mod.seedMeasure.real
                {ω | g ∈ (runDetAdmissionSteps (mod.det ω) v P π (k + 1) hk).2} := by
              refine Finset.sum_le_sum (fun π hπ => ?_)
              rw [h_punit_real (g ∈ (runDetAdmissionSteps detMod v P π (k + 1) hk).2),
                  if_pos (h_good_admit π hπ)]
          _ ≤ ∑ π ∈ ev, mod.seedMeasure.real
                {ω | g ∈ (runDetAdmissionSteps (mod.det ω) v P π (k + 1) hk).2} :=
              Finset.sum_le_sum_of_subset_of_nonneg h_sub_ev (fun π hπ _ => h_nonneg π hπ)
      have h_natR : (s : ℝ) * (ev.card : ℝ) ≤ (k : ℝ) * (goodF.card : ℝ) := by
        rw [← h_allF_eq_ev]
        exact_mod_cast h_nat_bound
      have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
      have h_div_le : ((s : ℝ) / (k : ℝ)) * (ev.card : ℝ) ≤ (goodF.card : ℝ) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hk_pos, mul_comm (goodF.card : ℝ)]
        exact h_natR
      unfold admitRate
      have hk_sub : (k + 1 - 1 : ℕ) = k := Nat.add_sub_cancel k 1
      rw [hk_sub]
      linarith
    
    obtain ⟨w, hw_nn, hv_eq⟩ := hud
    let c : Finset (Fin n) → Fin n → ℝ := fun _ g => w g
    have h_v_ne_bot : ∀ S : Finset (Fin n), v S ≠ ⊥ := by
      intro S; rw [hv_eq S]; exact WithBot.coe_ne_bot
    have h_realVal_emp : realVal v ∅ = 0 := by
      unfold realVal; rw [hv_eq ∅]; simp
    have h_realVal_sing : ∀ g : Fin n, realVal v {g} = w g := by
      intro g; unfold realVal; rw [hv_eq {g}]; simp
    refine ⟨h_is_adm, h_rate, c, ?_, fun S _ => h_v_ne_bot S, ?_⟩
    · intro S
      refine ⟨fun g _ => hw_nn g, ?_⟩
      rcases (P S).eq_empty_or_nonempty with hemp | ⟨g, hg⟩
      · rw [hemp, Finset.sum_empty, h_realVal_emp]
      · have hcard1 : (P S).card ≤ 1 := hP_card S
        have hsing : P S = {g} := by
          refine Finset.Subset.antisymm (fun y hy => ?_) (Finset.singleton_subset_iff.mpr hg)
          by_contra hy_ne
          have hy_ne' : y ≠ g := Finset.notMem_singleton.mp hy_ne
          have hsub2 : ({g, y} : Finset (Fin n)) ⊆ P S := by
            intro z hz
            rcases Finset.mem_insert.mp hz with rfl | hz'
            · exact hg
            · rw [Finset.mem_singleton.mp hz']; exact hy
          have h2 : 2 ≤ (P S).card := by
            have := Finset.card_le_card hsub2
            rw [Finset.card_pair hy_ne'.symm] at this
            exact this
          omega
        rw [hsing, Finset.sum_singleton, h_realVal_sing g]
    · have h_no_bot : ¬ ∃ S : Finset (Fin n), 0 < algAdmissionProb mod v P S ∧ v S = ⊥ := by
        rintro ⟨S, _, hb⟩; exact h_v_ne_bot S hb
      unfold expectedAdmissionVal
      rw [if_neg h_no_bot, WithBot.coe_le_coe]
      
      have h_adm_prob_sum : ∑ S : Finset (Fin n), algAdmissionProb mod v P S * realVal v S =
          (1 / (Nat.factorial n : ℝ)) *
            ∑ π : Equiv.Perm (Fin n), realVal v (runDetAdmission detMod v P π) := by
        unfold algAdmissionProb
        have h_each_S : ∀ S : Finset (Fin n),
            ((1 / (Nat.factorial n : ℝ)) *
              ∑ π : Equiv.Perm (Fin n),
                mod.seedMeasure.real {ω | runDetAdmission (mod.det ω) v P π = S}) * realVal v S =
            (1 / (Nat.factorial n : ℝ)) *
              ∑ π : Equiv.Perm (Fin n),
                if runDetAdmission detMod v P π = S then realVal v S else 0 := by
          intro S
          rw [mul_assoc, Finset.sum_mul]
          congr 1
          refine Finset.sum_congr rfl (fun π _ => ?_)
          rw [h_punit_real (runDetAdmission detMod v P π = S)]
          split_ifs <;> ring
        rw [Finset.sum_congr rfl (fun S _ => h_each_S S), ← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl (fun π _ => ?_)
        simp
      have h_cred_π : ∀ π : Equiv.Perm (Fin n),
          (∑ idx : Fin n,
            if s ≤ idx.1 then
              c (arrivalPrefixSet π (idx.1 + 1)) (π idx) *
                mod.seedMeasure.real {ω | π idx ∈
                  (runDetAdmissionSteps (mod.det ω) v P π (idx.1 + 1) idx.2).2}
            else 0) = realVal v (runDetAdmission detMod v P π) := by
        intro π
        rcases h_traj π n (le_refl n) with ⟨hemp, hnone⟩ | ⟨r0, hr0, hsr0, _, hsing, huniq⟩
        · have h_final : runDetAdmission detMod v P π = ∅ := hemp
          rw [h_final, h_realVal_emp]
          refine Finset.sum_eq_zero (fun idx _ => ?_)
          by_cases hs_idx : s ≤ idx.1
          · rw [if_pos hs_idx, h_punit_real (π idx ∈ (runDetAdmissionSteps detMod v P π (idx.1 + 1) idx.2).2)]
            have hnot := (hnone idx.1 idx.2).2
            have hidx_eq : (⟨idx.1, by omega⟩ : Fin n) = idx := Fin.ext rfl
            rw [hidx_eq] at hnot
            rw [if_neg hnot, mul_zero]
          · rw [if_neg hs_idx]
        · let idx0 : Fin n := ⟨r0, hr0⟩
          have h_final : runDetAdmission detMod v P π = {π idx0} := hsing
          rw [h_final, h_realVal_sing (π idx0)]
          rw [Finset.sum_eq_single idx0]
          · have hs_idx0 : s ≤ idx0.1 := hsr0
            rw [if_pos hs_idx0,
                h_punit_real (π idx0 ∈ (runDetAdmissionSteps detMod v P π (idx0.1 + 1) idx0.2).2)]
            have hmem0 : π idx0 ∈ (runDetAdmissionSteps detMod v P π (idx0.1 + 1) idx0.2).2 :=
              (huniq r0 hr0).mpr rfl
            rw [if_pos hmem0]
            dsimp [c]; ring
          · intro idx _ hne
            by_cases hs_idx : s ≤ idx.1
            · rw [if_pos hs_idx,
                  h_punit_real (π idx ∈ (runDetAdmissionSteps detMod v P π (idx.1 + 1) idx.2).2)]
              have hne_val : idx.1 ≠ r0 := fun heq => hne (Fin.ext heq)
              have hnot : π idx ∉ (runDetAdmissionSteps detMod v P π (idx.1 + 1) idx.2).2 := by
                intro hmem
                exact hne_val ((huniq idx.1 idx.2).mp hmem)
              rw [if_neg hnot, mul_zero]
            · rw [if_neg hs_idx]
          · intro hnot; exfalso; exact hnot (Finset.mem_univ idx0)
      rw [h_adm_prob_sum, Finset.sum_congr rfl (fun π _ => h_cred_π π)]
  
  
  
  have h_conj4 : ∀ {n m s : ℕ} (v : Fin m → ItemValuation n) (mod : Fin m → OnlineAdmissionModule n),
      1 ≤ s → s < n →
      (∀ i : Fin m, IsGSValuation (v i)) →
      (∀ i : Fin m, HasConditionalAdmission s (v i) (fun S => gsPrefixOptAlloc v S i) (mod i)) →
        ∃ alg : OnlineWelfareAlg n m,
          (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
            IsAllocOf (runDetWelfareSteps (alg.det ω) v π k hk).1.toFinset
              (runDetWelfareSteps (alg.det ω) v π k hk).2) ∧
          (((secretaryCutoffConst n s * optWelfare v : ℝ) : WithBot ℝ) ≤
            expectedWelfareVal alg v) := by
    intro n m s v mod hs1 hsn hv hmod
    obtain ⟨alg, halg⟩ := h_s5 mod hs1 hsn
    exact ⟨alg, halg v hv hmod⟩
  have h_conj5b : ∀ (n m : ℕ),
      ∃ alg : OnlineWelfareAlg n m,
        ∀ v : Fin m → ItemValuation n, (∀ i, IsUnitDemandValuation (v i)) →
          (((invE * optWelfare v : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg v) := by
    intro n m
    by_cases hn1 : n ≤ 1
    · obtain ⟨alg, halg⟩ := h_s4_small n m hn1
      exact ⟨alg, fun v hud => halg v (fun i => h_ud_gs (v i) (hud i))⟩
    · have hn2 : 2 ≤ n := by omega
      obtain ⟨s, hs1, hsn, hsec⟩ := h_s4_cutoff n hn2
      obtain ⟨mod0, hmod0⟩ := h_s6 n s hs1 hsn
      obtain ⟨alg, halg⟩ := h_s5 (fun (_ : Fin m) => mod0) hs1 hsn
      refine ⟨alg, fun v hud => ?_⟩
      have hv_gs : ∀ i : Fin m, IsGSValuation (v i) := fun i => h_ud_gs (v i) (hud i)
      have hv0 : ∀ i : Fin m, v i ∅ = ((0 : ℝ) : WithBot ℝ) := fun i => (hv_gs i).1
      obtain ⟨_, hP_map, hP_card⟩ := h_s3_main v hv0
      have h_adm : ∀ i : Fin m, HasConditionalAdmission s (v i) (fun S => gsPrefixOptAlloc v S i) mod0 :=
        fun i => hmod0 (v i) (fun S => gsPrefixOptAlloc v S i) (hud i) (hP_map i) (hP_card i (hud i))
      have h_welf_lb := (halg v hv_gs h_adm).2
      have h_opt_nn : 0 ≤ optWelfare v := h_opt_nonneg v hv0
      have h_inv_le : invE * optWelfare v ≤ secretaryCutoffConst n s * optWelfare v :=
        mul_le_mul_of_nonneg_right hsec h_opt_nn
      exact le_trans (WithBot.coe_le_coe.mpr h_inv_le) h_welf_lb
  have h_conj6 : (∀ (n s : ℕ), 2 ≤ n → 1 ≤ s → s < n →
        ∃ mod : OnlineAdmissionModule n,
          ∀ (v : ItemValuation n) (P : Finset (Fin n) → Finset (Fin n)),
            IsGSValuation v → IsProposalMap v P → HasConditionalAdmission s v P mod) →
      ∀ (n m : ℕ),
        ∃ alg : OnlineWelfareAlg n m,
          ∀ v : Fin m → ItemValuation n, (∀ i, IsGSValuation (v i)) →
            (((invE * optWelfare v : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg v) := by
    intro h_univ n m
    by_cases hn1 : n ≤ 1
    · exact h_s4_small n m hn1
    · have hn2 : 2 ≤ n := by omega
      obtain ⟨s, hs1, hsn, hsec⟩ := h_s4_cutoff n hn2
      obtain ⟨mod0, hmod0⟩ := h_univ n s hn2 hs1 hsn
      obtain ⟨alg, halg⟩ := h_s5 (fun (_ : Fin m) => mod0) hs1 hsn
      refine ⟨alg, fun v hv_gs => ?_⟩
      have hv0 : ∀ i : Fin m, v i ∅ = ((0 : ℝ) : WithBot ℝ) := fun i => (hv_gs i).1
      obtain ⟨_, hP_map, _⟩ := h_s3_main v hv0
      have h_adm : ∀ i : Fin m, HasConditionalAdmission s (v i) (fun S => gsPrefixOptAlloc v S i) mod0 :=
        fun i => hmod0 (v i) (fun S => gsPrefixOptAlloc v S i) (hv_gs i) (hP_map i)
      have h_welf_lb := (halg v hv_gs h_adm).2
      have h_opt_nn : 0 ≤ optWelfare v := h_opt_nonneg v hv0
      have h_inv_le : invE * optWelfare v ≤ secretaryCutoffConst n s * optWelfare v :=
        mul_le_mul_of_nonneg_right hsec h_opt_nn
      exact le_trans (WithBot.coe_le_coe.mpr h_inv_le) h_welf_lb
  refine ⟨h_s1, ?_, h_s3_main, h_conj4, h_s6, h_conj5b, h_conj6⟩
  clear h_s1 coe_unbotD coe_realVal h_allocCode_lt h_s3_main h_opt_nonneg h_ud_gs
    dom_erase dom_hereditary gs_submod gs_additive_support h_s4_prefix h_s4_cutoff
    h_s4_small h_pref_step h_pref_notMem h_card_pref h_swap_image h_adm_list_props
    h_s5 h_s6 h_conj4 h_conj5b h_conj6
  
  
  
  intro n hn lam hlam0 hlam1 v bernProb poolVal
  let h : ℕ → ℝ := fun k => (k : ℝ) - 3 * ((k - 1 : ℕ) : ℝ)
  have hv_eq : ∀ (i : Fin n) (S : Finset (Fin n)), v i S = ((h S.card : ℝ) : WithBot ℝ) :=
    fun _ _ => rfl
  have hh0 : h 0 = 0 := by norm_num [h]
  have hh1 : h 1 = 1 := by norm_num [h]
  have hh_ge1 : ∀ k : ℕ, 1 ≤ k → h k = 3 - 2 * (k : ℝ) := by
    intro k hk
    dsimp [h]
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      simpa using (Nat.cast_sub hk : ((k - 1 : ℕ) : ℝ) = _)
    rw [hcast]
    ring
  have hh_le1 : ∀ k : ℕ, h k ≤ 1 := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [hh0]; norm_num
    · rw [hh_ge1 k hk]
      have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
  have h_gs : ∀ i : Fin n, IsGSValuation (v i) := by
    intro i
    refine ⟨by simp [hv_eq i, hh0], ?_⟩
    intro X Y _ _ x hx
    obtain ⟨hxX, hxY⟩ := Finset.mem_sdiff.mp hx
    have hX_pos : 1 ≤ X.card := Finset.card_pos.mpr ⟨x, hxX⟩
    have hXe_card : (X.erase x).card = X.card - 1 := Finset.card_erase_of_mem hxX
    have hYx_card : (insert x Y).card = Y.card + 1 := Finset.card_insert_of_notMem hxY
    rcases Y.eq_empty_or_nonempty with rfl | hYne
    · refine le_trans ?_ (le_max_left _ _)
      rw [hv_eq i, hv_eq i, hv_eq i, hv_eq i, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
      simp only [Finset.card_empty, hh0, add_zero, hXe_card, hYx_card, zero_add, hh1]
      rcases eq_or_lt_of_le hX_pos with hX1 | hX2
      · rw [← hX1, Nat.sub_self, hh0, hh1]; norm_num
      · have h1 : 1 ≤ X.card - 1 := by omega
        rw [hh_ge1 X.card hX_pos, hh_ge1 (X.card - 1) h1]
        have hcast : ((X.card - 1 : ℕ) : ℝ) = (X.card : ℝ) - 1 := by
          simpa using (Nat.cast_sub hX_pos : ((X.card - 1 : ℕ) : ℝ) = _)
        linarith
    · have hY_pos : 1 ≤ Y.card := Finset.card_pos.mpr hYne
      rcases eq_or_lt_of_le hX_pos with hX1 | hX2
      · obtain ⟨y, hyY⟩ := hYne
        have hyX : y ∉ X := by
          intro hyX_mem
          have hXe_emp : X.erase x = ∅ := Finset.card_eq_zero.mp (by omega)
          have hX_sing : X = {x} := by rw [← Finset.insert_erase hxX, hXe_emp]; rfl
          rw [hX_sing, Finset.mem_singleton] at hyX_mem
          exact hxY (hyX_mem ▸ hyY)
        have hy_sdiff : y ∈ Y \ X := Finset.mem_sdiff.mpr ⟨hyY, hyX⟩
        refine le_trans ?_ (le_max_right _ _)
        refine le_trans ?_
          (Finset.le_sup (f := fun y => v i (insert y (X.erase x)) + v i ((insert x Y).erase y)) hy_sdiff)
        dsimp only
        have hXe_emp : X.erase x = ∅ := Finset.card_eq_zero.mp (by omega)
        have hins_y : (insert y (X.erase x)).card = 1 := by rw [hXe_emp]; simp
        have hy_ins : y ∈ insert x Y := Finset.mem_insert_of_mem hyY
        have her_y : ((insert x Y).erase y).card = Y.card := by
          rw [Finset.card_erase_of_mem hy_ins, hYx_card]; omega
        rw [hv_eq i, hv_eq i, hv_eq i, hv_eq i, ← hX1, hins_y, her_y]
      · refine le_trans ?_ (le_max_left _ _)
        rw [hv_eq i, hv_eq i, hv_eq i, hv_eq i, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
        rw [hXe_card, hYx_card]
        have h1 : 1 ≤ X.card - 1 := by omega
        have h2 : 1 ≤ Y.card + 1 := by omega
        rw [hh_ge1 X.card hX_pos, hh_ge1 Y.card hY_pos,
            hh_ge1 (X.card - 1) h1, hh_ge1 (Y.card + 1) h2]
        have hcast : ((X.card - 1 : ℕ) : ℝ) = (X.card : ℝ) - 1 := by
          simpa using (Nat.cast_sub hX_pos : ((X.card - 1 : ℕ) : ℝ) = _)
        push_cast [hcast]
        linarith
  have h_env : ∀ (i : Fin n) (S : Finset (Fin n)),
      disposalEnvelope (v i) S = (min S.card 1 : ℝ) := by
    intro i S
    rcases S.eq_empty_or_nonempty with rfl | ⟨x, hxS⟩
    · simp [disposalEnvelope, hv_eq i, hh0]
    · have hS_pos : 1 ≤ S.card := Finset.card_pos.mpr ⟨x, hxS⟩
      have hmin : (min S.card 1 : ℝ) = 1 := by
        have : min S.card 1 = 1 := Nat.min_eq_right hS_pos
        exact_mod_cast this
      have hsup : S.powerset.sup (v i) = ((1 : ℝ) : WithBot ℝ) := by
        refine le_antisymm (Finset.sup_le (fun T _ => ?_)) ?_
        · rw [hv_eq i, WithBot.coe_le_coe]
          exact hh_le1 T.card
        · have hx_sub : ({x} : Finset (Fin n)) ∈ S.powerset :=
            Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hxS)
          refine le_trans ?_ (Finset.le_sup (f := v i) hx_sub)
          rw [hv_eq i, Finset.card_singleton, hh1]
      rw [hmin]
      simp [disposalEnvelope, hsup]
  have h_opt : optWelfare v = (n : ℝ) := by
    let A_univ := (Finset.univ : Finset (Fin n → Finset (Fin n))).filter (fun X => IsAllocOf Finset.univ X)
    have hsup : A_univ.sup (allocWelfare v) = ((n : ℝ) : WithBot ℝ) := by
      refine le_antisymm (Finset.sup_le (fun X _ => ?_)) ?_
      · have hw_eq : allocWelfare v X = ((∑ i : Fin n, h (X i).card : ℝ) : WithBot ℝ) := by
          unfold allocWelfare
          rw [WithBot.coe_sum]
        rw [hw_eq, WithBot.coe_le_coe]
        calc
          ∑ i : Fin n, h (X i).card ≤ ∑ _i : Fin n, (1 : ℝ) :=
            Finset.sum_le_sum (fun i _ => hh_le1 (X i).card)
          _ = (n : ℝ) := by simp
      · let X_sing : Fin n → Finset (Fin n) := fun i => {i}
        have h_alloc : IsAllocOf Finset.univ X_sing := by
          refine ⟨fun _ => Finset.subset_univ _, fun i j hij => ?_⟩
          exact Finset.disjoint_singleton.mpr hij
        have h_mem : X_sing ∈ A_univ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_alloc⟩
        refine le_trans ?_ (Finset.le_sup (f := allocWelfare v) h_mem)
        unfold allocWelfare
        have h_each : ∀ i : Fin n, v i (X_sing i) = ((1 : ℝ) : WithBot ℝ) := by
          intro i; simp [X_sing, hv_eq, hh1]
        rw [Finset.sum_congr rfl (fun i _ => h_each i), ← WithBot.coe_sum]
        simp
    unfold optWelfare optWelfareOn
    rw [hsup, WithBot.unbotD_coe]
  let prefList : ∀ (t : ℕ), t ≤ n → List (Fin n) :=
    Nat.rec (fun _ => []) (fun t ih ht => ih (Nat.le_of_succ_le ht) ++ [(⟨t, ht⟩ : Fin n)])
  have h_pref_len : ∀ (t : ℕ) (ht : t ≤ n), (prefList t ht).length = t := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      change (prefList t (Nat.le_of_succ_le ht) ++ [(⟨t, ht⟩ : Fin n)]).length = t + 1
      rw [List.length_append, ih (Nat.le_of_succ_le ht)]
      simp
  have h_pref_get : ∀ (t : ℕ) (ht : t ≤ n) (k : ℕ) (hk : k < (prefList t ht).length),
      (prefList t ht)[k] = ⟨k, Nat.lt_of_lt_of_le (by rw [h_pref_len t ht] at hk; exact hk) ht⟩ := by
    intro t
    induction t with
    | zero =>
      intro ht k hk
      rw [h_pref_len 0 ht] at hk
      omega
    | succ t ih =>
      intro ht k hk
      have hk_lt : k < t + 1 := by rw [h_pref_len (t + 1) ht] at hk; exact hk
      change (prefList t (Nat.le_of_succ_le ht) ++ [(⟨t, ht⟩ : Fin n)])[k] = _
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk_lt with hlt | heq
      · have hlt_len : k < (prefList t (Nat.le_of_succ_le ht)).length := by
          rw [h_pref_len]; exact hlt
        rw [List.getElem_append_left hlt_len, ih (Nat.le_of_succ_le ht) k hlt_len]
      · subst k
        have hge_len : (prefList t (Nat.le_of_succ_le ht)).length ≤ t := by
          rw [h_pref_len]
        simp [List.getElem_append_right hge_len, h_pref_len]
  have h_pref_n : prefList n (le_refl n) = List.finRange n := by
    refine List.ext_getElem ?_ (fun k hk1 hk2 => ?_)
    · rw [h_pref_len, List.length_finRange]
    · rw [h_pref_get n (le_refl n) k hk1, List.getElem_finRange]
      ext; simp
  have h_pool_sum_eq : ∀ L : Finset (Fin n),
      let starters := (Finset.univ : Finset (Fin n)).filter
        (fun g : Fin n => g ∉ L ∧ ∀ x : Fin n, x.1 + 1 = g.1 → x ∈ L)
      (∑ i : Fin n, disposalEnvelope (v i) (frozenRoutingPools hn v L i)) = (starters.card : ℝ) := by
    intro L starters
    let r : ℕ → ℕ := fun t => (L.filter (fun x : Fin n => x.1 < t)).card
    have hr_le : ∀ t : ℕ, r t ≤ t := by
      intro t
      dsimp [r]
      have h_inj : ∀ a ∈ L.filter (fun x : Fin n => x.1 < t),
          ∀ b ∈ L.filter (fun x : Fin n => x.1 < t), a.1 = b.1 → a = b :=
        fun a _ b _ hab => Fin.ext hab
      have h_sub : (L.filter (fun x : Fin n => x.1 < t)).image Fin.val ⊆ Finset.range t := by
        intro m hm
        rcases Finset.mem_image.mp hm with ⟨x, hx, rfl⟩
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
      calc
        (L.filter (fun x : Fin n => x.1 < t)).card
          = ((L.filter (fun x : Fin n => x.1 < t)).image Fin.val).card :=
            (Finset.card_image_of_injOn h_inj).symm
        _ ≤ (Finset.range t).card := Finset.card_le_card h_sub
        _ = t := Finset.card_range t
    have hr_zero : r 0 = 0 := by simp [r]
    have hr_step : ∀ (t : ℕ) (ht : t + 1 ≤ n),
        r (t + 1) = if (⟨t, ht⟩ : Fin n) ∈ L then r t + 1 else r t := by
      intro t ht
      by_cases hgt : (⟨t, ht⟩ : Fin n) ∈ L
      · rw [if_pos hgt]
        have h_eq : L.filter (fun x : Fin n => x.1 < t + 1) =
            insert (⟨t, ht⟩ : Fin n) (L.filter (fun x : Fin n => x.1 < t)) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hxL, hxlt⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hxlt with hlt | heq
            · exact Or.inr ⟨hxL, hlt⟩
            · exact Or.inl (Fin.ext heq)
          · rintro (rfl | ⟨hxL, hlt⟩)
            · exact ⟨hgt, Nat.lt_succ_self t⟩
            · exact ⟨hxL, Nat.lt_succ_of_lt hlt⟩
        have hnot : (⟨t, ht⟩ : Fin n) ∉ L.filter (fun x : Fin n => x.1 < t) := by simp
        dsimp [r]
        rw [h_eq, Finset.card_insert_of_notMem hnot]
      · rw [if_neg hgt]
        have h_eq : L.filter (fun x : Fin n => x.1 < t + 1) =
            L.filter (fun x : Fin n => x.1 < t) := by
          ext x
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hxL, hxlt⟩
            refine ⟨hxL, ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hxlt with hlt | heq
            · exact hlt
            · exfalso; exact hgt ((Fin.ext heq : x = (⟨t, ht⟩ : Fin n)) ▸ hxL)
          · rintro ⟨hxL, hlt⟩
            exact ⟨hxL, Nat.lt_succ_of_lt hlt⟩
        dsimp [r]
        rw [h_eq]
    let stateAt : ∀ (t : ℕ), t ≤ n → (Fin n → Finset (Fin n)) × (Fin n → Finset (Fin n)) :=
      fun t ht => (prefList t ht).foldl (frozenRouteStep hn v L) (fun _ => ∅, fun _ => ∅)
    have h_inv : ∀ (t : ℕ) (ht : t ≤ n),
        (∀ i : Fin n, ((stateAt t ht).1 i).Nonempty ↔ i.1 < r t) ∧
        (∀ i : Fin n, (stateAt t ht).2 i =
          (Finset.univ : Finset (Fin n)).filter (fun g => g.1 < t ∧ g ∉ L ∧ r g.1 = i.1)) := by
      intro t
      induction t with
      | zero =>
        intro ht
        refine ⟨fun i => ?_, fun i => ?_⟩
        · simp [stateAt, prefList, hr_zero]
        · ext g; simp [stateAt, prefList]
      | succ t ih =>
        intro ht
        obtain ⟨ihB, ihR⟩ := ih (Nat.le_of_succ_le ht)
        let st := stateAt t (Nat.le_of_succ_le ht)
        let gt : Fin n := ⟨t, ht⟩
        have h_fold : stateAt (t + 1) ht = frozenRouteStep hn v L st gt := by
          dsimp [stateAt]
          change (prefList t (Nat.le_of_succ_le ht) ++ [gt]).foldl (frozenRouteStep hn v L) _ = _
          rw [List.foldl_append]
          rfl
        let marg : Fin n → ℝ := fun i =>
          disposalEnvelope (v i) (insert gt (st.1 i)) - disposalEnvelope (v i) (st.1 i)
        have h_marg_val : ∀ i : Fin n, marg i = if i.1 < r t then 0 else 1 := by
          intro i
          dsimp [marg]
          have h_ins_env : disposalEnvelope (v i) (insert gt (st.1 i)) = 1 := by
            rw [h_env i]
            have hpos : 1 ≤ (insert gt (st.1 i)).card :=
              Finset.card_pos.mpr ⟨gt, Finset.mem_insert_self _ _⟩
            have : min (insert gt (st.1 i)).card 1 = 1 := Nat.min_eq_right hpos
            exact_mod_cast this
          rw [h_ins_env]
          by_cases hlt : i.1 < r t
          · simp only [hlt, ↓reduceIte]
            have hne : (st.1 i).Nonempty := (ihB i).mpr hlt
            have h_bi : disposalEnvelope (v i) (st.1 i) = 1 := by
              rw [h_env i]
              have : min (st.1 i).card 1 = 1 := Nat.min_eq_right (Finset.card_pos.mpr hne)
              exact_mod_cast this
            linarith
          · simp only [hlt, ↓reduceIte]
            have hemp : st.1 i = ∅ := Finset.not_nonempty_iff_eq_empty.mp (mt (ihB i).mp hlt)
            rw [hemp, h_env i]
            simp
        have hrt_lt : r t < n := Nat.lt_of_le_of_lt (hr_le t) ht
        let i0 : Fin n := ⟨r t, hrt_lt⟩
        have h_i0_marg : marg i0 = 1 := by
          rw [h_marg_val i0]
          simp [i0]
        let best := (Finset.univ : Finset (Fin n)).sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ marg
        have h_best : best = 1 := by
          refine le_antisymm (Finset.sup'_le _ _ (fun i _ => ?_)) ?_
          · rw [h_marg_val i]; split_ifs <;> norm_num
          · rw [← h_i0_marg]
            exact Finset.le_sup' marg (Finset.mem_univ i0)
        let optBidders := (Finset.univ : Finset (Fin n)).filter (fun i => marg i = best)
        have h_i0_opt : i0 ∈ optBidders :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ i0, h_i0_marg.trans h_best.symm⟩
        have h_opt_ne : optBidders.Nonempty := ⟨i0, h_i0_opt⟩
        have h_min_eq : optBidders.min' h_opt_ne = i0 := by
          refine le_antisymm (Finset.min'_le optBidders i0 h_i0_opt) ?_
          have hmem := Finset.min'_mem optBidders h_opt_ne
          have hm : marg (optBidders.min' h_opt_ne) = 1 :=
            (Finset.mem_filter.mp hmem).2.trans h_best
          rw [h_marg_val] at hm
          by_cases hlt : (optBidders.min' h_opt_ne).1 < r t
          · simp [hlt] at hm
          · exact Fin.le_def.mpr (Nat.not_lt.mp hlt)
        have h_step_simp : frozenRouteStep hn v L st gt =
            if gt ∈ L then (Function.update st.1 i0 (insert gt (st.1 i0)), st.2)
            else (st.1, Function.update st.2 i0 (insert gt (st.2 i0))) := by
          dsimp [frozenRouteStep]
          change (if gt ∈ L then
              (Function.update st.1 (if h : optBidders.Nonempty then optBidders.min' h else ⟨0, hn⟩)
                (insert gt (st.1 (if h : optBidders.Nonempty then optBidders.min' h else ⟨0, hn⟩))), st.2)
            else
              (st.1, Function.update st.2 (if h : optBidders.Nonempty then optBidders.min' h else ⟨0, hn⟩)
                (insert gt (st.2 (if h : optBidders.Nonempty then optBidders.min' h else ⟨0, hn⟩))))) = _
          rw [dif_pos h_opt_ne, h_min_eq]
        rw [h_fold, h_step_simp, hr_step t ht]
        by_cases hgt : (⟨t, ht⟩ : Fin n) ∈ L
        · have hgt' : gt ∈ L := hgt
          simp only [hgt, hgt', ↓reduceIte]
          refine ⟨fun i => ?_, fun i => ?_⟩
          · by_cases hi : i = i0
            · subst hi
              simp [i0]
            · have hival : i.1 ≠ r t := fun heq => hi (Fin.ext heq)
              dsimp only [st]
              simp only [Function.update_of_ne hi, ihB i]
              omega
          · dsimp only [st]
            rw [ihR i]
            ext g
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hlt, hgL, hrg⟩
              exact ⟨Nat.lt_succ_of_lt hlt, hgL, hrg⟩
            · rintro ⟨hlt1, hgL, hrg⟩
              refine ⟨?_, hgL, hrg⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp hlt1 with hlt | heq
              · exact hlt
              · exfalso; exact hgL ((Fin.ext heq : g = ⟨t, ht⟩) ▸ hgt)
        · have hgt' : gt ∉ L := hgt
          simp only [hgt, hgt', ↓reduceIte]
          refine ⟨fun i => ihB i, fun i => ?_⟩
          by_cases hi : i = i0
          · subst hi
            dsimp only [st]
            simp only [Function.update_self, ihR i0]
            ext g
            simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro (rfl | ⟨hlt, hgL, hrg⟩)
              · exact ⟨Nat.lt_succ_self t, hgt', rfl⟩
              · exact ⟨Nat.lt_succ_of_lt hlt, hgL, hrg⟩
            · rintro ⟨hlt1, hgL, hrg⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp hlt1 with hlt | heq
              · exact Or.inr ⟨hlt, hgL, hrg⟩
              · exact Or.inl (Fin.ext heq)
          · dsimp only [st]
            simp only [Function.update_of_ne hi, ihR i]
            have hival : r t ≠ i.1 := fun heq => hi (Fin.ext heq.symm)
            ext g
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hlt, hgL, hrg⟩
              exact ⟨Nat.lt_succ_of_lt hlt, hgL, hrg⟩
            · rintro ⟨hlt1, hgL, hrg⟩
              refine ⟨?_, hgL, hrg⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp hlt1 with hlt | heq
              · exact hlt
              · exfalso; exact hival (heq ▸ hrg)
    have h_pools_eq : ∀ i : Fin n,
        frozenRoutingPools hn v L i =
          (Finset.univ : Finset (Fin n)).filter (fun g => g ∉ L ∧ r g.1 = i.1) := by
      intro i
      unfold frozenRoutingPools
      rw [← h_pref_n]
      change (stateAt n (le_refl n)).2 i = _
      rw [(h_inv n (le_refl n)).2 i]
      ext g
      simp
    let nonempPools := (Finset.univ : Finset (Fin n)).filter
      (fun i => (frozenRoutingPools hn v L i).Nonempty)
    have h_sum_nonemp :
        (∑ i : Fin n, disposalEnvelope (v i) (frozenRoutingPools hn v L i)) =
          (nonempPools.card : ℝ) := by
      have h_each : ∀ i : Fin n,
          disposalEnvelope (v i) (frozenRoutingPools hn v L i) =
            if (frozenRoutingPools hn v L i).Nonempty then 1 else 0 := by
        intro i
        rw [h_env i]
        rcases (frozenRoutingPools hn v L i).eq_empty_or_nonempty with hemp | hne
        · simp [hemp]
        · simp only [hne, ↓reduceIte]
          have : min (frozenRoutingPools hn v L i).card 1 = 1 :=
            Nat.min_eq_right (Finset.card_pos.mpr hne)
          exact_mod_cast this
      rw [Finset.sum_congr rfl (fun i _ => h_each i), ← Finset.sum_filter]
      dsimp [nonempPools]
      simp
    have h_card_bij : nonempPools.card = starters.card := by
      refine Finset.card_bij
        (fun i hi => (frozenRoutingPools hn v L i).min' (Finset.mem_filter.mp hi).2)
        ?_ ?_ ?_
      · intro i hi
        dsimp only
        set g_star := (frozenRoutingPools hn v L i).min' (Finset.mem_filter.mp hi).2
        have hg_mem : g_star ∈ frozenRoutingPools hn v L i :=
          Finset.min'_mem _ (Finset.mem_filter.mp hi).2
        rw [h_pools_eq i] at hg_mem
        obtain ⟨hg_notL, hrg⟩ := (Finset.mem_filter.mp hg_mem).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg_notL, fun x hx => ?_⟩
        by_contra hx_notL
        have hr_eq : r x.1 = r g_star.1 := by
          dsimp [r]
          congr 1
          ext z
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hzL, hzlt⟩
            exact ⟨hzL, by omega⟩
          · rintro ⟨hzL, hzlt⟩
            refine ⟨hzL, ?_⟩
            have hle : z.1 ≤ x.1 := by omega
            rcases eq_or_lt_of_le hle with heq | hlt
            · exfalso; exact hx_notL ((Fin.ext heq : z = x) ▸ hzL)
            · exact hlt
        have hx_mem : x ∈ frozenRoutingPools hn v L i := by
          rw [h_pools_eq i]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx_notL, hr_eq.trans hrg⟩
        have hmin_le : g_star ≤ x :=
          Finset.min'_le (frozenRoutingPools hn v L i) x hx_mem
        have hval_le : g_star.1 ≤ x.1 := Fin.le_def.mp hmin_le
        omega
      · intro i₁ hi₁ i₂ hi₂ heq
        dsimp only at heq
        set m₁ := (frozenRoutingPools hn v L i₁).min' (Finset.mem_filter.mp hi₁).2
        set m₂ := (frozenRoutingPools hn v L i₂).min' (Finset.mem_filter.mp hi₂).2
        have hm₁ : m₁ ∈ (Finset.univ : Finset (Fin n)).filter (fun g => g ∉ L ∧ r g.1 = i₁.1) := by
          rw [← h_pools_eq i₁]
          exact Finset.min'_mem _ _
        have hm₂ : m₂ ∈ (Finset.univ : Finset (Fin n)).filter (fun g => g ∉ L ∧ r g.1 = i₂.1) := by
          rw [← h_pools_eq i₂]
          exact Finset.min'_mem _ _
        have heq' : m₁ = m₂ := heq
        rw [heq'] at hm₁
        have hr₁ := (Finset.mem_filter.mp hm₁).2.2
        have hr₂ := (Finset.mem_filter.mp hm₂).2.2
        exact Fin.ext (hr₁.symm.trans hr₂)
      · intro g hg
        obtain ⟨hg_notL, hg_pred⟩ := (Finset.mem_filter.mp hg).2
        have hrg_lt : r g.1 < n := Nat.lt_of_le_of_lt (hr_le g.1) g.2
        let i : Fin n := ⟨r g.1, hrg_lt⟩
        have hg_in_i : g ∈ frozenRoutingPools hn v L i := by
          rw [h_pools_eq i]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg_notL, rfl⟩
        have hi_mem : i ∈ nonempPools :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨g, hg_in_i⟩⟩
        refine ⟨i, hi_mem, ?_⟩
        dsimp only
        let m0 := (frozenRoutingPools hn v L i).min' (Finset.mem_filter.mp hi_mem).2
        have hm0_le : m0 ≤ g := Finset.min'_le _ g hg_in_i
        have hm0_in : m0 ∈ frozenRoutingPools hn v L i := Finset.min'_mem _ _
        rw [h_pools_eq i] at hm0_in
        have hrm0 : r m0.1 = r g.1 := (Finset.mem_filter.mp hm0_in).2.2
        rcases eq_or_lt_of_le hm0_le with heq | hlt
        · exact heq
        · exfalso
          have hlt_val : m0.1 < g.1 := Fin.lt_def.mp hlt
          let x : Fin n := ⟨g.1 - 1, by omega⟩
          have hxL : x ∈ L := hg_pred x (by dsimp [x]; omega)
          have h_ssub : L.filter (fun z : Fin n => z.1 < m0.1) ⊂
              L.filter (fun z : Fin n => z.1 < g.1) := by
            rw [Finset.ssubset_iff_of_subset (fun z hz => by
              obtain ⟨hzL, hzlt⟩ := Finset.mem_filter.mp hz
              exact Finset.mem_filter.mpr ⟨hzL, lt_trans hzlt hlt_val⟩)]
            refine ⟨x, Finset.mem_filter.mpr ⟨hxL, by dsimp [x]; omega⟩, ?_⟩
            simp only [Finset.mem_filter, not_and]
            intro _; dsimp [x]; omega
          have hcard_lt : r m0.1 < r g.1 := Finset.card_lt_card h_ssub
          omega
    rw [h_sum_nonemp, h_card_bij]
  have h_pow_sum : ∀ U : Finset (Fin n),
      ∑ B ∈ U.powerset, lam ^ B.card * (1 - lam) ^ (U.card - B.card) = 1 := by
    intro U
    rw [Finset.sum_powerset]
    have h_in : ∀ k ∈ Finset.range (U.card + 1),
        ∑ B ∈ Finset.powersetCard k U, lam ^ B.card * (1 - lam) ^ (U.card - B.card) =
          lam ^ k * (1 - lam) ^ (U.card - k) * (U.card.choose k : ℝ) := by
      intro k _
      have hc : ∑ B ∈ Finset.powersetCard k U, lam ^ B.card * (1 - lam) ^ (U.card - B.card) =
          ∑ _B ∈ Finset.powersetCard k U, lam ^ k * (1 - lam) ^ (U.card - k) :=
        Finset.sum_congr rfl (fun B hB => by rw [(Finset.mem_powersetCard.mp hB).2])
      rw [hc, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, mul_comm]
    rw [Finset.sum_congr rfl h_in, ← add_pow]
    ring
  have h_bern_event : ∀ (A_in A_out : Finset (Fin n)), Disjoint A_in A_out →
      ∑ L ∈ (Finset.univ : Finset (Finset (Fin n))).filter
          (fun L => A_in ⊆ L ∧ Disjoint L A_out), bernProb L =
        lam ^ A_in.card * (1 - lam) ^ A_out.card := by
    intro A_in A_out hdisj
    let U := (Finset.univ : Finset (Fin n)) \ (A_in ∪ A_out)
    have h_card_union : (A_in ∪ A_out).card = A_in.card + A_out.card :=
      Finset.card_union_of_disjoint hdisj
    have h_union_le : A_in.card + A_out.card ≤ n := by
      rw [← h_card_union]
      exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
    have hU_card : U.card = n - (A_in.card + A_out.card) := by
      dsimp [U]
      rw [Finset.card_sdiff, Finset.inter_univ, h_card_union, Finset.card_univ, Fintype.card_fin]
    have h_bij : ∑ B ∈ U.powerset, bernProb (A_in ∪ B) =
        ∑ L ∈ (Finset.univ : Finset (Finset (Fin n))).filter
          (fun L => A_in ⊆ L ∧ Disjoint L A_out), bernProb L := by
      refine Finset.sum_bij (fun B _ => A_in ∪ B) ?_ ?_ ?_ ?_
      · intro B hB
        have hBU : B ⊆ U := Finset.mem_powerset.mp hB
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.subset_union_left, ?_⟩
        rw [Finset.disjoint_union_left]
        refine ⟨hdisj, Finset.disjoint_left.mpr (fun x hxB hxOut => ?_)⟩
        have hxU := hBU hxB
        exact (Finset.mem_sdiff.mp hxU).2 (Finset.mem_union_right _ hxOut)
      · intro B₁ hB₁ B₂ hB₂ heq
        have hd₁ : Disjoint A_in B₁ := Finset.disjoint_left.mpr (fun x hxIn hxB₁ =>
          (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hB₁ hxB₁)).2 (Finset.mem_union_left _ hxIn))
        have hd₂ : Disjoint A_in B₂ := Finset.disjoint_left.mpr (fun x hxIn hxB₂ =>
          (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hB₂ hxB₂)).2 (Finset.mem_union_left _ hxIn))
        have hs := congrArg (fun S => S \ A_in) heq
        simpa [Finset.union_sdiff_cancel_left hd₁, Finset.union_sdiff_cancel_left hd₂] using hs
      · intro L hL
        obtain ⟨hInL, hDisjOut⟩ := (Finset.mem_filter.mp hL).2
        refine ⟨L \ A_in, Finset.mem_powerset.mpr (fun x hx => ?_), Finset.union_sdiff_of_subset hInL⟩
        obtain ⟨hxL, hxNotIn⟩ := Finset.mem_sdiff.mp hx
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, fun hxUn => ?_⟩
        rcases Finset.mem_union.mp hxUn with hxIn | hxOut
        · exact hxNotIn hxIn
        · exact Finset.disjoint_left.mp hDisjOut hxL hxOut
      · intro _ _; rfl
    rw [← h_bij]
    have h_fac : ∀ B ∈ U.powerset,
        bernProb (A_in ∪ B) =
          (lam ^ A_in.card * (1 - lam) ^ A_out.card) *
            (lam ^ B.card * (1 - lam) ^ (U.card - B.card)) := by
      intro B hB
      have hBU : B ⊆ U := Finset.mem_powerset.mp hB
      have hdB : Disjoint A_in B := Finset.disjoint_left.mpr (fun x hxIn hxB =>
        (Finset.mem_sdiff.mp (hBU hxB)).2 (Finset.mem_union_left _ hxIn))
      have hB_le : B.card ≤ U.card := Finset.card_le_card hBU
      have hcard_un : (A_in ∪ B).card = A_in.card + B.card := Finset.card_union_of_disjoint hdB
      have hcard_rem : n - (A_in.card + B.card) = A_out.card + (U.card - B.card) := by omega
      dsimp [bernProb]
      rw [hcard_un, hcard_rem, pow_add, pow_add]
      ring
    rw [Finset.sum_congr rfl h_fac, ← Finset.mul_sum, h_pow_sum U, mul_one]
  have h_poolVal_exact : poolVal =
      (lam * (1 - lam) + (1 - lam) ^ 2 / (n : ℝ)) * optWelfare v := by
    let isStarter : Finset (Fin n) → Fin n → Prop :=
      fun L g => g ∉ L ∧ ∀ x : Fin n, x.1 + 1 = g.1 → x ∈ L
    have h_pv1 : poolVal =
        ∑ g : Fin n, ∑ L ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun L => isStarter L g),
          bernProb L := by
      calc
        poolVal
          = ∑ L : Finset (Fin n),
              bernProb L * (((Finset.univ : Finset (Fin n)).filter (fun g => isStarter L g)).card : ℝ) := by
            dsimp [poolVal]
            exact Finset.sum_congr rfl (fun L _ => by rw [h_pool_sum_eq L])
        _ = ∑ L : Finset (Fin n), ∑ g : Fin n, (if isStarter L g then bernProb L else 0) := by
            refine Finset.sum_congr rfl (fun L _ => ?_)
            have hc : (((Finset.univ : Finset (Fin n)).filter (fun g => isStarter L g)).card : ℝ) =
                ∑ g : Fin n, (if isStarter L g then (1 : ℝ) else 0) := by
              rw [← Finset.sum_filter]; simp
            rw [hc, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun g _ => ?_)
            split_ifs <;> ring
        _ = ∑ g : Fin n, ∑ L : Finset (Fin n), (if isStarter L g then bernProb L else 0) :=
            Finset.sum_comm
        _ = ∑ g : Fin n, ∑ L ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun L => isStarter L g),
              bernProb L := by
            refine Finset.sum_congr rfl (fun g _ => ?_)
            rw [← Finset.sum_filter]
    let g0 : Fin n := ⟨0, hn⟩
    have h_g0 : ∑ L ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun L => isStarter L g0),
        bernProb L = 1 - lam := by
      have h_filt : (Finset.univ : Finset (Finset (Fin n))).filter (fun L => isStarter L g0) =
          (Finset.univ : Finset (Finset (Fin n))).filter (fun L => ∅ ⊆ L ∧ Disjoint L {g0}) := by
        ext L
        simp [isStarter, g0]
      rw [h_filt, h_bern_event ∅ {g0} (Finset.disjoint_empty_left _)]
      simp
    have h_g_pos : ∀ g ∈ (Finset.univ : Finset (Fin n)).erase g0,
        ∑ L ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun L => isStarter L g),
          bernProb L = lam * (1 - lam) := by
      intro g hg
      have hg_ne : g ≠ g0 := (Finset.mem_erase.mp hg).1
      have hg_val_pos : 1 ≤ g.1 := by
        by_contra h0
        exact hg_ne (Fin.ext (by dsimp [g0]; omega))
      let xp : Fin n := ⟨g.1 - 1, by omega⟩
      have hxp_ne : xp ≠ g := fun heq => by
        have := congrArg Fin.val heq; dsimp [xp] at this; omega
      have h_filt : (Finset.univ : Finset (Finset (Fin n))).filter (fun L => isStarter L g) =
          (Finset.univ : Finset (Finset (Fin n))).filter (fun L => {xp} ⊆ L ∧ Disjoint L {g}) := by
        ext L
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, isStarter,
          Finset.singleton_subset_iff, Finset.disjoint_singleton_right]
        constructor
        · rintro ⟨hgL, hpred⟩
          exact ⟨hpred xp (by dsimp [xp]; omega), hgL⟩
        · rintro ⟨hxpL, hgL⟩
          refine ⟨hgL, fun x hx => ?_⟩
          have hxeq : x = xp := Fin.ext (by dsimp [xp]; omega)
          rwa [hxeq]
      rw [h_filt, h_bern_event {xp} {g} (Finset.disjoint_singleton.mpr hxp_ne)]
      simp
    rw [h_pv1, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ g0), h_g0,
        Finset.sum_congr rfl h_g_pos, Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ g0), Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, h_opt]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      simpa using (Nat.cast_sub hn : ((n - 1 : ℕ) : ℝ) = _)
    have hn_ne : (n : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    rw [hcast]
    field_simp
    ring
  have h_poolVal_ub : poolVal ≤ (1 / 4 + 1 / (n : ℝ)) * optWelfare v := by
    rw [h_poolVal_exact]
    have hopt_nn : 0 ≤ optWelfare v := by rw [h_opt]; positivity
    refine mul_le_mul_of_nonneg_right ?_ hopt_nn
    have h_q1 : lam * (1 - lam) ≤ 1 / 4 := by
      nlinarith [sq_nonneg (lam - 1 / 2)]
    have h_q2 : (1 - lam) ^ 2 ≤ 1 := by
      nlinarith
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have h_div : (1 - lam) ^ 2 / (n : ℝ) ≤ 1 / (n : ℝ) :=
      div_le_div_of_nonneg_right h_q2 (le_of_lt hn_pos)
    linarith
  have h_poolVal_lt : 9 ≤ n → poolVal < invE * optWelfare v := by
    intro hn9
    have hn9R : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn9
    have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
    have h_1n : 1 / (n : ℝ) ≤ 1 / 9 := one_div_le_one_div_of_le (by norm_num) hn9R
    have h_13_36 : 1 / 4 + 1 / (n : ℝ) ≤ 13 / 36 := by linarith
    have h_invE_pos : 0 < invE := Real.exp_pos (-1)
    have h_exp_prod : Real.exp 1 * invE = 1 := by
      dsimp [invE]; rw [← Real.exp_add]; norm_num
    have h_lt_invE : (13 : ℝ) / 36 < invE := by
      have he : 13 * Real.exp 1 < 36 := by linarith [Real.exp_one_lt_d9]
      have hmul := mul_lt_mul_of_pos_right he h_invE_pos
      have hprod : 13 * Real.exp 1 * invE = 13 := by
        calc 13 * Real.exp 1 * invE = 13 * (Real.exp 1 * invE) := by ring
        _ = 13 := by rw [h_exp_prod]; ring
      linarith
    have hopt_pos : 0 < optWelfare v := by rw [h_opt]; exact hn_pos
    calc
      poolVal ≤ (1 / 4 + 1 / (n : ℝ)) * optWelfare v := h_poolVal_ub
      _ ≤ (13 / 36) * optWelfare v := mul_le_mul_of_nonneg_right h_13_36 (le_of_lt hopt_pos)
      _ < invE * optWelfare v := mul_lt_mul_of_pos_right h_lt_invE hopt_pos
  exact ⟨h_gs, h_opt, h_env, h_poolVal_exact, h_poolVal_ub, h_poolVal_lt⟩


end Internal

/-- **Section 4.2 (`sec:routing`) — Non-Submodular Disposal Envelope of a Submodular Valuation**:
The 3-item directed-cut valuation (`0 ↔ 1, 2 → 0`) is finite, nonnegative, and submodular, yet its
disposal envelope satisfies `v̄({0}) = v̄({0, 1}) = v̄({0, 2}) = 1` and `v̄({0, 1, 2}) = 2`,
violating submodularity. -/
theorem rem_4_2_directed_cut_envelope_not_submodular :
    ∃ v : ItemValuation 3,
      IsFiniteValuation v ∧ IsNonnegValuation v ∧ IsSubmodularReal (realVal v) ∧
      disposalEnvelope v {0} = 1 ∧
      disposalEnvelope v {0, 1} = 1 ∧
      disposalEnvelope v {0, 2} = 1 ∧
      disposalEnvelope v {0, 1, 2} = 2 ∧
      ¬ IsSubmodularReal (disposalEnvelope v) :=
  Internal.thm_welfare_counterexamples_and_admission.1

/-- **Section 4.2 (`sec:routing`) — The Price of Freezing**:
For `n ≥ 1` items and `n` identical gross substitutes bidders with `v_i(S) = |S| - 3(|S| - 1)_+`,
`OPT = n`, `v̄_i(S) = min(|S|, 1)`, and for every sampling bias `λ ∈ [0, 1]` the expected total
envelope value of the frozen routing pools equals `(λ(1 - λ) + (1 - λ)^2 / n) OPT`, which is at
most `(1/4 + 1/n) OPT` and strictly below `OPT / e` for all `n ≥ 9`. -/
theorem rem_4_2_price_of_freezing
    (n : ℕ) (hn : 1 ≤ n) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    let v : Fin n → ItemValuation n := fun _ S =>
      (((S.card : ℝ) - 3 * ((S.card - 1 : ℕ) : ℝ) : ℝ) : WithBot ℝ)
    let bernProb : Finset (Fin n) → ℝ :=
      fun L => lam ^ L.card * (1 - lam) ^ (n - L.card)
    let poolVal : ℝ :=
      ∑ L : Finset (Fin n),
        bernProb L * (∑ i : Fin n, disposalEnvelope (v i) (frozenRoutingPools hn v L i))
    (∀ i : Fin n, IsGSValuation (v i)) ∧
    optWelfare v = (n : ℝ) ∧
    (∀ i S, disposalEnvelope (v i) S = (min S.card 1 : ℝ)) ∧
    poolVal = (lam * (1 - lam) + (1 - lam) ^ 2 / (n : ℝ)) * optWelfare v ∧
    poolVal ≤ (1 / 4 + 1 / (n : ℝ)) * optWelfare v ∧
    (9 ≤ n → poolVal < invE * optWelfare v) :=
  Internal.thm_welfare_counterexamples_and_admission.2.1 n hn lam h0 h1

/-- **Section 4.3 (`sec:towards`) — Prefix-Optimal Allocation Feasibility & Locality**:
Whenever `v_i(∅) = 0` for all `i`, `gsPrefixOptAlloc v S` is a feasible allocation of `S` achieving
`W(S)` and depending only on queries `v_i(T)` for subsets `T ⊆ S`. -/
theorem gsPrefixOptAlloc_spec
    {n m : ℕ} (v : Fin m → ItemValuation n)
    (h0 : ∀ i, v i ∅ = ((0 : ℝ) : WithBot ℝ)) (S : Finset (Fin n)) :
    IsAllocOf S (gsPrefixOptAlloc v S) ∧
    allocWelfare v (gsPrefixOptAlloc v S) = ((optWelfareOn v S : ℝ) : WithBot ℝ) ∧
    (∀ v' : Fin m → ItemValuation n,
      (∀ i, ∀ T ⊆ S, v' i T = v i T) → gsPrefixOptAlloc v' S = gsPrefixOptAlloc v S) :=
  (Internal.thm_welfare_counterexamples_and_admission.2.2.1 v h0).1 S

/-- **Section 4.3 (`sec:towards`, `eq:internal`) — Prefix-Optimal Bundles Form Proposal Maps**:
Whenever `v_i(∅) = 0` for all `i`, `S ↦ X^S_i` is a valid proposal map for `v_i` (and satisfies
`|X^S_i| ≤ 1` when `v_i` is unit-demand). -/
theorem gsPrefixOptAlloc_proposal
    {n m : ℕ} (v : Fin m → ItemValuation n)
    (h0 : ∀ i, v i ∅ = ((0 : ℝ) : WithBot ℝ)) :
    (∀ i : Fin m, IsProposalMap (v i) (fun S => gsPrefixOptAlloc v S i)) ∧
    (∀ i : Fin m, IsUnitDemandValuation (v i) →
      ∀ S : Finset (Fin n), (gsPrefixOptAlloc v S i).card ≤ 1) :=
  (Internal.thm_welfare_counterexamples_and_admission.2.2.1 v h0).2

/-- **Theorem 4.5 (`thm:admission`, Reduction to conditional admission)**:
For `1 ≤ s < n`, gross substitutes valuations `v_1, ..., v_m`, and per-bidder online admission
modules `mod_i` satisfying `HasConditionalAdmission s (v_i) (S ↦ X^S_i)`, running the modules side
by side defines a non-clairvoyant `OnlineWelfareAlg n m` maintaining disjoint prefix allocations
and achieving `E[∑_i v_i(A_i)] ≥ c_n(s) OPT`. -/
theorem thm_4_5_admission
    {n m s : ℕ} (v : Fin m → ItemValuation n) (mod : Fin m → OnlineAdmissionModule n)
    (hs1 : 1 ≤ s) (hsn : s < n)
    (hv : ∀ i : Fin m, IsGSValuation (v i))
    (hmod : ∀ i : Fin m, HasConditionalAdmission s (v i) (fun S => gsPrefixOptAlloc v S i) (mod i)) :
    ∃ alg : OnlineWelfareAlg n m,
      (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
        IsAllocOf (runDetWelfareSteps (alg.det ω) v π k hk).1.toFinset
          (runDetWelfareSteps (alg.det ω) v π k hk).2) ∧
      (((secretaryCutoffConst n s * optWelfare v : ℝ) : WithBot ℝ) ≤
        expectedWelfareVal alg v) :=
  Internal.thm_welfare_counterexamples_and_admission.2.2.2.1 v mod hs1 hsn hv hmod

/-- **`[KRTV13]` Unit-Demand Conditional Admission Module (`sec:towards`)**:
For any `1 ≤ s < n`, the deterministic first-accepted-offer module after cutoff `s` satisfies
`HasConditionalAdmission s v P` for every unit-demand valuation `v` and `≤ 1`-item proposal map `P`. -/
theorem krtv_unit_demand_module
    (n s : ℕ) (hs1 : 1 ≤ s) (hsn : s < n) :
    ∃ mod : OnlineAdmissionModule n,
      ∀ (v : ItemValuation n) (P : Finset (Fin n) → Finset (Fin n)),
        IsUnitDemandValuation v → IsProposalMap v P → (∀ S, (P S).card ≤ 1) →
          HasConditionalAdmission s v P mod :=
  Internal.thm_welfare_counterexamples_and_admission.2.2.2.2.1 n s hs1 hsn

/-- **`[KRTV13]` Online Welfare for Unit-Demand Bidders (`sec:towards`)**:
For every `n, m`, there exists a non-clairvoyant `OnlineWelfareAlg n m` achieving expected welfare
at least `OPT / e` for all unit-demand bidder profiles `v_1, ..., v_m`. -/
theorem krtv_unit_demand_welfare (n m : ℕ) :
    ∃ alg : OnlineWelfareAlg n m,
      ∀ v : Fin m → ItemValuation n, (∀ i, IsUnitDemandValuation (v i)) →
        (((invE * optWelfare v : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg v) :=
  Internal.thm_welfare_counterexamples_and_admission.2.2.2.2.2.1 n m

/-- **Open Problem 1.1 (`q:welfare`) Reduction via Theorem 4.5 & Lemma D.1**:
If for every `n ≥ 2` and `1 ≤ s < n` there exists a non-clairvoyant admission module satisfying
`HasConditionalAdmission s v P` for every gross substitutes valuation `v` and proposal map `P`,
then for every `n, m` there exists a non-clairvoyant `OnlineWelfareAlg n m` achieving expected
welfare at least `OPT / e` across all signed gross substitutes valuations. -/
theorem open_problem_1_1_reduction
    (hadm : ∀ (n s : ℕ), 2 ≤ n → 1 ≤ s → s < n →
      ∃ mod : OnlineAdmissionModule n,
        ∀ (v : ItemValuation n) (P : Finset (Fin n) → Finset (Fin n)),
          IsGSValuation v → IsProposalMap v P → HasConditionalAdmission s v P mod)
    (n m : ℕ) :
    ∃ alg : OnlineWelfareAlg n m,
      ∀ v : Fin m → ItemValuation n, (∀ i, IsGSValuation (v i)) →
        (((invE * optWelfare v : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg v) :=
  Internal.thm_welfare_counterexamples_and_admission.2.2.2.2.2.2 hadm n m

end

end GrossSubstitutesWelfare
