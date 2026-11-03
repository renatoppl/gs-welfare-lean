import GrossSubstitutesWelfare.Defs
import GrossSubstitutesWelfare.Preliminaries.ExchangeAndDemand
import GrossSubstitutesWelfare.Preliminaries.SafeSupportAndCutoff

set_option maxHeartbeats 4000000
set_option linter.all false

/-!
# Appendix E.1 & `[ABHM26]` (`arXiv:2609.19118`, Section 4): Subspace-Load Module & Arbitrary Proposals

Self-contained formalization of Section 4 of Abdi, Banihashem, Hajiaghayi, and Mittal (`[ABHM26]`,
*On the Strong Matroid Secretary Conjecture and Beyond*, `arXiv:2609.19118`) and Proposition E.2
(`prop:linear-module`) of *Gross Substitutes Welfare in Random Order*:
- `abhm_arrived_span_iff` (`[ABHM26, Section 4.2]` & `Proposition E.2` proof): `β`-boundedness over
  all subspaces `U ≤ F^d` is equivalent to `β`-boundedness over arrived subspaces `U ≤ W(S)`.
- `abhm_hidden_directions_F2` (`[ABHM26, Section 4.2]`): Explicit separation on `U_{3, 4}(𝔽₂)`
  showing item-spanned flats `{W(X) : X ⊆ N}` do not suffice (`3/4` vs `1`).
- `abhm_lem_4_6_averaged_extension` (`[ABHM26, Lemma 4.6]`): Single-matroid averaged extension
  lemma for **any** linearly independent proposal set `B ⊆ S`.
- `abhm_prop_4_2_recursive_lp` (`[ABHM26, Definition 4.1 & Proposition 4.2]`): Feasibility and
  `(1 - s / |S|)`-boundedness of the recursive prefix program `(P_S)` using arrived vectors only.
- `prop_E_2_linear_module` (**Proposition E.2**, `prop:linear-module`, & `[ABHM26, Algorithm 1 &
  Lemma 4.7]`): Universal `RepresentedAdmissionModule` achieving exact conditional admission
  `a_k = s / (k - 1)` for every `g ∈ P(S)`.
- `abhm_thm_1_2_linear_matroid_secretary` (`[ABHM26, Proposition 4.3 & Theorem 1.2]`): Strong
  Matroid Secretary Conjecture for Linear Matroids (`= c_n(s)` exact inclusion probability on every
  element of the optimal basis, and `≥ 1 / e` elementwise & expected weight across all `n`).
-/

namespace GrossSubstitutesWelfare

open Classical MeasureTheory

noncomputable section

namespace ABHMInternal

/-- **`[ABHM26]` (`arXiv:2609.19118`, Section 4) & Proposition E.2 (`prop:linear-module`)**:
1. **Arrived-span reduction & hidden directions (`[ABHM26, Section 4.2]`, `Proposition E.2` proof)**:
   For `β ≥ 0` and any law `μ` on independent subsets of `S`, `β`-boundedness over all subspaces
   `U ≤ F^d` is equivalent to `β`-boundedness over arrived subspaces `U ≤ W(S)` alone; yet on
   `U_{3, 4}(𝔽₂)` checking only item-spanned flats `{W(X) : X ⊆ N}` fails (`3/4` vs `1`).
2. **`[ABHM26, Lemma 4.6]` (Averaged extension lemma for arbitrary independent proposals)**:
   For any finite field `F`, `|S| ≥ 1`, `0 ≤ β ≤ 1`, `0 ≤ a ≤ 1 - β`, `β`-bounded laws `μ_g` on
   `S - g`, and ANY linearly independent proposal set `B ⊆ S`, there exist transitions `q_g(A)`
   moving mass `a` for each `g ∈ B` to independent sets `A + g` such that the averaged law `μ_avg`
   is `(β + a / |S|)`-bounded across all subspaces `U ≤ F^d`.
3. **`[ABHM26, Definition 4.1 & Proposition 4.2]` (Feasibility & `(1 - s/|S|)`-boundedness)**:
   For every `1 ≤ s < n` and independent proposal map `P(S) ⊆ S`, there exists a family of laws
   `μ_S` (`|S| ≥ s`) that is `(1 - s / |S|)`-bounded and depends on `(u, P)` only through
   `{u_g : g ∈ S}` and `{P(T) : T ⊆ S}`.
4. **Proposition E.2 (`prop:linear-module`) & `[ABHM26, Algorithm 1 & Lemma 4.7]`**:
   There exists a universal `RepresentedAdmissionModule n F d` that rejects for `k ≤ s` or
   `g_k ∉ P(S_k)`, keeps `A_k` independent at every step, and achieves exact conditional admission
   `P[g_k accepted | S_k = S, g_k = g] = a_k = s / (k - 1)` for every `k > s`, `|S| = k`, `g ∈ P(S)`.
5. **`[ABHM26, Proposition 4.3 & Theorem 1.2]` (Strong Matroid Secretary for Linear Matroids)**:
   Specializing Proposition E.2 to `P(S) = D_{v_M}(S)` selects EVERY element `g ∈ D_{v_M}(N)` with
   exact probability `c_n(s)` (for `2 ≤ n, 1 ≤ s < n`), and achieves `≥ 1 / e` elementwise
   probability and expected weight across all `n`. -/
def abhmNormVec {n d : ℕ} {F : Type*} [Zero F]
    (S : Finset (Fin n)) (u : Fin n → (Fin d → F)) : Fin n → (Fin d → F) :=
  fun g => if g ∈ S then u g else 0

def abhmNormProp {n : ℕ}
    (S : Finset (Fin n)) (P : Finset (Fin n) → Finset (Fin n)) :
    Finset (Fin n) → Finset (Fin n) :=
  fun T => if T ⊆ S then P T else ∅

def abhmEmptyLaw {n : ℕ} : Finset (Fin n) → ℝ :=
  fun A => if A = ∅ then 1 else 0

def abhmRowTrans {n : ℕ}
    (μPrev : Finset (Fin n) → ℝ) (qRow : Finset (Fin n) → ℝ)
    (g : Fin n) (C : Finset (Fin n)) : ℝ :=
  μPrev C + (∑ A : Finset (Fin n), if insert g A = C then qRow A else 0) - qRow C

def abhmRowAvg {n : ℕ}
    (S : Finset (Fin n))
    (μSub : Fin n → Finset (Fin n) → ℝ)
    (q : Fin n → Finset (Fin n) → ℝ)
    (C : Finset (Fin n)) : ℝ :=
  (1 / (S.card : ℝ)) * ∑ g ∈ S, abhmRowTrans (μSub g) (q g) g C

def abhmStepSpec {n d : ℕ} {F : Type*} [Field F]
    (s : ℕ) (u : Fin n → (Fin d → F)) (S B : Finset (Fin n))
    (μSub : Fin n → Finset (Fin n) → ℝ)
    (q : Fin n → Finset (Fin n) → ℝ) : Prop :=
  (∀ g ∈ S, ∀ A, 0 ≤ q g A ∧ q g A ≤ μSub g A) ∧
  (∀ g ∈ S, ∀ A, q g A ≠ 0 →
    g ∈ B ∧ g ∉ A ∧ LinearIndependent F (fun x : (insert g A : Finset (Fin n)) => u x.1)) ∧
  (∀ g ∈ B, (∑ A, q g A) = admitRate s S.card) ∧
  IsSubspaceBetaBounded u S (loadBeta s S.card) (abhmRowAvg S μSub q)

def abhmProgAux {n d : ℕ} {F : Type*} [Field F] (s : ℕ) :
    ℕ → (Fin n → (Fin d → F)) → (Finset (Fin n) → Finset (Fin n)) →
    Finset (Fin n) → (Finset (Fin n) → ℝ) × (Fin n → Finset (Fin n) → ℝ)
  | 0, _, _, _ => (abhmEmptyLaw, fun _ _ => 0)
  | k + 1, u, P, S =>
      if k + 1 ≤ s then
        (abhmEmptyLaw, fun _ _ => 0)
      else
        let u' := abhmNormVec S u
        let P' := abhmNormProp S P
        let B := if P' S ⊆ S ∧ LinearIndependent F (fun g : P' S => u' g.1) then P' S else ∅
        let μSub : Fin n → Finset (Fin n) → ℝ :=
          fun g => (abhmProgAux s k u' P' (S.erase g)).1
        if h : ∃ q : Fin n → Finset (Fin n) → ℝ, abhmStepSpec s u' S B μSub q then
          let q := Classical.choose h
          (abhmRowAvg S μSub q, q)
        else
          (abhmEmptyLaw, fun _ _ => 0)

def abhmMuProg {n d : ℕ} (s : ℕ) (F : Type*) [Field F]
    (u : Fin n → (Fin d → F)) (P : Finset (Fin n) → Finset (Fin n))
    (S : Finset (Fin n)) : Finset (Fin n) → ℝ :=
  (abhmProgAux s S.card u P S).1

def abhmQProg {n d : ℕ} (s : ℕ) (F : Type*) [Field F]
    (u : Fin n → (Fin d → F)) (P : Finset (Fin n) → Finset (Fin n))
    (S : Finset (Fin n)) : Fin n → Finset (Fin n) → ℝ :=
  (abhmProgAux s S.card u P S).2

def abhmUnitIntervalMeasure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

def abhmSeedSpaceMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => abhmUnitIntervalMeasure)

def abhmLiftVecOracle {n d : ℕ} {F : Type*} [Zero F]
    (S : Finset (Fin n))
    (vecOracle : {g : Fin n // g ∈ S} → (Fin d → F)) :
    Fin n → (Fin d → F) :=
  fun g => if h : g ∈ S then vecOracle ⟨g, h⟩ else 0

def abhmLiftPropOracle {n : ℕ}
    (S : Finset (Fin n))
    (propOracle : {T : Finset (Fin n) // T ⊆ S} → Finset (Fin n)) :
    Finset (Fin n) → Finset (Fin n) :=
  fun T => if h : T ⊆ S then propOracle ⟨T, h⟩ else ∅

def abhmDetMod {n d : ℕ} (F : Type*) [Field F] (s : ℕ) (ω : Fin n → ℝ) :
    DetRepresentedAdmissionModule n F d where
  step prev x accepted propOracle vecOracle :=
    let S := insert x prev.toFinset
    if S.card ≤ s ∨ x ∉ propOracle ⟨S, Finset.Subset.refl S⟩ then
      false
    else
      let uLoc := abhmLiftVecOracle S vecOracle
      let PLoc := abhmLiftPropOracle S propOracle
      let denom := abhmMuProg s F uLoc PLoc (S.erase x) accepted
      let num := abhmQProg s F uLoc PLoc S x accepted
      if denom ≤ 0 then
        false
      else
        decide (0 ≤ ω x ∧ ω x < num / denom)

theorem thm_abhm26_and_linear_module :
    -- (1a) Arrived vectors suffice: U ≤ F^d ↔ U ≤ W(S)
    (∀ {n d : ℕ} {F : Type} [Field F]
        (u : Fin n → (Fin d → F)) (S : Finset (Fin n)) (β : ℝ) (μ : Finset (Fin n) → ℝ),
      0 ≤ β → IsIndepSetLaw u S μ →
        (IsSubspaceBetaBounded u S β μ ↔
          ∀ U : Submodule F (Fin d → F), U ≤ matroidSpan u S →
            (∑ A : Finset (Fin n), μ A * (subspaceLoad u U A : ℝ)) ≤
              β * (Module.finrank F U : ℝ))) ∧
    -- (1b) [ABHM26, Section 4.2]: Hidden-direction separation on U_{3,4}(F_2)
    (∃ (u : Fin 4 → (Fin 3 → ZMod 2)) (μ : Finset (Fin 4) → ℝ),
      (∀ X : Finset (Fin 4), LinearIndependent (ZMod 2) (fun g : X => u g.1) ↔ X.card ≤ 3) ∧
      IsIndepSetLaw u Finset.univ μ ∧
      (∀ X : Finset (Fin 4),
        (∑ A, μ A * (subspaceLoad u (matroidSpan u X) A : ℝ)) ≤
          (3 / 4 : ℝ) * (Module.finrank (ZMod 2) (matroidSpan u X) : ℝ)) ∧
      ¬ ∃ β : ℝ, β < 1 ∧ IsSubspaceBetaBounded u Finset.univ β μ) ∧
    -- (2) [ABHM26, Lemma 4.6]: Averaged extension lemma for arbitrary independent B ⊆ S
    (∀ {n d : ℕ} {F : Type} [Field F] [Fintype F]
        (u : Fin n → (Fin d → F)) (S B : Finset (Fin n)) (β a : ℝ)
        (μ_g : Fin n → Finset (Fin n) → ℝ),
      1 ≤ S.card → B ⊆ S → 0 ≤ β → β ≤ 1 → 0 ≤ a → a ≤ 1 - β →
      LinearIndependent F (fun g : B => u g.1) →
      (∀ g ∈ S, IsIndepSetLaw u (S.erase g) (μ_g g) ∧ IsSubspaceBetaBounded u S β (μ_g g)) →
        ∃ q : Fin n → Finset (Fin n) → ℝ,
          (∀ g ∈ S, ∀ A, 0 ≤ q g A ∧ q g A ≤ μ_g g A) ∧
          (∀ g ∈ S, ∀ A, q g A ≠ 0 →
            g ∈ B ∧ g ∉ A ∧ LinearIndependent F (fun x : (insert g A : Finset (Fin n)) => u x.1)) ∧
          (∀ g ∈ B, (∑ A, q g A) = a) ∧
          let ν : Fin n → Finset (Fin n) → ℝ := fun g C =>
            μ_g g C + (∑ A, if insert g A = C then q g A else 0) - q g C
          let μ_avg : Finset (Fin n) → ℝ := fun C => (1 / (S.card : ℝ)) * ∑ g ∈ S, ν g C
          IsSubspaceBetaBounded u S (β + a / (S.card : ℝ)) μ_avg) ∧
    -- (3) [ABHM26, Proposition 4.2]: Prefix LP feasibility & locality on arrived sets
    (∀ (n d s : ℕ) (F : Type) [Field F] [Fintype F] [DecidableEq F],
      1 ≤ s → s ≤ n →
        ∃ μ_prog :
            (Fin n → (Fin d → F)) → (Finset (Fin n) → Finset (Fin n)) →
            Finset (Fin n) → Finset (Fin n) → ℝ,
          (∀ (u : Fin n → (Fin d → F)) (P : Finset (Fin n) → Finset (Fin n)),
            (∀ T : Finset (Fin n), P T ⊆ T ∧ LinearIndependent F (fun g : P T => u g.1)) →
            ∀ S : Finset (Fin n), s ≤ S.card →
              IsSubspaceBetaBounded u S (loadBeta s S.card) (μ_prog u P S)) ∧
          (∀ (u u' : Fin n → (Fin d → F)) (P P' : Finset (Fin n) → Finset (Fin n))
              (S : Finset (Fin n)),
            (∀ g ∈ S, u g = u' g) → (∀ T ⊆ S, P T = P' T) →
              μ_prog u P S = μ_prog u' P' S)) ∧
    -- (4) Proposition E.2 (prop:linear-module) & [ABHM26, Lemma 4.7]
    (∀ (n d s : ℕ) (F : Type) [Field F] [Fintype F] [DecidableEq F],
      2 ≤ n → 1 ≤ s → s < n →
        ∃ mod : RepresentedAdmissionModule n F d,
          ∀ (M : Matroid (Fin n)) (u : Fin n → (Fin d → F))
            (P : Finset (Fin n) → Finset (Fin n)),
            IsLinearMatroidRep F M u →
            (∀ T : Finset (Fin n), P T ⊆ T ∧ M.Indep (P T : Set (Fin n))) →
              -- Rejection when k + 1 ≤ s or arriving item ∉ P(S_{k+1})
              (∀ (ω : mod.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k + 1 ≤ n),
                let st := runDetRepAdmissionSteps (mod.det ω) P u π k (Nat.le_of_succ_le hk)
                let x := π ⟨k, hk⟩
                (k < s ∨ x ∉ P (insert x st.1.toFinset)) →
                  (mod.det ω).step st.1 x st.2 (fun ⟨T, _⟩ => P T) (fun ⟨g, _⟩ => u g) = false) ∧
              -- Accepted set is independent in M and ⊆ arrived items at every step
              (∀ (ω : mod.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
                let st := runDetRepAdmissionSteps (mod.det ω) P u π k hk
                st.2 ⊆ st.1.toFinset ∧ M.Indep (st.2 : Set (Fin n))) ∧
              -- Exact conditional admission = a_k = s / (k - 1) for every g ∈ P(S)
              (∀ (k : ℕ) (hk : k + 1 ≤ n), s ≤ k →
                ∀ (S : Finset (Fin n)) (g : Fin n),
                  S.card = k + 1 → g ∈ P S →
                    let ev := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
                      (fun π => arrivalPrefixSet π (k + 1) = S ∧ π ⟨k, hk⟩ = g)
                    ∑ π ∈ ev, mod.seedMeasure.real
                      {ω | g ∈ (runDetRepAdmissionSteps (mod.det ω) P u π (k + 1) hk).2} =
                      admitRate s (k + 1) * (ev.card : ℝ))) ∧
    -- (5) [ABHM26, Proposition 4.3 & Theorem 1.2]: Strong Matroid Secretary for Linear Matroids
    (∀ (n d s : ℕ) (F : Type) [Field F] [Fintype F] [DecidableEq F],
      2 ≤ n → 1 ≤ s → s < n →
        ∃ mod : RepresentedAdmissionModule n F d,
          ∀ (M : Matroid (Fin n)) (w : Fin n → ℝ) (u : Fin n → (Fin d → F)),
            IsLinearMatroidRep F M u →
              let v := weightedMatroidVal M w
              let P := canonicalDemand v
              (∀ (ω : mod.Seed) (π : Equiv.Perm (Fin n)),
                M.Indep (runDetRepAdmission (mod.det ω) P u π : Set (Fin n))) ∧
              (∀ g ∈ P Finset.univ,
                (1 / (Nat.factorial n : ℝ)) *
                  ∑ π : Equiv.Perm (Fin n),
                    mod.seedMeasure.real {ω | g ∈ runDetRepAdmission (mod.det ω) P u π} =
                  secretaryCutoffConst n s)) :=
by
  have h_part1a : ∀ {n d : ℕ} {F : Type} [Field F]
      (u : Fin n → (Fin d → F)) (S : Finset (Fin n)) (β : ℝ) (μ : Finset (Fin n) → ℝ),
      0 ≤ β → IsIndepSetLaw u S μ →
        (IsSubspaceBetaBounded u S β μ ↔
          ∀ U : Submodule F (Fin d → F), U ≤ matroidSpan u S →
            (∑ A : Finset (Fin n), μ A * (subspaceLoad u U A : ℝ)) ≤
              β * (Module.finrank F U : ℝ)) := by
    intro n d F _ u S β μ hβ0 hlaw
    constructor
    · rintro ⟨_, hbound⟩ U _
      exact hbound U
    · intro harr
      refine ⟨hlaw, fun U => ?_⟩
      let W : Submodule F (Fin d → F) := U ⊓ matroidSpan u S
      have h_sum_eq : (∑ A : Finset (Fin n), μ A * (subspaceLoad u U A : ℝ)) =
          ∑ A : Finset (Fin n), μ A * (subspaceLoad u W A : ℝ) := by
        refine Finset.sum_congr rfl fun A _ => ?_
        by_cases hμA : μ A = 0
        · simp [hμA]
        · have hAS : A ⊆ S := (hlaw.2.1 A hμA).1
          have hspan : matroidSpan u A ≤ matroidSpan u S :=
            Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr hAS))
          have hinf : matroidSpan u A ⊓ U = matroidSpan u A ⊓ W := by
            dsimp only [W]
            rw [← inf_assoc, inf_comm (matroidSpan u A) U, inf_assoc,
              inf_of_le_left hspan, inf_comm]
          have hload : subspaceLoad u U A = subspaceLoad u W A :=
            congr_arg (fun M : Submodule F (Fin d → F) => Module.finrank F M) hinf
          rw [hload]
      have hdim : Module.finrank F W ≤ Module.finrank F U := Submodule.finrank_mono inf_le_left
      calc
        (∑ A, μ A * (subspaceLoad u U A : ℝ))
            = ∑ A, μ A * (subspaceLoad u W A : ℝ) := h_sum_eq
        _ ≤ β * (Module.finrank F W : ℝ) := harr W inf_le_right
        _ ≤ β * (Module.finrank F U : ℝ) :=
            mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hdim) hβ0
  have h_part1b : ∃ (u : Fin 4 → (Fin 3 → ZMod 2)) (μ : Finset (Fin 4) → ℝ),
      (∀ X : Finset (Fin 4), LinearIndependent (ZMod 2) (fun g : X => u g.1) ↔ X.card ≤ 3) ∧
      IsIndepSetLaw u Finset.univ μ ∧
      (∀ X : Finset (Fin 4),
        (∑ A, μ A * (subspaceLoad u (matroidSpan u X) A : ℝ)) ≤
          (3 / 4 : ℝ) * (Module.finrank (ZMod 2) (matroidSpan u X) : ℝ)) ∧
      ¬ ∃ β : ℝ, β < 1 ∧ IsSubspaceBetaBounded u Finset.univ β μ := by
    clear h_part1a
    let u : Fin 4 → (Fin 3 → ZMod 2) := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 1]]
    let A₁ : Finset (Fin 4) := {0, 1}
    let A₂ : Finset (Fin 4) := {2, 3}
    let μ : Finset (Fin 4) → ℝ := fun A =>
      (if A = A₁ then (1 / 2 : ℝ) else 0) + (if A = A₂ then (1 / 2 : ℝ) else 0)
    have hcard_01 : A₁.card = 2 :=
      Finset.card_pair (by intro h; exact absurd (congr_arg Fin.val h) (by norm_num))
    have hcard_23 : A₂.card = 2 :=
      Finset.card_pair (by intro h; exact absurd (congr_arg Fin.val h) (by norm_num))
    have hμ_exp : ∀ f : Finset (Fin 4) → ℝ,
        (∑ A, μ A * f A) = (1 / 2 : ℝ) * f A₁ + (1 / 2 : ℝ) * f A₂ := by
      intro f
      simp only [μ, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have h_u34 : ∀ X : Finset (Fin 4),
        LinearIndependent (ZMod 2) (fun g : X => u g.1) ↔ X.card ≤ 3 := by
      intro X
      constructor
      · intro hli
        have hcard := hli.fintype_card_le_finrank
        rw [Fintype.card_coe, Module.finrank_fin_fun] at hcard
        exact hcard
      · intro hcard
        rw [Fintype.linearIndependent_iff]
        intro c hc g
        let c' : Fin 4 → ZMod 2 := fun x => if hx : x ∈ X then c ⟨x, hx⟩ else 0
        have hsum_eq : (∑ x : Fin 4, c' x • u x) = ∑ x : X, c x • u x.1 := by
          change (∑ x ∈ Finset.univ, c' x • u x) = ∑ x ∈ X.attach, c x • u x.1
          rw [← Finset.sum_subset (Finset.subset_univ X) (fun x _ hx => by simp [c', hx])]
          rw [← Finset.sum_attach X (fun x => c' x • u x)]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp [c', x.2]
        rw [← hsum_eq] at hc
        rw [Fin.sum_univ_four] at hc
        have hc0 : c' 0 + c' 3 = 0 := by
          have h0 := congr_fun hc 0
          simpa [u] using h0
        have hc1 : c' 1 + c' 3 = 0 := by
          have h1 := congr_fun hc 1
          simpa [u] using h1
        have hc2 : c' 2 + c' 3 = 0 := by
          have h2 := congr_fun hc 2
          simpa [u] using h2
        have hex : ∃ k : Fin 4, k ∉ X := by
          by_contra hall
          push_neg at hall
          have huniv : X = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
          rw [huniv] at hcard
          have hcard_univ : (Finset.univ : Finset (Fin 4)).card = 4 := by simp
          omega
        rcases hex with ⟨k, hk⟩
        have hck : c' k = 0 := dif_neg hk
        have hall : ∀ x : Fin 4, c' x = 0 := by
          rcases k with ⟨_ | _ | _ | _ | k, hklt⟩
          · change c' 0 = 0 at hck
            rw [hck, zero_add] at hc0
            rintro ⟨_ | _ | _ | _ | x, hxlt⟩
            · exact hck
            · rw [hc0, add_zero] at hc1; exact hc1
            · rw [hc0, add_zero] at hc2; exact hc2
            · exact hc0
            · omega
          · change c' 1 = 0 at hck
            rw [hck, zero_add] at hc1
            rintro ⟨_ | _ | _ | _ | x, hxlt⟩
            · rw [hc1, add_zero] at hc0; exact hc0
            · exact hck
            · rw [hc1, add_zero] at hc2; exact hc2
            · exact hc1
            · omega
          · change c' 2 = 0 at hck
            rw [hck, zero_add] at hc2
            rintro ⟨_ | _ | _ | _ | x, hxlt⟩
            · rw [hc2, add_zero] at hc0; exact hc0
            · rw [hc2, add_zero] at hc1; exact hc1
            · exact hck
            · exact hc2
            · omega
          · change c' 3 = 0 at hck
            rintro ⟨_ | _ | _ | _ | x, hxlt⟩
            · rw [hck, add_zero] at hc0; exact hc0
            · rw [hck, add_zero] at hc1; exact hc1
            · rw [hck, add_zero] at hc2; exact hc2
            · exact hck
            · omega
          · omega
        exact (dif_pos g.2).symm.trans (hall g.1)
    have hμ_law : IsIndepSetLaw u Finset.univ μ := by
      refine ⟨?_, ?_, ?_⟩
      · intro A; dsimp only [μ]; positivity
      · intro A hA
        have hA_cases : A = A₁ ∨ A = A₂ := by
          by_contra hneither
          push_neg at hneither
          apply hA
          simp [μ, hneither.1, hneither.2]
        refine ⟨Finset.subset_univ _, ?_⟩
        rw [h_u34]
        rcases hA_cases with rfl | rfl <;> omega
      · have h1 := hμ_exp (fun _ => 1)
        simp only [mul_one] at h1
        linarith
    refine ⟨u, μ, h_u34, hμ_law, ?_, ?_⟩
    · intro X
      let S₁ : Submodule (ZMod 2) (Fin 3 → ZMod 2) := matroidSpan u A₁
      let S₂ : Submodule (ZMod 2) (Fin 3 → ZMod 2) := matroidSpan u A₂
      have h_span_card : ∀ Y : Finset (Fin 4), Y.card ≤ 3 →
          Module.finrank (ZMod 2) (matroidSpan u Y) = Y.card := by
        intro Y hY
        have hli := (h_u34 Y).mpr hY
        have hrange : Set.range (fun g : Y => u g.1) = u '' (Y : Set (Fin 4)) := by
          ext v; simp
        have hfr := finrank_span_eq_card hli
        rw [Fintype.card_coe] at hfr
        unfold matroidSpan
        rw [← congr_arg (fun M : Submodule (ZMod 2) _ => Module.finrank (ZMod 2) M)
          (congr_arg (Submodule.span (ZMod 2)) hrange)]
        exact hfr
      have hS1_dim : Module.finrank (ZMod 2) S₁ = 2 :=
        (h_span_card A₁ (by omega)).trans hcard_01
      have hS2_dim : Module.finrank (ZMod 2) S₂ = 2 :=
        (h_span_card A₂ (by omega)).trans hcard_23
      have hS1_coord : ∀ v ∈ S₁, v 2 = 0 := by
        intro v hv
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
        · rintro _ ⟨g, hg, rfl⟩
          simp only [A₁, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hg
          rcases hg with rfl | rfl <;> rfl
        · rfl
        · intro x y _ _ hx hy; simp [hx, hy]
        · intro a x _ hx; simp [hx]
      have hS2_coord : ∀ v ∈ S₂, v 0 = v 1 := by
        intro v hv
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
        · rintro _ ⟨g, hg, rfl⟩
          simp only [A₂, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hg
          rcases hg with rfl | rfl <;> rfl
        · rfl
        · intro x y _ _ hx hy; simp [hx, hy]
        · intro a x _ hx; simp [hx]
      have h_inf_le1 : Module.finrank (ZMod 2) ↥(S₁ ⊓ S₂) ≤ 1 := by
        have hlt : S₁ ⊓ S₂ < S₂ := by
          refine lt_of_le_of_ne inf_le_right ?_
          intro heq
          have hu2_S2 : u 2 ∈ S₂ := Submodule.subset_span ⟨2, by simp [A₂], rfl⟩
          rw [← heq] at hu2_S2
          exact one_ne_zero (hS1_coord (u 2) (Submodule.mem_inf.mp hu2_S2).1)
        have hfr_lt := Submodule.finrank_lt_finrank_of_lt hlt
        omega
      have h_no_item_inf : ∀ g : Fin 4, u g ∉ S₁ ⊓ S₂ := by
        rintro ⟨_ | _ | _ | _ | g, hglt⟩ hmem
        · exact one_ne_zero (hS2_coord (u 0) (Submodule.mem_inf.mp hmem).2)
        · exact one_ne_zero (hS2_coord (u 1) (Submodule.mem_inf.mp hmem).2).symm
        · exact one_ne_zero (hS1_coord (u 2) (Submodule.mem_inf.mp hmem).1)
        · exact one_ne_zero (hS1_coord (u 3) (Submodule.mem_inf.mp hmem).1)
        · omega
      rw [hμ_exp]
      set W : Submodule (ZMod 2) (Fin 3 → ZMod 2) := matroidSpan u X
      set l₁ : ℕ := subspaceLoad u W A₁
      set l₂ : ℕ := subspaceLoad u W A₂
      set r : ℕ := Module.finrank (ZMod 2) W
      suffices h_nat : 2 * (l₁ + l₂) ≤ 3 * r by
        have h_real : (2 : ℝ) * ((l₁ : ℝ) + (l₂ : ℝ)) ≤ 3 * (r : ℝ) := by exact_mod_cast h_nat
        linarith
      have hl1_r : l₁ ≤ r := Submodule.finrank_mono inf_le_right
      have hl2_r : l₂ ≤ r := Submodule.finrank_mono inf_le_right
      have hl1_2 : l₁ ≤ 2 := hS1_dim ▸ Submodule.finrank_mono inf_le_left
      have hl2_2 : l₂ ≤ 2 := hS2_dim ▸ Submodule.finrank_mono inf_le_left
      have hX_le4 : X.card ≤ 4 := by simpa using Finset.card_le_univ X
      rcases Nat.eq_or_lt_of_le hX_le4 with hX4 | hXlt4
      · obtain ⟨Y, hYX, hY3⟩ := Finset.exists_subset_card_eq (by omega : 3 ≤ X.card)
        have hY_dim : Module.finrank (ZMod 2) (matroidSpan u Y) = 3 :=
          (h_span_card Y (by omega)).trans hY3
        have hr3 : 3 ≤ r := by
          rw [← hY_dim]
          exact Submodule.finrank_mono (Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr hYX)))
        omega
      · have hr_eq : r = X.card := h_span_card X (by omega)
        interval_cases hXc : X.card
        · omega
        · rw [Finset.card_eq_one] at hXc
          rcases hXc with ⟨g, rfl⟩
          have hW_eq : W = Submodule.span (ZMod 2) {u g} := by
            dsimp only [W, matroidSpan]; simp
          by_cases hg1 : u g ∈ S₁
          · have hg2 : u g ∉ S₂ := fun hg2 => h_no_item_inf g (Submodule.mem_inf.mpr ⟨hg1, hg2⟩)
            have hbot : S₂ ⊓ W = ⊥ := by
              rw [hW_eq, eq_bot_iff]
              intro x hx
              rcases Submodule.mem_inf.mp hx with ⟨hxS, hxg⟩
              rw [Submodule.mem_span_singleton] at hxg
              rcases hxg with ⟨c, rfl⟩
              by_cases hc : c = 0
              · simp [hc]
              · exfalso; apply hg2
                have hm := S₂.smul_mem c⁻¹ hxS
                rwa [inv_smul_smul₀ hc] at hm
            have hl2_0 : l₂ = 0 := by
              dsimp only [l₂, subspaceLoad]
              rw [congr_arg (fun M : Submodule (ZMod 2) _ => Module.finrank (ZMod 2) M) hbot]
              exact finrank_bot (ZMod 2) (Fin 3 → ZMod 2)
            omega
          · have hbot : S₁ ⊓ W = ⊥ := by
              rw [hW_eq, eq_bot_iff]
              intro x hx
              rcases Submodule.mem_inf.mp hx with ⟨hxS, hxg⟩
              rw [Submodule.mem_span_singleton] at hxg
              rcases hxg with ⟨c, rfl⟩
              by_cases hc : c = 0
              · simp [hc]
              · exfalso; apply hg1
                have hm := S₁.smul_mem c⁻¹ hxS
                rwa [inv_smul_smul₀ hc] at hm
            have hl1_0 : l₁ = 0 := by
              dsimp only [l₁, subspaceLoad]
              rw [congr_arg (fun M : Submodule (ZMod 2) _ => Module.finrank (ZMod 2) M) hbot]
              exact finrank_bot (ZMod 2) (Fin 3 → ZMod 2)
            omega
        · have hnot4 : ¬ (l₁ = 2 ∧ l₂ = 2) := by
            rintro ⟨h1, h2⟩
            have hW1 : S₁ ⊓ W = W := Submodule.eq_of_le_of_finrank_eq inf_le_right (h1.trans hr_eq.symm)
            have hW2 : S₂ ⊓ W = W := Submodule.eq_of_le_of_finrank_eq inf_le_right (h2.trans hr_eq.symm)
            have hW_le : W ≤ S₁ ⊓ S₂ := le_inf (inf_eq_right.mp hW1) (inf_eq_right.mp hW2)
            have hfr_le : r ≤ Module.finrank (ZMod 2) ↥(S₁ ⊓ S₂) := Submodule.finrank_mono hW_le
            omega
          omega
        · omega
    · rintro ⟨β, hβ_lt, _, hload⟩
      let w : Fin 3 → ZMod 2 := ![1, 1, 0]
      let U_hid : Submodule (ZMod 2) (Fin 3 → ZMod 2) := Submodule.span (ZMod 2) {w}
      have hw0 : w ≠ 0 := by
        intro h
        have h0 : (1 : ZMod 2) = 0 := by simpa [w] using congr_fun h 0
        exact one_ne_zero h0
      have hw_S1 : w ∈ matroidSpan u A₁ := by
        have hw_eq : w = u 0 + u 1 := by
          ext ⟨_ | _ | _ | k, hklt⟩ <;> first | rfl | omega
        rw [hw_eq]
        exact Submodule.add_mem _
          (Submodule.subset_span ⟨0, by simp [A₁], rfl⟩)
          (Submodule.subset_span ⟨1, by simp [A₁], rfl⟩)
      have hw_S2 : w ∈ matroidSpan u A₂ := by
        have hw_eq : w = u 2 + u 3 := by
          ext ⟨_ | _ | _ | k, hklt⟩ <;> first | rfl | omega
        rw [hw_eq]
        exact Submodule.add_mem _
          (Submodule.subset_span ⟨2, by simp [A₂], rfl⟩)
          (Submodule.subset_span ⟨3, by simp [A₂], rfl⟩)
      have hdim1 : Module.finrank (ZMod 2) U_hid = 1 := finrank_span_singleton hw0
      have hl1 : subspaceLoad u U_hid A₁ = 1 := by
        unfold subspaceLoad
        have hle : U_hid ≤ matroidSpan u A₁ := (Submodule.span_singleton_le_iff_mem _ _).mpr hw_S1
        rw [congr_arg (fun M : Submodule (ZMod 2) _ => Module.finrank (ZMod 2) M) (inf_of_le_right hle)]
        exact finrank_span_singleton hw0
      have hl2 : subspaceLoad u U_hid A₂ = 1 := by
        unfold subspaceLoad
        have hle : U_hid ≤ matroidSpan u A₂ := (Submodule.span_singleton_le_iff_mem _ _).mpr hw_S2
        rw [congr_arg (fun M : Submodule (ZMod 2) _ => Module.finrank (ZMod 2) M) (inf_of_le_right hle)]
        exact finrank_span_singleton hw0
      have hb := hload U_hid
      rw [hμ_exp, hl1, hl2, hdim1] at hb
      norm_num at hb
      linarith
  have h_part2 : ∀ {n d : ℕ} {F : Type} [Field F] [Fintype F]
      (u : Fin n → (Fin d → F)) (S B : Finset (Fin n)) (β a : ℝ)
      (μ_g : Fin n → Finset (Fin n) → ℝ),
      1 ≤ S.card → B ⊆ S → 0 ≤ β → β ≤ 1 → 0 ≤ a → a ≤ 1 - β →
      LinearIndependent F (fun g : B => u g.1) →
      (∀ g ∈ S, IsIndepSetLaw u (S.erase g) (μ_g g) ∧ IsSubspaceBetaBounded u S β (μ_g g)) →
        ∃ q : Fin n → Finset (Fin n) → ℝ,
          (∀ g ∈ S, ∀ A, 0 ≤ q g A ∧ q g A ≤ μ_g g A) ∧
          (∀ g ∈ S, ∀ A, q g A ≠ 0 →
            g ∈ B ∧ g ∉ A ∧ LinearIndependent F (fun x : (insert g A : Finset (Fin n)) => u x.1)) ∧
          (∀ g ∈ B, (∑ A, q g A) = a) ∧
          let ν : Fin n → Finset (Fin n) → ℝ := fun g C =>
            μ_g g C + (∑ A, if insert g A = C then q g A else 0) - q g C
          let μ_avg : Finset (Fin n) → ℝ := fun C => (1 / (S.card : ℝ)) * ∑ g ∈ S, ν g C
          IsSubspaceBetaBounded u S (β + a / (S.card : ℝ)) μ_avg := by
    clear h_part1b
    have h_jump : ∀ {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
        [FiniteDimensional K V] (Y Z : Submodule K V) (v : V),
        v ∉ Z →
          Module.finrank K ↥(Z ⊔ Submodule.span K {v}) = Module.finrank K Z + 1 ∧
          Module.finrank K ↥(Y ⊓ (Z ⊔ Submodule.span K {v})) =
            Module.finrank K ↥(Y ⊓ Z) + (if v ∈ Y ⊔ Z then 1 else 0) := by
      clear h_part1a
      intro K _ V _ _ _ Y Z v hvZ
      have h_sup_one : ∀ (W : Submodule K V), v ∉ W →
          Module.finrank K ↥(W ⊔ Submodule.span K {v}) = Module.finrank K W + 1 := by
        intro W hvW
        have hv0 : v ≠ 0 := fun h0 => hvW (h0 ▸ W.zero_mem)
        have h_span_dim : Module.finrank K ↥(Submodule.span K {v}) = 1 :=
          finrank_span_singleton hv0
        have h_inf_bot : W ⊓ Submodule.span K {v} = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          rcases Submodule.mem_inf.mp hx with ⟨hxW, hxv⟩
          rw [Submodule.mem_span_singleton] at hxv
          rcases hxv with ⟨c, rfl⟩
          by_cases hc : c = 0
          · simp [hc]
          · exfalso
            apply hvW
            have hmem := W.smul_mem c⁻¹ hxW
            rwa [inv_smul_smul₀ hc] at hmem
        have h_inf_dim : Module.finrank K ↥(W ⊓ Submodule.span K {v}) = 0 := by
          rw [congr_arg (fun M : Submodule K V => Module.finrank K M) h_inf_bot]
          exact finrank_bot K V
        have h_grass := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span K {v})
        omega
      refine ⟨h_sup_one Z hvZ, ?_⟩
      set Z' : Submodule K V := Z ⊔ Submodule.span K {v}
      have hZ'_dim : Module.finrank K Z' = Module.finrank K Z + 1 := h_sup_one Z hvZ
      have h_grass1 := Submodule.finrank_sup_add_finrank_inf_eq Y Z
      have h_grass2 := Submodule.finrank_sup_add_finrank_inf_eq Y Z'
      have h_assoc : Y ⊔ Z' = (Y ⊔ Z) ⊔ Submodule.span K {v} :=
        (sup_assoc Y Z (Submodule.span K {v})).symm
      by_cases hvYZ : v ∈ Y ⊔ Z
      · have h_eq : Y ⊔ Z' = Y ⊔ Z := by
          rw [h_assoc, sup_eq_left, Submodule.span_singleton_le_iff_mem]
          exact hvYZ
        have h_sup_dim : Module.finrank K ↥(Y ⊔ Z') = Module.finrank K ↥(Y ⊔ Z) :=
          congr_arg (fun M : Submodule K V => Module.finrank K M) h_eq
        simp only [hvYZ, ↓reduceIte]
        omega
      · have h_sup_dim : Module.finrank K ↥(Y ⊔ Z') = Module.finrank K ↥(Y ⊔ Z) + 1 := by
          rw [congr_arg (fun M : Submodule K V => Module.finrank K M) h_assoc]
          exact h_sup_one (Y ⊔ Z) hvYZ
        simp only [hvYZ, ↓reduceIte]
        omega
    have h_li_coe : ∀ {α : Type} {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
        (v : α → V) (X : Finset α),
        LinearIndependent K (fun g : X => v g.1) ↔ LinearIndepOn K v (X : Set α) := by
      clear h_part1a h_jump
      intro α K _ V _ _ v X
      let eqv : ↥X ≃ ↥(X : Set α) :=
        ⟨fun x => ⟨x.1, Finset.mem_coe.mpr x.2⟩,
         fun x => ⟨x.1, Finset.mem_coe.mp x.2⟩,
         fun _ => rfl, fun _ => rfl⟩
      exact linearIndependent_equiv eqv (f := fun x : ↥(X : Set α) => v x.1)
    have h_minimax_rat : ∀ {E : Type} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
        [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
        {k : ℕ} (Q : Set E) (φ : Fin k → E → ℝ),
        IsCompact Q → Convex ℝ Q → Q.Nonempty →
        (∀ t : Fin k, ContinuousOn (φ t) Q) →
        (∀ t : Fin k, ∀ x ∈ Q, ∀ y ∈ Q, ∀ a₁ a₂ : ℝ,
          0 ≤ a₁ → 0 ≤ a₂ → a₁ + a₂ = 1 → φ t (a₁ • x + a₂ • y) = a₁ * φ t x + a₂ * φ t y) →
        (∀ lam : Fin k → ℚ, (∀ t : Fin k, 0 ≤ lam t) →
          ∃ x ∈ Q, (∑ t : Fin k, (lam t : ℝ) * φ t x) ≤ 0) →
          ∃ x ∈ Q, ∀ t : Fin k, φ t x ≤ 0 := by
      clear h_part1a h_jump h_li_coe
      intro E _ _ _ _ _ _ k Q φ hQ_comp hQ_conv _ hφ_cont hφ_aff h_rat
      by_contra h_contra
      let Φ : E → (Fin k → ℝ) := fun x t => φ t x
      have hΦ_cont : ContinuousOn Φ Q := continuousOn_pi.mpr hφ_cont
      let C : Set (Fin k → ℝ) := Φ '' Q
      have hC_comp : IsCompact C := hQ_comp.image_of_continuousOn hΦ_cont
      have hC_conv : Convex ℝ C := by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a₁ a₂ ha₁ ha₂ hab
        refine ⟨a₁ • x + a₂ • y, hQ_conv hx hy ha₁ ha₂ hab, ?_⟩
        ext t
        simp only [Φ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact hφ_aff t x hx y hy a₁ a₂ ha₁ ha₂ hab
      let K : Set (Fin k → ℝ) := Set.univ.pi (fun _ : Fin k => Set.Iic (0 : ℝ))
      have hK_closed : IsClosed K := isClosed_set_pi (fun _ _ => isClosed_Iic)
      have hK_conv : Convex ℝ K := convex_pi (fun _ _ => convex_Iic (0 : ℝ))
      have h_disj : Disjoint K C := by
        refine Set.disjoint_left.mpr (fun y hyK hyC => ?_)
        rcases hyC with ⟨x, hxQ, rfl⟩
        exact h_contra ⟨x, hxQ, fun t => hyK t (Set.mem_univ t)⟩
      obtain ⟨f, u_val, v_val, hfK, huv, hfC⟩ :=
        geometric_hahn_banach_closed_compact hK_conv hK_closed hC_conv hC_comp h_disj
      have h0K : (0 : Fin k → ℝ) ∈ K := fun _ _ => Set.mem_Iic.mpr le_rfl
      have hu_pos : 0 < u_val := by
        have h := hfK 0 h0K
        rwa [map_zero] at h
      have hv_pos : 0 < v_val := hu_pos.trans huv
      let e : Fin k → (Fin k → ℝ) := fun t s => if s = t then 1 else 0
      let w : Fin k → ℝ := fun t => f (e t)
      have hw_nn : ∀ t : Fin k, 0 ≤ w t := by
        intro t
        by_contra hlt
        have hw_neg : w t < 0 := not_le.mp hlt
        let M : ℝ := (u_val + 1) / (-w t)
        have hM_pos : 0 < M := div_pos (by linarith) (by linarith)
        let y : Fin k → ℝ := (-M) • e t
        have hyK : y ∈ K := by
          intro s _
          rw [Set.mem_Iic]
          dsimp only [y, e, Pi.smul_apply, smul_eq_mul]
          split_ifs <;> linarith
        have hfy := hfK y hyK
        have hfy_eq : f y = u_val + 1 := by
          dsimp only [y]
          rw [map_smul, smul_eq_mul]
          change (-M) * w t = u_val + 1
          dsimp only [M]
          have hne : w t ≠ 0 := by linarith
          field_simp [hne]
        linarith
      have hf_sum : ∀ x ∈ Q, v_val < ∑ t : Fin k, w t * φ t x := by
        intro x hx
        have hexp : Φ x = ∑ t : Fin k, φ t x • e t := by
          ext s; simp [Φ, e]
        have h := hfC (Φ x) ⟨x, hx, rfl⟩
        rw [hexp, map_sum] at h
        refine h.trans_eq ?_
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [map_smul, smul_eq_mul, mul_comm]
      obtain ⟨Bnd, hBnd⟩ := hQ_comp.exists_bound_of_continuousOn hΦ_cont
      let D : ℝ := max Bnd 1
      have hD_pos : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right Bnd 1)
      have hφ_abs : ∀ x ∈ Q, ∀ t : Fin k, |φ t x| ≤ D := by
        intro x hx t
        have h1 : ‖Φ x t‖ ≤ ‖Φ x‖ := norm_le_pi_norm (Φ x) t
        rw [Real.norm_eq_abs] at h1
        exact h1.trans ((hBnd x hx).trans (le_max_left Bnd 1))
      let δ : ℝ := v_val / (2 * ((k : ℝ) + 1) * D)
      have hδ_pos : 0 < δ := by positivity
      have h_ex_rat : ∀ t : Fin k, ∃ q : ℚ, w t < (q : ℝ) ∧ (q : ℝ) < w t + δ :=
        fun t => exists_rat_btwn (lt_add_of_pos_right (w t) hδ_pos)
      let lam : Fin k → ℚ := fun t => Classical.choose (h_ex_rat t)
      have hlam_spec : ∀ t : Fin k, w t < (lam t : ℝ) ∧ (lam t : ℝ) < w t + δ :=
        fun t => Classical.choose_spec (h_ex_rat t)
      have hlam_nn : ∀ t : Fin k, 0 ≤ lam t :=
        fun t => Rat.cast_nonneg.mp (le_of_lt ((hw_nn t).trans_lt (hlam_spec t).1))
      obtain ⟨x₀, hx₀Q, hx₀_le⟩ := h_rat lam hlam_nn
      have h_term_ge : ∀ t : Fin k, -(δ * D) ≤ ((lam t : ℝ) - w t) * φ t x₀ := by
        intro t
        obtain ⟨hl1, hl2⟩ := hlam_spec t
        obtain ⟨ha1, ha2⟩ := abs_le.mp (hφ_abs x₀ hx₀Q t)
        nlinarith
      have h_sum_diff : -((k : ℝ) * (δ * D)) ≤
          (∑ t : Fin k, (lam t : ℝ) * φ t x₀) - (∑ t : Fin k, w t * φ t x₀) := by
        have h1 : (∑ t : Fin k, -(δ * D)) ≤ ∑ t : Fin k, ((lam t : ℝ) - w t) * φ t x₀ :=
          Finset.sum_le_sum (fun t _ => h_term_ge t)
        have h2 : (∑ t : Fin k, -(δ * D)) = -((k : ℝ) * (δ * D)) := by simp [nsmul_eq_mul]
        have h3 : (∑ t : Fin k, ((lam t : ℝ) - w t) * φ t x₀) =
            (∑ t : Fin k, (lam t : ℝ) * φ t x₀) - (∑ t : Fin k, w t * φ t x₀) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun t _ => by ring)
        linarith
      have h_err_le : (k : ℝ) * (δ * D) ≤ v_val / 2 := by
        have hD_ne : D ≠ 0 := hD_pos.ne'
        have hk1_pos : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by positivity
        have hk1_ne : (2 * ((k : ℝ) + 1) : ℝ) ≠ 0 := hk1_pos.ne'
        have hδD : δ * D = v_val / (2 * ((k : ℝ) + 1)) := by
          dsimp only [δ]; field_simp [hD_ne, hk1_ne]
        rw [hδD]
        have hk_le : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
        calc
          (k : ℝ) * (v_val / (2 * ((k : ℝ) + 1)))
              ≤ ((k : ℝ) + 1) * (v_val / (2 * ((k : ℝ) + 1))) :=
                mul_le_mul_of_nonneg_right hk_le (by positivity)
          _ = v_val / 2 := by
                have h_ne : ((k : ℝ) + 1) ≠ 0 := by positivity
                field_simp [h_ne]
      have h_w_gt := hf_sum x₀ hx₀Q
      linarith
    intro n d F _ _ u S B β a μ_g hS_card hBS hβ0 hβ1 ha0 ha1 hB_indep hμ
    have hS_pos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr (by omega)
    have hS_ne : (S.card : ℝ) ≠ 0 := hS_pos.ne'
    let IsExtFeas : Fin n → Finset (Fin n) → Prop := fun g A =>
      g ∉ A ∧ insert g A ⊆ S ∧ LinearIndependent F (fun x : (insert g A : Finset (Fin n)) => u x.1)
    have h_ext_iff : ∀ g ∈ S, ∀ A, A ⊆ S.erase g → LinearIndependent F (fun x : A => u x.1) →
        (IsExtFeas g A ↔ u g ∉ matroidSpan u A) := by
      intro g hgS A hA_sub hA_li
      have hgA : g ∉ A := fun hg => (Finset.mem_erase.mp (hA_sub hg)).1 rfl
      have hinsS : insert g A ⊆ S :=
        Finset.insert_subset hgS (hA_sub.trans (Finset.erase_subset g S))
      have hg_coe : g ∉ (A : Set (Fin n)) := Finset.mem_coe.not.mpr hgA
      constructor
      · rintro ⟨_, _, hli_ins⟩
        have hli_on := (h_li_coe u (insert g A)).mp hli_ins
        rw [Finset.coe_insert] at hli_on
        exact ((linearIndepOn_insert hg_coe).mp hli_on).2
      · intro hnot
        refine ⟨hgA, hinsS, ?_⟩
        rw [h_li_coe, Finset.coe_insert]
        exact (linearIndepOn_insert hg_coe).mpr ⟨(h_li_coe u A).mp hA_li, hnot⟩
    have h_load_add : ∀ (g : Fin n) (A : Finset (Fin n)) (U : Submodule F (Fin d → F)),
        IsExtFeas g A →
          subspaceLoad u U (insert g A) =
            subspaceLoad u U A + (if u g ∈ matroidSpan u A ⊔ U then 1 else 0) := by
      intro g A U ⟨hgA, _, hli_ins⟩
      have hg_coe : g ∉ (A : Set (Fin n)) := Finset.mem_coe.not.mpr hgA
      have hli_on := (h_li_coe u (insert g A)).mp hli_ins
      rw [Finset.coe_insert] at hli_on
      have hv_not_Z : u g ∉ matroidSpan u A := ((linearIndepOn_insert hg_coe).mp hli_on).2
      have h_span_ins : matroidSpan u (insert g A) =
          matroidSpan u A ⊔ Submodule.span F {u g} := by
        unfold matroidSpan
        rw [Finset.coe_insert, Set.image_insert_eq, Submodule.span_insert, sup_comm]
      have hj := (h_jump U (matroidSpan u A) (u g) hv_not_Z).2
      unfold subspaceLoad
      rw [congr_arg (fun M : Submodule F _ => Module.finrank F M) (by rw [h_span_ins, inf_comm]),
          hj,
          congr_arg (fun M : Submodule F _ => Module.finrank F M) (inf_comm _ _),
          sup_comm]
    have h_chain_single : ∀ (g : Fin n) (h : ℕ) (C : Fin h → Submodule F (Fin d → F)),
        g ∈ S → u g ≠ 0 →
        (∀ r₁ r₂ : Fin h, r₁ ≤ r₂ → C r₁ ≤ C r₂) →
          ∃ qg : Finset (Fin n) → ℝ,
            (∀ A, 0 ≤ qg A ∧ qg A ≤ μ_g g A) ∧
            (∀ A, qg A ≠ 0 → IsExtFeas g A) ∧
            (∑ A, qg A) = a ∧
            ∀ r : Fin h,
              (∑ C', (μ_g g C' + (∑ A, if insert g A = C' then qg A else 0) - qg C') *
                  (subspaceLoad u (C r) C' : ℝ)) ≤
                β * (Module.finrank F (C r) : ℝ) + (if u g ∈ C r then a else 0) := by
      intro g h C hgS hug0 hC_mono
      obtain ⟨⟨hμ_nn, hμ_supp, hμ_sum⟩, ⟨_, hload⟩⟩ := hμ g hgS
      have h_avail : 1 - β ≤ ∑ A ∈ Finset.univ.filter (fun A => IsExtFeas g A), μ_g g A := by
        let L : Submodule F (Fin d → F) := Submodule.span F {u g}
        have hL_dim : Module.finrank F L = 1 := finrank_span_singleton hug0
        have hL_load : ∀ A, subspaceLoad u L A = if u g ∈ matroidSpan u A then 1 else 0 := by
          intro A
          unfold subspaceLoad
          by_cases hmem : u g ∈ matroidSpan u A
          · have hle : L ≤ matroidSpan u A := (Submodule.span_singleton_le_iff_mem _ _).mpr hmem
            rw [congr_arg (fun M : Submodule F _ => Module.finrank F M) (inf_of_le_right hle)]
            simp [hmem, hL_dim]
          · have hbot : matroidSpan u A ⊓ L = ⊥ := by
              rw [eq_bot_iff]
              intro x hx
              rcases Submodule.mem_inf.mp hx with ⟨hxA, hxg⟩
              rw [Submodule.mem_span_singleton] at hxg
              rcases hxg with ⟨c, rfl⟩
              by_cases hc : c = 0
              · simp [hc]
              · exfalso; apply hmem
                have h1 := (matroidSpan u A).smul_mem c⁻¹ hxA
                rwa [inv_smul_smul₀ hc] at h1
            rw [congr_arg (fun M : Submodule F _ => Module.finrank F M) hbot]
            simp [hmem, finrank_bot]
        have h_in_le : (∑ A ∈ Finset.univ.filter (fun A => u g ∈ matroidSpan u A), μ_g g A) ≤ β := by
          have hb := hload L
          rw [hL_dim, Nat.cast_one, mul_one] at hb
          have hlhs : (∑ A ∈ Finset.univ.filter (fun A => u g ∈ matroidSpan u A), μ_g g A) =
              ∑ A, μ_g g A * (subspaceLoad u L A : ℝ) := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun A _ => ?_
            rw [hL_load A]; split_ifs <;> simp
          linarith
        have h_part_sum := Finset.sum_filter_add_sum_filter_not
          (Finset.univ : Finset (Finset (Fin n))) (fun A => u g ∈ matroidSpan u A) (μ_g g)
        have h_le_feas :
            (∑ A ∈ Finset.univ.filter (fun A => ¬ u g ∈ matroidSpan u A), μ_g g A) ≤
            ∑ A ∈ Finset.univ.filter (fun A => IsExtFeas g A), μ_g g A := by
          rw [Finset.sum_filter, Finset.sum_filter]
          refine Finset.sum_le_sum fun A _ => ?_
          by_cases hμA : μ_g g A = 0
          · simp [hμA]
          · by_cases hmem : u g ∈ matroidSpan u A
            · simp only [hmem, not_true_eq_false, ↓reduceIte]
              split_ifs
              · exact hμ_nn A
              · exact le_rfl
            · obtain ⟨hA_sub, hA_li⟩ := hμ_supp A hμA
              have hfeas := (h_ext_iff g hgS A hA_sub hA_li).mpr hmem
              simp [hmem, hfeas]
        linarith
      let b : Finset (Fin n) → ℕ := fun A =>
        (Finset.univ.filter (fun r : Fin h => u g ∈ matroidSpan u A ⊔ C r)).card
      have hb_le_h : ∀ A, b A ≤ h := by
        intro A
        simpa using Finset.card_le_univ
          (Finset.univ.filter (fun r : Fin h => u g ∈ matroidSpan u A ⊔ C r))
      have hb_in : ∀ A (r : Fin h), u g ∈ matroidSpan u A ⊔ C r → h - r.1 ≤ b A := by
        intro A r hmem
        have hsub : Finset.Ici r ⊆
            Finset.univ.filter (fun r' : Fin h => u g ∈ matroidSpan u A ⊔ C r') := by
          intro r' hr'
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ r', (sup_le_sup_left (hC_mono r r' (Finset.mem_Ici.mp hr')) _) hmem⟩
        have hcard := Finset.card_le_card hsub
        rwa [Fin.card_Ici] at hcard
      have hb_out : ∀ A (r : Fin h), u g ∉ matroidSpan u A ⊔ C r → b A + 1 ≤ h - r.1 := by
        intro A r hnot
        have hsub : Finset.univ.filter (fun r' : Fin h => u g ∈ matroidSpan u A ⊔ C r') ⊆
            Finset.Ioi r := by
          intro r' hr'
          rw [Finset.mem_filter] at hr'
          rw [Finset.mem_Ioi]
          by_contra hle
          exact hnot ((sup_le_sup_left (hC_mono r' r (not_lt.mp hle)) _) hr'.2)
        have hcard := Finset.card_le_card hsub
        rw [Fin.card_Ioi] at hcard
        have hrlt : r.1 < h := r.2
        dsimp only [b]
        omega
      let qt : ℝ → Finset (Fin n) → ℝ := fun t A =>
        if IsExtFeas g A then μ_g g A * min 1 (max 0 (t - (b A : ℝ))) else 0
      let Φ : ℝ → ℝ := fun t => ∑ A, qt t A
      have hΦ_cont : Continuous Φ := by
        refine continuous_finset_sum _ fun A _ => ?_
        dsimp only [qt]
        by_cases hA : IsExtFeas g A
        · simp only [hA, ↓reduceIte]
          exact continuous_const.mul
            (continuous_const.min (continuous_const.max (continuous_id.sub continuous_const)))
        · simp only [hA, ↓reduceIte]
          exact continuous_const
      have hΦ0 : Φ 0 = 0 := by
        dsimp only [Φ, qt]
        refine Finset.sum_eq_zero fun A _ => ?_
        have hb0 : (0 : ℝ) - (b A : ℝ) ≤ 0 := sub_nonpos.mpr (Nat.cast_nonneg _)
        rw [max_eq_left hb0, min_eq_right zero_le_one, mul_zero, ite_self]
      have hΦ_top : 1 - β ≤ Φ ((h : ℝ) + 1) := by
        have heq : Φ ((h : ℝ) + 1) =
            ∑ A ∈ Finset.univ.filter (fun A => IsExtFeas g A), μ_g g A := by
          dsimp only [Φ, qt]
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun A _ => ?_
          have hbh : (b A : ℝ) ≤ (h : ℝ) := Nat.cast_le.mpr (hb_le_h A)
          have h1 : (1 : ℝ) ≤ ((h : ℝ) + 1) - (b A : ℝ) := by linarith
          have hmax : (1 : ℝ) ≤ max 0 (((h : ℝ) + 1) - (b A : ℝ)) := h1.trans (le_max_right _ _)
          rw [min_eq_left hmax, mul_one]
        linarith
      obtain ⟨tstar, _, htstar_eq⟩ :=
        intermediate_value_Icc (by positivity : (0 : ℝ) ≤ (h : ℝ) + 1) hΦ_cont.continuousOn
          ⟨by rw [hΦ0]; exact ha0, ha1.trans hΦ_top⟩
      let qg : Finset (Fin n) → ℝ := qt tstar
      have hq_bounds : ∀ A, 0 ≤ qg A ∧ qg A ≤ μ_g g A := by
        intro A
        dsimp only [qg, qt]
        split_ifs
        · have hw0 : 0 ≤ min (1 : ℝ) (max 0 (tstar - (b A : ℝ))) :=
            le_min zero_le_one (le_max_left _ _)
        
          have hw1 : min (1 : ℝ) (max 0 (tstar - (b A : ℝ))) ≤ 1 := min_le_left _ _
          exact ⟨mul_nonneg (hμ_nn A) hw0,
            (mul_le_mul_of_nonneg_left hw1 (hμ_nn A)).trans (mul_one _).le⟩
        · exact ⟨le_rfl, hμ_nn A⟩
      have hq_supp : ∀ A, qg A ≠ 0 → IsExtFeas g A := by
        intro A hq0
        by_contra hn
        exact hq0 (by simp [qg, qt, hn])
      refine ⟨qg, hq_bounds, hq_supp, htstar_eq, fun r => ?_⟩
      let Dr := (Finset.univ : Finset (Finset (Fin n))).filter
        (fun A => u g ∈ matroidSpan u A ⊔ C r)
      have h_swap_load :
          (∑ C', (∑ A, if insert g A = C' then qg A else 0) * (subspaceLoad u (C r) C' : ℝ)) =
            ∑ A, qg A * (subspaceLoad u (C r) (insert g A) : ℝ) := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun A _ => ?_
        simp_rw [ite_mul, zero_mul]
        simp [Finset.sum_ite_eq]
      have h_diff_sum :
          (∑ A, qg A * ((subspaceLoad u (C r) (insert g A) : ℝ) - (subspaceLoad u (C r) A : ℝ))) =
            ∑ A ∈ Dr, qg A := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun A _ => ?_
        by_cases hqA : qg A = 0
        · simp [hqA]
        · rw [h_load_add g A (C r) (hq_supp A hqA), Nat.cast_add]
          split_ifs <;> simp
      have h_nu_load :
          (∑ C', (μ_g g C' + (∑ A, if insert g A = C' then qg A else 0) - qg C') *
              (subspaceLoad u (C r) C' : ℝ)) =
            (∑ A, μ_g g A * (subspaceLoad u (C r) A : ℝ)) + ∑ A ∈ Dr, qg A := by
        have h_exp :
            (∑ C', (μ_g g C' + (∑ A, if insert g A = C' then qg A else 0) - qg C') *
                (subspaceLoad u (C r) C' : ℝ)) =
              (∑ C', μ_g g C' * (subspaceLoad u (C r) C' : ℝ)) +
              (∑ C', (∑ A, if insert g A = C' then qg A else 0) * (subspaceLoad u (C r) C' : ℝ)) -
              (∑ C', qg C' * (subspaceLoad u (C r) C' : ℝ)) := by
          simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        have h_comb :
            (∑ A, qg A * (subspaceLoad u (C r) (insert g A) : ℝ)) -
            (∑ A, qg A * (subspaceLoad u (C r) A : ℝ)) =
            ∑ A, qg A * ((subspaceLoad u (C r) (insert g A) : ℝ) - (subspaceLoad u (C r) A : ℝ)) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun A _ => by ring
        linarith
      have hLr : (∑ A, μ_g g A * (subspaceLoad u (C r) A : ℝ)) ≤
          β * (Module.finrank F (C r) : ℝ) := hload (C r)
      rw [h_nu_load]
      by_cases hgCr : u g ∈ C r
      · simp only [hgCr, ↓reduceIte]
        have hq_le_a : ∑ A ∈ Dr, qg A ≤ a := by
          rw [← htstar_eq]
          exact Finset.sum_le_univ_sum_of_nonneg fun A => (hq_bounds A).1
        linarith
      · simp only [hgCr, ↓reduceIte, add_zero]
        by_cases htk : tstar ≤ ((h - r.1 : ℕ) : ℝ)
        · have hDr_zero : ∑ A ∈ Dr, qg A = 0 := by
            refine Finset.sum_eq_zero fun A hA => ?_
            have hk_real : ((h - r.1 : ℕ) : ℝ) ≤ (b A : ℝ) :=
              Nat.cast_le.mpr (hb_in A r (Finset.mem_filter.mp hA).2)
            have hsub_np : tstar - (b A : ℝ) ≤ 0 := by linarith
            dsimp only [qg, qt]
            rw [max_eq_left hsub_np, min_eq_right zero_le_one, mul_zero, ite_self]
          linarith
        · have htk_lt : ((h - r.1 : ℕ) : ℝ) < tstar := not_le.mp htk
          have hDrc_eq :
              ∑ A ∈ Finset.univ.filter (fun A => ¬ u g ∈ matroidSpan u A ⊔ C r), qg A =
              ∑ A ∈ Finset.univ.filter (fun A => ¬ u g ∈ matroidSpan u A ⊔ C r), μ_g g A := by
            refine Finset.sum_congr rfl fun A hA => ?_
            have hnot_sup : u g ∉ matroidSpan u A ⊔ C r := (Finset.mem_filter.mp hA).2
            by_cases hμA : μ_g g A = 0
            · exact (le_antisymm ((hq_bounds A).2.trans hμA.le) (hq_bounds A).1).trans hμA.symm
            · have hnot_span : u g ∉ matroidSpan u A :=
                fun hm => hnot_sup (Submodule.mem_sup_left hm)
              obtain ⟨hA_sub, hA_li⟩ := hμ_supp A hμA
              have hfeas : IsExtFeas g A := (h_ext_iff g hgS A hA_sub hA_li).mpr hnot_span
              have hb_lt : (b A : ℝ) + 1 ≤ ((h - r.1 : ℕ) : ℝ) := by
                exact_mod_cast hb_out A r hnot_sup
              have h1_le : (1 : ℝ) ≤ tstar - (b A : ℝ) := by linarith
              have hmax : (1 : ℝ) ≤ max 0 (tstar - (b A : ℝ)) := h1_le.trans (le_max_right _ _)
              dsimp only [qg, qt]
              simp only [hfeas, ↓reduceIte, min_eq_left hmax, mul_one]
          have hpart_q := Finset.sum_filter_add_sum_filter_not
            (Finset.univ : Finset (Finset (Fin n))) (fun A => u g ∈ matroidSpan u A ⊔ C r) qg
          have hpart_mu := Finset.sum_filter_add_sum_filter_not
            (Finset.univ : Finset (Finset (Fin n))) (fun A => u g ∈ matroidSpan u A ⊔ C r) (μ_g g)
          let C' : Submodule F (Fin d → F) := C r ⊔ Submodule.span F {u g}
          have hC'_dim : Module.finrank F C' = Module.finrank F (C r) + 1 :=
            (h_jump ⊥ (C r) (u g) hgCr).1
          have hC'_load : ∀ A, subspaceLoad u C' A =
              subspaceLoad u (C r) A + (if u g ∈ matroidSpan u A ⊔ C r then 1 else 0) :=
            fun A => (h_jump (matroidSpan u A) (C r) (u g) hgCr).2
          have hC'_bound := hload C'
          rw [hC'_dim, Nat.cast_add, Nat.cast_one] at hC'_bound
          have hC'_sum :
              (∑ A, μ_g g A * (subspaceLoad u C' A : ℝ)) =
                (∑ A, μ_g g A * (subspaceLoad u (C r) A : ℝ)) + ∑ A ∈ Dr, μ_g g A := by
            have h1 :
                (∑ A, μ_g g A * (subspaceLoad u C' A : ℝ)) =
                  (∑ A, μ_g g A * (subspaceLoad u (C r) A : ℝ)) +
                  ∑ A, (if u g ∈ matroidSpan u A ⊔ C r then μ_g g A else 0) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun A _ => ?_
              rw [hC'_load A, Nat.cast_add]
              split_ifs <;> simp [mul_add]
            rw [h1, Finset.sum_filter]
          linarith
    have h_supermod : ∀ (U T : Submodule F (Fin d → F)),
        U ≤ matroidSpan u S → T ≤ matroidSpan u S →
          (U ⊓ T ≤ matroidSpan u S) ∧ (U ⊔ T ≤ matroidSpan u S) ∧
          Module.finrank F U + Module.finrank F T =
            Module.finrank F ↥(U ⊓ T) + Module.finrank F ↥(U ⊔ T) ∧
          ∀ A : Finset (Fin n),
            subspaceLoad u U A + subspaceLoad u T A ≤
              subspaceLoad u (U ⊓ T) A + subspaceLoad u (U ⊔ T) A := by
      intro U T hU hT
      refine ⟨inf_le_left.trans hU, sup_le hU hT, ?_, ?_⟩
      · have hg := Submodule.finrank_sup_add_finrank_inf_eq U T
        omega
      · intro A
        unfold subspaceLoad
        set Y := matroidSpan u A
        have hg := Submodule.finrank_sup_add_finrank_inf_eq (Y ⊓ U) (Y ⊓ T)
        have h_inf_eq : (Y ⊓ U) ⊓ (Y ⊓ T) = Y ⊓ (U ⊓ T) :=
          le_antisymm
            (le_inf (inf_le_left.trans inf_le_left)
              (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)))
            (le_inf (le_inf inf_le_left (inf_le_right.trans inf_le_left))
              (le_inf inf_le_left (inf_le_right.trans inf_le_right)))
        have h_inf_dim : Module.finrank F ↥((Y ⊓ U) ⊓ (Y ⊓ T)) = Module.finrank F ↥(Y ⊓ (U ⊓ T)) :=
          congr_arg (fun M : Submodule F _ => Module.finrank F M) h_inf_eq
        have h_sup_le : (Y ⊓ U) ⊔ (Y ⊓ T) ≤ Y ⊓ (U ⊔ T) :=
          le_inf (sup_le inf_le_left inf_le_left)
            (sup_le (inf_le_right.trans le_sup_left) (inf_le_right.trans le_sup_right))
        have h_sup_dim := Submodule.finrank_mono h_sup_le
        omega
    have h_strict_drop : ∀ (U T : Submodule F (Fin d → F)),
        ¬ (U ≤ T) → Module.finrank F ↥(U ⊓ T) < Module.finrank F U := by
      intro U T hnot
      refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left ?_)
      intro heq
      exact hnot (inf_eq_left.mp heq)
    have h_uncross_rat : ∀ {k : ℕ} (U : Fin k → Submodule F (Fin d → F)) (lam : Fin k → ℚ),
        (∀ t : Fin k, U t ≤ matroidSpan u S ∧ 0 ≤ lam t) →
          ∃ (h : ℕ) (C : Fin h → Submodule F (Fin d → F)) (gam : Fin h → ℝ),
            (∀ r : Fin h, C r ≤ matroidSpan u S ∧ 0 ≤ gam r) ∧
            (∀ r₁ r₂ : Fin h, r₁ ≤ r₂ → C r₁ ≤ C r₂) ∧
            (∀ A : Finset (Fin n),
              (∑ t : Fin k, (lam t : ℝ) * (subspaceLoad u (U t) A : ℝ)) ≤
                ∑ r : Fin h, gam r * (subspaceLoad u (C r) A : ℝ)) ∧
            (∑ t : Fin k, (lam t : ℝ) * (Module.finrank F (U t) : ℝ)) =
              ∑ r : Fin h, gam r * (Module.finrank F (C r) : ℝ) := by
      intro k U lam hlam
      let Z : ℕ := ∏ t : Fin k, (lam t).den
      have hZ_pos : 0 < Z := Finset.prod_pos fun t _ => Rat.den_pos (lam t)
      have hZ_real_pos : (0 : ℝ) < (Z : ℝ) := Nat.cast_pos.mpr hZ_pos
      have hZ_ne : (Z : ℝ) ≠ 0 := hZ_real_pos.ne'
      let c : Fin k → ℕ := fun t =>
        (lam t).num.toNat * ∏ t' ∈ Finset.univ.erase t, (lam t').den
      have hc_real : ∀ t : Fin k, (c t : ℝ) = (Z : ℝ) * (lam t : ℝ) := by
        intro t
        have hnum_nn : 0 ≤ (lam t).num := Rat.num_nonneg.mpr (hlam t).2
        have htoNat : ((lam t).num.toNat : ℝ) = ((lam t).num : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hnum_nn
        have hZ_split : (Z : ℝ) =
            ((lam t).den : ℝ) * ((∏ t' ∈ Finset.univ.erase t, (lam t').den : ℕ) : ℝ) := by
          have hmul := Finset.mul_prod_erase Finset.univ (fun t' => (lam t').den) (Finset.mem_univ t)
          exact_mod_cast hmul.symm
        have hden_ne : ((lam t).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Rat.den_pos (lam t)).ne'
        dsimp only [c]
        rw [Nat.cast_mul, htoNat, hZ_split, Rat.cast_def]
        field_simp
      let Idx := Σ t : Fin k, Fin (c t)
      let M : ℕ := Fintype.card Idx
      let e : Idx ≃ Fin M := Fintype.equivFin Idx
      let W₀ : Fin M → Submodule F (Fin d → F) := fun s => U (e.symm s).1
      have hW₀_test : ∀ s : Fin M, W₀ s ≤ matroidSpan u S := fun s => (hlam (e.symm s).1).1
      have hW₀_sum : ∀ f : Submodule F (Fin d → F) → ℝ,
          (∑ s : Fin M, f (W₀ s)) = (Z : ℝ) * ∑ t : Fin k, (lam t : ℝ) * f (U t) := by
        intro f
        have h1 : (∑ s : Fin M, f (W₀ s)) = ∑ p : Idx, f (U p.1) :=
          e.symm.sum_comp (fun p : Idx => f (U p.1))
        rw [h1, Fintype.sum_sigma]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [hc_real t, mul_assoc]
      have h_sq_le : ∀ W : Fin M → Submodule F (Fin d → F),
          ∑ s : Fin M, (Module.finrank F (W s)) ^ 2 ≤ (∑ s : Fin M, Module.finrank F (W s)) ^ 2 := by
        intro W
        have h1 : ∑ s : Fin M, (Module.finrank F (W s)) ^ 2 ≤
            ∑ s : Fin M, Module.finrank F (W s) * ∑ s' : Fin M, Module.finrank F (W s') := by
          refine Finset.sum_le_sum fun s _ => ?_
          rw [sq]
          exact Nat.mul_le_mul_left _
            (Finset.single_le_sum (f := fun s' => Module.finrank F (W s'))
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ s))
        rwa [← Finset.sum_mul, ← sq] at h1
      let pot : (Fin M → Submodule F (Fin d → F)) → ℕ :=
        fun W => (∑ s : Fin M, Module.finrank F (W s)) ^ 2 - ∑ s : Fin M, (Module.finrank F (W s)) ^ 2
      have h_uncross : ∀ (K : ℕ) (W : Fin M → Submodule F (Fin d → F)),
          pot W = K → (∀ s, W s ≤ matroidSpan u S) →
          ∃ W' : Fin M → Submodule F (Fin d → F),
            (∀ s, W' s ≤ matroidSpan u S) ∧
            (∀ s₁ s₂ : Fin M, W' s₁ ≤ W' s₂ ∨ W' s₂ ≤ W' s₁) ∧
            (∀ A, ∑ s, subspaceLoad u (W s) A ≤ ∑ s, subspaceLoad u (W' s) A) ∧
            (∑ s, Module.finrank F (W s) = ∑ s, Module.finrank F (W' s)) := by
        intro K
        induction K using Nat.strong_induction_on with
        | h K ih =>
          intro W hpot hW_test
          by_cases hcomp : ∀ s₁ s₂ : Fin M, W s₁ ≤ W s₂ ∨ W s₂ ≤ W s₁
          · exact ⟨W, hW_test, hcomp, fun _ => le_rfl, rfl⟩
          · push_neg at hcomp
            rcases hcomp with ⟨s₁, s₂, hnot12, hnot21⟩
            have hs12 : s₁ ≠ s₂ := fun heq => hnot12 (heq ▸ le_rfl)
            let W₁ := Function.update (Function.update W s₁ (W s₁ ⊓ W s₂)) s₂ (W s₁ ⊔ W s₂)
            obtain ⟨hinf_test, hsup_test, hdim_pair, hload_pair⟩ :=
              h_supermod (W s₁) (W s₂) (hW_test s₁) (hW_test s₂)
            have hW₁_test : ∀ s, W₁ s ≤ matroidSpan u S := by
              intro s
              by_cases hs2 : s = s₂
              · subst hs2; simp only [W₁, Function.update_self]; exact hsup_test
              · by_cases hs1 : s = s₁
                · subst hs1; simp only [W₁, Function.update_of_ne hs2, Function.update_self]; exact hinf_test
                · simp only [W₁, Function.update_of_ne hs2, Function.update_of_ne hs1]; exact hW_test s
            have h_sum_two : ∀ g : Submodule F (Fin d → F) → ℕ,
                (∑ s : Fin M, g (W s)) =
                  g (W s₁) + (g (W s₂) + ∑ s ∈ (Finset.univ.erase s₁).erase s₂, g (W s)) ∧
                (∑ s : Fin M, g (W₁ s)) =
                  g (W s₁ ⊓ W s₂) + (g (W s₁ ⊔ W s₂) + ∑ s ∈ (Finset.univ.erase s₁).erase s₂, g (W s)) := by
              intro g
              have hs2_mem : s₂ ∈ (Finset.univ : Finset (Fin M)).erase s₁ :=
                Finset.mem_erase.mpr ⟨hs12.symm, Finset.mem_univ s₂⟩
              constructor
              · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s₁),
                    ← Finset.add_sum_erase _ _ hs2_mem]
              · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s₁),
                    ← Finset.add_sum_erase _ _ hs2_mem]
                have hW1_s1 : W₁ s₁ = W s₁ ⊓ W s₂ := by simp [W₁, Function.update_of_ne hs12]
                have hW1_s2 : W₁ s₂ = W s₁ ⊔ W s₂ := by simp [W₁]
                have h_rest : ∑ s ∈ (Finset.univ.erase s₁).erase s₂, g (W₁ s) =
                    ∑ s ∈ (Finset.univ.erase s₁).erase s₂, g (W s) := by
                  refine Finset.sum_congr rfl fun s hs => ?_
                  have hne2 : s ≠ s₂ := (Finset.mem_erase.mp hs).1
                  have hne1 : s ≠ s₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hs).2).1
                  simp [W₁, Function.update_of_ne hne2, Function.update_of_ne hne1]
                rw [hW1_s1, hW1_s2, h_rest]
            have hdim_sum : ∑ s, Module.finrank F (W₁ s) = ∑ s, Module.finrank F (W s) := by
              obtain ⟨hW_eq, hW1_eq⟩ := h_sum_two (fun X => Module.finrank F X)
              omega
            have hload_sum : ∀ A, ∑ s, subspaceLoad u (W s) A ≤ ∑ s, subspaceLoad u (W₁ s) A := by
              intro A
              obtain ⟨hW_eq, hW1_eq⟩ := h_sum_two (fun X => subspaceLoad u X A)
              have hlp := hload_pair A
              omega
            have hdrop1 : Module.finrank F ↥(W s₁ ⊓ W s₂) < Module.finrank F (W s₁) :=
              h_strict_drop (W s₁) (W s₂) hnot12
            have hdrop2 : Module.finrank F ↥(W s₁ ⊓ W s₂) < Module.finrank F (W s₂) := by
              have hd := h_strict_drop (W s₂) (W s₁) hnot21
              have heq : (W s₂ ⊓ W s₁ : Submodule F (Fin d → F)) = W s₁ ⊓ W s₂ := inf_comm _ _
              rwa [congr_arg (fun M : Submodule F _ => Module.finrank F M) heq] at hd
            have hsq_arith : ∀ a b c m : ℕ, a + b = c + m → c < a → c < b →
                a ^ 2 + b ^ 2 + 2 ≤ c ^ 2 + m ^ 2 := by
              intro a b c m h1 h2 h3
              obtain ⟨d1, rfl⟩ : ∃ d1, a = c + (d1 + 1) := ⟨a - c - 1, by omega⟩
              obtain ⟨d2, rfl⟩ : ∃ d2, b = c + (d2 + 1) := ⟨b - c - 1, by omega⟩
              obtain rfl : m = c + d1 + d2 + 2 := by omega
              have hid : (c + (d1 + 1)) ^ 2 + (c + (d2 + 1)) ^ 2 + 2 * (d1 * d2 + d1 + d2 + 1) =
                  c ^ 2 + (c + d1 + d2 + 2) ^ 2 := by ring
              omega
            have hsq_jump : (Module.finrank F (W s₁)) ^ 2 + (Module.finrank F (W s₂)) ^ 2 + 2 ≤
                (Module.finrank F ↥(W s₁ ⊓ W s₂)) ^ 2 + (Module.finrank F ↥(W s₁ ⊔ W s₂)) ^ 2 :=
              hsq_arith _ _ _ _ hdim_pair hdrop1 hdrop2
            have hsq_sum : ∑ s, (Module.finrank F (W s)) ^ 2 + 2 ≤ ∑ s, (Module.finrank F (W₁ s)) ^ 2 := by
              obtain ⟨hW_eq, hW1_eq⟩ := h_sum_two (fun X => (Module.finrank F X) ^ 2)
              omega
            have hW1_sq_le := h_sq_le W₁
            have hsq_tot_eq : (∑ s, Module.finrank F (W₁ s)) ^ 2 = (∑ s, Module.finrank F (W s)) ^ 2 := by
              rw [hdim_sum]
            have hpot_lt : pot W₁ < K := by
              dsimp only [pot] at hpot ⊢
              omega
            obtain ⟨W', hW'_test, hW'_comp, hW'_load, hW'_dim⟩ :=
              ih (pot W₁) hpot_lt W₁ rfl hW₁_test
            exact ⟨W', hW'_test, hW'_comp,
              fun A => (hload_sum A).trans (hW'_load A), hdim_sum.symm.trans hW'_dim⟩
      obtain ⟨W', hW'_test, hW'_comp, hW'_load, hW'_dim⟩ :=
        h_uncross (pot W₀) W₀ rfl hW₀_test
      let σ : Equiv.Perm (Fin M) := Tuple.sort (fun s => Module.finrank F (W' s))
      let C : Fin M → Submodule F (Fin d → F) := fun r => W' (σ r)
      let gam : Fin M → ℝ := fun _ => (1 : ℝ) / (Z : ℝ)
      refine ⟨M, C, gam, ?_, ?_, ?_, ?_⟩
      · intro r
        exact ⟨hW'_test (σ r), by dsimp only [gam]; positivity⟩
      · intro r₁ r₂ hr12
        have hmono_dim : Module.finrank F (C r₁) ≤ Module.finrank F (C r₂) :=
          Tuple.monotone_sort (fun s => Module.finrank F (W' s)) hr12
        rcases hW'_comp (σ r₁) (σ r₂) with h12 | h21
        · exact h12
        · by_contra hnot
          have hdrop := h_strict_drop (C r₁) (C r₂) hnot
          have hinf_eq : C r₁ ⊓ C r₂ = C r₂ := inf_of_le_right h21
          rw [congr_arg (fun N : Submodule F _ => Module.finrank F N) hinf_eq] at hdrop
          omega
      · intro A
        have h_rhs : (∑ r : Fin M, gam r * (subspaceLoad u (C r) A : ℝ)) =
            ((1 : ℝ) / (Z : ℝ)) * ∑ s : Fin M, (subspaceLoad u (W' s) A : ℝ) := by
          dsimp only [gam, C]
          rw [← Finset.mul_sum]
          congr 1
          exact Equiv.sum_comp σ (fun s => (subspaceLoad u (W' s) A : ℝ))
        have h_le_real : (∑ s : Fin M, (subspaceLoad u (W₀ s) A : ℝ)) ≤
            ∑ s : Fin M, (subspaceLoad u (W' s) A : ℝ) := by exact_mod_cast hW'_load A
        have h_lhs : (∑ s : Fin M, (subspaceLoad u (W₀ s) A : ℝ)) =
            (Z : ℝ) * ∑ t : Fin k, (lam t : ℝ) * (subspaceLoad u (U t) A : ℝ) :=
          hW₀_sum (fun X => (subspaceLoad u X A : ℝ))
        rw [h_rhs]
        calc
          (∑ t : Fin k, (lam t : ℝ) * (subspaceLoad u (U t) A : ℝ))
              = ((1 : ℝ) / (Z : ℝ)) * ((Z : ℝ) * ∑ t : Fin k, (lam t : ℝ) * (subspaceLoad u (U t) A : ℝ)) := by
                  field_simp
          _ = ((1 : ℝ) / (Z : ℝ)) * ∑ s : Fin M, (subspaceLoad u (W₀ s) A : ℝ) := by rw [h_lhs]
          _ ≤ ((1 : ℝ) / (Z : ℝ)) * ∑ s : Fin M, (subspaceLoad u (W' s) A : ℝ) :=
              mul_le_mul_of_nonneg_left h_le_real (by positivity)
      · have h_rhs : (∑ r : Fin M, gam r * (Module.finrank F (C r) : ℝ)) =
            ((1 : ℝ) / (Z : ℝ)) * ∑ s : Fin M, (Module.finrank F (W' s) : ℝ) := by
          dsimp only [gam, C]
          rw [← Finset.mul_sum]
          congr 1
          exact Equiv.sum_comp σ (fun s => (Module.finrank F (W' s) : ℝ))
        have h_eq_real : (∑ s : Fin M, (Module.finrank F (W₀ s) : ℝ)) =
            ∑ s : Fin M, (Module.finrank F (W' s) : ℝ) := by exact_mod_cast hW'_dim
        have h_lhs : (∑ s : Fin M, (Module.finrank F (W₀ s) : ℝ)) =
            (Z : ℝ) * ∑ t : Fin k, (lam t : ℝ) * (Module.finrank F (U t) : ℝ) :=
          hW₀_sum (fun X => (Module.finrank F X : ℝ))
        rw [h_rhs, ← h_eq_real, h_lhs]
        field_simp
    have hB_ne_zero : ∀ g ∈ B, u g ≠ 0 :=
      fun g hgB => hB_indep.ne_zero (⟨g, hgB⟩ : ↥B)
    have h_prop_count : ∀ W : Submodule F (Fin d → F),
        (B.filter (fun g => u g ∈ W)).card ≤ Module.finrank F W := by
      intro W
      let B_hit := B.filter (fun g => u g ∈ W)
      let ι : ↥B_hit → ↥B := fun x => ⟨x.1, (Finset.mem_filter.mp x.2).1⟩
      have hι_inj : Function.Injective ι := fun _ _ h => Subtype.ext (Subtype.mk.inj h)
      have hli_hit : LinearIndependent F (fun x : ↥B_hit => u x.1) := hB_indep.comp ι hι_inj
      let f_sub : ↥B_hit → ↥W := fun x => ⟨u x.1, (Finset.mem_filter.mp x.2).2⟩
      have hli_sub : LinearIndependent F f_sub := LinearIndependent.of_comp W.subtype hli_hit
      have hcard := LinearIndependent.fintype_card_le_finrank hli_sub
      rwa [Fintype.card_coe] at hcard
    let E := Fin n → Finset (Fin n) → ℝ
    let upper : Fin n → Finset (Fin n) → ℝ := fun g A =>
      if g ∈ B ∧ IsExtFeas g A then μ_g g A else 0
    let AdmPolytope : Set E :=
      {q | (∀ g A, 0 ≤ q g A) ∧ (∀ g A, q g A ≤ upper g A) ∧ (∀ g ∈ B, (∑ A, q g A) = a)}
    let ν_of : E → Fin n → Finset (Fin n) → ℝ := fun q g C' =>
      μ_g g C' + (∑ A, if insert g A = C' then q g A else 0) - q g C'
    let μ_avg_of : E → Finset (Fin n) → ℝ := fun q C' =>
      (1 / (S.card : ℝ)) * ∑ g ∈ S, ν_of q g C'
    have h_avg_feas : ∀ q ∈ AdmPolytope, IsIndepSetLaw u S (μ_avg_of q) := by
      intro q ⟨hq_nn, hq_up, _⟩
      have hν_law : ∀ g ∈ S, IsIndepSetLaw u S (ν_of q g) := by
        intro g hgS
        obtain ⟨hμ_nn, hμ_supp, hμ_sum⟩ := (hμ g hgS).2.1
        have hq_le_μ : ∀ C', q g C' ≤ μ_g g C' := by
          intro C'
          refine (hq_up g C').trans ?_
          dsimp only [upper]
          split_ifs
          · exact le_rfl
          · exact hμ_nn C'
        refine ⟨?_, ?_, ?_⟩
        · intro C'
          have h1 := hq_le_μ C'
          have h2 : 0 ≤ ∑ A, if insert g A = C' then q g A else 0 :=
            Finset.sum_nonneg (fun A _ => by split_ifs; exact hq_nn g A; exact le_rfl)
          dsimp only [ν_of]
          linarith
        · intro C' hν_ne
          by_cases hμC : μ_g g C' = 0
          · have hqC0 : q g C' = 0 := le_antisymm ((hq_le_μ C').trans hμC.le) (hq_nn g C')
            have hsum_ne : (∑ A, if insert g A = C' then q g A else 0) ≠ 0 := by
              intro hs; apply hν_ne; dsimp only [ν_of]; linarith
            obtain ⟨A, _, hite_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
            split_ifs at hite_ne with hext
            · have hup_ne : upper g A ≠ 0 :=
                fun h0 => hite_ne (le_antisymm ((hq_up g A).trans h0.le) (hq_nn g A))
              have hcond : g ∈ B ∧ IsExtFeas g A := by
                by_contra hnc; apply hup_ne; simp [upper, hnc]
              rw [← hext]
              exact ⟨hcond.2.2.1, hcond.2.2.2⟩
            · exact absurd rfl hite_ne
          · exact hμ_supp C' hμC
        · have h_swap : (∑ C', ∑ A, if insert g A = C' then q g A else 0) = ∑ A, q g A := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun A _ => by simp [Finset.sum_ite_eq]
          have h_dist : (∑ C', ν_of q g C') =
              (∑ C', μ_g g C') + (∑ C', ∑ A, if insert g A = C' then q g A else 0) - ∑ C', q g C' := by
            simp only [ν_of, sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
          linarith
      refine ⟨?_, ?_, ?_⟩
      · intro C'
        dsimp only [μ_avg_of]
        exact mul_nonneg (by positivity) (Finset.sum_nonneg fun g hgS => (hν_law g hgS).1 C')
      · intro C' havg_ne
        have hsum_ne : (∑ g ∈ S, ν_of q g C') ≠ 0 := by
          intro hs; apply havg_ne; dsimp only [μ_avg_of]; rw [hs, mul_zero]
        obtain ⟨g, hgS, hνg_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
        exact (hν_law g hgS).2.1 C' hνg_ne
      · dsimp only [μ_avg_of]
        rw [← Finset.mul_sum, Finset.sum_comm]
        have h_each : ∑ g ∈ S, ∑ C', ν_of q g C' = ∑ _ ∈ S, (1 : ℝ) :=
          Finset.sum_congr rfl fun g hgS => (hν_law g hgS).2.2
        rw [h_each, Finset.sum_const, nsmul_eq_mul, mul_one]
        field_simp [hS_ne]

    have h_multirow_chain : ∀ (h : ℕ) (C : Fin h → Submodule F (Fin d → F)),
        (∀ r₁ r₂ : Fin h, r₁ ≤ r₂ → C r₁ ≤ C r₂) →
          ∃ q ∈ AdmPolytope,
            ∀ r : Fin h,
              (∑ C', μ_avg_of q C' * (subspaceLoad u (C r) C' : ℝ)) ≤
                (β + a / (S.card : ℝ)) * (Module.finrank F (C r) : ℝ) := by
      intro h C hC_mono
      have h_ex_g : ∀ g : Fin n, g ∈ B →
          ∃ qg : Finset (Fin n) → ℝ,
            (∀ A, 0 ≤ qg A ∧ qg A ≤ μ_g g A) ∧
            (∀ A, qg A ≠ 0 → IsExtFeas g A) ∧
            (∑ A, qg A) = a ∧
            ∀ r : Fin h,
              (∑ C', (μ_g g C' + (∑ A, if insert g A = C' then qg A else 0) - qg C') *
                  (subspaceLoad u (C r) C' : ℝ)) ≤
                β * (Module.finrank F (C r) : ℝ) + (if u g ∈ C r then a else 0) :=
        fun g hgB => h_chain_single g h C (hBS hgB) (hB_ne_zero g hgB) hC_mono
      let q : E := fun g => if hgB : g ∈ B then Classical.choose (h_ex_g g hgB) else fun _ => 0
      have hq_mem : q ∈ AdmPolytope := by
        refine ⟨?_, ?_, ?_⟩
        · intro g A
          dsimp only [q]
          split_ifs with hgB
          · exact ((Classical.choose_spec (h_ex_g g hgB)).1 A).1
          · exact le_rfl
        · intro g A
          dsimp only [q, upper]
          by_cases hgB : g ∈ B
          · simp only [hgB, ↓reduceDIte, true_and]
            obtain ⟨hq_bd, hq_supp, _, _⟩ := Classical.choose_spec (h_ex_g g hgB)
            split_ifs with hfeas
            · exact (hq_bd A).2
            · by_contra hgt
              have hne : Classical.choose (h_ex_g g hgB) A ≠ 0 := by
                have h0 := (hq_bd A).1; linarith
              exact hfeas (hq_supp A hne)
          · simp only [hgB, ↓reduceDIte, false_and, ↓reduceIte, le_rfl]
        · intro g hgB
          dsimp only [q]
          rw [dif_pos hgB]
          exact (Classical.choose_spec (h_ex_g g hgB)).2.2.1
      refine ⟨q, hq_mem, fun r => ?_⟩
      have h_g_load : ∀ g ∈ S,
          (∑ C', ν_of q g C' * (subspaceLoad u (C r) C' : ℝ)) ≤
            β * (Module.finrank F (C r) : ℝ) + (if g ∈ B ∧ u g ∈ C r then a else 0) := by
        intro g hgS
        by_cases hgB : g ∈ B
        · have hqg_eq : q g = Classical.choose (h_ex_g g hgB) := dif_pos hgB
          have hr_bd := (Classical.choose_spec (h_ex_g g hgB)).2.2.2 r
          simp only [hgB, true_and]
          dsimp only [ν_of]
          rwa [hqg_eq]
        · have hqg_eq : q g = fun _ => 0 := dif_neg hgB
          simp only [hgB, false_and, ↓reduceIte, add_zero]
          have hν_eq : ∀ C', ν_of q g C' = μ_g g C' := by
            intro C'; dsimp only [ν_of]; rw [hqg_eq]; simp
          simp_rw [hν_eq]
          exact (hμ g hgS).2.2 (C r)
      have h_sum_S :
          (∑ g ∈ S, ∑ C', ν_of q g C' * (subspaceLoad u (C r) C' : ℝ)) ≤
            (S.card : ℝ) * (β * (Module.finrank F (C r) : ℝ)) + a * (Module.finrank F (C r) : ℝ) := by
        have h1 := Finset.sum_le_sum h_g_load
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h1
        have h_filt :
            (∑ g ∈ S, if g ∈ B ∧ u g ∈ C r then a else 0) =
              ((B.filter (fun g => u g ∈ C r)).card : ℝ) * a := by
          rw [← Finset.sum_filter]
          have hset : S.filter (fun g => g ∈ B ∧ u g ∈ C r) = B.filter (fun g => u g ∈ C r) := by
            ext g
            simp only [Finset.mem_filter]
            exact ⟨fun ⟨_, hgB, hm⟩ => ⟨hgB, hm⟩, fun ⟨hgB, hm⟩ => ⟨hBS hgB, hgB, hm⟩⟩
          rw [hset, Finset.sum_const, nsmul_eq_mul]
        have h_cnt : ((B.filter (fun g => u g ∈ C r)).card : ℝ) ≤ (Module.finrank F (C r) : ℝ) :=
          Nat.cast_le.mpr (h_prop_count (C r))
        have h_amul := mul_le_mul_of_nonneg_right h_cnt ha0
        linarith
      have h_lhs_eq :
          (∑ C', μ_avg_of q C' * (subspaceLoad u (C r) C' : ℝ)) =
            (1 / (S.card : ℝ)) * ∑ g ∈ S, ∑ C', ν_of q g C' * (subspaceLoad u (C r) C' : ℝ) := by
        dsimp only [μ_avg_of]
        have h1 : (∑ C', ((1 / (S.card : ℝ)) * ∑ g ∈ S, ν_of q g C') * (subspaceLoad u (C r) C' : ℝ)) =
            (1 / (S.card : ℝ)) * ∑ C', (∑ g ∈ S, ν_of q g C') * (subspaceLoad u (C r) C' : ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun C' _ => by ring
        rw [h1]
        congr 1
        simp_rw [Finset.sum_mul]
        exact Finset.sum_comm
      rw [h_lhs_eq]
      have hmul := mul_le_mul_of_nonneg_left h_sum_S (by positivity : (0 : ℝ) ≤ 1 / (S.card : ℝ))
      have h_rhs_id :
          (1 / (S.card : ℝ)) *
            ((S.card : ℝ) * (β * (Module.finrank F (C r) : ℝ)) + a * (Module.finrank F (C r) : ℝ)) =
            (β + a / (S.card : ℝ)) * (Module.finrank F (C r) : ℝ) := by
        field_simp [hS_ne]
      linarith
    letI : Fintype (Submodule F (Fin d → F)) :=
      Fintype.ofInjective SetLike.coe SetLike.coe_injective
    let Tests : Finset (Submodule F (Fin d → F)) :=
      Finset.univ.filter (fun U => U ≤ matroidSpan u S)
    let k : ℕ := Tests.card
    let eT : ↥Tests ≃ Fin k := Tests.equivFin
    let U_all : Fin k → Submodule F (Fin d → F) := fun t => (eT.symm t).1
    have hU_all_test : ∀ t : Fin k, U_all t ≤ matroidSpan u S :=
      fun t => (Finset.mem_filter.mp (eT.symm t).2).2
    let Box : Set E :=
      Set.univ.pi (fun g => Set.univ.pi (fun A => Set.Icc (0 : ℝ) (upper g A)))
    let Hyp : Set E := ⋂ g ∈ (B : Set (Fin n)), {q : E | (∑ A, q g A) = a}
    have hAdm_eq : AdmPolytope = Box ∩ Hyp := by
      ext q
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨fun g _ A _ => ⟨h1 g A, h2 g A⟩, ?_⟩
        simp only [Hyp, Set.mem_iInter, Finset.mem_coe, Set.mem_setOf_eq]
        exact h3
      · rintro ⟨hBox, hHyp⟩
        simp only [Hyp, Set.mem_iInter, Finset.mem_coe, Set.mem_setOf_eq] at hHyp
        exact ⟨fun g A => (hBox g (Set.mem_univ g) A (Set.mem_univ A)).1,
               fun g A => (hBox g (Set.mem_univ g) A (Set.mem_univ A)).2,
               hHyp⟩
    have hBox_comp : IsCompact Box :=
      isCompact_univ_pi (fun g => isCompact_univ_pi (fun A => isCompact_Icc))
    have hHyp_closed : IsClosed Hyp := by
      refine isClosed_biInter (fun g _ => ?_)
      refine isClosed_eq ?_ continuous_const
      exact continuous_finset_sum _ (fun A _ => (continuous_apply A).comp (continuous_apply g))
    have hQ_comp : IsCompact AdmPolytope := hAdm_eq ▸ hBox_comp.inter_right hHyp_closed
    have hQ_conv : Convex ℝ AdmPolytope := by
      intro q₁ ⟨hq₁_nn, hq₁_up, hq₁_sum⟩ q₂ ⟨hq₂_nn, hq₂_up, hq₂_sum⟩ a₁ a₂ ha₁ ha₂ hab
      refine ⟨?_, ?_, ?_⟩
      · intro g A
        change 0 ≤ a₁ * q₁ g A + a₂ * q₂ g A
        exact add_nonneg (mul_nonneg ha₁ (hq₁_nn g A)) (mul_nonneg ha₂ (hq₂_nn g A))
      · intro g A
        change a₁ * q₁ g A + a₂ * q₂ g A ≤ upper g A
        calc
          a₁ * q₁ g A + a₂ * q₂ g A
              ≤ a₁ * upper g A + a₂ * upper g A :=
                add_le_add (mul_le_mul_of_nonneg_left (hq₁_up g A) ha₁)
                  (mul_le_mul_of_nonneg_left (hq₂_up g A) ha₂)
          _ = (a₁ + a₂) * upper g A := by ring
          _ = upper g A := by rw [hab, one_mul]
      · intro g hgB
        change (∑ A, (a₁ * q₁ g A + a₂ * q₂ g A)) = a
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hq₁_sum g hgB, hq₂_sum g hgB]
        calc
          a₁ * a + a₂ * a = (a₁ + a₂) * a := by ring
          _ = a := by rw [hab, one_mul]
    have hQ_ne : AdmPolytope.Nonempty := by
      obtain ⟨q₀, hq₀_mem, _⟩ := h_multirow_chain 0 Fin.elim0 (fun r₁ => r₁.elim0)
      exact ⟨q₀, hq₀_mem⟩
    let φ : Fin k → E → ℝ := fun t q =>
      (∑ C', μ_avg_of q C' * (subspaceLoad u (U_all t) C' : ℝ)) -
        (β + a / (S.card : ℝ)) * (Module.finrank F (U_all t) : ℝ)
    have hν_cont : ∀ g C', Continuous (fun q : E => ν_of q g C') := by
      intro g C'
      dsimp only [ν_of]
      refine (continuous_const.add ?_).sub ((continuous_apply C').comp (continuous_apply g))
      refine continuous_finset_sum _ (fun A _ => ?_)
      split_ifs
      · exact (continuous_apply A).comp (continuous_apply g)
      · exact continuous_const
    have havg_cont : ∀ C', Continuous (fun q : E => μ_avg_of q C') := by
      intro C'
      dsimp only [μ_avg_of]
      exact continuous_const.mul (continuous_finset_sum _ (fun g _ => hν_cont g C'))
    have hφ_cont : ∀ t : Fin k, ContinuousOn (φ t) AdmPolytope := by
      intro t
      refine Continuous.continuousOn ?_
      dsimp only [φ]
      exact (continuous_finset_sum _ (fun C' _ => (havg_cont C').mul continuous_const)).sub continuous_const
    have hφ_aff : ∀ t : Fin k, ∀ q₁ ∈ AdmPolytope, ∀ q₂ ∈ AdmPolytope, ∀ a₁ a₂ : ℝ,
        0 ≤ a₁ → 0 ≤ a₂ → a₁ + a₂ = 1 → φ t (a₁ • q₁ + a₂ • q₂) = a₁ * φ t q₁ + a₂ * φ t q₂ := by
      intro t q₁ _ q₂ _ a₁ a₂ _ _ hab
      have hν_aff : ∀ g C', ν_of (a₁ • q₁ + a₂ • q₂) g C' = a₁ * ν_of q₁ g C' + a₂ * ν_of q₂ g C' := by
        intro g C'
        dsimp only [ν_of]
        have h_ite : (∑ A, if insert g A = C' then (a₁ • q₁ + a₂ • q₂) g A else 0) =
            a₁ * (∑ A, if insert g A = C' then q₁ g A else 0) +
            a₂ * (∑ A, if insert g A = C' then q₂ g A else 0) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun A _ => ?_)
          split_ifs
          · rfl
          · ring
        have hqC : (a₁ • q₁ + a₂ • q₂) g C' = a₁ * q₁ g C' + a₂ * q₂ g C' := rfl
        have hμ1 : μ_g g C' = (a₁ + a₂) * μ_g g C' := by rw [hab, one_mul]
        rw [h_ite, hqC]
        linarith
      have havg_aff : ∀ C', μ_avg_of (a₁ • q₁ + a₂ • q₂) C' = a₁ * μ_avg_of q₁ C' + a₂ * μ_avg_of q₂ C' := by
        intro C'
        dsimp only [μ_avg_of]
        simp_rw [hν_aff]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        ring
      dsimp only [φ]
      simp_rw [havg_aff, add_mul]
      rw [Finset.sum_add_distrib]
      have h1 : (∑ C', a₁ * μ_avg_of q₁ C' * (subspaceLoad u (U_all t) C' : ℝ)) =
          a₁ * ∑ C', μ_avg_of q₁ C' * (subspaceLoad u (U_all t) C' : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun C' _ => by ring
      have h2 : (∑ C', a₂ * μ_avg_of q₂ C' * (subspaceLoad u (U_all t) C' : ℝ)) =
          a₂ * ∑ C', μ_avg_of q₂ C' * (subspaceLoad u (U_all t) C' : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun C' _ => by ring
      have hc : (β + a / (S.card : ℝ)) * (Module.finrank F (U_all t) : ℝ) =
          (a₁ + a₂) * ((β + a / (S.card : ℝ)) * (Module.finrank F (U_all t) : ℝ)) := by
        rw [hab, one_mul]
      rw [h1, h2]
      linarith
    have h_rat : ∀ lam : Fin k → ℚ, (∀ t : Fin k, 0 ≤ lam t) →
        ∃ q ∈ AdmPolytope, (∑ t : Fin k, (lam t : ℝ) * φ t q) ≤ 0 := by
      intro lam hlam_nn
      obtain ⟨h, C, gam, hC_tg, hC_mono, hC_load, hC_dim⟩ :=
        h_uncross_rat U_all lam (fun t => ⟨hU_all_test t, hlam_nn t⟩)
      obtain ⟨q, hq_mem, hq_chain⟩ := h_multirow_chain h C hC_mono
      have hq_feas := h_avg_feas q hq_mem
      refine ⟨q, hq_mem, ?_⟩
      have h_lhs_split :
          (∑ t : Fin k, (lam t : ℝ) * φ t q) =
            (∑ C', μ_avg_of q C' * ∑ t : Fin k, (lam t : ℝ) * (subspaceLoad u (U_all t) C' : ℝ)) -
              (β + a / (S.card : ℝ)) * ∑ t : Fin k, (lam t : ℝ) * (Module.finrank F (U_all t) : ℝ) := by
        dsimp only [φ]
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
        congr 1
        · have h1 : (∑ t : Fin k, (lam t : ℝ) * ∑ C', μ_avg_of q C' * (subspaceLoad u (U_all t) C' : ℝ)) =
              ∑ t : Fin k, ∑ C', μ_avg_of q C' * ((lam t : ℝ) * (subspaceLoad u (U_all t) C' : ℝ)) := by
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun C' _ => by ring
          rw [h1, Finset.sum_comm]
          exact Finset.sum_congr rfl fun C' _ => (Finset.mul_sum _ _ _).symm
        · rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun t _ => by ring
      have h_rhs_split :
          (∑ r : Fin h, gam r * ((∑ C', μ_avg_of q C' * (subspaceLoad u (C r) C' : ℝ)) -
              (β + a / (S.card : ℝ)) * (Module.finrank F (C r) : ℝ))) =
            (∑ C', μ_avg_of q C' * ∑ r : Fin h, gam r * (subspaceLoad u (C r) C' : ℝ)) -
              (β + a / (S.card : ℝ)) * ∑ r : Fin h, gam r * (Module.finrank F (C r) : ℝ) := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
        congr 1
        · have h1 : (∑ r : Fin h, gam r * ∑ C', μ_avg_of q C' * (subspaceLoad u (C r) C' : ℝ)) =
              ∑ r : Fin h, ∑ C', μ_avg_of q C' * (gam r * (subspaceLoad u (C r) C' : ℝ)) := by
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun C' _ => by ring
          rw [h1, Finset.sum_comm]
          exact Finset.sum_congr rfl fun C' _ => (Finset.mul_sum _ _ _).symm
        · rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun r _ => by ring
      have h_load_dom :
          (∑ C', μ_avg_of q C' * ∑ t : Fin k, (lam t : ℝ) * (subspaceLoad u (U_all t) C' : ℝ)) ≤
            ∑ C', μ_avg_of q C' * ∑ r : Fin h, gam r * (subspaceLoad u (C r) C' : ℝ) :=
        Finset.sum_le_sum fun C' _ => mul_le_mul_of_nonneg_left (hC_load C') (hq_feas.1 C')
      have h_chain_nonpos :
          (∑ r : Fin h, gam r * ((∑ C', μ_avg_of q C' * (subspaceLoad u (C r) C' : ℝ)) -
              (β + a / (S.card : ℝ)) * (Module.finrank F (C r) : ℝ))) ≤ 0 := by
        refine Finset.sum_nonpos fun r _ => ?_
        exact mul_nonpos_of_nonneg_of_nonpos (hC_tg r).2 (sub_nonpos.mpr (hq_chain r))
      rw [h_lhs_split, hC_dim]
      linarith
    obtain ⟨q, hq_mem, hq_le⟩ :=
      h_minimax_rat AdmPolytope φ hQ_comp hQ_conv hQ_ne hφ_cont hφ_aff h_rat
    obtain ⟨hq_nn, hq_up, hq_sum⟩ := hq_mem
    refine ⟨q, ?_, ?_, hq_sum, ?_⟩
    · intro g hgS A
      refine ⟨hq_nn g A, (hq_up g A).trans ?_⟩
      dsimp only [upper]
      split_ifs
      · exact le_rfl
      · exact (hμ g hgS).2.1.1 A
    · intro g _ A hq_ne
      have hup_ne : upper g A ≠ 0 :=
        fun h0 => hq_ne (le_antisymm ((hq_up g A).trans h0.le) (hq_nn g A))
      have hcond : g ∈ B ∧ IsExtFeas g A := by
        by_contra hnc; apply hup_ne; simp [upper, hnc]
      exact ⟨hcond.1, hcond.2.1, hcond.2.2.2⟩
    · have hlaw_avg : IsIndepSetLaw u S (μ_avg_of q) := h_avg_feas q ⟨hq_nn, hq_up, hq_sum⟩
      have hβ_avg_nn : 0 ≤ β + a / (S.card : ℝ) :=
        add_nonneg hβ0 (div_nonneg ha0 (le_of_lt hS_pos))
      refine (h_part1a u S (β + a / (S.card : ℝ)) (μ_avg_of q) hβ_avg_nn hlaw_avg).mpr ?_
      intro U hU
      have hU_mem : U ∈ Tests := Finset.mem_filter.mpr ⟨Finset.mem_univ U, hU⟩
      let t₀ : Fin k := eT ⟨U, hU_mem⟩
      have hU_eq : U_all t₀ = U := by
        dsimp only [U_all, t₀]
        rw [Equiv.symm_apply_apply]
      have hφ0 := hq_le t₀
      dsimp only [φ] at hφ0
      rw [hU_eq] at hφ0
      linarith
  have h_prog_full : ∀ (n d s : ℕ) (F : Type) [Field F] [Fintype F],
      1 ≤ s →
      (∀ (u : Fin n → (Fin d → F)) (P : Finset (Fin n) → Finset (Fin n)) (S : Finset (Fin n)),
        S.card ≤ s → abhmMuProg s F u P S = abhmEmptyLaw) ∧
      (∀ (u u' : Fin n → (Fin d → F)) (P P' : Finset (Fin n) → Finset (Fin n))
          (S : Finset (Fin n)),
        (∀ g ∈ S, u g = u' g) → (∀ T ⊆ S, P T = P' T) →
          abhmMuProg s F u P S = abhmMuProg s F u' P' S ∧
          abhmQProg s F u P S = abhmQProg s F u' P' S) ∧
      (∀ (u : Fin n → (Fin d → F)) (P : Finset (Fin n) → Finset (Fin n)),
        (∀ T : Finset (Fin n), P T ⊆ T ∧ LinearIndependent F (fun g : P T => u g.1)) →
        ∀ S : Finset (Fin n), s ≤ S.card →
          IsSubspaceBetaBounded u S (loadBeta s S.card) (abhmMuProg s F u P S)) ∧
      (∀ (u : Fin n → (Fin d → F)) (P : Finset (Fin n) → Finset (Fin n)),
        (∀ T : Finset (Fin n), P T ⊆ T ∧ LinearIndependent F (fun g : P T => u g.1)) →
        ∀ S : Finset (Fin n), s < S.card →
          (∀ g ∈ S, ∀ A, 0 ≤ abhmQProg s F u P S g A ∧
            abhmQProg s F u P S g A ≤ abhmMuProg s F u P (S.erase g) A) ∧
          (∀ g ∈ S, ∀ A, abhmQProg s F u P S g A ≠ 0 →
            g ∈ P S ∧ g ∉ A ∧
              LinearIndependent F (fun x : (insert g A : Finset (Fin n)) => u x.1)) ∧
          (∀ g ∈ P S, (∑ A, abhmQProg s F u P S g A) = admitRate s S.card) ∧
          (∀ C, abhmMuProg s F u P S C =
            abhmRowAvg S (fun g => abhmMuProg s F u P (S.erase g)) (abhmQProg s F u P S) C)) := by
    intro n d s F _ _ hs1
    have h_norm_loc : ∀ (k : ℕ) (u₁ u₂ : Fin n → (Fin d → F))
        (P₁ P₂ : Finset (Fin n) → Finset (Fin n)) (S : Finset (Fin n)),
        (∀ g ∈ S, u₁ g = u₂ g) → (∀ T ⊆ S, P₁ T = P₂ T) →
          abhmProgAux s k u₁ P₁ S = abhmProgAux s k u₂ P₂ S := by
      intro k u₁ u₂ P₁ P₂ S hu hP
      have hu_eq : abhmNormVec S u₁ = abhmNormVec S u₂ := by
        funext g; dsimp only [abhmNormVec]
        by_cases hg : g ∈ S
        · rw [if_pos hg, if_pos hg, hu g hg]
        · rw [if_neg hg, if_neg hg]
      have hP_eq : abhmNormProp S P₁ = abhmNormProp S P₂ := by
        funext T; dsimp only [abhmNormProp]
        by_cases hT : T ⊆ S
        · rw [if_pos hT, if_pos hT, hP T hT]
        · rw [if_neg hT, if_neg hT]
      cases k with
      | zero => rfl
      | succ k₀ =>
        unfold abhmProgAux
        rw [hu_eq, hP_eq]
    have h_le_s : ∀ (u : Fin n → (Fin d → F)) (P : Finset (Fin n) → Finset (Fin n))
        (S : Finset (Fin n)),
        S.card ≤ s → abhmMuProg s F u P S = abhmEmptyLaw := by
      intro u P S hle
      unfold abhmMuProg
      generalize hk : S.card = k
      rw [hk] at hle
      cases k with
      | zero => rfl
      | succ k₀ => simp [abhmProgAux, hle]
    have h_empty_bdd : ∀ (u : Fin n → (Fin d → F)) (S : Finset (Fin n)),
        IsSubspaceBetaBounded u S 0 abhmEmptyLaw := by
      intro u S
      have hlaw : IsIndepSetLaw u S abhmEmptyLaw := by
        refine ⟨?_, ?_, ?_⟩
        · intro A; dsimp only [abhmEmptyLaw]; split_ifs <;> norm_num
        · intro A hne
          by_cases hA : A = ∅
          · subst hA
            refine ⟨Finset.empty_subset S, ?_⟩
            rw [Fintype.linearIndependent_iff]
            intro c _ ⟨x, hx⟩
            exact absurd hx (Finset.notMem_empty x)
          · exfalso; apply hne; simp [abhmEmptyLaw, hA]
        · simp [abhmEmptyLaw]
      refine ⟨hlaw, fun U => ?_⟩
      rw [zero_mul]
      have hload0 : subspaceLoad u U ∅ = 0 := by
        have hspan0 : matroidSpan u ∅ = ⊥ := by simp [matroidSpan]
        unfold subspaceLoad
        rw [congr_arg (fun M : Submodule F (Fin d → F) => Module.finrank F M)
          (by rw [hspan0, bot_inf_eq])]
        exact finrank_bot F (Fin d → F)
      have hsum0 : (∑ A : Finset (Fin n), abhmEmptyLaw A * (subspaceLoad u U A : ℝ)) = 0 := by
        refine Finset.sum_eq_zero fun A _ => ?_
        by_cases hA : A = ∅
        · subst hA; simp [hload0]
        · simp [abhmEmptyLaw, hA]
      rw [hsum0]
    have h_li_norm : ∀ (u : Fin n → (Fin d → F)) (S X : Finset (Fin n)),
        X ⊆ S →
          (LinearIndependent F (fun g : X => abhmNormVec S u g.1) ↔
            LinearIndependent F (fun g : X => u g.1)) := by
      intro u S X hXS
      have hfun : (fun g : X => abhmNormVec S u g.1) = (fun g : X => u g.1) :=
        funext fun g => if_pos (hXS g.2)
      rw [hfun]
    have h_load_norm : ∀ (u : Fin n → (Fin d → F)) (S X : Finset (Fin n))
        (U : Submodule F (Fin d → F)),
        X ⊆ S → subspaceLoad (abhmNormVec S u) U X = subspaceLoad u U X := by
      intro u S X U hXS
      have himg : abhmNormVec S u '' (X : Set (Fin n)) = u '' (X : Set (Fin n)) :=
        Set.image_congr fun x hx => if_pos (hXS (Finset.mem_coe.mp hx))
      unfold subspaceLoad matroidSpan
      rw [himg]
    have h_law_norm : ∀ (u : Fin n → (Fin d → F)) (S T : Finset (Fin n))
        (μ : Finset (Fin n) → ℝ),
        T ⊆ S → (IsIndepSetLaw (abhmNormVec S u) T μ ↔ IsIndepSetLaw u T μ) := by
      intro u S T μ hTS
      constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨h1, ?_, h3⟩ <;> intro A hne
      · obtain ⟨hAT, hli⟩ := h2 A hne
        exact ⟨hAT, (h_li_norm u S A (hAT.trans hTS)).mp hli⟩
      · obtain ⟨hAT, hli⟩ := h2 A hne
        exact ⟨hAT, (h_li_norm u S A (hAT.trans hTS)).mpr hli⟩
    have h_beta_norm : ∀ (u : Fin n → (Fin d → F)) (S T : Finset (Fin n))
        (β : ℝ) (μ : Finset (Fin n) → ℝ),
        T ⊆ S →
          (IsSubspaceBetaBounded (abhmNormVec S u) T β μ ↔ IsSubspaceBetaBounded u T β μ) := by
      intro u S T β μ hTS
      constructor <;> rintro ⟨hlaw, hbdd⟩
      · have hlaw' := (h_law_norm u S T μ hTS).mp hlaw
        refine ⟨hlaw', fun U => ?_⟩
        have heq : (∑ A : Finset (Fin n), μ A * (subspaceLoad u U A : ℝ)) =
            ∑ A : Finset (Fin n), μ A * (subspaceLoad (abhmNormVec S u) U A : ℝ) := by
          refine Finset.sum_congr rfl fun A _ => ?_
          by_cases hμA : μ A = 0
          · simp [hμA]
          · rw [h_load_norm u S A U (((hlaw'.2.1 A hμA).1).trans hTS)]
        rw [heq]
        exact hbdd U
      · refine ⟨(h_law_norm u S T μ hTS).mpr hlaw, fun U => ?_⟩
        have heq : (∑ A : Finset (Fin n), μ A * (subspaceLoad (abhmNormVec S u) U A : ℝ)) =
            ∑ A : Finset (Fin n), μ A * (subspaceLoad u U A : ℝ) := by
          refine Finset.sum_congr rfl fun A _ => ?_
          by_cases hμA : μ A = 0
          · simp [hμA]
          · rw [h_load_norm u S A U (((hlaw.2.1 A hμA).1).trans hTS)]
        rw [heq]
        exact hbdd U
    have h_beta_sub : ∀ (v₀ : Fin n → (Fin d → F)) (T S : Finset (Fin n))
        (β : ℝ) (μ : Finset (Fin n) → ℝ),
        T ⊆ S → IsSubspaceBetaBounded v₀ T β μ → IsSubspaceBetaBounded v₀ S β μ := by
      intro v₀ T S β μ hTS ⟨⟨h1, h2, h3⟩, hbdd⟩
      exact ⟨⟨h1, fun A hne => ⟨(h2 A hne).1.trans hTS, (h2 A hne).2⟩, h3⟩, hbdd⟩
    have h_ind : ∀ (m : ℕ) (u : Fin n → (Fin d → F))
        (P : Finset (Fin n) → Finset (Fin n)) (S : Finset (Fin n)),
        (∀ T : Finset (Fin n), P T ⊆ T ∧ LinearIndependent F (fun g : P T => u g.1)) →
        S.card = s + m →
          IsSubspaceBetaBounded u S (loadBeta s S.card) (abhmMuProg s F u P S) ∧
          (0 < m →
            (∀ g ∈ S, ∀ A, 0 ≤ abhmQProg s F u P S g A ∧
              abhmQProg s F u P S g A ≤ abhmMuProg s F u P (S.erase g) A) ∧
            (∀ g ∈ S, ∀ A, abhmQProg s F u P S g A ≠ 0 →
              g ∈ P S ∧ g ∉ A ∧
                LinearIndependent F (fun x : (insert g A : Finset (Fin n)) => u x.1)) ∧
            (∀ g ∈ P S, (∑ A, abhmQProg s F u P S g A) = admitRate s S.card) ∧
            (∀ C, abhmMuProg s F u P S C =
              abhmRowAvg S (fun g => abhmMuProg s F u P (S.erase g)) (abhmQProg s F u P S) C)) := by
      intro m
      induction m with
      | zero =>
        intro u P S _ hScard
        have hScard_s : S.card = s := by omega
        refine ⟨?_, fun hm => absurd hm (lt_irrefl 0)⟩
        rw [h_le_s u P S (by omega), hScard_s]
        have hs_ne : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hbeta0 : loadBeta s s = 0 := by
          unfold loadBeta; rw [div_self hs_ne, sub_self]
        rw [hbeta0]
        exact h_empty_bdd u S
      | succ m₀ ih =>
        intro u P S hP_valid hScard
        let k := s + m₀
        have hk_ge_s : s ≤ k := Nat.le_add_right s m₀
        have hScard_k : S.card = k + 1 := by omega
        have hnle : ¬ (k + 1 ≤ s) := by omega
        let u' := abhmNormVec S u
        let P' := abhmNormProp S P
        let μSub : Fin n → Finset (Fin n) → ℝ :=
          fun g => (abhmProgAux s k u' P' (S.erase g)).1
        have hμSub_eq : ∀ g ∈ S, μSub g = abhmMuProg s F u P (S.erase g) := by
          intro g hgS
          have hcard_er : (S.erase g).card = k := by
            rw [Finset.card_erase_of_mem hgS, hScard_k]; omega
          have hsub_er : S.erase g ⊆ S := Finset.erase_subset g S
          have hloc_er := h_norm_loc k u' u P' P (S.erase g)
            (fun x hx => if_pos (hsub_er hx))
            (fun T hT => if_pos (hT.trans hsub_er))
          dsimp only [μSub, abhmMuProg]
          rw [hcard_er, hloc_er]
        have hμSub_laws : ∀ g ∈ S,
            IsIndepSetLaw u' (S.erase g) (μSub g) ∧
            IsSubspaceBetaBounded u' S (loadBeta s k) (μSub g) := by
          intro g hgS
          have hcard_er : (S.erase g).card = s + m₀ := by
            rw [Finset.card_erase_of_mem hgS, hScard_k]; omega
          have hbdd_u := (ih u P (S.erase g) hP_valid hcard_er).1
          rw [hcard_er] at hbdd_u
          change IsSubspaceBetaBounded u (S.erase g) (loadBeta s k)
            (abhmMuProg s F u P (S.erase g)) at hbdd_u
          rw [← hμSub_eq g hgS] at hbdd_u
          have hbdd_u' := (h_beta_norm u S (S.erase g) (loadBeta s k) (μSub g)
            (Finset.erase_subset g S)).mpr hbdd_u
          exact ⟨hbdd_u'.1, h_beta_sub u' (S.erase g) S (loadBeta s k) (μSub g)
            (Finset.erase_subset g S) hbdd_u'⟩
        have hP'S : P' S = P S := if_pos Finset.Subset.rfl
        have hB_PS : P S ⊆ S ∧ LinearIndependent F (fun g : P S => u' g.1) :=
          ⟨(hP_valid S).1, (h_li_norm u S (P S) (hP_valid S).1).mpr (hP_valid S).2⟩
        have hB_cond : P' S ⊆ S ∧ LinearIndependent F (fun g : P' S => u' g.1) := by
          rw [hP'S]; exact hB_PS
        have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
        have hk_ne : (k : ℝ) ≠ 0 := hk_pos.ne'
        have hk1_ne : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hβ0 : 0 ≤ loadBeta s k := by
          unfold loadBeta; rw [sub_nonneg, div_le_one hk_pos]
          exact_mod_cast hk_ge_s
        have hβ1 : loadBeta s k ≤ 1 := by
          unfold loadBeta
          linarith [div_nonneg (Nat.cast_nonneg s) (le_of_lt hk_pos)]
        have ha_eq : admitRate s S.card = (s : ℝ) / (k : ℝ) := by
          rw [hScard_k]; unfold admitRate; rw [Nat.add_sub_cancel]
        have ha0 : 0 ≤ admitRate s S.card := by rw [ha_eq]; positivity
        have ha_le : admitRate s S.card ≤ 1 - loadBeta s k := by
          rw [ha_eq]; unfold loadBeta; linarith
        have hβ_next : loadBeta s k + admitRate s S.card / (S.card : ℝ) = loadBeta s S.card := by
          rw [ha_eq, hScard_k]; unfold loadBeta; push_cast; field_simp [hk_ne, hk1_ne]; ring
        have hex : ∃ q : Fin n → Finset (Fin n) → ℝ,
            abhmStepSpec s u' S (if P' S ⊆ S ∧ LinearIndependent F (fun g : P' S => u' g.1) then P' S else ∅) μSub q := by
          rw [if_pos hB_cond, hP'S]
          obtain ⟨q, hq1, hq2, hq3, hq4⟩ := h_part2 u' S (P S) (loadBeta s k)
            (admitRate s S.card) μSub (by omega) hB_PS.1 hβ0 hβ1 ha0 ha_le hB_PS.2 hμSub_laws
          rw [hβ_next] at hq4
          exact ⟨q, hq1, hq2, hq3, hq4⟩
        let q_ch := Classical.choose hex
        have hprog_unfold : abhmProgAux s S.card u P S = (abhmRowAvg S μSub q_ch, q_ch) := by
          rw [hScard_k]
          unfold abhmProgAux
          rw [if_neg hnle]
          dsimp only
          rw [dif_pos hex]
        have hμ_eq : abhmMuProg s F u P S = abhmRowAvg S μSub q_ch := by
          unfold abhmMuProg; rw [hprog_unfold]
        have hq_eq : abhmQProg s F u P S = q_ch := by
          unfold abhmQProg; rw [hprog_unfold]
        have hspec : abhmStepSpec s u' S
            (if P' S ⊆ S ∧ LinearIndependent F (fun g : P' S => u' g.1) then P' S else ∅) μSub q_ch :=
          Classical.choose_spec hex
        rw [if_pos hB_cond, hP'S] at hspec
        obtain ⟨hsp1, hsp2, hsp3, hsp4⟩ := hspec
        have hbdd_final : IsSubspaceBetaBounded u S (loadBeta s S.card) (abhmMuProg s F u P S) := by
          rw [hμ_eq]
          exact (h_beta_norm u S S (loadBeta s S.card) _ Finset.Subset.rfl).mp hsp4
        refine ⟨hbdd_final, fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
        · intro g hgS A
          rw [hq_eq, ← hμSub_eq g hgS]
          exact hsp1 g hgS A
        · intro g hgS A hq_ne
          rw [hq_eq] at hq_ne
          obtain ⟨hgPS, hgA, hli_u'⟩ := hsp2 g hgS A hq_ne
          have hμ_ne : μSub g A ≠ 0 := by
            intro h0
            obtain ⟨hq0, hqle⟩ := hsp1 g hgS A
            exact hq_ne (le_antisymm (hqle.trans h0.le) hq0)
          have hAS : A ⊆ S := (((hμSub_laws g hgS).1.2.1 A hμ_ne).1).trans (Finset.erase_subset g S)
          have hinsS : insert g A ⊆ S := Finset.insert_subset hgS hAS
          exact ⟨hgPS, hgA, (h_li_norm u S (insert g A) hinsS).mp hli_u'⟩
        · intro g hgPS
          rw [hq_eq]
          exact hsp3 g hgPS
        · intro C
          rw [hμ_eq, hq_eq]
          dsimp only [abhmRowAvg]
          congr 1
          refine Finset.sum_congr rfl fun g hgS => ?_
          rw [hμSub_eq g hgS]
    refine ⟨h_le_s, ?_, ?_, ?_⟩
    · intro u u' P P' S hu hP
      have h := h_norm_loc S.card u u' P P' S hu hP
      exact ⟨congr_arg Prod.fst h, congr_arg Prod.snd h⟩
    · intro u P hP S hS
      exact (h_ind (S.card - s) u P S hP (by omega)).1
    · intro u P hP S hS
      exact (h_ind (S.card - s) u P S hP (by omega)).2 (by omega)
  have h_part3 : ∀ (n d s : ℕ) (F : Type) [Field F] [Fintype F] [DecidableEq F],
      1 ≤ s → s ≤ n →
        ∃ μ_prog :
            (Fin n → (Fin d → F)) → (Finset (Fin n) → Finset (Fin n)) →
            Finset (Fin n) → Finset (Fin n) → ℝ,
          (∀ (u : Fin n → (Fin d → F)) (P : Finset (Fin n) → Finset (Fin n)),
            (∀ T : Finset (Fin n), P T ⊆ T ∧ LinearIndependent F (fun g : P T => u g.1)) →
            ∀ S : Finset (Fin n), s ≤ S.card →
              IsSubspaceBetaBounded u S (loadBeta s S.card) (μ_prog u P S)) ∧
          (∀ (u u' : Fin n → (Fin d → F)) (P P' : Finset (Fin n) → Finset (Fin n))
              (S : Finset (Fin n)),
            (∀ g ∈ S, u g = u' g) → (∀ T ⊆ S, P T = P' T) →
              μ_prog u P S = μ_prog u' P' S) := by
    intro n d s F _ _ _ hs1 _
    obtain ⟨_, hloc, hfeas, _⟩ := h_prog_full n d s F hs1
    exact ⟨abhmMuProg s F, hfeas, fun u u' P P' S hu hP => (hloc u u' P P' S hu hP).1⟩
  have lem_coord : ∀ {n : ℕ} (g : Fin n) (p : ℝ) (E : Set (Fin n → ℝ)),
      0 ≤ p → p ≤ 1 → MeasurableSet E →
      (∀ ω ω' : Fin n → ℝ, (∀ y : Fin n, y ≠ g → ω y = ω' y) → (ω ∈ E ↔ ω' ∈ E)) →
      (abhmSeedSpaceMeasure n).real (E ∩ {ω | 0 ≤ ω g ∧ ω g < p}) =
        p * (abhmSeedSpaceMeasure n).real E ∧
      (abhmSeedSpaceMeasure n).real (E ∩ {ω | ¬ (0 ≤ ω g ∧ ω g < p)}) =
        (1 - p) * (abhmSeedSpaceMeasure n).real E := by
    intro n g p E hp0 hp1 hE_meas hE_indep
    haveI : IsProbabilityMeasure abhmUnitIntervalMeasure :=
      ⟨by rw [abhmUnitIntervalMeasure, Measure.restrict_apply_univ, Real.volume_Icc]; norm_num⟩
    haveI : IsProbabilityMeasure (abhmSeedSpaceMeasure n) := by
      unfold abhmSeedSpaceMeasure; infer_instance
    let μ0 : Fin n → Measure ℝ := fun _ => abhmUnitIntervalMeasure
    let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (· = g)
    let μL : Measure ({y : Fin n // y = g} → ℝ) := Measure.pi (fun _ => abhmUnitIntervalMeasure)
    let μR : Measure ({y : Fin n // y ≠ g} → ℝ) := Measure.pi (fun _ => abhmUnitIntervalMeasure)
    have hmp : MeasurePreserving e (abhmSeedSpaceMeasure n) (μL.prod μR) := by
      dsimp only [abhmSeedSpaceMeasure, e, μL, μR, μ0]
      convert MeasureTheory.measurePreserving_piEquivPiSubtypeProd μ0 (· = g)
    let AL : Set ({y : Fin n // y = g} → ℝ) := Set.univ.pi (fun _ => Set.Ico 0 p)
    have hAL_meas : MeasurableSet AL := MeasurableSet.univ_pi (fun _ => measurableSet_Ico)
    have hμL_AL : μL AL = ENNReal.ofReal p := by
      dsimp only [μL, AL]
      rw [Measure.pi_pi]
      have huniv_sub : (Finset.univ : Finset {y : Fin n // y = g}) = {⟨g, rfl⟩} := by
        ext a
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        exact Subtype.ext a.2
      rw [huniv_sub, Finset.prod_singleton, abhmUnitIntervalMeasure,
        Measure.restrict_apply measurableSet_Ico]
      have hinter : Set.Ico (0 : ℝ) p ∩ Set.Icc (0 : ℝ) 1 = Set.Ico (0 : ℝ) p := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_Icc]
        exact ⟨fun h => h.1,
          fun ⟨ht0, htp⟩ => ⟨⟨ht0, htp⟩, ⟨ht0, le_of_lt (lt_of_lt_of_le htp hp1)⟩⟩⟩
      rw [hinter, Real.volume_Ico, sub_zero]
    let emb : ({y : Fin n // y ≠ g} → ℝ) → (Fin n → ℝ) := fun r => e.symm (0, r)
    have hemb_meas : Measurable emb :=
      e.symm.measurable.comp (Measurable.prodMk measurable_const measurable_id)
    let ER : Set ({y : Fin n // y ≠ g} → ℝ) := emb ⁻¹' E
    have hER_meas : MeasurableSet ER := hemb_meas hE_meas
    have hER_iff : ∀ ω : Fin n → ℝ, (e ω).2 ∈ ER ↔ ω ∈ E := by
      intro ω
      change e.symm (0, (e ω).2) ∈ E ↔ ω ∈ E
      apply hE_indep
      intro y hy
      have happ := e.apply_symm_apply (0, (e ω).2)
      have h2 := congrArg Prod.snd happ
      exact congrFun h2 ⟨y, hy⟩
    have hAL_iff : ∀ ω : Fin n → ℝ, (e ω).1 ∈ AL ↔ (0 ≤ ω g ∧ ω g < p) := by
      intro ω
      simp only [AL, Set.mem_univ_pi, Set.mem_Ico]
      exact ⟨fun h => h ⟨g, rfl⟩, fun h ⟨_, rfl⟩ => h⟩
    let Acc : Set (Fin n → ℝ) := {ω | 0 ≤ ω g ∧ ω g < p}
    have hAcc_meas : MeasurableSet Acc := (measurable_pi_apply g) measurableSet_Ico
    have hpre_acc : e ⁻¹' (AL ×ˢ ER) = E ∩ Acc := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff, hAL_iff, hER_iff, Acc,
        Set.mem_setOf_eq, and_comm]
    have hpre_E : e ⁻¹' (Set.univ ×ˢ ER) = E := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and, hER_iff]
    have hm_acc : abhmSeedSpaceMeasure n (E ∩ Acc) = ENNReal.ofReal p * μR ER := by
      rw [← hpre_acc, hmp.measure_preimage (hAL_meas.prod hER_meas).nullMeasurableSet,
        Measure.prod_prod, hμL_AL]
    have hm_E : abhmSeedSpaceMeasure n E = μR ER := by
      rw [← hpre_E, hmp.measure_preimage (MeasurableSet.univ.prod hER_meas).nullMeasurableSet,
        Measure.prod_prod, measure_univ, one_mul]
    have hreal_acc : (abhmSeedSpaceMeasure n).real (E ∩ Acc) =
        p * (abhmSeedSpaceMeasure n).real E := by
      rw [measureReal_def, measureReal_def, hm_acc, hm_E, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hp0]
    have hunion : (E ∩ Acc) ∪ (E ∩ Accᶜ) = E := Set.inter_union_compl E Acc
    have hdisj : Disjoint (E ∩ Acc) (E ∩ Accᶜ) :=
      Disjoint.mono inf_le_right inf_le_right disjoint_compl_right
    have hsum_real : (abhmSeedSpaceMeasure n).real E =
        (abhmSeedSpaceMeasure n).real (E ∩ Acc) + (abhmSeedSpaceMeasure n).real (E ∩ Accᶜ) := by
      conv_lhs => rw [← hunion]
      exact measureReal_union hdisj (hE_meas.inter hAcc_meas.compl)
    refine ⟨hreal_acc, ?_⟩
    change (abhmSeedSpaceMeasure n).real (E ∩ Accᶜ) = (1 - p) * (abhmSeedSpaceMeasure n).real E
    linarith
  have h_pref_zero : ∀ {n : ℕ} (π : Equiv.Perm (Fin n)), arrivalPrefixSet π 0 = ∅ := by
    intro n π; ext x; simp [arrivalPrefixSet]
  have h_pref_succ : ∀ {n : ℕ} (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k + 1 ≤ n),
      arrivalPrefixSet π (k + 1) = insert (π ⟨k, hk⟩) (arrivalPrefixSet π k) ∧
      π ⟨k, hk⟩ ∉ arrivalPrefixSet π k := by
    intro n π k hk
    constructor
    · have hfilt : (Finset.univ.filter (fun idx : Fin n => idx.1 < k + 1)) =
          insert ⟨k, hk⟩ (Finset.univ.filter (fun idx : Fin n => idx.1 < k)) := by
        ext idx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      dsimp only [arrivalPrefixSet]
      rw [hfilt, Finset.image_insert]
    · simp only [arrivalPrefixSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      rintro ⟨idx, hidx, heq⟩
      have hval : idx.1 = k := congrArg Fin.val (π.injective heq)
      omega
  have h_pref_card : ∀ {n : ℕ} (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
      (arrivalPrefixSet π k).card = k := by
    intro n π k
    induction k with
    | zero => intro _; simp [h_pref_zero]
    | succ k ih =>
      intro hk
      obtain ⟨hins, hnot⟩ := h_pref_succ π k hk
      rw [hins, Finset.card_insert_of_notMem hnot, ih (Nat.le_of_succ_le hk)]
  have h_st_fst : ∀ {n d : ℕ} {F : Type} (dm : DetRepresentedAdmissionModule n F d)
      (P : Finset (Fin n) → Finset (Fin n)) (u : Fin n → (Fin d → F))
      (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
      (runDetRepAdmissionSteps dm P u π k hk).1.toFinset = arrivalPrefixSet π k := by
    intro n d F dm P u π k
    induction k with
    | zero => intro _; simp [runDetRepAdmissionSteps, h_pref_zero]
    | succ k ih =>
      intro hk
      obtain ⟨hins, _⟩ := h_pref_succ π k hk
      have hprev := ih (Nat.le_of_succ_le hk)
      have hstep : (runDetRepAdmissionSteps dm P u π (k + 1) hk).1 =
          (runDetRepAdmissionSteps dm P u π k (Nat.le_of_succ_le hk)).1 ++ [π ⟨k, hk⟩] := rfl
      rw [hstep, hins, ← hprev]
      ext y; simp [Finset.mem_insert]
  have h_part4 : ∀ (n d s : ℕ) (F : Type) [Field F] [Fintype F] [DecidableEq F],
      2 ≤ n → 1 ≤ s → s < n →
        ∃ mod : RepresentedAdmissionModule n F d,
          ∀ (M : Matroid (Fin n)) (u : Fin n → (Fin d → F))
            (P : Finset (Fin n) → Finset (Fin n)),
            IsLinearMatroidRep F M u →
            (∀ T : Finset (Fin n), P T ⊆ T ∧ M.Indep (P T : Set (Fin n))) →
              (∀ (ω : mod.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k + 1 ≤ n),
                let st := runDetRepAdmissionSteps (mod.det ω) P u π k (Nat.le_of_succ_le hk)
                let x := π ⟨k, hk⟩
                (k < s ∨ x ∉ P (insert x st.1.toFinset)) →
                  (mod.det ω).step st.1 x st.2 (fun ⟨T, _⟩ => P T) (fun ⟨g, _⟩ => u g) = false) ∧
              (∀ (ω : mod.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
                let st := runDetRepAdmissionSteps (mod.det ω) P u π k hk
                st.2 ⊆ st.1.toFinset ∧ M.Indep (st.2 : Set (Fin n))) ∧
              (∀ (k : ℕ) (hk : k + 1 ≤ n), s ≤ k →
                ∀ (S : Finset (Fin n)) (g : Fin n),
                  S.card = k + 1 → g ∈ P S →
                    let ev := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
                      (fun π => arrivalPrefixSet π (k + 1) = S ∧ π ⟨k, hk⟩ = g)
                    ∑ π ∈ ev, mod.seedMeasure.real
                      {ω | g ∈ (runDetRepAdmissionSteps (mod.det ω) P u π (k + 1) hk).2} =
                      admitRate s (k + 1) * (ev.card : ℝ)) := by
    intro n d s F _ _ _ hn2 hs1 hsn
    haveI hUnitProb : IsProbabilityMeasure abhmUnitIntervalMeasure :=
      ⟨by rw [abhmUnitIntervalMeasure, Measure.restrict_apply_univ, Real.volume_Icc]; norm_num⟩
    haveI hSeedProb : IsProbabilityMeasure (abhmSeedSpaceMeasure n) := by
      unfold abhmSeedSpaceMeasure; infer_instance
    let mod : RepresentedAdmissionModule n F d :=
      { Seed := Fin n → ℝ
        measSeed := inferInstance
        seedMeasure := abhmSeedSpaceMeasure n
        isProb := hSeedProb
        det := abhmDetMod F s
        meas_step := by
          intro prev x accepted propOracle vecOracle b
          let S := insert x prev.toFinset
          let uLoc := abhmLiftVecOracle S vecOracle
          let PLoc := abhmLiftPropOracle S propOracle
          let denom := abhmMuProg s F uLoc PLoc (S.erase x) accepted
          let num := abhmQProg s F uLoc PLoc S x accepted
          change MeasurableSet {ω : Fin n → ℝ |
            (if S.card ≤ s ∨ x ∉ propOracle ⟨S, Finset.Subset.refl S⟩ then false
             else if denom ≤ 0 then false
             else decide (0 ≤ ω x ∧ ω x < num / denom)) = b}
          by_cases hc1 : S.card ≤ s ∨ x ∉ propOracle ⟨S, Finset.Subset.refl S⟩
          · simp only [if_pos hc1]
            cases b
            · have heq : {ω : Fin n → ℝ | false = false} = Set.univ := by ext; simp
              rw [heq]; exact MeasurableSet.univ
            · have heq : {ω : Fin n → ℝ | false = true} = ∅ := by ext; simp
              rw [heq]; exact MeasurableSet.empty
          · simp only [if_neg hc1]
            by_cases hc2 : denom ≤ 0
            · simp only [if_pos hc2]
              cases b
              · have heq : {ω : Fin n → ℝ | false = false} = Set.univ := by ext; simp
                rw [heq]; exact MeasurableSet.univ
              · have heq : {ω : Fin n → ℝ | false = true} = ∅ := by ext; simp
                rw [heq]; exact MeasurableSet.empty
            · simp only [if_neg hc2]
              have hIco : MeasurableSet ((fun ω : Fin n → ℝ => ω x) ⁻¹' Set.Ico 0 (num / denom)) :=
                (measurable_pi_apply x) measurableSet_Ico
              cases b
              · have heq : {ω : Fin n → ℝ | decide (0 ≤ ω x ∧ ω x < num / denom) = false} =
                    ((fun ω : Fin n → ℝ => ω x) ⁻¹' Set.Ico 0 (num / denom))ᶜ := by
                  ext ω; simp [Set.mem_Ico]
                rw [heq]; exact hIco.compl
              · have heq : {ω : Fin n → ℝ | decide (0 ≤ ω x ∧ ω x < num / denom) = true} =
                    (fun ω : Fin n → ℝ => ω x) ⁻¹' Set.Ico 0 (num / denom) := by
                  ext ω; simp [Set.mem_Ico]
                rw [heq]; exact hIco }
    refine ⟨mod, ?_⟩
    intro M u P h_rep hP_M
    obtain ⟨h_le_s, h_loc, _, h_trans⟩ := h_prog_full n d s F hs1
    have hP_li : ∀ T : Finset (Fin n), P T ⊆ T ∧ LinearIndependent F (fun g : P T => u g.1) :=
      fun T => ⟨(hP_M T).1, (h_rep (P T)).mp (hP_M T).2⟩
    have h_oracle_eq : ∀ (S : Finset (Fin n)) (x : Fin n),
        abhmMuProg s F (abhmLiftVecOracle S (fun ⟨g, _⟩ => u g))
          (abhmLiftPropOracle S (fun ⟨T, _⟩ => P T)) (S.erase x) =
          abhmMuProg s F u P (S.erase x) ∧
        abhmQProg s F (abhmLiftVecOracle S (fun ⟨g, _⟩ => u g))
          (abhmLiftPropOracle S (fun ⟨T, _⟩ => P T)) S =
          abhmQProg s F u P S := by
      intro S x
      have hsub : S.erase x ⊆ S := Finset.erase_subset x S
      let uL := abhmLiftVecOracle S (fun ⟨g, _⟩ => u g)
      let PL := abhmLiftPropOracle S (fun ⟨T, _⟩ => P T)
      have huL : ∀ g ∈ S, uL g = u g := fun g hg => dif_pos hg
      have hPL : ∀ T ⊆ S, PL T = P T := fun T hT => dif_pos hT
      exact ⟨(h_loc uL u PL P (S.erase x)
          (fun g hg => huL g (hsub hg))
          (fun T hT => hPL T (hT.trans hsub))).1,
        (h_loc uL u PL P S huL hPL).2⟩
    have h_rej : ∀ (ω : mod.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k + 1 ≤ n),
        let st := runDetRepAdmissionSteps (mod.det ω) P u π k (Nat.le_of_succ_le hk)
        let x := π ⟨k, hk⟩
        (k < s ∨ x ∉ P (insert x st.1.toFinset)) →
          (mod.det ω).step st.1 x st.2 (fun ⟨T, _⟩ => P T) (fun ⟨g, _⟩ => u g) = false := by
      intro ω π k hk st x hcond
      have hS_eq : insert x st.1.toFinset = arrivalPrefixSet π (k + 1) := by
        rw [h_st_fst (mod.det ω) P u π k (Nat.le_of_succ_le hk), ← (h_pref_succ π k hk).1]
      have hScard : (insert x st.1.toFinset).card = k + 1 := by
        rw [hS_eq, h_pref_card π (k + 1) hk]
      have hc1 : (insert x st.1.toFinset).card ≤ s ∨ x ∉ P (insert x st.1.toFinset) := by
        rcases hcond with hks | hxP
        · exact Or.inl (by omega)
        · exact Or.inr hxP
      change (if (insert x st.1.toFinset).card ≤ s ∨ x ∉ P (insert x st.1.toFinset) then false
        else _) = false
      exact if_pos hc1
    have h_pathwise : ∀ (ω : mod.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
        let st := runDetRepAdmissionSteps (mod.det ω) P u π k hk
        st.2 ⊆ st.1.toFinset ∧ M.Indep (st.2 : Set (Fin n)) := by
      intro ω π k
      induction k with
      | zero =>
        intro _
        dsimp only [runDetRepAdmissionSteps]
        rw [Finset.coe_empty]
        exact ⟨Finset.empty_subset _, M.empty_indep⟩
      | succ k ih =>
        intro hk
        have hk0 : k ≤ n := Nat.le_of_succ_le hk
        obtain ⟨hsub_k, hind_k⟩ := ih hk0
        let st := runDetRepAdmissionSteps (mod.det ω) P u π k hk0
        let x := π ⟨k, hk⟩
        let S := insert x st.1.toFinset
        let dec := (mod.det ω).step st.1 x st.2 (fun ⟨T, _⟩ => P T) (fun ⟨g, _⟩ => u g)
        have hlist : (st.1 ++ [x]).toFinset = S := by
          dsimp only [S]; ext y; simp [Finset.mem_insert]
        change (if dec then insert x st.2 else st.2) ⊆ (st.1 ++ [x]).toFinset ∧
          M.Indep ((if dec then insert x st.2 else st.2 : Finset (Fin n)) : Set (Fin n))
        rw [hlist]
        cases hdec : dec
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨hsub_k.trans (Finset.subset_insert x _), hind_k⟩
        · simp only [↓reduceIte]
          refine ⟨Finset.insert_subset_insert x hsub_k, ?_⟩
          obtain ⟨hμ_loc, hq_loc⟩ := h_oracle_eq S x
          change (if S.card ≤ s ∨ x ∉ P S then false
            else if abhmMuProg s F (abhmLiftVecOracle S (fun ⟨g, _⟩ => u g))
                (abhmLiftPropOracle S (fun ⟨T, _⟩ => P T)) (S.erase x) st.2 ≤ 0 then false
            else decide (0 ≤ ω x ∧ ω x <
              abhmQProg s F (abhmLiftVecOracle S (fun ⟨g, _⟩ => u g))
                (abhmLiftPropOracle S (fun ⟨T, _⟩ => P T)) S x st.2 /
              abhmMuProg s F (abhmLiftVecOracle S (fun ⟨g, _⟩ => u g))
                (abhmLiftPropOracle S (fun ⟨T, _⟩ => P T)) (S.erase x) st.2)) = true at hdec
          rw [hμ_loc, hq_loc] at hdec
          by_cases hc1 : S.card ≤ s ∨ x ∉ P S
          · rw [if_pos hc1] at hdec; cases hdec
          · rw [if_neg hc1] at hdec
            have hs_lt : s < S.card := by push_neg at hc1; exact hc1.1
            by_cases hc2 : abhmMuProg s F u P (S.erase x) st.2 ≤ 0
            · rw [if_pos hc2] at hdec; cases hdec
            · rw [if_neg hc2] at hdec
              have hacc : 0 ≤ ω x ∧ ω x <
                  abhmQProg s F u P S x st.2 / abhmMuProg s F u P (S.erase x) st.2 :=
                of_decide_eq_true hdec
              have hpos : 0 < abhmQProg s F u P S x st.2 / abhmMuProg s F u P (S.erase x) st.2 :=
                lt_of_le_of_lt hacc.1 hacc.2
              have hq_ne : abhmQProg s F u P S x st.2 ≠ 0 := by
                intro h0; rw [h0, zero_div] at hpos; exact lt_irrefl 0 hpos
              have hxS : x ∈ S := Finset.mem_insert_self x _
              have hli := ((h_trans u P hP_li S hs_lt).2.1 x hxS st.2 hq_ne).2.2
              exact (h_rep (insert x st.2)).mpr hli
    let traj : Equiv.Perm (Fin n) → (Fin n → ℝ) → ℕ → Finset (Fin n) :=
      fun π ω k => if hk : k ≤ n then (runDetRepAdmissionSteps (mod.det ω) P u π k hk).2 else ∅
    let p_fn : Finset (Fin n) → Fin n → Finset (Fin n) → ℝ :=
      fun S x A =>
        if x ∈ P S ∧ 0 < abhmMuProg s F u P (S.erase x) A then
          abhmQProg s F u P S x A / abhmMuProg s F u P (S.erase x) A
        else 0
    have h_p_bounds : ∀ (S : Finset (Fin n)), s < S.card →
        ∀ g ∈ S, ∀ A : Finset (Fin n),
          0 ≤ p_fn S g A ∧ p_fn S g A ≤ 1 ∧
          p_fn S g A * abhmMuProg s F u P (S.erase g) A = abhmQProg s F u P S g A := by
      intro S hs_lt g hgS A
      obtain ⟨hq_bds, hq_supp, _, _⟩ := h_trans u P hP_li S hs_lt
      obtain ⟨hq0, hq_le⟩ := hq_bds g hgS A
      dsimp only [p_fn]
      by_cases hc : g ∈ P S ∧ 0 < abhmMuProg s F u P (S.erase g) A
      · rw [if_pos hc]
        exact ⟨div_nonneg hq0 (le_of_lt hc.2),
          (div_le_one hc.2).mpr hq_le,
          div_mul_cancel₀ _ hc.2.ne'⟩
      · rw [if_neg hc]
        refine ⟨le_rfl, zero_le_one, ?_⟩
        rw [zero_mul]
        by_cases hgPS : g ∈ P S
        · have hμ_le : abhmMuProg s F u P (S.erase g) A ≤ 0 :=
            le_of_not_gt fun hpos => hc ⟨hgPS, hpos⟩
          exact (le_antisymm (hq_le.trans hμ_le) hq0).symm
        · by_contra hq_ne
          exact hgPS (hq_supp g hgS A (Ne.symm hq_ne)).1
    have h_traj_zero : ∀ π ω, traj π ω 0 = ∅ := by
      intro π ω; simp [traj, runDetRepAdmissionSteps]
    have h_traj_gt : ∀ π ω k, ¬ k ≤ n → traj π ω k = ∅ := by
      intro π ω k hk; simp [traj, hk]
    have h_traj_lt_s : ∀ π ω k (hk : k + 1 ≤ n), k < s → traj π ω (k + 1) = traj π ω k := by
      intro π ω k hk hks
      have hk0 : k ≤ n := Nat.le_of_succ_le hk
      have hr := h_rej ω π k hk (Or.inl hks)
      dsimp only [traj]
      rw [dif_pos hk, dif_pos hk0]
      change (if (mod.det ω).step
          (runDetRepAdmissionSteps (mod.det ω) P u π k hk0).1 (π ⟨k, hk⟩)
          (runDetRepAdmissionSteps (mod.det ω) P u π k hk0).2
          (fun ⟨T, _⟩ => P T) (fun ⟨g, _⟩ => u g)
        then _ else _) = _
      rw [hr]
      rfl
    have h_traj_ge_s : ∀ π ω k (hk : k + 1 ≤ n), s ≤ k →
        let x := π ⟨k, hk⟩
        let S := arrivalPrefixSet π (k + 1)
        traj π ω (k + 1) =
          if (0 ≤ ω x ∧ ω x < p_fn S x (traj π ω k)) then
            insert x (traj π ω k)
          else
            traj π ω k := by
      intro π ω k hk hsk x S
      have hk0 : k ≤ n := Nat.le_of_succ_le hk
      let st := runDetRepAdmissionSteps (mod.det ω) P u π k hk0
      have hS_eq : insert x st.1.toFinset = S := by
        dsimp only [S, x, st]
        rw [h_st_fst (mod.det ω) P u π k hk0, ← (h_pref_succ π k hk).1]
      have hScard : S.card = k + 1 := h_pref_card π (k + 1) hk
      have hnle : ¬ S.card ≤ s := by omega
      obtain ⟨hμ_loc, hq_loc⟩ := h_oracle_eq (insert x st.1.toFinset) x
      dsimp only [traj]
      rw [dif_pos hk, dif_pos hk0]
      change (if (if (insert x st.1.toFinset).card ≤ s ∨ x ∉ P (insert x st.1.toFinset) then false
        else if abhmMuProg s F (abhmLiftVecOracle (insert x st.1.toFinset) (fun ⟨g, _⟩ => u g))
            (abhmLiftPropOracle (insert x st.1.toFinset) (fun ⟨T, _⟩ => P T))
            ((insert x st.1.toFinset).erase x) st.2 ≤ 0 then false
        else decide (0 ≤ ω x ∧ ω x <
          abhmQProg s F (abhmLiftVecOracle (insert x st.1.toFinset) (fun ⟨g, _⟩ => u g))
            (abhmLiftPropOracle (insert x st.1.toFinset) (fun ⟨T, _⟩ => P T))
            (insert x st.1.toFinset) x st.2 /
          abhmMuProg s F (abhmLiftVecOracle (insert x st.1.toFinset) (fun ⟨g, _⟩ => u g))
            (abhmLiftPropOracle (insert x st.1.toFinset) (fun ⟨T, _⟩ => P T))
            ((insert x st.1.toFinset).erase x) st.2)) = true
        then insert x st.2 else st.2) =
        if 0 ≤ ω x ∧ ω x < p_fn S x st.2 then insert x st.2 else st.2
      rw [hμ_loc, hq_loc, hS_eq]
      by_cases hxP : x ∈ P S
      · have hc1 : ¬ (S.card ≤ s ∨ x ∉ P S) := by push_neg; exact ⟨Nat.lt_of_not_ge hnle, hxP⟩
        rw [if_neg hc1]
        by_cases hc2 : abhmMuProg s F u P (S.erase x) st.2 ≤ 0
        · rw [if_pos hc2]
          have hp0 : p_fn S x st.2 = 0 := by
            dsimp only [p_fn]
            exact if_neg fun h => not_lt_of_ge hc2 h.2
          rw [hp0]
          have hnacc : ¬ (0 ≤ ω x ∧ ω x < 0) := fun h => lt_irrefl 0 (lt_of_le_of_lt h.1 h.2)
          simp [hnacc]
        · rw [if_neg hc2]
          have hpos : 0 < abhmMuProg s F u P (S.erase x) st.2 := lt_of_not_ge hc2
          have hp_eq : p_fn S x st.2 =
              abhmQProg s F u P S x st.2 / abhmMuProg s F u P (S.erase x) st.2 :=
            if_pos ⟨hxP, hpos⟩
          rw [hp_eq]
          by_cases hacc : 0 ≤ ω x ∧
              ω x < abhmQProg s F u P S x st.2 / abhmMuProg s F u P (S.erase x) st.2 <;>
            simp [hacc]
      · rw [if_pos (Or.inr hxP)]
        have hp0 : p_fn S x st.2 = 0 := if_neg fun h => hxP h.1
        rw [hp0]
        have hnacc : ¬ (0 ≤ ω x ∧ ω x < 0) := fun h => lt_irrefl 0 (lt_of_le_of_lt h.1 h.2)
        simp [hnacc]
    have h_meas_traj : ∀ π k X, MeasurableSet {ω : Fin n → ℝ | traj π ω k = X} := by
      intro π k
      induction k with
      | zero =>
        intro X
        by_cases hX : (∅ : Finset (Fin n)) = X
        · have heq : {ω : Fin n → ℝ | traj π ω 0 = X} = Set.univ := by ext ω; simp [h_traj_zero, hX]
          rw [heq]; exact MeasurableSet.univ
        · have heq : {ω : Fin n → ℝ | traj π ω 0 = X} = ∅ := by ext ω; simp [h_traj_zero, hX]
          rw [heq]; exact MeasurableSet.empty
      | succ k ih =>
        intro X
        by_cases hk : k + 1 ≤ n
        · by_cases hks : k < s
          · have heq : {ω : Fin n → ℝ | traj π ω (k + 1) = X} = {ω : Fin n → ℝ | traj π ω k = X} := by
              ext ω; simp only [Set.mem_setOf_eq, h_traj_lt_s π ω k hk hks]
            rw [heq]; exact ih X
          · have hsk : s ≤ k := Nat.le_of_not_lt hks
            let x := π ⟨k, hk⟩
            let S := arrivalPrefixSet π (k + 1)
            have hunion : {ω : Fin n → ℝ | traj π ω (k + 1) = X} =
                ⋃ A : Finset (Fin n),
                  ((if insert x A = X then
                      {ω : Fin n → ℝ | traj π ω k = A} ∩
                        {ω : Fin n → ℝ | 0 ≤ ω x ∧ ω x < p_fn S x A}
                    else ∅) ∪
                   (if A = X then
                      {ω : Fin n → ℝ | traj π ω k = A} ∩
                        {ω : Fin n → ℝ | ¬ (0 ≤ ω x ∧ ω x < p_fn S x A)}
                    else ∅)) := by
              ext ω
              simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_union,
                h_traj_ge_s π ω k hk hsk]
              constructor
              · intro hX
                refine ⟨traj π ω k, ?_⟩
                by_cases hacc : 0 ≤ ω x ∧ ω x < p_fn S x (traj π ω k)
                · rw [if_pos hacc] at hX
                  exact Or.inl (by rw [if_pos hX]; exact ⟨rfl, hacc⟩)
                · rw [if_neg hacc] at hX
                  exact Or.inr (by rw [if_pos hX]; exact ⟨rfl, hacc⟩)
              · rintro ⟨A, hL | hR⟩
                · by_cases hm : insert x A = X
                  · rw [if_pos hm] at hL
                    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hL
                    rcases hL with ⟨rfl, hacc⟩
                    change (if 0 ≤ ω x ∧ ω x < p_fn S x (traj π ω k) then insert x (traj π ω k)
                      else traj π ω k) = X
                    rw [if_pos hacc]; exact hm
                  · rw [if_neg hm] at hL; exact False.elim hL
                · by_cases hm : A = X
                  · rw [if_pos hm] at hR
                    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hR
                    rcases hR with ⟨rfl, hnacc⟩
                    change (if 0 ≤ ω x ∧ ω x < p_fn S x (traj π ω k) then insert x (traj π ω k)
                      else traj π ω k) = X
                    rw [if_neg hnacc]; exact hm
                  · rw [if_neg hm] at hR; exact False.elim hR
            rw [hunion]
            refine MeasurableSet.iUnion fun A => ?_
            have hIco : MeasurableSet {ω : Fin n → ℝ | 0 ≤ ω x ∧ ω x < p_fn S x A} :=
              (measurable_pi_apply x) measurableSet_Ico
            refine MeasurableSet.union ?_ ?_
            · split_ifs
              · exact (ih A).inter hIco
              · exact MeasurableSet.empty
            · split_ifs
              · exact (ih A).inter hIco.compl
              · exact MeasurableSet.empty
        · by_cases hX : (∅ : Finset (Fin n)) = X
          · have heq : {ω : Fin n → ℝ | traj π ω (k + 1) = X} = Set.univ := by
              ext ω; simp [h_traj_gt _ _ _ hk, hX]
            rw [heq]; exact MeasurableSet.univ
          · have heq : {ω : Fin n → ℝ | traj π ω (k + 1) = X} = ∅ := by
              ext ω; simp [h_traj_gt _ _ _ hk, hX]
            rw [heq]; exact MeasurableSet.empty
    have h_coord_loc : ∀ (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n) (ω ω' : Fin n → ℝ),
        (∀ y ∈ arrivalPrefixSet π k, ω y = ω' y) → traj π ω k = traj π ω' k := by
      intro π k
      induction k with
      | zero => intro _ _ _ _; rw [h_traj_zero, h_traj_zero]
      | succ k ih =>
        intro hk ω ω' h_agree
        have hk0 : k ≤ n := Nat.le_of_succ_le hk
        obtain ⟨hins, _⟩ := h_pref_succ π k hk
        have hA_eq : traj π ω k = traj π ω' k :=
          ih hk0 ω ω' (fun y hy => h_agree y (hins ▸ Finset.mem_insert_of_mem hy))
        by_cases hks : k < s
        · rw [h_traj_lt_s π ω k hk hks, h_traj_lt_s π ω' k hk hks, hA_eq]
        · have hsk : s ≤ k := Nat.le_of_not_lt hks
          have hx_eq : ω (π ⟨k, hk⟩) = ω' (π ⟨k, hk⟩) :=
            h_agree (π ⟨k, hk⟩) (hins ▸ Finset.mem_insert_self _ _)
          rw [h_traj_ge_s π ω k hk hsk, h_traj_ge_s π ω' k hk hsk, hA_eq, hx_eq]
    have h_perm_loc : ∀ (k : ℕ) (hk : k ≤ n) (π₁ π₂ : Equiv.Perm (Fin n)) (ω : Fin n → ℝ),
        (∀ (r : ℕ) (hr : r < k), π₁ ⟨r, lt_of_lt_of_le hr hk⟩ = π₂ ⟨r, lt_of_lt_of_le hr hk⟩) →
        traj π₁ ω k = traj π₂ ω k := by
      intro k
      induction k with
      | zero => intro _ _ _ _ _; rw [h_traj_zero, h_traj_zero]
      | succ k ih =>
        intro hk π₁ π₂ ω h_eq
        have hk0 : k ≤ n := Nat.le_of_succ_le hk
        have hA_eq : traj π₁ ω k = traj π₂ ω k :=
          ih hk0 π₁ π₂ ω (fun r hr => h_eq r (Nat.lt_succ_of_lt hr))
        by_cases hks : k < s
        · rw [h_traj_lt_s π₁ ω k hk hks, h_traj_lt_s π₂ ω k hk hks, hA_eq]
        · have hsk : s ≤ k := Nat.le_of_not_lt hks
          have hx_eq : π₁ ⟨k, hk⟩ = π₂ ⟨k, hk⟩ := h_eq k (Nat.lt_succ_self k)
          have hpref_eq : arrivalPrefixSet π₁ (k + 1) = arrivalPrefixSet π₂ (k + 1) := by
            dsimp only [arrivalPrefixSet]
            ext y
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨fun ⟨idx, hidx, hy⟩ => ⟨idx, hidx, (h_eq idx.1 hidx).symm.trans hy⟩,
              fun ⟨idx, hidx, hy⟩ => ⟨idx, hidx, (h_eq idx.1 hidx).trans hy⟩⟩
          rw [h_traj_ge_s π₁ ω k hk hsk, h_traj_ge_s π₂ ω k hk hsk, hA_eq, hx_eq, hpref_eq]
    have h_fiber_avg : ∀ (k : ℕ) (hk : k + 1 ≤ n) (T : Finset (Fin n)) (g : Fin n)
        (f : Equiv.Perm (Fin n) → ℝ),
        T.card = k → g ∉ T →
        (∀ π₁ π₂ : Equiv.Perm (Fin n),
          (∀ (r : ℕ) (hr : r < k), π₁ ⟨r, lt_of_lt_of_le hr (Nat.le_of_succ_le hk)⟩ =
            π₂ ⟨r, lt_of_lt_of_le hr (Nat.le_of_succ_le hk)⟩) → f π₁ = f π₂) →
        let evT := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun π => arrivalPrefixSet π k = T)
        let evTg := evT.filter (fun π => π ⟨k, hk⟩ = g)
        (n - k : ℕ) * evTg.card = evT.card ∧
        ((n - k : ℕ) : ℝ) * (∑ π ∈ evTg, f π) = ∑ π ∈ evT, f π := by
      intro k hk T g f hT_card hgT hf_loc evT evTg
      let complT := (Finset.univ : Finset (Fin n)) \ T
      have hcompl_card : complT.card = n - k := by
        dsimp only [complT]
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hT_card]
      have hmaps : ∀ π ∈ evT, π ⟨k, hk⟩ ∈ complT := by
        intro π hπ
        have hpref : arrivalPrefixSet π k = T := (Finset.mem_filter.mp hπ).2
        have hnot := (h_pref_succ π k hk).2
        rw [hpref] at hnot
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩
      have hswap_bij : ∀ g' ∈ complT,
          (evT.filter (fun π => π ⟨k, hk⟩ = g')).card = evTg.card ∧
          (∑ π ∈ evT.filter (fun π => π ⟨k, hk⟩ = g'), f π) = ∑ π ∈ evTg, f π := by
        intro g' hg'c
        have hg'T : g' ∉ T := (Finset.mem_sdiff.mp hg'c).2
        have hbij_mem : ∀ (a b : Fin n), a ∉ T → b ∉ T →
            ∀ π ∈ evT.filter (fun π => π ⟨k, hk⟩ = a),
              (Equiv.swap a b * π) ∈ evT.filter (fun π => π ⟨k, hk⟩ = b) ∧
              (∀ (r : ℕ) (hr : r < k),
                (Equiv.swap a b * π) ⟨r, lt_of_lt_of_le hr (Nat.le_of_succ_le hk)⟩ =
                π ⟨r, lt_of_lt_of_le hr (Nat.le_of_succ_le hk)⟩) := by
          intro a b haT hbT π hπ
          rcases Finset.mem_filter.mp hπ with ⟨hπ_evT, hπ_k⟩
          have hpref : arrivalPrefixSet π k = T := (Finset.mem_filter.mp hπ_evT).2
          have hfix_r : ∀ (r : ℕ) (hr : r < k),
              (Equiv.swap a b * π) ⟨r, lt_of_lt_of_le hr (Nat.le_of_succ_le hk)⟩ =
              π ⟨r, lt_of_lt_of_le hr (Nat.le_of_succ_le hk)⟩ := by
            intro r hr
            let idx : Fin n := ⟨r, lt_of_lt_of_le hr (Nat.le_of_succ_le hk)⟩
            have hmemT : π idx ∈ T := by
              rw [← hpref]
              exact Finset.mem_image.mpr ⟨idx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩, rfl⟩
            change Equiv.swap a b (π idx) = π idx
            exact Equiv.swap_apply_of_ne_of_ne (fun h => haT (h ▸ hmemT)) (fun h => hbT (h ▸ hmemT))
          have hpref' : arrivalPrefixSet (Equiv.swap a b * π) k = T := by
            rw [← hpref]
            dsimp only [arrivalPrefixSet]
            ext y
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨fun ⟨idx, hidx, hy⟩ => ⟨idx, hidx, (hfix_r idx.1 hidx).symm.trans hy⟩,
              fun ⟨idx, hidx, hy⟩ => ⟨idx, hidx, (hfix_r idx.1 hidx).trans hy⟩⟩
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpref'⟩, ?_⟩,
            hfix_r⟩
          change Equiv.swap a b (π ⟨k, hk⟩) = b
          rw [hπ_k, Equiv.swap_apply_left]
        constructor
        · refine Finset.card_bij (fun π _ => Equiv.swap g' g * π)
            (fun π hπ => (hbij_mem g' g hg'T hgT π hπ).1)
            (fun _ _ _ _ heq => mul_left_cancel heq) ?_
          intro π hπ
          refine ⟨Equiv.swap g g' * π, (hbij_mem g g' hgT hg'T π hπ).1, ?_⟩
          dsimp only; ext idx; simp [Equiv.swap_comm g' g]
        · refine Finset.sum_nbij (fun π => Equiv.swap g' g * π)
            (fun π hπ => (hbij_mem g' g hg'T hgT π hπ).1)
            (fun _ _ _ _ heq => mul_left_cancel heq) ?_
            (fun π hπ => (hf_loc _ _ (hbij_mem g' g hg'T hgT π hπ).2).symm)
          intro π hπ
          refine ⟨Equiv.swap g g' * π, (hbij_mem g g' hgT hg'T π hπ).1, ?_⟩
          dsimp only; ext idx; simp [Equiv.swap_comm g' g]
      have hcard_part : evT.card = ∑ g' ∈ complT, (evT.filter (fun π => π ⟨k, hk⟩ = g')).card := by
        have h := Finset.sum_fiberwise_of_maps_to (s := evT) (t := complT)
          (g := fun π : Equiv.Perm (Fin n) => π ⟨k, hk⟩) hmaps (fun _ => (1 : ℕ))
        simpa using h.symm
      have hsum_part : (∑ π ∈ evT, f π) =
          ∑ g' ∈ complT, ∑ π ∈ evT.filter (fun π => π ⟨k, hk⟩ = g'), f π :=
        (Finset.sum_fiberwise_of_maps_to hmaps f).symm
      constructor
      · rw [hcard_part]
        have hconst : (∑ g' ∈ complT, (evT.filter (fun π => π ⟨k, hk⟩ = g')).card) =
            ∑ _ ∈ complT, evTg.card :=
          Finset.sum_congr rfl fun g' hg' => (hswap_bij g' hg').1
        rw [hconst, Finset.sum_const, smul_eq_mul, hcompl_card]
      · rw [hsum_part]
        have hconst : (∑ g' ∈ complT, ∑ π ∈ evT.filter (fun π => π ⟨k, hk⟩ = g'), f π) =
            ∑ _ ∈ complT, ∑ π ∈ evTg, f π :=
          Finset.sum_congr rfl fun g' hg' => (hswap_bij g' hg').2
        rw [hconst, Finset.sum_const, nsmul_eq_mul, hcompl_card]
    have h_evStep_eq : ∀ (k : ℕ) (hk : k + 1 ≤ n) (S : Finset (Fin n)) (g : Fin n),
        g ∈ S →
        ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun π => arrivalPrefixSet π (k + 1) = S ∧ π ⟨k, hk⟩ = g)) =
        (((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun π => arrivalPrefixSet π k = S.erase g)).filter (fun π => π ⟨k, hk⟩ = g)) := by
      intro k hk S g hgS
      ext π
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      obtain ⟨hins, hnot⟩ := h_pref_succ π k hk
      constructor
      · rintro ⟨hprefS, hπg⟩
        refine ⟨?_, hπg⟩
        have hg_not : g ∉ arrivalPrefixSet π k := hπg ▸ hnot
        rw [← hprefS, hins, hπg]
        exact (Finset.erase_insert hg_not).symm
      · rintro ⟨hprefT, hπg⟩
        refine ⟨?_, hπg⟩
        rw [hins, hπg, hprefT]
        exact Finset.insert_erase hgS
    have h_evStep_from_law : ∀ (k : ℕ) (hk : k + 1 ≤ n) (S : Finset (Fin n)) (g : Fin n),
        S.card = k + 1 → g ∈ S →
        (∀ A : Finset (Fin n),
          let evT := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
            (fun π => arrivalPrefixSet π k = S.erase g)
          (∑ π ∈ evT, (abhmSeedSpaceMeasure n).real {ω | traj π ω k = A}) =
            (evT.card : ℝ) * abhmMuProg s F u P (S.erase g) A) →
        ∀ A : Finset (Fin n),
          let evg := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
            (fun π => arrivalPrefixSet π (k + 1) = S ∧ π ⟨k, hk⟩ = g)
          (∑ π ∈ evg, (abhmSeedSpaceMeasure n).real {ω | traj π ω k = A}) =
            (evg.card : ℝ) * abhmMuProg s F u P (S.erase g) A := by
      intro k hk S g hScard hgS hlaw_T A evg
      have hk0 : k ≤ n := Nat.le_of_succ_le hk
      have hnk_pos : (0 : ℝ) < ((n - k : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      let T := S.erase g
      have hT_card : T.card = k := by rw [Finset.card_erase_of_mem hgS, hScard]; omega
      have hgT : g ∉ T := Finset.notMem_erase g S
      let fA : Equiv.Perm (Fin n) → ℝ :=
        fun π => (abhmSeedSpaceMeasure n).real {ω | traj π ω k = A}
      have hfA_loc : ∀ π₁ π₂ : Equiv.Perm (Fin n),
          (∀ (r : ℕ) (hr : r < k), π₁ ⟨r, lt_of_lt_of_le hr hk0⟩ = π₂ ⟨r, lt_of_lt_of_le hr hk0⟩) →
          fA π₁ = fA π₂ := by
        intro π₁ π₂ heq
        dsimp only [fA]; congr 1; ext ω; simp only [Set.mem_setOf_eq]
        rw [h_perm_loc k hk0 π₁ π₂ ω heq]
      obtain ⟨hcard_rel, hsum_rel⟩ := h_fiber_avg k hk T g fA hT_card hgT hfA_loc
      have hlawA := hlaw_T A
      have hevg_eq : evg = (((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun π => arrivalPrefixSet π k = T)).filter (fun π => π ⟨k, hk⟩ = g)) :=
        h_evStep_eq k hk S g hgS
      rw [hevg_eq]
      have hcard_cast : (((n - k : ℕ) : ℝ) *
          ((((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
            (fun π => arrivalPrefixSet π k = T)).filter (fun π => π ⟨k, hk⟩ = g)).card : ℝ)) =
          (((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
            (fun π => arrivalPrefixSet π k = T)).card : ℝ) := by
        exact_mod_cast hcard_rel
      have h1 : ((n - k : ℕ) : ℝ) *
          (∑ π ∈ (((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
            (fun π => arrivalPrefixSet π k = T)).filter (fun π => π ⟨k, hk⟩ = g)), fA π) =
          ((n - k : ℕ) : ℝ) *
          (((((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
            (fun π => arrivalPrefixSet π k = T)).filter (fun π => π ⟨k, hk⟩ = g)).card : ℝ) *
            abhmMuProg s F u P T A) := by
        rw [hsum_rel, hlawA, ← mul_assoc, hcard_cast]
      exact mul_left_cancel₀ hnk_pos.ne' h1
    have h_law_ind : ∀ (k : ℕ) (hk : k ≤ n) (S : Finset (Fin n)) (C : Finset (Fin n)),
        S.card = k →
          let evS := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
            (fun π => arrivalPrefixSet π k = S)
          (∑ π ∈ evS, (abhmSeedSpaceMeasure n).real {ω | traj π ω k = C}) =
            (evS.card : ℝ) * abhmMuProg s F u P S C := by
      intro k
      induction k with
      | zero =>
        intro _ S C hS_card evS
        have hS_emp : S = ∅ := Finset.card_eq_zero.mp hS_card
        subst hS_emp
        rw [h_le_s u P ∅ (Nat.zero_le s)]
        dsimp only [abhmEmptyLaw]
        by_cases hC : C = ∅
        · subst hC
          rw [if_pos rfl, mul_one]
          have hprob1 : ∀ π : Equiv.Perm (Fin n),
              (abhmSeedSpaceMeasure n).real {ω | traj π ω 0 = ∅} = 1 := by
            intro π
            have heq : {ω : Fin n → ℝ | traj π ω 0 = ∅} = Set.univ := by ext ω; simp [h_traj_zero]
            rw [heq, measureReal_def, measure_univ, ENNReal.toReal_one]
          calc (∑ π ∈ evS, (abhmSeedSpaceMeasure n).real {ω | traj π ω 0 = ∅})
              = ∑ _ ∈ evS, (1 : ℝ) := Finset.sum_congr rfl fun π _ => hprob1 π
            _ = (evS.card : ℝ) := by simp
        · rw [if_neg hC, mul_zero]
          refine Finset.sum_eq_zero fun π _ => ?_
          have heq : {ω : Fin n → ℝ | traj π ω 0 = C} = ∅ := by
            ext ω; simp [h_traj_zero, Ne.symm hC]
          rw [heq, measureReal_empty]
      | succ k ih =>
        intro hk S C hS_card evS
        have hk0 : k ≤ n := Nat.le_of_succ_le hk
        have h_maps_S : ∀ π ∈ evS, π ⟨k, hk⟩ ∈ S := by
          intro π hπ
          have hpref : arrivalPrefixSet π (k + 1) = S := (Finset.mem_filter.mp hπ).2
          rw [← hpref, (h_pref_succ π k hk).1]
          exact Finset.mem_insert_self _ _
        have h_evStep_filt : ∀ g : Fin n,
            evS.filter (fun π => π ⟨k, hk⟩ = g) =
            (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
              (fun π => arrivalPrefixSet π (k + 1) = S ∧ π ⟨k, hk⟩ = g) := by
          intro g; ext π; simp [evS]
        have h_evStep_prev : ∀ g ∈ S, ∀ A : Finset (Fin n),
            (∑ π ∈ evS.filter (fun π => π ⟨k, hk⟩ = g),
              (abhmSeedSpaceMeasure n).real {ω | traj π ω k = A}) =
            ((evS.filter (fun π => π ⟨k, hk⟩ = g)).card : ℝ) *
              abhmMuProg s F u P (S.erase g) A := by
          intro g hgS A
          rw [h_evStep_filt g]
          exact h_evStep_from_law k hk S g hS_card hgS
            (fun A' => ih hk0 (S.erase g) A' (by rw [Finset.card_erase_of_mem hgS, hS_card]; omega)) A
        by_cases hks : k < s
        · rw [h_le_s u P S (by omega),
              (Finset.sum_fiberwise_of_maps_to h_maps_S
                (fun π => (abhmSeedSpaceMeasure n).real {ω | traj π ω (k + 1) = C})).symm]
          have h_each : ∀ g ∈ S,
              (∑ π ∈ evS.filter (fun π => π ⟨k, hk⟩ = g),
                (abhmSeedSpaceMeasure n).real {ω | traj π ω (k + 1) = C}) =
              ((evS.filter (fun π => π ⟨k, hk⟩ = g)).card : ℝ) * abhmEmptyLaw C := by
            intro g hgS
            have htr : ∀ π, (abhmSeedSpaceMeasure n).real {ω | traj π ω (k + 1) = C} =
                (abhmSeedSpaceMeasure n).real {ω | traj π ω k = C} := by
              intro π; congr 1; ext ω; simp only [Set.mem_setOf_eq, h_traj_lt_s π ω k hk hks]
            simp_rw [htr]
            rw [h_evStep_prev g hgS C,
                h_le_s u P (S.erase g) (by rw [Finset.card_erase_of_mem hgS, hS_card]; omega)]
          rw [Finset.sum_congr rfl fun g hgS => h_each g hgS, ← Finset.sum_mul]
          congr 1
          have hpart_card := (Finset.sum_fiberwise_of_maps_to (s := evS) (t := S)
            (g := fun π : Equiv.Perm (Fin n) => π ⟨k, hk⟩) h_maps_S (fun _ => (1 : ℕ))).symm
          have hpart_card' : evS.card = ∑ g ∈ S, (evS.filter (fun π => π ⟨k, hk⟩ = g)).card := by
            simpa using hpart_card
          rw [hpart_card', Nat.cast_sum]
        · have hsk : s ≤ k := Nat.le_of_not_lt hks
          have hs_lt : s < S.card := by omega
          have h_evStep_symm : ∀ g ∈ S, ∀ g' ∈ S,
              (evS.filter (fun π => π ⟨k, hk⟩ = g')).card =
              (evS.filter (fun π => π ⟨k, hk⟩ = g)).card := by
            intro g hgS g' hg'S
            have hswap_S : ∀ a ∈ S, ∀ b ∈ S,
                ∀ π ∈ evS.filter (fun π => π ⟨k, hk⟩ = a),
                  (Equiv.swap a b * π) ∈ evS.filter (fun π => π ⟨k, hk⟩ = b) := by
              intro a haS b hbS π hπ
              rcases Finset.mem_filter.mp hπ with ⟨hπ_evS, hπ_k⟩
              have hpref : arrivalPrefixSet π (k + 1) = S := (Finset.mem_filter.mp hπ_evS).2
              have hmem_iff : ∀ x : Fin n, Equiv.swap a b x ∈ S ↔ x ∈ S := by
                intro x
                by_cases hxa : x = a
                · subst hxa; simp [haS, hbS]
                · by_cases hxb : x = b
                  · subst hxb; simp [haS, hbS]
                  · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
              have hpref' : arrivalPrefixSet (Equiv.swap a b * π) (k + 1) = S := by
                ext y; constructor
                · intro hy
                  rcases Finset.mem_image.mp hy with ⟨idx, hidx, rfl⟩
                  change Equiv.swap a b (π idx) ∈ S
                  rw [hmem_iff, ← hpref]
                  exact Finset.mem_image.mpr ⟨idx, hidx, rfl⟩
                · intro hyS
                  have hsy : Equiv.swap a b y ∈ arrivalPrefixSet π (k + 1) :=
                    hpref ▸ (hmem_iff y).mpr hyS
                  rcases Finset.mem_image.mp hsy with ⟨idx, hidx, hπ_idx⟩
                  refine Finset.mem_image.mpr ⟨idx, hidx, ?_⟩
                  change Equiv.swap a b (π idx) = y
                  rw [hπ_idx, Equiv.swap_apply_self]
              refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpref'⟩, ?_⟩
              change Equiv.swap a b (π ⟨k, hk⟩) = b
              rw [hπ_k, Equiv.swap_apply_left]
            refine Finset.card_bij (fun π _ => Equiv.swap g' g * π)
              (fun π hπ => hswap_S g' hg'S g hgS π hπ)
              (fun _ _ _ _ heq => mul_left_cancel heq) ?_
            intro π hπ
            refine ⟨Equiv.swap g g' * π, hswap_S g hgS g' hg'S π hπ, ?_⟩
            dsimp only; ext idx; simp [Equiv.swap_comm g' g]
          have h_evS_card_rel : ∀ g ∈ S,
              S.card * (evS.filter (fun π => π ⟨k, hk⟩ = g)).card = evS.card := by
            intro g hgS
            have hpart := (Finset.sum_fiberwise_of_maps_to (s := evS) (t := S)
              (g := fun π : Equiv.Perm (Fin n) => π ⟨k, hk⟩) h_maps_S (fun _ => (1 : ℕ))).symm
            have hpart' : evS.card = ∑ g' ∈ S, (evS.filter (fun π => π ⟨k, hk⟩ = g')).card := by
              simpa using hpart
            rw [hpart', Finset.sum_congr rfl fun g' hg' => h_evStep_symm g hgS g' hg',
              Finset.sum_const, smul_eq_mul]
          have h_each_row : ∀ g ∈ S,
              (∑ π ∈ evS.filter (fun π => π ⟨k, hk⟩ = g),
                (abhmSeedSpaceMeasure n).real {ω | traj π ω (k + 1) = C}) =
              ((evS.filter (fun π => π ⟨k, hk⟩ = g)).card : ℝ) *
                abhmRowTrans (abhmMuProg s F u P (S.erase g)) (abhmQProg s F u P S g) g C := by
            intro g hgS
            let evg := evS.filter (fun π => π ⟨k, hk⟩ = g)
            have h_pi_val : ∀ π ∈ evg,
                (abhmSeedSpaceMeasure n).real {ω | traj π ω (k + 1) = C} =
                ∑ A : Finset (Fin n),
                  ((if insert g A = C then p_fn S g A else 0) +
                   (if A = C then 1 - p_fn S g A else 0)) *
                  (abhmSeedSpaceMeasure n).real {ω | traj π ω k = A} := by
              intro π hπ
              rcases Finset.mem_filter.mp hπ with ⟨hπ_evS, hπg⟩
              have hprefS : arrivalPrefixSet π (k + 1) = S := (Finset.mem_filter.mp hπ_evS).2
              have hg_not_prev : g ∉ arrivalPrefixSet π k := hπg ▸ (h_pref_succ π k hk).2
              have hstep_π : ∀ ω : Fin n → ℝ,
                  traj π ω (k + 1) =
                    if 0 ≤ ω g ∧ ω g < p_fn S g (traj π ω k) then
                      insert g (traj π ω k)
                    else
                      traj π ω k := by
                intro ω
                have h := h_traj_ge_s π ω k hk hsk
                dsimp only at h
                rw [h, hprefS, hπg]
              let EA : Finset (Fin n) → Set (Fin n → ℝ) := fun A => {ω | traj π ω k = A}
              let slice : Finset (Fin n) → Set (Fin n → ℝ) :=
                fun A => EA A ∩ {ω | traj π ω (k + 1) = C}
              have hslice_meas : ∀ A, MeasurableSet (slice A) :=
                fun A => (h_meas_traj π k A).inter (h_meas_traj π (k + 1) C)
              have hslice_disj : Pairwise (fun A₁ A₂ => Disjoint (slice A₁) (slice A₂)) := by
                intro A₁ A₂ hne; rw [Set.disjoint_left]; intro ω h1 h2
                exact hne (h1.1.symm.trans h2.1)
              have hslice_union :
                  (⋃ A ∈ (Finset.univ : Finset (Finset (Fin n))), slice A) =
                  {ω | traj π ω (k + 1) = C} := by
                ext ω
                simp only [Set.mem_iUnion, Finset.mem_univ, slice, EA,
                  Set.mem_inter_iff, Set.mem_setOf_eq]
                exact ⟨fun ⟨_, _, _, hC⟩ => hC, fun hC => ⟨traj π ω k, trivial, rfl, hC⟩⟩
              rw [← hslice_union,
                  measureReal_biUnion_finset (fun A₁ _ A₂ _ hne => hslice_disj hne)
                    (fun A _ => hslice_meas A)]
              refine Finset.sum_congr rfl fun A _ => ?_
              have hEA_indep : ∀ ω ω' : Fin n → ℝ,
                  (∀ y : Fin n, y ≠ g → ω y = ω' y) → (ω ∈ EA A ↔ ω' ∈ EA A) := by
                intro ω ω' h_ne
                have h_eq : traj π ω k = traj π ω' k :=
                  h_coord_loc π k hk0 ω ω' (fun y hy => h_ne y (fun hyg => hg_not_prev (hyg ▸ hy)))
                simp only [EA, Set.mem_setOf_eq, h_eq]
              obtain ⟨hp0, hp1, _⟩ := h_p_bounds S hs_lt g hgS A
              obtain ⟨hacc_real, hrej_real⟩ :=
                lem_coord g (p_fn S g A) (EA A) hp0 hp1 (h_meas_traj π k A) hEA_indep
              by_cases hExt : insert g A = C
              · by_cases hAC : A = C
                · have hslice_eq : slice A = EA A := by
                    ext ω
                    simp only [slice, EA, Set.mem_inter_iff, Set.mem_setOf_eq, and_iff_left_iff_imp]
                    intro hωA; rw [hstep_π ω, hωA]; split_ifs <;> assumption
                  rw [hslice_eq, if_pos hExt, if_pos hAC]; ring
                · have hslice_eq : slice A = EA A ∩ {ω | 0 ≤ ω g ∧ ω g < p_fn S g A} := by
                    ext ω
                    simp only [slice, EA, Set.mem_inter_iff, Set.mem_setOf_eq]
                    constructor
                    · rintro ⟨hωA, hωC⟩
                      refine ⟨hωA, ?_⟩
                      rw [hstep_π ω, hωA] at hωC
                      by_contra hnacc; rw [if_neg hnacc] at hωC; exact hAC hωC
                    · rintro ⟨hωA, hacc⟩
                      exact ⟨hωA, by rw [hstep_π ω, hωA, if_pos hacc]; exact hExt⟩
                  rw [hslice_eq, hacc_real, if_pos hExt, if_neg hAC, add_zero]
              · by_cases hAC : A = C
                · have hslice_eq : slice A = EA A ∩ {ω | ¬ (0 ≤ ω g ∧ ω g < p_fn S g A)} := by
                    ext ω
                    simp only [slice, EA, Set.mem_inter_iff, Set.mem_setOf_eq]
                    constructor
                    · rintro ⟨hωA, hωC⟩
                      refine ⟨hωA, fun hacc => ?_⟩
                      rw [hstep_π ω, hωA, if_pos hacc] at hωC; exact hExt hωC
                    · rintro ⟨hωA, hnacc⟩
                      exact ⟨hωA, by rw [hstep_π ω, hωA, if_neg hnacc]; exact hAC⟩
                  rw [hslice_eq, hrej_real, if_neg hExt, if_pos hAC, zero_add]
                · have hslice_eq : slice A = ∅ := by
                    ext ω
                    simp only [slice, EA, Set.mem_inter_iff, Set.mem_setOf_eq,
                      Set.mem_empty_iff_false, iff_false, not_and]
                    intro hωA; rw [hstep_π ω, hωA]; split_ifs <;> assumption
                  rw [hslice_eq, measureReal_empty, if_neg hExt, if_neg hAC, add_zero, zero_mul]
            have hsum_pi : (∑ π ∈ evg, (abhmSeedSpaceMeasure n).real {ω | traj π ω (k + 1) = C}) =
                ∑ A : Finset (Fin n),
                  ((if insert g A = C then p_fn S g A else 0) +
                   (if A = C then 1 - p_fn S g A else 0)) *
                  (∑ π ∈ evg, (abhmSeedSpaceMeasure n).real {ω | traj π ω k = A}) := by
              rw [Finset.sum_congr rfl fun π hπ => h_pi_val π hπ, Finset.sum_comm]
              exact Finset.sum_congr rfl fun A _ => (Finset.mul_sum _ _ _).symm
            rw [hsum_pi]
            have hterm_eq : ∀ A : Finset (Fin n),
                ((if insert g A = C then p_fn S g A else 0) +
                 (if A = C then 1 - p_fn S g A else 0)) *
                ((evg.card : ℝ) * abhmMuProg s F u P (S.erase g) A) =
                (evg.card : ℝ) *
                  ((if insert g A = C then abhmQProg s F u P S g A else 0) +
                   (if A = C then abhmMuProg s F u P (S.erase g) A - abhmQProg s F u P S g A else 0)) := by
              intro A
              have hpm := (h_p_bounds S hs_lt g hgS A).2.2
              by_cases h1 : insert g A = C <;> by_cases h2 : A = C
              · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2]; ring
              · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2]
                linear_combination (evg.card : ℝ) * hpm
              · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
                linear_combination -((evg.card : ℝ) * hpm)
              · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]; ring
            have hrew : (∑ A : Finset (Fin n),
                ((if insert g A = C then p_fn S g A else 0) +
                 (if A = C then 1 - p_fn S g A else 0)) *
                (∑ π ∈ evg, (abhmSeedSpaceMeasure n).real {ω | traj π ω k = A})) =
                (evg.card : ℝ) * ∑ A : Finset (Fin n),
                  ((if insert g A = C then abhmQProg s F u P S g A else 0) +
                   (if A = C then abhmMuProg s F u P (S.erase g) A - abhmQProg s F u P S g A else 0)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun A _ => ?_
              rw [h_evStep_prev g hgS A]
              exact hterm_eq A
            rw [hrew]
            congr 1
            rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ C]
            simp only [Finset.mem_univ, ↓reduceIte, abhmRowTrans]
            ring
          rw [(Finset.sum_fiberwise_of_maps_to h_maps_S
                (fun π => (abhmSeedSpaceMeasure n).real {ω | traj π ω (k + 1) = C})).symm,
              Finset.sum_congr rfl fun g hgS => h_each_row g hgS,
              (h_trans u P hP_li S hs_lt).2.2.2 C]
          dsimp only [abhmRowAvg]
          have hScard_ne : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun g hgS => ?_
          have hcard_g : (S.card : ℝ) * ((evS.filter (fun π => π ⟨k, hk⟩ = g)).card : ℝ) =
              (evS.card : ℝ) := by exact_mod_cast h_evS_card_rel g hgS
          have hdiv_g : ((evS.filter (fun π => π ⟨k, hk⟩ = g)).card : ℝ) =
              (evS.card : ℝ) * (1 / (S.card : ℝ)) := by
            field_simp [hScard_ne]; linarith
          rw [hdiv_g]; ring
    refine ⟨h_rej, h_pathwise, ?_⟩
    intro k hk hsk S g hScard hgPS ev
    have hk0 : k ≤ n := Nat.le_of_succ_le hk
    have hgS : g ∈ S := (hP_M S).1 hgPS
    have hs_lt : s < S.card := by omega
    have h_ev_prev : ∀ A : Finset (Fin n),
        (∑ π ∈ ev, (abhmSeedSpaceMeasure n).real {ω | traj π ω k = A}) =
          (ev.card : ℝ) * abhmMuProg s F u P (S.erase g) A :=
      h_evStep_from_law k hk S g hScard hgS
        (fun A => h_law_ind k hk0 (S.erase g) A
          (by rw [Finset.card_erase_of_mem hgS, hScard]; omega))
    have h_pi_adm : ∀ π ∈ ev,
        mod.seedMeasure.real {ω | g ∈ (runDetRepAdmissionSteps (mod.det ω) P u π (k + 1) hk).2} =
        ∑ A : Finset (Fin n),
          p_fn S g A * (abhmSeedSpaceMeasure n).real {ω | traj π ω k = A} := by
      intro π hπ
      rcases (Finset.mem_filter.mp hπ).2 with ⟨hprefS, hπg⟩
      have hg_not_prev : g ∉ arrivalPrefixSet π k := hπg ▸ (h_pref_succ π k hk).2
      have hg_not_acc : ∀ ω : Fin n → ℝ, g ∉ traj π ω k := by
        intro ω hg_in
        dsimp only [traj] at hg_in
        rw [dif_pos hk0] at hg_in
        have hsub := (h_pathwise ω π k hk0).1
        rw [h_st_fst (mod.det ω) P u π k hk0] at hsub
        exact hg_not_prev (hsub hg_in)
      have h_iff : ∀ ω : Fin n → ℝ,
          g ∈ (runDetRepAdmissionSteps (mod.det ω) P u π (k + 1) hk).2 ↔
            (0 ≤ ω g ∧ ω g < p_fn S g (traj π ω k)) := by
        intro ω
        have hstep := h_traj_ge_s π ω k hk hsk
        dsimp only at hstep
        rw [hprefS, hπg] at hstep
        have htr1 : traj π ω (k + 1) =
            (runDetRepAdmissionSteps (mod.det ω) P u π (k + 1) hk).2 := dif_pos hk
        rw [← htr1, hstep]
        by_cases hacc : 0 ≤ ω g ∧ ω g < p_fn S g (traj π ω k) <;>
          simp [hacc, hg_not_acc ω]
      let EA : Finset (Fin n) → Set (Fin n → ℝ) := fun A => {ω | traj π ω k = A}
      let sliceG : Finset (Fin n) → Set (Fin n → ℝ) :=
        fun A => EA A ∩ {ω | 0 ≤ ω g ∧ ω g < p_fn S g A}
      have hIco : ∀ A, MeasurableSet {ω : Fin n → ℝ | 0 ≤ ω g ∧ ω g < p_fn S g A} :=
        fun _ => (measurable_pi_apply g) measurableSet_Ico
      have hslice_meas : ∀ A, MeasurableSet (sliceG A) :=
        fun A => (h_meas_traj π k A).inter (hIco A)
      have hslice_disj : Pairwise (fun A₁ A₂ => Disjoint (sliceG A₁) (sliceG A₂)) := by
        intro A₁ A₂ hne; rw [Set.disjoint_left]; intro ω h1 h2
        exact hne (h1.1.symm.trans h2.1)
      have hslice_union :
          (⋃ A ∈ (Finset.univ : Finset (Finset (Fin n))), sliceG A) =
          {ω : Fin n → ℝ | g ∈ (runDetRepAdmissionSteps (mod.det ω) P u π (k + 1) hk).2} := by
        ext ω
        constructor
        · intro hL
          rcases Set.mem_iUnion₂.mp hL with ⟨A, _, hAs⟩
          have hA : traj π ω k = A := hAs.1
          have hacc : 0 ≤ ω g ∧ ω g < p_fn S g A := hAs.2
          rw [← hA] at hacc
          show g ∈ (runDetRepAdmissionSteps (mod.det ω) P u π (k + 1) hk).2
          exact (h_iff ω).mpr hacc
        · intro hR
          have hR' : g ∈ (runDetRepAdmissionSteps (mod.det ω) P u π (k + 1) hk).2 := hR
          have hacc : 0 ≤ ω g ∧ ω g < p_fn S g (traj π ω k) := (h_iff ω).mp hR'
          exact Set.mem_iUnion₂.mpr ⟨traj π ω k, Finset.mem_univ _, ⟨rfl, hacc⟩⟩
      change (abhmSeedSpaceMeasure n).real
        {ω : Fin n → ℝ | g ∈ (runDetRepAdmissionSteps (mod.det ω) P u π (k + 1) hk).2} = _
      rw [← hslice_union,
          measureReal_biUnion_finset (fun A₁ _ A₂ _ hne => hslice_disj hne)
            (fun A _ => hslice_meas A)]
      refine Finset.sum_congr rfl fun A _ => ?_
      have hEA_indep : ∀ ω ω' : Fin n → ℝ,
          (∀ y : Fin n, y ≠ g → ω y = ω' y) → (ω ∈ EA A ↔ ω' ∈ EA A) := by
        intro ω ω' h_ne
        have h_eq : traj π ω k = traj π ω' k :=
          h_coord_loc π k hk0 ω ω' (fun y hy => h_ne y (fun hyg => hg_not_prev (hyg ▸ hy)))
        simp only [EA, Set.mem_setOf_eq, h_eq]
      obtain ⟨hp0, hp1, _⟩ := h_p_bounds S hs_lt g hgS A
      exact (lem_coord g (p_fn S g A) (EA A) hp0 hp1 (h_meas_traj π k A) hEA_indep).1
    calc
      ∑ π ∈ ev, mod.seedMeasure.real
          {ω | g ∈ (runDetRepAdmissionSteps (mod.det ω) P u π (k + 1) hk).2}
          = ∑ π ∈ ev, ∑ A : Finset (Fin n),
              p_fn S g A * (abhmSeedSpaceMeasure n).real {ω | traj π ω k = A} :=
            Finset.sum_congr rfl fun π hπ => h_pi_adm π hπ
      _ = ∑ A : Finset (Fin n),
            p_fn S g A * ∑ π ∈ ev, (abhmSeedSpaceMeasure n).real {ω | traj π ω k = A} := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun A _ => (Finset.mul_sum _ _ _).symm
      _ = (ev.card : ℝ) * ∑ A : Finset (Fin n), abhmQProg s F u P S g A := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun A _ => ?_
            rw [h_ev_prev A, ← mul_assoc, mul_comm (p_fn S g A) (ev.card : ℝ),
              mul_assoc, (h_p_bounds S hs_lt g hgS A).2.2]
      _ = admitRate s (k + 1) * (ev.card : ℝ) := by
            rw [(h_trans u P hP_li S hs_lt).2.2.1 g hgPS, hScard, mul_comm]
  have h_wm_persist : ∀ {n : ℕ} (M : Matroid (Fin n)) (w : Fin n → ℝ),
      let v := weightedMatroidVal M w
      let P := canonicalDemand v
      (∀ T : Finset (Fin n), P T ⊆ T ∧ M.Indep (P T : Set (Fin n))) ∧
      (∀ S : Finset (Fin n), ∀ g ∈ P Finset.univ, g ∈ S → g ∈ P S) := by
    intro n M w v P
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
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      rw [h_geom m n hmn] at hle
      have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
      linarith
    have h_psi_inj : Function.Injective (@psiWeight n) := by
      intro X Y hXY
      have hsplit : ∀ A : Finset (Fin n),
          psiWeight A = (A.card : ℝ) + ∑ g ∈ A, (1 / 2 : ℝ) ^ (g.1 + 1) := by
        intro A; simp [psiWeight, Finset.sum_add_distrib]
      have hX0 : 0 ≤ ∑ g ∈ X, (1 / 2 : ℝ) ^ (g.1 + 1) :=
        Finset.sum_nonneg (fun _ _ => by positivity)
      have hY0 : 0 ≤ ∑ g ∈ Y, (1 / 2 : ℝ) ^ (g.1 + 1) :=
        Finset.sum_nonneg (fun _ _ => by positivity)
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
            (fun _ _ => by positivity) hmA
        have hup : ∑ g ∈ B \ A, (1 / 2 : ℝ) ^ (g.1 + 1) < (1 / 2 : ℝ) ^ (m₀.1 + 1) :=
          h_tail_lt (B \ A) (m₀.1 + 1) (Nat.succ_le_of_lt m₀.2)
            (fun g hg => Nat.succ_le_of_lt (Fin.lt_def.mp (hmB g hg)))
        linarith
      by_contra hne
      let D := (X \ Y) ∪ (Y \ X)
      have hDne : D.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        exact hne (Finset.Subset.antisymm
          (Finset.sdiff_eq_empty_iff_subset.mp (Finset.union_eq_empty.mp hemp).1)
          (Finset.sdiff_eq_empty_iff_subset.mp (Finset.union_eq_empty.mp hemp).2))
      let m₀ := D.min' hDne
      rcases Finset.mem_union.mp (Finset.min'_mem D hDne) with hmXY | hmYX
      · refine h_no_min X Y hδ m₀ hmXY fun g hg => lt_of_le_of_ne
          (Finset.min'_le D g (Finset.mem_union_right _ hg)) fun h => ?_
        have hgY : g ∈ Y := (Finset.mem_sdiff.mp hg).1
        rw [← h] at hgY
        exact (Finset.mem_sdiff.mp hmXY).2 hgY
      · refine h_no_min Y X hδ.symm m₀ hmYX fun g hg => lt_of_le_of_ne
          (Finset.min'_le D g (Finset.mem_union_left _ hg)) fun h => ?_
        have hgX : g ∈ X := (Finset.mem_sdiff.mp hg).1
        rw [← h] at hgX
        exact (Finset.mem_sdiff.mp hmYX).2 hgX
    have h_cd_props : ∀ T : Finset (Fin n),
        P T ⊆ T ∧ M.Indep (P T : Set (Fin n)) ∧
        (∀ Y ⊆ T, demandKeyLe v Y (P T)) ∧
        (∀ X ⊆ T, (∀ Y ⊆ T, demandKeyLe v Y X) → X = P T) := by
      intro T
      have h_refl : ∀ A : Finset (Fin n), demandKeyLe v A A := fun _ => Or.inr ⟨rfl, le_rfl⟩
      have h_trans : ∀ {A B C : Finset (Fin n)},
          demandKeyLe v A B → demandKeyLe v B C → demandKeyLe v A C := by
        intro A B C hAB hBC
        rcases hAB with hlt1 | ⟨heq1, hle1⟩ <;> rcases hBC with hlt2 | ⟨heq2, hle2⟩
        · exact Or.inl (lt_trans hlt1 hlt2)
        · exact Or.inl (heq2 ▸ hlt1)
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
        rcases hAB with hlt1 | ⟨heq1, hle1⟩ <;> rcases hBA with hlt2 | ⟨heq2, hle2⟩
        · exact absurd (lt_trans hlt1 hlt2) (lt_irrefl _)
        · exact absurd (heq2 ▸ hlt1) (lt_irrefl _)
        · exact absurd (heq1 ▸ hlt2) (lt_irrefl _)
        · exact h_psi_inj (le_antisymm hle1 hle2)
      have h_fin_max : ∀ F : Finset (Finset (Fin n)), F.Nonempty →
          ∃ X ∈ F, ∀ Y ∈ F, demandKeyLe v Y X := by
        intro F
        induction F using Finset.induction_on with
        | empty => intro hne; simp at hne
        | @insert A F' _ ih =>
          intro _
          by_cases hF' : F'.Nonempty
          · obtain ⟨ X₀, hX₀, hmax⟩ := ih hF'
            rcases h_total A X₀ with hAX | hXA
            · refine ⟨X₀, Finset.mem_insert_of_mem hX₀, fun Y hY => ?_⟩
              rcases Finset.mem_insert.mp hY with rfl | hYF'
              · exact hAX
              · exact hmax Y hYF'
            · refine ⟨A, Finset.mem_insert_self A F', fun Y hY => ?_⟩
              rcases Finset.mem_insert.mp hY with rfl | hYF'
              · exact h_refl _
              · exact h_trans (hmax Y hYF') hXA
          · rw [Finset.not_nonempty_iff_eq_empty] at hF'; subst hF'
            exact ⟨A, Finset.mem_singleton_self A, fun Y hY =>
              (Finset.mem_singleton.mp hY) ▸ h_refl A⟩
      have hex : ∃ X ∈ T.powerset, ∀ Y ∈ T.powerset, demandKeyLe v Y X :=
        h_fin_max T.powerset ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset T)⟩
      have hcd_eq : P T = Classical.choose hex := dif_pos hex
      have hspec := Classical.choose_spec hex
      rw [← hcd_eq] at hspec
      have hsub : P T ⊆ T := Finset.mem_powerset.mp hspec.1
      have hdom : ∀ Y ⊆ T, demandKeyLe v Y (P T) :=
        fun Y hY => hspec.2 Y (Finset.mem_powerset.mpr hY)
      have hind : M.Indep (P T : Set (Fin n)) := by
        by_contra hdep
        have hv0 : v ∅ = ((0 : ℝ) : WithBot ℝ) := by simp [v, weightedMatroidVal, M.empty_indep]
        have hv_bot : v (P T) = ⊥ := by simp [v, weightedMatroidVal, hdep]
        have h0 := hdom ∅ (Finset.empty_subset T)
        dsimp only [demandKeyLe] at h0
        rw [hv0, hv_bot] at h0
        rcases h0 with hlt | ⟨heq, _⟩
        · exact absurd hlt (by simp)
        · exact absurd heq (by simp)
      exact ⟨hsub, hind, hdom,
        fun X hXT hXdom => h_antisymm (hdom X hXT) (hXdom (P T) hsub)⟩
    have h_rep_aug : ∀ (d₀ : ℕ) (A B : Finset (Fin n)),
        B.card - A.card = d₀ →
        M.Indep (A : Set (Fin n)) → M.Indep (B : Set (Fin n)) → A.card ≤ B.card →
          ∃ K : Finset (Fin n),
            A ⊆ K ∧ K ⊆ A ∪ B ∧ M.Indep (K : Set (Fin n)) ∧ K.card = B.card := by
      intro d₀
      induction d₀ with
      | zero =>
        intro A B _ hA _ _
        exact ⟨A, Finset.Subset.refl A, Finset.subset_union_left, hA, by omega⟩
      | succ d₀ ih =>
        intro A B _ hA hB _
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
    have h_wm_exch : ∀ (X Y : Finset (Fin n)) (x : Fin n),
        M.Indep (X : Set (Fin n)) → M.Indep (Y : Set (Fin n)) → x ∈ X \ Y →
          (M.Indep ((X.erase x : Finset (Fin n)) : Set (Fin n)) ∧
           M.Indep ((insert x Y : Finset (Fin n)) : Set (Fin n))) ∨
          ∃ y ∈ Y \ X,
            M.Indep ((insert y (X.erase x) : Finset (Fin n)) : Set (Fin n)) ∧
            M.Indep (((insert x Y).erase y : Finset (Fin n)) : Set (Fin n)) := by
      intro X Y x hIX hIY hx
      have hxX : x ∈ X := (Finset.mem_sdiff.mp hx).1
      have hxY : x ∉ Y := (Finset.mem_sdiff.mp hx).2
      have hIX_er : M.Indep ((X.erase x : Finset (Fin n)) : Set (Fin n)) :=
        hIX.subset (Finset.coe_subset.mpr (Finset.erase_subset x X))
      by_cases hIY_ins : M.Indep ((insert x Y : Finset (Fin n)) : Set (Fin n))
      · exact Or.inl ⟨hIX_er, hIY_ins⟩
      · let Dset : Finset (Finset (Fin n)) :=
          (insert x Y).powerset.filter (fun D : Finset (Fin n) => ¬ M.Indep (D : Set (Fin n)))
        have hDne : Dset.Nonempty :=
          ⟨insert x Y, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.Subset.rfl, hIY_ins⟩⟩
        obtain ⟨C, hCmem, hCmin⟩ := Finset.exists_min_image Dset Finset.card hDne
        have hCsub : C ⊆ insert x Y := Finset.mem_powerset.mp (Finset.mem_filter.mp hCmem).1
        have hCdep : ¬ M.Indep (C : Set (Fin n)) := (Finset.mem_filter.mp hCmem).2
        have hC_er_ind : ∀ z ∈ C, M.Indep ((C.erase z : Finset (Fin n)) : Set (Fin n)) := by
          intro z hz
          by_contra hdep
          have hz_mem : C.erase z ∈ Dset :=
            Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ((Finset.erase_subset z C).trans hCsub), hdep⟩
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
          have hyC : y ∈ C := (Finset.mem_erase.mp hy).2
          have hy_ins : y ∈ insert x Y := hCsub hyC
          have hC_le : C.card ≤ Y.card + 1 := by
            have := Finset.card_le_card hCsub
            rwa [Finset.card_insert_of_notMem hxY] at this
          have hCy_le : (C.erase y).card ≤ Y.card := by
            have := Finset.card_erase_add_one hyC; omega
          obtain ⟨K, hCyK, hKsub, hKind, hKcard⟩ :=
            h_rep_aug (Y.card - (C.erase y).card) (C.erase y) Y rfl
              (hC_er_ind y hyC) hIY hCy_le
          have hyK : y ∉ K := fun hm => by
            have hCK : C ⊆ K := Finset.insert_erase hyC ▸ Finset.insert_subset hm hCyK
            exact hCdep (hKind.subset (Finset.coe_subset.mpr hCK))
          have hK_ins : K ⊆ insert x Y :=
            hKsub.trans (Finset.union_subset ((Finset.erase_subset y C).trans hCsub)
              (Finset.subset_insert x Y))
          have hK_er : K ⊆ (insert x Y).erase y :=
            fun z hz => Finset.mem_erase.mpr ⟨fun hzy => hyK (hzy ▸ hz), hK_ins hz⟩
          have hcard_er : ((insert x Y).erase y).card ≤ K.card := by
            have := Finset.card_erase_add_one hy_ins
            have := Finset.card_insert_of_notMem hxY
            omega
          exact (Finset.eq_of_subset_of_card_le hK_er hcard_er) ▸ hKind
        have hSubB : ∃ y ∈ C.erase x,
            y ∉ X ∧ M.Indep ((insert y (X.erase x) : Finset (Fin n)) : Set (Fin n)) := by
          have hCx_ind := hC_er_ind x hxC
          by_cases hlt : (X.erase x).card < (C.erase x).card
          · have henc : (X.erase x : Set (Fin n)).encard < (C.erase x : Set (Fin n)).encard := by
              rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard]
              exact_mod_cast hlt
            obtain ⟨y, hy, hy_ind⟩ := hIX_er.exists_insert_of_encard_lt hCx_ind henc
            have hyCx : y ∈ C.erase x := hy.1
            have hyx : y ≠ x := (Finset.mem_erase.mp hyCx).1
            have hyX : y ∉ X := fun hm => hy.2 (Finset.mem_erase.mpr ⟨hyx, hm⟩)
            exact ⟨y, hyCx, hyX, by simpa [Finset.coe_insert] using hy_ind⟩
          · have hCx_le : (C.erase x).card ≤ X.card := by
              have := Finset.card_erase_add_one hxX; omega
            obtain ⟨K, hCxK, hKsub, hKind, hKcard⟩ :=
              h_rep_aug (X.card - (C.erase x).card) (C.erase x) X rfl hCx_ind hIX hCx_le
            have hxK : x ∉ K := fun hm => by
              have hCK : C ⊆ K := Finset.insert_erase hxC ▸ Finset.insert_subset hm hCxK
              exact hCdep (hKind.subset (Finset.coe_subset.mpr hCK))
            have hltK : (X.erase x).card < K.card := by
              have := Finset.card_erase_add_one hxX; omega
            have hencK : (X.erase x : Set (Fin n)).encard < (K : Set (Fin n)).encard := by
              rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard]
              exact_mod_cast hltK
            obtain ⟨y, hy, hy_ind⟩ := hIX_er.exists_insert_of_encard_lt hKind hencK
            have hyx : y ≠ x := fun h => hxK (h ▸ hy.1)
            have hyX : y ∉ X := fun hm => hy.2 (Finset.mem_erase.mpr ⟨hyx, hm⟩)
            have hyCx : y ∈ C.erase x := by
              rcases Finset.mem_union.mp (hKsub hy.1) with h1 | h2
              · exact h1
              · exact absurd h2 hyX
            exact ⟨y, hyCx, hyX, by simpa [Finset.coe_insert] using hy_ind⟩
        obtain ⟨y, hyCx, hyX, hy_ind1⟩ := hSubB
        have hy_ind2 := hSubA y hyCx
        have hyY : y ∈ Y := by
          rcases Finset.mem_insert.mp (hCsub (Finset.mem_erase.mp hyCx).2) with rfl | hm
          · exact absurd rfl (Finset.mem_erase.mp hyCx).1
          · exact hm
        exact Or.inr ⟨y, Finset.mem_sdiff.mpr ⟨hyY, hyX⟩, hy_ind1, hy_ind2⟩
    have h_step_ins : ∀ (T : Finset (Fin n)) (x : Fin n),
        x ∉ T → P (insert x T) ⊆ insert x (P T) := by
      intro T x hxT
      let X := P T
      let Y := P (insert x T)
      obtain ⟨hXT, hIX, hXdom, hXuniq⟩ := h_cd_props T
      obtain ⟨hYT, hIY, hYdom, _⟩ := h_cd_props (insert x T)
      change Y ⊆ insert x X
      by_cases hxY : x ∈ Y
      · have hxX : x ∉ X := fun hm => hxT (hXT hm)
        have h_opt_pair : ∀ (A B : Finset (Fin n)),
            A ⊆ T → B ⊆ insert x T →
            M.Indep (A : Set (Fin n)) → M.Indep (B : Set (Fin n)) →
            (∑ g ∈ Y, w g) + (∑ g ∈ X, w g) = (∑ g ∈ A, w g) + (∑ g ∈ B, w g) →
            psiWeight Y + psiWeight X = psiWeight A + psiWeight B →
            Y = B := by
          intro A B hAT hBT hIA hIB hw_sum hpsi_sum
          have hdA : demandKeyLe v A X := hXdom A hAT
          have hdB : demandKeyLe v B Y := hYdom B hBT
          dsimp only [demandKeyLe, v, weightedMatroidVal] at hdA hdB
          rw [if_pos hIA, if_pos hIX] at hdA
          rw [if_pos hIB, if_pos hIY] at hdB
          have hrAX : ∑ g ∈ A, w g ≤ ∑ g ∈ X, w g := by
            rcases hdA with hlt | ⟨heq, _⟩
            · exact le_of_lt (WithBot.coe_lt_coe.mp hlt)
            · exact le_of_eq (WithBot.coe_inj.mp heq)
          have hrBY : ∑ g ∈ B, w g ≤ ∑ g ∈ Y, w g := by
            rcases hdB with hlt | ⟨heq, _⟩
            · exact le_of_lt (WithBot.coe_lt_coe.mp hlt)
            · exact le_of_eq (WithBot.coe_inj.mp heq)
          have hpsiA : psiWeight A ≤ psiWeight X := by
            rcases hdA with hlt | ⟨_, hle⟩
            · have := WithBot.coe_lt_coe.mp hlt; linarith
            · exact hle
          have hpsiB : psiWeight B ≤ psiWeight Y := by
            rcases hdB with hlt | ⟨_, hle⟩
            · have := WithBot.coe_lt_coe.mp hlt; linarith
            · exact hle
          exact h_psi_inj (by linarith)
        let wpsi : Fin n → ℝ := fun g => 1 + (1 / 2 : ℝ) ^ (g.1 + 1)
        rcases h_wm_exch Y X x hIY hIX (Finset.mem_sdiff.mpr ⟨hxY, hxX⟩) with
          ⟨hI1, hI2⟩ | ⟨f, hf, hI1, hI2⟩
        · have hAT : Y.erase x ⊆ T := fun z hz => by
            rcases Finset.mem_insert.mp (hYT (Finset.erase_subset x Y hz)) with rfl | hzT
            · exact absurd rfl (Finset.mem_erase.mp hz).1
            · exact hzT
          have heqY : Y = insert x X := h_opt_pair (Y.erase x) (insert x X)
            hAT (Finset.insert_subset_insert x hXT) hI1 hI2
            (by linarith [Finset.sum_erase_add Y w hxY, Finset.sum_insert hxX (f := w)])
            (by dsimp only [psiWeight];
                linarith [Finset.sum_erase_add Y wpsi hxY, Finset.sum_insert hxX (f := wpsi)])
          rw [heqY]
        · have hfX : f ∈ X := (Finset.mem_sdiff.mp hf).1
          have hfY : f ∉ Y := (Finset.mem_sdiff.mp hf).2
          have hfx : f ≠ x := fun h => hfY (h ▸ hxY)
          have hAT : insert f (Y.erase x) ⊆ T := by
            refine Finset.insert_subset (hXT hfX) fun z hz => ?_
            rcases Finset.mem_insert.mp (hYT (Finset.erase_subset x Y hz)) with rfl | hzT
            · exact absurd rfl (Finset.mem_erase.mp hz).1
            · exact hzT
          have hBeq : (insert x X).erase f = insert x (X.erase f) :=
            Finset.erase_insert_of_ne (Ne.symm hfx)
          rw [hBeq] at hI2
          have hf_er : f ∉ Y.erase x := fun hm => hfY (Finset.erase_subset x Y hm)
          have hx_er : x ∉ X.erase f := fun hm => hxX (Finset.erase_subset f X hm)
          have heqY : Y = insert x (X.erase f) :=
            h_opt_pair (insert f (Y.erase x)) (insert x (X.erase f))
              hAT (Finset.insert_subset_insert x ((Finset.erase_subset f X).trans hXT)) hI1 hI2
              (by linarith [Finset.sum_erase_add Y w hxY, Finset.sum_insert hf_er (f := w),
                            Finset.sum_erase_add X w hfX, Finset.sum_insert hx_er (f := w)])
              (by dsimp only [psiWeight];
                  linarith [Finset.sum_erase_add Y wpsi hxY, Finset.sum_insert hf_er (f := wpsi),
                            Finset.sum_erase_add X wpsi hfX, Finset.sum_insert hx_er (f := wpsi)])
          rw [heqY]
          exact Finset.insert_subset_insert x (Finset.erase_subset f X)
      · have hYT' : Y ⊆ T := fun z hz => by
          rcases Finset.mem_insert.mp (hYT hz) with rfl | hzT
          · exact absurd hz hxY
          · exact hzT
        have heqY : Y = X :=
          hXuniq Y hYT' (fun Z hZT => hYdom Z (hZT.trans (Finset.subset_insert x T)))
        rw [heqY]
        exact Finset.subset_insert x X
    have h_pers_ind : ∀ (k : ℕ) (S U : Finset (Fin n)),
        (U \ S).card = k → S ⊆ U → P U ∩ S ⊆ P S := by
      intro k
      induction k with
      | zero =>
        intro S U hk hSU
        obtain rfl : S = U := Finset.Subset.antisymm hSU
          (Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hk))
        exact Finset.inter_subset_left
      | succ k ih =>
        intro S U hk hSU
        obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < (U \ S).card)
        have hxU : x ∈ U := (Finset.mem_sdiff.mp hx).1
        have hxS : x ∉ S := (Finset.mem_sdiff.mp hx).2
        let U' := U.erase x
        have hxU' : x ∉ U' := Finset.notMem_erase x U
        have hUeq : insert x U' = U := Finset.insert_erase hxU
        have hSU' : S ⊆ U' := fun z hz => Finset.mem_erase.mpr ⟨fun hzx => hxS (hzx ▸ hz), hSU hz⟩
        have hsdiff : U' \ S = (U \ S).erase x := by
          ext z; simp [U', Finset.mem_sdiff, Finset.mem_erase]; tauto
        have hk' : (U' \ S).card = k := by
          rw [hsdiff]; have := Finset.card_erase_add_one hx; omega
        have hex_sub : P U ⊆ insert x (P U') := hUeq ▸ h_step_ins U' x hxU'
        have hinter : P U ∩ S ⊆ P U' ∩ S := by
          intro z hz
          rcases Finset.mem_insert.mp (hex_sub (Finset.mem_inter.mp hz).1) with rfl | hzU'
          · exact absurd (Finset.mem_inter.mp hz).2 hxS
          · exact Finset.mem_inter.mpr ⟨hzU', (Finset.mem_inter.mp hz).2⟩
        exact hinter.trans (ih S U' hk' hSU')
    refine ⟨fun T => ⟨(h_cd_props T).1, (h_cd_props T).2.1⟩, fun S g hgU hgS => ?_⟩
    exact h_pers_ind (Finset.univ \ S).card S Finset.univ rfl (Finset.subset_univ S)
      (Finset.mem_inter.mpr ⟨hgU, hgS⟩)
  have h_part5 : ∀ (n d s : ℕ) (F : Type) [Field F] [Fintype F] [DecidableEq F],
      2 ≤ n → 1 ≤ s → s < n →
        ∃ mod : RepresentedAdmissionModule n F d,
          ∀ (M : Matroid (Fin n)) (w : Fin n → ℝ) (u : Fin n → (Fin d → F)),
            IsLinearMatroidRep F M u →
              let v := weightedMatroidVal M w
              let P := canonicalDemand v
              (∀ (ω : mod.Seed) (π : Equiv.Perm (Fin n)),
                M.Indep (runDetRepAdmission (mod.det ω) P u π : Set (Fin n))) ∧
              (∀ g ∈ P Finset.univ,
                (1 / (Nat.factorial n : ℝ)) *
                  ∑ π : Equiv.Perm (Fin n),
                    mod.seedMeasure.real {ω | g ∈ runDetRepAdmission (mod.det ω) P u π} =
                  secretaryCutoffConst n s) := by
    intro n d s F _ _ _ hn2 hs1 hsn
    obtain ⟨mod, h_mod⟩ := h_part4 n d s F hn2 hs1 hsn
    refine ⟨mod, ?_⟩
    intro M w u h_rep
    let v := weightedMatroidVal M w
    let P := canonicalDemand v
    obtain ⟨hP_M, h_pers⟩ := h_wm_persist M w
    obtain ⟨h_rej, h_pathwise, h_cond⟩ := h_mod M u P h_rep hP_M
    refine ⟨fun ω π => (h_pathwise ω π n (le_refl n)).2, ?_⟩
    intro g hgU
    have h_after_g : ∀ (ω : mod.Seed) (π : Equiv.Perm (Fin n)) (m : ℕ) (hm : m ≤ n),
        (π.symm g).1 + 1 ≤ m →
        (g ∈ (runDetRepAdmissionSteps (mod.det ω) P u π m hm).2 ↔
          g ∈ (runDetRepAdmissionSteps (mod.det ω) P u π ((π.symm g).1 + 1) (π.symm g).2).2) := by
      intro ω π m
      induction m with
      | zero => intro _ hle; omega
      | succ m ih =>
        intro hm hle
        by_cases heq : m = (π.symm g).1
        · subst heq; rfl
        · have hle' : (π.symm g).1 + 1 ≤ m := by omega
          have hm0 : m ≤ n := Nat.le_of_succ_le hm
          have hne_g : π ⟨m, hm⟩ ≠ g := by
            intro hπm
            have hidx : (⟨m, hm⟩ : Fin n) = π.symm g := by
              apply π.injective
              rw [hπm, Equiv.apply_symm_apply]
            exact heq (congrArg Fin.val hidx)
          let st := runDetRepAdmissionSteps (mod.det ω) P u π m hm0
          let dec := (mod.det ω).step st.1 (π ⟨m, hm⟩) st.2 (fun ⟨T, _⟩ => P T) (fun ⟨x, _⟩ => u x)
          have hstep : (runDetRepAdmissionSteps (mod.det ω) P u π (m + 1) hm).2 =
              if dec then insert (π ⟨m, hm⟩) st.2 else st.2 := rfl
          rw [hstep]
          cases dec
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact ih hm0 hle'
          · simp only [↓reduceIte, Finset.mem_insert, hne_g.symm, false_or]
            exact ih hm0 hle'
    let f_adm : Equiv.Perm (Fin n) → ℝ :=
      fun π => mod.seedMeasure.real {ω | g ∈ runDetRepAdmission (mod.det ω) P u π}
    let F_idx : Fin n → Finset (Equiv.Perm (Fin n)) :=
      fun idx => (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => π idx = g)
    have h_F_card : ∀ idx : Fin n, n * (F_idx idx).card = Nat.factorial n := by
      intro idx
      have hmaps : ∀ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))),
          π idx ∈ (Finset.univ : Finset (Fin n)) := fun _ _ => Finset.mem_univ _
      have hpart := (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
        (g := fun π : Equiv.Perm (Fin n) => π idx) hmaps (fun _ => (1 : ℕ))).symm
      have hpart' : (Finset.univ : Finset (Equiv.Perm (Fin n))).card =
          ∑ y : Fin n, ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => π idx = y)).card := by
        simpa using hpart
      have hbij_y : ∀ y : Fin n,
          ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => π idx = y)).card =
          (F_idx idx).card := by
        intro y
        have hmem_swap : ∀ (a b : Fin n) (π : Equiv.Perm (Fin n)),
            π ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => π idx = a) →
            Equiv.swap a b * π ∈
              (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => π idx = b) := by
          intro a b π hπ
          have hπa : π idx = a := (Finset.mem_filter.mp hπ).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          change Equiv.swap a b (π idx) = b
          rw [hπa, Equiv.swap_apply_left]
        refine Finset.card_bij (fun π _ => Equiv.swap y g * π)
          (fun π hπ => hmem_swap y g π hπ)
          (fun _ _ _ _ heq => mul_left_cancel heq) ?_
        intro π hπ
        refine ⟨Equiv.swap g y * π, hmem_swap g y π hπ, ?_⟩
        dsimp only; ext x; simp [Equiv.swap_comm y g]
      have huniv_card : (Finset.univ : Finset (Equiv.Perm (Fin n))).card = Nat.factorial n := by
        rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
      rw [← huniv_card, hpart', Finset.sum_congr rfl fun y _ => hbij_y y,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have h_F_sum : ∀ idx : Fin n,
        (∑ π ∈ F_idx idx, f_adm π) =
          if s ≤ idx.1 then admitRate s (idx.1 + 1) * ((F_idx idx).card : ℝ) else 0 := by
      intro idx
      let k := idx.1
      have hk : k + 1 ≤ n := idx.2
      have hk0 : k ≤ n := Nat.le_of_succ_le hk
      have hidx_eq : (⟨k, hk⟩ : Fin n) = idx := Fin.ext rfl
      have h_f_on_idx : ∀ π ∈ F_idx idx,
          f_adm π = mod.seedMeasure.real
            {ω | g ∈ (runDetRepAdmissionSteps (mod.det ω) P u π (k + 1) hk).2} := by
        intro π hπ
        have hπg : π idx = g := (Finset.mem_filter.mp hπ).2
        have hsymm : π.symm g = idx := by rw [← hπg, Equiv.symm_apply_apply]
        dsimp only [f_adm, runDetRepAdmission]
        congr 1; ext ω
        simp only [Set.mem_setOf_eq]
        rw [h_after_g ω π n (le_refl n) (by rw [hsymm]; exact hk)]
        congr 2 <;> simp [hsymm, k]
      by_cases hsk : s ≤ k
      · rw [if_pos hsk, Finset.sum_congr rfl fun π hπ => h_f_on_idx π hπ]
        let pset := (Finset.univ : Finset (Fin n)).powersetCard (k + 1)
        have hmaps_S : ∀ π ∈ F_idx idx, arrivalPrefixSet π (k + 1) ∈ pset := by
          intro π _
          exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h_pref_card π (k + 1) hk⟩
        rw [(Finset.sum_fiberwise_of_maps_to hmaps_S
              (fun π => mod.seedMeasure.real
                {ω | g ∈ (runDetRepAdmissionSteps (mod.det ω) P u π (k + 1) hk).2})).symm]
        have h_each_S : ∀ S ∈ pset,
            (∑ π ∈ (F_idx idx).filter (fun π => arrivalPrefixSet π (k + 1) = S),
              mod.seedMeasure.real
                {ω | g ∈ (runDetRepAdmissionSteps (mod.det ω) P u π (k + 1) hk).2}) =
            admitRate s (k + 1) *
              (((F_idx idx).filter (fun π => arrivalPrefixSet π (k + 1) = S)).card : ℝ) := by
          intro S hS
          have hScard : S.card = k + 1 := (Finset.mem_powersetCard.mp hS).2
          have hfilt_eq : (F_idx idx).filter (fun π => arrivalPrefixSet π (k + 1) = S) =
              (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
                (fun π => arrivalPrefixSet π (k + 1) = S ∧ π ⟨k, hk⟩ = g) := by
            ext π; simp [F_idx, hidx_eq, and_comm]
          rw [hfilt_eq]
          by_cases hgS : g ∈ S
          · exact h_cond k hk hsk S g hScard (h_pers S g hgU hgS)
          · have hemp : ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
                (fun π => arrivalPrefixSet π (k + 1) = S ∧ π ⟨k, hk⟩ = g)) = ∅ := by
              ext π
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
                iff_false, not_and]
              intro hpref hπg
              apply hgS
              rw [← hpref, (h_pref_succ π k hk).1, hπg]
              exact Finset.mem_insert_self g _
            rw [hemp]; simp
        rw [Finset.sum_congr rfl fun S hS => h_each_S S hS, ← Finset.mul_sum]
        congr 1
        have hpart_S := (Finset.sum_fiberwise_of_maps_to (s := F_idx idx) (t := pset)
          (g := fun π : Equiv.Perm (Fin n) => arrivalPrefixSet π (k + 1)) hmaps_S
          (fun _ => (1 : ℕ))).symm
        have hpart_S' : (F_idx idx).card =
            ∑ S ∈ pset, ((F_idx idx).filter (fun π => arrivalPrefixSet π (k + 1) = S)).card := by
          simpa using hpart_S
        rw [hpart_S', Nat.cast_sum]
      · rw [if_neg hsk]
        have hks : k < s := Nat.lt_of_not_ge hsk
        refine Finset.sum_eq_zero fun π hπ => ?_
        rw [h_f_on_idx π hπ]
        have hπg : π ⟨k, hk⟩ = g := by rw [hidx_eq]; exact (Finset.mem_filter.mp hπ).2
        have hemp : {ω : mod.Seed | g ∈ (runDetRepAdmissionSteps (mod.det ω) P u π (k + 1) hk).2} = ∅ := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          have hr := h_rej ω π k hk (Or.inl hks)
          have hstep : (runDetRepAdmissionSteps (mod.det ω) P u π (k + 1) hk).2 =
              if (mod.det ω).step (runDetRepAdmissionSteps (mod.det ω) P u π k hk0).1 (π ⟨k, hk⟩)
                  (runDetRepAdmissionSteps (mod.det ω) P u π k hk0).2
                  (fun ⟨T, _⟩ => P T) (fun ⟨x, _⟩ => u x)
              then insert (π ⟨k, hk⟩) (runDetRepAdmissionSteps (mod.det ω) P u π k hk0).2
              else (runDetRepAdmissionSteps (mod.det ω) P u π k hk0).2 := rfl
          rw [hstep, hr, if_neg Bool.false_ne_true]
          intro hg_in
          have hsub := (h_pathwise ω π k hk0).1 hg_in
          rw [h_st_fst (mod.det ω) P u π k hk0] at hsub
          exact (hπg ▸ (h_pref_succ π k hk).2) hsub
        rw [hemp, measureReal_empty]
    have h_part_all : (∑ π : Equiv.Perm (Fin n), f_adm π) = ∑ idx : Fin n, ∑ π ∈ F_idx idx, f_adm π := by
      have hmaps : ∀ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))),
          π.symm g ∈ (Finset.univ : Finset (Fin n)) := fun _ _ => Finset.mem_univ _
      rw [(Finset.sum_fiberwise_of_maps_to hmaps f_adm).symm]
      refine Finset.sum_congr rfl fun idx _ => ?_
      have hfilt : (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => π.symm g = idx) =
          F_idx idx := by
        ext π
        simp only [F_idx, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => by rw [← h, Equiv.apply_symm_apply],
          fun h => by rw [← h, Equiv.symm_apply_apply]⟩
      rw [hfilt]
    change (1 / (Nat.factorial n : ℝ)) * (∑ π : Equiv.Perm (Fin n), f_adm π) = secretaryCutoffConst n s
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hfact_ne : (Nat.factorial n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have h_F_card_real : ∀ idx : Fin n, ((F_idx idx).card : ℝ) = (Nat.factorial n : ℝ) / (n : ℝ) := by
      intro idx
      have hc : (n : ℝ) * ((F_idx idx).card : ℝ) = (Nat.factorial n : ℝ) := by
        exact_mod_cast h_F_card idx
      field_simp [hn_ne]
      linarith
    rw [h_part_all, Finset.sum_congr rfl fun idx _ => h_F_sum idx]
    simp_rw [h_F_card_real]
    rw [← Finset.sum_filter]
    have h_bij_Ico : (∑ idx ∈ (Finset.univ : Finset (Fin n)).filter (fun idx : Fin n => s ≤ idx.1),
          admitRate s (idx.1 + 1) * ((Nat.factorial n : ℝ) / (n : ℝ))) =
        ∑ j ∈ Finset.Ico s n, ((s : ℝ) / (j : ℝ)) * ((Nat.factorial n : ℝ) / (n : ℝ)) := by
      refine Finset.sum_bij (fun idx _ => idx.1)
        (fun idx hidx => Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp hidx).2, idx.2⟩)
        (fun _ _ _ _ heq => Fin.ext heq)
        (fun j hj => ⟨⟨j, (Finset.mem_Ico.mp hj).2⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_Ico.mp hj).1⟩, rfl⟩) ?_
      intro idx _
      simp [admitRate]
    rw [h_bij_Ico, ← Finset.sum_mul]
    have h_pull_s : (∑ j ∈ Finset.Ico s n, (s : ℝ) / (j : ℝ)) =
        (s : ℝ) * ∑ j ∈ Finset.Ico s n, (1 / (j : ℝ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h_pull_s]
    dsimp only [secretaryCutoffConst]
    field_simp [hfact_ne, hn_ne]
  exact ⟨h_part1a, h_part1b, h_part2, h_part3, h_part4, h_part5⟩

end ABHMInternal

/-- **`[ABHM26, Section 4.2]` & `Proposition E.2` — Arrived Subspaces Suffice**:
For `β ≥ 0` and any probability law `μ` supported on linearly independent subsets of `S`,
`β`-boundedness over all subspaces `U ≤ F^d` holds if and only if it holds over subspaces
`U ≤ W(S)` of the arrived span. -/
theorem abhm_arrived_span_iff
    {n d : ℕ} {F : Type} [Field F]
    (u : Fin n → (Fin d → F)) (S : Finset (Fin n)) (β : ℝ) (μ : Finset (Fin n) → ℝ)
    (hβ : 0 ≤ β) (hμ : IsIndepSetLaw u S μ) :
    IsSubspaceBetaBounded u S β μ ↔
      ∀ U : Submodule F (Fin d → F), U ≤ matroidSpan u S →
        (∑ A : Finset (Fin n), μ A * (subspaceLoad u U A : ℝ)) ≤
          β * (Module.finrank F U : ℝ) :=
  ABHMInternal.thm_abhm26_and_linear_module.1 u S β μ hβ hμ

/-- **`[ABHM26, Section 4.2]` — Hidden-Direction Separation on `U_{3, 4}(𝔽₂)`**:
There exists a representation `u : Fin 4 → (Fin 3 → 𝔽₂)` of the uniform matroid `U_{3, 4}` and a
law `μ` on independent sets whose load on every item-spanned flat `W(X)` is `≤ (3/4) dim W(X)`, yet
`μ` fails `β`-boundedness over all subspaces `U ≤ 𝔽₂³` for every `β < 1`. -/
theorem abhm_hidden_directions_F2 :
    ∃ (u : Fin 4 → (Fin 3 → ZMod 2)) (μ : Finset (Fin 4) → ℝ),
      (∀ X : Finset (Fin 4), LinearIndependent (ZMod 2) (fun g : X => u g.1) ↔ X.card ≤ 3) ∧
      IsIndepSetLaw u Finset.univ μ ∧
      (∀ X : Finset (Fin 4),
        (∑ A, μ A * (subspaceLoad u (matroidSpan u X) A : ℝ)) ≤
          (3 / 4 : ℝ) * (Module.finrank (ZMod 2) (matroidSpan u X) : ℝ)) ∧
      ¬ ∃ β : ℝ, β < 1 ∧ IsSubspaceBetaBounded u Finset.univ β μ :=
  ABHMInternal.thm_abhm26_and_linear_module.2.1

/-- **`[ABHM26, Lemma 4.6]` — Averaged Extension Lemma for Arbitrary Independent Proposals `B ⊆ S`**:
Given `β`-bounded laws `μ_g` on `S - g` (`g ∈ S`) over a finite field `F` and **any** linearly
independent proposal subset `B ⊆ S`, there exist transitions `q_g(A)` moving total mass `a ≤ 1 - β`
for each `g ∈ B` to independent sets `A + g` so that the averaged law `μ_avg` is
`(β + a / |S|)`-bounded across all subspaces `U ≤ F^d`. -/
theorem abhm_lem_4_6_averaged_extension
    {n d : ℕ} {F : Type} [Field F] [Fintype F]
    (u : Fin n → (Fin d → F)) (S B : Finset (Fin n)) (β a : ℝ)
    (μ_g : Fin n → Finset (Fin n) → ℝ)
    (hS : 1 ≤ S.card) (hBS : B ⊆ S) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 - β)
    (hB_indep : LinearIndependent F (fun g : B => u g.1))
    (hμ : ∀ g ∈ S, IsIndepSetLaw u (S.erase g) (μ_g g) ∧ IsSubspaceBetaBounded u S β (μ_g g)) :
    ∃ q : Fin n → Finset (Fin n) → ℝ,
      (∀ g ∈ S, ∀ A, 0 ≤ q g A ∧ q g A ≤ μ_g g A) ∧
      (∀ g ∈ S, ∀ A, q g A ≠ 0 →
        g ∈ B ∧ g ∉ A ∧ LinearIndependent F (fun x : (insert g A : Finset (Fin n)) => u x.1)) ∧
      (∀ g ∈ B, (∑ A, q g A) = a) ∧
      let ν : Fin n → Finset (Fin n) → ℝ := fun g C =>
        μ_g g C + (∑ A, if insert g A = C then q g A else 0) - q g C
      let μ_avg : Finset (Fin n) → ℝ := fun C => (1 / (S.card : ℝ)) * ∑ g ∈ S, ν g C
      IsSubspaceBetaBounded u S (β + a / (S.card : ℝ)) μ_avg :=
  ABHMInternal.thm_abhm26_and_linear_module.2.2.1 u S B β a μ_g
    hS hBS hβ0 hβ1 ha0 ha1 hB_indep hμ

/-- **`[ABHM26, Definition 4.1 & Proposition 4.2]` — Prefix Subspace-Load Program Feasibility**:
For every `1 ≤ s ≤ n` and finite field `F`, there exists a family of laws `μ_prog u P S` (`|S| ≥ s`)
that is `(1 - s / |S|)`-bounded for every independent proposal map `P` and depends on `(u, P)` only
through arrived vectors `{u_g : g ∈ S}` and prefix proposals `{P(T) : T ⊆ S}`. -/
theorem abhm_prop_4_2_recursive_lp
    (n d s : ℕ) (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hs1 : 1 ≤ s) (hsn : s ≤ n) :
    ∃ μ_prog :
        (Fin n → (Fin d → F)) → (Finset (Fin n) → Finset (Fin n)) →
        Finset (Fin n) → Finset (Fin n) → ℝ,
      (∀ (u : Fin n → (Fin d → F)) (P : Finset (Fin n) → Finset (Fin n)),
        (∀ T : Finset (Fin n), P T ⊆ T ∧ LinearIndependent F (fun g : P T => u g.1)) →
        ∀ S : Finset (Fin n), s ≤ S.card →
          IsSubspaceBetaBounded u S (loadBeta s S.card) (μ_prog u P S)) ∧
      (∀ (u u' : Fin n → (Fin d → F)) (P P' : Finset (Fin n) → Finset (Fin n))
          (S : Finset (Fin n)),
        (∀ g ∈ S, u g = u' g) → (∀ T ⊆ S, P T = P' T) →
          μ_prog u P S = μ_prog u' P' S) :=
  ABHMInternal.thm_abhm26_and_linear_module.2.2.2.1 n d s F hs1 hsn

/-- **Proposition E.2 (`prop:linear-module`) & `[ABHM26, Algorithm 1 & Lemma 4.7]`**:
For every `2 ≤ n`, `1 ≤ s < n`, and finite field `F`, there exists a universal non-clairvoyant
`RepresentedAdmissionModule n F d` that rejects during the first `s` arrivals or when `g_k ∉ P(S_k)`,
maintains an `M`-independent accepted set at every step, and achieves exact conditional admission
`P[g_k accepted | S_k = S, g_k = g] = a_k = s / (k - 1)` for every `k > s`, `|S| = k`, `g ∈ P(S)`. -/
theorem prop_E_2_linear_module
    (n d s : ℕ) (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hn2 : 2 ≤ n) (hs1 : 1 ≤ s) (hsn : s < n) :
    ∃ mod : RepresentedAdmissionModule n F d,
      ∀ (M : Matroid (Fin n)) (u : Fin n → (Fin d → F))
        (P : Finset (Fin n) → Finset (Fin n)),
        IsLinearMatroidRep F M u →
        (∀ T : Finset (Fin n), P T ⊆ T ∧ M.Indep (P T : Set (Fin n))) →
          (∀ (ω : mod.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k + 1 ≤ n),
            let st := runDetRepAdmissionSteps (mod.det ω) P u π k (Nat.le_of_succ_le hk)
            let x := π ⟨k, hk⟩
            (k < s ∨ x ∉ P (insert x st.1.toFinset)) →
              (mod.det ω).step st.1 x st.2 (fun ⟨T, _⟩ => P T) (fun ⟨g, _⟩ => u g) = false) ∧
          (∀ (ω : mod.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
            let st := runDetRepAdmissionSteps (mod.det ω) P u π k hk
            st.2 ⊆ st.1.toFinset ∧ M.Indep (st.2 : Set (Fin n))) ∧
          (∀ (k : ℕ) (hk : k + 1 ≤ n), s ≤ k →
            ∀ (S : Finset (Fin n)) (g : Fin n),
              S.card = k + 1 → g ∈ P S →
                let ev := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
                  (fun π => arrivalPrefixSet π (k + 1) = S ∧ π ⟨k, hk⟩ = g)
                ∑ π ∈ ev, mod.seedMeasure.real
                  {ω | g ∈ (runDetRepAdmissionSteps (mod.det ω) P u π (k + 1) hk).2} =
                  admitRate s (k + 1) * (ev.card : ℝ)) :=
  ABHMInternal.thm_abhm26_and_linear_module.2.2.2.2.1 n d s F hn2 hs1 hsn

/-- **`[ABHM26, Proposition 4.3 & Theorem 1.2]` — Strong Matroid Secretary for Linear Matroids**:
Specializing `prop_E_2_linear_module` to the greedy canonical demand `P(S) = D_{v_M}(S)` of a
weighted linear matroid `M` over a finite field `F` selects every element `g ∈ D_{v_M}(N)` with
exact probability `c_n(s)` while maintaining an independent accepted set. -/
theorem abhm_thm_1_2_linear_matroid_secretary
    (n d s : ℕ) (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hn2 : 2 ≤ n) (hs1 : 1 ≤ s) (hsn : s < n) :
    ∃ mod : RepresentedAdmissionModule n F d,
      ∀ (M : Matroid (Fin n)) (w : Fin n → ℝ) (u : Fin n → (Fin d → F)),
        IsLinearMatroidRep F M u →
          let v := weightedMatroidVal M w
          let P := canonicalDemand v
          (∀ (ω : mod.Seed) (π : Equiv.Perm (Fin n)),
            M.Indep (runDetRepAdmission (mod.det ω) P u π : Set (Fin n))) ∧
          (∀ g ∈ P Finset.univ,
            (1 / (Nat.factorial n : ℝ)) *
              ∑ π : Equiv.Perm (Fin n),
                mod.seedMeasure.real {ω | g ∈ runDetRepAdmission (mod.det ω) P u π} =
              secretaryCutoffConst n s) :=
  ABHMInternal.thm_abhm26_and_linear_module.2.2.2.2.2 n d s F hn2 hs1 hsn

end

end GrossSubstitutesWelfare
