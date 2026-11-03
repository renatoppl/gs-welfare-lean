import GrossSubstitutesWelfare.Defs
import GrossSubstitutesWelfare.Preliminaries.SafeSupportAndCutoff
import GrossSubstitutesWelfare.Welfare.ConditionalAdmission
import GrossSubstitutesWelfare.LinearMatroids.UniqueRepresentations
import GrossSubstitutesWelfare.LinearMatroids.ABHMSubspaceModule

set_option maxHeartbeats 4000000
set_option linter.all false

/-!
# Section 1.1 Theorem C & Appendix E: `1 / e`-Competitive Welfare for Linear, Binary & Ternary Matroids

This file formalizes Theorem C (`thm:C`), Theorem E.1(a)–(b) (`thm:linear`), the nonnegative
weighted matroid rank corollary (`sec:linear`), and Remark E.4 (`rem:fields`) of *Gross Substitutes
Welfare in Random Order*:
- `thm_E_1_a_represented` (**Theorem E.1(a)**): `c_n(s) OPT` welfare in the represented model for
  weighted matroids over arbitrary finite fields `𝔽_1, ..., 𝔽_m`.
- `thm_E_1_b_oracle` (**Theorem E.1(b)**): `c_n(s) OPT` welfare in the value-oracle model for
  binary/ternary weighted matroids (`𝔽_i ∈ {𝔽₂, 𝔽₃}`).
- `thm_E_1_b_weighted_rank` (**Appendix E Weighted Matroid Rank Corollary**): `c_n(s) OPT` welfare
  for nonnegative weighted matroid rank functions `weightedMatroidRankVal`.
- `thm_C_binary_oracle`, `thm_C_ternary_oracle`, `thm_C_mixed_oracle`, `thm_C_represented`, `thm_C`
  (**Theorem C**, `thm:C`): `1 / e`-competitive online welfare across all `n, m`.
- `rem_E_4_fields` (**Remark E.4**, `rem:fields`): Projective inequivalence over `𝔽₅` on `U_{3, 6}`
  producing zero extension availability on a nonzero 7th-item vector `h = (1, 0, 3)`.
-/

namespace GrossSubstitutesWelfare

open Classical MeasureTheory

noncomputable section

namespace LinearWelfareInternal

/-- **Theorem E.1 (`thm:linear`), Theorem C (`thm:C`), and Remark E.4 (`rem:fields`)**:
1. **Theorem E.1(a)**: Represented model with arbitrary cutoff `s ∈ {1, ..., n - 1}` (`≥ c_n(s) OPT`).
2. **Theorem E.1(b) + Rank Corollary**: Value-oracle model with known `𝔽_i ∈ {𝔽₂, 𝔽₃}` and cutoff
   `s ∈ {1, ..., n - 1}` (`≥ c_n(s) OPT`, both for signed `weightedMatroidVal` and nonnegative
   `weightedMatroidRankVal`).
3. **Theorem C (`thm:C`)**: `1 / e`-competitive online welfare across all `n, m` for:
   - Pure binary weighted matroids in the value-oracle model (no side tags);
   - Pure ternary weighted matroids in the value-oracle model (no side tags);
   - Mixed binary/ternary weighted matroids with known `𝔽_i ∈ {𝔽₂, 𝔽₃}` in the value-oracle model;
   - Represented linear matroids over arbitrary finite fields `𝔽_i` in the represented model.
4. **Remark E.4 (`rem:fields`)**: Over `𝔽₅`, two representations `R, R'` of `U_{3, 6}` and a law `μ`
   where `μ` is `2/3`-bounded in `R'`, yet in `R` the nonzero 7th-item vector `h = (1, 0, 3)` lies
   in `W_R(A)` for every `A` in the support of `μ` (zero extension availability!). -/
def obsPosIndep {n : ℕ} (vi : ItemValuation n) (T X : Finset (Fin n)) : Prop :=
  X ⊆ T ∧
  vi X ≠ ⊥ ∧
  (∀ g ∈ X, ((0 : ℝ) : WithBot ℝ) < vi {g}) ∧
  vi X = ((∑ g ∈ X, (vi {g}).unbotD 0 : ℝ) : WithBot ℝ)

def FBool : Bool → Type
  | true => ZMod 3
  | false => ZMod 2

instance instFieldFBool : ∀ b : Bool, Field (FBool b)
  | true => inferInstanceAs (Field (ZMod 3))
  | false => inferInstanceAs (Field (ZMod 2))

instance instFintypeFBool : ∀ b : Bool, Fintype (FBool b)
  | true => inferInstanceAs (Fintype (ZMod 3))
  | false => inferInstanceAs (Fintype (ZMod 2))

instance instDecidableEqFBool : ∀ b : Bool, DecidableEq (FBool b)
  | true => inferInstanceAs (DecidableEq (ZMod 3))
  | false => inferInstanceAs (DecidableEq (ZMod 2))

def canonicalLocalRep {n : ℕ} (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (vi : ItemValuation n) (T : Finset (Fin n)) : Fin n → (Fin n → F) :=
  if h : ∃ uLoc : Fin n → (Fin n → F),
      ∀ X ⊆ T, LinearIndependent F (fun g : X => uLoc g.1) ↔ obsPosIndep vi T X then
    Classical.choose h
  else
    0
def lrlpEmptyLaw {n : ℕ} : Finset (Fin n) → ℝ :=
  fun A => if A = ∅ then 1 else 0

def lrlpRowAvg {n : ℕ}
    (S : Finset (Fin n))
    (μSub : Fin n → Finset (Fin n) → ℝ)
    (q : Fin n → Finset (Fin n) → ℝ)
    (B : Finset (Fin n)) : ℝ :=
  (1 / (S.card : ℝ)) * ∑ g ∈ S,
    (μSub g B + (if g ∈ B then q g (B.erase g) else 0) - q g B)

def lrlpStepSpec {n d : ℕ} {F : Type*} [Field F]
    (s : ℕ) (u : Fin n → (Fin d → F)) (S B : Finset (Fin n))
    (μSub : Fin n → Finset (Fin n) → ℝ)
    (q : Fin n → Finset (Fin n) → ℝ) : Prop :=
  (∀ g ∈ S, ∀ A, 0 ≤ q g A ∧ q g A ≤ μSub g A) ∧
  (∀ g A, q g A ≠ 0 →
    g ∈ B ∧ A ⊆ S.erase g ∧ LinearIndependent F (fun x : (insert g A : Finset (Fin n)) => u x.1)) ∧
  (∀ g ∈ B, ∑ A : Finset (Fin n), q g A = (s : ℝ) / ((S.card - 1 : ℕ) : ℝ)) ∧
  IsSubspaceBetaBounded u S (1 - (s : ℝ) / (S.card : ℝ)) (lrlpRowAvg S μSub q)

def lrlpProgStep {n d : ℕ} {F : Type*} [Field F]
    (s : ℕ) (S : Finset (Fin n)) (uS : Fin n → (Fin d → F)) (PS : Finset (Fin n))
    (μSub : Fin n → Finset (Fin n) → ℝ) :
    (Finset (Fin n) → ℝ) × (Fin n → Finset (Fin n) → ℝ) :=
  let B := if PS ⊆ S ∧ LinearIndependent F (fun g : PS => uS g.1) then PS else ∅
  if h : ∃ q : Fin n → Finset (Fin n) → ℝ, lrlpStepSpec s uS S B μSub q then
    (lrlpRowAvg S μSub (Classical.choose h), Classical.choose h)
  else
    (lrlpEmptyLaw, fun _ _ => 0)

def lrlpProgAux {n d : ℕ} {F : Type*} [Field F] (s : ℕ) :
    ℕ → (Finset (Fin n) → Fin n → (Fin d → F)) →
    (Finset (Fin n) → Finset (Fin n)) → Finset (Fin n) →
    (Finset (Fin n) → ℝ) × (Fin n → Finset (Fin n) → ℝ)
  | 0, _, _, _ => (lrlpEmptyLaw, fun _ _ => 0)
  | k + 1, ρ, P, S =>
      if k + 1 ≤ s then
        (lrlpEmptyLaw, fun _ _ => 0)
      else
        lrlpProgStep s S (ρ S) (P S) (fun g => (lrlpProgAux s k ρ P (S.erase g)).1)

theorem lem_local_rep_prefix_lp (n d s : ℕ) (hs : 1 ≤ s)
    (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    ∃ (μProg : (Finset (Fin n) → Fin n → (Fin d → F)) →
        (Finset (Fin n) → Finset (Fin n)) → Finset (Fin n) → Finset (Fin n) → ℝ)
      (qProg : (Finset (Fin n) → Fin n → (Fin d → F)) →
        (Finset (Fin n) → Finset (Fin n)) → Finset (Fin n) → Fin n → Finset (Fin n) → ℝ),
      (∀ (ρ ρ' : Finset (Fin n) → Fin n → (Fin d → F))
         (P P' : Finset (Fin n) → Finset (Fin n)) (S : Finset (Fin n)),
        (∀ T ⊆ S, ρ T = ρ' T) → (∀ T ⊆ S, P T = P' T) →
          μProg ρ P S = μProg ρ' P' S ∧ qProg ρ P S = qProg ρ' P' S) ∧
      (∀ ρ P S, S.card ≤ s → μProg ρ P S = fun A => if A = ∅ then 1 else 0) ∧
      (∀ (ρ : Finset (Fin n) → Fin n → (Fin d → F))
         (P : Finset (Fin n) → Finset (Fin n)) (M : Matroid (Fin n)),
        (∀ T, P T ⊆ T ∧ M.Indep (P T : Set (Fin n))) →
        (∀ (T X : Finset (Fin n)), X ⊆ T →
          (LinearIndependent F (fun g : X => ρ T g.1) ↔ M.Indep (X : Set (Fin n)))) →
        (∀ T, ∀ g ∈ T, ∀ (β : ℝ) (μ : Finset (Fin n) → ℝ),
          0 ≤ β →
          IsSubspaceBetaBounded (ρ (T.erase g)) (T.erase g) β μ →
          IsSubspaceBetaBounded (ρ T) (T.erase g) β μ) →
        (∀ S : Finset (Fin n),
          (∀ A, 0 ≤ μProg ρ P S A) ∧
          (∀ A, μProg ρ P S A ≠ 0 → A ⊆ S ∧ M.Indep (A : Set (Fin n))) ∧
          (∑ A : Finset (Fin n), μProg ρ P S A) = 1) ∧
        (∀ S : Finset (Fin n), s < S.card →
          (∀ g ∈ S, ∀ A, 0 ≤ qProg ρ P S g A ∧ qProg ρ P S g A ≤ μProg ρ P (S.erase g) A) ∧
          (∀ g A, qProg ρ P S g A ≠ 0 →
            g ∈ S ∧ g ∈ P S ∧ A ⊆ S.erase g ∧ M.Indep (insert g A : Set (Fin n))) ∧
          (∀ g ∈ P S, ∑ A : Finset (Fin n), qProg ρ P S g A =
            (s : ℝ) / ((S.card - 1 : ℕ) : ℝ)) ∧
          (∀ B : Finset (Fin n),
            μProg ρ P S B = (1 / (S.card : ℝ)) * ∑ g ∈ S,
              (μProg ρ P (S.erase g) B +
                (if g ∈ B then qProg ρ P S g (B.erase g) else 0) -
                qProg ρ P S g B)))) :=
by
  have h_arrived_span :
      ∀ (u : Fin n → (Fin d → F)) (S : Finset (Fin n)) (β : ℝ) (μ : Finset (Fin n) → ℝ),
        0 ≤ β → IsIndepSetLaw u S μ →
          (IsSubspaceBetaBounded u S β μ ↔
            ∀ U : Submodule F (Fin d → F), U ≤ matroidSpan u S →
              (∑ A : Finset (Fin n), μ A * (subspaceLoad u U A : ℝ)) ≤
                β * (Module.finrank F U : ℝ)) := by
    intro u S β μ hβ0 hlaw
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
            congr_arg (fun W' : Submodule F (Fin d → F) => Module.finrank F W') hinf
          rw [hload]
      have hdim : Module.finrank F W ≤ Module.finrank F U := Submodule.finrank_mono inf_le_left
      calc
        (∑ A, μ A * (subspaceLoad u U A : ℝ))
            = ∑ A, μ A * (subspaceLoad u W A : ℝ) := h_sum_eq
        _ ≤ β * (Module.finrank F W : ℝ) := harr W inf_le_right
        _ ≤ β * (Module.finrank F U : ℝ) :=
            mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hdim) hβ0
  have h_ite_erase : ∀ (g : Fin n) (qg : Finset (Fin n) → ℝ) (C : Finset (Fin n)),
      (∀ A, g ∈ A → qg A = 0) →
      (if g ∈ C then qg (C.erase g) else 0) =
        ∑ A : Finset (Fin n), if insert g A = C then qg A else 0 := by
    intro g qg C hq0
    by_cases hgC : g ∈ C
    · rw [if_pos hgC]
      have hcongr : (∑ A : Finset (Fin n), if insert g A = C then qg A else 0) =
          ∑ A : Finset (Fin n), if A = C.erase g then qg A else 0 := by
        refine Finset.sum_congr rfl fun A _ => ?_
        by_cases hgA : g ∈ A
        · simp [hq0 A hgA]
        · have heq : (insert g A = C) ↔ (A = C.erase g) := by
            constructor
            · intro h
              rw [← h, Finset.erase_insert hgA]
            · intro h
              rw [h, Finset.insert_erase hgC]
          simp [heq]
      rw [hcongr, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    · rw [if_neg hgC]
      symm
      refine Finset.sum_eq_zero fun A _ => ?_
      have hne : insert g A ≠ C := fun h => hgC (h ▸ Finset.mem_insert_self g A)
      exact if_neg hne
  have h_ext : ∀ (u : Fin n → (Fin d → F)) (S B : Finset (Fin n)) (β a : ℝ)
      (μ_g : Fin n → Finset (Fin n) → ℝ),
      1 ≤ S.card → B ⊆ S → 0 ≤ β → β ≤ 1 → 0 ≤ a → a ≤ 1 - β →
      LinearIndependent F (fun g : B => u g.1) →
      (∀ g ∈ S, IsIndepSetLaw u (S.erase g) (μ_g g) ∧ IsSubspaceBetaBounded u S β (μ_g g)) →
        ∃ q : Fin n → Finset (Fin n) → ℝ,
          (∀ g ∈ S, ∀ A, 0 ≤ q g A ∧ q g A ≤ μ_g g A) ∧
          (∀ g A, q g A ≠ 0 →
            g ∈ B ∧ A ⊆ S.erase g ∧
              LinearIndependent F (fun x : (insert g A : Finset (Fin n)) => u x.1)) ∧
          (∀ g ∈ B, (∑ A, q g A) = a) ∧
          IsSubspaceBetaBounded u S (β + a / (S.card : ℝ)) (lrlpRowAvg S μ_g q) := by
    have h_jump : ∀ (Y Z : Submodule F (Fin d → F)) (v : Fin d → F),
        v ∉ Z →
          Module.finrank F ↥(Z ⊔ Submodule.span F {v}) = Module.finrank F Z + 1 ∧
          Module.finrank F ↥(Y ⊓ (Z ⊔ Submodule.span F {v})) =
            Module.finrank F ↥(Y ⊓ Z) + (if v ∈ Y ⊔ Z then 1 else 0) := by
      intro Y Z v hvZ
      have h_sup_one : ∀ (W : Submodule F (Fin d → F)), v ∉ W →
          Module.finrank F ↥(W ⊔ Submodule.span F {v}) = Module.finrank F W + 1 := by
        intro W hvW
        have hv0 : v ≠ 0 := fun h0 => hvW (h0 ▸ W.zero_mem)
        have h_span_dim : Module.finrank F ↥(Submodule.span F {v}) = 1 :=
          finrank_span_singleton hv0
        have h_inf_bot : W ⊓ Submodule.span F {v} = ⊥ := by
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
        have h_inf_dim : Module.finrank F ↥(W ⊓ Submodule.span F {v}) = 0 := by
          rw [congr_arg (fun W' : Submodule F (Fin d → F) => Module.finrank F W') h_inf_bot]
          exact finrank_bot F (Fin d → F)
        have h_grass := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span F {v})
        omega
      refine ⟨h_sup_one Z hvZ, ?_⟩
      set Z' : Submodule F (Fin d → F) := Z ⊔ Submodule.span F {v}
      have hZ'_dim : Module.finrank F Z' = Module.finrank F Z + 1 := h_sup_one Z hvZ
      have h_grass1 := Submodule.finrank_sup_add_finrank_inf_eq Y Z
      have h_grass2 := Submodule.finrank_sup_add_finrank_inf_eq Y Z'
      have h_assoc : Y ⊔ Z' = (Y ⊔ Z) ⊔ Submodule.span F {v} :=
        (sup_assoc Y Z (Submodule.span F {v})).symm
      by_cases hvYZ : v ∈ Y ⊔ Z
      · have h_eq : Y ⊔ Z' = Y ⊔ Z := by
          rw [h_assoc, sup_eq_left, Submodule.span_singleton_le_iff_mem]
          exact hvYZ
        have h_sup_dim : Module.finrank F ↥(Y ⊔ Z') = Module.finrank F ↥(Y ⊔ Z) :=
          congr_arg (fun W' : Submodule F (Fin d → F) => Module.finrank F W') h_eq
        simp only [hvYZ, ↓reduceIte]
        omega
      · have h_sup_dim : Module.finrank F ↥(Y ⊔ Z') = Module.finrank F ↥(Y ⊔ Z) + 1 := by
          rw [congr_arg (fun W' : Submodule F (Fin d → F) => Module.finrank F W') h_assoc]
          exact h_sup_one (Y ⊔ Z) hvYZ
        simp only [hvYZ, ↓reduceIte]
        omega
    have h_li_coe : ∀ (v : Fin n → (Fin d → F)) (X : Finset (Fin n)),
        LinearIndependent F (fun g : X => v g.1) ↔ LinearIndepOn F v (X : Set (Fin n)) := by
      intro v X
      let eqv : ↥X ≃ ↥(X : Set (Fin n)) :=
        ⟨fun x => ⟨x.1, Finset.mem_coe.mpr x.2⟩,
         fun x => ⟨x.1, Finset.mem_coe.mp x.2⟩,
         fun _ => rfl, fun _ => rfl⟩
      exact linearIndependent_equiv eqv (f := fun x : ↥(X : Set (Fin n)) => v x.1)
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
        let M_val : ℝ := (u_val + 1) / (-w t)
        have hM_pos : 0 < M_val := div_pos (by linarith) (by linarith)
        let y : Fin k → ℝ := (-M_val) • e t
        have hyK : y ∈ K := by
          intro s _
          rw [Set.mem_Iic]
          dsimp only [y, e, Pi.smul_apply, smul_eq_mul]
          split_ifs <;> linarith
        have hfy := hfK y hyK
        have hfy_eq : f y = u_val + 1 := by
          dsimp only [y]
          rw [map_smul, smul_eq_mul]
          change (-M_val) * w t = u_val + 1
          dsimp only [M_val]
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
    intro u S B β a μ_g hS_card hBS hβ0 hβ1 ha0 ha1 hB_indep hμ
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
      rw [congr_arg (fun W' : Submodule F _ => Module.finrank F W') (by rw [h_span_ins, inf_comm]),
          hj,
          congr_arg (fun W' : Submodule F _ => Module.finrank F W') (inf_comm _ _),
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
            rw [congr_arg (fun W' : Submodule F _ => Module.finrank F W') (inf_of_le_right hle)]
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
            rw [congr_arg (fun W' : Submodule F _ => Module.finrank F W') hbot]
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
          congr_arg (fun W' : Submodule F _ => Module.finrank F W') h_inf_eq
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
      let M_cnt : ℕ := Fintype.card Idx
      let e : Idx ≃ Fin M_cnt := Fintype.equivFin Idx
      let W₀ : Fin M_cnt → Submodule F (Fin d → F) := fun s_idx => U (e.symm s_idx).1
      have hW₀_test : ∀ s_idx : Fin M_cnt, W₀ s_idx ≤ matroidSpan u S :=
        fun s_idx => (hlam (e.symm s_idx).1).1
      have hW₀_sum : ∀ f : Submodule F (Fin d → F) → ℝ,
          (∑ s_idx : Fin M_cnt, f (W₀ s_idx)) = (Z : ℝ) * ∑ t : Fin k, (lam t : ℝ) * f (U t) := by
        intro f
        have h1 : (∑ s_idx : Fin M_cnt, f (W₀ s_idx)) = ∑ p : Idx, f (U p.1) :=
          e.symm.sum_comp (fun p : Idx => f (U p.1))
        rw [h1, Fintype.sum_sigma]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [hc_real t, mul_assoc]
      have h_sq_le : ∀ W : Fin M_cnt → Submodule F (Fin d → F),
          ∑ s_idx : Fin M_cnt, (Module.finrank F (W s_idx)) ^ 2 ≤
            (∑ s_idx : Fin M_cnt, Module.finrank F (W s_idx)) ^ 2 := by
        intro W
        have h1 : ∑ s_idx : Fin M_cnt, (Module.finrank F (W s_idx)) ^ 2 ≤
            ∑ s_idx : Fin M_cnt, Module.finrank F (W s_idx) *
              ∑ s' : Fin M_cnt, Module.finrank F (W s') := by
          refine Finset.sum_le_sum fun s_idx _ => ?_
          rw [sq]
          exact Nat.mul_le_mul_left _
            (Finset.single_le_sum (f := fun s' => Module.finrank F (W s'))
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ s_idx))
        rwa [← Finset.sum_mul, ← sq] at h1
      let pot : (Fin M_cnt → Submodule F (Fin d → F)) → ℕ :=
        fun W => (∑ s_idx : Fin M_cnt, Module.finrank F (W s_idx)) ^ 2 -
          ∑ s_idx : Fin M_cnt, (Module.finrank F (W s_idx)) ^ 2
      have h_uncross : ∀ (K : ℕ) (W : Fin M_cnt → Submodule F (Fin d → F)),
          pot W = K → (∀ s_idx, W s_idx ≤ matroidSpan u S) →
          ∃ W' : Fin M_cnt → Submodule F (Fin d → F),
            (∀ s_idx, W' s_idx ≤ matroidSpan u S) ∧
            (∀ s₁ s₂ : Fin M_cnt, W' s₁ ≤ W' s₂ ∨ W' s₂ ≤ W' s₁) ∧
            (∀ A, ∑ s_idx, subspaceLoad u (W s_idx) A ≤ ∑ s_idx, subspaceLoad u (W' s_idx) A) ∧
            (∑ s_idx, Module.finrank F (W s_idx) = ∑ s_idx, Module.finrank F (W' s_idx)) := by
        intro K
        induction K using Nat.strong_induction_on with
        | h K ih =>
          intro W hpot hW_test
          by_cases hcomp : ∀ s₁ s₂ : Fin M_cnt, W s₁ ≤ W s₂ ∨ W s₂ ≤ W s₁
          · exact ⟨W, hW_test, hcomp, fun _ => le_rfl, rfl⟩
          · push_neg at hcomp
            rcases hcomp with ⟨s₁, s₂, hnot12, hnot21⟩
            have hs12 : s₁ ≠ s₂ := fun heq => hnot12 (heq ▸ le_rfl)
            let W₁ := Function.update (Function.update W s₁ (W s₁ ⊓ W s₂)) s₂ (W s₁ ⊔ W s₂)
            obtain ⟨hinf_test, hsup_test, hdim_pair, hload_pair⟩ :=
              h_supermod (W s₁) (W s₂) (hW_test s₁) (hW_test s₂)
            have hW₁_test : ∀ s_idx, W₁ s_idx ≤ matroidSpan u S := by
              intro s_idx
              by_cases hs2 : s_idx = s₂
              · subst hs2; simp only [W₁, Function.update_self]; exact hsup_test
              · by_cases hs1 : s_idx = s₁
                · subst hs1; simp only [W₁, Function.update_of_ne hs2, Function.update_self]; exact hinf_test
                · simp only [W₁, Function.update_of_ne hs2, Function.update_of_ne hs1]; exact hW_test s_idx
            have h_sum_two : ∀ g_fn : Submodule F (Fin d → F) → ℕ,
                (∑ s_idx : Fin M_cnt, g_fn (W s_idx)) =
                  g_fn (W s₁) + (g_fn (W s₂) + ∑ s_idx ∈ (Finset.univ.erase s₁).erase s₂, g_fn (W s_idx)) ∧
                (∑ s_idx : Fin M_cnt, g_fn (W₁ s_idx)) =
                  g_fn (W s₁ ⊓ W s₂) + (g_fn (W s₁ ⊔ W s₂) + ∑ s_idx ∈ (Finset.univ.erase s₁).erase s₂, g_fn (W s_idx)) := by
              intro g_fn
              have hs2_mem : s₂ ∈ (Finset.univ : Finset (Fin M_cnt)).erase s₁ :=
                Finset.mem_erase.mpr ⟨hs12.symm, Finset.mem_univ s₂⟩
              constructor
              · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s₁),
                    ← Finset.add_sum_erase _ _ hs2_mem]
              · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s₁),
                    ← Finset.add_sum_erase _ _ hs2_mem]
                have hW1_s1 : W₁ s₁ = W s₁ ⊓ W s₂ := by simp [W₁, Function.update_of_ne hs12]
                have hW1_s2 : W₁ s₂ = W s₁ ⊔ W s₂ := by simp [W₁]
                have h_rest : ∑ s_idx ∈ (Finset.univ.erase s₁).erase s₂, g_fn (W₁ s_idx) =
                    ∑ s_idx ∈ (Finset.univ.erase s₁).erase s₂, g_fn (W s_idx) := by
                  refine Finset.sum_congr rfl fun s_idx hs_mem => ?_
                  have hne2 : s_idx ≠ s₂ := (Finset.mem_erase.mp hs_mem).1
                  have hne1 : s_idx ≠ s₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hs_mem).2).1
                  simp [W₁, Function.update_of_ne hne2, Function.update_of_ne hne1]
                rw [hW1_s1, hW1_s2, h_rest]
            have hdim_sum : ∑ s_idx, Module.finrank F (W₁ s_idx) = ∑ s_idx, Module.finrank F (W s_idx) := by
              obtain ⟨hW_eq, hW1_eq⟩ := h_sum_two (fun X => Module.finrank F X)
              omega
            have hload_sum : ∀ A, ∑ s_idx, subspaceLoad u (W s_idx) A ≤ ∑ s_idx, subspaceLoad u (W₁ s_idx) A := by
              intro A
              obtain ⟨hW_eq, hW1_eq⟩ := h_sum_two (fun X => subspaceLoad u X A)
              have hlp := hload_pair A
              omega
            have hdrop1 : Module.finrank F ↥(W s₁ ⊓ W s₂) < Module.finrank F (W s₁) :=
              h_strict_drop (W s₁) (W s₂) hnot12
            have hdrop2 : Module.finrank F ↥(W s₁ ⊓ W s₂) < Module.finrank F (W s₂) := by
              have hd := h_strict_drop (W s₂) (W s₁) hnot21
              have heq : (W s₂ ⊓ W s₁ : Submodule F (Fin d → F)) = W s₁ ⊓ W s₂ := inf_comm _ _
              rwa [congr_arg (fun W' : Submodule F _ => Module.finrank F W') heq] at hd
            have hsq_arith : ∀ a₀ b₀ c₀ m₀ : ℕ, a₀ + b₀ = c₀ + m₀ → c₀ < a₀ → c₀ < b₀ →
                a₀ ^ 2 + b₀ ^ 2 + 2 ≤ c₀ ^ 2 + m₀ ^ 2 := by
              intro a₀ b₀ c₀ m₀ h1 h2 h3
              obtain ⟨d1, rfl⟩ : ∃ d1, a₀ = c₀ + (d1 + 1) := ⟨a₀ - c₀ - 1, by omega⟩
              obtain ⟨d2, rfl⟩ : ∃ d2, b₀ = c₀ + (d2 + 1) := ⟨b₀ - c₀ - 1, by omega⟩
              obtain rfl : m₀ = c₀ + d1 + d2 + 2 := by omega
              have hid : (c₀ + (d1 + 1)) ^ 2 + (c₀ + (d2 + 1)) ^ 2 + 2 * (d1 * d2 + d1 + d2 + 1) =
                  c₀ ^ 2 + (c₀ + d1 + d2 + 2) ^ 2 := by ring
              omega
            have hsq_jump : (Module.finrank F (W s₁)) ^ 2 + (Module.finrank F (W s₂)) ^ 2 + 2 ≤
                (Module.finrank F ↥(W s₁ ⊓ W s₂)) ^ 2 + (Module.finrank F ↥(W s₁ ⊔ W s₂)) ^ 2 :=
              hsq_arith _ _ _ _ hdim_pair hdrop1 hdrop2
            have hsq_sum : ∑ s_idx, (Module.finrank F (W s_idx)) ^ 2 + 2 ≤
                ∑ s_idx, (Module.finrank F (W₁ s_idx)) ^ 2 := by
              obtain ⟨hW_eq, hW1_eq⟩ := h_sum_two (fun X => (Module.finrank F X) ^ 2)
              omega
            have hW1_sq_le := h_sq_le W₁
            have hsq_tot_eq : (∑ s_idx, Module.finrank F (W₁ s_idx)) ^ 2 =
                (∑ s_idx, Module.finrank F (W s_idx)) ^ 2 := by
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
      let σ : Equiv.Perm (Fin M_cnt) := Tuple.sort (fun s_idx => Module.finrank F (W' s_idx))
      let C : Fin M_cnt → Submodule F (Fin d → F) := fun r => W' (σ r)
      let gam : Fin M_cnt → ℝ := fun _ => (1 : ℝ) / (Z : ℝ)
      refine ⟨M_cnt, C, gam, ?_, ?_, ?_, ?_⟩
      · intro r
        exact ⟨hW'_test (σ r), by dsimp only [gam]; positivity⟩
      · intro r₁ r₂ hr12
        have hmono_dim : Module.finrank F (C r₁) ≤ Module.finrank F (C r₂) :=
          Tuple.monotone_sort (fun s_idx => Module.finrank F (W' s_idx)) hr12
        rcases hW'_comp (σ r₁) (σ r₂) with h12 | h21
        · exact h12
        · by_contra hnot
          have hdrop := h_strict_drop (C r₁) (C r₂) hnot
          have hinf_eq : C r₁ ⊓ C r₂ = C r₂ := inf_of_le_right h21
          rw [congr_arg (fun N : Submodule F _ => Module.finrank F N) hinf_eq] at hdrop
          omega
      · intro A
        have h_rhs : (∑ r : Fin M_cnt, gam r * (subspaceLoad u (C r) A : ℝ)) =
            ((1 : ℝ) / (Z : ℝ)) * ∑ s_idx : Fin M_cnt, (subspaceLoad u (W' s_idx) A : ℝ) := by
          dsimp only [gam, C]
          rw [← Finset.mul_sum]
          congr 1
          exact Equiv.sum_comp σ (fun s_idx => (subspaceLoad u (W' s_idx) A : ℝ))
        have h_le_real : (∑ s_idx : Fin M_cnt, (subspaceLoad u (W₀ s_idx) A : ℝ)) ≤
            ∑ s_idx : Fin M_cnt, (subspaceLoad u (W' s_idx) A : ℝ) := by exact_mod_cast hW'_load A
        have h_lhs : (∑ s_idx : Fin M_cnt, (subspaceLoad u (W₀ s_idx) A : ℝ)) =
            (Z : ℝ) * ∑ t : Fin k, (lam t : ℝ) * (subspaceLoad u (U t) A : ℝ) :=
          hW₀_sum (fun X => (subspaceLoad u X A : ℝ))
        rw [h_rhs]
        calc
          (∑ t : Fin k, (lam t : ℝ) * (subspaceLoad u (U t) A : ℝ))
              = ((1 : ℝ) / (Z : ℝ)) * ((Z : ℝ) * ∑ t : Fin k, (lam t : ℝ) * (subspaceLoad u (U t) A : ℝ)) := by
                  field_simp
          _ = ((1 : ℝ) / (Z : ℝ)) * ∑ s_idx : Fin M_cnt, (subspaceLoad u (W₀ s_idx) A : ℝ) := by rw [h_lhs]
          _ ≤ ((1 : ℝ) / (Z : ℝ)) * ∑ s_idx : Fin M_cnt, (subspaceLoad u (W' s_idx) A : ℝ) :=
              mul_le_mul_of_nonneg_left h_le_real (by positivity)
      · have h_rhs : (∑ r : Fin M_cnt, gam r * (Module.finrank F (C r) : ℝ)) =
            ((1 : ℝ) / (Z : ℝ)) * ∑ s_idx : Fin M_cnt, (Module.finrank F (W' s_idx) : ℝ) := by
          dsimp only [gam, C]
          rw [← Finset.mul_sum]
          congr 1
          exact Equiv.sum_comp σ (fun s_idx => (Module.finrank F (W' s_idx) : ℝ))
        have h_eq_real : (∑ s_idx : Fin M_cnt, (Module.finrank F (W₀ s_idx) : ℝ)) =
            ∑ s_idx : Fin M_cnt, (Module.finrank F (W' s_idx) : ℝ) := by exact_mod_cast hW'_dim
        have h_lhs : (∑ s_idx : Fin M_cnt, (Module.finrank F (W₀ s_idx) : ℝ)) =
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
              intro hs_zero; apply hν_ne; dsimp only [ν_of]; linarith
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
          intro hs_zero; apply havg_ne; dsimp only [μ_avg_of]; rw [hs_zero, mul_zero]
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
    have hq_supp : ∀ g A, q g A ≠ 0 →
        g ∈ B ∧ A ⊆ S.erase g ∧
          LinearIndependent F (fun x : (insert g A : Finset (Fin n)) => u x.1) := by
      intro g A hq_ne
      have hup_ne : upper g A ≠ 0 :=
        fun h0 => hq_ne (le_antisymm ((hq_up g A).trans h0.le) (hq_nn g A))
      have hcond : g ∈ B ∧ IsExtFeas g A := by
        by_contra hnc; apply hup_ne; simp [upper, hnc]
      rcases hcond with ⟨hgB, hgA, hinsS, hli_ins⟩
      have hA_er : A ⊆ S.erase g := by
        intro x hxA
        have hxS : x ∈ S := hinsS (Finset.mem_insert_of_mem hxA)
        have hxne : x ≠ g := fun h => hgA (h ▸ hxA)
        exact Finset.mem_erase.mpr ⟨hxne, hxS⟩
      exact ⟨hgB, hA_er, hli_ins⟩
    have h_avg_eq : μ_avg_of q = lrlpRowAvg S μ_g q := by
      funext C'
      dsimp only [μ_avg_of, ν_of, lrlpRowAvg]
      congr 1
      refine Finset.sum_congr rfl fun g _ => ?_
      have hq0 : ∀ A, g ∈ A → q g A = 0 := by
        intro A hgA
        by_contra hne
        have hA_er := (hq_supp g A hne).2.1
        exact (Finset.mem_erase.mp (hA_er hgA)).1 rfl
      rw [h_ite_erase g (q g) C' hq0]
    refine ⟨q, ?_, hq_supp, hq_sum, ?_⟩
    · intro g hgS A
      refine ⟨hq_nn g A, (hq_up g A).trans ?_⟩
      dsimp only [upper]
      split_ifs
      · exact le_rfl
      · exact (hμ g hgS).2.1.1 A
    · rw [← h_avg_eq]
      have hlaw_avg : IsIndepSetLaw u S (μ_avg_of q) := h_avg_feas q ⟨hq_nn, hq_up, hq_sum⟩
      have hβ_avg_nn : 0 ≤ β + a / (S.card : ℝ) :=
        add_nonneg hβ0 (div_nonneg ha0 (le_of_lt hS_pos))
      refine (h_arrived_span u S (β + a / (S.card : ℝ)) (μ_avg_of q) hβ_avg_nn hlaw_avg).mpr ?_
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
  let μProg : (Finset (Fin n) → Fin n → (Fin d → F)) →
      (Finset (Fin n) → Finset (Fin n)) → Finset (Fin n) → Finset (Fin n) → ℝ :=
    fun ρ P S => (lrlpProgAux s S.card ρ P S).1
  let qProg : (Finset (Fin n) → Fin n → (Fin d → F)) →
      (Finset (Fin n) → Finset (Fin n)) → Finset (Fin n) → Fin n → Finset (Fin n) → ℝ :=
    fun ρ P S => (lrlpProgAux s S.card ρ P S).2
  have h_loc_aux : ∀ (k : ℕ) (ρ ρ' : Finset (Fin n) → Fin n → (Fin d → F))
      (P P' : Finset (Fin n) → Finset (Fin n)) (S : Finset (Fin n)),
      (∀ T ⊆ S, ρ T = ρ' T) → (∀ T ⊆ S, P T = P' T) →
        lrlpProgAux s k ρ P S = lrlpProgAux s k ρ' P' S := by
    intro k
    induction k with
    | zero =>
      intro _ _ _ _ _ _ _
      rfl
    | succ k₀ ih =>
      intro ρ ρ' P P' S hρ hP
      unfold lrlpProgAux
      by_cases hle : k₀ + 1 ≤ s
      · rw [if_pos hle, if_pos hle]
      · rw [if_neg hle, if_neg hle]
        have hρS : ρ S = ρ' S := hρ S Finset.Subset.rfl
        have hPS : P S = P' S := hP S Finset.Subset.rfl
        have hsub : (fun g => (lrlpProgAux s k₀ ρ P (S.erase g)).1) =
            (fun g => (lrlpProgAux s k₀ ρ' P' (S.erase g)).1) := by
          funext g
          have her : S.erase g ⊆ S := Finset.erase_subset g S
          exact congr_arg Prod.fst (ih ρ ρ' P P' (S.erase g)
            (fun T hT => hρ T (hT.trans her))
            (fun T hT => hP T (hT.trans her)))
        rw [hρS, hPS, hsub]
  have h_base : ∀ (ρ : Finset (Fin n) → Fin n → (Fin d → F))
      (P : Finset (Fin n) → Finset (Fin n)) (S : Finset (Fin n)),
      S.card ≤ s → μProg ρ P S = lrlpEmptyLaw := by
    intro ρ P S hle
    dsimp only [μProg]
    generalize hk : S.card = k
    rw [hk] at hle
    cases k with
    | zero => rfl
    | succ k₀ => simp [lrlpProgAux, hle]
  have h_empty_bdd : ∀ (u : Fin n → (Fin d → F)) (S : Finset (Fin n)),
      IsSubspaceBetaBounded u S 0 lrlpEmptyLaw := by
    intro u S
    have hlaw : IsIndepSetLaw u S lrlpEmptyLaw := by
      refine ⟨?_, ?_, ?_⟩
      · intro A; dsimp only [lrlpEmptyLaw]; split_ifs <;> norm_num
      · intro A hne
        by_cases hA : A = ∅
        · subst hA
          refine ⟨Finset.empty_subset S, ?_⟩
          rw [Fintype.linearIndependent_iff]
          intro c _ ⟨x, hx⟩
          exact absurd hx (Finset.notMem_empty x)
        · exfalso; apply hne; simp [lrlpEmptyLaw, hA]
      · simp [lrlpEmptyLaw]
    refine ⟨hlaw, fun U => ?_⟩
    rw [zero_mul]
    have hload0 : subspaceLoad u U ∅ = 0 := by
      have hspan0 : matroidSpan u ∅ = ⊥ := by simp [matroidSpan]
      unfold subspaceLoad
      rw [congr_arg (fun W : Submodule F (Fin d → F) => Module.finrank F W)
        (by rw [hspan0, bot_inf_eq])]
      exact finrank_bot F (Fin d → F)
    have hsum0 : (∑ A : Finset (Fin n), lrlpEmptyLaw A * (subspaceLoad u U A : ℝ)) = 0 := by
      refine Finset.sum_eq_zero fun A _ => ?_
      by_cases hA : A = ∅
      · subst hA; simp [hload0]
      · simp [lrlpEmptyLaw, hA]
    rw [hsum0]
  have h_beta_sub : ∀ (v₀ : Fin n → (Fin d → F)) (T S : Finset (Fin n))
      (β : ℝ) (μ : Finset (Fin n) → ℝ),
      T ⊆ S → IsSubspaceBetaBounded v₀ T β μ → IsSubspaceBetaBounded v₀ S β μ := by
    intro v₀ T S β μ hTS ⟨⟨h1, h2, h3⟩, hbdd⟩
    exact ⟨⟨h1, fun A hne => ⟨(h2 A hne).1.trans hTS, (h2 A hne).2⟩, h3⟩, hbdd⟩
  refine ⟨μProg, qProg, ?_, h_base, ?_⟩
  · intro ρ ρ' P P' S hρ hP
    have h := h_loc_aux S.card ρ ρ' P P' S hρ hP
    exact ⟨congr_arg Prod.fst h, congr_arg Prod.snd h⟩
  · intro ρ P M hP hRep hTrans
    have h_ind : ∀ (m : ℕ) (S : Finset (Fin n)),
        S.card = s + m →
          IsSubspaceBetaBounded (ρ S) S (1 - (s : ℝ) / (S.card : ℝ)) (μProg ρ P S) ∧
          (0 < m →
            (∀ g ∈ S, ∀ A, 0 ≤ qProg ρ P S g A ∧ qProg ρ P S g A ≤ μProg ρ P (S.erase g) A) ∧
            (∀ g A, qProg ρ P S g A ≠ 0 →
              g ∈ S ∧ g ∈ P S ∧ A ⊆ S.erase g ∧ M.Indep (insert g A : Set (Fin n))) ∧
            (∀ g ∈ P S, ∑ A : Finset (Fin n), qProg ρ P S g A =
              (s : ℝ) / ((S.card - 1 : ℕ) : ℝ)) ∧
            (∀ B : Finset (Fin n),
              μProg ρ P S B = (1 / (S.card : ℝ)) * ∑ g ∈ S,
                (μProg ρ P (S.erase g) B +
                  (if g ∈ B then qProg ρ P S g (B.erase g) else 0) -
                  qProg ρ P S g B))) := by
      intro m
      induction m with
      | zero =>
        intro S hScard
        have hScard_s : S.card = s := by omega
        refine ⟨?_, fun hm => absurd hm (lt_irrefl 0)⟩
        rw [h_base ρ P S (by omega), hScard_s]
        have hs_ne : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        rw [div_self hs_ne, sub_self]
        exact h_empty_bdd (ρ S) S
      | succ m₀ ih =>
        intro S hScard
        let k := s + m₀
        have hk_ge_s : s ≤ k := Nat.le_add_right s m₀
        have hScard_k : S.card = k + 1 := by omega
        have hnle : ¬ (k + 1 ≤ s) := by omega
        let μSub : Fin n → Finset (Fin n) → ℝ :=
          fun g => (lrlpProgAux s k ρ P (S.erase g)).1
        have hμSub_eq : ∀ g ∈ S, μSub g = μProg ρ P (S.erase g) := by
          intro g hgS
          have hcard_er : (S.erase g).card = k := by
            rw [Finset.card_erase_of_mem hgS, hScard_k]; omega
          dsimp only [μSub, μProg]
          rw [hcard_er]
        have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
        have hk_ne : (k : ℝ) ≠ 0 := hk_pos.ne'
        have hk1_ne : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        let β : ℝ := 1 - (s : ℝ) / (k : ℝ)
        have hβ0 : 0 ≤ β := by
          dsimp only [β]
          rw [sub_nonneg, div_le_one hk_pos]
          exact_mod_cast hk_ge_s
        have hβ1 : β ≤ 1 := by
          dsimp only [β]
          linarith [div_nonneg (Nat.cast_nonneg s) (le_of_lt hk_pos)]
        have hμSub_laws : ∀ g ∈ S,
            IsIndepSetLaw (ρ S) (S.erase g) (μSub g) ∧
            IsSubspaceBetaBounded (ρ S) S β (μSub g) := by
          intro g hgS
          have hcard_er : (S.erase g).card = s + m₀ := by
            rw [Finset.card_erase_of_mem hgS, hScard_k]; omega
          have hbdd_er := (ih (S.erase g) hcard_er).1
          rw [hcard_er] at hbdd_er
          change IsSubspaceBetaBounded (ρ (S.erase g)) (S.erase g) β
            (μProg ρ P (S.erase g)) at hbdd_er
          rw [← hμSub_eq g hgS] at hbdd_er
          have hbdd_tr : IsSubspaceBetaBounded (ρ S) (S.erase g) β (μSub g) :=
            hTrans S g hgS β (μSub g) hβ0 hbdd_er
          exact ⟨hbdd_tr.1, h_beta_sub (ρ S) (S.erase g) S β (μSub g)
            (Finset.erase_subset g S) hbdd_tr⟩
        have hPS_sub : P S ⊆ S := (hP S).1
        have hPS_li : LinearIndependent F (fun g : P S => ρ S g.1) :=
          (hRep S (P S) hPS_sub).mpr (hP S).2
        have hB_cond : P S ⊆ S ∧ LinearIndependent F (fun g : P S => ρ S g.1) :=
          ⟨hPS_sub, hPS_li⟩
        let a : ℝ := (s : ℝ) / ((S.card - 1 : ℕ) : ℝ)
        have ha_eq : a = (s : ℝ) / (k : ℝ) := by
          dsimp only [a]; rw [hScard_k, Nat.add_sub_cancel]
        have ha0 : 0 ≤ a := by rw [ha_eq]; positivity
        have ha_le : a ≤ 1 - β := by rw [ha_eq]; dsimp only [β]; linarith
        have hβ_next : β + a / (S.card : ℝ) = 1 - (s : ℝ) / (S.card : ℝ) := by
          rw [ha_eq, hScard_k]
          dsimp only [β]
          push_cast
          field_simp [hk_ne, hk1_ne]
          ring
        have hex : ∃ q : Fin n → Finset (Fin n) → ℝ,
            lrlpStepSpec s (ρ S) S
              (if P S ⊆ S ∧ LinearIndependent F (fun g : P S => ρ S g.1) then P S else ∅)
              μSub q := by
          rw [if_pos hB_cond]
          obtain ⟨q, hq1, hq2, hq3, hq4⟩ :=
            h_ext (ρ S) S (P S) β a μSub (by omega) hPS_sub hβ0 hβ1 ha0 ha_le hPS_li hμSub_laws
          rw [hβ_next] at hq4
          exact ⟨q, hq1, hq2, hq3, hq4⟩
        let q_ch := Classical.choose hex
        have hprog_unfold : lrlpProgAux s S.card ρ P S = (lrlpRowAvg S μSub q_ch, q_ch) := by
          rw [hScard_k]
          unfold lrlpProgAux
          rw [if_neg hnle]
          unfold lrlpProgStep
          dsimp only
          rw [dif_pos hex]
        have hμ_eq : μProg ρ P S = lrlpRowAvg S μSub q_ch := by
          dsimp only [μProg]; rw [hprog_unfold]
        have hq_eq : qProg ρ P S = q_ch := by
          dsimp only [qProg]; rw [hprog_unfold]
        have hspec : lrlpStepSpec s (ρ S) S
            (if P S ⊆ S ∧ LinearIndependent F (fun g : P S => ρ S g.1) then P S else ∅)
            μSub q_ch :=
          Classical.choose_spec hex
        rw [if_pos hB_cond] at hspec
        obtain ⟨hsp1, hsp2, hsp3, hsp4⟩ := hspec
        refine ⟨by rw [hμ_eq]; exact hsp4, fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
        · intro g hgS A
          rw [hq_eq, ← hμSub_eq g hgS]
          exact hsp1 g hgS A
        · intro g A hq_ne
          rw [hq_eq] at hq_ne
          obtain ⟨hgPS, hA_er, hli_ins⟩ := hsp2 g A hq_ne
          have hgS : g ∈ S := hPS_sub hgPS
          have hAS : A ⊆ S := hA_er.trans (Finset.erase_subset g S)
          have hinsS : insert g A ⊆ S := Finset.insert_subset hgS hAS
          have hind_coe : M.Indep ((insert g A : Finset (Fin n)) : Set (Fin n)) :=
            (hRep S (insert g A) hinsS).mp hli_ins
          rw [Finset.coe_insert] at hind_coe
          exact ⟨hgS, hgPS, hA_er, hind_coe⟩
        · intro g hgPS
          rw [hq_eq]
          exact hsp3 g hgPS
        · intro B
          rw [hμ_eq, hq_eq]
          dsimp only [lrlpRowAvg]
          congr 1
          refine Finset.sum_congr rfl fun g hgS => ?_
          rw [hμSub_eq g hgS]
    refine ⟨?_, ?_⟩
    · intro S
      have hlaw : IsIndepSetLaw (ρ S) S (μProg ρ P S) := by
        by_cases hle : S.card ≤ s
        · rw [h_base ρ P S hle]
          exact (h_empty_bdd (ρ S) S).1
        · exact (h_ind (S.card - s) S (by omega)).1.1
      obtain ⟨h1, h2, h3⟩ := hlaw
      exact ⟨h1, fun A hne => ⟨(h2 A hne).1, (hRep S A (h2 A hne).1).mp (h2 A hne).2⟩, h3⟩
    · intro S hS
      exact (h_ind (S.card - s) S (by omega)).2 (by omega)

theorem lem_binary_ternary_rep_and_transfer : (∀ (n d : ℕ) (F : Type) [Field F] (M : Matroid (Fin n))
        (u : Fin n → (Fin d → F)) (T : Finset (Fin n)),
      IsLinearMatroidRep F M u →
        ∃ uLoc : Fin n → (Fin n → F),
          ∀ X ⊆ T, LinearIndependent F (fun g : X => uLoc g.1) ↔ M.Indep (X : Set (Fin n))) ∧
    (∀ (n d d' : ℕ) (T : Finset (Fin n))
        (u : Fin n → (Fin d → ZMod 2)) (u' : Fin n → (Fin d' → ZMod 2))
        (β : ℝ) (μ : Finset (Fin n) → ℝ),
      0 ≤ β →
      (∀ X ⊆ T,
        LinearIndependent (ZMod 2) (fun g : X => u g.1) ↔
        LinearIndependent (ZMod 2) (fun g : X => u' g.1)) →
      IsSubspaceBetaBounded u T β μ →
      IsSubspaceBetaBounded u' T β μ) ∧
    (∀ (n d d' : ℕ) (T : Finset (Fin n))
        (u : Fin n → (Fin d → ZMod 3)) (u' : Fin n → (Fin d' → ZMod 3))
        (β : ℝ) (μ : Finset (Fin n) → ℝ),
      0 ≤ β →
      (∀ X ⊆ T,
        LinearIndependent (ZMod 3) (fun g : X => u g.1) ↔
        LinearIndependent (ZMod 3) (fun g : X => u' g.1)) →
      IsSubspaceBetaBounded u T β μ →
      IsSubspaceBetaBounded u' T β μ) :=
by
  have h_dim_compress :
      ∀ (n d : ℕ) (F : Type) [Field F] (M : Matroid (Fin n))
        (u : Fin n → (Fin d → F)) (T : Finset (Fin n)),
      IsLinearMatroidRep F M u →
        ∃ uLoc : Fin n → (Fin n → F),
          ∀ X ⊆ T, LinearIndependent F (fun g : X => uLoc g.1) ↔ M.Indep (X : Set (Fin n)) := by
    intro n d F _ M u T hrep
    let V : Submodule F (Fin d → F) := Submodule.span F (u '' (T : Set (Fin n)))
    let r := Module.finrank F V
    have hr_le : r ≤ n := by
      have himg : (u '' (T : Set (Fin n))) = ((T.image u : Finset (Fin d → F)) : Set (Fin d → F)) := by
        simp [Finset.coe_image]
      have h1 : Module.finrank F V ≤ (T.image u).card := by
        dsimp only [V]
        rw [himg]
        exact finrank_span_finset_le_card (T.image u)
      have h2 : (T.image u).card ≤ T.card := Finset.card_image_le
      have h3 : T.card ≤ n := by simpa using T.card_le_univ
      exact h1.trans (h2.trans h3)
    let bV : Module.Basis (Fin r) F V := Module.finBasis F V
    let ι : (Fin r → F) →ₗ[F] (Fin n → F) :=
      { toFun := fun c j => if hj : j.1 < r then c ⟨j.1, hj⟩ else 0
        map_add' := fun c1 c2 => by ext j; by_cases hj : j.1 < r <;> simp [hj]
        map_smul' := fun a c => by ext j; by_cases hj : j.1 < r <;> simp [hj] }
    have hι_inj : Function.Injective ι := by
      intro c1 c2 hc
      ext idx
      have hj := congrFun hc ⟨idx.1, lt_of_lt_of_le idx.2 hr_le⟩
      simpa [ι, idx.2] using hj
    let ψ : V →ₗ[F] (Fin n → F) := ι.comp bV.equivFun.toLinearMap
    have hψ_ker : ψ.ker = ⊥ :=
      LinearMap.ker_eq_bot.mpr (hι_inj.comp bV.equivFun.injective)
    let uLoc : Fin n → (Fin n → F) := fun g =>
      if hg : g ∈ T then ψ ⟨u g, Submodule.subset_span ⟨g, hg, rfl⟩⟩ else 0
    refine ⟨uLoc, fun X hXT => ?_⟩
    rw [hrep X]
    let vV : X → V := fun g => ⟨u g.1, Submodule.subset_span ⟨g.1, hXT g.2, rfl⟩⟩
    have huLoc_eq : (fun g : X => uLoc g.1) = ψ ∘ vV := by
      funext g
      simp [uLoc, hXT g.2, vV]
    have hvV_eq : (fun g : X => u g.1) = V.subtype ∘ vV := rfl
    rw [huLoc_eq, hvV_eq]
    have hker_sub : V.subtype.ker = ⊥ := Submodule.ker_subtype V
    exact ⟨fun hli => (LinearIndependent.of_comp ψ hli).map' V.subtype hker_sub,
           fun hli => (LinearIndependent.of_comp V.subtype hli).map' ψ hψ_ker⟩
  have h_proj_transfer :
      ∀ (F : Type) [Field F] (n d d' : ℕ) (T : Finset (Fin n))
        (u : Fin n → (Fin d → F)) (u' : Fin n → (Fin d' → F))
        (β : ℝ) (μ : Finset (Fin n) → ℝ),
      0 ≤ β →
      (∀ X ⊆ T, LinearIndependent F (fun g : X => u g.1) ↔ LinearIndependent F (fun g : X => u' g.1)) →
      (∃ φ : matroidSpan u T ≃ₗ[F] matroidSpan u' T,
        ∀ (g : Fin n) (hg : g ∈ T), ∃ c : F, c ≠ 0 ∧
          (φ ⟨u g, Submodule.subset_span ⟨g, hg, rfl⟩⟩ : Fin d' → F) = c • u' g) →
      IsSubspaceBetaBounded u T β μ →
      IsSubspaceBetaBounded u' T β μ := by
    clear h_dim_compress
    intro F _ n d d' T u u' β μ hβ0 hindep ⟨φ, hφ⟩ ⟨⟨hμ_nn, hμ_supp, hμ_sum⟩, hμ_load⟩
    let V := matroidSpan u T
    let V' := matroidSpan u' T
    have h_span : ∀ X ⊆ T, ∀ v : V,
        (v : Fin d → F) ∈ matroidSpan u X ↔ (φ v : Fin d' → F) ∈ matroidSpan u' X := by
      intro X hXT v
      let SX : Set V := Set.range (fun g : X => (⟨u g.1, Submodule.subset_span ⟨g.1, hXT g.2, rfl⟩⟩ : V))
      let SX' : Set V' := Set.range (fun g : X => (⟨u' g.1, Submodule.subset_span ⟨g.1, hXT g.2, rfl⟩⟩ : V'))
      have hmapV : Submodule.map V.subtype (Submodule.span F SX) = matroidSpan u X := by
        dsimp only [matroidSpan]
        rw [Submodule.map_span]
        congr 1
        ext w
        simp only [Set.mem_image, SX, Set.mem_range, Finset.mem_coe]
        constructor
        · rintro ⟨_, ⟨⟨g, hg⟩, rfl⟩, rfl⟩
          exact ⟨g, hg, rfl⟩
        · rintro ⟨g, hg, rfl⟩
          exact ⟨⟨u g, Submodule.subset_span ⟨g, hXT hg, rfl⟩⟩, ⟨⟨g, hg⟩, rfl⟩, rfl⟩
      have hmapV' : Submodule.map V'.subtype (Submodule.span F SX') = matroidSpan u' X := by
        dsimp only [matroidSpan]
        rw [Submodule.map_span]
        congr 1
        ext w
        simp only [Set.mem_image, SX', Set.mem_range, Finset.mem_coe]
        constructor
        · rintro ⟨_, ⟨⟨g, hg⟩, rfl⟩, rfl⟩
          exact ⟨g, hg, rfl⟩
        · rintro ⟨g, hg, rfl⟩
          exact ⟨⟨u' g, Submodule.subset_span ⟨g, hXT hg, rfl⟩⟩, ⟨⟨g, hg⟩, rfl⟩, rfl⟩
      have hv_iff : (v : Fin d → F) ∈ matroidSpan u X ↔ v ∈ Submodule.span F SX := by
        rw [← hmapV]
        exact ⟨fun ⟨w, hw, hwv⟩ => Subtype.ext hwv ▸ hw, fun hv => ⟨v, hv, rfl⟩⟩
      have hφv_iff : (φ v : Fin d' → F) ∈ matroidSpan u' X ↔ φ v ∈ Submodule.span F SX' := by
        rw [← hmapV']
        exact ⟨fun ⟨w, hw, hwv⟩ => Subtype.ext hwv ▸ hw, fun hv => ⟨φ v, hv, rfl⟩⟩
      have hspan_eq : Submodule.map φ.toLinearMap (Submodule.span F SX) = Submodule.span F SX' := by
        rw [Submodule.map_span]
        apply le_antisymm
        · rw [Submodule.span_le]
          rintro _ ⟨_, ⟨⟨g, hgX⟩, rfl⟩, rfl⟩
          obtain ⟨c, _, hc_eq⟩ := hφ g (hXT hgX)
          have h_eq : φ ⟨u g, Submodule.subset_span ⟨g, hXT hgX, rfl⟩⟩ =
              c • (⟨u' g, Submodule.subset_span ⟨g, hXT hgX, rfl⟩⟩ : V') :=
            Subtype.ext hc_eq
          change φ ⟨u g, Submodule.subset_span ⟨g, hXT hgX, rfl⟩⟩ ∈ Submodule.span F SX'
          rw [h_eq]
          exact Submodule.smul_mem _ c (Submodule.subset_span ⟨⟨g, hgX⟩, rfl⟩)
        · rw [Submodule.span_le]
          rintro _ ⟨⟨g, hgX⟩, rfl⟩
          obtain ⟨c, hc0, hc_eq⟩ := hφ g (hXT hgX)
          have h_eq : (⟨u' g, Submodule.subset_span ⟨g, hXT hgX, rfl⟩⟩ : V') =
              c⁻¹ • φ ⟨u g, Submodule.subset_span ⟨g, hXT hgX, rfl⟩⟩ := by
            apply Subtype.ext
            change u' g = c⁻¹ • (φ ⟨u g, Submodule.subset_span ⟨g, hXT hgX, rfl⟩⟩ : Fin d' → F)
            rw [hc_eq, inv_smul_smul₀ hc0]
          change (⟨u' g, Submodule.subset_span ⟨g, hXT hgX, rfl⟩⟩ : V') ∈
            Submodule.span F (⇑φ.toLinearMap '' SX)
          rw [h_eq]
          exact Submodule.smul_mem _ c⁻¹
            (Submodule.subset_span ⟨⟨u g, Submodule.subset_span ⟨g, hXT hgX, rfl⟩⟩, ⟨⟨g, hgX⟩, rfl⟩, rfl⟩)
      rw [hv_iff, hφv_iff, ← hspan_eq]
      exact ⟨fun hv => ⟨v, hv, rfl⟩, fun ⟨w, hw, hwv⟩ => φ.injective hwv ▸ hw⟩
    refine ⟨⟨hμ_nn, ?_, hμ_sum⟩, ?_⟩
    · intro A hμA
      obtain ⟨hAT, hli⟩ := hμ_supp A hμA
      exact ⟨hAT, (hindep A hAT).mp hli⟩
    · intro U'
      let W' : Submodule F V' := Submodule.comap V'.subtype U'
      let W : Submodule F V := Submodule.map φ.symm.toLinearMap W'
      let U : Submodule F (Fin d → F) := Submodule.map V.subtype W
      have hmap_W' : Submodule.map V'.subtype W' = V' ⊓ U' := by
        dsimp only [W']
        rw [Submodule.map_comap_eq, Submodule.range_subtype]
      have hdim_le : Module.finrank F U ≤ Module.finrank F U' := by
        have h1 : Module.finrank F U = Module.finrank F (V' ⊓ U' : Submodule F (Fin d' → F)) := by
          dsimp only [U, W]
          rw [Submodule.finrank_map_subtype_eq, LinearEquiv.finrank_map_eq,
              ← hmap_W', Submodule.finrank_map_subtype_eq]
        rw [h1]
        exact Submodule.finrank_mono inf_le_right
      have hload_eq : ∀ A : Finset (Fin n), μ A ≠ 0 → subspaceLoad u U A = subspaceLoad u' U' A := by
        intro A hμA
        have hAT : A ⊆ T := (hμ_supp A hμA).1
        dsimp only [subspaceLoad]
        have hA_le : matroidSpan u A ≤ V :=
          Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr hAT))
        have hA'_le : matroidSpan u' A ≤ V' :=
          Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr hAT))
        let Y : Submodule F V := Submodule.comap V.subtype (matroidSpan u A)
        let Y' : Submodule F V' := Submodule.comap V'.subtype (matroidSpan u' A)
        have hmap_Y : Submodule.map V.subtype Y = matroidSpan u A := by
          dsimp only [Y]; rw [Submodule.map_comap_eq, Submodule.range_subtype]; exact inf_eq_right.mpr hA_le
        have hmap_Y' : Submodule.map V'.subtype Y' = matroidSpan u' A := by
          dsimp only [Y']; rw [Submodule.map_comap_eq, Submodule.range_subtype]; exact inf_eq_right.mpr hA'_le
        have hY_eq : Submodule.map φ.symm.toLinearMap Y' = Y := by
          ext v
          simp only [Submodule.mem_map, LinearEquiv.coe_toLinearMap, Y, Y', Submodule.mem_comap]
          constructor
          · rintro ⟨v', hv', rfl⟩
            exact (h_span A hAT (φ.symm v')).mpr (by simpa using hv')
          · intro hv
            exact ⟨φ v, (h_span A hAT v).mp hv, φ.symm_apply_apply v⟩
        have hinf_V : matroidSpan u A ⊓ U = Submodule.map V.subtype (Y ⊓ W) := by
          rw [Submodule.map_inf V.subtype (Submodule.subtype_injective V), hmap_Y]
        have hinf_V' : matroidSpan u' A ⊓ U' = Submodule.map V'.subtype (Y' ⊓ W') := by
          rw [Submodule.map_inf V'.subtype (Submodule.subtype_injective V'), hmap_Y', hmap_W',
              ← inf_assoc, inf_eq_left.mpr hA'_le]
        have hinf_φ : Y ⊓ W = Submodule.map φ.symm.toLinearMap (Y' ⊓ W') := by
          rw [Submodule.map_inf φ.symm.toLinearMap φ.symm.injective, hY_eq]
        rw [hinf_V, hinf_V', Submodule.finrank_map_subtype_eq, Submodule.finrank_map_subtype_eq,
            hinf_φ, LinearEquiv.finrank_map_eq]
      have hsum_eq : (∑ A : Finset (Fin n), μ A * (subspaceLoad u' U' A : ℝ)) =
          ∑ A : Finset (Fin n), μ A * (subspaceLoad u U A : ℝ) := by
        refine Finset.sum_congr rfl fun A _ => ?_
        by_cases hμA : μ A = 0
        · simp [hμA]
        · rw [hload_eq A hμA]
      calc (∑ A : Finset (Fin n), μ A * (subspaceLoad u' U' A : ℝ))
          = ∑ A : Finset (Fin n), μ A * (subspaceLoad u U A : ℝ) := hsum_eq
        _ ≤ β * (Module.finrank F U : ℝ) := hμ_load U
        _ ≤ β * (Module.finrank F U' : ℝ) :=
            mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hdim_le) hβ0
  have h_common_basis : ∀ (F : Type) [Field F] (n d d' : ℕ) (T : Finset (Fin n))
      (u : Fin n → (Fin d → F)) (u' : Fin n → (Fin d' → F)),
      (∀ S ⊆ T, LinearIndependent F (fun g : S => u g.1) ↔
                LinearIndependent F (fun g : S => u' g.1)) →
      ∃ (D : Finset (Fin n)) (_ : D ⊆ T)
        (bV : Module.Basis D F (matroidSpan u T))
        (bV' : Module.Basis D F (matroidSpan u' T)),
        (∀ b : D, (bV b : Fin d → F) = u b.1) ∧
        (∀ b : D, (bV' b : Fin d' → F) = u' b.1) ∧
        (∀ (k : ℕ) (r : Fin k → D) (c : Fin k → {g : Fin n // g ∈ T \ D}),
          (Matrix.submatrix
            (Matrix.of (fun (b : D) (g : {g : Fin n // g ∈ T \ D}) =>
              bV.repr ⟨u g.1, Submodule.subset_span ⟨g.1, (Finset.mem_sdiff.mp g.2).1, rfl⟩⟩ b))
            r c).det = 0 ↔
          (Matrix.submatrix
            (Matrix.of (fun (b : D) (g : {g : Fin n // g ∈ T \ D}) =>
              bV'.repr ⟨u' g.1, Submodule.subset_span ⟨g.1, (Finset.mem_sdiff.mp g.2).1, rfl⟩⟩ b))
            r c).det = 0) := by
    clear h_dim_compress h_proj_transfer
    have h_single_basis : ∀ (F : Type) [Field F] {n d : ℕ} (T D : Finset (Fin n)), D ⊆ T →
        ∀ (u : Fin n → (Fin d → F)),
        LinearIndependent F (fun b : D => u b.1) →
        (∀ g ∈ T \ D, ¬ LinearIndependent F (fun x : (insert g D : Finset (Fin n)) => u x.1)) →
        ∃ (bV : Module.Basis D F (matroidSpan u T)),
          (∀ b : D, (bV b : Fin d → F) = u b.1) ∧
          (∀ (k : ℕ) (r : Fin k → D) (c : Fin k → {g : Fin n // g ∈ T \ D}),
            Function.Injective r → Function.Injective c →
            ((Matrix.submatrix
              (Matrix.of (fun (b : D) (g : {g : Fin n // g ∈ T \ D}) =>
                bV.repr ⟨u g.1, Submodule.subset_span ⟨g.1, (Finset.mem_sdiff.mp g.2).1, rfl⟩⟩ b))
              r c).det = 0 ↔
             ¬ LinearIndependent F
                (fun s : ((D \ Finset.univ.image (fun i => (r i).1)) ∪
                          Finset.univ.image (fun j => (c j).1) : Finset (Fin n)) => u s.1))) := by
      intro F instF n d T D hDT u hli_D hmax_D
      let V := matroidSpan u T
      let vD : D → V := fun b => ⟨u b.1, Submodule.subset_span ⟨b.1, hDT b.2, rfl⟩⟩
      have hli_vD : LinearIndependent F vD :=
        LinearIndependent.of_comp V.subtype hli_D
      have hsp_D : u '' (T : Set (Fin n)) ⊆ (Submodule.span F (u '' (D : Set (Fin n))) : Set (Fin d → F)) := by
        rintro _ ⟨g, hgT, rfl⟩
        by_cases hgD : g ∈ D
        · exact Submodule.subset_span ⟨g, hgD, rfl⟩
        · by_contra hg_not_span
          have hg_sdiff : g ∈ T \ D := Finset.mem_sdiff.mpr ⟨hgT, hgD⟩
          have hli_on : LinearIndepOn F u (D : Set (Fin n)) := hli_D
          have hli_ins : LinearIndepOn F u (Set.insert g (D : Set (Fin n))) :=
            hli_on.insert hg_not_span
          have hcoe : ((insert g D : Finset (Fin n)) : Set (Fin n)) = Set.insert g (D : Set (Fin n)) :=
            Finset.coe_insert g D
          have hli_fin : LinearIndependent F (fun x : (insert g D : Finset (Fin n)) => u x.1) := by
            change LinearIndepOn F u ((insert g D : Finset (Fin n)) : Set (Fin n))
            rwa [hcoe]
          exact hmax_D g hg_sdiff hli_fin
      have hmap_vD : Submodule.map V.subtype (Submodule.span F (Set.range vD)) =
          Submodule.span F (u '' (D : Set (Fin n))) := by
        rw [Submodule.map_span]
        congr 1
        ext w
        simp only [Set.mem_image, Set.mem_range, Finset.mem_coe]
        constructor
        · rintro ⟨_, ⟨⟨b, hbD⟩, rfl⟩, rfl⟩
          exact ⟨b, hbD, rfl⟩
        · rintro ⟨b, hbD, rfl⟩
          exact ⟨vD ⟨b, hbD⟩, ⟨⟨b, hbD⟩, rfl⟩, rfl⟩
      have htop_vD : ⊤ ≤ Submodule.span F (Set.range vD) := by
        intro v _
        have hv1 : (v : Fin d → F) ∈ Submodule.span F (u '' (D : Set (Fin n))) :=
          (Submodule.span_le.mpr hsp_D) v.2
        rw [← hmap_vD] at hv1
        rcases hv1 with ⟨w, hw, hwv⟩
        exact Subtype.ext hwv ▸ hw
      let bV : Module.Basis D F V := Module.Basis.mk hli_vD htop_vD
      refine ⟨bV, ?_, ?_⟩
      · intro b
        change ((Module.Basis.mk hli_vD htop_vD) b : Fin d → F) = u b.1
        rw [Module.Basis.mk_apply]
      · intro k r c hr hc
        let X : Finset (Fin n) := Finset.univ.image (fun i => (r i).1)
        let Y : Finset (Fin n) := Finset.univ.image (fun j => (c j).1)
        let S : Finset (Fin n) := (D \ X) ∪ Y
        have hST : S ⊆ T := by
          intro x hx
          rcases Finset.mem_union.mp hx with hxDX | hxY
          · exact hDT (Finset.mem_sdiff.mp hxDX).1
          · rcases Finset.mem_image.mp hxY with ⟨j, _, rfl⟩
            exact (Finset.mem_sdiff.mp (c j).2).1
        let A : Matrix D {g : Fin n // g ∈ T \ D} F :=
          Matrix.of (fun b g => bV.repr ⟨u g.1, Submodule.subset_span ⟨g.1, (Finset.mem_sdiff.mp g.2).1, rfl⟩⟩ b)
        have hc_inj_val : Function.Injective (fun j : Fin k => (c j).1) := fun j1 j2 h =>
          hc (Subtype.ext h)
        have hdisj : Disjoint (D \ X) Y := by
          rw [Finset.disjoint_left]
          intro x hxDX hxY
          have hxD : x ∈ D := (Finset.mem_sdiff.mp hxDX).1
          rcases Finset.mem_image.mp hxY with ⟨j, _, rfl⟩
          exact (Finset.mem_sdiff.mp (c j).2).2 hxD
        let f_to_S : {x // x ∈ D \ X} ⊕ Fin k → S := fun z =>
          match z with
          | Sum.inl d0 => ⟨d0.1, Finset.mem_union_left _ d0.2⟩
          | Sum.inr j => ⟨(c j).1, Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))⟩
        have hf_bij : Function.Bijective f_to_S := by
          refine ⟨?_, ?_⟩
          · rintro (d1 | j1) (d2 | j2) h
            · have hval : d1.1 = d2.1 := congrArg (fun s : S => s.1) h
              exact congrArg Sum.inl (Subtype.ext hval)
            · exfalso
              have hval : d1.1 = (c j2).1 := congrArg (fun s : S => s.1) h
              exact Finset.disjoint_left.mp hdisj d1.2 (hval ▸ Finset.mem_image_of_mem _ (Finset.mem_univ j2))
            · exfalso
              have hval : (c j1).1 = d2.1 := congrArg (fun s : S => s.1) h
              exact Finset.disjoint_left.mp hdisj d2.2 (hval.symm ▸ Finset.mem_image_of_mem _ (Finset.mem_univ j1))
            · have hval : (c j1).1 = (c j2).1 := congrArg (fun s : S => s.1) h
              exact congrArg Sum.inr (hc_inj_val hval)
          · rintro ⟨x, hx⟩
            rcases Finset.mem_union.mp hx with hxDX | hxY
            · exact ⟨Sum.inl ⟨x, hxDX⟩, rfl⟩
            · rcases Finset.mem_image.mp hxY with ⟨j, _, rfl⟩
              exact ⟨Sum.inr j, rfl⟩
        let eS : {x // x ∈ D \ X} ⊕ Fin k ≃ S := Equiv.ofBijective f_to_S hf_bij
        let uV : S → V := fun s => ⟨u s.1, Submodule.subset_span ⟨s.1, hST s.2, rfl⟩⟩
        have hli_uV : LinearIndependent F (fun s : S => u s.1) ↔ LinearIndependent F uV :=
          ⟨fun h => LinearIndependent.of_comp V.subtype h,
           fun h => h.map' V.subtype (Submodule.ker_subtype V)⟩
        let W : {x // x ∈ D \ X} ⊕ Fin k → (D → F) := fun z => bV.equivFun (uV (eS z))
        have hli_W : LinearIndependent F uV ↔ LinearIndependent F W := by
          rw [← linearIndependent_equiv eS]
          exact ⟨fun h => h.map' bV.equivFun.toLinearMap bV.equivFun.ker,
                 fun h => LinearIndependent.of_comp bV.equivFun.toLinearMap h⟩
        have hW_inl : ∀ (d0 : {x // x ∈ D \ X}) (b : D),
            W (Sum.inl d0) b = if b.1 = d0.1 then 1 else 0 := by
          intro d0 b
          change bV.repr (uV ⟨d0.1, Finset.mem_union_left _ d0.2⟩) b = _
          have hdD : d0.1 ∈ D := (Finset.mem_sdiff.mp d0.2).1
          have huV_eq : uV ⟨d0.1, Finset.mem_union_left _ d0.2⟩ = bV ⟨d0.1, hdD⟩ := by
            apply Subtype.ext
            change u d0.1 = ((Module.Basis.mk hli_vD htop_vD) ⟨d0.1, hdD⟩ : Fin d → F)
            rw [Module.Basis.mk_apply]
          rw [huV_eq, Module.Basis.repr_self, Finsupp.single_apply]
          by_cases hbd : (⟨d0.1, hdD⟩ : D) = b
          · have hval : b.1 = d0.1 := (congrArg Subtype.val hbd).symm
            simp [hbd, hval]
          · have hval : b.1 ≠ d0.1 := fun hv => hbd (Subtype.ext hv.symm)
            simp [hbd, hval]
        have hW_inr : ∀ (j : Fin k) (b : D), W (Sum.inr j) b = A b (c j) := by
          intro j b
          rfl
        rw [hli_uV, hli_W, ← Matrix.exists_mulVec_eq_zero_iff, Fintype.linearIndependent_iff]
        push_neg
        constructor
        · rintro ⟨μ, hμ0, hmul⟩
          let α_fn : {x // x ∈ D \ X} → F := fun d0 =>
            - ∑ j : Fin k, μ j * A ⟨d0.1, (Finset.mem_sdiff.mp d0.2).1⟩ (c j)
          refine ⟨Sum.elim α_fn μ, ?_, ?_⟩
          · ext b
            simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
              Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hW_inl, hW_inr]
            by_cases hbX : b.1 ∈ X
            · rcases Finset.mem_image.mp hbX with ⟨i, _, hri⟩
              have hbr : b = r i := Subtype.ext hri.symm
              have hsum0 : (∑ d0 : {x // x ∈ D \ X}, α_fn d0 * (if b.1 = d0.1 then 1 else 0)) = 0 := by
                apply Finset.sum_eq_zero
                intro d0 _
                have hne : b.1 ≠ d0.1 := fun h => (Finset.mem_sdiff.mp d0.2).2 (h ▸ hbX)
                simp [hne]
              rw [hsum0, zero_add, hbr]
              have hi := congrFun hmul i
              simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.zero_apply] at hi
              simpa [mul_comm] using hi
            · let b0 : {x // x ∈ D \ X} := ⟨b.1, Finset.mem_sdiff.mpr ⟨b.2, hbX⟩⟩
              have hsum1 : (∑ d0 : {x // x ∈ D \ X}, α_fn d0 * (if b.1 = d0.1 then 1 else 0)) = α_fn b0 := by
                rw [Finset.sum_eq_single b0]
                · simp [b0]
                · intro d0 _ hd0
                  have hne : b.1 ≠ d0.1 := fun h => hd0 (Subtype.ext h.symm)
                  simp [hne]
                · intro h; exact absurd (Finset.mem_univ b0) h
              rw [hsum1]
              have hb_sub : (⟨b0.1, (Finset.mem_sdiff.mp b0.2).1⟩ : D) = b := Subtype.ext rfl
              simp only [α_fn, hb_sub]
              ring
          · obtain ⟨j, hj⟩ : ∃ j, μ j ≠ 0 := Function.ne_iff.mp hμ0
            exact ⟨Sum.inr j, hj⟩
        · rintro ⟨g, hsum, z0, hz0⟩
          let μ : Fin k → F := fun j => g (Sum.inr j)
          have hmul : (A.submatrix r c).mulVec μ = 0 := by
            ext i
            have hi := congrFun hsum (r i)
            simp only [Fintype.sum_sum_type, Finset.sum_apply, Pi.smul_apply,
              smul_eq_mul, Pi.zero_apply, hW_inl, hW_inr] at hi
            have hsum0 : (∑ d0 : {x // x ∈ D \ X}, g (Sum.inl d0) * (if (r i).1 = d0.1 then 1 else 0)) = 0 := by
              apply Finset.sum_eq_zero
              intro d0 _
              have hriX : (r i).1 ∈ X := Finset.mem_image_of_mem _ (Finset.mem_univ i)
              have hne : (r i).1 ≠ d0.1 := fun h => (Finset.mem_sdiff.mp d0.2).2 (h ▸ hriX)
              simp [hne]
            rw [hsum0, zero_add] at hi
            simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.zero_apply, μ]
            simpa [mul_comm] using hi
          have hμ0 : μ ≠ 0 := by
            intro hμ_zero
            have hg_inl : ∀ d0 : {x // x ∈ D \ X}, g (Sum.inl d0) = 0 := by
              intro d0
              let b : D := ⟨d0.1, (Finset.mem_sdiff.mp d0.2).1⟩
              have hb := congrFun hsum b
              simp only [Fintype.sum_sum_type, Finset.sum_apply, Pi.smul_apply,
                smul_eq_mul, Pi.zero_apply, hW_inl, hW_inr] at hb
              have hsum1 : (∑ d1 : {x // x ∈ D \ X}, g (Sum.inl d1) * (if b.1 = d1.1 then 0 + 1 else 0)) =
                  g (Sum.inl d0) := by
                rw [Finset.sum_eq_single d0]
                · simp [b]
                · intro d1 _ hd1
                  have hne : b.1 ≠ d1.1 := fun h => hd1 (Subtype.ext h.symm)
                  simp [hne]
                · intro h; exact absurd (Finset.mem_univ d0) h
              simp only [zero_add] at hsum1
              have hsum2 : (∑ j : Fin k, g (Sum.inr j) * A b (c j)) = 0 := by
                apply Finset.sum_eq_zero
                intro j _
                have hj0 : g (Sum.inr j) = 0 := congrFun hμ_zero j
                simp [hj0]
              rw [hsum1, hsum2, add_zero] at hb
              exact hb
            cases z0 with
            | inl d0 => exact hz0 (hg_inl d0)
            | inr j => exact hz0 (congrFun hμ_zero j)
          exact ⟨μ, hμ0, hmul⟩
    intro F instF n d d' T u u' hindep
    let ℱ := T.powerset.filter (fun S : Finset (Fin n) => LinearIndependent F (fun g : S => u g.1))
    have hℱ_ne : ℱ.Nonempty := ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset T,
      linearIndependent_empty_type⟩⟩
    obtain ⟨D, hD_mem, hD_max⟩ := Finset.exists_max_image ℱ Finset.card hℱ_ne
    have hDT : D ⊆ T := Finset.mem_powerset.mp (Finset.mem_filter.mp hD_mem).1
    have hli_u : LinearIndependent F (fun b : D => u b.1) := (Finset.mem_filter.mp hD_mem).2
    have hmax_u : ∀ g ∈ T \ D, ¬ LinearIndependent F (fun x : (insert g D : Finset (Fin n)) => u x.1) := by
      intro g hg hli_ins
      rcases Finset.mem_sdiff.mp hg with ⟨hgT, hgD⟩
      have hins_sub : insert g D ⊆ T := Finset.insert_subset hgT hDT
      have hins_mem : insert g D ∈ ℱ :=
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hins_sub, hli_ins⟩
      have hcard_le := hD_max (insert g D) hins_mem
      rw [Finset.card_insert_of_notMem hgD] at hcard_le
      omega
    have hli_u' : LinearIndependent F (fun b : D => u' b.1) := (hindep D hDT).mp hli_u
    have hmax_u' : ∀ g ∈ T \ D, ¬ LinearIndependent F (fun x : (insert g D : Finset (Fin n)) => u' x.1) := by
      intro g hg hli_ins'
      rcases Finset.mem_sdiff.mp hg with ⟨hgT, _⟩
      exact hmax_u g hg ((hindep (insert g D) (Finset.insert_subset hgT hDT)).mpr hli_ins')
    obtain ⟨bV, hbV, hdet_u⟩ := h_single_basis F T D hDT u hli_u hmax_u
    obtain ⟨bV', hbV', hdet_u'⟩ := h_single_basis F T D hDT u' hli_u' hmax_u'
    refine ⟨D, hDT, bV, bV', hbV, hbV', ?_⟩
    intro k r c
    by_cases hr : Function.Injective r
    · by_cases hc : Function.Injective c
      · rw [hdet_u k r c hr hc, hdet_u' k r c hr hc]
        have hS_sub : (D \ Finset.univ.image (fun i => (r i).1)) ∪
            Finset.univ.image (fun j => (c j).1) ⊆ T := by
          intro x hx
          rcases Finset.mem_union.mp hx with hxDX | hxY
          · exact hDT (Finset.mem_sdiff.mp hxDX).1
          · rcases Finset.mem_image.mp hxY with ⟨j, _, rfl⟩
            exact (Finset.mem_sdiff.mp (c j).2).1
        exact not_congr (hindep _ hS_sub)
      · simp only [Function.Injective, not_forall, exists_prop] at hc
        rcases hc with ⟨j1, j2, hj_eq, hj_ne⟩
        have h0 : ∀ (M : Matrix D {g : Fin n // g ∈ T \ D} F), (M.submatrix r c).det = 0 := by
          intro M
          exact Matrix.det_zero_of_column_eq hj_ne (by intro i; simp [hj_eq])
        rw [h0, h0]
    · simp only [Function.Injective, not_forall, exists_prop] at hr
      rcases hr with ⟨i1, i2, hi_eq, hi_ne⟩
      have h0 : ∀ (M : Matrix D {g : Fin n // g ∈ T \ D} F), (M.submatrix r c).det = 0 := by
        intro M
        exact Matrix.det_zero_of_row_eq hi_ne (by ext j; simp [hi_eq])
      rw [h0, h0]
  have h_part2 :
      ∀ (n d d' : ℕ) (T : Finset (Fin n))
        (u : Fin n → (Fin d → ZMod 2)) (u' : Fin n → (Fin d' → ZMod 2))
        (β : ℝ) (μ : Finset (Fin n) → ℝ),
      0 ≤ β →
      (∀ X ⊆ T,
        LinearIndependent (ZMod 2) (fun g : X => u g.1) ↔
        LinearIndependent (ZMod 2) (fun g : X => u' g.1)) →
      IsSubspaceBetaBounded u T β μ →
      IsSubspaceBetaBounded u' T β μ := by
    clear h_dim_compress
    intro n d d' T u u' β μ hβ0 hindep hbound
    obtain ⟨D, _, bV, bV', hbV, hbV', hdet⟩ :=
      h_common_basis (ZMod 2) n d d' T u u' hindep
    let V := matroidSpan u T
    let V' := matroidSpan u' T
    obtain ⟨φ, hφ_bV⟩ : ∃ φ : V ≃ₗ[ZMod 2] V', ∀ b : D, φ (bV b) = bV' b :=
      ⟨bV.equiv bV' (Equiv.refl D), fun b => bV.equiv_apply b bV' (Equiv.refl D)⟩
    have hz2 : ∀ x y : ZMod 2, (x = 0 ↔ y = 0) → x = y := by
      intro x y hxy
      fin_cases x <;> fin_cases y
      · rfl
      · exact (hxy.mp rfl).symm
      · exact hxy.mpr rfl
      · rfl
    have hφ_exact : ∀ (g : Fin n) (hg : g ∈ T),
        (φ ⟨u g, Submodule.subset_span ⟨g, hg, rfl⟩⟩ : Fin d' → ZMod 2) = u' g := by
      intro g hg
      by_cases hgD : g ∈ D
      · have hug_eq : (⟨u g, Submodule.subset_span ⟨g, hg, rfl⟩⟩ : V) = bV ⟨g, hgD⟩ :=
          Subtype.ext (hbV ⟨g, hgD⟩).symm
        rw [hug_eq, hφ_bV ⟨g, hgD⟩]
        exact hbV' ⟨g, hgD⟩
      · let g' : {x : Fin n // x ∈ T \ D} := ⟨g, Finset.mem_sdiff.mpr ⟨hg, hgD⟩⟩
        have hA_eq : ∀ b : D,
            bV.repr ⟨u g, Submodule.subset_span ⟨g, hg, rfl⟩⟩ b =
            bV'.repr ⟨u' g, Submodule.subset_span ⟨g, hg, rfl⟩⟩ b := by
          intro b
          have h1 := hdet 1 (fun _ => b) (fun _ => g')
          simp only [Matrix.det_fin_one, Matrix.submatrix_apply, Matrix.of_apply] at h1
          exact hz2 _ _ h1
        let ug : V := ⟨u g, Submodule.subset_span ⟨g, hg, rfl⟩⟩
        let u'g : V' := ⟨u' g, Submodule.subset_span ⟨g, hg, rfl⟩⟩
        have hsum_u : ∑ b : D, bV.repr ug b • bV b = ug := bV.sum_repr ug
        have hsum_u' : ∑ b : D, bV'.repr u'g b • bV' b = u'g := bV'.sum_repr u'g
        have hφ_ug : φ ug = u'g := by
          rw [← hsum_u, map_sum, ← hsum_u']
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [map_smul, hA_eq b, hφ_bV b]
        exact congrArg Subtype.val hφ_ug
    apply h_proj_transfer (ZMod 2) n d d' T u u' β μ hβ0 hindep _ hbound
    refine ⟨φ, fun g hg => ⟨1, one_ne_zero, ?_⟩⟩
    rw [one_smul]
    exact hφ_exact g hg
  have h_zmod3_scale :
      ∀ (α β : Type) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
        (A A' : Matrix α β (ZMod 3)),
        (∀ (k : ℕ) (r : Fin k → α) (c : Fin k → β),
          (Matrix.submatrix A r c).det = 0 ↔ (Matrix.submatrix A' r c).det = 0) →
        ∃ (σ : α → (ZMod 3)ˣ) (τ : β → (ZMod 3)ˣ),
          ∀ (i : α) (j : β), A' i j = (σ i : ZMod 3) * (τ j : ZMod 3) * A i j := by
    clear h_dim_compress h_proj_transfer h_common_basis h_part2
    intro α β instFα instFβ instDα instDβ A A' hdet
    let zmod3UnitRatio : α → β → (ZMod 3)ˣ :=
      fun i j => if h : A' i j * A i j ≠ 0 then Units.mk0 (A' i j * A i j) h else 1
    let zmod3BipAdj : α ⊕ β → α ⊕ β → Prop :=
      fun x y => match x, y with
        | Sum.inl i, Sum.inr j => A i j ≠ 0
        | Sum.inr j, Sum.inl i => A i j ≠ 0
        | _, _ => False
    let zmod3BipWeight : α ⊕ β → α ⊕ β → (ZMod 3)ˣ :=
      fun x y => match x, y with
        | Sum.inl i, Sum.inr j => zmod3UnitRatio i j
        | Sum.inr j, Sum.inl i => zmod3UnitRatio i j
        | _, _ => 1
    let isZMod3BipWalk : α ⊕ β → α ⊕ β → List (α ⊕ β) → Prop :=
      fun x y L => List.rec (motive := fun _ => (α ⊕ β) → Prop)
        (fun cur => cur = y)
        (fun z _ ih cur => zmod3BipAdj cur z ∧ ih z)
        L x
    let zmod3WalkWeight : α ⊕ β → List (α ⊕ β) → (ZMod 3)ˣ :=
      fun x L => List.rec (motive := fun _ => (α ⊕ β) → (ZMod 3)ˣ)
        (fun _ => 1)
        (fun z _ ih cur => zmod3BipWeight cur z * ih z)
        L x
    have hwt_nil : ∀ x, zmod3WalkWeight x [] = 1 := fun _ => rfl
    have hwt_cons : ∀ x z L, zmod3WalkWeight x (z :: L) = zmod3BipWeight x z * zmod3WalkWeight z L :=
      fun _ _ _ => rfl
    have hz3_sq : ∀ x : ZMod 3, x ≠ 0 → x * x = 1 := by
      intro x hx
      fin_cases x
      · exact absurd rfl hx
      · rfl
      · rfl
    have hunit_sq : ∀ u : (ZMod 3)ˣ, u * u = 1 := by
      intro u
      apply Units.ext
      push_cast
      exact hz3_sq u.1 u.ne_zero
    have hz3_eq_or_neg : ∀ x y : ZMod 3, x ≠ 0 → y ≠ 0 → (x + y = 0 ∨ x = y) := by
      intro x y hx hy
      fin_cases x <;> fin_cases y
      · exact absurd rfl hx
      · exact absurd rfl hx
      · exact absurd rfl hx
      · exact absurd rfl hy
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exact absurd rfl hy
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hz3_det_pair : ∀ p1 p2 q1 q2 s : ZMod 3,
        p1 ≠ 0 → p2 ≠ 0 → q1 ≠ 0 → q2 ≠ 0 → s * s = 1 →
        (p1 + s * p2 = 0 ↔ q1 + s * q2 = 0) → (q1 * p1) * (q2 * p2) = 1 := by
      intro p1 p2 q1 q2 s hp1 hp2 hq1 hq2 hs hiff
      have hs0 : s ≠ 0 := by intro h; rw [h, mul_zero] at hs; exact zero_ne_one hs
      have hsp2 : s * p2 ≠ 0 := mul_ne_zero hs0 hp2
      have hsq2 : s * q2 ≠ 0 := mul_ne_zero hs0 hq2
      by_cases hp : p1 + s * p2 = 0
      · have hq : q1 + s * q2 = 0 := hiff.mp hp
        have hp1_eq : p1 = -(s * p2) := eq_neg_of_add_eq_zero_left hp
        have hq1_eq : q1 = -(s * q2) := eq_neg_of_add_eq_zero_left hq
        calc (q1 * p1) * (q2 * p2)
            = (-(s * q2) * -(s * p2)) * (q2 * p2) := by rw [hp1_eq, hq1_eq]
          _ = (s * s) * (p2 * p2) * (q2 * q2) := by ring
          _ = 1 * 1 * 1 := by rw [hs, hz3_sq p2 hp2, hz3_sq q2 hq2]
          _ = 1 := by ring
      · have hq : q1 + s * q2 ≠ 0 := fun h => hp (hiff.mpr h)
        have hp1_eq : p1 = s * p2 := (hz3_eq_or_neg p1 (s * p2) hp1 hsp2).resolve_left hp
        have hq1_eq : q1 = s * q2 := (hz3_eq_or_neg q1 (s * q2) hq1 hsq2).resolve_left hq
        calc (q1 * p1) * (q2 * p2)
            = ((s * q2) * (s * p2)) * (q2 * p2) := by rw [hp1_eq, hq1_eq]
          _ = (s * s) * (p2 * p2) * (q2 * q2) := by ring
          _ = 1 * 1 * 1 := by rw [hs, hz3_sq p2 hp2, hz3_sq q2 hq2]
          _ = 1 := by ring
    have hzero : ∀ i j, A i j = 0 ↔ A' i j = 0 := by
      intro i j
      have h1 := hdet 1 (fun _ => i) (fun _ => j)
      simpa only [Matrix.det_fin_one, Matrix.submatrix_apply] using h1
    have huR_val : ∀ i j, A i j ≠ 0 → (zmod3UnitRatio i j : ZMod 3) = A' i j * A i j := by
      intro i j hA
      have hA' : A' i j ≠ 0 := fun h => hA (hzero i j |>.mpr h)
      have hmul : A' i j * A i j ≠ 0 := mul_ne_zero hA' hA
      simp only [zmod3UnitRatio, dif_pos hmul, Units.val_mk0]
    have hadj_symm : ∀ x y, zmod3BipAdj x y ↔ zmod3BipAdj y x := by
      rintro (i | j) (i' | j') <;> rfl
    have hew_symm : ∀ x y, zmod3BipWeight x y = zmod3BipWeight y x := by
      rintro (i | j) (i' | j') <;> rfl
    have hadj_flip : ∀ x y, zmod3BipAdj x y → Sum.isLeft x = !Sum.isLeft y := by
      rintro (i | j) (i' | j') h
      · exact False.elim h
      · rfl
      · rfl
      · exact False.elim h
    have hwalk_append : ∀ L₁ L₂ x y z,
        isZMod3BipWalk x y L₁ → isZMod3BipWalk y z L₂ →
        isZMod3BipWalk x z (L₁ ++ L₂) ∧
        zmod3WalkWeight x (L₁ ++ L₂) = zmod3WalkWeight x L₁ * zmod3WalkWeight y L₂ := by
      intro L₁
      induction L₁ with
      | nil =>
        intro L₂ x y z h1 h2
        change x = y at h1
        subst h1
        exact ⟨h2, by simp only [List.nil_append, hwt_nil, one_mul]⟩
      | cons w L₁ ih =>
        intro L₂ x y z h1 h2
        rcases h1 with ⟨hxw, h1'⟩
        obtain ⟨hw_app, hwt_app⟩ := ih L₂ w y z h1' h2
        refine ⟨⟨hxw, hw_app⟩, ?_⟩
        simp only [List.cons_append, hwt_cons, hwt_app, mul_assoc]
    have hwalk_split : ∀ L₁ u L₂ x z,
        isZMod3BipWalk x z (L₁ ++ u :: L₂) →
        isZMod3BipWalk x u (L₁ ++ [u]) ∧ isZMod3BipWalk u z L₂ ∧
        zmod3WalkWeight x (L₁ ++ u :: L₂) =
          zmod3WalkWeight x (L₁ ++ [u]) * zmod3WalkWeight u L₂ := by
      intro L₁
      induction L₁ with
      | nil =>
        intro u L₂ x z h
        rcases h with ⟨hxu, huL₂⟩
        refine ⟨⟨hxu, rfl⟩, huL₂, ?_⟩
        simp only [List.nil_append, hwt_cons, hwt_nil, mul_one]
      | cons w L₁ ih =>
        intro u L₂ x z h
        rcases h with ⟨hxw, h'⟩
        obtain ⟨h1, h2, hwt⟩ := ih u L₂ w z h'
        refine ⟨⟨hxw, h1⟩, h2, ?_⟩
        simp only [List.cons_append, hwt_cons, hwt, mul_assoc]
    have hwalk_rev : ∀ L x y,
        isZMod3BipWalk x y L →
        ∃ L', isZMod3BipWalk y x L' ∧ zmod3WalkWeight y L' = zmod3WalkWeight x L := by
      intro L
      induction L with
      | nil =>
        intro x y h
        change x = y at h
        subst h
        exact ⟨[], rfl, rfl⟩
      | cons w L ih =>
        intro x y ⟨hxw, hwy⟩
        obtain ⟨L', hL', hwt'⟩ := ih w y hwy
        have hwx : isZMod3BipWalk w x [x] := ⟨(hadj_symm x w).mp hxw, rfl⟩
        obtain ⟨happ, hwt_app⟩ := hwalk_append L' [x] y w x hL' hwx
        refine ⟨L' ++ [x], happ, ?_⟩
        rw [hwt_app, hwt']
        simp only [hwt_cons, hwt_nil, one_mul, hew_symm w x, mul_comm]
    have hwalk_parity : ∀ L x y,
        isZMod3BipWalk x y L →
        (Even L.length → Sum.isLeft x = Sum.isLeft y) ∧
        (¬ Even L.length → Sum.isLeft x = !Sum.isLeft y) := by
      intro L
      induction L with
      | nil =>
        intro x y h
        change x = y at h
        subst h
        exact ⟨fun _ => rfl, fun hne => absurd Even.zero hne⟩
      | cons w L ih =>
        intro x y ⟨hxw, hwy⟩
        have hflip := hadj_flip x w hxw
        obtain ⟨he, ho⟩ := ih w y hwy
        simp only [List.length_cons, Nat.even_add_one, Classical.not_not]
        refine ⟨fun hnL => ?_, fun heL => ?_⟩
        · have hw := ho hnL
          rw [hflip, hw, Bool.not_not]
        · have hw := he heL
          rw [hflip, hw]
    have hnot_nodup : ∀ (L : List (α ⊕ β)), ¬ L.Nodup →
        ∃ P u Q R, L = P ++ u :: Q ++ u :: R := by
      intro L
      induction L with
      | nil =>
        intro h; exact absurd List.nodup_nil h
      | cons a M ih =>
        intro h
        rw [List.nodup_cons, not_and_or] at h
        rcases h with haM | hnM
        · have haM' : a ∈ M := by simpa using haM
          obtain ⟨Q, R, rfl⟩ := List.append_of_mem haM'
          exact ⟨[], a, Q, R, rfl⟩
        · obtain ⟨P, u, Q, R, rfl⟩ := ih hnM
          exact ⟨a :: P, u, Q, R, rfl⟩
    have hlist_split_one : ∀ (M : List (α ⊕ β)) (idx : ℕ) (h : idx < M.length),
        M = M.take idx ++ M[idx] :: M.drop (idx + 1) := by
      intro M
      induction M with
      | nil => intro idx h; simp at h
      | cons x M' ih =>
        intro idx h
        cases idx with
        | zero => rfl
        | succ s =>
          have hs : s < M'.length := Nat.lt_of_succ_lt_succ h
          exact congrArg (x :: ·) (ih s hs)
    have hwalk_getLast : ∀ (L : List (α ⊕ β)) (x y : α ⊕ β) (hne : L ≠ []),
        isZMod3BipWalk x y L → L[L.length - 1]'(Nat.sub_lt (List.length_pos_iff.mpr hne) Nat.zero_lt_one) = y := by
      intro L
      induction L with
      | nil => intro x y hne; exact absurd rfl hne
      | cons z M ih =>
        intro x y _ ⟨_, hzy⟩
        cases M with
        | nil => exact hzy
        | cons w M' =>
          have h := ih z y (List.cons_ne_nil w M') hzy
          simpa using h
    have hwalk_step_adj : ∀ (L : List (α ⊕ β)) (x y : α ⊕ β),
        isZMod3BipWalk x y L →
        ∀ (s : ℕ) (hs : s < L.length),
          zmod3BipAdj ((x :: L)[s]'(Nat.lt_succ_of_lt hs)) ((x :: L)[s + 1]'(Nat.succ_lt_succ hs)) := by
      intro L
      induction L with
      | nil => intro x y _ s hs; simp at hs
      | cons z M ih =>
        intro x y ⟨hxz, hzy⟩ s hs
        cases s with
        | zero => exact hxz
        | succ s' =>
          have hs' : s' < M.length := Nat.lt_of_succ_lt_succ hs
          exact ih z y hzy s' hs'
    have hwalk_wt_prod : ∀ (L : List (α ⊕ β)) (x : α ⊕ β),
        zmod3WalkWeight x L =
        ∏ s : Fin L.length,
          zmod3BipWeight ((x :: L)[s.1]'(Nat.lt_succ_of_lt s.2))
                         ((x :: L)[s.1 + 1]'(Nat.succ_lt_succ s.2)) := by
      intro L
      induction L with
      | nil =>
        intro x
        simp only [hwt_nil, List.length_nil, Finset.univ_eq_empty, Finset.prod_empty]
      | cons z M ih =>
        intro x
        simp only [hwt_cons, ih z, List.length_cons]
        rw [Fin.prod_univ_succ]
        rfl
    have hprod_even_pairs : ∀ (k : ℕ) (f : Fin (2 * k) → (ZMod 3)ˣ),
        (∏ s : Fin (2 * k), f s) =
        ∏ t : Fin k, (f ⟨2 * t.1, by omega⟩ * f ⟨2 * t.1 + 1, by omega⟩) := by
      intro k
      induction k with
      | zero =>
        intro f
        simp only [Nat.mul_zero, Finset.univ_eq_empty, Finset.prod_empty]
      | succ m ih =>
        intro f
        have hlen : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
        let g : Fin ((2 * m + 1) + 1) → (ZMod 3)ˣ := fun s => f (s.cast hlen.symm)
        have hfg : (∏ s : Fin (2 * (m + 1)), f s) = ∏ s : Fin ((2 * m + 1) + 1), g s := by
          refine Fintype.prod_equiv (finCongr hlen) _ _ (fun s => rfl)
        rw [hfg, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
        have hprev : (∏ i : Fin (2 * m), g i.castSucc.castSucc) =
            ∏ t : Fin m, (f ⟨2 * t.1, by omega⟩ * f ⟨2 * t.1 + 1, by omega⟩) := by
          rw [ih]
          refine Finset.prod_congr rfl fun t _ => rfl
        rw [hprev, Fin.prod_univ_castSucc, mul_assoc]
        rfl
    have hcoe_prod : ∀ (k : ℕ) (g : Fin k → (ZMod 3)ˣ),
        ((∏ x : Fin k, g x : (ZMod 3)ˣ) : ZMod 3) = ∏ x : Fin k, (g x : ZMod 3) := by
      intro k g
      have hgen : ∀ (s : Finset (Fin k)),
          ((∏ x ∈ s, g x : (ZMod 3)ˣ) : ZMod 3) = ∏ x ∈ s, (g x : ZMod 3) := by
        intro s
        refine Finset.induction_on s rfl fun a s ha ih => ?_
        rw [Finset.prod_insert ha, Finset.prod_insert ha, Units.val_mul, ih]
      exact hgen Finset.univ
    have hclosed_len : ∀ (m : ℕ) (x : α ⊕ β) (L : List (α ⊕ β)),
        L.length = m → isZMod3BipWalk x x L → zmod3WalkWeight x L = 1 := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        have hinl : ∀ (i₀ : α) (L : List (α ⊕ β)),
            L.length = m → isZMod3BipWalk (Sum.inl i₀) (Sum.inl i₀) L →
            zmod3WalkWeight (Sum.inl i₀) L = 1 := by
          intro i₀ L hlen hw
          by_cases hnodup : L.Nodup
          · by_cases hchord : ∃ P u Q v R,
                L = (P ++ u :: Q) ++ v :: R ∧ zmod3BipAdj u v ∧ Q ≠ [] ∧ ¬ (P = [] ∧ R = [])
            · rcases hchord with ⟨P, u, Q, v, R, rfl, huv, hQ_ne, hPR_ne⟩
              obtain ⟨hw1, hwR, hwt1⟩ := hwalk_split (P ++ u :: Q) v R (Sum.inl i₀) (Sum.inl i₀) hw
              have heq_app : (P ++ u :: Q) ++ [v] = P ++ u :: (Q ++ [v]) := by
                simp only [List.append_assoc, List.cons_append]
              obtain ⟨hwP, hwQ, hwt2⟩ := hwalk_split P u (Q ++ [v]) (Sum.inl i₀) v (heq_app ▸ hw1)
              have hvu : zmod3BipAdj v u := (hadj_symm u v).mp huv
              obtain ⟨hwC1, hwtC1⟩ := hwalk_append (Q ++ [v]) [u] u v u hwQ ⟨hvu, rfl⟩
              obtain ⟨hwRP, hwtRP⟩ := hwalk_append R (P ++ [u]) v (Sum.inl i₀) u hwR hwP
              obtain ⟨hwC2, hwtC2⟩ := hwalk_append (R ++ (P ++ [u])) [v] v u v hwRP ⟨huv, rfl⟩
              have hQ_pos : 0 < Q.length := List.length_pos_iff.mpr hQ_ne
              have hPR_pos : 0 < P.length + R.length := by
                by_contra h0
                apply hPR_ne
                exact ⟨List.eq_nil_of_length_eq_zero (by omega), List.eq_nil_of_length_eq_zero (by omega)⟩
              have hlenC1 : ((Q ++ [v]) ++ [u]).length < m := by
                simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
                omega
              have hlenC2 : ((R ++ (P ++ [u])) ++ [v]).length < m := by
                simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
                omega
              have h1_C1 := ih _ hlenC1 u ((Q ++ [v]) ++ [u]) rfl hwC1
              have h1_C2 := ih _ hlenC2 v ((R ++ (P ++ [u])) ++ [v]) rfl hwC2
              rw [hwtC1] at h1_C1
              rw [hwtC2, hwtRP] at h1_C2
              simp only [hwt_cons, hwt_nil, mul_one, hew_symm v u] at h1_C1 h1_C2
              have halg : ∀ wP wQ wR e : (ZMod 3)ˣ,
                  e * e = 1 → wQ * e = 1 → (wR * wP) * e = 1 → (wP * wQ) * wR = 1 := by
                intro wP wQ wR e he h1 h2
                calc (wP * wQ) * wR
                    = ((wP * wQ) * wR) * (e * e) := by rw [he, mul_one]
                  _ = (wQ * e) * ((wR * wP) * e) := by
                      simp only [mul_left_comm, mul_comm]
                  _ = 1 * 1 := by rw [h1, h2]
                  _ = 1 := mul_one 1
              rw [hwt1, heq_app, hwt2]
              exact halg _ _ _ (zmod3BipWeight u v) (hunit_sq _) h1_C1 h1_C2
            · have heven : Even L.length := by
                by_contra hodd
                have h := (hwalk_parity L (Sum.inl i₀) (Sum.inl i₀) hw).2 hodd
                simp at h
              obtain ⟨k, hk_add⟩ := heven
              have hk_len : L.length = 2 * k := by omega
              rcases k with _ | ⟨_ | k_pred⟩
              · have hnil : L = [] := List.eq_nil_of_length_eq_zero (by omega)
                subst hnil; rfl
              · rcases L with _ | ⟨y, _ | ⟨z, _ | _⟩⟩ <;> try (simp at hk_len)
                rcases hw with ⟨hxy, hzy, hlast_eq⟩
                change z = Sum.inl i₀ at hlast_eq
                subst hlast_eq
                simp only [hwt_cons, hwt_nil, mul_one, hew_symm y (Sum.inl i₀)]
                exact hunit_sq _
              · set k := k_pred + 2
                have hk2 : 2 ≤ k := by omega
                have hget_congr : ∀ (a b : ℕ) (ha : a < (Sum.inl i₀ :: L).length)
                    (hb : b < (Sum.inl i₀ :: L).length),
                    a = b → (Sum.inl i₀ :: L)[a]'ha = (Sum.inl i₀ :: L)[b]'hb := by
                  rintro a _ ha hb rfl; rfl
                have hL_congr : ∀ (a b : ℕ) (ha : a < L.length) (hb : b < L.length),
                    a = b → L[a]'ha = L[b]'hb := by
                  rintro a _ ha hb rfl; rfl
                have hV_parity : ∀ (s : ℕ) (hs : s < (Sum.inl i₀ :: L).length),
                    (s % 2 = 0 → Sum.isLeft ((Sum.inl i₀ :: L)[s]'hs) = true) ∧
                    (s % 2 = 1 → Sum.isLeft ((Sum.inl i₀ :: L)[s]'hs) = false) := by
                  intro s
                  induction s with
                  | zero =>
                    intro _
                    exact ⟨fun _ => rfl, fun h => by omega⟩
                  | succ s' ihs =>
                    intro hs
                    have hs_L : s' < L.length := Nat.lt_of_succ_lt_succ hs
                    have hflip := hadj_flip _ _ (hwalk_step_adj L (Sum.inl i₀) (Sum.inl i₀) hw s' hs_L)
                    obtain ⟨he0, he1⟩ := ihs (Nat.lt_succ_of_lt hs_L)
                    refine ⟨fun hmod0 => ?_, fun hmod1 => ?_⟩
                    · have hprev := he1 (by omega)
                      rw [hprev] at hflip
                      cases hcur : Sum.isLeft ((Sum.inl i₀ :: L)[s' + 1]'hs)
                      · rw [hcur] at hflip; cases hflip
                      · rfl
                    · have hprev := he0 (by omega)
                      rw [hprev] at hflip
                      cases hcur : Sum.isLeft ((Sum.inl i₀ :: L)[s' + 1]'hs)
                      · rfl
                      · rw [hcur] at hflip; cases hflip
                have hex_r : ∀ t : Fin k, ∃ a : α,
                    (Sum.inl i₀ :: L)[2 * t.1]'(by simp only [List.length_cons, hk_len]; omega) = Sum.inl a := by
                  intro t
                  have hp := (hV_parity (2 * t.1) (by simp only [List.length_cons, hk_len]; omega)).1 (by omega)
                  rcases h : (Sum.inl i₀ :: L)[2 * t.1]'(by simp only [List.length_cons, hk_len]; omega) with a | b
                  · exact ⟨a, rfl⟩
                  · rw [h] at hp; simp at hp
                choose r hr using hex_r
                have hex_c : ∀ t : Fin k, ∃ b : β,
                    (Sum.inl i₀ :: L)[2 * t.1 + 1]'(by simp only [List.length_cons, hk_len]; omega) = Sum.inr b := by
                  intro t
                  have hp := (hV_parity (2 * t.1 + 1) (by simp only [List.length_cons, hk_len]; omega)).2 (by omega)
                  rcases h : (Sum.inl i₀ :: L)[2 * t.1 + 1]'(by simp only [List.length_cons, hk_len]; omega) with a | b
                  · rw [h] at hp; simp at hp
                  · exact ⟨b, rfl⟩
                choose c hc using hex_c
                let π_cyc : Equiv.Perm (Fin k) :=
                  { toFun := fun j => ⟨(j.1 + 1) % k, Nat.mod_lt _ (by omega)⟩
                    invFun := fun j => ⟨(j.1 + k - 1) % k, Nat.mod_lt _ (by omega)⟩
                    left_inv := fun j => by
                      ext; dsimp
                      by_cases hj : j.1 + 1 < k
                      · rw [Nat.mod_eq_of_lt hj, show j.1 + 1 + k - 1 = j.1 + k by omega,
                            Nat.add_mod_right, Nat.mod_eq_of_lt j.2]
                      · have hjk : j.1 + 1 = k := by omega
                        have hm1 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
                        rw [hjk, Nat.mod_self, zero_add, hm1]
                        omega
                    right_inv := fun j => by
                      ext; dsimp
                      by_cases hj0 : j.1 = 0
                      · have hm1 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
                        rw [hj0, zero_add, hm1, show k - 1 + 1 = k by omega, Nat.mod_self]
                      · have hm2 : (j.1 - 1) % k = j.1 - 1 := Nat.mod_eq_of_lt (by omega)
                        rw [show j.1 + k - 1 = (j.1 - 1) + k by omega, Nat.add_mod_right,
                            hm2, show j.1 - 1 + 1 = j.1 by omega, Nat.mod_eq_of_lt j.2] }
                have h1_ne_cyc : (1 : Equiv.Perm (Fin k)) ≠ π_cyc := by
                  intro heq
                  have h0 := congrArg (fun σ : Equiv.Perm (Fin k) => (σ ⟨0, by omega⟩).1) heq
                  dsimp [π_cyc] at h0
                  have hm1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
                  rw [hm1] at h0
                  omega
                have hL_ne : L ≠ [] := by intro h; simp [h] at hk_len; omega
                have hr0 : Sum.inl i₀ = Sum.inl (r ⟨0, by omega⟩) := hr ⟨0, by omega⟩
                have hr_succ : ∀ t : Fin k,
                    (Sum.inl i₀ :: L)[2 * t.1 + 2]'(by simp only [List.length_cons, hk_len]; omega) =
                    Sum.inl (r (π_cyc t)) := by
                  intro t
                  by_cases ht : t.1 + 1 < k
                  · have hmod : (π_cyc t).1 = t.1 + 1 := Nat.mod_eq_of_lt ht
                    rw [hget_congr (2 * t.1 + 2) (2 * (π_cyc t).1) _
                        (by simp only [List.length_cons, hk_len]; omega) (by omega)]
                    exact hr (π_cyc t)
                  · have htk : t.1 + 1 = k := by omega
                    have hcyc0 : π_cyc t = ⟨0, by omega⟩ := by
                      ext; change (t.1 + 1) % k = 0; rw [htk, Nat.mod_self]
                    have hlast := hwalk_getLast L (Sum.inl i₀) (Sum.inl i₀) hL_ne hw
                    change L[2 * t.1 + 1]'(by omega) = Sum.inl (r (π_cyc t))
                    rw [hL_congr (2 * t.1 + 1) (L.length - 1) (by omega) (by omega) (by omega),
                        hlast, hr0, hcyc0]
                have hA_diag : ∀ t : Fin k, A (r t) (c t) ≠ 0 := by
                  intro t
                  have hadj := hwalk_step_adj L (Sum.inl i₀) (Sum.inl i₀) hw (2 * t.1) (by omega)
                  rw [hr t, hc t] at hadj
                  exact hadj
                have hA_nxt : ∀ t : Fin k, A (r (π_cyc t)) (c t) ≠ 0 := by
                  intro t
                  have hadj := hwalk_step_adj L (Sum.inl i₀) (Sum.inl i₀) hw (2 * t.1 + 1) (by omega)
                  rw [hc t, hr_succ t] at hadj
                  exact hadj
                have hwt_formula : zmod3WalkWeight (Sum.inl i₀) L =
                    ∏ t : Fin k, (zmod3UnitRatio (r t) (c t) * zmod3UnitRatio (r (π_cyc t)) (c t)) := by
                  rw [hwalk_wt_prod]
                  let f : Fin (2 * k) → (ZMod 3)ˣ := fun s =>
                    zmod3BipWeight
                      ((Sum.inl i₀ :: L)[s.1]'(by simp only [List.length_cons, hk_len]; omega))
                      ((Sum.inl i₀ :: L)[s.1 + 1]'(by simp only [List.length_cons, hk_len]; omega))
                  have hreindex : (∏ s : Fin L.length,
                      zmod3BipWeight ((Sum.inl i₀ :: L)[s.1]'(Nat.lt_succ_of_lt s.2))
                        ((Sum.inl i₀ :: L)[s.1 + 1]'(Nat.succ_lt_succ s.2))) =
                      ∏ s : Fin (2 * k), f s :=
                    Fintype.prod_equiv (finCongr hk_len) _ _ (fun _ => rfl)
                  rw [hreindex, hprod_even_pairs k f]
                  refine Finset.prod_congr rfl fun t _ => ?_
                  have hf0 : f ⟨2 * t.1, by omega⟩ = zmod3UnitRatio (r t) (c t) := by
                    dsimp only [f]
                    rw [hr t, hc t]
                  have hf1 : f ⟨2 * t.1 + 1, by omega⟩ = zmod3UnitRatio (r (π_cyc t)) (c t) := by
                    dsimp only [f]
                    rw [hc t, hr_succ t]
                  rw [hf0, hf1]
                have hsparse : ∀ i j : Fin k, A (r i) (c j) ≠ 0 → i = j ∨ i = π_cyc j := by
                  intro i j hAij
                  let qi : ℕ := if i.1 = 0 then 2 * k - 1 else 2 * i.1 - 1
                  have hqi_lt : qi < L.length := by dsimp [qi]; split_ifs <;> omega
                  have hqi_odd : qi % 2 = 1 := by dsimp [qi]; split_ifs <;> omega
                  have hL_qi : L[qi]'hqi_lt = Sum.inl (r i) := by
                    by_cases hi0 : i.1 = 0
                    · have hqi_eq : qi = L.length - 1 := by dsimp [qi]; rw [if_pos hi0]; omega
                      have hi_zero : i = ⟨0, by omega⟩ := Fin.ext hi0
                      rw [hL_congr qi (L.length - 1) hqi_lt (by omega) hqi_eq,
                          hwalk_getLast L (Sum.inl i₀) (Sum.inl i₀) hL_ne hw, hr0, ← hi_zero]
                    · have hqi_eq : qi + 1 = 2 * i.1 := by dsimp [qi]; rw [if_neg hi0]; omega
                      change (Sum.inl i₀ :: L)[qi + 1]'(Nat.succ_lt_succ hqi_lt) = Sum.inl (r i)
                      rw [hget_congr (qi + 1) (2 * i.1) _
                          (by simp only [List.length_cons, hk_len]; omega) hqi_eq]
                      exact hr i
                  have h2j_lt : 2 * j.1 < L.length := by omega
                  have hL_2j : L[2 * j.1]'h2j_lt = Sum.inr (c j) := hc j
                  have hadj_ij : zmod3BipAdj (L[qi]'hqi_lt) (L[2 * j.1]'h2j_lt) := by
                    rw [hL_qi, hL_2j]; exact hAij
                  let a : ℕ := min qi (2 * j.1)
                  let b : ℕ := max qi (2 * j.1)
                  have hab : a < b := by dsimp [a, b]; omega
                  have hb_lt : b < L.length := by dsimp [b]; omega
                  have hadj_ab : zmod3BipAdj (L[a]'(Nat.lt_trans hab hb_lt)) (L[b]'hb_lt) := by
                    by_cases hle : qi ≤ 2 * j.1
                    · rw [hL_congr a qi _ hqi_lt (by dsimp [a]; omega),
                          hL_congr b (2 * j.1) hb_lt h2j_lt (by dsimp [b]; omega)]
                      exact hadj_ij
                    · rw [hL_congr a (2 * j.1) _ h2j_lt (by dsimp [a]; omega),
                          hL_congr b qi hb_lt hqi_lt (by dsimp [b]; omega)]
                      exact (hadj_symm _ _).mp hadj_ij
                  have hclose : b - a ≤ 1 ∨ (a = 0 ∧ b = 2 * k - 1) := by
                    by_contra hgap
                    apply hchord
                    have hsp1 := hlist_split_one L b hb_lt
                    have htake_len : (L.take b).length = b := List.length_take_of_le (Nat.le_of_lt hb_lt)
                    have ha_take : a < (L.take b).length := by omega
                    have hsp2 := hlist_split_one (L.take b) a ha_take
                    refine ⟨(L.take b).take a, (L.take b)[a]'ha_take,
                      (L.take b).drop (a + 1), L[b]'hb_lt, L.drop (b + 1), ?_, ?_, ?_, ?_⟩
                    · exact (hsp1.trans (congrArg (· ++ L[b]'hb_lt :: L.drop (b + 1)) hsp2)).trans
                        (by simp only [List.append_assoc, List.cons_append])
                    · rw [List.getElem_take]
                      exact hadj_ab
                    · intro hQ0
                      have hQl : ((L.take b).drop (a + 1)).length = 0 := by rw [hQ0]; rfl
                      simp only [List.length_drop, htake_len] at hQl
                      omega
                    · rintro ⟨hP0, hR0⟩
                      have hPl : ((L.take b).take a).length = 0 := by rw [hP0]; rfl
                      have hRl : (L.drop (b + 1)).length = 0 := by rw [hR0]; rfl
                      rw [List.length_take_of_le (by rw [htake_len]; omega)] at hPl
                      rw [List.length_drop] at hRl
                      omega
                  by_cases hi0 : i.1 = 0
                  · have hqi_val : qi = 2 * k - 1 := by dsimp [qi]; rw [if_pos hi0]
                    have ha_val : a = 2 * j.1 := by dsimp [a]; omega
                    have hb_val : b = 2 * k - 1 := by dsimp [b]; omega
                    rcases hclose with hle1 | ⟨ha0, _⟩
                    · right
                      have hj_last : j.1 + 1 = k := by omega
                      ext
                      change i.1 = (j.1 + 1) % k
                      rw [hi0, hj_last, Nat.mod_self]
                    · left
                      ext; omega
                  · have hqi_val : qi = 2 * i.1 - 1 := by dsimp [qi]; rw [if_neg hi0]
                    have hb_lt_last : b < 2 * k - 1 := by dsimp [b]; omega
                    rcases hclose with hle1 | ⟨_, hb_last⟩
                    · have hij : i.1 = j.1 ∨ i.1 = j.1 + 1 := by dsimp [a, b] at hle1; omega
                      rcases hij with heq | hsucc
                      · left; exact Fin.ext heq
                      · right
                        ext
                        change i.1 = (j.1 + 1) % k
                        rw [← hsucc, Nat.mod_eq_of_lt i.2]
                    · omega
                have hperm_char : ∀ π : Equiv.Perm (Fin k),
                    (∀ j : Fin k, π j = j ∨ π j = π_cyc j) → π = 1 ∨ π = π_cyc := by
                  intro π hπ
                  rcases hπ ⟨0, by omega⟩ with h0 | h0
                  · left
                    have hdown : ∀ (d : ℕ) (hd : d < k),
                        π ⟨k - 1 - d, by omega⟩ = ⟨k - 1 - d, by omega⟩ := by
                      intro d
                      induction d with
                      | zero =>
                        intro _
                        rcases hπ ⟨k - 1, by omega⟩ with hfix | hsh
                        · simpa using hfix
                        · have hcyc_last : π_cyc ⟨k - 1, by omega⟩ = ⟨0, by omega⟩ := by
                            ext; dsimp [π_cyc]
                            rw [show k - 1 + 1 = k by omega, Nat.mod_self]
                          rw [hcyc_last, ← h0] at hsh
                          have hinj := π.injective hsh
                          have hval := congrArg Fin.val hinj
                          dsimp at hval; omega
                      | succ d' ihd =>
                        intro hd
                        have hprev := ihd (by omega)
                        rcases hπ ⟨k - 1 - (d' + 1), by omega⟩ with hfix | hsh
                        · exact hfix
                        · have hcyc_eq : π_cyc ⟨k - 1 - (d' + 1), by omega⟩ = ⟨k - 1 - d', by omega⟩ := by
                            ext; dsimp [π_cyc]
                            have hm_lt : (k - 1 - (d' + 1) + 1) % k = k - 1 - (d' + 1) + 1 :=
                              Nat.mod_eq_of_lt (by omega)
                            rw [hm_lt]
                            omega
                          have hinj := π.injective ((hsh.trans hcyc_eq).trans hprev.symm)
                          have hval := congrArg Fin.val hinj
                          dsimp at hval; omega
                    ext j
                    have hj := hdown (k - 1 - j.1) (by omega)
                    have hidx : (⟨k - 1 - (k - 1 - j.1), by omega⟩ : Fin k) = j := by ext; dsimp; omega
                    rw [hidx] at hj
                    exact congrArg Fin.val hj
                  · right
                    have hup : ∀ (d : ℕ) (hd : d < k), π ⟨d, hd⟩ = π_cyc ⟨d, hd⟩ := by
                      intro d
                      induction d with
                      | zero => intro _; exact h0
                      | succ d' ihd =>
                        intro hd
                        have hprev := ihd (by omega)
                        have hcyc_prev : π_cyc ⟨d', by omega⟩ = ⟨d' + 1, hd⟩ := by
                          ext; dsimp [π_cyc]; rw [Nat.mod_eq_of_lt hd]
                        rw [hcyc_prev] at hprev
                        rcases hπ ⟨d' + 1, hd⟩ with hfix | hsh
                        · have hinj := π.injective (hfix.trans hprev.symm)
                          have hval := congrArg Fin.val hinj
                          dsimp at hval; omega
                        · exact hsh
                    ext j
                    exact congrArg Fin.val (hup j.1 j.2)
                have hdet_two : ∀ (M : Matrix (Fin k) (Fin k) (ZMod 3)),
                    (∀ i j : Fin k, M i j ≠ 0 → i = j ∨ i = π_cyc j) →
                    M.det = (∏ j : Fin k, M j j) + Equiv.Perm.sign π_cyc • (∏ j : Fin k, M (π_cyc j) j) := by
                  intro M hM_sp
                  rw [Matrix.det_apply]
                  have hsub : (∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ • ∏ j : Fin k, M (σ j) j) =
                      ∑ σ ∈ ({1, π_cyc} : Finset (Equiv.Perm (Fin k))),
                        Equiv.Perm.sign σ • ∏ j : Fin k, M (σ j) j := by
                    symm
                    refine Finset.sum_subset (Finset.subset_univ _) fun σ _ hnot => ?_
                    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
                    have hnall : ¬ ∀ j : Fin k, σ j = j ∨ σ j = π_cyc j :=
                      fun hall => (hperm_char σ hall).elim hnot.1 hnot.2
                    push_neg at hnall
                    obtain ⟨j, hj1, hj2⟩ := hnall
                    have hM0 : M (σ j) j = 0 := by
                      by_contra hne
                      exact (hM_sp (σ j) j hne).elim hj1 hj2
                    have hp0 : (∏ i : Fin k, M (σ i) i) = 0 :=
                      Finset.prod_eq_zero (Finset.mem_univ j) hM0
                    rw [hp0, smul_zero]
                  rw [hsub, Finset.sum_pair h1_ne_cyc, Equiv.Perm.sign_one, one_smul]
                  rfl
                have hdetB := hdet_two (A.submatrix r c) (fun i j h => hsparse i j h)
                have hdetB' := hdet_two (A'.submatrix r c) (fun i j h =>
                  hsparse i j (fun h0 => h ((hzero (r i) (c j)).mp h0)))
                let p1 : ZMod 3 := ∏ j : Fin k, A (r j) (c j)
                let p2 : ZMod 3 := ∏ j : Fin k, A (r (π_cyc j)) (c j)
                let q1 : ZMod 3 := ∏ j : Fin k, A' (r j) (c j)
                let q2 : ZMod 3 := ∏ j : Fin k, A' (r (π_cyc j)) (c j)
                have hp1 : p1 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hA_diag j
                have hp2 : p2 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hA_nxt j
                have hq1 : q1 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ =>
                  fun h0 => hA_diag j ((hzero _ _).mpr h0)
                have hq2 : q2 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ =>
                  fun h0 => hA_nxt j ((hzero _ _).mpr h0)
                have hiff_det := hdet k r c
                rw [hdetB, hdetB'] at hiff_det
                change p1 + Equiv.Perm.sign π_cyc • p2 = 0 ↔ q1 + Equiv.Perm.sign π_cyc • q2 = 0 at hiff_det
                have hprod_one : (q1 * p1) * (q2 * p2) = 1 := by
                  rcases Int.units_eq_one_or (Equiv.Perm.sign π_cyc) with hsign | hsign
                  · rw [hsign, one_smul, one_smul] at hiff_det
                    have hiff1 : p1 + 1 * p2 = 0 ↔ q1 + 1 * q2 = 0 := by
                      simpa only [one_mul] using hiff_det
                    exact hz3_det_pair p1 p2 q1 q2 1 hp1 hp2 hq1 hq2 (mul_one 1) hiff1
                  · rw [hsign, Units.smul_def, Units.smul_def, Units.val_neg, Units.val_one,
                        neg_one_zsmul, neg_one_zsmul] at hiff_det
                    have hiff1 : p1 + (-1 : ZMod 3) * p2 = 0 ↔ q1 + (-1 : ZMod 3) * q2 = 0 := by
                      simpa only [neg_one_mul] using hiff_det
                    exact hz3_det_pair p1 p2 q1 q2 (-1) hp1 hp2 hq1 hq2 (by ring) hiff1
                apply Units.ext
                rw [hwt_formula, hcoe_prod k]
                have hterm : ∀ t : Fin k,
                    ((zmod3UnitRatio (r t) (c t) * zmod3UnitRatio (r (π_cyc t)) (c t) : (ZMod 3)ˣ) : ZMod 3) =
                    (A' (r t) (c t) * A (r t) (c t)) * (A' (r (π_cyc t)) (c t) * A (r (π_cyc t)) (c t)) := by
                  intro t
                  rw [Units.val_mul, huR_val _ _ (hA_diag t), huR_val _ _ (hA_nxt t)]
                have hprod_eq : (∏ t : Fin k,
                    ((zmod3UnitRatio (r t) (c t) * zmod3UnitRatio (r (π_cyc t)) (c t) : (ZMod 3)ˣ) : ZMod 3)) =
                    (q1 * p1) * (q2 * p2) := by
                  calc (∏ t : Fin k, _)
                      = ∏ t : Fin k, ((A' (r t) (c t) * A (r t) (c t)) *
                          (A' (r (π_cyc t)) (c t) * A (r (π_cyc t)) (c t))) :=
                          Finset.prod_congr rfl fun t _ => hterm t
                    _ = (∏ t : Fin k, (A' (r t) (c t) * A (r t) (c t))) *
                        (∏ t : Fin k, (A' (r (π_cyc t)) (c t) * A (r (π_cyc t)) (c t))) :=
                          Finset.prod_mul_distrib
                    _ = (q1 * p1) * (q2 * p2) := by
                          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
                rw [hprod_eq, hprod_one, Units.val_one]
          · obtain ⟨P, u, Q, R, rfl⟩ := hnot_nodup L hnodup
            obtain ⟨hw1, hwR, hwt1⟩ := hwalk_split (P ++ u :: Q) u R (Sum.inl i₀) (Sum.inl i₀) hw
            have heq_app : (P ++ u :: Q) ++ [u] = P ++ u :: (Q ++ [u]) := by
              simp only [List.append_assoc, List.cons_append]
            obtain ⟨hwP, hwQ, hwt2⟩ := hwalk_split P u (Q ++ [u]) (Sum.inl i₀) u (heq_app ▸ hw1)
            obtain ⟨hwRP, hwtRP⟩ := hwalk_append R (P ++ [u]) u (Sum.inl i₀) u hwR hwP
            have hlenQ : (Q ++ [u]).length < m := by
              simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
              omega
            have hlenRP : (R ++ (P ++ [u])).length < m := by
              simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
              omega
            have h1_Q := ih _ hlenQ u (Q ++ [u]) rfl hwQ
            have h1_RP := ih _ hlenRP u (R ++ (P ++ [u])) rfl hwRP
            rw [hwtRP] at h1_RP
            rw [hwt1, heq_app, hwt2, h1_Q, mul_one, mul_comm, h1_RP]
        rintro (i₀ | j₀) L hlen hw
        · exact hinl i₀ L hlen hw
        · cases L with
          | nil => rfl
          | cons y L' =>
            rcases hw with ⟨hadj0, hw'⟩
            rcases y with i₀ | j₁
            · have hback : isZMod3BipWalk (Sum.inr j₀) (Sum.inl i₀) [Sum.inl i₀] := ⟨hadj0, rfl⟩
              obtain ⟨hw_rot, hwt_rot⟩ := hwalk_append L' [Sum.inl i₀] (Sum.inl i₀) (Sum.inr j₀) (Sum.inl i₀) hw' hback
              have hlen_rot : (L' ++ [Sum.inl i₀]).length = m := by
                simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
                omega
              have h1 := hinl i₀ (L' ++ [Sum.inl i₀]) hlen_rot hw_rot
              have hwt_eq : zmod3WalkWeight (Sum.inr j₀) (Sum.inl i₀ :: L') =
                  zmod3WalkWeight (Sum.inl i₀) (L' ++ [Sum.inl i₀]) := by
                rw [hwt_rot]
                simp only [hwt_cons, hwt_nil, one_mul, mul_comm]
              exact hwt_eq.trans h1
            · exact False.elim hadj0
    have hpath_indep : ∀ x y L₁ L₂,
        isZMod3BipWalk x y L₁ → isZMod3BipWalk x y L₂ →
        zmod3WalkWeight x L₁ = zmod3WalkWeight x L₂ := by
      intro x y L₁ L₂ hw1 hw2
      obtain ⟨L₂', hw2', hwt2'⟩ := hwalk_rev L₂ x y hw2
      obtain ⟨hw_cl, hwt_cl⟩ := hwalk_append L₁ L₂' x y x hw1 hw2'
      have h1 := hclosed_len _ x (L₁ ++ L₂') rfl hw_cl
      rw [hwt_cl, hwt2'] at h1
      calc zmod3WalkWeight x L₁
          = zmod3WalkWeight x L₁ * (zmod3WalkWeight x L₂ * zmod3WalkWeight x L₂) := by
            rw [hunit_sq, mul_one]
        _ = (zmod3WalkWeight x L₁ * zmod3WalkWeight x L₂) * zmod3WalkWeight x L₂ := by
            rw [mul_assoc]
        _ = 1 * zmod3WalkWeight x L₂ := by rw [h1]
        _ = zmod3WalkWeight x L₂ := one_mul _
    have hchoose_congr : ∀ (p q : (α ⊕ β) → Prop) (hp : ∃ z, p z) (hq : ∃ z, q z),
        p = q → Classical.choose hp = Classical.choose hq := by
      intro p q hp hq hpq
      subst hpq
      rfl
    let Comp : (α ⊕ β) → (α ⊕ β) → Prop := fun x z => ∃ L, isZMod3BipWalk z x L
    have hComp_ne : ∀ x : α ⊕ β, ∃ z, Comp x z := fun x => ⟨x, [], rfl⟩
    let rep : (α ⊕ β) → α ⊕ β := fun x => Classical.choose (hComp_ne x)
    have hrep_spec : ∀ x : α ⊕ β, ∃ L, isZMod3BipWalk (rep x) x L :=
      fun x => Classical.choose_spec (hComp_ne x)
    let pot : (α ⊕ β) → (ZMod 3)ˣ :=
      fun x => zmod3WalkWeight (rep x) (Classical.choose (hrep_spec x))
    have hpot_adj : ∀ x y, zmod3BipAdj x y → pot x * pot y = zmod3BipWeight x y := by
      intro x y hadj
      have hC : Comp x = Comp y := by
        funext z
        apply propext
        constructor
        · rintro ⟨L, hL⟩
          exact ⟨L ++ [y], (hwalk_append L [y] z x y hL ⟨hadj, rfl⟩).1⟩
        · rintro ⟨L, hL⟩
          exact ⟨L ++ [x], (hwalk_append L [x] z y x hL ⟨(hadj_symm x y).mp hadj, rfl⟩).1⟩
      have hrep_eq : rep x = rep y := hchoose_congr (Comp x) (Comp y) (hComp_ne x) (hComp_ne y) hC
      set Lx := Classical.choose (hrep_spec x)
      have hwLx : isZMod3BipWalk (rep x) x Lx := Classical.choose_spec (hrep_spec x)
      set Ly := Classical.choose (hrep_spec y)
      have hwLy : isZMod3BipWalk (rep y) y Ly := Classical.choose_spec (hrep_spec y)
      have hwLy' : isZMod3BipWalk (rep x) y Ly := hrep_eq.symm ▸ hwLy
      have hpot_y : pot y = zmod3WalkWeight (rep x) Ly := by
        dsimp only [pot]
        rw [hrep_eq]
      obtain ⟨hwLxy, hwtLxy⟩ := hwalk_append Lx [y] (rep x) x y hwLx ⟨hadj, rfl⟩
      have heq_wt := hpath_indep (rep x) y Ly (Lx ++ [y]) hwLy' hwLxy
      rw [← hpot_y, hwtLxy] at heq_wt
      simp only [hwt_cons, hwt_nil, mul_one] at heq_wt
      change pot y = pot x * zmod3BipWeight x y at heq_wt
      calc pot x * pot y
          = pot x * (pot x * zmod3BipWeight x y) := by rw [heq_wt]
        _ = (pot x * pot x) * zmod3BipWeight x y := by rw [mul_assoc]
        _ = zmod3BipWeight x y := by rw [hunit_sq, one_mul]
    refine ⟨fun i => pot (Sum.inl i), fun j => pot (Sum.inr j), fun i j => ?_⟩
    by_cases hA0 : A i j = 0
    · rw [hA0, (hzero i j).mp hA0, mul_zero]
    · have hadj : zmod3BipAdj (Sum.inl i) (Sum.inr j) := hA0
      have hp := hpot_adj (Sum.inl i) (Sum.inr j) hadj
      have hp_val : ((pot (Sum.inl i) : ZMod 3) * (pot (Sum.inr j) : ZMod 3)) =
          A' i j * A i j := by
        rw [← Units.val_mul, hp]
        exact huR_val i j hA0
      calc A' i j
          = A' i j * (A i j * A i j) := by rw [hz3_sq (A i j) hA0, mul_one]
        _ = (A' i j * A i j) * A i j := by ring
        _ = (pot (Sum.inl i) : ZMod 3) * (pot (Sum.inr j) : ZMod 3) * A i j := by rw [hp_val]
  have h_part3 :
      ∀ (n d d' : ℕ) (T : Finset (Fin n))
        (u : Fin n → (Fin d → ZMod 3)) (u' : Fin n → (Fin d' → ZMod 3))
        (β : ℝ) (μ : Finset (Fin n) → ℝ),
      0 ≤ β →
      (∀ X ⊆ T,
        LinearIndependent (ZMod 3) (fun g : X => u g.1) ↔
        LinearIndependent (ZMod 3) (fun g : X => u' g.1)) →
      IsSubspaceBetaBounded u T β μ →
      IsSubspaceBetaBounded u' T β μ := by
    clear h_dim_compress h_part2
    intro n d d' T u u' β μ hβ0 hindep hbound
    obtain ⟨D, _, bV, bV', hbV, hbV', hdet⟩ :=
      h_common_basis (ZMod 3) n d d' T u u' hindep
    obtain ⟨σ, τ, hscale⟩ := h_zmod3_scale
      D {g : Fin n // g ∈ T \ D}
      (Matrix.of (fun (b : D) (g : {g : Fin n // g ∈ T \ D}) =>
        bV.repr ⟨u g.1, Submodule.subset_span ⟨g.1, (Finset.mem_sdiff.mp g.2).1, rfl⟩⟩ b))
      (Matrix.of (fun (b : D) (g : {g : Fin n // g ∈ T \ D}) =>
        bV'.repr ⟨u' g.1, Submodule.subset_span ⟨g.1, (Finset.mem_sdiff.mp g.2).1, rfl⟩⟩ b))
      hdet
    let V := matroidSpan u T
    let V' := matroidSpan u' T
    obtain ⟨φ, hφ_bV⟩ : ∃ φ : V ≃ₗ[ZMod 3] V', ∀ b : D, φ (bV b) = (σ b : ZMod 3) • bV' b :=
      ⟨bV.equiv (bV'.unitsSMul σ) (Equiv.refl D), fun b => by
        have h1 := bV.equiv_apply b (bV'.unitsSMul σ) (Equiv.refl D)
        have h2 : (bV'.unitsSMul σ) b = (σ b : ZMod 3) • bV' b := by
          rw [bV'.unitsSMul_apply b, Units.smul_def]
        exact h1.trans h2⟩
    have hφ_proj : ∀ (g : Fin n) (hg : g ∈ T), ∃ c : ZMod 3, c ≠ 0 ∧
        (φ ⟨u g, Submodule.subset_span ⟨g, hg, rfl⟩⟩ : Fin d' → ZMod 3) = c • u' g := by
      intro g hg
      by_cases hgD : g ∈ D
      · refine ⟨(σ ⟨g, hgD⟩ : ZMod 3), (σ ⟨g, hgD⟩).ne_zero, ?_⟩
        have hug_eq : (⟨u g, Submodule.subset_span ⟨g, hg, rfl⟩⟩ : V) = bV ⟨g, hgD⟩ :=
          Subtype.ext (hbV ⟨g, hgD⟩).symm
        rw [hug_eq, hφ_bV ⟨g, hgD⟩]
        change (σ ⟨g, hgD⟩ : ZMod 3) • (bV' ⟨g, hgD⟩ : Fin d' → ZMod 3) = (σ ⟨g, hgD⟩ : ZMod 3) • u' g
        rw [hbV' ⟨g, hgD⟩]
      · let g' : {x : Fin n // x ∈ T \ D} := ⟨g, Finset.mem_sdiff.mpr ⟨hg, hgD⟩⟩
        let c : ZMod 3 := (((τ g')⁻¹ : (ZMod 3)ˣ) : ZMod 3)
        refine ⟨c, ((τ g')⁻¹).ne_zero, ?_⟩
        let ug : V := ⟨u g, Submodule.subset_span ⟨g, hg, rfl⟩⟩
        let u'g : V' := ⟨u' g, Submodule.subset_span ⟨g, hg, rfl⟩⟩
        have hinv : c * (τ g' : ZMod 3) = 1 := by
          dsimp only [c]
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        have hcoeff : ∀ b : D, bV.repr ug b * (σ b : ZMod 3) = c * bV'.repr u'g b := by
          intro b
          have hs : bV'.repr u'g b = (σ b : ZMod 3) * (τ g' : ZMod 3) * bV.repr ug b := hscale b g'
          calc bV.repr ug b * (σ b : ZMod 3)
              = (c * (τ g' : ZMod 3)) * ((σ b : ZMod 3) * bV.repr ug b) := by
                rw [hinv]; ring
            _ = c * ((σ b : ZMod 3) * (τ g' : ZMod 3) * bV.repr ug b) := by ring
            _ = c * bV'.repr u'g b := by rw [← hs]
        have hsum_u : ∑ b : D, bV.repr ug b • bV b = ug := bV.sum_repr ug
        have hsum_u' : ∑ b : D, bV'.repr u'g b • bV' b = u'g := bV'.sum_repr u'g
        have hφ_ug : φ ug = c • u'g := by
          rw [← hsum_u, map_sum, ← hsum_u', Finset.smul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [map_smul, hφ_bV b, smul_smul, smul_smul, hcoeff b]
        exact congrArg Subtype.val hφ_ug
    exact h_proj_transfer (ZMod 3) n d d' T u u' β μ hβ0 hindep ⟨φ, hφ_proj⟩ hbound
  exact ⟨h_dim_compress, h_part2, h_part3⟩

theorem lem_markov_threshold_welfare (n m s : ℕ) (hn : 2 ≤ n) (hs1 : 1 ≤ s) (hsn : s < n)
    (F : Fin m → Type) (d : Fin m → ℕ)
    (rateRule :
      (prev : List (Fin n)) → (x : Fin n) → (bundles : Fin m → Finset (Fin n)) →
      (Fin m → {T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → WithBot ℝ) →
      ((i : Fin m) → {g : Fin n // g ∈ insert x prev.toFinset} → (Fin (d i) → F i)) →
      Option (Fin m × ℝ)) :
    ∃ alg : RepresentedOnlineWelfareAlg n m F d,
      ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ)
        (u : (i : Fin m) → Fin n → (Fin (d i) → F i)),
        let v := fun i => weightedMatroidVal (M i) (w i)
        (∃ (X : Finset (Fin n) → Fin m → Finset (Fin n))
           (μ : Fin m → Finset (Fin n) → Finset (Fin n) → ℝ)
           (q : Fin m → Finset (Fin n) → Fin n → Finset (Fin n) → ℝ),
          (∀ S : Finset (Fin n),
            IsAllocOf S (X S) ∧
            (∀ i : Fin m, (M i).Indep (X S i : Set (Fin n))) ∧
            optWelfareOn v S ≤ ∑ i : Fin m, ∑ g ∈ X S i, w i g) ∧
          (∀ i : Fin m,
            (∀ S : Finset (Fin n), S.card ≤ s → μ i S = fun A => if A = ∅ then 1 else 0) ∧
            (∀ S : Finset (Fin n),
              (∀ A, 0 ≤ μ i S A) ∧
              (∀ A, μ i S A ≠ 0 → A ⊆ S ∧ (M i).Indep (A : Set (Fin n))) ∧
              (∑ A : Finset (Fin n), μ i S A) = 1) ∧
            (∀ S : Finset (Fin n), s < S.card →
              (∀ g ∈ S, ∀ A, 0 ≤ q i S g A ∧ q i S g A ≤ μ i (S.erase g) A) ∧
              (∀ g A, q i S g A ≠ 0 →
                g ∈ S ∧ g ∈ X S i ∧ A ⊆ S.erase g ∧ (M i).Indep (insert g A : Set (Fin n))) ∧
              (∀ g ∈ X S i, ∑ A : Finset (Fin n), q i S g A =
                (s : ℝ) / ((S.card - 1 : ℕ) : ℝ)) ∧
              (∀ B : Finset (Fin n),
                μ i S B = (1 / (S.card : ℝ)) * ∑ g ∈ S,
                  (μ i (S.erase g) B +
                    (if g ∈ B then q i S g (B.erase g) else 0) -
                    q i S g B)))) ∧
          (∀ (prev : List (Fin n)) (x : Fin n) (bundles : Fin m → Finset (Fin n)),
            x ∉ prev.toFinset →
            let S := insert x prev.toFinset
            (S.card ≤ s ∨ (∀ j : Fin m, x ∉ X S j) →
              rateRule prev x bundles (fun i ⟨T, _⟩ => v i T) (fun i ⟨g, _⟩ => u i g) = none) ∧
            (∀ j : Fin m, s < S.card → x ∈ X S j →
              rateRule prev x bundles (fun i ⟨T, _⟩ => v i T) (fun i ⟨g, _⟩ => u i g) =
                some (j, if μ j (S.erase x) (bundles j) = 0 then 0
                         else q j S x (bundles j) / μ j (S.erase x) (bundles j))))) →
        (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
          let st := runDetRepresentedWelfareSteps (alg.det ω) v u π k hk
          IsAllocOf st.1.toFinset st.2 ∧
          ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
        (((secretaryCutoffConst n s * optWelfare v : ℝ) : WithBot ℝ) ≤
          expectedRepresentedWelfareVal alg v u) :=
by
  let unitMeas : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  haveI hUnitProb : IsProbabilityMeasure unitMeas :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; norm_num⟩
  let seedMeas : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => unitMeas)
  haveI hSeedProb : IsProbabilityMeasure seedMeas := inferInstance
  let detAlg : (Fin n → ℝ) → DetRepresentedWelfareAlg n m F d := fun ω =>
    { step := fun prev x bundles oracle vecOracle =>
        match rateRule prev x bundles oracle vecOracle with
        | none => none
        | some (j, r) => if 0 ≤ ω x ∧ ω x < r then some j else none }
  let alg : RepresentedOnlineWelfareAlg n m F d :=
    { Seed := Fin n → ℝ
      measSeed := inferInstance
      seedMeasure := seedMeas
      isProb := hSeedProb
      det := detAlg
      meas_step := by
        intro prev x bundles oracle vecOracle dec
        dsimp only [detAlg]
        cases hr : rateRule prev x bundles oracle vecOracle with
        | none =>
          cases dec with
          | none =>
            have heq : {ω : Fin n → ℝ | (none : Option (Fin m)) = none} = Set.univ := by ext; simp
            rw [heq]; exact MeasurableSet.univ
          | some i =>
            have heq : {ω : Fin n → ℝ | (none : Option (Fin m)) = some i} = ∅ := by ext; simp
            rw [heq]; exact MeasurableSet.empty
        | some jr =>
          rcases jr with ⟨j, r⟩
          have hIco : MeasurableSet ((fun ω : Fin n → ℝ => ω x) ⁻¹' Set.Ico 0 r) :=
            (measurable_pi_apply x) measurableSet_Ico
          cases dec with
          | none =>
            have heq : {ω : Fin n → ℝ |
                (if 0 ≤ ω x ∧ ω x < r then some j else none) = none} =
                ((fun ω : Fin n → ℝ => ω x) ⁻¹' Set.Ico 0 r)ᶜ := by
              ext ω; simp [Set.mem_Ico]
            rw [heq]; exact hIco.compl
          | some i =>
            by_cases hji : j = i
            · subst hji
              have heq : {ω : Fin n → ℝ |
                  (if 0 ≤ ω x ∧ ω x < r then some j else none) = some j} =
                  (fun ω : Fin n → ℝ => ω x) ⁻¹' Set.Ico 0 r := by
                ext ω; simp [Set.mem_Ico]
              rw [heq]; exact hIco
            · have heq : {ω : Fin n → ℝ |
                  (if 0 ≤ ω x ∧ ω x < r then some j else none) = some i} = ∅ := by
                ext ω; simp [hji]
              rw [heq]; exact MeasurableSet.empty }
  refine ⟨alg, ?_⟩
  intro M w u v
  rintro ⟨X, μ, q, hX, hμq, hrate⟩
  let prefSet : Equiv.Perm (Fin n) → ℕ → Finset (Fin n) :=
    fun π k => (Finset.univ.filter (fun idx : Fin n => idx.1 < k)).image π
  have h_pref_zero : ∀ π : Equiv.Perm (Fin n), prefSet π 0 = ∅ := by
    intro π; ext y; simp [prefSet]
  have h_pref_succ : ∀ (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k + 1 ≤ n),
      prefSet π (k + 1) = insert (π ⟨k, hk⟩) (prefSet π k) ∧
      π ⟨k, hk⟩ ∉ prefSet π k := by
    intro π k hk
    constructor
    · have hfilt : (Finset.univ.filter (fun idx : Fin n => idx.1 < k + 1)) =
          insert ⟨k, hk⟩ (Finset.univ.filter (fun idx : Fin n => idx.1 < k)) := by
        ext idx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      dsimp only [prefSet]
      rw [hfilt, Finset.image_insert]
    · simp only [prefSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      rintro ⟨idx, hidx, heq⟩
      have hval : idx.1 = k := congrArg Fin.val (π.injective heq)
      omega
  have h_pref_card : ∀ (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
      (prefSet π k).card = k := by
    intro π k
    induction k with
    | zero => intro _; simp [h_pref_zero]
    | succ k ih =>
      intro hk
      obtain ⟨hins, hnot⟩ := h_pref_succ π k hk
      rw [hins, Finset.card_insert_of_notMem hnot, ih (Nat.le_of_succ_le hk)]
  let pRate : Fin m → Finset (Fin n) → Fin n → Finset (Fin n) → ℝ :=
    fun i S x A =>
      if s < S.card ∧ x ∈ X S i ∧ μ i (S.erase x) A ≠ 0 then
        q i S x A / μ i (S.erase x) A
      else 0
  let singleStep : Fin m → Equiv.Perm (Fin n) → (Fin n → ℝ) → ℕ → Finset (Fin n) → Finset (Fin n) :=
    fun i π ω k A =>
      if hk : k + 1 ≤ n then
        let x := π ⟨k, hk⟩
        let S := prefSet π (k + 1)
        if 0 ≤ ω x ∧ ω x < pRate i S x A then insert x A else A
      else A
  let singleTraj : Fin m → Equiv.Perm (Fin n) → (Fin n → ℝ) → ℕ → Finset (Fin n) :=
    fun i π ω k => Nat.rec ∅ (fun k₀ A => singleStep i π ω k₀ A) k
  have h_pathwise_decouple :
      ∀ (ω : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
        let st := runDetRepresentedWelfareSteps (alg.det ω) v u π k hk
        st.1.toFinset = prefSet π k ∧
        IsAllocOf st.1.toFinset st.2 ∧
        (∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
        (∀ i : Fin m, st.2 i = singleTraj i π ω k) := by
    intro ω π k
    induction k with
    | zero =>
      intro _
      refine ⟨by simp [runDetRepresentedWelfareSteps, h_pref_zero], ?_, ?_, ?_⟩
      · exact ⟨fun _ => Finset.empty_subset _, fun _ _ _ => disjoint_bot_left⟩
      · intro i; simp [runDetRepresentedWelfareSteps, (M i).empty_indep]
      · intro i; rfl
    | succ k ih =>
      intro hk
      have hk0 : k ≤ n := Nat.le_of_succ_le hk
      obtain ⟨hprev_set, hprev_alloc, hprev_ind, hprev_dec⟩ := ih hk0
      obtain ⟨hins, hnot_pref⟩ := h_pref_succ π k hk
      let prev := (runDetRepresentedWelfareSteps (alg.det ω) v u π k hk0).1
      let bundles := (runDetRepresentedWelfareSteps (alg.det ω) v u π k hk0).2
      let x := π ⟨k, hk⟩
      let S := insert x prev.toFinset
      have hx_not_prev : x ∉ prev.toFinset := by
        dsimp only [prev, x]; rw [hprev_set]; exact hnot_pref
      have hS_eq : S = prefSet π (k + 1) := by
        dsimp only [S, prev, x]; rw [hprev_set, hins]
      have hlist_set : (prev ++ [x]).toFinset = S := by
        dsimp only [S]; ext y; simp [Finset.mem_insert]
      have hx_not_bundle : ∀ i : Fin m, x ∉ bundles i :=
        fun i hxb => hx_not_prev (hprev_alloc.1 i hxb)
      obtain ⟨hr_none, hr_some⟩ := hrate prev x bundles hx_not_prev
      have h_none_alloc : IsAllocOf S bundles :=
        ⟨fun i => (hprev_alloc.1 i).trans (Finset.subset_insert x _), hprev_alloc.2⟩
      by_cases hc : S.card ≤ s ∨ (∀ j : Fin m, x ∉ X S j)
      · have hrr := hr_none hc
        have hstep_none : (alg.det ω).step prev x bundles
            (fun i ⟨T, _⟩ => v i T) (fun i ⟨g, _⟩ => u i g) = none := by
          dsimp only [alg, detAlg]; rw [hrr]
        have hp0 : ∀ i : Fin m, pRate i S x (bundles i) = 0 := by
          intro i
          dsimp only [pRate]
          refine if_neg ?_
          rintro ⟨hs_lt, hxi, _⟩
          rcases hc with hle | hall
          · exact not_lt_of_ge hle hs_lt
          · exact hall i hxi
        change (prev ++ [x]).toFinset = prefSet π (k + 1) ∧
          IsAllocOf (prev ++ [x]).toFinset
            (match (alg.det ω).step prev x bundles
                (fun i ⟨T, _⟩ => v i T) (fun i ⟨g, _⟩ => u i g) with
              | none => bundles
              | some i => Function.update bundles i (insert x (bundles i))) ∧
          (∀ i : Fin m, (M i).Indep ((match (alg.det ω).step prev x bundles
                (fun i ⟨T, _⟩ => v i T) (fun i ⟨g, _⟩ => u i g) with
              | none => bundles
              | some i => Function.update bundles i (insert x (bundles i))) i : Set (Fin n))) ∧
          (∀ i : Fin m, (match (alg.det ω).step prev x bundles
                (fun i ⟨T, _⟩ => v i T) (fun i ⟨g, _⟩ => u i g) with
              | none => bundles
              | some i => Function.update bundles i (insert x (bundles i))) i =
            singleStep i π ω k (singleTraj i π ω k))
        rw [hlist_set, hstep_none]
        refine ⟨hS_eq, h_none_alloc, hprev_ind, fun i => ?_⟩
        dsimp only [singleStep]
        rw [dif_pos hk, ← hprev_dec i, ← hS_eq, hp0 i]
        have hnacc : ¬ (0 ≤ ω x ∧ ω x < 0) := fun h => lt_irrefl 0 (lt_of_le_of_lt h.1 h.2)
        exact (if_neg hnacc).symm
      · push_neg at hc
        rcases hc with ⟨hs_lt, j, hxj⟩
        have hrr := hr_some j hs_lt hxj
        let r₀ : ℝ := if μ j (S.erase x) (bundles j) = 0 then 0
                      else q j S x (bundles j) / μ j (S.erase x) (bundles j)
        have hr₀_eq : r₀ = pRate j S x (bundles j) := by
          dsimp only [r₀, pRate]
          by_cases hμ0 : μ j (S.erase x) (bundles j) = 0
          · rw [if_pos hμ0, if_neg (fun h => h.2.2 hμ0)]
          · rw [if_neg hμ0, if_pos ⟨hs_lt, hxj, hμ0⟩]
        have hx_not_X : ∀ i : Fin m, i ≠ j → x ∉ X S i := by
          intro i hij hxi
          exact Finset.disjoint_left.mp ((hX S).1.2 i j hij) hxi hxj
        have hp_other : ∀ i : Fin m, i ≠ j → pRate i S x (bundles i) = 0 := by
          intro i hij
          dsimp only [pRate]
          exact if_neg (fun h => hx_not_X i hij h.2.1)
        have hstep_eval : (alg.det ω).step prev x bundles
            (fun i ⟨T, _⟩ => v i T) (fun i ⟨g, _⟩ => u i g) =
            if 0 ≤ ω x ∧ ω x < r₀ then some j else none := by
          dsimp only [alg, detAlg]; rw [hrr]
        change (prev ++ [x]).toFinset = prefSet π (k + 1) ∧
          IsAllocOf (prev ++ [x]).toFinset
            (match (alg.det ω).step prev x bundles
                (fun i ⟨T, _⟩ => v i T) (fun i ⟨g, _⟩ => u i g) with
              | none => bundles
              | some i => Function.update bundles i (insert x (bundles i))) ∧
          (∀ i : Fin m, (M i).Indep ((match (alg.det ω).step prev x bundles
                (fun i ⟨T, _⟩ => v i T) (fun i ⟨g, _⟩ => u i g) with
              | none => bundles
              | some i => Function.update bundles i (insert x (bundles i))) i : Set (Fin n))) ∧
          (∀ i : Fin m, (match (alg.det ω).step prev x bundles
                (fun i ⟨T, _⟩ => v i T) (fun i ⟨g, _⟩ => u i g) with
              | none => bundles
              | some i => Function.update bundles i (insert x (bundles i))) i =
            singleStep i π ω k (singleTraj i π ω k))
        rw [hlist_set, hstep_eval]
        by_cases hacc : 0 ≤ ω x ∧ ω x < r₀
        · rw [if_pos hacc]
          dsimp only
          refine ⟨hS_eq, ?_, ?_, ?_⟩
          · refine ⟨?_, ?_⟩
            · intro i
              by_cases hij : i = j
              · subst hij
                rw [Function.update_self]
                exact Finset.insert_subset_insert x (hprev_alloc.1 i)
              · rw [Function.update_of_ne hij]
                exact (hprev_alloc.1 i).trans (Finset.subset_insert x _)
            · intro i₁ i₂ h12
              by_cases h1 : i₁ = j
              · subst h1
                rw [Function.update_self, Function.update_of_ne h12.symm]
                exact Finset.disjoint_insert_left.mpr ⟨hx_not_bundle i₂, hprev_alloc.2 i₁ i₂ h12⟩
              · by_cases h2 : i₂ = j
                · subst h2
                  rw [Function.update_of_ne h1, Function.update_self]
                  exact Finset.disjoint_insert_right.mpr ⟨hx_not_bundle i₁, hprev_alloc.2 i₁ i₂ h12⟩
                · rw [Function.update_of_ne h1, Function.update_of_ne h2]
                  exact hprev_alloc.2 i₁ i₂ h12
          · intro i
            by_cases hij : i = j
            · subst hij
              rw [Function.update_self]
              have hr_pos : 0 < r₀ := lt_of_le_of_lt hacc.1 hacc.2
              have hq_ne : q i S x (bundles i) ≠ 0 := by
                intro hq0
                dsimp only [r₀] at hr_pos
                rw [hq0, zero_div] at hr_pos
                split_ifs at hr_pos <;> exact lt_irrefl 0 hr_pos
              rw [Finset.coe_insert]
              exact (((hμq i).2.2 S hs_lt).2.1 x (bundles i) hq_ne).2.2.2
            · rw [Function.update_of_ne hij]
              exact hprev_ind i
          · intro i
            dsimp only [singleStep]
            rw [dif_pos hk, ← hprev_dec i, ← hS_eq]
            by_cases hij : i = j
            · subst hij
              rw [Function.update_self, ← hr₀_eq, if_pos hacc]
            · rw [Function.update_of_ne hij, hp_other i hij]
              have hnacc : ¬ (0 ≤ ω x ∧ ω x < 0) := fun h => lt_irrefl 0 (lt_of_le_of_lt h.1 h.2)
              exact (if_neg hnacc).symm
        · rw [if_neg hacc]
          dsimp only
          refine ⟨hS_eq, h_none_alloc, hprev_ind, fun i => ?_⟩
          dsimp only [singleStep]
          rw [dif_pos hk, ← hprev_dec i, ← hS_eq]
          by_cases hij : i = j
          · subst hij
            rw [← hr₀_eq, if_neg hacc]
          · rw [hp_other i hij]
            have hnacc : ¬ (0 ≤ ω x ∧ ω x < 0) := fun h => lt_irrefl 0 (lt_of_le_of_lt h.1 h.2)
            exact (if_neg hnacc).symm
  have lem_coord : ∀ (g : Fin n) (r : ℝ) (E : Set (Fin n → ℝ)),
      0 ≤ r → r ≤ 1 → MeasurableSet E →
      (∀ ω ω' : Fin n → ℝ, (∀ y : Fin n, y ≠ g → ω y = ω' y) → (ω ∈ E ↔ ω' ∈ E)) →
      seedMeas.real (E ∩ {ω | 0 ≤ ω g ∧ ω g < r}) = r * seedMeas.real E ∧
      seedMeas.real (E ∩ {ω | ¬ (0 ≤ ω g ∧ ω g < r)}) = (1 - r) * seedMeas.real E := by
    intro g r E hr0 hr1 hE_meas hE_indep
    let μ0 : Fin n → Measure ℝ := fun _ => unitMeas
    let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (· = g)
    let μL : Measure ({y : Fin n // y = g} → ℝ) := Measure.pi (fun _ => unitMeas)
    let μR : Measure ({y : Fin n // y ≠ g} → ℝ) := Measure.pi (fun _ => unitMeas)
    have hmp : MeasurePreserving e seedMeas (μL.prod μR) := by
      dsimp only [seedMeas, e, μL, μR, μ0]
      convert MeasureTheory.measurePreserving_piEquivPiSubtypeProd μ0 (· = g)
    let AL : Set ({y : Fin n // y = g} → ℝ) := Set.univ.pi (fun _ => Set.Ico 0 r)
    have hAL_meas : MeasurableSet AL := MeasurableSet.univ_pi (fun _ => measurableSet_Ico)
    have hμL_AL : μL AL = ENNReal.ofReal r := by
      dsimp only [μL, AL]
      rw [Measure.pi_pi]
      have huniv_sub : (Finset.univ : Finset {y : Fin n // y = g}) = {⟨g, rfl⟩} := by
        ext a
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        exact Subtype.ext a.2
      rw [huniv_sub, Finset.prod_singleton]
      dsimp only [unitMeas]
      rw [Measure.restrict_apply measurableSet_Ico]
      have hinter : Set.Ico (0 : ℝ) r ∩ Set.Icc (0 : ℝ) 1 = Set.Ico (0 : ℝ) r := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_Icc]
        exact ⟨fun h => h.1, fun ⟨ht0, htr⟩ => ⟨⟨ht0, htr⟩, ⟨ht0, le_of_lt (lt_of_lt_of_le htr hr1)⟩⟩⟩
      rw [hinter, Real.volume_Ico, sub_zero]
    let emb : ({y : Fin n // y ≠ g} → ℝ) → (Fin n → ℝ) := fun z => e.symm (0, z)
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
    have hAL_iff : ∀ ω : Fin n → ℝ, (e ω).1 ∈ AL ↔ (0 ≤ ω g ∧ ω g < r) := by
      intro ω
      simp only [AL, Set.mem_univ_pi, Set.mem_Ico]
      exact ⟨fun h => h ⟨g, rfl⟩, fun h ⟨_, rfl⟩ => h⟩
    let Acc : Set (Fin n → ℝ) := {ω | 0 ≤ ω g ∧ ω g < r}
    have hAcc_meas : MeasurableSet Acc := (measurable_pi_apply g) measurableSet_Ico
    have hpre_acc : e ⁻¹' (AL ×ˢ ER) = E ∩ Acc := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff, hAL_iff, hER_iff, Acc,
        Set.mem_setOf_eq, and_comm]
    have hpre_E : e ⁻¹' (Set.univ ×ˢ ER) = E := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and, hER_iff]
    have hm_acc : seedMeas (E ∩ Acc) = ENNReal.ofReal r * μR ER := by
      rw [← hpre_acc, hmp.measure_preimage (hAL_meas.prod hER_meas).nullMeasurableSet,
        Measure.prod_prod, hμL_AL]
    have hm_E : seedMeas E = μR ER := by
      rw [← hpre_E, hmp.measure_preimage (MeasurableSet.univ.prod hER_meas).nullMeasurableSet,
        Measure.prod_prod, measure_univ, one_mul]
    have hreal_acc : seedMeas.real (E ∩ Acc) = r * seedMeas.real E := by
      rw [measureReal_def, measureReal_def, hm_acc, hm_E, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hr0]
    have hunion : (E ∩ Acc) ∪ (E ∩ Accᶜ) = E := Set.inter_union_compl E Acc
    have hdisj : Disjoint (E ∩ Acc) (E ∩ Accᶜ) :=
      Disjoint.mono inf_le_right inf_le_right disjoint_compl_right
    have hsum_real : seedMeas.real E =
        seedMeas.real (E ∩ Acc) + seedMeas.real (E ∩ Accᶜ) := by
      conv_lhs => rw [← hunion]
      exact measureReal_union hdisj (hE_meas.inter hAcc_meas.compl)
    refine ⟨hreal_acc, ?_⟩
    change seedMeas.real (E ∩ Accᶜ) = (1 - r) * seedMeas.real E
    linarith
  have h_meas_single : ∀ (i : Fin m) (π : Equiv.Perm (Fin n)) (k : ℕ) (C : Finset (Fin n)),
      MeasurableSet {ω : Fin n → ℝ | singleTraj i π ω k = C} := by
    intro i π k
    induction k with
    | zero =>
      intro C
      by_cases hC : (∅ : Finset (Fin n)) = C
      · have heq : {ω : Fin n → ℝ | singleTraj i π ω 0 = C} = Set.univ := by
          ext ω; simp [singleTraj, hC]
        rw [heq]; exact MeasurableSet.univ
      · have heq : {ω : Fin n → ℝ | singleTraj i π ω 0 = C} = ∅ := by
          ext ω; simp [singleTraj, hC]
        rw [heq]; exact MeasurableSet.empty
    | succ k ih =>
      intro C
      by_cases hk : k + 1 ≤ n
      · let x := π ⟨k, hk⟩
        let S := prefSet π (k + 1)
        have hstep_eq : ∀ ω : Fin n → ℝ,
            singleTraj i π ω (k + 1) =
              if 0 ≤ ω x ∧ ω x < pRate i S x (singleTraj i π ω k) then
                insert x (singleTraj i π ω k)
              else singleTraj i π ω k := by
          intro ω
          change singleStep i π ω k (singleTraj i π ω k) = _
          dsimp only [singleStep]
          rw [dif_pos hk]
        have hunion : {ω : Fin n → ℝ | singleTraj i π ω (k + 1) = C} =
            ⋃ A : Finset (Fin n),
              ((if insert x A = C then
                  {ω : Fin n → ℝ | singleTraj i π ω k = A} ∩
                    {ω : Fin n → ℝ | 0 ≤ ω x ∧ ω x < pRate i S x A}
                else ∅) ∪
               (if A = C then
                  {ω : Fin n → ℝ | singleTraj i π ω k = A} ∩
                    {ω : Fin n → ℝ | ¬ (0 ≤ ω x ∧ ω x < pRate i S x A)}
                else ∅)) := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_union, hstep_eq ω]
          constructor
          · intro hC
            refine ⟨singleTraj i π ω k, ?_⟩
            by_cases hacc : 0 ≤ ω x ∧ ω x < pRate i S x (singleTraj i π ω k)
            · rw [if_pos hacc] at hC
              exact Or.inl (by rw [if_pos hC]; exact ⟨rfl, hacc⟩)
            · rw [if_neg hacc] at hC
              exact Or.inr (by rw [if_pos hC]; exact ⟨rfl, hacc⟩)
          · rintro ⟨A, hL | hR⟩
            · by_cases hm : insert x A = C
              · rw [if_pos hm] at hL
                rcases hL with ⟨hA, hacc⟩
                change singleTraj i π ω k = A at hA
                change 0 ≤ ω x ∧ ω x < pRate i S x A at hacc
                rw [hA, if_pos hacc, hm]
              · rw [if_neg hm] at hL; exact False.elim hL
            · by_cases hm : A = C
              · rw [if_pos hm] at hR
                rcases hR with ⟨hA, hnacc⟩
                change singleTraj i π ω k = A at hA
                change ¬ (0 ≤ ω x ∧ ω x < pRate i S x A) at hnacc
                rw [hA, if_neg hnacc, hm]
              · rw [if_neg hm] at hR; exact False.elim hR
        rw [hunion]
        refine MeasurableSet.iUnion fun A => ?_
        have hIco : MeasurableSet {ω : Fin n → ℝ | 0 ≤ ω x ∧ ω x < pRate i S x A} :=
          (measurable_pi_apply x) measurableSet_Ico
        refine MeasurableSet.union ?_ ?_
        · split_ifs
          · exact (ih A).inter hIco
          · exact MeasurableSet.empty
        · split_ifs
          · exact (ih A).inter hIco.compl
          · exact MeasurableSet.empty
      · have heq : {ω : Fin n → ℝ | singleTraj i π ω (k + 1) = C} =
            {ω : Fin n → ℝ | singleTraj i π ω k = C} := by
          ext ω
          simp only [Set.mem_setOf_eq]
          change singleStep i π ω k (singleTraj i π ω k) = C ↔ _
          dsimp only [singleStep]
          rw [dif_neg hk]
        rw [heq]; exact ih C
  have h_coord_loc : ∀ (i : Fin m) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n)
      (ω ω' : Fin n → ℝ),
      (∀ y ∈ prefSet π k, ω y = ω' y) → singleTraj i π ω k = singleTraj i π ω' k := by
    intro i π k
    induction k with
    | zero => intro _ _ _ _; rfl
    | succ k ih =>
      intro hk ω ω' h_agree
      have hk0 : k ≤ n := Nat.le_of_succ_le hk
      obtain ⟨hins, _⟩ := h_pref_succ π k hk
      have hA_eq : singleTraj i π ω k = singleTraj i π ω' k :=
        ih hk0 ω ω' (fun y hy => h_agree y (hins ▸ Finset.mem_insert_of_mem hy))
      have hx_eq : ω (π ⟨k, hk⟩) = ω' (π ⟨k, hk⟩) :=
        h_agree (π ⟨k, hk⟩) (hins ▸ Finset.mem_insert_self _ _)
      change singleStep i π ω k (singleTraj i π ω k) = singleStep i π ω' k (singleTraj i π ω' k)
      dsimp only [singleStep]
      rw [dif_pos hk, dif_pos hk, hA_eq, hx_eq]
  have h_perm_loc : ∀ (i : Fin m) (k : ℕ) (hk : k ≤ n) (π₁ π₂ : Equiv.Perm (Fin n))
      (ω : Fin n → ℝ),
      (∀ (r : ℕ) (hr : r < k), π₁ ⟨r, lt_of_lt_of_le hr hk⟩ = π₂ ⟨r, lt_of_lt_of_le hr hk⟩) →
      singleTraj i π₁ ω k = singleTraj i π₂ ω k := by
    intro i k
    induction k with
    | zero => intro _ _ _ _ _; rfl
    | succ k ih =>
      intro hk π₁ π₂ ω h_eq
      have hk0 : k ≤ n := Nat.le_of_succ_le hk
      have hA_eq : singleTraj i π₁ ω k = singleTraj i π₂ ω k :=
        ih hk0 π₁ π₂ ω (fun r hr => h_eq r (Nat.lt_succ_of_lt hr))
      have hx_eq : π₁ ⟨k, hk⟩ = π₂ ⟨k, hk⟩ := h_eq k (Nat.lt_succ_self k)
      have hpref_eq : prefSet π₁ (k + 1) = prefSet π₂ (k + 1) := by
        dsimp only [prefSet]
        ext y
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨idx, hidx, hy⟩ => ⟨idx, hidx, (h_eq idx.1 hidx).symm.trans hy⟩,
          fun ⟨idx, hidx, hy⟩ => ⟨idx, hidx, (h_eq idx.1 hidx).trans hy⟩⟩
      change singleStep i π₁ ω k (singleTraj i π₁ ω k) =
        singleStep i π₂ ω k (singleTraj i π₂ ω k)
      dsimp only [singleStep]
      rw [dif_pos hk, dif_pos hk, hA_eq, hx_eq, hpref_eq]
  have h_traj_le_s : ∀ (i : Fin m) (k : ℕ) (hk : k ≤ n),
      k ≤ s → ∀ (π : Equiv.Perm (Fin n)) (ω : Fin n → ℝ), singleTraj i π ω k = ∅ := by
    intro i k
    induction k with
    | zero => intro _ _ _ _; rfl
    | succ k ih =>
      intro hk hks π ω
      have hk0 : k ≤ n := Nat.le_of_succ_le hk
      change singleStep i π ω k (singleTraj i π ω k) = ∅
      dsimp only [singleStep]
      rw [dif_pos hk, ih hk0 (Nat.le_of_succ_le hks) π ω]
      have hcard : (prefSet π (k + 1)).card = k + 1 := h_pref_card π (k + 1) hk
      have hp0 : pRate i (prefSet π (k + 1)) (π ⟨k, hk⟩) ∅ = 0 := by
        dsimp only [pRate]
        exact if_neg (fun h => by omega)
      rw [hp0]
      have hnacc : ¬ (0 ≤ ω (π ⟨k, hk⟩) ∧ ω (π ⟨k, hk⟩) < 0) :=
        fun h => lt_irrefl 0 (lt_of_le_of_lt h.1 h.2)
      exact if_neg hnacc
  have h_pRate_props : ∀ (i : Fin m) (S : Finset (Fin n)), s < S.card →
      ∀ g ∈ S, ∀ A : Finset (Fin n),
        0 ≤ pRate i S g A ∧ pRate i S g A ≤ 1 ∧
        pRate i S g A * μ i (S.erase g) A = q i S g A := by
    intro i S hs_lt g hgS A
    have hμ_nn := ((hμq i).2.1 (S.erase g)).1 A
    obtain ⟨hq_bds, hq_supp, _, _⟩ := (hμq i).2.2 S hs_lt
    obtain ⟨hq0, hq_le⟩ := hq_bds g hgS A
    dsimp only [pRate]
    by_cases hc : s < S.card ∧ g ∈ X S i ∧ μ i (S.erase g) A ≠ 0
    · rw [if_pos hc]
      have hμ_pos : 0 < μ i (S.erase g) A := lt_of_le_of_ne hμ_nn hc.2.2.symm
      exact ⟨div_nonneg hq0 hμ_nn, (div_le_one hμ_pos).mpr hq_le,
        div_mul_cancel₀ _ hc.2.2⟩
    · rw [if_neg hc]
      refine ⟨le_rfl, zero_le_one, ?_⟩
      rw [zero_mul]
      by_cases hgX : g ∈ X S i
      · have hμ0 : μ i (S.erase g) A = 0 := by
          by_contra hne
          exact hc ⟨hs_lt, hgX, hne⟩
        exact (le_antisymm (hμ0 ▸ hq_le) hq0).symm
      · by_contra hq_ne
        exact hgX (hq_supp g A (Ne.symm hq_ne)).2.1
  have h_acc_sum : ∀ (i : Fin m) (S : Finset (Fin n)), s < S.card →
      ∀ g ∈ S, ∀ C : Finset (Fin n),
        (∑ A : Finset (Fin n), if insert g A = C then q i S g A else 0) =
          if g ∈ C then q i S g (C.erase g) else 0 := by
    intro i S hs_lt g _ C
    obtain ⟨_, hq_supp, _, _⟩ := (hμq i).2.2 S hs_lt
    by_cases hgC : g ∈ C
    · rw [if_pos hgC]
      have hsingle : (∑ A : Finset (Fin n), if insert g A = C then q i S g A else 0) =
          if insert g (C.erase g) = C then q i S g (C.erase g) else 0 := by
        refine Finset.sum_eq_single (C.erase g) ?_ ?_
        · intro A _ hAne
          by_cases hins : insert g A = C
          · rw [if_pos hins]
            have hgA : g ∈ A := by
              by_contra hg_not
              have hA_eq : A = C.erase g := by
                rw [← hins, Finset.erase_insert hg_not]
              exact hAne hA_eq
            by_contra hq_ne
            have hsub : A ⊆ S.erase g := (hq_supp g A hq_ne).2.2.1
            exact Finset.notMem_erase g S (hsub hgA)
          · exact if_neg hins
        · intro hnot
          exact absurd (Finset.mem_univ _) hnot
      rw [hsingle, if_pos (Finset.insert_erase hgC)]
    · rw [if_neg hgC]
      refine Finset.sum_eq_zero fun A _ => ?_
      by_cases hins : insert g A = C
      · exact absurd (hins ▸ Finset.mem_insert_self g A) hgC
      · exact if_neg hins
  have h_fiber_avg : ∀ (k : ℕ) (hk : k + 1 ≤ n) (T : Finset (Fin n)) (g : Fin n)
      (f : Equiv.Perm (Fin n) → ℝ),
      T.card = k → g ∉ T →
      (∀ π₁ π₂ : Equiv.Perm (Fin n),
        (∀ (r : ℕ) (hr : r < k), π₁ ⟨r, lt_of_lt_of_le hr (Nat.le_of_succ_le hk)⟩ =
          π₂ ⟨r, lt_of_lt_of_le hr (Nat.le_of_succ_le hk)⟩) → f π₁ = f π₂) →
      let evT := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
        (fun π => prefSet π k = T)
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
      have hpref : prefSet π k = T := (Finset.mem_filter.mp hπ).2
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
        have hpref : prefSet π k = T := (Finset.mem_filter.mp hπ_evT).2
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
        have hpref' : prefSet (Equiv.swap a b * π) k = T := by
          rw [← hpref]
          dsimp only [prefSet]
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
  have h_law_ind : ∀ (i : Fin m) (k : ℕ) (hk : k ≤ n) (S C : Finset (Fin n)),
      S.card = k →
        let evS := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => prefSet π k = S)
        (∑ π ∈ evS, seedMeas.real {ω | singleTraj i π ω k = C}) =
          (evS.card : ℝ) * μ i S C := by
    intro i k
    induction k with
    | zero =>
      intro hk S C hS_card evS
      rw [(hμq i).1 S (by omega)]
      by_cases hC : C = ∅
      · subst hC
        simp only [↓reduceIte, mul_one]
        have hprob1 : ∀ π : Equiv.Perm (Fin n), seedMeas.real {ω | singleTraj i π ω 0 = ∅} = 1 := by
          intro π
          have heq : {ω : Fin n → ℝ | singleTraj i π ω 0 = ∅} = Set.univ := by
            ext ω; simp [singleTraj]
          rw [heq, measureReal_def, measure_univ, ENNReal.toReal_one]
        rw [Finset.sum_congr rfl fun π _ => hprob1 π]
        simp
      · simp only [hC, ↓reduceIte, mul_zero]
        refine Finset.sum_eq_zero fun π _ => ?_
        have heq : {ω : Fin n → ℝ | singleTraj i π ω 0 = C} = ∅ := by
          ext ω; simp [singleTraj, Ne.symm hC]
        rw [heq, measureReal_empty]
    | succ k ih =>
      intro hk S C hS_card evS
      have hk0 : k ≤ n := Nat.le_of_succ_le hk
      by_cases hks : k + 1 ≤ s
      · rw [(hμq i).1 S (by omega)]
        by_cases hC : C = ∅
        · subst hC
          simp only [↓reduceIte, mul_one]
          have hprob1 : ∀ π : Equiv.Perm (Fin n),
              seedMeas.real {ω | singleTraj i π ω (k + 1) = ∅} = 1 := by
            intro π
            have heq : {ω : Fin n → ℝ | singleTraj i π ω (k + 1) = ∅} = Set.univ := by
              ext ω; simp [h_traj_le_s i (k + 1) hk hks π ω]
            rw [heq, measureReal_def, measure_univ, ENNReal.toReal_one]
          rw [Finset.sum_congr rfl fun π _ => hprob1 π]
          simp
        · simp only [hC, ↓reduceIte, mul_zero]
          refine Finset.sum_eq_zero fun π _ => ?_
          have heq : {ω : Fin n → ℝ | singleTraj i π ω (k + 1) = C} = ∅ := by
            ext ω; simp [h_traj_le_s i (k + 1) hk hks π ω, Ne.symm hC]
          rw [heq, measureReal_empty]
      · have hs_lt : s < S.card := by omega
        have h_maps_S : ∀ π ∈ evS, π ⟨k, hk⟩ ∈ S := by
          intro π hπ
          have hpref : prefSet π (k + 1) = S := (Finset.mem_filter.mp hπ).2
          rw [← hpref, (h_pref_succ π k hk).1]
          exact Finset.mem_insert_self _ _
        have h_evStep_eq : ∀ g ∈ S,
            evS.filter (fun π => π ⟨k, hk⟩ = g) =
            (((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
              (fun π => prefSet π k = S.erase g)).filter (fun π => π ⟨k, hk⟩ = g)) := by
          intro g hgS
          ext π
          simp only [evS, Finset.mem_filter, Finset.mem_univ, true_and]
          obtain ⟨hins, hnot⟩ := h_pref_succ π k hk
          constructor
          · rintro ⟨hprefS, hπg⟩
            refine ⟨?_, hπg⟩
            have hg_not : g ∉ prefSet π k := hπg ▸ hnot
            rw [← hprefS, hins, hπg]
            exact (Finset.erase_insert hg_not).symm
          · rintro ⟨hprefT, hπg⟩
            refine ⟨?_, hπg⟩
            rw [hins, hπg, hprefT]
            exact Finset.insert_erase hgS
        have h_evStep_prev : ∀ g ∈ S, ∀ A : Finset (Fin n),
            (∑ π ∈ evS.filter (fun π => π ⟨k, hk⟩ = g),
              seedMeas.real {ω | singleTraj i π ω k = A}) =
            ((evS.filter (fun π => π ⟨k, hk⟩ = g)).card : ℝ) * μ i (S.erase g) A := by
          intro g hgS A
          have hnk_pos : (0 : ℝ) < ((n - k : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
          let T := S.erase g
          have hT_card : T.card = k := by rw [Finset.card_erase_of_mem hgS, hS_card]; omega
          have hgT : g ∉ T := Finset.notMem_erase g S
          let fA : Equiv.Perm (Fin n) → ℝ := fun π => seedMeas.real {ω | singleTraj i π ω k = A}
          have hfA_loc : ∀ π₁ π₂ : Equiv.Perm (Fin n),
              (∀ (r : ℕ) (hr : r < k),
                π₁ ⟨r, lt_of_lt_of_le hr hk0⟩ = π₂ ⟨r, lt_of_lt_of_le hr hk0⟩) →
              fA π₁ = fA π₂ := by
            intro π₁ π₂ heq
            dsimp only [fA]; congr 1; ext ω; simp only [Set.mem_setOf_eq]
            rw [h_perm_loc i k hk0 π₁ π₂ ω heq]
          obtain ⟨hcard_rel, hsum_rel⟩ := h_fiber_avg k hk T g fA hT_card hgT hfA_loc
          have hlawA := ih hk0 T A hT_card
          rw [h_evStep_eq g hgS]
          have hcard_cast : (((n - k : ℕ) : ℝ) *
              ((((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
                (fun π => prefSet π k = T)).filter (fun π => π ⟨k, hk⟩ = g)).card : ℝ)) =
              (((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
                (fun π => prefSet π k = T)).card : ℝ) := by
            exact_mod_cast hcard_rel
          have h1 : ((n - k : ℕ) : ℝ) *
              (∑ π ∈ (((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
                (fun π => prefSet π k = T)).filter (fun π => π ⟨k, hk⟩ = g)), fA π) =
              ((n - k : ℕ) : ℝ) *
              (((((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
                (fun π => prefSet π k = T)).filter (fun π => π ⟨k, hk⟩ = g)).card : ℝ) *
                μ i T A) := by
            rw [hsum_rel, hlawA, ← mul_assoc, hcard_cast]
          exact mul_left_cancel₀ hnk_pos.ne' h1
        have h_evStep_symm : ∀ g ∈ S, ∀ g' ∈ S,
            (evS.filter (fun π => π ⟨k, hk⟩ = g')).card =
            (evS.filter (fun π => π ⟨k, hk⟩ = g)).card := by
          intro g hgS g' hg'S
          have hswap_S : ∀ a ∈ S, ∀ b ∈ S,
              ∀ π ∈ evS.filter (fun π => π ⟨k, hk⟩ = a),
                (Equiv.swap a b * π) ∈ evS.filter (fun π => π ⟨k, hk⟩ = b) := by
            intro a haS b hbS π hπ
            rcases Finset.mem_filter.mp hπ with ⟨hπ_evS, hπ_k⟩
            have hpref : prefSet π (k + 1) = S := (Finset.mem_filter.mp hπ_evS).2
            have hmem_iff : ∀ x : Fin n, Equiv.swap a b x ∈ S ↔ x ∈ S := by
              intro x
              by_cases hxa : x = a
              · subst hxa; simp [haS, hbS]
              · by_cases hxb : x = b
                · subst hxb; simp [haS, hbS]
                · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
            have hpref' : prefSet (Equiv.swap a b * π) (k + 1) = S := by
              ext y; constructor
              · intro hy
                rcases Finset.mem_image.mp hy with ⟨idx, hidx, rfl⟩
                change Equiv.swap a b (π idx) ∈ S
                rw [hmem_iff, ← hpref]
                exact Finset.mem_image.mpr ⟨idx, hidx, rfl⟩
              · intro hyS
                have hsy : Equiv.swap a b y ∈ prefSet π (k + 1) :=
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
              seedMeas.real {ω | singleTraj i π ω (k + 1) = C}) =
            ((evS.filter (fun π => π ⟨k, hk⟩ = g)).card : ℝ) *
              (μ i (S.erase g) C +
                (if g ∈ C then q i S g (C.erase g) else 0) -
                q i S g C) := by
          intro g hgS
          let evg := evS.filter (fun π => π ⟨k, hk⟩ = g)
          have h_pi_val : ∀ π ∈ evg,
              seedMeas.real {ω | singleTraj i π ω (k + 1) = C} =
              ∑ A : Finset (Fin n),
                ((if insert g A = C then pRate i S g A else 0) +
                 (if A = C then 1 - pRate i S g A else 0)) *
                seedMeas.real {ω | singleTraj i π ω k = A} := by
            intro π hπ
            rcases Finset.mem_filter.mp hπ with ⟨hπ_evS, hπg⟩
            have hprefS : prefSet π (k + 1) = S := (Finset.mem_filter.mp hπ_evS).2
            have hg_not_prev : g ∉ prefSet π k := hπg ▸ (h_pref_succ π k hk).2
            have hstep_π : ∀ ω : Fin n → ℝ,
                singleTraj i π ω (k + 1) =
                  if 0 ≤ ω g ∧ ω g < pRate i S g (singleTraj i π ω k) then
                    insert g (singleTraj i π ω k)
                  else singleTraj i π ω k := by
              intro ω
              change singleStep i π ω k (singleTraj i π ω k) = _
              dsimp only [singleStep]
              rw [dif_pos hk, hprefS, hπg]
            let EA : Finset (Fin n) → Set (Fin n → ℝ) := fun A => {ω | singleTraj i π ω k = A}
            let slice : Finset (Fin n) → Set (Fin n → ℝ) :=
              fun A => EA A ∩ {ω | singleTraj i π ω (k + 1) = C}
            have hslice_meas : ∀ A, MeasurableSet (slice A) :=
              fun A => (h_meas_single i π k A).inter (h_meas_single i π (k + 1) C)
            have hslice_disj : Pairwise (fun A₁ A₂ => Disjoint (slice A₁) (slice A₂)) := by
              intro A₁ A₂ hne; rw [Set.disjoint_left]; intro ω h1 h2
              exact hne (h1.1.symm.trans h2.1)
            have hslice_union :
                (⋃ A ∈ (Finset.univ : Finset (Finset (Fin n))), slice A) =
                {ω | singleTraj i π ω (k + 1) = C} := by
              ext ω
              simp only [Set.mem_iUnion, Finset.mem_univ, slice, EA,
                Set.mem_inter_iff, Set.mem_setOf_eq]
              exact ⟨fun ⟨_, _, _, hC⟩ => hC, fun hC => ⟨singleTraj i π ω k, trivial, rfl, hC⟩⟩
            rw [← hslice_union,
                measureReal_biUnion_finset (fun A₁ _ A₂ _ hne => hslice_disj hne)
                  (fun A _ => hslice_meas A)]
            refine Finset.sum_congr rfl fun A _ => ?_
            have hEA_indep : ∀ ω ω' : Fin n → ℝ,
                (∀ y : Fin n, y ≠ g → ω y = ω' y) → (ω ∈ EA A ↔ ω' ∈ EA A) := by
              intro ω ω' h_ne
              have h_eq : singleTraj i π ω k = singleTraj i π ω' k :=
                h_coord_loc i π k hk0 ω ω' (fun y hy => h_ne y (fun hyg => hg_not_prev (hyg ▸ hy)))
              simp only [EA, Set.mem_setOf_eq, h_eq]
            obtain ⟨hp0, hp1, _⟩ := h_pRate_props i S hs_lt g hgS A
            obtain ⟨hacc_real, hrej_real⟩ :=
              lem_coord g (pRate i S g A) (EA A) hp0 hp1 (h_meas_single i π k A) hEA_indep
            by_cases hExt : insert g A = C
            · by_cases hAC : A = C
              · have hslice_eq : slice A = EA A := by
                  ext ω
                  simp only [slice, EA, Set.mem_inter_iff, Set.mem_setOf_eq, and_iff_left_iff_imp]
                  intro hωA; rw [hstep_π ω, hωA]; split_ifs <;> assumption
                rw [hslice_eq, if_pos hExt, if_pos hAC]; ring
              · have hslice_eq : slice A = EA A ∩ {ω | 0 ≤ ω g ∧ ω g < pRate i S g A} := by
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
              · have hslice_eq : slice A = EA A ∩ {ω | ¬ (0 ≤ ω g ∧ ω g < pRate i S g A)} := by
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
          have hsum_pi : (∑ π ∈ evg, seedMeas.real {ω | singleTraj i π ω (k + 1) = C}) =
              ∑ A : Finset (Fin n),
                ((if insert g A = C then pRate i S g A else 0) +
                 (if A = C then 1 - pRate i S g A else 0)) *
                (∑ π ∈ evg, seedMeas.real {ω | singleTraj i π ω k = A}) := by
            rw [Finset.sum_congr rfl fun π hπ => h_pi_val π hπ, Finset.sum_comm]
            exact Finset.sum_congr rfl fun A _ => (Finset.mul_sum _ _ _).symm
          rw [hsum_pi]
          have hterm_eq : ∀ A : Finset (Fin n),
              ((if insert g A = C then pRate i S g A else 0) +
               (if A = C then 1 - pRate i S g A else 0)) *
              ((evg.card : ℝ) * μ i (S.erase g) A) =
              (evg.card : ℝ) *
                ((if insert g A = C then q i S g A else 0) +
                 (if A = C then μ i (S.erase g) A - q i S g A else 0)) := by
            intro A
            have hpm := (h_pRate_props i S hs_lt g hgS A).2.2
            by_cases h1 : insert g A = C <;> by_cases h2 : A = C
            · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2]; ring
            · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2]
              linear_combination (evg.card : ℝ) * hpm
            · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
              linear_combination -((evg.card : ℝ) * hpm)
            · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]; ring
          have hrew : (∑ A : Finset (Fin n),
              ((if insert g A = C then pRate i S g A else 0) +
               (if A = C then 1 - pRate i S g A else 0)) *
              (∑ π ∈ evg, seedMeas.real {ω | singleTraj i π ω k = A})) =
              (evg.card : ℝ) * ∑ A : Finset (Fin n),
                ((if insert g A = C then q i S g A else 0) +
                 (if A = C then μ i (S.erase g) A - q i S g A else 0)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun A _ => ?_
            rw [h_evStep_prev g hgS A]
            exact hterm_eq A
          rw [hrew]
          congr 1
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ C, h_acc_sum i S hs_lt g hgS C]
          simp only [Finset.mem_univ, ↓reduceIte]
          ring
        rw [(Finset.sum_fiberwise_of_maps_to h_maps_S
              (fun π => seedMeas.real {ω | singleTraj i π ω (k + 1) = C})).symm,
            Finset.sum_congr rfl fun g hgS => h_each_row g hgS,
            ((hμq i).2.2 S hs_lt).2.2.2 C]
        have hScard_ne : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun g hgS => ?_
        have hcard_g : (S.card : ℝ) * ((evS.filter (fun π => π ⟨k, hk⟩ = g)).card : ℝ) =
            (evS.card : ℝ) := by exact_mod_cast h_evS_card_rel g hgS
        have hdiv_g : ((evS.filter (fun π => π ⟨k, hk⟩ = g)).card : ℝ) =
            (evS.card : ℝ) * (1 / (S.card : ℝ)) := by
          field_simp [hScard_ne]; linarith
        rw [hdiv_g]; ring
  have h_marginal_univ : ∀ (i : Fin m) (C : Finset (Fin n)),
      (1 / (Nat.factorial n : ℝ)) *
        (∑ π : Equiv.Perm (Fin n), seedMeas.real {ω | singleTraj i π ω n = C}) =
      μ i Finset.univ C := by
    intro i C
    have huniv_card : (Finset.univ : Finset (Fin n)).card = n := by simp
    have hlaw := h_law_ind i n (le_refl n) Finset.univ C huniv_card
    have hev_univ : (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
        (fun π => prefSet π n = Finset.univ) = Finset.univ := by
      ext π
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact Finset.eq_univ_of_card _ ((h_pref_card π n (le_refl n)).trans (Fintype.card_fin n).symm)
    rw [hev_univ] at hlaw
    have hperm_card : ((Finset.univ : Finset (Equiv.Perm (Fin n))).card : ℝ) =
        (Nat.factorial n : ℝ) := by
      rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    have hfac_ne : (Nat.factorial n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    rw [hlaw, hperm_card]
    field_simp [hfac_ne]
  have hwelf_ind : ∀ Y : Fin m → Finset (Fin n),
      (∀ i, (M i).Indep (Y i : Set (Fin n))) →
      allocWelfare v Y = ((∑ i : Fin m, ∑ g ∈ Y i, w i g : ℝ) : WithBot ℝ) := by
    intro Y hY
    unfold allocWelfare
    rw [WithBot.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only [v, weightedMatroidVal]
    exact if_pos (hY i)
  have h_exp_eq : expectedRepresentedWelfareVal alg v u =
      ((∑ i : Fin m, ∑ A : Finset (Fin n),
        μ i Finset.univ A * (∑ g ∈ A, w i g) : ℝ) : WithBot ℝ) := by
    let final : Equiv.Perm (Fin n) → (Fin n → ℝ) → (Fin m → Finset (Fin n)) :=
      fun π ω => runDetRepresentedWelfare (alg.det ω) v u π
    have hfinal_dec : ∀ π ω i, final π ω i = singleTraj i π ω n :=
      fun π ω i => (h_pathwise_decouple ω π n (le_refl n)).2.2.2 i
    have hfinal_ind : ∀ π ω i, (M i).Indep (final π ω i : Set (Fin n)) :=
      fun π ω i => (h_pathwise_decouple ω π n (le_refl n)).2.2.1 i
    have h_no_bot : ¬ ∃ Y : Fin m → Finset (Fin n),
        0 < algRepresentedWelfareProb alg v u Y ∧ allocWelfare v Y = ⊥ := by
      rintro ⟨Y, hpos, hbot⟩
      dsimp only [algRepresentedWelfareProb, alg] at hpos
      have hex_pi : ∃ π : Equiv.Perm (Fin n), 0 < seedMeas.real {ω | final π ω = Y} := by
        by_contra hall
        push_neg at hall
        have hsum_le : (∑ π : Equiv.Perm (Fin n), seedMeas.real {ω | final π ω = Y}) ≤ 0 :=
          Finset.sum_nonpos fun π _ => hall π
        have hfac_nn : (0 : ℝ) ≤ 1 / (Nat.factorial n : ℝ) := by positivity
        have hle0 := mul_nonpos_of_nonneg_of_nonpos hfac_nn hsum_le
        linarith
      rcases hex_pi with ⟨π, hπ_pos⟩
      have hne : ({ω : Fin n → ℝ | final π ω = Y}).Nonempty := by
        by_contra hemp
        rw [Set.not_nonempty_iff_eq_empty.mp hemp, measureReal_empty] at hπ_pos
        exact lt_irrefl 0 hπ_pos
      rcases hne with ⟨ω₀, hω₀⟩
      have hY_ind : ∀ i, (M i).Indep (Y i : Set (Fin n)) := by
        intro i; rw [← hω₀]; exact hfinal_ind π ω₀ i
      rw [hwelf_ind Y hY_ind] at hbot
      exact WithBot.coe_ne_bot hbot
    dsimp only [expectedRepresentedWelfareVal]
    rw [if_neg h_no_bot, WithBot.coe_inj]
    have h_meas_final : ∀ π Y, MeasurableSet {ω : Fin n → ℝ | final π ω = Y} := by
      intro π Y
      have heq : {ω : Fin n → ℝ | final π ω = Y} =
          ⋂ j : Fin m, {ω : Fin n → ℝ | singleTraj j π ω n = Y j} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iInter, funext_iff, hfinal_dec π ω]
      rw [heq]
      exact MeasurableSet.iInter fun j => h_meas_single j π n (Y j)
    have h_per_pi : ∀ π : Equiv.Perm (Fin n),
        (∑ Y : Fin m → Finset (Fin n),
          seedMeas.real {ω | final π ω = Y} * (allocWelfare v Y).unbotD 0) =
        ∑ i : Fin m, ∑ A : Finset (Fin n),
          seedMeas.real {ω | singleTraj i π ω n = A} * (∑ g ∈ A, w i g) := by
      intro π
      have h1 : (∑ Y : Fin m → Finset (Fin n),
            seedMeas.real {ω | final π ω = Y} * (allocWelfare v Y).unbotD 0) =
          ∑ Y : Fin m → Finset (Fin n),
            seedMeas.real {ω | final π ω = Y} * (∑ i : Fin m, ∑ g ∈ Y i, w i g) := by
        refine Finset.sum_congr rfl fun Y _ => ?_
        by_cases hne : ({ω : Fin n → ℝ | final π ω = Y}).Nonempty
        · rcases hne with ⟨ω₀, hω₀⟩
          have hY_ind : ∀ i, (M i).Indep (Y i : Set (Fin n)) := by
            intro i; rw [← hω₀]; exact hfinal_ind π ω₀ i
          rw [hwelf_ind Y hY_ind, WithBot.unbotD_coe]
        · rw [Set.not_nonempty_iff_eq_empty.mp hne, measureReal_empty, zero_mul, zero_mul]
      rw [h1]
      have h2 : (∑ Y : Fin m → Finset (Fin n),
            seedMeas.real {ω | final π ω = Y} * (∑ i : Fin m, ∑ g ∈ Y i, w i g)) =
          ∑ i : Fin m, ∑ Y : Fin m → Finset (Fin n),
            seedMeas.real {ω | final π ω = Y} * (∑ g ∈ Y i, w i g) := by
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
      rw [h2]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [(Finset.sum_fiberwise (Finset.univ : Finset (Fin m → Finset (Fin n)))
            (fun Y => Y i)
            (fun Y => seedMeas.real {ω | final π ω = Y} * (∑ g ∈ Y i, w i g))).symm]
      refine Finset.sum_congr rfl fun A _ => ?_
      have h_inner : (∑ Y ∈ (Finset.univ : Finset (Fin m → Finset (Fin n))).filter (fun Y => Y i = A),
            seedMeas.real {ω | final π ω = Y} * (∑ g ∈ Y i, w i g)) =
          (∑ Y ∈ (Finset.univ : Finset (Fin m → Finset (Fin n))).filter (fun Y => Y i = A),
            seedMeas.real {ω | final π ω = Y}) * (∑ g ∈ A, w i g) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun Y hY => ?_
        rw [(Finset.mem_filter.mp hY).2]
      rw [h_inner]
      congr 1
      let fib := (Finset.univ : Finset (Fin m → Finset (Fin n))).filter (fun Y => Y i = A)
      have hdisj : (↑fib : Set (Fin m → Finset (Fin n))).PairwiseDisjoint
          (fun Y => {ω : Fin n → ℝ | final π ω = Y}) := by
        intro Y₁ _ Y₂ _ hne
        exact Set.disjoint_left.mpr fun ω h1 h2 => hne (h1.symm.trans h2)
      have hunion_fib : (⋃ Y ∈ fib, {ω : Fin n → ℝ | final π ω = Y}) =
          {ω : Fin n → ℝ | singleTraj i π ω n = A} := by
        ext ω
        simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
          fib, ← hfinal_dec π ω i]
        exact ⟨fun ⟨Y, hYi, hωY⟩ => hωY ▸ hYi, fun h => ⟨final π ω, h, rfl⟩⟩
      rw [← hunion_fib]
      exact (measureReal_biUnion_finset hdisj (fun Y _ => h_meas_final π Y)).symm
    dsimp only [algRepresentedWelfareProb, alg]
    have h_swap_pi : (∑ Y : Fin m → Finset (Fin n),
          ((1 / (Nat.factorial n : ℝ)) *
            ∑ π : Equiv.Perm (Fin n), seedMeas.real {ω | final π ω = Y}) *
            (allocWelfare v Y).unbotD 0) =
        (1 / (Nat.factorial n : ℝ)) *
          ∑ π : Equiv.Perm (Fin n),
            ∑ Y : Fin m → Finset (Fin n),
              seedMeas.real {ω | final π ω = Y} * (allocWelfare v Y).unbotD 0 := by
      rw [Finset.mul_sum]
      calc (∑ Y : Fin m → Finset (Fin n),
              ((1 / (Nat.factorial n : ℝ)) *
                ∑ π : Equiv.Perm (Fin n), seedMeas.real {ω | final π ω = Y}) *
                (allocWelfare v Y).unbotD 0)
          = ∑ Y : Fin m → Finset (Fin n), ∑ π : Equiv.Perm (Fin n),
              (1 / (Nat.factorial n : ℝ)) *
                (seedMeas.real {ω | final π ω = Y} * (allocWelfare v Y).unbotD 0) := by
            refine Finset.sum_congr rfl fun Y _ => ?_
            rw [Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun π _ => by ring
        _ = ∑ π : Equiv.Perm (Fin n), ∑ Y : Fin m → Finset (Fin n),
              (1 / (Nat.factorial n : ℝ)) *
                (seedMeas.real {ω | final π ω = Y} * (allocWelfare v Y).unbotD 0) := Finset.sum_comm
        _ = ∑ π : Equiv.Perm (Fin n),
              (1 / (Nat.factorial n : ℝ)) *
                ∑ Y : Fin m → Finset (Fin n),
                  seedMeas.real {ω | final π ω = Y} * (allocWelfare v Y).unbotD 0 := by
            exact Finset.sum_congr rfl fun π _ => (Finset.mul_sum _ _ _).symm
    rw [h_swap_pi, Finset.sum_congr rfl fun π _ => h_per_pi π]
    rw [Finset.mul_sum]
    have h_to_i : (∑ π : Equiv.Perm (Fin n),
          (1 / (Nat.factorial n : ℝ)) *
            ∑ i : Fin m, ∑ A : Finset (Fin n),
              seedMeas.real {ω | singleTraj i π ω n = A} * (∑ g ∈ A, w i g)) =
        ∑ i : Fin m, ∑ π : Equiv.Perm (Fin n),
          (1 / (Nat.factorial n : ℝ)) *
            ∑ A : Finset (Fin n),
              seedMeas.real {ω | singleTraj i π ω n = A} * (∑ g ∈ A, w i g) := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    rw [h_to_i]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h_to_A : (∑ π : Equiv.Perm (Fin n),
          (1 / (Nat.factorial n : ℝ)) *
            ∑ A : Finset (Fin n),
              seedMeas.real {ω | singleTraj i π ω n = A} * (∑ g ∈ A, w i g)) =
        ∑ A : Finset (Fin n),
          ((1 / (Nat.factorial n : ℝ)) *
            ∑ π : Equiv.Perm (Fin n), seedMeas.real {ω | singleTraj i π ω n = A}) *
            (∑ g ∈ A, w i g) := by
      calc (∑ π : Equiv.Perm (Fin n),
              (1 / (Nat.factorial n : ℝ)) *
                ∑ A : Finset (Fin n),
                  seedMeas.real {ω | singleTraj i π ω n = A} * (∑ g ∈ A, w i g))
          = ∑ π : Equiv.Perm (Fin n), ∑ A : Finset (Fin n),
              (1 / (Nat.factorial n : ℝ)) *
                (seedMeas.real {ω | singleTraj i π ω n = A} * (∑ g ∈ A, w i g)) :=
            Finset.sum_congr rfl fun π _ => Finset.mul_sum _ _ _
        _ = ∑ A : Finset (Fin n), ∑ π : Equiv.Perm (Fin n),
              (1 / (Nat.factorial n : ℝ)) *
                (seedMeas.real {ω | singleTraj i π ω n = A} * (∑ g ∈ A, w i g)) := Finset.sum_comm
        _ = ∑ A : Finset (Fin n),
              ((1 / (Nat.factorial n : ℝ)) *
                ∑ π : Equiv.Perm (Fin n), seedMeas.real {ω | singleTraj i π ω n = A}) *
                (∑ g ∈ A, w i g) := by
            refine Finset.sum_congr rfl fun A _ => ?_
            rw [Finset.mul_sum Finset.univ _ (1 / (Nat.factorial n : ℝ)),
                Finset.sum_mul Finset.univ _ (∑ g ∈ A, w i g)]
            exact Finset.sum_congr rfl fun π _ => by ring
    rw [h_to_A]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [h_marginal_univ i A]
  let E_bid : Fin m → Finset (Fin n) → ℝ :=
    fun i S => ∑ A : Finset (Fin n), μ i S A * (∑ x ∈ A, w i x)
  let E_tot : Finset (Fin n) → ℝ :=
    fun S => ∑ i : Fin m, E_bid i S
  have h_Etot_le_s : ∀ S : Finset (Fin n), S.card ≤ s → E_tot S = 0 := by
    intro S hS
    refine Finset.sum_eq_zero fun i _ => ?_
    dsimp only [E_bid]
    rw [(hμq i).1 S hS]
    refine Finset.sum_eq_zero fun A _ => ?_
    by_cases hA : A = ∅
    · subst hA; simp
    · simp [hA]
  have h_g_inner : ∀ (i : Fin m) (S : Finset (Fin n)), s < S.card → ∀ g ∈ S,
      (∑ B : Finset (Fin n),
        (μ i (S.erase g) B + (if g ∈ B then q i S g (B.erase g) else 0) - q i S g B) *
          (∑ x ∈ B, w i x)) =
      E_bid i (S.erase g) + (∑ A : Finset (Fin n), q i S g A) * w i g := by
    intro i S hs_lt g _
    obtain ⟨_, hq_supp, _, _⟩ := (hμq i).2.2 S hs_lt
    have hsplit : (∑ B : Finset (Fin n),
          (μ i (S.erase g) B + (if g ∈ B then q i S g (B.erase g) else 0) - q i S g B) *
            (∑ x ∈ B, w i x)) =
        E_bid i (S.erase g) +
        (∑ B : Finset (Fin n),
          (if g ∈ B then q i S g (B.erase g) else 0) * (∑ x ∈ B, w i x)) -
        (∑ B : Finset (Fin n), q i S g B * (∑ x ∈ B, w i x)) := by
      dsimp only [E_bid]
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun B _ => by ring
    let S_in := (Finset.univ : Finset (Finset (Fin n))).filter (fun B => g ∈ B)
    let S_out := (Finset.univ : Finset (Finset (Fin n))).filter (fun A => g ∉ A)
    have h_in_eq : (∑ B : Finset (Fin n),
          (if g ∈ B then q i S g (B.erase g) else 0) * (∑ x ∈ B, w i x)) =
        ∑ B ∈ S_in, q i S g (B.erase g) * (∑ x ∈ B, w i x) := by
      rw [← Finset.sum_subset (Finset.subset_univ S_in)]
      · refine Finset.sum_congr rfl fun B hB => ?_
        rw [if_pos (Finset.mem_filter.mp hB).2]
      · intro B _ hBnot
        have hgB : g ∉ B := fun hg => hBnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩)
        rw [if_neg hgB, zero_mul]
    have h_bij : (∑ A ∈ S_out, q i S g A * (w i g + ∑ x ∈ A, w i x)) =
        ∑ B ∈ S_in, q i S g (B.erase g) * (∑ x ∈ B, w i x) := by
      refine Finset.sum_nbij' (fun A => insert g A) (fun B => B.erase g) ?_ ?_ ?_ ?_ ?_
      · intro A _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_insert_self g A⟩
      · intro B _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.notMem_erase g B⟩
      · intro A hA
        exact Finset.erase_insert (Finset.mem_filter.mp hA).2
      · intro B hB
        exact Finset.insert_erase (Finset.mem_filter.mp hB).2
      · intro A hA
        have hgA : g ∉ A := (Finset.mem_filter.mp hA).2
        rw [Finset.erase_insert hgA, Finset.sum_insert hgA]
    have h_out_eq : (∑ A ∈ S_out, q i S g A * (w i g + ∑ x ∈ A, w i x)) =
        ∑ A : Finset (Fin n), q i S g A * (w i g + ∑ x ∈ A, w i x) := by
      refine Finset.sum_subset (Finset.subset_univ S_out) fun A _ hAnot => ?_
      have hgA : g ∈ A := by
        by_contra hng
        exact hAnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hng⟩)
      have hq0 : q i S g A = 0 := by
        by_contra hq_ne
        exact Finset.notMem_erase g S ((hq_supp g A hq_ne).2.2.1 hgA)
      rw [hq0, zero_mul]
    have h_expand : (∑ A : Finset (Fin n), q i S g A * (w i g + ∑ x ∈ A, w i x)) =
        (∑ A : Finset (Fin n), q i S g A) * w i g +
        ∑ A : Finset (Fin n), q i S g A * (∑ x ∈ A, w i x) := by
      calc (∑ A : Finset (Fin n), q i S g A * (w i g + ∑ x ∈ A, w i x))
          = (∑ A : Finset (Fin n), q i S g A * w i g) +
            ∑ A : Finset (Fin n), q i S g A * (∑ x ∈ A, w i x) := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun A _ => mul_add _ _ _
        _ = (∑ A : Finset (Fin n), q i S g A) * w i g +
            ∑ A : Finset (Fin n), q i S g A * (∑ x ∈ A, w i x) := by
            rw [← Finset.sum_mul]
    rw [hsplit, h_in_eq, ← h_bij, h_out_eq, h_expand]
    ring
  have h_Ebid_step : ∀ (i : Fin m) (S : Finset (Fin n)), s < S.card →
      E_bid i S = (1 / (S.card : ℝ)) * (∑ g ∈ S, E_bid i (S.erase g)) +
        ((s : ℝ) / ((S.card : ℝ) * ((S.card - 1 : ℕ) : ℝ))) * (∑ g ∈ X S i, w i g) := by
    intro i S hs_lt
    obtain ⟨_, hq_supp, hq_sum, hμ_rec⟩ := (hμq i).2.2 S hs_lt
    have hSc_ne : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hSc1_ne : (((S.card - 1 : ℕ) : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h1 : E_bid i S = (1 / (S.card : ℝ)) *
        ∑ g ∈ S, (E_bid i (S.erase g) + (∑ A : Finset (Fin n), q i S g A) * w i g) := by
      calc E_bid i S
          = ∑ B : Finset (Fin n),
              ((1 / (S.card : ℝ)) * ∑ g ∈ S,
                (μ i (S.erase g) B + (if g ∈ B then q i S g (B.erase g) else 0) - q i S g B)) *
                (∑ x ∈ B, w i x) := by
            dsimp only [E_bid]
            exact Finset.sum_congr rfl fun B _ => by rw [hμ_rec B]
        _ = ∑ B : Finset (Fin n), ∑ g ∈ S,
              (1 / (S.card : ℝ)) *
                ((μ i (S.erase g) B + (if g ∈ B then q i S g (B.erase g) else 0) - q i S g B) *
                  (∑ x ∈ B, w i x)) := by
            refine Finset.sum_congr rfl fun B _ => ?_
            rw [Finset.mul_sum S _ (1 / (S.card : ℝ)),
                Finset.sum_mul S _ (∑ x ∈ B, w i x)]
            exact Finset.sum_congr rfl fun g _ => by ring
        _ = ∑ g ∈ S, ∑ B : Finset (Fin n),
              (1 / (S.card : ℝ)) *
                ((μ i (S.erase g) B + (if g ∈ B then q i S g (B.erase g) else 0) - q i S g B) *
                  (∑ x ∈ B, w i x)) := Finset.sum_comm
        _ = (1 / (S.card : ℝ)) * ∑ g ∈ S, ∑ B : Finset (Fin n),
              (μ i (S.erase g) B + (if g ∈ B then q i S g (B.erase g) else 0) - q i S g B) *
                (∑ x ∈ B, w i x) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun g _ => (Finset.mul_sum _ _ _).symm
        _ = (1 / (S.card : ℝ)) *
              ∑ g ∈ S, (E_bid i (S.erase g) + (∑ A : Finset (Fin n), q i S g A) * w i g) := by
            congr 1
            exact Finset.sum_congr rfl fun g hgS => h_g_inner i S hs_lt g hgS
    have hq_w_sum : (∑ g ∈ S, (∑ A : Finset (Fin n), q i S g A) * w i g) =
        ((s : ℝ) / ((S.card - 1 : ℕ) : ℝ)) * (∑ g ∈ X S i, w i g) := by
      have hsub_eq : (∑ g ∈ X S i, (∑ A : Finset (Fin n), q i S g A) * w i g) =
          ∑ g ∈ S, (∑ A : Finset (Fin n), q i S g A) * w i g := by
        refine Finset.sum_subset ((hX S).1.1 i) fun g _ hg_not => ?_
        have hq0 : ∀ A, q i S g A = 0 := by
          intro A
          by_contra hne
          exact hg_not (hq_supp g A hne).2.1
        simp [hq0]
      rw [← hsub_eq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g hgX => ?_
      rw [hq_sum g hgX]
    rw [h1, Finset.sum_add_distrib, mul_add, hq_w_sum]
    congr 1
    field_simp [hSc_ne, hSc1_ne]
  have h_Etot_step : ∀ S : Finset (Fin n), s < S.card →
      (1 / (S.card : ℝ)) * (∑ g ∈ S, E_tot (S.erase g)) +
        ((s : ℝ) / ((S.card : ℝ) * ((S.card - 1 : ℕ) : ℝ))) * optWelfareOn v S ≤
      E_tot S := by
    intro S hs_lt
    have hsum_i : E_tot S =
        (1 / (S.card : ℝ)) * (∑ g ∈ S, E_tot (S.erase g)) +
        ((s : ℝ) / ((S.card : ℝ) * ((S.card - 1 : ℕ) : ℝ))) *
          (∑ i : Fin m, ∑ g ∈ X S i, w i g) := by
      dsimp only [E_tot]
      rw [Finset.sum_congr rfl fun i _ => h_Ebid_step i S hs_lt, Finset.sum_add_distrib]
      congr 1
      · rw [← Finset.mul_sum, Finset.sum_comm]
      · rw [← Finset.mul_sum]
    have hc_nn : (0 : ℝ) ≤ (s : ℝ) / ((S.card : ℝ) * ((S.card - 1 : ℕ) : ℝ)) := by positivity
    have hopt_le := mul_le_mul_of_nonneg_left (hX S).2.2 hc_nn
    linarith
  have h_opt_sub : ∀ S : Finset (Fin n),
      (∑ i : Fin m, ∑ g ∈ X Finset.univ i ∩ S, w i g) ≤ optWelfareOn v S := by
    intro S
    let YS : Fin m → Finset (Fin n) := fun i => X Finset.univ i ∩ S
    have hYS_alloc : IsAllocOf S YS := by
      refine ⟨fun i => Finset.inter_subset_right, fun i₁ i₂ h12 => ?_⟩
      exact Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left
        ((hX Finset.univ).1.2 i₁ i₂ h12)
    have hYS_ind : ∀ i : Fin m, (M i).Indep (YS i : Set (Fin n)) :=
      fun i => ((hX Finset.univ).2.1 i).subset (Finset.coe_subset.mpr Finset.inter_subset_left)
    let F_S := (Finset.univ : Finset (Fin m → Finset (Fin n))).filter (fun Y => IsAllocOf S Y)
    have hYS_mem : YS ∈ F_S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hYS_alloc⟩
    have hle_sup : allocWelfare v YS ≤ F_S.sup (allocWelfare v) :=
      Finset.le_sup (f := allocWelfare v) hYS_mem
    rw [hwelf_ind YS hYS_ind] at hle_sup
    have hsup_ne : F_S.sup (allocWelfare v) ≠ ⊥ := by
      intro hb; rw [hb, le_bot_iff] at hle_sup; exact WithBot.coe_ne_bot hle_sup
    obtain ⟨r, hr⟩ := WithBot.ne_bot_iff_exists.mp hsup_ne
    dsimp only [optWelfareOn]
    change _ ≤ (F_S.sup (allocWelfare v)).unbotD 0
    rw [← hr, WithBot.unbotD_coe]
    rw [← hr, WithBot.coe_le_coe] at hle_sup
    exact hle_sup
  let Pcard : ℕ → Finset (Finset (Fin n)) :=
    fun k => (Finset.univ : Finset (Fin n)).powersetCard k
  let Avg : ℕ → ℝ :=
    fun k => (1 / (Nat.choose n k : ℝ)) * ∑ S ∈ Pcard k, E_tot S
  have h_Avg_s : Avg s = 0 := by
    dsimp only [Avg]
    have h0 : ∑ S ∈ Pcard s, E_tot S = 0 := by
      refine Finset.sum_eq_zero fun S hS => ?_
      have hcard : S.card = s := (Finset.mem_powersetCard.mp hS).2
      exact h_Etot_le_s S (by omega)
    rw [h0, mul_zero]
  have h_Avg_n : Avg n = E_tot Finset.univ := by
    have hPn : Pcard n = {Finset.univ} := by
      ext S
      simp only [Pcard, Finset.mem_powersetCard, Finset.subset_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => Finset.eq_univ_of_card S (h.trans (Fintype.card_fin n).symm),
        fun h => by subst h; simp⟩
    dsimp only [Avg]
    rw [hPn, Finset.sum_singleton, Nat.choose_self]
    simp
  have h_step_Ico : ∀ j ∈ Finset.Ico s n,
      ((s : ℝ) / (n : ℝ)) * (1 / (j : ℝ)) * optWelfare v ≤ Avg (j + 1) - Avg j := by
    intro j hj
    rcases Finset.mem_Ico.mp hj with ⟨hsj, hjn⟩
    have hj_pos : 0 < j := by omega
    have hj_ne : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hj1_ne : ((j + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hnj_ne : ((n - j : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hch_j_pos : 0 < Nat.choose n j := Nat.choose_pos (by omega)
    have hch_j1_pos : 0 < Nat.choose n (j + 1) := Nat.choose_pos (by omega)
    have hch_j_ne : (Nat.choose n j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hch_j_pos.ne'
    have hch_j1_ne : (Nat.choose n (j + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hch_j1_pos.ne'
    have h_double_sum :
        (∑ S ∈ Pcard (j + 1), ∑ g ∈ S, E_tot (S.erase g)) =
        ((n - j : ℕ) : ℝ) * ∑ T ∈ Pcard j, E_tot T := by
      have hsig1 : (∑ S ∈ Pcard (j + 1), ∑ g ∈ S, E_tot (S.erase g)) =
          ∑ p ∈ (Pcard (j + 1)).sigma (fun S => S), E_tot (p.1.erase p.2) :=
        Finset.sum_sigma' (Pcard (j + 1)) (fun S => S) (fun S g => E_tot (S.erase g))
      have hsig2 : (∑ T ∈ Pcard j, ∑ _ ∈ (Finset.univ : Finset (Fin n)) \ T, E_tot T) =
          ∑ q ∈ (Pcard j).sigma (fun T => (Finset.univ : Finset (Fin n)) \ T), E_tot q.1 :=
        Finset.sum_sigma' (Pcard j) (fun T => (Finset.univ : Finset (Fin n)) \ T)
          (fun T _ => E_tot T)
      have hbij : (∑ p ∈ (Pcard (j + 1)).sigma (fun S => S), E_tot (p.1.erase p.2)) =
          ∑ q ∈ (Pcard j).sigma (fun T => (Finset.univ : Finset (Fin n)) \ T), E_tot q.1 := by
        refine Finset.sum_nbij'
          (fun p => ⟨p.1.erase p.2, p.2⟩)
          (fun q => ⟨insert q.2 q.1, q.2⟩) ?_ ?_ ?_ ?_ ?_
        · intro p hp
          rcases Finset.mem_sigma.mp hp with ⟨hpS, hpg⟩
          have hScard : p.1.card = j + 1 := (Finset.mem_powersetCard.mp hpS).2
          refine Finset.mem_sigma.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, ?_⟩
          · rw [Finset.card_erase_of_mem hpg, hScard]; omega
          · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, Finset.notMem_erase _ _⟩
        · intro q hq
          rcases Finset.mem_sigma.mp hq with ⟨hqT, hqg⟩
          have hTcard : q.1.card = j := (Finset.mem_powersetCard.mp hqT).2
          have hqg_not : q.2 ∉ q.1 := (Finset.mem_sdiff.mp hqg).2
          refine Finset.mem_sigma.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩,
            Finset.mem_insert_self _ _⟩
          rw [Finset.card_insert_of_notMem hqg_not, hTcard]
        · intro p hp
          rcases p with ⟨S, g⟩
          have hpg : g ∈ S := (Finset.mem_sigma.mp hp).2
          simp only [Finset.insert_erase hpg]
        · intro q hq
          rcases q with ⟨T, g⟩
          have hqg_not : g ∉ T := (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hq).2).2
          simp only [Finset.erase_insert hqg_not]
        · intro _ _; rfl
      rw [hsig1, hbij, ← hsig2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun T hT => ?_
      have hTcard : T.card = j := (Finset.mem_powersetCard.mp hT).2
      have hsdiff_card : ((Finset.univ : Finset (Fin n)) \ T).card = n - j := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hTcard]
      rw [Finset.sum_const, nsmul_eq_mul, hsdiff_card]
    have h_avg_prev : (1 / (Nat.choose n (j + 1) : ℝ)) *
        (∑ S ∈ Pcard (j + 1), (1 / ((j + 1 : ℕ) : ℝ)) * (∑ g ∈ S, E_tot (S.erase g))) =
        Avg j := by
      rw [← Finset.mul_sum, h_double_sum]
      dsimp only [Avg]
      have hchoose_cast : (Nat.choose n (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) =
          (Nat.choose n j : ℝ) * ((n - j : ℕ) : ℝ) := by
        exact_mod_cast Nat.choose_succ_right_eq n j
      field_simp [hch_j1_ne, hj1_ne, hch_j_ne]
      linear_combination -((∑ T ∈ Pcard j, E_tot T) * hchoose_cast)
    have h_pg_card : ∀ g : Fin n,
        ((Pcard (j + 1)).filter (fun S => g ∈ S)).card = Nat.choose (n - 1) j := by
      intro g
      have hbij_card : ((Pcard (j + 1)).filter (fun S => g ∈ S)).card =
          (((Finset.univ : Finset (Fin n)).erase g).powersetCard j).card := by
        refine Finset.card_bij (fun S _ => S.erase g) ?_ ?_ ?_
        · intro S hS
          rcases Finset.mem_filter.mp hS with ⟨hSP, hgS⟩
          have hScard : S.card = j + 1 := (Finset.mem_powersetCard.mp hSP).2
          refine Finset.mem_powersetCard.mpr ⟨Finset.erase_subset_erase g (Finset.subset_univ S), ?_⟩
          rw [Finset.card_erase_of_mem hgS, hScard]; omega
        · intro S₁ hS₁ S₂ hS₂ heq
          dsimp only at heq
          have hg1 : g ∈ S₁ := (Finset.mem_filter.mp hS₁).2
          have hg2 : g ∈ S₂ := (Finset.mem_filter.mp hS₂).2
          rw [← Finset.insert_erase hg1, heq, Finset.insert_erase hg2]
        · intro T hT
          rcases Finset.mem_powersetCard.mp hT with ⟨hTsub, hTcard⟩
          have hgT : g ∉ T := fun hg => Finset.notMem_erase g Finset.univ (hTsub hg)
          refine ⟨insert g T, ?_, Finset.erase_insert hgT⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩,
            Finset.mem_insert_self _ _⟩
          rw [Finset.card_insert_of_notMem hgT, hTcard]
      rw [hbij_card, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ g),
        Finset.card_univ, Fintype.card_fin]
    have h_rr_sum :
        (∑ S ∈ Pcard (j + 1), ∑ i : Fin m, ∑ g ∈ X Finset.univ i ∩ S, w i g) =
        (Nat.choose (n - 1) j : ℝ) * (∑ i : Fin m, ∑ g ∈ X Finset.univ i, w i g) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h_inter_ite : ∀ S : Finset (Fin n),
          (∑ g ∈ X Finset.univ i ∩ S, w i g) =
          ∑ g ∈ X Finset.univ i, (if g ∈ S then w i g else 0) := by
        intro S
        calc (∑ g ∈ X Finset.univ i ∩ S, w i g)
            = ∑ g ∈ X Finset.univ i ∩ S, (if g ∈ S then w i g else 0) :=
              Finset.sum_congr rfl fun g hg => (if_pos (Finset.mem_inter.mp hg).2).symm
          _ = ∑ g ∈ X Finset.univ i, (if g ∈ S then w i g else 0) := by
              refine Finset.sum_subset Finset.inter_subset_left fun g hgX hg_not => ?_
              have hgS : g ∉ S := fun hgS => hg_not (Finset.mem_inter.mpr ⟨hgX, hgS⟩)
              exact if_neg hgS
      rw [Finset.sum_congr rfl fun S _ => h_inter_ite S, Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      let Pg := (Pcard (j + 1)).filter (fun S => g ∈ S)
      have h_ite_Pg : (∑ S ∈ Pcard (j + 1), (if g ∈ S then w i g else 0)) =
          ∑ _ ∈ Pg, w i g := by
        rw [← Finset.sum_subset (Finset.filter_subset (fun S => g ∈ S) (Pcard (j + 1)))]
        · exact Finset.sum_congr rfl fun S hS => if_pos (Finset.mem_filter.mp hS).2
        · intro S hSP hSnot
          have hgS : g ∉ S := fun hg => hSnot (Finset.mem_filter.mpr ⟨hSP, hg⟩)
          exact if_neg hgS
      rw [h_ite_Pg, Finset.sum_const, nsmul_eq_mul, h_pg_card g]
    have h_rr_opt :
        (((j + 1 : ℕ) : ℝ) / (n : ℝ)) * optWelfare v ≤
        (1 / (Nat.choose n (j + 1) : ℝ)) * ∑ S ∈ Pcard (j + 1), optWelfareOn v S := by
      have hsum_le1 :
          (Nat.choose (n - 1) j : ℝ) * optWelfare v ≤
          ∑ S ∈ Pcard (j + 1), optWelfareOn v S := by
        have h1 : (Nat.choose (n - 1) j : ℝ) * optWelfare v ≤
            (Nat.choose (n - 1) j : ℝ) * (∑ i : Fin m, ∑ g ∈ X Finset.univ i, w i g) := by
          dsimp only [optWelfare]
          exact mul_le_mul_of_nonneg_left (hX Finset.univ).2.2 (Nat.cast_nonneg _)
        have h2 : (∑ S ∈ Pcard (j + 1), ∑ i : Fin m, ∑ g ∈ X Finset.univ i ∩ S, w i g) ≤
            ∑ S ∈ Pcard (j + 1), optWelfareOn v S :=
          Finset.sum_le_sum fun S _ => h_opt_sub S
        linarith
      have h_n_choose : (n : ℝ) * (Nat.choose (n - 1) j : ℝ) =
          (Nat.choose n (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
        have hnat := Nat.add_one_mul_choose_eq (n - 1) j
        have hn1 : n - 1 + 1 = n := by omega
        rw [hn1] at hnat
        exact_mod_cast hnat
      have hcoeff_eq : (((j + 1 : ℕ) : ℝ) / (n : ℝ)) =
          (1 / (Nat.choose n (j + 1) : ℝ)) * (Nat.choose (n - 1) j : ℝ) := by
        field_simp [hn_ne, hch_j1_ne]
        linarith
      rw [hcoeff_eq, mul_assoc]
      exact mul_le_mul_of_nonneg_left hsum_le1 (by positivity)
    have h_step_sum :
        (∑ S ∈ Pcard (j + 1),
          ((1 / ((j + 1 : ℕ) : ℝ)) * (∑ g ∈ S, E_tot (S.erase g)) +
           ((s : ℝ) / (((j + 1 : ℕ) : ℝ) * (j : ℝ))) * optWelfareOn v S)) ≤
        ∑ S ∈ Pcard (j + 1), E_tot S := by
      refine Finset.sum_le_sum fun S hS => ?_
      have hScard : S.card = j + 1 := (Finset.mem_powersetCard.mp hS).2
      have hs_lt : s < S.card := by omega
      have hSc1 : (S.card - 1 : ℕ) = j := by omega
      have hstep := h_Etot_step S hs_lt
      rw [hSc1, hScard] at hstep
      exact hstep
    have h_avg_ineq :
        Avg j +
        ((s : ℝ) / (((j + 1 : ℕ) : ℝ) * (j : ℝ))) *
          ((1 / (Nat.choose n (j + 1) : ℝ)) * ∑ S ∈ Pcard (j + 1), optWelfareOn v S) ≤
        Avg (j + 1) := by
      have hmul := mul_le_mul_of_nonneg_left h_step_sum
        (show (0 : ℝ) ≤ 1 / (Nat.choose n (j + 1) : ℝ) by positivity)
      rw [Finset.sum_add_distrib, mul_add, h_avg_prev] at hmul
      have hassoc : (1 / (Nat.choose n (j + 1) : ℝ)) *
          ∑ S ∈ Pcard (j + 1),
            ((s : ℝ) / (((j + 1 : ℕ) : ℝ) * (j : ℝ))) * optWelfareOn v S =
          ((s : ℝ) / (((j + 1 : ℕ) : ℝ) * (j : ℝ))) *
            ((1 / (Nat.choose n (j + 1) : ℝ)) * ∑ S ∈ Pcard (j + 1), optWelfareOn v S) := by
        rw [← Finset.mul_sum]; ring
      rw [hassoc] at hmul
      exact hmul
    have h_rr_scaled :
        ((s : ℝ) / (n : ℝ)) * (1 / (j : ℝ)) * optWelfare v ≤
        ((s : ℝ) / (((j + 1 : ℕ) : ℝ) * (j : ℝ))) *
          ((1 / (Nat.choose n (j + 1) : ℝ)) * ∑ S ∈ Pcard (j + 1), optWelfareOn v S) := by
      have hm := mul_le_mul_of_nonneg_left h_rr_opt
        (show (0 : ℝ) ≤ (s : ℝ) / (((j + 1 : ℕ) : ℝ) * (j : ℝ)) by positivity)
      have hfactor : ((s : ℝ) / (((j + 1 : ℕ) : ℝ) * (j : ℝ))) *
          ((((j + 1 : ℕ) : ℝ) / (n : ℝ)) * optWelfare v) =
          ((s : ℝ) / (n : ℝ)) * (1 / (j : ℝ)) * optWelfare v := by
        field_simp [hj1_ne, hj_ne, hn_ne]
      linarith
    linarith
  have h_tele_bound : secretaryCutoffConst n s * optWelfare v ≤ E_tot Finset.univ := by
    have hsum_le : (∑ j ∈ Finset.Ico s n,
          ((s : ℝ) / (n : ℝ)) * (1 / (j : ℝ)) * optWelfare v) ≤
        ∑ j ∈ Finset.Ico s n, (Avg (j + 1) - Avg j) :=
      Finset.sum_le_sum fun j hj => h_step_Ico j hj
    have hlhs : (∑ j ∈ Finset.Ico s n,
          ((s : ℝ) / (n : ℝ)) * (1 / (j : ℝ)) * optWelfare v) =
        secretaryCutoffConst n s * optWelfare v := by
      dsimp only [secretaryCutoffConst]
      rw [Finset.mul_sum, Finset.sum_mul]
    have hrhs : (∑ j ∈ Finset.Ico s n, (Avg (j + 1) - Avg j)) = E_tot Finset.univ := by
      rw [Finset.sum_Ico_sub Avg hsn.le, h_Avg_n, h_Avg_s, sub_zero]
    linarith
  refine ⟨fun ω π k hk =>
      ⟨(h_pathwise_decouple ω π k hk).2.1, (h_pathwise_decouple ω π k hk).2.2.1⟩, ?_⟩
  rw [h_exp_eq]
  exact WithBot.coe_le_coe.mpr h_tele_bound

theorem lem_pos_oracle_and_opt_alloc : (∀ (n : ℕ) (vi vi' : ItemValuation n) (T : Finset (Fin n)),
      (∀ Y ⊆ T, vi Y = vi' Y) →
        ∀ X ⊆ T, obsPosIndep vi T X ↔ obsPosIndep vi' T X) ∧
    (∀ (n : ℕ) (M : Matroid (Fin n)) (w : Fin n → ℝ) (T X : Finset (Fin n)),
      X ⊆ T →
        (obsPosIndep (weightedMatroidVal M w) T X ↔
          (M.restrict {g : Fin n | 0 < w g}).Indep (X : Set (Fin n)))) ∧
    (∃ prefixPosOptAlloc :
        ∀ (n m : ℕ), (Fin m → ItemValuation n) → Finset (Fin n) → (Fin m → Finset (Fin n)),
      (∀ (n m : ℕ) (v v' : Fin m → ItemValuation n) (S : Finset (Fin n)),
        (∀ i : Fin m, ∀ T ⊆ S, v i T = v' i T) →
          prefixPosOptAlloc n m v S = prefixPosOptAlloc n m v' S) ∧
      (∀ (n m : ℕ) (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ)
          (S : Finset (Fin n)),
        let v := fun i => weightedMatroidVal (M i) (w i)
        let XS := prefixPosOptAlloc n m v S
        IsAllocOf S XS ∧
        (∀ i : Fin m, ((M i).restrict {g : Fin n | 0 < w i g}).Indep (XS i : Set (Fin n))) ∧
        optWelfareOn v S = ∑ i : Fin m, ∑ g ∈ XS i, w i g)) ∧
    (∀ (n m : ℕ) (c : ℝ) (isTernary : Fin m → Bool) (alg₀ : OnlineWelfareAlg n m),
      (∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
        (∀ i, if isTernary i then IsTernaryMatroid (M i) else IsBinaryMatroid (M i)) →
          let v := fun i => weightedMatroidVal (M i) (w i)
          (∀ (ω : alg₀.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
            let st := runDetWelfareSteps (alg₀.det ω) v π k hk
            IsAllocOf st.1.toFinset st.2 ∧
            ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
          (((c * optWelfare v : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg₀ v)) →
      ∃ alg : OnlineWelfareAlg n m,
        (∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
          (∀ i, if isTernary i then IsTernaryMatroid (M i) else IsBinaryMatroid (M i)) →
            let v := fun i => weightedMatroidVal (M i) (w i)
            (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
              let st := runDetWelfareSteps (alg.det ω) v π k hk
              IsAllocOf st.1.toFinset st.2 ∧
              ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
            (((c * optWelfare v : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg v)) ∧
        (∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
          (∀ i g, 0 ≤ w i g) →
          (∀ i, if isTernary i then IsTernaryMatroid (M i) else IsBinaryMatroid (M i)) →
            let vR := fun i => weightedMatroidRankVal (M i) (w i)
            (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
              let st := runDetWelfareSteps (alg.det ω) vR π k hk
              IsAllocOf st.1.toFinset st.2 ∧
              ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
            (((c * optWelfare vR : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg vR))) :=
by
  have h_obs_loc : ∀ (n : ℕ) (vi vi' : ItemValuation n) (T : Finset (Fin n)),
      (∀ Y ⊆ T, vi Y = vi' Y) →
        ∀ X ⊆ T, obsPosIndep vi T X ↔ obsPosIndep vi' T X := by
    intro n vi vi' T h_eq X hXT
    have hX : vi X = vi' X := h_eq X hXT
    have hsg : ∀ g ∈ X, vi {g} = vi' {g} := fun g hg =>
      h_eq {g} (Finset.singleton_subset_iff.mpr (hXT hg))
    have hsum : (∑ g ∈ X, (vi {g}).unbotD 0) = (∑ g ∈ X, (vi' {g}).unbotD 0) :=
      Finset.sum_congr rfl (fun g hg => by rw [hsg g hg])
    dsimp only [obsPosIndep]
    rw [hX, hsum]
    constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨h1, h2, ?_, h4⟩ <;> intro g hg
    · rw [← hsg g hg]; exact h3 g hg
    · rw [hsg g hg]; exact h3 g hg
  have h_obs_val : ∀ (n : ℕ) (M : Matroid (Fin n)) (w : Fin n → ℝ) (T X : Finset (Fin n)),
      X ⊆ T →
        (obsPosIndep (weightedMatroidVal M w) T X ↔
          (M.restrict {g : Fin n | 0 < w g}).Indep (X : Set (Fin n))) := by
    intro n M w T X hXT
    rw [Matroid.restrict_indep_iff]
    constructor
    · rintro ⟨_, hne, hpos, _⟩
      have hind : M.Indep (X : Set (Fin n)) := by
        by_contra hni
        dsimp only [weightedMatroidVal] at hne
        rw [if_neg hni] at hne
        exact hne rfl
      refine ⟨hind, ?_⟩
      intro g hgX
      have hgX' : g ∈ X := Finset.mem_coe.mp hgX
      have hind_sg : M.Indep (({g} : Finset (Fin n)) : Set (Fin n)) :=
        hind.subset (Finset.coe_subset.mpr (Finset.singleton_subset_iff.mpr hgX'))
      have hpos_g := hpos g hgX'
      dsimp only [weightedMatroidVal] at hpos_g
      rw [if_pos hind_sg, Finset.sum_singleton, WithBot.coe_lt_coe] at hpos_g
      exact hpos_g
    · rintro ⟨hind, hX_pos⟩
      have hpos_g : ∀ g ∈ X, M.Indep (({g} : Finset (Fin n)) : Set (Fin n)) ∧ 0 < w g := by
        intro g hgX
        exact ⟨hind.subset (Finset.coe_subset.mpr (Finset.singleton_subset_iff.mpr hgX)),
          hX_pos (Finset.mem_coe.mpr hgX)⟩
      refine ⟨hXT, ?_, ?_, ?_⟩
      · dsimp only [weightedMatroidVal]
        rw [if_pos hind]
        exact WithBot.coe_ne_bot
      · intro g hgX
        dsimp only [weightedMatroidVal]
        rw [if_pos (hpos_g g hgX).1, Finset.sum_singleton, WithBot.coe_lt_coe]
        exact (hpos_g g hgX).2
      · dsimp only [weightedMatroidVal]
        rw [if_pos hind, WithBot.coe_inj]
        apply Finset.sum_congr rfl
        intro g hgX
        rw [if_pos (hpos_g g hgX).1, Finset.sum_singleton, WithBot.unbotD_coe]
  let posWeightSum : ∀ (n m : ℕ), (Fin m → ItemValuation n) → (Fin m → Finset (Fin n)) → ℝ :=
    fun _ m v X => ∑ i : Fin m, ∑ g ∈ X i, (v i {g}).unbotD 0
  let IsPosIndepAlloc : ∀ (n m : ℕ), (Fin m → ItemValuation n) → Finset (Fin n) →
      (Fin m → Finset (Fin n)) → Prop :=
    fun _ m v S X => IsAllocOf S X ∧ ∀ i : Fin m, obsPosIndep (v i) S (X i)
  let IsMaxPosAlloc : ∀ (n m : ℕ), (Fin m → ItemValuation n) → Finset (Fin n) →
      (Fin m → Finset (Fin n)) → Prop :=
    fun n m v S X => IsPosIndepAlloc n m v S X ∧
      ∀ Y : Fin m → Finset (Fin n), IsPosIndepAlloc n m v S Y →
        posWeightSum n m v Y ≤ posWeightSum n m v X
  let prefixPosOptAlloc : ∀ (n m : ℕ), (Fin m → ItemValuation n) → Finset (Fin n) →
      (Fin m → Finset (Fin n)) :=
    fun n m v S =>
      if h : ∃ X : Fin m → Finset (Fin n), IsMaxPosAlloc n m v S X then
        Classical.choose h
      else
        fun _ => ∅
  have h_opt_loc : ∀ (n m : ℕ) (v v' : Fin m → ItemValuation n) (S : Finset (Fin n)),
      (∀ i : Fin m, ∀ T ⊆ S, v i T = v' i T) →
        prefixPosOptAlloc n m v S = prefixPosOptAlloc n m v' S := by
    intro n m v v' S h_eq
    have h_pia : ∀ Z : Fin m → Finset (Fin n),
        IsPosIndepAlloc n m v S Z ↔ IsPosIndepAlloc n m v' S Z := by
      intro Z
      constructor
      · rintro ⟨h_al, h_ind⟩
        exact ⟨h_al, fun i => (h_obs_loc n (v i) (v' i) S (h_eq i) (Z i) (h_al.1 i)).mp (h_ind i)⟩
      · rintro ⟨h_al, h_ind⟩
        exact ⟨h_al, fun i => (h_obs_loc n (v i) (v' i) S (h_eq i) (Z i) (h_al.1 i)).mpr (h_ind i)⟩
    have h_pws : ∀ Z : Fin m → Finset (Fin n),
        IsAllocOf S Z → posWeightSum n m v Z = posWeightSum n m v' Z := by
      intro Z h_al
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro g hg
      have hgS : ({g} : Finset (Fin n)) ⊆ S :=
        Finset.singleton_subset_iff.mpr (h_al.1 i hg)
      rw [h_eq i {g} hgS]
    have h_pred : IsMaxPosAlloc n m v S = IsMaxPosAlloc n m v' S := by
      funext X
      apply propext
      constructor
      · rintro ⟨hX, hmax⟩
        refine ⟨(h_pia X).mp hX, ?_⟩
        intro Y hY'
        have hY := (h_pia Y).mpr hY'
        rw [← h_pws Y hY.1, ← h_pws X hX.1]
        exact hmax Y hY
      · rintro ⟨hX', hmax'⟩
        have hX := (h_pia X).mpr hX'
        refine ⟨hX, ?_⟩
        intro Y hY
        have hY' := (h_pia Y).mp hY
        rw [h_pws Y hY.1, h_pws X hX.1]
        exact hmax' Y hY'
    have h_dite : ∀ (R₁ R₂ : (Fin m → Finset (Fin n)) → Prop)
        [d₁ : Decidable (∃ X, R₁ X)] [d₂ : Decidable (∃ X, R₂ X)],
        R₁ = R₂ →
        @dite _ (∃ X, R₁ X) d₁ (fun h => Classical.choose h) (fun _ => fun _ => ∅) =
        @dite _ (∃ X, R₂ X) d₂ (fun h => Classical.choose h) (fun _ => fun _ => ∅) := by
      intro R₁ R₂ d₁ d₂ hR
      subst hR
      rw [Subsingleton.elim d₁ d₂]
    exact @h_dite (IsMaxPosAlloc n m v S) (IsMaxPosAlloc n m v' S) _ _ h_pred
  have h_opt_full : ∀ (n m : ℕ) (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ)
      (S : Finset (Fin n)),
      let v := fun i => weightedMatroidVal (M i) (w i)
      let XS := prefixPosOptAlloc n m v S
      IsAllocOf S XS ∧
      (∀ i : Fin m, ((M i).restrict {g : Fin n | 0 < w i g}).Indep (XS i : Set (Fin n))) ∧
      (((Finset.univ : Finset (Fin m → Finset (Fin n))).filter (fun X => IsAllocOf S X)).sup
        (allocWelfare v) = ((∑ i : Fin m, ∑ g ∈ XS i, w i g : ℝ) : WithBot ℝ)) ∧
      optWelfareOn v S = ∑ i : Fin m, ∑ g ∈ XS i, w i g := by
    intro n m M w S
    let v : Fin m → ItemValuation n := fun i => weightedMatroidVal (M i) (w i)
    have h_pws_ind : ∀ Y : Fin m → Finset (Fin n),
        (∀ i : Fin m, (M i).Indep (Y i : Set (Fin n))) →
        posWeightSum n m v Y = ∑ i : Fin m, ∑ g ∈ Y i, w i g ∧
        allocWelfare v Y = ((∑ i : Fin m, ∑ g ∈ Y i, w i g : ℝ) : WithBot ℝ) := by
      intro Y hY_ind
      constructor
      · apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro g hg
        have hind_sg : (M i).Indep (({g} : Finset (Fin n)) : Set (Fin n)) :=
          (hY_ind i).subset (Finset.coe_subset.mpr (Finset.singleton_subset_iff.mpr hg))
        dsimp only [v, weightedMatroidVal]
        rw [if_pos hind_sg, Finset.sum_singleton, WithBot.unbotD_coe]
      · dsimp only [allocWelfare, v, weightedMatroidVal]
        rw [WithBot.coe_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [if_pos (hY_ind i)]
    let X₀ : Fin m → Finset (Fin n) := fun _ => ∅
    have hX₀_pia : IsPosIndepAlloc n m v S X₀ := by
      refine ⟨⟨fun _ => Finset.empty_subset S, fun _ _ _ => Finset.disjoint_empty_left _⟩, ?_⟩
      intro i
      rw [h_obs_val n (M i) (w i) S ∅ (Finset.empty_subset S), Finset.coe_empty]
      exact ((M i).restrict {g : Fin n | 0 < w i g}).empty_indep
    let cand : Finset (Fin m → Finset (Fin n)) :=
      Finset.univ.filter (fun X => IsPosIndepAlloc n m v S X)
    have hX₀_mem : X₀ ∈ cand := Finset.mem_filter.mpr ⟨Finset.mem_univ X₀, hX₀_pia⟩
    obtain ⟨X_max, hX_max_mem, hX_max_le⟩ :=
      Finset.exists_max_image cand (posWeightSum n m v) ⟨X₀, hX₀_mem⟩
    have hex : ∃ X : Fin m → Finset (Fin n), IsMaxPosAlloc n m v S X :=
      ⟨X_max, (Finset.mem_filter.mp hX_max_mem).2,
        fun Y hY => hX_max_le Y (Finset.mem_filter.mpr ⟨Finset.mem_univ Y, hY⟩)⟩
    let XS := prefixPosOptAlloc n m v S
    have hXS_eq : XS = Classical.choose hex := dif_pos hex
    have hXS_max : IsMaxPosAlloc n m v S XS := by
      rw [hXS_eq]
      exact Classical.choose_spec hex
    have hXS_al : IsAllocOf S XS := hXS_max.1.1
    have hXS_ind_pos : ∀ i : Fin m,
        ((M i).restrict {g : Fin n | 0 < w i g}).Indep (XS i : Set (Fin n)) :=
      fun i => (h_obs_val n (M i) (w i) S (XS i) (hXS_al.1 i)).mp (hXS_max.1.2 i)
    have hXS_ind : ∀ i : Fin m, (M i).Indep (XS i : Set (Fin n)) :=
      fun i => (hXS_ind_pos i).of_restrict
    obtain ⟨hXS_pws, hXS_aw⟩ := h_pws_ind XS hXS_ind
    let allAlloc : Finset (Fin m → Finset (Fin n)) :=
      Finset.univ.filter (fun X => IsAllocOf S X)
    have h_sup : allAlloc.sup (allocWelfare v) =
        ((∑ i : Fin m, ∑ g ∈ XS i, w i g : ℝ) : WithBot ℝ) := by
      apply le_antisymm
      · apply Finset.sup_le
        intro Y hY_mem
        have hY_al : IsAllocOf S Y := (Finset.mem_filter.mp hY_mem).2
        by_cases hY_ind : ∀ i : Fin m, (M i).Indep (Y i : Set (Fin n))
        · let Ypos : Fin m → Finset (Fin n) := fun i => (Y i).filter (fun g => 0 < w i g)
          have hYpos_sub : ∀ i : Fin m, Ypos i ⊆ Y i := fun i => Finset.filter_subset _ _
          have hYpos_al : IsAllocOf S Ypos :=
            ⟨fun i => Finset.Subset.trans (hYpos_sub i) (hY_al.1 i),
              fun i j hij => (hY_al.2 i j hij).mono (hYpos_sub i) (hYpos_sub j)⟩
          have hYpos_ind : ∀ i : Fin m, (M i).Indep (Ypos i : Set (Fin n)) :=
            fun i => (hY_ind i).subset (Finset.coe_subset.mpr (hYpos_sub i))
          have hYpos_pia : IsPosIndepAlloc n m v S Ypos := by
            refine ⟨hYpos_al, fun i => ?_⟩
            rw [h_obs_val n (M i) (w i) S (Ypos i) (hYpos_al.1 i)]
            exact (hYpos_ind i).indep_restrict_of_subset
              (fun g hg => (Finset.mem_filter.mp (Finset.mem_coe.mp hg)).2)
          have h_le_max : posWeightSum n m v Ypos ≤ posWeightSum n m v XS :=
            hXS_max.2 Ypos hYpos_pia
          rw [(h_pws_ind Ypos hYpos_ind).1, hXS_pws] at h_le_max
          have h_Y_le_Ypos : (∑ i : Fin m, ∑ g ∈ Y i, w i g) ≤
              (∑ i : Fin m, ∑ g ∈ Ypos i, w i g) := by
            apply Finset.sum_le_sum
            intro i _
            have hsplit := Finset.sum_filter_add_sum_filter_not (Y i) (fun g => 0 < w i g) (w i)
            have hneg : ∑ g ∈ (Y i).filter (fun g => ¬ 0 < w i g), w i g ≤ 0 := by
              apply Finset.sum_nonpos
              intro g hg
              exact le_of_not_gt (Finset.mem_filter.mp hg).2
            linarith
          rw [(h_pws_ind Y hY_ind).2, WithBot.coe_le_coe]
          exact le_trans h_Y_le_Ypos h_le_max
        · push_neg at hY_ind
          rcases hY_ind with ⟨i₀, hi₀⟩
          have hvi₀ : v i₀ (Y i₀) = ⊥ := by
            dsimp only [v, weightedMatroidVal]
            exact if_neg hi₀
          have haw_bot : allocWelfare v Y = ⊥ := by
            dsimp only [allocWelfare]
            rw [← Finset.add_sum_erase Finset.univ (fun i => v i (Y i)) (Finset.mem_univ i₀),
              hvi₀, WithBot.bot_add]
          rw [haw_bot]
          exact bot_le
      · have hXS_mem : XS ∈ allAlloc := Finset.mem_filter.mpr ⟨Finset.mem_univ XS, hXS_al⟩
        rw [← hXS_aw]
        exact Finset.le_sup (f := allocWelfare v) hXS_mem
    have h_opt : optWelfareOn v S = ∑ i : Fin m, ∑ g ∈ XS i, w i g := by
      dsimp only [optWelfareOn]
      change (allAlloc.sup (allocWelfare v)).unbotD 0 = _
      rw [h_sup, WithBot.unbotD_coe]
    exact ⟨hXS_al, hXS_ind_pos, h_sup, h_opt⟩
  refine ⟨h_obs_loc, h_obs_val, ⟨prefixPosOptAlloc, h_opt_loc, fun n m M w S =>
    let ⟨h1, h2, _, h4⟩ := h_opt_full n m M w S; ⟨h1, h2, h4⟩⟩, ?_⟩
  intro n m c isTernary alg₀ halg₀
  let posOracle (S : Finset (Fin n))
      (oracle : Fin m → {T : Finset (Fin n) // T ⊆ S} → WithBot ℝ) :
      Fin m → {T : Finset (Fin n) // T ⊆ S} → WithBot ℝ :=
    fun i ⟨T, _⟩ =>
      let viLoc : ItemValuation n := fun Y => if h : Y ⊆ S then oracle i ⟨Y, h⟩ else ⊥
      if obsPosIndep viLoc S T then ((∑ g ∈ T, (viLoc {g}).unbotD 0 : ℝ) : WithBot ℝ) else ⊥
  let alg : OnlineWelfareAlg n m :=
    { Seed := alg₀.Seed
      measSeed := alg₀.measSeed
      seedMeasure := alg₀.seedMeasure
      isProb := alg₀.isProb
      det := fun ω =>
        { step := fun prev x bundles oracle =>
            (alg₀.det ω).step prev x bundles (posOracle (insert x prev.toFinset) oracle) }
      meas_step := fun prev x bundles oracle dec =>
        alg₀.meas_step prev x bundles (posOracle (insert x prev.toFinset) oracle) dec }
  have h_pos_rep : ∀ {d : ℕ} (F : Type) [Field F] (Mi : Matroid (Fin n)) (wi : Fin n → ℝ)
      (ui : Fin n → (Fin d → F)),
      IsLinearMatroidRep F Mi ui →
      IsLinearMatroidRep F (Mi.restrict {g : Fin n | 0 < wi g})
        (fun g => if 0 < wi g then ui g else 0) := by
    intro d F _ Mi wi ui hui S
    rw [Matroid.restrict_indep_iff]
    constructor
    · rintro ⟨hS_ind, hS_pos⟩
      have hfun : (fun g : S => (if 0 < wi g.1 then ui g.1 else 0)) = (fun g : S => ui g.1) := by
        funext g
        exact if_pos (hS_pos g.2)
      rw [hfun]
      exact (hui S).mp hS_ind
    · intro hli
      have h_pos : ∀ g : S, 0 < wi g.1 := by
        intro g
        have hne : (if 0 < wi g.1 then ui g.1 else 0) ≠ 0 := LinearIndependent.ne_zero g hli
        by_contra hnp
        exact hne (if_neg hnp)
      have hfun : (fun g : S => (if 0 < wi g.1 then ui g.1 else 0)) = (fun g : S => ui g.1) := by
        funext g
        exact if_pos (h_pos g)
      rw [hfun] at hli
      exact ⟨(hui S).mpr hli, fun g hg => h_pos ⟨g, hg⟩⟩
  have h_pos_bt : ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
      (∀ i, if isTernary i then IsTernaryMatroid (M i) else IsBinaryMatroid (M i)) →
      (∀ i, if isTernary i then IsTernaryMatroid ((M i).restrict {g : Fin n | 0 < w i g})
            else IsBinaryMatroid ((M i).restrict {g : Fin n | 0 < w i g})) := by
    intro M w hM i
    have hMi := hM i
    by_cases hb : isTernary i = true
    · rw [if_pos hb] at hMi ⊢
      rcases hMi with ⟨d, ui, hui⟩
      exact ⟨d, _, h_pos_rep (ZMod 3) (M i) (w i) ui hui⟩
    · rw [if_neg hb] at hMi ⊢
      rcases hMi with ⟨d, ui, hui⟩
      exact ⟨d, _, h_pos_rep (ZMod 2) (M i) (w i) ui hui⟩
  have h_sim : ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ)
      (v_in : Fin m → ItemValuation n),
      (∀ i, if isTernary i then IsTernaryMatroid (M i) else IsBinaryMatroid (M i)) →
      (∀ (i : Fin m) (S T : Finset (Fin n)), T ⊆ S →
        (obsPosIndep (v_in i) S T ↔
          ((M i).restrict {g : Fin n | 0 < w i g}).Indep (T : Set (Fin n))) ∧
        (((M i).restrict {g : Fin n | 0 < w i g}).Indep (T : Set (Fin n)) →
          ∀ g ∈ T, (v_in i {g}).unbotD 0 = w i g)) →
      (∀ (i : Fin m) (X : Finset (Fin n)),
        ((M i).restrict {g : Fin n | 0 < w i g}).Indep (X : Set (Fin n)) →
        v_in i X = ((∑ g ∈ X, w i g : ℝ) : WithBot ℝ)) →
      (optWelfare v_in =
        optWelfare (fun i => weightedMatroidVal ((M i).restrict {g : Fin n | 0 < w i g}) (w i))) →
      (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
        let st := runDetWelfareSteps (alg.det ω) v_in π k hk
        IsAllocOf st.1.toFinset st.2 ∧
        ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
      (((c * optWelfare v_in : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg v_in) := by
    intro M w v_in hM hP1 hP2 h_opt_eq
    let Mpos : Fin m → Matroid (Fin n) := fun i => (M i).restrict {g : Fin n | 0 < w i g}
    let vpos : Fin m → ItemValuation n := fun i => weightedMatroidVal (Mpos i) (w i)
    obtain ⟨h_feas₀, h_wel₀⟩ := halg₀ Mpos w (h_pos_bt M w hM)
    have h_oracle_eq : ∀ S : Finset (Fin n),
        posOracle S (fun i ⟨T, _⟩ => v_in i T) = (fun i ⟨T, _⟩ => vpos i T) := by
      intro S
      funext i ⟨T, hTS⟩
      let viLoc : ItemValuation n := fun Y => if h : Y ⊆ S then v_in i Y else ⊥
      have h_loc_eq : ∀ Y ⊆ S, viLoc Y = v_in i Y := fun Y hYS => dif_pos hYS
      have h_obs_iff : obsPosIndep viLoc S T ↔ (Mpos i).Indep (T : Set (Fin n)) :=
        (h_obs_loc n viLoc (v_in i) S h_loc_eq T hTS).trans (hP1 i S T hTS).1
      dsimp only [posOracle, vpos, weightedMatroidVal]
      change (if obsPosIndep viLoc S T then
                ((∑ g ∈ T, (viLoc {g}).unbotD 0 : ℝ) : WithBot ℝ) else ⊥) =
             (if (Mpos i).Indep (T : Set (Fin n)) then
                ((∑ g ∈ T, w i g : ℝ) : WithBot ℝ) else ⊥)
      by_cases hind : (Mpos i).Indep (T : Set (Fin n))
      · rw [if_pos (h_obs_iff.mpr hind), if_pos hind, WithBot.coe_inj]
        apply Finset.sum_congr rfl
        intro g hgT
        have hgS : ({g} : Finset (Fin n)) ⊆ S := Finset.singleton_subset_iff.mpr (hTS hgT)
        rw [h_loc_eq {g} hgS]
        exact (hP1 i S T hTS).2 hind g hgT
      · rw [if_neg (fun h => hind (h_obs_iff.mp h)), if_neg hind]
    have h_steps_eq : ∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
        runDetWelfareSteps (alg.det ω) v_in π k hk =
        runDetWelfareSteps (alg₀.det ω) vpos π k hk := by
      intro ω π k
      induction k with
      | zero =>
        intro _
        rfl
      | succ k ih =>
        intro hk
        dsimp only [runDetWelfareSteps, alg]
        rw [ih (Nat.le_of_succ_le hk), h_oracle_eq]
    have h_prob_eq : algWelfareProb alg v_in = algWelfareProb alg₀ vpos := by
      funext X
      dsimp only [algWelfareProb, runDetWelfare]
      congr 1
      apply Finset.sum_congr rfl
      intro π _
      have h_set :
          {ω : alg.Seed | (runDetWelfareSteps (alg.det ω) v_in π n (le_refl n)).2 = X} =
          {ω : alg₀.Seed | (runDetWelfareSteps (alg₀.det ω) vpos π n (le_refl n)).2 = X} := by
        ext ω
        change (runDetWelfareSteps (alg.det ω) v_in π n (le_refl n)).2 = X ↔
          (runDetWelfareSteps (alg₀.det ω) vpos π n (le_refl n)).2 = X
        rw [h_steps_eq ω π n (le_refl n)]
      change alg₀.seedMeasure.real
          {ω : alg.Seed | (runDetWelfareSteps (alg.det ω) v_in π n (le_refl n)).2 = X} =
        alg₀.seedMeasure.real
          {ω : alg₀.Seed | (runDetWelfareSteps (alg₀.det ω) vpos π n (le_refl n)).2 = X}
      rw [h_set]
    have h_supp_aw : ∀ X : Fin m → Finset (Fin n),
        algWelfareProb alg₀ vpos X ≠ 0 →
        allocWelfare v_in X = ((∑ i : Fin m, ∑ g ∈ X i, w i g : ℝ) : WithBot ℝ) ∧
        allocWelfare vpos X = ((∑ i : Fin m, ∑ g ∈ X i, w i g : ℝ) : WithBot ℝ) := by
      intro X hprob_ne
      have hex_pair : ∃ (π : Equiv.Perm (Fin n)) (ω : alg₀.Seed),
          runDetWelfare (alg₀.det ω) vpos π = X := by
        by_contra hno
        push_neg at hno
        apply hprob_ne
        dsimp only [algWelfareProb]
        have hsum0 : (∑ π : Equiv.Perm (Fin n),
            alg₀.seedMeasure.real {ω | runDetWelfare (alg₀.det ω) vpos π = X}) = 0 := by
          apply Finset.sum_eq_zero
          intro π _
          have hemp : {ω : alg₀.Seed | runDetWelfare (alg₀.det ω) vpos π = X} = ∅ := by
            ext ω
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
            exact hno π ω
          rw [hemp, MeasureTheory.measureReal_empty]
        rw [hsum0, mul_zero]
      rcases hex_pair with ⟨π, ω, hrun⟩
      have hind_pos : ∀ i : Fin m, (Mpos i).Indep (X i : Set (Fin n)) := by
        rw [← hrun]
        exact (h_feas₀ ω π n (le_refl n)).2
      constructor
      · dsimp only [allocWelfare]
        rw [WithBot.coe_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact hP2 i (X i) (hind_pos i)
      · dsimp only [allocWelfare, vpos, weightedMatroidVal]
        rw [WithBot.coe_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [if_pos (hind_pos i)]
    have h_exp_eq : expectedWelfareVal alg v_in = expectedWelfareVal alg₀ vpos := by
      have h_no_bot_in : ¬ ∃ X : Fin m → Finset (Fin n),
          0 < algWelfareProb alg v_in X ∧ allocWelfare v_in X = ⊥ := by
        rintro ⟨X, hpos_p, hbot⟩
        rw [h_prob_eq] at hpos_p
        have haw := (h_supp_aw X (ne_of_gt hpos_p)).1
        rw [haw] at hbot
        exact WithBot.coe_ne_bot hbot
      have h_no_bot_pos : ¬ ∃ X : Fin m → Finset (Fin n),
          0 < algWelfareProb alg₀ vpos X ∧ allocWelfare vpos X = ⊥ := by
        rintro ⟨X, hpos_p, hbot⟩
        have haw := (h_supp_aw X (ne_of_gt hpos_p)).2
        rw [haw] at hbot
        exact WithBot.coe_ne_bot hbot
      dsimp only [expectedWelfareVal]
      rw [if_neg h_no_bot_in, if_neg h_no_bot_pos, WithBot.coe_inj]
      apply Finset.sum_congr rfl
      intro X _
      rw [h_prob_eq]
      by_cases hp : algWelfareProb alg₀ vpos X = 0
      · rw [hp, zero_mul, zero_mul]
      · obtain ⟨haw1, haw2⟩ := h_supp_aw X hp
        rw [haw1, haw2]
    refine ⟨?_, ?_⟩
    · intro ω π k hk
      rw [h_steps_eq ω π k hk]
      obtain ⟨h_al, h_ind_pos⟩ := h_feas₀ ω π k hk
      exact ⟨h_al, fun i => (h_ind_pos i).of_restrict⟩
    · rw [h_opt_eq, h_exp_eq]
      exact h_wel₀
  have h_opt_v_eq_vpos : ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
      optWelfare (fun i => weightedMatroidVal (M i) (w i)) =
      optWelfare (fun i => weightedMatroidVal ((M i).restrict {g : Fin n | 0 < w i g}) (w i)) := by
    intro M w
    let v : Fin m → ItemValuation n := fun i => weightedMatroidVal (M i) (w i)
    let Mpos : Fin m → Matroid (Fin n) := fun i => (M i).restrict {g : Fin n | 0 < w i g}
    let vpos : Fin m → ItemValuation n := fun i => weightedMatroidVal (Mpos i) (w i)
    let XS := prefixPosOptAlloc n m v Finset.univ
    obtain ⟨hXS_al, hXS_ind_pos, h_sup_v, h_opt_v⟩ := h_opt_full n m M w Finset.univ
    let allAlloc : Finset (Fin m → Finset (Fin n)) :=
      Finset.univ.filter (fun X => IsAllocOf Finset.univ X)
    have h_sup_vpos : allAlloc.sup (allocWelfare vpos) =
        ((∑ i : Fin m, ∑ g ∈ XS i, w i g : ℝ) : WithBot ℝ) := by
      apply le_antisymm
      · rw [← h_sup_v]
        apply Finset.sup_le
        intro Y hY_mem
        by_cases hY_pos : ∀ i : Fin m, (Mpos i).Indep (Y i : Set (Fin n))
        · have haw_eq : allocWelfare vpos Y = allocWelfare v Y := by
            dsimp only [allocWelfare, vpos, v, weightedMatroidVal]
            apply Finset.sum_congr rfl
            intro i _
            rw [if_pos (hY_pos i), if_pos (hY_pos i).of_restrict]
          rw [haw_eq]
          exact Finset.le_sup (f := allocWelfare v) hY_mem
        · push_neg at hY_pos
          rcases hY_pos with ⟨i₀, hi₀⟩
          have hvi₀ : vpos i₀ (Y i₀) = ⊥ := if_neg hi₀
          have haw_bot : allocWelfare vpos Y = ⊥ := by
            dsimp only [allocWelfare]
            rw [← Finset.add_sum_erase Finset.univ (fun i => vpos i (Y i)) (Finset.mem_univ i₀),
              hvi₀, WithBot.bot_add]
          rw [haw_bot]
          exact bot_le
      · have hXS_mem : XS ∈ allAlloc := Finset.mem_filter.mpr ⟨Finset.mem_univ XS, hXS_al⟩
        have haw_XS : allocWelfare vpos XS =
            ((∑ i : Fin m, ∑ g ∈ XS i, w i g : ℝ) : WithBot ℝ) := by
          dsimp only [allocWelfare, vpos, weightedMatroidVal]
          rw [WithBot.coe_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [if_pos (hXS_ind_pos i)]
        rw [← haw_XS]
        exact Finset.le_sup (f := allocWelfare vpos) hXS_mem
    dsimp only [optWelfare, optWelfareOn]
    change _ = (allAlloc.sup (allocWelfare vpos)).unbotD 0
    rw [h_sup_vpos, WithBot.unbotD_coe]
    exact h_opt_v
  have h_vR_max : ∀ (Mi : Matroid (Fin n)) (wi : Fin n → ℝ) (Y : Finset (Fin n)),
      ∃ Z : Finset (Fin n), Z ⊆ Y ∧ Mi.Indep (Z : Set (Fin n)) ∧
        weightedMatroidRankVal Mi wi Y = ((∑ g ∈ Z, wi g : ℝ) : WithBot ℝ) ∧
        (∀ Z' ⊆ Y, Mi.Indep (Z' : Set (Fin n)) → ∑ g ∈ Z', wi g ≤ ∑ g ∈ Z, wi g) := by
    intro Mi wi Y
    let indepSub : Finset (Set (Fin n)) :=
      Y.powerset.filter (fun T => Mi.Indep (T : Set (Fin n)))
    let fVal : Set (Fin n) → WithBot ℝ :=
      fun T => ((∑ g ∈ T, wi g : ℝ) : WithBot ℝ)
    have h_mem_iff : ∀ T : Set (Fin n), T ∈ indepSub ↔
        (∃ A : Finset (Fin n), A ⊆ Y ∧ (A : Set (Fin n)) = T) ∧ Mi.Indep T := by
      intro T
      simp [indepSub]
    have hfVal_coe : ∀ A : Finset (Fin n),
        fVal (A : Set (Fin n)) = ((∑ g ∈ A, wi g : ℝ) : WithBot ℝ) := by
      intro A
      dsimp only [fVal]
      congr 2
      ext x
      simp
    have hemp_mem : (∅ : Set (Fin n)) ∈ indepSub := by
      rw [h_mem_iff]
      exact ⟨⟨∅, Finset.empty_subset Y, Finset.coe_empty⟩, Mi.empty_indep⟩
    obtain ⟨T, hT_mem, hT_sup⟩ := Finset.exists_mem_eq_sup indepSub ⟨∅, hemp_mem⟩ fVal
    rcases (h_mem_iff T).mp hT_mem with ⟨⟨Z, hZY, rfl⟩, hZ_ind⟩
    refine ⟨Z, hZY, hZ_ind, ?_, ?_⟩
    · dsimp only [weightedMatroidRankVal]
      change (((indepSub.sup fVal).unbotD 0 : ℝ) : WithBot ℝ) = _
      rw [hT_sup, hfVal_coe Z, WithBot.unbotD_coe]
    · intro Z' hZ'Y hZ'i
      have hZ'_mem : (Z' : Set (Fin n)) ∈ indepSub :=
        (h_mem_iff (Z' : Set (Fin n))).mpr ⟨⟨Z', hZ'Y, rfl⟩, hZ'i⟩
      have hle := Finset.le_sup (f := fVal) hZ'_mem
      rw [hT_sup, hfVal_coe Z', hfVal_coe Z, WithBot.coe_le_coe] at hle
      exact hle
  have h_vR_indep : ∀ (Mi : Matroid (Fin n)) (wi : Fin n → ℝ) (Y : Finset (Fin n)),
      (∀ g, 0 ≤ wi g) → Mi.Indep (Y : Set (Fin n)) →
      weightedMatroidRankVal Mi wi Y = ((∑ g ∈ Y, wi g : ℝ) : WithBot ℝ) := by
    intro Mi wi Y hwi hind
    obtain ⟨Z, hZY, _, hvR_eq, hZ_le⟩ := h_vR_max Mi wi Y
    have h1 : ∑ g ∈ Y, wi g ≤ ∑ g ∈ Z, wi g := hZ_le Y (Finset.Subset.refl Y) hind
    have h2 : ∑ g ∈ Z, wi g ≤ ∑ g ∈ Y, wi g :=
      Finset.sum_le_sum_of_subset_of_nonneg hZY (fun g _ _ => hwi g)
    rw [hvR_eq, le_antisymm h2 h1]
  refine ⟨alg, ?_, ?_⟩
  · intro M w hM
    apply h_sim M w (fun i => weightedMatroidVal (M i) (w i)) hM
    · intro i S T hTS
      refine ⟨h_obs_val n (M i) (w i) S T hTS, ?_⟩
      intro hind_pos g hgT
      have hind_sg : (M i).Indep (({g} : Finset (Fin n)) : Set (Fin n)) :=
        hind_pos.of_restrict.subset (Finset.coe_subset.mpr (Finset.singleton_subset_iff.mpr hgT))
      dsimp only [weightedMatroidVal]
      rw [if_pos hind_sg, Finset.sum_singleton, WithBot.unbotD_coe]
    · intro i X hind_pos
      dsimp only [weightedMatroidVal]
      rw [if_pos hind_pos.of_restrict]
    · exact h_opt_v_eq_vpos M w
  · intro M w hw hM
    let vR : Fin m → ItemValuation n := fun i => weightedMatroidRankVal (M i) (w i)
    apply h_sim M w vR hM
    · intro i S T hTS
      have h_sg_pos : ∀ g : Fin n, ((0 : ℝ) : WithBot ℝ) < vR i {g} →
          0 < w i g ∧ (vR i {g}).unbotD 0 = w i g := by
        intro g hpos
        obtain ⟨Z, hZ_sub, _, hvR_eq, _⟩ := h_vR_max (M i) (w i) {g}
        have hpos' : ((0 : ℝ) : WithBot ℝ) < ((∑ x ∈ Z, w i x : ℝ) : WithBot ℝ) := by
          rwa [← hvR_eq]
        rw [WithBot.coe_lt_coe] at hpos'
        rcases Finset.subset_singleton_iff.mp hZ_sub with rfl | rfl
        · rw [Finset.sum_empty] at hpos'
          exact absurd hpos' (lt_irrefl 0)
        · rw [Finset.sum_singleton] at hpos' hvR_eq
          refine ⟨hpos', ?_⟩
          change (weightedMatroidRankVal (M i) (w i) {g}).unbotD 0 = w i g
          rw [hvR_eq, WithBot.unbotD_coe]
      have h_sg_of_ind : ((M i).restrict {g : Fin n | 0 < w i g}).Indep (T : Set (Fin n)) →
          ∀ g ∈ T, ((0 : ℝ) : WithBot ℝ) < vR i {g} ∧ (vR i {g}).unbotD 0 = w i g := by
        intro hind_pos g hgT
        have hind_sg : (M i).Indep (({g} : Finset (Fin n)) : Set (Fin n)) :=
          hind_pos.of_restrict.subset (Finset.coe_subset.mpr (Finset.singleton_subset_iff.mpr hgT))
        have hw_pos : 0 < w i g :=
          (Matroid.restrict_indep_iff.mp hind_pos).2 (Finset.mem_coe.mpr hgT)
        have hv_sg : vR i {g} = ((w i g : ℝ) : WithBot ℝ) := by
          dsimp only [vR]
          rw [h_vR_indep (M i) (w i) {g} (hw i) hind_sg, Finset.sum_singleton]
        rw [hv_sg]
        exact ⟨WithBot.coe_lt_coe.mpr hw_pos, WithBot.unbotD_coe 0 (w i g)⟩
      refine ⟨?_, fun hind_pos g hgT => (h_sg_of_ind hind_pos g hgT).2⟩
      constructor
      · rintro ⟨_, _, hpos, hsum⟩
        have hg_all : ∀ g ∈ T, 0 < w i g ∧ (vR i {g}).unbotD 0 = w i g :=
          fun g hg => h_sg_pos g (hpos g hg)
        obtain ⟨Z, hZT, hZ_ind, hvR_eq, _⟩ := h_vR_max (M i) (w i) T
        have h_sum_eq : ∑ g ∈ Z, w i g = ∑ g ∈ T, w i g := by
          have hsum' : vR i T = ((∑ g ∈ Z, w i g : ℝ) : WithBot ℝ) := hvR_eq
          rw [hsum', WithBot.coe_inj] at hsum
          exact hsum.trans (Finset.sum_congr rfl (fun g hg => (hg_all g hg).2))
        have hZT_eq : Z = T := by
          by_contra hne
          obtain ⟨g₀, hg₀T, hg₀Z⟩ := Finset.exists_of_ssubset (ssubset_of_subset_of_ne hZT hne)
          have hZ_er : Z ⊆ T.erase g₀ :=
            fun x hx => Finset.mem_erase.mpr ⟨fun h => hg₀Z (h ▸ hx), hZT hx⟩
          have hle_er : ∑ g ∈ Z, w i g ≤ ∑ g ∈ T.erase g₀, w i g :=
            Finset.sum_le_sum_of_subset_of_nonneg hZ_er (fun g _ _ => hw i g)
          have hadd := Finset.add_sum_erase T (w i) hg₀T
          have hgw : 0 < w i g₀ := (hg_all g₀ hg₀T).1
          linarith
        rw [hZT_eq] at hZ_ind
        exact hZ_ind.indep_restrict_of_subset (fun g hg => (hg_all g (Finset.mem_coe.mp hg)).1)
      · intro hind_pos
        have hv_T : vR i T = ((∑ g ∈ T, w i g : ℝ) : WithBot ℝ) :=
          h_vR_indep (M i) (w i) T (hw i) hind_pos.of_restrict
        refine ⟨hTS, ?_, fun g hgT => (h_sg_of_ind hind_pos g hgT).1, ?_⟩
        · rw [hv_T]
          exact WithBot.coe_ne_bot
        · rw [hv_T, WithBot.coe_inj]
          exact Finset.sum_congr rfl (fun g hgT => ((h_sg_of_ind hind_pos g hgT).2).symm)
    · intro i X hind_pos
      exact h_vR_indep (M i) (w i) X (hw i) hind_pos.of_restrict
    · rw [← h_opt_v_eq_vpos M w]
      let v : Fin m → ItemValuation n := fun i => weightedMatroidVal (M i) (w i)
      let XS := prefixPosOptAlloc n m v Finset.univ
      obtain ⟨hXS_al, hXS_ind_pos, h_sup_v, h_opt_v⟩ := h_opt_full n m M w Finset.univ
      let allAlloc : Finset (Fin m → Finset (Fin n)) :=
        Finset.univ.filter (fun X => IsAllocOf Finset.univ X)
      have h_sup_vR : allAlloc.sup (allocWelfare vR) =
          ((∑ i : Fin m, ∑ g ∈ XS i, w i g : ℝ) : WithBot ℝ) := by
        apply le_antisymm
        · rw [← h_sup_v]
          apply Finset.sup_le
          intro Y hY_mem
          have hY_al : IsAllocOf Finset.univ Y := (Finset.mem_filter.mp hY_mem).2
          have hexZ : ∀ i : Fin m, ∃ Z : Finset (Fin n),
              Z ⊆ Y i ∧ (M i).Indep (Z : Set (Fin n)) ∧
              vR i (Y i) = ((∑ g ∈ Z, w i g : ℝ) : WithBot ℝ) :=
            fun i => let ⟨Z, h1, h2, h3, _⟩ := h_vR_max (M i) (w i) (Y i); ⟨Z, h1, h2, h3⟩
          let Z : Fin m → Finset (Fin n) := fun i => Classical.choose (hexZ i)
          have hZ_spec := fun i => Classical.choose_spec (hexZ i)
          have hZ_al : IsAllocOf Finset.univ Z :=
            ⟨fun _ => Finset.subset_univ _,
              fun i j hij => (hY_al.2 i j hij).mono (hZ_spec i).1 (hZ_spec j).1⟩
          have haw_eq : allocWelfare vR Y = allocWelfare v Z := by
            dsimp only [allocWelfare, v, weightedMatroidVal]
            apply Finset.sum_congr rfl
            intro i _
            rw [(hZ_spec i).2.2, if_pos (hZ_spec i).2.1]
          rw [haw_eq]
          exact Finset.le_sup (f := allocWelfare v)
            (Finset.mem_filter.mpr ⟨Finset.mem_univ Z, hZ_al⟩)
        · have hXS_mem : XS ∈ allAlloc := Finset.mem_filter.mpr ⟨Finset.mem_univ XS, hXS_al⟩
          have haw_XS : allocWelfare vR XS =
              ((∑ i : Fin m, ∑ g ∈ XS i, w i g : ℝ) : WithBot ℝ) := by
            dsimp only [allocWelfare]
            rw [WithBot.coe_sum]
            apply Finset.sum_congr rfl
            intro i _
            exact h_vR_indep (M i) (w i) (XS i) (hw i) (hXS_ind_pos i).of_restrict
          rw [← haw_XS]
          exact Finset.le_sup (f := allocWelfare vR) hXS_mem
      dsimp only [optWelfare, optWelfareOn]
      change (allAlloc.sup (allocWelfare vR)).unbotD 0 = _
      rw [h_sup_vR, WithBot.unbotD_coe]
      exact h_opt_v.symm

theorem lem_cutoff_and_small_n_welfare : (∀ n : ℕ, 2 ≤ n → ∃ s : ℕ, 1 ≤ s ∧ s < n ∧ invE ≤ secretaryCutoffConst n s) ∧
    (∀ (n m : ℕ) (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
      0 ≤ optWelfare (fun i => weightedMatroidVal (M i) (w i))) ∧
    (∀ (n m : ℕ), n < 2 →
      ∃ alg : OnlineWelfareAlg n m,
        ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
          let v := fun i => weightedMatroidVal (M i) (w i)
          (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
            let st := runDetWelfareSteps (alg.det ω) v π k hk
            IsAllocOf st.1.toFinset st.2 ∧
            ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
          (((invE * optWelfare v : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg v)) :=
by
  have h_part1 : ∀ n : ℕ, 2 ≤ n → ∃ s : ℕ, 1 ≤ s ∧ s < n ∧ invE ≤ secretaryCutoffConst n s := by
    intro n hn2
    have h_invE_pos : 0 < invE := Real.exp_pos (-1)
    have h_exp_prod : Real.exp 1 * invE = 1 := by
      dsimp [invE]
      rw [← Real.exp_add]
      norm_num
    rcases eq_or_lt_of_le hn2 with rfl | hn3
    · refine ⟨1, le_refl 1, by omega, ?_⟩
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
      by_cases hc0 : invE ≤ secretaryCutoffConst n s0
      · exact ⟨s0, hs0_ge_1, hs0_lt_n, hc0⟩
      · refine ⟨s0 + 1, by omega, hs01_lt_n, ?_⟩
        by_contra hc1
        push_neg at hc0 hc1
        have hlt0 : (1 - η) * secretaryCutoffConst n s0 < (1 - η) * invE :=
          mul_lt_mul_of_pos_left hc0 h1mη_pos
        have hle1 : η * secretaryCutoffConst n (s0 + 1) ≤ η * invE :=
          mul_le_mul_of_nonneg_left (le_of_lt hc1) hη_nn
        linarith
  have h_val_empty : ∀ {n : ℕ} (M : Matroid (Fin n)) (w : Fin n → ℝ),
      weightedMatroidVal M w ∅ = 0 := by
    intro n M w
    dsimp [weightedMatroidVal]
    have hind : M.Indep ((∅ : Finset (Fin n)) : Set (Fin n)) := by
      rw [Finset.coe_empty]
      exact M.empty_indep
    rw [if_pos hind]
  have h_alloc_empty_welfare : ∀ {n m : ℕ} (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
      allocWelfare (fun i => weightedMatroidVal (M i) (w i)) (fun _ => ∅) = ((0 : ℝ) : WithBot ℝ) := by
    intro n m M w
    dsimp [allocWelfare]
    exact Finset.sum_eq_zero (fun i _ => h_val_empty (M i) (w i))
  have h_empty_isAlloc : ∀ {n m : ℕ} (S : Finset (Fin n)),
      IsAllocOf S (fun _ : Fin m => (∅ : Finset (Fin n))) := by
    intro n m S
    exact ⟨fun _ => Finset.empty_subset S, fun _ _ _ => Finset.disjoint_empty_left ∅⟩
  have h_part2 : ∀ (n m : ℕ) (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
      0 ≤ optWelfare (fun i => weightedMatroidVal (M i) (w i)) := by
    intro n m M w
    let v : Fin m → ItemValuation n := fun i => weightedMatroidVal (M i) (w i)
    let A_univ := (Finset.univ : Finset (Fin m → Finset (Fin n))).filter
      (fun X => IsAllocOf Finset.univ X)
    have h_mem : (fun _ : Fin m => (∅ : Finset (Fin n))) ∈ A_univ :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_empty_isAlloc Finset.univ⟩
    have h_le_sup : ((0 : ℝ) : WithBot ℝ) ≤ A_univ.sup (allocWelfare v) := by
      rw [← h_alloc_empty_welfare M w]
      exact Finset.le_sup (f := allocWelfare v) h_mem
    dsimp [optWelfare, optWelfareOn]
    change 0 ≤ (A_univ.sup (allocWelfare v)).unbotD 0
    cases hz : A_univ.sup (allocWelfare v) with
    | bot =>
      rw [hz, le_bot_iff] at h_le_sup
      exact absurd h_le_sup WithBot.coe_ne_bot
    | coe r =>
      rw [hz, WithBot.coe_le_coe] at h_le_sup
      rw [WithBot.unbotD_coe]
      exact h_le_sup
  have h_invE_le_one : invE ≤ 1 := by
    dsimp [invE]
    calc Real.exp (-1) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by norm_num)
      _ = 1 := Real.exp_zero
  have h_det_exp : ∀ {n m : ℕ} (alg : OnlineWelfareAlg n m)
      (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ)
      (X_star : Fin m → Finset (Fin n)),
      let v := fun i => weightedMatroidVal (M i) (w i)
      (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)), runDetWelfare (alg.det ω) v π = X_star) →
      allocWelfare v X_star = ((optWelfare v : ℝ) : WithBot ℝ) →
      (((invE * optWelfare v : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg v) := by
    intro n m alg M w X_star v h_run h_wel_eq
    have h_prob_star : algWelfareProb alg v X_star = 1 := by
      dsimp [algWelfareProb]
      have h_set : ∀ π : Equiv.Perm (Fin n),
          {ω : alg.Seed | runDetWelfare (alg.det ω) v π = X_star} = Set.univ := by
        intro π
        ext ω
        simp [h_run ω π]
      have h_sum : (∑ π : Equiv.Perm (Fin n),
          alg.seedMeasure.real {ω : alg.Seed | runDetWelfare (alg.det ω) v π = X_star}) =
          (Nat.factorial n : ℝ) := by
        have h1 : ∀ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))),
            alg.seedMeasure.real {ω : alg.Seed | runDetWelfare (alg.det ω) v π = X_star} = 1 := by
          intro π _
          rw [h_set π, MeasureTheory.probReal_univ]
        rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_univ,
            Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, mul_one]
      rw [h_sum, one_div_mul_cancel (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))]
    have h_prob_other : ∀ X : Fin m → Finset (Fin n), X ≠ X_star → algWelfareProb alg v X = 0 := by
      intro X hX
      dsimp [algWelfareProb]
      have h_set : ∀ π : Equiv.Perm (Fin n),
          {ω : alg.Seed | runDetWelfare (alg.det ω) v π = X} = ∅ := by
        intro π
        ext ω
        simp [h_run ω π, Ne.symm hX]
      have h_sum : (∑ π : Equiv.Perm (Fin n),
          alg.seedMeasure.real {ω : alg.Seed | runDetWelfare (alg.det ω) v π = X}) = 0 := by
        refine Finset.sum_eq_zero (fun π _ => ?_)
        rw [h_set π, MeasureTheory.measureReal_empty]
      rw [h_sum, mul_zero]
    have h_no_bot : ¬ ∃ X : Fin m → Finset (Fin n),
        0 < algWelfareProb alg v X ∧ allocWelfare v X = ⊥ := by
      rintro ⟨X, hpos, hbot⟩
      by_cases hX : X = X_star
      · subst hX
        rw [h_wel_eq] at hbot
        exact WithBot.coe_ne_bot hbot
      · rw [h_prob_other X hX] at hpos
        exact lt_irrefl 0 hpos
    have h_exp_eq : expectedWelfareVal alg v = ((optWelfare v : ℝ) : WithBot ℝ) := by
      dsimp [expectedWelfareVal]
      rw [if_neg h_no_bot]
      congr 1
      rw [Finset.sum_eq_single X_star]
      · rw [h_prob_star, h_wel_eq, WithBot.unbotD_coe, one_mul]
      · intro X _ hX
        rw [h_prob_other X hX, zero_mul]
      · intro h_not_mem
        exact absurd (Finset.mem_univ X_star) h_not_mem
    rw [h_exp_eq, WithBot.coe_le_coe]
    have h_opt_nn : 0 ≤ optWelfare v := h_part2 n m M w
    calc invE * optWelfare v ≤ 1 * optWelfare v :=
          mul_le_mul_of_nonneg_right h_invE_le_one h_opt_nn
      _ = optWelfare v := one_mul _
  have h_part3 : ∀ (n m : ℕ), n < 2 →
      ∃ alg : OnlineWelfareAlg n m,
        ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
          let v := fun i => weightedMatroidVal (M i) (w i)
          (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
            let st := runDetWelfareSteps (alg.det ω) v π k hk
            IsAllocOf st.1.toFinset st.2 ∧
            ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
          (((invE * optWelfare v : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg v) := by
    intro n m hn2
    have hn_cases : n = 0 ∨ n = 1 := by omega
    rcases hn_cases with rfl | rfl
    · let alg : OnlineWelfareAlg 0 m :=
        { Seed := Unit
          seedMeasure := Measure.dirac ()
          isProb := inferInstance
          det := fun _ => { step := fun _ x _ _ => Fin.elim0 x }
          meas_step := fun _ _ _ _ _ => MeasurableSet.of_discrete }
      refine ⟨alg, ?_⟩
      intro M w
      let v : Fin m → ItemValuation 0 := fun i => weightedMatroidVal (M i) (w i)
      let X_star : Fin m → Finset (Fin 0) := fun _ => ∅
      refine ⟨?_, ?_⟩
      · intro ω π k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
        subst hk0
        dsimp [runDetWelfareSteps]
        refine ⟨h_empty_isAlloc _, fun i => ?_⟩
        rw [Finset.coe_empty]
        exact (M i).empty_indep
      · apply h_det_exp alg M w X_star
        · intro ω π
          rfl
        · have hX_eq : ∀ X : Fin m → Finset (Fin 0), X = X_star := by
            intro X
            funext i
            ext x
            exact Fin.elim0 x
          let A_univ := (Finset.univ : Finset (Fin m → Finset (Fin 0))).filter
            (fun X => IsAllocOf Finset.univ X)
          have h_mem : X_star ∈ A_univ :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_empty_isAlloc Finset.univ⟩
          have h_sup : A_univ.sup (allocWelfare v) = ((0 : ℝ) : WithBot ℝ) := by
            apply le_antisymm
            · refine Finset.sup_le (fun X _ => ?_)
              rw [hX_eq X, h_alloc_empty_welfare M w]
            · rw [← h_alloc_empty_welfare M w]
              exact Finset.le_sup (f := allocWelfare v) h_mem
          have h_opt0 : optWelfare v = 0 := by
            dsimp [optWelfare, optWelfareOn]
            change (A_univ.sup (allocWelfare v)).unbotD 0 = 0
            rw [h_sup, WithBot.unbotD_coe]
          rw [h_opt0, h_alloc_empty_welfare M w]
    · let step₁ : (prev : List (Fin 1)) → (x : Fin 1) → (bundles : Fin m → Finset (Fin 1)) →
          (Fin m → {T : Finset (Fin 1) // T ⊆ insert x prev.toFinset} → WithBot ℝ) →
          Option (Fin m) :=
        fun prev x _ oracle =>
          let hx : ({x} : Finset (Fin 1)) ⊆ insert x prev.toFinset :=
            Finset.singleton_subset_iff.mpr (Finset.mem_insert_self x prev.toFinset)
          let P : Finset (Fin m) :=
            Finset.univ.filter (fun i : Fin m => ((0 : ℝ) : WithBot ℝ) < oracle i ⟨{x}, hx⟩)
          if hP : P.Nonempty then
            some (Classical.choose (Finset.exists_max_image P (fun i => oracle i ⟨{x}, hx⟩) hP))
          else
            none
      let alg : OnlineWelfareAlg 1 m :=
        { Seed := Unit
          seedMeasure := Measure.dirac ()
          isProb := inferInstance
          det := fun _ => { step := step₁ }
          meas_step := fun _ _ _ _ _ => MeasurableSet.of_discrete }
      refine ⟨alg, ?_⟩
      intro M w
      let v : Fin m → ItemValuation 1 := fun i => weightedMatroidVal (M i) (w i)
      have h_set_eq_singleton : ∀ S : Finset (Fin 1), (0 : Fin 1) ∈ S → S = {0} := by
        intro S h0
        ext y
        rw [Subsingleton.elim y 0]
        simp [h0]
      have h_set_eq_empty : ∀ S : Finset (Fin 1), (0 : Fin 1) ∉ S → S = ∅ := by
        intro S h0
        ext y
        rw [Subsingleton.elim y 0]
        simp [h0]
      have h_welfare_of_mem : ∀ (X : Fin m → Finset (Fin 1)) (i₀ : Fin m),
          IsPairwiseDisjoint X → (0 : Fin 1) ∈ X i₀ → allocWelfare v X = v i₀ {0} := by
        intro X i₀ hdisj hi₀
        dsimp [allocWelfare]
        rw [← Finset.add_sum_erase Finset.univ (fun i => v i (X i)) (Finset.mem_univ i₀)]
        have hXi₀ : X i₀ = {0} := h_set_eq_singleton (X i₀) hi₀
        have h_rest : ∑ i ∈ Finset.univ.erase i₀, v i (X i) = 0 := by
          refine Finset.sum_eq_zero (fun i hi => ?_)
          have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
          have h0_not : (0 : Fin 1) ∉ X i :=
            Finset.disjoint_left.mp (hdisj i₀ i hne.symm) hi₀
          rw [h_set_eq_empty (X i) h0_not]
          exact h_val_empty (M i) (w i)
        rw [hXi₀, h_rest, add_zero]
      have h_welfare_of_none : ∀ (X : Fin m → Finset (Fin 1)),
          (¬ ∃ i₀ : Fin m, (0 : Fin 1) ∈ X i₀) → allocWelfare v X = ((0 : ℝ) : WithBot ℝ) := by
        intro X hnone
        have hX_emp : X = (fun _ => ∅) := by
          funext i
          exact h_set_eq_empty (X i) (fun h0 => hnone ⟨i, h0⟩)
        rw [hX_emp]
        exact h_alloc_empty_welfare M w
      let P₀ : Finset (Fin m) :=
        Finset.univ.filter (fun i : Fin m => ((0 : ℝ) : WithBot ℝ) < v i {0})
      let dec₀ : Option (Fin m) :=
        if hP : P₀.Nonempty then
          some (Classical.choose (Finset.exists_max_image P₀ (fun i => v i {0}) hP))
        else
          none
      let X_star : Fin m → Finset (Fin 1) :=
        match dec₀ with
        | none => fun _ => ∅
        | some i => Function.update (fun _ => ∅) i {0}
      have h_step1_def : step₁ [] 0 (fun _ => ∅) (fun i y => v i y.1) = dec₀ := rfl
      have h_eval_x : ∀ x₀ : Fin 1,
          ([x₀],
            match step₁ [] x₀ (fun _ => ∅) (fun i y => v i y.1) with
            | none => fun _ => ∅
            | some i => Function.update (fun _ => ∅) i (insert x₀ ∅)) = ([0], X_star) := by
        intro x₀
        have hx0 : x₀ = 0 := Subsingleton.elim _ _
        subst hx0
        have h_ins : insert (0 : Fin 1) (∅ : Finset (Fin 1)) = {0} := by simp
        rw [h_step1_def, h_ins]
      have h_steps1 : ∀ (ω : alg.Seed) (π : Equiv.Perm (Fin 1)) (hk : 1 ≤ 1),
          runDetWelfareSteps (alg.det ω) v π 1 hk = ([0], X_star) := by
        intro ω π hk
        exact h_eval_x (π ⟨0, hk⟩)
      have h_star_props : IsAllocOf ({0} : Finset (Fin 1)) X_star ∧
          IsAllocOf Finset.univ X_star ∧
          (∀ i : Fin m, (M i).Indep (X_star i : Set (Fin 1))) ∧
          allocWelfare v X_star = ((optWelfare v : ℝ) : WithBot ℝ) := by
        by_cases hP : P₀.Nonempty
        · let j_star : Fin m := Classical.choose (Finset.exists_max_image P₀ (fun i => v i {0}) hP)
          have hj_spec := Classical.choose_spec (Finset.exists_max_image P₀ (fun i => v i {0}) hP)
          rcases hj_spec with ⟨hj_mem, hj_max⟩
          have hdec : dec₀ = some j_star := dif_pos hP
          have hX_star : X_star = Function.update (fun _ : Fin m => (∅ : Finset (Fin 1))) j_star {0} := by
            dsimp [X_star]
            rw [hdec]
          have hv_pos : ((0 : ℝ) : WithBot ℝ) < v j_star {0} := (Finset.mem_filter.mp hj_mem).2
          have hind_j : (M j_star).Indep (({0} : Finset (Fin 1)) : Set (Fin 1)) := by
            dsimp [v, weightedMatroidVal] at hv_pos
            by_contra hni
            rw [if_neg hni] at hv_pos
            exact absurd hv_pos (not_lt_of_ge bot_le)
          have hv_j_eq : v j_star {0} = ((w j_star 0 : ℝ) : WithBot ℝ) := by
            dsimp [v, weightedMatroidVal]
            rw [if_pos hind_j, Finset.sum_singleton]
          have hw_pos : 0 < w j_star 0 := by
            rw [hv_j_eq, WithBot.coe_lt_coe] at hv_pos
            exact hv_pos
          have h_disj_star : IsPairwiseDisjoint X_star := by
            intro i₁ i₂ hne
            rw [hX_star]
            by_cases hi₁ : i₁ = j_star
            · subst hi₁
              rw [Function.update_self, Function.update_of_ne hne.symm]
              exact Finset.disjoint_empty_right _
            · rw [Function.update_of_ne hi₁]
              exact Finset.disjoint_empty_left _
          have h_alloc_0 : IsAllocOf ({0} : Finset (Fin 1)) X_star := by
            refine ⟨fun i => ?_, h_disj_star⟩
            rw [hX_star]
            by_cases hi : i = j_star
            · subst hi
              rw [Function.update_self]
            · rw [Function.update_of_ne hi]
              exact Finset.empty_subset _
          have h_alloc_univ : IsAllocOf Finset.univ X_star :=
            ⟨fun i => Finset.subset_univ (X_star i), h_disj_star⟩
          have h_ind_all : ∀ i : Fin m, (M i).Indep (X_star i : Set (Fin 1)) := by
            intro i
            rw [hX_star]
            by_cases hi : i = j_star
            · subst hi
              rw [Function.update_self]
              exact hind_j
            · rw [Function.update_of_ne hi, Finset.coe_empty]
              exact (M i).empty_indep
          have h0_mem_j : (0 : Fin 1) ∈ X_star j_star := by
            rw [hX_star, Function.update_self]
            exact Finset.mem_singleton_self 0
          have h_wel_star : allocWelfare v X_star = ((w j_star 0 : ℝ) : WithBot ℝ) := by
            rw [h_welfare_of_mem X_star j_star h_disj_star h0_mem_j, hv_j_eq]
          let A_univ := (Finset.univ : Finset (Fin m → Finset (Fin 1))).filter
            (fun X => IsAllocOf Finset.univ X)
          have h_mem_A : X_star ∈ A_univ :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_alloc_univ⟩
          have h_sup : A_univ.sup (allocWelfare v) = ((w j_star 0 : ℝ) : WithBot ℝ) := by
            apply le_antisymm
            · refine Finset.sup_le (fun X hX => ?_)
              have hX_alloc : IsAllocOf Finset.univ X := (Finset.mem_filter.mp hX).2
              by_cases hex : ∃ i₀ : Fin m, (0 : Fin 1) ∈ X i₀
              · obtain ⟨i₀, hi₀⟩ := hex
                rw [h_welfare_of_mem X i₀ hX_alloc.2 hi₀]
                by_cases hi₀P : i₀ ∈ P₀
                · rw [← hv_j_eq]
                  exact hj_max i₀ hi₀P
                · have h_not_pos : ¬ (((0 : ℝ) : WithBot ℝ) < v i₀ {0}) := by
                    intro hlt
                    exact hi₀P (Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hlt⟩)
                  have h_le0 : v i₀ {0} ≤ ((0 : ℝ) : WithBot ℝ) := not_lt.mp h_not_pos
                  exact le_trans h_le0 (WithBot.coe_le_coe.mpr (le_of_lt hw_pos))
              · rw [h_welfare_of_none X hex]
                exact WithBot.coe_le_coe.mpr (le_of_lt hw_pos)
            · rw [← h_wel_star]
              exact Finset.le_sup (f := allocWelfare v) h_mem_A
          have h_opt_eq : optWelfare v = w j_star 0 := by
            dsimp [optWelfare, optWelfareOn]
            change (A_univ.sup (allocWelfare v)).unbotD 0 = w j_star 0
            rw [h_sup, WithBot.unbotD_coe]
          exact ⟨h_alloc_0, h_alloc_univ, h_ind_all, by rw [h_wel_star, h_opt_eq]⟩
        · have hdec : dec₀ = none := dif_neg hP
          have hX_star : X_star = (fun _ => ∅) := by
            dsimp [X_star]
            rw [hdec]
          have h_alloc_0 : IsAllocOf ({0} : Finset (Fin 1)) X_star := by
            rw [hX_star]
            exact h_empty_isAlloc _
          have h_alloc_univ : IsAllocOf Finset.univ X_star := by
            rw [hX_star]
            exact h_empty_isAlloc _
          have h_ind_all : ∀ i : Fin m, (M i).Indep (X_star i : Set (Fin 1)) := by
            intro i
            rw [hX_star, Finset.coe_empty]
            exact (M i).empty_indep
          have h_wel_star : allocWelfare v X_star = ((0 : ℝ) : WithBot ℝ) := by
            rw [hX_star]
            exact h_alloc_empty_welfare M w
          let A_univ := (Finset.univ : Finset (Fin m → Finset (Fin 1))).filter
            (fun X => IsAllocOf Finset.univ X)
          have h_mem_A : X_star ∈ A_univ :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_alloc_univ⟩
          have h_sup : A_univ.sup (allocWelfare v) = ((0 : ℝ) : WithBot ℝ) := by
            apply le_antisymm
            · refine Finset.sup_le (fun X hX => ?_)
              have hX_alloc : IsAllocOf Finset.univ X := (Finset.mem_filter.mp hX).2
              by_cases hex : ∃ i₀ : Fin m, (0 : Fin 1) ∈ X i₀
              · obtain ⟨i₀, hi₀⟩ := hex
                rw [h_welfare_of_mem X i₀ hX_alloc.2 hi₀]
                have h_not_pos : ¬ (((0 : ℝ) : WithBot ℝ) < v i₀ {0}) := by
                  intro hlt
                  exact hP ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hlt⟩⟩
                exact not_lt.mp h_not_pos
              · rw [h_welfare_of_none X hex]
            · rw [← h_wel_star]
              exact Finset.le_sup (f := allocWelfare v) h_mem_A
          have h_opt_eq : optWelfare v = 0 := by
            dsimp [optWelfare, optWelfareOn]
            change (A_univ.sup (allocWelfare v)).unbotD 0 = 0
            rw [h_sup, WithBot.unbotD_coe]
          exact ⟨h_alloc_0, h_alloc_univ, h_ind_all, by rw [h_wel_star, h_opt_eq]⟩
      rcases h_star_props with ⟨h_alloc_0, _, h_ind_all, h_wel_eq⟩
      refine ⟨?_, ?_⟩
      · intro ω π k hk
        have hk_cases : k = 0 ∨ k = 1 := by omega
        rcases hk_cases with rfl | rfl
        · dsimp [runDetWelfareSteps]
          refine ⟨h_empty_isAlloc _, fun i => ?_⟩
          rw [Finset.coe_empty]
          exact (M i).empty_indep
        · dsimp only
          rw [h_steps1 ω π hk]
          have h_toFinset : ([0] : List (Fin 1)).toFinset = {0} := by simp
          rw [h_toFinset]
          exact ⟨h_alloc_0, h_ind_all⟩
      · apply h_det_exp alg M w X_star
        · intro ω π
          dsimp [runDetWelfare]
          rw [h_steps1 ω π (le_refl 1)]
        · exact h_wel_eq
  exact ⟨h_part1, h_part2, h_part3⟩

theorem lem_remark_f5_u36_divergence : ∃ (M : Matroid (Fin 6))
      (uR uR' : Fin 6 → (Fin 3 → ZMod 5))
      (μ : Finset (Fin 6) → ℝ),
      let h : Fin 3 → ZMod 5 := ![1, 0, 3]
      (∀ S : Finset (Fin 6), M.Indep (S : Set (Fin 6)) ↔ S.card ≤ 3) ∧
      IsLinearMatroidRep (ZMod 5) M uR ∧
      IsLinearMatroidRep (ZMod 5) M uR' ∧
      IsSubspaceBetaBounded uR' Finset.univ (2 / 3 : ℝ) μ ∧
      (¬ ∃ β : ℝ, β < 1 ∧ IsSubspaceBetaBounded uR Finset.univ β μ) ∧
      h ≠ 0 ∧
      (∀ A : Finset (Fin 6), μ A ≠ 0 → h ∈ matroidSpan uR A) :=
by
  obtain ⟨M, hM⟩ : ∃ M : Matroid (Fin 6), ∀ S : Finset (Fin 6), M.Indep (S : Set (Fin 6)) ↔ S.card ≤ 3 := by
    let IM : IndepMatroid (Fin 6) := IndepMatroid.ofBddAugment
      (E := Set.univ)
      (Indep := fun I => I.encard ≤ 3)
      (indep_empty := by simp)
      (indep_subset := fun I J hJ hIJ => le_trans (Set.encard_le_encard hIJ) hJ)
      (indep_aug := by
        intro I J _ hJ hlt
        have hnot_sub : ¬ (J ⊆ I) := fun hJI => not_le_of_gt hlt (Set.encard_le_encard hJI)
        obtain ⟨e, heJ, heI⟩ := Set.not_subset.mp hnot_sub
        refine ⟨e, heJ, heI, ?_⟩
        change (insert e I).encard ≤ 3
        rw [Set.encard_insert_of_notMem heI]
        exact le_trans (Order.add_one_le_of_lt hlt) hJ)
      (indep_bdd := ⟨3, fun _ hI => hI⟩)
      (subset_ground := fun I _ => Set.subset_univ I)
    refine ⟨IM.matroid, fun S => ?_⟩
    rw [IndepMatroid.matroid_Indep]
    change (S : Set (Fin 6)).encard ≤ (3 : ℕ) ↔ S.card ≤ 3
    rw [Set.encard_coe_eq_coe_finsetCard, Nat.cast_le]
  let uR : Fin 6 → (Fin 3 → ZMod 5) :=
    ![![1, 0, 0], ![0, 0, 1], ![1, 1, 1], ![1, 2, 4], ![1, 3, 4], ![1, 4, 1]]
  let uR' : Fin 6 → (Fin 3 → ZMod 5) :=
    ![![1, 0, 0], ![1, 1, 1], ![1, 2, 4], ![1, 4, 1], ![1, 3, 4], ![0, 0, 1]]
  let det3 : (Fin 3 → ZMod 5) → (Fin 3 → ZMod 5) → (Fin 3 → ZMod 5) → ZMod 5 :=
    fun x y z =>
      x 0 * (y 1 * z 2 - y 2 * z 1) -
      x 1 * (y 0 * z 2 - y 2 * z 0) +
      x 2 * (y 0 * z 1 - y 1 * z 0)
  have hdet3_eq : ∀ x y z : Fin 3 → ZMod 5, (Matrix.of ![x, y, z]).det = det3 x y z := by
    intro x y z
    rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, det3]
    ring
  have hli_of_det : ∀ (Q : Fin 6 → (Fin 3 → ZMod 5)),
      (∀ a b c : Fin 6, a < b → b < c → det3 (Q a) (Q b) (Q c) ≠ 0) →
      ∀ S : Finset (Fin 6), LinearIndependent (ZMod 5) (fun g : S => Q g.1) ↔ S.card ≤ 3 := by
    intro Q hQ S
    constructor
    · intro hli
      have h := hli.fintype_card_le_finrank
      simpa [Fintype.card_coe, Module.finrank_fin_fun] using h
    · intro hS
      have hcompl : 3 - S.card ≤ (Finset.univ \ S).card := by
        have h1 : (Finset.univ \ S).card = 6 - S.card := by
          rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨E, hES, hE_card⟩ := Finset.exists_subset_card_eq hcompl
      let B : Finset (Fin 6) := S ∪ E
      have hdisj : Disjoint S E := by
        rw [Finset.disjoint_left]
        intro x hxS hxE
        exact (Finset.mem_sdiff.mp (hES hxE)).2 hxS
      have hB_card : B.card = 3 := by
        change (S ∪ E).card = 3
        rw [Finset.card_union_of_disjoint hdisj, hE_card]
        omega
      let e := B.orderIsoOfFin hB_card
      have h01 : (e 0).1 < (e 1).1 := e.strictMono (by omega)
      have h12 : (e 1).1 < (e 2).1 := e.strictMono (by omega)
      have hd : (Matrix.of ![Q (e 0).1, Q (e 1).1, Q (e 2).1]).det ≠ 0 := by
        rw [hdet3_eq]
        exact hQ (e 0).1 (e 1).1 (e 2).1 h01 h12
      have hli3 : LinearIndependent (ZMod 5) ![Q (e 0).1, Q (e 1).1, Q (e 2).1] :=
        Matrix.linearIndependent_rows_of_det_ne_zero hd
      have hfn_eq : (![Q (e 0).1, Q (e 1).1, Q (e 2).1] : Fin 3 → Fin 3 → ZMod 5) =
          fun i : Fin 3 => Q (e i).1 := by
        ext i j
        fin_cases i <;> rfl
      rw [hfn_eq] at hli3
      let f : S → Fin 3 := fun g => e.symm ⟨g.1, Finset.mem_union_left E g.2⟩
      have hf_inj : Function.Injective f := by
        intro g1 g2 h
        have h' := e.symm.injective h
        exact Subtype.ext (congrArg (fun b : B => b.1) h')
      have hcomp := hli3.comp f hf_inj
      convert hcomp using 1
      ext g j
      simp [f]
  have huR_det_bool : ((List.finRange 6).all fun a => (List.finRange 6).all fun b =>
      (List.finRange 6).all fun c =>
        !(Nat.ble (a.1 + 1) b.1 && Nat.ble (b.1 + 1) c.1) ||
        !(Nat.beq (det3 (uR a) (uR b) (uR c)).val 0)) = true := rfl
  have huR'_det_bool : ((List.finRange 6).all fun a => (List.finRange 6).all fun b =>
      (List.finRange 6).all fun c =>
        !(Nat.ble (a.1 + 1) b.1 && Nat.ble (b.1 + 1) c.1) ||
        !(Nat.beq (det3 (uR' a) (uR' b) (uR' c)).val 0)) = true := rfl
  have huR_det : ∀ a b c : Fin 6, a < b → b < c → det3 (uR a) (uR b) (uR c) ≠ 0 := by
    intro a b c hab hbc h0
    have ha := List.mem_finRange a
    have hb := List.mem_finRange b
    have hc := List.mem_finRange c
    have h1 := (List.all_eq_true.mp huR_det_bool) a ha
    have h2 := (List.all_eq_true.mp h1) b hb
    have h3 := (List.all_eq_true.mp h2) c hc
    have hab' : Nat.ble (a.1 + 1) b.1 = true := Nat.ble_eq.mpr hab
    have hbc' : Nat.ble (b.1 + 1) c.1 = true := Nat.ble_eq.mpr hbc
    have h0' : Nat.beq (det3 (uR a) (uR b) (uR c)).val 0 = true := by
      rw [h0]; rfl
    rw [hab', hbc', h0'] at h3
    contradiction
  have huR'_det : ∀ a b c : Fin 6, a < b → b < c → det3 (uR' a) (uR' b) (uR' c) ≠ 0 := by
    intro a b c hab hbc h0
    have ha := List.mem_finRange a
    have hb := List.mem_finRange b
    have hc := List.mem_finRange c
    have h1 := (List.all_eq_true.mp huR'_det_bool) a ha
    have h2 := (List.all_eq_true.mp h1) b hb
    have h3 := (List.all_eq_true.mp h2) c hc
    have hab' : Nat.ble (a.1 + 1) b.1 = true := Nat.ble_eq.mpr hab
    have hbc' : Nat.ble (b.1 + 1) c.1 = true := Nat.ble_eq.mpr hbc
    have h0' : Nat.beq (det3 (uR' a) (uR' b) (uR' c)).val 0 = true := by
      rw [h0]; rfl
    rw [hab', hbc', h0'] at h3
    contradiction
  have huR_li : ∀ S : Finset (Fin 6), LinearIndependent (ZMod 5) (fun g : S => uR g.1) ↔ S.card ≤ 3 :=
    hli_of_det uR huR_det
  have huR'_li : ∀ S : Finset (Fin 6), LinearIndependent (ZMod 5) (fun g : S => uR' g.1) ↔ S.card ≤ 3 :=
    hli_of_det uR' huR'_det
  let B0 : Finset (Fin 6) := {0, 1}
  let B1 : Finset (Fin 6) := {2, 3}
  let B2 : Finset (Fin 6) := {4, 5}
  let supp : Finset (Finset (Fin 6)) := {B0, B1, B2}
  let μ : Finset (Fin 6) → ℝ := fun A => if A ∈ supp then (1 / 3 : ℝ) else 0
  have hB01 : B0 ≠ B1 := by
    intro h
    have hm : (0 : Fin 6) ∈ B0 := by simp [B0]
    rw [h] at hm
    simp [B1] at hm
  have hB02 : B0 ≠ B2 := by
    intro h
    have hm : (0 : Fin 6) ∈ B0 := by simp [B0]
    rw [h] at hm
    simp [B2] at hm
  have hB12 : B1 ≠ B2 := by
    intro h
    have hm : (2 : Fin 6) ∈ B1 := by simp [B1]
    rw [h] at hm
    simp [B2] at hm
  have hsum_μ : ∀ f : Finset (Fin 6) → ℝ,
      (∑ A : Finset (Fin 6), μ A * f A) = (1 / 3 : ℝ) * (f B0 + f B1 + f B2) := by
    intro f
    have hsub : (∑ A : Finset (Fin 6), μ A * f A) = ∑ A ∈ supp, μ A * f A := by
      symm
      apply Finset.sum_subset (Finset.subset_univ supp)
      intro A _ hA
      simp [μ, hA]
    rw [hsub]
    have hmem0 : B0 ∉ ({B1, B2} : Finset _) := by simp [hB01, hB02]
    have hmem1 : B1 ∉ ({B2} : Finset _) := by simp [hB12]
    change (∑ A ∈ insert B0 (insert B1 {B2}), μ A * f A) = _
    rw [Finset.sum_insert hmem0, Finset.sum_insert hmem1, Finset.sum_singleton]
    have hs0 : B0 ∈ supp := by simp [supp]
    have hs1 : B1 ∈ supp := by simp [supp]
    have hs2 : B2 ∈ supp := by simp [supp]
    simp only [μ, hs0, hs1, hs2, ↓reduceIte]
    ring
  have hB0_card : B0.card ≤ 3 := le_trans Finset.card_le_two (by omega)
  have hB1_card : B1.card ≤ 3 := le_trans Finset.card_le_two (by omega)
  have hB2_card : B2.card ≤ 3 := le_trans Finset.card_le_two (by omega)
  have hlaw_uR' : IsIndepSetLaw uR' Finset.univ μ := by
    refine ⟨?_, ?_, ?_⟩
    · intro A; simp only [μ]; split_ifs <;> norm_num
    · intro A hμA
      have hAsupp : A ∈ supp := by
        by_contra h
        exact hμA (by simp [μ, h])
      refine ⟨Finset.subset_univ A, (huR'_li A).mpr ?_⟩
      simp only [supp, Finset.mem_insert, Finset.mem_singleton] at hAsupp
      rcases hAsupp with rfl | rfl | rfl
      · exact hB0_card
      · exact hB1_card
      · exact hB2_card
    · have h1 := hsum_μ (fun _ => 1)
      simp only [mul_one] at h1
      rw [h1]; norm_num
  let hv : Fin 3 → ZMod 5 := ![1, 0, 3]
  have hv_ne0 : hv ≠ 0 := by
    intro h0
    have h00 : hv 0 = 0 := congrFun h0 0
    change (1 : ZMod 5) = 0 at h00
    exact one_ne_zero h00
  have hv_B0 : hv ∈ matroidSpan uR B0 := by
    have heq : hv = (1 : ZMod 5) • uR 0 + (3 : ZMod 5) • uR 1 := by
      ext j; fin_cases j <;> rfl
    rw [heq]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp [B0], rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, by simp [B0], rfl⟩))
  have hv_B1 : hv ∈ matroidSpan uR B1 := by
    have heq : hv = (2 : ZMod 5) • uR 2 + (4 : ZMod 5) • uR 3 := by
      ext j; fin_cases j <;> rfl
    rw [heq]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, by simp [B1], rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨3, by simp [B1], rfl⟩))
  have hv_B2 : hv ∈ matroidSpan uR B2 := by
    have heq : hv = (4 : ZMod 5) • uR 4 + (2 : ZMod 5) • uR 5 := by
      ext j; fin_cases j <;> rfl
    rw [heq]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨4, by simp [B2], rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨5, by simp [B2], rfl⟩))
  have hv_supp : ∀ A : Finset (Fin 6), μ A ≠ 0 → hv ∈ matroidSpan uR A := by
    intro A hμA
    have hAsupp : A ∈ supp := by
      by_contra h
      exact hμA (by simp [μ, h])
    simp only [supp, Finset.mem_insert, Finset.mem_singleton] at hAsupp
    rcases hAsupp with rfl | rfl | rfl
    · exact hv_B0
    · exact hv_B1
    · exact hv_B2
  have h_not_beta_uR : ¬ ∃ β : ℝ, β < 1 ∧ IsSubspaceBetaBounded uR Finset.univ β μ := by
    rintro ⟨β, hβ_lt, _, hβ_load⟩
    let U : Submodule (ZMod 5) (Fin 3 → ZMod 5) := Submodule.span (ZMod 5) {hv}
    have hU_le_B0 : U ≤ matroidSpan uR B0 :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv_B0)
    have hU_le_B1 : U ≤ matroidSpan uR B1 :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv_B1)
    have hU_le_B2 : U ≤ matroidSpan uR B2 :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv_B2)
    have hdimU : Module.finrank (ZMod 5) U = 1 := finrank_span_singleton hv_ne0
    have hload0 : subspaceLoad uR U B0 = 1 := by
      dsimp only [subspaceLoad]
      rw [inf_of_le_right hU_le_B0, hdimU]
    have hload1 : subspaceLoad uR U B1 = 1 := by
      dsimp only [subspaceLoad]
      rw [inf_of_le_right hU_le_B1, hdimU]
    have hload2 : subspaceLoad uR U B2 = 1 := by
      dsimp only [subspaceLoad]
      rw [inf_of_le_right hU_le_B2, hdimU]
    have hineq := hβ_load U
    rw [hsum_μ, hload0, hload1, hload2, hdimU] at hineq
    norm_num at hineq
    linarith
  have h_plane_bound : ∀ (W : Submodule (ZMod 5) (Fin 3 → ZMod 5)),
      subspaceLoad uR' W B0 + subspaceLoad uR' W B1 + subspaceLoad uR' W B2 ≤
      2 * Module.finrank (ZMod 5) W := by
    have hspan2_le : ∀ a b : Fin 6,
        Module.finrank (ZMod 5) (matroidSpan uR' ({a, b} : Finset (Fin 6))) ≤ 2 := by
      intro a b
      have himg : uR' '' (({a, b} : Finset (Fin 6)) : Set (Fin 6)) =
          (({uR' a, uR' b} : Finset (Fin 3 → ZMod 5)) : Set (Fin 3 → ZMod 5)) := by
        ext x
        simp only [Set.mem_image, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨g, rfl | rfl, rfl⟩ <;> simp
        · rintro (rfl | rfl)
          · exact ⟨a, Or.inl rfl, rfl⟩
          · exact ⟨b, Or.inr rfl, rfl⟩
      dsimp only [matroidSpan]
      rw [himg]
      exact le_trans (finrank_span_finset_le_card _) Finset.card_le_two
    have h_triple_bot :
        matroidSpan uR' B0 ⊓ matroidSpan uR' B1 ⊓ matroidSpan uR' B2 = ⊥ := by
      let K0 : Submodule (ZMod 5) (Fin 3 → ZMod 5) :=
        { carrier := {x | 4 * x 1 + x 2 = 0}
          zero_mem' := by simp
          add_mem' := fun {a b} ha hb => by
            change 4 * (a 1 + b 1) + (a 2 + b 2) = 0
            calc 4 * (a 1 + b 1) + (a 2 + b 2) = (4 * a 1 + a 2) + (4 * b 1 + b 2) := by ring
              _ = 0 := by rw [ha, hb, add_zero]
          smul_mem' := fun c {a} ha => by
            change 4 * (c * a 1) + c * a 2 = 0
            calc 4 * (c * a 1) + c * a 2 = c * (4 * a 1 + a 2) := by ring
              _ = 0 := by rw [ha, mul_zero] }
      let K1 : Submodule (ZMod 5) (Fin 3 → ZMod 5) :=
        { carrier := {x | x 0 + 3 * x 1 + 2 * x 2 = 0}
          zero_mem' := by simp
          add_mem' := fun {a b} ha hb => by
            change (a 0 + b 0) + 3 * (a 1 + b 1) + 2 * (a 2 + b 2) = 0
            calc (a 0 + b 0) + 3 * (a 1 + b 1) + 2 * (a 2 + b 2)
                = (a 0 + 3 * a 1 + 2 * a 2) + (b 0 + 3 * b 1 + 2 * b 2) := by ring
              _ = 0 := by rw [ha, hb, add_zero]
          smul_mem' := fun c {a} ha => by
            change c * a 0 + 3 * (c * a 1) + 2 * (c * a 2) = 0
            calc c * a 0 + 3 * (c * a 1) + 2 * (c * a 2) = c * (a 0 + 3 * a 1 + 2 * a 2) := by ring
              _ = 0 := by rw [ha, mul_zero] }
      let K2 : Submodule (ZMod 5) (Fin 3 → ZMod 5) :=
        { carrier := {x | 3 * x 0 + 4 * x 1 = 0}
          zero_mem' := by simp
          add_mem' := fun {a b} ha hb => by
            change 3 * (a 0 + b 0) + 4 * (a 1 + b 1) = 0
            calc 3 * (a 0 + b 0) + 4 * (a 1 + b 1) = (3 * a 0 + 4 * a 1) + (3 * b 0 + 4 * b 1) := by ring
              _ = 0 := by rw [ha, hb, add_zero]
          smul_mem' := fun c {a} ha => by
            change 3 * (c * a 0) + 4 * (c * a 1) = 0
            calc 3 * (c * a 0) + 4 * (c * a 1) = c * (3 * a 0 + 4 * a 1) := by ring
              _ = 0 := by rw [ha, mul_zero] }
      have hP0_ker : matroidSpan uR' B0 ≤ K0 := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨g, hg, rfl⟩
        simp only [Finset.mem_coe, B0, Finset.mem_insert, Finset.mem_singleton] at hg
        rcases hg with rfl | rfl <;> rfl
      have hP1_ker : matroidSpan uR' B1 ≤ K1 := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨g, hg, rfl⟩
        simp only [Finset.mem_coe, B1, Finset.mem_insert, Finset.mem_singleton] at hg
        rcases hg with rfl | rfl <;> rfl
      have hP2_ker : matroidSpan uR' B2 ≤ K2 := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨g, hg, rfl⟩
        simp only [Finset.mem_coe, B2, Finset.mem_insert, Finset.mem_singleton] at hg
        rcases hg with rfl | rfl <;> rfl
      rw [eq_bot_iff]
      intro x hx
      rcases hx with ⟨⟨hx0, hx1⟩, hx2⟩
      have e0 : 4 * x 1 + x 2 = 0 := hP0_ker hx0
      have e1 : x 0 + 3 * x 1 + 2 * x 2 = 0 := hP1_ker hx1
      have e2 : 3 * x 0 + 4 * x 1 = 0 := hP2_ker hx2
      have h5 : (5 : ZMod 5) = 0 := rfl
      have hx_0 : x 0 = 0 := by
        calc x 0 = (x 0 + 3 * x 1 + 2 * x 2) - 2 * (4 * x 1 + x 2) + (5 : ZMod 5) * x 1 := by ring
          _ = 0 - 2 * 0 + 0 * x 1 := by rw [e1, e0, h5]
          _ = 0 := by ring
      have hx_1 : x 1 = 0 := by
        calc x 1 = (5 : ZMod 5) * x 1 - (3 * x 0 + 4 * x 1) + 3 * x 0 := by ring
          _ = 0 * x 1 - 0 + 3 * 0 := by rw [h5, e2, hx_0]
          _ = 0 := by ring
      have hx_2 : x 2 = 0 := by
        calc x 2 = (4 * x 1 + x 2) - 4 * x 1 := by ring
          _ = 0 - 4 * 0 := by rw [e0, hx_1]
          _ = 0 := by ring
      ext j; fin_cases j
      · exact hx_0
      · exact hx_1
      · exact hx_2
    have hP0_rk : Module.finrank (ZMod 5) (matroidSpan uR' B0) ≤ 2 := hspan2_le 0 1
    have hP1_rk : Module.finrank (ZMod 5) (matroidSpan uR' B1) ≤ 2 := hspan2_le 2 3
    have hP2_rk : Module.finrank (ZMod 5) (matroidSpan uR' B2) ≤ 2 := hspan2_le 4 5
    suffices hgen : ∀ (P0 P1 P2 W : Submodule (ZMod 5) (Fin 3 → ZMod 5)),
        Module.finrank (ZMod 5) P0 ≤ 2 →
        Module.finrank (ZMod 5) P1 ≤ 2 →
        Module.finrank (ZMod 5) P2 ≤ 2 →
        P0 ⊓ P1 ⊓ P2 = ⊥ →
        Module.finrank (ZMod 5) (P0 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) +
        Module.finrank (ZMod 5) (P1 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) +
        Module.finrank (ZMod 5) (P2 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) ≤
        2 * Module.finrank (ZMod 5) W by
      intro W
      dsimp only [subspaceLoad]
      exact hgen _ _ _ W hP0_rk hP1_rk hP2_rk h_triple_bot
    intro P0 P1 P2 W h0_rk h1_rk h2_rk hbot
    have hW_le3 : Module.finrank (ZMod 5) W ≤ 3 := by
      have h := Submodule.finrank_le W
      simpa [Module.finrank_fin_fun] using h
    have hd0W : Module.finrank (ZMod 5) (P0 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) ≤ Module.finrank (ZMod 5) W :=
      Submodule.finrank_mono inf_le_right
    have hd1W : Module.finrank (ZMod 5) (P1 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) ≤ Module.finrank (ZMod 5) W :=
      Submodule.finrank_mono inf_le_right
    have hd2W : Module.finrank (ZMod 5) (P2 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) ≤ Module.finrank (ZMod 5) W :=
      Submodule.finrank_mono inf_le_right
    have hd0P : Module.finrank (ZMod 5) (P0 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) ≤ 2 :=
      le_trans (Submodule.finrank_mono inf_le_left) h0_rk
    have hd1P : Module.finrank (ZMod 5) (P1 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) ≤ 2 :=
      le_trans (Submodule.finrank_mono inf_le_left) h1_rk
    have hd2P : Module.finrank (ZMod 5) (P2 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) ≤ 2 :=
      le_trans (Submodule.finrank_mono inf_le_left) h2_rk
    interval_cases hW : Module.finrank (ZMod 5) W
    · omega
    · by_contra hgt
      have heq0 : Module.finrank (ZMod 5) (P0 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) = 1 := by omega
      have heq1 : Module.finrank (ZMod 5) (P1 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) = 1 := by omega
      have heq2 : Module.finrank (ZMod 5) (P2 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) = 1 := by omega
      have hW0 : W ≤ P0 := inf_eq_right.mp (Submodule.eq_of_le_of_finrank_eq inf_le_right (heq0.trans hW.symm))
      have hW1 : W ≤ P1 := inf_eq_right.mp (Submodule.eq_of_le_of_finrank_eq inf_le_right (heq1.trans hW.symm))
      have hW2 : W ≤ P2 := inf_eq_right.mp (Submodule.eq_of_le_of_finrank_eq inf_le_right (heq2.trans hW.symm))
      have hW_bot : W ≤ ⊥ := hbot ▸ le_inf (le_inf hW0 hW1) hW2
      have hW_eq_bot : W = ⊥ := le_bot_iff.mp hW_bot
      rw [hW_eq_bot, finrank_bot] at hW
      omega
    · by_contra hgt
      by_cases h0_2 : Module.finrank (ZMod 5) (P0 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) = 2
      · by_cases h1_2 : Module.finrank (ZMod 5) (P1 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) = 2
        · have hW0 : W ≤ P0 := inf_eq_right.mp (Submodule.eq_of_le_of_finrank_eq inf_le_right (h0_2.trans hW.symm))
          have hW1 : W ≤ P1 := inf_eq_right.mp (Submodule.eq_of_le_of_finrank_eq inf_le_right (h1_2.trans hW.symm))
          have h2_bot : (P2 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) = ⊥ :=
            le_bot_iff.mp (hbot ▸ le_inf (le_inf (le_trans inf_le_right hW0) (le_trans inf_le_right hW1)) inf_le_left)
          rw [h2_bot, finrank_bot] at hgt
          omega
        · have h2_2 : Module.finrank (ZMod 5) (P2 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) = 2 := by omega
          have hW0 : W ≤ P0 := inf_eq_right.mp (Submodule.eq_of_le_of_finrank_eq inf_le_right (h0_2.trans hW.symm))
          have hW2 : W ≤ P2 := inf_eq_right.mp (Submodule.eq_of_le_of_finrank_eq inf_le_right (h2_2.trans hW.symm))
          have h1_bot : (P1 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) = ⊥ :=
            le_bot_iff.mp (hbot ▸ le_inf (le_inf (le_trans inf_le_right hW0) inf_le_left) (le_trans inf_le_right hW2))
          rw [h1_bot, finrank_bot] at hgt
          omega
      · have h1_2 : Module.finrank (ZMod 5) (P1 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) = 2 := by omega
        have h2_2 : Module.finrank (ZMod 5) (P2 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) = 2 := by omega
        have hW1 : W ≤ P1 := inf_eq_right.mp (Submodule.eq_of_le_of_finrank_eq inf_le_right (h1_2.trans hW.symm))
        have hW2 : W ≤ P2 := inf_eq_right.mp (Submodule.eq_of_le_of_finrank_eq inf_le_right (h2_2.trans hW.symm))
        have h0_bot : (P0 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) = ⊥ :=
          le_bot_iff.mp (hbot ▸ le_inf (le_inf inf_le_left (le_trans inf_le_right hW1)) (le_trans inf_le_right hW2))
        rw [h0_bot, finrank_bot] at hgt
        omega
    · omega
  have h_beta_uR' : IsSubspaceBetaBounded uR' Finset.univ (2 / 3 : ℝ) μ := by
    refine ⟨hlaw_uR', ?_⟩
    intro U
    rw [hsum_μ]
    have hbound : ((subspaceLoad uR' U B0 : ℝ) + (subspaceLoad uR' U B1 : ℝ) + (subspaceLoad uR' U B2 : ℝ)) ≤
        2 * (Module.finrank (ZMod 5) U : ℝ) := by
      exact_mod_cast h_plane_bound U
    linarith
  refine ⟨M, uR, uR', μ, ?_⟩
  dsimp only
  refine ⟨hM, ?_, ?_, h_beta_uR', h_not_beta_uR, hv_ne0, hv_supp⟩
  · intro S; exact (hM S).trans (huR_li S).symm
  · intro S; exact (hM S).trans (huR'_li S).symm

theorem thm_linear_and_binary_ternary_welfare :
    -- (1) Theorem E.1(a): Represented model with arbitrary cutoff s ∈ {1, ..., n - 1}
    (∀ (n m s : ℕ) (F : Fin m → Type) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
        [∀ i, DecidableEq (F i)] (d : Fin m → ℕ),
      2 ≤ n → 1 ≤ s → s < n →
        ∃ alg : RepresentedOnlineWelfareAlg n m F d,
          ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ)
            (u : (i : Fin m) → Fin n → (Fin (d i) → F i)),
            (∀ i, IsLinearMatroidRep (F i) (M i) (u i)) →
              let v := fun i => weightedMatroidVal (M i) (w i)
              (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
                let st := runDetRepresentedWelfareSteps (alg.det ω) v u π k hk
                IsAllocOf st.1.toFinset st.2 ∧
                ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
              (((secretaryCutoffConst n s * optWelfare v : ℝ) : WithBot ℝ) ≤
                expectedRepresentedWelfareVal alg v u)) ∧
    -- (2) Theorem E.1(b) + Rank Corollary: Value-oracle model with cutoff s ∈ {1, ..., n - 1}
    (∀ (n m s : ℕ) (isTernary : Fin m → Bool),
      2 ≤ n → 1 ≤ s → s < n →
        ∃ alg : OnlineWelfareAlg n m,
          (∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
            (∀ i, if isTernary i then IsTernaryMatroid (M i) else IsBinaryMatroid (M i)) →
              let v := fun i => weightedMatroidVal (M i) (w i)
              (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
                let st := runDetWelfareSteps (alg.det ω) v π k hk
                IsAllocOf st.1.toFinset st.2 ∧
                ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
              (((secretaryCutoffConst n s * optWelfare v : ℝ) : WithBot ℝ) ≤
                expectedWelfareVal alg v)) ∧
          (∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
            (∀ i g, 0 ≤ w i g) →
            (∀ i, if isTernary i then IsTernaryMatroid (M i) else IsBinaryMatroid (M i)) →
              let vR := fun i => weightedMatroidRankVal (M i) (w i)
              (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
                let st := runDetWelfareSteps (alg.det ω) vR π k hk
                IsAllocOf st.1.toFinset st.2 ∧
                ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
              (((secretaryCutoffConst n s * optWelfare vR : ℝ) : WithBot ℝ) ≤
                expectedWelfareVal alg vR))) ∧
    -- (3a) Theorem C (Pure Binary Value-Oracle Model, no side tags)
    (∀ (n m : ℕ),
      ∃ alg : OnlineWelfareAlg n m,
        ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
          (∀ i, IsBinaryMatroid (M i)) →
            let v := fun i => weightedMatroidVal (M i) (w i)
            (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
              let st := runDetWelfareSteps (alg.det ω) v π k hk
              IsAllocOf st.1.toFinset st.2 ∧
              ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
            (((invE * optWelfare v : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg v)) ∧
    -- (3b) Theorem C (Pure Ternary Value-Oracle Model, no side tags)
    (∀ (n m : ℕ),
      ∃ alg : OnlineWelfareAlg n m,
        ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
          (∀ i, IsTernaryMatroid (M i)) →
            let v := fun i => weightedMatroidVal (M i) (w i)
            (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
              let st := runDetWelfareSteps (alg.det ω) v π k hk
              IsAllocOf st.1.toFinset st.2 ∧
              ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
            (((invE * optWelfare v : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg v)) ∧
    -- (3c) Theorem C (Mixed Binary/Ternary Value-Oracle Model + Represented Model across all n, m)
    (∀ (n m : ℕ) (isTernary : Fin m → Bool),
      ∃ alg : OnlineWelfareAlg n m,
        ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
          (∀ i, if isTernary i then IsTernaryMatroid (M i) else IsBinaryMatroid (M i)) →
            let v := fun i => weightedMatroidVal (M i) (w i)
            (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
              let st := runDetWelfareSteps (alg.det ω) v π k hk
              IsAllocOf st.1.toFinset st.2 ∧
              ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
            (((invE * optWelfare v : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg v)) ∧
    (∀ (n m : ℕ) (F : Fin m → Type) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
        [∀ i, DecidableEq (F i)] (d : Fin m → ℕ),
      ∃ alg : RepresentedOnlineWelfareAlg n m F d,
        ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ)
          (u : (i : Fin m) → Fin n → (Fin (d i) → F i)),
          (∀ i, IsLinearMatroidRep (F i) (M i) (u i)) →
            let v := fun i => weightedMatroidVal (M i) (w i)
            (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
              let st := runDetRepresentedWelfareSteps (alg.det ω) v u π k hk
              IsAllocOf st.1.toFinset st.2 ∧
              ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
            (((invE * optWelfare v : ℝ) : WithBot ℝ) ≤
              expectedRepresentedWelfareVal alg v u)) ∧
    -- (4) Remark E.4 (rem:fields): F_5 U_{3,6} divergence + 7th item h = (1, 0, 3) zero availability
    (∃ (M : Matroid (Fin 6))
        (uR uR' : Fin 6 → (Fin 3 → ZMod 5))
        (μ : Finset (Fin 6) → ℝ),
      let h : Fin 3 → ZMod 5 := ![1, 0, 3]
      (∀ S : Finset (Fin 6), M.Indep (S : Set (Fin 6)) ↔ S.card ≤ 3) ∧
      IsLinearMatroidRep (ZMod 5) M uR ∧
      IsLinearMatroidRep (ZMod 5) M uR' ∧
      IsSubspaceBetaBounded uR' Finset.univ (2 / 3 : ℝ) μ ∧
      (¬ ∃ β : ℝ, β < 1 ∧ IsSubspaceBetaBounded uR Finset.univ β μ) ∧
      h ≠ 0 ∧
      (∀ A : Finset (Fin 6), μ A ≠ 0 → h ∈ matroidSpan uR A)) :=
by
  rcases lem_pos_oracle_and_opt_alloc with
    ⟨h_obs_loc, h_obs_val, ⟨prefixPosOptAlloc, h_opt_loc, h_opt_spec⟩, h_rank_upgrade⟩
  rcases lem_binary_ternary_rep_and_transfer with ⟨h_dim_comp, h_trans_2, h_trans_3⟩
  rcases lem_cutoff_and_small_n_welfare with ⟨h_dynkin, h_opt_nonneg, h_small_n⟩
  have h_pos_rep :
      ∀ {n d : ℕ} (F : Type) [Field F] (M : Matroid (Fin n)) (w : Fin n → ℝ)
        (u : Fin n → (Fin d → F)),
        IsLinearMatroidRep F M u →
        IsLinearMatroidRep F (M.restrict {g : Fin n | 0 < w g})
          (fun g => if 0 < w g then u g else 0) := by
    intro n d F _ M w u hu S
    rw [Matroid.restrict_indep_iff]
    constructor
    · rintro ⟨hS_ind, hS_pos⟩
      have hfun : (fun g : S => (if 0 < w g.1 then u g.1 else 0)) = (fun g : S => u g.1) := by
        funext g
        exact if_pos (hS_pos g.2)
      rw [hfun]
      exact (hu S).mp hS_ind
    · intro hli
      have h_pos : ∀ g : S, 0 < w g.1 := by
        intro g
        have hne : (if 0 < w g.1 then u g.1 else 0) ≠ 0 := LinearIndependent.ne_zero g hli
        by_contra hnp
        exact hne (if_neg hnp)
      have hfun : (fun g : S => (if 0 < w g.1 then u g.1 else 0)) = (fun g : S => u g.1) := by
        funext g
        exact if_pos (h_pos g)
      rw [hfun] at hli
      exact ⟨(hu S).mpr hli, fun g hg => h_pos ⟨g, hg⟩⟩
  have h_part1 :
      ∀ (n m s : ℕ) (F : Fin m → Type) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
        [∀ i, DecidableEq (F i)] (d : Fin m → ℕ),
      2 ≤ n → 1 ≤ s → s < n →
        ∃ alg : RepresentedOnlineWelfareAlg n m F d,
          ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ)
            (u : (i : Fin m) → Fin n → (Fin (d i) → F i)),
            (∀ i, IsLinearMatroidRep (F i) (M i) (u i)) →
              let v := fun i => weightedMatroidVal (M i) (w i)
              (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
                let st := runDetRepresentedWelfareSteps (alg.det ω) v u π k hk
                IsAllocOf st.1.toFinset st.2 ∧
                ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
              (((secretaryCutoffConst n s * optWelfare v : ℝ) : WithBot ℝ) ≤
                expectedRepresentedWelfareVal alg v u) := by
    intro n m s F _ _ _ d hn hs1 hsn
    let hlp := fun i : Fin m => lem_local_rep_prefix_lp n (d i) s hs1 (F i)
    let μProg := fun i : Fin m => (hlp i).choose
    let qProg := fun i : Fin m => (hlp i).choose_spec.choose
    have hProg := fun i : Fin m => (hlp i).choose_spec.choose_spec
    let rateFor (S : Finset (Fin n)) (vLoc : Fin m → ItemValuation n)
        (vecOracle : (i : Fin m) → {g : Fin n // g ∈ S} → (Fin (d i) → F i))
        (x : Fin n) (bundles : Fin m → Finset (Fin n)) (j : Fin m) : Fin m × ℝ :=
      let ρLoc : Finset (Fin n) → Fin n → (Fin (d j) → F j) :=
        fun T g =>
          if g ∈ T ∧ ((0 : ℝ) : WithBot ℝ) < vLoc j {g} then
            if hgS : g ∈ S then vecOracle j ⟨g, hgS⟩ else 0
          else 0
      let PLoc : Finset (Fin n) → Finset (Fin n) :=
        fun T => prefixPosOptAlloc n m vLoc T j
      let denom := μProg j ρLoc PLoc (S.erase x) (bundles j)
      let num := qProg j ρLoc PLoc S x (bundles j)
      (j, if denom = 0 then 0 else num / denom)
    let rateRule :
        (prev : List (Fin n)) → (x : Fin n) → (bundles : Fin m → Finset (Fin n)) →
        (Fin m → {T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → WithBot ℝ) →
        ((i : Fin m) → {g : Fin n // g ∈ insert x prev.toFinset} → (Fin (d i) → F i)) →
        Option (Fin m × ℝ) :=
      fun prev x bundles oracle vecOracle =>
        let S := insert x prev.toFinset
        if S.card ≤ s then none
        else
          let vLoc : Fin m → ItemValuation n :=
            fun i Y => if h : Y ⊆ S then oracle i ⟨Y, h⟩ else ⊥
          let XS := prefixPosOptAlloc n m vLoc S
          if h_rec : ∃ j : Fin m, x ∈ XS j then
            some (rateFor S vLoc vecOracle x bundles (Classical.choose h_rec))
          else none
    obtain ⟨alg, halg⟩ := lem_markov_threshold_welfare n m s hn hs1 hsn F d rateRule
    refine ⟨alg, ?_⟩
    intro M w u hu
    apply halg M w u
    let v : Fin m → ItemValuation n := fun i => weightedMatroidVal (M i) (w i)
    let Mpos : Fin m → Matroid (Fin n) := fun i => (M i).restrict {g : Fin n | 0 < w i g}
    let X : Finset (Fin n) → Fin m → Finset (Fin n) := fun S => prefixPosOptAlloc n m v S
    let ρ : (i : Fin m) → Finset (Fin n) → Fin n → (Fin (d i) → F i) :=
      fun i T g => if g ∈ T ∧ ((0 : ℝ) : WithBot ℝ) < v i {g} then u i g else 0
    let P : Fin m → Finset (Fin n) → Finset (Fin n) := fun i T => X T i
    let μ : Fin m → Finset (Fin n) → Finset (Fin n) → ℝ := fun i => μProg i (ρ i) (P i)
    let q : Fin m → Finset (Fin n) → Fin n → Finset (Fin n) → ℝ := fun i => qProg i (ρ i) (P i)
    refine ⟨X, μ, q, ?_, ?_, ?_⟩
    · intro S
      obtain ⟨h_alloc, h_ind_pos, h_opt_eq⟩ := h_opt_spec n m M w S
      exact ⟨h_alloc, fun i => (Matroid.restrict_indep_iff.mp (h_ind_pos i)).1,
        le_of_eq h_opt_eq⟩
    · intro i
      obtain ⟨_, hProg_base, hProg_rec⟩ := hProg i
      have hP_i : ∀ T, P i T ⊆ T ∧ (Mpos i).Indep (P i T : Set (Fin n)) := by
        intro T
        obtain ⟨h_alloc, h_ind_pos, _⟩ := h_opt_spec n m M w T
        exact ⟨h_alloc.1 i, h_ind_pos i⟩
      have hRep_i : ∀ (T Y : Finset (Fin n)), Y ⊆ T →
          (LinearIndependent (F i) (fun g : Y => ρ i T g.1) ↔ (Mpos i).Indep (Y : Set (Fin n))) := by
        intro T Y hYT
        constructor
        · intro hli
          have h_cond : ∀ g : Y, g.1 ∈ T ∧ ((0 : ℝ) : WithBot ℝ) < v i {g.1} := by
            intro g
            have hne : ρ i T g.1 ≠ 0 := LinearIndependent.ne_zero g hli
            by_contra hc
            exact hne (if_neg hc)
          have hfun : (fun g : Y => ρ i T g.1) = (fun g : Y => u i g.1) := by
            funext g
            exact if_pos (h_cond g)
          rw [hfun] at hli
          rw [Matroid.restrict_indep_iff]
          refine ⟨(hu i Y).mpr hli, ?_⟩
          intro g hgY
          have hpos : ((0 : ℝ) : WithBot ℝ) < v i {g} := (h_cond ⟨g, hgY⟩).2
          dsimp only [v, weightedMatroidVal] at hpos
          split_ifs at hpos with hind
          · rw [Finset.sum_singleton, WithBot.coe_lt_coe] at hpos
            exact hpos
          · exact absurd hpos (not_lt_of_ge bot_le)
        · intro hind_pos
          rw [Matroid.restrict_indep_iff] at hind_pos
          rcases hind_pos with ⟨hindY, hY_pos⟩
          have hfun : (fun g : Y => ρ i T g.1) = (fun g : Y => u i g.1) := by
            funext g
            have hgT : g.1 ∈ T := hYT g.2
            have hind_sg : (M i).Indep (({g.1} : Finset (Fin n)) : Set (Fin n)) :=
              hindY.subset (Finset.coe_subset.mpr (Finset.singleton_subset_iff.mpr g.2))
            have hpos_g : ((0 : ℝ) : WithBot ℝ) < v i {g.1} := by
              dsimp only [v, weightedMatroidVal]
              rw [if_pos hind_sg, Finset.sum_singleton, WithBot.coe_lt_coe]
              exact hY_pos g.2
            exact if_pos ⟨hgT, hpos_g⟩
          rw [hfun]
          exact (hu i Y).mp hindY
      have hTrans_i : ∀ T, ∀ g ∈ T, ∀ (β : ℝ) (μ₀ : Finset (Fin n) → ℝ),
          0 ≤ β →
          IsSubspaceBetaBounded (ρ i (T.erase g)) (T.erase g) β μ₀ →
          IsSubspaceBetaBounded (ρ i T) (T.erase g) β μ₀ := by
        intro T g _ β μ₀ _ hbeta
        rcases hbeta with ⟨⟨hμ_nn, hμ_supp, hμ_sum⟩, hμ_load⟩
        have h_eq_on : ∀ A : Finset (Fin n), A ⊆ T.erase g →
            ∀ y ∈ A, ρ i (T.erase g) y = ρ i T y := by
          intro A hA y hyA
          have hy_er : y ∈ T.erase g := hA hyA
          have hyT : y ∈ T := Finset.erase_subset g T hy_er
          dsimp only [ρ]
          by_cases hpos : ((0 : ℝ) : WithBot ℝ) < v i {y}
          · rw [if_pos ⟨hy_er, hpos⟩, if_pos ⟨hyT, hpos⟩]
          · rw [if_neg (fun h => hpos h.2), if_neg (fun h => hpos h.2)]
        refine ⟨⟨hμ_nn, ?_, hμ_sum⟩, ?_⟩
        · intro A hμA
          obtain ⟨hA_sub, hA_li⟩ := hμ_supp A hμA
          refine ⟨hA_sub, ?_⟩
          have hfun : (fun y : A => ρ i T y.1) = (fun y : A => ρ i (T.erase g) y.1) := by
            funext y
            exact (h_eq_on A hA_sub y.1 y.2).symm
          rwa [hfun]
        · intro U
          have hsum_eq :
              (∑ A : Finset (Fin n), μ₀ A * (subspaceLoad (ρ i T) U A : ℝ)) =
              (∑ A : Finset (Fin n), μ₀ A * (subspaceLoad (ρ i (T.erase g)) U A : ℝ)) := by
            apply Finset.sum_congr rfl
            intro A _
            by_cases hμA : μ₀ A = 0
            · simp [hμA]
            · obtain ⟨hA_sub, _⟩ := hμ_supp A hμA
              have himg : ρ i T '' (A : Set (Fin n)) = ρ i (T.erase g) '' (A : Set (Fin n)) := by
                ext z
                simp only [Set.mem_image, Finset.mem_coe]
                constructor
                · rintro ⟨y, hyA, rfl⟩
                  exact ⟨y, hyA, h_eq_on A hA_sub y hyA⟩
                · rintro ⟨y, hyA, rfl⟩
                  exact ⟨y, hyA, (h_eq_on A hA_sub y hyA).symm⟩
              have hload : subspaceLoad (ρ i T) U A = subspaceLoad (ρ i (T.erase g)) U A := by
                dsimp only [subspaceLoad, matroidSpan]
                rw [himg]
              rw [hload]
          rw [hsum_eq]
          exact hμ_load U
      obtain ⟨h_law, h_step⟩ := hProg_rec (ρ i) (P i) (Mpos i) hP_i hRep_i hTrans_i
      refine ⟨hProg_base (ρ i) (P i), ?_, ?_⟩
      · intro S
        obtain ⟨h1, h2, h3⟩ := h_law S
        exact ⟨h1, fun A hA => ⟨(h2 A hA).1, (Matroid.restrict_indep_iff.mp (h2 A hA).2).1⟩, h3⟩
      · intro S hS
        obtain ⟨hq1, hq2, hq3, hq4⟩ := h_step S hS
        refine ⟨hq1, ?_, hq3, hq4⟩
        intro g A hqA
        obtain ⟨hgS, hgP, hAS, hind_ins⟩ := hq2 g A hqA
        exact ⟨hgS, hgP, hAS, (Matroid.restrict_indep_iff.mp hind_ins).1⟩
    · intro prev x bundles _
      let S := insert x prev.toFinset
      let vLoc : Fin m → ItemValuation n :=
        fun i Y => if h : Y ⊆ S then v i Y else ⊥
      have hvLoc_eq : ∀ T ⊆ S, ∀ i : Fin m, ∀ Y ⊆ T, vLoc i Y = v i Y := by
        intro T hTS i Y hYT
        exact dif_pos (Finset.Subset.trans hYT hTS)
      have hXS_eq : prefixPosOptAlloc n m vLoc S = X S :=
        h_opt_loc n m vLoc v S (hvLoc_eq S (Finset.Subset.refl S))
      constructor
      · intro h_none
        dsimp only [rateRule]
        rcases h_none with h_le | h_no_j
        · exact if_pos h_le
        · by_cases h_le : S.card ≤ s
          · exact if_pos h_le
          · rw [if_neg h_le]
            have h_not_ex : ¬ ∃ j : Fin m, x ∈ prefixPosOptAlloc n m vLoc S j := by
              rw [hXS_eq]
              rintro ⟨j, hxj⟩
              exact h_no_j j hxj
            exact dif_neg h_not_ex
      · intro j hs_lt hxj
        have h_not_le : ¬ S.card ≤ s := not_le_of_gt hs_lt
        have h_ex : ∃ j' : Fin m, x ∈ prefixPosOptAlloc n m vLoc S j' := by
          rw [hXS_eq]
          exact ⟨j, hxj⟩
        dsimp only [rateRule]
        rw [if_neg h_not_le, dif_pos h_ex]
        have hj_eq : Classical.choose h_ex = j := by
          have hxj' : x ∈ X S (Classical.choose h_ex) :=
            Eq.mp (congrArg (x ∈ ·) (congrFun hXS_eq (Classical.choose h_ex)))
              (Classical.choose_spec h_ex)
          by_contra hne
          have hdisj := (h_opt_spec n m M w S).1.2 (Classical.choose h_ex) j hne
          exact (Finset.disjoint_left.mp hdisj) hxj' hxj
        rw [hj_eq]
        let ρLoc : Finset (Fin n) → Fin n → (Fin (d j) → F j) :=
          fun T g =>
            if g ∈ T ∧ ((0 : ℝ) : WithBot ℝ) < vLoc j {g} then
              if hgS : g ∈ S then u j g else 0
            else 0
        let PLoc : Finset (Fin n) → Finset (Fin n) :=
          fun T => prefixPosOptAlloc n m vLoc T j
        have hρ_eq : ∀ T ⊆ S, ρLoc T = ρ j T := by
          intro T hTS
          funext g
          dsimp only [ρLoc, ρ]
          by_cases hgT : g ∈ T
          · have hgS : g ∈ S := hTS hgT
            have hsgS : ({g} : Finset (Fin n)) ⊆ S := Finset.singleton_subset_iff.mpr hgS
            have hv_sg : vLoc j {g} = v j {g} := dif_pos hsgS
            rw [hv_sg, dif_pos hgS]
          · rw [if_neg (fun h => hgT h.1), if_neg (fun h => hgT h.1)]
        have hP_eq : ∀ T ⊆ S, PLoc T = P j T := by
          intro T hTS
          dsimp only [PLoc, P, X]
          exact congrFun (h_opt_loc n m vLoc v T (hvLoc_eq T hTS)) j
        have h_loc_S := (hProg j).1 ρLoc (ρ j) PLoc (P j) S hρ_eq hP_eq
        have h_loc_er := (hProg j).1 ρLoc (ρ j) PLoc (P j) (S.erase x)
          (fun T hT => hρ_eq T (Finset.Subset.trans hT (Finset.erase_subset x S)))
          (fun T hT => hP_eq T (Finset.Subset.trans hT (Finset.erase_subset x S)))
        have h_denom : μProg j ρLoc PLoc (S.erase x) (bundles j) = μ j (S.erase x) (bundles j) :=
          congrFun h_loc_er.1 (bundles j)
        have h_num : qProg j ρLoc PLoc S x (bundles j) = q j S x (bundles j) :=
          congrFun (congrFun h_loc_S.2 x) (bundles j)
        change some (j, if μProg j ρLoc PLoc (S.erase x) (bundles j) = 0 then 0
                        else qProg j ρLoc PLoc S x (bundles j) /
                             μProg j ρLoc PLoc (S.erase x) (bundles j)) =
               some (j, if μ j (S.erase x) (bundles j) = 0 then 0
                        else q j S x (bundles j) / μ j (S.erase x) (bundles j))
        rw [h_denom, h_num]
  have h_part2 :
      ∀ (n m s : ℕ) (isTernary : Fin m → Bool),
      2 ≤ n → 1 ≤ s → s < n →
        ∃ alg : OnlineWelfareAlg n m,
          (∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
            (∀ i, if isTernary i then IsTernaryMatroid (M i) else IsBinaryMatroid (M i)) →
              let v := fun i => weightedMatroidVal (M i) (w i)
              (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
                let st := runDetWelfareSteps (alg.det ω) v π k hk
                IsAllocOf st.1.toFinset st.2 ∧
                ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
              (((secretaryCutoffConst n s * optWelfare v : ℝ) : WithBot ℝ) ≤
                expectedWelfareVal alg v)) ∧
          (∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
            (∀ i g, 0 ≤ w i g) →
            (∀ i, if isTernary i then IsTernaryMatroid (M i) else IsBinaryMatroid (M i)) →
              let vR := fun i => weightedMatroidRankVal (M i) (w i)
              (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
                let st := runDetWelfareSteps (alg.det ω) vR π k hk
                IsAllocOf st.1.toFinset st.2 ∧
                ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
              (((secretaryCutoffConst n s * optWelfare vR : ℝ) : WithBot ℝ) ≤
                expectedWelfareVal alg vR)) := by
    intro n m s isTernary hn hs1 hsn
    have h_can_loc : ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F]
        (vi vi' : ItemValuation n) (T : Finset (Fin n)),
        (∀ Y ⊆ T, vi Y = vi' Y) →
        canonicalLocalRep F vi T = canonicalLocalRep F vi' T := by
      intro F _ _ _ vi vi' T h_eq
      let Q₁ : (Fin n → (Fin n → F)) → Prop :=
        fun uLoc => ∀ X ⊆ T, LinearIndependent F (fun g : X => uLoc g.1) ↔ obsPosIndep vi T X
      let Q₂ : (Fin n → (Fin n → F)) → Prop :=
        fun uLoc => ∀ X ⊆ T, LinearIndependent F (fun g : X => uLoc g.1) ↔ obsPosIndep vi' T X
      have hpred : Q₁ = Q₂ := by
        funext uLoc
        apply propext
        constructor <;> intro h X hXT
        · exact (h X hXT).trans (h_obs_loc n vi vi' T h_eq X hXT)
        · exact (h X hXT).trans (h_obs_loc n vi vi' T h_eq X hXT).symm
      have h_dite : ∀ (R₁ R₂ : (Fin n → (Fin n → F)) → Prop)
          [d₁ : Decidable (∃ u, R₁ u)] [d₂ : Decidable (∃ u, R₂ u)],
          R₁ = R₂ →
          @dite _ (∃ u, R₁ u) d₁ (fun h => Classical.choose h) (fun _ => 0) =
          @dite _ (∃ u, R₂ u) d₂ (fun h => Classical.choose h) (fun _ => 0) := by
        intro R₁ R₂ d₁ d₂ hR
        subst hR
        rw [Subsingleton.elim d₁ d₂]
      exact @h_dite Q₁ Q₂ _ _ hpred
    have h_bidder_b : ∀ (b : Bool) (Mi : Matroid (Fin n)) (wi : Fin n → ℝ),
        (if b then IsTernaryMatroid Mi else IsBinaryMatroid Mi) →
        let vi := weightedMatroidVal Mi wi
        let Mposi := Mi.restrict {g : Fin n | 0 < wi g}
        let ρi : Finset (Fin n) → Fin n → (Fin n → FBool b) :=
          fun T => canonicalLocalRep (FBool b) vi T
        (∀ (T X : Finset (Fin n)), X ⊆ T →
          (LinearIndependent (FBool b) (fun g : X => ρi T g.1) ↔
            Mposi.Indep (X : Set (Fin n)))) ∧
        (∀ T, ∀ g ∈ T, ∀ (β : ℝ) (μ₀ : Finset (Fin n) → ℝ),
          0 ≤ β →
          IsSubspaceBetaBounded (ρi (T.erase g)) (T.erase g) β μ₀ →
          IsSubspaceBetaBounded (ρi T) (T.erase g) β μ₀) := by
      intro b Mi wi hMi
      cases b with
      | false =>
        dsimp only [FBool] at *
        rw [if_neg Bool.false_ne_true] at hMi
        rcases hMi with ⟨di, ui, hui⟩
        have hpos_ui := h_pos_rep (ZMod 2) Mi wi ui hui
        have h_rep_T : ∀ T : Finset (Fin n), ∀ X ⊆ T,
            LinearIndependent (ZMod 2)
              (fun g : X => canonicalLocalRep (ZMod 2) (weightedMatroidVal Mi wi) T g.1) ↔
            (Mi.restrict {g : Fin n | 0 < wi g}).Indep (X : Set (Fin n)) := by
          intro T
          obtain ⟨uLoc, huLoc⟩ := h_dim_comp n di (ZMod 2)
            (Mi.restrict {g : Fin n | 0 < wi g}) (fun g => if 0 < wi g then ui g else 0) T hpos_ui
          have hex : ∃ u0 : Fin n → (Fin n → ZMod 2),
              ∀ X ⊆ T, LinearIndependent (ZMod 2) (fun g : X => u0 g.1) ↔
                obsPosIndep (weightedMatroidVal Mi wi) T X := by
            refine ⟨uLoc, fun X hXT => ?_⟩
            exact (huLoc X hXT).trans (h_obs_val n Mi wi T X hXT).symm
          intro X hXT
          dsimp only [canonicalLocalRep]
          rw [dif_pos hex]
          exact (Classical.choose_spec hex X hXT).trans (h_obs_val n Mi wi T X hXT)
        refine ⟨h_rep_T, ?_⟩
        intro T g _ β μ₀ hβ hbound
        apply h_trans_2 n n n (T.erase g) _ _ β μ₀ hβ _ hbound
        intro X hX_er
        exact (h_rep_T (T.erase g) X hX_er).trans
          (h_rep_T T X (Finset.Subset.trans hX_er (Finset.erase_subset g T))).symm
      | true =>
        dsimp only [FBool] at *
        rw [if_pos rfl] at hMi
        rcases hMi with ⟨di, ui, hui⟩
        have hpos_ui := h_pos_rep (ZMod 3) Mi wi ui hui
        have h_rep_T : ∀ T : Finset (Fin n), ∀ X ⊆ T,
            LinearIndependent (ZMod 3)
              (fun g : X => canonicalLocalRep (ZMod 3) (weightedMatroidVal Mi wi) T g.1) ↔
            (Mi.restrict {g : Fin n | 0 < wi g}).Indep (X : Set (Fin n)) := by
          intro T
          obtain ⟨uLoc, huLoc⟩ := h_dim_comp n di (ZMod 3)
            (Mi.restrict {g : Fin n | 0 < wi g}) (fun g => if 0 < wi g then ui g else 0) T hpos_ui
          have hex : ∃ u0 : Fin n → (Fin n → ZMod 3),
              ∀ X ⊆ T, LinearIndependent (ZMod 3) (fun g : X => u0 g.1) ↔
                obsPosIndep (weightedMatroidVal Mi wi) T X := by
            refine ⟨uLoc, fun X hXT => ?_⟩
            exact (huLoc X hXT).trans (h_obs_val n Mi wi T X hXT).symm
          intro X hXT
          dsimp only [canonicalLocalRep]
          rw [dif_pos hex]
          exact (Classical.choose_spec hex X hXT).trans (h_obs_val n Mi wi T X hXT)
        refine ⟨h_rep_T, ?_⟩
        intro T g _ β μ₀ hβ hbound
        apply h_trans_3 n n n (T.erase g) _ _ β μ₀ hβ _ hbound
        intro X hX_er
        exact (h_rep_T (T.erase g) X hX_er).trans
          (h_rep_T T X (Finset.Subset.trans hX_er (Finset.erase_subset g T))).symm
    let hlp := fun i : Fin m => lem_local_rep_prefix_lp n n s hs1 (FBool (isTernary i))
    let μProg := fun i : Fin m => (hlp i).choose
    let qProg := fun i : Fin m => (hlp i).choose_spec.choose
    have hProg := fun i : Fin m => (hlp i).choose_spec.choose_spec
    let rateFor (S : Finset (Fin n)) (vLoc : Fin m → ItemValuation n)
        (x : Fin n) (bundles : Fin m → Finset (Fin n)) (j : Fin m) : Fin m × ℝ :=
      let ρLoc : Finset (Fin n) → Fin n → (Fin n → FBool (isTernary j)) :=
        fun T => canonicalLocalRep (FBool (isTernary j)) (vLoc j) T
      let PLoc : Finset (Fin n) → Finset (Fin n) :=
        fun T => prefixPosOptAlloc n m vLoc T j
      let denom := μProg j ρLoc PLoc (S.erase x) (bundles j)
      let num := qProg j ρLoc PLoc S x (bundles j)
      (j, if denom = 0 then 0 else num / denom)
    let rateRule :
        (prev : List (Fin n)) → (x : Fin n) → (bundles : Fin m → Finset (Fin n)) →
        (Fin m → {T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → WithBot ℝ) →
        ((i : Fin m) → {g : Fin n // g ∈ insert x prev.toFinset} → (Fin 0 → Unit)) →
        Option (Fin m × ℝ) :=
      fun prev x bundles oracle _ =>
        let S := insert x prev.toFinset
        if S.card ≤ s then none
        else
          let vLoc : Fin m → ItemValuation n :=
            fun i Y => if h : Y ⊆ S then oracle i ⟨Y, h⟩ else ⊥
          let XS := prefixPosOptAlloc n m vLoc S
          if h_rec : ∃ j : Fin m, x ∈ XS j then
            some (rateFor S vLoc x bundles (Classical.choose h_rec))
          else none
    obtain ⟨algRep₀, halgRep₀⟩ :=
      lem_markov_threshold_welfare n m s hn hs1 hsn (fun _ => Unit) (fun _ => 0) rateRule
    let uDummy : (i : Fin m) → Fin n → (Fin 0 → Unit) := fun _ _ => Fin.elim0
    let alg₀ : OnlineWelfareAlg n m :=
      { Seed := algRep₀.Seed
        measSeed := algRep₀.measSeed
        seedMeasure := algRep₀.seedMeasure
        isProb := algRep₀.isProb
        det := fun ω =>
          { step := fun prev x bundles oracle =>
              (algRep₀.det ω).step prev x bundles oracle (fun _ _ => Fin.elim0) }
        meas_step := fun prev x bundles oracle dec =>
          algRep₀.meas_step prev x bundles oracle (fun _ _ => Fin.elim0) dec }
    have h_steps_eq : ∀ (v : Fin m → ItemValuation n) (ω : alg₀.Seed)
        (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
        runDetWelfareSteps (alg₀.det ω) v π k hk =
        runDetRepresentedWelfareSteps (algRep₀.det ω) v uDummy π k hk := by
      intro v ω π k
      induction k with
      | zero =>
        intro _
        rfl
      | succ k ih =>
        intro hk
        dsimp only [runDetWelfareSteps, runDetRepresentedWelfareSteps, alg₀, uDummy]
        rw [ih (Nat.le_of_succ_le hk)]
    have h_exp_eq : ∀ (v : Fin m → ItemValuation n),
        expectedWelfareVal alg₀ v = expectedRepresentedWelfareVal algRep₀ v uDummy := by
      intro v
      have h_prob : algWelfareProb alg₀ v = algRepresentedWelfareProb algRep₀ v uDummy := by
        funext X
        dsimp only [algWelfareProb, algRepresentedWelfareProb, runDetWelfare,
          runDetRepresentedWelfare]
        congr 1
        apply Finset.sum_congr rfl
        intro π _
        have h_set :
            {ω : alg₀.Seed | (runDetWelfareSteps (alg₀.det ω) v π n (le_refl n)).2 = X} =
            {ω : algRep₀.Seed |
              (runDetRepresentedWelfareSteps (algRep₀.det ω) v uDummy π n (le_refl n)).2 = X} := by
          ext ω
          change (runDetWelfareSteps (alg₀.det ω) v π n (le_refl n)).2 = X ↔
            (runDetRepresentedWelfareSteps (algRep₀.det ω) v uDummy π n (le_refl n)).2 = X
          rw [h_steps_eq v ω π n (le_refl n)]
        change algRep₀.seedMeasure.real
            {ω : alg₀.Seed | (runDetWelfareSteps (alg₀.det ω) v π n (le_refl n)).2 = X} =
          algRep₀.seedMeasure.real
            {ω : algRep₀.Seed |
              (runDetRepresentedWelfareSteps (algRep₀.det ω) v uDummy π n (le_refl n)).2 = X}
        rw [h_set]
      dsimp only [expectedWelfareVal, expectedRepresentedWelfareVal]
      rw [h_prob]
    apply h_rank_upgrade n m (secretaryCutoffConst n s) isTernary alg₀
    intro M w hM
    let v : Fin m → ItemValuation n := fun i => weightedMatroidVal (M i) (w i)
    have h_rep_res :
        (∀ (ω : algRep₀.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
          let st := runDetRepresentedWelfareSteps (algRep₀.det ω) v uDummy π k hk
          IsAllocOf st.1.toFinset st.2 ∧
          ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
        (((secretaryCutoffConst n s * optWelfare v : ℝ) : WithBot ℝ) ≤
          expectedRepresentedWelfareVal algRep₀ v uDummy) := by
      apply halgRep₀ M w uDummy
      let Mpos : Fin m → Matroid (Fin n) := fun i => (M i).restrict {g : Fin n | 0 < w i g}
      let X : Finset (Fin n) → Fin m → Finset (Fin n) := fun S => prefixPosOptAlloc n m v S
      let ρ : (i : Fin m) → Finset (Fin n) → Fin n → (Fin n → FBool (isTernary i)) :=
        fun i T => canonicalLocalRep (FBool (isTernary i)) (v i) T
      let P : Fin m → Finset (Fin n) → Finset (Fin n) := fun i T => X T i
      let μ : Fin m → Finset (Fin n) → Finset (Fin n) → ℝ := fun i => μProg i (ρ i) (P i)
      let q : Fin m → Finset (Fin n) → Fin n → Finset (Fin n) → ℝ := fun i => qProg i (ρ i) (P i)
      refine ⟨X, μ, q, ?_, ?_, ?_⟩
      · intro S
        obtain ⟨h_alloc, h_ind_pos, h_opt_eq⟩ := h_opt_spec n m M w S
        exact ⟨h_alloc, fun i => (Matroid.restrict_indep_iff.mp (h_ind_pos i)).1,
          le_of_eq h_opt_eq⟩
      · intro i
        obtain ⟨_, hProg_base, hProg_rec⟩ := hProg i
        obtain ⟨hRep_i, hTrans_i⟩ := h_bidder_b (isTernary i) (M i) (w i) (hM i)
        have hP_i : ∀ T, P i T ⊆ T ∧ (Mpos i).Indep (P i T : Set (Fin n)) := by
          intro T
          obtain ⟨h_alloc, h_ind_pos, _⟩ := h_opt_spec n m M w T
          exact ⟨h_alloc.1 i, h_ind_pos i⟩
        obtain ⟨h_law, h_step⟩ := hProg_rec (ρ i) (P i) (Mpos i) hP_i hRep_i hTrans_i
        refine ⟨hProg_base (ρ i) (P i), ?_, ?_⟩
        · intro S
          obtain ⟨h1, h2, h3⟩ := h_law S
          exact ⟨h1, fun A hA => ⟨(h2 A hA).1, (Matroid.restrict_indep_iff.mp (h2 A hA).2).1⟩, h3⟩
        · intro S hS
          obtain ⟨hq1, hq2, hq3, hq4⟩ := h_step S hS
          refine ⟨hq1, ?_, hq3, hq4⟩
          intro g A hqA
          obtain ⟨hgS, hgP, hAS, hind_ins⟩ := hq2 g A hqA
          exact ⟨hgS, hgP, hAS, (Matroid.restrict_indep_iff.mp hind_ins).1⟩
      · intro prev x bundles _
        let S := insert x prev.toFinset
        let vLoc : Fin m → ItemValuation n :=
          fun i Y => if h : Y ⊆ S then v i Y else ⊥
        have hvLoc_eq : ∀ T ⊆ S, ∀ i : Fin m, ∀ Y ⊆ T, vLoc i Y = v i Y := by
          intro T hTS i Y hYT
          exact dif_pos (Finset.Subset.trans hYT hTS)
        have hXS_eq : prefixPosOptAlloc n m vLoc S = X S :=
          h_opt_loc n m vLoc v S (hvLoc_eq S (Finset.Subset.refl S))
        constructor
        · intro h_none
          dsimp only [rateRule]
          rcases h_none with h_le | h_no_j
          · exact if_pos h_le
          · by_cases h_le : S.card ≤ s
            · exact if_pos h_le
            · rw [if_neg h_le]
              have h_not_ex : ¬ ∃ j : Fin m, x ∈ prefixPosOptAlloc n m vLoc S j := by
                rw [hXS_eq]
                rintro ⟨j, hxj⟩
                exact h_no_j j hxj
              exact dif_neg h_not_ex
        · intro j hs_lt hxj
          have h_not_le : ¬ S.card ≤ s := not_le_of_gt hs_lt
          have h_ex : ∃ j' : Fin m, x ∈ prefixPosOptAlloc n m vLoc S j' := by
            rw [hXS_eq]
            exact ⟨j, hxj⟩
          dsimp only [rateRule]
          rw [if_neg h_not_le, dif_pos h_ex]
          have hj_eq : Classical.choose h_ex = j := by
            have hxj' : x ∈ X S (Classical.choose h_ex) :=
              Eq.mp (congrArg (x ∈ ·) (congrFun hXS_eq (Classical.choose h_ex)))
                (Classical.choose_spec h_ex)
            by_contra hne
            have hdisj := (h_opt_spec n m M w S).1.2 (Classical.choose h_ex) j hne
            exact (Finset.disjoint_left.mp hdisj) hxj' hxj
          rw [hj_eq]
          let ρLoc : Finset (Fin n) → Fin n → (Fin n → FBool (isTernary j)) :=
            fun T => canonicalLocalRep (FBool (isTernary j)) (vLoc j) T
          let PLoc : Finset (Fin n) → Finset (Fin n) :=
            fun T => prefixPosOptAlloc n m vLoc T j
          have hρ_eq : ∀ T ⊆ S, ρLoc T = ρ j T := by
            intro T hTS
            dsimp only [ρLoc, ρ]
            exact h_can_loc (FBool (isTernary j)) (vLoc j) (v j) T (fun Y hYT => hvLoc_eq T hTS j Y hYT)
          have hP_eq : ∀ T ⊆ S, PLoc T = P j T := by
            intro T hTS
            dsimp only [PLoc, P, X]
            exact congrFun (h_opt_loc n m vLoc v T (hvLoc_eq T hTS)) j
          have h_loc_S := (hProg j).1 ρLoc (ρ j) PLoc (P j) S hρ_eq hP_eq
          have h_loc_er := (hProg j).1 ρLoc (ρ j) PLoc (P j) (S.erase x)
            (fun T hT => hρ_eq T (Finset.Subset.trans hT (Finset.erase_subset x S)))
            (fun T hT => hP_eq T (Finset.Subset.trans hT (Finset.erase_subset x S)))
          have h_denom : μProg j ρLoc PLoc (S.erase x) (bundles j) = μ j (S.erase x) (bundles j) :=
            congrFun h_loc_er.1 (bundles j)
          have h_num : qProg j ρLoc PLoc S x (bundles j) = q j S x (bundles j) :=
            congrFun (congrFun h_loc_S.2 x) (bundles j)
          change some (j, if μProg j ρLoc PLoc (S.erase x) (bundles j) = 0 then 0
                          else qProg j ρLoc PLoc S x (bundles j) /
                               μProg j ρLoc PLoc (S.erase x) (bundles j)) =
                 some (j, if μ j (S.erase x) (bundles j) = 0 then 0
                          else q j S x (bundles j) / μ j (S.erase x) (bundles j))
          rw [h_denom, h_num]
    refine ⟨?_, ?_⟩
    · intro ω π k hk
      rw [h_steps_eq v ω π k hk]
      exact h_rep_res.1 ω π k hk
    · rw [h_exp_eq v]
      exact h_rep_res.2
  have h_part3c :
      ∀ (n m : ℕ) (isTernary : Fin m → Bool),
        ∃ alg : OnlineWelfareAlg n m,
          ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
            (∀ i, if isTernary i then IsTernaryMatroid (M i) else IsBinaryMatroid (M i)) →
              let v := fun i => weightedMatroidVal (M i) (w i)
              (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
                let st := runDetWelfareSteps (alg.det ω) v π k hk
                IsAllocOf st.1.toFinset st.2 ∧
                ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
              (((invE * optWelfare v : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg v) := by
    intro n m isTernary
    by_cases hn : 2 ≤ n
    · obtain ⟨s, hs1, hsn, hs_invE⟩ := h_dynkin n hn
      obtain ⟨alg, halg_v, _⟩ := h_part2 n m s isTernary hn hs1 hsn
      refine ⟨alg, ?_⟩
      intro M w hM
      obtain ⟨h_feas, h_wel⟩ := halg_v M w hM
      refine ⟨h_feas, ?_⟩
      have h_le : invE * optWelfare (fun i => weightedMatroidVal (M i) (w i)) ≤
          secretaryCutoffConst n s * optWelfare (fun i => weightedMatroidVal (M i) (w i)) :=
        mul_le_mul_of_nonneg_right hs_invE (h_opt_nonneg n m M w)
      exact le_trans (WithBot.coe_le_coe.mpr h_le) h_wel
    · obtain ⟨alg, halg⟩ := h_small_n n m (Nat.lt_of_not_ge hn)
      exact ⟨alg, fun M w _ => halg M w⟩
  refine ⟨h_part1, h_part2, ?_, ?_, h_part3c, ?_, lem_remark_f5_u36_divergence⟩
  · intro n m
    obtain ⟨alg, halg⟩ := h_part3c n m (fun _ => false)
    refine ⟨alg, ?_⟩
    intro M w hM
    exact halg M w (fun i => by simp [hM i])
  · intro n m
    obtain ⟨alg, halg⟩ := h_part3c n m (fun _ => true)
    refine ⟨alg, ?_⟩
    intro M w hM
    exact halg M w (fun i => by simp [hM i])
  · intro n m F _ _ _ d
    by_cases hn : 2 ≤ n
    · obtain ⟨s, hs1, hsn, hs_invE⟩ := h_dynkin n hn
      obtain ⟨alg, halg⟩ := h_part1 n m s F d hn hs1 hsn
      refine ⟨alg, ?_⟩
      intro M w u hu
      obtain ⟨h_feas, h_wel⟩ := halg M w u hu
      refine ⟨h_feas, ?_⟩
      have h_le : invE * optWelfare (fun i => weightedMatroidVal (M i) (w i)) ≤
          secretaryCutoffConst n s * optWelfare (fun i => weightedMatroidVal (M i) (w i)) :=
        mul_le_mul_of_nonneg_right hs_invE (h_opt_nonneg n m M w)
      exact le_trans (WithBot.coe_le_coe.mpr h_le) h_wel
    · obtain ⟨alg₀, halg₀⟩ := h_small_n n m (Nat.lt_of_not_ge hn)
      let alg : RepresentedOnlineWelfareAlg n m F d :=
        { Seed := alg₀.Seed
          measSeed := alg₀.measSeed
          seedMeasure := alg₀.seedMeasure
          isProb := alg₀.isProb
          det := fun ω =>
            { step := fun prev x bundles oracle _ =>
                (alg₀.det ω).step prev x bundles oracle }
          meas_step := fun prev x bundles oracle _ dec =>
            alg₀.meas_step prev x bundles oracle dec }
      have h_steps_eq : ∀ (v : Fin m → ItemValuation n)
          (u : (i : Fin m) → Fin n → (Fin (d i) → F i))
          (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
          runDetRepresentedWelfareSteps (alg.det ω) v u π k hk =
          runDetWelfareSteps (alg₀.det ω) v π k hk := by
        intro v u ω π k
        induction k with
        | zero =>
          intro _
          rfl
        | succ k ih =>
          intro hk
          dsimp only [runDetRepresentedWelfareSteps, runDetWelfareSteps, alg]
          rw [ih (Nat.le_of_succ_le hk)]
      refine ⟨alg, ?_⟩
      intro M w u _
      let v : Fin m → ItemValuation n := fun i => weightedMatroidVal (M i) (w i)
      obtain ⟨h_feas, h_wel⟩ := halg₀ M w
      refine ⟨?_, ?_⟩
      · intro ω π k hk
        rw [h_steps_eq v u ω π k hk]
        exact h_feas ω π k hk
      · have h_prob : algRepresentedWelfareProb alg v u = algWelfareProb alg₀ v := by
          funext X
          dsimp only [algRepresentedWelfareProb, algWelfareProb,
            runDetRepresentedWelfare, runDetWelfare]
          congr 1
          apply Finset.sum_congr rfl
          intro π _
          have h_set :
              {ω : alg.Seed |
                (runDetRepresentedWelfareSteps (alg.det ω) v u π n (le_refl n)).2 = X} =
              {ω : alg₀.Seed |
                (runDetWelfareSteps (alg₀.det ω) v π n (le_refl n)).2 = X} := by
            ext ω
            change (runDetRepresentedWelfareSteps (alg.det ω) v u π n (le_refl n)).2 = X ↔
              (runDetWelfareSteps (alg₀.det ω) v π n (le_refl n)).2 = X
            rw [h_steps_eq v u ω π n (le_refl n)]
          change alg₀.seedMeasure.real
              {ω : alg.Seed |
                (runDetRepresentedWelfareSteps (alg.det ω) v u π n (le_refl n)).2 = X} =
            alg₀.seedMeasure.real
              {ω : alg₀.Seed |
                (runDetWelfareSteps (alg₀.det ω) v π n (le_refl n)).2 = X}
          rw [h_set]
        have h_exp : expectedRepresentedWelfareVal alg v u = expectedWelfareVal alg₀ v := by
          dsimp only [expectedRepresentedWelfareVal, expectedWelfareVal]
          rw [h_prob]
        rw [h_exp]
        exact h_wel

end LinearWelfareInternal

/-- **Theorem E.1(a) (`thm:linear`a, Represented Linear Matroid Welfare with Cutoff `s`)**:
For `2 ≤ n` and `1 ≤ s < n`, running represented subspace-load admission modules side by side
against canonical prefix-optimal proposals achieves `E[∑_i v_i(A_i)] ≥ c_n(s) OPT` while keeping
every bidder's accepted bundle independent at every step. -/
theorem thm_E_1_a_represented
    (n m s : ℕ) (F : Fin m → Type) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    [∀ i, DecidableEq (F i)] (d : Fin m → ℕ)
    (hn2 : 2 ≤ n) (hs1 : 1 ≤ s) (hsn : s < n) :
    ∃ alg : RepresentedOnlineWelfareAlg n m F d,
      ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ)
        (u : (i : Fin m) → Fin n → (Fin (d i) → F i)),
        (∀ i, IsLinearMatroidRep (F i) (M i) (u i)) →
          let v := fun i => weightedMatroidVal (M i) (w i)
          (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
            let st := runDetRepresentedWelfareSteps (alg.det ω) v u π k hk
            IsAllocOf st.1.toFinset st.2 ∧
            ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
          (((secretaryCutoffConst n s * optWelfare v : ℝ) : WithBot ℝ) ≤
            expectedRepresentedWelfareVal alg v u) :=
  LinearWelfareInternal.thm_linear_and_binary_ternary_welfare.1 n m s F d hn2 hs1 hsn

/-- **Theorem E.1(b) (`thm:linear`b, Binary/Ternary Matroid Welfare in Value-Oracle Model)**:
For `2 ≤ n`, `1 ≤ s < n`, and known `𝔽_i ∈ {𝔽₂, 𝔽₃}`, reconstructing canonical projective coordinates
on arrived prefixes (`lem_E_3_unique`) yields a pure value-oracle `OnlineWelfareAlg n m` achieving
`E[∑_i v_i(A_i)] ≥ c_n(s) OPT` with independent bundles at every step. -/
theorem thm_E_1_b_oracle
    (n m s : ℕ) (isTernary : Fin m → Bool)
    (hn2 : 2 ≤ n) (hs1 : 1 ≤ s) (hsn : s < n) :
    ∃ alg : OnlineWelfareAlg n m,
      ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
        (∀ i, if isTernary i then IsTernaryMatroid (M i) else IsBinaryMatroid (M i)) →
          let v := fun i => weightedMatroidVal (M i) (w i)
          (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
            let st := runDetWelfareSteps (alg.det ω) v π k hk
            IsAllocOf st.1.toFinset st.2 ∧
            ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
          (((secretaryCutoffConst n s * optWelfare v : ℝ) : WithBot ℝ) ≤
            expectedWelfareVal alg v) := by
  obtain ⟨alg, h1, _⟩ :=
    LinearWelfareInternal.thm_linear_and_binary_ternary_welfare.2.1 n m s isTernary hn2 hs1 hsn
  exact ⟨alg, h1⟩

/-- **Appendix E Corollary (`sec:linear`, Nonnegative Weighted Matroid Rank Valuations)**:
In the value-oracle model, `M_i|_S` is recovered from `v̄_i(T) = max_{I ⊆ T, I ∈ ℐ(M_i)} ∑_{g ∈ I} w_{i, g}`
via `I ∈ ℐ(M_i)` iff `v̄_i(I) = ∑_{g ∈ I} v̄_i({g})` on items with `v̄_i({g}) > 0`, giving the same
`c_n(s) OPT` guarantee for `weightedMatroidRankVal`. -/
theorem thm_E_1_b_weighted_rank
    (n m s : ℕ) (isTernary : Fin m → Bool)
    (hn2 : 2 ≤ n) (hs1 : 1 ≤ s) (hsn : s < n) :
    ∃ alg : OnlineWelfareAlg n m,
      ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
        (∀ i g, 0 ≤ w i g) →
        (∀ i, if isTernary i then IsTernaryMatroid (M i) else IsBinaryMatroid (M i)) →
          let vR := fun i => weightedMatroidRankVal (M i) (w i)
          (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
            let st := runDetWelfareSteps (alg.det ω) vR π k hk
            IsAllocOf st.1.toFinset st.2 ∧
            ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
          (((secretaryCutoffConst n s * optWelfare vR : ℝ) : WithBot ℝ) ≤
            expectedWelfareVal alg vR) := by
  obtain ⟨alg, _, h2⟩ :=
    LinearWelfareInternal.thm_linear_and_binary_ternary_welfare.2.1 n m s isTernary hn2 hs1 hsn
  exact ⟨alg, h2⟩

/-- **Theorem C (`thm:C`, Pure Binary Matroids — Value-Oracle Model, No Side Tags)**:
Across all `n, m`, there exists a pure value-oracle `OnlineWelfareAlg n m` achieving `≥ OPT / e`
and independent bundles at every step for all binary weighted matroid profiles. -/
theorem thm_C_binary_oracle (n m : ℕ) :
    ∃ alg : OnlineWelfareAlg n m,
      ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
        (∀ i, IsBinaryMatroid (M i)) →
          let v := fun i => weightedMatroidVal (M i) (w i)
          (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
            let st := runDetWelfareSteps (alg.det ω) v π k hk
            IsAllocOf st.1.toFinset st.2 ∧
            ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
          (((invE * optWelfare v : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg v) :=
  LinearWelfareInternal.thm_linear_and_binary_ternary_welfare.2.2.1 n m

/-- **Theorem C (`thm:C`, Pure Ternary Matroids — Value-Oracle Model, No Side Tags)**:
Across all `n, m`, there exists a pure value-oracle `OnlineWelfareAlg n m` achieving `≥ OPT / e`
and independent bundles at every step for all ternary weighted matroid profiles. -/
theorem thm_C_ternary_oracle (n m : ℕ) :
    ∃ alg : OnlineWelfareAlg n m,
      ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
        (∀ i, IsTernaryMatroid (M i)) →
          let v := fun i => weightedMatroidVal (M i) (w i)
          (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
            let st := runDetWelfareSteps (alg.det ω) v π k hk
            IsAllocOf st.1.toFinset st.2 ∧
            ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
          (((invE * optWelfare v : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg v) :=
  LinearWelfareInternal.thm_linear_and_binary_ternary_welfare.2.2.2.1 n m

/-- **Theorem C (`thm:C`, Mixed Binary/Ternary Matroids with Known `𝔽_i ∈ {𝔽₂, 𝔽₃}`)**:
Across all `n, m`, there exists a pure value-oracle `OnlineWelfareAlg n m` achieving `≥ OPT / e`
and independent bundles at every step when each bidder's field `𝔽_i ∈ {𝔽₂, 𝔽₃}` is known. -/
theorem thm_C_mixed_oracle (n m : ℕ) (isTernary : Fin m → Bool) :
    ∃ alg : OnlineWelfareAlg n m,
      ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
        (∀ i, if isTernary i then IsTernaryMatroid (M i) else IsBinaryMatroid (M i)) →
          let v := fun i => weightedMatroidVal (M i) (w i)
          (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
            let st := runDetWelfareSteps (alg.det ω) v π k hk
            IsAllocOf st.1.toFinset st.2 ∧
            ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
          (((invE * optWelfare v : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg v) :=
  LinearWelfareInternal.thm_linear_and_binary_ternary_welfare.2.2.2.2.1 n m isTernary

/-- **Theorem C (`thm:C`, Represented Linear Matroids over Finite Fields)**:
Across all `n, m` and finite fields `𝔽_1, ..., 𝔽_m`, there exists a `RepresentedOnlineWelfareAlg`
achieving `≥ OPT / e` and independent bundles at every step when representing vectors are revealed
upon arrival. -/
theorem thm_C_represented
    (n m : ℕ) (F : Fin m → Type) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    [∀ i, DecidableEq (F i)] (d : Fin m → ℕ) :
    ∃ alg : RepresentedOnlineWelfareAlg n m F d,
      ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ)
        (u : (i : Fin m) → Fin n → (Fin (d i) → F i)),
        (∀ i, IsLinearMatroidRep (F i) (M i) (u i)) →
          let v := fun i => weightedMatroidVal (M i) (w i)
          (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
            let st := runDetRepresentedWelfareSteps (alg.det ω) v u π k hk
            IsAllocOf st.1.toFinset st.2 ∧
            ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
          (((invE * optWelfare v : ℝ) : WithBot ℝ) ≤
            expectedRepresentedWelfareVal alg v u) :=
  LinearWelfareInternal.thm_linear_and_binary_ternary_welfare.2.2.2.2.2.1 n m F d

/-- **Theorem C (`thm:C`, Combined Statement)**:
Bundles all four regimes of Theorem C (`1 / e`-competitive online welfare for pure binary, pure
ternary, mixed binary/ternary in the value-oracle model, and represented linear matroids over
arbitrary finite fields). -/
theorem thm_C :
    (∀ (n m : ℕ),
      ∃ alg : OnlineWelfareAlg n m,
        ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
          (∀ i, IsBinaryMatroid (M i)) →
            let v := fun i => weightedMatroidVal (M i) (w i)
            (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
              let st := runDetWelfareSteps (alg.det ω) v π k hk
              IsAllocOf st.1.toFinset st.2 ∧
              ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
            (((invE * optWelfare v : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg v)) ∧
    (∀ (n m : ℕ),
      ∃ alg : OnlineWelfareAlg n m,
        ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
          (∀ i, IsTernaryMatroid (M i)) →
            let v := fun i => weightedMatroidVal (M i) (w i)
            (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
              let st := runDetWelfareSteps (alg.det ω) v π k hk
              IsAllocOf st.1.toFinset st.2 ∧
              ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
            (((invE * optWelfare v : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg v)) ∧
    (∀ (n m : ℕ) (isTernary : Fin m → Bool),
      ∃ alg : OnlineWelfareAlg n m,
        ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ),
          (∀ i, if isTernary i then IsTernaryMatroid (M i) else IsBinaryMatroid (M i)) →
            let v := fun i => weightedMatroidVal (M i) (w i)
            (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
              let st := runDetWelfareSteps (alg.det ω) v π k hk
              IsAllocOf st.1.toFinset st.2 ∧
              ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
            (((invE * optWelfare v : ℝ) : WithBot ℝ) ≤ expectedWelfareVal alg v)) ∧
    (∀ (n m : ℕ) (F : Fin m → Type) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
        [∀ i, DecidableEq (F i)] (d : Fin m → ℕ),
      ∃ alg : RepresentedOnlineWelfareAlg n m F d,
        ∀ (M : Fin m → Matroid (Fin n)) (w : Fin m → Fin n → ℝ)
          (u : (i : Fin m) → Fin n → (Fin (d i) → F i)),
          (∀ i, IsLinearMatroidRep (F i) (M i) (u i)) →
            let v := fun i => weightedMatroidVal (M i) (w i)
            (∀ (ω : alg.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n),
              let st := runDetRepresentedWelfareSteps (alg.det ω) v u π k hk
              IsAllocOf st.1.toFinset st.2 ∧
              ∀ i : Fin m, (M i).Indep (st.2 i : Set (Fin n))) ∧
            (((invE * optWelfare v : ℝ) : WithBot ℝ) ≤
              expectedRepresentedWelfareVal alg v u)) :=
  ⟨thm_C_binary_oracle, thm_C_ternary_oracle, thm_C_mixed_oracle, thm_C_represented⟩

/-- **Remark E.4 (`rem:fields`, Projective Inequivalence over `𝔽₅` on `U_{3, 6}`)**:
Over `𝔽₅`, there exist two inequivalent representations `uR, uR'` of `U_{3, 6}` and a law `μ` on
bases that is `2/3`-bounded in `uR'`, yet in `uR` fails `β`-boundedness for all `β < 1` because a
nonzero 7th-item vector `h = (1, 0, 3)` lies in `W_R(A)` for every `A ∈ supp(μ)`. -/
theorem rem_E_4_fields :
    ∃ (M : Matroid (Fin 6))
      (uR uR' : Fin 6 → (Fin 3 → ZMod 5))
      (μ : Finset (Fin 6) → ℝ),
      let h : Fin 3 → ZMod 5 := ![1, 0, 3]
      (∀ S : Finset (Fin 6), M.Indep (S : Set (Fin 6)) ↔ S.card ≤ 3) ∧
      IsLinearMatroidRep (ZMod 5) M uR ∧
      IsLinearMatroidRep (ZMod 5) M uR' ∧
      IsSubspaceBetaBounded uR' Finset.univ (2 / 3 : ℝ) μ ∧
      (¬ ∃ β : ℝ, β < 1 ∧ IsSubspaceBetaBounded uR Finset.univ β μ) ∧
      h ≠ 0 ∧
      (∀ A : Finset (Fin 6), μ A ≠ 0 → h ∈ matroidSpan uR A) :=
  LinearWelfareInternal.thm_linear_and_binary_ternary_welfare.2.2.2.2.2.2

end

end GrossSubstitutesWelfare
