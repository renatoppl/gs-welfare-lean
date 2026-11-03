import GrossSubstitutesWelfare.Defs

set_option maxHeartbeats 4000000

/-!
# Appendix E.2: Lemma E.3 — Projective Uniqueness of Binary & Ternary Representations (`lem:unique`)

Formalizes Appendix E.2 Lemma E.3 (`lem:unique`, `[BL76]`) and the base `𝔽₅` representation
divergence of Remark E.4 (`rem:fields`) from *Gross Substitutes Welfare in Random Order*:
- Over `𝔽₂` (`ZMod 2`), any two representations of `M | T` admit a linear isomorphism between their
  spans sending `u_g ↦ u'_g` and mapping `span{u_g : g ∈ X}` onto `span{u'_g : g ∈ X}` for all `X ⊆ T`;
- Over `𝔽₃` (`ZMod 3`), by the Brylawski–Lucas theorem (`[BL76]`, proved here from first principles),
  any two representations of `M | T` admit a linear isomorphism between their spans sending
  `u_g ↦ c_g u'_g` (`c_g ∈ 𝔽₃ˣ`) and mapping `span{u_g : g ∈ X}` onto `span{u'_g : g ∈ X}` for all
  `X ⊆ T`;
- Over `𝔽₅` (`ZMod 5`), two representations of `U_{3, 6}` disagree on subspace-load boundedness
  (`Remark E.4`).
-/

namespace GrossSubstitutesWelfare

open Classical MeasureTheory

noncomputable section

namespace UniqueRepresentationsInternal

/-- **Lemma E.3 (`lem:unique`) & Remark E.4 (`rem:fields`)**:
1. **Binary uniqueness (`𝔽₂ = ZMod 2`)**: Any two representations of `M | T` over `ZMod 2` admit a
   linear isomorphism between their spans sending `u_g` to `u'_g` (`c = 1`) and preserving the span
   of every `X ⊆ T`.
2. **Ternary uniqueness (`𝔽₃ = ZMod 3`, Brylawski–Lucas)**: Any two representations of `M | T` over
   `ZMod 3` admit a linear isomorphism between their spans sending each `u_g` (`g ∈ T`) to a nonzero
   scalar multiple `c_g • u'_g` (`c_g ≠ 0`) and preserving the span of every `X ⊆ T`.
3. **Transfer of `β`-boundedness across binary/ternary representations**: Consequently, in any
   profile where each bidder's matroid restriction on `T` is represented over `ZMod 2` or `ZMod 3`,
   `IsBetaBounded` on `T` is invariant under switching representations of `M_i | T`.
4. **Remark E.4 (`rem:fields`)**: Over `𝔽₅ = ZMod 5`, there exist two representations `u, u'` of
   the uniform matroid `U_{3, 6}` and an allocation law `μ` that is `2/3`-bounded in `u'` yet fails
   `β`-boundedness in `u` for every `β < 1`. -/
def zmod3UnitRatio {α β : Type*} (A A' : Matrix α β (ZMod 3)) (i : α) (j : β) : (ZMod 3)ˣ :=
  if h : A' i j * A i j ≠ 0 then Units.mk0 (A' i j * A i j) h else 1

def zmod3BipAdj {α β : Type*} (A : Matrix α β (ZMod 3)) : α ⊕ β → α ⊕ β → Prop
  | Sum.inl i, Sum.inr j => A i j ≠ 0
  | Sum.inr j, Sum.inl i => A i j ≠ 0
  | _, _ => False

def zmod3BipWeight {α β : Type*} (A A' : Matrix α β (ZMod 3)) : α ⊕ β → α ⊕ β → (ZMod 3)ˣ
  | Sum.inl i, Sum.inr j => zmod3UnitRatio A A' i j
  | Sum.inr j, Sum.inl i => zmod3UnitRatio A A' i j
  | _, _ => 1

def isZMod3BipWalk {α β : Type*} (A : Matrix α β (ZMod 3)) : α ⊕ β → α ⊕ β → List (α ⊕ β) → Prop
  | x, y, [] => x = y
  | x, y, z :: L => zmod3BipAdj A x z ∧ isZMod3BipWalk A z y L

def zmod3WalkWeight {α β : Type*} (A A' : Matrix α β (ZMod 3)) : α ⊕ β → List (α ⊕ β) → (ZMod 3)ˣ
  | _, [] => 1
  | x, z :: L => zmod3BipWeight A A' x z * zmod3WalkWeight A A' z L

end UniqueRepresentationsInternal

section
open UniqueRepresentationsInternal

theorem thm_linear_unique_representations :
    -- (1) Binary projective (exact) uniqueness over ZMod 2
    (∀ (n d d' : ℕ) (M : Matroid (Fin n)) (T : Finset (Fin n))
        (u : Fin n → (Fin d → ZMod 2)) (u' : Fin n → (Fin d' → ZMod 2)),
      (∀ S ⊆ T, M.Indep (S : Set (Fin n)) ↔ LinearIndependent (ZMod 2) (fun g : S => u g.1)) →
      (∀ S ⊆ T, M.Indep (S : Set (Fin n)) ↔ LinearIndependent (ZMod 2) (fun g : S => u' g.1)) →
        let V := Submodule.span (ZMod 2) (u '' (T : Set (Fin n)))
        let V' := Submodule.span (ZMod 2) (u' '' (T : Set (Fin n)))
        ∃ φ : V ≃ₗ[ZMod 2] V',
          (∀ (g : Fin n) (hg : g ∈ T),
            (φ ⟨u g, Submodule.subset_span ⟨g, hg, rfl⟩⟩ : Fin d' → ZMod 2) = u' g) ∧
          (∀ X ⊆ T, ∀ v : V,
            (v : Fin d → ZMod 2) ∈ Submodule.span (ZMod 2) (u '' (X : Set (Fin n))) ↔
            (φ v : Fin d' → ZMod 2) ∈ Submodule.span (ZMod 2) (u' '' (X : Set (Fin n))))) ∧
    -- (2) Ternary projective uniqueness over ZMod 3 (Brylawski–Lucas)
    (∀ (n d d' : ℕ) (M : Matroid (Fin n)) (T : Finset (Fin n))
        (u : Fin n → (Fin d → ZMod 3)) (u' : Fin n → (Fin d' → ZMod 3)),
      (∀ S ⊆ T, M.Indep (S : Set (Fin n)) ↔ LinearIndependent (ZMod 3) (fun g : S => u g.1)) →
      (∀ S ⊆ T, M.Indep (S : Set (Fin n)) ↔ LinearIndependent (ZMod 3) (fun g : S => u' g.1)) →
        let V := Submodule.span (ZMod 3) (u '' (T : Set (Fin n)))
        let V' := Submodule.span (ZMod 3) (u' '' (T : Set (Fin n)))
        ∃ φ : V ≃ₗ[ZMod 3] V',
          (∀ (g : Fin n) (hg : g ∈ T), ∃ c : ZMod 3, c ≠ 0 ∧
            (φ ⟨u g, Submodule.subset_span ⟨g, hg, rfl⟩⟩ : Fin d' → ZMod 3) = c • u' g) ∧
          (∀ X ⊆ T, ∀ v : V,
            (v : Fin d → ZMod 3) ∈ Submodule.span (ZMod 3) (u '' (X : Set (Fin n))) ↔
            (φ v : Fin d' → ZMod 3) ∈ Submodule.span (ZMod 3) (u' '' (X : Set (Fin n))))) ∧
    -- (3) Remark E.4: Larger-field counterexample over ZMod 5 on U_{3,6}
    (∃ (M : Matroid (Fin 6))
        (u u' : (i : Fin 1) → Fin 6 → (Fin 3 → ZMod 5))
        (μ : (Fin 1 → Finset (Fin 6)) → ℝ),
      (∀ S : Finset (Fin 6), M.Indep (S : Set (Fin 6)) ↔ S.card ≤ 3) ∧
      IsLinearMatroidRep (ZMod 5) M (u 0) ∧
      IsLinearMatroidRep (ZMod 5) M (u' 0) ∧
      IsBetaBounded u' Finset.univ (2 / 3 : ℝ) μ ∧
      ¬ ∃ β : ℝ, β < 1 ∧ IsBetaBounded u Finset.univ β μ) :=
by
  
  have h_span : ∀ (F : Type) [Field F] (n d d' : ℕ) (T : Finset (Fin n))
      (u : Fin n → (Fin d → F)) (u' : Fin n → (Fin d' → F))
      (φ : Submodule.span F (u '' (T : Set (Fin n))) ≃ₗ[F]
           Submodule.span F (u' '' (T : Set (Fin n)))),
      (∀ (g : Fin n) (hg : g ∈ T), ∃ c : F, c ≠ 0 ∧
        (φ ⟨u g, Submodule.subset_span ⟨g, hg, rfl⟩⟩ : Fin d' → F) = c • u' g) →
      ∀ X ⊆ T, ∀ v : Submodule.span F (u '' (T : Set (Fin n))),
        (v : Fin d → F) ∈ Submodule.span F (u '' (X : Set (Fin n))) ↔
        (φ v : Fin d' → F) ∈ Submodule.span F (u' '' (X : Set (Fin n))) := by
    intro F instF n d d' T u u' φ hφ X hXT v
    let V := Submodule.span F (u '' (T : Set (Fin n)))
    let V' := Submodule.span F (u' '' (T : Set (Fin n)))
    let SX : Set V := Set.range (fun g : X => (⟨u g.1, Submodule.subset_span ⟨g.1, hXT g.2, rfl⟩⟩ : V))
    let SX' : Set V' := Set.range (fun g : X => (⟨u' g.1, Submodule.subset_span ⟨g.1, hXT g.2, rfl⟩⟩ : V'))
    have hmapV : Submodule.map V.subtype (Submodule.span F SX) =
        Submodule.span F (u '' (X : Set (Fin n))) := by
      rw [Submodule.map_span]
      congr 1
      ext w
      simp only [Set.mem_image, SX, Set.mem_range, Finset.mem_coe]
      constructor
      · rintro ⟨_, ⟨⟨g, hg⟩, rfl⟩, rfl⟩
        exact ⟨g, hg, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨⟨u g, Submodule.subset_span ⟨g, hXT hg, rfl⟩⟩, ⟨⟨g, hg⟩, rfl⟩, rfl⟩
    have hmapV' : Submodule.map V'.subtype (Submodule.span F SX') =
        Submodule.span F (u' '' (X : Set (Fin n))) := by
      rw [Submodule.map_span]
      congr 1
      ext w
      simp only [Set.mem_image, SX', Set.mem_range, Finset.mem_coe]
      constructor
      · rintro ⟨_, ⟨⟨g, hg⟩, rfl⟩, rfl⟩
        exact ⟨g, hg, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨⟨u' g, Submodule.subset_span ⟨g, hXT hg, rfl⟩⟩, ⟨⟨g, hg⟩, rfl⟩, rfl⟩
    have hv_iff : (v : Fin d → F) ∈ Submodule.span F (u '' (X : Set (Fin n))) ↔
        v ∈ Submodule.span F SX := by
      rw [← hmapV]
      exact ⟨fun ⟨w, hw, hwv⟩ => Subtype.ext hwv ▸ hw, fun hv => ⟨v, hv, rfl⟩⟩
    have hφv_iff : (φ v : Fin d' → F) ∈ Submodule.span F (u' '' (X : Set (Fin n))) ↔
        φ v ∈ Submodule.span F SX' := by
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
  
  have h_single_basis : ∀ (F : Type) [Field F] {n d : ℕ} (T D : Finset (Fin n)), D ⊆ T →
      ∀ (u : Fin n → (Fin d → F)),
      LinearIndependent F (fun b : D => u b.1) →
      (∀ g ∈ T \ D, ¬ LinearIndependent F (fun x : (insert g D : Finset (Fin n)) => u x.1)) →
      ∃ (bV : Module.Basis D F (Submodule.span F (u '' (T : Set (Fin n))))),
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
    clear h_span
    intro F instF n d T D hDT u hli_D hmax_D
    let V := Submodule.span F (u '' (T : Set (Fin n)))
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
  have h_common_basis : ∀ (F : Type) [Field F] (n d d' : ℕ) (T : Finset (Fin n))
      (u : Fin n → (Fin d → F)) (u' : Fin n → (Fin d' → F)),
      (∀ S ⊆ T, LinearIndependent F (fun g : S => u g.1) ↔
                LinearIndependent F (fun g : S => u' g.1)) →
      ∃ (D : Finset (Fin n)) (_ : D ⊆ T)
        (bV : Module.Basis D F (Submodule.span F (u '' (T : Set (Fin n)))))
        (bV' : Module.Basis D F (Submodule.span F (u' '' (T : Set (Fin n))))),
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
    clear h_span
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
  clear h_single_basis
  
  have h_part1 : ∀ (n d d' : ℕ) (M : Matroid (Fin n)) (T : Finset (Fin n))
      (u : Fin n → (Fin d → ZMod 2)) (u' : Fin n → (Fin d' → ZMod 2)),
      (∀ S ⊆ T, M.Indep (S : Set (Fin n)) ↔ LinearIndependent (ZMod 2) (fun g : S => u g.1)) →
      (∀ S ⊆ T, M.Indep (S : Set (Fin n)) ↔ LinearIndependent (ZMod 2) (fun g : S => u' g.1)) →
        let V := Submodule.span (ZMod 2) (u '' (T : Set (Fin n)))
        let V' := Submodule.span (ZMod 2) (u' '' (T : Set (Fin n)))
        ∃ φ : V ≃ₗ[ZMod 2] V',
          (∀ (g : Fin n) (hg : g ∈ T),
            (φ ⟨u g, Submodule.subset_span ⟨g, hg, rfl⟩⟩ : Fin d' → ZMod 2) = u' g) ∧
          (∀ X ⊆ T, ∀ v : V,
            (v : Fin d → ZMod 2) ∈ Submodule.span (ZMod 2) (u '' (X : Set (Fin n))) ↔
            (φ v : Fin d' → ZMod 2) ∈ Submodule.span (ZMod 2) (u' '' (X : Set (Fin n)))) := by
    intro n d d' M T u u' hu hu' V V'
    have hindep : ∀ S ⊆ T, LinearIndependent (ZMod 2) (fun g : S => u g.1) ↔
                           LinearIndependent (ZMod 2) (fun g : S => u' g.1) :=
      fun S hST => (hu S hST).symm.trans (hu' S hST)
    obtain ⟨D, hDT, bV, bV', hbV, hbV', hdet⟩ :=
      h_common_basis (ZMod 2) n d d' T u u' hindep
    obtain ⟨φ, hφ_bV⟩ : ∃ φ : V ≃ₗ[ZMod 2] V', ∀ b : D, φ (bV b) = bV' b :=
      ⟨bV.equiv bV' (Equiv.refl D), fun b => bV.equiv_apply b bV' (Equiv.refl D)⟩
    have hz2 : ∀ x y : ZMod 2, (x = 0 ↔ y = 0) → x = y := by
      clear hφ_bV φ hdet hbV hbV' bV bV' hDT D hindep hu hu' V V' u u' T M d d' n h_common_basis h_span
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
    refine ⟨φ, hφ_exact, h_span (ZMod 2) n d d' T u u' φ ?_⟩
    intro g hg
    exact ⟨1, one_ne_zero, by rw [one_smul]; exact hφ_exact g hg⟩
  
  have h_zmod3_scale : ∀ (α β : Type) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
      (A A' : Matrix α β (ZMod 3)),
      (∀ (k : ℕ) (r : Fin k → α) (c : Fin k → β),
        (Matrix.submatrix A r c).det = 0 ↔ (Matrix.submatrix A' r c).det = 0) →
      ∃ (σ : α → (ZMod 3)ˣ) (τ : β → (ZMod 3)ˣ),
        ∀ (i : α) (j : β), A' i j = (σ i : ZMod 3) * (τ j : ZMod 3) * A i j := by
    clear h_span h_common_basis h_part1
    intro α β instFα instFβ instDα instDβ A A' hdet
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
    have huR_val : ∀ i j, A i j ≠ 0 → (zmod3UnitRatio A A' i j : ZMod 3) = A' i j * A i j := by
      intro i j hA
      have hA' : A' i j ≠ 0 := fun h => hA (hzero i j |>.mpr h)
      have hmul : A' i j * A i j ≠ 0 := mul_ne_zero hA' hA
      simp only [zmod3UnitRatio, dif_pos hmul, Units.val_mk0]
    have hadj_symm : ∀ x y, zmod3BipAdj A x y ↔ zmod3BipAdj A y x := by
      rintro (i | j) (i' | j') <;> rfl
    have hew_symm : ∀ x y, zmod3BipWeight A A' x y = zmod3BipWeight A A' y x := by
      rintro (i | j) (i' | j') <;> rfl
    have hadj_flip : ∀ x y, zmod3BipAdj A x y → Sum.isLeft x = !Sum.isLeft y := by
      rintro (i | j) (i' | j') h
      · exact False.elim h
      · rfl
      · rfl
      · exact False.elim h
    have hwalk_append : ∀ L₁ L₂ x y z,
        isZMod3BipWalk A x y L₁ → isZMod3BipWalk A y z L₂ →
        isZMod3BipWalk A x z (L₁ ++ L₂) ∧
        zmod3WalkWeight A A' x (L₁ ++ L₂) = zmod3WalkWeight A A' x L₁ * zmod3WalkWeight A A' y L₂ := by
      intro L₁
      induction L₁ with
      | nil =>
        intro L₂ x y z h1 h2
        cases h1
        exact ⟨h2, by simp only [List.nil_append, zmod3WalkWeight, one_mul]⟩
      | cons w L₁ ih =>
        intro L₂ x y z h1 h2
        rcases h1 with ⟨hxw, h1'⟩
        obtain ⟨hw_app, hwt_app⟩ := ih L₂ w y z h1' h2
        refine ⟨⟨hxw, hw_app⟩, ?_⟩
        simp only [List.cons_append, zmod3WalkWeight, hwt_app, mul_assoc]
    have hwalk_split : ∀ L₁ u L₂ x z,
        isZMod3BipWalk A x z (L₁ ++ u :: L₂) →
        isZMod3BipWalk A x u (L₁ ++ [u]) ∧ isZMod3BipWalk A u z L₂ ∧
        zmod3WalkWeight A A' x (L₁ ++ u :: L₂) =
          zmod3WalkWeight A A' x (L₁ ++ [u]) * zmod3WalkWeight A A' u L₂ := by
      intro L₁
      induction L₁ with
      | nil =>
        intro u L₂ x z h
        rcases h with ⟨hxu, huL₂⟩
        refine ⟨⟨hxu, rfl⟩, huL₂, ?_⟩
        simp only [List.nil_append, zmod3WalkWeight, mul_one]
      | cons w L₁ ih =>
        intro u L₂ x z h
        rcases h with ⟨hxw, h'⟩
        obtain ⟨h1, h2, hwt⟩ := ih u L₂ w z h'
        refine ⟨⟨hxw, h1⟩, h2, ?_⟩
        simp only [List.cons_append, zmod3WalkWeight, hwt, mul_assoc]
    have hwalk_rev : ∀ L x y,
        isZMod3BipWalk A x y L →
        ∃ L', isZMod3BipWalk A y x L' ∧ zmod3WalkWeight A A' y L' = zmod3WalkWeight A A' x L := by
      intro L
      induction L with
      | nil =>
        intro x y h
        cases h
        exact ⟨[], rfl, rfl⟩
      | cons w L ih =>
        intro x y ⟨hxw, hwy⟩
        obtain ⟨L', hL', hwt'⟩ := ih w y hwy
        have hwx : isZMod3BipWalk A w x [x] := ⟨(hadj_symm x w).mp hxw, rfl⟩
        obtain ⟨happ, hwt_app⟩ := hwalk_append L' [x] y w x hL' hwx
        refine ⟨L' ++ [x], happ, ?_⟩
        rw [hwt_app, hwt']
        simp only [zmod3WalkWeight, one_mul, hew_symm w x, mul_comm]
    have hwalk_parity : ∀ L x y,
        isZMod3BipWalk A x y L →
        (Even L.length → Sum.isLeft x = Sum.isLeft y) ∧
        (¬ Even L.length → Sum.isLeft x = !Sum.isLeft y) := by
      intro L
      induction L with
      | nil =>
        intro x y h
        cases h
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
        isZMod3BipWalk A x y L → L[L.length - 1]'(Nat.sub_lt (List.length_pos_iff.mpr hne) Nat.zero_lt_one) = y := by
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
        isZMod3BipWalk A x y L →
        ∀ (s : ℕ) (hs : s < L.length),
          zmod3BipAdj A ((x :: L)[s]'(Nat.lt_succ_of_lt hs)) ((x :: L)[s + 1]'(Nat.succ_lt_succ hs)) := by
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
        zmod3WalkWeight A A' x L =
        ∏ s : Fin L.length,
          zmod3BipWeight A A' ((x :: L)[s.1]'(Nat.lt_succ_of_lt s.2))
                              ((x :: L)[s.1 + 1]'(Nat.succ_lt_succ s.2)) := by
      intro L
      induction L with
      | nil =>
        intro x
        simp only [zmod3WalkWeight, List.length_nil, Finset.univ_eq_empty, Finset.prod_empty]
      | cons z M ih =>
        intro x
        simp only [zmod3WalkWeight, ih z, List.length_cons]
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
        L.length = m → isZMod3BipWalk A x x L → zmod3WalkWeight A A' x L = 1 := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        have hinl : ∀ (i₀ : α) (L : List (α ⊕ β)),
            L.length = m → isZMod3BipWalk A (Sum.inl i₀) (Sum.inl i₀) L →
            zmod3WalkWeight A A' (Sum.inl i₀) L = 1 := by
          intro i₀ L hlen hw
          by_cases hnodup : L.Nodup
          · by_cases hchord : ∃ P u Q v R,
                L = (P ++ u :: Q) ++ v :: R ∧ zmod3BipAdj A u v ∧ Q ≠ [] ∧ ¬ (P = [] ∧ R = [])
            · rcases hchord with ⟨P, u, Q, v, R, rfl, huv, hQ_ne, hPR_ne⟩
              obtain ⟨hw1, hwR, hwt1⟩ := hwalk_split (P ++ u :: Q) v R (Sum.inl i₀) (Sum.inl i₀) hw
              have heq_app : (P ++ u :: Q) ++ [v] = P ++ u :: (Q ++ [v]) := by
                simp only [List.append_assoc, List.cons_append]
              obtain ⟨hwP, hwQ, hwt2⟩ := hwalk_split P u (Q ++ [v]) (Sum.inl i₀) v (heq_app ▸ hw1)
              have hvu : zmod3BipAdj A v u := (hadj_symm u v).mp huv
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
              simp only [zmod3WalkWeight, mul_one, hew_symm v u] at h1_C1 h1_C2
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
              exact halg _ _ _ (zmod3BipWeight A A' u v) (hunit_sq _) h1_C1 h1_C2
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
                rcases hw with ⟨hxy, hzy, rfl⟩
                simp only [zmod3WalkWeight, mul_one, hew_symm y (Sum.inl i₀)]
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
                have hwt_formula : zmod3WalkWeight A A' (Sum.inl i₀) L =
                    ∏ t : Fin k, (zmod3UnitRatio A A' (r t) (c t) * zmod3UnitRatio A A' (r (π_cyc t)) (c t)) := by
                  rw [hwalk_wt_prod]
                  let f : Fin (2 * k) → (ZMod 3)ˣ := fun s =>
                    zmod3BipWeight A A'
                      ((Sum.inl i₀ :: L)[s.1]'(by simp only [List.length_cons, hk_len]; omega))
                      ((Sum.inl i₀ :: L)[s.1 + 1]'(by simp only [List.length_cons, hk_len]; omega))
                  have hreindex : (∏ s : Fin L.length,
                      zmod3BipWeight A A' ((Sum.inl i₀ :: L)[s.1]'(Nat.lt_succ_of_lt s.2))
                        ((Sum.inl i₀ :: L)[s.1 + 1]'(Nat.succ_lt_succ s.2))) =
                      ∏ s : Fin (2 * k), f s :=
                    Fintype.prod_equiv (finCongr hk_len) _ _ (fun _ => rfl)
                  rw [hreindex, hprod_even_pairs k f]
                  refine Finset.prod_congr rfl fun t _ => ?_
                  have hf0 : f ⟨2 * t.1, by omega⟩ = zmod3UnitRatio A A' (r t) (c t) := by
                    dsimp only [f]
                    rw [hr t, hc t]; rfl
                  have hf1 : f ⟨2 * t.1 + 1, by omega⟩ = zmod3UnitRatio A A' (r (π_cyc t)) (c t) := by
                    dsimp only [f]
                    rw [hc t, hr_succ t]; rfl
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
                  have hadj_ij : zmod3BipAdj A (L[qi]'hqi_lt) (L[2 * j.1]'h2j_lt) := by
                    rw [hL_qi, hL_2j]; exact hAij
                  let a : ℕ := min qi (2 * j.1)
                  let b : ℕ := max qi (2 * j.1)
                  have hab : a < b := by dsimp [a, b]; omega
                  have hb_lt : b < L.length := by dsimp [b]; omega
                  have hadj_ab : zmod3BipAdj A (L[a]'(Nat.lt_trans hab hb_lt)) (L[b]'hb_lt) := by
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
                    ((zmod3UnitRatio A A' (r t) (c t) * zmod3UnitRatio A A' (r (π_cyc t)) (c t) : (ZMod 3)ˣ) : ZMod 3) =
                    (A' (r t) (c t) * A (r t) (c t)) * (A' (r (π_cyc t)) (c t) * A (r (π_cyc t)) (c t)) := by
                  intro t
                  rw [Units.val_mul, huR_val _ _ (hA_diag t), huR_val _ _ (hA_nxt t)]
                have hprod_eq : (∏ t : Fin k,
                    ((zmod3UnitRatio A A' (r t) (c t) * zmod3UnitRatio A A' (r (π_cyc t)) (c t) : (ZMod 3)ˣ) : ZMod 3)) =
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
            · have hback : isZMod3BipWalk A (Sum.inr j₀) (Sum.inl i₀) [Sum.inl i₀] := ⟨hadj0, rfl⟩
              obtain ⟨hw_rot, hwt_rot⟩ := hwalk_append L' [Sum.inl i₀] (Sum.inl i₀) (Sum.inr j₀) (Sum.inl i₀) hw' hback
              have hlen_rot : (L' ++ [Sum.inl i₀]).length = m := by
                simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
                omega
              have h1 := hinl i₀ (L' ++ [Sum.inl i₀]) hlen_rot hw_rot
              have hwt_eq : zmod3WalkWeight A A' (Sum.inr j₀) (Sum.inl i₀ :: L') =
                  zmod3WalkWeight A A' (Sum.inl i₀) (L' ++ [Sum.inl i₀]) := by
                rw [hwt_rot]
                simp only [zmod3WalkWeight, one_mul, mul_comm]
              exact hwt_eq.trans h1
            · exact False.elim hadj0
    have hpath_indep : ∀ x y L₁ L₂,
        isZMod3BipWalk A x y L₁ → isZMod3BipWalk A x y L₂ →
        zmod3WalkWeight A A' x L₁ = zmod3WalkWeight A A' x L₂ := by
      intro x y L₁ L₂ hw1 hw2
      obtain ⟨L₂', hw2', hwt2'⟩ := hwalk_rev L₂ x y hw2
      obtain ⟨hw_cl, hwt_cl⟩ := hwalk_append L₁ L₂' x y x hw1 hw2'
      have h1 := hclosed_len _ x (L₁ ++ L₂') rfl hw_cl
      rw [hwt_cl, hwt2'] at h1
      calc zmod3WalkWeight A A' x L₁
          = zmod3WalkWeight A A' x L₁ * (zmod3WalkWeight A A' x L₂ * zmod3WalkWeight A A' x L₂) := by
            rw [hunit_sq, mul_one]
        _ = (zmod3WalkWeight A A' x L₁ * zmod3WalkWeight A A' x L₂) * zmod3WalkWeight A A' x L₂ := by
            rw [mul_assoc]
        _ = 1 * zmod3WalkWeight A A' x L₂ := by rw [h1]
        _ = zmod3WalkWeight A A' x L₂ := one_mul _
    have hchoose_congr : ∀ (p q : (α ⊕ β) → Prop) (hp : ∃ z, p z) (hq : ∃ z, q z),
        p = q → Classical.choose hp = Classical.choose hq := by
      intro p q hp hq hpq
      subst hpq
      rfl
    let Comp : (α ⊕ β) → (α ⊕ β) → Prop := fun x z => ∃ L, isZMod3BipWalk A z x L
    have hComp_ne : ∀ x : α ⊕ β, ∃ z, Comp x z := fun x => ⟨x, [], rfl⟩
    let rep : (α ⊕ β) → α ⊕ β := fun x => Classical.choose (hComp_ne x)
    have hrep_spec : ∀ x : α ⊕ β, ∃ L, isZMod3BipWalk A (rep x) x L :=
      fun x => Classical.choose_spec (hComp_ne x)
    let pot : (α ⊕ β) → (ZMod 3)ˣ :=
      fun x => zmod3WalkWeight A A' (rep x) (Classical.choose (hrep_spec x))
    have hpot_adj : ∀ x y, zmod3BipAdj A x y → pot x * pot y = zmod3BipWeight A A' x y := by
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
      have hwLx : isZMod3BipWalk A (rep x) x Lx := Classical.choose_spec (hrep_spec x)
      set Ly := Classical.choose (hrep_spec y)
      have hwLy : isZMod3BipWalk A (rep y) y Ly := Classical.choose_spec (hrep_spec y)
      have hwLy' : isZMod3BipWalk A (rep x) y Ly := hrep_eq.symm ▸ hwLy
      have hpot_y : pot y = zmod3WalkWeight A A' (rep x) Ly := by
        dsimp only [pot]
        rw [hrep_eq]
      obtain ⟨hwLxy, hwtLxy⟩ := hwalk_append Lx [y] (rep x) x y hwLx ⟨hadj, rfl⟩
      have heq_wt := hpath_indep (rep x) y Ly (Lx ++ [y]) hwLy' hwLxy
      rw [← hpot_y, hwtLxy] at heq_wt
      simp only [zmod3WalkWeight, mul_one] at heq_wt
      change pot y = pot x * zmod3BipWeight A A' x y at heq_wt
      calc pot x * pot y
          = pot x * (pot x * zmod3BipWeight A A' x y) := by rw [heq_wt]
        _ = (pot x * pot x) * zmod3BipWeight A A' x y := by rw [mul_assoc]
        _ = zmod3BipWeight A A' x y := by rw [hunit_sq, one_mul]
    refine ⟨fun i => pot (Sum.inl i), fun j => pot (Sum.inr j), fun i j => ?_⟩
    by_cases hA0 : A i j = 0
    · rw [hA0, (hzero i j).mp hA0, mul_zero]
    · have hadj : zmod3BipAdj A (Sum.inl i) (Sum.inr j) := hA0
      have hp := hpot_adj (Sum.inl i) (Sum.inr j) hadj
      have hp_val : ((pot (Sum.inl i) : ZMod 3) * (pot (Sum.inr j) : ZMod 3)) =
          A' i j * A i j := by
        rw [← Units.val_mul, hp]
        exact huR_val i j hA0
      calc A' i j
          = A' i j * (A i j * A i j) := by rw [hz3_sq (A i j) hA0, mul_one]
        _ = (A' i j * A i j) * A i j := by ring
        _ = (pot (Sum.inl i) : ZMod 3) * (pot (Sum.inr j) : ZMod 3) * A i j := by rw [hp_val]
  
  have h_part2 : ∀ (n d d' : ℕ) (M : Matroid (Fin n)) (T : Finset (Fin n))
      (u : Fin n → (Fin d → ZMod 3)) (u' : Fin n → (Fin d' → ZMod 3)),
      (∀ S ⊆ T, M.Indep (S : Set (Fin n)) ↔ LinearIndependent (ZMod 3) (fun g : S => u g.1)) →
      (∀ S ⊆ T, M.Indep (S : Set (Fin n)) ↔ LinearIndependent (ZMod 3) (fun g : S => u' g.1)) →
        let V := Submodule.span (ZMod 3) (u '' (T : Set (Fin n)))
        let V' := Submodule.span (ZMod 3) (u' '' (T : Set (Fin n)))
        ∃ φ : V ≃ₗ[ZMod 3] V',
          (∀ (g : Fin n) (hg : g ∈ T), ∃ c : ZMod 3, c ≠ 0 ∧
            (φ ⟨u g, Submodule.subset_span ⟨g, hg, rfl⟩⟩ : Fin d' → ZMod 3) = c • u' g) ∧
          (∀ X ⊆ T, ∀ v : V,
            (v : Fin d → ZMod 3) ∈ Submodule.span (ZMod 3) (u '' (X : Set (Fin n))) ↔
            (φ v : Fin d' → ZMod 3) ∈ Submodule.span (ZMod 3) (u' '' (X : Set (Fin n)))) := by
    clear h_part1
    intro n d d' M T u u' hu hu' V V'
    have hindep : ∀ S ⊆ T, LinearIndependent (ZMod 3) (fun g : S => u g.1) ↔
                           LinearIndependent (ZMod 3) (fun g : S => u' g.1) :=
      fun S hST => (hu S hST).symm.trans (hu' S hST)
    obtain ⟨D, hDT, bV, bV', hbV, hbV', hdet⟩ :=
      h_common_basis (ZMod 3) n d d' T u u' hindep
    obtain ⟨σ, τ, hscale⟩ := h_zmod3_scale
      D {g : Fin n // g ∈ T \ D}
      (Matrix.of (fun (b : D) (g : {g : Fin n // g ∈ T \ D}) =>
        bV.repr ⟨u g.1, Submodule.subset_span ⟨g.1, (Finset.mem_sdiff.mp g.2).1, rfl⟩⟩ b))
      (Matrix.of (fun (b : D) (g : {g : Fin n // g ∈ T \ D}) =>
        bV'.repr ⟨u' g.1, Submodule.subset_span ⟨g.1, (Finset.mem_sdiff.mp g.2).1, rfl⟩⟩ b))
      hdet
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
    exact ⟨φ, hφ_proj, h_span (ZMod 3) n d d' T u u' φ hφ_proj⟩
  clear h_span h_common_basis h_zmod3_scale
  
  have h_part3 : ∃ (M : Matroid (Fin 6))
      (u u' : (i : Fin 1) → Fin 6 → (Fin 3 → ZMod 5))
      (μ : (Fin 1 → Finset (Fin 6)) → ℝ),
      (∀ S : Finset (Fin 6), M.Indep (S : Set (Fin 6)) ↔ S.card ≤ 3) ∧
      IsLinearMatroidRep (ZMod 5) M (u 0) ∧
      IsLinearMatroidRep (ZMod 5) M (u' 0) ∧
      IsBetaBounded u' Finset.univ (2 / 3 : ℝ) μ ∧
      ¬ ∃ β : ℝ, β < 1 ∧ IsBetaBounded u Finset.univ β μ := by
    clear h_part1 h_part2
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
    let R : Fin 6 → (Fin 3 → ZMod 5) :=
      ![![1, 0, 0], ![0, 0, 1], ![1, 1, 1], ![1, 2, 4], ![1, 3, 4], ![1, 4, 1]]
    let R' : Fin 6 → (Fin 3 → ZMod 5) :=
      ![![1, 0, 0], ![1, 1, 1], ![1, 2, 4], ![1, 4, 1], ![1, 3, 4], ![0, 0, 1]]
    let u : Fin 1 → Fin 6 → (Fin 3 → ZMod 5) := fun _ => R
    let u' : Fin 1 → Fin 6 → (Fin 3 → ZMod 5) := fun _ => R'
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
    have hR_det_bool : ((List.finRange 6).all fun a => (List.finRange 6).all fun b =>
        (List.finRange 6).all fun c =>
          !(Nat.ble (a.1 + 1) b.1 && Nat.ble (b.1 + 1) c.1) ||
          !(Nat.beq (det3 (R a) (R b) (R c)).val 0)) = true := rfl
    have hR'_det_bool : ((List.finRange 6).all fun a => (List.finRange 6).all fun b =>
        (List.finRange 6).all fun c =>
          !(Nat.ble (a.1 + 1) b.1 && Nat.ble (b.1 + 1) c.1) ||
          !(Nat.beq (det3 (R' a) (R' b) (R' c)).val 0)) = true := rfl
    have hR_det : ∀ a b c : Fin 6, a < b → b < c → det3 (R a) (R b) (R c) ≠ 0 := by
      intro a b c hab hbc h0
      have ha := List.mem_finRange a
      have hb := List.mem_finRange b
      have hc := List.mem_finRange c
      have h1 := ((List.all_eq_true.mp hR_det_bool) a ha)
      have h2 := ((List.all_eq_true.mp h1) b hb)
      have h3 := ((List.all_eq_true.mp h2) c hc)
      have hab' : Nat.ble (a.1 + 1) b.1 = true := Nat.ble_eq.mpr hab
      have hbc' : Nat.ble (b.1 + 1) c.1 = true := Nat.ble_eq.mpr hbc
      have h0' : Nat.beq (det3 (R a) (R b) (R c)).val 0 = true := by
        rw [h0]; rfl
      rw [hab', hbc', h0'] at h3
      contradiction
    have hR'_det : ∀ a b c : Fin 6, a < b → b < c → det3 (R' a) (R' b) (R' c) ≠ 0 := by
      intro a b c hab hbc h0
      have ha := List.mem_finRange a
      have hb := List.mem_finRange b
      have hc := List.mem_finRange c
      have h1 := ((List.all_eq_true.mp hR'_det_bool) a ha)
      have h2 := ((List.all_eq_true.mp h1) b hb)
      have h3 := ((List.all_eq_true.mp h2) c hc)
      have hab' : Nat.ble (a.1 + 1) b.1 = true := Nat.ble_eq.mpr hab
      have hbc' : Nat.ble (b.1 + 1) c.1 = true := Nat.ble_eq.mpr hbc
      have h0' : Nat.beq (det3 (R' a) (R' b) (R' c)).val 0 = true := by
        rw [h0]; rfl
      rw [hab', hbc', h0'] at h3
      contradiction
    have hu_li : ∀ S : Finset (Fin 6), LinearIndependent (ZMod 5) (fun g : S => u 0 g.1) ↔ S.card ≤ 3 :=
      hli_of_det R hR_det
    have hu'_li : ∀ S : Finset (Fin 6), LinearIndependent (ZMod 5) (fun g : S => u' 0 g.1) ↔ S.card ≤ 3 :=
      hli_of_det R' hR'_det
    let B0 : Finset (Fin 6) := {0, 1}
    let B1 : Finset (Fin 6) := {2, 3}
    let B2 : Finset (Fin 6) := {4, 5}
    let A0 : Fin 1 → Finset (Fin 6) := fun _ => B0
    let A1 : Fin 1 → Finset (Fin 6) := fun _ => B1
    let A2 : Fin 1 → Finset (Fin 6) := fun _ => B2
    let supp : Finset (Fin 1 → Finset (Fin 6)) := {A0, A1, A2}
    let μ : (Fin 1 → Finset (Fin 6)) → ℝ := fun A => if A ∈ supp then (1 / 3 : ℝ) else 0
    have hA01 : A0 ≠ A1 := by
      intro h
      have hm : (0 : Fin 6) ∈ A0 0 := by simp [A0, B0]
      rw [h] at hm
      simp [A1, B1] at hm
    have hA02 : A0 ≠ A2 := by
      intro h
      have hm : (0 : Fin 6) ∈ A0 0 := by simp [A0, B0]
      rw [h] at hm
      simp [A2, B2] at hm
    have hA12 : A1 ≠ A2 := by
      intro h
      have hm : (2 : Fin 6) ∈ A1 0 := by simp [A1, B1]
      rw [h] at hm
      simp [A2, B2] at hm
    have hsum_μ : ∀ f : (Fin 1 → Finset (Fin 6)) → ℝ,
        (∑ A : Fin 1 → Finset (Fin 6), μ A * f A) = (1 / 3 : ℝ) * (f A0 + f A1 + f A2) := by
      intro f
      have hsub : (∑ A : Fin 1 → Finset (Fin 6), μ A * f A) = ∑ A ∈ supp, μ A * f A := by
        symm
        apply Finset.sum_subset (Finset.subset_univ supp)
        intro A _ hA
        simp [μ, hA]
      rw [hsub]
      have hmem0 : A0 ∉ ({A1, A2} : Finset _) := by simp [hA01, hA02]
      have hmem1 : A1 ∉ ({A2} : Finset _) := by simp [hA12]
      change (∑ A ∈ insert A0 (insert A1 {A2}), μ A * f A) = _
      rw [Finset.sum_insert hmem0, Finset.sum_insert hmem1, Finset.sum_singleton]
      have hs0 : A0 ∈ supp := by simp [supp]
      have hs1 : A1 ∈ supp := by simp [supp]
      have hs2 : A2 ∈ supp := by simp [supp]
      simp only [μ, hs0, hs1, hs2, ↓reduceIte]
      ring
    have hB0_card : B0.card ≤ 3 := le_trans Finset.card_le_two (by omega)
    have hB1_card : B1.card ≤ 3 := le_trans Finset.card_le_two (by omega)
    have hB2_card : B2.card ≤ 3 := le_trans Finset.card_le_two (by omega)
    have hlaw : ∀ (v_rep : Fin 1 → Fin 6 → (Fin 3 → ZMod 5)),
        (∀ S : Finset (Fin 6), LinearIndependent (ZMod 5) (fun g : S => v_rep 0 g.1) ↔ S.card ≤ 3) →
        IsFeasibleAllocLaw v_rep Finset.univ μ := by
      intro v_rep hv_li
      refine ⟨?_, ?_, ?_⟩
      · intro A; simp only [μ]; split_ifs <;> norm_num
      · intro A hμA
        have hAsupp : A ∈ supp := by by_contra h; exact hμA (by simp [μ, h])
        refine ⟨⟨fun _ => Finset.subset_univ _, fun i j hij => absurd (Subsingleton.elim i j) hij⟩, ?_⟩
        intro i
        rw [Subsingleton.elim i 0, hv_li (A 0)]
        simp only [supp, Finset.mem_insert, Finset.mem_singleton] at hAsupp
        rcases hAsupp with rfl | rfl | rfl
        · exact hB0_card
        · exact hB1_card
        · exact hB2_card
      · have h1 := hsum_μ (fun _ => 1)
        simp only [mul_one] at h1
        rw [h1]; norm_num
    have h_not_beta_u : ¬ ∃ β : ℝ, β < 1 ∧ IsBetaBounded u Finset.univ β μ := by
      rintro ⟨β, hβ_lt, _, hβ_test⟩
      let hv : Fin 3 → ZMod 5 := ![1, 0, 3]
      let U : Fin 1 → Submodule (ZMod 5) (Fin 3 → ZMod 5) :=
        fun _ => Submodule.span (ZMod 5) {hv}
      have hv_B0 : hv ∈ bidderSpan u 0 B0 := by
        have heq : hv = (1 : ZMod 5) • R 0 + (3 : ZMod 5) • R 1 := by
          ext j; fin_cases j <;> rfl
        rw [heq]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp [B0], rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, by simp [B0], rfl⟩))
      have hv_B1 : hv ∈ bidderSpan u 0 B1 := by
        have heq : hv = (2 : ZMod 5) • R 2 + (4 : ZMod 5) • R 3 := by
          ext j; fin_cases j <;> rfl
        rw [heq]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, by simp [B1], rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨3, by simp [B1], rfl⟩))
      have hv_B2 : hv ∈ bidderSpan u 0 B2 := by
        have heq : hv = (4 : ZMod 5) • R 4 + (2 : ZMod 5) • R 5 := by
          ext j; fin_cases j <;> rfl
        rw [heq]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨4, by simp [B2], rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨5, by simp [B2], rfl⟩))
      have hU_le_B0 : U 0 ≤ bidderSpan u 0 B0 :=
        Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv_B0)
      have hU_le_B1 : U 0 ≤ bidderSpan u 0 B1 :=
        Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv_B1)
      have hU_le_B2 : U 0 ≤ bidderSpan u 0 B2 :=
        Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv_B2)
      have htest : IsTestOn u Finset.univ U := by
        intro i
        rw [Subsingleton.elim i 0]
        exact le_trans hU_le_B0
          (Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr (Finset.subset_univ B0))))
      have hv_ne0 : hv ≠ 0 := by
        intro h0
        have h00 : hv 0 = 0 := congrFun h0 0
        change (1 : ZMod 5) = 0 at h00
        exact one_ne_zero h00
      have hdimU : testDim U = 1 := by
        simp only [testDim, Fin.sum_univ_one, U]
        exact finrank_span_singleton hv_ne0
      have hload0 : testLoad u U A0 = 1 := by
        simp only [testLoad, Fin.sum_univ_one, A0]
        rw [inf_of_le_right hU_le_B0]
        exact finrank_span_singleton hv_ne0
      have hload1 : testLoad u U A1 = 1 := by
        simp only [testLoad, Fin.sum_univ_one, A1]
        rw [inf_of_le_right hU_le_B1]
        exact finrank_span_singleton hv_ne0
      have hload2 : testLoad u U A2 = 1 := by
        simp only [testLoad, Fin.sum_univ_one, A2]
        rw [inf_of_le_right hU_le_B2]
        exact finrank_span_singleton hv_ne0
      have hineq := hβ_test U htest
      rw [hsum_μ, hload0, hload1, hload2, hdimU] at hineq
      norm_num at hineq
      linarith
    have h_plane_bound : ∀ (W : Submodule (ZMod 5) (Fin 3 → ZMod 5)),
        Module.finrank (ZMod 5) (Submodule.span (ZMod 5) (R' '' (B0 : Set (Fin 6))) ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) +
        Module.finrank (ZMod 5) (Submodule.span (ZMod 5) (R' '' (B1 : Set (Fin 6))) ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) +
        Module.finrank (ZMod 5) (Submodule.span (ZMod 5) (R' '' (B2 : Set (Fin 6))) ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) ≤
        2 * Module.finrank (ZMod 5) W := by
      have hspan2_le : ∀ a b : Fin 6,
          Module.finrank (ZMod 5) (Submodule.span (ZMod 5) (R' '' (({a, b} : Finset (Fin 6)) : Set (Fin 6)))) ≤ 2 := by
        intro a b
        have himg : R' '' (({a, b} : Finset (Fin 6)) : Set (Fin 6)) =
            (({R' a, R' b} : Finset (Fin 3 → ZMod 5)) : Set (Fin 3 → ZMod 5)) := by
          ext x
          simp only [Set.mem_image, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨g, rfl | rfl, rfl⟩ <;> simp
          · rintro (rfl | rfl)
            · exact ⟨a, Or.inl rfl, rfl⟩
            · exact ⟨b, Or.inr rfl, rfl⟩
        rw [himg]
        exact le_trans (finrank_span_finset_le_card _) Finset.card_le_two
      obtain ⟨hP01_ne, hP02_ne, hP12_ne, h_triple_bot⟩ :
          Submodule.span (ZMod 5) (R' '' (B0 : Set (Fin 6))) ≠ Submodule.span (ZMod 5) (R' '' (B1 : Set (Fin 6))) ∧
          Submodule.span (ZMod 5) (R' '' (B0 : Set (Fin 6))) ≠ Submodule.span (ZMod 5) (R' '' (B2 : Set (Fin 6))) ∧
          Submodule.span (ZMod 5) (R' '' (B1 : Set (Fin 6))) ≠ Submodule.span (ZMod 5) (R' '' (B2 : Set (Fin 6))) ∧
          Submodule.span (ZMod 5) (R' '' (B0 : Set (Fin 6))) ⊓
            Submodule.span (ZMod 5) (R' '' (B1 : Set (Fin 6))) ⊓
            Submodule.span (ZMod 5) (R' '' (B2 : Set (Fin 6))) = ⊥ := by
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
        have hP0_ker : Submodule.span (ZMod 5) (R' '' (B0 : Set (Fin 6))) ≤ K0 := by
          refine Submodule.span_le.mpr ?_
          rintro _ ⟨g, hg, rfl⟩
          simp only [Finset.mem_coe, B0, Finset.mem_insert, Finset.mem_singleton] at hg
          rcases hg with rfl | rfl <;> rfl
        have hP1_ker : Submodule.span (ZMod 5) (R' '' (B1 : Set (Fin 6))) ≤ K1 := by
          refine Submodule.span_le.mpr ?_
          rintro _ ⟨g, hg, rfl⟩
          simp only [Finset.mem_coe, B1, Finset.mem_insert, Finset.mem_singleton] at hg
          rcases hg with rfl | rfl <;> rfl
        have hP2_ker : Submodule.span (ZMod 5) (R' '' (B2 : Set (Fin 6))) ≤ K2 := by
          refine Submodule.span_le.mpr ?_
          rintro _ ⟨g, hg, rfl⟩
          simp only [Finset.mem_coe, B2, Finset.mem_insert, Finset.mem_singleton] at hg
          rcases hg with rfl | rfl <;> rfl
        have h2_ne : (2 : ZMod 5) ≠ 0 := fun h => by
          have hv : (2 : ZMod 5).val = (0 : ZMod 5).val := congrArg ZMod.val h
          change 2 = 0 at hv
          omega
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro heq
          have hm : R' 2 ∈ Submodule.span (ZMod 5) (R' '' (B1 : Set (Fin 6))) :=
            Submodule.subset_span ⟨2, by simp [B1], rfl⟩
          rw [← heq] at hm
          exact h2_ne (hP0_ker hm)
        · intro heq
          have hm : R' 5 ∈ Submodule.span (ZMod 5) (R' '' (B2 : Set (Fin 6))) :=
            Submodule.subset_span ⟨5, by simp [B2], rfl⟩
          rw [← heq] at hm
          exact one_ne_zero (hP0_ker hm)
        · intro heq
          have hm : R' 5 ∈ Submodule.span (ZMod 5) (R' '' (B2 : Set (Fin 6))) :=
            Submodule.subset_span ⟨5, by simp [B2], rfl⟩
          rw [← heq] at hm
          exact h2_ne (hP1_ker hm)
        · rw [eq_bot_iff]
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
      have hP0_rk : Module.finrank (ZMod 5) (Submodule.span (ZMod 5) (R' '' (B0 : Set (Fin 6)))) ≤ 2 := hspan2_le 0 1
      have hP1_rk : Module.finrank (ZMod 5) (Submodule.span (ZMod 5) (R' '' (B1 : Set (Fin 6)))) ≤ 2 := hspan2_le 2 3
      have hP2_rk : Module.finrank (ZMod 5) (Submodule.span (ZMod 5) (R' '' (B2 : Set (Fin 6)))) ≤ 2 := hspan2_le 4 5
      suffices hgen : ∀ (P0 P1 P2 W : Submodule (ZMod 5) (Fin 3 → ZMod 5)),
          Module.finrank (ZMod 5) P0 ≤ 2 →
          Module.finrank (ZMod 5) P1 ≤ 2 →
          Module.finrank (ZMod 5) P2 ≤ 2 →
          P0 ≠ P1 → P0 ≠ P2 → P1 ≠ P2 → P0 ⊓ P1 ⊓ P2 = ⊥ →
          Module.finrank (ZMod 5) (P0 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) +
          Module.finrank (ZMod 5) (P1 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) +
          Module.finrank (ZMod 5) (P2 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) ≤
          2 * Module.finrank (ZMod 5) W by
        intro W
        exact hgen _ _ _ W hP0_rk hP1_rk hP2_rk hP01_ne hP02_ne hP12_ne h_triple_bot
      intro P0 P1 P2 W h0_rk h1_rk h2_rk h01 h02 h12 hbot
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
      · have h_eq_plane : ∀ (P : Submodule (ZMod 5) (Fin 3 → ZMod 5)),
            Module.finrank (ZMod 5) P ≤ 2 →
            Module.finrank (ZMod 5) (P ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) = 2 → W = P := by
          intro P hPrk hPW
          have hWP_eq : (P ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) = W :=
            Submodule.eq_of_le_of_finrank_eq inf_le_right (hPW.trans hW.symm)
          have hW_le_P : W ≤ P := inf_eq_right.mp hWP_eq
          have hPrk_eq : Module.finrank (ZMod 5) W = Module.finrank (ZMod 5) P :=
            le_antisymm (hW ▸ Submodule.finrank_mono hW_le_P) (hW.symm ▸ hPrk)
          exact Submodule.eq_of_le_of_finrank_eq hW_le_P hPrk_eq
        by_contra hgt
        by_cases h0_2 : Module.finrank (ZMod 5) (P0 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) = 2
        · by_cases h1_2 : Module.finrank (ZMod 5) (P1 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) = 2
          · exact h01 ((h_eq_plane P0 h0_rk h0_2).symm.trans (h_eq_plane P1 h1_rk h1_2))
          · have h2_2 : Module.finrank (ZMod 5) (P2 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) = 2 := by omega
            exact h02 ((h_eq_plane P0 h0_rk h0_2).symm.trans (h_eq_plane P2 h2_rk h2_2))
        · have h1_2 : Module.finrank (ZMod 5) (P1 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) = 2 := by omega
          have h2_2 : Module.finrank (ZMod 5) (P2 ⊓ W : Submodule (ZMod 5) (Fin 3 → ZMod 5)) = 2 := by omega
          exact h12 ((h_eq_plane P1 h1_rk h1_2).symm.trans (h_eq_plane P2 h2_rk h2_2))
      · omega
    have h_lin : ∀ a b c d : ℕ, a + b + c ≤ 2 * d →
        (1 / 3 : ℝ) * ((a : ℝ) + (b : ℝ) + (c : ℝ)) ≤ (2 / 3 : ℝ) * (d : ℝ) := by
      intro a b c d h
      have hr : (a : ℝ) + (b : ℝ) + (c : ℝ) ≤ 2 * (d : ℝ) := by exact_mod_cast h
      have h13 : (0 : ℝ) ≤ 1 / 3 := by positivity
      calc (1 / 3 : ℝ) * ((a : ℝ) + (b : ℝ) + (c : ℝ))
          ≤ (1 / 3 : ℝ) * (2 * (d : ℝ)) := mul_le_mul_of_nonneg_left hr h13
        _ = (2 / 3 : ℝ) * (d : ℝ) := by ring
    have h_beta_u' : IsBetaBounded u' Finset.univ (2 / 3 : ℝ) μ := by
      refine ⟨hlaw u' hu'_li, ?_⟩
      intro U _
      rw [hsum_μ]
      have hl0 : testLoad u' U A0 =
          Module.finrank (ZMod 5) (Submodule.span (ZMod 5) (R' '' (B0 : Set (Fin 6))) ⊓ U 0 : Submodule (ZMod 5) (Fin 3 → ZMod 5)) :=
        Fin.sum_univ_one _
      have hl1 : testLoad u' U A1 =
          Module.finrank (ZMod 5) (Submodule.span (ZMod 5) (R' '' (B1 : Set (Fin 6))) ⊓ U 0 : Submodule (ZMod 5) (Fin 3 → ZMod 5)) :=
        Fin.sum_univ_one _
      have hl2 : testLoad u' U A2 =
          Module.finrank (ZMod 5) (Submodule.span (ZMod 5) (R' '' (B2 : Set (Fin 6))) ⊓ U 0 : Submodule (ZMod 5) (Fin 3 → ZMod 5)) :=
        Fin.sum_univ_one _
      have hdU : testDim U = Module.finrank (ZMod 5) (U 0) :=
        Fin.sum_univ_one _
      rw [hl0, hl1, hl2, hdU]
      exact h_lin _ _ _ _ (h_plane_bound (U 0))
    refine ⟨M, u, u', μ, hM, ?_, ?_, h_beta_u', h_not_beta_u⟩
    · intro S; exact (hM S).trans (hu_li S).symm
    · intro S; exact (hM S).trans (hu'_li S).symm
  exact ⟨h_part1, h_part2, h_part3⟩

end

end


section NamedResults

/-- **Lemma E.3 (`lem:unique`, Unique representations over `𝔽₂`)**:
Any two `𝔽₂`-representations of `M | T` admit a linear isomorphism `φ : V ≃ₗ[𝔽₂] V'` between their
spans mapping `u_g ↦ u'_g` (`g ∈ T`) and `span{u_g : g ∈ X}` onto `span{u'_g : g ∈ X}` for every
`X ⊆ T`. -/
theorem lem_E_3_unique_binary {n d d' : ℕ} (M : Matroid (Fin n)) (T : Finset (Fin n))
    (u : Fin n → (Fin d → ZMod 2)) (u' : Fin n → (Fin d' → ZMod 2))
    (hu : ∀ S ⊆ T, M.Indep (S : Set (Fin n)) ↔ LinearIndependent (ZMod 2) (fun g : S => u g.1))
    (hu' : ∀ S ⊆ T, M.Indep (S : Set (Fin n)) ↔ LinearIndependent (ZMod 2) (fun g : S => u' g.1)) :
    let V := Submodule.span (ZMod 2) (u '' (T : Set (Fin n)))
    let V' := Submodule.span (ZMod 2) (u' '' (T : Set (Fin n)))
    ∃ φ : V ≃ₗ[ZMod 2] V',
      (∀ (g : Fin n) (hg : g ∈ T),
        (φ ⟨u g, Submodule.subset_span ⟨g, hg, rfl⟩⟩ : Fin d' → ZMod 2) = u' g) ∧
      (∀ X ⊆ T, ∀ v : V,
        (v : Fin d → ZMod 2) ∈ Submodule.span (ZMod 2) (u '' (X : Set (Fin n))) ↔
        (φ v : Fin d' → ZMod 2) ∈ Submodule.span (ZMod 2) (u' '' (X : Set (Fin n)))) :=
  thm_linear_unique_representations.1 n d d' M T u u' hu hu'

/-- **Lemma E.3 (`lem:unique`, Unique representations over `𝔽₃`, `[BL76]`)**:
Any two `𝔽₃`-representations of `M | T` admit a linear isomorphism `φ : V ≃ₗ[𝔽₃] V'` between their
spans mapping each `u_g` (`g ∈ T`) to a nonzero scalar multiple `c_g • u'_g` and mapping
`span{u_g : g ∈ X}` onto `span{u'_g : g ∈ X}` for every `X ⊆ T`. -/
theorem lem_E_3_unique_ternary {n d d' : ℕ} (M : Matroid (Fin n)) (T : Finset (Fin n))
    (u : Fin n → (Fin d → ZMod 3)) (u' : Fin n → (Fin d' → ZMod 3))
    (hu : ∀ S ⊆ T, M.Indep (S : Set (Fin n)) ↔ LinearIndependent (ZMod 3) (fun g : S => u g.1))
    (hu' : ∀ S ⊆ T, M.Indep (S : Set (Fin n)) ↔ LinearIndependent (ZMod 3) (fun g : S => u' g.1)) :
    let V := Submodule.span (ZMod 3) (u '' (T : Set (Fin n)))
    let V' := Submodule.span (ZMod 3) (u' '' (T : Set (Fin n)))
    ∃ φ : V ≃ₗ[ZMod 3] V',
      (∀ (g : Fin n) (hg : g ∈ T), ∃ c : ZMod 3, c ≠ 0 ∧
        (φ ⟨u g, Submodule.subset_span ⟨g, hg, rfl⟩⟩ : Fin d' → ZMod 3) = c • u' g) ∧
      (∀ X ⊆ T, ∀ v : V,
        (v : Fin d → ZMod 3) ∈ Submodule.span (ZMod 3) (u '' (X : Set (Fin n))) ↔
        (φ v : Fin d' → ZMod 3) ∈ Submodule.span (ZMod 3) (u' '' (X : Set (Fin n)))) :=
  thm_linear_unique_representations.2.1 n d d' M T u u' hu hu'

/-- **Lemma E.3 (`lem:unique`, Combined `𝔽₂` and `𝔽₃` span-preserving uniqueness)**. -/
theorem lem_E_3_unique :
    (∀ (n d d' : ℕ) (M : Matroid (Fin n)) (T : Finset (Fin n))
        (u : Fin n → (Fin d → ZMod 2)) (u' : Fin n → (Fin d' → ZMod 2)),
      (∀ S ⊆ T, M.Indep (S : Set (Fin n)) ↔ LinearIndependent (ZMod 2) (fun g : S => u g.1)) →
      (∀ S ⊆ T, M.Indep (S : Set (Fin n)) ↔ LinearIndependent (ZMod 2) (fun g : S => u' g.1)) →
        let V := Submodule.span (ZMod 2) (u '' (T : Set (Fin n)))
        let V' := Submodule.span (ZMod 2) (u' '' (T : Set (Fin n)))
        ∃ φ : V ≃ₗ[ZMod 2] V',
          ∀ X ⊆ T, ∀ v : V,
            (v : Fin d → ZMod 2) ∈ Submodule.span (ZMod 2) (u '' (X : Set (Fin n))) ↔
            (φ v : Fin d' → ZMod 2) ∈ Submodule.span (ZMod 2) (u' '' (X : Set (Fin n)))) ∧
    (∀ (n d d' : ℕ) (M : Matroid (Fin n)) (T : Finset (Fin n))
        (u : Fin n → (Fin d → ZMod 3)) (u' : Fin n → (Fin d' → ZMod 3)),
      (∀ S ⊆ T, M.Indep (S : Set (Fin n)) ↔ LinearIndependent (ZMod 3) (fun g : S => u g.1)) →
      (∀ S ⊆ T, M.Indep (S : Set (Fin n)) ↔ LinearIndependent (ZMod 3) (fun g : S => u' g.1)) →
        let V := Submodule.span (ZMod 3) (u '' (T : Set (Fin n)))
        let V' := Submodule.span (ZMod 3) (u' '' (T : Set (Fin n)))
        ∃ φ : V ≃ₗ[ZMod 3] V',
          ∀ X ⊆ T, ∀ v : V,
            (v : Fin d → ZMod 3) ∈ Submodule.span (ZMod 3) (u '' (X : Set (Fin n))) ↔
            (φ v : Fin d' → ZMod 3) ∈ Submodule.span (ZMod 3) (u' '' (X : Set (Fin n)))) := by
  refine ⟨fun n d d' M T u u' hu hu' => ?_, fun n d d' M T u u' hu hu' => ?_⟩
  · obtain ⟨φ, _, hspan⟩ := lem_E_3_unique_binary M T u u' hu hu'
    exact ⟨φ, hspan⟩
  · obtain ⟨φ, _, hspan⟩ := lem_E_3_unique_ternary M T u u' hu hu'
    exact ⟨φ, hspan⟩

end NamedResults

end GrossSubstitutesWelfare
