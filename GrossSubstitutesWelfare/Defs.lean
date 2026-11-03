import Mathlib

/-!
# Shared Definitions for *Gross Substitutes Welfare in Random Order*

Unified definitions module covering all concepts and protocols across the paper:
- **Section 2**: Extended-real set valuations (`WithBot ℝ`), Kelso–Crawford gross substitutes via
  prices (`IsGSPrices`), the $M^\natural$-concavity exchange axiom (`IsGSValuation`), supremal
  convolution (`valConvolution`), matroid rank, weighted matroid, and bipartite assignment
  valuations (`matroidRankVal`, `weightedMatroidVal`, `weightedMatroidRankVal`, `assignmentVal`),
  and lexicographic canonical demands (`canonicalDemand`).
- **Section 3 & Appendix B**: Two-time continuous-time generalized survival process
  (`genSurvivalLaw2`, `genMovingProb2`), standard survival law (`survivalLaw`), survival acceptance
  probabilities (`survivalAcceptProb`), inclusion masses (`inclusionMass`), online survival law
  (`onlineSurvivalLaw`), and type-enforced non-clairvoyant online selection algorithms
  (`OnlineSelectionAlg`).
- **Section 4**: Multi-bidder disjoint allocations, optimal welfare (`optWelfare`), disposal
  envelopes (`disposalEnvelope`, `disposalEnvelopeVal`), type-enforced non-clairvoyant online
  welfare algorithms (`OnlineWelfareAlg`), prefix-optimal proposal maps (`IsProposalMap`,
  `gsPrefixOptAlloc`), and non-clairvoyant online admission modules (`OnlineAdmissionModule`,
  `HasConditionalAdmission`).
- **Appendix C & D**: Unit-demand valuations (`IsUnitDemandValuation`), harmonic numbers
  (`harmonicNum`), real-valued selection objectives (`optValReal`, `expectedSelectionValReal`),
  and finite-$n$ secretary cutoff constants (`secretaryCutoffConst`).
- **Appendix E & `[ABHM26]` (`arXiv:2609.19118`)**: Finite-field linear, binary, and ternary
  matroid representations (`IsLinearMatroidRep`, `IsBinaryMatroid`, `IsTernaryMatroid`), single-
  and multi-bidder subspace loads (`matroidSpan`, `subspaceLoad`, `IsSubspaceBetaBounded`,
  `bidderSpan`, `testLoad`, `IsBetaBounded`), represented admission modules
  (`RepresentedAdmissionModule`, `HasRepresentedConditionalAdmission`), and represented-model
  online welfare algorithms (`RepresentedOnlineWelfareAlg`).
-/

namespace GrossSubstitutesWelfare

open Classical MeasureTheory

noncomputable section

instance instFactPrime5 : Fact (Nat.Prime 5) := ⟨by decide⟩

/-! ## Section 2: Gross Substitutes Valuations & Canonical Demands -/

/-- A set valuation `v : 2^N → ℝ ∪ {-∞}` on `n` items (`Fin n`), modeled via `WithBot ℝ`. -/
abbrev ItemValuation (n : ℕ) := Finset (Fin n) → WithBot ℝ

/-- Zero valuation `z(S) = 0` for all `S ⊆ N`. -/
def zeroVal (n : ℕ) : ItemValuation n :=
  fun _ => ((0 : ℝ) : WithBot ℝ)

/-- Effective domain `dom v = {S | v(S) > -∞}`. -/
def valDom {n : ℕ} (v : ItemValuation n) : Set (Finset (Fin n)) :=
  {S | v S ≠ ⊥}

/-- Real part of `v(S)` (defaulting to `0` at `⊥`). -/
noncomputable def realVal {n : ℕ} (v : ItemValuation n) (S : Finset (Fin n)) : ℝ :=
  (v S).unbotD 0

/-- Marginal value `v(g | S) = v(S + g) - v(S)` in `ℝ` (used when `S, S + g ∈ dom v`). -/
noncomputable def marginalVal {n : ℕ} (v : ItemValuation n) (S : Finset (Fin n)) (g : Fin n) : ℝ :=
  realVal v (insert g S) - realVal v S

/-- Offline optimum `OPT(v) = max_{S ⊆ N} v(S)` in `ℝ` (at least `0` when `v(∅) = 0`). -/
noncomputable def optVal {n : ℕ} (v : ItemValuation n) : ℝ :=
  ((Finset.univ : Finset (Finset (Fin n))).sup v).unbotD 0

/-- Offline optimum `OPT(f) = max_{S ⊆ N} f(S)` for a finite-valued function `f : 2^N → ℝ`. -/
noncomputable def optValReal {n : ℕ} (f : Finset (Fin n) → ℝ) : ℝ :=
  ((Finset.univ : Finset (Finset (Fin n))).sup (fun S => ((f S : ℝ) : WithBot ℝ))).unbotD 0

/-- Quasi-linear utility `v(S) - ∑_{g ∈ S} p_g` in `WithBot ℝ` at price vector `p ∈ ℝ^N`. -/
noncomputable def priceUtility {n : ℕ}
    (v : ItemValuation n) (p : Fin n → ℝ) (S : Finset (Fin n)) : WithBot ℝ :=
  v S + ((- ∑ g ∈ S, p g : ℝ) : WithBot ℝ)

/-- Demand correspondence `𝒟(v, p) = argmax_{S ⊆ N} [v(S) - ∑_{g ∈ S} p_g]`, restricted to `dom v`. -/
def priceDemand {n : ℕ} (v : ItemValuation n) (p : Fin n → ℝ) : Set (Finset (Fin n)) :=
  {S | priceUtility v p S ≠ ⊥ ∧ ∀ T : Finset (Fin n), priceUtility v p T ≤ priceUtility v p S}

/-- **Definition 2.1 (`def:gs-prices`)**: Kelso–Crawford gross substitutes via prices. -/
def IsGSPrices {n : ℕ} (v : ItemValuation n) : Prop :=
  v ∅ = ((0 : ℝ) : WithBot ℝ) ∧
  ∀ p p' : Fin n → ℝ, (∀ g, p g ≤ p' g) →
    ∀ S ∈ priceDemand v p, ∃ S' ∈ priceDemand v p',
      S.filter (fun g => p g = p' g) ⊆ S'

/-- **Definition 2.2 (`def:gs`)**: Gross substitutes via the $M^\natural$-concavity exchange axiom,
with `v(∅) = 0` and maximum over the empty swap set equal to `⊥ = -∞`. -/
def IsGSValuation {n : ℕ} (v : ItemValuation n) : Prop :=
  v ∅ = ((0 : ℝ) : WithBot ℝ) ∧
  ∀ X Y : Finset (Fin n), v X ≠ ⊥ → v Y ≠ ⊥ →
    ∀ x ∈ X \ Y,
      v X + v Y ≤
        max (v (X.erase x) + v (insert x Y))
            ((Y \ X).sup (fun y => v (insert y (X.erase x)) + v ((insert x Y).erase y)))

/-- Nonnegative valuation `v(S) ≥ 0` on `2^N`. -/
def IsNonnegValuation {n : ℕ} (v : ItemValuation n) : Prop :=
  ∀ S : Finset (Fin n), ((0 : ℝ) : WithBot ℝ) ≤ v S

/-- Monotone (nondecreasing) valuation on `2^N`. -/
def IsMonotoneValuation {n : ℕ} (v : ItemValuation n) : Prop :=
  ∀ S T : Finset (Fin n), S ⊆ T → v S ≤ v T

/-- Finite-valued valuation (`dom v = 2^N`). -/
def IsFiniteValuation {n : ℕ} (v : ItemValuation n) : Prop :=
  ∀ S : Finset (Fin n), v S ≠ ⊥

/-- Submodular finite-valued set function `f : 2^N → ℝ` with `f(∅) = 0`. -/
def IsSubmodularReal {n : ℕ} (f : Finset (Fin n) → ℝ) : Prop :=
  f ∅ = 0 ∧ ∀ Q R : Finset (Fin n), Q ⊆ R → ∀ g : Fin n, g ∉ R →
    f (insert g R) - f R ≤ f (insert g Q) - f Q

/-- Unit-demand valuation `v(S) = max_{g ∈ S} w_g` with nonnegative item weights `w_g ≥ 0`
(`v(∅) = 0`). -/
def IsUnitDemandValuation {n : ℕ} (v : ItemValuation n) : Prop :=
  ∃ w : Fin n → ℝ, (∀ g, 0 ≤ w g) ∧
    ∀ S : Finset (Fin n),
      v S = (((S.sup (fun g => ((w g : ℝ) : WithBot ℝ))).unbotD 0 : ℝ) : WithBot ℝ)

/-- Adding a modular weight vector `a ∈ ℝ^N` to `v`. -/
noncomputable def addModular {n : ℕ} (v : ItemValuation n) (a : Fin n → ℝ) : ItemValuation n :=
  fun S => v S + ((∑ g ∈ S, a g : ℝ) : WithBot ℝ)

/-- Restriction of `v` to subsets of `N' ⊆ N` (assigning `⊥` outside `2^{N'}`). -/
def restrictVal {n : ℕ} (v : ItemValuation n) (N' : Finset (Fin n)) : ItemValuation n :=
  fun S => if S ⊆ N' then v S else ⊥

/-- Valuation treating item `d` as a dummy item (`v'(S) = v(S - d)`). -/
def dummyItemVal {n : ℕ} (v : ItemValuation n) (d : Fin n) : ItemValuation n :=
  fun S => v (S.erase d)

/-- Contraction `(v / x)(T) = v(T + x) - v({x})` on subsets `T ⊆ N - x` (`⊥` if `x ∈ T`),
keeping labels inherited from `Fin n` (`eq:contraction`). -/
noncomputable def contractVal {n : ℕ} (v : ItemValuation n) (x : Fin n) : ItemValuation n :=
  fun T =>
    if x ∈ T then ⊥
    else match v {x} with
      | ⊥ => ⊥
      | (vx : ℝ) => v (insert x T) + ((-vx : ℝ) : WithBot ℝ)

/-- Scaling a valuation by a scalar `c : ℝ`. -/
noncomputable def scaleVal {n : ℕ} (c : ℝ) (v : ItemValuation n) : ItemValuation n :=
  fun S => match v S with
    | ⊥ => ⊥
    | (r : ℝ) => ((c * r : ℝ) : WithBot ℝ)

/-- Supremal convolution `(u □ w)(S) = max_{T ⊆ S} [u(T) + w(S \ T)]` (`[Murota03]`, Lemma 4.2). -/
noncomputable def valConvolution {n : ℕ} (u w : ItemValuation n) : ItemValuation n :=
  fun S => S.powerset.sup (fun T => u T + w (S \ T))

/-- Weighted matroid valuation `v_M(S) = ∑_{g ∈ S} w_g` for `S ∈ ℐ(M)` and `-∞` (`⊥`) otherwise
(Lemma 2.6 / `lem:matroid`). -/
noncomputable def weightedMatroidVal {n : ℕ}
    (M : Matroid (Fin n)) (w : Fin n → ℝ) : ItemValuation n :=
  fun S => if M.Indep (S : Set (Fin n)) then ((∑ g ∈ S, w g : ℝ) : WithBot ℝ) else ⊥

/-- Weighted matroid rank valuation `v̄_M(S) = max_{T ⊆ S, T ∈ ℐ(M)} ∑_{g ∈ T} w_g`
(Example 2.4 & Appendix E). -/
noncomputable def weightedMatroidRankVal {n : ℕ}
    (M : Matroid (Fin n)) (w : Fin n → ℝ) : ItemValuation n :=
  fun S => (((S.powerset.filter (fun T => M.Indep (T : Set (Fin n)))).sup
    (fun T => ((∑ g ∈ T, w g : ℝ) : WithBot ℝ))).unbotD 0 : ℝ)

/-- Unweighted matroid rank valuation `r_M(S) = max_{T ⊆ S, T ∈ ℐ(M)} |T|` (Example 2.4). -/
noncomputable def matroidRankVal {n : ℕ} (M : Matroid (Fin n)) : ItemValuation n :=
  weightedMatroidRankVal M (fun _ => 1)

/-- Partial slot matching between `S ⊆ Fin n` and slots `Fin k` (Example 2.4). -/
def IsSlotMatchingOn {n k : ℕ} (S : Finset (Fin n)) (f : Fin k → Option (Fin n)) : Prop :=
  (∀ (j : Fin k) (g : Fin n), f j = some g → g ∈ S) ∧
  (∀ (j₁ j₂ : Fin k) (g : Fin n), f j₁ = some g → f j₂ = some g → j₁ = j₂)

/-- Bipartite assignment valuation `v(S) = max-weight matching of S to slots Fin k`
(Example 2.4 / `ex:gs`, `[LLN06, Murota03]`). -/
noncomputable def assignmentVal {n k : ℕ} (w : Fin n → Fin k → ℝ) : ItemValuation n :=
  fun S =>
    ((((Finset.univ : Finset (Fin k → Option (Fin n))).filter (IsSlotMatchingOn S)).sup
      (fun f => ((∑ j : Fin k,
        match f j with | none => (0 : ℝ) | some g => w g j : ℝ) : WithBot ℝ))).unbotD 0 : ℝ)

/-- Modular injective tie-breaking weight `ψ(X) = ∑_{g ∈ X} (1 + 2^{-(g + 1)})` (Section 2.2). -/
noncomputable def psiWeight {n : ℕ} (X : Finset (Fin n)) : ℝ :=
  ∑ g ∈ X, (1 + (1 / 2 : ℝ) ^ (g.1 + 1))

/-- Lexicographic order `(v(X), ψ(X)) ≤_lex (v(Y), ψ(Y))` used to define canonical demands. -/
def demandKeyLe {n : ℕ} (v : ItemValuation n) (X Y : Finset (Fin n)) : Prop :=
  v X < v Y ∨ (v X = v Y ∧ psiWeight X ≤ psiWeight Y)

/-- **Canonical demand `D_v(T)`** (`sec:canonical`): unique maximizer of `(v(X), ψ(X))` over `X ⊆ T`. -/
noncomputable def canonicalDemand {n : ℕ}
    (v : ItemValuation n) (T : Finset (Fin n)) : Finset (Fin n) :=
  if h : ∃ X ∈ T.powerset, ∀ Y ∈ T.powerset, demandKeyLe v Y X then
    Classical.choose h
  else ∅

/-- Choice-rule validity `C(T) ⊆ T`. -/
def IsChoiceRule {n : ℕ} (C : Finset (Fin n) → Finset (Fin n)) : Prop :=
  ∀ T : Finset (Fin n), C T ⊆ T

/-- Persistence (substitutes choice property, `eq:persistence`): `T ⊆ U ⟹ C(U) ∩ T ⊆ C(T)`. -/
def HasPersistence {n : ℕ} (C : Finset (Fin n) → Finset (Fin n)) : Prop :=
  ∀ T U : Finset (Fin n), T ⊆ U → C U ∩ T ⊆ C T

/-- Single displacement (`eq:displacement`): `x ∉ T ⟹ |C(T) \ C(T + x)| ≤ 1`. -/
def HasSingleDisplacement {n : ℕ} (C : Finset (Fin n) → Finset (Fin n)) : Prop :=
  ∀ (T : Finset (Fin n)) (x : Fin n), x ∉ T → (C T \ C (insert x T)).card ≤ 1

/-! ## Section 3 & Appendix B: Survival Laws, Two-Time Thought Experiments & Online Selection -/

/-- Threshold `1 / e = exp(-1)`. -/
noncomputable def invE : ℝ := Real.exp (-1)

/-- Present items `U_u = S_u ∪ B_u` at replay time `u` in the generalized thought experiment. -/
def presentSet {n : ℕ}
    (S B : Finset (Fin n)) (τ β : Fin n → ℝ) (u : ℝ) : Finset (Fin n) :=
  S.filter (fun g => τ g ≤ u) ∪ B.filter (fun g => β g ≤ u)

/-- Death time `σ_g = min({u ∈ [1/e, t] : g ∉ C(U_u)} ∪ {t})` (`sec:survival`, `sec:delay`). -/
noncomputable def deathTime {n : ℕ}
    (C : Finset (Fin n) → Finset (Fin n)) (t : ℝ)
    (S B : Finset (Fin n)) (τ β : Fin n → ℝ) (g : Fin n) : ℝ :=
  sInf ({u : ℝ | invE ≤ u ∧ u ≤ t ∧ g ∉ C (presentSet S B τ β u)} ∪ {t})

/-- Retention probability `θ_g = ln(e σ_g)` for early items (`τ_g ≤ 1/e`), and `0` otherwise. -/
noncomputable def retentionProb {n : ℕ}
    (C : Finset (Fin n) → Finset (Fin n)) (t : ℝ)
    (S B : Finset (Fin n)) (τ β : Fin n → ℝ) (g : Fin n) : ℝ :=
  if τ g ≤ invE then Real.log (Real.exp 1 * deathTime C t S B τ β g) else 0

/-- Conditional probability `ϕ_τ(A)` that retained set `R = A` given fixed timestamps `τ` (`eq:phi`). -/
noncomputable def retainProd {n : ℕ}
    (C : Finset (Fin n) → Finset (Fin n)) (t : ℝ)
    (S B : Finset (Fin n)) (τ β : Fin n → ℝ) (A : Finset (Fin n)) : ℝ :=
  if A ⊆ S then
    (∏ g ∈ A, retentionProb C t S B τ β g) *
      (∏ g ∈ S \ A, (1 - retentionProb C t S B τ β g))
  else 0

/-- Deleted-`f` retention product `ϕ^{-f}_τ` (`sec:delay`). -/
noncomputable def retainProdWithout {n : ℕ}
    (C : Finset (Fin n) → Finset (Fin n)) (t : ℝ)
    (S B : Finset (Fin n)) (τ β : Fin n → ℝ) (A : Finset (Fin n)) (f : Fin n) : ℝ :=
  (∏ g ∈ A, retentionProb C t S B τ β g) *
    (∏ g ∈ S \ insert f A, (1 - retentionProb C t S B τ β g))

/-- Product uniform measure `Unif([0, t₀])^n` on `Fin n → ℝ` (a probability measure for `t₀ > 0`). -/
noncomputable def unifCubeMeasure (n : ℕ) (t₀ : ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => (ENNReal.ofReal t₀)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) t₀))

/-- Two-time generalized thought experiment retention law `P[R = A]` (`sec:delay`):
reshuffled items `S` have timestamps `τ_g ~ Unif([0, t₀])` while replay runs until horizon `t`
(`1/e ≤ t₀ ≤ t ≤ 1`). -/
noncomputable def genSurvivalLaw2 {n : ℕ}
    (C : Finset (Fin n) → Finset (Fin n)) (t₀ t : ℝ)
    (S B : Finset (Fin n)) (β : Fin n → ℝ) (A : Finset (Fin n)) : ℝ :=
  ∫ τ, retainProd C t S B τ β A ∂(unifCubeMeasure n t₀)

/-- Two-time moving-item probability `μ̃(τ̃)` when `x` is pinned at `τ̃` in addition to `B`
with reshuffle time `t₀` and replay horizon `t` (`sec:delay`). -/
noncomputable def genMovingProb2 {n : ℕ}
    (C : Finset (Fin n) → Finset (Fin n)) (t₀ t : ℝ)
    (S B : Finset (Fin n)) (β : Fin n → ℝ) (x : Fin n) (A : Finset (Fin n)) (τ_tilde : ℝ) : ℝ :=
  genSurvivalLaw2 C t₀ t S (insert x B) (Function.update β x τ_tilde) A

/-- Equal-horizon (`t₀ = t`) generalized survival law `P[R = A]`. -/
noncomputable def genSurvivalLaw {n : ℕ}
    (C : Finset (Fin n) → Finset (Fin n)) (t : ℝ)
    (S B : Finset (Fin n)) (β : Fin n → ℝ) (A : Finset (Fin n)) : ℝ :=
  genSurvivalLaw2 C t t S B β A

/-- Equal-horizon (`t₀ = t`) moving-item probability `μ̃(τ̃)`. -/
noncomputable def genMovingProb {n : ℕ}
    (C : Finset (Fin n) → Finset (Fin n)) (t : ℝ)
    (S B : Finset (Fin n)) (β : Fin n → ℝ) (x : Fin n) (A : Finset (Fin n)) (τ_tilde : ℝ) : ℝ :=
  genMovingProb2 C t t S B β x A τ_tilde

/-- Standard survival law `μ^v_{S, t}(A)` (`sec:survival`). -/
noncomputable def survivalLaw {n : ℕ}
    (v : ItemValuation n) (S : Finset (Fin n)) (t : ℝ) (A : Finset (Fin n)) : ℝ :=
  genSurvivalLaw (canonicalDemand v) t S ∅ (fun _ => t) A

/-- Survival inclusion probability `P_{R ~ μ^v_{Q, t}}[A ⊆ R]`. -/
noncomputable def survivalInclProb {n : ℕ}
    (v : ItemValuation n) (Q A : Finset (Fin n)) (t : ℝ) : ℝ :=
  ∑ R ∈ Q.powerset.filter (fun R => A ⊆ R), survivalLaw v Q t R

/-- Scaled inclusion mass `m^v_{Q, A}(t) = t^{|Q|} P_{R ~ μ^v_{Q, t}}[A ⊆ R]` (`eq:inclusion`). -/
noncomputable def inclusionMass {n : ℕ}
    (v : ItemValuation n) (Q A : Finset (Fin n)) (t : ℝ) : ℝ :=
  t ^ Q.card * survivalInclProb v Q A t

/-- Acceptance probability `α_x(A, S, t)` of the survival algorithm (`eq:accept`, with `0/0 := 0`). -/
noncomputable def survivalAcceptProb {n : ℕ}
    (v : ItemValuation n) (x : Fin n) (A S : Finset (Fin n)) (t : ℝ) : ℝ :=
  if t ≤ invE then 0
  else if x ∉ canonicalDemand v (insert x S) then 0
  else if survivalLaw v S t A = 0 then 0
  else (1 / (Real.exp 1 * t)) * (survivalLaw (contractVal v x) S t A / survivalLaw v S t A)

/-- Single arrival transition of the survival algorithm's accepted-set distribution when item `x`
arrives at time `s` after arrived set `S`. -/
noncomputable def survivalStepDist {n : ℕ}
    (v : ItemValuation n) (S : Finset (Fin n)) (x : Fin n) (s : ℝ)
    (dist : Finset (Fin n) → ℝ) : Finset (Fin n) → ℝ :=
  fun B =>
    (if x ∉ B then dist B * (1 - survivalAcceptProb v x B S s) else 0) +
    (if x ∈ B then dist (B.erase x) * survivalAcceptProb v x (B.erase x) S s else 0)

/-- Fold the survival algorithm transitions along an ordered arrival list `items` with timestamps `τ`. -/
noncomputable def survivalRunDistList {n : ℕ}
    (v : ItemValuation n) (τ : Fin n → ℝ) :
    List (Fin n) → Finset (Fin n) → (Finset (Fin n) → ℝ) → (Finset (Fin n) → ℝ)
  | [], _, dist => dist
  | x :: xs, S, dist =>
      survivalRunDistList v τ xs (insert x S) (survivalStepDist v S x (τ x) dist)

/-- Online accepted-set law `L_{Q, t}(A)` when the survival algorithm runs on `Q` with independent
arrival times uniform on `[0, t]` (`sec:matching`). -/
noncomputable def onlineSurvivalLaw {n : ℕ}
    (v : ItemValuation n) (Q : Finset (Fin n)) (t : ℝ) (A : Finset (Fin n)) : ℝ :=
  ∫ τ,
    let ordered := (Q.sort (· ≤ ·)).mergeSort (fun a b => decide (τ a ≤ τ b))
    survivalRunDistList v τ ordered ∅ (fun B => if B = ∅ then 1 else 0) A
  ∂(unifCubeMeasure n t)

/-! ## Non-Clairvoyant Online Selection & Welfare Protocols -/

/-- Set `S_k = {π(0), ..., π(k - 1)}` of the first `k` arrived items under arrival order `π`. -/
def arrivalPrefixSet {n : ℕ} (π : Equiv.Perm (Fin n)) (k : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter (fun idx : Fin n => idx.1 < k)).image π

/-- Deterministic non-clairvoyant online selection policy: at each arrival `x` after `prev`,
queries `v` ONLY on subsets of `insert x prev.toFinset` and irrevocably accepts (`true`) or
rejects (`false`). -/
structure DetSelectionAlg (n : ℕ) where
  step : (prev : List (Fin n)) → (x : Fin n) → (accepted : Finset (Fin n)) →
    ({T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → WithBot ℝ) → Bool

/-- Execute `DetSelectionAlg` for `k` steps (`0 ≤ k ≤ n`) under arrival permutation `π`,
returning `(arrivedList, acceptedSet)`. -/
def runDetSelectionSteps {n : ℕ}
    (alg : DetSelectionAlg n) (v : ItemValuation n) (π : Equiv.Perm (Fin n)) :
    (k : ℕ) → k ≤ n → List (Fin n) × Finset (Fin n)
  | 0, _ => ([], ∅)
  | k + 1, hk =>
      let ⟨prev, acc⟩ := runDetSelectionSteps alg v π k (Nat.le_of_succ_le hk)
      let x := π ⟨k, hk⟩
      let dec := alg.step prev x acc (fun ⟨T, _⟩ => v T)
      (prev ++ [x], if dec then insert x acc else acc)

/-- Final accepted set `A ⊆ N` of `DetSelectionAlg` under arrival permutation `π`. -/
def runDetSelection {n : ℕ}
    (alg : DetSelectionAlg n) (v : ItemValuation n) (π : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  (runDetSelectionSteps alg v π n (le_refl n)).2

/-- Randomized non-clairvoyant online selection algorithm with arbitrary internal randomness
`(Seed, seedMeasure)` independent of `v` and the uniform arrival order `π`. -/
structure OnlineSelectionAlg (n : ℕ) where
  Seed : Type
  [measSeed : MeasurableSpace Seed]
  seedMeasure : Measure Seed
  isProb : IsProbabilityMeasure seedMeasure
  det : Seed → DetSelectionAlg n
  meas_step : ∀ (prev : List (Fin n)) (x : Fin n) (accepted : Finset (Fin n))
    (oracle : {T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → WithBot ℝ) (b : Bool),
    MeasurableSet {ω : Seed | (det ω).step prev x accepted oracle = b}

attribute [instance] OnlineSelectionAlg.measSeed OnlineSelectionAlg.isProb

/-- Probability `P[A_final = S]` under uniform arrival order `π` and internal randomness `ω`. -/
noncomputable def algSelectionProb {n : ℕ}
    (alg : OnlineSelectionAlg n) (v : ItemValuation n) (S : Finset (Fin n)) : ℝ :=
  (1 / (Nat.factorial n : ℝ)) *
    ∑ π : Equiv.Perm (Fin n), alg.seedMeasure.real {ω | runDetSelection (alg.det ω) v π = S}

/-- Marginal inclusion probability `P[g ∈ A_final]`. -/
noncomputable def algInclusionProb {n : ℕ}
    (alg : OnlineSelectionAlg n) (v : ItemValuation n) (g : Fin n) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => g ∈ S),
    algSelectionProb alg v S

/-- Expected value `E[v(A_final)] ∈ ℝ ∪ {-∞}` (`⊥` if any infeasible set has positive probability). -/
noncomputable def expectedSelectionVal {n : ℕ}
    (alg : OnlineSelectionAlg n) (v : ItemValuation n) : WithBot ℝ :=
  if ∃ S : Finset (Fin n), 0 < algSelectionProb alg v S ∧ v S = ⊥ then ⊥
  else ((∑ S : Finset (Fin n), algSelectionProb alg v S * realVal v S : ℝ) : WithBot ℝ)

/-- Expected value `E[f(A_final)]` for a finite-valued function `f : 2^N → ℝ` (Proposition C.3). -/
noncomputable def expectedSelectionValReal {n : ℕ}
    (alg : OnlineSelectionAlg n) (f : Finset (Fin n) → ℝ) : ℝ :=
  ∑ S : Finset (Fin n), algSelectionProb alg (fun T => ((f T : ℝ) : WithBot ℝ)) S * f S

/-! ## Section 4: Welfare, Disposal Envelopes & Conditional Admission -/

/-- Pairwise disjointness of an `m`-bidder bundle profile `X`. -/
def IsPairwiseDisjoint {n m : ℕ} (X : Fin m → Finset (Fin n)) : Prop :=
  ∀ i j : Fin m, i ≠ j → Disjoint (X i) (X j)

/-- `X` is an allocation of `S` (`X_1, ..., X_m ⊆ S` pairwise disjoint). -/
def IsAllocOf {n m : ℕ} (S : Finset (Fin n)) (X : Fin m → Finset (Fin n)) : Prop :=
  (∀ i : Fin m, X i ⊆ S) ∧ IsPairwiseDisjoint X

/-- Total welfare `∑_{i=1}^m v_i(X_i)` in `WithBot ℝ` (`⊥` if any `X_i ∉ dom v_i`). -/
noncomputable def allocWelfare {n m : ℕ}
    (v : Fin m → ItemValuation n) (X : Fin m → Finset (Fin n)) : WithBot ℝ :=
  ∑ i : Fin m, v i (X i)

/-- Optimal welfare `W(S)` on `S ⊆ N` in `ℝ` (`eq:welfare`). -/
noncomputable def optWelfareOn {n m : ℕ}
    (v : Fin m → ItemValuation n) (S : Finset (Fin n)) : ℝ :=
  (((Finset.univ : Finset (Fin m → Finset (Fin n))).filter (fun X => IsAllocOf S X)).sup
    (allocWelfare v)).unbotD 0

/-- Offline optimal welfare `OPT = W(N)` (`eq:welfare`). -/
noncomputable def optWelfare {n m : ℕ} (v : Fin m → ItemValuation n) : ℝ :=
  optWelfareOn v Finset.univ

/-- Disposal envelope `v̄(S) = max_{T ⊆ S} v(T)` in `ℝ` (Lemma 4.2 / `lem:envelope`). -/
noncomputable def disposalEnvelope {n : ℕ} (v : ItemValuation n) (S : Finset (Fin n)) : ℝ :=
  (S.powerset.sup v).unbotD 0

/-- Disposal envelope `v̄` viewed as an `ItemValuation n` (`S ↦ ((v̄(S) : ℝ) : WithBot ℝ)`). -/
noncomputable def disposalEnvelopeVal {n : ℕ} (v : ItemValuation n) : ItemValuation n :=
  fun S => ((disposalEnvelope v S : ℝ) : WithBot ℝ)

/-- Deterministic non-clairvoyant online welfare policy: at each arrival `x` after `prev`,
queries each `v_i` ONLY on subsets of `insert x prev.toFinset` and irrevocably allocates `x`
to `some i` or discards (`none`). -/
structure DetWelfareAlg (n m : ℕ) where
  step : (prev : List (Fin n)) → (x : Fin n) → (bundles : Fin m → Finset (Fin n)) →
    (Fin m → {T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → WithBot ℝ) → Option (Fin m)

/-- Execute `DetWelfareAlg` for `k` steps (`0 ≤ k ≤ n`) under arrival permutation `π`. -/
def runDetWelfareSteps {n m : ℕ}
    (alg : DetWelfareAlg n m) (v : Fin m → ItemValuation n) (π : Equiv.Perm (Fin n)) :
    (k : ℕ) → k ≤ n → List (Fin n) × (Fin m → Finset (Fin n))
  | 0, _ => ([], fun _ => ∅)
  | k + 1, hk =>
      let ⟨prev, bundles⟩ := runDetWelfareSteps alg v π k (Nat.le_of_succ_le hk)
      let x := π ⟨k, hk⟩
      let dec := alg.step prev x bundles (fun i ⟨T, _⟩ => v i T)
      let bundles' := match dec with
        | none => bundles
        | some i => Function.update bundles i (insert x (bundles i))
      (prev ++ [x], bundles')

/-- Final allocation `A = (A_1, ..., A_m)` of `DetWelfareAlg` under arrival permutation `π`. -/
def runDetWelfare {n m : ℕ}
    (alg : DetWelfareAlg n m) (v : Fin m → ItemValuation n) (π : Equiv.Perm (Fin n)) :
    Fin m → Finset (Fin n) :=
  (runDetWelfareSteps alg v π n (le_refl n)).2

/-- Randomized non-clairvoyant online welfare algorithm. -/
structure OnlineWelfareAlg (n m : ℕ) where
  Seed : Type
  [measSeed : MeasurableSpace Seed]
  seedMeasure : Measure Seed
  isProb : IsProbabilityMeasure seedMeasure
  det : Seed → DetWelfareAlg n m
  meas_step : ∀ (prev : List (Fin n)) (x : Fin n) (bundles : Fin m → Finset (Fin n))
    (oracle : Fin m → {T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → WithBot ℝ)
    (dec : Option (Fin m)),
    MeasurableSet {ω : Seed | (det ω).step prev x bundles oracle = dec}

attribute [instance] OnlineWelfareAlg.measSeed OnlineWelfareAlg.isProb

/-- Probability `P[A_final = X]` under uniform arrival order `π` and internal randomness `ω`. -/
noncomputable def algWelfareProb {n m : ℕ}
    (alg : OnlineWelfareAlg n m) (v : Fin m → ItemValuation n)
    (X : Fin m → Finset (Fin n)) : ℝ :=
  (1 / (Nat.factorial n : ℝ)) *
    ∑ π : Equiv.Perm (Fin n), alg.seedMeasure.real {ω | runDetWelfare (alg.det ω) v π = X}

/-- Expected welfare `E[∑_i v_i(A_i)] ∈ ℝ ∪ {-∞}` (`⊥` if any infeasible allocation has positive mass). -/
noncomputable def expectedWelfareVal {n m : ℕ}
    (alg : OnlineWelfareAlg n m) (v : Fin m → ItemValuation n) : WithBot ℝ :=
  if ∃ X : Fin m → Finset (Fin n), 0 < algWelfareProb alg v X ∧ allocWelfare v X = ⊥ then ⊥
  else ((∑ X : Fin m → Finset (Fin n),
    algWelfareProb alg v X * (allocWelfare v X).unbotD 0 : ℝ) : WithBot ℝ)

/-- Finite-`n` secretary cutoff constant `c_n(s) = (s / n) ∑_{j=s}^{n-1} (1 / j)` (`lem:cutoff`). -/
noncomputable def secretaryCutoffConst (n s : ℕ) : ℝ :=
  ((s : ℝ) / (n : ℝ)) * ∑ j ∈ Finset.Ico s n, (1 / (j : ℝ))

/-- `m`-th harmonic number `H_m = ∑_{j=1}^m 1 / j` (Proposition C.4). -/
noncomputable def harmonicNum (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 m, (1 / (j : ℝ))

/-- Subspace-load upper-bound schedule `β_k = 1 - s / k`. -/
noncomputable def loadBeta (s k : ℕ) : ℝ :=
  1 - (s : ℝ) / (k : ℝ)

/-- Prefix admission rate schedule `a_k = s / (k - 1)` (`sec:towards`). -/
noncomputable def admitRate (s k : ℕ) : ℝ :=
  (s : ℝ) / ((k - 1 : ℕ) : ℝ)

/-- Injective integer encoding of an `m`-bidder bundle profile on `Fin n` (for deterministic
tie-breaking of prefix allocations). -/
def allocCode {n m : ℕ} (X : Fin m → Finset (Fin n)) : ℕ :=
  ∑ i : Fin m, (∑ g ∈ X i, 2 ^ g.1) * (2 ^ n) ^ i.1

/-- Total cardinality+lexicographic tie-breaking key `(∑_i |X_i|) * 2^(n * m + 1) + allocCode X`
for canonical general prefix allocations `X^S` (`sec:towards`). Minimizing total bundle size first
automatically drops zero/negative-weight items in weighted matroid and unit-demand valuations. -/
def gsAllocTieKey {n m : ℕ} (X : Fin m → Finset (Fin n)) : ℕ :=
  (∑ i : Fin m, (X i).card) * (2 ^ (n * m + 1)) + allocCode X

/-- Canonical offline optimal allocation `X^S = (X^S_1, ..., X^S_m)` of `S` for general valuations
`v_1, ..., v_m` (`sec:towards`): among feasible allocations of `S` maximizing `∑_i v_i(X_i)`,
selects the unique one minimizing `gsAllocTieKey`. -/
noncomputable def gsPrefixOptAlloc {n m : ℕ}
    (v : Fin m → ItemValuation n) (S : Finset (Fin n)) : Fin m → Finset (Fin n) :=
  let cand := (Finset.univ : Finset (Fin m → Finset (Fin n))).filter
    (fun X => IsAllocOf S X ∧ allocWelfare v X ≠ ⊥)
  let best := cand.sup (allocWelfare v)
  let optCand := cand.filter (fun X => allocWelfare v X = best)
  if h : ∃ X ∈ optCand, ∀ Y ∈ optCand, gsAllocTieKey X ≤ gsAllocTieKey Y then
    Classical.choose h
  else
    fun _ => ∅

/-- **Proposal map** (`eq:internal`, Section 4.3): `P(S) ⊆ S`, `P(S) ∈ dom v`, and `v(P(S)) ≥ v(Y)`
for all `Y ⊆ P(S)`. -/
def IsProposalMap {n : ℕ} (v : ItemValuation n) (P : Finset (Fin n) → Finset (Fin n)) : Prop :=
  ∀ S : Finset (Fin n), P S ⊆ S ∧ v (P S) ≠ ⊥ ∧ ∀ Y ⊆ P S, v Y ≤ v (P S)

/-- Deterministic non-clairvoyant online admission module for `(v, P)` (`sec:towards`):
at each arrival `x` after `prev`, queries `v` and `P` ONLY on subsets of `insert x prev.toFinset`
and irrevocably accepts (`true`) or rejects (`false`). -/
structure DetAdmissionModule (n : ℕ) where
  step : (prev : List (Fin n)) → (x : Fin n) → (accepted : Finset (Fin n)) →
    ({T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → WithBot ℝ) →
    ({T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → Finset (Fin n)) →
    Bool

/-- Execute `DetAdmissionModule` for `k` steps (`0 ≤ k ≤ n`) under arrival permutation `π`. -/
def runDetAdmissionSteps {n : ℕ}
    (mod : DetAdmissionModule n) (v : ItemValuation n)
    (P : Finset (Fin n) → Finset (Fin n)) (π : Equiv.Perm (Fin n)) :
    (k : ℕ) → k ≤ n → List (Fin n) × Finset (Fin n)
  | 0, _ => ([], ∅)
  | k + 1, hk =>
      let ⟨prev, acc⟩ := runDetAdmissionSteps mod v P π k (Nat.le_of_succ_le hk)
      let x := π ⟨k, hk⟩
      let dec := mod.step prev x acc (fun ⟨T, _⟩ => v T) (fun ⟨T, _⟩ => P T)
      (prev ++ [x], if dec then insert x acc else acc)

/-- Final accepted set `A ⊆ N` of `DetAdmissionModule` under arrival permutation `π`. -/
def runDetAdmission {n : ℕ}
    (mod : DetAdmissionModule n) (v : ItemValuation n)
    (P : Finset (Fin n) → Finset (Fin n)) (π : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  (runDetAdmissionSteps mod v P π n (le_refl n)).2

/-- Randomized non-clairvoyant online admission module (`sec:towards`). -/
structure OnlineAdmissionModule (n : ℕ) where
  Seed : Type
  [measSeed : MeasurableSpace Seed]
  seedMeasure : Measure Seed
  isProb : IsProbabilityMeasure seedMeasure
  det : Seed → DetAdmissionModule n
  meas_step : ∀ (prev : List (Fin n)) (x : Fin n) (accepted : Finset (Fin n))
    (valOracle : {T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → WithBot ℝ)
    (propOracle : {T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → Finset (Fin n))
    (b : Bool),
    MeasurableSet {ω : Seed | (det ω).step prev x accepted valOracle propOracle = b}

attribute [instance] OnlineAdmissionModule.measSeed OnlineAdmissionModule.isProb

/-- Probability `P[A_final = S]` for an `OnlineAdmissionModule`. -/
noncomputable def algAdmissionProb {n : ℕ}
    (mod : OnlineAdmissionModule n) (v : ItemValuation n)
    (P : Finset (Fin n) → Finset (Fin n)) (S : Finset (Fin n)) : ℝ :=
  (1 / (Nat.factorial n : ℝ)) *
    ∑ π : Equiv.Perm (Fin n), mod.seedMeasure.real {ω | runDetAdmission (mod.det ω) v P π = S}

/-- Expected value `E[v(A_final)] ∈ ℝ ∪ {-∞}` of an `OnlineAdmissionModule`. -/
noncomputable def expectedAdmissionVal {n : ℕ}
    (mod : OnlineAdmissionModule n) (v : ItemValuation n)
    (P : Finset (Fin n) → Finset (Fin n)) : WithBot ℝ :=
  if ∃ S : Finset (Fin n), 0 < algAdmissionProb mod v P S ∧ v S = ⊥ then ⊥
  else ((∑ S : Finset (Fin n), algAdmissionProb mod v P S * realVal v S : ℝ) : WithBot ℝ)

/-- Rejection discipline of an admission module (`sec:towards`): rejects the `(k + 1)`-th arrival
whenever `k + 1 ≤ s` (`k < s`) or `g_{k+1} ∉ P(S_{k+1})`. -/
def IsAdmissionModuleFor {n : ℕ} (s : ℕ) (v : ItemValuation n)
    (P : Finset (Fin n) → Finset (Fin n)) (mod : OnlineAdmissionModule n) : Prop :=
  ∀ (ω : mod.Seed) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k + 1 ≤ n),
    let st := runDetAdmissionSteps (mod.det ω) v P π k (Nat.le_of_succ_le hk)
    let x := π ⟨k, hk⟩
    (k < s ∨ x ∉ P (insert x st.1.toFinset)) →
      (mod.det ω).step st.1 x st.2 (fun ⟨T, _⟩ => v T) (fun ⟨T, _⟩ => P T) = false

/-- **Definition 4.4 (`def:admission`, Conditional admission)**:
An admission module `mod` for `(v, P)` at cutoff `s` has conditional admission if:
- **(i)** For every `k > s` (`s ≤ k₀` with `k = k₀ + 1`), every `k`-set `S`, and every `g ∈ P(S)`,
  `P[g_k is accepted | S_k = S, g_k = g] ≥ a_k = s / (k - 1)`;
- **(ii)** There exist nonnegative credits `c_g(S) ≥ 0` summing to `v(P(S))` on `P(S)` such that
  `A ∈ dom v` almost surely and `E[v(A)] ≥ E[∑_{k = s + 1}^n c_{g_k}(S_k) 1{g_k is accepted}]`. -/
def HasConditionalAdmission {n : ℕ} (s : ℕ) (v : ItemValuation n)
    (P : Finset (Fin n) → Finset (Fin n)) (mod : OnlineAdmissionModule n) : Prop :=
  IsAdmissionModuleFor s v P mod ∧
  (∀ (k : ℕ) (hk : k + 1 ≤ n), s ≤ k →
    ∀ (S : Finset (Fin n)) (g : Fin n),
      S.card = k + 1 → g ∈ P S →
        let ev := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun π => arrivalPrefixSet π (k + 1) = S ∧ π ⟨k, hk⟩ = g)
        admitRate s (k + 1) * (ev.card : ℝ) ≤
          ∑ π ∈ ev, mod.seedMeasure.real
            {ω | g ∈ (runDetAdmissionSteps (mod.det ω) v P π (k + 1) hk).2}) ∧
  ∃ c : Finset (Fin n) → Fin n → ℝ,
    (∀ S : Finset (Fin n), (∀ g ∈ P S, 0 ≤ c S g) ∧ (∑ g ∈ P S, c S g) = realVal v (P S)) ∧
    (∀ S : Finset (Fin n), 0 < algAdmissionProb mod v P S → v S ≠ ⊥) ∧
    let creditEarned : ℝ :=
      (1 / (Nat.factorial n : ℝ)) *
        ∑ π : Equiv.Perm (Fin n),
          ∑ idx : Fin n,
            if s ≤ idx.1 then
              let S_k := arrivalPrefixSet π (idx.1 + 1)
              let g_k := π idx
              c S_k g_k * mod.seedMeasure.real
                {ω | g_k ∈ (runDetAdmissionSteps (mod.det ω) v P π (idx.1 + 1) idx.2).2}
            else 0
    ((creditEarned : ℝ) : WithBot ℝ) ≤ expectedAdmissionVal mod v P

/-! ## Appendix E & `[ABHM26]` (`arXiv:2609.19118`): Linear, Binary & Ternary Matroid Welfare -/

/-- Linear representation of matroid `M` over field `F` by vectors `u : Fin n → (Fin d → F)`:
`S ∈ ℐ(M) ↔ (u_g)_{g ∈ S}` is linearly independent over `F` (`sec:linear`). -/
def IsLinearMatroidRep {n d : ℕ} (F : Type*) [Field F]
    (M : Matroid (Fin n)) (u : Fin n → (Fin d → F)) : Prop :=
  ∀ S : Finset (Fin n), M.Indep (S : Set (Fin n)) ↔ LinearIndependent F (fun g : S => u g.1)

/-- Binary matroid: representable over `𝔽₂` (`ZMod 2`). -/
def IsBinaryMatroid {n : ℕ} (M : Matroid (Fin n)) : Prop :=
  ∃ (d : ℕ) (u : Fin n → (Fin d → ZMod 2)), IsLinearMatroidRep (ZMod 2) M u

/-- Ternary matroid: representable over `𝔽₃` (`ZMod 3`). -/
def IsTernaryMatroid {n : ℕ} (M : Matroid (Fin n)) : Prop :=
  ∃ (d : ℕ) (u : Fin n → (Fin d → ZMod 3)), IsLinearMatroidRep (ZMod 3) M u

/-- Single-matroid span `W(X) = span_F {u_g : g ∈ X}` (`[ABHM26, Section 4.2]`, `sec:abhm`). -/
def matroidSpan {n d : ℕ} {F : Type*} [Field F]
    (u : Fin n → (Fin d → F)) (X : Finset (Fin n)) : Submodule F (Fin d → F) :=
  Submodule.span F (u '' (X : Set (Fin n)))

/-- Single-matroid subspace load `ℓ_U(A) = dim_F(W(A) ∩ U)` (`[ABHM26, Section 4.2]`, `sec:abhm`). -/
noncomputable def subspaceLoad {n d : ℕ} {F : Type*} [Field F]
    (u : Fin n → (Fin d → F)) (U : Submodule F (Fin d → F)) (A : Finset (Fin n)) : ℕ :=
  Module.finrank F ((matroidSpan u A ⊓ U : Submodule F (Fin d → F)))

/-- Probability law `μ` supported on linearly independent subsets of `S` (`[ABHM26, Section 4]`). -/
def IsIndepSetLaw {n d : ℕ} {F : Type*} [Field F]
    (u : Fin n → (Fin d → F)) (S : Finset (Fin n)) (μ : Finset (Fin n) → ℝ) : Prop :=
  (∀ A, 0 ≤ μ A) ∧
  (∀ A, μ A ≠ 0 → A ⊆ S ∧ LinearIndependent F (fun g : A => u g.1)) ∧
  (∑ A : Finset (Fin n), μ A) = 1

/-- Single-matroid `β`-boundedness across ALL subspaces `U ≤ F^d` (`[ABHM26, Section 4.2]`,
`sec:abhm`): `E_{A ~ μ}[dim(W(A) ∩ U)] ≤ β dim U` for every subspace `U ≤ F^d`. -/
def IsSubspaceBetaBounded {n d : ℕ} {F : Type*} [Field F]
    (u : Fin n → (Fin d → F)) (S : Finset (Fin n)) (β : ℝ) (μ : Finset (Fin n) → ℝ) : Prop :=
  IsIndepSetLaw u S μ ∧
  ∀ U : Submodule F (Fin d → F),
    (∑ A : Finset (Fin n), μ A * (subspaceLoad u U A : ℝ)) ≤ β * (Module.finrank F U : ℝ)

/-- Deterministic non-clairvoyant admission module in the **represented model** (`Proposition E.2`):
observes arrived-subset proposals `P(T)` (`T ⊆ S_k`) and arrived vectors `u_g` (`g ∈ S_k`). -/
structure DetRepresentedAdmissionModule (n : ℕ) (F : Type*) (d : ℕ) where
  step : (prev : List (Fin n)) → (x : Fin n) → (accepted : Finset (Fin n)) →
    ({T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → Finset (Fin n)) →
    ({g : Fin n // g ∈ insert x prev.toFinset} → (Fin d → F)) →
    Bool

/-- Execute `DetRepresentedAdmissionModule` for `k` steps (`0 ≤ k ≤ n`) under arrival order `π`. -/
def runDetRepAdmissionSteps {n d : ℕ} {F : Type*}
    (mod : DetRepresentedAdmissionModule n F d)
    (P : Finset (Fin n) → Finset (Fin n))
    (u : Fin n → (Fin d → F))
    (π : Equiv.Perm (Fin n)) :
    (k : ℕ) → k ≤ n → List (Fin n) × Finset (Fin n)
  | 0, _ => ([], ∅)
  | k + 1, hk =>
      let ⟨prev, acc⟩ := runDetRepAdmissionSteps mod P u π k (Nat.le_of_succ_le hk)
      let x := π ⟨k, hk⟩
      let dec := mod.step prev x acc (fun ⟨T, _⟩ => P T) (fun ⟨g, _⟩ => u g)
      (prev ++ [x], if dec then insert x acc else acc)

/-- Final accepted set of `DetRepresentedAdmissionModule` under arrival order `π`. -/
def runDetRepAdmission {n d : ℕ} {F : Type*}
    (mod : DetRepresentedAdmissionModule n F d)
    (P : Finset (Fin n) → Finset (Fin n))
    (u : Fin n → (Fin d → F))
    (π : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  (runDetRepAdmissionSteps mod P u π n (le_refl n)).2

/-- Randomized non-clairvoyant admission module in the **represented model** (`Proposition E.2`). -/
structure RepresentedAdmissionModule (n : ℕ) (F : Type*) (d : ℕ) where
  Seed : Type
  [measSeed : MeasurableSpace Seed]
  seedMeasure : Measure Seed
  isProb : IsProbabilityMeasure seedMeasure
  det : Seed → DetRepresentedAdmissionModule n F d
  meas_step : ∀ (prev : List (Fin n)) (x : Fin n) (accepted : Finset (Fin n))
    (propOracle : {T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → Finset (Fin n))
    (vecOracle : {g : Fin n // g ∈ insert x prev.toFinset} → (Fin d → F))
    (b : Bool),
    MeasurableSet {ω : Seed | (det ω).step prev x accepted propOracle vecOracle = b}

attribute [instance] RepresentedAdmissionModule.measSeed RepresentedAdmissionModule.isProb

/-- Span `span_i(X) ≤ F_i^{d_i}` of the representing vectors of `X` for bidder `i`. -/
def bidderSpan {n m : ℕ} {F : Fin m → Type*} [∀ i, Field (F i)] {d : Fin m → ℕ}
    (u : (i : Fin m) → Fin n → (Fin (d i) → F i)) (i : Fin m) (X : Finset (Fin n)) :
    Submodule (F i) (Fin (d i) → F i) :=
  Submodule.span (F i) (u i '' (X : Set (Fin n)))

/-- `U = (U_1, ..., U_m)` is a subspace test on `S` (`U_i ≤ span_i(S)` for every bidder `i`). -/
def IsTestOn {n m : ℕ} {F : Fin m → Type*} [∀ i, Field (F i)] {d : Fin m → ℕ}
    (u : (i : Fin m) → Fin n → (Fin (d i) → F i)) (S : Finset (Fin n))
    (U : (i : Fin m) → Submodule (F i) (Fin (d i) → F i)) : Prop :=
  ∀ i : Fin m, U i ≤ bidderSpan u i S

/-- Total dimension `d(U) = ∑_i dim U_i` of a subspace test. -/
noncomputable def testDim {m : ℕ} {F : Fin m → Type*} [∀ i, Field (F i)] {d : Fin m → ℕ}
    (U : (i : Fin m) → Submodule (F i) (Fin (d i) → F i)) : ℕ :=
  ∑ i : Fin m, Module.finrank (F i) (U i)

/-- Load `ℓ_U(A) = ∑_i dim(span_i(A_i) ∩ U_i)` of test `U` at allocation `A`. -/
noncomputable def testLoad {n m : ℕ} {F : Fin m → Type*} [∀ i, Field (F i)] {d : Fin m → ℕ}
    (u : (i : Fin m) → Fin n → (Fin (d i) → F i))
    (U : (i : Fin m) → Submodule (F i) (Fin (d i) → F i))
    (A : Fin m → Finset (Fin n)) : ℕ :=
  ∑ i : Fin m,
    Module.finrank (F i) ((bidderSpan u i (A i) ⊓ U i : Submodule (F i) (Fin (d i) → F i)))

/-- Allocation `A` of `S` is feasible for linear representations `u` if each `A_i` is linearly independent. -/
def IsFeasibleLinearAlloc {n m : ℕ} {F : Fin m → Type*} [∀ i, Field (F i)] {d : Fin m → ℕ}
    (u : (i : Fin m) → Fin n → (Fin (d i) → F i))
    (S : Finset (Fin n)) (A : Fin m → Finset (Fin n)) : Prop :=
  IsAllocOf S A ∧ ∀ i : Fin m, LinearIndependent (F i) (fun g : A i => u i g.1)

/-- `μ` is a probability distribution supported on feasible allocations of `S`. -/
def IsFeasibleAllocLaw {n m : ℕ} {F : Fin m → Type*} [∀ i, Field (F i)] {d : Fin m → ℕ}
    (u : (i : Fin m) → Fin n → (Fin (d i) → F i))
    (S : Finset (Fin n)) (μ : (Fin m → Finset (Fin n)) → ℝ) : Prop :=
  (∀ A, 0 ≤ μ A) ∧
  (∀ A, μ A ≠ 0 → IsFeasibleLinearAlloc u S A) ∧
  (∑ A : Fin m → Finset (Fin n), μ A) = 1

/-- Multi-bidder `β`-boundedness on `S`. -/
def IsBetaBounded {n m : ℕ} {F : Fin m → Type*} [∀ i, Field (F i)] {d : Fin m → ℕ}
    (u : (i : Fin m) → Fin n → (Fin (d i) → F i))
    (S : Finset (Fin n)) (β : ℝ) (μ : (Fin m → Finset (Fin n)) → ℝ) : Prop :=
  IsFeasibleAllocLaw u S μ ∧
  ∀ U : (i : Fin m) → Submodule (F i) (Fin (d i) → F i),
    IsTestOn u S U →
      (∑ A : Fin m → Finset (Fin n), μ A * (testLoad u U A : ℝ)) ≤ β * (testDim U : ℝ)

/-- Updating allocation `A` by assigning item `g` to bidder `j`. -/
def extendAlloc {n m : ℕ}
    (A : Fin m → Finset (Fin n)) (g : Fin n) (j : Fin m) : Fin m → Finset (Fin n) :=
  Function.update A j (insert g (A j))

/-- Feasibility + strict-positivity predicate on subsets of `S` using value queries only. -/
def IsPositiveIndepAllocOf {n m : ℕ}
    (v : Fin m → ItemValuation n) (S : Finset (Fin n)) (X : Fin m → Finset (Fin n)) : Prop :=
  IsAllocOf S X ∧
  ∀ i : Fin m,
    v i (X i) ≠ ⊥ ∧
    (∀ g ∈ X i, ((0 : ℝ) : WithBot ℝ) < v i {g}) ∧
    v i (X i) = ((∑ g ∈ X i, (v i {g}).unbotD 0 : ℝ) : WithBot ℝ)

/-- Canonical prefix-optimal positive independent allocation `X^S` (`Appendix E`). -/
noncomputable def prefixOptAlloc {n m : ℕ}
    (v : Fin m → ItemValuation n) (S : Finset (Fin n)) : Fin m → Finset (Fin n) :=
  let cand := (Finset.univ : Finset (Fin m → Finset (Fin n))).filter
    (fun X => IsPositiveIndepAllocOf v S X)
  let best := cand.sup (allocWelfare v)
  let optCand := cand.filter (fun X => allocWelfare v X = best)
  if h : ∃ X ∈ optCand, ∀ Y ∈ optCand, allocCode X ≤ allocCode Y then
    Classical.choose h
  else
    fun _ => ∅

/-- Deterministic non-clairvoyant online welfare policy in the **represented model** (`Theorem E.1(a)`):
when `x` arrives after `prev`, observes value queries on subsets of `insert x prev.toFinset` AND
representing vectors ONLY for arrived items `g ∈ insert x prev.toFinset`. -/
structure DetRepresentedWelfareAlg (n m : ℕ) (F : Fin m → Type*) (d : Fin m → ℕ) where
  step : (prev : List (Fin n)) → (x : Fin n) → (bundles : Fin m → Finset (Fin n)) →
    (Fin m → {T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → WithBot ℝ) →
    ((i : Fin m) → {g : Fin n // g ∈ insert x prev.toFinset} → (Fin (d i) → F i)) →
    Option (Fin m)

/-- Execute `DetRepresentedWelfareAlg` for `k` steps (`0 ≤ k ≤ n`) under arrival permutation `π`. -/
def runDetRepresentedWelfareSteps {n m : ℕ} {F : Fin m → Type*} {d : Fin m → ℕ}
    (alg : DetRepresentedWelfareAlg n m F d)
    (v : Fin m → ItemValuation n)
    (u : (i : Fin m) → Fin n → (Fin (d i) → F i))
    (π : Equiv.Perm (Fin n)) :
    (k : ℕ) → k ≤ n → List (Fin n) × (Fin m → Finset (Fin n))
  | 0, _ => ([], fun _ => ∅)
  | k + 1, hk =>
      let ⟨prev, bundles⟩ := runDetRepresentedWelfareSteps alg v u π k (Nat.le_of_succ_le hk)
      let x := π ⟨k, hk⟩
      let dec := alg.step prev x bundles (fun i ⟨T, _⟩ => v i T) (fun i ⟨g, _⟩ => u i g)
      let bundles' := match dec with
        | none => bundles
        | some i => Function.update bundles i (insert x (bundles i))
      (prev ++ [x], bundles')

/-- Final allocation of `DetRepresentedWelfareAlg` under arrival permutation `π`. -/
def runDetRepresentedWelfare {n m : ℕ} {F : Fin m → Type*} {d : Fin m → ℕ}
    (alg : DetRepresentedWelfareAlg n m F d)
    (v : Fin m → ItemValuation n)
    (u : (i : Fin m) → Fin n → (Fin (d i) → F i))
    (π : Equiv.Perm (Fin n)) : Fin m → Finset (Fin n) :=
  (runDetRepresentedWelfareSteps alg v u π n (le_refl n)).2

/-- Randomized non-clairvoyant online welfare algorithm in the represented model. -/
structure RepresentedOnlineWelfareAlg (n m : ℕ) (F : Fin m → Type*) (d : Fin m → ℕ) where
  Seed : Type
  [measSeed : MeasurableSpace Seed]
  seedMeasure : Measure Seed
  isProb : IsProbabilityMeasure seedMeasure
  det : Seed → DetRepresentedWelfareAlg n m F d
  meas_step : ∀ (prev : List (Fin n)) (x : Fin n) (bundles : Fin m → Finset (Fin n))
    (oracle : Fin m → {T : Finset (Fin n) // T ⊆ insert x prev.toFinset} → WithBot ℝ)
    (vecOracle : (i : Fin m) → {g : Fin n // g ∈ insert x prev.toFinset} → (Fin (d i) → F i))
    (dec : Option (Fin m)),
    MeasurableSet {ω : Seed | (det ω).step prev x bundles oracle vecOracle = dec}

attribute [instance] RepresentedOnlineWelfareAlg.measSeed RepresentedOnlineWelfareAlg.isProb

/-- Probability `P[A_final = X]` in the represented model. -/
noncomputable def algRepresentedWelfareProb {n m : ℕ} {F : Fin m → Type*} {d : Fin m → ℕ}
    (alg : RepresentedOnlineWelfareAlg n m F d)
    (v : Fin m → ItemValuation n)
    (u : (i : Fin m) → Fin n → (Fin (d i) → F i))
    (X : Fin m → Finset (Fin n)) : ℝ :=
  (1 / (Nat.factorial n : ℝ)) *
    ∑ π : Equiv.Perm (Fin n),
      alg.seedMeasure.real {ω | runDetRepresentedWelfare (alg.det ω) v u π = X}

/-- Expected welfare `E[∑_i v_i(A_i)] ∈ ℝ ∪ {-∞}` in the represented model. -/
noncomputable def expectedRepresentedWelfareVal {n m : ℕ} {F : Fin m → Type*} {d : Fin m → ℕ}
    (alg : RepresentedOnlineWelfareAlg n m F d)
    (v : Fin m → ItemValuation n)
    (u : (i : Fin m) → Fin n → (Fin (d i) → F i)) : WithBot ℝ :=
  if ∃ X : Fin m → Finset (Fin n),
      0 < algRepresentedWelfareProb alg v u X ∧ allocWelfare v X = ⊥ then ⊥
  else ((∑ X : Fin m → Finset (Fin n),
    algRepresentedWelfareProb alg v u X * (allocWelfare v X).unbotD 0 : ℝ) : WithBot ℝ)

end

end GrossSubstitutesWelfare
