module dissertation where

-- Data types (naturals, strings, characters)
open import Data.Nat using (ℕ; zero; suc; _<_; _≥_; _≤_; _≤?_; _<?_; z≤n; s≤s; _⊔_)
  renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-<-trans; <-≤-trans;
  ≤-pred; +-mono-≤; <-trans; n≤1+n; m≤n⇒m≤1+n; n≮n; <⇒≢; ≰⇒>; ≮⇒≥; ≤∧≢⇒<; 1+n≢n)
open import Data.String using (String; fromList; toList) renaming (_≟_ to _≟str_;
  _++_ to _++str_; length to str-length)
open import Data.Char using (Char)
open import Data.Char.Properties using () renaming (_≟_ to _≟char_)

-- Function manipulation.
open import Function using (_∘_; flip; it)

-- Relations and predicates/decidability.
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong-app; cong₂)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable using (Dec; yes; no; True; False; toWitnessFalse;
  toWitness; fromWitness; ¬?; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Data.Empty using (⊥-elim)

-- Products and exists quantifier.
open import Data.Product using (_×_; proj₁; proj₂; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- Lists.
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (≡-dec)
import Data.List.Membership.DecPropositional as DecPropMembership
open import Data.List.Relation.Unary.All using (All; all?; lookup)
  renaming (fromList to All-fromList; toList to All-toList; map to All-map)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Extrema Data.Nat.Properties.≤-totalOrder using (max; xs≤max)

-- Import list membership using List Char comparisons.
_≟lchar_ : ∀ (xs ys : List Char) → Dec (xs ≡ ys)
xs ≟lchar ys = ≡-dec (_≟char_) xs ys

open DecPropMembership _≟lchar_ using (_∈_; _∉_; _∈?_)

module chapter3 where
  open import cofinite
  open import plfa_adaptions
  open import tspl_prior_work

  Id : Set
  Id = List Char

  data Type : Set where
    ‵ℕ      : Type                -- Base type.
    frᵀ     : Id → Type           -- Free type variables.
    #ᵀ      : ℕ → Type            -- Bound type variables.
    _⇒_     : Type → Type → Type  -- Arrow types.
    ∀ᵀ_     : Type → Type         -- "For all" type.

  data Term : Set where
    fr     : Id → Term
    #      : ℕ → Term
    ƛ_     : Term → Term
    _·_    : Term → Term → Term
    Λ_     : Term → Term
    _[_]   : Term → Type → Term
    ‵zero  : Term
    ‵suc_  : Term → Term

  ⇒-inj : ∀ {A B A' B'}→ A ⇒ B ≡ A' ⇒ B' → (A ≡ A') × (B ≡ B')
  ⇒-inj refl = ⟨ refl , refl ⟩
  ∀-inj : ∀ {A B} → ∀ᵀ A ≡ ∀ᵀ B → A ≡ B
  ∀-inj refl = refl
  ƛ-inj : ∀ {L M} → ƛ L ≡ ƛ M → (L ≡ M)
  ƛ-inj refl = refl
  ·-inj : ∀ {L M L' M'} → L · M ≡ L' · M' → (L ≡ L') × (M ≡ M')
  ·-inj refl = ⟨ refl , refl ⟩
  Λ-inj : ∀ {L M} → Λ L ≡ Λ M → L ≡ M
  Λ-inj refl = refl
  []-inj : ∀ {L M A B} → L [ A ] ≡ M [ B ] → (L ≡ M) × (A ≡ B)
  []-inj refl = ⟨ refl , refl ⟩
  ‵suc-inj : ∀ {L M} → ‵suc L ≡ ‵suc M → L ≡ M
  ‵suc-inj refl = refl

  ty-ty[_—→_]_ : ℕ → Id → Type → Type
  ty-ty[ i —→ x ] ‵ℕ = ‵ℕ
  ty-ty[ i —→ x ] (frᵀ y) = frᵀ y
  ty-ty[ i —→ x ] (#ᵀ n) with i ≟ℕ n
  ... | yes _ = frᵀ x
  ... | no  _ = #ᵀ n
  ty-ty[ i —→ x ] (A ⇒ B) = (ty-ty[ i —→ x ] A) ⇒ (ty-ty[ i —→ x ] B)
  ty-ty[ i —→ x ] ∀ᵀ A = ∀ᵀ (ty-ty[ suc i —→ x ] A)

  ty-tm[_—→_]_ : ℕ → Id → Term → Term
  ty-tm[ i —→ x ] (fr y) = fr y
  ty-tm[ i —→ x ] (# n) = # n
  ty-tm[ i —→ x ] (ƛ L) = ƛ (ty-tm[ i —→ x ] L)
  ty-tm[ i —→ x ] (L · M) = (ty-tm[ i —→ x ] L) · (ty-tm[ i —→ x ] M)
  ty-tm[ i —→ x ] (Λ L) = Λ ty-tm[ suc i —→ x ] L
  ty-tm[ i —→ x ] (L [ A ]) = (ty-tm[ i —→ x ] L) [ (ty-ty[ i —→ x ] A) ]
  ty-tm[ i —→ x ] ‵zero = ‵zero
  ty-tm[ i —→ x ] (‵suc L) = ‵suc ty-tm[ i —→ x ] L

  tm-tm[_—→_]_ : ℕ → Id → Term → Term
  tm-tm[ i —→ x ] (fr y) = fr y
  tm-tm[ i —→ x ] (# n) with i ≟ℕ n
  ... | yes _ = fr x
  ... | no  _ = # n
  tm-tm[ i —→ x ] (ƛ L) = ƛ tm-tm[ (suc i) —→ x ] L
  tm-tm[ i —→ x ] (L · M) =
    (tm-tm[ i —→ x ] L) · (tm-tm[ i —→ x ] M)
  tm-tm[ i —→ x ] (Λ L) = Λ (tm-tm[ i —→ x ] L)
  tm-tm[ i —→ x ] (L [ A ]) = (tm-tm[ i —→ x ] L) [ A ]
  tm-tm[ i —→ x ] ‵zero = ‵zero
  tm-tm[ i —→ x ] (‵suc L) = ‵suc tm-tm[ i —→ x ] L

  ax1-ty : ∀ (i : ℕ) (a b : Id) (A : Type)
    → ty-ty[ i —→ a ] (ty-ty[ i —→ b ] A) ≡ ty-ty[ i —→ b ] A
  ax1-ty i a b ‵ℕ = refl
  ax1-ty i a b (frᵀ x) = refl
  ax1-ty i a b (#ᵀ k) with i ≟ℕ k
  ... | yes _   = refl
  ... | no  i≢k with i ≟ℕ k
  ...   | yes refl = contradiction refl i≢k
  ...   | no  _    = refl
  ax1-ty i a b (A ⇒ B)
    rewrite ax1-ty i a b A | ax1-ty i a b B = refl
  ax1-ty i a b (∀ᵀ A) rewrite ax1-ty (suc i) a b A = refl

  ax1-tm : ∀ (i : ℕ) (a b : Id) (L : Term)
    → tm-tm[ i —→ a ] (tm-tm[ i —→ b ] L) ≡ tm-tm[ i —→ b ] L
  ax1-tm i a b (fr x) = refl
  ax1-tm i a b (# k) with i ≟ℕ k
  ... | yes refl = refl
  ... | no  i≢k  with i ≟ℕ k
  ... |   yes refl = contradiction refl i≢k
  ... |   no  _    = refl
  ax1-tm i a b (ƛ L) rewrite ax1-tm (suc i) a b L = refl
  ax1-tm i a b (L · M)
    rewrite ax1-tm i a b L | ax1-tm i a b M = refl
  ax1-tm i a b (Λ L) rewrite ax1-tm i a b L = refl
  ax1-tm i a b (L [ A ]) rewrite ax1-tm i a b L = refl
  ax1-tm i a b ‵zero = refl
  ax1-tm i a b (‵suc L) rewrite ax1-tm i a b L = refl

  ax1-ty-tm : ∀ (i : ℕ) (a b : Id) (L : Term)
    → ty-tm[ i —→ a ] (ty-tm[ i —→ b ] L) ≡ ty-tm[ i —→ b ] L
  ax1-ty-tm i a b (fr x) = refl
  ax1-ty-tm i a b (# k) = refl
  ax1-ty-tm i a b (ƛ L) rewrite
    ax1-ty-tm i a b L = refl
  ax1-ty-tm i a b (L · M) rewrite
    ax1-ty-tm i a b L | ax1-ty-tm i a b M = refl
  ax1-ty-tm i a b (Λ L)
    rewrite ax1-ty-tm (suc i) a b L = refl
  ax1-ty-tm i a b (L [ A ])
    rewrite ax1-ty i a b A | ax1-ty-tm i a b L = refl
  ax1-ty-tm i a b ‵zero = refl
  ax1-ty-tm i a b (‵suc L)
    rewrite ax1-ty-tm i a b L = refl

  _≻ty_ : ℕ → Type → Set
  i ≻ty A = (j : ℕ) ⦃ _ : j ≥ i ⦄ → И T , (ty-ty[ j —→ T ] A ≡ A)

  _≻tm_ : ℕ → Term → Set
  i ≻tm L = (j : ℕ) ⦃ _ : j ≥ i ⦄ → И a , (tm-tm[ j —→ a ] L ≡ L)

  _≻ty-tm_ : ℕ → Term → Set
  i ≻ty-tm L = (j : ℕ) ⦃ _ : j ≥ i ⦄ → И T , (ty-tm[ j —→ T ] L ≡ L)

  Ty-LocallyClosed : Type → Set
  Ty-LocallyClosed A = 0 ≻ty A

  Tm-LocallyClosed : Term → Set
  Tm-LocallyClosed L = 0 ≻tm L

  Ty-Tm-LocallyClosed : Term → Set
  Ty-Tm-LocallyClosed L = 0 ≻ty-tm L


  lemma2·6-ty : ∀ {i j L}
    → j ≥ i
    → i ≻ty L
    → j ≻ty L
  lemma2·6-ty j≥i i≻A k =
    i≻A k ⦃ ≤-trans j≥i it ⦄

  lemma2·6-tm : ∀ {i j L}
    → j ≥ i → i ≻tm L → j ≻tm L
  lemma2·6-tm j≥i i≻L k =
    i≻L k ⦃ ≤-trans j≥i it ⦄

  lemma2·6-ty-tm : ∀ {i j L}
    → j ≥ i → i ≻ty-tm L → j ≻ty-tm L
  lemma2·6-ty-tm j≥i i≻L k =
    i≻L k ⦃ ≤-trans j≥i it ⦄

  lemma2·7-1-ty : ∀ {i x y L}
    → ty-ty[ i —→ x ] L ≡ L
    → ty-ty[ i —→ y ] L ≡ L
  lemma2·7-1-ty {i} {x} {y} {A} assump =
    begin
      ty-ty[ i —→ y ] A
    ≡⟨ sym (cong (ty-ty[ i —→ y ]_) assump) ⟩
      ty-ty[ i —→ y ] (ty-ty[ i —→ x ] A)
    ≡⟨ ax1-ty i y x A ⟩
      ty-ty[ i —→ x ] A
    ≡⟨ assump ⟩
      A
    ∎
  lemma2·7-1-tm : ∀ {i x y L}
    → tm-tm[ i —→ x ] L ≡ L → tm-tm[ i —→ y ] L ≡ L
  lemma2·7-1-tm {i} {x} {y} {L} assump =
    begin
      tm-tm[ i —→ y ] L
    ≡⟨ sym (cong (tm-tm[ i —→ y ]_) assump) ⟩
      tm-tm[ i —→ y ] (tm-tm[ i —→ x ] L)
    ≡⟨ ax1-tm i y x L ⟩
      tm-tm[ i —→ x ] L
    ≡⟨ assump ⟩
      L
    ∎

  lemma2·7-1-ty-tm : ∀ {i x y L}
    → ty-tm[ i —→ x ] L ≡ L → ty-tm[ i —→ y ] L ≡ L
  lemma2·7-1-ty-tm {i} {x} {y} {L} assump =
    begin
      ty-tm[ i —→ y ] L
    ≡⟨ sym (cong (ty-tm[ i —→ y ]_) assump) ⟩
      ty-tm[ i —→ y ] (ty-tm[ i —→ x ] L)
    ≡⟨ ax1-ty-tm i y x L ⟩
      ty-tm[ i —→ x ] L
    ≡⟨ assump ⟩
      L
    ∎

  lemma2·7-2-ty : ∀ {i j x A}
    → j ≥ i
    → i ≻ty A
    → ty-ty[ j —→ x ] A ≡ A
  lemma2·7-2-ty {j = j} j≥i i≻A =
    let И⟨ Иe₁ , Иe₂ ⟩ = i≻A j ⦃ j≥i ⦄ in
      lemma2·7-1-ty (Иe₂ (fresh Иe₁) {fresh-correct Иe₁})

  lemma2·7-2-tm : ∀ {i j x L} → j ≥ i
    → i ≻tm L → tm-tm[ j —→ x ] L ≡ L
  lemma2·7-2-tm {j = j} j≥i i≻L =
    let И⟨ Иe₁ , Иe₂ ⟩ = i≻L j ⦃ j≥i ⦄ in
      lemma2·7-1-tm (Иe₂ (fresh Иe₁) {fresh-correct Иe₁})

  lemma2·7-2-ty-tm : ∀ {i j x L} → j ≥ i
    → i ≻ty-tm L → ty-tm[ j —→ x ] L ≡ L
  lemma2·7-2-ty-tm {j = j} j≥i i≻L =
    let И⟨ Иe₁ , Иe₂ ⟩ = i≻L j ⦃ j≥i ⦄ in
      lemma2·7-1-ty-tm (Иe₂ (fresh Иe₁) {fresh-correct Иe₁})

  i≻∀A⇒si≻A : ∀ {A i} → i ≻ty (∀ᵀ A) → (suc i) ≻ty A
  i≻∀A⇒si≻A {A} i≻∀ (suc j) =
    let И⟨ Иe₁ , Иe₂ ⟩ = i≻∀ j ⦃ ≤-pred it ⦄
    in И⟨ Иe₁ , (λ a {a∉} → ∀-inj (Иe₂ a {a∉})) ⟩

  ≻ƛ⇒s≻ƛ : ∀ {L i} → i ≻tm (ƛ L) → (suc i) ≻tm L
  ≻ƛ⇒s≻ƛ ≻ƛ (suc j) = let И⟨ Иe₁ , Иe₂ ⟩ = ≻ƛ j ⦃ ≤-pred it ⦄
    in И⟨ Иe₁ , (λ a {a∉} → ƛ-inj (Иe₂ a {a∉})) ⟩

  ≻Λ⇒s≻Λ : ∀ {L i} → i ≻ty-tm (Λ L) → (suc i) ≻ty-tm L
  ≻Λ⇒s≻Λ i≻Λ (suc j) = let И⟨ Иe₁ , Иe₂ ⟩ = i≻Λ j ⦃ ≤-pred it ⦄
    in И⟨ Иe₁ , (λ a {a∉} → Λ-inj (Иe₂ a {a∉})) ⟩

  Λ-≻ : ∀ {L i} → i ≻tm (Λ L) → i ≻tm L
  Λ-≻ i≻ j = let И⟨ Иe₁ , Иe₂ ⟩ = i≻ j
    in И⟨ Иe₁ , (λ a {a∉} → Λ-inj (Иe₂ a {a∉})) ⟩

  ‵suc-≻ : ∀ {L i} → i ≻tm (‵suc L) → i ≻tm L
  ‵suc-≻ i≻ j = let И⟨ Иe₁ , Иe₂ ⟩ = i≻ j
    in И⟨ Иe₁ , (λ a {a∉} → ‵suc-inj (Иe₂ a {a∉})) ⟩

  []-≻ : ∀ {L A i} → i ≻tm (L [ A ]) → i ≻tm L
  []-≻ {L} {A} {i} i≻ j = let И⟨ Иe₁ , Иe₂ ⟩ = i≻ j
    in И⟨ Иe₁ , (λ a {a∉} → proj₁ ([]-inj (Иe₂ a {a∉}))) ⟩

  n≻‵ℕ : ∀ {n : ℕ} → n ≻ty ‵ℕ
  n≻‵ℕ j = И⟨ [] , (λ _ → refl) ⟩

  ty-fr-lc : ∀ {A} → Ty-LocallyClosed (frᵀ A)
  ty-fr-lc j = И⟨ [] , (λ _ → refl) ⟩

  ⇒-≻ : ∀ {A B i} → i ≻ty (A ⇒ B) → (i ≻ty A) × (i ≻ty B)
  ⇒-≻ {A} {B} {i} i≻A⇒B = ⟨ i≻A , i≻B ⟩
    where
      i≻A : i ≻ty A
      i≻A j = let И⟨ Иe₁ , Иe₂ ⟩ = i≻A⇒B j
        in И⟨ Иe₁ , (λ a {a∉} → proj₁ (⇒-inj (Иe₂ a {a∉}))) ⟩
      i≻B : i ≻ty B
      i≻B j = let И⟨ Иe₁ , Иe₂ ⟩ = i≻A⇒B j
        in И⟨ Иe₁ , (λ a {a∉} → proj₂ (⇒-inj (Иe₂ a {a∉}))) ⟩

  ≻-⇒ : ∀ {A B i} → i ≻ty A → i ≻ty B → i ≻ty (A ⇒ B)
  ≻-⇒ i≻A i≻B j =
    let И⟨ A-Иe₁ , A-Иe₂ ⟩ = i≻A j
        И⟨ B-Иe₁ , B-Иe₂ ⟩ = i≻B j
    in И⟨ A-Иe₁ ++ B-Иe₁ , (λ a {a∉} →
      let ⟨ a∉A , a∉B ⟩ = ∉-++ a∉
      in cong₂ _⇒_ (A-Иe₂ a {a∉A}) (B-Иe₂ a {a∉B})) ⟩

  ·-≻ : ∀ {L M i} → i ≻tm (L · M) → (i ≻tm L) × (i ≻tm M)
  ·-≻ {L} {M} {i} i≻ = ⟨ i≻L , i≻M ⟩
    where
      i≻L : i ≻tm L
      i≻L j = let И⟨ Иe₁ , Иe₂ ⟩ = i≻ j
        in И⟨ Иe₁ , (λ a {a∉} → proj₁ (·-inj (Иe₂ a {a∉}))) ⟩
      i≻M : i ≻tm M
      i≻M j = let И⟨ Иe₁ , Иe₂ ⟩ = i≻ j
        in И⟨ Иe₁ , (λ a {a∉} → proj₂ (·-inj (Иe₂ a {a∉}))) ⟩

  open-rec-lc-lemma : ∀ {L : Term} {i j u v} → i ≢ j
    → tm-tm[ i —→ u ] (tm-tm[ j —→ v ] L) ≡ tm-tm[ j —→ v ] L
    → tm-tm[ i —→ u ] L ≡ L
  open-rec-lc-lemma {fr x} i≢j assump = refl
  open-rec-lc-lemma {# k} {i} {j} i≢j assump
    with i ≟ℕ j | i ≟ℕ k
  ... | yes refl | _ = contradiction refl i≢j
  ... | no _     | no _ = refl
  ... | no _     | yes refl with j ≟ℕ k
  ...   | yes refl = contradiction refl i≢j
  ...   | no j≢k with k ≟ℕ k
  ...     | yes refl with () ← assump
  ...     | no  k≢k  = contradiction refl k≢k
  open-rec-lc-lemma {ƛ L} {i} {j} i≢j assump
    rewrite open-rec-lc-lemma {L} {suc i} {suc j}
      (suc-preserves-≢ i≢j)
      (ƛ-inj assump) = refl
  open-rec-lc-lemma {L · M} i≢j assump rewrite
      open-rec-lc-lemma {L} i≢j (proj₁ (·-inj assump))
    | open-rec-lc-lemma {M} i≢j (proj₂ (·-inj assump)) = refl
  open-rec-lc-lemma {Λ L} i≢j assump
    rewrite open-rec-lc-lemma {L} i≢j (Λ-inj assump) = refl
  open-rec-lc-lemma {L [ x ]} i≢j assump
    rewrite open-rec-lc-lemma {L} i≢j (proj₁ ([]-inj assump)) = refl
  open-rec-lc-lemma {‵zero} i≢j assump = refl
  open-rec-lc-lemma {‵suc L} i≢j assump
    rewrite open-rec-lc-lemma {L} i≢j (‵suc-inj assump) = refl

  open-rec-lc-lemma-ty : ∀ {A : Type} {i j u v} → i ≢ j
    → ty-ty[ i —→ u ] (ty-ty[ j —→ v ] A) ≡ ty-ty[ j —→ v ] A
    → ty-ty[ i —→ u ] A ≡ A
  open-rec-lc-lemma-ty {‵ℕ} i≢j assump = refl
  open-rec-lc-lemma-ty {frᵀ x} i≢j assump = refl
  open-rec-lc-lemma-ty {#ᵀ k} {i} {j} i≢j assump with i ≟ℕ k
  ... | no  i≢k  = refl
  ... | yes refl with j ≟ℕ k
  ...   | yes refl = contradiction refl i≢j
  ...   | no  j≢k with k ≟ℕ k
  ...     | yes refl with () ← assump
  ...     | no  k≢k = contradiction refl k≢k
  open-rec-lc-lemma-ty {A ⇒ B} i≢j assump rewrite
      open-rec-lc-lemma-ty {A} i≢j (proj₁ (⇒-inj assump))
    | open-rec-lc-lemma-ty {B} i≢j (proj₂ (⇒-inj assump))
    = refl
  open-rec-lc-lemma-ty {∀ᵀ A} {i} {j} i≢j assump
    rewrite open-rec-lc-lemma-ty {A} {suc i} {suc j}
      (suc-preserves-≢ i≢j)
      (∀-inj assump)
        = refl

  open-rec-lc-lemma-ty-tm : ∀ {L : Term} {i j u v} → i ≢ j
    → ty-tm[ i —→ u ] (ty-tm[ j —→ v ] L) ≡ ty-tm[ j —→ v ] L
    → ty-tm[ i —→ u ] L ≡ L
  open-rec-lc-lemma-ty-tm {fr x} i≢j assump = refl
  open-rec-lc-lemma-ty-tm {# k} i≢j assump = refl
  open-rec-lc-lemma-ty-tm {ƛ L} i≢j assump rewrite
    open-rec-lc-lemma-ty-tm {L} i≢j (ƛ-inj assump) = refl
  open-rec-lc-lemma-ty-tm {L · M} i≢j assump rewrite
      open-rec-lc-lemma-ty-tm {L} i≢j (proj₁ (·-inj assump))
    | open-rec-lc-lemma-ty-tm {M} i≢j (proj₂ (·-inj assump)) = refl
  open-rec-lc-lemma-ty-tm {Λ L} i≢j assump rewrite
    open-rec-lc-lemma-ty-tm {L} (suc-preserves-≢ i≢j) (Λ-inj assump) = refl
  open-rec-lc-lemma-ty-tm {L [ A ]} i≢j assump rewrite
      open-rec-lc-lemma-ty-tm {L} i≢j (proj₁ ([]-inj assump))
    | open-rec-lc-lemma-ty {A} i≢j (proj₂ ([]-inj assump)) = refl
  open-rec-lc-lemma-ty-tm {‵zero} i≢j assump = refl
  open-rec-lc-lemma-ty-tm {‵suc L} i≢j assump rewrite
    open-rec-lc-lemma-ty-tm {L} i≢j (‵suc-inj assump) = refl

  open-rec-lc-lemma-ty-tm-tm-tm : ∀ {L : Term} {i j u v}
    → ty-tm[ i —→ u ] (tm-tm[ j —→ v ] L) ≡ tm-tm[ j —→ v ] L
    → ty-tm[ i —→ u ] L ≡ L
  open-rec-lc-lemma-ty-tm-tm-tm {fr x} assump = refl
  open-rec-lc-lemma-ty-tm-tm-tm {# k} assump = refl
  open-rec-lc-lemma-ty-tm-tm-tm {ƛ L} assump rewrite
    open-rec-lc-lemma-ty-tm-tm-tm {L} (ƛ-inj assump) = refl
  open-rec-lc-lemma-ty-tm-tm-tm {L · M} assump rewrite
      open-rec-lc-lemma-ty-tm-tm-tm {L} (proj₁ (·-inj assump))
    | open-rec-lc-lemma-ty-tm-tm-tm {M} (proj₂ (·-inj assump))
    = refl
  open-rec-lc-lemma-ty-tm-tm-tm {Λ L} assump rewrite
    open-rec-lc-lemma-ty-tm-tm-tm {L} (Λ-inj assump) = refl
  open-rec-lc-lemma-ty-tm-tm-tm {L [ A ]} assump rewrite
      proj₂ ([]-inj assump)
    | open-rec-lc-lemma-ty-tm-tm-tm {L} (proj₁ ([]-inj assump))
    = refl
  open-rec-lc-lemma-ty-tm-tm-tm {‵zero} assump = refl
  open-rec-lc-lemma-ty-tm-tm-tm {‵suc L} assump rewrite
    open-rec-lc-lemma-ty-tm-tm-tm {L} (‵suc-inj assump) = refl

  fv-tm : Term → List Id
  fv-tm (fr x) = x ∷ []
  fv-tm (# i) = []
  fv-tm (ƛ L) = fv-tm L
  fv-tm (L · M) = fv-tm L ++ fv-tm M
  fv-tm (Λ L) = fv-tm L
  fv-tm (L [ A ]) = fv-tm L
  fv-tm ‵zero = []
  fv-tm (‵suc L) = fv-tm L

  ftv-ty : Type → List Id
  ftv-ty ‵ℕ = []
  ftv-ty (frᵀ x) = x ∷ []
  ftv-ty (#ᵀ i) = []
  ftv-ty (A ⇒ B) = ftv-ty A ++ ftv-ty B
  ftv-ty (∀ᵀ A) = ftv-ty A

  ftv-tm : Term → List Id
  ftv-tm (fr x) = []
  ftv-tm (# i) = []
  ftv-tm (ƛ L) = ftv-tm L
  ftv-tm (L · M) = ftv-tm L ++ ftv-tm M
  ftv-tm (Λ L) = ftv-tm L
  ftv-tm (L [ A ]) = ftv-tm L ++ ftv-ty A
  ftv-tm ‵zero = []
  ftv-tm (‵suc L) = ftv-tm L

  tm-tm[_:=_]_ : Id → Term → Term → Term
  tm-tm[ x := N ] (fr y) with x ≟lchar y
  ... | yes refl = N
  ... | no  _    = fr y
  tm-tm[ x := N ] (# k) = # k
  tm-tm[ x := N ] (ƛ L) = ƛ tm-tm[ x := N ] L
  tm-tm[ x := N ] (L · M) = (tm-tm[ x := N ] L) · (tm-tm[ x := N ] M)
  tm-tm[ x := T ] (Λ L) = Λ (tm-tm[ x := T ] L)
  tm-tm[ x := T ] (L [ A ]) = (tm-tm[ x := T ] L) [ A ]
  tm-tm[ x := N ] ‵zero = ‵zero
  tm-tm[ x := N ] (‵suc L) = ‵suc tm-tm[ x := N ] L

  ty-ty[_:=_]_ : Id → Type → Type → Type
  ty-ty[ X := T ] ‵ℕ = ‵ℕ
  ty-ty[ X := T ] (frᵀ Y) with X ≟lchar Y
  ... | yes refl = T
  ... | no  _    = frᵀ Y
  ty-ty[ X := T ] (#ᵀ k) = #ᵀ k
  ty-ty[ X := T ] (A ⇒ B) = (ty-ty[ X := T ] A) ⇒ (ty-ty[ X := T ] B)
  ty-ty[ X := T ] (∀ᵀ A) = ∀ᵀ (ty-ty[ X := T ] A)

  ty-tm[_:=_]_ : Id → Type → Term → Term
  ty-tm[ X := T ] (fr x) = fr x
  ty-tm[ X := T ] (# k) = # k
  ty-tm[ X := T ] (ƛ L) = ƛ (ty-tm[ X := T ] L)
  ty-tm[ X := T ] (L · M) = (ty-tm[ X := T ] L) · (ty-tm[ X := T ] M)
  ty-tm[ X := T ] (Λ L) = Λ (ty-tm[ X := T ] L)
  ty-tm[ X := T ] (L [ A ]) = (ty-tm[ X := T ] L) [ ty-ty[ X := T ] A ]
  ty-tm[ X := T ] ‵zero = ‵zero
  ty-tm[ X := T ] (‵suc L) = ‵suc ty-tm[ X := T ] L

  :=-≻ : ∀ {A X C i j} → j ≥ i → i ≻ty A → i ≻ty C
    → j ≻ty (ty-ty[ X := C ] A)
  :=-≻ {‵ℕ} j≥i i≻A i≻C = n≻‵ℕ
  :=-≻ {frᵀ Y} {X} j≥i i≻A i≻C with X ≟lchar Y
  ... | yes refl = lemma2·6-ty j≥i i≻C
  ... | no  X≢Y  = lemma2·6-ty j≥i i≻A
  :=-≻ {#ᵀ k} j≥i i≻A i≻C = lemma2·6-ty j≥i i≻A
  :=-≻ {A ⇒ B} j≥i i≻ i≻C k =
    let ⟨ i≻A , i≻B ⟩ = ⇒-≻ i≻
        И⟨ A-Иe₁ , A-Иe₂ ⟩ = (:=-≻ j≥i i≻A i≻C) k
        И⟨ B-Иe₁ , B-Иe₂ ⟩ = (:=-≻ j≥i i≻B i≻C) k
    in И⟨ A-Иe₁ ++ B-Иe₁ , (λ a {a∉} →
      let ⟨ a∉A , a∉B ⟩ = ∉-++ a∉
      in cong₂ _⇒_ (A-Иe₂ a {a∉A}) (B-Иe₂ a {a∉B})) ⟩
  :=-≻ {∀ᵀ A} {C = C} {i = i} j≥i i≻∀A i≻C k =
    let И⟨ Иe₁ , Иe₂ ⟩ = (:=-≻ (s≤s j≥i) si≻A si≻C) (suc k) ⦃ s≤s it ⦄
    in И⟨ Иe₁ , (λ a {a∉} → cong ∀ᵀ_ (Иe₂ a {a∉})) ⟩
    where
      si≻A : suc i ≻ty A
      si≻A = i≻∀A⇒si≻A i≻∀A
      si≻C : suc i ≻ty C
      si≻C = lemma2·6-ty (n≤1+n i) i≻C

  :=-∉-invariant : ∀ {A X B} → X ∉ ftv-ty A
    → (ty-ty[ X := B ] A) ≡ A
  :=-∉-invariant {‵ℕ} X∉A = refl
  :=-∉-invariant {frᵀ Y} {X} X∉A with X ≟lchar Y
  ... | yes refl = contradiction refl (∉∷[]⇒≢ X∉A)
  ... | no  X≢Y  = refl
  :=-∉-invariant {#ᵀ k} X∉A = refl
  :=-∉-invariant {A ⇒ B} {X} {B = C} X∉ = cong₂ _⇒_
    (:=-∉-invariant {A} (proj₁ (∉-++ X∉)))
    (:=-∉-invariant {B} (proj₂ (∉-++ X∉)))
  :=-∉-invariant {∀ᵀ A} X∉A = cong ∀ᵀ_ (:=-∉-invariant {A} X∉A)

  tm-tm[_:→_]_ : ℕ → Term → Term → Term
  tm-tm[ k :→ N ] (fr x) = fr x
  tm-tm[ k :→ N ] (# i) with k ≟ℕ i
  ... | yes refl = N
  ... | no  _    = # i
  tm-tm[ k :→ N ] (ƛ L) = ƛ tm-tm[ suc k :→ N ] L
  tm-tm[ k :→ N ] (L · M) =
    (tm-tm[ k :→ N ] L) · (tm-tm[ k :→ N ] M)
  tm-tm[ k :→ N ] (Λ L) = Λ tm-tm[ k :→ N ] L
  tm-tm[ k :→ N ] (L [ A ]) = (tm-tm[ k :→ N ] L) [ A ]
  tm-tm[ k :→ N ] ‵zero = ‵zero
  tm-tm[ k :→ N ] (‵suc L) = ‵suc tm-tm[ k :→ N ] L

  ty-ty[_:→_]_ : ℕ → Type → Type → Type
  ty-ty[ k :→ T ] ‵ℕ = ‵ℕ
  ty-ty[ k :→ T ] (frᵀ x) = frᵀ x
  ty-ty[ k :→ T ] (#ᵀ i) with k ≟ℕ i
  ... | yes refl = T
  ... | no  _    = #ᵀ i
  ty-ty[ k :→ T ] (A ⇒ B) = (ty-ty[ k :→ T ] A) ⇒ (ty-ty[ k :→ T ] B)
  ty-ty[ k :→ T ] (∀ᵀ A) = ∀ᵀ (ty-ty[ (suc k) :→ T ] A)

  ty-tm[_:→_]_ : ℕ → Type → Term → Term
  ty-tm[ k :→ T ] (fr x) = fr x
  ty-tm[ k :→ T ] (# i) = # i
  ty-tm[ k :→ T ] (ƛ L) = ƛ ty-tm[ k :→ T ] L
  ty-tm[ k :→ T ] (L · M) = (ty-tm[ k :→ T ] L) · (ty-tm[ k :→ T ] M)
  ty-tm[ k :→ T ] (Λ L) = Λ ty-tm[ suc k :→ T ] L
  ty-tm[ k :→ T ] (L [ A ]) = (ty-tm[ k :→ T ] L) [ ty-ty[ k :→ T ] A ]
  ty-tm[ k :→ T ] ‵zero = ‵zero
  ty-tm[ k :→ T ] (‵suc L) = ‵suc ty-tm[ k :→ T ] L

  ≻⇒:→-invariant : ∀ {C i j} (A : Type) → j ≥ i
    → i ≻ty A
    → ty-ty[ j :→ C ] A ≡ A
  ≻⇒:→-invariant ‵ℕ j≥i i≻A = refl
  ≻⇒:→-invariant (frᵀ x) j≥i i≻A = refl
  ≻⇒:→-invariant {C} {i} {j} (#ᵀ n) j≥i i≻A with j ≟ℕ n
  ... | no  j≢n  = refl
  ... | yes refl with i≻A j ⦃ j≥i ⦄
  ...   | И⟨ Иe₁ , Иe₂ ⟩ with n ≟ℕ n
  ...     | yes refl with () ← Иe₂ (fresh Иe₁) {fresh-correct Иe₁}
  ...     | no  n≢n  = contradiction refl n≢n
  ≻⇒:→-invariant (A ⇒ B) j≥i i≻ = let ⟨ i≻A , i≻B ⟩ = ⇒-≻ i≻
    in cong₂ _⇒_ (≻⇒:→-invariant A j≥i i≻A) (≻⇒:→-invariant B j≥i i≻B)
  ≻⇒:→-invariant {i = i} {j = j} (∀ᵀ A) j≥i i≻ = cong ∀ᵀ_
    (≻⇒:→-invariant A (s≤s j≥i) (i≻∀A⇒si≻A i≻))

  data Context : Set where
    ∅ : Context
    _,_⦂_ : Context → Id → Type → Context
    _,_ : Context → Id → Context

  _+_ : Context → Context → Context
  Γ + ∅ = Γ
  Γ + (Δ , x ⦂ A) = (Γ + Δ) , x ⦂ A
  Γ + (Δ , X) = (Γ + Δ) , X

  map : (Type → Type) → Context → Context
  map f ∅ = ∅
  map f (Γ , x ⦂ A) = (map f Γ) , x ⦂ f A
  map f (Γ , X) = (map f Γ) , X

  domain-ftv : Context → List Id
  domain-ftv ∅ = []
  domain-ftv (ctx , x ⦂ A) = domain-ftv ctx
  domain-ftv (ctx , X) = X ∷ domain-ftv ctx

  domain-all-ftv : Context → List Id
  domain-all-ftv ∅ = []
  domain-all-ftv (ctx , x ⦂ A) = (ftv-ty A) ++ domain-all-ftv ctx
  domain-all-ftv (ctx , X) = X ∷ domain-all-ftv ctx

  domain-ftv-map-invariant : ∀ {Γ f}
    → domain-ftv Γ ≡ (domain-ftv (map f Γ))
  domain-ftv-map-invariant {∅} = refl
  domain-ftv-map-invariant {Γ , x ⦂ A} =
    domain-ftv-map-invariant {Γ}
  domain-ftv-map-invariant {Γ , X} =
    cong (X ∷_) (domain-ftv-map-invariant {Γ})

  domain-++ : ∀ (Γ Δ : Context)
    → (domain-ftv Δ) ++ (domain-ftv Γ) ≡ domain-ftv (Γ + Δ)
  domain-++ Γ ∅ = refl
  domain-++ Γ (Δ , x ⦂ A) = domain-++ Γ Δ
  domain-++ Γ (Δ , Y) = cong (Y ∷_) (domain-++ Γ Δ)

  domain-ftv-++ʳ : ∀ {X} (Γ Δ : Context)
    → X ∈ (domain-ftv Δ) → X ∈ domain-ftv (Γ + Δ)
  domain-ftv-++ʳ {X} Γ Δ X∈Δ = ∈-≡ (∈-++ˡ X∈Δ) (domain-++ Γ Δ)

  data Ok : Context → Set where
    ok-∅ : Ok ∅
    ok-∷fv : ∀ {Γ A x} → Ok Γ → Ty-LocallyClosed A
      → ftv-ty A ⊆ domain-ftv Γ → Ok (Γ , x ⦂ A)
    ok-∷ftv : ∀ {Γ X} → Ok Γ → X ∉ domain-all-ftv Γ → Ok (Γ , X)

  ok-+ : ∀ {Γ Δ} → Ok (Γ + Δ) → Ok Γ
  ok-+ {Γ} {∅} okΓ = okΓ
  ok-+ {Γ} {Δ , x ⦂ A} (ok-∷fv ok+ _ _) = ok-+ ok+
  ok-+ {Γ} {Δ , X} (ok-∷ftv ok+ _) = ok-+ ok+

  extract-⊆ : ∀ {Γ x A} → Ok (Γ , x ⦂ A) → ftv-ty A ⊆ domain-ftv Γ
  extract-⊆ (ok-∷fv okΓ lc-A A⊆Γ) = A⊆Γ

  data _∋_ : Context → Id → Set where
    Z : ∀ {Γ X} → (Γ , X) ∋ X
    S : ∀ {Γ X Y} → Γ ∋ X → (Γ , Y) ∋ X
    S⦂ : ∀ {Γ X y B} → Γ ∋ X → (Γ , y ⦂ B) ∋ X

  infix 4 _∋_⦂_
  data _∋_⦂_ : Context → Id → Type → Set where
    H : ∀ {Γ x y A} → x ≡ y → (Γ , x ⦂ A) ∋ y ⦂ A
    T : ∀ {Γ x y A B} → x ≢ y → (Γ ∋ x ⦂ A) → (Γ , y ⦂ B) ∋ x ⦂ A
    T⦂ : ∀ {Γ x Y A} → (Γ ∋ x ⦂ A) → (Γ , Y) ∋ x ⦂ A

  H′ : ∀ {Γ x A} → (Γ , x ⦂ A) ∋ x ⦂ A
  H′ = H refl

  T′ : ∀ {Γ x y A B} {x≢y : False (x ≟lchar y)}
    → Γ ∋ x ⦂ A → (Γ , y ⦂ B) ∋ x ⦂ A
  T′ { x≢y = x≢y } x = T (toWitnessFalse x≢y) x

  ∋⇒∈ : ∀ {Γ X} → Γ ∋ X → X ∈ domain-ftv Γ
  ∋⇒∈ Z = here refl
  ∋⇒∈ (S ∋X) = there (∋⇒∈ ∋X)
  ∋⇒∈ (S⦂ ∋X) = ∋⇒∈ ∋X

  ∈⇒∋ : ∀ {Γ X} → X ∈ domain-ftv Γ → Γ ∋ X
  ∈⇒∋ {Γ , x ⦂ A} X∈Γ = S⦂ (∈⇒∋ X∈Γ)
  ∈⇒∋ {Γ , Y} {X = X} (here X≡Y) with X ≟lchar Y
  ... | yes refl = Z
  ... | no  X≢Y  = contradiction X≡Y X≢Y
  ∈⇒∋ {Γ , Y} (there X∈Γ) = S (∈⇒∋ X∈Γ)

  ∉-domain-all-∋ : ∀ {Γ X x A} → X ∉ domain-all-ftv Γ → Γ ∋ x ⦂ A
    → X ∉ ftv-ty A
  ∉-domain-all-∋ X∉Γ (H refl) = proj₁ (∉-++ X∉Γ)
  ∉-domain-all-∋ X∉Γ (T _ ∋x) = ∉-domain-all-∋ (proj₂ (∉-++ X∉Γ)) ∋x
  ∉-domain-all-∋ X∉Γ (T⦂ ∋x) = ∉-domain-all-∋ (proj₂ (∉-++ X∉Γ)) ∋x

  ⊆-change-ctx : ∀ {Γ A Δ} → ftv-ty A ⊆ domain-ftv Γ
    → (∀ {X} → Γ ∋ X → Δ ∋ X)
    → ftv-ty A ⊆ domain-ftv Δ
  ⊆-change-ctx {Γ} {A} A⊆Γ ρ =
    All-map (λ px → ∋⇒∈ (ρ (∈⇒∋ px))) A⊆Γ

  ≡-with-∋-ty : ∀ {Γ x A B} → Γ ∋ x ⦂ A → A ≡ B → Γ ∋ x ⦂ B
  ≡-with-∋-ty ∋x refl = ∋x

  ∋-map-ftv : ∀ {Γ X x A C} (Δ : Context)
    → Ok ((Γ , X) + Δ)
    → ((Γ , X) + Δ) ∋ x ⦂ A
    → Γ + (map (ty-ty[ X := C ]_) Δ) ∋ x ⦂ (ty-ty[ X := C ] A)
  ∋-map-ftv ∅ (ok-∷ftv okΓ X∉Γ) (T⦂ ∋x) = ≡-with-∋-ty
    ∋x
    (sym (:=-∉-invariant (∉-domain-all-∋ X∉Γ ∋x)))
  ∋-map-ftv (Δ , y ⦂ B) _ (H refl) = H′
  ∋-map-ftv (Δ , y ⦂ B) (ok-∷fv okΓ+Δ _ _) (T x≢y ∋x) =
    T x≢y (∋-map-ftv Δ okΓ+Δ ∋x)
  ∋-map-ftv (Δ , Y) (ok-∷ftv okΓ,X+Δ Y∉) (T⦂ ∋x) =
    T⦂ (∋-map-ftv Δ okΓ,X+Δ ∋x)

  ftv⊆dom-:= : ∀ {X A C} (Γ Δ : Context)
     → Ty-LocallyClosed C
     → ftv-ty C ⊆ domain-ftv Δ
     → Ok (Γ + (map (ty-ty[ X := C ]_) Δ))
     → ftv-ty A ⊆ domain-ftv ((Γ , X) + Δ)
       -------------------------------------------
     → ftv-ty (ty-ty[ X := C ] A)
         ⊆ domain-ftv (Γ + map (ty-ty[ X := C ]_) Δ)
  ftv⊆dom-:= {X} {‵ℕ} Γ Δ lc-C C⊆Δ okΓ+map A⊆dom = All.[]
  ftv⊆dom-:= {X} {frᵀ Y} {C} Γ Δ _ C⊆Δ _ (Y∈ All.∷ All.[])
    with X ≟lchar Y
  ... | yes refl = All-map
    (λ x∈ → domain-ftv-++ʳ Γ (map (ty-ty[ X := C ]_) Δ)
      (∈-≡ x∈ (domain-ftv-map-invariant {Δ} {ty-ty[ X := C ]_})))
    C⊆Δ
  ... | no  X≢Y  = (helper Δ Y∈ (sym-≢ X≢Y)) All.∷ All.[]
    where
      helper : ∀ {Γ X Y} (Δ : Context)
        → Y ∈ domain-ftv ((Γ , X) + Δ)
        → Y ≢ X
        → Y ∈ domain-ftv (Γ + map (ty-ty[_:=_]_ X C) Δ)
      helper ∅ (here refl) Y≢X = contradiction refl Y≢X
      helper ∅ (there Y∈) Y≢X = Y∈
      helper (Δ , z ⦂ C) Y∈ Y≢X = helper Δ Y∈ Y≢X
      helper (Δ , W) (here refl) Y≢X = here refl
      helper (Δ , W) (there Y∈) Y≢X = there (helper Δ Y∈ Y≢X)
  ftv⊆dom-:= {X} {#ᵀ n} Γ Δ lc-C C⊆Δ okΓ+map A⊆dom = All.[]
  ftv⊆dom-:= {X} {A ⇒ B} Γ Δ lc-C C⊆Δ okΓ+map ⊆dom =
    let ⟨ A⊆ , B⊆ ⟩ = ⊆-++ ⊆dom
    in ++-⊆
      (ftv⊆dom-:= {A = A} Γ Δ lc-C C⊆Δ okΓ+map A⊆)
      (ftv⊆dom-:= {A = B} Γ Δ lc-C C⊆Δ okΓ+map B⊆)
  ftv⊆dom-:= {X} {∀ᵀ A} Γ Δ lc-C C⊆Δ okΓ+map A⊆dom =
    ftv⊆dom-:= {X} {A} Γ Δ lc-C C⊆Δ okΓ+map A⊆dom

  infix  4 _⊢_⦂_
  data _⊢_⦂_ : Context → Term → Type → Set where
    ⊢free : ∀ {Γ x A}
      → Ok Γ
      → Ty-LocallyClosed A
      → Γ ∋ x ⦂ A
        ----------------
      → Γ ⊢ fr x ⦂ A

    ⊢ƛ : ∀ {Γ L A B}
      → Ty-LocallyClosed A
      → И x , (Γ , x ⦂ A ⊢ tm-tm[ 0 —→ x ] L ⦂ B)
        ------------------------------------
      → Γ ⊢ ƛ L ⦂ (A ⇒ B)

    ⊢· : ∀ {Γ L M A B}
      → Γ ⊢ L ⦂ (A ⇒ B)
      → Γ ⊢ M ⦂ A
        ---------------
      → Γ ⊢ L · M ⦂ B

    ⊢Λ : ∀ {Γ L B}
      → И T , ((Γ , T) ⊢ ty-tm[ 0 —→ T ] L ⦂ (ty-ty[ 0 —→ T ] B))
        ----------------------------------------------------
      → Γ ⊢ Λ L ⦂ ∀ᵀ B

    ⊢[] : ∀ {Γ L A B}
      → Ty-LocallyClosed A
      → ftv-ty A ⊆ domain-ftv Γ
      → Γ ⊢ L ⦂ ∀ᵀ B
        ---------------------------
      → Γ ⊢ L [ A ] ⦂ ty-ty[ 0 :→ A ] B

    ⊢zero : ∀ {Γ}
      → Ok Γ
        -----------
      → Γ ⊢ ‵zero ⦂ ‵ℕ

    ⊢suc : ∀ {Γ L}
      → Γ ⊢ L ⦂ ‵ℕ
        -------------
      → Γ ⊢ ‵suc L ⦂ ‵ℕ

  twice : ∅ ⊢ (Λ ƛ (ƛ ((# 1) · ((# 1) · (# 0)))))
      ⦂ ∀ᵀ (((#ᵀ 0) ⇒ (#ᵀ 0)) ⇒ ((#ᵀ 0) ⇒ (#ᵀ 0)))
  twice = ⊢Λ И⟨ [] , (λ X {X∉} → ⊢ƛ fr⇒fr-lc И⟨ [] , (λ f {f∉} →
    ⊢ƛ ty-fr-lc И⟨ (f ∷ []) , (λ x {x∉} → ⊢·
      (⊢free ok-ctx fr⇒fr-lc (T (f≢x x∉) H′))
      (⊢·
        (⊢free ok-ctx fr⇒fr-lc (T (f≢x x∉) H′))
        (⊢free ok-ctx ty-fr-lc H′))) ⟩) ⟩) ⟩
    where
      fr⇒fr-lc : ∀ {A} → Ty-LocallyClosed (frᵀ A ⇒ frᵀ A)
      fr⇒fr-lc j = И⟨ [] , (λ _ → refl) ⟩
      f≢x : ∀ {f x} → x ∉ f ∷ [] → f ≢ x
      f≢x x∉ = sym-≢ (∉∷[]⇒≢ x∉)
      ok-ctx : ∀ {f X x}
        → Ok (((∅ , X) , f ⦂ (frᵀ X ⇒ frᵀ X)) , x ⦂ frᵀ X)
      ok-ctx = ok-∷fv
                  (ok-∷fv (ok-∷ftv ok-∅ (λ ()))
                    fr⇒fr-lc
                    (here refl All.∷ here refl All.∷ All.[]))
                  ty-fr-lc
                  ((here refl) All.∷ All.[])

  Ω : ∅ ⊢ (ƛ (((# 0) [ ∀ᵀ ((#ᵀ 0) ⇒ (#ᵀ 0)) ]) · (# 0)))
      ⦂ (∀ᵀ ((#ᵀ 0) ⇒ (#ᵀ 0))) ⇒ (∀ᵀ ((#ᵀ 0) ⇒ (#ᵀ 0)))
  Ω = ⊢ƛ lc-forall И⟨ [] , (λ x {x∉} →
    ⊢·
      (⊢[] lc-forall All.[] (⊢free ok-ctx lc-forall H′))
      (⊢free ok-ctx lc-forall H′)) ⟩
    where
      lc-forall : Ty-LocallyClosed (∀ᵀ (#ᵀ 0 ⇒ #ᵀ 0))
      lc-forall j = И⟨ [] , (λ _ → refl) ⟩
      ok-ctx : ∀ {x} →  Ok (∅ , x ⦂ (∀ᵀ (#ᵀ 0 ⇒ #ᵀ 0)))
      ok-ctx = ok-∷fv ok-∅ lc-forall All.[]

  ≡-with-⊢-tm : ∀ {Γ L M A} → Γ ⊢ L ⦂ A → L ≡ M → Γ ⊢ M ⦂ A
  ≡-with-⊢-tm ⊢L refl = ⊢L
  ≡-with-⊢-ty : ∀ {Γ L A B} → Γ ⊢ L ⦂ A → A ≡ B → Γ ⊢ L ⦂ B
  ≡-with-⊢-ty ⊢L refl = ⊢L
  ≡-with-⊢-ctx : ∀ {Γ Δ L A} → Γ ⊢ L ⦂ A → Γ ≡ Δ → Δ ⊢ L ⦂ A
  ≡-with-⊢-ctx ⊢L refl = ⊢L

  ⊢⇒Ok : ∀ {Γ L A} → Γ ⊢ L ⦂ A → Ok Γ
  ⊢⇒Ok (⊢free okΓ lc-A ∋x) = okΓ
  ⊢⇒Ok (⊢ƛ lc-A И⟨ Иe₁ , Иe₂ ⟩)
    with ⊢⇒Ok (Иe₂ (fresh Иe₁) {fresh-correct Иe₁})
  ... | ok-∷fv OkΓ _ _ = OkΓ
  ⊢⇒Ok (⊢· ⊢L ⊢LM) = ⊢⇒Ok ⊢L
  ⊢⇒Ok (⊢Λ И⟨ Иe₁ , Иe₂ ⟩)
    with ⊢⇒Ok (Иe₂ (fresh Иe₁) {fresh-correct Иe₁})
  ... | ok-∷ftv OkΓ _ = OkΓ
  ⊢⇒Ok (⊢[] lc-A _ ⊢L) = ⊢⇒Ok ⊢L
  ⊢⇒Ok (⊢zero OkΓ) = OkΓ
  ⊢⇒Ok (⊢suc ⊢L) = ⊢⇒Ok ⊢L

  ext-tm : ∀ {Γ Δ}
    → (∀ {x A}     →        Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
    → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
  ext-tm ρ (H refl) = H′
  ext-tm ρ (T x≢y ∋x) = T x≢y (ρ ∋x)

  ext-ty : ∀ {Γ Δ}
    → (∀ {X}   →       Γ ∋ X →       Δ ∋ X)
    → (∀ {X Y} → (Γ , Y) ∋ X → (Δ , Y) ∋ X)
  ext-ty ρ Z = Z
  ext-ty ρ (S ∋X) = S (ρ ∋X)

  ext-tm-ty : ∀ {Γ Δ}
    → (∀ {x A}   →       Γ ∋ x ⦂ A →       Δ ∋ x ⦂ A)
    → (∀ {x Y A} → (Γ , Y) ∋ x ⦂ A → (Δ , Y) ∋ x ⦂ A)
  ext-tm-ty ρ (T⦂ ∋x) = T⦂ (ρ ∋x)

  ext-ty-tm : ∀ {Γ Δ}
    → (∀ {X}     →          Γ ∋ X →           Δ ∋ X)
    → (∀ {X y A} → (Γ , y ⦂ A) ∋ X → (Δ , y ⦂ A) ∋ X)
  ext-ty-tm ρ (S⦂ ∋X) = S⦂ (ρ ∋X)

  rename : ∀ {Γ Δ}
    → Ok Δ
    → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
    → (∀ {X} → Γ ∋ X → Δ ∋ X)
      ---------------------------------
    → (∀ {L A} → Γ ⊢ L ⦂ A → Δ ⊢ L ⦂ A)
  rename okΔ ρ-tm ρ-ty (⊢free okΓ lc-A x) = ⊢free okΔ lc-A (ρ-tm x)
  rename okΔ ρ-tm ρ-ty (⊢· ⊢A⇒B ⊢A) =
    ⊢· (rename okΔ ρ-tm ρ-ty ⊢A⇒B) (rename okΔ ρ-tm ρ-ty ⊢A)
  rename {Γ} {Δ} okΔ ρ-tm ρ-ty (⊢Λ И⟨ Иe₁ , Иe₂ ⟩) =
    ⊢Λ И⟨ Иe₁ ++ domain-all-ftv Δ , (λ T {T∉} →
      let ⟨ T∉Иe₁ , T∉Δ ⟩ = ∉-++ T∉
      in rename
        (ok-∷ftv okΔ T∉Δ)
        (ext-tm-ty ρ-tm)
        (ext-ty ρ-ty)
        (Иe₂ T {T∉Иe₁}) ) ⟩
  rename {Γ} {Δ} okΔ ρ-tm ρ-ty {_} {A ⇒ B} (⊢ƛ lc-A И⟨ Иe₁ , Иe₂ ⟩) =
    ⊢ƛ lc-A И⟨ Иe₁ , (λ a {a∉} →
      rename
        (OkΔ,x a a∉)
        (ext-tm ρ-tm)
        (ext-ty-tm ρ-ty)
        (Иe₂ a {a∉})) ⟩
    where
      OkΔ,x : (x : Id) → x ∉ Иe₁ → Ok (Δ , x ⦂ A)
      OkΔ,x x x∉ with ⊢⇒Ok (Иe₂ x {x∉})
      ... | ok-∷fv OkΓ lc-A ftvA⊆Γ =
        ok-∷fv okΔ lc-A (⊆-change-ctx {Γ} {A} ftvA⊆Γ ρ-ty)
  rename okΔ ρ-tm ρ-ty (⊢[] lc A⊆Γ ⊢L) = ⊢[]
    lc
    (All-map (λ px → ∋⇒∈ (ρ-ty (∈⇒∋ px))) A⊆Γ)
    (rename okΔ ρ-tm ρ-ty ⊢L)
  rename okΔ ρ-tm ρ-ty (⊢zero okΓ) = ⊢zero okΔ
  rename okΔ ρ-tm ρ-ty (⊢suc ⊢L) = ⊢suc (rename okΔ ρ-tm ρ-ty ⊢L)

  weaken : ∀ {Γ L A} → Ok Γ → ∅ ⊢ L ⦂ A → Γ ⊢ L ⦂ A
  weaken okΓ ⊢L = rename okΓ (λ ()) (λ ()) ⊢L

  swap : ∀ {Γ x y L A B C}
    → x ≢ y
    → (Γ , y ⦂ B) , x ⦂ A ⊢ L ⦂ C
    → (Γ , x ⦂ A) , y ⦂ B ⊢ L ⦂ C
  swap {Γ} {x} {y} {L} {A} {B} {C} x≢y ⊢L with ⊢⇒Ok ⊢L
  ... | ok-∷fv (ok-∷fv okΓ lc-B B⊆Γ) lc-A A⊆Γ =
    rename (ok-∷fv (ok-∷fv okΓ lc-A A⊆Γ) lc-B B⊆Γ) ρ₁ ρ₂ ⊢L
    where
      ρ₁ : ∀ {z C}
        → (Γ , y ⦂ B) , x ⦂ A ∋ z ⦂ C
          -------------------------
        → (Γ , x ⦂ A) , y ⦂ B ∋ z ⦂ C
      ρ₁ (H refl) = T x≢y H′
      ρ₁ (T z≢x (H refl)) = H′
      ρ₁ (T z≢x (T z≢y ∋z)) = T z≢y (T z≢x ∋z)
      ρ₂ : ∀ {X}
        → ((Γ , y ⦂ B) , x ⦂ A) ∋ X
          -------------------------
        → ((Γ , x ⦂ A) , y ⦂ B) ∋ X
      ρ₂ (S⦂ (S⦂ ∋X)) = S⦂ (S⦂ ∋X)

  swap-tm-ty : ∀ {Γ X y L B C}
    → ((Γ , y ⦂ B) , X) ⊢ L ⦂ C
    → (Γ , X) , y ⦂ B ⊢ L ⦂ C
  swap-tm-ty {Γ} {X} {y} {L} {B} {C} ⊢L with ⊢⇒Ok ⊢L
  ... | ok-∷ftv (ok-∷fv okΓ lc-B B⊆Γ) X∉Γ =
    rename
      (ok-∷fv (ok-∷ftv okΓ (proj₂ (∉-++ X∉Γ))) lc-B (⊆⇒⊆∷ B⊆Γ))
      ρ₁
      ρ₂
      ⊢L
    where
      ρ₁ : ∀ {x A}
        → ((Γ , y ⦂ B) , X) ∋ x ⦂ A
          -------------------------
        → ((Γ , X) , y ⦂ B) ∋ x ⦂ A
      ρ₁ (T⦂ (H refl)) = H′
      ρ₁ (T⦂ (T x≢y ∋x)) = T x≢y (T⦂ ∋x)
      ρ₂ : ∀ {Z : Id}
        → ((Γ , y ⦂ B) , X) ∋ Z
        → ((Γ , X) , y ⦂ B) ∋ Z
      ρ₂ Z = S⦂ Z
      ρ₂ (S (S⦂ ∋Z)) = S⦂ (S ∋Z)

  drop : ∀ {Γ x L A B C}
    → (Γ , x ⦂ A) , x ⦂ B ⊢ L ⦂ C
    → Γ , x ⦂ B ⊢ L ⦂ C
  drop {Γ} {x} {L} {A} {B} {C} ⊢L with ⊢⇒Ok ⊢L
  ... | ok-∷fv (ok-∷fv okΓ lc-A A⊆Γ) lc-B B⊆Γ =
    rename (ok-∷fv okΓ lc-B B⊆Γ) ρ₁ ρ₂ ⊢L
    where
      ρ₁ : ∀ {z C}
        → (Γ , x ⦂ A) , x ⦂ B ∋ z ⦂ C
          -------------------------
        → Γ , x ⦂ B ∋ z ⦂ C
      ρ₁ (H refl) = H′
      ρ₁ (T z≢x (H refl)) = contradiction refl z≢x
      ρ₁ (T z≢x (T .z≢x ∋z)) = T z≢x ∋z
      ρ₂ : ∀ {X}
        → ((Γ , x ⦂ A) , x ⦂ B) ∋ X
          -------------------------
        → (Γ , x ⦂ B) ∋ X
      ρ₂ (S⦂ (S⦂ ∋X)) = S⦂ ∋X

  subst-open : ∀ {N x y i} (L : Term)
    → x ≢ y → (i ≻tm N)
    → tm-tm[ x := N ] (tm-tm[ i —→ y ] L)
      ≡ tm-tm[ i —→ y ] (tm-tm[ x := N ] L)
  subst-open {x = x} (fr z) x≢y i≻u with x ≟lchar z
  ... | yes refl = sym (lemma2·7-2-tm ≤-refl i≻u)
  ... | no  _    = refl
  subst-open {_} {x} {y} {i} (# k) x≢y i≻u with i ≟ℕ k
  ... | no  _ = refl
  ... | yes refl with x ≟lchar y
  ...    | yes refl = contradiction refl x≢y
  ...    | no  _    = refl
  subst-open {i = i} (ƛ L) x≢y i≻u = cong ƛ_
    (subst-open L x≢y (lemma2·6-tm (n≤1+n i) i≻u))
  subst-open (L · M) x≢y i≻u = cong₂ _·_
    (subst-open L x≢y i≻u) (subst-open M x≢y i≻u)
  subst-open (Λ L) x≢y i≻u = cong Λ_ (subst-open L x≢y i≻u)
  subst-open (L [ A ]) x≢y i≻u =
    cong₂ _[_] (subst-open L x≢y i≻u) refl
  subst-open ‵zero x≢y i≻u = refl
  subst-open (‵suc L) x≢y i≻u = cong ‵suc_ (subst-open L x≢y i≻u)

  subst-open-ctx : ∀ {Γ A N x y i} (L : Term)
    → x ≢ y → (i ≻tm N)
    → Γ ⊢ tm-tm[ x := N ] (tm-tm[ i —→ y ] L) ⦂ A
    → Γ ⊢ tm-tm[ i —→ y ] (tm-tm[ x := N ] L) ⦂ A
  subst-open-ctx L x≢y i≻N assump =
    ≡-with-⊢-tm assump (subst-open L x≢y i≻N)

  subst-open-ty-tm : ∀ {N x y i j} (L : Term)
    → x ≢ y → j ≥ i → (i ≻ty-tm N)
    → tm-tm[ x := N ] (ty-tm[ j —→ y ] L)
      ≡ ty-tm[ j —→ y ] (tm-tm[ x := N ] L)
  subst-open-ty-tm {N} {x} {y} {i} {j} (fr z) x≢y j≥i i≻N
    with x ≟lchar z
  ... | yes refl =
    begin
      N
    ≡⟨ sym (lemma2·7-2-ty-tm ≤-refl (lemma2·6-ty-tm j≥i i≻N)) ⟩
      ty-tm[ j —→ y ] N
    ∎
  ... | no  x≢z  = refl
  subst-open-ty-tm (# k) x≢y j≥i i≻N = refl
  subst-open-ty-tm (ƛ L) x≢y j≥i i≻N
    rewrite subst-open-ty-tm L x≢y j≥i i≻N = refl
  subst-open-ty-tm (L · M) x≢y j≥i i≻N
    rewrite subst-open-ty-tm L x≢y j≥i i≻N
    | subst-open-ty-tm M x≢y j≥i i≻N
    = refl
  subst-open-ty-tm (Λ L) x≢y j≥i i≻N
    rewrite subst-open-ty-tm L x≢y (m≤n⇒m≤1+n j≥i) i≻N = refl
  subst-open-ty-tm (L [ A ]) x≢y j≥i i≻N
    rewrite subst-open-ty-tm L x≢y j≥i i≻N = refl
  subst-open-ty-tm ‵zero x≢y j≥i i≻N = refl
  subst-open-ty-tm (‵suc L) x≢y j≥i i≻N rewrite
    subst-open-ty-tm L x≢y j≥i i≻N = refl

  subst-open-ty-tm-ctx : ∀ {Γ A N x y i j} (L : Term)
    → x ≢ y → j ≥ i → (i ≻ty-tm N)
    → Γ ⊢ tm-tm[ x := N ] (ty-tm[ j —→ y ] L) ⦂ A
    → Γ ⊢ ty-tm[ j —→ y ] (tm-tm[ x := N ] L) ⦂ A
  subst-open-ty-tm-ctx L x≢y j≥i i≻N assump =
    ≡-with-⊢-tm assump (subst-open-ty-tm L x≢y j≥i i≻N)

  subst-open-ty-tm-tm-tm : ∀ {C x y i j} (L : Term)
    → j ≥ i → (i ≻ty C)
    → ty-tm[ x := C ] (tm-tm[ j —→ y ] L)
      ≡ tm-tm[ j —→ y ] (ty-tm[ x := C ] L)
  subst-open-ty-tm-tm-tm (fr y) j≥i i≻C = refl
  subst-open-ty-tm-tm-tm {j = j} (# k) j≥i i≻C with j ≟ℕ k
  ... | yes refl = refl
  ... | no  j≢k  = refl
  subst-open-ty-tm-tm-tm (ƛ L) j≥i i≻C = cong ƛ_
    (subst-open-ty-tm-tm-tm L (m≤n⇒m≤1+n j≥i) i≻C)
  subst-open-ty-tm-tm-tm (L · M) j≥i i≻C = cong₂ _·_
    (subst-open-ty-tm-tm-tm L j≥i i≻C)
    (subst-open-ty-tm-tm-tm M j≥i i≻C)
  subst-open-ty-tm-tm-tm (Λ L) j≥i i≻C = cong Λ_
    (subst-open-ty-tm-tm-tm L j≥i i≻C)
  subst-open-ty-tm-tm-tm (L [ A ]) j≥i i≻C = cong₂ _[_]
    (subst-open-ty-tm-tm-tm L j≥i i≻C)
    refl
  subst-open-ty-tm-tm-tm ‵zero j≥i i≻C = refl
  subst-open-ty-tm-tm-tm (‵suc L) j≥i i≻C = cong ‵suc_
    (subst-open-ty-tm-tm-tm L j≥i i≻C)

  subst-open-ty-tm-tm-tm-ctx : ∀ {Γ A C x y i j} (L : Term)
    → j ≥ i → (i ≻ty C)
    → Γ ⊢ ty-tm[ x := C ] (tm-tm[ j —→ y ] L) ⦂ A
    → Γ ⊢ tm-tm[ j —→ y ] (ty-tm[ x := C ] L) ⦂ A
  subst-open-ty-tm-tm-tm-ctx L j≥i i≻C assump =
    ≡-with-⊢-tm assump (subst-open-ty-tm-tm-tm L j≥i i≻C)

  subst-open-ty-ty-ty-ty : ∀ {C x y i j} (A : Type)
    → x ≢ y → j ≥ i → (i ≻ty C)
    → ty-ty[ x := C ] (ty-ty[ j —→ y ] A)
      ≡ ty-ty[ j —→ y ] (ty-ty[ x := C ] A)
  subst-open-ty-ty-ty-ty ‵ℕ x≢y j≥i i≻C = refl
  subst-open-ty-ty-ty-ty {x = x} {j = j} (frᵀ z) x≢y j≥i i≻C
    with x ≟lchar z
  ... | yes refl = sym (lemma2·7-2-ty j≥i i≻C)
  ... | no  x≢z  = refl
  subst-open-ty-ty-ty-ty {x = x} {y = y} {j = j}
      (#ᵀ k) x≢y j≥i i≻C with j ≟ℕ k
  ... | no  j≢k  = refl
  ... | yes refl with x ≟lchar y
  ...   | yes refl = contradiction refl x≢y
  ...   | no  _    = refl
  subst-open-ty-ty-ty-ty (A ⇒ B) x≢y j≥i i≻C rewrite
      subst-open-ty-ty-ty-ty A x≢y j≥i i≻C
    | subst-open-ty-ty-ty-ty B x≢y j≥i i≻C
    = refl
  subst-open-ty-ty-ty-ty {j = j} (∀ᵀ A) x≢y j≥i i≻C = cong ∀ᵀ_
    (subst-open-ty-ty-ty-ty {j = suc j} A x≢y (m≤n⇒m≤1+n j≥i) i≻C)

  subst-open-ty-ty-ty-ty-ctx : ∀ {Γ L C A x y i j}
    → x ≢ y → j ≥ i → (i ≻ty C)
    → Γ ⊢ L ⦂ ty-ty[ x := C ] (ty-ty[ j —→ y ] A)
    → Γ ⊢ L ⦂ ty-ty[ j —→ y ] (ty-ty[ x := C ] A)
  subst-open-ty-ty-ty-ty-ctx {A = A} x≢y j≥i i≻C assump =
    ≡-with-⊢-ty assump (subst-open-ty-ty-ty-ty A x≢y j≥i i≻C)

  subst-open-ty-tm-ty-tm : ∀ {C x y i j} (L : Term)
    → x ≢ y → j ≥ i → (i ≻ty C)
    → ty-tm[ x := C ] (ty-tm[ j —→ y ] L)
      ≡ ty-tm[ j —→ y ] (ty-tm[ x := C ] L)
  subst-open-ty-tm-ty-tm (fr z) x≢y j≥i i≻C = refl
  subst-open-ty-tm-ty-tm (# k) x≢y j≥i i≻C = refl
  subst-open-ty-tm-ty-tm (ƛ L) x≢y j≥i i≻C rewrite
    subst-open-ty-tm-ty-tm L x≢y j≥i i≻C = refl
  subst-open-ty-tm-ty-tm (L · M) x≢y j≥i i≻C rewrite
      subst-open-ty-tm-ty-tm L x≢y j≥i i≻C
    | subst-open-ty-tm-ty-tm M x≢y j≥i i≻C
    = refl
  subst-open-ty-tm-ty-tm {j = j} (Λ L) x≢y j≥i i≻C = cong Λ_
    (subst-open-ty-tm-ty-tm {j = suc j} L x≢y (m≤n⇒m≤1+n j≥i) i≻C)
  subst-open-ty-tm-ty-tm (L [ A ]) x≢y j≥i i≻C = cong₂ _[_]
    (subst-open-ty-tm-ty-tm L x≢y j≥i i≻C)
    (subst-open-ty-ty-ty-ty A x≢y j≥i i≻C)
  subst-open-ty-tm-ty-tm ‵zero x≢y j≥i i≻C = refl
  subst-open-ty-tm-ty-tm (‵suc L) x≢y j≥i i≻C rewrite
    (subst-open-ty-tm-ty-tm L x≢y j≥i i≻C) = refl

  subst-open-ty-tm-ty-tm-ctx : ∀ {Γ L A C x y i j}
    → x ≢ y → j ≥ i → (i ≻ty C)
    → Γ ⊢ ty-tm[ x := C ] (ty-tm[ j —→ y ] L) ⦂ A
    → Γ ⊢ ty-tm[ j —→ y ] (ty-tm[ x := C ] L) ⦂ A
  subst-open-ty-tm-ty-tm-ctx {L = L} x≢y j≥i i≻C assump =
    ≡-with-⊢-tm assump (subst-open-ty-tm-ty-tm L x≢y j≥i i≻C)

  subst-intro : ∀ {x i} (L N : Term) → x ∉ fv-tm L
    → tm-tm[ i :→ N ] L ≡ tm-tm[ x := N ] (tm-tm[ i —→ x ] L)
  subst-intro {x} (fr y) N x∉fv-L with x ≟lchar y
  ... | yes refl = contradiction refl (∉∷[]⇒≢ x∉fv-L)
  ... | no  x≢y  = refl
  subst-intro {x} {i} (# k) N x∉fv-L with i ≟ℕ k
  ... | no  i≢k = refl
  ... | yes refl with x ≟lchar x
  ...   | yes refl = refl
  ...   | no  x≢x  = contradiction refl x≢x
  subst-intro {x} {i} (ƛ L) N x∉fv-L
    rewrite subst-intro {x} {suc i} L N x∉fv-L = refl
  subst-intro (L · M) N x∉ =
    let ⟨ x∉fv-L , x∉fv-M ⟩ = ∉-++ {xs = fv-tm L} x∉
    in cong₂ _·_ (subst-intro L N x∉fv-L) (subst-intro M N x∉fv-M)
  subst-intro (Λ L) N x∉fv-L = cong Λ_ (subst-intro L N x∉fv-L)
  subst-intro (L [ A ]) N x∉fv-L =
    cong₂ _[_] (subst-intro L N x∉fv-L) refl
  subst-intro ‵zero N x∉fv-L = refl
  subst-intro (‵suc L) N x∉fv-L =
    cong ‵suc_ (subst-intro L N x∉fv-L)

  subst-intro-ty-ty : ∀ {x i B} (A : Type)
    → x ∉ ftv-ty A
    → ty-ty[ i :→ B ] A
      ≡ ty-ty[ x := B ] (ty-ty[ i —→ x ] A)
  subst-intro-ty-ty ‵ℕ x∉ = refl
  subst-intro-ty-ty {x} (frᵀ y) x∉ with x ≟lchar y
  ... | yes refl = contradiction refl (∉∷[]⇒≢ x∉)
  ... | no  x≢y  = refl
  subst-intro-ty-ty {x} {i} (#ᵀ k) x∉ with i ≟ℕ k
  ... | no  i≢k  = refl
  ... | yes refl with x ≟lchar x
  ...   | yes refl = refl
  ...   | no  x≢x  = contradiction refl x≢x
  subst-intro-ty-ty (A ⇒ B) x∉ = let ⟨ x∉A , x∉B ⟩ = ∉-++ x∉
    in cong₂ _⇒_ (subst-intro-ty-ty A x∉A) (subst-intro-ty-ty B x∉B)
  subst-intro-ty-ty {i = i} (∀ᵀ A) x∉ =
    cong ∀ᵀ_ (subst-intro-ty-ty {i = suc i} A x∉)

  subst-intro-ty-tm : ∀ {x i B} (L : Term)
    → x ∉ ftv-tm L
    → ty-tm[ i :→ B ] L
      ≡ ty-tm[ x := B ] (ty-tm[ i —→ x ] L)
  subst-intro-ty-tm (fr x) x∉ = refl
  subst-intro-ty-tm (# k) x∉ = refl
  subst-intro-ty-tm (ƛ L) x∉ = cong ƛ_ (subst-intro-ty-tm L x∉)
  subst-intro-ty-tm (L · M) x∉ = let ⟨ x∉L , x∉M ⟩ = ∉-++ x∉
    in cong₂ _·_ (subst-intro-ty-tm L x∉L) (subst-intro-ty-tm M x∉M)
  subst-intro-ty-tm (Λ L) x∉ = cong Λ_ (subst-intro-ty-tm L x∉)
  subst-intro-ty-tm (L [ A ]) x∉ = let ⟨ x∉L , x∉A ⟩ = ∉-++ x∉
    in cong₂ _[_] (subst-intro-ty-tm L x∉L) (subst-intro-ty-ty A x∉A )
  subst-intro-ty-tm ‵zero x∉ = refl
  subst-intro-ty-tm (‵suc L) x∉ = cong ‵suc_ (subst-intro-ty-tm L x∉)

  ⊢⇒lc : ∀ {Γ L A} → Γ ⊢ L ⦂ A → Tm-LocallyClosed L
  ⊢⇒lc (⊢free okΓ lc-A ∋x) j = И⟨ [] , (λ _ → refl) ⟩
  ⊢⇒lc (⊢ƛ lc-A И⟨ Иe₁ , Иe₂ ⟩) j = И⟨ Иe₁ , (λ a {a∉} → cong ƛ_
    (open-rec-lc-lemma (λ ())
      (lemma2·7-2-tm z≤n (⊢⇒lc (Иe₂ a {a∉}))))) ⟩
  ⊢⇒lc {Γ} (⊢· ⊢A⇒B ⊢A) _ = И⟨ [] , (λ _ → cong₂ _·_
    (lemma2·7-2-tm z≤n (⊢⇒lc ⊢A⇒B))
    (lemma2·7-2-tm z≤n (⊢⇒lc ⊢A))) ⟩
  ⊢⇒lc {Γ} (⊢Λ И⟨ Иe₁ , Иe₂ ⟩) j =
    И⟨ Иe₁ , (λ a {a∉} →
      cong Λ_ (lemma2·7-2-tm z≤n
        (helper z≤n (⊢⇒lc (Иe₂ a {a∉}))))) ⟩
    where
      helper : ∀ {N i k q x} → k ≥ i → i ≻tm (ty-tm[ q —→ x ] N)
        → k ≻tm N
      helper {fr x} {k = k} k≥i i≻ty j = i≻ty k ⦃ k≥i ⦄
      helper {# n} k≥i i≻ty = lemma2·6-tm k≥i i≻ty
      helper {ƛ N} {i} {k} {q} {x} k≥i i≻ty j =
        let induc-hypo = helper {k = suc i} (≤-refl) (≻ƛ⇒s≻ƛ i≻ty)
            И⟨ Иe₁ , Иe₂ ⟩ = induc-hypo (suc j) ⦃ s≤s (≤-trans k≥i it) ⦄
        in И⟨ Иe₁ , (λ a {a∉} → cong ƛ_ (Иe₂ a {a∉})) ⟩
      helper {N · N₁} k≥i i≻ty j =
        let ⟨ i≻L  , i≻M ⟩ = ·-≻ i≻ty
            И⟨ L-Иe₁ , L-Иe₂ ⟩ = (helper k≥i i≻L) j
            И⟨ M-Иe₁ , M-Иe₂ ⟩ = (helper k≥i i≻M) j
          in И⟨ (L-Иe₁ ++ M-Иe₁) , (λ a {a∉} → cong₂ _·_
            (L-Иe₂ a {proj₁ (∉-++ a∉)})
            (M-Иe₂ a {proj₂ (∉-++ {xs = L-Иe₁} a∉)})) ⟩
      helper {Λ N} k≥i i≻ty j =
        let И⟨ Иe₁ , Иe₂ ⟩ = (helper k≥i (Λ-≻ i≻ty)) j
        in И⟨ Иe₁ , (λ a {a∉} → cong Λ_ (Иe₂ a {a∉})) ⟩
      helper {N [ A ]} k≥i i≻ty j =
        let И⟨ Иe₁ , Иe₂ ⟩ = (helper k≥i ([]-≻ i≻ty)) j
        in И⟨ Иe₁ , (λ a {a∉} → cong _[ A ] (Иe₂ a {a∉})) ⟩
      helper {‵zero} k≥i i≻ty j = И⟨ [] , (λ _ → refl) ⟩
      helper {‵suc N} k≥i i≻ty j =
        let И⟨ Иe₁ , Иe₂ ⟩ = (helper k≥i (‵suc-≻ i≻ty)) j
        in И⟨ Иe₁ , (λ a {a∉} → cong ‵suc_ (Иe₂ a {a∉})) ⟩
  ⊢⇒lc {L = L [ A ]} (⊢[] _ _ ⊢L) j =
    let И⟨ Иe₁ , Иe₂ ⟩ = (⊢⇒lc ⊢L) j
    in И⟨ Иe₁ , (λ a {a∉} → cong _[ A ]  (Иe₂ a {a∉})) ⟩
  ⊢⇒lc (⊢zero _) j = И⟨ [] , (λ _ → refl) ⟩
  ⊢⇒lc (⊢suc ⊢L) j = let И⟨ Иe₁ , Иe₂ ⟩ = (⊢⇒lc ⊢L) j
    in И⟨ Иe₁ , (λ a {a∉} → cong ‵suc_ (Иe₂ a {a∉})) ⟩

  ⊢⇒lc-ty : ∀ {Γ L A} → Γ ⊢ L ⦂ A → Ty-LocallyClosed A
  ⊢⇒lc-ty {Γ} {fr x} (⊢free okΓ lc-A ∋x) = lc-A
  ⊢⇒lc-ty {Γ} {ƛ L} (⊢ƛ lc-B И⟨ Иe₁ , Иe₂ ⟩) j =
    let И⟨ B-Иe₁ , B-Иe₂ ⟩ = lc-B j
        И⟨ A-Иe₁ , A-Иe₂ ⟩ =
          (⊢⇒lc-ty (Иe₂ (fresh Иe₁) {fresh-correct Иe₁})) j
    in И⟨ A-Иe₁ ++ B-Иe₁ , (λ a {a∉} → cong₂ _⇒_
      (B-Иe₂ a {proj₂ (∉-++ {xs = A-Иe₁} a∉)})
      (A-Иe₂ a {proj₁ (∉-++ a∉)})) ⟩
  ⊢⇒lc-ty {Γ} {L · M} (⊢· ⊢L ⊢M) = proj₂ (⇒-≻ (⊢⇒lc-ty ⊢L))
  ⊢⇒lc-ty {Γ} {Λ L} (⊢Λ И⟨ Иe₁ , Иe₂ ⟩) j =
    let induction-hypo = ⊢⇒lc-ty (Иe₂ (fresh Иe₁) {fresh-correct Иe₁})
        И⟨ B-Иe₁ , B-Иe₂ ⟩ = induction-hypo (suc j) ⦃ z≤n ⦄
    in И⟨ B-Иe₁ ++ Иe₁ , (λ a {a∉} → cong ∀ᵀ_
      (open-rec-lc-lemma-ty
        (λ ())
        (B-Иe₂ a {proj₁ (∉-++ a∉)}))) ⟩
  ⊢⇒lc-ty {Γ} {L [ B ]} (⊢[] lc-B _ ⊢L) =
    let 1≻A = i≻∀A⇒si≻A (⊢⇒lc-ty ⊢L)
    in helper z≤n 1≻A lc-B
    where
      helper : ∀ {A B i j}
        → j ≥ i
        → (suc i) ≻ty A
        → i ≻ty B → j ≻ty (ty-ty[ i :→ B ] A)
      helper {‵ℕ} j≥i si≻A lc-B j = И⟨ [] , (λ _ → refl) ⟩
      helper {frᵀ x} j≥i si≻A lc-B j = И⟨ [] , (λ _ → refl) ⟩
      helper {#ᵀ n} {_} {i} j≥i si≻A i≻B k with i ≟ℕ n
      ... | yes refl = i≻B k ⦃ ≤-trans j≥i it ⦄
      ... | no  i≢n  with k ≟ℕ n
      ...   | no  _    = И⟨ [] , (λ _ → refl) ⟩
      ...   | yes refl with si≻A n ⦃ ≤∧≢⇒< (≤-trans j≥i it) i≢n ⦄
      ...     | И⟨ Иe₁ , Иe₂ ⟩ with n ≟ℕ n
      ...       | yes refl with () ← Иe₂ (fresh Иe₁) {fresh-correct Иe₁}
      ...       | no  n≢n =  contradiction refl n≢n
      helper {A ⇒ C} j≥i si≻A⇒C i≻B k =
        let ⟨ si≻A , si≻C ⟩ = ⇒-≻ si≻A⇒C
            И⟨ A-Иe₁ , A-Иe₂ ⟩ = (helper j≥i si≻A i≻B) k
            И⟨ C-Иe₁ , C-Иe₂ ⟩ = (helper j≥i si≻C i≻B) k
        in И⟨ A-Иe₁ ++ C-Иe₁ , (λ a {a∉} → cong₂ _⇒_
          (A-Иe₂ a {proj₁ (∉-++ a∉)})
          (C-Иe₂ a {proj₂ (∉-++ {xs = A-Иe₁} a∉)})) ⟩
      helper {∀ᵀ A} {B} {i} j≥i si≻∀A i≻B k =
        let ssi≻A = i≻∀A⇒si≻A si≻∀A
            И⟨ Иe₁ , Иe₂ ⟩ = (helper (s≤s j≥i) ssi≻A si≻B) (suc k) ⦃ s≤s it ⦄
        in И⟨ Иe₁ , (λ a {a∉} → cong ∀ᵀ_ (Иe₂ a {a∉})) ⟩
        where
          si≻B : suc i ≻ty B
          si≻B = lemma2·6-ty (n≤1+n i) i≻B
  ⊢⇒lc-ty {Γ} {‵zero} (⊢zero _) = n≻‵ℕ
  ⊢⇒lc-ty {Γ} {‵suc L} (⊢suc ⊢L) = n≻‵ℕ

  ⊢⇒lc-ty-tm : ∀ {Γ L A} → Γ ⊢ L ⦂ A → Ty-Tm-LocallyClosed L
  ⊢⇒lc-ty-tm (⊢free okΓ lc-A ∋x) j = И⟨ [] , (λ _ → refl) ⟩
  ⊢⇒lc-ty-tm (⊢ƛ lc-A И⟨ B-Иe₁ , B-Иe₂ ⟩) j =
    let И⟨ A-Иe₁ , A-Иe₂ ⟩ = lc-A j
        И⟨ Иe₁ , Иe₂ ⟩ = (⊢⇒lc-ty-tm (B-Иe₂ #-B-Иe₁ {#-B-Иe₁-✓})) j
    in И⟨ Иe₁ ++ A-Иe₁ , (λ a {a∉} → cong ƛ_
      (open-rec-lc-lemma-ty-tm-tm-tm
        (Иe₂ a {proj₁ (∉-++ a∉)}))) ⟩
    where
      #-B-Иe₁ : Id
      #-B-Иe₁ = fresh B-Иe₁
      #-B-Иe₁-✓ : #-B-Иe₁ ∉ B-Иe₁
      #-B-Иe₁-✓ = fresh-correct B-Иe₁
  ⊢⇒lc-ty-tm {Γ} (⊢· ⊢L ⊢M) j = И⟨ [] , (λ a → cong₂ _·_
    (lemma2·7-2-ty-tm it (⊢⇒lc-ty-tm ⊢L))
    (lemma2·7-2-ty-tm it (⊢⇒lc-ty-tm ⊢M))) ⟩
  ⊢⇒lc-ty-tm {Γ} {Λ L} (⊢Λ И⟨ Иe₁ , Иe₂ ⟩) j =
      let induc-hypo = ⊢⇒lc-ty-tm (Иe₂ (fresh Иe₁) {fresh-correct Иe₁})
          sj≻ = lemma2·6-ty-tm z≤n induc-hypo
          И⟨ L-Иe₁ , L-Иe₂ ⟩ = (helper L z≤n sj≻) (suc j) ⦃ s≤s it ⦄
      in И⟨ L-Иe₁ , (λ a {a∉} → cong Λ_ (L-Иe₂ a {a∉})) ⟩
    where
      helper : ∀ {i x j} (L : Term)
        → j ≥ i
        → (suc i) ≻ty-tm (ty-tm[ i —→ x ] L)
        → (suc j) ≻ty-tm L
      helper L j≥i si≻[]L k =
        let И⟨ Иe₁ , Иe₂ ⟩ = si≻[]L k ⦃ ≤-trans (s≤s j≥i) it ⦄
            k≢i = sym-≢ (<⇒≢ (≤-trans (s≤s j≥i) it))
        in И⟨ Иe₁ , (λ a {a∉} →
          open-rec-lc-lemma-ty-tm k≢i (Иe₂ a {a∉})) ⟩
  ⊢⇒lc-ty-tm {Γ} (⊢[] lc _ ⊢L) j =
    И⟨ [] , (λ a → cong₂ _[_]
      (lemma2·7-2-ty-tm it (⊢⇒lc-ty-tm ⊢L))
      (lemma2·7-2-ty it lc)) ⟩
  ⊢⇒lc-ty-tm (⊢zero _) j = И⟨ [] , (λ _ → refl) ⟩
  ⊢⇒lc-ty-tm {Γ} (⊢suc ⊢L) j = И⟨ [] , (λ a →
    cong ‵suc_ (lemma2·7-2-ty-tm it (⊢⇒lc-ty-tm ⊢L))) ⟩

  extract-subst : ∀ {X C A i j}
    (B : Type)
    → j ≥ i
    → i ≻ty C
    → ty-ty[ j :→ ty-ty[ X := C ] A ] (ty-ty[ X := C ] B)
        ≡ ty-ty[ X := C ] (ty-ty[ j :→ A ] B)
  extract-subst ‵ℕ j≥i i≻C = refl
  extract-subst {X} {C} (frᵀ Y) j≥i i≻C with X ≟lchar Y
  ... | yes refl = ≻⇒:→-invariant C j≥i i≻C
  ... | no  X≢Y  = refl
  extract-subst {i = i} {j = j} (#ᵀ n) j≥i i≻C with j ≟ℕ n
  ... | yes refl = refl
  ... | no  j≢n  = refl
  extract-subst (B ⇒ B') j≥i i≻C = cong₂ _⇒_
    (extract-subst B j≥i i≻C) (extract-subst B' j≥i i≻C)
  extract-subst (∀ᵀ B) j≥i i≻C =
    cong ∀ᵀ_ (extract-subst B (m≤n⇒m≤1+n j≥i) i≻C)

  extract-subst-ctx : ∀ {Γ L X C B A i j}
    → j ≥ i
    → i ≻ty C
    → Γ ⊢ L ⦂ ty-ty[ j :→ ty-ty[ X := C ] A ] (ty-ty[ X := C ] B)
    → Γ ⊢ L ⦂ ty-ty[ X := C ] (ty-ty[ j :→ A ] B)
  extract-subst-ctx {B = B} j≥i i≻C assump =
    ≡-with-⊢-ty assump (extract-subst B j≥i i≻C)

  subst-ty : ∀ {Γ Δ X L B C}
    → Ty-LocallyClosed C
    → ftv-ty C ⊆ domain-ftv Δ
    → Ok (Γ + (map (ty-ty[ X := C ]_) Δ))
    → ((Γ , X) + Δ) ⊢ L ⦂ B
      --------------------
    → (Γ + (map (ty-ty[ X := C ]_) Δ))
        ⊢ ty-tm[ X := C ] L ⦂ ty-ty[ X := C ] B
  subst-ty {Γ} {Δ} {X} lc-C C⊆Δ okΓ+map (⊢free okΓ+Δ lc-B ∋x)
    with ok-+ {Γ = Γ , X} okΓ+Δ
  ... | ok-∷ftv okΓ X∉Γ =
    ⊢free okΓ+map (:=-≻ z≤n lc-B lc-C) (∋-map-ftv Δ okΓ+Δ ∋x)
  subst-ty lc-C C⊆Δ okΓ+map (⊢· ⊢L ⊢M) = ⊢·
    (subst-ty lc-C C⊆Δ okΓ+map ⊢L)
    (subst-ty lc-C C⊆Δ okΓ+map ⊢M)
  subst-ty {Γ} {Δ} {X} {B = ∀ᵀ B} {C = C}
      lc-C C⊆Δ okΓ+map (⊢Λ И⟨ Иe₁ , Иe₂ ⟩) =
    ⊢Λ
      И⟨ (X ∷ Иe₁) ++ domain-all-ftv (Γ + map (ty-ty[_:=_]_ X C) Δ)
      , (λ a {a∉} →
        let ⟨ a∉X∷Иe₁ , a∉dom-all-ftv ⟩ = ∉-++ a∉
            ⟨ a∉X∷[] , a∉Иe₁ ⟩ = ∉-++ a∉X∷Иe₁
            X≢a = sym-≢ (∉∷[]⇒≢ a∉X∷[])
            hypo = subst-ty {Δ = Δ , a} lc-C (⊆⇒⊆∷ C⊆Δ)
                (ok-∷ftv okΓ+map a∉dom-all-ftv) (Иe₂ a {a∉Иe₁})
        in subst-open-ty-tm-ty-tm-ctx X≢a z≤n lc-C
          (subst-open-ty-ty-ty-ty-ctx {A = B} {j = 0} X≢a z≤n lc-C hypo) ) ⟩
  subst-ty {Γ} {Δ} {L = ƛ L}
      lc-C C⊆Δ okΓ+map (⊢ƛ {A = A} lc-A И⟨ Иe₁ , Иe₂ ⟩) =
    ⊢ƛ (:=-≻ z≤n lc-A lc-C) И⟨ Иe₁ , (λ a {a∉} →
      let ⊢tm-tm[0→]L = Иe₂ a {a∉}
          ok = ⊢⇒Ok ⊢tm-tm[0→]L
      in subst-open-ty-tm-tm-tm-ctx L z≤n lc-C
        (subst-ty lc-C C⊆Δ (ok-∷fv
            okΓ+map
            (:=-≻ z≤n lc-A lc-C)
            (ftv⊆dom-:= {A = A} Γ Δ lc-C C⊆Δ okΓ+map (extract-⊆ ok)))
          ⊢tm-tm[0→]L)) ⟩
  subst-ty {Γ} {Δ} {X = Y} {L = L [ A ]} {B = D}
      lc-C C⊆Δ okΓ+map (⊢[] {B = B} lc-A A⊆ ⊢L)
    = extract-subst-ctx {X = Y} {B = B} {A = A} {j = 0} z≤n lc-C
      (⊢[]
        (:=-≻ {X = Y} z≤n lc-A lc-C)
        (ftv⊆dom-:= {A = A} Γ Δ lc-C C⊆Δ okΓ+map A⊆)
        (subst-ty lc-C C⊆Δ okΓ+map ⊢L))
  subst-ty lc-C C⊆Δ okΓ+map (⊢zero okΓ+Δ) = ⊢zero okΓ+map
  subst-ty lc-C C⊆Δ okΓ+map (⊢suc ⊢L) =
    ⊢suc (subst-ty lc-C C⊆Δ okΓ+map ⊢L)

  {-# TERMINATING #-}
  subst : ∀ {Γ x L N A B}
    → ∅ ⊢ N ⦂ A
    → Γ , x ⦂ A ⊢ L ⦂ B
      -----------------------
    → Γ ⊢ tm-tm[ x := N ] L ⦂ B
  subst {x = y} ⊢N (⊢free (ok-∷fv okΓ _ A⊆Γ) lc-A (H refl))
    with y ≟lchar y
  ... | yes refl = weaken okΓ ⊢N
  ... | no  y≢y  = contradiction refl y≢y
  subst {x = y} ⊢N (⊢free {x = x} (ok-∷fv okΓ _ A⊆Γ) lc-A (T x≢y ∋x))
    with y ≟lchar x
  ... | yes refl = contradiction refl x≢y
  ... | no  _    = ⊢free okΓ lc-A ∋x
  subst {x = y} {L = ƛ L} ⊢N (⊢ƛ lc-A И⟨ Иe₁ , Иe₂ ⟩) =
    ⊢ƛ lc-A И⟨ (y ∷ Иe₁) , (λ a {a∉} →
      let a∉Иe₁ = proj₂ (∉-++ {xs = y ∷ []} a∉)
          y≢a = sym-≢ (∉y∷ys⇒≢y a∉)
          ⊢tm-tm[]L = swap (sym-≢ y≢a) (Иe₂ a {a∉Иe₁})
      in subst-open-ctx L y≢a (⊢⇒lc ⊢N) (subst ⊢N ⊢tm-tm[]L)) ⟩
  subst ⊢N (⊢· ⊢L ⊢M) = ⊢· (subst ⊢N ⊢L) (subst ⊢N ⊢M)
  subst {x = y} {L = Λ L} ⊢N (⊢Λ И⟨ Иe₁ , Иe₂ ⟩) =
    ⊢Λ И⟨ y ∷ Иe₁ , (λ A {A∉} →
      let A∉Иe₁ = proj₂ (∉-++ {xs = y ∷ []} A∉)
          y≢A = sym-≢ (∉y∷ys⇒≢y A∉)
          ⊢ty-tm[]L = Иe₂ A {A∉Иe₁}
          induc-hypo = subst ⊢N (swap-tm-ty ⊢ty-tm[]L)
      in subst-open-ty-tm-ctx L y≢A z≤n (⊢⇒lc-ty-tm ⊢N) induc-hypo ) ⟩
  subst ⊢N (⊢[] lc ⊆[] ⊢L) = ⊢[] lc ⊆[] (subst ⊢N ⊢L)
  subst ⊢N (⊢zero (ok-∷fv okΓ _ _)) = ⊢zero okΓ
  subst ⊢N (⊢suc ⊢L) = ⊢suc (subst ⊢N ⊢L)

  subst-op : ∀ {Γ L N A B}
    → ∅ ⊢ N ⦂ A
    → Γ ⊢ ƛ L ⦂ A ⇒ B
      -----------------------
    → Γ ⊢ tm-tm[ 0 :→ N ] L ⦂ B
  subst-op {Γ} {L} {N} ⊢N (⊢ƛ lc-A И⟨ Иe₁ , Иe₂ ⟩) =
    let x                  = fresh (fv-tm L ++ Иe₁)
        ⟨ x∉fv-L , x∉Иe₁ ⟩ = ∉-++ {xs = fv-tm L}
                                (fresh-correct (fv-tm L ++ Иe₁))
    in ≡-with-⊢-tm (subst ⊢N (Иe₂ x {x∉Иe₁}))
      (sym (subst-intro L N (x∉fv-L)))

  subst-op-ty : ∀ {L B C}
    → Ty-LocallyClosed C
    → ftv-ty C ⊆ []
    → ∅ ⊢ Λ L ⦂ ∀ᵀ B
      -----------------------------
    → ∅ ⊢ ty-tm[ 0 :→ C ] L ⦂ ty-ty[ 0 :→ C ] B
  subst-op-ty {L} {B} {C} lc-C C⊆[] (⊢Λ И⟨ Иe₁ , Иe₂ ⟩) =
    let x = fresh (fv-tm L ++ ftv-ty B ++ ftv-tm L ++ Иe₁)
        ⟨ x∉fv-L , x∉ ⟩ = ∉-++ {xs = fv-tm L}
          (fresh-correct (fv-tm L ++ ftv-ty B ++ ftv-tm L ++ Иe₁))
        ⟨ x∉ftv-B , x∉ ⟩ = ∉-++ {xs = ftv-ty B} x∉
        ⟨ x∉ftv-L , x∉Иe₁ ⟩ = ∉-++ {xs = ftv-tm L} x∉
    in ≡-with-⊢-ty (≡-with-⊢-tm
          (subst-ty {Δ = ∅} lc-C C⊆[] ok-∅ (Иe₂ x {x∉Иe₁}))
          (sym (subst-intro-ty-tm L x∉ftv-L)))
      (sym (subst-intro-ty-ty B x∉ftv-B))

  data Value : Term → Set where
    V-ƛ : ∀ {L} → Value (ƛ L)
    V-Λ : ∀ {L} → Value (Λ L)
    V-zero : Value ‵zero
    V-suc : ∀ {L} → Value L → Value (‵suc L)

  infix 4 _—→_
  data _—→_ : Term → Term → Set where
    ξ₁ : ∀ {L L' M}
      → L —→ L'
        -------------------
      → L · M —→ L' · M

    ξ₂ : ∀ {L M M'}
      → M —→ M'
        ---------
      → L · M —→ L · M'

    ξ-[] : ∀ {L L' A}
      → L —→ L'
        ------------------
      → L [ A ] —→ L' [ A ]

    ξ-suc : ∀ {L L'}
      → L —→ L'
        ------------------
      → ‵suc L —→ ‵suc L'

    β-ƛ : ∀ {L M}
      → 1 ≻tm L              → Value M
        ------------------------------
      → (ƛ L) · M —→ tm-tm[ 0 :→ M ] L

    β-Λ : ∀ {L A}
      → 1 ≻ty-tm L  → Ty-LocallyClosed A
      → ftv-ty A ⊆ []
        --------------------------------
      → (Λ L) [ A ] —→ ty-tm[ 0 :→ A ] L

  data _—↠_ : Term → Term → Set where
    _∎' : ∀ M → M —↠ M
    step—→ : ∀ L {M N} → M —↠ N → L —→ M → L —↠ N
  pattern _—→⟨_⟩_ L L—→M M—↠N = step—→ L M—↠N L—→M

  begin'_ : ∀ {M N} → M —↠ N → M —↠ N
  begin' M—↠N = M—↠N

  data Progress (L : Term) : Set where
    done : Value L → Progress L
    step : ∀ {L'} → L —→ L' → Progress L

  progress : ∀ {L A} → ∅ ⊢ L ⦂ A → Progress L
  progress (⊢ƛ lc-A cof) = done V-ƛ
  progress (⊢· ⊢L ⊢M) with progress ⊢L
  ... | step L→L' = step (ξ₁ L→L')
  ... | done V-ƛ with progress ⊢M
  ...   | step M→M' = step (ξ₂ M→M')
  ...   | done val  = step (β-ƛ (≻ƛ⇒s≻ƛ (⊢⇒lc ⊢L)) val)
  progress (⊢Λ x) = done V-Λ
  progress (⊢[] lc-A A⊆[] ⊢L) with progress ⊢L
  ... | step L→L' = step (ξ-[] L→L')
  ... | done V-Λ = step (β-Λ (≻Λ⇒s≻Λ (⊢⇒lc-ty-tm ⊢L)) lc-A A⊆[])
  progress (⊢zero ok-∅) = done V-zero
  progress (⊢suc ⊢L) with progress ⊢L
  ... | step L→L'  = step (ξ-suc L→L')
  ... | done val-L = done (V-suc val-L)

  preserve : ∀ {L L' A} → ∅ ⊢ L ⦂ A → L —→ L' → ∅ ⊢ L' ⦂ A
  preserve (⊢· ⊢L ⊢M) (ξ₁ L→L') = ⊢· (preserve ⊢L L→L') ⊢M
  preserve (⊢· ⊢L ⊢M) (ξ₂ M→M') = ⊢· ⊢L (preserve ⊢M M→M')
  preserve (⊢· ⊢L ⊢M) (β-ƛ 1≻L val-M) = subst-op ⊢M ⊢L
  preserve (⊢[] lc-A A⊆[] ⊢L) (ξ-[] L→L') =
    ⊢[] lc-A A⊆[] (preserve ⊢L L→L')
  preserve (⊢[] lc-A A⊆[] ⊢L) (β-Λ 1≻L _ C⊆[]) =
    subst-op-ty lc-A C⊆[] ⊢L
  preserve (⊢suc ⊢L) (ξ-suc L→L') = ⊢suc (preserve ⊢L L→L')

  record Gas : Set where
    pattern
    constructor gas
    field
      amount : ℕ

  data Finished (N : Term) : Set where
    out-of-gas : Finished N
    done : Value N → Finished N

  data Steps (L : Term) : Set where
    steps : ∀ {N} → L —↠ N → Finished N → Steps L

  eval : ∀ {L A} → Gas → ∅ ⊢ L ⦂ A → Steps L
  eval {L} (gas zero) ⊢L = steps (L ∎') out-of-gas
  eval {L} (gas (suc n)) ⊢L with progress ⊢L
  ... | done val = steps (L ∎') (done val)
  ... | step {M} L→M with eval (gas n) (preserve ⊢L L→M)
  ...   | steps M→N fin = steps (L —→⟨ L→M ⟩ M→N) fin

  ⊢twice-suc-zero :
    ∅ ⊢ (((Λ ƛ (ƛ ((# 1) · ((# 1) · (# 0))))) [ ‵ℕ ])
          · (ƛ ‵suc (# 0))) · ‵zero
        ⦂ ‵ℕ
  ⊢twice-suc-zero = ⊢·
    (⊢· (⊢[] n≻‵ℕ All.[] twice)
      (⊢ƛ n≻‵ℕ И⟨ [] , (λ a →
        ⊢suc (⊢free (ok-∷fv ok-∅ n≻‵ℕ All.[]) n≻‵ℕ H′)) ⟩))
    (⊢zero ok-∅)

  _≻'ty_ : ℕ → Type → Set
  i ≻'ty A = (j : ℕ) ⦃ _ : j ≥ i ⦄ → ∃[ T ] (ty-ty[ j —→ T ] A ≡ A)

  ≻ty⇒≻'ty : ∀ (i : ℕ) (A : Type)
    → i ≻ty A → i ≻'ty A
  ≻ty⇒≻'ty i A i≻tyA j =
    let И⟨ Иe₁ , Иe₂ ⟩ = i≻tyA j
    in ⟨ (fresh Иe₁) , Иe₂ (fresh Иe₁) {fresh-correct Иe₁} ⟩
  ≻'ty⇒≻ty : ∀ (i : ℕ) (A : Type)
    → i ≻'ty A → i ≻ty A
  ≻'ty⇒≻ty i ‵ℕ i≻'tyA = n≻‵ℕ
  ≻'ty⇒≻ty i (frᵀ X) i≻'tyA j = И⟨ [] , (λ _ → refl) ⟩
  ≻'ty⇒≻ty i (#ᵀ k) i≻'tyA j with j ≟ℕ k
  ... | no  j≢k  = И⟨ [] , (λ _ → refl) ⟩
  ... | yes refl with i≻'tyA j
  ...   | ⟨ X , op-invariant ⟩ with k ≟ℕ k
  ...     | yes refl with () ← op-invariant
  ...     | no  k≢k  = contradiction refl k≢k
  ≻'ty⇒≻ty i (A ⇒ B) i≻'ty j =
    let И⟨ A-Иe₁ , A-Иe₂ ⟩ = (≻'ty⇒≻ty i A i≻'tyA) j
        И⟨ B-Иe₁ , B-Иe₂ ⟩ = (≻'ty⇒≻ty i B i≻'tyB) j
    in И⟨ A-Иe₁ ++ B-Иe₁ , (λ X {X∉} →
      let ⟨ X∉A , X∉B ⟩ = ∉-++ X∉
      in cong₂ _⇒_ (A-Иe₂ X {X∉A}) (B-Иe₂ X {X∉B})) ⟩
    where
      i≻'tyA : i ≻'ty A
      i≻'tyA j = let ⟨ X , op-invariant ⟩ = i≻'ty j
        in ⟨ X , proj₁ (⇒-inj op-invariant) ⟩
      i≻'tyB : i ≻'ty B
      i≻'tyB j = let ⟨ X , op-invariant ⟩ = i≻'ty j
        in ⟨ X , proj₂ (⇒-inj op-invariant) ⟩
  ≻'ty⇒≻ty i (∀ᵀ A) i≻'ty j =
    let И⟨ Иe₁ , Иe₂ ⟩ = induc-hypo (suc j) ⦃ s≤s it ⦄
    in И⟨ Иe₁ , (λ X {X∉} → (cong ∀ᵀ_ (Иe₂ X {X∉}))) ⟩
    where
      si≻'tyA : (suc i) ≻'ty A
      si≻'tyA (suc j) =
        let ⟨ X , op-invariant ⟩ = i≻'ty j ⦃ ≤-pred it ⦄
        in ⟨ X , ∀-inj op-invariant ⟩
      induc-hypo : (suc i) ≻ty A
      induc-hypo = ≻'ty⇒≻ty (suc i) A si≻'tyA

  _≻'tm_ : ℕ → Term → Set
  i ≻'tm L = (j : ℕ) ⦃ _ : j ≥ i ⦄ → ∃[ T ] (tm-tm[ j —→ T ] L ≡ L)

  ≻tm⇒≻'tm : ∀ (i : ℕ) (L : Term)
    → i ≻tm L → i ≻'tm L
  ≻tm⇒≻'tm i L i≻tmA j = let И⟨ Иe₁ , Иe₂ ⟩ = i≻tmA j
    in ⟨ (fresh Иe₁) , Иe₂ (fresh Иe₁) {fresh-correct Иe₁} ⟩

  ≻'tm⇒≻tm : ∀ (i : ℕ) (L : Term)
    → i ≻'tm L → i ≻tm L
  ≻'tm⇒≻tm i (fr x) i≻'L j = И⟨ [] , (λ _ → refl) ⟩
  ≻'tm⇒≻tm i (# k) i≻'L j with j ≟ℕ k
  ... | no  _    = И⟨ [] , (λ _ → refl) ⟩
  ... | yes refl with i≻'L j
  ...   | ⟨ X , op-invariant ⟩ with k ≟ℕ k
  ...     | yes refl with () ← op-invariant
  ...     | no  k≢k = contradiction refl k≢k
  ≻'tm⇒≻tm i (ƛ L) i≻' j =
    let И⟨ Иe₁ , Иe₂ ⟩ = induc-hypo (suc j) ⦃ s≤s it ⦄
    in И⟨ Иe₁ , (λ a {a∉} → cong ƛ_ (Иe₂ a {a∉})) ⟩
    where
      si≻'L : (suc i) ≻'tm L
      si≻'L (suc j) =
        let ⟨ X , op-invariant ⟩ = i≻' j ⦃ ≤-pred it ⦄
        in ⟨ X , ƛ-inj op-invariant ⟩
      induc-hypo : (suc i) ≻tm L
      induc-hypo = ≻'tm⇒≻tm (suc i) L si≻'L
  ≻'tm⇒≻tm i (L · M) i≻' j =
    let И⟨ L-Иe₁ , L-Иe₂ ⟩ = (≻'tm⇒≻tm i L i≻'L) j
        И⟨ M-Иe₁ , M-Иe₂ ⟩ = (≻'tm⇒≻tm i M i≻'M) j
    in И⟨ L-Иe₁ ++ M-Иe₁ , (λ a {a∉} →
      let ⟨ a∉L , a∉M ⟩ = ∉-++ a∉
      in cong₂ _·_ (L-Иe₂ a {a∉L}) (M-Иe₂ a {a∉M})) ⟩
    where
      i≻'L : i ≻'tm L
      i≻'L j = let ⟨ x , op-invariant ⟩ = i≻' j
        in ⟨ x , proj₁ (·-inj op-invariant) ⟩
      i≻'M : i ≻'tm M
      i≻'M j = let ⟨ x , op-invariant ⟩ = i≻' j
        in ⟨ x , proj₂ (·-inj op-invariant) ⟩
  ≻'tm⇒≻tm i (Λ L) i≻' j =
    let И⟨ Иe₁ , Иe₂ ⟩ = induc-hypo j
    in И⟨ Иe₁ , (λ a {a∉} → cong Λ_ (Иe₂ a {a∉})) ⟩
    where
      i≻'L : i ≻'tm L
      i≻'L j =
        let ⟨ X , op-invariant ⟩ = i≻' j
        in ⟨ X , Λ-inj op-invariant ⟩
      induc-hypo : i ≻tm L
      induc-hypo = ≻'tm⇒≻tm i L i≻'L
  ≻'tm⇒≻tm i (L [ A ]) i≻' j =
    let И⟨ Иe₁ , Иe₂ ⟩ = induc-hypo j
    in И⟨ Иe₁ , (λ a {a∉} → cong _[ A ] (Иe₂ a {a∉})) ⟩
    where
      i≻'L : i ≻'tm L
      i≻'L j =
        let ⟨ X , op-invariant ⟩ = i≻' j
        in ⟨ X , proj₁ ([]-inj op-invariant) ⟩
      induc-hypo : i ≻tm L
      induc-hypo = ≻'tm⇒≻tm i L i≻'L
  ≻'tm⇒≻tm i ‵zero i≻' j = И⟨ [] , (λ _ → refl) ⟩
  ≻'tm⇒≻tm i (‵suc L) i≻' j =
    let И⟨ Иe₁ , Иe₂ ⟩ = induc-hypo j
    in И⟨ Иe₁ , (λ a {a∉} → cong ‵suc_ (Иe₂ a {a∉})) ⟩
    where
      i≻'L : i ≻'tm L
      i≻'L j =
        let ⟨ X , op-invariant ⟩ = i≻' j
        in ⟨ X , ‵suc-inj op-invariant ⟩
      induc-hypo : i ≻tm L
      induc-hypo = ≻'tm⇒≻tm i L i≻'L

  _≻'ty-tm_ : ℕ → Term → Set
  i ≻'ty-tm L = (j : ℕ) ⦃ _ : j ≥ i ⦄ → ∃[ a ] (ty-tm[ j —→ a ] L ≡ L)

  ≻ty-tm⇒≻'ty-tm : ∀ (i : ℕ) (L : Term)
    → i ≻ty-tm L → i ≻'ty-tm L
  ≻ty-tm⇒≻'ty-tm i L i≻L j =
    let И⟨ Иe₁ , Иe₂ ⟩ = i≻L j
    in ⟨ (fresh Иe₁) , Иe₂ (fresh Иe₁) {fresh-correct Иe₁} ⟩

  ≻'ty-tm⇒≻ty-tm : ∀ (i : ℕ) (L : Term)
    → i ≻'ty-tm L → i ≻ty-tm L
  ≻'ty-tm⇒≻ty-tm i (fr x) i≻'L j = И⟨ [] , (λ _ → refl) ⟩
  ≻'ty-tm⇒≻ty-tm i (# k) i≻'L j = И⟨ [] , (λ _ → refl) ⟩
  ≻'ty-tm⇒≻ty-tm i (ƛ L) i≻' j =
    let И⟨ Иe₁ , Иe₂ ⟩ = induc-hypo j
    in И⟨ Иe₁ , (λ a {a∉} → cong ƛ_ (Иe₂ a {a∉})) ⟩
    where
      i≻'L : i ≻'ty-tm L
      i≻'L j =
        let ⟨ X , op-invariant ⟩ = i≻' j
        in ⟨ X , ƛ-inj op-invariant ⟩
      induc-hypo : i ≻ty-tm L
      induc-hypo = ≻'ty-tm⇒≻ty-tm i L i≻'L
  ≻'ty-tm⇒≻ty-tm i (L · M) i≻' j =
    let И⟨ L-Иe₁ , L-Иe₂ ⟩ = (≻'ty-tm⇒≻ty-tm i L i≻'L) j
        И⟨ M-Иe₁ , M-Иe₂ ⟩ = (≻'ty-tm⇒≻ty-tm i M i≻'M) j
    in И⟨ L-Иe₁ ++ M-Иe₁ , (λ a {a∉} →
      let ⟨ a∉L , a∉M ⟩ = ∉-++ a∉
      in cong₂ _·_ (L-Иe₂ a {a∉L}) (M-Иe₂ a {a∉M})) ⟩
    where
      i≻'L : i ≻'ty-tm L
      i≻'L j = let ⟨ x , op-invariant ⟩ = i≻' j
        in ⟨ x , proj₁ (·-inj op-invariant) ⟩
      i≻'M : i ≻'ty-tm M
      i≻'M j = let ⟨ x , op-invariant ⟩ = i≻' j
        in ⟨ x , proj₂ (·-inj op-invariant) ⟩
  ≻'ty-tm⇒≻ty-tm i (Λ L) i≻' j =
    let И⟨ Иe₁ , Иe₂ ⟩ = induc-hypo (suc j) ⦃ s≤s it ⦄
    in И⟨ Иe₁ , (λ a {a∉} → cong Λ_ (Иe₂ a {a∉})) ⟩
    where
      si≻'L : (suc i) ≻'ty-tm L
      si≻'L (suc j) =
        let ⟨ X , op-invariant ⟩ = i≻' j ⦃ ≤-pred it ⦄
        in ⟨ X , Λ-inj op-invariant ⟩
      induc-hypo : (suc i) ≻ty-tm L
      induc-hypo = ≻'ty-tm⇒≻ty-tm (suc i) L si≻'L
  ≻'ty-tm⇒≻ty-tm i (L [ A ]) i≻' j =
    let И⟨ L-Иe₁ , L-Иe₂ ⟩ = L-induc-hypo j
        И⟨ A-Иe₁ , A-Иe₂ ⟩ = A-induc-hypo j
    in И⟨ L-Иe₁ ++ A-Иe₁ , (λ a {a∉} →
      let ⟨ a∉L , a∉A ⟩ = ∉-++ a∉
      in cong₂ _[_] (L-Иe₂ a {a∉L}) (A-Иe₂ a {a∉A}))⟩
    where
      i≻'L : i ≻'ty-tm L
      i≻'L j =
        let ⟨ X , op-invariant ⟩ = i≻' j
        in ⟨ X , proj₁ ([]-inj op-invariant) ⟩
      L-induc-hypo : i ≻ty-tm L
      L-induc-hypo = ≻'ty-tm⇒≻ty-tm i L i≻'L
      i≻'A : i ≻'ty A
      i≻'A j =
        let ⟨ X , op-invariant ⟩ = i≻' j
        in ⟨ X , proj₂ ([]-inj op-invariant) ⟩
      A-induc-hypo : i ≻ty A
      A-induc-hypo = ≻'ty⇒≻ty i A i≻'A
  ≻'ty-tm⇒≻ty-tm i ‵zero i≻' j = И⟨ [] , (λ _ → refl) ⟩
  ≻'ty-tm⇒≻ty-tm i (‵suc L) i≻' j =
    let И⟨ Иe₁ , Иe₂ ⟩ = induc-hypo j
    in И⟨ Иe₁ , (λ a {a∉} → cong ‵suc_ (Иe₂ a {a∉})) ⟩
    where
      i≻'L : i ≻'ty-tm L
      i≻'L j =
        let ⟨ X , op-invariant ⟩ = i≻' j
        in ⟨ X , ‵suc-inj op-invariant ⟩
      induc-hypo : i ≻ty-tm L
      induc-hypo = ≻'ty-tm⇒≻ty-tm i L i≻'L
