module stlc where

-- Data types (naturals, strings, characters)
open import Data.Nat using (ℕ; zero; suc; _<_; _≥_; _≤_; _≤?_; _<?_; z≤n; s≤s; _⊔_)
  renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-<-trans; <-≤-trans; ≤-antisym; ≤-total;
  +-mono-≤; n≤1+n; m≤n⇒m≤1+n; suc-injective; <⇒≢; ≰⇒>; ≮⇒≥)
open import Data.String using (String; fromList) renaming (_≟_ to _≟str_; _++_ to _++str_;
  length to str-length; toList to ⟪_⟫)
open import Data.Char using (Char)
open import Data.Char.Properties using () renaming (_≟_ to _≟char_)

-- Function manipulation.
open import Function using (_∘_; flip; it; id; case_returning_of_)

-- Relations and predicates/decidability.
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong-app; cong₂)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable using (Dec; yes; no; True; False; toWitnessFalse;
  toWitness; fromWitness; ¬?; ⌊_⌋; From-yes)
open import Relation.Unary using (Decidable)
open import Relation.Binary using () renaming (Decidable to BinaryDecidable)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Data.Empty using (⊥-elim)

-- Products and exists quantifier.
open import Data.Product using (_×_; proj₁; proj₂; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- Lists.
open import Data.List using (List; []; _∷_; _++_; length; filter; map; foldr; head; replicate)
open import Data.List.Properties using (≡-dec)
import Data.List.Membership.DecPropositional as DecPropMembership
open import Data.List.Relation.Unary.All using (All; all?; lookup)
  renaming (fromList to All-fromList; toList to All-toList)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Extrema Data.Nat.Properties.≤-totalOrder using (max; xs≤max)

-- Import list membership using List Char comparisons.
private
  _≟lchar_ : ∀ (xs ys : List Char) → Dec (xs ≡ ys)
  xs ≟lchar ys = ≡-dec (_≟char_) xs ys

open DecPropMembership _≟lchar_ using (_∈_; _∉_; _∈?_)

open import plfa_adaptions
open import tspl_prior_work
open import cofinite

⊢⇒lc : ∀ {Γ t A} → Γ ⊢ t ⦂ A → LocallyClosed t
⊢⇒lc {Γ} {t} {A} (⊢free Γ∋A) = free-lc
⊢⇒lc {Γ} {ƛ t} {A} (⊢ƛ И⟨ Иe₁ , Иe₂ ⟩) j =
  И⟨ Иe₁ , (λ a {a∉} → cong ƛ_
    (open-rec-lc-lemma
      (λ ())
      (open-rec-lc (⊢⇒lc (Иe₂ a {a∉}))))) ⟩
⊢⇒lc {Γ} {t₁ · t₂} (⊢· ⊢A⇒B ⊢A) _ =
  И⟨ domain Γ , (λ _ → cong₂ _·_
    (open-rec-lc (⊢⇒lc ⊢A⇒B)) (open-rec-lc (⊢⇒lc ⊢A))) ⟩
⊢⇒lc {Γ} {‵zero} ⊢zero = ‵zero-≻
⊢⇒lc {Γ} {‵suc t} (⊢suc ⊢t) j =
  И⟨ domain Γ , (λ a {a∉} →
    cong ‵suc_ (open-rec-lc (⊢⇒lc ⊢t))) ⟩

{-# TERMINATING #-}
subst : ∀ {Γ x t u A B}
  → ∅ ⊢ u ⦂ A
  → Γ , x ⦂ A ⊢ t ⦂ B
    --------------------
  → Γ ⊢ [ x := u ] t ⦂ B
subst {x = y} ⊢u (⊢free {x = x} (H refl)) with y ≟lchar y
... | yes _   = weaken ⊢u
... | no  y≢y = contradiction refl y≢y
subst {x = y} ⊢u (⊢free {x = x} (T x≢y ∋x)) with y ≟lchar x
... | yes y≡x = contradiction (sym y≡x) x≢y
... | no  _   = ⊢free ∋x
subst {x = x} {t = ƛ t} ⊢u (⊢ƛ И⟨ Иe₁ , Иe₂ ⟩) =
  ⊢ƛ И⟨ x ∷ Иe₁
      , (λ a {a∉} →
        let a≢y   = ∉∷[]⇒≢ (proj₁ (∉-++ a∉))
            a∉Иe₁ = proj₂ (∉-++ a∉)
        in subst-open-context
          {t = t}
          (sym-≢ a≢y)
          (⊢⇒lc ⊢u)
          (subst ⊢u (swap a≢y (Иe₂ a {a∉Иe₁}))) )
      ⟩
subst ⊢u (⊢· ⊢t₁ ⊢t₂) = ⊢· (subst ⊢u ⊢t₁) (subst ⊢u ⊢t₂)
subst ⊢u ⊢zero = ⊢zero
subst ⊢u (⊢suc ⊢t) = ⊢suc (subst ⊢u ⊢t)

[_:→_]_ : ℕ → Term → Term → Term
[ k :→ u ] (free x) = free x
[ k :→ u ] (bound i) with k ≟ℕ i
... | yes _ = u
... | no  _ = bound i
[ k :→ u ] (ƛ t) = ƛ [ (suc k) :→ u ] t
[ k :→ u ] (t₁ · t₂) = [ k :→ u ] t₁ · [ k :→ u ] t₂
[ k :→ u ] ‵zero = ‵zero
[ k :→ u ] (‵suc t) = ‵suc ([ k :→ u ] t)

—→≡:→free : ∀ {i : ℕ} {x : List Char} (t : Term)
  → [ i —→ x ] t ≡ [ i :→ free x ] t
—→≡:→free {i} {x} (free y) = refl
—→≡:→free {i} {x} (bound k) with i ≟ℕ k
... | yes _ = refl
... | no  _ = refl
—→≡:→free {i} {x} (ƛ t) = cong ƛ_ (—→≡:→free t)
—→≡:→free {i} {x} (t₁ · t₂) =
  cong₂ _·_ (—→≡:→free t₁) (—→≡:→free t₂)
—→≡:→free {i} {x} ‵zero = refl
—→≡:→free {i} {x} (‵suc t) = cong ‵suc_ (—→≡:→free t)

subst-intro : ∀ {x : List Char} {i : ℕ} (t u : Term)
  → x # t
  → [ i :→ u ] t ≡ [ x := u ] ([ i —→ x ] t)
subst-intro {x} (free y) u x#t with x ≟lchar y
... | yes refl with () ← x#t
... | no  x≢y  = refl
subst-intro {x} {i} (bound j) u x#t with i ≟ℕ j
... | no  i≢j  = refl
... | yes refl with x ≟lchar x
...   | yes refl = refl
...   | no  x≢x  = contradiction refl x≢x
subst-intro (ƛ t) u x#ƛt = cong ƛ_ (subst-intro t u (#-ƛ t x#ƛt))
subst-intro {x} (t₁ · t₂) u x#t =
  let ⟨ x#t₁ , x#t₂ ⟩ = #-· t₁ t₂ x#t in
    cong₂ _·_ (subst-intro t₁ u x#t₁) (subst-intro t₂ u x#t₂)
subst-intro ‵zero u x#t = refl
subst-intro (‵suc t) u x#st =
  cong ‵suc_ (subst-intro t u (#-‵suc t x#st))

subst-op : ∀ {Γ t u A B}
  → ∅ ⊢ u ⦂ A
  → Γ ⊢ ƛ t ⦂ A ⇒ B
    --------------------
  → Γ ⊢ [ 0 :→ u ] t ⦂ B
subst-op {t = t} {u = u} ⊢u (⊢ƛ И⟨ Иe₁ , Иe₂ ⟩) =
  let x                  = fresh (fv t ++ Иe₁)
      ⟨ x∉fv-t , x∉Иe₁ ⟩ = ∉-++ {xs = fv t} {ys = Иe₁}
                              (fresh-correct (fv t ++ Иe₁))
  in ≡-with-⊢ (subst ⊢u (Иe₂ x {x∉Иe₁}))
    (sym (subst-intro t u (∉fv⇒# x t (x∉fv-t))))

data Value : Term → Set where
  V-ƛ : ∀ {t} → Value (ƛ t)
  V-zero : Value ‵zero
  V-suc : ∀ {t} → Value t → Value (‵suc t)

infix 4 _—→_
data _—→_ : Term → Term → Set where
  ξ₁ : ∀ {t₁ t₁' t₂}
    → t₁ —→ t₁'
    → LocallyClosed t₂
      -------------------
    → t₁ · t₂ —→ t₁' · t₂

  ξ₂ : ∀ {t₁ t₂ t₂'}
    → t₂ —→ t₂'
      ---------
    → t₁ · t₂ —→ t₁ · t₂'

  ξ-suc : ∀ {t t'}
    → t —→ t'
      ------------------
    → ‵suc t —→ ‵suc t'

  β : ∀ {t u}
    → 1 ≻ t
    → Value u
      -------
    → (ƛ t) · u —→ [ 0 :→ u ] t

infix  2 _—↠_
infix  1 begin'_
infixr 2 _—→⟨_⟩_
infix  3 _∎'

data _—↠_ : Term → Term → Set where
  _∎' : ∀ M
      ---------
    → M —↠ M

  step—→ : ∀ L {M N}
    → M —↠ N
    → L —→ M
      ---------
    → L —↠ N

pattern _—→⟨_⟩_ L L—→M M—↠N = step—→ L M—↠N L—→M

begin'_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin' M—↠N = M—↠N

data Progress (t : Term) : Set where
  step : ∀ {t'}
    → t —→ t'
      ----------
    → Progress t

  done :
      Value t
      ----------
    → Progress t

progress : ∀ {t A}
  → ∅ ⊢ t ⦂ A
    ----------
  → Progress t
progress (⊢ƛ x) = done V-ƛ
progress (⊢· ⊢t₁ ⊢t₂) with progress ⊢t₁
... | step t₁→t₁' = step (ξ₁ t₁→t₁' (⊢⇒lc ⊢t₂))
... | done V-ƛ with progress ⊢t₂
...   | step t₂→t₂' = step (ξ₂ t₂→t₂')
...   | done val    = step (β (i≻ƛt⇒si≻t (⊢⇒lc ⊢t₁)) val)
progress ⊢zero = done V-zero
progress (⊢suc ⊢t) with progress ⊢t
... | step t→t' = step (ξ-suc t→t')
... | done val  = done (V-suc val)

preserve : ∀ {t t' A}
  → ∅ ⊢ t ⦂ A
  → t —→ t'
    ----------
  → ∅ ⊢ t' ⦂ A
preserve (⊢· ⊢t₁ ⊢t₂) (ξ₁ t→t' _) = ⊢· (preserve ⊢t₁ t→t') ⊢t₂
preserve (⊢· ⊢t₁ ⊢t₂) (ξ₂ t→t') = ⊢· ⊢t₁  (preserve ⊢t₂ t→t')
preserve (⊢· ⊢t₁ ⊢t₂) (β x x₁) = subst-op ⊢t₂ ⊢t₁
preserve (⊢suc ⊢t) (ξ-suc t→t') = ⊢suc (preserve ⊢t t→t')

record Gas : Set where
  eta-equality
  constructor gas
  field
    amount : ℕ

data Finished (t : Term) : Set where
  done : Value t → Finished t
  out-of-gas : Finished t

data Steps (t : Term) : Set where
  steps : ∀ {t'} → t —↠ t' → Finished t' → Steps t

eval : ∀ {t A} → Gas → ∅ ⊢ t ⦂ A → Steps t
eval {t} (gas zero) ⊢t = steps (t ∎') out-of-gas
eval {t} (gas (suc n)) ⊢t with progress ⊢t
... | done V-t = steps (t ∎') (done V-t)
... | step {t'} t→t' with eval (gas n) (preserve ⊢t t→t')
...   | steps t'→u fin-u = steps (t —→⟨ t→t' ⟩ t'→u) fin-u

two : Term
two = ƛ ƛ bound 1 · (bound 1 · bound 0)

plus : Term
plus = ƛ ƛ ƛ ƛ bound 3 · bound 1 · (bound 2 · bound 1 · bound 0)

suc' : Term
suc' = ƛ ‵suc (bound 0)

⊢two : ∅ ⊢ two ⦂ (‵ℕ ⇒ ‵ℕ) ⇒ ‵ℕ ⇒ ‵ℕ
⊢two = ⊢ƛ
  И⟨ []
  , (λ a → ⊢ƛ
    И⟨ (a ∷ [])
    , (λ b {b∉} →
      ⊢·
      (⊢free (T (sym-≢ (∉∷[]⇒≢ b∉)) H′))
      (⊢· (⊢free (T (sym-≢ (∉∷[]⇒≢ b∉)) H′)) (⊢free (H′)))) ⟩) ⟩

⊢plus : ∀ {Γ A} → Γ ⊢ plus ⦂
  ((A ⇒ A) ⇒ A ⇒ A) ⇒ ((A ⇒ A) ⇒ A ⇒ A) ⇒ ((A ⇒ A) ⇒ A ⇒ A)
⊢plus = ⊢ƛ
  И⟨ []
  , (λ a → ⊢ƛ
    И⟨ a ∷ []
    , (λ b {b∉} → ⊢ƛ
      И⟨ a ∷ b ∷ []
      , (λ c {c∉} → ⊢ƛ
        И⟨ a ∷ b ∷ c ∷ []
        , (λ d {d∉} →
        ⊢·
          (⊢·
            (⊢free (T (a≢d d∉) (T (a≢c c∉) (T (a≢b b∉) H′))))
            (⊢free (T (c≢d d∉) (H′))))
          (⊢·
            (⊢·
              (⊢free (T (b≢d d∉) (T (b≢c c∉) H′)))
              (⊢free (T (c≢d d∉) H′)))
            (⊢free H′))) ⟩) ⟩) ⟩) ⟩
  where
    a≢d : ∀ {a b c d} → d ∉ a ∷ b ∷ c ∷ [] → a ≢ d
    a≢d d∉ = sym-≢ (∉∷[]⇒≢ (proj₁ (∉-++ d∉)))
    a≢c : ∀ {a b c} → c ∉ a ∷ b ∷ [] → a ≢ c
    a≢c c∉ = sym-≢ (∉∷[]⇒≢ (proj₁ (∉-++ c∉)))
    a≢b : ∀ {a b} → b ∉ a ∷ [] → a ≢ b
    a≢b b∉ = sym-≢ (∉∷[]⇒≢ b∉)
    c≢d : ∀ {a b c d} → d ∉ a ∷ b ∷ c ∷ [] → c ≢ d
    c≢d {a} {b} d∉ =
      sym-≢ (∉∷[]⇒≢ (proj₂ (∉-++ {xs = a ∷ b ∷ []} d∉)))
    b≢d : ∀ {a b c d} → d ∉ a ∷ b ∷ c ∷ [] → b ≢ d
    b≢d {a} {b} d∉ =
      sym-≢ (∉∷[]⇒≢ (proj₂ (
        ∉-++
          {xs = a ∷ []}
          (proj₁ (∉-++ {xs = a ∷ b ∷ []} d∉)))))
    b≢c : ∀ {a b c} → c ∉ a ∷ b ∷ [] → b ≢ c
    b≢c {a} c∉ = sym-≢ (∉∷[]⇒≢ (proj₂ (∉-++ {xs = a ∷ []} c∉)))

⊢suc' : ∀ {Γ} → Γ ⊢ suc' ⦂ ‵ℕ ⇒ ‵ℕ
⊢suc' = ⊢ƛ И⟨ [] , (λ _ → ⊢suc (⊢free H′)) ⟩

⊢2+2 : ∅ ⊢ plus · two · two · suc' · ‵zero ⦂ ‵ℕ
⊢2+2 = ⊢· (⊢· (⊢· (⊢· ⊢plus  ⊢two) ⊢two) ⊢suc') ⊢zero
