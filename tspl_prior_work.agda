module tspl_prior_work where

open import plfa_adaptions
-- Import cofinite quantification.
open import cofinite using (Cof-syntax; Иe₁; Иe₂; И⟨_,_⟩) 

-- Data types (naturals, strings, characters)
open import Data.Nat using (ℕ; zero; suc; _<_; _≥_; _≤_; _≤?_; _<?_; z≤n; s≤s; _⊔_)
  renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-<-trans; <-≤-trans; ≤-antisym; ≤-total;
  +-mono-≤; n≤1+n; m≤n⇒m≤1+n; suc-injective; <⇒≢; ≰⇒>; ≮⇒≥)
open import Data.String using (String; fromList; toList) renaming (_≟_ to _≟str_;
  _++_ to _++str_; length to str-length)
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

infix  4  _∋_⦂_
infix  4 _⊢_⦂_
infixl 5 _,_⦂_

infixr 7 _⇒_

infix  5 ƛ_
infixl 7 _·_
infix  9 free_
infix  9 bound_

Id : Set
Id = List Char

All≤⇒<⇒All< : ∀ {n m : ℕ} (xs : List ℕ)
  → n < m
  → All (_≤ n) xs
    -------------
  → All (_< m) xs
All≤⇒<⇒All< [] n<m All.[] = All.[]
All≤⇒<⇒All< (x ∷ xs) n<m (x≤n All.∷ all≤) =
  ≤-<-trans x≤n n<m All.∷ All≤⇒<⇒All< xs n<m all≤

sym-≢ : ∀ {A : Set} {x y : A}
  → x ≢ y
    -----
  → y ≢ x
sym-≢ x≢y y≡x = x≢y (sym y≡x)

≡⇒<s : ∀ {n m : ℕ} → n ≡ m → n < suc m
≡⇒<s {zero} {m} n≡m = s≤s z≤n
≡⇒<s {suc n} {suc m} sn≡sm = s≤s (≡⇒<s (suc-injective sn≡sm))

∉⇒≢ : ∀ {xs : List Id} {x y : Id}
  → x ∈ xs
  → y ∉ xs
    -------
  → x ≢ y
∉⇒≢ {xs} x∈ y∉ refl = y∉ x∈

len≠⇒≠ : ∀ {A : Set} (xs ys : List A)
  → length xs ≢ length ys → xs ≢ ys
len≠⇒≠ xs ys len≢ =
  λ xs≡ys → contradiction (cong length xs≡ys) len≢

len-replicate : ∀ {A : Set} (n : ℕ) (a : A)
  → length (replicate n a) ≡ n
len-replicate zero a = refl
len-replicate (suc n) a = cong suc (len-replicate n a)

new-list : ∀ {A : Set} → A → List (List A) → List A
new-list a xss = a ∷ replicate (max 0 (map length xss)) a

fresh : List Id → Id
fresh xss = new-list 'q' xss

len-new-list : ∀ {A : Set} (a : A) (xss : List (List A))
  → max 0 (map length xss) < length (new-list a xss)
len-new-list a xss =
  ≡⇒<s (sym (len-replicate (max 0 (map length xss)) a))

new-list-correct :
  ∀ {A : Set} (xss : List (List A)) (a : A)
  → ¬ Any ((new-list a xss) ≡_) xss
new-list-correct xss a = All¬⇒¬Any (go xss a)
  where
    go : ∀ {A : Set} (xss : List (List A)) (a : A)
      → All ((new-list a xss) ≢_) xss
    go xs a =
      helper
        xs
        (new-list a xs)
        (All≤⇒<⇒All<
          (map length xs)
          (len-new-list a xs)
          (xs≤max 0 (map length xs)))
      where
        helper : ∀ {A : Set} (xss : List (List A)) (ys : List A)
          → All (_< length ys) (map length xss)
          → All (ys ≢_) xss
        helper [] ys All.[] = All.[]
        helper (xs ∷ xss) ys (lenxs<lenys All.∷ all<) =
          sym-≢ (len≠⇒≠ xs ys (<⇒≢ lenxs<lenys))
            All.∷ helper xss ys all<

fresh-correct : (xss : List Id) → (fresh xss) ∉ xss
fresh-correct xss = new-list-correct xss 'q'

data Term : Set where
  free_  : Id → Term
  bound_ : ℕ → Term
  ƛ_     : Term → Term
  _·_    : Term → Term → Term
  ‵zero  : Term
  ‵suc_  : Term → Term

ƛ-inj : ∀{t t'} → ƛ t ≡ ƛ t' → t ≡ t'
ƛ-inj refl = refl

·-inj : {t₁ t₂ t₁' t₂' : Term}
  → t₁ · t₂ ≡ t₁' · t₂'
    -----------------------
  → (t₁ ≡ t₁') × (t₂ ≡ t₂')
·-inj refl = ⟨ refl , refl ⟩

‵suc-inj : {t₁ t₂ : Term}
  → ‵suc t₁ ≡ ‵suc t₂
    -------------
  → t₁ ≡ t₂
‵suc-inj refl = refl

[_—→_]_ : ℕ → Id → Term → Term
[ k —→ x ] (free y) = free y
[ k —→ x ] (bound i) with k ≟ℕ i
... | yes _ = free x
... | no  _ = bound i
[ k —→ x ] (ƛ t) = ƛ ([ suc k —→ x ] t)
[ k —→ x ] (t₁ · t₂) = [ k —→ x ] t₁ · [ k —→ x ] t₂
[ k —→ x ] ‵zero = ‵zero
[ k —→ x ] ‵suc t = ‵suc ([ k —→ x ] t)

[_←—_]_ : ℕ → Id → Term → Term
[ k ←— x ] (free y) with x ≟lchar y
... | yes _ = bound k
... | no  _ = free y
[ k ←— x ] (bound i) = bound i
[ k ←— x ] (ƛ t) = ƛ [ suc k ←— x ] t
[ k ←— x ] (t₁ · t₂) = [ k ←— x ] t₁ · [ k ←— x ] t₂
[ k ←— x ] ‵zero = ‵zero
[ k ←— x ] ‵suc t = ‵suc ([ k ←— x ] t)

ax1 : ∀ (i : ℕ) (a b : Id) (t : Term)
  → [ i —→ a ] ([ i —→ b ] t) ≡ [ i —→ b ] t
ax1 i a b (free x) = refl
ax1 i a b (bound k) with i ≟ℕ k
... | yes _   = refl
... | no  i≢k with i ≟ℕ k
...   | yes i≡k = contradiction i≡k i≢k
...   | no  _   = refl
ax1 i a b (ƛ t) rewrite ax1 (suc i) a b t = refl
ax1 i a b (t₁ · t₂) rewrite ax1 i a b t₁ | ax1 i a b t₂ = refl
ax1 i a b ‵zero = refl
ax1 i a b (‵suc t) rewrite ax1 i a b t = refl

ax1-cor : ∀ (i k : ℕ) (a : Id) (t : Term)
  → i ≡ k
  → [ k —→ a ] ([ i —→ a ] t) ≡ [ i —→ a ] t
ax1-cor i .i a t refl = ax1 i a a t

ax2 : ∀ (i j : ℕ) (x : Id) (t : Term)
    → [ i ←— x ] ([ j ←— x ] t) ≡ [ j ←— x ] t
ax2 i j x (free y) with x ≟lchar y
... | yes refl = refl
... | no  x≢y with x ≟lchar y
...   | yes x≡y = contradiction x≡y x≢y
...   | no  _   = refl
ax2 i j x (bound k) = refl
ax2 i j x (ƛ t) rewrite ax2 (suc i) (suc j) x t = refl
ax2 i j x (t₁ · t₂) rewrite ax2 i j x t₁ | ax2 i j x t₂ = refl
ax2 i j x ‵zero = refl
ax2 i j x (‵suc t) rewrite ax2 i j x t = refl

suc-preserves-≢ : ∀ {n m : ℕ} → n ≢ m → suc n ≢ suc m
suc-preserves-≢ {n} {m} n≢m sn≡sm = n≢m (helper n m sn≡sm)
  where
    helper : ∀ (n m : ℕ) → suc n ≡ suc m → n ≡ m
    helper n m refl = refl

ax5 : ∀ (i j : ℕ) (a b : Id) (t : Term)
  → (i≢j : i ≢ j)
  → [ i —→ a ] ([ j —→ b ] t) ≡ [ j —→ b ] ([ i —→ a ] t)
ax5 i j a b (free x) _ = refl
ax5 i j a b (bound k) i≢j with j ≟ℕ k
... | no  j≢k with i ≟ℕ k
...   | yes i≡k = refl
...   | no  i≢k with j ≟ℕ k
...     | yes j≡k = contradiction j≡k j≢k
...     | no  j≢k = refl
ax5 i j a b (bound k) i≢j | yes j≡k with i ≟ℕ k
...   | yes i≡k = ⊥-elim (i≢j (trans i≡k (sym j≡k)))
...   | no  i≢k with j ≟ℕ k
...     | yes j≡k = refl
...     | no  j≢k = contradiction j≡k j≢k
ax5 i j a b (ƛ t) i≢j
  rewrite ax5 (suc i) (suc j) a b t (suc-preserves-≢ i≢j) = refl
ax5 i j a b (t₁ · t₂) i≢j
  rewrite ax5 i j a b t₁ (i≢j) | ax5 i j a b t₂ (i≢j) = refl
ax5 i j a b ‵zero i≢j = refl
ax5 i j a b (‵suc t) i≢j rewrite ax5 i j a b t i≢j = refl

fv : Term → List Id
fv (free x) = x ∷ []
fv (bound i) = []
fv (ƛ t) = fv t
fv (t₁ · t₂) = fv t₁ ++ fv t₂
fv ‵zero = []
fv (‵suc t) = fv t

_#_ : Id → Term → Set
x # t = [ 0 ←— x ] t ≡ t

#⇒∉fv : ∀ (x : Id) (t : Term) → x # t → x ∉ fv t
#⇒∉fv x (free y) x#t with x ≟lchar y
... | yes x≡y with () ← x#t
... | no  x≢y = All¬⇒¬Any (x≢y All.∷ All.[])
#⇒∉fv x (bound i) x#t = λ ()
#⇒∉fv x (ƛ t) x#t = #⇒∉fv x t (
  begin
    [ 0 ←— x ] t
  ≡⟨ sym (cong ([ 0 ←— x ]_) (ƛ-inj x#t)) ⟩
    [ 0 ←— x ] ([ 1 ←— x ] t)
  ≡⟨ ax2 0 1 x t ⟩
    [ 1 ←— x ] t
  ≡⟨ ƛ-inj x#t ⟩
    t
  ∎)
#⇒∉fv x (t₁ · t₂) x#t = let ⟨ x#t₁ , x#t₂ ⟩ = ·-inj x#t in
  ++-∉
    (#⇒∉fv x t₁ x#t₁)
    (#⇒∉fv x t₂ x#t₂)
#⇒∉fv x (‵suc t) x#t = #⇒∉fv x t (‵suc-inj x#t)

∉fv⇒# : ∀ (x : Id) (t : Term) → x ∉ fv t → x # t
∉fv⇒# x (free y) x∉fv with x ≟lchar y
... | yes x≡y = ⊥-elim (x∉fv (here x≡y))
... | no  x≢y = refl
∉fv⇒# x (bound i) x∉fv = refl
∉fv⇒# x (ƛ t) x∉fv = cong ƛ_ (
  begin
    [ 1 ←— x ] t
  ≡⟨ sym (cong ([ 1 ←— x ]_) (∉fv⇒# x t x∉fv)) ⟩
    [ 1 ←— x ] ([ 0 ←— x ] t)
  ≡⟨ ax2 1 0 x t ⟩
    [ 0 ←— x ] t
  ≡⟨ ∉fv⇒# x t x∉fv ⟩
    t
  ∎)
∉fv⇒# x (t₁ · t₂) x∉fv =
  let ⟨ x∉fv-t₁ , x∉fv-t₂ ⟩ = (∉-++ x∉fv) in
    cong₂ _·_
      (∉fv⇒# x t₁ x∉fv-t₁)
      (∉fv⇒# x t₂ x∉fv-t₂)
∉fv⇒# x ‵zero x∉fv = refl
∉fv⇒# x (‵suc t) x∉fv rewrite ∉fv⇒# x t x∉fv = refl

#-ƛ : ∀ {x : Id} (t : Term)
  → x # (ƛ t)
    -------
  → x # t
#-ƛ {x} t x#ƛt =
  begin
    [ 0 ←— x ] t
  ≡⟨ sym (cong ([ 0 ←— x ]_) (ƛ-inj x#ƛt)) ⟩
    [ 0 ←— x ] ([ 1 ←— x ] t)
  ≡⟨ ax2 0 1 x t ⟩
    [ 1 ←— x ] t
  ≡⟨ ƛ-inj x#ƛt ⟩
    t
  ∎

#-· : ∀ {x : Id} (t₁ t₂ : Term)
  → x # (t₁ · t₂)
    ---------------
  → x # t₁ × x # t₂
#-· {x} t₁ t₂ x#t₁t₂ with ∉-++ (#⇒∉fv x (t₁ · t₂) x#t₁t₂)
... | ⟨ x∉fv-t₁ , x∉fv-t₂ ⟩
  = ⟨ (∉fv⇒# x t₁ x∉fv-t₁) , ∉fv⇒# x t₂ x∉fv-t₂ ⟩

#-‵suc : ∀ {x : Id} (t : Term)
  → x # (‵suc t)
    -------
  → x # t
#-‵suc {x} t x#‵suc-t = ∉fv⇒# x t (#⇒∉fv x (‵suc t) x#‵suc-t)

_≻_ : ℕ → Term → Set
i ≻ t = (j : ℕ) ⦃ _ : j ≥ i ⦄ → И a , ([ j —→ a ] t ≡ t)

LocallyClosed_ : Term → Set
LocallyClosed t = 0 ≻ t

lemma2·6 : ∀ {i j : ℕ} {t : Term}
  → j ≥ i
  → i ≻ t
    -----
  → j ≻ t
lemma2·6 {i} {j} {t} j≥i i≻t k = i≻t k ⦃ ≤-trans j≥i it ⦄

≻⇒s≻ : ∀ {i : ℕ} {t : Term}
  → i ≻ t
    -----
  → (suc i) ≻ t
≻⇒s≻ {i} i≻t = lemma2·6 (n≤1+n i) i≻t

lemma2·7-1 : ∀ {i : ℕ} {x y : Id} {t : Term}
  → [ i —→ x ] t ≡ t
    ----------------
  → [ i —→ y ] t ≡ t
lemma2·7-1 {i} {x} {y} {t} [i>x]t≡t =
  begin
    ([ i —→ y ] t)
  -- use the fact that t ≡ [ i —→ x ] t
  ≡⟨ sym (cong ([ i —→ y ]_) [i>x]t≡t) ⟩
    [ i —→ y ] ([ i —→ x ] t)
  ≡⟨ ax1 i y x t ⟩
    [ i —→ x ] t
  ≡⟨ [i>x]t≡t ⟩
    t
  ∎

lemma2·7-2 : ∀ {i j : ℕ} {x : Id} {t : Term}
  → j ≥ i
  → i ≻ t
    ----------------
  → [ j —→ x ] t ≡ t
lemma2·7-2 {j = j} j≥i i≻t with (i≻t j ⦃ j≥i ⦄)
... | И⟨ Иe₁ , Иe₂ ⟩ =
  lemma2·7-1 (Иe₂ (fresh Иe₁) {fresh-correct Иe₁})

open-rec-lc : ∀ {t : Term} {i : ℕ} {x : Id}
  → LocallyClosed t
    ----------------
  → [ i —→ x ] t ≡ t
open-rec-lc lc-t = lemma2·7-2 z≤n lc-t

open-rec-lc-lemma : ∀ {t : Term} {i j : ℕ} {u v : Id}
  → i ≢ j
  → [ i —→ u ] ([ j —→ v ] t) ≡ [ j —→ v ] t
  → [ i —→ u ] t ≡ t
open-rec-lc-lemma {free x} i≢j assump = refl
open-rec-lc-lemma {bound k} {i} {j} i≢j assump
  with i ≟ℕ j | i ≟ℕ k
... | yes i≡j | yes i≡k = contradiction i≡j i≢j
... | yes i≡j | no  i≢k = contradiction i≡j i≢j
... | no  _   | no  _   = refl
... | no i≢j' | yes i≡k with j ≟ℕ k
...   | yes j≡k = ⊥-elim (i≢j (trans i≡k (sym j≡k)))
...   | no  j≢k with i ≟ℕ k
...     | yes i≡k' with () ← assump
...     | no  i≢k  = contradiction i≡k i≢k
open-rec-lc-lemma {ƛ t} {i} {j} i≢j assump
  rewrite open-rec-lc-lemma {t} {suc i} {suc j}
      (suc-preserves-≢ i≢j)
      (ƛ-inj assump)
    = refl
open-rec-lc-lemma {t₁ · t₂} i≢j assump
  rewrite
    open-rec-lc-lemma {t₁} i≢j (proj₁ (·-inj assump))
  | open-rec-lc-lemma {t₂} i≢j (proj₂ (·-inj assump))
  = refl
open-rec-lc-lemma {‵zero} _ _ = refl
open-rec-lc-lemma {‵suc t} i≢j assump
  rewrite open-rec-lc-lemma {t} i≢j (‵suc-inj assump) = refl

lemma2·13 : ∀ {t : Term} {a : Id} {i : ℕ} (j : ℕ)
  → j ≥ i
  → i ≻ t
  → i ≻ ([ j —→ a ] t)
lemma2·13 {t} {a} {i} j j≥i i≻t k
  with j ≟ℕ k | Иe₁ (i≻t j ⦃ j≥i ⦄)
... | yes refl | l = И⟨ l , (λ b → ax1 j b a t) ⟩
... | no  j≢k  | l = И⟨ l , (λ b →
  begin
    [ k —→ b ] ([ j —→ a ] t)
  ≡⟨ ax5 k j b a t (sym-≢ j≢k) ⟩
    [ j —→ a ] ([ k —→ b ] t)
  ≡⟨ cong([ j —→ a ]_) (lemma2·7-2 it i≻t) ⟩
    [ j —→ a ] t
  ∎) ⟩

data Lc-at : ℕ → Term → Set where
  lc-at-bound : ∀ {i j : ℕ} ⦃ _ : j < i ⦄ → Lc-at i (bound j)
  lc-at-free : ∀ {i : ℕ} {a : Id} → Lc-at i (free a)
  lc-at-lam : ∀ {i : ℕ} {t : Term}
    → Lc-at (suc i) t
      ------------------
    → Lc-at i (ƛ t)
  lc-at-app : ∀ {i : ℕ} {t₁ t₂ : Term}
    → Lc-at i t₁
    → Lc-at i t₂
      -------------------
    → Lc-at i (t₁ · t₂)
  lc-at-‵zero : ∀ {i : ℕ} → Lc-at i ‵zero
  lc-at-‵suc : ∀ {i : ℕ} {t : Term}
    → Lc-at i t
      ------------------
    → Lc-at i (‵suc t)

≻⇒lc-at : ∀ (i : ℕ) (t : Term) → i ≻ t → Lc-at i t
≻⇒lc-at i (free x) i≻t = lc-at-free
≻⇒lc-at i (bound j) i≻t with j <? i
... | yes j<i = lc-at-bound ⦃ j<i ⦄
... | no  j≮i with
  (Иe₂ (i≻t j ⦃ ≮⇒≥ j≮i ⦄))
    (fresh (Иe₁ (i≻t j ⦃ ≮⇒≥ j≮i ⦄)))
    {fresh-correct (Иe₁ (i≻t j ⦃ ≮⇒≥ j≮i ⦄))}
...   | q with j ≟ℕ j
...     | yes refl with () ← q
...     | no  j≢j  = contradiction refl j≢j
≻⇒lc-at i (ƛ t) i≻t = lc-at-lam (≻⇒lc-at (suc i) t helper)
  where
    helper : suc i ≻ t
    helper (suc j) ⦃ s≤s j≥i ⦄ =
      И⟨ Иe₁ (i≻t j ⦃ j≥i ⦄)
      , (λ a {a∉} → ƛ-inj ((Иe₂ (i≻t j ⦃ j≥i ⦄)) a {a∉})) ⟩
≻⇒lc-at i (t₁ · t₂) i≻t =
  lc-at-app (≻⇒lc-at i t₁ i≻t₁) (≻⇒lc-at i t₂ i≻t₂)
  where
    i≻t₁ : i ≻ t₁
    i≻t₁ j ⦃ j≥i ⦄ =
      И⟨ Иe₁ (i≻t j ⦃ j≥i ⦄)
      , (λ a {a∉} → proj₁ (·-inj ((Иe₂ (i≻t j ⦃ j≥i ⦄)) a {a∉})))
      ⟩
    i≻t₂ : i ≻ t₂
    i≻t₂ j ⦃ j≥i ⦄ =
      И⟨ Иe₁ (i≻t j ⦃ j≥i ⦄)
      , (λ a {a∉} → proj₂ (·-inj ((Иe₂ (i≻t j ⦃ j≥i ⦄)) a {a∉})))
      ⟩
≻⇒lc-at _ ‵zero _ = lc-at-‵zero
≻⇒lc-at i (‵suc t) i≻t = lc-at-‵suc (≻⇒lc-at i t (λ j →
  И⟨ (Иe₁ (i≻t j ⦃ it ⦄))
  , (λ a {a∉} → ‵suc-inj ((Иe₂ (i≻t j ⦃ it ⦄)) a {a∉})) ⟩))

lc-at⇒≻ : ∀ (i : ℕ) (t : Term) → Lc-at i t → i ≻ t
-- Here we use "[]" because we don't really care what string
-- we use to test the locally closedness.
lc-at⇒≻ i (bound k) lc-at-bound j ⦃ i≤j ⦄ with j ≟ℕ k
... | yes j≡k = contradiction (sym j≡k) (<⇒≢ (≤-trans it i≤j))
... | no  j≢k = И⟨ [] , (λ a → refl) ⟩
lc-at⇒≻ i (free x) lc-at-free j = И⟨ [] , (λ a → refl) ⟩
lc-at⇒≻ i (ƛ t) (lc-at-lam lc-at) j
  with lc-at⇒≻ (suc i) t lc-at
... | si≻t = И⟨ [] , (λ a → cong ƛ_ (lemma2·7-2 (s≤s it) si≻t)) ⟩
lc-at⇒≻ i (t₁ · t₂) (lc-at-app lc-at₁ lc-at₂) j =
  И⟨ []
  , (λ a → cong₂ _·_
      (lemma2·7-2 it (lc-at⇒≻ i t₁ lc-at₁))
      (lemma2·7-2 it (lc-at⇒≻ i t₂ lc-at₂))) ⟩
lc-at⇒≻ _ (‵zero) (lc-at-‵zero) j = И⟨ [] , (λ _ → refl) ⟩
lc-at⇒≻ i (‵suc t) (lc-at-‵suc lc-at) j =
  И⟨ []
  , (λ _ → cong ‵suc_ (lemma2·7-2 it (lc-at⇒≻ i t lc-at))) ⟩

bound-never-lc : ∀ (n : ℕ) → ¬ LocallyClosed (bound n)
bound-never-lc n x with ≻⇒lc-at 0 (bound n) x
... | lc-at-bound ⦃ () ⦄ -- This implies that n < 0
                        -- which is never true.

free-lc : ∀ {x : Id} → LocallyClosed (free x)
free-lc _ = И⟨ [] , (λ _ → refl) ⟩

i≻ƛt⇒si≻t : ∀ {i : ℕ} {t : Term} → i ≻ (ƛ t) → suc i ≻ t
i≻ƛt⇒si≻t {i} {t} lc-t with ≻⇒lc-at i (ƛ t) lc-t
... | lc-at-lam lc-at-si-t = lc-at⇒≻ (suc i) t lc-at-si-t

·-≻ : ∀ {t₁ t₂ : Term} {i : ℕ}
  → i ≻ (t₁ · t₂) → (i ≻ t₁) × (i ≻ t₂)
·-≻ {t₁} {t₂} {i} i≻· with ≻⇒lc-at i (t₁ · t₂) i≻·
... | lc-at-app t₁-at t₂-at =
  ⟨ lc-at⇒≻ i t₁ t₁-at
  , lc-at⇒≻ i t₂ t₂-at ⟩

‵zero-≻ : ∀ {i : ℕ} → i ≻ ‵zero
‵zero-≻ j = И⟨ [] , (λ _ → refl) ⟩

‵suc-≻ : ∀ {t : Term} {i : ℕ} → i ≻ (‵suc t) → i ≻ t
‵suc-≻ {t} {i} i≻‵suc-t with ≻⇒lc-at i (‵suc t) i≻‵suc-t
... | lc-at-‵suc lc-at-i = lc-at⇒≻ i t lc-at-i

[_:=_]_ : Id → Term → Term → Term
[ x := u ] (free y) with x ≟lchar y
... | yes _ = u
... | no  _ = free y
[ x := u ] (bound i) = bound i
[ x := u ] (ƛ t) = ƛ [ x := u ] t
[ x := u ] (t₁ · t₂) = [ x := u ] t₁ · [ x := u ] t₂
[ x := u ] (‵zero) = ‵zero
[ x := u ] (‵suc t) = ‵suc ([ x := u ] t)

subst-open-var : ∀ {u : Term} {x y : Id} {i : ℕ} (t : Term)
  → x ≢ y
  → i ≻ u
  → [ x := u ] ([ i —→ y ] t) ≡ [ i —→ y ] ([ x := u ] t)
subst-open-var {x = x} (free z) x≢y i≻u with x ≟lchar z
... | yes x≡z = sym (lemma2·7-2 ≤-refl i≻u)
... | no  x≢z = refl
subst-open-var {_} {x} {y} {i} (bound k) x≢y lc-u with i ≟ℕ k
... | no  i≢k = refl
... | yes i≡k with x ≟lchar y
...   | yes x≡y = contradiction x≡y x≢y
...   | no  x≢y = refl
subst-open-var (ƛ t) x≢y lc-u =
  cong ƛ_ (subst-open-var t x≢y (≻⇒s≻ lc-u))
subst-open-var (t₁ · t₂) x≢y lc-u =
  cong₂ _·_
    (subst-open-var t₁ x≢y lc-u)
    (subst-open-var t₂ x≢y lc-u)
subst-open-var (‵zero) x≢y lc-u = refl
subst-open-var (‵suc t) x≢y lc-u =
  cong ‵suc_ (subst-open-var t x≢y lc-u)

subst-open-lc : ∀ {t u : Term} {x y : Id}
  → x ≢ y
  → LocallyClosed u
  → [ x := u ] ([ 0 —→ y ] t) ≡ [ 0 —→ y ] ([ x := u ] t)
subst-open-lc {t} x≢y lc-u = subst-open-var t x≢y lc-u
  
subst-fresh : ∀ {t u : Term} {x : Id}
  → x ∉ fv t
  → [ x := u ] t ≡ t
subst-fresh {free y} {u} {x} x∉ with x ≟lchar y
... | yes refl = ⊥-elim (x∉ (here refl))
... | no  _    = refl
subst-fresh {bound i} {u} {x} x∉ = refl
subst-fresh {ƛ t} {u} {x} x∉ = cong ƛ_ (subst-fresh x∉)
subst-fresh {t₁ · t₂} {u} {x} x∉ =
  let ⟨ x∉t₁ , x∉t₂ ⟩ = ∉-++ x∉ in
    cong₂ _·_ (subst-fresh x∉t₁) (subst-fresh x∉t₂)
subst-fresh {‵zero} {u} {x} x∉ = refl
subst-fresh {‵suc t} {u} {x} x∉ = cong ‵suc_ (subst-fresh x∉)

subst-≻ : ∀ {t u : Term} {i : ℕ} (x : Id)
  → i ≻ t
  → i ≻ u
    ----------------
  → i ≻ ([ x := u ] t)
subst-≻ {free y} x i≻t i≻u j with x ≟lchar y
... | yes _ = i≻u j
... | no  _ = И⟨ [] , (λ _ → refl) ⟩
subst-≻ {bound k} x i≻t i≻u j with j ≟ℕ k
... | no  _   = И⟨ [] , (λ _ → refl) ⟩
... | yes j≡k with i≻t j
...   | И⟨ Иe₁ , Иe₂ ⟩ with j ≟ℕ k
...     | no  j≢k = contradiction j≡k j≢k
...     | yes _   with () ← Иe₂ (fresh Иe₁) {fresh-correct Иe₁}
subst-≻ {ƛ t} {u} x i≻t i≻u j with i≻ƛt⇒si≻t i≻t
... | si≻t =
  И⟨ (x ∷ (Иe₁ (si≻t (suc j) ⦃ s≤s it ⦄)))
  , (λ a {a∉} → cong ƛ_ ((
    begin
      [ suc j —→ a ] ([ x := u ] t)
    ≡⟨ sym (subst-open-var
          t
          (sym-≢ (∉∷[]⇒≢ (proj₁ (∉-++ {xs = x ∷ []} a∉))))
          (lemma2·6 (m≤n⇒m≤1+n it) i≻u)) ⟩
      [ x := u ] ([ suc j —→ a ] t)
    ≡⟨ cong ([ x := u ]_)
        ((Иe₂ (si≻t (suc j) ⦃ s≤s it ⦄))
          a
          {proj₂ (∉-++ {xs = x ∷ []} a∉)}) ⟩
      [ x := u ] t
    ∎))) ⟩
subst-≻ {t₁ · t₂} {i = i} x i≻t i≻u j =
  let ⟨ i≻t₁ , i≻t₂ ⟩ = ·-≻ i≻t in
    И⟨ (Иe₁ ((subst-≻ x i≻t₁ i≻u) j)
      ++ Иe₁ ((subst-≻ x i≻t₂ i≻u) j))
    , (λ a {a∉} → cong₂ _·_
        (lemma2·7-2 it (subst-≻ x i≻t₁ i≻u))
        (lemma2·7-2 it (subst-≻ x i≻t₂ i≻u))) ⟩
subst-≻ {‵zero} {u} x i≻t i≻u j = И⟨ [] , (λ _ → refl) ⟩
subst-≻ {‵suc t} {u} x i≻t i≻u j =
  let И⟨ Иe₁ , Иe₂ ⟩ = (subst-≻ {t} x (‵suc-≻ i≻t) i≻u) j ⦃ it ⦄
    in И⟨ Иe₁ , (λ a {a∉} → cong ‵suc_ (Иe₂ a {a∉})) ⟩

subst-lc : ∀ {t u : Term} (x : Id)
  → LocallyClosed t
  → LocallyClosed u
    --------------------------
  → LocallyClosed [ x := u ] t
subst-lc = subst-≻

data Type : Set where
  ‵ℕ : Type
  _⇒_ : Type → Type → Type

data Context : Set where
  ∅ : Context
  _,_⦂_ : Context → Id → Type → Context

data _∋_⦂_ : Context → Id → Type → Set where
  H : ∀ {Γ x y A}
    → x ≡ y
      ------------------
    → Γ , x ⦂ A ∋ y ⦂ A

  T : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      -----------------
    → Γ , y ⦂ B ∋ x ⦂ A

H′ : ∀ {Γ x A}
  → Γ , x ⦂ A ∋ x ⦂ A
H′ = H refl

T′ : ∀ {Γ x y A B}
  → ⦃ x≢y : False (x ≟lchar y) ⦄
  → Γ ∋ x ⦂ A
    ------------------
  → Γ , y ⦂ B ∋ x ⦂ A
T′ ⦃ x≢y = x≢y ⦄ x = T (toWitnessFalse x≢y) x

domain : Context → List Id
domain ∅ = []
domain (Γ , x ⦂ A) = x ∷ domain Γ

data _⊢_⦂_ : Context → Term → Type → Set where
  ⊢free : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      ---------
    → Γ ⊢ free x ⦂ A

  ⊢ƛ : ∀ {Γ t A B}
    → И x , ((Γ , x ⦂ A) ⊢ [ 0 —→ x ] t ⦂ B)
      ---------------------------
    → Γ ⊢ ƛ t ⦂ (A ⇒ B)

  ⊢· : ∀ {Γ t₁ t₂ A B}
    → Γ ⊢ t₁ ⦂ (A ⇒ B)
    → Γ ⊢ t₂ ⦂ A
      ---------
    → Γ ⊢ t₁ · t₂ ⦂ B

  ⊢zero : ∀ {Γ}
      -------
    → Γ ⊢ ‵zero ⦂ ‵ℕ

  ⊢suc : ∀ {Γ t}
    → Γ ⊢ t ⦂ ‵ℕ
      ----------------
    → Γ ⊢ ‵suc t ⦂ ‵ℕ

-- Apply term-equality within type judgements.
≡-with-⊢ : ∀ {Γ t u A}
  → Γ ⊢ t ⦂ A
  → t ≡ u
    ----------
  → Γ ⊢ u ⦂ A
≡-with-⊢ ⊢t refl = ⊢t

_ : (∅ , (toList "x") ⦂ ‵ℕ) ⊢ (ƛ (bound 0)) · (free (toList "x")) ⦂ ‵ℕ
_ = ⊢· (⊢ƛ И⟨ (toList "x") ∷ [] , (λ a → ⊢free H′) ⟩) (⊢free H′)

ex-for-all-contexts : ∀ {Γ} → Γ ⊢ ƛ ƛ (bound 0) · (bound 1) ⦂ (‵ℕ ⇒ (‵ℕ ⇒ ‵ℕ) ⇒ ‵ℕ)
ex-for-all-contexts {Γ} = ⊢ƛ (
  И⟨ [] , (λ a → ⊢ƛ (
    И⟨ a ∷ []
    , (λ b {b∉} → ⊢· (⊢free (H′)) (⊢free (T (∉⇒≢ (here refl) b∉) H′))) ⟩ )) ⟩)

-- Extending contexts.
ext : ∀ {Γ Δ}
  → (∀ {x A}     →         Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
    ----------------------------------------------------
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ (H refl) = H refl
ext ρ (T x≢y ∋x) = T x≢y (ρ ∋x)

-- Renaming (aka. "rebasing") of contexts.
rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
    --------------------------------
  → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
rename ρ (⊢free ∋A) = ⊢free (ρ ∋A)
rename {Δ = Δ} ρ (⊢ƛ И⟨ Иe₁ , Иe₂ ⟩ ) =
  ⊢ƛ И⟨ (domain Δ ++ Иe₁) , (λ a {a∉} →
    rename (ext ρ) (Иe₂ a {proj₂ (∉-++ a∉)})) ⟩
rename ρ (⊢· ⊢A⇒B ⊢A) = ⊢· (rename ρ ⊢A⇒B) (rename ρ ⊢A)
rename {Δ = Δ} ρ ⊢zero = ⊢zero
rename {Δ = Δ} ρ (⊢suc ⊢t) = ⊢suc (rename ρ ⊢t)

-- Weakening of contexts.
weaken : ∀ {Γ t A}
  → ∅ ⊢ t ⦂ A
    ---------
  → Γ ⊢ t ⦂ A
weaken {Γ} ⊢A = rename (λ ()) ⊢A

-- Swapping variables in a context.
swap : ∀ {Γ x y t A B C}
  → x ≢ y
  → Γ , y ⦂ B , x ⦂ A ⊢ t ⦂ C
    ------------------------
  → Γ , x ⦂ A , y ⦂ B ⊢ t ⦂ C
swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢t = rename ρ ⊢t
  where
    ρ : ∀ {z C}
      → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ C
        --------------------------
      → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ C
    ρ (H refl) = T x≢y (H′)
    ρ (T z≢x (H refl)) = H′
    ρ (T z≢x (T z≢y ∋z)) = T z≢y (T z≢x ∋z)

-- Dropping shadowed variables.
drop : ∀ {Γ x M A B C}
  → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
    ------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C
drop {Γ} {x} {M} {A} {B} {C} ⊢M = rename ρ ⊢M
  where
    ρ : ∀ {z C}
      → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C
        -------------------------
      → Γ , x ⦂ B ∋ z ⦂ C
    ρ (H refl) = H refl
    ρ (T z≢x (H x≡z)) = contradiction (sym x≡z) z≢x
    ρ (T z≢x (T _ ∋z)) = T z≢x ∋z

-- subst-open-var adapted to work with judgements.
subst-open-context : ∀ {Γ A} {t u : Term} {x y : Id}
  → x ≢ y
  → LocallyClosed u
  → Γ ⊢ [ x := u ] ([ 0 —→ y ] t) ⦂ A
    ---------------------------------
  → Γ ⊢ [ 0 —→ y ] ([ x := u ] t) ⦂ A
subst-open-context {t = t} x≢y lc-u sub-open =
  ≡-with-⊢ sub-open (subst-open-var t x≢y lc-u)
