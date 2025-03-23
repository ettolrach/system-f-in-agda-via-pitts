module cofinite where

open import plfa_adaptions using (∉∷[]⇒≢)

-- Data types (naturals, strings, characters)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-total)
open import Data.Char using (Char)
open import Data.Char.Properties using () renaming (_≟_ to _≟char_)

-- Relations and predicates/decidability.
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable using (Dec)
open import Relation.Unary using (Decidable)
open import Relation.Binary using () renaming (Decidable to BinaryDecidable)
open import Relation.Nullary.Negation using (contradiction)

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

record Cof (P : List Char → Set) : Set where
  inductive
  eta-equality
  constructor И⟨_,_⟩
  field
    Иe₁ : List (List Char)
    Иe₂ : (a : List Char) {_ : a ∉ Иe₁} → P a
open Cof public

Cof-syntax : (P : List Char → Set) → Set
Cof-syntax = Cof
syntax Cof-syntax (λ a → P) = И a , P

simple-cof : {s : List Char} → И s , (1 ≤ length s)
simple-cof = И⟨ [] ∷ [] , (
  λ{[] {a∉}  → contradiction refl (∉∷[]⇒≢ a∉)
  ; (x ∷ xs) → s≤s z≤n}) ⟩
