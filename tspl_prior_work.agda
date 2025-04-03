
module tspl_prior_work where
  open import plfa_adaptions
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

  private
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

  suc-preserves-≢ : ∀ {n m : ℕ} → n ≢ m → suc n ≢ suc m
  suc-preserves-≢ {n} {m} n≢m sn≡sm = n≢m (helper n m sn≡sm)
    where
      helper : ∀ (n m : ℕ) → suc n ≡ suc m → n ≡ m
      helper n m refl = refl

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
