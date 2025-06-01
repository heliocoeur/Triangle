{-# OPTIONS --without-K --safe #-}
module Core where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

-- ================================
-- Basic Types (Generalized)
-- ================================
data ⊥ {ℓ} : Set ℓ where

⊥-elim : ∀ {ℓ ℓ'} {A : Set ℓ'} → ⊥ {ℓ} → A
⊥-elim ()

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬_ {ℓ} A = A → ⊥ {ℓ}

record Unit {ℓ} : Set ℓ where
  constructor unit

_×_ : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
A × B = Σ A (λ _ → B)

-- ================================
-- Boolean Type
-- ================================
data Bool : Set where
  true false : Bool

-- ================================
-- Vectors (Polymorphic)
-- ================================
infixr 5 _∷_
data Vec {ℓ} (A : Set ℓ) : Nat → Set ℓ where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

replicate : ∀ {ℓ} {A : Set ℓ} {n} → A → Vec A n
replicate {n = zero} x = []
replicate {n = suc n} x = x ∷ replicate x

-- Append for regular vectors
_++_ : ∀ {ℓ} {A : Set ℓ} {m n} → Vec A m → Vec A n → Vec A (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- ================================
-- Indexed Vectors (Universe Polymorphic)
-- ================================
infixr 5 _∷ᵢ_
data IVec {ℓ₁ ℓ₂} {I : Set ℓ₁} (A : I → Set ℓ₂) : ∀ {n} → Vec I n → Set (ℓ₁ ⊔ ℓ₂) where
  []ᵢ  : IVec A []
  _∷ᵢ_ : ∀ {i n} {is : Vec I n} → A i → IVec A is → IVec A (i ∷ is)

-- ================================
-- IVec Operations
-- ================================

-- Map over indexed vectors
imapᵢ : ∀ {ℓ₁ ℓ₂ ℓ₃} {I : Set ℓ₁} {A : I → Set ℓ₂} {B : I → Set ℓ₃}
        {n} {is : Vec I n} →
        (∀ {i} → A i → B i) → IVec A is → IVec B is
imapᵢ f []ᵢ = []ᵢ
imapᵢ f (x ∷ᵢ xs) = f x ∷ᵢ imapᵢ f xs

-- Replicate for indexed vectors
ireplicateᵢ : ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} {A : I → Set ℓ₂} {n} {is : Vec I n} →
              (∀ i → A i) → IVec A is
ireplicateᵢ {is = []} f = []ᵢ
ireplicateᵢ {is = i ∷ is} f = f i ∷ᵢ ireplicateᵢ f

-- Fold over indexed vectors
ifoldᵢ : ∀ {ℓ₁ ℓ₂ ℓ₃} {I : Set ℓ₁} {A : I → Set ℓ₂} {B : Set ℓ₃}
         {n} {is : Vec I n} →
         (∀ {i} → A i → B → B) → B → IVec A is → B
ifoldᵢ f b []ᵢ = b
ifoldᵢ f b (x ∷ᵢ xs) = f x (ifoldᵢ f b xs)

-- Zip indexed vectors
izipᵢ : ∀ {ℓ₁ ℓ₂ ℓ₃} {I : Set ℓ₁} {A : I → Set ℓ₂} {B : I → Set ℓ₃}
        {n} {is : Vec I n} →
        IVec A is → IVec B is → IVec (λ i → A i × B i) is
izipᵢ []ᵢ []ᵢ = []ᵢ
izipᵢ (x ∷ᵢ xs) (y ∷ᵢ ys) = (x , y) ∷ᵢ izipᵢ xs ys

-- Head and tail for non-empty indexed vectors
iheadᵢ : ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} {A : I → Set ℓ₂} {i n} {is : Vec I n} →
         IVec A (i ∷ is) → A i
iheadᵢ (x ∷ᵢ _) = x

itailᵢ : ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} {A : I → Set ℓ₂} {i n} {is : Vec I n} →
         IVec A (i ∷ is) → IVec A is
itailᵢ (_ ∷ᵢ xs) = xs

-- Append indexed vectors
_++ᵢ_ : ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} {A : I → Set ℓ₂}
        {m n} {is : Vec I m} {js : Vec I n} →
        IVec A is → IVec A js → IVec A (is ++ js)
[]ᵢ ++ᵢ ys = ys
(x ∷ᵢ xs) ++ᵢ ys = x ∷ᵢ (xs ++ᵢ ys)

-- ================================
-- Dependent Pairs for IVec
-- ================================
IΣ : ∀ {ℓ₁ ℓ₂ ℓ₃} {I : Set ℓ₁} (A : I → Set ℓ₂) (B : ∀ i → A i → Set ℓ₃)
     {n} {is : Vec I n} →
     IVec A is → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
IΣ {ℓ₁} {ℓ₂} {ℓ₃} A B []ᵢ = Unit {ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃}
IΣ {ℓ₁} {ℓ₂} {ℓ₃} A B (_∷ᵢ_ {i = i} x xs) = Σ (B i x) (λ _ → IΣ {ℓ₁} {ℓ₂} {ℓ₃} A B xs)

-- ================================
-- Equality lemmas for IVec
-- ================================
IVec-≡ : ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} {A : I → Set ℓ₂}
         {n} {is js : Vec I n} →
         is ≡ js → IVec A is → IVec A js
IVec-≡ refl xs = xs

-- ================================
-- Helper functions
-- ================================
cong : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

-- Function composition
_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} →
      (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

-- Identity function
id : ∀ {ℓ} {A : Set ℓ} → A → A
id x = x

-- ================================
-- Example: Type-safe heterogeneous lists
-- ================================
module Example where
  -- Index type for our heterogeneous list
  data Type : Set where
    nat  : Type
    bool : Type

  -- Interpretation function
  El : Type → Set
  El nat  = Nat
  El bool = Bool

  -- Example heterogeneous list
  example : IVec El (nat ∷ bool ∷ nat ∷ [])
  example = zero ∷ᵢ true ∷ᵢ (suc zero) ∷ᵢ []ᵢ

  -- Another example with operations
  example2 : IVec El (bool ∷ bool ∷ [])
  example2 = false ∷ᵢ true ∷ᵢ []ᵢ

  -- Example of mapping
  not : Bool → Bool
  not true = false
  not false = true

  mapExample : ∀ {n} {is : Vec Type n} → IVec El is → IVec El is
  mapExample xs = imapᵢ {A = El} {B = El} f xs
    where
      f : ∀ {i} → El i → El i
      f {nat} n = suc n
      f {bool} b = not b