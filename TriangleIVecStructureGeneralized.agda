{-# OPTIONS --without-K --safe #-}

{-
  Generalized Incompatibility Triangle for Indexed Vectors
  ========================================================
  
  This module implements the incompatibility triangle theory:
  (O ∧ Lₙ ∧ Tₙ) ⊢ ⊥
  
  where:
  - O  ≡ ∃x. ¬P(x)                    -- Existence of a counterexample
  - Lₙ ≡ ∀x₁...xₙ. R(x₁...xₙ) → ∧P(xᵢ) -- Locality (P propagates via R)
  - Tₙ ≡ ∀x₁...xₙ. R(x₁...xₙ)         -- Totality (R is universal)
  
  The generalization to indexed types allows heterogeneity:
  different types at different positions in vectors.
-}

module TriangleIVecStructureGeneralized where

open import Core
open import Agda.Primitive using (_⊔_; lzero; Level; lsuc)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- ================================
-- IAll: The generalized ∧P(xᵢ) predicate
-- ================================
-- Implements the conjunction P(x₁) ∧ ... ∧ P(xₙ) for indexed vectors
-- where each xᵢ can have a different type A(i)
IAll : ∀ {ℓ₁ ℓ₂ ℓ₃} {I : Set ℓ₁} {A : I → Set ℓ₂}
       → (∀ {i} → A i → Set ℓ₃) → ∀ {n} {is : Vec I n} → IVec A is → Set ℓ₃
IAll {ℓ₃ = ℓ₃} P {is = []} []ᵢ = Unit {ℓ₃}
IAll P {is = i ∷ is} (x ∷ᵢ xs) = P {i} x × IAll P xs

-- Extract the first element from the conjunction
iheadAll : ∀ {ℓ₁ ℓ₂ ℓ₃} {I : Set ℓ₁} {A : I → Set ℓ₂} {P : ∀ {i} → A i → Set ℓ₃}
           {i n} {is : Vec I n} {x : A i} {xs : IVec A is}
         → IAll P (x ∷ᵢ xs) → P x
iheadAll (px , _) = px

-- ================================
-- Triangle Formulas Generalized
-- ================================

{-
  IO : Implementation of O ≡ ∃x. ¬P(x)
  
  In the indexed context:
  - ∃i:I. ∃x:A(i). ¬P(x)
  - There exists an index i and an element x of type A(i) 
    that does not satisfy P
-}
IO : ∀ {ℓ₁ ℓ₂ ℓ₃} {I : Set ℓ₁} (A : I → Set ℓ₂) → (∀ {i} → A i → Set ℓ₃) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
IO {I = I} A P = Σ I (λ i → Σ (A i) (λ x → ¬ (P x)))

{-
  ILn : Implementation of Lₙ ≡ ∀x₁...xₙ. R(x₁...xₙ) → (P(x₁) ∧ ... ∧ P(xₙ))
  
  Parameterized by n (the arity of the relation):
  - n = 0 : Degenerate case, R([]) → P(x) for all x
  - n > 0 : For all vectors xs, if R(xs) then all elements 
            of xs satisfy P
  
  This is the locality principle: the local property P propagates
  through the global relation R.
-}
ILn : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {I : Set ℓ₁} (A : I → Set ℓ₂) → (∀ {i} → A i → Set ℓ₃) → Nat
    → (∀ {m} {is : Vec I m} → IVec A is → Set ℓ₄) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
ILn {I = I} A P zero R = ∀ {i} {x : A i} → R []ᵢ → P x
ILn {I = I} A P (suc n) R = ∀ {m} {is : Vec I m} (xs : IVec A is) → R xs → IAll P xs

{-
  ITn : Implementation of Tₙ ≡ ∀x₁...xₙ. R(x₁...xₙ)
  
  Totality: R holds for ALL possible indexed vectors.
  This creates the tension with O (existence of counterexample)
  and Lₙ (propagation of P).
-}
ITn : ∀ {ℓ₁ ℓ₂ ℓ₃} {I : Set ℓ₁} (A : I → Set ℓ₂)
    → (∀ {m} {is : Vec I m} → IVec A is → Set ℓ₃) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
ITn {I = I} A R = ∀ {m} {is : Vec I m} (xs : IVec A is) → R xs

-- Helper: Build a constant vector (repetition of one element)
-- Used in the proof to construct a witness for contradiction
ireplicateConst : ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} {A : I → Set ℓ₂} {n} (i : I) → A i → IVec A (replicate {n = n} i)
ireplicateConst {n = zero} i x = []ᵢ
ireplicateConst {n = suc n} i x = x ∷ᵢ ireplicateConst i x

{-
  Incompatibility Triangle Theorem
  ================================
  
  (O ∧ Lₙ ∧ Tₙ) ⊢ ⊥
  
  Intuitive proof:
  1. O gives us a counterexample: ∃i,x. ¬P(x)
  2. Tₙ says R is total, so R([x,x,...,x]) holds
  3. Lₙ says if R([x,x,...,x]) then P(x) ∧ P(x) ∧ ... ∧ P(x)
  4. Therefore P(x), but we have ¬P(x) from O. Contradiction!
  
  The constructive proof uses ireplicateConst to build
  the vector [x,x,...,x] that leads to contradiction.
-}
itriangle : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅} {I : Set ℓ₁} {A : I → Set ℓ₂} {P : ∀ {i} → A i → Set ℓ₃} {n}
          {R : ∀ {m} {is : Vec I m} → IVec A is → Set ℓ₄}
          → IO A P → ILn A P n R → ITn A R → ⊥ {ℓ₅}
itriangle {I = I} {A} {P} {zero} {R} (i , x , ¬Px) iln itn = 
  -- Case n=0: Direct since Lₙ says R([]) → P(x)
  ⊥-elim (¬Px (iln {i = i} {x = x} (itn []ᵢ)))
itriangle {I = I} {A} {P} {suc n} {R} (i , x , ¬Px) iln itn =
  -- Case n>0: Build [x,x,...,x] and extract P(x) from IAll P [x,x,...,x]
  let xs = ireplicateConst {n = suc n} i x in
  ⊥-elim (¬Px (iheadAll (iln xs (itn xs))))

-- ================================
-- Consequences: Binary Operations
-- ================================
{-
  The triangle reveals that Tₙ forces saturation:
  If R is total, then R is closed under operations.
  
  Intuition: If R(xs) for all xs, then R(xs ⊕ ys) too!
-}
module IBinaryOps {ℓ₁ ℓ₂} {I : Set ℓ₁} {A : I → Set ℓ₂} (_⊕_ : ∀ {i} → A i → A i → A i) where

  -- Position-wise application of a binary operation
  izipWith : ∀ {n} {is : Vec I n} → IVec A is → IVec A is → IVec A is
  izipWith []ᵢ []ᵢ = []ᵢ
  izipWith (_∷ᵢ_ {i = i} x xs) (_∷ᵢ_ y ys) = (_⊕_ {i} x y) ∷ᵢ izipWith xs ys

  -- Theorem: ITn implies closure of R under ⊕
  ITn-closure : ∀ {ℓ₃} {R : ∀ {m} {is : Vec I m} → IVec A is → Set ℓ₃}
                {n} {is : Vec I n} (xs ys : IVec A is)
              → ITn A R → R (izipWith xs ys)
  ITn-closure xs ys itn = itn (izipWith xs ys)

  -- Corollary: Non-closure contradicts ITn
  icomplementary-from-ITn : ∀ {ℓ₃ ℓ₄} {n} {is : Vec I n} (xs ys : IVec A is)
                           (R : ∀ {m} {js : Vec I m} → IVec A js → Set ℓ₃)
                         → ITn A R → ¬ R (izipWith xs ys) → ⊥ {ℓ₄}
  icomplementary-from-ITn xs ys R itn ¬r = ⊥-elim (¬r (ITn-closure xs ys itn))

-- ================================
-- Saturation and Triangle
-- ================================
{-
  Saturation is a key property revealed by the triangle:
  
  R is saturated iff: ∀xs,ys. R(xs) → R(ys) → R(xs ⊕ ys)
  
  The triangle shows that Tₙ (totality) implies saturation.
  This is a manifestation of the tension between local and global.
-}
module ISaturation {ℓ₁ ℓ₂} {I : Set ℓ₁} {A : I → Set ℓ₂} where

  -- Definition of saturation for a relation R
  ISaturated : ∀ {ℓ₃} → (∀ {n} {is : Vec I n} → IVec A is → IVec A is → IVec A is)
             → (∀ {m} {is : Vec I m} → IVec A is → Set ℓ₃) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  ISaturated _⊕_ R = ∀ {n} {is : Vec I n} (xs ys : IVec A is) → R xs → R ys → R (xs ⊕ ys)

  -- Theorem: ITn implies saturation
  -- This is a direct consequence of the incompatibility triangle
  ITn-implies-saturated : ∀ {ℓ₃} (_⊕_ : ∀ {i} → A i → A i → A i)
                          {R : ∀ {m} {is : Vec I m} → IVec A is → Set ℓ₃}
                        → let open IBinaryOps _⊕_ in
                          ITn A R → ISaturated izipWith R
  ITn-implies-saturated _⊕_ itn xs ys rx ry = itn _

-- ================================
-- Concrete Example: Heterogeneous Bits
-- ================================
{-
  Illustration of the triangle with bits having different semantics.
  Shows that the triangle applies even with heterogeneity.
-}
module HetBitExample where

  -- Bit types with different semantics
  data BitType : Set where
    standard : BitType              -- 0=false, 1=true (normal)
    inverted : BitType              -- 0=true, 1=false (inverted)

  -- Type family (all Bool but interpreted differently)
  BitFamily : BitType → Set
  BitFamily standard = Bool
  BitFamily inverted = Bool

  -- XOR operation adapted to each type
  _⊕ₕ_ : ∀ {bt} → BitFamily bt → BitFamily bt → BitFamily bt
  _⊕ₕ_ {standard} false false = false
  _⊕ₕ_ {standard} _ _ = true
  _⊕ₕ_ {inverted} true true = true    -- true represents 0 in inverted
  _⊕ₕ_ {inverted} _ _ = false

  -- Property P: "represents the true value"
  -- Adapted according to bit type
  IsTrue : ∀ {bt} → BitFamily bt → Set
  IsTrue {standard} true = Unit {lzero}
  IsTrue {standard} false = ⊥ {lzero}
  IsTrue {inverted} false = Unit {lzero}  -- false represents 1=true in inverted
  IsTrue {inverted} true = ⊥ {lzero}

  -- Heterogeneous vector mixing types
  exampleVec : IVec BitFamily (standard ∷ inverted ∷ standard ∷ [])
  exampleVec = true ∷ᵢ false ∷ᵢ false ∷ᵢ []ᵢ

  -- Example where all elements satisfy IsTrue
  allTrueExample : IVec BitFamily (standard ∷ inverted ∷ [])
  allTrueExample = true ∷ᵢ false ∷ᵢ []ᵢ

  -- Proof that IAll IsTrue holds
  allTrueProof : IAll IsTrue allTrueExample
  allTrueProof = unit , (unit , unit)

-- ================================
-- Connection to Homogeneous Case
-- ================================
{-
  Shows that our generalization properly captures the classical case
  where all elements have the same type.
-}
module HomogeneousConnection where

  -- Homogeneous version of IAll
  All : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → (A → Set ℓ₂) → ∀ {n} → Vec A n → Set ℓ₂
  All {ℓ₂ = ℓ₂} P {n = zero} [] = Unit {ℓ₂}
  All P {n = suc n} (x ∷ xs) = P x × All P xs

  -- Convert Vec → IVec with constant index
  vecToIVec : ∀ {ℓ} {A : Set ℓ} {n} → Vec A n → IVec {ℓ₁ = lzero} {ℓ₂ = ℓ} {I = Unit} (λ _ → A) (replicate {n = n} unit)
  vecToIVec [] = []ᵢ
  vecToIVec (x ∷ xs) = x ∷ᵢ vecToIVec xs

  -- All translates naturally to IAll
  allToIAll : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} {n} {xs : Vec A n}
            → All P xs → IAll {ℓ₁ = lzero} {ℓ₂ = ℓ₁} {I = Unit} {A = λ _ → A} (λ {_} → P) (vecToIVec xs)
  allToIAll {xs = []} _ = unit
  allToIAll {xs = x ∷ xs} (px , pxs) = px , allToIAll pxs

-- ================================
-- General Insights from the Triangle
-- ================================
{-
  The incompatibility triangle reveals deep principles:
  
  1. Fundamental tension between local (P) and global (R)
  2. Totality (Tₙ) forces structural constraints (saturation)
  3. The existence of counterexamples (O) is incompatible with 
     universal propagation (Lₙ) under totality (Tₙ)
  
  These principles transcend implementation details and
  apply to the most general data structures.
-}
module ITriangleInsights where
  open ISaturation

  -- Key insight: ITn forces saturation even for heterogeneous types
  insight-general : ∀ {ℓ₁ ℓ₂ ℓ₃} {I : Set ℓ₁} {A : I → Set ℓ₂}
                    (_⊕_ : ∀ {i} → A i → A i → A i)
                    {R : ∀ {m} {is : Vec I m} → IVec A is → Set ℓ₃}
                  → ITn A R → ISaturated (IBinaryOps.izipWith _⊕_) R
  insight-general _⊕_ = ITn-implies-saturated _⊕_
