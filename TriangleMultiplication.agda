{-# OPTIONS --without-K --safe #-}

{-
  Triangle Multiplication (Product ⋆) for Indexed Vectors
  =======================================================

  This module implements the logical product operation ⋆ from the
  incompatibility triangle algebra, generalized to indexed vectors.

  Based on the formal theory:
  - O ≡ ∃x. ¬P(x)
  - Lₙ ≡ ∀x₁,...,xₙ. R(x₁,...,xₙ) → (P(x₁) ∧ ... ∧ P(xₙ))
  - Tₙ ≡ ∀x₁,...,xₙ. R(x₁,...,xₙ)

  The product ⋆ implements:
  - O ⋆ Tₙ ≡ ¬Lₙ (constructive form)
  - O ⋆ Lₙ ≡ ¬Tₙ
  - Lₙ ⋆ Tₙ ≡ ¬O
  - Φ ⋆ ¬Φ ≡ ⊥ (contradiction)
-}

module TriangleMultiplication where

open import Core
open import TriangleIVecStructureGeneralized
open import Agda.Primitive using (_⊔_; lzero; Level; lsuc)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- ================================
-- Formula Types for the Algebra
-- ================================

data IFormula {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} {I : Set ℓ₁} (A : I → Set ℓ₂)
              (P : ∀ {i} → A i → Set ℓ₃)
              (R : ∀ {n} {is : Vec I n} → IVec A is → Set ℓ₄)
              (n : Nat) : Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
  FO     : IFormula A P R n                    -- O ≡ ∃x. ¬P(x)
  FLn    : IFormula A P R n                    -- Lₙ ≡ ∀xs. R(xs) → IAll P xs
  FTn    : IFormula A P R n                    -- Tₙ ≡ ∀xs. R(xs)
  FNegO  : IFormula A P R n                    -- ¬O ≡ ∀x. P(x)
  FNegLn : IFormula A P R n                    -- ¬Lₙ
  FNegTn : IFormula A P R n                    -- ¬Tₙ

-- ================================
-- The Logical Product ⋆
-- ================================

module ILogicalProduct
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
  {I : Set ℓ₁}
  {A : I → Set ℓ₂}
  (P : ∀ {i} → A i → Set ℓ₃)
  (R : ∀ {n} {is : Vec I n} → IVec A is → Set ℓ₄)
  (n : Nat)
  where

  -- ================================
  -- Core definitions from theory
  -- ================================

  -- O: ∃x. ¬P(x)
  O-def : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  O-def = IO A P

  -- Lₙ: ∀xs. R(xs) → IAll P xs
  Ln-def : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
  Ln-def = ILn A P n R

  -- Tₙ: ∀xs. R(xs)
  Tn-def : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄)
  Tn-def = ITn A R

  -- ¬O: ∀x. P(x)
  NegO-def : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  NegO-def = ∀ {i} (x : A i) → P x

  -- ================================
  -- Lift types to the maximum level
  -- ================================

  -- The maximum level for all our types
  ℓmax : Level
  ℓmax = ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄

  -- Lift a type to a higher universe level
  record Lift {a} ℓ (A : Set a) : Set (a ⊔ ℓ) where
    constructor lift
    field lower : A

  -- Lift our core types to the maximum level
  O-lifted : Set ℓmax
  O-lifted = Lift ℓ₄ O-def

  NegO-lifted : Set ℓmax
  NegO-lifted = Lift ℓ₄ NegO-def

  Tn-lifted : Set ℓmax
  Tn-lifted = Lift (ℓ₃) Tn-def

  -- ================================
  -- Constructive forms of negations
  -- ================================

  -- ¬Lₙ constructive: ∃xs. R(xs) ∧ (∃i. ¬P(xsᵢ))
  -- In our indexed setting, this becomes:
  NegLn-constructive : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
  NegLn-constructive = Σ Nat (λ m → Σ (Vec I m) (λ is → Σ (IVec A is)
                         (λ xs → R xs × (¬ IAll P xs))))

  -- ¬Tₙ constructive: ∃xs. ¬R(xs)
  NegTn-constructive : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄)
  NegTn-constructive = Σ Nat (λ m → Σ (Vec I m) (λ is → Σ (IVec A is)
                         (λ xs → ¬ R xs)))

  -- Helper for contradiction case
  IContradiction : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  IContradiction = O-def × NegO-def

  -- ================================
  -- Product operation definition
  -- ================================

  _⋆_ : (Φ₁ Φ₂ : IFormula A P R n) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)

  -- Case 1: Contradictions Φ ⋆ ¬Φ (lift to max level)
  FO ⋆ FNegO = O-lifted × NegO-lifted
  FNegO ⋆ FO = O-lifted × NegO-lifted
  FLn ⋆ FNegLn = Ln-def × (¬ Ln-def)
  FNegLn ⋆ FLn = Ln-def × (¬ Ln-def)
  FTn ⋆ FNegTn = Tn-lifted × Lift (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) (¬ Tn-def)
  FNegTn ⋆ FTn = Tn-lifted × Lift (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) (¬ Tn-def)

  -- Case 2: Triangle-specific products
  FO ⋆ FTn = NegLn-constructive  -- ¬Lₙ
  FTn ⋆ FO = NegLn-constructive  -- ¬Lₙ

  FO ⋆ FLn = Lift ℓ₃ NegTn-constructive  -- ¬Tₙ (lifted)
  FLn ⋆ FO = Lift ℓ₃ NegTn-constructive  -- ¬Tₙ (lifted)

  FLn ⋆ FTn = Lift ℓ₄ NegO-def  -- ¬O (lifted)
  FTn ⋆ FLn = Lift ℓ₄ NegO-def  -- ¬O (lifted)

  -- Case 3: Default to conjunction (all lifted to max level)
  FO ⋆ FO = O-lifted × O-lifted
  FO ⋆ FNegLn = O-lifted × (¬ Ln-def)
  FO ⋆ FNegTn = O-lifted × Lift (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) (¬ Tn-def)

  FLn ⋆ FLn = Ln-def × Ln-def
  FLn ⋆ FNegO = Ln-def × NegO-lifted
  FLn ⋆ FNegTn = Ln-def × Lift (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) (¬ Tn-def)

  FTn ⋆ FTn = Tn-lifted × Tn-lifted
  FTn ⋆ FNegO = Tn-lifted × NegO-lifted
  FTn ⋆ FNegLn = Tn-lifted × (¬ Ln-def)

  FNegO ⋆ FNegO = NegO-lifted × NegO-lifted
  FNegO ⋆ FLn = NegO-lifted × Ln-def
  FNegO ⋆ FTn = NegO-lifted × Tn-lifted
  FNegO ⋆ FNegLn = NegO-lifted × (¬ Ln-def)
  FNegO ⋆ FNegTn = NegO-lifted × Lift (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) (¬ Tn-def)

  FNegLn ⋆ FO = (¬ Ln-def) × O-lifted
  FNegLn ⋆ FNegLn = (¬ Ln-def) × (¬ Ln-def)
  FNegLn ⋆ FNegO = (¬ Ln-def) × NegO-lifted
  FNegLn ⋆ FTn = (¬ Ln-def) × Tn-lifted
  FNegLn ⋆ FNegTn = (¬ Ln-def) × Lift (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) (¬ Tn-def)

  FNegTn ⋆ FO = Lift (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) (¬ Tn-def) × O-lifted
  FNegTn ⋆ FNegTn = Lift (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) (¬ Tn-def) × Lift (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) (¬ Tn-def)
  FNegTn ⋆ FNegO = Lift (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) (¬ Tn-def) × NegO-lifted
  FNegTn ⋆ FLn = Lift (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) (¬ Tn-def) × Ln-def
  FNegTn ⋆ FNegLn = Lift (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) (¬ Tn-def) × (¬ Ln-def)

  -- ================================
  -- Constructive implementations
  -- ================================

  -- Implementation for O ⋆ Tₙ = ¬Lₙ
  -- From the theory: O ∧ Tₙ ⊢ ∃x₁,...,xₙ.(R(x₁,...,xₙ) ∧ (∨ᵏ₌₁ⁿ ¬P(xₖ)))
  construct-O⋆Tn : O-def → Tn-def → NegLn-constructive
  construct-O⋆Tn (i , x , ¬Px) itn = k , is , xs , r-xs , not-all-p
    where
      -- For any n, we use a vector of size (suc n) to ensure we have elements
      -- This gives us a concrete witness for ¬Lₙ
      k = suc n
      is = replicate {n = k} i
      xs = ireplicateConst {n = k} i x
      r-xs = itn xs
      not-all-p : ¬ IAll P xs
      not-all-p (px , _) = ¬Px px  -- First element contradicts

  -- Implementation for Lₙ ⋆ Tₙ = ¬O
  construct-Ln⋆Tn : Ln-def → Tn-def → NegO-def
  construct-Ln⋆Tn = construct-Ln⋆Tn-aux n
    where
      construct-Ln⋆Tn-aux : ∀ k → ILn A P k R → ITn A R → NegO-def
      construct-Ln⋆Tn-aux zero iln itn {i} x = iln {i} {x} (itn []ᵢ)
      construct-Ln⋆Tn-aux (suc k) iln itn {i} x =
        let xs = ireplicateConst {n = suc k} i x
            r-xs = itn xs
            all-p = iln xs r-xs
        in iheadAll all-p

  -- Implementation for O ⋆ Lₙ = ¬Tₙ
  construct-O⋆Ln : O-def → Ln-def → NegTn-constructive
  construct-O⋆Ln (i , x , ¬Px) = construct-O⋆Ln-aux n (i , x , ¬Px)
    where
      construct-O⋆Ln-aux : ∀ k → IO A P → ILn A P k R → NegTn-constructive
      construct-O⋆Ln-aux zero (i , x , ¬Px) iln =
        zero , [] , []ᵢ , λ r → ¬Px (iln {i} {x} r)
      construct-O⋆Ln-aux (suc k) (i , x , ¬Px) iln =
        let is = i ∷ []
            xs = x ∷ᵢ []ᵢ
            ¬r : ¬ R xs
            ¬r r = let all-p = iln xs r
                   in ¬Px (iheadAll all-p)
        in 1 , is , xs , ¬r

  -- ================================
  -- Properties of the Product
  -- ================================

  -- Show that contradiction is impossible
  contradiction-impossible : IContradiction → ⊥ {ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃}
  contradiction-impossible ((i , x , ¬Px) , all-P) = ¬Px (all-P x)

  -- Commutativity of product (type level)
  ⋆-comm-type : (Φ₁ Φ₂ : IFormula A P R n) → (Φ₁ ⋆ Φ₂) ≡ (Φ₂ ⋆ Φ₁)
  ⋆-comm-type FO FO = refl
  ⋆-comm-type FO FLn = refl
  ⋆-comm-type FO FTn = refl
  ⋆-comm-type FO FNegO = refl
  ⋆-comm-type FO FNegLn = refl
  ⋆-comm-type FO FNegTn = refl
  ⋆-comm-type FLn FO = refl
  ⋆-comm-type FLn FLn = refl
  ⋆-comm-type FLn FTn = refl
  ⋆-comm-type FLn FNegO = refl
  ⋆-comm-type FLn FNegLn = refl
  ⋆-comm-type FLn FNegTn = refl
  ⋆-comm-type FTn FO = refl
  ⋆-comm-type FTn FLn = refl
  ⋆-comm-type FTn FTn = refl
  ⋆-comm-type FTn FNegO = refl
  ⋆-comm-type FTn FNegLn = refl
  ⋆-comm-type FTn FNegTn = refl
  ⋆-comm-type FNegO FO = refl
  ⋆-comm-type FNegO FLn = refl
  ⋆-comm-type FNegO FTn = refl
  ⋆-comm-type FNegO FNegO = refl
  ⋆-comm-type FNegO FNegLn = refl
  ⋆-comm-type FNegO FNegTn = refl
  ⋆-comm-type FNegLn FO = refl
  ⋆-comm-type FNegLn FLn = refl
  ⋆-comm-type FNegLn FTn = refl
  ⋆-comm-type FNegLn FNegO = refl
  ⋆-comm-type FNegLn FNegLn = refl
  ⋆-comm-type FNegLn FNegTn = refl
  ⋆-comm-type FNegTn FO = refl
  ⋆-comm-type FNegTn FLn = refl
  ⋆-comm-type FNegTn FTn = refl
  ⋆-comm-type FNegTn FNegO = refl
  ⋆-comm-type FNegTn FNegLn = refl
  ⋆-comm-type FNegTn FNegTn = refl

  -- The triangle theorem via product
  triangle-via-product : O-def → Ln-def → Tn-def → ⊥ {ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄}
  triangle-via-product io iln itn =
    itriangle {ℓ₅ = ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄} io iln itn

-- ================================
-- Example Usage
-- ================================

module ExampleProduct where
  -- Use Bool from Core instead of importing Agda.Builtin.Bool
  -- This avoids the ambiguity

  -- Simple property: being true (using Bool from Core)
  IsTrue : Bool → Set
  IsTrue true = Unit {lzero}
  IsTrue false = ⊥ {lzero}

  -- Simple relation: all elements are equal
  AllEqualI : ∀ {n} {is : Vec Unit n} → IVec (λ _ → Bool) is → Set
  AllEqualI []ᵢ = Unit {lzero}
  AllEqualI (x ∷ᵢ []ᵢ) = Unit {lzero}
  AllEqualI (x ∷ᵢ y ∷ᵢ xs) = (x ≡ y) × AllEqualI (y ∷ᵢ xs)

  -- Open the product module
  open ILogicalProduct {I = Unit} {A = λ _ → Bool} (λ {_} → IsTrue) AllEqualI 2

  -- Example: O ⋆ Tₙ produces ¬Lₙ
  example-O⋆T : O-def → Tn-def → NegLn-constructive
  example-O⋆T = construct-O⋆Tn

  -- Example: The contradiction O ⋆ ¬O is impossible
  example-contradiction : O-def × NegO-def → ⊥ {lzero}
  example-contradiction = contradiction-impossible