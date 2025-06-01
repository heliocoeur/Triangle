{-# OPTIONS --without-K --safe #-}
module TriangleSubstraction where

open import Core
open import TriangleIVecStructureGeneralized
open import Agda.Primitive using (_⊔_; lzero; Level)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)

variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  I : Set ℓ₁
  A : I → Set ℓ₂

-- Disjonction (si pas dans Core)
data _⊎_ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- ================================
-- SOUSTRACTION DU TRIANGLE pour IVec
-- ================================

module IVecLogicalSubtraction
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
  {I : Set ℓ₁}
  {A : I → Set ℓ₂}
  (P : ∀ {i} → A i → Set ℓ₃)
  (R : ∀ {n} {is : Vec I n} → IVec A is → Set ℓ₄)
  (n : Nat)
  (iln : ILn A P n R)
  where

  -- DP : négation de IAll P (au moins un élément ne satisfait pas P)
  IDP : ∀ {m} {is : Vec I m} → IVec A is → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
  IDP xs = IAll P xs → ⊥ {ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄}

  -- Forme existentielle : il existe un vecteur indexé xs tel que R(xs) et IDP(xs)
  IForme-Existentielle : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
  IForme-Existentielle = Σ (Σ Nat (λ m → Σ (Vec I m) (λ is → IVec A is)))
                           (λ { (m , is , xs) → (R xs) × (IDP xs) })

  -- Base intuitionniste I : (IO et ITn) implique non ILn
  II : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
  II = (IO A P × ITn A R) → ¬ (ILn A P n R)

  -- Dérivation de II (directe depuis le triangle)
  derivation-II : II
  derivation-II (io , itn) iln = itriangle {ℓ₅ = ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄} io iln itn

  -- Théorème classique ICL : (IO et ITn) implique IForme-Existentielle
  ICL : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
  ICL = (IO A P × ITn A R) → IForme-Existentielle

  -- ================================
  -- Construction rigoureuse du témoin
  -- ================================

  -- Fonction auxiliaire pour n = 0
  itemoin-zero : IO A P → ITn A R → IForme-Existentielle
  itemoin-zero (i , x , ¬Px) itn =
    let xs = x ∷ᵢ []ᵢ  -- Vecteur singleton
        R-xs = itn xs    -- R tient pour ce vecteur par ITn
        IDP-xs : IDP xs
        IDP-xs = λ { (px , _) → ⊥-elim {ℓ = ℓ₃} {ℓ' = ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄} (¬Px px) }  -- Conversion du niveau
    in (1 , i ∷ [] , xs) , (R-xs , IDP-xs)

  -- Fonction auxiliaire pour n = suc m
  itemoin-suc : ∀ m → IO A P → ITn A R → IForme-Existentielle
  itemoin-suc m (i , x , ¬Px) itn =
    let k = suc m
        xs = ireplicateConst {n = k} i x  -- k copies de x avec index i
        R-xs = itn xs    -- R tient par ITn
        IDP-xs : IDP xs
        IDP-xs = λ iall-P-xs → ⊥-elim {ℓ = ℓ₃} {ℓ' = ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄} (¬Px (iheadAll iall-P-xs))  -- Conversion du niveau
    in (k , replicate {n = k} i , xs) , (R-xs , IDP-xs)

  -- Construction du témoin par analyse de cas sur n
  iconstruction-temoin : IO A P → ITn A R → IForme-Existentielle
  iconstruction-temoin io itn = aux n io itn
    where
      aux : (k : Nat) → IO A P → ITn A R → IForme-Existentielle
      aux zero io' itn' = itemoin-zero io' itn'
      aux (suc m) io' itn' = itemoin-suc m io' itn'

  -- Dérivation de ICL - COMPLÈTEMENT RIGOUREUSE
  derivation-ICL : ICL
  derivation-ICL (io , itn) = iconstruction-temoin io itn

  -- ================================
  -- IDelta : non ILn implique IForme-Existentielle
  -- ================================

  IDelta : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
  IDelta = ¬ (ILn A P n R) → IForme-Existentielle

  -- Construction de IDelta à partir des prémisses
  IDelta-construction : (IO A P × ITn A R) → IDelta
  IDelta-construction prémisses ¬iln = derivation-ICL prémisses

  -- ================================
  -- Vérification de la décomposition
  -- ================================

  -- Vérifier ¬ILn à partir de IForme-Existentielle pour n = 0
  iverif-¬ILn-zero : IForme-Existentielle → IO A P → ITn A R → ¬ (ILn A P zero R)
  iverif-¬ILn-zero ((m , is , xs) , (R-xs , IDP-xs)) (i , x , ¬Px) itn iln-zero =
    -- Pour n = 0, ILn dit : ∀ {i} {x} → R []ᵢ → P x
    -- Donc pour tout vecteur ys, on peut construire IAll P ys
    let all-P-xs : IAll P xs
        all-P-xs = construct-IAll-from-iln-zero xs
    in IDP-xs all-P-xs
    where
      construct-IAll-from-iln-zero : ∀ {m} {is : Vec I m} (ys : IVec A is) → IAll P ys
      construct-IAll-from-iln-zero []ᵢ = unit
      construct-IAll-from-iln-zero (_∷ᵢ_ {i = j} z zs) =
        (iln-zero {j} {z} (itn []ᵢ)) , construct-IAll-from-iln-zero zs

  -- Vérifier ¬ILn à partir de IForme-Existentielle pour n = suc k
  iverif-¬ILn-suc : ∀ k → IForme-Existentielle → ¬ (ILn A P (suc k) R)
  iverif-¬ILn-suc k ((m , is , xs) , (R-xs , IDP-xs)) iln-suc =
    -- Pour n ≥ 1, ILn dit : ∀ xs → R xs → IAll P xs
    -- On a R xs et IDP xs (= ¬IAll P xs)
    -- Donc iln-suc xs R-xs devrait donner IAll P xs
    -- Mais IDP-xs dit ¬IAll P xs, contradiction
    IDP-xs (iln-suc xs R-xs)

  -- Équivalence logique
  _↔_ : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
  A ↔ B = (A → B) × (B → A)

  -- Vérification complète de la décomposition
  iverification-decomposition :
    (prémisses : IO A P × ITn A R) →
    IForme-Existentielle ↔ ((¬ (ILn A P n R)) × IDelta)
  iverification-decomposition prémisses@(io , itn) = (sens1 , sens2)
    where
      sens1 : IForme-Existentielle → ((¬ (ILn A P n R)) × IDelta)
      sens1 forme-ex = (¬iln , idelta)
        where
          ¬iln : ¬ (ILn A P n R)
          ¬iln = aux n forme-ex
            where
              aux : (k : Nat) → IForme-Existentielle → ¬ (ILn A P k R)
              aux zero fe = iverif-¬ILn-zero fe io itn
              aux (suc m) fe = iverif-¬ILn-suc m fe

          idelta : IDelta
          idelta _ = forme-ex

      sens2 : ((¬ (ILn A P n R)) × IDelta) → IForme-Existentielle
      sens2 (¬iln , idelta) = idelta ¬iln

-- ================================
-- THÉORÈME DE SOUSTRACTION DU TRIANGLE pour IVec
-- ================================

-- Construction du théorème principal
itheoreme-soustraction-principal :
  ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
    {I : Set ℓ₁}
    {A : I → Set ℓ₂}
    (P : ∀ {i} → A i → Set ℓ₃)
    (R : ∀ {n} {is : Vec I n} → IVec A is → Set ℓ₄)
    (n : Nat)
    (iln : ILn A P n R)
    (prémisses : IO A P × ITn A R)
  → IVecLogicalSubtraction.IForme-Existentielle P R n iln
    × (¬ (ILn A P n R))
itheoreme-soustraction-principal P R n iln prémisses@(io , itn) =
  let open IVecLogicalSubtraction P R n iln
      témoin = derivation-ICL prémisses
      ¬iln = derivation-II prémisses
  in témoin , ¬iln

-- ================================
-- COROLLAIRE : Le dilemme est maintenant rigoureusement prouvé
-- ================================

-- Si on a les prémisses (IO et ITn), alors on peut construire
-- soit ¬ILn (via II), soit un témoin explicite (via ICL)
idilemme-constructif :
  ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
    {I : Set ℓ₁}
    {A : I → Set ℓ₂}
    (P : ∀ {i} → A i → Set ℓ₃)
    (R : ∀ {n} {is : Vec I n} → IVec A is → Set ℓ₄)
    (n : Nat)
    (iln : ILn A P n R)
  → (prémisses : IO A P × ITn A R)
  → (¬ (ILn A P n R)) × IVecLogicalSubtraction.IForme-Existentielle P R n iln
idilemme-constructif P R n iln prémisses@(io , itn) =
  let open IVecLogicalSubtraction P R n iln
      ¬iln = derivation-II prémisses
      témoin = derivation-ICL prémisses
  in ¬iln , témoin