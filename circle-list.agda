open import Data.Fin.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Vec.Base


-- empty type.
data ⊥ : Set where

~ : Set
  → Set
~ A
  = A → ⊥

  
data Dec (P : Set) : Set where
  yes : P
    → Dec P
  no : ~ P
    → Dec P


record Node (A : Set) (n : ℕ) : Set where 
    constructor
        node
    field
        val : A
        next : Maybe (Fin n)

LinkedList : Set → ℕ → Set
LinkedList A n = Vec (Node A n) n

data Lookup {A : Set} : ∀ {n} → Vec A n → Fin n → A → Set where
    zero : ∀ {x xs} → Lookup (x ∷ xs) zero x
    suc : ∀ {x xs k y} → Lookup xs k y → Lookup (x ∷ xs) (suc k) y

data Path {A n} (l : LinkedList A n) (i : Fin n) : Fin n → Set where
    one : ∀ {x j} → Lookup l i (node x (just j)) → Path l i j
    suc : ∀ {x j k} → Lookup l j (node x (just k)) → Path l i j → Path l i k

data Circular {A n} : LinkedList A n → Set where


floyd : ∀ {A n} → (l : LinkedList A n) → Dec (Circular l)
floyd = {!   !}

-- updateNext : {A : Set} → {n : ℕ} → Fin n → Vec (Node A n) n → Vec (Node A n) n
-- updateNext _ [] = []
-- updateNext _ ((node a _) ∷ []) = {!   !} -- (node a (just zero)) ∷ []
-- updateNext n ((node a m) ∷ xs) = {! (node a (suc n)) ∷ (updateNext (suc n) xs)  !}

-- append : {A : Set} → {n : ℕ} → A → Vec (Node A n) n → Vec (Node A n) (suc n)
-- append a [] = {! (Node a zero) ∷ [] !}
-- append a (x ∷ []) = {!   !}
-- append a (x ∷ xs) = {!   !}

