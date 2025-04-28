open import Data.Fin.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Vec.Base

-- We got this from Data.Fin.Base in stdlib. Would not import correctly,
-- but code is at:
-- https://agda.github.io/agda-stdlib/master/Data.Fin.Base.html
data ordering {n : ℕ} : Fin n → Fin n → Set where
  less    : ∀ greatest (least : Fin′ greatest) →
            ordering (inject least) greatest
  equal   : ∀ i → ordering i i
  greater : ∀ greatest (least : Fin′ greatest) →
            ordering greatest (inject least)

Compare : ∀ {n} (i j : Fin n) → ordering i j
Compare zero    zero    = equal   zero
Compare zero    (suc j) = less    (suc j) zero
Compare (suc i) zero    = greater (suc i) zero
Compare (suc i) (suc j) with Compare i j
... | less    greatest least = less    (suc greatest) (suc least)
... | greater greatest least = greater (suc greatest) (suc least)
... | equal   i              = equal   (suc i)

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

-- Each node will hold a value & a pointer to
-- another node. Maybe type so that it can potentially
-- point to none
record Node (A : Set) (n : ℕ) : Set where 
    constructor
        node
    field
        val : A
        next : Maybe (Fin n)

-- given a set & a natural number to find,
-- creates a length list of length N
LinkedList : Set → ℕ → Set
LinkedList A n = Vec (Node A n) n



-- finds a specific node in the LinkedList given Fin at 0
data Lookup {A : Set} : ∀ {n} → Vec A n → Fin n → A → Set where
    zero : ∀ {n x xs} → Lookup {n = suc n} (x ∷ xs) zero x
    suc : ∀ {n x xs k y} → Lookup {n = n} xs k y → Lookup (x ∷ xs) (suc k) y
-- 



data Path {A n} (l : LinkedList A n) (i : Fin n) : Fin n → Set where
    one : ∀ {x j} → Lookup l i (node x (just j)) → Path l i j
    suc : ∀ {x j k} → Lookup l j (node x (just k)) → Path l i j → Path l i k

data Circular {A n} : LinkedList A n → Set where
  circle : ∀ {l i} → Path l i i → Circular l
    -- circle : ∀ {l i} → Path l 0 i → Path l i i → Circular l

-- data Length : Path l i j → Nat → Set

-- record LongPath : LinkedList A n → Set

-- circular-path : Circular l → LongPath l

-- nothing-circular : Path l zero i → Lookup l i (node x nothing) → Circular l → ⊥
-- nothing-circular = ?



stepNextHelp : ∀ {A n} → Node A n → Maybe (Fin n)
stepNextHelp (node v n)= n

-- Helper to step forward from one node to the next
stepNext : ∀ {A n} → LinkedList A n → Fin n → Maybe (Fin n) 
stepNext l F = stepNextHelp (lookup l F)

-- A toNat function that accounts for the potential "nothing" in 
--toNat : ∀ (Maybe (Fin n)) → ℕ
--toNat nothing = λ ()
--toNat zero = zero
--toNat suc(zero) = (suc zero)

FloydNext : ∀ {A n} (l : LinkedList A n) → Maybe (Fin n) → Maybe (Fin n) → Dec (Circular l)
FloydNext l _ nothing = no {! (λ {(circle ())}) !} -- ((λ {circle ()}))
FloydNext xs i (just j) = {!  floydHelper !}

FloydEq : ∀ {A n} (l : LinkedList A n) → (i : Fin n) → (j : Fin n) → ordering i j → Dec (Circular l)
FloydEq xs i _ (equal _) = yes (circle (one {!   !}))
FloydEq xs i j _ = FloydNext xs (stepNext xs i) (stepNext xs j)

-- FloydEq : ∀ {A n} (l : LinkedList A n) → Maybe (Fin n) → ℕ → Maybe (Fin n) → ℕ → Dec (Circular l)
-- FloydEq l nothing _ _ _= ?
-- FloydEq l _ _ _ nothing = ?
-- FloydEq l 

floydHelper' : ∀ {A n} → (l : LinkedList A (suc n)) → (i j : Fin (suc n)) → Path l zero i → Path l i j → Dec (Circular l)
floydHelper' x y z = {!   !}

-- Helper function using fin to represent the nodes of LinkedList
-- slow moves 1 step at a time & fast moves 2 steps each time
-- Base cases: 1. Slow == fast & they're not at the beginning, loop detected.
-- 2. Slow or fast hits nothing, no loop
-- 3. Move slow 1 & fast 2 steps.
floydHelper : ∀ {A n} (l : LinkedList A n) → Maybe (Fin n) → Maybe (Fin n) → Dec (Circular l)
-- floydHelper l s f = {!   !}
floydHelper xs nothing _ = no {! λ () !}
floydHelper xs _ nothing = no {!   !}
floydHelper xs (just O) (just T) = FloydEq xs O T (Compare O T)

-- Floyd's cycle: more efficient way for proving a loop in a 
-- linked list. 
-- 2 nodes: 1 moves 2 nodes each iteration & another moves 
-- 1 node each iteration.
-- If there's a cycle, the nodes will eventually equal each other
-- again. If not, the faster node will be Maybe nothing
floyd : ∀ {A n} → (l : LinkedList A n) → Dec (Circular l)
-- floyd [] = no (λ {(circle ())})
floyd [] = no (λ {(circle {_} {()} _)})
floyd ys@(node v n ∷ xs) = floydHelper ys (just zero) n 

-- updateNext : {A : Set} → {n : ℕ} → Fin n → Vec (Node A n) n → Vec (Node A n) n
-- updateNext _ [] = []
-- updateNext _ ((node a _) ∷ []) = {!   !} -- (node a (just zero)) ∷ []
-- updateNext n ((node a m) ∷ xs) = {! (node a (suc n)) ∷ (updateNext (suc n) xs)  !}

-- append : {A : Set} → {n : ℕ} → A → Vec (Node A n) n → Vec (Node A n) (suc n)
-- append a [] = {! (Node a zero) ∷ [] !}
-- append a (x ∷ []) = {!   !}
-- append a (x ∷ xs) = {!   !}
  