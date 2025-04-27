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
    zero : ∀ {x xs} → Lookup (x ∷ xs) zero x
    suc : ∀ {x xs k y} → Lookup xs k y → Lookup (x ∷ xs) (suc k) y
-- 
data Path {A n} (l : LinkedList A n) (i : Fin n) : Fin n → Set where
    one : ∀ {x j} → Lookup l i (node x (just j)) → Path l i j
    suc : ∀ {x j k} → Lookup l j (node x (just k)) → Path l i j → Path l i k

data Circular {A n} : LinkedList A n → Set where
    circle : ∀ {l i} → Path l i i → Circular l

-- Helper to step forward from one node to the next
stepNext : ∀ {A n} → LinkedList A n → Fin n → Maybe (Fin n)
stepNext n _  = {!   !}

-- Helper function using fin to represent the nodes of LinkedList
-- slow moves 1 step at a time & fast moves 2 steps each time
-- Base cases: 1. Slow == fast & they're not at the beginning, loop detected.
-- 2. Slow or fast hits nothing, no loop
-- 3. Move slow 1 & fast 2 steps.
floydHelper : ∀ {A n} (l : LinkedList A n) → (slow fast : Fin n) → Dec (Circular l)
floydHelper l s f = {!   !}

-- Floyd's cycle: more efficient way for proving a loop in a 
-- linked list. 
-- 2 nodes: 1 moves 2 nodes each iteration & another moves 
-- 1 node each iteration.
-- If there's a cycle, the nodes will eventually equal each other
-- again. If not, the faster node will be Maybe nothing
floyd : ∀ {A n} → (l : LinkedList A n) → Dec (Circular l)
floyd l = {!   !} -- floyd l = {! floydHelper l zero zero !}



-- updateNext : {A : Set} → {n : ℕ} → Fin n → Vec (Node A n) n → Vec (Node A n) n
-- updateNext _ [] = []
-- updateNext _ ((node a _) ∷ []) = {!   !} -- (node a (just zero)) ∷ []
-- updateNext n ((node a m) ∷ xs) = {! (node a (suc n)) ∷ (updateNext (suc n) xs)  !}

-- append : {A : Set} → {n : ℕ} → A → Vec (Node A n) n → Vec (Node A n) (suc n)
-- append a [] = {! (Node a zero) ∷ [] !}
-- append a (x ∷ []) = {!   !}
-- append a (x ∷ xs) = {!   !}

 