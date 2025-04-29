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

-- l: linked list to traverse
-- i : next val to a node of linked list
data Path {A n} (l : LinkedList A n) (i : Fin n) : Fin n → Set where
    one : ∀ {x j} → Lookup l i (node x (just j)) → Path l i j
    suc : ∀ {x j k} → Lookup l j (node x (just k)) → Path l i j → Path l i k

data Circular {A n} : LinkedList A (suc n) → Set where
  circle : ∀ {l i} → Path l zero i → Path l i i → Circular l
  -- circle : ∀ {l i} → Path l


-- The next 3 functions were to help use so the problem of absurdPaths.
-- Essentially, if the dec was no, we can determine that it is absurd either
-- due to the fast or slow node's next pointing to nothing.
-- We had issues with defining the empty case without zero (suc n does not allow for zero,
-- but it kept asking for it as one of the goals)


-- contraDerive: if we can prove something is not true, it means
-- that something else is true
-- We used this somewhere in the last proofs project
--contraDerive : ∀ {A : Set} → ⊥ → A
--contraDerive ()

-- getNodeByLookup : ∀ {A n} {l : LinkedList A n} {i : Fin n} {x : Node A n} → Lookup l i x → Node A n
-- getNodeByLookup (zero {x = x} ) = x
-- getNodeByLookup (suc {xs = xs} lookup) = ? -- getNodeByLookup lookup

-- Try to define a path that is not possible so that we can fill in the no cases
absurdPath : ∀ {A n} {l : LinkedList A (suc n)} {i : Fin (suc n)} → Path l zero i → ⊥

--absurdPath (one lookup) with getNodeByLookup lookup
--... | node v nothing = contraDerive -- 
-- ... | just j = {!!} -- should not happen in this branch
--absurdPath (suc lookup p) = absurdPath p
absurdPath = {!   !}

-- These are ideas for potentially determining circularity
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

-- FloydNext : ∀ {A n} (l : LinkedList A n) → Maybe (Fin n) → Maybe (Fin n) → Dec (Circular l)
-- FloydNext l _ nothing = no {! (λ {(circle ())}) !} -- ((λ {circle ()}))
-- FloydNext xs i (just j) = {!  floydHelper !}

-- FloydEq : ∀ {A n} (l : LinkedList A n) → (i : Fin n) → (j : Fin n) → ordering i j → Dec (Circular l)
-- FloydEq xs i _ (equal _) = yes (circle (one {!   !}))
-- FloydEq xs i j _ = FloydNext xs (stepNext xs i) (stepNext xs j)

-- FloydEq : ∀ {A n} (l : LinkedList A n) → Maybe (Fin n) → ℕ → Maybe (Fin n) → ℕ → Dec (Circular l)
-- FloydEq l nothing _ _ _= ?
-- FloydEq l _ _ _ nothing = ?
-- FloydEq l 


-- Helper function using fin to represent the nodes of LinkedList
-- slow moves 1 step at a time & fast moves 2 steps each time
-- Base cases: 1. Slow == fast & they're not at the beginning, loop detected.
-- 2. Slow or fast hits nothing, no loop
-- 3. Move slow 1 & fast 2 steps.
-- floydHelper : ∀ {A n} (l : LinkedList A n) → Maybe (Fin n) → Maybe (Fin n) → Dec (Circular l)
-- floydHelper l s f = {!   !}
-- floydHelper xs nothing _ = no {! λ () !}
-- floydHelper xs _ nothing = no {!   !}
-- floydHelper xs (just O) (just T) = FloydEq xs O T (Compare O T)

{-# TERMINATING #-}
floydHelper' : ∀ {A n} → (l : LinkedList A (suc n)) → (i j : Fin (suc n)) → Path l zero i → Path l i j → Dec (Circular l)
floydHelper' xs s f p0 pn = {! FloydEq xs s f (Compare s f) !}


-- Floyd's cycle: more efficient way for proving a loop in a 
-- linked list. 
-- Assumes the list is not empty as we have to pass a successor to pattern match,
-- else the two Paths in circular will throw an error "suc n != n"
-- 2 nodes: 1 moves 2 nodes each iteration & another moves 
-- 1 node each iteration.
-- If there's a cycle, the nodes will eventually equal each other
-- again. If not, the faster node will be Maybe nothing
floyd : ∀ {A n} → (l : LinkedList A (suc n)) → Dec (Circular l)
-- floyd [] = no (λ {(circle {_} {()} _)}) -- unnecessary case since it can not be null due to suc n setup
floyd ys@(node v (just n) ∷ xs) = floydHelper' ys zero n (one {!   !}) (suc {!   !} {!   !}) -- floydHelper' ys (just zero) n
floyd ys@(node v (nothing) ∷ xs) = no ( λ { (circle p0 pn) → absurdPath p0}) -- (λ { (circle (one (zero ())) _) })

-- updateNext : {A : Set} → {n : ℕ} → Fin n → Vec (Node A n) n → Vec (Node A n) n
-- updateNext _ [] = []
-- updateNext _ ((node a _) ∷ []) = {!   !} -- (node a (just zero)) ∷ []
-- updateNext n ((node a m) ∷ xs) = {! (node a (suc n)) ∷ (updateNext (suc n) xs)  !}

-- append : {A : Set} → {n : ℕ} → A → Vec (Node A n) n → Vec (Node A n) (suc n)
-- append a [] = {! (Node a zero) ∷ [] !}
-- append a (x ∷ []) = {!   !}
-- append a (x ∷ xs) = {!   !}
