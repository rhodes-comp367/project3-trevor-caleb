open import Data.Fin.Base
open import Data.Nat.Base
open import Data.Vec.Base

record Node (A : Set) (n : ℕ) : Set where 
    constructor
        node
    field
        val : A
        next : Fin n

updateVal : {A : Set} → {n : ℕ} → Fin n → Vec (Node A n) n → Vec (Node A n) n
updateVal _ [] = []
updateVal zero ((node a _) ∷ []) = (node a zero) ∷ []
updateVal zero ((node a m) ∷ xs) = {! (node a (suc zero)) ∷ (updateVal (suc zero) xs)  !}
updateVal n ((node a m) ∷ xs) = {! (node a (suc n)) ∷ (updateVal (suc n) xs)  !}

