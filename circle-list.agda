open import Data.Fin.Base

data CircleList (A : Set) : Set where 
    head : A → CircleList A → CircleList A
    node : A → CircleList A → CircleList A
    tail : A → head
