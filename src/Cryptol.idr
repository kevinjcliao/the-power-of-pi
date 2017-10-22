module Data.Cryptol

import Data.Vect

public export
data Bit : Type where
    O : Bit
    I : Bit

public export
data Word : Type where
    Word : Nat -> Type
    Word n = Vect n Bit

-- Split takes a vector of size (m*n) and splits it into m vectors of
-- size n. See Power of Pi page 42. 
export
split : (n : Nat) -> (m : Nat) -> Vect (m * n) a -> Vect m (Vect n a)
split n  Z    [] = []
split n (S k) xs = take n xs :: split n k (drop n xs)