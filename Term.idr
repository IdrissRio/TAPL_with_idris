-- Author: Idriss Riouak
-- Since: 11/04/2020
module Main

import Data.List

data Term = STrue |
            SFalse |
            SZero |
            SUCC Term|
            PRED Term |
            ISZERO Term|
            IFTHENELSE Term Term Term

data Natural =
  Z |
  S Natural

nat_to_int : Natural -> Integer
nat_to_int Z = 0
nat_to_int (S k) = 1 + (nat_to_int k)


Eq Term where
    (==) STrue STrue = True
    (==) SFalse SFalse = True
    (==) SZero SZero = True
    (==) (SUCC e1) (SUCC e2) = e1 == e2
    (==) (PRED e1) (PRED e2) = e1 == e2
    (==) (ISZERO e1) (ISZERO e2) = e1 == e2
    (==) (IFTHENELSE e11 e12 e13) (IFTHENELSE e21 e22 e23) = e11 == e21
                                                            && e12 == e22
                                                            && e13 == e23
    (==) _ _ = False

Show Term where
  show STrue = "True"
  show SFalse = "False"
  show SZero = "Zero"
  show (SUCC e1) = "Succ "++ show e1
  show (PRED e1) = "Pred "++ show e1
  show (ISZERO e1) = "IsZero "++ show e1
  show (IFTHENELSE e1 e2 e3) = "If "++ (show e1) ++
                              " then " ++ (show e2) ++
                              " else "++ (show e3)

Show Natural where
  show x = show (nat_to_int x)




add : Natural -> Natural -> Natural
add x Z = x
add x (S y) = S (add x y)

add_commutes_Z : n = add Z n
add_commutes_Z {n = Z} = Refl
add_commutes_Z {n = (S x)} = let rec = add_commutes_Z {n=x} in
                             rewrite rec in Refl

add_commutes_S: (n:Natural) -> (x:Natural) -> S(add x n) = add (S x) n
add_commutes_S Z x = Refl
add_commutes_S (S y) x = rewrite add_commutes_S y x in Refl

total
add_commutes: (n: Natural) -> (m: Natural) -> n `add` m = m `add` n
add_commutes n Z = add_commutes_Z
add_commutes n (S x) = rewrite add_commutes n x in add_commutes_S n x

total
is_zero: Natural -> Bool
is_zero Z = True
is_zero (S n) = False

--Compute the set S_k
total
s : Natural -> List Term
s Z = []
s (S k) = let sk = s k
              def_set = [STrue, SFalse, SZero]
              succ_set = [SUCC x| x <-sk]
              pres_set = [PRED x| x <- sk]
              iszero_set = [ISZERO x| x <- sk]
              ifthenelse_set = [IFTHENELSE x y z | x <- sk, y <- sk, z <- sk ]
          in
          foldl (++) [] [def_set, succ_set, pres_set, iszero_set, ifthenelse_set]



-- Compute the lenght of a list in linear time
len : List a-> Integer
len [] = 0;
len (x::xs) = 1 + (len xs)

uniq :(Eq a) => List a -> List a -> List a
uniq x [] = x
uniq [] (a::xs) = uniq [a] xs
uniq x (a::xs) = if elem a x then  uniq x xs else uniq (a::x) xs


-- Const function
Sconst:Term -> List Term
Sconst SZero = [SZero]
Sconst STrue = [STrue]
Sconst SFalse = [SFalse]
Sconst (SUCC x) = Sconst x
Sconst (PRED x) = Sconst x
Sconst (ISZERO x) = Sconst x
Sconst (IFTHENELSE x y z) = uniq [] ((Sconst x)++(Sconst y)++(Sconst z))


--elem :(Eq a) => a -> List a -> Bool
--elem x [] = False
--elem x (y :: xs) = case x==y of
--                   True => True
--                   False => elem x xs






main : IO ()
main = do putStr "************************************"
          putStr "The cardinality of S is"
          print (s i)
          putStr "************************************"
        where i = (S Z)




