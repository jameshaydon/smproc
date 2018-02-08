module VectHelp

import Data.Vect

%default total

||| If an element is in a concat of two vectors, then it's in one or the other.
export
elemConcat: {x: a} -> (xs: Vect m a) -> (ys: Vect n a) -> Elem x (xs ++ ys) -> Either (Elem x xs) (Elem x ys)
elemConcat {x} []        (x :: xs) Here          = Right Here
elemConcat {x} []        (y :: xs) (There later) = Right (There later)
elemConcat {x} (x :: xs) ys        Here          = Left Here
elemConcat {x} (y :: xs) ys        (There later) = case elemConcat xs ys later of
  Left l  => Left $ There l
  Right r => Right r

shift : {x : a} -> {xs : Vect len a} ->
        (y : a ** Elem y xs) -> (y : a ** Elem y (x :: xs))
shift (x ** pf) = (x ** There pf)

||| Returns all the proofs that elements of a vector are in that vector.
export
allElems: (xs: Vect n a) -> Vect n (x: a ** Elem x xs)
allElems []        = []
allElems (x :: xs) =
    let es = allElems xs
    in (x ** Here) :: (map shift es)
