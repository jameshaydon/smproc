module Main

import IdrisScript

import Data.Vect

%default total

infixl 9 ~~>
infixl 9 ~>~

main: JS_IO ()
main = putStrLn' "hello"

namespace SigTy
  data SigTy: Type where
    Pos: Type -> SigTy
    Neg: Type -> SigTy
    (*): SigTy -> SigTy -> SigTy

  dual: SigTy -> SigTy
  dual (Pos x) = Neg x
  dual (Neg x) = Pos x
  dual (x * y) = dual x * dual y

data (~~>): SigTy -> SigTy -> Type where
  Pure: (a -> b) -> Pos a ~~> Pos b
  (~>~): (x ~~> y) -> (y ~~> z) -> (x ~~> z)

-- (~~): SigTy -> SigTy -> Type
-- (~~) a b = Bord a b

-- data CoBord: SigTy -> SigTy -> Type where
--   Pure: (a -> b) -> CoBord (Pos a) (Pos b)
--   (*): CoBord a b -> CoBord c d -> CoBord (a * c) (b * d)
--   (~~): CoBord a b -> CoBord b c -> CoBord a c
--   Dual: CoBord a b -> CoBord (dual a) (dual b)
--   Unit:   (a: SigTy) -> CoBord (Pos ()) (dual a * a)
--   CoUnit: (a: SigTy) -> CoBord (a * dual a) (Pos ())
--
-- f : CoBord (Pos Int) (Pos Int)
-- f = Pure id
--
-- alpha : CoBord (Pos Int * Pos String) (Pos Int * Pos String)
-- alpha = Pure id * Pure id
--
-- beta : CoBord (Neg String) (Neg String)
-- beta = Dual (Pure id)
--
-- alphabeta : CoBord (Pos Int * Pos String * Neg String) (Pos Int * Pos String * Neg String)
-- alphabeta = alpha * beta
--
-- left: CoBord (Pos Int * Pos ()) (Pos Int * (Neg String * Pos String))
-- left = Pure id * Unit (Pos String)
--
-- right: CoBord (Pos Int * (Pos String * Neg String)) (Pos Int * Pos ())
-- right = Pure id * CoUnit (Pos String)
