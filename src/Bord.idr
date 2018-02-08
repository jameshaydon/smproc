module Bord

import System.Concurrency.Channels

import Data.Vect

%default total

infixl 9 -.-
infixl 3 ~>~

main: JS_IO ()
main = putStrLn' "hello"

namespace SigTy
  data SigTy: Type where
    Pos: Type -> SigTy
    Neg: Type -> SigTy
    (+): SigTy -> SigTy -> SigTy

  dual: SigTy -> SigTy
  dual (Pos x) = Neg x
  dual (Neg x) = Pos x
  dual (x + y) = dual x + dual y

data (~>~): SigTy -> SigTy -> Type where
  Pure:   (a -> b) -> Pos a ~>~ Pos b
  Io:     (a -> IO b) -> Pos a ~>~ Pos b
  (-.-):  (x ~>~ y) -> (y ~>~ z) -> (x ~>~ z)
  (+):    (w ~>~ x) -> (y ~>~ z) -> (w + y ~>~ x + z)
  Dual:   (x ~>~ y) -> (dual y ~>~ dual x)
  Unit:   (x: SigTy) -> (Pos Void ~>~ (dual x + x))
  CoUnit: (x: SigTy) -> (x + dual x ~>~ Pos Void)
  Join:   Pos a + Pos b    ~>~ Pos (Either a b)
  Split:  Pos (Either a b) ~>~ Pos a + Pos b
  Assoc:  (x,y,z: SigTy) -> x + (y + z) ~>~ (x + y) + z

plusEq: {x,x',y,y': SigTy} -> x = x' -> y = y' -> x + y = x' + y'
plusEq Refl Refl = Refl

dualIdem: (x: SigTy) -> dual (dual x) = x
dualIdem (Pos x) = Refl
dualIdem (Neg x) = Refl
dualIdem (x + y) = plusEq (dualIdem x) (dualIdem y)

lemma1: (x,y,z: SigTy) -> dual (dual x + dual y + dual z) = x + y + z
lemma1 x y z = plusEq (plusEq (dualIdem x) (dualIdem y)) (dualIdem z)

lemma2: (x,y,z: SigTy) -> dual (dual x + (dual y + dual z)) = x + (y + z)
lemma2 x y z = plusEq (dualIdem x) (plusEq (dualIdem y) (dualIdem z))

revAssoc: (x,y,z: SigTy) -> (x + y) + z ~>~ x + (y + z)
revAssoc x y z =    rewrite sym (lemma1 x y z)
                 in rewrite sym (lemma2 x y z)
                 in Dual (Assoc (dual x) (dual y) (dual z))

alpha: Pos Int ~>~ Pos Int
alpha = Pure id

beta: Pos String ~>~ Pos String
beta = Pure id

gamma: Neg String ~>~ Neg String
gamma = Dual (Pure id)

alphabeta: Pos Int + Pos String ~>~ Pos Int + Pos String
alphabeta = alpha + beta

middle: Pos Int + Pos String + Neg String ~>~ Pos Int + Pos String + Neg String
middle = alphabeta + gamma

right: Pos Int + Pos String + Neg String ~>~ Pos Int + Pos Void
right = revAssoc (Pos Int) (Pos String) (Neg String) -.- (Pure id + CoUnit (Pos String))

left: Pos Int + Pos Void ~>~ Pos Int + Pos String + Neg String
left = (Pure id + Unit (Neg String)) -.- Assoc (Pos Int) (Pos String) (Neg String)

big: Pos Int + Pos Void ~>~ Pos Int + Pos Void
big = left -.- middle -.- right

-- make processes

partial
inPortLoop: (a: Type) -> (f: a -> b) -> Channel -> Channel -> IO ()
inPortLoop a f sender_chan worker_chan = do
  Just i <- unsafeRecv a sender_chan
  ok <- unsafeSend worker_chan i
  inPortLoop a f sender_chan worker_chan

partial
inPort: (a: Type) -> (f: a -> b) -> IO ()
inPort a f = do
  Just sender_chan <- listen 1 
  Just worker_chan <- listen 1
  inPortLoop a f sender_chan worker_chan

outPort: (b: Type) -> IO ()
outPort b = ?outPort_rhs

-- mkPure: (a -> b) -> IO (Maybe (Channel, Channel))
-- mkPure f = do
--   Just pure_id <- spawn pureProc
--     | Nothing => putStrLn "Error"
