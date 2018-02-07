module Util

import Data.Vect
import ProcessLib
import System

%default total

export
(>>): Process iface a s0 s1 -> Process iface b s1 s2 -> Process iface b s0 s2
(>>) x y = do { x ; y }

export
sequence: Vect n (Process iface () s s) -> Process iface () s s
sequence xs = foldr (>>) (Pure ()) xs

export
sleeper: Nat -> Process iface () s s
sleeper Z     = Pure ()
sleeper (S k) = sleeper k >> (Action $ usleep 1000000)

export
dot_sleeper: Nat -> Process iface () s s
dot_sleeper Z = Pure ()
dot_sleeper (S k) = dot_sleeper k >> (do {Action (usleep 1000000); Action (putStrLn ".")})
