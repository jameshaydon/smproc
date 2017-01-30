||| Horizontal composition
module HoriComp

import Data.Vect
import VectHelp
import ProcessLib

import Proto

%default total
%access public export

resp: {m0,n0,m1,n1: Nat} ->
      {top0: Cut m0} -> {top1: Cut m1} -> {bot0: Cut n0} -> {bot1: Cut n1} ->
      ProcPID (MkNiche top0 bot0) ->
      ProcPID (MkNiche top1 bot1) ->
      (msg : Req (MkNiche (top0 ++ top1) (bot0 ++ bot1))) ->
      Process (ProcIF (MkNiche (top0 ++ top1) (bot0 ++ bot1)))
              (ProcIF (MkNiche (top0 ++ top1) (bot0 ++ bot1)) msg)
              Ready
              Ready
resp {top0 = top0} {top1 = top1} {bot0 = bot0} {bot1 = bot1} pid_a pid_b (Conn (TopOutWire loc) pid' target) =
  case elemConcat top0 top1 loc of
    Left l  => Request pid_a (Conn (TopOutWire l) pid' target)
    Right r => Request pid_b (Conn (TopOutWire r) pid' target)
resp {top0 = top0} {top1 = top1} {bot0 = bot0} {bot1 = bot1} pid_a pid_b (Conn (BotOutWire loc) pid' target) =
  case elemConcat bot0 bot1 loc of
    Left l  => Request pid_a (Conn (BotOutWire l) pid' target)
    Right r => Request pid_b (Conn (BotOutWire r) pid' target)
resp {top0 = top0} {top1 = top1} {bot0 = bot0} {bot1 = bot1} pid_a pid_b (Val (TopInWire loc) x) =
  case elemConcat top0 top1 loc of
    Left l  => Request pid_a (Val (TopInWire l) x)
    Right r => Request pid_b (Val (TopInWire r) x)
resp {top0 = top0} {top1 = top1} {bot0 = bot0} {bot1 = bot1} pid_a pid_b (Val (BotInWire loc) x) =
  case elemConcat bot0 bot1 loc of
    Left l  => Request pid_a (Val (BotInWire l) x)
    Right r => Request pid_b (Val (BotInWire r) x)

||| Monoidal operation on morphisms in the symetric monoidal category of processes
partial
(+): {m0,n0,m1,n1: Nat} ->
     {top0: Cut m0} -> {top1: Cut m1} -> {bot0: Cut n0} -> {bot1: Cut n1} ->
     Hom top0 bot0 -> Hom top1 bot1 -> Hom (top0 ++ top1) (bot0 ++ bot1)
(+) alpha beta = do Just pid_a <- Spawn alpha
                    Just pid_b <- Spawn beta
                    looper pid_a pid_b
  where
    looper: ProcPID (MkNiche top0 bot0) ->
            ProcPID (MkNiche top1 bot1) ->
            Process (ProcIF (MkNiche (top0 ++ top1) (bot0 ++ bot1))) () Ready Looping
    looper pid_a pid_b = do Respond (resp pid_a pid_b)
                            Loop (looper pid_a pid_b)
