module Dualise

import Data.Vect
import ProcessLib
import Proto

%default total
%access public export

--TODO: think about if we need to make dualise not send on requests

resp: (pid: ProcPID (MkNiche cut_a cut_b)) ->
      (msg : Req (MkNiche (dual cut_b) (dual cut_a))) ->
      SubProc (MkNiche (dual cut_b) (dual cut_a))
              (ProcIF (MkNiche (dual cut_b) (dual cut_a)) msg)
resp pid (Conn (TopOutWire loc) pid' outw) = Request pid (Conn (BotOutWire (dualAddrUp   loc)) pid' outw)
resp pid (Conn (BotOutWire loc) pid' outw) = Request pid (Conn (TopOutWire (dualAddrDown loc)) pid' outw)
resp pid (Val  (TopInWire  loc) x)         = do --Action $ putStrLn "dual: got top, sending to bot"
                                                Request pid (Val  (BotInWire  (dualAddrDown loc)) x)
resp pid (Val  (BotInWire  loc) x)         = do --Action $ putStrLn "dual: got bot, sending to top"
                                                Request pid (Val  (TopInWire  (dualAddrUp   loc)) x)

loop: ProcPID (MkNiche cut_a cut_b) ->
      Process (ProcIF (MkNiche (dual cut_b) (dual cut_a))) () Ready Looping
loop pid = do --Action $ putStrLn "dual: starting normal loop"
              Just msg <- Respond $ resp pid | _ => do --Action $ putStrLn "dual: got nothing"
                                                       Loop (loop pid)
              Loop    $ loop pid

partial
dualise: Hom cut_a cut_b -> Hom (dual cut_b) (dual cut_a)
dualise proc = do Just pid <- Spawn proc
                  loop pid
