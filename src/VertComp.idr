||| Vertical composition of morphisms
module VertComp

import Data.Vect
import VectHelp
import ProcessLib
import Util
import Proto

%default total

-- TODO: we aren't handling any errors here
||| Connect two process
makeConnection: (w: DTy) ->
                (loc: Elem w cut_b) ->
                ProcPID (MkNiche cut_a cut_b) ->
                ProcPID (MkNiche cut_b cut_c) ->
                Process (ProcIF (MkNiche cut_a cut_c)) () Ready Ready
makeConnection (Down a) loc pid_f pid_g = do r <- Request pid_f (Conn (BotOutWire loc) pid_g (TopInWire loc))
                                             Action $ putStrLn $ "CONN: Down: " ++ show r
makeConnection (Up a)   loc pid_f pid_g = do r <- Request pid_g (Conn (TopOutWire loc) pid_f (BotInWire loc))
                                             Action $ putStrLn $ "CONN: Up  : " ++ show r

||| Connect two process that have a common cut
makeConnections: (cut_b: Cut m1) ->
                 ProcPID (MkNiche cut_a cut_b) ->
                 ProcPID (MkNiche cut_b cut_c) ->
                 Process (ProcIF (MkNiche cut_a cut_c)) () Ready Ready
makeConnections cut_b pid_f pid_g = let locs = allElems cut_b
  in sequence (map (\(dt ** loc) => makeConnection dt loc pid_f pid_g) locs)

||| Handle incoming requests
||| Just reroutes the requests to the appropriate morphism
resp: ProcPID (MkNiche cut_a cut_b) ->
      ProcPID (MkNiche cut_b cut_c) ->
      (msg : Req (MkNiche cut_a cut_c)) ->
      Process (ProcIF (MkNiche cut_a cut_c))
              (ProcIF (MkNiche cut_a cut_c) msg)
              Ready
              Ready
resp pid_f pid_g con@(Conn (TopOutWire _) _ _) = Request pid_f con
resp pid_f pid_g con@(Conn (BotOutWire _) _ _) = Request pid_g con
resp pid_f pid_g val@(Val (TopInWire _) _)     = do r <- Request pid_f val
                                                    --Action $ putStrLn $ "vert: reroute top val: " ++ show r
                                                    Pure r
resp pid_f pid_g val@(Val (BotInWire _) _)     = do r <- Request pid_g val
                                                    --Action $ putStrLn $ "vert: reroute bot val: " ++ show r
                                                    Pure r

infixl 3 -*-

||| Vertical composition of morphisms in the category of processes
public export partial
(-*-): {l,m,n: Nat} -> {cut_a: Cut l} -> {cut_b: Cut m} -> {cut_c: Cut n} ->
       Hom cut_a cut_b -> Hom cut_b cut_c -> Hom cut_a cut_c
(-*-) {cut_b} f g = do Just pid_f <- Spawn f | _ => do Action $ putStrLn "ERROR: (-*-): failed spawn 1"
                                                       f -*- g
                       Just pid_g <- Spawn g | _ => do Action $ putStrLn "ERROR: (-*-): failed spawn 2"
                                                       f -*- g
                       makeConnections cut_b pid_f pid_g
                       looper pid_f pid_g
  where
    looper : ProcPID (MkNiche cut_a cut_b) ->
             ProcPID (MkNiche cut_b cut_c) ->
             Process (ProcIF (MkNiche cut_a cut_c)) () Ready Looping
    looper pid_f pid_g = do --Action $ putStrLn $ "(-*-): normal loop"
                            Respond (resp pid_f pid_g)
                            Loop (looper pid_f pid_g)
