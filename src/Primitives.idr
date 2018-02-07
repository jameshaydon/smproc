module Primitives

import Data.Vect
import ProcessLib
import Proto

%default total

||| Takes a pure function and returns a process that depends on a slot
||| This process will wait for another process to register to its output
||| Then it will tranform messages according to the pure function.
mkPure': (Show a, Show b) => (name: String) -> (f: a -> b) -> Slot b -> Hom [Down a] [Down b]
mkPure' name f EmptySlot = do Just msg <- Respond (\msg => Pure (fst (handleInitMsg msg))) | _ => Loop (mkPure' name f EmptySlot)
                              Loop $ mkPure' name f (snd (handleInitMsg msg))
  where
    handleInitMsg: (msg : Req (MkNiche [Down a] [Down b])) ->
                   ( ProcIF (MkNiche [Down a] [Down b]) msg
                   , Slot b )
    handleInitMsg (Conn (BotOutWire Here) pid targetInWire) = ( ConnAccepted, FullSlot pid targetInWire )
    handleInitMsg (Val _ _)                                 = ( Error       , EmptySlot                 )
    handleInitMsg (Conn (BotOutWire (There _)) _ _)         impossible
    handleInitMsg (Conn (TopOutWire (There _)) _ _)         impossible
mkPure' name f {a} {b} fs@(FullSlot pid tar) = do --Action $ putStrLn $ name ++ "normal loop"
                                                  Just msg <- Respond (\msg => Pure (normal msg)) | _ => Loop (mkPure' name f fs)
                                                  forward msg
                                                  Loop (mkPure' name f fs)
  where
    forward: Req (MkNiche [Down a] [Down b]) -> Process (ProcIF (MkNiche [Down a] [Down b])) () Sent Sent
    forward (Conn _ _ _) = Pure ()
    forward (Val (TopInWire Here) x) = do Request pid (Val tar (f x))
                                          Action $ putStrLn $ name ++ show x ++ " -->-- " ++ show (f x)
    forward (Val (TopInWire (There l)) _) = absurd l
    forward (Val (BotInWire (There l)) _) = absurd l

    normal: (msg : Req (MkNiche [Down a] [Down b])) -> ProcIF (MkNiche [Down a] [Down b]) msg
    normal (Conn _ _ _)                  = Taken
    normal (Val (TopInWire Here) _)      = Accepted
    normal (Val (TopInWire (There l)) _) = absurd l
    normal (Val (BotInWire (There l)) _) = absurd l

export mkPure: (Show a, Show b) => (name: String) -> (f: a -> b) -> Hom [Down a] [Down b]
mkPure name f = mkPure' name f EmptySlot

||| A service wich prints integers to the console
export downPrinter: Hom [Down Int] []
downPrinter = do Respond resp
                 Loop downPrinter
  where resp: (msg : Req (MkNiche [Down Int] [])) -> Process (ProcIF (MkNiche [Down Int] [])) (ProcIF (MkNiche [Down Int] []) msg) Ready Ready
        resp (Conn _ _ _) = do Action $ putStrLn "ERROR: printer got connection request"
                               Pure Taken
        resp (Val (TopInWire Here) i) = do Action $ putStrLn $ "Hello this is IntPrinter, here is your Int: " ++ show i
                                           Pure Accepted
        resp (Val (TopInWire (There _)) _) impossible
        resp (Val (BotInWire Here) _)      impossible
        resp (Val (BotInWire (There _)) _) impossible

export upPrinter: Hom [] [Up Int]
upPrinter = do Respond resp
               Loop upPrinter
  where
    resp: (msg : Req (MkNiche [] [Up Int])) -> SubProc (MkNiche [] [Up Int]) (ProcIF (MkNiche [] [Up Int]) msg)
    resp (Conn _ _ _) = do Action $ putStrLn "ERROR: printer got conn req"
                           Pure Taken
    resp (Val (BotInWire Here) i) = do Action $ putStrLn $ "upPrinter: " ++ show i
                                       Pure Accepted
    resp (Val (BotInWire (There later)) x) impossible
    resp (Val (TopInWire Here) _) impossible
    resp (Val (TopInWire (There _)) _) impossible

-- downTick': Slot () -> Hom [] [Down ()]
-- downTick' EmptySlot = ?oo_1
-- downTick' s@(FullSlot pid tar) = do Respond (\msg => Pure Error)
--                                     Loop (downTick' s)
