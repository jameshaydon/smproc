module CupCap

import Data.Vect
import VectHelp
import ProcessLib
import Proto
import Primitives

%default total

capT': Slot a -> Hom [] [Up a, Down a]
capT' {a} EmptySlot = do Just blam <- Respond initResp | _ => Loop (capT' EmptySlot)
                         Loop (capT' (fillSlot blam))
  where
    fillSlot: Req (MkNiche [] [Up a, Down a]) -> Slot a
    fillSlot (Conn (BotOutWire (There Here)) pid target) = FullSlot pid target
    fillSlot (Val _ _)                                   = EmptySlot
    fillSlot (Conn (BotOutWire (There (There _))) _ _)   impossible
    fillSlot (Conn (TopOutWire Here) _ _)                impossible
    fillSlot (Conn (TopOutWire (There _)) _ _)           impossible

    initResp: (msg: Req (MkNiche [] [Up a, Down a])) ->
              SubProc (MkNiche [] [Up a, Down a]) (ProcIF (MkNiche [] [Up a, Down a]) msg)
    initResp (Conn (BotOutWire (There Here)) _ _)      = do Action $ putStrLn "cap: accepted connection request"
                                                            Pure ConnAccepted
    initResp (Val _ _)                                 = do Action $ putStrLn "cap: got val before initialised"
                                                            Pure Error
    initResp (Conn (BotOutWire (There (There _))) _ _) impossible
    initResp (Conn (TopOutWire _) _ _)                 impossible

capT' {a} (FullSlot pid target) = do Action $ putStrLn "cap: starting loop"
                                     Respond (normal pid target)
                                     Loop (capT' (FullSlot pid target))
  where
    normal : MessagePID (ProcIF niche) ->
             InWire niche a ->
             (msg : Req (MkNiche [] [Up a, Down a])) ->
             SubProc (MkNiche [] [Up a, Down a]) (ProcIF (MkNiche [] [Up a, Down a]) msg)
    normal _ _ (Conn _ _ _) = do Action $ putStrLn "ERROR: cap got conn req when taken"
                                 Pure Taken
    normal _ _ (Val (BotInWire Here) x)              = do Action $ putStrLn $ "Passing through cap!"
                                                          r <- Request pid (Val target x)
                                                          Action $ putStrLn $ "cap got resp: " ++ show r
                                                          Pure r
    normal _ _ (Val (TopInWire _) _)                 impossible
    normal _ _ (Val (BotInWire (There (There _))) _) impossible

-- cap going the other way

cap': Slot a -> Hom [] [Down a, Up a]
cap' {a} EmptySlot = do Just blam <- Respond initResp | _ => Loop (cap' EmptySlot)
                        Loop (cap' (fillSlot blam))
  where
    -- TODO: the following two functions do the same deconstructing work
    fillSlot: Req (MkNiche [] [Down a, Up a]) -> Slot a
    fillSlot (Conn (BotOutWire Here) pid tar) = FullSlot pid tar
    fillSlot (Val _ _) = EmptySlot
    fillSlot (Conn (BotOutWire (There (There later))) pid tar) impossible
    fillSlot (Conn (TopOutWire Here) _ _) impossible
    fillSlot (Conn (TopOutWire (There _)) _ _) impossible

    initResp: (msg: Req (MkNiche [] [Down a, Up a])) ->
              SubProc (MkNiche [] [Down a, Up a]) (ProcIF (MkNiche [] [Down a, Up a]) msg)
    initResp (Conn (BotOutWire Here) pid tar) = Pure ConnAccepted
    initResp (Val _ _) = Pure Error
    initResp (Conn (BotOutWire (There (There later))) pid tar) impossible
    initResp (Conn (TopOutWire Here) _ _) impossible
    initResp (Conn (TopOutWire (There _)) _ _) impossible

-- do Action $ putStrLn $ "Passing through cap!"
--                                              r <- Request pid (Val target x)
--                                              Action $ putStrLn $ "capS got response: " ++ show r
--                                              Pure r

cap' {a} slot@(FullSlot pid target) = do Just msg <- Respond normal | _ => Loop (cap' slot)
                                         forward msg
                                         Loop (cap' slot)
  where
    forward : Req (MkNiche [] [Down a, Up a]) ->
              Process (ProcIF (MkNiche [] [Down a, Up a])) () Sent Sent
    forward (Conn _ _ _) = Pure ()
    forward (Val (BotInWire (There Here)) x) = do Request pid (Val target x)
                                                  Action $ putStrLn "passing through capS!"
    forward (Val (BotInWire (There (There l))) _) = absurd l
    forward (Val (TopInWire e) _) = absurd e

    normal : (msg : Req (MkNiche [] [Down a, Up a])) ->
             SubProc (MkNiche [] [Down a, Up a]) (ProcIF (MkNiche [] [Down a, Up a]) msg)
    normal (Val (BotInWire (There Here)) x) = Pure Accepted
    normal (Conn _ _ _) = do Action $ putStrLn "ERROR: cap got conn req when taken"
                             Pure Taken
    normal (Val (BotInWire (There (There l))) _) = absurd l
    normal (Val (TopInWire e) _) = absurd e

-- cup

cup': Slot a -> Hom [Down a, Up a] []
cup' {a} EmptySlot = do Just blam <- Respond initResp | _ => Loop (cup' EmptySlot)
                        Loop (cup' (fillSlot blam))
  where
    fillSlot: Req (MkNiche [Down a, Up a] []) -> Slot a
    fillSlot (Conn (TopOutWire (There Here)) pid tar) = FullSlot pid tar
    fillSlot (Val inWire y) = EmptySlot
    fillSlot (Conn (TopOutWire (There (There later))) pid tar) impossible
    fillSlot (Conn (BotOutWire Here) _ _) impossible
    fillSlot (Conn (BotOutWire (There _)) _ _) impossible

    initResp: (msg: Req (MkNiche [Down a, Up a] [])) ->
              SubProc (MkNiche [Down a, Up a] []) (ProcIF (MkNiche [Down a, Up a] []) msg)
    initResp (Conn (TopOutWire (There Here)) pid tar) = do --Action $ putStrLn $ "cup: accepted conn req"
                                                           Pure ConnAccepted
    initResp (Val inWire y) = do Action $ putStrLn "ERROR: cup: got val when not ready"
                                 Pure Error
    initResp (Conn (TopOutWire (There (There later))) pid tar) impossible
    initResp (Conn (BotOutWire Here) _ _) impossible
    initResp (Conn (BotOutWire (There _)) _ _) impossible

cup' {a} (FullSlot pid target) = do Just msg <- Respond normal | _ => Loop (cup' (FullSlot pid target))
                                    forward msg
                                    Loop (cup' (FullSlot pid target))
  where
    forward : Req (MkNiche [Down a, Up a] []) ->
              Process (ProcIF (MkNiche [Down a, Up a] [])) () Sent Sent
    forward (Conn _ _ _) = Pure ()
    forward (Val (BotInWire _) _) = Pure ()
    forward (Val (TopInWire Here) x) = do Action $ putStrLn "cup: about to forward"
                                          r <- Request pid (Val target x)
                                          Action $ putStrLn $ "cup: forward result: " ++ show r
    forward (Val (TopInWire (There (There _))) _) impossible

    normal : (msg : Req (MkNiche [Down a, Up a] [])) ->
             SubProc (MkNiche [Down a, Up a] []) (ProcIF (MkNiche [Down a, Up a] []) msg)
    normal (Conn _ _ _) = do Action $ putStrLn "ERROR: cup got conn req when taken"
                             Pure Taken
    normal (Val (TopInWire Here) x) = Pure Accepted
    normal (Val (TopInWire (There (There later))) x) impossible
    normal (Val (BotInWire Here) _) impossible
    normal (Val (BotInWire (There _)) _) impossible

-- public:

export capT: Hom [] [Up a, Down a]
capT = capT' EmptySlot

export cap: Hom [] [Down a, Up a]
cap = cap' EmptySlot

export cup: Hom [Down a, Up a] []
cup = cup' EmptySlot
