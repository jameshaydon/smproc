||| Relationship between sum-types and the monoidal operation on wires
module SumWire

import Data.Vect
import ProcessLib
import Proto
import Primitives
import VertComp

%default total

-- TODO: move these to a util
pi1: (a,b,c) -> a
pi1 (x,y,z) = x
pi2: (a,b,c) -> b
pi2 (x,y,z) = y
pi3: (a,b,c) -> c
pi3 (x,y,z) = z

--------------------------------
--  Split Eithers
--------------------------------

normal: (msg : Req (MkNiche [Down (Either a b)] [Down a, Down b])) ->
        SubProc (MkNiche [Down (Either a b)] [Down a, Down b]) (ProcIF (MkNiche [Down (Either a b)] [Down a, Down b]) msg)
normal (Val (TopInWire Here) x) = Pure Accepted
normal (Conn _ _ _) = Pure Taken
normal (Val (TopInWire (There _)) _) impossible
normal (Val (BotInWire (There (There _))) _) impossible

forward : MessagePID (ProcIF niche_a) ->
          InWire niche_a a ->
          MessagePID (ProcIF niche_b) ->
          InWire niche_b b ->
          Maybe (Req (MkNiche [Down (Either a b)] [Down a, Down b])) ->
          Process (ProcIF (MkNiche [Down (Either a b)] [Down a, Down b]))
                  ()
                  Sent
                  Sent
forward pid_a tar_a pid_b tar_b Nothing = Pure ()
forward pid_a tar_a pid_b tar_b (Just (Conn _ _ _)) = Pure ()
forward pid_a tar_a pid_b tar_b (Just (Val (TopInWire Here) x)) = case x of
  Left l  => do { Request pid_a (Val tar_a l); Pure () }
  Right r => do { Request pid_b (Val tar_b r); Pure () }
forward pid_a tar_a pid_b tar_b (Just (Val (TopInWire (There _)) _))         impossible
forward pid_a tar_a pid_b tar_b (Just (Val (BotInWire (There (There _))) _)) impossible

initResp : Slot a ->
           Slot b ->
           (msg : Req (MkNiche [Down (Either a b)] [Down a, Down b])) ->
           ( SubProc (MkNiche [Down (Either a b)] [Down a, Down b])
                     (ProcIF (MkNiche [Down (Either a b)] [Down a, Down b]) msg)
           , Slot a
           , Slot b )
initResp EmptySlot slot_b    (Conn (BotOutWire Here) pid tar)         = ( Pure ConnAccepted, FullSlot pid tar, slot_b           )
initResp slot_a    EmptySlot (Conn (BotOutWire (There Here)) pid tar) = ( Pure ConnAccepted, slot_a          , FullSlot pid tar )
initResp slot_a    slot_b    (Conn (BotOutWire _) _   _  )            = ( Pure Taken       , slot_a          , slot_b           )
initResp slot_a    slot_b    (Val _ _)                                = ( Pure Error       , slot_a          , slot_b           )
initResp _         _         (Conn (BotOutWire (There (There _))) _ _) impossible
initResp _         _         (Conn (TopOutWire (There _)) _ _)         impossible

splitEither': Slot a -> Slot b -> Hom [Down (Either a b)] [Down a, Down b]
splitEither' sl1@(FullSlot pid_a tar_a) sl2@(FullSlot pid_b tar_b) = do
  r <- Respond normal
  forward pid_a tar_a pid_b tar_b r
  Loop $ splitEither' sl1 sl2
splitEither' {a} {b} slot_a slot_b = do
  Just msg <- Respond $ (\msg => pi1 (initResp slot_a slot_b msg)) | _ => Loop (splitEither' slot_a slot_b)
  Loop $ splitEither' (pi2 $ initResp slot_a slot_b msg) (pi3 $ initResp slot_a slot_b msg)

export splitEither: Hom [Down (Either a b)] [Down a, Down b]
splitEither = splitEither' EmptySlot EmptySlot

------------------------------
--  Join Eithers
------------------------------

respJ : (msg : Req (MkNiche [Down a, Down b] [Down (Either a b)])) ->
        ( SubProc (MkNiche [Down a, Down b] [Down (Either a b)])
                  (ProcIF (MkNiche [Down a, Down b] [Down (Either a b)]) msg)
        , Slot (Either a b) )
respJ (Conn (BotOutWire Here) pid tar) = ( Pure ConnAccepted, FullSlot pid tar )
respJ (Val inWire x)                   = ( Pure Error       , EmptySlot        )
respJ (Conn (BotOutWire (There Here)) _ _)      impossible
respJ (Conn (BotOutWire (There (There _))) _ _) impossible
respJ (Conn (TopOutWire (There (There _))) _ _) impossible

normalJ: MessagePID (ProcIF niche) ->
         InWire niche (Either a b) ->
         (msg : Req (MkNiche [Down a, Down b] [Down (Either a b)])) ->
         ( ProcIF (MkNiche [Down a, Down b] [Down (Either a b)]) msg
         , Process (ProcIF (MkNiche [Down a, Down b] [Down (Either a b)])) () Sent Sent )
normalJ pid tar (Conn _ _ _)                          = ( Taken   , Pure ()                                         )
normalJ pid tar (Val (TopInWire Here) x)              = ( Accepted, do { Request pid (Val tar (Left  x)); Pure () } )
normalJ pid tar (Val (TopInWire (There Here)) x)      = ( Accepted, do { Request pid (Val tar (Right x)); Pure () } )
normalJ pid tar (Val (TopInWire (There (There _))) _) impossible
normalJ pid tar (Val (BotInWire (There _)) _)         impossible

joinEither': Slot (Either a b) -> Hom [Down a, Down b] [Down (Either a b)]
joinEither' slot@(FullSlot pid tar) = do Just msg <- Respond (\msg => Pure $ fst $ normalJ pid tar msg) | _ => Loop (joinEither' slot)
                                         snd $ normalJ pid tar msg
                                         Loop (joinEither' slot)
joinEither' EmptySlot = do Just msg <- Respond (\msg => fst (respJ msg)) | _ => Loop (joinEither' EmptySlot)
                           Loop $ joinEither' $ snd (respJ msg)

export joinEither: Hom [Down a, Down b] [Down (Either a b)]
joinEither = joinEither' EmptySlot

-----------------------------------
--  Symetric monoidal structure
-----------------------------------

-- we get this for free by using {join,split}Either, but would be better to make a primitive

symEither: Either a b -> Either b a
symEither (Left x)  = Right x
symEither (Right x) = Left x

export partial sym: (Show a, Show b) => Hom [Down a, Down b] [Down b, Down a]
sym = joinEither -*- (mkPure "sym: " symEither) -*- splitEither

--------------------------------------
--  Splicing
--------------------------------------

spliceEither: Either a a -> a
spliceEither (Left x)  = x
spliceEither (Right x) = x

export partial splice: Show a => Hom [Down a, Down a] [Down a]
splice = joinEither -*- (mkPure "splice: " spliceEither)
