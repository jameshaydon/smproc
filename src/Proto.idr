module Proto

import Data.Vect
import VectHelp
import ProcessLib

%default total

namespace DirectedType
  ||| DTy = DirectedTypes = a typed wire that goes up or down
  public export data DTy = Down Type | Up Type

  public export type: DTy -> Type
  type (Down ty) = ty
  type (Up   ty) = ty

  public export dual: DTy -> DTy
  dual (Down x) = Up x
  dual (Up   x) = Down x

namespace Cut
  ||| Cut through n typed wires
  ||| These are the objects of the category
  public export Cut: Nat -> Type
  Cut n = Vect n DTy

  public export dual: Cut n -> Cut n
  dual = map dual

||| A niche is the top and bottom cut representing the full interface
||| to a process
public export data Niche: Nat -> Nat -> Type where
  MkNiche: (top: Cut m) -> (bot: Cut n) -> Niche m n

||| Incoming wires of a niche
public export data InWire: Niche m n -> Type -> Type where
  TopInWire: Elem (Down a) top -> InWire (MkNiche top bot) a
  BotInWire: Elem (Up a)   bot -> InWire (MkNiche top bot) a

||| Outgoing wires of a niche
public export data OutWire: Niche m n -> Type -> Type where
  TopOutWire: Elem (Up a)   top -> OutWire (MkNiche top bot) a
  BotOutWire: Elem (Down a) bot -> OutWire (MkNiche top bot) a

mutual
  ||| The type of messages that can be sent to a process
  public export data Req: Niche m n -> Type where
    ||| A connection request. This asks to connect one of the processes
    ||| out-wires to a specific in-wire of another process
    Conn: {niche: Niche m n} ->
          {niche': Niche m' n'} ->
          OutWire niche a -> ProcPID niche' -> InWire niche' a -> Req niche
    ||| an incoming value, on a specific in-wire
    Val:  {niche: Niche m n} ->
          (inWire: InWire niche a) -> (x: a) -> Req niche

  ||| Responses to incoming values
  public export data ValResp = Accepted | Error

  export Show ValResp where
    show Accepted = "Accepted"
    show Error = "Error"

  ||| Responses to connection requests
  public export data ConnResp = ConnAccepted | Taken

  export Show ConnResp where
    show ConnAccepted = "ConnAccepted"
    show Taken = "Taken"

  public export ProcIF: (niche: Niche m n) -> Req niche -> Type
  ProcIF niche (Conn _ _ _) = ConnResp
  ProcIF niche (Val _ _)    = ValResp

  -- to start functioning a process must have a complete mapping from its
  -- out-wires to: a process and a suitable inWire of that process

  ||| PIDs of processes that respond according to the proc intercase
  public export ProcPID: Niche m n -> Type
  ProcPID niche = MessagePID (ProcIF niche)

||| The morphisms in our category
public export Hom: Cut m -> Cut n -> Type
Hom c0 c1 = Service (ProcIF (MkNiche c0 c1)) ()

public export SubProc: Niche m n -> Type -> Type
SubProc niche a = Process (ProcIF niche) a Ready Ready

||| A slot is a place where a process can register to be sent the output
public export data Slot: Type -> Type where
  EmptySlot: Slot b
  FullSlot: {niche: Niche m n} ->
            ProcPID niche -> InWire niche b -> Slot b

-- some lemmas we need

export dualAddrUp: {c: Cut n} -> Elem (Up a) (map DirectedType.dual c) -> Elem (Down a) c
dualAddrUp {c= (Down _) :: _}  Here         = Here
dualAddrUp {c= _        :: _} (There later) = There (dualAddrUp later)
--
export dualAddrDown: {c: Cut n} -> Elem (Down a) (map DirectedType.dual c) -> Elem (Up a) c
dualAddrDown {c= (Up _) :: _}  Here         = Here
dualAddrDown {c= _      :: _} (There later) = There (dualAddrDown later)
