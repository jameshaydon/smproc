module Examples

import Data.Vect
import ProcessLib
import Proto
import HoriComp
import VertComp
import Primitives
import SumWire
import Dualise
import SumWire
import CupCap
import Util

%flag C "-O3"

gt5: Hom [Down Int] [Down Int, Down Int]
gt5 = mkPure "gt5: " (\n => if n > 5 then Left n else Right n) -*- splitEither

inc: Hom [Down Int] [Down Int]
inc = mkPure "inc: " (\i => i + 1)

downIntWire: Hom [Down Int] [Down Int]
downIntWire = mkPure "down int: " id

upIntWire: Hom [Up Int] [Up Int]
upIntWire = dualise downIntWire

myProc: Hom [Down Int] []
myProc =     downIntWire + cap
         -*- (splice -*- inc -*- gt5) + upIntWire
         -*- downPrinter + cup

test: Client ()
test = do Just proc <- Spawn myProc | _ => Action (putStrLn "failed to spawn the process")
          val_resp <- Request proc (Val (TopInWire Here) 1)
          Action $ putStrLn $ "result: " ++ show val_resp
          Util.dot_sleeper 20

namespace Main
  main: IO ()
  main = runProc test
