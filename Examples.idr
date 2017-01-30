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
import ProcUnit
import Util

gt5: Mor [Down Int] [Down Int, Down Int]
gt5 = mkPure "gt5: " (\n => if n > 5 then Left n else Right n) -.- splitEither

inc: Mor [Down Int] [Down Int]
inc = mkPure "inc: " (\i => i + 1)

downIntWire: Mor [Down Int] [Down Int]
downIntWire = mkPure "down int: " id

upIntWire: Mor [Up Int] [Up Int]
upIntWire = dualise downIntWire

myProc: Mor [Down Int] []
myProc =     downIntWire + capS
         -.- (splice -.- inc -.- gt5) + upIntWire
         -.- downPrinter + cup

test: Client ()
test = do Just proc <- Spawn myProc | _ => Action (putStrLn "failed to spawn the process")
          val_resp <- Request proc (Val (TopInWire Here) 1)
          Action $ putStrLn $ "result: " ++ show val_resp
          Util.dot_sleeper 20

main: IO ()
main = runProc test
