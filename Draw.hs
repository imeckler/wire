{-# LANGUAGE GADTs, NoMonomorphismRestriction #-}

import WireU
import Diagrams.Prelude
import Diagrams.Backend.SVG.CmdLine

data WireDiagram
  = D { lefts  :: [Double]
      , middle :: Diagram SVG R2
      , rights :: [Double] 
      }

-- straightLine = fromVertices [p2 (0, 0), p2 (1, 0)] # strokeLine
straightLine = fromOffsets [r2 (0, 1)]

zeroElim = fromSegments [bezier3 undefined undefined (r2 (1, -0.5))]
           === straightLine

drawWire :: Wire (Ty, Ty) -> WireDiagram
drawWire Id    = D { lefts = [0], middle = mempty, rights = [0] }
drawWire PlusU =
  D { lefts = [1, 0], middle = zeroElim, rights = [0] }

main = defaultMain (middle (drawWire Id))
