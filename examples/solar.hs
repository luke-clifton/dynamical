module Main where

import Dynamical.Sim.Internal
import Data.Default.Class

main :: IO ()
main = do
    plotParaSimUntilToFile
        "grav.svg"
        "Gravity"
        15552000 -- 180 days
        (rk4 100)
        ex9
