module Main where

import System.Environment
import Dynamical.Sim
import Dynamical.Sim.Gravity
import Data.Default.Class

main :: IO ()
main = do
    [a] <- getArgs
    plotParaSimUntilToFile "20.png" "Many Bodies" (read a * 100) (rk4 0.1) example2 
