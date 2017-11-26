{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
module Dynamical.Sim.Gravity where

import qualified Debug.Trace as Dbg
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Dynamical.Sim
import Linear
import Data.List

data Body v t = Body
    { bodyPos :: Signal t (v t)
    , bodyVel :: Signal t (v t)
    , bodyAcc :: Signal t (v t)
    , bodyMass:: t
    }

type Force v t = v t

makeBody :: (Time t, Ord (v t), Splat t (v t), Functor v, Fractional t, Num (v t)) => v t -> v t -> t -> Signal t (Force v t) -> Sim t (Body v t)
makeBody ip iv mass f = do
    let a = fmap (^/mass) f
    v <- integral iv a
    p <- integral ip v
    return $ Body p v a mass

newtype BodyT k v t m a = BodyT
    { unBodyT :: ReaderT (Map k (Body v t)) (WriterT [(k, Signal t (Force v t))] m) a
    } deriving (Functor, Applicative, Monad)

applyDefault :: (Ord k) => a -> Map k (a -> b) -> Map k a -> Map k b
applyDefault d = Map.mergeWithKey (\k f a -> Just $ f a) (Map.map ($ d)) (const Map.empty)

runBody
    :: (Ord k, Num (v t))
    => Map k (Signal t (Force v t) -> Sim t (Body v t))
    -> BodyT k v t (Sim t) a
    -> Sim t a
runBody ic (BodyT b) = do
    rec
        (a,fm) <- runWriterT (runReaderT b final)
        let
            finalSim = applyDefault 0 ic $ Map.fromListWith (+) fm
        final <- sequence finalSim

    return a

applyForce :: (k ~ String, Show (v t), Ord k) => k -> Signal t (v t) -> BodyT k v t (Sim t) ()
applyForce k@"0_0" f = BodyT $ tell [(k,f)]
applyForce k f = BodyT $ tell [(k,f)]

getMap :: (Monad m, Ord k) => BodyT k v t m (Map k (Body v t))
getMap = BodyT ask

getBody :: (Monad m, Ord k) => k -> BodyT k v t m (Body v t)
getBody k = BodyT $ asks $ (Map.! k)

gravity :: (k ~ String, Show (v t), Num (v t), Num t, Metric v, Floating t, Ord k) => k -> k -> BodyT k v t (Sim t) ()
gravity an bn = do
    a <- getBody an
    b <- getBody bn
    let
        g = 6.674e-11
        f_num = pure $ g * bodyMass a * bodyMass b
        f = f_num / (qd <$> bodyPos a <*> bodyPos b)
        dirA = signorm <$> (bodyPos b - bodyPos a)
        dirB = signorm <$> (bodyPos a - bodyPos b)
    applyForce an ((*^) <$> f <*> dirA)
    applyForce bn ((*^) <$> f <*> dirB)

nbody :: (k ~ String, Show (v t), Eq k, Ord k, Metric v, Num (v t), Floating t) => Map k (Signal t (Force v t) -> Sim t (Body v t)) -> Sim t (Map k (Body v t))
nbody ic = runBody ic $ do
    let
        k = Map.keys ic
        kp = [(a,b) | a <- k, b <- k, a < b]
    mapM_ (uncurry gravity) kp
    getMap

mapToSignal :: Map k (Signal t a) -> Signal t (Map k a)
mapToSignal = sequenceA

example :: Sim Double (Signal Double (Map String (V2 Double)))
example =
    let
        initialConditions = Map.fromList
            [ ("Earth", makeBody 0 0 5.972e24)
            , ("Moon" , makeBody (V2 384.4e6 0) (V2 0 1.022e3) 7.3477e22)
            , ("ISS"  , makeBody (V2 (6371e3 + 408.0e3) 0) (V2 0 7.66e3) 419.5e3)
            ]
    in mapToSignal <$> fmap bodyPos <$> nbody initialConditions

example2 :: Sim Double (Signal Double (Map String (V2 Double)))
example2 =
    let
        ic = Map.fromList $ do
            i <- [0..10]
            j <- [0..10]
            let
                x = fromIntegral i
                y = fromIntegral j

            return $ (show i ++ "_" ++ show j, makeBody (V2 x y) (V2 (0.02 * sin x) (0.02 * sin y)) 1e6)
    in
        mapToSignal <$> fmap bodyPos <$> nbody ic
