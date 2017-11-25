{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
module Dynamical.Sim.Gravity where

import Control.Monad.Reader
import Control.Monad.Writer
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Dynamical.Sim
import Linear

data Body v t = Body
    { bodyPos :: Signal t (v t)
    , bodyVel :: Signal t (v t)
    , bodyAcc :: Signal t (v t)
    , bodyMass:: t
    }

newtype Force v t = Force {toV :: v t}
    deriving (Show, Eq, Ord, Num, Fractional, Floating, RealFloat, RealFrac, Real)

instance Num (v t) => Monoid (Force v t) where
    mempty = 0
    mappend a b = a + b

makeBody :: (Time t, Splat t (v t), Functor v, Fractional t, Num (v t)) => v t -> v t -> t -> Signal t (Force v t) -> Sim t (Body v t)
makeBody ip iv mass f = do
    let a = fmap ((^/mass) . toV) f
    v <- integral iv a
    p <- integral ip v
    return $ Body p v a mass

newtype BodyT k v t m a = BodyT
    { unBodyT :: ReaderT (Map k (Body v t)) (WriterT (Map k (Signal t (Force v t))) m) a
    } deriving (Functor, Applicative, Monad)

applyMempty :: (Ord k, Monoid a) => Map k (a -> b) -> Map k a -> Map k b
applyMempty = Map.mergeWithKey (\k f a -> Just $ f a) (Map.map ($ mempty)) (const Map.empty)

runBody
    :: (Ord k, Num (v t))
    => Map k (Signal t (Force v t) -> Sim t (Body v t))
    -> BodyT k v t (Sim t) a
    -> Sim t a
runBody ic (BodyT b) = do
    rec
        (a,fm) <- runWriterT (runReaderT b final)
        let
            finalSim = applyMempty ic fm
        final <- sequence finalSim

    return a

applyForce :: Ord k => k -> Signal t (v t) -> BodyT k v t (Sim t) ()
applyForce k f = BodyT $ tell (Map.singleton k (Force <$> f))

getMap :: (Monad m, Ord k) => BodyT k v t m (Map k (Body v t))
getMap = BodyT ask

getBody :: (Monad m, Ord k) => k -> BodyT k v t m (Body v t)
getBody k = BodyT $ asks $ (Map.! k)

gravity :: (Num (v t), Num t, Metric v, Floating t, Ord k) => k -> k -> BodyT k v t (Sim t) ()
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

nbody :: (Eq k, Ord k, Metric v, Num (v t), Floating t) => Map k (Signal t (Force v t) -> Sim t (Body v t)) -> Sim t (Map k (Body v t))
nbody ic = runBody ic $ do
    let
        k = Map.keys ic
        kp = [(a,b) | a <- k, b <- k, a > b]
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
                x = 300e6 * fromIntegral i
                y = 300e6 * fromIntegral j

            return $ (show i ++ "_" ++ show j, makeBody (V2 x y) (V2 0 0) 5e20)
    in
        mapToSignal <$> fmap bodyPos <$> nbody ic
