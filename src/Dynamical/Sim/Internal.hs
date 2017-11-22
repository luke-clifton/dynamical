{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}

module Dynamical.Sim.Internal where

import Data.Proxy
import Data.Maybe
import Data.Fixed
import Control.Applicative
import Debug.Trace
import Control.Monad.State
import Control.Monad.Writer hiding (Any)
import Data.List
import GHC.Prim (Any)
import Unsafe.Coerce
import qualified Data.IntMap.Strict as Map
import Data.IntMap.Strict (IntMap)
import Data.Monoid hiding (Any)
import qualified Data.Monoid as Monoid
import Graphics.Rendering.Chart.Easy hiding (tan, Vector)
import Graphics.Rendering.Chart.Backend.Diagrams
import qualified Data.IntSet as Set
import Data.IntSet (IntSet)
import qualified Data.Vector.Unboxed as UV
import qualified Data.Vector.Generic as G
import qualified Data.Vector as V
import Data.Time

-- TODO: Think about sharing.

data Signal t a where
    SPure   :: a -> Signal t a
    SAp     :: Signal t (a -> b) -> Signal t a -> Signal t b
    SMap    :: (a -> b) -> Signal t a -> Signal t b
    SInt    :: Splat t a => Int -> Signal t a
    SFn     :: Int -> Signal t a
    SSwitch :: Signal t a -> Event t (Sim t (Signal t a)) -> Signal t a

instance Functor (Signal t) where
    fmap = SMap

instance Applicative (Signal t) where
    pure = SPure
    (<*>) = SAp

instance Num a => Num (Signal t a) where
    fromInteger = pure . fromInteger
    a + b = (+) <$> a <*> b
    a * b = (*) <$> a <*> b
    abs a = abs <$> a
    signum a = signum <$> a
    negate a = negate <$> a

instance Show (Signal t a) where
    show (SInt i) = "SInt " ++ show i
    show (SFn  i) = "SFn " ++ show i
    show (SMap f s) = "SMap (" ++ show s ++ ")"
    show (SAp f a) = "SAp (" ++ show f ++ ") (" ++ show a ++ ")"
    show (SSwitch s e) = "SSwitch (" ++ show s ++ ")"
    show (SPure _) = "SPure"

data Event t a where
    ERoot  :: (Num a, Ord a) => Signal t a -> Event t ()
    ETag   :: Event t a -> Signal t b -> Event t (a,b)
    EMap   :: (a -> b) -> Event t a -> Event t b

evalEvent :: Time t => Network t o -> Event t a -> a
evalEvent n (ERoot s) = ()
evalEvent n (EMap f e) = f $ evalEvent n e
evalEvent n (ETag e s) = (evalEvent n e, evalSignal n s)

instance Functor (Event t) where
    fmap = EMap

newtype Sim t a = Sim {unSim :: forall o. State (Network t o) a}

class Integrable t a where
    integrate :: a -> Signal t a -> Sim t (Signal t a)

instance (Integrable t a, Integrable t b) => Integrable t (a,b) where
    integrate (a,b) s = do
        a' <- integrate a (fmap fst s)
        b' <- integrate b (fmap snd s)
        return $ (,) <$> a' <*> b'

instance (Integrable t a, Integrable t b, Integrable t c) => Integrable t (a,b,c) where
    integrate (a,b,c) s = do
        a' <- integrate a (fmap (\(a,_,_) -> a) s)
        b' <- integrate b (fmap (\(_,b,_) -> b) s)
        c' <- integrate c (fmap (\(_,_,c) -> c) s)
        return $ (,,) <$> a' <*> b' <*> c'

instance Time t => Integrable t t where
    integrate a s = integral a s

{-
integral :: Time t => t -> Signal t t -> Sim t (Signal t t)
integral i s = Sim $ do
    st <- get
    let
        ix = G.length (netIntState st)
    put st
        { netIntState = netIntState st `G.snoc` i
        , netIntDeriv = netIntDeriv st `G.snoc` (fmap splat s)
        }
    return $ SInt ix
-}

class Splat t a where
    splen :: Proxy t -> Proxy a -> Int
    splat :: Time t => a -> NetStore t
    unsplat :: Time t => NetStore t -> a

instance Splat t t where
    splen _ _ = 1
    splat t = G.singleton t
    unsplat v = v G.! 0

instance Time t => Splat t (t,t) where
    splen _ _ = 2
    splat (a,b) = G.fromList [a,b]
    unsplat v = (v G.! 0, v G.! 1)

integral :: (Splat t a, Time t) => a -> Signal t a -> Sim t (Signal t a)
integral i s = Sim $ do
    st <- get
    let
        sp = splat i
        ix = G.length (netIntState st)
    put st
        { netIntState = netIntState st G.++ sp
        , netIntDeriv = Map.insert ix (fmap splat s) (netIntDeriv st)
        }
    return $ SInt ix

timeFn' :: t -> (t -> a) -> Sim t (Signal t a)
timeFn' t f = Sim $ do
    st <- get
    let
        mix = Map.maxViewWithKey . netFnS $ st
        ix = maybe 0 (succ . fst . fst) mix
    put st
        { netFnS = Map.insert ix (FnS t (unsafeCoerce . f)) (netFnS st)
        }
    return $ SFn ix

switch :: Signal t a -> Event t (Sim t (Signal t a)) -> Signal t a
switch s e = become s (fmap (\s' -> s' >>= \s'' -> pure (switch s'' e)) e)

becomeOn :: Signal t a -> Event t b -> (b -> Sim t (Signal t a)) -> Signal t a
becomeOn s e f = become s (fmap f e)

timeFn :: Num t => (t -> a) -> Sim t (Signal t a)
timeFn = timeFn' 0

become :: Signal t a -> Event t (Sim t (Signal t a)) -> Signal t a
become = SSwitch

root :: (Ord a, Num a) => Signal t a -> Event t ()
root = ERoot

tag :: Event t a -> Signal t b -> Event t (a,b)
tag  = ETag

instance Functor (Sim t) where
    fmap f (Sim s) = Sim (fmap f s)

instance Applicative (Sim t) where
    pure a = Sim (pure a)
    (Sim f) <*> (Sim a) = Sim (f <*> a)

instance Monad (Sim t) where
    (Sim a) >>= f = Sim $ do
        r <- a
        let (Sim k) = f r
        k

instance MonadFix (Sim t) where
    mfix f = Sim $ mfix (unSim . f)


data FnS t = FnS
    { fnLocalTime :: !t
    , fnFunc      :: !(t -> Any)
    }

fnApply :: FnS t -> Any
fnApply FnS{..} = fnFunc fnLocalTime

instance Show t => Show (FnS t) where
    show FnS{..} = "FnS " ++ show fnLocalTime

type family NetStore' a :: * -> *
type instance NetStore' Double = UV.Vector
type instance NetStore' Float = UV.Vector
type instance NetStore' Word = UV.Vector
type instance NetStore' Int = UV.Vector

type NetStore t = NetStore' t t

type Time t = (G.Vector (NetStore' t) t)

data Network t o = Network
    { netIntState :: NetStore t
    , netIntDeriv :: IntMap (Signal t (NetStore t))
    , netFnS      :: IntMap (FnS t)
    , netRoot     :: Signal t o
    }

-- TODO: Rewrite
gc :: forall v t o. Time t => Network t o -> Network t o
gc n@Network{..} =
    let
        (intReachable, fnReachable) = findNames netRoot

        findNames :: Signal t a -> (IntSet, IntSet)
        findNames s = execState (go s)  mempty

        go :: Signal t a -> State (IntSet,IntSet) ()
        go (SInt ix) = do
            (i,f) <- get
            when (not $ Set.member ix i) $ do
                put (Set.insert ix i, f)
                go (netIntDeriv Map.! ix)
        go (SAp a b) = go a >> go b
        go (SMap _ s) = go s
        go (SPure _) = return ()
        go (SFn ix) = modify $ mappend (mempty, Set.singleton ix)
        go (SSwitch s e) = go s >> goE e

        goE :: Event t a -> State (IntSet, IntSet) ()
        goE (ERoot s) = go s
        goE (EMap _ e) = goE e
        goE (ETag e s) = goE e >> go s
        
        intMap  = UV.fromList (Set.toAscList intReachable)
        intMap' = Map.fromList $ zip (Set.toAscList intReachable) [0..]

        rename :: IntMap Int -> Signal t a -> Signal t a
        rename m (SAp a b) = SAp (rename m a) (rename m b)
        rename m (SMap f a) = SMap f (rename m a)
        rename m s@(SPure _) = s
        rename m (SInt ix) = SInt (m Map.! ix)
        rename m s@SFn{} = s
        rename m (SSwitch s e) = SSwitch (rename m s) (renameE m e)

        renameE :: IntMap Int -> Event t a -> Event t a
        renameE m (ERoot s) = ERoot (rename m s)
        renameE m (EMap f e) = EMap f (renameE m e)
        renameE m (ETag e s) = ETag (renameE m e) (rename m s)

        intCnt = UV.length intMap

        intState' = G.generate intCnt $ \ix -> netIntState G.! (intMap UV.! ix)
        -- intDeriv' = G.generate intCnt $ \ix -> netIntDeriv Map.! (intMap UV.! ix)

        restrictKeys m s = Map.filterWithKey (\k _ -> k `Set.member` s) m
        intDeriv' = restrictKeys netIntDeriv intReachable

        fnS' = restrictKeys netFnS fnReachable

    in n
        { netIntState = intState'
        , netIntDeriv = fmap (rename intMap') intDeriv'
        , netFnS = fnS'
        , netRoot = rename intMap' netRoot
        }

eventOccured :: Time t => Network t o -> Network t o -> Event t a -> Maybe a
eventOccured old new (EMap f e) = f <$> eventOccured old new e
eventOccured old new (ETag e s) = flip (,) (evalSignal new s) <$> eventOccured old new e
eventOccured old new (ERoot s)
    | oldS < 0 && 0 <= newS = Just ()
    | newS <= 0 && 0 < oldS = Just ()
    | otherwise = Nothing
        where
            oldS = evalSignal old s
            newS = evalSignal new s

runSwitches' :: forall v t o. Time t => Network t o -> Network t o -> (Bool, Network t o)
runSwitches' old new =
    let
        go :: Signal t a -> WriterT Monoid.Any (Sim t) (Signal t a)
        go s@(SPure a) = return s
        go (SMap f s) = go s >>= pure . SMap f
        go (SAp f a) = do
            f' <- go f
            a' <- go a
            return $ SAp f' a'
        go s@(SInt ix) = return s
        go s@(SFn ix) = return s
        go (SSwitch s e) = case eventOccured old new e of
            Just v -> tell (Monoid.Any True) >> lift v
            Nothing -> do
                s' <- go s
                e' <- goE e
                return $ SSwitch s' e'

        goE :: Event t a -> WriterT Monoid.Any (Sim t) (Event t a)
        goE (ERoot s) = go s >>= pure . ERoot
        goE (EMap f e) = goE e >>= pure . EMap f
        goE (ETag e s) = do
            e' <- goE e
            s' <- go s
            return (ETag e' s')
        
        ((root', changed), net') = addSim new $ runWriterT (go $ netRoot new) 
    in 
        if getAny changed
        then (getAny changed, gc $ net'
            { netRoot = root'
            })
        else (getAny changed, new)
        
runSwitches old new = snd $ runSwitches' old new
anyEvent old new = fst $ runSwitches' old new

newtype Integrator t o = Integrator
    { runIntegrator :: Network t o -> (Network t o, t, Integrator t o)
    }

newDoubleSim :: Sim Double (Signal Double a) -> Network Double a
newDoubleSim = newSim

newSim :: Time t => Sim t (Signal t a) -> Network t a
newSim (Sim s) =
    let
        (r,n) = runState s Network
            { netIntState = G.empty
            , netIntDeriv = Map.empty
            , netFnS  = mempty
            , netRoot = r
            }
    in n

addSim :: Time t => Network t o -> Sim t a -> (a, Network t o)
addSim n (Sim s) = runState s n



evalSignal :: forall t o a. Time t => Network t o -> Signal t a -> a
evalSignal c (SPure a) = a
evalSignal c (SMap f s) = f $ evalSignal c s
evalSignal c (SAp f a) = evalSignal c f $ evalSignal c a
evalSignal c (SFn ix) = unsafeCoerce . fnApply $ netFnS c Map.! ix
evalSignal c (SInt ix) = unsplat $ G.slice ix (splen (Proxy :: Proxy t) (Proxy :: Proxy a)) (netIntState c)
evalSignal c (SSwitch s _) = evalSignal c s

evalRoot :: Time t => Network t o -> o
evalRoot c = evalSignal c (netRoot c)

deltaNet :: (Num t, Time t) => Network t o -> t -> NetStore t -> Network t o
deltaNet n@Network{..} h dv = (deltaNetTime n h)
    { netIntState = G.zipWith (+) netIntState dv
    }

deltaNetTime :: (Num t, Time t) => Network t o -> t -> Network t o
deltaNetTime n@Network{..} h = n
    { netFnS  = Map.map (\s@FnS{..} -> s {fnLocalTime = fnLocalTime + h}) netFnS
    }


derivs :: (Num t, Time t) => Network t o -> t -> NetStore t -> NetStore t
derivs n h dv =
    let
        n' = deltaNet n h dv
    in G.concat $ map (evalSignal n' . snd) $ Map.toAscList $ netIntDeriv n'

derivsNow :: (Time t) => Network t o -> NetStore t
derivsNow n = G.concat $ map (evalSignal n . snd) $ Map.toAscList $ netIntDeriv n

simulateDouble
    :: Integrator Double o
    -> Sim Double (Signal Double o)
    -> [(Double,Network Double o)]
simulateDouble = simulate

simulate :: forall v t o. (Num t, Time t) => Integrator t o -> Sim t (Signal t o) -> [(t,Network t o)]
simulate integrator s =
    let
        n = newSim s
    in unfoldr (\(i,n,t) ->
        let
            (n',r,i') =  runIntegrator i n
            t' = t + r
        in
            Just ( (t, n)        -- Previous step
                 , (i', n', t')
                 )
        ) (integrator,n,0)

replace :: Signal t a -> Event t (Sim t (Signal t a)) -> Signal t a
replace = SSwitch


--------------------------------

euler :: (Num t, Time t) => t -> Integrator t o
euler h = integrator
    where
        integrator = Integrator go
        go n =
            let
                ds = derivsNow n
                n' = deltaNet n h (G.map (*h) ds)
            in (runSwitches n n', h, integrator)

eulerBisect :: (Fractional t, Ord t, Time t) => t -> t -> Integrator t o
eulerBisect tol h = integrator
    where
        integrator = Integrator $ go h
        go h' n =
            let
                ds = derivsNow n
                n' = deltaNet n h' (G.map (*h) ds)
                (e,n'') = runSwitches' n n'
                res
                    -- TODO: Don't emit nearby points, jump strait to it.
                    | e && h' > tol = go (h'/2) n
                    | otherwise = (n'', h', integrator)
            in res
                


rk4 :: (Fractional t, Time t) => t -> Integrator t o
rk4 h = integrator
    where
        integrator = Integrator go
        go n =
            let
                h2 = h / 2
                h6 = h / 6
                k1 = derivsNow n
                k2 = derivs n h2 (G.map (*h2) k1)
                k3 = derivs n h2 (G.map (*h2) k2)
                k4 = derivs n h  (G.map (*h)  k3)
                n' = deltaNet n h (G.map (* h6)
                    $ G.zipWith4 (\a b c d -> a + 2 * b + 2 * c + d) k1 k2 k3 k4)
            in
                (runSwitches n n', h, integrator)

runRk4RealTime :: forall a. Show a => Sim Double (Signal Double a) -> IO ()
runRk4RealTime s =
    let
        n = newSim s
        go :: UTCTime -> Network Double a -> IO ()
        go prev n = do
            now <- getCurrentTime
            let
                h = realToFrac $ diffUTCTime now prev
                (n',_,_) = runIntegrator (rk4 h) n
            print $ evalRoot n'
            go now n'
    in do
        now <- getCurrentTime
        go now n

--------------------------------

example :: (Time t, Fractional t) => Sim t (Signal t (t, t))
example = do
    rec a <- integral 0.5 a
    b <- integral 0 1
    return $ (,) <$> a <*> b

ex2 :: forall t. (Fractional t, Ord t, Time t) => Sim t (Signal t t)
ex2 = do
    t <- integral (5 :: t) (-1)
    let
        e = root t
        e' = fmap (const $ pure 3) e
    return $ become 1 e'

ex3 :: (Floating t, Ord t) => Sim t (Signal t (t,t))
ex3 = do
    t <- timeFn sin
    let
        e = tag (root t) (signum t)
        e' = fmap (\(_,v) -> return $ pure v) e
    return $ (,) <$> t <*> switch 0 e'

ex4 :: (Floating t, Time t) => Sim t (Signal t (t,t))
ex4 = do
    s <- timeFn sin
    s' <- integral (-1) s >>= integral 0 >>= integral 1 >>= integral 0
    return $ (,) <$> s <*> s'

