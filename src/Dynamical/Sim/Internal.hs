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

import Control.Applicative
import Control.Monad
import Control.Monad.Fix (MonadFix(mfix))
import Control.Monad.State (StateT, State, get, put, runState, modify, execState, evalState)
import Control.Monad.Trans (lift)
import Control.Monad.Writer (Writer, tell, WriterT, runWriterT)
import Data.Complex (Complex((:+)))
import Data.Fixed (Fixed)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as Map
import Data.IntSet (IntSet)
import qualified Data.IntSet as Set
import Data.List
import Data.Maybe
import Data.Monoid (Monoid(), Any(Any), (<>), mempty, mappend)
import Data.Proxy (Proxy(Proxy))
import Data.Scientific (Scientific)
import Data.StableMemo (memo)
import Data.Time (getCurrentTime, diffUTCTime, UTCTime)
import qualified Data.Vector as V
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Mutable as VM
import qualified Data.Vector.Unboxed as UV
import qualified Data.Vector.Unboxed.Mutable as UM
import Debug.Trace
import qualified GHC.Prim as Prim
import Linear (V1(..), V2(..), V3(..), V4(..), norm)
import System.IO.Unsafe (unsafePerformIO)
import System.Mem.StableName (hashStableName,eqStableName,StableName,makeStableName)
import Unsafe.Coerce (unsafeCoerce)

-------------------------------------------------------------------
-- Signal
-------------------------------------------------------------------

-- | A `Signal t a` represents a time varying value of type `a`, where
-- time is measured using a `t`.
data Signal t a where
    SPure   :: a -> Signal t a
    SAp     :: Signal t (a -> b) -> Signal t a -> Signal t b
    SMap    :: (a -> b) -> Signal t a -> Signal t b
    SInt    :: Splat t a => Int -> Signal t a
    SFn     :: Int -> (t -> a) -> Signal t a
    SSwitch :: Signal t a -> Event t (Sim t (Signal t a)) -> Signal t a
    SShare  :: Signal t a -> Signal t a

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

-------------------------------------------------------------------
-- Event
-------------------------------------------------------------------

-- | An `Event t a` represents a series of instantaneous events.
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

-------------------------------------------------------------------
-- Sim
-------------------------------------------------------------------

-- | The `Sim t` monad is used for constructing certain `Signal` values.
newtype Sim t a = Sim {unSim :: forall o. State (Network t o) a}

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

-------------------------------------------------------------------
-- Network
-------------------------------------------------------------------

-- | This type family is used for determining the best way to store
-- a vector of values. It should evaluate to something that is an
-- instance of @Data.Vector.Generic.Vector@.
type family NetStoreVec a :: * -> *
type instance NetStoreVec Double = UV.Vector
type instance NetStoreVec Float = UV.Vector
type instance NetStoreVec Word = UV.Vector
type instance NetStoreVec Int = UV.Vector
type instance NetStoreVec (Fixed a) = V.Vector
type instance NetStoreVec Scientific = V.Vector

type NetStore t = NetStoreVec t t
type NetStoreMut t = G.Mutable (NetStoreVec t) t

type Time t = (G.Vector (NetStoreVec t) t, Show (NetStore t))

-- | A `Network` represents a compiled simulation.
data Network t o = Network
    { netIntState :: NetStore t
    , netIntDeriv :: IntMap (Signal t (NetStore t))
    , netFnTime   :: NetStore t
    , netRoot     :: Signal t o
    }

-- TODO: Rewrite

-- | Cleans up a `Network` after a switching event, removing signals
-- that are no longer needed.
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
        go (SFn ix _) = modify $ mappend (mempty, Set.singleton ix)
        go (SSwitch s e) = go s >> goE e
        go (SShare s) = go s

        goE :: Event t a -> State (IntSet, IntSet) ()
        goE (ERoot s) = go s
        goE (EMap _ e) = goE e
        goE (ETag e s) = goE e >> go s
        
        intMap  = UV.fromList (Set.toAscList intReachable)
        intMap' = Map.fromList $ zip (Set.toAscList intReachable) [0..]

        fnMap   = UV.fromList (Set.toAscList fnReachable)

        rename :: IntMap Int -> Signal t a -> Signal t a
        rename m (SAp a b) = SAp (rename m a) (rename m b)
        rename m (SMap f a) = SMap f (rename m a)
        rename m s@(SPure _) = s
        rename m (SInt ix) = SInt (m Map.! ix)
        rename m s@SFn{} = s
        rename m (SSwitch s e) = SSwitch (rename m s) (renameE m e)
        rename m (SShare s) = SShare (rename m s)

        renameE :: IntMap Int -> Event t a -> Event t a
        renameE m (ERoot s) = ERoot (rename m s)
        renameE m (EMap f e) = EMap f (renameE m e)
        renameE m (ETag e s) = ETag (renameE m e) (rename m s)

        intCnt = UV.length intMap
        fnCnt  = UV.length fnMap

        intState' = G.generate intCnt $ \ix -> netIntState G.! (intMap UV.! ix)

        restrictKeys m s = Map.filterWithKey (\k _ -> k `Set.member` s) m
        intDeriv' = restrictKeys netIntDeriv intReachable

        fnTime' = G.generate fnCnt $ \ix -> netFnTime G.! (fnMap UV.! ix)

    in n
        { netIntState = intState'
        , netIntDeriv = fmap (rename intMap') intDeriv'
        , netFnTime = fnTime'
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
        go :: Signal t a -> WriterT Any (Sim t) (Signal t a)
        go s@(SPure a) = return s
        go (SMap f s) = go s >>= pure . SMap f
        go (SAp f a) = do
            f' <- go f
            a' <- go a
            return $ SAp f' a'
        go s@(SInt ix) = return s
        go s@(SFn ix f) = return s
        go (SSwitch s e) = case eventOccured old new e of
            Just v -> tell (Any True) >> lift v
            Nothing -> do
                s' <- go s
                e' <- goE e
                return $ SSwitch s' e'
        go (SShare s) = go s >>= pure . SShare

        goE :: Event t a -> WriterT Any (Sim t) (Event t a)
        goE (ERoot s) = go s >>= pure . ERoot
        goE (EMap f e) = goE e >>= pure . EMap f
        goE (ETag e s) = do
            e' <- goE e
            s' <- go s
            return (ETag e' s')
        
        ((root', Any changed), net') = addSim new $ runWriterT (go $ netRoot new) 
    in 
        if changed
        then (changed, gc $ net'
            { netRoot = root'
            })
        else (changed, new)
        
runSwitches old new = snd $ runSwitches' old new
anyEvent old new = fst $ runSwitches' old new

newDoubleSim :: Sim Double (Signal Double a) -> Network Double a
newDoubleSim = newSim

newSim :: Time t => Sim t (Signal t a) -> Network t a
newSim (Sim s) =
    let
        (r,n) = runState s Network
            { netIntState = G.empty
            , netIntDeriv = Map.empty
            , netFnTime  = G.empty
            , netRoot = r
            }
    in n

addSim :: Time t => Network t o -> Sim t a -> (a, Network t o)
addSim n (Sim s) = runState s n

-- TODO: Below are three implementations of evalSignal. Each with different
-- sharing characteristics.
--  * evalSignal' does explicit sharing
--  * evalSignal'' does no sharing
--  * evalSignal''' does implicit sharing
-- We need to benchmark and determine which is best.
-- Once we determine which solution to go for, we should integrate it
-- more with the rest of the code such that sharing caries over to
-- events.
evalSignal'
    :: forall t o a. (Time t)
    => Network t o -> Signal t a -> State (IntMap (StableName Prim.Any, Any)) a
evalSignal' c me@(SShare s) = do
    m <- get
    let
        name = unsafePerformIO $ makeStableName me
        nameh = hashStableName name
        mv = do
            (n,v) <- Map.lookup nameh m
            if eqStableName name n
            then return $ unsafeCoerce v
            else Nothing
    case mv of
        Just v -> return v
        Nothing -> do
            v' <- evalSignal' c s
            put $ Map.insert nameh (unsafeCoerce name, unsafeCoerce v') m
            return v'
evalSignal' c (SPure a) = return a
evalSignal' c (SMap f s) = f <$> evalSignal' c s
evalSignal' c (SAp f a) = do
    f' <- evalSignal' c f
    a' <- evalSignal' c a
    return $ f' a'
evalSignal' c (SFn ix f) = return $ f $ netFnTime c G.! ix
evalSignal' c (SInt ix) = do
    let
        len = splen (Proxy :: Proxy t) (Proxy :: Proxy a)
    return $ unsplat $ G.slice ix len (netIntState c)
evalSignal' c (SSwitch s _) = evalSignal' c s

evalSignal'' :: forall t o a. Time t => Network t o -> Signal t a -> a
evalSignal'' c (SPure a) = a
evalSignal'' c (SMap f s) = f $ evalSignal c s
evalSignal'' c (SAp f a) = evalSignal c f $ evalSignal c a
evalSignal'' c (SFn ix f) = f $ netFnTime c G.! ix
evalSignal'' c (SInt ix) = unsplat $ G.slice ix (splen (Proxy :: Proxy t) (Proxy :: Proxy a)) (netIntState c)
evalSignal'' c (SSwitch s _) = evalSignal c s
evalSignal'' c (SShare s) = evalSignal c s

evalSignal''' :: forall t o a. Time t => Network t o -> Signal t a -> a
evalSignal''' c = go
    where
        go :: Signal t c -> c
        go = memo gogo

        gogo :: forall b. Signal t b -> b
        gogo (SPure a) = a
        gogo (SMap f s) = f $ go s
        gogo (SAp f a) = go f $ go a
        gogo (SFn ix f) = f $ netFnTime c G.! ix
        gogo (SInt ix) = unsplat $ G.slice ix (splen (Proxy :: Proxy t) (Proxy :: Proxy b)) (netIntState c)
        gogo (SSwitch s _) = go s
        gogo (SShare s) = go s

evalSignal :: forall t o a. Time t => Network t o -> Signal t a -> a
--evalSignal n s = evalState (evalSignal' n s) mempty
--evalSignal = evalSignal''
evalSignal = evalSignal'''
--evalSignal n = memo (evalSignal'' n)
--{-# NOINLINE evalSignal #-}

evalRoot :: Time t => Network t o -> o
evalRoot c = evalSignal c (netRoot c)

deltaNet :: (Num t, Time t) => Network t o -> t -> NetStore t -> Network t o
deltaNet n@Network{..} h dv = (deltaNetTime n h)
    { netIntState = G.zipWith (+) netIntState dv
    }

deltaNetTime :: (Num t, Time t) => Network t o -> t -> Network t o
deltaNetTime n@Network{..} h = n
    { netFnTime  = G.map (+h) netFnTime
    }

derivs :: (Num t, Time t) => Network t o -> t -> NetStore t -> NetStore t
derivs n h dv =
    let
        n' = deltaNet n h dv
    in derivsNow n'

derivsNow :: (Time t) => Network t o -> NetStore t
derivsNow n = G.concat $ map (evalSignal n . snd) $ Map.toAscList $ netIntDeriv n


-------------------------------------------------------------------
-- Splat
-------------------------------------------------------------------

class Splat t a where
    splen :: Proxy t -> Proxy a -> Int
    splat :: Time t => a -> NetStore t
    unsplat :: Time t => NetStore t -> a

instance Splat t t where
    splen _ _ = 1
    splat t = G.singleton t
    unsplat v = v G.! 0

instance Splat t (t,t) where
    splen t _ = 2
    splat (a,b) = splat a G.++ splat b
    unsplat v = (v G.! 0, v G.! 1)

instance Splat t (t,t,t) where
    splen t _ = 3
    splat (a,b,c) = G.fromList [a,b,c]
    unsplat v = (v G.! 0, v G.! 1, v G.! 2)

instance Splat t (t,t,t,t) where
    splen t _ = 4
    splat (a,b,c,d) = G.fromList [a,b,c,d]
    unsplat v = (v G.! 0, v G.! 1, v G.! 2, v G.! 3)

instance Splat t (Complex t) where
    splen t _ = 2
    splat (a :+ b) = G.fromList [a,b]
    unsplat v = (v G.! 0) :+ (v G.! 1)

instance Splat t (V1 t) where
    splen t _ = splen t (Proxy :: Proxy t)
    splat (V1 a) = splat a
    unsplat = V1 . unsplat

instance Splat t (V2 t) where
    splen t _ = splen t (Proxy :: Proxy (t,t))
    splat (V2 a b) = splat (a,b)
    unsplat v = let (a,b) = unsplat v in V2 a b

instance Splat t (V3 t) where
    splen t _ = splen t (Proxy :: Proxy (t,t,t))
    splat (V3 a b c) = splat (a,b,c)
    unsplat v = let (a,b,c) = unsplat v in V3 a b c

instance Splat t (V4 t) where
    splen t _ = splen t (Proxy :: Proxy (t,t,t,t))
    splat (V4 a b c d) = splat (a,b,c,d)
    unsplat v = let (a,b,c,d) = unsplat v in V4 a b c d

-------------------------------------------------------------------
-- API
-------------------------------------------------------------------

-- | Integrate the input `Signal` with respect to time.
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

-- | Create a `Signal` that is a pure function of time. Each `timeFn'` has
-- a local concept of time, and this time starts from the provided time
-- value.
timeFn' :: Time t => t -> (t -> a) -> Sim t (Signal t a)
timeFn' t f = Sim $ do
    st <- get
    let
        ix = G.length (netFnTime st)
    put st
        { netFnTime = netFnTime st `G.snoc` t
        }
    return $ SFn ix f

-- | As `timeFn'` but local time starts at 0.
timeFn :: (Time t, Num t) => (t -> a) -> Sim t (Signal t a)
timeFn = timeFn' 0

-- | Start out as the input `Signal`, but when the `Event` occurs, become
-- the signal that it carries, and remain as that signal forever. Future
-- `Event`s from this event source will be ignored. See `switch` for
-- alternate behavior.
become :: Signal t a -> Event t (Sim t (Signal t a)) -> Signal t a
become = SSwitch

-- | Start out as the input `Signal` and everytime the `Event` occurs, change
-- to the new `Signal` carried in the `Event`. This can easily cause
-- a space leak if used recursively. Look at `become` for a safer solution.
switch :: Signal t a -> Event t (Sim t (Signal t a)) -> Signal t a
switch s e = become s (fmap (\s' -> s' >>= \s'' -> pure (switch s'' e)) e)

-- | Useful combination of `become` and `fmap`
becomeOn :: Signal t a -> Event t b -> (b -> Sim t (Signal t a)) -> Signal t a
becomeOn s e f = become s (fmap f e)

-- | Turns the input `Signal t a` into a `Signal t (Maybe a)`, resulting
-- in `Nothing` as soon as the `Event` fires, and remaining `Nothing` forever
-- after that point.
becomeNothingOn :: Signal t a -> Event t b -> Signal t (Maybe a)
becomeNothingOn s e = becomeOn (fmap Just s) e $ \_ -> return $ pure Nothing


-- | Memoize the result of evaluating this Signal so that repeated
-- uses don't have to re-evaluate everything. Integrations are
-- already shared by default, so avoid sharing them directly.
--
-- TODO: Depending on the signal evaluation strategy (see comments in code)
-- sharing may implicitly happen for all signals, or not at all.
share :: Signal t a -> Signal t a
share = SShare

-- | Emit an event every time the input `Signal` crosses 0.
root :: (Ord t, Num t) => Signal t t -> Event t ()
root = ERoot

-- | Tag the given event with the value of the signal when it occurs.
tag :: Event t a -> Signal t b -> Event t (a,b)
tag  = ETag

-------------------------------------------------------------------
-- Simulation
-------------------------------------------------------------------

-- | Run the `Integrator` over the given `Signal` outputting a list of
-- time stamp and `Network`s.
simulate' :: forall v t o. (Num t, Time t) => Integrator t o -> Sim t (Signal t o) -> [(t,Network t o)]
simulate' integrator s =
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

-- | Run the `Integrator` over the given `Signal`, outputting a list of
-- time stamp and signal values.
simulate :: (Num t, Time t) => Integrator t o -> Sim t (Signal t o) -> [(t,o)]
simulate i s = fmap evalRoot <$> simulate' i s

-- | `simulate'` specialised to `Double`
simulateDouble'
    :: Integrator Double o
    -> Sim Double (Signal Double o)
    -> [(Double,Network Double o)]
simulateDouble' = simulate'

-- | `simulate` specialised to `Double`
simulateDouble
    :: Integrator Double o
    -> Sim Double (Signal Double o)
    -> [(Double,o)]
simulateDouble = simulate

-- | `simulate` which stops as soon as the `Signal` value becomes `Nothing`
simulateJust :: (Num t, Time t) => Integrator t (Maybe o) -> Sim t (Signal t (Maybe o)) -> [(t,o)]
simulateJust i s = fmap (\(t,Just x) -> (t,x)) $ takeWhile (isJust . snd) $ simulate i s

-- | `simulateJust` specialised to `Double`
simulateJustDouble :: Integrator Double (Maybe o) -> Sim Double (Signal Double (Maybe o)) -> [(Double,o)]
simulateJustDouble = simulateJust

-- | Run a simulation in real time, printing the result values to the terminal.
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

-- | Same as `runRk4RealTime` but stops when a `Nothing` value is produced.
runRk4RealTimeJust :: forall a. Show a => Sim Double (Signal Double (Maybe a)) -> IO ()
runRk4RealTimeJust s =
    let
        n = newSim s
        go :: UTCTime -> Network Double (Maybe a) -> IO ()
        go prev n = do
            now <- getCurrentTime
            let
                h = realToFrac $ diffUTCTime now prev
                (n',_,_) = runIntegrator (rk4 h) n
            case evalRoot n' of
                Nothing -> return ()
                Just x -> print x >> go now n'
    in do
        now <- getCurrentTime
        go now n


-------------------------------------------------------------------
-- Integrators
-------------------------------------------------------------------

newtype Integrator t o = Integrator
    { runIntegrator :: Network t o -> (Network t o, t, Integrator t o)
    }

euler :: (Num t, Time t) => t -> Integrator t o
euler h = integrator
    where
        integrator = Integrator go
        go n =
            let
                ds = derivsNow n
                n' = deltaNet n h (G.map (*h) ds)
            in (runSwitches n n', h, integrator)

-- | Same as `euler` except that it bisects around `Event`s until it is within
-- the provided tolerance.
eulerBisect :: (Fractional t, Ord t, Time t) => t -> t -> Integrator t o
eulerBisect tol h = integrator
    where
        integrator = Integrator $ go h
        go h' n =
            let
                ds = derivsNow n
                n' = deltaNet n h' (G.map (*h') ds)
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


-------------------------------------------------------------------
-- Examples/Test
-------------------------------------------------------------------

-- Ex1 demonstrates basic integration with recursion.
ex1 :: (Time t, Fractional t) => Sim t (Signal t (t, t))
ex1 = do
    rec a <- integral 0.5 a
    b <- integral 0 1
    return $ (,) <$> a <*> b

-- Ex2 shows how to use `become` to change a singal to a new one upon
-- an event.
ex2 :: forall t. (Fractional t, Ord t, Time t) => Sim t (Signal t t)
ex2 = do
    t <- integral 5 (-1)
    let
        e = root t
        e' = fmap (const $ pure 3) e
    return $ become 1 e'

-- Ex3 show the use of `switch` to control a signal.
ex3 :: (Time t, Floating t, Ord t) => Sim t (Signal t (t,t))
ex3 = do
    t <- timeFn sin
    let
        e = tag (root t) (signum t)
        e' = fmap (\(_,v) -> return $ pure v) e
    return $ (,) <$> t <*> switch 0 e'


-- Ex4 can be used to demonstrate the accuracy of various integrators.
ex4 :: (Floating t, Time t) => Sim t (Signal t (t,t))
ex4 = do
    s <- timeFn sin
    s' <- integral (-1) s >>= integral 0 >>= integral 1 >>= integral 0
    return $ (,) <$> s <*> s'

-- Ex5 demonstrates using `Maybe` to terminate a simulation with
-- `simulateJust`.
--
-- Note: The use of an `Event` rather than `fmap`ing over the signal
-- causes the root finding algorithm of many integrators to kick in allowing
-- for very precise finishing times.
ex5 :: (Floating t, Time t, Ord t) => Sim t (Signal t (Maybe (V4 t)))
ex5 = do
    i <- (integral 0 $ pure (V4 0 1 2 (-0.5)) )
    let
        s = fmap (\i -> 5 - norm i) i
        e = root s
    return $ i `becomeNothingOn` e

-- Ex6 demonstrates the use of `share` to reduce the number
-- of times a signal is evaluated. The trace will show
-- "Calc A" once, but "Calc B" twice.
ex6 :: (Time t, Floating t) => Sim t (Signal t (V4 t))
ex6 = do
    let
        a = share $ fmap (trace "Calc A") $ 5 + 2
        b = fmap (trace "Calc B") $ 5 + 2
    return $ V4 <$> a <*> a <*> b <*> b

