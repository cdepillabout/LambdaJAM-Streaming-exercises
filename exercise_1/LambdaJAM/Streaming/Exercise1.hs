{-# LANGUAGE BangPatterns, DeriveFoldable, DeriveTraversable, InstanceSigs, RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

{- |
   Module      : LambdaJAM.Streaming.Exercise1
   Description : Exercise 1
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : MIT
   Maintainer  : Ivan.Miljenovic@gmail.com

   This exercise focuses on how Stream differs from Pipe and Conduit.

 -}
module LambdaJAM.Streaming.Exercise1 where

import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Class
import qualified Data.Foldable             as F
import           Data.Monoid

-- For Task 3
import           Control.Monad     (join)
import           Data.Conduit      (ConduitM, await, runConduit, transPipe,
                                    (.|))
import qualified Data.Conduit.List as CL

--------------------------------------------------------------------------------

{-

This is an inlined variant of @Stream (Of a) m r@ with a subset of the
functionality made available.

-}

data IStream a m r = IStep (a, IStream a m r)
                   | IEffect (m (IStream a m r))
                   | IReturn r

instance (Monad m) => Functor (IStream a m) where
  fmap f = go
    where
      go stream = case stream of
                    IStep g   -> IStep (fmap go g)
                    IEffect m -> IEffect (m >>= return . go)
                    IReturn r -> IReturn (f r)

instance (Monad m) => Applicative (IStream a m) where
  pure = IReturn

  streamf <*> streamx = do
    f <- streamf
    x <- streamx
    return (f x)

instance (Monad m) => Monad (IStream a m) where
  stream >>= f = go stream
    where
      go str = case str of
                 IStep g   -> IStep (fmap go g)
                 IEffect m -> IEffect (fmap go m)
                 IReturn r -> f r

  fail = lift . fail

instance MonadTrans (IStream a) where
  lift = IEffect . fmap IReturn

instance (MonadIO m) => MonadIO (IStream a m) where
  liftIO = lift . liftIO

inlineFold :: (Monad m) => (x -> a -> x) -> x -> (x -> b) -> IStream a m r -> m (b, r)
inlineFold step begin done str = go str begin
  where
    go stream !x = case stream of
                     IReturn r       -> return (done x, r)
                     IEffect m       -> m >>= \str' -> go str' x
                     IStep (a, rest) -> go rest $! step x a

inlineToList :: (Monad m) => IStream a m r -> m ([a], r)
inlineToList = inlineFold (\diff a ls -> diff (a:ls)) id ($[])

listToInline :: (Monad m, F.Foldable f) => f a -> IStream a m ()
listToInline = F.foldr (\a p -> IStep (a, p)) (IReturn ())

iMapM_ :: (Monad m) => (a -> m b) -> IStream a m r -> m r
iMapM_ f = go
  where
    go stream = case stream of
                  IStep (a,str') -> f a >> go str'
                  IEffect m      -> m >>= go
                  IReturn r      -> return r

printIStream :: (Show a, MonadIO m) => IStream a m r -> m r
printIStream = iMapM_ (liftIO . print)

--------------------------------------------------------------------------------


{-

Task 1:

When dealing with lists, a common operation is to split the list at a specified index:

@

  splitAt :: Int -> [a] -> ([a], [a])

@

such that the length of the first returned list is equal (or less than
if the length of the input list is less than) the specified @Int@
parameter:

@

  splitAt 3  [1..10] = ([1,2,3],[4,5,6,7,8,9,10])

  splitAt 11 [1..10] = ([1,2,3,4,5,6,7,8,9,10],[])

@

Define such a function on 'IStream's.

Consider: what would be the appropriate return type? (Remember that
@IStream a m r@ is roughly analogous to @m ([a], r)@!).

Test it out!  'printIStream' should come in handy.

What are the consequences of the type you chose?

-}

splitAtStr :: Functor m => Int -> IStream a m r -> IStream a m (IStream a m r)
splitAtStr i str
  | i <= 0 = IReturn str
  | otherwise =
    case str of
      IReturn r -> IReturn (IReturn r)
      IEffect nextStr -> IEffect $ fmap (splitAtStr i) nextStr
      IStep (a, next) -> IStep (a, splitAtStr (i - 1) next)

--------------------------------------------------------------------------------

{-

Motivating discussion:

Rather than just taking /a/ list of @n@ elements from the front of the
list, we often want to split an entire list into sub-lists of size no
greater than @n@ (allowing for the last sub-list to be shorter).

How can we express this using 'IStream'?

One solution may be to have a function with a type like:

@
  chunksOf :: (Monad m) => Int -> IStream a m r -> IStream [a] m r
@

but this is clearly sub-optimal: we are no longer able to capture the
streaming nature of the original data, and must periodically wait to
collect enough values to construct a list.

One attempt to resolve this might be this slight variation:

@
  chunksOf :: (Monad m) => Int -> IStream a m r -> IStream (IStream a m r) m r
@

Except... where do we get value for the @r@ returned by each
sub-stream?  If we get the final value of @r@ then there's no point in
streaming; we can't create one as there's no @Monoid@ or similar
constraint on it.

First of all, let's realise that it doesn't /have/ to be of type @r@!
This type makes just as much sense:

@
  chunksOf :: (Monad m) => Int -> IStream a m r -> IStream (IStream a m v) m r
@

We still can't actually create these values... so let's denote that:

@
  -- Type alias for clarity
  type SubIStream = IStream

  chunksOf :: (Monad m) => Int -> IStream a m r -> IStream (forall v. SubIStream a m v) m r
@

Now, every time we have a new @SubIStream@, the actual value of the outer @IStream@ is:

@
  IStep (forall v. SubIStream a m v, IStream b m r)

  -- b ~ (forall v. SubIStream a m v)
@

In actual usage, that inner @IStream@ /really/ shouldn't be accessed
or used until we've evaluated that @SubIStream@.  So why not kill two
birds with one stone: ensure we can't access the rest of the @IStream@
by having it as the return value of the @SubIStream@!

@
  SubIStream a m (IStream b m r)

  = SubIStream a m (IStream (SubIStream a m (IStream b m r) m r)

  = SubIStream a m (IStream (SubIStream a m (IStream (SubIStream a m (IStream b m r) m r) m r) m r)
@

We obviously can't keep doing this indefinitely if we expect a usable type out of this.

Some of you may recognise this: it's reminiscent of the free monad transformer:

@
  -- The "free monad transformer" for a functor @f@
  newtype FreeT f m a = FreeT { runFreeT :: m (FreeF f a (FreeT f m a)) }

  -- The base functor for a free monad.
  data FreeF f a b = Pure a | Free (f b)
@

So we should be able to define a FreeT-inspired Stream datatype, and
to actually carry a payload, we can use the left-strict pair.

-}

data FStream f m r = FStep (f (FStream f m r))
                   | FEffect (m (FStream f m r))
                   | FReturn r
                   deriving Functor

instance (Monad m, Functor f) => Applicative (FStream f m) where
  pure = FReturn
  (<*>) = ap

instance (Functor f, Monad m) => Monad (FStream f m) where
  (>>=) :: FStream f m a -> (a -> FStream f m b) -> FStream f m b
  FReturn a >>= strf = strf a
  FEffect next >>= strf = FEffect (next >>= pure . (>>= strf))
  FStep next >>= strf = FStep $ fmap (>>= strf) next

-- | A left-strict pair; the base functor for streams of individual elements.
data Of a b = !a :> b
    deriving (Eq, Foldable, Ord,
              Read, Show, Traversable)

infixr 5 :>

instance Functor (Of a) where
  fmap f (a :> x) = a :> f x

fYield :: a -> FStream (Of a) m ()
fYield a = FStep (a :> FReturn ())

fCons :: a -> FStream (Of a) m r -> FStream (Of a) m r
fCons a str = FStep (a :> str)

{-

(Actually, the @Stream@ data type grew out of "attempt to implement
`FreeT` in the style of `Pipes.Internal`".)

We could then say:

@
  type IStream a = FStream (Of a)
@

-}

--------------------------------------------------------------------------------

{-

Task 2:

Port the various instances and functions (including your @splitAt@
function!) to 'FStream'.

After that, implement a @chunksOf@ function.

Think about the actual minimum type required for both @splitAt@ and
@chunksOf@.

Test it: can you take a list, convert it to a stream, chunk it, then
convert each sub-stream into a list and print it?  The following
function may be useful:

-}

-- Compared to @mapM@, this transforms the functor rather than any
-- values stored within that functor (though the transformation
-- function may modify the values).
mapsM :: (Monad m, Functor f) => (forall x. f x -> m (g x))
         -> FStream f m r -> FStream g m r
mapsM phi = go
  where
    go str = case str of
               FStep f   -> FEffect (fmap FStep (phi (fmap go f)))
               FEffect m -> FEffect (fmap go m)
               FReturn r -> FReturn r

-- A traditional @mapM@-style function implemented using 'mapsM'.
fMapM :: (Monad m) => (a -> m b) -> FStream (Of a) m r -> FStream (Of b) m r
fMapM f = mapsM (\(a :> x) -> (:> x) <$> f a)

fusedFold ::
     forall m x a b r.
     (Monad m)
  => (x -> a -> x)
  -> x
  -> (x -> b)
  -> FStream (Of a) m r
  -> m (Of b r)
fusedFold comb nil toB strm = go nil strm
  where
    go :: x -> FStream (Of a) m r -> m (Of b r)
    go x (FReturn r) = pure $ toB x :> r
    go x (FEffect nextM) = nextM >>= go x
    go x (FStep (a :> next)) = go (comb x a) next

iMapMF_ :: (Monad m) => (a -> m b) -> FStream (Of a) m r -> m r
iMapMF_ f = go
  where
    go stream = case stream of
                  FStep (a :> str') -> f a >> go str'
                  FEffect m      -> m >>= go
                  FReturn r      -> return r

printFStream :: (Show a, MonadIO m) => FStream (Of a) m r -> m r
printFStream = iMapMF_ (liftIO . print)

inlineFoldF ::
     forall m x a b r.
     (Monad m)
  => (x -> a -> x)
  -> x
  -> (x -> b)
  -> FStream (Of a) m r
  -> m (b, r)
inlineFoldF step begin done str = go str begin
  where
    go :: FStream (Of a) m r -> x -> m (b, r)
    go stream !x = case stream of
                     FReturn r       -> return (done x, r)
                     FEffect m       -> m >>= \str' -> go str' x
                     FStep (a :> rest) -> go rest $! step x a

inlineFoldF' ::
     forall m f x a b c r.
     (Monad m)
  => (x -> a -> x)
  -> x
  -> (x -> r -> c)
  -> (forall z. f a z -> a)
  -> (forall y. f y (FStream (f a) m r) -> FStream (f a) m r)
  -> FStream (f a) m r
  -> m c
inlineFoldF' step begin end getA getNext str = go str begin
  where
    go :: FStream (f a) m r -> x -> m c
    go stream !x = case stream of
                     FReturn r       -> return (end x r)
                     FEffect m       -> m >>= \str' -> go str' x
                     FStep next -> go (getNext next) $! step x (getA next)

inlineToListF :: (Monad m) => FStream (Of a) m r -> m ([a], r)
inlineToListF = inlineFoldF (\diff a ls -> diff (a:ls)) id ($[])

-- inlineToListF' :: (Monad m) => FStream (f a) m r -> m (f [a] r)
-- inlineToListF' = inlineFoldF (\diff a ls -> diff (a:ls)) id ($[])

listToInlineF :: (Monad m, F.Foldable f) => f a -> FStream (Of a) m ()
listToInlineF = F.foldr (\a p -> FStep (a :> p)) (FReturn ())

-- chunksOfF ::
--      forall m r a.
--      (Monad m)
--   => Int
--   -> FStream (Of a) m r
--   -> FStream (FStream (Of a) m) m r
-- chunksOfF num = go 0
--   where
--     go :: Int -> FStream (Of a) m r -> FStream (FStream (Of a) m) m r
--     go i (FReturn r) = FReturn r
--     go i (FEffect nextM) = FEffect $ fmap (go i) nextM
--     go i (FStep (a :> next))
--       | i < num = FStep (FStep (a :> foobar i next))
--       | otherwise = FStep (FReturn (go 0 (FStep (a :> next))))

--     foobar :: Int -> FStream (Of a) m r -> FStream (Of a) m (FStream (FStream (Of a) m) m r)
--     foobar i next =
--       let res = splitAtStrF i next
--       in fmap (go 0) res

chunksOfF ::
     forall m f r.
     (Monad m, Functor f)
  => Int
  -> FStream f m r
  -> FStream (FStream f m) m r
chunksOfF num = go
  where
    go :: FStream f m r -> FStream (FStream f m) m r
    go (FReturn r) = FReturn r
    go (FEffect nextM) = FEffect $ fmap go nextM
    go strm@(FStep next) =
      FStep (FStep (fmap (fmap go . splitAtStrF (num - 1)) next))

    recurseOnRemainder ::
         FStream f m (FStream f m r)
      -> FStream f m (FStream (FStream f m) m r)
    recurseOnRemainder = fmap go

-- chunksOf' :: (Monad m, Functor f) => Int -> FStream f m r -> FStream (FStream f m) m r
-- chunksOf' c = go
--   where
--     recurseOnRemainder = fmap go

--     go (FReturn r)  = FReturn r
--     go (FEffect m)  = FEffect (fmap go m)
--     go (FStep step) =
--       FStep (FStep (fmap (recurseOnRemainder . splitAtStrF (c - 1)) step))

splitAtStrF ::
     (Functor f, Functor m)
  => Int
  -> FStream f m r
  -> FStream f m (FStream f m r)
splitAtStrF i (FReturn r) = FReturn (FReturn r)
splitAtStrF i (FEffect nextM) = FEffect (fmap (splitAtStrF i) nextM)
splitAtStrF i (FStep next)
  | i <= 0 = FReturn (FStep next)
  | otherwise = FStep (fmap (splitAtStrF (i - 1)) next)

doStuff :: FStream (FStream (Of Int) IO) IO () -> IO ()
doStuff (FReturn ()) = do
  putStrLn "doStuff, got FReturn in outer, evaluating nextM..."
  pure ()
doStuff (FEffect nextM) = do
  putStrLn "doStuff, got FEffect in outter, evaluating nextM..."
  next <- nextM
  putStrLn "doStuff, got FEffect in outter, finished evaluating nextM, recursing into next"
  doStuff next
doStuff (FStep (FReturn aefase)) = do
  putStrLn "doStuff, got FStep in outer, FReturn in inner, recursing into next"
  doStuff aefase
doStuff (FStep (FEffect nextM)) = do
  putStrLn "doStuff, got FStep in outer, FEffect in inner, printing ints..."
  next <- nextM
  ga <- iMapMF_ (\i -> putStrLn $ "doStuff, FStep in outer, FEffect in inner, inner iMapMF_, printing i: " <> show i) next
  putStrLn "doStuff, got FStep in outer, FEffect in inner, finished printing ints, now recursing into next"
  doStuff ga
doStuff (FStep (FStep (i :> next))) = do
  putStrLn $ "doStuff, got FStep in outer, FStep in inner, printing i: " <> show i
  ga <- iMapMF_ (\i -> putStrLn $ "doStuff, FStep in outer, FStep in FStep, inner iMapMF_, printing i: " <> show i) next
  putStrLn $ "doStuff, got FStep in outer, FStep in inner, finished printing ints, now recursing into next"
  doStuff ga

ofFst :: Of a b -> a
ofFst (a :> _) = a

ofSnd :: Of a b -> b
ofSnd (_ :> b) = b

testtest :: forall a. FStream (FStream (Of a) IO) IO () -> IO [[a]]
testtest = fmap fst . inlineToListF . mapsM go
  where
    go :: forall x. FStream (Of a) IO x -> IO (Of [a] x)
    go = inlineFoldF' (\as a -> a : as) [] (\as r -> reverse as :> r) ofFst ofSnd

-- chunksOfF n strm =
--   splitAtStrF n strm
    -- go :: Int -> FStream (Of a) m r -> FStream (FStream (Of a)
    -- go i str
    --   | i < num = undefined
    --   | otherwise =
-- chunksOfF i (FReturn r) = FReturn r
-- chunksOfF i (FEffect nextM) = FEffect (fmap (chunksOfF i) nextM)
-- chunksOfF i (FStep (a :> next))
--   | i <= 0 = FReturn _

--------------------------------------------------------------------------------

{-

Motivating discussion:

(If you don't have experience with more "traditional" data streaming
libraries like /pipes/ or /conduit/, you may wish to skip this
section.  However, it will give you an idea of alternate ways of
approaching this problem.)

As you've hopefully seen (but will be explored in another exercise in
more depth), the @Stream@ type is (if you squint hard enough) kind of
like a traditional list interspersed with Monadic actions (which are
typically to obtain the next value).

Just about every other library that aims to solve the data streaming
problem in Haskell tends to do it using more of an automata/state
machine approach where they accept both inputs and outputs (and in the
case of pipes also allows for sending data back downstream!).  This
means some fundamental differences in how you approach and use these:

* In essence, a pipe or conduit is a /function/ that transforms inputs
  to outputs; with Streams we tend to denote this using an actual
  function.

* As such, pipes and conduits have their own set of functions and
  operators for composing them (@>->@ and @.|@ respectively for the
  simple cases).  With Streams, we use standard function composition.

* Furthermore, you typically have a need for some kind of @runPipe@ or
  @runConduit@ function to actually feed in inputs, etc.  Whereas with
  a Stream you'll use a function to create a Stream, then at the end
  use another (e.g. @mapM_@) to process one.

* At least in my experience, the downstream capabilities of pipes
  tends not to be very useful (typically setting @a'@ and @b'@ to
  @()@).

* In many ways, a Stream is more like a @Producer@ or @Source@ in
  pipes and conduit.

-}

--------------------------------------------------------------------------------

{-

Task 3:

Implement the following FStream <-> Conduit functions to get an idea
how they compare to each other.

These are all taken from streaming-conduit:
https://hackage.haskell.org/package/streaming-conduit (If you can
think of better definitions, please provide a pull request!)

Hint: see what I've imported for you to use.  You shouldn't need
anything else.

-}

-- | Convert a Stream to a Producer-style 'ConduitM'.
--
--   Hint: try using 'CL.unfoldEitherM'.
fromFStream :: (Monad m) => FStream (Of o) m r -> ConduitM i o m r
fromFStream = error "fromFStream"

-- toFStream is a little more involved, so will provide it for you.
-- Uncomment the definition when you've defined instances for FStream.

-- | Convert a Producer-style Conduit to a 'FStream'.
toFStream :: (Monad m) => ConduitM () o m () -> FStream (Of o) m ()
toFStream = error "toFStream"
-- toFStream cnd = runConduit (transPipe lift cnd .| CL.mapM_ fYield)

asStream :: (Monad m) => ConduitM i o m () -> FStream (Of i) m () -> FStream (Of o) m ()
asStream = error "asStream"

-- This one is very manual...
asConduit :: (Monad m) => (FStream (Of i) m () -> FStream (Of o) m r) -> ConduitM i o m r
asConduit = error "asConduit"
