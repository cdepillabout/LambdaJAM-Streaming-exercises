{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE InstanceSigs #-}
{- |
   Module      : LambdaJAM.Streaming.Exercise0
   Description : Exercise 0
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : MIT
   Maintainer  : Ivan.Miljenovic@gmail.com

   In this exercise, you will build up a simplistic version of the
   Stream data type and functions for it.

 -}
module LambdaJAM.Streaming.Exercise0 where

import Control.Monad

--------------------------------------------------------------------------------

{-

As it currently stands, the 'Stream' data type here is isomorphic to
@([a],r)@.

  * @a@ is the elements of the 'Stream'

  * @r@ is the final result from running the 'Stream'.

-}
data Stream a m r = Step a (m (Stream a m r))
                  | Return r
  deriving (Functor)

instance Functor m => Applicative (Stream a m) where
  pure = Return
  (<*>) = ap

instance Functor m => Monad (Stream x m) where
  (>>=) :: Stream x m a -> (a -> Stream x m b) -> Stream x m b
  Return r >>= strf = strf r
  Step a next >>= strf = Step a $ fmap (>>= strf) next

--------------------------------------------------------------------------------

{-

Task 1:

Implement 'streamToList' and 'listToStream'.  These will serve as our
initial methods of creating/running 'Stream's.

-}

-- streamToList :: Stream a m r -> m ([a], r)
-- streamToList (Step a str) = let (as, r) = streamToList str in (a : as, r)
-- streamToList (Return r) = ([], r)
-- streamToList = foldStream (\a (as, r) -> (a:as, r)) (\r -> ([], r))

streamToList :: Monad m => Stream a m r -> m ([a], r)
streamToList (Return r) = pure ([], r)
streamToList (Step a next) = do
  str <- next
  (as, r) <- streamToList str
  pure (a : as, r)

-- foldStream :: (a -> b -> b) -> (r -> b) -> Stream a m r -> m b
-- foldStream comb b (Return r) = b r
-- foldStream comb b (Step a str) = comb a (foldStream comb b str)

-- listToStream :: [a] -> Stream a m ()
-- listToStream [] = Return ()
-- listToStream (a:as) = Step a (listToStream as)
-- listToStream = foldr Step (Return ())
-- listToStream = foldr Step (Return ())

listToStream :: Applicative m => [a] -> Stream a m ()
listToStream [] = Return ()
listToStream (a:as) = Step a (pure $ listToStream as)

--------------------------------------------------------------------------------

{-

Task 2:

As this current 'Stream' implementation is isomorphic to a list, it
doesn't actually serve any purpose.  The true power of the 'Stream'
type comes about when we allow a /monadic effect/.

Augment the 'Stream' datatype to add in the ability to have a monadic
action returning another 'Stream'.

The canonical type parameters for this are @Stream a m r@.

Make sure to update 'streamToList' and 'listToStream'!

Ideally you would also be able to define 'Applicative' and 'Monad'
instances for 'Stream'.

-}

--------------------------------------------------------------------------------

{-

Task 3:

We typically do not want to pattern match every time we interact with
a 'Stream'; instead, it would be convenient to have what we expect
from many of our functional data structures: a folding function:

> foldStream :: (Monad m) => (x -> a -> x) -> x -> (x -> b) -> Stream a m r -> m (b, r)

(The @(x -> b)@ parameter will often be the 'id' function; i.e. @x ~ b@.)

You may wish to re-implement 'streamToList' to use this function (and
possibly make 'listToStream' take a 'Foldable').

Try using this function to implement Stream analogues of functions
like 'length'.

-}

foldStream :: Monad m => (a -> b -> b) -> (r -> b) -> Stream a m r -> m b
foldStream fol nul (Return r) = pure  $ nul r
foldStream fol nul (Step a next) = next >>= foldStream fol nul >>= pure . fol a

--------------------------------------------------------------------------------

{-

Task 4:

We typically want to transform our streamed values.  Try defining
Stream analogues of 'map', 'mapM' and 'mapM_' (you may wish to define
a monadic fold function as well).

Use these to do the equivalent of:

> mapM_ print . map (*2) $ [1..10]

-}

mapMStr_ :: Monad f => (a -> f ()) -> Stream a f r -> f ()
mapMStr_ f (Return r) = pure ()
mapMStr_ f (Step a next) = f a *> next >>= mapMStr_ f
