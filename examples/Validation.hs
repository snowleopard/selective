{-# LANGUAGE ConstraintKinds, GADTs, RankNTypes #-}
module Validation where

import Control.Selective

-- See Section 2.2 of the paper: https://dl.acm.org/doi/10.1145/3341694.

type Radius = Word
type Width  = Word
type Height = Word

-- | A circle or rectangle.
data Shape = Circle Radius | Rectangle Width Height deriving (Eq, Show)

-- Some validation examples:
--
-- > shape (Success True) (Success 1) (Failure ["width?"]) (Failure ["height?"])
-- > Success (Circle 1)
--
-- > shape (Success False) (Failure ["radius?"]) (Success 2) (Success 3)
-- > Success (Rectangle 2 3)
--
-- > shape (Success False) (Failure ["radius?"]) (Success 2) (Failure ["height?"])
-- > Failure ["height?"]
--
-- > shape (Success False) (Success 1) (Failure ["width?"]) (Failure ["height?"])
-- > Failure ["width?", "height?"]
--
-- > shape (Failure ["choice?"]) (Failure ["radius?"]) (Success 2) (Failure ["height?"])
-- > Failure ["choice?"]
shape :: Selective f => f Bool -> f Radius -> f Width -> f Height -> f Shape
shape s r w h = ifS s (Circle <$> r) (Rectangle <$> w <*> h)

-- > s1 = shape (Failure ["choice 1?"]) (Success 1) (Failure ["width 1?"]) (Success 3)
-- > s2 = shape (Success False) (Success 1) (Success 2) (Failure ["height 2?"])
-- > twoShapes s1 s2
-- > Failure ["choice 1?","height 2?"]
twoShapes :: Selective f => f Shape -> f Shape -> f (Shape, Shape)
twoShapes s1 s2 = (,) <$> s1 <*> s2
