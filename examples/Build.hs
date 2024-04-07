{-# LANGUAGE ConstraintKinds, DeriveFunctor, FlexibleInstances, GADTs, RankNTypes #-}
module Build where

import Control.Selective
import Control.Selective.Rigid.Free

-- See Section 3 of the paper: https://dl.acm.org/doi/10.1145/3341694.

-- | Selective build tasks.
-- See "Build Systems à la Carte": https://dl.acm.org/citation.cfm?id=3236774.
newtype Task k v = Task { run :: forall f. Selective f => (k -> f v) -> f v }

-- | Selective build scripts.
type Script k v = k -> Maybe (Task k v)

-- | Build dependencies with over-approximation.
dependenciesOver :: Task k v -> [k]
dependenciesOver task = getOver $ run task (\k -> Over [k])

-- | Build dependencies with under-approximation.
dependenciesUnder :: Task k v -> [k]
dependenciesUnder task = getUnder $ run task (\k -> Under [k])

-- | A build script with a static dependency cycle, which always resolves into
-- an acyclic dependency graph in runtime.
--
-- @
-- 'dependenciesOver'  ('fromJust' $ 'cyclic' "B1") == ["C1","B2","A2"]
-- 'dependenciesOver'  ('fromJust' $ 'cyclic' "B2") == ["C1","A1","B1"]
-- 'dependenciesUnder' ('fromJust' $ 'cyclic' "B1") == ["C1"]
-- 'dependenciesUnder' ('fromJust' $ 'cyclic' "B2") == ["C1"]
-- @
cyclic :: Script String Integer
cyclic "B1" = Just $ Task $ \fetch -> ifS ((1==) <$> fetch "C1") (fetch "B2") (fetch "A2")
cyclic "B2" = Just $ Task $ \fetch -> ifS ((1==) <$> fetch "C1") (fetch "A1") (fetch "B1")
cyclic _    = Nothing

-- | A build task demonstrating the use of 'bindS'.
--
-- @
-- 'dependenciesOver'  'taskBind' == ["A1","A2","C5","C6","D5","D6"]
-- 'dependenciesUnder' 'taskBind' == ["A1"]
-- @
taskBind :: Task String Integer
taskBind = Task $ \fetch -> (odd <$> fetch "A1") `bindS` \x ->
                            (odd <$> fetch "A2") `bindS` \y ->
                                let c = if x then "C" else "D"
                                    n = if y then "5" else "6"
                                in fetch (c ++ n)

data Key = A Int | B Int | C Int Int deriving (Eq, Show)

editDistance :: Script Key Int
editDistance (C i 0) = Just $ Task $ const $ pure i
editDistance (C 0 j) = Just $ Task $ const $ pure j
editDistance (C i j) = Just $ Task $ \fetch ->
    ((==) <$> fetch (A i) <*> fetch (B j)) `bindS` \equals ->
        if equals
            then fetch (C (i - 1) (j - 1))
            else (\insert delete replace -> 1 + minimum [insert, delete, replace])
                 <$> fetch (C  i      (j - 1))
                 <*> fetch (C (i - 1)  j     )
                 <*> fetch (C (i - 1) (j - 1))
editDistance _ = Nothing

-- | Example from the paper: a mock for the @tar@ archiving utility.
tar :: Applicative f => [f String] -> f String
tar xs = concat <$> sequenceA xs

-- | Example from the paper: a mock for the configuration parser.
parse :: Functor f => f String -> f Bool
parse = fmap null

-- | Example from the paper: a mock for the OCaml compiler parser.
compile :: Applicative f => [f String] -> f String
compile xs = concat <$> sequenceA xs

-- | Example from the paper.
script :: Script FilePath String
script "release.tar" = Just $ Task $ \fetch -> tar [fetch "LICENSE", fetch "exe"]
script "exe" = Just $ Task $ \fetch ->
    let src   = fetch "src.ml"
        cfg   = fetch "config"
        libc  = fetch "lib.c"
        libml = fetch "lib.ml"
    in compile [src, ifS (parse cfg) libc libml]
script _ = Nothing

--------------------------------- Free example ---------------------------------

-- | Base functor for a free build system.
data Fetch k v a = Fetch k (v -> a) deriving Functor

instance Eq k => Eq (Fetch k v ()) where
    Fetch x _ == Fetch y _ = x == y

instance Show k => Show (Fetch k v a) where
    show (Fetch k _) = "Fetch " ++ show k

-- | A convenient alias.
fetch :: k -> Select (Fetch k v) v
fetch key = liftSelect $ Fetch key id

-- | Analyse a build task via free selective functors.
--
-- @
-- runBuild (fromJust $ cyclic "B1") == [ Fetch "C1" (const ())
--                                      , Fetch "B2" (const ())
--                                      , Fetch "A2" (const ()) ]
-- @
runBuild :: Task k v -> [Fetch k v ()]
runBuild task = getEffects (run task fetch)
