{-# LANGUAGE TypeApplications #-}

import Control.Arrow (ArrowMonad)
import Control.Monad.Trans.Writer hiding (writer)
import Control.Selective
import Data.Functor.Identity
import Data.Maybe hiding (maybe)
import Prelude hiding (maybe)
import Test.Tasty
import Test.Tasty.ExpectedFailure
import Test.Tasty.QuickCheck hiding (Success, Failure)

import Build
import Laws
import Validation

import qualified Control.Selective.Free       as F
import qualified Control.Selective.Rigid.Free as FR
import qualified Teletype                     as F
import qualified Teletype.Rigid               as FR

main :: IO ()
main = defaultMain $ testGroup "Tests"
    [pingPong, build, over, under, validation, arrowMonad, maybe, identity, writer]

--------------------------------------------------------------------------------
------------------------ Ping-pong----------------------------------------------
--------------------------------------------------------------------------------
pingPong :: TestTree
pingPong = testGroup "pingPong"
    [ testProperty "Free.getEffects pingPongS == [Read,Write \"pong\"]" $
        F.getEffects F.pingPongS == [F.Read (const ()),F.Write "pong" ()]
    , testProperty "Free.getNecessaryEffects pingPongS == [Read]" $
        F.getNecessaryEffects F.pingPongS == [F.Read (const ())]
    , testProperty "Free.Rigid.getEffects pingPongS == [Read,Write \"pong\"]" $
        FR.getEffects FR.pingPongS == [FR.Read (const ()),FR.Write "pong" ()] ]

--------------------------------------------------------------------------------
------------------------ Build -------------------------------------------------
--------------------------------------------------------------------------------
build :: TestTree
build = testGroup "Build" [cyclicDeps, taskBindDeps, runBuildDeps]

cyclicDeps :: TestTree
cyclicDeps = testGroup "cyclicDeps"
    [ testProperty "dependenciesOver (fromJust $ cyclic \"B1\") == [\"C1\",\"B2\",\"A2\"]" $
        dependenciesOver (fromJust $ cyclic "B1") == ["C1","B2","A2"]
    , testProperty "dependenciesOver cyclic \"B2\") == [\"C1\",\"A1\",\"B1\"]" $
        dependenciesOver (fromJust $ cyclic "B2") == ["C1","A1","B1"]
    , testProperty "dependenciesUnder (fromJust $ cyclic \"B1\") == [\"C1\"]" $
        dependenciesUnder (fromJust $ cyclic "B1") == ["C1"]
    , testProperty "dependenciesUnder cyclic \"B2\") == [\"C1\"]" $
        dependenciesUnder (fromJust $ cyclic "B2") == ["C1"] ]

taskBindDeps :: TestTree
taskBindDeps = testGroup "taskBindDeps"
    [ testProperty "dependenciesOver taskBind == [\"A1\",\"A2\",\"C5\",\"C6\",\"A2\",\"D5\",\"D6\"]" $
        dependenciesOver taskBind == ["A1","A2","C5","C6","A2","D5","D6"]
    , testProperty "dependenciesUnder taskBind == [\"A1\"]" $
        dependenciesUnder taskBind == ["A1"] ]

runBuildDeps :: TestTree
runBuildDeps = testGroup "runBuildDeps"
    [ testProperty "runBuild (fromJust $ cyclic \"B1\") == [Fetch \"C1\",Fetch \"B2\",Fetch \"A2\"]" $
        runBuild (fromJust $ cyclic "B1") == [Fetch "C1" (const ()),Fetch "B2" (const ()),Fetch "A2" (const ())] ]

--------------------------------------------------------------------------------
------------------------ Over --------------------------------------------------
--------------------------------------------------------------------------------
over :: TestTree
over = testGroup "Over" [overLaws, overTheorems, overProperties]

overLaws :: TestTree
overLaws = testGroup "Laws"
    [ testProperty "Identity: (x <*? pure id) == (either id id <$> x)" $
        \x -> lawIdentity @(Over String) x
    , testProperty "Distributivity: (pure x <*? (y *> z)) == ((pure x <*? y) *> (pure x <*? z))" $
        \x -> lawDistributivity @(Over String) @Int @Int x
    , testProperty "Associativity: take a look at tests/Laws.hs" $
        \x -> lawAssociativity @(Over String) @Int @Int x ]

overTheorems :: TestTree
overTheorems = testGroup "Theorems"
    [ testProperty "Apply a pure function to the result: (f <$> select x y) == (select (second f <$> x) ((f .) <$> y))" $
        \x -> theorem1 @(Over String) @Int @Int x
    , testProperty "Apply a pure function to the Left case of the first argument: (select (first f <$> x) y) == (select x ((. f) <$> y))" $
        \x -> theorem2 @(Over String) @Int @Int @Int x
    , testProperty "Apply a pure function to the second argument: (select x (f <$> y)) == (select (first (flip f) <$> x) ((&) <$> y))" $
        \x -> theorem3 @(Over String) @Int @Int @Int x
    , testProperty "Generalised identity: (x <*? pure y) == (either y id <$> x)" $
        \x -> theorem4 @(Over String) @Int @Int x
    , testProperty "(f <*> g) == (f `apS` g)" $
        \x -> theorem5 @(Over String) @Int @Int x
    , testProperty "Interchange: (x *> (y <*? z)) == ((x *> y) <*? z)" $
        \x -> theorem6 @(Over String) @Int @Int x ]

overProperties :: TestTree
overProperties = testGroup "Properties"
    [ expectFail $ testProperty "pure-right: pure (Right x) <*? y = pure x" $
        \x -> propertyPureRight @(Over String) @Int @Int x
    , testProperty "pure-left: pure (Left x) <*? y = ($x) <$> y" $
        \x -> propertyPureLeft @(Over String) @Int @Int x ]

--------------------------------------------------------------------------------
------------------------ Under -------------------------------------------------
--------------------------------------------------------------------------------
under :: TestTree
under = testGroup "Under" [underLaws, underTheorems, underProperties]

underLaws :: TestTree
underLaws = testGroup "Laws"
    [ testProperty "Identity: (x <*? pure id) == (either id id <$> x)" $
        \x -> lawIdentity @(Under String) x
    , testProperty "Distributivity: (pure x <*? (y *> z)) == ((pure x <*? y) *> (pure x <*? z))" $
        \x -> lawDistributivity @(Under String) @Int @Int x
    , testProperty "Associativity: take a look at tests/Laws.hs" $
        \x -> lawAssociativity @(Under String) @Int @Int x ]

underTheorems :: TestTree
underTheorems = testGroup "Theorems"
    [ testProperty "Apply a pure function to the result: (f <$> select x y) == (select (second f <$> x) ((f .) <$> y))" $
        \x -> theorem1 @(Under String) @Int @Int x
    , testProperty "Apply a pure function to the Left case of the first argument: (select (first f <$> x) y) == (select x ((. f) <$> y))" $
        \x -> theorem2 @(Under String) @Int @Int @Int x
    , testProperty "Apply a pure function to the second argument: (select x (f <$> y)) == (select (first (flip f) <$> x) ((&) <$> y))" $
        \x -> theorem3 @(Under String) @Int @Int @Int x
    , testProperty "Generalised identity: (x <*? pure y) == (either y id <$> x)" $
        \x -> theorem4 @(Under String) @Int @Int x
    -- 'Under' is a non-rigid selective functor
    , expectFail $ testProperty "(f <*> g) == (f `apS` g)" $
        \x -> theorem5 @(Under String) @Int @Int x
    , testProperty "Interchange: (x *> (y <*? z)) == ((x *> y) <*? z)" $
        \x -> theorem6 @(Under String) @Int @Int x ]

underProperties :: TestTree
underProperties = testGroup "Properties"
    [ testProperty "pure-right: pure (Right x) <*? y = pure x" $
        \x -> propertyPureRight @(Under String) @Int @Int x
    , expectFail $ testProperty "pure-left: pure (Left x) <*? y = ($x) <$> y" $
        \x -> propertyPureLeft @(Under String) @Int @Int x ]

--------------------------------------------------------------------------------
------------------------ Validation --------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
validation :: TestTree
validation = testGroup "Validation"
    [validationLaws, validationTheorems, validationProperties, validationExample]

validationLaws :: TestTree
validationLaws = testGroup "Laws"
    [ testProperty "Identity: (x <*? pure id) == (either id id <$> x)" $
        \x -> lawIdentity @(Validation String) @Int x
    , testProperty "Distributivity: (pure x <*? (y *> z)) == ((pure x <*? y) *> (pure x <*? z))" $
        \x -> lawDistributivity @(Validation String) @Int @Int x
    , testProperty "Associativity: take a look at tests/Laws.hs" $
        \x -> lawAssociativity @(Validation String) @Int @Int @Int x ]

validationTheorems :: TestTree
validationTheorems = testGroup "Theorems"
    [ testProperty "Apply a pure function to the result: (f <$> select x y) == (select (second f <$> x) ((f .) <$> y))" $
        \x -> theorem1 @(Validation String) @Int @Int @Int x
    , testProperty "Apply a pure function to the Left case of the first argument: (select (first f <$> x) y) == (select x ((. f) <$> y))" $
        \x -> theorem2 @(Validation String) @Int @Int @Int x
    , testProperty "Apply a pure function to the second argument: (select x (f <$> y)) == (select (first (flip f) <$> x) ((&) <$> y))" $
        \x -> theorem3 @(Validation String) @Int @Int @Int x
    , testProperty "Generalised identity: (x <*? pure y) == (either y id <$> x)" $
        \x -> theorem4 @(Validation String) @Int @Int x
    -- 'Validation' is a non-rigid selective functor
    , expectFail $ testProperty "(f <*> g) == (f `apS` g)" $
        \x -> theorem5 @(Validation String) @Int @Int x
    -- 'Validation' is a non-rigid selective functor
    , expectFail $ testProperty "Interchange: (x *> (y <*? z)) == ((x *> y) <*? z)" $
        \x -> theorem6 @(Validation String) @Int @Int @Int x ]

validationProperties :: TestTree
validationProperties = testGroup "Properties"
    [ testProperty "pure-right: pure (Right x) <*? y = pure x" $
        \x -> propertyPureRight @(Validation String) @Int @Int x
    , testProperty "pure-left: pure (Left x) <*? y = ($x) <$> y" $
        \x -> propertyPureLeft @(Validation String) @Int @Int x ]

validationExample :: TestTree
validationExample = testGroup "validationExample"
    [ testProperty "shape (Success True) (Success 1) (Failure [\"width?\"]) (Failure [\"height?\"])" $
        shape (Success True) (Success 1) (Failure ["width?"]) (Failure ["height?"]) == Success (Circle 1)
    , testProperty "shape (Success False) (Failure [\"radius?\"]) (Success 2) (Success 3)" $
        shape (Success False) (Failure ["radius?"]) (Success 2) (Success 3) == Success (Rectangle 2 3)
    , testProperty "shape (Success False) (Failure [\"radius?\"]) (Success 2) (Failure [\"height?\"])" $
        shape (Success False) (Failure ["radius?"]) (Success 2) (Failure ["height?"]) == Failure ["height?"]
    , testProperty "shape (Success False) (Success 1) (Failure [\"width?\"]) (Failure [\"height?\"])" $
        shape (Success False) (Success 1) (Failure ["width?"]) (Failure ["height?"]) == Failure ["width?", "height?"]
    , testProperty "shape (Failure [\"choice?\"]) (Failure [\"radius?\"]) (Success 2) (Failure [\"height?\"])" $
        shape (Failure ["choice?"]) (Failure ["radius?"]) (Success 2) (Failure ["height?"]) == Failure ["choice?"]
    , testProperty "twoShapes s1 s2" $
        twoShapes (shape (Failure ["choice 1?"]) (Success 1) (Failure ["width 1?"]) (Success 3)) (shape (Success False) (Success 1) (Success 2) (Failure ["height 2?"])) == Failure ["choice 1?","height 2?"] ]

--------------------------------------------------------------------------------
------------------------ ArrowMonad --------------------------------------------
--------------------------------------------------------------------------------
arrowMonad :: TestTree
arrowMonad = testGroup "ArrowMonad (->)"
    [arrowMonadLaws, arrowMonadTheorems, arrowMonadProperties]

arrowMonadLaws :: TestTree
arrowMonadLaws = testGroup "Laws"
    [ testProperty "Identity: (x <*? pure id) == (either id id <$> x)" $
        \x -> lawIdentity @(ArrowMonad (->)) @Int x
    , testProperty "Distributivity: (pure x <*? (y *> z)) == ((pure x <*? y) *> (pure x <*? z))" $
        \x -> lawDistributivity @(ArrowMonad (->)) @Int @Int x
    , testProperty "Associativity: take a look at tests/Laws.hs" $
        \x -> lawAssociativity @(ArrowMonad (->)) @Int @Int @Int x
    , testProperty "select == selectM" $
        \x -> lawMonad @(ArrowMonad (->)) @Int @Int x
    , testProperty "select == selectA" $
        \x -> selectALaw @(ArrowMonad (->)) @Int @Int x ]

arrowMonadTheorems :: TestTree
arrowMonadTheorems = testGroup "Theorems"
    [ testProperty "Apply a pure function to the result: (f <$> select x y) == (select (second f <$> x) ((f .) <$> y))" $
        \x -> theorem1 @(ArrowMonad (->)) @Int @Int @Int x
    , testProperty "Apply a pure function to the Left case of the first argument: (select (first f <$> x) y) == (select x ((. f) <$> y))" $
        \x -> theorem2 @(ArrowMonad (->)) @Int @Int @Int x
    , testProperty "Apply a pure function to the second argument: (select x (f <$> y)) == (select (first (flip f) <$> x) ((&) <$> y))" $
        \x -> theorem3 @(ArrowMonad (->)) @Int @Int @Int x
    , testProperty "Generalised identity: (x <*? pure y) == (either y id <$> x)" $
        \x -> theorem4 @(ArrowMonad (->)) @Int @Int x
    , testProperty "(f <*> g) == (f `apS` g)" $
        \x -> theorem5 @(ArrowMonad (->)) @Int @Int x
    , testProperty "Interchange: (x *> (y <*? z)) == ((x *> y) <*? z)" $
        \x -> theorem6 @(ArrowMonad (->)) @Int @Int @Int x ]

arrowMonadProperties :: TestTree
arrowMonadProperties = testGroup "Properties"
    [ testProperty "pure-right: pure (Right x) <*? y = pure x" $
        \x -> propertyPureRight @(ArrowMonad (->)) @Int @Int x
    , testProperty "pure-left: pure (Left x) <*? y = ($x) <$> y" $
        \x -> propertyPureLeft @(ArrowMonad (->)) @Int @Int x ]

--------------------------------------------------------------------------------
------------------------ Maybe -------------------------------------------------
--------------------------------------------------------------------------------
maybe :: TestTree
maybe = testGroup "Maybe" [maybeLaws, maybeTheorems, maybeProperties]

maybeLaws :: TestTree
maybeLaws = testGroup "Laws"
    [ testProperty "Identity: (x <*? pure id) == (either id id <$> x)" $
        \x -> lawIdentity @Maybe @Int x
    , testProperty "Distributivity: (pure x <*? (y *> z)) == ((pure x <*? y) *> (pure x <*? z))" $
        \x -> lawDistributivity @Maybe @Int @Int x
    , testProperty "Associativity: take a look at tests/Laws.hs" $
        \x -> lawAssociativity @Maybe @Int @Int @Int x
    , testProperty "select == selectM" $
        \x -> lawMonad @Maybe @Int @Int x ]

maybeTheorems :: TestTree
maybeTheorems = testGroup "Theorems"
    [ testProperty "Apply a pure function to the result: (f <$> select x y) == (select (second f <$> x) ((f .) <$> y))" $
        \x -> theorem1 @Maybe @Int @Int @Int x
    , testProperty "Apply a pure function to the Left case of the first argument: (select (first f <$> x) y) == (select x ((. f) <$> y))" $
        \x -> theorem2 @Maybe @Int @Int @Int x
    , testProperty "Apply a pure function to the second argument: (select x (f <$> y)) == (select (first (flip f) <$> x) ((&) <$> y))" $
        \x -> theorem3 @Maybe @Int @Int @Int x
    , testProperty "Generalised identity: (x <*? pure y) == (either y id <$> x)" $
        \x -> theorem4 @Maybe @Int @Int x
    , testProperty "(f <*> g) == (f `apS` g)" $
        \x -> theorem5 @Maybe @Int @Int x
    , testProperty "Interchange: (x *> (y <*? z)) == ((x *> y) <*? z)" $
        \x -> theorem6 @Maybe @Int @Int @Int x ]

maybeProperties :: TestTree
maybeProperties = testGroup "Properties"
    [ testProperty "pure-right: pure (Right x) <*? y = pure x" $
        \x -> propertyPureRight @Maybe @Int @Int x
    , testProperty "pure-left: pure (Left x) <*? y = ($x) <$> y" $
        \x -> propertyPureLeft @Maybe @Int @Int x ]

--------------------------------------------------------------------------------
------------------------ Identity ----------------------------------------------
--------------------------------------------------------------------------------
identity :: TestTree
identity = testGroup "Identity" [identityLaws, identityTheorems, identityProperties]

identityLaws :: TestTree
identityLaws = testGroup "Laws"
    [ testProperty "Identity: (x <*? pure id) == (either id id <$> x)" $
        \x -> lawIdentity @Identity @Int x
    , testProperty "Distributivity: (pure x <*? (y *> z)) == ((pure x <*? y) *> (pure x <*? z))" $
        \x -> lawDistributivity @Identity @Int @Int x
    , testProperty "Associativity: take a look at tests/Laws.hs" $
        \x -> lawAssociativity @Identity @Int @Int @Int x
    , testProperty "select == selectM" $
        \x -> lawMonad @Identity @Int @Int x ]

identityTheorems :: TestTree
identityTheorems = testGroup "Theorems"
    [ testProperty "Apply a pure function to the result: (f <$> select x y) == (select (second f <$> x) ((f .) <$> y))" $
        \x -> theorem1 @Identity @Int @Int @Int x
    , testProperty "Apply a pure function to the Left case of the first argument: (select (first f <$> x) y) == (select x ((. f) <$> y))" $
        \x -> theorem2 @Identity @Int @Int @Int x
    , testProperty "Apply a pure function to the second argument: (select x (f <$> y)) == (select (first (flip f) <$> x) ((&) <$> y))" $
        \x -> theorem3 @Identity @Int @Int @Int x
    , testProperty "Generalised identity: (x <*? pure y) == (either y id <$> x)" $
        \x -> theorem4 @Identity @Int @Int x
    , testProperty "(f <*> g) == (f `apS` g)" $
        \x -> theorem5 @Identity @Int @Int x
    , testProperty "Interchange: (x *> (y <*? z)) == ((x *> y) <*? z)" $
        \x -> theorem6 @Identity @Int @Int @Int x ]

identityProperties :: TestTree
identityProperties = testGroup "Properties"
    [ testProperty "pure-right: pure (Right x) <*? y = pure x" $
        \x -> propertyPureRight @Identity @Int @Int x
    , testProperty "pure-left: pure (Left x) <*? y = ($x) <$> y" $
        \x -> propertyPureLeft @Identity @Int @Int x ]

--------------------------------------------------------------------------------
------------------------ Writer ------------------------------------------------
--------------------------------------------------------------------------------

writer :: TestTree
writer = testGroup "Writer" [writerLaws, writerTheorems, writerProperties]

type MyWriter = Writer [Int]

writerLaws :: TestTree
writerLaws = testGroup "Laws"
    [ testProperty "Identity: (x <*? pure id) == (either id id <$> x)" $
        \x -> lawIdentity @MyWriter @Int x
    , testProperty "Distributivity: (pure x <*? (y *> z)) == ((pure x <*? y) *> (pure x <*? z))" $
        \x -> lawDistributivity @MyWriter @Int @Int x
    , testProperty "Associativity: take a look at tests/Laws.hs" $
        \x -> lawAssociativity @MyWriter @Int @Int @Int x
    , testProperty "select == selectM" $
        \x -> lawMonad @MyWriter @Int @Int x ]

writerTheorems :: TestTree
writerTheorems = testGroup "Theorems"
    [ testProperty "Apply a pure function to the result: (f <$> select x y) == (select (second f <$> x) ((f .) <$> y))" $
        \x -> theorem1 @MyWriter @Int @Int @Int x
    , testProperty "Apply a pure function to the Left case of the first argument: (select (first f <$> x) y) == (select x ((. f) <$> y))" $
        \x -> theorem2 @MyWriter @Int @Int @Int x
    , testProperty "Apply a pure function to the second argument: (select x (f <$> y)) == (select (first (flip f) <$> x) ((&) <$> y))" $
        \x -> theorem3 @MyWriter @Int @Int @Int x
    , testProperty "Generalised Identity: (x <*? pure y) == (either y id <$> x)" $
        \x -> theorem4 @MyWriter @Int @Int x
    , testProperty "(f <*> g) == (f `apS` g)" $
        \x -> theorem5 @MyWriter @Int @Int x
    , testProperty "Interchange: (x *> (y <*? z)) == ((x *> y) <*? z)" $
        \x -> theorem6 @MyWriter @Int @Int @Int x ]

writerProperties :: TestTree
writerProperties = testGroup "Properties"
    [ testProperty "pure-right: pure (Right x) <*? y = pure x" $
        \x -> propertyPureRight @MyWriter @Int @Int x
    , testProperty "pure-left: pure (Left x) <*? y = ($x) <$> y" $
        \x -> propertyPureLeft @MyWriter @Int @Int x ]
