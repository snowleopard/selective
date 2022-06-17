{-# LANGUAGE TypeApplications #-}

import Control.Arrow (ArrowMonad)
import Control.Monad.Trans.Writer hiding (writer)
import Control.Selective.Trans.Except hiding (except)
import Control.Selective
import Data.Functor.Identity
import Data.Maybe hiding (maybe)
import Prelude hiding (maybe)

import Build
import Laws
import Validation

import Test

import qualified Control.Selective.Free       as F
import qualified Control.Selective.Rigid.Free as FR
import qualified Teletype                     as F
import qualified Teletype.Rigid               as FR

main :: IO ()
main = runTests $ testGroup "Tests"
    [ pingPong
    , build
    , over
    , under
    , validation
    , arrowMonad
    , maybe
    , identity
    , writer
    , except
    ]

--------------------------------------------------------------------------------
------------------------ Ping-pong----------------------------------------------
--------------------------------------------------------------------------------
pingPong :: Tests
pingPong = testGroup "pingPong"
    [ expectSuccess "Free.getEffects pingPongS == [Read,Write \"pong\"]" $
        F.getEffects F.pingPongS == [F.Read (const ()),F.Write "pong" ()]
    , expectSuccess "Free.getNecessaryEffects pingPongS == [Read]" $
        F.getNecessaryEffects F.pingPongS == [F.Read (const ())]
    , expectSuccess "Free.Rigid.getEffects pingPongS == [Read,Write \"pong\"]" $
        FR.getEffects FR.pingPongS == [FR.Read (const ()),FR.Write "pong" ()] ]

--------------------------------------------------------------------------------
------------------------ Build -------------------------------------------------
--------------------------------------------------------------------------------
build :: Tests
build = testGroup "Build"
    [ cyclicDeps
    , taskBindDeps
    , runBuildDeps ]

cyclicDeps :: Tests
cyclicDeps = testGroup "cyclicDeps"
    [ expectSuccess "dependenciesOver (fromJust $ cyclic \"B1\") == [\"C1\",\"B2\",\"A2\"]" $
        dependenciesOver (fromJust $ cyclic "B1") == ["C1","B2","A2"]
    , expectSuccess "dependenciesOver cyclic \"B2\") == [\"C1\",\"A1\",\"B1\"]" $
        dependenciesOver (fromJust $ cyclic "B2") == ["C1","A1","B1"]
    , expectSuccess "dependenciesUnder (fromJust $ cyclic \"B1\") == [\"C1\"]" $
        dependenciesUnder (fromJust $ cyclic "B1") == ["C1"]
    , expectSuccess "dependenciesUnder cyclic \"B2\") == [\"C1\"]" $
        dependenciesUnder (fromJust $ cyclic "B2") == ["C1"] ]

taskBindDeps :: Tests
taskBindDeps = testGroup "taskBindDeps"
    [ expectSuccess "dependenciesOver taskBind == [\"A1\",\"A2\",\"C5\",\"C6\",\"A2\",\"D5\",\"D6\"]" $
        dependenciesOver taskBind == ["A1","A2","C5","C6","A2","D5","D6"]
    , expectSuccess "dependenciesUnder taskBind == [\"A1\"]" $
        dependenciesUnder taskBind == ["A1"] ]

runBuildDeps :: Tests
runBuildDeps = testGroup "runBuildDeps"
    [ expectSuccess "runBuild (fromJust $ cyclic \"B1\") == [Fetch \"C1\",Fetch \"B2\",Fetch \"A2\"]" $
        runBuild (fromJust $ cyclic "B1") == [Fetch "C1" (const ()),Fetch "B2" (const ()),Fetch "A2" (const ())] ]

--------------------------------------------------------------------------------
------------------------ Over --------------------------------------------------
--------------------------------------------------------------------------------
over :: Tests
over = testGroup "Over"
    [ overLaws
    , overTheorems
    , overProperties ]

overLaws :: Tests
overLaws = testGroup "Laws"
    [ expectSuccess "Identity: (x <*? pure id) == (either id id <$> x)" $
        \x -> lawIdentity @(Over String) x
    , expectSuccess "Distributivity: (pure x <*? (y *> z)) == ((pure x <*? y) *> (pure x <*? z))" $
        \x -> lawDistributivity @(Over String) @Int @Int x
    , expectSuccess "Associativity: take a look at tests/Laws.hs" $
        \x -> lawAssociativity @(Over String) @Int @Int x ]

overTheorems :: Tests
overTheorems = testGroup "Theorems"
    [ expectSuccess "Apply a pure function to the result: (f <$> select x y) == (select (second f <$> x) ((f .) <$> y))" $
        \x -> theorem1 @(Over String) @Int @Int x
    , expectSuccess "Apply a pure function to the Left case of the first argument: (select (first f <$> x) y) == (select x ((. f) <$> y))" $
        \x -> theorem2 @(Over String) @Int @Int @Int x
    , expectSuccess "Apply a pure function to the second argument: (select x (f <$> y)) == (select (first (flip f) <$> x) ((&) <$> y))" $
        \x -> theorem3 @(Over String) @Int @Int @Int x
    , expectSuccess "Generalised identity: (x <*? pure y) == (either y id <$> x)" $
        \x -> theorem4 @(Over String) @Int @Int x
    , expectSuccess "(f <*> g) == (f `apS` g)" $
        \x -> theorem5 @(Over String) @Int @Int x
    , expectSuccess "Interchange: (x *> (y <*? z)) == ((x *> y) <*? z)" $
        \x -> theorem6 @(Over String) @Int @Int x ]

overProperties :: Tests
overProperties = testGroup "Properties"
    [ expectFailure "pure-right: pure (Right x) <*? y = pure x" $
        \x -> propertyPureRight @(Over String) @Int @Int x
    , expectSuccess "pure-left: pure (Left x) <*? y = ($x) <$> y" $
        \x -> propertyPureLeft @(Over String) @Int @Int x ]

--------------------------------------------------------------------------------
------------------------ Under -------------------------------------------------
--------------------------------------------------------------------------------
under :: Tests
under = testGroup "Under"
    [ underLaws
    , underTheorems
    , underProperties ]

underLaws :: Tests
underLaws = testGroup "Laws"
    [ expectSuccess "Identity: (x <*? pure id) == (either id id <$> x)" $
        \x -> lawIdentity @(Under String) x
    , expectSuccess "Distributivity: (pure x <*? (y *> z)) == ((pure x <*? y) *> (pure x <*? z))" $
        \x -> lawDistributivity @(Under String) @Int @Int x
    , expectSuccess "Associativity: take a look at tests/Laws.hs" $
        \x -> lawAssociativity @(Under String) @Int @Int x ]

underTheorems :: Tests
underTheorems = testGroup "Theorems"
    [ expectSuccess "Apply a pure function to the result: (f <$> select x y) == (select (second f <$> x) ((f .) <$> y))" $
        \x -> theorem1 @(Under String) @Int @Int x
    , expectSuccess "Apply a pure function to the Left case of the first argument: (select (first f <$> x) y) == (select x ((. f) <$> y))" $
        \x -> theorem2 @(Under String) @Int @Int @Int x
    , expectSuccess "Apply a pure function to the second argument: (select x (f <$> y)) == (select (first (flip f) <$> x) ((&) <$> y))" $
        \x -> theorem3 @(Under String) @Int @Int @Int x
    , expectSuccess "Generalised identity: (x <*? pure y) == (either y id <$> x)" $
        \x -> theorem4 @(Under String) @Int @Int x
    -- 'Under' is a non-rigid selective functor
    , expectFailure "(f <*> g) == (f `apS` g)" $
        \x -> theorem5 @(Under String) @Int @Int x
    , expectSuccess "Interchange: (x *> (y <*? z)) == ((x *> y) <*? z)" $
        \x -> theorem6 @(Under String) @Int @Int x ]

underProperties :: Tests
underProperties = testGroup "Properties"
    [ expectSuccess "pure-right: pure (Right x) <*? y = pure x" $
        \x -> propertyPureRight @(Under String) @Int @Int x
    , expectFailure "pure-left: pure (Left x) <*? y = ($x) <$> y" $
        \x -> propertyPureLeft @(Under String) @Int @Int x ]

--------------------------------------------------------------------------------
------------------------ Validation --------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
validation :: Tests
validation = testGroup "Validation"
    [ validationLaws
    , validationTheorems
    , validationProperties
    , validationExample ]

validationLaws :: Tests
validationLaws = testGroup "Laws"
    [ expectSuccess "Identity: (x <*? pure id) == (either id id <$> x)" $
        \x -> lawIdentity @(Validation String) @Int x
    , expectSuccess "Distributivity: (pure x <*? (y *> z)) == ((pure x <*? y) *> (pure x <*? z))" $
        \x -> lawDistributivity @(Validation String) @Int @Int x
    , expectSuccess "Associativity: take a look at tests/Laws.hs" $
        \x -> lawAssociativity @(Validation String) @Int @Int @Int x ]

validationTheorems :: Tests
validationTheorems = testGroup "Theorems"
    [ expectSuccess "Apply a pure function to the result: (f <$> select x y) == (select (second f <$> x) ((f .) <$> y))" $
        \x -> theorem1 @(Validation String) @Int @Int @Int x
    , expectSuccess "Apply a pure function to the Left case of the first argument: (select (first f <$> x) y) == (select x ((. f) <$> y))" $
        \x -> theorem2 @(Validation String) @Int @Int @Int x
    , expectSuccess "Apply a pure function to the second argument: (select x (f <$> y)) == (select (first (flip f) <$> x) ((&) <$> y))" $
        \x -> theorem3 @(Validation String) @Int @Int @Int x
    , expectSuccess "Generalised identity: (x <*? pure y) == (either y id <$> x)" $
        \x -> theorem4 @(Validation String) @Int @Int x
    -- 'Validation' is a non-rigid selective functor
    , expectFailure "(f <*> g) == (f `apS` g)" $
        \x -> theorem5 @(Validation String) @Int @Int x
    -- 'Validation' is a non-rigid selective functor
    , expectFailure "Interchange: (x *> (y <*? z)) == ((x *> y) <*? z)" $
        \x -> theorem6 @(Validation String) @Int @Int @Int x ]

validationProperties :: Tests
validationProperties = testGroup "Properties"
    [ expectSuccess "pure-right: pure (Right x) <*? y = pure x" $
        \x -> propertyPureRight @(Validation String) @Int @Int x
    , expectSuccess "pure-left: pure (Left x) <*? y = ($x) <$> y" $
        \x -> propertyPureLeft @(Validation String) @Int @Int x ]

validationExample :: Tests
validationExample = testGroup "validationExample"
    [ expectSuccess "shape (Success True) (Success 1) (Failure [\"width?\"]) (Failure [\"height?\"])" $
        shape (Success True) (Success 1) (Failure ["width?"]) (Failure ["height?"]) == Success (Circle 1)
    , expectSuccess "shape (Success False) (Failure [\"radius?\"]) (Success 2) (Success 3)" $
        shape (Success False) (Failure ["radius?"]) (Success 2) (Success 3) == Success (Rectangle 2 3)
    , expectSuccess "shape (Success False) (Failure [\"radius?\"]) (Success 2) (Failure [\"height?\"])" $
        shape (Success False) (Failure ["radius?"]) (Success 2) (Failure ["height?"]) == Failure ["height?"]
    , expectSuccess "shape (Success False) (Success 1) (Failure [\"width?\"]) (Failure [\"height?\"])" $
        shape (Success False) (Success 1) (Failure ["width?"]) (Failure ["height?"]) == Failure ["width?", "height?"]
    , expectSuccess "shape (Failure [\"choice?\"]) (Failure [\"radius?\"]) (Success 2) (Failure [\"height?\"])" $
        shape (Failure ["choice?"]) (Failure ["radius?"]) (Success 2) (Failure ["height?"]) == Failure ["choice?"]
    , expectSuccess "twoShapes s1 s2" $
        twoShapes (shape (Failure ["choice 1?"]) (Success 1) (Failure ["width 1?"]) (Success 3)) (shape (Success False) (Success 1) (Success 2) (Failure ["height 2?"])) == Failure ["choice 1?","height 2?"] ]

--------------------------------------------------------------------------------
------------------------ ArrowMonad --------------------------------------------
--------------------------------------------------------------------------------
arrowMonad :: Tests
arrowMonad = testGroup "ArrowMonad (->)"
    [ arrowMonadLaws
    , arrowMonadTheorems
    , arrowMonadProperties ]

arrowMonadLaws :: Tests
arrowMonadLaws = testGroup "Laws"
    [ expectSuccess "Identity: (x <*? pure id) == (either id id <$> x)" $
        \x -> lawIdentity @(ArrowMonad (->)) @Int x
    , expectSuccess "Distributivity: (pure x <*? (y *> z)) == ((pure x <*? y) *> (pure x <*? z))" $
        \x -> lawDistributivity @(ArrowMonad (->)) @Int @Int x
    , expectSuccess "Associativity: take a look at tests/Laws.hs" $
        \x -> lawAssociativity @(ArrowMonad (->)) @Int @Int @Int x
    , expectSuccess "select == selectM" $
        \x -> lawMonad @(ArrowMonad (->)) @Int @Int x
    , expectSuccess "select == selectA" $
        \x -> selectALaw @(ArrowMonad (->)) @Int @Int x ]

arrowMonadTheorems :: Tests
arrowMonadTheorems = testGroup "Theorems"
    [ expectSuccess "Apply a pure function to the result: (f <$> select x y) == (select (second f <$> x) ((f .) <$> y))" $
        \x -> theorem1 @(ArrowMonad (->)) @Int @Int @Int x
    , expectSuccess "Apply a pure function to the Left case of the first argument: (select (first f <$> x) y) == (select x ((. f) <$> y))" $
        \x -> theorem2 @(ArrowMonad (->)) @Int @Int @Int x
    , expectSuccess "Apply a pure function to the second argument: (select x (f <$> y)) == (select (first (flip f) <$> x) ((&) <$> y))" $
        \x -> theorem3 @(ArrowMonad (->)) @Int @Int @Int x
    , expectSuccess "Generalised identity: (x <*? pure y) == (either y id <$> x)" $
        \x -> theorem4 @(ArrowMonad (->)) @Int @Int x
    , expectSuccess "(f <*> g) == (f `apS` g)" $
        \x -> theorem5 @(ArrowMonad (->)) @Int @Int x
    , expectSuccess "Interchange: (x *> (y <*? z)) == ((x *> y) <*? z)" $
        \x -> theorem6 @(ArrowMonad (->)) @Int @Int @Int x ]

arrowMonadProperties :: Tests
arrowMonadProperties = testGroup "Properties"
    [ expectSuccess "pure-right: pure (Right x) <*? y = pure x" $
        \x -> propertyPureRight @(ArrowMonad (->)) @Int @Int x
    , expectSuccess "pure-left: pure (Left x) <*? y = ($x) <$> y" $
        \x -> propertyPureLeft @(ArrowMonad (->)) @Int @Int x ]

--------------------------------------------------------------------------------
------------------------ Maybe -------------------------------------------------
--------------------------------------------------------------------------------
maybe :: Tests
maybe = testGroup "Maybe"
    [ maybeLaws
    , maybeTheorems
    , maybeProperties ]

maybeLaws :: Tests
maybeLaws = testGroup "Laws"
    [ expectSuccess "Identity: (x <*? pure id) == (either id id <$> x)" $
        \x -> lawIdentity @Maybe @Int x
    , expectSuccess "Distributivity: (pure x <*? (y *> z)) == ((pure x <*? y) *> (pure x <*? z))" $
        \x -> lawDistributivity @Maybe @Int @Int x
    , expectSuccess "Associativity: take a look at tests/Laws.hs" $
        \x -> lawAssociativity @Maybe @Int @Int @Int x
    , expectSuccess "select == selectM" $
        \x -> lawMonad @Maybe @Int @Int x ]

maybeTheorems :: Tests
maybeTheorems = testGroup "Theorems"
    [ expectSuccess "Apply a pure function to the result: (f <$> select x y) == (select (second f <$> x) ((f .) <$> y))" $
        \x -> theorem1 @Maybe @Int @Int @Int x
    , expectSuccess "Apply a pure function to the Left case of the first argument: (select (first f <$> x) y) == (select x ((. f) <$> y))" $
        \x -> theorem2 @Maybe @Int @Int @Int x
    , expectSuccess "Apply a pure function to the second argument: (select x (f <$> y)) == (select (first (flip f) <$> x) ((&) <$> y))" $
        \x -> theorem3 @Maybe @Int @Int @Int x
    , expectSuccess "Generalised identity: (x <*? pure y) == (either y id <$> x)" $
        \x -> theorem4 @Maybe @Int @Int x
    , expectSuccess "(f <*> g) == (f `apS` g)" $
        \x -> theorem5 @Maybe @Int @Int x
    , expectSuccess "Interchange: (x *> (y <*? z)) == ((x *> y) <*? z)" $
        \x -> theorem6 @Maybe @Int @Int @Int x ]

maybeProperties :: Tests
maybeProperties = testGroup "Properties"
    [ expectSuccess "pure-right: pure (Right x) <*? y = pure x" $
        \x -> propertyPureRight @Maybe @Int @Int x
    , expectSuccess "pure-left: pure (Left x) <*? y = ($x) <$> y" $
        \x -> propertyPureLeft @Maybe @Int @Int x ]

--------------------------------------------------------------------------------
------------------------ Identity ----------------------------------------------
--------------------------------------------------------------------------------
identity :: Tests
identity = testGroup "Identity"
    [ identityLaws
    , identityTheorems
    , identityProperties ]

identityLaws :: Tests
identityLaws = testGroup "Laws"
    [ expectSuccess "Identity: (x <*? pure id) == (either id id <$> x)" $
        \x -> lawIdentity @Identity @Int x
    , expectSuccess "Distributivity: (pure x <*? (y *> z)) == ((pure x <*? y) *> (pure x <*? z))" $
        \x -> lawDistributivity @Identity @Int @Int x
    , expectSuccess "Associativity: take a look at tests/Laws.hs" $
        \x -> lawAssociativity @Identity @Int @Int @Int x
    , expectSuccess "select == selectM" $
        \x -> lawMonad @Identity @Int @Int x ]

identityTheorems :: Tests
identityTheorems = testGroup "Theorems"
    [ expectSuccess "Apply a pure function to the result: (f <$> select x y) == (select (second f <$> x) ((f .) <$> y))" $
        \x -> theorem1 @Identity @Int @Int @Int x
    , expectSuccess "Apply a pure function to the Left case of the first argument: (select (first f <$> x) y) == (select x ((. f) <$> y))" $
        \x -> theorem2 @Identity @Int @Int @Int x
    , expectSuccess "Apply a pure function to the second argument: (select x (f <$> y)) == (select (first (flip f) <$> x) ((&) <$> y))" $
        \x -> theorem3 @Identity @Int @Int @Int x
    , expectSuccess "Generalised identity: (x <*? pure y) == (either y id <$> x)" $
        \x -> theorem4 @Identity @Int @Int x
    , expectSuccess "(f <*> g) == (f `apS` g)" $
        \x -> theorem5 @Identity @Int @Int x
    , expectSuccess "Interchange: (x *> (y <*? z)) == ((x *> y) <*? z)" $
        \x -> theorem6 @Identity @Int @Int @Int x ]

identityProperties :: Tests
identityProperties = testGroup "Properties"
    [ expectSuccess "pure-right: pure (Right x) <*? y = pure x" $
        \x -> propertyPureRight @Identity @Int @Int x
    , expectSuccess "pure-left: pure (Left x) <*? y = ($x) <$> y" $
        \x -> propertyPureLeft @Identity @Int @Int x ]

--------------------------------------------------------------------------------
------------------------ Writer ------------------------------------------------
--------------------------------------------------------------------------------

writer :: Tests
writer = testGroup "Writer"
    [ writerLaws
    , writerTheorems
    , writerProperties ]

type MyWriter = Writer [Int]

writerLaws :: Tests
writerLaws = testGroup "Laws"
    [ expectSuccess "Identity: (x <*? pure id) == (either id id <$> x)" $
        \x -> lawIdentity @MyWriter @Int x
    , expectSuccess "Distributivity: (pure x <*? (y *> z)) == ((pure x <*? y) *> (pure x <*? z))" $
        \x -> lawDistributivity @MyWriter @Int @Int x
    , expectSuccess "Associativity: take a look at tests/Laws.hs" $
        \x -> lawAssociativity @MyWriter @Int @Int @Int x
    , expectSuccess "select == selectM" $
        \x -> lawMonad @MyWriter @Int @Int x ]

writerTheorems :: Tests
writerTheorems = testGroup "Theorems"
    [ expectSuccess "Apply a pure function to the result: (f <$> select x y) == (select (second f <$> x) ((f .) <$> y))" $
        \x -> theorem1 @MyWriter @Int @Int @Int x
    , expectSuccess "Apply a pure function to the Left case of the first argument: (select (first f <$> x) y) == (select x ((. f) <$> y))" $
        \x -> theorem2 @MyWriter @Int @Int @Int x
    , expectSuccess "Apply a pure function to the second argument: (select x (f <$> y)) == (select (first (flip f) <$> x) ((&) <$> y))" $
        \x -> theorem3 @MyWriter @Int @Int @Int x
    , expectSuccess "Generalised Identity: (x <*? pure y) == (either y id <$> x)" $
        \x -> theorem4 @MyWriter @Int @Int x
    , expectSuccess "(f <*> g) == (f `apS` g)" $
        \x -> theorem5 @MyWriter @Int @Int x
    , expectSuccess "Interchange: (x *> (y <*? z)) == ((x *> y) <*? z)" $
        \x -> theorem6 @MyWriter @Int @Int @Int x ]

writerProperties :: Tests
writerProperties = testGroup "Properties"
    [ expectSuccess "pure-right: pure (Right x) <*? y = pure x" $
        \x -> propertyPureRight @MyWriter @Int @Int x
    , expectSuccess "pure-left: pure (Left x) <*? y = ($x) <$> y" $
        \x -> propertyPureLeft @MyWriter @Int @Int x ]

--------------------------------------------------------------------------------
------------------------ Except ------------------------------------------------
--------------------------------------------------------------------------------

except :: Tests
except = testGroup "Except"
    [ exceptLaws
    , exceptTheorems
    , exceptProperties ]

type MyExcept = Except [Int]

exceptLaws :: Tests
exceptLaws = testGroup "Laws"
    [ expectSuccess "Identity: (x <*? pure id) == (either id id <$> x)" $
        \x -> lawIdentity @MyExcept @Int x
    , expectSuccess "Distributivity: (pure x <*? (y *> z)) == ((pure x <*? y) *> (pure x <*? z))" $
        \x -> lawDistributivity @MyExcept @Int @Int x
    , expectSuccess "Associativity: take a look at tests/Laws.hs" $
        \x -> lawAssociativity @MyExcept @Int @Int @Int x
    , expectSuccess "select == selectM" $
        \x -> lawMonad @MyExcept @Int @Int x ]

exceptTheorems :: Tests
exceptTheorems = testGroup "Theorems"
    [ expectSuccess "Apply a pure function to the result: (f <$> select x y) == (select (second f <$> x) ((f .) <$> y))" $
        \x -> theorem1 @MyExcept @Int @Int @Int x
    , expectSuccess "Apply a pure function to the Left case of the first argument: (select (first f <$> x) y) == (select x ((. f) <$> y))" $
        \x -> theorem2 @MyExcept @Int @Int @Int x
    , expectSuccess "Apply a pure function to the second argument: (select x (f <$> y)) == (select (first (flip f) <$> x) ((&) <$> y))" $
        \x -> theorem3 @MyExcept @Int @Int @Int x
    , expectSuccess "Generalised Identity: (x <*? pure y) == (either y id <$> x)" $
        \x -> theorem4 @MyExcept @Int @Int x
    , expectSuccess "(f <*> g) == (f `apS` g)" $
        \x -> theorem5 @MyExcept @Int @Int x
    , expectSuccess "Interchange: (x *> (y <*? z)) == ((x *> y) <*? z)" $
        \x -> theorem6 @MyExcept @Int @Int @Int x ]

exceptProperties :: Tests
exceptProperties = testGroup "Properties"
    [ expectSuccess "pure-right: pure (Right x) <*? y = pure x" $
        \x -> propertyPureRight @MyExcept @Int @Int x
    , expectSuccess "pure-left: pure (Left x) <*? y = ($x) <$> y" $
        \x -> propertyPureLeft @MyExcept @Int @Int x ]
