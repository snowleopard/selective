{-# LANGUAGE TypeApplications #-}

import Prelude hiding (maybe)
import Data.Functor.Identity
import Test.Tasty
import Test.Tasty.QuickCheck as QC
import Test.Tasty.ExpectedFailure
import Control.Selective
import Laws

main :: IO ()
main = defaultMain $
    testGroup "Selective instances" [over, under, validation, maybe, identity]

-- main :: IO ()
-- main = do
--     putStrLn $ "\n\nCyclic dependency graph:\n\n" ++ draw task "B1"

--------------------------------------------------------------------------------
------------------------ Over --------------------------------------------------
--------------------------------------------------------------------------------
over :: TestTree
over = testGroup "Over" [overLaws, overTheorems, overProperties]

overLaws = testGroup "Laws"
    [ QC.testProperty "Identity: (x <*? pure id) == (either id id <$> x)" $
        \x -> lawIdentity @(Over String) x
    , QC.testProperty "Distributivity: (pure x <*? (y *> z)) == ((pure x <*? y) *> (pure x <*? z))" $
        \x -> lawDistributivity @(Over String) @Int @Int x
    , QC.testProperty "Associativity: take a look at tests/Laws.hs" $
        \x -> lawAssociativity @(Over String) @Int @Int x
    ]

overTheorems = testGroup "Theorems"
    [ QC.testProperty "Apply a pure function to the result: (f <$> select x y) == (select (second f <$> x) ((f .) <$> y))" $
        \x -> theorem1 @(Over String) @Int @Int x
    , QC.testProperty "Apply a pure function to the Left case of the first argument: (select (first f <$> x) y) == (select x ((. f) <$> y))" $
        \x -> theorem2 @(Over String) @Int @Int @Int x
    , QC.testProperty "Apply a pure function to the second argument: (select x (f <$> y)) == (select (first (flip f) <$> x) (flip ($) <$> y))" $
        \x -> theorem3 @(Over String) @Int @Int @Int x
    , QC.testProperty "Generalised identity: (x <*? pure y) == (either y id <$> x)" $
        \x -> theorem4 @(Over String) @Int @Int x
    , QC.testProperty "(f <*> g) == (f `apS` g)" $
        \x -> theorem5 @(Over String) @Int @Int x
    , QC.testProperty "Interchange: (x *> (y <*? z)) == ((x *> y) <*? z)" $
        \x -> theorem6 @(Over String) @Int @Int x
    ]

overProperties = testGroup "Properties"
    [ expectFail $
      QC.testProperty "pure-right: pure (Right x) <*? y = pure x" $
        \x -> propertyPureRight @(Over String) @Int @Int x
    , QC.testProperty "pure-left: pure (Left x) <*? y = ($x) <$> y" $
        \x -> propertyPureLeft @(Over String) @Int @Int x
    ]

--------------------------------------------------------------------------------
------------------------ Under -------------------------------------------------
--------------------------------------------------------------------------------
under :: TestTree
under = testGroup "Under" [underLaws, underTheorems, underProperties]

underLaws = testGroup "Laws"
    [ QC.testProperty "Identity: (x <*? pure id) == (either id id <$> x)" $
        \x -> lawIdentity @(Under String) x
    , QC.testProperty "Distributivity: (pure x <*? (y *> z)) == ((pure x <*? y) *> (pure x <*? z))" $
        \x -> lawDistributivity @(Under String) @Int @Int x
    , QC.testProperty "Associativity: take a look at tests/Laws.hs" $
        \x -> lawAssociativity @(Under String) @Int @Int x
    ]

underTheorems = testGroup "Theorems"
    [ QC.testProperty "Apply a pure function to the result: (f <$> select x y) == (select (second f <$> x) ((f .) <$> y))" $
        \x -> theorem1 @(Under String) @Int @Int x
    , QC.testProperty "Apply a pure function to the Left case of the first argument: (select (first f <$> x) y) == (select x ((. f) <$> y))" $
        \x -> theorem2 @(Under String) @Int @Int @Int x
    , QC.testProperty "Apply a pure function to the second argument: (select x (f <$> y)) == (select (first (flip f) <$> x) (flip ($) <$> y))" $
        \x -> theorem3 @(Under String) @Int @Int @Int x
    , QC.testProperty "Generalised identity: (x <*? pure y) == (either y id <$> x)" $
        \x -> theorem4 @(Under String) @Int @Int x
    , expectFailBecause "'Under' is a non-rigid selective functor" $
      QC.testProperty "(f <*> g) == (f `apS` g)" $
        \x -> theorem5 @(Under String) @Int @Int x
    , QC.testProperty "Interchange: (x *> (y <*? z)) == ((x *> y) <*? z)" $
        \x -> theorem6 @(Under String) @Int @Int x
    ]

underProperties = testGroup "Properties"
    [ QC.testProperty "pure-right: pure (Right x) <*? y = pure x" $
        \x -> propertyPureRight @(Under String) @Int @Int x
    , expectFail $
      QC.testProperty "pure-left: pure (Left x) <*? y = ($x) <$> y" $
        \x -> propertyPureLeft @(Under String) @Int @Int x
    ]
--------------------------------------------------------------------------------
------------------------ Validation --------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
validation :: TestTree
validation = testGroup "Validation"
    [validationLaws, validationTheorems, validationProperties]

validationLaws = testGroup "Laws"
    [ QC.testProperty "Identity: (x <*? pure id) == (either id id <$> x)" $
        \x -> lawIdentity @(Validation String) @Int x
    , QC.testProperty "Distributivity: (pure x <*? (y *> z)) == ((pure x <*? y) *> (pure x <*? z))" $
        \x -> lawDistributivity @(Validation String) @Int @Int x
    , QC.testProperty "Associativity: take a look at tests/Laws.hs" $
        \x -> lawAssociativity @(Validation String) @Int @Int @Int x
    ]

validationTheorems = testGroup "Theorems"
    [ QC.testProperty "Apply a pure function to the result: (f <$> select x y) == (select (second f <$> x) ((f .) <$> y))" $
        \x -> theorem1 @(Validation String) @Int @Int @Int x
    , QC.testProperty "Apply a pure function to the Left case of the first argument: (select (first f <$> x) y) == (select x ((. f) <$> y))" $
        \x -> theorem2 @(Validation String) @Int @Int @Int x
    , QC.testProperty "Apply a pure function to the second argument: (select x (f <$> y)) == (select (first (flip f) <$> x) (flip ($) <$> y))" $
        \x -> theorem3 @(Validation String) @Int @Int @Int x
    , QC.testProperty "Generalised identity: (x <*? pure y) == (either y id <$> x)" $
        \x -> theorem4 @(Validation String) @Int @Int x
    , expectFailBecause "'Validation' is a non-rigid selective functor" $
      QC.testProperty "(f <*> g) == (f `apS` g)" $
        \x -> theorem5 @(Validation String) @Int @Int x
    , expectFailBecause "'Validation' is a non-rigid selective functor" $
      QC.testProperty "Interchange: (x *> (y <*? z)) == ((x *> y) <*? z)" $
        \x -> theorem6 @(Validation String) @Int @Int @Int x
    ]

validationProperties = testGroup "Properties"
    [ QC.testProperty "pure-right: pure (Right x) <*? y = pure x" $
        \x -> propertyPureRight @(Validation String) @Int @Int x
    , QC.testProperty "pure-left: pure (Left x) <*? y = ($x) <$> y" $
        \x -> propertyPureLeft @(Validation String) @Int @Int x
    ]
--------------------------------------------------------------------------------
------------------------ Maybe -------------------------------------------------
--------------------------------------------------------------------------------
maybe :: TestTree
maybe = testGroup "Maybe" [maybeLaws, maybeTheorems, maybeProperties]

maybeLaws = testGroup "Laws"
    [ QC.testProperty "Identity: (x <*? pure id) == (either id id <$> x)" $
        \x -> lawIdentity @Maybe @Int x
    , QC.testProperty "Distributivity: (pure x <*? (y *> z)) == ((pure x <*? y) *> (pure x <*? z))" $
        \x -> lawDistributivity @Maybe @Int @Int x
    , QC.testProperty "Associativity: take a look at tests/Laws.hs" $
        \x -> lawAssociativity @Maybe @Int @Int @Int x
    , QC.testProperty "select == selectM" $
        \x -> lawMonad @Maybe @Int @Int x
    ]

maybeTheorems = testGroup "Theorems"
    [ QC.testProperty "Apply a pure function to the result: (f <$> select x y) == (select (second f <$> x) ((f .) <$> y))" $
        \x -> theorem1 @Maybe @Int @Int @Int x
    , QC.testProperty "Apply a pure function to the Left case of the first argument: (select (first f <$> x) y) == (select x ((. f) <$> y))" $
        \x -> theorem2 @Maybe @Int @Int @Int x
    , QC.testProperty "Apply a pure function to the second argument: (select x (f <$> y)) == (select (first (flip f) <$> x) (flip ($) <$> y))" $
        \x -> theorem3 @Maybe @Int @Int @Int x
    , QC.testProperty "Generalised identity: (x <*? pure y) == (either y id <$> x)" $
        \x -> theorem4 @Maybe @Int @Int x
    , QC.testProperty "(f <*> g) == (f `apS` g)" $
        \x -> theorem5 @Maybe @Int @Int x
    , QC.testProperty "Interchange: (x *> (y <*? z)) == ((x *> y) <*? z)" $
        \x -> theorem6 @Maybe @Int @Int @Int x
    ]

maybeProperties = testGroup "Properties"
    [ QC.testProperty "pure-right: pure (Right x) <*? y = pure x" $
        \x -> propertyPureRight @Maybe @Int @Int x
    , QC.testProperty "pure-left: pure (Left x) <*? y = ($x) <$> y" $
        \x -> propertyPureLeft @Maybe @Int @Int x
    ]
--------------------------------------------------------------------------------
------------------------ Identity ----------------------------------------------
--------------------------------------------------------------------------------
identity :: TestTree
identity = testGroup "Identity"
    [identityLaws, identityTheorems, identityProperties]

identityLaws = testGroup "Laws"
    [ QC.testProperty "Identity: (x <*? pure id) == (either id id <$> x)" $
        \x -> lawIdentity @Identity @Int x
    , QC.testProperty "Distributivity: (pure x <*? (y *> z)) == ((pure x <*? y) *> (pure x <*? z))" $
        \x -> lawDistributivity @Identity @Int @Int x
    , QC.testProperty "Associativity: take a look at tests/Laws.hs" $
        \x -> lawAssociativity @Identity @Int @Int @Int x
    , QC.testProperty "select == selectM" $
        \x -> lawMonad @Identity @Int @Int x
    ]

identityTheorems = testGroup "Theorems"
    [ QC.testProperty "Apply a pure function to the result: (f <$> select x y) == (select (second f <$> x) ((f .) <$> y))" $
        \x -> theorem1 @Identity @Int @Int @Int x
    , QC.testProperty "Apply a pure function to the Left case of the first argument: (select (first f <$> x) y) == (select x ((. f) <$> y))" $
        \x -> theorem2 @Identity @Int @Int @Int x
    , QC.testProperty "Apply a pure function to the second argument: (select x (f <$> y)) == (select (first (flip f) <$> x) (flip ($) <$> y))" $
        \x -> theorem3 @Identity @Int @Int @Int x
    , QC.testProperty "Generalised identity: (x <*? pure y) == (either y id <$> x)" $
        \x -> theorem4 @Identity @Int @Int x
    , QC.testProperty "(f <*> g) == (f `apS` g)" $
        \x -> theorem5 @Identity @Int @Int x
    , QC.testProperty "Interchange: (x *> (y <*? z)) == ((x *> y) <*? z)" $
        \x -> theorem6 @Identity @Int @Int @Int x
    ]

identityProperties = testGroup "Properties"
    [ QC.testProperty "pure-right: pure (Right x) <*? y = pure x" $
        \x -> propertyPureRight @Identity @Int @Int x
    , QC.testProperty "pure-left: pure (Left x) <*? y = ($x) <$> y" $
        \x -> propertyPureLeft @Identity @Int @Int x
    ]