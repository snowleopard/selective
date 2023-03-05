# Change log

## 0.7

* Drop `MonadTrans (ExceptT e)` instance to allow `transformers-0.6.1`.
  See #70.

## 0.6

* Start supporting GHC 9.4. See #66.
* Add `ComposeTraversable`. See #65.
* Make the `Applicative` instance of `ComposeEither` more interesting by relying
  on the `Selective f` constraint. See #64.
* Make the `Lift` instance lazier. See #63.
* Stop supporting GHC <= 8.6. See #62.
* Add `Control.Selective.Trans.Except` transformer. See #39.

## 0.5

* Allow `transformers-0.6`, see #47.
* Drop dependencies on `mtl` and `tasty`. See #45, #46.
* Derive the stock `Eq` and `Ord` instances for `Validation`, see #43.
* Add `selectT`, see #42.
* Add more general instances for `IdentityT` and `ReaderT`. This is technically
  a breaking change because `Selective` is not a superclass of `Monad`. See #38.

## 0.4.1

* Allow newer QuickCheck.

## 0.4

* Add multi-way selective functors: `Control.Selective.Multi`.

## 0.3

* Add freer rigid selective functors: `Control.Selective.Rigid.Freer`.
* Rename `Control.Selective.Free.Rigid` to `Control.Selective.Rigid.Free`.
* Add free selective functors: `Control.Selective.Free`.
* Switch to more conventional field names in `SelectA` and `SelectM`.

## 0.2

* Make compatible with GHC >= 8.0.2.
* Add another free construction `Control.Selective.Free`.
* Add several new `Selective` instances.
