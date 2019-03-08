# An IRC conversation about `Branchy` type class

The conversation below has been extracted from a complete IRC #haskell log for
13 February 2009. Various "user join/left" notifications have been filtered out.
Thanks to Brent Yorgey for providing the original log.

----

```
15:59:22 <beelsebob> we can even take this further... (:) <$> getChar <*> myGetLine -- now all we're missing is the if part
15:59:29 <wli> Opportunistically do partial normalization at various places in the implementation, add some API function to force normalization further.
15:59:50 <beelsebob> but that really does require monads
15:59:54 <beelsebob> not just applicatives
16:04:21 <Cale> hmm
16:05:12 <Cale> Does an applicative with that sort of branching imply that it's a monad?
16:06:24 <byorgey> Cale: what sort of branching?
16:06:35 <beelsebob> Cale: not any sort of branching
16:06:39 <beelsebob> just some sorts of branching
16:07:58 <beelsebob> (if' (=='\n') (\_ _ -> "") (:)) <$> getChar <*> myGetLine -- does this work?
16:08:02 <beelsebob> I'm not certain
16:08:09 <beelsebob> it looks like it should
16:08:41 <beelsebob> maybe I was wrong about that one being monadic
16:08:55 <jasondew> anyone know who maintains the GD bindings?
16:09:01 <beelsebob> oh wait – that one doesn't work
16:09:10 <beelsebob> that one evaluates myGetLine whether the condition was true or not
16:09:16 <beelsebob> so yeh, it does need a monad
16:09:57 <Cale> So applicative + if -> monad?
16:10:05 <byorgey> anything where you need to decide which effects you want based on some intermediate result requires a monad.
16:10:05 <Cale> Or is it something in between?
16:10:32 <byorgey> Cale: what, precisely, do you mean by 'applicative + if' ?
16:10:35 <beelsebob> it's not so much applicative + if -> monad, it's applicative + if and not wanting to be too strict -> monad
16:10:35 <Cale> Can you define join using the applicative operations and an  if :: f Bool -> f a -> f a -> f a ?
16:10:46 <Cale> (I don't think so...)
16:10:51 <beelsebob> Cale: no, you can't
16:11:01 <Cale> So there might be something in between there.
16:11:08 <byorgey> Cale: I see, no, monad is more powerful than that
16:11:14 <Cale> Yeah.
16:11:14 <beelsebob> I'm not sure what you mean by between the two
16:11:27 <Cale> beelsebob: Between Applicative and Monad
16:11:29 <beelsebob> what would it be able to express?
16:11:37 <beelsebob> i.e. what more than applicative but less than monad
16:11:45 <byorgey> it would be able to express some useful things.
16:11:49 <Cale> This function in particular.
16:12:00 <beelsebob> Cale: I think bind is the crucial thing missing here
16:12:13 <beelsebob> it needs a "do the getChar first, then do the if, then figure out the rest"
16:12:15 <Cale> Well, this doesn't need the full power of bind.
16:12:23 <beelsebob> doesn't it?
16:13:19 <byorgey> applicative + if  allows you to do anything where you know the computations you want to choose among beforehand (and there are finitely many).
16:13:35 <byorgey> monad lets you arbitrarily *compute* new computations based on intermediate results.
16:13:43 <byorgey> so there could be infinitely many you want to choose among.
16:13:48 <Cale> yeah
16:13:50 <beelsebob> the key is that the function (if') returns a wrapped value from a pure value, rather than requiring the whole thing to be wrapped?
16:13:56 <beelsebob> unless I'm missing something
16:14:27 <beelsebob> hmm... interesting
16:14:30 <Cale> beelsebob: Well, it lets you decide which of two computations you'd like to choose to execute based on the result of another.
16:14:41 <Cale> (and thus you could choose between finitely many)
16:14:49 <beelsebob> Cale: yeh, that's kinda what I'm saying – it does that by only needing a pure valued input
16:14:56 <beelsebob> rather than needing the whole function to be wrapped up
16:15:07 <beelsebob> which is exactly the difference between (=<<) and (<*>)
16:15:43 <ddarius> beelsebob: They're not even the same type.
16:15:45 <beelsebob> so I find this interesting – it suggests that monads are only necessary over applicatives when you actually want sequencing
16:15:50 <beelsebob> ddarius: that's my point
16:16:01 <beelsebob> (<*>)'s type has the function all wrapped up
16:16:07 <beelsebob> you can't evaluate anything until you get into the applicative
16:16:22 <beelsebob> (=<<) doesn't – it allows you to figure out what action you want without getting inside the monad yet
16:16:37 <Cale> I find this wording to be confusing... but I think I see what you're saying.
16:16:47 * byorgey was about to say that =)
16:16:53 <beelsebob> yeh, sorry
16:17:03 <beelsebob> a decent amount of champagne has passed my lips :/
16:17:26 <beelsebob> so hmm, does this mean that monads are litterally all about sequencing?
16:17:27 <byorgey> hehe
16:17:29 <rndm> beelsebob: hopefully in the canonical direction
16:17:36 <beelsebob> rndm: so far, yes :)
16:17:45 <beelsebob> are they only more powerful than applicatives exactly when you want sequencing
16:17:45 <Cale> beelsebob: Well... so are applicatives, in a way.
16:17:52 <beelsebob> true
16:18:17 <Cale> beelsebob: The difference between applicatives and monads is in your ability to choose what the rest of the computation should be.
16:18:23 <beelsebob> yeh
16:18:29 <beelsebob> decision half way through
16:18:35 <byorgey> I don't think either are inherently about sequencing.
16:18:37 <wli> > let orbit (n :: Integer) k = unfoldr (\(x, s) -> let y = (x * k) `mod` n in if member y s then Nothing else Just (y, (y, Data.Set.insert y s))) (1, empty) ; order n k = length $ orbit n k in (orbit 40 3, order 40 3)
16:18:38 <Cale> In an applicative, it's fixed independently of the result of the earlier computations.
16:18:39 <lambdabot>   Not in scope: `member'    Ambiguous occurrence `empty'
16:18:39 <lambdabot>      It could refer ...
16:18:42 <byorgey> no more than function composition is, at least.
16:18:44 <wli> ergh
16:18:54 <beelsebob> byorgey: I think monad really is
16:19:09 <beelsebob> it's sole advantage over applicative is that you can base descisions based on "earlier" computations
16:19:10 <Cale> byorgey: Well, perhaps composing computations is a better name than sequencing.
16:19:16 <beelsebob> i.e. ones on the right of the =<<
16:19:18 <byorgey> Cale: sure.
16:19:21 <wli> > let orbit (n :: Integer) k = unfoldr (\(x, s) -> let y = (x * k) `mod` n in if Data.Set.member y s then Nothing else Just (y, (y, Data.Set.insert y s))) (1, Data.Set.empty) ; order n k = length $ orbit n k in (orbit 40 3, order 40 3)
16:19:23 <lambdabot>   /tmp/2059571785234403431:70:139: Not in scope: `Data.Set.member'/tmp/205957...
16:19:30 <wli> Brilliant.
16:19:42 <byorgey> Cale: that's my point.
16:19:43 <Cale> beelsebob: But we just found a nice thing sitting in between applicative and monad which has a weaker kind of selection.
16:19:53 <beelsebob> did we?
16:19:56 <Cale> Yes :)
16:20:02 <beelsebob> what can it not do?
16:20:10 <beelsebob> (that a monad can)
16:20:18 <Cale> class Applicative f => Branchy f where ifA :: f Bool -> f a -> f a -> f a
16:20:31 <Cale> It can't select between infinitely many futures.
16:20:36 <idnar> that sounds arrowish
16:20:43 <beelsebob> but that's just liftA2 (if') isn't it?
16:20:46 <Cale> no
16:20:51 <Cale> It's intended to be different.
16:20:56 <beelsebob> oh so hang on
16:21:04 <beelsebob> this thing can do the lazyness with finitely many things
16:21:05 <byorgey> beelsebob: liftA2 (if') would still have the effects of both its arguments.
16:21:08 <idnar> @type liftA2 (if1)
16:21:09 <beelsebob> but can't deal with infinitely many
16:21:09 <lambdabot> Not in scope: `if1'
16:21:11 <idnar> @type liftA2 (if')
16:21:12 <beelsebob> interesting
16:21:12 <wli> Somebody please add fully-qualified Map and Set to lambdabot's namespace.
16:21:13 <lambdabot> Not in scope: `if''
16:21:27 <idnar> @type let if' p a b = if p then a else b in liftA2 (if')
16:21:29 <lambdabot> forall b (f :: * -> *). (Applicative f) => f Bool -> f b -> f (b -> b)
16:21:44 <Cale> hmm...
16:21:48 <idnar> @type let if' p a b = if p then a else b in liftA3 (if')
16:21:49 <lambdabot> forall b (f :: * -> *). (Applicative f) => f Bool -> f b -> f b -> f b
16:22:05 <beelsebob> idnar: it has the right type, but not the right semantics
16:22:09 <Cale> > let orbit (n :: Integer) k = unfoldr (\(x, s) -> let y = (x * k) `mod` n in if S.member y s then Nothing else Just (y, (y, S.insert y s))) (1, S.empty) ; order n k = length $ orbit n k in (orbit 40 3, order 40 3)
16:22:11 <beelsebob> so... hmm
16:22:11 <lambdabot>   /tmp/67296378691101627:70:139: Not in scope: `S.member'/tmp/672963786911016...
16:22:14 <Cale> okay.
16:22:16 <Cale> I don't know :)
16:22:18 <beelsebob> I really get the feeling it should be possible to implement bind with that
16:22:31 <wli> > let orbit (n :: Integer) k = unfoldr (\(x, s) -> let y = (x * k) `mod` n in if Set.member y s then Nothing else Just (y, (y, Set.insert y s))) (1, Set.empty) ; order n k = length $ orbit n k in (orbit 40 3, order 40 3)
16:22:31 <Cale> beelsebob: Forget bind, think about join.
16:22:33 <lambdabot>   ([3,9,27,1],4)
16:22:40 <beelsebob> Cale: well, one or the other
16:22:44 <beelsebob> they're equally powerful
16:22:48 <Cale> beelsebob: To implement join, you need something which decreases the number of functor applications.
16:22:59 <Cale> beelsebob: But ifA doesn't give us anything like that.
16:23:02 <beelsebob> hmm
16:23:13 <beelsebob> I'm not sure I get what you mean by decreasing the number of function apps
16:23:20 <Cale> :t join
16:23:21 <lambdabot> forall (m :: * -> *) a. (Monad m) => m (m a) -> m a
16:23:38 <Cale> m (m a) -> m a -- we go from 2 m's to 1.
16:23:44 * byorgey doesn't get it either, how does (>>=) 'decrease the number of functor applications'?  yet you can implement join with that.
16:23:50 <idnar> @type (>>=)
16:23:51 <lambdabot> forall (m :: * -> *) a b. (Monad m) => m a -> (a -> m b) -> m b
16:24:00 <idnar> there's an m a and an a there :P
16:24:10 <Cale> well, take a = m b
16:24:23 <byorgey> ah, ok
16:24:26 <beelsebob> ahhh
16:24:30 <beelsebob> interesting
16:25:30 <idnar> @type (=<<) id
16:25:31 <lambdabot> forall (m :: * -> *) b. (Monad m) => m (m b) -> m b
16:25:44 <ddarius> @src join
16:25:45 <lambdabot> join x =  x >>= id
16:26:35 --- part: ispiked left #haskell
16:27:48 <Cale> (but yeah, bind is a little harder to think about in this way because it has both a and b)
16:27:56 <beelsebob> so hmm
16:28:14 <beelsebob> do we have any Branchies that are useful as Monads?
16:28:34 <Cale> Or any Branchies which are not Monads? :)
16:28:39 <beelsebob> yeh
16:28:45 <byorgey> that's the more interesting question...
16:29:20 <beelsebob> well what I was thinking was are the monadic operators actually useful on IO for example, if you have the IO Branchy
16:29:34 <byorgey> hmm, ZipList is Branchy I think
16:29:44 <byorgey> although I'm not sure what laws Branchy things should satisfy.
16:30:54 <byorgey> instance Branchy ZipList where ifA (ZipList bs) (ZipList xs) (ZipList ys) = ZipList $ zipWith if' bs xs ys
16:30:57 <Cale> ifA (pure True) x y = x
16:31:02 <Cale> ifA (pure False) x y = y
16:31:04 <Cale> for one
16:31:09 <byorgey> check! =)
16:31:39 <byorgey> er, sorry, that should be zipWith3 or something
16:32:05 <byorgey> hopefully the idea is clear =)
16:32:18 <beelsebob> @instances Monad
16:32:19 <lambdabot> ((->) r), ArrowMonad a, Cont r, ContT r m, Either e, ErrorT e m, IO, Maybe, RWS r w s, RWST r w s m, Reader r, ReaderT r m, ST s, State s, StateT s m, Writer w, WriterT w m, []
16:32:21 <byorgey> (the point being that ZipList is an Applicative which is not a Monad)
16:32:28 <beelsebob> so hmm
16:32:38 <beelsebob> are there any Applicatives which are not Branchies
16:32:58 <beelsebob> yes, the normal list applicative?
16:33:00 <idnar> > let ifA (ZipList bs) (ZipList xs) (ZipList ys) = ZipList $ zipWith3 if' bs xs ys in ifA (pure True) (ZipList [1]) (ZipList [2])
16:33:02 <lambdabot>   Not in scope: `if''    Ambiguous occurrence `pure'
16:33:02 <lambdabot>      It could refer to e...
16:33:10 <byorgey> beelsebob: that's a monad, so it has to be Branchy
16:33:17 <beelsebob> oh, duh
16:33:18 <idnar> > let if' p a b = if p then a else b; ifA (ZipList bs) (ZipList xs) (ZipList ys) = ZipList $ zipWith3 if' bs xs ys in ifA (pure True) (ZipList [1]) (ZipList [2])
16:33:20 <lambdabot>       Ambiguous occurrence `pure'
16:33:20 <lambdabot>      It could refer to either `Control.Appl...
16:33:26 <byorgey> doh!
16:33:30 <beelsebob> @instances Applicative
16:33:31 <lambdabot> Couldn't find class `Applicative'. Try @instances-importing
16:33:33 <idnar> > let if' p a b = if p then a else b; ifA (ZipList bs) (ZipList xs) (ZipList ys) = ZipList $ zipWith3 if' bs xs ys in ifA (Control.Applicative.pure True) (ZipList [1]) (ZipList [2])
16:33:34 <lambdabot>       No instance for (Show (ZipList t))
16:33:34 <lambdabot>        arising from a use of `show' ...
16:33:41 <byorgey> double doh
16:33:43 <beelsebob> @instances-importing Control.Applicative Applicative
16:33:44 <lambdabot> ((,) a), ((->) a), Const m, IO, Maybe, WrappedArrow a b, WrappedMonad m, ZipList, []
16:33:48 <idnar> > let if' p a b = if p then a else b; ifA (ZipList bs) (ZipList xs) (ZipList ys) = ZipList $ zipWith3 if' bs xs ys in getZipList $ ifA (Control.Applicative.pure True) (ZipList [1]) (ZipList [2])
16:33:50 <lambdabot>   [1]
16:33:57 <idnar> > let if' p a b = if p then a else b; ifA (ZipList bs) (ZipList xs) (ZipList ys) = ZipList $ zipWith3 if' bs xs ys in getZipList $ ifA (Control.Applicative.pure False) (ZipList [1]) (ZipList [2])
16:33:58 <lambdabot>   [2]
16:34:03 <idnar> yay
16:34:07 <beelsebob> ((,) a) is another Branchy that's not a monad, isn't it
16:34:43 <idnar> why isn't ((,) a) a monad?
16:34:45 <byorgey> beelsebob: that's the writer monad
16:34:52 <beelsebob> is it?
16:35:02 <beelsebob> I thought that needed Monoid on the a?
16:35:20 <byorgey> beelsebob: yeah, the Applicative instance requires Monoid on the a too.
16:35:25 <beelsebob> oh, okay
16:35:27 <byorgey> it just isn't shown in that list.
16:35:31 <Peaker> idnar: without Monoid or something else, how do you implement "return"?
16:35:50 <beelsebob> Peaker: similarly though, how do you implement pure, as byorgey points out
16:35:54 <Peaker> yeah
16:35:57 <Peaker> same thing
16:36:01 <Peaker> pure=return
16:36:14 <byorgey> right, @instances-importing just doesn't list type class constraints
16:36:33 <idnar> Peaker: okay, but assuming you have Monoid...?
16:36:37 <Peaker> > return 5 :: (Int, Int)
16:36:39 <lambdabot>       No instance for (Monad ((,) Int))
16:36:39 <lambdabot>        arising from a use of `return'...
16:36:42 <Peaker> idnar: mempty then
16:36:57 <idnar> Peaker: hmm?
16:37:05 <Peaker> idnar: then it is a monad
16:37:09 <idnar> > Control.Applicative.pure 5 :: (Int, Int)
16:37:10 <lambdabot>       No instance for (Monoid Int)
16:37:10 <lambdabot>        arising from a use of `Control.Appl...
16:37:16 <idnar> > Control.Applicative.pure [5] :: (Int, Int)
16:37:18 <lambdabot>   Couldn't match expected type `Int' against inferred type `[a]'
16:37:20 <beelsebob> hmm, I think Cale's laws may actually encode the whole thing
16:37:21 <idnar> oops
16:37:21 <Peaker> I was hoping it would complain about missing Monoid instance
16:37:26 <idnar> > Control.Applicative.pure [5] :: ([Int], [Int])
16:37:28 <lambdabot>   ([],[5])
16:37:32 <byorgey> anyway, I don't know of any Applicatives that aren't Monads other than ZipList
16:37:34 <Peaker> > return 5 :: ([Int], Int)
16:37:35 <idnar> > return [5] :: ([Int], [Int])
16:37:36 <lambdabot>       No instance for (Monad ((,) [Int]))
16:37:36 <lambdabot>        arising from a use of `retur...
16:37:37 <lambdabot>       No instance for (Monad ((,) [Int]))
16:37:37 <lambdabot>        arising from a use of `retur...
16:37:42 <beelsebob> in that they demand that ifB (pure True) x _|_ = x
16:37:48 <idnar> so, there's an Applicative instance but no Monad instance
16:37:49 <Peaker> the writer monad seems to not be imported there
16:37:50 <beelsebob> which is the thing we really wanted
16:37:57 <idnar> (where is that Applicative instance defined?)
16:38:19 <Peaker> idnar: that's the disadvantage of orphaned instances -- the writer monad instance is really an orphan instance
16:38:35 <idnar> anyhow Writer is just a newtype of (,) a
16:38:37 <Peaker> (you have imported both the class and the type, but the instance isn't there)
16:38:51 <idnar> I can't find a definition for (,) a though
16:39:03 <byorgey> idnar: I think it's in Control.Monad.Instances, isn't it?
16:39:12 <idnar> byorgey: not on my local system
16:39:39 <byorgey> idnar: huh, maybe there isn't one
16:39:45 <byorgey> idnar: there's only the Writer newtype
16:39:50 <idnar> anyhow, that doesn't really matter
16:39:57 <byorgey> > return [5] :: Writer [Int] [Int]
16:39:58 <lambdabot>       No instance for (Show (Writer [Int] [Int]))
16:39:58 <lambdabot>        arising from a use o...
16:40:10 <idnar> the point is ((,) a) is a monad even if there's no standard instance :P
16:40:13 <beelsebob> hmm
16:40:18 <byorgey> indeed =)
16:40:23 <idnar> NEEEEXT!
16:40:58 <beelsebob> would it make any sense for Branchy and Applicative to be equal – i.e. is it possible that (<*>) and pure are not sufficient to write ifB, but that for anything that you can get an Applicative instance of, you can also write ifB
16:41:11 <Petrosian> Hey, anyone got any useful examples of using mfix?
16:41:16 <idnar> what is Const?
16:41:25 <byorgey> beelsebob: that sounds possible, I don't know.
16:41:30 <byorgey> idnar: newtype Const a b = Const a
16:41:49 <byorgey> it's an Applicative (and Monad) with Monoid a
16:41:53 <idnar> that's an applicative that "contains no value"?
16:41:55 <Cale> beelsebob: Possibly for Hask, but I highly doubt in an arbitrary category.
16:42:07 <byorgey> idnar: right.
16:42:20 <idnar> funky (also, can't find a monad instance, but I guess I can probably figure it out)
16:42:36 * beelsebob is suddenly stricken with the wish he'd learned more of category theory
16:42:52 <idnar> > Control.Applicative.pure 5 :: Const String
16:42:54 <lambdabot>       `Const String' is not applied to enough type arguments
16:42:54 <lambdabot>      Expected ki...
16:42:59 <idnar> > Control.Applicative.pure 5 :: Const String Int
16:43:00 <lambdabot>       No instance for (Show (Const String Int))
16:43:00 <lambdabot>        arising from a use of ...
16:43:01 <byorgey> idnar: it's mostly useful in conjunction with things like Traversable -- e.g. for computing some property of a structure that doesn't depend on the data it contains
16:43:08 <idnar> > getConst $ Control.Applicative.pure 5 :: Const String Int
16:43:10 <lambdabot>       No instance for (Show (Const String Int))
16:43:10 <lambdabot>        arising from a use of ...
16:43:22 <idnar> whaat?
16:43:29 <idnar> > getConst (Control.Applicative.pure 5 :: Const String Int)
16:43:31 <lambdabot>   ""
16:43:34 <idnar> ah
16:43:56 <Peaker> beelsebob: what's the type of ifB?
16:43:58 <idnar> byorgey: okay
16:44:18 <byorgey> > getConst (Const "foo" (+1) <*> Const "bar" 5)
16:44:20 <lambdabot>   Couldn't match expected type `(a2 -> a2) -> Const a (a1 -> b)'
16:44:26 <beelsebob> Peaker: ifB :: (Branchy b) => b Bool -> b a -> b a -> b a
16:44:35 <byorgey> err, hmm
16:44:44 <byorgey> oh, duh
16:44:57 <idnar> byorgey: I guess the instances are the same as for (,) a, except with the second member discarded
16:45:05 <byorgey> idnar: right.
16:45:46 <byorgey> all you do is just mempty for pure, and mappend for <*>.
16:46:19 <byorgey> idnar: McBride and Paterson's "Applicative Programming With Effects" has some neat examples of its use.
16:46:26 <Peaker> beelsebob: not all Applicatives can implement that
16:46:32 <beelsebob> Peaker: which one can't?
16:46:58 <gwern> good grief. I looked in at noon and y'all were talking about applicative; and now it's 8 and y'all are *still* talking about applicative
16:47:14 <beelsebob> gwern: no, we're talking about Branchies now
16:47:20 <byorgey> Peaker: we know you can't implement that using the Applicative methods.  beelsebob's question was whether there is *actually* anything which could be an instance of Applicative but not Branchy.
16:47:28 <Peaker> beelsebob: if you have some parser/grammar type as an applicative instance, you don't want to have your grammar depend on the previous parse results - so you can build a DSM from it
16:47:33 <idnar> beelsebob: I'm sure you could deliberately construct an applicative that isn't a branchy
16:47:39 <Peaker> byorgey: I understand
16:47:52 <gwern> beelsebob: looks like an applicative discussion to me -_-
16:47:55 <byorgey> gwern: I think you need a larger sample size. ;)
16:47:56 <idnar> beelsebob: the question is whether there are any /interesting/ applicatives that aren't branchies, or any interesting branchies that aren't monads
16:47:58 <beelsebob> idnar: are you sure?
16:48:07 <beelsebob> idnar: well, we already found the latter
16:48:13 <beelsebob> ZipList is a Branchy but not a Monad
16:48:29 <idnar> oh, well, yes
16:48:29 <gwern> byorgey: I only deal in logical proofs! we care not for sample sizes!
16:48:59 <gwern> (show me as many non-black non-ravens, and I still will maintain we do not know ravens are black!)
16:49:01 <idnar> if it's not possible to build ifB from pure and <*>, then my intuition tells me that it should be possible to construct an applicative that isn't a branchy; I can't prove that, though :P
16:49:20 <beelsebob> idnar: yeh, nor can I, which is why I'm suspicious of it
16:49:28 <byorgey> beelsebob: well, there aren't going to be any other *standard* instances that are Applicative but not Branchy, because ZipList is the only standard Applicative instance that isn't a monad
16:49:32 <beelsebob> I can't even think how a proof would start
16:49:34 <gwern> hm, c.h.o is down?
16:49:48 <idnar> the thing is, an applicative constructed in that fashion would probably not have much practical value :P
16:49:49 <beelsebob> byorgey: yeh, I want to think more generally than the standard things we see in haskell
16:49:57 <byorgey> right, ok.
16:49:59 <gwern> yeah, it's up for ping but a darcs pull & web browsing fails
16:50:02 <gwern> how annoying
16:50:12 <byorgey> gwern: yeah, down for me too.
16:50:22 <idnar> I'm too tired to think about this properly; but you just need to find some way to deliberately "break" ifB without breaking <*> / pure
16:51:01 <beelsebob> Cale: your Branchy laws aren't quite right btw – should have been ifB (pure True) (pure x) _ = pure x and ifB (pure False) _ (prue y) = pure y
16:51:07 <idnar> so, what other applicatives do we have? parsec?
16:51:15 <Cale> beelsebob: oh?
16:51:18 <Cale> beelsebob: why?
16:51:29 <beelsebob> well, take the ZipList branchy for example
16:51:33 <Cale> beelsebob: I think it's *very* important that it's not just for pure
16:51:33 <beelsebob> oh hang on
16:51:41 <beelsebob> am I thinking bollocks
16:51:42 <idnar> we already proved Cale's version for ZipList :P
16:51:43 <beelsebob> ...
16:51:44 <beelsebob> *thinks*
16:51:52 <beelsebob> yeh, sorry, I'm thinking bollocks
16:51:53 <Peaker> beelsebob, idnar, byorgey: here you go: data NotBranchy a = NotBranchy (IO ()) ; instance Functor NotBranchy where fmap = id ; instance Applicative NotBranchy where pure _ = NotBranchy (return ()) ; (NotBranchy x)<*>(NotBranchy y) = (NotBranchy (x>>y))
16:51:55 <beelsebob> too much booze
16:51:58 <idnar> oh, maybe not
16:52:30 <idnar> @type fmap
16:52:31 <lambdabot> forall a b (f :: * -> *). (Functor f) => (a -> b) -> f a -> f b
16:52:32 <idnar> @type id
16:52:34 <lambdabot> forall a. a -> a
16:52:39 <byorgey> Peaker: fmap = id??
16:52:53 <Peaker> byorgey: yeah, it doesn't actually contain a value -- its an applicative purely for the effect
16:53:10 <byorgey> ohhhh, right, I see. sorry.
16:53:15 <idnar> id :: (a -> b) -> NotBranchy a -> NotBranchy b
16:53:21 <idnar> how can that unify?
16:53:38 <byorgey> oh, wait!
16:53:43 <byorgey> Const works.
16:53:47 <byorgey> it isn't a monad, I forgot.
16:53:53 <byorgey> and it isn't Branchy either.
16:53:55 <beelsebob> oh, awesome
16:53:58 <idnar> I guess Peaker meant const
16:54:08 <beelsebob> so Branchy is useful
16:54:14 <byorgey> for the same reason as Peaker's example above -- a 'Const b a' does not actually contain an a.
16:54:17 <Peaker> yeah, I don't know Const, so I re-made it up :)
16:54:24 <idnar> beelsebob: eh, only if NotBranchy is useful
16:54:41 <byorgey> beelsebob: let's not jump to conclusions =)
16:54:43 <beelsebob> idnar: which is reducable to if Const is useful
16:54:44 <Peaker> beelsebob: there's ArrowChoice which is pretty similar
16:54:44 <beelsebob> which it is
16:55:01 <Peaker> @src ArrowChoice
16:55:01 <lambdabot> Source not found. Sorry.
16:55:10 <idnar> beelsebob: but Const is a monad
16:55:13 <byorgey> Peaker: yeah, I wonder what the connection is.
16:55:22 <beelsebob> idnar: no its not?
16:55:26 <Peaker> ArrowChoice to Arrow is what Branchy is to Applicative?
16:55:43 <idnar> beelsebob: oh, whoops, I'm thinking of Identity
16:55:51 <byorgey> Peaker: something like that.
16:55:52 <idnar> uhm, so is Const a Branchy?
16:55:56 <beelsebob> nope
16:56:14 <beelsebob> so we have an Applicative which is not a Branchy, and a Branchy which is not a Monad
16:56:24 <byorgey> no, it isn't.  you could *implement* it, but it wouldn't satisfy the laws.
16:56:32 --- part: BrokenClockwork left #haskell
16:56:39 <byorgey> since a 'Const x Bool' does not actually contain a Bool
16:56:46 <byorgey> you wouldn't know which to pick.
16:57:21 <Peaker> beelsebob: who is a Branchy that is not a monad?
16:57:27 <beelsebob> ZipList
16:57:28 <idnar> Peaker: ZipList
16:57:28 <byorgey> Peaker: ZipList
16:57:42 <idnar> oh boy
16:57:59 <byorgey> someone should write this up on their blog =)
16:58:08 <Peaker> finite ZipLists are well-formed Applicatives?
16:58:21 <byorgey> I'll do it if no one else does, but I need to get back to writing my Monad.Reader article...
16:58:35 <beelsebob> Peaker: yep, pure is robot monkey, and <*> is pairwise application
16:58:45 <byorgey> beelsebob: no, pure is repeat
16:58:55 <beelsebob> oh, yeh
16:59:19 <byorgey> pure is robot monkey for the normal list instance, which corresponds to the list monad too.
16:59:28 <beelsebob> yeh
17:00:14 <byorgey> well, fun hashing this out with you all
17:00:19 * byorgey goes back to writing
17:01:03 * beelsebob will try and synthesise a blog entry about this tomorrow if no one else wants to
17:01:10 <beelsebob> I may be rather more sober
17:02:28 <idnar> someone write a paper
17:03:26 <byorgey> I kind of doubt it's worth a paper, unless we can find some great use case for which Branchy is well-suited
17:03:46 <beelsebob> well, Ivan Tomac just went "oh hay, I could really use that in my GPU code generator"
17:03:49 <idnar> oh, yeah, we need an interesting use of ifB :P
17:03:49 <beelsebob> so...
17:03:57 <idnar> oh, sweet
17:04:22 <byorgey> beelsebob: well, maybe we can =)
17:04:56 <gwern> @quote Pilgrim
17:04:57 <lambdabot> No quotes match.
17:04:58 <byorgey> it's not necessarily *un*interesting to use things as Branchies which also happen to be Monads.
17:05:00 <gwern> @quote Mark
17:05:01 <lambdabot> ghc says: internal error: scavenge_mark_stack: unimplemented/strange closure type -1368815400 @ 0x2aaaae6981f8
17:05:03 <gwern> @quote Mark
17:05:03 <lambdabot> JohnPeterson says: [1991] `Miranda' is a trademark of Research Software Ltd. `Haskell' is not a trademark of anyone.
17:05:12 <byorgey> it's nice to know that you're not using more power than you actually need.
17:05:19 <gwern> @remember MarkPilgrim "In the long run, the utility of all non-Free software approaches zero. All non-Free software is a dead end."
17:05:20 <lambdabot> Nice!
17:05:21 <beelsebob> byorgey: true true
17:05:24 <gwern> @flush
17:05:42 <byorgey> now all we need is some nice syntax sugar for using ifB
17:05:50 <beelsebob> byorgey: also, I can see tripple-wise ifB on ZipLists being really useful
17:06:06 <byorgey> beelsebob: indeed.
17:06:42 <byorgey> haha, someone was just asking the other day how to pick elements alternatingly from two lists
17:07:15 <byorgey> with a Branchy instance for ZipList you could just write   ifB (cycle [True, False]) l1 l2
17:07:26 <beelsebob> neat
17:07:29 <idnar> > let if' p a b = if p then a else b; ifA (ZipList bs) (ZipList xs) (ZipList ys) = ZipList $ zipWith3 if' bs xs ys in getZipList $ ifA (cycle [True, False]) (ZipList [1..]) (ZipList [2..])
17:07:29 <byorgey> well, except with some annoying ZipList constructors in there too
17:07:30 <lambdabot>   Couldn't match expected type `ZipList Bool'
17:07:38 <idnar> > let if' p a b = if p then a else b; ifA (ZipList bs) (ZipList xs) (ZipList ys) = ZipList $ zipWith3 if' bs xs ys in getZipList $ ifA (ZipList . cycle [True, False]) (ZipList [1..]) (ZipList [2..])
17:07:40 <lambdabot>   Couldn't match expected type `a -> [a1]'
17:07:42 <idnar> erf
17:07:44 <idnar> > let if' p a b = if p then a else b; ifA (ZipList bs) (ZipList xs) (ZipList ys) = ZipList $ zipWith3 if' bs xs ys in getZipList $ ifA (ZipList $ cycle [True, False]) (ZipList [1..]) (ZipList [2..])
17:07:46 <lambdabot>   [1,3,3,5,5,7,7,9,9,11,11,13,13,15,15,17,17,19,19,21,21,23,23,25,25,27,27,29...
17:08:01 <idnar> > let if' p a b = if p then a else b; ifA (ZipList bs) (ZipList xs) (ZipList ys) = ZipList $ zipWith3 if' bs xs ys in getZipList $ ifA (ZipList $ cycle [True, False]) (ZipList [1,1..]) (ZipList [2,2..])
17:08:03 <lambdabot>   [1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,...
17:08:12 <beelsebob> shiny as hell :)
17:08:37 <byorgey> that's a pretty complicated way to make (cycle [1,2]) =)
17:08:42 <idnar> haha
17:08:46 <beelsebob> haha
17:08:50 <byorgey> but I could see it being actually useful in some circumstances.
17:09:01 <byorgey> just have to think up some interesting examples.
```