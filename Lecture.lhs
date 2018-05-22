> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE FlexibleInstances #-}

> module Lecture where
>
> import Data.Functor.Identity (Identity(..))

During the last weeks we have seen multiple monad instances and, thus, proved the monad laws several times.
Although proving the monad laws for a lot examples is good practice, it often follows the same scheme and it gets tedious to repeat the same process over and over again.
On top of that, for each monad we do not only need to prove the monad laws, we also need prove the corresponding laws to declare a functor and an applicative instance.
It would be nice if we could prove the laws once and for all --- or at least to reduce the costs.

In order to to prepare ourselves for the journey towards such a comfortable situation, let us recap the essence of the type class `Monad`.

~~~{.haskell}
class Applicative m => Monad m where
  return :: a -> m a
  (>>=) :: m a -> (a -> m b) -> m b
~~~

Remember also that we also demand that `m` has to be Functor (and an Applicative) as well.

~~~{.haskell}
class Functor f where
  fmap :: (a -> b) -> f a -> f b

class Functor f => Applicative f where

  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b
~~~

So, we can see that the `Monad` type class actually just adds the operation `(>>=)` on top of the structure that is available before.
Sometimes an alternative function to `(>>=)` is introduced to form the `Monad` type class.
This alternative arises, because the essence of a `Monad` is that we can reduce several layers of monad into just one layer.
Reducing layers is something that we cannot do with `Applicative`, because we can only transform values under the layer.
So, we define a function `join` that transforms a value that has to monadic layers into a value with just one monadic layer.

~~~{.haskell}
class Applicative m => MonadWithJoin m where
  return :: a -> m a
  join :: m (m a) -> m a
~~~

We can actually define the functionality of `(>>=)` in terms of `join`, that is, we do not loose expressiveness with this alternative definition.

~~~{.haskell}
(>>=) :: Monad m => m a -> (a -> m b) -> m b
mx >>= f = join (fmap f mx)
~~~

The nice thing about this alternative definition is that we can now actually see that is essential for our monad to also be an instance of the type class `Functor`; otherwise we could not use `fmap` and had not possibility to define this function.
From this observation we can also argue that we cannot define `fmap` using `join` --- because we would need `fmap` first!
Recall that we can actually define `fmap` using `(>>=)`.

~~~{.haskell}
fmap :: Monad m => (a -> b) -> m a -> m b
fmap f mx = mx >>= return . f
~~~

That is, the definition of `(>>=)` implies the functionality of `fmap`, whereas `join` really capture the new functionality we actually gain from the notion of a monad.

Obviously, the notion using `join` also needs to obey laws in order to capture the interplay with `fmap` and `return`.

~~~{.haskell}
join . pure = id                    (1)
join . fmap pure = id               (2)
join . fmap join = join . join      (3)
~~~

Law (1) says that adding a dummy layer and reducing it again does not change the value.
The same reasoning applies to law (2), with the difference that we lift the value `a` using `join` instead of lifting the whole monadic computation `m a`.
At last, law (3) captures the associativity of `join`, that is, given a value with at least three layers of monads, it does not matter if we smash the inner laters first and then the outer layers or the outer way around.

The idea we should take home from this little discourse is that we can turn a functor into a monad by adding the functionality of `return` and `join` that additionally obey the laws stated above.

> data AMonad f a = AReturn a
>                 | AJoin (AMonad f (AMonad f a))
>

The basic idea behind this data type definition is that, instead of actually computing new monadic values (by lifting via `return` or smashing via `join`), we keep track of all these operation by stacking them.
The stacking is reflected in the second constructor `join` that is defined in a recursive manner.

Now we can give the needed instance to make this data type a monad.

> instance Functor (AMonad f) where
>     fmap f (AReturn a) = AReturn (f a)
>     fmap f (AJoin mx)  = AJoin (fmap (fmap f) mx)
>
> instance Applicative (AMonad f) where
>     pure = AReturn
>     ff <*> fx = AJoin (fmap (\f -> fmap f fx) ff)
>
> instance Monad (AMonad f) where
>     return = AReturn
>     mx >>= f = AJoin (fmap f mx)

By now the attentive reader might notice that, although we advertised that we can turn any functor into a monad by the above data type, the type parameter `f` does not have a functor context, nor is it even used as a type constructor!
In particular, the type parameter `f` is just a dummy type argument that is propagated in the recursive call, but never actually used.

> data AMonadWithoutF a = Return a
>                       | Join (AMonadWithoutF (AMonadWithoutF a))
>
> instance Functor AMonadWithoutF where
>     fmap f (Return a) = Return (f a)
>     fmap f (Join mx)  = Join (fmap (fmap f) mx)
>
> instance Applicative AMonadWithoutF where
>     pure = Return
>     ff <*> fx = Join (fmap (\f -> fmap f fx) ff)
>
> instance Monad AMonadWithoutF where
>     return = Return
>     mx >>= f = Join (fmap f mx)

The same implementation is perfectly fine without the type parameter `f`, so we really did not use it in the definition before.

However, we actually do want to use `f` in the definition!
We want to turn a functor `f` into a monad with the data type, so, of course, `f` has to be used in a reasonable way somewhere in our data type definition.
The key idea is to let `Join` to keep track of the functor applied to the recursive usage of the type `AMonad`.
That is, instead of using `AMonad f (AMonad f a)` as argument to `AJoin`, we actually apply the functor `f` to the recursive usage of `AMonad f a`.

~~~{.haskell}
data AMonad f a = AReturn a
                | AJoin (f (AMonad f a))
~~~
After some renaming because of already used constructor names --- and actually using the names found in the literature, we end up with the following data type that is called \emph{free monad}.

> data Free f a = Pure a
>               | Impure (f (Free f a))

The free monad captures the essence of a monad into one single data type that we can then use to represent monads we already know and actually uses the fact that `f` is a functor!
In order to see the functor in action, we give the corresponding instances to make `Free f` a monad.

> instance Functor f => Functor (Free f) where
>     fmap f (Pure a) = Pure (f a)
>     fmap f (Impure fx) = Impure (fmap (fmap f) fx)
>
> instance Functor f => Applicative (Free f) where
>     pure = Pure
>     Pure f <*> fx = fmap f fx
>     Impure ff <*> fx = Impure (fmap (\ff' -> ff' <*> fx) ff)
>
> instance Functor f => Monad (Free f) where
>     return = Pure
>     Pure x >>= f = f x
>     Impure fx >>= f = Impure (fmap (\fx' -> fx' >>= f) fx)

Now we got our hands dirty to reduce the future work we have when defining monad instances, so it is time to see what we gained from all this work!
Therefor, we will take a look at the values we can construct using `Free`.

> valF1 :: Free f a
> valF1 = Pure undefined

Okay, maybe we need to use more concrete type to have some value we can actually work with.

> valFInt1 :: Free f ()
> valFInt1 = Pure ()

Can we also give a value using `Impure`?

> valFInt2 :: Free f ()
> valFInt2 = Impure x
>  where x :: f (Free f ())
>        x = undefined

Again, we need to use more concrete types in order to specify a value.
The advertisement promises us to turn functors into monads, so let us try the first functor that comes to mind: identity!

Now we can define values using `Pure` and `Impure`, because we know which functor to use in the latter case.

> testId1 :: Free Identity ()
> testId1 = Pure ()

> testId2 :: Free Identity ()
> testId2 = Impure (Identity testId1)

> testId3 :: Free Identity ()
> testId3 = Impure (Identity testId3)

We could to this all day, but all we gain is one `Identity` constructor more until we finally yield `()` (or some other value if we like to).
Now the question arises what kind of monad we have at hand here using `Free Identity ()`.
It is more expressive than `Identity` alone, because we have the additional `Impure` constructor that can add finite layers of `Identity`.
Is there a data type the definition above is isomorphic to?
That is, is there a type `t` such that we can give function `to :: t -> Free Identity ()` and `from :: Free Identity () -> t` that have the following property?

~~~{.haskell}
from . to = id
to . from = id
~~~

The answer is: yes, there is; and we even use it recently, when we talked about the lambda calculus.
We just defined Peano numbers!

> data Nat = Zero
>          | Succ Nat

We can even give a data type that is isomorphic for the more general case where we have an arbitrary value of type `a` inside the Free layer.
Instead of yielding `()` in the end (that is, a dummy value), we can add a type parameter that we yield in case of the first constructor.
As we already observed, we either have a value of type `a` directly (using `Pure`) or we \emph{delay} the computation with on layer of the functor `Identity` before we eventually yield a value of type `a`.

> testId4 :: Free Identity Int
> testId4 = Impure (Identity (Pure 42))

This functionality corresponds to the following data type (that has a suitable name).

> data Delay a = Now a
>              | Later (Delay a)
>  deriving Show

On top of that we can give the implementations of the functions `to` and `from` and show that the demanded laws hold.

> class Iso t1 t2 where
>     to :: t1 -> t2
>     from :: t2 -> t1

> instance Iso (Delay a) (Free Identity a) where
>     to   (Now x)                = Pure x
>     to   (Later dx)             = Impure (Identity (to dx))
>     from (Pure x)               = Now x
>     from (Impure (Identity fx)) = Later (from fx)

~~~{.haskell}
forall types (a :: *) and (fx :: Delay a), we want to show

to (from fx) = fx
    
By using induction on `fx`, we can reason as follows.
    
1) fx = Now x

   from (to (Now x))
 = from (Pure x)
 = Now x

2) fx = Later fx' and induction hypothesis `from (to fx') = fx'`

   from (to (Later fx')
 = from (Impure (Identity (to fx')))
 = Later (from (to fx'))
 = Later fx'


   forall types (a :: *) and (fx :: Free Identity a), we want to show

   to (from fx) = fx
    
   By using induction on `fx`, we can reason as follows.

   1) fx = Pure x

      to (from (Pure x))
    = to (Now x)
    = Pure x

   2) fx = Impure (Identity fx') and induction hypothesis `to (from fx') = fx'`

      to (from (Impure (Identity fx')))
    = to (Later (from fx'))
    = Impure (Identity (to (from fx')))
    = Impure Identity fx'
~~~

On top of that, we can observe that can also give and instance `Iso (Delay ()) Nat` that follows to laws, which implies that the example above using `Free Identity ()` is also isomorphic ot `Nat`.

Going back to the initial benefit of defining one data type to use for various kind of monad instances, we can use the functions `(>>=)` and `return` as we are used to and observe that they behave as expected for `Delay`.

> testDelay1 = testId4 >>= return . (+1)
> testDelay2 = testId4 >> testId2
>
> freeToDelay :: Free Identity a -> Delay a
> freeToDelay = from

~~~{.haskell}
ghci> freeToDelay (testDelay1)
Later (Now 43)
ghci> freeToDelay (testDelay2)
Later (Later (Now ()))
~~~
Observe that we combine all `Later` that we see in both arguments of `(>>=)` in the resulting expression.

The data type `Delay` is actually not one of the monads we are used to work with.
So now we want to take the other way and search for the functor to use in order to get a specific monad.

For example, we like to have a structure using `Free` that is isomorphic to `Maybe`.

> instance Iso (Maybe a) (Free MaybeFunctor a) where
>   to   (Just x)    = Pure x
>   to   Nothing     = Impure nothingMaybeFunctor
>   from (Pure x)    = Just x
>   from (Impure fx) = Nothing

We observe that we have no problem to map `Just` to `Pure`.
The problematic case is how to map `Nothing` into a value constructed by `Impure`.
Recall that `Maybe` --- in contrast to `Delay` discussed above --- is not a recursive type, it is a type that can hold a value of type `a` or yield a constant `Nothing` that does not have any polymorphic component.
So what we need is a functor that does not use its polymorphic type argument.
We have already seen such a functor in of the exercises when we were working with functors.

> data One a = One

The data type `One` is in a sense a type with just one value, but has --- in contrast to `()` --- an additional polymorphic argument, and, thus is a functor!

> instance Functor One where
>     fmap f One = One

By defining the synonym `MaybeFunctor` as `One`, we can define the `Nothing` case as follows.

> type MaybeFunctor = One

> nothingMaybeFunctor :: MaybeFunctor a
> nothingMaybeFunctor = One

Now we need to think about the backward direction where we map `Impure fx` to `Nothing` and make sure that `from` and `to` actually obey the corresponding laws, that is, that there is no other value that map in incorrectly.
Indeed, since the functor `One` has just one constructor, there is no other value that we can constructor using `Impure` than `Impure One`.

We leave it as an exercise to show that `to` and `from` indeed obey the laws stated above.
   
There are more monads to discover!

(1) Which functor do we need use to get the identity monad?
(2) Which monad do we get by using the functor `data Pair a = Pair a a` that is an special instance of `(,)`.

These are all questions that we will discuss in the exercises.
