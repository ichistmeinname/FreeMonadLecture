> {-# LANGUAGE RankNTypes #-}

> import Lecture

** Maybe and Free One

In class we discussed that we can transform the `Delay` monad into `Free Identity` and vice versa as well as the `Maybe` monad into `Free One`.

- Give an implementation for the instance `Iso (Delay a) (Free Identity a)`.
- Give an implementation for the instance `Iso (Maybe a) (Free One a)`.
- Prove that the round-trip property for `to` and `from` hold for both instances!

** Identity and Pair

First, we want to search for the functor in order to get an instantiation of `Free f a` that is isomorphic to `Identity a`.

- Give an implementation of the corresponding `Iso`-instance.
- Prove the round-trip property for `to` and `from`.

Second, we search for the monad (aka. data type that is an instance of `Monad`) that is isomorphic to `Free Pair a`, where `Pair` is defined as follows.

> data Pair a = Pair a a

- Give the functor instance for `Pair`.
- Implement the `Iso`-instance for `Free Pair a` and the corresponding monad.
- Prove the round-trip property.

** Folding

We are quite familiar with folding functions for lists and might still remember folding on trees from our Bachelors' course on `Advanced Programming`.

> data List a = Nil | Cons a (List a)
>
> foldList :: (a -> b -> b) -> b -> List a -> b
> foldList cons nil xs = case xs of
>                          Nil -> nil
>                          Cons y ys -> cons y (foldList cons nil ys)

> data Tree a = Empty | Leaf a | Branch (Tree a) (Tree a)
>
> foldTree :: (b -> b -> b) -> (a -> b) -> b -> Tree a -> b
> foldTree branch leaf empty tree = case tree of
>                                      Empty -> empty
>                                      Leaf x -> leaf x
>                                      Branch t1 t2 -> branch (foldTree branch leaf empty t1) (foldTree branch leaf empty t2)

The naming was chosen to make the essense of a folding function more clear: for each constructor of the data type, the folding function takes an argument that can transform the constructor into a value of type `b`.
That is, each concrete constructor is then replaced by its abstract interpretation.

- Implement a folding function `foldFree` for the data type `Free f a`.

> foldFree = undefined

- All previous implementation that transform `Free f a` into a concrete monad can now be implemented using `foldFree`. Just do it!
- We can even observe a special case. If the target type `b` is a monad, we can define a function `induce` that takes a so-called natural transformation and transforms the free value into a monad. Now use `induce` to define the transformations function one last time.

> type Natural f m a = forall a. f a -> m a
>
> induce :: Monad m => Natural f m a -> Free f a -> m a
> induce ntf fx = foldFree undefined undefined fx
    
- Explain why it is not enough to quantify the type variable `a` in the type signature of `induce` at the beginning --- as we normally do, but quantify over all type variables `a` directly in the function type of the first arugment.

** Interpreters

We have used arithmetic expression as example for nearly all topics introduced in the lecture. Free monads is no exception.

One key essence of using a `Free` is that we have an AST-like representatin of a monadic program. The computations are not actually performed, but stacked via the `Impure`-constructor. That is, when we represent a monadic program using `Free` we can implement various interpreters for this program.

Here, we want to talke arithmetic expressions, again. In order to have a monadic program with arithmetic expression, we define a calculator-like DSL.

> data Calc next = Add next
>                | Num Int next
>                | Clear next
>                | End

The type parameter `next` is used to chain commands and th operation `End` marks the end of such a chain (similar to pushing the "="-button on most common calculators). 

With this DSL on top of `Free` we can define programs as follows.

    > program1 :: Free Calc ()
    > program1 = do
    >   num 1
    >   num 2
    >   add
    >   end
    
    > program2 :: Free Calc ()
    > program2 = do
    >   num 1
    >   num 2
    >   add
    >   clear
    >   num 42
    >   end

Using `foldFree` we can define intepretations of calculator-programs.

- Define an interpreter that transforms the `Free`-based program into our well-known `Expr` data type.

> data Expr = Number Int
>           | Expr :+: Expr
>           | Expr :*: Expr
>  deriving Show
> freeCalcToExpr :: Free Calc () -> Maybe Expr
> freeCalcToExpr fx = undefined

- Define an interpreter that evaluate `Free Calc ()` programs directly.

> evalCalc :: Free Calc () -> Maybe Int
> evalCalc fx = undefined

- Last but not least, define an interpreter to pretty print `Free Calc` programs.

> freeCalcToString :: Free Calc () -> String
> freeCalcToString fx = undefined
