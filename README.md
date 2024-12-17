*The contents of this repository have been merged into <https://github.com/kztk-m/EbU>. This repository will no longer be maintained.*


Examples for Embedding by Unembedding
=====================================

This is a collection of proof-of-concept application examples of the [embedding-by-unembedding](https://github.com/kztk-m/EbU). 

* `AppLens.hs` - extracts of code for a simple lens language from the ["Embedding by Unembedding" paper](https://doi.org/10.1145/3607830).
* `CTS.hs` - the cache transfer variant of the incremental lambda calculus.
* `ELens.hs` - bidirectional transformations
* `STLC.hs` - example usage of the framework on the simply typed lambda calc. (This is a good file to start in to understand the Embedding by Unembedding technique)
* `ILC.hs` - the incremental lambda calculus (<https://inc-lc.github.io/>)

The code is supposed to be used in REPL, by:

```
cabal repl
```

Then, as shown below, you can experiment with code in each of the files by focussing on them with `:l`.

Usage Examples: `ELens.hs`
--------------------------

```haskell
$ cabal repl
ghci> :l Unembedding.Examples.ELens
[1 of 1] Compiling Unembedding.Examples.ELens
Ok, one module loaded.
ghci> :t linesB
linesB :: HOBiT e => e String -> e [String]
ghci> :t runHOBiT linesB
runHOBiT linesB :: Lens String [String]
ghci> let l = runHOBiT linesB
ghci> :t l
l :: Lens String [String]
ghci> get l "A\nB"
Right ["A","B"]
ghci> put l "A\nB" ["a","b"]
Right "a\nb"
ghci> put l "A\nB" ["a","b","c"]
Right "a\nb\nc"
ghci> put l "A\nB" ["a"]
Right "a"
ghci> get l "A\nB\n"
Right ["A","B"]
ghci> put l "A\nB\n" ["a", "b"]
Right "a\nb\n"
ghci> put l "A\nB\n" ["a", "b", "c"]
Right "a\nb\nc\n"
ghci> put l "A\nB\n" ["a"]
Right "a\n"
```

Usage Examples: `CTS.hs`
------------------------

```haskell
$ cabal repl
ghci> :l Unembedding.Examples.CTS
[1 of 1] Compiling Unembedding.Examples.CTS
Ok, one module loaded.
ghci> :t cartesianRecreation
cartesianRecreation
  :: (CTSSeq exp, Diff a, Diff b) =>
     exp (Seq a) -> exp (Seq b) -> exp (Seq (a, b))
ghci>
ghci> :t runCTS
runCTS
  :: Diff a => CTS '[a] b -> a -> (b, Interact (Delta a) (Delta b))
ghci> :t UE.runOpen (\z -> cartesianRecreation (fst_ z) (snd_ z))
UE.runOpen (\z -> cartesianRecreation (fst_ z) (snd_ z))
  :: (Variables sem, CTSSeq (EnvI sem), Diff a, Diff b) =>
     sem '[(Seq a, Seq b)] (Seq (a, b))
ghci> :t caInc
caInc
  :: (Diff a, Diff b) =>
     (Seq a, Seq b)
     -> (Seq (a, b),
         Interact (Delta (Seq a, Seq b)) (Delta (Seq (a, b))))
ghci> let (res, i) = caInc (S.fromList [1,2,3::Int], S.fromList [4,5,6::Int])
ghci> res
fromList [(1,4),(1,5),(1,6),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6)]
ghci> let (db1, i1) = runInteract i (PairDelta (DSeq [Ins 0 42]) mempty)
ghci> db1
DSeq [Ins 0 (42,6),Ins 0 (42,5),Ins 0 (42,4)]
ghci> res /+ db1
fromList [(42,4),(42,5),(42,6),(1,4),(1,5),(1,6),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6)]
ghci> let (db1', i1') = runInteract i (PairDelta mempty (DSeq [Ins 0 42]))
ghci> db1'
DSeq [Ins 0 (1,42),Ins 4 (2,42),Ins 8 (3,42)]
ghci> res /+ db1'
fromList [(1,42),(1,4),(1,5),(1,6),(2,42),(2,4),(2,5),(2,6),(3,42),(3,4),(3,5),(3,6)]
```
