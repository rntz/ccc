import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.Vect


---------- Renamings ----------
0 Renaming: List a -> List a -> Type
Renaming xs ys = All (\y => Elem y xs) ys
--Renaming xs ys = forall y. Elem y ys -> Elem y xs

lookup: All p xs -> Elem y xs -> p y
lookup (x :: xs) Here = x
lookup (x :: xs) (There p) = lookup xs p

tabulate: {xs: _} -> (forall y. Elem y xs -> p y) -> All p xs
tabulate {xs = []} r = []
tabulate {xs = (x :: xs)} r = r Here :: tabulate (r . There)

(++): All p as -> All p bs -> All p (as ++ bs)
[] ++ bs = bs
(x :: y) ++ bs = x :: y ++ bs

divide: {as: List _} -> All p (as ++ bs) -> (All p as, All p bs)
divide {as = []} xs = ([], xs)
divide {as = (a :: as)} (x :: xs) =
  let (xs', ys) = divide xs in
  (x :: xs', ys)


---------- Categories & concategories ----------
interface Cat obj (0 hom: obj -> obj -> Type) | hom where
  id : {a: obj} -> hom a a
  seq: {a, b, c: obj} -> hom a b -> hom b c -> hom a c

-- can I make this type-indexed instead of explicit lists?
interface Cat (List obj) hom => Concat obj hom | hom where
  para: {Γ₁, Γ₂, Δ₁, Δ₂ : List obj}
     -> hom Γ₁ Δ₁ -> hom Γ₂ Δ₂
     -> hom (Γ₁ ++ Γ₂) (Δ₁ ++ Δ₂)

interface Concat obj hom => Tuples obj hom | hom where
  tuple: List obj -> obj
  merge: {Γ: List obj} -> hom Γ [tuple Γ]
  split: {Γ: List obj} -> hom [tuple Γ] Γ

interface Concat obj hom => Cartesian obj hom | hom where
  rename: {Γ, Δ: List obj} -> Renaming Γ Δ -> hom Γ Δ
  -- fork: {Γ, Δ₁, Δ₂: List obj}
  --    -> hom Γ Δ₁ -> hom Γ Δ₂
  --    -> hom Γ (Δ₁ ++ Δ₂)
  -- fork f g = seq (renameBy (\l => l ++ l)) (para f g)
  -- renameBy: {Γ: List obj} -> (ρ: forall a. List a -> List a) -> hom Γ (ρ Γ)
  -- -- Need to show that (r Γ = r (vectList (Vect.fromList Γ))). ugh.
  -- renameBy r = rename (\v => r (vectList v))

interface Concat obj hom => Closed obj hom | hom where
  fun: List obj -> List obj -> obj
  curry: {Γ, Δ, Ω: List obj} -> hom (Γ ++ Δ) Ω -> hom Γ [fun Δ Ω]
  uncurry: {Γ, Δ, Ω: List obj} -> hom Γ [fun Δ Ω] -> hom (Γ ++ Δ) Ω


---------- Category of multi-in/output functions ----------
Vec: List Type -> Type
Vec = All id

MultiFun: List Type -> List Type -> Type
MultiFun as bs = Vec as -> Vec bs

Cat (List Type) MultiFun where
  id x = x
  seq f g x = g (f x)
Concat Type MultiFun where
  para f g v = let (a,b) = divide v in f a ++ g b
Tuples Type MultiFun where
  tuple = Vec
  merge v = [v]
  split [v] = v
Cartesian Type MultiFun where
  rename [] v = []
  rename (r :: rs) v = lookup v r :: rename {hom=MultiFun} rs v
Closed Type MultiFun where
  fun = MultiFun
  curry f g = [\d => f (g ++ d)]
  uncurry f gd = let (g,d) = divide gd in
                 let [h] = f g in
                 h d


---------- Concategory of string diagrams ----------
0 Symbol : Type
Symbol = (String, Int)

record Node where
  constructor MkNode
  name: String
  ins: List Symbol
  outs: List Symbol

record Gen a where
  constructor MkGen
  runGen: Int -> (Int, List Node, a)

gensym: String -> Gen Symbol
gensym name = MkGen$ \n => (n+1, [], (name, n))
emit: List Node -> Gen ()
emit nodes = MkGen$ \n => (n, nodes, ())

Functor Gen where
  map f d = MkGen$ \n => let (n, ns, x) = runGen d n in (n, ns, f x)

Applicative Gen where
  pure x = MkGen$ \n => (n, [], x)
  (d <*> d') = MkGen$ \n =>
               let (n, ns, x) = runGen d n in
               let (n, ns', y) = runGen d' n in
               (n, ns ++ ns', x y)

Monad Gen where
  (d >>= f) = MkGen$ \n =>
              let (n, ns, x) = runGen d n in
              let (n, ns', y) = runGen (f x) n in
              (n, ns ++ ns', y)

0 Many: Type -> List _ -> Type
Many a = All (const a)

0 Diagram: List () -> List () -> Type
Diagram x y = Many Symbol x -> Gen (Many Symbol y)

Cat (List ()) Diagram where id = pure; seq = (>=>)
Concat () Diagram where
  para f g zs = let (xs, ys) = divide zs in
                do x <- f xs; y <- g ys; pure (x ++ y)

Tuples () Diagram where
  tuple _ = ()
  merge {Γ=xs} = ?m
  split = ?s

Cartesian () Diagram where
  -- this is entirely pure computation. in fact, it's basically just list renaming
  -- on All.
  rename {Γ=xs} {Δ=[]} [] ins = pure []
  rename {Γ=xs} {Δ=(y :: ys)} (r :: rs) ins = ?asdf_1

-- interface Concat obj hom => Closed obj hom | hom where
--   fun: List obj -> List obj -> obj
--   curry: {Γ, Δ, Ω: List obj} -> hom (Γ ++ Δ) Ω -> hom Γ [fun Δ Ω]
--   uncurry: {Γ, Δ, Ω: List obj} -> hom Γ [fun Δ Ω] -> hom (Γ ++ Δ) Ω
