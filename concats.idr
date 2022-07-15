import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.Vect


---------- Renamings ----------
0 Renaming: List a -> List a -> Type
Renaming xs ys = All (\y => Elem y xs) ys
--Renaming xs ys = forall y. Elem y ys -> Elem y xs

allElem: All p xs -> Elem y xs -> p y
allElem (x :: xs) Here = x
allElem (x :: xs) (There p) = allElem xs p

elemAll: {xs: _} -> (forall y. Elem y xs -> p y) -> All p xs
elemAll {xs = []} r = []
elemAll {xs = (x :: xs)} r = r Here :: elemAll (r . There)

-- toAll: (f: forall a. List a -> List a) -> {xs : List a} -> All (\y => Elem y xs) (f xs)
-- toAll f {xs} = ?ally

-- toRename: (f: forall a. List a -> List a) -> {xs : List a} -> Renaming xs (f xs)
-- toRename f = allToRename (toAll f)


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


---------- The category of multi-in/output functions ----------
Vec: List Type -> Type
Vec = All id

MultiFun: List Type -> List Type -> Type
MultiFun as bs = Vec as -> Vec bs

unappend: {as: List Type} -> Vec (as ++ bs) -> (Vec as, Vec bs)
unappend {as = []} xs = ([], xs)
unappend {as = (a :: as)} (x :: xs) =
  let (xs', ys) = unappend xs in
  (x :: xs', ys)

(++): Vec as -> Vec bs -> Vec (as ++ bs)
[] ++ bs = bs
(x :: y) ++ bs = x :: y ++ bs

Cat (List Type) MultiFun where
  id x = x
  seq f g x = g (f x)
Concat Type MultiFun where
  para f g v = let (a,b) = unappend v in f a ++ g b
Tuples Type MultiFun where
  tuple = Vec
  merge v = [v]
  split [v] = v
Cartesian Type MultiFun where
  rename [] v = []
  rename (r :: rs) v = allElem v r :: rename {hom=MultiFun} rs v
Closed Type MultiFun where
  fun = MultiFun
  curry f g = [\d => f (g ++ d)]
  uncurry f gd = let (g,d) = unappend gd in
                 let [h] = f g in
                 h d
