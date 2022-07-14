import Data.List
import Data.List.Quantifiers

interface Cat obj (0 hom: obj -> obj -> Type) | hom where
  id : {a: obj} -> hom a a
  seq: {a, b, c: obj} -> hom a b -> hom b c -> hom a c

-- can I make this type-indexed instead of explicit lists?
interface Cat (List obj) hom => Concat obj hom | hom where
  para: {Γ₁, Γ₂, Δ₁, Δ₂ : List obj}
     -> hom Γ₁ Δ₁ -> hom Γ₂ Δ₂ 
     -> hom (Γ₁ ++ Γ₂) (Δ₁ ++ Δ₂)
     
interface Concat obj hom => Cartesian obj hom | hom where
  product: List obj -> obj
  rename: {Γ: List obj}
       -> (ρ: forall a. List a -> List a) -- FIXME: wrong
       -> hom Γ (ρ Γ)
  merge: {Γ: List obj} -> hom Γ [product Γ]
  split: {Γ: List obj} -> hom [product Γ] Γ
  fork: {Γ, Δ₁, Δ₂: List obj} 
     -> hom Γ Δ₁ -> hom Γ Δ₂
     -> hom Γ (Δ₁ ++ Δ₂)
  fork f g = seq (rename (\l => l ++ l)) (para f g)
  
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
Cartesian Type MultiFun where
  product = Vec
  split [v] = v
  merge v = [v]
  rename r [] = ?renamea_0
  rename r (x :: y) = ?renamea_1
  fork = ?forka
