interface Cat obj (0 hom: obj -> obj -> Type) | hom where
  id : {a: obj} -> hom a a
  seq: {a, b, c: obj} -> hom a b -> hom b c -> hom a c

-- "Contexts"
Set a = a -> Type
single: a -> Set a
single a b = a = b
(++): Set a -> Set a -> Set a
(++) f g x = Either (f x) (g x)

interface Cat (Set obj) hom => Concat obj hom | hom where
  para: {Γ₁, Γ₂, Δ₁, Δ₂ : Set obj}
     -> hom Γ₁ Δ₁ -> hom Γ₂ Δ₂ 
     -> hom (Γ₁ ++ Γ₂) (Δ₁ ++ Δ₂)
     
interface Concat obj hom => Cartesian obj hom | hom where
  product: Set obj -> obj
  rename: {Γ: Set obj}
       -> (ρ: forall a. Set a -> Set a)
       -> hom Γ (ρ Γ)
  merge: {Γ: Set obj} -> hom Γ (single (product Γ))
  split: {Γ: Set obj} -> hom (single (product Γ)) Γ
  fork: {Γ, Δ₁, Δ₂: Set obj} 
     -> hom Γ Δ₁ -> hom Γ Δ₂
     -> hom Γ (Δ₁ ++ Δ₂)
  fork f g = seq (rename (\l => l ++ l)) (para f g)
  
interface Concat obj hom => Closed obj hom | hom where
  fun: Set obj -> Set obj -> obj
  curry: {Γ, Δ, Ω: Set obj} -> hom (Γ ++ Δ) Ω -> hom Γ (single (fun Δ Ω))
  uncurry: {Γ, Δ, Ω: Set obj} -> hom Γ (single (fun Δ Ω)) -> hom (Γ ++ Δ) Ω


---------- The category of multi-in/output functions ----------
Vect: Set Type -> Type
Vect ctx = (a : Type) -> ctx a -> a

MultiFun: Set Type -> Set Type -> Type
MultiFun as bs = Vect as -> Vect bs

Cat (Set Type) MultiFun where
  id x = x
  seq f g x = g (f x)
Concat Type MultiFun where
  para f g v _ (Left y) = f (\a,x => v _ (Left x)) _ y
  para f g v _ (Right y) = g (\a,x => v _ (Right x)) _ y
Cartesian Type MultiFun where
  product = Vect
  rename r v _ x = ?renamea
  split = ?splita
  merge = ?mergea
  fork = ?forka
