module Laws

public export
record MyFunctor (f : Type -> Type) where
  constructor MkFunctor
  fmap : {0 a, b : Type} -> (a -> b) -> f a -> f b

public export
record LawfulFunctor f where
  constructor MkLawful
  func : MyFunctor f
  mapIdent : {0 a : Type} -> (x: f a) -> func.fmap (Prelude.id) x = Prelude.id x
  mapCompose : (0 a, b, c : Type) -> { 0 g : b -> c } -> { 0 h : a -> b } ->
               (x: f a) -> func.fmap (g . h) x = (func.fmap g . func.fmap h) x

-- public export
-- interface (CoAlgebra f t, Algebra f t) => LawfulCata f t where
--   cata : (f a -> a) -> t -> a
--
--   cataIdent :
--     (xs : t) ->
--     (cata Interfaces.uncarry) xs = id xs
--
--
--   -- Example for lists:
--   -- concat : [[a]] -> [a]
--   -- sum    : [Int] -> Int
--   -- length : [a] -> Int
--   --
--   -- catFuse : [[a]] -> Int = [[a]] -> Int
--   -- catFuse = length . concat = sum . fmap length
--   cataFuse :
--     {0 alg : f t -> t } ->
--     {0 func : _ } ->
--     (y : t) ->
--     ({ 0 x : f t } -> (func . alg) x = (alg . map func) x) ->
--     (func . cata alg) y = (cata alg) y
--
--   -- given alg  : f a -> a
--   -- and   f    : f a -> g a
--   -- cata g . cata (embed . f) ≍ cata (g . f)
--   cataCompose :
--     { 0 eps : f t -> f t } ->
--     { 0 phi : f t -> t } ->
--     (x : t) ->
--     (cata phi . cata (Interfaces.uncarry . eps)) x = cata (phi . eps) x
--
--
--   -- given alg  : f a -> a
--   -- and   f    : f a -> g a
--   -- cata g . cata (embed . f) ≍ cata (g . f)
--   -- cata_compose :
--   --   { 0 g : Type -> Type} -> { 0 xs : t } ->
--   --   { 0 alg : f a -> a } -> { 0 nat : f a -> g a } ->
--   --   cata nat . ?help = cata (nat . ?help2) xs
--
