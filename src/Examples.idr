module Examples

import Interfaces
import Schemes
import Implementations
import Laws

%hide Prelude.Stream.(::)

public export
data NatF : Type -> Type where
  ZeroF : NatF r
  SuccF : r -> NatF r

mapNat : (a -> b) -> NatF a -> NatF b
mapNat f (ZeroF {r = a}) = ZeroF {r = b}
mapNat f (SuccF {r = a} x) = SuccF {r = b} (f x)


public export
implementation Functor NatF where
  map = mapNat

NatFunctor : MyFunctor NatF
NatFunctor = MkFunctor mapNat

lemma : (0 a, b, c : Type) -> {0 g : b -> c} -> {0 h : a -> b} ->
        (x : NatF a) -> Equal {a = NatF c} {b = NatF c}
        (fmap NatFunctor {b = c} {a = a} (\x : a => g (h x)) x)
        (fmap NatFunctor {b = c} {a = b} g (fmap NatFunctor {b = b} {a = a} h x))
lemma _ _ _ (ZeroF {r = a}) = Refl
lemma _ _ _ (SuccF {r = a} x) = Refl

lemmaId : {0 a : Type} -> (x : NatF a) -> Equal (Examples.mapNat (Prelude.id {a = a}) x ) x
lemmaId (ZeroF {r = a}) = Refl
lemmaId (SuccF {r = a} x) = Refl


law : LawfulFunctor NatF
law = MkLawful
  { func = NatFunctor
  , mapIdent = lemmaId
  , mapCompose = lemma
  }


public export
Nat' : Type
Nat' = Fix NatF

implementation FixpointIsomorphism NatF Nat where
  concretize (Fx ZeroF) = Z
  concretize (Fx (SuccF n)) = S $ concretize n

  generalize Z = Fx ZeroF
  generalize (S n) = Fx $ SuccF (generalize n)

cata : MyFunctor f -> (f a -> a) -> Fix f -> a
cata func alg = alg . func.fmap (cata func alg) . unfix

test : {0 a : Type} -> (alg : NatF a -> a) -> cata NatFunctor alg (Fx ZeroF) = alg ZeroF
test alg = Refl

lemmaPrf : (alg : (NatF a -> a)) -> (h : (Fix NatF -> a)) -> (fix : NatF (Fix NatF)) -> h (Fx fix) = alg (mapNat h fix)
lemmaPrf alg h ZeroF = ?huh -- `trans` test {a} alg
lemmaPrf alg h (SuccF x) = ?lemmaPrf_rhs_1

natFIsInitial : InitialAlgebra NatF
natFIsInitial = MkInit
  { func = law
  , prf = ?heh
  }

  -- iaHomomorphism
  -- alg h ZeroF = ?ia_0
  --   -- rewrite cong alg (temp { a = a } h) in ?ia_0
  -- iaHomomorphism alg h (SuccF x) = ?ia_1

public export
zero : Nat'
zero = generalize Z

public export
succ : Nat' -> Nat'
succ = generalize . S . concretize

public export
List' : Type -> Type
List' a = Fix (ListF a)

public export
implementation {a: _} -> FixpointIsomorphism (ListF a) (List a) where
  concretize (Fx NilF) = Nil
  concretize (Fx (ConsF x xs)) = x :: (concretize xs)

  generalize Nil = Fx NilF
  generalize (x::xs) = Fx $ x `ConsF` (generalize xs)

public export
nil : {a:_} -> List' a
nil = generalize n
  where
    n : List a
    n = Nil

public export
cons : {a:_} -> a -> List' a -> List' a
cons x = generalize . (::) x . concretize

-- public export
-- data TreeF : (0 _ : Type) -> Type -> Type where
--   EmptyF : TreeF a r
--   LeafF : a -> TreeF a r
--   NodeF : r -> r -> TreeF a r
--
-- public export
-- Tree : Type -> Type
-- Tree a = Fix (TreeF a)
--
-- public export
-- empty : Tree a
-- empty = Fx EmptyF
--
-- public export
-- leaf : a -> Tree a
-- leaf = Fx . LeafF
--
-- public export
-- node : Tree a -> Tree a -> Tree a
-- node l r = Fx $ NodeF l r
--
-- implementation Functor (TreeF a) where
--   map f (NodeF t1 t2) = NodeF (f t1) (f t2)
--   map _ EmptyF = EmptyF
--   map _ (LeafF a) = LeafF a

-- Cata Examples

-- public export
-- natsum : Nat -> Int
-- natsum = cata alg
--   where
--     alg : NatF Int -> Int
--     alg ZeroF = 0
--     alg (SuccF n) = n + 1
--
-- public export
-- listFoldr :
--   {0 a : _} -> {0 b : _} ->
--   (a -> b -> b) -> b -> List a -> b
-- listFoldr f z = cata alg
--   where
--     alg : (ListF a b) -> b
--     alg NilF = z
--     alg (ConsF x xs) = f x xs
--
-- public export
-- listFoldl :
--   {0 a : _} -> {0 b : _} ->
--   (b -> a -> b) -> b -> List a -> b
-- listFoldl f z list = cata alg list $ z
--   where
--     alg : (ListF a (b -> b)) -> (b -> b)
--     alg NilF = id
--     alg (ConsF x xs) = xs . \y => f y x
--
--
-- -- Ana Examples
--
-- public export
-- nat : Int -> Nat
-- nat = ana coalg
--   where
--     coalg : Int -> NatF Int
--     coalg n = if n <= 0 then ZeroF else SuccF (n - 1)
--
-- public export
-- replicate : {0 a : _} -> Int -> a -> List a
-- replicate n x = ana coalg n
--  where
--    coalg : Int -> ListF a Int
--    coalg n = if n <= 0 then NilF else ConsF x (n - 1)
--
-- -- Para Examples
-- public export
-- natpred : Nat -> Nat
-- natpred = para alg
--   where
--     alg : NatF (Nat, _) -> Nat
--     alg ZeroF = zero
--     alg (SuccF (n, _)) = n
--
-- public export
-- drop : {0 a : _} -> Nat -> List a -> List a
-- drop nat list = para alg list nat
--   where
--     alg : ListF a (List a, Nat -> List a) -> (Nat -> List a)
--     alg NilF = const nil
--     alg (ConsF v (xs, r)) = \case
--       (Fx ZeroF) => cons v xs
--       (Fx (SuccF n)) => r n
--
-- -- Helper for window
-- public export
-- take : {0 a : _} -> Nat -> List a -> List a
-- take num xs = fst (listFoldl f (id, num) xs) nil
--   where
--     f : (List a -> List a, Nat) -> a -> (List a -> List a, Nat)
--     f (t, Fx ZeroF) _ = (t, zero)
--     f (t, Fx (SuccF n)) x = (t . \xs => cons x xs, n)
--
-- public export
-- window : {0 a : _} -> Nat -> List a -> List (List a)
-- window n = para alg
--   where
--     alg : ListF a (List a, List (List a)) -> List (List a)
--     alg NilF = nil
--     alg (ConsF x (xs, r)) = cons (take n (cons x xs)) r
--
-- -- Hylo examples
-- public export
-- implementation Functor List where
--   map f = cata alg
--     where
--       alg : ListF a (List b) -> List b
--       alg NilF = nil
--       alg (ConsF x r) = cons (f x) r
--
-- public export
-- implementation Functor Tree where
--   map f = cata alg
--     where
--       alg : TreeF a (Tree b) -> Tree b
--       alg EmptyF = empty
--       alg (LeafF x) = leaf . f $ x
--       alg (NodeF x y) = node x y
--
-- public export
-- splitAt : Nat -> List a -> (List a, List a)
-- splitAt n xs = (take n xs, drop n xs)
--
-- public export
-- listLength : List a -> Nat
-- listLength = listFoldr (\_ => succ) zero
--
-- public export
-- mergeList : Ord a => List a -> List a -> List a
-- mergeList = curry $ ana coalg
--   where
--     coalg : (List a, List a) -> ListF a (List a, List a)
--     coalg (Fx NilF, Fx NilF) = NilF
--     coalg (Fx (ConsF x xs), Fx NilF) = ConsF x (xs, nil)
--     coalg (Fx NilF, Fx (ConsF x xs)) = ConsF x (xs, nil)
--     coalg (Fx (ConsF x xs), Fx (ConsF y ys)) =
--       if compare x y /= GT
--          then ConsF x (xs, cons y ys)
--          else ConsF y (cons x xs, ys)
--
-- public export
-- listToTreeCoalg : List a -> TreeF a (List a)
-- listToTreeCoalg (Fx NilF) = EmptyF
-- listToTreeCoalg (Fx (ConsF x (Fx NilF))) = LeafF x
-- listToTreeCoalg xs =
--   let (l,r) = splitAt (nat $ natsum (listLength xs) `div` 2) xs
--   in NodeF l r
--
-- public export
-- listToTree : List a -> Tree a
-- listToTree = ana listToTreeCoalg
--
-- public export
-- mergeTreeAlg : Ord a => TreeF a (List a) -> List a
-- mergeTreeAlg EmptyF = nil
-- mergeTreeAlg (LeafF c) = cons c nil
-- mergeTreeAlg (NodeF l r) = mergeList l r
--
-- public export
-- mergeTree : Ord a => Tree a -> List a
-- mergeTree = cata mergeTreeAlg
--
-- public export
-- mergeSort : Ord a => List a -> List a
-- mergeSort list = hylo mergeTreeAlg listToTreeCoalg list
