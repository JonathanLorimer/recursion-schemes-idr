module Interfaces

public export
record Fix (f : Type -> Type) where
    constructor Fx
    unfix : f (Fix f)

public export
interface FixpointIsomorphism (f : Type -> Type) (t : Type) where
  generalize : t -> Fix f
  concretize : Fix f -> t

public export
interface InitialAlgebra (f : Type -> Type) where
  iaHomomorphism :
    (Functor f) =>
    (alg : f a -> a) ->
    (h : Fix f -> a) ->
    (fix : f (Fix f)) ->
    (x : Fix f) ->
    (h . Fx) fix = (alg . map h) fix

-- public export
-- interface (Functor f) => CoAlgebra (0 f : Type -> Type) (0 t : Type) where
--   uncarry : f t -> t
--
-- public export
-- interface (Functor f) => Algebra (0 f : Type -> Type) (0 t : Type) where
--   carry : t -> f t
--

