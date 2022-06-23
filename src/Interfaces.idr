module Interfaces

import Laws

public export
record Fix (f : Type -> Type) where
    constructor Fx
    unfix : f (Fix f)

public export
interface FixpointIsomorphism (f : Type -> Type) (t : Type) where
  generalize : t -> Fix f
  concretize : Fix f -> t

public export
record InitialAlgebra (f : Type -> Type) where
  constructor MkInit
  func : (LawfulFunctor f)
  prf : {a : Type} ->
        (alg : f a -> a) ->
        (h : Fix f -> a) ->
        (fix : f (Fix f)) ->
        h (Fx fix) = alg ((Prelude.map h) fix)

-- public export
-- interface FinalCoAlgebra (f : Type -> Type) where
--   fcHomomorphism :
--     (Functor f) =>
--     (coalg : c -> f c) ->
--     (h : c -> Fix f) ->
--     (fix : f (Fix f)) ->
--     (h . Fx) fix = (Prelude.map h . coalg) fix
