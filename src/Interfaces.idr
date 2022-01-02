module Interfaces

public export
interface (Functor f) => Corecursive (0 f : Type -> Type) (0 t : Type) where
  embed : f t -> t

public export
interface (Functor f) => Recursive (0 f : Type -> Type) (0 t : Type) where
  project : t -> f t
