module Schemes

import Interfaces

-- public export
-- cata :
--   {0 f : _} -> {0 t : _} ->
--   (Algebra f t) =>
--   (f a -> a) -> t -> a
-- cata algebra x = algebra . map (cata algebra) . carry $ x
--
-- public export
-- ana :
--   {0 f : _} -> {0 t : _} ->
--   (CoAlgebra f t) =>
--   (a -> f a) -> a -> t
-- ana coalgebra x = uncarry . map (ana coalgebra) . coalgebra $ x
--
-- public export
-- para :
--   {0 f : _} -> {0 t : _} ->
--   (Algebra f t, Functor f) =>
--   (f (t, a) -> a) -> t -> a
-- para alg = alg . map (\x => (x, para alg x)) . carry
--
-- public export
-- hylo : Functor f => (f b -> b) -> (a -> f a) -> a -> b
-- hylo alg coalg x = alg . map (hylo alg coalg) . coalg $ x
