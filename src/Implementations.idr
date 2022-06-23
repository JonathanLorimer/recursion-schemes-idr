module Implementations

import Interfaces
import Schemes
import Laws

public export
data ListF : (0 _ : Type) -> Type -> Type where
  NilF : ListF a r
  ConsF : a -> r -> ListF a r

public export
implementation Functor (ListF a) where
  map f NilF = NilF
  map f (ConsF x xs) = ConsF x (f xs)

listfMapIdent : (x: ListF b a) -> map Prelude.id x = Prelude.id x
listfMapIdent NilF = Refl
listfMapIdent (ConsF x y) = Refl

listfMapCompose : { 0 g : b -> c } -> { 0 h : a -> b } ->
                  (x: ListF r a) -> map (g . h) x = (map g . map h) x
listfMapCompose NilF = Refl
listfMapCompose (ConsF x y) = Refl

implementation LawfulFunctor (ListF a) where
  mapIdent = listfMapIdent
  mapCompose = listfMapCompose

listMapIdent : (x: List a) -> map Prelude.id x = Prelude.id x
listMapIdent [] = Refl
listMapIdent (x :: xs) =
  let lemma = listMapIdent xs in
  rewrite lemma in
  Refl

listMapCompose : { 0 g : b -> c } -> { 0 h : a -> b } ->
                  (x: List a) -> map (g . h) x = (map g . map h) x

implementation LawfulFunctor List where
  mapIdent = listMapIdent
  mapCompose = listMapCompose

-- listCataIdent : (xs : List a) -> (Schemes.cata {f = ListF a} Interfaces.uncarry) xs = id xs
-- listCataIdent [] = Refl
-- listCataIdent (x :: xs) =
--   let identXs = listCataIdent xs in
--   rewrite identXs in
--   Refl
--
-- lemma : (phi : _) -> (x : ListF a (List a)) -> map (Schemes.cata {f = ListF a} phi) (carry (uncarry x)) = x
-- lemma phi NilF = Refl
-- lemma phi (ConsF x y) =
--   let lemma': (phi (map (cata phi) (carry y)) = y)
--       lemma' = ?lemma' in
--   ?lemma_rhs_1
--
-- implementation LawfulCata (ListF a) (List a) where
--   cata = Schemes.cata
--
--   cataIdent = listCataIdent
--
--   cataFuse {alg} [] assump =
--     let assump' = assump { x = NilF } in
--     rewrite assump' in
--     Refl
--   cataFuse {alg} {func} (x :: xs) assump =
--     let assump' = assump { x = ConsF x (alg (map (Schemes.cata alg) (carry xs))) }
--         lemma = cataFuse {alg = alg} {func = func} xs assump
--         cong' = cong (alg . ConsF x) lemma in
--     rewrite assump' in
--     rewrite cong' in
--     Refl
--
--   cataCompose [] = ?cataCompose_0
--   cataCompose (x :: xs) = ?cataCompose_1
--
