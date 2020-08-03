{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
module PickleSOP ( 
    module PickleSOP
) where

import Text.XML.HXT.Core
import Generics.SOP
import Text.XML.HXT.Arrow.Pickle.Xml (xpElemQN, mchoice, throwMsg)
import Text.XML.HXT.Arrow.Pickle.Schema (scSeq, scAlt, scNull)
import Data.Coerce (Coercible, coerce)
import Control.Applicative (Applicative(liftA2))

type SOP' f a = NS (NP f) a

xpSOP' :: Generic a => PU a -> PU (SOP' I (Code a))
xpSOP' = xpWrap (unSOP . from , to . SOP)

xpSOP :: Generic a => PU a -> PU (SOP I (Code a))
xpSOP = xpWrap (from , to)

xpSOP'' :: Generic a => PU a -> PU (SOP' I (Code a))
xpSOP'' = coerce . xpSOP

-- xpNewtype :: Coercible a x => PU x -> PU a
xpNewtype :: IsNewtype a x => PU x -> PU a
xpNewtype = coerce

liftCoercion :: Coercible (f a) (f b) => (a -> b) -> f a -> f b
liftCoercion _ = coerce

pickleDeep :: NP (NP PU) a -> PU (NS (NP I) a)
pickleDeep Nil = xpNull
pickleDeep (x :* xs) = xpOr (pickleMany x) $ pickleDeep xs

pickleMany :: NP PU x -> PU (NP I x)
pickleMany Nil = xpLift Nil
pickleMany (x :* xs) = xpCons (xpNewtype x) $ pickleMany xs
-- pickleMany (x :* xs) = xpWrap (_ , _) $ xpPair x $ pickleMany xs

pickleMany' :: NP PU x -> PU (NP I x)
pickleMany' = hfoldr (xpCons . xpNewtype) xpOne

-- | Convert a product of picklers to a pickler of a sum
pickleSum :: NP (PU :.: f) a -> PU (NS f a)
pickleSum Nil = xpNull
pickleSum (Comp x :* xs) = xpOr x $ pickleSum xs

pickleSum' :: NP (PU :.: f) a -> PU (NS f a)
pickleSum' = unComp . hfoldr' (liftComp2 xpOr) (Comp xpNull)
  where
    -- liftComp f = unComp . f . Comp 
    -- liftComp2 :: (:.:) PU f (g x) -> (:.:) PU f (g x) -> (:.:) PU f (g x)
 -- f (g p) -> f (g p) -> f (g p)
    -- liftComp2 f x y = Comp $ f (unComp x) (unComp y)
    liftComp2 f x y = Comp $ f (unComp x) (unComp y)

pickleSum'' :: forall f a. NP (PU :.: f) a -> PU (NS f a)
pickleSum'' = hfoldr (xpOr . unComp) xpNull
-- pickleSum'' = (coerce $ hfoldr' @f @(PU :.: NS f) @a) xpOr xpNull

pickleSum''' :: SListI xs => NP (PU :.: f) xs -> PU (NS f xs)
pickleSum''' picklers = xpAlt hindex $ fmap sequencePU z
  where z = apInjs_NP picklers

sequencePU :: NS (PU :.: f) xs -> PU (NS f xs)
sequencePU = error "not implemented"

-- pickleSum' :: SListI a => NP (PU :.: f) a -> PU (NS f a)
-- pickleSum' = undefined . hmap (_ . fn . xpOr . unComp)

-- From pointless-fun
(~>) :: (a -> b1) -> (b2 -> c) -> (b1 -> b2) -> a -> c
(f ~> g) x = g . x .f

infixr 6 ~>

hfoldr :: forall f r g xss. (forall x xs. f x -> r (g xs) -> r (g (x : xs))) -> r (g '[]) -> NP f xss -> r (g xss)
hfoldr f = Comp ~> id ~> unComp $ hfoldr' $ id ~> unComp ~> Comp $ f
-- hfoldr = (id ~> unComp ~> Comp ) ~> Comp ~> id ~> unComp $ hfoldr' @f @(r :.: g)
-- hfoldr f z = unComp . hfoldr' (\x -> Comp . f x . unComp) (Comp z)
-- hfoldr f z = go where
--     go :: forall z. NP f z -> r (g z)
--     go Nil = z
--     go (x :* xs) = f x $ go xs
-- hfoldr = coerce $ hfoldr' @(r :.: g f) @r @xss



hfoldr' :: forall f r xss. (forall x xs. f x -> r xs -> r (x : xs)) -> r '[] -> NP f xss -> r xss
hfoldr' f z = go where
    go :: forall z. NP f z -> r z
    go Nil = z
    go (x :* xs) = f x $ go xs

pickleDeep2 :: SListI a => NP (NP PU) a -> PU (NS (NP I) a)
pickleDeep2 = pickleSum . hmap (Comp . pickleMany)

autoProduct :: All XmlPickler a => PU (NP I a)
autoProduct = unComp $ cpara_SList proxyXP (Comp xpOne) (Comp . xpCons (xpNewtype xpickle) . unComp)

-- |
autoPickle :: All2 XmlPickler a => NP (K QName) a -> PU (SOP' I a)
autoPickle Nil = xpNull
autoPickle (K x :* xs) = xpOr (xpElemQN x autoProduct) $ autoPickle xs
-- autoPickle :: SListI2 a => NP (K QName) a -> PU (SOP' I a)
-- autoPickle = _ . cpara_SList proxyXP _ _
-- autoPickle = undefined . hliftA2 (\(Comp x) (K name) -> K $ xpElemQN name (x)) (hcpure proxyXP1 $ fixComplaints $ Comp autoProduct)
-- autoPickle pb = xpAlt hindex _

-- Same thing without explicit recursion
autoPickle' :: forall a. All2 XmlPickler a => NP (K QName) a -> PU (SOP I a)
autoPickle' names = coerce pickleFull
  where
    allPicklers :: POP PU a
    allPicklers = hcpure proxyXP xpickle
    pickleContents :: NP (PU :.: NP I) a
    pickleContents = hmap (Comp . pickleMany) $ unPOP allPicklers
    pickleElem :: NP (PU :.: NP I) a
    pickleElem = hliftA2 mkElem names pickleContents
    pickleFull :: PU (NS (NP I) a) 
    pickleFull = pickleSum pickleElem

    mkElem :: forall a1. K QName a1 -> (:.:) PU (NP I) a1 -> (:.:) PU (NP I) a1
    mkElem = coerce $ xpElemQN @(NP I a1)
    -- mkElem (K name) (Comp pickl) = Comp $ xpElemQN name pickl

-- autoPickle'' :: All2 XmlPickler a => NP (K QName) a -> PU (SOP' I a)
-- autoPickle'' = hcfoldr Proxy (\x -> xpOr $ xpElemQN (unK x) autoProduct) xpNull
-- autoPickle'' Nil = xpNull
-- autoPickle'' (K x :* xs) = xpOr (xpElemQN x autoProduct) $ autoPickle'' xs

-- | Pickle a simple product type
-- You'll need to manually call xpElem to specify the element name
--
-- data Foo = Foo Some Things
-- instance XmlPickler Foo where
--   xpickle = xpElem "foo" pickleProduct
pickleProduct :: (IsProductType a xs, All XmlPickler xs) => PU a 
pickleProduct = xpWrap (productTypeTo , productTypeFrom) autoProduct

newtype SimpleProduct a = SimpleProduct a

proxyTop :: Proxy Top
proxyTop = Proxy

proxyXP1 :: Proxy (All XmlPickler)
proxyXP1 = Proxy
proxyXP :: Proxy XmlPickler
proxyXP = Proxy

-- The base combinators that corresponds to an algebraic data type.
-- xpOne is Unit, xpCons is Product type, xpNull is empty type, xpOr is product type
xpOne :: PU (NP f '[])
xpOne = xpLift Nil

xpCons :: PU (f a) -> PU (NP f as) -> PU (NP f (a ': as))
xpCons p q = PU
  { appPickle = \(a :* b) -> appPickle p a . appPickle q b
  , appUnPickle = liftA2 (:*) (appUnPickle p) (appUnPickle q)
  , theSchema = theSchema p `scSeq` theSchema q
  }

xpNull :: PU (NS f '[])
xpNull = PU
    { appPickle = \a _ -> case a of {}
    , appUnPickle = throwMsg "PU.zero"
    , theSchema = scNull
    }

xpOr :: PU (f x) -> PU (NS f xs) -> PU (NS f (x ': xs))
xpOr p q = PU
    { appPickle = \case
        Z a  -> appPickle p (a)
        S as -> appPickle q as
    , appUnPickle = mchoice (Z <$> appUnPickle p) pure (S <$> appUnPickle q)
    , theSchema = theSchema p `scAlt` theSchema q
    }
