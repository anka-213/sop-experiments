{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
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
import Data.Maybe (fromMaybe, fromJust)

-- | An unwrapped sum of products
type SOP' f a = NS (NP f) a

-- | An unwrapped product of products
type POP' f a = NP (NP f) a

xpSOPInv' :: Generic a => PU a -> PU (SOP' I (Code a))
xpSOPInv' = xpWrap (unSOP . from , to . SOP)

xpSOPInv :: Generic a => PU a -> PU (SOP I (Code a))
xpSOPInv = xpWrap (from , to)

xpSOPInv'' :: Generic a => PU a -> PU (SOP' I (Code a))
xpSOPInv'' = coerce . xpSOPInv

xpSOP:: Generic a => PU (SOP I (Code a)) -> PU a
xpSOP= xpWrap (to , from)

xpSOP' :: Generic a => PU (SOP' I (Code a)) -> PU a
xpSOP' = xpSOP . coerce

-- xpNewtype :: Coercible a x => PU x -> PU a
xpNewtype :: IsNewtype a x => PU x -> PU a
xpNewtype = coerce

liftCoercion :: Coercible (f a) (f b) => (a -> b) -> f a -> f b
liftCoercion _ = coerce

pickleDeep :: POP' PU a -> PU (SOP' I a)
pickleDeep Nil = xpNull
pickleDeep (x :* xs) = xpOr (pickleMany x) $ pickleDeep xs

pickleMany :: NP PU x -> PU (NP I x)
pickleMany Nil = xpLift Nil
pickleMany (x :* xs) = xpCons (xpNewtype x) $ pickleMany xs
-- pickleMany (x :* xs) = xpWrap (_ , _) $ xpPair x $ pickleMany xs

pickleMany' :: NP PU x -> PU (NP I x)
pickleMany' = hfoldr (xpCons . xpNewtype) xpOne


-- ictraverse'_NS  ::
--      forall c proxy xs f f'. (All c xs)
--   => proxy c -> (forall a. c a => f a -> PU (f' a)) -> NS f xs  -> PU (NS f' xs)
-- ictraverse'_NS _ f = go where
--   go :: All c ys => NS f ys -> PU (NS f' ys)
--   go (Z x)  = _ $ f x
--   go (S xs) = _ $ go xs

-- | Convert a product of picklers to a pickler of a sum
-- This is equivalent to hsequence', except that PU is not applicative
pickleSum :: NP (PU :.: f) a -> PU (NS f a)
pickleSum Nil = xpNull
pickleSum (Comp x :* xs) = xpOr x $ pickleSum xs

pickleSum' :: NP (PU :.: f) a -> PU (NS f a)
pickleSum' = unComp . hfoldr' (liftComp2 xpOr) (Comp xpNull)
    -- liftComp f = unComp . f . Comp 
    -- liftComp2 :: (:.:) PU f (g x) -> (:.:) PU f (g x) -> (:.:) PU f (g x)
 -- f (g p) -> f (g p) -> f (g p)
    -- liftComp2 f x y = Comp $ f (unComp x) (unComp y)

ictraverse'_NS  ::
     forall c proxy xs f f' . (All c xs)
  => proxy c -> (forall a. c a => f a -> PU (f' a)) -> NP f xs  -> PU (NS f' xs)
-- ictraverse'_NS p f = isequence'_NS . hcmap p (Comp . f)
ictraverse'_NS _ f = go where
  go :: All c ys => NP f ys -> PU (NS f' ys)
  go Nil = xpNull
  go (x :* xs) = xpOr (f x) (go xs)

lowerComp :: (((f :.: g) p -> (f1 :.: g1) p1) -> f (g p) -> f1 (g1 p1))
lowerComp f = unComp . f . Comp 

liftComp :: (f (g p) -> f1 (g1 p1)) -> ((f :.: g) p -> (f1 :.: g1) p1)
liftComp f = coerce f

liftComp2 :: ((f (g p)    -> f (g1 p1)     -> f (g2 p2))
           -> (:.:) f g p -> (:.:) f g1 p1 -> (:.:) f g2 p2)
liftComp2 f x y = Comp $ f (unComp x) (unComp y)

pickleSum'' :: forall f a. NP (PU :.: f) a -> PU (NS f a)
pickleSum'' = hfoldr (xpOr . unComp) xpNull
-- pickleSum'' = (coerce $ hfoldr' @f @(PU :.: NS f) @a) xpOr xpNull

-- -- Less safe and doesn't work
-- pickleSum''' :: SListI xs => NP (PU :.: f) xs -> PU (NS f xs)
-- pickleSum''' picklers = xpAlt hindex $ fmap sequencePU $ apInjs_NP picklers

-- sequencePU :: SListI xs => NS (PU :.: f) xs -> PU (NS f xs)
-- sequencePU = hcollapse . hmap (K . xpWrap (_ , _) . unComp)

-- | Bad version. Don't use
pickleSum'''' :: SListI xs => NP (PU :.: f) xs -> PU (NS f xs)
pickleSum'''' picklers = xpAlt hindex . hcollapse $ hliftA3 ejectInject ejections injections picklers

-- | Combine an ejection and an injection to convert a PU (f a) to a PU (NS f xs)
-- Warning: The function is partial
ejectInject :: Ejection f xs a -> Injection f xs a -> (PU :.: f) a -> K (PU (NS f xs)) a
ejectInject (Fn ej) (Fn inj) (Comp pu) = K $ xpWrap (unK . inj , fromJust . unComp . ej . K) pu

-- pickleSum' :: SListI a => NP (PU :.: f) a -> PU (NS f a)
-- pickleSum' = undefined . hmap (_ . fn . xpOr . unComp)

-- From pointless-fun
(~>) :: (a -> b1) -> (b2 -> c) -> (b1 -> b2) -> a -> c
(f ~> g) x = g . x .f

infixr 6 ~>

hfoldr ::
  forall f r g xss.
  (forall x xs. f x -> r (g xs) -> r (g (x : xs))) ->
  r (g '[]) ->
  NP f xss ->
  r (g xss)
-- hfoldr f = Comp ~> id ~> unComp $ hfoldr' $ id ~> unComp ~> Comp $ f
-- hfoldr f = coerce $ hfoldr' (\x -> coerce . f x . unComp)
hfoldr f = coerce $ hfoldr' (liftComp . f)
-- hfoldr f z = unComp . hfoldr' (\x -> Comp . f x . unComp) (Comp z)
-- hfoldr f z = go where
--     go :: forall z. NP f z -> r (g z)
--     go Nil = z
--     go (x :* xs) = f x $ go xs
-- Failing attemts:
-- hfoldr = (id ~> unComp ~> Comp ) ~> Comp ~> id ~> unComp $ hfoldr' @f @(r :.: g)
-- hfoldr = coerce $ hfoldr' @(r :.: g f) @r @xss
-- hfoldr = coerce $ hfoldr''
--   where
--    hfoldr'' :: (forall (x :: k) (xs :: [k]).
--      f x -> (:.:) r g xs -> (:.:) r g (x : xs))
--     -> (:.:) r g '[] -> NP f xss -> (:.:) r g xss
--    hfoldr'' = hfoldr'
 

hfoldr' :: forall f r xss. (forall x xs. f x -> r xs -> r (x : xs)) -> r '[] -> NP f xss -> r xss
hfoldr' f z = go where
    go :: forall z. NP f z -> r z
    go Nil = z
    go (x :* xs) = f x $ go xs

pickleDeep2 :: SListI a => POP' PU a -> PU (SOP' I a)
pickleDeep2 = pickleSum . hmap (Comp . pickleMany)

autoProduct :: All XmlPickler a => PU (NP I a)
autoProduct = unComp $ cpara_SList proxyXP (Comp xpOne) (Comp . xpCons (xpNewtype xpickle) . unComp)

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
    pickleFull :: PU (SOP' I a)
    pickleFull = pickleSum pickleElem

    mkElem :: forall a1. K QName a1 -> (:.:) PU (NP I) a1 -> (:.:) PU (NP I) a1
    mkElem = coerce $ xpElemQN @(NP I a1)
    -- mkElem (K name) (Comp pickl) = Comp $ xpElemQN name pickl

autoPickle'' :: All2 XmlPickler a => NP (K QName) a -> PU (SOP' I a)
autoPickle'' = pickleSum . hcmap (allP proxyXP) (\x -> Comp $ xpElemQN (unK x) autoProduct)
-- autoPickle'' = hfoldr (xpOr . unComp) xpNull . hcmap proxyXP1 (\x -> Comp $ xpElemQN (unK x) autoProduct)
-- autoPickle'' = hfoldr (\x -> xpOr $ unComp x) xpNull . hcmap proxyXP1 (\(x :: K QName a1) -> Comp $ xpElemQN (unK x) $ autoProduct @a1)
-- Defunct:
-- autoPickle'' = hfoldr (\x -> xpOr $ unK x) xpNull . hmap (\x -> K $ xpElemQN (unK x) autoProduct)
-- autoPickle'' = hfoldr (\x -> xpOr $ xpElemQN (unK x) autoProduct) xpNull

autoPickle''' :: All2 XmlPickler a => NP (K QName) a -> PU (SOP' I a)
autoPickle''' = ictraverse'_NS (allP proxyXP) (\x -> xpElemQN (unK x) autoProduct)

pickleElem :: All XmlPickler a => QName -> PU (NP I a)
pickleElem qname = xpElemQN qname autoProduct

-- | Create a product of picklers for all the cases in a sum type, 
-- given the element names for each constructor
productOfPicklers :: All2 XmlPickler a => NP (K QName) a -> NP (PU :.: NP I) a
productOfPicklers = hcmap proxyXP1 (\x -> Comp $ xpElemQN (unK x) autoProduct)

type NamespaceUri = String
type NSPrefix = String
type LocalName = String

-- | Turns a product of unqualified names into a product of qualified names.
qualify :: SListI xs => NamespaceUri -> NSPrefix -> NP (K LocalName) xs -> NP (K QName) xs
qualify namespace prefix = hmap $ mapKK $ \name -> mkQName prefix name namespace


type XmlSOP a = (Generic a, All2 XmlPickler (Code a))

-- | Given a namespace, a prefix and a list of element names,
-- return a pickler for a sum type, assuming all contained data 
autoPickleSOP :: XmlSOP a => NamespaceUri -> NSPrefix -> NP (K LocalName) (Code a) -> PU a
autoPickleSOP namespace prefix elemNames =
  xpSOP'
    . pickleSum''
    . productOfPicklers
    $ qualify namespace prefix elemNames

-- | Partial version of the function above, which instead takes an ordinary list
autoPickleSOPList :: XmlSOP a => NamespaceUri -> NSPrefix -> [LocalName] -> PU a
autoPickleSOPList namespace prefix elemNames =
  autoPickleSOP namespace prefix
    . fromMaybe (error $ "autoPickleSOPList: Wrong length of list: " ++ show elemNames)
    $ fromList elemNames

unpickle :: PU a -> String -> Either String a
unpickle p = unpickleDoc' p . head . runLA (removeAllWhiteSpace <<< xread) 

-- | Pickle a simple product type
-- You'll need to manually call xpElem to specify the element name
--
-- data Foo = Foo Some Things
-- instance XmlPickler Foo where
--   xpickle = xpElem "foo" pickleProduct
pickleProduct :: (IsProductType a xs, All XmlPickler xs) => PU a
pickleProduct = xpWrap (productTypeTo , productTypeFrom) autoProduct

pickleProduct' :: (IsProductType a xs, All XmlPickler xs) => PU a
pickleProduct' = xpSOP' . xpWrap (Z , unZ) $ autoProduct

-- | Constructor for lists of `K a`
-- 
-- >>> "a" <: "b" <: Nil :: NP (K String) '[x, y]
-- K "a" :* K "b" :* Nil
(<:) :: a -> NP (K a) xs -> NP (K a) (x : xs)
x <: xs = K x :* xs

infixr 5 <:

-- Wrapper for use with deriving via
-- newtype SimpleProduct a = SimpleProduct a

proxyTop :: Proxy Top
proxyTop = Proxy

allP :: Proxy a -> Proxy (All a)
allP _ = Proxy

proxyXP1 :: Proxy (All XmlPickler)
proxyXP1 = Proxy
proxyXP :: Proxy XmlPickler
proxyXP = Proxy

-- * The base combinators that corresponds to an algebraic data type.
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
        Z a  -> appPickle p a
        S as -> appPickle q as
    , appUnPickle = mchoice (Z <$> appUnPickle p) pure (S <$> appUnPickle q)
    , theSchema = theSchema p `scAlt` theSchema q
    }
