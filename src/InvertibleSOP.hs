{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE QuasiQuotes #-}
module InvertibleSOP (module InvertibleSOP) where

import Generics.SOP
import qualified Data.Invertible as Inv
import Data.Invertible (invert, type (<->))
import Data.Kind (Type)
import Generics.SOP.Constraint (SListIN)
import Control.Invertible.Monoidal
import Data.Void (absurd, Void)
-- import Control.Invertible.Monoidal (liftI2, unit, (>*<), (>$<), Monoidal)

toFrom :: Generic a => a <-> Rep a
toFrom = from :<->: to

productTypeConv :: IsProductType a xs => a <-> NP I xs
productTypeConv = productTypeFrom :<->: productTypeTo

enumTypeConv :: IsEnumType a => a <-> NS (K ()) (Code a)
enumTypeConv = enumTypeFrom :<->: enumTypeTo

wrappedTypeConv :: IsWrappedType a x => a <-> x
wrappedTypeConv = wrappedTypeFrom :<->: wrappedTypeTo

newtypeConv :: IsNewtype a x => a <-> x
newtypeConv = newtypeFrom :<->: newtypeTo

sopConv :: SOP f xss <-> NS (NP f) xss
sopConv = unSOP :<->: SOP

popConv :: POP f xss <-> NP (NP f) xss
popConv = unPOP :<->: POP

hdTl :: NP f (x ': xs) <-> (f x, NP f xs)
hdTl = (\x -> (hd x, tl x)) :<->: (uncurry (:*))

tlHd :: (f x, NP f xs) <-> NP f (x ': xs)
tlHd = invert hdTl

newtype (f <-.-> g) a = Bij { apBij :: f a <-> g a }

-- nilUnit :: 
nilMon :: Monoidal f => f (NP g '[])
nilMon = Inv.fmap nilUnit unit

(>:*<) :: Monoidal f => f (g x) -> f (NP g xs) -> f (NP g (x : xs))
x >:*< xs = liftI2 tlHd x xs

class HAp h => HSequenceInv (h :: (k -> Type) -> (l -> Type)) where
  ihsequence' :: (SListIN h xs, Monoidal f) => (Prod h) (f :.: g) xs -> f (h g xs)
  ihctraverse' :: (AllN h c xs, Monoidal g) => proxy c -> (forall a. c a => f a -> g (f' a)) -> (Prod h) f xs -> g (h f' xs)
--   ihtraverse' :: (SListIN' h xs , Monoidal g) => (forall a. f a -> g (f' a)) -> h f xs -> g (h f' xs)

ihtraverse' :: (HSequenceInv h , SListIN' h xs , Monoidal g) => (forall a. f a -> g (f' a)) -> (Prod h) f xs -> g (h f' xs)
ihtraverse' f = ihctraverse' topP f

-- A type alias variant, so we can derive `AllN h Top` from `SequenceListIN' h`
type SListIN' (h :: (k -> Type) -> (l -> Type)) = AllN h Top

-- | Specialization of 'hsequence''.

topP :: Proxy Top
topP = Proxy

isequence'_NP  ::              Monoidal f  => NP  (f :.: g) xs  -> f (NP  g xs)
isequence'_NP Nil              = nilUnit >$< unit
isequence'_NP (Comp mx :* mxs) = mx >:*< isequence'_NP mxs
  -- _ >$< unComp mx >*< sequence'_NP mxs

ictraverse'_NP  ::
     forall c proxy xs f f' g. (All c xs,  Monoidal g)
  => proxy c -> (forall a. c a => f a -> g (f' a)) -> NP f xs  -> g (NP f' xs)
ictraverse'_NP _ f = go where
    go :: All c ys => NP f ys -> g (NP f' ys)
    go Nil       = nilMon
    go (x :* xs) = liftI2 tlHd (f x) (go xs)
--   go (x :* xs) = tlHd >$< (f x >*< go xs)

instance HSequenceInv NP where
    ihsequence' = isequence'_NP
    ihctraverse' = ictraverse'_NP

nilUnit :: () <-> NP g '[]
nilUnit = mempty :<->: mempty

zOrS :: NS f (x ': xs) <-> Either (f x) (NS f xs) 
zOrS = [biCase|
    Z x <-> Left x
    S xs <-> Right xs
    |]

zOrS' ::  Either (f x) (NS f xs) <-> NS f (x ': xs)
zOrS' = invert zOrS

nsVoid :: Void <-> NS g '[]
nsVoid = absurd :<->: \case {}

fzero :: MonoidalAlt f => f (NS g '[])
fzero = nsVoid >$< zero

nsPlus :: MonoidalAlt f => f (g x) -> f (NS g xs) -> f (NS g (x : xs))
nsPlus x xs = zOrS' >$< (x >|< xs)

-- go' :: All c ys => proxy c -> NS f ys <-> g (NS f' ys)
-- go' _ = _ Inv.. zOrS

isequence'_NS  ::   MonoidalAlt f  => NP  (f :.: g) xs  -> f (NS  g xs)
isequence'_NS Nil = fzero
isequence'_NS (Comp x :* xs) = nsPlus x (isequence'_NS xs)

ictraverse'_NS  ::
     forall c proxy xs f f' g. (All c xs,  MonoidalAlt g)
  => proxy c -> (forall a. c a => f a -> g (f' a)) -> NP f xs  -> g (NS f' xs)
-- ictraverse'_NS p f = isequence'_NS . hcmap p (Comp . f)
ictraverse'_NS _ f = go where
  go :: All c ys => NP f ys -> g (NS f' ys)
  go Nil = fzero
  go (x :* xs) = nsPlus (f x) (go xs)

ihtraverse'_NS :: (SListI xs , MonoidalAlt g) => (forall a. f a -> g (f' a)) -> NP f xs -> g (NS f' xs)
ihtraverse'_NS f = ictraverse'_NS topP f

{-
ictraverse'_NS  ::
     forall c proxy xs f f' g. (All c xs,  Inv.Functor g)
  => proxy c -> (forall a. c a => f a -> g (f' a)) -> NS f xs  -> g (NS f' xs)
ictraverse'_NS _ f = go where
  go :: All c ys => NS f ys -> g (NS f' ys)
--   go x@(Z _) = go' x
--   go x@(S _) = go' x
--   go' :: All c (y ': ys) => NS f (y ': ys) -> g (NS f' (y ': ys))
-- --   go' = _
--   go' = _ Prelude.. biFrom zOrS'
  go (Z x)  =  _ >$< f x
  go (S xs) = _ >$< go xs
-}

-- class (Prod (Prod h) ~ Prod h, HPure (Prod h)) => HApInv (h  :: (k -> Type) -> (l -> Type)) where
--     hapInv :: Prod h (f <-.-> g) xs -> h f xs <-> h g xs

-- hapInv :: Prod h (f <-.-> g) xs -> h f xs <-> h g xs
-- hapInv = _

-- instance HApInv NP  where hapInv = apInv_NP
-- instance HApInv POP where hapInv = apInv_POP

-- apInv_POP :: POP (f <-.-> g) xs -> POP f xs <-> POP g xs
-- apInv_POP = error "not implemented"

-- apInv_NP :: NP (f <-.-> g) xs -> NP f xs <-> NP g xs
-- apInv_NP Nil            = hcoerce :<->: hcoerce
-- apInv_NP (Bij f :* fs)  = _ :<->: _
-- apInv_NP = error "not implemented"
-- apInv_NP Nil           = [biCase| Nil    <->    Nil |]
-- apInv_NP (Fn f :* fs)  = [biCase| (x :* xs) <-> (f x :* ap_NP fs xs) |]
-- apInv_NP Nil           Nil        = Nil
-- apInv_NP (Fn f :* fs)  (x :* xs)  = f x :* ap_NP fs xs


    -- _ :<->: _(Monoidal f, Functor f1)(Monoidal f, Functor f1)(All c xs, Monoidal g, Applicative g)(Functor f, MonoidalAlt f)(All c xs, Functor g, MonoidalAlt g)