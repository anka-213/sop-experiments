{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeApplications #-}
module SopParser (module SopParser) where

import qualified GHC.Generics as GHC
import Generics.SOP
import Text.ParserCombinators.ReadP
import Control.Applicative (Alternative((<|>)))
import Test.QuickCheck (arbitrary, elements, Gen, Arbitrary)
import Control.Monad (liftM)
import Generics.SOP.NP (sequence_NP, cpure_NP)

data FooBar = Foo | Bar
  deriving stock (Eq, Show)
  deriving stock (GHC.Generic)
  deriving anyclass (Generic, HasDatatypeInfo)


--- $> :browse Text.ParserCombinators.ReadP

-- mkParse :: ConstrInfos a -> ReadP a
-- mkParse (Constructor s :* _xs) = string s
-- mkParse Nil = pfail

-- mkParse :: IsEnumType a => Proxy a -> ConstrInfos a -> NP (K (ReadP (SOP I (Code a)))) (Code a)
-- mkParse _ = hmap $ K . (_ <$) . string . constructorName

-- mkParse :: IsEnumType a => Proxy a -> ConstrInfos a -> NP (K (ReadP ())) (Code a)
-- mkParse _ = hmap $ K . (() <$) . string . constructorName

type IsEnumCode c = All ((~) '[]) c

mkParse :: IsEnumCode c => NP ConstructorInfo c -> NP (K (ReadP ())) c
mkParse = hmap $ K . (() <$) . string . constructorName

-- mkParse2 :: All ((~) '[]) c => NP (K (ReadP ())) c -> ReadP (SOP I c)
-- mkParse2 (K x :* xs) = SOP (Z Nil) <$ x <|> SOP . S . unSOP <$> mkParse2 xs
-- mkParse2 Nil = pfail

mkParse2 :: IsEnumCode c => NP (K (ReadP ())) c -> ReadP (NS (K ()) c)
mkParse2 (K x :* xs) = Z (K ()) <$ x <|> S <$> mkParse2 xs
mkParse2 Nil = pfail

mkParse2' :: IsEnumCode c => NP (K (ReadP ())) c -> ReadP (NS (K ()) c)
mkParse2' = choice . fmap hsequenceK . apInjs_NP

parse :: (IsEnumType a, HasDatatypeInfo a) => Proxy a -> ReadP a
parse p = fmap enumTypeTo . mkParse2 . mkParse $ getConstructors p

-- mkParseG0 :: ConstructorInfo a -> ReadP (NP I a)
-- mkParseG0 (Constructor name) = undefined name
-- mkParseG0 (Infix name b _n) = undefined name b
-- mkParseG0 (Record a b) = _

parseOne :: Read a => ReadP a
parseOne = readS_to_P reads

mkParseG1 :: All2 Read c => NP ConstructorInfo c -> NP (ReadP :.: NP I) c
mkParseG1 = hcmap (Proxy @(All Read)) $ Comp . mkParseG1Inner

mkParseG1Inner :: All Read c => ConstructorInfo c -> ReadP (NP I c)
mkParseG1Inner info =
    string (constructorName info)
    *> sequence_NP (cpure_NP @Read Proxy parseOne)

-- getIt :: ReadP (NP I a)
-- getIt = _

-- mkParseG1 = hmap $ Comp . _ . string . constructorName

mkParseG2 :: SListI c => NP (ReadP :.: NP I) c -> ReadP (NS (NP I) c)
mkParseG2 = choice . fmap hsequence' . apInjs_NP

type Parsable c = All2 Read c

gparse :: (Parsable (Code a), HasDatatypeInfo a) => Proxy a -> ReadP a
gparse = fmap (to . SOP) . mkParseG2 . mkParseG1 . getConstructors 

type ConstrInfos a =  NP ConstructorInfo (Code a)

getConstructors :: HasDatatypeInfo t => proxy t -> NP ConstructorInfo (Code t)
getConstructors = constructorInfo . datatypeInfo

parseFoo :: ReadP FooBar
parseFoo = parse Proxy

gparseFoo :: ReadP FooBar
gparseFoo = gparse Proxy

-- $> readP_to_S (gparse (Proxy @([Int]))) ": 1 [2,3]"

garbitrary :: forall a. (Generic a, All2 Arbitrary (Code a)) => Gen a
garbitrary = liftM to $ hsequence =<< elements (apInjs_POP $ hcpure p arbitrary)
  where
    p :: Proxy Arbitrary
    p = Proxy