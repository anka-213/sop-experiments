{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
module PickleSopExample (module PickleSopExample) where

import qualified GHC.Generics as GHC
import Generics.SOP
import PickleSOP
import Text.XML.HXT.Core

unpickleC :: XmlPickler a => String -> Either String a
unpickleC = unpickleDoc' xpickle . head . runLA (removeAllWhiteSpace <<< xread) 

unpickle :: PU a -> String -> Either String a
unpickle p = unpickleDoc' p . head . runLA (removeAllWhiteSpace <<< xread) 

pickleC :: XmlPickler a => a -> String
pickleC = showPickled []

pickle :: PU a -> a -> String
pickle p = showPickled' p []

showPickled' :: PU a -> SysConfigList -> a -> String
showPickled' pu a = concat . (pickleDoc pu >>> runLA (writeDocumentToString a))

data PSExample = PSExample String String
  deriving stock (Eq, Show)
  deriving stock (GHC.Generic)
  deriving anyclass (Generic, HasDatatypeInfo)

instance XmlPickler PSExample where
  xpickle = xpProduct $ 
    xpAttr "foo" xpText :*
    xpAttr "bar" xpText :*
    Nil

data SomeFoo = SomeFoo PSExample
  deriving stock (Eq, Show)
  deriving stock (GHC.Generic)
  deriving anyclass (Generic, HasDatatypeInfo)

instance XmlPickler SomeFoo where
  xpickle = xpElem "some_foo" $ pickleProduct

fooOrBar :: PU (Either SomeFoo PSExample)
fooOrBar = xpElem "either" $ autoPickleSOP "" "" $
   "leftFoo" <:
   "rightBar" <:
   Nil

fooOrBar' :: PU (Either SomeFoo PSExample)
fooOrBar' = xpElem "either" $ xpAlt (\case (Left _) -> 0; (Right _) -> 1)
   [ xpElem "leftFoo" $ xpWrap (Left, getLeft) xpickle
   , xpElem "rightBar" $ xpWrap (Right, getRight) xpickle
   ]

getLeft :: Show b => Either p b -> p
getLeft (Left x) = x
getLeft (Right e) = error $ "not left: " ++ show e

getRight :: Show e => Either e p -> p
getRight (Right x) = x
getRight (Left e) = error $ "not right: " ++ show e


data ThreeAlts = A | B | C
  deriving stock (Eq, Show)
  deriving stock (GHC.Generic)
  deriving anyclass (Generic, HasDatatypeInfo)

instance XmlPickler ThreeAlts where
  xpickle = xpElem "either" $ autoPickleSOP "" "" $
    "A" <: "B" <: "C" <: Nil

xpta :: PU ThreeAlts
xpta = xpickle

-- -- $> putStrLn . pickleC . SomeFoo $ PSExample "f" "b"
--
-- -- $> putStrLn . pickle fooOrBar . Left . SomeFoo $ PSExample "f" "b"
--
-- -- $> putStrLn . pickle fooOrBar . Right $ PSExample "f" "b"

-- $> print . getRight . unpickle fooOrBar $ "<either><rightBar foo=\"f\" bar=\"b\"/></either>"

-- $> putStrLn . getLeft . unpickle fooOrBar $ "<either><leftFoo bar=\"f\" foo=\"b\" baz=\"z\"/></either>"

-- $> putStrLn . getLeft . unpickle fooOrBar $ "<either><rightBar bar=\"f\" foo=\"b\" baz=\"z\"/></either>"

-- $> putStrLn . getLeft . unpickle xpta $ "<either><rightBar bar=\"f\" foo=\"b\" baz=\"z\"/></either>"