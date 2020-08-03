{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}

{-# LANGUAGE DerivingStrategies #-}
{- |
Copyright: (c) 2020 Andreas Källberg
SPDX-License-Identifier: MIT
Maintainer: Andreas Källberg <anka.213@gmail.com>

Experiments with generics-sop
-}

module SopExperiments
       ( module SopExperiments
       , Proxy(..)
       ) where

import qualified GHC.Generics as GHC
import Generics.SOP
-- import Data.Proxy

someFunc :: IO ()
someFunc = putStrLn ("someFunc" :: String)

--- $> :browse Generics.SOP

data Example = Ex1 Int () | Ex2 { _ex2 :: Char}
  deriving stock (Eq, Show)
  deriving stock (GHC.Generic)

instance Generic Example
instance HasDatatypeInfo Example

px :: Proxy t
px = Proxy

-- $> :kind! Code Example
-- '[ '[Int, ()], '[(), Char]]

-- $> datatypeInfo @Example px

--- $> :kind! DatatypeInfoOf Example

type CE = Code Example

-- ex :: DatatypeInfo '[ '[Int, ()], '[(), Char]]
ex :: DatatypeInfo CE
ex = datatypeInfo @Example px

conInfo :: NP ConstructorInfo CE
conInfo = case ex of
  ADT _moduleName _name c _strictnessInfo -> c

-- $> conInfo
-- Constructor "Ex1" :* Record "Ex2" (FieldInfo "_ex2" :* Nil) :* Nil

newtype Use f b a = Use (f a -> b)

-- Consume a sum type with a product of functions
nsCase :: NP (Use f r) arr -> NS f arr -> r
nsCase (Use f :* _) (Z x) = f x
nsCase (_ :* fs) (S xs) = nsCase fs xs
nsCase Nil nope = case nope of {}

useEx :: Example -> String
useEx = nsCase handleIt . unSOP . from

handleIt :: NP (Use (NP I) String) CE
handleIt = Use ex1 :* Use ex2 :* Nil

wrap :: (f a -> r) -> (f -.-> K r) a
wrap f = Fn $ K . f

handleIt' :: NP (NP I -.-> K String) CE
handleIt' = wrap ex1 :* wrap ex2 :* Nil

-- useEx' :: Example -> Int
useEx' :: Example -> String
useEx' = hcollapse . hap handleIt' . unSOP . from @Example

ex1 :: NP I '[Int, ()] -> String
ex1 (I n :* I () :* Nil) = "Ex1, Int: " ++ show n

ex2 :: NP I '[Char] -> String
ex2 (I c :* Nil) = "Ex2. Char: " ++ show c

-- $> to . from $ False :: FooBar
