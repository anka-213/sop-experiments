{- |
Copyright: (c) 2020 Andreas Källberg
SPDX-License-Identifier: MIT
Maintainer: Andreas Källberg <anka.213@gmail.com>

Experiments with generics-sop
-}

module SopExperiments
       ( someFunc
       ) where


someFunc :: IO ()
someFunc = putStrLn ("someFunc" :: String)
