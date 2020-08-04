-- | Copied from https://hackage.haskell.org/package/invertible-hxt

{-
Copyright (c) 2016-2017, Dylan Simon

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.

    * Redistributions in binary form must reproduce the above
      copyright notice, this list of conditions and the following
      disclaimer in the documentation and/or other materials provided
      with the distribution.

    * Neither the name of Dylan Simon nor the names of other
      contributors may be used to endorse or promote products derived
      from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
-}

module HxtPickleInvertible (
  zero,
  unit,
  (>*<),
  (>|<),
) where

import Data.Void (Void, absurd)
import Text.XML.HXT.Core
import Text.XML.HXT.Arrow.Pickle.Xml (mchoice, throwMsg)
import Text.XML.HXT.Arrow.Pickle.Schema (scSeq, scAlt, scNull)

unit :: PU ()
unit = xpUnit

(>*<) :: PU a -> PU b -> PU (a, b)
p >*< q = PU -- xpPair
  { appPickle = \(a, b) -> appPickle p a . appPickle q b
  , appUnPickle = do
      a <- appUnPickle p 
      b <- appUnPickle q
      return (a, b)
  , theSchema = theSchema p `scSeq` theSchema q
  }

zero :: PU Void
zero = PU
    { appPickle = \a _ -> absurd a
    , appUnPickle = throwMsg "PU.zero"
    , theSchema = scNull
    }

(>|<) :: PU a1 -> PU a2 -> PU (Either a1 a2)
p >|< q = PU
    { appPickle = either (appPickle p) (appPickle q)
    , appUnPickle = mchoice (Left <$> appUnPickle p) return (Right <$> appUnPickle q)
    , theSchema = theSchema p `scAlt` theSchema q
    }