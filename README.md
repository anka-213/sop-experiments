# sop-experiments

[![GitHub CI](https://github.com/anka-213/sop-experiments/workflows/CI/badge.svg)](https://github.com/anka-213/sop-experiments/actions)
[![Build status](https://img.shields.io/travis/anka-213/sop-experiments.svg?logo=travis)](https://travis-ci.org/anka-213/sop-experiments)
[![Hackage](https://img.shields.io/hackage/v/sop-experiments.svg?logo=haskell)](https://hackage.haskell.org/package/sop-experiments)
[![Stackage Lts](http://stackage.org/package/sop-experiments/badge/lts)](http://stackage.org/lts/package/sop-experiments)
[![Stackage Nightly](http://stackage.org/package/sop-experiments/badge/nightly)](http://stackage.org/nightly/package/sop-experiments)
[![MIT license](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

Experiments with [generics-sop](https://hackage.haskell.org/package/generics-sop).

Run `ghcid --allow-eval` in the directory to see examples.

# [SopExperiments.hs](src/SopExperiments.hs)

Random stuff to get familiar with the library

# [SopParser.hs](src/SopParser.hs)

Experiments to see how parsing works with SOP

# [PickleSOP.hs](src/PickleSOP.hs)

A library for writing [HXT Picklers](https://hackage.haskell.org/package/hxt-9.3.1.18/docs/Text-XML-HXT-Arrow-Pickle.html) generically with SOP

See [PickleSopExample.hs](src/PickleSopExample.hs) for a few examples on how to use it. More examples and some cleaning up will come.

# [InvertibleSOP.hs](src/InvertibleSOP.hs)

Connects [generics-sop](https://hackage.haskell.org/package/generics-sop) with [invertible](https://hackage.haskell.org/package/invertible).
If paired with [invertible-hxt](https://hackage.haskell.org/package/invertible-hxt-0.1) it can serve a similar purpose as PickleSOP.hs above

# [BetterUnpickleErrors.hs](src/BetterUnpickleErrors.hs)

Provides more info when failing to unpickle a sum. Instead of just saying "xpAlt: no matching unpickler found for a sum datatype", it will list all the errors from the individual parsers.