module BetterUnpickleErrors (module BetterUnpickleErrors) where

import Text.XML.HXT.Arrow.Pickle.Xml (PU(..), nesting, Unpickler(..), St, UnpickleErr, UnpickleVal, Unpickler)
import Control.Monad.Except (throwError, MonadError(catchError))
import Control.Monad.State.Class (get, gets)
-- import Control.Arrow (Arrow(first))

simpleChoice :: Unpickler a -> Unpickler a -> Unpickler a
simpleChoice u v = catchError u $ \e -> do
    myNest <- gets nesting
    if myNest == nesting (snd e)
        then v
        else throwError e -- note that this changes st

catchSameLevel :: Unpickler a -> (UnpickleErr -> Unpickler a) -> Unpickler a
catchSameLevel u handler = catchError u $ \e -> do
    myNest <- gets nesting
    if myNest == nesting (snd e)
        then handler e
        else throwError e -- note that this changes st

prependErrorMessage :: String -> Unpickler a -> Unpickler a
prependErrorMessage msg u = catchSameLevel u $ \(msg', _st) -> do
    st <- get
    throwError $ (msg ++ "\n" ++ msg', st)

xpPrependErrorMessage :: String -> PU a -> PU a
xpPrependErrorMessage msg pu = pu { appUnPickle = prependErrorMessage msg $ appUnPickle pu }

choiceCollectErrors :: Unpickler a -> Unpickler a -> Unpickler a
choiceCollectErrors u v = catchSameLevel u $ \(msg, _) ->
    prependErrorMessage msg v
-- choiceCollectErrors u v = catchSameLevel u $ \e -> do
--     st <- get
--     catchError v $ throwError . combineErrors' st e
-- choiceCollectErrors u v = catchError u $ \e@(_msg, st') -> do
--     st <- get
--     myNest <- gets nesting
--     if myNest == nesting st'
--         then catchError v $ throwError . combineErrors' st e
--         else throwError e

combineErrors' :: St -> UnpickleErr -> UnpickleErr -> UnpickleErr
combineErrors' st (msg1, st1) (msg2, st2)
  | nesting st1 == nesting st2 = (msg1 ++ "\n" ++ msg2, st)
  | otherwise = (msg2, st)

-- $> putStrLn . getLeft . unpickle fooOrBar $ "<either x=\"x\"><lightBar foo=\"f\" bar=\"b\"/><rightBar/></either>"

-- choiceCollectErrors u v = UP $ \st ->
--   let (r, st') = runUP u st in
--   case r of
--     Right _ -> (r, st')
--     Left e@(msg, st'') ->
--       if nesting st'' == nesting st
--         then let (r', st''') = runUP u st in
--           case r' of
--             Right _ -> (r', st''')
--             Left e' -> combineErrors e e'
--         else (Left e, st')

combineErrors :: UnpickleErr -> UnpickleErr -> (UnpickleVal a, St)
combineErrors = error "not implemented"