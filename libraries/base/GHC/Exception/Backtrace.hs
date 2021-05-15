{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE NoImplicitPrelude
           , ExistentialQuantification
           , MagicHash
           , RecordWildCards
           , PatternSynonyms
  #-}
{-# OPTIONS_HADDOCK not-home #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  GHC.Exception.Backtrace
-- Copyright   :  (c) The University of Glasgow, 2020-2025
-- License     :  see libraries/base/LICENSE
--
-- Maintainer  :  cvs-ghc@haskell.org
-- Stability   :  internal
-- Portability :  non-portable (GHC extensions)
--
-- Exception backtraces.
--
-----------------------------------------------------------------------------

module GHC.Exception.Backtrace
       ( Backtrace(..)
       , setGlobalBacktraceMechanism
       , getGlobalBacktraceMechanism
       ) where

import GHC.Ptr
import GHC.Stack.CCS
import GHC.Stack
import GHC.ExecutionStack
import GHC.Base
import GHC.Show

-- | An exception backtrace.
--
-- @since 4.15
data Backtrace
    = CostCenterBacktrace (Ptr GHC.Stack.CCS.CostCentreStack)
      -- ^ a cost center profiler backtrace
    | HasCallStackBacktrace GHC.Stack.CallStack
      -- ^ a stack from 'GHC.Stack.HasCallStack'
    | ExecutionBacktrace [GHC.ExecutionStack.Location]
      -- ^ a stack unwinding (e.g. DWARF) backtrace

-- | @since 4.15
instance Show Backtrace where
    -- TODO
    showsPrec p (CostCenterBacktrace ccs) = showsPrec p ccs
    showsPrec p (HasCallStackBacktrace ccs) = showsPrec p ccs
    showsPrec p (ExecutionBacktrace ccs) = showsPrec p ccs

-- | How to collect a backtrace when an exception is thrown.
data BacktraceMechanism
    = NoBacktrace
      -- ^ don't collect a backtrace
    | CostCenterBacktrace
      -- ^ collect a cost center stacktrace (only available when built with profiling)
    | ExecutionStackBacktrace (Maybe Int)
      -- ^ use execution stack unwinding with given limit

currentBacktraceMechanism :: IORef BacktraceMechanism
currentBacktraceMechanism = unsafePerformIO $ mkIORef Nothing
{-# NOINLINE currentBacktraceMechanism #-}

-- | Set how 'Control.Exception.throwIO', et al. collect backtraces.
setGlobalBacktraceMechanism :: BacktraceMechanism -> IO ()
setGlobalBacktraceMechanism = writeIORef currentBacktraceMechanism

-- | Returns the currently selected 'BacktraceMechanism'.
getGlobalBacktraceMechanism :: IO BacktraceMechanism
getGlobalBacktraceMechanism = readIORef currentBacktraceMechanism

-- | Collect a 'Backtrace' via the current global 'BacktraceMechanism'. See
-- 'setGlobalBacktraceMechanism'.
collectBacktrace :: IO (Maybe Backtrace)
collectBacktrace = do
    mech <- getGlobalBacktraceMechanism
    collectBacktrace' mech

-- | Collect a 'Backtrace' via the given 'BacktraceMechanism'.
collectBacktrace' :: BacktraceMechanism -> IO (Maybe Backtrace)
collectBacktrace' NoBacktrace = Nothing
collectBacktrace' CostCenterBacktrace = do
  ptr <- getCurrentCCS ()
  -- TODO: is the unit here safe? Is this dummy argument really needed? Why
  -- isn't the state token sufficient?
  return $ if ptr == nullPtr then Nothing else Just (CostCenterBacktrace ptr)
collectBacktrace' ExecutionStackBacktrace = fmap ExecutionBacktrace <$> getStackTrace
