module Loop where 

import Prelude hiding (catch)
import Data.Typeable
import Control.Monad.Error
import Control.Exception 
import Data.IORef 

incr ref = modifyIORef ref (+1)

(#=) ref val = modifyIORef ref (\ _ -> val)

test ref f = do 
  val <- readIORef ref
  return (f val)

data ForBreakException = ForBreakException deriving (Typeable,Show)

instance Exception ForBreakException 

foreach :: [a] -> (a -> IO b) -> IO ()
foreach l f = mapM_ f l `catch` \ (e :: ForBreakException) -> return ()

forbreak = throwIO ForBreakException

while test action = do
  val <- test
  if val 
    then do 
      action
      while test action
    else return ()
