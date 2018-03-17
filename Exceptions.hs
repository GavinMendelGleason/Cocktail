module Exceptions where 

import Control.Monad.Error 

maybeToError x e = maybe (throwError e) return x

eitherToMaybe (Left e) = Nothing
eitherToMaybe (Right x) = Just x

eitherToList (Left e) = [] 
eitherToList (Right x) = [x]
                    
fromEither (Left e) = error $ e
fromEither (Right x) = x