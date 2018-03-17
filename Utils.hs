module Utils where

ith :: Int -> [a] -> Maybe a
ith i [] = Nothing
ith i (h:t) = if i == 0 
              then Just h 
              else ith (i-1) t
