module Choice where

(|+|) :: [a] -> [a] -> [a]
(|+|) [] ys = ys
(|+|) xs [] = xs
(|+|) (x:xs) (y:ys) = x:y:(xs |+| ys)

(>>-) :: [a] -> (a -> [b]) -> [b]
(>>-) [] p = []
(>>-) (x:xs) p = p x |+| (xs >>- p)
