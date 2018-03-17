data Void 

void :: Void -> a
void _ = error "I will never be here"

instance Show Void where 
    show = void

data CTree a = Var a
             | Leaf
             | Bin Int (CTree (Maybe a)) (CTree (Maybe a)) deriving Show

shiftT :: CTree a -> CTree (Maybe a)
shiftT (Var a) = Var (Just a) 
shiftT Leaf = Leaf
shiftT (Bin x xsL xsR) = Bin x (shiftT xsL) (shiftT xsR)

cbin :: Int -> CTree Void -> CTree Void -> CTree Void
cbin x xsL xsR = Bin x (shiftT xsL) (shiftT xsR)

csubL :: CTree Void -> CTree Void
csubL (Var a) = void a
csubL (Bin x xsL xsR) = csnocL x xsR xsL

csubR :: CTree Void -> CTree Void 
csubR (Var a) = void a
csubR (Bin x xsL xsR) = csnocR x xsL xsR

csnocL :: Int -> CTree (Maybe a) -> CTree (Maybe a) -> CTree a
csnocL y ys (Var Nothing) = Bin y (Var Nothing) ys
csnocL y ys (Var (Just z)) = Var z
csnocL y ys Leaf = Leaf
csnocL y ys (Bin x xsL xsR) = Bin x (csnocL y ys' xsL) (csnocL y ys' xsR)
                              where ys' = shiftT ys

csnocR :: Int -> CTree (Maybe a) -> CTree (Maybe a) -> CTree a
csnocR y ys (Var Nothing) = Bin y ys (Var Nothing)
csnocR y ys (Var (Just z)) = Var z
csnocR y ys Leaf = Leaf
csnocR y ys (Bin x xsL xsR) = Bin x (csnocR y ys' xsL) (csnocR y ys' xsR)
                              where ys' = shiftT ys

chead :: CTree Void -> Int
chead (Var a) = void a
chead (Bin x xsL xsR) = x

ctails :: CTree Void -> [CTree Void]
ctails t = [csubL t, csubR t]

tree1 = Bin 1 (Bin 2 (Var Nothing) Leaf) (Bin 3 Leaf (Var Nothing))

ctree = Bin 1 
        (Bin 2 (Bin 3 (Var Nothing) Leaf)
              Leaf)
        (Bin 4 (Bin 5 Leaf Leaf)
                  (Bin 6 Leaf Leaf))

{-
class (Functor f, Functor g) => Ctx f g | f -> g where 
    distCtx :: f x -> f (g x, x) 
    combCtx :: g x -> x -> f x

data ListCtx x = ConsCtx Int

instance Functor ListCtx where 
    fmap f (ConsCtx x) = ConsCtx x 

instance Ctx List ListCtx where 
    distCtx Nil = Nil 
    distCtx (Cons n l) = Cons n (ConsCtx n,l)

    combCtx (ConsCtx n) l = Cons n l

1. Write up type checker.
2. Start with initial term and perform supercompilation.
3. Check final proof. 

Supercompilation(t) := 



-}