module CList where

data Void

void :: Void -> a
void _ = error "I will never be here"

instance Show Void where 
    show = void

data CList a = Var a
             | Nil
             | Cons Int (CList (Maybe a)) deriving Show

shift :: CList a -> CList (Maybe a)
shift (Var a) = Var (Just a) 
shift Nil = Nil 
shift (Cons x l) = Cons x (shift l)

ccons :: Int -> CList Void -> CList Void 
ccons x xs = Cons x (shift xs)

clist1 = Cons 1 (Cons 2 (Var Nothing))
clist2 = Cons 1 (Cons 2 (Cons 3 (Var (Just Nothing))))

chead :: CList Void -> Int
chead (Var a) = void a
chead (Cons x xs) = x

ctail :: CList Void -> CList Void
ctail (Var z) = void z
ctail (Cons x xs) = csnoc x xs

csnoc :: Int -> CList (Maybe a) -> CList a
csnoc y (Var Nothing) = Cons y (Var Nothing)
csnoc y (Var (Just z)) = Var z
csnoc y Nil = Nil
csnoc y (Cons x xs) = Cons x (csnoc y xs)




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

-}