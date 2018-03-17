module Simple where

data Void

type Var = Int 
type TVar = Int
type Name = String
type Fun = String
data Type = One 
          | TV TVar
          | And Type Type 
          | Or Type Type 
          | Imp Type Type
          | All Name Type 
          | Mu Name Type
          | Nu Name Type deriving Show

instance Eq Type where 
    (==) One One = True 
    (==) (TV i) (TV j) = i == j
    (==) (And s t) (And u v) = s == u && t == v
    (==) (Or s t) (Or u v) =  s == u && t == v
    (==) (Imp s t) (Imp u v) = s == u && t == v
    (==) (All _ t) (All _ s) = t == s
    (==) (Nu _ t) (Nu _ s) = t == s
    (==) (Mu _ t) (Mu _ s) = t == s
    (==) _ _ = False

data Term = V Var
          | F Fun
          | Unit
          | App Term Term
          | TApp Term Type
          | Pair Term Term
          | Inl Term Type
          | Inr Term Type
          | Fold Term Type 
          | Unfold Term Type
          | Case Term Name Term Name Term 
          | Split Term Name Name Term
          | Lambda Name Type Term 
          | TLambda Name Term 
            deriving Show

instance Eq Term where 
    (==) (V i) (V j) = i == j 
    (==) (F f) (F g) = f == g 
    (==) Unit Unit = True
    (==) (App f t) (App g s) = f == g && t == s
    (==) (TApp t ty1) (TApp s ty2) = t == s && ty1 == ty2 
    (==) (Pair a b) (Pair c d) = a == c && b == d
    (==) (Inl a ty1) (Inl b ty2) = a == b && ty1 == ty2 
    (==) (Inr a ty1) (Inr b ty2) = a == b && ty1 == ty2 
    (==) (Fold a ty1) (Fold b ty2) = a == b && ty1 == ty2 
    (==) (Unfold a ty1) (Unfold b ty2) = a == b && ty1 == ty2
    (==) (Case t1 _ s1 _ r1) (Case t2 _ s2 _ r2) = 
         t1 == t2 && s1 == s2 && r1 == r2
    (==) (Split t1 _ _ s1) (Split t2 _ _ s2) = t1 == t2 && s1 == s2
    (==) (Lambda _ ty1 t1) (Lambda _ ty2 t2) = ty1 == ty2 && t1 == t2
    (==) (TLambda _ t1) (TLambda _ t2) = t1 == t2
    (==) _ _ = False

type TypeCtx = [Name] 
type VarCtx = [(Name,Type)]
type FunCtx = [(Name,Term,Type)] 
data Holds = H TypeCtx VarCtx FunCtx Term Type 
             deriving Show

data Proof a = UnitRule Holds 
             | VarRule Holds
             | FunRule Holds
             | AndIntro Holds a a
             | OrIntroL Holds a
             | OrIntroR Holds a
             | ImpIntro Holds a
             | MuIntro Holds a
             | NuIntro Holds a
             | AllIntro Holds a
             | AndElim Holds a a
             | OrElim Holds a a a
             | MuElim Holds a
             | NuElim Holds a
             | ImpElim Holds a a
             | AllElim Holds a
               deriving Show

data Cyc f a = Var a
             | RIn (f (Cyc f (Maybe a)))

instance Functor Proof where 
    fmap f (UnitRule h) = UnitRule h
    fmap f (VarRule h) = VarRule h
    fmap f (FunRule h) = FunRule h
    fmap f (AndIntro h x y) = AndIntro h (f x) (f y)
    fmap f (OrIntroL h x) = OrIntroL h (f x)    
    fmap f (OrIntroR h x) = OrIntroR h (f x)
    fmap f (ImpIntro h x) = ImpIntro h (f x)
    fmap f (MuIntro h x) = MuIntro h (f x)
    fmap f (NuIntro h x) = NuIntro h (f x)
    fmap f (AllIntro h x) = AllIntro h (f x)
    fmap f (AndElim h x y) = AndElim h (f x) (f y)
    fmap f (OrElim h x y z) = OrElim h (f x) (f y) (f z) 
    fmap f (MuElim h x) = MuElim h (f x) 
    fmap f (NuElim h x) = NuElim h (f x)
    fmap f (ImpElim h x y) = ImpElim h (f x) (f y)
    fmap f (AllElim h x) = AllElim h (f x)

shift :: Functor f => Cyc f a -> Cyc f (Maybe a)
shift (Var a) = Var (Just a) 
shift (RIn x) = RIn (fmap shift x)

cin :: Functor f => f (Cyc f Void) -> Cyc f Void
cin = RIn . fmap shift

type CProof = Cyc Proof 

class (Functor f, Functor g) => Ctx f g | f -> g where 
    distCtx :: f x -> f (g x, x) 
    combCtx :: g x -> x -> f x

data ProofCtx x = AndIntroCtxL Holds x 
                | AndIntroCtxR Holds x
                | OrIntroLCtx Holds
                | OrIntroRCtx Holds
                | ImpIntroCtx Holds
                | MuIntroCtx Holds 
                | NuIntroCtx Holds 
                | AllIntroCtx Holds 
                | AndElimCtxL Holds x 
                | AndElimCtxR Holds x 
                | OrElimCtxT Holds x x
                | OrElimCtxL Holds x x
                | OrElimCtxR Holds x x
                | MuElimCtx Holds 
                | NuElimCtx Holds 
                | ImpElimCtxL Holds x
                | ImpElimCtxR Holds x
                | AllElimCtx Holds
                  deriving Show 

instance Functor ProofCtx where 
    fmap f (AndIntroCtxL h x) = AndIntroCtxL h (f x)
    fmap f (AndIntroCtxR h x) = AndIntroCtxR h (f x)
    fmap f (OrElimCtxT h x y) = OrElimCtxT h (f x) (f y) 
    fmap f (OrElimCtxL h x y) = OrElimCtxL h (f x) (f y)
    fmap f (OrElimCtxR h x y) = OrElimCtxR h (f x) (f y) 
    fmap f (ImpElimCtxL h x) = ImpElimCtxL h (f x)
    fmap f (ImpElimCtxR h x) = ImpElimCtxR h (f x)
    fmap f (OrIntroLCtx h) = OrIntroLCtx h
    fmap f (OrIntroRCtx h) = OrIntroRCtx h
    fmap f (ImpIntroCtx h) = ImpIntroCtx h
    fmap f (MuIntroCtx h) = MuIntroCtx h
    fmap f (NuIntroCtx h) = NuIntroCtx h
    fmap f (AllIntroCtx h) = AllIntroCtx h
    fmap f (MuElimCtx h) = MuElimCtx h
    fmap f (NuElimCtx h) = NuElimCtx h
    fmap f (AllElimCtx h) = AllElimCtx h

instance Ctx Proof ProofCtx where 
    distCtx (UnitRule h) = UnitRule h
    distCtx (VarRule h) = VarRule h
    distCtx (FunRule h) = FunRule h
    distCtx (OrIntroL h x) = OrIntroL h (OrIntroLCtx h,x)
    distCtx (OrIntroR h x) = OrIntroR h (OrIntroRCtx h,x)
    distCtx (ImpIntro h x) = ImpIntro h (ImpIntroCtx h, x)
    distCtx (MuIntro h x) = MuIntro h (MuIntroCtx h, x)
    distCtx (NuIntro h x) = NuIntro h (NuIntroCtx h, x)
    distCtx (AllIntro h x) = AllIntro h (AllIntroCtx h, x)
    distCtx (MuElim h x) = MuElim h (MuElimCtx h, x)
    distCtx (NuElim h x) = NuElim h (NuElimCtx h, x)
    distCtx (AllElim h x) = AllElim h (AllElimCtx h, x)
    distCtx (AndIntro h x y) = AndIntro h (AndIntroCtxL h y,x) (AndIntroCtxR h x,y)
    distCtx (AndElim h x y) = AndElim h (AndElimCtxL h y,x) (AndElimCtxR h x, y)
    distCtx (ImpElim h x y) = ImpElim h (ImpElimCtxL h y,x) (ImpElimCtxR h x,y)
    distCtx (OrElim h x y z) = OrElim h (OrElimCtxT h y z,x) (OrElimCtxL h x z, y) (OrElimCtxR h x y, z)

    combCtx (AndIntroCtxL h y) x = AndIntro h x y
    combCtx (AndIntroCtxR h x) y = AndIntro h x y
    combCtx (OrElimCtxT h x y) t = OrElim h t x y
    combCtx (OrElimCtxL h t y) x = OrElim h t x y
    combCtx (OrElimCtxR h t x) y = OrElim h t x y
    combCtx (ImpElimCtxL h y) x = ImpElim h x y
    combCtx (ImpElimCtxR h x) y = ImpElim h x y
    combCtx (AndElimCtxL h y) x = AndElim h x y
    combCtx (AndElimCtxR h x) y = AndElim h x y
    combCtx (OrIntroLCtx h) x = OrIntroL h x
    combCtx (OrIntroRCtx h) x = OrIntroR h x
    combCtx (ImpIntroCtx h) x = ImpIntro h x 
    combCtx (MuIntroCtx h) x = MuIntro h x
    combCtx (AllIntroCtx h) x = AllIntro h x
    combCtx (MuElimCtx h) x = MuElim h x
    combCtx (NuElimCtx h) x = NuElim h x
    combCtx (AllElimCtx h) x = AllElim h x


               