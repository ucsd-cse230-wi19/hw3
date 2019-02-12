{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Hw3 where 

import           Prelude hiding ((++), const, sum) 
import           ProofCombinators
import qualified State as S 

--------------------------------------------------------------------------------
-- | Arithmetic Expressions 
--------------------------------------------------------------------------------

type Vname = String

data AExp  
  = N Val 
  | V Vname 
  | Plus AExp AExp 
  deriving (Show)

type Val   = Int 
type State = S.GState Vname Val 

{-@ reflect aval @-}
aval                :: AExp -> State -> Val 
aval (N n) _        = n 
aval (V x) s        = S.get s x 
aval (Plus e1 e2) s = aval e1 s + aval e2 s


---------------------------------------------------------------------------------------
-- | Q1: Prove `asimp_const` folds *all* subexpressions of the form `Plus (N i) (N j)`. 
--------------------------------------------------------------------------------

-- | `is_opt` checks whether an expression is indeed is_opt, i.e. has no `i + j` sub-terms.

{-@ measure is_opt @-}
is_opt :: AExp -> Bool
is_opt (N _) = True
is_opt (V _) = True
is_opt (Plus a1 a2) = is_opt a1 && is_opt a2 && not (const a1 && const a2)

{-@ measure const @-}
const :: AExp -> Bool
const (N _) = True
const _     = False

-- | `asimp_const` the constant-folding function we saw in class

{-@ reflect asimp_const @-}
asimp_const :: AExp -> AExp 
asimp_const (N n) = N n
asimp_const (V x) = V x  
asimp_const (Plus a1 a2) = case (asimp_const a1, asimp_const a2) of 
  (N n1, N n2) -> N (n1 + n2) 
  (b1  , b2)   -> Plus b1 b2

-- | Complete the proof of lem_is_opt which states that `is_opt (asimp_const a)`

{-@ lem_is_opt :: a:_ -> { is_opt (asimp_const a) } @-}
lem_is_opt :: AExp -> Proof 
lem_is_opt a = impossible "TBD" 

--------------------------------------------------------------------------------
-- | Q2: Next we will do a more serious transformation where expressions like 
--         `(x + 2) + (y + 5)` 
--       into a "normal form" that looks like  
--         `x + (y + 7)` 
--       That is into a sum of variables plus with all the constants at the end. 
--------------------------------------------------------------------------------

-- | An expression is in normal form if every LHS of an addition is a `Var`
{-@ measure is_normal @-}
is_normal :: AExp -> Bool 
is_normal (Plus a1 a2) = is_var a1 && is_normal a2 
is_normal a            = True 

{-@ measure is_var @-}
is_var :: AExp -> Bool 
is_var (V _) = True 
is_var _     = False 

-- | An `NAExp` is the subset of `AExp` that are in *Normal Form* 

{-@ type NAExp = {a:AExp | is_normal a} @-}

-- | Complete the definition of the function `full_asimp` that takes an `AExp` 
--   and returns an equivalent version that is in Normal Form.

{-@ reflect full_asimp @-}
{-@ full_asimp :: AExp -> NAExp @-} 
full_asimp :: AExp -> AExp 
full_asimp a = V "TBD"  -- <<< Replace this with something that works

-- | Prove that your `full_asimp` yields an expression equivalent to its input.
{-@ lem_full_asimp :: a:_ -> s:_ -> { aval a s == aval (full_asimp a) s } @-}
lem_full_asimp :: AExp -> State -> Proof
lem_full_asimp a s = impossible "TBD" 

-- HINT: You will likely need helper functions to define `full_asimp` and helper 
--       lemmas to prove properties of those helper functions.

--------------------------------------------------------------------------------
-- | Q3:  Substitution `subst x a e` replaces all occurrences of variable `x` by 
--        an expression `a` in an expression `e`
--------------------------------------------------------------------------------

{-@ reflect subst @-}
subst :: Vname -> AExp -> AExp -> AExp 
subst x a (Plus e1 e2)   = Plus (subst x a e1) (subst x a e2) 
subst x a (V y) | x == y = a 
subst _ _ e              = e 

-- Prove the so-called "substitution lemma" that says that we can 
-- either substitute first and evaluate afterwards or evaluate with 
-- an updated state: 

{-@ reflect asgn @-}
asgn :: State -> Vname -> AExp -> State
asgn s x a = S.set s x (aval a s)

{-@ lem_subst :: x:_ -> a:_ -> e:_ -> s:_ -> 
       { aval (subst x a e) s == aval e (asgn s x a) } 
  @-}
lem_subst :: Vname -> AExp -> AExp -> State -> Proof
lem_subst = impossible "TBD"

-- HINT: You may find  `S.lemma_get_set` and `S.lemma_get_not_set` useful.

--------------------------------------------------------------------------------
-- | Q4: Let-binders: Consider the following expression language that 
--       extends AExp with let-bound variables, so you can write expressions

--         let x = 10 
--             y = x + 5
--         in  x + y 

--       which should evaluate to 25
--------------------------------------------------------------------------------

data LExp 
  = LN    Int                 -- ^ Numbers 
  | LV    Vname               -- ^ Variables
  | LPlus LExp  LExp          -- ^ Addition
  | LLet  Vname LExp LExp     -- ^ Let binding
  deriving (Show)

-- | `lval l s` takes a let-bound expression and a State and returns the result 
--    of evaluating `l` in `s`: 

{-@ reflect lval @-}
lval :: LExp -> State -> Int 
lval (LN i) _         = i 
lval (LV x) s         = S.get s x 
lval (LPlus e1 e2)  s = lval e1 s + lval e2 s 
lval (LLet x e1 e2) s = lval e2 (S.set s x (lval e1 s)) 

-- | Write a function `inlyne` that converts an `LExp` into a plain `AExp` 
--   by "inlining" the let-definitions, i.e. `let x = e1 in e2` should become 
--     e2-with-all-occurrences-x-replaced-by-e1 

{-@ reflect inlyne @-}
inlyne :: LExp -> AExp 
inlyne l = V "TBD" -- <<<< replace this with proper implementation

-- | Prove that your `inlyne` function is correct.
{-@ lem_inlyne :: l:_ -> s:_ -> { lval l s = aval (inlyne l) s } @-} 
lem_inlyne :: LExp -> State -> Proof 
lem_inlyne = impossible "TODO"

--------------------------------------------------------------------------------
-- | Q5: Negation Normal Form (*) 
--------------------------------------------------------------------------------

-- The following datatype represents Boolean propositions

data Pred 
  = Var Vname           -- ^ x, y, z    variables 
  | Not Pred            -- ^ ~ p        negation
  | Or  Pred Pred       -- ^ p1 \/ p2   disjunction
  | And Pred Pred       -- ^ p1 /\ p2   conjunction
  deriving (Show)

-- | A @Pred@ is in *Negation Normal Form* if all occurrences of `Not` 
--   are only one variables, so 
--        not (x /\ y) 
--   IS NOT in NNF but instead 
--        not x \/ not y  
--   is an equivalent formula that IS in NNF. 

{-@ type NNF = {v:Pred | isNNF v} @-}

{-@ measure isNNF @-}
isNNF :: Pred -> Bool 
isNNF (Var _)   = True 
isNNF (And p q) = isNNF p && isNNF q 
isNNF (Or  p q) = isNNF p && isNNF q 
isNNF (Not p)   = isVar p 

{-@ measure isVar @-}
isVar :: Pred -> Bool 
isVar (Var _) = True 
isVar _       = False 

-- | A `BState` maps each variable to a Bool

type BState = S.GState Vname Bool

-- | `pval p s` evaluates a @Pred@ in a given `BState` 

{-@ reflect pval @-}
pval :: Pred -> BState -> Bool
pval (Var x)     s = S.get s x 
pval (And p1 p2) s = (pval p1 s) && (pval p2 s) 
pval (Or  p1 p2) s = (pval p1 s) || (pval p2 s)
pval (Not p)     s = not (pval p s)

-- | Write a function `nnf` that converts a `Pred` to its NNF form:

{-@ reflect nnf @-}
{-@ nnf :: Pred -> NNF @-} 
nnf :: Pred -> Pred 
nnf p = Var "TBD"   --  <<<<< replace with actual implementation

-- HINT: you may need a mutually recursive helper function that 
--       converts a "negative" predicate (i.e. one that occurs 
---      under a `Not` to its NNF variant)

-- | Complete the proof of `lem_nnf` to prove that your `nnf` is correct

{-@ lem_nnf :: s:_ -> p:_ -> { pval p s = pval (nnf p) s } @-}
lem_nnf :: BState -> Pred -> Proof 
lem_nnf s p = impossible "TODO" 

-- HINT: You may need to prove a suitable lemma about your mutually recursive helper.
