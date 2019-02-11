{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module State where

import Prelude hiding ((++), const, max)
import ProofCombinators

-- | A Generic "State"
data GState = GState 
  { sVals :: [(String, Int)] -- ^ binders and their values
  , sDef  :: Int             -- ^ default value (for missing binder)
  }  

{-@ reflect init @-}
init :: Int -> GState
init def = GState [] def 

{-@ reflect set @-}
set :: GState -> String -> Int -> GState 
set (GState kvs v0) k v = GState ((k,v) : kvs) v0 

{-@ reflect getDefault @-}
getDefault :: Int -> String -> [(String, Int)] -> Int 
getDefault v0 key ((k, v) : kvs) 
  | key == k          = v 
  | otherwise         = getDefault v0 key kvs 
getDefault v0 _ [] = v0 

{-@ lazy get @-}
{-@ reflect get @-}
get :: GState -> String -> Int 
get (GState []          v0) key = v0
get (GState ((k,v):kvs) v0) key = if key == k then v else get (GState kvs v0) key

{-@ lemma_get_set :: k:_ -> v:_ -> s:_ -> { get (set s k v) k == v }  @-}
lemma_get_set :: String -> Int -> GState -> Proof 
lemma_get_set _ _ _ = () 

{-@ lemma_get_not_set :: k0:_ -> k:{k /= k0} -> val:_ -> s:_ 
                      -> { get (set s k val) k0 = get s k0 }  @-}
lemma_get_not_set :: String -> String -> Int -> GState -> Proof 
lemma_get_not_set _ _ _ (GState {}) = ()
