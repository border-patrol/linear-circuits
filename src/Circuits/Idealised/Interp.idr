module Circuits.Idealised.Interp

import Decidable.Equality

import Data.List.Elem
import Data.List.Quantifiers

import Utilities
import EdgeBoundedGraph

import Circuits.Types
import Circuits.Idealised

%default total

public export
InterpTy : Ty -> Type
InterpTy Unit = Graph
InterpTy (Port x) = Vertex
InterpTy Gate = Graph

namespace Environments
  public export
  data Env : List (Ty, Usage) -> Type where
    Empty  : Env Nil
    Extend : InterpTy type -> Env rest -> Env ((type,usage) :: rest)

  export
  lookup : (envO  : Env old )
        -> (prf   : Elem (type,FREE) old)
        -> (which : Use old prf new)
        -> (Env new, InterpTy type)
  lookup (Extend x y) Here H = (Extend x y, x)
  lookup (Extend y z) (There later) (T x)
    = let (newEnv, res) = lookup z later x
      in (Extend y newEnv, res)


namespace Result

  public export
  data Result : (context : List (Ty, Usage))
             -> (type    : Ty)
                        -> Type
    where
      R : (counter : Nat)
       -> (env     : Env new)
       -> (result  : InterpTy type)
                  -> Result new type
  public export
  getResult : Result ctxt type -> InterpTy type
  getResult (R _ _ res) = res

interp : (env     : Env old)
      -> (term    : Term old type new)
      -> (counter : Nat)
      -> (graph   : Graph)
                 -> Result new type
interp env (Var prf x) counter graph
  = let (newEnv, res) = lookup env prf x
    in R counter newEnv res

interp env (NewSignal flow datatype body) counter graph
  = let n    = case flow of {INPUT => driver (S counter); OUTPUT => catcher (S counter)} in
    let env' = Extend n env in
    let g'   = insertNode n graph
    in interp env' body (S counter) g'

interp env (Wire datatype body) counter graph
  = let o = Node (S counter) 1 1 in
    let i = Node (S (S counter)) 1 1 in
    let env' = (Extend i (Extend o env)) in
    let g'   = foldr insertNode graph [o,i] in
    let g''  = insertEdge (S (S counter), S counter) g'
    in interp env' body (S (S counter)) g''

interp env (Mux output ctrl inA inB) counter graph
  = let R c'    env'    o = interp env    output  counter graph in
    let R c''   env''   c = interp env'   ctrl    c'      graph in
    let R c'''  env'''  a = interp env''  inA     c''     graph in
    let R c'''' env'''' b = interp env''' inB     c'''    graph in

    let n   = Node (S c'''') 3 1 in
    let g' = insertNode n graph  in

    let es = [ (ident a, S c''''), (ident b, S c'''')
             , (ident c, S c'''')
             , (S c'''', ident o)
             ]
    in R (S c'''') env'''' (foldr (insertEdge) g' es)

interp env (Dup outputA outputB input) counter graph
  = let R c'   env'   a = interp env   outputA counter graph in
    let R c''  env''  b = interp env'  outputB c'      graph in
    let R c''' env''' i = interp env'' input   c''     graph in
    let n               = Node (S c''') 1 2                  in
    let g'              = insertNode n graph                 in
    let es              = [ (ident i, S c''')
                          , (S c''', ident a)
                          , (S c''', ident b)
                          ]
    in R (S c''') env''' (foldr (insertEdge) g' es)

interp env (Seq x y) counter graph
  = let R c' env' x' = interp env x counter graph
    in interp env' y c' x'

interp env (Not output input) counter graph
  = let R c'  env'  o = interp env  output counter graph in
    let R c'' env'' i = interp env' input  c'      graph in

    let n  = Node (S c'') 1 1         in
    let g' = insertNode n  graph in
    let es = [(S c'', ident o),(ident i, S c'')]
    in R (S c'') env'' (foldr insertEdge g' es)


interp env (Gate k output inputA inputB) counter graph
  = let R c'   env'   o = interp env   output counter graph in
    let R c''  env''  a = interp env'  inputA c'      graph in
    let R c''' env''' b = interp env'' inputB c''     graph in
    let n               = Node (S c''') 2 1                  in
    let g'              = insertNode n graph                in
    let es              = [ (S c''', ident o)
                          , (ident a, S c''')
                          , (ident b, S c''')
                          ]
    in R (S c''') env''' (foldr (insertEdge) g' es)

interp env (IndexSingleton o i) counter graph
  = let R c'   env'   o = interp env   o counter graph in
    let R c''  env''  i = interp env'  i c'      graph in
    let c''' = S c'' in
    let n    = Node c''' 1 1 in
    let g'   = insertNode n graph in
    let es   = [ (ident i, c''')
               , (c'''   , ident o)
               ]
    in R c''' env'' (foldr insertEdge g' es)

interp env (IndexEdge p idx oused ofree i) counter graph
  = let R c'    env'    oused = interp env    oused counter graph in
    let R c''   env''   ofree = interp env'   ofree c'      graph in
    let R c'''  env'''  input = interp env''  i     c''     graph in

    let c'''' = S c''' in
    let n     = Node c'''' 1 2 in
    let g'    = insertNode n graph in
    let es    = [ (ident input, c'''')
               , (c''''       , ident oused)
               , (c''''       , ident ofree)
               ]
    in R c'''' env''' (foldr insertEdge g' es)


interp env (IndexSplit p idx used freeA freeB i) counter graph
  = let R c'     env'     oused = interp env    used  counter graph in
    let R c''    env''    freeA = interp env'   freeA c'      graph in
    let R c'''   env'''   freeB = interp env''  freeB c''     graph in
    let R c''''  env''''  input = interp env''' i     c'''    graph in

    let c''''' = S c'''' in
    let n      = Node c''''' 1 3 in
    let g'     = insertNode n graph in
    let es     = [ (ident input  , c''''')
                 , (c'''''       , ident oused)
                 , (c'''''       , ident freeA)
                 , (c'''''       , ident freeB)
                 ]
    in R c''''' env'''' (foldr insertEdge g' es)

interp env (Stop x) counter graph
  = R counter Empty graph

public export
data Valid : (type : Ty) -> InterpTy type -> Type where
  P : Valid (Port x) v
  G : (g : Graph) -> ValidGraph g -> Valid Gate g
  D : (g : Graph) -> ValidGraph g -> Valid Unit g

isValid : {type : Ty}
        -> (g   : InterpTy type)
               -> Dec (Valid type g)
isValid g {type = Unit} with (validGraph g)
  isValid g {type = Unit} | (Yes prf)
    = Yes (D g prf)
  isValid g {type = Unit} | (No contra)
    = No (\(D g prf) => contra prf)
isValid g {type = (Port x)} = Yes P
isValid g {type = Gate} with (validGraph g)
  isValid g {type = Gate} | (Yes prf)
    = Yes (G g prf)
  isValid g {type = Gate} | (No contra)
    = No (\(G g prf) => contra prf)


export
run : (term : Term Nil Unit Nil)
           -> Dec (Valid Unit (getResult (interp Empty term Z (MkGraph Nil Nil))))
run term with (interp Empty term Z (MkGraph Nil Nil))
  run term | R cout eout gout with (validGraph gout)
    run term | R cout eout gout | (Yes prf)
      = Yes (D gout prf)
    run term | R cout eout gout | (No contra)
      = No (\(D g prf) => contra prf)

export
runIO : (term : Term Nil Unit Nil)
             -> IO (Maybe (g ** Valid Unit g))
runIO term with (interp Empty term Z (MkGraph Nil Nil))
  runIO term | (R counter env result) with (validGraph result)
    runIO term | (R counter Empty (MkGraph vs es)) | (Yes (IsValid x))
      = pure (Just ((MkGraph vs es) ** D (MkGraph vs es) (IsValid x)))
    runIO term | (R counter env result) | (No contra)
      = pure Nothing

-- [ EOF ]