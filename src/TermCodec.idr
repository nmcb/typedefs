module TermCodec

import Data.Vect
import Data.Vect.Quantifiers

import Typedefs
import Types

%default total
%access public export

interface AllShow (f : Vect n Type) where
  provide : All Show f

mutual
  AllShow ts => Show (Mu ts td) where
    show @{as} {ts} {td} (Inn x) = assert_total $ serialize {ts = Mu ts td :: ts } (%implementation :: provide @{as}) td x 

  
  serialize : {ts : Vect n Type} -> All Show ts -> (t : TDef n) -> (tm : Ty ts t) -> String
  serialize                        _          T1                                  ()        = 
    "()"
  
  serialize                        sh        (TSum [x,y])                         (Left l)  = 
    "(left " ++ serialize sh x l ++ ")"
  
  serialize                        sh        (TSum [x,y])                         (Right r) = 
    "(right " ++ serialize sh y r ++ ")"
  
  serialize                        sh        (TSum (x::y::z::zs))                 (Left l)  = 
    "(left " ++ serialize sh x l ++ ")"
  
  serialize                        sh        (TSum (x::y::z::zs))                 (Right r) = 
    "(right " ++ serialize sh (TSum (y::z::zs)) r ++ ")"
  
  serialize                        sh        (TProd [x,y])                        (a, b)    = 
    "(both " ++ serialize sh x a ++ " " ++ serialize sh y b ++ ")"
  
  serialize                        sh        (TProd (x::y::z::zs))                (a, b)    = 
    "(both " ++ serialize sh x a ++ " " ++ serialize sh (TProd (y::z::zs)) b ++ ")"
  
  serialize             {ts=t::ts} (sh :: _) (TVar FZ)                             tm       = 
    show tm
  
  serialize {n=S Z}     {ts=_::_}  _         (TVar (FS x))                         _        = 
    absurd x
  
  serialize {n=S (S n)} {ts=t::ts} (_ :: st) (TVar (FS x))                         tm       = 
    serialize st (TVar x) tm
  
  serialize                        sh        (TMu nm [])                           (Inn x)  = 
    absurd x
  
  serialize                 {ts}   sh        (TMu nm [(nm1, td)])                  ix  = 
    show ix --serialize {ts = Mu ts td :: ts} (%implementation :: sh) td x
  
    --"(" ++ nm ++ " " ++ "(" ++ nm1 ++ ?wat ++ "))"
  
  serialize                        sh        (TMu nm [(nmx, tdx),(nmy, tdy)]) (Inn x)  = 
    ?wat8 --"(" ++ nm ++ " " ++ ?wat2
  
  serialize                        sh        (TMu nm ((nmx, tdx)::(nmy, tdy)::(nmz, tdz)::zs)) (Inn x)  = 
    ?wat9 --"(" ++ nm ++ " " ++ ?wat2
  
--deserialise : String -> (t:Ty ** tau t)
