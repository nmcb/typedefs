module TermCodec

import Data.Vect
import Data.Vect.Quantifiers

import Typedefs
import Types

%default total
%access public export

serialize : {ts : Vect n Type} -> All Show ts -> (t : TDef n) -> (tm : Ty ts t) -> String
serialize                        _          T1                   ()                      = 
  "()"
serialize                        sh        (TSum [x,y])          (Left l)                = 
  "(left " ++ serialize sh x l ++ ")"
serialize                        sh        (TSum [x,y])          (Right r)               = 
  "(right " ++ serialize sh y r ++ ")"
serialize                        sh        (TSum (x::y::z::zs))  (Left l)                = 
  "(left " ++ serialize sh x l ++ ")"
serialize                        sh        (TSum (x::y::z::zs))  (Right r)               = 
  "(right " ++ serialize sh (TSum (y::z::zs)) r ++ ")"
serialize                        sh        (TProd [x,y])         (a, b)                  = 
  "(both " ++ serialize sh x a ++ " " ++ serialize sh y b ++ ")"
serialize                        sh        (TProd (x::y::z::zs)) (a, b)                  = 
  "(both " ++ serialize sh x a ++ " " ++ serialize sh (TProd (y::z::zs)) b ++ ")"
serialize             {ts=t::ts} (sh :: _) (TVar FZ)             tm                      = 
  show tm
serialize {n=S Z}     {ts=_::_}  _         (TVar (FS x))         _                       = 
  absurd x
serialize {n=S (S n)} {ts=t::ts} (_ :: st) (TVar (FS x))         tm                      = 
  serialize st (TVar x) tm
serialize                        sh        (TMu nm [])           (Inn x)                 = 
  absurd x
serialize                        sh        (TMu nm [(nm1, td)])                  (Inn x) = 
  "(" ++ nm ++ " " ++ "(" ++ nm1 ++ ?wat "" "))"
serialize                        sh        (TMu nm ((nmx, tdx)::(nmy, tdy)::ys)) (Inn x) = 
  "(" ++ nm ++ " " ++ ?wat2

--deserialise : String -> (t:Ty ** tau t)