{
module Core.Parser.Parse ( parseExpr ) where

import Core.Parser.Token
import Core.Parser.Helper
import Core.Expression (ParsedExpr(..))
import qualified Core.Expression as Expr
}


%name parseExpr
%tokentype { Token }

%monad { Parser } { thenP } { returnP }
%lexer { lexer  } { Token _ EOF }

%token
    '('       { Token _ LeftBracket  }
    ')'       { Token _ RightBracket }
    var       { Token _ (Var $$)     }
    ann       { Token _ Ann          }
    arr       { Token _ Arr          }
    fun       { Token _ Fun          }
    '=>'      { Token _ MapsTo       }
    prod      { Token _ Star         }
    cons      { Token _ Cons         }
    car       { Token _ Car          }
    cdr       { Token _ Cdr          }
    nat       { Token _ Nat          }
    zero      { Token _ Zero         }
    add1      { Token _ Add1         }
    indnat    { Token _ IndNat       }
    eq        { Token _ Eq           }
    refl      { Token _ Refl         }
    trans     { Token _ Trans        }
    unit      { Token _ Unit         }
    tt        { Token _ TT           }
    absurd    { Token _ Absurd       }
    indabsurd { Token _ IndAbsurd    }
    atom      { Token _ Atom         }
    tick      { Token _ (Tick $$)    }
    univ      { Token _ Univ         }
%%

AnnExpr :: { Expr.ParsedExpr }
         : ArrExpr { $1 }
         | ArrExpr ann ArrExpr { TheP $1 $3 }

ArrExpr :: { Expr.ParsedExpr }
         : '(' var ann InfExpr ')' arr  ArrExpr { PiP $2 $4 $7 }
         | Atom arr ArrExpr {PiP Expr.dummyVar $1 $3}
         | '(' var ann InfExpr ')' prod ArrExpr  { SigmaP $2 $4 $7 }
         | InfExpr { $1 }

InfExpr :: { Expr.ParsedExpr }
         : add1 InfExpr { Add1P $2 }
         | cons InfExpr InfExpr { ConsP $2 $3 }
         | car InfExpr { CarP $2 }
         | cdr InfExpr { CdrP  $2 }
         | fun var '=>' InfExpr { LamP $2 $4 }
         | indnat InfExpr InfExpr InfExpr InfExpr { IndNatP $2 $3 $4 $5 }
         | trans InfExpr InfExpr InfExpr { ReplaceP $2 $3 $4 }
         | eq InfExpr InfExpr InfExpr { EqualP $2 $3 $4 }
         | indabsurd InfExpr ArrExpr { IndAbsurdP $2 $3}
         | AppSpine { $1 }

AppSpine :: { Expr.ParsedExpr }
          : AppSpine Atom { AppP $1 $2 }
          | Atom { $1 }

Atom :: { Expr.ParsedExpr }
      : '(' AnnExpr ')' { $2 }
      | var          { VarP $1 }
      | zero         { ZeroP }
      | tt           { SoleP }
      | refl         { SameP }
      | nat          { NatP }
      | univ         { UnivP }
      | absurd       { AbsurdP }
      | unit         { UnitP }
      | atom         { AtomP }
      | tick         { TickP $1 }

{}
