{
module Core.Parser.Parse ( parseExpr ) where

import Core.Parser.Token
import Core.Parser.Helper
import Core.Expression (RawExpr(..))
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

AnnExpr :: { Expr.RawExpr }
         : ArrExpr { $1 }
         | ArrExpr ann ArrExpr { TheR $1 $3 }

ArrExpr :: { Expr.RawExpr }
         : '(' var ann InfExpr ')' arr  ArrExpr { PiR $2 $4 $7 }
         | Atom arr ArrExpr {PiR Expr.dummyVar $1 $3}
         | '(' var ann InfExpr ')' prod ArrExpr  { SigmaR $2 $4 $7 }
         | InfExpr { $1 }

InfExpr :: { Expr.RawExpr }
         : add1 InfExpr { Add1R $2 }
         | cons InfExpr InfExpr { ConsR $2 $3 }
         | car InfExpr { CarR $2 }
         | cdr InfExpr { CdrR  $2 }
         | fun var '=>' InfExpr { LamR $2 $4 }
         | indnat InfExpr InfExpr InfExpr InfExpr { IndNatR $2 $3 $4 $5 }
         | trans InfExpr InfExpr InfExpr { ReplaceR $2 $3 $4 }
         | eq InfExpr InfExpr InfExpr { EqualR $2 $3 $4 }
         | indabsurd InfExpr ArrExpr { IndAbsurdR $2 $3}
         | AppSpine { $1 }

AppSpine :: { Expr.RawExpr }
          : AppSpine Atom { AppR $1 $2 }
          | Atom { $1 }

Atom :: { Expr.RawExpr }
      : '(' AnnExpr ')' { $2 }
      | var          { LocR $1 }
      | zero         { ZeroR }
      | tt           { SoleR }
      | refl         { SameR }
      | nat          { NatR }
      | univ         { UnivR }
      | absurd       { AbsurdR }
      | unit         { UnitR }
      | atom         { AtomR }
      | tick         { TickR $1 }

{}
