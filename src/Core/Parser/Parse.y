{
module Core.Parser.Parse ( parseExpr ) where

import Core.Parser.Token
import Core.Parser.Helper
import Core.Parser.SrcLoc
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
    var       { Token _ (Var _)      }
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
    tick      { Token _ (Tick _)     }
    univ      { Token _ Univ         }
%%


AnnExpr :: { Expr.RawExpr }
         : ArrExpr { $1 }
         | ArrExpr ann ArrExpr { TheR $1 $3 }

ArrExpr :: { Expr.RawExpr }
         : '(' var ann InfExpr ')' arr  ArrExpr
             { Expr.SrcPos (tokSrcPos $2) (PiR (getVar $2) $4 $7) }
         | Atom arr ArrExpr
             { (PiR Expr.dummyVar $1 $3) }
         | '(' var ann InfExpr ')' prod ArrExpr
             { Expr.SrcPos (tokSrcPos $1) (SigmaR (getVar $2) $4 $7) }
         | InfExpr { $1 }

InfExpr :: { Expr.RawExpr }
         : add1 InfExpr           { Add1R $2 }
         | cons InfExpr InfExpr   { ConsR $2 $3 }
         | car InfExpr            { Expr.SrcPos (tokSrcPos $1) (CarR $2) }
         | cdr InfExpr            { Expr.SrcPos (tokSrcPos $1) (CdrR $2) }
         | fun var '=>' InfExpr   { Expr.SrcPos (tokSrcPos $1) (LamR (getVar $2) $4) }
         | eq InfExpr InfExpr InfExpr
             { Expr.SrcPos (tokSrcPos $1) (EqualR $2 $3 $4 ) }
         | indabsurd InfExpr ArrExpr
             { Expr.SrcPos (tokSrcPos $1) (IndAbsurdR $2 $3) }
         | AppSpine
             { $1 }
         | trans InfExpr InfExpr InfExpr
             { Expr.SrcPos (tokSrcPos $1) (ReplaceR $2 $3 $4) }
         | indnat InfExpr InfExpr InfExpr InfExpr
             { Expr.SrcPos (tokSrcPos $1) (IndNatR $2 $3 $4 $5) }

AppSpine :: { Expr.RawExpr }
          : AppSpine Atom { AppR $1 $2 }
          | Atom { $1 }

Atom :: { Expr.RawExpr }
      : '(' AnnExpr ')' { $2 }
      | var          { Expr.SrcPos (tokSrcPos $1) (LocR  (getVar $1)) }
      | zero         { Expr.SrcPos (tokSrcPos $1) ZeroR    }
      | tt           { Expr.SrcPos (tokSrcPos $1) SoleR    }
      | refl         { Expr.SrcPos (tokSrcPos $1) SameR    }
      | nat          { Expr.SrcPos (tokSrcPos $1) NatR     }
      | univ         { Expr.SrcPos (tokSrcPos $1) UnivR    }
      | absurd       { Expr.SrcPos (tokSrcPos $1) AbsurdR  }
      | unit         { Expr.SrcPos (tokSrcPos $1) UnitR    }
      | atom         { Expr.SrcPos (tokSrcPos $1) AtomR    }
      | tick         { Expr.SrcPos (tokSrcPos $1) (TickR (getTick $1)) }
