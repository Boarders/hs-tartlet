{
module Core.Parser.Parse ( parseExpr ) where

import Core.Parser.Token
import Core.Parser.Helper
import Core.Parser.SrcLoc
import Core.Expression (RawExpr(..))
import qualified Core.Expression as Expr
import qualified Core.Quantity as Quantity

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
    one       { Token _ One          }
    inf       { Token _ Inf          }
    natzero   { Token _ NatZero      }
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
         : '(' Quantity var ann InfExpr ')' arr  ArrExpr
             { Expr.SrcPosR (tokSrcPos $3)
               (PiR (Expr.BindInfo (getVar $3) $2) $5 $8) }
         | Atom arr ArrExpr
             { (PiR Expr.dummyBindInfo $1 $3) }
         | '(' Quantity var ann InfExpr ')' prod ArrExpr
             { Expr.SrcPosR (tokSrcPos $1)
               (SigmaR (Expr.BindInfo (getVar $3) $2) $5 $8) }
         | InfExpr { $1 }

InfExpr :: { Expr.RawExpr }
         : add1 InfExpr           { Add1R $2 }
         | cons InfExpr InfExpr   { ConsR $2 $3 }
         | car InfExpr            { Expr.SrcPosR (tokSrcPos $1) (CarR $2) }
         | cdr InfExpr            { Expr.SrcPosR (tokSrcPos $1) (CdrR $2) }
         | fun var '=>' InfExpr   { Expr.SrcPosR (tokSrcPos $1) (LamR (getVar $2) $4) }
         | eq InfExpr InfExpr InfExpr
             { Expr.SrcPosR (tokSrcPos $1) (EqualR $2 $3 $4 ) }
         | indabsurd InfExpr ArrExpr
             { Expr.SrcPosR (tokSrcPos $1) (IndAbsurdR $2 $3) }
         | AppSpine
             { $1 }
         | trans InfExpr InfExpr InfExpr
             { Expr.SrcPosR (tokSrcPos $1) (ReplaceR $2 $3 $4) }
         | indnat InfExpr InfExpr InfExpr InfExpr
             { Expr.SrcPosR (tokSrcPos $1) (IndNatR $2 $3 $4 $5) }

AppSpine :: { Expr.RawExpr }
          : AppSpine Atom { AppR $1 $2 }
          | Atom { $1 }

Atom :: { Expr.RawExpr }
      : '(' AnnExpr ')' { $2 }
      | var          { Expr.SrcPosR (tokSrcPos $1) (LocR  (getVar $1)) }
      | natzero      { Expr.SrcPosR (tokSrcPos $1) ZeroR    }
      | tt           { Expr.SrcPosR (tokSrcPos $1) SoleR    }
      | refl         { Expr.SrcPosR (tokSrcPos $1) SameR    }
      | nat          { Expr.SrcPosR (tokSrcPos $1) NatR     }
      | univ         { Expr.SrcPosR (tokSrcPos $1) UnivR    }
      | absurd       { Expr.SrcPosR (tokSrcPos $1) AbsurdR  }
      | unit         { Expr.SrcPosR (tokSrcPos $1) UnitR    }
      | atom         { Expr.SrcPosR (tokSrcPos $1) AtomR    }
      | tick         { Expr.SrcPosR (tokSrcPos $1) (TickR (getTick $1)) }


Quantity :: { Quantity.Quantity }
      : zero  { Quantity.Zero }
      | one   { Quantity.One  }
      | inf   { Quantity.Inf  }
