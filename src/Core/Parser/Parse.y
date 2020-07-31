{
module Core.Parser.Parse

import Core.Parser.Token
import Core.Parser.Helper
import Core.Expression
}


%name parseExpr
%tokentype { Token }

%monad { Parser } { thenP } { returnP }
%lexer { lexer  } { Token _ EOF }

%token
    '('       { Token _ LeftBracket  }
    ')'       { Token _ RightBracket }
    var       { Token _ Var $$       }
    ann       { Token _ Ann          }
    arr       { Token _ Arr          }
    fun       { Token _ Fun          }
    =>        { Token _ MapsTo       }
    prod      { Token _ Star         }
    cons      { Token _ Cons         }
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
    tick      { Token _ Tick $$      }
    univ      { Token _ Univ         }
%%


Type :: { ParsedExpr }
      : nat                     { NatP }
      | univ                    { UP }
      | var ann Type prod Type  { SigmaP $1 $3 }
      | var ann Type arr Type   { PiP $1 $3 $5 }
      | var                     { VarP $1 }
      | eq Type Expr Expr       { EqualP $2 $3 $4 }

Expr :: {Expr}
      : tt   { Sole }
      | zero { Zero }
      | add1 Expr { Add1 $2 }
      | cons Expr { Cons $2 }
      | cdr Expr  { Cdr  $2 }
