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
    '(' { Token _ LeftBracket  }
    ')' { Token _ RightBracket }
    var { Token _ Var Chars    }
    ann { Token _ Ann          }
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
    tick      { Token _ Tick String  }
    univ      { Token _ Univ         }
%%

Exp :: {E
