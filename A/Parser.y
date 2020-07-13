{
module Parser where
import Lexer
}

%name parser
%tokentype { Token }
%error { parseError }

%token
    var                 { TVariable $$ }
    "->"                { TImplication }
    '|'                 { TDisjunction }
    '&'                 { TConjunction }
    '!'                 { TNegation }
    '('                 { TOpeningBracket }
    ')'                 { TClosingBracket }

%%

Expression  : Disjunction                                 { Disjunction $1 }
            | Disjunction "->" Expression                 { Implication $1 $3 }

Disjunction : Conjunction                                 { Conjunction $1 }
            | Disjunction '|' Conjunction                 { Disj $1 $3 }

Conjunction : Negation                                    { Negation $1 }
            | Conjunction '&' Negation                    { Conj $1 $3 }

Negation    : '!' Negation                                { NegationNot $2 }
            | var                                         { Variable $1 }
            | '(' Expression ')'                          { Expression $2 }

{
parseError :: [Token] -> a
parseError _ = error "Parse error"

data Expression
    = Disjunction Disjunction
    | Implication Disjunction Expression

data Disjunction
    = Conjunction Conjunction
    | Disj Disjunction Conjunction

data Conjunction
    = Negation Negation
    | Conj Conjunction Negation

data Negation
    = NegationNot Negation
    | Variable String
    | Expression Expression

instance Show Expression where
    show (Disjunction expression)       = (show expression)
    show (Implication left right)       = "(->," ++ (show left) ++ "," ++ (show right) ++ ")"

instance Show Disjunction where
    show (Conjunction expression)       = (show expression)
    show (Disj left right)              = "(|," ++ (show left) ++ "," ++ (show right) ++ ")"

instance Show Conjunction where
    show (Negation expression)          = (show expression)
    show (Conj left right)              = "(&," ++ (show left) ++ "," ++ (show right) ++ ")"

instance Show Negation where
    show (NegationNot expression)       = "(!" ++ (show expression) ++ ")"
    show (Variable variable)            = variable
    show (Expression expression)        = (show expression)
}
