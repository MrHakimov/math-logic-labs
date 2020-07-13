{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE Strict #-}
{
module Parser where
import Lexer
}

%name parser Expression
%name parseStatement Statement
%tokentype { Token }
%error { parseError }

%token
    var                 { TVariable $$ }
    pre                 { TPredicate $$ }
    "|-"                { TCarriage }
    "->"                { TImplication }
    '|'                 { TDisjunction }
    '&'                 { TConjunction }
    '!'                 { TNegation }
    '('                 { TOpeningBracket }
    ')'                 { TClosingBracket }
    '@'                 { TForAll }
    '?'                 { TExists }
    '.'                 { TDot }
    '='                 { TEquality }
    '+'                 { TAddition }
    '*'                 { TMultiplication }
    '0'                 { TZero }
    '\''                { TIncrement }

%%

Statement   : "|-" Expression                             { Statement $2}

Expression  : Disjunction                                 { $1 }
            | Disjunction "->" Expression                 { Implication $1 $3 }

Disjunction : Conjunction                                 { $1 }
            | Disjunction '|' Conjunction                 { Disj $1 $3 }

Conjunction : Unary                                       { $1 }
            | Conjunction '&' Unary                       { Conj $1 $3 }

Unary       : Predicate                                   { $1 }
            | '!' Unary                                   { NegationNot $2 }
            | '(' Expression ')'                          { $2 }
            | '@' var '.' Expression                      { ForAll $2 $4 }
            | '?' var '.' Expression                      { Exists $2 $4 }

Predicate   : pre                                         { PreVariable $1 }
            | Term '=' Term                               { Equality $1 $3}

Term        : Addition                                    { $1 }
            | Term '+' Addition                           { Plus $1 $3 }

Addition    : Multiple                                    { $1 }
            | Addition '*' Multiple                       { Multiply $1 $3 }

Multiple    : var                                         { Variable $1 }
            | '(' Term ')'                                { $2 }
            | '0'                                         { Zero }
            | Multiple '\''                               { Increment $1 }

{
parseError :: [Token] -> a
parseError _ = error "Parse error"

data Statement = Statement { getResult :: Expression } deriving Show

data Term = Plus Term Term
          | Multiply Term Term
          | Variable String
          | Zero
          | Increment Term
          deriving (Ord, Eq)

data Expression = Implication Expression Expression
                | Disj Expression Expression
                | Conj Expression Expression
                | NegationNot Expression
                | ForAll String Expression
                | Exists String Expression
                | PreVariable String
                | Equality Term Term
                deriving (Ord, Eq)

instance Show Term where
    show (Plus a b)      = "(" ++ (show a) ++ "+" ++ (show b) ++ ")"
    show (Multiply a b)  = "(" ++ (show a) ++ "*" ++ (show b) ++ ")"
    show (Variable a)    = a
    show (Zero)          = "0"
    show (Increment a)   = (show a) ++ "'"

instance Show Expression where
    show (Implication left right)       = "(" ++ (show left) ++ "->" ++ (show right) ++ ")"
    show (Disj left right)              = "(" ++ (show left) ++ "|" ++ (show right) ++ ")"
    show (Conj left right)              = "(" ++ (show left) ++ "&" ++ (show right) ++ ")"
    show (NegationNot expression)       = "(!" ++ (show expression) ++ ")"
    show (ForAll variable expression)   = "(@" ++ variable ++ "." ++ (show expression) ++ ")"
    show (Exists variable expression)   = "(?" ++ variable ++ "." ++ (show expression) ++ ")"
    show (Equality left right)          = "(" ++ (show left) ++ "=" ++ (show right) ++ ")"
    show (PreVariable variable)         = variable
}
