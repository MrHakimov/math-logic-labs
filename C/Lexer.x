{
module Lexer where
}

%wrapper "basic"

$digit = 0-9            -- digits
$alpha = A-Z            -- alphabetic characters
$lower = a-z            -- lower alphabetic characters

tokens :-

        $white+                       ;
        $lower+                       { \s -> TVariable s }
        $alpha+                       { \s -> TPredicate s }
        "|-"                          { \s -> TCarriage }
        "->"                          { \s -> TImplication }
        \|                            { \s -> TDisjunction }
        \&                            { \s -> TConjunction }
        \!                            { \s -> TNegation }
        \(                            { \s -> TOpeningBracket }
        \)                            { \s -> TClosingBracket }
        \@                            { \s -> TForAll }
        \?                            { \s -> TExists }
        \.                            { \s -> TDot }
        \=                            { \s -> TEquality }
        \+                            { \s -> TAddition }
        \*                            { \s -> TMultiplication }
        0                             { \s -> TZero }
        \'                            { \s -> TIncrement }

{
data Token
    = TVariable String
    | TPredicate String
    | TCarriage
    | TImplication
    | TDisjunction
    | TConjunction
    | TNegation
    | TOpeningBracket
    | TClosingBracket
    | TForAll
    | TExists
    | TDot
    | TEquality
    | TAddition
    | TMultiplication
    | TZero
    | TIncrement
}
