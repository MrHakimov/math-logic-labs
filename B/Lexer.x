{
module Lexer where
}

%wrapper "basic"

$digit = 0-9            -- digits
$alpha = A-Z            -- alphabetic characters

tokens :-

        $white+                       ;
        $alpha [$alpha $digit \']*    { \s -> TVariable s }
        "|-"                          { \s -> TCarriage }
        "->"                          { \s -> TImplication }
        \,                            { \s -> TComma }
        \|                            { \s -> TDisjunction }
        \&                            { \s -> TConjunction }
        \!                            { \s -> TNegation }
        \(                            { \s -> TOpeningBracket }
        \)                            { \s -> TClosingBracket }

{
data Token
    = TVariable String
    | TCarriage
    | TImplication
    | TComma
    | TDisjunction
    | TConjunction
    | TNegation
    | TOpeningBracket
    | TClosingBracket
}
