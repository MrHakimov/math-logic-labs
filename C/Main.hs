{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE Strict #-}

module Main where
import System.IO
import Data.List
import Data.Char
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Set (toList, fromList)
import Lexer
import Parser

data Axiom       = Axiom { getNumberAxiom :: Int, getExpressionAxiom :: Expression } deriving Show
data Hypothesis  = Hypothesis { getNumberHypothesis :: Int, getExpressionHypothesis :: Expression } deriving Show
data ModusPonens = ModusPonens { getLeft :: Int, getRight :: Int, getExpression :: Expression } deriving Show

check []                           = True
check ((a1, a2) : as)  | a1 == a2  = check as
                       | otherwise = False

substitutionTest' x Zero Zero                       = Set.empty
substitutionTest' x a'@(Variable a) b'              =
    if x == a then
        Set.singleton b'
    else if a' == b' then
        Set.empty
    else
        Set.singleton (Variable "aa") -- переменной aa в нашей грамматике не может быть, поэтому смело используем такое название
substitutionTest' x (Increment a) (Increment b)     = substitutionTest' x a b
substitutionTest' x (Plus a b) (Plus a' b')         = Set.union (substitutionTest' x a a') (substitutionTest' x b b')
substitutionTest' x (Multiply a b) (Multiply a' b') = Set.union (substitutionTest' x a a') (substitutionTest' x b b')
substitutionTest' x a b                             = Set.singleton (Variable "aa")

substitutionTest x (PreVariable a) (PreVariable b)       = if a == b then Set.empty else Set.singleton (Variable "aa")
substitutionTest x (NegationNot a) (NegationNot b)       = substitutionTest x a b
substitutionTest x a'@(ForAll y a) b'@(ForAll z b)       =
    if x == y && a' == b' then
        Set.empty
    else if x /= y && y == z then
        substitutionTest x a b
    else
        Set.singleton (Variable "aa")
substitutionTest x a'@(Exists y a) b'@(Exists z b)       =
    if x == y && a' == b' then
        Set.empty
    else if x /= y && y == z then
        substitutionTest x a b
    else
        Set.singleton (Variable "aa")
substitutionTest x (Equality a b) (Equality a' b')       = Set.union (substitutionTest' x a a') (substitutionTest' x b b')
substitutionTest x (Implication a b) (Implication a' b') = Set.union (substitutionTest x a a') (substitutionTest x b b')
substitutionTest x (Conj a b) (Conj a' b')               = Set.union (substitutionTest x a a') (substitutionTest x b b')
substitutionTest x (Disj a b) (Disj a' b')               = Set.union (substitutionTest x a a') (substitutionTest x b b')
substitutionTest x a b                                   = Set.singleton (Variable "aa")

getBoolFromSet st expression = (Set.elemAt 0 st) == expression

inductionTest x psi psii psi0 psi' =
    let
        st1 = (substitutionTest x psi psi0)
        st2 = (substitutionTest x psi psi')
    in
        psi == psii && ((Set.size st1) == 1) && (not (Set.member (Variable "aa") st1)) && ((Set.size st2) == 1) && (not (Set.member (Variable "aa") st2)) && (getBoolFromSet st1 Zero) && (getBoolFromSet st2 (Increment (Variable x)))

getFreeVariables Zero           = Set.empty
getFreeVariables (Variable x)   = Set.singleton x
getFreeVariables (Increment x)  = getFreeVariables x
getFreeVariables (Plus a b)     = Set.union (getFreeVariables a) (getFreeVariables b)
getFreeVariables (Multiply a b) = Set.union (getFreeVariables a) (getFreeVariables b)

isFree' x Zero variables kvantors           = True
isFree' x (Variable y) variables kvantors   =
    if x == y then
        if (((Set.size variables) + (Set.size kvantors)) == (Set.size (Set.union variables kvantors))) then
            True
        else
            False
    else
        True
isFree' x (Increment a) variables kvantors    = isFree' x a variables kvantors
isFree' x (Plus a b) variables kvantors       = (isFree' x a variables kvantors) && (isFree' x b variables kvantors)
isFree' x (Multiply a b) variables kvantors   = (isFree' x a variables kvantors) && (isFree' x b variables kvantors)

isFree x (PreVariable a) variables kvantors   = True
isFree x (NegationNot a) variables kvantors   = isFree x a variables kvantors
isFree x (ForAll y phi) variables kvantors    =
    if x == y then
        isFree x phi variables kvantors
    else
        isFree x phi variables (Set.insert y kvantors)
isFree x (Exists y phi) variables kvantors    =
    if x == y then
        isFree x phi variables kvantors
    else
        isFree x phi variables (Set.insert y kvantors)
isFree x (Equality a b) variables kvantors    = (isFree' x a variables kvantors) && (isFree' x b variables kvantors)
isFree x (Implication a b) variables kvantors = (isFree x a variables kvantors) && (isFree x b variables kvantors)
isFree x (Disj a b) variables kvantors        = (isFree x a variables kvantors) && (isFree x b variables kvantors)
isFree x (Conj a b) variables kvantors        = (isFree x a variables kvantors) && (isFree x b variables kvantors)

forAllTest x phi phi'  =
    let
        st = (substitutionTest x phi phi')
    in
        if (Set.size st == 1) && (not (Set.member (Variable "aa") st)) then
            ((1, isFree x phi (getFreeVariables (Set.elemAt 0 st)) Set.empty), Equality (Set.elemAt 0 st) (Variable x))
        else
            ((0, False), PreVariable "A")

getNumber' Nothing  expression = Hypothesis 0 expression
getNumber' (Just n) expression = Hypothesis n expression

isHypothesis !htMp expression = getNumber' (Map.lookup expression htMp) expression

isAxiom expression@(Implication a1 (Implication b a2))                                                                      | check [(a1, a2)]                                                     = Axiom 1 expression
isAxiom expression@(Implication (Implication a1 b1) (Implication (Implication a2 (Implication b2 c1)) (Implication a3 c2))) | check [(a1, a2), (a2, a3), (b1, b2), (c1, c2)]                       = Axiom 2 expression
isAxiom expression@(Implication (Conj a1 b) a2)                                                                             | check [(a1, a2)]                                                     = Axiom 3 expression
isAxiom expression@(Implication (Conj a b1) b2)                                                                             | check [(b1, b2)]                                                     = Axiom 4 expression
isAxiom expression@(Implication a1 (Implication b1 (Conj a2 b2)))                                                           | check [(a1, a2), (b1, b2)]                                           = Axiom 5 expression
isAxiom expression@(Implication a1 (Disj a2 b))                                                                             | check [(a1, a2)]                                                     = Axiom 6 expression
isAxiom expression@(Implication b1 (Disj a b2))                                                                             | check [(b1, b2)]                                                     = Axiom 7 expression
isAxiom expression@(Implication (Implication a1 c1) (Implication (Implication b1 c2) (Implication (Disj a2 b2) c3)))        | check [(a1, a2), (b1, b2), (c1, c2), (c2, c3)]                       = Axiom 8 expression
isAxiom expression@(Implication (Implication a1 b1) (Implication (Implication a2 (NegationNot b2)) (NegationNot a3)))       | check [(a1, a2), (a2, a3), (b1, b2)]                                 = Axiom 9 expression
isAxiom expression@(Implication (NegationNot (NegationNot a1)) a2)                                                          | check [(a1, a2)]                                                     = Axiom 10 expression
isAxiom expression@(Implication (ForAll x phi) phi')                                                                        | check [(phi, phi')] || fst (forAllTest x phi phi') == (1, True)      = Axiom 11 expression
isAxiom expression@(Implication phi' (Exists x phi))                                                                        | check [(phi, phi')] || fst (forAllTest x phi phi') == (1, True)      = Axiom 12 expression
isAxiom expression@(Implication (ForAll x phi) phi')                                                                        | check [(phi, phi')] || fst (forAllTest x phi phi') == (1, False)     = Axiom 111 (Implication expression (snd (forAllTest x phi phi')))
isAxiom expression@(Implication phi' (Exists x phi))                                                                        | check [(phi, phi')] || fst (forAllTest x phi phi') == (1, False)     = Axiom 112 (Implication expression (snd (forAllTest x phi phi')))
isAxiom expression@(Implication (Equality (Variable "a") (Variable "b")) (Implication (Equality (Variable "a") (Variable "c")) (Equality (Variable "b") (Variable "c"))))                          = Axiom 101 expression
isAxiom expression@(Implication (Equality (Variable "a") (Variable "b")) (Equality (Increment (Variable "a")) (Increment (Variable "b"))))                                                         = Axiom 102 expression
isAxiom expression@(Implication (Equality (Increment (Variable "a")) (Increment (Variable "b"))) (Equality (Variable "a") (Variable "b")))                                                         = Axiom 103 expression
isAxiom expression@(NegationNot (Equality (Increment (Variable "a")) Zero))                                                                                                                        = Axiom 104 expression
isAxiom expression@(Equality (Plus (Variable "a") Zero) (Variable "a"))                                                                                                                            = Axiom 105 expression
isAxiom expression@(Equality (Plus (Variable "a") (Increment (Variable "b"))) (Increment (Plus (Variable "a") (Variable "b"))))                                                                    = Axiom 106 expression
isAxiom expression@(Equality (Multiply (Variable "a") Zero) Zero)                                                                                                                                  = Axiom 107 expression
isAxiom expression@(Equality (Multiply (Variable "a") (Increment (Variable "b"))) (Plus (Multiply (Variable "a") (Variable "b")) (Variable "a")))                                                  = Axiom 108 expression
isAxiom expression@(Implication (Conj psi0 (ForAll x (Implication psi psi'))) psii)                                         | inductionTest x psi psii psi0 psi'                                   = Axiom 109 expression
isAxiom expression                                                                                                                                                                                 = Axiom 0 expression

getExpressionNumber Nothing  = 0
getExpressionNumber (Just n) = n

getExprNumber !allExpr expression = getExpressionNumber (Map.lookup expression allExpr)

maxx (a1, b1) (a2, b2) | a1 > a2 = (a1, b1)
                       | a1 == a2 && b1 >= b2 = (a1, b1)
                       | otherwise = (a2, b2)

getMP Nothing !allExpr expression                                          = ModusPonens 0 0 expression
getMP (Just []) !allExpr expression                                        = ModusPonens 0 0 expression
getMP (Just (a : as)) !allExpr expression | (getExprNumber allExpr a) == 0 = getMP (Just as) allExpr expression
                                          | otherwise                      =
                                                    let
                                                        (x1, y1) = ((getExprNumber allExpr a), (getExprNumber allExpr (Implication a expression)))
                                                        tmp = getMP (Just as) allExpr expression
                                                        (x2, y2) = ((getLeft tmp), (getRight tmp))
                                                        mx = (maxx (x1, y1) (x2, y2))
                                                        lft = fst mx
                                                        rgt = snd mx
                                                    in
                                                        ModusPonens lft rgt expression

isModusPonens !mpMap !allExpr expression = getMP (Map.lookup expression mpMap) allExpr expression

isNotFree' x Zero           = True
isNotFree' x (Variable y)   = if x == y then False else True
isNotFree' x (Increment y)  = isNotFree' x y
isNotFree' x (Plus a b)     = (isNotFree' x a) && (isNotFree' x b)
isNotFree' x (Multiply a b) = (isNotFree' x a) && (isNotFree' x b)

isNotFree x (PreVariable p)   = True
isNotFree x (NegationNot a)   = isNotFree x a
isNotFree x (ForAll y a)      =
    if x == y then
        True
    else
        isNotFree x a
isNotFree x (Exists y a)      =
    if x == y then
        True
    else
        isNotFree x a
isNotFree x (Equality a b)    = (isNotFree' x a) && (isNotFree' x b)
isNotFree x (Implication a b) = (isNotFree x a) && (isNotFree x b)
isNotFree x (Disj a b)        = (isNotFree x a) && (isNotFree x b)
isNotFree x (Conj a b)        = (isNotFree x a) && (isNotFree x b)

isForAllIntro x phi psi allExpr = case Map.lookup (Implication psi phi) allExpr of
    (Just n)  -> case isNotFree x psi of
        True  -> (0, n)
        False -> (1, n)
    (Nothing) -> (2, 0)

isExistsIntro x phi psi allExpr = case Map.lookup (Implication phi psi) allExpr of
    (Just n)  -> case isNotFree x psi of
        True  -> (0, n)
        False -> (1, n)
    (Nothing) -> (2, 0)

setMP htMp !allExpr !exprAll cnt !mpMap x (Implication a b) = iter htMp allExpr exprAll cnt (Map.insertWith (++) b [a] mpMap) x 1
setMP htMp !allExpr !exprAll cnt !mpMap x _                 = iter htMp allExpr exprAll cnt mpMap x 1

data Result = Success { getAllNumbers :: (Map.Map Int (Expression, (Int, Int))), getLastNumber :: Int, getHasErrors :: Bool } | Fail deriving (Eq, Show)

getCnt (Just x) = x

iter !htMp !allExpr !exprAll cnt !mpMap [] 0                  = Success exprAll (cnt - 1) False
iter !htMp !allExpr !exprAll cnt !mpMap [] 2                  = Success exprAll (cnt - 1) False
iter !htMp !allExpr !exprAll cnt !mpMap x@(expression : xs) 2 = iter htMp allExpr exprAll cnt mpMap x 0
iter !htMp !allExpr !exprAll cnt !mpMap x@(expression : xs) 0 = setMP htMp allExpr exprAll cnt mpMap x expression
iter !htMp !allExpr !exprAll cnt !mpMap   (expression : xs) 1 =
    let
        htNumber      = getNumberHypothesis (isHypothesis htMp expression)
        amNumber      = getNumberAxiom (isAxiom expression)
        mpLeftNumber  = getLeft (isModusPonens mpMap allExpr expression)
        mpRightNumber = getRight (isModusPonens mpMap allExpr expression)
        newAllExpr    = (Map.insertWith (\n o -> n) expression cnt allExpr)
        newExprAll    = Map.insert (getCnt (Map.lookup expression newAllExpr))
        existsCheck   = case expression of
            (Implication (Exists x phi) psi) -> isExistsIntro x phi psi newAllExpr
            _                                -> (3, 0)
        forAllCheck   = case expression of
            (Implication psi (ForAll x phi)) -> isForAllIntro x phi psi newAllExpr
            _                                -> (3, 0)
    in
        if htNumber /= 0 then
            iter htMp newAllExpr (newExprAll (expression, ((-1), htNumber)) exprAll) (cnt + 1) mpMap xs 2
        else if amNumber /= 0 then
            if amNumber == 111 || amNumber == 112 then
                Success (newExprAll (getExpressionAxiom (isAxiom expression), ((-20), 0)) exprAll) cnt True
            else if amNumber >= 101 && amNumber <= 109 then
                iter htMp newAllExpr (newExprAll (expression, ((-200), (amNumber - 100))) exprAll) (cnt + 1) mpMap xs 2
            else
                iter htMp newAllExpr (newExprAll (expression, ((-2), amNumber)) exprAll) (cnt + 1) mpMap xs 2
        else if mpLeftNumber /= 0 then
            iter htMp newAllExpr (newExprAll (expression, (mpLeftNumber, mpRightNumber)) exprAll) (cnt + 1) mpMap xs 2
        else if (fst existsCheck) == 0 then
            iter htMp newAllExpr (newExprAll (expression, ((-3), (snd existsCheck))) exprAll) (cnt + 1) mpMap xs 2
        else if (fst existsCheck) == 1 then
            Success (newExprAll (expression, ((-30), (snd existsCheck))) exprAll) cnt True
        else if (fst forAllCheck) == 0 then
            iter htMp newAllExpr (newExprAll (expression, ((-4), (snd forAllCheck))) exprAll) (cnt + 1) mpMap xs 2
        else if (fst forAllCheck) == 1 then
            Success (newExprAll (expression, ((-40), (snd forAllCheck))) exprAll) cnt True
        else
            Success (newExprAll (expression, ((-5), 0)) exprAll) cnt True

getActualVariable expression@(Implication _ (Equality _ (Variable x))) = x
getActualVariable expression@(Implication _ (ForAll x _))              = x
getActualVariable expression@(Implication (Exists x _) _)              = x
getActualVariable expression@(ForAll x _)                              = x
getActualVariable expression@(Exists x _)                              = x

getActualTerm expression@(Implication _ (Equality x _)) = x

printResult 0 _           = []
printResult index exprAll =
    case (getCnt (Map.lookup index exprAll)) of
        (expression, (-2, n))   -> "[" ++ (show index) ++ ". Ax. sch. " ++ (show n) ++ "] " ++ (show expression)
        (expression, (-20, n))  -> "Expression " ++ (show index) ++ ": variable " ++ (getActualVariable expression) ++ " is not free for term " ++ (show (getActualTerm expression)) ++ " in ?@-axiom."
        (expression, (-200, n)) -> "[" ++ (show index) ++ ". Ax. " ++ (if n == 9 then "sch. " else "") ++ "A" ++ (show n) ++ "] " ++ (show expression)
        (expression, (-3, n))   -> "[" ++ (show index) ++ ". ?@-intro " ++ (show n) ++ "] " ++ (show expression)
        (expression, (-30, n))  -> "Expression " ++ (show index) ++ ": variable " ++ (getActualVariable expression) ++ " occurs free in ?@-rule."
        (expression, (-4, n))   -> "[" ++ (show index) ++ ". ?@-intro " ++ (show n) ++ "] " ++ (show expression)
        (expression, (-40, n))  -> "Expression " ++ (show index) ++ ": variable " ++ (getActualVariable expression) ++ " occurs free in ?@-rule."
        (expression, (-5, n))   -> "Expression " ++ (show index) ++ " is not proved."
        (expression, (x, y))    -> "[" ++ (show index) ++ ". M.P. " ++ (show x) ++ ", " ++ (show y) ++ "] " ++ (show expression)
    : printResult (index - 1) exprAll

getLastLine [x]      = x
getLastLine (x : xs) = getLastLine xs

main = do
    input <- getContents
    let firstLine   = (head $ lines input)
    let statement   = parseStatement $ alexScanTokens firstLine
    let result      = getResult statement

    let expressions = map (parser . alexScanTokens) (filter (not . all isSpace) (tail $ lines input))
    let tmpResult'  = iter (Map.fromListWith (\a b -> b) (zip [] [1..])) Map.empty Map.empty 1 Map.empty expressions 2

    case tmpResult' of
        Fail                        -> putStrLn "Proof is incorrect"
        Success exprAll n hasErrors -> putStrLn ("|-" ++ (show result) ++ "\n" ++ (unlines $ map id (reverse $ printResult n exprAll)) ++ (if (not hasErrors) && (n == (length expressions)) && (getLastLine expressions) /= result then "The proof proves different expression." else ""))
