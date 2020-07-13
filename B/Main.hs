{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE Strict #-}

module Main where
import System.IO
import Data.List
import Data.Char
import qualified Data.Map.Strict as Map
import Data.Set (toList, fromList)
import Lexer
import Parser

data Axiom       = Axiom { getNumberAxiom :: Int, getExpressionAxiom :: Expression } deriving Show
data Hypothesis  = Hypothesis { getNumberHypothesis :: Int, getExpressionHypothesis :: Expression } deriving Show
data ModusPonens = ModusPonens { getLeft :: Int, getRight :: Int, getExpression :: Expression } deriving Show

check []                           = True
check ((a1, a2) : as)  | a1 == a2  = check as
                       | otherwise = False

getNumber' Nothing  expression = Hypothesis 0 expression
getNumber' (Just n) expression = Hypothesis n expression

isHypothesis !htMp expression = getNumber' (Map.lookup expression htMp) expression

isAxiom expression@(Implication a1 (Implication b a2))                                                                      | check [(a1, a2)]                               = Axiom 1 expression
isAxiom expression@(Implication (Implication a1 b1) (Implication (Implication a2 (Implication b2 c1)) (Implication a3 c2))) | check [(a1, a2), (a2, a3), (b1, b2), (c1, c2)] = Axiom 2 expression
isAxiom expression@(Implication a1 (Implication b1 (Conj a2 b2)))                                                           | check [(a1, a2), (b1, b2)]                     = Axiom 3 expression
isAxiom expression@(Implication (Conj a1 b) a2)                                                                             | check [(a1, a2)]                               = Axiom 4 expression
isAxiom expression@(Implication (Conj a b1) b2)                                                                             | check [(b1, b2)]                               = Axiom 5 expression
isAxiom expression@(Implication a1 (Disj a2 b))                                                                             | check [(a1, a2)]                               = Axiom 6 expression
isAxiom expression@(Implication b1 (Disj a b2))                                                                             | check [(b1, b2)]                               = Axiom 7 expression
isAxiom expression@(Implication (Implication a1 c1) (Implication (Implication b1 c2) (Implication (Disj a2 b2) c3)))        | check [(a1, a2), (b1, b2), (c1, c2), (c2, c3)] = Axiom 8 expression
isAxiom expression@(Implication (Implication a1 b1) (Implication (Implication a2 (NegationNot b2)) (NegationNot a3)))       | check [(a1, a2), (a2, a3), (b1, b2)]           = Axiom 9 expression
isAxiom expression@(Implication (NegationNot (NegationNot a1)) a2)                                                          | check [(a1, a2)]                               = Axiom 10 expression
isAxiom expression                                                                                                                                                           = Axiom 0 expression

getExpressionNumber Nothing  = 0
getExpressionNumber (Just n) = n

getExprNumber !allExpr expression = getExpressionNumber (Map.lookup expression allExpr)

getMP Nothing !allExpr expression                                          = ModusPonens 0 0 expression
getMP (Just []) !allExpr expression                                        = ModusPonens 0 0 expression
getMP (Just (a : as)) !allExpr expression | (getExprNumber allExpr a) == 0 = getMP (Just as) allExpr expression
                                          | otherwise                      = ModusPonens (getExprNumber allExpr (Implication a expression)) (getExprNumber allExpr a) expression

isModusPonens !mpMap !allExpr expression = getMP (Map.lookup expression mpMap) allExpr expression

setMP htMp !allExpr !exprAll cnt !mpMap x (Implication a b) = iter htMp allExpr exprAll cnt (Map.insertWith (++) b [a] mpMap) x 1
setMP htMp !allExpr !exprAll cnt !mpMap x _                 = iter htMp allExpr exprAll cnt mpMap x 1

data Result = Success { getAllNumbers :: (Map.Map Int (Expression, (Int, Int))), getLastNumber :: Int } | Fail deriving (Eq, Show)

getCnt (Just x) = x

iter !htMp !allExpr !exprAll cnt !mpMap [] 0                  = Success exprAll (cnt - 1)
iter !htMp !allExpr !exprAll cnt !mpMap [] 2                  = Success exprAll (cnt - 1)
iter !htMp !allExpr !exprAll cnt !mpMap x@(expression : xs) 2 = case (Map.lookup expression allExpr) of
    (Just n) -> iter htMp allExpr exprAll cnt mpMap xs 2
    (Nothing) -> iter htMp allExpr exprAll cnt mpMap x 0
iter !htMp !allExpr !exprAll cnt !mpMap x@(expression : xs) 0 = setMP htMp allExpr exprAll cnt mpMap x expression
iter !htMp !allExpr !exprAll cnt !mpMap   (expression : xs) 1 =
    let
        htNumber      = getNumberHypothesis (isHypothesis htMp expression)
        amNumber      = getNumberAxiom (isAxiom expression)
        mpLeftNumber  = getLeft (isModusPonens mpMap allExpr expression)
        mpRightNumber = getRight (isModusPonens mpMap allExpr expression)
        newAllExpr    = (Map.insertWith (\o n -> n) expression cnt allExpr) 
        newExprAll    = Map.insert (getCnt (Map.lookup expression newAllExpr))
    in
        if htNumber /= 0 then
            iter htMp newAllExpr (newExprAll (expression, (-1, htNumber)) exprAll) (cnt + 1) mpMap xs 2
        else if amNumber /= 0 then
            iter htMp newAllExpr (newExprAll (expression, (-2, amNumber)) exprAll) (cnt + 1) mpMap xs 2
        else if mpLeftNumber /= 0 then
            iter htMp newAllExpr (newExprAll (expression, (mpRightNumber, mpLeftNumber)) exprAll) (cnt + 1) mpMap xs 2
        else
            Fail

getFirst (Just a)        = (fst a)
getSecondFirst (Just a)  = (fst (snd a))
getSecondSecond (Just a) = (snd (snd a))

getOne (Just a)  = a
getOne (Nothing) = -111

getBool (Just a)  = a
getBool (Nothing) = False

getPair cur !allNums = ((getSecondFirst (Map.lookup cur allNums)), (getSecondSecond (Map.lookup cur allNums)))

getActual cur !allNums otobr =
    let
        (first, second) = getPair cur allNums
    in
        (
            if (first == -1 || first == -2) then
                ((getFirst (Map.lookup cur allNums)), (first, second))
            else
                ((getFirst (Map.lookup cur allNums)),  (getOne (Map.lookup first otobr), getOne (Map.lookup second otobr)))
        )

dfs u !allNums !used =
    if (getSecondFirst (Map.lookup u allNums) < 0) then
        (Map.insert u True used)
    else
        dfs (getSecondFirst (Map.lookup u allNums)) allNums (dfs (getSecondSecond (Map.lookup u allNums)) allNums (Map.insert u True used))

order cur act cnt !used !allNums !newAllNums !otobr | cur > cnt                     = newAllNums
order cur act cnt !used !allNums !newAllNums !otobr | getBool (Map.lookup cur used) = order (cur + 1) (act + 1) cnt used allNums ((getActual cur allNums otobr) : newAllNums) (Map.insert cur act otobr)
                                                    | otherwise                     = order (cur + 1) act cnt used allNums newAllNums (Map.insert cur act otobr)

printAnswer [] cnt !res = res
printAnswer ((expr, (f, s)) : xs) cnt res | f == -1   = printAnswer xs (cnt + 1) (("[" ++ (show cnt) ++ ". Hypothesis " ++ (show s) ++ "] " ++ (show expr)) : res)
                                          | f == -2   = printAnswer xs (cnt + 1) (("[" ++ (show cnt) ++ ". Ax. sch. " ++ (show s) ++ "] " ++ (show expr)) : res)
                                          | otherwise = printAnswer xs (cnt + 1) (("[" ++ (show cnt) ++ ". M.P. " ++ (show s) ++ ", " ++ (show f) ++ "] " ++ (show expr)) : res)

printStatement [] res       = res
printStatement [x] res      = ((show x) : res)
printStatement (x : xs) res = printStatement xs (((show x) ++ ", ") : res)

getLastLine [x]      = x
getLastLine (x : xs) = getLastLine xs

main = do
    input <- getContents
    let firstLine  = (head $ lines input)
    let statement  = parseStatement $ alexScanTokens firstLine
    let hypotheses = (reverse $ getHypotheses statement)
    let result     = getResult statement

    let expressions     = map (parser . alexScanTokens) (filter (not . all isSpace) (tail $ lines input))
    let tmpResult'      = iter (Map.fromListWith (\a b -> b) (zip hypotheses [1..])) Map.empty Map.empty 1 Map.empty expressions 2
    let getVal (Just a) = (fst a)

    let tmpResult cnt | cnt == 0                                                       = (-1)
                      | (getVal (Map.lookup cnt (getAllNumbers tmpResult')) /= result) = tmpResult (cnt - 1)
                      | otherwise                                                      = cnt

    if (tmpResult' == Fail) then
        putStrLn "Proof is incorrect"
    else if ((getLastLine expressions) /= result) || ((tmpResult (getLastNumber tmpResult')) == (-1)) then
        putStrLn "Proof is incorrect"
    else
        putStrLn (firstLine ++ "\n" ++ (unlines $ reverse (printAnswer (reverse (order 1 1 (tmpResult (getLastNumber tmpResult')) (dfs (tmpResult (getLastNumber tmpResult')) (getAllNumbers tmpResult') Map.empty) (getAllNumbers tmpResult') [] Map.empty)) 1 [])))
