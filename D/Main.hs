{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE Strict #-}

module Main where
import System.IO
import Data.Char
import qualified Data.Map.Strict as Map
import qualified Data.List as List
import qualified Data.Set as Set
import Data.Set (toList, fromList)
import System.Exit
import Lexer
import Parser
import Helper

data Axiom       = Axiom { getNumberAxiom :: Int, getExpressionAxiom :: Expression } deriving Show
data Hypothesis  = Hypothesis { getNumberHypothesis :: Int, getExpressionHypothesis :: Expression } deriving Show
data ModusPonens = ModusPonens { getLeft :: Int, getRight :: Int, getExpression :: Expression, getLeftExpression :: Expression } deriving Show

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

getMP Nothing !allExpr expression                                          = ModusPonens 0 0 expression expression
getMP (Just []) !allExpr expression                                        = ModusPonens 0 0 expression expression
getMP (Just (a : as)) !allExpr expression | (getExprNumber allExpr a) == 0 = getMP (Just as) allExpr expression
                                          | otherwise                      = ModusPonens (getExprNumber allExpr (Implication a expression)) (getExprNumber allExpr a) expression a

isModusPonens !mpMap !allExpr expression = getMP (Map.lookup expression mpMap) allExpr expression

setMP htMp !allExpr cnt !mpMap x (Implication a b) lastHt = iter htMp allExpr cnt (Map.insertWith (++) b [a] mpMap) x 1 lastHt
setMP htMp !allExpr cnt !mpMap x _                 lastHt = iter htMp allExpr cnt mpMap x 1 lastHt

iter !htMp !allExpr cnt !mpMap [] 0 lastHt                  = []
iter !htMp !allExpr cnt !mpMap [] 2 lastHt                  = []
iter !htMp !allExpr cnt !mpMap x@(expression : xs) 2 lastHt = case (Map.lookup expression allExpr) of
    (Just n) -> iter htMp allExpr cnt mpMap xs 2 lastHt
    (Nothing) -> iter htMp allExpr cnt mpMap x 0 lastHt
iter !htMp !allExpr cnt !mpMap x@(expression : xs) 0 lastHt = setMP htMp allExpr cnt mpMap x expression lastHt
iter !htMp !allExpr cnt !mpMap   (expression : xs) 1 lastHt =
    let
        htNumber     = getNumberHypothesis (isHypothesis htMp expression)
        amNumber     = getNumberAxiom (isAxiom expression)
        mpLeftNumber = getLeft (isModusPonens mpMap allExpr expression)
        left         = getLeftExpression (isModusPonens mpMap allExpr expression)
        newAllExpr   = (Map.insertWith (\o n -> n) expression cnt allExpr)
    in
        if lastHt == expression then
            (
                (Implication expression (Implication expression expression)) :
                (Implication (Implication expression (Implication expression expression)) (Implication (Implication expression (Implication (Implication expression expression) expression)) (Implication expression expression))) :
                (Implication (Implication expression (Implication (Implication expression expression) expression)) (Implication expression expression)) :
                (Implication expression (Implication (Implication expression expression) expression)) :
                (Implication expression expression) :
                (iter htMp newAllExpr (cnt + 1) mpMap xs 2 lastHt)
            )
        else if htNumber /= 0 then
            (
                expression :
                (Implication expression (Implication lastHt expression)) :
                (Implication lastHt expression) :
                (iter htMp newAllExpr (cnt + 1) mpMap xs 2 lastHt)
            )
        else if amNumber /= 0 then
            (
                expression :
                (Implication expression (Implication lastHt expression)) :
                (Implication lastHt expression) :
                (iter htMp newAllExpr (cnt + 1) mpMap xs 2 lastHt)
            )
        else if mpLeftNumber /= 0 then
            (
                (Implication (Implication lastHt left) (Implication (Implication lastHt (Implication left expression)) (Implication lastHt expression))) :
                (Implication (Implication lastHt (Implication left expression)) (Implication lastHt expression)) :
                (Implication lastHt expression) :
                (iter htMp newAllExpr (cnt + 1) mpMap xs 2 lastHt)
            )
        else
            []

loop prevHt checker index =
    let
        myFilter       = List.filter (\x -> checker (getHypotheses x))
        prevHypotheses = myFilter prevHt

        currHt         = minimizeHypotheses prevHt []
        currHypotheses = myFilter currHt
    in
        if (null currHypotheses) then
            prevHypotheses
        else if (index == 0) then
            currHypotheses
        else
            loop currHt checker (index - 1)

getVariables expression@(Variable a) result = Set.insert expression result
getVariables (Implication a b)       result = getVariables a (getVariables b result)
getVariables (Disj a b)              result = getVariables a (getVariables b result)
getVariables (Conj a b)              result = getVariables a (getVariables b result)
getVariables (NegationNot a)         result = getVariables a result

getAllSubsets []       result = result
getAllSubsets (x : xs) result = (map (\y -> (x : y)) (getAllSubsets xs result)) ++ (map (\y -> ((NegationNot x) : y)) (getAllSubsets xs result))

buildProof (SingleHypotheses hypotheses) result              = getPredefinedProof result hypotheses
buildProof (TripleHypotheses hypotheses first second) result =
    let
        ht   = head ((List.\\) (getHypotheses first) hypotheses)
        htMp = (Map.fromList (zip hypotheses [1..]))
        hp   = case ht of
            (NegationNot a) -> a
            a               -> a
    in
        (iter htMp Map.empty 1 Map.empty (buildProof first result) 2 ht) ++

        (iter htMp Map.empty 1 Map.empty (buildProof second result) 2 (case ht of
            (NegationNot expression) -> expression
            expression               -> (NegationNot expression)
        )) ++

        (aOrNotA hp) ++
        (
            (Implication (Implication hp result) (Implication (Implication (NegationNot hp) result) (Implication (Disj hp (NegationNot hp)) result))) :
            (Implication (Implication (NegationNot hp) result) (Implication (Disj hp (NegationNot hp)) result)) :
            (Implication (Disj hp (NegationNot hp)) result) :
            result : []
        )

printStatement []       = ""
printStatement [x]      = (show x)
printStatement (x : xs) = ((show x) ++ ",") ++ (printStatement xs)

proofBuilder subsets expression checker True  = do
    let basic   = map SingleHypotheses (List.filter (evaluate expression) subsets)
    let hypotheses = loop basic checker 3

    let result | not (null hypotheses) = do
                    putStrLn $ (printStatement (getHypotheses (head hypotheses))) ++ "|-" ++ (show expression)
                    putStr $ unlines $ map show (buildProof (head hypotheses) expression)
                    exitSuccess
               | otherwise             = do
                    putStr ""
    result
proofBuilder subsets expression checker False = putStrLn ":("

ok a = case a of
    []                     -> True
    ((NegationNot x) : xs) -> False
    (x : xs)               -> ok xs

okNegationNot a = case a of
    []                     -> True
    ((NegationNot x) : xs) -> okNegationNot xs
    (x : xs)               -> False

main = do
    input <- getLine
    let expression   = parser $ alexScanTokens input

    let allVariables = Set.toList $ getVariables expression Set.empty

    proofBuilder (getAllSubsets allVariables [[]]) expression ok True
    proofBuilder (getAllSubsets allVariables [[]]) (NegationNot expression) okNegationNot True
    proofBuilder (getAllSubsets allVariables [[]]) expression ok False
