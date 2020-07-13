module Main where
import Lexer
import Parser

main = do
	expression <- getLine
	putStrLn $ show $ parser $ alexScanTokens expression
