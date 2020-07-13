all:
	alex Lexer.x
	happy Parser.y
	ghc Main.hs

run:
	./Main

clean:
	rm *.o *.hi Lexer.hs Parser.hs
	rm Main
