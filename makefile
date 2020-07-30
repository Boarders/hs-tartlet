cabal:=cabal new-

build: lexer
	${cabal}build

lexer: src/Core/Parser/Token.x
	alex src/Core/Parser/Token.x

repl-core:
	${cabal}repl core

repl-main:
	${cabal}repl repl
