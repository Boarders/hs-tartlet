cabal:=cabal new-

build: parser
	${cabal}build

lexer: src/Core/Parser/Token.x
	alex src/Core/Parser/Token.x

parser: src/Core/Parser/Parse.y lexer
	happy src/Core/Parser/Parse.y

repl-core:
	${cabal}repl core

repl-main:
	${cabal}repl repl
