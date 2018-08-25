
all: raillisp.fth raillisp.lsp
	gforthmi raillisp.fi create-image.fth #TODO: fix

test: tests.lsp raillisp.fth raillisp.lsp
	gforth test.fth

bench:
	gforth-fast benchmark/run.fth #TODO: fix
