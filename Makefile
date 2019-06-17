
all: raillisp.fth raillisp.lsp
	gforthmi raillisp.fi create-image.fth #TODO: fix

forth: forth.c extract.py
	python extract.py
	gcc forth.c -o forth -lreadline -lm -O2

asm: forth.c extract.py
	python extract.py
	gcc -S forth.c -o forth.s -lreadline -lm #-O3

test: tests.lsp raillisp.fth raillisp.lsp
	gforth test.fth

run:
	gforth raillisp.fth

bench:
	gforth-fast benchmark/run.fth #TODO: fix

clean:
	rm -f forth _forth-words.c raillisp.fi temp-image.fi*
