
all: raillisp.fth raillisp.lsp
	gforthmi raillisp.fi create-image.fth #TODO: fix

forth: forth.c extract.py
	python extract.py
	gcc forth.c -o forth -lreadline -lm -O3 # -g

asm: forth.c extract.py
	python extract.py
	gcc -S forth.c -o forth.s -lreadline -lm # -O3

objdump: forth.c extract.py
	python extract.py
	gcc -c forth.c -lreadline -g # -O3
	objdump -d -M intel -S forth.o > forth-objdump.s


test: tests.lsp raillisp.fth raillisp.lsp
	gforth test.fth

run:
	gforth raillisp.fth

bench:
	gforth-fast benchmark/run.fth #TODO: fix

clean:
	rm -f forth _forthwords.c raillisp.fi temp-image.fi*
