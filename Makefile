
all: test/test1.s test/test1.out
	test/test1.out

parse: test/test1.arr pyretc.exe
	_build/default/pyretc.exe --parse-only $<

pyretc.exe:
	dune build pyretc.exe

test/%.s: test/%.arr pyretc.exe
	dune exec ./pyretc.exe $<

test/%.out: test/%.s
	gcc -g -no-pie $< -o $@

clean:
	dune clean

.PHONY: all clean pyretc.exe
