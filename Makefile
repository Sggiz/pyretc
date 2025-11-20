
all: pyretc.exe

# commandes pratiques

parse: test/test.arr pyretc.exe
	_build/default/pyretc.exe --parse-only $<

jcfparse: runtest.sh pyretc.exe
	sh $< -1



# constructions

pyretc.exe:
	dune build pyretc.exe

test/%.s: test/%.arr pyretc.exe
	dune exec ./pyretc.exe $<

test/%.out: test/%.s
	gcc -g -no-pie $< -o $@

clean:
	dune clean

.PHONY: all clean parse jcfparse pyretc.exe
