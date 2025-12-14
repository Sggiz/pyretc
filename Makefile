
all: pyretc.exe

# commandes pratiques

parse: test/test.arr pyretc.exe
	_build/default/pyretc.exe --parse-only $<

jcfparse: runtest.sh pyretc.exe
	sh $< -1

type: test/test.arr pyretc.exe
	_build/default/pyretc.exe --type-only $<

jcftype: runtest.sh pyretc.exe
	bash $< -2

clean:
	dune clean



# constructions

pyretc.exe:
	dune build pyretc.exe

test/%.s: test/%.arr pyretc.exe
	dune exec ./pyretc.exe $<

test/%.out: test/%.s
	gcc -g -no-pie $< -o $@


.PHONY: all clean parse jcfparse pyretc.exe

