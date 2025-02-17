all: tex/BasilIR.pdf ocaml

java/basil_ir/Test.class: java/basil_ir/BasilIRParser.g4
	$(MAKE) -C java

ocaml :  ocamlBasil/BasilIR/AbsBasilIR.ml

ocamlBasil/BasilIR/AbsBasilIR.ml: BasilIR.cf
	bnfc --ocaml-menhir -o ocamlBasil/BasilIR BasilIR.cf


lbnf/lib/AbsLBNF.ml: LBNF.cf
	bnfc --ocaml-menhir -o lbnf/lib LBNF.cf

.PHONY=runjava
runjava: java/basil_ir/Test.class FORCE
	CLASSPATH="$$CLASSPATH:java"  java basil_ir.Test ../../../test-output.il

java/basil_ir/BasilIRParser.g4: BasilIR.cf
	bnfc --java-antlr -m -o java BasilIR.cf

cpp/TestBasilIR: BasilIR.cf
	bnfc --cpp -m -o cpp BasilIR.cf
	$(MAKE) -C cpp

runcpp: cpp/TestBasilIR FORCE
	./cpp/TestBasilIR ../../../test-output.il

test : ./cpp/TestBasilIR desugar.cpp test.cpp
	g++ -O2 -g test.cpp desugar.cpp  cpp/Skeleton.C cpp/Absyn.o cpp/Buffer.o cpp/Lexer.o cpp/Parser.o cpp/Printer.o -o test

c/Absyn.c : BasilIR.cf
	bnfc --c -m -o c BasilIR.cf

tex/BasilIR.pdf: BasilIR.cf
		bnfc --latex -m -o tex BasilIR.cf
		$(MAKE) -C tex

FORCE: ;
