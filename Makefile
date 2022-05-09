GHC        = ghc

all : frappe_interpreter

frappe_interpreter : 
	${GHC} -o main -i./src/bnfc/:./src/typechecker/:./src/interpreter/ src/main.hs

clean :
	-rm -f *.hi *.o *.log *.aux *.dvi