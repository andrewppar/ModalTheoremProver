test : 
	ghc -O2 ./ModalTheoremProver/Tests.hs
	time ./ModalTheoremProver/Tests
main : 
	ghc -O2 ./ModalTheoremProver/Main.hs
	
clean : 
	rm -f ./ModalTheoremProver/*.hi 
	rm -f ./ModalTheoremProver/*.o 
	rm -f ./ModalTheoremProver/Tests
	rm -f ./ModalTheoremProver/Main
