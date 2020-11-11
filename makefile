test : 
	ghc -O2 ./ModalTheoremProver/Tests.hs
		time ./ModalTheoremProver/Tests

clean : 
	rm -f ./ModalTheoremProver/*.hi 
	rm -f ./ModalTheoremProver/*.o 
	rm -f ./ModalTheoremProver/Tests
	rm -f ./ModalTheoremProver/Main
