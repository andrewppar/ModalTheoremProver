test : 
	ghc -O2 ./ModalTheoremProver/Tests.hs
		time ./ModalTheoremProver/Tests

clean : 
	rm ./main/*.hi 
	rm ./main/*.o 
	rm ./main/Tests
