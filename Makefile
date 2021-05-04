satTest: clean File.o Proof.o Solver.o satTest.o
	g++ -o $@ File.o Proof.o Solver.o satTest.o -O3

ref: clean File.o Proof.o Solver.o satTest-ref.o
	g++ -o $@ -g File.o Proof.o Solver.o satTest-ref.o

File.o: File.cpp
	g++ -c -g File.cpp -O3

Proof.o: Proof.cpp
	g++ -c -g Proof.cpp -O3

Solver.o: Solver.cpp
	g++ -c -g Solver.cpp -O3

satTest.o: satTest.cpp
	g++ -c -g satTest.cpp -O3

satTest2.o: satTest2.cpp
	g++ -c -g satTest2.cpp -O3

satTest-ref.o: satTest-ref.cpp
	g++ -c -g satTest-ref.cpp

clean:
	rm -f *.o ref tags
