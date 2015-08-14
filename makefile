CC=g++
CFLAGS=-I.

dsverifier: dsverifier.cpp
	$(CC) -o dsverifier dsverifier.cpp -I.

clean:
	rm -rf dsverifier
