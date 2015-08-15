CC=g++
CFLAGS=-I.

dsverifier: dsverifier.cpp
	$(CC) -o dsverifier -std=c++11 dsverifier.cpp -I.

clean:
	rm -rf dsverifier
