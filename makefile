CC=g++
CFLAGS=-I.

dsverifier: dsverifier.cpp
	$(CC) -o dsverifier -static -std=c++11 dsverifier.cpp -I /usr/include/eigen3/ -I.

clean:
	rm -rf dsverifier
