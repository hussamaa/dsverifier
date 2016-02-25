CC=g++
CFLAGS=-I.
OS := $(shell uname)

dsverifier: dsverifier.cpp

ifeq ($(shell uname),Darwin)
	$(CC) -o dsverifier -std=c++11 dsverifier.cpp -I /usr/local/include/eigen3/ -I. -I /opt/local/include/
else
	$(CC) -o dsverifier -static -std=c++11 dsverifier.cpp -I /usr/include/eigen3/ -I.
endif

clean:
	rm -rf dsverifier
