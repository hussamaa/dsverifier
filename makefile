CC=g++
CFLAGS=-I.

dsverifier: dsverifier.c
	$(CC) -o dsverifier dsverifier.c -I.

clean:
	rm -rf dsverifier
