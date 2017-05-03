CC=clang++
CFLAGS=-I.
OS := $(shell uname)

verification_metrics: utils.cpp metrics_collector_t.cpp verification_metrics.cpp

ifeq ($(shell uname),Darwin)
	$(CC) -L/opt/local/lib/ -std=c++11 -lboost_system-mt -lboost_chrono-mt -lm -o verification_metrics utils.cpp metrics_collector_t.cpp verification_metrics.cpp -I /opt/local/include/
else
	$(CC) -std=c++11 -lboost_system -lboost_chrono -lrt -o verification_metrics utils.cpp metrics_collector_t.cpp verification_metrics.cpp
endif

clean:
	rm -f verification_metrics
