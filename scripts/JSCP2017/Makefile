CC_MAC=clang++
CC_LINUX=clang++-3.6
CFLAGS=-I.
OS := $(shell uname)

verification_metrics: utils.cpp metrics_collector_t.cpp verification_metrics.cpp

ifeq ($(shell uname),Darwin)
	$(CC_MAC) -L/opt/local/lib/ -std=c++11 -lboost_system-mt -lboost_chrono-mt -lm -o verification_metrics utils.cpp metrics_collector_t.cpp verification_metrics.cpp -I /opt/local/include/ -Wno-everything
else
	$(CC_LINUX) -std=c++11 -lboost_system -lboost_chrono -lrt -o verification_metrics utils.cpp metrics_collector_t.cpp verification_metrics.cpp -Wno-everything
endif

clean:
	rm -f verification_metrics
