#!/bin/bash

CXX=clang++ -std=c++11 -O3   
CFLAGS=  -O3 -Wall
LDFLAGS= -lm -Wall
ALL=community convert hierarchy coefficient
OBJ1= graph_binary.o community.o
OBJ2= graph.o

all: $(ALL)

community : $(OBJ1) main_community.o
	$(CXX) -o $@ $^ $(LDFLAGS)

convert : $(OBJ2) main_convert.o
	$(CXX) -o $@ $^ $(LDFLAGS)

hierarchy : main_hierarchy.o
	$(CXX) -o $@ $^ $(LDFLAGS)

coefficient : $(OBJ1) main_coefficient.o
	$(CXX) -o $@ $^ $(LDFLAGS)

.HONY: install

install: all
	cp $(ALL) ../bin

##########################################
# Generic rules
##########################################

%.o: %.cpp %.h
	$(CXX) -o $@ -c $< $(CFLAGS)

%.o: %.cpp
	$(CXX) -o $@ -c $< $(CFLAGS)

clean:
	rm -f *.o *~ $(ALL)
