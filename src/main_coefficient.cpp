// File: main_community.cpp
// -- community detection, sample main file
//-----------------------------------------------------------------------------
// Community detection 
// Based on the article "Fast unfolding of community hierarchies in large networks"
// Copyright (C) 2008 V. Blondel, J.-L. Guillaume, R. Lambiotte, E. Lefebvre
//
// This program must not be distributed without agreement of the above mentionned authors.
//-----------------------------------------------------------------------------
// Author   : E. Lefebvre, adapted by J.-L. Guillaume
// Email    : jean-loup.guillaume@lip6.fr
// Location : Paris, France
// Time	    : February 2008
//-----------------------------------------------------------------------------
// see readme.txt for more details

#include <stdlib.h>
#include <math.h>
#include <string>
#include <iostream> 
#include <fstream>
#include <sstream>
#include <vector>
#include <algorithm>
#include <unistd.h>
#include "graph_binary.h"
#include "community.h"
#include "time.h"
#include "iterator"

using namespace std;

char *filename = NULL;
char *outfile  = NULL;
Graph g;

vector<int>
getNeighbors(int node, int deg )
{
	vector<int> neighbor;
	neighbor.resize(deg);
  	pair<vector<unsigned int>::iterator, vector<float>::iterator> p = g.neighbors(node);
	for (unsigned int i=0 ; i < deg ; i++) {
		unsigned int neigh    = *(p.first+i); 
		neighbor[i] = neigh;
	}
	return neighbor;  
}

void
parse_args(int argc, char **argv) {
  if (argc<1)
    cerr<<"Bad arguments number\n"<<endl;

  for (int i = 1; i < argc; i++) {
    if(argv[i][0] == '-') {
      switch(argv[i][1]) {
      case 'i':
        filename = argv[i+1];
	i++;
	break;
      case 'o':
    	outfile  = argv[i+1];
	i++;
	break;
      default:
		cerr<<"Unknown option\n"<<endl;
      }
    } 
  }
}

int
main(int argc, char **argv) {
	cerr << "Compute Node Coefficient start!!" << endl;
	parse_args(argc, argv);

	g = Graph(filename, NULL, UNWEIGHTED);
	int size = g.nb_nodes;
	
	vector<int> neighbor;
	vector<vector<int> > neighneighbor;
	vector<double> coefficient;
	coefficient.resize(size);
	int sum = 0;
	double total = 0.;
	for (int node = 0; node < size; node++) {
  		sum = 0;
  		unsigned int deg = g.nb_neighbors(node);
  		pair<vector<unsigned int>::iterator, vector<float>::iterator> p = g.neighbors(node);
		neighbor.resize(deg);
		neighneighbor.resize(deg);
		for (unsigned int i=0 ; i < deg ; i++) {
			unsigned int neigh    = *(p.first+i);
			unsigned int neighDeg = g.nb_neighbors(neigh); 
			neighbor[i] = neigh;
			neighneighbor[i].resize(neighDeg);
			neighneighbor[i] = getNeighbors(neigh, neighDeg);
		}
		for (int i = 0; i < deg; ++i){
			sort(neighbor.begin(), neighbor.end());
			sort(neighneighbor[i].begin(), neighneighbor[i].end());
			vector<int> intersection;
    		set_intersection(neighbor.begin(), neighbor.end()
                     , neighneighbor[i].begin(), neighneighbor[i].end()
                     , inserter(intersection, intersection.end()));
			sum += intersection.size();
		}
		if( deg == 1 || deg == 0)  coefficient[node] = 0.;
		else if ( deg == 2 ) coefficient[node] = sum / 2;
		else	coefficient[node] = (double)( sum ) / (deg * ( deg - 1 ));
  		total += coefficient[node];
  	}

	ofstream foutput;
	foutput.open(outfile ,fstream::out | fstream::binary);
	for (int i = 0; i < coefficient.size(); ++i){	
		foutput.write((char *)(&coefficient[i]), 8);
	}
	foutput.close();
	cerr << "Data:: " << filename << ", " << "coefficient:: " << (double) total / size << endl;
  	// Read number of nodes on 4 bytes
  	cerr << "Data Size is::" << size << endl;
  	cerr << "Compute Node Coefficient end!!" << endl;
}