// File: main_convert.cpp
// -- conversion of a graph from ascii to binary, sample main file
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

#include "graph_binary.h"
#include "community.h"
#include "time.h"
#include <vector>

using namespace std;

char *infile      = NULL;
char *outfile     = NULL;
char *outfile_w   = NULL;
char *resultfile  = NULL;
int type          = UNWEIGHTED;
bool do_renumber  = false;
int inside_total  = 0;
int Total = 0;
vector<int> n2c;

int
main(int argc, char **argv) {
  infile = argv[1];
  resultfile = argv[2];

  Community c(infile, NULL, UNWEIGHTED, -1, 0.000001);

  n2c.resize(c.size);
  ifstream finput;
  finput.open(resultfile,fstream::in);
  while (!finput.eof()) {
    unsigned int id, comm;
    finput >> id >> comm;
    if (finput) {
      n2c[id]=comm;
    }
  }
  finput.close();

  for (int node=0 ; node<c.size ; node++) {
      for (unsigned int i = 0 ; i<c.neigh_last ; i++)
        c.neigh_weight[c.neigh_pos[i]]=-1;
      c.neigh_last = 0;

      pair<vector<unsigned int>::iterator, vector<float>::iterator> p = c.g.neighbors(node);

      unsigned int deg = c.g.nb_neighbors(node);
      int node_comm = n2c[node];

      for (unsigned int i = 0 ; i<deg ; i++) {
        unsigned int neigh        = *(p.first+i);
        unsigned int neigh_comm   = n2c[neigh];
        //cerr<<"node, node_comm, neigh, neigh_comm"<<node<<", "<<node_comm<<", "<<neigh<<", "<<neigh_comm<<endl;
        if (node_comm==neigh_comm) {
          inside_total++; 
        }
        Total++;
      }
  }
  cerr<<"Total, Inside::"<<Total<<", "<<inside_total<<endl;
}