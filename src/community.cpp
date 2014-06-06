// File: community.h
// -- community detection source file
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
#include <libgen.h>

#include "community.h"
#include "functional"
#include "algorithm"
#include "time.h"
using namespace std;

/*class LogMod{ public: int passNum; int nodeNum; int src_deg; int edgeWeight; int dst; double dst_tot; double dst_in; double increase; 
  public: LogMod(){} 
  public: LogMod(int pn, int nm, int sd, int ew, int d, int dd, int dc, double i){ 
    passNum = pn;  nodeNum    = nm; 
    src_deg = sd;  edgeWeight = ew;   
    dst     = d;   dst_tot    = dd;   
    dst_in  = dc;  increase   = i ;}};*/

//class LogMod{ public: int passNum; int nodeNum; int srcDeg; double edgeWeight; double increase; double coeff; int comSize; public: LogMod(){} public: LogMod(int pn, int nm, int sd, double ew, double i, double cf, int cs){ passNum = pn; nodeNum = nm; srcDeg = sd; edgeWeight = ew; increase = i; coeff = cf; comSize = cs;}};
class LogMod{ public: double increase; public: LogMod(){} public: LogMod(double i){ increase = i; }};
//class LogTime{public: double Computetime; public:LogTime(){} public:LogTime(double i){ Computetime = i; }};
class LogDeltaMod{ public: double increase; public: LogDeltaMod(){} public: LogDeltaMod(double i){ increase = i; }};


inline bool
Community::great_second(const Pair & m1, const Pair & m2) {
        return m1.second > m2.second;
}


Community::Community(char * filename, char * filename_w, char * filename_coe, int type, int nbp, double minm) {
  g = Graph(filename, filename_w, type);
  size = g.nb_nodes;

  neigh_weight.resize(size,-1);
  neigh_pos.resize(size);
  neigh_last=0;

  coefficient.resize(size);
  commCoeff.resize(size);
  n2c.resize(size);
  in.resize(size);
  tot.resize(size);
  isChanged.resize(size);
  changedComm.resize(size);

  for (int i=0 ; i<size ; i++) {
    n2c[i] = i;
    tot[i] = g.weighted_degree(i);
    in[i]  = g.nb_selfloops(i);
    isChanged[i]   = false;
    changedComm[i] = -1;
  }

  nb_pass = nbp;
  min_modularity = minm;
  node_deg = 0;
  //read coefficient file 
  /*ifstream finput_c;
  finput_c.open(filename_coe,fstream::in | fstream::binary);
  for (int i = 0; i < size; ++i)
  {
    finput_c.read((char *)(&coefficient[i]), 8);
    commCoeff[i] = coefficient[i];
  }*/
}

Community::Community(Graph gc, int nbp, double minm) {
  g = gc;
  size = g.nb_nodes;

  neigh_weight.resize(size,-1);
  neigh_pos.resize(size);
  neigh_last=0;

  n2c.resize(size);
  in.resize(size);
  tot.resize(size);
  isChanged.resize(size);
  changedComm.resize(size);

  for (int i=0 ; i<size ; i++) {
    n2c[i] = i;
    in[i]  = g.nb_selfloops(i);
    tot[i] = g.weighted_degree(i);
    isChanged[i] = false;
    changedComm[i] = -1;
  }

  nb_pass = nbp;
  min_modularity = minm;
  node_deg = 0;
}

void
Community::init_partition(char * filename) {
  ifstream finput;
  finput.open(filename,fstream::in);

  // read partition
  while (!finput.eof()) {
    unsigned int node, comm;
    finput >> node >> comm;
    
    if (finput) {
      int old_comm = n2c[node];
      neigh_comm(node);

      remove(node, old_comm, neigh_weight[old_comm]);

      unsigned int i=0;
      for ( i=0 ; i<neigh_last ; i++) {
	unsigned int best_comm     = neigh_pos[i];
	float best_nblinks  = neigh_weight[neigh_pos[i]];
	if (best_comm==comm) {
	  insert(node, best_comm, best_nblinks);
	  break;
	}
      }
      if (i==neigh_last)
	insert(node, comm, 0);
    }
  }
  finput.close();
}

void
Community::display() {
  for (int i=0 ; i<size ; i++)
    cerr << " " << i << "/" << n2c[i] << "/" << in[i] << "/" << tot[i] ;
  cerr << endl;
}


double
Community::modularity() {
  double q  = 0.;
  double m2 = (double)g.total_weight;

  for (int i=0 ; i<size ; i++) {
    if (tot[i]>0)
      q += (double)in[i]/m2 - ((double)tot[i]/m2)*((double)tot[i]/m2);
  }

  return q;
}

inline int 
Community::getCommSize( int comm ){
  int commSize = 0;
  double  coef = 0.;      
  for (int i = 0; i < size; ++i)
  {
    int commNum = n2c[i];
    if ( commNum == comm ){
      coef += coefficient[i];
      commSize++;
    }
  }
  commCoeff[comm] = (double)coef / commSize;
  return commSize;
}

inline int
Community::neigh_comm(unsigned int node) {
  for (unsigned int i=0 ; i<neigh_last ; i++)
    neigh_weight[neigh_pos[i]]=-1;
  neigh_last=0;

  pair<vector<unsigned int>::iterator, vector<float>::iterator> p = g.neighbors(node);

  unsigned int deg = g.nb_neighbors(node);

  neigh_pos[0]=n2c[node];
  neigh_weight[neigh_pos[0]]=0;
  neigh_last=1;

  for (unsigned int i=0 ; i<deg ; i++) {
    unsigned int neigh        = *(p.first+i);
    unsigned int neigh_comm   = n2c[neigh];
    double neigh_w = (g.weights.size()==0)?1.:*(p.second+i);
    
    if (neigh!=node) {
      if (neigh_weight[neigh_comm]==-1) {
	neigh_weight[neigh_comm]=0.;
	neigh_pos[neigh_last++]=neigh_comm;
      }
      neigh_weight[neigh_comm]+=neigh_w;
    }
  }
  return deg;
}

inline bool
Community::neigh_comm( unsigned int node, unsigned int nb_pass_done ) {
  bool isCompute = false;
  for (unsigned int i=0 ; i<neigh_last ; i++)
    neigh_weight[neigh_pos[i]]=-1;
  neigh_last=0;

  pair<vector<unsigned int>::iterator, vector<float>::iterator> p = g.neighbors(node);

  unsigned int deg = g.nb_neighbors(node);
  node_deg = 0;
  node_deg = deg;
  neigh_pos[0]=n2c[node];
  neigh_weight[neigh_pos[0]]=0;
  neigh_last=1;

  for (unsigned int i=0 ; i<deg ; i++) {
    unsigned int neigh        = *(p.first+i);
    unsigned int neigh_comm   = n2c[neigh];
    double neigh_w = (g.weights.size()==0)?1.:*(p.second+i);
    if( nb_pass_done !=1 && isChanged[neigh_comm] ){
        isCompute = true;
        //continue;
    }
    if (neigh!=node) {
      if (neigh_weight[neigh_comm]==-1) {
        neigh_weight[neigh_comm]=0.;
        neigh_pos[neigh_last++]=neigh_comm;
    }
      neigh_weight[neigh_comm]+=neigh_w;
    }
  }
  if(nb_pass_done == 1) return true;
  return isCompute;
  //return deg;
}

void
Community::partition2graph() {
  vector<int> renumber(size, -1);
  for (int node=0 ; node<size ; node++) {
    renumber[n2c[node]]++;
  }

  int final=0;
  for (int i=0 ; i<size ; i++)
    if (renumber[i]!=-1)
      renumber[i]=final++;


  for (int i=0 ; i<size ; i++) {
    pair<vector<unsigned int>::iterator, vector<float>::iterator> p = g.neighbors(i);

    int deg = g.nb_neighbors(i);
    for (int j=0 ; j<deg ; j++) {
      int neigh = *(p.first+j);
      cout << renumber[n2c[i]] << " " << renumber[n2c[neigh]] << endl;
    }
  }
}

void
Community::display_partition() {
  vector<int> renumber(size, -1);
  for (int node=0 ; node<size ; node++) {
    renumber[n2c[node]]++;
  }

  int final=0;
  for (int i=0 ; i<size ; i++)
    if (renumber[i]!=-1)
      renumber[i]=final++;

  for (int i=0 ; i<size ; i++)
    cout << i << " " << renumber[n2c[i]] << endl;
}


Graph
Community::partition2graph_binary() {
  // Renumber communities
  vector<int> renumber(size, -1);
  for (int node=0 ; node<size ; node++) {
    renumber[n2c[node]]++;
  }

  int final=0;
  for (int i=0 ; i<size ; i++)
    if (renumber[i]!=-1)
      renumber[i]=final++;

  // Compute communities
  vector<vector<int> > comm_nodes(final);
  for (int node=0 ; node<size ; node++) {
    comm_nodes[renumber[n2c[node]]].push_back(node);
  }

  // Compute weighted graph
  Graph g2;
  g2.nb_nodes = comm_nodes.size();
  g2.degrees.resize(comm_nodes.size());

  int comm_deg = comm_nodes.size();
  for (int comm=0 ; comm<comm_deg ; comm++) {
    map<int,float> m;
    map<int,float>::iterator it;

    int comm_size = comm_nodes[comm].size();
    for (int node=0 ; node<comm_size ; node++) {
      pair<vector<unsigned int>::iterator, vector<float>::iterator> p = g.neighbors(comm_nodes[comm][node]);
      int deg = g.nb_neighbors(comm_nodes[comm][node]);
      for (int i=0 ; i<deg ; i++) {
	int neigh        = *(p.first+i);
	int neigh_comm   = renumber[n2c[neigh]];
	double neigh_weight = (g.weights.size()==0)?1.:*(p.second+i);

	it = m.find(neigh_comm);
	if (it==m.end())
	  m.insert(make_pair(neigh_comm, neigh_weight));
	else
	  it->second+=neigh_weight;
      }
    }
    g2.degrees[comm]=(comm==0)?m.size():g2.degrees[comm-1]+m.size();
    g2.nb_links+=m.size();

    
    for (it = m.begin() ; it!=m.end() ; it++) {
      g2.total_weight  += it->second;
      g2.links.push_back(it->first);
      g2.weights.push_back(it->second);
    }
  }

  return g2;
}


bool
Community::one_level( int level, char * fileName ) {
  vector<LogMod> logmod;
  vector<LogDeltaMod> logdelta;
  //vector<LogTime> logtime;
  bool improvement=false ;
  int nb_moves;
  int nb_pass_done = 0;
  double new_mod   = modularity();
  double cur_mod   = new_mod;
  //for changing heuristics automatically when the compute efficiency is decreasing.
  bool change = false;

  vector<int> random_order(size);
  for (int i=0 ; i<size ; i++)
    random_order[i]=i;
  for (int i=0 ; i< (size-1) ; i++) {
    int rand_pos = rand()%(size-i)+i;
    int tmp      = random_order[i];
    random_order[i] = random_order[rand_pos];
    random_order[rand_pos] = tmp;
  }

  // repeat while 
  //   there is an improvement of modularity
  //   or there is an improvement of modularity greater than a given epsilon 
  //   or a predefined number of pass have been done
  int nodeTimes = 0;
  double before1 = cur_mod;
  double before2 = 0; 
  int t = 0;
  do {
    cur_mod = new_mod;
    nb_moves = 0;
    nb_pass_done++;
    //cerr<< "Pass::" << nb_pass_done << endl;
    // for each node: remove the node from its community and insert it in the best community
    for (int node_tmp=0 ; node_tmp<size ; node_tmp++) {
      //int node = node_tmp;
      int node = random_order[node_tmp];
      int node_comm     = n2c[node];
      double w_degree = g.weighted_degree(node);

      // computation of all neighboring communities of current node
      //int deg = neigh_comm(node);
      bool isCompute = neigh_comm(node, nb_pass_done);
      if( !isCompute ) continue;
      // remove node from its current community
      remove(node, node_comm, neigh_weight[node_comm]);

      int    best_comm     = node_comm;
      double best_nblinks  = neigh_weight[best_comm];
      double best_increase = modularity_gain(node, best_comm, best_nblinks, w_degree);
      //if (level == 0)logmod.push_back(LogMod( nb_pass_done, node, g.nb_neighbors(node) , best_nblinks, best_comm, tot[best_comm], in[best_comm], best_increase));
      nodeTimes++;
      bool isNum = false;
      #define MAX_CMP 3

      if( level == 0 && neigh_last > MAX_CMP && change ) {
        vector<Pair> comm_weight;
        for (int i = 1; i < neigh_last; ++i)
        {
          int    theN2C    = neigh_pos[i];
          double theWeight = neigh_weight[theN2C];
          Pair p(theN2C, theWeight);
          comm_weight.push_back(p);
        }
        sort(comm_weight.begin(), comm_weight.end(), great_second);
        for (int i = 0; i < 3; ++i)
        {
            int    theN2C    = comm_weight[i].first;
            double theWeight = comm_weight[i].second;
            double increase  = modularity_gain(node, theN2C, theWeight, w_degree);
          //if (level == 0)logmod.push_back(LogMod( nb_pass_done, node, g.nb_neighbors(node), theWeight, theN2C, tot[theN2C], in[theN2C], increase));
            nodeTimes++;
            if(nodeTimes % 10000 == 0) isNum = true;
            //logmod.push_back(LogMod( nb_pass_done, node, deg, theWeight, increase));
            if (increase > best_increase) {
                best_comm     = theN2C;
                best_nblinks  = theWeight;
                best_increase = increase;
            }  
        }
      } else {
        //logmod.push_back(LogMod( nb_pass_done, node, deg, best_nblinks, best_increase));
        pair<vector<unsigned int>::iterator, vector<float>::iterator> p = g.neighbors(node);
                if(/*neigh_last*/node_deg > MAX_CMP)
                {
                //int index = rand()%neigh_last;
                //int index = rand()%deg;
                int index = rand() % node_deg; 
                for(int i = 1 ; i < MAX_CMP; i++ ){ 
                  int neigh_node  = *(p.first + index);
                  if (node == neigh_node) 
                    {
                      if ( node_deg <= 6 ) index = ( index + 1 ) %node_deg;
                      else index = rand() % node_deg; 
                      continue;
                    } 
                  int theN2C = n2c[neigh_node];
                  double theWeight = neigh_weight[theN2C];
                  double increase = modularity_gain(node, theN2C, theWeight, w_degree);
                  nodeTimes++;
                  if(nodeTimes % 10000 == 0) isNum = true;
                  if (increase > best_increase) {
                    best_comm     = theN2C;
                    best_nblinks  = theWeight;
                    best_increase = increase;
                    }
                  if ( node_deg <= 6 ) index = ( index + 1 ) %node_deg;
                  else index = rand() % node_deg; 
                }
                }
                else {
                for(unsigned int i = 1; i < neigh_last; i++){  
                  int    theN2C    = neigh_pos[i];
                  double theWeight = neigh_weight[theN2C];
                  double increase  = modularity_gain(node, theN2C, theWeight, w_degree);
                  //if (isWrite == 0)logmod.push_back(LogMod( nb_pass_done, node, theWeight, neigh_node, g.nb_neighbors(neigh_node), best_increase));
                  nodeTimes++;
                  if(nodeTimes % 10000 == 0) isNum = true;
                  if (increase > best_increase) {
                      best_comm     = theN2C;
                      best_nblinks  = theWeight;
                      best_increase = increase;
                  }
                }
                }
      }
      // insert node in the nearest community
      insert(node, best_comm, best_nblinks);
      if (isNum && level == 0){
         double newMod = modularity();
         //logdelta.push_back(LogDeltaMod(newMod - before1));
         logmod.push_back(LogMod( newMod ));
        double deltaMod1 = before1 - before2;
        double deltaMod2 = newMod  - before1;
        if( deltaMod2 - deltaMod1 < 0. ) change = true;
        before2 = before1;
        before1 = newMod;
         nodeTimes = 0;
         isNum = false;
         t++;
      }

      if (best_comm!=node_comm){
        changedComm[best_comm] = 1;
        changedComm[node_comm] = 1;
        nb_moves++;
      }
    }
    isChanged.clear();
    for (int i = 0; i < size; ++i)
    {
      int changed = changedComm[i];
      isChanged[i] = ( changed > 0 ) ? true : false;
      changedComm[i] = -1;
    }
    new_mod = modularity();
    // cerr<<" Pass"<<nb_pass_done<<" ::"<<new_mod<<endl;
    if (nb_moves>0)
      improvement=true;
    
  } while (nb_moves>0 && new_mod-cur_mod>min_modularity);
  if (level == 0)
  {
    ofstream csvdelta;//csvbest, csvdelta, sv1, csv2, csvDetail, csvmove;
    time_t  nowtime = time(NULL);  
    struct  tm  *p;  
    p = gmtime(&nowtime);  
    char    filename[256] = {0};
    sprintf(filename, "/Users/donaldchi/Dropbox/x10/Data/ChangeTime/%s-%d-mod-optmax-time-auto.csv", basename(fileName), level);  
    csvdelta.open(filename);
    for (vector<LogMod>::iterator iter1 = logmod.begin(); iter1 != logmod.end(); ++iter1) {
      LogMod entry1 = *iter1;
      csvdelta << entry1.increase << endl;
      // csvdelta << entry1.passNum << ",\t" << entry1.nodeNum    << ",\t" 
      //          << entry1.src_deg << ",\t" << entry1.edgeWeight << ",\t"
      //          << entry1.dst     << ",\t" << entry1.dst_tot    << ",\t" 
      //          << entry1.dst_in  << ",\t" << entry1.increase <<endl;
    }
    csvdelta.close();
    //     sprintf(filename, "/Users/donaldchi/Dropbox/x10/Data/OptMaxToOptMaxPlusRC/%s-%d-deltaMod-optmax-time.csv", basename(fileName), level);  
    // csvdelta.open(filename);
    // for (vector<LogDeltaMod>::iterator iter1 = logdelta.begin(); iter1 != logdelta.end(); ++iter1) {
    //   LogDeltaMod entry1 = *iter1;
    //   csvdelta << entry1.increase << endl;
    // }
    // csvdelta.close();
  }
  return improvement;
}

