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

#include "community.h"
#include "time.h"
using namespace std;

//class Log1 { public: int times; double increase; public: Log1(){ } public: Log1(int t, double i){ times = t; increase = i;} };
//class Log2 { public: int pass; double increase; int computeTimes; public: Log2(){ } public: Log2(int t, double i, int ct){ pass = t; increase = i; computeTimes = ct; } };
//class LogMove { public: int src; int best_comm; public: LogMove(){ } public: LogMove(int s, int b){ src = s; best_comm = b;} };
//class LogDelta{ public: double increase; public: LogDelta(){} public: LogDelta(double i){ increase = i;}};
class LogDegree{ public: int src; int src_deg; int dst; int dst_deg; double dnodecomm; double deltaQ; public: LogDegree(){} 
                 public: LogDegree( int s, double sd, int d, double dd, double dnode, double q ){ 
                 src = s; src_deg = sd; dst = d; dst_deg = dd; dnodecomm = dnode; deltaQ = q;}
               };
class LogBest{public: int pass; int src; int src_deg; int dst; int dst_deg; double deltaQ; public: LogBest(){} 
                 public: LogBest( int p, int s, double sd, int d, double dd, double q ){ 
                 pass = p; src = s; src_deg = sd; dst = d; dst_deg = dd; deltaQ = q;}
              };
Community::Community(char * filename, char * filename_w, int type, int nbp, double minm) {
  g = Graph(filename, filename_w, type);
  size = g.nb_nodes;

  neigh_weight.resize(size,-1);
  neigh_pos.resize(size);
  neigh_last=0;

  n2c.resize(size);
  in.resize(size);
  tot.resize(size);

  for (int i=0 ; i<size ; i++) {
    n2c[i] = i;
    tot[i] = g.weighted_degree(i);
    in[i]  = g.nb_selfloops(i);
  }

  nb_pass = nbp;
  min_modularity = minm;
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

  for (int i=0 ; i<size ; i++) {
    n2c[i] = i;
    in[i]  = g.nb_selfloops(i);
    tot[i] = g.weighted_degree(i);
  }

  nb_pass = nbp;
  min_modularity = minm;
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
Community::modularity(){
  double q  = 0.;
  double m2 = (double)g.total_weight;
  //double m2 = total_weight;

  for (int i=0 ; i<size ; i++) {
    if (tot[i]>0)
      q += (double)in[i]/m2 - ((double)tot[i]/m2)*((double)tot[i]/m2);
  }

  return q;
}

void
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
}

void
Community::partition2graph() {
  vector<int> renumber(size, -1);
  for (int node=0 ; node<size ; node++) {
    cerr<<node<<", "<<n2c[node]<<endl;
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
  
  vector<vector<int> > comm_list(size);
    
  for (int node=0 ; node<size ; node++)
  {
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
Community::one_level( int level, char * filename ) {
  // vector<Log1> log1;
  // vector<Log2> log2;
  // vector<LogMove> logmove;
  //vector<LogDelta> logdelta;
  vector<LogDegree> logdegree;
  vector<LogBest> logbest;

  bool improvement = false ;
  int nb_moves     = 0;
  int nb_pass_done = 0;

  double new_mod   = modularity();
  double cur_mod   = new_mod;

  vector<int> random_order(size);
  for (int i=0 ; i<size ; i++)
    random_order[i]=i;
  for (int i=0 ; i<size-1 ; i++) {
    int rand_pos = rand()%(size-i)+i;
    int tmp      = random_order[i];
    random_order[i] = random_order[rand_pos];
    random_order[rand_pos] = tmp;
  }

  // repeat while 
  //   there is an improvement of modularity
  //   or there is an improvement of modularity greater than a given epsilon 
  //   or a predefined number of pass have been done
  int times = 0;
  double totalTimes = 0.;  
  int    nodeTimes  = 0;
  double before = cur_mod;
  do {
    cur_mod = new_mod;
    nb_moves = 0;
    totalTimes += times;
    times     = 0;

    //cerr<<"Pass:: "<<nb_pass_done<<endl;
    // for each node: remove the node from its community and insert it in the best community
    for (int node_tmp=0 ; node_tmp<size ; node_tmp++) {
      //int node = random_order[node_tmp];
      int node = node_tmp;
      int node_comm     = n2c[node];
      double w_degree = g.weighted_degree(node);

      // computation of all neighboring communities of current node
      neigh_comm(node);
      // remove node from its current community
      remove(node, node_comm, neigh_weight[node_comm]);

      // compute the nearest community for node
      // default choice for future insertion is the former community
      int    best_comm     = node_comm;
      double best_nblinks  = neigh_weight[best_comm];
      double best_increase = modularity_gain(node, neigh_pos[0], neigh_weight[neigh_pos[0]], w_degree);

     // if (level==0){
          int    neigh_comm   = neigh_pos[0]; 
          double dnodecomm    = neigh_weight[neigh_comm];
          double commTot      = tot[neigh_comm]; 
          int    maxDnodecomm = dnodecomm;
          int    minTot       = commTot;
          vector<int> nodeList;
          //cerr<<"node, neigh_comm:: "<<node<<", "<<neigh_comm<<endl;
          nodeList.push_back(neigh_comm);
          for (unsigned int i = 1; i < neigh_last; i++){   
              neigh_comm = neigh_pos[i];
              //cerr<<"node, neigh_comm:: "<<node<<", "<<neigh_comm<<endl;
              dnodecomm  = neigh_weight[neigh_comm];
              if ( maxDnodecomm < dnodecomm){
                  nodeList.clear();
                  maxDnodecomm = dnodecomm;
                  nodeList.push_back(neigh_comm);
              }
              else if (maxDnodecomm == dnodecomm){
                  nodeList.push_back(neigh_comm);
              }    
          }
          best_comm = nodeList[0]; 
          if (nodeList.size() > 1){
              minTot = tot[nodeList[0]];
             // if( node < 10100 && node >= 10000) cerr<<"neigh_comm, tot::"<<nodeList[0]<<", "<<tot[nodeList[0]] <<endl;
              for (unsigned int i = 1; i < nodeList.size(); ++i){  
              //if( node < 10100 && node >= 10000)  cerr<<"neigh_comm, tot::"<<nodeList[i]<<", "<<tot[nodeList[i]] <<endl;
                 
                 if ( minTot > tot[nodeList[i]] ){
                   minTot = tot[nodeList[i]];
                   best_comm = nodeList[i];
                 }
              }
          }
          best_nblinks = neigh_weight[best_comm];
          //if( node < 10100 && node >= 10000 ) cerr<<"node, best:: "<<node<<", "<<best_comm<<endl;
      // }
      // else{
      //     for (unsigned int i=1 ; i<neigh_last ; i++) {
      //       double increase = modularity_gain(node, neigh_pos[i], neigh_weight[neigh_pos[i]], w_degree);
      //       times++;
      //       nodeTimes++;
      //       // if ( level == 0 /*&& nodeTimes < size*/ ){ 
      //       //   logdegree.push_back(LogDegree(node, g.nb_neighbors(node), neigh_pos[i], tot[neigh_pos[i]], neigh_weight[neigh_pos[i]], increase)); }
      //       if (increase > best_increase) {
      //         best_comm     = neigh_pos[i];
      //         best_nblinks  = neigh_weight[neigh_pos[i]];
      //         best_increase = increase;
      //       }
      //     }
      // }
      
      //if ( level == 0 /*&& nodeTimes < size*/ ){         logdegree.push_back(LogDegree(node, g.nb_neighbors(node), neigh_pos[0], tot[neigh_pos[0]], neigh_weight[neigh_pos[0]], best_increase));  }
      // nodeTimes++;
      // for (unsigned int i=1 ; i<neigh_last ; i++) {
      //   double increase = modularity_gain(node, neigh_pos[i], neigh_weight[neigh_pos[i]], w_degree);
      //   times++;
      //   nodeTimes++;
      //   // if ( level == 0 /*&& nodeTimes < size*/ ){ 
      //   //   logdegree.push_back(LogDegree(node, g.nb_neighbors(node), neigh_pos[i], tot[neigh_pos[i]], neigh_weight[neigh_pos[i]], increase)); }
      //   if (increase > best_increase) {
      //     best_comm     = neigh_pos[i];
      //     best_nblinks  = neigh_weight[neigh_pos[i]];
      //     best_increase = increase;
      //   }
      // }

      /*if ( level == 0 && nodeTimes % 10000 < 20 ){
        new_mod = modularity();
        logdelta.push_back(LogDelta((new_mod - before)));
        before = new_mod;
        nodeTimes = 0;
      }*/

      // insert node in the nearest community
      insert(node, best_comm, best_nblinks);
      // if ( level == 0/* && nb_pass_done < 3*/){ 
      //     logbest.push_back(LogBest( nb_pass_done,node, g.nb_neighbors(node), best_comm, tot[best_comm], best_increase)); }
      //if ( level == 0 ) { logmove.push_back(LogMove(node, best_comm)); }
      /*nodeTimes++;      
      if (( level == 0 ) && (nodeTimes % 10000 == 0))
      {
        new_mod = modularity();
        log1.push_back( Log1(nodeTimes / 10000, (new_mod - before)));
        before = new_mod;
        increase_per_Ntimes = 0.;
      }*/

      if (best_comm!=node_comm)
        nb_moves++;
    }

    totalTimes += times; 
    new_mod = modularity();
    nb_pass_done++;


    /*if ( level == 0 )
    {
      log2.push_back( Log2(nb_pass_done, new_mod, times) );
    }*/ 
    
    if (nb_moves>0)
      improvement=true;  
  } while (nb_moves>0 && new_mod-cur_mod>min_modularity);

  if ( level == 0 )
  {
    // ofstream csvdelta, csvbest;
    // time_t  nowtime = time(NULL);  
    // struct  tm  *p;  
    // p = gmtime(&nowtime);  
    // char    filename[256] = {0};  
    // sprintf(filename,"../Result/Increase/%d%d%d-%d%d%d-0-detail-origin.csv", 1900+p->tm_year, 1+p->tm_mon, p->tm_mday, p->tm_hour, p->tm_min, p->tm_sec);  
    // csvdelta.open(filename);
    // for (vector<LogDegree>::iterator iter1 = logdegree.begin(); iter1 != logdegree.end(); ++iter1) {
    //   LogDegree entry1 = *iter1;
    //   csvdelta << entry1.src << ", " << entry1.src_deg << ", " << entry1.dst << ", " << entry1.dst_deg << ", " << entry1.dnodecomm << ", " <<entry1.deltaQ <<endl;
    // }
    // csvdelta.close();
    // sprintf(filename,"../Result/Increase/%d%d%d-%d%d%d-0-best-origin.csv", 1900+p->tm_year, 1+p->tm_mon, p->tm_mday, p->tm_hour, p->tm_min, p->tm_sec);  
    // csvbest.open(filename);
    // for (vector<LogBest>::iterator iter1 = logbest.begin(); iter1 != logbest.end(); ++iter1) {
    //   LogBest entry1 = *iter1;
    //   csvbest << entry1.pass <<", "<<entry1.src << ", " << entry1.src_deg << ", " << entry1.dst << ", " << entry1.dst_deg << ", " << entry1.deltaQ <<endl;
    // }
    // csvbest.close();
    /*ofstream csv1, csv2, csvmove;
    time_t  nowtime = time(NULL);  
    struct  tm  *p;  
    p = gmtime(&nowtime);  
    char    filename[256] = {0};  
    sprintf(filename,"../Result/Increase/%d%d%d-%d%d%d-0-origin.csv", 1900+p->tm_year, 1+p->tm_mon, p->tm_mday, p->tm_hour, p->tm_min, p->tm_sec);  
    csv1.open(filename);
    for (vector<Log1>::iterator iter1 = log1.begin(); iter1 != log1.end(); ++iter1) {
      Log1 entry1 = *iter1;
      csv1 << entry1.times << ", " << entry1.increase << endl;
    }
    csv1.close();
    sprintf(filename,"../Result/Pass/%d%d%d-%d%d%d-1-origin.csv", 1900+p->tm_year, 1+p->tm_mon, p->tm_mday, p->tm_hour, p->tm_min, p->tm_sec);  
    csv2.open(filename);
    for (vector<Log2>::iterator iter1 = log2.begin(); iter1 != log2.end(); ++iter1) {
      Log2 entry1 = *iter1;
      csv2 << entry1.pass << ", " << entry1.increase << ", " <<  entry1.computeTimes << endl;
    }
    csv2.close();
    sprintf(filename,"../Result/Pass/%d%d%d-%d%d%d-1-move-origin.csv", 1900+p->tm_year, 1+p->tm_mon, p->tm_mday, p->tm_hour, p->tm_min, p->tm_sec);  
    csvmove.open(filename);
    for (vector<LogMove>::iterator iter1 = logmove.begin(); iter1 != logmove.end(); ++iter1) {
      LogMove entry1 = *iter1;
      csvmove << entry1.src << ", " << entry1.best_comm << endl;
    }
    csvmove.close();*/
  }
  improvement = false;
  cerr<<"Level "<<level<<":: TotalTimes::"<<totalTimes<<endl;
  return improvement;
}

