#!/bin/sh
cd $PBS_O_WORKDIR
mpirun -n 1 -hostfile $PBS_NODEFILE ./community  relation.bin -l -1 -v > relation.tree 
