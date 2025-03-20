#!/usr/bin/bash

#Job name
#SBATCH -J ltt5092
# Asking for one node
#SBATCH -N 1
#SBATCH -n 1
#SBATCH -p small
#SBATCH --ntasks-per-node=1
# Output results message
#SBATCH -o chol%j.out
# Output error message
#SBATCH -e chol%j.err
#SBATCH -t 0:05:00
##SBATCH --exclusive

module purge
source ${HOME}/ltt5092/TP_Chol/env_cpuonly.sh

cd ${SLURM_SUBMIT_DIR}

# export OMP_NUM_THREADS=80

./bench_strong 200 60

./bench_weak 200 20
