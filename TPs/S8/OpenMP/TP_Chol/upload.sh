#/usr/bin/bash

make clean

rm -f dosub.sh

cat <<EOF >> dosub.sh
#!/usr/bin/bash

#Job name
#SBATCH -J ${USER}
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
source \${HOME}/${USER}/TP_Chol_corr/env_cpuonly.sh

cd \${SLURM_SUBMIT_DIR}

# export OMP_NUM_THREADS=80

./bench_strong 200 60

./bench_weak 200 20
EOF

rsync --rsh='ssh -F none' -r ../TP_Chol_corr ${1}@turpanlogin.calmip.univ-toulouse.fr:${USER}/

