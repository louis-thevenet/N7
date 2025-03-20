#/usr/bin/bash

# scp -F none ${1}@turpanlogin.calmip.univ-toulouse.fr:${USER}/TP_Chol/\{\*.csv,\*.svg\} .

rsync --rsh='ssh -F none' -a --include='*.svg' --include='*.csv' --exclude='*' ${1}@turpanlogin.calmip.univ-toulouse.fr:${USER}/TP_Chol/ .

gnuplot -p < plots.gp
