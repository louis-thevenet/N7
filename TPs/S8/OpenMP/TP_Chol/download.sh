#/usr/bin/bash

# scp -F none ${1}@turpanlogin.calmip.univ-toulouse.fr:${USER}/TP_Chol_corr/\{\*.csv,\*.svg\} .

rsync --rsh='ssh -F none' -a --include='*.svg' --include='*.csv' --exclude='*' ${1}@turpanlogin.calmip.univ-toulouse.fr:${USER}/TP_Chol_corr/ .

gnuplot -p < plots.gp
