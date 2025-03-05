set terminal png size 800, 400 
set output "scalability_plot.png"
set multiplot layout 1,2 title "Scalability" font ",14"

set title "Strong scalability"
set key left top
set xlabel '\# threads'
set grid
set ylabel "Gflops/s"

plot 'strong_scalability.csv' using 2:4 with linespoints lw 2 t 'simple loop'  ,\
     'strong_scalability.csv' using 2:6 with linespoints lw 2 t 'improved loop',\
     'strong_scalability.csv' using 2:8 with linespoints lw 2 t 'tasks'


set title "Weak scalability"
set key right top
set xlabel '\# threads'
set grid
set ylabel "Gflops/s/core"

plot 'weak_scalability.csv' using 2:4 with linespoints lw 2 t 'simple loop'  ,\
     'weak_scalability.csv' using 2:6 with linespoints lw 2 t 'improved loop',\
     'weak_scalability.csv' using 2:8 with linespoints lw 2 t 'tasks'        

unset multiplot
