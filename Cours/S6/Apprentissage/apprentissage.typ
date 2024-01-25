#import "../../templates/template.typ": *
#set page(height: auto)
#show :project.with(title: "Cours - Apprentissage")

= Algorithmes
== Local Outlier Factor (LOF) (clustering)
Ca ressemble aux $k$-NN.
#definition[ Local density

  $ mu(x_i) = (1/abs((cal(N))_k (x_i)) sum_(x_j in cal(N)_k (x_i)) d_k (x_i, x_j))^(-1) $
  with $N_k (x_i)$ is the neighborhood if $x_i$ et $d_k$ is called _reachability distance_"

  $ op("LOF")_k (x_i) = (1/abs(N_k (x_i)) sum_(x_j in N_k (x_i)) mu(x_j)) / mu(x_i) $ ]

