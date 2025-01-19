import utils 
import sys
import numpy as np
import matplotlib.pyplot as plt
from collections import Counter


def main():
    ranges = [20_000, 40_000, 60_000]
    print(f"{sys.argv[1]}")
    fig_d, axs_d = plt.subplots(len(ranges))
    fig_c, axs_c = plt.subplots(len(ranges))
    fig_components, axs_components = plt.subplots(len(ranges))
    fig_cliques, axs_cliques = plt.subplots(len(ranges))

    for i in range(len(ranges)):
        r = ranges[i]
        print(f"Range {r} ------------------")
        graph = utils.build_graph(utils.load_data(sys.argv[1]), r)
        degrees = utils.degrees(graph)
        
        axs_d[i].hist(degrees, bins = len(degrees),color='skyblue', edgecolor='black')
        axs_d[i].set_title(f"Distribution des degrés pour {ranges[i]} m")

        print(f"Average degree: {np.mean(degrees)}")
        print(f"Clustering coefficient: {utils.clustering_distribution_coefficient(graph)}")

        local_clustering_coeffs = utils.list_local_clustering_coeffs(graph)
        axs_c[i].hist(local_clustering_coeffs, bins = len(local_clustering_coeffs),color='skyblue', edgecolor='black')
        axs_c[i].set_title(f"Distribution des coefficients de clustering local pour {ranges[i]} m")

        print(f"Average local clustering coefficient {np.mean(local_clustering_coeffs)}")

        connex_components=utils.connex_components(graph)
        data_cc=[len(x) for x in connex_components]
        print(f"Number of connex composants: {len(connex_components)}")
        axs_components[i].hist(data_cc, bins = max(data_cc),color='skyblue', edgecolor='black')

        axs_components[i].set_title(f"Distribution des tailles des composantes connexes pour {ranges[i]} m")

        cliques=utils.cliques(graph)
        data_c = [len(x) for x in cliques]
        print(f"Number of cliques: {len(cliques)}")
        axs_cliques[i].hist(data_c, bins= max(data_c),color='skyblue', edgecolor='black')
        axs_cliques[i].set_title(f"Distribution des tailles des cliques connexes pour {ranges[i]} m")

        
        
    
    plt.show()
    return 0

if __name__ == "__main__":
    main()
