import csv 
from math import sqrt
import statistics
import numpy as np
import math 

def load_data(filename):
    data = []
    scale = 1
    with open(filename, newline='') as csvfile:
        first = True
        for row in csv.DictReader(csvfile):
            if not first:
                data.append((float(row['x'])/scale,float(row['y'])/scale,float(row['z'])/scale))
            first = False
    return data


def build_graph(data, rang_sat):
    adj_list = [[] for _ in range(len(data)+1)]
    for i in range(len(data)):
        for j in range(i+1, len(data)):
            dist = sqrt(
                (data[i][0] - data[j][0])**2
                + (data[i][1] - data[j][1])**2
                + (data[i][2] - data[j][2])**2
                )
           
            if dist <= rang_sat:
                adj_list[i].append(j)
                adj_list[j].append(i)
    return adj_list


def degrees(graph):
    return [len(adj) for adj in graph]
    
    
def average_degree(graph):
    return statistics.mean(degrees(graph))

def clustering_distribution_coefficient(graph):
    n=len(graph)
    adj = np.zeros((n,n))
    for i in range(n):
        for j in graph[i]:           
            adj[i][j] = 1
            adj[j][i] = 1
    
    d = degrees(graph)
    distinct_neighbors = np.sum([math.comb(d[i],2) for i in range(n)]) / 2
    

    A = np.linalg.matrix_power(adj, 3)
    
    triangles=0
    for i in range(n):
        triangles+= A[i][i]
    
    return 3 * triangles / distinct_neighbors

    
def local_clustering_distribution_coefficient(graph, node):
    n=len(graph)
    adj = np.zeros((n,n))
    for i in range(n):
        for j in graph[i]:           
            adj[i][j] = 1
            adj[j][i] = 1
    
    distinct_neighbors = np.sum(np.sum(adj)) / 2

    A = np.linalg.matrix_power(adj, 3)
    if len(graph[node]) > 1:
        return A[node][node] / math.comb(len(graph[node]), 2)
    else:
        return 0
    
    
def list_local_clustering_coeffs(graph):
    return [local_clustering_distribution_coefficient(graph, u) for u in range(len(graph))]

def aux_connex_components(graph, u, visited):
    stack = [u]
    while stack:
        node = stack.pop()
        if node not in visited:
            visited.add(node)
            for neighbor in graph[node]:
                if neighbor not in visited:
                    stack.append(neighbor)
    return visited

def connex_components(graph):
    n = len(graph)
    to_visit = set(range(n))
    print(to_visit)
    components = []
    
    while to_visit:
        u = to_visit.pop()
        visited = aux_connex_components(graph, u, set())  
        components.append(list(visited)) 
        to_visit -= visited  
    
    return components


def matches_clique(graph, value, visited):
    for v in visited:
        if value not in graph[v]:
            return False
    return True

def aux_cliques(graph, u, visited):
    stack = [u]
    while len(stack)>0:
        node = stack.pop()
        if node not in visited:
            visited.add(node)
            for neighbor in graph[node]:
                if neighbor not in visited and matches_clique(graph, neighbor, visited):
                    stack.append(neighbor)
    return visited

def cliques(graph):
    n = len(graph)
    to_visit = set(range(n))
    cliques = []

    while to_visit:
        u = to_visit.pop()
        visited = aux_cliques(graph, u, set())  
        cliques.append(list(visited)) 
        to_visit -= visited  
    print(cliques)
    return cliques