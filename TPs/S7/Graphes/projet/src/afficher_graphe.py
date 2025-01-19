import sys
import matplotlib.pyplot as plt
import numpy as np
from mpl_toolkits.mplot3d import Axes3D 
import utils


def connectpoints(x,y,z,p1,p2):
    x1, x2 = x[p1], x[p2]
    y1, y2 = y[p1], y[p2]
    z1, z2 = z[p1], z[p2]
    plt.plot([x1,x2],[y1,y2],[z1,z2],'red',linewidth=0.2)


def set_axes_equal(ax):
    x_limits = ax.get_xlim3d()
    y_limits = ax.get_ylim3d()
    z_limits = ax.get_zlim3d()

    x_range = abs(x_limits[1] - x_limits[0])
    x_middle = np.mean(x_limits)
    y_range = abs(y_limits[1] - y_limits[0])
    y_middle = np.mean(y_limits)
    z_range = abs(z_limits[1] - z_limits[0])
    z_middle = np.mean(z_limits)

    plot_radius = 0.5*max([x_range, y_range, z_range])

    ax.set_xlim3d([x_middle - plot_radius, x_middle + plot_radius])
    ax.set_ylim3d([y_middle - plot_radius, y_middle + plot_radius])
    ax.set_zlim3d([z_middle - plot_radius, z_middle + plot_radius])


def plot_graph(data, ranges):
    x, y, z = [], [], []
    for i in range(len(data)):
        x.append(data[i][0])
        y.append(data[i][1])
        z.append(data[i][2])

 
    
    fig = plt.figure(figsize=plt.figaspect(1/len(ranges)))
    for index in range(len(ranges)):
        ax = fig.add_subplot(1, len(ranges), index+1, projection='3d')
        graph = utils.build_graph(data, ranges[index])
        ax.scatter(x, y, z)
        for i in range(len(graph)):
            for j in graph[i]:
                connectpoints(x,y,z,i,j)
            

        set_axes_equal(ax)
    plt.show()

   
   

def main():
    data = utils.load_data(sys.argv[1])
    plot_graph(data, [20_000, 40_000, 60_000])
    
    return 0

if __name__ == "__main__":
    main()

  