### 2017华为软件精英挑战赛

##题目大意

有一个无向网络，网路的每条路径有一个带宽容量限制和单位带宽的花费，网路中有一些消费节点，每个消费节点有一个容量需求，现在让你在网络中布置一些服务器给消费节点提供带宽，每个服务器有固定的费用，让你设计一种服务器的布置方案使得费用尽量少并输出服务器给消费节点提供带宽的路径
##赛题分析

这道题是一道NP-hard问题，可以归为优化选址一类的问题中去。

对于确定服务器的位置这道题就是一个经典的多源多汇费用流问题了，关于于多源多汇的费用流问题可以参考：[POJ 2516 Minimum Cost(费用流 建图)][1] 
 
这里简单说一下思路：建立一个超级源点(不是图中的点，自己虚拟的)连接到所有的服务器，再建一个超级汇点连接到所有消费节点，这样就变成了一个单源点单汇点的费用流问题，而费用流的求解可以用SPFA、dinic算法、单纯性算法等，但是做为一个经典的算法，我认为SPFA就差不多足够了(其实是比较懒只会这一个算法)。

由于题目要求还要输出路径，所以在费用流求完之后需要再进行一次深广搜找路径。

而对于这道题主要就是服务器位置的确定了。主流的解决思路有遗传算法、模拟退火、粒子群等。

模拟退火类似于爬山，大体思路是选取一个初始状态，从这个状态开始走，每次去找一个临近地状态，如果比当前的解好就走它，比当前的差有一定的概率会走它，在模拟退火里面这个概率是用温度作为一个影响因子来表示的，温度越小，走差解的可能性越小。随着迭代次数温度逐渐降低最终收敛到一个局部最优值。
而遗传算法则是随机选一些状态作为初始的个体构成一个群体，每一次迭代都将这个群体中解较优的个体进行叫交叉互换和变异之后形成新的解。但是使用遗传算法需要我们认同一个假设:两个较优解通过交叉互换变异之后也得到较优解的可能性是比较大的。
粒子群可以看成是让一群粒子在整个搜索空间搜索，这样可以比较好的避免陷入局部最优，但同时由于粒子数很多使得迭代一次所花费的时间也相对较多。

以上几个算法本质上都是启发式搜索，目的都是高效地找到较优的解，各有各的好处，效果还是要具体实验之后才能知道

[1]: https://blog.csdn.net/mmy1996/article/details/56280326  "POJ 2516 Minimum Cost(费用流 建图)"

