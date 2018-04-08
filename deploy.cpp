#include <iostream>
#include <cstring>
#include <cstdlib>
#include <cstdio>
#include <climits>
#include <algorithm>
#include <ctime>
#include <string>
#include <queue>
#include <deque>
#include <cmath>
//#include <windows.h>
#include "deploy.h"

#define MaxV 4500
#define MaxE 3500
#define MaxC 400
#define MaxS 400
#define MaxP 3000
#define Max_Cost 50
#define MAX_LINE_LEN 40

#define INF 500000.0

//模拟退火算法中使用到的参数
#define T     3000    //初始温度值
#define Eps   1e-8    //终止温度值
#define Decay 0.98    //温度衰减率

#define Limit 10000   //概率选择上限
#define Out_Loop 1000    //外循环次数
#define In_Loop 15000   //内循环次数

using namespace std;

//整体架构使用模拟退火算法，其中每次循环更改视频服务器的数量和位置，然后使用Ford-Fulkerson算法求出满足消费节点需求的最小费用路径
//Ford-Fulkerson算法，解决最小费用最大流问题（服务器位置已经确定，即源点位置确定）
//本程序中用到SPFA算法计算最短路径，残存网络和曾广路径的概念求最小费用最大流，具体概念参考算法导论书籍第26章和文档

struct edge_information
{
    int bandwidth_ori;    //原始链路带宽，该带宽永远不变，用于描述图的最原始连通性
    int bandwidth;        //链路带宽，随着程序的运行处于不断变化之中，用于计算曾广路径等
    int bandwidth_used;   //链路已使用带宽
    float cost;             //链路费用
    int node;
    edge_information *next;
};

struct node_information
{
    int name;
    edge_information *first;
}G[MaxV];
// G是重构的图

struct cons_node_information
{
    int connect_node;
    int demand;
}C_V[MaxC];
//C_V是消费节点数组

struct source_list
{
    int source_node;
    source_list *next;
};
//源点链表
source_list * source_first=NULL;   //源点链表头指针
source_list * best_source_first=NULL;  //保存在预优化过程中得到的最优解对应下的源点链表，在之后的模拟退火算法中，在该链表上操作
deque<int>  bad_source;            //不适合做源点的网络节点队列
deque<int>  fixed_source;          //在布置服务器之后，基本不更改的网络节点队列

struct source_send
{
    int s_name;
    int s_send;
};

priority_queue<source_send>  q_s_s;   //定义各一个源点输出流量的优先队列，每找到更优异的解，时更新一次

deque<int> Path[MaxP];

int V_Num, E_Num, C_V_Num, S_Num=0;  //顶点的数量，边的数量，消费节点的数量，其中点和边的数量指原始无向图中边的数量
int Server_Cost;            //视频服务器的费用

int pre[MaxV];     //spfa 算法下的前驱节点
float dis[MaxV];     //spfa 算法下距离源点的距离（用链路费用计算）
int flow_num=0;   //在程序运行过程中不断增加的流量
int require_num=0;
float cost_num=0.0;       //阶段最小费用（包括链路费用和服务器费用）
int path_num=0;

float best_cost_num=INF;   //存储全局最小费用（包括链路费用和服务器费用）
int No_num=0;              //标记连续无解的次数
int Yes_num=0;             //标记没有能够找到更小费用解的连续次数

int logo=0;


string Result_File;        //用于最终结果打印文件
clock_t Start_time;

char str[10];

//判断链路p,q是否存在，如果不存在，则返回空指针；如果存在，则返回指向该链路的地址
edge_information *Find_Link(int p, int q)
{
    edge_information * pNode=G[p].first;
    while( pNode!=NULL )
    {
        if(pNode->node==q)
        {
            return pNode;
        }
        pNode=pNode->next;
    }
    return NULL;
}

//构建链路p->q，返回指向该链路的地址
edge_information *Structure_Link(int p, int q)
{
    edge_information * pNode=new edge_information;
    pNode->node=q;
    pNode->bandwidth=0;
    pNode->bandwidth_ori=0;
    pNode->bandwidth_used=0;
    pNode->cost=Max_Cost;
    pNode->next=G[p].first;
    G[p].first=pNode;
    return pNode;
}

//判断节点n是不是源点
bool Is_Source_Node(int n)
{
    source_list * p;
    for(p=source_first; p!=NULL; p=p->next)
        if(p->source_node==n)
            return true;
    return false;
}

//判断是不是最优源点链表中的源点
bool Is_Best_Source_Node(int n)
{
    source_list * p;
    for(p=best_source_first; p!=NULL; p=p->next)
        if(p->source_node==n)
            return true;
    return false;
}


//判断节点n是不是在不适合布置服务器的队列中
bool Is_Bad_Source_Node(int n)
{
    int i;
    if(bad_source.empty())
        return false;
    else
    {
        for(i=0; i<bad_source.size(); i++)
            if(bad_source[i]==n)
                return true;
    }
    return false;
}

bool Is_Fixed_Source_Node(int n)
{
    int i;
    if(fixed_source.empty())
        return false;
    else
    {
        for(i=0; i<fixed_source.size(); i++)
            if(fixed_source[i]==n)
                return true;
    }
    return false;
}

//重新初始化函数，在最小费用最大流算法运行一遍之后，需要对相关的变量重新初始化，这样才能保证下一次能够正确运行（模拟退火算法中要多次运行该算法）。
void Re_Init()
{
    int i;
    edge_information * m;
    edge_information * tem;
    cost_num=0;
    flow_num=0;
    require_num=0;     //需求总和每次也要更新一下，因为在构造图函数中，构建消费节点数组时将所有消费节点的需求相加求得总需求
    for(i=0; i<=V_Num+E_Num+1; i++)
    {
        tem=G[i].first;
        while(tem!=NULL)
        {
            m=tem;
            tem=tem->next;
            delete m;
        }
    }
}

bool operator <(source_send m, source_send n)
{
    if(m.s_send<n.s_send)
        return false;
    else if(m.s_send==n.s_send)
        return m.s_name>n.s_name;
    else
        return true;
}

void Stru_Pri_Q_S()
{
    source_send tem;
    edge_information * m;
    while(!q_s_s.empty())
        q_s_s.pop();
    for(m=G[V_Num+E_Num].first; m!=NULL; m=m->next)
    {
        tem.s_name=m->node;
        tem.s_send=m->bandwidth_used;
        q_s_s.push(tem);
    }
}

char * Division_String(char *first)
{
    int i=0;
    memset(str,0,10);
    while(first[i]!=' ' && first[i]!='\n')
    {
        str[i]=first[i];
        i++;
    }
    return first+i+1;
}

void Stru_G(char * topo[MAX_EDGE_NUM])
{
    //freopen("out.txt", "w", stdout);
    int i=0,j=0,m=0;
    int E_start, E_end, band;
    float co;
    int cid, conn, dam;
    edge_information *f;    //重新构建图时使用
    source_list * s;
    char *p;
    char *hel;
    //line_num = read_file(topo, MaxE, "C:\\Users\\jd\\Desktop\\流量规划\\多源多汇问题转换成单源单汇问题\\多源多汇转单源单汇问题\\3\\case1.txt");
    hel=Division_String(topo[0]);
    p=str;
    V_Num=atof(p);
    hel=Division_String(hel);
    p=str;
    E_Num=atof(p);
    hel=Division_String(hel);
    p=str;
    C_V_Num=atof(p);
    Server_Cost=atof(topo[2]);
    for(i=0; i<=V_Num+E_Num+1;i++)
    {
        G[i].name=i;
        G[i].first=NULL;
    }
    m=V_Num;
    for(i=4; i<=E_Num+3; i++)    //一共有条弧 每条弧包括边起始节点信息、边结束节点信息，边的权重和链路上单位带宽的费用
    {
        hel=Division_String(topo[i]);
        p=str;
        E_start=atof(p);
        hel=Division_String(hel);
        p=str;
        E_end=atof(p);
        hel=Division_String(hel);
        p=str;
        band=atof(p);
        hel=Division_String(hel);
        p=str;
        co=atof(p);

        f=new edge_information;
        f->node=E_end;
        f->bandwidth=band;
        f->bandwidth_ori=band;
        f->bandwidth_used=0;
        f->cost=co;
        f->next=G[E_start].first;
        G[E_start].first=f;

        f=new edge_information;
        f->node=m;
        f->bandwidth=band;
        f->bandwidth_ori=band;
        f->bandwidth_used=0;
        f->cost=co/2;
        f->next=G[E_end].first;
        G[E_end].first=f;

        f=new edge_information;
        f->node=E_start;
        f->bandwidth=band;
        f->bandwidth_ori=band;
        f->bandwidth_used=0;
        f->cost=co/2;
        f->next=G[m].first;
        G[m].first=f;

        m++;
        //delete [] topo[i];
    }
    //构建消费节点链表
    for(j=i+1; j<=i+C_V_Num; j++)
    {
        hel=Division_String(topo[j]);
        p=str;
        cid=atof(p);
        hel=Division_String(hel);
        p=str;
        conn=atof(p);
        hel=Division_String(hel);
        p=str; 
        dam=atof(p);

        C_V[cid].connect_node=conn;
        C_V[cid].demand=dam;
    }
    //构建超级汇点，为V_Num+E_Num+2
    for(i=0; i<C_V_Num; i++)
    {
        f=new edge_information;
        f->node=V_Num+E_Num+1;
        f->bandwidth=C_V[i].demand;
        f->bandwidth_ori=C_V[i].demand;
        f->bandwidth_used=0;
        f->cost=0.0;
        f->next=G[ C_V[i].connect_node ].first;
        G[ C_V[i].connect_node ].first=f;
        require_num=require_num+C_V[i].demand;
    }
}

void Select_Source()
{
    int i,n;
    int tem[4];
    int hyl;
    int select=0;
    double ran=0.0;
    int cnt=0;
    source_list * s;        //构建源点链表时使用
    source_list * p_s;
    edge_information * p;
    edge_information * m;
    if(Yes_num>=800)                    //如果连续多次都没有找到更优异的解，那尝试减少一个源点继续寻找，否则更换源点的位置（源点的数量不变）继续寻找
    {
        if(S_Num==1)
        {
            logo=1;
            return;
        }
        S_Num=S_Num-1;
        Yes_num=0;
        hyl=q_s_s.top().s_name;
        while(Is_Fixed_Source_Node(hyl))
        {
            q_s_s.pop();
            if(!q_s_s.empty())
                hyl=q_s_s.top().s_name;
            else
                break;
        }
        bad_source.push_back(hyl);
        p_s=best_source_first;
        for(s=best_source_first; s!=NULL; s=s->next)
        {
            if(s->source_node==hyl)
            {
                if(s==best_source_first)
                {
                    best_source_first=s->next;
                    delete s;
                }
                else
                {
                    p_s->next=s->next;
                    delete s;
                }
            }
            p_s=s;
        }
    }
    else
    {
        if(C_V_Num<100)
        {
            tem[0]=q_s_s.top().s_name;
            while(Is_Fixed_Source_Node(tem[0]))
            {
                q_s_s.pop();
                if(!q_s_s.empty())
                    tem[0]=q_s_s.top().s_name;
                else
                    break;
            }
            for(s=best_source_first; s!=NULL; s=s->next)
            {
                 ran=(double)rand()/(RAND_MAX+1.0);
                 select=V_Num*ran;
                 while(Is_Bad_Source_Node(select) ||  Is_Best_Source_Node(select)  )
                 {
                     ran=(double)rand()/(RAND_MAX+1.0);
                     select=V_Num*ran;
                 }
                 s->source_node=select;
                 break;
            }
        }
        else
        {
            for(i=0; i<2; i++)
            {
                tem[i]=q_s_s.top().s_name;
                while(Is_Fixed_Source_Node(tem[i]))
                {
                    q_s_s.pop();
                    if(!q_s_s.empty())
                        tem[i]=q_s_s.top().s_name;
                    else
                        break;
                }
                q_s_s.pop();
            }
            for(s=best_source_first; s!=NULL; s=s->next)
            {
                if(s->source_node==tem[0]  ||  s->source_node==tem[1] )
                {
                    n=G[s->source_node].first->node;
                    for(m=G[n].first; m!=NULL; m=m->next)
                    {
                        if(  (!Is_Bad_Source_Node(m->node)) &&  (!Is_Best_Source_Node(m->node)) &&  m->node!=tem[0] && m->node!=tem[1]  &&  m->node<V_Num)
                        {
                            s->source_node=m->node;
                        }
                    }
                }
            }
        }
    }
    //源点选定之后，构建超级源点V_Num+E_Num，它与选取的源点各连接一条链路，其中带宽无穷大，费用为0
    for(s=best_source_first; s!=NULL; s=s->next)
    {
        p=new edge_information;
        p->node=s->source_node;
        p->bandwidth=INF;
        p->bandwidth_ori=INF;
        p->bandwidth_used=0;
        p->cost=0.0;
        p->next=G[V_Num+E_Num].first;
        G[V_Num+E_Num].first=p;
    }
}

bool Is_Ring( int m, int n)
{
    int i;
    for(i=pre[m]; i!=-1; i=pre[i])
    {
        if(i==n)
            return true;
    }
    return false;
}

//计算源点为s的单源最短路径spfa算法
void spfa(int s)
{
    queue<int> Q;
    int u;
    edge_information *tem;
    bool visit[MaxV];        //标记节点是否已经被访问
    for(int i=0; i<=V_Num+E_Num+1; i++)//初始化
    {
        dis[i]=INF;
        pre[i]=-1;
        visit[i]=false;
    }
    dis[s]=0.0;
    Q.push(s);
    visit[s] = true;
    while(!Q.empty())
    {
        u=Q.front();
        Q.pop();
        visit[u]=false;
        for(tem=G[u].first; tem!=NULL; tem=tem->next)//更新u的邻接点的dist[], pre[], inq[]
        {
            int v=tem->node;
            if(tem->bandwidth==0)    //曾经有边，但是现在没有
                continue;
            if(dis[v]>dis[u]+tem->cost)//松弛操作
            {
                dis[v]=dis[u]+tem->cost;
                    pre[v]=u;
                if(visit[v]==false)
                {
                    Q.push(v);
                    visit[v]=true;
                }
            }
        }
    }
}

void min_cost_max_flow()
{
    int i;
    int flow=100;
    edge_information * tem;
    edge_information * hel;

    spfa(V_Num+E_Num);

    cost_num=cost_num+S_Num*Server_Cost;
    while( pre[V_Num+E_Num+1]!=-1 )
    {
        for(i=V_Num+E_Num+1; i!=V_Num+E_Num; i=pre[i])    //找到一条源点到汇点的最小费用路径之后，判断该条路径能溜过来的流量（路径上容量最小的链路）
        {
            tem=Find_Link(pre[i],i);
            if( (tem->bandwidth) < flow )
                flow=tem->bandwidth;
        }
        flow_num=flow_num+flow;
        if(flow_num<require_num)
        {
            for(i=V_Num+E_Num+1; i!=V_Num+E_Num; i=pre[i])
            {
                tem=Find_Link(pre[i],i);
                tem->bandwidth=tem->bandwidth-flow;
                tem=Find_Link(i,pre[i]);
                if(tem==NULL)
                    tem=Structure_Link(i,pre[i]);
                tem->bandwidth=tem->bandwidth+flow;
                hel=Find_Link(pre[i],i);
                //if(G[i][pre[i]].cost==Max_Cost)
                    tem->cost=-hel->cost;
                tem=Find_Link(pre[i],i);
                if(tem->bandwidth_ori>0)
                    tem->bandwidth_used=tem->bandwidth_used+flow;
                if(tem->bandwidth_ori==0)
                {
                    tem=Find_Link(i,pre[i]);
                    tem->bandwidth_used=tem->bandwidth_used-flow;
                }
            }
            cost_num=cost_num+flow*dis[V_Num+E_Num+1];
            spfa(V_Num+E_Num);
        }
        else
        {
            int surplus=flow_num-require_num;
            flow_num=flow_num-surplus;
            flow=flow-surplus;
            for(i=V_Num+E_Num+1; i!=V_Num+E_Num; i=pre[i])
            {
                tem=Find_Link(pre[i],i);
                tem->bandwidth=tem->bandwidth-flow;
                tem=Find_Link(i,pre[i]);
                if(tem==NULL)
                    tem=Structure_Link(i,pre[i]);
                tem->bandwidth=tem->bandwidth+flow;
                hel=Find_Link(pre[i],i);
                //if(G[i][pre[i]].cost==Max_Cost)
                    tem->cost=-hel->cost;
                tem=Find_Link(pre[i],i);
                if(tem->bandwidth_ori>0)
                    tem->bandwidth_used=tem->bandwidth_used+flow;
                if(tem->bandwidth_ori==0)
                {
                    tem=Find_Link(i,pre[i]);
                    tem->bandwidth_used=tem->bandwidth_used-flow;
                }
            }
            cost_num=cost_num+flow*dis[V_Num+E_Num+1];
            return;
        }
        flow=INF;
    }
}

//根据图中链路的bandwidth_used元素构建路径数组
void Str_Path(int source)
{
    int  i,j,n,tep,flow_path=0;
    int p=INF;
    edge_information * m;
    edge_information * hel;
    int tem[MaxV];
    while(flow_path!=flow_num)
    {
        i=0;
        memset(tem, -1, MaxV*sizeof(int));
        Path[path_num].push_back(source);
        tem[i]=source;
        i++;
        n=Path[path_num].back();
        tep=n;
        m=G[n].first;
        while(m!=NULL)
        {
            if(m->bandwidth_used>0)
            {
                Path[path_num].push_back(m->node);
                tem[i]=m->node;
                i++;
            }
            n=Path[path_num].back();
            if(tep!=n)
                m=G[n].first;
            else
                m=m->next;
            tep=n;
        }
        if(Path[path_num].back()==V_Num+E_Num+1)
        {
            for(j=0; tem[j+1]!=-1; j++)
            {
                hel=Find_Link(tem[j],tem[j+1]);
                if(hel->bandwidth_used<p)
                    p=hel->bandwidth_used;
            }

            Path[path_num].push_back(p);
            for(j=0; tem[j+1]!=-1; j++)
            {
                hel=Find_Link(tem[j],tem[j+1]);
                hel->bandwidth_used=hel->bandwidth_used-p;
            }
            flow_path=flow_path+p;
            path_num++;
        }
        p=INF;
    }
}

void Pre_Optimization(char * topo[MAX_EDGE_NUM])
{
    int i,j;
    int tem[4];
    int logo_cnt=0;
    int help=0;
    source_list * p;
    source_list * pre;
    source_list * b_p;
    source_list * b_pre;
    edge_information * m;
    Stru_G(topo);
    if(S_Num==0)
        S_Num=C_V_Num;
    for(i=0; i<C_V_Num; i=i+1)
    {
        p= new source_list;
        p->source_node=C_V[i].connect_node;
        p->next=source_first;
        source_first=p;
    }
    //源点选定之后，构建超级源点V_Num+E_Num，它与选取的源点各连接一条链路，其中带宽无穷大，费用为0
    for(p=source_first; p!=NULL; p=p->next)
    {
        m=new edge_information;
        m->node=p->source_node;
        m->bandwidth=INF;
        m->bandwidth_ori=INF;
        m->bandwidth_used=0;
        m->cost=0.0;
        m->next=G[V_Num+E_Num].first;
        G[V_Num+E_Num].first=m;
    }
    min_cost_max_flow();
    while( 1   )
    {
	if(cost_num>best_cost_num)
            logo_cnt++;
        if(logo_cnt>=14)
            break;
	
	if(flow_num<require_num)
        {
            for(i=0; i<C_V_Num; i++)
            {
                m=Find_Link(C_V[i].connect_node, V_Num+E_Num+1);
                if(m->bandwidth_used<C_V[i].demand)
                {
                    S_Num++;
                    p=new source_list;
                    p->source_node=C_V[i].connect_node;
                    p->next=source_first;
                    source_first=p;
                    fixed_source.push_back(C_V[i].connect_node);
                }
            }
        }

        //best_cost_num=cost_num;
        Stru_Pri_Q_S();

        tem[0]=q_s_s.top().s_name;
        while(Is_Fixed_Source_Node(tem[0]))
        {
            q_s_s.pop();
            if(!q_s_s.empty())
                tem[0]=q_s_s.top().s_name;
            else
                break;
        }
        if(q_s_s.empty())          //该处有改动
            break;

	bad_source.push_back(tem[0]);
        
	S_Num=S_Num-1;
	pre=source_first;
        for(p=source_first; p!=NULL; p=p->next)
        {
            if(p->source_node==tem[0])
            {
                if(p==source_first)
                {
                    source_first=p->next;
                    delete p;
                }
                else
                {
                    pre->next=p->next;
                    delete p;
                }
            }
            pre=p;
        }

	if(flow_num>=require_num  &&  cost_num<best_cost_num   )
        {
	    
	    //构建最优解情况下的源点链表
            if(help!=0)
                help=0;
            if(best_source_first!=NULL)
            {
                b_p=best_source_first;
                while(b_p!=NULL)
                {
                    b_pre=b_p;
                    b_p=b_p->next;
                    delete b_pre;
                }
                best_source_first=NULL;
            }
            for(m=G[V_Num+E_Num].first; m!=NULL; m=m->next)
            {
                help=help+1;
                b_p=new source_list;
                b_p->source_node=m->node;
                b_p->next=best_source_first;
                best_source_first=b_p;
            }


	    best_cost_num=cost_num;
            for(j=0; j<path_num; j++)
                Path[j].clear();
            path_num=0;
            Str_Path(V_Num+E_Num);
        }  

        Re_Init();
        Stru_G(topo);
        for(p=source_first; p!=NULL; p=p->next)
        {
            m=new edge_information;
            m->node=p->source_node;
            m->bandwidth=INF;
            m->bandwidth_ori=INF;
            m->bandwidth_used=0;
            m->cost=0.0;
            m->next=G[V_Num+E_Num].first;
            G[V_Num+E_Num].first=m;
        }
        min_cost_max_flow();
    }
    //预优化运行完之后，重新初始化，释放中间的源点链表，在以后的退火算法中不在使用，使用best_source_list链表
    S_Num=help;         //预优化之后的源点数量
    Re_Init();
    p=source_first;
    while(p!=NULL)
    {
        pre=p;
        p=p->next;
        delete pre;
    }
    source_first=NULL;

}

//模拟退火算法
void S_A( char * topo[MAX_EDGE_NUM]  )
{
    int i,j;
    double t,time;
    float cur_cost_num=best_cost_num;
    float dE;
    double e,rad;
    int In=0, Out=0;
    clock_t curten_time;
    while(1)
    {
        for(i=0; i<In_Loop; i++)
        {
            curten_time=clock();
            time=(double)(curten_time-Start_time)/CLOCKS_PER_SEC;
            if(time>88)
            {
                return;
            }
            Stru_G(topo);
	        if(C_V_Num>100)
		        return;
            Select_Source();
            if(logo==1)
                return;
            min_cost_max_flow();
            //cout<<"j"<<endl;
            //cout<<flow_num<<" ";
            //cout<<cost_num<<" ";
            if(flow_num<require_num)
            {
                dE=INF-cur_cost_num;
                e=exp(-dE/t);
                rad=(double)rand()/(RAND_MAX+1.0);
                if(rad<e && e<1)
                {
                    cur_cost_num=INF;
                }
                //cout<<"fjg"<<" ";
                In++;
                Stru_Pri_Q_S();
                Yes_num++;;
            }
            else if(cost_num<cur_cost_num)
            {
                cur_cost_num=cost_num;
                Stru_Pri_Q_S();
                if(cur_cost_num<best_cost_num)
                {
                    best_cost_num=cur_cost_num;
                    for(j=0; j<path_num; j++)
                        Path[j].clear();
                    path_num=0;
                    Str_Path(V_Num+E_Num);
                }
                Yes_num=0;
                In=0;
                Out=0;
            }
            else
            {
                dE=cost_num-cur_cost_num;
                e=exp(-dE/t);
                rad=(double)rand()/(RAND_MAX+1.0);
                Stru_Pri_Q_S();
                if(rad<e && e<1)
                {
                    cur_cost_num=cost_num;
                    if(cur_cost_num<best_cost_num)
                    {
                        best_cost_num=cur_cost_num;
                        for(j=0; j<path_num; j++)
                            Path[j].clear();
                        path_num=0;
                        Str_Path(V_Num+E_Num);
                    }
                }
                In++;
                Yes_num++;
            }
            //cout<<endl;
            //cout<<Yes_num<<" ";
            //cout<<S_Num<<" ";
            //cout<<cur_cost_num<<endl;
            Re_Init();
            if(In>Limit)
            {
                Out++;
                break;
            }
        }
        if(Out>=Out_Loop || t<Eps)
            break;
        t=t*Decay;
    }
    return;
}


void path_printf()
{
    int i,j,n;
    char tem[20];
    memset(tem, 0, 20);
    sprintf(tem,"%d", path_num);
    Result_File=Result_File+tem+"\n\n";
    memset(tem, 0, 20);
    for(i=0; i<path_num; i++)
    {
        Path[i].pop_front();
        while(Path[i].size()>3)
        {
            n=Path[i].front();
            if(n<V_Num)
            {
                sprintf(tem,"%d", n);
                Result_File=Result_File+tem+" ";
                memset(tem, 0, 20);
            }
            Path[i].pop_front();
        }
        n=Path[i].front();
        sprintf(tem,"%d", n);
        Result_File=Result_File+tem+" ";
        memset(tem, 0, 20);
        Path[i].pop_front();
        for(j=0; j<C_V_Num; j++)
            if(C_V[j].connect_node==n)
                break;
        sprintf(tem,"%d", j);
        Result_File=Result_File+tem+" ";
        memset(tem, 0, 20);
        Path[i].pop_front();
        n=Path[i].front();
        sprintf(tem,"%d", n);
        Result_File=Result_File+tem+" ";
        memset(tem, 0, 20);
        Path[i].pop_front();
        Result_File=Result_File+"\n";
    }
}

//你要完成的功能总入口
void deploy_server(char * topo[MAX_EDGE_NUM], int line_num, char * filename)
{
    Start_time=clock();
    Pre_Optimization(topo);
    S_A(topo);
    //Stru_G();
    //Select_Source();
    //min_cost_max_flow();
    //cout<<endl;
    //if(flow_num<require_num)
    if(path_num==0)
        cout<<"No"<<endl;
    else
    {
        //Str_Path(V_Num+E_Num);
        path_printf();
        //cout<<Result_File;
    }
    //cout<<cost_num<<endl;
    cout<<S_Num<<endl;
    cout<<best_cost_num<<endl;
	// 需要输出的内容
	const char * topo_file=Result_File.data();

	// 直接调用输出文件的方法输出到指定文件中(ps请注意格式的正确性，如果有解，第一行只有一个数据；第二行为空；第三行开始才是具体的数据，数据之间用一个空格分隔开)
	write_result(topo_file, filename);

}
