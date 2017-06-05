#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<cstring>
#include<malloc.h>
#include<algorithm>
#include<vector>
#include<math.h>
#include<set>
#include<stack>
#include<time.h>
// in linux it's #include<sys/times.h>

using namespace std;

const int machineMap[5][16] = {{0}, {0}, {2, 0, 1, 3}, {4, 1, 2, 5, 8, 7, 6, 3, 0}, {9, 5, 6, 10, 14, 13, 12, 8, 4, 0, 1, 2, 3, 7, 11, 15}};

const double eps_0 = 1.0e-6;
const int MAXN = 270;
const int MAXM = 270;
int m;
int n;
const int inf = 0x3f3f3f3f;
const int cycle=1;//周期数
//const double Rdk=0.4;//处理器工作消耗
//const double Rsk=150;//处理器睡眠消耗0.15
//const double Rik=160;//处理器空闲消耗0.16
const double Rb_dis=1;//线路能耗
const double Rb_node=4;//节点能耗
const double cominitcost=2;
const double t0=200.0;//时间阈值
const double t_penalty=25;//时间惩罚
const double extra_E=1;//能耗惩罚
const int meshfactor=2;//2*2
const double t_dis=7.0;//线路传输速度
const double t_node=8.0;//节点传输速度
const double xi= 8.0;//冲突间隔
const double xita=1.0;//xita-dominance
int mycycle;

double com_sum=0;
double pp[MAXN][MAXN]={0};
double Rdk[meshfactor*meshfactor]= {0}; //处理器工作能耗
double Rik[meshfactor*meshfactor]= {0}; //处理器工作能耗
int gamma[meshfactor*meshfactor][meshfactor*meshfactor][meshfactor*meshfactor][meshfactor*meshfactor]= {0};
double pc[meshfactor*meshfactor][meshfactor*meshfactor][meshfactor*meshfactor][meshfactor*meshfactor]= {0}; //冲突概率
clock_t start, finish;
//in linux it's tms start finish
double start_time;
double real_time;
double exe_time;
//*******
//**pop - Population size
//**gen - Total number of generations
int pop, gen;
int isdep[cycle][MAXN];//被i依赖的个数
int todep[cycle][MAXN];//i依赖的任务数
int taskIndex[MAXN];// 记录每个机器所匹配到的位置
bool taskUsed[MAXN];
int mesh[meshfactor*meshfactor]= {0}; //3*3 2D mesh
int D[meshfactor*meshfactor][meshfactor*meshfactor];

set<int> doneSet;

double time_limit;

/****************************************
目标函数   Minimize communication cost
目标函数   Minimize the balance of processor workload
目标函数   Minimize the Energy
t(m,n)     Execution time of a task on a processor
c(m,n)     Communication cost between two tasks
****************************************/


double t[MAXM][MAXN];
struct time_table
{
    double time;
    int id;
} time_in_machine[MAXN];

double c[MAXN][MAXN];
bool uesd[MAXN];

vector< vector<int> > machines;
vector<int> _machines;

struct Individual
{
    vector<int> machine[MAXM]; //save permutation of the tasks
    double p_contention; //object 1
    double makespan; //object 2
    double energy;  //object 3
    double Ed;
    double Ei;
    double Es;
    double comtime;
    double idltime;
    double sleeptime;
    int front; //rank of domination
    vector< int > S; //the collections dominated by this Individual
    int n;// count of dominated solution
    double dfitness; //fitness
    double crowd_distance;

    int mesh[meshfactor*meshfactor];
} Collection[MAXN], new_individual;

vector<Individual> Front[MAXN];
vector<Individual> ElistCollection;
//升序
int cmp(const void *a, const void *b)
{
    return (*(Individual *)a).p_contention > (*(Individual *)b).p_contention ? 1:-1;
}
//升序
int cmp1(const void *a, const void *b)
{
    return (*(Individual *)a).makespan > (*(Individual *)b).makespan ? 1:-1;
}
int cmp0(const void *a, const void *b)
{
    return (*(Individual *)a).energy > (*(Individual *)b).energy ? 1:-1;
}
//降序
int cmp2(const void *a, const void *b)
{
    return (*(Individual *)a).crowd_distance > (*(Individual *)b).crowd_distance ? -1:1;
}
//降序
int cmp3(const void *a, const void *b)
{
    return (*(time_table *)a).time > (*(time_table *)b).time ? -1 : 1;
}
//个体替换
void copy_individual(Individual *i, Individual *j)
{
    vector<int>:: iterator iter;
    for(int ii = 0 ; ii < m ; ii ++)
    {
        i->machine[ii].erase(i->machine[ii].begin(), i->machine[ii].end());
//    }
//    for(int ii = 0 ; ii < m ; ii ++)
//    {
        for(iter = j->machine[ii].begin(); iter != j->machine[ii].end(); ++ iter)
        {
            i->machine[ii].push_back((*iter));
        }
    }
}

double abs(double t)
{
    return t>0?t:-t;
}

void evaluate_objective(Individual *i)
{
    //printf("here");
    for(int ii = 0; ii < meshfactor*meshfactor; ii ++)
    {
        if(i->machine[ii].size() != 0)
        {
            i->mesh[ii] = 1;
        }
        else
        {
            i->mesh[ii] = 0;
        }
    }

    vector<int>:: iterator iter;
    vector<int>:: iterator jter;

    i->n = inf;
    i->makespan = 0;
    i->p_contention = 0;
    i->energy=0;
    i->Ed=0;
    i->Ei=0;
    i->Es=0;
    i->comtime=0;
    i->idltime=0;
    i->sleeptime=0;

    double depcopy[cycle][MAXN][MAXN];
    double Ed=0,Eis=0,Eb=0,Ei=0,Es=0;
    double comtime=0,idltime=0,sleeptime=0;
    com_sum=0.0;

    int isdepcopy[cycle][MAXN],todepcopy[cycle][MAXN];
    double path[meshfactor*meshfactor][meshfactor*meshfactor][2];

    for(int ii=0; ii<meshfactor*meshfactor; ii++)
    {
        for(int jj=0; jj<meshfactor*meshfactor; jj++)
        {
            path[ii][jj][0]=0.0;//路径占用起始时间
            path[ii][jj][1]=0.0;//路径占用完成时间
        }
    }

    for(int k=0; k<mycycle; k++)
    {
        for(int ii=0; ii<n; ii++)
        {
            isdepcopy[k][ii]=isdep[k][ii];
            todepcopy[k][ii]=todep[k][ii];
            for(int j=0; j<n; j++)
            {
                depcopy[k][ii][j]=c[ii][j];
            }
        }
    }
    double load[MAXM];
    memset(load, 0, sizeof(load));
    int jud_index[MAXM],flag_end[MAXM],flag_com[MAXM],position;
    memset(jud_index,0,sizeof(jud_index));
    memset(flag_end,0,sizeof(flag_end));
    //memset(pp,0,sizeof(pp));
    double E[MAXM];
    memset(E,0,sizeof(E));
    double tao[cycle][MAXN];
    double taoend[cycle][MAXN];
    double Lstart,ltemp;
    double idletime=0;
    int source_path,destination_path;
    int x_temp=0,y_temp=0;
    int it=1,task_in_machine[MAXN],flag;
    double avg = 0,workload=0;
//    for(int j = 0 ; j < n ; j ++)
//    {
//        avg += t[0][j];
//    }
//    i->comtime=avg*mycycle;
//    avg /= m;
//    for(int ii = 0; ii < m; ii ++) {
//        printf("%d ", i->mesh[ii]);
//    }
//    printf("\n");

for(int ii=0;ii<n;ii++){
	for(int jj=0;jj<n;jj++){
		pp[ii][jj]=0;
	}
}

    for(int j = 0 ; j < meshfactor*meshfactor ; j ++)
    {
        if(i->mesh[j]==1)
        {
            for(iter = i->machine[j].begin(); iter != i->machine[j].end(); ++ iter)
            {
                task_in_machine[*iter]=j;
                load[j]=load[j]+t[j][(*iter)];

            }
//        workload+= abs(load[j]-avg);
            i->comtime=i->comtime+load[j]*mycycle;
            Ed+=load[j]*Rdk[j]*mycycle;//处理器花费的一部分
            flag_com[j]=0;
        }
    }
    //i->workload=workload;

    while(it<=n*mycycle)
    {

        for(int ii=0; ii<meshfactor*meshfactor; ii++)
        {
            //printf("ii = %d\n", ii);
            if(i->mesh[ii]==1)
            {
                flag_com[ii]=0;
                if(flag_end[ii]==mycycle||i->machine[ii].empty())   //printf("continue\n");
                {
                    continue;
                }
                position=i->machine[ii].at(jud_index[ii]);
                if(isdepcopy[flag_end[ii]][position]==0)
                {

                    Lstart=E[ii];
                    for(int kk=0; kk<n; kk++)
                    {
                        //需要通信
                        //printf("kk = %d\n", kk);
                        if((c[kk][position]>0)&&(task_in_machine[kk]!=task_in_machine[position]))
                        {
                            flag_com[ii]=1;
                            Eb+=c[kk][position]*(D[task_in_machine[kk]][task_in_machine[position]]*Rb_dis)+(D[task_in_machine[kk]][task_in_machine[position]]+1)*Rb_node;
//                        ltemp=taoend[flag_end[ii]][kk]+c[kk][position]*(D[task_in_machine[kk]][task_in_machine[position]]*t_dis+(D[task_in_machine[kk]][task_in_machine[position]]+1)*t_node)+2;
                            ltemp=taoend[flag_end[ii]][kk];

                            //考虑通信阻塞

                            source_path=task_in_machine[kk];
                            destination_path=task_in_machine[position];
                            x_temp=abs(task_in_machine[kk]%meshfactor-task_in_machine[position]%meshfactor);
                            y_temp=abs(task_in_machine[kk]/meshfactor-task_in_machine[position]/meshfactor);
                            while(1) //printf("xtemp = %d ytemp=%d\n", x_temp, y_temp);
                            {
                                if(x_temp==0&&y_temp==0)
                                {
                                    ltemp+=c[kk][position]*t_node;//目标核上的路由器也有个花费
                                    break;
                                }
                                else
                                {
                                    if(x_temp==0)
                                    {
                                        //走y轴
                                        if(task_in_machine[kk]/meshfactor-task_in_machine[position]/meshfactor>0)
                                        {
                                            //向上传
                                            y_temp--;
                                            if(path[source_path][source_path-meshfactor][0]<=ltemp && ltemp<path[source_path][source_path-meshfactor][1])
                                            {
                                                ltemp+=path[source_path][source_path-meshfactor][1]+c[kk][position]*t_dis+t_node;
                                                path[source_path][source_path-meshfactor][1]=ltemp;
                                                path[source_path-meshfactor][source_path][0]=path[source_path][source_path-meshfactor][0];
                                                path[source_path-meshfactor][source_path][1]=ltemp;//一条路径被占用，反过来也是占用的
                                                source_path=source_path-meshfactor;
                                            }
                                            else
                                            {
                                                path[source_path][source_path-meshfactor][0]=ltemp;
                                                path[source_path-meshfactor][source_path][0]=ltemp;
                                                ltemp+=c[kk][position]*t_dis+t_node;
                                                path[source_path][source_path-meshfactor][1]=ltemp;
                                                path[source_path-meshfactor][source_path][1]=ltemp;
                                                source_path=source_path-meshfactor;

                                            }
                                        }
                                        else
                                        {
                                            //向下传
                                            y_temp--;
                                            if(path[source_path][source_path+meshfactor][0]<=ltemp && ltemp<path[source_path][source_path+meshfactor][1])
                                            {
                                                ltemp+=path[source_path][source_path+meshfactor][1]+c[kk][position]*t_dis+t_node;
                                                path[source_path][source_path+meshfactor][1]=ltemp;
                                                path[source_path+meshfactor][source_path][0]=path[source_path][source_path+meshfactor][0];
                                                path[source_path+meshfactor][source_path][1]=ltemp;//一条路径被占用，反过来也是占用的
                                                source_path=source_path+meshfactor;
                                            }
                                            else
                                            {
                                                path[source_path][source_path+meshfactor][0]=ltemp;
                                                path[source_path+meshfactor][source_path][0]=ltemp;
                                                ltemp+=c[kk][position]*t_dis+t_node;
                                                path[source_path][source_path+meshfactor][1]=ltemp;
                                                path[source_path+meshfactor][source_path][1]=ltemp;
                                                source_path=source_path+meshfactor;
                                            }
                                        }
                                    }
                                    else  //包括y_temp=0和 x,y都不为0，优先走x轴
                                    {
                                        //走x轴
                                        if(task_in_machine[kk]%meshfactor-task_in_machine[position]%meshfactor>0)
                                        {
                                            //向左传
                                            x_temp--;
                                            if(path[source_path][source_path-1][0]<=ltemp && ltemp<path[source_path][source_path-1][1])
                                            {
                                                ltemp+=path[source_path][source_path-1][1]+c[kk][position]*t_dis+t_node;
                                                path[source_path][source_path-1][1]=ltemp;
                                                path[source_path-1][source_path][0]=path[source_path][source_path-1][0];
                                                path[source_path-1][source_path][1]=ltemp;//一条路径被占用，反过来也是占用的
                                                source_path=source_path-1;
                                            }
                                            else
                                            {
                                                path[source_path][source_path-1][0]=ltemp;
                                                path[source_path-1][source_path][0]=ltemp;
                                                ltemp+=c[kk][position]*t_dis+t_node;
                                                path[source_path][source_path-1][1]=ltemp;
                                                path[source_path-1][source_path][1]=ltemp;
                                                source_path=source_path-1;
                                            }
                                        }
                                        else
                                        {
                                            //向右传
                                            x_temp--;
                                            if(path[source_path][source_path+1][0]<=ltemp && ltemp<path[source_path][source_path+1][1])
                                            {
                                                ltemp+=path[source_path][source_path+1][1]+c[kk][position]*t_dis+t_node;
                                                path[source_path][source_path+1][1]=ltemp;
                                                path[source_path+1][source_path][0]=path[source_path][source_path+1][0];
                                                path[source_path+1][source_path][1]=ltemp;//一条路径被占用，反过来也是占用的
                                                source_path=source_path+1;
                                            }
                                            else
                                            {
                                                path[source_path][source_path+1][0]=ltemp;
                                                path[source_path+1][source_path][0]=ltemp;
                                                ltemp+=c[kk][position]*t_dis+t_node;
                                                path[source_path][source_path+1][1]=ltemp;
                                                path[source_path+1][source_path][1]=ltemp;
                                                source_path=source_path+1;
                                            }
                                        }
                                    }
                                }
                            }
                            if(ltemp>Lstart)
                            {
                                Lstart=ltemp;
                            }
                        }
                    }
                    idletime=Lstart-E[ii];
                    //待机和睡眠能耗
                    if(idletime!=0)
                    {
                        //if(idletime<t0)
                       // {
                            Eis+=Rik[ii]*idletime;
                            Ei+=Rik[ii]*idletime;
                            idltime+=idletime;
                       // }
//                        else
//                        {
//                            Eis+=Rsk*(idletime-t_penalty)+extra_E;
//                            Es+=Rsk*(idletime-t_penalty)+extra_E;
//                            //idltime+=t0;
//                            i->comtime+=t_penalty;
//                            sleeptime+=idletime-t_penalty;//切换时间也算在sleep中
//                        }
                    }
                    tao[flag_end[ii]][position]=Lstart;
                    E[ii]=tao[flag_end[ii]][position]+t[ii][position];
                    taoend[flag_end[ii]][position]=E[ii];//每个任务的完成时间
//                    for(int kk=0; kk<n; kk++)
//                    {
//                        if(c[position][kk]>0 && (task_in_machine[kk] != task_in_machine[position]))
//                        {
//                            E[ii]+=2;
//                            break;
//                        }
//                    }
                    it++;
                    for(int jj=0; jj<n; jj++)
                    {
                        if(depcopy[flag_end[ii]][position][jj]>0&&position!=jj)
                        {

                            depcopy[flag_end[ii]][position][jj]=0.0;
                            isdepcopy[flag_end[ii]][jj]--;
                            todepcopy[flag_end[ii]][position]--;
                        }
                    }
                    if(position==(*(i->machine[ii].rbegin()))) //
                    {
                        flag_end[ii]++;
                        jud_index[ii]=0;
                    }
                    else
                    {
                        jud_index[ii]++;
                    }

                }
//                if(1==flag_com[ii])
//                {
//                    Ed+=cominitcost*Rdk[ii];//有外层循环了就不需要乘mycycle了。处理器花费的另一部分
//                }
            }
        }
//        for(int i=0;i<n;i++){
//            for(int j=0;j<n;j++){
//
//            }
//        }

    }

    for(int jj=0; jj<meshfactor*meshfactor; jj++)
    {
        if(i->mesh[jj]==1)
        {
            if(E[jj]>i->makespan)
            {
                i->makespan=E[jj];
            }
        }
    }
    //double tempsleep=0;
    for(int jj=0; jj<meshfactor*meshfactor; jj++)
    {
        if(i->mesh[jj]==1)
        {
//            if(i->makespan-E[jj]<t0)
//            {
                idltime+=i->makespan-E[jj];
                Eis+=Rik[jj]*(i->makespan-E[jj]);
                Ei+=Rik[jj]*(i->makespan-E[jj]);
//            }
//            else
//            {
//                sleeptime+=i->makespan-E[jj];
//                Eis+=Rsk*(i->makespan-E[jj]-t_penalty)+extra_E;
//                Es+=Rsk*(i->makespan-E[jj]-t_penalty)+extra_E;
//            }
        }
        //tempsleep+=i->makespan-E[jj];
    }

    i->energy=Ed+Eis+Eb;
    i->Ed=Ed;
    i->Ei=Ei;
    //i->Es=Es;
    //i->comtime=i->makespan-idltime-sleeptime;

    i->idltime=idltime;
    //i->sleeptime=sleeptime;
    //计算冲突概率，没有同源情况发生
    for(int cyc=0; cyc<mycycle; cyc++)
    {
        for(int ii=0; ii<n; ii++)
        {
            for(int jj=0; jj<n; jj++)
            {
                if(abs(taoend[cyc][ii]-taoend[cyc][jj])<=xi&&ii!=jj)
                {
                    for(int p=0; p<n; p++)
                    {
                        for(int qq=0; qq<n; qq++)
                        {
                            if(c[ii][p]>0&&c[jj][qq]>0)
                            {
                                pp[ii][jj]=pp[ii][jj]+pc[task_in_machine[ii]][task_in_machine[p]][task_in_machine[jj]][task_in_machine[qq]];
                            }
                        }
                    }
                }
            }
        }
    }
    for(int ii=0; ii<n; ii++)
    {
        for(int jj=0; jj<n; jj++)
        {
            com_sum+=pp[ii][jj];
            //printf("%lf\n",pp[ii][jj]);
        }
    }
    for(int ii=0; ii<n; ii++)
    {
        for(int jj=0; jj<n; jj++)
        {
            i-> p_contention = i->p_contention+abs(pp[ii][jj]-com_sum/(n*mycycle));
            //printf("pc:%lf\n",i->p_contention);
        }
    }
}

// 非支配排序
void non_domination_sort(Individual individuals[], int length, bool last)
{
    vector< Individual > frontCollection;
    vector< Individual > tempCollection;
    int rank = 1;
    for(int i = 0 ; i < length ; i ++)
    {
        //initial
        individuals[i].S.erase(individuals[i].S.begin(), individuals[i].S.end());
        individuals[i].n = 0;
        for(int j = 0 ; j < length ; j ++)
        {
            if(i!=j)
            {
                if(!last)  //last作为不同支配关系的判定，规定只执行else部分
                {
                    // if individual[i] dominate individual[j]
                    if(individuals[i].makespan < individuals[j].makespan && individuals[i].p_contention < individuals[j].p_contention && individuals[i].energy < individuals[j].energy)
                    {
                        // let individual[j] added to the S of the individual[i]
                        individuals[i].S.push_back(j);
                    }
                    else if(individuals[j].makespan < individuals[i].makespan && individuals[j].p_contention < individuals[i].p_contention && individuals[j].energy < individuals[i].energy)
                    {
                        individuals[i].n = individuals[i].n + 1;
                    }
                }
                else
                {
                    // if individual[i] dominate individual[j]
                    if(individuals[i].makespan <= individuals[j].makespan && individuals[i].p_contention <= individuals[j].p_contention&&individuals[i].energy <= individuals[j].energy)
                    {
                        // let individual[j] added to the S of the individual[i]
                        if(fabs(individuals[i].makespan - individuals[j].makespan) >= eps_0 && fabs(individuals[i].p_contention - individuals[j].p_contention) >= eps_0 && fabs(individuals[i].energy - individuals[j].energy) >= eps_0)
                        {
                            continue;
                        }
                        individuals[i].S.push_back(j);

                    }
                    else if(individuals[j].makespan <= individuals[i].makespan && individuals[j].p_contention <= individuals[i].p_contention&& individuals[j].energy <= individuals[i].energy)
                    {
                        if(fabs(individuals[i].makespan - individuals[j].makespan) >= eps_0 && fabs(individuals[i].p_contention - individuals[j].p_contention)>=eps_0&& fabs(individuals[i].energy - individuals[j].energy)>=eps_0)
                        {
                            continue;
                        }
                        individuals[i].n = individuals[i].n + 1;
                    }
                }
            }
        }
    }
    for(int i = 0 ; i < MAXN ; i ++)
    {
        vector<Individual>().swap(Front[i]);
    }
    for(int i = 0 ; i < length ; i ++)
    {
        if(individuals[i].n == 0)
        {
            individuals[i].front = rank;
            frontCollection.push_back(individuals[i]);
            Front[rank].push_back(individuals[i]);
        }
    }

    while(!frontCollection.empty())
    {
        tempCollection.erase(tempCollection.begin(), tempCollection.end());
        for(vector<Individual>::iterator iter = frontCollection.begin() ; iter != frontCollection.end() ; ++iter)
        {
            for(vector<int>::iterator jter = (*iter).S.begin() ; jter != (*iter).S.end() ; ++jter)
            {
                individuals[(*jter)].n = individuals[(*jter)].n - 1;
                if(individuals[(*jter)].n == 0)
                {
                    individuals[(*jter)].front = rank + 1;
                    Front[rank+1].push_back(individuals[(*jter)]);
                    tempCollection.push_back(individuals[(*jter)]);
                }
            }
        }
        rank++;
        frontCollection.erase(frontCollection.begin(), frontCollection.end());
        frontCollection.assign(tempCollection.begin(), tempCollection.end());
    }
}

//一半概率是随机两个个体，一半概率是随机一个，精英选一个
void gacrossover(int target1, int target2, Individual *individual) //将选择的两q个个体进行交叉
{
//    printf("crossover\n");
    int myMap[MAXN][2];//记录一个任务的所属机器
    vector<int>:: iterator iter;
    Individual ind1,ind2;
//	for(int j=0; j<m;++j){
//                printf("~machine %d: ",j);
//			for(iter=ind1.machine[j].begin();iter!=ind2.machine[j].end();iter++){
//				printf("%d ",(*iter));
//			}
//			printf("\n");
//        }
    for(int j = 0 ; j < m ; ++ j)
    {
        vector<int>().swap(individual->machine[j]);
    }
    ind1=*individual;
    ind2=*individual;
    int temp = rand() % 10;
    //if(temp >= 0 && temp < 10 && ElistCollection.size() != 0) {
//    if(0) {
//        target2 = rand() % ElistCollection.size();
//        for(int j = 0 ; j < m ; ++ j)
//        {
//            for(iter = Collection[target1].machine[j].begin(); iter != Collection[target1].machine[j].end(); iter ++)
//            {
//                myMap[(*iter)][0] = j;
//            }
//            for(iter = ElistCollection[target2].machine[j].begin(); iter != ElistCollection[target2].machine[j].end(); iter ++)
//            {
//                myMap[(*iter)][1] = j;
//            }
//        }
//    }else {
    for(int j = 0 ; j < m ; ++ j)
    {
        for(iter = Collection[target1].machine[j].begin(); iter != Collection[target1].machine[j].end(); iter ++)
        {
            myMap[(*iter)][0] = j;
        }
        for(iter = Collection[target2].machine[j].begin(); iter != Collection[target2].machine[j].end(); iter ++)
        {
            myMap[(*iter)][1] = j;
        }
    }
//    }
//printf("crossover2\n");
    for(int j=0; j<m; ++j)
    {
        for(iter=Collection[target1].machine[j].begin(); iter!=Collection[target1].machine[j].end(); iter++)
        {
            int temp=rand()%2;
            ind1.machine[myMap[(*iter)][temp]].push_back(*iter);
        }
        for(iter=Collection[target2].machine[j].begin(); iter!=Collection[target2].machine[j].end(); iter++)
        {
            int temp=rand()%2;
            ind2.machine[myMap[(*iter)][temp]].push_back(*iter);
        }
    }
    temp=rand()%2;

    if(temp==0)
    {
        //individual=&ind2;
        copy_individual(individual,&ind1);
    }
    else
    {
        copy_individual(individual,&ind2);
        //individual=&ind2;
    }
//        for(int j=0; j<m;++j){
//                printf("machine %d: ",j);
//			for(iter=individual->machine[j].begin();iter!=individual->machine[j].end();iter++){
//				printf("%d ",(*iter));
//			}
//			printf("\n");
//        }
//    for(int i = 0 ; i < n ; ++ i)
//    {
//        int temp = rand() % 2;
//        individual -> machine[myMap[i][temp]].push_back(i);//生成一个新的个体,保存到individual中
//    }
}

void light_perturbation(int segment[], int size_of_segment, int interval[])
{
    int temp, k, pos1, pos2, temp1;
    int interval1[MAXN];
    interval1[0] = interval[0];
    for(int i = 1 ; i < m ; i ++)
    {
        interval1[i] = interval1[i-1] + interval[i];
    }
    //产生两个随机机器
    temp = rand() % m;
    while(!interval[temp])
    {
        temp = rand() % m;
    }
    temp1 = rand() % m;
    while(temp == temp1)
    {
        temp1 = rand() % m;
    }

    if(interval[temp1] != 0)
    {
        if(temp == 0)
        {
            pos1 = rand() % interval1[temp];
        }
        else
        {
            pos1 = interval1[temp-1] + rand() % interval[temp];
        }
        if(temp1 == 0)
        {
            pos2 = rand() % interval1[temp1];
        }
        else
        {
            pos2 = interval1[temp1-1] + rand() % interval[temp1];
        }
        if(pos1 > pos2)
        {
            k = pos1;
            pos1 = pos2;
            pos2 = k;
        }
        k = segment[pos1];
        //插入操作
        for(int i = pos1 ; i < pos2 ; i ++)
        {
            segment[i] = segment[i + 1];
        }
        segment[pos2] = k;

        interval[temp] -= 1;
        interval[temp1] += 1;
    }
    else
    {
        interval[temp] -= 1;
        interval[temp1] += 1;
    }

}

void heavy_perturbation(int segment[], int size_of_segment, int interval[])
{
    int temp, k, pos1, pos2, temp1;
    int interval1[MAXN];
    interval1[0] = interval[0];
    for(int i = 1 ; i < m ; i ++)
    {
        interval1[i] = interval1[i-1] + interval[i];
    }

    temp = rand() % m;
    while(!interval[temp])
    {
        temp = rand() % m;
    }
    temp1 = rand() % m;
    while(temp == temp1)
    {
        temp1 = rand() % m;
    }

    if(interval[temp1])
    {
        if(temp == 0)
        {
            pos1 = rand() % interval1[temp];
        }
        else
        {
            pos1 = interval1[temp-1] + rand() % interval[temp];
        }
        if(temp1 == 0)
        {
            pos2 = rand() % interval1[temp1];
        }
        else
        {
            pos2 = interval1[temp1-1] + rand() % interval[temp1];
        }

        k = segment[pos1];
        segment[pos1] = segment[pos2];
        segment[pos2] = k;
    }
    else
    {

    }

}


void gamutation(Individual *individual)
{

    int temp = rand() % 10;
    int machine_time[MAXM];
    int all = 0;
    memset(machine_time, 0, sizeof(machine_time[0]));
    printf("mutation前的机器分布\n");
    for(int j = 0 ; j < m ; j ++){
        printf("第%d个机器: ", j);
        for(vector<int>::iterator iter = individual->machine[j].begin(); iter != individual->machine[j].end() ; iter ++){
            printf("%d ", (*iter));
        }
        printf("\n");
    }
    for(int i = 0; i < m; i ++) {
        printf("%d ", individual->mesh[i]);
    } printf("\n");
    for(int i = 0; i < m; i ++) {
        all += individual->mesh[i];
        if(individual->mesh[i]) {
            for(int j = 0; j < individual->machine[i].size(); j ++) {
                machine_time[i] += t[i][j];
            }
        }
    }

    double _temp = rand() % 10 * 1.0 / 10 * 1.0;
//        printf("temp = %lf\n", temp);
//        printf("scale = %lf\n", all * 1.0 / m * 1.0);
    if(_temp > all / m * 1.0) { // 拆核
        vector<int> tempV;
        tempV.clear();
//        printf("拆迁\n");
//        for(int i = 0; i < m; i ++) {
//            printf("%d ", individual->mesh[i]);
//        } printf("\n");
        int _id1 = 0;
        int _min = -inf;
        for(int i = 0; i < m; i ++) {
            if(machine_time[i] > _min && individual->mesh[i]) {
                _id1 = i;
                _min = machine_time[i];
            }

        }
        int _m = sqrt(m);

        for(int j = 0; j < individual->machine[_id1].size(); j ++) {
            tempV.push_back(individual->machine[_id1][j]);
        }
        individual->machine[_id1].clear();
        individual->mesh[_id1] = 0;
//        printf("tempSize= %d\n", tempV.size());
        for(int j = 0; j < m; j ++) {
            if(!individual->mesh[machineMap[_m][j]]) {
                for(int i = 0; i < tempV.size() / 2; i ++) {
                    individual->machine[machineMap[_m][j]].push_back(tempV[i]);
                }
                individual->mesh[machineMap[_m][j]] = 1;
                break;
            }
        }
        for(int j = 0; j < m; j ++) {
            if(!individual->mesh[machineMap[_m][j]]) {
                for(int i = tempV.size() / 2; i < tempV.size(); i ++) {
                    individual->machine[machineMap[_m][j]].push_back(tempV[i]);
                }
                individual->mesh[machineMap[_m][j]] = 1;
                break;
            }
        }
//        for(int i = 0; i < m; i ++) {
//            printf("%d ", individual->mesh[i]);
//        } printf("\n");
//        printf("拆迁完毕\n");

    } else {
        int _id = 0;
        int _id1 = 0;
        int _id2 = 0;
        int _max = inf;
        vector<int> tempV;
        tempV.clear();
        for(int i = 0; i < m; i ++) {
            if(machine_time[i] < _max && individual->mesh[i]) {
                _id1 = i;
                _max = machine_time[i];
            }
        }
        machine_time[_id1] = inf;
        _max = inf;
        for(int i = 0; i < m; i ++) {
            if(machine_time[i] < _max && individual->mesh[i]) {
                _id2 = i;
                _max = machine_time[i];
            }
        }
        printf("id1 = %d id2 = %d\n", _id1, _id2);

        for(int j = 0; j < individual->machine[_id1].size(); j ++) {
            tempV.push_back(individual->machine[_id1][j]);
        }
        for(int j = 0; j < individual->machine[_id2].size(); j ++) {
            tempV.push_back(individual->machine[_id2][j]);
        }

        individual->machine[_id1].clear();
        individual->mesh[_id1] = 0;
        individual->machine[_id2].clear();
        individual->mesh[_id2] = 0;
        int _m = sqrt(m);
        for(int i = 0; i < m; i ++) {
            if(machineMap[_m][i] == _id1 || machineMap[_m][i] == _id2) {
                individual->mesh[machineMap[_m][i]] = 1;
                for(int j = 0; j < tempV.size(); j ++) {
                    individual->machine[machineMap[_m][i]].push_back(tempV[j]);
                }
                break;
            }
        }

        for(int i = 0; i < m; i ++) {
            printf("%d ", individual->mesh[i]);
        } printf("bbbbbbbbbbbbbbbbbbbb\n");
//            while(1) {}
    }


    printf("mutation后的机器分布\n");
    for(int j = 0 ; j < m ; j ++){
        printf("第%d个机器: ", j);
        for(vector<int>::iterator iter = individual->machine[j].begin(); iter != individual->machine[j].end() ; iter ++){
            printf("%d ", (*iter));
        }
        printf("\n");
    }
}
double get_max_energy(int now_rank)
{
    vector<Individual>::iterator iter;
    double max_energy = -inf;
    double this_energy;
    for(iter = Front[now_rank].begin(); iter != Front[now_rank].end(); ++iter)
    {
        this_energy = (*iter).energy;
        if(max_energy < this_energy)
        {
            max_energy = this_energy;
        }
    }
    return max_energy;
}
double get_min_energy(int now_rank)
{
    vector<Individual>::iterator iter;
    double min_energy = inf;
    double this_energy;
    for(iter = Front[now_rank].begin(); iter != Front[now_rank].end(); ++iter)
    {
        this_energy = (*iter).energy;
        if(min_energy > this_energy)
        {
            min_energy = this_energy;
        }
    }
    return min_energy;
}
double get_max_communication(int now_rank)
{
    vector<Individual>::iterator iter;
    double max_communication = -inf;
    double this_communication;
    for(iter = Front[now_rank].begin(); iter != Front[now_rank].end(); ++iter)
    {
        this_communication = (*iter).makespan;
        if(max_communication < this_communication)
        {
            max_communication = this_communication;
        }
    }
    return max_communication;
}

double get_min_communication(int now_rank)
{
    vector<Individual>::iterator iter;
    double min_communication = inf;
    double this_communication;
    for(iter = Front[now_rank].begin(); iter != Front[now_rank].end(); ++iter)
    {
        this_communication = (*iter).makespan;
        if(min_communication > this_communication)
        {
            min_communication = this_communication;
        }
    }
    return min_communication;
}

double get_max_maxspan(int now_rank)
{
    vector<Individual>::iterator iter;
    double max_maxspan = -inf;
    double this_max_span;
    for(iter = Front[now_rank].begin(); iter != Front[now_rank].end(); ++iter)
    {
        this_max_span = (*iter).p_contention;
        if(max_maxspan < this_max_span)
        {
            max_maxspan = this_max_span;
        }
    }
    return max_maxspan;
}

double get_min_maxspan(int now_rank)
{
    vector<Individual>::iterator iter;
    double min_maxspan = inf;
    double this_min_span;
    for(iter = Front[now_rank].begin(); iter != Front[now_rank].end(); ++iter)
    {
        this_min_span = (*iter).p_contention;
        if(min_maxspan > this_min_span)
        {
            min_maxspan = this_min_span;
        }
    }
    return min_maxspan;
}

//计算拥挤距离
void crowdDistance(int now_rank)
{
    vector<Individual>::iterator iter;
    Individual front_individuals[MAXN];
    int length = 0;
    double max_communication = get_max_communication(now_rank);
    double min_communication = get_min_communication(now_rank);
    double max_maxspan = get_max_maxspan(now_rank);
    double min_maxspan = get_min_maxspan(now_rank);
    double max_energy = get_max_energy(now_rank);
    double min_energy = get_min_energy(now_rank);
    for(iter = Front[now_rank].begin(); iter != Front[now_rank].end(); ++ iter)
    {
        front_individuals[length] = (*iter);
        length ++;
    }
    qsort(front_individuals, length, sizeof(front_individuals[0]), cmp);
    front_individuals[0].crowd_distance = inf;
    front_individuals[length - 1].crowd_distance = inf;
    for(int i = 1 ; i < length - 1 ; i ++)
    {
        front_individuals[i].crowd_distance = front_individuals[i].crowd_distance + (front_individuals[i+1].p_contention - front_individuals[i-1].p_contention) / (max_communication - min_communication);
    }
    qsort(front_individuals, length, sizeof(front_individuals[0]), cmp1);
    front_individuals[0].crowd_distance = inf;
    front_individuals[length - 1].crowd_distance = inf;
    for(int i = 1 ; i < length - 1 ; i ++)
    {
        front_individuals[i].crowd_distance = front_individuals[i].crowd_distance + (front_individuals[i+1].makespan - front_individuals[i-1].makespan) / (max_maxspan - min_maxspan);
    }
    qsort(front_individuals, length, sizeof(front_individuals[0]), cmp0);
    front_individuals[0].crowd_distance = inf;
    front_individuals[length - 1].crowd_distance = inf;
    for(int i = 1 ; i < length - 1 ; i ++)
    {
        front_individuals[i].crowd_distance = front_individuals[i].crowd_distance + (front_individuals[i+1].energy - front_individuals[i-1].energy) / (max_energy - min_energy);
    }

    qsort(front_individuals, length, sizeof(front_individuals[0]), cmp2);
//    printf("*************\n");
//    for(int i = 0 ; i < n ; i ++){
//        printf("distance = %.2lf\n", front_individuals[i].crowd_distance);
//    }
//    printf("*************\n");
    Front[now_rank].erase(Front[now_rank].begin(), Front[now_rank].end());
    for(int i = 0 ; i < length ; i ++)
    {
        Front[now_rank].push_back(front_individuals[i]);
    }
}

void insertMachine(Individual *i, int a, int b, int c)   // a = taskIndex[nowPoint], b = nowPoint, c = temp
{
    vector<int>:: iterator iter;
    int j = 0;
    int k = 0;
    // delete temp
    for(j = 0 ; j < m ; j ++)
    {
        for(iter = i->machine[j].begin(); iter != i->machine[j].end(); iter ++)
        {
            if((*iter) == c)
            {
                i->machine[j].erase(iter);
                iter = i->machine[b].begin();
                while(k < a)
                {
                    k ++;
                    iter ++;
                }
                i->machine[b].insert(iter, c);
                return ;
            }
        }
    }
    return ;
}

//void swapMachine(Individual *i, int a, int b, int c) { // a = taskIndex[nowPoint], b = nowPoint, c = temp
//    vector<int>:: iterator iter;
//    int j = 0;
//    int k = 0;
//    //printf("value = %d c = %d\n", i->machine[b][a], c);
//    // delete temp
//    for(j = 0 ; j < m ; j ++) {
//        for(iter = i->machine[j].begin(); iter != i->machine[j].end(); iter ++) {
//            if((*iter) == c) {
//                //printf("b = %d a= %d\n", b, a);
//                int temp = c;
//                (*iter) = i->machine[b][a];
//                i->machine[b][a] = temp;
//                return ;
//            }
//        }
//    }
//    return ;
//}

int test(int task)
{
    int i;
    int tot = 0;
    int arr[MAXN];
    memset(arr, 0, sizeof(arr));
    for(i = 0 ; i < n ; i ++)
    {
        if(c[i][task] > 0)
        {
            if(doneSet.find(i) == doneSet.end() && taskUsed[i] == false)   //如果没有找到
            {
                arr[tot ++] = i;
            }
        }
    }
    if(tot == 0)return -1;//该任务可以被执行
    else
    {
        int random = rand() % tot;
        return arr[random];//返回需要依赖的一个任务
    }
}

//Repair segment
/********************************************
Function: repair_segment
Description: repair input segment of machines to fit in with requirement
Input: An individual
Output: void;
Others: Get accepted input of an individual
********************************************/
void repair_segment(Individual *i)
{
    vector<int>:: iterator iter;
    /***************initialize******************/
//    printf("repair前的结果\n");
//    for(int j = 0 ; j < m ; j ++){
//        printf("第%d个机器: ", j);
//        for(iter = i->machine[j].begin(); iter != i->machine[j].end() ; iter ++){
//            printf("%d ", (*iter));
//        }
//        printf("\n");
//    }
    memset(taskIndex, 0, sizeof(taskIndex));
    int acTask = 0;
    int nowPoint = 0;
    int depentTask[MAXM];
    bool dependent = false;
    memset(taskUsed, 0, sizeof(taskUsed));
    doneSet.clear();
    /*******************done********************/
    while(acTask < n)
    {
//        printf("actask = %d\n", acTask);
        dependent = false;
        for(nowPoint = 0 ; nowPoint < m ; nowPoint ++)   // 对所有的指针进行循环
        {
//            printf("size = %d\n", i->machine[nowPoint].size());
//            printf("taskindex = %d\n", taskIndex[nowPoint]);
            if(i->machine[nowPoint].size() == taskIndex[nowPoint])
            {
//                    dependent = true;
                depentTask[nowPoint] = -1; // 如果指针指向最后一个任务的后面，说明这个机器已经完成，他的依赖是-1.
                continue; // 如果指针指向最后一个元素，跳出
            }
            int nowTask = i->machine[nowPoint].at(taskIndex[nowPoint]);
//            printf("nowPoint = %d\n", nowPoint);
//            printf("nowTask = %d\n", nowTask);
            depentTask[nowPoint] = test(nowTask);
//            printf("depentTask[nowPoint] = %d\n", depentTask[nowPoint]);
            if(depentTask[nowPoint] == -1)   // 如果能符合依赖，指针后移并且可满足的机器数+1.
            {
                taskIndex[nowPoint] ++;
                acTask ++;
                taskUsed[nowTask] = true;
                doneSet.insert(nowTask);
                dependent = true;
                break;
            }
        }

        if(dependent == false)
        {
//            printf("不符合依赖\n");
//            int machine = rand() % m;

//            int temp = rand() % m;
//            printf("选择的机器是%d\n", temp);
//            while(depentTask[temp] == -1) temp = rand() % m;
//            int number = rand() % m;
//            while(depentTask[number] == -1) number = rand() % m;
//            insertMachine(i, taskIndex[machine], machine, depentTask[temp]);
//            printf("插入后的结果\n");
//            for(int j = 0 ; j < m ; j ++){
//                printf("第%d个机器: ", j);
//                for(iter = i->machine[j].begin(); iter != i->machine[j].end() ; iter ++){
//                    printf("%d ", (*iter));
//                }
//                printf("\n");
//            }
            for(int machine=0; machine<m; machine++)
            {
                if(depentTask[machine]==-1)
                    continue;
                else
                {
                    insertMachine(i, taskIndex[machine], machine, depentTask[machine]);
                }
            }
        }
    }
}

void swap_machine(Individual *individual, int nowM, int nowPos, int toM, int toPos)
{
    vector<int>::iterator iter;
    int temp = individual->machine[nowM][nowPos];
    individual->machine[nowM][nowPos] = individual->machine[toM][toPos];
    individual->machine[toM][toPos] = temp;
}

void insert_machine(Individual *individual, int nowM, int nowPos, int toM, int toPos)
{
    if(individual->mesh[toM] == 1)
    {
        vector<int>::iterator iter;
        int temp = individual->machine[nowM][nowPos];
        individual->machine[toM].insert(individual->machine[toM].begin() + toPos, temp);

        if(nowM == toM && nowPos > toPos) individual->machine[nowM].erase(individual->machine[nowM].begin() + nowPos + 1);//插入temp，所以要加1
        else individual->machine[nowM].erase(individual->machine[nowM].begin() + nowPos);//正常删除就行
    }
}

bool check_machine(Individual *individual)
{
    vector<int>:: iterator iter;
    /***************initialize******************/
    memset(taskIndex, 0, sizeof(taskIndex));
    int acTask = 0;
    int nowPoint = 0;
    int depentTask[MAXM];
    bool dependent = false;
    memset(taskUsed, 0, sizeof(taskUsed));
    doneSet.clear();
    /*******************done********************/
    while(acTask < n)
    {
//        printf("n = %d\n", n);
//        printf("actask = %d\n", acTask);
//        dependent = false;
//        for(int i = 0; i < m; i ++) {
//            printf("%d ", taskIndex[i]);
//        }
//        printf("\n");
        dependent = false;
        for(nowPoint = 0 ; nowPoint < m ; nowPoint ++)   // 对所有的指针进行循环
        {
//            printf("nowpoint = %d\n", nowPoint);
            if(individual->machine[nowPoint].size() == taskIndex[nowPoint])
            {
                depentTask[nowPoint] = -1; // 如果指针指向最后一个任务的后面，说明这个机器已经完成，他的依赖是-1.
                continue; // 如果指针指向最后一个元素，跳出
            }
            int nowTask = individual->machine[nowPoint].at(taskIndex[nowPoint]);
            depentTask[nowPoint] = test(nowTask);
            if(depentTask[nowPoint] == -1)   // 如果能符合依赖，指针后移并且可满足的机器数+1.
            {
                taskIndex[nowPoint] ++;
                acTask ++;
                if(acTask == n) return true;
                taskUsed[nowTask] = true;
                doneSet.insert(nowTask);
                dependent = true;
                break;
            }
        }
        if(dependent == false)
        {
            return false;
        }
    }
}
//定义非支配关系
int compareIndividual(Individual *a, Individual *b)
{
    if(fabs(a->makespan - b->makespan) <= eps_0 && fabs(a->p_contention - b->p_contention) <= eps_0 && fabs(a->energy - b->energy) <= eps_0) return 0;//a=b
//    if((a->makespan < b->makespan && a->workload <= b->workload) || (a->workload < b->workload && a->makespan <= b->makespan)) return 1;//a dominates b
//    if((a->makespan >= b->makespan && a->workload >= b->workload) || (a->workload > b->workload && a->makespan >= b->makespan)) return 2;//b dominates a
    if(xita*(a->makespan) <= b->makespan && xita*(a->p_contention) <= b->p_contention && xita*(a->energy)<=b->energy) return 1;//a dominates b
    if(a->makespan >= xita*(b->makespan) && a->p_contention >= xita*(b->p_contention) && a->energy >= xita*(b->energy)) return 2;//a dominates b

    return 3;
}

void relaxElistCollection(Individual *i)
{
    vector<Individual>::iterator iter;
    for(iter = ElistCollection.begin(); iter != ElistCollection.end(); iter ++)
    {
        if(fabs(i->makespan - (*iter).makespan) >= eps_0 && (fabs(i->p_contention - (*iter).p_contention) >= eps_0)&& (fabs(i->energy - (*iter).energy) >= eps_0))
        {
            continue;
        }
        else
        {
            int ret = compareIndividual(i, &(*iter));
            if(ret == 1)
            {
                ElistCollection.erase(iter);
                iter --;
            }
        }
    }
}

void updateElistCollection(Individual *i)
{
    bool flag = false;
    bool changed = false;
    vector<Individual>::iterator iter;
    if(ElistCollection.empty())
    {
        ElistCollection.push_back(*i);
        finish = clock();
        real_time=(double)(finish - start) / CLOCKS_PER_SEC;
//        printf("find a better solution in: %.2f s	\n", real_time);
        changed = true;
    }
    else
    {
        for(iter = ElistCollection.begin(); iter != ElistCollection.end(); iter ++)
        {
            int ret = compareIndividual(i, &(*iter));
            if(ret == 0)
            {
                flag = true;
                break;
            }
            else if(ret == 1)
            {
                (*iter) = *i;
                flag = true;
                relaxElistCollection(i);
                finish = clock();
                real_time=(double)(finish - start) / CLOCKS_PER_SEC;
//                printf("find a better solution in: %.2f s	\n", real_time);
                changed = true;
                break;
            }
            else if(ret == 2)
            {
                flag = true;
                break;
            }
        }
        if(!flag)
        {
            ElistCollection.push_back(*i);
            changed = true;
            finish = clock();
            real_time=(double)(finish - start) / CLOCKS_PER_SEC;
//            printf("find a better solution in : %.2f s	\n", real_time);
        }
    }
}

void swap_localsearch(Individual *individual)
{
    /***************initialize******************/
    int flag[MAXN];
    int k = 1;
    int kMax = 1;
    int nowMachine;
    int nowPos;
    int toMachine;
    int toPos;
    int segmentSize[MAXM];
    int randomSequence[MAXN];
    int machineNumber;
    int temp;
    Individual temp_individual = *individual;
    Individual best_individual = *individual;
    Individual origin_individual = *individual;
    for(int l = 0 ; l < m ; l ++)
    {
        segmentSize[l] = temp_individual.machine[l].size();
    }

    //generate a sequence by randomly swap
    for(int i = 0 ; i < n ; i ++)
    {
        randomSequence[i] = i;
    }
    for(int i = 0 ; i < n ; i ++)
    {
        temp = rand() % n;
        swap(randomSequence[i], randomSequence[temp]);
    }

    int mark = 0;
    machineNumber = 0;
    /******************done*********************/
    while(k <= kMax)
    {

//        origin_individual = temp_individual;
       // printf("aaaaa begin\n");
        evaluate_objective(&best_individual);
     //   printf("aaaaa end\n");
        double makespan = best_individual.makespan;
        double p_contention = best_individual.p_contention;
        double energy=best_individual.energy;
        nowMachine = 0;
        temp = randomSequence[machineNumber];
//        printf("temp = %d\n", temp);
        for(int l = 0 ; l < m ; l ++)
        {
            segmentSize[l] = temp_individual.machine[l].size();
        }
        while(temp - segmentSize[nowMachine] >= 0)
        {
            temp -= segmentSize[nowMachine];
            nowMachine ++;
        }
//        printf("segmentSize[%d] = %d\n", nowMachine, segmentSize[nowMachine]);
        if(temp < 0) nowPos = segmentSize[nowMachine] + temp;
        else nowPos = temp;
        machineNumber ++;
//        printf("nowMachine = %d nowPos = %d\n", nowMachine, nowPos);
        // random generate a task
//        nowMachine = rand() % m;
//        if(segmentSize[nowMachine] == 0) continue;
//        nowPos = rand() % segmentSize[nowMachine];
        // task done
        // find best neighbor
        /*-------------------------------------------*/
        for(toMachine = 0 ; toMachine < m ; toMachine ++)
        {
            if(segmentSize[toMachine]) for(toPos = 0 ; toPos < segmentSize[toMachine] ; toPos ++)
                {
                    if(nowMachine != toMachine || nowPos != toPos)
                    {
//                    printf("nowMachine = %d nowPos = %d toMachine = %d toPos = %d\n", nowMachine, nowPos, toMachine, toPos);
//                    printf("insert 前\n");
//                    for(int j = 0 ; j < m ; j ++){
//                        printf("第%d个机器: ", j);
//                        for(vector<int>::iterator iter = temp_individual.machine[j].begin(); iter != temp_individual.machine[j].end() ; iter ++){
//                            printf("%d ", (*iter));
//                        }
//                        printf("\n");
//                    }

                        insert_machine(&temp_individual, nowMachine, nowPos, toMachine, toPos);
//                        printf("insert 后\n");
//                    for(int j = 0 ; j < m ; j ++){
//                        printf("第%d个机器: ", j);
//                        for(vector<int>::iterator iter = temp_individual.machine[j].begin(); iter != temp_individual.machine[j].end() ; iter ++){
//                            printf("%d ", (*iter));
//                        }
//                        printf("\n");
//                    }

                        if(check_machine(&temp_individual))   //如果符合条件
                        {
//                        printf("fuhe\n");
//                            printf("bbbbb begin\n");
                            evaluate_objective(&temp_individual);
//                            printf("bbbbb begin\n");
//                        printf("evaluate 后\n");
//                        for(int j = 0 ; j < m ; j ++){
//                            printf("第%d个机器: ", j);
//                            for(vector<int>::iterator iter = temp_individual.machine[j].begin(); iter != temp_individual.machine[j].end() ; iter ++){
//                                printf("%d ", (*iter));
//                            }
//                            printf("\n");
//                        }
//                        printf("individual\n");
//                        for(int j = 0 ; j < m ; j ++){
//                            printf("第%d个机器: ", j);
//                            for(vector<int>::iterator iter = individual->machine[j].begin(); iter != individual->machine[j].end() ; iter ++){
//                                printf("%d ", (*iter));
//                            }
//                            printf("\n");
//                        }
//                        for(int j = 0 ; j < m ; j ++){
//                            printf("第%d个机器: ", j);
//                            for(vector<int>::iterator iter = individual->machine[j].begin(); iter != individual->machine[j].end() ; iter ++){
//                                printf("%d ", (*iter));
//                            }
//                            printf("\n");
//                        }
                            //if((temp_individual.makespan <= makespan && temp_individual.workload < workload) || (temp_individual.makespan < makespan && temp_individual.workload <= workload)) {
                            if(xita*(temp_individual.makespan) <= makespan && xita*(temp_individual.p_contention) <= p_contention && xita*(temp_individual.energy) <= energy)
                            {
                                if(fabs(xita*(temp_individual.makespan)-makespan) <= eps_0 && fabs(xita*(temp_individual.p_contention)-p_contention) <= eps_0 && fabs(xita*(temp_individual.energy)-energy) <= eps_0 )
                                {

                                }
                                else
                                {

                                    makespan = temp_individual.makespan;
                                    p_contention = temp_individual.p_contention;
                                    energy=temp_individual.energy;
//                            printf("find best before before\n");
//                            for(int j = 0 ; j < m ; j ++){
//                                printf("第%d个机器: ", j);
//                                for(vector<int>::iterator iter = individual->machine[j].begin(); iter != individual->machine[j].end() ; iter ++){
//                                    printf("%d ", (*iter));
//                                }
//                                printf("\n");
//                            }
                                    best_individual = temp_individual;
//                            printf("find best before\n");
//                            for(int j = 0 ; j < m ; j ++){
//                                printf("第%d个机器: ", j);
//                                for(vector<int>::iterator iter = individual->machine[j].begin(); iter != individual->machine[j].end() ; iter ++){
//                                    printf("%d ", (*iter));
//                                }
//                                printf("\n");
//                            }
                                    makespan = best_individual.makespan;
                                    p_contention = best_individual.p_contention;
                                    energy=best_individual.energy;
                                    //找到更优解，更新
                                    updateElistCollection(&temp_individual);
//                            printf("find best\n");
//                            for(int j = 0 ; j < m ; j ++){
//                                printf("第%d个机器: ", j);
//                                for(vector<int>::iterator iter = individual->machine[j].begin(); iter != individual->machine[j].end() ; iter ++){
//                                    printf("%d ", (*iter));
//                                }
//                                printf("\n");
//                            }
                                }
                            }
                            //非支配 则更新
                            if(xita*(temp_individual.makespan) < makespan || xita*(temp_individual.p_contention) < p_contention||xita*(temp_individual.energy)<energy)
                            {
                                updateElistCollection(&temp_individual);

                                //in linux it's times(&)
//                            real_time = double(finish.tms_utime - start.tms_utime + finish.tms_stime - start.tms_stime)/sysconf(_SC_CLK_TCK);
//                            real_time = round(real_time * 100)/100.0;

                            }
                        }
//                    printf("individual\n");
//                    for(int j = 0 ; j < m ; j ++){
//                        printf("第%d个机器: ", j);
//                        for(vector<int>::iterator iter = individual->machine[j].begin(); iter != individual->machine[j].end() ; iter ++){
//                            printf("%d ", (*iter));
//                        }
//                        printf("\n");
//                    }
                        temp_individual = *individual;

//                    printf("还原temp\n");
//                    for(int j = 0 ; j < m ; j ++){
//                        printf("第%d个机器: ", j);
//                        for(vector<int>::iterator iter = temp_individual.machine[j].begin(); iter != temp_individual.machine[j].end() ; iter ++){
//                            printf("%d ", (*iter));
//                        }
//                        printf("\n");
//                    }
//                    printf("individual\n");
//                    for(int j = 0 ; j < m ; j ++){
//                        printf("第%d个机器: ", j);
//                        for(vector<int>::iterator iter = individual->machine[j].begin(); iter != individual->machine[j].end() ; iter ++){
//                            printf("%d ", (*iter));
//                        }
//                        printf("\n");
//                    }
                    }
                }
        }
        k ++;
//        printf("best_individual.makespan = %.2lf individual->makespan = %.2lf\n", best_individual.makespan, individual->makespan);
        // if((best_individual.makespan <= individual->makespan && best_individual.workload < individual->workload) || (best_individual.makespan < individual->makespan && best_individual.workload <= individual->workload)) {
        if(xita*(best_individual.makespan) <= individual->makespan && xita*(best_individual.p_contention) <= individual->p_contention && xita*(best_individual.energy)<=individual->energy)
        {
            if(fabs(xita*(best_individual.makespan) - individual->makespan) <= eps_0 && fabs(xita*(best_individual.p_contention)- individual->p_contention) <= eps_0 && fabs(xita*(best_individual.energy)-individual->energy) <= eps_0)
            {
            }
            else
            {

                *individual = best_individual;
                temp_individual = best_individual;
                k = 1;
                machineNumber = 0;
                for(int i = 0 ; i < n ; i ++)
                {
                    randomSequence[i] = i;
                }
                for(int i = 0 ; i < n ; i ++)
                {
                    temp = rand() % n;
                    swap(randomSequence[i], randomSequence[temp]);
                }
                for(int l = 0 ; l < m ; l ++)
                {
                    segmentSize[l] = temp_individual.machine[l].size();
                }
//            printf("k init\n");
            }
        }
    }
}

void make_new_pop(Individual individuals[], int length)
{
    vector<int>::iterator iter;
    int flag_individual[MAXN]; //标记这个个体是否被选择过
    //tournament_selection
    memset(flag_individual, 0, sizeof(flag_individual)); //初始全部未被选择
    for(int i = 0 ; i < length ; i ++)
    {
        int target1 = rand() % ((length<<1));
        while(flag_individual[target1] != 0)
        {
            target1 = rand() % ((length<<1));
        }
        //   printf("1新生成机器%d\n",i);
        flag_individual[target1] = 1;
        int target2 = rand() % ((length<<1));
        while(flag_individual[target2] != 0)
        {
            target2 = rand() % ((length<<1));
        } //随机选择两个目标
        //     printf("2新生成机器%d\n",i);
        flag_individual[target2] = 1;
//        printf("target1 = %d, target2 = %d\n", target1, target2);
        int temp = rand() % 10;
        gacrossover(target1, target2, &new_individual);
        //printf("3新生成机器%d\n",i);
        if(temp >= 0 && temp < 9) {}
        else
        {
            //        printf("4新生成机器%d\n",i);
            gamutation(&new_individual);
            //        printf("5新生成机器%d\n",i);
        }
//        printf("temp = %d\n", temp);
//        printf("新生成机器%d\n",i);
//        for(int j = 0 ; j < m ; j ++){
//            printf("第%d个机器: ", j);
//            for(iter = new_individual.machine[j].begin(); iter != new_individual.machine[j].end() ; iter ++){
//                printf("%d ", (*iter));
//            }
//            printf("\n");
//        }
        //Swap_localsearch(&new_individual);

        repair_segment(&new_individual);
        //printf("evaluate begin \n");
        evaluate_objective(&new_individual);
        //printf("evaluate done\n");
       // printf("swap begin\n");
        swap_localsearch(&new_individual);
       // printf("swap done\n");
        copy_individual(&individuals[length + i], &new_individual);

//        gacrossover(target1, target2, &new_individual);
//        gamutation(&new_individual);


    }
}
bool machines_cmp(const vector<int> &a,const vector<int> &b)
{
    return a.size() < b.size();
}
bool machines_cmp1(const vector<int> &a,const vector<int> &b)
{
    return a.size() > b.size();
}

void normalizeAssign()
{

    vector<int> temp;

    sort(machines.begin(), machines.end(), machines_cmp);
    printf("after sort\n");
    printf("*********************************\n");
    for(int i = 0; i < machines.size(); i ++)
    {
        for(int j = 0; j < machines[i].size(); j ++)
        {
            printf("%d ", machines[i][j]);
        }
        printf("\n");
    }
    printf("\n");
//    //merge
    printf("开始合并\n");

    int k = 0;
    while(machines.size() > m)
    {
        temp.clear();
        int size1 = machines[0].size();
        int size2 = machines[1].size();
        k = 0;
//        printf("size1 = %d size2 = %d\n", size1, size2);
        while(k < size1 && k < size2)
        {
            temp.push_back(machines[0][k]);
            temp.push_back(machines[1][k]);
            k ++;
        }
        while(k < size1)
        {
            temp.push_back(machines[0][k]);
            k ++;
        }
        while(k < size2)
        {
            temp.push_back(machines[1][k]);
            k ++;
        }
        machines.erase(machines.begin());
        machines.erase(machines.begin());
        machines.push_back(temp);
        sort(machines.begin(), machines.end(), machines_cmp);
//        printf("***************合并一次的结果*****************\n");
//        for(int i = 0; i < machines.size(); i ++) {
//            for(int j = 0; j < machines[i].size(); j ++) {
//                printf("%d ", machines[i][j]);
//            } printf("\n");
//        }
//        printf("\n");
    }
    printf("after sort\n");
    printf("*********************************\n");
    sort(machines.begin(), machines.end(), machines_cmp1);
    for(int i = 0; i < machines.size(); i ++)
    {
        for(int j = 0; j < machines[i].size(); j ++)
        {
            printf("%d ", machines[i][j]);
        }
        printf("\n");
    }
    printf("\n");
    int _m = (int)sqrt(m);
    for(int i = 0; i < machines.size(); i ++)
    {
        for(int j = 0; j < machines[i].size(); j ++)
        {
//            printf("m=%d\n", m);
//            printf("id=%d\n", machineMap[_m][i]);
            Collection[0].machine[machineMap[_m][i]].push_back(machines[i][j]);
        }
    }
//    int _m = (int)sqrt(m);
//    for(int i = 0; i < machines.size(); i ++) {
//        for(int j = 0; j < machines[i].size(); j ++) {
////            printf("m=%d\n", m);
////            printf("id=%d\n", machineMap[_m][i]);
//            Collection[0].machine[i].push_back(machines[i][j]);
//        }
//    }
}

//只产生一个解
void greedy_with_topo()
{
    int in[MAXN];
    int number_in_machine[MAXM];
    int ac_task = 0;
    int now_machine = 0;
    int maxN = n / m;
    int vis[MAXN];
    bool updateMachine;
    bool seal[MAXN];

    for(int i = 0 ; i < n ; i ++)
    {
        in[i] = isdep[0][i];
    }
    memset(number_in_machine, 0, sizeof(number_in_machine));
    memset(vis, 0, sizeof(vis));
    memset(seal, 0, sizeof(seal));

    while(ac_task < n)
    {

        updateMachine = false;

        for(int i = 0 ; i < n ; i ++)
        {

            if(!in[i] && !vis[i] && !seal[i])
            {
//                Collection[0].machine[now_machine].push_back(i);
//                printf("asdasdasd\n");
                for(int j = 0 ; j < n ; j ++)
                {
                    if(!in[j] && !vis[j])
                    {
                        seal[j] = 1;
                    }
                }

                vis[i] = 1;
                for(int j = 0 ; j < n ; j ++)
                {
                    if(c[i][j] > 0)
                    {
                        in[j] --;
                    }
                }

                updateMachine = true;
                _machines.push_back(i);
                ac_task ++;
                printf("actask = %d\n", ac_task);
//                if(Collection[0].machine[now_machine].size() >= maxN && now_machine < m - 1) {
//                    now_machine ++;
//                }
                printf("分配的机器\n");
                for(int j = 0; j < _machines.size(); j ++)
                {
                    printf("%d ", _machines[j]);
                }
                printf("\n");
            }
        }

        if(!updateMachine)
        {

            for(int i = 0 ; i < n ; i ++)
            {
                if(seal[i] && !vis[i])
                {
                    seal[i] = 0;

                    machines.push_back(_machines);
                    _machines.clear();

                    break;
                }
            }
        }
    }
    machines.push_back(_machines);
    normalizeAssign();

}


void init()
{
//    set<int> flag_machine;
//    stack<int> segment;
//    set<int> interval;
//    int kk, kkk;
//    vector<int>::iterator iter;
//    set<int>::iterator iiter;
//    int tempkk;
//    for(int i = 0 ; i < pop*2 ; i ++)
//    {
//        for(int j = 0 ; j < m ; j ++)
//        {
//            Collection[i].machine[j].erase(Collection[i].machine[j].begin(), Collection[i].machine[j].end());
//        }
//    }
//    printf("greedy begin\n");
//    greedy_with_topo();
//    printf("greedy done\n");
//
//
//    for(int i = 0; i < m; i ++)
//    {
//        if(Collection[0].machine[i].size() != 0)
//        {
//            Collection[0].mesh[i] = 1;
//        }
//    }
//
//    bool greedy = check_machine(&Collection[0]);
//    printf("新生成是否可行  %d\n", greedy);
//
//    printf("贪心生成的机器序列\n");
//    for(int i = 0 ; i < m ; i ++)
//    {
//        printf("第%d个机器\n", i);
//        for(int j = 0; j < Collection[0].machine[i].size(); j ++)
//        {
//            printf("%d ", Collection[0].machine[i][j]);
//        }
//        printf("\n");
//    }
//
//    for(int i = 1 ; i < pop*2 ; i ++)
//    {
//        flag_machine.clear();
//        while(!segment.empty())
//        {
//            segment.pop();
//        }
//
//        for(int j = 0 ; j < n * 2 ; j ++)
//        {
//            int temp = rand() % n;
//            if(flag_machine.insert(temp).second)
//            {
//                segment.push(temp);
//            }
//        }
//        for(int k = 0 ; k < n ; k ++)
//        {
//            if(flag_machine.insert(k).second)
//            {
//                segment.push(k);
//            }
//        }
//
//        interval.clear();
//        kk = m - 1;
//
//        while(kk)
//        {
//            int temp = rand() % (n);
//            if(temp == 0) temp = 1;
//            while(!interval.insert(temp).second)
//            {
//                temp = rand() % (n);
//                if(temp == 0) temp = 1;
////                 printf("%d\n",kk);
//            }
//            kk --;
//
//        }
//
//        kkk = 0;
//        for(iiter = interval.begin(); iiter != interval.end(); iiter ++)
//        {
//            if(iiter == interval.begin())
//            {
//                kk = (*iiter);
//            }
//            else
//            {
//                kk = (*iiter) - kk;
//            }
//            tempkk = kk;
//            while(tempkk --)
//            {
//                Collection[i].machine[kkk].push_back(segment.top());
//                segment.pop();
//
//            }
//            kkk ++;
//            kk = (*iiter);
//        }
//
//        kk = n - kk;
//        tempkk = kk;
//        while(tempkk --)
//        {
//            Collection[i].machine[kkk].push_back(segment.top());
//            segment.pop();
//
//        }
//
//        repair_segment(&Collection[i]);
//        for(int j = 0; j < m; j ++)
//        {
//            if(Collection[i].machine[j].size() != 0)
//            {
//                Collection[i].mesh[j] = 1;
//            }
//        }
//    }
    Collection[0].machine[0].push_back(0);
    Collection[0].machine[0].push_back(1);
    Collection[0].machine[0].push_back(2);
    Collection[0].machine[0].push_back(3);
    Collection[0].machine[0].push_back(4);
    for(int i = 0;i < m; i ++) {
    if(Collection[0].machine[i].size()) {
        Collection[0].mesh[i] = 1;
    } else {
        Collection[0].mesh[i] = 0;
    }
    }
    repair_segment(&Collection[0]);
    printf("初始化生成的机器\n");
    for(int i = 0 ; i < m ; i ++)
    {
        printf("第%d个机器\n", i);
        for(int j = 0; j < Collection[0].machine[i].size(); j ++)
        {
            printf("%d ", Collection[0].machine[i][j]);
        }
        printf("\n");
    }
    for(int i = 0;i < m; i ++) {
        if(Collection[0].machine[i].size()) {
            Collection[0].mesh[i] = 1;
        } else {
            Collection[0].mesh[i] = 0;
        }
    }
    evaluate_objective(&Collection[0]);
    printf("makespan = %lf energy = %lf p_contention = %lf\n", Collection[0].makespan, Collection[0].energy, Collection[0].p_contention);
    exit(0);
}

void compute_shared_path()
{
    int ox=0,oy=0;

    for(int i=0; i<meshfactor*meshfactor; i++)
    {
        for(int j=0; j<meshfactor*meshfactor; j++)
        {
            D[i][j]=abs(i/meshfactor-j/meshfactor)+abs(i%meshfactor-j%meshfactor);//计算两个核之间的距离
        }
    }
    //暂时只处理2*2,3*3 mesh
    if(2==meshfactor){
        int shared[4][4][4][4] ={0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0  ,
0, 1, 0, 1 ,
0, 0, 0, 0 ,
0, 1, 0, 0 ,
0, 0, 0, 0  ,
0, 0, 1, 1 ,
0, 0, 1, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 1, 1, 2 ,
0, 0, 0, 1 ,
0, 0, 0, 1 ,
0, 0, 0, 0,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 1, 0 ,
0, 0, 1, 1 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 1 ,
0, 0, 1, 1 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 1, 0, 0 ,
0, 0, 0, 0 ,
0, 1, 0, 1 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 1 ,
0, 0, 0, 0 ,
0, 1, 0, 1 ,
0, 0, 0, 0,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0 ,
0, 0, 0, 0};
 memcpy(gamma,shared,sizeof(shared));
         //gamma[i][j][p][q]=ox+oy;
    }
    else if(3==meshfactor){
         int shared[9] [9] [9] [9]  ={0, 0, 0, 0, 0, 0, 0, 0, 0 ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
0, 1, 1, 0, 1, 1, 0, 1, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
0, 1, 2, 0, 1, 2, 0, 1, 2  ,
0, 0, 1, 0, 0, 1, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
0, 0, 0, 1, 0, 0, 1, 0, 0  ,
0, 0, 0, 1, 0, 0, 1, 0, 0  ,
0, 0, 0, 1, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
0, 1, 1, 0, 2, 1, 0, 2, 1  ,
0, 0, 0, 0, 1, 0, 0, 1, 0  ,
0, 0, 0, 0, 1, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
0, 1, 2, 0, 1, 3, 0, 1, 3  ,
0, 0, 1, 0, 0, 2, 0, 0, 2  ,
0, 0, 0, 0, 0, 1, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
0, 0, 0, 1, 0, 0, 2, 0, 0  ,
0, 0, 0, 1, 0, 0, 2, 0, 0  ,
0, 0, 0, 1, 0, 0, 2, 0, 0  ,
0, 0, 0, 0, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
0, 1, 1, 0, 2, 1, 0, 3, 1  ,
0, 0, 0, 0, 1, 0, 0, 2, 0  ,
0, 0, 0, 0, 1, 0, 0, 2, 0  ,
0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
0, 1, 2, 0, 1, 3, 0, 1, 4  ,
0, 0, 1, 0, 0, 2, 0, 0, 3  ,
0, 0, 0, 0, 0, 1, 0, 0, 2  ,
0, 0, 0, 0, 0, 0, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0     ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 1, 0, 0, 1, 0, 0  ,
1, 0, 0, 1, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
0, 0, 1, 0, 0, 1, 0, 0, 1  ,
0, 0, 1, 0, 0, 1, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
0, 0, 0, 1, 0, 0, 1, 0, 0  ,
1, 0, 0, 2, 0, 0, 2, 0, 0  ,
1, 0, 0, 2, 0, 0, 2, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
0, 0, 0, 0, 1, 0, 0, 1, 0  ,
0, 0, 0, 0, 1, 0, 0, 1, 0  ,
0, 0, 0, 0, 1, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
0, 0, 1, 0, 0, 2, 0, 0, 2  ,
0, 0, 1, 0, 0, 2, 0, 0, 2  ,
0, 0, 0, 0, 0, 1, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
0, 0, 0, 1, 0, 0, 2, 0, 0  ,
1, 0, 0, 2, 0, 0, 3, 0, 0  ,
1, 0, 0, 2, 0, 0, 3, 0, 0  ,
0, 0, 0, 0, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
0, 0, 0, 0, 1, 0, 0, 2, 0  ,
0, 0, 0, 0, 1, 0, 0, 2, 0  ,
0, 0, 0, 0, 1, 0, 0, 2, 0  ,
0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
0, 0, 1, 0, 0, 2, 0, 0, 3  ,
0, 0, 1, 0, 0, 2, 0, 0, 3  ,
0, 0, 0, 0, 0, 1, 0, 0, 2  ,
0, 0, 0, 0, 0, 0, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0     ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 1, 0, 0, 1, 0, 0  ,
2, 1, 0, 2, 1, 0, 2, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 1, 0, 1, 1, 0, 1, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 1, 0, 0, 1, 0, 0  ,
1, 0, 0, 2, 0, 0, 2, 0, 0  ,
2, 1, 0, 3, 1, 0, 3, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 1, 0, 0, 1, 0  ,
0, 0, 0, 0, 1, 0, 0, 1, 0  ,
1, 1, 0, 1, 2, 0, 1, 2, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 1, 0, 0, 1  ,
0, 0, 0, 0, 0, 1, 0, 0, 1  ,
0, 0, 0, 0, 0, 1, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 1, 0, 0, 2, 0, 0  ,
1, 0, 0, 2, 0, 0, 3, 0, 0  ,
2, 1, 0, 3, 1, 0, 4, 1, 0  ,
0, 0, 0, 0, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 1, 0, 0, 2, 0  ,
0, 0, 0, 0, 1, 0, 0, 2, 0  ,
1, 1, 0, 1, 2, 0, 1, 3, 0  ,
0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 1, 0, 0, 2  ,
0, 0, 0, 0, 0, 1, 0, 0, 2  ,
0, 0, 0, 0, 0, 1, 0, 0, 2  ,
0, 0, 0, 0, 0, 0, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0     ,
  0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 2, 1, 0, 1, 1, 0, 1, 1  ,
0, 1, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 3, 0, 1, 2, 0, 1, 2  ,
0, 0, 2, 0, 0, 1, 0, 0, 1  ,
0, 0, 1, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 1, 0, 1, 1, 0, 1, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 2, 0, 1, 2, 0, 1, 2  ,
0, 0, 1, 0, 0, 1, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 1, 1, 0, 1, 1, 0, 2, 1  ,
0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 1  ,
0, 1, 2, 0, 1, 2, 0, 1, 3  ,
0, 0, 1, 0, 0, 1, 0, 0, 2  ,
0, 0, 0, 0, 0, 0, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0     ,
  0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 0, 0, 0, 0, 0, 0  ,
2, 0, 0, 1, 0, 0, 1, 0, 0  ,
2, 0, 0, 1, 0, 0, 1, 0, 0  ,
1, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 2, 0, 0, 1, 0, 0, 1  ,
0, 0, 2, 0, 0, 1, 0, 0, 1  ,
0, 0, 1, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 1, 0, 0, 1, 0, 0  ,
1, 0, 0, 1, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 1, 0, 0, 1  ,
0, 0, 1, 0, 0, 1, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 1, 0, 0  ,
1, 0, 0, 1, 0, 0, 2, 0, 0  ,
1, 0, 0, 1, 0, 0, 2, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 1  ,
0, 0, 1, 0, 0, 1, 0, 0, 2  ,
0, 0, 1, 0, 0, 1, 0, 0, 2  ,
0, 0, 0, 0, 0, 0, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0     ,
  0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 0, 0, 0, 0, 0, 0  ,
2, 0, 0, 1, 0, 0, 1, 0, 0  ,
3, 1, 0, 2, 1, 0, 2, 1, 0  ,
1, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0  ,
1, 2, 0, 1, 1, 0, 1, 1, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 1, 0, 0, 1, 0, 0  ,
2, 1, 0, 2, 1, 0, 2, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 1, 0, 1, 1, 0, 1, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 1, 0, 0  ,
0, 0, 0, 0, 0, 0, 1, 0, 0  ,
1, 0, 0, 1, 0, 0, 2, 0, 0  ,
2, 1, 0, 2, 1, 0, 3, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 1, 0  ,
0, 0, 0, 0, 0, 0, 0, 1, 0  ,
1, 1, 0, 1, 1, 0, 1, 2, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0     ,
  0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 0, 0, 0, 0, 0, 0  ,
2, 0, 0, 1, 0, 0, 0, 0, 0  ,
2, 0, 0, 1, 0, 0, 0, 0, 0  ,
2, 0, 0, 1, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0  ,
0, 3, 1, 0, 2, 1, 0, 1, 1  ,
0, 2, 0, 0, 1, 0, 0, 0, 0  ,
0, 2, 0, 0, 1, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 0, 0, 0, 0  ,
0, 1, 4, 0, 1, 3, 0, 1, 2  ,
0, 0, 3, 0, 0, 2, 0, 0, 1  ,
0, 0, 2, 0, 0, 1, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 1, 0, 0, 0, 0, 0  ,
1, 0, 0, 1, 0, 0, 0, 0, 0  ,
1, 0, 0, 1, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 2, 1, 0, 2, 1, 0, 1, 1  ,
0, 1, 0, 0, 1, 0, 0, 0, 0  ,
0, 1, 0, 0, 1, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 3, 0, 1, 3, 0, 1, 2  ,
0, 0, 2, 0, 0, 2, 0, 0, 1  ,
0, 0, 1, 0, 0, 1, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 1, 0, 1, 1, 0, 1, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 2, 0, 1, 2, 0, 1, 2  ,
0, 0, 1, 0, 0, 1, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 0     ,
  0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 0, 0, 0, 0, 0, 0  ,
2, 0, 0, 1, 0, 0, 0, 0, 0  ,
3, 0, 0, 2, 0, 0, 1, 0, 0  ,
3, 0, 0, 2, 0, 0, 1, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0  ,
0, 2, 0, 0, 1, 0, 0, 0, 0  ,
0, 2, 0, 0, 1, 0, 0, 0, 0  ,
0, 2, 0, 0, 1, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 0, 0, 0, 0  ,
0, 0, 3, 0, 0, 2, 0, 0, 1  ,
0, 0, 3, 0, 0, 2, 0, 0, 1  ,
0, 0, 2, 0, 0, 1, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 1, 0, 0, 0, 0, 0  ,
2, 0, 0, 2, 0, 0, 1, 0, 0  ,
2, 0, 0, 2, 0, 0, 1, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 1, 0, 0, 0, 0  ,
0, 1, 0, 0, 1, 0, 0, 0, 0  ,
0, 1, 0, 0, 1, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 2, 0, 0, 2, 0, 0, 1  ,
0, 0, 2, 0, 0, 2, 0, 0, 1  ,
0, 0, 1, 0, 0, 1, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 1, 0, 0, 1, 0, 0  ,
1, 0, 0, 1, 0, 0, 1, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 1, 0, 0, 1  ,
0, 0, 1, 0, 0, 1, 0, 0, 1  ,
0, 0, 0, 0, 0, 0, 0, 0, 0     ,
  0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 0, 0, 0, 0, 0, 0  ,
2, 0, 0, 1, 0, 0, 0, 0, 0  ,
3, 0, 0, 2, 0, 0, 1, 0, 0  ,
4, 1, 0, 3, 1, 0, 2, 1, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 0, 0, 0, 0, 0  ,
0, 2, 0, 0, 1, 0, 0, 0, 0  ,
0, 2, 0, 0, 1, 0, 0, 0, 0  ,
1, 3, 0, 1, 2, 0, 1, 1, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 0, 0, 0, 0  ,
0, 0, 2, 0, 0, 1, 0, 0, 0  ,
0, 0, 2, 0, 0, 1, 0, 0, 0  ,
0, 0, 2, 0, 0, 1, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 1, 0, 0, 0, 0, 0  ,
2, 0, 0, 2, 0, 0, 1, 0, 0  ,
3, 1, 0, 3, 1, 0, 2, 1, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 1, 0, 0, 1, 0, 0, 0, 0  ,
0, 1, 0, 0, 1, 0, 0, 0, 0  ,
1, 2, 0, 1, 2, 0, 1, 1, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 1, 0, 0, 1, 0, 0, 0  ,
0, 0, 1, 0, 0, 1, 0, 0, 0  ,
0, 0, 1, 0, 0, 1, 0, 0, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 0, 0, 1, 0, 0, 1, 0, 0  ,
2, 1, 0, 2, 1, 0, 2, 1, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
1, 1, 0, 1, 1, 0, 1, 1, 0    ,
 0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0  ,
0, 0, 0, 0, 0, 0, 0, 0, 0     ,
};
 memcpy(gamma,shared,sizeof(shared));
    }

    //从i到j，和从p到q 两条路径的冲突
    for(int i=0; i<meshfactor*meshfactor; i++)
    {
        for(int j=0; j<meshfactor*meshfactor; j++)
        {
            for(int p=0; p<meshfactor*meshfactor; p++)
            {
                for(int q=0; q<meshfactor*meshfactor; q++)
                {

//                    gamma [i] [j] [p] [q]=ox+oy;
                    if(D[i][j]==0||D[p][q]==0){
                    	pc[i][j][p][q]=0;
					}
					else{
						pc[i][j][p][q]=gamma[i][j][p][q]*1.0/(D[i][j]*D[p][q]);
					}

//                    printf("%lf\n",pc[i][j][p][q]);
                }
            }

        }
    }
}

//Main Process
void solve()
{
    double factor_construction=1.0;
//    for(int i=0; i<meshfactor*meshfactor; i++)
//    {
//        Rdk[i]=240;
//    }
//    scanf("%d%d", &pop, &gen);
    compute_shared_path();
//distance between pi and pj
//    for(int i=0;i<meshfactor*meshfactor;i++){
//        for(int j=0;j<meshfactor*meshfactor;j++){
//
//            //printf("%d ",D[i][j]);
//        }
//    }
//读文件
    scanf("%d", &mycycle);
    scanf("%d", &n);
    printf("m = %d n = %d\n", meshfactor*meshfactor, n);
    printf("pop = %d gen = %d\n", pop, gen);
    //所有任务在不同机器上执行时间不同
    for(int i=0; i<n; i++)
    {
        scanf("%lf",&t[0][i]);
    }
    for(int j=1; j<meshfactor*meshfactor; j++)
    {
        if(j%2==0)
        {
            factor_construction=1.0;
            Rdk[j]=10;
            Rik[j]=3;
        }
        else if(j%2==1)
        {
            factor_construction=2.0;
            Rdk[j]=20;
            Rik[j]=6;
        }
        for(int i=0; i<n; i++)
        {
            t[j][i]=t[0][i]/factor_construction;
            //scanf("%lf",&t[j][i]);
            //printf("%lf ",t[j][i]);
        }
    }
    for(int i=0; i<n; i++)
    {
        for(int j=0; j<cycle; j++)
        {
            isdep[j][i]=0;//依赖任务i的个数
            todep[j][i]=0;//i依赖的任务数
        }

    }
    for(int i = 0 ; i < n ; i ++)
    {
        for(int j = 0 ; j < n ; j ++)
        {
            scanf("%lf", &c[i][j]);
            if(c[i][j]>0)
            {
                todep[0][i]++;
                isdep[0][j]++;
            }
        }
    }


//    for(int i = 0 ; i < n ; i ++)
//    {
//        for(int j = 0 ; j < n ; j ++)
//        {
//            if(c[i][j]>0)
//            {
//                todep[0][i]++;
//                isdep[0][j]++;
//            }
//        }
//    }
    for(int i=1; i<cycle; i++)
    {
        for(int j=0; j<n; j++)
        {
            todep[i][j]=todep[0][j];
            isdep[i][j]=isdep[0][j];
        }
    }

    int t = 0;
    printf("init...begin\n");
    init();
    //greedy_with_topo();
    printf("init...done\n");

    while(exe_time < time_limit)
    {
        printf("*****************************t=%d*****************************\n", t);
        int P_size = 0;
        int now_rank = 1;

        make_new_pop(Collection, pop);
        for(int i = 0 ; i < pop*2 ; i ++)
        {
            evaluate_objective(&Collection[i]);
        }
        non_domination_sort(Collection, pop * 2, true);//用正常的非支配关系
        for(vector<Individual>::iterator iter = Front[1].begin(); iter != Front[1].end(); ++ iter)
        {
            updateElistCollection(&(*iter)); // 更新精英种群
        }

        while(1)
        {
            if(P_size + Front[now_rank].size() > pop)
            {
                break;
            }
            for(vector<Individual>::iterator iter = Front[now_rank].begin(); iter != Front[now_rank].end(); ++ iter)
            {
                Collection[P_size] = (*iter);
                P_size ++;
                printf("insert to Collection\n");
            }
            now_rank ++;
        }
        crowdDistance(now_rank);
        while(1)
        {
            if(P_size > pop)
            {
                break;
            }
            for(vector<Individual>::iterator iter = Front[now_rank].begin(); iter != Front[now_rank].end(); ++ iter)
            {
                Collection[P_size] = (*iter);
                P_size ++;
            }
        }
        t ++;
        finish = clock();
        exe_time=(double)(finish - start) / CLOCKS_PER_SEC;

        printf("%d generation time: %.2f s\n", t,exe_time);
//	for(int i = 0 ; i < ElistCollection.size() ; i ++)
//        {
//    //        if(Collection[i].front == 1)
//    //        {
//                printf("[");
//                printf("%.2lf,", ElistCollection[i].makespan);
//                printf("%.2lf", ElistCollection[i].workload);
//                printf("],");
//                printf("\n");
//    //        }
//        }
    }

    non_domination_sort(Collection, pop * 2, true);
    vector<int>:: iterator iter;
    int tot = 0;
    double tempCE=0,tempIE=0,tempSE=0;
    double tempCT=0,tempIT=0,tempST=0;
    for(int i = 0 ; i < ElistCollection.size() ; i ++)
    {
//        if(Collection[i].front == 1)
//        {
        printf("[");
        printf("%.2lf,", ElistCollection[i].makespan);
        printf("%.2lf,", ElistCollection[i].p_contention);
        printf("%.2lf", ElistCollection[i].energy);
        printf("],");
        printf("\n");
        int _m = 0;
        for(int j = 0; j < m; j ++) {
            if(ElistCollection[i].mesh[j]) {
                _m ++;
            }
        }
        tempCE+=ElistCollection[i].Ed/ElistCollection[i].energy;
        tempIE+=ElistCollection[i].Ei/ElistCollection[i].energy;
        //tempSE+=ElistCollection[i].Es/ElistCollection[i].energy;
        tempCT+=ElistCollection[i].comtime/(ElistCollection[i].makespan*_m);
        tempIT+=ElistCollection[i].idltime/(ElistCollection[i].makespan*_m);
        //tempST+=ElistCollection[i].sleeptime/(ElistCollection[i].makespan*m);


        printf("computation energy ratio: %lf, idle energy ratio: %lf, sleep energy ratio: %lf\n",ElistCollection[i].Ed/ElistCollection[i].energy,ElistCollection[i].Ei/ElistCollection[i].energy,ElistCollection[i].Es/ElistCollection[i].energy);
        printf("computation time ratio: %lf, idle time ratio: %lf, sleep time ratio: %lf\n",ElistCollection[i].comtime/(ElistCollection[i].makespan*_m),ElistCollection[i].idltime/(ElistCollection[i].makespan*_m),ElistCollection[i].sleeptime/(ElistCollection[i].makespan*_m));

        tot ++;

        for(int j = 0 ; j < m ; j ++)
        {
            printf("第%d个机器\n", j);
            for(int k = 0; k < ElistCollection[i].machine[j].size(); k ++)
            {
                printf("%d ", ElistCollection[i].machine[j][k]);
            }
            printf("\n");
        }
//        }
    }
    tempCE=tempCE/ElistCollection.size();
    tempIE=tempIE/ElistCollection.size();
    //tempSE=tempSE/ElistCollection.size();
    tempCT=tempCT/ElistCollection.size();
    tempIT=tempIT/ElistCollection.size();
    //tempST=tempST/ElistCollection.size();
    printf("AVERAGE: computation energy ratio: %lf, idle energy ratio: %lf, \n",tempCE,tempIE);
    printf("AVERAGE: computation time ratio: %lf, idle time ratio: %lf,\n",tempCT,tempIT);

    printf("x=[");
    for(int i = 0 ; i < ElistCollection.size() ; i ++)
    {
//        if(Collection[i].front == 1)
//        {

        printf("%.2lf ", ElistCollection[i].makespan);

        tot ++;
//        }
    }
    printf("];");
    printf("\n");
    printf("y=[");
    for(int i = 0 ; i < ElistCollection.size() ; i ++)
    {
//        if(Collection[i].front == 1)
//        {

        printf("%.2lf ", ElistCollection[i].p_contention);


//        }
    }
    printf("];");
    printf("\n");
    printf("z=[");
    for(int i = 0 ; i < ElistCollection.size() ; i ++)
    {
//        if(Collection[i].front == 1)
//        {

        printf("%.2lf ", ElistCollection[i].energy);


//        }
    }
    printf("];");
    printf("\n");
    printf("tot = %d\n", tot);
}

int main(int argc, char **argv)
{
//int main(){
    char outPutFile[100];
    char testcase[100];
    char *fileName;
    int myRand;
    strcpy(testcase, argv[1]);
    strtok(strtok(argv[1], "."), "/");
    strcpy(outPutFile, fileName = strtok(NULL, "/"));
    strcat(outPutFile, "/");
    strcat(outPutFile, fileName);
    strcat(outPutFile, "-");
    strcat(outPutFile, argv[2]);
    myRand = atoi(argv[2]);
    strcat(outPutFile, "-");
    strcat(outPutFile, argv[3]);
    pop = atoi(argv[3]);
    strcat(outPutFile, "-");
    strcat(outPutFile, argv[4]);
    strcat(outPutFile, "-MOHA-3object-MACHINE");

    gen = atoi(argv[4]);
    m = atoi(argv[5]);
    strcat(outPutFile, argv[5]);
    srand(myRand);
    strcat(outPutFile, "-");

    time_limit = atoi(argv[6]);
    strcat(outPutFile, argv[6]);
    strcat(outPutFile, "s");
    strcat(outPutFile, "-RAND");
    strcat(outPutFile, argv[2]);
    strcat(outPutFile, ".txt");
    freopen(testcase, "r", stdin);
    freopen("test1.txt", "w", stdout);
//    freopen(outPutFile, "w", stdout);
    printf("%s\n", outPutFile);
//    printf("%s\n", outPutFile);
    start = clock();
//    start_time = start.tms_utime + start.tms_stime;

    solve();

//	double finish_time = double(finish.tms_utime - start.tms_utime + finish.tms_stime - start.tms_stime)/sysconf(_SC_CLK_TCK);
//	finish_time = round(finish_time * 100)/100.0;
    finish = clock();
    exe_time=(double)(finish - start) / CLOCKS_PER_SEC;

    printf("total time: %.2f s\n", exe_time);
//    srand(3);
////    freopen("testcase/TMNR.dat", "r", stdin);
//    freopen("testcase/h264_14.dat", "r", stdin);
//    solve();

    return 0;
}
