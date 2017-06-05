/*********************************************
 * OPL 12.6.0.0 Model
 * Author: Rj Yan
 * Creation Date: 2017-4-24
 *
*********************************************/

 int NbProcs = ...;
 int NbTasks = ...;
 int Cycles = ...;

// size of NoC
 int xN = ...;
 int yN = ...;

 range Procs = 1..NbProcs;
 range Tasks = 1..NbTasks;
 range Cycle = 1..Cycles;


 int Time[Tasks] = ...;
 int comm[Tasks][Tasks] = ...;
 int Dep[Tasks][Tasks] = ...;
 int shared[Procs][Procs][Procs][Procs]=...;

/*MPPA-256 NOC*/
 int link=7;
 int rout=8;
////////////////
 int delay = 8;
int elink= 1;
int erout = 4;

 /* the speed of processors*/
 int Freq[Procs]=...;
 int dPk[Procs]=...;
 int sPk[Procs]=...;

 /* the maximal load of every processors*/
 int maxP = 3;

 /* the location of processors*/
 int xP[Procs]=...;
 int yP[Procs]=...;

// int Ack[Tasks][Procs] = ...;
 int Max = 100000;

//modified by YRJ in Sep. 2, 2016
float w1=0.999;
float w2=0.001;


/**------------------varaibles -------------------------*/
/*mapping relation between tasks and processors*/
dvar boolean Map[Tasks][Procs];
/*load of every processor*/


/*whehter communicaiton exists between two tasks*/
dvar boolean o[Tasks][Tasks];

/*whether the two tasks are mapped to the same processor*/
dvar boolean b[Tasks][Tasks];

/*the exact mapping of tasks on a processor*/
dvar boolean bp[Procs][Tasks][Tasks];

/*the execution sequence between tasks on the same processor*/
dvar boolean q[Procs][Tasks][Tasks];
dvar int dis[Tasks][Tasks];

dvar int Load[Procs];
//dvar float pro[Tasks][Tasks][Tasks][Tasks];

/*the execution time of a task on different cycles */
dvar int tao[Cycle][Tasks];
dvar int fin[Cycle][Tasks];
dvar int se[Cycle][Tasks][Tasks];
dvar int fe[Cycle][Tasks][Tasks];
dvar boolean conflict[Tasks][Tasks][Tasks][Tasks];

/*the execution time for the last task in the last cycle*/
dvar int MP;
dvar int En;
//minimize E;
minimize w1*MP+w2*En;
//minimize sum(u in Cycle, i in Tasks)tao[u][i];
//minimize (sum(u in Cycles)sum(i in Tasks)tao[u][i]);
/*minimize w1*E+w2*(sum(k in Procs)abs(Load[k]/Avg-1));

*minimize the total execution cost
*
*/
/*minimize the load balance
 *minimize (sum(k in Procs)abs(Load[k]/Avg-1));
*/
 subject to {

    /*for objective optimization*/
    forall(k in Procs){
        Load[k]== (sum(i in Tasks) Time[i]*Map[i][k])/Freq[k];
    }

    En == sum(k in Procs)(dPk[k]*Load[k]+sPk[k]*(MP-Load[k])*Cycles);

    /*forall(i,j in Tasks)
        pro[i][i][j][j]== 0;


    forall(i,j,l,r in Tasks, k1,k2,k3,k4 in Procs:i!=j && l!=r){
        if (shared[k1][k2][k3][k4]>=1){

            (dis[i][j]==0)+(dis[l][r]==0)+(Map[i][k1]==0)+(Map[j][k2]==0) + (Map[l][k3]==0) + (Map[r][k4]==0)+(pro[i][j][l][r]== shared[k1][k2][k3][k4])>=1;
            (dis[i][j]>=1 && dis[l][r]>=1)+(Map[i][k1]==0)+(Map[j][k2]==0) + (Map[l][k3]==0) + (Map[r][k4]==0)+(pro[i][j][l][r]== 0)>=1;

        }
    }*/

    /*every task can only be mapped to one processor*/
    forall(i in Tasks)
      ct1:
      sum(k in Procs)
        Map[i][k]==1;

    /*every processor has at least one task*/
    forall(k in Procs)
      ct2:
     {
      sum(i in Tasks)
        Map[i][k]>=1;
      sum(i in Tasks)
        Map[i][k]<=maxP;
     }
    /*every mapping should be legal*/
    /*
    forall(i in Tasks, k in Procs)
      ct3:
        Map[i][k] <= Ack[i][k];
    */


    /*whether tasks are on the same processor*/
    forall(i in Tasks)
        ct50:
        b[i][i]==0;
    forall(i,j in Tasks: i!=j)
        ct51:
        b[i][j]==1-(sum(k in Procs)(abs(Map[i][k]-Map[j][k])))/2;

    /*tasks are on which processor*/
    forall(i,j in Tasks, k in Procs: i!=j)
        ct60:
        bp[k][i][j] <= (Map[i][k] + Map[j][k])/2;

    forall(i,j in Tasks)
        ct61:
        b[i][j] == sum(k in Procs)bp[k][i][j];


    /*whether two tasks have communication cost*/
    forall(i,j in Tasks: i!=j)
      ct7:
        {
        //o[i][j]==(Dep[i][j]-b[i][j]+1) div 2;
        o[i][j] >= Dep[i][j] - b[i][j] ;
        o[i][j] <= Dep[i][j];
        (b[i][j]==0)+(Dep[i][j]==0)+ (o[i][j]==0)>=1;
        }

        //

    /*the execution sequence on every processor*/
    forall(i,j in Tasks, k,l in Procs: k!=l){
        ct80:
            q[k][i][i] == 0;
            (q[k][i][j]==1) + (q[l][i][j]==1) <=1;
    }
    forall(i,j in Tasks,k in Procs:i!=j){
        ct81:
            (sum(i,j in Tasks)(bp[k][i][j]))/2==sum(i,j in Tasks)(q[k][i][j]);
            q[k][i][j]+q[k][j][i]>=bp[k][i][j];
    }
    forall(i,j,l in Tasks,k in Procs:i!=j && j!=l){
        ct82:
            q[k][i][j]*q[k][j][l]<=q[k][i][l];
    }

    /*conflict calculation*/
    forall(i,j,l,r in Tasks,k1,k2,k3,k4 in Procs: i!=j &&l!=r)
    {
        ct9:

        conflict[i][i][i][i]==0;
        conflict[i][i][l][l]==0;
        (o[i][j]==1)+(conflict[i][j][l][r]==0)>=1;
        (o[l][r]==1)+(conflict[i][j][l][r]==0)>=1;

        (o[i][j]==0)+(o[l][r]==0)+(Map[i][k1]==0)+(Map[j][k2]==0) + (Map[l][k3]==0) + (Map[r][k4]==0)+(shared[k1][k2][k3][k4]==0) +(conflict[i][j][l][r]==1)>=1;

        (o[i][j]==0)+(o[l][r]==0)+(Map[i][k1]==0)+(Map[j][k2]==0) + (Map[l][k3]==0) + (Map[r][k4]==0)+(shared[k1][k2][k3][k4]>=1) +(conflict[i][j][l][r]==0)>=1;

    }

    /* the distance between i and j*/
    forall(i,j in Tasks, u in Cycle: i!=j)

        ct10:
        {
        dis[i][j]>=0;
        dis[i][j]<=xN+yN-2;
        //dis[i][j]>=sum(k1,k2 in Procs)(Map[i][k1]+Map[j][k2]-1)* (abs(xP[k1]-xP[k2])+abs(yP[k1]-yP[k2])) ;
        dis[i][j]>=sum(k1,k2 in Procs)Map[i][k1]*Map[j][k2]* (abs(xP[k1]-xP[k2])+abs(yP[k1]-yP[k2]));
        dis[i][j]<=sum(k1,k2 in Procs)Map[i][k1]*Map[j][k2]* (abs(xP[k1]-xP[k2])+abs(yP[k1]-yP[k2]));
    }


    ////////////////////////
    forall(i,j in Tasks, u in Cycle)
        s0:
        {
            tao[u][i]>=0;
            se[u][i][j]>=0;
            fe[u][i][j]>=0;
            dis[i][i]>=0;
        }
    ////////////////////////////////////////////////////////////
    /*the execution time*/
    forall(i in Tasks, u in Cycle)
        eq0:
        fin[u][i] == tao[u][i] + sum(k in Procs)(Map[i][k]*Time[i]/Freq[k]);

    forall(i,j in Tasks, u in Cycle)
        eq1:
        if (Dep[i][j]==1){
            fin[u][i] <= se[u][i][j] ;
            fe[u][i][j]<= tao[u][j];}

    /*forall(i,j in Tasks, k1,k2 in Procs: i!=j)
    {
        disk[i][k1][j][k2]>=0;
        disk[i][k1][j][k2]>=Map[i][k1]+Map[j][k2]-1;
    }*/

    /*forall(i in Tasks, u in Cycle){
        se[u][i][i]==fe[u][i][i]==fin[u][i];
    }*/

    /*the cost spent for tranmission*/
    forall(i,j in Tasks, u in Cycle)
        eq3:
        {
            if (comm[i][j]==0){
                se[u][i][j]==0;
                fe[u][i][j]==0;
            }
            else
                se[u][i][j]+comm[i][j]*dis[i][j]*link+(dis[i][j]+1)*rout<=fe[u][i][j];
            //(o[i][j]==0) + (se[u][i][j] + comm[i][j]*(dis[i][j]*link+(dis[i][j]+1)*rout)-fe[u][i][j]<=0)>=1;
            //(o[i][j]==1) + (se[u][i][j] -fe[u][i][j]==0)>=1;
        }

    /*the total cost is larger than the last execution of the last task*/
    forall(i in Tasks)
      s1:
        MP>=tao[Cycles][i] + sum(k in Procs)(Map[i][k]*Time[i]);


    /*the execution sequence in the same processor*/
    //modified by YRJ in Sep. 2, 2016
    forall(i,j in Tasks, u in Cycle, k in Procs: i!=j)
        s3:
            fin[u][i] <= tao[u][j] + Max* (1-q[k][i][j]) ;

    /*the same task on different cycles*/
    //modified by YRJ in Sep. 2, 2016
    forall(i in Tasks,u,v in Cycle){
        s4:
        if(u<v)
        fin[u][i] <= tao[v][i];
    }

    /*the execution of a task in later cycles should be later than the last executed task in earlier cycles*/
    //modified by YRJ in Sep. 2, 2016
    forall(i,j in Tasks,u,v in Cycle,k in Procs){
      s5:
        if(u<v)
            fin[u][j] <= tao[v][i] + Max*(1-q[k][i][j]);
    }


    /*two tasks on the same processor cannot overlap*/
    forall(i,j in Tasks,u,v in Cycle){
        s6:
        (b[i][j]==0) + (tao[u][j]- fin[v][i]>= 0) + (tao[v][i]-fin[u][j]>=0 ) >=1;
    }

    /*two transfer from the same source and occupying the same link should be sequentical*/
    forall(i,j,l in Tasks,u in Cycle: j!=l)
        s7:
        (conflict[i][j][i][l]==0)+(abs(se[u][i][j]-se[u][i][l])-delay>=0)>=1;


    /*two data transfer on the same resource cannot overlap*/
    forall(i,j,l,r in Tasks, u,v in Cycle:i!=l ||j!=r){
    s8:

        (conflict[i][j][l][r]==0)+(abs(se[u][i][j]-se[u][i][l])>=delay) + (se[u][i][j]- fe[v][l][r]>= 0) + (se[v][l][r]-fe[u][i][j]>=0 ) >=1;

    }

}


execute{
    var ofile = new IloOplOutputFile("modelRun.txt");
    ofile.writeln("Mapping:");
    for(var k in thisOplModel.Procs){
        for(var i in thisOplModel.Tasks){
            if (thisOplModel.Map[i][k]==1)
                ofile.write(" m["+i+"]["+k+"]="+thisOplModel.Map[i][k]);
        }
        ofile.writeln();
    }

    for(var i in thisOplModel.Tasks)
        for(var j in thisOplModel.Tasks)
            for(var l in thisOplModel.Tasks)
                for(var r in thisOplModel.Tasks){
                    if(thisOplModel.conflict[i][j][l][r]==1)
                        ofile.writeln(" conflict["+i+"]["+j+"]["+l+"]["+r+"]="+thisOplModel.conflict[i][j][l][r]);
    }

    for(var i in thisOplModel.Procs)
        for(var j in thisOplModel.Procs)
            for(var l in thisOplModel.Procs)
                for(var r in thisOplModel.Procs){
                    if(thisOplModel.shared[i][j][l][r]>0)
                        ofile.writeln(" shared["+i+"]["+j+"]["+l+"]["+r+"]="+thisOplModel.shared[i][j][l][r]);
    }



    for(var u in thisOplModel.Cycle){
        for(var i in thisOplModel.Tasks){

            ofile.write(" tao["+u+"]["+i+"]="+thisOplModel.tao[u][i]);
        }
        ofile.writeln();
    }
    for(var k in thisOplModel.Procs){
        for(var i in thisOplModel.Tasks)
            for(var j in thisOplModel.Tasks){
                if (thisOplModel.q[k][i][j]==1)
                    ofile.write(" q["+k+"]["+i+"][" + j + "]="+thisOplModel.q[k][i][j]);
            }
        ofile.writeln();
    }

        ofile.close();
}