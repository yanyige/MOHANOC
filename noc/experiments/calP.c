//gcc -Wall -g -o calP calP.c
//  calP.c
//  
//
//  Created by yrj on 25/4/17.
//
//
//#include <iostream>
//#include <windows.h>
#include <stdio.h>
//#include <windef.h>
//using namespace std;
const int Proc=4;
int xP[Proc]={0,1,0,1};
int yP[Proc]={0,0,1,1};

int min(int x,int y){
    if (x>y) {
        return y;
    }else
        return x;
}
int max(int x,int y){
    if (x>y) {
        return x;
    }else
        return y;
}
int main () {

    int shared[Proc][Proc][Proc][Proc];
    int tempX, tempY;
    int tempXX, tempYY;
    for(int k1=0;k1<Proc;k1++)
        for(int k2=0;k2<Proc;k2++)
            for(int k3=0;k3<Proc;k3++)
                for(int k4=0;k4<Proc;k4++){
                    tempX = (xP[k2]-xP[k1])+(xP[k4]-xP[k3])-(max(xP[k4],xP[k2])-min(xP[k3],xP[k1]));
                    tempXX = max(tempX,0);
                    tempY = (yP[k2]-yP[k1])+(yP[k4]-yP[k3])-(max(yP[k4],yP[k2])-min(yP[k3],yP[k1]));
                    tempYY = max(tempY,0);
                    if((tempX>=0 && tempY>=0) ||(k1==k3 || k1== k4 || k2==k3 || k2==k4))
                        shared[k1][k2][k3][k4]=tempXX+tempYY;
                    else
                        shared[k1][k2][k3][k4]=0;
                }
    
    printf("shared =[");
    for(int k1=0;k1<Proc;k1++){
        printf("[");
        for(int k2=0;k2<Proc;k2++){
            printf("[");
            for(int k3=0;k3<Proc;k3++){
                printf("[");
                for(int k4=0;k4<Proc;k4++){
                    if (k4==Proc-1) {
                        printf("%d] ",shared[k1][k2][k3][k4]);
                    }
                    else
                        printf("%d, ",shared[k1][k2][k3][k4]);
                    
                }
                
                if (k3==Proc-1) {
                    printf("] ");
                }
                else
                    printf(",\n");
            }
            if (k2==Proc-1)
                printf("],\n");
            else
                printf(",\n");
        }
    }
    printf("];\n");
    
    return 0;
}
