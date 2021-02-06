#include <iostream>
#include <string>
#include <ctime>
#include <random>
#include <vector>
#include "define.hpp"
#include "Galois.hpp"
#include "Polynomial.hpp"
using namespace std;
int get_weight(Code c){
    int cnt=0;
    while(c){
        c=c&(c-1);
        cnt++;
    }
    return cnt;
}

double* new_BPSK(CPolynomial in,int symbols,int block){
    double *data=new double[symbols*block];
    int x=0;
    for(int i=0;i<symbols;i++){
        for(int j=0;j<block;j++){
            if((in[i].getNum() >> j)&1) data[x]=-1;
            else    data[x]=1;
            x++;
        }
    }
    return data;
}

CPolynomial de_BPSK(double *in,int symbols,int block){
    CPolynomial data;
    int x=0;
    for(int i=0;i<symbols;i++){
        Code a=0;
        for(int j=0;j<block;j++){
            if(in[x]<0) a=a | (1ull<<j);
            x++;
        }
        data[i]=a;
    }
    return data;
}

void AWGN(double *message,int size,double _r){
    static std::default_random_engine generator = std::default_random_engine( time(NULL) );
    double sigma = sqrt((pow(10,(-(_r/10))))/2);
    std::normal_distribution<float> norm(0.0, sigma);
    for(int i=0;i<size;i++){
        message[i]+=norm(generator);
    }
    //double x = norm(generator);
}

CPolynomial generateGX(int t,int b=0,CGalois a=2){
    CPolynomial GXPT;GXPT[0]=1;
    CGalois m=a^b;
    for(int i=b;i<(t*2)+b;i++){
        CPolynomial MT;MT[0] = m;MT[1] = 1;
        GXPT=GXPT*MT;
        m=m*a;
    }
    return GXPT;
}

CPolynomial Euclidean_Algorithm(CPolynomial &R){
    CGalois Si[T*2+1];
    for(int i=0;i<T*2+1;i++){
        Si[i]=R.inputx(1ull<<i);
    }
    bool ckerr=true;
    for(int i=1;i<=T*2;i++){
        if(Si[i]!=0){
            ckerr=false;
            break;
        }
    }
    if(ckerr)
        return R;
    CPolynomial S;
    for(int i=0;i<2*T;i++)
        S[i]=Si[i+1];
    CPolynomial r_n1;r_n1[2*T]=1;
    CPolynomial r_0=S;
    CPolynomial t_n1;
    CPolynomial t_0;t_0[0]=1;
    while(r_0.get_max()>=T){
        CPolynomial q=r_n1/r_0;
        CPolynomial r_i=r_n1+(r_0*q);
        CPolynomial t_i=t_n1+(t_0*q);
        r_n1=r_0; r_0=r_i;
        t_n1=t_0; t_0=t_i;
    }
    CPolynomial Lambda_=t_0.differential();
    CPolynomial E;
    CGalois a=1;
    for(int i=0;i<MASK;i++,a=a*2){
        if(t_0.inputx(a)==0){
            int errorloc=(MASK-i)%MASK;
            CGalois errorvalue=r_0.inputx(a)/Lambda_.inputx(a);
            //cout<<"error localtion is "<<errorloc<<",error value is "<<errorvalue<<endl;
            E[errorloc]=errorvalue;
        }
    }
#ifdef DEBUG
    cout<<"Euclidean Algorithm."<<endl;
    for(int i=0;i<T*2+1;i++){
        cout<<"S"<<i<<"="<<Si[i]<<" ";
    }cout<<endl;
    cout<<"S(x)="<<S<<endl;
    cout<<"A(x)="<<t_0<<endl;
    cout<<"O(x)="<<r_0<<endl;
    cout<<"A'(x)="<<Lambda_<<endl;
    cout<<"DE(x)="<<E<<endl;
#endif
    return R+E;
}

CPolynomial Berlekamp_Massey(CPolynomial &R,bool* pass=NULL){
    CGalois Si[T*2+1];
    for(int i=0;i<T*2+1;i++){
        Si[i]=R.inputx(1ull<<i);
    }
    bool ckerr=true;
    for(int i=1;i<=T*2;i++){
        if(Si[i]!=0){
            ckerr=false;
            break;
        }
    }
    if(pass) *pass=true;
    if(ckerr)
        return R;
    CPolynomial Lambda;Lambda[0]=1;//A(x)=1
    Code Lu=0;
    CPolynomial B;B[0]=1;
    for(int u=0;u<=2*T-1;u++){
         CGalois du=Si[u+1];
         for(int i=u,j=1;i>=u-Lu+1;i--,j++){
             du=du+Lambda[j]*Si[i];
         }
         if(du==0){
             B=B<<1;
         }else if(2*Lu>u){//du!=0
            Lambda=Lambda+(B<<1)*du;
            B=B<<1;
         }else{//du!=0 and 2*Lu<=u
            CPolynomial Lam=Lambda;
            Lambda=Lambda+(B<<1)*du;
            Lu=u+1-Lu;
            B=Lam*(du^-1);
         }
    }
    CPolynomial S;
    S[0]=1;
    for(int i=0;i<2*T;i++)
        S[i]=Si[i+1];
    CPolynomial keyequation;
    keyequation[0]=1;
    keyequation=Lambda*S%(keyequation<<(2*T));
    CPolynomial Lambda_=Lambda.differential();
    //Chien's search
    CPolynomial E;
    CGalois a=1;
    for(int i=0;i<MASK;i++,a=a*2){
        if(Lambda.inputx(a)==0){
            int errorloc=(MASK-i)%MASK;
            CGalois errorvalue=keyequation.inputx(a)/Lambda_.inputx(a);
            //cout<<"error localtion is "<<errorloc<<",error value is "<<errorvalue<<endl;
            E[errorloc]=errorvalue;
        }
    }
#ifdef DEBUG
    cout<<"Berlekamp Massey"<<endl;
    for(int i=0;i<T*2+1;i++){
        cout<<"S"<<i<<"="<<Si[i]<<" ";
    }cout<<endl;
    cout<<"S(x)="<<S<<endl;
    cout<<"A(x)="<<Lambda<<endl;
    cout<<"O(x)="<<keyequation<<endl;
    cout<<"A'(x)="<<Lambda_<<endl;
    cout<<"DE(x)="<<E<<endl;
#endif
    if(pass){
        if(E.empty()) *pass=false;
    }
    return R+E;
}

CPolynomial getMessage(int n){
    CPolynomial M;
    for(int i=0;i<n;i++){
        M[i]=rand()%(MASK+1);
    }
    return M;
}

CPolynomial getNose(int n){
    CPolynomial E;
    for(int i=0;i<n;i++){
        int randindex=rand()%MASK;
        if(E[randindex]==0)
            E[randindex]=rand()%(MASK+1);
        else
            i--;
    }
    return E;
}

double Euclidean_distance(double *A,double *B,int n){
    double d=0;
    for(int i=0;i<n;i++){
        double x=A[i]-B[i];
        d=d+(x*x);
    }
    return d;
}

CPolynomial Efficient_Chase2(CPolynomial &R,double *y){
    vector<CPolynomial> all_dc;
    bool pass=false;
    CPolynomial Algebraic = Berlekamp_Massey(R,&pass);
    if(pass) all_dc.push_back(Algebraic);

    double SYM_Y[15];
    for(int i=0;i<15;i++){
        SYM_Y[i]=ABS(y[i*4]);
        for(int j=1;j<4;j++){
            double x=ABS(y[i*4+j]);
            if(SYM_Y[i]>x) SYM_Y[i]=x;
        }
    }
    int index[T];
    index[0]=0;
    for(int i=1;i<T;i++) index[i]=-1;
    for(int i=1;i<15;i++){
        if(SYM_Y[i] < SYM_Y[index[0]]){
            for(int j=T-1;j>0;j--) index[j]=index[j-1];
            index[0]=i;
        }else{
            for(int z=1;z < T;z++){
                if(index[z]==-1 || (SYM_Y[i] < SYM_Y[index[z]])){
                    for(int j=T-1;j>z;j--) index[j]=index[j-1];
                    index[z]=i;
                    break;
                }
            }
        }
    }
    CPolynomial N;
    for(int i=0;i<=15;i++){
        N[index[2]]=i;
        for(int j=0;j<=15;j++){
            N[index[1]]=j;
            for(int k=0;k<=15;k++){
                N[index[0]]=k;
                CPolynomial RpN=R+N;
                bool ispass=false;
                for(vector<CPolynomial>::iterator it=all_dc.begin();it!=all_dc.end();it++){
                    if(it->distance(RpN)<=T){
                        ispass=true;
                        break;
                    }
                }
                if(ispass)
                    continue;
                CPolynomial ddc=Berlekamp_Massey(RpN,&ispass);
                if(ispass) all_dc.push_back(ddc);
            }
        }   
    }
    if(all_dc.size()==0) return R;
    CPolynomial minDC;
    double min=-1;
    for(vector<CPolynomial>::iterator it=all_dc.begin();it!=all_dc.end();it++){
        double *D=new_BPSK(*it,15,4);
        double Ed=Euclidean_distance(y,D,60);
        if(min==-1 || min > Ed){ 
            min=Ed;
            minDC=*it;
        }
        delete [] D;
    }
    return minDC;
}

int main(){
    srand(time(NULL));
    CPolynomial GXP=generateGX(T,1);//b=1
    int count=10000;
    double Noise=3;

    int allbit=0;
    int biterr1=0;
    int biterr2=0;
    for(int i=0;i<count;i++){
        system("clear");
        cout<<i<<endl;
        cout<<"G(x)="<<GXP<<endl;
        CPolynomial M=getMessage(9);//(marr,8);
        cout<<"m(x)="<<M<<endl;
        CPolynomial C=M<<(T*2);
        C=C+C%GXP;
        cout<<"c(x)="<<C<<endl;
        double *Y=new_BPSK(C,15,4);
        AWGN(Y,60,Noise);
        CPolynomial R=de_BPSK(Y,15,4);
        cout<<"r(x)="<<R<<endl;
        CPolynomial HDD=Berlekamp_Massey(R);
        cout<<"HDD(x)="<<HDD<<endl;
        CPolynomial EC2=Efficient_Chase2(R,Y);
        cout<<"EC2(x)="<<EC2<<endl;
        /*if(HDD!=EC2){
            string xxx;
            cin>>xxx;
        }*/
        delete [] Y;
        for(int i=0;i<15;i++){
            Code n=HDD[i].getNum()^C[i].getNum();
            //if(n!=0){
                biterr1+=get_weight(n);
            //}
            n=EC2[i].getNum()^C[i].getNum();
            //if(n!=0){
                biterr2+=get_weight(n);
            //}
        }
        allbit+=60;
    }
    cout<<"HDD BER:"<<(double)biterr1/allbit<<endl;
    cout<<"EC2 BER:"<<(double)biterr2/allbit<<endl;

    return 0;
}
/*
count = 10000
E/N=2
HDD BER:0.0159383
EC2 BER:0.0134883
E/N=3
HDD BER:0.00377333
EC2 BER:0.00251333
*/