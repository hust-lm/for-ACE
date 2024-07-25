#include <iostream>
#include "/usr/local/include/pbc/pbc.h"
#include <map>
#include <cstring>
#include <cstdlib>
#include <set>
#include<vector>
using namespace std;

    static inline void pbc_pairing_init(pairing_t pairing, char* filename) 
    {  
        char param[1024];  
        FILE *fp;  
        unsigned int count;
        fp = fopen(filename, "r");  
        if (!fp){  
        printf("error opening %s", filename);  
        }  
        count = fread(param, 1, 1024, fp);  
        if (!count){  
        printf("input error");  
        }  
        fclose(fp);  
        pairing_init_set_buf(pairing, param, count); 
    }

    void matrix_gen(int v[],int lambda[],int omega[]){
        int matrix[5][4] = 
            {{1,1,0,0},
            {0,1,0,0},
            {1,0,1,1},
            {0,0,0,1},
            {0,0,1,0}
            };

        for(int i=0;i<5;i++){
            for(int j=0;j<4;j++){
                lambda[i]=lambda[i]+matrix[i][j]*v[j];
        }}
    }

    void setup_pp(element_t msk,element_t ha[],element_t g_alpha,element_t g_a,element_t g,element_t g_g,element_t alpha,element_t a,pairing_t pairing){
            element_init_GT(g_alpha, pairing);
            element_init_G1(g_a, pairing);
            element_init_G1(msk, pairing);
            element_random(g);
            pairing_apply(g_g,g,g,pairing);

            element_pow_zn(g_alpha,g_g,alpha);
            element_pow_zn(g_a,g,a);
            element_pow_zn(msk,g,alpha);


            for(int i=0;i<5;i++){
            element_init_G1(ha[i], pairing);
            element_random(ha[i]);
    }
    }

    void sign_setup(element_t p,element_t H,element_t X,element_t sign_v,element_t sign_V,pairing_t pairing){
            element_init_G1(p, pairing);
            element_init_G2(H, pairing);
            element_init_G1(X, pairing);
            element_init_Zr(sign_v, pairing);
            element_init_G2(sign_V, pairing);


            element_random(p);

            element_random(H);
            element_random(X);
            element_random(sign_v);

            element_pow_zn(sign_V,H,sign_v);
    }



    void encrypt(element_t M,element_t C,element_t C_0,element_t V[],element_t LAMBDA[],element_t C_L[],element_t D_L[],element_t r[],int v[],int lambda[],element_t alpha,element_t g_g,element_t ha[],element_t a,element_t g,pairing_t pairing){
            
            element_t ctemp1,ctemp2,ctemp3,ctemp4,ctemp5,ctemp6;

            element_init_GT(C,pairing);
            element_init_G1(C_0,pairing);
            element_init_Zr(ctemp1,pairing);
            element_init_GT(ctemp2,pairing);
            element_init_Zr(ctemp3,pairing);
            element_init_G1(ctemp4,pairing);
            element_init_Zr(ctemp5,pairing);
            element_init_G1(ctemp6,pairing);

            for(int i=0;i<5;i++){
                element_init_Zr(V[i],pairing);
                element_init_Zr(LAMBDA[i],pairing);
                element_set_si(V[i],v[i]);
                element_set_si(LAMBDA[i],lambda[i]);
            }


            element_mul(ctemp1,alpha,V[0]);
            element_pow_zn(ctemp2,g_g,ctemp1);
            element_mul(C,M,ctemp2);

            element_pow_zn(C_0,g,V[0]);

            for(int i=0;i<5;i++){
                element_init_Zr(r[i],pairing);
                element_random(r[i]);
                element_init_G1(C_L[i],pairing);
                element_init_G1(D_L[i],pairing);

                element_neg(ctemp3,r[i]);
                element_pow_zn(ctemp4,ha[i],ctemp3);
                element_mul(ctemp5,a,LAMBDA[i]);
                element_pow_zn(ctemp6,g,ctemp5);

                element_mul(C_L[i],ctemp6,ctemp4);
                element_pow_zn(D_L[i],g,r[i]);
    }

    }

    void keygen(element_t K,element_t L,element_t t,element_t K_x[],element_t g_a,element_t msk,element_t g,element_t ha[],pairing_t pairing){
                element_t ktemp1;

                element_init_G1(K,pairing);
                element_init_G1(L,pairing);
                element_init_G1(ktemp1,pairing);
                element_init_Zr(t,pairing);
                element_random(t);

                element_pow_zn(ktemp1,g_a,t);
                element_mul(K,msk,ktemp1);
                element_pow_zn(L,g,t);

                for(int i=0;i<2;i++){
                    element_init_G1(K_x[i],pairing);
                    element_pow_zn(K_x[i],ha[i],t);
                }
    }

    void decrypt(element_t OMEGA[],element_t DEC,element_t C_0,element_t K,int omega[],element_t C_L[],element_t L,element_t D_L[],element_t K_x[],element_t C,pairing_t pairing){
    element_t dtemp_up,dtemp_down,dtemp_r,dtemp1,dtemp2,dtemp3,dtemp4;
    element_init_GT(dtemp_up,pairing);
    element_init_GT(dtemp_down,pairing);
    element_init_GT(dtemp_r,pairing);
    element_init_GT(dtemp1,pairing);
    element_init_GT(dtemp2,pairing);
    element_init_GT(dtemp3,pairing);
    element_init_GT(dtemp4,pairing);
    element_init_GT(DEC,pairing);
    element_set1(dtemp_down);

    pairing_apply(dtemp_up,C_0,K,pairing);

    for(int i=0;i<5;i++){
        element_init_Zr(OMEGA[i],pairing);
        element_set_si(OMEGA[i],omega[i]);
    }

    for(int i=0;i<2;i++){
        pairing_apply(dtemp1,C_L[i],L,pairing);
        pairing_apply(dtemp2,D_L[i],K_x[i],pairing);
        element_mul(dtemp3,dtemp1,dtemp2);
        element_pow_zn(dtemp4,dtemp3,OMEGA[i]);
        element_mul(dtemp_down,dtemp_down,dtemp4);
    }

    element_div(dtemp_r,dtemp_up,dtemp_down);
    element_div(DEC,C,dtemp_r);
    }


int main(){

//————————————————————————————————矩阵——————————————————————————————————————
    hash<string> h;
    pairing_t pairing;

    char file[]="a.param";
    pbc_pairing_init(pairing, file);

    int x=rand();
    int y=rand();

    int v[4]={2,3,1,4},lambda[5]={0,0,0,0,0},omega[2]={1,-1};
    matrix_gen(v,lambda,omega);



//————————————————————————————————初始化——————————————————————————————————————
    
    element_t g,g_g;
    element_t alpha,a;
    element_init_G1(g, pairing);
    element_init_GT(g_g, pairing);
    element_init_Zr(alpha, pairing);
    element_init_Zr(a, pairing);
    element_random(alpha);
    element_random(a);

    //签名算法初始化
    element_t p,H,X,sign_v,sign_V;
    sign_setup(p,H,X,sign_v,sign_V,pairing);


//————————————————————————————————计算PK、MSK——————————————————————————————————————

    element_t g_alpha,g_a,msk;
    element_t ha[5];

    setup_pp(msk,ha,g_alpha,g_a,g,g_g,alpha,a,pairing);

//————————————————————————————————加密——————————————————————————————————————

    element_t M,C,C_0,V[5],LAMBDA[5],C_L[5],D_L[5],r[5];

    element_init_GT(M,pairing);
    element_random(M);

    encrypt(M,C,C_0,V,LAMBDA,C_L,D_L,r,v,lambda,alpha,g_g,ha,a,g,pairing);

    
//————————————————————————————————密钥生成——————————————————————————————————————

    element_t K,L,t,K_x[2];

    keygen(K,L,t,K_x,g_a,msk,g,ha,pairing);

//————————————————————————————————解密——————————————————————————————————————

    element_t OMEGA[2],DEC;
    decrypt(OMEGA,DEC,C_0,K,omega,C_L,L,D_L,K_x,C,pairing);


    element_printf("%B\n",M); 
    element_printf("%B\n",DEC); 


}