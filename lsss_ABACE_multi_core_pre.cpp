#include <iostream>
#include "/usr/local/include/pbc/pbc.h"
#include <map>
#include <cstring>
#include <cstdlib>
#include <set>
#include <vector>
#include <eigen3/Eigen/Dense>
#include <random>
#include <fstream>
#include <chrono>


#include <thread>
#include <ctime>

#define RUN_TIMES 10
using namespace std;
using namespace Eigen;

    void compute_pairings(element_t** results, element_t* D_L, element_t* K_x, pairing_t pairing, int count, int start, int end) {
        for (int i = start; i < end; i++) {
            for (int j = 0; j < count; j++) {
                pairing_apply(results[i][j], D_L[j], K_x[j], pairing);
            }
        }
    }

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

    void setup_pp(element_t msk,element_t ha1[],element_t ha2[],element_t g_alpha,element_t h_a,element_t g,element_t h,element_t g_h,element_t alpha,element_t a,pairing_t pairing,int count){
            element_init_GT(g_alpha, pairing);
            element_init_G2(h_a, pairing);
            element_init_G2(msk, pairing);
            element_random(g);
            element_random(h);
            pairing_apply(g_h,g,h,pairing);

            element_pow_zn(g_alpha,g_h,alpha);
            element_pow_zn(h_a,h,a);
            element_pow_zn(msk,h,alpha);

            element_t r;
            element_init_Zr(r,pairing);
            for(int i=0;i<count;i++){
                element_random(r);
                element_init_G1(ha1[i], pairing);
                element_init_G2(ha2[i], pairing);
                element_pow_zn(ha1[i],g,r); 
                element_pow_zn(ha2[i],h,r); 

            // element_init_G1(ha[i], pairing);
            // element_random(ha[i]);
    }
    }


    void collector(element_t A,element_t A_0,element_t V[],element_t LAMBDA[],element_t A_L[],element_t B_L[],element_t r[],int v[],int lambda[],element_t alpha,element_t g_h,element_t ha[],element_t a,element_t g,pairing_t pairing,int count){

            element_t ctemp1,ctemp2,ctemp3,ctemp4,ctemp5,ctemp6;

            element_init_GT(A,pairing);
            element_init_G1(A_0,pairing);
            element_init_Zr(ctemp1,pairing);
            element_init_GT(ctemp2,pairing);
            element_init_Zr(ctemp3,pairing);
            element_init_G1(ctemp4,pairing);
            element_init_Zr(ctemp5,pairing);
            element_init_G1(ctemp6,pairing);

            for(int i=0;i<count;i++){
                element_init_Zr(V[i],pairing);
                element_init_Zr(LAMBDA[i],pairing);
                element_set_si(V[i],v[i]);
                element_set_si(LAMBDA[i],lambda[i]);
            }


            element_mul(ctemp1,alpha,V[0]);
            element_pow_zn(A,g_h,ctemp1);

            element_pow_zn(A_0,g,V[0]);

            for(int i=0;i<count;i++){
                element_init_Zr(r[i],pairing);
                element_random(r[i]);
                element_init_G1(A_L[i],pairing);
                element_init_G1(B_L[i],pairing);

                element_neg(ctemp3,r[i]);
                element_pow_zn(ctemp4,ha[i],ctemp3);
                element_mul(ctemp5,a,LAMBDA[i]);
                element_pow_zn(ctemp6,g,ctemp5);

                element_mul(A_L[i],ctemp6,ctemp4);
                element_pow_zn(B_L[i],g,r[i]);
    }

    //         for(int i=count;i<10;i++){

    //         element_init_G1(A_L[i],pairing);
    //         element_init_G1(B_L[i],pairing);
    //         element_random(A_L[i]);
    //         element_random(B_L[i]);
    // }

    }

    void encrypt(element_t k,element_t q, element_t M,element_t C,element_t C_0,element_t C_L[],element_t D_L[],element_t c,element_t c_0,element_t c_L[],element_t d_L[],element_t A,element_t A_0,element_t A_L[],element_t B_L[],pairing_t pairing,int count){


        element_t etemp;
        element_init_GT(etemp,pairing);
        element_init_GT(C,pairing);
        element_init_G1(C_0,pairing);
        element_init_GT(c,pairing);
        element_init_G1(c_0,pairing);

        element_pow_zn(etemp,A,k);
        element_mul(C,M,etemp);
        element_pow_zn(C_0,A_0,k);
        element_pow_zn(c,A,q);
        element_pow_zn(c_0,A_0,q);

        for(int i=0;i<count;i++){
            element_init_G1(C_L[i],pairing);
            element_init_G1(D_L[i],pairing);
            element_pow_zn(C_L[i],A_L[i],k);
            element_pow_zn(D_L[i],B_L[i],k);

            element_init_G1(c_L[i],pairing);
            element_init_G1(d_L[i],pairing);
            element_pow_zn(c_L[i],A_L[i],q);
            element_pow_zn(d_L[i],B_L[i],q);
    }

    //     for(int i=count;i<10;i++){
    //         element_init_G1(C_L[i],pairing);
    //         element_init_G1(D_L[i],pairing);
    //         element_random(C_L[i]);
    //         element_random(D_L[i]);

    //         element_init_G1(c_L[i],pairing);
    //         element_init_G1(d_L[i],pairing);
    //         element_random(c_L[i]);
    //         element_random(d_L[i]);
    // }



    }


    void keygen(element_t K,element_t L,element_t t,element_t K_x[],element_t h_a,element_t msk,element_t h,element_t ha2[],pairing_t pairing,int count){
                element_t ktemp1;

                element_init_G2(K,pairing);
                element_init_G2(L,pairing);
                element_init_G2(ktemp1,pairing);
                element_init_Zr(t,pairing);
                element_random(t);

                element_pow_zn(ktemp1,h_a,t);
                element_mul(K,msk,ktemp1);
                element_pow_zn(L,h,t);

                for(int i=0;i<count;i++){
                    element_init_G2(K_x[i],pairing);
                    element_pow_zn(K_x[i],ha2[i],t);
                }
    }


    void sanitize(element_t C_r,element_t C_0_r,element_t C_L_r[],element_t D_L_r[],element_t C,element_t C_0,element_t C_L[],element_t D_L[],element_t c,element_t c_0,element_t c_L[],element_t d_L[],pairing_t pairing,int count){
        element_t u;
        element_t stemp,stemp_0,stemps[count];
        element_init_Zr(u,pairing);
        element_init_GT(stemp,pairing);
        element_init_G1(stemp_0,pairing);
        element_init_GT(C_r,pairing);
        element_init_G1(C_0_r,pairing);
        element_random(u);

        element_pow_zn(stemp,c,u);
        element_mul(C_r,C,stemp);    
        element_pow_zn(stemp_0,c_0,u);
        element_mul(C_0_r,C_0,stemp_0); 

        for(int i=0;i<count;i++){
            element_init_G1(C_L_r[i],pairing);
            element_init_G1(D_L_r[i],pairing);
            element_init_G1(stemps[i],pairing);

            element_pow_zn(stemps[i],c_L[i],u);
            element_mul(C_L_r[i],C_L[i],stemps[i]);
            element_pow_zn(stemps[i],d_L[i],u);
            element_mul(D_L_r[i],D_L[i],stemps[i]);

    }

    }

    void decrypt(element_t OMEGA[],element_t DEC,element_t C_0,element_t K,int omega[],element_t C_L[],element_t L,element_t D_L[],element_t K_x[],element_t C,pairing_t pairing,int count){
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

    for(int i=0;i<count;i++){
        element_init_Zr(OMEGA[i],pairing);
        element_set_si(OMEGA[i],omega[i]);
    }

    //--------------------------预计算测试开始--------------------------

    auto start = std::chrono::high_resolution_clock::now();
    int runtime = 200;
    element_t** results = new element_t*[runtime];
    for (int i = 0; i < runtime; i++) {
        results[i] = new element_t[count];
        for (int j = 0; j < count; j++) {
            element_init_GT(results[i][j], pairing);
        }
    }

    int num_threads = std::thread::hardware_concurrency();
    std::vector<std::thread> threads;
    int iterations_per_thread = runtime / num_threads;
    int remainder = runtime % num_threads;



    for (int i = 0; i < num_threads; i++) {
        int start_index = i * iterations_per_thread;
        int end_index = start_index + iterations_per_thread;
        if (i == num_threads - 1) {
            end_index += remainder;
        }
        threads.emplace_back(compute_pairings, results, D_L, K_x, pairing, count, start_index, end_index);
    }

    for (auto& th : threads) {
        th.join();
    }

    auto end = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> elapsed = end - start;
    std::cout << "Total time for 200 iterations: " << elapsed.count() << " seconds\n";

    // 清理结果数组
    for (int i = 0; i < runtime; i++) {
        for (int j = 0; j < count; j++) {
            element_clear(results[i][j]);
        }
        delete[] results[i];
    }
    delete[] results;
    //--------------------------预计算测试结束--------------------------

    for(int i=0;i<count;i++){
        pairing_apply(dtemp2,D_L[i],K_x[i],pairing);
    }

    for(int i=0;i<count;i++){
        pairing_apply(dtemp1,C_L[i],L,pairing);
        //pairing_apply(dtemp2,D_L[i],K_x[i],pairing);
        element_mul(dtemp3,dtemp1,dtemp2);
        element_pow_zn(dtemp4,dtemp3,OMEGA[i]);
        element_mul(dtemp_down,dtemp_down,dtemp4);
    }

    element_div(dtemp_r,dtemp_up,dtemp_down);
    element_div(DEC,C,dtemp_r);

    }

    void sign(element_t A,element_t g,element_t H,element_t R,element_t S,element_t T,element_t W,element_t sign_v,element_t X,pairing_t pairing){
    element_t r;
    element_t stemp0,stemp1,stemp2,stemp3,stemp4,stemp5;

    element_init_Zr(r, pairing);

    element_init_Zr(stemp0, pairing);
    element_init_Zr(stemp1, pairing);
    element_init_Zr(stemp2, pairing);
    element_init_G1(stemp3, pairing);
    element_init_G1(stemp4, pairing);
    element_init_G1(stemp5, pairing);

    element_set1(stemp0);
    element_random(r);

    element_pow_zn(R,H,r);

    element_div(stemp1,sign_v,r);
    element_div(stemp2,stemp0,r);

    element_pow_zn(stemp3,A,stemp1);
    element_pow_zn(stemp4,X,stemp2);
    element_mul(S,stemp3,stemp4);

    element_pow_zn(stemp5,S,stemp1);
    element_pow_zn(W,g,stemp2);
    element_mul(T,stemp5,W);
    }


    void sign_rand(element_t alpha,element_t R,element_t S,element_t T,element_t W,element_t R_1,element_t S_1,element_t T_1,pairing_t pairing){
    element_t rtemp0,rtemp1,rtemp2,rtemp3,rtemp4,rtemp5,rtemp6;

    element_init_Zr(rtemp0, pairing);
    element_init_Zr(rtemp1, pairing);
    element_init_Zr(rtemp2, pairing);
    element_init_Zr(rtemp3, pairing);
    element_init_Zr(rtemp4, pairing);
    element_init_G1(rtemp5, pairing);
    element_init_G1(rtemp6, pairing);
    element_set1(rtemp0);

    element_div(rtemp1,rtemp0,alpha);
    element_pow_zn(R_1,R,rtemp1);

    element_pow_zn(S_1,S,alpha);

    element_mul(rtemp2,alpha,alpha);
    element_sub(rtemp3,rtemp0,alpha);
    element_mul(rtemp4,alpha,rtemp3);
    element_pow_zn(rtemp5,T,rtemp2);
    element_pow_zn(rtemp6,W,rtemp4);
    element_mul(T_1,rtemp5,rtemp6);
    }

    int vfy(element_t A,element_t R,element_t S,element_t T,element_t sign_V,element_t X,element_t g,element_t H,pairing_t pairing){
    element_t e_av,e_xh,e_sv,e_gh;
    element_t left_1,left_2,right_1,right_2;

    element_init_GT(e_av, pairing);
    element_init_GT(e_xh, pairing);
    element_init_GT(e_sv, pairing);
    element_init_GT(e_gh, pairing);
    element_init_GT(left_1, pairing);
    element_init_GT(left_2, pairing);
    element_init_GT(right_1, pairing);
    element_init_GT(right_2, pairing);

    pairing_apply(left_1,S,R,pairing);
    pairing_apply(left_2,T,R,pairing);
    pairing_apply(e_av,A,sign_V,pairing);
    pairing_apply(e_xh,X,H,pairing);
    pairing_apply(e_sv,S,sign_V,pairing);
    pairing_apply(e_gh,g,H,pairing);
    element_mul(right_1,e_av,e_xh);
    element_mul(right_2,e_sv,e_gh);

    // cout<<"element_cmp(left_1,right_1) = "<<element_cmp(left_1,right_1)<<endl;
    // cout<<"element_cmp(left_2,right_2) = "<<element_cmp(left_2,right_2)<<endl;

    if((element_cmp(left_1,right_1)==0)&&(element_cmp(left_2,right_2)==0))
    {
        return 1;
    }
    else{return 0;}
    }

    int vfy(element_t A_r,element_t R,element_t S,element_t T,element_t sign_V,element_t sign_V_r1,element_t X,element_t g,element_t H,pairing_t pairing){
    element_t e_av,e_xh,e_sv,e_gh;
    element_t left_1,left_2,right_1,right_2;

    element_init_GT(e_av, pairing);
    element_init_GT(e_xh, pairing);
    element_init_GT(e_sv, pairing);
    element_init_GT(e_gh, pairing);
    element_init_GT(left_1, pairing);
    element_init_GT(left_2, pairing);
    element_init_GT(right_1, pairing);
    element_init_GT(right_2, pairing);

    pairing_apply(left_1,S,R,pairing);
    pairing_apply(left_2,T,R,pairing);
    pairing_apply(e_av,A_r,sign_V_r1,pairing);
    pairing_apply(e_xh,X,H,pairing);
    pairing_apply(e_sv,S,sign_V,pairing);
    pairing_apply(e_gh,g,H,pairing);
    element_mul(right_1,e_av,e_xh);
    element_mul(right_2,e_sv,e_gh);

    // cout<<"element_cmp(left_1,right_1) = "<<element_cmp(left_1,right_1)<<endl;
    // cout<<"element_cmp(left_2,right_2) = "<<element_cmp(left_2,right_2)<<endl;

    if((element_cmp(left_1,right_1)==0)&&(element_cmp(left_2,right_2)==0))
    {
        return 1;
    }
    else{return 0;}
    }

void cal_hash(element_t c,element_t xx[],element_t yy[],element_t tt[], int n,pairing_t pairing)
{

    int length=element_length_in_bytes(xx[0]);
    // cout<<length<<endl;

    unsigned char *element_byte=new unsigned char [length];
    string s;
    for (int i=0;i<n;i++)
    {
        string  temp_s;
        element_to_bytes(element_byte,xx[i]);
        temp_s.assign((const char*)element_byte, element_length_in_bytes(xx[i]));
        s=s+temp_s;
    }
    for (int i=0;i<n;i++)
    {
        string  temp_s;
        element_to_bytes(element_byte,yy[i]);
        temp_s.assign((const char*)element_byte, element_length_in_bytes(yy[i]));
        s=s+temp_s;
    }
    for (int i=0;i<n;i++)
    {
        string  temp_s;
        element_to_bytes(element_byte,tt[i]);
        temp_s.assign((const char*)element_byte, element_length_in_bytes(tt[i]));
        s=s+temp_s;
    }

    // print_hex(s.c_str(), s.size());




    hash<string> hash_func;
    string hash_s=to_string(hash_func(s));
    element_from_hash(c,(void*)hash_s.c_str(),hash_s.size());
    // element_printf("%B\n",c);

    // print_hex(s.c_str(), s.size());
}

    
    void prove(element_t s,element_t tt[],element_t xx[],element_t yy[],int length,element_t x, pairing_t pairing )
    {
        //这里用到的三个局部变量，temp存储中间计算结果，c存储哈希结果，r只是随机数
        element_t temp;
        element_t r;
        element_t c;
        element_init_Zr(temp,pairing);
        element_init_Zr(r,pairing);
        element_init_Zr(c,pairing);

        element_random(r);

        for(int i =0;i<length;i++)
        {
            element_pow_zn(tt[i],xx[i],r);
        }

        // element_pow_zn(t1,x1,r);
        // element_pow_zn(t2,x2,r);
        // element_pow_zn(t3,x3,r);

        cal_hash(c,xx,yy,tt,length, pairing);
    //计算s
        element_mul(temp,x,c);
        element_add(s,r,temp);

    }

    int verify(element_t s,element_t tt[],element_t xx[],element_t yy[],int length, pairing_t pairing)
{
    element_t c;
    element_init_Zr(c,pairing);

    element_t xx_s[length];
    element_t yy_c[length];
    element_t temp[length];
    for (int i=0;i<length;i++)
    {
        element_init_G1(xx_s[i],pairing);
    }
    for (int i=0;i<length;i++)
    {
        element_init_G1(yy_c[i],pairing);
    }
    for (int i=0;i<length;i++)
    {
        element_init_G1(temp[i],pairing);
    }


    // cal_hash(c,x1,x2, x3,y1, y2,y3, t1,t2,t3 , pairing);
    cal_hash(c,xx,yy,tt,length,pairing);
    

    // 计算并判断是否相等
    for (int i=0;i<length;i++)
    {
        element_pow_zn(yy_c[i],yy[i],c);
        element_pow_zn(xx_s[i],xx[i],s);
        element_mul(temp[i],yy_c[i],tt[i]);

    }

    for (int i=0;i<length;i++)
    {
        // element_printf("xx_s=%B\n",xx_s[i]);
        // element_printf("temp s=%B\n",temp[i]);
        if(element_cmp(xx_s[i],temp[i])!=0)
        { return 0;}
    }
    return 1;


}






int main(){
    random_device rd;  //如果可用的话，从一个随机数发生器上获得一个真正的随机数
    mt19937 gen(rd()); //gen是一个使用rd()作种子初始化的标准梅森旋转算法的随机数发生器
    uniform_int_distribution<> distrib(1, 10);

// for (int i =0;i<5;i++)
// {
    fstream f;
    f.open("lsss_ABACE.csv",ios::out|ios::app);
    f<<"Number of Attributes,Setup,Encrytion key generation,Decrytion key generation,Encryption,Sanitization,Decrytion"<<endl;

    for(int iter_i =0;iter_i<1;iter_i++)
{
    int count=1000;
    f<<count<<",";
    cout<<"test--------------"<<iter_i<<"--------------"<<endl;

    clock_t start,end;

//————————————————————————————————矩阵——————————————————————————————————————
    pairing_t pairing;

    char file[]="f.param";
    pbc_pairing_init(pairing, file);


    Matrix<float, Dynamic,Dynamic> matrix_c; 
    matrix_c.resize(2,2);
    matrix_c<< 1,0,
        1,1;
    // cout<<matrix_c<<endl;

    Matrix<float, Dynamic,Dynamic> matrix_A;  
    // int count=10;
    for(int i=2;i<count;i++)
    {
        matrix_A.resize(i+1,i+1);
        // cout<<"i="<<i<<endl;
        matrix_A.block(0, 1, i, i)<<matrix_c;
        matrix_A.block(0, 0, i, 1)<<matrix_c.col(0);
        for(int k=0;k<i+1;k++)
        {
            matrix_A(i,k)=0;
        }
        matrix_A(i,1)=1;
        matrix_c.resize(i+1,i+1);
        matrix_c=matrix_A;

    }
    // cout<<"matrix_A"<<endl<<matrix_A<<endl;

    Matrix<float, Dynamic,Dynamic> matrix_v; 
    matrix_v.resize(count,1);
    for(int i=0;i<count;i++)
    {
        matrix_v(i,0)=distrib(gen);
    }
    Matrix<float, Dynamic,Dynamic> matrix_lambda;
    matrix_lambda.resize(count,1);
    matrix_lambda=matrix_A*matrix_v;

    // cout<<"matrix_v"<<endl<<matrix_v<<endl;
    // cout<<"matrix_lambda"<<endl<<matrix_lambda<<endl; 
    // cout<<"AT"<<endl<<matrix_A.transpose()<<endl;


    Matrix<float, Dynamic,Dynamic> sigma; 
    sigma.resize(count,1);
    for(int i=0;i<count;i++)
    {
        sigma(i,0)=0;
    }
    sigma(0,0)=1;

    Matrix<float, Dynamic,Dynamic> matrix_omega; 
    matrix_omega.resize(count,1);
    matrix_omega=matrix_A.transpose().colPivHouseholderQr().solve(sigma); 
    for (int i=0;i<count;i++)
    {
        // if(abs(abs(matrix_omega(i,0))-round(abs(matrix_omega(i,0))))<0.01)
        {matrix_omega(i,0)=round(matrix_omega(i,0));}
    }
    // cout<<"matrix_omega"<<endl<<matrix_omega<<endl;

    // cout<<"result"<<matrix_lambda.transpose()*matrix_omega<<endl;

    // int v[4]={2,3,1,4},lambda[count]={0,0,0,0,0},omega[2]={1,-1};
    int v[count];
    int lambda[count];
    int omega[count];
    for (int i=0;i<count;i++)
    {
        v[i]=matrix_v(i,0);
        omega[i]=matrix_omega(i,0);
        lambda[i]=matrix_lambda(i,0);
    }




//————————————————————————————————初始化——————————————————————————————————————
    //---------------------计时-----------------
    //程序开始计时
    start=clock();	
    
    element_t g,g_h,h;
    element_t alpha,a;
    element_init_G1(g, pairing);
    element_init_G2(h, pairing);
    element_init_GT(g_h, pairing);
    element_init_Zr(alpha, pairing);
    element_init_Zr(a, pairing);
    element_random(alpha);
    element_random(a);

    //签名算法初始化
    element_t p,H,X,sign_v,sign_V;
    sign_setup(p,H,X,sign_v,sign_V,pairing);

//————————————————————————————————计算PK、MSK——————————————————————————————————————

    element_t g_alpha,h_a,msk;
    element_t ha1[count];
    element_t ha2[count];

    setup_pp(msk,ha1,ha2,g_alpha,h_a,g,h,g_h,alpha,a,pairing,count);

    //程序结束用时
	end=clock();		
	double endtime1=(double)(end-start)/CLOCKS_PER_SEC;
	cout<<"setup Total time:"<<endtime1*1000<<"ms"<<endl;	//ms为单位
    f<<endtime1*1000<<",";
//---------------------计时-----------------




// ————————————————————————————————计算加密秘钥——————————————————————————————————————
//---------------------计时-----------------
    //程序开始计时
    start=clock();	

    element_t A,A_0,V[count],LAMBDA[count],A_L[count],B_L[count],r[count];  

    collector(A,A_0,V,LAMBDA,A_L,B_L,r,v,lambda,alpha,g_h,ha1,a,g,pairing,count);

        //对加密密钥进行签名
    element_t R_A,S_A,T_A,W_A;
    element_init_G2(R_A, pairing);
    element_init_G1(S_A, pairing);
    element_init_G1(T_A, pairing);
    element_init_G1(W_A, pairing);

    sign(A_0,g,H,R_A,S_A,T_A,W_A,sign_v,X,pairing);

    element_t R_A_L[count],S_A_L[count],T_A_L[count],W_A_L[count],R_B_L[count],S_B_L[count],T_B_L[count],W_B_L[count];
    for(int i=0;i<count;i++){
    element_init_G2(R_A_L[i], pairing);
    element_init_G1(S_A_L[i], pairing);
    element_init_G1(T_A_L[i], pairing);
    element_init_G1(W_A_L[i], pairing);

    element_init_G2(R_B_L[i], pairing);
    element_init_G1(S_B_L[i], pairing);
    element_init_G1(T_B_L[i], pairing);
    element_init_G1(W_B_L[i], pairing);

    sign(A_L[i],g,H,R_A_L[i],S_A_L[i],T_A_L[i],W_A_L[i],sign_v,X,pairing);
    sign(B_L[i],g,H,R_B_L[i],S_B_L[i],T_B_L[i],W_B_L[i],sign_v,X,pairing);
    }

    //程序结束用时
	end=clock();		
	double endtime2=(double)(end-start)/CLOCKS_PER_SEC;
	cout<<"encryption key generation Total time:"<<endtime2*1000<<"ms"<<endl;	//ms为单位
    f<<endtime2*1000<<",";
//---------------------计时-----------------

// //————————————————————————————————秘钥生成——————————————————————————————————————
//---------------------计时-----------------
    //程序开始计时
    start=clock();	

    element_t K,L,t,K_x[count];

    keygen(K,L,t,K_x,h_a,msk,h,ha2,pairing,count);

    //程序结束用时
	end=clock();		
	double endtime4=(double)(end-start)/CLOCKS_PER_SEC;
	cout<<"decryption key generation Total time:"<<endtime4*1000<<"ms"<<endl;	//ms为单位
    f<<endtime4*1000<<",";
//---------------------计时-----------------



// //————————————————————————————————加密——————————————————————————————————————

//    //加密之前,先对解密密钥进行rand处理
    element_t rr;
    element_init_Zr(rr, pairing);
    element_random(rr);

    element_t A_L_r[count];
    element_t B_L_r[count];

     for(int i=0;i<count;i++){
    element_init_G1(A_L_r[i], pairing);
    element_init_G1(B_L_r[i], pairing);

    element_pow_zn(A_L_r[i],A_L[i],rr);
    element_pow_zn(B_L_r[i],B_L[i],rr);
    }

        //计算V^(1/r)用于对A_L_r进行验证,r1是1/r
    element_t sign_V_r1,r1;
    element_init_G2(sign_V_r1, pairing);
    element_init_Zr(r1,pairing);
    element_invert(r1,rr);
    element_pow_zn(sign_V_r1,sign_V,r1);

    element_t R_A_r,S_A_r,T_A_r;
    element_init_G2(R_A_r, pairing);
    element_init_G1(S_A_r, pairing);
    element_init_G1(T_A_r, pairing);


    sign_rand(rr,R_A,S_A,T_A,W_A,R_A_r,S_A_r,T_A_r,pairing);

    element_t R_A_L_r[count],S_A_L_r[count],T_A_L_r[count],R_B_L_r[count],S_B_L_r[count],T_B_L_r[count];
    for(int i=0;i<count;i++){
    element_init_G2(R_A_L_r[i], pairing);
    element_init_G1(S_A_L_r[i], pairing);
    element_init_G1(T_A_L_r[i], pairing);

    element_init_G2(R_B_L_r[i], pairing);
    element_init_G1(S_B_L_r[i], pairing);
    element_init_G1(T_B_L_r[i], pairing);

    sign_rand(rr,R_A_L[i],S_A_L[i],T_A_L[i],W_A_L[i],R_A_L_r[i],S_A_L_r[i],T_A_L_r[i],pairing);
    sign_rand(rr,R_B_L[i],S_B_L[i],T_B_L[i],W_B_L[i],R_B_L_r[i],S_B_L_r[i],T_B_L_r[i],pairing);
    }


    element_t A_r,A_0_r;
    element_init_GT(A_r,pairing);
    element_init_G1(A_0_r,pairing);
    element_pow_zn(A_r,A,rr);
    element_pow_zn(A_0_r,A_0,rr);


    element_t M,C,C_0,C_L[count],D_L[count],c,c_0,c_L[count],d_L[count];
    element_init_GT(M,pairing);
    element_random(M);

    element_t k,q;
    element_init_Zr(k,pairing);
    element_init_Zr(q,pairing);
    element_random(k);
    element_random(q);


//现在使用加密密钥的r次方进行加密
    encrypt(k,q,M,C,C_0,C_L,D_L,c,c_0,c_L,d_L,A_r,A_0_r,A_L_r,B_L_r,pairing,count);

//---------------------计时-----------------
    //程序开始计时
    start=clock();	
//生成密文的NIZK proof
    element_t  CL_ss;
    element_init_Zr(CL_ss,pairing);
    element_t CL_tt[count];

    element_t  DL_ss;
    element_init_Zr(DL_ss,pairing);
    element_t DL_tt[count];

        for (int i =0;i<count;i++)
    {
        element_init_G1(CL_tt[i],pairing);
    }
        for (int i =0;i<count;i++)
    {
        element_init_G1(DL_tt[i],pairing);
    }

    prove(CL_ss,CL_tt,A_L_r,C_L,count,k,pairing);

    prove(DL_ss,DL_tt,B_L_r,D_L,count,k,pairing);


//生成净化项的NIZK proof
    element_t  cL_ss;
    element_init_Zr(cL_ss,pairing);
    element_t cL_tt[count];

    element_t  dL_ss;
    element_init_Zr(dL_ss,pairing);
    element_t dL_tt[count];

        for (int i =0;i<count;i++)
    {
        element_init_G1(cL_tt[i],pairing);
    }
        for (int i =0;i<count;i++)
    {
        element_init_G1(dL_tt[i],pairing);
    }

    prove(cL_ss,cL_tt,A_L_r,c_L,count,q,pairing);

    prove(dL_ss,dL_tt,B_L_r,d_L,count,q,pairing);


    //程序结束用时
	end=clock();		
	double endtime3=(double)(end-start)/CLOCKS_PER_SEC;
	cout<<"encryption Total time:"<<endtime3*1000<<"ms"<<endl;	//ms为单位
//---------------------计时-----------------
    f<<endtime3*1000<<",";



// //————————————————————————————————净化——————————————————————————————————————


    //签名验证
    vfy(A_0,R_A_r,S_A_r,T_A_r,sign_V,X,g,H,pairing);
    // cout<<"A verification result: "<<vfy(A_0,R_A_r,S_A_r,T_A_r,sign_V,X,g,H,pairing)<<endl;

    

    for(int i=0;i<count;i++){

    // cout<<"A["<<i<<"] verification result: "<<vfy(A_L_r[i],R_A_L_r[i],S_A_L_r[i],T_A_L_r[i],sign_V,sign_V_r1,X,g,H,pairing)<<endl;
    // cout<<"B["<<i<<"] verification result: "<<vfy(B_L_r[i],R_B_L_r[i],S_B_L_r[i],T_B_L_r[i],sign_V,sign_V_r1,X,g,H,pairing)<<endl;

    vfy(A_L_r[i],R_A_L_r[i],S_A_L_r[i],T_A_L_r[i],sign_V,sign_V_r1,X,g,H,pairing);
    vfy(B_L_r[i],R_B_L_r[i],S_B_L_r[i],T_B_L_r[i],sign_V,sign_V_r1,X,g,H,pairing);
    }

    //---------------------计时-----------------
    //程序开始计时
    start=clock();	

    int result1=verify(CL_ss,CL_tt ,A_L_r,C_L,count, pairing);
    // cout<<"CL NIZK verification "<<result1<<endl;

    int result2=verify(DL_ss,DL_tt ,B_L_r,D_L,count, pairing);
    // cout<<"DL NIZK verification "<<result2<<endl;

    int result3=verify(cL_ss,cL_tt ,A_L_r,c_L,count, pairing);
    // cout<<"cL NIZK verification "<<result3<<endl;

    int result4=verify(dL_ss,dL_tt ,B_L_r,d_L,count, pairing);
    // cout<<"dL NIZK verification "<<result4<<endl;

    //程序结束用时
	end=clock();		
	double endtime5=(double)(end-start)/CLOCKS_PER_SEC;
	cout<<"sanitization Total time:"<<endtime5*1000<<"ms"<<endl;	//ms为单位
    f<<endtime5*1000<<",";

    element_t C_r,C_0_r,C_L_r[count],D_L_r[count];

    sanitize(C_r,C_0_r,C_L_r,D_L_r,C,C_0,C_L,D_L,c,c_0,c_L,d_L,pairing,count);


//---------------------计时-----------------



// //————————————————————————————————解密——————————————————————————————————————
    //---------------------计时-----------------
    //程序开始计时
    start=clock();
    element_t OMEGA[count],DEC;
    decrypt(OMEGA,DEC,C_0_r,K,omega,C_L_r,L,D_L_r,K_x,C_r,pairing,count);

    //程序结束用时
	end=clock();		
	double endtime6=(double)(end-start)/CLOCKS_PER_SEC;
	cout<<"decryption Total time:"<<endtime6*1000<<"ms"<<endl;	//ms为单位
    f<<endtime6*1000<<endl;
//---------------------计时-----------------



    // element_printf("massage\n%B\n",M); 
    // element_printf("decryption\n%B\n",DEC); 
    cout<<"--------------finished--------------"<<endl;
}
    f.close();
// }
}