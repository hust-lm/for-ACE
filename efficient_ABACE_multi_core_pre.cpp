#include <iostream>
#include <fstream>
#include "/usr/local/include/pbc/pbc.h"
#include <map>
#include <cstring>
#include <cstdlib>
#include <set>
#include<vector>
#include <time.h>   
#include <vector>
#include <thread>
#include <chrono>
using namespace std;

#define RUN_TIMES 10

    void compute_pairings(int start, int end, element_t* sigma, element_t c_1, pairing_t pairing, element_t* results, int count) {
        element_t temp_sigma_w;
        element_init_G2(temp_sigma_w, pairing);  // 对每个线程单独初始化

        for (int j = start; j < end; ++j) {
            element_set1(temp_sigma_w);  // 重置为1

            for (int i = 0; i < count; ++i) {
                element_mul(temp_sigma_w, temp_sigma_w, sigma[i]);  // 私钥连乘
            }

            pairing_apply(results[j], c_1, temp_sigma_w, pairing);  // 计算配对
        }

        element_clear(temp_sigma_w);  // 清理资源
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

    void cal_hash(element_t c,element_t g,element_t h,element_t y,element_t z,element_t t1,element_t t2,pairing_t pairing)
    {
        string s1;
        string s2;
        string s3;
        string s4;
        string s5;
        string s6;

        int length=element_length_in_bytes(g);
        // cout<<length<<endl;

        unsigned char *element_byte=new unsigned char [length];
        element_to_bytes(element_byte,g);
        s1.assign((const char*)element_byte, element_length_in_bytes(g));
        element_to_bytes(element_byte,h);
        s2.assign((const char*)element_byte, element_length_in_bytes(h));
        element_to_bytes(element_byte,y);
        s3.assign((const char*)element_byte, element_length_in_bytes(y));
        element_to_bytes(element_byte,z);
        s4.assign((const char*)element_byte, element_length_in_bytes(z));
        element_to_bytes(element_byte,t1);
        s5.assign((const char*)element_byte, element_length_in_bytes(t1));
        element_to_bytes(element_byte,t2);
        s6.assign((const char*)element_byte, element_length_in_bytes(t2));

        string s=s1+s2+s3+s4+s5+s6;
        hash<string> hash_func;
        string hash_s=to_string(hash_func(s));
        
        element_from_hash(c,(void*)hash_s.c_str(),hash_s.size());
        // element_printf("%B\n",c);

        // print_hex(s.c_str(), s.size());
    }

    void cal_hash(element_t c,element_t x1,element_t x2,element_t x3,element_t y1,element_t y2,element_t y3,element_t t1,element_t t2,element_t t3 ,pairing_t pairing)
{
    string s1;
    string s2;
    string s3;
    string s4;
    string s5;
    string s6;
    string s7;
    string s8;
    string s9;

    int length=element_length_in_bytes(x1);
    // cout<<length<<endl;

    unsigned char *element_byte=new unsigned char [length];
    element_to_bytes(element_byte,x1);
    s1.assign((const char*)element_byte, element_length_in_bytes(x1));
    element_to_bytes(element_byte,x2);
    s2.assign((const char*)element_byte, element_length_in_bytes(x2));
    element_to_bytes(element_byte,x3);
    s3.assign((const char*)element_byte, element_length_in_bytes(x3));
    element_to_bytes(element_byte,y1);
    s4.assign((const char*)element_byte, element_length_in_bytes(y1));
    element_to_bytes(element_byte,y2);
    s5.assign((const char*)element_byte, element_length_in_bytes(y2));
    element_to_bytes(element_byte,y3);
    s6.assign((const char*)element_byte, element_length_in_bytes(y3));
    element_to_bytes(element_byte,t1);
    s7.assign((const char*)element_byte, element_length_in_bytes(t1));
    element_to_bytes(element_byte,t2);
    s8.assign((const char*)element_byte, element_length_in_bytes(t2));
    element_to_bytes(element_byte,t3);
    s9.assign((const char*)element_byte, element_length_in_bytes(t3));


    string s=s1+s2+s3+s4+s5+s6+s7+s8+s9;
    hash<string> hash_func;
    string hash_s=to_string(hash_func(s));
    
    element_from_hash(c,(void*)hash_s.c_str(),hash_s.size());
    // element_printf("%B\n",c);

    // print_hex(s.c_str(), s.size());
}

    void prove(element_t s,element_t t1,element_t t2,element_t g,element_t h,element_t y,element_t z,element_t x, pairing_t pairing )
    {
        //这里用到的三个局部变量，temp存储中间计算结果，c存储哈希结果，r只是随机数
        element_t temp;
        element_t r;
        element_t c;
        element_init_Zr(temp,pairing);
        element_init_Zr(r,pairing);
        element_init_Zr(c,pairing);

        element_random(r);

        element_pow_zn(t1,g,r);
        element_pow_zn(t2,h,r);


        cal_hash(c,g,h,y,z,t1,t2,pairing);
    // //计算s
        element_mul(temp,x,c);
        element_add(s,r,temp);

    }

    void prove(element_t s,element_t t1,element_t t2,element_t t3,element_t x1,element_t x2,element_t x3,element_t y1,element_t y2,element_t y3,element_t x, pairing_t pairing )
    {
        //这里用到的三个局部变量，temp存储中间计算结果，c存储哈希结果，r只是随机数
        element_t temp;
        element_t r;
        element_t c;
        element_init_Zr(temp,pairing);
        element_init_Zr(r,pairing);
        element_init_Zr(c,pairing);

        element_random(r);

        element_pow_zn(t1,x1,r);
        element_pow_zn(t2,x2,r);
        element_pow_zn(t3,x3,r);

        cal_hash(c,x1,x2, x3,y1, y2,y3, t1,t2,t3 , pairing);
    //计算s
    //     element_mul(temp,x,c);
    //     element_add(s,r,temp);

    }


    int verify(element_t s,element_t t1,element_t t2, element_t g,element_t h,element_t y,element_t z,pairing_t pairing)
    {
        element_t g_s,h_s,y_c,z_c,temp2,temp3,c;

        element_init_G1(g_s,pairing);
        element_init_G1(h_s,pairing);
        element_init_G1(y_c,pairing);
        element_init_G1(z_c,pairing);
        element_init_G1(temp2,pairing);
        element_init_G1(temp3,pairing);
        element_init_Zr(c,pairing);

        cal_hash(c,g,h,y,z,t1,t2,pairing);
        

        //计算并判断是否相等

        element_pow_zn(y_c,y,c);
        element_pow_zn(z_c,z,c);
        element_pow_zn(g_s,g,s);
        element_pow_zn(h_s,h,s);
        element_mul(temp2,y_c,t1);
        element_mul(temp3,z_c,t2);

        if((element_cmp(g_s,temp2)==0)&&(element_cmp(h_s,temp3)==0))
        {return 1;}
        else
        {return 0;}

    }

    int verify(element_t s,element_t t1,element_t t2, element_t t3,element_t x1,element_t x2, element_t x3,element_t y1,element_t y2, element_t y3,pairing_t pairing)
    {
        element_t x1_s,x2_s,x3_s,y1_c,y2_c,y3_c,c;
        element_t temp1,temp2,temp3;

        element_init_G1(x1_s,pairing);
        element_init_G1(x2_s,pairing);
        element_init_G1(x3_s,pairing);
        element_init_G1(y1_c,pairing);
        element_init_G1(y2_c,pairing);
        element_init_G1(y3_c,pairing);
        element_init_G1(temp1,pairing);
        element_init_G1(temp2,pairing);
        element_init_G1(temp3,pairing);
        element_init_Zr(c,pairing);

        cal_hash(c,x1,x2, x3,y1, y2,y3, t1,t2,t3 , pairing);
        

        //计算并判断是否相等

        element_pow_zn(y1_c,y1,c);
        element_pow_zn(y2_c,y2,c);
        element_pow_zn(y3_c,y3,c);
        element_pow_zn(x1_s,x1,s);
        element_pow_zn(x2_s,x2,s);
        element_pow_zn(x3_s,x3,s);
        element_mul(temp1,y1_c,t1);
        element_mul(temp2,y2_c,t2);
        element_mul(temp3,y3_c,t3);


        if((element_cmp(x1_s,temp1)==0)&&(element_cmp(x2_s,temp2)==0)&&(element_cmp(x3_s,temp3)==0))
        {return 1;}
        else
        {return 0;}

    }


    //十进制数字转成二进制字符串
    string Binary(int x) 
    {
        string s = "";
        while(x){
            if(x % 2 == 0) s = '0' + s;
            else s = '1' + s;
            x /= 2;
        }
        return s;
    }

    //获取数组中的属性的下标
    void get_position(int&x,string target,string attribute[],int count)
    {
        for (int i=0;i<count;i++)
        {
            if (target==attribute[i])
            {
                x=i+1;
                return ;
            }

        }
    }

    void init(int&x, int&y, element_t g,element_t h, map<string, pair<element_t,element_t>> &map_attribute, pairing_t pairing, hash<string> h_func,string attribute[], int count)
    {

        element_t temp1, temp2,temp3;
        element_t temp_x[count],temp_y[count];
        element_init_Zr(temp1, pairing);
        element_init_Zr(temp2, pairing);
        element_init_GT(temp3, pairing);
        element_random(g);
        element_random(h);
        // int j=0;

        //map存入<属性，pair<X,Y>>
        for(int i =0;i<count;i++)
        {
            // for (int j =0;j<4;j++)
            // {
            if (attribute[i]=="")
            {continue;}

            element_init_G1(temp_x[i], pairing);
            element_init_GT(temp_y[i], pairing);

            //首先分别计算每个属性对应的X和Y
            string s1=to_string(h_func(Binary(x)+Binary(i+1)));
            char c1[50];
            strcpy(c1,s1.c_str());

            string s2=to_string(h_func(Binary(y)+Binary(i+1)));
            char c2[50];
            strcpy(c2,s2.c_str());

            element_from_hash(temp1, c1, s1.size());
            element_neg(temp2,temp1);
            element_pow_zn(temp_x[i], g, temp2);

            element_from_hash(temp1, c2, s2.size());
            pairing_apply(temp3, g, h, pairing);
            element_pow_zn(temp_y[i], temp3, temp1);
            
            //将属性和对应X、Y建立映射，存入map中
            map_attribute[attribute[i]].first->data = temp_x[i]->data;
            map_attribute[attribute[i]].first->field = temp_x[i]->field;
            map_attribute[attribute[i]].second->data = temp_y[i]->data;
            map_attribute[attribute[i]].second->field = temp_y[i]->field;
            // }
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

    void enc_keygen(element_t xw,element_t yw,map<string, pair<element_t,element_t>> map_attribute,string policyW[],int count,pairing_t pairing){
        element_init_G1(xw,pairing);        
        element_init_GT(yw,pairing);
        element_set1(xw);
        element_set1(yw);

        //连乘生成xw、yw
        for(int i=0;i<count;i++){
            element_mul(xw,xw,map_attribute[policyW[i]].first);
            element_mul(yw,yw,map_attribute[policyW[i]].second);
        }
    }

    void keygen(int sk,element_t sigma[], pairing_t pairing, int x, int y, element_t h,string attribute_list[], string attribute[],hash<string> h_func,int count)
        //ktemp1、2是上面的指数，ktemp3是前面g^H0的结果，ktemp4是H1(sk)，ktemp5是H1(sk)^H0的结果
    {
        element_t ktemp1,ktemp2,ktemp3,ktemp4,ktemp5;
        element_init_Zr(ktemp1,pairing);
        element_init_Zr(ktemp2,pairing);
        element_init_G2(ktemp3,pairing);
        element_init_G2(ktemp4,pairing);
        element_init_G2(ktemp5,pairing);

        //定义用户属性列表，但是将string二维数组传到函数中，需要下面的步骤声明一个指向二维数组的指针ss  

            

        for(int i =0;i<count;i++)
        {
                // int a;
                // get_position(a,attribute_list[i],attribute,count);

                int a=i+1;

                //计算第一部分
                string s3=to_string(h_func(Binary(y)+Binary(a)));
                char c3[50];
                strcpy(c3,s3.c_str());
                element_from_hash(ktemp1, c3, s3.size());
                element_pow_zn(ktemp3,h,ktemp1);

                //计算第二部分指数
                string s4=to_string(h_func(Binary(x)+Binary(a)));
                char c4[50];
                strcpy(c4,s4.c_str());
                element_from_hash(ktemp2, c4, s4.size());

                //计算第二部分底数得到第二部分结果
                string s5=to_string(sk);
                char c5[50];
                strcpy(c5,s5.c_str());
                element_from_hash(ktemp4,c5,s5.size());
                element_pow_zn(ktemp5,ktemp4,ktemp2);

                //两部分结果相乘，存入sigma数组中
                element_init_G2(sigma[i],pairing);
                element_mul(sigma[i],ktemp3,ktemp5);
        }
    }

    void encrypt(element_t h_r,element_t t,element_t s,element_t xw_r,element_t yw_r,element_t c_0,element_t c_1,element_t c_2 ,element_t c_00,element_t c_11,element_t c_22,pairing_t pairing,element_t M, element_t g)
    {

        //生成密文c0,c1,c2。明文m的类型应该是G1或者Zr都可以，这里定义为G1,也可以是自己指定的整数Zr

        element_t mtemp;

        element_init_GT(mtemp,pairing);
  

        element_pow_zn(mtemp, yw_r, t);
        element_mul(c_0,M,mtemp);
        element_pow_zn(c_1, h_r, t);
        element_pow_zn(c_2, xw_r, t);

        element_pow_zn(c_00, yw_r, s);
        element_pow_zn(c_11, h_r, s);
        element_pow_zn(c_22, xw_r, s);

    }

    void sanitization(element_t C_0,element_t C_1,element_t C_2 ,element_t c_0,element_t c_1,element_t c_2 ,element_t c_00,element_t c_11,element_t c_22,pairing_t pairing){
        element_t s_r1,temp1,temp2,temp3;
        element_init_GT(temp1,pairing);
        element_init_G1(temp2,pairing);
        element_init_G1(temp3,pairing);
        element_init_Zr(s_r1,pairing);
        element_random(s_r1);

        element_pow_zn(temp1,c_00,s_r1);
        element_mul(C_0,c_0,temp1);
        element_pow_zn(temp2,c_11,s_r1);
        element_mul(C_1,c_1,temp2);
        element_pow_zn(temp3,c_22,s_r1);
        element_mul(C_2,c_2,temp3);
    }

    void decrypt(element_t Mresult,pairing_t pairing,int sk,element_t sigma[],element_t c_0,element_t c_1,element_t c_2,int count)
    {
    //————————————————————————————————解密部分——————————————————————————————————————
        // 其中dtemp1是分母下面左边的双线性映射结果，dtemp2是分母下面左边的双线性映射结果
        //dtemp3是H1(sk), dtemp4是两个双线性映射相乘的结果

        //初始化
        element_t sigma_w;
        element_t dtemp3;
        element_t dtemp1;
        element_t dtemp2;
        element_t dtemp4;
        
        element_init_G2(sigma_w,pairing);
        element_init_GT(dtemp1,pairing);
        element_init_GT(dtemp2,pairing);
        element_init_G2(dtemp3,pairing);
        element_init_GT(dtemp4,pairing);

        //sigma_w的值设置为1
        element_set1(sigma_w);

        //计算H1(sk)
        string s_sk=to_string(sk);
        char c6[50];
        strcpy(c6,s_sk.c_str());
        element_from_hash(dtemp3,c6,s_sk.size());

        //---------------------------------预计算开销---------------------------------
        int runtime = 200;
        element_t* temp_dtemp1 = new element_t[runtime];
        for (int i = 0; i < runtime; ++i) {
            element_init_GT(temp_dtemp1[i], pairing);  // 初始化结果数组
        }

        int num_threads = std::thread::hardware_concurrency();
        std::vector<std::thread> threads;
        int iterations_per_thread = runtime / num_threads;
        int remainder = runtime % num_threads;

        auto start = std::chrono::high_resolution_clock::now();

        // 创建并启动线程
        for (int i = 0; i < num_threads; ++i) {
            int start_index = i * iterations_per_thread;
            int end_index = (i + 1) * iterations_per_thread;
            if (i == num_threads - 1) {
                end_index += remainder;  // 确保最后一个线程覆盖所有剩余的部分
            }
            threads.emplace_back(compute_pairings, start_index, end_index, sigma, c_1, pairing, temp_dtemp1, count);
        }

        // 等待所有线程完成
        for (auto& th : threads) {
            th.join();
        }

        auto end = std::chrono::high_resolution_clock::now();
        std::chrono::duration<double> elapsed = end - start;
        std::cout << "Total pre-computing time for " << runtime << " iterations: " << elapsed.count() << " seconds\n";

        // 清理
        for (int i = 0; i < runtime; ++i) {
            element_clear(temp_dtemp1[i]);
        }
        delete[] temp_dtemp1;

        //---------------------------------预计算开销结束---------------------------------

        //sigma_w就是用户的所有私钥连乘的结果
        for (int i=0;i<count;i++)
        {
            element_mul(sigma_w,sigma_w,sigma[i]);
        }

        //计算最后的等式
        pairing_apply(dtemp1,c_1,sigma_w,pairing);


        pairing_apply(dtemp2,c_2,dtemp3,pairing);
        element_mul(dtemp4,dtemp1,dtemp2);
        // element_printf("c %B\n",c_0);
        element_div(Mresult,c_0,dtemp4);
        // element_printf("%B\n",Mresult);
    }





int main(){

for (int i=0;i<1;i++){

string universe[1000]={"a1","a2","a3","a4","a5","a6","a7","a8","a9","a10","a11","a12","a13","a14","a15","a16","a17","a18","a19","a20","a21","a22","a23","a24","a25","a26","a27","a28","a29","a30","a31","a32","a33","a34","a35","a36","a37","a38","a39","a40","a41","a42","a43","a44","a45","a46","a47","a48","a49","a50","a51","a52","a53","a54","a55","a56","a57","a58","a59","a60","a61","a62","a63","a64","a65","a66","a67","a68","a69","a70","a71","a72","a73","a74","a75","a76","a77","a78","a79","a80","a81","a82","a83","a84","a85","a86","a87","a88","a89","a90","a91","a92","a93","a94","a95","a96","a97","a98","a99","a100","a101","a102","a103","a104","a105","a106","a107","a108","a109","a110","a111","a112","a113","a114","a115","a116","a117","a118","a119","a120","a121","a122","a123","a124","a125","a126","a127","a128","a129","a130","a131","a132","a133","a134","a135","a136","a137","a138","a139","a140","a141","a142","a143","a144","a145","a146","a147","a148","a149","a150","a151","a152","a153","a154","a155","a156","a157","a158","a159","a160","a161","a162","a163","a164","a165","a166","a167","a168","a169","a170","a171","a172","a173","a174","a175","a176","a177","a178","a179","a180","a181","a182","a183","a184","a185","a186","a187","a188","a189","a190","a191","a192","a193","a194","a195","a196","a197","a198","a199","a200","a201","a202","a203","a204","a205","a206","a207","a208","a209","a210","a211","a212","a213","a214","a215","a216","a217","a218","a219","a220","a221","a222","a223","a224","a225","a226","a227","a228","a229","a230","a231","a232","a233","a234","a235","a236","a237","a238","a239","a240","a241","a242","a243","a244","a245","a246","a247","a248","a249","a250","a251","a252","a253","a254","a255","a256","a257","a258","a259","a260","a261","a262","a263","a264","a265","a266","a267","a268","a269","a270","a271","a272","a273","a274","a275","a276","a277","a278","a279","a280","a281","a282","a283","a284","a285","a286","a287","a288","a289","a290","a291","a292","a293","a294","a295","a296","a297","a298","a299","a300","a301","a302","a303","a304","a305","a306","a307","a308","a309","a310","a311","a312","a313","a314","a315","a316","a317","a318","a319","a320","a321","a322","a323","a324","a325","a326","a327","a328","a329","a330","a331","a332","a333","a334","a335","a336","a337","a338","a339","a340","a341","a342","a343","a344","a345","a346","a347","a348","a349","a350","a351","a352","a353","a354","a355","a356","a357","a358","a359","a360","a361","a362","a363","a364","a365","a366","a367","a368","a369","a370","a371","a372","a373","a374","a375","a376","a377","a378","a379","a380","a381","a382","a383","a384","a385","a386","a387","a388","a389","a390","a391","a392","a393","a394","a395","a396","a397","a398","a399","a400","a401","a402","a403","a404","a405","a406","a407","a408","a409","a410","a411","a412","a413","a414","a415","a416","a417","a418","a419","a420","a421","a422","a423","a424","a425","a426","a427","a428","a429","a430","a431","a432","a433","a434","a435","a436","a437","a438","a439","a440","a441","a442","a443","a444","a445","a446","a447","a448","a449","a450","a451","a452","a453","a454","a455","a456","a457","a458","a459","a460","a461","a462","a463","a464","a465","a466","a467","a468","a469","a470","a471","a472","a473","a474","a475","a476","a477","a478","a479","a480","a481","a482","a483","a484","a485","a486","a487","a488","a489","a490","a491","a492","a493","a494","a495","a496","a497","a498","a499","a500","a501","a502","a503","a504","a505","a506","a507","a508","a509","a510","a511","a512","a513","a514","a515","a516","a517","a518","a519","a520","a521","a522","a523","a524","a525","a526","a527","a528","a529","a530","a531","a532","a533","a534","a535","a536","a537","a538","a539","a540","a541","a542","a543","a544","a545","a546","a547","a548","a549","a550","a551","a552","a553","a554","a555","a556","a557","a558","a559","a560","a561","a562","a563","a564","a565","a566","a567","a568","a569","a570","a571","a572","a573","a574","a575","a576","a577","a578","a579","a580","a581","a582","a583","a584","a585","a586","a587","a588","a589","a590","a591","a592","a593","a594","a595","a596","a597","a598","a599","a600","a601","a602","a603","a604","a605","a606","a607","a608","a609","a610","a611","a612","a613","a614","a615","a616","a617","a618","a619","a620","a621","a622","a623","a624","a625","a626","a627","a628","a629","a630","a631","a632","a633","a634","a635","a636","a637","a638","a639","a640","a641","a642","a643","a644","a645","a646","a647","a648","a649","a650","a651","a652","a653","a654","a655","a656","a657","a658","a659","a660","a661","a662","a663","a664","a665","a666","a667","a668","a669","a670","a671","a672","a673","a674","a675","a676","a677","a678","a679","a680","a681","a682","a683","a684","a685","a686","a687","a688","a689","a690","a691","a692","a693","a694","a695","a696","a697","a698","a699","a700","a701","a702","a703","a704","a705","a706","a707","a708","a709","a710","a711","a712","a713","a714","a715","a716","a717","a718","a719","a720","a721","a722","a723","a724","a725","a726","a727","a728","a729","a730","a731","a732","a733","a734","a735","a736","a737","a738","a739","a740","a741","a742","a743","a744","a745","a746","a747","a748","a749","a750","a751","a752","a753","a754","a755","a756","a757","a758","a759","a760","a761","a762","a763","a764","a765","a766","a767","a768","a769","a770","a771","a772","a773","a774","a775","a776","a777","a778","a779","a780","a781","a782","a783","a784","a785","a786","a787","a788","a789","a790","a791","a792","a793","a794","a795","a796","a797","a798","a799","a800","a801","a802","a803","a804","a805","a806","a807","a808","a809","a810","a811","a812","a813","a814","a815","a816","a817","a818","a819","a820","a821","a822","a823","a824","a825","a826","a827","a828","a829","a830","a831","a832","a833","a834","a835","a836","a837","a838","a839","a840","a841","a842","a843","a844","a845","a846","a847","a848","a849","a850","a851","a852","a853","a854","a855","a856","a857","a858","a859","a860","a861","a862","a863","a864","a865","a866","a867","a868","a869","a870","a871","a872","a873","a874","a875","a876","a877","a878","a879","a880","a881","a882","a883","a884","a885","a886","a887","a888","a889","a890","a891","a892","a893","a894","a895","a896","a897","a898","a899","a900","a901","a902","a903","a904","a905","a906","a907","a908","a909","a910","a911","a912","a913","a914","a915","a916","a917","a918","a919","a920","a921","a922","a923","a924","a925","a926","a927","a928","a929","a930","a931","a932","a933","a934","a935","a936","a937","a938","a939","a940","a941","a942","a943","a944","a945","a946","a947","a948","a949","a950","a951","a952","a953","a954","a955","a956","a957","a958","a959","a960","a961","a962","a963","a964","a965","a966","a967","a968","a969","a970","a971","a972","a973","a974","a975","a976","a977","a978","a979","a980","a981","a982","a983","a984","a985","a986","a987","a988","a989","a990","a991","a992","a993","a994","a995","a996","a997","a998","a999","a1000"};


fstream f;
f.open("efficient_ABACE.csv",ios::out|ios::app);
f<<"Number of Attributes,Setup,Encrytion key generation,Decrytion key generation,Encryption,Sanitization,Decrytion"<<endl;

for(int iter_i =0;iter_i<1;iter_i++)
{
    int count=1000;
    f<<count<<",";
    cout<<"test--------------"<<iter_i<<"--------------"<<endl;
    clock_t start,end;
 

	// start=clock();		//程序开始计时
	

//————————————————————————————————初始化——————————————————————————————————————
    hash<string> h_func;
    pairing_t pairing;

    char file[]="f.param";
    pbc_pairing_init(pairing, file);

    //程序开始计时
    start=clock();	

    int x=rand();
    int y=rand();
    //g,h are the generator of two groups
    element_t g;
    element_t h;
    element_init_G1(g, pairing);
    element_init_G2(h, pairing);

    // string attribute[3][4] = 
    // {{"hust","whu","whut"},
    // {"cse","cs","se","ai"},
    // {"bachelor","master","doctor"},
    // };
    string attribute[count];

    for(int i=0;i<count;i++)
    {
        attribute[i]=universe[i];
        // cout<<attribute[i]<<endl;
    }



    map<string, pair<element_t,element_t>> map_attribute;

    init(x,y,g,h,map_attribute,pairing,h_func,attribute,count);

    //签名算法初始化
    element_t p,H,X,sign_v,sign_V;
    sign_setup(p,H,X,sign_v,sign_V,pairing);

    //程序结束用时
	end=clock();		
	double endtime1=(double)(end-start)/CLOCKS_PER_SEC;
	cout<<"setup Total time:"<<endtime1*1000<<"ms"<<endl;	//ms为单位
    f<<endtime1*1000<<",";
//---------------------计时-----------------


     //————————————————————————————————生成用户的加密密钥——————————————————————————————————————
        //---------------------计时-----------------
    //程序开始计时
    start=clock();	

    element_t xw,yw;
    
    string policyW[count];
    for(int i=0;i<count;i++)
    {
        policyW[i]=universe[i];
        // cout<<policyW[i]<<endl;
    }

    enc_keygen(xw,yw,map_attribute,policyW,count,pairing);

    element_t R_xw,S_xw,T_xw,W_xw,R_yw,S_yw,T_yw,W_yw;
    element_init_G2(R_xw, pairing);
    element_init_G1(S_xw, pairing);
    element_init_G1(T_xw, pairing);
    element_init_G1(W_xw, pairing);
    element_init_G2(R_yw, pairing);
    element_init_G1(S_yw, pairing);
    element_init_G1(T_yw, pairing);
    element_init_G1(W_yw, pairing);

    //对xw、yw进行签名
    sign(xw,g,H,R_xw,S_xw,T_xw,W_xw,sign_v,X,pairing);
//     // sign(yw,g,H,R_yw,S_yw,T_yw,W_yw,sign_v,X,pairing);

    //程序结束用时
	end=clock();		
	double endtime2=(double)(end-start)/CLOCKS_PER_SEC;
	cout<<"encryption key generation Total time:"<<endtime2*1000<<"ms"<<endl;	//ms为单位
    f<<endtime2*1000<<",";
//---------------------计时-----------------



    //————————————————————————————————生成用户的解密密钥——————————————————————————————————————
    //定义用户属性列表，但是将string二维数组传到函数中，需要下面的步骤声明一个指向二维数组的指针ss  
    //---------------------计时-----------------
    //程序开始计时
    start=clock();	


    string attribute_list[count];
    for(int i=0;i<count;i++)
    {
        attribute_list[i]=universe[i];
        // cout<<attribute_list[i]<<endl;
    }
         
    int sk;
    element_t sigma[count];

    keygen(sk,sigma,pairing,x,y,h,attribute_list,attribute,h_func,count);


    //程序结束用时
	end=clock();		
	double endtime3=(double)(end-start)/CLOCKS_PER_SEC;
	cout<<"decryption key generation Total time:"<<endtime3*1000<<"ms"<<endl;	//ms为单位
    f<<endtime3*1000<<",";
//---------------------计时-----------------



// // //————————————————————————————————加密部分——————————————————————————————————————

    //---------------------计时-----------------
    //程序开始计时
    start=clock();	
// //首先对xw，yw进行隐藏，也就是指数上进行r次方，得到xw_r,yw_r
    element_t r,xw_r,yw_r;
    element_init_Zr(r,pairing);
    element_init_G1(xw_r,pairing);
    element_init_GT(yw_r,pairing);
    element_random(r);

    element_pow_zn(xw_r,xw,r);
    element_pow_zn(yw_r,yw,r);
//然后对xw，yw的签名sigma进行rand算法，得到xw_r,yw_r的签名sigma'
    element_t R_xw_r,S_xw_r,T_xw_r,R_yw_r,S_yw_r,T_yw_r;
    element_init_G2(R_xw_r, pairing);
    element_init_G1(S_xw_r, pairing);
    element_init_G1(T_xw_r, pairing);
    element_init_G2(R_yw_r, pairing);
    element_init_G1(S_yw_r, pairing);
    element_init_G1(T_yw_r, pairing);

    sign_rand(r,R_xw,S_xw,T_xw,W_xw,R_xw_r,S_xw_r,T_xw_r,pairing);
    sign_rand(r,R_xw,S_xw,T_xw,W_xw,R_xw_r,S_xw_r,T_xw_r,pairing);

    //计算V^(1/r)用于对xw_r,yw_r进行验证,r1是1/r
    element_t sign_V_r1,r1;
    element_init_G2(sign_V_r1, pairing);
    element_init_Zr(r1,pairing);
    element_invert(r1,r);
    element_pow_zn(sign_V_r1,sign_V,r1);

//ABE加密，对M进行加密，并将之前用的随机数r传入，用于计算g^r，同时g^r需要作为零知识证明的元素返回
    element_t g_r;
    element_init_G1(g_r,pairing);
    element_pow_zn(g_r, g, r);
    //t和s是用于加密的随机数，也需要用于零知识证明
    element_t t,s;
    element_init_Zr(t,pairing);
    element_random(t);
    element_init_Zr(s,pairing);
    element_random(s);

    element_t c_0,c_1,c_2;
    element_init_GT(c_0,pairing);
    element_init_G1(c_1,pairing);
    element_init_G1(c_2,pairing);
    element_t c_00,c_11,c_22;
    element_init_GT(c_00,pairing);
    element_init_G1(c_11,pairing);
    element_init_G1(c_22,pairing);

    element_t M;
    element_init_GT(M,pairing);
    element_random(M);
    // element_printf("plaintext\n%B\n",M);

    encrypt(g_r,t,s,xw_r,yw_r,c_0,c_1,c_2,c_00,c_11,c_22,pairing,M,g);
//零知识证明
    element_t t1,t2,nizk_s1;
    element_init_G1(t1,pairing);
    element_init_G1(t2,pairing);
    element_init_Zr(nizk_s1,pairing);

    element_t t3,t4,t5,nizk_s2;
    element_init_G1(t3,pairing);
    element_init_G1(t4,pairing);
    element_init_G1(t5,pairing);
    element_init_Zr(nizk_s2,pairing);

    //生成证明
    prove(nizk_s1, t1, t2,  g_r, xw_r, c_1, c_2, t,  pairing );

    // prove(nizk_s2, t3, t4,t5, g_r, xw_r, yw_r,c_11, c_22,c_00, s,  pairing );


   
    //程序结束用时
	end=clock();		
	double endtime4=(double)(end-start)/CLOCKS_PER_SEC;
	cout<<"encryption Total time:"<<endtime4*1000<<"ms"<<endl;	//ms为单位
    f<<endtime4*1000<<",";
//---------------------计时-----------------


//————————————————————————————————净化部分——————————————————————————————————————
    //---------------------计时-----------------
    //程序开始计时
    start=clock();	

    //签名验证
    vfy(xw_r,R_xw_r,S_xw_r,T_xw_r,sign_V,sign_V_r1,X,g,H,pairing);
    // cout<<"xw_r verification result: "<<vfy(xw_r,R_xw_r,S_xw_r,T_xw_r,sign_V,sign_V_r1,X,g,H,pairing)<<endl;
    // cout<<"yw verification result:"<<vfy(yw,R_yw,S_yw,T_yw,sign_V,X,g,H,pairing)<<endl;

    // 零知识证明验证
    verify(nizk_s1, t1, t2,  g_r, xw_r,c_1, c_2, pairing);
    // cout<<"NIZK_1 verification result: "<<verify(nizk_s1, t1, t2,  g_r, xw_r,c_1, c_2, pairing)<<endl;
//     cout<<"NIZK_2 verification result: "<<verify(nizk_s2, t3, t4,t5, g_r, xw_r, yw_r,c_11, c_22,c_00, pairing)<<endl;
    
    element_t C_0,C_1,C_2;
    element_init_GT(C_0,pairing);
    element_init_G1(C_1,pairing);
    element_init_G1(C_2,pairing);
    sanitization(C_0,C_1,C_2,c_0,c_1,c_2,c_00,c_11,c_22,pairing);

    //程序结束用时
	end=clock();		
	double endtime5=(double)(end-start)/CLOCKS_PER_SEC;
	cout<<"sanitization Total time:"<<endtime5*1000<<"ms"<<endl;	//ms为单位
    f<<endtime5*1000<<",";
//---------------------计时-----------------


// //————————————————————————————————解密部分——————————————————————————————————————
//     // 其中dtemp1是分母下面左边的双线性映射结果，dtemp2是分母下面左边的双线性映射结果
//     //dtemp3是H1(sk), dtemp4是两个双线性映射相乘的结果
    //---------------------计时-----------------
    //程序开始计时
    start=clock();	

    element_t Mresult;
    element_init_GT(Mresult,pairing);

    decrypt(Mresult,pairing,sk,sigma,C_0,C_1,C_2,count);
    // element_printf("massage\n%B\n",M);
    // element_printf("decryption\n%B\n",Mresult);



    //程序结束用时
	end=clock();		
	double endtime6=(double)(end-start)/CLOCKS_PER_SEC;
	cout<<"decryption Total time:"<<endtime6*1000<<"ms"<<endl;	//ms为单位
    f<<endtime6*1000<<endl;
//---------------------计时-----------------
        cout<<"--------------finished--------------"<<endl;
}
    f.close();
}

}