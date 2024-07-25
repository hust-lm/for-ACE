#include <iostream>
#include "/usr/local/include/pbc/pbc.h"
#include <map>
#include <cstring>
#include <cstdlib>
#include <set>
#include<vector>
#include <time.h>   
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
        element_mul(temp,x,c);
        element_add(s,r,temp);

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
    void get_position(int&x, int&y,string target,string * attribute[],int m, int n)
    {
        for (int i=0;i<m;i++)
        {
            for (int j=0;j<n;j++)
            {
                if (target==attribute[i][j])
                {
                    x=i+1;
                    y=j+1;
                    return ;
                }
            }
        }
    }

    void init(int&x, int&y, element_t g, map<string, pair<element_t,element_t>> &map_attribute, pairing_t pairing, hash<string> h,string * attribute[], int m, int n)
    {

        element_t temp1, temp2,temp3;
        element_t temp_x[3][4],temp_y[3][4];
        element_init_Zr(temp1, pairing);
        element_init_Zr(temp2, pairing);
        element_init_GT(temp3, pairing);
        element_random(g);


        //map存入<属性，pair<X,Y>>
        for(int i =0;i<3;i++)
        {
            for (int j =0;j<4;j++)
            {
                if (attribute[i][j]=="")
                {continue;}

                element_init_G1(temp_x[i][j], pairing);
                element_init_GT(temp_y[i][j], pairing);

                //首先分别计算每个属性对应的X和Y
                string s1=to_string(h(Binary(x)+Binary(i+1)+Binary(j+1)));
                char c1[50];
                strcpy(c1,s1.c_str());

                string s2=to_string(h(Binary(y)+Binary(i+1)+Binary(j+1)));
                char c2[50];
                strcpy(c2,s2.c_str());

                element_from_hash(temp1, c1, s1.size());
                element_neg(temp2,temp1);
                element_pow_zn(temp_x[i][j], g, temp2);

                element_from_hash(temp1, c2, s2.size());
                pairing_apply(temp3, g, g, pairing);
                element_pow_zn(temp_y[i][j], temp3, temp1);
                
                //将属性和对应X、Y建立映射，存入map中
                map_attribute[attribute[i][j]].first->data = temp_x[i][j]->data;
                map_attribute[attribute[i][j]].first->field = temp_x[i][j]->field;
                map_attribute[attribute[i][j]].second->data = temp_y[i][j]->data;
                map_attribute[attribute[i][j]].second->field = temp_y[i][j]->field;
            }
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

    void enc_keygen(element_t xw,element_t yw,map<string, pair<element_t,element_t>> map_attribute,string policyW[],pairing_t pairing){
        element_init_G1(xw,pairing);        
        element_init_GT(yw,pairing);
        element_set1(xw);
        element_set1(yw);

        //连乘生成xw、yw
        for(int i=0;i<3;i++){
            element_mul(xw,xw,map_attribute[policyW[i]].first);
            element_mul(yw,yw,map_attribute[policyW[i]].second);
        }
    }

    void keygen(int sk,element_t sigma[], pairing_t pairing, int x, int y, element_t g,string attribute_list[], string *ss[],hash<string> h)
        //ktemp1、2是上面的指数，ktemp3是前面g^H0的结果，ktemp4是H1(sk)，ktemp5是H1(sk)^H0的结果
    {
        element_t ktemp1,ktemp2,ktemp3,ktemp4,ktemp5;
        element_init_Zr(ktemp1,pairing);
        element_init_Zr(ktemp2,pairing);
        element_init_G1(ktemp3,pairing);
        element_init_G1(ktemp4,pairing);
        element_init_G1(ktemp5,pairing);

        //定义用户属性列表，但是将string二维数组传到函数中，需要下面的步骤声明一个指向二维数组的指针ss  

            

        for(int i =0;i<3;i++)
        {
                int a,b;
                get_position(a,b,attribute_list[i],ss,3,4);

                //计算第一部分
                string s3=to_string(h(Binary(y)+Binary(a)+Binary(b)));
                char c3[50];
                strcpy(c3,s3.c_str());
                element_from_hash(ktemp1, c3, s3.size());
                element_pow_zn(ktemp3,g,ktemp1);

                //计算第二部分指数
                string s4=to_string(h(Binary(x)+Binary(a)+Binary(b)));
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
                element_init_G1(sigma[i],pairing);
                element_mul(sigma[i],ktemp3,ktemp5);
        }
    }

    void encrypt(element_t g_r,element_t t,element_t s,element_t xw_r,element_t yw_r,element_t c_0,element_t c_1,element_t c_2 ,element_t c_00,element_t c_11,element_t c_22,pairing_t pairing,element_t M, element_t g)
    {

        //生成密文c0,c1,c2。明文m的类型应该是G1或者Zr都可以，这里定义为G1,也可以是自己指定的整数Zr

        element_t mtemp;

        element_init_G1(mtemp,pairing);
  

        element_pow_zn(mtemp, yw_r, t);
        element_mul(c_0,M,mtemp);
        element_pow_zn(c_1, g_r, t);
        element_pow_zn(c_2, xw_r, t);

        element_pow_zn(c_00, yw_r, s);
        element_pow_zn(c_11, g_r, s);
        element_pow_zn(c_22, xw_r, s);

    }

    void sanitization(element_t C_0,element_t C_1,element_t C_2 ,element_t c_0,element_t c_1,element_t c_2 ,element_t c_00,element_t c_11,element_t c_22,pairing_t pairing){
        element_t s_r1,temp;
        element_init_G1(temp,pairing);
        element_init_Zr(s_r1,pairing);
        element_random(s_r1);

        element_pow_zn(temp,c_00,s_r1);
        element_mul(C_0,c_0,temp);
        element_pow_zn(temp,c_11,s_r1);
        element_mul(C_1,c_1,temp);
        element_pow_zn(temp,c_22,s_r1);
        element_mul(C_2,c_2,temp);

    }

    void decrypt(element_t Mresult,pairing_t pairing,int sk,element_t sigma[],element_t c_0,element_t c_1,element_t c_2 )
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
        
        element_init_G1(sigma_w,pairing);
        element_init_GT(dtemp1,pairing);
        element_init_GT(dtemp2,pairing);
        element_init_G1(dtemp3,pairing);
        element_init_GT(dtemp4,pairing);

        //sigma_w的值设置为1
        element_set1(sigma_w);

        //计算H1(sk)
        string s_sk=to_string(sk);
        char c6[50];
        strcpy(c6,s_sk.c_str());
        element_from_hash(dtemp3,c6,s_sk.size());

        //sigma_w就是用户的所有私钥连乘的结果
        for (int i=0;i<3;i++)
        {
            element_mul(sigma_w,sigma_w,sigma[i]);
        }

        //计算最后的等式
        pairing_apply(dtemp1,sigma_w,c_1,pairing);
        pairing_apply(dtemp2,dtemp3,c_2,pairing);
        element_mul(dtemp4,dtemp1,dtemp2);
        element_div(Mresult,c_0,dtemp4);
        // element_printf("%B\n",Mresult);
    }





int main(){




clock_t start,end;
 

	// start=clock();		//程序开始计时
	

//————————————————————————————————初始化——————————————————————————————————————
    hash<string> h;
    pairing_t pairing;

    char file[]="a.param";
    pbc_pairing_init(pairing, file);

    int x=rand();
    int y=rand();
    element_t g;
    element_init_G1(g, pairing);

    string attribute[3][4] = 
    {{"hust","whu","whut"},
    {"cse","cs","se","ai"},
    {"bachelor","master","doctor"},
    };
    string *ss[3];
    for (int i = 0; i < 3; i++)
    {
        ss[i]=attribute[i];
    }

    int m=4;
    map<string, pair<element_t,element_t>> map_attribute;

    init(x,y,g,map_attribute,pairing,h,ss,3,4);

    //签名算法初始化
    element_t p,H,X,sign_v,sign_V;
    sign_setup(p,H,X,sign_v,sign_V,pairing);


     //————————————————————————————————生成用户的加密密钥——————————————————————————————————————

    element_t xw,yw;
    
    string policyW[3]={"hust","cs","master"};

    enc_keygen(xw,yw,map_attribute,policyW,pairing);

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
    sign(yw,g,H,R_yw,S_yw,T_yw,W_yw,sign_v,X,pairing);

    //————————————————————————————————生成用户的解密密钥——————————————————————————————————————
    //定义用户属性列表，但是将string二维数组传到函数中，需要下面的步骤声明一个指向二维数组的指针ss  
    string attribute_list[3]={"hust","cs","master"};
         
    int sk;
    element_t sigma[3];

    keygen(sk,sigma,pairing,x,y,g,attribute_list,ss,h);


//————————————————————————————————加密部分——————————————————————————————————————
//首先对xw，yw进行隐藏，也就是指数上进行r次方，得到xw_r,yw_r
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
    element_init_G1(c_0,pairing);
    element_init_G1(c_1,pairing);
    element_init_G1(c_2,pairing);
    element_t c_00,c_11,c_22;
    element_init_G1(c_00,pairing);
    element_init_G1(c_11,pairing);
    element_init_G1(c_22,pairing);

    element_t M;
    element_init_G1(M,pairing);
    element_random(M);
    element_printf("plaintext\n%B\n",M);

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

    prove(nizk_s2, t3, t4,t5, g_r, xw_r, yw_r,c_11, c_22,c_00, s,  pairing );

    //-----------------------------------计时------------------------------
    //首先对xw，yw进行隐藏，也就是指数上进行r次方，得到xw_r,yw_r
    //程序开始计时
    start=clock();	
    for (int i =0;i<100;i++)
    {
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
    element_init_G1(c_0,pairing);
    element_init_G1(c_1,pairing);
    element_init_G1(c_2,pairing);
    element_t c_00,c_11,c_22;
    element_init_G1(c_00,pairing);
    element_init_G1(c_11,pairing);
    element_init_G1(c_22,pairing);

    element_t M;
    element_init_G1(M,pairing);
    element_random(M);

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

    prove(nizk_s2, t3, t4,t5, g_r, xw_r, yw_r,c_11, c_22,c_00, s,  pairing );
    }
    //程序结束用时
	end=clock();		
	double endtime=(double)(end-start)/CLOCKS_PER_SEC;
	cout<<"encryption Total time:"<<endtime*1000<<"ms"<<endl;	//ms为单位
    


//————————————————————————————————净化部分——————————————————————————————————————
    element_t C_0,C_1,C_2;
    element_init_G1(C_0,pairing);
    element_init_G1(C_1,pairing);
    element_init_G1(C_2,pairing);


    // vfy(xw_r,xw_result,R_xw_r,S_xw_r,T_xw_r,sign_V,X,g,H,pairing);
    // vfy(yw_r,yw_result,R_yw_r,S_yw_r,T_yw_r,sign_V,X,g,H,pairing);

    //签名验证
    cout<<"xw_r verification result: "<<vfy(xw_r,R_xw_r,S_xw_r,T_xw_r,sign_V,sign_V_r1,X,g,H,pairing)<<endl;
    // cout<<"yw verification result:"<<vfy(yw,R_yw,S_yw,T_yw,sign_V,X,g,H,pairing)<<endl;

    // 零知识证明验证
    cout<<"NIZK_1 verification result: "<<verify(nizk_s1, t1, t2,  g_r, xw_r,c_1, c_2, pairing)<<endl;
    cout<<"NIZK_2 verification result: "<<verify(nizk_s2, t3, t4,t5, g_r, xw_r, yw_r,c_11, c_22,c_00, pairing)<<endl;

    // if(xw_result){
    // if(yw_result){
    // cout<<"vfy successful!"<<endl;
    sanitization(C_0,C_1,C_2,c_0,c_1,c_2,c_00,c_11,c_22,pairing);
    //}
    // }else cout<<"vfy x!"<<endl;

// //---------------------计时-----------------
//     //程序开始计时
//     start=clock();	
//     for (int i =0;i<100;i++)
//     {
//     element_t C_0,C_1,C_2;
//     element_init_G1(C_0,pairing);
//     element_init_G1(C_1,pairing);
//     element_init_G1(C_2,pairing);

//     vfy(xw_r,R_xw_r,S_xw_r,T_xw_r,sign_V,sign_V_r1,X,g,H,pairing);
//     // cout<<"yw verification result:"<<vfy(yw,R_yw,S_yw,T_yw,sign_V,X,g,H,pairing)<<endl;

//     // 零知识证明验证
//     verify(nizk_s1, t1, t2,  g_r, xw_r,c_1, c_2, pairing);
//     verify(nizk_s2, t3, t4,t5, g_r, xw_r, yw_r,c_11, c_22,c_00, pairing);
//     sanitization(C_0,C_1,C_2,c_0,c_1,c_2,c_00,c_11,c_22,pairing);
//     }
//     //程序结束用时
// 	end=clock();		
// 	double endtime=(double)(end-start)/CLOCKS_PER_SEC;
// 	cout<<"Total time:"<<endtime*1000<<"ms"<<endl;	//ms为单位
// //---------------------计时-----------------



//————————————————————————————————解密部分——————————————————————————————————————
    // 其中dtemp1是分母下面左边的双线性映射结果，dtemp2是分母下面左边的双线性映射结果
    //dtemp3是H1(sk), dtemp4是两个双线性映射相乘的结果

    element_t Mresult;
    element_init_G1(Mresult,pairing);

    decrypt(Mresult,pairing,sk,sigma,c_0,c_1,c_2);
    element_printf("decryption\n%B\n",Mresult);

// //---------------------计时-----------------
//     //程序开始计时
//     start=clock();	
//     for (int i =0;i<100;i++)
//     {
//     element_t Mresult;
//     element_init_G1(Mresult,pairing);

//     decrypt(Mresult,pairing,sk,sigma,c_0,c_1,c_2);
//     }
//     //程序结束用时
// 	end=clock();		
// 	double endtime=(double)(end-start)/CLOCKS_PER_SEC;
// 	cout<<"Total time:"<<endtime*1000<<"ms"<<endl;	//ms为单位
// //---------------------计时-----------------


    // cout<<"pyj"<<endl;




}