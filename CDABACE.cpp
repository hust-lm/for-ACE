#include <iostream>
#include <fstream>
#include "/usr/local/include/pbc/pbc.h"
#include <map>
#include <cstring>
#include <cstdlib>
#include <set>
#include<vector>
#include <time.h>   
using namespace std;

#define RUN_TIMES 10

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
//计算s
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
    element_t g_s,h_s,y_c,z_c,temp1,temp2,c;

    element_init_G2(g_s,pairing);
    element_init_G1(h_s,pairing);
    element_init_G2(y_c,pairing);
    element_init_G1(z_c,pairing);
    element_init_G2(temp1,pairing);
    element_init_G1(temp2,pairing);
    element_init_Zr(c,pairing);

    cal_hash(c,g,h,y,z,t1,t2,pairing);
    

    //计算并判断是否相等

    element_pow_zn(y_c,y,c);
    element_pow_zn(z_c,z,c);
    element_pow_zn(g_s,g,s);
    element_pow_zn(h_s,h,s);
    element_mul(temp1,y_c,t1);
    element_mul(temp2,z_c,t2);

    if((element_cmp(g_s,temp1)==0)&&(element_cmp(h_s,temp2)==0))
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

void c(element_t a[],element_t b[],int n, int m,const int M,element_t &sum,pairing_t pairing)
{

	if (m>0)
	{
		for (int i =n;i>=m;i--)
		{
            element_set(b[m-1],a[i-1]);
			//由于确定了当前位置的值
			//则下次递归c(n-1,m-1) 
			c(a,b,i-1,m-1,M,sum,pairing);
		}
	}
	else 
	{
        element_t tempx;
        element_init_Zr(tempx,pairing);
        element_set_si(tempx,1);

		for(int i =0 ; i<M;i++)
        {
			// cout<<b[i]<<" ";
            // x=x*b[i];
            element_mul(tempx,tempx,b[i]);
        }
            // cout<<x<<endl;
            // sum=sum+x;
            element_add(sum,sum,tempx);
			// cout<<endl; 

	} 
}


void cal_coeffficent(element_t arr[], int n, element_t result[],pairing_t pairing)
{
    element_t b[n];

    element_t sum;
    element_init_Zr(sum,pairing);
    element_set_si(sum,0);

    for(int i=0;i<n;i++)
    {
        element_init_Zr(b[i],pairing);
    }

    // for (int i=n;i>=0;i-- )
    // {
    //     c(arr,b,n,i,i,sum,pairing); 
    //     // cout<<sum<<endl;
    //     // if(sum>0) cout<<"+"; 
    //     // cout<<sum<<"x^("<<n-i<<")";
        
    //     element_set(result[n-i],sum);
    //     // result[n-i]=sum;
    //     // sum=0;
    //     element_set_si(sum,0);
    // }

        for (int i=0;i<=n;i++ )
    {

        c(arr,b,n,n-i,n-i,sum,pairing); 
        // cout<<sum<<endl;
        // if(sum>0) cout<<"+"; 
        // cout<<sum<<"x^("<<n-i<<")";
        
        element_set(result[i],sum);
        // result[n-i]=sum;
        // sum=0;
        element_set_si(sum,0);
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


void Z_polynomial(element_t result,element_t x,int n,element_t k[],int b[],pairing_t pairing){

    element_t temp3,temp4,temp5;
    element_init_Zr(temp3, pairing);
    element_init_Zr(temp4, pairing);
    element_init_Zr(temp5, pairing);
    int sign;

    for (int i=0;i<n;i++)
    {
        element_sub(temp3,x,k[i]);
        if(b[i]==1)sign=0;
        else sign=1;
        element_set_si(temp4,sign);
        element_pow_zn(temp5,temp3,temp4);
        element_mul(result,result,temp5);
    }
    return ;
}

void dec_keygen(element_t dk ,pairing_t pairing,element_t alpha,element_t g_1,element_t k[],int b[],int count)
{
    element_t result;
    element_t temp6,temp7;
    element_init_Zr(result, pairing);
    element_init_Zr(temp6, pairing);
    element_init_Zr(temp7, pairing);

    element_set1(result);
    element_set1(temp7);

    Z_polynomial(result,alpha,count,k,b,pairing);

    element_div(temp6,temp7,result);
    element_pow_zn(dk,g_1,temp6);
}

void enc_keygen(element_t ek,int& temp_len, pairing_t pairing,element_t alpha,element_t g_2,element_t k[],int p[],int count)
{


    element_t test[2];
    element_t z[count+1];
    element_t sum;

    element_t etemp1,etemp2;

    element_init_Zr(sum,pairing);

    element_init_Zr(etemp1,pairing);
    element_init_Zr(etemp2,pairing);
    element_set1(etemp1);


    //test ki
    //     for(int i=0;i<4;i++)
    // {
    //     element_set_si(k[i],i+1);
    // }
    for(int i=0;i<count;i++)
    {
        if(p[i]==0)
        {
            element_init_Zr(test[temp_len],pairing);
            element_set(test[temp_len],k[i]);
            element_neg(test[temp_len],test[temp_len]);

            // element_printf("%B\n",k[i]);
            // element_printf("%B\n",test[temp_len]);
            temp_len++;

        }
    }

    // element_mul(sum,test[0],test[1]);

    for(int i=0;i<count+1;i++)
    {
        element_init_Zr(z[i],pairing);
        element_set_si(z[i],0);
    }
    cal_coeffficent(test,2,z,pairing);
    // for(int i=0;i<5;i++)
    // {
    //     cout<<"z["<<i<<"]="<<endl;
    //     element_printf("%B\n",z[i]);
    // }

    Z_polynomial(etemp1,alpha,count,k,p,pairing);
    element_mul(etemp2,alpha,etemp1);
    element_pow_zn(ek,g_2,etemp2);
    // element_printf("%B\n",etemp1);
    // element_printf("%B\n",etemp2);
    // element_printf("%B\n",ek);
}

void encryption(element_t r,element_t C,element_t C_1,element_t C_2,pairing_t pairing,element_t M,element_t alpha, element_t g_t,element_t ek,element_t g2)
{



    element_t ctemp1,ctemp2,ctemp3,ctemp4;
    element_init_Zr(ctemp1, pairing);
    element_init_GT(ctemp2, pairing);
    element_init_Zr(ctemp3, pairing);

    //计算C
    element_mul(ctemp1,r,alpha);
    element_pow_zn(ctemp2,g_t,ctemp1);
    element_mul(C,M,ctemp2);

    //计算C1
    element_pow_zn(C_1,ek,r);

    //计算C2
    element_neg(ctemp3,r);
    element_pow_zn(C_2,g2,ctemp3);

}

void sanitization(element_t Cs,element_t C_1s,element_t C_2s,element_t s,element_t gt_alpha,element_t ek,element_t g2,element_t C,element_t C_1,element_t C_2,pairing_t pairing)
{
    element_t neg_s,s_temp1,s_temp2,s_temp3;

    element_init_Zr(neg_s,pairing);
    element_init_GT(s_temp1,pairing);
    element_init_G2(s_temp2,pairing);
    element_init_G1(s_temp3,pairing);

    element_random(s);
    element_pow_zn(s_temp1,gt_alpha,s);
    element_mul(Cs,C,s_temp1);

    element_pow_zn(s_temp2,ek,s);
    element_mul(C_1s,C_1,s_temp2);

    element_neg(neg_s,s);
    element_pow_zn(s_temp3,g2,neg_s);
    element_mul(C_2s,C_2,s_temp3);
}

void decryption(element_t dec,pairing_t pairing, element_t attribute_value[],  element_t k[] ,element_t dk,int b[], int p[],int temp_len,element_t C,element_t C_1,element_t C_2,int count)
{
 int c[count];
    for(int i=0;i<count;i++)
    {
        c[i]=b[i]-p[i];
    }

    element_t dtest[1];
    element_t f[count+1];
    element_t dtemp1,dtemp2,dtemp3,dtemp4,dtemp5;
    element_t hf;
    element_t expo;


    element_init_G2(dtemp1,pairing);
    element_init_GT(dtemp2,pairing);
    element_init_GT(dtemp3,pairing);
    element_init_GT(dtemp4,pairing);
    element_init_GT(dtemp5,pairing);
    element_init_G2(hf,pairing);
    element_init_Zr(expo,pairing);
    element_init_GT(dec,pairing);

    element_set1(hf);
    element_set1(dtemp1);
    temp_len=0;


    for(int i=0;i<count;i++)
    {
        if(c[i]==1)
        {
            element_init_Zr(dtest[temp_len],pairing);
            element_set(dtest[temp_len],k[i]);
            element_neg(dtest[temp_len],dtest[temp_len]);
            temp_len++;

        }
    }

    for(int i=0;i<count+1;i++)
    {
        element_init_Zr(f[i],pairing);
        element_set_si(f[i],0);
    }

    cal_coeffficent(dtest,1,f,pairing);

    // for(int i=0;i<5;i++)
    // {
    //     cout<<"f["<<i<<"]="<<endl;
    //     element_printf("%B\n",f[i]);
    // }


    for(int i=0;i<count;i++)
    {
        element_pow_zn(dtemp1,attribute_value[i],f[i+1]);
        element_mul(hf,hf,dtemp1);
        // element_printf("%B\n",hf);
    }

    pairing_apply(dtemp2,C_2,hf,pairing);
    // element_printf("%B\n",dtemp2);

    pairing_apply(dtemp3,dk,C_1,pairing);
    // element_printf("%B\n",dtemp3);

    element_mul(dtemp4,dtemp2,dtemp3);
    // element_printf("%B\n",dtemp4);

    // element_printf("%B\n",f[0]);
    element_invert(expo,f[0]);
    // element_printf("%B\n",expo);
    element_neg(expo,expo);
    // element_printf("%B\n",expo);
    element_pow_zn(dtemp5,dtemp4,expo);
    // element_printf("%B\n",dtemp5);

    element_mul(dec,C,dtemp5);



}

void setup(string attribute[],element_t alpha,element_t g2,element_t g_1,element_t g_2,element_t g_t,element_t attribute_value[],element_t gt_alpha,element_t k[],int count,pairing_t pairing){

    element_t temp1,temp2;

    element_init_G1(g_1, pairing);
    element_init_G2(g_2, pairing);
    element_init_GT(g_t, pairing);
    element_random(g_1);
    element_random(g_2);
    element_init_Zr(alpha, pairing);
    element_random(alpha);
    element_init_G1(g2, pairing);

    element_init_Zr(temp1, pairing);
    element_init_Zr(temp2, pairing);
    element_init_GT(gt_alpha, pairing);
    pairing_apply(g_t,g_1,g_2,pairing);

        //计算属性全集对应的值
    for(int i=0;i<=count;i++){
        element_set_si(temp1,i);
        element_init_G2(attribute_value[i], pairing);
        element_pow_zn(temp2, alpha, temp1);
        element_pow_zn(attribute_value[i], g_2, temp2);
    }
    //计算ki
    for(int i=0;i<count;i++){
        char c1[1000];
        strcpy(c1,attribute[i].c_str());
        element_init_Zr(k[i], pairing);
        element_from_hash(k[i], c1, attribute[i].size());
        // element_printf("%B\n",k[i]);
    }

    //计算初始化所需参数
        element_set_si(temp1,2);
        element_pow_zn(temp2, alpha, temp1);
        element_pow_zn(g2, g_1, temp2);
        element_pow_zn(gt_alpha, g_t, alpha);
    }

void sign_setup(element_t alpha,element_t g_1,element_t H,element_t sign_v,element_t sign_V,pairing_t pairing){
            element_t temp;
            element_init_Zr(sign_v, pairing);
            element_init_G1(sign_V, pairing);
            element_init_Zr(temp, pairing);

            element_random(sign_v);

            element_mul(temp,alpha,alpha);  
            element_mul(temp,sign_v,temp);
            element_pow_zn(sign_V,g_1,temp);
    }

void sign(element_t A,element_t g_1,element_t g_2,element_t alpha,element_t R,element_t S,element_t T,element_t W,element_t sign_v,element_t Y,pairing_t pairing){
    element_t r;
    element_t stemp0,stemp1,stemp2,stemp3,stemp4,stemp5,stemp6,stemp7;

    element_init_Zr(r, pairing);
    element_init_G2(Y, pairing);

    element_init_Zr(stemp0, pairing);
    element_init_Zr(stemp1, pairing);
    element_init_Zr(stemp2, pairing);
    element_init_Zr(stemp3, pairing);
    element_init_Zr(stemp4, pairing);
    element_init_G2(stemp5, pairing);
    element_init_G2(stemp6, pairing);
    element_init_G2(stemp7, pairing);

    element_set1(stemp0);
    element_random(r);
    element_random(Y);

    element_div(stemp1,sign_v,r);
    element_div(stemp2,stemp0,r);

    element_mul(stemp3,alpha,alpha);
    element_mul(stemp4,r,stemp3);
    element_pow_zn(R,g_1,stemp4);

    element_pow_zn(stemp5,A,stemp1);
    element_pow_zn(stemp6,Y,stemp2);
    element_mul(S,stemp5,stemp6);

    element_pow_zn(stemp7,S,stemp1);
    element_pow_zn(W,g_2,stemp2);
    element_mul(T,stemp7,W);
    }

void sign_rand(element_t alpha,element_t R,element_t S,element_t T,element_t W,element_t R_1,element_t S_1,element_t T_1,pairing_t pairing){
    element_t rtemp0,rtemp1,rtemp2,rtemp3,rtemp4,rtemp5,rtemp6;

    element_init_Zr(rtemp0, pairing);
    element_init_Zr(rtemp1, pairing);
    element_init_Zr(rtemp2, pairing);
    element_init_Zr(rtemp3, pairing);
    element_init_Zr(rtemp4, pairing);
    element_init_G2(rtemp5, pairing);
    element_init_G2(rtemp6, pairing);
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

int vfy(element_t A,element_t alpha,element_t g_1,element_t g_2,element_t Y,element_t sign_V,element_t R,element_t S,element_t T,pairing_t pairing){
    element_t e_vkm,e_alphay,e_vks,e_alpha1;
    element_t left_1,left_2,right_1,right_2;
    element_t vtemp0,vtemp1,vtemp2,vtemp3;

    element_init_GT(e_vkm, pairing);
    element_init_GT(e_alphay, pairing);
    element_init_GT(e_vks, pairing);
    element_init_GT(e_alpha1, pairing);
    element_init_GT(left_1, pairing);
    element_init_GT(left_2, pairing);
    element_init_GT(right_1, pairing);
    element_init_GT(right_2, pairing);

    element_init_Zr(vtemp0, pairing);
    element_init_Zr(vtemp1, pairing);
    element_init_G1(vtemp2, pairing);
    element_init_G2(vtemp3, pairing);
    element_set1(vtemp0);

    pairing_apply(left_1,R,S,pairing);
    pairing_apply(left_2,R,T,pairing);
    pairing_apply(e_vkm,sign_V,A,pairing);
    
    element_mul(vtemp1,alpha,alpha);
    element_pow_zn(vtemp2,g_1,vtemp1);
    pairing_apply(e_alphay,vtemp2,Y,pairing);

    element_mul(right_1,e_vkm,e_alphay);

    pairing_apply(e_vks,sign_V,S,pairing);
    element_pow_zn(vtemp3,g_2,vtemp0);
    pairing_apply(e_alpha1,vtemp2,vtemp3,pairing);
    element_mul(right_2,e_vks,e_alpha1);

    // cout<<"element_cmp(left_1,right_1) = "<<element_cmp(left_1,right_1)<<endl;
    // cout<<"element_cmp(left_2,right_2) = "<<element_cmp(left_2,right_2)<<endl;

    if((element_cmp(left_1,right_1)==0)&&(element_cmp(left_2,right_2)==0))
    {
        return 1;
    }
    else{return 0;}
    }








int main(){

for (int i=0;i<5;i++){
string universe[1000]={"a1","a2","a3","a4","a5","a6","a7","a8","a9","a10","a11","a12","a13","a14","a15","a16","a17","a18","a19","a20","a21","a22","a23","a24","a25","a26","a27","a28","a29","a30","a31","a32","a33","a34","a35","a36","a37","a38","a39","a40","a41","a42","a43","a44","a45","a46","a47","a48","a49","a50","a51","a52","a53","a54","a55","a56","a57","a58","a59","a60","a61","a62","a63","a64","a65","a66","a67","a68","a69","a70","a71","a72","a73","a74","a75","a76","a77","a78","a79","a80","a81","a82","a83","a84","a85","a86","a87","a88","a89","a90","a91","a92","a93","a94","a95","a96","a97","a98","a99","a100","a101","a102","a103","a104","a105","a106","a107","a108","a109","a110","a111","a112","a113","a114","a115","a116","a117","a118","a119","a120","a121","a122","a123","a124","a125","a126","a127","a128","a129","a130","a131","a132","a133","a134","a135","a136","a137","a138","a139","a140","a141","a142","a143","a144","a145","a146","a147","a148","a149","a150","a151","a152","a153","a154","a155","a156","a157","a158","a159","a160","a161","a162","a163","a164","a165","a166","a167","a168","a169","a170","a171","a172","a173","a174","a175","a176","a177","a178","a179","a180","a181","a182","a183","a184","a185","a186","a187","a188","a189","a190","a191","a192","a193","a194","a195","a196","a197","a198","a199","a200","a201","a202","a203","a204","a205","a206","a207","a208","a209","a210","a211","a212","a213","a214","a215","a216","a217","a218","a219","a220","a221","a222","a223","a224","a225","a226","a227","a228","a229","a230","a231","a232","a233","a234","a235","a236","a237","a238","a239","a240","a241","a242","a243","a244","a245","a246","a247","a248","a249","a250","a251","a252","a253","a254","a255","a256","a257","a258","a259","a260","a261","a262","a263","a264","a265","a266","a267","a268","a269","a270","a271","a272","a273","a274","a275","a276","a277","a278","a279","a280","a281","a282","a283","a284","a285","a286","a287","a288","a289","a290","a291","a292","a293","a294","a295","a296","a297","a298","a299","a300","a301","a302","a303","a304","a305","a306","a307","a308","a309","a310","a311","a312","a313","a314","a315","a316","a317","a318","a319","a320","a321","a322","a323","a324","a325","a326","a327","a328","a329","a330","a331","a332","a333","a334","a335","a336","a337","a338","a339","a340","a341","a342","a343","a344","a345","a346","a347","a348","a349","a350","a351","a352","a353","a354","a355","a356","a357","a358","a359","a360","a361","a362","a363","a364","a365","a366","a367","a368","a369","a370","a371","a372","a373","a374","a375","a376","a377","a378","a379","a380","a381","a382","a383","a384","a385","a386","a387","a388","a389","a390","a391","a392","a393","a394","a395","a396","a397","a398","a399","a400","a401","a402","a403","a404","a405","a406","a407","a408","a409","a410","a411","a412","a413","a414","a415","a416","a417","a418","a419","a420","a421","a422","a423","a424","a425","a426","a427","a428","a429","a430","a431","a432","a433","a434","a435","a436","a437","a438","a439","a440","a441","a442","a443","a444","a445","a446","a447","a448","a449","a450","a451","a452","a453","a454","a455","a456","a457","a458","a459","a460","a461","a462","a463","a464","a465","a466","a467","a468","a469","a470","a471","a472","a473","a474","a475","a476","a477","a478","a479","a480","a481","a482","a483","a484","a485","a486","a487","a488","a489","a490","a491","a492","a493","a494","a495","a496","a497","a498","a499","a500","a501","a502","a503","a504","a505","a506","a507","a508","a509","a510","a511","a512","a513","a514","a515","a516","a517","a518","a519","a520","a521","a522","a523","a524","a525","a526","a527","a528","a529","a530","a531","a532","a533","a534","a535","a536","a537","a538","a539","a540","a541","a542","a543","a544","a545","a546","a547","a548","a549","a550","a551","a552","a553","a554","a555","a556","a557","a558","a559","a560","a561","a562","a563","a564","a565","a566","a567","a568","a569","a570","a571","a572","a573","a574","a575","a576","a577","a578","a579","a580","a581","a582","a583","a584","a585","a586","a587","a588","a589","a590","a591","a592","a593","a594","a595","a596","a597","a598","a599","a600","a601","a602","a603","a604","a605","a606","a607","a608","a609","a610","a611","a612","a613","a614","a615","a616","a617","a618","a619","a620","a621","a622","a623","a624","a625","a626","a627","a628","a629","a630","a631","a632","a633","a634","a635","a636","a637","a638","a639","a640","a641","a642","a643","a644","a645","a646","a647","a648","a649","a650","a651","a652","a653","a654","a655","a656","a657","a658","a659","a660","a661","a662","a663","a664","a665","a666","a667","a668","a669","a670","a671","a672","a673","a674","a675","a676","a677","a678","a679","a680","a681","a682","a683","a684","a685","a686","a687","a688","a689","a690","a691","a692","a693","a694","a695","a696","a697","a698","a699","a700","a701","a702","a703","a704","a705","a706","a707","a708","a709","a710","a711","a712","a713","a714","a715","a716","a717","a718","a719","a720","a721","a722","a723","a724","a725","a726","a727","a728","a729","a730","a731","a732","a733","a734","a735","a736","a737","a738","a739","a740","a741","a742","a743","a744","a745","a746","a747","a748","a749","a750","a751","a752","a753","a754","a755","a756","a757","a758","a759","a760","a761","a762","a763","a764","a765","a766","a767","a768","a769","a770","a771","a772","a773","a774","a775","a776","a777","a778","a779","a780","a781","a782","a783","a784","a785","a786","a787","a788","a789","a790","a791","a792","a793","a794","a795","a796","a797","a798","a799","a800","a801","a802","a803","a804","a805","a806","a807","a808","a809","a810","a811","a812","a813","a814","a815","a816","a817","a818","a819","a820","a821","a822","a823","a824","a825","a826","a827","a828","a829","a830","a831","a832","a833","a834","a835","a836","a837","a838","a839","a840","a841","a842","a843","a844","a845","a846","a847","a848","a849","a850","a851","a852","a853","a854","a855","a856","a857","a858","a859","a860","a861","a862","a863","a864","a865","a866","a867","a868","a869","a870","a871","a872","a873","a874","a875","a876","a877","a878","a879","a880","a881","a882","a883","a884","a885","a886","a887","a888","a889","a890","a891","a892","a893","a894","a895","a896","a897","a898","a899","a900","a901","a902","a903","a904","a905","a906","a907","a908","a909","a910","a911","a912","a913","a914","a915","a916","a917","a918","a919","a920","a921","a922","a923","a924","a925","a926","a927","a928","a929","a930","a931","a932","a933","a934","a935","a936","a937","a938","a939","a940","a941","a942","a943","a944","a945","a946","a947","a948","a949","a950","a951","a952","a953","a954","a955","a956","a957","a958","a959","a960","a961","a962","a963","a964","a965","a966","a967","a968","a969","a970","a971","a972","a973","a974","a975","a976","a977","a978","a979","a980","a981","a982","a983","a984","a985","a986","a987","a988","a989","a990","a991","a992","a993","a994","a995","a996","a997","a998","a999","a1000"};

fstream f;
f.open("CDABACE.csv",ios::out|ios::app);
f<<"Number of Attributes,Setup,Encrytion key generation,Decrytion key generation,Encryption,Sanitization,Decrytion"<<endl;

for(int iter_i =0;iter_i<40;iter_i++)
{
    int count=(iter_i+1)*5;
    f<<count<<",";
    cout<<"test--------------"<<iter_i<<"--------------"<<endl;
    clock_t start,end;

//————————————————————————————————初始化——————————————————————————————————————

    hash<string> h;
    pairing_t pairing;

    char file[]="f.param";
    pbc_pairing_init(pairing, file);

    //程序开始计时
    start=clock();
    element_t alpha,g2;
    element_t g_1,g_2,g_t;
    
    //初始化属性全集
    // string attribute[4]={"A","B","C","D"};
    string attribute[count];
    for(int i=0;i<count;i++)
    {
        attribute[i]=universe[i];
        // cout<<attribute[i]<<endl;
    }
    element_t attribute_value[count+1];
    element_t gt_alpha;
    element_t k[count];

    setup(attribute,alpha,g2,g_1,g_2,g_t,attribute_value,gt_alpha,k,count,pairing);


    //签名算法初始化
    element_t sign_v,sign_V;
    sign_setup(alpha,g_1,g_2,sign_v,sign_V,pairing);

    //程序结束用时
	end=clock();		
	double endtime1=(double)(end-start)/CLOCKS_PER_SEC;
	cout<<"setup Total time:"<<endtime1*1000<<"ms"<<endl;	//ms为单位
    f<<endtime1*1000<<",";

//————————————————————————————————计算加密秘钥ek——————————————————————————————————————
    //程序开始计时
    start=clock();
    element_t ek;
    element_init_G2(ek,pairing);
        //初始化pi
    int p[count];
    for(int i=0;i<count;i++)
    {
        p[i]=1;
    }p[0]=0;p[1]=0;
    int temp_len=0;

    enc_keygen(ek,temp_len, pairing,alpha, g_2,k,p,count);
    

    element_t R_ek,S_ek,T_ek,W_ek,Y;
    element_init_G1(R_ek, pairing);
    element_init_G2(S_ek, pairing);
    element_init_G2(T_ek, pairing);
    element_init_G2(W_ek, pairing);

    sign(ek,g_1,g_2,alpha,R_ek,S_ek,T_ek,W_ek,sign_v,Y,pairing);

        //程序结束用时
	end=clock();		
	double endtime3=(double)(end-start)/CLOCKS_PER_SEC;
	cout<<"encryption key generation Total time:"<<endtime3*1000<<"ms"<<endl;	//ms为单位
    f<<endtime3*1000<<",";

//————————————————————————————————计算解密秘钥dk——————————————————————————————————————
    //程序开始计时
    start=clock();
    //初始化bi
    int b[count];
    for(int i=0;i<count;i++)
    {
        b[i]=1;
    }
    b[0]=0;
    element_t dk;
    element_init_G1(dk, pairing);

    dec_keygen(dk,pairing,alpha,g_1,k,b,count);

    //程序结束用时
	end=clock();		
	double endtime2=(double)(end-start)/CLOCKS_PER_SEC;
	cout<<"decryption key generation Total time:"<<endtime2*1000<<"ms"<<endl;	//ms为单位
    f<<endtime2*1000<<",";


//————————————————————————————————计算密文——————————————————————————————————————
    //程序开始计时
    start=clock();
    element_t R_ek_r,S_ek_r,T_ek_r;
    element_init_G1(R_ek_r, pairing);
    element_init_G2(S_ek_r, pairing);
    element_init_G2(T_ek_r, pairing);

    sign_rand(alpha,R_ek,S_ek,T_ek,W_ek,R_ek_r,S_ek_r,T_ek_r,pairing);
//生成零知识证明的元素
    element_t r;
    element_init_Zr(r, pairing);
    element_random(r);

    element_t g2_;
    element_init_G1(g2_,pairing);
    element_invert(g2_,g2);

//
    element_t M;
    element_t C;
    element_t C_1;
    element_t C_2;
    element_init_GT(C, pairing);
    element_init_G2(C_1, pairing);
    element_init_G1(C_2, pairing);
    element_init_GT(M, pairing);
    element_random(M);
    // cout<<"massage"<<endl;
    // element_printf("%B\n",M);

    encryption(r,C, C_1,C_2,pairing, M,alpha,g_t, ek, g2);

//NIZK prove
    element_t t1,t2,nizk_s;
    element_init_G2(t1,pairing);
    element_init_G1(t2,pairing);
    element_init_Zr(nizk_s,pairing);

    prove(nizk_s, t1, t2, ek, g2_, C_1,C_2, r,  pairing );

    //程序结束用时
	end=clock();		
	double endtime4=(double)(end-start)/CLOCKS_PER_SEC;
	cout<<"encryption Total time:"<<endtime4*1000<<"ms"<<endl;	//ms为单位
    f<<endtime4*1000<<",";

//————————————————————————————————净化——————————————————————————————————————
    start=clock();
    verify(nizk_s, t1, t2, ek, g2_, C_1,C_2, pairing);
    vfy(ek,alpha,g_1,g_2,Y,sign_V,R_ek_r,S_ek_r,T_ek_r,pairing);

    // cout<<"nizk verification result: "<<verify(nizk_s, t1, t2, ek, g2_, C_1,C_2, pairing)<<endl;
    // cout<<"ek verification result: "<<vfy(ek,alpha,g_1,g_2,Y,sign_V,R_ek_r,S_ek_r,T_ek_r,pairing)<<endl;

    //程序开始计时

    element_t Cs,C_1s,C_2s,s;
    element_init_GT(Cs,pairing);
    element_init_G2(C_1s,pairing);
    element_init_G1(C_2s,pairing);
    element_init_Zr(s,pairing);
    element_random(s);

    sanitization( Cs, C_1s, C_2s, s, gt_alpha, ek, g2, C, C_1, C_2, pairing);
	end=clock();		
	double endtime5=(double)(end-start)/CLOCKS_PER_SEC;
	cout<<"sanitization Total time:"<<endtime5*1000<<"ms"<<endl;	//ms为单位
    f<<endtime5*1000<<",";
//---------------------计时-----------------



//————————————————————————————————解密——————————————————————————————————————
    //程序开始计时
    start=clock();
    element_t dec;
    decryption(dec,pairing, attribute_value, k ,dk,b, p,temp_len, Cs, C_1s, C_2s,count);
    // element_printf("massage %B\n", M);
    // element_printf("decryption %B\n",dec);
    //程序结束用时
	end=clock();		
	double endtime=(double)(end-start)/CLOCKS_PER_SEC;
	cout<<"decryption Total time:"<<endtime*1000<<"ms"<<endl;	//ms为单位
    f<<endtime*1000<<endl;

}

        f.close();
    }

}
