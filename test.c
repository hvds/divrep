#include <stdio.h>

FILE *rfp = NULL;

void f1(void){
     int d;
     int e;
     int f;
     freopen(NULL, "a+", rfp);
     printf ("Enter (2) first digit \n");
     scanf("%d", &d);
     printf ("Enter (2) second digit \n");
     scanf("%d", &e);
     f=d+e;
     fprintf(rfp,"%d %d %d\n",d,e,f);
     fflush(rfp);
}

int main(int argc, char **argv, char **envp){
     int a;
     int b;
     int c;
     rfp = fopen("out.txt", "a+");
     printf ("Enter first digit \n");
     scanf("%d", &a);
     printf ("Enter second digit \n");
     scanf("%d", &b);
     c=a+b;
     fprintf(rfp,"%d %d %d\n",a,b,c);
     fflush(rfp);
     {
       int d;
       int e;
       int f;
       freopen(NULL, "a+", rfp);
       printf ("Enter (2:%d) first digit \n",i);
       scanf("%d", &d);
       printf ("Enter (2:%d) second digit \n",i);
       scanf("%d", &e);
       f=d+e;
       fprintf(rfp,"%d %d %d\n",d,e,f);
       fflush(rfp);
     }
/*
 * We test each version of the code twice, once with no arguments
 * (and so without the extra fflush() call) expecting to reproduce
 * the issue, and once with an argument (and so *with* the extra
 * fflush() call) expecting *not* to reproduce the issue.
 */
     if (argc > 1)
        fflush(rfp);

     printf ("Enter (3) first digit \n");
     scanf("%d", &a);
     printf ("Enter (3) second digit \n");
     scanf("%d", &b);
     c=a+b;
     fprintf(rfp,"%d %d %d\n",a,b,c);
     fflush(rfp);
     fprintf(rfp,"=================\n");
     fclose(rfp);
}
