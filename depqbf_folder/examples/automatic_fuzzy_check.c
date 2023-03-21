#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "../qdpll.h"
#include <time.h>
#include <sys/time.h>
#include <unistd.h>
#include <dirent.h>

int main (int argc, char** argv)
{
  int num_clauses=100000;
  int num_vars=5000;
  char command[300];
  int part1=1;
  int part2=1;
  int part3=1;

  /*
  time_t start_check, end_check;
  double cpu_time_used_check;
  cpu_time_used_check = 0;

  clock_t clock_start_check, clock_end_check;
  double clock_cpu_time_used_check;
  clock_cpu_time_used_check = 0;

  time_t start_mus, end_mus;
  double cpu_time_used_mus;
  cpu_time_used_mus = 0;
  */

  struct timeval start, end;
  struct timeval start_mus, end_mus;



  int nv=80; //v
  int nc=40; //c
  int nb=15; //s
  int min=5; //min
  int max=15; //max




  if(part1==1){
    //sprintf(command, "python3 /home/andreas/Documents/Programming-Projects/C-Projects/qbfuzz-1.1.1/qbfuzz.py -v%d -c%d -o/home/andreas/Documents/GitLabProjects/depqbf/examples/Check-Files/fuzzy_output", num_vars, num_clauses);
    sprintf(command, "python3 /home/andreas/Documents/Programming-Projects/C-Projects/qbfuzz-1.1.1/qbfuzz.py -v%d -c%d -s%d --min=%d --max=%d -o/home/andreas/Documents/GitLabProjects/depqbf/examples/Check-Files/fuzzy_output", nv, nc, nb, min, max);
    system(command);
  }
  if(part2==1){
    //system("/home/andreas/Documents/GitLabProjects/depqbf/examples/basic-api-example_implementationtest /home/andreas/Documents/GitLabProjects/depqbf/examples/Check-Files/fuzzy_output");
  }
  if(part3==1){
    //system("/home/andreas/Documents/GitLabProjects/depqbf/depqbf --incremental-use --trace=qrp --dep-man=simple --traditional-qcdcl /home/andreas/Documents/GitLabProjects/depqbf/examples/Check-Files/PCNF20-DUNSAT/arbiter-05-comp-error01-qbf-hardness-depth-8.qdimacs > /home/andreas/Documents/GitLabProjects/depqbf/examples/Check-Files/output");
    //system("/home/andreas/Documents/GitLabProjects/depqbf/depqbf --incremental-use --trace=qrp --dep-man=simple --traditional-qcdcl /home/andreas/Documents/GitLabProjects/depqbf/examples/Check-Files/fuzzy_output > /home/andreas/Documents/GitLabProjects/depqbf/examples/Check-Files/output");
    //printf("initial solver call finished\n");
    //start_check=time(NULL);
    //clock_start_check=clock();




    gettimeofday(&start, NULL);
    //system("/home/andreas/Documents/Programming-Projects/C-Projects/Haifa-HLMUC/hhlmuc /home/andreas/Documents/GitLabProjects/depqbf/examples/Check-Files/sample");
    gettimeofday(&end, NULL);
    //clock_end_check=clock();
    //end_check=time(NULL);
    //start_mus=time(NULL);
    gettimeofday(&start_mus, NULL);
    //system(" /home/andreas/Documents/Programming-Projects/C-Projects/Mus-Extraction_cert/qrpcert /home/andreas/Documents/GitLabProjects/depqbf/examples/Check-Files/output");
    //system(" /home/andreas/Documents/Programming-Projects/C-Projects/Mus-Extraction_hash/mus_extraction /home/andreas/Documents/GitLabProjects/depqbf/examples/Check-Files/output");

    DIR *d;
    struct dirent *dir;
    d = opendir("./Check-Files/PCNF20-DUNSAT");
    if (d) {
      while ((dir = readdir(d)) != NULL) {
        //printf("%s\n", dir->d_name);
        char buffer[1024];
        snprintf(buffer, sizeof(buffer), "/home/andreas/Documents/GitLabProjects/depqbf/depqbf --incremental-use --trace=qrp --dep-man=simple --traditional-qcdcl /home/andreas/Documents/GitLabProjects/depqbf/examples/Check-Files/PCNF20-DUNSAT/%s > /home/andreas/Documents/GitLabProjects/depqbf/examples/Check-Files/output", dir->d_name);
        //printf("%s",buffer);
        system(buffer);
        system(" /home/andreas/Documents/Programming-Projects/C-Projects/Mus-Extraction_hash/mus_extraction /home/andreas/Documents/GitLabProjects/depqbf/examples/Check-Files/output");
      }
      closedir(d);
    }

    //system("/home/andreas/Documents/GitLabProjects/depqbf/depqbf --incremental-use --trace=qrp --dep-man=simple --traditional-qcdcl /home/andreas/Documents/GitLabProjects/depqbf/examples/Check-Files/PCNF20-DUNSAT/arbiter-05-comp-error01-qbf-hardness-depth-8.qdimacs > /home/andreas/Documents/GitLabProjects/depqbf/examples/Check-Files/output");
    //system(" /home/andreas/Documents/Programming-Projects/C-Projects/Mus-Extraction_hash/mus_extraction /home/andreas/Documents/GitLabProjects/depqbf/examples/Check-Files/output");

    gettimeofday(&end_mus, NULL);
  //end_mus=time(NULL);
  //cpu_time_used_check = ((double) (end_check - start_check));
  //printf("start_check=%f\n",(double)start_check);
  //printf("end_check=%f\n",(double)end_check);
  }else{
    gettimeofday(&start, NULL);

    gettimeofday(&end, NULL);

    gettimeofday(&start_mus, NULL);

    gettimeofday(&end_mus, NULL);

  }
  //system("python3 /home/andreas/Documents/Programming-Projects/C-Projects/qbfuzz-1.1.1/qbfuzz.py -v10 -c10 -o/home/andreas/Documents/GitLabProjects/depqbf/examples/Check-Files/fuzzy_output");


  long seconds = (end.tv_sec - start.tv_sec);
  long micros = ((seconds * 1000000) + end.tv_usec) - (start.tv_usec);

  long seconds_mus = (end_mus.tv_sec - start_mus.tv_sec);
  long micros_mus = ((seconds_mus * 1000000) + end_mus.tv_usec) - (start_mus.tv_usec);

  //printf("check programm took %f seconds to execute \n", cpu_time_used_check);
  //clock_cpu_time_used_check += (double)(clock_end_check - clock_start_check) / CLOCKS_PER_SEC;
  //printf("check programm took %f seconds to execute (clock) \n", clock_cpu_time_used_check);
  printf("The elapsed time for the check is %ld seconds and %ld micros\n", seconds, micros);


  //cpu_time_used_mus = ((double) (end_mus - start_mus));
  printf("The elapsed time for the mus is %ld seconds and %ld micros\n", seconds_mus, micros_mus);


}
