#include <stdio.h>
#include <map>
#include <string>
#include <sstream>
#include <iostream>

using namespace std;


extern "C" void PrintLoopInfo(long numIterations, long numInstances ) {
  
   //FILE * fp = fopen("./main1.dump", "w");
   //fprintf( fp, "Iterations: %ld\n", numIterations);
   //fprintf( fp, "Instances: %ld\n", numInstances);

   //fclose(fp);
	printf("Iterations: %ld\n", numIterations);
	printf( "Instances: %ld\n", numInstances);
}

extern "C" void PrintWorkingRatio(long numIterations, long numWorkingIterations ) {
   //FILE * fp = fopen("./main2.dump", "w");
   //fprintf(fp, "Iterations: %ld\n", numIterations);
   //fprintf(fp, "Working Iterations: %ld\n", numWorkingIterations);
   //fprintf(fp, "Ratio: %f\n", (double)numWorkingIterations/numIterations);
   //fclose(fp);
   printf("Iterations: %ld\n", numIterations);
   printf("Working Iterations: %ld\n", numWorkingIterations);
   printf("Ratio: %f\n", (double)numWorkingIterations/numIterations);
}


