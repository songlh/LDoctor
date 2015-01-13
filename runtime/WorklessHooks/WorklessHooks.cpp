#include <stdio.h>
#include <map>
#include <string>
#include <sstream>
#include <iostream>

using namespace std;


extern "C" void PrintLoopInfo(long numIterations, long numInstances ) {
  
   FILE * fp = fopen("./main1.dump", "w");
   fprintf( fp, "Iterations: %ld\n", numIterations);
   fprintf( fp, "Instances: %ld\n", numInstances);

   fclose(fp);

}

extern "C" void PrintWorkingRatio(long numIterations, long numWorkingIterations ) {
   FILE * fp = fopen("./main2.dump", "w");
   fprintf(fp, "Iterations: %ld\n", numIterations);
   fprintf(fp, "Working Iterations: %ld\n", numWorkingIterations);
   fprintf(fp, "Ratio: %f\n", (double)numWorkingIterations/numIterations);
   fclose(fp);
   
}


