
#include <errno.h>
#include <fcntl.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <time.h>
#include <unistd.h>

#define BUFFERSIZE (unsigned long)1 << 38


//----- Function prototypes -------------------------------------------------
int geo(int iRate);            // Returns a geometric random variable
static double rand_val(int seed);    // Jain's RNG
static int old_value = -1;

//===========================================================================
//=  Function to generate geometrically distributed random variables        =
//=    - Input:  Probability of success p                                   =
//=    - Output: Returns with geometrically distributed random variable     =
//===========================================================================
int geo(int iRate)
{
	double p = 1/(double)iRate;
	double z;                     // Uniform random number (0 < z < 1)
	double geo_value;             // Computed geometric value to be returned
	
	do
	{
		// Pull a uniform random number (0 < z < 1)
		do
		{
			z = rand_val(0);
		}
		while ((z == 0) || (z == 1));

		// Compute geometric random variable using inversion method
		geo_value = (int) (log(z) / log(1.0 - p)) + 1;
	} 
	while((int)geo_value == old_value + 1);


	old_value = (int)geo_value; 
	return(geo_value);
}

//=========================================================================
//= Multiplicative LCG for generating uniform(0.0, 1.0) random numbers    =
//=   - x_n = 7^5*x_(n-1)mod(2^31 - 1)                                    =
//=   - With x seeded to 1 the 10000th x value should be 1043618065       =
//=   - From R. Jain, "The Art of Computer Systems Performance Analysis," =
//=     John Wiley & Sons, 1991. (Page 443, Figure 26.2)                  =
//=========================================================================
static double rand_val(int seed)
{
	const long  a =      16807;  // Multiplier
	const long  m = 2147483647;  // Modulus
	const long  q =     127773;  // m div a
	const long  r =       2836;  // m mod a
	static long x;               // Random int value
	long        x_div_q;         // x divided by q
	long        x_mod_q;         // x modulo q
	long        x_new;           // New x value

	// Set the seed if argument is non-zero and then return zero
	if (seed > 0)
	{
		x = seed;
		return(0.0);
	}

	// RNG using integer arithmetic
	x_div_q = x / q;
	x_mod_q = x % q;
	x_new = (a * x_mod_q) - (r * x_div_q);
	if (x_new > 0)
		x = x_new;
	else
		x = x_new + m;

	// Return a random value between 0.0 and 1.0
	return((double) x / m);
}


int fd;

void FinalizeMemHooks(long iBufferIndex) 
{
	if(ftruncate64(fd, iBufferIndex) == -1)
	{
		fprintf(stderr,  "ftruncate: %s\n", strerror(errno) );
		exit(-1);
	}
	
	close(fd);
}

char * InitMemHooks()
{
	time_t T = time(NULL);
	struct tm *LT = localtime(&T);
	char LogFileNameCStr[1024];
	sprintf(LogFileNameCStr, "/home/songlh/PLDI2015/tmp/CPI-%04d%02d%02d-%02d%02d%02d", LT->tm_year + 1900, LT->tm_mon + 1, LT->tm_mday, LT->tm_hour, LT->tm_min, LT->tm_sec);
	
	printf("%s\n", LogFileNameCStr);

	//fd = shm_open( LogFileNameCStr, O_RDWR | O_CREAT, 0777 );
	fd = open(LogFileNameCStr, O_RDWR | O_CREAT, 0777);

	if(fd == -1)
	{	
		fprintf( stderr, "Open failed:%s\n", strerror( errno ) );
		exit(-1);
	}

	if( ftruncate64( fd, (BUFFERSIZE) ) == -1 ) 
	{
		fprintf( stderr, "ftruncate: %s\n", strerror( errno ));
		exit(-1);
	}

	char * pcBuffer = (char *)mmap(0, BUFFERSIZE, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
	printf("%ld\n", (long)pcBuffer);
	return pcBuffer;
}


char * InitHooks()
{
	rand_val(35749);
	return InitMemHooks();
}

