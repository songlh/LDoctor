
#include <errno.h>
#include <fcntl.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <time.h>
#include <unistd.h>

#define BUFFERSIZE 1 << 30

/*
typedef struct stLoadRecord {
	unsigned uInstructionID;
	long LoadAddress;
	long LoadValue;
} LoadRecord;

typedef struct stStoreRecord {
	unsigned uInstructionID;
	long StoreAddress;
	long StoreValue;
} StoreRecord;

typedef struct stInstRecord {
	unsigned uInstructionID;
	long Value;
} InstRecord;

typedef struct stParaRecord {
	unsigned uValueID;
	long Value;
} ParaRecord;

typedef struct stDelimiterRecord {
	long numExecution;
} DelimiterRecord;

typedef struct stLogRecord {
	enum LogRecordType
	{
		Load,
		Store,
		Inst,
		Para,
		Delimiter
	};

	enum LogRecordType RecordType;

	union {
		LoadRecord LR;
		StoreRecord SR;
		InstRecord IR;
		ParaRecord PR;
		DelimiterRecord DR;
	} Value;

} LogRecord;

*/

//using namespace std;

//----- Function prototypes -------------------------------------------------
int geo(int iRate);            // Returns a geometric random variable
static double rand_val(int seed);    // Jain's RNG

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

	// Pull a uniform random number (0 < z < 1)
	do
	{
		z = rand_val(0);
	}
	while ((z == 0) || (z == 1));

	// Compute geometric random variable using inversion method
	geo_value = (int) (log(z) / log(1.0 - p)) + 1;

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

/*
int iRecordSize;
char * pcBuffer;
int iBufferIndex;
*/
int fd;


//void FinalizeMemHooks()
void FinalizeMemHooks(int iBufferIndex) 
{
	/*
	if(munmap(pcBuffer, iBufferIndex) == -1)
	{
		fprintf(stderr,  "munmap: %s\n", strerror(errno) );
		exit(-1);
	}
	*/
	if(ftruncate(fd, iBufferIndex) == -1)
	{
		fprintf(stderr,  "ftruncate: %s\n", strerror(errno) );
		exit(-1);
	}
	close(fd);
}

//static void InitMemHooks() 
char * InitMemHooks()
{
	time_t T = time(NULL);
	struct tm *LT = localtime(&T);
	char LogFileNameCStr[1024];
	sprintf(LogFileNameCStr, "CPI-%04d%02d%02d-%02d%02d%02d", LT->tm_year + 1900, LT->tm_mon + 1, LT->tm_mday, LT->tm_hour, LT->tm_min, LT->tm_sec);
	//cout << LogFileNameCStr << endl;
	printf("%s\n", LogFileNameCStr);
	//fd = open( LogFileNameCStr, O_RDWR | O_CREAT, 0777 );
	fd = shm_open( LogFileNameCStr, O_RDWR | O_CREAT, 0777 );
	if(fd == -1)
	{	
		fprintf( stderr, "Open failed:%s\n", strerror( errno ) );
		exit(-1);
	}

	if( ftruncate( fd, (BUFFERSIZE) ) == -1 ) 
	{
		fprintf( stderr, "ftruncate: %s\n", strerror( errno ));
		exit(-1);
	}

	char * pcBuffer = (char *)mmap(0, BUFFERSIZE, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
	//iBufferIndex = 0;
	//iRecordSize = sizeof(LogRecord);
	//atexit(FinalizeMemHooks);
	return pcBuffer;
}


/*
void HookStore(long address, long value, unsigned InsID) {
	LogRecord Record;
	//Record.RecordType = LogRecord::Store;
	Record.RecordType = Store;
	Record.Value.SR.StoreAddress = address;
	Record.Value.SR.StoreValue = value;
	Record.Value.SR.uInstructionID = InsID;
	memcpy(pcBuffer + iBufferIndex, &Record, iRecordSize);
	iBufferIndex += iRecordSize;
}

void HookLoad(long address, long value, unsigned InsID) {
	LogRecord Record;
	Record.RecordType = Load;
	Record.Value.LR.LoadAddress = address;
	Record.Value.LR.LoadValue = value;
	Record.Value.LR.uInstructionID = InsID;
	memcpy(pcBuffer + iBufferIndex, &Record, iRecordSize);
	iBufferIndex += iRecordSize;
}


void HookPara(long value, unsigned ValID) {
	LogRecord Record;
	Record.RecordType = Para;
	Record.Value.PR.uValueID = ValID;
	Record.Value.PR.Value = value;
	memcpy(pcBuffer + iBufferIndex, &Record, iRecordSize);
	iBufferIndex += iRecordSize;
}

void HookInst(long value, unsigned InstID) {
	LogRecord Record;
	Record.RecordType = Inst;
	Record.Value.IR.uInstructionID = InstID;
	Record.Value.IR.Value = value;
	memcpy(pcBuffer + iBufferIndex, &Record, iRecordSize);
	iBufferIndex += iRecordSize;
}


void HookDelimiter(long numExecution)
{
	LogRecord Record;
	Record.RecordType = Delimiter;
	Record.Value.DR.numExecution = numExecution;
	memcpy(pcBuffer + iBufferIndex, &Record, iRecordSize);
	iBufferIndex += iRecordSize;
}
*/

//void InitHooks()
char * InitHooks()
{
	rand_val(997);
	return InitMemHooks();
}

