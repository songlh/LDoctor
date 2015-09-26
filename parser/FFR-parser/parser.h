typedef struct stLoadRecord {
	long uInstance;
	unsigned uInstructionID;
	long LoadAddress;
	long LoadValue;
} LoadRecord;

typedef struct stStoreRecord {
	long uInstance;
	unsigned uInstructionID;
	long StoreAddress;
	long StoreValue;
} StoreRecord;

typedef struct stInstRecord {
	long uInstance;
	unsigned uInstructionID;
	long Value;
} InstRecord;

typedef struct stParaRecord {
	long uInstance;
	unsigned uValueID;
	long Value;
} ParaRecord;

typedef struct stMemRecord {
	long uInstance;
	unsigned uInstructionID;
	long uLength;
} MemRecord;

typedef struct stDelimiterRecord {
	long numExecution;
} DelimiterRecord;

typedef struct stLogRecord {
	enum LogRecordType
	{
		Load,
		Para,
		Store,
		Inst,
		Mem,
		Delimiter
	};

	LogRecordType RecordType;
	union {
		LoadRecord LR;
		ParaRecord PR;
		StoreRecord SR;
		InstRecord IR;
		MemRecord MR;
		DelimiterRecord DR;
	};

} LogRecord;