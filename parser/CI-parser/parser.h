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

typedef struct stMemRecord {
	unsigned uInstructionID;
	long uLength;
} MemRecord;

typedef struct stLogRecord {
	enum LogRecordType
	{
		Load,
		Store,
		Inst,
		Para,
		Delimiter,
		Mem
	};

	LogRecordType RecordType;
	union {
		LoadRecord LR;
		StoreRecord SR;
		InstRecord IR;
		ParaRecord PR;
		DelimiterRecord DR;
		MemRecord MR;
	};

} LogRecord;