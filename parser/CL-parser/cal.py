
import sys
import re
import math

class Inst:
	def __init__(self, iID):
		self.ID = iID
		self.IsStart = False
		self.IsTripCounter = False
		self.Stride = 0
		self.IsSequence = False
		self.IsSkip = False
		self.Type = 0

	def DumpInst(self):
		print self.ID,
		print self.IsStart,
		print self.IsTripCounter,
		print self.Stride,
		print self.IsSequence,
		print self.IsSkip


class Para:
	def __init__(self, iID):
		self.ID = iID
		self.IsStart = False
		self.IsTripCounter = False
		self.Stride = 0
		self.IsSequence = False
		self.IsSkip = False
		self.Type = 1

	def DumpPara(self):
		print self.ID,
		print self.IsStart,
		print self.IsTripCounter,
		print self.Stride,
		print self.IsSequence,
		print self.IsSkip

class Instance:
	def __init__(self, iID):
		self.ID = iID
		self.InstValueMapping = {}
		self.ParaValueMapping = {}
		self.LoadLengthMapping = {}


class Pair:
	def __init__(self, iID1, iID2):
		self.Instance1 = Instance(iID1)
		self.Instance2 = Instance(iID2)
		self.LoadCmpMapping = {}
		self.InstCmpMapping = {}
		self.ParaCmpMapping = {}

		



def ParseInstFile(sInstFile):
	fInstFile = open(sInstFile, 'r')
	IDInstMapping = {}

	reInst = re.compile(r'Inst ([0-9]+):')
	rePara = re.compile(r'Func [^\s]+ ([0-9]+) ([0-9]+)')

	reIsIterative = re.compile(r'//---Start of Iterative Variable (Stride:)?( ([\-0-9]+))*')
	reIsTripCounter = re.compile(r'//---Possible Loop Boundary')
	reControlSkip = re.compile(r'//---Control Skip')
	reNoDepSkip   = re.compile(r'//---No Dependence Skip')

	IDInstMapping = {}
	IDParaMapping = {}

	obj = None

	while True:
		line = fInstFile.readline()
		if not line:
			break

		match = reInst.match(line)
		if match:
			strID = match.group(1)
			iID = int(strID)
			if obj != None:
				if obj.Type == 0:
					IDInstMapping[obj.ID] = obj
				elif obj.Type == 1:
					IDParaMapping[obj.ID] = obj

			obj = Inst(iID)
			continue

		match = rePara.match(line)
		if match:
			strFunc = match.group(1)
			strPara = match.group(2)

			iID = int(strFunc) * 10 + int(strPara)

			if obj != None:
				if obj.Type == 0:
					IDInstMapping[obj.ID] = obj
				elif obj.Type == 1:
					IDParaMapping[obj.ID] = obj

			obj = Para(iID)
			continue

		match = reIsIterative.match(line)
		if match:
			obj.IsStart = True
			if len(match.groups()) == 3:
				obj.Stride = int(match.group(3))

			if len(match.groups()) > 3:
				exit("more than one stride")

			continue

		match = reIsTripCounter.match(line)
		if match:
			obj.IsTripCounter = True
			continue

		match = reControlSkip.match(line)
		if match:
			obj.IsSkip = True
			continue

		match = reNoDepSkip.match(line)
		if match:
			obj.IsSkip = True
			continue


	if obj != None:
		if obj.Type == 0:
			IDInstMapping[obj.ID] = obj
		elif obj.Type == 1:
			IDParaMapping[obj.ID] = obj


	fInstFile.close()

	return (IDInstMapping, IDParaMapping)


def GetLength(Instance1, IDInstMapping, IDParaMapping):
	#maximum length of load
	length = -1

	for key in Instance1.LoadLengthMapping:
		if Instance1.LoadLengthMapping[key] > length:
			length = Instance1.LoadLengthMapping[key]

	if length != -1:
		return length

	vecTripCounter = []

	for key in IDInstMapping:
		if IDInstMapping[key].IsTripCounter:
			vecTripCounter.append(key)

	for key in IDParaMapping:
		if IDParaMapping[key].IsTripCounter:
			vecTripCounter.append(key)


	if len(vecTripCounter) == 0:
		return -1

	length = 10000000

	for key in vecTripCounter:
		if Instance1.InstValueMapping[key] < length:
			length = Instance1.InstValueMapping[key]

	return length
	#try trip counter variable




def CalRedundancy(pair, IDInstMapping, IDParaMapping):
	
	length1 = GetLength(pair.Instance1, IDInstMapping, IDParaMapping)
	length2 = GetLength(pair.Instance2, IDInstMapping, IDParaMapping)
	
	if length1 == -1:
		for key in pair.InstCmpMapping:
			if pair.InstCmpMapping[key] == 1:
				return (0, -1)

		return (1, -1)

	minLength = min(length1, length2)
	maxLength = max(length1, length2)
	gapLength = abs(length1 - length2)

	vecRedundancy = []

	for key in pair.InstCmpMapping: 
		if pair.InstCmpMapping[key] == 0:
			vecRedundancy.append(1)
		else:
			if IDInstMapping[key].IsStart:
				if IDInstMapping[key].Stride == 1 or IDInstMapping[key].Stride == -1:
					valueGap = abs(pair.Instance1.InstValueMapping[key] - pair.Instance2.InstValueMapping[key])
					if gapLength > valueGap:
						differentIteration = 0
					else:
						differentIteration = valueGap - gapLength

					redundancy = 1.0 - differentIteration/minLength
					vecRedundancy.append(redundancy)
					continue
					

				elif IDInstMapping[key].Stride > 1 or IDInstMapping[key].Stride < -1:
					valueGap = abs(pair.Instance1.InstValueMapping[key] - pair.Instance2.InstValueMapping[key])
					stride = abs(IDInstMapping[key].Stride)
					if valueGap % stride != 0:
						vecRedundancy.append(0)
						continue

					valueGap = valueGap / stride

					if gapLength > valueGap:
						differentIteration = 0
					else:
						differentIteration = valueGap - gapLength

					redundancy = 1.0 - differentIteration/minLength
					vecRedundancy.append(redundancy)
					continue

			elif IDInstMapping[key].IsTripCounter:
				vecRedundancy.append(1)
				continue

			elif IDInstMapping[key].IsSkip:
				continue

			vecRedundancy.append(0)


	for key in pair.ParaCmpMapping: 
		if pair.ParaCmpMapping[key] == 0:
			vecRedundancy.append(1)
		else:
			if IDParaMapping[key].IsStart:
				if IDParaMapping[key].Stride == 1 or IDParaMapping[key].Stride == -1:
					valueGap = abs(pair.Instance1.ParaValueMapping[key] - pair.Instance2.ParaValueMapping[key])
					if gapLength > valueGap:
						differentIteration = 0
					else:
						differentIteration = valueGap - gapLength

					redundancy = 1.0 - differentIteration/minLength
					vecRedundancy.append(redundancy)
					continue

				elif IDParaMapping[key].Stride > 1 or IDParaMapping[key].Stride < -1:
					valueGap = abs(pair.Instance1.ParaValueMapping[key] - pair.Instance2.ParaValueMapping[key])
					stride = abs(IDParaMapping[key].Stride)
					if valueGap % stride != 0:
						vecRedundancy.append(0)

					valueGap = valueGap / stride

					if gapLength > valueGap:
						differentIteration = 0
					else:
						differentIteration = valueGap - gapLength

					redundancy = 1.0 - differentIteration/minLength
					vecRedundancy.append(redundancy)
					continue

			elif IDParaMapping[key].IsTripCounter:
				vecRedundancy.append(1)
				continue

			elif IDParaMapping[key].IsSkip:
				continue

			vecRedundancy.append(0)


	for key in pair.LoadCmpMapping:

		if pair.LoadCmpMapping[key][0] == 0:
			vecRedundancy.append(1)
		elif pair.LoadCmpMapping[key][0] == 1:
			distance = min(pair.LoadCmpMapping[key][1], pair.LoadCmpMapping[key][2])
			distance = distance - abs(pair.Instance1.LoadLengthMapping[key] - pair.Instance2.LoadLengthMapping[key])
			
			minLoadLength = min(pair.Instance1.LoadLengthMapping[key], pair.Instance2.LoadLengthMapping[key])
			red = 1.0 - 1.0 * distance / minLoadLength
			vecRedundancy.append(red)

	res = sum(vecRedundancy)/len(vecRedundancy)

	return (res, minLength, maxLength, vecRedundancy)




def ParseTraceFile(sTraceFile, IDInstMapping, IDParaMapping):
	fTraceFile = open(sTraceFile, 'r')

	reTotalLoad = re.compile(r'Total Load: ([0-9]+)')
	reTotalInst = re.compile(r'Total Instruction: ([0-9]+)')
	reTotalPara = re.compile(r'Total Parameter: ([0-9]+)')
	reTotalInstance = re.compile(r'Total Exeuction: ([0-9]+)')

	reInstance = re.compile(r'Instance ([0-9]+) ([0-9]+)')
	reInst     = re.compile(r'Inst: ([SD]) ([0-9]+) ([0-9]+) ([0-9]+)')
	rePara     = re.compile(r'Para: ([SD]) ([0-9]+) ([0-9]+) ([0-9]+)')
	reLoadSub  = re.compile(r'Load: SubSequence ([0-9]+) ([0-9]+) ([0-9]+)')
	reLoadEdit = re.compile(r'Load: EditDistance ([0-9]+) ([0-9]+) ([0-9]+) ([0-9]+) ([0-9]+) ([0-9]+) ([0-9]+)')

	reFinish   = re.compile(r'[\*]+\n')

	vecRedundancy = []

	while True:
		line = fTraceFile.readline()
		if not line:
			break

		match = reTotalLoad.match(line)
		if match:
			iTotalLoad = int(match.group(1))
			continue

		match = reTotalInst.match(line)
		if match:
			iTotalInst = int(match.group(1))
			continue

		match = reTotalPara.match(line)
		if match:
			iTotalPara = int(match.group(1))
			continue

		match = reTotalInstance.match(line)
		if match:
			iTotalInstance = int(match.group(1))
			continue

		match = reInstance.match(line)
		if match:
			iID1 = int(match.group(1))
			iID2 = int(match.group(2))

			currentPair = Pair(iID1, iID2)
			continue

		match = reInst.match(line)
		if match:
			instID = int(match.group(2))
			iValue1 = int(match.group(3))
			iValue2 = int(match.group(4))

			if cmp(match.group(1), 'S') == 0:
				currentPair.InstCmpMapping[instID] = 0
			elif cmp(match.group(1), 'D') == 0:
				currentPair.InstCmpMapping[instID] = 1

			currentPair.Instance1.InstValueMapping[instID] = iValue1
			currentPair.Instance2.InstValueMapping[instID] = iValue2

			continue

		match = rePara.match(line)
		if match:
			paraID = int(match.group(2))
			iValue1 = int(match.group(3))
			iValue2 = int(match.group(4))

			if cmp(match.group(1), 'S') == 0:
				currentPair.ParaCmpMapping[paraID] = 0
			elif cmp(match.group(1), 'D') == 0:
				currentPair.ParaCmpMapping[paraID] = 1

			currentPair.Instance1.ParaValueMapping[paraID] = iValue1
			currentPair.Instance2.ParaValueMapping[paraID] = iValue2

			continue


		match = reLoadSub.match(line)
		if match:
			instID = int(match.group(1))
			iLength1 = int(match.group(2))
			iLength2 = int(match.group(3))

			currentPair.LoadCmpMapping[instID] = [0]
			currentPair.Instance1.LoadLengthMapping[instID] = iLength1
			currentPair.Instance2.LoadLengthMapping[instID] = iLength2

			continue

		match = reLoadEdit.match(line)
		if match:
			instID = int(match.group(1))
			iLength1 = int(match.group(2))
			iLength2 = int(match.group(3))

			valueDis = int(match.group(5))
			reverseDis = int(match.group(7))

			currentPair.LoadCmpMapping[instID] = [1]
			currentPair.LoadCmpMapping[instID].append(valueDis)
			currentPair.LoadCmpMapping[instID].append(reverseDis)

			currentPair.Instance1.LoadLengthMapping[instID] = iLength1
			currentPair.Instance2.LoadLengthMapping[instID] = iLength2

			continue

		match = reFinish.match(line)
		if match:
			vecRedundancy.append(CalRedundancy(currentPair, IDInstMapping, IDParaMapping))


	count = 0

	for redundancy in vecRedundancy:
		print redundancy
		if redundancy[1] < 100 and redundancy[2]/redundancy[1] > 2:
			continue
		if redundancy[2] < 10 :
			continue
		if redundancy[0] >= 0.9:
			count += 1

	print "Total Load:", iTotalLoad
	print "Total Inst:", iTotalInst
	print "Total Para:", iTotalPara
	print "Total Instance:", iTotalInstance

	print "redundant Pair:", count, '/', len(vecRedundancy)
	print 'ratio:', count * 1.0 / len(vecRedundancy)



if __name__ == '__main__':

	if len(sys.argv) != 3:
		exit("parameter number is wrong");

	(IDInstMapping, IDParaMapping) = ParseInstFile(sys.argv[1])
	ParseTraceFile(sys.argv[2], IDInstMapping, IDParaMapping)

	#for key in IDInstMapping:
	#	print "Inst", key, ":"
	#	IDInstMapping[key].DumpInst()

	#for key in IDParaMapping:
	#	print "Para", key, ":"
	#	IDParaMapping[key].DumpPara()

	#print sys.argv[1]
	#print sys.argv[2]