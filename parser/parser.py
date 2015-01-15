from os import listdir
from os.path import isfile, join
from struct import *
from sets import Set

def minimun(A, B, C):
    if A > B:
        if B > C:
            return C
        else:
            return B
    else:
        if A > C:
            return C
        else:
            return A



def EditDistance(seqA, seqB):
    
    d = []
    for i in range(len(seqA)+1):
        d.append([])
        for j in range(len(seqB)+1):
            d[i].append(0)
            
   
    for i in range(len(seqA)+1):
        d[i][0] = i
       
    for j in range(len(seqB)+1):
        d[0][j] = j
       
    for i in range(1, len(seqA) + 1):
        #print i
        for j in range(1, len(seqB) + 1):
            if seqA[i-1] == seqB[j-1]:
                d[i][j] = d[i-1][j-1]
            else:
                d[i][j] = minimun(d[i-1][j], d[i-1][j-1], d[i][j-1]) + 1
                
          
    return d[len(seqA)][len(seqB)]
       

def EditDistance2(seqA, seqB):
    d = []
    d.append([])
    d.append([])
    
    for j in range(len(seqB)+1):
        d[0].append(j)
        d[1].append(0)
    
    index = 0
    for i in range(1, len(seqA) + 1):
        if i % 1000 == 0:
            print i
        last = index
        index = (index + 1) % 2

        for j in range(1, len(seqB) + 1):
            if seqA[i-1] == seqB[j-1]:
                
                if j == 1:
                    d[index][j] = i -1
                else:
                    d[index][j] = d[last][j-1]
                
            else:
                if j == 1:
                    
                    d[index][j] = minimun(d[last][j], i-1, i) + 1
                    
                else:
                   
                    d[index][j] = minimun(d[last][j], d[last][j-1], d[index][j-1]) + 1

        
    return d[index][len(seqB)]

def CompTwoConsecutiveInstances(InstanceA, InstanceB, setDifferentPara, setDifferentInst):
    if InstanceA[0][0] != 4 or InstanceB[0][0] != 4:
        print 'Start Record Is Not Delimiter'
        exit(0)
    
    if InstanceA[0][1] + 1 != InstanceB[0][1]:
        print 'Delimiter Number Is Wrong\n'
        exit(0)


    mapParaA = {}
    indexA = 1
    
    while indexA < len(InstanceA):
        if InstanceA[indexA][0] != 3:
            break
        mapParaA[InstanceA[indexA][1]] = InstanceA[indexA][2]    
        indexA += 1
        
    mapParaB = {}
    indexB = 1
    
    while indexB < len(InstanceB):
        if InstanceB[indexB][0] != 3:
            break
        mapParaB[InstanceB[indexB][1]] = InstanceB[indexB][2]    
        indexB += 1
        
    for key in mapParaA:
        if mapParaA[key] != mapParaB[key]:
            print key, mapParaA[key], mapParaB[key]
            if setDifferentPara.get(key) == None:
                setDifferentPara[key] = Set([])
            setDifferentPara[key].add(mapParaA[key])
            setDifferentPara[key].add(mapParaB[key])
            
            
            
    mapInstA = {}        
    while indexA < len(InstanceA):
        if InstanceA[indexA][0] != 2:
            break
        mapInstA[InstanceA[indexA][1]] = InstanceA[indexA][2]    
        indexA += 1
        
    mapInstB = {}
    while indexB < len(InstanceB):
        if InstanceB[indexB][0] != 2:
            break
        mapInstB[InstanceB[indexB][1]] = InstanceB[indexB][2]    
        indexB += 1
        
    for key in mapInstA:
        if mapInstA[key] != mapInstB[key]:
            print key, mapInstA[key], mapInstB[key]
            if setDifferentInst.get(key) == None:
                setDifferentInst[key] = Set([])
            setDifferentInst[key].add(mapInstA[key])
            setDifferentInst[key].add(mapInstB[key])
            
            
    mapLoadA = {}
    mapLoadB = {}
    
    while indexA < len(InstanceA):
        if mapLoadA.get(InstanceA[indexA][1]) == None:
            mapLoadA[InstanceA[indexA][1]] = []
        mapLoadA[InstanceA[indexA][1]].append([InstanceA[indexA][2], InstanceA[indexA][3]])
        indexA += 1
        
    print 'after building loadA'
        
    while indexB < len(InstanceB):
        if mapLoadB.get(InstanceB[indexB][1]) == None:
            mapLoadB[InstanceB[indexB][1]] = []
        mapLoadB[InstanceB[indexB][1]].append([InstanceB[indexB][2], InstanceB[indexB][3]])
        indexB += 1

    print 'after building loadB'

    for key in mapLoadA:
        listAddressA = []
        listAddressB = []
        
        listValueA = []
        listValueB = []
        
        for index in range(len(mapLoadA[key])):
            listAddressA.append(mapLoadA[key][index][0])
            listValueA.append(mapLoadA[key][index][1])
            
        print len(listAddressA), len(listValueA)
        for index in range(len(mapLoadB[key])):
            listAddressB.append(mapLoadB[key][index][0])
            listValueB.append(mapLoadB[key][index][1])
            
        print len(listAddressB), len(listValueB)
            
        print key, EditDistance2(listAddressA, listAddressB), EditDistance(listValueA, listValueB)
        


if __name__=='__main__':

    strA = 'abcdefgaaaaaaaaaaaaaaa'
    strB = 'a'
    print EditDistance(strB, strA)
    print EditDistance(strA, strB)
    print EditDistance2(strB, strA)
    print EditDistance2(strA, strB)
    exit(0)

    file_list = [ f for f in listdir('/dev/shm') if isfile(join('/dev/shm',f)) ]
    
    logFiles = []
    for f in file_list:
        if f.find('CPI-') == 0:
            logFiles.append(f)
                     
    latest = max(logFiles)
    print latest
    
    log = open('/dev/shm/' + latest, "rb")
    
    count = 0
    
    vecInstances = []
    while True:
        bytes = log.read(32)
        if not bytes:
            break
            
        record_type = unpack('i', bytes[0:4])
        if record_type[0] == 4:
            numExecution =  unpack('l', bytes[8:16])
            vecInstances.append([])
            vecInstances[len(vecInstances)-1].append([record_type[0], numExecution[0]])
        elif record_type[0] == 2:
            uInstructionID = unpack('I', bytes[8:12])
            Value          = unpack('l', bytes[16:24])
            vecInstances[len(vecInstances)-1].append([record_type[0], uInstructionID[0], Value[0]])
        elif record_type[0] == 0:
            uInstructionID = unpack('I', bytes[8:12])
            LoadAddress    = unpack('l', bytes[16:24])
            LoadValue      = unpack('l', bytes[24:32])
            vecInstances[len(vecInstances)-1].append([record_type[0], uInstructionID[0], LoadAddress[0], LoadValue[0]])
        elif record_type[0] == 3:
            uValueID = unpack('I', bytes[8:12])
            Value    = unpack('l', bytes[16:24])
            vecInstances[len(vecInstances)-1].append([record_type[0], uValueID[0], Value[0]])
        
        count += 1
        
    
    log.close()
    
    print count
    print len(vecInstances)
    
    setDifferentPara = {}
    setDifferentInst = {}
    
    
    for i in range(0, len(vecInstances)/2):
        CompTwoConsecutiveInstances(vecInstances[i*2], vecInstances[i*2+1], setDifferentPara, setDifferentInst)
