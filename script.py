import os as os
import re
import numpy as np
import sys
import time
import matplotlib.pyplot as plt
import struct
import binascii as bn
import aeskeyschedule as aeskey
import lecroyparser as lec
from scipy.fftpack import fft  
import sys, traceback
from Cryptodome.Cipher import AES


###########################AES#################################################
INVSBOX = [
0x52,0x09,0x6a,0xd5,0x30,0x36,0xa5,0x38,0xbf,0x40,0xa3,0x9e,0x81,0xf3,0xd7,0xfb,
0x7c,0xe3,0x39,0x82,0x9b,0x2f,0xff,0x87,0x34,0x8e,0x43,0x44,0xc4,0xde,0xe9,0xcb,
0x54,0x7b,0x94,0x32,0xa6,0xc2,0x23,0x3d,0xee,0x4c,0x95,0x0b,0x42,0xfa,0xc3,0x4e,
0x08,0x2e,0xa1,0x66,0x28,0xd9,0x24,0xb2,0x76,0x5b,0xa2,0x49,0x6d,0x8b,0xd1,0x25,
0x72,0xf8,0xf6,0x64,0x86,0x68,0x98,0x16,0xd4,0xa4,0x5c,0xcc,0x5d,0x65,0xb6,0x92,
0x6c,0x70,0x48,0x50,0xfd,0xed,0xb9,0xda,0x5e,0x15,0x46,0x57,0xa7,0x8d,0x9d,0x84,
0x90,0xd8,0xab,0x00,0x8c,0xbc,0xd3,0x0a,0xf7,0xe4,0x58,0x05,0xb8,0xb3,0x45,0x06,
0xd0,0x2c,0x1e,0x8f,0xca,0x3f,0x0f,0x02,0xc1,0xaf,0xbd,0x03,0x01,0x13,0x8a,0x6b,
0x3a,0x91,0x11,0x41,0x4f,0x67,0xdc,0xea,0x97,0xf2,0xcf,0xce,0xf0,0xb4,0xe6,0x73,
0x96,0xac,0x74,0x22,0xe7,0xad,0x35,0x85,0xe2,0xf9,0x37,0xe8,0x1c,0x75,0xdf,0x6e,
0x47,0xf1,0x1a,0x71,0x1d,0x29,0xc5,0x89,0x6f,0xb7,0x62,0x0e,0xaa,0x18,0xbe,0x1b,
0xfc,0x56,0x3e,0x4b,0xc6,0xd2,0x79,0x20,0x9a,0xdb,0xc0,0xfe,0x78,0xcd,0x5a,0xf4,
0x1f,0xdd,0xa8,0x33,0x88,0x07,0xc7,0x31,0xb1,0x12,0x10,0x59,0x27,0x80,0xec,0x5f,
0x60,0x51,0x7f,0xa9,0x19,0xb5,0x4a,0x0d,0x2d,0xe5,0x7a,0x9f,0x93,0xc9,0x9c,0xef,
0xa0,0xe0,0x3b,0x4d,0xae,0x2a,0xf5,0xb0,0xc8,0xeb,0xbb,0x3c,0x83,0x53,0x99,0x61,
0x17,0x2b,0x04,0x7e,0xba,0x77,0xd6,0x26,0xe1,0x69,0x14,0x63,0x55,0x21,0x0c,0x7d ]


# SBOX = sub-bytes table
SBOX= [
0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76,
0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0,
0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15,
0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75,
0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84,
0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf,
0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8,
0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,
0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,
0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb,
0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,
0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08,
0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,
0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,
0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,
0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16 ]

# hamming weight tabela
HWTable=[0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4, 1, 2, 2, 3, 2, 3,
       3, 4, 2, 3, 3, 4, 3, 4, 4, 5, 1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4,
       3, 4, 4, 5, 2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, 1, 2,
       2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5, 2, 3, 3, 4, 3, 4, 4, 5,
       3, 4, 4, 5, 4, 5, 5, 6, 2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5,
       5, 6, 3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7, 1, 2, 2, 3,
       2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5, 2, 3, 3, 4, 3, 4, 4, 5, 3, 4,
       4, 5, 4, 5, 5, 6, 2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
       3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7, 2, 3, 3, 4, 3, 4,
       4, 5, 3, 4, 4, 5, 4, 5, 5, 6, 3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6,
       5, 6, 6, 7, 3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7, 4, 5,
       5, 6, 5, 6, 6, 7, 5, 6, 6, 7, 6, 7, 7, 8]
    
### PRIMEIRA ETAPA => COLETAMOS AQUI OS VALORES DO DISPOSITIVO, COMO SE FOSSE A QUANTIDADE DE VEZES QUE O DISPOSITIVO FOI ACIONADO
def CreateFileList_trc(folder):
    FileListAll=os.listdir(folder)
    FileList=[]
    for i in range(len(FileListAll)):
        temp=FileListAll[i]
        if temp.find('.trc')>0:
            FileList.append(temp)
    return(FileList)

### SEGUNDA ETAPA => FAZ O GRÁFICO DO SIDE CHANNEL ( SCA ) 
def Scope(Folder,nfig=1,colortrace='k',Style='Raw',nbtraces=1):
    FileList=CreateFileList_trc(Folder)
    Data=[]
    for i in range(nbtraces):
        file=os.path.join(Folder,FileList[i])
        with open(file,"rb") as f:
            Data.append(np.fromfile(f,dtype=np.int8))
    Data=np.asarray(Data)
    if Style=='Raw':
        plt.figure(nfig)
        plt.plot(np.transpose(Data),colortrace)
        plt.grid()
        #plt.show()
        return plt
    if Style=='Mean':
        plt.figure(nfig)
        plt.plot(np.mean(Data,axis=0),colortrace)
        plt.grid()
        #plt.show()
        return plt
    if Style=='Var':
        plt.figure(nfig)
        plt.plot(np.var(Data,axis=0),colortrace)
        plt.grid()
        #plt.show()
        return plt
    if Style=='MinMax':
        plt.figure(nfig)
        plt.plot(np.max(Data,axis=0),colortrace)
        plt.plot(np.min(Data,axis=0),colortrace)
        plt.grid()
        #plt.show()
        return plt
    return()


##########################ReadTRACESbin#######################################
def ReadTRACESbin(Folder,FileList,num):
    # Filelist obtenue avec CreateFileList
    # num : position du FileName dans FileList
    FileName=FileList[num]
    Items=re.split("[= _ .]",FileName)
    key=Items[4]
    keyhex=bn.unhexlify(key)
    K1=aeskey.key_schedule(keyhex)[0]  
    K10=aeskey.key_schedule(keyhex)[10]    
    pti=Items[6]
    cto=Items[8]

    Key=[]
    Pti=[]
    Cto=[]
    for i in range(16):
        Key.append((int(key[i*2:(i+1)*2],16)))
        Pti.append((int(pti[i*2:(i+1)*2],16)))
        Cto.append((int(cto[i*2:(i+1)*2],16)))
    file=os.path.join(Folder,FileName)
    with open(file,"rb") as f:
        Data=np.fromfile(f, dtype=np.int8)
    if i ==1:
        print(Data)
    return(Key,Pti,Cto,Data,K1,K10)
##########################ReadTRACESbin#######################################

### Usa a tabela HWTable, que é os pesos de hamming 
def IVptixork():
    HW=np.zeros((256,256),dtype='float')
    for o in range(256):
        for k in range(256):
            HW[o,k] = HWTable[o^k]
    return (HW)


### Usa a tabela subbytes do protocolo AES com a tabela de hamming, isso quer dizer que
### iremos no indice da tabela de hamming com ajuda da tabela de subbytes, retorna uma
### matriz 256x256
def IVSBOXptixork():
    HW=np.zeros((256,256),dtype='float')
    for o in range(256):
        for k in range(256):
            HW[o,k] = HWTable[SBOX[o^k]]
    return (HW)

'''
# LeakageAss of the second class
def LeakageAss(Folder,noctet,nfig,nbtraces):
    FileList=CreateFileList_trc(Folder)
    Key,Pti,Cto,Data,K1,K10=ReadTRACESbin(Folder,FileList,0)
    High=np.zeros(len(Data),dtype='float')
    CountHigh=0
    Low=np.zeros(len(Data),dtype='float')
    CountLow=0
    HW= IVSBOXptixork()
    
    for i in range(nbtraces):
        Key,Pti,Cto,Data,K1,K10 =ReadTRACESbin(Folder,FileList,i)
        if i>0 and i%100 == 0:
            print('Traitement trace n* ' + str(i))
            
        if HW[Pti[noctet],K1[noctet]]>4:    # se a posição na matriz de hamming é maior q 4
            High+=np.asarray(Data)          # soma o high com ele, esse valor "Data" é o que ta no arquivo
            CountHigh+=1
        else:
            Low+= np.asarray(Data)
            CountLow+=1
    
    MeanHigh=High/CountHigh
    MeanLow=Low/CountLow

    plt.figure(nfig)
    plt.subplot(2,1,1)
    plt.plot(MeanHigh,'r')
    plt.plot(MeanLow,'b')
    plt.subplot(2,1,2)
    plt.plot(MeanHigh-MeanLow,'b')
    plt.show()
    return()
'''

def LeakageAss(Folder,noctet,nfig,nbtraces):
    FileList=CreateFileList_trc(Folder)
    Key,Pti,Cto,Data,K1,K10=ReadTRACESbin(Folder,FileList,0)
    
    X=np.zeros(len(Data),dtype='float')
    Xsq=np.zeros(len(Data),dtype='float')    # raiz quadrada de X 
    XY=np.zeros((256,len(Data)),dtype='float')
    Y=np.zeros(256,dtype='float')
    Ysq=np.zeros(256,dtype='float')          # raiz quadrada de Y
    VX = np.zeros(len(Data),dtype='float')
    VY = np.zeros(256,dtype='float')
    CovXY =np.zeros(256,len(Data),dtype='float')
    CorXY =np.zeros(256,len(Data),dtype='float')
    
    HW=IVSBOXptixork()
    
    for i in range(len(FileList)):
        Key,Pti,Cto,Data,K1,K10=ReadTRACESbin(Folder,FileList,i)
        Data = np.asarray(Data).astype('float')
        X+=Data
        Xsq+=Data**2
        Y+=HW[Pti[noctet],K1[noctet]]
        Ysq+=HW[Pti[noctet],K1[noctet]]**2
        XY+=HW[Pti[noctet],K1[noctet]]*np.asarray(Data)
        
        if i>0 and i%100==0:
            print('Tratamento do grafico numero: ' + str(i))
            VX=Xsq/(i+1) - (X/(i+1))**2
            VY=Ysq/(i+1) - (Y/(i+1))**2
            CovXY = (XY)/(i+1) - (X/(i+1)) * (Y/(i+1))
            CorXY=CovXY/(VX*VY)**0.5
    plt.figure(nfig)
    plt.plot(CorXY)
        
    plt.show()        
    return()

def DPA(Folder,noctect,nfig=1,nbtraces=1000):
    FileList=CreateFileList_trc(Folder)
    Key,Pti,Cto,Data,K1,K10=ReadTRACESbin(Folder, FileList, 0)
   
    MeanHigh = np.zeros((256,len(Data)), dtype='float')
    CountHigh = np.zeros(256,dtype='float')
    MeanLow = np.zeros((256,len(Data)), dtype='float')
    CountLow = np.zeros(256,dtype='float')
    Low = np.zeros((256,len(Data)),dtype='float')
    High = np.zeros((256,len(Data)),dtype='float')
   
    HW= IVSBOXptixork()
   
    for i in range(nbtraces):
        Key,Pti,Cto,Data,K1,K10=ReadTRACESbin(Folder, FileList, i)
           
        for k in range(256):
            if HW[Pti[noctect],k]>4:
                High[k,:]+=np.asarray(Data)
                CountHigh[k]+=1
            else:
                Low[k,:]+=np.asarray(Data)
                CountLow[k]+=1
               
        if i>0 and i%100==0:
            #print('Traitement trace n° ' + str(i))
               
            for k in range(256):
                MeanHigh[k,:]=(High[k,:]/CountHigh[k])
                MeanLow[k,:]=(Low[k,:]/CountLow[k])    
       
            DoMmax = np.max(abs(MeanHigh-MeanLow),axis=1)
            keyfound=np.argmax(DoMmax)
            #print('Keyfound : ' + str(keyfound))
            #print('True Key : ' + str(K1[noctect]))
           
    return(abs(MeanHigh-MeanLow),keyfound,K1[noctect])


Folder='TracesEM_ferrite'
# PRIMEIRA AULA FOI ISSO
'''graphs = []
graphs.append(Scope(Folder,nfig=1,colortrace='k',Style='Raw',nbtraces=100))
graphs.append(Scope(Folder,nfig=1,colortrace='r--',Style='MinMax',nbtraces=100))
graphs.append(Scope(Folder,nfig=1,colortrace='b',Style='Mean',nbtraces=100))
for i in graphs:
    i.show()
Scope(Folder,nfig=2,colortrace='b',Style='Var',nbtraces=100).show()
'''

####################################################################################
# SEGUNDA AULA FOI ISSO
'''
np.set_printoptions(threshold=sys.maxsize)     # para ver toda a matriz
# Plotando a matriz como um mapa de calor
matriz = IVptixork()
plt.figure(figsize=(10, 8))
plt.imshow(matriz, cmap='hot', interpolation='nearest')
plt.colorbar(label='Peso de Hamming')
plt.xlabel('Valor de k')
plt.ylabel('Valor de o')
plt.title('Mapa de Calor do Peso de Hamming')
plt.show()

LeakageAss(Folder,1,1,5000)
'''
####################################################################################

#TERCEIRA AULA FOI ISSO

####################################################################################
'''
DoM,keyfound,TrueKey = DPA(Folder,0,nfig=1,nbtraces=5000)

plt.plot(np.transpose(DoM),'k')
plt.plot(DoM[keyfound],'r')
plt.plot(DoM[TrueKey],'bo')

plt.show()
'''
LeakageAss(Folder,1,nfig=1,nbtraces=5000)