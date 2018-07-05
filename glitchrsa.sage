#!/usr/bin/env sage
#
from Crypto.PublicKey import RSA
from itertools import groupby
import argparse
import logging
import os
import pprint
import time
import csv
from binascii import hexlify
from collections import OrderedDict

parser = argparse.ArgumentParser(description='Break some RSA')
parser.add_argument('pubkey', type=argparse.FileType('r', 0), help='public key file in PEM format')
#parser.add_argument('--out', type=argparse.FileType('wb', 0), help='output file for signature') ## not implemented
parser.add_argument('--sign', type=argparse.FileType('rb', 0), help='binary to sign')
parser.add_argument('--fault', help='fault model to apply, currently replace, glitch0 or glitch1')
parser.add_argument('--pos', type=str, nargs='+', help='a list of space-separated byte positions, or a range (e.g. 0-7) to apply glitch to', default=[0])
parser.add_argument('--byte', type=lambda x: int(x,0), help='byte to replace, use with replacebyte')
parser.add_argument('--group', action='store_true', help="group glitches", default=False)
parser.add_argument('--timeout', type=int, help='timeout for the factorization in seconds', default=300)
parser.add_argument('--debug', action='store_true', help='enable debug messages')
parser.add_argument('--threads', type=int, help='number of threads to use for factoring', default=2)
parser.add_argument('--log', type=argparse.FileType('a', 0), help='filename for log')
parser.add_argument('--stats', type=argparse.FileType('a', 0), help='filename for factoring statistics csv')
args = parser.parse_args()

arguments = []
for argument in args.pos:
    if '-' in argument:
        splt = argument.split('-')
        if args.group == True:
            arguments.append(range(int(splt[0]), int(splt[1]) + 1))
        else:
            arguments.extend(range(int(splt[0]), int(splt[1]) + 1))
    else:
        if args.group == True:
            arguments.append([int(argument)])
        else: 
            arguments.append(int(argument))

if args.group == True:
    args.pos = arguments
else:
    args.pos = list(OrderedDict.fromkeys(arguments))

#print args.pos

pp = pprint.PrettyPrinter()

# Fault models to implement: 
# Flip single bit
# Set single bit to 0 or 1
# Zeroize arbitrary byte(s)     # DONE
# Set arbitrary byte(s) to 0xFF # DONE
# Randomize byte (probably only useful for testing)
# Early break from copy loop (zeroize rest of data or 0xFF (depending on memset?)) # possible with group option
# User-supplied mask

def log_to_file(s):
    if args.log != None:
        args.log.write(s)

def split_int(n):
    """ split_int(n): Split an integer n into a list of bytes by shifting. List is little-endian.
    """
    octets = []
    for byte in range(0, ceil(n.nbits()/8)):
        octets.append( ( n >> (byte*8)) & 0xFF)
    return octets

def glue_int(octets):
    """ glue_int(octets): Glue a list of bytes back togeter to an integer. Little-endian.
    """
    out = 0
    for byte in range(len(octets)):
        out += (octets[byte] << (byte * 8))
    return out

def glitch_bytes(n, pos, glitch, byte):
    if byte == None:
        byte = 0x00
    octets = split_int(n)
    for p in pos:
        if glitch == 'glitch1':
            octets[p] = 0xFF
        elif glitch == 'glitch0':
            octets[p] = 0x00
        elif glitch == 'replace':
            octets[p] = byte
    return glue_int(octets)

@parallel(ncpus=args.threads, timeout=args.timeout)#, verbose=args.debug)
def ecm_factor(n):
    ecm = ECM()
    start = int(time.time())
    log_to_file("Attempting to factor " + hex(n) +"\n")
    result = ecm.factor(n)
    timetaken = int(time.time()) - start
    log_to_file("Factored " + hex(n) + " in " + str(timetaken) + " seconds\nFactors: " + pp.pformat(result) +"\n")
    logging.debug("Found factors of %x, which took %d seconds:\n %r", n, timetaken, result)
    return result, timetaken

def eulerphi(factors):
    """ euler(factors)
        Compute eulers totient over a list of prime factors, taking into account repeating factors
    """
    factors = sorted(factors)                               # should already be sorted, but just to make sure
    f = [(p, len(list(k))) for p, k in groupby(factors)]    # make a list of factors and their multiplicity, so if there are 8 2's, it becomes a tuple (2,8)
    t = 1
    for p in f:
        if p[1] > 1:                                        # prime power, special case
            t *= (p[0]^(p[1]-1)) * (p[0]-1)                 # Euler's function for prime powers is (p**k-1) * (p-1), p is the prime factor and k is it's multiplicity
        else:                                               # not a multiple, use regular (p-1) algorithm.
            t *= p[0]-1
    return t


def calc_d(factors, e):
    
    t = eulerphi(factors)
    checkt = gcd(t,e)
    
    if checkt != 1:
        logging.warning("totient should be coprime with e but gcd is %d", checkn)
        return None

    d = inverse_mod(e, t)
    
    checkd = mod(e*d, t) # This is redundant?
    if checkd != 1:
        logging.warning("ed mod totient is %d but it should be 1!", checkd)
        return None
    return d  

def create_privkey(n,e,d, factors, fhandle):
    # Need to get rid of this fake p & q craziness...
    fake_p = factors[-1]
    fake_q = prod(factors[:-1])

    # p should be bigger than q, not that it really matters...
    if fake_p < fake_q:
        fake_p, fake_q = fake_q, fake_p

    key = RSA.construct((long(n), long(e), long(d), long(fake_p), long(fake_q)))
    fhandle.write(key.exportKey('PEM'))

def read_pubkey(fhandle):
    pubkey = RSA.importKey(fhandle.read())
    return Integer(pubkey.n), Integer(pubkey.e)

def read_message(fhandle):
    message = fhandle.read()
    message = hexlify(message)
    return Integer(int(message, 16))

def check_message(message, n):
    # Check if message is too long for key
    if message.nbits() > n.nbits()-1:
        logging.debug("The message is too long for this key!")
        return False
    # Check if message can be signed by this modulus
    elif gcd(message, n) != 1:
        logging.debug("The message and modulus are not coprime.")
        return False
    else:
        return True

def init_logging(debug):
    if debug == True:
        log_level = logging.DEBUG
    else:
        log_level = logging.INFO
    logging.basicConfig(level=log_level, format='%(message)s')

def test_key(n,e,d):
    l = n.nbits() - 1
    rand = Integer(getrandbits(l))
    c = power_mod(rand, e, n)
    return rand, power_mod(c,d,n)

def random_test(i, n, e, d):
    logging.debug("Running %d random encrypt/decrypt tests", i)
    successes = []
    failures = []
    for j in range(i):
        test = test_key(n,e,d)
        if test[0] == test[1]:
            successes.append((test[0],test[1]))
        else:
            failures.append((test[0],test[1]))
    logging.debug("Successes: %d Failures %d", len(successes), len(failures))

#    if len(failures) > 0:
#        logging.debug("Here is a failure: %r", failures[0])

def sign(m,d,n):
    if d == None:
        return None
    else:
        return power_mod(m,d,n)

def parallel_factor(modulo_list):
    result = list(ecm_factor(modulo_list)) # cast to list to get rid of generator
    thefactors = [x[1][0] if 'NO DATA' not in x[1] else x[1] for x in result]
    timetaken = [str(x[1][1]) for x in result if 'NO DATA' not in x[1]]
    log_to_file("Failed to factor:\n" + pp.pformat([hex(x[0][0][0]) for x in result if 'NO DATA' in x[1]]) + "\n")
    stats_dict['factortimes'].extend(timetaken)
    return thefactors 

def chunker(l, n):
    for i in range(0, len(l), n):
        yield l[i:i+n]

def start_glitching(n, e, glitch, pos, threads, byte, message=None):
    glitches = []
    factorizations = []
    keypairs = []
     
    for p in pos:
        if args.group == True:
            glitches.append(glitch_bytes(n, p, glitch, byte))
        else: 
            glitches.append(glitch_bytes(n, [p], glitch, byte))

    if message != None:
        orig_len = len(glitches)
        glitches = [g for g in glitches if check_message(message, g) == True]
        logging.debug("Removing %d moduli that are unsuitable for this message", orig_len - len(glitches))

    logging.info("Going to factor %d glitched moduli with fault %s", len(glitches), glitch)
    stats_dict['attempts'] = len(glitches)

    chunks = chunker(glitches, threads)
    n_chunk = 1
    n_chunks = ceil(Integer(len(glitches)) / Integer(threads))

    for chunk in chunks:
        log_to_file("Starting chunk "+ str(n_chunk) +" ########################################################################\n")
        logging.info("Trying chunk %d out of %d", n_chunk, n_chunks)
        thefactors = parallel_factor(chunk) # timeout gets set in function decorator for ecm_factor
        thefactors = [x for x in thefactors if 'NO DATA' not in x] # pruning timeouts from results
        if len(thefactors) == 0:
            logging.info("Unable to factor this chunk in time limit given")
        else:
            logging.info("%d factorization(s) found in this chunk", len(thefactors))
            factorizations.extend(thefactors)
        log_to_file("Ended chunk "+ str(n_chunk) +"\n")
        n_chunk += 1
        os.system("pkill ecm") # clean up ecm processes that @parallel fails to kill

    if len(factorizations) == 0:
        logging.warning("We did not succeed in factoring any moduli")
        sys.exit()
    logging.info("%d factorization(s) found", len(factorizations))
    logging.debug("Factorizations:\n%s", pp.pformat(factorizations))

    # calulate the private key for each
    for fact in factorizations:
        keypairs.append({'n': prod(fact), 'd':calc_d(fact, e)})
    return keypairs

stats_dict = {}

def main():

    log_to_file("Starting run at " + time.ctime() + "\n")
    log_to_file("===============================================RUN START===============================================\n")

    init_logging(args.debug)

    # Read in the original public key
    n,e = read_pubkey(args.pubkey)

    log_to_file("Original modulus ("+ str(n.nbits()) + " bits): " + hex(n) +"\n")
    log_to_file("Fault model " + args.fault + " at positions " + repr(args.pos) + "\n")
    log_to_file("Timeout " + str(args.timeout) + " seconds\n")
    
    stats_dict['keysize'] = n.nbits()
    stats_dict['timeout'] = args.timeout
    stats_dict['fault'] = args.fault
    stats_dict['factortimes'] = []

    # Read in the message to sign
    if args.sign is not None:
        message = read_message(args.sign)
    else:
        message = None
    
    # Glitch and try to factor
    successes = start_glitching(n, e, args.fault, args.pos, args.threads, args.byte, message)
    log_to_file("Done factoring at: " + time.ctime() + "\n")
    stats_dict['successes'] = len(successes)
    stats_dict['failures'] = stats_dict['attempts'] - stats_dict['successes']

    if args.debug:
        for key in successes:
            random_test(100, key['n'], e, key['d'])

    if message is not None:
        logging.info("Calculating signatures")
        for key in successes:
            key['sig'] = sign(message,key['d'],key['n'])
            key['e'] = e

    logging.info("Results: \n%s", pp.pformat(successes))
    log_to_file("Results: \n" + pp.pformat(successes) + "\n================================================RUN END================================================\n")
   
    stats_dict['factortimes'] = ' '.join(stats_dict['factortimes'])
    if args.stats != None :
        c = csv.writer(args.stats)
        if os.path.getsize(args.stats.name) == 0: # Write the header if the file doesn't exist already
            c.writerow(stats_dict.keys())
        c.writerow(stats_dict.values())


if __name__ == "__main__":
    main()
