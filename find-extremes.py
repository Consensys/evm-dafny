#! python3
"""
Runs measure-complexity with random seeds until it finds logs with Resource Usage <min and >max
"""
import argparse
import csv
from math import inf
from os import error, rename
import random
import subprocess as sp
import sys
#from shlex import quote
import time
import logging as log
import enum
from datetime import datetime as dt, timedelta as td
from quantiphy import Quantity

def shell(str, **kwargs):
    """Convenient way to run a shell command and get its exit code, stdout, stderr.."""
    r = sp.run(str, shell=True, capture_output=True, text=True, **kwargs)
    #print(r)
    return r

parser = argparse.ArgumentParser()
parser.add_argument("dafnyfile")
parser.add_argument("displayname")
parser.add_argument("min", type=Quantity)
parser.add_argument("max", type=Quantity)
args = parser.parse_args()
#remember there's also sys.argv

loglevel = "debug"
numeric_level = getattr(log, loglevel.upper(), None)
if not isinstance(numeric_level, int):
    raise ValueError('Invalid log level: %s' % loglevel)
log.basicConfig(level=numeric_level,format='%(levelname)s:%(message)s')


uint32_max = 4294967295 # the Dafny random seed is expected as a C# uint32
random.seed()
min_ru = inf
max_ru = -inf
Quantity.set_prefs(strip_zeros=False)

while True:
    # Better not to simply sweep random-seed from 0 because we'd be repeating that sequence at each new run
    random_seed = random.randint(0, uint32_max)
    argstring = f"--random-seed {random_seed}"  # --iterations 1"
    argstring4filename = (argstring + args.displayname).replace("/","").replace("--","").replace(" ","")
    d : str = dt.now()
    dstr = d.strftime('%Y%m%d-%H%M%S')
    filename = "TestResults/" + dstr + "_" + argstring4filename + ".csv"
    # log.debug(f"filename={filename}")

    res = shell(fr"dafny44 measure-complexity --log-format csv\;LogFileName='{filename}' {argstring} {args.dafnyfile}")
    if res.returncode == 0:
        with open(filename) as csvfile:
            reader = csv.DictReader(csvfile)
            ru = None
            for row in reader:
                if args.displayname in row['TestResult.DisplayName'] :
                    if ru == None:
                        ru = int(row['TestResult.ResourceCount'])
                    else:
                        # if we run a single iteration, there should be no multiple rows for a given method/function, right? Though those might happen when something is included or whatever...
                        log.error("Multiple rows for {arg.displayname}!")
                        exit(100)
                    break
        if ru == None:
            log.error("DisplayName not in results!")
            exit(100)
    else:
        print(f"returncode={res.returncode}")
        print(f"stdout={res.stdout}")
        print(f"stderr={res.stderr}")
        #exit(res.returncode)

    rus = f"{Quantity(ru):.3}"
    line = f"seed {random_seed:12} -> {rus:7} RU"

    if ru < min_ru:
        filename2 = f"{filename}MIN{rus}"
        rename(filename, filename2)
        min_ru = ru
        line += "\tMIN"
    elif ru > max_ru:
        filename2 = f"{filename}MAX{rus}"
        rename(filename, filename2)
        max_ru = ru
        line += "\tMAX"

    print(line)

    if min_ru <= args.min and max_ru >= args.max:
        # generate HTML report
        break

