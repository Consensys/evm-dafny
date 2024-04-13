#! python3
"""
Make it easier to run measure-complexity, store its log file with the current date and run a tool on it

Runs dafny's measure-complexity with the given args,
stores the CSV file with the args in the filename for easier bookkeeping,
and runs dafny-reportgenerator on that file
"""

import argparse
import os
import subprocess as sp
import sys
#from shlex import quote
import time
import logging as log
import enum
from datetime import datetime as dt, timedelta as td

def shell(str, **kwargs):
    """Convenient way to run a CLI string and get its exit code, stdout, stderr.."""
    r = sp.run(str, shell=True, capture_output=True, text=True, **kwargs)
    #print(r)
    return r

parser = argparse.ArgumentParser()
parser.add_argument("dafnyfile")
parser.add_argument("-e", "--extra_args", default="")
parser.add_argument("-d", "--dafnyexec", default="dafny")
parser.add_argument("-r", "--rseed", default=str(int(time.time())))
parser.add_argument("-i", "--iter", default="1")
parser.add_argument("-f", "--format", default="json")
args = parser.parse_args()


loglevel = "debug"
numeric_level = getattr(log, loglevel.upper(), None)
if not isinstance(numeric_level, int):
    raise ValueError('Invalid log level: %s' % loglevel)
log.basicConfig(level=numeric_level,format='%(levelname)s:%(message)s')

argstring4filename = f"{args.dafnyexec}{args.dafnyfile}rs{args.rseed}i{args.iter}{args.extra_args}".replace("/","").replace("-","").replace(":","").replace(" ","")
d : str = dt.now()
dstr = d.strftime('%Y%m%d-%H%M%S')
filename = "TestResults/" + dstr + "_" + argstring4filename
#log.debug(f"filename={filename}")
#shell_line = fr"{args.dafnyexec} measure-complexity --log-format csv\;LogFileName='{filename}' {args.extra_args} {args.dafnyfile}"
#log.info(f"Executing:{args.dafnyexec} {cli_args}")

#CHANGE TO USE os.execvp()
arglist = [
    args.dafnyexec,
    "measure-complexity",
    "--random-seed",
    args.rseed,
    "--iterations",
    args.iter,
    "--log-format",
    f"{args.format};LogFileName={filename}.{args.format}",
    *args.extra_args.split(),

    args.dafnyfile
    ]
log.info(f"Executing:{args.dafnyexec} {" ".join(arglist)}")
os.execvp(args.dafnyexec, arglist )


res = shell(args.dafnyexec + " " + shell_line)
#res = shell(fr"dafny44 verify --log-format csv\;LogFileName='{filename}' {argstring} {dafnyfile}")
print(f"out: {res.stdout}")
if res.returncode != 0:
    print(f"err: {res.stderr}")
    exit(res.returncode)

shell_line = f"dafny-reportgenerator summarize-csv-results --max-resource-cv-pct 10 '{filename}'"
log.debug(f"Executing:{shell_line}")
res = shell(shell_line)
print(f"out: {res.stdout}")
if res.returncode != 0:

    print(f"err: {res.stderr}")
    exit(res.returncode)