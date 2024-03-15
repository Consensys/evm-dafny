#! python3
"""
Runs dafny's measure-complexity with the given args,
stores the CSV file with the args in the filename for easier bookkeeping,
and runs dafny-reportgenerator on that file
"""

import argparse
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
parser.add_argument("extra_args", nargs='?', default="")
args = parser.parse_args()


loglevel = "debug"
numeric_level = getattr(log, loglevel.upper(), None)
if not isinstance(numeric_level, int):
    raise ValueError('Invalid log level: %s' % loglevel)
log.basicConfig(level=numeric_level,format='%(levelname)s:%(message)s')

argstring = args.extra_args
dafnyfile = args.dafnyfile
argstring4filename = f"{args.dafnyfile}{argstring}".replace("/","").replace("-","").replace(":","").replace(" ","")
d : str = dt.now()
dstr = d.strftime('%Y%m%d-%H%M%S')
filename = "TestResults/" + dstr + "_" + argstring4filename + ".csv"
#log.debug(f"filename={filename}")
cli = fr"dafny44 measure-complexity --log-format csv\;LogFileName='{filename}' {argstring} {dafnyfile}"
log.debug(f"Executing:{cli}")
res = shell(cli)
#res = shell(fr"dafny44 verify --log-format csv\;LogFileName='{filename}' {argstring} {dafnyfile}")
if res.returncode != 0:
    print(f"out: {res.stdout}")
    print(f"err: {res.stderr}")
    exit(res.returncode)
cli = f"dafny-reportgenerator summarize-csv-results --max-resource-cv-pct 10 '{filename}'"
log.debug(f"Executing:{cli}")
res = shell(cli)
print(res.stdout)