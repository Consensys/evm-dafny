#! python3
"""
Runs measure-complexity with random seeds until it finds CSV logs with Resource Usage <min and >max for the given DisplayName
"""
import argparse
import csv
from math import inf
from os import error, mkdir, rename
import os
import random
import subprocess as sp
import sys
#from shlex import quote
import time
import logging as log
import enum
from datetime import datetime as dt, timedelta as td
from quantiphy import Quantity
# from yaspin import yaspin, Spinner
# from yaspin.spinners import Spinners

def shell(str, **kwargs):
    """Convenient way to run a shell command and get its exit code, stdout, stderr.."""
    r = sp.run(str, shell=True, capture_output=True, text=True, **kwargs)
    #print(r)
    return r

def smag(i) -> str:
    return f"{Quantity(i):.3}"

parser = argparse.ArgumentParser()
parser.add_argument("dafnyfile")
parser.add_argument("--displayname", default="")
parser.add_argument("--min", type=Quantity, default=-inf)
parser.add_argument("--max", type=Quantity, default=inf)
parser.add_argument("extra_args", nargs='?', default="")
parser.add_argument("-v", "--verbose", action="count", default=0)

args = parser.parse_args()

# loglevel = "debug"
# numeric_level = getattr(log, loglevel.upper(), None)
# if not isinstance(numeric_level, int):
#     raise ValueError('Invalid log level: %s' % loglevel)
numeric_level = log.WARNING - args.verbose * 10
log.basicConfig(level=numeric_level,format='%(levelname)s:%(message)s')


uint32_max = 4294967295
random.seed()
ru_gmin = inf
seed_gmin = None
ru_gmax = -inf
seed_gmax = None
Quantity.set_prefs(strip_zeros=False)
iterations = 0
logs_directory: str = "TestResults/" + dt.now().strftime('%Y%m%d-%H%M%S')
os.makedirs(logs_directory)

#with yaspin(Spinner("/-\\|",1000), text="Working...") as spinner:
#    spinner.hide()
while True:
    iterations += 1
    # Better not to simply sweep random-seed from 0 because we'd be repeating that sequence at each new run
    random_seed = random.randint(0, uint32_max)
    #argstring = f"--random-seed {random_seed} "
    argstring = f"--boogie /randomSeed:{random_seed}"
    #argstring += "--iterations 1 "
    argstring += args.extra_args
    argstring4filename = (argstring + args.displayname).replace("/","").replace("--","").replace(" ","").replace(":","")
    d : str = dt.now()
    dstr = d.strftime('%Y%m%d-%H%M%S')
    filename = logs_directory + "/" + dstr + "_" + argstring4filename + ".csv"

    #CLI_line: str = fr"dafny44 measure-complexity --log-format csv\;LogFileName='{filename}' {argstring} {args.dafnyfile}"
    CLI_line: str = fr"dafny44 verify --log-format csv\;LogFileName='{filename}' {argstring} {args.dafnyfile}"
    log.debug("executing: " + CLI_line)
    try:
        res = shell(CLI_line, timeout=10)
    except sp.TimeoutExpired as te:
        log.info(f"Timed out:\n{te}")
        #log.info("executed: " + CLI_line)
        continue

    if res.returncode != 0:
        print(f"returncode={res.returncode}")
        print(f"stdout={res.stdout}")
        print(f"stderr={res.stderr}")
        continue
        #exit(res.returncode)

    if args.displayname == "":
        continue

    with open(filename) as csvfile:
        reader = csv.DictReader(csvfile)
        rows_num = 0
        rus: list[int] = []
        for row in reader:
            rows_num += 1
            log.debug(f"CSV row {rows_num}")
            if args.displayname in row['TestResult.DisplayName'] :
                # if ru == None:
                #     ru = int(row['TestResult.ResourceCount'])
                # else:
                #     # if we run a single iteration, there should be no multiple rows for a given method/function, right? Though those might happen when something is included or whatever...?
                #     log.error(f"File {filename} contains multiple rows for {args.displayname}!")
                #     exit(100)
                rus.append(int(row['TestResult.ResourceCount']))

    if rus == []:
        log.error("DisplayName not in results!")
        exit(100)

    rus.sort()
    rus_min = rus[0]
    rus_max = rus[-1]

    rus_range_str = f"{smag(rus_min)}"

    if rus_min != rus_max:
        rus_range_str += f"..{smag(rus_max)}"

    if rus_min < ru_gmin:
        filename2 = f"{filename[:-4]}MIN{smag(rus_min)}.csv"
        rename(filename, filename2)
        ru_gmin = rus_min
        seed_gmin = random_seed
    elif rus_max > ru_gmax:
        filename2 = f"{filename[:-4]}MAX{smag(rus_max)}.csv"
        rename(filename, filename2)
        ru_gmax = rus_max
        seed_gmax = random_seed

    status = f"iteration {iterations:4}: seed {random_seed:12} -> {len(rus)}/{rows_num} rows, RU {rus_range_str}\t-"
    status += f"\tmin {smag(ru_gmin)} "
    if ru_gmin <= args.min:
        status += "✅"
    status += f"\tmax {smag(ru_gmax)} "
    if ru_gmax >= args.max:
        status += "✅"

    #spinner.text=line #+ "\n"
    #spinner.write(line)
    log.info(status)

    if ru_gmin <= args.min and ru_gmax >= args.max:
        # TODO generate HTML report
        #spinner.write(line)
        break
    else:
        time.sleep(1)

print(f"Done: {iterations} iterations. Max RU = {ru_gmax} with seed {seed_gmax}. Min RU = {ru_gmin} with seed {seed_gmin}.")
