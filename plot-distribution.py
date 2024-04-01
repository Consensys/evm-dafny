#! python3


# We want to print a histogram for each of the displaynames
# linear X, log Y
# given a directory of CSVs,
# gather all the Resource Counts for each DisplayName
# no matter if there's multiple rows per CSV

# see "bars with legend" in https://matplotlib.org/stable/gallery/statistics/histogram_multihist.html#sphx-glr-gallery-statistics-histogram-multihist-py
# density = True looks good


import argparse
import csv
import logging as log
import os
import pickle
from time import sleep
# from matplotlib.container import BarContainer
# import matplotlib.pyplot as plt
# from matplotlib.ticker import EngFormatter
#from matplotlib.animation import adjusted_figsize
import numpy as np
import re
from datetime import datetime as dt, timedelta as td

from quantiphy import Quantity


def cleanDisplayName(dn:str) -> str:
    new = dn.replace("(well-formedness)","WF")
    new = re.sub(r"\(assertion batch (\d+)\)",r"AB\1", new)
    return new.strip()

def readCSV(fullpath) -> int:
    """Reads the CSV into the global usages map"""
    rows = 0
    global usages
    with open(fullpath) as csvfile:
        reader = csv.DictReader(csvfile)
        for row in reader:
            rows += 1
            dn = cleanDisplayName(row['TestResult.DisplayName'])
            rc = row['TestResult.ResourceCount']
            usages[dn] = usages.get(dn,[]) + [int(rc)]
    log.info(f"{fullpath} :{rows} rows")
    return rows

def smag(i) -> str:
    return f"{Quantity(i):.3}"

parser = argparse.ArgumentParser()
parser.add_argument('paths', nargs='+')
parser.add_argument("-v", "--verbose", action="count", default=0)
parser.add_argument("-p", "--recreate-pickle",action="store_true")
parser.add_argument("-n", "--nbins", default=50)
parser.add_argument("-y", "--ylog",action="store_true")
parser.add_argument("-d", "--delta", default=10)

args = parser.parse_args()

numeric_level = log.WARNING - args.verbose * 10
log.basicConfig(level=numeric_level,format='%(levelname)s:%(message)s')


usages: dict[str, list[int]] = {}
files = 0
rows = 0
# to be un/pickled: [files, rows, usages]

t0 = dt.now()
picklefilepath = "".join(args.paths)+".pickle"
pickle_contents = []
if os.path.isfile(picklefilepath) and not args.recreate_pickle:
    with open(picklefilepath, 'rb') as pf:
        [files, rows, usages] = pickle.load(pf)
    print(f"Loaded pickle: {files} files, {rows} rows in {(dt.now()-t0)/td(seconds=1)}")
else:

    for p in args.paths:
        log.debug(f"root {p}")
        if os.path.isfile(p):
            rows_read = readCSV(p)
            if rows_read == 0:
                print(f"no rows in {p}")
                exit(1)
            files +=1
            rows += rows_read
            continue
        files_before_root = files
        for dirpath, dirnames, dirfiles in os.walk(p):
            files_before = files
            for f in dirfiles:
                if not ".csv" in f:
                    continue
                files +=1
                fullpath = os.path.join(dirpath, f)
                log.debug(f"file {files}: {fullpath}")
                rows_before = rows
                rows_read = readCSV(fullpath)
                if rows_read == 0:
                    print(f"no files found in {p}")
                    exit(1)
                rows += rows_read

        if files_before_root == files:
            print(f"no files found in {p}")
            exit(1)


    print(f"Processed {files} files, {rows} rows in {(dt.now()-t0)/td(seconds=1)}")
    #print(usages)

    with open(picklefilepath, "wb") as pf:
        pickle.dump([files, rows, usages], pf)




dns = list(usages.keys())
m = [l for l in usages.values()]

# fig, ax = plt.subplots()
# #hist, bins, patches = ax.hist(usages, bins=10, edgecolor='black')
# hist, bins, bar_container = ax.hist(m, bins=20, label=dns)

# # counts, bins = np.histogram(m, bins=10)

# # print(counts)
# # print(bins)
# # for c in counts:
# #     plt.bar(bins[:-1], c)


# #ax.legend()#shadow=True, fancybox=True)
# #ax.set_yscale('log')




# plt.xlabel('RC')
# plt.ylabel('occurrences')
# plt.title('ResCount Distribution')
# formatter0 = EngFormatter()
# ax.xaxis.set_major_formatter(formatter0)
# ax.yaxis.set_major_formatter(formatter0)
# plt.grid(True)
# plt.show()






#fig: Figure = px.histogram(usages, barmode="group",marginal="rug", nbins=50)

maxRC = np.max(m) + 1
bins = np.linspace(0,maxRC, num=args.nbins)
bin_size = maxRC / args.nbins
#counts, bins2 = np.histogram(m,bins=bins)
#bins = 0.5 * (bins[:-1] + bins[1:])

# import plotly.express as px
# fig = px.bar(x=bins[:-1], y=counts, barmode="group")#,labels={'x':'RC', 'y':'occurrences'},)



traces = []
labels = []
for k,v in usages.items():
    minRC = min(v)
    maxRC = max(v)
    delta = (maxRC-minRC)/maxRC # difference between max and min
    print(f"{k}: \t{len(v)} points \t{smag(minRC)} - {smag(maxRC)} \tdiff={delta:.2%}", end="")
    if delta < args.delta/100:
        print("")
        continue

    print("\t PLOTTED")
    traces.append(v)
    labels.append(k)

#DEPRECATED
#import plotly.figure_factory as ff
#fig = ff.create_distplot(traces, labels, bin_size=bin_size,show_curve=False)

# impossibly slow
import plotly.express as px
fig = px.histogram(usages, x=labels, barmode="group", nbins = args.nbins, marginal="rug")#,labels=labels,)

title = f'{args.nbins} bins, {len(traces)}/{len(usages)} categories'
print(title)

# fig.update_traces({"visible":"legendonly"})
fig.update_layout(
    title_text=title, # title of plot
    xaxis_title_text='Resource Count', # xaxis label
    yaxis_title_text='Occurrences', # yaxis label
    bargap=0.2, # gap between bars of adjacent location coordinates
    bargroupgap=0, # gap between bars of the same location coordinates,

)

if args.ylog:
    fig.update_yaxes(type="log")

# to set x-axes ticks to limits of bins
#fig.update_xaxes(tickvals=np.arange(range_dict.start, range_dict.end+range_dict.size, range_dict.size))

print(fig.to_dict())

# ADD 2 BUTTONS TO TOGGLE LOG/LINEAR Y, but only in the yaxis 1
# fig.update_layout(
#     updatemenus=[
#         dict(
#             type="buttons",
#             direction="right",
#             active=0,
#             x=0.57,
#             y=1.2,
#             buttons=list([
#                 dict(label="Linear",
#                      method="update",
#                      args=[{"visible": [True, False, True, False]},
#                            {"title": "Yahoo",
#                             "annotations": []}]),
#                 dict(label="High",
#                      method="update",
#                      args=[{"visible": [True, True, False, False]},
#                            {"title": "Yahoo High",
#                             "annotations": high_annotations}]),
#                 dict(label="Low",
#                      method="update",
#                      args=[{"visible": [False, False, True, True]},
#                            {"title": "Yahoo Low",
#                             "annotations": low_annotations}]),
#                 dict(label="Both",
#                      method="update",
#                      args=[{"visible": [True, True, True, True]},
#                            {"title": "Yahoo",
#                             "annotations": high_annotations + low_annotations}]),
#             ]),
#         )
#     ])



fig.show()
