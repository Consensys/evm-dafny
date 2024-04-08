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
log.basicConfig(level=numeric_level,format='%(asctime)s-%(levelname)s:%(message)s',datefmt='%H:%M:%S')


usages: dict[str, list[int]] = {}   # DisplayName : list of RCs
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
maxRC = np.max(m) + 1
bins = np.linspace(0,maxRC, num=args.nbins)
bin_size = maxRC / args.nbins
counts, bins2 = np.histogram(m,bins=bins)
#bins = 0.5 * (bins[:-1] + bins[1:])

log.info("Selecting traces")
traces_selected = []
labels_selected = []
for k,v in usages.items():
    minRC = min(v)
    maxRC = max(v)
    delta = (maxRC-minRC)/maxRC # difference between max and min
    line = f"{k}: \t{len(v)} points \t{smag(minRC)} - {smag(maxRC)} \tdiff={delta:.2%}"
    log.debug(line)
    if delta < args.delta/100:
        continue

    print(f"{line}\t PLOTTED")
    traces_selected.append(v)
    labels_selected.append(k)


# MATPLOTLIB

# from matplotlib.container import BarContainer
# import matplotlib.pyplot as plt
# from matplotlib.ticker import EngFormatter
#from matplotlib.animation import adjusted_figsize

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


# PLOTLY FIGUREFACTORY

# #DEPRECATED
# import plotly.figure_factory as ff
# fig_ff = ff.create_distplot(traces, labels, bin_size=bin_size,show_curve=False)


# title = f'{args.nbins} bins, {len(traces)}/{len(usages)} categories'
# print(title)

# # fig.update_traces({"visible":"legendonly"})
# fig_ff.update_layout(
#     title_text=title, # title of plot
#     xaxis_title_text='Resource Count', # xaxis label
#     yaxis_title_text='Occurrences', # yaxis label
#     bargap=0.2, # gap between bars of adjacent location coordinates
#     bargroupgap=0, # gap between bars of the same location coordinates,

# )

# if args.ylog:
#     fig_ff.update_yaxes(type="log")

# fig_ff.write_html('ff.html', auto_open=False)
# #fig_ff.show()

# #del fig_ff



# # PLOTLY EXPRESS

# # impossibly slow
# import plotly.express as px
# fig_px = px.histogram(usages, x=labels, barmode="group", nbins = args.nbins, marginal="rug")#,labels=labels,)
# # fig = px.bar(x=bins[:-1], y=counts, barmode="group")#,labels={'x':'RC', 'y':'occurrences'},)

# fig_px.update_layout(
#     title_text=title, # title of plot
#     xaxis_title_text='Resource Count', # xaxis label
#     yaxis_title_text='Occurrences', # yaxis label
#     bargap=0.2, # gap between bars of adjacent location coordinates
#     bargroupgap=0, # gap between bars of the same location coordinates,
# )

# if args.ylog:
#     fig_px.update_yaxes(type="log")
# # to set x-axes ticks to limits of bins
# #fig.update_xaxes(tickvals=np.arange(range_dict.start, range_dict.end+range_dict.size, range_dict.size))

# fig_px.write_html('px.html', auto_open=False)
# #fig_px.show()
# #del fig_px




# HOLOVIEWS

log.info("Imports")
import numpy as np
import pandas as pd
import holoviews as hv
import hvplot
from hvplot import hvPlot
import hvplot.pandas
from holoviews import opts

log.info("hvplot extension")
hvplot.extension('bokeh')
log.info("hvplot renderer")
renderer = hv.renderer('bokeh')


log.info("creating dataframe")
dfu = pd.DataFrame(usages)
dfu = dfu.reset_index()

log.info("hvplot")
hist = dfu.hvplot(kind='hist',y=labels_selected, xlabel="Resource Count", ylabel="Occurrences", bins=25, responsive=True, height=500, logy=False, ylim=[0.5,1000])
#hist2 = dfu.hvplot.hist(y=labels_selected, xlabel="Resource Count", ylabel="Occurrences", bins=25)
violin = dfu.hvplot(kind='violin', y=labels_selected, invert=True, responsive=True, height=200)
violin.opts(opts.Violin(inner='stick'))

plot = violin + hist
plot.cols(1)
plot.opts(
    opts.Violin(tools=['box_select','lasso_select']),
    #opts.Histogram(responsive=True, height=500, width=1000),
    opts.Layout(sizing_mode="scale_both", shared_axes=True, sync_legends=True, shared_datasource=True)
)
ls = hv.link_selections.instance()
lplot = ls(plot)


#renderer.save(plot, 'plot')
hv.save(plot, 'plot.html')
#hvplot.show(plot)

#webbrowser.open('plot.html')
os.system("open plot.html")

#log.info("holoviews")
#plot2 = hv.Histogram(data=traces_selected)
#hvplot.show(plot2)
#renderer.save(plot2, 'plot2')

log.info("done")

