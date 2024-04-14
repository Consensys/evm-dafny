#! python3

import argparse
parser = argparse.ArgumentParser()
parser.add_argument('paths', nargs='+')
parser.add_argument("-v", "--verbose", action="count", default=0)
parser.add_argument("-p", "--recreate-pickle",action="store_true")
parser.add_argument("-n", "--nbins", default=50)
#parser.add_argument("-y", "--ylog",action="store_true")
parser.add_argument("-d", "--delta", type=int, default=10)
parser.add_argument("-i", "--ignore", action='append', default=[])
parser.add_argument("-t", "--top", default=5)

args = parser.parse_args()


#######################################################################################################################
# A tick formatter for Bokeh plots, so that is uses SI suffixes for big numbers

TS_CODE = """
// Bureau International des Poids et Mesures
// The International System of Units (SI)
// 9th edition 2019
//
// Table 7. SI prefixes
// _____________________________________________________
// Factor   Name    Symbol      Factor  Name    Symbol
// 10^1     deca    da          10^-1   deci    d
// 10^2     hecto   h           10^-2   centi   c
// 10^3     kilo    k           10^-3   milli   m
// 10^6     mega    M           10^-6   micro   μ
// 10^9     giga    G           10^-9   nano    n
// 10^12    tera    T           10^-12  pico    p
// 10^15    peta    P           10^-15  femto   f
// 10^18    exa     E           10^-18  atto    a
// 10^21    zetta   Z           10^-21  zepto   z
// 10^24    yotta   Y           10^-24  yocto   y
// _____________________________________________________
// ref.: https://www.bipm.org/documents/20126/41483022/SI-Brochure-9-EN.pdf/2d2b50bf-f2b4-9661-f402-5f9d66e4b507?version=1.10&t=1632138671693&download=true
//
// Currently deca, hecto, deci, centi are not used.
// Implemented to be a suffix to the axis ticks.

import {TickFormatter} from "models/formatters/tick_formatter"
import * as p from "core/properties"

let factorMapping: any = {
    '1': 'da', '2': 'h', '3': 'k', '6': 'M', '9': 'G',
    '12': 'T', '15': 'P', '18': 'E', '21': 'Z', '24': 'Y',
    '-1': 'd', '-2': 'c', '-3': 'm', '-6': 'μ', '-9': 'n',
    '-12': 'p', '-15': 'f', '-18': 'a', '-21': 'z', '-24': 'y'
};

export namespace SIFormatter {
  export type Attrs = p.AttrsOf<Props>

  export type Props = TickFormatter.Props & {
    precision: p.Property<number | "auto">,
    suffix: p.Property<string>
  }
}

export interface SIFormatter extends SIFormatter.Attrs {}

export class SIFormatter extends TickFormatter {
  // TickFormatters should implement this method, which accepts a list
  // of numbers (ticks) and returns a list of strings where numbers
  // converted to appropiate SI symbol
  properties: SIFormatter.Props

  constructor(attrs?: Partial<SIFormatter.Attrs>) {
    super(attrs)
  }

  static {
    this.define<SIFormatter.Props>(({Or, Int, Auto, String}) => ({
      precision: [ Or(Int, Auto), 'auto' ],
      suffix: [ String, '' ]
    }))
  }

  doFormat(ticks: number[], _opts: {loc: number}): string[] {
    var factorStr = '';
    const highThreshold = 10000;
    const lowThreshold = 0.1;
    const maxVal = Math.max(...ticks);
    const formatted = [];

    var base = Math.floor(Math.log10(Math.abs(maxVal)));
    var base = Math.floor(base / 3);
    var factor = base * 3;

    for (let i = 0, len = ticks.length; i < len; i++) {
        if (base === 0) {
            var newTickVal = ticks[i];
        } else if ((maxVal < highThreshold) && (maxVal > lowThreshold)) {
            var newTickVal = ticks[i];
        } else {
            var newTickVal = ((ticks[i]) / Math.pow(10, factor));

            // Sometimes I experience ticks with trailing numbers eg. 0.006000000001
            // This is an attempt to check for this and remove eg. 0.000000000001
            // Not sure if a JS function exist for this?
            // Or should it be handled in TickFormatter?

            const remain = newTickVal % (Math.trunc(newTickVal));
            if (remain < 1e-8) {
                newTickVal -= remain;
            }

            factorStr = ' ' + factorMapping[factor];
        }
        if (this.precision != 'auto') {
            var newTickStr = newTickVal.toFixed(this.precision);
        } else {
            var newTickStr = newTickVal.toString();
        }
        if ((factorStr == '') && (this.suffix != '')) {
            factorStr = ' ';
        }
        formatted.push(newTickStr + factorStr + this.suffix);
    }
    return formatted;
  }
}
"""

from curses.ascii import SI
from bokeh.models import TickFormatter, NumeralTickFormatter
from bokeh.util.compiler import TypeScript
from bokeh.core.properties import Auto, Either, Int, String

class SIFormatter(TickFormatter):

    __implementation__ = TypeScript(TS_CODE)

    precision = Either(Auto, Int, help="""
    How many digits of precision to display in tick labels.
    """)

    suffix = String(default="", help="""
    Any suffix to add to ticks labels eg. Hz.
    """)


#######################################################################################################################

import json
import logging as log
from math import inf
import os
import pickle
from time import sleep
import numpy as np
import re
from datetime import datetime as dt, timedelta as td

from quantiphy import Quantity


def cleanDisplayName(dn:str) -> str:
    new = dn.replace("(well-formedness)","") # WF is almost everywhere, so omit it; better just mention anything non-WF
    new = new.replace("(correctness)","[C]")
    new = re.sub(r"\(assertion batch (\d+)\)",r"AB\1", new)
    return new.strip()

class Details:
    def __init__(self):
        self.RC: list[int]= []
    RC: list[int]
    RC_max: int
    RC_min: int
    line: int = None
    col: int = None
    description: str = None
    randomSeed: int = None
    RC_delta: int



def readJSON(fullpath) -> int:  #reads 1 file, returns number of entries created
    # We want entries like: Precompiled.CallModExp WF ABx : [usages],Line,Row,Message
    entries = 0
    global results
    with open(fullpath) as jsonfile:
        verificationResults = json.load(jsonfile)["verificationResults"]
    
    # A JSON verification log contains a list of verificationResults
    # Each of vR corresponds to a function or method
    # and contains its Display Name, overall Resource Count, verification outcome and the Assertion Batches (vcResults)
    # If "isolating assertions" was NOT used, then the AB list will contain only 1 batch
    #   Each AB contains its number (vcNum), outcome, Resource Count, and a list of assertions
    #   if "isolating assertions" was NOT used, then the list will contain multiple assertions: 1 vcResult = multiple assertions
    #       Each assertion contains its location and description of the result
    #
    # Recap: if "isolating assertions" was NOT used, then the AB number is always 1, so no need to add it to our DN
    # and its entry only contains the list of RCs, not anything deeper
    # But if "isolating assertions" was used, then each DN contains an "AB x"; and each DN+AB's entry contains not only list of RCs,
    # but usages and location

    mode_IA = None  # Isolate Assertions. Guess the mode to check if it stays coherent.
    for vr in verificationResults:
        display_name = cleanDisplayName(vr["name"])
        assert vr["outcome"] == "Correct", f"{vr["name"]} has outcome {vr["outcome"]}" # didn't see it before, not implemented

        dn_RC = vr["resourceCount"] # should equal the sum of the RC of all the ABs

        # vcResults is the list of Assertion Batches (AKA Verification Conditions)
        # And without "isolating assertions", there is only 1 vcr per vr
        # Curiously, with IA, there is always (?) an extra empty assertion in each AB, so with IA the minimum is 2 assertions per AB

        if mode_IA == None:
            mode_IA = (len(vr['vcResults']) > 1)

        assert mode_IA == (len(vr['vcResults']) != 1), f"It looked like 'isolating-assertions'=={mode_IA}, and yet there's {len(vr['vcResults'])} ABs for {display_name}"

        for vcr in vr['vcResults']:
            assert vcr['outcome'] == "Valid", f"{vr["name"]} has vcResult.outcome == {vr["outcome"]}, stopping"

            display_name_AB: str = display_name + (f" AB{vcr["vcNum"]}" if mode_IA else "")
                
            det: Details = results.get(display_name_AB, Details())

            if mode_IA:
                # There's multiple ABs, but each AB contains a single assertion
                if len(vcr['assertions']) == 0:
                    assert vcr['vcNum'] == 1 #only seems to happen in the first one
                    # Ensure that it's empty every time it appears
                    assert det.line == None
                    assert det.col == None
                    assert det.description == None
                else:
                    assert len(vcr['assertions']) == 1, f"{display_name_AB} contains {len(vcr['assertions'])} assertions, expected only 1 because we're in IA mode!"
                    a = vcr['assertions'][0]
                    if det.line != None:
                        # Just double-check that everything stays consistent
                        assert det.line == a['line']
                        assert det.col == a['col']
                        assert det.description == a['description']
                    else:
                        det.line = a['line']
                        det.col = a['col']
                        det.description = a['description']
            else:
                # A single AB with multiple assertions. We don't want that much detail for plotting.
                pass

            det.RC.append(vcr['resourceCount'])
            det.randomSeed = vcr['randomSeed']
            results[display_name_AB] = det
            entries += 1

    return entries

def smag(i) -> str:
    return f"{Quantity(i):.3}"


numeric_level = log.WARNING - args.verbose * 10
log.basicConfig(level=numeric_level,format='%(asctime)s-%(levelname)s:%(message)s',datefmt='%H:%M:%S')


results: dict[str, Details] = {}    # DisplayName (ABn) : details
files = 0
entries = 0
# to be un/pickled: [files, rows, usages]

t0 = dt.now()
picklefilepath = "".join(args.paths)+"v2.pickle"
pickle_contents = []
if os.path.isfile(picklefilepath) and not args.recreate_pickle:
    with open(picklefilepath, 'rb') as pf:
        [files, entries, results] = pickle.load(pf)
    print(f"Loaded pickle: {files} files, {entries} rows in {(dt.now()-t0)/td(seconds=1)}")
else:

    for p in args.paths:
        # os.walk doesn't accept files, only dirs; so we need to process single files separately
        log.debug(f"root {p}")
        if os.path.isfile(p):
            entries_read = readJSON(p)
            if entries_read == 0:
                print(f"no rows in {p}")
                exit(1)
            files +=1
            entries += entries_read
            continue
        files_before_root = files
        for dirpath, dirnames, dirfiles in os.walk(p):
            files_before = files
            for f in dirfiles:
                if not ".json" in f:
                    continue
                files +=1
                fullpath = os.path.join(dirpath, f)
                log.debug(f"file {files}: {fullpath}")
                #rows_before = entries
                entries_read = readJSON(fullpath)
                if entries_read == 0:
                    print(f"no files found in {p}")
                    exit(1)
                entries += entries_read

        if files_before_root == files:
            print(f"no files found in {p}")
            exit(1)


    print(f"Processed {files} files, {entries} rows in {(dt.now()-t0)/td(seconds=1)}")
    #print(results)

    with open(picklefilepath, "wb") as pf:
        pickle.dump([files, entries, results], pf)




# dns = list(results.keys())
# m = [l for l in results.values()]
# maxRC = np.max(m) + 1
# bins = np.linspace(0,maxRC, num=args.nbins)
# bin_size = maxRC / args.nbins
# counts, bins2 = np.histogram(m,bins=bins)
# #bins = 0.5 * (bins[:-1] + bins[1:])

log.debug("Selecting traces")
# Decide which displaynames look interesting
#traces_selected = []
#labels_selected = []
maxRC = -inf
minRC = inf

for k,v in results.items():
    if k in args.ignore:
        continue
    minRC_entry = min(v.RC)
    minRC = min(minRC, minRC_entry)
    maxRC_entry = max(v.RC)
    maxRC = max(maxRC, maxRC_entry)
    delta = (maxRC_entry-minRC_entry)/maxRC_entry # difference between max and min, relative to max
    line = f"{k:40} {len(v.RC):>10} {smag(minRC_entry):>8}    {smag(maxRC_entry):>6} {delta:>8.2%}"
    log.debug(line)
    if delta < args.delta/100:
        continue
    results[k].RC_max = maxRC_entry
    results[k].RC_min = minRC_entry
    results[k].RC_delta = delta

    #print(f"{line}")
    #traces_selected.append(v)
    #labels_selected.append(k)

#sort the dictionary of results by the delta; high delta == high interest
results = {k:v for k,v in sorted(results.items(), reverse=True, key=lambda item: getattr(item[1],'RC_delta',0))}

# add the sorted index to the beginning of each DN
# results2 = {f'{i} {k}':v for i,k,v in zip(range(len(results.items())),results.keys(), results.values())}
# results = results2
results2 = {}
keys = list(results.keys())
for i in range(len(keys)):
    new_key = f'{i+1} {keys[i]}'
    results2[new_key] = results[keys[i]]
results = results2

# We have the interesting DNs, but when plotting all histograms together, the bin distribution might cause some DNs to fall into a single bin
# So let's remove those from the plots
print(f"{'Display Name':40} {'Datapoints':>10} {'minRC':>8}    {'maxRC':>6} {'diff':>8}")
print(f"{'============':40} {'==========':>10} {'=====':>8}    {'=====':>6} {'====':>8}")
bins = np.linspace(minRC,maxRC, num=args.nbins+1)
bh = 0.5 * (bins[:-1] + bins[1:])
hist_dict = {}
# the results dict is sorted by delta; to keep that order we need to traverse the dict, not the list of labs_selected
for dn in results.keys():
    d = results[dn]
    delta = getattr(d,'RC_delta',0)
    if delta < args.delta/100:
        break #because it's sorted
    counts, _ = np.histogram(d.RC,bins=bins)
    line = f"{dn:40} {len(d.RC):>10} {smag(d.RC_min):>8}    {smag(d.RC_max):>6} {d.RC_delta:>8.2%}"
    # remove plots that would fall into less than 3 bins
    nonempty = []
    for i in range(len(counts)):
        if counts[i] != 0:
            nonempty += [i]
    if nonempty[-1]-nonempty[0] < 3:
        print(line)
        continue
    print(f"{line}\tPLOTTED")
    hist_dict[dn] = counts
print("Plotting those not in a single bin...")

#######################################################################################################################

# MATPLOTLIB
# good for static plots

# see "bars with legend" in https://matplotlib.org/stable/gallery/statistics/histogram_multihist.html#sphx-glr-gallery-statistics-histogram-multihist-py
# density = True looks good

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

#######################################################################################################################

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

#######################################################################################################################

# # PLOTLY EXPRESS
# worked using the "express" functionality, but the moment I wanted to improve something it turned very complicated

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


#######################################################################################################################

# HOLOVIEWS

log.debug("Imports")
import numpy as np
import pandas as pd
import holoviews as hv
import hvplot
from hvplot import hvPlot
import hvplot.pandas
from holoviews import opts
from holoviews.plotting.links import DataLink

log.debug("hvplot extension")
hvplot.extension('bokeh')
log.debug("hvplot renderer")
renderer = hv.renderer('bokeh')


log.debug("creating dataframe")
d = {k:v for k,v in zip(results.keys(), map(lambda v: v.RC, results.values()))}

# df = pd.DataFrame(d)
# df = df.reset_index() # adds an index column, makes life easier with plotting libs

log.debug("hvplot")
histplots_dict = {
    l: hv.Histogram((bins, hist_dict[l])).redim(x="RC").opts(autorange='y',ylim=(0,None), xlim=(bins[0],bins[-1]),padding=(0, (0, 0.1)))
        for l in hist_dict.keys()
    }
hists = hv.NdOverlay(histplots_dict)#, kdims='Elements')
hists.opts(
    opts.Histogram(alpha=0.9, responsive=True, height=500,  tools=['hover'],autorange='y',show_legend=True)
    #,logy=True # histograms with logY have been broken in bokeh for years: https://github.com/holoviz/holoviews/issues/2591
    )

nlabs = len(hist_dict)
spikes_dict = {}
for i in range(len(hist_dict.keys())):
    dn = list(hist_dict.keys())[i]
    x= results[dn].RC
    y = [dn]*len(x)
    spikes_dict[dn] = hv.Spikes((x,y),kdims="RC").opts(position=i,tools=['hover'])
spikes = hv.NdOverlay(spikes_dict).opts(yticks=[((i+1)-0.5, list(spikes_dict.keys())[i]) for i in range(nlabs)])
spikes.opts(
    opts.Spikes(spike_length=1,line_alpha=0.4,responsive=True, height=50+nlabs*20,color=hv.Cycle(),ylim=(0,nlabs),autorange=None,tools=['hover'],yaxis='right'),
    opts.NdOverlay(show_legend=False,click_policy='mute',autorange=None,ylim=(0,nlabs),tools=['hover']),
    #opts.NdOverlay(shared_axes=True, shared_datasource=True,show_legend=False)
    )

#dlink = DataLink(spikes,hists)

plot = hists + spikes #+ hist #+ violin
plot.cols(1)
plot.opts(
#     #opts.Violin(tools=['box_select','lasso_select']),
#     #opts.Histogram(responsive=True, height=500, width=1000),
    # opts.Layout(sizing_mode="scale_both", shared_axes=True, sync_legends=True, shared_datasource=True)
    opts.NdOverlay(click_policy='mute',autorange='y',xformatter=SIFormatter(),legend_position="right")
)
#plot.opts(shared_axes=True)

#renderer.save(plot, 'plot')
hv.save(plot, 'plot.html')
#hvplot.show(plot)
os.system("open plot.html")

#webbrowser.open('plot.html')

# ls = hv.link_selections.instance()
# lplot = ls(plot)
# hv.save(lplot, 'lplot.html')
# os.system("open lplot.html")



