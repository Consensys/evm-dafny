#! python3

import argparse
import math
import re
import sys
# from matplotlib import table
from quantiphy import Quantity
import logging as log
from math import inf
import os
import numpy as np
import pandas as pd
from log_readers import Details, readLogs
from quantiphy import Quantity

def smag(i) -> str:
    return f"{Quantity(i):.3}"

def dn_is_excluded(dn, exclude_list):
    for e in exclude_list:
        if e.lower() in dn.lower():
            return True
    return False

parser = argparse.ArgumentParser()
parser.add_argument('paths', nargs='+')
parser.add_argument("-v", "--verbose", action="count", default=0)
parser.add_argument("-p", "--recreate-pickle",action="store_true")
parser.add_argument("-n", "--nbins", default=50)
#parser.add_argument("-d", "--RCspan", type=int, default=10, help="The span maxRC-minRC (as a % of max) over which a plot is considered interesting")
parser.add_argument("-x", "--exclude", action='append', default=[], help="DisplayNames matched by this regex will be excluded from plot")
#parser.add_argument("-o", "--only", action='append', default=[], help="Only plot DisplayNames with these substrings")
parser.add_argument("-t", "--top", type=int, default=5, help="Plot only the top N most interesting")
parser.add_argument("-s", "--stop", default=False, action='store_true', help="Process the data but stop before plotting")
parser.add_argument("-a", "--IAmode", default=False, action='store_true', help="Isolated Assertions mode. Used only for sanity checking.")
parser.add_argument("-l", "--limitRC", type=Quantity, default=None, help="The RC limit used during verification. Used only for sanity checking.")
parser.add_argument("-b", "--bspan", type=int, default=0, help="The minimum bin span for a histogram to be plotted")

args = parser.parse_args()

numeric_level = log.WARNING - args.verbose * 10
log.basicConfig(level=numeric_level,format='%(asctime)s-%(levelname)s:%(message)s',datefmt='%H:%M:%S')

results = readLogs(args.paths, args.recreate_pickle)

# PROCESS THE DATA

# Calculate the max-min span for each DisplayName, and the global maxRC, minRC, minFail
maxRC = -inf
minRC = inf
minOoR = inf # min RC of the OoR entries
minFailures = inf # min RC of the failed entries
ABs_present = False
vr_past_limitRC = ""
df = pd.DataFrame( columns=["minRC", "maxRC", "span", "successes", "OoRs","failures","is_AB","loc","comment"])
df.index.name="Element"

for k,v in results.items():
    # for ig in args.exclude:
    #     if ig in k:
    #         log.debug(f"Excluding {k}")
    #         continue
    minRC_entry = min(v.RC, default=inf)
    minRC = min(minRC, minRC_entry)
    maxRC_entry = max(v.RC, default=-inf)
    maxRC = max(maxRC, maxRC_entry)
    minOoR_entry = min(v.OoR, default=inf)
    minOoR = min(minOoR,minOoR_entry)
    minFailures_entry = min(v.failures, default=inf)
    minFailures = min(minFailures,minFailures_entry)
    if v.is_AB:
        ABs_present = True
    comment = ""
    if args.limitRC is not None:
            # if there was a limit, any RC > limitRC should be in the fails, not in the RCs
            if maxRC_entry > args.limitRC:
                if v.is_AB or not args.IAmode:
                    sys.exit(f"LimitRC={args.limitRC} but {k}() has maxRC={Quantity(maxRC_entry)}. Should be a fail! ")
                else:
                    # IAmode could hide a genuinely failed VR. Ensure that IAmode is only used when there are ABs.
                    vr_past_limitRC += f"LimitRC={args.limitRC} but {k} has maxRC={Quantity(maxRC_entry)}. Should be a fail!\n"
            if minOoR_entry < args.limitRC and v.is_AB:
                log.warning(f"MinOoR for {k} is {min(v.OoR)}, should be > {args.limitRC=}")
                # comment = "FAILED "
    # Calculate the % span between max and min
    span = (maxRC_entry-minRC_entry)/minRC_entry
    info = f"{k:40} {len(v.RC):>10} {smag(minRC_entry):>8}    {smag(maxRC_entry):>6} {span:>8.2%}"
    log.debug(info)
    lincol = "" if v.line is None else f":{v.line}:{v.col}"
    df.loc[k] = {
        "successes": len(v.RC),
        "minRC" : minRC_entry,
        "maxRC" : maxRC_entry,
        "span" : span,
        "OoRs" : len(v.OoR),
        "failures" : len(v.failures),
        "is_AB" : v.is_AB,
        "loc"   : f"{v.filename}{lincol}",
        "comment": comment
    }

minFailures = Quantity(minFailures)
minOoR = Quantity(minOoR)
# assert maxRC < minFail
if args.IAmode and not ABs_present:
    # Not important
    log.debug("ABs expected but not present")
    # But this could hide a mistake
    assert vr_past_limitRC == "", vr_past_limitRC

df["weighted_span"] = df["span"] * df["minRC"]
df = df.sort_values(["failures","OoRs","weighted_span"], ascending=False,kind='stable')#.drop("weighted_span")

# IA plots contain both vrs and vcrs. Separate them.
df_ABs = df[df["is_AB"]]
if df_ABs.empty:
    df_vrs = None
    df = df
else:
    df_vrs = df[df["is_AB"] == False]
    df = df_ABs

df.reset_index(inplace=True)
df['Element_ordered'] = [f"{i} {s}" for i,s in zip(df.index,df["Element"])]

if args.limitRC is None:
    if minOoR < inf:
        log.warning(f"Logs contain OoR results, but no limitRC was given. Minimum OoR RC found = {minOoR}.")
        OoRstr: str = f"OoR > {minOoR}"
    else:
        OoRstr = ""
else:
    OoRstr: str = f"OoR > {args.limitRC}"

failstr: str = OoRstr #"FAILED"# + fstr

# PREPARATORY CALCULATIONS TO PLOT THE RESULTS

# When plotting all histograms together, the result distribution might cause some DNs
# to fall too close together; the plot is not helpful then.
# So let's remove such histograms.
# For that, first we need to calculate all the histograms.
# And for that, we need to decide their bins.
# So get the min([minRCs]) and max([maxRCs]) of the top candidates.
df["excluded"] = df["Element"].map(lambda dn: dn_is_excluded(dn, args.exclude)).astype(bool)

minRC_plot = min(df[~df["excluded"]].iloc[0:args.top]["minRC"])
maxRC_plot = max(df[~df["excluded"]].iloc[0:args.top]["maxRC"])

# The histograms have the user-given num of bins, + filler until x=0, + 2 if there are fails (spacer and fails)
bins = np.linspace(Quantity(minRC_plot),Quantity(maxRC_plot), num=args.nbins+1)
bin_width = bins[1]-bins[0]
log.debug(f"{args.nbins=}, range {smag(minRC_plot)} - {smag(maxRC_plot)}, width {smag(bin_width)}")
plotting_fails = (minOoR != inf) or (minFailures != inf)
bin_margin = bins[-1] + 3 * bin_width
bin_fails = bin_margin + 3 * bin_width
bins_with_fails = np.append(bins,[bin_margin,bin_fails])

labels_plotted = []
bins_plot = bins_with_fails if plotting_fails else bins
bin_centers = 0.5 * (bins_plot[:-1] + bins_plot[1:])
bin_labels = [smag(b) for b in bin_centers]
if plotting_fails:
    bin_labels = bin_labels[0:-2] + ["",failstr ]
hist_df = pd.DataFrame(index = bin_centers)
for i in df.index[:args.top]:
    if df.loc[i,"excluded"]:
        df.loc[i,"comment"] += "excluded"
        continue
    dn = df.loc[i,"Element"]
    d = results[dn]
    nfails = len(d.OoR)+len(d.failures)
    counts, _ = np.histogram(d.RC,bins=bins)
    if plotting_fails:
        counts = np.append(counts,[0,nfails])

    # remove plots without fails that would span less than 3 bins
    nonempty_bins = []
    for b,c in enumerate(counts):
        if c != 0:
            nonempty_bins.append(b)
    bin_span = nonempty_bins[-1]-nonempty_bins[0]

    if (nfails > 0) or (bin_span >= args.bspan):
        labels_plotted.append(dn)
        hist_df[dn] = counts
        with np.errstate(divide='ignore'): # to silence the errors because of log of 0 values
            hist_df[dn+"_log"] = np.log10(counts)
        hist_df[dn+"_log"] = hist_df[dn+"_log"].apply(
            lambda l: l if l!=0 else 0.2    # log10(1) = 0, so it's barely visible in plot. log10(2)=0.3. So let's plot 1 as 0.2
            ) 
        hist_df[dn+"_RCbin"] = bin_labels # for the hover tool
        df.loc[i,"comment"]+="plotted" #f"F={len(d.failures)} O={len(d.OoR)}"
    else:
        df.loc[i,"comment"]+=f"{bin_span=}"

print(df.drop(columns=["Element_ordered","is_AB","excluded"])
        .rename(columns={
            "span"          : "RC span (%)",
            "weighted_span" : "minRC * span"
            })
        .head(args.top)
        .to_string (formatters={
                'maxRC':smag , 
                'minRC':smag, 
                #'OoRs':smag,
                #'failures':smag,
                'span':lambda d:f"{d:>8.2%}"
                },
            #max_rows=8
            )
        )

if args.stop:
    log.info("Stopping as requested.")
    exit(0)

# HOLOVIEWS

import holoviews as hv
import hvplot
from hvplot import hvPlot
from holoviews import opts
from bokeh.models.tickers import FixedTicker, CompositeTicker, BasicTicker
from bokeh.models import NumeralTickFormatter, HoverTool
from bokeh.util.compiler import TypeScript

hv.extension('bokeh')
renderer = hv.renderer('bokeh')

histplots_dict = {}
jitter = (bin_width)/len(labels_plotted)/3
for i,dn in enumerate(labels_plotted):
    eo = df[df["Element"]==dn]["Element_ordered"].values[0]
    h = hv.Histogram(
            (bins_plot+i*jitter,
                hist_df[dn+"_log"],
                hist_df[dn],
                hist_df[dn+"_RCbin"]
                ),
            kdims=["RC"],
            vdims=["LogQuantity", "Quantity", "RCbin"]
        )
    histplots_dict[eo] = h

hover = HoverTool(tooltips=[
    ("Element", "@Element"),
    ("ResCount bin", "@RCbin"),
    ("Quantity", "@Quantity"),
    ("Log(Quantity)", "@LogQuantity"),
    ])

bticker = BasicTicker(min_interval = 10**math.floor(math.log10(bin_width)), num_minor_ticks=0)

hists = hv.NdOverlay(histplots_dict)#, kdims='Elements')
hists.opts(
    opts.Histogram(alpha=0.9,
                    responsive=True,
                    height=500,
                    tools=[hover],
                    show_legend=True,
                    muted=True,
                    backend_opts={
                       "xaxis.bounds" : (0,bins_plot[-1]+bin_width),
                       "xaxis.ticker" : bticker
                        },
                    autorange='y',
                    ylim=(0,None),
                    xlim=(0,bins_plot[-1]+bin_width),
                    xlabel="RC bins",
                    padding=((0.1,0.1), (0, 0.1)),
        ),
    #,logy=True # histograms with logY have been broken in bokeh for years: https://github.com/holoviz/holoviews/issues/2591
    opts.NdOverlay(show_legend=True,)
    )

# A vertical line separating the fails bar
# disabled because it disables the autoranging of the histograms
# vline = hv.VLine(bin_centers[-2]).opts(
#     opts.VLine(color='black', line_width=3, autorange='y',ylim=(0,None))
# )
# vspan = hv.VSpan(bin_centers[-2],bin_centers[-1]).opts(
#     opts.VSpan(color='red', autorange='y',ylim=(0,None),apply_ranges=False)
# )

# hists = hists * vspan


####### SPIKES

# A JavaScript function to customize the hovertool
from bokeh.models import CustomJSHover
RCFfunc = CustomJSHover(code='''
        var value;
        var modified;
        if (value > ''' + str(int(maxRC)) + ''') {
            modified = "''' + failstr + '''";
        } else {
            modified = value.toString();
        }
        return modified
''')

nlabs = len(labels_plotted)
spikes_dict = {}
for i,dn in enumerate(labels_plotted):
    eo = df[df["Element"]==dn]["Element_ordered"].values[0]
    RC = results[dn].RC
    # Represent the failures / OoRs with a spike in the last bin
    if results[dn].OoR != [] or results[dn].failures != []:
        RC.append(bin_centers[-1])
    hover2 = HoverTool(
                tooltips=[
                    ("Element", dn),
                    ("ResCount", "@RC{custom}"),
                    ],
                formatters={
                    "@RC" : RCFfunc,
                    "dn"  : 'numeral'
                }
            )
    spikes_dict[eo] = hv.Spikes(RC,kdims="RC").opts(position=nlabs-i-1,tools=[hover2],xaxis="bottom")

yticks = [(nlabs-i-0.5, list(spikes_dict.keys())[i]) for i in range(nlabs)]#-1,-1,-1)]
spikes = hv.NdOverlay(spikes_dict).opts(
    yticks = yticks
    )

spikes.opts(
    opts.Spikes(spike_length=1,
                line_alpha=1,
                responsive=True,
                height=50+nlabs*20,
                color=hv.Cycle(),
                ylim=(0,nlabs),
                autorange=None,
                yaxis='right',
                backend_opts={
                    "xaxis.bounds" : (0,bins_plot[-1]+bin_width)
                    },
                ),
    opts.NdOverlay(show_legend=False,
                    click_policy='mute',
                    autorange=None,
                    ylim=(0,nlabs),
                    xlim=(0,bins_plot[-1]+bin_width),
                    padding=((0.1,0.1), (0, 0.1)),
                ),
    #opts.NdOverlay(shared_axes=True, shared_datasource=True,show_legend=False)
    )

# TABLE/S

# df["minRC"] = df["minRC"].apply(smag)
# df["maxRC"] = df["maxRC"].apply(smag)
# df["span"] = df["span"].apply(lambda d:f"{d:>8.2%}")
df["span"] = df["span"].apply(lambda d:d*100)
table_plot = hv.Table(df.drop(columns=["Element_ordered","is_AB","excluded"])
                      .rename(
                          columns={
                            "span":"RC span (%)",
                            "weighted_span" : "minRC * span"
                            }),
                    kdims="Element"
                ).opts(height=310,width=800)

if df_vrs is not None:
    # df_vrs["minRC"] = df_vrs["minRC"].apply(smag)
    # df_vrs["maxRC"] = df_vrs["maxRC"].apply(smag)
    # df_vrs["span"] = df_vrs["span"].apply(lambda d:f"{d:>8.2%}")
    df_vrs["span"] = df_vrs["span"].apply(lambda d:d*100)
    table_vrs = hv.Table(df_vrs.drop(columns=["is_AB"]).rename(
                          columns={
                            "span":"RC span (%)",
                            "weighted_span" : "minRC * span"
                            }),
                    kdims="Element"
                ).opts(height=310,width=800)
    table_plot = ( table_plot + 
                  hv.Div("<h2>Per-function totals (in Isolated Assertions mode):</h2>").opts(height=50) + 
                  table_vrs)
    
plot = hists + spikes + table_plot #+ hist #+ violin
plot.cols(1)

class NumericalTickFormatterWithLimit(NumeralTickFormatter):
    __implementation__ = TypeScript("""
import {NumeralTickFormatter} from "models/formatters/numeral_tick_formatter"

export class NumericalTickFormatterWithLimit extends NumeralTickFormatter {
  FAIL_MIN=""" + str(int(bin_margin)) + """

  doFormat(ticks: number[], _opts: {loc: number}): string[] {
    const formatted = []
    const ticks2 = super.doFormat(ticks, _opts)
    for (let i = 0; i < ticks.length; i++) {
      if (ticks[i] < this.FAIL_MIN) {
        formatted.push(ticks2[i])
      } else {
        formatted.push('FAILED')
      }
    }
    return formatted
  }
}
""")

mf = NumericalTickFormatterWithLimit(format="0.0a")

plot.opts(
#     #opts.Histogram(responsive=True, height=500, width=1000),
    # opts.Layout(sizing_mode="scale_both", shared_axes=True, sync_legends=True, shared_datasource=True)
    opts.NdOverlay(
        click_policy='mute',
        autorange='y',
        xformatter=mf,
        legend_position="right",
        responsive=True
        )
)
plot.opts(shared_axes=True)

# fig = hv.render(plot)
# #hb = fig.traverse(specs=[hv.plotting.bokeh.Histogram])

# fig.xaxis.bounds = (0,bin_fails)

#title = "".join(args.paths)
plotfilepath = "".join(args.paths)+".html"

try:
    os.remove(plotfilepath)
except:
    pass

#renderer.save(plot, 'plot')
hv.save(plot, plotfilepath)#, title=title)
#hvplot.show(plot)
# from bokeh.resources import INLINE
#plot.save(plotfilepath)#, resources=INLINE)

print(f"Created file {plotfilepath}")
os.system(f"open {plotfilepath}")

# Repeat the warning
if args.limitRC is None:
    if minOoR < inf:
        log.warning(f"There are 'failed' results, but no limitRC was given. Min failed RC found = {smag(minOoR)}")


#webbrowser.open('plot.html')

# ls = hv.link_selections.instance()
# lplot = ls(plot)
# hv.save(lplot, 'lplot.html')
# os.system("open lplot.html")



