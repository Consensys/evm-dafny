#! python3

import argparse
from matplotlib import table
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

parser = argparse.ArgumentParser()
parser.add_argument('paths', nargs='+')
parser.add_argument("-v", "--verbose", action="count", default=0)
parser.add_argument("-p", "--recreate-pickle",action="store_true")
parser.add_argument("-n", "--nbins", default=50)
#parser.add_argument("-y", "--ylog",action="store_true")
parser.add_argument("-d", "--delta", type=int, default=10, help="The delta maxRC-minRC (as a % of max) over which a plot is considered interesting")
parser.add_argument("-i", "--ignore", action='append', default=[], help="DisplayNames with these substrings will be ignored")
parser.add_argument("-t", "--top", type=int, default=5, help="Plot only the top N most interesting")
parser.add_argument("-l", "--limitRC", type=Quantity, default=None, help="The RC limit used during verification. Used only for sanity checking")

args = parser.parse_args()

numeric_level = log.WARNING - args.verbose * 10
log.basicConfig(level=numeric_level,format='%(asctime)s-%(levelname)s:%(message)s',datefmt='%H:%M:%S')

results = readLogs(args.paths, args.recreate_pickle)

# PROCESS THE DATA

# Calculate the max-min delta for each DisplayName, and the global maxRC, minRC, minFail
maxRC = -inf
minRC = inf
minFail = inf # min RC of the failed entries
df = pd.DataFrame( columns=["minRC", "maxRC", "delta", "success", "fails"])
df.index.name="Element"

for k,v in results.items():
    for ig in args.ignore:
        if ig in k:
            continue
    minRC_entry = min(v.RC)
    minRC = min(minRC, minRC_entry)
    maxRC_entry = max(v.RC)
    maxRC = max(maxRC, maxRC_entry)
    if v.fails != []:
        minFail = min(minFail,min(v.fails))
    if args.limitRC != None:
            # if there was a limit, any resource count over the limit should be in the fails, not in the RCs
            assert maxRC_entry < args.limitRC, f"{args.limitRC=} but {k}:{maxRC_entry=}"
            #assert v.fails == [] or min(v.fails) > args.limitRC,
            if v.fails != [] and min(v.fails) < args.limitRC:
                log.warning(f"{args.limitRC=} but min failed for {k} is smaller {min(v.fails)=}")
    # Calculate the % difference between max and min
    delta = (maxRC_entry-minRC_entry)/maxRC_entry 
    line = f"{k:40} {len(v.RC):>10} {smag(minRC_entry):>8}    {smag(maxRC_entry):>6} {delta:>8.2%}"
    log.debug(line)

    df.loc[k] = {
        "success": len(v.RC),
        "minRC": smag(minRC_entry),
        "maxRC": smag(maxRC_entry),
        "delta": f"{delta:>8.2%}",
        "fails": len(v.fails),
    }

minFail = Quantity(minFail)
assert maxRC < minFail


#sort the dictionary of results by the delta; high delta == high interest
# results = {k:v for k,v in sorted(results.items(), reverse=True, key=lambda item: getattr(item[1],'RC_delta'))}
# but failed results are even more interesting
# results = {k:v for k,v in sorted(results.items(), reverse=True, key=lambda item: getattr(item[1],'fails'))}
df.sort_values(["fails","delta"],inplace=True, ascending=False,kind='stable')
df.reset_index(inplace=True)
df['Element_ordered'] = [f"{i} {s}" for i,s in zip(df.index,df["Element"])]

if args.limitRC==None:
    if minFail < inf:
        log.warning(f"There are 'failed' results, but no limitRC was given. It had to be smaller than the {minFail=}")
        fstr: str = f" > {minFail}"
    else:
        fstr = ""
else:
    fstr: str = f" > {args.limitRC}"

failstr: str = "FAILED" + fstr

# Plot the results

# When plotting all histograms together, the result distribution might cause some DNs
# to fall close together; the plot is not helpful then.
# So let's remove such histograms.
# For that, we need to calculate all the histograms.
# And for that, we need to decide their bins.
# So get the min([minRCs]) and max([maxRCs]) of the top candidates.
minRC_plot = min(df.loc[df.index[0:args.top], "minRC"])
maxRC_plot =  max(df.loc[df.index[0:args.top], "maxRC"])

# The histograms have the user-given num of bins, +2 (spacer and fails)
bins = np.linspace(Quantity(minRC_plot),Quantity(maxRC_plot), num=args.nbins+1)
bin_width = bins[1]-bins[0]
log.info(f"{args.nbins=}, range {smag(minRC_plot)} - {smag(maxRC_plot)}, width {smag(bin_width)}")
bin_margin = bins[-1] + 3 * bin_width
bin_fails = bin_margin + 3 * bin_width
bins_with_fails = np.append(bins,[bin_margin,bin_fails])

labels_plotted = []
bin_centers = 0.5 * (bins_with_fails[:-1] + bins_with_fails[1:])
hist_df = pd.DataFrame(index = bin_centers)
#hist_df["bins"] = bin_centers
#hist_df = hist_df.reindex()
for i in df.index[:args.top]:
    dn = df.loc[i,"Element"]
    d = results[dn]
    nfails = df[df["Element"]==dn]["fails"].values[0]#.query(f'Element="{dn}"')
    counts, _ = np.histogram(d.RC,bins=bins)
    counts = np.append(counts,[0,nfails])

    # remove plots without fails that would span less than 3 bins
    nonempty_bins = []
    for i,c in enumerate(counts):
        if c != 0:
            nonempty_bins.append(i)
    plotted: bool = ((nfails > 0) or
                        (nonempty_bins[-1]-nonempty_bins[0] > 3)
                    )
    if plotted:
        labels_plotted.append(dn)
        hist_df[dn] = counts
        with np.errstate(divide='ignore'): # to silence the errors because of log of 0 values
            hist_df[dn+"_log"] = np.log10(counts)
        hist_df[dn+"_RCFail"] = [smag(b) for b in bin_centers[0:-2]] + ["",failstr ]

#dfs=df.style.format({'maxRC': lambda x: 1, 'minRC':smag})
print(df.drop(columns="Element_ordered"))


# HOLOVIEWS

import holoviews as hv
import hvplot
from hvplot import hvPlot
from holoviews import opts
from bokeh.models.tickers import FixedTicker, CompositeTicker, BasicTicker
from bokeh.models import NumeralTickFormatter
from bokeh.util.compiler import TypeScript

hv.extension('bokeh')
renderer = hv.renderer('bokeh')

histplots_dict = {}
jitter = (bin_width)/len(labels_plotted)/3
for i,dn in enumerate(labels_plotted):
    eo = df[df["Element"]==dn]["Element_ordered"].values[0]
    h = hv.Histogram(
            (bins_with_fails+i*jitter,
                hist_df[dn+"_log"],
                hist_df[dn],
                hist_df[dn+"_RCFail"]
                ),
            kdims=["RC"],
            vdims=["LogQuantity", "Quantity", "RCFail"]
        )
    histplots_dict[eo] = h

from bokeh.models import HoverTool
hover = HoverTool(tooltips=[
    ("Element", "@Element"),
    ("ResCount bin", "@RCFail"),
    ("Quantity", "@Quantity"),
    ("Log(Quantity)", "@LogQuantity"),
    ])

fticker = FixedTicker(ticks=bin_centers, num_minor_ticks=0)
bticker = BasicTicker(min_interval = bin_width, num_minor_ticks=0)
cticker = CompositeTicker(tickers=[fticker, bticker])

hists = hv.NdOverlay(histplots_dict)#, kdims='Elements')
hists.opts(
    opts.Histogram(alpha=0.9,
                    responsive=True,
                    height=500,
                    tools=[hover],
                    show_legend=True,
                    muted=True,
                    backend_opts={
                       "xaxis.bounds" : (0,bin_fails+bin_width),
                       "xaxis.ticker" : cticker
                        },
                    autorange='y',
                    ylim=(0,None),
                    xlim=(0,bins_with_fails[-1]+bin_width),
                    xlabel="RC bins",
                    padding=((0.1,0.1), (0, 0.1)),
        )
    #,logy=True # histograms with logY have been broken in bokeh for years: https://github.com/holoviz/holoviews/issues/2591
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
    #RCFail = RCs # so that it'll appear in the hover tool
    if results[dn].fails != []:
        RC.append(bin_centers[-1])
        #RCFail.append(0)
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
                    "xaxis.bounds" : (0,bin_fails+bin_width)
                    },
                ),
    opts.NdOverlay(show_legend=False,
                    click_policy='mute',
                    autorange=None,
                    ylim=(0,nlabs),
                    xlim=(0,bins_with_fails[-1]+bin_width),
                    padding=((0.1,0.1), (0, 0.1)),
                ),
    #opts.NdOverlay(shared_axes=True, shared_datasource=True,show_legend=False)
    )

table_plot = hv.Table(df.drop(columns="Element_ordered"))#,kdims="Element")

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
        )
)
plot.opts(shared_axes=True)

# fig = hv.render(plot)
# #hb = fig.traverse(specs=[hv.plotting.bokeh.Histogram])

# fig.xaxis.bounds = (0,bin_fails)

plotfilepath = "".join(args.paths)+".html"

try:
    os.remove(plotfilepath)
except:
    pass

#renderer.save(plot, 'plot')
hv.save(plot, plotfilepath)
#hvplot.show(plot)
# from bokeh.resources import INLINE
#plot.save(plotfilepath)#, resources=INLINE)

print(f"Created file {plotfilepath}")
os.system(f"open {plotfilepath}")

# Repeat the warning
if args.limitRC==None:
    if minFail < inf:
        log.warning(f"There are 'failed' results, but no limitRC was given. Min failed RC found = {smag(minFail)}")


#webbrowser.open('plot.html')

# ls = hv.link_selections.instance()
# lplot = ls(plot)
# hv.save(lplot, 'lplot.html')
# os.system("open lplot.html")



