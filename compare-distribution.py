#! python3

import argparse
import math
import re
import sys
from matplotlib import table
from quantiphy import Quantity
import logging as log
from math import inf
import os
import numpy as np
import pandas as pd
from log_readers import Details, readLogs
from quantiphy import Quantity
from pathlib import Path

def smag(i) -> str:
    return f"{Quantity(i):.3}"

def dn_is_excluded(dn, exclude_list):
    for e in exclude_list:
        if e.lower() in dn.lower():
            return True
    return False

def row_from_Details(v: Details):
    minRC_entry = min(v.RC, default=inf)
#    minRC = min(minRC, minRC_entry)
    maxRC_entry = max(v.RC, default=-inf)
#    maxRC = max(maxRC, maxRC_entry)
    minOoR_entry = min(v.OoR, default=inf)
#    minOoR = min(minOoR,minOoR_entry)
    minFailures_entry = min(v.failures, default=inf)
#    minFailures = min(minFailures,minFailures_entry)

    #comment = ""

    # Calculate the % span between max and min
    span = (maxRC_entry-minRC_entry)/minRC_entry
    # info = f"{k:40} {len(v.RC):>10} {smag(minRC_entry):>8}    {smag(maxRC_entry):>6} {span:>8.2%}"
    # log.debug(info)
    return {
        "successes": len(v.RC),
        "minRC" : minRC_entry,
        "maxRC" : maxRC_entry,
        "span" : span,
        "OoRs" : len(v.OoR),
        "failures" : len(v.failures),
        "is_AB" : v.is_AB,
        #"comment": comment
    }




parser = argparse.ArgumentParser()
parser.add_argument('path_normal')#, nargs='+')
parser.add_argument('-i','--path_IA')#, nargs='+')
parser.add_argument("-v", "--verbose", action="count", default=0)
#parser.add_argument("-p", "--recreate-pickle", default=, action="store_true")
# parser.add_argument("-n", "--nbins", default=50)
# #parser.add_argument("-d", "--RCspan", type=int, default=10, help="The span maxRC-minRC (as a % of max) over which a plot is considered interesting")
# parser.add_argument("-x", "--exclude", action='append', default=[], help="DisplayNames matched by this regex will be excluded from plot")
# #parser.add_argument("-o", "--only", action='append', default=[], help="Only plot DisplayNames with these substrings")
# parser.add_argument("-t", "--top", type=int, default=5, help="Plot only the top N most interesting")
# parser.add_argument("-s", "--stop", default=False, action='store_true', help="Process the data but stop before plotting")
# parser.add_argument("-a", "--IAmode", default=False, action='store_true', help="Isolated Assertions mode. Used only for sanity checking.")
parser.add_argument("-l", "--limitRC", type=Quantity, default=None, help="The RC limit used during verification. Used only for sanity checking.")
# parser.add_argument("-b", "--bspan", type=int, default=0, help="The minimum bin span for a histogram to be plotted")

args = parser.parse_args()

numeric_level = log.WARNING - args.verbose * 10
log.basicConfig(level=numeric_level,format='%(asctime)s-%(levelname)s:%(message)s',datefmt='%H:%M:%S')

product = Path(args.path_normal).name + "-" + Path(args.path_IA).name

results_normal = readLogs([args.path_normal])#, args.recreate_pickle)
results_IA = readLogs([args.path_IA])#, args.recreate_pickle)

# PROCESS THE DATA

ABs_present = False
vr_past_limitRC = ""
df_IA = pd.DataFrame( columns=["minRC", "maxRC", "span", "successes", "OoRs","failures","is_AB"])
df_IA.index.name="Element"

for k,v in results_IA.items():
    if v.is_AB:
        # we want to make sure that these are results from an IA run
        ABs_present = True
        # but we only care for the function-level results
        continue
    df_IA.loc[k] = row_from_Details(v)

assert ABs_present

df_IA.drop(columns=["is_AB"],inplace=True)
df_IA["minRC * span"] = df_IA["span"] * df_IA["minRC"]
# df_IA = df_IA.sort_values(["failures","OoRs","minRC * span"], ascending=False,kind='stable')
# df_IA.reset_index(inplace=True)
# df_IA['Element_ordered'] = [f"{i} {s}" for i,s in zip(df_IA.index,df_IA["Element"])]
cs = [e for e in df_IA.columns.values if e != "Element"]
cs_IA = [c + " IA" for c in cs]
renamer = {c:c_IA for c, c_IA in zip(cs, cs_IA)}
renamer["span IA"]="RC span% IA"
df_IA.rename(columns=renamer, inplace=True)

df = pd.DataFrame( columns=["minRC", "maxRC", "span", "successes", "OoRs","failures","is_AB"])
df.index.name="Element"
for k,v in results_normal.items():
    assert not v.is_AB
    if k not in df_IA.index.values:
        #we only want the same funcs that were contained in the IA file 
        continue
    df.loc[k] = row_from_Details(v)
df.drop(columns=["is_AB"], inplace=True)
df["minRC * span"] = df["span"] * df["minRC"]
df = df.sort_values(["failures","OoRs","minRC * span"], ascending=False,kind='stable')
dfc =pd.concat([df, df_IA], axis=1)

df = dfc
df.reset_index(inplace=True)
df['Element_ordered'] = [f"{i} {s}" for i,s in zip(df.index,df["Element"])]


maxRC = max(max(df["maxRC"]),max(df["maxRC IA"]))
minRC = min(min(df["minRC"]),min(df["minRC IA"]))
RCfailure = maxRC * 2 # for logx we need a big difference
# minOoR = min(min(df["minRC"]),min(df_IA["minRC"]))
# minFailures = min(min(df["minRC"]),min(df_IA["minRC"]))

# minFailures = Quantity(minFailures)
# minOoR = Quantity(minOoR)
# assert maxRC < minFail


OoRstr: str = "OoR"

if args.limitRC is not None:
    OoRstr += f">{args.limitRC}"

failstr: str = OoRstr #"FAILED"# + fstr


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

labels_plotted = df["Element"].values
nlabs = len(labels_plotted)
spikes_dict = {}
scatter_dict = {}
for i,dn in enumerate(labels_plotted):
    eo = df[df["Element"]==dn]["Element_ordered"].values[0]
    RCs_IA = results_IA[dn].RC
    RCs_normal = results_normal[dn].RC
    # Represent the failures / OoRs with a spike/dot at x=RCfailure 
    if results_IA[dn].OoR != [] or results_IA[dn].failures != []:
        RCs_IA.append(RCfailure)
    if results_normal[dn].OoR != [] or results_normal[dn].failures != []:
        RCs_normal.append(RCfailure)

    hover2 = HoverTool(
                tooltips=[
                    ("Func", eo + " IA"),
                    ("ResCount", "@RC{custom}"),
                    ],
                formatters={
                    "@RC" : RCFfunc,
                    #"dn"  : 'numeral'
                    }
            )
    hover3 = HoverTool(
                tooltips=[
                    ("Func", "@Name"),
                    ("ResCount", "@RC{custom}"),
                    ],
                formatters={
                    "@RC" : RCFfunc,
                    #"dn"  : 'numeral'
                    }
            )
    spikes_dict[eo] = hv.Spikes(RCs_IA,kdims="RC").opts(position=nlabs-i-1,tools=[hover2],xaxis="bottom", logx = True)
    scatter_dict[eo] = hv.Scatter((
            RCs_normal,
            [nlabs-i-0.5]*len(RCs_normal),
            [eo]*len(RCs_normal)
            ),
         kdims="RC",
         vdims=["y", "Name"]
         ).opts(
                tools=[hover3],
                xaxis="bottom",
                logx = True,
                marker='s',
                size=5,
                show_grid=True,
                xlabel="Log(RC)",
                ylabel="Func"
            )

yticks = [(nlabs-i-0.5, list(spikes_dict.keys())[i]) for i in range(nlabs)]#-1,-1,-1)]
spikes = hv.NdOverlay(spikes_dict).opts(
    yticks = yticks
    )
scatter = hv.NdOverlay(scatter_dict).opts(
    yticks = yticks
    )

spikes.opts(
    opts.Spikes(spike_length=1,
                #line_alpha=1,
                responsive=True,
                height=50+nlabs*20,
                color=hv.Cycle(),
                ylim=(0,nlabs),
                #autorange=None,
                yaxis='right',
                backend_opts={
                    # "xaxis.bounds" : (0,RCfailure)
                    },
                title="◼️ = normal mode, | = Isolated Assertions mode"
                ),    

    opts.NdOverlay(show_legend=False,
                    click_policy='mute',
                    autorange=None,
                    ylim=(0,nlabs),
                    #xlim=(3000,RCfailure),
                    padding=(0.05),
                ),
    #opts.NdOverlay(shared_axes=True, shared_datasource=True,show_legend=False)
    )

scatter.opts(
    opts.Scatter(
            responsive=True,
            height=50+nlabs*20,
            color=hv.Cycle(),
            #ylim=(0,nlabs),
            #autorange=None,
            yaxis='right',
            #backend_opts={
                #"xaxis.bounds" : (0,bins_plot[-1]+bin_width)
            #    },
            ),
)

# TABLE

df["span IA"] = df["span IA"].apply(lambda s:s*100)
df["span"] = df["span"].apply(lambda s:s*100)
df.drop(columns=["Element_ordered"], inplace=True)

table = hv.Table(df).opts(height=310,width=800)

# table = hv.Div("<h2>Normal mode:</h2>").opts(height=50) + table

    
plot = scatter * spikes + table
plot.cols(1)

class NumericalTickFormatterWithLimit(NumeralTickFormatter):
    __implementation__ = TypeScript("""
import {NumeralTickFormatter} from "models/formatters/numeral_tick_formatter"

export class NumericalTickFormatterWithLimit extends NumeralTickFormatter {
  FAIL_MIN=""" + str(int(RCfailure)) + """

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
plotfilepath = product+".html"

try:
    os.remove(plotfilepath)
except:
    pass

hv.save(plot, plotfilepath)#, title=title)


print(f"Created file {plotfilepath}")
os.system(f"open {plotfilepath}")

# Repeat the warning
# if args.limitRC is None:
#     if minOoR < inf:
#         log.warning(f"There are OoR results, but no limitRC was given. Min OoR found = {smag(minOoR)}")


#webbrowser.open('plot.html')

# ls = hv.link_selections.instance()
# lplot = ls(plot)
# hv.save(lplot, 'lplot.html')
# os.system("open lplot.html")


