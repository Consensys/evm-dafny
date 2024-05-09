import dis
import json
import logging as log
import re
from datetime import datetime as dt, timedelta as td
import os
import pickle

def cleanDisplayName(dn:str) -> str:
    new = dn.replace("(well-formedness)","") # WF is almost everywhere, so omit it; better just mention anything non-WF
    new = new.replace("(correctness)","[C]")
    new = re.sub(r"\(assertion batch (\d+)\)",r"AB\1", new)
    return new.strip()

class Details:
    def __init__(self):
        self.RC: list[int]= []
        self.fails = []
    RC: list[int]
    RC_max: int     #useful for the table
    RC_min: int
    line: int = None
    col: int = None
    filename: str = None
    description: str = None
    randomSeed: int = None
    RC_delta: int
    fails: list[int]

type resultsType = dict[str, Details]

def mergeResults(r:resultsType, rNew:resultsType):
    if len(rNew) == 0:
        log.error(f"no results in rNew")
        exit(1)
    for k in rNew:
        if k in r:
            r[k].RC.extend(rNew[k].RC)
            r[k].fails.extend(rNew[k].fails)
        else:
            r[k] = rNew[k]

def check_locations_ABs(locations) -> None:
    # checks across the whole file
    for loc,RStoABs in locations.items():
        ABs_first = None
        # Ensure that, for each location, the ABs stay the same in every run
        for r,ABs in RStoABs.items():
            if ABs_first == None:
                ABs_first = ABs
                continue
            assert ABs_first == ABs, f"{loc} has changing ABs. Until now it was {ABs_first}. But for rseed {r}, it's {ABs}"



def readJSON(fullpath: str, paranoid=False) -> resultsType:
    #reads 1 file (possibly containing multiple verification runs)
    results: resultsType = {}

    with open(fullpath) as jsonfile:
        verificationResults = json.load(jsonfile)["verificationResults"]
    log.debug(f"{fullpath}: {len(verificationResults)} verificationResults")

    # A JSON verification log contains a list of verificationResults
    # multiple verification runs are only distinguishable because the randomseed changes
    # Each vR corresponds to a function or method
    # and contains its Display Name, overall Resource Count, verification outcome and the vcResults (Assertion Batches)
    #   Each AB contains its number (vcNum), outcome, Resource Count, and a list of assertions
    # If "isolating assertions" was NOT used, then the AB list in a vR will contain only 1 AB
    #   1 vR = 1 AB = 1*(multiple assertions); we ignore them for plotting
    #       The AB contains the details we want; we ignore the individual assertions
    # If "isolating assertions" was used, then
    #   1 vR = n AB = n*(1 assertion)
    #       Each AB contains details we want; we store the assertion locations
    #
    # Recap: if "isolating assertions" was NOT used, then the AB number is always 1, so no need to add it to our DN
    # and its entry only contains the list of RCs, not anything deeper
    # But if "isolating assertions" was used, then each DN contains an "AB x";
    # and each DN+AB's entry contains not only list of RCs, but also location

    mode_IA = None  # Isolate Assertions. We'll guess the mode to check if it stays coherent.
    locations: dict[tuple,dict[int,dict[str,str]]] = {} # to detect when a location (file,line,col) has consistent ABs across random seeds:{randomseed:{displayname_AB:description}}
    dn_to_vcrs: dict[str,int] = {} # does a dn always have the same number of vcrs?

    for vr in verificationResults:
        display_name = cleanDisplayName(vr["name"])
        assert vr["outcome"] in ["Correct", "Errors", "OutOfResource"], f"{vr["name"]} has unknown outcome: {vr["outcome"]=}"

        # Without "isolating assertions", there is only 1 vcr per vr
        # Curiously, with IA, there is always (?) an extra empty assertion in each AB, so with IA the minimum is 2 assertions per AB

        if mode_IA == None:
            mode_IA = (len(vr['vcResults']) > 1)

        assert mode_IA == (len(vr['vcResults']) != 1), f"It looked like 'isolating-assertions'=={mode_IA}, and yet there's {len(vr['vcResults'])} ABs for {display_name}"

        # We will store only the vcr's RC in each DN
        # but check that the vr's RC equals the sum of the vcrs.
        vcrs_RC = []
        vr_RC = vr["resourceCount"]

        vr_randomseed = None # The vr doesn't contain a randomseed, only the vcrs do. Ensure that the randomseed stays consistent across them.
        for vcr in vr['vcResults']:
            if vr_randomseed == None:
                vr_randomseed = vcr["randomSeed"]
            else:
                assert vr_randomseed == vcr["randomSeed"]

            #assert vcr['outcome'] == "Valid", f"{vr["name"]} has vcResult.outcome == {vr["outcome"]}, stopping"
            if mode_IA:
                # There's multiple ABs. Each AB contains a single assertion
                display_name_AB: str = display_name + f" AB{vcr["vcNum"]}"
                det: Details = results.get(display_name_AB, Details())

                if vcr['vcNum'] == 1:
                    assert len(vcr['assertions']) == 0 #only seems to happen in the first one
                    # Plus, assertions contain their location and description, so here there should be nothing either
                    # Ensure that it's empty every time it appears
                    assert det.line == None
                    assert det.col == None
                    assert det.description == None
                else:
                    assert len(vcr['assertions']) == 1, f"{display_name_AB} contains {len(vcr['assertions'])} assertions, expected only 1 because we're in IA mode!"
                    a = vcr['assertions'][0]
                    if det.line != None:
                        # Looks like this is not the first verification run, so
                        # just double-check that everything stays consistent with previous runs
                        assert det.filename == a['filename']
                        assert det.line == a['line']
                        assert det.col == a['col']
                        assert det.description == a['description']
                    else:
                        det.filename = a['filename']
                        det.line = a['line']
                        det.col = a['col']
                        det.description = a['description']
                location_current = (det.filename, det.line, det.col)
                l = locations.get(location_current,{})
                l2 = l.get(vr_randomseed,{})
                l2[vcr["vcNum"]]=det.description
                l[vr_randomseed]=l2
                locations[location_current] = l
            else:
                # A single AB with all the assertions. We don't want that much detail for plotting.
                display_name_AB = display_name
                det: Details = results.get(display_name_AB, Details())
                pass

            vcr_RC = vcr['resourceCount']
            vcrs_RC.append(vcr_RC)
            det.randomSeed = vcr['randomSeed']
            if vcr["outcome"] != "Valid" :
                assert vcr["outcome"] in ["OutOfResource","Invalid"], f"{display_name_AB}.outcome == {vcr["outcome"]}: unexpected!"
                assert vr["outcome"] in ["OutOfResource","Errors"], f"{display_name}.outcome == {vr["outcome"]}: unexpected!"
                det.fails.append(vcr_RC)
            else: # vcr Valid
                det.RC.append(vcr_RC)
            results[display_name_AB] = det

        # Ensure that the sum of AB's RCs equals the vr's RC
        assert sum(vcrs_RC) == vr_RC, f"{display_name}.RC={vr_RC}, but the sum of the vcrs' RCs is {sum(vcrs_RC)} "
        
        if paranoid:
            check_locations_ABs(locations)

    return results



def readLogs(paths,recreate_pickle = True) -> resultsType:
    results: resultsType = {}
    files = 0
    # to be un/pickled: [files, results]

    t0 = dt.now()
    picklefilepath = "".join(paths)+"v2.pickle"
    if os.path.isfile(picklefilepath) and not recreate_pickle:
        with open(picklefilepath, 'rb') as pf:
            [files, results] = pickle.load(pf)
        print(f"Loaded pickle: {files} files {(dt.now()-t0)/td(seconds=1)}")
        return results
    else:

        for p in paths:
            # os.walk doesn't accept files, only dirs; so we need to process single files separately
            log.debug(f"root {p}")
            if os.path.isfile(p):
                results_read = readJSON(p)
                mergeResults(results, results_read)
                files += 1
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
                    results_read = readJSON(fullpath)
                    mergeResults(results, results_read)

            if files_before_root == files:
                print(f"no files found in {p}")
                exit(1)


        print(f"Processed {files} files in {(dt.now()-t0)/td(seconds=1)}")
        #print(results)

        # print overlapping ABs
        # go through each result, store its location vs what happened in it
        # finally print locations with multiple results
        # loc_ABs: dict[tuple,dict[str,str]] = {}
        # for dn,det in results.items():
        #     loc = (det.filename,det.line,det.col)
        #     if loc == (None, None, None):
        #         continue
        #     ABs = loc_ABs.get(loc,{})
        #     ABs[dn]=det.description
        #     loc_ABs[loc]=ABs
        # for loc,ABs in loc_ABs.items():
        #     if len(ABs)>1:
        #         log.info(f" {loc[0]}:{loc[1]}:{loc[2]} contains {len(ABs)} ABs: {ABs}")

        with open(picklefilepath, "wb") as pf:
            pickle.dump([files, results], pf)
        return results

#TODO warn of ABs with the same location
#TODO warn of vcr totals != sum of vcr's partials
