/*
 * Copyright 2022 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License. You may obtain
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */
package dafnyevm.util;

import java.io.IOException;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.MathContext;
import java.math.RoundingMode;
import java.nio.file.*;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Scanner;
import java.util.concurrent.atomic.AtomicInteger;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

class Result {
    private static final BigDecimal KILO = BigDecimal.valueOf(1_000L);
    private static final BigDecimal MEGA = BigDecimal.valueOf(1_000_000L);
    private static final BigDecimal GIGA = BigDecimal.valueOf(1_000_000_000L);
    private static final MathContext CONTEXT = new MathContext(4,RoundingMode.HALF_UP);
    public final String name;
    public final ArrayList<BigInteger> usages;

    public Result(Map<String,String> entry) {
        // Strip off trailing stuff (e.g. assertion batch 0) as it just gets in the way.
        if (! Objects.equals(entry.get("TestResult.Outcome"),"Passed")) {
            System.err.println("Failed entry: %s = %s".formatted(toName(entry.get("TestResult.DisplayName")),toUnitString(new BigInteger(entry.get("TestResult.ResourceCount")))));
            //System.exit(1);
        }
        this.name = toName(entry.get("TestResult.DisplayName"));
        this.usages = new ArrayList<>();
        this.usages.add(new BigInteger(entry.get("TestResult.ResourceCount")));
    }

    public BigInteger sum() {
        BigInteger n = BigInteger.ZERO;
        for(int i=0;i!=usages.size();++i) {
            n = n.add(usages.get(i));
        }
        return n;
    }

    public BigInteger mean() {
        return sum().divide(BigInteger.valueOf(usages.size()));
    }

    public BigInteger variance() {
        BigInteger variance = BigInteger.ZERO;
        BigInteger mean = mean();
        for(int i=0;i!=usages.size();++i) {
            BigInteger ith = usages.get(i);
            ith = ith.subtract(mean).pow(2);
            variance = variance.add(ith);
        }
        return variance;
    }

    public BigInteger stddev() {
        BigInteger N = BigInteger.valueOf(usages.size());
        return variance().divide(N).sqrt();
    }

    public double coeffVariance() {
        return stddev().doubleValue() / mean().doubleValue();
    }

    public BigInteger min() {
        return usages.get(0);
    }

    public BigInteger max() {
        return usages.get(usages.size()-1);
    }

    public BigInteger median() {
        var i = usages.size();
        return usages.get(i/2);
    }

    public void join(Result r) {
        usages.addAll(r.usages);
    }

    private String toName(String displayName) {
        String[] items = displayName.split(" ");
        if (! displayName.contains("(assertion batch 0)")) {
            System.err.println("Assertion batch != 0!");
            System.exit(1);
        }
        String res = "[" + toNameType(items[1]) + "] " + items[0];
        return res;
    }

    private String toNameType(String input) {
        switch(input) {
            case "(well-formedness)":
                return "WF";
            case "(correctness)":
                return "CO";
            default:
                return "??";
        }
    }

    public String toString(int width) {
        String samples = "[" + usages.size() + "]";
        width -= name.length() + samples.length();
        String mean = toUnitString(mean());
        var min = toUnitString(min());
        var max = toUnitString(max());
        var median = toUnitString(median());
        String label = String.format("%1$s  (%2$.2f) %3$7s %4$7s %5$7s", mean, coeffVariance(), min, median, max);
        return samples + name + String.format("%1$" + width + "s", label);
    }

    private String toUnitString(BigInteger _value) {
        BigDecimal value = new BigDecimal(_value, CONTEXT);
        if(value.compareTo(GIGA) >= 0) {
            return value.divide(GIGA).toString() + "G";
        } else if(value.compareTo(MEGA) >= 0) {
            return value.divide(MEGA).toString() + "M";
        } else if(value.compareTo(KILO) >= 0) {
            return value.divide(KILO).toString() + "K";
        } else {
            return value.toString();
        }
    }
}

public class DafnyLogSummariser {
    private static final Option[] OPTIONS = new Option[] {
            new Option("entries", true, "Report at most n results"),
    };

    public static CommandLine parseCommandLine(String[] args) {
        // Configure command-line options.
        Options options = new Options();
        for(Option o : OPTIONS) { options.addOption(o); }
        CommandLineParser parser = new DefaultParser();
        // use to read Command Line Arguments
        HelpFormatter formatter = new HelpFormatter();  // // Use to Format
        try {
            return parser.parse(options, args);  //it will parse according to the options and parse option value
        } catch (ParseException e) {
            System.out.println(e.getMessage());
            formatter.printHelp("dafnyevm", options);
            System.exit(1);
            return null;
        }
    }

    public static ArrayList<Result> merge(ArrayList<Result> results) {
        HashMap<String,Result> map = new HashMap<>();
        // Join all results together
        for(int i=0;i!=results.size();++i) {
            Result ith = results.get(i);
            if(map.containsKey(ith.name)) {
                ith.join(map.get(ith.name));
            }
            map.put(ith.name,ith);
        }

        // sort the usages so that we can get the medians (and easy max,min)
        for (var k: map.keySet()) {
            var v = map.get(k);
            v.usages.sort(BigInteger::compareTo);
        }

        // Done
        return new ArrayList<>(map.values());
    }

    public static void main(String[] args) throws IOException {
        // Parse command-line arguments.
        CommandLine cmd = parseCommandLine(args);
        //System.out.println("args at Java = " + String.join(" ",args));
        int nResults = Integer.parseInt(cmd.getOptionValue("entries", "20"));
        //
        FileSystem fs = FileSystems.getDefault();
        ArrayList<Result> results = new ArrayList<>();
        // Process globs given on the command-line.
        for (String line : args) {
            PathMatcher matcher = fs.getPathMatcher("glob:" + line);
            int count = processGlobs(matcher,results);
            if (count == 0){
                System.err.println("NO MATCHES: %s ".formatted(line));
            }
        }
        // Combine duplicate results
        results = merge(results);
        // Sort results into ascending order
        //results.sort((r1,r2) -> r1.mean().compareTo(r2.mean()));
        //results.sort((r1,r2) -> Double.compare(r1.coeffVariance(),r2.coeffVariance()));
        results.sort((r1,r2) -> r1.max().compareTo(r2.max()));

        // Revert into descending order
        Collections.reverse(results);
        // Print out header
        System.out.println("Name" + String.format("%1$" + 76 + "s", "RU   (CoV)      Min  Median     Max"));
        System.out.println(String.format("%1$" + 80 + "s", "").replace(' ','='));
        // Print top n results
        BigInteger total = BigInteger.ZERO;
        BigInteger subtotal = BigInteger.ZERO;
        for(int i=0;i!=results.size();++i) {
            Result ith = results.get(i);
            if(i < nResults) {
                System.out.println(ith.toString(80));
                subtotal = subtotal.add(ith.mean());
            }
            total = total.add(ith.mean());
        }
        System.out.println("...");
        System.out.println(String.format("%1$" + 80 + "s", "").replace(' ','='));
        System.out.println(String.format("Subtotal (mean):" + "%1$" + 64 + "s", subtotal.toString()));
        System.out.println(String.format("Total (mean):" + "%1$" + 67 + "s", total.toString()));
    }

    private static int processGlobs(PathMatcher matcher, List<Result> results) throws IOException {
        Path dir = Path.of(".");
        AtomicInteger count = new AtomicInteger(0);
        Files.walk(dir,10).forEach(f -> {
            Path rf = dir.relativize(f);
            if(matcher.matches(rf)) {
                count.incrementAndGet();
                try {
                    processPath(rf,results);
                } catch (IOException e) {
                   throw new RuntimeException(e);
                }
            }
        });
        return count.intValue();

    }

    private static void processPath(Path p, List<Result> results) throws IOException {
        System.out.println("processing file "+p);
        try (Scanner scanner = new Scanner(p);) {
            String[] headers = scanner.nextLine().split(",");
            while (scanner.hasNextLine()) {
                String[] items = scanner.nextLine().split(",");
                HashMap<String,String> map = new HashMap<>();
                for(int i=0;i!=headers.length;++i) {
                    map.put(headers[i],items[i]);
                }
                results.add(new Result(map));
            }
        }
    }
}
