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
import java.nio.file.*;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Scanner;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

class Result {
    public final String name;
    public final long usage;

    public Result(Map<String,String> entry) {
        this.name = entry.get("TestResult.DisplayName");
        this.usage = Long.parseLong(entry.get("TestResult.ResourceCount"));
    }

    public String toString(int width) {
        width = width - name.length();
        return name + String.format("%1$" + width + "s", Long.toString(usage));
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

    public static void main(String[] args) throws IOException {
        // Parse command-line arguments.
        CommandLine cmd = parseCommandLine(args);
        int nResults = Integer.parseInt(cmd.getOptionValue("entries", "10"));
        //
        FileSystem fs = FileSystems.getDefault();
        ArrayList<Result> results = new ArrayList<>();
        // Process globs given on the command-line.
        for (String line : args) {
            PathMatcher matcher = fs.getPathMatcher("glob:" + line);
            processGlobs(matcher,results);
        }
        // Sort results into ascending order
        results.sort((r1,r2) -> Long.compare(r1.usage, r2.usage));
        // Revert into descending order
        Collections.reverse(results);
        // Print out header
        System.out.println("Name" + String.format("%1$" + 76 + "s", "Resource Usage"));
        System.out.println(String.format("%1$" + 80 + "s", "").replace(' ','='));
        // Print top n results
        for(int i=0;i!=Math.min(nResults,results.size());++i) {
            Result ith = results.get(i);
            System.out.println(ith.toString(80));
        }
        System.out.println("...");
    }

    private static void processGlobs(PathMatcher matcher, List<Result> results) throws IOException {
        Path dir = Path.of(".");
        Files.walk(dir,10).forEach(f -> {
            Path rf = dir.relativize(f);
            if(matcher.matches(rf)) {
                try {
                    processPath(rf,results);
                } catch (IOException e) {
                   throw new RuntimeException(e);
                }
            }
        });
    }

    private static void processPath(Path p, List<Result> results) throws IOException {
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
