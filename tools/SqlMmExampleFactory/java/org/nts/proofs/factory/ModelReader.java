package org.nts.proofs.factory;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.Reader;
import java.util.ArrayList;
import java.util.List;

/**
 * Line-oriented stdin model → {@link Example}. Hunter / tools only;
 * does not remint Rocq emit inhabit.
 *
 * <pre>
 * id=synth-1
 * keyword=LINESTRING
 * tau=TagLineString
 * hens=0,1
 * pt=0,0
 * pt=2,0
 * control=0,0
 * control=2,0
 * chicken=0,1,MkChord
 * </pre>
 *
 * Compound children: {@code child-begin} … {@code child-end}.
 * JTS clothoid: {@code jts=k0,k1,L}. EMPTY: {@code empty=true}.
 *
 * claimId: none (tools).
 */
public final class ModelReader {
    private ModelReader() {}

    public static Example read(Reader raw) throws IOException {
        BufferedReader in = raw instanceof BufferedReader
                ? (BufferedReader) raw
                : new BufferedReader(raw);
        return parseBlock(in, false);
    }

    private static Example parseBlock(BufferedReader in, boolean stopOnChildEnd)
            throws IOException {
        String id = "stdin";
        String keyword = null;
        boolean empty = false;
        String tau = "TagLineString";
        List<Integer> hens = new ArrayList<>();
        List<double[]> pts = new ArrayList<>();
        List<double[]> controls = new ArrayList<>();
        List<int[]> chickenEnds = new ArrayList<>();
        List<String> chickenEggs = new ArrayList<>();
        List<Example> children = new ArrayList<>();
        String k0 = null;
        String k1 = null;
        String L = null;
        String line;
        while ((line = in.readLine()) != null) {
            line = line.trim();
            if (line.isEmpty() || line.startsWith("#")) {
                continue;
            }
            if ("child-end".equals(line)) {
                if (!stopOnChildEnd) {
                    throw new IllegalArgumentException("child-end without child-begin");
                }
                break;
            }
            if ("child-begin".equals(line)) {
                children.add(parseBlock(in, true));
                continue;
            }
            int eq = line.indexOf('=');
            if (eq <= 0) {
                throw new IllegalArgumentException("expected key=value, got: " + line);
            }
            String key = line.substring(0, eq).trim();
            String val = line.substring(eq + 1).trim();
            switch (key) {
                case "id" -> id = val;
                case "keyword" -> keyword = val;
                case "empty" -> empty = Boolean.parseBoolean(val);
                case "tau" -> tau = val;
                case "hens" -> hens.addAll(parseHens(val));
                case "pt" -> pts.add(parseXy(val));
                case "control" -> controls.add(parseXy(val));
                case "chicken" -> {
                    String[] parts = split3(val);
                    chickenEnds.add(new int[] {Integer.parseInt(parts[0]), Integer.parseInt(parts[1])});
                    chickenEggs.add(parts[2]);
                }
                case "jts" -> {
                    String[] parts = split3(val);
                    k0 = parts[0];
                    k1 = parts[1];
                    L = parts[2];
                }
                default -> throw new IllegalArgumentException("unknown model key: " + key);
            }
        }
        if (keyword == null || keyword.isBlank()) {
            throw new IllegalArgumentException("model missing keyword=");
        }
        Example.Builder b = Example.builder(id, keyword);
        if (empty) {
            b.empty();
        }
        if (!hens.isEmpty()) {
            int[] hs = new int[hens.size()];
            for (int i = 0; i < hens.size(); i++) {
                hs[i] = hens.get(i);
            }
            b.hens(hs);
        }
        for (double[] p : pts) {
            b.pt(p[0], p[1]);
        }
        for (double[] p : controls) {
            b.control(p[0], p[1]);
        }
        for (int i = 0; i < chickenEnds.size(); i++) {
            b.chicken(chickenEnds.get(i)[0], chickenEnds.get(i)[1], chickenEggs.get(i));
        }
        for (Example c : children) {
            b.child(c);
        }
        b.tau(tau);
        if (k0 != null) {
            b.jts(k0, k1, L);
        }
        return b.build();
    }

    private static List<Integer> parseHens(String val) {
        List<Integer> out = new ArrayList<>();
        if (val.isEmpty()) {
            return out;
        }
        for (String p : val.split(",")) {
            String t = p.trim();
            if (!t.isEmpty()) {
                out.add(Integer.parseInt(t));
            }
        }
        return out;
    }

    private static double[] parseXy(String val) {
        String[] parts = val.split("[,\\s]+");
        if (parts.length != 2) {
            throw new IllegalArgumentException("expected x,y got: " + val);
        }
        return new double[] {Double.parseDouble(parts[0]), Double.parseDouble(parts[1])};
    }

    private static String[] split3(String val) {
        String[] parts = val.split(",", 3);
        if (parts.length != 3) {
            throw new IllegalArgumentException("expected three comma fields, got: " + val);
        }
        return new String[] {parts[0].trim(), parts[1].trim(), parts[2].trim()};
    }
}
