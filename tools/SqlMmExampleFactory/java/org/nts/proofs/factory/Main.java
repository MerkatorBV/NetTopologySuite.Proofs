package org.nts.proofs.factory;

import java.nio.file.Files;
import java.nio.file.Path;
import org.stringtemplate.v4.ST;
import org.stringtemplate.v4.STGroup;
import org.stringtemplate.v4.STGroupFile;

/**
 * Minimal StringTemplate 4 driver: bag/model → WKT (§5.1.67) + WKB hex
 * (§5.1.68 Table 15). Upstream of the oracle; no new ADR-0006 keyword.
 * Engines still test the bag.
 *
 * claimId: none (tools). Does not remint
 * {@code ticket_sqlmm_factory_emit_qed_or_qex} (Rocq emit stays QEX).
 */
public final class Main {
    public static void main(String[] args) {
        if (args.length == 0 || "--help".equals(args[0]) || "-h".equals(args[0])) {
            usage();
            System.exit(args.length == 0 ? 2 : 0);
            return;
        }
        if ("--list".equals(args[0])) {
            for (String id : Catalog.all().keySet()) {
                System.out.println(id);
            }
            return;
        }
        Example g;
        if ("--stdin".equals(args[0]) || "-".equals(args[0])) {
            try {
                g = ModelReader.read(new java.io.InputStreamReader(System.in, java.nio.charset.StandardCharsets.UTF_8));
            } catch (Exception e) {
                System.err.println("stdin model: " + e.getMessage());
                System.exit(2);
                return;
            }
        } else {
            g = Catalog.get(args[0]);
        }
        emit(g);
    }

    static void emit(Example g) {
        Path templates = templatesDir();
        System.out.println("ID=" + g.id);
        System.out.println("WKT=" + renderWkt(templates, g));
        System.out.println("BAG=" + g.bagWire());
        System.out.println("TAU=" + g.tau);
        System.out.println("WKB-NDR=" + renderWkb(templates, g, true));
        System.out.println("WKB-XDR=" + renderWkb(templates, g, false));
    }

    static String renderWkt(Path templates, Example g) {
        STGroup group = new STGroupFile(templates.resolve("SqlMmWkt.stg").toString());
        ST st = group.getInstanceOf("wkt");
        if (st == null) {
            throw new IllegalStateException("SqlMmWkt.stg missing rule wkt");
        }
        st.add("g", g);
        return st.render().trim();
    }

    static String renderWkb(Path templates, Example g, boolean ndr) {
        STGroup group = new STGroupFile(templates.resolve("SqlMmWkb.stg").toString());
        ST st = group.getInstanceOf("wkb");
        if (st == null) {
            throw new IllegalStateException("SqlMmWkb.stg missing rule wkb");
        }
        st.add("g", WkbView.of(g, ndr));
        return st.render().trim();
    }

    static Path templatesDir() {
        String env = System.getenv("SQLMM_FACTORY_TEMPLATES");
        if (env != null && !env.isBlank()) {
            return Path.of(env);
        }
        Path cwd = Path.of(System.getProperty("user.dir"));
        Path[] candidates = {
            cwd.resolve("templates"),
            cwd.resolve("tools/SqlMmExampleFactory/templates")
        };
        for (Path p : candidates) {
            if (Files.isRegularFile(p.resolve("SqlMmWkt.stg"))) {
                return p;
            }
        }
        throw new IllegalStateException(
                "cannot find templates/SqlMmWkt.stg (set SQLMM_FACTORY_TEMPLATES)");
    }

    private static void usage() {
        System.err.println("usage: org.nts.proofs.factory.Main --list | <example-id> | --stdin | -");
        System.err.println("  --stdin / -  read a line-oriented Example model from stdin");
        System.err.println("env: SQLMM_FACTORY_TEMPLATES  directory with SqlMmWkt.stg / SqlMmWkb.stg");
        System.err.println("inhabits tools bytes only; Rocq emit QEX (ticket_sqlmm_factory_emit_qed_or_qex)");
    }
}
