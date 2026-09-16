package org.nts.proofs.factory;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import org.nts.proofs.factory.Example.Pt;

/**
 * ST4 attributes for {@code SqlMmWkb.stg}. Signed Table 15 codes this
 * slice: 1, 2, 8, 9. CIRCLE / CLOTHOID / empty Point take the HOLD
 * rule (κ=none; not 13–17 / 18–21).
 *
 * claimId: none (tools).
 */
public final class WkbView {
    public final boolean point;
    public final boolean lineString;
    public final boolean circularString;
    public final boolean compound;
    public final boolean signedWkb;
    public final String orderHex;
    public final String typeHex;
    public final String countHex;
    public final String pointsHex;
    public final String holdName;
    public final List<WkbView> children;

    private WkbView(
            boolean point,
            boolean lineString,
            boolean circularString,
            boolean compound,
            boolean signedWkb,
            String orderHex,
            String typeHex,
            String countHex,
            String pointsHex,
            String holdName,
            List<WkbView> children) {
        this.point = point;
        this.lineString = lineString;
        this.circularString = circularString;
        this.compound = compound;
        this.signedWkb = signedWkb;
        this.orderHex = orderHex;
        this.typeHex = typeHex;
        this.countHex = countHex;
        this.pointsHex = pointsHex;
        this.holdName = holdName;
        this.children = children;
    }

    public static WkbView of(Example g, boolean ndr) {
        String order = Hex.u8(ndr ? 1 : 0);
        if (g.circle) {
            return hold("CIRCLE κ=none (not WKB 18; not codes 13–17 / 18–21)");
        }
        if (g.clothoid) {
            return hold("CLOTHOID κ=none (not WKB 22; not codes 13–17 / 18–21)");
        }
        if (g.point && g.empty) {
            return hold("POINT EMPTY (no signed empty-point payload this slice)");
        }
        if (g.point) {
            Pt p = g.controls.isEmpty() ? g.pts.get(0) : g.controls.get(0);
            return new WkbView(
                    true, false, false, false, true,
                    order, Hex.u32(1, ndr), "",
                    Hex.f64(p.xd, ndr) + Hex.f64(p.yd, ndr),
                    "", List.of());
        }
        if (g.lineString || g.circularString) {
            int code = g.circularString ? 8 : 2;
            List<Pt> pts = g.empty ? List.of() : (g.controls.isEmpty() ? g.pts : g.controls);
            return new WkbView(
                    false, g.lineString, g.circularString, false, true,
                    order, Hex.u32(code, ndr), Hex.u32(pts.size(), ndr),
                    xyHex(pts, ndr), "", List.of());
        }
        if (g.compound) {
            List<WkbView> kids = new ArrayList<>();
            for (Example c : g.children) {
                WkbView child = of(c, ndr);
                if (!child.signedWkb) {
                    return hold("COMPOUNDCURVE child without signed Table 15 code: " + child.holdName);
                }
                kids.add(child);
            }
            return new WkbView(
                    false, false, false, true, true,
                    order, Hex.u32(9, ndr), Hex.u32(kids.size(), ndr),
                    "", "", Collections.unmodifiableList(kids));
        }
        return hold("no signed Table 15 code for " + g.keyword
                + " (HOLD 13–17 / 18–21; not advertised as signed I/O)");
    }

    private static WkbView hold(String name) {
        return new WkbView(
                false, false, false, false, false,
                "", "", "", "", name, List.of());
    }

    private static String xyHex(List<Pt> pts, boolean ndr) {
        StringBuilder sb = new StringBuilder();
        for (Pt p : pts) {
            sb.append(Hex.f64(p.xd, ndr));
            sb.append(Hex.f64(p.yd, ndr));
        }
        return sb.toString();
    }
}
