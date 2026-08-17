/*
 * Copyright (c) 2026 grootstebozewolf
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License 2.0
 * and Eclipse Distribution License v. 1.0 which accompanies this distribution.
 * The Eclipse Public License is available at http://www.eclipse.org/legal/epl-v20.html
 * and the Eclipse Distribution License is available at
 *
 * http://www.eclipse.org/org/documents/edl-v10.php.
 */
package org.locationtech.jts.algorithm.rocq;

import com.sun.jna.Library;
import com.sun.jna.Native;
import com.sun.jna.ptr.DoubleByReference;

/**
 * Phase 5 reference binding: the Java side of {@code libntsrocq}
 * ({@code oracle/nts_ffi.h}).
 * <p>
 * Loads the shared library at runtime (JNA). Override the path with
 * {@code NTS_ROCQ_LIB}. Default library name is {@code ntsrocq}
 * (JNA resolves {@code libntsrocq.so} / {@code libntsrocq.dylib} /
 * {@code ntsrocq.dll}).
 * <p>
 * Threading: the embedded OCaml 4.14 runtime is not re-entrant. Every
 * call is serialised on {@link #GATE}.
 * <p>
 * This class is the ABI twin of {@code oracle/csharp/RocqNative.cs} and
 * {@code oracle/cpp/RocqNative.hpp}. If they disagree, one of them is wrong.
 * The Java consumer lands on fork PR #7 ({@code feature/sfa-curve-rgr});
 * locationtech/jts is not a gate.
 * <p>
 * AI disclosure: authored with AI assistance (see CONTRIBUTING.md).
 */
public final class RocqNative {

    public static final int EXPECTED_ABI_VERSION = 1;

    public static final int ORIENT_NEG = -1;
    public static final int ORIENT_ZERO = 0;
    public static final int ORIENT_POS = 1;
    public static final int ORIENT_NAN = 2;
    public static final int ORIENT_UNCERTAIN = 3;

    public static final int INTERSECT_NONE = 0;
    public static final int INTERSECT_POINT = 1;
    public static final int INTERSECT_COLLINEAR = 2;
    public static final int INTERSECT_NAN = 3;
    public static final int INTERSECT_UNCERTAIN = 4;

    public static final int OP_UNION = 0;
    public static final int OP_INTERSECTION = 1;
    public static final int OP_DIFFERENCE = 2;
    public static final int OP_SYMDIFF = 3;

    private static final Object GATE = new Object();
    private static final Lib LIB;
    private static final boolean AVAILABLE;

    static {
        Lib loaded = null;
        boolean ok = false;
        try {
            String override = System.getenv("NTS_ROCQ_LIB");
            if (override != null && !override.isEmpty()) {
                loaded = Native.load(override, Lib.class);
            }
            else {
                loaded = Native.load("ntsrocq", Lib.class);
            }
            if (loaded.nts_rocq_init() == 0
                && loaded.nts_rocq_abi_version() == EXPECTED_ABI_VERSION) {
                ok = true;
            }
        }
        catch (UnsatisfiedLinkError | RuntimeException ex) {
            loaded = null;
            ok = false;
        }
        LIB = loaded;
        AVAILABLE = ok;
    }

    private RocqNative() {
    }

    public static boolean isAvailable() {
        return AVAILABLE;
    }

    public static int abiVersion() {
        return require().nts_rocq_abi_version();
    }

    public static int orientSignFiltered(
        double p0x, double p0y, double p1x, double p1y, double qx, double qy) {
        synchronized (GATE) {
            return require().nts_rocq_orient_sign_filtered(p0x, p0y, p1x, p1y, qx, qy);
        }
    }

    public static int orientSignNaive(
        double p0x, double p0y, double p1x, double p1y, double qx, double qy) {
        synchronized (GATE) {
            return require().nts_rocq_orient_sign_naive(p0x, p0y, p1x, p1y, qx, qy);
        }
    }

    public static int orientSignExact(
        double p0x, double p0y, double p1x, double p1y, double qx, double qy) {
        synchronized (GATE) {
            return require().nts_rocq_orient_sign_exact(p0x, p0y, p1x, p1y, qx, qy);
        }
    }

    public static double orient2d(
        double p0x, double p0y, double p1x, double p1y, double qx, double qy) {
        synchronized (GATE) {
            return require().nts_rocq_orient2d(p0x, p0y, p1x, p1y, qx, qy);
        }
    }

    public static int intersectSignFiltered(
        double p0x, double p0y, double p1x, double p1y,
        double q0x, double q0y, double q1x, double q1y) {
        synchronized (GATE) {
            return require().nts_rocq_intersect_sign_filtered(
                p0x, p0y, p1x, p1y, q0x, q0y, q1x, q1y);
        }
    }

    public static boolean tryIntersectPoint(
        double p0x, double p0y, double p1x, double p1y,
        double q0x, double q0y, double q1x, double q1y,
        double[] xy) {
        DoubleByReference x = new DoubleByReference();
        DoubleByReference y = new DoubleByReference();
        synchronized (GATE) {
            int r = require().nts_rocq_intersect_point(
                p0x, p0y, p1x, p1y, q0x, q0y, q1x, q1y, x, y);
            xy[0] = x.getValue();
            xy[1] = y.getValue();
            return r == 1;
        }
    }

    public static boolean passesThroughHotPixel(
        double p0x, double p0y, double p1x, double p1y, double cx, double cy) {
        synchronized (GATE) {
            return require().nts_rocq_passes_through_hot_pixel(p0x, p0y, p1x, p1y, cx, cy) == 1;
        }
    }

    public static double inCircle(
        double ax, double ay, double bx, double by,
        double cx, double cy, double px, double py) {
        synchronized (GATE) {
            return require().nts_rocq_in_circle(ax, ay, bx, by, cx, cy, px, py);
        }
    }

    public static boolean chordCrossesArcCircle(
        double sx, double sy, double mx, double my, double ex, double ey,
        double px, double py, double qx, double qy) {
        synchronized (GATE) {
            return require().nts_rocq_chord_crosses_arc_circle(
                sx, sy, mx, my, ex, ey, px, py, qx, qy) == 1;
        }
    }

    private static Lib require() {
        if (!AVAILABLE || LIB == null) {
            throw new IllegalStateException(
                "libntsrocq is not available. Build it with `make -C oracle ffi` "
                    + "in NetTopologySuite.Proofs, or set NTS_ROCQ_LIB.");
        }
        return LIB;
    }

    public interface Lib extends Library {
        int nts_rocq_init();
        int nts_rocq_abi_version();
        int nts_rocq_orient_sign_filtered(double p0x, double p0y, double p1x, double p1y, double qx, double qy);
        int nts_rocq_orient_sign_naive(double p0x, double p0y, double p1x, double p1y, double qx, double qy);
        int nts_rocq_orient_sign_exact(double p0x, double p0y, double p1x, double p1y, double qx, double qy);
        double nts_rocq_orient2d(double p0x, double p0y, double p1x, double p1y, double qx, double qy);
        int nts_rocq_intersect_sign_filtered(
            double p0x, double p0y, double p1x, double p1y,
            double q0x, double q0y, double q1x, double q1y);
        int nts_rocq_intersect_point(
            double p0x, double p0y, double p1x, double p1y,
            double q0x, double q0y, double q1x, double q1y,
            DoubleByReference outX, DoubleByReference outY);
        int nts_rocq_passes_through_hot_pixel(
            double p0x, double p0y, double p1x, double p1y, double cx, double cy);
        double nts_rocq_in_circle(
            double ax, double ay, double bx, double by,
            double cx, double cy, double px, double py);
        int nts_rocq_chord_crosses_arc_circle(
            double sx, double sy, double mx, double my, double ex, double ey,
            double px, double py, double qx, double qy);
    }
}
