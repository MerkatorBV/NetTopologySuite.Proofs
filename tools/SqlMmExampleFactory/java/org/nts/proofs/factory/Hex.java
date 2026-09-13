package org.nts.proofs.factory;

/**
 * Endian hex fragments for §5.1.68 WKB. Templates concatenate; this class
 * does not invent type codes.
 *
 * claimId: none (tools).
 */
public final class Hex {
    private Hex() {}

    public static String u8(int v) {
        return String.format("%02x", v & 0xff);
    }

    public static String u32(int v, boolean littleEndian) {
        byte[] b = new byte[4];
        if (littleEndian) {
            b[0] = (byte) v;
            b[1] = (byte) (v >>> 8);
            b[2] = (byte) (v >>> 16);
            b[3] = (byte) (v >>> 24);
        } else {
            b[0] = (byte) (v >>> 24);
            b[1] = (byte) (v >>> 16);
            b[2] = (byte) (v >>> 8);
            b[3] = (byte) v;
        }
        return bytes(b);
    }

    public static String f64(double v, boolean littleEndian) {
        long bits = Double.doubleToLongBits(v);
        byte[] b = new byte[8];
        if (littleEndian) {
            for (int i = 0; i < 8; i++) {
                b[i] = (byte) (bits >>> (8 * i));
            }
        } else {
            for (int i = 0; i < 8; i++) {
                b[i] = (byte) (bits >>> (8 * (7 - i)));
            }
        }
        return bytes(b);
    }

    public static String bytes(byte[] b) {
        StringBuilder sb = new StringBuilder(b.length * 2);
        for (byte x : b) {
            sb.append(String.format("%02x", x & 0xff));
        }
        return sb.toString();
    }

    /** Same trim as {@code IntakeResult} so bag pts and WKT share spellings. */
    public static String trim(double v) {
        if (v == Math.rint(v) && Math.abs(v) < 1e12) {
            return Long.toString((long) v);
        }
        return Double.toString(v);
    }
}
