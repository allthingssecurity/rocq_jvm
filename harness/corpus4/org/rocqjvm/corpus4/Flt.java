package org.rocqjvm.corpus4;

/** Phase 5 corpus: every float/double opcode javac emits, conversions, comparisons, float arrays and fields. */
public class Flt {
    static float fv; static double dv = 0.1;
    float inst = 1.5f;
    static float fadd(float a, float b) { return a + b; }
    static float fsub(float a, float b) { return a - b; }
    static float fmul(float a, float b) { return a * b; }
    static float fdiv(float a, float b) { return a / b; }
    static float frem(float a, float b) { return a % b; }
    static float fneg(float a) { return -a; }
    static double dadd(double a, double b) { return a + b; }
    static double dsub(double a, double b) { return a - b; }
    static double dmul(double a, double b) { return a * b; }
    static double ddiv(double a, double b) { return a / b; }
    static double drem(double a, double b) { return a % b; }
    static double dneg(double a) { return -a; }
    static int f2i(float a) { return (int) a; }
    static long f2l(float a) { return (long) a; }
    static double f2d(float a) { return a; }
    static int d2i(double a) { return (int) a; }
    static long d2l(double a) { return (long) a; }
    static float d2f(double a) { return (float) a; }
    static float i2f(int a) { return a; }
    static double i2d(int a) { return a; }
    static float l2f(long a) { return a; }
    static double l2d(long a) { return a; }
    static int fcmps(float a, float b) { return (a < b ? 1 : 0) | (a > b ? 2 : 0) | (a == b ? 4 : 0) | (a <= b ? 8 : 0) | (a >= b ? 16 : 0) | (a != b ? 32 : 0); }
    static int dcmps(double a, double b) { return (a < b ? 1 : 0) | (a > b ? 2 : 0) | (a == b ? 4 : 0) | (a <= b ? 8 : 0) | (a >= b ? 16 : 0) | (a != b ? 32 : 0); }
    static double poly(double x, int n) { double s = 0; double p = 1; for (int i = 0; i < (n & 15); i++) { s += p / (i + 1); p *= x; } return s; }
    static float consts(float a) { return a * 0.0f + 1.0f + 2.0f - 3.25f + (float) 1e-3; }
    static double dconsts(double a) { return a * 0.0 + 1.0 - 1e-300 + 6.02214076e23; }
    static float arrs(float a, int n) { float[] x = new float[(n & 7) + 1]; double[] y = new double[x.length]; for (int i = 0; i < x.length; i++) { x[i] = a * i; y[i] = x[i] / 3.0; } float s = 0; for (int i = 0; i < x.length; i++) s += x[i] - (float) y[i]; return s; }
    static double fields(double a) { fv = (float) a; dv = dv * a; Flt o = new Flt(); o.inst += fv; return o.inst + dv; }
    static float mixed(int i, long l, float f, double d) { return (float) (i * f + l / d - (f - i) * d); }
    static long avg(long a, double w) { return (long) (a * w + (1 - w) * (double) a); }
}
