package org.rocqjvm.corpus6;

/** Corpus 6: field resolution through superclasses and superinterfaces (JVMS 5.4.3.2), shadowed
 *  instance and static fields, class initialisation order (JVMS 5.5: declaring class only,
 *  superclass before subclass, superinterfaces with default methods, circular initialisation,
 *  erroneous classes), static methods inherited from a superclass (invokestatic initialises the
 *  declaring class).  Every test records the initialisation events in Log.v (one digit per event). */
public class Fld {
    static class Log { static long v; static int add(int k) { v = v * 10 + k; return k; }
                       static int boom(int x) { if (x != 0) throw new IllegalStateException(); return 1; } static int sel; }

    // inherited statics
    static class P { static int ps = Log.add(1); static int pt = 10; static int pm(int x) { return x + ps; } }
    static class Q extends P { static int qs = Log.add(2); static int pt = 20; }
    static class Q2 extends Q { static int q2 = Log.add(3); }
    interface IF { int K = Log.add(4); int K2 = 40; }
    interface IG extends IF { int G = Log.add(5); }
    static class R implements IG { static int rs = Log.add(6); }
    static class R2 extends Q implements IF { static int r2 = Log.add(7); }

    /** getstatic of a field inherited from a superclass initialises only the declaring class. */
    static long inheritedGet(int x) {
        int a = Q.ps;                       // getstatic Q.ps -> P only
        if ((x & 1) != 0) a += Q2.ps;       // still P
        if ((x & 2) != 0) a += Q2.qs;       // Q, Q2 not (qs declared in Q)
        if ((x & 4) != 0) a += Q2.q2;       // Q2
        if ((x & 8) != 0) a += Q2.pt + Q.pt + P.pt;  // shadowed statics: Q.pt, Q.pt, P.pt
        return Log.v * 1000 + a;
    }
    /** putstatic through a subclass writes the superclass's field. */
    static long inheritedPut(int x) {
        Q.ps = x;                           // putstatic Q.ps -> P initialised, then written
        if ((x & 1) != 0) Q2.pt = x + 1;    // Q's pt
        return Log.v * 1_000_000_000L + (long) P.ps + 3L * Q.pt + 7L * P.pt;
    }
    /** interface fields: initialise the interface, not the class that implements it. */
    static long ifaceField(int x) {
        int a = 0;
        if ((x & 1) != 0) a += R.K;         // getstatic R.K -> IF only
        if ((x & 2) != 0) a += R.G;         // IG only (IF is not initialised by IG's initialisation)
        if ((x & 4) != 0) a += R.rs;        // R: no superinterface initialised (no default methods)
        if ((x & 8) != 0) a += R2.K + R2.ps;// IF; P
        if ((x & 16) != 0) a += R2.r2;      // P, Q, R2
        if ((x & 32) != 0) a += IG.K2 + R.K2; // constants: no initialisation
        return Log.v * 1000 + a;
    }
    /** invokestatic of a static method inherited from a superclass initialises only the declaring class. */
    static long inheritedStaticCall(int x) {
        int a = Q.pm(x & 0xff);             // invokestatic Q.pm -> P
        if ((x & 256) != 0) a += Q2.pm(1);
        if ((x & 512) != 0) a += Q2.qs;
        return Log.v * 10000 + a;
    }

    // superinterfaces with default methods are initialised before the class (JVMS 5.5 step 7)
    interface DA0 { int a0 = Log.add(1); default int m0() { return 1; } }
    interface DA extends DA0 { int a = Log.add(2); default int ma() { return 2; } }
    interface DB { int b = Log.add(3); private int pb() { return 3; } static int sb() { return 4; } }
    interface DC { int c = Log.add(9); int mc(); }
    interface DD { int d = Log.add(8); static int sd() { return 5; } }
    static class DP { static int dp = Log.add(5); }
    static class DS extends DP implements DC, DA, DB, DD { static int ds = Log.add(6); public int mc() { return 7; } }
    static class DT extends DS implements DA0 { static int dt = Log.add(7); }
    static long defaultsInit(int x) {
        int r = 0;
        if ((x & 1) != 0) r += DA.a;        // DA only (interfaces do not initialise superinterfaces)
        if ((x & 2) != 0) r += new DS().mc(); // DP, DA0, DA, DB (private instance method), DS; not DC, DD
        if ((x & 4) != 0) r += DT.dt;
        if ((x & 8) != 0) r += DD.sd();     // DD
        return Log.v * 100 + r;
    }

    // circular initialisation: the subclass is "in progress" while its superclass initialiser runs
    static class CA { static int a = CB.b + 1; static int a2 = CB.c; }
    static class CB extends CA { static int b = 5; static final int c = 6; static int d = CA.a * 10; }
    static long circular(int x) {
        if ((x & 1) != 0) return CA.a * 1000 + CB.b * 100 + CB.d;   // CA first: CB.b triggers CB -> CA in progress
        return CB.b * 1000 + CA.a * 100 + CB.d + CA.a2;             // CB first: CA sees CB.b == 0
    }

    // erroneous classes
    static class EP { static int ep = Log.add(1); }
    static class ES extends EP { static int es = Log.boom(Log.sel); static int get() { return es; } }
    interface IE { int ie = Log.add(2) + Log.boom(Log.sel); default int q() { return 1; } }
    static class CE extends EP implements IE { static int ce = Log.add(3); }
    static class CE2 extends CE { static int ce2 = Log.add(4); }
    static long erroneous(int x) {
        Log.sel = x & 1;
        long r = 0;
        try { r += ES.es; } catch (ExceptionInInitializerError e) { r += 100; }
        try { r += ES.ep; } catch (NoClassDefFoundError e) { r += 1000; }      // EP is fine: no error
        try { Object o = new ES(); r += (o != null ? 1 : 0); } catch (NoClassDefFoundError e) { r += 10000; }
        try { r += ES.get(); } catch (NoClassDefFoundError e) { r += 100000; }
        return Log.v * 1_000_000 + r;
    }
    static long erroneousIface(int x) {
        Log.sel = x & 1;
        long r = 0;
        if ((x & 2) != 0) { try { r += IE.ie; } catch (ExceptionInInitializerError e) { r += 10; } }
        try { r += CE2.ce2; } catch (ExceptionInInitializerError e) { r += 100; } catch (NoClassDefFoundError e) { r += 200; }
        try { r += CE.ce; } catch (NoClassDefFoundError e) { r += 1000; }
        try { r += CE2.ep; } catch (NoClassDefFoundError e) { r += 10000; }
        if ((x & 4) != 0) r += CE2.ce2;     // escapes (NoClassDefFoundError) when IE failed
        return Log.v * 1_000_000 + r;
    }
    static int uncaughtInit(int x) { Log.sel = x & 1; return IE.ie; }

    // shadowed instance fields
    static class A { int x = 1; long y = 5; int getAX() { return x; } void setAX(int v) { x = v; } }
    static class B extends A { int x = 2; int getBX() { return x; } void setBX(int v) { x = v; } }
    static class C extends B { int x = 3; String y = "c"; int getCX() { return x; } }
    static class D extends B { int z = 4; }
    static long shadow(int v) {
        C c = new C(); D d = new D(); B b = new B();
        c.setAX(v); c.setBX(v + 1); b.setAX(v ^ 7);
        ((A) d).x = v * 3; d.x = v * 5;     // putfield A.x, putfield D.x (= B.x)
        long r = c.getAX() + 10L * c.getBX() + 100L * c.getCX() + 1000L * ((B) c).x + 10000L * ((A) c).x + c.x
               + 7L * d.x + 11L * ((A) d).x + 13L * d.getBX() + 17L * d.getAX() + d.z + 19L * b.getAX() + 23L * b.x
               + ((A) c).y + c.y.length();
        return r;
    }

    // an enum that declares fields called "name" and "ordinal" (shadowing java.lang.Enum's private fields)
    enum Col { RED("rr", 7), GREEN("g", 8), BLUE("", 9);
        final String name; final int ordinal;
        Col(String n, int o) { this.name = n; this.ordinal = o; } }
    static int enumFields(int i) {
        Col c = Col.values()[(i & 0x7fffffff) % 3];
        return c.name().length() * 1000 + c.name.length() * 100 + c.ordinal() * 10 + c.ordinal;
    }
}
