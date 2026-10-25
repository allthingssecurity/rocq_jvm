package org.rocqjvm.corpus7;

import org.rocqjvm.corpus7.p1.PP;
import org.rocqjvm.corpus7.p1.PR;
import org.rocqjvm.corpus7.p1.PS;
import org.rocqjvm.corpus7.p2.PQ;
import org.rocqjvm.corpus7.p2.PT;

/** Corpus 7: method selection (JVMS 5.4.3.3, 5.4.3.4, 5.4.5, 5.4.6, invokespecial).
 *  Private methods (selected as resolved, also through nestmates and interfaces), maximally-specific
 *  default methods, superclass methods over defaults, package-private overriding across packages,
 *  super calls; and, through classes recompiled separately (harness/corpus7/build.sh), the
 *  IncompatibleClassChangeError / AbstractMethodError / NoSuchMethodError / NoSuchFieldError cases. */
public class Sel {
    static class PA { private int f() { return 1; } int g() { return f(); } private static int sf() { return 11; } static int sg() { return sf(); } }
    static class PB extends PA { int f() { return 2; } }
    static class PC extends PA { private int f() { return 3; } int h() { return f(); } private static int sf() { return 13; } static int sh() { return sf(); } }
    static class PD extends PC { public int f() { return 4; } }
    static int privates(int x) {
        PA a = (x & 1) != 0 ? new PB() : (x & 2) != 0 ? new PC() : new PD();
        int r = a.g() * 100;
        if (a instanceof PC) r += ((PC) a).h() * 10;
        if (a instanceof PB) r += ((PB) a).f() * 10;
        if (a instanceof PD) r += ((PD) a).f() * 1000;
        return r + PA.sg() + PC.sh();
    }

    static class Outer {
        private int p() { return 10; }
        private int q;
        class In { int z() { return p() + q; } void set(int v) { q = v; } }
        static class SIn { int w(Outer o) { return o.p() * 2; } }
    }
    static class Outer2 extends Outer { int p() { return 20; } }
    static int nestmates(int x) {
        Outer o = (x & 1) != 0 ? new Outer2() : new Outer();
        Outer.In in = o.new In();
        in.set(x & 0xff);
        return in.z() + new Outer.SIn().w(o) + ((x & 1) != 0 ? ((Outer2) o).p() * 100 : 0);
    }

    interface IP { private int pp() { return 7; } default int q() { return pp(); } }
    static class CP implements IP { public int pp() { return 8; } }
    static class CP2 implements IP { public int pp() { return 9; } public int q() { return IP.super.q() + 100; } }
    static int ifacePrivate(int x) {
        IP i = (x & 1) != 0 ? new CP() : new CP2();
        return i.q() * 10 + (i instanceof CP ? ((CP) i).pp() : ((CP2) i).pp());
    }

    interface DA { default int m() { return 1; } default int n() { return 10; } }
    interface DB extends DA { default int m() { return 2; } }
    interface DX { default int n() { return 20; } }
    static class DC implements DA, DB { }
    static class DD extends DC implements DA { }
    static class DE { public int m() { return 5; } }
    static class DF extends DE implements DB { }
    static class DG implements DA, DX { public int n() { return DA.super.n() + DX.super.n() + 100; } }
    abstract static class DH implements DB { public abstract int m(); }
    static class DI extends DH { public int m() { return 9 + super.n(); } }
    static int defaults(int x) {
        DA a;
        switch ((x & 0x7fffffff) % 5) {
            case 0: a = new DC(); break;
            case 1: a = new DD(); break;
            case 2: a = new DF(); break;
            case 3: a = new DG(); break;
            default: a = new DI(); break;
        }
        int r = a.m() * 1000 + a.n();
        if (a instanceof DE) r += ((DE) a).m() * 100000;
        if (a instanceof DX) r += ((DX) a).n() * 1000000;
        return r;
    }

    static int packages(int x) {
        PP o;
        switch ((x & 0x7fffffff) % 5) {
            case 0: o = new PP(); break;
            case 1: o = new PQ(); break;    // p2.PQ.pk does not override p1.PP.pk
            case 2: o = new PR(); break;    // p1.PR.pk overrides p1.PP.pk (same package)
            case 3: o = new PS(); break;    // p1.PS.pk (public) overrides
            default: o = new PT(); break;   // p2.PT.pk overrides PP.pk through PS.pk (JVMS 5.4.5 (b))
        }
        return o.callPk() * 100 + o.callPub();
    }

    static class SupA { int v() { return 1; } int w() { return 100; } }
    static class SupB extends SupA { int v() { return 2 + super.v(); } }
    static class SupC extends SupB { int v() { return 4 + super.v(); } int w() { return super.w() + 1; } }
    static int superCalls(int x) {
        SupA a = (x & 1) != 0 ? new SupC() : new SupB();
        return a.v() * 1000 + a.w();
    }

    // classes changed after the caller was compiled (build.sh, stage 1 vs stage 2)
    static int changed(int x) {
        switch ((x & 0x7fffffff) % 12) {
            case 0: return new XC().x();               // XA and XB both supply x(): ICCE
            case 1: return ((XA) new XC()).x();        // invokeinterface: ICCE
            case 2: return new YC().y();               // y() became abstract: AME
            case 3: return new ZC().z();               // ZB re-abstracts z(): AME
            case 4: return SX.s();                     // s() is no longer static: ICCE
            case 5: return SX.f;                       // f is no longer static: ICCE
            case 6: return new SX().gone();            // method removed: NoSuchMethodError
            case 7: return new SX().g;                 // field removed: NoSuchFieldError
            case 8: { SX n = (x & 0x10000) != 0 ? null : new SX(); return n.gone(); }  // NoSuchMethodError before the null check
            case 9: { SX n = (x & 0x10000) != 0 ? null : new SX(); return n.g; }       // NoSuchFieldError before the null check
            case 10: { XC n = null; return n.ok(); }                                    // NullPointerException
            default: return new XC().ok() + new WC().w(); // WA gained a default that WC's superclass overrides
        }
    }
    static int changedCaught(int x) {
        try { return changed(x); }
        catch (AbstractMethodError e) { return -1; }
        catch (NoSuchMethodError e) { return -3; }
        catch (NoSuchFieldError e) { return -4; }
        catch (IncompatibleClassChangeError e) { return -2; }
    }
}
