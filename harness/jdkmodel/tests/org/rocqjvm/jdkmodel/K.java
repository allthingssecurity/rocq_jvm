package org.rocqjvm.jdkmodel;

/** Test key: equality by id, hash code chosen by the test (collisions on demand). */
final class K {
    final int id;
    final int h;

    K(int id, int h) {
        this.id = id;
        this.h = h;
    }

    public int hashCode() {
        return h;
    }

    public boolean equals(Object o) {
        return o instanceof K && ((K) o).id == id;
    }

    public String toString() {
        return "K" + id;
    }
}
