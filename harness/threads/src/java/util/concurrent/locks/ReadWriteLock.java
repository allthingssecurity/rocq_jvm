/* rocq-jvm model of java.util.concurrent.locks.ReadWriteLock (clean-room, Apache-2.0): the interface. */
package java.util.concurrent.locks;

public interface ReadWriteLock {
    Lock readLock();
    Lock writeLock();
}
