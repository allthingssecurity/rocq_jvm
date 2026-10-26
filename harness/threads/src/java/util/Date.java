/*
 * rocq-jvm model of java.util.Date (clean-room, Apache-2.0): only the millisecond value, as
 * needed by Condition.awaitUntil. Date() reads System.currentTimeMillis, which in the machine
 * counts from the start of the run (the epoch is not modelled), so only differences of such values
 * agree with HotSpot. Not modelled (no such method in the model, STUCK): the calendar fields and
 * their deprecated accessors, parse, toString / toGMTString / toLocaleString (time zones),
 * from / toInstant, serialization.
 */
package java.util;

public class Date implements java.io.Serializable, Cloneable, Comparable<Date> {
    private static final long serialVersionUID = 7523967970034938905L;

    private transient long fastTime;

    public Date() {
        this(System.currentTimeMillis());
    }

    public Date(long date) {
        fastTime = date;
    }

    public Object clone() {
        Date d = null;
        try {
            d = (Date) super.clone();
        } catch (CloneNotSupportedException e) {
        }
        return d;
    }

    public long getTime() {
        return fastTime;
    }

    public void setTime(long time) {
        fastTime = time;
    }

    public boolean before(Date when) {
        return getMillisOf(this) < getMillisOf(when);
    }

    public boolean after(Date when) {
        return getMillisOf(this) > getMillisOf(when);
    }

    public boolean equals(Object obj) {
        return obj instanceof Date && getTime() == ((Date) obj).getTime();
    }

    static final long getMillisOf(Date date) {
        if (date == null) throw new NullPointerException("Cannot invoke \"Object.getClass()\" because \"date\" is null");
        if (date.getClass() != Date.class) {
            return date.getTime();
        }
        return date.fastTime;
    }

    public int compareTo(Date anotherDate) {
        return Long.compare(getMillisOf(this), getMillisOf(anotherDate));
    }

    public int hashCode() {
        long ht = this.getTime();
        return (int) ht ^ (int) (ht >> 32);
    }

    public String toString() {
        throw unsupported("Date.toString: time zones are not modelled");
    }

    private static native RuntimeException unsupported(String what);
}
