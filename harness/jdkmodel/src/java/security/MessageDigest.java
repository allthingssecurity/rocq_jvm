/*
 * rocq-jvm model of java.security.MessageDigest (clean-room, Apache-2.0), from the Javadoc and the
 * algorithms of the default JDK 21 configuration (the SUN provider): MD5 (RFC 1321), SHA-1, SHA-224,
 * SHA-256, SHA-384, SHA-512, SHA-512/224, SHA-512/256 (FIPS 180-4), looked up by their names and
 * aliases (case-insensitive); the object is a MessageDigest$Delegate$CloneableDelegate as in the JDK,
 * getAlgorithm is the name asked for, toString "<name> Message Digest from SUN, <initialized>|<in
 * progress>\n"; the argument checks and messages of update/digest, isEqual, clone.
 * Not modelled (STUCK): MD2 and SHA-3, OID names, getProvider, explicit providers, ByteBuffer input.
 * A name no provider offers: NoSuchAlgorithmException "<name> MessageDigest not available".
 */
package java.security;

public abstract class MessageDigest extends MessageDigestSpi {
    private static final int INITIAL = 0;
    private static final int IN_PROGRESS = 1;

    private final String algorithm;
    private int state = INITIAL;

    protected MessageDigest(String algorithm) {
        this.algorithm = algorithm;
    }

    private static final String[][] NAMES = {
        {"MD5", "MD5"}, {"SHA-1", "SHA-1"}, {"SHA", "SHA-1"}, {"SHA1", "SHA-1"},
        {"SHA-224", "SHA-224"}, {"SHA224", "SHA-224"}, {"SHA-256", "SHA-256"}, {"SHA256", "SHA-256"},
        {"SHA-384", "SHA-384"}, {"SHA384", "SHA-384"}, {"SHA-512", "SHA-512"}, {"SHA512", "SHA-512"},
        {"SHA-512/224", "SHA-512/224"}, {"SHA512/224", "SHA-512/224"}, {"SHA-512/256", "SHA-512/256"},
        {"SHA512/256", "SHA-512/256"}};

    private static final String[] OTHER = {"MD2", "SHA3-224", "SHA3-256", "SHA3-384", "SHA3-512"};

    public static MessageDigest getInstance(String algorithm) throws NoSuchAlgorithmException {
        if (algorithm == null) throw new NullPointerException("null algorithm name");
        for (String[] n : NAMES) if (n[0].equalsIgnoreCase(algorithm)) return new Delegate.CloneableDelegate(new ModelDigest(n[1]), algorithm);
        for (String n : OTHER) if (n.equalsIgnoreCase(algorithm)) throw ModelStuckSec.unsupported("MessageDigest " + n);
        String oid = algorithm.regionMatches(true, 0, "OID.", 0, 4) ? algorithm.substring(4) : algorithm;
        boolean dotted = !oid.isEmpty();
        for (int i = 0; i < oid.length(); i++) {
            char c = oid.charAt(i);
            if (!(c == '.' || (c >= '0' && c <= '9'))) dotted = false;
        }
        if (dotted) throw ModelStuckSec.unsupported("MessageDigest: an OID name");
        throw new NoSuchAlgorithmException(algorithm + " MessageDigest not available");
    }

    public static MessageDigest getInstance(String algorithm, String provider) throws NoSuchAlgorithmException, NoSuchProviderException {
        throw ModelStuckSec.unsupported("MessageDigest.getInstance with a provider");
    }

    public static MessageDigest getInstance(String algorithm, Provider provider) throws NoSuchAlgorithmException {
        throw ModelStuckSec.unsupported("MessageDigest.getInstance with a provider");
    }

    public final Provider getProvider() {
        throw ModelStuckSec.unsupported("MessageDigest.getProvider");
    }

    public void update(byte input) {
        engineUpdate(input);
        state = IN_PROGRESS;
    }

    public void update(byte[] input, int offset, int len) {
        if (input == null) throw new IllegalArgumentException("No input buffer given");
        if (input.length - offset < len) throw new IllegalArgumentException("Input buffer too short");
        engineUpdate(input, offset, len);
        state = IN_PROGRESS;
    }

    public void update(byte[] input) {
        if (input == null) throw new NullPointerException("Cannot read the array length because \"input\" is null");
        engineUpdate(input, 0, input.length);
        state = IN_PROGRESS;
    }

    public final void update(java.nio.ByteBuffer input) {
        throw ModelStuckSec.unsupported("MessageDigest.update(ByteBuffer)");
    }

    public byte[] digest() {
        byte[] result = engineDigest();
        state = INITIAL;
        return result;
    }

    public int digest(byte[] buf, int offset, int len) throws DigestException {
        if (buf == null) throw new IllegalArgumentException("No output buffer given");
        if (buf.length - offset < len) throw new IllegalArgumentException("Output buffer too small for specified offset and length");
        int numBytes = engineDigest(buf, offset, len);
        state = INITIAL;
        return numBytes;
    }

    public byte[] digest(byte[] input) {
        update(input);
        return digest();
    }

    public String toString() {
        return algorithm + " Message Digest from SUN, " + (state == INITIAL ? "<initialized>" : "<in progress>") + "\n";
    }

    public static boolean isEqual(byte[] digesta, byte[] digestb) {
        if (digesta == digestb) return true;
        if (digesta == null || digestb == null) return false;
        int lenA = digesta.length;
        int lenB = digestb.length;
        if (lenB == 0) return lenA == 0;
        int result = lenA - lenB;
        for (int i = 0; i < lenA; i++) {
            int indexB = ((i - lenB) >>> 31) * i;
            result |= digesta[i] ^ digestb[indexB];
        }
        return result == 0;
    }

    public void reset() {
        engineReset();
        state = INITIAL;
    }

    public final String getAlgorithm() {
        return algorithm;
    }

    public final int getDigestLength() {
        return engineGetDigestLength();
    }

    public Object clone() throws CloneNotSupportedException {
        throw new CloneNotSupportedException();
    }

    void copyState(MessageDigest from) {
        state = from.state;
    }

    /** The JDK's wrapper of a provider's MessageDigestSpi (the SUN digests are Cloneable). */
    static class Delegate extends MessageDigest {
        final ModelDigest spi;

        Delegate(ModelDigest spi, String algorithm) {
            super(algorithm);
            this.spi = spi;
        }

        protected int engineGetDigestLength() {
            return spi.length;
        }

        protected void engineUpdate(byte input) {
            spi.update(input);
        }

        protected void engineUpdate(byte[] input, int offset, int len) {
            spi.update(input, offset, len);
        }

        protected byte[] engineDigest() {
            return spi.digest();
        }

        protected int engineDigest(byte[] buf, int offset, int len) throws DigestException {
            return spi.digest(buf, offset, len);
        }

        protected void engineReset() {
            spi.reset();
        }

        static final class CloneableDelegate extends Delegate implements Cloneable {
            CloneableDelegate(ModelDigest spi, String algorithm) {
                super(spi, algorithm);
            }

            public Object clone() throws CloneNotSupportedException {
                CloneableDelegate c = new CloneableDelegate(spi.copy(), getAlgorithm());
                c.copyState(this);
                return c;
            }
        }
    }
}
