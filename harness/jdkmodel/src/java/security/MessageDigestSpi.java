/*
 * rocq-jvm model of java.security.MessageDigestSpi (clean-room, Apache-2.0): the service provider
 * interface of MessageDigest. engineUpdate(ByteBuffer) is not modelled (STUCK).
 */
package java.security;

public abstract class MessageDigestSpi {
    public MessageDigestSpi() {
    }

    protected int engineGetDigestLength() {
        return 0;
    }

    protected abstract void engineUpdate(byte input);

    protected abstract void engineUpdate(byte[] input, int offset, int len);

    protected void engineUpdate(java.nio.ByteBuffer input) {
        throw ModelStuckSec.unsupported("MessageDigestSpi.engineUpdate(ByteBuffer)");
    }

    protected abstract byte[] engineDigest();

    protected int engineDigest(byte[] buf, int offset, int len) throws DigestException {
        throw ModelStuckSec.unsupported("MessageDigestSpi.engineDigest(byte[], int, int)");
    }

    protected abstract void engineReset();

    public Object clone() throws CloneNotSupportedException {
        throw ModelStuckSec.unsupported("MessageDigestSpi.clone");
    }
}
