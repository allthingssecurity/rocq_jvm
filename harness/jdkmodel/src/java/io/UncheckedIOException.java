/* rocq-jvm model of java.io.UncheckedIOException (clean-room, Apache-2.0). */
package java.io;

import java.util.Objects;

public class UncheckedIOException extends RuntimeException {
    private static final long serialVersionUID = -8134305061645241065L;

    public UncheckedIOException(String message, IOException cause) {
        super(message, Objects.requireNonNull(cause));
    }

    public UncheckedIOException(IOException cause) {
        super(Objects.requireNonNull(cause));
    }

    @Override
    public IOException getCause() {
        return (IOException) super.getCause();
    }
}
