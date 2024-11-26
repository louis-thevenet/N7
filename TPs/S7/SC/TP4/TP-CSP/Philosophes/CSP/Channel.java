package CSP;

import org.jcsp.lang.*;

/** A communication channel with an identification.
 *  This class is generic with regard to the id.
 *  A channel supports `read` and `write` of Object.
 */
public class Channel<T> {

    private T id;
    private Any2OneChannel c;

    public Channel(T id) {
        this.c = org.jcsp.lang.Channel.any2one();
        this.id = id;
    }

    public T getId() { return id; }

    /* needed by Alt. */
    protected AltingChannelInput in() {
        return c.in();
    }

    protected SharedChannelOutput out() {
        return c.out();
    }

    public Object read() {
        return c.in().read();
    }

    public void write(Object o) {
        c.out().write(o);
    }

    /** Returns whether there is data pending on this channel: read will not block. */
    public boolean pending() {
        return c.in().pending();
    }
}
