package CSP;

/** A communication channel with a guard.
 *  The guard is a Predicate, used in the Alternative conditions.
 *  A guarded channel supports `read` and `write` of Object.
 */
public class GuardedChannel<T> {

    private Channel<T> channel;
    private Predicate guard;

    public GuardedChannel(Channel<T> channel, Predicate guard) {
        this.channel = channel;
        this.guard = guard;
    }

    public GuardedChannel(Channel<T> channel) {
        this.channel = channel;
        this.guard = Predicate::True;
    }
    
    public Channel<T> getChannel() { return channel; }
    public Predicate getGuard() { return guard; }

    public Object read() { return this.channel.read(); }
    public void write(Object o) { this.channel.write(o); }
    public boolean pending() { return this.channel.pending(); }
}
