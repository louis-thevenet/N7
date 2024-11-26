package CSP;

import org.jcsp.lang.Guard;
import java.util.stream.Collectors;
import java.util.Arrays;
import java.util.List;

/** An alternative between a set of GuardedChannel.
 *  An alternative is created with a set of GuardedChannel, i.e a set of couples (Channel,Predicate). A shortcut constructor accepts a set of Channel, which implies Predicate::True for all the channels.
 * An alternative supports a `select` operation. It returns the id of a channel for which the Predicate is true and a `read` operation is enabled (possible without blocking). `select` blocks while none exists.
 */
public class Alternative<T> {

    private List<GuardedChannel<T>> channels;
    private org.jcsp.lang.Alternative alt;

    /** Create an alternative for a set of guarded channels.
     * Only the channels whose predicate is true are tested in select.
     */
    @SafeVarargs
    public Alternative(GuardedChannel<T>... channels) {
        this.channels = Arrays.asList(channels);
        var inchans = Arrays.stream(channels).map(g -> g.getChannel().in()).toArray(Guard[]::new);
        this.alt = new org.jcsp.lang.Alternative(inchans);
    }

    /** Create an alternative for a set of channels.
     *  The predicate is true for all the channels (always tested).
     */
    @SafeVarargs
    public Alternative(Channel<T>... channels) {
        this.channels = Arrays.stream(channels).map(GuardedChannel<T>::new).collect(Collectors.toList());
        var inchans = Arrays.stream(channels).map(Channel::in).toArray(Guard[]::new);
        this.alt = new org.jcsp.lang.Alternative(inchans);
    }

    /** Return the id of a channel for which the Predicate is true and a
     * `read` operation is enabled (read is possible without waiting).
     * Block while none exists.
     * If more than one is ready, the choice is arbitrary.
     * The conditions are evaluated once at the beginning of `select`. */
    public T select() {
        boolean condition[] = new boolean[channels.size()];
        for (int i = 0; i < condition.length; i++) {
            condition[i] = channels.get(i).getGuard().test();
        }
        int index = alt.select(condition);
        return channels.get(index).getChannel().getId();
    }

    /** Return the id of a channel for which the Predicate is true and a
     * `read` operation is enabled (read is possible without waiting).
     * Block while none exists.
     * If more than one is ready, the one with the lowest index is selected.
     * The conditions are evaluated once at the beginning of `select`. */
    public T priSelect() {
        boolean condition[] = new boolean[channels.size()];
        for (int i = 0; i < condition.length; i++) {
            condition[i] = channels.get(i).getGuard().test();
        }
        int index = alt.priSelect(condition);
        return channels.get(index).getChannel().getId();
    }
}
