import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

public class exo1 {

  public static void main(String args[]) {
    Collection<Integer> list = new ArrayList<Integer>();
    list.addAll(List.of(2, 3, 5, 7));
    list.remove(5);
    System.out.println(list);

    Collection<Integer> list2 = Collections.unmodifiableCollection(list);
    // list2.remove(3); // throws UnsupportedOperationException

  }

}
