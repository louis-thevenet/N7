import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Collection;
import java.util.HashMap;

public class Exo2 {

  public static void main(String args[]) throws NoSuchMethodException, SecurityException, Throwable {

    Collection<Integer> list = new ArrayList<Integer>();
    list.addAll(List.of(2, 3, 5, 7));
    list.remove((Object) (5));
    System.out.println(list);

    Protection protection_list = new Protection(list, new ArrayList<String>() {
      {
        add("add");
      }
    });

    System.out.println("Protected list: " +
        protection_list.invoke(protection_list, list.getClass().getMethod("toString"), null));
    // protection_list.invoke(protection_list, list.getClass().getMethod("add",
    // Object.class), new Object[] { 11 });

    // System.out.println(
    // protection_list.invoke(protection_list,
    // list.getClass().getMethod("toString"), null));

    Protection map = new Protection(

        new HashMap<Integer, String>(),
        new ArrayList<String>() {
          {
            add("put");
            add("clear");
          }
        });

    System.out.println("Protected map: " +
        map.invoke(map, HashMap.class.getMethod("toString"), null));
    map.invoke(map, HashMap.class.getMethod("put", Object.class, Object.class),
        new Object[] { 1, "one" });

  }
}
