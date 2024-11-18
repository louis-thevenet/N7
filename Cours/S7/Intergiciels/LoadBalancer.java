import java.util.Random;

public class LoadBalancer {
  static String hosts[] = { "host1", "host2" };
  static int ports[] = { 8081, 8082 };
  static int nbHost = 2;
  static Random rand = new Random();

  static void receive() {
    var server = rand.nextInt(nbHost);

  }

}
