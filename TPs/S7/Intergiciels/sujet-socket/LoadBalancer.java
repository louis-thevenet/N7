import java.io.DataOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.LineNumberReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintStream;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.Random;

class LoadBalancer implements Runnable {
  static String hosts[] = { "localhost", "localhost" };
  static int ports[] = { 8081, 8082 };
  static int nbHosts = 2;
  static Random rand = new Random();
  static Socket s;
  static DataOutputStream serverDataStreams[];

  public LoadBalancer(Socket s) {
    this.s = s;
  }

  public static void main(String[] args) throws IOException {
    ServerSocket s = new ServerSocket(8080);
    serverDataStreams = new DataOutputStream[nbHosts];

    for (int i = 0; i < nbHosts; i++) {
      serverDataStreams[i] = new DataOutputStream(new Socket(hosts[i], ports[i]).getOutputStream());
    }

    while (true) {
      new Thread(new LoadBalancer(s.accept())).start();
    }
  }

  @Override
  public void run() {
    try {
      InputStreamReader clientInput = new InputStreamReader(s.getInputStream());
      PrintStream clientOutput = new PrintStream(s.getOutputStream());
      String rq = new LineNumberReader(clientInput).readLine();
      System.out.println(rq);

      int serverIndex = rand.nextInt(nbHosts);
      System.out.println("Sending to " + hosts[serverIndex] + ":" + ports[serverIndex]);

      // Transmet au serveur
      var web = new Socket(hosts[serverIndex], ports[serverIndex]);
      var webInput = new DataOutputStream(web.getOutputStream());
      webInput.write(rq.getBytes());
      webInput.writeBytes("\n");

      // Reçoit du serveur
      InputStreamReader webOutput = new InputStreamReader(web.getInputStream());
      System.out.println("Lecture du serveur");
      char[] buffer = new char[1024];
      var byteRead = webOutput.read(buffer, 0, 1024);
      System.out.println("Lu : " + byteRead);
      webOutput.close();

      // Envoie au client
      clientOutput.println(buffer);
      clientOutput.flush();

      clientOutput.close();
      s.close();
    } catch (IOException ex) {
      ex.printStackTrace();
    }
  }

}
