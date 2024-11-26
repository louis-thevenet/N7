import java.util.Random;

public class Main {

    // Crée un producteur-consommateur à 4 places
    private static ProdCons<Integer> prodcons = new ProdCons<>(4);
    
    public static void main(String args []) {
        // Crée trois producteurs
        for (int i = 0; i < 3; i++) {
            new Thread(new Producteur(i)).start();
        }
        // Crée deux consommateurs
        for (int i = 0; i < 2; i++) {
            new Thread(new Consommateur(i)).start();
        }
    }

    static class Producteur implements Runnable {
        private int id;
        public Producteur(int id) { this.id = id; }
        public void run() {
            try {
                Random rand = new Random();
                for (int i = 0; i < 10; i++) {
                    int val = Math.abs(rand.nextInt()) % 100;
                    System.out.println("Prod " + id + ",  dépôt : " + val); 
                    prodcons.deposer(val);
                    Thread.sleep(Math.abs(rand.nextInt()) % 1000); // max 1 sec
                }
            }  catch (InterruptedException e) {}
        }
    }
    static class Consommateur implements Runnable {
        private int id;
        public Consommateur(int id) { this.id = id; }
        public void run() {
            try {
                Random rand = new Random();
                while (true) {
                    int val = prodcons.retirer();
                    System.out.println("Conso " + id + ", obtenu : " + val); 
                    Thread.sleep(Math.abs(rand.nextInt()) % 1000); // max 1 sec
                }
            }  catch (InterruptedException e) {}
        }
    }
}
