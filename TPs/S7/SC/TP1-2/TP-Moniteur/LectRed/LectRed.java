// Time-stamp: <28 oct 2022 10:20 queinnec@enseeiht.fr>

public interface LectRed {

    public void demanderLecture() throws InterruptedException;
    public void terminerLecture() throws InterruptedException;
    public void demanderEcriture() throws InterruptedException;
    public void terminerEcriture() throws InterruptedException;
    public String nomStrategie();
}
