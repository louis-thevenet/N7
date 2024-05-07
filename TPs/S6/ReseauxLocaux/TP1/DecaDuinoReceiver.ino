// DecaDuinoReceiver
// Ce croquis est un exemple d'utilisation de la librairie DecaDuino
// Il permet de recevoir un message quelconque envoyé par UWB.
// Il écrit le contenu des octets reçus en HEX
// Il peut-être utilisé comme un sniffer de trames. 
// by Adrien van den Bossche <vandenbo@univ-tlse2.fr>
// Ce croquis fait partir du projet DecaDuino (cf. fichier DecaDuino LICENCE)

#include <SPI.h>
#include <DecaDuino.h>

#define MAX_FRAME_LEN 120
//#define MY_ADDR 32 // Mon adresse

DecaDuino decaduino;  //Interface radio UWB
uint8_t rxData[MAX_FRAME_LEN];  //buffer des données reçues (tableau d'octets)
uint16_t rxLen; // nombre d'octets reçus, <= MAX_FRAME_LEN
uint8_t rxNb; // nombre de trames modulo 255


void setup()
{
  //Sélection de la LED interne connectée au pin 13 de la carte
  pinMode(13, OUTPUT); 
  Serial.begin(115200); // Init Serial port speed
  SPI.setSCK(14); // Set SPI clock pin (pin 14 on DecaWiNo board)

  // Initialisation de DecaDuino
  if ( !decaduino.init() ) {
    // LED 13 clignotte si init échoue
    Serial.println("decaduino init failed");
    while(1) { digitalWrite(13, HIGH); delay(50); digitalWrite(13, LOW); delay(50); }
  }
  
  // Initialisation du buffer de reception avec rxData, 
  // et de la variable où sera enregistré le nombre d'octets reçus.
  decaduino.setRxBuffer(rxData, &rxLen);
  // Lancement de l'écoute pour la réception d'une trame.
  decaduino.plmeRxEnableRequest();
  // On met a zéro le nombre de trames reçues
  rxNb = 0;
}


void loop()
{  
  // Si un message a été reçu, l'afficher sur le port série 
  // et repasser en écoute
  if ( decaduino.rxFrameAvailable() ) {
    digitalWrite(13, HIGH);
    Serial.print(" rxNb |"); 
    Serial.print(++rxNb); 
    Serial.print("| ");
    
    Serial.print(" rxLen |"); 
    Serial.print(rxLen);
    Serial.print("| ");
    
    Serial.print(" DATA: |");
    for (int i=0; i<rxLen; i++) {
      Serial.print(rxData[i], HEX);
    }
    Serial.print("|");
    Serial.println();
   // on repasse en écoute
    decaduino.plmeRxEnableRequest();
    digitalWrite(13, LOW);
  }
}


