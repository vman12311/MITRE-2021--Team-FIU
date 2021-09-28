/*
 * 2021 Collegiate eCTF
 * SCEWL Bus Controller implementation
 * Ben Janis
 *
 * (c) 2021 The MITRE Corporation
 *
 * This source file is part of an example system for MITRE's 2021 Embedded System CTF (eCTF).
 * This code is being provided only for educational purposes for the 2021 MITRE eCTF competition,
 * and may not meet MITRE standards for quality. Use this code at your own risk!
 */

#include "controller.h"
#include <tinycrypt/constants.h>
#include <tinycrypt/utils.h>
#include <tinycrypt/cbc_mode.h>
#include <tinycrypt/hmac.h>
#include <tinycrypt/sha256.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h>

// max buffer values
static const int maxMsgLength = 16456;
static const int maxMsgRecLength = 16528;

//functions for implementing an integer to ascii conversion
void swap(char *x, char *y);
char* reverse(char *buffer, int i, int j);
char* itoa(unsigned long value, char* buffer, int base);

//temporary keys
uint8_t key[16] = { "0123456789abcdef"};
uint8_t DT_hmac_key[16] = { "0123456789abcdef"};
uint8_t DT_recv_hmac_key[16] = { "0123456789abcdef"};
uint8_t BC_hmac_key[16] = { "0123456789abcdef"};
uint8_t iv[16] = { "0123456789abcdef"};
uint8_t badKey[16] = { "0123456789abcdef"};


uint8_t DTdigestArray[16][32]; //Saved Direct Transmissions MACs
uint8_t BCdigestArray[16][32]; //Saved Broadcasts MACs

unsigned long tenDigitSerial = 0;
unsigned long msgCounter = 1;

#define send_str(M) send_msg(RAD_INTF, SCEWL_ID, SCEWL_FAA_ID, strlen(M), M)
#define BLOCK_SIZE 16

// message buffer
char buf[SCEWL_MAX_DATA_SZ];

int registered = 0;


int read_msg(intf_t *intf, char *data, scewl_id_t *src_id, scewl_id_t *tgt_id,
             size_t n, int blocking) {

  scewl_hdr_t hdr;
  int read, max;

  // clear buffer and header
  memset(&hdr, 0, sizeof(hdr));
  memset(data, 0, n);


  // find header start
  do {
    hdr.magicC = 0;

    if (intf_read(intf, (char *)&hdr.magicS, 1, blocking) == INTF_NO_DATA) {
      send_str("no data");
      return SCEWL_NO_MSG;
    }

    // check for SC
    if (hdr.magicS == 'S') {
      do {
        if (intf_read(intf, (char *)&hdr.magicC, 1, blocking) == INTF_NO_DATA) {
          return SCEWL_NO_MSG;
        }
      } while (hdr.magicC == 'S'); // in case of multiple 'S's in a row
    }
  } while (hdr.magicS != 'S' && hdr.magicC != 'C');

  // read rest of header
  read = intf_read(intf, (char *)&hdr + 2, sizeof(scewl_hdr_t) - 2, blocking);
  if(read == INTF_NO_DATA) {
    return SCEWL_NO_MSG;
  }

  // unpack header
  *src_id = hdr.src_id;
  *tgt_id = hdr.tgt_id;

  // read body
  max = hdr.len < n ? hdr.len : n;
  read = intf_read(intf, data, max, blocking);

  // throw away rest of message if too long
  for (int i = 0; hdr.len > n && i < hdr.len - n; i++) {
    intf_readb(intf, 0);
  }

  // report if not blocking and full message not received
  if(read == INTF_NO_DATA || read < max) {
    return SCEWL_NO_MSG;
  }

  return max;
}

int send_msg(intf_t *intf, scewl_id_t src_id, scewl_id_t tgt_id, uint16_t len, char *data) {
  scewl_hdr_t hdr;

  // pack header
  hdr.magicS  = 'S';
  hdr.magicC  = 'C';
  hdr.src_id = src_id;
  hdr.tgt_id = tgt_id;
  hdr.len    = len;

  // send header
  intf_write(intf, (char *)&hdr, sizeof(scewl_hdr_t));

  // send body
  intf_write(intf, data, len);

  return SCEWL_OK;
}



int handle_scewl_recv(char* data, scewl_id_t src_id, uint16_t len) {

  // Check is message exceeds max length and discard if so
  if (len > maxMsgRecLength) {
    memset(data, 0, len);
    return 0;
  }
  
  // Copy data into 2 new arrays - 1 for encypted text and 1 for HMAC
  uint16_t n = len - 32;
  uint8_t encrypted[n];
  uint8_t hmac[32];
  int i;
  for (i = 0; i < n; i++) encrypted[i] = data[i];
  for (i = n; i < n + 32; i++) hmac[i - n] = data[i];

  // Calculate HMAC based on encryted text
  struct tc_hmac_state_struct h;
  uint8_t digest[32];
  (void)memset(&h, 0x00, sizeof(h));
  (void)tc_hmac_set_key(&h, DT_recv_hmac_key, sizeof(DT_recv_hmac_key));
  (void)tc_hmac_init(&h);
  (void)tc_hmac_update(&h, (char *)encrypted, n);
  (void)tc_hmac_final(digest, 32, &h);

  if (!_compare(digest, hmac, 32)) //Check to determine if HMAC calulated matches the one sent
  {
      // Check if MAC matches previously recieved MACs. Ignore if the same.
      for (int i = 0; i < 16; i++) {
        if (!_compare(digest, DTdigestArray[i], 32)) {
          return 0;
          }
      } 

      //store newly recieved MAC in array
      for (int j = 15; j > 0; j--){
        for (int i = 0; i < 32; i++) DTdigestArray[j][i] = DTdigestArray[j-1][i];
      }
      for (int i = 0; i < 32; i++) DTdigestArray[0][i] = digest[i];      

      uint16_t sizeofDec = n - 16;
      uint8_t decrypted[sizeofDec]; //create decryted text array
      char *p;

      //decrypt text and store in array
      struct tc_aes_key_sched_struct a;
      (void)tc_aes128_set_decrypt_key(&a, key);
      p = &data[16];
      tc_cbc_mode_decrypt(decrypted, len, (uint8_t *)p, len, (uint8_t *)data, &a);

      //remove padding
      for (i = sizeofDec - 1; decrypted[i] == '#'; i--,sizeofDec--) decrypted[i] = '\0';
      sizeofDec -= 10; //discard unique messageID
      
      return send_msg(CPU_INTF, src_id, SCEWL_ID, sizeofDec, (char *)decrypted);
  }
  else
  {
    //disregard message if not authentic
    //send_str("HMAC doesn't match. disgarding message.");
    return 0;
  }  

}

int handle_scewl_send(char* data, scewl_id_t tgt_id, uint16_t len) {
  
  //check if message exceeds buffer length and reduces to message to small length if so
  if (len > maxMsgLength) {
    memset(data + 32, 0, len - 32);
    len = 32;
  } 

  msgCounter++; //increment message counter for unique message ID
  DT_hmac_key[11] = (u_int8_t)(tgt_id % 256); //customize HMAC for specific target SED

  //append message with unique message ID
  char tempAry[10]; 
  char* messageID; 
  messageID = itoa(tenDigitSerial + msgCounter, tempAry, 10);
  for(int i = len; i < len + 10; i++) data[i] = messageID[i-len];
  len += 10; 
  

  //pad message if needed for 16 byte blocks
  if (len % 16 != 0) 
  {
       for (int i = len; i < len + (16 - (len % 16)); i++) data[i] = '#';
       len = len + (16 - (len % 16));
  }

  //randomize initialization vector
  for (int i = 0; i < 16; i++) iv[i] = (rand() % 256);

  //encrypt data AES CBC algo implementation 
  struct tc_aes_key_sched_struct a;
	uint8_t iv_buffer[16];
  uint16_t sizeofEnc = len + 16;
	uint8_t encrypted[sizeofEnc];
  (void)tc_aes128_set_encrypt_key(&a, key);
	(void)memcpy(iv_buffer, iv, 16);
  tc_cbc_mode_encrypt(encrypted, sizeofEnc,
	(uint8_t *)data, len , iv_buffer, &a);

  //calulate HMAC of encryoted data
  struct tc_hmac_state_struct h;
  uint8_t digest[32];
  (void)memset(&h, 0x00, sizeof(h));
  (void)tc_hmac_set_key(&h, DT_hmac_key, sizeof(DT_hmac_key));
  (void)tc_hmac_init(&h);
  (void)tc_hmac_update(&h, (char *)encrypted, sizeofEnc);
  (void)tc_hmac_final(digest, 32, &h);


  //copy ciphertext and HMAC to new array
  uint8_t msg[sizeofEnc + 32];
  int i;
  for (i = 0; i < sizeofEnc; i++) msg[i] = encrypted[i];
  for (i = sizeofEnc; i < sizeofEnc + 32; i++) msg[i] = digest[i - sizeofEnc];

  //send encrypted message
  return send_msg(RAD_INTF, SCEWL_ID, tgt_id, sizeof(msg), (char *)msg);
}


int handle_brdcst_recv(char* data, scewl_id_t src_id, uint16_t len) {

  // Check is message exceeds max length and discard if so
  if (len > maxMsgRecLength) {
    memset(data, 0, len);
    return 0;
  }
  
  // Copy data into 2 new arrays - 1 for encypted text and 1 for HMAC
  uint16_t n = len - 32;
  uint8_t encrypted[n];
  uint8_t hmac[32];
  int i;
  for (i = 0; i < n; i++) encrypted[i] = data[i];
  for (i = n; i < n + 32; i++) hmac[i - n] = data[i];

  // Calculate HMAC based on encryted text
  struct tc_hmac_state_struct h;
  uint8_t digest[32];
  (void)memset(&h, 0x00, sizeof(h));
  (void)tc_hmac_set_key(&h, BC_hmac_key, sizeof(BC_hmac_key));
  (void)tc_hmac_init(&h);
  (void)tc_hmac_update(&h, (char *)encrypted, n);
  (void)tc_hmac_final(digest, 32, &h);

  if (!_compare(digest, hmac, 32)) //Check to determine if HMAC calulated matches the one sent
  {
      // Check if MAC matches previously recieved MACs. Ignore if the same.
      for (int i = 0; i < 16; i++) {
        if (!_compare(digest, BCdigestArray[i], 32)) {
          return 0; 
          }
      } 

      //store newly recieved MAC in array
      for (int j = 15; j > 0; j--){
        for (int i = 0; i < 32; i++) BCdigestArray[j][i] = BCdigestArray[j-1][i];
      }
      for (int i = 0; i < 32; i++) BCdigestArray[0][i] = digest[i];
      
      
      uint16_t sizeofDec = n - 16;
      uint8_t decrypted[sizeofDec]; //create decrypted text array
      char *p;

      //decrypt text and store in array
      struct tc_aes_key_sched_struct a;
      (void)tc_aes128_set_decrypt_key(&a, key);
      p = &data[16];
      tc_cbc_mode_decrypt(decrypted, len, (uint8_t *)p, len, (uint8_t *)data, &a);

      //remove padding
      for (i = sizeofDec - 1; decrypted[i] == '#'; i--,sizeofDec--) decrypted[i] = '\0';
      sizeofDec -= 10; //discard unique messageID
      
      //send message
      return send_msg(CPU_INTF, src_id, SCEWL_BRDCST_ID, sizeofDec, (char *)decrypted);
  }
  else
  {
    //disregard non-authentic messages
    return 0;
  }  
}


int handle_brdcst_send(char *data, uint16_t len) {

  //check if message exceeds buffer length and reduces to message to small length if so
  if (len > maxMsgLength) {
    memset(data + 32, 0, len - 32);
    len = 32;
  } 

  msgCounter++; //increment message counter for unique message ID

  //append message with unique message ID
  char tempAry[10];
  char* messageID;
  messageID = itoa(tenDigitSerial + msgCounter, tempAry, 10);
  for(int i = len; i < len + 10; i++) data[i] = messageID[i-len];
  len += 10;
  
  //pad message if need to fit into 16 byte blocks
  if (len % 16 != 0) 
  {
       for (int i = len; i < len + (16 - (len % 16)); i++) data[i] = '#';
       len = len + (16 - (len % 16));  
  }

  //randomize initialization vector
  for (int i = 0; i < 16; i++) iv[i] = (rand() % 256);
  
  //Encrypt using AES CBC algo
  struct tc_aes_key_sched_struct a;
	uint8_t iv_buffer[16];
  uint16_t sizeofEnc = len + 16;
	uint8_t encrypted[sizeofEnc];
  (void)tc_aes128_set_encrypt_key(&a, key);
	(void)memcpy(iv_buffer, iv, 16);
  tc_cbc_mode_encrypt(encrypted, sizeofEnc,
	(uint8_t *)data, len , iv_buffer, &a);

  //Calulate HMAC of ciphertext
  struct tc_hmac_state_struct h;
  uint8_t digest[32];
  (void)memset(&h, 0x00, sizeof(h));
  (void)tc_hmac_set_key(&h, BC_hmac_key, sizeof(BC_hmac_key));
  (void)tc_hmac_init(&h);
  (void)tc_hmac_update(&h, (char *)encrypted, sizeofEnc);
  (void)tc_hmac_final(digest, 32, &h);


  //copy ciphertext and HMAC to new array
  uint8_t msg[sizeofEnc + 32];
  for (int i = 0; i < sizeofEnc; i++) msg[i] = encrypted[i];
  for (int i = sizeofEnc; i < sizeofEnc + 32; i++) msg[i] = digest[i - sizeofEnc];

  //send message
  return send_msg(RAD_INTF, SCEWL_ID, SCEWL_BRDCST_ID, sizeof(msg), (char *)msg);
}   


int handle_faa_recv(char* data, uint16_t len) {
  return send_msg(CPU_INTF, SCEWL_FAA_ID, SCEWL_ID, len, data);
}


int handle_faa_send(char* data, uint16_t len) {
  return send_msg(RAD_INTF, SCEWL_ID, SCEWL_FAA_ID, len, data);
}


void handle_registration(char* msg) {
  scewl_sss_msg_t *sss_msg = (scewl_sss_msg_t *)msg;
  if (sss_msg->op == SCEWL_SSS_REG && sss_register()) {
    registered = 1;
  } else if (sss_msg->op == SCEWL_SSS_DEREG && sss_deregister()) {
    registered = 0;
  }
}


int sss_register() {
  char msg2[52]; //create message array for server response, large enough to recieve secret keys
  scewl_sss_msg_t msg;
  scewl_id_t src_id, tgt_id;
  int status, len;

  // fill registration message
  msg.dev_id = SCEWL_ID;
  msg.op = SCEWL_SSS_REG;
  msg.passcode = SECRET; //add secret passcode to registration message
  msg.serialNum = DATA1; //add device serial number to registration message
  
  // send registration
  status = send_msg(SSS_INTF, SCEWL_ID, SCEWL_SSS_ID, sizeof(msg), (char *)&msg);
  if (status == SCEWL_ERR) {
    return 0;
  }

  // receive response
  len = read_msg(SSS_INTF, msg2, &src_id, &tgt_id, sizeof(msg2) , 1);

  for (int i = 0; i < 16; i++) {
    key[i] = msg2[4 + i]; //get AES key from server response
    DT_hmac_key[i] = msg2[20 + i]; //get HMAC key from server response
    BC_hmac_key[i] = msg2[20 + i]; //get HMAC key from server response
    iv[i] = msg2[36 + i]; //get initialization vector from server response
  }
  memcpy(DT_recv_hmac_key, DT_hmac_key,16);
  DT_recv_hmac_key[11] = (u_int8_t)(SCEWL_ID % 256); //personalize direct transmission key based on provisoned ID
  tenDigitSerial = DATA1; //set serial equal to provisioned registration number 
  while (tenDigitSerial < 1000000000) tenDigitSerial *= 2; //increment if less than 10 digits


  // notify CPU of response
  status = send_msg(CPU_INTF, src_id, tgt_id, len, msg2);
  if (status == SCEWL_ERR) {
    return 0;
  }

  // op should be REG on success
  return msg.op == SCEWL_SSS_REG;
}


int sss_deregister() {
  scewl_sss_msg_t msg;
  scewl_id_t src_id, tgt_id;
  int status, len;

  // fill registration message
  msg.dev_id = SCEWL_ID;
  msg.op = SCEWL_SSS_DEREG;
  
  // send registration
  status = send_msg(SSS_INTF, SCEWL_ID, SCEWL_SSS_ID, sizeof(msg), (char *)&msg);
  if (status == SCEWL_ERR) {
    return 0;
  }

  //remove stored encryption keys on deregistration
  memcpy(key,badKey,16);
  memcpy(BC_hmac_key,badKey,16);
  memcpy(DT_recv_hmac_key,badKey,16);
  memcpy(DT_hmac_key,badKey,16);
  memcpy(iv,badKey,16);
  tenDigitSerial = 0; // reset serial num

  // receive response
  len = read_msg(SSS_INTF, (char *)&msg, &src_id, &tgt_id, sizeof(scewl_sss_msg_t), 1);

  // notify CPU of response
  status = send_msg(CPU_INTF, src_id, tgt_id, len, (char *)&msg);
  if (status == SCEWL_ERR) {
    return 0;
  }

  // op should be DEREG on success
  return msg.op == SCEWL_SSS_DEREG;
}

int main() {
  int len;
  scewl_hdr_t hdr;
  uint16_t src_id, tgt_id;

  // initialize interfaces
  intf_init(CPU_INTF);
  intf_init(SSS_INTF);
  intf_init(RAD_INTF);

  //seed randGen with provisioned Device Registration Number and msgCounter
  unsigned long randomizer = DATA1;
  randomizer += msgCounter;
  srand(randomizer);
  randomizer = 0;

  // serve forever
  while (1) {
    // register with SSS
    read_msg(CPU_INTF, buf, &hdr.src_id, &hdr.tgt_id, sizeof(buf), 1);

    
    if (hdr.tgt_id == SCEWL_SSS_ID) {
      handle_registration(buf);
    }

    // server while registered
    while (registered) {
      memset(&hdr, 0, sizeof(hdr));

      // handle outgoing message from CPU
      if (intf_avail(CPU_INTF)) { 
        // Read message from CPU
        len = read_msg(CPU_INTF, buf, &src_id, &tgt_id, sizeof(buf), 1);

        if (tgt_id == SCEWL_BRDCST_ID) {
          handle_brdcst_send(buf, len);
        } else if (tgt_id == SCEWL_SSS_ID) {
          handle_registration(buf);
        } else if (tgt_id == SCEWL_FAA_ID) {
          handle_faa_send(buf, len);
        } else {
          handle_scewl_send(buf, tgt_id, len);
        }

        continue;
      }

      // handle incoming radio message
      if (intf_avail(RAD_INTF)) {
        // Read message from antenna
        len = read_msg(RAD_INTF, buf, &src_id, &tgt_id, sizeof(buf), 1);
        
        if (src_id != SCEWL_ID) { // ignore our own outgoing messages
          if (tgt_id == SCEWL_BRDCST_ID) {
            // check if FAA broadcast
            if (src_id == SCEWL_FAA_ID) handle_faa_recv(buf, len);
            // else receive broadcast message
            else handle_brdcst_recv(buf, src_id, len);
          } else if (tgt_id == SCEWL_ID) {
            // receive unicast message
            if (src_id == SCEWL_FAA_ID) {
              handle_faa_recv(buf, len);
            } else {
              handle_scewl_recv(buf, src_id, len);
            }
          }
        }
      }
    }
  }
}

//functions to implement integer to ascii conversion
void swap(char *x, char *y) {
    char t = *x; *x = *y; *y = t;
}
 
// function to reverse buffer[i..j]
char* reverse(char *buffer, int i, int j)
{
    while (i < j)
        swap(&buffer[i++], &buffer[j--]);
 
    return buffer;
}
 
// Iterative function to implement itoa() function in C
char* itoa(unsigned long value, char* buffer, int base)
{
    // invalid input
    if (base < 2 || base > 32)
        return buffer;
 
    // consider absolute value of number
    unsigned long n = value;
 
    int i = 0;
    while (n)
    {
        int r = n % base;
 
        if (r >= 10) 
            buffer[i++] = 65 + (r - 10);
        else
            buffer[i++] = 48 + r;
 
        n = n / base;
    }
 
    // if number is 0
    if (i == 0)
        buffer[i++] = '0';
 
    // If base is 10 and value is negative, the resulting string 
    // is preceded with a minus sign (-)
    // With any other base, value is always considered unsigned
    if (value < 0 && base == 10)
        buffer[i++] = '-';
 
    buffer[i] = '\0'; // null terminate string
 
    // reverse the string and return it
    return reverse(buffer, 0, i - 1);
}