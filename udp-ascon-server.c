#include "contiki.h"
#include "net/routing/routing.h"
#include "net/netstack.h"
#include "net/ipv6/simple-udp.h"
#include <stdint.h>
#include <inttypes.h>
#include <string.h>

#include <stdio.h>
#include "api.h"
#include "crypto_aead.h"

#include "sys/log.h"

#define LOG_MODULE "App"
#define LOG_LEVEL LOG_LEVEL_INFO

#define WITH_SERVER_REPLY  1
#define UDP_CLIENT_PORT    8765
#define UDP_SERVER_PORT    5678

static struct simple_udp_connection udp_conn;

typedef unsigned char u8;
typedef unsigned long long u64;
typedef long long i64;

void print_hex(const char* name, const unsigned char* var, unsigned long long len) {
  printf("%s[%llu] = ", name, len);
  for (unsigned long long i = 0; i < len; ++i) {
    printf("%02x", var[i]);
  }
  printf("\n");
}

#define ROTR(x,n) (((x)>>(n))|((x)<<(64-(n))))

void load64(u64* x, u8* S) {
  int i;
  *x = 0;
  for (i = 0; i < 8; ++i)
    *x |= ((u64) S[i]) << (56 - i * 8);
}

void store64(u8* S, u64 x) {
  int i;
  for (i = 0; i < 8; ++i)
    S[i] = (u8) (x >> (56 - i * 8));
}

void permutation(u8* S, int rounds) {
  int i;
  u64 x0, x1, x2, x3, x4;
  u64 t0, t1, t2, t3, t4;
  load64(&x0, S + 0);
  load64(&x1, S + 8);
  load64(&x2, S + 16);
  load64(&x3, S + 24);
  load64(&x4, S + 32);
  for (i = 0; i < rounds; ++i) {
    // addition of round constant
    x2 ^= ((0xfull - i) << 4) | i;
    // substitution layer
    x0 ^= x4;    x4 ^= x3;    x2 ^= x1;
    t0  = x0;    t1  = x1;    t2  = x2;    t3  = x3;    t4  = x4;
    t0 =~ t0;    t1 =~ t1;    t2 =~ t2;    t3 =~ t3;    t4 =~ t4;
    t0 &= x1;    t1 &= x2;    t2 &= x3;    t3 &= x4;    t4 &= x0;
    x0 ^= t1;    x1 ^= t2;    x2 ^= t3;    x3 ^= t4;    x4 ^= t0;
    x1 ^= x0;    x0 ^= x4;    x3 ^= x2;    x2 =~ x2;
    // linear diffusion layer
    x0 ^= ROTR(x0, 19) ^ ROTR(x0, 28);
    x1 ^= ROTR(x1, 61) ^ ROTR(x1, 39);
    x2 ^= ROTR(x2,  1) ^ ROTR(x2,  6);
    x3 ^= ROTR(x3, 10) ^ ROTR(x3, 17);
    x4 ^= ROTR(x4,  7) ^ ROTR(x4, 41);
  }
  store64(S + 0, x0);
  store64(S + 8, x1);
  store64(S + 16, x2);
  store64(S + 24, x3);
  store64(S + 32, x4);
}

int crypto_aead_decrypt(
    unsigned char *m, unsigned long long *mlen,
    unsigned char *nsec,
    const unsigned char *c, unsigned long long clen,
    const unsigned char *ad, unsigned long long adlen,
    const unsigned char *npub,
    const unsigned char *k) {

  *mlen = 0;
  if (clen < CRYPTO_KEYBYTES)
    return -1;

  int klen = CRYPTO_KEYBYTES;
  int size = 320 / 8;
  int capacity = 2 * klen;
  int rate = size - capacity;
  int a = 12;
  int b = (klen == 16) ? 6 : 8;
  i64 s = adlen / rate + 1;
  i64 t = (clen - klen) / rate + 1;
  i64 l = (clen - klen) % rate;

  u8 S[size];
  u8 A[s * rate];
  u8 M[t * rate];
  i64 i, j;

  // pad associated data
  for (i = 0; i < adlen; ++i)
    A[i] = ad[i];
  A[adlen] = 0x80;
  for (i = adlen + 1; i < s * rate; ++i)
    A[i] = 0;

  // initialization
  S[0] = klen * 8;
  S[1] = a;
  S[2] = b;
  for (i = 3; i < rate; ++i)
    S[i] = 0;
  for (i = 0; i < klen; ++i)
    S[rate + i] = k[i];
  for (i = 0; i < klen; ++i)
    S[rate + klen + i] = npub[i];
  permutation(S, a);
  for (i = 0; i < klen; ++i)
    S[rate + klen + i] ^= k[i];

  // process associated data
  if (adlen) {
    for (i = 0; i < s; ++i) {
      for (j = 0; j < rate; ++j)
        S[j] ^= A[i * rate + j];
      permutation(S, b);
    }
  }
  S[size - 1] ^= 1;

  // process plaintext
  for (i = 0; i < t - 1; ++i) {
    for (j = 0; j < rate; ++j) {
      M[i * rate + j] = S[j] ^ c[i * rate + j];
      S[j] = c[i * rate + j];
    }
    permutation(S, b);
  }
  for (j = 0; j < l; ++j)
    M[(t - 1) * rate + j] = S[j] ^ c[(t - 1) * rate + j];
  for (j = 0; j < l; ++j)
    S[j] = c[(t - 1) * rate + j];
  S[l] ^= 0x80;

  // finalization
  for (i = 0; i < klen; ++i)
    S[rate + i] ^= k[i];
  permutation(S, a);
  for (i = 0; i < klen; ++i)
    S[rate + klen + i] ^= k[i];

  // return -1 if verification fails
  for (i = 0; i < klen; ++i)
    if (c[clen - klen + i] != S[rate + klen + i])
      return -1;

  // return plaintext
  *mlen = clen - klen;
  for (i = 0; i < *mlen; ++i)
    m[i] = M[i];

  return 0;
}

PROCESS(udp_server_process, "UDP server");
AUTOSTART_PROCESSES(&udp_server_process);

static void udp_rx_callback(struct simple_udp_connection *c,
         const uip_ipaddr_t *sender_addr,
         uint16_t sender_port,
         const uip_ipaddr_t *receiver_addr,
         uint16_t receiver_port,
         const uint8_t *data,
         uint16_t datalen)
{
  unsigned char m[100];
  unsigned long long mlen;
  unsigned char npub[CRYPTO_NPUBBYTES] = {0};
  unsigned char k[CRYPTO_KEYBYTES] = {0};
  unsigned char ad[] = "ASCON";
  unsigned long long adlen = strlen((char *)ad);
  
  // Log sender's information
  LOG_INFO("Received message from ");
  LOG_INFO_6ADDR(sender_addr);
  LOG_INFO_(" (Port: %u)\n", sender_port);
  
  int r = crypto_aead_decrypt(m, &mlen, NULL, data, datalen, ad, adlen, npub, k);
  if (r != 0) {
    LOG_ERR("Decryption failed! '%.*s'\n", (int)mlen, m);
    return;
  }

  LOG_INFO("Decrypted message: '%.*s'\n", (int)mlen, m);

  LOG_INFO("Sending response to ");
  LOG_INFO_6ADDR(sender_addr);
  LOG_INFO_(" (Port: %u)\n", sender_port);
  LOG_INFO("Sending response.\n");
  simple_udp_sendto(&udp_conn, m, mlen, sender_addr);
}

/*---------------------------------------------------------------------------*/
PROCESS_THREAD(udp_server_process, ev, data)
{
  PROCESS_BEGIN();

  /* Initialize DAG root */
  NETSTACK_ROUTING.root_start();

  /* Initialize UDP connection */
  simple_udp_register(&udp_conn, UDP_SERVER_PORT, NULL,
                      UDP_CLIENT_PORT, udp_rx_callback);

  PROCESS_END();
}