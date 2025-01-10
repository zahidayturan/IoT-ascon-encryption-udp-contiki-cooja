#include "contiki.h"
#include "net/routing/routing.h"
#include "random.h"
#include "net/netstack.h"
#include "net/ipv6/simple-udp.h"
#include <stdint.h>
#include <inttypes.h>
#include <string.h>
#include <stdio.h>

#include "api.h"
#include "crypto_aead.h"

#include "sys/log.h"
#include "sys/energest.h"

#define LOG_MODULE "App"
#define LOG_LEVEL LOG_LEVEL_INFO

#define UDP_CLIENT_PORT    8765
#define UDP_SERVER_PORT    5678

#define SEND_INTERVAL      (10 * CLOCK_SECOND)

static struct simple_udp_connection udp_conn;

static unsigned long
to_seconds(uint64_t time)
{
  return (unsigned long)(time / ENERGEST_SECOND);
}
/*void print_hex(const char* name, const unsigned char* var, unsigned long long len) {
  printf("%s[%llu] = ", name, len);
  for (unsigned long long i = 0; i < len; ++i) {
    printf("%02x", var[i]);
  }
  printf("\n");
}*/

typedef unsigned char u8;
typedef unsigned long long u64;
typedef long long i64;

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
    x2 ^= ((0xfull - i) << 4) | i;
    x0 ^= x4;    x4 ^= x3;    x2 ^= x1;
    t0  = x0;    t1  = x1;    t2  = x2;    t3  = x3;    t4  = x4;
    t0 =~ t0;    t1 =~ t1;    t2 =~ t2;    t3 =~ t3;    t4 =~ t4;
    t0 &= x1;    t1 &= x2;    t2 &= x3;    t3 &= x4;    t4 &= x0;
    x0 ^= t1;    x1 ^= t2;    x2 ^= t3;    x3 ^= t4;    x4 ^= t0;
    x1 ^= x0;    x0 ^= x4;    x3 ^= x2;    x2 =~ x2;
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

int crypto_aead_encrypt(
    unsigned char *c, unsigned long long *clen,
    const unsigned char *m, unsigned long long mlen,
    const unsigned char *ad, unsigned long long adlen,
    const unsigned char *nsec,
    const unsigned char *npub,
    const unsigned char *k) {

  int klen = CRYPTO_KEYBYTES;
  int size = 320 / 8;
  int capacity = 2 * klen;
  int rate = size - capacity;
  int a = 12;
  int b = (klen == 16) ? 6 : 8;
  i64 s = adlen / rate + 1;
  i64 t = mlen / rate + 1;
  i64 l = mlen % rate;

  u8 S[size];
  u8 A[s * rate];
  u8 M[t * rate];
  i64 i, j;

  for (i = 0; i < adlen; ++i)
    A[i] = ad[i];
  A[adlen] = 0x80;
  for (i = adlen + 1; i < s * rate; ++i)
    A[i] = 0;
  for (i = 0; i < mlen; ++i)
    M[i] = m[i];
  M[mlen] = 0x80;
  for (i = mlen + 1; i < t * rate; ++i)
    M[i] = 0;

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

  if (adlen != 0) {
    for (i = 0; i < s; ++i) {
      for (j = 0; j < rate; ++j)
        S[j] ^= A[i * rate + j];
      permutation(S, b);
    }
  }
  S[size - 1] ^= 1;

  for (i = 0; i < t - 1; ++i) {
    for (j = 0; j < rate; ++j) {
      S[j] ^= M[i * rate + j];
      c[i * rate + j] = S[j];
    }
    permutation(S, b);
  }
  for (j = 0; j < rate; ++j)
    S[j] ^= M[(t - 1) * rate + j];
  for (j = 0; j < l; ++j)
    c[(t - 1) * rate + j] = S[j];

  for (i = 0; i < klen; ++i)
    S[rate + i] ^= k[i];
  permutation(S, a);
  for (i = 0; i < klen; ++i)
    S[rate + klen + i] ^= k[i];

  for (i = 0; i < klen; ++i)
    c[mlen + i] = S[rate + klen + i];
  *clen = mlen + klen;

  return 0;
}



PROCESS(udp_client_process, "UDP client");
AUTOSTART_PROCESSES(&udp_client_process);

PROCESS_THREAD(udp_client_process, ev, data) {
  static struct etimer periodic_timer;
  uip_ipaddr_t dest_ipaddr;

  unsigned long long alen, mlen, clen;
  unsigned char a[] = "ASCON";
  unsigned char m[] = "SAMSUN";
  unsigned char c[sizeof(m) + CRYPTO_ABYTES];
#if CRYPTO_NSECBYTES > 0
  unsigned char nsec[CRYPTO_NSECBYTES] = {0};
#endif
  unsigned char npub[CRYPTO_NPUBBYTES] = {0};
  unsigned char k[CRYPTO_KEYBYTES] = {0};
  int r;

  alen = strlen((char *)a);
  mlen = strlen((char *)m);
  clen = mlen + CRYPTO_ABYTES;

  PROCESS_BEGIN();

  simple_udp_register(&udp_conn, UDP_CLIENT_PORT, NULL, UDP_SERVER_PORT, NULL);
  etimer_set(&periodic_timer, random_rand() % SEND_INTERVAL);

  while (1) {
    PROCESS_WAIT_EVENT_UNTIL(etimer_expired(&periodic_timer));

    if (NETSTACK_ROUTING.node_is_reachable() && NETSTACK_ROUTING.get_root_ipaddr(&dest_ipaddr)) {

    energest_flush();
    static unsigned long counter = 0;
    if (++counter % 10 == 0) {
        LOG_INFO("Energest:\n");
        LOG_INFO(" CPU %4lus - LPM %4lus - Total time %lus - Radio LISTEN %4lus\n",
           to_seconds(energest_type_time(ENERGEST_TYPE_CPU)),
           to_seconds(energest_type_time(ENERGEST_TYPE_LPM)),
           to_seconds(ENERGEST_GET_TOTAL_TIME()),
           to_seconds(energest_type_time(ENERGEST_TYPE_LISTEN)));
    }

      LOG_INFO("Starting encryption...\n");

      /*
      print_hex("k", k, CRYPTO_KEYBYTES);
      print_hex("n", npub, CRYPTO_NPUBBYTES);
      print_hex("a", a, alen);
      print_hex("m", m, mlen);
      */

#if CRYPTO_NSECBYTES > 0
      r = crypto_aead_encrypt(c, &clen, m, mlen, a, alen, nsec, npub, k);
#else
      r = crypto_aead_encrypt(c, &clen, m, mlen, a, alen, NULL, npub, k);
#endif
      if (r != 0) {
        LOG_ERR("Encryption failed!\n");
        continue;
      }

      /*
      print_hex("c", c, clen - CRYPTO_ABYTES);
      print_hex("t", c + clen - CRYPTO_ABYTES, CRYPTO_ABYTES);
      */

      LOG_INFO("Sending encrypted message...\n");
      simple_udp_sendto(&udp_conn, c, clen, &dest_ipaddr);
    } else {
      LOG_INFO("Network not reachable.\n");
    }

    etimer_set(&periodic_timer, SEND_INTERVAL - CLOCK_SECOND + (random_rand() % (2 * CLOCK_SECOND)));
  }

  PROCESS_END();
}