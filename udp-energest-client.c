#include "contiki.h"
#include "net/routing/routing.h"
#include "random.h"
#include "net/netstack.h"
#include "net/ipv6/simple-udp.h"
#include "sys/log.h"
#include "sys/energest.h"

#define LOG_MODULE "Router"
#define LOG_LEVEL LOG_LEVEL_INFO

#define UDP_CLIENT_PORT    8765
#define UDP_SERVER_PORT    5678
#define SEND_INTERVAL      (10 * CLOCK_SECOND)

static struct simple_udp_connection udp_conn;

static uint32_t rx_count = 0;
static uint32_t tx_count = 0;

PROCESS(router_process, "Router process");
AUTOSTART_PROCESSES(&router_process);

/*---------------------------------------------------------------------------*/
static unsigned long
to_seconds(uint64_t time)
{
  return (unsigned long)(time / ENERGEST_SECOND);
}

static void print_energest(void) {
  /* Update energest counters */
  energest_flush();

  /* Print energy statistics */
  LOG_INFO("Energest:\n");
  LOG_INFO(" CPU          %4lus LPM      %4lus DEEP LPM %4lus  Total time %lus\n",
           to_seconds(energest_type_time(ENERGEST_TYPE_CPU)),
           to_seconds(energest_type_time(ENERGEST_TYPE_LPM)),
           to_seconds(energest_type_time(ENERGEST_TYPE_DEEP_LPM)),
           to_seconds(ENERGEST_GET_TOTAL_TIME()));
  LOG_INFO(" Radio LISTEN %4lus TRANSMIT %4lus OFF      %4lus\n",
           to_seconds(energest_type_time(ENERGEST_TYPE_LISTEN)),
           to_seconds(energest_type_time(ENERGEST_TYPE_TRANSMIT)),
           to_seconds(ENERGEST_GET_TOTAL_TIME()
                      - energest_type_time(ENERGEST_TYPE_TRANSMIT)
                      - energest_type_time(ENERGEST_TYPE_LISTEN)));
}

/*---------------------------------------------------------------------------*/
static void
udp_rx_callback(struct simple_udp_connection *c,
         const uip_ipaddr_t *sender_addr,
         uint16_t sender_port,
         const uip_ipaddr_t *receiver_addr,
         uint16_t receiver_port,
         const uint8_t *data,
         uint16_t datalen)
{
  LOG_INFO("Received message: '%.*s' from ", datalen, (char *)data);
  LOG_INFO_6ADDR(sender_addr);
  LOG_INFO_("\n");

  rx_count++;

  // Log message sender and receiver
  LOG_INFO("Message received from: ");
  LOG_INFO_6ADDR(sender_addr);
  LOG_INFO_(" to ");
  LOG_INFO_6ADDR(receiver_addr);
  LOG_INFO_("\n");

  // Forward message to the next hop (destination)
  LOG_INFO("Forwarding message to ");
  LOG_INFO_6ADDR(receiver_addr);
  LOG_INFO_("\n");

  // Send the message back to the sender (or to another node in the path)
  simple_udp_sendto(&udp_conn, data, datalen, receiver_addr);

  tx_count++;
}

/*---------------------------------------------------------------------------*/
PROCESS_THREAD(router_process, ev, data)
{
  static struct etimer periodic_timer; 

  PROCESS_BEGIN();

  /* Initialize UDP connection */
  simple_udp_register(&udp_conn, UDP_CLIENT_PORT, NULL, UDP_SERVER_PORT, udp_rx_callback);

  etimer_set(&periodic_timer, random_rand() % SEND_INTERVAL);

  while(1) {
    PROCESS_WAIT_EVENT_UNTIL(etimer_expired(&periodic_timer));

    /* Print statistics every 10th message */
    if (rx_count % 10 == 0) {
      LOG_INFO("Messages received: %" PRIu32 ", Messages forwarded: %" PRIu32 "\n", rx_count, tx_count);
      print_energest();  // Log energy statistics
    }

    etimer_set(&periodic_timer, SEND_INTERVAL - CLOCK_SECOND + (random_rand() % (2 * CLOCK_SECOND)));
  }

  PROCESS_END();
}
