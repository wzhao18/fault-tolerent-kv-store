// Copyright (C) 2016, 2017 Alexey Khrabrov, Bogdan Simion
//                     2020 Angela Demke Brown
// Distributed under the terms of the GNU General Public License.
//
// This file is part of Assignment 3, CSC469, Fall 2020.
//
// This is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This file is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this file.  If not, see <http://www.gnu.org/licenses/>.


// The key-value server implementation

#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <pthread.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#include <sys/types.h>
#include <sys/socket.h>

#include "defs.h"
#include "hash.h"
#include "util.h"


// Program arguments

// Host name and port number of the metadata server
static char coord_host_name[HOST_NAME_MAX] = "";
static uint16_t coord_port = 0;

// Ports for listening to incoming connections from clients, servers and coord
static uint16_t clients_port = 0;
static uint16_t servers_port = 0;
static uint16_t coord_in_port = 0; 

// Current server id and total number of servers
static int server_id = -1;
static int num_servers = 0;

// Log file name
static char log_file_name[PATH_MAX] = "";

static bool recovery_mode = false;
static bool self_recovery_mode = false;

bool g_received_shutdown = false;

static void usage(char **argv)
{
	printf("usage: %s -h <coord host> -m <coord port> -c <clients port> "
	       "-s <servers port> -M <coord incoming port> -S <server id> "
	       "-n <num servers> [-l <log file>]\n", argv[0]);
	printf("If the log file (-l) is not specified, log output is written "
	       "to stdout\n");
}

// Returns false if the arguments are invalid
static bool parse_args(int argc, char **argv)
{
	char option;
	while ((option = getopt(argc, argv, "h:m:c:s:M:S:n:l:")) != -1) {
		switch(option) {
		case 'h':
			strncpy(coord_host_name, optarg, HOST_NAME_MAX);
			break;
		case 'm':
			coord_port  = atoi(optarg);
			break;
		case 'c':
			clients_port  = atoi(optarg);
			break;
		case 's':
			servers_port  = atoi(optarg);
			break;
		case 'M':
			coord_in_port = atoi(optarg);
			break;
		case 'S':
			server_id     = atoi(optarg);
			break;
		case 'n':
			num_servers   = atoi(optarg);
			break;
		case 'l':
			strncpy(log_file_name, optarg, PATH_MAX);
			break;
		default:
			fprintf(stderr, "Invalid option: -%c\n", option);
			return false;
		}
	}

	// Allow server to choose own ports. Uncomment extra conditions if
	// server ports must be specified on command line.
	return (coord_host_name[0] != '\0') && (coord_port != 0) &&
		//(clients_port != 0) && (servers_port != 0) &&
		//(coord_in_port != 0) &&
		(num_servers >= 3) && (server_id >= 0) && (server_id < num_servers);
}


// Socket for sending requests to the coordinator
static int coord_fd_out = -1;
// Socket for receiving requests from the coordinator
static int coord_fd_in = -1;

// Sockets for listening for incoming connections from clients, servers
// and coordinator
static int my_clients_fd = -1;
static int my_servers_fd = -1;
static int my_coord_fd = -1;

// Store fds for all connected clients, up to MAX_CLIENT_SESSIONS
static int client_fd_table[MAX_CLIENT_SESSIONS];

// Store fds for connected servers
#define MAX_SERVER_SESSIONS 2
static int server_fd_table[MAX_SERVER_SESSIONS] = { -1, -1 };


// Storage for this server's primary key set
hash_table primary_hash = {0};

// Storage for this server's secondary key set
hash_table secondary_hash = {0};

// Primary server (the one that stores the primary copy for this server's
// secondary key set)
static int primary_sid = -1;
static int primary_fd = -1;

// Secondary server (the one that stores the secondary copy for this server's
// primary key set)
static int secondary_sid = -1;
static int secondary_fd = -1;


static void cleanup();

static const int hash_size = 65536;

void *thread_heartbeat(void *threadid) {

	log_write("Start thread id: %ld for sending heartbeat to coordinator\n", (long int)threadid);
	
	char send_buffer[MAX_MSG_LEN] = {0};
	coord_ctrl_request *req = (coord_ctrl_request*)send_buffer;

	while (1) {
		sleep(0.5);
		req->hdr.type = MSG_COORD_CTRL_REQ;
		req->type = HEARTBEAT;
		req->server_id = server_id;
		if (!send_msg(coord_fd_out, req, sizeof(*req))) {
			log_error("thread_heatbreak\n");
			log_msg_into_stderr(req, true);
			break;
		}
	}

	log_write("fail to send heartbeat message to coordinator\n");
	pthread_exit(NULL);
}


// Initialize and start the server
static bool init_server()
{
	for (int i = 0; i < MAX_CLIENT_SESSIONS; i++) {
		client_fd_table[i] = -1;
	}

	// Get the host name that server is running on
	char my_host_name[HOST_NAME_MAX] = "";
	char timebuf[TIME_STR_SIZE];

	if (get_local_host_name(my_host_name, sizeof(my_host_name)) < 0) {
		return false;
	}
	log_write("%s Server starts on host: %s\n",
		  current_time_str(timebuf, TIME_STR_SIZE), my_host_name);

	// Create sockets for incoming connections from clients and other servers
	uint16_t newport = 0;
	my_clients_fd  = create_server(clients_port, MAX_CLIENT_SESSIONS, &newport);
	if (my_clients_fd < 0)  {
		goto cleanup;
	}
	if (newport != 0) {
		clients_port = newport;
		newport = 0;
	}

	my_servers_fd  = create_server(servers_port, MAX_SERVER_SESSIONS, &newport);
	if (my_servers_fd < 0) {
		goto cleanup;
	}
	if (newport != 0) {
		servers_port = newport;
		newport = 0;
	}
	
	my_coord_fd = create_server(coord_in_port, 1, &newport);
	if (my_coord_fd < 0) {
		goto cleanup;
	}
	if (newport != 0) {
		coord_in_port = newport;
		newport = 0;
	}

	// Determine the ids of replica servers
	primary_sid = primary_server_id(server_id, num_servers);
	secondary_sid = secondary_server_id(server_id, num_servers);

	// Initialize key-value storage for primary
	if (!hash_init(&primary_hash, hash_size)) {
		goto cleanup;
	}

	// Initialize key-value storage for secondary 
	if (!hash_init(&secondary_hash, hash_size)) {
		goto cleanup;
	}

	// Connect to coordinator to "register" that we are live
	if ((coord_fd_out = connect_to_server(coord_host_name, coord_port)) < 0) {
		goto cleanup;
	}
	// Tell coordinator about the port numbers we are using
	char send_buffer[MAX_MSG_LEN] = {0};
	coord_ctrl_request *req = (coord_ctrl_request*)send_buffer;
	req->hdr.type = MSG_COORD_CTRL_REQ;
	req->type = STARTED;
	req->server_id = server_id;
	req->ports[0] = clients_port;
	req->ports[1] = servers_port;
	req->ports[2] = coord_in_port;

	assert(coord_fd_out >= 0);
	if (!send_msg(coord_fd_out, req, sizeof(*req) + 3*sizeof(uint16_t))) {
		log_error("init_server\n");
		log_msg_into_stderr(req, true);
		goto cleanup;
	}

	// TODO: Create a separate thread that takes care of sending periodic heartbeat messages
	// ...

	pthread_t heartbeat_thread;
    if (pthread_create(&heartbeat_thread, NULL, thread_heartbeat, (void *)0)){
    	log_write("Error: pthread_create failed %d.\n", 0);
        return false;
    }

	log_write("Server initialized\n");
	return true;

cleanup:
	log_write("Server initialization failed.\n");
	cleanup();
	return false;
}

// Hash iterator for freeing memory used by values; called during storage cleanup
static void clean_iterator_f(const char key[KEY_SIZE], void *value, size_t value_sz, void *arg)
{
	(void)key;
	(void)value_sz;
	(void)arg;

	assert(value != NULL);
	free(value);
}

// Cleanup and release all the resources
static void cleanup()
{
	log_write("Cleaning up and exiting ...\n");

	close_safe(&coord_fd_out);
	close_safe(&coord_fd_in);
	close_safe(&my_clients_fd);
	close_safe(&my_servers_fd);
	close_safe(&my_coord_fd);
	close_safe(&secondary_fd);
	close_safe(&primary_fd);

	for (int i = 0; i < MAX_CLIENT_SESSIONS; i++) {
		close_safe(&(client_fd_table[i]));
	}
	for (int i = 0; i < MAX_SERVER_SESSIONS; i++) {
		close_safe(&(server_fd_table[i]));
	}

	hash_iterate(&primary_hash, clean_iterator_f, NULL);
	hash_cleanup(&primary_hash);

	// TODO: release all other resources
	// ...
	hash_iterate(&secondary_hash, clean_iterator_f, NULL);
	hash_cleanup(&secondary_hash);

}


// Connection will be closed after calling this function regardless of result
static void process_client_message(int fd)
{
	char timebuf[TIME_STR_SIZE];

	log_write("%s Receiving a client message\n",
		  current_time_str(timebuf, TIME_STR_SIZE));

	// Read and parse the message
	char req_buffer[MAX_MSG_LEN] = {0};
	if (!recv_msg(fd, req_buffer, MAX_MSG_LEN, MSG_OPERATION_REQ)) {
		return;
	}
	operation_request *request = (operation_request*)req_buffer;

	// Initialize the response
	char resp_buffer[MAX_MSG_LEN] = {0};
	operation_response *response = (operation_response*)resp_buffer;
	response->hdr.type = MSG_OPERATION_RESP;
	uint16_t value_sz = 0;

	// TODO: extend this function to support replication
	// Make sure to implement all necessary synchronization.
	// Feel free to use the lock/unlock functions from hash.h.
	// ...

	// Check that requested key is valid.
	// A server should only respond to requests for which it holds the
	// primary replica. For debugging and testing, however, we also want
	// to allow the secondary server to respond to OP_VERIFY requests,
	// to confirm that replication has succeeded. To check this, we need
	// to know the primary server id for which this server is the secondary.
	int key_srv_id = key_server_id(request->key, num_servers);


	int recovery_mode = recovery_mode;

	int invalid_request = false;

	if (self_recovery_mode){
		invalid_request = true;
	}

	if (key_srv_id != server_id){
		if (!recovery_mode){
			if ((key_srv_id != primary_sid) || (request->type != OP_VERIFY)){
				invalid_request = true;
			}
		}
		else{
			if ((key_srv_id != primary_sid)){
				invalid_request = true;
			}
		}
	}
	

	if (invalid_request){
		log_error("sid %d: Invalid client key %s sid %d\n", server_id, key_to_str(request->key), key_srv_id);
		// This can happen if client is using old config during recovery
		response->status = INVALID_REQUEST;
		assert(fd >= 0);
		if (send_msg(fd, response, sizeof(*response) + value_sz)) {
			log_error("process_clieng_msg::invalid_request_send\n");
			log_msg_into_stderr(response, true);
		}
		return;
	}

	// Process the request based on its type
	switch (request->type) {
		case OP_NOOP:
			response->status = SUCCESS;
			break;

		case OP_GET: {
			void *data = NULL;
			size_t size = 0;

			// assert(key_srv_id == server_id);
			hash_table *logical_primary_hash;
			if (key_srv_id == server_id){
				logical_primary_hash = &primary_hash;
			}
			else{
				assert(key_srv_id == primary_sid);
				logical_primary_hash = &secondary_hash;
			}

			hash_lock(logical_primary_hash, request->key);

			// Get the value for requested key from the hash table
			if (!hash_get(logical_primary_hash, request->key, &data, &size)) {
				log_write("Key %s not found\n", key_to_str(request->key));
				response->status = KEY_NOT_FOUND;
				break;
			}

			hash_unlock(logical_primary_hash, request->key);

			// Copy the stored value into the response buffer
			memcpy(response->value, data, size);
			value_sz = size;

			response->status = SUCCESS;
			break;
		}

		case OP_PUT: {
			// Need to copy the value to dynamically allocated memory
			size_t value_size = request->hdr.length - sizeof(*request);
			void *value_copy = malloc(value_size);

			// assert(key_srv_id == server_id);

			if (value_copy == NULL) {
				log_perror("malloc");
				log_error("sid %d: Out of memory\n", server_id);
				response->status = OUT_OF_SPACE;
				break;
			}
			memcpy(value_copy, request->value, value_size);

			void *old_value = NULL;
			size_t old_value_sz = 0;

			hash_table *logical_primary_hash;
			int logical_secondary_fd;

			// this server is the primary for key
			if (key_srv_id == server_id) {
				logical_primary_hash = &primary_hash;
				logical_secondary_fd = secondary_fd;
			}
			// this server is the secondary for key
			else if (key_srv_id == primary_sid) {
				assert(recovery_mode);
				logical_primary_hash = &secondary_hash;
				logical_secondary_fd = primary_fd;
			} else {
				assert(false);
			}

			hash_lock(logical_primary_hash, request->key);

			if (!hash_put(logical_primary_hash, request->key, value_copy, value_size, &old_value, &old_value_sz))
			{
				log_error("sid %d: Out of memory\n", server_id);
				free(value_copy);
				response->status = OUT_OF_SPACE;
				break;
			}

			hash_unlock(logical_primary_hash, request->key);

			// // TODO: forward the PUT request to the secondary replica
			// assert(logical_secondary_fd >= 0);
			// send_msg(logical_secondary_fd, request, sizeof(*request) + value_size);
			if (logical_secondary_fd < 0) {
				assert(false);
				// log_error("There is no valid fd for secondary now.\n");
			} else {
				// TODO: forward the PUT request to the secondary replica
				if (!send_msg(logical_secondary_fd, request, sizeof(*request) + value_size)){
					log_error("fail to send message to logical_secondary_fd\n");
					log_msg_into_stderr(request, true);
					
				}
				else{
					char recv_buffer[MAX_MSG_LEN] = {0};
					int recv_result = recv_msg(logical_secondary_fd, recv_buffer, MAX_MSG_LEN, MSG_OPERATION_RESP);

					operation_response *sec_response = (operation_response*)recv_buffer;

					if (!recv_result || sec_response->status != SUCCESS)
					{
						log_write("Fail to put value into secondary copy\n");
					}
				}
			}

			// Need to free the old value (if there was any)
			if (old_value != NULL) {
				free(old_value);
			}

			response->status = SUCCESS;
			break;
		}

		case OP_VERIFY: {
			// Checked for invalid OP_VERIFY earlier. Now just check
			// if we are primary or secondary for this key.
			if (key_srv_id == server_id) {
				// Handle just like a GET request
				void *data = NULL;
				size_t size = 0;

				hash_lock(&primary_hash, request->key);

				// Get the value for key from the primary hash table
				if (!hash_get(&primary_hash, request->key, &data, &size)) {
					log_write("Key %s not found\n",
						  key_to_str(request->key));
					response->status = KEY_NOT_FOUND;
				} else {
					// Copy the value into the response buffer
					memcpy(response->value, data, size);
					value_sz = size;
					response->status = SUCCESS;
				}

				hash_unlock(&primary_hash, request->key);
			} else if (key_srv_id == primary_sid) {
				//TODO: server should hold secondary replica of key
				//Process like a GET request, using secondary keys.
				//...
				// log_write("sid %d: OP_VERIFY not implemented yet.\n",
				// 	  server_id);
				// response->status = KEY_NOT_FOUND;

				// Handle just like a GET request
				void *data = NULL;
				size_t size = 0;
				// Get the value for key from the secondary hash table

				hash_lock(&secondary_hash, request->key);

				if (!hash_get(&secondary_hash, request->key, &data, &size)) {
					log_write("Key %s not found\n",
						  key_to_str(request->key));
					response->status = KEY_NOT_FOUND;
				} else {
					// Copy the value into the response buffer
					memcpy(response->value, data, size);
					value_sz = size;
					response->status = SUCCESS;
				}

				hash_unlock(&secondary_hash, request->key);

			} else {
				// Should not be possible if logic for checking
				// invalid request prior to switch is correct.
				assert(false);
			}
			break;
		}
		default:
			log_error("sid %d: Invalid client operation type\n", server_id);
			return;
	}

	// Send reply to the client
	assert(fd >= 0);
	if (!send_msg(fd, response, sizeof(*response) + value_sz)) {
		log_error("process_client_msg::send\n");
		log_msg_into_stderr(response, true);
	}
	return;
}


// Returns false if either the message was invalid or if this was the last message
// (in both cases the connection will be closed)
static bool process_server_message(int fd)
{
	char timebuf[TIME_STR_SIZE];

	log_write("%s Receiving a server message\n",
		  current_time_str(timebuf, TIME_STR_SIZE));

	// Read and parse the message
	char req_buffer[MAX_MSG_LEN] = {0};
	if (!recv_msg(fd, req_buffer, MAX_MSG_LEN, MSG_OPERATION_REQ)) {
		return false;
	}
	operation_request *request = (operation_request*)req_buffer;

	int key_srv_id = key_server_id(request->key, num_servers);

	// NOOP operation request is used to indicate the last message in an UPDATE sequence
	if (request->type == OP_NOOP) {
		log_write("Received the last server message, closing connection\n");
		return false;
	}

	// Initialize the response
	char resp_buffer[MAX_MSG_LEN] = {0};
	operation_response *response = (operation_response*)resp_buffer;
	response->hdr.type = MSG_OPERATION_RESP;

	hash_table *hash_table_ptr;
	if (key_srv_id == server_id){
		hash_table_ptr = &primary_hash;
	}
	else if (key_srv_id == primary_sid){
		hash_table_ptr = &secondary_hash;
	}
	else{
		assert(false);
	}

	// TODO: process the message and send the response
	if (request->type == OP_PUT) {
		assert(key_srv_id == primary_sid);
		// Need to copy the value to dynamically allocated memory
		size_t value_size = request->hdr.length - sizeof(*request);
		void *value_copy = malloc(value_size);

		if (value_copy == NULL) {
			log_perror("malloc");
			log_error("sid %d: Out of memory\n", server_id);
			response->status = OUT_OF_SPACE;
			assert(fd >= 0);
			if (!send_msg(fd, response, sizeof(*response))) {
				log_error("process_server_msg::OP_PUT::send\n");
				log_msg_into_stderr(response, true);
			}
			return false;
		}
		memcpy(value_copy, request->value, value_size);

		void *old_value = NULL;
		size_t old_value_sz = 0;

		hash_lock(hash_table_ptr, request->key);

		// Put the <key, value> pair into the hash table
		if (!hash_put(hash_table_ptr, request->key, value_copy, value_size, &old_value, &old_value_sz))
		{
			log_error("sid %d: Out of memory\n", server_id);
			hash_unlock(hash_table_ptr, request->key);
			free(value_copy);
			response->status = OUT_OF_SPACE;
			assert(fd >= 0);
			if (!send_msg(fd, response, sizeof(*response))) {
				log_error("process_server_msg::OP_PUT");
				log_msg_into_stderr(response, true);
			}
			return false;
		}

		hash_unlock(hash_table_ptr, request->key);

		// Need to free the old value (if there was any)
		if (old_value != NULL) {
			free(old_value);
		}

		response->status = SUCCESS;
		assert(fd >= 0);
		if (!send_msg(fd, response, sizeof(*response))) {
			log_error("process_server_msg::OP_PUT::send\n");
			log_msg_into_stderr(response, true);
		}
	}
	else if (request->type == OP_RECOVER) {
		assert(self_recovery_mode);
		size_t value_size = request->hdr.length - sizeof(*request);
		void *value_copy = malloc(value_size);

		if (value_copy == NULL) {
			log_perror("malloc");
			log_error("sid %d: Out of memory\n", server_id);
			response->status = OUT_OF_SPACE;
			assert(fd >= 0);
			if (!send_msg(fd, response, sizeof(*response))){
				log_write("fail to send response to server\n");
				log_msg_into_stderr(response, true);
			}
			return false;
		}
		memcpy(value_copy, request->value, value_size);

		void *old_value = NULL;
		size_t old_value_sz = 0;

		hash_lock(hash_table_ptr, request->key);

		if (!hash_get(hash_table_ptr, request->key, &old_value, &old_value_sz)){
			// For recovery purpose PUT, only put into hashmap if key not exists
			if (!hash_put(hash_table_ptr, request->key, value_copy, value_size, &old_value, &old_value_sz))
			{
				hash_unlock(hash_table_ptr, request->key);
				log_error("sid %d: Out of memory\n", server_id);
				free(value_copy);
				response->status = OUT_OF_SPACE;
				assert(fd >= 0);
				if (!send_msg(fd, response, sizeof(*response))){
					log_write("fail to send response to server\n");
					log_msg_into_stderr(response, true);
				}
				return false;
			}

			if (old_value != NULL) {
				free(old_value);
			}

			response->status = SUCCESS;
			assert(fd >= 0);
			if (!send_msg(fd, response, sizeof(*response))) {
				log_error("process_server_message::OP_RECOVER::send_msg\n");
				log_write("fail to send response to server\n");
				log_msg_into_stderr(response, true);
			}
		}

		hash_unlock(hash_table_ptr, request->key);
	}

	return true;
}

/*
	Helper to dump hashtable content to file and arg stores the FILE * to write to.
*/
void dump_hash_iterator(const char key[KEY_SIZE], void *value, size_t value_sz, void *arg) {
	FILE *file = *((FILE **) arg);

	char value_cpy[value_sz + 1];
	memcpy(value_cpy, value, value_sz);
	value_cpy[value_sz] = '\0';

	if (fprintf(file, "%s -> %s\n", key_to_str(key), value_cpy) < 0) {
		fprintf(stderr, "Failed dumping key->value.");
		return;
	}

	// fseek(file, 0, SEEK_END);
	// fwrite(value, value_sz, 1, file);
}

/*
	Helper to send key-value pair to new primary.
	arg is an int[2], arg[0] is sockfd, arg[1] indicates failure
*/
void update_hashtable_iterator(const char key[KEY_SIZE], void *value, size_t value_sz, void *arg) {
	int sockfd = ((int *)arg)[0];
	char send_buffer[MAX_MSG_LEN] = {0};
	operation_request *request = (operation_request*)send_buffer;
	request->hdr.type = MSG_OPERATION_REQ;
	request->type = OP_RECOVER;
	memcpy(request->key, key, KEY_SIZE);

	// Need to copy the value, only for PUT operations
	strncpy(request->value, (char *)value, value_sz);

	char recv_buffer[MAX_MSG_LEN] = {0};
	assert(sockfd >= 0);
	if (!send_msg(sockfd, request, sizeof(*request) + value_sz) ||
	    !recv_msg(sockfd, recv_buffer, sizeof(recv_buffer), MSG_OPERATION_RESP))
	{
		log_error("[Step 3]: update_primary_iterator failed with SERVER_FAILURE\n");
		log_msg_into_stderr(request, true);
		((int *)arg)[1] = 1;
		return;
	}

	operation_response *response = (operation_response*)recv_buffer;
	if (response->status != SUCCESS) {
		log_error("[Step 3]: update_primary_iterator respond with non-SUCCESS\n");
		((int *)arg)[1] = 1;
		return;
	}
}

/*
	As stated in Step 3 of the recovery steps:
	KV_b receives the UPDATE-PRIMARY message. Then, KV_b spawns a new thread to asynchronously send
	its set X to KV_aa. Basically, this thread will send the set X one by one to KV_aa in the background,
	as new client requests (GET or PUT) keep coming in to KV_b.
*/
void *async_kv_b_send_kv_aa(void *arg) {
	int args[2] = {*((int *) arg), 0};

	hash_iterate(&secondary_hash, &update_hashtable_iterator, (void *)args);

	int failure = args[1];
	char send_buffer[MAX_MSG_LEN] = {0};
	coord_ctrl_request *req = (coord_ctrl_request*)send_buffer;
	req->server_id = server_id;
	req->hdr.type = MSG_COORD_CTRL_REQ;
	req->type = failure ? UPDATE_PRIMARY_FAILED : UPDATED_PRIMARY;

	assert(coord_fd_out >= 0);
	if(!send_msg(coord_fd_out, req, sizeof(*req))){
		log_error("failed to send updated primary to coord\n");
		log_msg_into_stderr(req, true);
	}

	pthread_exit(NULL);
}

/* TODO: Implement the async function that send info from KV_c
	         to KV_aa.
 */
void *async_kv_c_send_kv_aa(void *arg) {
	int args[2] = {*((int *) arg), 0};

	hash_iterate(&primary_hash, &update_hashtable_iterator, (void *) args);

	int failure = args[1];
	char send_buffer[MAX_MSG_LEN] = {0};
	coord_ctrl_request *req = (coord_ctrl_request*)send_buffer;
	req->server_id = server_id;
	req->hdr.type = MSG_COORD_CTRL_REQ;
	req->type = failure ? UPDATE_SECONDARY_FAILED : UPDATED_SECONDARY;

	//kv_c should be done with recovery mode at this point
	recovery_mode = false;

	assert(coord_fd_out >= 0);
	if (!send_msg(coord_fd_out, req, sizeof(*req))){
		log_error("failed to send updated secondary to coord\n");
		log_msg_into_stderr(req, true);
	}

	pthread_exit(NULL);
}

// Returns false if the message was invalid (so the connection will be closed)
// Sets *shutdown_requested to true if received a SHUTDOWN message (so the server will terminate)
static bool process_coordinator_message(int fd, bool *shutdown_requested)
{
	int sockfd;
	char filename[256];
	char timebuf[TIME_STR_SIZE];
	pthread_t tid;

	assert(shutdown_requested != NULL);
	*shutdown_requested = false;

	log_write("%s Receiving a coordinator message\n",
		  current_time_str(timebuf,TIME_STR_SIZE));

	// Read and parse the message
	char req_buffer[MAX_MSG_LEN] = {0};
	if (!recv_msg(fd, req_buffer, MAX_MSG_LEN, MSG_SERVER_CTRL_REQ)) {
		return false;
	}
	server_ctrl_request *request = (server_ctrl_request*)req_buffer;

	// Initialize the response
	server_ctrl_response response = {0};
	response.hdr.type = MSG_SERVER_CTRL_RESP;
	response.status = SERVER_CTRLREQ_STATUS_MAX; // Detect unset status
	
	// Process the request based on its type
	switch (request->type) {
	case SET_SECONDARY:
		if ((secondary_fd = connect_to_server(request->host_name,
						      request->port)) < 0) {
			response.status = CTRLREQ_FAILURE;
		} else {
			response.status = CTRLREQ_SUCCESS;
		}
		break;

	case UPDATE_PRIMARY:
		// TODO: handle this message type
		// 3. KV_b receives the UPDATE-PRIMARY message. Then, KV_b
		//    spawns a new thread to asynchronously send its set X
		//    to KV_aa. Basically, this thread will send the set X
		//    one by one to KV_aa in the background, as new client
		//    requests (GET or PUT) keep coming in to KV_b. Next,
		//    KV_b sends a confirmation back to CO, to indicate that
		//    it received the UPDATE-PRIMARY message.
		sockfd = connect_to_server(request->host_name, request->port);
		if (sockfd < 0) {
			log_error("[Step 3]: failed to connect to KV_aa from KV_b");
			response.status = CTRLREQ_FAILURE;
		} else {

			pthread_create(&tid, NULL, async_kv_b_send_kv_aa, (void *)(&sockfd));
			int old_primary_fd = primary_fd;
			primary_fd = sockfd;
			close_safe(&old_primary_fd);
			recovery_mode = true;

			response.status = CTRLREQ_SUCCESS;
			assert(fd >= 0);
			if (!send_msg(fd, &response, sizeof(response))) {
				log_error("process_coordinator_msg::UPDATE_PRIMARY::send\n");
				log_msg_into_stderr(&response, true);
			}

			return true;
		}
		break;

	case UPDATE_SECONDARY:
		// TODO: handle this message type
		// 6. KV_c receives the UPDATE-SECONDARY message and spawns
		//    a new thread to asynchronously send its set Y to KV_aa.
		//    KV_c confirms the UPDATE-SECONDARY message by sending a
		//    confirmation message to CO.

		// secondary_fd updated: from KV_a to KV_aa
		sockfd = connect_to_server(request->host_name, request->port);
		if (sockfd < 0) {
			log_error("[Step 3]: failed to connect to KV_aa from KV_b");
			response.status = CTRLREQ_FAILURE;
		} else {
			response.status = CTRLREQ_SUCCESS;
			assert(fd >= 0);
			if (!send_msg(fd, &response, sizeof(response))) {
				log_msg_into_stderr(&response, true);
				log_error("process_coordinate_msg::UPDATE_SECONDARY::send\n");
			}

			pthread_create(&tid, NULL, async_kv_c_send_kv_aa, (void *)(&sockfd));
			int old_secondary_fd = secondary_fd;
			secondary_fd = sockfd;
			close_safe(&old_secondary_fd);
			secondary_fd = sockfd;
			recovery_mode = true;

			return true;
		}
		break;

	case SWITCH_PRIMARY:
		// TODO: handle this message type
		response.status = CTRLREQ_SUCCESS;

		recovery_mode = false;
		break;
	case INFORM_RECOVERY:
		response.status = CTRLREQ_SUCCESS;
		self_recovery_mode = true;
		break;
	case INFORM_RECOVERY_COMPLETE:
		response.status = CTRLREQ_SUCCESS;
		self_recovery_mode = false;
		break;
	case SHUTDOWN:
		*shutdown_requested = true;
		return true;
		
	case DUMP_PRIMARY:
		// TODO: write primary keys from hash table to file, overwriting
		// any previous content in the output file. 
		// The output file should be named "server_<sid>.primary",
		// where <sid> is the server id number of this server.
		// No response is expected, so after dumping keys, just return.
		// char filename[256] = "server";
		// strcat(filename, itoa(server_id));
		// strcat(filename, ".primary");

		snprintf(filename, sizeof(char) * 256, "server_%d.primary", server_id);
		FILE *dump_file_primary = fopen(filename, "w");
		hash_iterate(&primary_hash, &dump_hash_iterator, &dump_file_primary);
		fclose(dump_file_primary);
		response.status = CTRLREQ_SUCCESS;

		break;
		
	case DUMP_SECONDARY:
		// TODO: write secondary keys from hash table to file, overwriting
		// any previous content in the output file. 
		// The output file should be named "server_<sid>.secondary",
		// where <sid> is the server id number of this server.
		// No response is expected, so after dumping keys, just return.
		// char filename[256] = "server";
		// strcat(filename, itoa(server_id));
		// strcat(filename, ".primary");

		snprintf(filename, sizeof(char) * 256, "server_%d.secondary", server_id);
		FILE *dump_file_secondary = fopen(filename, "w");
		hash_iterate(&secondary_hash, &dump_hash_iterator, &dump_file_secondary);
		fclose(dump_file_secondary);
		response.status = CTRLREQ_SUCCESS;
		
		break;
	
	default:// impossible
		assert(false);
		break;
	}

	assert(response.status != SERVER_CTRLREQ_STATUS_MAX);
	
	assert(fd >= 0);
	if (!send_msg(fd, &response, sizeof(response))) {
		log_msg_into_stderr(&response, true);
		log_error("process_coordinate_msg:::send\n");
	}
	
	return true;
}

void *run_server_to_server_loop(){
	fd_set rset, allset;
	FD_SET(my_servers_fd, &allset);
	int maxfd = my_servers_fd;
	for (;;) {
		if (g_received_shutdown) {
			break;
		}

		rset = allset;

		int num_ready_fds = select(maxfd + 1, &rset, NULL, NULL, NULL);
		if (num_ready_fds < 0) {
			log_perror("select");
			break;
		}

		if (num_ready_fds <= 0) {
			continue;
		}

		// Incoming connection from the server
		if (FD_ISSET(my_servers_fd, &rset)) {
			int fd_idx = accept_connection(my_servers_fd, server_fd_table, 2);
			if (fd_idx >= 0) {
				FD_SET(server_fd_table[fd_idx], &allset);
				maxfd = max(maxfd, server_fd_table[fd_idx]);
			}
			assert(fd_idx == 0 || fd_idx == 1);

			if (--num_ready_fds <= 0) {
				continue;
			}
		}

		// Check for any messages from the servers
		for (int i = 0; i < MAX_SERVER_SESSIONS; i++){
			if ((server_fd_table[i] != -1) && FD_ISSET(server_fd_table[i], &rset)) {
				if(!process_server_message(server_fd_table[i])) {
					// Received an invalid message or last message, close the connection
					log_error("sid %d: Closing server to server connection\n", server_id);
					FD_CLR(server_fd_table[i], &allset);
					close_safe(&(server_fd_table[i]));
				}
			}
		}
	}

	pthread_exit(NULL);
}



// Returns false if stopped due to errors, true if shutdown was requested
static bool run_server_loop()
{
	// Usual preparation stuff for select()
	fd_set rset, allset;
	FD_ZERO(&allset);
	FD_SET(my_clients_fd, &allset);
	FD_SET(my_coord_fd, &allset);

	int maxfd = max(my_clients_fd, my_coord_fd);

	// Server sits in an infinite loop waiting for incoming connections
	// from coordinator or clients, and for incoming messages from already
	// connected coordinator or clients
	//
	// TODO: process connections and messages from other servers as well
	// ...

	for (;;) {
		rset = allset;

		int num_ready_fds = select(maxfd + 1, &rset, NULL, NULL, NULL);
		if (num_ready_fds < 0) {
			log_perror("select");
			return false;
		}

		if (num_ready_fds <= 0) {
			continue;
		}

		// Incoming connection from the coordinator
		if (FD_ISSET(my_coord_fd, &rset)) {
			int fd_idx = accept_connection(my_coord_fd, &coord_fd_in, 1);
			if (fd_idx >= 0) {
				FD_SET(coord_fd_in, &allset);
				maxfd = max(maxfd, coord_fd_in);
			}
			assert(fd_idx == 0);

			if (--num_ready_fds <= 0) {
				continue;
			}
		}

		// Check for any messages from the coordinator
		if ((coord_fd_in != -1) && FD_ISSET(coord_fd_in, &rset)) {
			bool shutdown_requested = false;
			if (!process_coordinator_message(coord_fd_in,
							 &shutdown_requested)) {
				// Received an invalid message, close the connection
				log_error("sid %d: Closing coordinator connection\n", server_id);
				FD_CLR(coord_fd_in, &allset);
				close_safe(&(coord_fd_in));
			} else if (shutdown_requested) {
				g_received_shutdown = true;
				return true;
			}

			if (--num_ready_fds <= 0) {
				continue;
			}
		}

		// Incoming connection from a client
		if (FD_ISSET(my_clients_fd, &rset)) {
			int fd_idx = accept_connection(my_clients_fd, client_fd_table, MAX_CLIENT_SESSIONS);
			if (fd_idx >= 0) {
				FD_SET(client_fd_table[fd_idx], &allset);
				maxfd = max(maxfd, client_fd_table[fd_idx]);
			}

			if (--num_ready_fds <= 0) {
				continue;
			}
		}

		// Check for any messages from connected clients
		for (int i = 0; i < MAX_CLIENT_SESSIONS; i++) {
			if ((client_fd_table[i] != -1) && FD_ISSET(client_fd_table[i], &rset)) {
				process_client_message(client_fd_table[i]);
				// Close connection after processing (semantics are "one connection per request")
				FD_CLR(client_fd_table[i], &allset);
				close_safe(&(client_fd_table[i]));

				if (--num_ready_fds <= 0) {
					break;
				}
			}
		}
	}
}


int main(int argc, char **argv)
{
	signal(SIGPIPE, SIG_IGN);

	if (!parse_args(argc, argv)) {
		usage(argv);
		return 1;
	}

	open_log(log_file_name);

	if (!init_server()) {
		return 1;
	}

	pthread_t server_to_server_thread;
	if (pthread_create(&server_to_server_thread, NULL, run_server_to_server_loop, (void *)0)){
		log_write("Error: pthread_create failed %d.\n", 0);
		return false;
    }
	bool result = run_server_loop();

	pthread_join(server_to_server_thread, NULL);

	cleanup();
	// pthread_cancel(server_to_server_thread);
	return result ? 0 : 1;
}
