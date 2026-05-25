// SPDX-License-Identifier: GPL-2.0

#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sched.h>
#include <signal.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/mount.h>
#include <sys/wait.h>
#include <unistd.h>
#include <linux/android/binder.h>
#include <linux/android/binderfs.h>

#include "kselftest_harness.h"

#define BINDER_MAPPING_SIZE	(128 * 1024)
#define READ_BUFFER_SIZE	1024
#define REQUEST_COUNT		3
#define SUCCESS_COUNT		2
#define GET_SESSION_CODE	0x700
#define FORWARD_SESSION_CODE	0x701
#define ORDINARY_REQUEST_CODE	0x702
#define ORDINARY_REPLY_CODE	0x703
#define ORDINARY_REQUEST_PAYLOAD	0x12340702
#define ORDINARY_REPLY_PAYLOAD		0x98760703
#define MIXED_REQUEST_ID	404
#define MIXED_CLAIM_ID		504
#define MIXED_REQUEST_CODE	0x404
#define OWNER_EXIT_REQUEST_ID	405
#define OWNER_EXIT_CLAIM_ID	505
#define OWNER_EXIT_REQUEST_CODE	0x405

static size_t append_command(unsigned char *buffer, size_t offset, __u32 command,
			     const void *payload, size_t payload_size)
{
	memcpy(buffer + offset, &command, sizeof(command));
	offset += sizeof(command);
	memcpy(buffer + offset, payload, payload_size);

	return offset + payload_size;
}

static int binder_write(int fd, const void *buffer, size_t size)
{
	struct binder_write_read bwr = {
		.write_size = size,
		.write_buffer = (uintptr_t)buffer,
	};
	int ret;

	do {
		ret = ioctl(fd, BINDER_WRITE_READ, &bwr);
	} while (ret < 0 && errno == EINTR);

	if (ret == 0 && bwr.write_consumed != size) {
		errno = EIO;
		return -1;
	}

	return ret;
}

static int binder_read(int fd, __u32 expected, void *payload, size_t payload_size)
{
	unsigned char buffer[READ_BUFFER_SIZE];
	unsigned char done_buffer[sizeof(__u32) +
				  sizeof(struct binder_ptr_cookie)];
	struct binder_write_read bwr = {
		.read_size = sizeof(buffer),
		.read_buffer = (uintptr_t)buffer,
	};
	struct binder_ptr_cookie ptr_cookie;
	size_t position, size;
	bool found;
	__u32 command;
	int ret;

	for (;;) {
		position = 0;
		found = false;
		bwr.read_consumed = 0;
		do {
			ret = ioctl(fd, BINDER_WRITE_READ, &bwr);
		} while (ret < 0 && errno == EINTR);
		if (ret < 0)
			return ret;

		while (position + sizeof(command) <= bwr.read_consumed) {
			memcpy(&command, buffer + position, sizeof(command));
			position += sizeof(command);

			if (command == BR_NOOP || command == BR_SPAWN_LOOPER ||
			    command == BR_TRANSACTION_COMPLETE)
				continue;
			if (command == BR_INCREFS || command == BR_ACQUIRE) {
				if (position + sizeof(ptr_cookie) >
				    bwr.read_consumed) {
					errno = EPROTO;
					return -1;
				}
				memcpy(&ptr_cookie, buffer + position,
				       sizeof(ptr_cookie));
				position += sizeof(ptr_cookie);
				command = command == BR_INCREFS ? BC_INCREFS_DONE :
								  BC_ACQUIRE_DONE;
				size = append_command(done_buffer, 0, command,
						      &ptr_cookie,
						      sizeof(ptr_cookie));
				if (binder_write(fd, done_buffer, size) < 0)
					return -1;
				continue;
			}
			if (found || command != expected ||
			    position + payload_size > bwr.read_consumed) {
				errno = EPROTO;
				return -1;
			}

			memcpy(payload, buffer + position, payload_size);
			position += payload_size;
			found = true;
		}

		if (position != bwr.read_consumed) {
			errno = EPROTO;
			return -1;
		}
		if (found)
			return 0;
	}
}

static int free_buffer(int fd, binder_uintptr_t buffer)
{
	unsigned char command[sizeof(__u32) + sizeof(buffer)];
	size_t size;

	size = append_command(command, 0, BC_FREE_BUFFER, &buffer,
			      sizeof(buffer));
	return binder_write(fd, command, size);
}

static int claim_reply(int fd, __u32 handle, __u64 claim_id)
{
	unsigned char command[sizeof(__u32) +
			      sizeof(struct binder_multiplexed_reply_claim)];
	struct binder_multiplexed_reply_claim claim = {
		.handle = handle,
		.claim_id = claim_id,
	};
	size_t size;

	size = append_command(command, 0, BC_CLAIM_MULTIPLEXED_REPLY, &claim,
			      sizeof(claim));
	return binder_write(fd, command, size);
}

static int release_handle(int fd, __u32 handle)
{
	unsigned char command[sizeof(__u32) + sizeof(handle)];
	size_t size;

	size = append_command(command, 0, BC_RELEASE, &handle, sizeof(handle));
	return binder_write(fd, command, size);
}

static int retire_multiplexed_node(int fd,
				   const struct flat_binder_object *session)
{
	unsigned char command[sizeof(__u32) + sizeof(struct binder_ptr_cookie)];
	struct binder_ptr_cookie node = {
		.ptr = session->binder,
		.cookie = session->cookie,
	};
	size_t size;

	size = append_command(command, 0, BC_RETIRE_MULTIPLEXED_NODE,
			      &node, sizeof(node));
	return binder_write(fd, command, size);
}

static int send_session_node(int fd, const struct flat_binder_object *session)
{
	unsigned char command[sizeof(__u32) +
			      sizeof(struct binder_transaction_data)];
	struct binder_transaction_data request;
	struct binder_transaction_data reply = {
		.data_size = sizeof(*session),
		.offsets_size = sizeof(binder_size_t),
		.data.ptr.buffer = (uintptr_t)session,
	};
	binder_size_t offset = 0;
	size_t size;

	reply.data.ptr.offsets = (uintptr_t)&offset;
	if (binder_read(fd, BR_TRANSACTION, &request, sizeof(request)) < 0)
		return -1;
	if (request.code != GET_SESSION_CODE || request.data_size != 0)
		return -1;
	if (free_buffer(fd, request.data.ptr.buffer) < 0)
		return -1;
	size = append_command(command, 0, BC_REPLY, &reply, sizeof(reply));
	return binder_write(fd, command, size);
}

static int get_session_handle(int fd, __u32 *handle)
{
	unsigned char command[sizeof(__u32) +
			      sizeof(struct binder_transaction_data)];
	struct binder_transaction_data request = {
		.target.handle = 0,
		.code = GET_SESSION_CODE,
	};
	struct binder_transaction_data reply;
	const struct flat_binder_object *object;
	size_t size;

	size = append_command(command, 0, BC_TRANSACTION, &request,
			      sizeof(request));
	if (binder_write(fd, command, size) < 0 ||
	    binder_read(fd, BR_REPLY, &reply, sizeof(reply)) < 0)
		return -1;
	if (reply.data_size != sizeof(*object) ||
	    reply.offsets_size != sizeof(binder_size_t))
		return -1;
	object = (const struct flat_binder_object *)(uintptr_t)
		reply.data.ptr.buffer;
	if (object->hdr.type != BINDER_TYPE_HANDLE)
		return -1;
	*handle = object->handle;
	size = append_command(command, 0, BC_ACQUIRE, handle, sizeof(*handle));
	if (binder_write(fd, command, size) < 0)
		return -1;
	return free_buffer(fd, reply.data.ptr.buffer);
}

static int forward_session_handle(int fd, __u32 handle)
{
	unsigned char command[sizeof(__u32) +
			      sizeof(struct binder_transaction_data)];
	struct flat_binder_object session = {
		.hdr.type = BINDER_TYPE_HANDLE,
		.handle = handle,
	};
	struct binder_transaction_data request = {
		.target.handle = 0,
		.code = FORWARD_SESSION_CODE,
		.data_size = sizeof(session),
		.offsets_size = sizeof(binder_size_t),
		.data.ptr.buffer = (uintptr_t)&session,
	};
	struct binder_transaction_data reply;
	binder_size_t offset = 0;
	size_t size;

	request.data.ptr.offsets = (uintptr_t)&offset;
	size = append_command(command, 0, BC_TRANSACTION, &request,
			      sizeof(request));
	if (binder_write(fd, command, size) < 0 ||
	    binder_read(fd, BR_REPLY, &reply, sizeof(reply)) < 0)
		return -1;
	if (reply.data_size != 0 || reply.offsets_size != 0)
		return -1;
	return free_buffer(fd, reply.data.ptr.buffer);
}

static int receive_forwarded_session(int fd, struct flat_binder_object *session)
{
	unsigned char command[sizeof(__u32) +
			      sizeof(struct binder_transaction_data)];
	struct binder_transaction_data request;
	struct binder_transaction_data reply = { 0 };
	const struct flat_binder_object *received;
	const binder_size_t *offset;
	size_t size;

	if (binder_read(fd, BR_TRANSACTION, &request, sizeof(request)) < 0)
		return -1;
	if (request.code != FORWARD_SESSION_CODE ||
	    request.data_size != sizeof(*session) ||
	    request.offsets_size != sizeof(*offset))
		return -1;
	received = (const struct flat_binder_object *)(uintptr_t)
		request.data.ptr.buffer;
	offset = (const binder_size_t *)(uintptr_t)request.data.ptr.offsets;
	if (*offset != 0 ||
	    (received->hdr.type != BINDER_TYPE_BINDER &&
	     received->hdr.type != BINDER_TYPE_HANDLE))
		return -1;
	*session = *received;
	if (free_buffer(fd, request.data.ptr.buffer) < 0)
		return -1;
	size = append_command(command, 0, BC_REPLY, &reply, sizeof(reply));
	return binder_write(fd, command, size);
}

static int reply_to_ordinary_caller(int fd)
{
	static const __u64 reply_payload = ORDINARY_REPLY_PAYLOAD;
	unsigned char command[sizeof(__u32) +
			      sizeof(struct binder_multiplexed_reply_sg)];
	struct binder_multiplexed_transaction_received request;
	struct binder_buffer_object reply_object = {
		.hdr.type = BINDER_TYPE_PTR,
		.buffer = (uintptr_t)&reply_payload,
		.length = sizeof(reply_payload),
	};
	struct binder_multiplexed_reply_sg reply = {
		.transaction_data.transaction_data.code = ORDINARY_REPLY_CODE,
		.transaction_data.transaction_data.data_size =
				sizeof(reply_object),
		.transaction_data.transaction_data.offsets_size =
				sizeof(binder_size_t),
		.transaction_data.transaction_data.data.ptr.buffer =
				(uintptr_t)&reply_object,
		.transaction_data.buffers_size = sizeof(reply_payload),
	};
	binder_size_t offset = 0;
	size_t size;

	reply.transaction_data.transaction_data.data.ptr.offsets =
		(uintptr_t)&offset;
	if (binder_read(fd, BR_TRANSACTION_MULTIPLEXED, &request,
			sizeof(request)) < 0)
		return -1;
	if (request.request_id != 0 || request.reply_token == 0 ||
	    request.delivery_flags != BINDER_MULTIPLEXED_DELIVERY_ORDINARY ||
	    request.reserved != 0 ||
	    request.transaction_data.code != ORDINARY_REQUEST_CODE ||
	    request.transaction_data.data_size != sizeof(__u32) ||
	    request.transaction_data.offsets_size != 0 ||
	    *(const __u32 *)(uintptr_t)request.transaction_data.data.ptr.buffer !=
			    ORDINARY_REQUEST_PAYLOAD ||
	    free_buffer(fd, request.transaction_data.data.ptr.buffer) < 0)
		return -1;
	reply.reply_token = request.reply_token;
	size = append_command(command, 0, BC_REPLY_MULTIPLEXED_SG, &reply,
			      sizeof(reply));
	return binder_write(fd, command, size);
}

static int call_ordinary_transaction(int fd, __u32 handle)
{
	static const __u32 request_payload = ORDINARY_REQUEST_PAYLOAD;
	unsigned char command[sizeof(__u32) +
			      sizeof(struct binder_transaction_data)];
	struct binder_transaction_data request = {
		.target.handle = handle,
		.code = ORDINARY_REQUEST_CODE,
		.data_size = sizeof(request_payload),
		.data.ptr.buffer = (uintptr_t)&request_payload,
	};
	struct binder_transaction_data reply;
	const struct binder_buffer_object *object;
	size_t size;

	size = append_command(command, 0, BC_TRANSACTION, &request,
			      sizeof(request));
	if (binder_write(fd, command, size) < 0 ||
	    binder_read(fd, BR_REPLY, &reply, sizeof(reply)) < 0)
		return -1;
	if (reply.code != ORDINARY_REPLY_CODE ||
	    reply.data_size != sizeof(*object) ||
	    reply.offsets_size != sizeof(binder_size_t))
		return -1;
	object = (const struct binder_buffer_object *)(uintptr_t)
		reply.data.ptr.buffer;
	if (object->hdr.type != BINDER_TYPE_PTR ||
	    object->length != sizeof(__u64) ||
	    *(const __u64 *)(uintptr_t)object->buffer != ORDINARY_REPLY_PAYLOAD)
		return -1;
	return free_buffer(fd, reply.data.ptr.buffer);
}

static int server(const char *path, int read_fd, int write_fd)
{
	static const __u64 request_ids[REQUEST_COUNT] = { 101, 202, 303 };
	static const __u32 request_codes[REQUEST_COUNT] = { 0x101, 0x202, 0x303 };
	static const __u32 request_payloads[REQUEST_COUNT] = {
		0x12340101, 0x12340202, 0x12340303
	};
	static const __u32 reply_codes[SUCCESS_COUNT] = { 0x301, 0x302 };
	static const __u32 reply_payloads[SUCCESS_COUNT] = {
		0x98760301, 0x98760302
	};
	unsigned char command_buffer[sizeof(__u32) +
				     sizeof(struct binder_multiplexed_reply)];
	struct binder_multiplexed_transaction_received received;
	struct binder_multiplexed_reply reply = { 0 };
	struct flat_binder_object manager = {
		.hdr.type = BINDER_TYPE_BINDER,
		.binder = 1,
		.cookie = 2,
	};
	struct flat_binder_object session = {
		.hdr.type = BINDER_TYPE_BINDER,
		.flags = FLAT_BINDER_FLAG_MULTIPLEXED_DELIVERY,
		.binder = 3,
		.cookie = 4,
	};
	struct flat_binder_object exit_session = {
		.hdr.type = BINDER_TYPE_BINDER,
		.flags = FLAT_BINDER_FLAG_MULTIPLEXED_DELIVERY,
		.binder = 5,
		.cookie = 6,
	};
	struct flat_binder_object mixed_session = {
		.hdr.type = BINDER_TYPE_BINDER,
		.flags = FLAT_BINDER_FLAG_MULTIPLEXED_DELIVERY,
		.binder = 7,
		.cookie = 8,
	};
	struct flat_binder_object forwarded_session;
	__u64 tokens[REQUEST_COUNT] = { 0 };
	void *mapping;
	size_t size;
	int fd, i, index;
	char ready = 1;
	__u32 enter_looper = BC_ENTER_LOOPER;

	fd = open(path, O_RDWR | O_CLOEXEC);
	if (fd < 0)
		return 1;
	mapping = mmap(NULL, BINDER_MAPPING_SIZE, PROT_READ, MAP_PRIVATE, fd, 0);
	if (mapping == MAP_FAILED)
		return 1;
	if (ioctl(fd, BINDER_SET_CONTEXT_MGR_EXT, &manager) < 0)
		return 1;
	if (binder_write(fd, &enter_looper, sizeof(enter_looper)) < 0)
		return 1;
	if (write(write_fd, &ready, sizeof(ready)) != sizeof(ready))
		return 1;
	if (send_session_node(fd, &session) < 0 ||
	    receive_forwarded_session(fd, &forwarded_session) < 0)
		return 1;

	for (i = 0; i < REQUEST_COUNT; i++) {
		if (binder_read(fd, BR_TRANSACTION_MULTIPLEXED, &received,
				sizeof(received)) < 0)
			return 1;
		if (received.request_id == request_ids[0])
			index = 0;
		else if (received.request_id == request_ids[1])
			index = 1;
		else if (received.request_id == request_ids[2])
			index = 2;
		else
			return 1;
		if (tokens[index] || received.reply_token == 0 ||
		    received.delivery_flags != 0 || received.reserved != 0 ||
		    received.transaction_data.code != request_codes[index] ||
		    received.transaction_data.data_size !=
			    sizeof(request_payloads[index]) ||
		    *(const __u32 *)(uintptr_t)
			    received.transaction_data.data.ptr.buffer !=
			    request_payloads[index])
			return 1;
		tokens[index] = received.reply_token;
		if (free_buffer(fd, received.transaction_data.data.ptr.buffer) < 0)
			return 1;
	}
	if (write(write_fd, &ready, sizeof(ready)) != sizeof(ready) ||
	    send_session_node(fd, &forwarded_session) < 0 ||
	    read(read_fd, &ready, sizeof(ready)) != sizeof(ready) ||
	    send_session_node(fd, &forwarded_session) < 0 ||
	    read(read_fd, &ready, sizeof(ready)) != sizeof(ready))
		return 1;

	{
		unsigned char buffer[READ_BUFFER_SIZE];
		struct binder_write_read bwr = {
			.read_size = sizeof(buffer),
			.read_buffer = (uintptr_t)buffer,
		};
		struct binder_ptr_cookie ptr_cookie;
		bool released = false, decrefs = false;
		__u32 command;
		size_t position;
		int ret;

		while (!released || !decrefs) {
			bwr.read_consumed = 0;
			do {
				ret = ioctl(fd, BINDER_WRITE_READ, &bwr);
			} while (ret < 0 && errno == EINTR);
			if (ret < 0)
				return 1;
			for (position = 0; position < bwr.read_consumed;) {
				if (position + sizeof(command) > bwr.read_consumed)
					return 1;
				memcpy(&command, buffer + position, sizeof(command));
				position += sizeof(command);
				if (command == BR_NOOP || command == BR_SPAWN_LOOPER ||
				    command == BR_TRANSACTION_COMPLETE)
					continue;
				if (command != BR_INCREFS && command != BR_ACQUIRE &&
				    command != BR_RELEASE && command != BR_DECREFS)
					return 1;
				if (position + sizeof(ptr_cookie) > bwr.read_consumed)
					return 1;
				memcpy(&ptr_cookie, buffer + position,
				       sizeof(ptr_cookie));
				position += sizeof(ptr_cookie);
				if (command == BR_INCREFS || command == BR_ACQUIRE) {
					command = command == BR_INCREFS ?
						  BC_INCREFS_DONE : BC_ACQUIRE_DONE;
					size = append_command(command_buffer, 0, command,
							      &ptr_cookie,
							      sizeof(ptr_cookie));
					if (binder_write(fd, command_buffer, size) < 0)
						return 1;
					continue;
				}
				if (ptr_cookie.ptr != session.binder ||
				    ptr_cookie.cookie != session.cookie)
					continue;
				released |= command == BR_RELEASE;
				decrefs |= command == BR_DECREFS;
			}
		}
	}

	for (i = SUCCESS_COUNT - 1; i >= 0; i--) {
		if (i == 0) {
			unsigned char sg_command[sizeof(__u32) +
						 sizeof(struct binder_multiplexed_reply_sg)];
			struct binder_multiplexed_reply_sg sg_reply = {
				.reply_token = tokens[i],
			};

			size = append_command(sg_command, 0, BC_REPLY_MULTIPLEXED_SG,
					      &sg_reply, sizeof(sg_reply));
			errno = 0;
			if (binder_write(fd, sg_command, size) == 0 ||
			    errno != EINVAL)
				return 1;
		}
		memset(&reply, 0, sizeof(reply));
		reply.transaction_data.code = reply_codes[i];
		reply.transaction_data.data_size = sizeof(reply_payloads[i]);
		reply.transaction_data.data.ptr.buffer =
			(uintptr_t)&reply_payloads[i];
		reply.reply_token = tokens[i];
		size = append_command(command_buffer, 0, BC_REPLY_MULTIPLEXED,
				      &reply, sizeof(reply));
		if (binder_write(fd, command_buffer, size) < 0)
			return 1;
	}
	if (retire_multiplexed_node(fd, &session) < 0)
		return 1;
	memset(&reply, 0, sizeof(reply));
	reply.reply_token = tokens[SUCCESS_COUNT];
	size = append_command(command_buffer, 0, BC_REPLY_MULTIPLEXED,
			      &reply, sizeof(reply));
	if (binder_write(fd, command_buffer, size) == 0 || errno != EINVAL ||
	    write(write_fd, &ready, sizeof(ready)) != sizeof(ready) ||
	    read(read_fd, &ready, sizeof(ready)) != sizeof(ready))
		return 1;
	if (send_session_node(fd, &mixed_session) < 0 ||
	    binder_read(fd, BR_TRANSACTION_MULTIPLEXED, &received,
			sizeof(received)) < 0 ||
	    received.request_id != MIXED_REQUEST_ID ||
	    received.delivery_flags != 0 || received.reserved != 0 ||
	    received.transaction_data.code != MIXED_REQUEST_CODE ||
	    received.reply_token == 0 ||
	    free_buffer(fd, received.transaction_data.data.ptr.buffer) < 0 ||
	    write(write_fd, &ready, sizeof(ready)) != sizeof(ready) ||
	    reply_to_ordinary_caller(fd) < 0 ||
	    read(read_fd, &ready, sizeof(ready)) != sizeof(ready) ||
	    binder_read(fd, BR_TRANSACTION_MULTIPLEXED, &received,
			sizeof(received)) < 0 ||
	    received.request_id != 0 ||
	    received.delivery_flags != BINDER_MULTIPLEXED_DELIVERY_ORDINARY ||
	    received.reserved != 0 ||
	    received.transaction_data.code != ORDINARY_REQUEST_CODE ||
	    received.reply_token == 0 ||
	    received.transaction_data.data_size != sizeof(__u32) ||
	    received.transaction_data.offsets_size != 0 ||
	    *(const __u32 *)(uintptr_t)received.transaction_data.data.ptr.buffer !=
			    ORDINARY_REQUEST_PAYLOAD ||
	    free_buffer(fd, received.transaction_data.data.ptr.buffer) < 0 ||
	    retire_multiplexed_node(fd, &mixed_session) < 0 ||
	    write(write_fd, &ready, sizeof(ready)) != sizeof(ready) ||
	    send_session_node(fd, &exit_session) < 0 ||
	    binder_read(fd, BR_TRANSACTION_MULTIPLEXED, &received,
			sizeof(received)) < 0 ||
	    received.request_id != OWNER_EXIT_REQUEST_ID ||
	    received.delivery_flags != 0 || received.reserved != 0 ||
	    received.transaction_data.code != OWNER_EXIT_REQUEST_CODE ||
	    received.reply_token == 0 ||
	    free_buffer(fd, received.transaction_data.data.ptr.buffer) < 0 ||
	    write(write_fd, &ready, sizeof(ready)) != sizeof(ready) ||
	    read(read_fd, &ready, sizeof(ready)) != sizeof(ready))
		return 1;
	close(read_fd);
	close(write_fd);
	munmap(mapping, BINDER_MAPPING_SIZE);
	close(fd);
	return 0;
}

static int abandon_claims(const char *path, int write_fd)
{
	static const __u64 claim_ids[REQUEST_COUNT] = { 401, 402, 403 };
	void *mapping;
	__u32 session_handle;
	int fd, i;
	char ready = 1;

	fd = open(path, O_RDWR | O_CLOEXEC);
	if (fd < 0)
		return 1;
	mapping = mmap(NULL, BINDER_MAPPING_SIZE, PROT_READ, MAP_PRIVATE, fd, 0);
	if (mapping == MAP_FAILED)
		return 1;
	if (get_session_handle(fd, &session_handle) < 0)
		return 1;
	for (i = 0; i < REQUEST_COUNT; i++) {
		if (claim_reply(fd, session_handle, claim_ids[i]) < 0)
			return 1;
	}
	if (write(write_fd, &ready, sizeof(ready)) != sizeof(ready))
		return 1;
	close(write_fd);
	munmap(mapping, BINDER_MAPPING_SIZE);
	close(fd);
	return 0;
}

static int claimant(const char *path, int read_fd, int write_fd)
{
	static const __u64 request_ids[REQUEST_COUNT] = { 101, 202, 303 };
	static const __u64 claim_ids[REQUEST_COUNT] = { 501, 502, 503 };
	static const __u32 reply_codes[SUCCESS_COUNT] = { 0x301, 0x302 };
	static const __u32 reply_payloads[SUCCESS_COUNT] = {
		0x98760301, 0x98760302
	};
	struct binder_multiplexed_reply_received reply;
	struct binder_multiplexed_reply_error error;
	void *mapping;
	__u32 session_handle;
	__u32 enter_looper = BC_ENTER_LOOPER;
	int fd, i, index, tries;
	char ready = 1;

	fd = open(path, O_RDWR | O_CLOEXEC);
	if (fd < 0)
		return 1;
	mapping = mmap(NULL, BINDER_MAPPING_SIZE, PROT_READ, MAP_PRIVATE, fd, 0);
	if (mapping == MAP_FAILED)
		return 1;
	if (get_session_handle(fd, &session_handle) < 0)
		return 1;
	if (binder_write(fd, &enter_looper, sizeof(enter_looper)) < 0)
		return 1;
	for (i = 0; i < REQUEST_COUNT; i++) {
		for (tries = 0; tries < 1000; tries++) {
			if (claim_reply(fd, session_handle, claim_ids[i]) == 0)
				break;
			if (errno != ENOSPC)
				return 1;
			usleep(1000);
		}
		if (tries == 1000)
			return 1;
	}
	if (release_handle(fd, session_handle) < 0)
		return 1;
	if (write(write_fd, &ready, sizeof(ready)) != sizeof(ready))
		return 1;
	close(write_fd);
	if (read(read_fd, &ready, sizeof(ready)) != sizeof(ready))
		return 1;
	close(read_fd);
	for (i = 0; i < SUCCESS_COUNT; i++) {
		index = SUCCESS_COUNT - i - 1;
		if (binder_read(fd, BR_REPLY_MULTIPLEXED, &reply,
				sizeof(reply)) < 0)
			return 1;
		if (reply.claim_id != claim_ids[i] ||
		    reply.request_id != request_ids[index] ||
		    reply.transaction_data.code != reply_codes[index] ||
		    reply.transaction_data.data_size !=
			    sizeof(reply_payloads[index]) ||
		    *(const __u32 *)(uintptr_t)
			    reply.transaction_data.data.ptr.buffer !=
			    reply_payloads[index] ||
		    free_buffer(fd, reply.transaction_data.data.ptr.buffer) < 0)
			return 1;
	}
	if (binder_read(fd, BR_REPLY_MULTIPLEXED_ERROR, &error,
			sizeof(error)) < 0 ||
	    error.claim_id != claim_ids[SUCCESS_COUNT] ||
	    error.request_id != request_ids[SUCCESS_COUNT] ||
	    error.reason != BINDER_MULTIPLEXED_REPLY_SHUTDOWN || error.error != 0)
		return 1;
	munmap(mapping, BINDER_MAPPING_SIZE);
	close(fd);
	return 0;
}

TEST(multiplexed_reply_claim_by_second_holder)
{
	static const __u64 request_ids[REQUEST_COUNT] = { 101, 202, 303 };
	static const __u32 request_codes[REQUEST_COUNT] = { 0x101, 0x202, 0x303 };
	static const __u32 request_payloads[REQUEST_COUNT] = {
		0x12340101, 0x12340202, 0x12340303
	};
	char mountpoint[] = P_tmpdir "/binder_multiplexed_XXXXXX";
	char path[sizeof(P_tmpdir "/binder_multiplexed_XXXXXX/") +
		  BINDERFS_MAX_NAME + sizeof("features/multiplexed_transactions")];
	unsigned char command_buffer[REQUEST_COUNT *
				     (sizeof(__u32) +
				      sizeof(struct binder_multiplexed_transaction))];
	struct binder_multiplexed_transaction request = { 0 };
	struct binder_multiplexed_reply_error error;
	struct binderfs_device device = { .name = "mux-binder" };
	void *mapping = MAP_FAILED;
	size_t size = 0;
	int abandoner_to_parent[2] = { -1, -1 };
	int claimant_to_parent[2] = { -1, -1 };
	int parent_to_claimant[2] = { -1, -1 };
	int parent_to_server[2] = { -1, -1 };
	int server_to_parent[2] = { -1, -1 }, status;
	int control_fd = -1, feature_fd = -1, fd = -1;
	pid_t abandoner_pid = -1, claimant_pid = -1, server_pid = -1;
	char ready, feature;
	__u32 session_handle;
	__u32 enter_looper = BC_ENTER_LOOPER;
	int ret, i;

	if (geteuid() != 0)
		SKIP(return, "Test requires root to mount binderfs");

	ret = unshare(CLONE_NEWNS);
	ASSERT_EQ(ret, 0) {
		TH_LOG("%s - Failed to unshare mount namespace", strerror(errno));
	}
	ret = mount(NULL, "/", NULL, MS_REC | MS_PRIVATE, 0);
	ASSERT_EQ(ret, 0) {
		TH_LOG("%s - Failed to make mounts private", strerror(errno));
	}
	ASSERT_NE(mkdtemp(mountpoint), NULL) {
		TH_LOG("%s - Failed to create binderfs mountpoint", strerror(errno));
	}
	ret = mount(NULL, mountpoint, "binder", 0, 0);
	if (ret < 0 && errno == ENODEV)
		SKIP(goto out_rmdir, "binderfs is not available");
	ASSERT_EQ(ret, 0) {
		TH_LOG("%s - Failed to mount binderfs", strerror(errno));
	}

	snprintf(path, sizeof(path), "%s/features/multiplexed_transactions",
		 mountpoint);
	feature_fd = open(path, O_RDONLY | O_CLOEXEC);
	if (feature_fd < 0 && errno == ENOENT)
		SKIP(goto out_umount, "Multiplexed transactions are not supported");
	ASSERT_GE(feature_fd, 0);
	ret = read(feature_fd, &feature, sizeof(feature));
	ASSERT_EQ(ret, sizeof(feature));
	close(feature_fd);
	feature_fd = -1;
	if (feature != '1')
		SKIP(goto out_umount, "Multiplexed transactions are disabled");

	snprintf(path, sizeof(path), "%s/binder-control", mountpoint);
	control_fd = open(path, O_RDONLY | O_CLOEXEC);
	ASSERT_GE(control_fd, 0);
	ret = ioctl(control_fd, BINDER_CTL_ADD, &device);
	ASSERT_EQ(ret, 0);
	close(control_fd);
	control_fd = -1;

	snprintf(path, sizeof(path), "%s/%s", mountpoint, device.name);
	ret = pipe2(parent_to_server, O_CLOEXEC);
	ASSERT_EQ(ret, 0);
	ret = pipe2(server_to_parent, O_CLOEXEC);
	ASSERT_EQ(ret, 0);
	server_pid = fork();
	ASSERT_GE(server_pid, 0);
	if (server_pid == 0) {
		close(parent_to_server[1]);
		close(server_to_parent[0]);
		_exit(server(path, parent_to_server[0], server_to_parent[1]));
	}
	close(parent_to_server[0]);
	parent_to_server[0] = -1;
	close(server_to_parent[1]);
	server_to_parent[1] = -1;

	fd = open(path, O_RDWR | O_CLOEXEC);
	EXPECT_GE(fd, 0);
	if (fd < 0)
		goto out_server;
	mapping = mmap(NULL, BINDER_MAPPING_SIZE, PROT_READ, MAP_PRIVATE, fd, 0);
	EXPECT_NE(mapping, MAP_FAILED);
	if (mapping == MAP_FAILED)
		goto out_server;
	ret = read(server_to_parent[0], &ready, sizeof(ready));
	EXPECT_EQ(ret, sizeof(ready)) {
		TH_LOG("Server failed before becoming ready");
	}
	if (ret != sizeof(ready))
		goto out_server;
	memset(&request, 0, sizeof(request));
	request.request_id = MIXED_REQUEST_ID;
	size = append_command(command_buffer, 0, BC_TRANSACTION_MULTIPLEXED,
			      &request, sizeof(request));
	errno = 0;
	ret = binder_write(fd, command_buffer, size);
	EXPECT_LT(ret, 0);
	EXPECT_EQ(errno, EOPNOTSUPP);
	if (ret == 0 || errno != EOPNOTSUPP)
		goto out_server;
	ret = get_session_handle(fd, &session_handle);
	EXPECT_EQ(ret, 0) {
		TH_LOG("%s - Failed to obtain private session node",
		       strerror(errno));
	}
	if (ret)
		goto out_server;
	ret = forward_session_handle(fd, session_handle);
	EXPECT_EQ(ret, 0) {
		TH_LOG("%s - Failed to forward private session node",
		       strerror(errno));
	}
	if (ret)
		goto out_server;
	for (i = 0; i < REQUEST_COUNT; i++) {
		memset(&request, 0, sizeof(request));
		request.transaction_data.target.handle = session_handle;
		request.transaction_data.code = request_codes[i];
		request.transaction_data.data_size = sizeof(request_payloads[i]);
		request.transaction_data.data.ptr.buffer =
			(uintptr_t)&request_payloads[i];
		request.request_id = request_ids[i];
		size = append_command(command_buffer, size,
				      BC_TRANSACTION_MULTIPLEXED,
				      &request, sizeof(request));
	}
	ret = binder_write(fd, command_buffer, size);
	EXPECT_EQ(ret, 0) {
		TH_LOG("%s - Failed to submit multiplexed transactions",
		       strerror(errno));
	}
	if (ret)
		goto out_server;

	ret = read(server_to_parent[0], &ready, sizeof(ready));
	EXPECT_EQ(ret, sizeof(ready)) {
		TH_LOG("Server failed before submitting replies");
	}
	if (ret != sizeof(ready))
		goto out_server;

	ret = pipe2(abandoner_to_parent, O_CLOEXEC);
	ASSERT_EQ(ret, 0);
	abandoner_pid = fork();
	ASSERT_GE(abandoner_pid, 0);
	if (abandoner_pid == 0) {
		close(abandoner_to_parent[0]);
		close(parent_to_server[1]);
		close(server_to_parent[0]);
		_exit(abandon_claims(path, abandoner_to_parent[1]));
	}
	close(abandoner_to_parent[1]);
	abandoner_to_parent[1] = -1;
	ret = read(abandoner_to_parent[0], &ready, sizeof(ready));
	EXPECT_EQ(ret, sizeof(ready));
	if (ret != sizeof(ready))
		goto out_server;
	close(abandoner_to_parent[0]);
	abandoner_to_parent[0] = -1;
	ret = waitpid(abandoner_pid, &status, 0);
	EXPECT_EQ(ret, abandoner_pid);
	if (ret != abandoner_pid)
		goto out_server;
	abandoner_pid = -1;
	EXPECT_TRUE(WIFEXITED(status));
	if (!WIFEXITED(status))
		goto out_server;
	EXPECT_EQ(WEXITSTATUS(status), 0);
	if (WEXITSTATUS(status))
		goto out_server;
	ret = write(parent_to_server[1], &ready, sizeof(ready));
	EXPECT_EQ(ret, sizeof(ready));
	if (ret != sizeof(ready))
		goto out_server;

	ret = pipe2(claimant_to_parent, O_CLOEXEC);
	ASSERT_EQ(ret, 0);
	ret = pipe2(parent_to_claimant, O_CLOEXEC);
	ASSERT_EQ(ret, 0);
	claimant_pid = fork();
	ASSERT_GE(claimant_pid, 0);
	if (claimant_pid == 0) {
		close(claimant_to_parent[0]);
		close(parent_to_claimant[1]);
		close(parent_to_server[1]);
		close(server_to_parent[0]);
		_exit(claimant(path, parent_to_claimant[0], claimant_to_parent[1]));
	}
	close(claimant_to_parent[1]);
	claimant_to_parent[1] = -1;
	close(parent_to_claimant[0]);
	parent_to_claimant[0] = -1;
	ret = read(claimant_to_parent[0], &ready, sizeof(ready));
	EXPECT_EQ(ret, sizeof(ready));
	if (ret != sizeof(ready))
		goto out_server;
	ret = release_handle(fd, session_handle);
	EXPECT_EQ(ret, 0) {
		TH_LOG("%s - Failed to release submitted session handle",
		       strerror(errno));
	}
	if (ret)
		goto out_server;
	ret = write(parent_to_server[1], &ready, sizeof(ready));
	EXPECT_EQ(ret, sizeof(ready));
	if (ret != sizeof(ready))
		goto out_server;

	ret = read(server_to_parent[0], &ready, sizeof(ready));
	EXPECT_EQ(ret, sizeof(ready)) {
		TH_LOG("Server failed before retiring multiplexed transactions");
	}
	if (ret != sizeof(ready))
		goto out_server;
	ret = write(parent_to_claimant[1], &ready, sizeof(ready));
	EXPECT_EQ(ret, sizeof(ready));
	if (ret != sizeof(ready))
		goto out_server;
	close(parent_to_claimant[1]);
	parent_to_claimant[1] = -1;
	close(claimant_to_parent[0]);
	claimant_to_parent[0] = -1;
	ret = waitpid(claimant_pid, &status, 0);
	EXPECT_EQ(ret, claimant_pid);
	if (ret != claimant_pid)
		goto out_server;
	claimant_pid = -1;
	EXPECT_TRUE(WIFEXITED(status));
	if (!WIFEXITED(status))
		goto out_close;
	EXPECT_EQ(WEXITSTATUS(status), 0);
	if (WEXITSTATUS(status))
		goto out_close;
	ret = write(parent_to_server[1], &ready, sizeof(ready));
	EXPECT_EQ(ret, sizeof(ready));
	if (ret != sizeof(ready))
		goto out_server;
	ret = get_session_handle(fd, &session_handle);
	EXPECT_EQ(ret, 0) {
		TH_LOG("%s - Failed to obtain mixed-use test node",
		       strerror(errno));
	}
	if (ret)
		goto out_server;
	memset(&request, 0, sizeof(request));
	request.transaction_data.target.handle = session_handle;
	request.transaction_data.code = MIXED_REQUEST_CODE;
	request.request_id = MIXED_REQUEST_ID;
	size = append_command(command_buffer, 0, BC_TRANSACTION_MULTIPLEXED,
			      &request, sizeof(request));
	ret = binder_write(fd, command_buffer, size);
	EXPECT_EQ(ret, 0);
	if (ret)
		goto out_server;
	ret = read(server_to_parent[0], &ready, sizeof(ready));
	EXPECT_EQ(ret, sizeof(ready)) {
		TH_LOG("Server failed to receive pending mixed-use transaction");
	}
	if (ret != sizeof(ready))
		goto out_server;
	ret = call_ordinary_transaction(fd, session_handle);
	EXPECT_EQ(ret, 0) {
		TH_LOG("%s - Ordinary transaction failed while multiplexed work was pending",
		       strerror(errno));
	}
	if (ret)
		goto out_server;
	ret = binder_write(fd, &enter_looper, sizeof(enter_looper));
	EXPECT_EQ(ret, 0);
	if (ret)
		goto out_server;
	ret = claim_reply(fd, session_handle, MIXED_CLAIM_ID);
	EXPECT_EQ(ret, 0);
	if (ret)
		goto out_server;
	ret = write(parent_to_server[1], &ready, sizeof(ready));
	EXPECT_EQ(ret, sizeof(ready));
	if (ret != sizeof(ready))
		goto out_server;
	{
		static const __u32 payload = ORDINARY_REQUEST_PAYLOAD;
		struct binder_transaction_data ordinary = {
			.target.handle = session_handle,
			.code = ORDINARY_REQUEST_CODE,
			.data_size = sizeof(payload),
			.data.ptr.buffer = (uintptr_t)&payload,
		};

		size = append_command(command_buffer, 0, BC_TRANSACTION,
				      &ordinary, sizeof(ordinary));
		ret = binder_write(fd, command_buffer, size);
		if (!ret)
			ret = binder_read(fd, BR_DEAD_REPLY, &ordinary, 0);
	}
	EXPECT_EQ(ret, 0) {
		TH_LOG("%s - Retiring node did not invalidate an ordinary reply token",
		       strerror(errno));
	}
	if (ret)
		goto out_server;
	ret = read(server_to_parent[0], &ready, sizeof(ready));
	EXPECT_EQ(ret, sizeof(ready)) {
		TH_LOG("Server failed to retire the mixed-use node");
	}
	if (ret != sizeof(ready))
		goto out_server;
	ret = binder_read(fd, BR_REPLY_MULTIPLEXED_ERROR, &error,
			  sizeof(error));
	EXPECT_EQ(ret, 0);
	if (ret)
		goto out_server;
	EXPECT_EQ(error.claim_id, MIXED_CLAIM_ID);
	EXPECT_EQ(error.request_id, MIXED_REQUEST_ID);
	EXPECT_EQ(error.reason, BINDER_MULTIPLEXED_REPLY_SHUTDOWN);
	EXPECT_EQ(error.error, 0);
	if (error.claim_id != MIXED_CLAIM_ID ||
	    error.request_id != MIXED_REQUEST_ID ||
	    error.reason != BINDER_MULTIPLEXED_REPLY_SHUTDOWN ||
	    error.error != 0)
		goto out_server;
	{
		static const __u32 payload = ORDINARY_REQUEST_PAYLOAD;
		struct binder_transaction_data ordinary = {
			.target.handle = session_handle,
			.code = ORDINARY_REQUEST_CODE,
			.data_size = sizeof(payload),
			.data.ptr.buffer = (uintptr_t)&payload,
		};

		size = append_command(command_buffer, 0, BC_TRANSACTION,
				      &ordinary, sizeof(ordinary));
		ret = binder_write(fd, command_buffer, size);
		if (!ret)
			ret = binder_read(fd, BR_DEAD_REPLY, &ordinary, 0);
	}
	EXPECT_EQ(ret, 0) {
		TH_LOG("%s - Retired node accepted an ordinary transaction",
		       strerror(errno));
	}
	if (ret)
		goto out_server;
	{
		struct binder_transaction_data oneway = {
			.target.handle = session_handle,
			.flags = TF_ONE_WAY,
			.code = ORDINARY_REQUEST_CODE,
		};

		size = append_command(command_buffer, 0, BC_TRANSACTION,
				      &oneway, sizeof(oneway));
		ret = binder_write(fd, command_buffer, size);
		if (!ret)
			ret = binder_read(fd, BR_DEAD_REPLY, &oneway, 0);
	}
	EXPECT_EQ(ret, 0) {
		TH_LOG("%s - Retired node accepted a one-way transaction",
		       strerror(errno));
	}
	if (ret)
		goto out_server;
	ret = get_session_handle(fd, &session_handle);
	EXPECT_EQ(ret, 0) {
		TH_LOG("%s - Failed to obtain endpoint-exit test node",
		       strerror(errno));
	}
	if (ret)
		goto out_server;
	memset(&request, 0, sizeof(request));
	request.transaction_data.target.handle = session_handle;
	request.transaction_data.code = OWNER_EXIT_REQUEST_CODE;
	request.request_id = OWNER_EXIT_REQUEST_ID;
	size = append_command(command_buffer, 0, BC_TRANSACTION_MULTIPLEXED,
			      &request, sizeof(request));
	ret = binder_write(fd, command_buffer, size);
	EXPECT_EQ(ret, 0);
	if (ret)
		goto out_server;
	ret = claim_reply(fd, session_handle, OWNER_EXIT_CLAIM_ID);
	EXPECT_EQ(ret, 0);
	if (ret)
		goto out_server;
	ret = read(server_to_parent[0], &ready, sizeof(ready));
	EXPECT_EQ(ret, sizeof(ready)) {
		TH_LOG("Server failed before endpoint-exit terminal result");
	}
	if (ret != sizeof(ready))
		goto out_server;
	ret = write(parent_to_server[1], &ready, sizeof(ready));
	EXPECT_EQ(ret, sizeof(ready));
	if (ret != sizeof(ready))
		goto out_server;
	close(parent_to_server[1]);
	parent_to_server[1] = -1;
	close(server_to_parent[0]);
	server_to_parent[0] = -1;
	ret = waitpid(server_pid, &status, 0);
	EXPECT_EQ(ret, server_pid);
	if (ret != server_pid)
		goto out_server;
	server_pid = -1;
	EXPECT_TRUE(WIFEXITED(status));
	if (!WIFEXITED(status))
		goto out_close;
	EXPECT_EQ(WEXITSTATUS(status), 0);
	if (WEXITSTATUS(status))
		goto out_close;
	ret = binder_read(fd, BR_REPLY_MULTIPLEXED_ERROR, &error,
			  sizeof(error));
	EXPECT_EQ(ret, 0);
	if (ret)
		goto out_close;
	EXPECT_EQ(error.claim_id, OWNER_EXIT_CLAIM_ID);
	EXPECT_EQ(error.request_id, OWNER_EXIT_REQUEST_ID);
	EXPECT_EQ(error.reason, BINDER_MULTIPLEXED_REPLY_DEAD);
	EXPECT_EQ(error.error, 0);
	if (error.claim_id != OWNER_EXIT_CLAIM_ID ||
	    error.request_id != OWNER_EXIT_REQUEST_ID ||
	    error.reason != BINDER_MULTIPLEXED_REPLY_DEAD || error.error != 0)
		goto out_close;

out_close:
	munmap(mapping, BINDER_MAPPING_SIZE);
	close(fd);
	ret = umount2(mountpoint, MNT_DETACH);
	EXPECT_EQ(ret, 0);
	ret = rmdir(mountpoint);
	EXPECT_EQ(ret, 0);
	return;

out_server:
	if (abandoner_to_parent[0] >= 0)
		close(abandoner_to_parent[0]);
	if (abandoner_to_parent[1] >= 0)
		close(abandoner_to_parent[1]);
	if (claimant_to_parent[0] >= 0)
		close(claimant_to_parent[0]);
	if (claimant_to_parent[1] >= 0)
		close(claimant_to_parent[1]);
	if (parent_to_claimant[0] >= 0)
		close(parent_to_claimant[0]);
	if (parent_to_claimant[1] >= 0)
		close(parent_to_claimant[1]);
	if (parent_to_server[0] >= 0)
		close(parent_to_server[0]);
	if (parent_to_server[1] >= 0)
		close(parent_to_server[1]);
	if (server_to_parent[0] >= 0)
		close(server_to_parent[0]);
	if (server_to_parent[1] >= 0)
		close(server_to_parent[1]);
	if (server_pid > 0) {
		kill(server_pid, SIGKILL);
		waitpid(server_pid, NULL, 0);
	}
	if (abandoner_pid > 0) {
		kill(abandoner_pid, SIGKILL);
		waitpid(abandoner_pid, NULL, 0);
	}
	if (claimant_pid > 0) {
		kill(claimant_pid, SIGKILL);
		waitpid(claimant_pid, NULL, 0);
	}
	if (mapping != MAP_FAILED)
		munmap(mapping, BINDER_MAPPING_SIZE);
	if (fd >= 0)
		close(fd);
out_umount:
	umount2(mountpoint, MNT_DETACH);
out_rmdir:
	rmdir(mountpoint);
}

TEST_HARNESS_MAIN
