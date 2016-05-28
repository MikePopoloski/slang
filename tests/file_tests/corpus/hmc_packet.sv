/*
 *                              .--------------. .----------------. .------------.
 *                             | .------------. | .--------------. | .----------. |
 *                             | | ____  ____ | | | ____    ____ | | |   ______ | |
 *                             | ||_   ||   _|| | ||_   \  /   _|| | | .' ___  || |
 *       ___  _ __   ___ _ __  | |  | |__| |  | | |  |   \/   |  | | |/ .'   \_|| |
 *      / _ \| '_ \ / _ \ '_ \ | |  |  __  |  | | |  | |\  /| |  | | || |       | |
 *       (_) | |_) |  __/ | | || | _| |  | |_ | | | _| |_\/_| |_ | | |\ `.___.'\| |
 *      \___/| .__/ \___|_| |_|| ||____||____|| | ||_____||_____|| | | `._____.'| |
 *           | |               | |            | | |              | | |          | |
 *           |_|               | '------------' | '--------------' | '----------' |
 *                              '--------------' '----------------' '------------'
 *
 *  openHMC - An Open Source Hybrid Memory Cube Controller
 *  (C) Copyright 2014 Computer Architecture Group - University of Heidelberg
 *  www.ziti.uni-heidelberg.de
 *  B6, 26
 *  68159 Mannheim
 *  Germany
 *
 *  Contact: openhmc@ziti.uni-heidelberg.de
 *  http://ra.ziti.uni-heidelberg.de/openhmc
 *
 *   This source file is free software: you can redistribute it and/or modify
 *   it under the terms of the GNU Lesser General Public License as published by
 *   the Free Software Foundation, either version 3 of the License, or
 *   (at your option) any later version.
 *
 *   This source file is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU Lesser General Public License for more details.
 *
 *   You should have received a copy of the GNU Lesser General Public License
 *   along with this source file.  If not, see <http://www.gnu.org/licenses/>.
 *
 *
 */

//
// hmc_packet
//

`ifndef HMC_PACKET_SV
`define HMC_PACKET_SV

`define HMC_TYPE_MASK 6'h38

class hmc_packet extends uvm_sequence_item;

	// request header fields
	rand bit [2:0]			cube_ID;				// CUB
	rand bit [33:0]		address;				// ADRS
	rand bit [8:0]			tag;					// TAG
	rand bit [3:0]			packet_length;			// LNG 128-bit (16-byte) flits
	rand bit [3:0]			duplicate_length;		// DLN
	rand hmc_command_encoding 	command;			// CMD

	bit [127:0]				payload[$];				// 16-byte granularity

	// request tail fields
	rand bit [4:0]			return_token_count;		// RTC
	rand bit [2:0]			source_link_ID;			// SLID
	rand bit [2:0]			sequence_number;		// SEQ
	rand bit [7:0]			forward_retry_pointer;	// FRP
	rand bit [7:0]			return_retry_pointer;	// RRP
	rand bit [31:0]		packet_crc;				// CRC

	// response header fields not used before
	rand bit [8:0]			return_tag;				// TGA (Optional)

	// response tail fields not used before
	rand bit [6:0]			error_status;			// ERRSTAT
	rand bit				data_invalid;			// DINV

	// special bits for IRTRY
	rand bit				start_retry;
	rand bit				clear_error_abort;

	// CRC status fields
	rand bit				poisoned;				// Inverted CRC
	rand bit				crc_error;

	// helper fields
	rand int				flit_delay;
	
	int						timestamp;

	`uvm_object_utils_begin(hmc_packet)
		`uvm_field_int(flit_delay, UVM_ALL_ON | UVM_NOPACK | UVM_DEC | UVM_NOCOMPARE | UVM_DEC)
		`uvm_field_int(cube_ID, UVM_ALL_ON | UVM_NOPACK | UVM_DEC)
		`uvm_field_int(address, UVM_ALL_ON | UVM_NOPACK | UVM_HEX)
		`uvm_field_int(tag, UVM_ALL_ON | UVM_NOPACK | UVM_DEC)
		`uvm_field_int(packet_length, UVM_ALL_ON | UVM_NOPACK | UVM_DEC)
		`uvm_field_int(duplicate_length, UVM_ALL_ON | UVM_NOPACK | UVM_DEC)
		`uvm_field_enum(hmc_command_encoding, command, UVM_ALL_ON | UVM_NOPACK )
		`uvm_field_queue_int(payload, UVM_ALL_ON | UVM_NOPACK)
		`uvm_field_int(return_token_count, UVM_ALL_ON | UVM_NOPACK | UVM_DEC)
		`uvm_field_int(source_link_ID, UVM_ALL_ON | UVM_NOPACK | UVM_DEC)
		`uvm_field_int(sequence_number, UVM_ALL_ON | UVM_NOPACK | UVM_DEC)
		`uvm_field_int(forward_retry_pointer, UVM_ALL_ON | UVM_NOPACK | UVM_DEC)
		`uvm_field_int(return_retry_pointer, UVM_ALL_ON | UVM_NOPACK | UVM_DEC)
		`uvm_field_int(packet_crc, UVM_ALL_ON | UVM_NOPACK | UVM_HEX)
		`uvm_field_int(return_tag, UVM_ALL_ON | UVM_NOPACK | UVM_DEC)
		`uvm_field_int(error_status, UVM_ALL_ON | UVM_NOPACK | UVM_DEC)
		`uvm_field_int(data_invalid, UVM_ALL_ON | UVM_NOPACK | UVM_DEC)
		`uvm_field_int(poisoned, UVM_ALL_ON | UVM_NOPACK | UVM_DEC)
		`uvm_field_int(crc_error, UVM_ALL_ON | UVM_NOPACK | UVM_DEC)
	`uvm_object_utils_end

	constraint c_poisoned { poisoned == 0; }
	constraint c_cube_id {cube_ID ==0;}
	constraint c_address {
		soft address < 80000000;
		((command & `HMC_TYPE_MASK) == HMC_FLOW_TYPE) -> address == 0;	
		soft address[3:0]==4'h0;
	}
	constraint c_source_link_ID {source_link_ID ==0;}
	constraint c_crc_error { crc_error == 0; }
	constraint c_matching_length { packet_length == duplicate_length; }
	constraint c_return_tag { return_tag == 0; }
	constraint c_packet_length { (
						(packet_length == 2 && command == HMC_POSTED_WRITE_16) ||
						(packet_length == 3 && command == HMC_POSTED_WRITE_32) ||
						(packet_length == 4 && command == HMC_POSTED_WRITE_48) ||
						(packet_length == 5 && command == HMC_POSTED_WRITE_64) ||
						(packet_length == 6 && command == HMC_POSTED_WRITE_80) ||
						(packet_length == 7 && command == HMC_POSTED_WRITE_96) ||
						(packet_length == 8 && command == HMC_POSTED_WRITE_112) ||
						(packet_length == 9 && command == HMC_POSTED_WRITE_128) ||
						(packet_length == 2 && command == HMC_WRITE_16) ||
						(packet_length == 3 && command == HMC_WRITE_32) ||
						(packet_length == 4 && command == HMC_WRITE_48) ||
						(packet_length == 5 && command == HMC_WRITE_64) ||
						(packet_length == 6 && command == HMC_WRITE_80) ||
						(packet_length == 7 && command == HMC_WRITE_96) ||
						(packet_length == 8 && command == HMC_WRITE_112) ||
						(packet_length == 9 && command == HMC_WRITE_128) ||
						(packet_length > 1 && packet_length <= 9 && command == HMC_READ_RESPONSE) ||
						(packet_length == 1 && command == HMC_WRITE_RESPONSE) ||
						(packet_length == 1 && command == HMC_MODE_WRITE_RESPONSE) ||
						(packet_length == 1 && command == HMC_ERROR_RESPONSE) ||
						(packet_length == 2 && (command & `HMC_TYPE_MASK) == HMC_MISC_WRITE_TYPE) ||
						(packet_length == 2 && (command & `HMC_TYPE_MASK) == HMC_POSTED_MISC_WRITE_TYPE) ||
						(packet_length == 1 && (command & `HMC_TYPE_MASK) == HMC_MODE_READ_TYPE) ||
						(packet_length == 1 && (command & `HMC_TYPE_MASK) == HMC_READ_TYPE) ||
						(packet_length == 1 && (command & `HMC_TYPE_MASK) == HMC_FLOW_TYPE)
		); }
	constraint c_flit_delay {
		soft flit_delay dist{0:/90, [1:8]:/8, [8:200]:/2  };
	}
	constraint c_error_status {
		soft error_status == 0;
	}
	
	constraint c_data_invalid {
		soft data_invalid == 0;
	}
	
	
	constraint c_pret {
		(command == HMC_PRET)-> forward_retry_pointer	==0;
		(command == HMC_PRET)-> sequence_number			==0;
	}
	constraint c_irtry{
		(command == HMC_IRTRY) 							-> start_retry 			!= clear_error_abort;
		((command == HMC_IRTRY)&&(start_retry)) 		->forward_retry_pointer == 1;
		((command == HMC_IRTRY)&&(clear_error_abort))	->forward_retry_pointer == 2;
		(command == HMC_IRTRY)							-> sequence_number		== 0;
	}
	
	constraint c_flow {
		((command & `HMC_TYPE_MASK) == HMC_FLOW_TYPE) -> tag == 0;
		((command & `HMC_TYPE_MASK) == HMC_FLOW_TYPE) -> cube_ID == 0;
	}
	
	function new (string name = "hmc_packet");
		super.new(name);
	endfunction : new

    function void post_randomize();
		bit [127:0] rand_flit;

        super.post_randomize();

		if (packet_length > 9)
			`uvm_fatal(get_type_name(),$psprintf("post_randomize packet_length = %0d",packet_length))

		`uvm_info("AXI Packet queued",$psprintf("%0s packet_length = %0d",command.name(), packet_length), UVM_HIGH)
		
		if (packet_length < 2)
			return;

		for (int i=0; i<packet_length-1; i++) begin
			randomize_flit_successful : assert (std::randomize(rand_flit));
			payload.push_back(rand_flit);
		end
		if ((command == HMC_POSTED_DUAL_8B_ADDI)||
			(command == HMC_DUAL_8B_ADDI)) begin
			payload[0] [63:32] = 32'b0;
			payload[0][127:96] = 32'b0;
		end
		
		if ((command == HMC_MODE_WRITE)|| (command == HMC_MODE_READ)) begin
			payload[0][127:32] = 96'b0;
		end
    endfunction

	function hmc_command_type get_command_type();

		case(command & `HMC_TYPE_MASK)
			HMC_FLOW_TYPE:				return HMC_FLOW_TYPE;
			HMC_READ_TYPE:				return HMC_READ_TYPE;
			HMC_MODE_READ_TYPE:			return HMC_MODE_READ_TYPE;
			HMC_POSTED_WRITE_TYPE:		return HMC_POSTED_WRITE_TYPE;
			HMC_POSTED_MISC_WRITE_TYPE:	return HMC_POSTED_MISC_WRITE_TYPE;
			HMC_WRITE_TYPE:				return HMC_WRITE_TYPE;
			HMC_MISC_WRITE_TYPE:		return HMC_MISC_WRITE_TYPE;
			HMC_RESPONSE_TYPE:			return HMC_RESPONSE_TYPE;
			default: uvm_report_fatal(get_type_name(), $psprintf("command with an illegal command type='h%0h!", command));
		endcase

	endfunction : get_command_type

/*
		The CRC algorithm used on the HMC is the Koopman CRC-32K. This algorithm was
		chosen for the HMC because of its balance of coverage and ease of implementation. The
		polynomial for this algorithm is:
		x32 + x30 + x29 + x28 + x26 + x20 + x19 + x17 + x16 + x15 + x11 + x10 + x7 + x6 + x4 + x2 + x + 1

		bit [31:0] polynomial = 33'b1_0111_0100_0001_1011_1000_1100_1101_0111;	// Normal

		The CRC calculation operates on the LSB of the packet first. The packet CRC calculation
		must insert 0s in place of the 32-bits representing the CRC field before generating or
		checking the CRC. For example, when generating CRC for a packet, bits [63: 32] of the
		Tail presented to the CRC generator should be all zeros. The output of the CRC generator
		will have a 32-bit CRC value that will then be inserted in bits [63:32] of the Tail before
		forwarding that FLIT of the packet. When checking CRC for a packet, the CRC field
		should be removed from bits [63:32] of the Tail and replaced with 32-bits of zeros, then
		presented to the CRC checker. The output of the CRC checker will have a 32-bit CRC
		value that can be compared with the CRC value that was removed from the tail. If the two
		compare, the CRC check indicates no bit failures within the packet.
*/

	function bit [31:0] calculate_crc();
		bit bitstream[];
		packer_succeeded : assert (pack(bitstream) > 0);
		return calc_crc(bitstream);
	endfunction : calculate_crc
	
	function bit [31:0] calc_crc(bit bitstream[]);
		bit [32:0] polynomial = 33'h1741B8CD7; // Normal
		
		bit [32:0] remainder = 33'h0;
		for( int i=0; i < bitstream.size()-32; i++ ) begin	// without the CRC
			remainder = {remainder[31:0], bitstream[i]};
			if( remainder[32] ) begin
				remainder = remainder ^ polynomial;
			end
		end

		for( int i=0; i < 64; i++ ) begin	// zeroes for CRC and remainder
			remainder = {remainder[31:0], 1'b0};
			if( remainder[32] ) begin
				remainder = remainder ^ polynomial;
			end
		end

		return remainder[31:0];
	endfunction : calc_crc

	virtual function void do_pack(uvm_packer packer);

		super.do_pack(packer);
		packer.big_endian = 0;

		// pack header half flit
		case(command & `HMC_TYPE_MASK)
			HMC_FLOW_TYPE:
				case (command)
					HMC_NULL:		packer.pack_field( {64'h0}, 64);
					HMC_PRET:		packer.pack_field ( {3'h0, 3'h0, 34'h0, 9'h0, duplicate_length[3:0], packet_length[3:0], 1'b0, command[5:0]}, 64);
					HMC_TRET:		packer.pack_field ( {3'h0, 3'h0, 34'h0, 9'h0, duplicate_length[3:0], packet_length[3:0], 1'b0, command[5:0]}, 64);
					HMC_IRTRY:		packer.pack_field ( {3'h0, 3'h0, 34'h0, 9'h0, duplicate_length[3:0], packet_length[3:0], 1'b0, command[5:0]}, 64);
					default: uvm_report_fatal(get_type_name(), $psprintf("pack function called for a hmc_packet with an illegal FLOW type='h%0h!", command));
				endcase
			HMC_READ_TYPE:			packer.pack_field ( {cube_ID[2:0], 3'h0, address[33:0], tag[8:0], duplicate_length[3:0], packet_length[3:0], 1'b0, command[5:0]}, 64);
			HMC_MODE_READ_TYPE:		packer.pack_field ( {cube_ID[2:0], 3'h0, 34'h0, tag[8:0], duplicate_length[3:0], packet_length[3:0], 1'b0, command[5:0]}, 64);
			HMC_POSTED_WRITE_TYPE:	packer.pack_field ( {cube_ID[2:0], 3'h0, address[33:0], tag[8:0], duplicate_length[3:0], packet_length[3:0], 1'b0, command[5:0]}, 64);
			HMC_WRITE_TYPE:			packer.pack_field ( {cube_ID[2:0], 3'h0, address[33:0], tag[8:0], duplicate_length[3:0], packet_length[3:0], 1'b0, command[5:0]}, 64);
			HMC_POSTED_MISC_WRITE_TYPE:	packer.pack_field ( {cube_ID[2:0], 3'h0, address[33:0], tag[8:0], duplicate_length[3:0], packet_length[3:0], 1'b0, command[5:0]}, 64);
			HMC_MISC_WRITE_TYPE:	packer.pack_field ( {cube_ID[2:0], 3'h0, address[33:0], tag[8:0], duplicate_length[3:0], packet_length[3:0], 1'b0, command[5:0]}, 64);
			HMC_RESPONSE_TYPE:		packer.pack_field ( {22'h0, source_link_ID[2:0], 6'h0, return_tag[8:0], tag[8:0], duplicate_length[3:0], packet_length[3:0], 1'b0, command[5:0]}, 64);
			default: uvm_report_fatal(get_type_name(), $psprintf("pack function called for a hmc_packet with an illegal command type='h%0h!", command));
		endcase

		// Allow for errors when packet_length != duplicate_length
		if ((packet_length == duplicate_length) && payload.size() + 1 != packet_length && command != HMC_NULL)
			uvm_report_fatal(get_type_name(), $psprintf("pack function size mismatch payload.size=%0d packet_length=%0d!", payload.size(), packet_length));

		// pack payload
		for( int i=0; i<payload.size(); i++ ) packer.pack_field ( payload[i], 128);

		// pack tail half flit
		case(command & `HMC_TYPE_MASK)
			HMC_FLOW_TYPE:
				case (command)
					HMC_NULL:		packer.pack_field( {64'h0}, 64);
					HMC_PRET:		packer.pack_field ( {packet_crc[31:0], 5'h0, 3'h0, 5'h0, 3'h0, 8'h0, return_retry_pointer[7:0]}, 64);
					HMC_TRET:		packer.pack_field ( {packet_crc[31:0], return_token_count[4:0], 3'h0, 5'h0, sequence_number[2:0], forward_retry_pointer[7:0], return_retry_pointer[7:0]}, 64);
					HMC_IRTRY:		packer.pack_field ( {packet_crc[31:0], 5'h0, 3'h0, 5'h0, 3'h0, 6'h0, clear_error_abort, start_retry, return_retry_pointer[7:0]}, 64);
					default: uvm_report_fatal(get_type_name(), $psprintf("pack function (tail) called for a hmc_packet with an illegal FLOW type='h%0h!", command));
				endcase
			HMC_READ_TYPE:			packer.pack_field ( {packet_crc[31:0], return_token_count[4:0], source_link_ID[2:0], 5'h0, sequence_number[2:0], forward_retry_pointer[7:0], return_retry_pointer[7:0]}, 64);
			HMC_POSTED_WRITE_TYPE:	packer.pack_field ( {packet_crc[31:0], return_token_count[4:0], source_link_ID[2:0], 5'h0, sequence_number[2:0], forward_retry_pointer[7:0], return_retry_pointer[7:0]}, 64);
			HMC_WRITE_TYPE:			packer.pack_field ( {packet_crc[31:0], return_token_count[4:0], source_link_ID[2:0], 5'h0, sequence_number[2:0], forward_retry_pointer[7:0], return_retry_pointer[7:0]}, 64);
			HMC_MODE_READ_TYPE:		packer.pack_field ( {packet_crc[31:0], return_token_count[4:0], source_link_ID[2:0], 5'h0, sequence_number[2:0], forward_retry_pointer[7:0], return_retry_pointer[7:0]}, 64);
			HMC_POSTED_MISC_WRITE_TYPE:	packer.pack_field ( {packet_crc[31:0], return_token_count[4:0], source_link_ID[2:0], 5'h0, sequence_number[2:0], forward_retry_pointer[7:0], return_retry_pointer[7:0]}, 64);
			HMC_MISC_WRITE_TYPE:	packer.pack_field ( {packet_crc[31:0], return_token_count[4:0], source_link_ID[2:0], 5'h0, sequence_number[2:0], forward_retry_pointer[7:0], return_retry_pointer[7:0]}, 64);
			HMC_RESPONSE_TYPE:		packer.pack_field ( {packet_crc[31:0], return_token_count[4:0], error_status[6:0], data_invalid, sequence_number[2:0], forward_retry_pointer[7:0], return_retry_pointer[7:0]}, 64);
			default: uvm_report_fatal(get_type_name(), $psprintf("pack function (tail) called for a hmc_packet with an illegal command type='h%0h!", command));
		endcase
	endfunction : do_pack


	virtual function void do_unpack(uvm_packer packer);
		bit [63:0]	header;
		bit [63:0]	tail;
		bit [31:0]	calculated_crc;
		bit [21:0]	rsvd22;
		bit [5:0]	rsvd6;
		bit [4:0]	rsvd5;
		bit [2:0]	rsvd3;
		bit 		rsvd1;

		bit bitstream[];

		super.do_unpack(packer);
		packer.big_endian = 0;

		packer.get_bits(bitstream);
		
		for (int i = 0; i <32; i++)begin
			packet_crc[i] = bitstream[bitstream.size()-32 +i];
		end
		
		calculated_crc = calc_crc(bitstream);
		// header
		header = packer.unpack_field(64);
		command[5:0] = header[5:0];//-- doppelt?

		if (get_command_type != HMC_RESPONSE_TYPE)
			{cube_ID[2:0], rsvd3, address[33:0], tag[8:0], duplicate_length[3:0], packet_length[3:0], rsvd1, command[5:0]}	= header;
		else
			{rsvd22[21:0], source_link_ID[2:0], rsvd6[5:0], return_tag[8:0], tag[8:0], duplicate_length[3:0], packet_length[3:0], rsvd1, command[5:0]}	= header;
		// Unpack should not be called with length errors
		if (duplicate_length != packet_length || packet_length == 0)
			`uvm_fatal(get_type_name(), $psprintf("do_unpack: length mismatch dln=%0d len=%0d cmd=%0d!", duplicate_length, packet_length, command));

		// payload
		for (int i = 0; i < packet_length-1; i++)
			payload.push_back(packer.unpack_field(128));

		// tail
		tail = packer.unpack_field(64);
		if (get_command_type != HMC_RESPONSE_TYPE) 
			{packet_crc[31:0], return_token_count[4:0], source_link_ID[2:0], rsvd5, sequence_number[2:0], forward_retry_pointer[7:0], return_retry_pointer[7:0]}	= tail;
		else
			{packet_crc[31:0], return_token_count[4:0], error_status[6:0], data_invalid, sequence_number[2:0], forward_retry_pointer[7:0], return_retry_pointer[7:0]}	= tail;

		start_retry			= (command == HMC_IRTRY ? forward_retry_pointer[0] : 1'b0);
		clear_error_abort	= (command == HMC_IRTRY ? forward_retry_pointer[1] : 1'b0);

		crc_error = 0;

		poisoned = (packet_crc == ~calculated_crc) ? 1'b1 : 1'b0;
		if (packet_crc != calculated_crc &&  !poisoned )
		begin
			crc_error = 1;
		end
	endfunction : do_unpack


	virtual function bit compare_adaptive_packet(hmc_packet rhs, uvm_comparer comparer);

		string name_string;

		compare_adaptive_packet &= comparer.compare_field("packet_length", packet_length, rhs.packet_length, 64, UVM_DEC);
		compare_adaptive_packet &= comparer.compare_field("payload.size()", payload.size(), rhs.payload.size(), 64, UVM_DEC);

		for (int i=0; i<packet_length; i++)
		begin
			if (!compare_adaptive_packet)
				return 0;
			$sformat(name_string, "payload[%0d]", i);
			compare_adaptive_packet &= comparer.compare_field(name_string, payload[i], rhs.payload[i], 128, UVM_HEX);
		end

		compare_adaptive_packet &= comparer.compare_field("cube_ID", cube_ID, rhs.cube_ID, 64, UVM_DEC);
		compare_adaptive_packet &= comparer.compare_field("address", address, rhs.address, 64, UVM_DEC);
		compare_adaptive_packet &= comparer.compare_field("tag", tag, rhs.tag, 64, UVM_DEC);
		compare_adaptive_packet &= comparer.compare_field("packet_length", packet_length, rhs.packet_length, 64, UVM_DEC);
		compare_adaptive_packet &= comparer.compare_field("duplicate_length", duplicate_length, rhs.duplicate_length, 64, UVM_DEC);
		compare_adaptive_packet &= comparer.compare_field("command", command, rhs.command, 64, UVM_DEC);
		compare_adaptive_packet &= comparer.compare_field("return_token_count", return_token_count, rhs.return_token_count, 64, UVM_DEC);
		compare_adaptive_packet &= comparer.compare_field("source_link_ID", source_link_ID, rhs.source_link_ID, 64, UVM_DEC);
		compare_adaptive_packet &= comparer.compare_field("sequence_number", sequence_number, rhs.sequence_number, 64, UVM_DEC);
		compare_adaptive_packet &= comparer.compare_field("forward_retry_pointer", forward_retry_pointer, rhs.forward_retry_pointer, 64, UVM_DEC);
		compare_adaptive_packet &= comparer.compare_field("return_tag", return_tag, rhs.return_tag, 64, UVM_DEC);
		compare_adaptive_packet &= comparer.compare_field("error_status", error_status, rhs.error_status, 64, UVM_DEC);
		compare_adaptive_packet &= comparer.compare_field("data_invalid", data_invalid, rhs.data_invalid, 64, UVM_DEC);
		compare_adaptive_packet &= comparer.compare_field("start_retry", start_retry, rhs.start_retry, 64, UVM_DEC);
		compare_adaptive_packet &= comparer.compare_field("clear_error_abort", clear_error_abort, rhs.clear_error_abort, 64, UVM_DEC);

	endfunction : compare_adaptive_packet

endclass : hmc_packet

`endif // HMC_PACKET_SV

