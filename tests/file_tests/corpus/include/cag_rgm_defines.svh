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

typedef enum {
    NONE,
    CONTAINER,
    REPEAT_BLOCK,
    REGISTER,
    RAM,
    REGISTER_FILE
} CAG_RGM_TYPE;

typedef enum {
    CAG_RGM_UNDEFINED,
    CAG_RGM_READ,
    CAG_RGM_WRITE,
    CAG_RGM_READ_RESPONSE,
    CAG_RGM_WRITE_RESPONSE
} CAG_RGM_TRANSFER_COMMAND;

typedef enum {
    SINGLE,
    ALL
} CAG_RGM_MODE;

`define cag_rgm_register_fields(T) \
rand T fields;

`define cag_rgm_driver_utils_start \
task start_rf(); \
    super.start_rf(); \
    fork

`define cag_rgm_driver_utils_end \
    join \
endtask : start_rf

`define cag_rgm_driver_field_reg_begin(TYPE,PATH,NAME) \
begin \
	TYPE m_reg; \
    $cast(m_reg,rf_model.get_by_name(PATH)); \
    if( m_reg == null ) \
        uvm_report_fatal(get_type_name(),{PATH," not found"});\
    forever begin \
        wait(!vif.res_n); \
        vif.NAME <= {16{1'b0}}; \
        @(posedge vif.res_n); \
        fork \
            @(negedge vif.res_n); \
            begin \
                forever begin \
                    @(posedge vif.clk);

`define cag_rgm_driver_field_reg_no_reset_begin(TYPE,PATH) \
begin \
	TYPE m_reg; \
    $cast(m_reg,rf_model.get_by_name(PATH)); \
    if( m_reg == null ) \
        uvm_report_fatal(get_type_name(),{PATH," not found"});\
    forever begin \
        wait(!vif.res_n); \
        @(posedge vif.res_n); \
        fork \
            @(negedge vif.res_n); \
            begin \
                forever begin \
                    @(posedge vif.clk);

`define cag_rgm_driver_field_reg_end \
                end \
            end \
        join_any \
        disable fork; \
    end \
end

`define cag_rgm_driver_reg_ro(TYPE,PATH,NAME,FIELD) \
	`cag_rgm_driver_field_reg_begin(TYPE,PATH,NAME) \
		vif.NAME <= m_reg.fields.FIELD; \
	`cag_rgm_driver_field_reg_end

`define cag_rgm_driver_reg_wo(TYPE,PATH,NAME,FIELD) \
	`cag_rgm_driver_field_reg_no_reset_begin(TYPE,PATH) \
		m_reg.fields.FIELD = vif.NAME``_next; \
	`cag_rgm_driver_field_reg_end

`define cag_rgm_driver_reg_wo_en(TYPE,PATH,NAME,FIELD) \
	`cag_rgm_driver_field_reg_begin(TYPE,PATH,NAME) \
		if(vif.NAME``_wen) \
			m_reg.fields.FIELD = vif.NAME; \
	`cag_rgm_driver_field_reg_end

`define cag_rgm_driver_reg_rw(TYPE,PATH,NAME,FIELD) \
	`cag_rgm_driver_field_reg_begin(TYPE,PATH,NAME) \
		vif.NAME <= m_reg.fields.FIELD; \
		m_reg.fields.FIELD = vif.NAME; \
	`cag_rgm_driver_field_reg_end

`define cag_rgm_driver_reg_rw_en(TYPE,PATH,NAME,FIELD) \
	`cag_rgm_driver_field_reg_begin(TYPE,PATH,NAME) \
		vif.NAME <= m_reg.fields.FIELD; \
		if(vif.NAME``_wen) \
			m_reg.fields.FIELD = vif.NAME; \
	`cag_rgm_driver_field_reg_end

`define cag_rgm_driver_ram_int(TYPE,PATH,NAME,WIDTH) \
    begin \
        TYPE m_ram; \
        bit [WIDTH-1:0] ram_address; \
        bit enable = 0; \
        $cast(m_ram,rf_model.get_by_name(PATH)); \
        if( m_ram == null ) \
            uvm_report_fatal(get_type_name(),{PATH," not found"}); \
        forever begin \
        	enable = vif.NAME``_ren; \
        	if(enable) \
        		ram_address = vif.NAME``_rf_addr; \
        	@(posedge vif.clk); \
        	if(enable) \
        		vif.NAME``_rdata <= m_ram.get_entry(ram_address); \
        	->m_ram.write_done; \
        end \
    end

`define cag_rgm_driver_ram_ext(TYPE,PATH,NAME) \
    begin \
    	TYPE m_ram; \
    	int unsigned entry; \
    	$cast(m_ram,rf_model.get_by_name(PATH)); \
        if( m_ram == null ) \
            uvm_report_fatal(get_type_name(),{PATH," not found"}); \
        vif.NAME``_rf_wen <= 1'b0; \
        vif.NAME``_rf_ren <= 1'b0; \
        forever begin \
        	@(m_ram.read_event or m_ram.write_event); \
        	@(posedge vif.clk); \
        	entry = m_ram.entry; \
        	vif.NAME``_rf_addr <= entry; \
        	if(m_ram.read_write) begin \
        		vif.NAME``_rf_wdata <= m_ram.get_entry(entry); \
        		vif.NAME``_rf_wen   <= 1'b1; \
        	end else begin \
        		vif.NAME``_rf_ren <= 1'b1; \
        	end \
        	@(posedge vif.clk); \
        	vif.NAME``_rf_wen <= 1'b0; \
        	while(!vif.NAME``_rf_access_complete) \
        		@(posedge vif.clk); \
        	vif.NAME``_rf_wen <= 1'b0; \
        	vif.NAME``_rf_ren <= 1'b0; \
        	if(!m_ram.read_write) \
        		m_ram.set_entry(vif.NAME``_rf_rdata, entry ); \
        	->m_ram.write_done; \
        end \
    end

